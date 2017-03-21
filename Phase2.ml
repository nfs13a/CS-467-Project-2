(* for keeping track of program run time *)
val timer = Timer.startCPUTimer();

fun printTime () = let
	val {sys:Time.time, usr:Time.time} = Timer.checkCPUTimer timer
	in Real.toString ((real (LargeInt.toInt (Time.toMicroseconds usr)) + real (LargeInt.toInt(Time.toMicroseconds sys)) ) / 1000000.0) ^ " seconds"
end;

fun readlist (infile : string) = let
	val ins = TextIO.openIn infile;
	fun loop ins =
		case TextIO.inputLine ins of
    	SOME line => line :: loop ins
    	| NONE    => []
	in loop ins before TextIO.closeIn ins
end;

val fileInput = readlist "h09.csv";

(* max capacity of sack *)
val SOME houses = Int.fromString (hd fileInput);
val SOME peopleCount = Int.fromString (hd (tl fileInput));

fun toPreferences (nil, n) = []
  | toPreferences (a::b, n) = let
	val SOME A = Int.fromString a;
	fun prefs (h::t, n) = let
		val SOME H = Int.fromString h
	  	in if n = 1 then [H] else H::prefs (t, n - 1)
	end;
	fun elim (a::b, n) = if n = 1 then b else elim (b, n - 1)
  	in (A, prefs (b,n))::toPreferences (elim (b, n),n)
end;

(* (person, (preferences)) *)
val prefs = toPreferences (tl (tl fileInput), peopleCount);

(* helper variables for random number generation *)
val nextInt = Random.randRange (0, houses - 1);	(* for initial population generation *)
val nextChild = Random.randRange (1, length prefs - 1);	(* the number of elements from left parent *)
val mutationChance = Random.randRange (0, 199);	(* .005 chance of any given bit being flipped *)
val harshMutationChance = Random.randRange (0, 4);	(* .2 chance of any given bit being flipped upon convergence *)
val parentOptions = Random.randRange (0, length prefs - 1);	(* for picking parents of next child *)
val r = Random.rand (1,1);	(* rand for seed for random number generation *)

(* return person a's preference for person b *)
fun getPreference (a, b, p::pt:(int * int list) list) = let
	fun getVal (b, p::pt:int list) = if b = 1 then p else getVal(b - 1, pt)
	in if a = 1 then getVal(b, #2p) else getPreference(a - 1, b, pt)
end;

(* start at house 0, go through house n - 1 (house n cannot exist) *)
fun fitness (member,n) = let
	(* for a house n, computes the fitness for the people in the house *)
	(* full member, member position to examine, house number, individual number *)
	fun houseFit (member, nil, n, i) = 0
	  | houseFit (member:int list, m::ms:int list, n, i) = let
		val next = houseFit(member, ms, n, i + 1);
		(* given an individual i, computes the fitness of i with the rest of the members of the house *)
		fun singeFits (m::nil:int list, n, i, j) = if m = n then getPreference(i, j, prefs) else 0
		  | singeFits (m::mt:int list, n, i, j) = let
		  	val next = singeFits (mt, n, i, j + 1)
		  	in if m = n then getPreference(i, j, prefs) + next else next
		end;
		in if i <= (length prefs) andalso m = n then singeFits(member, n, i, 1) + next else 0 + next
	end;
	in if n = houses then 0 else houseFit(member, member, n, 1) + fitness(member, n + 1)
end;

(* inserts the a bit string into population when building the initial population *)
fun insert (nil, newMember) = if fitness (newMember,0) > 0 then [newMember] else nil
(* if newMember is not better than current, do not insert it, else add the rest of the old after it except the last *)
  | insert (h::t, newMember) = if fitness (h,0) >= fitness (newMember,0) then h::insert(t, newMember) else newMember::complete(h::t)
(* once the new member has been inserted,  *)
and complete (nil) = nil
  | complete (h::nil) = []
  | complete (h::t) = h::complete(t);

fun insertWhenFull (h::nil, newMember) = if fitness (h,0) >= fitness (newMember,0) then [h] else [newMember]
(* if newMember is not better than current, do not insert it, else add the rest of the old after it except the last *)
  | insertWhenFull (h::t, newMember) = let
  	val tuple = insertWhenFull(t, newMember)
	in if fitness (h,0) >= fitness (newMember,0) then h::tuple else newMember::complete(h::t)
end;

fun createPop p = let
	fun randMem L = let
		val t = nextInt r
		(* in if length L = 5 then L else randMem (t::L) *)
		in if length L = length prefs then L else randMem (t::L)
	end;
	val mem = randMem []
	(* in if length p < 5 then createPop (insert (p,mem)) else p *)
	in if length p < length prefs then createPop (insert (p,mem)) else p
end;

val population = createPop [];
printTime();

fun getLast (h::nil) = h
  | getLast (p::ps) = getLast ps;

fun shouldMutate () = mutationChance r = 0;

fun flipVals (c::nil) = if shouldMutate() then [(c + 1) mod (length prefs)] else [c] 
  | flipVals (c::cs) = if shouldMutate() then ((c + 1) mod (length prefs))::flipVals(cs) else c::flipVals(cs);

fun shouldMutateHarshly () = harshMutationChance r = 0;

fun flipValsHarshly (c::nil) = if shouldMutateHarshly() then [(c + 1) mod (length prefs)] else [c] 
  | flipValsHarshly (c::cs) = if shouldMutateHarshly() then ((c + 1) mod (length prefs))::flipVals(cs) else c::flipVals(cs);

(* waits for 3 equal convergences of population or timeout *)
fun waitForIt (L,P) = let
	(* given a population, create and insert new children until a convergence is reached *)
	fun evolve (p) = let
		(* given two parents, produce a new child *)
		fun reproduce (pL, pR) = let
			(* random number between  *)
			val t = nextChild r;
			fun headParent (p::ps,n) = if n > 1 then p::headParent(ps, n - 1) else [p];
			fun tailParent (p::ps,n) = if n > 1 then tailParent(ps,n - 1) else ps;
			fun mutation c = flipVals (c)
			in mutation ((headParent(pL,t)) @ (tailParent(pR,t)))
		end;
		fun getParentNumbers () = let
			val left = parentOptions r;
			val right = parentOptions r
			in if left = right then getParentNumbers () else (left, right)
		end;
		fun getParents (p, (l, r)) = let
			fun getAParent (p::ps,n) = if n = 0 then p else getAParent (ps, n - 1)
			in (getAParent (p,l), getAParent (p,r))
		end;
		val childAdded = insertWhenFull(p, reproduce (getParents(p, getParentNumbers ())))
		in if hd childAdded <> getLast childAdded then evolve (childAdded) else childAdded
	end;
	fun allEqual (nil) = true
	  | allEqual (a::nil) = true
	  | allEqual (a::b::nil) = a = b
	  | allEqual (a::b::c) = a = b andalso allEqual(b::c);
	val evolutionResult = evolve (P);
	val newPop = evolutionResult;
	val newFinalMembers = (hd newPop)::L;
	fun editFinalMembers L = if allEqual newFinalMembers then L else [hd L];
	val trueNewFinalMembers = editFinalMembers newFinalMembers;
	fun massMutate (h::t) = h::(map flipValsHarshly t);
	val {sys:Time.time, usr:Time.time} = Timer.checkCPUTimer timer;
	val seconds = (real (LargeInt.toInt (Time.toMicroseconds usr)) + real (LargeInt.toInt(Time.toMicroseconds sys)) )/ 1000000.0
	(* stop at 3 equal convergences or timeout *)
	in if length trueNewFinalMembers = 3 orelse seconds > 600.0 then (hd trueNewFinalMembers) else waitForIt(massMutate(trueNewFinalMembers), newPop)
end;

Control.Print.printLength := length globes;

val answer = waitForIt([], population);

val happiness = fitness (answer, 0);

printTime();

Control.Print.printLength := 10;