(* accepts filename, returns string list of each line *)
fun readlist (infile : string) = let
	val ins = TextIO.openIn infile;
	fun loop ins =
		case TextIO.inputLine ins of
    	SOME line => line :: loop ins
    	| NONE    => []
	in loop ins before TextIO.closeIn ins
end;

fun trimLast s = String.substring(s, 0, size s - 1)

val SOME filename = TextIO.inputLine TextIO.stdIn;

val filename = trimLast filename;

(* for keeping track of program run time *)
val timer = Timer.startCPUTimer();

fun printTime () = let
	val {sys:Time.time, usr:Time.time} = Timer.checkCPUTimer timer
	in Real.toString ((real (LargeInt.toInt (Time.toMicroseconds usr)) + real (LargeInt.toInt(Time.toMicroseconds sys)) ) / 1000000.0) ^ " seconds"
end;

val fileInput = readlist (filename^".csv");

(* max capacity of sack *)
val SOME houses = Int.fromString (hd fileInput);
val SOME peopleCount = Int.fromString (hd (tl fileInput));

(* formatting preferences from individual lines into an (int * int list) list *)
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

val maxPopLength = if length prefs > 50 then 50 else length prefs;

(* helper variables for random number generation *)
val nextInt = Random.randRange (0, houses - 1);	(* for initial population generation *)
val nextChild = Random.randRange (1, length prefs - 1);	(* the number of elements from left parent *)
val mutationChance = Random.randRange (0, 199);	(* .005 chance of any given bit being flipped *)
val harshMutationChance = Random.randRange (0, 4);	(* .2 chance of any given bit being flipped upon convergence *)
val parentOptions = Random.randRange (0, maxPopLength - 1);	(* for picking parents of next child *)
val r = Random.rand (1,1);	(* rand for seed for random number generation *)

(* return person a's preference for person b *)
fun getPreference (a, b, p::pt:(int * int list) list) = let
	fun getVal (b, p::pt:int list) = if b = 1 then p else getVal(b - 1, pt)
	in if a = 1 then getVal(b, #2p) else getPreference(a - 1, b, pt)
end;

(* only computes the fitness if there is at least 1 person per house *)
fun fitness (member, n) = let
	(* returns true if every house has at least 1 person, else returns false *)
	fun balanced (member, n) = let
		(* number of people in house n *)
		val len = length (List.filter (fn x => x = n) member)
		in if n < houses - 1 then len > 0 andalso balanced (member, n + 1) else len > 0
	end;
	(* start at house 0, go through house n - 1 (house n cannot exist) *)
	fun f (member,n) = let
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
			fun houseBalance (member, n) = let 
				val len = length (List.filter (fn x => x = n) member)
				fun log2 (n,e) = let
					fun exp2 (e) = if e = 0 then 1 else 2 * exp2(e - 1)
					in if exp2 e + 1 > n then e else log2 (n, e + 1)
				end;
				val pdh = (length prefs) div houses
				in if len > 0 andalso abs (len - pdh) < log2 (pdh, 0) then (length prefs) else 0
			end
			(* fun houseBalance (member, n) = if abs (length (List.filter (fn x => x = n) member) - ((length prefs) div houses)) < 2 then 1 else 0; *)
			(* fun houseBalance (member, n) = if abs (length (List.filter (fn x => x = n) member) - ((length prefs) div houses)) < 1 then (length prefs) div houses else 0; *)
			(* fun houseBalance (member, n) = if abs (length (List.filter (fn x => x = n) member) - ((length prefs) div houses)) < 1 then 1 else 0; *)
			in if i <= (length prefs) andalso m = n then singeFits(member, n, i, 1) + houseBalance(member, i) + next else 0 + next
		end;
		in if n = houses then 0 else houseFit(member, member, n, 1) + f(member, n + 1)
	end
	(* do not bother computing fitness if some houses do not have at least 1 person *)
	in if not (balanced (member, n)) then 0 else f (member, n)
end;

(* unweighted fitness (for data comparison, not for computation) *)
fun flatFitness (member, n) = let
	(* start at house 0, go through house n - 1 (house n cannot exist) *)
	fun f (member,n) = let
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
			in if i <= (length prefs) then singeFits(member, n, i, 1) + next else 0 + next
		end;
		in if n = houses then 0 else houseFit(member, member, n, 1) + f(member, n + 1)
	end
	in f (member, n)
end;

(* inserts the a bit string into population when building the initial population *)
fun insert (nil, newMember) = [newMember]
(* if newMember is not better than current, do not insert it, else add the rest of the old after it except the last *)
  | insert (h::t, newMember) = if fitness (h,0) >= fitness (newMember,0) then h::insert(t, newMember) else newMember::complete(h::t)
(* once the new member has been inserted, put everything back except the last one *)
and complete (nil) = nil
  | complete (h::nil) = []
  | complete (h::t) = h::complete(t);

fun insertWhenFull (h::nil, newMember,n) = if fitness (h,0) >= fitness (newMember,0) then 
([h],n+2) else ([newMember],n+2)
(* if newMember is not better than current, do not insert it, else add the rest of the old after it except the last *)
  | insertWhenFull (h::t, newMember,n) = let
  	val tuple = insertWhenFull(t, newMember,n+2)
	in if fitness (h,0) >= fitness (newMember,0) then (h::(#1tuple),#2tuple) else (newMember::complete(h::t),n)
end;

fun createPop p = let
	fun genOrganism O = let
		fun housesList i = if i < houses - 1 then i::housesList(i + 1) else [i];
		fun randMem L = let
			val t = nextInt r
			(* in if length L = 5 then L else randMem (t::L) *)
			in if length L = length prefs then L else randMem (t::L)
		end;
		fun getVal (h::t,i) = if i = 0 then h else getVal(t,i-1);
		fun genSub nil = []
		  | genSub H = let
		    val nextH = Random.randRange (0, length H - 1);
		    val t = nextH r;
		    val y = getVal(H,t);
		    val newH = List.filter (fn x => x <> y) H
			in y::genSub(newH)
		end;
		fun genSmall (H, h) = let
			val nextH = Random.randRange (0, length H - 1);
		    val t = nextH r;
		    val y = getVal(H,t);
		    val newH = List.filter (fn x => x <> y) H
			in if h = 0 then [] else y::genSmall(newH, h - 1)
		end;
		val lenLeft = length prefs - length O
		in if lenLeft >= houses then genOrganism(O@(genSub (housesList 0))) else O@(genSmall(housesList 0, length prefs - length O))
	end;
	val mem = genOrganism []
	(* in if length p < 5 then createPop (insert (p,mem)) else p *)
	in if length p < maxPopLength then createPop (insert (p,mem)) else p
end;

val population = createPop [];
printTime();

fun getLast (h::nil) = h
  | getLast (p::ps) = getLast ps;

fun shouldMutate () = mutationChance r = 0;

fun flipVals (c::nil) = if shouldMutate() then [(c + 1) mod houses] else [c] 
  | flipVals (c::cs) = if shouldMutate() then ((c + 1) mod houses)::flipVals(cs) else c::flipVals(cs);

fun shouldMutateHarshly () = harshMutationChance r = 0;

fun flipValsHarshly (c::nil) = if shouldMutateHarshly() then [(c + 1) mod houses] else [c] 
  | flipValsHarshly (c::cs) = if shouldMutateHarshly() then ((c + 1) mod houses)::flipVals(cs) else c::flipVals(cs);

(* waits for 3 equal convergences of population or timeout *)
fun waitForIt (L,P,n) = let
	(* given a population, create and insert new children until a convergence is reached *)
	fun evolve (p,n) = let
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
		val tuple = insertWhenFull(p, reproduce (getParents(p, getParentNumbers ())),n)
		val childAdded = #1tuple;
		val newN = #2tuple
		in if fitness (hd childAdded,0) <> fitness(getLast childAdded,0) then evolve (childAdded,newN) else (childAdded,n)
	end;
	fun allEqual (nil) = true
	  | allEqual (a::nil) = true
	  | allEqual (a::b::nil) = a = b
	  | allEqual (a::b::c) = a = b andalso allEqual(b::c);
	val tuple = evolve (P,n);
	val newPop = #1tuple;
	val newFitnessCount = #2tuple;
	val newFinalMembers = (hd newPop)::L;
	fun editFinalMembers L = if allEqual newFinalMembers then L else [hd L];
	val trueNewFinalMembers = editFinalMembers newFinalMembers;
	fun massMutate (h::t) = h::(map flipValsHarshly t);
	val {sys:Time.time, usr:Time.time} = Timer.checkCPUTimer timer;
	val seconds = (real (LargeInt.toInt (Time.toMicroseconds usr)) + real (LargeInt.toInt(Time.toMicroseconds sys)) )/ 1000000.0
	(* stop at 3 equal convergences or timeout *)
	in if length trueNewFinalMembers = 3 orelse seconds > 600.0 then (hd trueNewFinalMembers, newFitnessCount) else waitForIt(massMutate(trueNewFinalMembers), newPop, newFitnessCount)
end;

fun addIdentifiersToAnswer (m::nil, i) = [(i,m)]
  | addIdentifiersToAnswer (m::ms, i) = (i,m)::addIdentifiersToAnswer(ms, i + 1);

fun formatHouses (answerMember:(int * int) list, n) = if n = houses then nil else (foldl (fn (x,s) => if #2x = n then s@[#1x] else s) nil answerMember)::formatHouses(answerMember, n + 1);

Control.Print.printLength := length prefs;

val (answer,callsToFitness) = waitForIt([], population,0);

val formattedAnswer = formatHouses ( addIdentifiersToAnswer (answer, 1), 0);

val happiness = fitness (answer, 0);

val finalTime = printTime();

Control.Print.printLength := 10;