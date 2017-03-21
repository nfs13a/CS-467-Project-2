(* for keeping track of program run time *)
val timer = Timer.startCPUTimer();

fun printTime () = 
	let	val {sys:Time.time, usr:Time.time} = Timer.checkCPUTimer timer
	in Real.toString ((real (LargeInt.toInt (Time.toMicroseconds usr)) + real (LargeInt.toInt(Time.toMicroseconds sys)) )/ 1000000.0) ^ " seconds"
end;

fun readlist (infile : string) = let
  val ins = TextIO.openIn infile
  fun loop ins =
   case TextIO.inputLine ins of
      SOME line => line :: loop ins
    | NONE      => []
in loop ins before TextIO.closeIn ins
end;

val fileInput = readlist "F2.csv";

(* max capacity of sack *)
val SOME cap = Int.fromString (hd fileInput);

fun toGlobes (nil) = []
  | toGlobes (a::b::c::d) = 
	let val SOME C = Int.fromString c;
  		val SOME B = Int.fromString b;
  		val A = str (hd (explode a))
  	in (C, B, A)::toGlobes d 
  end;

(* (value, cost, name) *)
val globes = toGlobes (tl fileInput);

(* helper variables for random number generation *)
val nextInt = Random.randRange (0,1);	(* for initial population generation *)
val nextChild = Random.randRange (1, length globes - 1);	(* the number of elements from left parent *)
val mutationChance = Random.randRange (0, 199);	(* .005 chance of any given bit being flipped *)
val harshMutationChance = Random.randRange (0, 4);	(* .2 chance of any given bit being flipped upon convergence *)
val parentOptions = Random.randRange (0, length globes - 1);	(* for picking parents of next child *)
val r = Random.rand (1,1);	(* rand for seed for random number generation *)

(* combine bit string with globes list *)
fun addBitToList(nil, nil) = []
  | addBitToList(b::bt:int list, g::gt:(int * int * string) list) = (#1g, #2g, #3g, b)::addBitToList(bt, gt);

(* return sum of values of globes with corresponding 1 in bit string *)
(* using pattern matching and recursion *)
fun getValueFromBits (nil, nil) = 0
  | getValueFromBits (b::bt, g::gt:(int * int * string) list) = if b = 1 then #1g + getValueFromBits(bt, gt) else getValueFromBits(bt, gt);

(* return sum of values of globes with corresponding 1 in bit string *)
(* using higher order functions *)
fun getValueFromBits (B, G:(int * int * string) list) =
	let val newList = addBitToList(B,G)
	in foldl (fn (x,s) => if #4x = 1 then #1x + s else s) 0 newList
end;

(* return some of costs of globes with corresponding 1 in bit string *)
(* using pattern matching and recursion *)
fun getCostFromBits (nil, nil) = 0
  | getCostFromBits (b::bt, g::gt:(int * int * string) list) = if b = 1 then #2g + getCostFromBits(bt, gt) else getCostFromBits(bt, gt);

(* return some of costs of globes with corresponding 1 in bit string *)
(* using higher order functions *)
fun getCostFromBits (B, G:(int * int * string) list) =
	let val newList = addBitToList(B,G)
	in foldl (fn (x,s) => if #4x = 1 then #2x + s else s) 0 newList
end;


(* return list of name of globes with corresponding 1 in bit string *)
(* using pattern matching and recursion *)
fun getItemsFromBits (nil, nil) = []
  | getItemsFromBits (b::bt, g::gt:(int * int * string) list) = if b = 1 then #3g::getItemsFromBits(bt, gt) else getItemsFromBits(bt, gt);

(* return list of name of globes with corresponding 1 in bit string *)
(* using higher order functions *)
fun getItemsFromBits (B, G:(int * int * string) list) =
	let val newList = addBitToList(B,G)
	in foldl (fn (x,s) => if #4x = 1 then s@[#3x] else s) [] newList
end;

(* simple fitness function - 0 if cost > capacity, else the value of the member *)
fun fitness member = if getCostFromBits(member, globes) > cap then 0 else getValueFromBits(member, globes);

(* inserts the a bit string into population when building the initial population *)
fun insert (nil, newMember) = if fitness newMember > 0 then [newMember] else nil
(* if newMember is not better than current, do not insert it, else add the rest of the old after it except the last *)
  | insert (h::t, newMember) = if fitness h >= fitness newMember then h::insert(t, newMember) else newMember::complete(h::t)
(* once the new member has been inserted,  *)
and complete (nil) = nil
  | complete (h::nil) = []
  | complete (h::t) = h::complete(t);

fun insertWhenFull (h::nil, newMember, n) = if fitness h >= fitness newMember then ([h], n + 2) else ([newMember], n + 2)
(* if newMember is not better than current, do not insert it, else add the rest of the old after it except the last *)
  | insertWhenFull (h::t, newMember, n) = 
  	let val tuple = insertWhenFull(t, newMember, n + 2)
	in if fitness h >= fitness newMember then (h::(#1tuple), #2tuple) else (newMember::complete(h::t), n)
	end;

fun createPop p =
	let fun randMem L =
		let val t = nextInt r
		(* in if length L = 5 then L else randMem (t::L) *)
		in if length L = length globes then L else randMem (t::L)
		end;
	val mem = randMem []
	(* in if length p < 5 then createPop (insert (p,mem)) else p *)
	in if length p < length globes then createPop (insert (p,mem)) else p
	end;

val population = createPop [];
printTime();

fun getLast (h::nil) = h
  | getLast (p::ps) = getLast ps;

fun shouldMutate () = mutationChance r = 0;

fun flipVals (c::nil) = if shouldMutate() then [((c + 3) mod 2)] else [c] 
| flipVals (c::cs) = if shouldMutate() then ((c + 3) mod 2)::flipVals(cs) else c::flipVals(cs);

fun shouldMutateHarshly () = harshMutationChance r = 0;

fun flipValsHarshly (c::nil) = if shouldMutateHarshly() then [((c + 3) mod 2)] else [c] 
| flipValsHarshly (c::cs) = if shouldMutateHarshly() then ((c + 3) mod 2)::flipVals(cs) else c::flipVals(cs);

(* waits for 3 equal convergences of population or timeout *)
fun waitForIt (L,P,n) =
	(* given a population, create and insert new children until a convergence is reached *)
	let fun evolve (p, n) =
		(* given two parents, produce a new child *)
		let fun reproduce (pL, pR) =
			(* random number between  *)
			let val t = nextChild r;
				fun headParent (p::ps,n) = if n > 1 then p::headParent(ps, n - 1) else [p];
				fun tailParent (p::ps,n) = if n > 1 then tailParent(ps,n - 1) else ps;
				fun mutation c = flipVals (c)
			in mutation ((headParent(pL,t)) @ (tailParent(pR,t)))
		end;
			fun getParentNumbers () = 
				let val left = parentOptions r;
					val right = parentOptions r
				in if left = right then getParentNumbers () else (left, right)
			end;
			fun getParents (p, (l, r)) =
				let fun getAParent (p::ps,n) = if n = 0 then p else getAParent (ps, n - 1)
				in (getAParent (p,l), getAParent (p,r))
			end;
			val tuple = insertWhenFull(p, reproduce (getParents(p, getParentNumbers () )), n);
			val childAdded = #1tuple;
			val newN = #2tuple;
		in if hd childAdded <> getLast childAdded then evolve (childAdded, newN) else (childAdded, n)
	end;
		fun allEqual (nil) = true
		  | allEqual (a::nil) = true
		  | allEqual (a::b::nil) = a = b
		  | allEqual (a::b::c) = a = b andalso allEqual(b::c);
		val evolutionResult = evolve (P, n);
		val newPop = #1evolutionResult;
		val newFitnessCount = #2evolutionResult;
		val newFinalMembers = (hd newPop)::L;
		fun editFinalMembers L = if allEqual newFinalMembers then L else [hd L];
		val trueNewFinalMembers = editFinalMembers newFinalMembers;
		fun massMutate (h::t) = h::(map flipValsHarshly t);
		val {sys:Time.time, usr:Time.time} = Timer.checkCPUTimer timer;
		val seconds = (real (LargeInt.toInt (Time.toMicroseconds usr)) + real (LargeInt.toInt(Time.toMicroseconds sys)) )/ 1000000.0
	(* stop at 3 equal convergences or timeout *)
	in if length trueNewFinalMembers = 3 orelse seconds > 600.0 then (hd trueNewFinalMembers, newFitnessCount) else waitForIt(massMutate(trueNewFinalMembers), newPop, newFitnessCount)
end;

Control.Print.printLength := length globes;

val (answer,callsToFitness) = waitForIt([], population, 0);

val sack = getItemsFromBits(answer,globes);

getValueFromBits (answer,globes);

getCostFromBits (answer,globes);

printTime();

Control.Print.printLength := 10;