val globes = [(117,151),(181,83),(183,7),(147,11),(65,144),(11,139),(37,121),(157,44),(129,61),(51,166),(46,117),(5,94),(156,153),(136,1),(62,118),(93,149),(155,176),(189,54),(74,90),(181,125),(110,78),(41,35),(97,75),(24,197),(75,183),(80,54),(142,120),(59,156),(38,48),(49,12),(172,74),(62,108),(121,29),(157,1),(38,140),(165,89),(105,37),(112,137),(11,68),(72,10),(140,13),(152,46),(192,159),(172,16),(129,108),(162,105),(114,81),(70,150),(154,200),(71,194),(129,152),(137,130),(125,26),(119,135),(196,7),(115,20),(121,65),(66,73),(139,196),(63,95),(104,153),(59,99),(116,117),(182,198),(182,59),(115,42),(65,162),(106,178),(197,111),(35,42),(155,154),(110,3),(107,200),(15,139),(114,55),(99,50),(45,134),(59,179),(175,142),(142,58),(33,198),(174,167),(186,105),(119,144),(117,178),(136,91),(147,188),(137,74),(3,195),(117,18),(20,109),(182,81),(80,125),(61,6),(147,187),(172,138),(187,38),(194,133),(64,122),(170,56)];

val cap = 5127;

val finalMember = []

(* val population = []; *)

(* helper variables for random number generation *)
val nextInt = Random.randRange (0,1);
val nextChild = Random.randRange (1,99);	(* the number of elements from left parent *)
val mutationChance = Random.randRange (0, 99);
val r = Random.rand (1,1);

(* valid indexes: 0..99 *)
fun getGlobeN (n,L) = if n = 0 then hd L else getGlobeN(n-1,tl L);

fun getValueFromBits (nil, nil) = 0
  | getValueFromBits (b::bt, g::gt:(int * int) list) = if b = 1 then #1g + getValueFromBits(bt, gt) else getValueFromBits(bt, gt);

fun getCostFromBits (nil, nil) = 0
  | getCostFromBits (b::bt, g::gt:(int * int) list) = if b = 1 then #2g + getCostFromBits(bt, gt) else getCostFromBits(bt, gt);

fun fitness member = if getCostFromBits(member, globes) > cap then 0 else getValueFromBits(member, globes);

fun insert (nil, newMember) = if fitness newMember > 0 then [newMember] else nil
(* if newMember is not better than current, do not insert it, else add the rest of the old after it except the last *)
  | insert (h::t, newMember) = if fitness h >= fitness newMember then h::insert(t, newMember) else newMember::complete(h::t)
and complete (nil) = nil
  | complete (h::nil) = []
  | complete (h::t) = h::complete(t);

fun insertWhenFull (h::nil, newMember) = if fitness h >= fitness newMember then [h] else [newMember]
(* if newMember is not better than current, do not insert it, else add the rest of the old after it except the last *)
  | insertWhenFull (h::t, newMember) = if fitness h >= fitness newMember then h::insert(t, newMember) else newMember::complete(h::t)

fun createPop p =
	let fun randMem L =
		let val t = nextInt r
		in if length L = 100 then L else randMem (t::L)
		end;
	val mem = randMem []
	in if length p < 100 then createPop (insert (p,mem)) else p
	end;

val population = createPop [];

(* while first <> last *)
	(* create a child *)
	(* insert child *)

fun getLast (h::nil) = h
  | getLast (p::ps) = getLast ps;

fun waitForIt (L,P) =
	let fun evolve p =
		let fun reproduce (pL, pR) =
			let val t = nextChild r;
				val mut = mutationChance r;
				fun headParent (p::ps,n) = if n > 1 then p::headParent(ps, n - 1) else [p];
				fun tailParent (p::ps,n) = if n > 1 then tailParent(ps,n - 1) else ps;
				fun mutation (c, mc) = 
					let fun shouldMutate mc = mc = 0;
						fun flipVal (nil, _) = []
						  | flipVal (c::cs, n) = if n = 0 then ((c + 3) mod 2)::flipVal(cs, n - 1) else c::flipVal(cs, n - 1)
					in if shouldMutate mc then flipVal (c, mutationChance r) else c
					end;
			in mutation ((headParent(pL,t)) @ (tailParent(pR,t)), mut)
			end;
			fun getParentNumbers () = 
				let val left = mutationChance r;
					val right = mutationChance r
				in if left = right then getParentNumbers () else (left, right)
				end;
			fun getParents (p, (l, r)) =
				let fun getAParent (p::ps,n) = if n = 0 then p else getAParent (ps, n - 1)
				in (getAParent (p,l), getAParent (p,r))
				end;
			val childAdded = insertWhenFull(p, reproduce (getParents(p, getParentNumbers () )))
		in if hd childAdded <> getLast childAdded then evolve childAdded else childAdded
		end;
		fun allEqual (nil) = true
		  | allEqual (a::nil) = true
		  | allEqual (a::b::nil) = a = b
		  | allEqual (a::b::c) = a = b andalso allEqual(b::c);
		val newP = evolve P;
		val newFinalMembers = (hd newP)::L;
		fun editFinalMembers L = if allEqual newFinalMembers then L else [hd L];
		val trueNewFinalMembers = editFinalMembers newFinalMembers
	in if List.length trueNewFinalMembers = 3 then hd trueNewFinalMembers else waitForIt(trueNewFinalMembers, newP)
	end;

val answer = waitForIt([], population);

getValueFromBits (answer,globes);

getCostFromBits (answer,globes);