open Engine
include Engine

module Strategy = struct

type task =
     Code of (slots -> slots-> task list -> task list)
   | Move of move
   | Yield

let tasks = Array.make 4 ([] : task list)

let isfree = 
  let arr = Array.make 256 true in
  arr.(0) <- false;
  arr.(1) <- false;
  arr.(2) <- false;
  arr.(3) <- false; 
  arr

let alloc_reg () = 
  let rec find_free n = if (isfree.(n)) then n else find_free (n+1) in
  let reg = find_free 1 in
  isfree.(reg) <- false; reg

let is_simple_card = function
   Val 0     -> true
 | Val _     -> false
 | App (_,_) -> false
 | _         -> true

let is_binary_card = function
   Val 1       -> true
 | App (c1,c2) -> is_simple_card(c1) && is_simple_card(c2)
 | _           -> false

let apply0 card =
  App(App(S, card),App(App(S,Get), I))

let rec cost_set_number c n =
  let rec cost_set_number_val i n =
    let rec num_steps n = 
      if (n == 0) then 2
      else (num_steps (n / 2)) + 1 + (n mod 2) in

    if (i > n) then num_steps n
    else if (i < n/2) then 1 + cost_set_number_val i (n/2)
    else min (n - i) (num_steps n) in

  match c with 
    Val i -> cost_set_number_val i n
  | I     -> 1 + cost_set_number_val 0 n
  | _     -> 2 + cost_set_number_val 0 n

(**
 * Strategy free_reg: free register r.
 *)
let free_reg r prepon oppon tail =
  isfree.(r) <- true; tail

(**
 * Strategy set_number: set register r to number n.
 *)
let rec set_number r n prepon oppon tail =
  let rec num_steps n = 
    if (n == 0) then 2
    else (num_steps (n / 2)) + 1 + (n mod 2) in

  match (get_card prepon r) with
  Val i -> if (i < n/2) then 
                set_number r (n/2) prepon oppon (Code(set_number r n) :: tail)
           else if (i == n) then tail
           else if (i != 0 && i == n/2) then 
                Move(AppCS (Dbl, r)) :: Code(set_number r n) :: tail
           else if (i < n &&
                    (n - i < 3 || n - i < num_steps n)) then 
                Move(AppCS (Succ, r)) :: Code(set_number r n) :: tail
           else
                Move(AppCS (Put, r)) :: Code(set_number r n) :: tail
  | I   -> Move(AppSC (r, Val 0)) :: Code(set_number r n) :: tail
  | _   -> Move(AppCS (Put, r)) :: Code(set_number r n) :: tail


(**
 * Strategy set_card: set register r to card c.
 *
 * TODO search for reusable code.
 *)
let rec set_card r c prepon oppon tail =
   if (get_card prepon r = c) then tail
   else match c with
     Val n -> set_number r n prepon oppon tail
   | App (c1, c2) -> 
         if is_simple_card c1 then
             set_card r c2 prepon oppon (Move(AppCS(c1, r)) :: tail)
         else if r != 0 || is_binary_card c2 then
             set_card r c1 prepon oppon (Code(apply_card r c2) :: tail)
         else let newr = alloc_reg () in
             Code(set_card newr c) :: Code(set_card 0 (App (Get, Val 0))) :: 
             Code(free_reg newr) :: tail
   | _ -> if (get_card prepon r = I) then 
            Move(AppSC(r, c)) :: tail
          else
            Move(AppCS(Put, r)) :: Code(set_card r c) :: tail

and apply_binary r c prepon oppon tail =
   let fallback () = 
     if r == 0 then 
       raise (Failure "Strategy apply_card on reg 0 with non-trivial card")
     else
       set_card 0 c prepon oppon 
             (Code(apply_binary r (App (Get, Val 0))) :: tail) in

   match c with
     Val 1      -> Move(AppSC(r, Succ)) :: Move(AppSC(r, Val 0)) :: tail
   | App(c1,c2) -> 
            if (is_simple_card c1 && is_simple_card c2)
            then Move(AppSC(r, c1)) :: Move(AppSC(r, c2)) :: tail 
            else fallback ()
   | _ -> fallback ()

and apply_card r c prepon oppon tail = 
   if (is_simple_card c) then
       Move(AppSC(r, c)) :: tail
   else Move(AppCS(K, r)) :: Move(AppCS(S, r)) :: 
       Code(apply_binary r c) :: tail

let apply_slots r1 r2 = 
   apply_card r1 (App(Get, Val r2))

let rec use_zombie s r prepon oppon tail = 
   let vital = get_vitality oppon s in
      Code(set_card 2 (App(App(S,App(K,App(App(Help, Val s), Val s))), 
		          App(K,Val (vital*2/3))))) ::
      Code(set_card 1 (App(App(Zombie, Val r),App(Get, Val 2)))) ::
      Code(use_zombie ((s+1) mod 256) r) :: tail

let binapply c = App(S, App(K, c))

let main_strategy prepon oppon tail =
   (* Attack + Attack *)
   Code(set_card 0 (Val 2)) ::
   Code(set_card 1 (App(App(Attack, App(Get, Val 0)), Val 0))) ::
   Code(set_card 0 (Val 3)) ::
   Code(set_card 2 (App(App(Attack, App(Get, Val 0)), Val 0))) ::
   Code(set_card 0 (Val (6*1024))) ::
   Code(apply_card 1 (App(Get, Val 0))) ::
   Code(apply_card 2 (App(Get, Val 0))) ::
   Code(use_zombie 0 0) :: tail

let rec revive prepon oppon tail =
    let ntail = Code(revive) :: tail in
    let rec findbestreg start reg best = 
       if (start == 256) then best else
       let newbest = if not (isfree.(best)) then start
           else if not (isfree.(start)) then best
           else if (get_vitality prepon start <= 0) then best
           else if (get_vitality prepon best <= 0) then start
           else let bestcard = get_card prepon best in
                let startcard =  get_card prepon start in
	        if (cost_set_number bestcard reg
                    <= cost_set_number startcard reg)
                then best else start in
       findbestreg (start+1) reg newbest in

    let revive_reg reg  =
       let tmpreg = findbestreg 0 reg 0 in
       List.hd (set_number tmpreg reg 
                      prepon oppon [Move(AppCS(Revive, tmpreg))]) :: ntail in

    let rec reviveloop reg  =
        if (reg == 256) then
           Yield :: ntail
        else if (not (isfree.(reg)) && (get_vitality prepon reg <= 0)) then
           revive_reg reg
        else
           reviveloop (reg+1) in

    reviveloop 0

let inittask = 
   tasks.(0) <- [ Code(revive) ];
   tasks.(3) <- [ Code(main_strategy) ]; 
   tasks

let play_strategy prepon oppon =
    let rec apply_task i =
       let rec run_task = function
           [] -> apply_task (i+1)
         | Move(m) :: tail ->   tasks.(i) <- tail ; m
         | Code(c) :: tail ->   run_task (c prepon oppon tail)
         | Yield   :: tail ->   tasks.(i) <- tail ; apply_task(i+1) in
       run_task tasks.(i) in

    apply_task 0

end
