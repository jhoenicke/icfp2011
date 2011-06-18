open Engine
include Engine

module Strategy = struct

type macros =
     SimpleStep of move         (* m: do the simple move m *)
   | SetNumber of (int * int)   (* r n: set the slot r to number n *)
   | SetCard of (int * card)    (* r c: set the slot r to card c *)
   | ApplySlots of (int * int)  (* r1 r2: set the slot r1 to App(r1,r2) *)
   | FreeReg of (int)           (* r: free register r *)
   | CopyReg of (int * int)     (* d s: copy slot s into slot d *)
   | DoubleCard of (int)        (* r: slot[r].card  := 
                                           S slot[r].card slot[r].card *)
   | UseZombie of (int * int)
   | PrepareBinApply of (int)   (* r: apply K and S to r to prepare bin apply *)
   | BinApply of (int * card)   (* r c: apply slot r to func c and arg c *)
   | ApplyCard of (int * card)  (* r c: apply slot r to card c *)

let isfree = 
  let arr = Array.make 256 true in
  arr.(0) <- false;
  arr.(1) <- false;
  arr.(2) <- false;
  arr.(3) <- false; arr

let alloc_reg () = 
  let rec find_free n = if (isfree.(n)) then n else find_free (n+1) in
  let reg = find_free 1 in
  isfree.(reg) <- false; reg

let is_simple_card = function
   Val 0     -> true
 | Val _     -> false
 | App (_,_) -> false
 | _         -> true

let apply0 card =
  App(App(S, card),App(App(S,Get), I))

let rec cost_step_number i n =
  let rec num_steps n = 
    if (n == 0) then 2
    else (num_steps (n / 2)) + 1 + (n mod 2) in

  if (i > n) then num_steps n
  else if (i < n/2) then 1 + cost_step_number i (n/2)
  else min (n - i) (num_steps n)

let rec cost_step_number_card c n =
  match c with 
    Val i -> cost_step_number i n
  | I     -> 1 + cost_step_number 0 n
  | _     -> 2 + cost_step_number 0 n

let rec step_number r i n =
  let rec num_steps n = 
    if (n == 0) then 2
    else (num_steps (n / 2)) + 1 + (n mod 2) in
  
  if (i < n/2) then (step_number r i (n/2))
  else if (i != 0 && i == n/2) then AppCS (Dbl, r)
  else if (n-i > 0 && n - i < 2) then AppCS (Succ, r)
  else if (n-i > 0 && n - i < num_steps n) then AppCS (Succ, r)
  else AppCS (Put, r)

let rec step_strategy prepon oppon = function
  SetNumber(r,n) :: tail -> 
     let oldcard = get_card prepon r in
     if (oldcard = Val n) then (step_strategy prepon oppon tail) else
     (match oldcard with
       I     -> (AppSC (r, Val 0), SetNumber(r,n) :: tail)
     | Val i -> ((step_number r i n), SetNumber(r,n) :: tail)
     | _     -> (AppCS (Put, r), SetNumber(r,n) :: tail)
     )
| ApplyCard(r, c) :: tail ->
     if (is_simple_card c) then AppSC(r,c), tail
     else step_strategy prepon oppon 
                (PrepareBinApply(r) :: BinApply(r,c) :: tail)
| PrepareBinApply(r) :: tail ->
     AppCS(K, r), SimpleStep(AppCS(S,r)) :: tail
| BinApply(r, c) :: tail ->
     let fallback = step_strategy prepon oppon
                (SetCard(0, c) :: BinApply(r, App(Get, (Val 0))) :: tail) in
     let binapply c1 c2 =
                AppSC(r, c1), SimpleStep(AppSC(r,c2)) :: tail in
     (match c with 
       Val 1 -> binapply Succ (Val 0)
     | App(f,a) -> if (is_simple_card f && is_simple_card a) then
                    binapply f a
                 else
                    fallback
     | _ -> fallback)
| ApplySlots(r1,r2) :: tail ->
     if (r2 != 0) then 
        step_strategy prepon oppon
                      (SetNumber(0, r2) :: SimpleStep (AppCS(Get,0)) :: 
                       ApplySlots (r1, 0) :: tail)
     else
        step_strategy prepon oppon
                      (PrepareBinApply(r1) :: 
                       BinApply(r1, App(Get, (Val 0))) :: tail)
| SimpleStep step :: tail -> (step, tail)
| FreeReg(r) :: tail ->
         isfree.(r) <- true ; step_strategy prepon oppon tail
| CopyReg(d, s) :: tail ->
     step_strategy prepon oppon (SetNumber(d,s) :: SimpleStep (AppCS(Get, d)) :: tail)
| DoubleCard(r) :: tail ->
     step_strategy prepon oppon 
       (SetNumber(0,r) :: SimpleStep (AppCS(Get, 0)) :: 
	SimpleStep(AppCS(S, r)) :: ApplySlots(1, 0) :: tail)
| SetCard(r, c) :: tail -> 
   if (get_card prepon r = c) then step_strategy prepon oppon tail
   else (match c with
     Val n -> step_strategy prepon oppon (SetNumber(r, n) :: tail)
   | App (c1, c2) -> step_strategy prepon oppon
         (if is_simple_card c1 then
            (SetCard(r, c2) :: SimpleStep(AppCS (c1,r)) :: tail)
          else if is_simple_card c2 then
            (SetCard(r, c1) :: SimpleStep(AppSC (r,c2)) :: tail)
          else if (r != 0) then
            (SetCard(r, App(App(S, App(K, c1)), Get)) :: 
             SetCard(0, c2) :: SimpleStep(AppSC(r, Val 0)) :: tail)
          else let newr = alloc_reg () in
            (SetCard(newr, App(c1,c2)) :: SetNumber(0, newr) ::
             SimpleStep(AppCS (Get, 0)) :: FreeReg(newr) :: tail))
   | _ -> if (get_card prepon r != I) then
             AppCS (Put, r), (SimpleStep (AppSC(r, c)) :: tail)
          else
             AppSC(r, c), tail)
| UseZombie(s, r) :: tail -> 
   let vital = get_vitality oppon s in
   step_strategy prepon oppon 
      (SetCard(2, App(App(S,App(K,App(App(Help, Val s), Val s))), 
		       App(K,Val (vital*2/3)))) ::
      SetCard(1, App(App(Zombie, Val r),App(Get, Val 2))) ::
      UseZombie(((s+1) mod 256), r)::tail)
| _ -> raise (Failure "Unimplemented Strategy")

let binapply c = App(S, App(K, c))

let global_strategy = ref 
    [ 
      (* Attack + Attack *)
      SetCard(0, Val 2);
      SetCard(1, App(App(Attack, App(Get, Val 0)), Val 0));
      SetCard(0, Val 3);
      SetCard(2, App(App(Attack, App(Get, Val 0)), Val 0));
      SetCard(0, Val (6*1024));
      ApplyCard(1, App(Get, Val 0));
      ApplyCard(2, App(Get, Val 0));
   (* Help + Attack:
      SetCard(1, App(Help, Val 2));
      SetCard(0, Val 3);
      ApplyCard(1, App(Get, Val 0));
      SetCard(2, App(Attack, App(Get, Val 0)));
      ApplyCard(2, Val 0);
      ApplyCard(1, Val (6*1024));
      ApplyCard(2, Val (12*1024));*)
      UseZombie(0,0)
    ]


let step_revive prepon oppon strategy =
    let rec findbestreg start reg best = 
       if (start == 256) then best else
       let newbest = if not (isfree.(best)) then start
           else if not (isfree.(start)) then best
           else if (get_vitality prepon start <= 0) then best
           else if (get_vitality prepon best <= 0) then start
           else let bestcard = get_card prepon best in
                let startcard =  get_card prepon start in
	        if (cost_step_number_card bestcard reg
                    <= cost_step_number_card startcard reg)
                then best else start in
       findbestreg (start+1) reg newbest in

    let revive_reg reg  =
       let tmpreg = findbestreg 0 reg 0 in
       match get_card prepon tmpreg with
         Val i   -> if i == reg then  AppCS(Revive, tmpreg), strategy
                    else              step_number tmpreg i reg, strategy
       | I       -> AppSC(tmpreg, Val 0), strategy
       | _       -> AppCS(Put, tmpreg), strategy in

    let rec reviveloop reg  =
        if (reg == 256) then
           step_strategy prepon oppon strategy
        else if (not (isfree.(reg)) && (get_vitality prepon reg <= 0)) then
           revive_reg reg
        else
           reviveloop (reg+1) in

    reviveloop 0

let play_strategy prepon oppon =
    match step_revive prepon oppon !global_strategy with
       (move,tail) -> global_strategy := tail; move

end
