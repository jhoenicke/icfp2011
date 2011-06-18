open Engine
include Engine

module Strategy = struct

let ( *+ ) c1 c2 = App(c1,c2)

type task =
     Code of (slots -> slots-> task list -> task list)
   | Move of move
   | Yield

let tasks = Array.make 4 ([] : task list)

let isfree = 
  let arr = Array.make 256 true in
  arr.(0) <- false;
  arr.(1) <- false;
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
   (*prerr_string ("set_card " ^ (string_of_int (r)) ^ "," ^ (string_of_card c));
   prerr_newline ();*)
   if (get_card prepon r = c) then tail
   else match c with
     Val n -> set_number r n prepon oppon tail
   | App (c1, c2) -> 
         if is_simple_card c1 then
             set_card r c2 prepon oppon (Move(AppCS(c1, r)) :: tail)
         else if r != 0 || is_binary_card c2 then
             set_card r c1 prepon oppon (Code(apply_card r c2) :: tail)
         else let newr = alloc_reg () in
             Code(set_card newr c) :: Code(set_card 0 (Get *+ Val newr)) :: 
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

let rec find_dead_reg prepon start best = 
   if (start == 256) then best else
   find_dead_reg prepon (start+1)
      (if (not (isfree.(best))) then start
       else if (not (isfree.(start))) then best
       else if (get_vitality prepon start <= 0) then start
       else if (get_vitality prepon best <= 0) then best
       else start)

let attack reg prepon oppon tail =
  let rec findattackreg start best = if (start == 256) then best else
     findattackreg (start+1)
        (if (get_vitality prepon start > get_vitality prepon best) then start
         else best) in
  let rec findvitality start max min =
     if (2*start > (max *8/10)) then start
     else if (start*9/10 > min) then start
     else findvitality (2*start) max min in

  let srcreg = findattackreg 3 2 in
  let vitality = findvitality 1 (get_vitality prepon srcreg) (get_vitality oppon reg) in
  Code(set_card 0 (Attack *+ Val srcreg *+ Val (255-reg) *+ Val vitality)) ::
    tail
  
let rec install_zombie installer reg card prepon oppon tail =
  let rec retry_zombie tmp prepon oppon tail = 
    if (get_vitality oppon reg <= 6) then
      Move(AppSC(tmp, Val  0)) :: tail
    else if (get_vitality oppon reg > 24) then (
      isfree.(tmp) <- true; 
      install_zombie installer reg card prepon oppon tail
    ) else
      Code(set_card 1 (Get *+ Val tmp)) :: 
      Move(AppSC(1, Val 0)) :: Code(retry_zombie tmp) :: tail in
  
  
  if (get_vitality oppon reg > 24) then
    Code(attack reg) :: Code(install_zombie installer reg card) :: tail
  else (
    let t1 = alloc_reg () in
    let prepare = (Get *+ Val installer) *+ card in
    if (reg < 254) then
      Code(set_card t1 (S *+ (K *+ prepare) *+ Get)) ::
        Code(set_card 0 (Val (255-reg))) :: Code(retry_zombie t1) :: 
	Code(free_reg t1) :: tail
    else if (reg == 254) then
      Code(set_card t1 (S *+ (K *+ prepare) *+ Succ))
      :: Code(retry_zombie t1) :: Code(free_reg t1) :: tail
    else
      Code(set_card t1 prepare) :: Code(retry_zombie t1) :: 
	Code(free_reg t1) :: tail
  )

let compvital vital = 
  let rec approx start =
    if (2 * start <= vital) then (approx (2*start))
    else if (start * 19/10 > vital+100) then start
    else (start * 3 / 2) in
  approx 1

let rec use_zombie installer s zombiereg prepon oppon tail = 
   let vital = compvital (get_vitality oppon s) in
   let codereg = alloc_reg () in
   Code(set_card codereg 
          (S *+ (K *+ (Help *+ Val s *+ Val s))
             *+ (K *+ (Val vital)))) ::
     Code(install_zombie installer zombiereg (Get *+ Val codereg)) ::
     Code(free_reg codereg) ::
     Code(use_zombie installer ((s+1) mod 256) zombiereg) :: tail

let rec watch_double_zombie installer hisdead codereg prepon oppon tail = 
  if (get_vitality oppon hisdead < 0) then 
    Yield :: Code(watch_double_zombie installer hisdead codereg) :: tail
  else (
    (*prerr_string ("reinstall double zombie " ^ 
                  string_of_int installer ^ " " ^
                  string_of_int hisdead ^ " " ^
                  string_of_int codereg); prerr_newline ();
    prerr_slots oppon;*)
    Code(install_zombie installer hisdead (Get *+ Val codereg)) :: 
      Code(watch_double_zombie installer hisdead codereg) :: tail
  )

let start_watcher installer hisdead codereg prepon oppon tail =
  tasks.(1) <- [Code(watch_double_zombie installer hisdead codereg)]; tail

let double_zombie prepon oppon tail =
   let zombiereg  = alloc_reg () in
   let zombieinstaller = alloc_reg () in
   let backzombie = alloc_reg () in
   let mydeadreg  = find_dead_reg prepon 1 0 in
   let hisdeadreg = 255 in

   Code(set_card backzombie
        (S *+ (K *+ (Zombie *+ Val (255 - mydeadreg)))
           *+ (S *+ (K *+ Copy) *+ (K *+ Val zombiereg)))) ::
   Code(set_card zombiereg
        (S *+ (K *+ (Zombie *+ Val (255-hisdeadreg)))
           *+ (K *+ (S *+ (S *+ (K *+ Inc) *+ (K *+ Val 0))
                       *+ (Get *+ Val backzombie))))) ::
   let attack =
     let vital = get_vitality oppon 0 in
     let snd_zombiereg = 254 in
       Code(set_card 1  (Zombie *+ Val (255-hisdeadreg) *+
                        (S *+ (S *+ (K *+ (Help *+ Val 0 *+ Val 0))
                                 *+ (K *+ Val (compvital vital)))
                           *+ (Get *+ Val backzombie)))) ::
       Code(set_card zombieinstaller 
	    (S *+ (K *+ (S *+ (S *+ (S *+ Dec *+ Dec) 
		     *+ (S *+ (S *+ Dec *+ Dec) *+ (S *+ Dec *+ Dec)))))
             *+ (S *+ (K *+ (S *+ Zombie)) *+ K)))
       :: Code(start_watcher zombieinstaller hisdeadreg backzombie)
       :: Code(use_zombie zombieinstaller 1 snd_zombiereg) :: tail in
	    
   let myvital = get_vitality prepon mydeadreg in
   if (myvital > 0) then
       Code(set_card 1 (Attack *+ Val mydeadreg *+ Val hisdeadreg *+ Val myvital)) :: attack
   else
       attack


let binapply c = App(S, App(K, c))

let main_strategy prepon oppon tail =
   let tmpreg = alloc_reg() in
   (* Attack + Attack *)
   Code(set_card 0 (Val 2)) ::
   Code(set_card 1 (App(App(Attack, App(Get, Val 0)), Val 0))) ::
   Code(set_card 0 (Val 3)) ::
   Code(set_card tmpreg (App(App(Attack, App(Get, Val 0)), Val 0))) ::
   Code(set_card 0 (Val (6*1024))) ::
   Code(apply_card 1 (App(Get, Val 0))) ::
   Code(apply_card tmpreg (App(Get, Val 0))) ::
   Code(free_reg tmpreg) ::
   Code(double_zombie) :: tail


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
