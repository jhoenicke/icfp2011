open Engine
include Engine

module Strategy = struct

let ( *+ ) c1 c2 = App(c1,c2)

type task =
     Code of (slots -> slots-> task list -> task list)
   | Move of move
   | Yield

let tasks = Array.make 4 ([] : task list)

let rec buildrec card n = if (n == 1) then card else
    (S *+ (buildrec card (n - 1)) *+ card)

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

    if (i == n) then 0
    else if (i > n) then num_steps n
    else if (i <= n/2) then cost_set_number_val i (n/2) + 1 + (n mod 2)
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
         else if r != 0 || is_simple_card c2 || is_binary_card c2 then
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

let double_dec reg prepon oppon tail =
  Code(set_card 0 (Get *+ Val reg)) :: 
    Move(AppCS(S, reg)) :: Code(apply_card reg (Get *+ Val 0)) :: tail
  
let rec install_zombie installer reg card prepon oppon tail =
  let rec retry_zombie tmp prepon oppon tail = 
    if (get_vitality oppon reg < 320) then
      Move(AppSC(tmp, Val  0)) :: tail
    else if (get_vitality oppon reg > 1000) then (
      isfree.(tmp) <- true; 
      install_zombie installer reg card prepon oppon tail
    ) else
      Code(set_card 1 (Get *+ Val tmp)) :: 
      Move(AppSC(1, Val 0)) :: Code(retry_zombie tmp) :: tail in
  
  
  if (get_vitality oppon reg > 1000) then
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

let rec use_zombie_iter i auxreg prepon oppon tail =
  let v = (get_vitality oppon i) in
  if (v <= 0) then
    use_zombie_iter ((i+1) mod 256) auxreg prepon oppon tail
  else (
    let vital = compvital v in
    let tmp = alloc_reg() in
    Code(set_number 0 i) ::
      Code(set_number 1 vital) ::
      Code(set_card tmp (Get *+ Val auxreg)) ::
      Move(AppSC(tmp, Val 0)) ::
      Code(free_reg tmp) ::
      Code(use_zombie_iter i auxreg) :: tail
  )



let rec use_zombie installer zombiereg auxreg prepon oppon tail = 
  if (get_vitality oppon zombiereg > 1000) then
    Code(attack zombiereg) :: 
      Code(use_zombie installer zombiereg auxreg) :: tail
  else
  let help00 = (S *+ (K *+ (S *+ Help *+ I)) *+ Get) in
  let get1 = (S *+ (K *+ Get) *+ Succ) in
  let app1 (c, v) = (S *+ (K *+ c) *+ v) in
  let app2 (v, c) = (S *+ v *+ (K *+ c)) in
  let app3 (v1, v2) = (S *+ v1 *+ v2) in
  let zombie = app3(app1(S, app1(K,help00)), app1(K,get1)) in
  Code(set_card auxreg
	 (app2(app1(Get *+ Val installer, zombie), Val (255-zombiereg)))) ::
    Code(use_zombie_iter 0 auxreg) :: tail

let rec watch_double_zombie installer hisdead codereg prepon oppon tail = 
  if (get_vitality oppon hisdead < 0) then 
    Yield :: Code(watch_double_zombie installer hisdead codereg) :: tail
  else (
    (*prerr_string ("reinstall double zombie " ^ 
                  string_of_int installer ^ " " ^
                  string_of_int hisdead ^ " " ^
                  string_of_int codereg); prerr_newline ();
    prerr_slots oppon;*)
    let t1 = alloc_reg() in
    let t2 = alloc_reg() in
    Code(set_card t1 (Get *+ Val 0))::
      Code(set_card t2 (Get *+ Val 1))::
      Code(install_zombie installer hisdead (Get *+ Val codereg)) :: 
      Code(set_card 0 (Get *+ Val t1)) ::
      Code(free_reg t1) ::
      Code(set_card 1 (Get *+ Val t2)) ::
      Code(free_reg t2) ::
      Code(watch_double_zombie installer hisdead codereg) :: tail
  )

let start_watcher installer hisdead codereg prepon oppon tail =
  tasks.(1) <- [Code(watch_double_zombie installer hisdead codereg)]; tail

let phase4 installer prepon oppon tail =
  let auxreg = alloc_reg () in
  let hisdead = 254 in
  Code(use_zombie installer hisdead auxreg)::tail

let phase3 installer hisdeadreg backzombie prepon oppon tail =
  Code(start_watcher installer hisdeadreg backzombie)
  :: Code(phase4 installer) :: tail

let phase2 installer hisdeadreg zombiereg backzombie prepon oppon tail =
  Code(set_card installer (buildrec Dec 10)) ::
    Code(double_dec installer) ::
    Code(double_dec installer) ::
    Code(double_dec installer) ::
    Code(double_dec installer) ::
    Code(double_dec installer) ::
    Move(AppCS(S, installer)) ::
    Move(AppCS(K, installer)) ::
    Move(AppCS(S, installer)) ::
    Code(apply_card installer (S *+ (K *+ (S *+ Zombie)) *+ K)) ::
    Code(phase3 installer hisdeadreg backzombie) :: tail

let double_zombie prepon oppon tail =
   let zombiereg  = alloc_reg () in
   let zombieinstaller = alloc_reg () in
   let backzombie = alloc_reg () in
   let mydeadreg  = find_dead_reg prepon 1 0 in
   let tmpreg = alloc_reg() in
   let hisdeadreg = 255 in

   Code(set_card tmpreg (S *+ Inc *+ Inc)) ::
     Code(double_dec tmpreg) ::
     Move(AppCS(K,tmpreg)) :: Move(AppCS(S,tmpreg)) ::
     Code(set_card backzombie
            (S *+ (K *+ (Zombie *+ Val (255 - mydeadreg)))
             *+ (S *+ (K *+ Copy) *+ (K *+ Val zombiereg)))) ::
     Code(set_card zombiereg
            (S *+ (K *+ (Zombie *+ Val (255-hisdeadreg)))
             *+ (K *+ (S *+ (S *+ (Get *+ Val tmpreg *+ (K *+ Val 0))
                               *+ (Get *+ Val tmpreg *+ (K *+ Val 1)))
                       *+ (Get *+ Val backzombie))))) ::
     Code(free_reg tmpreg) ::
   let attack prepon oppon tail =
     let vital = get_vitality oppon 0 in
       Code(set_card 1  (Zombie *+ Val (255-hisdeadreg) *+
                        (S *+ (S *+ (K *+ (Help *+ Val 0 *+ Val 0))
                                 *+ (K *+ Val (compvital vital)))
                           *+ (Get *+ Val backzombie)))) ::
       Code(phase2 zombieinstaller hisdeadreg zombiereg backzombie) :: tail in
	    
   let myvital = get_vitality prepon mydeadreg in
   if (myvital > 0) then
       Code(set_card 1 (Attack *+ Val mydeadreg *+ Val hisdeadreg *+ Val myvital)) :: Code(attack) :: tail
   else
       Code(attack) :: tail


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


let revive_reg reg prepon oppon tail = 
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

    let tmpreg = findbestreg 0 reg 0 in
    List.hd (set_number tmpreg reg 
               prepon oppon [Move(AppCS(Revive, tmpreg))]) :: tail

let revive_step prepon oppon tail =
    let rec reviveloop reg  =
        if (reg == 256) then
           Yield :: tail
        else if (not (isfree.(reg)) && (get_vitality prepon reg <= 0)) then
           revive_reg reg prepon oppon tail
        else
           reviveloop (reg+1) in

    reviveloop 0

let rec revive prepon oppon tail =
  revive_step prepon oppon (Code(revive) :: tail)


let rec random_apply start cnt prepon oppon tail =
  let rand = Random.int cnt in
  Code(set_card 20 (Get *+ Val (start+rand))) :: 
  Move(AppSC(20, I)) :: Code(random_apply start cnt) :: tail

let defender prepon oppon tail = 
(*   Code(set_card 25 (S *+ (S *+ (K *+ Revive) *+ (K *+ Val 254)) *+
	                  (S *+ (K *+ (Help *+ Val 128 *+ Val 254)) *+ (K *+ Val 50)))) ::
*)
   Code(set_card 26 (S *+ (S *+ (K *+ Revive) *+ (K *+ Val 255)) *+
	                  (S *+ (K *+ (Help *+ Val 128 *+ Val 255)) *+ (K *+ Val 50)))) ::

   Code(set_card 27 (S *+ (S *+ (K *+ Revive) *+ (K *+ Val 0)) *+
	                  (S *+ (K *+ (Help *+ Val 128 *+ Val 0)) *+ (K *+ Val 50)))) ::

   Code(set_card 28 (S *+ (S *+ (K *+ Revive) *+ (K *+ Val 255)) *+
	                  (S *+ (K *+ Inc) *+ (K *+ Val 255)))) ::
(*
   Code(set_card 29 (S *+ (S *+ (K *+ Revive) *+ (K *+ Val 254)) *+
	                  (S *+ (K *+ Inc) *+ (K *+ Val 254)))) ::
   Code(set_card 30 (S *+ (S *+ (K *+ Revive) *+ (K *+ Val 0)) *+
	                  (S *+ (K *+ Inc) *+ (K *+ Val 0)))) :: 
   Code(set_card 31 (S *+ (K *+ (Help *+ Val 129 *+ Val 128)) *+ (K *+ Val 200))) ::*)
   Code(random_apply 26 3) :: tail

let attack_from fromreg toreg prepon oppon tail =
  let rec continue prepon oppon tail = 
    if (get_card prepon 0 = Val (get_vitality prepon fromreg)) then
      Move(AppSC(1, Val 0)) :: tail
    else
      Code(set_number 0 (get_vitality prepon fromreg)) ::
	Code(continue) :: tail in
      
  Code(set_card 1 (S *+ (K *+ (Attack *+ Val fromreg *+ Val (255-toreg)))
		   *+ Get)) :: Code(continue) :: tail

let rec revive_zombie mydeadreg hisdeadreg prepon oppon tail =
  if (get_vitality prepon mydeadreg > 0) then
    Code(attack_from mydeadreg hisdeadreg) :: 
      Code(revive_zombie mydeadreg hisdeadreg) :: tail
  else if (get_vitality oppon hisdeadreg > 320) then
    Code(attack hisdeadreg) :: Code(revive_zombie mydeadreg hisdeadreg) :: tail
  else if (get_vitality oppon hisdeadreg >= 0) then
    Move(AppSC(64, I)) :: Code(revive_zombie mydeadreg hisdeadreg) :: tail
  else
    Yield :: Code(revive_zombie mydeadreg hisdeadreg) :: tail

let rec main_strategy_strongdbl_zombie prepon oppon tail =
  isfree.(64) <- false;
  let installer = alloc_reg () in
  let inc5 = alloc_reg () in
  let mydeadreg = 255 in
  let hisdeadreg = 255 in
  let continue prepon oppon tail =
    tasks.(1) <- [ Code(revive_zombie mydeadreg hisdeadreg) ];
    Code(phase4 installer) :: tail in
  (* Create zombie installer: it does 320 dec before invoking zombie *)
  (* Usage: (Get *+ Val installer) *+ zombiecode *+ (255-zombiereg) *)
  Code(set_card installer (buildrec Dec 10)) ::
    Code(double_dec installer) ::
    Code(double_dec installer) ::
    Code(double_dec installer) ::
    Code(double_dec installer) ::
    Code(double_dec installer) ::
    Move(AppCS(S, installer)) ::
    Move(AppCS(K, installer)) ::
    Move(AppCS(S, installer)) ::
    Code(apply_card installer (S *+ (K *+ (S *+ Zombie)) *+ K)) ::
    (* Create zombie code; it uses a simpler installer *)
    Code(set_card inc5 (buildrec Inc 5)) ::
    Code(set_card 0 (S*+ (S *+ (S *+ (K *+ (Get *+ Val inc5)) *+ (K *+ Val 0))
	                  *+ (S *+ (K *+ (Get *+ Val inc5)) *+ (K *+ Val 1)))
		     *+ (S *+ (K *+ (Zombie *+ Val (255 - mydeadreg)))
			 *+ (S *+ (K *+ Copy) *+ (K *+ Val 64))))) ::
    Code(set_card 64 (Get *+ Val installer)) ::
    Code(apply_card 64 (Get *+ Val 0)) ::
    Move(AppCS(K, 64)) ::
    Move(AppCS(S, 64)) ::
    Code(apply_card 64 (K *+ Val (255-hisdeadreg))) ::
    Move(AppCS(S, 64)) ::
    Code(apply_card 64 (S *+ (K *+ Get) *+ (K *+ Val 64))) ::
    Code(attack_from mydeadreg hisdeadreg) ::
    Code(continue) :: tail

let rec newreviver prepon oppon tail =
  let rec need_saving i =
    if (get_vitality prepon i <= 0 && 
	(i < 20 || not (isfree.(i)))) then
      i
    else if (i == 255) then -1 else need_saving (i+1) in
  
  let savereg = need_saving 0 in
  (*prerr_string ("newreviver " ^ string_of_int savereg); prerr_newline();*)
  if (savereg >= 0) then (
    if (get_vitality prepon 32 <= 0) then (
      revive_reg 32 prepon oppon (Code(newreviver) :: tail)
    ) else if (savereg < 70) then (
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
      
      let tmpreg = findbestreg 0 32 0 in
      prerr_string ("tmpreg " ^ string_of_int tmpreg); prerr_newline();
      let setnum = set_number tmpreg 32 prepon oppon [] in
      if (setnum = []) then
	Move(AppCS(Get, tmpreg)) :: Move(AppSC(tmpreg, Val 0)) :: 
	  Code(newreviver) :: tail
      else
	List.hd(setnum) :: Code(newreviver) :: tail
    ) else
      revive_reg savereg prepon oppon (Code(newreviver) :: tail)
  ) else
    Yield :: Code(newreviver) :: tail

let main_strategy_newreviver prepon oppon tail =
  let continue prepon oppon tail =
    tasks.(0) <- [ Code(newreviver) ];
    Code (main_strategy_strongdbl_zombie) :: tail in
  
  isfree.(32) <- false;
  Code(set_card 32 
	 (S *+ (S *+ (S *+ Revive *+ Inc) *+ Inc)
          *+ (S *+ (S *+ (K *+ Get) *+ (K *+ Val 32)) *+ Succ))) ::
    Code(continue) :: tail
  
(*
let inittask = 
   tasks.(3) <- [ Code(defender) ]; 
   tasks
*)
let inittask = 
   tasks.(0) <- [ Code(revive) ];
   tasks.(3) <- [ Code(main_strategy_newreviver) ]; 
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
