module Engine = struct

  type card = Val of int | App of card * card | 
     I | Succ | Dbl | Get | Put | S | K |
     Inc | Dec | Attack | Help | 
     Copy | Revive | Zombie

  type slots = (int * card) array

  type move = AppSC of (int * card) | AppCS of (card * int)


  exception ApplyError

  let rec string_of_card c = 
    match c with 
      App(f,a) -> (string_of_card f) ^ 
                  "(" ^ (string_of_card a) ^ ")"
    | Val 0    -> "zero"
    | Val n    -> string_of_int n
    | I        -> "I"
    | Succ     -> "succ"
    | Dbl      -> "dbl"
    | Get      -> "get"
    | Put      -> "put"
    | S        -> "S"
    | K        -> "K"
    | Inc      -> "inc"
    | Dec      -> "dec"
    | Attack   -> "attack"
    | Help     -> "help"
    | Copy     -> "copy"
    | Revive   -> "revive"
    | Zombie   -> "zombie"

  let print_card card =
    print_string (string_of_card card)

  let read_card () = 
    match read_line () with
      "zero"   -> Val 0
    | "I"      -> I
    | "succ"   -> Succ
    | "dbl"    -> Dbl
    | "get"    -> Get
    | "put"    -> Put
    | "S"      -> S
    | "K"      -> K
    | "inc"    -> Inc
    | "dec"    -> Dec
    | "attack" -> Attack
    | "help"   -> Help
    | "copy"   -> Copy
    | "revive" -> Revive
    | "zombie" -> Zombie
    | _        -> raise (Failure "read_card")

  let prerr_slot (v, c) = 
      prerr_string "[";
      prerr_int v;
      prerr_string ",";
      prerr_string (string_of_card c);
      prerr_string "]"
 
  let prerr_slots sl = 
    let rec loop i = 
      if (i == 256) then () else 
      (if (sl.(i) = (10000, I)) then () else
         (prerr_int i; prerr_string ": "; 
         prerr_slot sl.(i); prerr_newline ());
         loop (i+1)) in
    loop 0

  let create_slots () = Array.make 256 (10000, I)

  let get_card (sl : slots) i = snd (sl.(i))

  let get_vitality (sl : slots) i = fst (sl.(i))

  let set_vitality (sl : slots) i v =
    sl.(i) <- (v, (snd (sl.(i))))

  let set_card (sl : slots) i c =
    sl.(i) <- ((fst (sl.(i))), c)

  let set_slot (sl : slots) i s =
    sl.(i) <- s

  let apply_cards prepon oppon func arg isZombie =
    let counter = ref 0 in
    let parsenum = function Val n -> n | _ -> raise ApplyError in
    let parseslot c = let n = parsenum c in
		      if (n < 0 || n >= 256) then raise ApplyError else n in
    let limit v =
       if v < 0 then 0 else if v > 65535 then 65535 else v in
    let add v inc = 
       if v <= 0 then v 
                 else limit (if isZombie then v - inc else v + inc) in

    let rec apply func arg =
      (*prerr_string ("Apply "^(string_of_card func) ^ " on "
                            ^(string_of_card arg) ^ "\n");*)
      counter := !counter + 1;
      if (!counter > 1000) then
        raise ApplyError
      else (match func with
        App (App (S, f), g) -> 
              let h = apply f arg in
              let y = apply g arg in
              apply h y
      | App (K, x)     -> x
      | I              -> arg
      | Val n          -> raise ApplyError
      | Succ           -> Val (limit (parsenum arg + 1))
      | Dbl            -> Val (limit (parsenum arg * 2))
      | Get            -> let n = parseslot arg in
			  if get_vitality prepon n <= 0 then raise ApplyError
			  else get_card prepon n
      | Put            -> I
      | Copy           -> get_card oppon (parseslot arg)
      | Inc            -> let slot = parseslot arg in
			  let oldval = get_vitality prepon slot in
			  set_vitality prepon slot (add oldval 1);
			  I
      | Dec            -> let slot = parseslot arg in
			  let oldval = get_vitality oppon (255-slot) in
			  set_vitality oppon (255-slot) (add oldval (-1));
			  I
      | App (App (Attack, argi), argj) ->
                    let i = parseslot argi in
                    let n = parsenum arg in
	            let myval = get_vitality prepon i in
		    if (myval < n) then raise ApplyError
		    else (
		      set_vitality prepon i (myval-n); 
                      let j = parseslot argj in
                      let oldval = get_vitality oppon (255-j) in
		      set_vitality oppon (255-j) (add oldval (-(n*9/10)));
                      I
		    )
      | App (App (Help, argi), argj) ->
                    let i = parseslot argi in
                    let n = parsenum arg in
	            let myval = get_vitality prepon i in
		    if (myval < n) then raise ApplyError
		    else (
		      set_vitality prepon i (myval-n) ;
                      let j = parseslot argj in
                      let oldval = get_vitality prepon j in
		      set_vitality prepon j (add oldval (n*11/10));
                      I
		    )
      | Revive     ->    let n = parseslot arg in
                         let oldval = get_vitality prepon n in
                         if oldval <= 0 then (set_vitality prepon n 1) else ();
                         I
      | App (Zombie, argn) ->
                       let n = parseslot argn in
                       let oldval = get_vitality oppon (255-n) in
                       if oldval <= 0 then (set_slot oppon (255-n) (-1, arg))
                       else raise ApplyError; 
		       I
      | _ -> App (func, arg)
      ) in
    apply func arg
    

let read_move () = 
  let appdir = read_int () in
  match appdir with
   1 -> let card1 = read_card () in
        let slot  = read_int () in
        AppCS(card1,slot)
 | 2 -> let slot  = read_int () in
        let card2 = read_card () in
        AppSC(slot, card2)
 | _ -> raise (Failure "Wrong number")
  

let print_move = function
   AppCS(c,s) -> 
        print_int 1; print_newline ();
        print_card c; print_newline ();
        print_int s; print_newline ()
 | AppSC(s,c) -> 
        print_int 2; print_newline ();
        print_int s; print_newline ();
        print_card c; print_newline ()


end

