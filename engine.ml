module Engine = struct

  type card = Val of int | App of card * card | 
     I | Succ | Dbl | Get | Put | S | K |
     Inc | Dec | Attack | Help | 
     Copy | Revive | Zombie

  type slots = (int * card) array

  type move = AppSC of (int * card) | AppCS of (card * int)


  exception ApplyError

  let rec card_to_string c = 
    match c with 
      App(f,a) -> (card_to_string f) ^ 
                  "(" ^ (card_to_string a) ^ ")"
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
    print_string (card_to_string card)

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
      prerr_string (card_to_string c);
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
    let limit_vitality v =
       if v < 0 then 0 else if v > 65535 then 65535 else v in

    let rec apply func arg =
      (*prerr_string ("Apply "^(card_to_string func) ^ " on "
                            ^(card_to_string arg) ^ "\n");*)
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
      | Succ           -> 
          (match arg with 
             Val n -> Val (n+1) 
           | _ -> raise ApplyError)
      | Dbl            -> 
          (match arg with 
             Val n -> Val (2*n) 
           | _ -> raise ApplyError)
      | Get            -> 
          (match arg with 
             Val n ->  if (n < 0 || n > 255
                           || get_vitality prepon n <= 0) then raise ApplyError
                       else get_card prepon n
           | _ -> raise ApplyError)
      | Put            -> I
      | Copy           ->
          (match arg with 
             Val n ->  if (n < 0 || n > 255) then raise ApplyError
                       else get_card oppon n
           | _ -> raise ApplyError)
      | Inc           ->
          (match arg with 
             Val n -> if (n < 0 || n > 255) then raise ApplyError
                       else let oldval = get_vitality prepon n in
                         if oldval <= 0 || oldval == 65535 then ()
                         else (set_vitality prepon n (oldval+1)); I
           | _ -> raise ApplyError)
      | Dec           ->
          (match arg with 
             Val n ->  if (n < 0 || n > 255) then raise ApplyError
                       else let oldval = get_vitality oppon (255-n) in
                         if oldval <= 0 then ()
                         else (set_vitality oppon (255-n) (oldval-1)); I
           | _ -> raise ApplyError)
      | App (App (Attack, argi), argj) ->
          (match argi,argj,arg with 
             Val i, Val j, Val n ->  
                       if (i < 0 || i > 255) then raise ApplyError
		       else let myval = get_vitality prepon i in
		       if (myval < n) then raise ApplyError
		       else (set_vitality prepon i (myval-n));
		       if (j < 0 || j > 255) then raise ApplyError
		       else let oldval = get_vitality oppon (255-j) in
		       let dec = if isZombie then -(n*9/10) else n*9/10 in
		       set_vitality oppon (255-j) 
		            (if oldval <= 0 then oldval
			     else limit_vitality (oldval - dec)); I
           | _ -> raise ApplyError)
      | App (App (Help, argi), argj) ->
          (match argi,argj,arg with 
             Val i, Val j, Val n ->  
                       if (i < 0 || i > 255) then raise ApplyError
		       else let myval = get_vitality prepon i in
		       if (myval < n) then raise ApplyError
		       else (set_vitality prepon i (myval-n));
		       if (j < 0 || j > 255) then raise ApplyError
		       else let oldval = get_vitality prepon j in
		       let inc = if isZombie then -(n*11/10) else n*11/10 in
		       set_vitality prepon j 
		            (if oldval <= 0 then oldval
			     else limit_vitality (oldval + inc)); I
           | _ -> raise ApplyError)
      | Revive           ->
          (match arg with 
             Val n ->  if (n < 0 || n > 255) then raise ApplyError
                       else let oldval = get_vitality prepon n in
                         if oldval <= 0 then (set_vitality prepon n 1)
                         else (); I
           | _ -> raise ApplyError)
      | App (Zombie, argi)           ->
          (match argi with 
             Val n ->  if (n < 0 || n > 255) then raise ApplyError
                       else let oldval = get_vitality oppon (255-n) in
                         if oldval <= 0 then (set_slot oppon (255-n) (-1, arg))
                         else raise ApplyError; I
           | _ -> raise ApplyError)
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

