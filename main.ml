open Sys
open Engine
include Engine
open Strategy


let rec mainloop prepon oppon player opponent = 
  let rec process_zombies i = if i == 256 then () else
    let oldval = get_vitality prepon i in
    if (oldval == -1) then (
      let card   = get_card prepon i in
      let _ = try apply_cards prepon oppon card I true
      with ApplyError -> I in
      set_slot prepon i (0, I)
    ) else ();
    process_zombies (i+1) in
	
  prerr_slots prepon;
  process_zombies 0;
  let move = player prepon oppon in
  match move with
    AppCS(card1, slot) -> 
        let card2 = get_card prepon slot in
        let outcard = 
          if (get_vitality prepon slot <= 0) then I
          else try apply_cards prepon oppon card1 card2 false
          with ApplyError -> I in
        set_card prepon slot outcard;
        mainloop oppon prepon opponent player
  | AppSC(slot, card2) -> 
        let card1 = get_card prepon slot in
        let outcard = 
          if (get_vitality prepon slot <= 0) then I
          else try apply_cards prepon oppon card1 card2 false
          with ApplyError -> I in
        set_card prepon slot outcard;
        mainloop oppon prepon opponent player


;;


let reader prepon oppon =
   read_move () in

let call_and_print strategy prepon oppon =
   let move = strategy prepon oppon in
   print_move move;
   move in

let pl0 = create_slots () in
let pl1 = create_slots () in
  match Sys.argv.(1) with
    "0" -> mainloop pl0 pl1 (call_and_print Strategy.play_strategy) reader
  | "1" -> mainloop pl0 pl1 reader (call_and_print Strategy.play_strategy)
  | _   -> raise (Failure "Who Am I?")
  
