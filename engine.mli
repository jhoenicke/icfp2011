(** Module that provides game engine functionality *)

module Engine :
  sig
    (** 
     * The card type.  Most Cards are represented by an enumeration.
     * Cards can be partially applied, e.g. S(K), which is represented
     * as App(S,K).  Numbers are represented by Val(n), where n is an integer.
     * The Card zero is represented by Val 0.
     * Note that App(x,y) and Val n for n!=0 are not valid cards for a move.
     *)
    type card = Val of int | App of card * card | 
	        I | Succ | Dbl | Get | Put | S | K |
                Inc | Dec | Attack | Help | 
                Copy | Revive | Zombie

    (** 
     * The move type.  The are two moves: 
     * apply slot on card (AppSC), or apply card on slot (AppCS).
     *)
    type move = AppSC of (int * card) | AppCS of (card * int)

    (** 
     * The slots.  These are represented as an array containing the
     * pair of vitality and card.
     *)
    type slots = (int * card) array
    exception ApplyError

    val create_slots : unit -> slots
    val get_card     : slots -> int -> card
    val get_vitality : slots -> int -> int
    val set_card     : slots -> int -> card -> unit
    val set_slot     : slots -> int -> (int * card) -> unit

    (**
     * apply_cards myslots hisslots func arg isZombie
     * Apply func on arg and return the result.  The functions can have
     * side-effects on myslots and hisslots.  If isZombie is true, the
     * inc,dec,attack and help cards behave differently
     *)
    val apply_cards  : slots -> slots -> card -> card -> bool -> card

    val string_of_card : card -> string
    val print_card   : card -> unit
    val prerr_slots  : slots -> unit
    val print_move   : move -> unit
    val read_card    : unit -> card
    val read_move    : unit -> move
  end
