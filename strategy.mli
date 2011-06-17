open Engine

(** Module that provides game engine functionality *)

module Strategy :
  sig
    val play_strategy : Engine.slots -> Engine.slots -> Engine.move
  end
