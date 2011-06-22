module Engine where

import Data.Array

-------
-- Card data type
-------

infixl 1 :$

data Card
   = Val Integer    -- number
   | Card :$ Card   -- card application
   | I | Succ | Dbl | Get | Put | S | K
   | Inc | Dec | Attack | Help
   | Copy | Revive | Zombie
   deriving (Eq)

instance Show Card where
   showsPrec _ (Val 0)  s = 'z':'e':'r':'o':s
   showsPrec _ (Val n)  s = shows n s
   showsPrec _ (f :$ a) s = shows f $ '(' : shows a (')' : s)
   showsPrec _ I        s = 'I':s
   showsPrec _ Succ     s = 's':'u':'c':'c':s
   showsPrec _ Dbl      s = 'd':'b':'l':s
   showsPrec _ Get      s = 'g':'e':'t':s
   showsPrec _ Put      s = 'p':'u':'t':s
   showsPrec _ S        s = 'S':s
   showsPrec _ K        s = 'K':s
   showsPrec _ Inc      s = 'i':'n':'c':s
   showsPrec _ Dec      s = 'd':'e':'c':s
   showsPrec _ Attack   s = 'a':'t':'t':'a':'c':'k':s
   showsPrec _ Help     s = 'h':'e':'l':'p':s
   showsPrec _ Copy     s = 'c':'o':'p':'y':s
   showsPrec _ Revive   s = 'r':'e':'v':'i':'v':'e':s
   showsPrec _ Zombie   s = 'z':'o':'m':'b':'i':'e':s

readSimpleCard "zero"   = Val 0
readSimpleCard "I"      = I
readSimpleCard "succ"   = Succ
readSimpleCard "dbl"    = Dbl
readSimpleCard "get"    = Get
readSimpleCard "put"    = Put
readSimpleCard "S"      = S
readSimpleCard "K"      = K
readSimpleCard "inc"    = Inc
readSimpleCard "dec"    = Dec
readSimpleCard "attack" = Attack
readSimpleCard "help"   = Help
readSimpleCard "copy"   = Copy
readSimpleCard "revive" = Revive
readSimpleCard "zombie" = Zombie
readSimpleCard s        = Val (read s)
	                               
readsArgsOfCard card s = 
      [ (result,x) | ("(", s') <- lex s,
                     (arg, s'') <- [head $ readsCard s'],
	             (")", s''') <- lex s'',
	             (result,x) <- readsArgsOfCard (card :$ arg) s''' ] 
      ++ [(card,s)]

readsCard s = [ (card, x) | (token, s') <- lex s,
                            (card,x) <- let card1 = readSimpleCard token in
                                            readsArgsOfCard card1 s' ]


instance Read Card where
   readsPrec _ = readsCard

---------------------
--  Slots & Moves
---------------------

type Slots = Array Int (Int, Card)

data Move = MoveSC Int Card | MoveCS Card Int
   deriving (Eq, Show, Read)


---------------------
-- Applying Cards
---------------------

type SlotState = State (Slots,Slots)
data Exceptional t = Success t
                   | Exception String
   deriving(Show, Read)



apply :: Bool -> Card -> Card -> 
                        State (Int,Slots,Slots) (Exceptional Card))
apply isZombie func arg = do
   (counter, my, his) <- get
   when counter >= 1000 $ return (Exception "Counter exceeded")
   put (counter + 1, my, his)
   match func with
    (S :$ f :$ g) -> do
        h <- apply f arg
        y <- apply g arg
        return Success(apply h y)
    (K :$ x) -> x
    I -> arg
    Val n -> return Exception "Applying integer as function"
    Val 


applyCard :: Bool -> Card -> Card -> SlotState (Exceptional Card)
applyCard isZombie func arg =
  return (\my his -> 
             let (_, my', his') = runState (applyCardWithCounter isZombie func arg) (0,my,his) in (my',his'))

apply_cards isZombie func arg
  let apply_cards prepon oppon func arg isZombie =
    let counter = ref 0 in
    let limit_vitality v =
       if v < 0 then 0 else if v > 65535 then 65535 else v in

    let rec apply func arg =
      (*prerr_string ("Apply "^(string_of_card func) ^ " on "
                            ^(string_of_card arg) ^ "\n");*)
      counter := !counter + 1;
      if (!counter > 1000) then
        raise ApplyError
      else (match func with


