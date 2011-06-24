{-# OPTIONS_GHC -XDeriveDataTypeable #-}

module Engine where

import Data.Array.IO
import Data.IORef
import Data.Array.IArray
import Data.Array.MArray
import Data.Typeable
import Control.Exception
import Control.Monad

-------
-- Card data type
-------

infixl 1 :$

data Card
   = Val !Int    -- number
   | !Card :$ !Card   -- card application
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

type SlotsA a = (a Int Int, a Int Card)
type Slots = SlotsA Array
type IOSlots = SlotsA IOArray

data Move = MoveSC !Int !Card | MoveCS !Card !Int
   deriving (Eq, Show, Read)

createSlotsM :: IO IOSlots
createSlotsM = do
  vits <- newArray (0,255) 10000
  cards <- newArray (0,255) I
  return (vits, cards)

lookupCardI slots slotnr = snd slots ! slotnr
lookupCardM slots slotnr = readArray (snd slots) slotnr

lookupVitalityI slots slotnr = fst slots ! slotnr
lookupVitalityM slots slotnr = readArray (fst slots) slotnr

writeCardM slots slotnr card = 
  writeArray (snd slots) slotnr card
writeVitalityM slots slotnr vit = 
  writeArray (fst slots) slotnr vit
writeZombieM slots slotnr card = do
  writeCardM slots slotnr card
  writeVitalityM slots slotnr (-1)

freezeSlots :: IOSlots -> IO Slots
freezeSlots slots = do
  vits <- freeze $ fst slots 
  cards <- freeze $ snd slots
  return (vits,cards)

---------------------
-- Applying Cards
---------------------

data ApplyException = ApplyLimitException
                    | ApplyIntegerException
                    | NotNumericException
                    | InvalidSlotException Int
                    | NotEnoughVitalityException
                    | DeadSlotException Int
                    deriving (Show, Typeable)

instance Exception ApplyException

applyCard :: Bool -> Card -> Card -> IOSlots -> IOSlots -> IO Card
applyCard isZombie func arg my his = do
  ctr <- newIORef 0
  let incAndCheck 1000 = throw ApplyLimitException
      incAndCheck c = c + 1
      
      getCardValue (Val n) = return n
      getCardValue _ = throw NotNumericException
      
      getCardSlot (Val n) | n >= 0 && n < 256 = return n
      getCardSlot (Val n) = throw $ InvalidSlotException n
      getCardSlot _ = throw NotNumericException
      getOtherCardSlot arg = do 
        slot <- getCardSlot arg
        return $ 255 - slot
      
      limit vit 
        | vit < 0 = 0
        | vit > 65535 = 65535
        | otherwise = vit
      zombieAdd vit incr 
        | vit <= 0 = vit
        | isZombie = limit $ vit - incr
        | otherwise = limit $ vit + incr
      
      apply func arg = do
        modifyIORef ctr incAndCheck
        case func of
          S :$ f :$ g -> do
            h <- apply f arg
            y <- apply g arg
            apply h y
          K :$ x -> return x
          I      -> return arg
          Val n  -> throw ApplyIntegerException
          Succ   -> do n <- getCardValue arg; return $ Val $ limit $ n + 1
          Dbl    -> do n <- getCardValue arg; return $ Val $ limit $ 2 * n
          Get    -> do
            slot <- getCardSlot arg
            vit <- lookupVitalityM my slot
            when (vit <= 0) $ throw $ DeadSlotException slot
            lookupCardM my slot
          Put    -> return I
          Copy   -> do 
            slot <- getCardSlot arg
            result <- lookupCardM his $ slot
            return result
          Inc    -> do
            slot <- getCardSlot arg
            vitality <- lookupVitalityM my slot
            writeVitalityM my slot (zombieAdd vitality 1)
            return I
          Dec    -> do
            slot <- getOtherCardSlot arg
            vitality <- lookupVitalityM his slot
            writeVitalityM his slot (zombieAdd vitality (-1))
            return I
          Help :$ x :$ y -> do            
            fromslot <- getCardSlot x
            vit <- getCardValue arg
            fromvit <- lookupVitalityM my fromslot
            when (fromvit < vit) $ throw NotEnoughVitalityException
            writeVitalityM my fromslot (fromvit - vit)
            toslot <- getCardSlot y
            vitality <- lookupVitalityM my toslot
            writeVitalityM my toslot (zombieAdd vitality $ (vit*11 `div` 10))
            return I
          Attack :$ x :$ y -> do
            fromslot <- getCardSlot x
            vit <- getCardValue arg
            fromvit <- lookupVitalityM my fromslot
            when (fromvit < vit) $ throw NotEnoughVitalityException 
            writeVitalityM my fromslot (fromvit - vit)
            toslot <- getOtherCardSlot y
            vitality <- lookupVitalityM his toslot
            writeVitalityM his toslot (zombieAdd vitality $ -(vit*9 `div` 10))
            return I
          Revive -> do
            slot <- getCardSlot arg
            vitality <- lookupVitalityM my slot
            when (vitality <= 0) $ writeVitalityM my slot 1
            return I
          Zombie :$ x -> do
            slot <- getOtherCardSlot x
            vitality <- lookupVitalityM his slot
            when (vitality <= 0) $ writeZombieM his slot arg
            return I
          _ -> return $ func :$ arg
  apply func arg
