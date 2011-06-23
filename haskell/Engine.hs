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
   = Val !Integer    -- number
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
type Slots = (Array Int Int, Array Int Card)
type IOSlots = (IOArray Int Int, IOArray Int Card)
-- type STSlots s = (STArray s Int Int, STArray s Int Card)

data Move = MoveSC !Int !Card | MoveCS !Card !Int
   deriving (Eq, Show, Read)

createSlotsM :: IO IOSlots
createSlotsM = do
  vits <- newArray (0,255) 10000
  cards <- newArray (0,255) I
  return (vits, cards)

lookupCardI slots slotnr = snd slots Data.Array.IArray.! slotnr
lookupCardM slots slotnr = readArray (snd slots) slotnr

lookupVitalityI slots slotnr = fst slots Data.Array.IArray.! slotnr
lookupVitalityM slots slotnr = readArray (fst slots) slotnr

writeCardM slots slotnr card = 
  writeArray (snd slots) slotnr card
writeVitalityM slots slotnr vit = 
  writeArray (fst slots) slotnr vit
writeZombieM slots slotnr card = do
  writeCardM slots slotnr card
  writeVitalityM slots slotnr (-1)

freezeSlots :: IOSlots -> IO (Slots)
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
                    | InvalidSlotException Integer
                    | NotEnoughVitalityException
                    | DeadSlotException Int
                    deriving (Show, Typeable)

instance Exception ApplyException

applyCard :: Bool -> Card -> Card -> IOSlots -> IOSlots -> IO Card
applyCard isZombie func arg my his = do
  ctr <- newIORef 0
  let incAndCheck 1000 = throw ApplyLimitException
      incAndCheck c = c + 1
      
      getCardValue (Val n) = n
      getCardValue _ = throw NotNumericException
      
      getCardSlot (Val n) | n >= 0 && n <= 256 = fromInteger n
      getCardSlot (Val n) = throw $ InvalidSlotException n
      getCardSlot _ = throw NotNumericException
      
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
          Succ   -> return $ Val $ getCardValue arg + 1
          Dbl    -> return $ Val $ getCardValue arg * 2
          Get    -> let slot = getCardSlot arg in do
            vit <- lookupVitalityM my slot
            when (vit < 0) $ throw $ DeadSlotException slot
            lookupCardM my slot
          Put    -> return I
          Copy   -> do result <- lookupCardM his $ getCardSlot arg
                       return result
          Inc    -> let slot = getCardSlot arg in do
            vitality <- lookupVitalityM my slot
            writeVitalityM my slot (zombieAdd vitality 1)
            return I
          Dec    -> let slot = getCardSlot arg in do
            vitality <- lookupVitalityM his slot
            writeVitalityM his slot (zombieAdd vitality (-1))
            return I
          Help :$ x :$ y -> let fromslot = getCardSlot x 
                                toslot   = getCardSlot y
                                vit      = getCardSlot arg in do
            fromvit <- lookupVitalityM my fromslot
            when (fromvit < vit) $ throw NotEnoughVitalityException
            writeVitalityM my fromslot (fromvit - vit)
            vitality <- lookupVitalityM my toslot
            writeVitalityM my toslot (zombieAdd vitality $ (vit*11 `div` 10))
            return I
          Attack :$ x :$ y -> let fromslot = getCardSlot x 
                                  toslot   = getCardSlot y
                                  vit      = getCardSlot arg in do
            fromvit <- lookupVitalityM my fromslot
            when (fromvit < vit) $ throw NotEnoughVitalityException 
            writeVitalityM my fromslot (fromvit - vit)
            vitality <- lookupVitalityM his toslot
            writeVitalityM his toslot (zombieAdd vitality $ -(vit*9 `div` 10))
            return I
          Revive -> let slot = getCardSlot arg in do
            vitality <- lookupVitalityM my slot
            when (vitality < 0) $ writeVitalityM my slot 1
            return I
          Zombie :$ x -> let slot = getCardSlot x in do
            vitality <- lookupVitalityM my slot
            when (vitality < 0) $ writeZombieM my slot arg
            return I
  apply func arg