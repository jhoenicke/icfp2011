---------
-- New Strategy for killing the opponent by a massive attack through
-- parallel zombie slots.
--
-- The idea is to do a very fast sequence of
--   help(src,src,36410)*5,attack(src,dest,36410),
--   help(backup,backup,36410)*5,help(backup,src,17400)
-- provided that src and backup start with vitality > 36410
-- this succeeds and kills dest surely.
---------

import Control.Monad
import Engine
import Lambda
import Strategy
import System (getArgs)

reviveSlot n = undefined

-- safe version of set card/get card etc.
applySCS :: [Int] -> Int -> Card -> Strategy ()
applySCS tmpReg slot card = do
  vit <- getVitality Me slot
  when (vit <= 0) $ reviveSlot slot
  applySCR tmpReg slot card

setCardS :: [Int] -> Int -> Card -> Strategy ()
setCardS tmpReg slot card = do
  vit <- getVitality Me slot
  when (vit <= 0) $ reviveSlot slot
  setCardR tmpReg slot card

surefire = do
  setCardS [] 0 $ lambdaCard "%z %f %x f (z f x)"
  setCardS [] 1 $ lambdaCard "S(K(get 0))get"
  setCardS [] 2 $ lambdaCard "get 1"
  applySCS [] 0 $ lambdaCard "I"      -- f (f x)
  applySCS [] 1 $ lambdaCard "0"  -- f (f (f x))
  applySCS [] 2 $ lambdaCard "1"  -- f (f (f (f (f x))))
  applyCS K 2 
  applyCS S 2
  applySCS [] 2 $ lambdaCard "%x %c %y help x x y (c y)"
  applyCS K 2
  applyCS S 2
  applySCS [] 2 Get
  setCardS [] 1 $ lambdaCard "get 2"  
  setNumber 0 25
  applySCS [] 1 zero
  applySCS [0] 1 $ lambdaCard "%y help 25 26 (K 17400 y)"  
  setNumber 0 26
  applySCS [] 2 zero
  applySCS [0] 2 $ lambdaCard "(%y attack 26 0 y ((get 1) y))"  
--  setCardS [] 0 $ lambdaCard "get 2"
--  setCardS [1,2,3] 2 $ 


main = do
  args <- getArgs
  rungame (head args == "0") surefire
  return ()
          