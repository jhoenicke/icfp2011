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
  
-- general remarks
--  we represent pairs (x,y) by %sw sw x y = S(SI(Kx))(Ky)
--   1. applying K   extracts x
--   2. applying put extracts y
--   3. applying I   executes x on y  (useful for transformers)


-- transformer
-- a transformer is a function
--  tr y -> %sw %y sw (get myslot) (some transformation on y)
-- the idea is that the so build function can be called with either
--  (1) I   - which extends y by applying trafo again.
--  (2) put - which discards the transformer and extracts y.
transformer = "%sw %y sw (get trslot) (trafo y)"

-- iterator slot n -- builds the formula
--    (%f %x f^n(x)) = %f %x f(...f(x)...)
-- into slot n
--  uses slots 0 and 1 as temporary registers; slot should not be 0 or 1.
iterator slot n = do
  case n of
    1 -> setCardS [] slot I
    2 -> setCardS [] slot $ ffx
    3 -> do setCardS [] 0    fzfx
            setCardS [] slot get0
            applySCS [] 0    I
            applySCS [] slot get0    
    4 -> do setCardS [] 0    ffx
            setCardS [] slot $ lambdaCard "(%r (get r) (get r)) 0"
    5 -> do setCardS [] 0    fzfx
            setCardS [] slot $ lambdaCard "get 0"
            applySCS [] 0    I
            applySCS [] slot $ lambdaCard "(%r (get r) (get r)) 0"
    55-> do setCardS [] 0    fzfx
            setCardS [] slot $ lambdaCard "(%r (S S I (get 0) I) (get r)) 0 I"
    -5-> do setCardS [] 0    fzfx
            setCardS [] 1    get0
            applySCS [] 0    I
            setCardS [] slot $ lambdaCard "(%r (get r) (get r)) 0"
            applySCS [] slot get1
            applySCS [] slot I
    6 -> do iterator slot 3
            applyCS K slot
            applyCS S slot
            applySCS [] slot get0
    7 -> do setCardS [] 0    fzfx
            setCardS [] 1    (S :$ (K :$ get0) :$ Get)
            setCardS [] slot get1
            applySCS [] 0    I
            applySCS [] 1    (Val 0)   
            applyCS K 1
            applyCS S 1
            applySCS [] 1 get0
            applySCS [] slot (Val 1)
    77-> do setCardS [] 0    fzfx
            setCardS [] 1    get0
            setCardS [] slot get0
            applySCS [] 0    I
            applySCS [] slot get0    
            applyCS K slot
            applyCS S slot
            applySCS [] slot get0    
            applySCS [] slot get1   
            applySCS [] slot I
    -7-> do setCardS [] 0    fzfx
            setCardS [] 1 get0
            setCardS [] slot get0
            applySCS [] 0    I
            applySCS [] 1 get0    
            applyCS K 1
            applyCS S 1
            applySCS [] 1 get0
            applySCS [] slot get1
    -77->do setCardS [] 0    fzfx
            setCardS [] 1    (get0 :$ I)
            applyCS K 0
            applyCS S 0
            setCardS [] 1    (S :$ (K :$ (S :$ (K :$ get0) :$ get0)) :$ get0)
            setCardS [] 0    get1
            setCardS [] slot get0
            applySCS [] 0    I
            applySCS [] slot get0
    8 -> do setCardS [] 0    fzfx
            setCardS [] slot $ lambdaCard "(%r get 0 (get r) (get r))"
            applySCS [] 0    I
            applySCS [] slot zero
    10 -> do iterator slot 5
             applyCS  K slot; applyCS S slot
             applySCS [] slot get0
    16 -> do setCardS [] 0    ffx
             setCardS [] slot (lambdaCard "(%r (get r) (get r) (get r)) 0")
    32 -> do iterator slot 16
             applyCS  K slot; applyCS S slot
             applySCS [] slot get0
    64 -> do setCardS [] 0    fzfx
             setCardS [] slot $ lambdaCard "(%r (get 0) (get r) ((get r) (get r)))"
             applySCS [] 0    I
             applySCS [] slot zero
    128 -> do iterator slot 64
              applyCS  K slot; applyCS S slot
              applySCS [] slot get0
    256 -> do setCardS [] 0    fzfx
              setCardS [] slot $ lambdaCard "(%r get 0 (get r) (get r) (get r))"
              applySCS [] 0    I
              applySCS [] slot zero
  where
    fzfx = lambdaCard "%z %f %x f (z f x)"
    ffx  = lambdaCard "%f %x f (f x)"
    get0 = lambdaCard "get 0"
    get1 = lambdaCard "get 1"
    build r@[two,three,five] = do
      setCardS [] 0  $ lambdaCard "%f %x f (f x)"
      when (two > 0)    $do setCardS [] two get0
      when (three > 0)  $do setCardS [] three get0
      when (three >= 0) $do applyCS K three; applyCS S three
      when (five >= 0)  $do setCardS [] five (Get :$ Val three)
                            applySCS [] five get0
      applySCS [] two I
      when (three >= 0) $do applySCS [] three (Get :$ Val two)
      when (five >= 0)  $do applySCS [] three (Get :$ Val three)
      
---
-- distribute vitality a bit to make zombie-help-bombs less effective.
--  of course a skill-full attacker might see the pattern and work around it.
distributeVitality = do
  iterator 3 64
  applySCS [0,1,2] 3 $ lambdaCard "%c %x help x (succ x) 4096 (c (succ (succ (succ x))))"
  applySCS [] 3 Attack
  applySCS [] 3 zero
  mapM_ (\slot -> applyCS I slot) [0..255]


help10slot = 9
installHelp10 =
  recurse 


-- maximizeSelf = %slot %cont (help slot slot 8192) * 10
--                            (help slot slot 16384) * 10
--                            cont

{-
maximizeSelf = 
  recurse 4 5
  tr = %y %sw sw (K get y tr) (recurse4) 
                 ((%c (%x%y help x x y) (K get y 0) (K (K get y 1) c) ) y
-}

{- kill oslot = [maximizeSelf slot
                (help  slot slot 32768) * 10
                (attack slot oslot 48*1024)] *2
   instzombie oslot = (dec myzslot) * 64
                  kill oslot
                  zombie oslot (zombie myzslot (%x instzombie (K oslot x)))
-}

--prepareRevivers slots = do
  -- slot == maximizeSelf slot
  --         revive 0 (help slot 0 32768)
  --         for n in [important regs ending with first reviver] 
  --           revive (succ n) (help n (succ n) 32768)
  --         for n in [revivers]
  --           (help n n 32768)*2 (revive (dbl n)) (help n (dbl n) 32768) 
surefire = do
  iterator 2 5
  applyCS K 2 
  applyCS S 2
  applySCS [0,1] 2 $ lambdaCard "%x %c %cont %y help x x y (c cont y)"
  applyCS K 2
  applyCS S 2
  applySCS [] 2 Get
  setCardS [] 1 $ lambdaCard "get 2"  
  setNumber 0 25
  applySCS [] 1 zero
  applySCS [0] 1 $ lambdaCard "%cont %y help 25 26 (K 17400 y) (cont y)"  
  setNumber 0 26
  applySCS [] 2 zero
  applySCS [0] 2 $ lambdaCard "(%cont %y attack 26 0 y (get 1 cont y))"  
--  setCardS [] 0 $ lambdaCard "get 2"
--  setCardS [1,2,3] 2 $ 


main = do
  args <- getArgs
  rungame (head args == "0") surefire
  return ()
          