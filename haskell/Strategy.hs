type Slots = Array Int (Int, Card)
data Player = Me | Him
type Strategy a = (Slots -> Slots -> Either a (Move, Strategy a))

instance Monoid MStrategy a where
  return a = \me him -> Left a
  (>>=) strat1 fstrat2 = \me him -> 
    (case strat1 me him of
        Left a -> (fstrat2 a)
        Right move cstrat -> Right (move, cstrat >>= fstrat2))
  
playMove :: Move -> MStrategy ()
playMove move = Right (move, return ())

getCard :: Player -> Int -> Strategy (Card)
getCard Me i = \me him -> Left (snd (me ! i))
getCard Him i = \me him -> Left (snd (him ! i))

getVitality :: Player -> Int -> Strategy (Int)
getVitality Me i = \me him -> Left (fst (me ! i))
getVitality Him i = \me him -> Left (fst (him ! i))

---------
-- Strategy set_number: set register r to number n.
---------
setNumber :: Int -> Int -> Strategy ()
setNumber slot num = 
  let numSteps n = if n == 0 then 2 else
                     (num_steps (n / 2)) + 1 + (n mod 2) in
  card <- getCard Me slot
  case card of
    Val i -> if i == n then return () else do
      case () of _
        | i < num / 2                          -> setNumber slot (num / 2)
        | i != 0 && i == num/2                 -> playMove AppCS(Dbl, slot)
        | i < num && (num - i < num_steps num) -> playMove AppCS(Succ, slot)
        | otherwise                            -> playMove AppCS(Put, slot))
      setNumber slot Num
    I -> do { playMove AppSC(slot, Val 0) ; setNumber slot Num }
    _ -> do { playMove AppCS(Put, slot) ; setNumber slot Num }

valToApp num 
  | num == 0 -> Val 0
  | num mod 2 = 1 -> App(Inc, valToApp $ num - 1)
  | otherwise     -> App(Dbl, valToApp $ num / 2)

applyCard slot (Val 0) = playMove AppCS(slot, Val 0)
applyCard slot (Val n) = applyCard slot (valToApp n)

applyCard 0 card =
  case card of
    App(c1,c2) -> do 
      playMove AppCS(K, 0)
      playMove AppCS(S, 0)
      applyCard 0 c1
      applyCard 0 c2
    _ ->
      playMove AppSC(0, card)

applyCard slot card =
  case card of
    App(c1,c2) | complex card -> do 
      setCard 0 c1
      applyCard 0 c2
      applyCard slot App(Get, Val 0)
               | simple card -> do 
      playMove AppCS(K, slot)
      playMove AppCS(S, slot)
      applyCard slot c1
      applyCard slot c2
    _ ->
      playMove AppSC(0, card)
  

setCard slot Val n = setNumber slot n
setCard slot App(c1,c2)
   | complex card c2 -> do
       setCard slot c2
       setCard 0 App(Get, Val slot)
       setCard slot c1
       applyCard c1 App(Get, Val 0)
   | otherwise -> do
       setCard slot c1
       applyCard slot c2
setCard slot c = do
   card <- getCard Me slot
   when card /= c case card of
     I -> AppSC(slot, c)
     _ -> do { AppCS(put, slot); setCard slot c }
