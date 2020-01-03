{-@ LIQUID "--no-termination" @-}

module Redblack where
import Language.Haskell.Liquid.Prelude

data Color = Red | Black deriving (Eq, Show)

data RBTree a v = Leaf
              | Node { nCol   :: Color
                     , nKey   :: a
                     , nvalue :: v
                     , nLeft  :: !(RBTree a v)
                     , nRight :: !(RBTree a v)
                     }
              deriving (Show)


{-@ data RBTree a v <l :: a -> a -> Bool, r :: a -> a -> Bool>
            = Leaf
            | Node { nCol   :: Color
                   , nKey   :: a
                   , nvalue :: v
                   , nLeft  :: RBTree <l, r> (a <l nKey>) v
                   , nRight :: RBTree <l, r> (a <r nKey>) v
                  }
@-}


-------------------------------------------------------------------------
--SPECIFICATIONS


-- | Black Height

{-@ measure isBH        :: RBTree a v -> Bool
    isBH (Leaf)         = true
    isBH (Node c x v l r) = (isBH l && isBH r && bh l = bh r)
  @-}

{-@ measure bh        :: RBTree a v -> Int
    bh (Leaf)         = 0
    bh (Node c x v l r) = bh l + if (c == Red) then 0 else 1
  @-}

-- | Color of a tree

{-@ measure col         :: RBTree a v-> Color
    col (Node c x v l r)  = c
    col (Leaf)            = Black
  @-}

{-@ measure isB         :: RBTree a v-> Bool
    isB (Leaf)            = false
    isB (Node c x v l r)  = c == Black
  @-}

{-@ predicate IsB T = not (col T == Red) @-}


-- | Ordered Red-Black Trees

{-@ type ORBT a v = RBTree <{\root v -> v < root }, {\root v -> v > root}> a v@-}

-- | Red-Black Trees

{-@ measure isRB        :: RBTree a v -> Bool
    isRB (Leaf)         = true
    isRB (Node c x v l r) = isRB l && isRB r && (c == Red => (IsB l && IsB r))
@-}

{-@ type RBT a  v1  = {v: ORBT a v1 | isRB v && isBH v } @-}
{-@ type RBTN a v1 N = {v: RBT a v1 | bh v = N }         @-}

{-@ type ORBTL a v1 X = RBT {v:a | v < X} v1 @-}
{-@ type ORBTG a v1 X = RBT {v:a | X < v} v1 @-}


-- | Almost Red-Black Trees

{-@ type ARBT a v1    = {v: ORBT a v1 | isARB v && isBH v} @-}
{-@ type ARBTN a v1 N = {v: ARBT a v1 | bh v = N }         @-}

{-@ measure isARB        :: (RBTree a v) -> Bool
    isARB (Leaf)           = true
    isARB (Node c x v l r) = (isRB l && isRB r)
@-}

-- | Conditionally Red-Black Tree

{-@ type ARBT2 a v1 L R = {v:ARBTN a v1 {bh L} | (IsB L && IsB R) => isRB v} @-}




----------------------------------------------------------------------------------

--{-@ reflect lookup' @-}
{-@ lookup' :: (Ord k, Eq k) => k -> v -> t:RBT k v -> v @-}
lookup' x def (Leaf)           = def
lookup' x def (Node _  k v l r) = if(x<k)      then lookup' x def l
                                else if(x>k) then lookup' x def r
                                else v


{-@ balance :: c:Color -> k:a -> t1:ORBT {k1:a | k1<k} v1-> v1 
     -> t2:{ ORBT  {k1:a | k1>k} v1 |    if (c==Black) then ((isRB t2 && isBH t2 && (bh t2 = bh t1)  && (isARB t1 && isBH t1) ) ||  (isRB t1 && isBH t1 && (bh t2 = bh t1)  && (isARB t2 && isBH t2) )  )  else
         (isRB t2 && isBH t2 && (bh t2 = bh t1) && isRB t1 && isBH t1 )
     } 
     -> t3:{ARBT a v1 | (if (c==Black) then (bh t3 = bh t1+1) else (bh t3 = bh t1)) && ((c == Red && IsB t1 && IsB t2) || (c == Black) => isRB t3) }
@-}-- να θυμηθω αν t1 t2 isB -> RB
balance Red    k t1                               vk t2                              = (Node Red k vk t1 t2)
balance Black  k (Node Red y vy (Node Red x vx a b) c)  vk t2                        = (Node Red y vy (Node Black x vx a b) (Node Black k vk c t2))
balance Black  k (Node Red x vx a (Node Red y vy b c))  vk t2                        = (Node Red y vy (Node Black x vx a b) (Node Black k vk c t2))
balance Black  k t1                               vk (Node Red z vz (Node Red y vy b c) d) = (Node Red y vy (Node Black k vk t1 b) (Node Black z vz c d))
balance Black  k t1                               vk (Node Red y vy b (Node Red z vz c d)) = (Node Red y vy (Node Black k vk t1 b) (Node Black z vz c d))
balance Black  k t1                               vk t2                              = (Node Black k vk t1 t2)





{-@ type BlackRBT a v1 = {v: RBT a v1| IsB v && bh v > 0} @-}

{-@ makeRed :: l:BlackRBT a v -> ARBTN a v {bh l - 1} @-}
makeRed (Node Black x v l r) = Node Red x v l r
makeRed _ = liquidError "nein"


{-@ makeBlack :: ARBT a v -> RBT a v @-}
makeBlack Leaf           = Leaf
makeBlack (Node _ x v l r) = Node Black x v l r


{-@ ins :: (Ord a) => a -> v1 -> t:RBT a v1 -> v:{ARBTN a v1 {bh t} | IsB t => isRB v} @-}
ins k kx (Leaf)            = Node Red k kx Leaf Leaf
ins k kx (Node Red y vy a b) =   if(k<y)      then  balance Red y (ins k kx a)  vy b
                               else if(y<k) then  balance Red y a  vy (ins k kx b)
                               else (Node Red  k kx a  b) 
ins k kx (Node Black y vy a b) =   if(k<y)      then  balance Black y (ins k kx a)  vy b
                               else if(y<k) then  balance Black y a  vy (ins k kx b)
                               else (Node Black  k kx a  b) 



{-@ insert :: k -> v -> RBT k v -> RBT k v @-}
insert x vx s = makeBlack (ins x vx s)
