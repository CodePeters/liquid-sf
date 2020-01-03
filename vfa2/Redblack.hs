{-@ LIQUID "--reflection"                          @-}
{-@ LIQUID "--ple"                                 @-}

{-@ infix : @-}
{-@ infix ++ @-}

module Redblack where
import Language.Haskell.Liquid.ProofCombinators 	


{-@ type Key = Nat@-}
type Key = Int

data Color = Red | Black deriving (Eq)

data Pair a b = P a b


data Tree  v = E | T Color (Tree v) Key v (Tree v) deriving (Eq)



{-@
data Tree [tlen]  v = E
  | T   {  color  :: Color
         , bLeft  :: Tree  v
         , bKey   :: Key
         , bValue :: v
         , bRight :: Tree v }
@-}



{-@ reflect empty_tree @-}
empty_tree = E


{-@ measure tlen @-}
{-@ tlen :: Tree v-> Nat @-}
tlen :: (Tree v) -> Int
tlen (E)                 = 0
tlen (T color l key v  r) = 1 + (tlen l) + (tlen r)


{-@ reflect lookup' @-}
lookup' :: (Ord v, Eq v) => Key -> v -> Tree v -> v
lookup' x def (E)           = def
lookup' x def (T _  l k v r) = if(x<k)      then lookup' x def l
	                          else if(x>k) then lookup' x def r
	                          else v


{-@ reflect balance @-}
{-@ balance :: Color -> Tree v -> Nat -> v -> Tree v -> Tree v @-}
balance :: Color -> Tree v -> Key -> v -> Tree v -> Tree v
balance Red    t1                              k vk t2                              = (T Red t1 k vk t2)
balance Black  (T Red (T Red a x vx b) y vy c) k vk t2                              = (T Red (T Black a x vx b) y vy (T Black c k vk t2))
balance Black  (T Red a x vx (T Red b y vy c)) k vk t2                              = (T Red (T Black a x vx b) y vy (T Black c k vk t2))
balance Black  t1                              k vk (T Red (T Red b y vy c) z vz d) = (T Red (T Black t1 k vk b) y vy (T Black c z vz d))
balance Black  t1                              k vk (T Red b y vy (T Red c z vz d)) = (T Red (T Black t1 k vk b) y vy (T Black c z vz d))
balance Black  t1                              k vk t2                              = (T Black t1 k vk t2)


{-@ reflect makeBlack @-}
makeBlack :: Tree v -> Tree v
makeBlack E              = E
makeBlack (T _ a x vx b) = (T Black a x vx b)


{-@ reflect ins@-}
{-@ ins :: Nat -> v -> Tree v -> Tree v@-}
ins :: Key -> v -> Tree v -> Tree v
ins x vx (E)            = (T Red E x vx E)
ins x vx (T c a y vy b) = if(x<y)      then  balance c (ins x vx a) y vy b
	                        else if(y<x) then  balance c a y vy (ins x vx b)
	                        else (T c a x vx b)	

{-@ reflect insert @-}
{-@ insert :: Nat -> v -> Tree v -> Tree v @-}
insert :: Key -> v -> Tree v -> Tree v
insert x vx s = makeBlack (ins x vx s)

------------------------------------------------------------------------------------------------------------------


{-@ lemma_T_neq_E :: (Eq v) => c:Color -> l:Tree v -> k:Key -> val:v -> r:Tree v -> { (T c l k val r) /= E }@-}
lemma_T_neq_E :: (Eq v) => Color -> Tree v -> Key -> v -> Tree v -> Proof
lemma_T_neq_E c l k v r = ((T c l k v r) /= E ) *** QED

{-@ lemma_ins_not_E :: x:Key -> vx:v -> s:Tree v -> {ins x vx s /= E} @-}
lemma_ins_not_E :: Key -> v -> Tree v -> Proof
lemma_ins_not_E x vx E = trivial
lemma_ins_not_E x vx (T c a y vy b) 
        |(x<y)  = trivial
        |(x>y)  = trivial
        |(x==y) = trivial


{-@reflect searchTree @-}
searchTree :: Int ->  Tree v -> Int -> Bool
searchTree lo E hi             = (lo<=hi)
searchTree lo (T _ l k v r) hi = (searchTree lo l k) && (searchTree (k+1) r hi)


{-@ lemma_balance_SearchTree :: lo:Int -> hi:Int -> k:Key -> s1:{ Tree v| searchTree lo s1 k} -> s2:{ Tree v| searchTree (k+1) s2 hi} -> c:Color  
        -> kv:{v | searchTree lo (T c s1 k kv s2) hi}
        -> { searchTree  lo (balance c s1 k kv s2) hi} 
@-}
lemma_balance_SearchTree :: Int -> Int -> Key -> Tree v -> Tree v -> Color  -> v -> Proof
lemma_balance_SearchTree lo hi k s1 s2 c kv = undefined
lemma_balance_SearchTree lo hi k s1 s2 Red vk = trivial
lemma_balance_SearchTree lo hi k (T Red (T Red a x vx b) y vy c1) s2 Black vk = trivial
lemma_balance_SearchTree lo hi k (T Red a x vx (T Red b y vy c1)) s2 Black vk = trivial
lemma_balance_SearchTree lo hi k s1 (T Red (T Red b y vy c1) z vz d) Black vk = trivial
lemma_balance_SearchTree lo hi k s1 (T Red b y vy (T Red c1 z vz d)) Black vk = trivial          
lemma_balance_SearchTree lo hi k s1 s2 Black vk = trivial



{-@ lemma_ins_SearchTree :: x:Key -> vx:v -> lo:{Int | lo<=x } -> hi:{Int | x<hi } -> s:{Tree v | searchTree lo s hi} 
                -> {searchTree lo (ins x vx s) hi} 
@-}
lemma_ins_SearchTree :: Key -> v -> Int -> Int -> Tree v -> Proof
lemma_ins_SearchTree x vx lo hi E = trivial
lemma_ins_SearchTree x vx lo hi (T c l k vk r) 
            | (x<k) = [lemma_ins_SearchTree x vx lo k l,    lemma_balance_SearchTree lo hi k (ins x vx l) r c vk] *** QED
            | (x>k)	= [lemma_ins_SearchTree x vx (k+1) hi r,lemma_balance_SearchTree lo hi k l (ins x vx r) c vk] *** QED
            | otherwise = trivial


{-@ empty_tree_SearchTree :: lo:Int -> hi:{Int | lo <= hi } -> {searchTree lo empty_tree hi} @-}
empty_tree_SearchTree :: Int -> Int -> Proof
empty_tree_SearchTree lo hi = trivial


{-@ lemma_SearchTree:: lo:Int -> hi:Int -> t: {Tree v| searchTree lo t hi} -> {lo<=hi} @-}
lemma_SearchTree :: Int -> Int -> Tree v -> Proof
lemma_SearchTree lo hi E = trivial
lemma_SearchTree lo hi (T c l k vk r) = [lemma_SearchTree lo k l, lemma_SearchTree (k+1) hi r] *** QED


{-@ lemma_expand_range_SearchTree:: lo:Int -> hi:Int -> s: {Tree v| searchTree lo s hi} -> lo':{Int | lo'<=lo } -> hi':{Int | hi<=hi' } -> {searchTree lo' s hi'} @-}
lemma_expand_range_SearchTree :: Int -> Int -> Tree v -> Int -> Int -> Proof
lemma_expand_range_SearchTree lo hi E lo' hi' = trivial
lemma_expand_range_SearchTree lo hi (T c l k vk r) lo' hi'
       = ( lemma_SearchTree lo k l,
           lemma_SearchTree (k+1) hi r,
       	   lemma_expand_range_SearchTree lo k l lo' k , 
       	   lemma_expand_range_SearchTree (k+1) hi r (k+1) hi' ) *** QED




{-@ reflect is_redblack @-}
{-@ is_redblack :: Tree v -> Color -> Nat -> Bool @-}
is_redblack :: Tree v -> Color -> Int -> Bool
is_redblack  E                   c     0  = True
is_redblack (T Red   tl k kv tr) Black n  = is_redblack tl Red   n && is_redblack tr Red   n
is_redblack (T Black tl k kv tr) c     0  = False
is_redblack (T Black tl k kv tr) c     n  = is_redblack tl Black (n-1) && is_redblack tr Black (n-1) 
is_redblack  _                   _     _  = False


{-@ lemma_is_redblack_toblack :: n:Nat -> s:{ Tree v | is_redblack s Red n} -> { is_redblack s Black n } @-}
lemma_is_redblack_toblack :: Int -> Tree v -> Proof
lemma_is_redblack_toblack n E = trivial
lemma_is_redblack_toblack n (T Red tl k kv tr)   = trivial
lemma_is_redblack_toblack n (T Black tl k kv tr) = trivial


{-@ lemma_makeblack_fiddle:: n:Nat -> s:{Tree v | is_redblack s Black n } -> (n':: {v:Int | v>=0}, {is_redblack (makeBlack s) Red n'}) @-}
lemma_makeblack_fiddle :: Int -> Tree v -> (Int , Proof)
lemma_makeblack_fiddle 0 E = (0, trivial )
lemma_makeblack_fiddle n E = (n+1, trivial )
lemma_makeblack_fiddle n (T Red tl k kv tr) = (n+1, [lemma_is_redblack_toblack n tl, lemma_is_redblack_toblack n tr]*** QED )
lemma_makeblack_fiddle n (T Black tl k kv tr) = (n, trivial )

{-@ reflect nearly_redblack @-}
{-@ nearly_redblack :: Tree v -> Nat -> Bool @-}
nearly_redblack :: Tree v -> Int -> Bool
nearly_redblack (T Red tl k kv tr)    n = is_redblack tl Black n && is_redblack tr Black n
nearly_redblack (T Black tl k kv tr)  0 = False
nearly_redblack (T Black tl k kv tr)  n = is_redblack tl Black (n-1) && is_redblack tr Black (n-1)
nearly_redblack  E                    n = False 

--struggling in theorems below....  :(

-- @ lemma_ins_is_redblack1 :: x:Key -> vx:v -> s:Tree v -> n:{Nat |  is_redblack s Red n}
--         ->{ is_redblack (ins x vx s) Black n }  
-- @
-- lemma_ins_is_redblack1 :: Key -> v -> Tree v -> Int -> Proof
-- lemma_ins_is_redblack1 x vx s n = undefined


-- {-@ lemma_ins_is_redblack :: x:Key -> vx:v -> s:Tree v -> n:{Nat |  is_redblack s Black n}
--         ->{ nearly_redblack (ins x vx s) n }  
-- @-}
-- lemma_ins_is_redblack :: Key -> v -> Tree v -> Int -> Proof
-- --lemma_ins_is_redblack x vx E n = trivial
-- --lemma_ins_is_redblack x vx (T Red a y vy b) n 
--              -- | x<y =   nearly_redblack (ins x vx (T Red a y vy b)) n
--              --       ==. nearly_redblack ( balance Red (ins x vx a) y vy b ) n
--              --       ==. nearly_redblack ( T Red (ins x vx a) y vy b ) n
--              --       ==. (is_redblack (ins x vx a) Black n && is_redblack b Black n)
--              --       ==. True ? lemma_ins_is_redblack1 x vx a n &&& lemma_is_redblack_toblack  n b
--              --       *** QED
--               -- | x>y =  nearly_redblack (ins x vx (T Red a y vy b)) n
--               --      ==. nearly_redblack ( balance Red (ins x vx a) y vy b ) n
--               --      ==. nearly_redblack ( T Red a y vy (ins x vx b) ) n
--               --      ==. (is_redblack a Black n && is_redblack (ins x vx b) Black n)
--               --      ==. True ? lemma_ins_is_redblack1 x vx b n &&& lemma_is_redblack_toblack  n a
--               --      *** QED     
--               -- | x==y =  nearly_redblack (ins x vx (T Red a y vy b)) n
--               --      ==. nearly_redblack (T Red  a x vx b ) n
--               --      ==. (is_redblack a Black n && is_redblack (ins x vx b) Black n)
--               --      ==. True ? lemma_is_redblack_toblack n b  &&& lemma_is_redblack_toblack  n a
--               --      *** QED  
-- lemma_ins_is_redblack x vx (T Black a y vy b) n 
--                  | x< y && n> 0 =   nearly_redblack (ins x vx (T Black a y vy b)) n 
--                         ==. nearly_redblack ( balance Black (ins x vx a) y vy b) n
--                         ==. nearly_redblack ( T Black (ins x vx a) y vy b) n
--                         ==. (is_redblack (ins x vx a) Black (n-1) && is_redblack b Black (n-1))
--                         ==. True ? lemma_ins_is_redblack1 x vx a (n-1) 
--                         *** QED       
 






