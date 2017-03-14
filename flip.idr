-- 参考Belleve@zhihu

data Tree:Type -> Type where
    Leaf: a-> Tree a
    Branch : a->Tree a->Tree a->Tree a

flipTree : Tree a-> Tree a
flipTree (Leaf x)= Leaf x
flipTree (Branch x l r) = Branch x (flipTree r) (flipTree l)

flipTreeSym :  (t:Tree a) -> t = flipTree (flipTree t)
flipTreeSym (Leaf x) = Refl
flipTreeSym (Branch x l r) = do 
    let recL = flipTreeSym l
    let recR = flipTreeSym r
    rewrite recL in 
        rewrite recR in Refl

{-
map_id : Functor f => f a -> f a
map_id : map id

interface Functor f => VerifiedFunctor (f:Type->Type) where
    identity: (fa:fa) -> map_id fa = fa
    dist : (fa:fa) -> (g:b->c)->(h:a->b)->map (g.h) fa = (map g).(map h) $ fa

VerifiedFunctor List where
    identity [] = Refl
    identity (x:xs) = let ih = (identity xs) in rewrite ih in Refl

dist [] _ _ = Refl
dist (x:xs) g h = let ih = (dist xs g h) in rewrite ih in Refl
-}