-- 自己写的一个一个链表翻转程序和验证程序


{- 翻转函数 -}
myreverse : List a-> List a
myreverse [] = []
myreverse (x::xs) = myreverse xs ++ [x]

{- 引理1 -}
app_nil_r : (l:List a)->(l++[]=l)
app_nil_r [] = Refl
app_nil_r (x::xs) = 
    let ind_xs = app_nil_r xs in
        rewrite ind_xs in Refl

{- 引理2：结合性 -}
app_assoc : (l1: List a) -> (l2 : List a) -> (l3:List a) -> ((l1++l2)++l3=l1++(l2++l3))
app_assoc [] l2 l3 = Refl
app_assoc (x::xs) l2 l3 = 
    let ind_xs = app_assoc xs l2 l3 in 
        rewrite ind_xs in Refl

{- 引理3：分配律 -}
app_distr : (l1:List a)->(l2:List a)->(myreverse (l1++l2)=myreverse l2++myreverse l1)
app_distr [] l2 = 
    rewrite app_nil_r (myreverse l2) in Refl
app_distr (x::xs) l2 = 
    rewrite app_distr xs l2 in 
        rewrite app_assoc (myreverse l2) (myreverse xs) [x] in Refl

{- 定理：链表翻转的函数的逆元是其自身 -}
myreverseSym : (l:List a)->(l=myreverse (myreverse l))
myreverseSym [] = Refl
myreverseSym (x::xs) = 
    let ind_xs = myreverseSym xs in 
        rewrite app_distr (myreverse xs) [x] in 
            rewrite ind_xs in Refl