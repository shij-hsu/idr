
data Vect : Nat -> Type -> Type where
    Nil : Vect Z a
    (::) : a-> Vect k a-> Vect (S k) a

(++) : Vect n a -> Vect m a -> Vect (n+m) a
(++) Nil ys =ys
(++) (x::xs) ys = x :: xs ++ ys

data Fin : Nat -> Type where
    FZ : Fin (S k)
    FS : Fin k  -> Fin (S k) 

index : Fin n -> Vect n a -> a
index FZ (x::xs) = x
index (FS k) (x::xs) = index k xs


isEmpty : Vect n a -> Bool
isEmpty {n=Z} _ = True
isEmpty {n=S k} _ = False

1::(2::(3::Nil)) : Vect 3 Integer