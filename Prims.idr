module Prims

x:Int
x=42

foo:String
foo="Sausage machine"

bar:Char
bar='Z'

quux:Bool
quux=False

myplus:Nat->Nat->Nat
myplus Z y = y
myplus (S k) y = S (plus k y)


myreverse : List a -> List a
myreverse xs = revAcc [] xs where
  revAcc : List a -> List a -> List a
  revAcc acc [] = acc
  revAcc acc (x::xs) = revAcc (x::acc) xs


foo2 : Int -> Int
foo2 x = case isLT of
          Yes => x*2
          No => x*4
      where
        data myLT = Yes | No
        isLT:myLT
        isLT = if x <20 then Yes else No


even : Nat -> Bool
even Z = True
even (S k) = odd k where
  odd Z = False
  odd (S k) = even k
