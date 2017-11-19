module Refined 


data Vect : (len : Nat) -> (elem : Type) -> Type where
  Nil  : Vect Z elem
  (::) : (x : elem) -> (xs : Vect len elem) -> Vect (S len) elem



-- Definitions 

digits : List Char
digits = ['0'..'9']

lowerCase : List Char
lowerCase = ['a'..'z']

upperCase : List Char
upperCase = ['A'..'Z']


-- Elem property
data Elem : a -> List a -> Type where
  Here : Elem x (x :: xs)
  There : (later : Elem x xs) -> Elem x (y :: xs)


-- Elem examples


aIsLC : Elem 'a' Refined.lowerCase


bIsLC : Elem 'b' Refined.lowerCase


kIsLC : Elem 'k' Refined.lowerCase




-- Not true....












-- Properties
Digits : Char -> Type 


LowerCase : Char -> Type


UpperCase : Char -> Type












-- Dependent pairs
x : (n : Nat ** Vect n Int)














-- Refinement type 

-- x : Refined Char UpperCase 







--refbIsLC : Refined Char LowerCase










-- Conversion

--toRefined : { a : Type } -> { P : a -> Type } -> ??? 





--testRefA : Refined Char LowerCase





--testRefB : Char `Refined` LowerCase






--fromRefined : { P : Char -> Type } -> ??? 



-- Examples


printChar : Char -> IO ()
printChar = printLn

main : IO () 

















{-

Idris Refined
https://github.com/janschultecom/idris-refined

-}





