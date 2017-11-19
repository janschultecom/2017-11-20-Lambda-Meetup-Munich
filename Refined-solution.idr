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
aIsLC = Here  


bIsLC : Elem 'b' Refined.lowerCase
bIsLC = There Here  


kIsLC : Elem 'k' Refined.lowerCase
kIsLC = There (There (There (There (There (There (There (There (There (There Here)))))))))

notA : Elem 'a' ['A'] -> Void 
notA (There Here) impossible
notA (There (There _)) impossible


-- Not true....












-- Properties
Digits : Char -> Type 
Digits c = Elem c Refined.digits


LowerCase : Char -> Type
LowerCase c = Elem c Refined.lowerCase 


UpperCase : Char -> Type
UpperCase c = Elem c Refined.upperCase












-- Dependent pairs
x : (n : Nat ** Vect n Int)
x = (_ ** [1,2,3])














-- Refinement type 

Refined : (a: Type) -> ( P : a -> Type ) -> Type 
Refined = DPair 






refbIsLC : Refined Char LowerCase
refbIsLC = ('b' ** There Here ) 









-- Conversion

implicit 
toRefined : { a : Type } -> { P : a -> Type } -> ( x : a) -> { auto property: P x } -> Refined a P 
toRefined x { property } = ( x ** property ) 





testRefA : Refined Char LowerCase
testRefA = 'a'




testRefB : Char `Refined` LowerCase
testRefB = 'b'




implicit 
fromRefinedChar : { P : Char -> Type } -> Refined Char P -> Char 
fromRefinedChar = fst


-- Examples


printChar : Char -> IO ()
printChar = printLn

main : IO () 
main = printChar Refined.testRefA















{-

Idris Refined
https://github.com/janschultecom/idris-refined

-}





