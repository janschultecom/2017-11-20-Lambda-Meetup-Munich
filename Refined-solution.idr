module Refined

import Data.Vect

-- Elem property
data LElem : a -> List a -> Type where
  Here : LElem x (x :: xs)
  There : (later : LElem x xs) -> LElem x (y :: xs)










-- Definitions 


digits : List Char
digits = ['0'..'9']

lowerCase : List Char
lowerCase = ['a'..'z']

upperCase : List Char
upperCase = ['A'..'Z']




-- Elem examples



aIsLowerCase : LElem '0' Refined.digits
aIsLowerCase = Here 


notA : LElem 'a' ['A'] -> Void
notA (There Here) impossible
notA (There (There _)) impossible



-- Properties


Digits : Char -> Type 
Digits c = LElem c digits

LowerCase : Char -> Type
LowerCase c = LElem c lowerCase

UpperCase : Char -> Type
UpperCase c = LElem c upperCase








-- Dependent pairs
x : (n : Nat ** Vect n Int)
x = (_ ** [1,2,3])













-- Refinement type 

-- x : Refined Char UpperCase 


Refined : ( a : Type ) -> ( P : a -> Type ) -> Type 
Refined = DPair 





test1 : Refined Char LowerCase
test1 = ( 'b'  ** (There Here) )










-- Conversion

implicit
toRefined : { a : Type } -> { P : a -> Type } -> ( x : a) -> { auto property : P x } -> Refined a P 
toRefined c { property} = ( c ** property )


test2 : Refined Char LowerCase
test2 = 'a'

test3 : Char `Refined` LowerCase
test3 = 'b' 

implicit 
fromRefinedChar : { P : Char -> Type } -> Refined Char P -> Char
fromRefinedChar = fst

printChar : Char -> IO ()
printChar = printLn

main : IO () 
main = printChar test2 


-- Examples





















{-

Thank you! 

Twitter: @janschultecom
Github: github.com/janschultecom

Idris Refined - https://github.com/janschultecom/idris-refined

Contributions welcome!!! :-)

-}





