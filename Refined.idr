
--import Data.Vect


-- Elem property
data Elem : a -> List a -> Type where
  Here : Elem x (x :: xs)
  There : (later : Elem x xs) -> Elem x (y :: xs)


-- Elem examples















-- Definitions 


--digits : List Char
--digits = ['0'..'9']

--lowerCase : List Char
--lowerCase = ['a'..'z']

--upperCase : List Char
--upperCase = ['A'..'Z']






-- Properties












-- Dependent pairs
--x : (n : Nat ** Vect n Int)














-- Refinement type 
















-- Conversion















-- Examples





















{-

Thank you! 

Twitter: @janschultecom
Github: github.com/janschultecom

Idris Refined - https://github.com/janschultecom/idris-refined

Contributions welcome!!! :-)

-}





