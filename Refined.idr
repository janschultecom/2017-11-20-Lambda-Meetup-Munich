


data Elem : a -> List a -> Type where
  Here : Elem x (x :: xs)
  There : (later : Elem x xs) -> Elem x (y :: xs)










































{-

Thank you! 

Twitter: @janschultecom
Github: github.com/janschultecom

Idris Refined - https://github.com/janschultecom/idris-refined

Contributions welcome!!! :-)

-}





