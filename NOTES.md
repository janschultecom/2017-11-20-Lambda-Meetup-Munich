
* Scala Refinement library
  - URL
  - Example

* Idris
  - Elem data type
    * Elem 'a' --> Here
    * Elem 'b' --> There
    * Elem 'b' --> Here --> Error
    * Proof search 'k'
    * Elem 'a' ['A'] -> Void

  - Properties
    * Type constructor

  - Dependent pairs
    * 3 [1,2,3]
    * 2 [1,2,3]
    * _ value inference

  - Type declaration Refined
    * Type -> Type constrcutor -> Type
    * Idris DPair

  - Example refined type
    test1 : Refined Char LowerCase
    test1 = ( 'b'  ** (There Here) )

  - Conversion toRefined
    * definition
    * Type -> automatic proof -> Refined
    * test2 'a'
    * test2 'A' --> Error

  - Conversion fromRefined
   * Refined type -> type
   * fromRefinedChar c = fst c
   * fromRefinedChar = fst -- point free notation

  - Example
    * printChar
    * main

  - Idris refined
    * URL
    * Give me 61 stars
