{` -*- narya-prog-args: ("-proofgeneral" "-hott") -*- `}

{` The type of squares in a type is oriented as follows:

          x12
     x10 ----> x11
      ∧         ∧
  x20 |         | x21
      |         |
     x00 ----> x01.
          x02
 `}

def Sq (A : Type) (x00 x01 : A) (x02 : Id A x00 x01) (x10 x11 : A)
  (x12 : Id A x10 x11) (x20 : Id A x00 x10) (x21 : Id A x01 x11)
  : Type
  ≔ A⁽ᵉᵉ⁾ x02 x12 x20 x21
