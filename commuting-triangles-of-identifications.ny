{` -*- narya-prog-args: ("-proofgeneral" "-hott") -*- `}

import "groupoid-operations-on-identifications"
import "squares-of-identifications"

{` A commuting triangle of identifications

        q
   x ------> y
    \       /
   p \  ⇒  / r
      \   /
       ∨ ∨
        z.

 is given by a filler for a square of the following form:

       refl z
    z --------> z
    ∧           ∧
  p |           | r
    |           |
    x --------> y
          q

`}

def triangle_Id (A : Type) (x y z : A) (left : Id A x z) (right : Id A y z)
  (top : Id A x y)
  : Type
  ≔ Sq A x y top z z (refl z) left right
