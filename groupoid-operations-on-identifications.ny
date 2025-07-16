{` -*- narya-prog-args: ("-proofgeneral" "-hott") -*- `}

import "connection-squares-of-identifications"
import "iterated-identity-types"
import "squares-of-identifications"

{` Concatenation p ∙ q of identifications p : Id A x y and q : Id A y z is an identification Id A x z that fits in a square

          q
    y --------> z
    ∧           ∧
  p |           | p ∙ q
    |           |
    x --------> x
       refl x
`}

def concat (A : Type) (x y z : A) (p : Id A x y) (q : Id A y z) : Id A x z
  ≔ Id (Id A) (refl x) q .trr p

def compute_concat (A : Type) (x y z : A) (p : Id A x y) (q : Id A y z)
  : Sq A x x (refl x) y z q p (concat A x y z p q)
  ≔ Id (Id A) (refl x) q .liftr p

{` The right identity law can be obtained by transporting along a cylinder. `}

def concat_p1 (A : Type) (x y : A) (p : Id A x y)
  : Id (Id A x y) (concat A x y y p (refl y)) p
  ≔ refl ((q ↦ Id2 A x y q p) : Id A x y → Type)
        (refl ((z ↦ Id A x z) : A → Type) (refl y) .liftr.1 p)
      .trr.1 (refl p)

{` Using a connection square, we can prove the left identity law by a similar cylindrical transport. `}

def concat_1p (A : Type) (x y : A) (p : Id A x y)
  : Id (Id A x y) (concat A x x y (refl x) p) p
  ≔ refl (Id2 A x) p (refl ((z ↦ Id A x z) : A → Type) p .liftr.1 (refl x))
        (coconn A x y p)
      .trr.1 (refl (refl x))

{` Inverting an identification p gives an identification p⁻¹ that fits in a square

         p⁻¹
    y --------> x
    ∧           ∧
  p |           | refl x
    |           |
    x --------> x
       refl x
`}

def inverse (A : Type) (x y : A) (p : Id A x y) : Id A y x
  ≔ Id (Id A) p (refl x) .trr (refl x)

def compute_inverse (A : Type) (x y : A) (p : Id A x y)
  : Sq A x x (refl x) y x (inverse A x y p) p (refl x)
  ≔ sym (Id (Id A) p (refl x) .liftr (refl x))
