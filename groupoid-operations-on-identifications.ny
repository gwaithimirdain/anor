{` -*- narya-prog-args: ("-proofgeneral" "-hott") -*- `}

import "iterated-identity-types"

def concat (A : Type) (x y z : A) (p : Id A x y) (q : Id A y z) : Id A x z
  ≔ refl ((y ↦ Id A x y) : A → Type) q .trr.1 p

def inverse (A : Type) (x y : A) (p : Id A x y) : Id A y x
  ≔ refl ((z ↦ Id A z x) : A → Type) p .trr.1 (refl x)

{` The right identity law can be obtained by transporting along a cylinder. `}

def concat_p1 (A : Type) (x y : A) (p : Id A x y)
  : Id (Id A x y) (concat A x y y p (refl y)) p
  ≔ refl ((q ↦ Id2 A x y q p) : Id A x y → Type)
        (refl ((z ↦ Id A x z) : A → Type) (refl y) .liftr.1 p)
      .trr.1 (refl p)
