{` -*- narya-prog-args: ("-proofgeneral" "-hott") -*- `}

import "squares-of-identifications"

{` A connection is filler for a square of the form

       refl z
    z --------> z
    ∧           ∧
  p |           | refl z
    |           |
    x --------> z
        p
 `}

def conn (A : Type) (x y : A) (p : Id A x y)
  : Sq A x y p y y (refl y) p (refl y)
  ≔
  let P ≔ (z : A) (q : Id A x z) ↦ Sq A x z q z z (refl z) q (refl z) in
  let p0 ≔ (refl (refl x)) in
  let sq ≔ refl ((z ↦ Id A x z) : A → Type) p in
  let q ≔ sq .trr.1 (refl x) in
  let s ≔ sym (sq .liftr.1 (refl x)) in
  refl P q s .trr.1 p0

{` A coconnection square is a filler for a square of the form

               p
         x --------> z
         ∧           ∧
  refl x |           | p
         |           |
         x --------> x.
            refl x
`}

def coconn (A : Type) (x y : A) (p : Id A x y)
  : Sq A x x (refl x) x y p (refl x) p
  ≔
  let P ≔ (z : A) (q : Id A x z) ↦ Sq A x x (refl x) x z q (refl x) q in
  let p0 ≔ (refl (refl x)) in
  let sq ≔ refl ((z ↦ Id A x z) : A → Type) p in
  let q ≔ sq .trr.1 (refl x) in
  let s ≔ sym (sq .liftr.1 (refl x)) in
  refl P q s .trr.1 p0
