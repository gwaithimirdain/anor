{` -*- narya-prog-args: ("-proofgeneral" "-hott") -*- `}

import "connection-squares-of-identifications"
import "groupoid-operations-on-identifications"
import "iterated-identity-types"
import "squares-of-identifications"
import "transport-along-identifications"

{` The Paulin-Möhring identity type eliminator, constructed as in cubical type theory. `}
def J (A : Type) (a : A) (P : (y : A) → Id A a y → Type)
  (pa : P a (refl a)) (b : A) (p : Id A a b)
  : P b p
  ≔
  let sq ≔ refl ((y ↦ Id A a y) : A → Type) p in
  let q ≔ sq .trr.1 (refl a) in
  let s ≔ sq .liftr.1 (refl a) in
  refl P q (sym s) .trr.1 pa

` A⁽ᵉᵉ⁾ z 
def coconn (A : Type) (x y : A) (p : Id A x y)
  : Sq A x x (refl x) x y p (refl x) p
  ≔
  let P ≔ (z : A) (q : Id A x z) → Sq A x x (refl x) x z q (refl x) q in
  let p0 := (refl (refl x)) in
  let sq ≔ refl ((z ↦ Id A x z) : A → Type) p in
  let q ≔ sq .trr.1 (refl x) in
  let s ≔ sym (sq .liftr.1 (refl x)) in
`  refl P q s .trr.1 p0

  J A x (z q ↦ Sq A x x (refl x) x z q (refl x) q) (refl (refl x)) y p

{` Using a connection square, we can prove the left identity law by a similar cylindrical transport. `}
def concat_1p (A : Type) (x y : A) (p : Id A x y)
  : Id (Id A x y) (concat A x x y (refl x) p) p
  ≔ refl (Id2 A x) p (refl ((z ↦ Id A x z) : A → Type) p .liftr.1 (refl x))
        (coconn A x y p)
      .trr.1 (refl (refl x))

{` Finally, we can prove the typal β-rule for the J-eliminator. `}
def Jβ (A : Type) (a : A) (P : (y : A) → Id A a y → Type)
  (pa : P a (refl a))
  : Id (P a (refl a)) pa (J A a P pa a (refl a))
  ≔
  let sq ≔ refl ((y ↦ Id A a y) : A → Type) (refl a) in
  let q ≔ sq .trr.1 (refl a) in
  let s ≔ sq .liftr.1 (refl a) in
  let cube
    ≔ refl (Sq A) (refl a) (refl a) a⁽ᵉᵉ⁾ (refl a) (refl a) s a⁽ᵉᵉ⁾ a⁽ᵉᵉ⁾
    in
  let t ≔ cube .trr.1 a⁽ᵉᵉ⁾ in
  let c ≔ cube .liftr.1 a⁽ᵉᵉ⁾ in
  sym (P⁽ᵉᵉ⁾ (sym t) c⁽³²¹⁾) (refl pa) (refl P q (sym s) .liftr.1 pa)
    .trr.1 (refl pa)
