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
