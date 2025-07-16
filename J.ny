{` -*- narya-prog-args: ("-proofgeneral" "-hott") -*- `}

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
  let SqA
    ≔ (x00 : A) (x01 : A) (x02 : Id A x00 x01) (x10 : A) (x11 : A)
        (x12 : Id A x10 x11) (x20 : Id A x00 x10) (x21 : Id A x01 x11) ↦
      A⁽ᵉᵉ⁾ x02 x12 x20 x21 in
  let sq ≔ refl ((y ↦ Id A a y) : A → Type) (refl a) in
  let q ≔ sq .trr.1 (refl a) in
  let s ≔ sq .liftr.1 (refl a) in
  let cube
    ≔ refl SqA (refl a) (refl a) a⁽ᵉᵉ⁾ (refl a) (refl a) s a⁽ᵉᵉ⁾ a⁽ᵉᵉ⁾ in
  let t ≔ cube .trr.1 a⁽ᵉᵉ⁾ in
  let c ≔ cube .liftr.1 a⁽ᵉᵉ⁾ in
  sym (P⁽ᵉᵉ⁾ (sym t) c⁽³²¹⁾) (refl pa) (refl P q (sym s) .liftr.1 pa)
    .trr.1 (refl pa)
