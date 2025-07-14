{` -*- narya-prog-args: ("-proofgeneral" "-hott") -*- `}

import "contractible-types"
import "sigma-types"

def isTorsorial (A : Type) (B : A → Type) : Type ≔ isContr (Σ A B)

def istorsorial_idfrom (A : Type) (a0 : A)
  : isTorsorial A (a1 ↦ Id A a0 a1)
  ≔ (
  center ≔ (a0, refl a0),
  contract ≔ a1_a2 ↦
    let a1 ≔ a1_a2 .fst in
    let a2 ≔ a1_a2 .snd in
    (refl ((z ↦ Id A z a0) : A → Type) a2 .trr (refl a0),
     sym (refl ((z ↦ Id A z a0) : A → Type) a2 .liftr (refl a0))))
