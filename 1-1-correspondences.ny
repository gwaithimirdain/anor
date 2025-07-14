{` -*- narya-prog-args: ("-proofgeneral" "-hott") -*- `}

import "sigma-types"
import "contractible-types"

def is11 (A B : Type) (R : A → B → Type) : Type ≔ sig (
  contrr : (a : A) → isContr (Σ B (b ↦ R a b)),
  contrl : (b : B) → isContr (Σ A (a ↦ R a b)) )
