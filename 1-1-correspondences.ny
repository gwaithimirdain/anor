{` -*- narya-prog-args: ("-proofgeneral" "-hott") -*- `}

import "contractible-types"
import "sigma-types"
import "torsorial-type-families"

def is11 (A B : Type) (R : A → B → Type) : Type ≔ sig (
  contrr : (a : A) → isTorsorial B (R a),
  contrl : (b : B) → isTorsorial A (a ↦ R a b) )
