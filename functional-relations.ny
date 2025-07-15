{` -*- narya-prog-args: ("-proofgeneral" "-hott") -*- `}

import "torsorial-type-families"

def isFunctionalRelation (A : Type) (B : Type) (R : A → B → Type) : Type
  ≔ (a : A) → isTorsorial B (R a)
