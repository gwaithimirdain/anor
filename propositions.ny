{` -*- narya-prog-args: ("-proofgeneral" "-hott") -*- `}

import "contractible-types"
import "truncated-types"
import "truncation-levels"

def isProp (A : Type) : Type ≔ isTruncated neg_one A

def isProofIrrelevant (A : Type) : Type ≔ A → isContr A

def allElementsEqual (A : Type) : Type ≔ (x y : A) → Id A x y

def isProp_isProofIrrelevant (A : Type) (H : isProofIrrelevant A)
  : isProp A
  ≔ x y ↦ ?
