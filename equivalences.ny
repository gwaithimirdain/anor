{` -*- narya-prog-args: ("-proofgeneral" "-hott") -*- `}

import "1-1-correspondences"
import "graphs-of-functions"
import "torsorial-type-families"

def isEquiv (A B : Type) (f : A → B) : Type
  ≔ (b : B) → isTorsorial A (a ↦ graphFunction A B f a b)

def is11_of_isEquiv (A B : Type) (f : A → B) (H : isEquiv A B f)
  : is11 A B (graphFunction A B f)
  ≔ (contrr ≔ isFunctionalRelation_graphFunction A B f, contrl ≔ H)
