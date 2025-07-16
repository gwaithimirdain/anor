{` -*- narya-prog-args: ("-proofgeneral" "-hott") -*- `}

import "groupoid-operations-on-identifications"
import "sigma-types"

def isContr (A : Type) : Type ≔ sig (
  center : A,
  contraction : (a : A) → Id A a center )

def allElementsEqual_isContr (A : Type) (H : isContr A) (x y : A)
  : Id A x y
  ≔
  let c ≔ H .center in
  let γ ≔ H .contraction in
  concat A x c y (γ x) (inverse A y c (γ y))

def isProp_isContr (A : Type) (H : isContr A) (x y : A)
  : isContr (Id A x y)
  ≔ (center ≔ allElementsEqual_isContr A H x y, contraction ≔ ?)
