{` -*- narya-prog-args: ("-proofgeneral" "-hott") -*- `}

import "sigma-types"

def isContr (A : Type) : Type ≔ sig (
  center : A,
  contract : (a : A) → Id A a center )
