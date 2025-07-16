{` -*- narya-prog-args: ("-proofgeneral" "-hott") -*- `}

import "contractible-types"
import "truncation-levels"

def isTruncated (k : 𝕋) (A : Type) : Type ≔ match k [
| neg_two. ↦ isContr A
| suc. k ↦ (x y : A) → isTruncated k (Id A x y)]
