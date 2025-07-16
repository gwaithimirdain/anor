{` -*- narya-prog-args: ("-proofgeneral" "-hott") -*- `}

`The type of truncation levels

def 𝕋 : Type ≔ data [ neg_two. : 𝕋 | suc. : (_ : 𝕋) → 𝕋 ]

def neg_one : 𝕋 ≔ suc. neg_two.

def zero : 𝕋 ≔ suc. neg_one
