{` -*- narya-prog-args: ("-proofgeneral" "-hott") -*- `}


def 𝕎 (A : Type) (B : A → Type) := data [
| tree. (a : A) (f : B a → 𝕎 A B)
]
