{` -*- narya-prog-args: ("-proofgeneral" "-hott") -*- `}

def ℕ : Type := data [
| zero.
| suc. (_ : ℕ)
]
