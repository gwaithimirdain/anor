{` -*- narya-prog-args: ("-proofgeneral" "-hott") -*- `}

def Σ (A : Type) (B : A → Type) : Type ≔ sig ( fst : A, snd : B fst )

