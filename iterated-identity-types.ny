{` -*- narya-prog-args: ("-proofgeneral" "-hott") -*- `}

{` Two-dimensional globular identity types (which compute to squares with refl on two sides). `}

def Id2 (A : Type) (x y : A) (p q : Id A x y) : Type ≔ Id (Id A x y) p q

