{` -*- narya-prog-args: ("-proofgeneral" "-hott") -*- `}

def fiber (A B : Type) (f : A → B) (b : B) : Type ≔ sig (
  val : A,
  eq : Id B (f val) b )
