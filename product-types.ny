{` -*- narya-prog-args: ("-proofgeneral" "-hott") -*- `}

def prod (A B : Type) : Type ≔ sig ( pr1 : A, pr2 : B )

notation(1) A "×" B ≔ prod A B
