{` -*- narya-prog-args: ("-proofgeneral" "-hott") -*- `}

import "J"

def fiber (A B : Type) (f : A → B) (b : B) : Type ≔ sig (
  val1 : A,
  eq : Id B (f val1) b )

def Id_fiber (A B : Type) (f : A → B) (b : B) (x y : fiber A B f b) : Type
  ≔ sig (
  val : Id A (x .val1) (y .val1),
  eq : Id (Id B (f (x .val1)) b) (x .eq)
         (concat B (f (x .val1)) (f (y .val1)) b ? (y .eq)) )
