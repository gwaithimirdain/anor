{` -*- narya-prog-args: ("-proofgeneral" "-hott") -*- `}

import "groupoid-operations-on-identifications"
import "J"
import "commuting-triangles-of-identifications"

def fiber (A B : Type) (f : A → B) (b : B) : Type ≔ sig (
  val : A,
  eq : Id B (f val) b )

def Id_fiber (A B : Type) (f : A → B) (b : B) (x y : fiber A B f b) : Type
  ≔ sig (
  val : Id A (x .val) (y .val),
  eq : triangle_Id B (f (x .val)) (f (y .val)) b (x .eq) (y .eq) (ap f val) )

def make_eq_fiber (A B : Type) (f : A → B) (b : B) (x y : fiber A B f b)
  (p : Id A (x .val) (y .val))
  (q : triangle_Id B (f (x .val)) (f (y .val)) b (x .eq) (y .eq) (ap f p))
  : Id (fiber A B f b) x y
  ≔ (p, q)
