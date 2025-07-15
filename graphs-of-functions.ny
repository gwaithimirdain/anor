{` -*- narya-prog-args: ("-proofgeneral" "-hott") -*- `}

import "functional-relations"
import "torsorial-type-families"

`The graph of a function

def graphFunction (A B : Type) (f : A → B) : A → B → Type
  ≔ x y ↦ Id B (f x) y

`The graph of a function is a functional relation

def isFunctionalRelation_graphFunction (A B : Type) (f : A → B)
  : isFunctionalRelation A B (graphFunction A B f)
  ≔ a ↦ isTorsorial_idfrom B (f a)
