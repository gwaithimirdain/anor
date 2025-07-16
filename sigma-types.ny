{` -*- narya-prog-args: ("-proofgeneral" "-hott") -*- `}

import "fibers-of-maps"

`Σ-types

def Σ (A : Type) (B : A → Type) : Type ≔ sig ( fst : A, snd : B fst )

`Functoriality of Σ-types

def mapΣ (A : Type) (B : A → Type) (C : Type) (D : C → Type) (f : A → C)
  (g : (a : A) → B a → D (f a))
  : Σ A B → Σ C D
  ≔ x ↦ (f (x .fst), g (x .fst) (x .snd))

`The map on total spaces induced by a family of maps

def tot (A : Type) (B C : A → Type) (f : (a : A) → B a → C a)
  : Σ A B → Σ A C
  ≔ mapΣ A B A C (x ↦ x) f

def fiber_tot (A : Type) (B C : A → Type) (f : (a : A) → B a → C a)
  (x : Σ A C)
  : Type
  ≔ fiber (Σ A B) (Σ A C) (tot A B C f) x

`Compute the fiber of tot

def type_compute_fiber_tot (A : Type) (B C : A → Type)
  (f : (a : A) → B a → C a) (x : Σ A C)
  : Type
  ≔ fiber (B (x .fst)) (C (x .fst)) (f (x .fst)) (x .snd)

def make_fiber_tot (A : Type) (B C : A → Type) (f : (a : A) → B a → C a)
  (x : Σ A C) (y : type_compute_fiber_tot A B C f x)
  : fiber_tot A B C f x
  ≔
  let x0 ≔ x .fst in
  let y0 ≔ y .val in
  let y1 ≔ y .eq in
  ((x0, y0), (refl x0, y1))

{`
def destruct_fiber_tot (A : Type) (B C : A → Type)
  (f : (a : A) → B a → C a) (x : Σ A C) (y : fiber_tot A B C f x)
  : type_compute_fiber_tot A B C f x
  ≔
  let y0 ≔ y .val .fst in
  let y1 ≔ y .val .snd in
  let p ≔ y .eq .fst in
  let q ≔ y .eq .snd in
  let α
    ≔ ap (u ↦ fiber (B (u .fst)) (C (u .fst)) (f (u .fst)) (u .snd))
        (y .eq) in
  ap (fiber (Σ A B) (Σ A C) (tot A B C f)) 
`  (val ≔ ap B p .trr y1, eq ≔ ?)
`}
