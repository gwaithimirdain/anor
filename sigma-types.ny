{` -*- narya-prog-args: ("-proofgeneral" "-hott") -*- `}

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
