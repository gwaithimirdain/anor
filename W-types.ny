{` -*- narya-prog-args: ("-proofgeneral" "-hott") -*- `}


def 𝕎 (A : Type) (B : A → Type) : Type ≔ data [
| tree. (a : A) (f : B a → 𝕎 A B) ]

def shape𝕎 (A : Type) (B : A → Type) (x : 𝕎 A B) : A ≔ match x [
| tree. a _ ↦ a]

def component𝕎 (A : Type) (B : A → Type) (x : 𝕎 A B)
  : B (shape𝕎 A B x) → 𝕎 A B
  ≔ match x [ tree. _ f ↦ f ]

def η𝕎 (A : Type) (B : A → Type) (x : 𝕎 A B)
  : Id (𝕎 A B) (tree. (shape𝕎 A B x) (component𝕎 A B x)) x
  ≔ match x [ tree. _ _ ↦ refl x ] 

