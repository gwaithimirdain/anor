{` -*- narya-prog-args: ("-proofgeneral" "-hott") -*- `}

import "groupoid-operations-on-identifications"
import "squares-of-identifications"

{` Concatenation of squares of identifications takes two squares sharing a horizontal edge and returns a single square:

        p₂₀₂₁
   x₂₀ ------> x₂₁
    ∧          ∧
    |          |              x₂₀ -----> x₂₁
    |   p₁₀₁₁  |               ∧          ∧
   x₁₀ ------> x₁₁   =====>    |          |
    ∧          ∧               |          |
    |          |              x₀₀ -----> x₀₁.
    |          |
   x₀₀ ------> x₀₁
        p₀₀₀₁

  This new square fits in a commuting cube. This square is defined by ap (concat A).

`}

def vertical_concat_Sq (A : Type) (x₀₀ x₀₁ x₁₀ x₁₁ x₂₀ x₂₁ : A)
  (p₀₀₀₁ : Id A x₀₀ x₀₁) (p₁₀₁₁ : Id A x₁₀ x₁₁) (p₂₀₂₁ : Id A x₂₀ x₂₁)
  (p₀₀₁₀ : Id A x₀₀ x₁₀) (p₁₀₂₀ : Id A x₁₀ x₂₀) (p₀₁₁₁ : Id A x₀₁ x₁₁)
  (p₁₁₂₁ : Id A x₁₁ x₂₁) (r : Sq A x₀₀ x₀₁ p₀₀₀₁ x₁₀ x₁₁ p₁₀₁₁ p₀₀₁₀ p₀₁₁₁)
  (s : Sq A x₁₀ x₁₁ p₁₀₁₁ x₂₀ x₂₁ p₂₀₂₁ p₁₀₂₀ p₁₁₂₁)
  : Sq A x₀₀ x₀₁ p₀₀₀₁ x₂₀ x₂₁ p₂₀₂₁ (concat A x₀₀ x₁₀ x₂₀ p₀₀₁₀ p₁₀₂₀)
      (concat A x₀₁ x₁₁ x₂₁ p₀₁₁₁ p₁₁₂₁)
  ≔ ap (concat A) p₀₀₀₁ p₁₀₁₁ p₂₀₂₁ r s

def horizontal_concat_Sq (A : Type) (x₀₀ x₀₁ x₀₂ x₁₀ x₁₁ x₁₂ : A)
  (p₀₀₀₁ : Id A x₀₀ x₀₁) (p₀₁₀₂ : Id A x₀₁ x₀₂) (p₁₀₁₁ : Id A x₁₀ x₁₁)
  (p₁₁₁₂ : Id A x₁₁ x₁₂) (p₀₀₁₀ : Id A x₀₀ x₁₀) (p₀₁₁₁ : Id A x₀₁ x₁₁)
  (p₀₂₁₂ : Id A x₀₂ x₁₂) (r : Sq A x₀₀ x₀₁ p₀₀₀₁ x₁₀ x₁₁ p₁₀₁₁ p₀₀₁₀ p₀₁₁₁)
  (s : Sq A x₀₁ x₀₂ p₀₁₀₂ x₁₁ x₁₂ p₁₁₁₂ p₀₁₁₁ p₀₂₁₂)
  : Sq A x₀₀ x₀₂ (concat A x₀₀ x₀₁ x₀₂ p₀₀₀₁ p₀₁₀₂) x₁₀ x₁₂
      (concat A x₁₀ x₁₁ x₁₂ p₁₀₁₁ p₁₁₁₂) p₀₀₁₀ p₀₂₁₂
  ≔ sym
      (vertical_concat_Sq A x₀₀ x₁₀ x₀₁ x₁₁ x₀₂ x₁₂ p₀₀₁₀ p₀₁₁₁ p₀₂₁₂ p₀₀₀₁
         p₀₁₀₂ p₁₀₁₁ p₁₁₁₂ (sym r) (sym s))
