{` -*- narya-prog-args: ("-proofgeneral" "-hott") -*- `}

def transport (A : Type) (B : A → Type) (x y : A) (p : Id A x y)
  : B x → B y
  ≔ refl B p .trr.1

def refl_transport_1 (A : Type) (B : A → Type) (x₀₀ x₀₁ : A)
  (x₀₂ : Id A x₀₀ x₀₁) (x₁₀ x₁₁ : A) (x₁₂ : Id A x₁₀ x₁₁)
  (x₂₀ : Id A x₀₀ x₁₀) (x₂₁ : Id A x₀₁ x₁₁)
  (x₂₂ : Id (Id A) x₀₂ x₁₂ x₂₀ x₂₁) (y₀ : B x₀₀) (y₁ : B x₀₁)
  (y₂ : Id B x₀₂ y₀ y₁)
  : Id B x₁₂ (transport A B x₀₀ x₁₀ x₂₀ y₀) (transport A B x₀₁ x₁₁ x₂₁ y₁)
  ≔ Id (Id B) x₂₂ .trr.1 y₂

def refl_transport_2 (A : Type) (B : A → Type) (x₀₀ x₀₁ : A)
  (x₀₂ : Id A x₀₀ x₀₁) (x₁₀ x₁₁ : A) (x₁₂ : Id A x₁₀ x₁₁)
  (x₂₀ : Id A x₀₀ x₁₀) (x₂₁ : Id A x₀₁ x₁₁)
  (x₂₂ : Id (Id A) x₀₂ x₁₂ x₂₀ x₂₁) (y₀ : B x₀₀) (y₁ : B x₁₀)
  (y₂ : Id B x₂₀ y₀ y₁)
  : Id B x₂₁ (transport A B x₀₀ x₀₁ x₀₂ y₀) (transport A B x₁₀ x₁₁ x₁₂ y₁)
  ≔ Id (Id B) x₂₂ .trr.2 y₂

def transport2 (A : Type) (B : A → Type) (x y : A) (p q : Id A x y)
  (r : Id (Id A x y) p q) (b : B x)
  : Id (B y) (transport A B x y p b) (transport A B x y q b)
  ≔ sym (B⁽ᵉᵉ⁾ r) (refl B p .liftr.1 b) (refl B q .liftr.1 b)
      .trr.1 (refl b)

