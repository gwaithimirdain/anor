{` -*- narya-prog-args: ("-proofgeneral" "-hott") -*- `}

import "squares-of-identifications"

{`
Consider a type family B over A and an identification p : x₀ ＝ x₁ in A. For y₀ : B x₀ and y₁ : B x₁ we define the type of dependent identifications over p in one of several equivalent ways:
- The type refl B p y₀ y₁, or the definitionally equal type Id B p y₀ y₁. The element refl B is of type {x₀ x₁ : A} (p : Id A x₀ x₁) → Id Type (B x₀) (B x₁). Thus, for each y₀ : B x₀ and y₁ : B x₁ we have a type refl B p y₀ y₁, which is the natural definition of the type of identifications over p from y₀ to y₁.
- The type Id (B x₁) (ap B p .trr y₀) y₁. This type is a more explicit implementation of the type of identifications over p from y₀ to y₁. Although it is conceptually clear that it is the right type, the previous definition is a more primitive implementation of the same type.
 `}

def dependent_Id (A : Type) (B : A → Type) (x₀ x₁ : A) (p : Id A x₀ x₁)
  (y₀ : B x₀) (y₁ : B x₁)
  : Type
  ≔ Id B p y₀ y₁

{` The definition of identifications over an identifications also works for binary dependent identifications over double identifications in a binary family of types. Consider C : (x : A) → B x → Type, we define
`}

def binary_dependent_Id (A : Type) (B : A → Type)
  (C : (x : A) → B x → Type) (x₀ x₁ : A) (p : Id A x₀ x₁) (y₀ : B x₀)
  (y₁ : B x₁) (q : Id B p y₀ y₁) (z₀ : C x₀ y₀) (z₁ : C x₁ y₁)
  : Type
  ≔ Id C p q z₀ z₁

{` Given the definition of binary dependent identifications over double identifications in a family of types, we now analyze the binary dependent identifications of the identity type itself.

binary_dependent_Id A (_ ↦ A) (x y ↦ Id A x y) (x₀₀ x₀₁ : A) (p : Id A x₀₀ x₀₁) (x₁₀ x₁₁ : A) (q : Id A x₁₀ x₁₁) (r : Id A x₀₀ x₁₀) (s : Id A x₀₁ x₁₁) : Type

This ought to be the type of squares.
`}
