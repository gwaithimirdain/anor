{` -*- narya-prog-args: ("-proofgeneral" "-hott") -*- `}

import "groupoid-operations-on-identifications"

def ℕ : Type ≔ data [ zero. | suc. (_ : ℕ) ]

def iterate (A : Type) (f : A → A) (n : ℕ) (a : A) : A ≔ match n [
| zero. ↦ a
| suc. n ↦ f (iterate A f n a)]

def add_ℕ (m n : ℕ) : ℕ ≔ iterate ℕ suc. n m

def add_zero_ℕ (n : ℕ) : Id ℕ (add_ℕ n zero.) n ≔ refl n

def zero_add_ℕ (n : ℕ) : Id ℕ (add_ℕ zero. n) n ≔ match n [
| zero. ↦ refl zero.
| suc. x ↦ ap (y ↦ suc. y) (zero_add_ℕ x)]

def mul_ℕ (m n : ℕ) : ℕ ≔ iterate ℕ (x ↦ add_ℕ m x) n zero.

def zero_mul_ℕ (n : ℕ) : Id ℕ (mul_ℕ zero. n) zero. ≔ match n [
| zero. ↦ refl zero.
| suc. n ↦
    concat ℕ (mul_ℕ zero. (suc. n)) (mul_ℕ zero. n) zero.
      (zero_add_ℕ (mul_ℕ zero. n)) (zero_mul_ℕ n)]

def mul_zero_ℕ (n : ℕ) : Id ℕ (mul_ℕ n zero.) zero. ≔ refl zero.
