{` -*- narya-prog-args: ("-proofgeneral" "-hott") -*- `}

import "natural-numbers"
import "product-types"

def ℤ : Type ≔ sig (
  nonneg : ℕ,
  nonpos : ℕ,
  isint : Id ℕ (mul_ℕ nonneg nonpos) zero. )

def zero_ℤ : ℤ ≔ (zero., zero., refl zero.)

def suc_ℤ (x : ℤ) : ℤ ≔ match (x .nonpos) [
| zero. ↦ (suc. (x .nonneg), zero., refl zero.)
| suc. y ↦ (zero., y, zero_mul_ℕ y)]

def one_ℤ : ℤ ≔ suc_ℤ zero_ℤ

def pred_ℤ (x : ℤ) : ℤ ≔ match (x .nonneg) [
| zero. ↦ (zero., suc. (x .nonpos), zero_mul_ℕ (suc. (x .nonpos)))
| suc. y ↦ (y, zero., refl zero.)]

def int_pair_ℕ (x : ℕ × ℕ) : ℤ ≔ match (x .pr1) [
| zero. ↦ (zero., x .pr2, zero_mul_ℕ (x .pr2))
| suc. y ↦ match (x .pr2) [
  | zero. ↦ (suc. y, zero., mul_zero_ℕ (suc. y))
  | suc. z ↦ int_pair_ℕ (y, z)]]

def add_ℤ (x y : ℤ) : ℤ
  ≔ int_pair_ℕ
      (add_ℕ (x .nonneg) (y .nonneg), add_ℕ (x .nonpos) (y .nonpos))

notation(1) x "＋ℤ" y ≔ add_ℤ x y
