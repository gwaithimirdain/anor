{` -*- narya-prog-args: ("-proofgeneral" "-hott") -*- `}

import "integers"

def ℚ : Type ≔ data [
| in_int. (_ : ℤ)
| mediant. (a b : ℚ) (_ : adjacent_ℚ a b) ]

and adjacent_ℚ : (_ _ : ℚ) → Type ≔ data [
| int_adjacent. (a : ℤ) : adjacent_ℚ (in_int. a) (in_int. (suc_ℤ a))
| l_mediant. (p q : ℚ) (r : adjacent_ℚ p q) : adjacent_ℚ p (mediant. p q r)
| r_mediant. (p q : ℚ) (r : adjacent_ℚ p q) : adjacent_ℚ (mediant. p q r) q ]

def numerator_ℚ (q : ℚ) : ℤ ≔ match q [
| in_int. a ↦ a
| mediant. p q r ↦ add_ℤ (numerator_ℚ p) (numerator_ℚ q)]

def denominator_ℚ (q : ℚ) : ℤ ≔ match q [
| in_int. a ↦ one_ℤ
| mediant. p q r ↦ add_ℤ (denominator_ℚ p) (denominator_ℚ q)]

def suc_ℚ (q : ℚ) : ℚ ≔ match q [
| in_int. a ↦ in_int. (suc_ℤ a)
| mediant. p q r ↦ mediant. (suc_ℚ p) (suc_ℚ q) (suc_adjacent_ℚ p q r)]

and suc_adjacent_ℚ (p q : ℚ) (r : adjacent_ℚ p q)
  : adjacent_ℚ (suc_ℚ p) (suc_ℚ q)
  ≔ match r [
| int_adjacent. a ↦ int_adjacent. (suc_ℤ a)
| l_mediant. p q r ↦ l_mediant. (suc_ℚ p) (suc_ℚ q) (suc_adjacent_ℚ p q r)
| r_mediant. p q r ↦ r_mediant. (suc_ℚ p) (suc_ℚ q) (suc_adjacent_ℚ p q r)]
