import Mathlib

/-!
# A283751: least b > 1 such that n, written in base b and read in base b^2, is a multiple of n

Source: https://oeis.org/A283751
Credit: @xor2k

Formalizes the OEIS A283751 conjecture (offset 0):
Conjecture: if n is composite, then a(n) < n.

Conventions:
* `a n` is the least `b > 1` such that `n` divides `Nat.ofDigits (b ^ 2) (Nat.digits b n)`, i.e. the
  base-`b` digits of `n` (Mathlib `Nat.digits`, least significant first) evaluated in base `b ^ 2`.
  It is defined as `sInf` of the set of such `b`; this matches the OEIS data for all listed terms
  (for `n = 0` the digit list is empty, the value is `0`, and `a 0 = 2`).
* `n` composite means `1 < n` and `n` is not prime.
-/

namespace OMA.S_oeis_a283751

/-- Least `b > 1` such that `n` written in base `b` and read in base `b ^ 2` is a multiple of `n`. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {b : ℕ | 1 < b ∧ n ∣ Nat.ofDigits (b ^ 2) (Nat.digits b n)}

/-- For every composite `n`, `a n < n`. -/
theorem main :
    ∀ n : ℕ, 1 < n → ¬ n.Prime → a n < n := by
  sorry

end OMA.S_oeis_a283751
