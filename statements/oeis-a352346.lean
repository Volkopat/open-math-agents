import Mathlib

/-!
# OEIS A352346: Common terms between A061078 and A061077.

Source: https://oeis.org/A352346
Credit: @unserus

OEIS: "Smarandache's conjecture: there are infinitely many terms."
A061078(n) is the sum of the products of the decimal digits of the first `n` positive even
numbers `2, 4, ..., 2n`; A061077(n) is the same sum over the first `n` odd numbers
`1, 3, ..., 2n - 1` (both for `n ≥ 1`). A352346 lists the values taken by both sequences
(first term `26 = A061077(6) = A061078(7)`).
-/

namespace OMA.S_oeis_a352346

/-- The product of the decimal digits of `m`. -/
def digitProd (m : ℕ) : ℕ := (Nat.digits 10 m).prod

/-- A061078: `∑_{k=1}^{n} digitProd(2k)`. -/
def a061078 (n : ℕ) : ℕ := ∑ k ∈ Finset.Icc 1 n, digitProd (2 * k)

/-- A061077: `∑_{k=1}^{n} digitProd(2k - 1)`. -/
def a061077 (n : ℕ) : ℕ := ∑ k ∈ Finset.Icc 1 n, digitProd (2 * k - 1)

/-- The terms of A352346: values of both A061078 and A061077 (at indices `≥ 1`). -/
def a352346Set : Set ℕ :=
  {v : ℕ | (∃ n : ℕ, 1 ≤ n ∧ a061078 n = v) ∧ (∃ m : ℕ, 1 ≤ m ∧ a061077 m = v)}

/-- A352346 is infinite. -/
theorem main : a352346Set.Infinite := by
  sorry

end OMA.S_oeis_a352346
