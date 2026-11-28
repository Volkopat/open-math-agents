import Mathlib

/-!
# The conjectures on the divisor digit-product sum A093811

M. F. Hasler's July 11, 2026 comment and formula in https://oeis.org/A093811.
The record index conventions are also specified in https://oeis.org/A397260.
The first conjunct implies that every fixed point occurs at an index at most 798.
Credit: @DhruRules
-/

namespace OMA.S_oeis_a093811

/-- Sum over all positive divisors of the products of their decimal digits. -/
def digitProductSum (n : ℕ) : ℕ :=
  ∑ d ∈ n.divisors, (Nat.digits 10 d).prod

/-- A value strictly greater than all values at earlier positive indices. -/
def recordAt (n : ℕ) : Prop :=
  0 < n ∧ ∀ m : ℕ, 0 < m → m < n → digitProductSum m < digitProductSum n

/-- Sharp eventual inequality, record indices, their two asymptotic sizes,
the vanishing linear-scale ratio, and the global normalized limit superior. -/
theorem main :
    (∀ n : ℕ, 798 < n → digitProductSum n < n) ∧
    (∀ k : ℕ, 1 ≤ k → recordAt (10 ^ k - 4)) ∧
    (∀ k : ℕ, 4 < k → recordAt (10 ^ k - 2)) ∧
    Filter.Tendsto (fun k : ℕ => (digitProductSum (10 ^ k - 4) : ℝ) / (9 : ℝ) ^ k)
      Filter.atTop (nhds (94 / 81 : ℝ)) ∧
    Filter.Tendsto (fun k : ℕ => (digitProductSum (10 ^ k - 2) : ℝ) / (9 : ℝ) ^ k)
      Filter.atTop (nhds (4 / 3 : ℝ)) ∧
    Filter.Tendsto (fun n : ℕ => (digitProductSum n : ℝ) / n)
      Filter.atTop (nhds 0) ∧
    Filter.limsup (fun n : ℕ => (digitProductSum n : ℝ) / (9 : ℝ) ^ (Real.logb 10 n))
      Filter.atTop = (4 / 3 : ℝ) := by
  sorry

end OMA.S_oeis_a093811
