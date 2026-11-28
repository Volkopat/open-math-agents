import Mathlib.Data.Finset.Card
import Mathlib.Order.Lattice.Nat

namespace OMA.S_oeis_a328151

/-- Number of ordered pairs `(x, y)` of positive integers with `x^2 + y^2 = m` (OEIS A063725). -/
def numOrderedPosSumTwoSq (m : ℕ) : ℕ :=
  ((Finset.Icc 1 m ×ˢ Finset.Icc 1 m).filter (fun p => p.1 ^ 2 + p.2 ^ 2 = m)).card

/-- Number of unordered representations of `m` as a sum of two distinct positive squares,
counted via pairs `(x, y)` with `1 ≤ x < y` and `x^2 + y^2 = m`. -/
def numDistinctPosSumTwoSq (m : ℕ) : ℕ :=
  ((Finset.Icc 1 m ×ˢ Finset.Icc 1 m).filter (fun p => p.1 < p.2 ∧ p.1 ^ 2 + p.2 ^ 2 = m)).card

/-- OEIS A328151(n): Smallest nonnegative integer `m` such that there are exactly `n` ordered
pairs `(x, y)` of positive integers with `x^2 + y^2 = m`. -/
noncomputable def A328151 (n : ℕ) : ℕ :=
  sInf { m : ℕ | numOrderedPosSumTwoSq m = n }

/-- OEIS A093195(k): Least positive integer which is the sum of two distinct nonzero squares
in exactly `k` ways. -/
noncomputable def A093195 (k : ℕ) : ℕ :=
  sInf { m : ℕ | 1 ≤ m ∧ numDistinctPosSumTwoSq m = k }

/-- OEIS A006339(k): Least positive integer `c` which is the hypotenuse of exactly `k`
distinct integer Pythagorean triangles `(a, b, c)` with `0 < a < b` and `a^2 + b^2 = c^2`. -/
noncomputable def A006339 (k : ℕ) : ℕ :=
  sInf { c : ℕ | 1 ≤ c ∧ numDistinctPosSumTwoSq (c ^ 2) = k }

/-- Conjecture (Jon E. Schoenfield, Jan 23 2022; OEIS A328151):
For all `k ≥ 1`, `A328151(2k) = A093195(k)`, and for all `k ≥ 0`,
`A328151(2k + 1) = 2 * A006339(k)^2`. -/
theorem main :
    (∀ k : ℕ, 1 ≤ k → A328151 (2 * k) = A093195 k) ∧
    (∀ k : ℕ, A328151 (2 * k + 1) = 2 * (A006339 k) ^ 2) := by
  sorry

end OMA.S_oeis_a328151
