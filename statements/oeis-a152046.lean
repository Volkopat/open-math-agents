import Mathlib

/-!
# A152046: a(n) = Product_{k=1..floor((n-1)/2)} (1 + 8*cos(k*Pi/n)^2) for n >= 0.

Source: https://oeis.org/A152046
Credit: @rickmanelius

Conjecture (R. J. Mathar, Nov 27 2008): Apparently the same as A001045 after the first term.
(Peter Luschny, Nov 28 2019: This conjecture is true.)

Formalization notes:
* Offset 0. `a n` is the product over k in `Finset.Icc 1 ((n - 1) / 2)` of 1 + 8 cos(kπ/n)^2,
  computed in the reals with `Real.cos` and `Real.pi`. For n ≥ 1 the natural-number value
  (n - 1) / 2 is exactly floor((n-1)/2). For n = 0 the upper limit of the entry is
  floor(-1/2) = -1 and the natural-number value is 0; both give the empty product, so a(0) = 1,
  as in the data. The data begin 1, 1, 1, 3, 5, 11, 21, 43, 85, ..., matching the entry.
* A001045 is the Jacobsthal sequence, which Mathlib does not have. It is defined as in the name
  of A001045: J(0) = 0, J(1) = 1 and J(n) = J(n-1) + 2*J(n-2) (data 0, 1, 1, 3, 5, 11, 21, ...).
* Both entries have offset 0, so the same as A001045 after the first term means a(n) = J(n) for
  every n ≥ 1 (the first terms differ: a(0) = 1 while J(0) = 0).
-/

namespace OMA.S_oeis_a152046

/-- a(n) = Product_{k=1..floor((n-1)/2)} (1 + 8*cos(k*Pi/n)^2), in the reals. -/
noncomputable def a (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.Icc 1 ((n - 1) / 2), (1 + 8 * Real.cos ((k : ℝ) * Real.pi / (n : ℝ)) ^ 2)

/-- A001045, the Jacobsthal numbers: J(0) = 0, J(1) = 1, J(n) = J(n-1) + 2*J(n-2). -/
def jacobsthal : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | (n + 2) => jacobsthal (n + 1) + 2 * jacobsthal n

/-- Mathar's conjecture: a(n) agrees with A001045 for every n ≥ 1. -/
theorem main : ∀ n : ℕ, 1 ≤ n → a n = jacobsthal n := by
  sorry

end OMA.S_oeis_a152046
