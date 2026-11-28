import Mathlib

/-!
# A202277: Numbers m such that number of integers k such sigma(k) <= m (A074753) is equal to number of integers k <= m such that sigma(x) = k has no solution (A202276).

Source: https://oeis.org/A202277
Credit: @luciusacarr

Data: 2, 537, 639, 647, 653, 655, 657, 661, 663, 672, 674, 684, 686.

Conjecture (from the entry): the sequence is finite with 13 terms. `main` states it.

Reading of the source:
* The integers `k` and `x` are positive (sigma is defined on the positive integers), and `m`
  ranges over the positive integers (offset 1).
* The first count is the number of positive `k` with `sigma(k) ≤ m`, as the name says (the
  linked A074753 uses `<`, but the data of this entry match `≤`: with `<` the terms would start
  1, 2, 3, 537, 639, 640, ...). Since `sigma(k) ≥ k`, such `k` satisfy `k ≤ m`.
* The second count is the number of `k` with `1 ≤ k ≤ m` such that no positive `x` has
  `sigma(x) = k`.
* With this reading the terms below 3000 are exactly the thirteen listed (checked numerically),
  so "finite with 13 terms" is stated as the equality of the set of terms with the listed set.
-/

namespace OMA.S_oeis_a202277

/-- The number of positive integers `k` with `sigma(k) ≤ m`. -/
def countSigmaLe (m : ℕ) : ℕ :=
  ((Finset.Icc 1 m).filter (fun k => ArithmeticFunction.sigma 1 k ≤ m)).card

/-- The number of integers `1 ≤ k ≤ m` that are not of the form `sigma(x)` with `x` positive. -/
noncomputable def countNonSigma (m : ℕ) : ℕ :=
  open Classical in
  ((Finset.Icc 1 m).filter (fun k => ¬ ∃ x : ℕ, 0 < x ∧ ArithmeticFunction.sigma 1 x = k)).card

/-- The terms of A202277. -/
def S : Set ℕ := {m | 0 < m ∧ countSigmaLe m = countNonSigma m}

theorem main :
    -- The sequence is finite with 13 terms (the ones listed).
    S = {2, 537, 639, 647, 653, 655, 657, 661, 663, 672, 674, 684, 686} := by
  sorry

end OMA.S_oeis_a202277
