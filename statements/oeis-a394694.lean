import Mathlib

/-!
# A394694: Number of occurrences of n in triangle A081493(i,j) = i + (i-1)*(j-1).

Source: https://oeis.org/A394694
Credit: @cj-55m (agent: Claude Code, model claude-opus-5-5)

The entry (offset 1, data 1, 1, 2, 1, 2, 1, 3, 1, 2, 2, 2, 1, 4, 1, 2, 2, 3, 1, 3, 1, 4, ...)
records in its COMMENTS section (entry by Gokul Padmanabhan, Mar 29 2026):

  Conjecturally: a(n) = A000005(n-1)/2 + e(n), where e(n) = 1/2 if n-1 is a perfect square,
  1 if n-1 is pronic, and 0 otherwise.
  Here A000005(k) is the number of divisors of k.

Conventions:
* A081493 is the triangle with rows `i ≥ 1` and columns `1 ≤ j ≤ i`, entry
  `T(i,j) = i + (i-1)*(j-1)` (the formula given in A081493 and in the name of A394694).
* `a n` is the number of positions `(i, j)` with `1 ≤ j ≤ i` and `T(i,j) = n`. Since
  `T(i,j) ≥ i ≥ j`, every such position has `i ≤ n` and `j ≤ n`, so it suffices to count inside
  `[1, n] × [1, n]`.
* `A000005(k)` is `(Nat.divisors k).card`. Since `A000005(0)` is undefined, the conjecture is
  stated for `n ≥ 2`, i.e. `n - 1 ≥ 1`.
* `n - 1` is a perfect square means `IsSquare (n - 1)`; `n - 1` is pronic means
  `n - 1 = k * (k + 1)` for some natural number `k`. For `n - 1 ≥ 1` these two cases are
  mutually exclusive, so the order in which `e` tests them does not matter.
* The identity is stated in `ℚ`, since `A000005(n-1)/2` need not be an integer.
-/

namespace OMA.S_oeis_a394694

/-- The entry `T(i,j) = i + (i-1)*(j-1)` of the triangle A081493. -/
def T (i j : ℕ) : ℕ := i + (i - 1) * (j - 1)

/-- A394694: the number of positions `(i, j)` with `1 ≤ j ≤ i` in the triangle A081493 whose
entry equals `n`. -/
def a (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n ×ˢ Finset.Icc 1 n).filter fun p => p.2 ≤ p.1 ∧ T p.1 p.2 = n).card

/-- `m` is pronic: `m = k * (k + 1)` for some natural number `k`. -/
def IsPronic (m : ℕ) : Prop := ∃ k : ℕ, m = k * (k + 1)

open Classical in
/-- The correction term `e(n)`: `1/2` if `n - 1` is a perfect square, `1` if `n - 1` is pronic,
and `0` otherwise. -/
noncomputable def e (n : ℕ) : ℚ :=
  if IsSquare (n - 1) then 1 / 2 else if IsPronic (n - 1) then 1 else 0

/-- The conjecture of A394694: `a(n) = A000005(n-1)/2 + e(n)` for `n ≥ 2`. -/
theorem main : ∀ n : ℕ, 2 ≤ n →
    (a n : ℚ) = ((Nat.divisors (n - 1)).card : ℚ) / 2 + e n := by
  sorry

end OMA.S_oeis_a394694
