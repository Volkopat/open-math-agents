import Mathlib

/-!
# A180291: Number of arrangements of n indistinguishable balls in n boxes with the maximum number of balls in any box equal to n-1.

Source: https://oeis.org/A180291
Credit: @agchua

Bruce J. Nicholson (Apr 05 2017), in the comments of A180291:
  Conjecture: For n > 2, a(n) = 2*A000217(n+1).
Luca Ferrigno (Jul 13 2023), in the next comment of the entry, proves a(n) = n*(n-1) for n > 2
(choose the box with n-1 balls, then the box of the last ball) and records the conjecture and
the empirical formulas as correct.

A180291 has offset 2. An arrangement of n indistinguishable balls in n boxes is a function
f : Fin n → ℕ with Sum_i f i = n; `Finset.Nat.antidiagonalTuple n n` is the finset of these.
Following Gus Wiseman's clarification in the entry, the heaviest box holds exactly n - 1 balls:
every f i is at most n - 1 and some f i equals n - 1. A000217 (offset 0) is the triangular
numbers m*(m+1)/2. As printed, 2*A000217(n+1) = (n+1)*(n+2) is not a(3) = 6; the listed data
(6, 12, 20, 30, ...) and Ferrigno's proof give a(n) = n*(n-1) = 2*A000217(n-1) for n > 2. The
entry records the conjecture as proved in this form, which is the form stated here.
-/

namespace OMA.S_oeis_a180291

/-- A180291(n): arrangements of n balls in n boxes whose heaviest box holds exactly n - 1 balls. -/
noncomputable def a (n : ℕ) : ℕ :=
  ((Finset.Nat.antidiagonalTuple n n).filter
    (fun f : Fin n → ℕ => (∀ i, f i ≤ n - 1) ∧ ∃ i, f i = n - 1)).card

/-- A000217(m) = m*(m+1)/2, the triangular numbers. -/
def A000217 (m : ℕ) : ℕ := m * (m + 1) / 2

/-- Nicholson's conjecture in the form proved by Ferrigno: a(n) = n*(n-1) = 2*A000217(n-1)
for n > 2. -/
theorem main : ∀ n : ℕ, 2 < n → a n = n * (n - 1) ∧ a n = 2 * A000217 (n - 1) := by
  sorry

end OMA.S_oeis_a180291
