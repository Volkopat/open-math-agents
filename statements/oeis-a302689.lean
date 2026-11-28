import Mathlib

/-!
# A302689: a(n) = 4 + 2^n - 4*n.

Source: https://oeis.org/A302689
Credit: @agchua

Formula line of A302689 (the entry is by Eric W. Weisstein, Apr 11 2018):
  a(n) = A258547(n-5) for n > 5 (conjectured).
A302689 has offset 1, and the claim is stated as written, for every n > 5. The values of
4 + 2^n - 4*n are integers, so a(n) is computed in ℤ.
A258547 (offset 1, by R. H. Hardin) is the number of (n+1)X(1+1) 0..1 arrays with every 2X2
subblock ne-sw antidiagonal difference nondecreasing horizontally and nw+se diagonal sum
nondecreasing vertically. `hardin n m` counts the (n+1)X(m+1) arrays x of 0..1 with these two
properties. For the subblock with top left corner (i, j), i < n, j < m, the ne-sw antidiagonal
difference is x(i, j+1) - x(i+1, j) and the nw+se diagonal sum is x(i, j) + x(i+1, j+1).
Nondecreasing horizontally means that the difference does not decrease from the subblock at
(i, j) to the subblock at (i, j+1); nondecreasing vertically means that the sum does not
decrease from the subblock at (i, j) to the subblock at (i+1, j). A258547(n) is `hardin n 1`.
This reproduces the listed terms of A258547 (checked for n = 1..9), and with two rows it also
reproduces them as row 1 of A258554 (checked for m = 1..7).
-/

namespace OMA.S_oeis_a302689

/-- A302689(n) = 4 + 2^n - 4n. -/
def a (n : ℕ) : ℤ := 4 + 2 ^ n - 4 * n

/-- The entry of the array x in row i and column j, as an integer (0 outside the array). -/
def entry {n m : ℕ} (x : Fin (n + 1) → Fin (m + 1) → Fin 2) (i j : ℕ) : ℤ :=
  if h : i < n + 1 ∧ j < m + 1 then ((x ⟨i, h.1⟩ ⟨j, h.2⟩ : ℕ) : ℤ) else 0

/-- The two conditions of A258547 on an (n+1)X(m+1) array of 0..1. -/
abbrev Good {n m : ℕ} (x : Fin (n + 1) → Fin (m + 1) → Fin 2) : Prop :=
  (∀ i ∈ Finset.range n, ∀ j ∈ Finset.range (m - 1),
      entry x i (j + 1) - entry x (i + 1) j ≤ entry x i (j + 2) - entry x (i + 1) (j + 1)) ∧
    (∀ i ∈ Finset.range (n - 1), ∀ j ∈ Finset.range m,
      entry x i j + entry x (i + 1) (j + 1) ≤ entry x (i + 1) j + entry x (i + 2) (j + 1))

/-- The number of (n+1)X(m+1) arrays of 0..1 with the two conditions. -/
def hardin (n m : ℕ) : ℕ :=
  (Finset.univ.filter (fun x : Fin (n + 1) → Fin (m + 1) → Fin 2 => Good x)).card

/-- A258547(n), n >= 1. -/
def A258547 (n : ℕ) : ℕ := hardin n 1

/-- The conjecture as written: a(n) = A258547(n-5) for n > 5. -/
theorem main : ∀ n : ℕ, 5 < n → a n = (A258547 (n - 5) : ℤ) := by
  sorry

end OMA.S_oeis_a302689
