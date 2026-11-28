import Mathlib

/-!
# Prime values of polynomials with squarefree coefficients

Zhi-Wei Sun's conjecture of March 26, 2013, in OEIS A005117.
Source: https://oeis.org/A005117 (OEIS Foundation, CC BY-SA 4.0).
-/

namespace OMA.S_oeis_a005117

/-- The squarefree numbers in increasing order, indexed from zero: 1, 2, 3, 5, ... -/
noncomputable def coeff (i : ℕ) : ℕ :=
  Nat.nth (fun m : ℕ => 0 < m ∧ Squarefree m) i

/-- Bases strictly above the last coefficient at which the polynomial is prime. -/
def primeBases (n : ℕ) : Set ℕ :=
  {b | coeff (n - 1) < b ∧ Nat.Prime (∑ i ∈ Finset.range n, coeff i * b ^ i)}

/-- For each length at least two, infinitely many bases qualify, including one
at most the stated bound. Existence within the bound is equivalent to the
same upper bound on the least qualifying base. -/
theorem main : ∀ n : ℕ, 2 ≤ n →
    (primeBases n).Infinite ∧ ∃ b ∈ primeBases n, b ≤ (n + 3) * (n + 4) := by
  sorry

end OMA.S_oeis_a005117
