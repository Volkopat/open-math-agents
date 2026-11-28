import Mathlib

namespace OMA.S_oeis_a392338

/-- The `n × n` circulant integer matrix whose first row is given by a permutation `σ`
of `{0, 1, ..., n - 1}`, i.e., entry `(i, j)` is `σ((j - i) mod n)`. -/
def circulantMatrix (n : ℕ) (σ : Equiv.Perm (Fin n)) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j => ((σ ⟨(j.val + n - i.val) % n, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩).val : ℤ)

/-- OEIS A392338: the minimum absolute value of the determinant of a nonsingular
`n × n` circulant matrix whose rows are permutations of `[0, 1, ..., n - 1]`. -/
noncomputable def a392338 (n : ℕ) : ℕ :=
  sInf { d : ℕ | ∃ σ : Equiv.Perm (Fin n),
    (circulantMatrix n σ).det ≠ 0 ∧ (circulantMatrix n σ).det.natAbs = d }

/-- OEIS A084367: `a(m) = m * (2 * m + 1)^2`. -/
def a084367 (m : ℕ) : ℕ := m * (2 * m + 1) ^ 2

/-- Conjecture in OEIS A392338: for every odd `n = 2 * m + 1` with `m ≥ 1`,
`A392338(2 * m + 1) = A084367(m) = m * (2 * m + 1)^2`. -/
theorem main : ∀ m : ℕ, 1 ≤ m → a392338 (2 * m + 1) = a084367 m := by sorry

end OMA.S_oeis_a392338
