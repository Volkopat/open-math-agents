import Mathlib

/-! Source: https://mathoverflow.net/questions/120980 -/

namespace OMA.S_mo_120980

/-- Two matrices can generate the full complex matrix algebra even when
every linear combination has minimal-polynomial degree below n. -/
theorem main : ∃ (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℂ), 2 ≤ n ∧
    Algebra.adjoin ℂ ({A, B} : Set (Matrix (Fin n) (Fin n) ℂ)) = ⊤ ∧
    ∀ α β : ℂ, (minpoly ℂ (α • A + β • B)).natDegree ≤ n - 1 := by
  sorry

end OMA.S_mo_120980
