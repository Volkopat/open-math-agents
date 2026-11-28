import OMAStatements.S_oeis_a034917
import Mathlib

open OMA.S_oeis_a034917 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a034917.main) := by
  intro h
  let M : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 1, 0]
  have hM : Adm 2 M := by
    constructor
    · intro i j
      fin_cases i <;> fin_cases j <;> decide
    · intro i j
      fin_cases i <;> fin_cases j <;> decide
  have hdet : M.det = -1 := by
    rw [Matrix.det_fin_two]
    decide
  let S : Set ℤ := {d | ∃ N, Adm 2 N ∧ N.det = d}
  have hmem : (-1 : ℤ) ∈ S := ⟨M, hM, hdet⟩
  have hlower : ∀ d ∈ S, (-1 : ℤ) ≤ d := by
    rintro d ⟨N, hN, rfl⟩
    have hdiag : N 0 0 = N 1 1 := hN.1 0 0
    rw [Matrix.det_fin_two, ← hdiag]
    have hoff : N 0 1 * N 1 0 ≤ 1 := by
      rcases hN.2 0 1 with h1 | h1 | h1 <;>
        rcases hN.2 1 0 with h2 | h2 | h2 <;> rw [h1, h2] <;> decide
    nlinarith [sq_nonneg (N 0 0)]
  have hinf : sInf S = -1 :=
    le_antisymm (csInf_le ⟨-1, hlower⟩ hmem) (le_csInf ⟨-1, hmem⟩ hlower)
  have heq : M.det = -a 2 := by
    change M.det = -(-sInf S)
    rw [hdet, hinf, neg_neg]
  exact h.1 2 (by decide) M hM heq 0 0 (by decide)