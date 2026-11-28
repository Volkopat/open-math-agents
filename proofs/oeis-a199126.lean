import OMAStatements.S_oeis_a199126

-- Problem: A199126: Number of nX1 0..2 arrays with values 0..2 introduced in row major order, the number of instances of each value within one of each other, and no element equal to any horizontal or vertical neighbor.
-- Upstream: formal-conjectures statements/oeis-a199126.lean:0 (declaration OMA.S_oeis_a199126.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: for a word of length 3n the numbers of instances c0, c1, c2 of the three values add
-- up to 3n (count the positions by their value). If they are pairwise within one of each other,
-- they are all equal to n (otherwise the sum would be 3m + 1 or 3m + 2); conversely all equal to n
-- are within one. So the two filters select the same words and the two counts agree.

namespace R09A199126

open OMA.S_oeis_a199126

theorem fin3_cases : ∀ v : Fin 3, v = 0 ∨ v = 1 ∨ v = 2 := by
  decide

theorem numOcc_sum (n : ℕ) (w : Fin (3 * n) → Fin 3) :
    numOcc w 0 + numOcc w 1 + numOcc w 2 = 3 * n := by
  have h := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin (3 * n))))
    (t := (Finset.univ : Finset (Fin 3))) (f := w)
    (by intro x _; exact Finset.mem_coe.mpr (Finset.mem_univ (w x)))
  rw [Fin.sum_univ_three, Finset.card_univ, Fintype.card_fin] at h
  exact h.symm

theorem main_eq (n : ℕ) : a (3 * n) = A190917 n := by
  unfold a A190917
  congr 1
  apply Finset.filter_congr
  intro w _
  have hs := numOcc_sum n w
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, h1, h3⟩
    have _a01 := h2 0 1
    have _a10 := h2 1 0
    have _a02 := h2 0 2
    have _a20 := h2 2 0
    have _a12 := h2 1 2
    have _a21 := h2 2 1
    intro v
    rcases fin3_cases v with rfl | rfl | rfl
    · omega
    · omega
    · omega
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h2, ?_, h3⟩
    intro u v
    have hu := h1 u
    have hv := h1 v
    omega

end R09A199126

open OMA.S_oeis_a199126 R09A199126 in
theorem OMA.solution : type_of% @OMA.S_oeis_a199126.main := by
  intro n _
  exact main_eq n
