import OMAStatements.S_oeis_a073923
import Mathlib

namespace OMA.S_oeis_a073923

lemma next_one : next [1] = 2 := by
  classical
  unfold next
  have h : ∃ k : ℕ, 2 ^ k ∉ [1] ∧ ([1].sum + 2 ^ k).Prime :=
    ⟨1, by simp, by norm_num⟩
  rw [dif_pos h]
  have : Nat.find h = 1 := by
    rw [Nat.find_eq_iff]
    refine ⟨⟨by simp, by norm_num⟩, ?_⟩
    intro m hm
    have : m = 0 := by omega
    subst this
    simp
  rw [this]; norm_num

lemma a_two : a 2 = 2 := by
  have : terms 2 = [1, 2] := by
    show terms 1 ++ [next (terms 1)] = _
    show [1] ++ [next [1]] = _
    rw [next_one]; rfl
  unfold a
  rw [this]; rfl

lemma flip_two : flipStep 2 = 3 := by
  classical
  unfold flipStep
  have h : ∃ k : ℕ, 2 < 2 ^^^ 2 ^ k ∧ (2 ^^^ 2 ^ k).Prime :=
    ⟨0, by decide, by decide⟩
  rw [dif_pos h]
  have : Nat.find h = 0 := by
    rw [Nat.find_eq_zero]; exact ⟨by decide, by decide⟩
  rw [this]; decide

end OMA.S_oeis_a073923

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a073923.main) := by
  intro h
  have := h 2 le_rfl
  have hb2 : OMA.S_oeis_a073923.b 2 = 3 := by
    show OMA.S_oeis_a073923.flipStep (OMA.S_oeis_a073923.b 1) = 3
    exact OMA.S_oeis_a073923.flip_two
  have hb1 : OMA.S_oeis_a073923.b 1 = 2 := rfl
  rw [OMA.S_oeis_a073923.a_two] at this
  simp only [Nat.reduceSub] at this
  rw [hb2, hb1] at this
  norm_num at this
