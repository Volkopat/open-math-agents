import OMAStatements.S_oeis_a344503
import Mathlib

namespace OMA.S_oeis_a344503

lemma cc (b c : ℕ) (h : b ≤ c) : (c.choose b : ℚ) = (c.factorial : ℚ) / ((b.factorial : ℚ) * ((c - b).factorial : ℚ)) :=
  Nat.cast_choose ℚ h

lemma c2 (m : ℕ) : (((3*m+2).choose m : ℕ) : ℚ) * ((2*m+2)*(2*m+1)) = ((3*m).choose m : ℚ) * ((3*m+2)*(3*m+1)) := by
  rw [cc m (3*m+2) (by omega), cc m (3*m) (by omega), show 3*m+2-m = 2*m+2 by omega, show 3*m-m = 2*m by omega]
  simp only [Nat.factorial_succ]
  push_cast
  have : ((3*m).factorial : ℚ) ≠ 0 := by positivity
  have : ((2*m).factorial : ℚ) ≠ 0 := by positivity
  have : (m.factorial : ℚ) ≠ 0 := by positivity
  field_simp
  ring

lemma c3 (m : ℕ) : (((3*m+3).choose (m+1) : ℕ) : ℚ) * (((m:ℚ)+1)*(2*m+2)*(2*m+1)) = ((3*m).choose m : ℚ) * ((3*m+3)*(3*m+2)*(3*m+1)) := by
  rw [cc (m+1) (3*m+3) (by omega), cc m (3*m) (by omega), show 3*m+3-(m+1) = 2*m+2 by omega, show 3*m-m = 2*m by omega]
  simp only [Nat.factorial_succ]
  push_cast
  have : ((3*m).factorial : ℚ) ≠ 0 := by positivity
  have : ((2*m).factorial : ℚ) ≠ 0 := by positivity
  have : (m.factorial : ℚ) ≠ 0 := by positivity
  field_simp
  ring

lemma c5 (m : ℕ) : (((3*m+5).choose (m+1) : ℕ) : ℚ) * (((m:ℚ)+1)*(2*m+4)*(2*m+3)*(2*m+2)*(2*m+1)) = ((3*m).choose m : ℚ) * ((3*m+5)*(3*m+4)*(3*m+3)*(3*m+2)*(3*m+1)) := by
  rw [cc (m+1) (3*m+5) (by omega), cc m (3*m) (by omega), show 3*m+5-(m+1) = 2*m+4 by omega, show 3*m-m = 2*m by omega]
  simp only [Nat.factorial_succ]
  push_cast
  have : ((3*m).factorial : ℚ) ≠ 0 := by positivity
  have : ((2*m).factorial : ℚ) ≠ 0 := by positivity
  have : (m.factorial : ℚ) ≠ 0 := by positivity
  field_simp
  ring

lemma c6 (m : ℕ) : (((3*m+6).choose (m+2) : ℕ) : ℚ) * (((m:ℚ)+2)*((m:ℚ)+1)*(2*m+4)*(2*m+3)*(2*m+2)*(2*m+1)) = ((3*m).choose m : ℚ) * ((3*m+6)*(3*m+5)*(3*m+4)*(3*m+3)*(3*m+2)*(3*m+1)) := by
  rw [cc (m+2) (3*m+6) (by omega), cc m (3*m) (by omega), show 3*m+6-(m+2) = 2*m+4 by omega, show 3*m-m = 2*m by omega]
  simp only [Nat.factorial_succ]
  push_cast
  have : ((3*m).factorial : ℚ) ≠ 0 := by positivity
  have : ((2*m).factorial : ℚ) ≠ 0 := by positivity
  have : (m.factorial : ℚ) ≠ 0 := by positivity
  field_simp
  ring

end OMA.S_oeis_a344503

theorem OMA.solution : type_of% @OMA.S_oeis_a344503.main := by
  intro a h0 h1 h2 n hn
  open OMA.S_oeis_a344503 in
  have hB : ∀ m : ℕ, ((3*m).choose m : ℚ) ≠ 0 := fun m => by
    have := Nat.choose_pos (show m ≤ 3*m by omega); positivity
  have v0 : ∀ m, a (3*m) = ((3*m).choose m : ℚ) := h0
  have v1 : ∀ m, a (3*m+1) = 0 := h1
  have v2 : ∀ m, a (3*m+2) = -((3*m+2).choose m : ℚ) := h2
  have v3 : ∀ m, a (3*m+3) = ((3*m+3).choose (m+1) : ℚ) := fun m => by
    have := h0 (m+1); rw [show 3*(m+1) = 3*m+3 by ring] at this; exact this
  have v4 : ∀ m, a (3*m+4) = 0 := fun m => by
    have := h1 (m+1); rw [show 3*(m+1)+1 = 3*m+4 by ring] at this; exact this
  have v5 : ∀ m, a (3*m+5) = -((3*m+5).choose (m+1) : ℚ) := fun m => by
    have := h2 (m+1); rw [show 3*(m+1)+2 = 3*m+5 by ring] at this; exact this
  have v6 : ∀ m, a (3*m+6) = ((3*m+6).choose (m+2) : ℚ) := fun m => by
    have := h0 (m+2); rw [show 3*(m+2) = 3*m+6 by ring] at this; exact this
  have v7 : ∀ m, a (3*m+7) = 0 := fun m => by
    have := h1 (m+2); rw [show 3*(m+2)+1 = 3*m+7 by ring] at this; exact this
  obtain ⟨m, hm⟩ : ∃ m, n = 3*m+5 ∨ n = 3*m+6 ∨ n = 3*m+7 := ⟨(n-5)/3, by omega⟩
  have x2 : ((3*m+2).choose m : ℚ) = ((3*m).choose m : ℚ) * ((3*m+2)*(3*m+1)) / ((2*m+2)*(2*m+1)) := by
    rw [eq_div_iff (by positivity)]; exact OMA.S_oeis_a344503.c2 m
  have x3 : ((3*m+3).choose (m+1) : ℚ) = ((3*m).choose m : ℚ) * ((3*m+3)*(3*m+2)*(3*m+1)) / (((m:ℚ)+1)*(2*m+2)*(2*m+1)) := by
    rw [eq_div_iff (by positivity)]; exact OMA.S_oeis_a344503.c3 m
  have x5 : ((3*m+5).choose (m+1) : ℚ) = ((3*m).choose m : ℚ) * ((3*m+5)*(3*m+4)*(3*m+3)*(3*m+2)*(3*m+1)) / (((m:ℚ)+1)*(2*m+4)*(2*m+3)*(2*m+2)*(2*m+1)) := by
    rw [eq_div_iff (by positivity)]; exact OMA.S_oeis_a344503.c5 m
  have x6 : ((3*m+6).choose (m+2) : ℚ) = ((3*m).choose m : ℚ) * ((3*m+6)*(3*m+5)*(3*m+4)*(3*m+3)*(3*m+2)*(3*m+1)) / (((m:ℚ)+2)*((m:ℚ)+1)*(2*m+4)*(2*m+3)*(2*m+2)*(2*m+1)) := by
    rw [eq_div_iff (by positivity)]; exact OMA.S_oeis_a344503.c6 m
  have hb := hB m
  rcases hm with rfl | rfl | rfl
  · rw [show 3*m+5-1 = 3*m+4 by omega, show 3*m+5-2 = 3*m+3 by omega, show 3*m+5-3 = 3*m+2 by omega,
      show 3*m+5-4 = 3*m+1 by omega, show 3*m+5-5 = 3*m by omega, v5, v4, v3, v2, v1, v0, x2, x3, x5]
    push_cast
    field_simp
    ring
  · rw [show 3*m+6-1 = 3*m+5 by omega, show 3*m+6-2 = 3*m+4 by omega, show 3*m+6-3 = 3*m+3 by omega,
      show 3*m+6-4 = 3*m+2 by omega, show 3*m+6-5 = 3*m+1 by omega, v6, v5, v4, v3, v2, v1, x2, x3, x5, x6]
    push_cast
    field_simp
    ring
  · rw [show 3*m+7-1 = 3*m+6 by omega, show 3*m+7-2 = 3*m+5 by omega, show 3*m+7-3 = 3*m+4 by omega,
      show 3*m+7-4 = 3*m+3 by omega, show 3*m+7-5 = 3*m+2 by omega, v7, v6, v5, v4, v3, v2, x2, x3, x5, x6]
    push_cast
    field_simp
    ring
