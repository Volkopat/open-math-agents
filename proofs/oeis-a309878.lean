import OMAStatements.S_oeis_a309878

namespace OMA.P309878

open OMA.S_oeis_a309878 Complex

lemma b_closed (n : ℕ) : b n = -2 * I * (1 + I) ^ n + (I - 1) * (n : ℂ) + 2 * I := by
  induction n with
  | zero => simp [b]
  | succ n ih =>
    rw [b, ih]
    push_cast
    linear_combination ((n : ℂ) + 2) * I_sq

lemma b_rec (m : ℕ) :
    b (m + 4) = 4 * b (m + 3) - 7 * b (m + 2) + 6 * b (m + 1) - 2 * b m := by
  simp only [b_closed]
  have hw : (1 + I) ^ 2 - 2 * (1 + I) + 2 = 0 := by
    linear_combination I_sq
  push_cast
  generalize (1 + I : ℂ) = w at hw ⊢
  linear_combination (-2 * I * w ^ m * (w - 1) ^ 2) * hw

end OMA.P309878

open OMA.S_oeis_a309878 OMA.P309878 Complex in
theorem OMA.solution : type_of% @OMA.S_oeis_a309878.main := by
  constructor
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    have h := congrArg Complex.re (b_rec m)
    have e1 : m + 4 - 1 = m + 3 := by omega
    have e2 : m + 4 - 2 = m + 2 := by omega
    have e3 : m + 4 - 3 = m + 1 := by omega
    have e4 : m + 4 - 4 = m := by omega
    rw [e1, e2, e3, e4]
    unfold a
    simp only [Complex.add_re, Complex.sub_re, Complex.mul_re] at h
    norm_num at h
    linarith
  · intro n
    unfold a
    rw [b_closed]
    have hc : (1 - I : ℂ) ^ n = (starRingEnd ℂ) ((1 + I) ^ n) := by
      simp [map_pow, sub_eq_add_neg]
    rw [hc]
    generalize (1 + I : ℂ) ^ n = z
    apply Complex.ext <;> simp <;> ring
