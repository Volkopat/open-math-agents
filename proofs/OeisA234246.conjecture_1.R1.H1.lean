import OMAReductions.R_OeisA234246_conjecture_1_R1

/-!
A single witness k with k phi(n - k) + 1 = r^2 makes the counting sum
positive. With n - k = j and f = phi(j), the witnesses k = c^2 f + 2c
(r = c f + 1) and k = c^2 f - 2c (r = c f - 1) give the two families.
-/

namespace OMA.R_OeisA234246_conjecture_1_R1.Step1

theorem pos_of_witness (n k r : ℕ) (hk1 : 1 ≤ k) (hkn : k < n)
    (hr : r * r = k * (n - k).totient + 1) : 0 < OeisA234246.a n := by
  unfold OeisA234246.a
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum
    (f := fun k => (let m := k * (n - k).totient + 1
      if ∃ r ≤ m, r * r = m then 1 else 0))
    (fun i _ => Nat.zero_le _) (Finset.mem_Ico.mpr ⟨hk1, hkn⟩))
  have hrle : r ≤ k * (n - k).totient + 1 := by
    rw [← hr]
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · simp [h0]
    · exact Nat.le_mul_of_pos_left r h0
  simp only
  rw [if_pos ⟨r, hrle, hr⟩]
  exact Nat.one_pos

end OMA.R_OeisA234246_conjecture_1_R1.Step1

open OMA.R_OeisA234246_conjecture_1_R1.Step1 in
theorem OMA.solution : OMA.R_OeisA234246_conjecture_1_R1.H1 := by
  intro j c hj hc
  constructor
  · apply pos_of_witness _ (c ^ 2 * j.totient + 2 * c) (c * j.totient + 1) (by nlinarith) (by omega)
    rw [Nat.add_sub_cancel]
    ring
  · intro hlt
    apply pos_of_witness _ (c ^ 2 * j.totient - 2 * c) (c * j.totient - 1) (by omega) (by omega)
    rw [Nat.add_sub_cancel]
    generalize j.totient = f at hlt ⊢
    have h2 : 2 ≤ c * f := by
      by_contra h
      push_neg at h
      have : c ^ 2 * f ≤ 2 * c := by nlinarith
      omega
    have hle : 2 * c ≤ c ^ 2 * f := hlt.le
    have h1 : 1 ≤ c * f := by omega
    zify [hle, h1]
    ring
