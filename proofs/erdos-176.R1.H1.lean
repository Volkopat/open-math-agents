import OMAReductions.R_erdos_176_R1

/-! Suppose every k-term progression a, a + d, …, a + (k - 1) d in [1, N] has f-sum zero.
Comparing the progressions with difference 1 starting at b and at b + 1 gives f (b + k) = f b
whenever b + k ≤ N. Hence f (1 + i k) = f 1 for all i < k, because 1 + (k - 1) k ≤ k² ≤ N. Then
the progression 1, 1 + k, …, 1 + (k - 1) k has sum k · f 1 = ±k ≠ 0, a contradiction. -/

theorem OMA.solution : OMA.R_erdos_176_R1.H1 := by
  intro k hk N hN f hf
  by_contra hcon
  push Not at hcon
  have step : ∀ b, 1 ≤ b → b + k ≤ N → f (b + k) = f b := by
    intro b hb hbk
    have e1 := hcon b 1 hb le_rfl (by omega)
    have e2 := hcon (b + 1) 1 (by omega) le_rfl (by omega)
    have e1' : ∑ i ∈ Finset.range k, f (b + i) = 0 := by
      rw [← e1]
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      ring
    have e2' : ∑ i ∈ Finset.range k, f (b + (i + 1)) = 0 := by
      rw [← e2]
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      ring
    have h3 : ∑ i ∈ Finset.range (k + 1), f (b + i) =
        ∑ i ∈ Finset.range k, f (b + i) + f (b + k) := Finset.sum_range_succ _ _
    have h4 : ∑ i ∈ Finset.range (k + 1), f (b + i) =
        ∑ i ∈ Finset.range k, f (b + (i + 1)) + f (b + 0) := Finset.sum_range_succ' _ _
    simp only [add_zero] at h4
    linarith
  have per : ∀ i, i < k → f (1 + i * k) = f 1 := by
    intro i
    induction i with
    | zero => intro _; simp
    | succ i ih =>
      intro hi
      have h2 := Nat.mul_le_mul_right k (show i + 2 ≤ k by omega)
      have hik : 1 + i * k + k ≤ N := by nlinarith
      rw [show 1 + (i + 1) * k = 1 + i * k + k by ring, step _ (by omega) hik, ih (by omega)]
  have hlast : 1 + (k - 1) * k ≤ N := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    nlinarith
  have hfin := hcon 1 k le_rfl hk hlast
  have hsum : ∑ i ∈ Finset.range k, f (1 + i * k) = ∑ i ∈ Finset.range k, f 1 :=
    Finset.sum_congr rfl (fun i hi => per i (Finset.mem_range.1 hi))
  rw [hsum, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hfin
  rcases hf 1 with h | h <;> rw [h] at hfin <;> omega
