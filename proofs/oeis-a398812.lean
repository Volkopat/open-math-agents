import OMAStatements.S_oeis_a398812

-- Problem: A398812, a(n)/n^2 -> 1 (A138808(n) <= n tau(n) <= 2 n sqrt n).
-- Credit: @bnb9001

namespace OMA_A398812_Proof

open Filter Topology OMA.S_oeis_a398812

lemma B_le (n : ℕ) : B n ≤ 2 * n * Nat.sqrt n := by
  let s := Finset.Icc 1 n
  let t := Finset.Icc 1 (Nat.sqrt n)
  unfold B
  calc
    _ ≤ (t ×ˢ s ∪ s ×ˢ t).card := by
      apply Finset.card_le_card
      rintro ⟨x, y⟩ h
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at h
      obtain ⟨⟨hx, hy⟩, p, hp, hxp, hyp⟩ := h
      have hxy : x * y ≤ n :=
        (Nat.mul_le_mul hxp hyp).trans_eq (Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hp))
      simp only [s, t, Finset.mem_union, Finset.mem_product, Finset.mem_Icc]
      rcases le_total x y with h | h
      · exact Or.inl ⟨⟨hx.1, Nat.le_sqrt.2 ((Nat.mul_le_mul_left x h).trans hxy)⟩, hy⟩
      · exact Or.inr ⟨hx, hy.1, Nat.le_sqrt.2 ((Nat.mul_le_mul_right y h).trans hxy)⟩
    _ ≤ (t ×ˢ s).card + (s ×ˢ t).card := Finset.card_union_le _ _
    _ = _ := by simp [s, t, Finset.card_product, Nat.card_Icc]; ring

lemma B_le_sq (n : ℕ) : B n ≤ n ^ 2 := by
  unfold B
  calc _ ≤ (Finset.Icc 1 n ×ˢ Finset.Icc 1 n).card := Finset.card_filter_le _ _
    _ = n ^ 2 := by simp [sq]

end OMA_A398812_Proof

open Filter Topology OMA_A398812_Proof OMA.S_oeis_a398812 in
theorem OMA.solution : type_of% @OMA.S_oeis_a398812.main := by
  have hsq : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun n : ℕ => 2 / Real.sqrt n) atTop (𝓝 0) := by
    have := (tendsto_inv_atTop_zero.comp hsq).const_mul 2
    simpa [div_eq_mul_inv] using this
  have hB : Tendsto (fun n : ℕ => (B n : ℝ) / (n : ℝ) ^ 2) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hs0 : 0 < Real.sqrt n := Real.sqrt_pos.2 hn0
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h1 : (B n : ℝ) ≤ n * (2 * Real.sqrt n) := by
      have hb : (B n : ℝ) ≤ 2 * n * (Nat.sqrt n : ℝ) := by exact_mod_cast B_le n
      calc
        _ ≤ 2 * n * (Nat.sqrt n : ℝ) := hb
        _ ≤ 2 * n * Real.sqrt n := by gcongr; exact Real.nat_sqrt_le_real_sqrt
        _ = _ := by ring
    have hsqn : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn0.le
    rw [div_le_div_iff₀ (by positivity) hs0]
    nlinarith
  have := hB.const_sub 1
  simp only [sub_zero] at this
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  unfold a
  rw [Nat.cast_sub (B_le_sq n)]
  push_cast
  field_simp
