import FormalConjectures.ErdosProblems.«1136»

/-! Enumerating the multiples below n gives a ceiling, so the density follows
directly from the asymptotic for the ceiling function. -/

open Filter Topology

private theorem count_thirds (n : ℕ) :
    ({m : ℕ | 3 ∣ m} ∩ Set.Iio n).ncard = ⌈(1 / 3 : ℝ) * n⌉₊ := by
  have image : {m : ℕ | 3 ∣ m} ∩ Set.Iio n =
      (3 * ·) '' Set.Iio ⌈(1 / 3 : ℝ) * n⌉₊ := by
    ext m
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Iio, Set.mem_image,
      Nat.lt_ceil, one_div_mul_eq_div, lt_div_iff₀ (by norm_num : (0 : ℝ) < 3)]
    constructor
    · rintro ⟨⟨k, rfl⟩, h⟩
      exact ⟨k, by exact_mod_cast (show k * 3 < n by omega), rfl⟩
    · rintro ⟨k, h, rfl⟩
      exact ⟨dvd_mul_right _ _, by exact_mod_cast (mul_comm (3 : ℝ) k ▸ h)⟩
  rw [image, Set.ncard_image_of_injective _ (mul_right_injective₀ (by decide : (3 : ℕ) ≠ 0))]
  simp

theorem OMA.solution : type_of% @Erdos1136.erdos_1136.variants.multiples_of_three := by
  constructor
  · intro a ha b hb k h
    exact (by decide : ¬ (3 : ℕ) ∣ 2)
      (Nat.prime_three.dvd_of_dvd_pow (h ▸ dvd_add ha hb))
  · simpa [Set.HasDensity, Set.partialDensity, count_thirds, Function.comp_def] using
      (tendsto_nat_ceil_mul_div_atTop (a := (1 / 3 : ℝ)) (by norm_num)).comp
        tendsto_natCast_atTop_atTop
