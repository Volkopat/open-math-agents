import OMAStatements.S_mo_476278

lemma OMA.mo476278_cross {ι : Type*} [Fintype ι] (p d g : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hd : ∑ i, p i * d i = 0)
    (hc : ∀ i j, 0 < d i → d j < 0 → g j ≤ g i) :
    0 ≤ ∑ i, p i * d i * g i := by
  classical
  by_cases hne : (Finset.univ.filter (fun j => d j < 0)).Nonempty
  · obtain ⟨j0, hj0, hmax⟩ := Finset.exists_max_image _ g hne
    have hj0' : d j0 < 0 := (Finset.mem_filter.mp hj0).2
    have key : ∑ i, p i * d i * g i = ∑ i, p i * d i * (g i - g j0) := by
      have : ∑ i, p i * d i * (g i - g j0)
          = ∑ i, p i * d i * g i - (∑ i, p i * d i) * g j0 := by
        rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        ring
      rw [this, hd]; ring
    rw [key]
    apply Finset.sum_nonneg
    intro i _
    rcases lt_trichotomy (d i) 0 with h | h | h
    · have h1 := hmax i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      have h2 : p i * d i ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (hp i) h.le
      nlinarith
    · simp [h]
    · have h1 := hc i j0 h hj0'
      have h2 : 0 ≤ p i * d i := mul_nonneg (hp i) h.le
      nlinarith
  · have hall : ∀ i, 0 ≤ d i := by
      intro i; by_contra h; replace h := lt_of_not_ge h
      exact hne ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩
    have hz := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => mul_nonneg (hp i) (hall i))).mp hd
    apply le_of_eq; symm
    apply Finset.sum_eq_zero
    intro i hi
    rw [hz i hi, zero_mul]

lemma OMA.mo476278_conc (f : ℝ → ℝ) (hf : ConcaveOn ℝ (Set.Ici 0) f) {a b c : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hbc : b < c) :
    (f c - f b) * (c - a) ≤ (f c - f a) * (c - b) := by
  have hca : 0 < c - a := by linarith
  have ha' : a ∈ Set.Ici (0:ℝ) := ha
  have hc' : c ∈ Set.Ici (0:ℝ) := by simp only [Set.mem_Ici]; linarith
  have h1 : 0 ≤ (c - b) / (c - a) := div_nonneg (by linarith) hca.le
  have h2 : 0 ≤ (b - a) / (c - a) := div_nonneg (by linarith) hca.le
  have h3 : (c - b) / (c - a) + (b - a) / (c - a) = 1 := by
    field_simp; ring
  have h : ((c - b) / (c - a)) • f a + ((b - a) / (c - a)) • f c
      ≤ f (((c - b) / (c - a)) • a + ((b - a) / (c - a)) • c) := hf.2 ha' hc' h1 h2 h3
  have hb : ((c - b) / (c - a)) • a + ((b - a) / (c - a)) • c = b := by
    simp only [smul_eq_mul]; field_simp; ring
  rw [hb] at h
  simp only [smul_eq_mul] at h
  have h4 := mul_le_mul_of_nonneg_right h hca.le
  have e : ((c - b) / (c - a) * f a + (b - a) / (c - a) * f c) * (c - a)
      = (c - b) * f a + (b - a) * f c := by
    field_simp
  nlinarith [h4, e]

theorem OMA.solution : type_of% @OMA.S_mo_476278.main := by
  intro n x hx0 hxm p hp hp1 f hfc hfm hfpos hVx hVf
  have hxc : ∀ i, x i ≤ x (Fin.last n) := fun i => hxm (Fin.le_last i)
  have hfle : ∀ i j, x i ≤ x j → f (x i) ≤ f (x j) :=
    fun i j h => hfm (hx0 i) (hx0 j) h
  generalize hc : x (Fin.last n) = c at hxc ⊢
  have hc0 : 0 ≤ c := hc ▸ hx0 _
  have hfc' : ∀ i, f (x i) ≤ f c := fun i => hfm (hx0 i) hc0 (hxc i)
  generalize hmx : ∑ j, p j * x j = mx at hVx ⊢
  generalize hmf : ∑ j, p j * f (x j) = mf at hVf ⊢
  -- B and A as sums
  have hB : c - mx = ∑ i, p i * (c - x i) := by
    rw [← hmx]
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hp1, one_mul]
  have hA : f c - mf = ∑ i, p i * (f c - f (x i)) := by
    rw [← hmf]
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hp1, one_mul]
  have hVx' : ∑ i, p i * (x i - mx) ^ 2
      = ∑ i, p i * (c - x i) ^ 2 - (c - mx) ^ 2 := by
    have e : ∀ i, p i * (x i - mx) ^ 2
        = p i * (c - x i) ^ 2 - 2 * (c - mx) * (p i * (c - x i)) + (c - mx) ^ 2 * p i := by
      intro i; ring
    rw [Finset.sum_congr rfl (fun i _ => e i), Finset.sum_add_distrib,
      Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hp1, ← hB]
    ring
  have hVf' : ∑ i, p i * (f (x i) - mf) ^ 2
      = ∑ i, p i * (f c - f (x i)) ^ 2 - (f c - mf) ^ 2 := by
    have e : ∀ i, p i * (f (x i) - mf) ^ 2
        = p i * (f c - f (x i)) ^ 2 - 2 * (f c - mf) * (p i * (f c - f (x i)))
          + (f c - mf) ^ 2 * p i := by
      intro i; ring
    rw [Finset.sum_congr rfl (fun i _ => e i), Finset.sum_add_distrib,
      Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hp1, ← hA]
    ring
  have hB0 : 0 ≤ c - mx := by
    rw [hB]; exact Finset.sum_nonneg (fun i _ => mul_nonneg (hp i) (by linarith [hxc i]))
  have hA0 : 0 ≤ f c - mf := by
    rw [hA]; exact Finset.sum_nonneg (fun i _ => mul_nonneg (hp i) (by linarith [hfc' i]))
  -- core inequality
  have core : (f c - mf) ^ 2 * ∑ i, p i * (c - x i) ^ 2
      ≤ (c - mx) ^ 2 * ∑ i, p i * (f c - f (x i)) ^ 2 := by
    set A := f c - mf with hAdef
    set B := c - mx with hBdef
    have hsum : ∑ i, p i * (B * (f c - f (x i)) - A * (c - x i)) = 0 := by
      have e : ∀ i, p i * (B * (f c - f (x i)) - A * (c - x i))
          = B * (p i * (f c - f (x i))) - A * (p i * (c - x i)) := by intro i; ring
      rw [Finset.sum_congr rfl (fun i _ => e i), Finset.sum_sub_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum, ← hA, ← hB]
      ring
    have hcr := OMA.mo476278_cross p (fun i => B * (f c - f (x i)) - A * (c - x i))
      (fun i => B * (f c - f (x i)) + A * (c - x i)) hp hsum (by
        intro i j hi hj
        by_cases hij : x i ≤ x j
        · have h1 := hfle i j hij
          nlinarith [mul_le_mul_of_nonneg_left h1 hB0, mul_le_mul_of_nonneg_left hij hA0]
        · replace hij := lt_of_not_ge hij
          exfalso
          have hic : x i < c := by
            rcases lt_or_eq_of_le (hxc i) with h | h
            · exact h
            · rw [h] at hi; simp at hi
          have hconc := OMA.mo476278_conc f hfc (hx0 j) hij hic
          have hzi : 0 < c - x i := by linarith
          have hzj : 0 < c - x j := by linarith
          nlinarith [mul_pos hi hzj, mul_pos (neg_pos.mpr hj) hzi,
            mul_le_mul_of_nonneg_left hconc hB0])
    have e2 : ∑ i, p i * (B * (f c - f (x i)) - A * (c - x i)) * (B * (f c - f (x i)) + A * (c - x i))
        = B ^ 2 * ∑ i, p i * (f c - f (x i)) ^ 2 - A ^ 2 * ∑ i, p i * (c - x i) ^ 2 := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      ring
    beta_reduce at hcr
    linarith [hcr, e2]
  have sx := Real.sqrt_pos.mpr hVx
  have sf := Real.sqrt_pos.mpr hVf
  rw [div_le_div_iff₀ sf sx]
  have L0 : 0 ≤ (f c - mf) * Real.sqrt (∑ i, p i * (x i - mx) ^ 2) := mul_nonneg hA0 sx.le
  have R0 : 0 ≤ (c - mx) * Real.sqrt (∑ i, p i * (f (x i) - mf) ^ 2) := mul_nonneg hB0 sf.le
  have hsq : ((f c - mf) * Real.sqrt (∑ i, p i * (x i - mx) ^ 2)) ^ 2
      ≤ ((c - mx) * Real.sqrt (∑ i, p i * (f (x i) - mf) ^ 2)) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hVx.le, Real.sq_sqrt hVf.le, hVx', hVf']
    nlinarith [core]
  nlinarith [hsq, L0, R0]
