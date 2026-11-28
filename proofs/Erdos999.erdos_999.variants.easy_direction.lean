import FormalConjectures.ErdosProblems.«999»

/-! Proof of `Erdos999.erdos_999.variants.easy_direction` via the first Borel-Cantelli lemma
on the interval `(1/4, 3/4)`. -/

open MeasureTheory Finset

theorem OMA.solution : type_of% @Erdos999.erdos_999.variants.easy_direction := by
  intro f hf hae hsum
  let B : Set ℝ := Set.Ioo (1 / 4) (3 / 4)
  let A : ℕ → Set ℝ := fun q =>
    B ∩ {x | 0 < q ∧ ∃ p : ℤ, Int.gcd p q = 1 ∧ |x - p / q| < f q / q}
  have hle : ∀ q, volume (A q) ≤ ENNReal.ofReal (2 * ((q.totient : ℝ) * f q / q)) := fun q => by
    rcases Nat.eq_zero_or_pos q with rfl | hq
    · simp [A]
    · have hφ : (1 : ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
      rcases le_or_gt (1 / 4) (f q / q) with hr | hr
      · exact (measure_mono Set.inter_subset_left).trans <|
          Real.volume_Ioo.trans_le <| ENNReal.ofReal_le_ofReal (by rw [mul_div_assoc]; nlinarith)
      · calc volume (A q)
          _ ≤ volume (⋃ j ∈ (range q).filter q.Coprime, Metric.ball ((j : ℝ) / q) (f q / q)) := by
              refine measure_mono fun x ⟨⟨hx1, hx2⟩, _, p, hgcd, hdist⟩ => ?_
              have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr hq
              have hd := abs_lt.mp hdist
              have hp0 : (0 : ℤ) ≤ p := by
                exact_mod_cast ((div_pos_iff_of_pos_right hqR).mp (by linarith : (0 : ℝ) < p / q)).le
              have hpq : p < q := by
                exact_mod_cast (div_lt_one hqR).mp (by linarith : (p : ℝ) / q < 1)
              lift p to ℕ using hp0
              exact Set.mem_biUnion
                (mem_filter.mpr ⟨mem_range.mpr (by exact_mod_cast hpq),
                  by simpa [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm] using hgcd⟩)
                (by simpa [Metric.mem_ball, Real.dist_eq] using hdist)
          _ ≤ ∑ j ∈ (range q).filter q.Coprime, volume (Metric.ball ((j : ℝ) / q) (f q / q)) :=
              measure_biUnion_finset_le _ _
          _ = ENNReal.ofReal (2 * ((q.totient : ℝ) * f q / q)) := by
              simp only [Real.volume_ball, sum_const, nsmul_eq_mul, ← Nat.totient_eq_card_coprime,
                ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
              congr 1; ring
  have htsum : (∑' q, volume (A q)) ≠ ⊤ :=
    ne_top_of_le_ne_top (by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun q => by have := hf q; positivity) (hsum.mul_left 2)]
      exact ENNReal.ofReal_ne_top) (ENNReal.tsum_le_tsum hle)
  have hB : ∀ᵐ x, x ∉ B :=
    (hae.and (ae_finite_setOfPred_mem htsum)).mono fun x ⟨hx, hfin⟩ hxB =>
      hx (hfin.subset fun q hq => ⟨hxB, hq⟩)
  simp [ae_iff] at hB
  norm_num [B, Real.volume_Ioo] at hB
