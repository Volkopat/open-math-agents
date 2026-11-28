import OMAReductions.R_Bugeaud08_problem_10_8_variants_exceptional_set_dimH_zero_R1

open Filter Set

theorem OMA.solution : OMA.R_Bugeaud08_problem_10_8_variants_exceptional_set_dimH_zero_R1.H2 := by
  intro p _ ξ hξ
  let u (q : ℕ) : ℝ := q * padicNorm p q * distToNearestInt (q * ξ)
  let B : Set ℝ := {a | ∀ᶠ q in atTop, a ≤ u q}
  change liminf u atTop ≠ 0 at hξ
  rw [liminf_eq] at hξ
  change sSup B ≠ 0 at hξ
  have hb : BddAbove B := by
    by_contra hn
    exact hξ (Real.sSup_of_not_bddAbove hn)
  have hzero : 0 ∈ B := by
    apply Eventually.of_forall
    intro q
    unfold u
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg q)
      (Rat.cast_nonneg.mpr (padicNorm.nonneg (p := p) q))) (distToNearestInt_nonneg _)
  have hpos : 0 < sSup B := lt_of_le_of_ne (le_csSup hb hzero) (Ne.symm hξ)
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hpos
  obtain ⟨a, ha, hka⟩ := exists_lt_of_lt_csSup ⟨0, hzero⟩ hk
  have he : ∀ᶠ q in atTop, (1 : ℝ) / (k + 1) ≤ u q :=
    (show ∀ᶠ q in atTop, a ≤ u q from ha).mono fun q hq => hka.le.trans hq
  exact mem_iUnion.mpr ⟨k, eventually_atTop.mp he⟩