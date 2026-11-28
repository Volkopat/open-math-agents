import OMAStatements.S_mo_253088

-- Problem: Expectation of changing the gift choice
-- Source: https://mathoverflow.net/questions/253088/expectation-of-changing-the-gift-choice
-- The distinction between the fair initial choice and the posterior given the
-- observed amount follows the answer by usul (26 October 2016).
-- Credit: @grp06

open OMA.S_mo_253088
open scoped BigOperators

theorem OMA.solution : type_of% @OMA.S_mo_253088.main := by
  classical
  constructor
  · intro n w a hw htotal _ha
    have hmass (ω : Fin n × Bool) : 0 ≤ mass w ω :=
      div_nonneg (hw ω.1) (by norm_num)
    refine ⟨hmass, ?_, ?_, ?_⟩
    · rw [← htotal]
      simp only [Fintype.sum_prod_type, Fintype.sum_bool, mass]
      apply Finset.sum_congr rfl
      intro i _
      ring
    · simp only [expectation, Fintype.sum_prod_type, Fintype.sum_bool]
      apply Finset.sum_congr rfl
      intro i _
      simp [mass, opened, other] <;> ring
    · intro v hv hobs
      let M := observationMass w a v
      let S := smallerMass w a v
      let T : ℝ := ∑ ω : Fin n × Bool, if opened a ω = v then mass w ω * other a ω else 0
      have hM : 0 < M := hobs
      have hS : 0 ≤ S := by
        unfold S smallerMass
        apply Finset.sum_nonneg
        intro ω _
        split
        · exact hmass ω
        · exact le_rfl
      have hSM : S ≤ M := by
        unfold S M smallerMass observationMass
        apply Finset.sum_le_sum
        intro ω _
        by_cases h : opened a ω = v ∧ ω.2 = true
        · simp only [if_pos h, if_pos h.1, le_refl]
        · rw [if_neg h]
          split
          · exact hmass ω
          · exact le_rfl
      have hT : T = v * (3 * S + M) / 2 := by
        calc
          T = ∑ ω : Fin n × Bool,
              v * (3 * (if opened a ω = v ∧ ω.2 = true then mass w ω else 0) +
                (if opened a ω = v then mass w ω else 0)) / 2 := by
            unfold T
            apply Finset.sum_congr rfl
            intro ω _
            by_cases h : opened a ω = v
            · obtain ⟨i, coin⟩ := ω
              cases coin
              · have hi : 2 * a i = v := by simpa [opened] using h
                have ho : other a (i, false) = v / 2 := by
                  simp [other]
                  linarith only [hi]
                have hs : ¬ (opened a (i, false) = v ∧ (i, false).2 = true) := by simp
                simp only [if_pos h, if_neg hs, ho]
                ring
              · have hi : a i = v := by simpa [opened] using h
                have ho : other a (i, true) = 2 * v := by simp [other, hi]
                simp [h, ho] <;> ring
            · simp [h]
          _ = v * (3 * S + M) / 2 := by
            unfold S M smallerMass observationMass
            simp only [div_eq_mul_inv, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
      have hGain : conditionalOther w a v - v = v * (3 * posterior w a v - 1) / 2 := by
        change T / M - v = v * (3 * (S / M) - 1) / 2
        rw [hT]
        field_simp [ne_of_gt hM] <;> ring
      refine ⟨⟨div_nonneg hS hM.le, ?_⟩, hGain, ?_⟩
      · change S / M ≤ 1
        exact (div_le_iff₀ hM).2 (by simpa only [one_mul] using hSM)
      · calc
          v < conditionalOther w a v ↔ 0 < conditionalOther w a v - v := sub_pos.symm
          _ ↔ 0 < v * (3 * posterior w a v - 1) / 2 := by rw [hGain]
          _ ↔ (1 / 3 : ℝ) < posterior w a v := by
            rw [div_pos_iff_of_pos_right (by norm_num : (0 : ℝ) < 2), mul_pos_iff_of_pos_left hv]
            constructor <;> intro h <;> linarith only [h]
  · dsimp only
    repeat' apply And.intro
    all_goals
      norm_num [observationMass, smallerMass, posterior, conditionalOther, mass, opened, other,
        Fintype.sum_prod_type, Fintype.sum_bool, Fintype.univ_unit, Finset.sum_singleton]
