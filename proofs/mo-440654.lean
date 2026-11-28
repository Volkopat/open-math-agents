import OMAStatements.S_mo_440654

theorem OMA.solution : type_of% @OMA.S_mo_440654.main := by
  intro H _ _ _ f x P hconv hprox s hs t ht hst
  rw [Set.mem_Ici] at hs ht
  rcases hconv with ⟨hne_bot, ⟨z, hz_top⟩, _⟩
  rcases eq_or_lt_of_le hs with rfl | hs_pos
  · have h0 := hprox 0 le_rfl x
    simp only [OMA.S_mo_440654.objective, EReal.coe_zero, zero_mul, add_zero, sub_self,
      norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at h0
    rw [← EReal.coe_zero, EReal.coe_le_coe_iff] at h0
    exact le_trans h0 (sq_nonneg _)
  · rcases eq_or_lt_of_le hst with rfl | hst_lt
    · exact le_rfl
    · have ht_pos : 0 < t := lt_trans hs_pos hst_lt
      have hne_top : ∀ r : ℝ, 0 < r → f (P r) ≠ ⊤ := by
        intro r hr htop
        have hle := hprox r (le_of_lt hr) z
        unfold OMA.S_mo_440654.objective at hle
        rw [htop, EReal.coe_mul_top_of_pos hr, EReal.coe_add_top] at hle
        have hz_eq : ((f z).toReal : EReal) = f z := EReal.coe_toReal hz_top (hne_bot z)
        rw [← hz_eq, ← EReal.coe_mul, ← EReal.coe_add] at hle
        exact EReal.coe_ne_top _ (top_le_iff.mp hle)
      have hfs : ((f (P s)).toReal : EReal) = f (P s) :=
        EReal.coe_toReal (hne_top s hs_pos) (hne_bot (P s))
      have hft : ((f (P t)).toReal : EReal) = f (P t) :=
        EReal.coe_toReal (hne_top t ht_pos) (hne_bot (P t))
      have h1 := hprox s hs (P t)
      have h2 := hprox t ht (P s)
      unfold OMA.S_mo_440654.objective at h1 h2
      rw [← hfs, ← hft] at h1 h2
      simp only [← EReal.coe_mul, ← EReal.coe_add, EReal.coe_le_coe_iff] at h1 h2
      have hmul : 0 ≤ (t - s) * ((f (P s)).toReal - (f (P t)).toReal) := by
        have hadd := add_le_add h1 h2
        have hsub : 0 ≤ (‖P t - x‖ ^ 2 + s * (f (P t)).toReal + (‖P s - x‖ ^ 2 + t * (f (P s)).toReal)) -
            (‖P s - x‖ ^ 2 + s * (f (P s)).toReal + (‖P t - x‖ ^ 2 + t * (f (P t)).toReal)) :=
          sub_nonneg.mpr hadd
        have heq : (t - s) * ((f (P s)).toReal - (f (P t)).toReal) =
            (‖P t - x‖ ^ 2 + s * (f (P t)).toReal + (‖P s - x‖ ^ 2 + t * (f (P s)).toReal)) -
            (‖P s - x‖ ^ 2 + s * (f (P s)).toReal + (‖P t - x‖ ^ 2 + t * (f (P t)).toReal)) := by
          ring
        rw [heq]
        exact hsub
      have hba : 0 ≤ (f (P s)).toReal - (f (P t)).toReal :=
        nonneg_of_mul_nonneg_right hmul (sub_pos.mpr hst_lt)
      have hsba : 0 ≤ s * ((f (P s)).toReal - (f (P t)).toReal) :=
        mul_nonneg (le_of_lt hs_pos) hba
      have hdiff : 0 ≤ ‖P t - x‖ ^ 2 - ‖P s - x‖ ^ 2 := by
        have h1' : s * ((f (P s)).toReal - (f (P t)).toReal) ≤ ‖P t - x‖ ^ 2 - ‖P s - x‖ ^ 2 := by
          have := sub_le_sub_right h1 (‖P s - x‖ ^ 2 + s * (f (P t)).toReal)
          have hl : ‖P s - x‖ ^ 2 + s * (f (P s)).toReal - (‖P s - x‖ ^ 2 + s * (f (P t)).toReal) =
              s * ((f (P s)).toReal - (f (P t)).toReal) := by ring
          have hr : ‖P t - x‖ ^ 2 + s * (f (P t)).toReal - (‖P s - x‖ ^ 2 + s * (f (P t)).toReal) =
              ‖P t - x‖ ^ 2 - ‖P s - x‖ ^ 2 := by ring
          rwa [hl, hr] at this
        exact le_trans hsba h1'
      exact sub_nonneg.mp hdiff
