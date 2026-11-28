import FormalConjectures.Wikipedia.RefactorableNumber

-- Credit: @mjsechrest2
theorem OMA.solution : type_of% @RefactorableNumber.zelinsky_refactorable_progression_conjecture := by
  rintro m n hm ⟨h0, hd⟩
  obtain ⟨p, hp, hg, hq⟩ := Nat.exists_prime_gt_modEq_one n (Nat.one_le_iff_ne_zero.mp hm)
  have h1 : p - 1 ≠ 0 := by have := hp.two_le; omega
  have hp0 : 0 < p ^ (p - 1) := pow_pos hp.pos _
  have hd2 : p ∣ p ^ (p - 1) := dvd_pow_self p h1
  refine ⟨n * p ^ (p - 1), by nlinarith [hp.two_le, Nat.le_of_dvd hp0 hd2], ⟨mul_pos h0 hp0, ?_⟩, ?_⟩
  · rw [((hp.coprime_iff_not_dvd.mpr fun h => hg.not_ge (Nat.le_of_dvd h0 h)).symm.pow_right _).card_divisors_mul,
      Nat.divisors_prime_pow hp, Finset.card_map, Finset.card_range, Nat.sub_add_cancel hp.pos]
    exact Nat.mul_dvd_mul hd hd2
  · simpa using (hq.pow (p - 1)).mul_left n
