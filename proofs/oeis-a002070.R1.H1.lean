import OMAReductions.R_oeis_a002070_R1

open OMA.S_oeis_a002070

theorem OMA.solution : OMA.R_oeis_a002070_R1.H1 := by
  intro p hp
  let I := Finset.Icc 1 p
  let D (xy : ℕ × ℕ) := (p : ℤ) ∣ f xy.1 xy.2
  let g (xy : ℕ × ℕ) := Int.gcd (f xy.1 xy.2) p
  have hg (xy : ℕ × ℕ) : g xy = 1 ∨ g xy = p := by
    apply (Nat.dvd_prime hp).mp
    exact_mod_cast Int.gcd_dvd_right (f xy.1 xy.2) (p : ℤ)
  have hd (xy : ℕ × ℕ) : D xy ↔ g xy = p := by
    constructor
    · intro h
      rcases hg xy with h1 | h2
      · have hpg : p ∣ g xy := Int.dvd_gcd h (dvd_refl (p : ℤ))
        rw [h1] at hpg
        exact (hp.ne_one (Nat.dvd_one.mp hpg)).elim
      · exact h2
    · intro h
      have hdiv := Int.gcd_dvd_left (f xy.1 xy.2) (p : ℤ)
      change (g xy : ℤ) ∣ f xy.1 xy.2 at hdiv
      rw [h] at hdiv
      exact hdiv
  have hmem (xy : ℕ × ℕ) : g xy ∈ I := by
    rcases hg xy with h | h
    · simp [I, h, hp.one_lt.le]
    · simp [I, h, hp.one_lt.le]
  have hweight (xy : ℕ × ℕ) :
      ((A023900 (g xy) : ℤ) : ℚ) / p = 1 / (p : ℚ) - (if D xy then 1 else 0) := by
    have hpn : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
    by_cases h : D xy
    · rw [(hd xy).mp h, if_pos h]
      simp [A023900, hp.primeFactors]
      field_simp
    · have h1 := (hg xy).resolve_right (fun he => h ((hd xy).mpr he))
      rw [h1, if_neg h]
      simp [A023900]
  change (∑ k ∈ I, ∑ y ∈ I, ∑ x ∈ I,
    if g (x,y) = k then ((A023900 k : ℤ) : ℚ) / p else 0) =
      (p : ℚ) - (((I ×ˢ I).filter D).card : ℚ)
  calc
    _ = ∑ k ∈ I, ∑ xy ∈ I ×ˢ I,
        if g xy = k then ((A023900 k : ℤ) : ℚ) / p else 0 := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_product, Finset.sum_comm]
    _ = ∑ xy ∈ I ×ˢ I, ((A023900 (g xy) : ℤ) : ℚ) / p := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro xy _
      simp [Finset.sum_ite_eq, hmem xy]
    _ = (p : ℚ) - (((I ×ˢ I).filter D).card : ℚ) := by
      simp_rw [hweight]
      rw [Finset.sum_sub_distrib, ← Finset.sum_filter]
      have hcard : I.card = p := by simp [I, Nat.card_Icc]
      simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_one, mul_one,
        Finset.card_product, Nat.cast_mul, hcard]
      have hpn : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
      field_simp
