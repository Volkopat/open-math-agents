import OMAReductions.R_OeisA243512_conjecture_R1

/-!
# Proof of `OeisA243512.conjecture.R1.H1`

For every prime `p`:
- `i = p ^ 2` has `σ(p^2) / p^2 = (p^2 + p + 1) / p^2` in lowest terms, so
  `abundancyDiff (p^2) = p + 1`, hence `OeisA243512.a (p + 1) ≠ 0`.
- For `5 ≤ p`, `i = 2 * p` has `σ(2p) / (2p) = (3 * ((p + 1) / 2)) / p` in lowest terms, so
  `abundancyDiff (2 * p) = (p + 3) / 2`, hence `OeisA243512.a ((p + 3) / 2) ≠ 0`.
-/

open OeisA243512

private lemma mkRat_num_den_of_coprime {a b : ℕ} (hb : b ≠ 0) (hcop : a.Coprime b) :
    (mkRat (a : ℤ) b).num = (a : ℤ) ∧ (mkRat (a : ℤ) b).den = b := by
  set r : ℚ := mkRat (a : ℤ) b
  have hr_eq : (r : ℚ) = (a : ℚ) / (b : ℚ) := by
    simp [r, Rat.mkRat_eq_div]
  have hr_nonneg : 0 ≤ r := by
    rw [hr_eq]
    positivity
  have hnum_nonneg : 0 ≤ r.num := Rat.num_nonneg.mpr hr_nonneg
  have hden_pos : 0 < r.den := r.pos
  have hcross_q : (r.num : ℚ) * (b : ℚ) = (a : ℚ) * (r.den : ℚ) := by
    have h1 : (r.num : ℚ) / (r.den : ℚ) = (a : ℚ) / (b : ℚ) :=
      (Rat.num_div_den r).trans hr_eq
    have hb_q : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hb
    have hden_q : (r.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hden_pos.ne'
    field_simp [hb_q, hden_q] at h1
    linarith
  have hcross_z : r.num * (b : ℤ) = (a : ℤ) * (r.den : ℤ) := by
    exact_mod_cast hcross_q
  have hcross_n : r.num.natAbs * b = a * r.den := by
    have := congrArg Int.natAbs hcross_z
    simpa [Int.natAbs_mul] using this
  have hred : r.num.natAbs.Coprime r.den := r.reduced
  have hdvd1 : r.den ∣ b := hred.symm.dvd_of_dvd_mul_left ⟨a, by linarith⟩
  have hdvd2 : b ∣ r.den := hcop.symm.dvd_of_dvd_mul_left ⟨r.num.natAbs, by linarith⟩
  have hden_eq : r.den = b := Nat.dvd_antisymm hdvd1 hdvd2
  have hnum_nat : r.num.natAbs = a := by
    rw [hden_eq] at hcross_n
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hb) hcross_n
  have hnum_eq : r.num = (a : ℤ) := by
    have := Int.natAbs_of_nonneg hnum_nonneg
    omega
  exact ⟨hnum_eq, hden_eq⟩

private lemma a_ne_zero_of_witness {n i : ℕ} (hi : 0 < i) (h : abundancyDiff i = n) :
    OeisA243512.a n ≠ 0 := by
  unfold OeisA243512.a
  have hne : {j : ℕ | 0 < j ∧ abundancyDiff j = n}.Nonempty := ⟨i, hi, h⟩
  have hmem := Nat.sInf_mem hne
  exact hmem.1.ne'

private lemma sum_divisors_int_eq_sigma (i : ℕ) :
    (∑ d ∈ i.divisors, (d : ℤ)) = (ArithmeticFunction.sigma 1 i : ℤ) := by
  norm_cast
  simp [ArithmeticFunction.sigma_apply]

theorem OMA.solution : OMA.R_OeisA243512_conjecture_R1.H1 := by
  intro p hp
  constructor
  · apply a_ne_zero_of_witness (i := p ^ 2) (pow_pos hp.pos 2)
    unfold abundancyDiff
    have hp2_ne : p ^ 2 ≠ 0 := pow_ne_zero 2 hp.ne_zero
    rw [if_neg hp2_ne, sum_divisors_int_eq_sigma]
    have hsig : ArithmeticFunction.sigma 1 (p ^ 2) = p ^ 2 + p + 1 := by
      have h := ArithmeticFunction.sigma_one_apply_prime_pow hp (i := 2)
      simp [Finset.sum_range_succ] at h
      omega
    rw [hsig]
    have hcop : (p ^ 2 + p + 1).Coprime (p ^ 2) := by
      refine Nat.Coprime.pow_right 2 ?_
      rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
      intro hdvd
      have h1 : p ∣ p ^ 2 + p := by
        rw [sq]; exact dvd_add (dvd_mul_left p p) dvd_rfl
      have : p ∣ 1 := (Nat.dvd_add_right h1).mp hdvd
      exact hp.not_dvd_one this
    obtain ⟨hnum, hden⟩ := mkRat_num_den_of_coprime hp2_ne hcop
    dsimp only
    rw [hnum, hden]
    omega
  · intro hp5
    apply a_ne_zero_of_witness (i := 2 * p) (by omega)
    unfold abundancyDiff
    have h2p_ne : 2 * p ≠ 0 := by omega
    rw [if_neg h2p_ne, sum_divisors_int_eq_sigma]
    have hp_odd : p % 2 = 1 := by
      rcases hp.eq_two_or_odd with h2 | hodd
      · omega
      · exact hodd
    have hcop2p : Nat.Coprime 2 p :=
      Nat.prime_two.coprime_iff_not_dvd.mpr (by omega)
    have hsig : ArithmeticFunction.sigma 1 (2 * p) = 3 * (p + 1) := by
      rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop2p]
      have h2 : ArithmeticFunction.sigma 1 2 = 3 := by decide
      have hp1 : ArithmeticFunction.sigma 1 p = p + 1 := by
        have h := ArithmeticFunction.sigma_one_apply_prime_pow hp (i := 1)
        simp [Finset.sum_range_succ] at h
        omega
      rw [h2, hp1]
    rw [hsig]
    set k := (p + 1) / 2
    have hk : 2 * k = p + 1 := by omega
    have hmk : mkRat ((3 * (p + 1) : ℕ) : ℤ) (2 * p) = mkRat ((3 * k : ℕ) : ℤ) p := by
      rw [Rat.mkRat_eq_div, Rat.mkRat_eq_div]
      have h2q : (2 : ℚ) ≠ 0 := by norm_num
      have hpq : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
      have hkq : (p : ℚ) + 1 = 2 * (k : ℚ) := by exact_mod_cast hk.symm
      push_cast
      rw [hkq]
      field_simp [h2q, hpq]
    have hcop3k : (3 * k).Coprime p := by
      refine Nat.Coprime.mul_left ?_ ?_
      · rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
        intro h
        have := Nat.le_of_dvd (by norm_num) h
        omega
      · rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
        intro h
        have hk_pos : 0 < k := by omega
        have := Nat.le_of_dvd hk_pos h
        omega
    obtain ⟨hnum, hden⟩ := mkRat_num_den_of_coprime hp.ne_zero hcop3k
    dsimp only
    rw [hmk, hnum, hden]
    omega
