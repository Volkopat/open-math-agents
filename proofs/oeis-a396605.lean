import OMAStatements.S_oeis_a396605

-- Credit: @oh-meh
open OMA.S_oeis_a396605 Finset Filter Topology

private theorem small_totient {d K : ℕ} (hd : 0 < d) (hφ : d.totient ≤ K) :
    d ≤ (2*K).factorial := by
  apply Nat.le_of_dvd (Nat.factorial_pos _)
  apply (Nat.dvd_iff_prime_pow_dvd_dvd _ _).mpr
  intro p e hp hpd
  cases e with
  | zero => simp
  | succ e =>
    have h := Nat.le_of_dvd (Nat.totient_pos.mpr hd) (Nat.totient_dvd_of_dvd hpd)
    rw [Nat.totient_prime_pow_succ hp] at h
    apply Nat.dvd_factorial (pow_pos hp.pos _)
    rw [pow_succ]
    have hprime : p ≤ 2*(p-1) := by have := hp.two_le; omega
    have hmul := Nat.mul_le_mul_left (p^e) hprime
    nlinarith

private theorem count_bound (K N : ℕ) (hK : 0 < K) (hN : (2*K).factorial*K ≤ N) :
    zeroCount N ≤ N/K := by
  classical
  let g := fun d : ℕ => d*d.totient
  have hsub : (range (N+1)).filter zeroAt ⊆ (Icc 1 (N/K)).image g := by
    intro x hx
    obtain ⟨hx, d, hd, _, rfl⟩ := mem_filter.mp hx
    refine mem_image.mpr ⟨d,mem_Icc.mpr ⟨by omega,?_⟩,rfl⟩
    apply (Nat.le_div_iff_mul_le hK).mpr
    by_cases h : K ≤ d.totient
    · exact (Nat.mul_le_mul_left d h).trans (Nat.le_of_lt_succ (mem_range.mp hx))
    · exact (Nat.mul_le_mul_right K (small_totient (by omega) (by omega))).trans hN
  exact (card_le_card hsub).trans (card_image_le.trans (by simp))

theorem OMA.solution : type_of% @OMA.S_oeis_a396605.main := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨K,hK⟩ := exists_nat_gt (1/ε)
  have hkpos : (0:ℝ) < K := lt_trans (by positivity : 0<1/ε) hK
  have hkNat : 0 < K := by exact_mod_cast hkpos
  refine ⟨max 1 ((2*K).factorial*K), ?_⟩
  intro N hN
  have hnpos : (0:ℝ) < N := by exact_mod_cast (show 0<N by omega)
  have hb := count_bound K N hkNat (le_trans (le_max_right ..) hN)
  have hc : (zeroCount N:ℝ)*K ≤ N := by exact_mod_cast (Nat.le_div_iff_mul_le hkNat).mp hb
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (by positivity)]
  have hratio : (zeroCount N:ℝ)/N ≤ 1/K := by
    rw [div_le_div_iff₀ hnpos hkpos]; simpa using hc
  exact hratio.trans_lt ((div_lt_iff₀ hkpos).mpr (by
    have := (div_lt_iff₀ hε).mp hK
    linarith))
