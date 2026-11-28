import FormalConjectures.ErdosProblems.«292»
import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import Mathlib.NumberTheory.Chebyshev

/-! Clear the denominators below `p ^ k` using their least common multiple. -/

theorem OMA.solution : type_of% @Erdos292.erdos_292.variants.prime_pow := by
  rintro n ⟨s, hs, hn, hsum⟩ hpow
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp hpow
  simp only [one_div] at hsum
  let L := Nat.lcmUpto (p ^ k - 1)
  let q : ℚ := ∑ d ∈ s.erase (p ^ k), (d : ℚ)⁻¹
  have hL : q.den ∣ L := by
    apply (Finset.Rat.den_sum_dvd_lcm_den _ _).trans (Finset.lcm_dvd ?_)
    intro d hd
    obtain ⟨hne, hm⟩ := Finset.mem_erase.mp hd
    have ⟨hpos, hle⟩ := Finset.mem_Icc.mp (hs hm)
    rw [Rat.inv_natCast_den_of_pos hpos]
    exact Finset.dvd_lcm (f := id)
      (show d ∈ Finset.Icc 1 (p ^ k - 1) from Finset.mem_Icc.mpr ⟨hpos, by omega⟩)
  have heq : q = 1 - ((p ^ k : ℕ) : ℚ)⁻¹ := eq_sub_of_add_eq
    ((Finset.sum_erase_add s (fun d : ℕ => (d : ℚ)⁻¹) hn).trans hsum)
  have hdvd : p ^ k ∣ L := by
    rw [heq] at hL
    simpa [hp.ne_zero] using hL
  have hv := (hp.pow_dvd_iff_le_factorization (Nat.lcmUpto_ne_zero _)).mp hdvd
  rw [Nat.factorization_lcmUpto _ hp] at hv
  exact (Nat.log_lt_of_lt_pow' hk.ne' (Nat.sub_lt (pow_pos hp.pos _) one_pos)).not_ge hv
