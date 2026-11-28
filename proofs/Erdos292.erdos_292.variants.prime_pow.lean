import FormalConjectures.ErdosProblems.«292»
import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import Mathlib.NumberTheory.Chebyshev

/-! Denominators strictly below `p ^ k` have LCM indivisible by `p ^ k`. -/

open Finset in
theorem OMA.solution : type_of% @Erdos292.erdos_292.variants.prime_pow := by
  rintro n ⟨s, hs, hn, hsum⟩ hw
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).1 hw
  simp only [one_div] at hsum
  have hL : (1 - ((p ^ k : ℕ) : ℚ)⁻¹).den ∣ (p ^ k - 1).lcmUpto := by
    rw [← eq_sub_of_add_eq ((sum_erase_add s (fun d : ℕ => (d : ℚ)⁻¹) hn).trans hsum)]
    refine (Finset.Rat.den_sum_dvd_lcm_den _ _).trans (lcm_dvd fun d hd => ?_)
    obtain ⟨_, hm⟩ := mem_erase.1 hd
    obtain ⟨h0, _⟩ := mem_Icc.1 (hs hm)
    rw [Rat.inv_natCast_den_of_pos h0]
    exact dvd_lcm (f := id) (mem_Icc.2 ⟨h0, by omega⟩)
  have hv := (hp.pow_dvd_iff_le_factorization (Nat.lcmUpto_ne_zero _)).1
    (by simpa [hp.ne_zero] using hL)
  rw [Nat.factorization_lcmUpto _ hp] at hv
  exact (Nat.log_lt_of_lt_pow' hk.ne' (Nat.sub_lt (pow_pos hp.pos _) one_pos)).not_ge hv
