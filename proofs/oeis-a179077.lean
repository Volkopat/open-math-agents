import OMAStatements.S_oeis_a179077
import Mathlib

/-!
# Proof for OEIS A179077, conjecture of Felix Fröhlich (Sep 13 2019)

Claim: for `p = prime(n)`, `a(n) = ((2^p - 2)/p) mod p` is the residue modulo `p` of the Genocchi number
`G(p-1)` (A036968, e.g.f. `2x/(exp x + 1)`).

This is a corollary of the von Staudt-Clausen theorem (`Bernoulli.vonStaudt_clausen` in Mathlib).

1. In the rational power series, `T = 2 B(x) - 2 B(2x)` with `B` the e.g.f. of the Bernoulli numbers
   satisfies `T * (exp x + 1) * (exp x - 1) = 2x * (exp x - 1)`, by `B(x) * (exp x - 1) = x`, its rescaling
   by `2` and `exp(2x) = (exp x)^2`. Hence `2x/(exp x + 1) = T` and `G(n) = 2 (1 - 2^n) B(n)`.
2. `p = 2`: `G(1) = 1` and `a(1) = 1`.
3. `p = 2k + 1` odd. von Staudt-Clausen: `B(2k) + Sum_{q in S} 1/q = N` is an integer, where `S` is the
   set of primes `q` with `(q - 1) | 2k`; `p` belongs to `S`. Write `2^(2k) - 1 = p * m` (Fermat). Then
   `G(2k) = -2 p m N + 2 m + Sum_{q in S, q != p} 2 (2^(2k) - 1)/q`, and `2 m = (2^p - 2)/p`.
4. For `q` in `S`, `q != p`: `q` divides `2 (2^(2k) - 1) = p * (2 m)` (trivially for `q = 2`, by Fermat
   and `(q - 1) | 2k` otherwise) and `q` does not divide `p`, so `q | 2 m` and the term is `p * (2m/q)`.
5. So `G(p-1) = (2^p - 2)/p + c * p` with an integer `c`: `G(p-1)` is an integer with the residue `a(n)`.
-/

namespace A179077Proof

open OMA.S_oeis_a179077 PowerSeries

/-- `2x/(exp x + 1) = 2 B(x) - 2 B(2x)`, where `B` is the e.g.f. of the Bernoulli numbers. -/
private lemma egf_eq :
    (2 * X * (exp ℚ + 1)⁻¹ : PowerSeries ℚ) =
      2 * bernoulliPowerSeries ℚ - 2 * rescale (2 : ℚ) (bernoulliPowerSeries ℚ) := by
  have h1 : bernoulliPowerSeries ℚ * (exp ℚ - 1) = X := bernoulliPowerSeries_mul_exp_sub_one ℚ
  have h3 : rescale (2 : ℚ) (exp ℚ) = exp ℚ ^ 2 := by
    have h := exp_pow_eq_rescale_exp (A := ℚ) 2
    rw [h]
    norm_num
  have h2 : rescale (2 : ℚ) (bernoulliPowerSeries ℚ) * (exp ℚ ^ 2 - 1) = 2 * X := by
    have h := congrArg (rescale (2 : ℚ)) h1
    rw [map_mul, map_sub, map_one, h3, rescale_X] at h
    rw [h, show (2 : ℚ) = 1 + 1 by norm_num, map_add, map_one, one_add_one_eq_two]
  have hne : (exp ℚ - 1 : PowerSeries ℚ) ≠ 0 := by
    intro h
    have h' := congrArg (coeff 1) h
    simp [coeff_exp] at h'
  have hc : constantCoeff (exp ℚ + 1 : PowerSeries ℚ) ≠ 0 := by
    rw [map_add, constantCoeff_exp, map_one]
    norm_num
  have hT : (2 * bernoulliPowerSeries ℚ - 2 * rescale (2 : ℚ) (bernoulliPowerSeries ℚ)) *
      (exp ℚ + 1) = 2 * X := by
    apply mul_right_cancel₀ hne
    linear_combination 2 * (exp ℚ + 1) * h1 - 2 * h2
  rw [← hT, mul_assoc, PowerSeries.mul_inv_cancel _ hc, mul_one]

/-- The formula `G(n) = 2 (1 - 2^n) B(n)` of A036968. -/
private lemma genocchi_eq (n : ℕ) : genocchi n = 2 * (1 - 2 ^ n) * bernoulli n := by
  have hf : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have hcancel : (n.factorial : ℚ) * (bernoulli n / n.factorial) = bernoulli n := by
    field_simp
  unfold genocchi
  rw [egf_eq, map_sub, two_mul (bernoulliPowerSeries ℚ),
    two_mul (rescale (2 : ℚ) (bernoulliPowerSeries ℚ)), map_add, map_add, coeff_rescale]
  simp only [bernoulliPowerSeries, coeff_mk, Algebra.algebraMap_self_apply]
  linear_combination (2 - 2 * 2 ^ n) * hcancel

/-- Fermat for the base 2 and an exponent divisible by `q - 1`. -/
private lemma dvd_two_pow_sub_one {q j : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hj : (q - 1) ∣ j) :
    (q : ℤ) ∣ 2 ^ j - 1 := by
  obtain ⟨t, rfl⟩ := hj
  have hcop : IsCoprime (2 : ℤ) (q : ℤ) := by
    have h : Nat.Coprime 2 q := (Nat.coprime_primes Nat.prime_two hq).2 (Ne.symm hq2)
    exact_mod_cast Nat.isCoprime_iff_coprime.2 h
  have h := (Int.ModEq.pow_card_sub_one_eq_one hq hcop).pow t
  rw [one_pow, ← pow_mul] at h
  exact Int.modEq_iff_dvd.1 h.symm

/-- For an odd prime `p = 2k + 1`: `G(p-1) = (2^p - 2)/p + c * p` with an integer `c`. -/
private lemma odd_case (p k : ℕ) (hpk : p = 2 * k + 1) (hp : p.Prime) :
    ∃ c : ℤ, genocchi (2 * k) = ((((2 : ℤ) ^ p - 2) / (p : ℤ) + c * (p : ℤ) : ℤ) : ℚ) := by
  have hk : 0 < k := by
    have := hp.two_le
    omega
  have hp2 : p ≠ 2 := by omega
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  obtain ⟨m, hm⟩ : (p : ℤ) ∣ 2 ^ (2 * k) - 1 :=
    dvd_two_pow_sub_one hp hp2 (dvd_of_eq (by omega))
  have hquot : ((2 : ℤ) ^ p - 2) / (p : ℤ) = 2 * m := by
    have h2p : (2 : ℤ) ^ p = 2 ^ (2 * k) * 2 := by rw [hpk, pow_succ]
    have h : (2 : ℤ) ^ p - 2 = (p : ℤ) * (2 * m) := by
      rw [h2p]
      linear_combination 2 * hm
    rw [h, Int.mul_ediv_cancel_left _ (by exact_mod_cast hp.ne_zero)]
  have hmQ : ((2 : ℚ) ^ (2 * k) - 1) = (p : ℚ) * m := by exact_mod_cast hm
  obtain ⟨N, hN⟩ := Bernoulli.vonStaudt_clausen k
  generalize hS : (Finset.range (2 * k + 2)).filter (fun q => q.Prime ∧ (q - 1) ∣ 2 * k) = S at hN
  have hpS : p ∈ S := by
    rw [← hS, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hp, dvd_of_eq (by omega)⟩
  rw [← Finset.add_sum_erase S _ hpS] at hN
  have hterm : ∀ q ∈ S.erase p,
      ∃ c : ℤ, (2 * (2 ^ (2 * k) - 1) : ℚ) * (1 / (q : ℚ)) = (p : ℚ) * c := by
    intro q hq
    rw [Finset.mem_erase, ← hS, Finset.mem_filter] at hq
    obtain ⟨hqp, -, hqprime, hqdvd⟩ := hq
    have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hqprime.ne_zero
    have h1 : (q : ℤ) ∣ 2 * (2 ^ (2 * k) - 1) := by
      by_cases hq2 : q = 2
      · subst hq2
        exact ⟨2 ^ (2 * k) - 1, by simp⟩
      · exact Dvd.dvd.mul_left (dvd_two_pow_sub_one hqprime hq2 hqdvd) 2
    have h2 : (q : ℤ) ∣ 2 * m := by
      have h1' : (q : ℤ) ∣ (p : ℤ) * (2 * m) := by
        rw [hm] at h1
        convert h1 using 1
        ring
      have hqZ : Prime (q : ℤ) := Nat.prime_iff_prime_int.1 hqprime
      rcases hqZ.dvd_or_dvd h1' with h | h
      · exfalso
        have hdvd : q ∣ p := by exact_mod_cast h
        exact hqp ((Nat.prime_dvd_prime_iff_eq hqprime hp).1 hdvd)
      · exact h
    obtain ⟨t, ht⟩ := h2
    refine ⟨t, ?_⟩
    have htQ : (2 : ℚ) * m = (q : ℚ) * t := by exact_mod_cast ht
    rw [hmQ, mul_one_div, div_eq_iff hq0]
    linear_combination (p : ℚ) * htQ
  have hsum : ∃ c : ℤ,
      ∑ q ∈ S.erase p, (2 * (2 ^ (2 * k) - 1) : ℚ) * (1 / (q : ℚ)) = (p : ℚ) * c := by
    apply Finset.sum_induction _ (fun x : ℚ => ∃ c : ℤ, x = (p : ℚ) * c)
    · rintro x y ⟨c, rfl⟩ ⟨d, rfl⟩
      exact ⟨c + d, by push_cast; ring⟩
    · exact ⟨0, by simp⟩
    · exact hterm
  obtain ⟨c, hc⟩ := hsum
  rw [← Finset.mul_sum] at hc
  have hpinv : (p : ℚ) * (1 / (p : ℚ)) = 1 := by field_simp
  refine ⟨c - 2 * m * N, ?_⟩
  rw [genocchi_eq, hquot]
  push_cast
  linear_combination hc + (-2 * (N : ℚ) + 2 * (1 / (p : ℚ))) * hmQ + 2 * (m : ℚ) * hpinv
    - 2 * (1 - 2 ^ (2 * k)) * hN

end A179077Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a179077.main := by
  intro n _
  have hp : (OMA.S_oeis_a179077.prime n).Prime := Nat.prime_nth_prime _
  unfold OMA.S_oeis_a179077.a
  rcases hp.eq_two_or_odd' with h2 | ⟨k, hk⟩
  · refine ⟨1, ?_, ?_⟩
    · rw [h2, A179077Proof.genocchi_eq]
      norm_num [bernoulli_one]
    · rw [h2]
      norm_num
  · obtain ⟨c, hc⟩ := A179077Proof.odd_case _ k hk hp
    have hsub : OMA.S_oeis_a179077.prime n - 1 = 2 * k := by omega
    rw [hsub]
    exact ⟨_, hc.symm, (Int.add_mul_emod_self_right ..).symm⟩
