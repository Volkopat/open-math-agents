import OMAStatements.S_oeis_a385478

namespace OMA.S_oeis_a385478

private def sigmaFast (n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors, ∑ j ∈ Finset.range (n.factorization p + 1), p ^ j

private theorem sigma_eq_fast {n : ℕ} (hn : 0 < n) : sigma n = sigmaFast n := by
  simpa only [sigma, sigmaFast, ArithmeticFunction.sigma_apply, pow_one, Nat.mul_one] using
    ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul (k := 1) hn.ne'

private theorem sigma_witness : sigma 1787 = 1788 := by
  rw [sigma, (by norm_num : Nat.Prime 1787).divisors]
  norm_num

private theorem sigma_earlier : sigma 1489 = 1490 := by
  rw [sigma, (by norm_num : Nat.Prime 1489).divisors]
  norm_num

-- Only the exponent-one case can contribute a multiple of 149.
private theorem first_power_cases :
    ∀ q : Fin 12, (149 * q.val - 1).Prime → 149 * q.val - 1 = 1489 := by
  decide +kernel

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1000000 in
private theorem higher_power_cases :
    ∀ (p : Fin 43) (e : Fin 11), p.val.Prime → 2 ≤ e.val → p.val ^ e.val < 1787 →
      ¬ 149 ∣ ∑ j ∈ Finset.range (e.val + 1), p.val ^ j := by
  decide +kernel

private theorem only_prior_multiple (k : ℕ) (hk : 0 < k) (hlt : k < 1787)
    (hd : 149 ∣ sigma k) : k = 1489 := by
  rw [sigma_eq_fast hk, sigmaFast] at hd
  have h149 : Nat.Prime 149 := by decide
  obtain ⟨p, hp, hsum⟩ := (h149.prime.dvd_finsetProd_iff _).mp hd
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hpd := Nat.dvd_of_mem_primeFactors hp
  let e := k.factorization p
  have hpos : 0 < e := hprime.factorization_pos_of_dvd hk.ne' hpd
  have hpow : p ^ e < 1787 := (Nat.le_of_dvd hk (Nat.ordProj_dvd k p)).trans_lt hlt
  change 149 ∣ ∑ j ∈ Finset.range (e + 1), p ^ j at hsum
  by_cases he : e = 1
  · have hpSum : 149 ∣ p + 1 := by
      simpa [he, Finset.sum_range_succ, add_comm] using hsum
    obtain ⟨q, hq⟩ := hpSum
    have hpBound := Nat.le_of_dvd hk hpd
    have hqBound : q < 12 := by omega
    have hpEq : 149 * q - 1 = p := by omega
    have heq := first_power_cases ⟨q, hqBound⟩ (hpEq ▸ hprime)
    have hpVal : p = 1489 := hpEq.symm.trans heq
    rw [hpVal] at hpd
    obtain ⟨v, hv⟩ := hpd
    omega
  · have he₂ : 2 ≤ e := by omega
    have hpSmall : p < 43 := by
      by_contra! h
      have hsq : 43 ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left h _
      have hmon := Nat.pow_le_pow_right hprime.pos he₂
      omega
    have heSmall : e < 11 := by
      by_contra! h
      have hbase : 2 ^ e ≤ p ^ e := Nat.pow_le_pow_left hprime.two_le _
      have hpow₂ : (2 : ℕ) ^ 11 ≤ 2 ^ e := Nat.pow_le_pow_right (by decide) h
      omega
    exact (higher_power_cases ⟨p, hpSmall⟩ ⟨e, heSmall⟩ hprime he₂ hpow hsum).elim

private theorem mem_fresh_iff {d n : ℕ} :
    d ∈ freshDivisors n ↔ d ∈ (sigma n).divisors ∧ ∀ k ∈ Finset.Ico 1 n, ¬ d ∣ sigma k := by
  unfold freshDivisors
  exact @Finset.mem_filter ℕ _ (fun _ => Classical.propDecidable _) _ _

private theorem fresh_witness (d : ℕ) (hnew : d ∣ 1788) (hmul : 149 ∣ d)
    (hold : ¬ d ∣ 1490) : d ∈ freshDivisors 1787 := by
  have hin : d ∈ (sigma 1787).divisors := by
    rw [sigma_witness]
    exact Nat.mem_divisors.mpr ⟨hnew, by decide⟩
  refine mem_fresh_iff.mpr ⟨hin, ?_⟩
  intro k hk hd
  obtain ⟨hk₁, hk₂⟩ := Finset.mem_Ico.mp hk
  have he : k = 1489 := only_prior_multiple k hk₁ hk₂ (hmul.trans hd)
  exact hold (by simpa only [he, sigma_earlier] using hd)

end OMA.S_oeis_a385478

open OMA.S_oeis_a385478 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a385478.main) := by
  classical
  intro h
  have h₁ : 447 ∈ freshDivisors 1787 := fresh_witness 447 (by decide) (by decide) (by decide)
  have h₂ : 596 ∈ freshDivisors 1787 := fresh_witness 596 (by decide) (by decide) (by decide)
  have hne : (freshDivisors 1787).Nonempty := ⟨447, h₁⟩
  have hm : term 1787 ∈ freshDivisors 1787 := by
    unfold term
    rw [dif_pos hne]
    exact Finset.min'_mem _ _
  have hd : term 1787 ∣ 149 :=
    Nat.dvd_gcd (h 1787 (by decide) 447 h₁) (h 1787 (by decide) 596 h₂)
  exact (mem_fresh_iff.mp hm).2 1489 (Finset.mem_Ico.mpr ⟨by decide, by decide⟩)
    (hd.trans (by rw [sigma_earlier]; decide : 149 ∣ sigma 1489))
