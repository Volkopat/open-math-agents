import OMAStatements.S_oeis_a179875
import Mathlib

open scoped BigOperators
open Finset

namespace OMA.ResidueMeans

open OMA.S_oeis_a179875
open UniqueFactorizationMonoid

private abbrev mu (n : ℕ) : ℚ := (ArithmeticFunction.moebius n : ℤ)

private theorem mu_sum (n : ℕ) :
    (∑ d ∈ n.divisors, mu d) = if n = 1 then 1 else 0 := by
  have h := congrFun (congrArg (fun f : ArithmeticFunction ℤ => (f : ℕ → ℤ))
    ArithmeticFunction.moebius_mul_coe_zeta) n
  rw [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
  exact_mod_cast h

private theorem coprime_indicator {n : ℕ} (hn : n ≠ 0) (x : ℕ) :
    (if x.Coprime n then (1 : ℚ) else 0) =
      ∑ d ∈ n.divisors.filter (fun d => d ∣ x), mu d := by
  have hg : n.divisors.filter (fun d => d ∣ x) = (x.gcd n).divisors := by
    ext d
    have hne : x.gcd n ≠ 0 := Nat.gcd_ne_zero_right hn
    simp only [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
    tauto
  rw [hg, mu_sum]

private theorem multiples {n d : ℕ} (hd : 0 < d) (f : ℕ → ℚ) :
    (∑ x ∈ (Finset.Icc 1 n).filter (fun x => d ∣ x), f x) =
      ∑ j ∈ Finset.Icc 1 (n / d), f (d * j) := by
  symm
  refine Finset.sum_nbij (fun j => d * j) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro j hj
    have h := Finset.mem_Icc.mp hj
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, dvd_mul_right _ _⟩
    · exact Nat.succ_le_of_lt (Nat.mul_pos hd (by omega))
    · simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hd).mp h.2
  · intro a ha b hb he
    exact Nat.eq_of_mul_eq_mul_left hd he
  · intro x hx
    obtain ⟨hx, ⟨j, h⟩⟩ := Finset.mem_filter.mp hx
    have hx' := Finset.mem_Icc.mp hx
    rw [h] at hx'
    refine ⟨j, Finset.mem_Icc.mpr ⟨?_, ?_⟩, h.symm⟩
    · by_contra! hj
      have hj0 : j = 0 := by omega
      simp [hj0] at hx'
    · apply (Nat.le_div_iff_mul_le hd).mpr
      simpa [Nat.mul_comm] using hx'.2

private theorem mob_power {n : ℕ} (hn : n ≠ 0) (e : ℕ) :
    (∑ x ∈ residues n, (x : ℚ)^e) =
      ∑ d ∈ n.divisors, mu d * (d : ℚ)^e * (∑ j ∈ Finset.Icc 1 (n / d), (j : ℚ)^e) := by
  classical
  calc
    _ = ∑ x ∈ Finset.Icc 1 n,
        (x : ℚ)^e * ∑ d ∈ n.divisors, if d ∣ x then mu d else 0 := by
      rw [residues, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro x _
      rw [← Finset.sum_filter, ← coprime_indicator hn x]
      split <;> simp
    _ = ∑ d ∈ n.divisors, mu d * ∑ x ∈ (Finset.Icc 1 n).filter (fun x => d ∣ x),
        (x : ℚ)^e := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d _
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro x _
      split <;> simp [mul_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hd
      have hdp : 0 < d := Nat.pos_of_mem_divisors hd
      rw [multiples hdp, mul_assoc]
      congr 1
      rw [Finset.mul_sum]
      simp only [Nat.cast_mul, mul_pow]

private theorem residues_card {n : ℕ} (hn : 1 < n) : (residues n).card = n.totient := by
  unfold residues Nat.totient
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
  rw [Nat.coprime_comm (m := n) (n := x)]
  constructor
  · rintro ⟨⟨hx, hle⟩, hcop⟩
    have h : x ≠ n := by
      intro h
      subst x
      have he : n = 1 := by simpa using hcop
      omega
    exact ⟨by omega, hcop⟩
  · rintro ⟨hlt, hcop⟩
    have hx : x ≠ 0 := by
      intro h
      subst x
      have he : n = 1 := by simpa using hcop
      omega
    exact ⟨⟨by omega, hlt.le⟩, hcop⟩

private theorem mu_totient {n : ℕ} (hn : 1 < n) :
    (∑ d ∈ n.divisors, mu d * ((n / d : ℕ) : ℚ)) = (n.totient : ℚ) := by
  have h := mob_power (n := n) (by omega) 0
  simpa [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc, residues_card hn] using h.symm

private theorem range_sum (q : ℕ) :
    (∑ j ∈ Finset.Icc 1 q, (j : ℚ)) = (q : ℚ) * (q + 1) / 2 := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    push_cast
    ring

private theorem range_squares (q : ℕ) :
    (∑ j ∈ Finset.Icc 1 q, (j : ℚ)^2) = (q : ℚ) * (q + 1) * (2 * q + 1) / 6 := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    push_cast
    ring

private theorem mul_quotient {n d : ℕ} (hd : d ∈ n.divisors) :
    (d : ℚ) * ((n / d : ℕ) : ℚ) = n := by
  exact_mod_cast Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)

private theorem first_moment {n : ℕ} (hn : 1 < n) :
    (∑ x ∈ residues n, (x : ℚ)) = (n : ℚ) * n.totient / 2 := by
  have h := mob_power (n := n) (by omega) 1
  simp only [pow_one, range_sum] at h
  calc
    _ = _ := h
    _ = ∑ d ∈ n.divisors, (n : ℚ)/2 * (mu d * ((n/d : ℕ) : ℚ) + mu d) := by
      apply Finset.sum_congr rfl
      intro d hd
      have hc := mul_quotient hd
      linear_combination (mu d * (((n/d : ℕ) : ℚ)+1) / 2) * hc
    _ = _ := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib, mu_totient hn, mu_sum, if_neg (by omega)]
      ring

private theorem second_moment {n : ℕ} (hn : 1 < n) :
    (∑ x ∈ residues n, (x : ℚ)^2) =
      (n : ℚ)^2 * n.totient / 3 + (n : ℚ)/6 * ∑ d ∈ n.divisors, mu d * (d : ℚ) := by
  calc
    _ = ∑ d ∈ n.divisors, mu d * (d : ℚ)^2 *
        (((n/d : ℕ) : ℚ) * (((n/d : ℕ) : ℚ)+1) * (2 * ((n/d : ℕ) : ℚ)+1) / 6) := by
      simpa only [range_squares] using mob_power (n := n) (by omega) 2
    _ = ∑ d ∈ n.divisors, ((n : ℚ)^2 / 3 * (mu d * ((n/d : ℕ) : ℚ))
        + (n : ℚ)^2/2 * mu d + (n : ℚ)/6 * (mu d * (d : ℚ))) := by
      apply Finset.sum_congr rfl
      intro d hd
      let q : ℚ := (n/d : ℕ)
      change mu d * (d : ℚ)^2 * (q * (q+1) * (2*q+1) / 6) =
        (n : ℚ)^2/3 * (mu d*q) + (n : ℚ)^2/2 * mu d + (n : ℚ)/6 * (mu d*(d : ℚ))
      have hq : (d : ℚ) * q = n := mul_quotient hd
      rw [← hq]
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        ← Finset.mul_sum, mu_totient hn, mu_sum, if_neg (by omega)]
      ring

private theorem weighted_mu {n : ℕ} (hn : n ≠ 0) :
    (∑ d ∈ n.divisors, mu d * (d : ℚ)) =
      mu (radical n) * (∏ p ∈ n.primeFactors, ((p-1 : ℕ) : ℚ)) := by
  have hsf : Squarefree (radical n) := squarefree_radical
  have hs : (radical n).divisors ⊆ n.divisors := Nat.divisors_subset_of_dvd hn radical_dvd_self
  have hsub : (∑ d ∈ (radical n).divisors, mu d * (d : ℚ)) =
      ∑ d ∈ n.divisors, mu d * (d : ℚ) := by
    apply Finset.sum_subset hs
    intro d hd hnot
    have hns : ¬Squarefree d := by
      intro h
      apply hnot
      exact Nat.mem_divisors.mpr
        ⟨(dvd_radical_iff h.isRadical hn).mpr (Nat.dvd_of_mem_divisors hd), hsf.ne_zero⟩
    simp [mu, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hns]
  rw [← hsub]
  let f : ArithmeticFunction ℚ := (ArithmeticFunction.id : ArithmeticFunction ℕ)
  have hp := (ArithmeticFunction.IsMultiplicative.prodPrimeFactors_one_sub_of_squarefree
    f ArithmeticFunction.isMultiplicative_id.natCast hsf).symm
  have he : (∑ d ∈ (radical n).divisors, mu d * (d : ℚ)) =
      ∏ p ∈ n.primeFactors, (1 - (p : ℚ)) := by
    simpa [f, Nat.primeFactors_radical] using hp
  have hl : ArithmeticFunction.cardFactors (radical n) = n.primeFactors.card := by
    rw [ArithmeticFunction.cardFactors_apply, ← Nat.primeFactors_radical n]
    exact (List.toFinset_card_of_nodup hsf.nodup_primeFactorsList).symm
  rw [he, show mu (radical n) = (-1 : ℚ)^n.primeFactors.card by
    simp only [mu, ArithmeticFunction.moebius_apply_of_squarefree hsf, hl,
      Int.cast_pow, Int.cast_neg, Int.cast_one]]
  rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_lt.le]
  ring

private noncomputable def correction (n : ℕ) : ℚ := mu (radical n) / ((n / radical n : ℕ) : ℚ)

private theorem quotient_pos {n : ℕ} (hn : 0 < n) : 0 < n / radical n :=
  Nat.div_pos (Nat.le_of_dvd hn radical_dvd_self) (Nat.radical_pos n)

private theorem mu_ratio {n : ℕ} (hn : 0 < n) :
    (∑ d ∈ n.divisors, mu d * (d : ℚ)) / (n.totient : ℚ) = correction n := by
  rw [weighted_mu hn.ne', Nat.totient_eq_div_primeFactors_mul, ← Nat.radical_eq_prod_primeFactors]
  unfold correction
  rw [Nat.cast_mul, Nat.cast_prod]
  have hp : (∏ p ∈ n.primeFactors, ((p-1 : ℕ) : ℚ)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro p he
    exact_mod_cast Nat.sub_ne_zero_of_lt (Nat.prime_of_mem_primeFactors he).one_lt
  have hq : ((n / radical n : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast (quotient_pos hn).ne'
  field_simp

private theorem mean_formula {n : ℕ} (hn : 1 < n) :
    mean n = (2*(n : ℚ) + correction n)/3 := by
  unfold mean
  rw [first_moment hn, second_moment hn, ← mu_ratio (by omega : 0 < n)]
  have ht : (n.totient : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (by omega : 0 < n)).ne'
  have hz : (n : ℚ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  field_simp
  ring

private theorem correction_range {n : ℕ} (hn : 0 < n) : -1 ≤ correction n ∧ correction n ≤ 1 := by
  have hq : (0 : ℚ) < ((n / radical n : ℕ) : ℚ) := by exact_mod_cast quotient_pos hn
  have hq1 : (1 : ℚ) ≤ ((n / radical n : ℕ) : ℚ) := by
    exact_mod_cast (quotient_pos hn)
  have hm : |mu (radical n)| ≤ 1 := by
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := radical n))
  unfold correction
  rw [le_div_iff₀ hq, div_le_iff₀ hq]
  have h := abs_le.mp hm
  constructor <;> linarith

private theorem correction_endpoint {n : ℕ} (hn : 0 < n) (z : ℤ) (hz : z = 1 ∨ z = -1) :
    correction n = (z : ℚ) ↔ ArithmeticFunction.moebius n = z := by
  have hq : (0 : ℚ) < ((n / radical n : ℕ) : ℚ) := by exact_mod_cast quotient_pos hn
  have hq1 : (1 : ℚ) ≤ ((n / radical n : ℕ) : ℚ) := by exact_mod_cast quotient_pos hn
  constructor
  · intro h
    have hc := (div_eq_iff hq.ne').mp h
    have hm : |mu (radical n)| ≤ 1 := by
      exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := radical n))
    have hzQ : |(z : ℚ)| = 1 := by rcases hz with h | h <;> norm_num [h]
    rw [hc, abs_mul, hzQ, one_mul, abs_of_nonneg hq.le] at hm
    have hqone := le_antisymm hm hq1
    have hnq : n / radical n = 1 := by exact_mod_cast hqone
    have hrad := Nat.mul_div_cancel' (radical_dvd_self (a := n))
    rw [hnq, mul_one] at hrad
    rw [hqone, mul_one, hrad] at hc
    exact_mod_cast hc
  · intro h
    have hmu : ArithmeticFunction.moebius n ≠ 0 := by
      rw [h]
      rcases hz with hz | hz <;> simp [hz]
    have hsf := ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hmu
    have hrad := Nat.dvd_antisymm radical_dvd_self (hsf.isRadical.dvd_radical hn.ne')
    simp [correction, mu, hrad, Nat.div_self hn, h]

theorem formula (k : ℕ) (hk : 0 < k) :
    (mean k = mean (k+1) ↔
      ArithmeticFunction.moebius k = 1 ∧ ArithmeticFunction.moebius (k+1) = -1) := by
  by_cases h : k = 1
  · subst k
    have he : mean 1 = mean 2 := by decide +kernel
    simp [he, ArithmeticFunction.moebius_apply_prime Nat.prime_two]
  have hk' : 1 < k := by omega
  rw [mean_formula hk', mean_formula (by omega : 1 < k+1)]
  push_cast
  constructor
  · intro he
    have hc := (correction_range hk).2
    have hd := (correction_range (by omega : 0 < k+1)).1
    have h1 : correction k = 1 := by linarith only [he, hc, hd]
    have h2 : correction (k+1) = -1 := by linarith only [he, hc, hd]
    exact ⟨(correction_endpoint hk 1 (Or.inl rfl)).mp (by simpa using h1),
      (correction_endpoint (by omega) (-1) (Or.inr rfl)).mp (by simpa using h2)⟩
  · rintro ⟨h1, h2⟩
    have ha := (correction_endpoint hk 1 (Or.inl rfl)).mpr h1
    have hb := (correction_endpoint (by omega) (-1) (Or.inr rfl)).mpr h2
    rw [ha, hb]
    push_cast
    ring

end OMA.ResidueMeans

theorem OMA.solution : type_of% @OMA.S_oeis_a179875.main := OMA.ResidueMeans.formula