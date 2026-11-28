import OMAStatements.S_oeis_a307974
import Mathlib

namespace OMA.A307974Proof

open OMA.S_oeis_a307974

/-- `b` is `bernoulli'` plus the two swap corrections. -/
theorem b_eq : ∀ k : ℕ, b k = bernoulli' k + (if k = 0 then (-1 / 2 : ℚ) else 0) +
    (if k = 1 then (1 / 2 : ℚ) else 0)
  | 0 => by norm_num [b]
  | 1 => by norm_num [b]
  | k + 2 => by
      have h1 : k + 2 ≠ 1 := by omega
      simp [b, h1]

/-- Closed form: `t n = B_n - (-1)^n (n+1)/2` (with Mathlib's `bernoulli`, `B_1 = -1/2`). -/
theorem t_closed (n : ℕ) : t n = bernoulli n - (-1) ^ n * ((n : ℚ) + 1) / 2 := by
  have hmain : (∑ k ∈ Finset.range (n + 1), (-1 : ℚ) ^ (n - k) * (n.choose k : ℚ) * bernoulli' k)
      = (-1) ^ n * ((if n = 1 then (1 : ℚ) else 0) + bernoulli n) := by
    have hs : (∑ k ∈ Finset.range (n + 1), (n.choose k : ℚ) * bernoulli k)
        = (if n = 1 then (1 : ℚ) else 0) + bernoulli n := by
      rw [Finset.sum_range_succ, sum_bernoulli, Nat.choose_self, Nat.cast_one, one_mul]
    rw [← hs, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [bernoulli'_eq_bernoulli k]
    have hpow : (-1 : ℚ) ^ n = (-1) ^ (n - k) * (-1) ^ k := by
      rw [← pow_add, Nat.sub_add_cancel hk']
    rw [hpow]
    ring
  have h0 : (∑ k ∈ Finset.range (n + 1),
      (-1 : ℚ) ^ (n - k) * (n.choose k : ℚ) * (if k = 0 then (-1 / 2 : ℚ) else 0))
      = (-1) ^ n * (-1 / 2) := by
    rw [Finset.sum_eq_single 0]
    · simp
    · intro k _ hk
      simp [hk]
    · intro h
      exact absurd (Finset.mem_range.mpr (by omega)) h
  have h1 : (∑ k ∈ Finset.range (n + 1),
      (-1 : ℚ) ^ (n - k) * (n.choose k : ℚ) * (if k = 1 then (1 / 2 : ℚ) else 0))
      = if n = 0 then (0 : ℚ) else (-1) ^ (n - 1) * (n : ℚ) * (1 / 2) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [Finset.sum_eq_single 1]
      · simp [hn.ne']
      · intro k _ hk
        simp [hk]
      · intro h
        exact absurd (Finset.mem_range.mpr (by omega)) h
  have ht : t n =
      (∑ k ∈ Finset.range (n + 1), (-1 : ℚ) ^ (n - k) * (n.choose k : ℚ) * bernoulli' k) +
      (∑ k ∈ Finset.range (n + 1),
        (-1 : ℚ) ^ (n - k) * (n.choose k : ℚ) * (if k = 0 then (-1 / 2 : ℚ) else 0)) +
      (∑ k ∈ Finset.range (n + 1),
        (-1 : ℚ) ^ (n - k) * (n.choose k : ℚ) * (if k = 1 then (1 / 2 : ℚ) else 0)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    unfold t
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [b_eq k]
    ring
  rw [ht, hmain, h0, h1]
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n <;> norm_num
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    have hne : k + 2 ≠ 1 := by omega
    have hne0 : k + 2 ≠ 0 := by omega
    rw [if_neg hne, if_neg hne0, zero_add, show k + 2 - 1 = k + 1 by omega]
    have hb : (-1 : ℚ) ^ (k + 2) * bernoulli (k + 2) = bernoulli (k + 2) := by
      rw [← bernoulli'_eq_bernoulli, bernoulli_eq_bernoulli'_of_ne_one hne]
    rw [hb]
    push_cast
    ring

/-- The odd terms: `A307974 (2n+1) = n + 1`. -/
theorem odd_case (n : ℕ) : A307974 (2 * n + 1) = n + 1 := by
  unfold A307974
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h : t 1 = 1 / 2 := by
      rw [t_closed]
      norm_num
    rw [show 2 * 0 + 1 = 1 from rfl, h]
    norm_num
  · have ho : Odd (2 * n + 1) := ⟨n, rfl⟩
    have h : t (2 * n + 1) = (((n : ℤ) + 1 : ℤ) : ℚ) := by
      rw [t_closed, bernoulli_eq_zero_of_odd ho (by omega), ho.neg_one_pow]
      push_cast
      ring
    rw [h, Rat.num_intCast]

/-- The denominator of `c * q` is that of `q` when the integer `c` is coprime to it. -/
theorem den_aux (c : ℤ) (q : ℚ) (h : Nat.Coprime c.natAbs q.den) : ((c : ℚ) * q).den = q.den := by
  rw [Rat.mul_den, Rat.den_intCast, Rat.num_intCast, Int.natAbs_mul, one_mul,
    Nat.Coprime.gcd_eq_one (Nat.Coprime.mul_left h q.reduced), Nat.div_one]

/-- `2^(2n-1) = 2^(2n)/2` with an integer exponent. -/
theorem zpow_aux (n : ℕ) : (2 : ℚ) ^ ((2 * n : ℤ) - 1) = 2 ^ (2 * n) / 2 := by
  have e : (2 * n : ℤ) = ((2 * n : ℕ) : ℤ) := by omega
  rw [e, zpow_sub_one₀ (by norm_num : (2 : ℚ) ≠ 0), zpow_natCast]
  ring

/-- Fermat: an odd prime `p` with `(p - 1) ∣ 2m` does not divide `2^(2m) - 2`. -/
theorem fermat_aux (m p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hdvd : (p - 1) ∣ 2 * m) :
    ¬ (p : ℤ) ∣ (2 : ℤ) ^ (2 * m) - 2 := by
  have := Fact.mk hp
  intro hdiv
  have h0 : (((2 : ℤ) ^ (2 * m) - 2 : ℤ) : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdiv
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    have h3 := Nat.le_of_dvd (by norm_num) h'
    have h4 := hp.two_le
    omega
  have hferm : (2 : ZMod p) ^ (2 * m) = 1 := by
    obtain ⟨d, hd⟩ := hdvd
    rw [hd, pow_mul, ZMod.pow_card_sub_one_eq_one h2ne, one_pow]
  push_cast at h0
  rw [hferm] at h0
  have h1 : (1 : ZMod p) = 0 := by linear_combination -h0
  exact one_ne_zero h1

/-- The even terms, from von Staudt-Clausen: for `m ≥ 1`, `den (t (2m)) = A001897 m`. -/
theorem key (m : ℕ) (hm : 1 ≤ m) (P : Finset ℕ)
    (hV : (bernoulli (2 * m) + ∑ p ∈ P, (1 : ℚ) / p) ∈ Set.range (Int.cast : ℤ → ℚ))
    (hP : ∀ p ∈ P, p.Prime ∧ (p - 1) ∣ 2 * m) (h2 : 2 ∈ P) :
    (t (2 * m)).den = A001897 m := by
  obtain ⟨Z, hZ⟩ := Set.mem_range.mp hV
  obtain ⟨S, hS⟩ : ∃ S : ℚ, S = ∑ p ∈ P.erase 2, (1 : ℚ) / p := ⟨_, rfl⟩
  have hsplit : (∑ p ∈ P, (1 : ℚ) / p) = 1 / 2 + S := by
    rw [hS, ← Finset.add_sum_erase P (fun p : ℕ => (1 : ℚ) / p) h2]
    norm_num
  have hB : bernoulli (2 * m) = (Z : ℚ) - 1 / 2 - S := by
    rw [hsplit] at hZ
    linarith
  have hdvd : S.den ∣ ∏ p ∈ P.erase 2, p := by
    have h : (∑ p ∈ P.erase 2, (1 : ℚ) / p).den ∣ ∏ p ∈ P.erase 2, ((1 : ℚ) / p).den :=
      Finset.Rat.den_sum_dvd_prod_den _ _
    have hprod : ∏ p ∈ P.erase 2, ((1 : ℚ) / p).den = ∏ p ∈ P.erase 2, p := by
      refine Finset.prod_congr rfl fun p hp => ?_
      have hp0 : p ≠ 0 := (hP p (Finset.mem_of_mem_erase hp)).1.ne_zero
      simp [hp0]
    rw [hprod] at h
    rw [hS]
    exact h
  have hcop : Nat.Coprime ((2 : ℤ) ^ (2 * m) - 2).natAbs S.den := by
    have hprod : Nat.Coprime ((2 : ℤ) ^ (2 * m) - 2).natAbs (∏ p ∈ P.erase 2, p) := by
      apply Nat.Coprime.prod_right
      intro p hp
      obtain ⟨hp2, hpP⟩ := Finset.mem_erase.mp hp
      obtain ⟨hpr, hpd⟩ := hP p hpP
      show Nat.Coprime _ p
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hpr, ← Int.natCast_dvd]
      exact fermat_aux m p hpr hp2 hpd
    exact Nat.Coprime.coprime_dvd_right hdvd hprod
  have ht : t (2 * m) = ((Z - m - 1 : ℤ) : ℚ) - S := by
    rw [t_closed, hB, (even_two_mul m).neg_one_pow]
    push_cast
    ring
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hA : -2 * ((2 : ℚ) ^ ((2 * ((k + 1 : ℕ) : ℤ)) - 1) - 1) * bernoulli (2 * (k + 1))
      = ((-((2 : ℤ) ^ (2 * (k + 1)) - 2) * Z + 2 * 2 ^ (2 * k) - 1 : ℤ) : ℚ)
        + (((2 : ℤ) ^ (2 * (k + 1)) - 2 : ℤ) : ℚ) * S := by
    rw [zpow_aux, hB]
    push_cast
    ring
  unfold A001897
  rw [hA, Rat.intCast_add_den, den_aux _ _ hcop, ht, Rat.intCast_sub_den]

end OMA.A307974Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a307974.main := by
  refine ⟨fun n => OMA.A307974Proof.odd_case n, fun n hn => ?_⟩
  exact OMA.A307974Proof.key n hn _ (Bernoulli.vonStaudt_clausen n)
    (fun p hp => (Finset.mem_filter.mp hp).2)
    (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), Nat.prime_two, by norm_num⟩)
