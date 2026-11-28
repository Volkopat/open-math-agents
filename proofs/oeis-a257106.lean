import OMAStatements.S_oeis_a257106
import Mathlib

open OMA.S_oeis_a257106

namespace P257106

open Finset

theorem SL (x : ℚ) (p : ℕ) (hp : p.Prime) (hx : ¬ p ∣ x.den) (r : ℤ) (hr : ¬ (p : ℤ) ∣ r) :
    (x + r / p).den = x.den * p := by
  have hd : (x.den : ℚ) ≠ 0 := by positivity
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have e : x + r / p = ((x.num * p + r * x.den : ℤ) : ℚ) / ((x.den * p : ℤ) : ℚ) := by
    conv_lhs => rw [← Rat.num_div_den x]
    push_cast
    field_simp
  rw [e]
  have hb : (0 : ℤ) < x.den * p := by
    have := hp.pos; have := x.den_pos; positivity
  have hpi : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have c1 : IsCoprime x.num (x.den : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]; exact x.reduced
  have c2 : IsCoprime (p : ℤ) (x.den : ℤ) := by
    rw [Nat.isCoprime_iff_coprime]; exact (Nat.Prime.coprime_iff_not_dvd hp).mpr hx
  have c3 : IsCoprime r (p : ℤ) := ((Prime.coprime_iff_not_dvd hpi).mpr hr).symm
  have h1 : IsCoprime (x.num * p + r * x.den) (x.den : ℤ) :=
    (IsCoprime.mul_left c1 c2).add_mul_right_left r
  have h2 : IsCoprime (x.num * p + r * x.den) (p : ℤ) := by
    rw [add_comm]
    exact (IsCoprime.mul_left c3 c2.symm).add_mul_right_left x.num
  have h := IsCoprime.mul_right h1 h2
  have := Rat.den_div_eq_of_coprime hb (Int.isCoprime_iff_gcd_eq_one.mp h)
  exact_mod_cast this

theorem glem (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (z : ℤ) (r : ℕ → ℤ)
    (hr : ∀ p ∈ P, ¬ (p : ℤ) ∣ r p) :
    ((z : ℚ) + ∑ p ∈ P, (r p : ℚ) / p).den = ∏ p ∈ P, p := by
  induction P using Finset.induction_on with
  | empty => simp
  | insert q P hq ih =>
    have ih' := ih (fun p hp => hP p (mem_insert_of_mem hp)) (fun p hp => hr p (mem_insert_of_mem hp))
    have hqp := hP q (mem_insert_self q P)
    have hnd : ¬ q ∣ ((z : ℚ) + ∑ p ∈ P, (r p : ℚ) / p).den := by
      rw [ih']
      intro hd
      obtain ⟨p, hp, hqp'⟩ := (Prime.dvd_finsetProd_iff (Nat.prime_iff.mp hqp) _).mp hd
      have := (Nat.prime_dvd_prime_iff_eq hqp (hP p (mem_insert_of_mem hp))).mp hqp'
      exact hq (this ▸ hp)
    rw [sum_insert hq, prod_insert hq, add_left_comm, add_comm,
      SL _ q hqp hnd (r q) (hr q (mem_insert_self q P)), ih', mul_comm]

theorem b_eq (k : ℕ) : b k = bernoulli k + (if k = 1 then 7 / 6 else 0) := by
  unfold b
  split_ifs with h
  · subst h; rw [bernoulli_one]; norm_num
  · simp

theorem sum_B (n : ℕ) : ∑ k ∈ range (n + 1), (-1 : ℚ) ^ (n - k) * (n.choose k : ℚ) * bernoulli k =
    bernoulli n - (n : ℚ) * (-1 : ℚ) ^ (n - 1) := by
  have h := Polynomial.bernoulli_eval_one_add n (-1)
  rw [show (1 : ℚ) + -1 = 0 by norm_num, Polynomial.bernoulli_eval_zero] at h
  have h2 : (Polynomial.bernoulli n).eval (-1) =
      ∑ k ∈ range (n + 1), (-1 : ℚ) ^ (n - k) * (n.choose k : ℚ) * bernoulli k := by
    rw [Polynomial.bernoulli, Polynomial.eval_finsetSum]
    refine sum_congr rfl fun k _ => ?_
    rw [Polynomial.eval_monomial]
    ring
  rw [← h2]
  linear_combination -h

theorem sum_corr (n : ℕ) :
    ∑ k ∈ range (n + 1), (-1 : ℚ) ^ (n - k) * (n.choose k : ℚ) * (if k = 1 then 7 / 6 else 0) =
      if n = 0 then (0 : ℚ) else (7 / 6 : ℚ) * (n : ℚ) * (-1 : ℚ) ^ (n - 1) := by
  rcases n with _ | n
  · simp
  · rw [if_neg (by omega), Finset.sum_eq_single 1 (fun k _ hk => by simp [hk]) (by simp)]
    simp only [if_true, Nat.choose_one_right]
    push_cast
    ring

theorem c_eq (n : ℕ) : c n = bernoulli n - (n : ℚ) * (-1 : ℚ) ^ (n - 1) +
    (if n = 0 then (0 : ℚ) else (7 / 6 : ℚ) * (n : ℚ) * (-1 : ℚ) ^ (n - 1)) := by
  unfold c
  simp_rw [b_eq, mul_add, sum_add_distrib, sum_B, sum_corr]

theorem c_odd (m : ℕ) : c (2 * m + 1) = bernoulli (2 * m + 1) + (2 * m + 1) / 6 := by
  rw [c_eq, if_neg (by omega), Nat.add_sub_cancel, pow_mul]
  norm_num
  ring

theorem c_even (m : ℕ) (hm : 1 ≤ m) : c (2 * m) = bernoulli (2 * m) - m / 3 := by
  rw [c_eq, if_neg (by omega), show 2 * m - 1 = 2 * (m - 1) + 1 by omega, pow_succ, pow_mul]
  norm_num
  ring

theorem den_of (x : ℤ) (y : ℕ) (hy : 0 < y) (h : Nat.Coprime x.natAbs y) :
    ((x : ℚ) / y).den = y := by
  have := Rat.den_div_eq_of_coprime (a := x) (b := y) (by exact_mod_cast hy) (by simpa using h)
  exact_mod_cast this

theorem conj1 (n : ℕ) : a (2 * n + 1) = if n = 0 then 3 else if n % 3 = 1 then 2 else 6 := by
  unfold a
  rw [c_odd]
  rcases n with _ | n
  · rw [if_pos rfl, bernoulli_one]
    have : (-1 / 2 + (2 * ((0 : ℕ) : ℚ) + 1) / 6 : ℚ) = ((-1 : ℤ) : ℚ) / (3 : ℕ) := by norm_num
    rw [this, den_of _ _ (by norm_num) (by norm_num)]
  · rw [if_neg (by omega), bernoulli_eq_zero_of_odd ⟨n + 1, by ring⟩ (by omega), zero_add]
    split_ifs with h
    · obtain ⟨j, hj⟩ : ∃ j, n + 1 = 3 * j + 1 := ⟨(n + 1) / 3, by omega⟩
      have : (2 * ((n + 1 : ℕ) : ℚ) + 1) / 6 = ((2 * j + 1 : ℕ) : ℤ) / (2 : ℕ) := by
        rw [hj]; push_cast; ring
      rw [this, den_of _ _ (by norm_num)]
      rw [Int.natAbs_natCast, Nat.coprime_two_right]
      exact ⟨j, rfl⟩
    · have : (2 * ((n + 1 : ℕ) : ℚ) + 1) / 6 = ((2 * (n + 1) + 1 : ℕ) : ℤ) / (6 : ℕ) := by
        push_cast; ring
      rw [this, den_of _ _ (by norm_num)]
      rw [Int.natAbs_natCast, show (6 : ℕ) = 2 * 3 by rfl]
      apply Nat.Coprime.mul_right
      · rw [Nat.coprime_two_right]; exact ⟨n + 1, rfl⟩
      · exact (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (by omega)))

theorem not_dvd_neg_one (p : ℕ) (hp : p.Prime) : ¬ (p : ℤ) ∣ -1 := by
  intro h
  rw [Int.dvd_neg] at h
  have : p ∣ 1 := by exact_mod_cast h
  exact hp.one_lt.ne' (Nat.dvd_one.mp this)

def r3 (n p : ℕ) : ℤ := if p = 3 then -((n : ℤ) + 1) else -1

theorem conj2 (n : ℕ) :
    (a (2 * n) : ℚ) = (A002445 n : ℚ) / (if n % 3 = 2 then 3 else 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [a, A002445, c, b]
  set VS := (range (2 * n + 2)).filter fun p => p.Prime ∧ (p - 1) ∣ 2 * n with hVS
  obtain ⟨z, hz⟩ := Bernoulli.vonStaudt_clausen n
  rw [← hVS] at hz
  have hprime : ∀ p ∈ VS, p.Prime := fun p hp => (mem_filter.mp hp).2.1
  have h3 : 3 ∈ VS := by
    rw [hVS, mem_filter, mem_range]
    exact ⟨by omega, Nat.prime_three, ⟨n, by omega⟩⟩
  have hB : bernoulli (2 * n) = (z : ℚ) + ∑ p ∈ VS, ((-1 : ℤ) : ℚ) / p := by
    rw [hz]; simp only [Int.cast_neg, Int.cast_one, neg_div, sum_neg_distrib]; ring
  have hden : A002445 n = ∏ p ∈ VS, p := by
    unfold A002445
    rw [hB]
    exact glem VS hprime z (fun _ => -1) (fun p hp => not_dvd_neg_one p (hprime p hp))
  have hsplit : ∑ p ∈ VS, ((-1 : ℤ) : ℚ) / p = -1 / 3 + ∑ p ∈ VS.erase 3, ((-1 : ℤ) : ℚ) / p := by
    rw [← add_sum_erase VS _ h3]; push_cast; ring
  have hc : c (2 * n) = (z : ℚ) - (n + 1) / 3 + ∑ p ∈ VS.erase 3, ((-1 : ℤ) : ℚ) / p := by
    rw [c_even n hn, hB, hsplit]; ring
  unfold a
  have hprod := Finset.mul_prod_erase VS (fun p => p) h3
  split_ifs with h
  · obtain ⟨t, ht⟩ : ∃ t, n + 1 = 3 * t := ⟨(n + 1) / 3, by omega⟩
    have hc' : c (2 * n) = ((z - t : ℤ) : ℚ) + ∑ p ∈ VS.erase 3, ((-1 : ℤ) : ℚ) / p := by
      rw [hc]; push_cast
      rw [show ((n : ℚ) + 1) = 3 * t by exact_mod_cast ht]; ring
    rw [hc', glem (VS.erase 3) (fun p hp => hprime p (mem_of_mem_erase hp)) (z - t) (fun _ => -1)
      (fun p hp => not_dvd_neg_one p (hprime p (mem_of_mem_erase hp))), hden, ← hprod]
    push_cast
    ring
  · have hc' : c (2 * n) = (z : ℚ) + ∑ p ∈ VS, (r3 n p : ℚ) / p := by
      rw [hc, ← add_sum_erase VS _ h3]
      have : ∀ p ∈ VS.erase 3, (r3 n p : ℚ) / p = ((-1 : ℤ) : ℚ) / p := by
        intro p hp
        rw [r3, if_neg (ne_of_mem_erase hp)]
      rw [sum_congr rfl this, r3, if_pos rfl]
      push_cast; ring
    rw [hc', glem VS hprime z (r3 n), hden]
    · simp
    · intro p hp
      rw [r3]
      split_ifs with hp3
      · subst hp3
        intro hd
        rw [Int.dvd_neg] at hd
        have : 3 ∣ n + 1 := by exact_mod_cast hd
        omega
      · exact not_dvd_neg_one p (hprime p hp)

end P257106

theorem OMA.solution : type_of% @OMA.S_oeis_a257106.main :=
  ⟨P257106.conj1, P257106.conj2⟩
