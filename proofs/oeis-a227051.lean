import OMAStatements.S_oeis_a227051
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace OMA.P_oeis_a227051

open OMA.S_oeis_a227051

/-- Split a sum over `Finset.range (2 * n + 1)` into even and odd indices. -/
private lemma sum_range_two_mul_add_one {R : Type*} [AddCommMonoid R] (f : ℕ → R) (n : ℕ) :
    ∑ r ∈ Finset.range (2 * n + 1), f r =
      (∑ k ∈ Finset.range (n + 1), f (2 * k)) + (∑ j ∈ Finset.range n, f (2 * j + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : 2 * (n + 1) + 1 = (2 * n + 1) + 1 + 1 := by omega
    rw [h1, Finset.sum_range_succ, Finset.sum_range_succ, ih]
    rw [Finset.sum_range_succ (f := fun k => f (2 * k)) (n + 1),
      Finset.sum_range_succ (f := fun j => f (2 * j + 1)) n]
    have h2 : 2 * n + 1 + 1 = 2 * (n + 1) := by omega
    rw [h2]
    abel

/-- Even-index binomial sum identity: `2 * ∑_{k=0}^n C(2n, 2k) * t^(2k) = (1 + t)^(2n) + (1 - t)^(2n)`. -/
private lemma two_mul_sum_even_choose {R : Type*} [CommRing R] (t : R) (n : ℕ) :
    2 * ∑ k ∈ Finset.range (n + 1), (Nat.choose (2 * n) (2 * k) : R) * t ^ (2 * k) =
      (1 + t) ^ (2 * n) + (1 - t) ^ (2 * n) := by
  have hplus : (1 + t) ^ (2 * n) = ∑ r ∈ Finset.range (2 * n + 1), (Nat.choose (2 * n) r : R) * t ^ r := by
    rw [add_comm, add_pow]
    refine Finset.sum_congr rfl (fun r _ => by rw [one_pow, mul_one, mul_comm])
  have hminus : (1 - t) ^ (2 * n) = ∑ r ∈ Finset.range (2 * n + 1), (Nat.choose (2 * n) r : R) * (-t) ^ r := by
    rw [sub_eq_add_neg, add_comm, add_pow]
    refine Finset.sum_congr rfl (fun r _ => by rw [one_pow, mul_one, mul_comm])
  rw [hplus, hminus, sum_range_two_mul_add_one, sum_range_two_mul_add_one]
  have heven : ∑ k ∈ Finset.range (n + 1), (Nat.choose (2 * n) (2 * k) : R) * (-t) ^ (2 * k) =
      ∑ k ∈ Finset.range (n + 1), (Nat.choose (2 * n) (2 * k) : R) * t ^ (2 * k) := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Even.neg_pow ⟨k, by omega⟩]
  have hodd : ∑ j ∈ Finset.range n, (Nat.choose (2 * n) (2 * j + 1) : R) * (-t) ^ (2 * j + 1) =
      -(∑ j ∈ Finset.range n, (Nat.choose (2 * n) (2 * j + 1) : R) * t ^ (2 * j + 1)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Odd.neg_pow ⟨j, rfl⟩]
    ring
  rw [heven, hodd]
  ring

/-- Odd-index binomial sum identity: `2 * t * ∑_{j=0}^{n-1} C(2n, 2j+1) * (t^2)^j = (1 + t)^(2n) - (1 - t)^(2n)`. -/
private lemma two_mul_sum_odd_choose {R : Type*} [CommRing R] (t : R) (n : ℕ) :
    2 * t * ∑ j ∈ Finset.range n, (Nat.choose (2 * n) (2 * j + 1) : R) * (t ^ 2) ^ j =
      (1 + t) ^ (2 * n) - (1 - t) ^ (2 * n) := by
  have hplus : (1 + t) ^ (2 * n) = ∑ r ∈ Finset.range (2 * n + 1), (Nat.choose (2 * n) r : R) * t ^ r := by
    rw [add_comm, add_pow]
    refine Finset.sum_congr rfl (fun r _ => by rw [one_pow, mul_one, mul_comm])
  have hminus : (1 - t) ^ (2 * n) = ∑ r ∈ Finset.range (2 * n + 1), (Nat.choose (2 * n) r : R) * (-t) ^ r := by
    rw [sub_eq_add_neg, add_comm, add_pow]
    refine Finset.sum_congr rfl (fun r _ => by rw [one_pow, mul_one, mul_comm])
  rw [hplus, hminus, sum_range_two_mul_add_one, sum_range_two_mul_add_one]
  have heven : ∑ k ∈ Finset.range (n + 1), (Nat.choose (2 * n) (2 * k) : R) * (-t) ^ (2 * k) =
      ∑ k ∈ Finset.range (n + 1), (Nat.choose (2 * n) (2 * k) : R) * t ^ (2 * k) := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Even.neg_pow ⟨k, by omega⟩]
  have hodd : ∑ j ∈ Finset.range n, (Nat.choose (2 * n) (2 * j + 1) : R) * (-t) ^ (2 * j + 1) =
      -(∑ j ∈ Finset.range n, (Nat.choose (2 * n) (2 * j + 1) : R) * t ^ (2 * j + 1)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Odd.neg_pow ⟨j, rfl⟩]
    ring
  rw [heven, hodd, Finset.mul_sum]
  have hpow : ∑ j ∈ Finset.range n, 2 * t * ((Nat.choose (2 * n) (2 * j + 1) : R) * (t ^ 2) ^ j) =
      2 * ∑ j ∈ Finset.range n, (Nat.choose (2 * n) (2 * j + 1) : R) * t ^ (2 * j + 1) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← pow_mul, pow_succ]
    ring
  rw [hpow]
  ring

/-- In `ZMod 2`, `denomCoeff k = 1` for all `k`. -/
private lemma denomCoeff_mod2 (k : ℕ) : (denomCoeff k : ZMod 2) = 1 := by
  have heven : (2 : ℤ) ∣ ∑ j ∈ Finset.range k, (-1 : ℤ) ^ j * (Nat.choose (2 * k) (2 * j + 1) : ℤ) := by
    have hsum : ∑ j ∈ Finset.range k, (Nat.choose (2 * k) (2 * j + 1) : ℤ) =
        if k = 0 then 0 else 2 ^ (2 * k - 1) := by
      cases k with
      | zero => simp
      | succ m =>
        have h1 := two_mul_sum_odd_choose (R := ℤ) 1 (m + 1)
        simp only [one_pow, mul_one, sub_self, zero_pow (by omega : 2 * (m + 1) ≠ 0), sub_zero] at h1
        have h2 : (1 + 1 : ℤ) ^ (2 * (m + 1)) = 2 * 2 ^ (2 * (m + 1) - 1) := by
          have hexp : 2 * (m + 1) = (2 * (m + 1) - 1) + 1 := by omega
          conv_lhs => rw [hexp, pow_succ']
          norm_num
        rw [h2] at h1
        have h3 : ∑ j ∈ Finset.range (m + 1), (Nat.choose (2 * (m + 1)) (2 * j + 1) : ℤ) =
            2 ^ (2 * (m + 1) - 1) := by linarith
        simpa using h3
    have hmod2 : ((∑ j ∈ Finset.range k, (-1 : ℤ) ^ j * (Nat.choose (2 * k) (2 * j + 1) : ℤ) : ℤ) : ZMod 2) =
        ((∑ j ∈ Finset.range k, (Nat.choose (2 * k) (2 * j + 1) : ℤ) : ℤ) : ZMod 2) := by
      push_cast
      refine Finset.sum_congr rfl (fun j _ => ?_)
      have hneg1 : (-1 : ZMod 2) = 1 := by decide
      rw [hneg1, one_pow, one_mul]
    have hzero : ((∑ j ∈ Finset.range k, (Nat.choose (2 * k) (2 * j + 1) : ℤ) : ℤ) : ZMod 2) = 0 := by
      rw [hsum]
      cases k with
      | zero => simp
      | succ m =>
        simp only [Nat.succ_ne_zero, if_false]
        push_cast
        have h20 : (2 : ZMod 2) = 0 := by decide
        rw [h20, zero_pow (by omega)]
    rw [hzero] at hmod2
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp hmod2
  have hsub0 : ((∑ j ∈ Finset.range k, (-1 : ℤ) ^ j * (Nat.choose (2 * k) (2 * j + 1) : ℤ) : ℤ) : ZMod 2) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mpr heven
  simp only [denomCoeff, Int.cast_sub, Int.cast_pow, Int.cast_neg, Int.cast_one]
  rw [hsub0, sub_zero]
  have hneg1 : (-1 : ZMod 2) = 1 := by decide
  rw [hneg1, one_pow]

/-- In `ZMod 5`, `denomCoeff k = 2 * (-1)^k - 1` for all `k`. -/
private lemma denomCoeff_mod5 (k : ℕ) :
    (denomCoeff k : ZMod 5) = 2 * (-1 : ZMod 5) ^ k - 1 := by
  have hodd := two_mul_sum_odd_choose (R := ZMod 5) (2 : ZMod 5) k
  have h22 : (2 : ZMod 5) ^ 2 = -1 := by decide
  have h2t : (2 : ZMod 5) * 2 = -1 := by decide
  have h1p : (1 + (2 : ZMod 5)) ^ (2 * k) = (-1 : ZMod 5) ^ k := by
    rw [pow_mul]
    have hsq : (1 + (2 : ZMod 5)) ^ 2 = -1 := by decide
    rw [hsq]
  have h1m : (1 - (2 : ZMod 5)) ^ (2 * k) = 1 := by
    rw [pow_mul]
    have hsq : (1 - (2 : ZMod 5)) ^ 2 = 1 := by decide
    rw [hsq, one_pow]
  rw [h22, h2t, h1p, h1m] at hodd
  have hsum : ∑ j ∈ Finset.range k, (-1 : ZMod 5) ^ j * (Nat.choose (2 * k) (2 * j + 1) : ZMod 5) =
      1 - (-1 : ZMod 5) ^ k := by
    have hcomm : ∑ j ∈ Finset.range k, (-1 : ZMod 5) ^ j * (Nat.choose (2 * k) (2 * j + 1) : ZMod 5) =
        ∑ j ∈ Finset.range k, (Nat.choose (2 * k) (2 * j + 1) : ZMod 5) * (-1 : ZMod 5) ^ j :=
      Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
    rw [hcomm]
    linear_combination -hodd
  simp only [denomCoeff, Int.cast_sub, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_sum,
    Int.cast_mul, Int.cast_natCast]
  rw [hsum]
  ring

private lemma sum_even_choose_mod2 (n : ℕ) (hn : 1 ≤ n) :
    (∑ k ∈ Finset.range (n + 1), (Nat.choose (2 * n) (2 * k) : ZMod 2)) = 0 := by
  have h := two_mul_sum_even_choose (R := ℤ) 1 n
  simp only [one_pow, mul_one, sub_self, zero_pow (by omega : 2 * n ≠ 0), add_zero] at h
  have h2 : (1 + 1 : ℤ) ^ (2 * n) = 2 * 2 ^ (2 * n - 1) := by
    have hexp : 2 * n = (2 * n - 1) + 1 := by omega
    conv_lhs => rw [hexp, pow_succ']
    norm_num
  rw [h2] at h
  have hval : ∑ k ∈ Finset.range (n + 1), (Nat.choose (2 * n) (2 * k) : ℤ) = 2 ^ (2 * n - 1) := by
    linarith
  have hcast := congr_arg (Int.cast (R := ZMod 2)) hval
  push_cast at hcast
  rw [hcast]
  have h20 : (2 : ZMod 2) = 0 := by decide
  rw [h20, zero_pow (by omega)]

private lemma sum_even_choose_mod5 (n : ℕ) (hn : 1 ≤ n) :
    (∑ k ∈ Finset.range (n + 1), (Nat.choose (2 * n) (2 * k) : ZMod 5)) = 3 * (-1 : ZMod 5) ^ n := by
  have h := two_mul_sum_even_choose (R := ZMod 5) 1 n
  simp only [one_pow, mul_one, sub_self, zero_pow (by omega : 2 * n ≠ 0), add_zero] at h
  have hpow : (1 + (1 : ZMod 5)) ^ (2 * n) = (-1 : ZMod 5) ^ n := by
    rw [pow_mul]
    have hsq : (1 + (1 : ZMod 5)) ^ 2 = -1 := by decide
    rw [hsq]
  rw [hpow] at h
  have h32 : (3 : ZMod 5) * 2 = 1 := by decide
  calc ∑ k ∈ Finset.range (n + 1), (Nat.choose (2 * n) (2 * k) : ZMod 5)
      = (3 : ZMod 5) * (2 * ∑ k ∈ Finset.range (n + 1), (Nat.choose (2 * n) (2 * k) : ZMod 5)) := by
        rw [← mul_assoc, h32, one_mul]
    _ = 3 * (-1 : ZMod 5) ^ n := by rw [h]

private lemma sum_even_choose_alt_mod5 (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), (Nat.choose (2 * n) (2 * k) : ZMod 5) * (-1 : ZMod 5) ^ k) =
      3 * ((-1 : ZMod 5) ^ n + 1) := by
  have h := two_mul_sum_even_choose (R := ZMod 5) 2 n
  have h2k : ∀ k : ℕ, (2 : ZMod 5) ^ (2 * k) = (-1 : ZMod 5) ^ k := by
    intro k; rw [pow_mul]
    have hsq : (2 : ZMod 5) ^ 2 = -1 := by decide
    rw [hsq]
  have h1p : (1 + (2 : ZMod 5)) ^ (2 * n) = (-1 : ZMod 5) ^ n := by
    rw [pow_mul]
    have hsq : (1 + (2 : ZMod 5)) ^ 2 = -1 := by decide
    rw [hsq]
  have h1m : (1 - (2 : ZMod 5)) ^ (2 * n) = 1 := by
    rw [pow_mul]
    have hsq : (1 - (2 : ZMod 5)) ^ 2 = 1 := by decide
    rw [hsq, one_pow]
  simp only [h2k] at h
  rw [h1p, h1m] at h
  have h32 : (3 : ZMod 5) * 2 = 1 := by decide
  calc ∑ k ∈ Finset.range (n + 1), (Nat.choose (2 * n) (2 * k) : ZMod 5) * (-1 : ZMod 5) ^ k
      = (3 : ZMod 5) * (2 * ∑ k ∈ Finset.range (n + 1), (Nat.choose (2 * n) (2 * k) : ZMod 5) * (-1 : ZMod 5) ^ k) := by
        rw [← mul_assoc, h32, one_mul]
    _ = 3 * ((-1 : ZMod 5) ^ n + 1) := by rw [h]

private lemma prove_a227051 (a : ℕ → ℤ) (ha0 : a 0 = 1)
    (harec : ∀ n : ℕ, 1 ≤ n →
      ∑ k ∈ Finset.range (n + 1),
        (Nat.choose (2 * n) (2 * k) : ℤ) * denomCoeff k * a (n - k) = 0)
    (n : ℕ) (hn : 1 ≤ n) : a n ≡ 3 [ZMOD 10] := by
  -- Step 1: `a m ≡ 1 (mod 2)` for all `m ≥ 0`.
  have hmod2 : ∀ m : ℕ, (a m : ZMod 2) = 1 := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      rcases Nat.eq_zero_or_pos m with rfl | hmpos
      · simp [ha0]
      · have hrec := congr_arg (Int.cast (R := ZMod 2)) (harec m hmpos)
        simp only [Int.cast_sum, Int.cast_mul, Int.cast_natCast, Int.cast_zero, denomCoeff_mod2,
          mul_one] at hrec
        rw [Finset.sum_range_succ'] at hrec
        simp only [mul_zero, Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero] at hrec
        have htail : ∑ k ∈ Finset.range m, (Nat.choose (2 * m) (2 * (k + 1)) : ZMod 2) * (a (m - (k + 1)) : ZMod 2) =
            ∑ k ∈ Finset.range m, (Nat.choose (2 * m) (2 * (k + 1)) : ZMod 2) := by
          refine Finset.sum_congr rfl (fun k hk => ?_)
          have hkm : k < m := Finset.mem_range.mp hk
          rw [ih (m - (k + 1)) (by omega), mul_one]
        rw [htail] at hrec
        have htot := sum_even_choose_mod2 m hmpos
        rw [Finset.sum_range_succ'] at htot
        simp only [mul_zero, Nat.choose_zero_right, Nat.cast_one] at htot
        linear_combination hrec - htot
  -- Step 2: `a m ≡ 3 (mod 5)` for all `m ≥ 1`.
  have hmod5 : ∀ m : ℕ, 1 ≤ m → (a m : ZMod 5) = 3 := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro hm
      have hrec := congr_arg (Int.cast (R := ZMod 5)) (harec m hm)
      simp only [Int.cast_sum, Int.cast_mul, Int.cast_natCast, Int.cast_zero] at hrec
      rw [Finset.sum_range_succ'] at hrec
      have hd0 : (denomCoeff 0 : ZMod 5) = 1 := by simp [denomCoeff]
      simp only [mul_zero, Nat.choose_zero_right, Nat.cast_one, one_mul, hd0, Nat.sub_zero] at hrec
      have htail : ∑ k ∈ Finset.range m,
          (Nat.choose (2 * m) (2 * (k + 1)) : ZMod 5) * (denomCoeff (k + 1) : ZMod 5) * (a (m - (k + 1)) : ZMod 5) =
          (∑ k ∈ Finset.range m,
            (Nat.choose (2 * m) (2 * (k + 1)) : ZMod 5) * (denomCoeff (k + 1) : ZMod 5) * 3) -
            2 * (denomCoeff m : ZMod 5) := by
        have hm1 : m = (m - 1) + 1 := by omega
        rw [hm1, Finset.sum_range_succ, Finset.sum_range_succ]
        have hprev : ∑ k ∈ Finset.range (m - 1),
            (Nat.choose (2 * (m - 1 + 1)) (2 * (k + 1)) : ZMod 5) * (denomCoeff (k + 1) : ZMod 5) * (a (m - 1 + 1 - (k + 1)) : ZMod 5) =
            ∑ k ∈ Finset.range (m - 1),
            (Nat.choose (2 * (m - 1 + 1)) (2 * (k + 1)) : ZMod 5) * (denomCoeff (k + 1) : ZMod 5) * 3 := by
          refine Finset.sum_congr rfl (fun k hk => ?_)
          have hkl : k < m - 1 := Finset.mem_range.mp hk
          rw [ih (m - 1 + 1 - (k + 1)) (by omega) (by omega)]
        rw [hprev]
        have hsub0 : m - 1 + 1 - (m - 1 + 1) = 0 := Nat.sub_self _
        rw [hsub0, ha0, Int.cast_one, Nat.choose_self, Nat.cast_one, one_mul, ← hm1]
        ring
      rw [htail] at hrec
      have hfull : (∑ k ∈ Finset.range (m + 1),
          (Nat.choose (2 * m) (2 * k) : ZMod 5) * (denomCoeff k : ZMod 5)) * 3 -
          2 * (denomCoeff m : ZMod 5) = 0 := by
        have hsum_d : ∑ k ∈ Finset.range (m + 1),
            (Nat.choose (2 * m) (2 * k) : ZMod 5) * (denomCoeff k : ZMod 5) =
            2 * (∑ k ∈ Finset.range (m + 1), (Nat.choose (2 * m) (2 * k) : ZMod 5) * (-1 : ZMod 5) ^ k) -
            (∑ k ∈ Finset.range (m + 1), (Nat.choose (2 * m) (2 * k) : ZMod 5)) := by
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [denomCoeff_mod5 k]
          ring
        rw [hsum_d, sum_even_choose_alt_mod5 m, sum_even_choose_mod5 m hm, denomCoeff_mod5 m]
        have h5 : (5 : ZMod 5) = 0 := by decide
        have hexpand : (2 * (3 * ((-1 : ZMod 5) ^ m + 1)) - 3 * (-1 : ZMod 5) ^ m) * 3 -
            2 * (2 * (-1 : ZMod 5) ^ m - 1) =
            5 * ((-1 : ZMod 5) ^ m + 4) := by ring
        rw [hexpand, h5, zero_mul]
      rw [Finset.sum_range_succ', add_mul] at hfull
      simp only [mul_zero, Nat.choose_zero_right, Nat.cast_one, one_mul, hd0] at hfull
      rw [Finset.sum_mul] at hfull
      linear_combination hrec - hfull
  -- Step 3: Combine `mod 2` and `mod 5` via CRT (`2` and `5` coprime).
  have hdvd2 : (2 : ℤ) ∣ 3 - a n := by
    refine (ZMod.intCast_zmod_eq_zero_iff_dvd (3 - a n) 2).mp ?_
    push_cast
    rw [hmod2 n]
    decide
  have hdvd5 : (5 : ℤ) ∣ 3 - a n := by
    refine (ZMod.intCast_zmod_eq_zero_iff_dvd (3 - a n) 5).mp ?_
    push_cast
    rw [hmod5 n hn]
    ring
  have hdvd10 : (10 : ℤ) ∣ 3 - a n := by
    have hcop : IsCoprime (2 : ℤ) 5 := by
      refine ⟨-2, 1, by norm_num⟩
    have h := hcop.mul_dvd hdvd2 hdvd5
    simpa using h
  exact Int.modEq_iff_dvd.mpr hdvd10

end OMA.P_oeis_a227051

theorem OMA.solution : type_of% @OMA.S_oeis_a227051.main :=
  OMA.P_oeis_a227051.prove_a227051
