import OMAStatements.S_oeis_a036284
import Mathlib

-- Problem: A036284: Polynomials formed from the binary digits of Fibonacci numbers
-- Upstream: statements/oeis-a036284.lean (declaration OMA.S_oeis_a036284.main)
-- Credit: @nnkostov

namespace A036284Proof

open Polynomial
open scoped BigOperators

private abbrev R := (ZMod 2)[X]

/-! ### Part 1: Fibonacci addition formula and congruences modulo 2^(n+1) -/

private lemma fib_add_succ (a b : ℕ) :
    Nat.fib (a + b + 1) = Nat.fib (a + 1) * Nat.fib (b + 1) + Nat.fib a * Nat.fib b := by
  induction b using Nat.twoStepInduction generalizing a with
  | zero =>
    simp
  | one =>
    simp [Nat.fib_add_two]
    ring
  | more b ih0 ih1 =>
    have h1 : a + (b + 2) + 1 = (a + b + 1) + 2 := by omega
    have h2 : a + b + 1 + 1 = a + (b + 1) + 1 := by omega
    have h3 : Nat.fib (b + 3) = Nat.fib (b + 1) + Nat.fib (b + 2) := Nat.fib_add_two
    have h4 : Nat.fib (b + 2) = Nat.fib b + Nat.fib (b + 1) := Nat.fib_add_two
    rw [h1, Nat.fib_add_two, h2, ih0, ih1,
      show b + 2 + 1 = b + 3 by omega, show b + 1 + 1 = b + 2 by omega, h3, h4]
    ring

private lemma fib_pow2_cong : ∀ n : ℕ, 2 ≤ n →
    2 ^ (n + 1) ∣ Nat.fib (3 * 2 ^ (n - 1)) ∧
    Nat.fib (3 * 2 ^ (n - 1) + 1) % 2 ^ (n + 1) = 1 + 2 ^ n := by
  intro n hn
  induction n with
  | zero => omega
  | succ m ih =>
    by_cases hm : m = 1
    · subst hm
      decide
    · have hm2 : 2 ≤ m := by omega
      obtain ⟨hdvd, hmod⟩ := ih hm2
      set L := 3 * 2 ^ (m - 1)
      have h2L : 3 * 2 ^ (m + 1 - 1) = 2 * L := by
        have : 2 ^ m = 2 * 2 ^ (m - 1) := by
          cases m with
          | zero => omega
          | succ k => simp [pow_succ, mul_comm]
        change 3 * 2 ^ m = 2 * (3 * 2 ^ (m - 1))
        rw [this]
        ring
      have hLpos : 1 ≤ L := by
        have : 1 ≤ 2 ^ (m - 1) := Nat.one_le_pow _ _ (by omega)
        omega
      rw [h2L]
      constructor
      · -- 2 ^ (m + 2) ∣ fib (2 * L)
        have heq : 2 * L = (L - 1) + L + 1 := by omega
        rw [heq, fib_add_succ, Nat.sub_add_cancel hLpos]
        have hfac : Nat.fib L * Nat.fib (L + 1) + Nat.fib (L - 1) * Nat.fib L =
            Nat.fib L * (Nat.fib (L + 1) + Nat.fib (L - 1)) := by ring
        rw [hfac]
        have hstep : Nat.fib (L + 1) = Nat.fib (L - 1) + Nat.fib L := by
          have hL2 : L + 1 = (L - 1) + 2 := by omega
          rw [hL2, Nat.fib_add_two, Nat.sub_add_cancel hLpos]
        have h2dvdL : 2 ∣ Nat.fib L := dvd_trans (dvd_pow_self 2 (by omega : m + 1 ≠ 0)) hdvd
        have heven : 2 ∣ Nat.fib (L + 1) + Nat.fib (L - 1) := by
          rw [hstep]
          obtain ⟨t, ht⟩ := h2dvdL
          refine ⟨Nat.fib (L - 1) + t, ?_⟩
          omega
        obtain ⟨q, hq⟩ := hdvd
        obtain ⟨s, hs⟩ := heven
        refine ⟨q * s, ?_⟩
        rw [hq, hs]
        have hpow : 2 ^ (m + 1 + 1) = 2 ^ (m + 1) * 2 := by rw [pow_succ]
        rw [hpow]
        ring
      · -- fib (2 * L + 1) % 2 ^ (m + 2) = 1 + 2 ^ (m + 1)
        have heq : 2 * L + 1 = L + L + 1 := by omega
        rw [heq, fib_add_succ]
        obtain ⟨q, hq⟩ := hdvd
        set r := Nat.fib (L + 1) / 2 ^ (m + 1)
        have hFL1 : Nat.fib (L + 1) = 2 ^ (m + 1) * r + (1 + 2 ^ m) := by
          rw [← hmod]
          exact (Nat.div_add_mod (Nat.fib (L + 1)) (2 ^ (m + 1))).symm
        have h2m_dvd : 2 ^ (m + 2) ∣ 2 ^ (2 * m) := Nat.pow_dvd_pow 2 (by omega)
        obtain ⟨c, hc⟩ := h2m_dvd
        have hsq1 : Nat.fib (L + 1) ^ 2 =
            2 ^ (m + 2) * (2 ^ m * r ^ 2 + r * (1 + 2 ^ m) + c) + (1 + 2 ^ (m + 1)) := by
          rw [hFL1]
          have hpow1 : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ]; ring
          have hpow2 : 2 ^ (m + 2) = 4 * 2 ^ m := by rw [pow_succ, pow_succ]; ring
          have hsq2m : (2 ^ m) ^ 2 = 2 ^ (2 * m) := by rw [← pow_mul]; ring_nf
          calc
            (2 ^ (m + 1) * r + (1 + 2 ^ m)) ^ 2
                = (2 ^ (m + 1)) ^ 2 * r ^ 2 + 2 * 2 ^ (m + 1) * r * (1 + 2 ^ m) +
                    (2 ^ m) ^ 2 + (1 + 2 * 2 ^ m) := by ring
            _ = (4 * 2 ^ m) * (2 ^ m * r ^ 2) + (4 * 2 ^ m) * (r * (1 + 2 ^ m)) +
                    2 ^ (2 * m) + (1 + 2 ^ (m + 1)) := by rw [hpow1, hsq2m]; ring
            _ = 2 ^ (m + 2) * (2 ^ m * r ^ 2 + r * (1 + 2 ^ m) + c) + (1 + 2 ^ (m + 1)) := by
                    rw [← hpow2, hc]; ring
        have hsq0 : Nat.fib L ^ 2 = 2 ^ (m + 2) * (2 ^ m * q ^ 2) := by
          rw [hq]
          have hpow1 : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ]; ring
          have hpow2 : 2 ^ (m + 2) = 4 * 2 ^ m := by rw [pow_succ, pow_succ]; ring
          rw [hpow1, hpow2]
          ring
        have htot : Nat.fib (L + 1) ^ 2 + Nat.fib L ^ 2 =
            2 ^ (m + 2) * (2 ^ m * r ^ 2 + r * (1 + 2 ^ m) + c + 2 ^ m * q ^ 2) +
              (1 + 2 ^ (m + 1)) := by
          rw [hsq1, hsq0]
          ring
        have hlt : 1 + 2 ^ (m + 1) < 2 ^ (m + 2) := by
          have : 2 ^ (m + 2) = 2 * 2 ^ (m + 1) := by rw [pow_succ]; ring
          have h2pos : 1 < 2 ^ (m + 1) := by
            calc 1 < 2 ^ 1 := by decide
            _ ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by omega) (by omega)
          omega
        change (Nat.fib (L + 1) * Nat.fib (L + 1) + Nat.fib L * Nat.fib L) % 2 ^ (m + 2) =
          1 + 2 ^ (m + 1)
        rw [← sq, ← sq, htot, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]

private lemma fib_shift_mod {n : ℕ} (hn : 2 ≤ n) (k : ℕ) :
    Nat.fib (k + 3 * 2 ^ (n - 1)) % 2 ^ (n + 1) = ((1 + 2 ^ n) * Nat.fib k) % 2 ^ (n + 1) := by
  obtain ⟨hdvd, hmod⟩ := fib_pow2_cong n hn
  set L := 3 * 2 ^ (n - 1)
  cases k with
  | zero =>
    simp only [zero_add, Nat.fib_zero, mul_zero, Nat.zero_mod]
    exact Nat.mod_eq_zero_of_dvd hdvd
  | succ m =>
    have heq : m + 1 + L = m + L + 1 := by omega
    rw [heq, fib_add_succ]
    obtain ⟨q, hq⟩ := hdvd
    set r := Nat.fib (L + 1) / 2 ^ (n + 1)
    have hFL1 : Nat.fib (L + 1) = 2 ^ (n + 1) * r + (1 + 2 ^ n) := by
      rw [← hmod]
      exact (Nat.div_add_mod (Nat.fib (L + 1)) (2 ^ (n + 1))).symm
    have hsum : Nat.fib (m + 1) * Nat.fib (L + 1) + Nat.fib m * Nat.fib L =
        2 ^ (n + 1) * (Nat.fib (m + 1) * r + Nat.fib m * q) + (1 + 2 ^ n) * Nat.fib (m + 1) := by
      rw [hFL1, hq]
      ring
    rw [hsum, Nat.mul_add_mod]

/-! ### Part 2: Binary digit shift identity in ZMod 2 -/

private lemma div_pow_mod_two_eq (n x : ℕ) :
    (x / 2 ^ n) % 2 = (x % 2 ^ (n + 1)) / 2 ^ n := by
  have hpow : 2 ^ (n + 1) = 2 ^ n * 2 := by rw [pow_succ]
  have hdiv : x = 2 ^ n * (2 * (x / 2 ^ (n + 1))) + x % 2 ^ (n + 1) := by
    have h := Nat.div_add_mod x (2 ^ (n + 1))
    calc x = 2 ^ (n + 1) * (x / 2 ^ (n + 1)) + x % 2 ^ (n + 1) := h.symm
      _ = 2 ^ n * (2 * (x / 2 ^ (n + 1))) + x % 2 ^ (n + 1) := by rw [hpow, mul_assoc]
  have hpos : 0 < 2 ^ n := Nat.pos_of_ne_zero (by positivity)
  have hlt : x % 2 ^ (n + 1) < 2 ^ n * 2 := by
    rw [← hpow]
    exact Nat.mod_lt x (by positivity)
  have hq : x / 2 ^ n = 2 * (x / 2 ^ (n + 1)) + (x % 2 ^ (n + 1)) / 2 ^ n := by
    conv_lhs => rw [hdiv]
    rw [Nat.mul_add_div hpos]
  have hqlt : (x % 2 ^ (n + 1)) / 2 ^ n < 2 := Nat.div_lt_of_lt_mul hlt
  rw [hq, Nat.mul_add_mod, Nat.mod_eq_of_lt hqlt]

private lemma digit_shift {n : ℕ} (hn : 2 ≤ n) (k : ℕ) :
    OMA.S_oeis_a036284.digit n (k + 3 * 2 ^ (n - 1)) =
      OMA.S_oeis_a036284.digit n k + ((Nat.fib k % 2 : ℕ) : ZMod 2) := by
  unfold OMA.S_oeis_a036284.digit
  have hmod := fib_shift_mod hn k
  have hbit : (Nat.fib (k + 3 * 2 ^ (n - 1)) / 2 ^ n) % 2 =
      (Nat.fib k / 2 ^ n + Nat.fib k) % 2 := by
    rw [div_pow_mod_two_eq, hmod, ← div_pow_mod_two_eq]
    have hpos : 0 < 2 ^ n := Nat.pos_of_ne_zero (by positivity)
    have hmul : (1 + 2 ^ n) * Nat.fib k = 2 ^ n * Nat.fib k + Nat.fib k := by ring
    rw [hmul, Nat.mul_add_div hpos, add_comm]
  rw [hbit]
  have hcast : (((Nat.fib k / 2 ^ n + Nat.fib k) % 2 : ℕ) : ZMod 2) =
      ((Nat.fib k / 2 ^ n : ℕ) : ZMod 2) + ((Nat.fib k : ℕ) : ZMod 2) := by
    rw [ZMod.natCast_mod, Nat.cast_add]
  rw [hcast, ZMod.natCast_mod, ZMod.natCast_mod]

/-! ### Part 3: Fibonacci parity polynomial identity in (ZMod 2)[X] -/

private lemma fib_mod_two (k : ℕ) :
    Nat.fib k % 2 = if k % 3 = 0 then 0 else 1 := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    match k with
    | 0 => decide
    | 1 => decide
    | 2 => decide
    | m + 3 =>
      have hrec : Nat.fib (m + 3) = 2 * Nat.fib (m + 1) + Nat.fib m := by
        rw [Nat.fib_add_two (n := m + 1), Nat.fib_add_two (n := m)]
        ring
      rw [hrec, Nat.mul_add_mod, ih m (by omega)]
      have hmod3 : (m + 3) % 3 = m % 3 := by omega
      rw [hmod3]

private lemma sum_fib_parity_poly (m : ℕ) :
    ∑ k ∈ Finset.range (3 * m), C ((Nat.fib k % 2 : ℕ) : ZMod 2) * (X : R) ^ k =
      X * (X + 1) * ∑ j ∈ Finset.range m, ((X : R) ^ 3) ^ j := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h3 : 3 * (m + 1) = 3 * m + 3 := by ring
    rw [h3, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ]
    have h0 : Nat.fib (3 * m) % 2 = 0 := by rw [fib_mod_two]; simp
    have h1 : Nat.fib (3 * m + 1) % 2 = 1 := by
      rw [fib_mod_two]
      simp
    have h2 : Nat.fib (3 * m + 2) % 2 = 1 := by
      rw [fib_mod_two]
      simp
    rw [h0, h1, h2]
    simp only [Nat.cast_zero, map_zero, zero_mul, add_zero, Nat.cast_one, map_one, one_mul]
    have hpow1 : (X : R) ^ (3 * m + 1) = X * ((X : R) ^ 3) ^ m := by
      rw [pow_add, pow_one, pow_mul, mul_comm]
    have hpow2 : (X : R) ^ (3 * m + 2) = X ^ 2 * ((X : R) ^ 3) ^ m := by
      rw [pow_add, pow_mul, mul_comm]
    rw [hpow1, hpow2]
    ring

/-! ### Part 4: Characteristic-2 polynomial identities in (ZMod 2)[X] -/

private lemma two_eq_zero_R : (2 : R) = 0 := by
  have h0 : (2 : ZMod 2) = 0 := by decide
  have h1 : (C (2 : ZMod 2) : R) = 0 := by rw [h0, map_zero]
  simpa only [map_ofNat] using h1

private lemma add_sq_char_two (p q : R) : (p + q) ^ 2 = p ^ 2 + q ^ 2 := by
  calc
    (p + q) ^ 2 = p ^ 2 + (2 : R) * (p * q) + q ^ 2 := by ring
    _ = p ^ 2 + q ^ 2 := by rw [two_eq_zero_R, zero_mul, add_zero]

private lemma add_pow_two_pow_char_two (p q : R) :
    ∀ k : ℕ, (p + q) ^ (2 ^ k) = p ^ (2 ^ k) + q ^ (2 ^ k)
  | 0 => by simp
  | k + 1 => by
    rw [pow_succ, pow_mul, pow_mul, pow_mul, add_pow_two_pow_char_two p q k, add_sq_char_two]

private lemma neg_eq_self_char_two (p : R) : -p = p := by
  have hadd : p + p = 0 := by
    calc p + p = (2 : R) * p := by ring
    _ = 0 := by rw [two_eq_zero_R, zero_mul]
  exact neg_eq_of_add_eq_zero_right hadd

private lemma X_cube_add_one_ne_zero : (X : R) ^ 3 + 1 ≠ 0 := by
  intro h
  have hev := congr_arg (Polynomial.eval (0 : ZMod 2)) h
  simp at hev

private lemma geom_sum_X_cube_eq_factor (n : ℕ) :
    ∑ j ∈ Finset.range (2 ^ (n - 1)), ((X : R) ^ 3) ^ j = OMA.S_oeis_a036284.factor n := by
  have hne : (X : R) ^ 3 + 1 ≠ 0 := X_cube_add_one_ne_zero
  apply mul_left_cancel₀ hne
  have hsub : ((X : R) ^ 3 - 1) = (X : R) ^ 3 + 1 := by
    rw [sub_eq_add_neg, neg_eq_self_char_two]
  have hgeom := mul_geom_sum ((X : R) ^ 3) (2 ^ (n - 1))
  rw [hsub] at hgeom
  rw [hgeom, sub_eq_add_neg, neg_eq_self_char_two]
  unfold OMA.S_oeis_a036284.factor
  have hpos : 1 ≤ 2 ^ (n - 1) := Nat.one_le_pow _ _ (by omega)
  have hpow : (X ^ 3 + 1 : R) * (X ^ 3 + 1) ^ (2 ^ (n - 1) - 1) =
      (X ^ 3 + 1) ^ (2 ^ (n - 1)) := by
    rw [← pow_succ', Nat.sub_add_cancel hpos]
  rw [hpow, add_pow_two_pow_char_two, one_pow]

private lemma X_cube_add_one_factor :
    (X : R) ^ 3 + 1 = (X + 1) * (X ^ 2 + X + 1) := by
  symm
  calc
    (X + 1 : R) * (X ^ 2 + X + 1)
        = X ^ 3 + (2 : R) * X ^ 2 + (2 : R) * X + 1 := by ring
    _ = X ^ 3 + 1 := by rw [two_eq_zero_R]; ring

/-! ### Part 5: Base case n = 1 and general case n ≥ 2 -/

private lemma case_one :
    OMA.S_oeis_a036284.factor 1 ∣ OMA.S_oeis_a036284.column 1 ∧
    OMA.S_oeis_a036284.column 1 =
      OMA.S_oeis_a036284.factor 1 * (OMA.S_oeis_a036284.column 1 / OMA.S_oeis_a036284.factor 1) ∧
    X * (X + 1) ∣ OMA.S_oeis_a036284.column 1 / OMA.S_oeis_a036284.factor 1 := by
  have hfac : OMA.S_oeis_a036284.factor 1 = 1 := by
    unfold OMA.S_oeis_a036284.factor
    simp
  have hcol : OMA.S_oeis_a036284.column 1 = X * (X + 1) * X ^ 2 := by
    unfold OMA.S_oeis_a036284.column
    have h6 : 3 * 2 ^ 1 = 6 := by decide
    rw [h6]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add]
    have hd0 : OMA.S_oeis_a036284.digit 1 0 = 0 := by decide
    have hd1 : OMA.S_oeis_a036284.digit 1 1 = 0 := by decide
    have hd2 : OMA.S_oeis_a036284.digit 1 2 = 0 := by decide
    have hd3 : OMA.S_oeis_a036284.digit 1 3 = 1 := by decide
    have hd4 : OMA.S_oeis_a036284.digit 1 4 = 1 := by decide
    have hd5 : OMA.S_oeis_a036284.digit 1 5 = 0 := by decide
    rw [hd0, hd1, hd2, hd3, hd4, hd5]
    simp only [map_zero, zero_mul, add_zero, zero_add, map_one, one_mul]
    ring
  rw [hfac, hcol]
  refine ⟨one_dvd _, ?_, ?_⟩
  · simp
  · rw [EuclideanDomain.div_one]
    exact dvd_mul_right _ _

private lemma case_ge_two {n : ℕ} (hn : 2 ≤ n) :
    OMA.S_oeis_a036284.factor n ∣ OMA.S_oeis_a036284.column n ∧
    OMA.S_oeis_a036284.column n =
      OMA.S_oeis_a036284.factor n * (OMA.S_oeis_a036284.column n / OMA.S_oeis_a036284.factor n) ∧
    X * (X + 1) ∣ OMA.S_oeis_a036284.column n / OMA.S_oeis_a036284.factor n := by
  set L := 3 * 2 ^ (n - 1)
  have h2L : 3 * 2 ^ n = L + L := by
    have : 2 ^ n = 2 ^ (n - 1) + 2 ^ (n - 1) := by
      cases n with
      | zero => omega
      | succ m => simp [pow_succ, mul_two]
    change 3 * 2 ^ n = 3 * 2 ^ (n - 1) + 3 * 2 ^ (n - 1)
    rw [this]
    ring
  set P : R := ∑ k ∈ Finset.range L, C (OMA.S_oeis_a036284.digit n k) * X ^ k
  have hP_div_X : ∃ P' : R, P = X * P' := by
    have hLpos : 1 ≤ L := by
      have : 1 ≤ 2 ^ (n - 1) := Nat.one_le_pow _ _ (by omega)
      omega
    refine ⟨∑ k ∈ Finset.range (L - 1), C (OMA.S_oeis_a036284.digit n (k + 1)) * X ^ k, ?_⟩
    have hLsucc : L = (L - 1) + 1 := by omega
    show ∑ k ∈ Finset.range L, C (OMA.S_oeis_a036284.digit n k) * X ^ k = _
    rw [hLsucc, Finset.sum_range_succ']
    have hd0 : OMA.S_oeis_a036284.digit n 0 = 0 := by
      unfold OMA.S_oeis_a036284.digit
      simp
    rw [hd0, map_zero, zero_mul, add_zero, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [pow_succ']
    ring
  have hcol_split : OMA.S_oeis_a036284.column n =
      (X ^ L + 1) * P + X ^ L * (X * (X + 1) * OMA.S_oeis_a036284.factor n) := by
    unfold OMA.S_oeis_a036284.column
    rw [h2L, Finset.sum_range_add]
    have hsecond : ∑ k ∈ Finset.range L, C (OMA.S_oeis_a036284.digit n (L + k)) * X ^ (L + k) =
        X ^ L * P + X ^ L * (X * (X + 1) * OMA.S_oeis_a036284.factor n) := by
      have hterm : ∀ k ∈ Finset.range L,
          C (OMA.S_oeis_a036284.digit n (L + k)) * (X : R) ^ (L + k) =
            X ^ L * (C (OMA.S_oeis_a036284.digit n k) * X ^ k) +
            X ^ L * (C ((Nat.fib k % 2 : ℕ) : ZMod 2) * X ^ k) := by
        intro k _
        rw [add_comm L k, digit_shift hn k, map_add, pow_add]
        ring
      rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      congr 2
      rw [sum_fib_parity_poly (2 ^ (n - 1)), geom_sum_X_cube_eq_factor n]
    rw [hsecond]
    ring
  have hXL_add_one : (X : R) ^ L + 1 = OMA.S_oeis_a036284.factor n * (X ^ 3 + 1) := by
    unfold OMA.S_oeis_a036284.factor
    have hpos : 1 ≤ 2 ^ (n - 1) := Nat.one_le_pow _ _ (by omega)
    rw [← pow_succ, Nat.sub_add_cancel hpos, add_pow_two_pow_char_two, one_pow, ← pow_mul]
  set Q : R := (X ^ 3 + 1) * P + X ^ L * (X * (X + 1))
  have hcol_eq : OMA.S_oeis_a036284.column n = OMA.S_oeis_a036284.factor n * Q := by
    rw [hcol_split, hXL_add_one]
    ring
  have hfac_ne : OMA.S_oeis_a036284.factor n ≠ 0 := by
    unfold OMA.S_oeis_a036284.factor
    exact pow_ne_zero _ X_cube_add_one_ne_zero
  have hdiv_eq : OMA.S_oeis_a036284.column n / OMA.S_oeis_a036284.factor n = Q := by
    apply mul_left_cancel₀ hfac_ne
    have hmod : OMA.S_oeis_a036284.column n % OMA.S_oeis_a036284.factor n = 0 :=
      EuclideanDomain.mod_eq_zero.mpr ⟨Q, hcol_eq⟩
    have hdm := EuclideanDomain.div_add_mod (OMA.S_oeis_a036284.column n) (OMA.S_oeis_a036284.factor n)
    rw [hmod, add_zero] at hdm
    rw [hdm, hcol_eq]
  refine ⟨⟨Q, hcol_eq⟩, ?_, ?_⟩
  · rw [hdiv_eq, hcol_eq]
  · rw [hdiv_eq]
    obtain ⟨P', hP'⟩ := hP_div_X
    refine ⟨(X ^ 2 + X + 1) * P' + X ^ L, ?_⟩
    change (X ^ 3 + 1) * P + X ^ L * (X * (X + 1)) = _
    rw [hP', X_cube_add_one_factor]
    ring

end A036284Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a036284.main := by
  intro n hn
  by_cases h1 : n = 1
  · subst h1
    exact A036284Proof.case_one
  · exact A036284Proof.case_ge_two (by omega)
