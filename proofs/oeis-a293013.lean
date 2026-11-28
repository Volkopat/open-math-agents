import OMAStatements.S_oeis_a293013
import Mathlib

/-!
# Proof of OEIS A293013 Conjecture

For `a(n) = Sum_{i=0..n} C(n, i) * (n * (n - i) + i - 1).descFactorial i`:
In `ZMod k`, Vandermonde's identity + `t ∣ i! ∣ m.descFactorial i` gives
`C(n + k, i) * m.descFactorial i = C(n, i) * m.descFactorial i` in `ZMod k`.
For `i <= n`, `((n + k) * (n + k - i) + i - 1 : ZMod k) = (n * (n - i) + i - 1 : ZMod k)`,
so their `i`-th falling factorials agree in `ZMod k`; for `i > n`, `C(n, i) = 0`.
-/

namespace OeisA293013Proof

open Finset

private lemma cast_descFactorial_zmod (k m : ℕ) :
    ∀ r : ℕ, (m.descFactorial r : ZMod k) =
      ∏ j ∈ Finset.range r, ((m : ZMod k) - (j : ZMod k)) := by
  intro r
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Nat.descFactorial_succ, Finset.prod_range_succ, Nat.cast_mul, ih]
    by_cases hmr : r ≤ m
    · rw [Nat.cast_sub hmr, mul_comm]
    · have hm_lt : m < r := by omega
      have h0 : ∏ j ∈ Finset.range r, ((m : ZMod k) - (j : ZMod k)) = 0 :=
        Finset.prod_eq_zero (Finset.mem_range.mpr hm_lt) (sub_self _)
      rw [h0, mul_zero, zero_mul]

private lemma descFactorial_modEq_of_zmod {a b i k : ℕ} (h : (a : ZMod k) = (b : ZMod k)) :
    (a.descFactorial i : ZMod k) = (b.descFactorial i : ZMod k) := by
  rw [cast_descFactorial_zmod, cast_descFactorial_zmod, h]

private lemma choose_add_mul_descFactorial_zmod (n k i m : ℕ) (hk : 1 ≤ k) :
    ((Nat.choose (n + k) i * m.descFactorial i : ℕ) : ZMod k) =
      ((Nat.choose n i * m.descFactorial i : ℕ) : ZMod k) := by
  have hvand : Nat.choose (n + k) i =
      Nat.choose n i + ∑ t ∈ Finset.Icc 1 i, Nat.choose n (i - t) * Nat.choose k t := by
    rw [Nat.add_choose_eq,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun x y => Nat.choose n x * Nat.choose k y)]
    have hrev : ∑ t ∈ Finset.range (i + 1), Nat.choose n t * Nat.choose k (i - t) =
        ∑ t ∈ Finset.range (i + 1), Nat.choose n (i - t) * Nat.choose k t := by
      refine Finset.sum_bij (fun t _ => i - t) ?_ ?_ ?_ ?_
      · intro t ht; simp only [Finset.mem_range] at ht ⊢; omega
      · intro t1 ht1 t2 ht2 h; simp only [Finset.mem_range] at ht1 ht2; omega
      · intro t ht; refine ⟨i - t, ?_, ?_⟩
        · simp only [Finset.mem_range] at ht ⊢; omega
        · simp only [Finset.mem_range] at ht; omega
      · intro t ht; simp only [Finset.mem_range] at ht; rw [show i - (i - t) = t by omega]
    rw [hrev, Finset.sum_range_succ']
    simp only [Nat.sub_zero, Nat.choose_zero_right, mul_one]
    rw [add_comm (Nat.choose n i)]
    congr 1
    refine Finset.sum_bij (fun t _ => t + 1) ?_ ?_ ?_ ?_
    · intro t ht; simp only [Finset.mem_range, Finset.mem_Icc] at ht ⊢; omega
    · intro t1 _ t2 _ h; omega
    · intro t ht; refine ⟨t - 1, ?_, ?_⟩
      · simp only [Finset.mem_Icc, Finset.mem_range] at ht ⊢; omega
      · simp only [Finset.mem_Icc] at ht; omega
    · intro t _; rfl
  have hdvd : k ∣ (∑ t ∈ Finset.Icc 1 i, Nat.choose n (i - t) * Nat.choose k t) * m.descFactorial i := by
    rw [Finset.sum_mul]
    apply Finset.dvd_sum
    intro t ht
    simp only [Finset.mem_Icc] at ht
    have ht_dvd_fact : t ∣ i.factorial := Nat.dvd_factorial ht.1 ht.2
    have hfact_dvd : i.factorial ∣ m.descFactorial i := by
      rw [Nat.descFactorial_eq_factorial_mul_choose]
      exact dvd_mul_right _ _
    obtain ⟨q, hq⟩ := dvd_trans ht_dvd_fact hfact_dvd
    have hkt : Nat.choose k t * t = k * Nat.choose (k - 1) (t - 1) := by
      have hk1 : k = (k - 1) + 1 := by omega
      have ht1 : t = (t - 1) + 1 := by omega
      conv_lhs => rw [hk1, ht1]
      have := Nat.add_one_mul_choose_eq (k - 1) (t - 1)
      rw [← hk1, ← ht1] at this ⊢
      linarith
    rw [hq]
    refine ⟨Nat.choose n (i - t) * Nat.choose (k - 1) (t - 1) * q, ?_⟩
    calc Nat.choose n (i - t) * Nat.choose k t * (t * q)
        = Nat.choose n (i - t) * (Nat.choose k t * t) * q := by ring
      _ = Nat.choose n (i - t) * (k * Nat.choose (k - 1) (t - 1)) * q := by rw [hkt]
      _ = k * (Nat.choose n (i - t) * Nat.choose (k - 1) (t - 1) * q) := by ring
  rw [hvand, add_mul, Nat.cast_add]
  have h0 : (((∑ t ∈ Finset.Icc 1 i, Nat.choose n (i - t) * Nat.choose k t) * m.descFactorial i : ℕ) : ZMod k) = 0 :=
    (ZMod.natCast_eq_zero_iff _ k).mpr hdvd
  rw [h0, add_zero]


end OeisA293013Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a293013.main := by
  intro n k hk
  rw [← ZMod.natCast_eq_natCast_iff]
  unfold OMA.S_oeis_a293013.a
  push_cast
  have hsplit : Finset.range (n + k + 1) =
      Finset.range (n + 1) ∪ (Finset.range (n + k + 1) \ Finset.range (n + 1)) := by
    ext x; simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_range]; omega
  rw [hsplit, Finset.sum_union disjoint_sdiff_self_right]
  have htail : ∑ i ∈ Finset.range (n + k + 1) \ Finset.range (n + 1),
      ((Nat.choose (n + k) i : ZMod k) *
        (((n + k) * (n + k - i) + i - 1).descFactorial i : ZMod k)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp only [Finset.mem_sdiff, Finset.mem_range] at hi
    rw [← Nat.cast_mul, OeisA293013Proof.choose_add_mul_descFactorial_zmod n k i _ hk]
    rw [Nat.choose_eq_zero_of_lt (by omega), zero_mul, Nat.cast_zero]
  rw [htail, add_zero]
  apply Finset.sum_congr rfl
  intro i hi
  have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [← Nat.cast_mul, OeisA293013Proof.choose_add_mul_descFactorial_zmod n k i _ hk, Nat.cast_mul]
  congr 1
  cases i with
  | zero => simp
  | succ i' =>
    apply OeisA293013Proof.descFactorial_modEq_of_zmod
    have h1 : 1 ≤ (n + k) * (n + k - (i' + 1)) + (i' + 1) := by omega
    have h2 : 1 ≤ n * (n - (i' + 1)) + (i' + 1) := by omega
    rw [Nat.cast_sub h1, Nat.cast_sub h2]
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_sub (by omega : i' + 1 ≤ n + k),
               Nat.cast_sub hin, ZMod.natCast_self, add_zero]
