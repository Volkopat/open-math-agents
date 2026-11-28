import OMAStatements.S_oeis_a292782
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Alternating powers and the two divisors of A292782

Translation by half a block gives one divisor. Reflection about an odd
center gives a second, coprime divisor. At an odd index n the reflection
also works modulo n²: (n-k)^(2n) and k^(2n) agree to first order in n.

Source: https://oeis.org/A292782. Credit: @Solitude1312
-/

open OMA.S_oeis_a292782

namespace OMA.A292782

private def total (R : Type*) [CommRing R] (length exponent : ℕ) : R :=
  ∑ k ∈ Finset.range length, (-1 : R) ^ k * (k : R) ^ exponent

private lemma cast_total (m l e : ℕ) :
    ((total ℤ l e : ℤ) : ZMod m) = total (ZMod m) l e := by simp [total]

private lemma dvd_total_iff (m l e : ℕ) :
    (m : ℤ) ∣ total ℤ l e ↔ total (ZMod m) l e = 0 := by
  rw [← cast_total, ZMod.intCast_zmod_eq_zero_iff_dvd]

private lemma translate (m e : ℕ) :
    total (ZMod m) (2 * m) e = (1 + (-1 : ZMod m) ^ m) * total (ZMod m) m e := by
  unfold total
  rw [two_mul, Finset.sum_range_add, add_mul, one_mul, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  simp only [pow_add, Nat.cast_add, ZMod.natCast_self, zero_add]
  ring

private lemma half_block (m e : ℕ) (hm : 0 < m) : (m : ℤ) ∣ total ℤ (2 * m) e := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    rw [dvd_total_iff, translate]
    rcases Nat.even_or_odd' m with ⟨j, hj | hj⟩
    · have hEven : Even m := ⟨j, by omega⟩
      have hdiv := ih j (by omega) (by omega)
      obtain ⟨c, hc⟩ := hdiv
      have htwice : (m : ℤ) ∣ 2 * total ℤ m e := by
        rw [hj, hc]
        exact ⟨c, by push_cast; ring⟩
      have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ m).mpr htwice
      rw [Int.cast_mul, Int.cast_ofNat, cast_total] at hz
      rw [hEven.neg_one_pow, one_add_one_eq_two]
      exact hz
    · have hOdd : Odd m := ⟨j, hj⟩
      rw [hOdd.neg_one_pow, add_neg_cancel, zero_mul]

/-- Reflection in k↔q-k has no fixed point when q is odd. -/
private lemma reflection {R : Type*} [CommRing R] (q e : ℕ) (hq : Odd q)
    (hp : ∀ k ≤ q, ((q - k : ℕ) : R) ^ e = (k : R) ^ e) :
    total R (q + 1) e = 0 := by
  unfold total
  apply Finset.sum_involution (fun k _ => q - k)
  · intro k hk
    have hle : k ≤ q := by simpa using Finset.mem_range.mp hk
    have hs : (-1 : R) ^ (q - k) = -((-1 : R) ^ k) := by
      obtain ⟨u, hu⟩ := hq
      rcases Nat.even_or_odd' k with ⟨t, ht | ht⟩
      · have h1 : Odd (q - k) := ⟨u - t, by omega⟩
        have h2 : Even k := ⟨t, by omega⟩
        rw [h1.neg_one_pow, h2.neg_one_pow]
      · have h1 : Even (q - k) := ⟨u - t, by omega⟩
        have h2 : Odd k := ⟨t, ht⟩
        rw [h1.neg_one_pow, h2.neg_one_pow, neg_neg]
    rw [hs, hp k hle]
    ring
  · intro k hk _
    obtain ⟨u, hu⟩ := hq
    have := Finset.mem_range.mp hk
    omega
  · intro k _
    apply Finset.mem_range.mpr
    omega
  · intro k hk
    have := Finset.mem_range.mp hk
    omega

/-- First-order binomial expansion for a square-zero increment. -/
private lemma nilpotent_shift {R : Type*} [CommRing R] (x z : R) (hz : z ^ 2 = 0) (t : ℕ) :
    (x + z) ^ (t + 1) = x ^ (t + 1) + ((t : R) + 1) * x ^ t * z := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ (x + z) (t + 1), ih, pow_succ x (t + 1), pow_succ x t]
    push_cast
    linear_combination ((t : R) + 1) * x ^ t * hz

private lemma base_reflection (q n : ℕ) (hq : Odd q) :
    (q : ℤ) ∣ total ℤ (q + 1) (2 * n) := by
  rw [dvd_total_iff]
  apply reflection q _ hq
  intro k hk
  rw [Nat.cast_sub hk, ZMod.natCast_self, zero_sub, pow_mul, neg_sq, ← pow_mul]

private lemma square_reflection (n : ℕ) (hn : Odd n) :
    ((n ^ 2 : ℕ) : ℤ) ∣ total ℤ n (2 * n) := by
  let R := ZMod (n ^ 2)
  have hnpos : 0 < n := by obtain ⟨j, hj⟩ := hn; omega
  have hz : (n : R) ^ 2 = 0 := by
    change (n : ZMod (n ^ 2)) ^ 2 = 0
    rw [← Nat.cast_pow, ZMod.natCast_self]
  have hsmall (k : ℕ) (hk : k ≤ n) : ((n - k : ℕ) : R) ^ n = (-(k : R)) ^ n := by
    obtain ⟨j, hj⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
    have h := nilpotent_shift (-(k : R)) (n : R) hz j
    have hc : (j : R) + 1 = (n : R) := by
      simpa only [Nat.cast_add, Nat.cast_one] using congrArg (fun a : ℕ => (a : R)) hj.symm
    rw [← hj, hc] at h
    rw [Nat.cast_sub hk, show (n : R) - (k : R) = -(k : R) + n by ring, h]
    linear_combination (-(k : R)) ^ j * hz
  have hfull : total R (n + 1) (2 * n) = 0 := by
    apply reflection n _ hn
    intro k hk
    rw [Nat.mul_comm 2 n, pow_mul, hsmall k hk, ← pow_mul, Nat.mul_comm n 2,
      pow_mul, neg_sq, ← pow_mul]
  have hlast : (n : R) ^ (2 * n) = 0 := by rw [pow_mul, hz, zero_pow (by omega : n ≠ 0)]
  rw [dvd_total_iff]
  simpa only [total, Finset.sum_range_succ, hlast, mul_zero, add_zero] using hfull

private lemma right_divisor (n : ℕ) (d : ℤ) (hd : d ∣ total ℤ n (2 * n)) : d ∣ a n := by
  exact dvd_mul_of_dvd_right hd _

lemma divisibility (n : ℕ) (hn : 2 ≤ n) :
    (((n * (n - 1) / 2 : ℕ) : ℤ) ∣ a n) ∧
    (Odd n → ((n ^ 2 * (n - 1) / 2 : ℕ) : ℤ) ∣ a n) := by
  rcases Nat.even_or_odd' n with ⟨t, ht | ht⟩
  · have hpos : 0 < t := by omega
    let q := n - 1
    have hq : q + 1 = n := by dsimp [q]; omega
    have hodd : Odd q := ⟨t - 1, by dsimp [q]; omega⟩
    have hpart := half_block t (2 * n) hpos
    rw [← ht] at hpart
    have hother := base_reflection q n hodd
    rw [hq] at hother
    have hbez : IsCoprime (t : ℤ) (q : ℤ) := by
      refine ⟨2, -1, ?_⟩
      have hcast : (q : ℤ) + 1 = 2 * (t : ℤ) := by exact_mod_cast hq.trans ht
      omega
    have hfactor : n * (n - 1) / 2 = t * q := by
      change n * q / 2 = _
      rw [ht, Nat.mul_assoc, Nat.mul_div_cancel_left _ (by decide)]
    constructor
    · rw [hfactor, Nat.cast_mul]
      exact right_divisor n _ (hbez.mul_dvd hpart hother)
    · rintro ⟨j, hj⟩
      omega
  · have hpos : 0 < t := by omega
    have hodd : Odd n := ⟨t, ht⟩
    have hpart := half_block t (2 * n) hpos
    have hshort : total (ZMod t) (2 * t) (2 * n) = 0 := (dvd_total_iff ..).mp hpart
    have hfull : (t : ℤ) ∣ total ℤ n (2 * n) := by
      rw [dvd_total_iff]
      conv_lhs => arg 2; rw [ht]
      simpa only [total, Finset.sum_range_succ, Nat.cast_mul, ZMod.natCast_self,
        mul_zero, zero_pow (by omega : 2 * n ≠ 0), add_zero] using hshort
    have hsq := square_reflection n hodd
    rw [Nat.cast_pow] at hsq
    have hncast : (n : ℤ) = 2 * (t : ℤ) + 1 := by exact_mod_cast ht
    have hbez : IsCoprime (t : ℤ) ((n : ℤ) ^ 2) := by
      refine ⟨-4 * (t : ℤ) - 4, 1, ?_⟩
      rw [hncast]
      ring
    have hcombined := right_divisor n _ (hbez.mul_dvd hfull hsq)
    have hf (x : ℕ) : x * (n - 1) / 2 = t * x := by
      rw [show n - 1 = 2 * t by omega, show x * (2 * t) = 2 * (t * x) by ring,
        Nat.mul_div_cancel_left _ (by decide)]
    rw [hf, hf, Nat.cast_mul, Nat.cast_mul, Nat.cast_pow]
    exact ⟨(show (t : ℤ) * n ∣ (t : ℤ) * (n : ℤ) ^ 2 from ⟨n, by ring⟩).trans hcombined,
      fun _ => hcombined⟩

end OMA.A292782

theorem OMA.solution : type_of% @OMA.S_oeis_a292782.main := by
  exact OMA.A292782.divisibility
