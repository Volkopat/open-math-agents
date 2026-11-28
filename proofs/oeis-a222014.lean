import OMAStatements.S_oeis_a222014
import Mathlib

namespace OMA.S_oeis_a222014

open PowerSeries in
theorem sq_coeff_char2 (b : ℕ → ZMod 2) (n : ℕ) :
    ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, b p.1 * b p.2 = if Even n then b (n / 2) ^ 2 else 0 := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.HasAntidiagonal.antidiagonal n) (fun p => p.1 = p.2)]
  have h1 : ∑ p ∈ (Finset.HasAntidiagonal.antidiagonal n).filter (fun p => ¬ p.1 = p.2), b p.1 * b p.2 = 0 := by
    refine Finset.sum_involution (fun p _ => Prod.swap p) ?_ ?_ ?_ ?_
    · intro p hp
      have : b p.1 * b p.2 + b p.2 * b p.1 = 0 := by
        rw [mul_comm (b p.2)]
        generalize b p.1 * b p.2 = t
        revert t; decide
      simpa using this
    · intro p hp _ h
      simp only [Finset.mem_filter] at hp
      apply hp.2
      have := congrArg Prod.fst h
      simpa using this.symm
    · intro p hp
      simp only [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at hp ⊢
      refine ⟨by simp [add_comm, hp.1], fun h => hp.2 h.symm⟩
    · intro p _; simp
  rw [h1, add_zero]
  by_cases he : Even n
  · obtain ⟨m, hm⟩ := he
    have hfil : (Finset.HasAntidiagonal.antidiagonal n).filter (fun p => p.1 = p.2) = {(m, m)} := by
      ext p
      simp only [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal, Finset.mem_singleton]
      constructor
      · rintro ⟨h1, h2⟩
        ext <;> simp <;> omega
      · rintro rfl; simp; omega
    rw [hfil, if_pos ⟨m, hm⟩]
    simp [show n / 2 = m by omega, sq]
  · have hfil : (Finset.HasAntidiagonal.antidiagonal n).filter (fun p => p.1 = p.2) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro p hp h
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
      exact he ⟨p.1, by omega⟩
    rw [hfil, if_neg he]
    simp


open PowerSeries in
theorem key (A : PowerSeries ℤ) (h : IsA222014 A) :
    PowerSeries.map (Int.castRingHom (ZMod 2)) A =
      1 + X * (PowerSeries.map (Int.castRingHom (ZMod 2)) A) ^ 2 := by
  obtain ⟨T, hT, hA⟩ := h
  set φ := Int.castRingHom (ZMod 2) with hφ
  set B := PowerSeries.map φ A with hB
  have hS : ∀ k : ℕ, PowerSeries.map φ (T k) *
      (∏ j ∈ Finset.range k, (1 + ((j + 1 : ℕ) : PowerSeries (ZMod 2)) * X * B ^ k)) =
        ((Nat.factorial k : ℕ) : PowerSeries (ZMod 2)) * X ^ k * B ^ (k ^ 2) := by
    intro k
    have := congrArg (PowerSeries.map φ) (hT k)
    simpa [map_mul, map_prod, map_pow, hB] using this
  have hunit : ∀ k : ℕ, IsUnit (∏ j ∈ Finset.range k,
      (1 + ((j + 1 : ℕ) : PowerSeries (ZMod 2)) * X * B ^ k)) := by
    intro k
    rw [PowerSeries.isUnit_iff_constantCoeff]
    have hc : PowerSeries.constantCoeff (∏ j ∈ Finset.range k,
        (1 + ((j + 1 : ℕ) : PowerSeries (ZMod 2)) * X * B ^ k)) = 1 := by
      simp [map_prod]
    rw [hc]; exact isUnit_one
  have hzero : ∀ k : ℕ, 2 ≤ k → PowerSeries.map φ (T k) = 0 := by
    intro k hk
    have h2 : ((Nat.factorial k : ℕ) : PowerSeries (ZMod 2)) = 0 := by
      have : ((Nat.factorial k : ℕ) : ZMod 2) = 0 := by
        rw [ZMod.natCast_eq_zero_iff]
        exact Nat.dvd_factorial (by norm_num) hk
      have h3 : ((Nat.factorial k : ℕ) : PowerSeries (ZMod 2)) =
          PowerSeries.C ((Nat.factorial k : ℕ) : ZMod 2) := by simp
      rw [h3, this]; simp
    have := hS k
    rw [h2] at this
    simp only [zero_mul] at this
    exact ((hunit k).mul_left_eq_zero).mp this
  have hS0 : PowerSeries.map φ (T 0) = 1 := by
    have := hS 0
    simpa using this
  have hS1 : PowerSeries.map φ (T 1) * (1 + X * B) = X * B := by
    have := hS 1
    simpa using this
  have hBsum : B = 1 + PowerSeries.map φ (T 1) := by
    ext m
    have hm := hA m
    have hm' : PowerSeries.coeff m B = ∑ k ∈ Finset.range (m + 1), PowerSeries.coeff m (PowerSeries.map φ (T k)) := by
      rw [hB, PowerSeries.coeff_map, hm]
      simp [map_sum, PowerSeries.coeff_map]
    rw [hm']
    rcases m with _ | m
    · have h1c : PowerSeries.coeff 0 (PowerSeries.map φ (T 1)) = 0 := by
        have := congrArg PowerSeries.constantCoeff hS1
        simp only [map_mul, map_add, map_one, PowerSeries.constantCoeff_X, zero_mul, add_zero, mul_one] at this
        rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]; exact this
      rw [Finset.sum_range_one, hS0, map_add, h1c]; simp
    · rw [Finset.sum_range_succ', Finset.sum_range_succ']
      rw [Finset.sum_eq_zero (fun k _ => by rw [hzero (k + 2) (by omega)]; simp)]
      simp [hS0]
  have hE : (B - 1) * (1 + X * B) = X * B := by
    have : B - 1 = PowerSeries.map φ (T 1) := by rw [hBsum]; ring
    rw [this]; exact hS1
  have h2 : (2 : PowerSeries (ZMod 2)) = 0 := by
    have : (2 : PowerSeries (ZMod 2)) = PowerSeries.C (2 : ZMod 2) := (map_ofNat PowerSeries.C 2).symm
    rw [this, show (2 : ZMod 2) = 0 from rfl, map_zero]
  linear_combination hE + (X * B - X * B ^ 2) * h2

open PowerSeries in
theorem rec_coeff (B : PowerSeries (ZMod 2)) (hB : B = 1 + X * B ^ 2) (n : ℕ) :
    coeff n B = if n = 0 then 1 else if n % 2 = 1 then coeff (n / 2) B else 0 := by
  rcases n with _ | k
  · conv_lhs => rw [hB]
    simp
  · conv_lhs => rw [hB]
    rw [map_add, coeff_succ_X_mul, pow_two, coeff_mul, sq_coeff_char2 (fun i => coeff i B) k]
    simp only [coeff_one, Nat.succ_ne_zero, if_false, zero_add]
    by_cases he : Even k
    · have h1 : (k + 1) % 2 = 1 := by obtain ⟨m, hm⟩ := he; omega
      have h2 : (k + 1) / 2 = k / 2 := by obtain ⟨m, hm⟩ := he; omega
      rw [if_pos he, if_pos h1, h2]
      generalize coeff (k / 2) B = t
      revert t; decide
    · have h1 : ¬ (k + 1) % 2 = 1 := by
        intro h; apply he; exact ⟨k / 2, by omega⟩
      rw [if_neg he, if_neg h1]

theorem odd_iff (b : ℕ → ZMod 2) (h0 : b 0 = 1)
    (hr : ∀ n, b n = if n = 0 then 1 else if n % 2 = 1 then b (n / 2) else 0) :
    ∀ n, b n = 1 ↔ ∃ k : ℕ, n = 2 ^ k - 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [hr n]
    by_cases hn : n = 0
    · subst hn
      simp only [if_true]
      exact ⟨fun _ => ⟨0, by norm_num⟩, fun _ => trivial⟩
    · rw [if_neg hn]
      by_cases hodd : n % 2 = 1
      · rw [if_pos hodd, ih (n / 2) (by omega)]
        constructor
        · rintro ⟨k, hk⟩
          refine ⟨k + 1, ?_⟩
          rw [pow_succ]
          have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
          omega
        · rintro ⟨k, hk⟩
          rcases k with _ | k
          · simp at hk; omega
          · refine ⟨k, ?_⟩
            rw [pow_succ] at hk
            have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
            omega
      · rw [if_neg hodd]
        constructor
        · intro h; exact absurd h (by decide)
        · rintro ⟨k, hk⟩
          exfalso
          rcases k with _ | k
          · simp at hk; omega
          · rw [pow_succ] at hk
            have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
            omega

theorem final (A : PowerSeries ℤ) (h : IsA222014 A) (n : ℕ) :
    PowerSeries.coeff n A % 2 = 1 ↔ ∃ k : ℕ, n = 2 ^ k - 1 := by
  have hk := key A h
  set B := PowerSeries.map (Int.castRingHom (ZMod 2)) A with hB
  have hrec := rec_coeff B hk
  have hb : ∀ m, PowerSeries.coeff m B = ((PowerSeries.coeff m A : ℤ) : ZMod 2) := by
    intro m; simp [hB, PowerSeries.coeff_map]
  have h0 : PowerSeries.coeff 0 B = 1 := by rw [hrec 0]; simp
  have key2 : ∀ z : ℤ, ((z : ZMod 2) = 1 ↔ z % 2 = 1) := by
    intro z
    have hz : (z : ZMod 2) = ((z % 2 : ℤ) : ZMod 2) := (ZMod.intCast_mod z 2).symm
    rcases Int.emod_two_eq_zero_or_one z with h | h
    · rw [hz, h]
      constructor
      · intro hh; exfalso; revert hh; decide
      · intro hh; omega
    · rw [hz, h]; simp
  rw [← odd_iff (fun m => PowerSeries.coeff m B) h0 hrec n]
  simp only [hb]
  exact (key2 _).symm

end OMA.S_oeis_a222014

theorem OMA.solution : type_of% @OMA.S_oeis_a222014.main := by
  intro A hA n
  exact OMA.S_oeis_a222014.final A hA n
