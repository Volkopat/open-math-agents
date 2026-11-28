import OMAStatements.S_oeis_a337948
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace OMA.P_oeis_a337948

open OMA.S_oeis_a337948

private lemma two_pow_odd_add_one_mod3 (m : ℕ) (hm : m % 2 = 1) :
    ((2 : ZMod 3) ^ m + 1) = 0 := by
  rcases Nat.even_or_odd m with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · omega
  · have hsq : (2 : ZMod 3) ^ 2 = 1 := by decide
    rw [pow_succ, pow_mul, hsq, one_pow, one_mul]
    decide

private lemma coeff_inv_of_dvd_supp {p : ℕ} {g h : PowerSeries (ZMod 3)}
    (hg0 : PowerSeries.constantCoeff g = 1) (hgh : g * h = 1)
    (hsupp : ∀ n, ¬ p ∣ n → PowerSeries.coeff n g = 0) :
    ∀ n, ¬ p ∣ n → PowerSeries.coeff n h = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hnd
    have h0 := congrArg (PowerSeries.coeff n) hgh
    have hn0 : n ≠ 0 := by rintro rfl; exact hnd (dvd_zero p)
    rw [PowerSeries.coeff_one, if_neg hn0, PowerSeries.coeff_mul,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ
          (fun i j => PowerSeries.coeff i g * PowerSeries.coeff j h),
        Finset.sum_range_succ'] at h0
    have htail : ∑ k ∈ Finset.range n,
        PowerSeries.coeff (k + 1) g * PowerSeries.coeff (n - (k + 1)) h = 0 := by
      refine Finset.sum_eq_zero fun k hk => ?_
      rw [Finset.mem_range] at hk
      by_cases hd : p ∣ k + 1
      · have hnd' : ¬ p ∣ n - (k + 1) := by
          intro hd'
          have : p ∣ (n - (k + 1)) + (k + 1) := dvd_add hd' hd
          rw [Nat.sub_add_cancel (by omega)] at this
          exact hnd this
        rw [ih (n - (k + 1)) (by omega) hnd', mul_zero]
      · rw [hsupp (k + 1) hd, zero_mul]
    rw [htail, zero_add, Nat.sub_zero, PowerSeries.coeff_zero_eq_constantCoeff, hg0, one_mul] at h0
    exact h0

private lemma coeff_mul_of_dvd_supp {p : ℕ} {g h : PowerSeries (ZMod 3)}
    (hg : ∀ n, ¬ p ∣ n → PowerSeries.coeff n g = 0)
    (hh : ∀ n, ¬ p ∣ n → PowerSeries.coeff n h = 0) :
    ∀ n, ¬ p ∣ n → PowerSeries.coeff n (g * h) = 0 := by
  intro n hnd
  rw [PowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun q hq => ?_
  rw [Finset.mem_antidiagonal] at hq
  by_cases hd : p ∣ q.1
  · have hnd2 : ¬ p ∣ q.2 := by
      intro hd2; exact hnd (by rw [← hq]; exact dvd_add hd hd2)
    rw [hh q.2 hnd2, mul_zero]
  · rw [hg q.1 hd, zero_mul]

theorem solution : type_of% @OMA.S_oeis_a337948.main := by
  intro A S hS0 hS hEq
  let φ : PowerSeries ℤ →+* PowerSeries (ZMod 3) := PowerSeries.map (Int.castRingHom (ZMod 3))
  let a3 : PowerSeries (ZMod 3) := φ A
  let s3 : PowerSeries (ZMod 3) := φ S
  have hs3_0 : PowerSeries.constantCoeff s3 = 1 := by
    dsimp only [s3, φ]
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
        PowerSeries.coeff_zero_eq_constantCoeff, hS0, map_one]
  -- Every coefficient of s3 at index not divisible by 4 is 0!
  have hs3_supp : ∀ r : ℕ, ¬ 4 ∣ r → PowerSeries.coeff r s3 = 0 := by
    intro r hr4
    have hr1 : 1 ≤ r := by
      by_contra h0
      have : r = 0 := by omega
      subst this; exact hr4 (dvd_zero 4)
    dsimp only [s3, φ]
    rw [PowerSeries.coeff_map, hS r hr1, map_sum]
    refine Finset.sum_eq_zero fun m _ => ?_
    split_ifs with hsq
    · by_cases hm : m % 2 = 1
      · have hcast : (Int.castRingHom (ZMod 3)) ((2 : ℤ) ^ m + 1) = (2 : ZMod 3) ^ m + 1 := by
          simp [map_add, map_pow]
        rw [map_mul, map_mul, hcast, two_pow_odd_add_one_mod3 m hm, mul_zero, zero_mul]
      · exfalso
        apply hr4
        have hm2 : 2 ∣ m := ⟨m / 2, by omega⟩
        rcases hm2 with ⟨q, rfl⟩
        exact ⟨q ^ 2, by rw [← hsq]; ring⟩
    · exact map_zero _
  -- Every coefficient of φ (-X * S') at index not divisible by 4 is 0!
  let d3 : PowerSeries (ZMod 3) := φ (-PowerSeries.X * PowerSeries.derivative ℤ S)
  have hd3_supp : ∀ r : ℕ, ¬ 4 ∣ r → PowerSeries.coeff r d3 = 0 := by
    intro r hr4
    have hr1 : 1 ≤ r := by
      by_contra h0
      have : r = 0 := by omega
      subst this; exact hr4 (dvd_zero 4)
    dsimp only [d3, φ]
    rw [PowerSeries.coeff_map, neg_mul, map_neg,
        ← pow_one (PowerSeries.X : PowerSeries ℤ), PowerSeries.coeff_X_pow_mul',
        if_pos hr1, PowerSeries.coeff_derivative, show r - 1 + 1 = r by omega,
        map_neg, map_mul]
    have hs0 : (Int.castRingHom (ZMod 3)) (PowerSeries.coeff r S) = 0 := by
      have := hs3_supp r hr4
      dsimp only [s3, φ] at this
      rwa [PowerSeries.coeff_map] at this
    rw [hs0, zero_mul, neg_zero]
  -- Invert s3 in PowerSeries (ZMod 3)
  have hs3_unit : IsUnit s3 := PowerSeries.isUnit_iff_constantCoeff.mpr (by rw [hs3_0]; exact isUnit_one)
  let t3 : PowerSeries (ZMod 3) := Ring.inverse s3
  have hs3t3 : s3 * t3 = 1 := Ring.mul_inverse_cancel s3 hs3_unit
  have ht3_supp : ∀ r : ℕ, ¬ 4 ∣ r → PowerSeries.coeff r t3 = 0 :=
    coeff_inv_of_dvd_supp hs3_0 hs3t3 hs3_supp
  have ha3_eq : a3 = d3 * t3 := by
    have h := congrArg φ hEq
    rw [map_mul] at h
    calc a3 = a3 * 1 := (mul_one _).symm
      _ = a3 * (s3 * t3) := by rw [hs3t3]
      _ = (a3 * s3) * t3 := by ring
      _ = d3 * t3 := by rw [h]
  have ha3_supp : ∀ r : ℕ, ¬ 4 ∣ r → (3 : ℤ) ∣ PowerSeries.coeff r A := by
    intro r hr4
    have h0 : ((PowerSeries.coeff r A : ℤ) : ZMod 3) = 0 := by
      have h1 : ((PowerSeries.coeff r A : ℤ) : ZMod 3) = PowerSeries.coeff r a3 := by
        dsimp only [a3, φ]; rw [PowerSeries.coeff_map]; rfl
      rw [h1, ha3_eq]
      exact coeff_mul_of_dvd_supp hd3_supp ht3_supp r hr4
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp h0
  intro n
  exact ⟨ha3_supp (4 * n + 1) (by omega),
         ha3_supp (4 * n + 2) (by omega),
         ha3_supp (4 * n + 3) (by omega)⟩

end OMA.P_oeis_a337948

theorem OMA.solution : type_of% @OMA.S_oeis_a337948.main := OMA.P_oeis_a337948.solution
