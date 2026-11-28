import OMAStatements.S_oeis_a375449
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace OeisA375449Proof

open OMA.S_oeis_a375449
open Classical

private noncomputable def xDeriv2 (F : PowerSeries (ZMod 2)) : PowerSeries (ZMod 2) :=
  PowerSeries.mk fun n => (n : ZMod 2) * PowerSeries.coeff n F

private lemma map_xDeriv (F : PowerSeries ℤ) :
    PowerSeries.map (Int.castRingHom (ZMod 2)) (xDeriv F) =
      xDeriv2 (PowerSeries.map (Int.castRingHom (ZMod 2)) F) := by
  ext n
  simp [xDeriv, xDeriv2]

private def isTarget (n : ℕ) : Prop :=
  n = 1 ∨ ∃ k : ℕ, 1 < k ∧ (n = 2 ^ k - 2 ∨ n = 2 ^ k - 1)

private noncomputable def modelB : PowerSeries (ZMod 2) :=
  PowerSeries.mk fun n => if isTarget n then 1 else 0

private noncomputable def seriesR : PowerSeries (ZMod 2) :=
  PowerSeries.mk fun n => if n = 0 then 0 else 1

private lemma isTarget_zero : ¬ isTarget 0 := by
  rintro (h | ⟨k, hk, h | h⟩)
  · omega
  · have : 4 ≤ 2 ^ k := by
      calc 4 = 2 ^ 2 := by decide
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk
    omega
  · have : 4 ≤ 2 ^ k := by
      calc 4 = 2 ^ 2 := by decide
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk
    omega

private lemma isTarget_even_iff (m : ℕ) (_hm : 1 ≤ m) :
    isTarget (2 * m) ↔ Odd m ∧ isTarget m := by
  constructor
  · rintro (h1 | ⟨k, hk, h | h⟩)
    · omega
    · have hk4 : 4 ≤ 2 ^ k := by
        calc 4 = 2 ^ 2 := by decide
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk
      have hpow : 2 ^ k = 2 * 2 ^ (k - 1) := by
        conv_lhs => rw [show k = (k - 1) + 1 by omega, pow_succ']
      have hm_eq : m = 2 ^ (k - 1) - 1 := by omega
      have hpow_ge2 : 2 ≤ 2 ^ (k - 1) := by
        calc 2 = 2 ^ 1 := by decide
          _ ≤ 2 ^ (k - 1) := Nat.pow_le_pow_right (by decide) (by omega)
      have hodd : Odd m := by
        rw [hm_eq, Nat.odd_iff]
        have h2 : 2 ∣ 2 ^ (k - 1) := dvd_pow_self 2 (by omega)
        rcases h2 with ⟨t, ht⟩
        omega
      refine ⟨hodd, ?_⟩
      by_cases hk2 : k = 2
      · left; subst hk2; simp [hm_eq]
      · right; exact ⟨k - 1, by omega, Or.inr hm_eq⟩
    · have hk4 : 4 ≤ 2 ^ k := by
        calc 4 = 2 ^ 2 := by decide
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk
      have h2 : 2 ∣ 2 ^ k := dvd_pow_self 2 (by omega)
      rcases h2 with ⟨t, ht⟩
      omega
  · rintro ⟨hodd, h1 | ⟨k, hk, h | h⟩⟩
    · right; exact ⟨2, by decide, Or.inl (by omega)⟩
    · have hk4 : 4 ≤ 2 ^ k := by
        calc 4 = 2 ^ 2 := by decide
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk
      have h2 : 2 ∣ 2 ^ k := dvd_pow_self 2 (by omega)
      rcases h2 with ⟨t, ht⟩
      rw [Nat.odd_iff] at hodd
      omega
    · right
      refine ⟨k + 1, by omega, Or.inl ?_⟩
      have hk4 : 4 ≤ 2 ^ k := by
        calc 4 = 2 ^ 2 := by decide
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk
      rw [pow_succ']
      omega

private lemma isTarget_odd_succ_iff (m : ℕ) (hm : 1 ≤ m) :
    isTarget (2 * m) ↔ isTarget (2 * m + 1) := by
  constructor
  · rintro (h1 | ⟨k, hk, h | h⟩)
    · omega
    · right; exact ⟨k, hk, Or.inr (by
        have : 4 ≤ 2 ^ k := by
          calc 4 = 2 ^ 2 := by decide
            _ ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk
        omega)⟩
    · have h2 : 2 ∣ 2 ^ k := dvd_pow_self 2 (by omega)
      have : 4 ≤ 2 ^ k := by
        calc 4 = 2 ^ 2 := by decide
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk
      rcases h2 with ⟨t, ht⟩; omega
  · rintro (h1 | ⟨k, hk, h | h⟩)
    · omega
    · have h2 : 2 ∣ 2 ^ k := dvd_pow_self 2 (by omega)
      have : 4 ≤ 2 ^ k := by
        calc 4 = 2 ^ 2 := by decide
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk
      rcases h2 with ⟨t, ht⟩; omega
    · right; exact ⟨k, hk, Or.inl (by
        have : 4 ≤ 2 ^ k := by
          calc 4 = 2 ^ 2 := by decide
            _ ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk
        omega)⟩

private lemma cancel_coeff0_one (U F : PowerSeries (ZMod 2))
    (hU0 : PowerSeries.coeff 0 U = 1) (hUF : U * F = 0) : F = 0 := by
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hn := congrArg (PowerSeries.coeff n) hUF
    rw [PowerSeries.coeff_mul, map_zero,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => PowerSeries.coeff i U * PowerSeries.coeff j F),
      Finset.sum_range_succ', Nat.sub_zero, hU0, one_mul] at hn
    have htail : ∑ k ∈ Finset.range n,
        PowerSeries.coeff (k + 1) U * PowerSeries.coeff (n - (k + 1)) F = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      rw [Finset.mem_range] at hk
      rw [ih (n - (k + 1)) (by omega), map_zero, mul_zero]
    rw [htail, zero_add] at hn
    simpa using hn

private lemma seriesR_mul_one_add_modelB :
    seriesR * (1 + modelB) = xDeriv2 modelB := by
  have h1 : (1 + PowerSeries.X : PowerSeries (ZMod 2)) * seriesR = PowerSeries.X := by
    ext n
    rw [add_mul, one_mul, map_add,
      show PowerSeries.X * seriesR = PowerSeries.X ^ 1 * seriesR by ring,
      PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X]
    match n with
    | 0 => simp [seriesR]
    | 1 => simp [seriesR]
    | m + 2 =>
      simp only [seriesR, PowerSeries.coeff_mk, show m + 2 ≠ 0 by omega,
        show 1 ≤ m + 2 by omega, show m + 2 - 1 ≠ 0 by omega, show m + 2 ≠ 1 by omega, ↓reduceIte]
      decide
  have h2 : (1 + PowerSeries.X : PowerSeries (ZMod 2)) * xDeriv2 modelB =
      PowerSeries.X * (1 + modelB) := by
    ext n
    rw [add_mul, one_mul, map_add,
      show PowerSeries.X * xDeriv2 modelB = PowerSeries.X ^ 1 * xDeriv2 modelB by ring,
      show PowerSeries.X * (1 + modelB) = PowerSeries.X ^ 1 * (1 + modelB) by ring,
      PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul']
    match n with
    | 0 => simp [xDeriv2]
    | 1 =>
      simp only [xDeriv2, modelB, PowerSeries.coeff_mk, show 1 ≤ 1 by decide, ↓reduceIte,
        Nat.sub_self, map_add, PowerSeries.coeff_one, isTarget_zero]
      have h1t : isTarget 1 := Or.inl rfl
      simp [h1t]
    | m + 2 =>
      simp only [show 1 ≤ m + 2 by omega, ↓reduceIte, show m + 2 - 1 = m + 1 by omega,
        map_add, PowerSeries.coeff_one, show m + 1 ≠ 0 by omega, zero_add,
        xDeriv2, modelB, PowerSeries.coeff_mk]
      rcases Nat.even_or_odd (m + 1) with ⟨r, hr⟩ | ⟨r, hr⟩
      · have hr1 : 1 ≤ r := by omega
        have hm1 : ((m + 1 : ℕ) : ZMod 2) = 0 :=
          (ZMod.natCast_eq_zero_iff (m + 1) 2).mpr ⟨r, by omega⟩
        have hm2 : ((m + 2 : ℕ) : ZMod 2) = 1 := by
          rw [show m + 2 = 2 * r + 1 by omega]; push_cast
          rw [show (2 : ZMod 2) = 0 by decide]; ring
        rw [hm1, hm2, zero_mul, add_zero, one_mul]
        have hiff : isTarget (m + 2) ↔ isTarget (m + 1) := by
          rw [show m + 1 = 2 * r by omega, show m + 2 = 2 * r + 1 by omega]
          exact (isTarget_odd_succ_iff r hr1).symm
        simp [hiff]
      · have hm1 : ((m + 1 : ℕ) : ZMod 2) = 1 := by
          rw [hr]; push_cast; rw [show (2 : ZMod 2) = 0 by decide]; ring
        have hm2 : ((m + 2 : ℕ) : ZMod 2) = 0 :=
          (ZMod.natCast_eq_zero_iff (m + 2) 2).mpr ⟨r + 1, by omega⟩
        rw [hm1, hm2, zero_mul, zero_add, one_mul]
  have hprod : (1 + PowerSeries.X : PowerSeries (ZMod 2)) *
      (seriesR * (1 + modelB) - xDeriv2 modelB) = 0 := by
    calc (1 + PowerSeries.X) * (seriesR * (1 + modelB) - xDeriv2 modelB)
        = ((1 + PowerSeries.X) * seriesR) * (1 + modelB) -
            (1 + PowerSeries.X) * xDeriv2 modelB := by ring
      _ = PowerSeries.X * (1 + modelB) - PowerSeries.X * (1 + modelB) := by rw [h1, h2]
      _ = 0 := sub_self _
  have hU0 : PowerSeries.coeff 0 (1 + PowerSeries.X : PowerSeries (ZMod 2)) = 1 := by simp
  exact sub_eq_zero.mp (cancel_coeff0_one _ _ hU0 hprod)

private lemma coeff_even_A_mul_xDeriv_mod2 (A : PowerSeries ℤ) (m : ℕ) :
    ((PowerSeries.coeff (2 * m) (A * xDeriv A) : ℤ) : ZMod 2) =
      (m : ZMod 2) * ((PowerSeries.coeff m A : ℤ) : ZMod 2) := by
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => PowerSeries.coeff i A * PowerSeries.coeff j (xDeriv A))]
  simp only [xDeriv, PowerSeries.coeff_mk, Int.cast_sum, Int.cast_mul, Int.cast_natCast]
  have hsplit :
      ∑ i ∈ Finset.range (2 * m + 1),
        ((PowerSeries.coeff i A : ℤ) : ZMod 2) *
          (((2 * m - i : ℕ) : ZMod 2) * ((PowerSeries.coeff (2 * m - i) A : ℤ) : ZMod 2)) =
      (∑ i ∈ Finset.range m,
        (((PowerSeries.coeff i A : ℤ) : ZMod 2) *
            (((2 * m - i : ℕ) : ZMod 2) * ((PowerSeries.coeff (2 * m - i) A : ℤ) : ZMod 2)) +
         ((PowerSeries.coeff (2 * m - i) A : ℤ) : ZMod 2) *
            ((i : ZMod 2) * ((PowerSeries.coeff i A : ℤ) : ZMod 2)))) +
      ((PowerSeries.coeff m A : ℤ) : ZMod 2) *
        ((m : ZMod 2) * ((PowerSeries.coeff m A : ℤ) : ZMod 2)) := by
    rw [show 2 * m + 1 = (m + 1) + m by omega, Finset.sum_range_add, Finset.sum_range_succ]
    have hrev :
        ∑ x ∈ Finset.range m,
          ((PowerSeries.coeff (m + 1 + x) A : ℤ) : ZMod 2) *
            (((2 * m - (m + 1 + x) : ℕ) : ZMod 2) *
              ((PowerSeries.coeff (2 * m - (m + 1 + x)) A : ℤ) : ZMod 2)) =
        ∑ i ∈ Finset.range m,
          ((PowerSeries.coeff (2 * m - i) A : ℤ) : ZMod 2) *
            ((i : ZMod 2) * ((PowerSeries.coeff i A : ℤ) : ZMod 2)) := by
      apply Finset.sum_nbij (fun x => m - 1 - x)
      · intro x hx; rw [Finset.mem_range] at hx ⊢; omega
      · intro a ha b hb hab; simp only [Finset.coe_range, Set.mem_Iio] at ha hb; simp only at hab; omega
      · intro i hi
        simp only [Finset.coe_range, Set.mem_Iio] at hi
        exact ⟨m - 1 - i, by simp only [Finset.coe_range, Set.mem_Iio]; omega, by simp only; omega⟩
      · intro x hx
        rw [Finset.mem_range] at hx
        simp only [show 2 * m - (m - 1 - x) = m + 1 + x by omega,
          show 2 * m - (m + 1 + x) = m - 1 - x by omega]
    rw [hrev, show 2 * m - m = m by omega, Finset.sum_add_distrib]
    ring
  rw [hsplit]
  have hpair0 : ∀ i ∈ Finset.range m,
      ((PowerSeries.coeff i A : ℤ) : ZMod 2) *
          (((2 * m - i : ℕ) : ZMod 2) * ((PowerSeries.coeff (2 * m - i) A : ℤ) : ZMod 2)) +
       ((PowerSeries.coeff (2 * m - i) A : ℤ) : ZMod 2) *
          ((i : ZMod 2) * ((PowerSeries.coeff i A : ℤ) : ZMod 2)) = 0 := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hsum2m : (((2 * m - i : ℕ) : ZMod 2) + (i : ZMod 2)) = 0 := by
      rw [← Nat.cast_add, show 2 * m - i + i = 2 * m by omega, Nat.cast_mul,
        show ((2 : ℕ) : ZMod 2) = 0 by decide, zero_mul]
    calc ((PowerSeries.coeff i A : ℤ) : ZMod 2) *
            (((2 * m - i : ℕ) : ZMod 2) * ((PowerSeries.coeff (2 * m - i) A : ℤ) : ZMod 2)) +
          ((PowerSeries.coeff (2 * m - i) A : ℤ) : ZMod 2) *
            ((i : ZMod 2) * ((PowerSeries.coeff i A : ℤ) : ZMod 2))
        = ((PowerSeries.coeff i A : ℤ) : ZMod 2) * ((PowerSeries.coeff (2 * m - i) A : ℤ) : ZMod 2) *
            (((2 * m - i : ℕ) : ZMod 2) + (i : ZMod 2)) := by ring
      _ = 0 := by rw [hsum2m, mul_zero]
  rw [Finset.sum_eq_zero hpair0, zero_add]
  have hsq : ∀ z : ZMod 2, z * z = z := by decide
  calc ((PowerSeries.coeff m A : ℤ) : ZMod 2) * ((m : ZMod 2) * ((PowerSeries.coeff m A : ℤ) : ZMod 2))
      = (m : ZMod 2) * (((PowerSeries.coeff m A : ℤ) : ZMod 2) * ((PowerSeries.coeff m A : ℤ) : ZMod 2)) := by ring
    _ = (m : ZMod 2) * ((PowerSeries.coeff m A : ℤ) : ZMod 2) := by rw [hsq]

private lemma map_A_eq_modelB {A : PowerSeries ℤ} (hA : IsA375449 A) :
    PowerSeries.map (Int.castRingHom (ZMod 2)) A = modelB := by
  let A2 : PowerSeries (ZMod 2) := PowerSeries.map (Int.castRingHom (ZMod 2)) A
  change A2 = modelB
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero =>
      simp only [A2, modelB, PowerSeries.coeff_map, PowerSeries.coeff_mk, Int.coe_castRingHom, hA.1,
        Int.cast_zero, if_neg isTarget_zero]
    | succ n' =>
      set n := n' + 1
      obtain ⟨Q, hQeq, hQn⟩ := hA.2 n (by omega)
      rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
      · have hm1 : 1 ≤ m := by omega
        have hn2m : n = 2 * m := by omega
        -- Unfold Q = xDeriv A + C n * A * Q twice
        have hQ1 : Q = xDeriv A + PowerSeries.C (n : ℤ) * (A * Q) := by
          have : Q - PowerSeries.C (n : ℤ) * (A * Q) = xDeriv A := by
            calc Q - PowerSeries.C (n : ℤ) * (A * Q)
                = Q * (1 - PowerSeries.C (n : ℤ) * A) := by ring
              _ = xDeriv A := hQeq
          linear_combination this
        have hQ2 : Q = xDeriv A + PowerSeries.C (n : ℤ) * (A * xDeriv A) +
            PowerSeries.C ((n : ℤ) ^ 2) * (A ^ 2 * Q) := by
          conv_lhs => rw [hQ1]
          conv_lhs => arg 2; arg 2; arg 2; rw [hQ1]
          rw [map_pow]
          ring
        have hc := congrArg (PowerSeries.coeff n) hQ2
        simp only [hQn, map_add, PowerSeries.coeff_C_mul] at hc
        rw [show PowerSeries.coeff n (xDeriv A) = (n : ℤ) * PowerSeries.coeff n A by simp [xDeriv]] at hc
        have hc' : (n : ℤ) * (n : ℤ) ^ n =
            (n : ℤ) * (PowerSeries.coeff n A + PowerSeries.coeff n (A * xDeriv A) +
              (n : ℤ) * PowerSeries.coeff n (A ^ 2 * Q)) := by
          have hpow : (n : ℤ) ^ (n + 1) = (n : ℤ) * (n : ℤ) ^ n := by rw [pow_succ']
          rw [hpow] at hc
          linear_combination hc
        have hdiv : (n : ℤ) ^ n = PowerSeries.coeff n A + PowerSeries.coeff n (A * xDeriv A) +
            (n : ℤ) * PowerSeries.coeff n (A ^ 2 * Q) :=
          mul_left_cancel₀ (by positivity : (n : ℤ) ≠ 0) hc'
        have hmod2 := congrArg (Int.castRingHom (ZMod 2)) hdiv
        simp only [map_pow, map_add, map_mul, Int.coe_castRingHom, Int.cast_natCast] at hmod2
        have hn0 : (n : ZMod 2) = 0 :=
          (ZMod.natCast_eq_zero_iff n 2).mpr ⟨m, by omega⟩
        rw [hn0, zero_pow (by omega : n ≠ 0), zero_mul, add_zero] at hmod2
        have hconv : ((PowerSeries.coeff n (A * xDeriv A) : ℤ) : ZMod 2) =
            (m : ZMod 2) * ((PowerSeries.coeff m A : ℤ) : ZMod 2) := by
          rw [hn2m]; exact coeff_even_A_mul_xDeriv_mod2 A m
        rw [hconv] at hmod2
        have hAn : PowerSeries.coeff n A2 = (m : ZMod 2) * PowerSeries.coeff m A2 := by
          simp only [A2, PowerSeries.coeff_map, Int.coe_castRingHom]
          have hneg : ∀ x : ZMod 2, -x = x := by decide
          calc ((PowerSeries.coeff n A : ℤ) : ZMod 2)
              = -((m : ZMod 2) * ((PowerSeries.coeff m A : ℤ) : ZMod 2)) := by
                linear_combination -hmod2
            _ = (m : ZMod 2) * ((PowerSeries.coeff m A : ℤ) : ZMod 2) := hneg _
        rw [hAn, ih m (by omega), modelB, PowerSeries.coeff_mk, PowerSeries.coeff_mk,
          hn2m, isTarget_even_iff m hm1]
        by_cases hodd : Odd m
        · have hm1_2 : (m : ZMod 2) = 1 := by
            rcases hodd with ⟨r, rfl⟩; push_cast
            rw [show (2 : ZMod 2) = 0 by decide]; ring
          rw [hm1_2, one_mul]; simp [hodd]
        · have hm0_2 : (m : ZMod 2) = 0 := by
            rw [ZMod.natCast_eq_zero_iff]; rw [Nat.not_odd_iff_even] at hodd
            exact hodd.two_dvd
          rw [hm0_2, zero_mul]; simp [hodd]
      · -- Odd n: reduce Q * (1 - C n * A) = xDeriv A directly mod 2
        let Q2 : PowerSeries (ZMod 2) := PowerSeries.map (Int.castRingHom (ZMod 2)) Q
        have hn1 : (n : ZMod 2) = 1 := by
          rw [hm]; push_cast; rw [show (2 : ZMod 2) = 0 by decide]; ring
        have hQ2eq : Q2 * (1 + A2) = xDeriv2 A2 := by
          have h := congrArg (PowerSeries.map (Int.castRingHom (ZMod 2))) hQeq
          simp only [map_mul, map_sub, map_one, PowerSeries.map_C, Int.coe_castRingHom,
            Int.cast_natCast, hn1, map_one, one_mul, map_xDeriv] at h
          have hsub : (1 : PowerSeries (ZMod 2)) - A2 = 1 + A2 := by
            ext k; simp only [map_sub, map_add]; exact by
              have : ∀ a b : ZMod 2, a - b = a + b := by decide
              exact this _ _
          rw [hsub] at h
          exact h
        have hQ2n : PowerSeries.coeff n Q2 = 1 := by
          simp only [Q2, PowerSeries.coeff_map, Int.coe_castRingHom, hQn, Int.cast_pow,
            Int.cast_natCast, hn1, one_pow]
        have hQ2_0 : PowerSeries.coeff 0 Q2 = 0 := by
          have h0 := congrArg (PowerSeries.coeff 0) hQ2eq
          rw [PowerSeries.coeff_mul, Finset.Nat.antidiagonal_zero, Finset.sum_singleton] at h0
          have h1A0 : PowerSeries.coeff 0 (1 + A2) = 1 := by rw [map_add, PowerSeries.coeff_one, if_pos rfl]; simp only [A2, PowerSeries.coeff_map, Int.coe_castRingHom, hA.1, Int.cast_zero, add_zero]
          rw [h1A0, mul_one] at h0
          simpa [xDeriv2] using h0
        have hQ2_agree : ∀ j < n, PowerSeries.coeff j Q2 = PowerSeries.coeff j seriesR := by
          intro j
          induction j using Nat.strong_induction_on with
          | h j ihj =>
            intro hj
            have hL := congrArg (PowerSeries.coeff j) hQ2eq
            have hR := congrArg (PowerSeries.coeff j) seriesR_mul_one_add_modelB
            have hRHS : PowerSeries.coeff j (xDeriv2 A2) = PowerSeries.coeff j (xDeriv2 modelB) := by
              simp only [xDeriv2, PowerSeries.coeff_mk, ih j hj]
            have hEq := hL.trans (hRHS.trans hR.symm)
            rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul,
              Finset.Nat.sum_antidiagonal_eq_sum_range_succ
                (fun a b => PowerSeries.coeff a Q2 * PowerSeries.coeff b (1 + A2)),
              Finset.Nat.sum_antidiagonal_eq_sum_range_succ
                (fun a b => PowerSeries.coeff a seriesR * PowerSeries.coeff b (1 + modelB)),
              Finset.sum_range_succ, Finset.sum_range_succ, Nat.sub_self] at hEq
            have h1A0 : PowerSeries.coeff 0 (1 + A2) = 1 := by rw [map_add, PowerSeries.coeff_one, if_pos rfl]; simp only [A2, PowerSeries.coeff_map, Int.coe_castRingHom, hA.1, Int.cast_zero, add_zero]
            have h1B0 : PowerSeries.coeff 0 (1 + modelB) = 1 := by rw [map_add, PowerSeries.coeff_one, if_pos rfl]; simp only [modelB, PowerSeries.coeff_mk, if_neg isTarget_zero, add_zero]
            rw [h1A0, h1B0, mul_one, mul_one] at hEq
            have hsum_eq :
                ∑ i ∈ Finset.range j, PowerSeries.coeff i Q2 * PowerSeries.coeff (j - i) (1 + A2) =
                ∑ i ∈ Finset.range j, PowerSeries.coeff i seriesR * PowerSeries.coeff (j - i) (1 + modelB) := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [Finset.mem_range] at hi
              rw [ihj i hi (by omega), map_add, map_add, ih (j - i) (by omega)]
            rw [hsum_eq] at hEq
            exact add_left_cancel hEq
        have hLn := congrArg (PowerSeries.coeff n) hQ2eq
        have hRn := congrArg (PowerSeries.coeff n) seriesR_mul_one_add_modelB
        rw [PowerSeries.coeff_mul,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ
            (fun a b => PowerSeries.coeff a Q2 * PowerSeries.coeff b (1 + A2)),
          Finset.sum_range_succ, Finset.sum_range_succ', Nat.sub_zero, Nat.sub_self,
          hQ2_0, zero_mul, add_zero] at hLn
        rw [PowerSeries.coeff_mul,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ
            (fun a b => PowerSeries.coeff a seriesR * PowerSeries.coeff b (1 + modelB)),
          Finset.sum_range_succ, Finset.sum_range_succ', Nat.sub_zero, Nat.sub_self,
          show PowerSeries.coeff 0 seriesR = 0 by simp [seriesR], zero_mul, add_zero] at hRn
        have h1A0 : PowerSeries.coeff 0 (1 + A2) = 1 := by rw [map_add, PowerSeries.coeff_one, if_pos rfl]; simp only [A2, PowerSeries.coeff_map, Int.coe_castRingHom, hA.1, Int.cast_zero, add_zero]
        have h1B0 : PowerSeries.coeff 0 (1 + modelB) = 1 := by rw [map_add, PowerSeries.coeff_one, if_pos rfl]; simp only [modelB, PowerSeries.coeff_mk, if_neg isTarget_zero, add_zero]
        have hRn_val : PowerSeries.coeff n seriesR = 1 := by simp [seriesR, show n ≠ 0 by omega]
        rw [h1A0, mul_one, hQ2n] at hLn
        rw [h1B0, mul_one, hRn_val] at hRn
        have hmid_eq :
            ∑ k ∈ Finset.range (n - 1),
              PowerSeries.coeff (k + 1) Q2 * PowerSeries.coeff (n - (k + 1)) (1 + A2) =
            ∑ k ∈ Finset.range (n - 1),
              PowerSeries.coeff (k + 1) seriesR * PowerSeries.coeff (n - (k + 1)) (1 + modelB) := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [Finset.mem_range] at hk
          rw [hQ2_agree (k + 1) (by omega), map_add, map_add, ih (n - (k + 1)) (by omega)]
        rw [show n' = n - 1 by omega] at hLn hRn
        have hD_eq : PowerSeries.coeff n (xDeriv2 A2) = PowerSeries.coeff n (xDeriv2 modelB) := by
          rw [← hLn, ← hRn, hmid_eq]
        simp only [xDeriv2, PowerSeries.coeff_mk, hn1, one_mul] at hD_eq
        exact hD_eq

end OeisA375449Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a375449.main := by
  intro A hA n hn
  have hmap := OeisA375449Proof.map_A_eq_modelB hA
  have h := congrArg (PowerSeries.coeff n) hmap
  simp only [PowerSeries.coeff_map, Int.coe_castRingHom, OeisA375449Proof.modelB, PowerSeries.coeff_mk] at h
  have hiff : OeisA375449Proof.isTarget n ↔ ∃ k : ℕ, 1 < k ∧ (n = 2 ^ k - 2 ∨ n = 2 ^ k - 1) := by
    unfold OeisA375449Proof.isTarget
    constructor
    · rintro (h1 | h2)
      · omega
      · exact h2
    · intro h2; exact Or.inr h2
  rw [Int.odd_iff]
  constructor
  · intro hodd
    by_contra hnot
    rw [if_neg (fun ht => hnot (hiff.mp ht))] at h
    have h2 := (ZMod.intCast_zmod_eq_zero_iff_dvd (PowerSeries.coeff n A) 2).mp h
    omega
  · intro hex
    rw [if_pos (hiff.mpr hex)] at h
    have hne : ((PowerSeries.coeff n A : ℤ) : ZMod 2) ≠ 0 := by rw [h]; decide
    have hndvd : ¬ (((2 : ℕ) : ℤ) ∣ PowerSeries.coeff n A) := by
      intro hdvd; exact hne ((ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mpr hdvd)
    omega
