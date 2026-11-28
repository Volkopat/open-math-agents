import OMAStatements.S_oeis_a000182
import Mathlib.Tactic.LinearCombination
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Algebra.Polynomial.Derivation
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Tactic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors

/-
Tangent-number congruences follow by lifting powers of the tangent derivation.
Coefficientwise Euler products give integrality. Weighted walks give the
classical Stieltjes fraction, which can be transformed in pairs of tails.
-/

namespace TangentConjecture

open PowerSeries

abbrev Series := PowerSeries ℚ

theorem cancel_right {A B P : Series} (hP : constantCoeff P ≠ 0)
    (h : A * P = B * P) : A = B := by
  simpa only [mul_assoc, PowerSeries.mul_inv_cancel _ hP, mul_one]
    using congrArg (fun z : Series => z * P⁻¹) h

theorem convert_step (m S T : Series)
    (hS : constantCoeff S ≠ 0) (hT : constantCoeff T ≠ 0)
    (hST : S * T = T - (m * (m + 1)) * X) :
    let R := T - (m + 1) * X
    let V := 1 - (m ^ 2 - 1) * X * R⁻¹
    1 - (m - 1) * X - ((m - 1) * m) * X * S⁻¹ =
      1 + X - m ^ 2 * X * V⁻¹ := by
  let R : Series := T - (m + 1) * X
  let V : Series := 1 - (m ^ 2 - 1) * X * R⁻¹
  change _ = 1 + X - m ^ 2 * X * V⁻¹
  have hR : constantCoeff R ≠ 0 := by simpa [R] using hT
  have hV : constantCoeff V ≠ 0 := by simp [V]
  have hTR : T * (S + m - 1) = m * R := by
    dsimp [R]
    linear_combination hST
  have hVR : V * R = R - (m ^ 2 - 1) * X := by
    simp only [V, sub_mul, one_mul, mul_assoc, PowerSeries.inv_mul_cancel _ hR, mul_one]
  have hVS : V * (S + m - 1) = m * S := by
    apply cancel_right hT
    calc
      V * (S + m - 1) * T = V * (T * (S + m - 1)) := by ring
      _ = V * (m * R) := by rw [hTR]
      _ = (V * R) * m := by ring
      _ = (m * S) * T := by
        rw [hVR, mul_assoc, hST]
        dsimp [R]
        ring
  have hSi : S * S⁻¹ = 1 := PowerSeries.mul_inv_cancel S hS
  have hVi : V * V⁻¹ = 1 := PowerSeries.mul_inv_cancel V hV
  have hKey : m + (m - 1) * m * S⁻¹ = m ^ 2 * V⁻¹ := by
    calc
      _ = m * S⁻¹ * (S + m - 1) := by linear_combination -m * hSi
      _ = (m * S⁻¹ * (S + m - 1)) * (V * V⁻¹) := by rw [hVi, mul_one]
      _ = (m * S⁻¹) * (V * (S + m - 1)) * V⁻¹ := by ring
      _ = m ^ 2 * V⁻¹ := by
        rw [hVS]
        linear_combination (m ^ 2 * V⁻¹) * hSi
  linear_combination -X * hKey

structure ClassicalTails (S : ℕ → Series) : Prop where
  constant : ∀ h, constantCoeff (S h) = 1
  step : ∀ h, S h = 1 - (((h : Series) + 1) * ((h : Series) + 2)) * X * (S (h + 1))⁻¹

noncomputable def parameter (j : ℕ) : Series := (2 * j + 3 : ℕ)

noncomputable def paired (S : ℕ → Series) (j : ℕ) : Series :=
  S (2 * j + 1) - (parameter j - 1) * X

noncomputable def alternate (S : ℕ → Series) (j : ℕ) : Series :=
  1 - (parameter j ^ 2 - 1) * X * (paired S (j + 1))⁻¹

theorem paired_step {S : ℕ → Series} (h : ClassicalTails S) (j : ℕ) :
    paired S j = 1 + X - parameter j ^ 2 * X * (alternate S j)⁻¹ := by
  let m := parameter j
  let A := S (2 * j + 2)
  let B := S (2 * j + 3)
  have hA : constantCoeff A ≠ 0 := by simp [A, h.constant]
  have hB : constantCoeff B ≠ 0 := by simp [B, h.constant]
  have eB : (2 * j + 2) + 1 = 2 * j + 3 := by omega
  have eA : (2 * j + 1) + 1 = 2 * j + 2 := by omega
  have hAB : A * B = B - m * (m + 1) * X := by
    conv_lhs => dsimp only [A]; rw [h.step (2 * j + 2), eB]
    rw [sub_mul, one_mul, mul_assoc (_ * X), PowerSeries.inv_mul_cancel _ hB, mul_one]
    simp only [m, parameter, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    ring
  have hFirst :
      paired S j = 1 - (m - 1) * X - ((m - 1) * m) * X * A⁻¹ := by
    unfold paired
    rw [h.step (2 * j + 1), eA]
    simp only [A, m, parameter, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    ring
  have hNext : paired S (j + 1) = B - (m + 1) * X := by
    unfold paired
    rw [show 2 * (j + 1) + 1 = 2 * j + 3 by omega]
    simp only [B, m, parameter, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    ring
  rw [hFirst, alternate, hNext]
  exact convert_step m A B hA hB hAB

noncomputable def switched (S : ℕ → Series) (j : ℕ) : Series :=
  if Even j then paired S (j / 2) else alternate S (j / 2)

noncomputable def base (j : ℕ) : Series := 1 + if Even j then X else 0

noncomputable def weight (j : ℕ) : Series :=
  C ((((2 * (j / 2) + 3 : ℕ) : ℚ) ^ 2) - if Even j then 0 else 1)

theorem switched_constant {S : ℕ → Series} (h : ClassicalTails S) (j : ℕ) :
    constantCoeff (switched S j) = 1 := by
  by_cases e : Even j <;> simp [switched, e, paired, alternate, h.constant]

theorem switched_step {S : ℕ → Series} (h : ClassicalTails S) (j : ℕ) :
    switched S j = base j - weight j * X * (switched S (j + 1))⁻¹ := by
  have even_twice (k : ℕ) : Even (2 * k) := ⟨k, by omega⟩
  have not_even_twice_add (k : ℕ) : ¬ Even (2 * k + 1) := by
    rintro ⟨t, ht⟩
    omega
  have halves (k : ℕ) : (2 * k) / 2 = k := by omega
  have halves_odd (k : ℕ) : (2 * k + 1) / 2 = k := by omega
  have halves_after (k : ℕ) : (2 * k + 1 + 1) / 2 = k + 1 := by omega
  have even_after (k : ℕ) : Even (2 * k + 1 + 1) := ⟨k + 1, by omega⟩
  have parameter_sq (k : ℕ) :
      C ((((2 * k + 3 : ℕ) : ℚ) ^ 2)) = parameter k ^ 2 := by
    rw [map_pow, map_natCast]
    rfl
  rcases Nat.even_or_odd j with ⟨k, hk⟩ | ⟨k, hk⟩
  · have ej : j = 2 * k := by omega
    clear hk
    subst j
    simp only [switched, base, weight, even_twice, not_even_twice_add, if_true, if_false,
      halves, halves_odd, sub_zero, parameter_sq]
    exact paired_step h k
  · have ej : j = 2 * k + 1 := by omega
    subst j
    simp only [switched, base, weight, not_even_twice_add, if_false, halves_odd, even_after,
      if_true, halves_after, add_zero, map_sub, map_one, parameter_sq]
    rfl

theorem inverse_close {A B : Series} (hA : constantCoeff A ≠ 0)
    (hB : constantCoeff B ≠ 0) (n : ℕ) (h : (X : Series) ^ n ∣ A - B) :
    (X : Series) ^ n ∣ A⁻¹ - B⁻¹ := by
  obtain ⟨Z, hZ⟩ := h
  have eA := PowerSeries.inv_mul_cancel A hA
  have eB := PowerSeries.inv_mul_cancel B hB
  refine ⟨-A⁻¹ * B⁻¹ * Z, ?_⟩
  calc
    A⁻¹ - B⁻¹ = (-A⁻¹ * B⁻¹) * (A - B) := by
      linear_combination B⁻¹ * eA - A⁻¹ * eB
    _ = _ := by rw [hZ]; ring

open OMA.S_oeis_a000182

theorem fractionTail_constant (d j : ℕ) :
    constantCoeff (fractionTail d j) = 1 := by
  by_cases he : Even j <;> cases d <;> simp [fractionTail, he]

theorem finite_close {S : ℕ → Series} (h : ClassicalTails S) (d j : ℕ) :
    (X : Series) ^ (d + 1) ∣ fractionTail d j - switched S j := by
  induction d generalizing j with
  | zero =>
      rw [zero_add, pow_one, X_dvd_iff, map_sub, fractionTail_constant, switched_constant h, sub_self]
  | succ d ih =>
      obtain ⟨Z, hZ⟩ := inverse_close (by simp [fractionTail_constant])
        (by simp [switched_constant h]) (d + 1) (ih (j + 1))
      refine ⟨-weight j * Z, ?_⟩
      change (base j - weight j * X * (fractionTail d (j + 1))⁻¹) - switched S j = _
      rw [switched_step h j]
      calc
        _ = (-weight j * X) * ((fractionTail d (j + 1))⁻¹ - (switched S (j + 1))⁻¹) := by ring
        _ = _ := by rw [hZ, pow_succ]; ring

theorem paired_head {S : ℕ → Series} (h : ClassicalTails S) :
    (S 0)⁻¹ = 1 + 2 * X * (switched S 0)⁻¹ := by
  have hu (j : ℕ) : constantCoeff (S j) ≠ 0 := by simp [h.constant]
  have hp : constantCoeff (switched S 0) ≠ 0 := by simp [switched_constant h]
  have hpair : switched S 0 = S 0 * S 1 := by
    have e : S 0 = 1 - 2 * X * (S 1)⁻¹ := by
      simpa using h.step 0
    rw [e, sub_mul, one_mul, mul_assoc (2 * X), PowerSeries.inv_mul_cancel _ (hu 1), mul_one]
    norm_num [switched, paired, parameter]
  apply cancel_right hp
  conv_lhs => rw [hpair, ← mul_assoc, PowerSeries.inv_mul_cancel _ (hu 0), one_mul]
  rw [add_mul, one_mul, mul_assoc (2 * X), PowerSeries.inv_mul_cancel _ hp, mul_one]
  norm_num [switched, paired, parameter]

theorem continuedFraction_of_classical {S : ℕ → Series} (h : ClassicalTails S)
    (hcoeff : ∀ n, coeff n (X * (S 0)⁻¹) = (tangentNumber n : ℚ)) :
    ContinuedFraction := by
  intro n
  refine ⟨n, ?_⟩
  intro d hd
  rw [← hcoeff, paired_head h]
  apply sub_eq_zero.mp
  rw [← map_sub]
  obtain ⟨Z, hZ⟩ := inverse_close (by simp [fractionTail_constant])
    (by simp [switched_constant h]) (d + 1) (finite_close h d 0)
  have es :
      fractionApproximation d - X * (1 + 2 * X * (switched S 0)⁻¹) =
        (2 * X ^ 2 * Z) * (X : Series) ^ (d + 1) := by
    unfold fractionApproximation
    calc
      _ = (2 * X ^ 2) * ((fractionTail d 0)⁻¹ - (switched S 0)⁻¹) := by ring
      _ = _ := by rw [hZ]; ring
  rw [es, coeff_mul_X_pow', if_neg (by omega)]

end TangentConjecture

namespace TangentConjecture

open PowerSeries
open OMA.S_oeis_a000182

def heightWeight (h : ℕ) : ℕ → ℕ → ℚ
  | 0, j => if j = 0 then 1 else 0
  | n + 1, 0 => ((h : ℚ) + 1) * heightWeight h n 1
  | n + 1, j + 1 => ((h : ℚ) + j) * heightWeight h n j +
      ((h : ℚ) + j + 2) * heightWeight h n (j + 2)

noncomputable def column (h j : ℕ) : Series := mk (fun n => heightWeight h n j)

theorem column_zero (h : ℕ) :
    column h 0 = 1 + C ((h : ℚ) + 1) * (X * column h 1) := by
  ext n
  cases n with
  | zero => simp [column, heightWeight, coeff_zero_eq_constantCoeff]
  | succ n =>
      simp only [column, coeff_mk, heightWeight, map_add (coeff (n + 1)), coeff_one, Nat.succ_ne_zero,
        if_false, coeff_C_mul, coeff_succ_X_mul, zero_add]

theorem column_succ (h j : ℕ) :
    column h (j + 1) = C ((h : ℚ) + j) * (X * column h j) +
      C ((h : ℚ) + j + 2) * (X * column h (j + 2)) := by
  ext n
  cases n with
  | zero => simp [column, heightWeight, coeff_zero_eq_constantCoeff]
  | succ n =>
      simp only [column, coeff_mk, heightWeight, map_add (coeff (n + 1)), coeff_C_mul, coeff_succ_X_mul]

theorem transfer (h j : ℕ) :
    column h (j + 1) = (C (h : ℚ) * (X * column h 0)) * column (h + 1) j := by
  let A : Series := C (h : ℚ) * (X * column h 0)
  let D : ℕ → Series := fun j => column h (j + 1) - A * column (h + 1) j
  have d0 : D 0 = C ((h : ℚ) + 2) * (X * D 1) := by
    change column h (0 + 1) - A * column (h + 1) 0 = _
    rw [column_succ h 0, column_zero (h + 1)]
    simp only [A, D, Nat.cast_zero, add_zero, Nat.cast_add, Nat.cast_one]
    have e : (h : ℚ) + 1 + 1 = (h : ℚ) + 2 := by ring
    rw [e]
    ring
  have ds (j : ℕ) :
      D (j + 1) =
        C ((h : ℚ) + j + 1) * (X * D j) +
          C ((h : ℚ) + j + 3) * (X * D (j + 2)) := by
    change column h ((j + 1) + 1) - A * column (h + 1) (j + 1) = _
    rw [column_succ h (j + 1), column_succ (h + 1) j]
    simp only [D, Nat.cast_add, Nat.cast_one]
    have e : (h : ℚ) + (↑j + 1) = (h : ℚ) + ↑j + 1 := by ring
    have f : (h : ℚ) + 1 + ↑j = (h : ℚ) + ↑j + 1 := by ring
    have g : (h : ℚ) + ↑j + 1 + 2 = (h : ℚ) + ↑j + 3 := by ring
    rw [e, f, g]
    ring
  have kills (n : ℕ) : ∀ j, coeff n (D j) = 0 := by
    induction n with
    | zero =>
        intro j
        cases j with
        | zero => rw [d0]; simp [coeff_zero_eq_constantCoeff]
        | succ j => rw [ds j]; simp [coeff_zero_eq_constantCoeff]
    | succ n ih =>
        intro j
        cases j with
        | zero =>
            rw [d0]
            simp only [coeff_C_mul, coeff_succ_X_mul, ih, mul_zero]
        | succ j =>
            rw [ds j]
            simp only [map_add (coeff (n + 1)), coeff_C_mul, coeff_succ_X_mul, ih, mul_zero, add_zero]
  apply sub_eq_zero.mp
  change D j = 0
  ext n
  simpa using kills n j

theorem column_return (h : ℕ) :
    column h 0 =
      1 + C (((h : ℚ) + 1) * h) * X ^ 2 * column h 0 * column (h + 1) 0 := by
  conv_lhs => rw [column_zero h, transfer h 0]
  rw [map_mul]
  ring

theorem heightWeight_parity (h : ℕ) (n j : ℕ) (hpar : n % 2 ≠ j % 2) :
    heightWeight h n j = 0 := by
  induction n generalizing j with
  | zero =>
      have hj : j ≠ 0 := by intro e; subst j; exact hpar rfl
      simp [heightWeight, hj]
  | succ n ih =>
      cases j with
      | zero =>
          have hs : n % 2 ≠ 1 % 2 := by omega
          simp [heightWeight, ih 1 hs]
      | succ j =>
          have hs : n % 2 ≠ j % 2 := by omega
          have ht : n % 2 ≠ (j + 2) % 2 := by omega
          simp [heightWeight, ih j hs, ih (j + 2) ht]

noncomputable def returns (h : ℕ) : Series := mk (fun n => heightWeight h (2 * n) 0)

theorem returns_constant (h : ℕ) : constantCoeff (returns h) = 1 := by
  simp [returns, heightWeight]

theorem expand_returns (h : ℕ) :
    (returns h).expand 2 (by decide) = column h 0 := by
  ext n
  by_cases hn : 2 ∣ n
  · obtain ⟨k, rfl⟩ := hn
    simp [coeff_expand_mul, returns, column]
  · rw [coeff_expand_of_not_dvd _ _ _ hn]
    simpa [column] using (heightWeight_parity h n 0 (by omega)).symm

theorem returns_step (h : ℕ) :
    returns h = 1 + C (((h : ℚ) + 1) * h) * X * returns h * returns (h + 1) := by
  have hm := column_return h
  have expand_eq :
      (returns h).expand 2 (by decide) =
      (1 + C (((h : ℚ) + 1) * h) * X * returns h * returns (h + 1)).expand 2 (by decide) := by
    simp only [map_add, map_one, map_mul, expand_X, expand_C, expand_returns]
    simpa only [map_mul, map_add, map_one] using hm
  ext n
  simpa only [coeff_expand_mul] using congrArg (coeff (2 * n)) expand_eq

noncomputable def classical (j : ℕ) : Series :=
  1 - (((j : Series) + 1) * ((j : Series) + 2)) * X * returns (j + 2)

theorem returns_inverse (j : ℕ) : returns (j + 1) = (classical j)⁻¹ := by
  have hc : constantCoeff (classical j) ≠ 0 := by simp [classical]
  apply cancel_right hc
  rw [PowerSeries.inv_mul_cancel _ hc]
  have e := returns_step (j + 1)
  simp only [Nat.cast_add, Nat.cast_one, map_mul, map_add, map_one, map_natCast] at e
  simp only [classical, mul_sub, mul_one]
  linear_combination e

theorem classical_ok : ClassicalTails classical := by
  constructor
  · intro j; simp [classical]
  · intro j
    have e : j + 1 + 1 = j + 2 := by omega
    rw [← returns_inverse (j + 1), e]
    rfl

theorem tangentPolynomial_coeff (n j : ℕ) :
    ((tangentPolynomial n).coeff (j + 1) : ℚ) = heightWeight 1 n j := by
  induction n generalizing j with
  | zero =>
      cases j with
      | zero => simp [tangentPolynomial, heightWeight]
      | succ j => simp [tangentPolynomial, heightWeight, Polynomial.coeff_X]
  | succ n ih =>
      simp only [tangentPolynomial, add_mul, one_mul, Polynomial.coeff_add,
        Polynomial.coeff_X_pow_mul', Polynomial.coeff_derivative]
      cases j with
      | zero =>
          norm_num [heightWeight, Polynomial.coeff_derivative]
          rw [show 2 = 1 + 1 by decide, ← ih 1]
          ring
      | succ j =>
          have hj : 2 ≤ j + 1 + 1 := by omega
          have e : j + 1 + 1 - 2 = j := by omega
          rw [if_pos hj, e]
          simp only [Nat.cast_add, Nat.cast_one, Int.cast_add, Int.cast_mul, Int.cast_natCast]
          rw [show j + 1 + 1 + 1 = (j + 2) + 1 by omega, ih j, ih (j + 2)]
          simp only [heightWeight]
          ring

theorem classical_tangent_coeff (n : ℕ) :
    coeff n (X * (classical 0)⁻¹) = (tangentNumber n : ℚ) := by
  rw [← returns_inverse]
  cases n with
  | zero =>
      simp [tangentNumber, tangentPolynomial, coeff_zero_eq_constantCoeff]
  | succ n =>
      rw [coeff_succ_X_mul]
      unfold tangentNumber
      rw [show 2 * (n + 1) - 1 = 2 * n + 1 by omega]
      simp [returns, tangentPolynomial, Polynomial.coeff_derivative,
        ← Polynomial.coeff_zero_eq_eval_zero, tangentPolynomial_coeff]

theorem tangent_continuedFraction : ContinuedFraction :=
  continuedFraction_of_classical classical_ok classical_tangent_coeff

end TangentConjecture

namespace TangentConjecture

open Polynomial
open OMA.S_oeis_a000182

noncomputable def operator (P : ℤ[X]) : ℤ[X] := (1 + X ^ 2) * P.derivative

theorem operator_C_mul (a : ℤ) (P : ℤ[X]) :
    operator (C a * P) = C a * operator P := by
  simp only [operator, derivative_C_mul]
  ring

theorem twice_operator_even (P : ℤ[X]) :
    C (2 : ℤ) ∣ operator (operator P) := by
  have dvd_twice_derivative : C (2 : ℤ) ∣ P.derivative.derivative := by
    rw [C_dvd_iff_dvd_coeff]
    intro n
    simp only [coeff_derivative, Nat.cast_add, Nat.cast_one]
    have hd : (2 : ℤ) ∣ ((n : ℤ) + 1) * ((n : ℤ) + 1 + 1) :=
      Int.two_dvd_mul_add_one ((n : ℤ) + 1)
    apply dvd_trans hd
    exact ⟨P.coeff (n + 1 + 1), by ring⟩
  have h :
      operator (operator P) =
        (1 + X ^ 2) * (C 2 * (X * P.derivative) + (1 + X ^ 2) * P.derivative.derivative) := by
    simp only [operator, derivative_mul, derivative_add, derivative_one, derivative_X_pow]
    norm_num
    exact Or.inl (by ring)
  rw [h]
  exact dvd_mul_of_dvd_right (dvd_add (dvd_mul_right _ _)
    (dvd_mul_of_dvd_right dvd_twice_derivative _)) _

theorem tangent_polynomial_even (n : ℕ) :
    C ((2 : ℤ) ^ n) ∣ tangentPolynomial (2 * n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      obtain ⟨R, eR⟩ := ih
      have e : 2 * (n + 1) + 1 = (2 * n + 1 + 1) + 1 := by omega
      rw [e]
      change C ((2 : ℤ) ^ (n + 1)) ∣ operator (operator (tangentPolynomial (2 * n + 1)))
      rw [eR, operator_C_mul, operator_C_mul]
      obtain ⟨Q, eQ⟩ := twice_operator_even R
      refine ⟨Q, ?_⟩
      rw [eQ, pow_succ, map_mul, mul_assoc]

theorem tangent_two_power (n : ℕ) (hn : 0 < n) :
    (2 : ℤ) ^ (n - 1) ∣ tangentNumber n := by
  have e : 2 * n - 1 = 2 * (n - 1) + 1 := by omega
  unfold tangentNumber
  rw [e]
  obtain ⟨R, hr⟩ := tangent_polynomial_even (n - 1)
  exact ⟨R.eval 0, by rw [hr, eval_mul, eval_C]⟩

end TangentConjecture

namespace TangentConjecture

open Polynomial Finset

theorem iterate_leibniz {R : Type*} [CommRing R] (D : Derivation R R[X] R[X])
    {n : ℕ} (a b : R[X]) :
    D^[n] (a * b) =
      ∑ k ∈ range (n + 1), n.choose k • (D^[n - k] a * D^[k] b) := by
  have leibniz (x y : R[X]) : D (x * y) = D x * y + x * D y := by
    rw [D.leibniz]
    simp only [smul_eq_mul]
    ring
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        D^[n + 1] (a * b) =
            D (∑ k ∈ range (n + 1), n.choose k • (D^[n - k] a * D^[k] b)) := by
          rw [Function.iterate_succ_apply', ih]
        _ = (∑ k ∈ range (n + 1),
              n.choose k • (D^[n - k + 1] a * D^[k] b)) +
            ∑ k ∈ range (n + 1), n.choose k • (D^[n - k] a * D^[k + 1] b) := by
          simp only [map_sum, map_nsmul, leibniz, Function.iterate_succ_apply']
          simp_rw [nsmul_add, sum_add_distrib]
        _ = ((∑ k ∈ range (n + 1),
                n.choose k • (D^[n - k] a * D^[k + 1] b)) +
              ∑ k ∈ range (n + 1), n.choose (k + 1) • (D^[n - k] a * D^[k + 1] b)) +
            1 • (D^[n + 1] a * D^[0] b) := by
          have shift :
              (∑ k ∈ range (n + 1), n.choose k • (D^[n - k + 1] a * D^[k] b)) =
                (∑ k ∈ range (n + 1), n.choose (k + 1) • (D^[n - k] a * D^[k + 1] b)) +
                   1 • (D^[n + 1] a * D^[0] b) := by
            rw [sum_range_succ' _ n, Nat.choose_zero_right, Nat.sub_zero]
            rw [sum_range_succ _ n, Nat.choose_succ_self, zero_smul, add_zero]
            congr 1
            refine sum_congr rfl fun k hk => ?_
            rw [mem_range] at hk
            rw [show n - (k + 1) + 1 = n - k by omega]
          rw [shift]
          abel
        _ = (∑ k ∈ range (n + 1),
                (n + 1).choose (k + 1) • (D^[n + 1 - (k + 1)] a * D^[k + 1] b)) +
            1 • (D^[n + 1] a * D^[0] b) := by
          simp_rw [Nat.choose_succ_succ, Nat.succ_sub_succ, add_smul, sum_add_distrib]
        _ = ∑ k ∈ range (n + 1 + 1),
              (n + 1).choose k • (D^[n + 1 - k] a * D^[k] b) := by
          rw [sum_range_succ' _ (n + 1), Nat.choose_zero_right, Nat.sub_zero]

theorem prime_iterate_mul (p : ℕ) [Fact p.Prime]
    (D : Derivation (ZMod p) (ZMod p)[X] (ZMod p)[X]) (a b : (ZMod p)[X]) :
    D^[p] (a * b) = a * D^[p] b + b * D^[p] a := by
  have hp : p.Prime := Fact.out
  have rest : (∑ k ∈ range p, p.choose k • (D^[p - k] a * D^[k] b)) =
      D^[p] a * b := by
    rw [sum_eq_single_of_mem 0 (mem_range.mpr hp.pos)]
    · simp
    · intro k hk hk0
      have hz : (↑(p.choose k) : ZMod p) = 0 :=
        (ZMod.natCast_eq_zero_iff _ _).2 (hp.dvd_choose_self hk0 (mem_range.mp hk))
      rw [← Nat.cast_smul_eq_nsmul (R := ZMod p), hz, zero_smul]
  rw [iterate_leibniz, sum_range_succ, rest]
  simp [add_comm, mul_comm]

noncomputable def primeIteratedDerivation (p : ℕ) [Fact p.Prime]
    (D : Derivation (ZMod p) (ZMod p)[X] (ZMod p)[X]) :
    Derivation (ZMod p) (ZMod p)[X] (ZMod p)[X] where
  toLinearMap := D.toLinearMap ^ p
  leibniz' a b := by
    simp only [Module.End.pow_apply, smul_eq_mul]
    exact prime_iterate_mul p D a b
  map_one_eq_zero' := by
    have hp : p.Prime := Fact.out
    have e : p - 1 + 1 = p := Nat.sub_add_cancel hp.one_lt.le
    calc
      (D.toLinearMap ^ p) 1 = (D.toLinearMap ^ (p - 1 + 1)) 1 :=
        congrArg (fun n : ℕ => (D.toLinearMap ^ n) 1) e.symm
      _ = 0 := by
        rw [pow_succ, Module.End.mul_apply]
        simp

noncomputable def tanDerivation (R : Type*) [CommRing R] : Derivation R R[X] R[X] :=
  mkDerivation R (1 + X ^ 2 : R[X])

theorem tanDerivation_apply {R : Type*} [CommRing R] (f : R[X]) :
    tanDerivation R f = (1 + X ^ 2) * f.derivative := by
  simp [tanDerivation, mkDerivation_apply, smul_eq_mul, mul_comm, add_mul]

theorem tanFactor_degree (R : Type*) [CommRing R] [Nontrivial R] :
    (1 + X ^ 2 : R[X]).natDegree = 2 := by
  rw [natDegree_add_eq_right_of_natDegree_lt, natDegree_X_pow]
  simp

noncomputable def tanQuotient (R : Type*) [CommRing R] : ℕ → R[X]
  | 0 => 1
  | n + 1 => (2 * X) * tanQuotient R n + (1 + X ^ 2) * (tanQuotient R n).derivative

theorem iterate_tan_X {R : Type*} [CommRing R] (n : ℕ) :
    (tanDerivation R)^[n + 1] X = (1 + X ^ 2) * tanQuotient R n := by
  induction n with
  | zero => simp [tanDerivation, tanQuotient]
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, tanDerivation_apply, tanQuotient, derivative_mul]
      simp [derivative_add]
      ring

theorem tanQuotient_degree {R : Type*} [CommRing R] (n : ℕ) :
    (tanQuotient R n).natDegree ≤ n := by
  induction n with
  | zero => simp [tanQuotient]
  | succ n ih =>
      rw [tanQuotient]
      refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
      · have h : (2 * X : R[X]).natDegree ≤ 1 := by
          refine (natDegree_mul_le (p := (2 : R[X])) (q := X)).trans ?_
          simpa using (natDegree_X_le (R := R))
        have hd := natDegree_mul_le (p := (2 * X : R[X])) (q := tanQuotient R n)
        omega
      · have ha : (1 + X ^ 2 : R[X]).natDegree ≤ 2 := by
          refine (natDegree_add_le _ _).trans ?_
          exact max_le (by simp) (by simpa using
            (natDegree_pow_le_of_le (p := (X : R[X])) 2 natDegree_X_le))
        by_cases hz : (tanQuotient R n).natDegree = 0
        · simp [derivative_of_natDegree_zero hz]
        · have hd := natDegree_mul_le (p := (1 + X ^ 2 : R[X]))
            (q := (tanQuotient R n).derivative)
          have hdd := natDegree_derivative_le (tanQuotient R n)
          omega

theorem tanQuotient_residue {R : Type*} [CommRing R] (n : ℕ) :
    (1 + X ^ 2 : R[X]) ∣ tanQuotient R n - (2 * X) ^ n := by
  induction n with
  | zero => simp [tanQuotient]
  | succ n ih =>
      obtain ⟨B, hB⟩ := ih
      refine ⟨(2 * X) * B + (tanQuotient R n).derivative, ?_⟩
      rw [tanQuotient, pow_succ]
      linear_combination (2 * X) * hB

theorem const_of_small_degree_derivative_zero (p : ℕ) [Fact p.Prime]
    (Q : (ZMod p)[X]) (hdeg : Q.natDegree < p) (hD : Q.derivative = 0) :
    Q = C (Q.coeff 0) := by
  ext n
  cases n with
  | zero => simp
  | succ n =>
      simp only [coeff_C, Nat.succ_ne_zero, if_false]
      by_cases h : n + 1 < p
      · have hq := congrArg (fun f : (ZMod p)[X] => f.coeff n) hD
        rw [coeff_derivative, coeff_zero] at hq
        have hn : (↑(n + 1) : ZMod p) ≠ 0 := by
          rw [Ne, ZMod.natCast_eq_zero_iff]
          exact Nat.not_dvd_of_pos_of_lt (by omega) h
        exact (mul_eq_zero.mp hq).resolve_right (by simpa using hn)
      · exact coeff_eq_zero_of_natDegree_lt (by omega)

theorem tanQuotient_constant (p : ℕ) [Fact p.Prime] :
    tanQuotient (ZMod p) (p - 1) = C ((tanQuotient (ZMod p) (p - 1)).coeff 0) := by
  have hp : p.Prime := Fact.out
  have hpos := hp.pos
  let K := ZMod p
  let D := tanDerivation K
  let Q := tanQuotient K (p - 1)
  let F : K[X] := 1 + X ^ 2
  have ep : p - 1 + 1 = p := Nat.sub_add_cancel hp.one_lt.le
  have hQ : D^[p] X = F * Q := by
    simpa only [ep] using (iterate_tan_X (R := K) (p - 1))
  have hD : primeIteratedDerivation p D = mkDerivation K (F * Q) := by
    apply Polynomial.derivation_ext
    rw [mkDerivation_X]
    change (D.toLinearMap ^ p) X = _
    rw [Module.End.pow_apply]
    exact hQ
  have commuteD : D (D^[p] X) = D^[p] (D X) := by
    exact (Function.iterate_succ_apply' D p X).symm.trans (Function.iterate_succ_apply D p X)
  have hCore : F ^ 2 * Q.derivative = 0 := by
    rw [hQ] at commuteD
    rw [show D^[p] (D X) = (D.toLinearMap ^ p) (D X) from
      (Module.End.pow_apply D.toLinearMap p (D X)).symm] at commuteD
    change D (F * Q) = primeIteratedDerivation p D (D X) at commuteD
    rw [hD, mkDerivation_apply] at commuteD
    have hDX : D X = F := by simp [D, F, tanDerivation]
    rw [hDX, tanDerivation_apply, derivative_mul, smul_eq_mul] at commuteD
    change F ^ 2 * Q.derivative = 0
    linear_combination commuteD
  have hF : F ≠ 0 := by
    intro e
    have hd := tanFactor_degree K
    change F.natDegree = 2 at hd
    rw [e, natDegree_zero] at hd
    omega
  have hm : Q.derivative = 0 := (mul_eq_zero.mp hCore).resolve_left (pow_ne_zero _ hF)
  apply const_of_small_degree_derivative_zero p _ _ hm
  have deg := tanQuotient_degree (R := K) (p - 1)
  change Q.natDegree ≤ p - 1 at deg
  omega

theorem tanQuotient_sign (p : ℕ) [Fact p.Prime] (hne : p ≠ 2) :
    tanQuotient (ZMod p) (p - 1) = C ((-1 : ZMod p) ^ ((p - 1) / 2)) := by
  have hp : p.Prime := Fact.out
  have oddp := hp.eq_two_or_odd.resolve_left hne
  have hlt : 2 < p := by have := hp.two_le; omega
  let K := ZMod p
  let n := (p - 1) / 2
  let Q := tanQuotient K (p - 1)
  let sign : K := (-1) ^ n
  let F : K[X] := 1 + X ^ 2
  change Q = C sign
  have evenPred : p - 1 = 2 * n := by dsimp [n]; omega
  have ht : (2 : K) ≠ 0 := by
    change (↑(2 : ℕ) : ZMod p) ≠ 0
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt (by decide) hlt
  have hOne : (2 : K[X]) ^ (p - 1) = 1 := by
    rw [← show C (2 : K) = (2 : K[X]) from map_ofNat _ _, ← map_pow,
      ZMod.pow_card_sub_one_eq_one ht, map_one]
  have hpow : F ∣ (2 * X) ^ (p - 1) - C sign := by
    rw [mul_pow, hOne, one_mul, evenPred, pow_mul]
    simpa [F, sign, map_pow, map_neg, map_one, add_comm] using
      sub_dvd_pow_sub_pow ((X : K[X]) ^ 2) (-1) n
  have hDiv : F ∣ Q - C sign := by
    have e : Q - C sign = (Q - (2 * X) ^ (p - 1)) +
        ((2 * X) ^ (p - 1) - C sign) := by ring
    rw [e]
    exact dvd_add (tanQuotient_residue (p - 1)) hpow
  apply sub_eq_zero.mp
  apply eq_zero_of_dvd_of_natDegree_lt hDiv
  have eqQ : Q = C (Q.coeff 0) := tanQuotient_constant p
  have hF : F.natDegree = 2 := tanFactor_degree K
  rw [hF, eqQ, ← map_sub, natDegree_C]
  decide

theorem tanDerivation_prime_iterate (p : ℕ) [Fact p.Prime] (hne : p ≠ 2)
    (f : (ZMod p)[X]) :
    (tanDerivation (ZMod p))^[p] f =
      C ((-1 : ZMod p) ^ ((p - 1) / 2)) * tanDerivation (ZMod p) f := by
  have hp : p.Prime := Fact.out
  let K := ZMod p
  let D := tanDerivation K
  let F : K[X] := 1 + X ^ 2
  let c : K := (-1) ^ ((p - 1) / 2)
  have equiv : primeIteratedDerivation p D = mkDerivation K (F * C c) := by
    apply Polynomial.derivation_ext
    rw [mkDerivation_X]
    change (D.toLinearMap ^ p) X = _
    rw [Module.End.pow_apply]
    change D^[p] X = F * C c
    have e : p - 1 + 1 = p := Nat.sub_add_cancel hp.one_lt.le
    calc
      _ = D^[p - 1 + 1] X := congrArg (fun n : ℕ => D^[n] X) e.symm
      _ = F * tanQuotient K (p - 1) := iterate_tan_X (p - 1)
      _ = _ := congrArg (F * ·) (tanQuotient_sign p hne)
  change D^[p] f = C c * D f
  rw [← show (D.toLinearMap ^ p) f = D^[p] f from Module.End.pow_apply D.toLinearMap p f]
  change primeIteratedDerivation p D f = C c * D f
  rw [equiv, mkDerivation_apply, smul_eq_mul, tanDerivation_apply]
  change f.derivative * (F * C c) = C c * (F * f.derivative)
  ring

theorem tanDerivation_period_base (p : ℕ) [Fact p.Prime] (hne : p ≠ 2)
    (f : (ZMod p)[X]) :
    (tanDerivation (ZMod p))^[2 * p - 1] f = tanDerivation (ZMod p) f := by
  have hp : p.Prime := Fact.out
  have ep : p - 1 + 1 = p := Nat.sub_add_cancel hp.one_lt.le
  let K := ZMod p
  let D := tanDerivation K
  let c : K := (-1) ^ ((p - 1) / 2)
  have hc : c * c = 1 := by
    have hs : (-1 : K) * (-1) = 1 := by ring
    dsimp [c]
    rw [← mul_pow, hs, one_pow]
  have linear_iterate (n : ℕ) (g : K[X]) :
      D^[n] (C c * g) = C c * D^[n] g := by
    calc
      _ = (D.toLinearMap ^ n) (C c * g) := (Module.End.pow_apply D.toLinearMap n _).symm
      _ = C c * (D.toLinearMap ^ n) g := by simp only [← smul_eq_C_mul, map_smul]
      _ = _ := congrArg (C c * ·) (Module.End.pow_apply D.toLinearMap n g)
  change D^[2 * p - 1] f = D f
  calc
    D^[2 * p - 1] f = D^[p - 1 + p] f := congrArg (fun n : ℕ => D^[n] f) (by omega)
    _ = D^[p - 1] (D^[p] f) := Function.iterate_add_apply D _ _ f
    _ = C c * D^[p - 1] (D f) := by
      rw [show D^[p] f = C c * D f from tanDerivation_prime_iterate p hne f, linear_iterate]
    _ = C c * D^[p] f := by
      rw [← Function.iterate_succ_apply D]
      exact congrArg (fun n : ℕ => C c * D^[n] f) ep
    _ = D f := by
      rw [show D^[p] f = C c * D f from tanDerivation_prime_iterate p hne f,
        ← mul_assoc, ← map_mul, hc, map_one, one_mul]

end TangentConjecture

namespace TangentConjecture

open Finset

theorem cast_pow_dvd {R : Type*} [Ring R] (p k i : ℕ) {d : R}
    (hd : ((p : R) ^ k) ∣ d) : ((p : R) ^ (k * i)) ∣ d ^ i := by
  obtain ⟨z, rfl⟩ := hd
  refine ⟨z ^ i, ?_⟩
  rw [((Nat.cast_commute p z).pow_left k).mul_pow, ← pow_mul]

theorem lift_prime_power {R : Type*} [Ring R] (p k : ℕ) (hp : p.Prime) (hk : 0 < k)
    {a b : R} (hComm : Commute a b) (hd : ((p : R) ^ k) ∣ a - b) :
    ((p : R) ^ (k + 1)) ∣ a ^ p - b ^ p := by
  let d := a - b
  have hDB : Commute d b := hComm.sub_left (Commute.refl b)
  have pa : a = d + b := (sub_add_cancel a b).symm
  rw [pa, hDB.add_pow, sum_range_succ']
  simp only [pow_zero, Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, one_mul, mul_one,
    add_sub_cancel_right]
  refine Finset.dvd_sum (fun i hi => ?_)
  have hi' : i + 1 ≤ p := by have := mem_range.mp hi; omega
  by_cases e : i + 1 = p
  · rw [e, Nat.sub_self, pow_zero, Nat.choose_self, Nat.cast_one, mul_one, mul_one]
    have ex : k + 1 ≤ k * p := by
      have hp2 := hp.two_le
      exact (show k + 1 ≤ k * 2 by omega).trans (Nat.mul_le_mul_left _ hp2)
    exact (pow_dvd_pow _ ex).trans (cast_pow_dvd p k p hd)
  · have exp : k ≤ k * (i + 1) := by
      rw [Nat.mul_add, Nat.mul_one]
      omega
    obtain ⟨u, hu⟩ := (pow_dvd_pow (p : R) exp).trans (cast_pow_dvd p k (i + 1) hd)
    obtain ⟨v, hv⟩ := hp.dvd_choose_self (show i + 1 ≠ 0 by omega) (by omega : i + 1 < p)
    refine ⟨u * b ^ (p - (i + 1)) * (v : R), ?_⟩
    rw [hu, hv, Nat.cast_mul, pow_succ]
    calc
      _ = (p : R) ^ k * ((u * b ^ (p - (i + 1))) * (p : R)) * (v : R) := by
        simp only [mul_assoc]
      _ = _ := by
        rw [(Nat.cast_commute p (u * b ^ (p - (i + 1)))).eq.symm]
        simp only [mul_assoc]

theorem lift_iterated_prime {R : Type*} [Ring R] (p : ℕ) (hp : p.Prime)
    {a b : R} (hc : Commute a b) (h : (p : R) ∣ a - b) (r : ℕ) :
    ((p : R) ^ (r + 1)) ∣ a ^ (p ^ r) - b ^ (p ^ r) := by
  induction r with
  | zero => simpa using h
  | succ r ih =>
      rw [pow_succ p r, pow_mul, pow_mul]
      exact lift_prime_power p (r + 1) hp (by omega)
        ((hc.pow_left (p ^ r)).pow_right (p ^ r)) ih

open Polynomial

abbrev IntegerEnd := Module.End ℤ ℤ[X]

theorem end_dvd_of_polynomial_dvd {a : ℤ} (ha : a ≠ 0) (E : IntegerEnd)
    (h : ∀ f, C a ∣ E f) : (a : IntegerEnd) ∣ E := by
  let q : ℤ[X] → ℤ[X] := fun f => (h f).choose
  have eq (f : ℤ[X]) : E f = C a * q f := (h f).choose_spec
  have ha' : (C a : ℤ[X]) ≠ 0 := C_ne_zero.mpr ha
  let Q : IntegerEnd :=
    { toFun := q
      map_add' := fun x y => by
        apply mul_left_cancel₀ ha'
        rw [← eq, mul_add, ← eq, ← eq, map_add]
      map_smul' := fun c f => by
        apply mul_left_cancel₀ ha'
        rw [← eq, map_smul]
        simp only [RingHom.id_apply, smul_eq_C_mul]
        rw [eq f]
        ring }
  refine ⟨Q, ?_⟩
  apply LinearMap.ext
  intro f
  rw [Module.End.mul_apply, Module.End.intCast_apply, smul_eq_C_mul]
  exact eq f

theorem eval_end_dvd {a : ℤ} {E : IntegerEnd} (h : (a : IntegerEnd) ∣ E) (f : ℤ[X]) :
    a ∣ (E f).eval 0 := by
  obtain ⟨Q, rfl⟩ := h
  refine ⟨(Q f).eval 0, ?_⟩
  rw [Module.End.mul_apply, Module.End.intCast_apply, smul_eq_C_mul, eval_mul, eval_C]

end TangentConjecture

namespace TangentConjecture

open Polynomial OMA.S_oeis_a000182

noncomputable def integerTangent : IntegerEnd := (tanDerivation ℤ).toLinearMap

theorem exact_polynomial (n : ℕ) : tangentPolynomial n = (integerTangent ^ n) X := by
  induction n with
  | zero => simp [tangentPolynomial]
  | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, ← ih, tangentPolynomial]
      exact (tanDerivation_apply _).symm

theorem iterate_tan_map {R S : Type*} [CommRing R] [CommRing S] (g : R →+* S)
    (n : ℕ) (f : R[X]) :
    ((tanDerivation R)^[n] f).map g = (tanDerivation S)^[n] (f.map g) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        tanDerivation_apply, tanDerivation_apply, Polynomial.map_mul, Polynomial.map_add,
        Polynomial.map_one, Polynomial.map_pow, Polynomial.map_X, ← derivative_map, ih]

theorem prime_iterate_stepping (p : ℕ) [Fact p.Prime] (hne : p ≠ 2)
    (s : ℕ) (f : (ZMod p)[X]) :
    (tanDerivation (ZMod p))^[1 + 2 * (p - 1) * s] f = tanDerivation (ZMod p) f := by
  let D := tanDerivation (ZMod p)
  have hp : p.Prime := Fact.out
  have hpos := hp.pos
  change D^[1 + 2 * (p - 1) * s] f = D f
  induction s with
  | zero => simp
  | succ s ih =>
      have e : 1 + 2 * (p - 1) * (s + 1) = 2 * (p - 1) + (1 + 2 * (p - 1) * s) := by ring
      rw [e, Function.iterate_add_apply, ih, ← Function.iterate_succ_apply D]
      exact (congrArg (fun n : ℕ => D^[n] f) (by omega : 2 * (p - 1) + 1 = 2 * p - 1)).trans
        (tanDerivation_period_base p hne f)

theorem integer_tangent_base_dvd (p : ℕ) [Fact p.Prime] (hne : p ≠ 2) (s : ℕ) :
    (p : IntegerEnd) ∣ integerTangent ^ (1 + 2 * (p - 1) * s) - integerTangent := by
  have hp : p.Prime := Fact.out
  have hnonzero : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hCast : ((p : ℤ) : IntegerEnd) = (p : IntegerEnd) := Int.cast_natCast p
  rw [← hCast]
  apply end_dvd_of_polynomial_dvd hnonzero
  intro f
  rw [LinearMap.sub_apply, C_dvd_iff_dvd_coeff]
  let φ : ℤ →+* ZMod p := Int.castRingHom _
  have hMap :
      (((integerTangent ^ (1 + 2 * (p - 1) * s)) f) - integerTangent f).map φ = 0 := by
    rw [Polynomial.map_sub, sub_eq_zero, Module.End.pow_apply]
    change ((tanDerivation ℤ)^[1 + 2 * (p - 1) * s] f).map φ =
      ((tanDerivation ℤ)^[1] f).map φ
    rw [iterate_tan_map, iterate_tan_map, Function.iterate_one, prime_iterate_stepping p hne]
  intro k
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1
  have e := congrArg (fun P : (ZMod p)[X] => P.coeff k) hMap
  simpa only [coeff_map, coeff_zero, φ, Int.coe_castRingHom] using e

theorem odd_prime_step (p r m s : ℕ) [Fact p.Prime] (hne : p ≠ 2)
    (hm : p ^ r ≤ 2 * m - 1) :
    Int.ModEq ((p : ℤ) ^ (r + 1))
      (tangentNumber (m + ((p - 1) * p ^ r) * s)) (tangentNumber m) := by
  have hp : p.Prime := Fact.out
  let E := integerTangent
  let t := 1 + 2 * (p - 1) * s
  let n := ((p - 1) * p ^ r) * s
  let u := 2 * m - 1 - p ^ r
  change Int.ModEq _ (tangentNumber (m + n)) (tangentNumber m)
  have hmul : t * p ^ r = p ^ r + 2 * n := by dsimp [t, n]; ring
  have hpowpos : 0 < p ^ r := pow_pos hp.pos _
  have e₁ : t * p ^ r + u = 2 * (m + n) - 1 := by rw [hmul]; dsimp [u]; omega
  have e₂ : p ^ r + u = 2 * m - 1 := by dsimp [u]; omega
  have eComm : Commute (E ^ t) E := (Commute.refl E).pow_left t
  have dd := lift_iterated_prime p hp eComm (integer_tangent_base_dvd p hne s) r
  have dds := dvd_mul_of_dvd_left dd (E ^ u)
  rw [sub_mul, ← pow_mul, ← pow_add, ← pow_add, e₁, e₂] at dds
  have hCast : (↑((p : ℤ) ^ (r + 1)) : IntegerEnd) = (p : IntegerEnd) ^ (r + 1) := by
    rw [Int.cast_pow, Int.cast_natCast]
  rw [← hCast] at dds
  have hf := eval_end_dvd dds (X : ℤ[X])
  rw [LinearMap.sub_apply, eval_sub] at hf
  rw [← show tangentPolynomial (2 * (m + n) - 1) = (E ^ (2 * (m + n) - 1)) X from
    exact_polynomial _, ← show tangentPolynomial (2 * m - 1) = (E ^ (2 * m - 1)) X from
    exact_polynomial _] at hf
  exact (Int.modEq_of_dvd hf).symm

end TangentConjecture

namespace TangentConjecture

open OMA.S_oeis_a000182

theorem gauss_odd (p r n i : ℕ) [Fact p.Prime] (hne : p ≠ 2) (hn : 0 < n) :
    Int.ModEq ((p : ℤ) ^ (r + 1)) (tangentNumber (n * p ^ (r + 1) + i))
      (tangentNumber (n * p ^ r + i)) := by
  have hp : p.Prime := Fact.out
  have exponent : n * p ^ (r + 1) + i =
      n * p ^ r + i + ((p - 1) * p ^ r) * n := by
    rw [pow_succ]
    calc
      _ = n * (p ^ r * ((p - 1) + 1)) + i := by rw [Nat.sub_add_cancel hp.one_lt.le]
      _ = _ := by ring
  rw [exponent]
  have lower : p ^ r ≤ n * p ^ r := by
    simpa using Nat.mul_le_mul_right (p ^ r) (Nat.succ_le_of_lt hn)
  have pos : 0 < p ^ r := pow_pos hp.pos _
  exact odd_prime_step p r _ n hne (by omega)

theorem tangentIndexCast (n : ℕ) :
    (tangentNumber (n + 1) : ℚ) = heightWeight 1 (2 * n) 0 := by
  have eq := (classical_tangent_coeff (n + 1)).symm
  simpa only [← returns_inverse 0, PowerSeries.coeff_succ_X_mul, returns, PowerSeries.coeff_mk] using eq

theorem tangent_one : tangentNumber 1 = 1 := by
  have e := tangentIndexCast 0
  norm_num [heightWeight] at e
  exact_mod_cast e

theorem tangent_two : tangentNumber 2 = 2 := by
  have e := tangentIndexCast 1
  norm_num [heightWeight] at e
  exact_mod_cast e

theorem tangent_four : tangentNumber 4 = 272 := by
  have e := tangentIndexCast 3
  norm_num [heightWeight] at e
  exact_mod_cast e

theorem two_power_modEq {k m n : ℕ} (hm : k + 1 ≤ m) (hn : m ≤ n) :
    Int.ModEq ((2 : ℤ) ^ k) (tangentNumber n) (tangentNumber m) := by
  have hdm : (2 : ℤ) ^ k ∣ tangentNumber m :=
    (pow_dvd_pow _ (by omega : k ≤ m - 1)).trans (tangent_two_power m (by omega))
  have hdn : (2 : ℤ) ^ k ∣ tangentNumber n :=
    (pow_dvd_pow _ (by omega : k ≤ n - 1)).trans (tangent_two_power n (by omega))
  exact Int.modEq_of_dvd (dvd_sub hdm hdn)

theorem two_power_lower (r : ℕ) (hr : 2 ≤ r) : r + 2 ≤ 2 ^ r := by
  obtain ⟨s, e⟩ : ∃ s, r = s + 2 := ⟨r - 2, by omega⟩
  rw [e]
  clear e hr r
  induction s with
  | zero => decide
  | succ s ih =>
      rw [show s + 1 + 2 = s + 2 + 1 by omega, pow_succ]
      omega

theorem gauss_two (r n i : ℕ) (hn : 0 < n)
    (h : ¬ (n = 1 ∧ (r = 0 ∨ r = 1) ∧ i = 0)) :
    Int.ModEq ((2 : ℤ) ^ (r + 1)) (tangentNumber (n * 2 ^ (r + 1) + i))
      (tangentNumber (n * 2 ^ r + i)) := by
  have hle : n * 2 ^ r + i ≤ n * 2 ^ (r + 1) + i := by
    rw [pow_succ, ← Nat.mul_assoc]
    omega
  apply two_power_modEq _ hle
  by_cases hr : 2 ≤ r
  · have hh : 2 ^ r ≤ n * 2 ^ r := by
      simpa using (Nat.mul_le_mul_right (2 ^ r) (Nat.succ_le_of_lt hn))
    have hl := two_power_lower r hr
    omega
  · have cases : r = 0 ∨ r = 1 := by omega
    rcases cases with rfl | rfl <;> norm_num at h ⊢ <;> omega

theorem tangent_shiftedGauss : ShiftedGauss := by
  intro i p n k hi hp hn hk
  have e : k = (k - 1) + 1 := by omega
  rw [e]
  simp only [Nat.add_sub_cancel]
  by_cases he : p = 2
  · subst p
    exact gauss_two (k - 1) n i hn (by omega)
  · letI : Fact p.Prime := ⟨hp⟩
    exact gauss_odd p (k - 1) n i he hn

theorem tangent_unshiftedGauss : UnshiftedGauss := by
  intro p n k hp hn hk
  obtain ⟨r, e⟩ : ∃ r, k = r + 1 := ⟨k - 1, by omega⟩
  subst k
  simp only [Nat.add_sub_cancel]
  by_cases he : p = 2
  · subst p
    by_cases exc : n = 1 ∧ (r = 0 ∨ r = 1)
    · obtain ⟨rfl, rfl | rfl⟩ := exc <;>
        norm_num [tangent_one, tangent_two, tangent_four, Int.ModEq]
    · constructor
      · intro _ h
        exact exc ⟨h.2.1, by omega⟩
      · intro _
        simpa only [add_zero, Nat.cast_ofNat] using
          (gauss_two r n 0 hn (fun h => exc ⟨h.1, h.2.1⟩))
  · letI : Fact p.Prime := ⟨hp⟩
    simp only [he, false_and, not_false_eq_true, iff_true]
    simpa only [add_zero] using gauss_odd p r n 0 he hn

theorem tangent_periodicity : Periodicity := by
  intro q hq
  refine ⟨q.totient, Nat.totient_pos.mpr hq, dvd_rfl, q + 1, by omega, ?_⟩
  intro m hm
  rw [Int.modEq_iff_dvd, Int.natCast_dvd, Nat.dvd_iff_prime_pow_dvd_dvd]
  intro p a hp hd
  cases a with
  | zero => simp
  | succ r =>
      have hpq : p ^ (r + 1) ≤ q := Nat.le_of_dvd hq hd
      have cong : Int.ModEq ((p : ℤ) ^ (r + 1))
          (tangentNumber (m + q.totient)) (tangentNumber m) := by
        by_cases he : p = 2
        · subst p
          have lower : r + 1 < 2 ^ (r + 1) := Nat.lt_two_pow_self
          exact two_power_modEq (by omega) (by omega)
        · letI : Fact p.Prime := ⟨hp⟩
          have power : p ^ r ≤ p ^ (r + 1) := Nat.pow_le_pow_right hp.pos (by omega)
          have hpφ : (p - 1) * p ^ r ∣ q.totient := by
            rw [mul_comm, ← Nat.totient_prime_pow_succ hp]
            exact Nat.totient_dvd_of_dvd hd
          obtain ⟨s, hs⟩ := hpφ
          rw [hs]
          exact odd_prime_step p r m s he (by omega)
      apply Int.natCast_dvd.mp
      simpa only [Nat.cast_pow] using cong.dvd

end TangentConjecture

namespace TangentConjecture

def GaussSequence (b : ℕ → ℤ) : Prop :=
  ∀ p r n : ℕ, p.Prime → 0 < n →
    Int.ModEq ((p : ℤ) ^ (r + 1)) (b (n * p ^ (r + 1))) (b (n * p ^ r))

theorem earlier_dvd_of_not_pow (p r m n : ℕ) (hp : p.Prime)
    (h : m ∣ n * p ^ (r + 1)) (hbad : ¬ p ^ (r + 1) ∣ m) :
    m ∣ n * p ^ r := by
  rw [Nat.dvd_iff_prime_pow_dvd_dvd]
  intro q j hq hqj
  by_cases eq : q = p
  · subst q
    have hj : j ≤ r := by
      by_contra! he
      exact hbad ((pow_dvd_pow p (by omega : r + 1 ≤ j)).trans hqj)
    exact (pow_dvd_pow p hj).trans (dvd_mul_left _ _)
  · have hcop : q.Coprime p := hq.coprime_iff_not_dvd.mpr
      (fun h => eq ((Nat.prime_dvd_prime_iff_eq hq hp).mp h))
    have hdiv := ((hcop.pow_left j).pow_right (r + 1)).dvd_of_dvd_mul_right (hqj.trans h)
    exact hdiv.trans (dvd_mul_right _ _)

theorem strip_gauss {b : ℕ → ℤ} (hb : GaussSequence b)
    (m : ℕ) (z : ℤ) (hm : (m : ℤ) ∣ z) :
    GaussSequence (fun n => b n - if m ∣ n then z else 0) := by
  intro p r n hp hn
  apply (hb p r n hp hn).sub
  by_cases hEarlier : m ∣ n * p ^ r
  · have hd : m ∣ n * p ^ (r + 1) := by
      rw [pow_succ, ← mul_assoc]
      exact hEarlier.trans (dvd_mul_right _ _)
    simp [hd, hEarlier, Int.ModEq.refl]
  · by_cases hLater : m ∣ n * p ^ (r + 1)
    · have hPow : p ^ (r + 1) ∣ m := by
        by_contra he
        exact hEarlier (earlier_dvd_of_not_pow p r m n hp hLater he)
      have hd : (p : ℤ) ^ (r + 1) ∣ z := by
        have hd' : ((p ^ (r + 1) : ℕ) : ℤ) ∣ (m : ℤ) := Int.natCast_dvd_natCast.mpr hPow
        exact (by simpa only [Nat.cast_pow] using hd'.trans hm)
      simp only [hEarlier, hLater, if_true, if_false]
      exact Int.modEq_zero_iff_dvd.mpr hd
    · simp [hEarlier, hLater, Int.ModEq.refl]

def residual (b : ℕ → ℤ) : ℕ → ℕ → ℤ
  | 0 => b
  | k + 1 => fun n => residual b k n - if k + 1 ∣ n then residual b k (k + 1) else 0

theorem residual_zero (b : ℕ → ℤ) (k n : ℕ) (hn : 0 < n) (hle : n ≤ k) :
    residual b k n = 0 := by
  induction k with
  | zero => omega
  | succ k ih =>
      by_cases he : n = k + 1
      · subst n; simp [residual]
      · have hnd : ¬ k + 1 ∣ n := Nat.not_dvd_of_pos_of_lt hn (by omega)
        simp [residual, hnd, ih (by omega)]

theorem residual_next_dvd {b : ℕ → ℤ} (k : ℕ) (hb : GaussSequence (residual b k)) :
    ((k + 1 : ℕ) : ℤ) ∣ residual b k (k + 1) := by
  rw [Int.natCast_dvd, Nat.dvd_iff_prime_pow_dvd_dvd]
  intro p a hp hd
  cases a with
  | zero => simp
  | succ r =>
      obtain ⟨n, en⟩ := hd
      have hn : 0 < n := by
        by_contra! e
        have : n = 0 := by omega
        simp [this] at en
      have hmul : n * p ^ (r + 1) = k + 1 := (en.trans (mul_comm _ _)).symm
      have hle : n * p ^ r < k + 1 := by
        rw [← hmul]
        exact Nat.mul_lt_mul_of_pos_left
          (Nat.pow_lt_pow_right hp.one_lt (Nat.lt_succ_self _)) hn
      have earlier := residual_zero b k (n * p ^ r) (Nat.mul_pos hn (pow_pos hp.pos _)) (by omega)
      have hm := hb p r n hp hn
      rw [hmul, earlier] at hm
      apply Int.natCast_dvd.mp
      simpa only [Nat.cast_pow] using (Int.modEq_zero_iff_dvd.mp hm)

theorem residual_gauss {b : ℕ → ℤ} (hb : GaussSequence b) (k : ℕ) :
    GaussSequence (residual b k) := by
  induction k with
  | zero => exact hb
  | succ k ih =>
      exact strip_gauss ih (k + 1) _ (residual_next_dvd k ih)

noncomputable def eulerExponent {b : ℕ → ℤ} (hb : GaussSequence b) (k : ℕ) : ℤ :=
  (residual_next_dvd k (residual_gauss hb k)).choose

theorem eulerExponent_mul {b : ℕ → ℤ} (hb : GaussSequence b) (k : ℕ) :
    residual b k (k + 1) = ((k + 1 : ℕ) : ℤ) * eulerExponent hb k :=
  (residual_next_dvd k (residual_gauss hb k)).choose_spec

end TangentConjecture

namespace TangentConjecture

open PowerSeries Finset

abbrev FSeries := PowerSeries ℚ

noncomputable def logSeries (b : ℕ → ℤ) : FSeries :=
  mk fun n => (b n : ℚ) / (n : ℚ)

noncomputable def logarithmicCoeffs (b : ℕ → ℤ) : FSeries :=
  mk fun n => if n = 0 then 0 else (b n : ℚ)

noncomputable def residualExponential (b : ℕ → ℤ) : FSeries :=
  (PowerSeries.exp ℚ).subst (logSeries b)

theorem logSeries_constant (b : ℕ → ℤ) : constantCoeff (logSeries b) = 0 := by
  simp [logSeries]

theorem logSeries_derivative (b : ℕ → ℤ) : X * (PowerSeries.derivative ℚ) (logSeries b) = logarithmicCoeffs b := by
  ext n
  cases n with
  | zero => simp [coeff_zero_eq_constantCoeff, logarithmicCoeffs]
  | succ n =>
      rw [coeff_succ_X_mul, coeff_derivative]
      simp only [logSeries, logarithmicCoeffs, coeff_mk, Nat.succ_ne_zero, if_false]
      simp only [Nat.cast_add, Nat.cast_one]
      have hn : ((n + 1 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast n.succ_ne_zero
      exact div_mul_cancel₀ _ (by simpa using hn)

theorem residualExponential_constant (b : ℕ → ℤ) :
    constantCoeff (residualExponential b) = 1 := by
  change MvPowerSeries.constantCoeff ((PowerSeries.exp ℚ).subst (logSeries b)) = 1
  rw [PowerSeries.constantCoeff_subst (.of_constantCoeff_zero (logSeries_constant b))]
  rw [finsum_eq_single _ 0]
  · simp
  · intro d hd
    change coeff d (PowerSeries.exp ℚ) • constantCoeff ((logSeries b) ^ d) = 0
    simp [logSeries_constant, zero_pow hd]

theorem residualExponential_derivative (b : ℕ → ℤ) :
    X * (PowerSeries.derivative ℚ) (residualExponential b) = logarithmicCoeffs b * residualExponential b := by
  rw [residualExponential, derivative_subst (.of_constantCoeff_zero (logSeries_constant b)),
    derivative_exp]
  calc
    _ = (X * (PowerSeries.derivative ℚ) (logSeries b)) * (PowerSeries.exp ℚ).subst (logSeries b) := by ring
    _ = _ := by rw [logSeries_derivative]

theorem derivative_prod (f g : FSeries) : (PowerSeries.derivative ℚ) (f * g) = (PowerSeries.derivative ℚ) f * g + f * (PowerSeries.derivative ℚ) g := by
  rw [(PowerSeries.derivative ℚ).leibniz]
  simp only [smul_eq_mul]
  ring

theorem log_equation_unique {B F G : FSeries} (hF : constantCoeff F = 1)
    (hG : constantCoeff G = 1) (hDF : X * (PowerSeries.derivative ℚ) F = B * F) (hDG : X * (PowerSeries.derivative ℚ) G = B * G) :
    F = G := by
  have hG0 : constantCoeff G ≠ 0 := by simp [hG]
  have hGi : G * G⁻¹ = 1 := PowerSeries.mul_inv_cancel G hG0
  have hZ : X * (PowerSeries.derivative ℚ) (F * G⁻¹) = 0 := by
    rw [derivative_prod, derivative_inv']
    calc
      _ = (X * (PowerSeries.derivative ℚ) F) * G⁻¹ - F * G⁻¹ ^ 2 * (X * (PowerSeries.derivative ℚ) G) := by ring
      _ = 0 := by rw [hDF, hDG]; linear_combination (-B * F * G⁻¹) * hGi
  have hz : (PowerSeries.derivative ℚ) (F * G⁻¹) = 0 := (mul_eq_zero.mp hZ).resolve_left X_ne_zero
  have hun : F * G⁻¹ = 1 :=
    derivative.ext (by simpa using hz) (by simp [hF, hG])
  calc
    F = (F * G⁻¹) * G := by
      rw [mul_assoc, PowerSeries.inv_mul_cancel _ hG0, mul_one]
    _ = G := by rw [hun, one_mul]

noncomputable def oneMinusUnit (m : ℕ) (hm : 0 < m) : (PowerSeries ℤ)ˣ :=
  (isUnit_iff_constantCoeff.mpr (show IsUnit (constantCoeff (1 - X ^ m : PowerSeries ℤ)) by
    simp [Nat.ne_of_gt hm])).unit

theorem oneMinusUnit_val (m : ℕ) (hm : 0 < m) :
    (oneMinusUnit m hm : PowerSeries ℤ) = 1 - X ^ m := by
  exact IsUnit.unit_spec _

noncomputable def rationalize : PowerSeries ℤ →+* FSeries := PowerSeries.map (Int.castRingHom ℚ)

noncomputable def rationalEulerUnit (m : ℕ) (hm : 0 < m) : FSeriesˣ :=
  Units.map rationalize.toMonoidHom (oneMinusUnit m hm)

theorem rationalEulerUnit_val (m : ℕ) (hm : 0 < m) :
    (rationalEulerUnit m hm : FSeries) = 1 - X ^ m := by
  change rationalize (oneMinusUnit m hm : PowerSeries ℤ) = _
  rw [oneMinusUnit_val]
  simp [rationalize]

noncomputable def unitLog : FSeriesˣ →* Multiplicative FSeries where
  toFun U := Multiplicative.ofAdd (↑U⁻¹ * (X * (PowerSeries.derivative ℚ) (U : FSeries)))
  map_one' := by simp
  map_mul' U V := by
    apply Multiplicative.toAdd.injective
    change (↑((U * V)⁻¹) : FSeries) * (X * (PowerSeries.derivative ℚ) ((↑U : FSeries) * (↑V : FSeries))) =
      (↑U⁻¹ : FSeries) * (X * (PowerSeries.derivative ℚ) (U : FSeries)) +
        (↑V⁻¹ : FSeries) * (X * (PowerSeries.derivative ℚ) (V : FSeries))
    rw [mul_inv_rev, Units.val_mul, derivative_prod]
    have hu : (↑U⁻¹ : FSeries) * ↑U = 1 := U.inv_val
    have hv : (↑V⁻¹ : FSeries) * ↑V = 1 := V.inv_val
    linear_combination ((↑U⁻¹ : FSeries) * X * (PowerSeries.derivative ℚ) (U : FSeries)) * hv +
      ((↑V⁻¹ : FSeries) * X * (PowerSeries.derivative ℚ) (V : FSeries)) * hu

theorem unitLog_zpow (U : FSeriesˣ) (z : ℤ) :
    (unitLog (U ^ z)).toAdd = (z : FSeries) * (unitLog U).toAdd := by
  rw [map_zpow]
  change z • (unitLog U).toAdd = _
  rw [zsmul_eq_mul]

noncomputable def geometric (m : ℕ) : FSeries :=
  mk fun n => if m ∣ n then 1 else 0

theorem shifted_dvd_iff {m n : ℕ} (hle : m ≤ n) : m ∣ n - m ↔ m ∣ n := by
  constructor
  · intro hd
    have h := Nat.dvd_add hd (dvd_rfl : m ∣ m)
    rwa [Nat.sub_add_cancel hle] at h
  · exact fun hd => Nat.dvd_sub hd dvd_rfl

theorem geometric_inverse {m : ℕ} (hm : 0 < m) :
    (1 - X ^ m) * geometric m = (1 : FSeries) := by
  ext n
  rw [sub_mul, one_mul, map_sub, coeff_X_pow_mul', coeff_one]
  by_cases hle : m ≤ n
  · have hn : n ≠ 0 := by omega
    simp [geometric, hle, hn, shifted_dvd_iff hle]
  · by_cases hn : n = 0
    · simp [geometric, hn, Nat.ne_of_gt hm]
    · have hnd : ¬ m ∣ n := Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
      simp [geometric, hle, hn, hnd]

theorem rationalEulerUnit_inv (m : ℕ) (hm : 0 < m) :
    (↑((rationalEulerUnit m hm)⁻¹) : FSeries) = geometric m := by
  have he : (↑((rationalEulerUnit m hm)⁻¹) : FSeries) *
      (rationalEulerUnit m hm : FSeries) = 1 := (rationalEulerUnit m hm).inv_val
  calc
    _ = (↑((rationalEulerUnit m hm)⁻¹) : FSeries) * (1 : FSeries) := by ring
    _ = _ * ((1 - X ^ m) * geometric m) := by rw [geometric_inverse hm]
    _ = geometric m := by
      rw [← rationalEulerUnit_val m hm, ← mul_assoc, he, one_mul]

theorem eulerUnit_derivative (m : ℕ) (hm : 0 < m) :
    X * (PowerSeries.derivative ℚ) (rationalEulerUnit m hm : FSeries) = -(m : FSeries) * X ^ m := by
  rw [rationalEulerUnit_val, map_sub, derivative_one, derivative_pow, derivative_X, mul_one,
    zero_sub]
  calc
    _ = -(m : FSeries) * (X ^ (m - 1) * X) := by ring
    _ = _ := by rw [← pow_succ, Nat.sub_add_cancel (by omega)]

noncomputable def eulerFactor (m : ℕ) (hm : 0 < m) (z : ℤ) : FSeriesˣ :=
  rationalEulerUnit m hm ^ (-z)

theorem eulerFactor_constant (m : ℕ) (hm : 0 < m) (z : ℤ) :
    constantCoeff (eulerFactor m hm z : FSeries) = 1 := by
  let eval := Units.map (constantCoeff : FSeries →+* ℚ).toMonoidHom
  have e : eval (rationalEulerUnit m hm) = 1 := by
    apply Units.ext
    change constantCoeff (rationalEulerUnit m hm : FSeries) = 1
    simp [rationalEulerUnit_val, Nat.ne_of_gt hm]
  change (eval (rationalEulerUnit m hm ^ (-z)) : ℚ) = 1
  rw [map_zpow, e, one_zpow]
  rfl

theorem eulerFactor_logCoeffs (m : ℕ) (hm : 0 < m) (z : ℤ) (n : ℕ) :
    coeff n (unitLog (eulerFactor m hm z)).toAdd =
      if n = 0 then 0 else if m ∣ n then ((m : ℤ) * z : ℚ) else 0 := by
  have hc : ((m : FSeries) * (z : FSeries)) = C ((m : ℤ) * z : ℚ) := by
    rw [Int.cast_natCast, map_mul, map_natCast, map_intCast]
  have eq : (unitLog (eulerFactor m hm z)).toAdd = C ((m : ℤ) * z : ℚ) *
      (X ^ m * geometric m) := by
    rw [eulerFactor, unitLog_zpow]
    change ((-z : ℤ) : FSeries) *
      ((↑((rationalEulerUnit m hm)⁻¹) : FSeries) * (X * (PowerSeries.derivative ℚ) (rationalEulerUnit m hm : FSeries))) = _
    rw [rationalEulerUnit_inv, eulerUnit_derivative, ← hc, Int.cast_neg]
    ring
  rw [eq, coeff_C_mul, coeff_X_pow_mul']
  by_cases hle : m ≤ n
  · have hn : n ≠ 0 := by omega
    simp [geometric, hle, hn, shifted_dvd_iff hle]
  · by_cases hn : n = 0
    · simp [hn, Nat.ne_of_gt hm]
    · have hnd : ¬ m ∣ n := Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
      simp [hle, hn, hnd]

theorem unitLog_times_unit (U : FSeriesˣ) :
    (unitLog U).toAdd * (U : FSeries) = X * (PowerSeries.derivative ℚ) (U : FSeries) := by
  change ((↑U⁻¹ : FSeries) * (X * (PowerSeries.derivative ℚ) (U : FSeries))) * (↑U : FSeries) = _
  have hu : (↑U⁻¹ : FSeries) * ↑U = 1 := U.inv_val
  linear_combination (X * (PowerSeries.derivative ℚ) (U : FSeries)) * hu

theorem residual_log_coeffs {b : ℕ → ℤ} (hb : GaussSequence b) (k : ℕ) :
    logarithmicCoeffs (residual b k) =
      (unitLog (eulerFactor (k + 1) (by omega) (eulerExponent hb k))).toAdd +
        logarithmicCoeffs (residual b (k + 1)) := by
  ext n
  rw [map_add (coeff n), eulerFactor_logCoeffs]
  simp only [logarithmicCoeffs, coeff_mk]
  by_cases hn : n = 0
  · simp [hn]
  · by_cases hd : k + 1 ∣ n
    · simp only [hn, hd, if_false, if_true, residual, Int.cast_sub]
      rw [eulerExponent_mul hb k]
      simp only [Int.cast_mul, Int.cast_natCast]
      ring
    · simp [hn, hd, residual]

theorem residual_exponential_step {b : ℕ → ℤ} (hb : GaussSequence b) (k : ℕ) :
    residualExponential (residual b k) =
      (eulerFactor (k + 1) (by omega) (eulerExponent hb k) : FSeries) *
        residualExponential (residual b (k + 1)) := by
  let U := eulerFactor (k + 1) (by omega) (eulerExponent hb k)
  let G := residualExponential (residual b (k + 1))
  change residualExponential (residual b k) = (U : FSeries) * G
  apply log_equation_unique (residualExponential_constant _) ?_
    (residualExponential_derivative _) ?_
  · rw [map_mul, residualExponential_constant, eulerFactor_constant, mul_one]
  · rw [derivative_prod]
    calc
      _ = (X * (PowerSeries.derivative ℚ) (U : FSeries)) * G + (U : FSeries) * (X * (PowerSeries.derivative ℚ) G) := by ring
      _ = _ := by
        rw [← unitLog_times_unit U, residualExponential_derivative, residual_log_coeffs hb k]
        change _ = ((unitLog U).toAdd + logarithmicCoeffs (residual b (k + 1))) *
          ((U : FSeries) * G)
        ring

noncomputable def finiteEuler {b : ℕ → ℤ} (hb : GaussSequence b) : ℕ → PowerSeries ℤ
  | 0 => 1
  | k + 1 => finiteEuler hb k *
      ↑((oneMinusUnit (k + 1) (by omega)) ^ (-(eulerExponent hb k)))

theorem rationalize_factor (m : ℕ) (hm : 0 < m) (z : ℤ) :
    rationalize ↑((oneMinusUnit m hm) ^ (-z)) = (eulerFactor m hm z : FSeries) := by
  change (↑(Units.map rationalize.toMonoidHom ((oneMinusUnit m hm) ^ (-z))) : FSeries) =
    (eulerFactor m hm z : FSeries)
  rw [map_zpow]
  rfl

theorem expand_finiteEuler {b : ℕ → ℤ} (hb : GaussSequence b) (k : ℕ) :
    residualExponential b =
      rationalize (finiteEuler hb k) * residualExponential (residual b k) := by
  induction k with
  | zero => simp [finiteEuler, residual]
  | succ k ih =>
      rw [ih, finiteEuler, map_mul, rationalize_factor, mul_assoc]
      rw [← residual_exponential_step hb k]

theorem coeff_mul_eq_zero_of_left {P Q : FSeries} (n : ℕ)
    (h : ∀ j ≤ n, coeff j P = 0) : coeff n (P * Q) = 0 := by
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun j hj => ?_
  have he := Finset.mem_antidiagonal.mp hj
  rw [h j.1 (by omega), zero_mul]

theorem residual_exponential_coeff {b : ℕ → ℤ} (k n : ℕ) (hle : n ≤ k) :
    coeff n (residualExponential (residual b k)) = coeff n (1 : FSeries) := by
  cases n with
  | zero => simp [coeff_zero_eq_constantCoeff, residualExponential_constant]
  | succ n =>
      have eq := congrArg (coeff (n + 1)) (residualExponential_derivative (residual b k))
      have h : ∀ j ≤ n + 1, coeff j (logarithmicCoeffs (residual b k)) = 0 := by
        intro j hj
        by_cases h : j = 0
        · simp [logarithmicCoeffs, h]
        · simp [logarithmicCoeffs, h, residual_zero b k j (by omega) (by omega)]
      rw [coeff_succ_X_mul, coeff_derivative, coeff_mul_eq_zero_of_left _ h] at eq
      have hne : (n : ℚ) + 1 ≠ 0 := by positivity
      have hz := (mul_eq_zero.mp eq).resolve_right hne
      simpa using hz

theorem rationalExponential_integral {b : ℕ → ℤ} (hb : GaussSequence b) (n : ℕ) :
    ∃ z : ℤ, coeff n (residualExponential b) = (z : ℚ) := by
  let P := rationalize (finiteEuler hb n)
  let G := residualExponential (residual b n)
  refine ⟨coeff n (finiteEuler hb n), ?_⟩
  rw [expand_finiteEuler hb n]
  change coeff n (P * G) = _
  have eq : coeff n P = ((coeff n (finiteEuler hb n) : ℤ) : ℚ) := by
    simp only [P, rationalize, coeff_map, Int.coe_castRingHom]
  rw [← eq]
  apply sub_eq_zero.mp
  rw [← map_sub]
  have e : P * G - P = (G - 1) * P := by ring
  rw [e]
  apply coeff_mul_eq_zero_of_left
  intro j hj
  rw [map_sub, residual_exponential_coeff n j hj, sub_self]

open OMA.S_oeis_a000182

theorem tangent_integrality (h : ShiftedGauss) (i : ℕ) (hi : 0 < i) (n : ℕ) :
    ∃ z : ℤ, coeff n (shiftedExponential i) = (z : ℚ) := by
  let b := fun j => tangentNumber (j + i)
  have hb : GaussSequence b := by
    intro p r n hp hn
    simpa [b] using (h i p n (r + 1) hi hp hn (by omega))
  exact rationalExponential_integral hb n

end TangentConjecture

theorem OMA.solution : type_of% @OMA.S_oeis_a000182.main := by
  exact ⟨TangentConjecture.tangent_periodicity, TangentConjecture.tangent_unshiftedGauss,
    TangentConjecture.tangent_shiftedGauss, TangentConjecture.tangent_integrality,
    TangentConjecture.tangent_continuedFraction⟩
