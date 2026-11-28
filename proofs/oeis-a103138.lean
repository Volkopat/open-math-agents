import OMAStatements.S_oeis_a103138
import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

namespace SchroederDelannoy

open Finset

def schroeder (n : ℕ) : ℕ :=
  ∑ k ∈ range (n + 1), catalan k * (n + k).choose (n - k)

private def term (n k : ℕ) : ℤ := (catalan k : ℤ) * (n + k).choose (2 * k)

private theorem term_zero {n k : ℕ} (h : n < k) : term n k = 0 := by
  simp [term, Nat.choose_eq_zero_of_lt (show n + k < 2 * k by omega)]

private theorem catalan_step (s : ℕ) :
    ((s : ℤ) + 2) * catalan (s + 1) = 2 * (2 * (s : ℤ) + 1) * catalan s := by
  have hn : (s + 2) * catalan (s + 1) = 2 * (2 * s + 1) * catalan s := by
    apply Nat.eq_of_mul_eq_mul_left (show 0 < s + 1 by omega)
    calc
      (s + 1) * ((s + 2) * catalan (s + 1)) = (s + 1) * (s + 1).centralBinom := by
        rw [succ_mul_catalan_eq_centralBinom]
      _ = 2 * (2 * s + 1) * s.centralBinom := Nat.succ_mul_centralBinom_succ s
      _ = (s + 1) * (2 * (2 * s + 1) * catalan s) := by
        rw [← succ_mul_catalan_eq_centralBinom]
        ring
  exact_mod_cast hn

/-- A termwise certificate for the large Schröder recurrence. -/
private theorem term_step (n k : ℕ) :
    ((n : ℤ) + 3) * term (n + 2) k + n * term n k =
      (2 * (n : ℤ) + 3) *
        (term (n + 1) k + 2 * (if k = 0 then 0 else term (n + 1) (k - 1))) := by
  cases k with
  | zero => simp [term]; ring
  | succ s =>
    by_cases h : s ≤ n + 1
    · let v := n + s + 1
      let c : ℤ := v.choose (2 * s)
      let b : ℤ := v.choose (2 * s + 1)
      let a : ℤ := v.choose (2 * s + 2)
      have stepB : b * (2 * (s : ℤ) + 1) = c * ((n : ℤ) + 1 - s) := by
        have edge := Nat.choose_succ_right_eq v (2 * s)
        rw [show v - 2 * s = n + 1 - s by dsimp [v]; omega] at edge
        dsimp only [b, c]
        exact_mod_cast edge
      have pas₁ : ((v + 1).choose (2 * s + 2) : ℤ) = b + a := by
        dsimp only [b, a]
        exact_mod_cast Nat.choose_succ_succ' v (2 * s + 1)
      have pas₂ : ((v + 1).choose (2 * s + 1) : ℤ) = c + b := by
        dsimp only [c, b]
        exact_mod_cast Nat.choose_succ_succ' v (2 * s)
      have pas₃ : ((v + 2).choose (2 * s + 2) : ℤ) = c + 2 * b + a := by
        push_cast [Nat.choose_succ_succ']
        change c + b + (b + a) = c + 2 * b + a
        ring
      have scaled : (2 * (s : ℤ) + 1) * (((n : ℤ) + 3) * c + 3 * b) =
          (2 * (n : ℤ) + 3) * ((s : ℤ) + 2) * c := by
        linear_combination 3 * stepB
      have combine :
          (catalan (s + 1) : ℤ) * (((n : ℤ) + 3) * c + 3 * b) =
            2 * (2 * (n : ℤ) + 3) * catalan s * c := by
        apply Int.eq_of_mul_eq_mul_left (a := 2 * (s : ℤ) + 1) (by omega)
        linear_combination (catalan (s + 1) : ℤ) * scaled +
          (2 * (n : ℤ) + 3) * c * catalan_step s
      simp only [Nat.succ_ne_zero, if_false, Nat.succ_sub_one, term]
      rw [show n + 2 + s.succ = v + 2 by dsimp [v]; omega,
        show n + 1 + s.succ = v + 1 by dsimp [v]; omega,
        show n + s.succ = v by rfl,
        show n + 1 + s = v by dsimp [v]; omega, show 2 * s.succ = 2 * s + 2 by omega]
      rw [pas₁, pas₃]
      change ((n : ℤ) + 3) * (catalan (s + 1) * (c + 2 * b + a)) +
        n * (catalan (s + 1) * a) =
          (2 * (n : ℤ) + 3) * (catalan (s + 1) * (b + a) + 2 * (catalan s * c))
      linear_combination combine
    · have big : n + 1 < s := by omega
      simp only [Nat.succ_ne_zero, if_false, Nat.succ_sub_one,
        term_zero (n := n + 2) (k := s.succ) (by omega),
        term_zero (n := n) (k := s.succ) (by omega),
        term_zero (n := n + 1) (k := s.succ) (by omega), term_zero big,
        mul_zero, add_zero]

private theorem sum_term (n l : ℕ) (h : n + 1 ≤ l) :
    ∑ k ∈ range l, term n k = (schroeder n : ℤ) := by
  unfold schroeder
  push_cast
  calc
    _ = ∑ k ∈ range (n + 1), term n k := by
      symm
      apply sum_subset (range_mono h)
      intro k _ hmiss
      exact term_zero (by simpa [mem_range] using hmiss)
    _ = _ := by
      apply sum_congr rfl
      intro k hk
      unfold term
      rw [Nat.choose_symm_of_eq_add (n := n + k) (a := 2 * k) (b := n - k) (by
        have := mem_range.mp hk
        omega)]

theorem schroeder_step (n : ℕ) :
    ((n : ℤ) + 3) * schroeder (n + 2) + n * schroeder n =
      3 * (2 * (n : ℤ) + 3) * schroeder (n + 1) := by
  have h := sum_congr (rfl : range (n + 3) = range (n + 3)) (fun k _ => term_step n k)
  have shifted : ∑ k ∈ range (n + 3), (if k = 0 then 0 else term (n + 1) (k - 1)) =
      (schroeder (n + 1) : ℤ) := by
    rw [sum_range_succ']
    simp only [Nat.succ_ne_zero, if_false, Nat.succ_sub_one, if_true, add_zero]
    exact sum_term (n + 1) (n + 2) (by omega)
  simp only [sum_add_distrib, ← mul_sum] at h
  rw [sum_term (n + 2) (n + 3) (by omega), sum_term n (n + 3) (by omega),
    sum_term (n + 1) (n + 3) (by omega), shifted] at h
  linear_combination h

section Series

open PowerSeries

/-- Coefficients of the zero-constant solution of the Schröder quadratic. -/
private def u : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => -u (n + 1) - ∑ k : Fin (n + 1), u (k + 1) * u (n + 1 - k)
termination_by n => n
decreasing_by
  all_goals omega

private noncomputable def U : PowerSeries ℤ := mk u

@[simp] private theorem coeff_U (n : ℕ) : coeff (R := ℤ) n U = u n := by simp [U]

@[simp] private theorem const_U : constantCoeff (R := ℤ) U = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_U, u]

private theorem coeff_shift (V : PowerSeries ℤ) (n : ℕ) :
    coeff (R := ℤ) n (X * V) = if 1 ≤ n then coeff (R := ℤ) (n - 1) V else 0 := by
  rw [← pow_one (X : PowerSeries ℤ), coeff_X_pow_mul']

private theorem coeff_U_sq (n : ℕ) :
    coeff (R := ℤ) (n + 2) (U ^ 2) = ∑ k : Fin (n + 1), u (k + 1) * u (n + 1 - k) := by
  rw [pow_two, coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => coeff (R := ℤ) i U * coeff (R := ℤ) j U)]
  simp only [coeff_U]
  rw [sum_range_succ', sum_range_succ]
  simp only [Nat.sub_self, u.eq_1, mul_zero, zero_mul, add_zero]
  rw [← sum_range (fun k => u (k + 1) * u (n + 1 - k))]
  apply sum_congr rfl
  intro k hk
  have : n + 2 - (k + 1) = n + 1 - k := by omega
  rw [this]

private theorem quadratic : U ^ 2 + (1 + X) * U = X := by
  ext n
  cases n with
  | zero => simp [pow_two, coeff_mul, u]
  | succ n =>
    cases n with
    | zero =>
      simp [pow_two, coeff_one_mul, add_mul, coeff_X, coeff_shift, u]
    | succ n =>
      simp only [map_add, add_mul, one_mul, coeff_U]
      rw [coeff_U_sq, coeff_shift, if_pos (by omega : 1 ≤ n + 1 + 1),
        show n + 1 + 1 - 1 = n + 1 by omega, coeff_X,
        if_neg (by omega : n + 1 + 1 ≠ 1), coeff_U, u]
      ring

private theorem series_smul (x y : PowerSeries ℤ) : x • y = x * y := rfl

private theorem ode_U :
    (1 + 6 * X + X ^ 2) * (derivative ℤ U) - (3 + X) * U =
      (1 - X : PowerSeries ℤ) := by
  have diff := congrArg (derivative ℤ) quadratic
  simp only [pow_two, map_add, Derivation.leibniz, derivative_X, Derivation.map_one_eq_zero,
    zero_add, one_mul, series_smul] at diff
  linear_combination (2 * U + 1 + X) * diff - (4 * derivative ℤ U + 2) * quadratic

private theorem seriesNat (c : ℕ) : (c : PowerSeries ℤ) = C (R := ℤ) (c : ℤ) :=
  (map_natCast (C (R := ℤ)) c).symm

private theorem u_step (n : ℕ) :
    ((n : ℤ) + 3) * u (n + 3) + 3 * (2 * (n : ℤ) + 3) * u (n + 2) +
      (n : ℤ) * u (n + 1) = 0 := by
  have h := congrArg (coeff (R := ℤ) (n + 2)) ode_U
  simp only [add_mul, one_mul, mul_assoc, map_add, map_sub,
    show (6 : PowerSeries ℤ) = C (R := ℤ) 6 from seriesNat 6,
    show (3 : PowerSeries ℤ) = C (R := ℤ) 3 from seriesNat 3,
    coeff_C_mul, coeff_shift, coeff_X_pow_mul', coeff_X, coeff_one,
    if_pos (by omega : 1 ≤ n + 2), if_pos (by omega : 2 ≤ n + 2),
    if_neg (by omega : n + 2 ≠ 0), if_neg (by omega : n + 2 ≠ 1),
    show n + 2 - 1 = n + 1 by omega, Nat.add_sub_cancel,
    coeff_derivative, coeff_U, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at h
  linear_combination h

private theorem u_schroeder (n : ℕ) :
    u (n + 1) = (-1 : ℤ) ^ n * schroeder n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => simp [u, schroeder]
    | 1 => norm_num [u, schroeder, sum_range_succ]
    | m + 2 =>
      have h := u_step m
      rw [ih (m + 1) (by omega), ih m (by omega), pow_succ (-1 : ℤ) m] at h
      apply Int.eq_of_mul_eq_mul_left (a := (m : ℤ) + 3) (by omega)
      rw [pow_add, show (-1 : ℤ) ^ 2 = 1 by norm_num, mul_one]
      linear_combination h - (-1 : ℤ) ^ m * schroeder_step m

noncomputable def sNeg : PowerSeries ℤ := mk fun n => (-1) ^ n * (schroeder n : ℤ)

noncomputable def gf : PowerSeries ℤ := (1 - X * sNeg) * (X * sNeg)

noncomputable def a (n : ℕ) : ℤ := coeff (R := ℤ) n gf

private theorem coeff_gf (n : ℕ) : coeff (R := ℤ) n gf = a n := rfl

private theorem eq_U : X * sNeg = U := by
  ext n
  cases n with
  | zero => simp [coeff_shift, u]
  | succ n =>
    simpa [coeff_shift, sNeg] using (u_schroeder n).symm

private theorem gf_linear : gf = (2 + X) * U - X := by
  unfold gf
  rw [eq_U]
  linear_combination -quadratic

private theorem a_zero : a 0 = 0 := by
  unfold a
  rw [gf_linear, coeff_zero_eq_constantCoeff_apply]
  simp

private theorem ode_gf :
    (2 + 13 * X + 8 * X ^ 2 + X ^ 3) * derivative ℤ gf -
      (7 + 11 * X + 2 * X ^ 2) * gf = (2 - 6 * X : PowerSeries ℤ) := by
  have dTwo : derivative ℤ (2 : PowerSeries ℤ) = 0 := by
    rw [show (2 : PowerSeries ℤ) = C (R := ℤ) 2 from seriesNat 2, derivative_C]
  rw [gf_linear]
  simp only [map_sub, Derivation.leibniz, map_add, derivative_X,
    dTwo, zero_add, series_smul, mul_one]
  linear_combination (2 + X) ^ 2 * ode_U

theorem main (n : ℕ) (hn : 3 ≤ n) :
    2 * (n : ℤ) * a n + (13 * n - 20 : ℤ) * a (n - 1) + (8 * n - 27 : ℤ) * a (n - 2) +
      ((n : ℤ) - 5) * a (n - 3) = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have h := congrArg (coeff (R := ℤ) (m + 2)) ode_gf
  simp only [add_mul, one_mul, mul_assoc, map_add, map_sub,
    show (2 : PowerSeries ℤ) = C (R := ℤ) 2 from seriesNat 2,
    show (13 : PowerSeries ℤ) = C (R := ℤ) 13 from seriesNat 13,
    show (8 : PowerSeries ℤ) = C (R := ℤ) 8 from seriesNat 8,
    show (7 : PowerSeries ℤ) = C (R := ℤ) 7 from seriesNat 7,
    show (11 : PowerSeries ℤ) = C (R := ℤ) 11 from seriesNat 11,
    show (6 : PowerSeries ℤ) = C (R := ℤ) 6 from seriesNat 6,
    coeff_C_mul, coeff_shift, coeff_X_pow_mul', coeff_X, coeff_C,
    if_pos (by omega : 1 ≤ m + 2), if_pos (by omega : 2 ≤ m + 2),
    if_neg (by omega : m + 2 ≠ 0), if_neg (by omega : m + 2 ≠ 1),
    show m + 2 - 1 = m + 1 by omega, Nat.add_sub_cancel,
    coeff_derivative, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, coeff_gf] at h
  simp only [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega,
    Nat.add_sub_cancel, Nat.cast_add, Nat.cast_ofNat]
  by_cases hm : m = 0
  · subst m
    norm_num [a_zero] at h ⊢
    linear_combination h
  · rw [if_pos (by omega : 3 ≤ m + 2), show m + 2 - 3 + 1 = m by omega] at h
    have hi : ((m + 2 - 3 : ℕ) : ℤ) + 1 = m := by omega
    rw [hi] at h
    linear_combination h

end Series

end SchroederDelannoy

theorem OMA.solution : type_of% @OMA.S_oeis_a103138.main :=
  SchroederDelannoy.main
