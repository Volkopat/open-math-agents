import OMAStatements.S_oeis_a176832
import Mathlib

open PowerSeries

namespace OMA.QuadraticConvolution

open OMA.S_oeis_a176832

private theorem list_length (n : ℕ) : (aList n).length = n + 1 := by
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more n ih₀ ih₁ =>
    rw [aList, List.length_append, ih₁]
    rfl

private theorem list_coeff (n k : ℕ) (hk : k ≤ n) : (aList n).getD k 0 = a k := by
  induction n using Nat.twoStepInduction with
  | zero =>
    have : k = 0 := by omega
    subst k
    rfl
  | one => interval_cases k <;> rfl
  | more n ih₀ ih₁ =>
    by_cases he : k = n + 2
    · subst k
      rfl
    rw [aList, List.getD_append _ _ _ _ (by rw [list_length]; omega)]
    exact ih₁ (by omega)

private theorem convolution (n : ℕ) :
    a (n+2) = (∑ i ∈ Finset.range (n+2), a i * a (n+1-i)) + ((n : ℤ) + 1) := by
  unfold a
  rw [aList, List.getD_append_right _ _ _ _ (by rw [list_length])]
  rw [list_length, Nat.sub_self]
  simp only [List.getD_cons_zero]
  change (∑ i ∈ Finset.range (n+2), (aList (n+1)).getD i 0 *
      (aList (n+1)).getD (n+1-i) 0) + ((n : ℤ) + 1) = _
  apply congrArg (fun z : ℤ => z + ((n : ℤ) + 1))
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  rw [list_coeff _ _ (by omega), list_coeff _ _ (by omega)]
  rfl


private def A : ℤ⟦X⟧ := PowerSeries.mk a
private def E : ℤ⟦X⟧ := PowerSeries.mk fun n => if n = 0 then 1 else 1 * (n : ℤ) + (-1)
private def ones : ℤ⟦X⟧ := PowerSeries.mk fun _ => 1

private theorem forcingSeries : (1-X)^2 * E = 1 - 2*X + 2*X^2 := by
  have hone : (1-X) * ones = 1 := by
    ext n
    cases n with
    | zero => simp [sub_mul, ones, coeff_zero_eq_constantCoeff_apply]
    | succ n => simp [sub_mul, ones, coeff_succ_X_mul, coeff_one]
  have hs : (1-X)*E = 1 + C (-1)*X + C (1)*(X^2*ones) := by
    ext n
    rcases n with _ | (_ | n)
    · norm_num [E, ones, sub_mul, coeff_zero_eq_constantCoeff_apply]
    · simp only [sub_mul, one_mul, map_sub, map_add, coeff_C_mul, coeff_X, coeff_succ_X_mul,
        coeff_X_pow_mul', E, coeff_mk, coeff_one]
      norm_num
    · simp only [sub_mul, one_mul, map_sub, map_add, coeff_C_mul, coeff_X, coeff_succ_X_mul,
        coeff_X_pow_mul', E, coeff_mk, coeff_one, ones]
      have h1 : n + 2 ≠ 1 := by omega
      simp only [if_neg h1, Nat.succ_ne_zero, if_pos (by omega : 2 ≤ n+2), Nat.cast_succ, mul_zero, add_zero]
      simp <;> ring
  rw [show C (-1) = (-1 : ℤ⟦X⟧) by simp, show C (1) = (1 : ℤ⟦X⟧) by simp] at hs
  linear_combination (1-X)*hs + (1 : ℤ⟦X⟧)*X^2*hone

private theorem series_eq : A = (4 : ℤ⟦X⟧)*X + X*A^2 + E := by
  ext n
  rcases n with _ | (_ | n)
  · have ha : a 0 = 1 := by decide
    norm_num [A, E, ha, coeff_zero_eq_constantCoeff_apply]
  · have ha : a 1 = 5 := by decide
    have h0 : a 0 = 1 := by decide
    rw [show (4 : ℤ⟦X⟧) = C (4) by simp]
    simp only [map_add, coeff_C_mul, coeff_X, coeff_succ_X_mul, A, E, coeff_mk, ha]
    norm_num [coeff_zero_eq_constantCoeff_apply, h0]
  · have hno : n + 2 ≠ 1 := by omega
    simp only [map_add, A, E, coeff_mk]
    rw [show (4 : ℤ⟦X⟧) = C (4) by simp, coeff_C_mul, coeff_X, if_neg hno, mul_zero, zero_add,
      coeff_succ_X_mul, pow_two, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [coeff_mk, if_neg (by omega : n + 2 ≠ 0), Nat.cast_succ]
    convert convolution n using 1 <;> ring

private theorem differential :
    (1 - 7*X - X^2 + 31*X^3 - 40*X^4 + 16*X^5) * (d⁄dX ℤ (X*A)) +
      (2*X + 10*X^2 - 36*X^3 + 44*X^4 - 16*X^5)*A = 1 + 5*X - 18*X^2 + 22*X^3 - 8*X^4 := by
  let P : ℤ⟦X⟧ := 1-X
  let B : ℤ⟦X⟧ := 1-2*X*A
  let D : ℤ⟦X⟧ := 1 - 6*X - 7*X^2 + 24*X^3 - 16*X^4
  let U : ℤ⟦X⟧ := 1 + 5*X - 18*X^2 + 22*X^3 - 8*X^4
  let F : ℤ⟦X⟧ := d⁄dX ℤ (X*A)
  have hAE : P^2*A = (1 - 2*X + 2*X^2)+(4 : ℤ⟦X⟧)*X*P^2+X*P^2*A^2 := by
    dsimp [P]
    linear_combination (1-X)^2*series_eq + forcingSeries
  have hD : P^2*B^2 = D := by
    calc
      P^2*B^2 = P^2 - 4*X*(P^2*A) + 4*X^2*P^2*A^2 := by dsimp [B]; ring
      _ = D := by rw [hAE]; dsimp [P,D]; ring
  have hb : d⁄dX ℤ B = -2*F := by
    dsimp [B,F]
    rw [show 2*X*A = 2*(X*A) by ring, map_sub, derivative_one, Derivation.leibniz]
    have hzero : d⁄dX ℤ (2 : ℤ⟦X⟧) = 0 := Derivation.map_natCast _ 2
    simp [smul_eq_mul, hzero]
  have hdB : (-2*P)*B^2 - 4*P^2*B*F = d⁄dX ℤ D := by
    have hh := congrArg (fun Y => d⁄dX ℤ Y) hD
    have hp : d⁄dX ℤ P = -1 := by simp [P]
    have hp' : d⁄dX ℤ (P^2) = -2*P := by
      rw [derivative_pow, hp]
      simp
    rw [Derivation.leibniz, hp', derivative_pow, hb] at hh
    simp only [smul_eq_mul] at hh
    linear_combination hh
  have hdD : P*(d⁄dX ℤ D)+2*D = -4*U := by
    dsimp [P,D,U]
    have hd6 : d⁄dX ℤ (6 : ℤ⟦X⟧) = 0 := Derivation.map_natCast _ 6
    have hd7 : d⁄dX ℤ (7 : ℤ⟦X⟧) = 0 := Derivation.map_natCast _ 7
    have hd16 : d⁄dX ℤ (16 : ℤ⟦X⟧) = 0 := Derivation.map_natCast _ 16
    have hd24 : d⁄dX ℤ (24 : ℤ⟦X⟧) = 0 := Derivation.map_natCast _ 24
    simp [Derivation.leibniz, smul_eq_mul, hd6, hd7, hd16, hd24]
    ring
  have hK : 4*(P^3*B*F-U) = 0 := by
    linear_combination -P*hdB - 2*hD - hdD
  have hFour : (4 : ℤ⟦X⟧) ≠ 0 := by
    intro hz
    have hc := congrArg (constantCoeff (R := ℤ)) hz
    have hfour : constantCoeff (4 : ℤ⟦X⟧) = 4 := map_natCast (constantCoeff (R := ℤ)) 4
    rw [hfour, map_zero] at hc
    omega
  have hK' : P^3*B*F = U :=
    sub_eq_zero.mp ((mul_eq_zero.mp hK).resolve_left hFour)
  have hFinal : (D*P)*F = U*B := by
    linear_combination B*hK' - P*F*hD
  calc
    _ = (D*P)*F + (2*X*U)*A := by dsimp [D,P,F,U]; ring
    _ = _ := by rw [hFinal]; dsimp [B,U]; ring

end OMA.QuadraticConvolution

open OMA.S_oeis_a176832 OMA.QuadraticConvolution in
theorem OMA.solution : type_of% @OMA.S_oeis_a176832.main := by
  intro n hn
  have h₀ : n ≠ 0 := by omega
  have h₁ : n ≠ 1 := by omega
  have h₂ : n ≠ 2 := by omega
  have h₃ : n ≠ 3 := by omega
  have h₄ : n ≠ 4 := by omega
  have hj (j : ℕ) (hj' : j ≤ n) (f : ℤ⟦X⟧) :
      coeff n (X^j * f) = coeff (n-j) f := by simp [coeff_X_pow_mul', hj']
  have hX (f : ℤ⟦X⟧) : coeff n (X * f) = coeff (n-1) f := by
    simpa using hj 1 (by omega) f
  have hcoef (m : ℕ) : coeff m (d⁄dX ℤ (X*A)) = (a m : ℤ)*(m+1) := by
    simp only [coeff_derivative, coeff_succ_X_mul, A, coeff_mk]
  have heq := congrArg (coeff (R := ℤ) n) differential
  rw [show (2 : ℤ⟦X⟧) = C 2 by simp,
    show (5 : ℤ⟦X⟧) = C 5 by simp,
    show (7 : ℤ⟦X⟧) = C 7 by simp,
    show (8 : ℤ⟦X⟧) = C 8 by simp,
    show (10 : ℤ⟦X⟧) = C 10 by simp,
    show (16 : ℤ⟦X⟧) = C 16 by simp,
    show (18 : ℤ⟦X⟧) = C 18 by simp,
    show (22 : ℤ⟦X⟧) = C 22 by simp,
    show (31 : ℤ⟦X⟧) = C 31 by simp,
    show (36 : ℤ⟦X⟧) = C 36 by simp,
    show (40 : ℤ⟦X⟧) = C 40 by simp,
    show (44 : ℤ⟦X⟧) = C 44 by simp] at heq
  simp only [sub_mul, add_mul, one_mul, mul_assoc, map_sub, map_add, coeff_C_mul, hX,
    hj 2 (by omega), hj 3 (by omega), hj 4 (by omega), hj 5 hn, coeff_one, coeff_X,
    coeff_X_pow, if_neg h₀, if_neg h₁, if_neg h₂, if_neg h₃, if_neg h₄,
    hcoef, mul_zero, add_zero, sub_zero] at heq
  simp only [A, coeff_mk] at heq
  push_cast [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_sub (by omega : 2 ≤ n),
    Nat.cast_sub (by omega : 3 ≤ n), Nat.cast_sub (by omega : 4 ≤ n), Nat.cast_sub hn] at heq
  linear_combination heq