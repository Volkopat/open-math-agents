import OMAStatements.S_oeis_a268149

/-!
# OEIS A268149

The weighted convolution reduces the double sum to the third absolute moment of one binomial row. Symmetry and a finite difference evaluate it as (2n)² times the central binomial coefficient at 2n.

Source: https://oeis.org/A268149
-/

open Finset Polynomial
open OMA.S_oeis_a268149

namespace CubicMoment268149

private noncomputable def row (m : ℕ) : ℤ[X] :=
  ∑ i ∈ range (m+1), monomial i (m.choose i : ℤ)

private theorem roweq (m : ℕ) : row m = (X+1)^m := by
  ext k
  simp only [row, finsetSum_coeff, coeff_monomial, coeff_X_add_one_pow]
  by_cases h : k ≤ m
  · simp [h, Nat.lt_succ_iff]
  · simp [h, Nat.lt_succ_iff, Nat.choose_eq_zero_of_lt (by omega : m<k)]

private def wt (m : ℕ) (p : ℤ[X]) : ℤ :=
  ∑ t ∈ range (2*m+1), p.coeff t * |(t:ℤ)-m|^3

private theorem wtSum (m : ℕ) {α : Type*} (s : Finset α) (f : α → ℤ[X]) :
    wt m (∑ i ∈ s, f i) = ∑ i ∈ s, wt m (f i) := by
  unfold wt
  simp_rw [finsetSum_coeff, sum_mul]
  rw [sum_comm]

private theorem wtMono (m t : ℕ) (h : t ≤ 2*m) (c : ℤ) :
    wt m (monomial t c) = c*|(t:ℤ)-m|^3 := by
  unfold wt
  simp [coeff_monomial, ite_mul, Nat.lt_succ_iff, h]

private theorem conv (m : ℕ) :
    (∑ i ∈ range (m+1), ∑ j ∈ range (m+1),
      (m.choose i : ℤ) * (m.choose j : ℤ) * |(i:ℤ)-j|^3) =
    wt m ((X+1)^(2*m)) := by
  rw [two_mul, pow_add, ←roweq, row, sum_mul, wtSum]
  apply sum_congr rfl
  intro i hi
  rw [mul_sum, wtSum, ←sum_range_reflect
    (fun j : ℕ => (m.choose i : ℤ) * (m.choose j : ℤ) * |(i:ℤ)-j|^3) (m+1)]
  apply sum_congr rfl
  intro j hj
  have h : j ≤ m := by simpa using hj
  simp only [Nat.add_sub_cancel, Nat.choose_symm h, monomial_mul_monomial,
    wtMono m (i+j) (by have := mem_range.mp hi; omega)]
  push_cast [Nat.cast_sub h]
  ring_nf

private def v (m k : ℕ) : ℤ := ((2*m).choose k : ℤ) * |(k:ℤ)-m|^3

private theorem half (m : ℕ) : wt m ((X+1)^(2*m)) = 2 * ∑ k ∈ range m, v m k := by
  change (∑ k ∈ range (2*m+1), _) = _
  simp only [coeff_X_add_one_pow]
  change (∑ k ∈ range (2*m+1), v m k) = _
  rw [show 2*m+1 = (m+1)+m by omega, sum_range_add, sum_range_succ]
  have hi : (∑ k ∈ range m, v m (m+1+k)) = ∑ k ∈ range m, v m k := by
    rw [←sum_range_reflect (fun k => v m (m+1+k)) m]
    apply sum_congr rfl
    intro k hk
    have hk' := mem_range.mp hk
    rw [show m+1+(m-1-k)=2*m-k by omega]
    unfold v
    rw [Nat.choose_symm (by omega : k≤2*m), Nat.cast_sub (by omega : k≤2*m)]
    push_cast
    rw [show (2:ℤ)*m-k-m = -((k:ℤ)-m) by ring, abs_neg]
  rw [hi]
  simp [v] at *
  ring

private def B (m k : ℤ) := k^2-(2*m+1)*k+m^2+2*m
private def T (m k : ℕ) : ℤ := k * B m k * ((2*m).choose k : ℤ)

private theorem diff (m k : ℕ) (hk : k < m) :
    T m (k+1)-T m k = 2*v m k := by
  have h := congrArg (fun x : ℕ => (x:ℤ)) (Nat.choose_succ_right_eq (2*m) k)
  push_cast [Nat.cast_sub (by omega : k ≤ 2*m)] at h
  unfold T v B
  rw [abs_of_nonpos (by omega : (k:ℤ)-m ≤ 0)]
  push_cast
  linear_combination (((k:ℤ)+1)^2-(2*m+1)*(k+1)+m^2+2*m)*h

private theorem moment (m : ℕ) : wt m ((X+1)^(2*m)) =
    (m:ℤ)^2 * ((2*m).choose m : ℤ) := by
  rw [half, mul_sum]
  calc
    _ = ∑ k ∈ range m, (T m (k+1) - T m k) :=
      sum_congr rfl fun k hk => (diff m k (mem_range.mp hk)).symm
    _ = _ := by rw [sum_range_sub]; simp only [T, B, Nat.cast_zero, zero_mul, sub_zero]; ring

private theorem closed (n : ℕ) : a n = ((2*n:ℕ):ℤ)^2 * ((4*n).choose (2*n) : ℤ) := by
  unfold a
  rw [conv, moment, show 2*(2*n)=4*n by omega]

end CubicMoment268149

namespace CubicMoment268149

private def C (m : ℕ) : ℤ := m.centralBinom
private theorem Cstep (m : ℕ) : ((m:ℤ)+1) * C (m+1) = 2*(2*m+1)*C m := by
  unfold C
  exact_mod_cast Nat.succ_mul_centralBinom_succ m

private theorem closedC (n : ℕ) : a n = (2*(n:ℤ))^2 * C (2*n) := by
  rw [closed]
  unfold C Nat.centralBinom
  push_cast
  rw [show 2*(2*n) = 4*n by omega]

private theorem twoSteps (m : ℕ) :
    ((m:ℤ)+2)*(m+1)*C (m+2) = 4*(2*m+3)*(2*m+1)*C m := by
  have e := Cstep (m+1)
  push_cast at e
  linear_combination (m+1:ℤ)*e + 2*(2*m+3)*Cstep m

end CubicMoment268149

theorem OMA.solution : type_of% @OMA.S_oeis_a268149.main := by
  intro k
  dsimp
  simp only [CubicMoment268149.closedC, Nat.cast_add, Nat.cast_ofNat]
  rw [show 2*(k+2)=2*k+2+2 by omega, show 2*(k+1)=2*k+2 by omega]
  have h := CubicMoment268149.twoSteps (2*k+2)
  have g := CubicMoment268149.twoSteps (2*k)
  push_cast at h g
  -- Cancel the second-order recurrence with the two consecutive central-binomial ratios.
  linear_combination 2*((k:ℤ)+1)*(k+2)*h - 12*k^2*g
