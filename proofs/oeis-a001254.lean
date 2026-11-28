import OMAStatements.S_oeis_a001254

/-!
For an odd positive shift m the denominator is L(n-m)L(n+m), where L
extends the Lucas numbers to all integer indices. The reciprocal is a
difference of shifted reciprocal products, since L(n+m)-L(n-m)=L(m)L(n).
Reflection cancels every term of the finite boundary sum except n=m.

Sela Fried's proof for the related Fibonacci-square series (A007598)
uses an analogous telescoping identity. Here the Lucas numbers have
no zero term, and reflection leaves a different boundary contribution.
-/

namespace LucasReciprocal

open OMA.S_oeis_a001254 Finset
open scoped goldenRatio
noncomputable section

private def L (z : ℤ) : ℝ := φ^z + ψ^z

private theorem binet : ∀ n : ℕ, φ^n + ψ^n = (lucas n : ℝ)
  | 0 => by norm_num [lucas]
  | 1 => by simp [lucas, Real.goldenRatio_add_goldenConj]
  | n+2 => by
    calc
      _ = (φ^(n+1) + ψ^(n+1)) + (φ^n + ψ^n) := by
        rw [pow_add φ n 2, pow_add ψ n 2, Real.goldenRatio_sq, Real.goldenConj_sq]
        ring
      _ = _ := by rw [binet (n+1), binet n]; simp [lucas]

private theorem L_nat (n : ℕ) : L (n : ℤ) = (lucas n : ℝ) := by
  simpa only [L, zpow_natCast] using binet n

private theorem lucas_pos : ∀ n : ℕ, 0 < lucas n
  | 0 => by decide
  | 1 => by decide
  | n+2 => by rw [lucas]; exact Nat.add_pos_left (lucas_pos (n+1)) _

private theorem le_lucas : ∀ n : ℕ, n ≤ lucas n
  | 0 => by decide
  | 1 => by decide
  | n+2 => by rw [lucas]; have := le_lucas (n+1); have := lucas_pos n; omega

private theorem reflect_L (n : ℕ) : L (-(n : ℤ)) = (-1 : ℝ)^n * L (n : ℤ) := by
  simp only [L, zpow_neg, zpow_natCast, ← inv_pow, Real.inv_goldenRatio, Real.inv_goldenConj]
  simp only [neg_eq_neg_one_mul ψ, neg_eq_neg_one_mul φ, mul_pow]
  ring

private theorem L_ne (z : ℤ) : L z ≠ 0 := by
  obtain ⟨n, rfl | rfl⟩ := z.eq_nat_or_neg
  · rw [L_nat]
    exact_mod_cast (lucas_pos n).ne'
  · rw [reflect_L, L_nat]
    exact mul_ne_zero (by norm_num) (by exact_mod_cast (lucas_pos n).ne')

private theorem shifted (n m : ℕ) (hm : Odd m) :
    L ((n : ℤ) + m) - L ((n : ℤ) - m) = L (m : ℤ) * L (n : ℤ) ∧
    L ((n : ℤ) - m) * L ((n : ℤ) + m) =
      (a n : ℝ) - 5 * (-1 : ℝ)^n * (Nat.fib m : ℝ)^2 := by
  have uv : φ^m * ψ^m = -1 := by
    rw [← mul_pow, Real.goldenRatio_mul_goldenConj, hm.neg_one_pow]
  have ab : φ^n * ψ^n = (-1 : ℝ)^n := by rw [← mul_pow, Real.goldenRatio_mul_goldenConj]
  have addL : L ((n : ℤ) + m) = φ^n*φ^m + ψ^n*ψ^m := by
    simp only [L, zpow_add₀ Real.goldenRatio_ne_zero, zpow_add₀ Real.goldenConj_ne_zero,
      zpow_natCast]
  have subL : L ((n : ℤ) - m) = -(φ^n*ψ^m + ψ^n*φ^m) := by
    simp only [L, sub_eq_add_neg, zpow_add₀ Real.goldenRatio_ne_zero,
      zpow_add₀ Real.goldenConj_ne_zero, zpow_neg, zpow_natCast, ← inv_pow,
      Real.inv_goldenRatio, Real.inv_goldenConj, hm.neg_pow]
    ring
  have fib : 5 * (Nat.fib m : ℝ)^2 = (φ^m - ψ^m)^2 := by
    rw [Real.coe_fib_eq, div_pow, Real.sq_sqrt (by norm_num)]
    ring
  rw [addL, subL]
  constructor
  · simp only [L, zpow_natCast]
    ring
  · rw [show (a n : ℝ) = (φ^n + ψ^n)^2 by rw [binet]; simp [a], ← ab,
        show 5 * (φ^n * ψ^n) * (Nat.fib m : ℝ)^2 = (φ^n * ψ^n) * (5 * (Nat.fib m : ℝ)^2) by ring, fib]
    linear_combination -(φ^n + ψ^n)^2 * uv

private def h (m j : ℕ) : ℝ := 1 / (L (((j+1 : ℕ) : ℤ) - m) * L ((j+1 : ℕ) : ℤ))

private theorem h_summable (m : ℕ) : Summable (h m) := by
  apply (summable_nat_add_iff m).mp
  have cmp : Summable (fun n : ℕ => 1 / (((n+1 : ℕ) : ℝ)^2)) :=
    (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2))
  have val (n : ℕ) : h m (n+m) = 1 / ((lucas (n+1) : ℝ) * lucas (n+m+1)) := by
    unfold h
    rw [show ((n+m+1 : ℕ) : ℤ) - m = ((n+1 : ℕ) : ℤ) by omega, L_nat, L_nat]
  refine .of_nonneg_of_le (fun n => by rw [val]; positivity) (fun n => ?_) cmp
  rw [val]
  apply one_div_le_one_div_of_le (by positivity)
  rw [sq]
  exact mul_le_mul (by exact_mod_cast le_lucas (n+1))
    (by exact_mod_cast (show n+1 ≤ lucas (n+m+1) from (by omega : n+1 ≤ n+m+1).trans (le_lucas _)))
    (by positivity) (by positivity)

private theorem boundary (k : ℕ) :
    ∑ j ∈ range (2*k+1), h (2*k+1) j = 1 / (2 * L ((2*k+1 : ℕ) : ℤ)) := by
  let m := 2*k+1
  have hm : Odd m := ⟨k, rfl⟩
  have flip (i : ℕ) (hi : i ∈ range (2*k)) : h m (2*k-1-i) = - h m i := by
    have hi' := mem_range.mp hi
    let u := i+1
    let v := (2*k-1-i)+1
    have hu : u+v=m := by dsimp [u,v,m]; omega
    have sg : (-1 : ℝ)^u * (-1 : ℝ)^v = -1 := by rw [← pow_add, hu, hm.neg_one_pow]
    have opposite : (-1 : ℝ)^u = -(-1 : ℝ)^v := by
      rcases neg_one_pow_eq_or ℝ v with hv | hv <;> rw [hv] at sg ⊢ <;> linarith
    change 1 / (L ((v : ℤ) - m) * L (v : ℤ)) = - (1 / (L ((u : ℤ) - m) * L (u : ℤ)))
    rw [show (v : ℤ)-m = -(u : ℤ) by omega, show (u : ℤ)-m = -(v : ℤ) by omega,
      reflect_L, reflect_L, opposite]
    ring_nf
  have cancelled : ∑ j ∈ range (2*k), h m j = 0 := by
    have e := sum_range_reflect (h m) (2*k)
    rw [sum_congr rfl flip, sum_neg_distrib] at e
    linarith
  rw [sum_range_succ, cancelled, zero_add]
  norm_num [h, L]

private theorem term (m n : ℕ) (hm : Odd m) :
    1 / ((a (n+1) : ℝ) - 5 * (-1 : ℝ)^(n+1) * (Nat.fib m : ℝ)^2) =
      (L (m : ℤ))⁻¹ * (h m n - h m (n+m)) := by
  obtain ⟨addL, prodL⟩ := shifted (n+1) m hm
  rw [← prodL]
  unfold h
  rw [show ((n+m+1 : ℕ) : ℤ) - m = ((n+1 : ℕ) : ℤ) by omega,
      show ((n+m+1 : ℕ) : ℤ) = ((n+1 : ℕ) : ℤ) + m by omega]
  field_simp [L_ne]
  linarith

theorem series (k : ℕ) : HasSum
    (fun n : ℕ => 1 / ((a (n+1) : ℝ) - 5 * (-1 : ℝ)^(n+1) * (Nat.fib (2*k+1) : ℝ)^2))
    (1 / (2 * (a (2*k+1) : ℝ))) := by
  let m := 2*k+1
  have hm : Odd m := ⟨k, rfl⟩
  have hs := h_summable m
  have tail := (summable_nat_add_iff m).mpr hs
  have e := hs.sum_add_tsum_nat_add m
  have eb : ∑ i ∈ range m, h m i = 1 / (2 * L (m : ℤ)) := boundary k
  rw [eb] at e
  have tot := (hs.hasSum.sub tail.hasSum).mul_left (L (m : ℤ))⁻¹
  have value : (L (m : ℤ))⁻¹ * ((∑' n, h m n) - ∑' n, h m (n+m)) = 1 / (2 * (a m : ℝ)) := by
    rw [show (∑' n, h m n) - (∑' n, h m (n+m)) = 1 / (2 * L (m : ℤ)) by linarith [e],
      L_nat]
    simp only [a, Nat.cast_pow]
    ring
  rw [← value]
  exact tot.congr_fun (fun n => term m n hm)

end
end LucasReciprocal

theorem OMA.solution : type_of% @OMA.S_oeis_a001254.main := LucasReciprocal.series
