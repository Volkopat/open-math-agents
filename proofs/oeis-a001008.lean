import OMAStatements.S_oeis_a001008

/-!
A finite-difference proof of P. Bala's harmonic-number identity (OEIS A001008).
Tong Niu gave a generating-function proof in arXiv:2604.23206.

Let P_a(X) be the product of 1 + aX/j over j = 1, ..., n. For 1 ≤ k ≤ n,
P_{-1}(k) vanishes. The polynomial (P_{m-1} - P_{-1})/X has degree less
than n, so its nth forward difference is zero. Its value at zero is m H(n).
-/

namespace OMA

lemma harmonic_shifted_choose (n : ℕ) (x : ℚ) :
    Ring.choose ((n : ℚ) + x) n =
      ∏ j ∈ Finset.range n, (1 + x / ((j : ℚ) + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hs := Ring.choose_smul_choose (((n : ℚ) + x) + 1)
      (n := n + 1) (k := 1) (by omega)
    simp [nsmul_eq_mul] at hs
    rw [Finset.prod_range_succ, ← ih, Nat.cast_succ,
      show (n : ℚ) + 1 + x = ((n : ℚ) + x) + 1 by ring]
    have hn : (n : ℚ) + 1 ≠ 0 := by positivity
    field_simp [hn]
    linear_combination hs

lemma harmonic_binomial_product (m : ℤ) (n k : ℕ) (hk : k ≤ n) :
    Ring.choose ((m * k : ℤ) : ℚ) k *
        Ring.choose ((n + (m - 1) * k : ℤ) : ℚ) (n - k) =
      (n.choose k : ℚ) * ∏ j ∈ Finset.range n,
        (1 + ((m : ℚ) - 1) * k / ((j : ℚ) + 1)) := by
  push_cast
  have h := Ring.choose_smul_choose ((n : ℚ) + ((m : ℚ) - 1) * k)
    (k := n - k) (n := n) (Nat.sub_le n k)
  rw [nsmul_eq_mul, Nat.choose_symm hk, Nat.sub_sub_self hk, Nat.cast_sub hk,
    show (n : ℚ) + ((m : ℚ) - 1) * k - ((n : ℚ) - (k : ℚ)) =
      (m : ℚ) * (k : ℚ) by ring,
    harmonic_shifted_choose] at h
  rw [mul_comm (Ring.choose _ k)]
  exact h.symm

end OMA

namespace OMA.A001008

open Polynomial

noncomputable def slope (a : ℚ) : ℕ → ℚ[X]
  | 0 => 0
  | n + 1 =>
    let c := C (a / ((n : ℚ) + 1))
    slope a n * (1 + c * X) + c

noncomputable def poly (a : ℚ) (n : ℕ) : ℚ[X] := 1 + X * slope a n

noncomputable def divided (a : ℚ) (n : ℕ) : ℚ[X] := slope a n - slope (-1) n

theorem slope_degree (a : ℚ) (n : ℕ) : (slope a (n + 1)).natDegree ≤ n := by
  induction n with
  | zero => simp [slope]
  | succ n ih =>
    rw [slope, natDegree_add_C]
    apply natDegree_mul_le.trans
    apply add_le_add ih
    compute_degree

theorem divided_degree (a : ℚ) (n : ℕ) : (divided a (n + 1)).natDegree ≤ n :=
  (natDegree_sub_le _ _).trans (max_le (slope_degree a n) (slope_degree (-1) n))

theorem slope_at_zero (a : ℚ) (n : ℕ) : (slope a n).eval 0 = a * S_oeis_a001008.H n := by
  induction n with
  | zero => simp [slope, S_oeis_a001008.H]
  | succ n ih =>
    simp [slope, ih, S_oeis_a001008.H, Finset.sum_range_succ, mul_add, div_eq_mul_inv]

theorem divided_at_zero (a : ℚ) (n : ℕ) :
    (divided a n).eval 0 = (a + 1) * S_oeis_a001008.H n := by
  simp [divided, slope_at_zero, add_mul]

theorem poly_eval_prod (a x : ℚ) (n : ℕ) :
    (poly a n).eval x = ∏ j ∈ Finset.range n, (1 + a * x / ((j : ℚ) + 1)) := by
  induction n with
  | zero => simp [poly, slope]
  | succ n ih =>
    rw [Finset.prod_range_succ, ← ih]
    simp only [poly, slope, eval_add, eval_mul, eval_one, eval_C, eval_X]
    ring

theorem poly_neg_one_root (n k : ℕ) (hk : 0 < k) (hkn : k ≤ n) :
    (poly (-1) n).eval (k : ℚ) = 0 := by
  rw [poly_eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_range.mpr (by omega : k - 1 < n))
  have h : ((k - 1 : ℕ) : ℚ) + 1 = k := by exact_mod_cast Nat.sub_add_cancel hk
  rw [h]
  field_simp [show (k : ℚ) ≠ 0 by positivity]
  norm_num

theorem divided_at_node (a : ℚ) (n k : ℕ) (hk : 0 < k) (hkn : k ≤ n) :
    (divided a n).eval (k : ℚ) = (poly a n).eval (k : ℚ) / (k : ℚ) := by
  have h := poly_neg_one_root n k hk hkn
  simp only [poly, divided, eval_add, eval_sub, eval_one, eval_mul, eval_X] at h ⊢
  apply (eq_div_iff (show (k : ℚ) ≠ 0 by positivity)).2
  linear_combination -h

end OMA.A001008

open Finset

namespace OMA.A001008

lemma alternating_eval {n : ℕ} (P : Polynomial ℚ) (hP : P.natDegree < n) :
    ∑ k ∈ Finset.Icc 1 n, (-1 : ℚ) ^ (k + 1) * n.choose k * P.eval (k : ℚ) =
      P.eval 0 := by
  have hz := congrFun (Polynomial.fwdDiff_iter_eq_zero_of_degree_lt hP) (0 : ℚ)
  rw [fwdDiff_iter_eq_sum_shift] at hz
  have hsum : ∑ k ∈ range (n + 1),
      (-1 : ℚ) ^ (n - k) * n.choose k * P.eval (k : ℚ) = 0 := by
    simpa [zsmul_eq_mul, nsmul_eq_mul] using hz
  have hsign (k : ℕ) (hk : k ≤ n) :
      (-1 : ℚ) ^ k = (-1 : ℚ) ^ n * (-1 : ℚ) ^ (n - k) := by
    rw [← pow_add, show n + (n - k) = k + 2 * (n - k) by omega, pow_add, pow_mul]
    norm_num
  have halt : ∑ k ∈ range (n + 1),
      (-1 : ℚ) ^ k * n.choose k * P.eval (k : ℚ) = 0 := by
    calc
      _ = (-1 : ℚ) ^ n * ∑ k ∈ range (n + 1),
            (-1 : ℚ) ^ (n - k) * n.choose k * P.eval (k : ℚ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k hk ↦ ?_
        rw [hsign k (by simpa using Finset.mem_range.mp hk)]
        ring
      _ = 0 := by rw [hsum, mul_zero]
  have hrange : range (n + 1) = insert 0 (Icc 1 n) := by
    ext k
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [hrange, Finset.sum_insert (by simp)] at halt
  simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, Nat.cast_zero,
    one_mul] at halt
  calc
    _ = -(∑ k ∈ Icc 1 n, (-1 : ℚ) ^ k * n.choose k * P.eval (k : ℚ)) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun k _ ↦ by rw [pow_succ]; ring
    _ = _ := by linarith

end OMA.A001008

open OMA.A001008 in
theorem OMA.solution : type_of% @OMA.S_oeis_a001008.main := by
  intro m hm n
  cases n with
  | zero => simp [S_oeis_a001008.H]
  | succ n =>
    let a : ℚ := (m : ℚ) - 1
    have hd := alternating_eval (divided a (n + 1))
      (Nat.lt_succ_of_le (divided_degree a n))
    have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm
    rw [divided_at_zero, show a + 1 = (m : ℚ) by dsimp [a]; ring] at hd
    rw [one_div, ← div_eq_inv_mul, eq_div_iff hm', mul_comm, ← hd]
    apply Finset.sum_congr rfl
    intro k hk
    obtain ⟨hk0, hkn⟩ := Finset.mem_Icc.mp hk
    rw [divided_at_node a (n + 1) k hk0 hkn, poly_eval_prod,
      mul_assoc (((-1 : ℚ) ^ (k + 1)) / k), harmonic_binomial_product m (n + 1) k hkn]
    dsimp [a]
    ring
