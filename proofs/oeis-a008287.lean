import OMAStatements.S_oeis_a008287

namespace OMA.P_oeis_a008287

open Polynomial

theorem key (n : ℕ) : (1 + X + X ^ 2 + X ^ 3 : ℤ[X]) ^ n =
    ∑ j ∈ Finset.range (n + 1),
      C ((-2 : ℤ) ^ j * (n.choose j : ℤ)) * (X ^ j * (1 + X) ^ (3 * n - 2 * j)) := by
  have h : (1 + X + X ^ 2 + X ^ 3 : ℤ[X]) = C (-2) * X * (1 + X) + (1 + X) ^ 3 := by
    simp only [map_neg, C_ofNat]; ring
  rw [h, add_pow]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have e : 3 * n - 2 * j = j + 3 * (n - j) := by omega
  rw [e, pow_add, ← pow_mul, mul_pow, mul_pow, ← C_pow]
  simp only [map_mul, map_natCast]
  ring

theorem coeff_term (n j k : ℕ) :
    (X ^ j * (1 + X : ℤ[X]) ^ (3 * n - 2 * j)).coeff k =
      if j ≤ k then ((3 * n - 2 * j).choose (k - j) : ℤ) else 0 := by
  rw [coeff_X_pow_mul', add_comm (1 : ℤ[X]) X, coeff_X_add_one_pow]

end OMA.P_oeis_a008287

open Polynomial in
theorem OMA.solution : type_of% @OMA.S_oeis_a008287.main := by
  intro n k _
  unfold OMA.S_oeis_a008287.T
  rw [OMA.P_oeis_a008287.key, finsetSum_coeff]
  simp only [coeff_C_mul, OMA.P_oeis_a008287.coeff_term]
  set g : ℕ → ℤ := fun j => (-2 : ℤ) ^ j * (n.choose j : ℤ) * ((3 * n - 2 * j).choose (k - j) : ℤ)
  have lhs : ∀ j ∈ Finset.range (n + 1),
      (-2 : ℤ) ^ j * (n.choose j : ℤ) * (if j ≤ k then ((3 * n - 2 * j).choose (k - j) : ℤ) else 0)
        = if j ≤ k then g j else 0 := by
    intro j _
    split_ifs <;> simp only [g, mul_zero]
  rw [Finset.sum_congr rfl lhs]
  rw [← Finset.sum_filter]
  have e1 : (Finset.range (n + 1)).filter (fun j => j ≤ k) = Finset.range (min n k + 1) := by
    ext j; simp only [Finset.mem_filter, Finset.mem_range]; omega
  have e2 : Finset.range (k + 1) = Finset.range (min n k + 1) ∪
      Finset.Ico (min n k + 1) (k + 1) := by
    ext j; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
  rw [e1, e2, Finset.sum_union]
  · rw [left_eq_add]
    refine Finset.sum_eq_zero fun j hj => ?_
    have hj := Finset.mem_Ico.mp hj
    have hlt : n < j := by omega
    simp [Nat.choose_eq_zero_of_lt hlt]
  · rw [Finset.disjoint_left]
    intro j h1 h2
    simp at h1 h2; omega
