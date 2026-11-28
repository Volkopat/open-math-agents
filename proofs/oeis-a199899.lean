import OMAStatements.S_oeis_a199899

/-!
Proof of Barker's conjectures for A199899 (arrays x(0..3) with entries in -n..n, zero sum, and no
two adjacent elements both strictly positive or both strictly negative).

Group the arrays by their middle entries `(x1, x2)`. The last entry is `x3 = -(x0 + x1 + x2)`, so
the arrays with given middle entries correspond to the admissible first entries `x0`, which form
an integer interval `F n x1 x2` of size
* `2n + 1` if `x1 = x2 = 0`,
* `n + 1` if exactly one of `x1, x2` is `0`,
* `0` if `x1, x2` are both strictly positive or both strictly negative,
* `n + 1 - |x1 + x2|` if they have opposite strict signs.
Summing over `x1, x2` in `-n..n` and using `Σ_{k, j < n} |k - j| = (n^3 - n) / 3` gives
`3 a(n) = 4n^3 + 18n^2 + 20n + 3` for every `n`. The recurrence and the generating function
follow by comparing coefficients.
-/

namespace OMA.Helpers

open OMA.S_oeis_a199899 Finset

/-- The admissible first entries `x0` of an array with middle entries `x1, x2`
(the last entry is then `-(x0 + x1 + x2)`). -/
noncomputable def F (n : ℕ) (x1 x2 : ℤ) : Finset ℤ :=
  (Icc (-(n : ℤ)) n).filter (fun x0 =>
    -(n : ℤ) ≤ -(x0 + x1 + x2) ∧ -(x0 + x1 + x2) ≤ n ∧
    ¬ (0 < x0 ∧ 0 < x1) ∧ ¬ (x0 < 0 ∧ x1 < 0) ∧
    ¬ (0 < x1 ∧ 0 < x2) ∧ ¬ (x1 < 0 ∧ x2 < 0) ∧
    ¬ (0 < x2 ∧ 0 < -(x0 + x1 + x2)) ∧ ¬ (x2 < 0 ∧ -(x0 + x1 + x2) < 0))

theorem mem_F {n : ℕ} {x1 x2 x0 : ℤ} : x0 ∈ F n x1 x2 ↔
    (-(n : ℤ) ≤ x0 ∧ x0 ≤ n) ∧ -(n : ℤ) ≤ -(x0 + x1 + x2) ∧ -(x0 + x1 + x2) ≤ n ∧
    ¬ (0 < x0 ∧ 0 < x1) ∧ ¬ (x0 < 0 ∧ x1 < 0) ∧
    ¬ (0 < x1 ∧ 0 < x2) ∧ ¬ (x1 < 0 ∧ x2 < 0) ∧
    ¬ (0 < x2 ∧ 0 < -(x0 + x1 + x2)) ∧ ¬ (x2 < 0 ∧ -(x0 + x1 + x2) < 0) := by
  simp only [F, mem_filter, mem_Icc]

/-- Grouping the arrays by their middle entries `(x1, x2)`. -/
theorem a_eq_sum (n : ℕ) :
    a n = ∑ x1 ∈ Icc (-(n : ℤ)) n, ∑ x2 ∈ Icc (-(n : ℤ)) n, (F n x1 x2).card := by
  unfold a
  rw [card_eq_sum_card_fiberwise (f := fun x : ℤ × ℤ × ℤ × ℤ => (x.2.1, x.2.2.1))
    (t := Icc (-(n : ℤ)) n ×ˢ Icc (-(n : ℤ)) n)]
  · rw [sum_product]
    refine sum_congr rfl (fun x1 hx1 => sum_congr rfl (fun x2 hx2 => ?_))
    rw [mem_Icc] at hx1 hx2
    apply card_nbij' (fun x => x.1) (fun x0 => (x0, x1, x2, -(x0 + x1 + x2)))
    · rintro ⟨y0, y1, y2, y3⟩ hy
      simp only [mem_coe, mem_filter, mem_product, mem_Icc, Prod.mk.injEq] at hy
      simp only [mem_coe, mem_F]
      omega
    · intro x0 hx0
      simp only [mem_coe, mem_F] at hx0
      simp only [mem_coe, mem_filter, mem_product, mem_Icc, Prod.mk.injEq, and_true]
      omega
    · rintro ⟨y0, y1, y2, y3⟩ hy
      simp only [mem_coe, mem_filter, mem_product, mem_Icc, Prod.mk.injEq] at hy
      simp only [Prod.mk.injEq, true_and]
      omega
    · intro x0 _
      rfl
  · rintro ⟨y0, y1, y2, y3⟩ hy
    simp only [mem_coe, mem_filter, mem_product, mem_Icc] at hy
    simp only [coe_product, Set.mem_prod, mem_coe, mem_Icc]
    omega

theorem card_Icc_int (lo hi : ℤ) (h : lo ≤ hi + 1) : ((Icc lo hi).card : ℤ) = hi + 1 - lo := by
  rw [Int.card_Icc]
  omega

theorem h_zero_zero (n : ℕ) : ((F n 0 0).card : ℤ) = 2 * n + 1 := by
  have e : F n 0 0 = Icc (-(n : ℤ)) n := by
    ext x0
    rw [mem_F, mem_Icc]
    omega
  rw [e, card_Icc_int _ _ (by omega)]
  ring

theorem h_zero_pos (n : ℕ) (v : ℤ) (hv : 0 < v) (hvn : v ≤ n) :
    ((F n 0 v).card : ℤ) = n + 1 := by
  have e : F n 0 v = Icc (-v) (n - v) := by
    ext x0
    rw [mem_F, mem_Icc]
    omega
  rw [e, card_Icc_int _ _ (by omega)]
  ring

theorem h_zero_neg (n : ℕ) (v : ℤ) (hv : v < 0) (hvn : -(n : ℤ) ≤ v) :
    ((F n 0 v).card : ℤ) = n + 1 := by
  have e : F n 0 v = Icc (-n - v) (-v) := by
    ext x0
    rw [mem_F, mem_Icc]
    omega
  rw [e, card_Icc_int _ _ (by omega)]
  ring

theorem h_pos_zero (n : ℕ) (u : ℤ) (hu : 0 < u) (hun : u ≤ n) :
    ((F n u 0).card : ℤ) = n + 1 := by
  have e : F n u 0 = Icc (-(n : ℤ)) 0 := by
    ext x0
    rw [mem_F, mem_Icc]
    omega
  rw [e, card_Icc_int _ _ (by omega)]
  ring

theorem h_neg_zero (n : ℕ) (u : ℤ) (hu : u < 0) (hun : -(n : ℤ) ≤ u) :
    ((F n u 0).card : ℤ) = n + 1 := by
  have e : F n u 0 = Icc 0 (n : ℤ) := by
    ext x0
    rw [mem_F, mem_Icc]
    omega
  rw [e, card_Icc_int _ _ (by omega)]
  ring

theorem h_pos_pos (n : ℕ) (u v : ℤ) (hu : 0 < u) (hv : 0 < v) : ((F n u v).card : ℤ) = 0 := by
  have e : F n u v = ∅ := by
    ext x0
    rw [mem_F]
    simp only [notMem_empty, iff_false]
    omega
  rw [e, card_empty, Nat.cast_zero]

theorem h_neg_neg (n : ℕ) (u v : ℤ) (hu : u < 0) (hv : v < 0) : ((F n u v).card : ℤ) = 0 := by
  have e : F n u v = ∅ := by
    ext x0
    rw [mem_F]
    simp only [notMem_empty, iff_false]
    omega
  rw [e, card_empty, Nat.cast_zero]

theorem h_pos_neg (n : ℕ) (u v : ℤ) (hu : 0 < u) (hun : u ≤ n) (hv : v < 0)
    (hvn : -(n : ℤ) ≤ v) : ((F n u v).card : ℤ) = n + 1 - max (u + v) (-(u + v)) := by
  have e : F n u v = Icc (max (-(n : ℤ)) (-n - (u + v))) (min 0 (-(u + v))) := by
    ext x0
    rw [mem_F, mem_Icc]
    omega
  rw [e, card_Icc_int _ _ (by omega)]
  omega

theorem h_neg_pos (n : ℕ) (u v : ℤ) (hu : u < 0) (hun : -(n : ℤ) ≤ u) (hv : 0 < v)
    (hvn : v ≤ n) : ((F n u v).card : ℤ) = n + 1 - max (u + v) (-(u + v)) := by
  have e : F n u v = Icc (max 0 (-(u + v))) (min (n : ℤ) (n - (u + v))) := by
    ext x0
    rw [mem_F, mem_Icc]
    omega
  rw [e, card_Icc_int _ _ (by omega)]
  omega

/-- A sum over `-n..n`, split into `0` and the pairs `±(k + 1)`, `k < n`. -/
theorem sum_Icc_symm (n : ℕ) (f : ℤ → ℤ) :
    ∑ x ∈ Icc (-(n : ℤ)) n, f x = f 0 + ∑ k ∈ range n, (f ((k : ℤ) + 1) + f (-((k : ℤ) + 1))) := by
  induction n with
  | zero => simp
  | succ m ih =>
    have e : Icc (-((m + 1 : ℕ) : ℤ)) ((m + 1 : ℕ) : ℤ) =
        insert ((m : ℤ) + 1) (insert (-((m : ℤ) + 1)) (Icc (-(m : ℤ)) m)) := by
      ext x
      simp only [mem_insert, mem_Icc]
      push_cast
      omega
    rw [e, sum_insert, sum_insert, ih, sum_range_succ]
    · abel
    · simp only [mem_Icc]
      omega
    · simp only [mem_insert, mem_Icc]
      omega

theorem row_zero (n : ℕ) :
    ∑ x2 ∈ Icc (-(n : ℤ)) n, ((F n 0 x2).card : ℤ) = 2 * n + 1 + 2 * n * (n + 1) := by
  rw [sum_Icc_symm, h_zero_zero]
  have e : ∀ j ∈ range n, ((F n 0 ((j : ℤ) + 1)).card : ℤ) + ((F n 0 (-((j : ℤ) + 1))).card : ℤ)
      = 2 * ((n : ℤ) + 1) := by
    intro j hj
    rw [mem_range] at hj
    rw [h_zero_pos n _ (by omega) (by omega), h_zero_neg n _ (by omega) (by omega)]
    ring
  rw [sum_congr rfl e, sum_const, card_range, nsmul_eq_mul]
  ring

/-- The row `x1 = k + 1`. -/
theorem row_pos (n k : ℕ) (hk : k < n) :
    ∑ x2 ∈ Icc (-(n : ℤ)) n, ((F n ((k : ℤ) + 1) x2).card : ℤ) =
      (n + 1) + ∑ j ∈ range n, ((n : ℤ) + 1 - max ((k : ℤ) - j) ((j : ℤ) - k)) := by
  rw [sum_Icc_symm, h_pos_zero n _ (by omega) (by omega)]
  congr 1
  refine sum_congr rfl (fun j hj => ?_)
  rw [mem_range] at hj
  rw [h_pos_pos n _ _ (by omega) (by omega),
    h_pos_neg n _ _ (by omega) (by omega) (by omega) (by omega)]
  omega

/-- The row `x1 = -(k + 1)`. -/
theorem row_neg (n k : ℕ) (hk : k < n) :
    ∑ x2 ∈ Icc (-(n : ℤ)) n, ((F n (-((k : ℤ) + 1)) x2).card : ℤ) =
      (n + 1) + ∑ j ∈ range n, ((n : ℤ) + 1 - max ((k : ℤ) - j) ((j : ℤ) - k)) := by
  rw [sum_Icc_symm, h_neg_zero n _ (by omega) (by omega)]
  congr 1
  refine sum_congr rfl (fun j hj => ?_)
  rw [mem_range] at hj
  rw [h_neg_pos n _ _ (by omega) (by omega) (by omega) (by omega),
    h_neg_neg n _ _ (by omega) (by omega)]
  omega

theorem sum_cast_id (m : ℕ) : 2 * ∑ k ∈ range m, (k : ℤ) = m * (m - 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, mul_add, ih]
    push_cast
    ring

theorem sum_sub_id (m : ℕ) : 2 * ∑ k ∈ range m, ((m : ℤ) - k) = m * (m + 1) := by
  rw [sum_sub_distrib, mul_sub, sum_cast_id, sum_const, card_range, nsmul_eq_mul]
  ring

/-- `Σ_{k, j < n} |k - j| = (n^3 - n) / 3`. -/
theorem sum_max (n : ℕ) :
    3 * ∑ k ∈ range n, ∑ j ∈ range n, max ((k : ℤ) - j) ((j : ℤ) - k) = (n : ℤ) ^ 3 - n := by
  induction n with
  | zero => simp
  | succ m ih =>
    simp only [sum_range_succ, sum_add_distrib]
    have e1 : ∑ k ∈ range m, max ((k : ℤ) - m) ((m : ℤ) - k) = ∑ k ∈ range m, ((m : ℤ) - k) := by
      refine sum_congr rfl (fun k hk => ?_)
      rw [mem_range] at hk
      omega
    have e2 : ∑ j ∈ range m, max ((m : ℤ) - j) ((j : ℤ) - m) = ∑ k ∈ range m, ((m : ℤ) - k) := by
      refine sum_congr rfl (fun k hk => ?_)
      rw [mem_range] at hk
      omega
    have e3 : max ((m : ℤ) - m) ((m : ℤ) - m) = 0 := by simp
    rw [e1, e2, e3]
    have h2 := sum_sub_id m
    push_cast
    linear_combination ih + 3 * h2

/-- The closed form `3 a(n) = 4n^3 + 18n^2 + 20n + 3`. -/
theorem closed (n : ℕ) : 3 * (a n : ℤ) = 4 * (n : ℤ) ^ 3 + 18 * n ^ 2 + 20 * n + 3 := by
  rw [a_eq_sum]
  push_cast
  rw [sum_Icc_symm n (fun x1 => ∑ x2 ∈ Icc (-(n : ℤ)) n, ((F n x1 x2).card : ℤ)), row_zero]
  have e : ∀ k ∈ range n, (∑ x2 ∈ Icc (-(n : ℤ)) n, ((F n ((k : ℤ) + 1) x2).card : ℤ) +
      ∑ x2 ∈ Icc (-(n : ℤ)) n, ((F n (-((k : ℤ) + 1)) x2).card : ℤ)) =
      2 * ((n : ℤ) + 1) + 2 * ((n : ℤ) * (n + 1) -
        ∑ j ∈ range n, max ((k : ℤ) - j) ((j : ℤ) - k)) := by
    intro k hk
    rw [row_pos n k (mem_range.1 hk), row_neg n k (mem_range.1 hk), sum_sub_distrib, sum_const,
      card_range, nsmul_eq_mul]
    ring
  rw [sum_congr rfl e]
  simp only [sum_add_distrib, ← mul_sum, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
  have h := sum_max n
  linear_combination (-2) * h

theorem closedQ (n : ℕ) : (a n : ℚ) = (4 * (n : ℚ) ^ 3 + 18 * n ^ 2 + 20 * n + 3) / 3 := by
  have h : ((3 * (a n : ℤ) : ℤ) : ℚ) = ((4 * (n : ℤ) ^ 3 + 18 * n ^ 2 + 20 * n + 3 : ℤ) : ℚ) := by
    rw [closed n]
  push_cast at h
  linarith

theorem recurrence (n : ℕ) (hn : 4 < n) :
    (a n : ℤ) = 4 * a (n - 1) - 6 * a (n - 2) + 4 * a (n - 3) - a (n - 4) := by
  have h : ((a n : ℤ) : ℚ) =
      ((4 * a (n - 1) - 6 * a (n - 2) + 4 * a (n - 3) - a (n - 4) : ℤ) : ℚ) := by
    push_cast
    rw [closedQ n, closedQ (n - 1), closedQ (n - 2), closedQ (n - 3), closedQ (n - 4)]
    push_cast [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega,
      show 4 ≤ n by omega]
    ring
  exact_mod_cast h

open PowerSeries in
theorem gen_fun :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) =
      (X * (3 - X) * (5 - 2 * X + X ^ 2)) * ((1 - X) ^ 4)⁻¹ := by
  rw [PowerSeries.eq_mul_inv_iff_mul_eq (by simp)]
  set A : ℚ⟦X⟧ := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have hlhs : A * (1 - X) ^ 4 =
      A - C (4 : ℚ) * (A * X ^ 1) + C (6 : ℚ) * (A * X ^ 2) - C (4 : ℚ) * (A * X ^ 3) +
        A * X ^ 4 := by
    simp only [map_ofNat]
    ring
  have hrhs : (X * (3 - X) * (5 - 2 * X + X ^ 2) : ℚ⟦X⟧) =
      C (15 : ℚ) * X ^ 1 - C (11 : ℚ) * X ^ 2 + C (5 : ℚ) * X ^ 3 - C (1 : ℚ) * X ^ 4 := by
    simp only [map_ofNat, map_one]
    ring
  rw [hlhs, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', coeff_C, hA, coeff_mk]
  rcases Nat.lt_or_ge k 5 with hk | hk
  · interval_cases k <;> norm_num [closedQ]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 5 := ⟨k - 5, by omega⟩
    simp only [show ¬ (j + 5 = 0) by omega, show 1 ≤ j + 5 by omega, show 2 ≤ j + 5 by omega,
      show 3 ≤ j + 5 by omega, show 4 ≤ j + 5 by omega, show j + 5 - 1 = j + 4 by omega,
      show j + 5 - 2 = j + 3 by omega, show j + 5 - 3 = j + 2 by omega,
      show j + 5 - 4 = j + 1 by omega, show ¬ (j + 4 = 0) by omega, show ¬ (j + 3 = 0) by omega,
      show ¬ (j + 2 = 0) by omega, show ¬ (j + 1 = 0) by omega, if_true, if_false]
    rw [closedQ (j + 5), closedQ (j + 4), closedQ (j + 3), closedQ (j + 2), closedQ (j + 1)]
    push_cast
    ring

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a199899.main :=
  ⟨OMA.Helpers.gen_fun, OMA.Helpers.recurrence⟩
