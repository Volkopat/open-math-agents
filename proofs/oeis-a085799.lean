import OMAStatements.S_oeis_a085799

/-!
# OEIS A085799 via the determinant of a weighted path

For a path with two or more vertices, the determinant depends only on the sum and
product of its edge weights. This is the path case of the weighted tree distance
determinant of Bapat, Kirkland and Neumann. The argument below works over any
commutative ring. Applying it to the successive odd gaps between squares gives
Fried's formula and the permutation interpretation from the registry statement.
-/

namespace WeightedPath

open Matrix

/-- The algebraic path distance is the sum of the edge weights between the two indices.
The label at a vertex is the cumulative weight from the initial vertex. -/
def pathMatrix {R : Type*} [CommRing R] (x : ℕ → R) (m : ℕ) : Matrix (Fin m) (Fin m) R :=
  fun i j => x (max i.val j.val) - x (min i.val j.val)

private def signMatrix (R : Type*) [CommRing R] (m : ℕ) : Matrix (Fin m) (Fin m) R :=
  fun i j => if j.val < i.val then 1 else -1

/-- Successive column differences leave a lower triangular sign matrix. -/
private lemma det_signMatrix (R : Type*) [CommRing R] (n : ℕ) :
    (signMatrix R (n + 1)).det = -((-2 : R) ^ n) := by
  let B : Matrix (Fin (n + 1)) (Fin (n + 1)) R := fun i j =>
    if j.val = 0 then signMatrix R (n + 1) i j else if i.val = j.val then -2 else 0
  have e : (signMatrix R (n + 1)).det = B.det := by
    apply det_eq_of_forall_col_eq_smul_add_pred (fun _ => 1)
    · intro i
      simp [B]
    · intro i j
      simp only [B, signMatrix, Fin.val_succ, Fin.val_castSucc]
      split_ifs <;> first | (exfalso; omega) | ring
  have lower : B.IsLowerTriangular := by
    intro i j hij
    change i.val < j.val at hij
    have hj : j ≠ 0 := by
      intro e
      subst j
      simp at hij
    simp [B, hj, ne_of_lt hij]
  rw [e, det_of_isLowerTriangular _ lower, Fin.prod_univ_succ]
  simp [B, signMatrix]

/-- Weighted path determinant over every commutative ring, without dividing by any weight. -/
theorem det_pathMatrix {R : Type*} [CommRing R] (x : ℕ → R) (n : ℕ) :
    (pathMatrix x (n + 2)).det = -(x (n + 1) - x 0) * (-2) ^ n *
      ∏ i : Fin (n + 1), (x (i.val + 1) - x i.val) := by
  let D := pathMatrix x (n + 2)
  let total := x (n + 1) - x 0
  let gap := fun i : Fin (n + 1) => x (i.val + 1) - x i.val
  -- The two endpoint columns add to the total path weight in every row.
  let A := D.updateCol 0 (fun i => D i 0 + D i (Fin.last (n + 1)))
  have detA : A.det = D.det :=
    D.det_updateCol_add_self (by
      intro e
      have := congrArg Fin.val e
      simp at this)
  have a0 (i : Fin (n + 2)) : A i 0 = total := by
    have hi : i.val ≤ n + 1 := by omega
    simp [A, D, pathMatrix, total, max_eq_right hi, min_eq_left hi]
  have aj (i : Fin (n + 2)) (j : Fin (n + 1)) : A i j.succ = D i j.succ :=
    updateCol_ne j.succ_ne_zero
  -- Row differences annihilate this constant column and extract one gap per row.
  let S := signMatrix R (n + 1)
  let B : Matrix (Fin (n + 2)) (Fin (n + 2)) R := fun i j =>
    Fin.cases (A 0 j) (fun r => Fin.cases 0 (fun c => gap r * S r c) j) i
  have diff : A.det = B.det := by
    apply det_eq_of_forall_row_eq_smul_add_pred (fun _ => 1)
    · intro j
      rfl
    · intro i j
      refine Fin.cases ?_ (fun c => ?_) j
      · simp [B, a0]
      · simp only [B, Fin.cases_succ, aj, D, pathMatrix, gap, S, signMatrix,
          Fin.val_succ, Fin.val_castSucc, one_mul]
        by_cases hc : c.val < i.val
        · have h₁ : c.val + 1 ≤ i.val := by omega
          have h₂ : c.val + 1 ≤ i.val + 1 := by omega
          rw [if_pos hc, max_eq_left h₁, min_eq_right h₁, max_eq_left h₂, min_eq_right h₂]
          ring
        · have h₁ : i.val ≤ c.val + 1 := by omega
          have h₂ : i.val + 1 ≤ c.val + 1 := by omega
          rw [if_neg hc, max_eq_right h₁, min_eq_left h₁, max_eq_right h₂, min_eq_left h₂]
          ring
  have minor : B.submatrix (0 : Fin (n + 2)).succAbove Fin.succ =
      Matrix.of (fun i j => gap i * S i j) := by
    ext i j
    simp [B, Matrix.submatrix]
  have detB : B.det = total * ((∏ i, gap i) * S.det) := by
    rw [det_succ_column_zero, Fin.sum_univ_succ, minor, det_mul_column]
    simp [B, a0]
  change D.det = _
  rw [← detA, diff, detB, show S.det = -((-2 : R) ^ n) from det_signMatrix R n]
  dsimp [total, gap]
  ring

/-- Arbitrary edge weights, including zero, with no order or positivity assumptions. -/
theorem det_edgeWeights {R : Type*} [CommRing R] (w : ℕ → R) (n : ℕ) :
    (pathMatrix (fun k => ∑ i ∈ Finset.range k, w i) (n + 2)).det =
      -(∑ i ∈ Finset.range (n + 1), w i) * (-2) ^ n * ∏ i : Fin (n + 1), w i.val := by
  simpa [Finset.sum_range_succ] using det_pathMatrix (fun k => ∑ i ∈ Finset.range k, w i) n

end WeightedPath

open OMA.S_oeis_a085799

namespace SquarePath

/-- Split the factorial into odd factors and powers of two times a smaller factorial. -/
private lemma odd_prod (p : ℕ) :
    (2 : ℚ) ^ (p + 1) * (p + 1).factorial * (∏ i : Fin (p + 1), (2 * (i.val : ℚ) + 3)) =
      ((2 * p + 3).factorial : ℚ) := by
  induction p with
  | zero => norm_num [Fin.prod_univ_one, Nat.factorial]
  | succ p ih =>
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [show 2 * (p + 1) + 3 = (2 * p + 3) + 1 + 1 by omega,
      Nat.factorial_succ (2 * p + 3 + 1), Nat.factorial_succ (2 * p + 3),
      Nat.factorial_succ (p + 1), pow_succ (2 : ℚ) (p + 1)]
    push_cast
    rw [← ih]
    ring

private lemma square_det (p : ℕ) :
    a (p + 2) = (-1 : ℚ) ^ (p + 1) * (((p : ℚ) + 3) / 2) *
      ((2 * p + 3).factorial : ℚ) / (p.factorial : ℚ) := by
  let x := fun k : ℕ => ((k : ℚ) + 1) ^ 2
  have mono : Monotone x := by
    intro i j hij
    dsimp [x]
    gcongr
  have hD : squareDistance (p + 2) = WeightedPath.pathMatrix x (p + 2) := by
    ext i j
    change |x i.val - x j.val| = x (max i.val j.val) - x (min i.val j.val)
    rcases le_total i.val j.val with h | h
    · rw [max_eq_right h, min_eq_left h, abs_of_nonpos (sub_nonpos.mpr (mono h))]
      ring
    · rw [max_eq_left h, min_eq_right h, abs_of_nonneg (sub_nonneg.mpr (mono h))]
  have inc (i : Fin (p + 1)) : x (i.val + 1) - x i.val = 2 * (i.val : ℚ) + 3 := by
    dsimp [x]
    push_cast
    ring
  rw [a, hD, WeightedPath.det_pathMatrix]
  simp_rw [inc]
  have power : (-2 : ℚ) ^ p = (-1 : ℚ) ^ p * 2 ^ p := by
    rw [← mul_pow]
    norm_num
  rw [← odd_prod, Nat.factorial_succ p, power]
  dsimp [x]
  push_cast
  rw [pow_succ (-1 : ℚ), pow_succ (2 : ℚ)]
  field_simp
  ring

end SquarePath

theorem OMA.solution : type_of% @OMA.S_oeis_a085799.main := by
  have formula (n : ℕ) (hn : 2 ≤ n) : a n = (-1 : ℚ) ^ (n - 1) * ((n : ℚ) + 1) / 2 *
      ((2 * n - 1).factorial : ℚ) / ((n - 2).factorial : ℚ) := by
    obtain ⟨p, rfl⟩ : ∃ p, n = p + 2 := ⟨n - 2, by omega⟩
    rw [SquarePath.square_det, show p + 2 - 1 = p + 1 by omega,
      show 2 * (p + 2) - 1 = 2 * p + 3 by omega,
      show p + 2 - 2 = p by omega]
    push_cast
    ring
  refine ⟨formula, ?_⟩
  intro n hn
  simp only [permutationCount, Fintype.card_embedding_eq, Fintype.card_fin,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  by_cases h : 2 ≤ n
  · have less : n + 1 ≤ 2 * n - 1 := by omega
    have fact := Nat.factorial_mul_descFactorial less
    rw [show 2 * n - 1 - (n + 1) = n - 2 by omega] at fact
    have e : ((2 * n - 1).factorial : ℚ) = (n - 2).factorial *
        ((2 * n - 1).descFactorial (n + 1) : ℚ) := by
      exact_mod_cast fact.symm
    rw [formula n h, e]
    rw [abs_div, abs_mul, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_nonneg (show (0 : ℚ) ≤ n + 1 by positivity), abs_of_pos (show (0 : ℚ) < 2 by norm_num),
      abs_of_nonneg (show (0 : ℚ) ≤ _ * _ by positivity), abs_of_nonneg (by positivity)]
    push_cast
    field_simp
  · obtain rfl : n = 1 := by omega
    norm_num [a, Matrix.det_fin_one, squareDistance, Nat.descFactorial]
