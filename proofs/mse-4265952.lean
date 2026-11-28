import OMAStatements.S_mse_4265952

open OMA.S_mse_4265952

private def point (x y : ℝ) : Point2 := WithLp.toLp 2 ![x, y]

private def pentagon : Fin 5 → Point2 :=
  ![point 6 0, point (-1) 4, point (-2) 1, point (-2) (-1), point (-1) (-4)]

private theorem distSq (u v : Point2) :
    dist u v ^ 2 = (u 0 - v 0)^2 + (u 1 - v 1)^2 := by
  simp [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq, sq_abs]

private theorem distPoint (x y a b : ℝ) :
    dist (point x y) (point a b) = Real.sqrt ((x-a)^2 + (y-b)^2) := by
  rw [← Real.sqrt_sq (dist_nonneg (x := point x y) (y := point a b)), distSq]
  rfl

private theorem sinBound : (11 : ℝ) / 20 < Real.sin (Real.pi / 5) := by
  have hp := Real.pi_gt_three
  have h := Real.sin_gt_sub_cube (show (0 : ℝ) < 3 / 5 by norm_num)
  have h' := Real.sin_lt_sin_of_lt_of_le_pi_div_two
    (x := (3 : ℝ) / 5) (y := Real.pi / 5) (by linarith) (by linarith) (by linarith)
  norm_num at h
  linarith

private theorem nextVertex (i : Fin 5) :
    i + 1 = ![(1 : Fin 5), 2, 3, 4, 0] i := by
  fin_cases i <;> decide

theorem OMA.disproof : ¬ (type_of% @OMA.S_mse_4265952.main) := by
  intro h
  have hc : IsConvexPentagon pentagon := by
    left
    intro i j hij hj
    have hnext (i : Fin 5) : pentagon (i + 1) =
        ![point (-1) 4, point (-2) 1, point (-2) (-1), point (-1) (-4), point 6 0] i := by
      fin_cases i <;> rfl
    rw [hnext]
    fin_cases i <;> fin_cases j <;> first
      | exact (hij rfl).elim
      | exact (hj rfl).elim
      | norm_num [pentagon, point, cross2]
  have hz : (∑ i : Fin 5, pentagon i) = 0 := by
    ext j
    fin_cases j <;> norm_num [Fin.sum_univ_succ, pentagon, point]
  have hmax (i : Fin 5) : ‖pentagon i‖ ≤ ‖pentagon 0‖ := by
    have hsq : ‖pentagon i‖^2 ≤ ‖pentagon 0‖^2 := by
      fin_cases i <;> norm_num [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two,
        pentagon, point]
    nlinarith [norm_nonneg (pentagon i), norm_nonneg (pentagon 0)]
  have hdist (i j : Fin 5) : dist (pentagon i) (pentagon j) ≤ Real.sqrt 65 := by
    have hsq : dist (pentagon i) (pentagon j)^2 ≤ 65 := by
      fin_cases i <;> fin_cases j <;>
        norm_num [distSq, pentagon, point]
    nlinarith [dist_nonneg (x := pentagon i) (y := pentagon j), Real.sqrt_nonneg 65,
      Real.sq_sqrt (show (0 : ℝ) ≤ 65 by norm_num)]
  have hp : perimeter pentagon = 2 * Real.sqrt 65 + 2 * Real.sqrt 10 + 2 := by
    unfold perimeter
    simp_rw [nextVertex]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change dist (point 6 0) (point (-1) 4) + (dist (point (-1) 4) (point (-2) 1) +
      (dist (point (-2) 1) (point (-2) (-1)) + (dist (point (-2) (-1)) (point (-1) (-4)) +
        dist (point (-1) (-4)) (point 6 0)))) = _
    norm_num [distPoint]
    ring
  have h2 : Real.sqrt 65 < (81 : ℝ) / 10 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 65 by norm_num), Real.sqrt_nonneg 65]
  have h3 : (63 : ℝ) / 20 < Real.sqrt 10 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 10 by norm_num), Real.sqrt_nonneg 10]
  have hs (i j : Fin 5) : dist (pentagon i) (pentagon j) < perimeter pentagon / 3 := by
    rw [hp]
    linarith [hdist i j]
  have hr (x y : ℝ) : projOnto (point 6 0) (point x y) = point x 0 := by
    have hn : ‖point 6 0‖^2 = 36 := by
      norm_num [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, point]
    unfold projOnto
    rw [hn]
    ext j
    fin_cases j <;> simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
      Fin.sum_univ_two, point]
    ring
  have hleft : (∑ i : Fin 5, dist (pentagon 0) (projOnto (pentagon 0) (pentagon i))) = 30 := by
    have h49 : Real.sqrt 49 = 7 := by norm_num
    have h64 : Real.sqrt 64 = 8 := by norm_num
    norm_num [Fin.sum_univ_succ, pentagon, hr, distPoint, h49, h64]
  have hright : (∑ i : Fin 5, dist (pentagon 0) (pentagon i)) = 4 * Real.sqrt 65 := by
    norm_num [Fin.sum_univ_succ, pentagon, distPoint]
    ring
  have hh := h pentagon 0 hc hz hs hmax
  rw [hleft, hright] at hh
  have hpos : 0 < 2 * Real.sin (Real.pi / 5) := by linarith [sinBound]
  have hle : 30 ≤ 4 * Real.sqrt 65 / (2 * Real.sin (Real.pi / 5)) := by
    convert hh using 1
    ring
  have hle' := (le_div_iff₀ hpos).mp hle
  linarith [sinBound]