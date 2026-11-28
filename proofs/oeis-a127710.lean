import OMAStatements.S_oeis_a127710

namespace OMA.S_oeis_a127710

open Matrix Finset



/-- The 0/1 pattern of the triangle, over the integers. -/
def pat (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℤ :=
  fun n k => if (k : ℕ) ≤ n ∧ (n : ℕ) ≤ 2 * k then 1 else 0

lemma pat_lower (N : ℕ) : (pat N).IsLowerTriangular := by
  intro i j hij
  have h : i < j := OrderDual.toDual_lt_toDual.mp hij
  have h' : (i : ℕ) < j := h
  simp only [pat]
  rw [if_neg]
  omega

lemma pat_det (N : ℕ) : (pat N).det = 1 := by
  rw [det_of_isLowerTriangular _ (pat_lower N)]
  apply Finset.prod_eq_one
  intro i _
  simp only [pat]
  rw [if_pos ⟨le_rfl, by omega⟩]

lemma tri_eq (N : ℕ) :
    tri N = diagonal (fun n : Fin (N + 1) => 1 / ((n : ℚ) + 1)) * (pat N).map (Int.castRingHom ℚ) := by
  ext n k
  rw [diagonal_mul]
  simp only [tri, pat, map_apply]
  split_ifs <;> simp

/-- The candidate inverse: P^(-1) * diag(k+1). -/
noncomputable def B (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℚ :=
  ((pat N)⁻¹).map (Int.castRingHom ℚ) * diagonal (fun k : Fin (N + 1) => (k : ℚ) + 1)

lemma tri_mul_B (N : ℕ) : tri N * B N = 1 := by
  have hu : IsUnit (pat N).det := by rw [pat_det]; exact isUnit_one
  have hP : (pat N).map (Int.castRingHom ℚ) * ((pat N)⁻¹).map (Int.castRingHom ℚ) = 1 := by
    rw [← Matrix.map_mul, mul_nonsing_inv _ hu, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [tri_eq, B, Matrix.mul_assoc, ← Matrix.mul_assoc ((pat N).map _), hP, Matrix.one_mul,
    diagonal_mul_diagonal]
  rw [← diagonal_one]
  congr 1
  funext n
  have : (n : ℚ) + 1 ≠ 0 := by positivity
  field_simp

lemma inv_eq (N : ℕ) : (tri N)⁻¹ = B N := inv_eq_right_inv (tri_mul_B N)

lemma B_apply (N : ℕ) (n k : Fin (N + 1)) :
    B N n k = (((pat N)⁻¹ n k * ((k : ℤ) + 1) : ℤ) : ℚ) := by
  simp only [B, mul_diagonal, map_apply]
  push_cast
  rfl

theorem integral (N : ℕ) (n k : Fin (N + 1)) : ∃ z : ℤ, (tri N)⁻¹ n k = z :=
  ⟨(pat N)⁻¹ n k * ((k : ℤ) + 1), by rw [inv_eq, B_apply]⟩

lemma ruler_odd (t : ℕ) : ruler (2 * t + 1) = 1 := by
  unfold ruler
  rw [padicValNat.mul (by norm_num) (by omega), padicValNat.self (by norm_num),
    padicValNat.eq_zero_of_not_dvd (by omega)]

lemma ruler_double (m : ℕ) (hm : 0 < m) : ruler (2 * m) = ruler m + 1 := by
  unfold ruler
  rw [padicValNat.mul (by norm_num) (by omega), padicValNat.self (by norm_num),
    padicValNat.mul (by norm_num) (by omega), padicValNat.self (by norm_num)]
  omega

lemma key (n : ℕ) : ∑ k ∈ Icc ((n + 1) / 2) n, ruler (k + 1) = n + 1 := by
  induction n with
  | zero =>
    rw [show (0 + 1) / 2 = 0 from rfl, Icc_self, sum_singleton]
    exact ruler_odd 0
  | succ n ih =>
    rcases Nat.even_or_odd' n with ⟨t, rfl | rfl⟩
    · -- n = 2t
      rw [show (2 * t + 1 + 1) / 2 = t + 1 by omega]
      rw [show (2 * t + 1) / 2 = t by omega] at ih
      rw [show 2 * t + 1 = 2 * t + 1 from rfl, sum_Icc_succ_top (by omega)]
      rw [← add_sum_Ioc_eq_sum_Icc (by omega), ← Finset.Icc_add_one_left_eq_Ioc] at ih
      have h2 : ruler (2 * t + 1 + 1) = ruler (t + 1) + 1 := by
        rw [show 2 * t + 1 + 1 = 2 * (t + 1) by ring]
        exact ruler_double (t + 1) (by omega)
      rw [h2]
      omega
    · -- n = 2t+1
      rw [show (2 * t + 1 + 1 + 1) / 2 = t + 1 by omega]
      rw [show (2 * t + 1 + 1) / 2 = t + 1 by omega] at ih
      rw [sum_Icc_succ_top (by omega), ih]
      have h1 : ruler (2 * t + 1 + 1 + 1) = 1 := by
        rw [show 2 * t + 1 + 1 + 1 = 2 * (t + 1) + 1 by ring]
        exact ruler_odd (t + 1)
      rw [h1]

lemma tri_mulVec (N : ℕ) :
    tri N *ᵥ (fun k : Fin (N + 1) => ((ruler ((k : ℕ) + 1) : ℕ) : ℚ)) = fun _ => 1 := by
  funext n
  simp only [mulVec, dotProduct, tri]
  rw [Fin.sum_univ_eq_sum_range
    (fun k : ℕ => (if k ≤ (n : ℕ) ∧ (n : ℕ) ≤ 2 * k then 1 / ((n : ℚ) + 1) else 0) *
      ((ruler (k + 1) : ℕ) : ℚ)) (N + 1)]
  simp_rw [ite_mul, zero_mul]
  rw [← sum_filter]
  have hfilter : (range (N + 1)).filter (fun k => k ≤ (n : ℕ) ∧ (n : ℕ) ≤ 2 * k) =
      Icc (((n : ℕ) + 1) / 2) n := by
    ext k
    simp only [mem_filter, mem_range, mem_Icc]
    have := n.isLt
    omega
  rw [hfilter, ← mul_sum]
  have hk := key (n : ℕ)
  have hk' : ∑ k ∈ Icc (((n : ℕ) + 1) / 2) (n : ℕ), ((ruler (k + 1) : ℕ) : ℚ) = (n : ℚ) + 1 := by
    exact_mod_cast hk
  rw [hk']
  have : (n : ℚ) + 1 ≠ 0 := by positivity
  field_simp

theorem row_sums (N : ℕ) (n : Fin (N + 1)) :
    ∑ k, (tri N)⁻¹ n k = ((ruler ((n : ℕ) + 1) : ℕ) : ℚ) := by
  have hBA : B N * tri N = 1 := mul_eq_one_comm.mp (tri_mul_B N)
  have h : (tri N)⁻¹ *ᵥ (fun _ => (1 : ℚ)) = fun k : Fin (N + 1) => ((ruler ((k : ℕ) + 1) : ℕ) : ℚ) := by
    rw [← tri_mulVec N, mulVec_mulVec, inv_eq, hBA, one_mulVec]
  have := congrFun h n
  simpa [mulVec, dotProduct] using this

/-- Barry's two conjectures, for every truncation of the triangle. -/
theorem conjecture : ∀ N : ℕ, (∀ n k : Fin (N + 1), ∃ z : ℤ, (tri N)⁻¹ n k = z) ∧
    (∀ n : Fin (N + 1), ∑ k, (tri N)⁻¹ n k = ((ruler ((n : ℕ) + 1) : ℕ) : ℚ)) :=
  fun N => ⟨integral N, row_sums N⟩

end OMA.S_oeis_a127710

theorem OMA.solution : type_of% @OMA.S_oeis_a127710.main :=
  OMA.S_oeis_a127710.conjecture
