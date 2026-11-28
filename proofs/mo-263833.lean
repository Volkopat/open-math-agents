import OMAStatements.S_mo_263833

namespace QCCDisproof

open Matrix OMA.S_mo_263833

/-- The six directions of the counterexample. -/
def u : Fin 6 → Fin 3 → ℤ :=
  ![![-1, 2, 1], ![0, -3, 1], ![-3, -2, 0], ![2, -2, -2], ![-1, 0, 2], ![-1, 3, 0]]

/-- The six weights. -/
def w : Fin 6 → ℤ := ![10, 10, 100, 100, 100, 100]

/-- `100 • X k` as an integer matrix. -/
def XZ (k : Fin 6) : Matrix (Fin 3) (Fin 3) ℤ :=
  Matrix.of fun i j => 100 * w k * u k i * u k j + if i = j then 1 else 0

/-- `100 • ∑_{k ∈ S} X k` as an integer matrix. -/
def AZ (S : Finset (Fin 6)) : Matrix (Fin 3) (Fin 3) ℤ := ∑ k ∈ S, XZ k

/-- The test vector. -/
def xZ : Fin 3 → ℤ := ![4, 1, 3]

/-- The determinant of a `3 × 3` matrix, written out. -/
def det3 (A : Matrix (Fin 3) (Fin 3) ℤ) : ℤ :=
  A 0 0 * A 1 1 * A 2 2 - A 0 0 * A 1 2 * A 2 1 - A 0 1 * A 1 0 * A 2 2 +
    A 0 1 * A 1 2 * A 2 0 + A 0 2 * A 1 0 * A 2 1 - A 0 2 * A 1 1 * A 2 0

/-- The adjugate of a `3 × 3` matrix, written out. -/
def adj3 (A : Matrix (Fin 3) (Fin 3) ℤ) : Matrix (Fin 3) (Fin 3) ℤ :=
  !![A 1 1 * A 2 2 - A 1 2 * A 2 1, -(A 0 1 * A 2 2) + A 0 2 * A 2 1,
      A 0 1 * A 1 2 - A 0 2 * A 1 1;
    -(A 1 0 * A 2 2) + A 1 2 * A 2 0, A 0 0 * A 2 2 - A 0 2 * A 2 0,
      -(A 0 0 * A 1 2) + A 0 2 * A 1 0;
    A 1 0 * A 2 1 - A 1 1 * A 2 0, -(A 0 0 * A 2 1) + A 0 1 * A 2 0,
      A 0 0 * A 1 1 - A 0 1 * A 1 0]

theorem det_eq (A : Matrix (Fin 3) (Fin 3) ℤ) : A.det = det3 A := by
  rw [det_fin_three]
  rfl

theorem adj_eq (A : Matrix (Fin 3) (Fin 3) ℤ) : A.adjugate = adj3 A := by
  rw [adjugate_fin_three]
  rfl

/-- The six positive definite matrices `X k = w k • u k u kᵀ + (1/100) • 1`. -/
noncomputable def X (k : Fin 6) : Matrix (Fin 3) (Fin 3) ℝ :=
  (w k : ℝ) • vecMulVec (fun i => (u k i : ℝ)) (fun i => (u k i : ℝ)) + (1 / 100 : ℝ) • 1

theorem X_posDef (k : Fin 6) : (X k).PosDef := by
  have h1 : (vecMulVec (fun i => (u k i : ℝ)) (fun i => (u k i : ℝ))).PosSemidef := by
    have := posSemidef_vecMulVec_self_star (fun i => (u k i : ℝ))
    simpa using this
  have hw : (0 : ℝ) ≤ (w k : ℝ) := by
    fin_cases k <;> norm_num [w]
  exact PosDef.posSemidef_add (h1.smul hw) (PosDef.one.smul (by norm_num))

theorem X_eq (k : Fin 6) : X k = (1 / 100 : ℝ) • (XZ k).map (Int.cast : ℤ → ℝ) := by
  ext i j
  simp only [X, XZ, Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply, one_apply, map_apply,
    of_apply, smul_eq_mul]
  split_ifs <;> push_cast <;> ring

theorem sum_X (S : Finset (Fin 6)) :
    ∑ k ∈ S, X k = (1 / 100 : ℝ) • (AZ S).map (Int.cast : ℤ → ℝ) := by
  simp_rw [X_eq, ← Finset.smul_sum]
  congr 1
  ext i j
  simp [AZ, Matrix.sum_apply]

/-- The test vector, over `ℝ`. -/
def xR : Fin 3 → ℝ := fun i => (xZ i : ℝ)

theorem quad (A : Matrix (Fin 3) (Fin 3) ℤ) :
    xR ⬝ᵥ (((1 / 100 : ℝ) • A.map (Int.cast : ℤ → ℝ))⁻¹ *ᵥ xR) =
      (((100 * (xZ ⬝ᵥ (adj3 A *ᵥ xZ)) : ℚ) / (det3 A : ℚ) : ℚ) : ℝ) := by
  have hd : (A.map (Int.cast : ℤ → ℝ)).det = (A.det : ℝ) := by
    simpa using ((Int.castRingHom ℝ).map_det A).symm
  have ha : (A.map (Int.cast : ℤ → ℝ)).adjugate = A.adjugate.map (Int.cast : ℤ → ℝ) := by
    simpa using ((Int.castRingHom ℝ).map_adjugate A).symm
  have hn : xR ⬝ᵥ (A.adjugate.map (Int.cast : ℤ → ℝ) *ᵥ xR) =
      ((xZ ⬝ᵥ (A.adjugate *ᵥ xZ) : ℤ) : ℝ) := by
    simp only [xR, dotProduct, mulVec, map_apply, Fin.sum_univ_three]
    push_cast
    ring
  rw [inv_def, smul_mulVec, dotProduct_smul, det_smul, adjugate_smul, hd, ha,
    smul_mulVec, dotProduct_smul, hn, det_eq, adj_eq, Ring.inverse_eq_inv']
  simp only [Fintype.card_fin, smul_eq_mul]
  push_cast
  rcases eq_or_ne ((det3 A : ℤ) : ℝ) 0 with h0 | h0
  · rw [h0]
    simp
  · field_simp

/-- The exact value, over `ℚ`, of `xᵀ Q₆ x`. -/
def qval : ℚ :=
  ∑ S ∈ (Finset.univ : Finset (Fin 6)).powerset.filter (fun S => S.Nonempty),
    (-1 : ℚ) ^ (S.card + 1) * ((100 * (xZ ⬝ᵥ (adj3 (AZ S) *ᵥ xZ)) : ℚ) / (det3 (AZ S) : ℚ))

theorem qval_neg : qval < 0 := by
  decide +kernel

theorem form_eq :
    xR ⬝ᵥ (couponMatrix X *ᵥ xR) = (qval : ℝ) := by
  unfold couponMatrix qval
  rw [Matrix.sum_mulVec, dotProduct_sum]
  push_cast
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [smul_mulVec, dotProduct_smul, sum_X, quad, smul_eq_mul]
  push_cast
  ring

theorem not_posDef : ¬ (couponMatrix X).PosDef := by
  intro h
  have hx : xR ≠ 0 := by
    intro h0
    have := congrFun h0 0
    norm_num [xR, xZ] at this
  have hpos := h.dotProduct_mulVec_pos hx
  have hs : star xR = xR := by
    funext i
    simp
  rw [hs, form_eq] at hpos
  have := qval_neg
  have h' : ((qval : ℚ) : ℝ) < 0 := by exact_mod_cast this
  linarith

end QCCDisproof

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_263833.main) := by
  intro h
  exact QCCDisproof.not_posDef (h 3 6 (by norm_num) QCCDisproof.X QCCDisproof.X_posDef)
