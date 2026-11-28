import OMAStatements.S_mo_5041

namespace OMA.S_mo_5041_Proof

open OMA.S_mo_5041 MvPolynomial

private noncomputable def G : MvPolynomial (Fin 5) ℂ :=
  X 0 * X 2 * X 3 * X 4

private noncomputable def H : MvPolynomial (Fin 5) ℂ :=
  X 1 * X 2 * X 3 * X 4

private lemma eval_eq_of_not_mem_vars {P : MvPolynomial (Fin 5) ℂ} {x y : Fin 5 → ℂ}
    (h4 : (4 : Fin 5) ∉ P.vars) (hxy : ∀ i : Fin 5, i ≠ 4 → x i = y i) :
    eval x P = eval y P := by
  simp only [eval_eq']
  refine Finset.sum_congr rfl fun d hd => ?_
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hdi : d i = 0
  · simp [hdi]
  · have hi_vars : i ∈ P.vars :=
      (mem_vars_iff_mem_support i).mpr ⟨d, hd, Finsupp.mem_support_iff.mpr hdi⟩
    have hi_ne : i ≠ 4 := fun h => h4 (h ▸ hi_vars)
    rw [hxy i hi_ne]

private lemma eval_linSubst_X (A : Matrix (Fin 5) (Fin 5) ℂ) (x : Fin 5 → ℂ) (i : Fin 5) :
    eval x (linSubst A (X i)) = (A.mulVec x) i := by
  unfold linSubst
  rw [aeval_X, map_sum]
  simp only [map_mul, eval_C, eval_X, Matrix.mulVec, dotProduct]

private lemma linSubst_G_H_not_avoid_4 (A : Matrix (Fin 5) (Fin 5) ℂ) (hA : IsUnit A.det) :
    ¬ ((4 : Fin 5) ∉ (linSubst A G).vars ∧ (4 : Fin 5) ∉ (linSubst A H).vars) := by
  rintro ⟨hG4, hH4⟩
  have hcol : ∃ k : Fin 5, A k 4 ≠ 0 := by
    by_contra hall
    push Not at hall
    have hdet0 : A.det = 0 := Matrix.det_eq_zero_of_column_eq_zero 4 hall
    rw [hdet0] at hA
    exact not_isUnit_zero hA
  obtain ⟨k, hk⟩ := hcol
  let w : Fin 5 → ℂ := A⁻¹.mulVec (fun _ => 1)
  have hAw : ∀ i : Fin 5, (A.mulVec w) i = 1 := by
    intro i
    dsimp [w]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hA, Matrix.one_mulVec]
  let t : ℂ := -(A k 4)⁻¹
  let v : Fin 5 → ℂ := Function.update w 4 (w 4 + t)
  have hvw : ∀ i : Fin 5, i ≠ 4 → v i = w i := fun i hi => Function.update_of_ne hi _ _
  have hAv : ∀ i : Fin 5, (A.mulVec v) i = 1 + t * A i 4 := by
    intro i
    have hsub : v = w + t • Pi.single 4 (1 : ℂ) := by
      ext j
      by_cases hj : j = 4
      · subst hj; simp [v]
      · simp [v, Function.update_of_ne hj, Pi.single_eq_of_ne hj]
    rw [hsub, Matrix.mulVec_add, Matrix.mulVec_smul, Pi.add_apply, Pi.smul_apply, hAw i,
      smul_eq_mul, Matrix.mulVec_single_one, Matrix.col_apply]
  have hAk0 : (A.mulVec v) k = 0 := by
    rw [hAv k]
    dsimp [t]
    rw [neg_mul, inv_mul_cancel₀ hk, add_neg_cancel]
  have hG_eq : eval v (linSubst A G) = eval w (linSubst A G) :=
    eval_eq_of_not_mem_vars hG4 hvw
  have hH_eq : eval v (linSubst A H) = eval w (linSubst A H) :=
    eval_eq_of_not_mem_vars hH4 hvw
  have hG_eval : ∀ x, eval x (linSubst A G) =
      (A.mulVec x) 0 * (A.mulVec x) 2 * (A.mulVec x) 3 * (A.mulVec x) 4 := by
    intro x
    simp only [G, linSubst, map_mul]
    rw [← linSubst, ← linSubst, ← linSubst, ← linSubst]
    simp only [eval_linSubst_X]
  have hH_eval : ∀ x, eval x (linSubst A H) =
      (A.mulVec x) 1 * (A.mulVec x) 2 * (A.mulVec x) 3 * (A.mulVec x) 4 := by
    intro x
    simp only [H, linSubst, map_mul]
    rw [← linSubst, ← linSubst, ← linSubst, ← linSubst]
    simp only [eval_linSubst_X]
  rw [hG_eval, hG_eval] at hG_eq
  rw [hH_eval, hH_eval] at hH_eq
  simp only [hAw, mul_one] at hG_eq hH_eq
  fin_cases k
  · change A.mulVec v 0 = 0 at hAk0; rw [hAk0] at hG_eq; norm_num at hG_eq
  · change A.mulVec v 1 = 0 at hAk0; rw [hAk0] at hH_eq; norm_num at hH_eq
  · change A.mulVec v 2 = 0 at hAk0; rw [hAk0] at hG_eq; norm_num at hG_eq
  · change A.mulVec v 3 = 0 at hAk0; rw [hAk0] at hG_eq; norm_num at hG_eq
  · change A.mulVec v 4 = 0 at hAk0; rw [hAk0] at hG_eq; norm_num at hG_eq

theorem main_proof :
    ∃ (G H : MvPolynomial (Fin 5) ℂ) (d : ℕ) (pt : Fin 3 → ℂ × ℂ),
      G.IsHomogeneous d ∧ H.IsHomogeneous d ∧
      (∀ a b : ℂ, a • G = b • H → a = 0 ∧ b = 0) ∧
      (∀ A : Matrix (Fin 5) (Fin 5) ℂ, IsUnit A.det →
        ¬ (4 ∉ (linSubst A G).vars ∧ 4 ∉ (linSubst A H).vars)) ∧
      (∀ i, pt i ≠ 0) ∧ (∀ i j, i ≠ j → (pt i).1 * (pt j).2 ≠ (pt j).1 * (pt i).2) ∧
      ∀ i, IsProdLinear (C (pt i).2 * G - C (pt i).1 * H) := by
  let pt : Fin 3 → ℂ × ℂ := ![(0, 1), (1, 0), (1, 1)]
  refine ⟨G, H, 4, pt, ?_, ?_, ?_, linSubst_G_H_not_avoid_4, ?_, ?_, ?_⟩
  · -- G.IsHomogeneous 4
    have h1 := ((isHomogeneous_X ℂ (0 : Fin 5)).mul (isHomogeneous_X ℂ (2 : Fin 5))).mul
      (isHomogeneous_X ℂ (3 : Fin 5))
    simpa [G] using h1.mul (isHomogeneous_X ℂ (4 : Fin 5))
  · -- H.IsHomogeneous 4
    have h1 := ((isHomogeneous_X ℂ (1 : Fin 5)).mul (isHomogeneous_X ℂ (2 : Fin 5))).mul
      (isHomogeneous_X ℂ (3 : Fin 5))
    simpa [H] using h1.mul (isHomogeneous_X ℂ (4 : Fin 5))
  · -- linear independence of G and H
    intro a b hab
    have h1 := congrArg (eval (![1, 0, 1, 1, 1] : Fin 5 → ℂ)) hab
    have h2 := congrArg (eval (![0, 1, 1, 1, 1] : Fin 5 → ℂ)) hab
    simp [G, H, smul_eq_C_mul] at h1 h2
    exact ⟨h1, h2.symm⟩
  · -- pt i ≠ 0
    intro i
    fin_cases i <;> simp [pt]
  · -- pairwise non-proportional
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [pt]
  · -- three completely decomposable fibers
    intro i
    fin_cases i
    · -- i = 0: G
      refine ⟨?_, 1, [X 0, X 2, X 3, X 4], ?_, ?_⟩
      · intro h0
        have he := congrArg (eval (![1, 0, 1, 1, 1] : Fin 5 → ℂ)) h0
        simp [pt, G, H] at he
      · intro l hl
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl | rfl | rfl <;> exact isHomogeneous_X ℂ _
      · simp [pt, G, H]; ring
    · -- i = 1: -H
      refine ⟨?_, -1, [X 1, X 2, X 3, X 4], ?_, ?_⟩
      · intro h0
        have he := congrArg (eval (![0, 1, 1, 1, 1] : Fin 5 → ℂ)) h0
        simp [pt, G, H] at he
      · intro l hl
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl | rfl | rfl <;> exact isHomogeneous_X ℂ _
      · simp [pt, G, H]; ring
    · -- i = 2: G - H = (X 0 - X 1) * X 2 * X 3 * X 4
      refine ⟨?_, 1, [X 0 - X 1, X 2, X 3, X 4], ?_, ?_⟩
      · intro h0
        have he := congrArg (eval (![1, 0, 1, 1, 1] : Fin 5 → ℂ)) h0
        simp [pt, G, H] at he
      · intro l hl
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl | rfl | rfl
        · exact (isHomogeneous_X ℂ (0 : Fin 5)).sub (isHomogeneous_X ℂ (1 : Fin 5))
        · exact isHomogeneous_X ℂ _
        · exact isHomogeneous_X ℂ _
        · exact isHomogeneous_X ℂ _
      · simp [pt, G, H]; ring

end OMA.S_mo_5041_Proof

theorem OMA.solution : type_of% @OMA.S_mo_5041.main :=
  OMA.S_mo_5041_Proof.main_proof
