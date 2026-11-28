import OMAStatements.S_mo_132242

/-!
Retains @connoranderson's complete signed proof #27448, head
8b52b00791a8059b39aba356aaf41d453071ce6f, linked by statement #23212.
Uses an independent spanning row set directly and the standard nonsingular
matrix kernel lemma. The cofactor, projector and degenerate-node constructions remain unchanged.
Source: trion, MathOverflow 132242 (CC BY-SA 3.0).
-/

namespace OMA.S_mo_132242

open Matrix

lemma cof_mulVec {d : ℕ} (A : Matrix (Fin d) (Fin (d+1)) ℝ) : A *ᵥ cof A = 0 := by
  classical
  funext i
  let B : Matrix (Fin (d+1)) (Fin (d+1)) ℝ := Matrix.of (Fin.cases (A i) (fun k => A k))
  have hz : B.det=0 := Matrix.det_zero_of_row_eq (Fin.succ_ne_zero i).symm rfl
  have he := Matrix.det_succ_row_zero B
  rw [hz] at he
  change ∑ j, A i j * cof A j = 0
  simpa [cof, B, Matrix.submatrix, mul_comm, mul_left_comm, mul_assoc] using he.symm

lemma cof_spans {d : ℕ} (A : Matrix (Fin d) (Fin (d+1)) ℝ) (h : cof A ≠ 0) :
    ∀ v, A *ᵥ v = 0 ↔ ∃ c : ℝ, v=c • cof A := by
  classical
  obtain ⟨j,hj⟩ : ∃ j, cof A j ≠ 0 := by simpa [funext_iff] using h
  let D := A.submatrix id j.succAbove
  have hD : D.det ≠ 0 := fun he => hj (by change _*D.det = 0; rw [he,mul_zero])
  intro v
  constructor
  · intro hv
    let c := v j/cof A j
    let w := v - c • cof A
    have hw : A *ᵥ w = 0 := by simp [w,mulVec_sub,mulVec_smul,hv,cof_mulVec]
    have hwj : w j=0 := by simp [w,c,div_mul_cancel₀ _ hj]
    have hker : D *ᵥ (w ∘ j.succAbove) = 0 := by
      funext i
      have he := congrFun hw i
      change ∑ k, A i k*w k = 0 at he
      rw [Fin.sum_univ_succAbove _ j,hwj,mul_zero,zero_add] at he
      exact he
    have hw' : w ∘ j.succAbove = 0 :=
      Matrix.eq_zero_of_mulVec_eq_zero hD hker
    refine ⟨c,sub_eq_zero.mp ?_⟩
    funext i
    have he : ∀ t, w t=0 := (Fin.forall_iff_succAbove j).mpr ⟨hwj,fun k => congrFun hw' k⟩
    exact he i
  · rintro ⟨c,rfl⟩
    simp [mulVec_smul,cof_mulVec]

end OMA.S_mo_132242

namespace OMA.S_mo_132242
open Matrix

lemma kernel_formula {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (A : Matrix ι κ ℝ) : ∃ (s : Finset ι),
    let B := A.submatrix (fun i : s => (i:ι)) id
    ∀ v : κ → ℝ, A *ᵥ v = 0 ↔ ∃ w : κ → ℝ, v = (1 - B.transpose * (B * B.transpose)⁻¹ * B) *ᵥ w := by
  classical
  obtain ⟨I,_,_,hspan,hI⟩ := exists_linearIndepOn_extension
    (linearIndepOn_empty ℝ A.row) (Set.empty_subset Set.univ)
  let s := I.toFinset
  let B := A.submatrix (fun i : s => (i:ι)) id
  have hBe : LinearIndependent ℝ B.row := by
    change LinearIndepOn ℝ A.row (s:Set ι)
    simpa only [s,Set.coe_toFinset] using hI
  have detU : IsUnit (B*B.transpose).det := by
    apply (Matrix.isUnit_iff_isUnit_det _).mp
    apply Matrix.linearIndependent_rows_iff_isUnit.mp
    apply linearIndependent_iff_card_eq_finrank_span.mpr
    rw [Set.finrank, ← Matrix.rank_eq_finrank_span_row,Matrix.rank_self_mul_transpose]
    exact hBe.rank_matrix.symm
  have hker (v : κ → ℝ) : A *ᵥ v = 0 ↔ B *ᵥ v = 0 := by
    constructor
    · intro h
      funext i
      exact congrFun h i.val
    · intro h
      let T : (κ→ℝ) →ₗ[ℝ] ℝ := (dotProductBilin ℝ ℝ).flip v
      have hsub : Submodule.span ℝ (A.row '' I) ≤ LinearMap.ker T := by
        apply Submodule.span_le.mpr
        rintro _ ⟨i,hi,rfl⟩
        exact congrFun h ⟨i,by simpa [s] using hi⟩
      funext i
      exact hsub (hspan ⟨i, Set.mem_univ i, rfl⟩)
  refine ⟨s,?_⟩
  change ∀ v : κ→ℝ, A *ᵥ v=0 ↔ ∃ w, v=(1-B.transpose*(B*B.transpose)⁻¹*B) *ᵥ w
  intro v
  rw [hker]
  constructor
  · intro hv
    refine ⟨v,?_⟩
    simp [Matrix.sub_mulVec,←Matrix.mulVec_mulVec,hv]
  · rintro ⟨w,rfl⟩
    rw [Matrix.sub_mulVec,Matrix.one_mulVec,Matrix.mulVec_sub,Matrix.mulVec_mulVec]
    have he : B*(B.transpose*(B*B.transpose)⁻¹*B) =B := by
      rw [←Matrix.mul_assoc,←Matrix.mul_assoc,Matrix.mul_nonsing_inv _ detU,Matrix.one_mul]
    rw [he,sub_self]

end OMA.S_mo_132242

namespace OMA.S_mo_132242

lemma degenerate (m : ℕ) : (vand m (fun j => (j.val:ℝ)) (fun _ => 0)).rank ≤ m := by
  classical
  let A : Matrix (Fin m × Fin m) (Fin m) ℝ :=
    fun ab k => if k=ab.1 then (0:ℝ)^ab.2.val else 0
  let B : Matrix (Fin m) (Fin (m*m+1)) ℝ := fun k j => (j.val:ℝ)^k.val
  have h : vand m (fun j => (j.val:ℝ)) (fun _ => 0)=A*B := by
    ext ab j
    rw [Matrix.mul_apply]
    simp [vand,A,B,mul_comm]
  rw [h]
  exact (Matrix.rank_mul_le_left A B).trans (by simpa using A.rank_le_card_width)

end OMA.S_mo_132242

open OMA.S_mo_132242

theorem OMA.solution : type_of% @OMA.S_mo_132242.main := by
  classical
  constructor
  · intro m x y _
    exact ⟨⟨cof_mulVec _, cof_spans _⟩,kernel_formula _⟩
  · intro m hm
    let x : Fin (m*m+1) → ℝ := fun j => (j.val : ℝ)
    let y : Fin (m*m+1) → ℝ := fun _ => 0
    refine ⟨x,y,?_,?_⟩
    · intro j k h
      apply Fin.ext
      have he : (j.val : ℝ) = (k.val : ℝ) := congrArg Prod.fst h
      exact_mod_cast he
    · have hr := degenerate m
      have hdim := (vand m x y).mulVecLin.finrank_range_add_finrank_ker
      rw [← Matrix.rank] at hdim
      simp only [Module.finrank_pi, Fintype.card_fin] at hdim
      change (vand m x y).rank ≤ m at hr
      have hmm := Nat.mul_le_mul_right m hm
      omega
