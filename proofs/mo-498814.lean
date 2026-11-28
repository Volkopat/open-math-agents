import OMAStatements.S_mo_498814

/-!
Complete proof by @connoranderson, linked from statement PR #25619 and desk DONE #117242.
Pinned companion: https://github.com/connoranderson/open-math-agents/blob/9df485ae315311be9a69f2e613f707072772dec4/proofs/mo-498814.lean
All mathematical code retained unchanged; this port adds attribution and current-checker validation.
Source: Roy, https://mathoverflow.net/questions/498814 (CC BY-SA 4.0).
The optimal constant is for the principal positive covariance square root: squared constant 2,
or norm constant sqrt(2). No optimality over arbitrary square-root selections is asserted.
Port and validation: @rodolfoquint.
-/

namespace OMA.S_mo_498814

open Matrix
open scoped MatrixOrder

private lemma froSq_as_trace {d : Type*} [Fintype d] (A : Matrix d d ℝ) (hA : A.IsHermitian) :
    froSq A = (A*A).trace := by
  calc froSq A = (A*Aᴴ).trace := by
         simp [froSq, Matrix.trace, Matrix.diag, Matrix.mul_apply, sq]
    _ = _ := by rw [hA.eq]

private lemma trace_product_nonneg {d : Type*} [Fintype d] [DecidableEq d]
    {A B : Matrix d d ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) : 0 ≤ (A*B).trace := by
  obtain ⟨C,rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA
  rw [star_eq_conjTranspose, trace_mul_cycle, trace_mul_cycle]
  exact (hB.posSemidef.mul_mul_conjTranspose_same C).trace_nonneg

private lemma trace_abs_product {d : Type*} [Fintype d] [DecidableEq d]
    (A B : Matrix d d ℝ) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (A*B).trace ≤ (CFC.abs A*CFC.abs B).trace := by
  calc (A*B).trace = ((A⁺-A⁻)*(B⁺-B⁻)).trace := by
         rw [CFC.posPart_sub_negPart A hA,CFC.posPart_sub_negPart B hB]
    _ ≤ ((A⁺+A⁻)*(B⁺+B⁻)).trace := by
      simp only [sub_mul, mul_sub, add_mul, mul_add, trace_add, trace_sub]
      linarith [trace_product_nonneg (CFC.posPart_nonneg A) (CFC.negPart_nonneg B),
        trace_product_nonneg (CFC.negPart_nonneg A) (CFC.posPart_nonneg B)]
    _ = _ := by rw [CFC.posPart_add_negPart A hA,CFC.posPart_add_negPart B hB]

lemma abs_lipschitz {d : Type*} [Fintype d] [DecidableEq d] (A B : Matrix d d ℝ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    froSq (CFC.sqrt (A*A) - CFC.sqrt (B*B)) ≤ froSq (A-B) := by
  have aa : CFC.abs A = CFC.sqrt (A*A) := by rw [CFC.abs,show star A = A from hA]
  have bb : CFC.abs B = CFC.sqrt (B*B) := by rw [CFC.abs,show star B = B from hB]
  rw [←aa,←bb, froSq_as_trace _ ((CFC.abs_nonneg A).posSemidef.1.sub (CFC.abs_nonneg B).posSemidef.1),
    froSq_as_trace _ (hA.sub hB)]
  simp only [sub_mul,mul_sub,trace_sub,CFC.abs_mul_abs,show star A = A from hA,show star B = B from hB]
  linarith [trace_abs_product A B hA hB,trace_abs_product B A hB hA]

end OMA.S_mo_498814

namespace OMA.S_mo_498814
open Matrix Finset
open scoped MatrixOrder Matrix.Norms.L2Operator

private lemma fro_zero {m n : Type*} [Fintype m] [Fintype n] : froSq (0 : Matrix m n ℝ)=0 := by
  simp [froSq]

private lemma block_pos {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    {P : Matrix m m ℝ} {Q : Matrix n n ℝ} (hP : 0≤P) (hQ : 0≤Q) :
    0 ≤ fromBlocks P 0 0 Q := by
  apply Matrix.PosSemidef.nonneg
  rw [posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_,fun x => ?_⟩
  · exact hP.posSemidef.1.fromBlocks (by simp) hQ.posSemidef.1
  · rw [fromBlocks_mulVec]
    simp only [zero_mulVec,add_zero,zero_add,dotProduct,Fintype.sum_sum_type]
    exact add_nonneg (hP.posSemidef.dotProduct_mulVec_nonneg (x ∘ Sum.inl))
      (hQ.posSemidef.dotProduct_mulVec_nonneg (x ∘ Sum.inr))

private def dil {m n : Type*} (A : Matrix m n ℝ) : Matrix (m ⊕ n) (m ⊕ n) ℝ :=
  fromBlocks 0 A Aᵀ 0

private lemma dil_herm {m n : Type*} (A : Matrix m n ℝ) : (dil A).IsHermitian := by
  exact Matrix.IsHermitian.fromBlocks (by simp) (by simp) (by simp)

private lemma dil_root {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℝ) : CFC.sqrt (dil A * dil A) =
      fromBlocks (CFC.sqrt (A*Aᵀ)) 0 0 (CFC.sqrt (Aᵀ*A)) := by
  apply CFC.sqrt_unique
  swap
  · exact block_pos (P:=CFC.sqrt (A*Aᵀ)) (Q:=CFC.sqrt (Aᵀ*A))
      (CFC.sqrt_nonneg _) (CFC.sqrt_nonneg _)
  have h1 : 0 ≤ A*Aᵀ := (posSemidef_self_mul_conjTranspose A).nonneg
  have h2 : 0 ≤ Aᵀ*A := (posSemidef_conjTranspose_mul_self A).nonneg
  simp [dil,fromBlocks_multiply,CFC.sqrt_mul_sqrt_self _ h1,CFC.sqrt_mul_sqrt_self _ h2]

private lemma block_dist {m n : Type*} [Fintype m] [Fintype n]
    (A A' : Matrix m m ℝ) (B B' : Matrix m n ℝ) (C C' : Matrix n m ℝ) (D D' : Matrix n n ℝ) :
    froSq (fromBlocks A B C D - fromBlocks A' B' C' D') =
      froSq (A-A')+froSq (B-B')+froSq (C-C')+froSq (D-D') := by
  simp only [froSq,Matrix.sub_apply,Fintype.sum_sum_type,fromBlocks_apply₁₁,
    fromBlocks_apply₁₂,fromBlocks_apply₂₁,fromBlocks_apply₂₂,sum_add_distrib]
  ring

lemma rect_bound {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A B : Matrix m n ℝ) : froSq (CFC.sqrt (A*Aᵀ)-CFC.sqrt (B*Bᵀ)) ≤ 2*froSq (A-B) := by
  have h := abs_lipschitz (dil A) (dil B) (dil_herm A) (dil_herm B)
  rw [dil_root,dil_root] at h
  simp only [dil,block_dist,sub_self] at h
  simp only [fro_zero,add_zero,zero_add] at h
  have ht : froSq (Aᵀ-Bᵀ)=froSq (A-B) := by
    unfold froSq
    rw [sum_comm]
    rfl
  have hpos (M : Matrix n n ℝ) : 0≤froSq M := by unfold froSq; positivity
  linarith [hpos (CFC.sqrt (Aᵀ*A)-CFC.sqrt (Bᵀ*B))]

end OMA.S_mo_498814

namespace OMA.S_mo_498814
open Matrix Finset
open scoped InnerProductSpace MatrixOrder Matrix.Norms.L2Operator

lemma covariance_bound {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (X Y : Fin n → H) : froSq (stdRoot X-stdRoot Y) ≤ 2 * ∑ i, ‖X i-Y i‖^2 := by
  let Z : Fin n ⊕ Fin n → H := Sum.elim X Y
  let T := CFC.sqrt (Matrix.gram ℝ Z)
  have hTpos : 0≤T := CFC.sqrt_nonneg _
  have hT : Tᵀ=T := hTpos.posSemidef.1.eq
  have hG : T*Tᵀ = Matrix.gram ℝ Z := by
    rw [hT]
    exact CFC.sqrt_mul_sqrt_self _ (Matrix.posSemidef_gram ℝ Z).nonneg
  let A : Matrix (Fin n) (Fin n ⊕ Fin n) ℝ := fun i j => T (.inl i) j
  let B : Matrix (Fin n) (Fin n ⊕ Fin n) ℝ := fun i j => T (.inr i) j
  have hdot (a b : Fin n ⊕ Fin n) : ∑ j, T a j * T b j = ⟪Z a,Z b⟫_ℝ := by
    exact congrFun (congrFun hG a) b
  have hA : A*Aᵀ=Matrix.gram ℝ X := by ext i k; exact hdot (.inl i) (.inl k)
  have hB : B*Bᵀ=Matrix.gram ℝ Y := by ext i k; exact hdot (.inr i) (.inr k)
  have hh := rect_bound A B
  rw [hA,hB] at hh
  have he : froSq (A-B) = ∑ i, ‖X i-Y i‖^2 := by
    apply sum_congr rfl
    intro i _
    change ∑ j, (T (.inl i) j - T (.inr i) j)^2 = _
    rw [← real_inner_self_eq_norm_sq,inner_sub_left,inner_sub_right,inner_sub_right]
    have hxx := hdot (.inl i) (.inl i)
    have hxy := hdot (.inl i) (.inr i)
    have hyy := hdot (.inr i) (.inr i)
    simp only [Z,Sum.elim_inl,Sum.elim_inr] at hxx hxy hyy
    have term (j) : (T (.inl i) j - T (.inr i) j)^2 =
        T (.inl i) j*T (.inl i) j - 2*(T (.inl i) j*T (.inr i) j) + T (.inr i) j*T (.inr i) j := by ring
    simp_rw [term]
    rw [sum_add_distrib,sum_sub_distrib,←mul_sum,hxx,hxy,hyy]
    linarith [real_inner_comm (X i) (Y i)]
  simpa only [stdRoot,he] using hh

lemma std_factor {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (X : Fin n → H) : (stdRoot X).PosSemidef ∧ stdRoot X * (stdRoot X)ᵀ = Matrix.gram ℝ X := by
  have h : 0 ≤ stdRoot X := CFC.sqrt_nonneg _
  refine ⟨h.posSemidef,?_⟩
  rw [show (stdRoot X)ᵀ=stdRoot X from h.posSemidef.1.eq]
  exact CFC.sqrt_mul_sqrt_self _ (Matrix.posSemidef_gram ℝ X).nonneg

end OMA.S_mo_498814

namespace OMA.S_mo_498814
open Matrix Finset
open scoped MatrixOrder Matrix.Norms.L2Operator

private lemma root_unit_vector {n : ℕ} (v : Fin n → ℝ) (hv : ∑ i, v i^2 = 1) :
    stdRoot v = gram ℝ v := by
  have h := (Matrix.posSemidef_gram ℝ v).nonneg
  apply (CFC.sqrt_eq_iff _ _ h h).mpr
  ext i j
  simp only [mul_apply,gram_apply,Real.inner_apply]
  calc ∑ k, v i * v k * (v k * v j) = ∑ k, (v i*v j) * v k^2 := by
         apply sum_congr rfl
         intro k _
         ring
    _ = _ := by rw [←mul_sum,hv,mul_one]

lemma optimal (C : ℝ) (hC : C<2) : ∃ X Y : Fin 2 → ℝ,
    C * (∑ i, ‖X i-Y i‖^2) < froSq (stdRoot X-stdRoot Y) := by
  let c := max 0 (C/2)
  let s := Real.sqrt (1-c^2)
  have hc0 : 0≤c := le_max_left _ _
  have hc1 : c<1 := max_lt (by norm_num) (by linarith)
  have hs : s^2 = 1-c^2 := Real.sq_sqrt (by nlinarith [mul_nonneg hc0 (sub_nonneg.mpr hc1.le)])
  let X : Fin 2 → ℝ := ![1,0]
  let Y : Fin 2 → ℝ := ![c,s]
  have hx : ∑ i, X i^2 = 1 := by simp [X,Fin.sum_univ_two]
  have hy : ∑ i, Y i^2 = 1 := by simp [Y,Fin.sum_univ_two,hs]
  refine ⟨X,Y,?_⟩
  rw [root_unit_vector X hx,root_unit_vector Y hy]
  simp [froSq,Fin.sum_univ_two,Real.norm_eq_abs,sq_abs,X,Y]
  have hdiff : C < 1+c := by dsimp [c]; have := le_max_right (0:ℝ) (C/2); linarith
  have hstrict := mul_pos (sub_pos.mpr hdiff) (sub_pos.mpr hc1)
  nlinarith [hs,congrArg (fun t : ℝ => t^2) hs,congrArg (fun t : ℝ => c^2*t) hs]

end OMA.S_mo_498814

open OMA.S_mo_498814

theorem OMA.solution : type_of% @OMA.S_mo_498814.main := by
  refine ⟨?_,optimal⟩
  intro n H _ _ X Y
  exact ⟨(std_factor X).1,(std_factor X).2,covariance_bound X Y⟩
