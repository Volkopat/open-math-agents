import OMAStatements.S_mo_485413

/-!
Complete proof by @connoranderson, linked from statement PR #26206 and desk DONE #119988.
Pinned companion: https://github.com/connoranderson/open-math-agents/blob/8b24282236e514e24622950b4bf17fe7ac74345a/proofs/mo-485413.lean
All mathematical code is retained unchanged. This port adds attribution and current-checker validation.
Source: Yaroslav Bulatov, https://mathoverflow.net/questions/485413 (CC BY-SA 4.0).
Credit Nathaniel Johnston for the deterministic lower inequality in the original discussion.
The registered probabilistic results assume full support or isotropy; this proof does not separately
construct the uniform sphere law or assert almost-sure equality. Port: @rodolfoquint; no new discovery claimed.
-/

namespace OMA.S_mo_485413
open Matrix Finset

private def planeBlock {d t : ℕ} (e : Fin 2 ⊕ Fin t ≃ Fin d) (A : Mat 2) : Mat d :=
  reindex e e (fromBlocks A 0 0 (1:Mat t))

private lemma planeBlock_mul {d t : ℕ} (e : Fin 2 ⊕ Fin t ≃ Fin d) (A B : Mat 2) :
    planeBlock e A * planeBlock e B = planeBlock e (A*B) := by
  change reindexAlgEquiv ℝ ℝ e _ * reindexAlgEquiv ℝ ℝ e _ = reindexAlgEquiv ℝ ℝ e _
  rw [←map_mul,fromBlocks_multiply]; simp

private lemma planeBlock_pow {d t : ℕ} (e : Fin 2 ⊕ Fin t ≃ Fin d) (A : Mat 2) (k : ℕ) :
    (planeBlock e A)^k = planeBlock e (A^k) := by
  induction k with
  | zero => simp [planeBlock]
  | succ k ih => rw [pow_succ,ih,planeBlock_mul,pow_succ]

private lemma block_gap {d t : ℕ} (e : Fin 2 ⊕ Fin t ≃ Fin d) (A : Mat 2) :
    froSq (planeBlock e A) - (planeBlock e A).trace = froSq A - A.trace := by
  have he (f : Fin d → ℝ) : (∑ i, f i) = ∑ i, f (e i) := (e.sum_comp f).symm
  unfold froSq Matrix.trace
  rw [he,he (fun i => (planeBlock e A).diag i)]
  simp_rw [he (fun j => (planeBlock e A) (e _) j ^2)]
  simp [planeBlock,Fintype.sum_sum_type,Matrix.reindex_apply, Matrix.diag, Matrix.one_apply]

private noncomputable def dir {d t : ℕ} (e : Fin 2 ⊕ Fin t ≃ Fin d)
    (v : Fin 2 → ℝ) (hv : ∑ i,v i ^ 2 = 1) : Sphere d := by
  let x : E d := WithLp.toLp 2 (fun i => Sum.elim v (fun _ => 0) (e.symm i))
  refine ⟨x,?_⟩
  change dist x 0 = 1
  rw [dist_zero_right]
  have hx : ‖x‖^2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq, ←e.sum_comp (fun i => (x i)^2)]
    simpa [x,Fintype.sum_sum_type] using hv
  nlinarith [norm_nonneg x]

private lemma dir_proj {d t : ℕ} (e : Fin 2 ⊕ Fin t ≃ Fin d)
    (v : Fin 2 → ℝ) (hv : ∑ i,v i ^ 2 = 1) :
    proj (dir e v hv) = planeBlock e (1 - vecMulVec v v) := by
  ext i j
  obtain ⟨i,rfl⟩ := e.surjective i
  obtain ⟨j,rfl⟩ := e.surjective j
  cases i <;> cases j <;> simp [proj,dir,planeBlock,Matrix.reindex_apply, Matrix.one_apply,
    Matrix.vecMulVec_apply]

lemma bad_walk (d : ℕ) (hd : 3≤d) (s : ℕ) (hs : Odd s) :
    ∃ w : Fin d → Sphere d, ((walk w)^s).trace < froSq ((walk w)^s) := by
  obtain ⟨m,rfl⟩ : ∃ m, d=m+3 := ⟨d-3,by omega⟩
  let e : Fin 2 ⊕ Fin (m+1) ≃ Fin (m+3) := Fintype.equivOfCardEq (by simp; omega)
  let a : Fin 2 → ℝ := ![0,1]
  let b : Fin 2 → ℝ := ![-4/5,3/5]
  let c : Fin 2 → ℝ := ![-4/5,-3/5]
  have ha : ∑ i,a i^2=1 := by norm_num [a,Fin.sum_univ_succ]
  have hb : ∑ i,b i^2=1 := by norm_num [b,Fin.sum_univ_succ]
  have hc : ∑ i,c i^2=1 := by norm_num [c,Fin.sum_univ_succ]
  let w : Fin (m+3) → Sphere (m+3) :=
    Fin.cases (dir e a ha) (Fin.cases (dir e b hb) (fun _ => dir e c hc))
  let A : Mat 2 := 1-vecMulVec a a
  let B : Mat 2 := 1-vecMulVec b b
  let C : Mat 2 := 1-vecMulVec c c
  have hC : C*C=C := by
    ext i j; fin_cases i <;> fin_cases j <;> norm_num [C,c,Matrix.mul_apply,Matrix.one_apply,Fin.sum_univ_succ,Fin.succ_zero_eq_one]
  have hcp (k : ℕ) : C^(k+1)=C := by
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ,ih,hC]
  have hw : walk w = planeBlock e (A*B*C) := by
    unfold walk
    rw [List.ofFn_succ,List.ofFn_succ]
    simp only [w,List.prod_cons,Fin.cases_zero,Fin.cases_succ]
    rw [List.ofFn_const,List.prod_replicate]
    simp only [dir_proj,planeBlock_pow,planeBlock_mul,Matrix.mul_assoc]
    change planeBlock e (A*(B*C^(m+1))) = _
    rw [hcp]
  let l : ℝ := -63/625
  let T : Mat 2 := !![l,84/625; 0,0]
  have hT : A*B*C=T := by
    ext i j; fin_cases i <;> fin_cases j <;> norm_num [A,B,C,T,a,b,c,l,Matrix.mul_apply,Matrix.one_apply,Fin.sum_univ_succ,Fin.succ_zero_eq_one]
  have hp (k : ℕ) : T^(k+1) = l^k • T := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ,ih,Matrix.smul_mul,pow_succ,mul_smul]
      congr 1
      ext i j; fin_cases i <;> fin_cases j <;> norm_num [T,l,Matrix.mul_apply,Fin.sum_univ_succ]
  obtain ⟨k,rfl⟩ := hs
  have hneg : (T^(2*k+1)).trace < 0 := by
    rw [hp,Matrix.trace_smul]
    have ht : T.trace=l := by simp [T,Matrix.trace,Fin.sum_univ_succ]
    rw [ht,smul_eq_mul,pow_mul]
    exact mul_neg_of_pos_of_neg (pow_pos (by norm_num [l]) _) (by norm_num [l])
  refine ⟨w,?_⟩
  rw [hw,hT,planeBlock_pow]
  have hg := block_gap e (T^(2*k+1))
  have hnn : 0 ≤ froSq (T^(2*k+1)) := sum_nonneg fun i _ => sum_nonneg fun j _ => sq_nonneg _
  linarith

end OMA.S_mo_485413

namespace OMA.S_mo_485413
open Matrix Finset MeasureTheory

private lemma coordinate_cont {d : ℕ} (i : Fin d) : Continuous (fun v : Sphere d => v.val i) :=
  (PiLp.continuous_apply 2 _ i).comp continuous_subtype_val

private lemma projection_cont {d : ℕ} : Continuous (@proj d) := by
  apply continuous_matrix
  intro i j
  exact continuous_const.sub ((coordinate_cont i).mul (coordinate_cont j))

private lemma walk_cons {d k : ℕ} (v : Sphere d) (w : Fin k → Sphere d) :
    walk (Fin.cons v w) = proj v * walk w := by
  simp [walk,List.ofFn_succ]

private lemma walk_continuous {d : ℕ} (k : ℕ) : Continuous (@walk d k) := by
  induction k with
  | zero =>
    have h : (@walk d 0) = fun _ => 1 := by funext w; simp [walk]
    rw [h]; exact continuous_const
  | succ k ih =>
    have h (w : Fin (k+1) → Sphere d) : walk w = proj (w 0) * walk (fun i => w i.succ) := by
      simp [walk,List.ofFn_succ]
    simp_rw [funext h]
    exact (projection_cont.comp (continuous_apply 0)).matrix_mul
      (ih.comp (continuous_pi fun i => continuous_apply i.succ))

private lemma proj_symm {d : ℕ} (v : Sphere d) : (proj v)ᵀ = proj v := by
  ext i j
  simp [proj,Matrix.transpose_apply,Matrix.one_apply,vecMulVec_apply,eq_comm,mul_comm]

private lemma proj_idemp {d : ℕ} (v : Sphere d) : proj v * proj v = proj v := by
  have hn : ‖v.val‖ = 1 := mem_sphere_zero_iff_norm.mp v.property
  have hs := EuclideanSpace.real_norm_sq_eq v.val
  have h : (fun i => v.val i) ⬝ᵥ (fun i => v.val i) = 1 := by
    simpa [dotProduct,sq,hn] using hs.symm
  simp only [proj,sub_mul,mul_sub,one_mul,mul_one,vecMulVec_mul_vecMulVec,h,one_smul]
  abel

private lemma fro_trace_eq {d : ℕ} (A : Mat d) : froSq A = (A*Aᵀ).trace := by
  simp [froSq,Matrix.trace,Matrix.diag,Matrix.mul_apply,sq]

private lemma proj_fro_trace {d : ℕ} (v : Sphere d) (A : Mat d) :
    froSq (proj v * A) = (proj v * (A*Aᵀ)).trace := by
  rw [fro_trace_eq,transpose_mul,proj_symm]
  calc _ = (proj v*(A*Aᵀ)*proj v).trace := by simp only [mul_assoc]
    _ = _ := by rw [trace_mul_cycle,proj_idemp]

private lemma mean_trace {d : ℕ} (μ : Measure (Sphere d)) [IsProbabilityMeasure μ] (hμ : iso μ)
    (A : Mat d) : (∫ v : Sphere d, (proj v*A).trace ∂μ) = (1-1/(d:ℝ))*A.trace := by
  let F (i j : Fin d) (v : Sphere d) := v.val i * v.val j * A j i
  have hi (i j : Fin d) : Integrable (F i j) μ :=
    (((coordinate_cont i).mul (coordinate_cont j)).mul continuous_const).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hsum : Integrable (fun v => ∑ i,∑ j,F i j v) μ :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hi i j
  have h (v : Sphere d) : (proj v*A).trace = A.trace - ∑ i,∑ j,F i j v := by
    rw [proj,sub_mul,one_mul,Matrix.trace_sub]
    rfl
  simp_rw [h]
  rw [integral_sub (integrable_const _) hsum,integral_const,probReal_univ,one_smul,
      integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hi i j)]
  simp_rw [integral_finsetSum _ (fun j _ => hi _ j)]
  have hF (i j : Fin d) : (∫ v,F i j v ∂μ) = (if i=j then 1/(d:ℝ) else 0)*A j i := by
    dsimp only [F]
    rw [integral_mul_const,hμ i j]
  simp_rw [hF]
  have hrow (i : Fin d) : ∑ j, (if i=j then 1/(d:ℝ) else 0)*A j i = (1/(d:ℝ))*A i i := by
    simp [ite_mul]
  simp_rw [hrow]
  rw [← mul_sum]
  change A.trace - 1/(d:ℝ)*A.trace = _
  ring

private lemma product_iterate {d : ℕ} (μ : Measure (Sphere d)) [IsProbabilityMeasure μ]
    (F : Mat d → ℝ) (hF : Continuous F) (c : ℝ)
    (hstep : ∀ A, (∫ v : Sphere d, F (proj v*A) ∂μ) = c*F A) (k : ℕ) :
    (∫ w : Fin k → Sphere d, F (walk w) ∂Measure.pi (fun _ => μ)) = F 1*c^k := by
  induction k with
  | zero => simp [walk]
  | succ k ih =>
    let ν := Measure.pi (fun _ : Fin k => μ)
    let T (p : Sphere d × (Fin k → Sphere d)) := F (proj p.1 * walk p.2)
    have hT : Continuous T := hF.comp ((projection_cont.comp continuous_fst).matrix_mul
      ((walk_continuous k).comp continuous_snd))
    have hInt : Integrable T (μ.prod ν) :=
      hT.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace T)
    calc (∫ w : Fin (k+1) → Sphere d, F (walk w) ∂Measure.pi (fun _ => μ)) = ∫ p, T p ∂μ.prod ν := by
           rw [←((measurePreserving_piFinSuccAbove (fun _ : Fin (k+1) => μ) 0).symm).integral_comp']
           apply integral_congr_ae
           filter_upwards with p
           rw [MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv_zero]
           change F (walk (Fin.cons p.1 p.2)) = T p
           exact congrArg F (walk_cons p.1 p.2)
      _ = ∫ w, c * F (walk w) ∂ν := by rw [integral_prod_symm T hInt];simp only [T,hstep]
      _ = _ := by rw [integral_const_mul,show (∫ w,F (walk w) ∂ν) = _ from ih,pow_succ];ring

lemma moments {d : ℕ} (_hd : 0 < d) (μ : Measure (Sphere d)) [IsProbabilityMeasure μ]
    (hμ : iso μ) (k : ℕ) :
    (∫ w : Fin k → Sphere d, (walk w).trace ∂Measure.pi (fun _ => μ)) = (d:ℝ)*(1-1/(d:ℝ))^k ∧
    (∫ w : Fin k → Sphere d, froSq (walk w) ∂Measure.pi (fun _ => μ)) = (d:ℝ)*(1-1/(d:ℝ))^k := by
  have ht : Continuous (fun A : Mat d => A.trace) := continuous_finsetSum _ fun i _ =>
    (continuous_apply i).comp (continuous_apply i)
  have hf : Continuous (@froSq d) := continuous_finsetSum _ fun i _ =>
    continuous_finsetSum _ fun j _ => ((continuous_apply j).comp (continuous_apply i)).pow 2
  constructor
  · simpa using product_iterate μ _ ht _ (mean_trace μ hμ) k
  · have h (A : Mat d) : (∫ v : Sphere d,froSq (proj v*A) ∂μ) = (1-1/(d:ℝ))*froSq A := by
      simp_rw [proj_fro_trace]
      rw [mean_trace μ hμ,←fro_trace_eq]
    simpa [fro_trace_eq] using product_iterate μ _ hf _ h k

end OMA.S_mo_485413

namespace OMA.S_mo_485413
open MeasureTheory Finset

lemma iso_of_orthInvariant {d : ℕ} (hd : 0 < d) (μ : Measure (Sphere d))
    [IsProbabilityMeasure μ] (hμ : orthInvariant μ) : iso μ := by
  classical
  have cont (i j : Fin d) : Continuous (fun v : Sphere d => v.val i * v.val j) :=
    ((PiLp.continuous_apply 2 _ i).comp continuous_subtype_val).mul
      ((PiLp.continuous_apply 2 _ j).comp continuous_subtype_val)
  have inv (U : E d ≃ₗᵢ[ℝ] E d) (i j : Fin d) :
      (∫ v : Sphere d, (U v.val) i * (U v.val) j ∂μ) =
        ∫ v : Sphere d, v.val i * v.val j ∂μ := by
    have h := integral_map (hμ U).measurable.aemeasurable
      ((cont i j).aestronglyMeasurable (μ := Measure.map (sphereAction U) μ))
    rw [(hμ U).map_eq] at h
    exact h.symm
  have diag (i j : Fin d) : (∫ v : Sphere d, v.val j * v.val j ∂μ) =
      ∫ v : Sphere d, v.val i * v.val i ∂μ := by
    have h := inv (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap i j)) i i
    change (∫ v : Sphere d, v.val ((Equiv.swap i j).symm i) *
      v.val ((Equiv.swap i j).symm i) ∂μ) = _ at h
    simpa using h
  intro i j
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl]
    have hs (v : Sphere d) : ∑ k, v.val k * v.val k = 1 := by
      have h : ‖v.val‖ = 1 := by simp
      simp [← sq, ← EuclideanSpace.real_norm_sq_eq, h]
    have hsum := calc
      (d : ℝ) * (∫ v : Sphere d, v.val i * v.val i ∂μ)
          = ∑ _ : Fin d, ∫ v : Sphere d, v.val i * v.val i ∂μ := by simp
      _ = ∑ k : Fin d, ∫ v : Sphere d, v.val k * v.val k ∂μ :=
        Finset.sum_congr rfl fun k _ => (diag i k).symm
      _ = ∫ v : Sphere d, ∑ k : Fin d, v.val k * v.val k ∂μ := by
        rw [integral_finsetSum]
        intro k _
        exact (cont k k).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      _ = 1 := by simp_rw [hs]; simp
    apply (eq_div_iff (by exact_mod_cast hd.ne' : (d : ℝ) ≠ 0)).2
    rwa [mul_comm]
  · rw [if_neg hij]
    let φ (k : Fin d) : ℝ ≃ₗᵢ[ℝ] ℝ :=
      if k = i then LinearIsometryEquiv.neg ℝ else LinearIsometryEquiv.refl ℝ ℝ
    have h := inv (LinearIsometryEquiv.piLpCongrRight 2 φ) i j
    change (∫ v : Sphere d, φ i (v.val i) * φ j (v.val j) ∂μ) = _ at h
    simp [φ, Ne.symm hij, integral_neg] at h
    linarith

end OMA.S_mo_485413

namespace OMA.S_mo_485413
open Matrix Finset MeasureTheory
private lemma trace_bound {d : ℕ} (M : Mat d) (s : ℕ) :
    (M^(2*s)).trace ≤ froSq (M^s) := by
  rw [two_mul, pow_add]
  let N := M^s
  change (∑ i, ∑ j, N i j * N j i) ≤ ∑ i, ∑ j, (N i j)^2
  have hh : ∀ i j, 2*(N i j * N j i) ≤ (N i j)^2+(N j i)^2 := by
    intro i j
    nlinarith [sq_nonneg (N i j - N j i)]
  have ht := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin d))) (fun i _ =>
    Finset.sum_le_sum (s := (Finset.univ : Finset (Fin d))) (fun j _ => hh i j))
  simp_rw [← Finset.mul_sum, Finset.sum_add_distrib] at ht
  have he : (∑ i, ∑ j, (N j i)^2) = ∑ i, ∑ j, (N i j)^2 := Finset.sum_comm
  linarith
private lemma positive_bad (d : ℕ) (hd : 3≤d) (s : ℕ) (hs : Odd s)
    (μ : Measure (Sphere d)) [IsProbabilityMeasure μ] [μ.IsOpenPosMeasure] :
    0 < (Measure.pi (fun _ : Fin d => μ))
      {w : Fin d → Sphere d | ((walk w)^s).trace < froSq ((walk w)^s)} := by
  have hw := walk_continuous (d:=d) d
  have ht : Continuous (fun w : Fin d → Sphere d => ((walk w)^s).trace) := by
    unfold Matrix.trace Matrix.diag
    fun_prop
  have hf : Continuous (fun w : Fin d → Sphere d => froSq ((walk w)^s)) := by
    unfold froSq
    fun_prop
  let : (Measure.pi (fun _ : Fin d => μ)).IsOpenPosMeasure :=
    Measure.pi.isOpenPosMeasure (fun _ : Fin d => μ)
  exact (isOpen_lt ht hf).measure_pos _ (bad_walk d hd s hs)
end OMA.S_mo_485413

open OMA.S_mo_485413
theorem OMA.solution : type_of% @OMA.S_mo_485413.main := by
  exact ⟨fun _ => trace_bound, positive_bad, fun _ hd => moments hd,
    fun _ hd => iso_of_orthInvariant hd⟩

