import OMAStatements.S_mo_263532

namespace OMA.S_mo_263532
open LinearPMap Set
open scoped ENNReal
private lemma graph_kernel (d : Fin 2) (p : H × H) (hp : p∈graphAt d) (h : p.1=0) : p.2=0 := by
  ext i
  have := hp i
  simpa [coord,h] using this
lemma op_coord (d : Fin 2) (x : (op d).domain) (i : I) : (op d x) i = coord d x.val i :=
  (Submodule.mem_graph_toLinearPMap (graph_kernel d) x) i
lemma op_closed (d : Fin 2) : (op d).IsClosed := by
  change IsClosed (↑(graphAt d).toLinearPMap.graph : Set (H×H))
  rw [Submodule.toLinearPMap_graph_eq _ (graph_kernel d)]
  change IsClosed {p : H×H | ∀ i,p.2 i=coord d p.1 i}
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro i
  apply isClosed_eq
  · exact (lp.evalCLM ℂ (fun _ : I => ℂ) 2 i).continuous.comp continuous_snd
  · by_cases hi : i.2=d
    · simp only [coord,if_pos hi]
      exact continuous_const.mul ((lp.evalCLM ℂ (fun _ : I => ℂ) 2 (i.1,0)).continuous.comp continuous_fst)
    · simpa only [coord,if_neg hi] using (continuous_const : Continuous (fun _ : H×H => (0:ℂ)))
private lemma single_dom (d : Fin 2) (i : I) (c : ℂ) : lp.single 2 i c ∈ (op d).domain := by
  let y : H := if i.2=0 then lp.single 2 (i.1,d) (((i.1:ℂ)+1)*c) else 0
  refine ⟨(lp.single 2 i c,y),?_,rfl⟩
  intro j
  change y j=coord d (lp.single 2 i c) j
  rcases i with ⟨n,b⟩
  rcases j with ⟨m,e⟩
  by_cases he : e=d <;> by_cases hn : m=n <;> by_cases hb : b=0 <;>
    simp_all [y,coord,lp.single_apply,Prod.ext_iff]
lemma common_dense : Dense (↑((op 0).domain ⊓ (op 1).domain) : Set H) := by
  intro x
  apply mem_closure_of_tendsto (lp.hasSum_single (by norm_num : (2:ℝ≥0∞)≠⊤) x)
  apply Filter.Eventually.of_forall
  intro S
  exact Submodule.sum_mem _ (fun i _ => ⟨single_dom 0 i _,single_dom 1 i _⟩)
lemma op_dense (d : Fin 2) : Dense ((op d).domain:Set H) := by
  intro x
  apply mem_closure_of_tendsto (lp.hasSum_single (by norm_num : (2:ℝ≥0∞)≠⊤) x)
  exact Filter.Eventually.of_forall fun S => Submodule.sum_mem _ (fun i _ => single_dom d i _)
lemma orthogonal_outputs (x : (op 0).domain) (y : (op 1).domain) :
    inner ℂ (op 0 x) (op 1 y)=0 := by
  rw [lp.inner_eq_tsum]
  trans ∑' _ : I, (0:ℂ)
  · apply tsum_congr
    intro i
    rw [op_coord,op_coord]
    by_cases h : i.2=0
    · simp [coord,h]
    · simp [coord,h]
  · simp
end OMA.S_mo_263532

namespace OMA.S_mo_263532
open LinearPMap Set
open scoped ENNReal
private lemma single_adj_dom (d : Fin 2) (i : I) (c : ℂ) :
    lp.single 2 i c ∈ (op d).adjoint.domain := by
  apply LinearPMap.mem_adjoint_domain_of_exists
  by_cases hi : i.2=d
  · refine ⟨lp.single 2 (i.1,0) (((i.1:ℂ)+1)*c),?_⟩
    intro x
    simp [lp.inner_single_left,RCLike.inner_apply,op_coord,coord,hi,mul_comm,mul_left_comm,mul_assoc]
  · refine ⟨0,?_⟩
    intro x
    simp [lp.inner_single_left,RCLike.inner_apply,op_coord,coord,hi]
lemma adjoint_common_dense : Dense (↑((op 0).adjoint.domain ⊓ (op 1).adjoint.domain) : Set H) := by
  intro x
  apply mem_closure_of_tendsto (lp.hasSum_single (by norm_num : (2:ℝ≥0∞)≠⊤) x)
  exact Filter.Eventually.of_forall fun S => Submodule.sum_mem _ (fun i _ => ⟨single_adj_dom 0 i _,single_adj_dom 1 i _⟩)
end OMA.S_mo_263532

namespace OMA.S_mo_263532
open LinearPMap
open scoped InnerProductSpace

private noncomputable def probe (n : ℕ) : H :=
  lp.single 2 (n,0) (1:ℂ) + lp.single 2 (n,1) (1:ℂ)
private noncomputable def response (n : ℕ) : H :=
  lp.single 2 (n,0) ((n:ℂ)+1)

private lemma probe_finite (n : ℕ) : probe n ∈ finiteSupport := by
  apply (Set.toFinite ({(n,0),(n,1)} : Set I)).subset
  intro i hi
  by_contra hn
  have h0 : i≠(n,0) := fun e => hn (by simp [e])
  have h1 : i≠(n,1) := fun e => hn (by simp [e])
  exact hi (by simp [probe,Pi.single_eq_of_ne h0,Pi.single_eq_of_ne h1])

private lemma adjoint_probe (n : ℕ) (d : Fin 2) :
    ∃ h : probe n ∈ (op d).adjoint.domain,
      (op d).adjoint ⟨probe n,h⟩ = response n := by
  have pair (x : (op d).domain) :
      inner ℂ (response n) (x:H)=inner ℂ (probe n) (op d x) := by
    simp only [response,probe,inner_add_left,lp.inner_single_left,RCLike.inner_apply,op_coord]
    fin_cases d <;> simp [coord,mul_comm]
  have h := LinearPMap.mem_adjoint_domain_of_exists (T:=op d) (probe n) ⟨response n,pair⟩
  exact ⟨h,LinearPMap.adjoint_apply_eq (op_dense d) ⟨_,h⟩ pair⟩

lemma unbounded_adjoint (c : ℝ) :
    ∃ y ∈ finiteSupport, ∃ (h0 : y ∈ (op 0).adjoint.domain) (h1 : y ∈ (op 1).adjoint.domain),
      c*‖y‖^2 < ‖inner ℂ ((op 0).adjoint ⟨y,h0⟩) ((op 1).adjoint ⟨y,h1⟩)‖ := by
  obtain ⟨n,hn⟩ := exists_nat_gt (2*c)
  obtain ⟨h0,e0⟩ := adjoint_probe n 0
  obtain ⟨h1,e1⟩ := adjoint_probe n 1
  refine ⟨probe n,probe_finite n,h0,h1,?_⟩
  have hnorm : ‖probe n‖^2=2 := by
    rw [@norm_sq_eq_re_inner ℂ]
    simp only [probe,inner_add_left,lp.inner_single_left,lp.coeFn_add,Pi.add_apply]
    norm_num [lp.single_apply]
  rw [e0,e1,hnorm,inner_self_eq_norm_sq_to_K]
  have hn' : ‖response n‖=(n:ℝ)+1 := by
    rw [response,lp.norm_single (by norm_num)]
    norm_cast
  rw [Complex.norm_pow]
  rw [RCLike.norm_ofReal,hn',abs_of_nonneg (show 0 ≤ (n:ℝ)+1 by positivity)]
  nlinarith [sq_nonneg (n:ℝ), show 0 ≤ (n:ℝ) by positivity]
end OMA.S_mo_263532

open OMA.S_mo_263532
theorem OMA.solution : type_of% @OMA.S_mo_263532.main :=
  ⟨fun d => ⟨op_closed d,op_dense d⟩,common_dense,adjoint_common_dense,orthogonal_outputs,unbounded_adjoint⟩
