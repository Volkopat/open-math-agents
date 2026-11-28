import OMAStatements.S_mo_123377

namespace OMA.S_mo_123377
open Matrix Filter MeasureTheory Finset
open scoped Topology
private lemma riemann_left (f : ℝ → ℂ) (hf : Continuous f) :
    Tendsto (fun m : ℕ => (m:ℂ)⁻¹*∑ j ∈ range m, f ((j:ℝ)/m)) atTop (𝓝 (∫ u in (0:ℝ)..1, f u)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ,hδ,hmod⟩ := Metric.uniformContinuousOn_iff.mp
    ((isCompact_Icc (a:=(0:ℝ)) (b:=1)).uniformContinuousOn_of_continuous hf.continuousOn) (ε/2) (half_pos hε)
  obtain ⟨N,hN⟩ := exists_nat_gt (1/δ)
  refine ⟨N,?_⟩
  intro m hm
  have hm' : 1/δ < (m:ℝ) := hN.trans_le (by exact_mod_cast hm)
  have hmp : 0 < (m:ℝ) := lt_trans (by positivity) hm'
  have hmesh : 1/(m:ℝ)<δ := (div_lt_iff₀ hmp).mpr (by linarith [(div_lt_iff₀ hδ).mp hm'])
  let t (j : ℕ) : ℝ := (j:ℝ)/m
  have ht (j : ℕ) : t (j+1)-t j=1/m := by simp [t,add_div]
  have hloc (j : ℕ) (hj : j < m) : ‖∫ u in t j..t (j+1), f (t j)-f u‖ ≤ (ε/2)*(1/m) := by
    have hle : t j ≤ t (j+1) := by have := ht j; linarith [one_div_pos.mpr hmp]
    rw [←ht j,←abs_of_nonneg (sub_nonneg.mpr hle)]
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro u hu
    rw [Set.uIoc_of_le hle] at hu
    have hl : 0 ≤ t j := by dsimp [t]; positivity
    have hr : t (j+1) ≤ 1 := (div_le_one hmp).mpr (by exact_mod_cast hj)
    apply le_of_lt
    rw [←dist_eq_norm]
    apply hmod _ ⟨hl,hle.trans hr⟩ _ ⟨hl.trans hu.1.le,hu.2.trans hr⟩
    rw [Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hu.1.le)]
    linarith [hu.2,ht j]
  have hind (j : ℕ) : (m:ℂ)⁻¹ * f (t j) - ∫ u in t j..t (j+1), f u =
      ∫ u in t j..t (j+1), f (t j)-f u := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const (hf.intervalIntegrable _ _),intervalIntegral.integral_const,ht]
    simp [Complex.real_smul]
  have hall := intervalIntegral.sum_integral_adjacent_intervals (a:=t) (n:=m) (μ:=volume) (f:=f)
    (fun _ _ => hf.intervalIntegrable _ _)
  have hstart : t 0=0 := by simp [t]
  have hend : t m=1 := div_self hmp.ne'
  rw [hstart,hend] at hall
  rw [dist_eq_norm,←hall,mul_sum,←sum_sub_distrib]
  change ‖∑ j ∈ range m, ((m:ℂ)⁻¹*f (t j)-∫ u in t j..t (j+1), f u)‖ < ε
  simp_rw [hind]
  refine (norm_sum_le _ _).trans_lt ?_
  refine (sum_le_sum (fun j hj => hloc j (mem_range.mp hj))).trans_lt ?_
  simp [hmp.ne',mul_comm]
  linarith
end OMA.S_mo_123377

namespace OMA.S_mo_123377
open Matrix Finset Filter MeasureTheory
open scoped Topology
private lemma continuous_node (K : ℝ) : Continuous (node K) := by unfold node; fun_prop
private lemma density (n : ℕ) (K : ℝ) :
    Tendsto (fun m : ℕ => empirical n m K) atTop (𝓝 (continuum n K)) := by
  classical
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  let f (u : ℝ) := node K (2*u-1)^i.val * star (node K (2*u-1)^j.val)
  have hf : Continuous f := by dsimp [f,node]; fun_prop
  have hr := riemann_left f hf
  have hm : Tendsto (fun m : ℕ => ((m:ℝ)+1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have hm' : Tendsto (fun m : ℕ => ((m:ℂ)+1)⁻¹) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (Complex.continuous_ofReal.tendsto 0).comp hm
  have hlim := ((tendsto_const_nhds (x:=(1:ℂ))).sub hm').mul hr
  have hfinal := hlim.add (hm'.mul (tendsto_const_nhds (x:=f 1)))
  change Tendsto (fun m : ℕ => empirical n m K i j) atTop (𝓝 (∫ u in (0:ℝ)..1, f u))
  apply Tendsto.congr' (f₁:=fun m : ℕ => (1-((m:ℂ)+1)⁻¹)*((m:ℂ)⁻¹*∑ k ∈ range m, f ((k:ℝ)/m)) +
    ((m:ℂ)+1)⁻¹*f 1) _ (by simpa only [sub_zero,one_mul,zero_mul,add_zero] using hfinal)
  filter_upwards [eventually_gt_atTop 0] with m hm
  have hmc : (m:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hm1 : (m:ℂ)+1 ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero m)
  have hentry : empirical n m K i j = ((m:ℂ)+1)⁻¹ * ∑ k ∈ range (m+1), f ((k:ℝ)/m) := by
    simp only [empirical,Matrix.smul_apply,smul_eq_mul,Matrix.mul_apply,Matrix.conjTranspose_apply,
      samples,Matrix.of_apply]
    congr 1
    rw [←Fin.sum_univ_eq_sum_range]
    apply sum_congr rfl
    intro k _
    simp [f,grid,mul_div_assoc]
  rw [hentry,sum_range_succ,div_self (Nat.cast_ne_zero.mpr hm.ne')]
  field_simp
  ring
end OMA.S_mo_123377

namespace OMA.S_mo_123377
open Matrix Finset Filter
open scoped Topology ComplexOrder
private noncomputable def scaledNode (K t : ℝ) : ℂ := (node K t-1)/(K:ℂ)
private noncomputable def scaledV (n m : ℕ) (K : ℝ) : Matrix (Fin n) (Fin (m+1)) ℂ :=
  .of fun i j => scaledNode K (grid m j)^i.val
private noncomputable def pascal (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  .of fun i j => (i.val.choose j.val : ℂ)
private noncomputable def scales (n : ℕ) (K : ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  diagonal fun i => (K:ℂ)^i.val

private lemma scaled_tendsto (t : ℝ) :
    Tendsto (fun K => scaledNode K t) (𝓝[≠] 0) (𝓝 ((Real.pi*t:ℝ)*Complex.I)) := by
  have hd : HasDerivAt (fun K => node K t) ((Real.pi*t:ℝ)*Complex.I) 0 := by
    have h := (((((hasDerivAt_id (0:ℝ)).mul_const t).sin.const_mul Real.pi).ofReal_comp).mul_const Complex.I).cexp
    simpa [node] using h
  simpa [scaledNode,node,Complex.real_smul,div_eq_inv_mul] using hd.tendsto_slope_zero

private lemma pascal_det (n : ℕ) : (pascal n).det=1 := by
  rw [det_of_isLowerTriangular]
  · simp [pascal]
  · intro i j hij
    change i.val < j.val at hij
    simp [pascal,Nat.choose_eq_zero_of_lt hij]

private lemma factorize (n m : ℕ) (K : ℝ) (hK : K≠0) :
    samples n m K = pascal n*scales n K*scaledV n m K := by
  ext i j
  let z := node K (grid m j)
  have hz : (K:ℂ)*scaledNode K (grid m j)=z-1 := by
    dsimp [scaledNode,z]; field_simp [Complex.ofReal_ne_zero.mpr hK]
  change z^i.val = _
  conv_lhs => rw [show z=(z-1)+1 by ring,add_pow]
  rw [Matrix.mul_apply]
  simp only [scales,Matrix.mul_diagonal,pascal,scaledV,Matrix.of_apply,one_pow,mul_one]
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => (i.val.choose k:ℂ)*(K:ℂ)^k*scaledNode K (grid m j)^k) n]
  symm
  rw [←sum_subset (show range (i.val+1) ⊆ range n from range_mono i.isLt)]
  · apply sum_congr rfl
    intro k _
    rw [←hz,mul_pow]
    ring
  · intro k hk hki
    have hlt : i.val < k := by simpa using hki
    simp [Nat.choose_eq_zero_of_lt hlt]

private lemma det_factor (n m : ℕ) (K : ℝ) (hK : K≠0) :
    (samples n m K*(samples n m K)ᴴ).det =
      (K:ℂ)^(n*(n-1))*(scaledV n m K*(scaledV n m K)ᴴ).det := by
  let P := pascal n
  let D := scales n K
  let W := scaledV n m K
  have hf : samples n m K=P*D*W := factorize n m K hK
  have hh : P*D*W*(P*D*W)ᴴ=P*(D*(W*Wᴴ)*Dᴴ)*Pᴴ := by
    simp only [conjTranspose_mul,Matrix.mul_assoc]
  have hd : D.det=(K:ℂ)^(∑ j ∈ range n,j) := by
    simp [D,scales,det_diagonal,←Finset.prod_pow_eq_pow_sum,Fin.prod_univ_eq_prod_range]
  rw [hf,hh]
  simp only [det_mul,det_conjTranspose,hd,show P.det=1 from pascal_det n,star_one,one_mul,mul_one,
    star_pow,show star (K:ℂ)=(K:ℂ) from Complex.conj_ofReal K]
  rw [←sum_range_id_mul_two n, pow_mul, pow_two]
  dsimp only [W]
  ring

private lemma tangent_nondegenerate (n m : ℕ) (hm : 0 < m) (hn : n ≤ m+1) :
    0 < ((tangent n m*(tangent n m)ᴴ).det).re := by
  let e := Fin.castLE hn
  let v := fun i : Fin n => (Real.pi*grid m (e i):ℝ)*Complex.I
  have hinj : Function.Injective v := by
    intro i j h
    have h' := congrArg Complex.im h
    simp [v,grid,e] at h'
    apply Fin.ext
    have hm' : (m:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
    have hij : (i.val:ℝ)=j.val := by
      field_simp [hm'] at h'
      nlinarith [Real.pi_pos]
    exact_mod_cast hij
  have hsub : (tangent n m).submatrix id e=(vandermonde v)ᵀ := by ext i j; rfl
  have hu : IsUnit ((tangent n m).submatrix id e).det := by
    rw [hsub,det_transpose,isUnit_iff_ne_zero,det_vandermonde_ne_zero_iff]
    exact hinj
  have hi : Function.Injective (tangent n m)ᴴ.mulVec := by
    intro u w h
    apply Matrix.mulVec_injective_of_isUnit (A:=((tangent n m).submatrix id e)ᴴ)
    · exact (Matrix.isUnit_iff_isUnit_det _).mpr (by rw [det_conjTranspose]; exact hu.star)
    · ext i
      exact congrFun h (e i)
  have hp := (Matrix.PosDef.one (n:=Fin (m+1)) (R:=ℂ)).conjTranspose_mul_mul_same hi
  have hp' : (tangent n m*(tangent n m)ᴴ).PosDef := by simpa using hp
  exact hp'.det_pos.1

private lemma aperture (n m : ℕ) : Tendsto (fun K : ℝ =>
    (samples n m K*(samples n m K)ᴴ).det / (K:ℂ)^(n*(n-1))) (𝓝[≠] 0)
      (𝓝 ((tangent n m*(tangent n m)ᴴ).det)) := by
  have hW : Tendsto (scaledV n m) (𝓝[≠] 0) (𝓝 (tangent n m)) :=
    tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => (scaled_tendsto _).pow i.val
  apply Tendsto.congr' (f₁:=fun K => (scaledV n m K*(scaledV n m K)ᴴ).det) _
    ((show Continuous (fun W : Matrix (Fin n) (Fin (m+1)) ℂ => (W*Wᴴ).det) by fun_prop).continuousAt.tendsto.comp hW)
  filter_upwards [self_mem_nhdsWithin] with K hK
  have hK' : K≠0 := hK
  rw [det_factor n m K hK']
  field_simp [Complex.ofReal_ne_zero.mpr hK']
end OMA.S_mo_123377

/-! Finite-dimensional Courant–Fischer bounds.
Port of Jon Crall's discrete min-max proof from Erotemic/mathlib4,
commit 695af67e71ef73beecc3c15fd3f3546da1adbe9b.
Copyright (c) 2026 Jon Crall. All rights reserved. Used under Apache-2.0.
The upper-direction proof allows larger subspaces. Adapted from the project proof
of OeisA69191.conjecture_2.R1.H2 by Marcus Buffett, and used in the project
proof of MO437602. -/

section
open scoped InnerProductSpace
open Module (finrank)

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {n : ℕ}

private noncomputable def specSubspace (b : OrthonormalBasis (Fin n) 𝕜 E) (p : Fin n → Prop) :
    Submodule 𝕜 E :=
  Submodule.span 𝕜 (Set.range (fun i : {i : Fin n // p i} => b i))

private theorem finrank_specSubspace (b : OrthonormalBasis (Fin n) 𝕜 E) (p : Fin n → Prop)
    [DecidablePred p] :
    finrank 𝕜 (specSubspace b p) = (Finset.univ.filter p).card := by
  rw [specSubspace,
    finrank_span_eq_card (b := fun i : {i : Fin n // p i} => b i)
      (b.orthonormal.linearIndependent.comp _ Subtype.val_injective),
    Fintype.card_subtype]

private theorem repr_eq_zero_of_mem_specSubspace (b : OrthonormalBasis (Fin n) 𝕜 E)
    (p : Fin n → Prop) {x : E} (hx : x ∈ specSubspace b p) {i : Fin n} (hi : ¬ p i) :
    b.repr x i = 0 := by
  rw [b.repr_apply_apply]
  
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · rintro y ⟨j, rfl⟩
    refine b.inner_eq_zero ?_
    rintro rfl
    exact hi j.2
  · rw [inner_zero_right]
  · intro y z _ _ hy hz
    rw [inner_add_right, hy, hz, add_zero]
  · intro a y _ hy
    rw [inner_smul_right, hy, mul_zero]

private theorem sum_sq_norm_repr_eq_sq_norm (b : OrthonormalBasis (Fin n) 𝕜 E) (x : E) :
    ∑ i : Fin n, ‖b.repr x i‖ ^ 2 = ‖x‖ ^ 2 := by
  simp_rw [b.repr_apply_apply]
  exact b.sum_sq_norm_inner_right x

variable [FiniteDimensional 𝕜 E] {T S : E →ₗ[𝕜] E}

namespace LinearMap.IsSymmetric

theorem re_inner_map_self_eq_sum_eigenvalues_mul_sq
    (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n) (x : E) :
    RCLike.re ⟪T x, x⟫_𝕜
      = ∑ i : Fin n, hT.eigenvalues hn i * ‖(hT.eigenvectorBasis hn).repr x i‖ ^ 2 := by
  have key : ⟪T x, x⟫_𝕜
      = ((∑ i : Fin n,
          hT.eigenvalues hn i * ‖(hT.eigenvectorBasis hn).repr x i‖ ^ 2 : ℝ) : 𝕜) := by
    rw [← (hT.eigenvectorBasis hn).repr.inner_map_map (T x) x, PiLp.inner_apply]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [RCLike.inner_apply, hT.eigenvectorBasis_apply_self_apply, map_mul, RCLike.conj_ofReal,
      mul_left_comm, RCLike.mul_conj]
  rw [key, RCLike.ofReal_re]

private theorem re_inner_map_self_le_of_mem_specSubspace
    (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n) {p : Fin n → Prop} {c : ℝ}
    (hc : ∀ i, p i → hT.eigenvalues hn i ≤ c)
    {x : E} (hx : x ∈ specSubspace (hT.eigenvectorBasis hn) p) :
    RCLike.re ⟪T x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2 := by
  set b := hT.eigenvectorBasis hn
  rw [re_inner_map_self_eq_sum_eigenvalues_mul_sq hT hn x,
    show c * ‖x‖ ^ 2 = ∑ i : Fin n, c * ‖b.repr x i‖ ^ 2 by
      rw [← Finset.mul_sum, sum_sq_norm_repr_eq_sq_norm]]
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases hp : p i
  · exact mul_le_mul_of_nonneg_right (hc i hp) (sq_nonneg _)
  · rw [repr_eq_zero_of_mem_specSubspace b p hx hp]; simp

private theorem le_re_inner_map_self_of_mem_specSubspace
    (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n) {p : Fin n → Prop} {c : ℝ}
    (hc : ∀ i, p i → c ≤ hT.eigenvalues hn i)
    {x : E} (hx : x ∈ specSubspace (hT.eigenvectorBasis hn) p) :
    c * ‖x‖ ^ 2 ≤ RCLike.re ⟪T x, x⟫_𝕜 := by
  set b := hT.eigenvectorBasis hn
  rw [re_inner_map_self_eq_sum_eigenvalues_mul_sq hT hn x,
    show c * ‖x‖ ^ 2 = ∑ i : Fin n, c * ‖b.repr x i‖ ^ 2 by
      rw [← Finset.mul_sum, sum_sq_norm_repr_eq_sq_norm]]
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases hp : p i
  · exact mul_le_mul_of_nonneg_right (hc i hp) (sq_nonneg _)
  · rw [repr_eq_zero_of_mem_specSubspace b p hx hp]; simp

private theorem card_filter_le (k : Fin n) :
    (Finset.univ.filter (fun i : Fin n => k ≤ i)).card = n - (k : ℕ) := by
  have : (Finset.univ.filter (fun i : Fin n => k ≤ i)).card
      = (Finset.Ici k).card := by
    congr 1
    ext i
    simp [Finset.mem_Ici]
  rw [this, Fin.card_Ici]

private theorem card_filter_ge (k : Fin n) :
    (Finset.univ.filter (fun i : Fin n => i ≤ k)).card = (k : ℕ) + 1 := by
  have : (Finset.univ.filter (fun i : Fin n => i ≤ k)).card
      = (Finset.Iic k).card := by
    congr 1
    ext i
    simp [Finset.mem_Iic]
  rw [this, Fin.card_Iic]

theorem exists_unit_vector_re_inner_le_eigenvalue
    (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n) (k : Fin n)
    (V : Submodule 𝕜 E) (hV : (k : ℕ) + 1 ≤ finrank 𝕜 V) :
    ∃ x ∈ V, ‖x‖ = 1 ∧ RCLike.re ⟪T x, x⟫_𝕜 ≤ hT.eigenvalues hn k := by
  set b := hT.eigenvectorBasis hn
  set W := specSubspace b (fun i : Fin n => k ≤ i) with hW
  have hWdim : finrank 𝕜 W = n - (k : ℕ) := by
    rw [hW, finrank_specSubspace, card_filter_le]
  
  have hsum : n < finrank 𝕜 V + finrank 𝕜 W := by
    rw [hWdim]
    have hk : (k : ℕ) < n := k.2
    omega
  have hinf : V ⊓ W ≠ ⊥ := by
    intro hbot
    have hle := Submodule.finrank_sup_add_finrank_inf_eq V W
    rw [hbot, finrank_bot, add_zero] at hle
    have hsup : finrank 𝕜 (↑(V ⊔ W) : Submodule 𝕜 E) ≤ n := by
      rw [← hn]; exact Submodule.finrank_le _
    omega
  obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hinf
  obtain ⟨hzV, hzW⟩ := Submodule.mem_inf.mp hz
  have hz0' : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz0
  set x := ((‖z‖⁻¹ : ℝ) : 𝕜) • z with hx
  have hnx : ‖x‖ = 1 := by
    rw [hx, norm_smul, RCLike.norm_ofReal, abs_inv, abs_norm, inv_mul_cancel₀ hz0']
  refine ⟨x, V.smul_mem _ hzV, hnx, ?_⟩

  have hxW : x ∈ W := W.smul_mem _ hzW
  calc RCLike.re ⟪T x, x⟫_𝕜
      ≤ hT.eigenvalues hn k * ‖x‖ ^ 2 :=
        re_inner_map_self_le_of_mem_specSubspace hT hn
          (fun _ hik => hT.eigenvalues_antitone hn hik) hxW
    _ = hT.eigenvalues hn k := by rw [hnx]; ring

theorem forall_unit_vector_eigenvalue_le_re_inner
    (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n) (k : Fin n) :
    ∃ V : Submodule 𝕜 E, finrank 𝕜 V = (k : ℕ) + 1 ∧
      ∀ x ∈ V, ‖x‖ = 1 → hT.eigenvalues hn k ≤ RCLike.re ⟪T x, x⟫_𝕜 := by
  set b := hT.eigenvectorBasis hn
  refine ⟨specSubspace b (fun i : Fin n => i ≤ k), ?_, ?_⟩
  · rw [finrank_specSubspace, card_filter_ge]
  · intro x hxV hnx

    calc hT.eigenvalues hn k
        = hT.eigenvalues hn k * ‖x‖ ^ 2 := by rw [hnx]; ring
      _ ≤ RCLike.re ⟪T x, x⟫_𝕜 :=
          le_re_inner_map_self_of_mem_specSubspace hT hn
            (fun _ hik => hT.eigenvalues_antitone hn hik) hxV

end LinearMap.IsSymmetric
end

namespace OMA.S_mo_123377
open Module LinearMap
open scoped InnerProductSpace
variable {𝕜 E F G H : Type} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G] [NormedAddCommGroup H]
  [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 F] [InnerProductSpace 𝕜 G] [InnerProductSpace 𝕜 H]
  [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] [FiniteDimensional 𝕜 G] [FiniteDimensional 𝕜 H]

private lemma ray_norm (T : E →ₗ[𝕜] F) (x : E) :
    RCLike.re ⟪(T.adjoint.comp T) x,x⟫_𝕜 = ‖T x‖^2 := by
  rw [LinearMap.comp_apply,LinearMap.adjoint_inner_left,inner_self_eq_norm_sq]

private lemma top_space (T : E →ₗ[𝕜] F) {i : ℕ} (hi : i<finrank 𝕜 E) :
    ∃ U : Submodule 𝕜 E, finrank 𝕜 U=i+1 ∧ ∀ x∈U, T.singularValues i * ‖x‖ ≤ ‖T x‖ := by
  obtain ⟨U,hU,h⟩ := T.isSymmetric_adjoint_comp_self.forall_unit_vector_eigenvalue_le_re_inner
    rfl ⟨i,hi⟩
  refine ⟨U,hU,?_⟩
  have hunit (y) (hy : y∈U) (hn : ‖y‖=1) : T.singularValues i ≤ ‖T y‖ := by
    have hh := h y hy hn
    rw [← T.sq_singularValues_fin rfl ⟨i,hi⟩,ray_norm] at hh
    exact (sq_le_sq₀ (T.singularValues_nonneg _) (norm_nonneg _)).mp hh
  intro x hx
  by_cases hz : x=0
  · simp [hz]
  have hp := norm_pos_iff.mpr hz
  let a : 𝕜 := ((‖x‖⁻¹ : ℝ) : 𝕜)
  have ha : ‖a‖ = ‖x‖⁻¹ := by simp [a]
  have hu : ‖a • x‖=1 := by rw [norm_smul,ha,inv_mul_cancel₀ hp.ne']
  have hh := hunit (a • x) (U.smul_mem _ hx) hu
  rw [map_smul,norm_smul,ha,← div_eq_inv_mul] at hh
  exact (le_div_iff₀ hp).mp hh

private lemma sv_ideal (L : F →ₗ[𝕜] G) (A : E →ₗ[𝕜] F) (R : H →ₗ[𝕜] E)
    (a b : ℝ) (ha : 0≤a) (hb : 0≤b) (hL : ∀ y, ‖L y‖ ≤ a*‖y‖) (hR : ∀ x, ‖R x‖ ≤ b*‖x‖) (i : ℕ) :
    (L.comp (A.comp R)).singularValues i ≤ (a*b)*A.singularValues i := by
  let T := L.comp (A.comp R)
  change T.singularValues i ≤ (a*b)*A.singularValues i
  by_cases hpos : 0 < T.singularValues i
  · have hi : i < finrank 𝕜 H := by
      by_contra! hh
      exact hpos.ne' (T.singularValues_of_finrank_le hh)
    obtain ⟨U,hU,hlo⟩ := top_space T hi
    let f : U →ₗ[𝕜] E := R.comp U.subtype
    have hf : Function.Injective f := by
      apply LinearMap.ker_eq_bot.mp
      apply LinearMap.ker_eq_bot'.mpr
      intro u hu
      have hr : R u.val=0 := hu
      have ht : T u.val=0 := by simp [T,hr]
      have hh := hlo u.val u.property
      rw [ht,norm_zero] at hh
      apply Subtype.ext
      apply norm_eq_zero.mp
      exact le_antisymm (by by_contra! hnorm; exact (not_lt_of_ge hh) (mul_pos hpos hnorm)) (norm_nonneg _)
    have hdim := (LinearEquiv.ofInjective f hf).finrank_eq
    have hV : i+1 ≤ finrank 𝕜 f.range := by omega
    have hin : i < finrank 𝕜 E := by have := Submodule.finrank_le f.range; omega
    obtain ⟨y,hy,hn,hsmall⟩ := A.isSymmetric_adjoint_comp_self.exists_unit_vector_re_inner_le_eigenvalue
      rfl ⟨i,hin⟩ f.range hV
    rw [ray_norm,← A.sq_singularValues_fin rfl ⟨i,hin⟩] at hsmall
    have hs := (sq_le_sq₀ (norm_nonneg _) (A.singularValues_nonneg _)).mp hsmall
    obtain ⟨u,hu⟩ := hy
    change R u.val = y at hu
    have hu1 : 1 ≤ b*‖u.val‖ := by rw [← hn,← hu]; exact hR _
    calc
      T.singularValues i ≤ T.singularValues i * (b * ‖u.val‖) := le_mul_of_one_le_right hpos.le hu1
      _ = b*(T.singularValues i*‖u.val‖) := by ring
      _ ≤ b*‖T u.val‖ := mul_le_mul_of_nonneg_left (hlo _ u.property) hb
      _ ≤ b*(a*‖A y‖) := mul_le_mul_of_nonneg_left (by rw [←hu]; exact hL _) hb
      _ ≤ b*(a*A.singularValues i) := by gcongr
      _ = _ := by ring
  · exact (le_of_not_gt hpos).trans (mul_nonneg (mul_nonneg ha hb) (A.singularValues_nonneg _))
end OMA.S_mo_123377

namespace OMA.S_mo_123377
open Matrix Finset Filter Polynomial
open scoped Matrix.Norms.L2Operator Topology
private lemma sv_transform {a b c d : ℕ} (L : Matrix (Fin a) (Fin b) ℂ)
    (A : Matrix (Fin b) (Fin c) ℂ) (R : Matrix (Fin c) (Fin d) ℂ) (i : ℕ) :
    (L*A*R).toEuclideanLin.singularValues i ≤ (‖L‖*‖R‖)*A.toEuclideanLin.singularValues i := by
  have hh : (L*A*R).toEuclideanLin=L.toEuclideanLin.comp (A.toEuclideanLin.comp R.toEuclideanLin) := by
    apply LinearMap.ext
    intro x
    change WithLp.toLp 2 ((L*A*R)*ᵥWithLp.ofLp x) = WithLp.toLp 2 (L*ᵥ(A*ᵥ(R*ᵥWithLp.ofLp x)))
    rw [mulVec_mulVec,mulVec_mulVec]
  rw [hh]
  exact sv_ideal _ _ _ _ _ (norm_nonneg _) (norm_nonneg _) L.l2_opNorm_mulVec R.l2_opNorm_mulVec i

private lemma diag_mode {n : ℕ} (v : Fin n → ℝ) (hv : ∀ i,0 ≤ v i) (hdis : Antitone v)
    (i : Fin n) : (diagonal (fun j => (v j:ℂ))).toEuclideanLin.singularValues i.val=v i := by
  let T := (diagonal (fun j => (v j:ℂ))).toEuclideanLin
  have hn : Module.finrank ℂ (EuclideanSpace ℂ (Fin n))=n := finrank_euclideanSpace_fin
  let q := fun j : Fin n => v j^2
  have hq : Antitone q := fun j k hjk => pow_le_pow_left₀ (hv k) (hdis hjk) 2
  have hT : T.adjoint ∘ₗ T = (diagonal (fun j => (q j:ℂ))).toEuclideanLin := by
    dsimp only [T]
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    change (Matrix.toLpLin 2 2 _ ∘ₗ Matrix.toLpLin 2 2 _) = Matrix.toLpLin 2 2 _
    rw [← Matrix.toLpLin_mul_same]
    congr 1
    ext j k
    by_cases h : j=k <;> simp [h,q,diagonal_conjTranspose,pow_two]
  have hroots : (T.adjoint ∘ₗ T).charpoly.roots.map RCLike.re = univ.val.map q := by
    rw [hT,Matrix.toEuclideanLin_eq_toLin_orthonormal,Matrix.charpoly_toLin,Matrix.charpoly_diagonal,
      Polynomial.roots_prod _ _ (by simp [Finset.prod_ne_zero_iff,Polynomial.X_sub_C_ne_zero])]
    simp [Function.comp_def]
  have hev : T.isSymmetric_adjoint_comp_self.eigenvalues hn=q := by
    rw [←List.ofFn_inj,←T.isSymmetric_adjoint_comp_self.sort_roots_charpoly_eq_eigenvalues hn,hroots,
      Fin.univ_val_map,Multiset.coe_sort]
    apply List.mergeSort_of_pairwise
    simp_rw [decide_eq_true_eq,← List.sortedGE_iff_pairwise]
    exact hq.sortedGE_ofFn
  change T.singularValues i.val=_
  rw [T.singularValues_fin hn,hev]
  exact Real.sqrt_sq (hv i)
end OMA.S_mo_123377

namespace OMA.S_mo_123377
open Matrix Filter Finset
open scoped Matrix.Norms.L2Operator Topology
private lemma modes (n m : ℕ) (hm : 0 < m) (hn : n ≤ m+1) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ K : ℝ in 𝓝[>] 0, ∀ i : Fin n,
      c*K^i.val ≤ (samples n m K).toEuclideanLin.singularValues i.val ∧
      (samples n m K).toEuclideanLin.singularValues i.val ≤ C*K^i.val := by
  let P := pascal n
  let W := scaledV n m
  let W₀ := tangent n m
  let G (M : Matrix (Fin n) (Fin (m+1)) ℂ) := M*Mᴴ
  let R (M : Matrix (Fin n) (Fin (m+1)) ℂ) := Mᴴ*(G M)⁻¹
  have hW : Tendsto W (𝓝[>] 0) (𝓝 W₀) := (show Tendsto W (𝓝[≠] 0) (𝓝 W₀) from
    tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => (scaled_tendsto _).pow i.val).mono_left
      (nhdsGT_le_nhdsNE 0)
  have hG : Continuous G := by dsimp [G]; fun_prop
  have hdet : (G W₀).det ≠ 0 := by
    intro h
    have hh := tangent_nondegenerate n m hm hn
    change 0 < (G W₀).det.re at hh
    simp [h] at hh
  have hInv := continuousAt_matrix_inv (G W₀) (by
    simpa [Ring.inverse_eq_inv] using (continuousAt_inv₀ hdet))
  have hR : ContinuousAt R W₀ := by
    dsimp only [R]
    have ht : Continuous (fun M : Matrix (Fin n) (Fin (m+1)) ℂ => Mᴴ) := by fun_prop
    have hmul : Continuous (fun p : Matrix (Fin (m+1)) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ => p.1*p.2) := continuous_fst.matrix_mul continuous_snd
    let Q := fun M : Matrix (Fin n) (Fin (m+1)) ℂ => (Mᴴ,(G M)⁻¹)
    have hQ : ContinuousAt Q W₀ := ContinuousAt.prodMk (ht.continuousAt (x:=W₀)) (hInv.comp (hG.continuousAt (x:=W₀)))
    exact (hmul.continuousAt (x:=Q W₀)).comp hQ
  have hne := ((continuous_id.matrix_det.comp hG).continuousAt.tendsto.comp hW).eventually_ne hdet
  let V := (‖P⁻¹‖+1)*(‖R W₀‖+1)
  let U := (‖P‖+1)*(‖W₀‖+1)
  have hV : 0 < V := by dsimp [V]; positivity
  have hU : 0 < U := by dsimp [U]; positivity
  refine ⟨V⁻¹,U,inv_pos.mpr hV,hU,?_⟩
  filter_upwards [hne,hW.norm.eventually_lt_const (show ‖W₀‖ < ‖W₀‖+1 by linarith),
    (hR.tendsto.comp hW).norm.eventually_lt_const (show ‖R W₀‖ < ‖R W₀‖+1 by linarith),
    self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds (gt_mem_nhds (by norm_num : (0:ℝ)<1))] with K hk hw hr hK hK1
  have hpos : 0<K := hK
  have hlt : K<1 := hK1
  intro i
  let D := scales n K
  have hf : samples n m K=P*D*W K := factorize n m K hpos.ne'
  have hsd : D.toEuclideanLin.singularValues i.val=K^i.val := by
    simpa [D,scales] using diag_mode (fun j : Fin n => K^j.val) (by intro j; positivity)
      (fun {j k} h => pow_le_pow_of_le_one hpos.le hlt.le h) i
  have huP : IsUnit P.det := by rw [show P.det=1 from pascal_det n]; exact isUnit_one
  have hwr : W K*R (W K)=1 := by
    change W K*((W K)ᴴ*(G (W K))⁻¹)=1
    rw [←Matrix.mul_assoc]
    exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hk)
  have hb : D=P⁻¹*samples n m K*R (W K) := by
    calc
      D = (P⁻¹*P)*D*(W K*R (W K)) := by rw [Matrix.nonsing_inv_mul _ huP,hwr,Matrix.one_mul,Matrix.mul_one]
      _ = P⁻¹*(P*D*W K)*R (W K) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [←hf]
  constructor
  · have ha := sv_transform P⁻¹ (samples n m K) (R (W K)) i.val
    rw [← hb,hsd] at ha
    rw [inv_mul_eq_div,div_le_iff₀ hV,mul_comm _ V]
    exact ha.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul (by linarith) hr.le (norm_nonneg _) (by positivity)) (LinearMap.singularValues_nonneg _ _))
  · have ha := sv_transform P D (W K) i.val
    rw [←hf,hsd] at ha
    exact ha.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul (by linarith) hw.le (norm_nonneg _) (by positivity)) (by positivity))
end OMA.S_mo_123377

namespace OMA.S_mo_123377
open Matrix Filter MeasureTheory
open scoped Topology
lemma solve :
    (∀ (n : ℕ) (K : ℝ), Tendsto (fun m : ℕ => empirical n m K) atTop (𝓝 (continuum n K))) ∧
    (∀ n m : ℕ, 0 < m → n ≤ m+1 →
      0 < ((tangent n m*(tangent n m)ᴴ).det).re ∧
      Tendsto (fun K : ℝ => (samples n m K*(samples n m K)ᴴ).det / (K:ℂ)^(n*(n-1)))
        (𝓝[≠] 0) (𝓝 ((tangent n m*(tangent n m)ᴴ).det))) ∧
    (∀ n m : ℕ, 0 < m → n ≤ m+1 → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ᶠ K : ℝ in 𝓝[>] 0, ∀ i : Fin n, c*K^i.val ≤ (samples n m K).toEuclideanLin.singularValues i.val ∧
        (samples n m K).toEuclideanLin.singularValues i.val ≤ C*K^i.val) :=
  ⟨density, fun n m hm hn => ⟨tangent_nondegenerate n m hm hn,aperture n m⟩,modes⟩
end OMA.S_mo_123377

open OMA.S_mo_123377 in
theorem OMA.solution : type_of% @OMA.S_mo_123377.main := solve
