import OMAReductions.R_mo_178849_R1
/- Adapted from OpenAI openai/math 3344da59991ed94f9ba711217b29c1d760badfa6 with private Spark2 overlays (threshold, factory, GChain). -/
section
open Set MeasureTheory Finsupp Geometry TopologicalSpace
open scoped Pointwise Classical
namespace FT
noncomputable def Small : Prop :=
 ∀(H Y:Type) (X:Profinite.{0})[Group H][Countable H][Countable Y][LinearOrder Y][MulAction H Y][IsCancelSMul H Y][MulAction H X][ContinuousConstSMul H X][IsCancelSMul H X],letI:=borel X;∀ μ:ProbabilityMeasure X,(∀h:H,MeasurePreserving ((h•·):X→X) μ μ)→∀(G:SimpleGraph Y)[G.LocallyFinite],G.Connected→(∀(h:H) u v,G.Adj (h•u) (h•v)↔G.Adj u v)→∀D n:ℕ,2≤D→(∀y,Fintype.card (G.neighborSet y)≤D)→(4*D^3+D+3)^2≤n→∀(F:Finset (Finset Y)) (B:PreAbstractSimplicialComplex Y),(∀t∈F,t.card=n+1∧(G.induce ↑t).Connected)→B.faces={s|s.Nonempty∧∃h:H,∃t∈F,s⊆h•t}→
 let K:=SimplicialComplex.onFinsupp (𝕜:=ℝ) B
 let V:=Y→₀ℝ
 letI:=(letI:=Classical.decEq Y; induced (linearCombination ℝ (fun y↦lp.single 2 y 1):V→ₗ[ℝ] lp (fun _:Y↦ℝ) 2) inferInstance)
 letI:=borel V
 let E (p:V) (f:Y→ℝ):=p.sum fun y r↦r*f y
 let ok (U:Set V):=∀A⊆U,IsPreconnected A→∀p∈A,∀q∈A,sSup {r|∃f:Y→ℝ,(∀u v,dist (f u) (f v)≤G.dist u v)∧E p f-E q f=r}/Real.sqrt n≤2*(4*(D:ℝ)^2)
 let I:={s:Finset Y//s∈B.faces∧s.card=n+1}
 ∃C:I→ℝ,(∀s,0≤C s)∧∀ε:ℝ,0<ε→
 let count (P:X→Set V):=∀s:I,(∫ x,(Measure.count (P x∩convexHull ℝ ((s.val.image fun y↦single y (1:ℝ)):Set V))).toReal ∂μ)≤C s*ε
 let S:=SimplicialComplex ℝ V
 let c (s:Finset V):=convexHull ℝ ↑s
 let tr (A:Set (Finset V)) (p:Set V):={s∈A|↑s⊆p}
 let sub (L B:S):=L.space=B.space∧(∀s∈L.faces,∃t∈B.faces,c s⊆c t)∧∀t∈B.faces,(∀s∈L.faces,c s∩c t=convexHull ℝ (↑s∩c t))∧(tr L.faces (c t)).Finite
 let a (h:H):=Finsupp.domLCongr (R:=ℝ) (MulAction.toPerm h:Y≃Y)
 ∃(T:ℕ→X→S) (P:ℕ→X→Set V),count (P 0)∧(∀i x,sub (T i x) K)∧(∀i x v,v∈P i x→∃s∈(T i x).faces,v∈c s∧c s⊆P i x)∧(∀i t,t∈K.faces→IsLocallyConstant (fun x↦tr (T i x).faces (c t))∧IsLocallyConstant (fun x↦tr {s∈(T i x).faces|c s⊆P i x} (c t)))∧(∀i h x s,s∈(T i x).faces→s.map (a h).toEmbedding∈(T i (h•x)).faces)∧(∀i h x v,v∈P i x→a h v∈P i (h•x))∧(∀x,T n x=K∧P n x=K.space)∧∀i,i<n→∀x,sub (T i x) (T (i+1) x)∧P i x⊆P (i+1) x∧(∀t∈(T (i+1) x).faces,c t⊆P (i+1) x→∀s∈(T i x).faces,c s⊆c t∩P i x→s.card<t.card)∧ok (P (i+1) x\P i x)
end FT
end
section
open Set MeasureTheory
open scoped Classical Pointwise
namespace FT
def Raw {H X Y : Type} [Group H] [MulAction H X] [MulAction H Y] [TopologicalSpace X]
    (K : Geometry.SimplicialComplex ℝ (Y →₀ ℝ)) (n : ℕ)
    (ok : Set (Y →₀ ℝ) → Prop) (count : (X → Set (Y →₀ ℝ)) → Prop) : Prop :=
 let V := Y →₀ ℝ
 let S := Geometry.SimplicialComplex ℝ V
 let c := fun s : Finset V => convexHull ℝ (s : Set V)
 let tr := fun (A : Set (Finset V)) (p : Set V) => {s ∈ A | (s : Set V) ⊆ p}
 let sub := fun (L B : S) => L.space=B.space ∧ (∀ s∈L.faces,∃ t∈B.faces,c s⊆c t) ∧
  ∀ t∈B.faces,(∀ s∈L.faces,c s∩c t=convexHull ℝ ((s:Set V)∩c t)) ∧ (tr L.faces (c t)).Finite
 let a := fun h : H => Finsupp.domLCongr (R:=ℝ) (MulAction.toPerm h : Y≃Y)
 ∃ (T : ℕ → X → S) (P : ℕ → X → Set V), count (P 0) ∧
 (∀ i x,sub (T i x) K) ∧ (∀ i x v,v∈P i x → ∃ s∈(T i x).faces,v∈c s ∧ c s⊆P i x) ∧
 (∀ i t,t∈K.faces → IsLocallyConstant (fun x=>tr (T i x).faces (c t)) ∧
  IsLocallyConstant (fun x=>tr {s∈(T i x).faces | c s⊆P i x} (c t))) ∧
 (∀ i h x s,s∈(T i x).faces → s.map (a h).toEmbedding∈(T i (h•x)).faces) ∧
 (∀ i h x v,v∈P i x → a h v∈P i (h•x)) ∧ (∀ x,T n x=K ∧ P n x=K.space) ∧
 ∀ i,i<n → ∀ x,sub (T i x) (T (i+1) x) ∧ P i x⊆P (i+1) x ∧
 (∀ t∈(T (i+1) x).faces,c t⊆P (i+1) x → ∀ s∈(T i x).faces,c s⊆c t∩P i x → s.card<t.card) ∧
 ok (P (i+1) x \ P i x)
end FT
end
section
theorem ite_eq_left {c : Prop} {h : Decidable c} (hc : c) {α : Sort*} {t e : α} : (ite c t e) = t := if_pos hc
theorem ite_eq_right {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort*} {t e : α} : (ite c t e) = e := if_neg hc
theorem dite_eq_left {c : Prop} {h : Decidable c} (hc : c) {α : Sort*} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := dif_pos hc
theorem Finsupp.mapDomain_apply_of_injective {α β M : Type*} [AddCommMonoid M] {f : α → β} (hf : f.Injective) (x : α →₀ M) (a : α) : Finsupp.mapDomain f x (f a) = x a := Finsupp.mapDomain_apply hf x a
def Set.equivOfEq {α : Type*} {s t : Set α} (h : s = t) : s ≃ t := Equiv.setCongr h
theorem Isometry.lipschitzWith {α β : Type*} [PseudoEMetricSpace α] [PseudoEMetricSpace β] {f : α → β} (h : Isometry f) : LipschitzWith 1 f := h.lipschitz
@[simp] theorem SimpleGraph.ncard_neighborSet {V : Type*} (G : SimpleGraph V) (v : V) [Fintype (G.neighborSet v)] : (G.neighborSet v).ncard = G.degree v := by
  simp [← Set.fintypeCard_eq_ncard, SimpleGraph.card_neighborSet_eq_degree]
end
section
namespace OAI
namespace BassTrace
end BassTrace
end OAI

end
section
namespace OAI
noncomputable section
namespace BassTrace
namespace Chains
open scoped BigOperators
variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]
abbrev contraction (α : M →ₗ[R] R) : ExteriorAlgebra R M →ₗ[R] ExteriorAlgebra R M :=
  CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) α
@[simp] lemma contraction_one (α : M →ₗ[R] R) :
    contraction α (1 : ExteriorAlgebra R M) = 0 :=
  CliffordAlgebra.contractLeft_one _ α
lemma contraction_ι_mul (α : M →ₗ[R] R) (v : M) (x : ExteriorAlgebra R M) :
    contraction α (ExteriorAlgebra.ι R v * x) =
      α v • x - ExteriorAlgebra.ι R v * contraction α x :=
  CliffordAlgebra.contractLeft_ι_mul α v x
lemma contraction_ιMulti_succ (α : M →ₗ[R] R) {n : ℕ} (v : Fin (n+1) → M) :
    contraction α (ExteriorAlgebra.ιMulti R (n+1) v) =
      α (v 0) • ExteriorAlgebra.ιMulti R n (fun i => v i.succ) -
        ExteriorAlgebra.ι R (v 0) *
          contraction α (ExteriorAlgebra.ιMulti R n (fun i => v i.succ)) := by
  rw [ExteriorAlgebra.ιMulti_succ_apply, contraction_ι_mul]
  rfl
lemma contraction_mem_exteriorPower (α : M →ₗ[R] R) (n : ℕ)
    {x : ExteriorAlgebra R M} (hx : x ∈ ⋀[R]^(n+1) M) :
    contraction α x ∈ ⋀[R]^n M := by
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree R (n+1)] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    induction n with
    | zero =>
      rw [contraction_ιMulti_succ]
      simp only [ExteriorAlgebra.ιMulti_zero_apply, contraction_one, mul_zero, sub_zero]
      exact Submodule.smul_mem _ _ (by simp [ExteriorAlgebra.exteriorPower])
    | succ n ih =>
      rw [contraction_ιMulti_succ]
      apply Submodule.sub_mem
      · exact Submodule.smul_mem _ _ (ExteriorAlgebra.ιMulti_range R (n+1) ⟨_, rfl⟩)
      · have ht := ih (fun i => v i.succ)
        rw [ExteriorAlgebra.exteriorPower, pow_succ' ]
        exact Submodule.mul_mem_mul (LinearMap.mem_range.mpr ⟨v 0, rfl⟩) ht
  | zero => simp
  | add x y _ _ hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
  | smul a x _ hx => simpa only [map_smul] using Submodule.smul_mem _ a hx
variable (Y : Type*)
abbrev Vectors := Y →₀ ℂ
abbrev Algebra := ExteriorAlgebra ℂ (Vectors Y)
abbrev Degree (n : ℕ) := ⋀[ℂ]^n (Vectors Y)
noncomputable def augmentation : Vectors Y →ₗ[ℂ] ℂ :=
  Finsupp.linearCombination ℂ (fun _ : Y => (1 : ℂ))
noncomputable def boundary : Algebra Y →ₗ[ℂ] Algebra Y :=
  contraction (augmentation Y)
end Chains
namespace Oriented
open scoped BigOperators
variable {Y A : Type*} [AddCommGroup A] [Module ℂ A]
abbrev Degree (Y : Type*) (n : ℕ) := ⋀[ℂ]^n (Y →₀ ℂ)
def wedge (n : ℕ) (v : Fin n → Y) : Degree Y n :=
  exteriorPower.ιMulti ℂ n (fun i => Finsupp.single (v i) 1)
lemma wedge_perm (n : ℕ) (v : Fin n → Y) (σ : Equiv.Perm (Fin n)) :
    wedge n (v ∘ σ) = Equiv.Perm.sign σ • wedge n v :=
  by simpa only [wedge, Function.comp_def] using
    (exteriorPower.ιMulti ℂ n).map_perm (fun i => Finsupp.single (v i) 1) σ
lemma wedge_eq_zero_of_not_injective (n : ℕ) {v : Fin n → Y}
    (hv : ¬ Function.Injective v) : wedge n v = 0 := by
  apply (exteriorPower.ιMulti ℂ n).map_eq_zero_of_not_injective
  intro h
  exact hv fun i j hij => h (by simpa only using congrArg (fun y => Finsupp.single y (1 : ℂ)) hij)
structure AltFunction (Y : Type*) (n : ℕ) (A : Type*) [AddCommGroup A] where
  toFun : (Fin n → Y) → A
  perm : ∀ v (σ : Equiv.Perm (Fin n)), toFun (v ∘ σ) = Equiv.Perm.sign σ • toFun v
  zero : ∀ v, ¬ Function.Injective v → toFun v = 0
instance {n : ℕ} : CoeFun (AltFunction Y n A) (fun _ => (Fin n → Y) → A) :=
  ⟨AltFunction.toFun⟩
variable [LinearOrder Y]
abbrev basis (n : ℕ) : Module.Basis (Set.powersetCard Y n) ℂ (Degree Y n) :=
  (Finsupp.basisSingleOne : Module.Basis Y ℂ (Y →₀ ℂ)).exteriorPower n
lemma basis_eq_wedge (n : ℕ) (s : Set.powersetCard Y n) :
    basis n s = wedge n (Set.powersetCard.ofFinEmbEquiv.symm s) := by
  rw [exteriorPower.basis_apply]
  rfl
lemma exists_sorted_perm {n : ℕ} (v : Fin n → Y) (hv : Function.Injective v) :
    ∃ (s : Set.powersetCard Y n) (σ : Equiv.Perm (Fin n)),
      v = (Set.powersetCard.ofFinEmbEquiv.symm s) ∘ σ := by
  classical
  let s : Set.powersetCard Y n :=
    ⟨Finset.univ.image v, by simpa using Finset.card_image_of_injective Finset.univ hv⟩
  let w : Fin n ↪o Y := Set.powersetCard.ofFinEmbEquiv.symm s
  have hs (i : Fin n) : v i ∈ s := by simp [s]
  have hw (i : Fin n) : ∃ j, w j = v i :=
    (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem s (v i)).mpr (hs i)
  let f : Fin n → Fin n := fun i => (hw i).choose
  have hf (i : Fin n) : w (f i) = v i := (hw i).choose_spec
  have hfinj : Function.Injective f := by
    intro i j hij
    apply hv
    rw [← hf i, ← hf j, hij]
  let σ : Equiv.Perm (Fin n) := Equiv.ofBijective f
    ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hfinj, rfl⟩)
  refine ⟨s, σ, ?_⟩
  funext i
  exact (hf i).symm
def AltFunction.lift {n : ℕ} (f : AltFunction Y n A) : Degree Y n →ₗ[ℂ] A :=
  (basis n).constr ℂ fun s => f (Set.powersetCard.ofFinEmbEquiv.symm s)
@[simp] lemma AltFunction.lift_wedge {n : ℕ} (f : AltFunction Y n A)
    (v : Fin n → Y) : f.lift (wedge n v) = f v := by
  classical
  by_cases hv : Function.Injective v
  · obtain ⟨s, σ, rfl⟩ := exists_sorted_perm v hv
    rw [wedge_perm, f.perm, ← basis_eq_wedge]
    simp only [Units.smul_def, map_zsmul, AltFunction.lift, Module.Basis.constr_basis]
  · rw [wedge_eq_zero_of_not_injective n hv, map_zero, f.zero v hv]
lemma linearMap_ext_wedge {n : ℕ} {f g : Degree Y n →ₗ[ℂ] A}
    (h : ∀ v, f (wedge n v) = g (wedge n v)) : f = g := by
  apply (basis n).ext
  intro s
  rw [basis_eq_wedge]
  exact h _
end Oriented
namespace ChainHomotopy
open scoped BigOperators
open Oriented
variable {Y : Type*}
def average (n : ℕ) (v : Fin n → Y) : Y →₀ ℂ :=
  (n : ℂ)⁻¹ • ∑ i, Finsupp.single (v i) 1
lemma average_perm (n : ℕ) (v : Fin n → Y) (σ : Equiv.Perm (Fin n)) :
    average n (v ∘ σ) = average n v := by
  unfold average
  congr 1
  exact Equiv.sum_comp σ (fun y => Finsupp.single (v y) (1 : ℂ))
def cone (n : ℕ) (v : Y →₀ ℂ) : Degree Y n →ₗ[ℂ] Degree Y (n+1) where
  toFun x := ⟨ExteriorAlgebra.ι ℂ v * x, by
    change _ ∈ (ExteriorAlgebra.ι ℂ).range ^ (n+1)
    rw [pow_succ']
    exact Submodule.mul_mem_mul (LinearMap.mem_range.mpr ⟨v, rfl⟩) x.property⟩
  map_add' a b := by ext; exact mul_add _ _ _
  map_smul' a x := by ext; exact mul_smul_comm _ _ _
def d (n : ℕ) : Degree Y (n+1) →ₗ[ℂ] Degree Y n :=
  ((Chains.boundary Y).comp (Degree Y (n+1)).subtype).codRestrict _ fun x =>
    Chains.contraction_mem_exteriorPower (Chains.augmentation Y) n x.property
def coneFunction {n : ℕ} (r : Degree Y n →ₗ[ℂ] Degree Y n) :
    AltFunction Y n (Degree Y (n+1)) where
  toFun v := cone n (average n v) (r (wedge n v))
  perm v σ := by
    rw [average_perm, wedge_perm]
    simp only [Units.smul_def, map_zsmul]
  zero v hv := by
    rw [wedge_eq_zero_of_not_injective n hv, map_zero, map_zero]
variable [LinearOrder Y]
def coneLift {n : ℕ} (r : Degree Y n →ₗ[ℂ] Degree Y n) :
    Degree Y n →ₗ[ℂ] Degree Y (n+1) := (coneFunction r).lift
end ChainHomotopy
end BassTrace
end
end OAI

end
section
namespace OAI
noncomputable section
namespace BassTrace
namespace OrientedIncidence
section
open scoped BigOperators
open Oriented ChainHomotopy
variable {V : Type*} [LinearOrder V]
abbrev vertices {n : ℕ} (s : Set.powersetCard V n) : Fin n ↪o V :=
  Set.powersetCard.ofFinEmbEquiv.symm s
lemma vertices_mem {n : ℕ} (s : Set.powersetCard V n) (i : Fin n) : vertices s i ∈ s.val :=
  Finset.orderEmbOfFin_mem s.val s.property i
def eraseFace {n : ℕ} (s : Set.powersetCard V (n+1)) (i : Fin (n+1)) :
    Set.powersetCard V n :=
  ⟨s.val.erase (vertices s i), by simp [Finset.card_erase_of_mem (vertices_mem s i)]⟩
end
end OrientedIncidence
namespace Sparse.Orientation
section
open scoped BigOperators
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
def facetForm (n : ℕ) (v : Fin n → (Fin (n+1) → ℝ)) : (Fin (n+1) → ℝ) →ₗ[ℝ] ℝ :=
  { toFun := fun x => Matrix.detRowAlternating.curryLeft x v
    map_add' := fun x y => by simp
    map_smul' := fun c x => by simp }
end
end Sparse.Orientation
namespace Fundamental
open scoped BigOperators
open OrientedIncidence Oriented ChainHomotopy Sparse.Orientation
variable {V : Type*} [LinearOrder V] {n : ℕ}
def chain (F : Finset (Set.powersetCard V (n+1))) (p : V → (Fin (n+1) → ℝ)) :
    Oriented.Degree V (n+1) :=
  ∑ s ∈ F, (Real.sign (Matrix.det (fun i => p (vertices s i))) : ℂ) • basis (n+1) s
end Fundamental
end BassTrace
end
end OAI

end
section
namespace OAI
noncomputable section
namespace BassTrace.Sparse
section
open Set Finset
open scoped Topology
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
lemma sum_weights_mem_convexHull (s : Finset E) {w : E → ℝ}
    (hw : ∀ x ∈ s, 0 ≤ w x) (hsum : ∑ x ∈ s, w x = 1) :
    ∑ x ∈ s, w x • x ∈ convexHull ℝ (s : Set E) :=
  (convex_convexHull ℝ (s : Set E)).sum_mem hw hsum
    (fun _ hx => subset_convexHull ℝ (s : Set E) hx)
end
section
end
section
end
section
open Set Finset
open scoped Topology Classical
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma positiveCombination_carrier {F T : Finset E}
    (hF : AffineIndependent ℝ ((↑) : F → E)) (hTF : T ⊆ F)
    (w : E → ℝ) (hw : ∀ x ∈ F, 0 < w x) (hws : ∑ x ∈ F, w x = 1)
    (hq : (∑ x ∈ F, w x • x) ∈ convexHull ℝ (T : Set E)) : F ⊆ T := by
  classical
  obtain ⟨a,_,has,hap⟩ := Finset.mem_convexHull'.mp hq
  let a' : E → ℝ := fun x => if x ∈ T then a x else 0
  have hs : ∑ x ∈ F, a' x = 1 := by
    calc
      _ = ∑ x ∈ T, a' x := (Finset.sum_subset hTF (fun x _ hx => by simp [a',hx])).symm
      _ = ∑ x ∈ T, a x := Finset.sum_congr rfl (fun x hx => by simp [a',hx])
      _ = 1 := has
  have hp : ∑ x ∈ F, a' x • x = ∑ x ∈ F, w x • x := by
    calc
      _ = ∑ x ∈ T, a' x • x :=
        (Finset.sum_subset hTF (fun x _ hx => by simp [a',hx])).symm
      _ = ∑ x ∈ T, a x • x := Finset.sum_congr rfl (fun x hx => by simp [a',hx])
      _ = _ := hap
  have he := hF.eq_of_sum_eq_sum_subtype (hs.trans hws.symm) hp
  intro x hx
  by_contra hxt
  have hzero : w x = 0 := by simpa [a',hxt] using (he x hx).symm
  exact (ne_of_gt (hw x hx)) hzero
lemma simplex_contains_positivePoint (K : Geometry.SimplicialComplex ℝ E)
    {F T : Finset E} (hF : F ∈ K.faces) (hT : T ∈ K.faces)
    (w : E → ℝ) (hw : ∀ x ∈ F, 0 < w x) (hws : ∑ x ∈ F, w x = 1)
    (hq : (∑ x ∈ F, w x • x) ∈ convexHull ℝ (T : Set E)) : F ⊆ T := by
  classical
  have hqF := sum_weights_mem_convexHull F (fun x hx => (hw x hx).le) hws
  have hqI := K.inter_subset_convexHull hF hT ⟨hqF,hq⟩
  have hs := positiveCombination_carrier (K.indep hF) Finset.inter_subset_left w hw hws
    (by simpa only [Finset.coe_inter] using hqI)
  exact hs.trans Finset.inter_subset_right
end
end
section
end
open Set Finset
open scoped Classical
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
def facetApexes (K : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (F : Finset E) : Finset E :=
  (hK.toFinset.biUnion id).filter (fun u => u ∉ F ∧ insert u F ∈ K.faces)
@[simp] lemma mem_facetApexes (K : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (F : Finset E) (u : E) : u ∈ facetApexes K hK F ↔ u ∉ F ∧ insert u F ∈ K.faces := by
  simp only [facetApexes,Finset.mem_filter,Finset.mem_biUnion,Set.Finite.mem_toFinset,id_eq]
  exact ⟨fun h => h.2,fun h => ⟨⟨insert u F,h.2,Finset.mem_insert_self _ _⟩,h⟩⟩
end BassTrace.Sparse
end
end OAI

end
section
namespace OAI
noncomputable section
namespace BassTrace
namespace Sparse
section
end
end Sparse
namespace Fundamental
section
open scoped BigOperators
open OrientedIncidence Oriented ChainHomotopy Sparse.Orientation
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [LinearOrder E]
def faces (K : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite) (k : ℕ) :
    Finset (Set.powersetCard E k) := by
  classical
  exact hK.toFinset.subtype fun s : Finset E => s ∈ Set.powersetCard E k
end
section
end
end
section
end
section
end
section
end
end Fundamental
end BassTrace
end
end OAI

end
section
namespace OAI
noncomputable section
namespace BassTrace
namespace ChainHomotopy
open scoped BigOperators
open Oriented
variable {Y Z W : Type*}
def vertexMap (f : Y → Z) : (Y →₀ ℂ) →ₗ[ℂ] (Z →₀ ℂ) := Finsupp.lmapDomain ℂ ℂ f
def relabel (n : ℕ) (f : Y → Z) : Degree Y n →ₗ[ℂ] Degree Z n :=
  exteriorPower.map n (vertexMap f)
end ChainHomotopy
namespace Fundamental
end Fundamental
namespace Sparse
end Sparse
namespace Fundamental
end Fundamental
namespace Oriented
open scoped BigOperators
variable {Y A : Type*} [AddCommGroup A] [Module ℂ A]
instance {n : ℕ} : CoeFun (AltFunction Y n A) (fun _ => (Fin n → Y) → A) :=
  ⟨AltFunction.toFun⟩
end Oriented
namespace ChainHomotopy
section
end
section
end
end ChainHomotopy
end BassTrace
end
end OAI

end
section
namespace OAI
noncomputable section
namespace BassTrace
namespace ChainHomotopy
open scoped BigOperators
open Oriented
variable {Y H : Type*} [LinearOrder Y]
lemma tuple_image_perm {n : ℕ} (v : Fin n → Y) (σ : Equiv.Perm (Fin n)) :
    Finset.univ.image (v ∘ σ) = Finset.univ.image v := by
  classical
  ext y
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨fun ⟨i, hi⟩ => ⟨σ i, hi⟩,
    fun ⟨i, hi⟩ => ⟨σ.symm i, by simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hi⟩⟩
end ChainHomotopy
namespace BarycentricChains
open scoped BigOperators
open Oriented ChainHomotopy
variable {V Y : Type*} [LinearOrder V]
def stepValues {n : ℕ} (b : Finset V → Y →₀ ℂ)
    (F : Degree V n →ₗ[ℂ] Degree Y n) : AltFunction V (n+1) (Degree Y (n+1)) where
  toFun v := cone n (b (Finset.univ.image v)) (F (d n (wedge (n+1) v)))
  perm v σ := by
    rw [tuple_image_perm, wedge_perm]
    simp only [Units.smul_def,map_zsmul]
  zero v hv := by
    rw [wedge_eq_zero_of_not_injective _ hv,map_zero,map_zero,map_zero]
def labelMap (b : Finset V → Y →₀ ℂ) : ∀ n, Degree V n →ₗ[ℂ] Degree Y n
  | 0 => exteriorPower.map 0 (0 : (V →₀ ℂ) →ₗ[ℂ] (Y →₀ ℂ))
  | n+1 => (stepValues b (labelMap b n)).lift
end BarycentricChains
end BassTrace
end
end OAI

end
section
namespace OAI
namespace BassTrace.Sparse.Cuts
open Set Finset
open scoped Classical
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
noncomputable def vertexMean (s : Finset E) : E :=
  (s.card : ℝ)⁻¹ • ∑ x ∈ s, x
lemma vertexMean_mem_convexHull {s : Finset E} (hs : s.Nonempty) :
    vertexMean s ∈ convexHull ℝ (s : Set E) := by
  have h := s.centerMass_id_mem_convexHull (R := ℝ) (w := fun _ => 1)
    (fun _ _ => zero_le_one) (by simpa using (Nat.cast_pos.mpr hs.card_pos : (0 : ℝ) < s.card))
  simpa [Finset.centerMass, vertexMean] using h
def cell {I : Type*} (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ) : Set E :=
  {x | ∀ i, a i x ≤ b i}
section BoundedRay
end BoundedRay
lemma linear_eq_on_affineSpan (f : E →ₗ[ℝ] ℝ) {S : Set E} {b : ℝ}
    (hS : ∀ x ∈ S, f x = b) {x : E} (hx : x ∈ affineSpan ℝ S) : f x = b := by
  refine affineSpan_induction hx hS ?_
  intro t u v w hu hv hw
  simp only [vsub_eq_sub, vadd_eq_add, map_add, map_smul, map_sub, hu, hv, hw,
    sub_self, smul_zero, zero_add]
lemma convexHull_inter_supporting (S : Set E) (f : E →ₗ[ℝ] ℝ) (b : ℝ)
    (hS : ∀ x ∈ S, f x ≤ b) :
    convexHull ℝ S ∩ {x | f x = b} = convexHull ℝ (S ∩ {x | f x = b}) := by
  let T := convexHull ℝ (S ∩ {x | f x = b})
  let C := {x : E | f x ≤ b ∧ (f x = b → x ∈ T)}
  have hSC : S ⊆ C := by
    intro x hx
    exact ⟨hS x hx, fun he => subset_convexHull ℝ _ ⟨hx, he⟩⟩
  have hC : Convex ℝ C := by
    intro x hx y hy u v hu hv huv
    change f (u • x + v • y) ≤ b ∧ (f (u • x + v • y) = b → _)
    simp only [map_add, map_smul, smul_eq_mul]
    have hew : u*b + v*b = b := by rw [← add_mul, huv, one_mul]
    have hux : 0 ≤ u*(b-f x) := mul_nonneg hu (sub_nonneg.mpr hx.1)
    have hvy : 0 ≤ v*(b-f y) := mul_nonneg hv (sub_nonneg.mpr hy.1)
    refine ⟨?_, ?_⟩
    · nlinarith only [hew, hux, hvy]
    · intro he
      by_cases hu0 : u = 0
      · have hv1 : v = 1 := by linarith
        have hyb : f y = b := by simpa [hu0, hv1] using he
        simpa [hu0, hv1] using hy.2 hyb
      by_cases hv0 : v = 0
      · have hu1 : u = 1 := by linarith
        have hxb : f x = b := by simpa [hv0, hu1] using he
        simpa [hv0, hu1] using hx.2 hxb
      have hux0 : u*(b-f x) = 0 := by nlinarith only [he, hew, hux, hvy]
      have hvy0 : v*(b-f y) = 0 := by nlinarith only [he, hew, hux, hvy]
      have hxb : f x = b := (sub_eq_zero.mp ((mul_eq_zero.mp hux0).resolve_left hu0)).symm
      have hyb : f y = b := (sub_eq_zero.mp ((mul_eq_zero.mp hvy0).resolve_left hv0)).symm
      exact (convex_convexHull ℝ _) (hx.2 hxb) (hy.2 hyb) hu hv huv
  apply subset_antisymm
  · intro x hx
    exact (convexHull_min hSC hC hx.1).2 hx.2
  · intro x hx
    refine ⟨convexHull_mono Set.inter_subset_left hx, ?_⟩
    exact linear_eq_on_affineSpan f (fun _ hy => hy.2)
      (convexHull_subset_affineSpan _ hx)
end BassTrace.Sparse.Cuts
end OAI

end
section
namespace OAI
namespace BassTrace.Sparse.Cuts
open Set Finset
open scoped Classical
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
section Restriction
def restrictComplex (B : Geometry.SimplicialComplex ℝ E) (P : Set E) :
    Geometry.SimplicialComplex ℝ E where
  faces := {s | s ∈ B.faces ∧ (s : Set E) ⊆ P}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨B.nonempty_of_mem_faces hs.1, ?_⟩
    intro t hts ht
    exact ⟨B.down_closed hs.1 hts ht, fun _ hx => hs.2 (hts hx)⟩
  indep hs := B.indep hs.1
  inter_subset_convexHull hs ht := B.inter_subset_convexHull hs.1 ht.1
end Restriction
section Trace
def RespectsSet (B : Geometry.SimplicialComplex ℝ E) (P : Set E) : Prop :=
  ∀ s ∈ B.faces, convexHull ℝ (s : Set E) ∩ P = convexHull ℝ ((s : Set E) ∩ P)
lemma restrictComplex_space_of_respects (B : Geometry.SimplicialComplex ℝ E)
    (P : Set E) (h : RespectsSet B P) :
    (restrictComplex B P).space = B.space ∩ P := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨s, hs, hx⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx
    refine ⟨B.convexHull_subset_space hs.1 hx, ?_⟩
    have he : (s : Set E) ∩ P = s := Set.inter_eq_left.mpr hs.2
    have hx' : x ∈ convexHull ℝ (s : Set E) ∩ P := by
      rw [h s hs.1, he]
      exact hx
    exact hx'.2
  · rintro ⟨hx, hxP⟩
    obtain ⟨s, hs, hx⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx
    let t := s.filter (· ∈ P)
    have ht : (t : Set E) = (s : Set E) ∩ P := by ext; simp [t]
    have hxt : x ∈ convexHull ℝ (t : Set E) := by
      rw [ht, ← h s hs]
      exact ⟨hx, hxP⟩
    have hne : t.Nonempty := Finset.coe_nonempty.mp (convexHull_nonempty_iff.mp ⟨x, hxt⟩)
    refine Geometry.SimplicialComplex.mem_space_iff.mpr
      ⟨t, ⟨B.down_closed hs (Finset.filter_subset _ _) hne, ?_⟩, hxt⟩
    intro y hy
    exact (Finset.mem_filter.mp hy).2
lemma hull_inter_of_supporting_eq (s : Finset E) (P Q : Set E)
    (hsP : convexHull ℝ (s : Set E) ⊆ P) (f : E →ₗ[ℝ] ℝ) (b : ℝ)
    (hf : ∀ x ∈ P, f x ≤ b) (hface : P ∩ Q = P ∩ {x | f x = b}) :
    convexHull ℝ (s : Set E) ∩ Q = convexHull ℝ ((s : Set E) ∩ Q) := by
  have hiff (x : E) (hx : x ∈ P) : x ∈ Q ↔ f x = b := by
    constructor
    · intro hq
      exact (hface.subset ⟨hx, hq⟩).2
    · intro he
      exact (hface.symm.subset ⟨hx, he⟩).2
  calc
    _ = convexHull ℝ (s : Set E) ∩ {x | f x = b} := by
      ext x
      exact and_congr_right (fun hx => hiff x (hsP hx))
    _ = convexHull ℝ ((s : Set E) ∩ {x | f x = b}) :=
      convexHull_inter_supporting _ f b (fun x hx => hf x (hsP (subset_convexHull _ _ hx)))
    _ = _ := by
      congr 1
      ext x
      exact and_congr_right (fun hx => (hiff x (hsP (subset_convexHull _ _ hx))).symm)
end Trace
section GeneralBoundary
end GeneralBoundary
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
def SupportingFace (Q P : Set V) : Prop :=
  ∃ (f : V →ₗ[ℝ] ℝ) (b : ℝ), (∀ x ∈ P, f x ≤ b) ∧
    Q = P ∩ {x | f x = b}
lemma SupportingFace.subset {Q P : Set V} (h : SupportingFace Q P) : Q ⊆ P := by
  obtain ⟨f, b, _, rfl⟩ := h
  exact Set.inter_subset_left
lemma linear_le_on_convexHull (s : Set V) (f : V →ₗ[ℝ] ℝ) (b : ℝ)
    (hf : ∀ x ∈ s, f x ≤ b) : ∀ x ∈ convexHull ℝ s, f x ≤ b := by
  intro x hx
  apply convexHull_min (s := s) (t := {y | f y ≤ b}) hf _ hx
  intro y hy z hz u v hu hv huv
  simp only [Set.mem_ofPred_eq, map_add, map_smul, smul_eq_mul] at *
  calc
    u * f y + v * f z ≤ u * b + v * b :=
      add_le_add (mul_le_mul_of_nonneg_left hy hu) (mul_le_mul_of_nonneg_left hz hv)
    _ = b := by rw [← add_mul, huv, one_mul]
end BassTrace.Sparse.Cuts
end OAI

end
section
namespace OAI
namespace BassTrace.Sparse.Cuts
open Set Finset
open scoped Classical
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
section CellVertices
open Filter
open scoped Topology
variable {I : Type*} [Fintype I]
noncomputable def activeConstraints (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ) (x : E) : Finset I :=
  Finset.univ.filter fun i => a i x = b i
lemma mem_activeConstraints (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ) (x : E) (i : I) :
    i ∈ activeConstraints a b x ↔ a i x = b i := by
  classical
  simp [activeConstraints]
lemma exists_extrapolate_mem
    (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ) {x y : E}
    (hx : x ∈ cell a b)
    (hactive : activeConstraints a b x = activeConstraints a b y) :
    ∃ t : ℝ, 0 < t ∧ x + t • (x - y) ∈ cell a b := by
  have hi (i : I) : ∀ᶠ t : ℝ in 𝓝 0, a i (x + t • (x - y)) ≤ b i := by
    by_cases h : a i x = b i
    · have hyi : a i y = b i := by
        rw [← mem_activeConstraints, ← hactive, mem_activeConstraints]
        exact h
      filter_upwards [] with t
      simp only [map_add, map_smul, map_sub, smul_eq_mul, h, hyi, sub_self,
        mul_zero, add_zero, le_refl]
    · have hlt : a i x < b i := lt_of_le_of_ne (hx i) h
      have hc : Continuous (fun t : ℝ => a i x + t * (a i x - a i y)) := by fun_prop
      have he : ∀ᶠ t : ℝ in 𝓝 0, a i x + t * (a i x - a i y) < b i :=
        hc.continuousAt.eventually (gt_mem_nhds (by simpa using hlt))
      filter_upwards [he] with t ht
      simpa only [map_add, map_smul, map_sub, smul_eq_mul] using ht.le
  have hall : ∀ᶠ t : ℝ in 𝓝 0, ∀ i, a i (x + t • (x - y)) ≤ b i :=
    Filter.eventually_all.mpr hi
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hall
  refine ⟨δ / 2, by positivity, hball ?_⟩
  simp only [Metric.mem_ball, Real.dist_eq, sub_zero]
  rw [abs_of_pos (by positivity : 0 < δ / 2)]
  linarith
lemma activeConstraints_injOn_extremePoints
    (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ) :
    Set.InjOn (activeConstraints a b) ((cell a b).extremePoints ℝ) := by
  intro x hx y hy hactive
  obtain ⟨t, ht, hz⟩ := exists_extrapolate_mem a b hx.1 hactive
  have hsum : t + 1 ≠ 0 := by positivity
  have hseg : x ∈ openSegment ℝ y (x + t • (x - y)) := by
    apply mem_openSegment_iff_div.mpr
    refine ⟨t, 1, ht, by norm_num, ?_⟩
    simp only [smul_add, smul_sub, smul_smul]
    rw [show 1 / (t + 1) * t = t / (t + 1) by ring]
    calc
      _ = (1 / (t + 1) + t / (t + 1)) • x := by module
      _ = x := by rw [← add_div, add_comm 1 t, div_self hsum, one_smul]
  exact (hx.2 hy.1 hz hseg).symm
lemma finite_extremePoints_cell
    (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ) :
    ((cell a b).extremePoints ℝ).Finite := by
  classical
  exact Set.Finite.of_injOn (t := Set.univ) (Set.mapsTo_univ _ _)
    (activeConstraints_injOn_extremePoints a b) Set.finite_univ
noncomputable def polyhedronVertices (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ) : Finset E :=
  (finite_extremePoints_cell a b).toFinset
@[simp] lemma mem_polyhedronVertices
    (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ) (x : E) :
    x ∈ polyhedronVertices a b ↔ x ∈ (cell a b).extremePoints ℝ :=
  Set.Finite.mem_toFinset _
end CellVertices
section Arrangements
end Arrangements
section ArrangementTriangulation
end ArrangementTriangulation
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]
omit [FiniteDimensional ℝ V] in
lemma affine_decomp_apply (f : V →ᵃ[ℝ] ℝ) (x : V) : f x = f.linear x + f 0 := by
  exact congrFun f.decomp x
omit [FiniteDimensional ℝ V] in
lemma simplex_affine_indicator (s t : Finset V)
    (hi : AffineIndependent ℝ ((↑) : s → V)) :
    ∃ f : V →ᵃ[ℝ] ℝ, ∀ x ∈ s, f x = if x ∈ t then 1 else 0 := by
  classical
  obtain ⟨u, hsu, huind, hutop⟩ := exists_subset_affineIndependent_affineSpan_eq_top hi
  let B : AffineBasis u ℝ V := ⟨Subtype.val, huind, by simpa using hutop⟩
  let T : Finset u := t.preimage Subtype.val Subtype.val_injective.injOn
  refine ⟨∑ i ∈ T, B.coord i, ?_⟩
  intro x hx
  let i : u := ⟨x, hsu hx⟩
  have hsum (R : Finset u) : (∑ j ∈ R, B.coord j) (B i) =
      ∑ j ∈ R, B.coord j (B i) := by
    induction R using Finset.induction_on with
    | empty => simp
    | @insert j R hj ih => simp [Finset.sum_insert hj, ih]
  change (∑ j ∈ T, B.coord j) (B i) = _
  rw [hsum]
  simp [T, B.coord_apply, i]
omit [FiniteDimensional ℝ V] in
lemma simplex_face_supporting (s t : Finset V)
    (hi : AffineIndependent ℝ ((↑) : s → V)) (ht : t ⊆ s) :
    SupportingFace (convexHull ℝ (t : Set V)) (convexHull ℝ (s : Set V)) := by
  classical
  obtain ⟨f, hf⟩ := simplex_affine_indicator s t hi
  have hle : ∀ x ∈ (s : Set V), f.linear x ≤ 1-f 0 := by
    intro x hx
    have hh := hf x hx
    have hd := affine_decomp_apply f x
    split_ifs at hh <;> linarith
  refine ⟨f.linear, 1-f 0, linear_le_on_convexHull _ _ _ hle, ?_⟩
  rw [convexHull_inter_supporting _ f.linear (1-f 0) hle]
  congr 1
  ext x
  constructor
  · intro hx
    refine ⟨ht hx, ?_⟩
    have hh := hf x (ht hx)
    have hd := affine_decomp_apply f x
    change x ∈ t at hx
    rw [ite_eq_left hx] at hh
    change f.linear x = 1-f 0
    linarith
  · rintro ⟨hx, he⟩
    have hh := hf x hx
    have hd := affine_decomp_apply f x
    change f.linear x = 1-f 0 at he
    by_contra hxt
    change x ∉ t at hxt
    rw [ite_eq_right hxt] at hh
    linarith
end BassTrace.Sparse.Cuts
end OAI

end
section
namespace OAI
namespace BassTrace.Sparse.Cuts
section CanonicalCenters
end CanonicalCenters
section CanonicalFaceFamilies
end CanonicalFaceFamilies
end BassTrace.Sparse.Cuts
end OAI

end
section
namespace OAI.BassTrace.Sparse.Cuts.ActiveFlags
end OAI.BassTrace.Sparse.Cuts.ActiveFlags
end
section
namespace OAI.BassTrace.Sparse.Cuts.ActiveFlags
end OAI.BassTrace.Sparse.Cuts.ActiveFlags
end
section
namespace OAI.BassTrace.Sparse.Cuts.Intrinsic
end OAI.BassTrace.Sparse.Cuts.Intrinsic
end
section
namespace OAI
namespace BassTrace.Sparse.Cuts
section EmbeddingNaturality
end EmbeddingNaturality
section CanonicalCuts
end CanonicalCuts
section GeneralChains
end GeneralChains
section LinearCutNaturality
end LinearCutNaturality
end BassTrace.Sparse.Cuts
end OAI

end
section
namespace OAI
namespace BassTrace.Sparse.Cuts
section ArbitraryAmbientComplex
end ArbitraryAmbientComplex
section FiniteComplexPatches
end FiniteComplexPatches
end BassTrace.Sparse.Cuts
end OAI

end
section
namespace OAI
namespace BassTrace.Sparse.Cuts
section LocallyFiniteCuts
namespace LocalCutData
end LocalCutData
end LocallyFiniteCuts
end BassTrace.Sparse.Cuts
end OAI

end
section
namespace OAI
noncomputable section
namespace BassTrace
namespace Sparse
end Sparse
namespace Sparse.Cuts
section
end
section
open Set Finset
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
def geometricRestriction (K : Geometry.SimplicialComplex ℝ E) (P : Set E) :
    Geometry.SimplicialComplex ℝ E where
  faces := {s | s ∈ K.faces ∧ convexHull ℝ (s : Set E) ⊆ P}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨K.nonempty_of_mem_faces hs.1, ?_⟩
    intro t hts ht
    exact ⟨K.down_closed hs.1 hts ht, (convexHull_mono hts).trans hs.2⟩
  indep hs := K.indep hs.1
  inter_subset_convexHull hs ht := K.inter_subset_convexHull hs.1 ht.1
def IsMarked (K : Geometry.SimplicialComplex ℝ E) (P : Set E) : Prop :=
  ∀ x ∈ P, ∃ s ∈ K.faces, x ∈ convexHull ℝ (s : Set E) ∧
    convexHull ℝ (s : Set E) ⊆ P
lemma IsMarked.subset_space {K : Geometry.SimplicialComplex ℝ E} {P : Set E}
    (hP : IsMarked K P) : P ⊆ K.space := by
  intro x hx
  obtain ⟨s, hs, hxs, _⟩ := hP x hx
  exact K.convexHull_subset_space hs hxs
lemma IsMarked.restriction_space {K : Geometry.SimplicialComplex ℝ E} {P : Set E}
    (hP : IsMarked K P) : (geometricRestriction K P).space = P := by
  ext x
  constructor
  · intro hx
    obtain ⟨s, hs, hxs⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx
    exact hs.2 hxs
  · intro hx
    obtain ⟨s, hs, hxs, hsub⟩ := hP x hx
    exact Geometry.SimplicialComplex.mem_space_iff.mpr ⟨s, ⟨hs, hsub⟩, hxs⟩
lemma isMarked_space (K : Geometry.SimplicialComplex ℝ E) : IsMarked K K.space := by
  intro x hx
  obtain ⟨s, hs, hxs⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx
  exact ⟨s, hs, hxs, K.convexHull_subset_space hs⟩
lemma IsMarked.iUnion {K : Geometry.SimplicialComplex ℝ E} {I : Sort*}
    {P : I → Set E} (hP : ∀ i, IsMarked K (P i)) : IsMarked K (⋃ i, P i) := by
  intro x hx
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
  obtain ⟨s, hs, hxs, hsub⟩ := hP i x hxi
  exact ⟨s, hs, hxs, hsub.trans (Set.subset_iUnion P i)⟩
lemma IsMarked.union {K : Geometry.SimplicialComplex ℝ E} {P Q : Set E}
    (hP : IsMarked K P) (hQ : IsMarked K Q) : IsMarked K (P ∪ Q) := by
  intro x hx
  rcases hx with hx | hx
  · obtain ⟨s, hs, hxs, hsub⟩ := hP x hx
    exact ⟨s, hs, hxs, hsub.trans Set.subset_union_left⟩
  · obtain ⟨s, hs, hxs, hsub⟩ := hQ x hx
    exact ⟨s, hs, hxs, hsub.trans Set.subset_union_right⟩
lemma IsMarked.inter {K : Geometry.SimplicialComplex ℝ E} {P Q : Set E}
    (hP : IsMarked K P) (hQ : IsMarked K Q) : IsMarked K (P ∩ Q) := by
  classical
  intro x hx
  obtain ⟨s, hs, hxs, hsP⟩ := hP x hx.1
  obtain ⟨t, ht, hxt, htQ⟩ := hQ x hx.2
  have hxst : x ∈ convexHull ℝ ((s ∩ t : Finset E) : Set E) := by
    rw [Finset.coe_inter, ← K.convexHull_inter_convexHull hs ht]
    exact ⟨hxs, hxt⟩
  have hne : (s ∩ t).Nonempty :=
    Finset.coe_nonempty.mp (convexHull_nonempty_iff.mp ⟨x, hxst⟩)
  refine ⟨s ∩ t, K.down_closed hs Finset.inter_subset_left hne, hxst, ?_⟩
  exact subset_inter ((convexHull_mono Finset.inter_subset_left).trans hsP)
    ((convexHull_mono Finset.inter_subset_right).trans htQ)
lemma IsMarked.refinement {K L : Geometry.SimplicialComplex ℝ E} {P : Set E}
    (hP : IsMarked K P)
    (hcover : ∀ s ∈ K.faces, IsMarked L (convexHull ℝ (s : Set E))) :
    IsMarked L P := by
  intro x hx
  obtain ⟨s, hs, hxs, hsP⟩ := hP x hx
  obtain ⟨t, ht, hxt, hts⟩ := hcover s hs x hxs
  exact ⟨t, ht, hxt, hts.trans hsP⟩
lemma card_lt_of_generic_hyperplane {s t : Finset E}
    (ht : AffineIndependent ℝ ((↑) : t → E))
    (hst : (t : Set E) ⊆ convexHull ℝ (s : Set E))
    (f : E →ₗ[ℝ] ℝ) (b : ℝ)
    (heq : ∀ x ∈ t, f x = b) (hne : ∃ x ∈ s, f x ≠ b) :
    t.card < s.card := by
  apply ht.card_lt_card_of_affineSpan_lt_affineSpan
  have hle : affineSpan ℝ (t : Set E) ≤ affineSpan ℝ (s : Set E) := by
    apply affineSpan_le.mpr
    exact hst.trans (convexHull_subset_affineSpan (s : Set E))
  apply lt_of_le_of_ne hle
  intro h
  have he : (t : Set E).EqOn f.toAffineMap (AffineMap.const ℝ E b) := heq
  have he' := AffineMap.eqOn_affineSpan he
  obtain ⟨x, hx, hnx⟩ := hne
  apply hnx
  exact he' (by rw [h]; exact subset_affineSpan ℝ (s : Set E) hx)
end
section
end
section
open Set Finset
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
lemma RespectsSet.isMarked {K : Geometry.SimplicialComplex ℝ V} {P : Set V}
    (h : RespectsSet K P) : IsMarked K (K.space ∩ P) := by
  intro x hx
  have hx' : x ∈ (restrictComplex K P).space := by
    rw [restrictComplex_space_of_respects K P h]
    exact hx
  obtain ⟨s, hs, hxs⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx'
  refine ⟨s, hs.1, hxs, fun y hy => ⟨K.convexHull_subset_space hs.1 hy, ?_⟩⟩
  have he : (s : Set V) ∩ P = s := Set.inter_eq_left.mpr hs.2
  have hy' : y ∈ convexHull ℝ (s : Set V) ∩ P := by
    rw [h s hs.1, he]
    exact hy
  exact hy'.2
end
section
open Set Finset
section
namespace LocalCutData
end LocalCutData
end
open Set Finset
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
lemma exists_smallest_carrier (K : Geometry.SimplicialComplex ℝ V) {x : V}
    (hx : x ∈ K.space) :
    ∃ s ∈ K.faces, x ∈ convexHull ℝ (s : Set V) ∧
      ∀ t ∈ K.faces, x ∈ convexHull ℝ (t : Set V) → s ⊆ t := by
  classical
  let P : ℕ → Prop := fun n => ∃ s ∈ K.faces,
    x ∈ convexHull ℝ (s : Set V) ∧ s.card = n
  have hex : ∃ n, P n := by
    obtain ⟨s,hs,hxs⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx
    exact ⟨s.card,s,hs,hxs,rfl⟩
  obtain ⟨s,hs,hxs,hcard⟩ := Nat.find_spec hex
  refine ⟨s,hs,hxs,fun t ht hxt => ?_⟩
  have hxst : x ∈ convexHull ℝ ((s ∩ t : Finset V) : Set V) := by
    rw [Finset.coe_inter, ← K.convexHull_inter_convexHull hs ht]
    exact ⟨hxs,hxt⟩
  have hne : (s ∩ t).Nonempty :=
    Finset.coe_nonempty.mp (convexHull_nonempty_iff.mp ⟨x,hxst⟩)
  have hst := K.down_closed hs Finset.inter_subset_left hne
  have hmin : s.card ≤ (s ∩ t).card := by
    rw [hcard]
    exact Nat.find_min' hex ⟨s ∩ t,hst,hxst,rfl⟩
  have he : s ∩ t = s := Finset.eq_of_subset_of_card_le Finset.inter_subset_left hmin
  exact he ▸ Finset.inter_subset_right
namespace LocalCutData
end LocalCutData
end
open Set Finset
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
open scoped Classical
omit [NormedAddCommGroup V] [NormedSpace ℝ V] in
lemma coe_filter_mem (s : Finset V) (P : Set V) :
    ((s.filter (· ∈ P) : Finset V) : Set V) = (s : Set V) ∩ P := by
  ext x
  simp
lemma respectsSet_face {K : Geometry.SimplicialComplex ℝ V} {P : Set V}
    (hP : RespectsSet K P) {s : Finset V} (hs : s ∈ K.faces)
    (hne : (convexHull ℝ (s : Set V) ∩ P).Nonempty) :
    s.filter (· ∈ P) ∈ K.faces := by
  classical
  apply K.down_closed hs (Finset.filter_subset _ _)
  have hh := hP s hs
  rw [hh] at hne
  rw [← coe_filter_mem s P] at hne
  exact Finset.coe_nonempty.mp (convexHull_nonempty_iff.mp hne)
namespace LocalCutData
end LocalCutData
structure UniversalCuts (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] (J : Type*) where
  form : J → V →ₗ[ℝ] ℝ
  level : J → ℝ
  positive : ∀ j, 0 ≤ level j
  relevant : Finset V → Finset J
  vanish : ∀ s j, j ∉ relevant s →
    ∀ x ∈ convexHull ℝ (s : Set V), form j x = 0
namespace UniversalCuts
end UniversalCuts
end Sparse.Cuts
end BassTrace
end
end OAI

end
section
namespace OAI
noncomputable section
namespace BassTrace.Sparse.Cuts
open Set Finset
section
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
structure Subdivision (K : Geometry.SimplicialComplex ℝ V) where
  complex : Geometry.SimplicialComplex ℝ V
  space_eq : complex.space = K.space
  carrier : ∀ s ∈ complex.faces, ∃ t ∈ K.faces,
    convexHull ℝ (s : Set V) ⊆ convexHull ℝ (t : Set V)
  respects : ∀ s ∈ K.faces, RespectsSet complex (convexHull ℝ (s : Set V))
  finite : ∀ s ∈ K.faces,
    (restrictComplex complex (convexHull ℝ (s : Set V))).faces.Finite
lemma complex_respects_simplex (K : Geometry.SimplicialComplex ℝ V)
    {t : Finset V} (ht : t ∈ K.faces) : RespectsSet K (convexHull ℝ (t : Set V)) := by
  intro s hs
  have hv : (s : Set V) ∩ convexHull ℝ (t : Set V) = (s : Set V) ∩ t := by
    ext x
    constructor
    · rintro ⟨hx,hxt⟩
      have hxv : x ∈ K.vertices := K.down_closed hs (Finset.singleton_subset_iff.mpr hx)
        (Finset.singleton_nonempty _)
      exact ⟨hx,(K.vertex_mem_convexHull_iff hxv ht).mp hxt⟩
    · rintro ⟨hx,hxt⟩
      exact ⟨hx,subset_convexHull ℝ _ hxt⟩
  rw [hv,K.convexHull_inter_convexHull hs ht]
lemma complex_restrict_finite (K : Geometry.SimplicialComplex ℝ V)
    {t : Finset V} (ht : t ∈ K.faces) :
    (restrictComplex K (convexHull ℝ (t : Set V))).faces.Finite := by
  classical
  apply (t.powerset.finite_toSet).subset
  intro s hs
  apply Finset.mem_powerset.mpr
  apply (K.face_subset_face_iff hs.1 ht).mp
  exact convexHull_min hs.2 (convex_convexHull ℝ _)
namespace Subdivision
variable {K : Geometry.SimplicialComplex ℝ V}
def original (K : Geometry.SimplicialComplex ℝ V) : Subdivision K where
  complex := K
  space_eq := rfl
  carrier := fun s hs => ⟨s,hs,subset_rfl⟩
  respects := fun _ hs => complex_respects_simplex K hs
  finite := fun _ hs => complex_restrict_finite K hs
lemma marked (T : Subdivision K) {s : Finset V} (hs : s ∈ K.faces) :
    IsMarked T.complex (convexHull ℝ (s : Set V)) := by
  classical
  intro x hx
  have hxsp : x ∈ T.complex.space := T.space_eq.symm ▸ K.convexHull_subset_space hs hx
  obtain ⟨t,ht,hxt⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hxsp
  have he := T.respects s hs t ht
  have hxs : x ∈ convexHull ℝ ((t : Set V) ∩ convexHull ℝ (s : Set V)) := by
    rw [← he]
    exact ⟨hxt,hx⟩
  let u := t.filter (· ∈ convexHull ℝ (s : Set V))
  have hu : u ∈ T.complex.faces := respectsSet_face (T.respects s hs) ht ⟨x,hxt,hx⟩
  refine ⟨u,hu,?_,?_⟩
  · simpa only [u,coe_filter_mem] using hxs
  · apply convexHull_min
    · intro y hy
      exact (Finset.mem_filter.mp hy).2
    · exact convex_convexHull ℝ _
end Subdivision
namespace UniversalCuts
end UniversalCuts
structure SubdivisionFamily (X : Type*) [TopologicalSpace X]
    (K : Geometry.SimplicialComplex ℝ V) where
  val : X → Subdivision K
  localConstancy : ∀ s ∈ K.faces, IsLocallyConstant
    (fun x => (restrictComplex (val x).complex (convexHull ℝ (s : Set V))).faces)
namespace UniversalCuts
end UniversalCuts
end
section
variable {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace X] [CompactSpace X]
variable {K : Geometry.SimplicialComplex ℝ V}
namespace SubdivisionFamily
lemma finite_faces_on (T : SubdivisionFamily X K) (s : Finset V) (hs : s ∈ K.faces) :
    (⋃ x, (restrictComplex (T.val x).complex (convexHull ℝ (s : Set V))).faces).Finite := by
  let f := fun x => (restrictComplex (T.val x).complex (convexHull ℝ (s : Set V))).faces
  have hf : (Set.range f).Finite := (T.localConstancy s hs).range_finite
  have hh : (⋃ F ∈ Set.range f, F).Finite := hf.biUnion (by
    rintro F ⟨x,rfl⟩
    exact (T.val x).finite s hs)
  apply hh.subset
  intro u hu
  obtain ⟨x,hx⟩ := Set.mem_iUnion.mp hu
  exact Set.mem_iUnion₂.mpr ⟨f x,⟨x,rfl⟩,hx⟩
lemma countable_faces (T : SubdivisionFamily X K) (hK : K.faces.Countable) :
    (⋃ x, (T.val x).complex.faces).Countable := by
  have hh : (⋃ s ∈ K.faces, ⋃ x,
      (restrictComplex (T.val x).complex (convexHull ℝ (s : Set V))).faces).Countable :=
    hK.biUnion (fun s hs => (T.finite_faces_on s hs).countable)
  apply hh.mono
  intro u hu
  obtain ⟨x,hxu⟩ := Set.mem_iUnion.mp hu
  obtain ⟨s,hs,hus⟩ := (T.val x).carrier u hxu
  exact Set.mem_iUnion₂.mpr ⟨s,hs,Set.mem_iUnion.mpr
    ⟨x,hxu,(subset_convexHull ℝ _).trans hus⟩⟩
lemma countable_vertices (T : SubdivisionFamily X K) (hK : K.faces.Countable) :
    (⋃ x, (T.val x).complex.vertices).Countable := by
  have hh : (⋃ s ∈ (⋃ x, (T.val x).complex.faces), (s : Set V)).Countable :=
    (T.countable_faces hK).biUnion (fun s _ => s.countable_toSet)
  apply hh.mono
  intro y hy
  obtain ⟨x,hxy⟩ := Set.mem_iUnion.mp hy
  exact Set.mem_iUnion₂.mpr ⟨{y},Set.mem_iUnion.mpr ⟨x,hxy⟩,by simp⟩
end SubdivisionFamily
end
section
variable {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace X]
variable {K : Geometry.SimplicialComplex ℝ V}
def Refines (L K : Geometry.SimplicialComplex ℝ V) : Prop :=
  ∃ S : Subdivision K, S.complex = L
lemma refines_self (K : Geometry.SimplicialComplex ℝ V) : Refines K K :=
  ⟨Subdivision.original K,rfl⟩
structure MarkedFamily (T : SubdivisionFamily X K) where
  val : X → Set V
  marked : ∀ x, IsMarked (T.val x).complex (val x)
  localConstancy : ∀ s ∈ K.faces, IsLocallyConstant (fun x =>
    (restrictComplex (geometricRestriction (T.val x).complex (val x))
      (convexHull ℝ (s : Set V))).faces)
def ComponentDiameter (ρ : V → V → ℝ) (P : Set V) (R : ℝ) : Prop :=
  ∀ C : Set V, IsPreconnected C → C ⊆ P →
    ∀ p ∈ C, ∀ q ∈ C, ρ p q ≤ R
def DimensionDrop (T S : Geometry.SimplicialComplex ℝ V) (P Z : Set V) : Prop :=
  ∀ F ∈ T.faces, convexHull ℝ (F : Set V) ⊆ P →
    ∀ E ∈ S.faces, convexHull ℝ (E : Set V) ⊆ convexHull ℝ (F : Set V) ∩ Z →
      E.card < F.card
structure AdmissibleStep (ρ : V → V → ℝ) (R : ℝ)
    (T : SubdivisionFamily X K) (P : MarkedFamily T) where
  next : SubdivisionFamily X K
  finer : ∀ x, Refines (next.val x).complex (T.val x).complex
  oldMarked : ∀ x, IsMarked (next.val x).complex (P.val x)
  zero : MarkedFamily next
  subset : ∀ x, zero.val x ⊆ P.val x
  dimensionDrop : ∀ x, DimensionDrop (T.val x).complex (next.val x).complex (P.val x) (zero.val x)
  diameter : ∀ x, ComponentDiameter ρ (P.val x \ zero.val x) (2*R)
end
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
namespace Subdivision
variable {K : Geometry.SimplicialComplex ℝ V} (S : Subdivision K)
lemma preserves_marked {P : Set V} (hP : IsMarked K P) : IsMarked S.complex P :=
  hP.refinement (fun _ hs => S.marked hs)
lemma carrier_in {P : Set V} (hP : RespectsSet K P) {s : Finset V}
    (hs : s ∈ S.complex.faces) (hsp : (s : Set V) ⊆ P) :
    ∃ t ∈ K.faces, (t : Set V) ⊆ P ∧ convexHull ℝ (s : Set V) ⊆ convexHull ℝ (t : Set V) := by
  classical
  obtain ⟨t,ht,hst⟩ := S.carrier s hs
  have hv := Set.subset_inter ((subset_convexHull ℝ _).trans hst) hsp
  have hne := (S.complex.nonempty_of_mem_faces hs).to_set.mono hv
  refine ⟨t.filter (· ∈ P),respectsSet_face hP ht hne,?_,?_⟩
  · intro x hx
    exact (Finset.mem_filter.mp hx).2
  · apply convexHull_min _ (convex_convexHull ℝ _)
    simpa only [coe_filter_mem] using (hP t ht ▸ hv)
lemma preserves_respects {P : Set V} (hP : RespectsSet K P) : RespectsSet S.complex P := by
  classical
  intro s hs
  obtain ⟨t,ht,hst⟩ := S.carrier s hs
  by_cases hh : (convexHull ℝ (t : Set V) ∩ P).Nonempty
  · let u := t.filter (· ∈ P)
    have hu : u ∈ K.faces := respectsSet_face hP ht hh
    have he : convexHull ℝ (u : Set V) = convexHull ℝ (t : Set V) ∩ P := by
      simpa only [u,coe_filter_mem] using (hP t ht).symm
    have htrace := S.respects u hu s hs
    have hc : convexHull ℝ (s : Set V) ∩ convexHull ℝ (u : Set V) =
        convexHull ℝ (s : Set V) ∩ P := by
      rw [he,← Set.inter_assoc,Set.inter_eq_left.mpr hst]
    have hv : (s : Set V) ∩ convexHull ℝ (u : Set V) = (s : Set V) ∩ P := by
      rw [he,← Set.inter_assoc,Set.inter_eq_left.mpr ((subset_convexHull ℝ _).trans hst)]
    simpa only [hc,hv] using htrace
  · have hc : convexHull ℝ (s : Set V) ∩ P = ∅ :=
      Set.eq_empty_iff_forall_notMem.mpr (fun x hx => hh ⟨x,hst hx.1,hx.2⟩)
    have hv : (s : Set V) ∩ P = ∅ := Set.eq_empty_iff_forall_notMem.mpr
      (fun x hx => hh ⟨x,hst (subset_convexHull ℝ _ hx.1),hx.2⟩)
    rw [hc,hv,convexHull_empty]
lemma finite_on_respected {P : Set V} (hP : RespectsSet K P)
    (hf : (restrictComplex K P).faces.Finite) : (restrictComplex S.complex P).faces.Finite := by
  have hh : (⋃ t ∈ (restrictComplex K P).faces,
      (restrictComplex S.complex (convexHull ℝ (t : Set V))).faces).Finite :=
    hf.biUnion (fun t ht => S.finite t ht.1)
  apply hh.subset
  intro s hs
  obtain ⟨t,ht,htP,hst⟩ := S.carrier_in hP hs.1 hs.2
  exact Set.mem_iUnion₂.mpr ⟨t,⟨ht,htP⟩,hs.1,(subset_convexHull ℝ _).trans hst⟩
def trans {L : Geometry.SimplicialComplex ℝ V} (T : Subdivision L)
    (h : T.complex = K) : Subdivision L where
  complex := S.complex
  space_eq := S.space_eq.trans (h ▸ T.space_eq)
  carrier := by
    intro s hs
    obtain ⟨t,ht,hst⟩ := S.carrier s hs
    obtain ⟨u,hu,htu⟩ := T.carrier t (h.symm ▸ ht)
    exact ⟨u,hu,hst.trans htu⟩
  respects := fun s hs => S.preserves_respects (h ▸ T.respects s hs)
  finite := fun s hs => S.finite_on_respected (h ▸ T.respects s hs) (h ▸ T.finite s hs)
end Subdivision
lemma Refines.trans {K L M : Geometry.SimplicialComplex ℝ V}
    (hML : Refines M L) (hLK : Refines L K) : Refines M K := by
  obtain ⟨S,rfl⟩ := hML
  obtain ⟨T,hT⟩ := hLK
  exact ⟨S.trans T hT,rfl⟩
lemma Refines.preserves_marked {K L : Geometry.SimplicialComplex ℝ V}
    (h : Refines L K) {P : Set V} (hP : IsMarked K P) : IsMarked L P := by
  obtain ⟨S,rfl⟩ := h
  exact S.preserves_marked hP
end BassTrace.Sparse.Cuts
end
end OAI

end
section
namespace OAI
noncomputable section
namespace BassTrace.Sparse.Cuts
section
open Set Finset
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
lemma Subdivision.carrier_marked {K : Geometry.SimplicialComplex ℝ V}
    (S : Subdivision K) {P : Set V} (hP : IsMarked K P) {E : Finset V}
    (hE : E ∈ S.complex.faces) (hEP : convexHull ℝ (E : Set V) ⊆ P) :
    ∃ F ∈ K.faces, convexHull ℝ (F : Set V) ⊆ P ∧
      convexHull ℝ (E : Set V) ⊆ convexHull ℝ (F : Set V) := by
  classical
  let c : ℝ := (E.card : ℝ)⁻¹
  have hc : 0 < c := inv_pos.mpr (Nat.cast_pos.mpr
    (S.complex.nonempty_of_mem_faces hE).card_pos)
  have hsum : ∑ x ∈ E, c = 1 := by
    simp only [Finset.sum_const, nsmul_eq_mul]
    exact mul_inv_cancel₀ (ne_of_gt (inv_pos.mp hc))
  have hb := Sparse.sum_weights_mem_convexHull E (fun _ _ => hc.le) hsum
  obtain ⟨F,hF,hbF,hFP⟩ := hP _ (hEP hb)
  let A := E.filter (· ∈ convexHull ℝ (F : Set V))
  have hbA : (∑ x ∈ E, c • x) ∈ convexHull ℝ (A : Set V) := by
    simpa only [A,coe_filter_mem] using (S.respects F hF E hE ▸
      (show (∑ x ∈ E, c • x) ∈ convexHull ℝ (E : Set V) ∩
        convexHull ℝ (F : Set V) from ⟨hb,hbF⟩))
  have hEA := Sparse.positiveCombination_carrier (S.complex.indep hE)
    (Finset.filter_subset _ _) (fun _ => c) (fun _ _ => hc) hsum hbA
  refine ⟨F,hF,hFP,convexHull_min ?_ (convex_convexHull ℝ _)⟩
  intro x hx
  exact (Finset.mem_filter.mp (hEA hx)).2
structure PointFiltration (K : Geometry.SimplicialComplex ℝ V) (n : ℕ) where
  T : ℕ → Geometry.SimplicialComplex ℝ V
  Z : ℕ → Set V
  top : T n = K
  top_space : Z n = K.space
  marked : ∀ i, i ≤ n → IsMarked (T i) (Z i)
  finer : ∀ i, i < n → Refines (T i) (T (i+1))
  nested : ∀ i, i < n → Z i ⊆ Z (i+1)
  drop : ∀ i, i < n → DimensionDrop (T (i+1)) (T i) (Z (i+1)) (Z i)
namespace PointFiltration
variable {K : Geometry.SimplicialComplex ℝ V} {n : ℕ} (Q : PointFiltration K n)
lemma refines {j i : ℕ} (hji : j ≤ i) (hin : i ≤ n) : Refines (Q.T j) (Q.T i) := by
  induction i, hji using Nat.le_induction with
  | base => exact refines_self _
  | succ i hji ih => exact ih (by omega) |>.trans (Q.finer i (by omega))
lemma subset {j i : ℕ} (hji : j ≤ i) (hin : i ≤ n) : Q.Z j ⊆ Q.Z i := by
  induction i, hji using Nat.le_induction with
  | base => exact subset_rfl
  | succ i hji ih => exact (ih (by omega)).trans (Q.nested i (by omega))
lemma iterated_drop {j i : ℕ} (hji : j ≤ i) (hin : i ≤ n)
    {F : Finset V} (hF : F ∈ (Q.T i).faces) (_hFZ : convexHull ℝ (F : Set V) ⊆ Q.Z i)
    {E : Finset V} (hE : E ∈ (Q.T j).faces)
    (hEF : convexHull ℝ (E : Set V) ⊆ convexHull ℝ (F : Set V) ∩ Q.Z j) :
    E.card + (i-j) ≤ F.card := by
  classical
  generalize hd : i-j = d
  induction d using Nat.strong_induction_on generalizing j E with
  | h d ih =>
    by_cases hji' : j = i
    · subst j
      have hcard := (Q.T i).indep hE |>.card_le_card_of_subset_affineSpan
        ((subset_convexHull ℝ _).trans ((hEF.trans Set.inter_subset_left).trans
          (convexHull_subset_affineSpan _)))
      have : d = 0 := by simpa using hd.symm
      simpa [this] using hcard
    · have hj : j < i := by omega
      obtain ⟨S,hS⟩ := Q.finer j (by omega)
      obtain ⟨W,hW⟩ := Q.refines (show j+1 ≤ i by omega) hin
      have hm : IsMarked (Q.T (j+1)) (convexHull ℝ (F : Set V) ∩ Q.Z (j+1)) :=
        (hW ▸ W.marked hF).inter (Q.marked (j+1) (by omega))
      have hEP : convexHull ℝ (E : Set V) ⊆
          convexHull ℝ (F : Set V) ∩ Q.Z (j+1) :=
        Set.subset_inter (hEF.trans Set.inter_subset_left)
          ((hEF.trans Set.inter_subset_right).trans (Q.nested j (by omega)))
      obtain ⟨U,hU,hUP,hEU⟩ := S.carrier_marked hm (hS.symm ▸ hE) hEP
      have hcard := Q.drop j (by omega) U hU (hUP.trans Set.inter_subset_right)
        E hE (Set.subset_inter hEU (hEF.trans Set.inter_subset_right))
      have hrec := ih (i-(j+1)) (by omega) (show j+1 ≤ i by omega) hU hUP rfl
      omega
lemma dimension_bound (hK : ∀ F ∈ K.faces, F.card ≤ n+1) {i : ℕ} (hi : i ≤ n)
    {E : Finset V} (hE : E ∈ (Q.T i).faces) (hEZ : convexHull ℝ (E : Set V) ⊆ Q.Z i) :
    E.card ≤ i+1 := by
  obtain ⟨S,hS⟩ := Q.refines hi le_rfl
  obtain ⟨F,hF,hEF⟩ := S.carrier E (hS.symm ▸ hE)
  have hFZ : convexHull ℝ (F : Set V) ⊆ Q.Z n := by
    rw [Q.top_space]
    exact K.convexHull_subset_space (Q.top ▸ hF)
  have hb := Q.iterated_drop hi le_rfl hF hFZ hE (Set.subset_inter hEF hEZ)
  have hc := hK F (Q.top ▸ hF)
  omega
lemma card_lower_of_mem_zero {i : ℕ} (hi : i ≤ n) {z : V} (hz : z ∈ Q.Z 0)
    {F : Finset V} (hF : F ∈ (Q.T i).faces) (hFZ : convexHull ℝ (F : Set V) ⊆ Q.Z i)
    (hzF : z ∈ convexHull ℝ (F : Set V)) : i+1 ≤ F.card := by
  obtain ⟨S,hS⟩ := Q.refines (Nat.zero_le i) hi
  have hm : IsMarked (Q.T 0) (convexHull ℝ (F : Set V) ∩ Q.Z 0) :=
    (hS ▸ S.marked hF).inter (Q.marked 0 (Nat.zero_le n))
  obtain ⟨E,hE,_,hEF⟩ := hm z ⟨hzF,hz⟩
  have hb := Q.iterated_drop (Nat.zero_le i) hi hF hFZ hE hEF
  have hc := (Q.T 0).nonempty_of_mem_faces hE |>.card_pos
  omega
end PointFiltration
end
section
open Set Finset
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {K S T : Geometry.SimplicialComplex ℝ V}
lemma IsMarked.contains_of_positive_barycenter {P : Set V} (hP : IsMarked K P)
    {F : Finset V} (hF : F ∈ K.faces) (w : V → ℝ)
    (hw : ∀ x ∈ F, 0 < w x) (hws : ∑ x ∈ F, w x = 1)
    (hp : (∑ x ∈ F, w x • x) ∈ P) : convexHull ℝ (F : Set V) ⊆ P := by
  obtain ⟨E,hE,hpE,hEP⟩ := hP _ hp
  exact (convexHull_mono (Sparse.simplex_contains_positivePoint K hF hE w hw hws hpE)).trans hEP
lemma IsMarked.face_in_union {I : Type*} {P : I → Set V}
    (hP : ∀ i, IsMarked K (P i)) {F : Finset V} (hF : F ∈ K.faces)
    (hFU : convexHull ℝ (F : Set V) ⊆ ⋃ i, P i) :
    ∃ i, convexHull ℝ (F : Set V) ⊆ P i := by
  let c : ℝ := (F.card : ℝ)⁻¹
  have hc : 0 < c := inv_pos.mpr (Nat.cast_pos.mpr (K.nonempty_of_mem_faces hF).card_pos)
  have hs : ∑ x ∈ F, c = 1 := by simp [c,ne_of_gt (Nat.cast_pos.mpr
    (K.nonempty_of_mem_faces hF).card_pos : (0 : ℝ) < F.card)]
  obtain ⟨i,hi⟩ := Set.mem_iUnion.mp (hFU (Sparse.sum_weights_mem_convexHull F
    (fun _ _ => hc.le) hs))
  exact ⟨i,(hP i).contains_of_positive_barycenter hF _ (fun _ _ => hc) hs hi⟩
lemma DimensionDrop.refine {P Z : Set V} (h : DimensionDrop T S P Z)
    (hZ : IsMarked S Z) {L : Geometry.SimplicialComplex ℝ V}
    (hL : Refines L S) (hST : Refines S T) : DimensionDrop T L P Z := by
  obtain ⟨A,rfl⟩ := hL
  obtain ⟨B,rfl⟩ := hST
  intro F hF hFP E hE hEF
  have hm : IsMarked B.complex (convexHull ℝ (F : Set V) ∩ Z) :=
    (B.marked hF).inter hZ
  obtain ⟨C,hC,hCP,hEC⟩ := A.carrier_marked hm hE hEF
  have hcard : E.card ≤ C.card := (A.complex.indep hE).card_le_card_of_subset_affineSpan
    ((subset_convexHull ℝ _).trans (hEC.trans (convexHull_subset_affineSpan _)))
  exact lt_of_le_of_lt hcard (h F hF hFP C hC hCP)
end
section
open Set Finset
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {K : Geometry.SimplicialComplex ℝ V}
lemma IsMarked.inter_iInter {I : Type*} {P : Set V} {Q : I → Set V}
    (hP : IsMarked K P) (hQ : ∀ i, IsMarked K (K.space ∩ Q i)) :
    IsMarked K (P ∩ ⋂ i, Q i) := by
  intro x hx
  obtain ⟨F,hF,hxF,hmin⟩ := exists_smallest_carrier K (hP.subset_space hx.1)
  obtain ⟨E,hE,hxE,hEP⟩ := hP _ hx.1
  refine ⟨F,hF,hxF,fun y hy => ⟨hEP (convexHull_mono (hmin E hE hxE) hy),?_⟩⟩
  apply Set.mem_iInter.mpr
  intro i
  obtain ⟨E,hE,hxE,hEQ⟩ := hQ i _ ⟨hP.subset_space hx.1,Set.mem_iInter.mp hx.2 i⟩
  exact (hEQ (convexHull_mono (hmin E hE hxE) hy)).2
namespace UniversalCuts
variable {J : Type*} (d : UniversalCuts V J)
def closedPatch (P : Set V) (A : Finset J) : Set V :=
  P ∩ {x | ∀ j ∈ A, d.form j x ≤ d.level j}
def spherePatch (P : Set V) (A : Finset J) : Set V :=
  d.closedPatch P A ∩ {x | ∃ j ∈ A, d.form j x = d.level j}
end UniversalCuts
end
open Set Finset
open scoped Classical Topology
variable {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace X] {K : Geometry.SimplicialComplex ℝ V}
namespace MarkedFamily
lemma set_localConstancy {T : SubdivisionFamily X K} (P : MarkedFamily T)
    (s : Finset V) (hs : s ∈ K.faces) :
    IsLocallyConstant (fun x => P.val x ∩ convexHull ℝ (s : Set V)) := by
  let U : Set (Finset V) → Set V := fun A => ⋃ t ∈ A, convexHull ℝ (t : Set V)
  have he (x : X) : P.val x ∩ convexHull ℝ (s : Set V) = U
      ((restrictComplex (geometricRestriction (T.val x).complex (P.val x))
        (convexHull ℝ (s : Set V))).faces) := by
    have hh := restrictComplex_space_of_respects
      (geometricRestriction (T.val x).complex (P.val x)) (convexHull ℝ (s : Set V))
      (fun t ht => (T.val x).respects s hs t ht.1)
    rw [(P.marked x).restriction_space] at hh
    exact hh.symm
  simp_rw [he]
  exact (P.localConstancy s hs).comp U
def ofSets (T : SubdivisionFamily X K) (P : X → Set V)
    (hP : ∀ x, IsMarked (T.val x).complex (P x))
    (hLC : ∀ s ∈ K.faces, IsLocallyConstant (fun x => P x ∩ convexHull ℝ (s : Set V))) :
    MarkedFamily T where
  val := P
  marked := hP
  localConstancy := by
    intro s hs
    let F : Set (Finset V) → Set V → Set (Finset V) :=
      fun A Q => {t | t ∈ A ∧ convexHull ℝ (t : Set V) ⊆ Q}
    have he (x : X) :
        (restrictComplex (geometricRestriction (T.val x).complex (P x))
          (convexHull ℝ (s : Set V))).faces = F
        ((restrictComplex (T.val x).complex (convexHull ℝ (s : Set V))).faces)
        (P x ∩ convexHull ℝ (s : Set V)) := by
      ext t
      change ((t ∈ (T.val x).complex.faces ∧ convexHull ℝ (t : Set V) ⊆ P x) ∧
        (t : Set V) ⊆ convexHull ℝ (s : Set V)) ↔
        ((t ∈ (T.val x).complex.faces ∧ (t : Set V) ⊆ convexHull ℝ (s : Set V)) ∧
          convexHull ℝ (t : Set V) ⊆ P x ∩ convexHull ℝ (s : Set V))
      constructor
      · rintro ⟨⟨ht,hP⟩,hst⟩
        exact ⟨⟨ht,hst⟩,Set.subset_inter hP (convexHull_min hst (convex_convexHull _ _))⟩
      · rintro ⟨⟨ht,hst⟩,hP⟩
        exact ⟨⟨ht,fun _ hy => (hP hy).1⟩,hst⟩
    simp_rw [he]
    exact (T.localConstancy s hs).comp₂ (hLC s hs) F
def refine {T S : SubdivisionFamily X K} (P : MarkedFamily T)
    (hS : ∀ x, Refines (S.val x).complex (T.val x).complex) : MarkedFamily S :=
  ofSets S P.val (fun x => by
    obtain ⟨W,hW⟩ := hS x
    rw [← hW]
    exact W.preserves_marked (P.marked x)) P.set_localConstancy
omit [NormedAddCommGroup V] [NormedSpace ℝ V] in
lemma locallyConstant_active_union {I : Type*} (A : I → Set V) (B : I → Set X)
    (hB : ∀ i, IsClopen (B i)) (Q : Set V)
    (hfinite : {i | (A i ∩ Q).Nonempty}.Finite) :
    IsLocallyConstant (fun x => (⋃ i, if x ∈ B i then A i else ∅) ∩ Q) := by
  classical
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro x
  have hp (i : I) : ∀ᶠ y in 𝓝 x, (y ∈ B i ↔ x ∈ B i) := by
    by_cases hx : x ∈ B i
    · exact Filter.Eventually.mono ((hB i).2.mem_nhds hx) (by intro y hy; exact ⟨fun _ => hx, fun _ => hy⟩)
    · exact Filter.Eventually.mono ((hB i).1.isOpen_compl.mem_nhds hx)
        (by intro y hy; exact ⟨fun h => False.elim (hy h), fun h => False.elim (hx h)⟩)
  filter_upwards [hfinite.eventually_all.mpr (fun i _ => hp i)] with y hy
  ext p
  simp only [Set.mem_inter_iff,Set.mem_iUnion]
  constructor
  · rintro ⟨⟨i,hi⟩,hpQ⟩
    by_cases hyB : y ∈ B i
    · simp only [hyB,ite_true] at hi
      have hxB := (hy i ⟨p,hi,hpQ⟩).mp hyB
      exact ⟨⟨i,by simpa only [hxB,ite_true] using hi⟩,hpQ⟩
    · simp only [hyB,ite_false,Set.mem_empty_iff_false] at hi
  · rintro ⟨⟨i,hi⟩,hpQ⟩
    by_cases hxB : x ∈ B i
    · simp only [hxB,ite_true] at hi
      have hyB := (hy i ⟨p,hi,hpQ⟩).mpr hxB
      exact ⟨⟨i,by simpa only [hyB,ite_true] using hi⟩,hpQ⟩
    · simp only [hxB,ite_false,Set.mem_empty_iff_false] at hi
end MarkedFamily
end BassTrace.Sparse.Cuts
end
end OAI

end
section
namespace OAI
noncomputable section
namespace BassTrace.Sparse.Cuts
section
open Set Finset
open scoped Classical Topology
variable {V X I : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace X] {K : Geometry.SimplicialComplex ℝ V}
def activatedUnion (A : I → Set V) (B : I → Set X) (x : X) : Set V :=
  ⋃ i, if x ∈ B i then A i else ∅
def replacementSet (P Z : Set V) (U S : I → Set V) (B : I → Set X) (x : X) : Set V :=
  (Z \ activatedUnion U B x) ∪ (P ∩ activatedUnion S B x)
omit [TopologicalSpace X] in
lemma activatedUnion_marked (T : Geometry.SimplicialComplex ℝ V)
    (A : I → Set V) (hA : ∀ i, IsMarked T (A i)) (B : I → Set X) (x : X) :
    IsMarked T (activatedUnion A B x) := by
  apply IsMarked.iUnion
  intro i
  split_ifs
  · exact hA i
  · intro p hp
    exact hp.elim
omit [TopologicalSpace X] in
lemma difference_activatedUnion_marked (T : Geometry.SimplicialComplex ℝ V)
    {Z : Set V} (hZ : IsMarked T Z) (U : I → Set V)
    (hU : ∀ i, IsMarked T (T.space \ U i)) (B : I → Set X) (x : X) :
    IsMarked T (Z \ activatedUnion U B x) := by
  have hh := hZ.inter_iInter (I := I)
    (Q := fun i => if x ∈ B i then (U i)ᶜ else Set.univ) (by
      intro i
      split_ifs
      · exact hU i
      · simpa only [Set.inter_univ] using isMarked_space T)
  convert hh using 1
  ext p
  simp only [Set.mem_sdiff,activatedUnion,Set.mem_iUnion,Set.mem_inter_iff,
    Set.mem_iInter]
  constructor
  · rintro ⟨hp,hout⟩
    refine ⟨hp,fun i => ?_⟩
    by_cases hi : x ∈ B i
    · simp only [hi,ite_true,Set.mem_compl_iff]
      intro hpi
      exact hout ⟨i,by simpa only [hi,ite_true] using hpi⟩
    · simp only [hi,ite_false,Set.mem_univ]
  · rintro ⟨hp,hout⟩
    refine ⟨hp,fun ⟨i,hi⟩ => ?_⟩
    have hoi := hout i
    by_cases hxi : x ∈ B i
    · simp only [hxi,ite_true] at hi hoi
      exact hoi hi
    · simp only [hxi,ite_false,Set.mem_empty_iff_false] at hi
omit [TopologicalSpace X] in
lemma replacementSet_marked (T : Geometry.SimplicialComplex ℝ V)
    {P Z : Set V} (hP : IsMarked T P) (hZ : IsMarked T Z)
    (U S : I → Set V) (hU : ∀ i, IsMarked T (T.space \ U i))
    (hS : ∀ i, IsMarked T (S i)) (B : I → Set X) (x : X) :
    IsMarked T (replacementSet P Z U S B x) := by
  exact (difference_activatedUnion_marked T hZ U hU B x).union
    (hP.inter (activatedUnion_marked T S hS B x))
omit [NormedAddCommGroup V] [NormedSpace ℝ V] [TopologicalSpace X] in
lemma replacementSet_subset {P Z : Set V} (hZ : Z ⊆ P)
    (U S : I → Set V) (B : I → Set X) (x : X) :
    replacementSet P Z U S B x ⊆ P := by
  intro p hp
  exact hp.elim (fun h => hZ h.1) (fun h => h.1)
namespace MarkedFamily
def replacement {T : SubdivisionFamily X K} (P Z : MarkedFamily T)
    (U S : I → Set V) (B : I → Set X) (hB : ∀ i, IsClopen (B i))
    (hU : ∀ x i, IsMarked (T.val x).complex ((T.val x).complex.space \ U i))
    (hS : ∀ x i, IsMarked (T.val x).complex (S i))
    (hfinU : ∀ s ∈ K.faces, {i | (U i ∩ convexHull ℝ (s : Set V)).Nonempty}.Finite)
    (hfinS : ∀ s ∈ K.faces, {i | (S i ∩ convexHull ℝ (s : Set V)).Nonempty}.Finite) :
    MarkedFamily T :=
  ofSets T (fun x => replacementSet (P.val x) (Z.val x) U S B x)
    (fun x => replacementSet_marked (T.val x).complex (P.marked x) (Z.marked x)
      U S (hU x) (hS x) B x) (by
    intro s hs
    let Q := convexHull ℝ (s : Set V)
    have hZ := Z.set_localConstancy s hs
    have hP := P.set_localConstancy s hs
    have hU' := locallyConstant_active_union U B hB Q (hfinU s hs)
    have hS' := locallyConstant_active_union S B hB Q (hfinS s hs)
    have hh := (hZ.comp₂ hU' Set.diff).comp₂ (hP.comp₂ hS' Set.inter) Set.union
    convert hh using 1
    ext x p
    change (((p ∈ Z.val x ∧ p ∉ activatedUnion U B x) ∨
      (p ∈ P.val x ∧ p ∈ activatedUnion S B x)) ∧ p ∈ Q) ↔
      (((p ∈ Z.val x ∧ p ∈ Q) ∧ ¬ (p ∈ activatedUnion U B x ∧ p ∈ Q)) ∨
       ((p ∈ P.val x ∧ p ∈ Q) ∧ (p ∈ activatedUnion S B x ∧ p ∈ Q)))
    tauto)
end MarkedFamily
end
open Set Finset
open scoped Topology
variable {V X I J : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace X]
variable {K : Geometry.SimplicialComplex ℝ V}
lemma sphereUnion_componentDiameter (ρ : V → V → ℝ) (P : Set V)
    (hP : P ⊆ K.space) (f : I → V → ℝ) (t R : ℝ)
    (hcont : ∀ i, ContinuousOn (f i) K.space)
    (hcover : ∀ p ∈ K.space, ∃ i, f i p < t)
    (htriangle : ∀ i p, p ∈ K.space → ∀ q, q ∈ K.space → ρ p q ≤ f i p + f i q)
    (ht : t ≤ R) :
    ComponentDiameter ρ (P \ (P ∩ ⋃ i, {p | f i p = t})) (2*R) := by
  intro C hC hCP p hp q hq
  have hCK : C ⊆ K.space := fun y hy => hP (hCP hy).1
  obtain ⟨i,hip⟩ := hcover p (hCK hp)
  have hq' : f i q < t := by
    by_contra hh
    obtain ⟨z,hz,hzt⟩ := hC.intermediate_value hp hq ((hcont i).mono hCK)
      ⟨hip.le,le_of_not_gt hh⟩
    exact (hCP hz).2 ⟨(hCP hz).1,Set.mem_iUnion.mpr ⟨i,hzt⟩⟩
  exact (htriangle i p (hCK hp) q (hCK hq)).trans (by linarith)
namespace UniversalCuts
end UniversalCuts
end BassTrace.Sparse.Cuts
end
end OAI

end
section
namespace OAI
namespace BassTrace.Sparse
open Finset
structure FinProbability (Y : Type*) where
  coeff : Y →₀ ℝ
  nonneg : ∀ y, 0 ≤ coeff y
  total : coeff.sum (fun _ r => r) = 1
namespace FinProbability
variable {Y : Type*}
theorem ext_coeff {p q : FinProbability Y} (h : p.coeff = q.coeff) : p = q := by
  cases p
  cases q
  cases h
  rfl
noncomputable def expectation (p : FinProbability Y) (f : Y → ℝ) : ℝ :=
  p.coeff.sum fun y r => r * f y
lemma expectation_const (p : FinProbability Y) (c : ℝ) :
    p.expectation (fun _ => c) = c := by
  classical
  unfold expectation Finsupp.sum at *
  rw [← Finset.sum_mul, show (∑ y ∈ p.coeff.support, p.coeff y) = 1 from p.total, one_mul]
lemma expectation_sub (p : FinProbability Y) (f g : Y → ℝ) :
    p.expectation (fun y => f y - g y) = p.expectation f - p.expectation g := by
  classical
  simp [expectation, Finsupp.sum, mul_sub, Finset.sum_sub_distrib]
lemma expectation_neg (p : FinProbability Y) (f : Y → ℝ) :
    p.expectation (-f) = - p.expectation f := by
  classical
  simp [expectation, Finsupp.sum]
lemma expectation_mono (p : FinProbability Y) {f g : Y → ℝ} (h : ∀ y, f y ≤ g y) :
    p.expectation f ≤ p.expectation g := by
  classical
  exact Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (h y) (p.nonneg y)
lemma expectation_nonneg (p : FinProbability Y) {f : Y → ℝ} (h : ∀ y, 0 ≤ f y) :
    0 ≤ p.expectation f := by
  classical
  exact Finset.sum_nonneg fun y _ => mul_nonneg (p.nonneg y) (h y)
lemma abs_expectation_le (p : FinProbability Y) (f : Y → ℝ) :
    |p.expectation f| ≤ p.expectation (fun y => |f y|) := by
  classical
  unfold expectation Finsupp.sum
  calc
    |∑ y ∈ p.coeff.support, p.coeff y * f y|
      ≤ ∑ y ∈ p.coeff.support, |p.coeff y * f y| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ y ∈ p.coeff.support, p.coeff y * |f y| := by
      congr 1
      funext y
      rw [abs_mul, abs_of_nonneg (p.nonneg y)]
noncomputable def gap (p q : FinProbability Y) (f : Y → ℝ) : ℝ :=
  p.expectation f - q.expectation f
lemma gap_const (p q : FinProbability Y) (c : ℝ) : p.gap q (fun _ => c) = 0 := by
  simp [gap, expectation_const]
lemma gap_sub_const (p q : FinProbability Y) (f : Y → ℝ) (c : ℝ) :
    p.gap q (fun y => f y - c) = p.gap q f := by
  simp only [gap, expectation_sub, expectation_const]
  ring
lemma gap_neg (p q : FinProbability Y) (f : Y → ℝ) :
    p.gap q (-f) = -p.gap q f := by
  simp only [gap, expectation_neg]
  ring
lemma gap_telescope (p q r : FinProbability Y) (f : Y → ℝ) :
    p.gap r f = p.gap q f + q.gap r f := by
  simp only [gap]
  ring
lemma coeff_support_nonempty (p : FinProbability Y) : p.coeff.support.Nonempty := by
  by_contra h
  have he := Finset.not_nonempty_iff_eq_empty.mp h
  have hz : p.coeff = 0 := Finsupp.support_eq_empty.mp he
  have ht := p.total
  simp [hz] at ht
lemma gap_bound [PseudoMetricSpace Y] (p q : FinProbability Y)
    (f : Y → ℝ) (hf : LipschitzWith 1 f) (o : Y) :
    |p.gap q f| ≤ p.expectation (fun y => dist y o) +
      q.expectation (fun y => dist y o) := by
  rw [← gap_sub_const p q f (f o)]
  unfold gap
  calc
    |p.expectation (fun y => f y - f o) - q.expectation (fun y => f y - f o)|
      ≤ |p.expectation (fun y => f y - f o)| +
        |q.expectation (fun y => f y - f o)| := abs_sub _ _
    _ ≤ p.expectation (fun y => dist y o) + q.expectation (fun y => dist y o) := by
      apply add_le_add
      · apply (p.abs_expectation_le _).trans
        apply p.expectation_mono
        intro y
        simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using hf.dist_le_mul y o
      · apply (q.abs_expectation_le _).trans
        apply q.expectation_mono
        intro y
        simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using hf.dist_le_mul y o
noncomputable def transport [PseudoMetricSpace Y] (p q : FinProbability Y) : ℝ :=
  sSup {r : ℝ | ∃ f : Y → ℝ, LipschitzWith 1 f ∧ p.gap q f = r}
lemma potential_values_nonempty [PseudoMetricSpace Y] (p q : FinProbability Y) :
    {r : ℝ | ∃ f : Y → ℝ, LipschitzWith 1 f ∧ p.gap q f = r}.Nonempty := by
  refine ⟨0, fun _ => 0, (LipschitzWith.const 0).weaken (by norm_num), ?_⟩
  exact gap_const p q 0
lemma potential_values_bddAbove [PseudoMetricSpace Y] (p q : FinProbability Y) :
    BddAbove {r : ℝ | ∃ f : Y → ℝ, LipschitzWith 1 f ∧ p.gap q f = r} := by
  classical
  obtain ⟨o, _⟩ := p.coeff_support_nonempty
  refine ⟨p.expectation (fun y => dist y o) + q.expectation (fun y => dist y o), ?_⟩
  rintro r ⟨f, hf, rfl⟩
  exact (le_abs_self _).trans (gap_bound p q f hf o)
lemma gap_le_transport [PseudoMetricSpace Y] (p q : FinProbability Y)
    (f : Y → ℝ) (hf : LipschitzWith 1 f) : p.gap q f ≤ p.transport q :=
  le_csSup (potential_values_bddAbove p q) ⟨f, hf, rfl⟩
lemma abs_gap_le_transport [PseudoMetricSpace Y] (p q : FinProbability Y)
    (f : Y → ℝ) (hf : LipschitzWith 1 f) : |p.gap q f| ≤ p.transport q := by
  apply abs_le.mpr
  constructor
  · have h := gap_le_transport p q (-f) hf.neg
    rw [gap_neg] at h
    linarith
  · exact gap_le_transport p q f hf
lemma transport_nonneg [PseudoMetricSpace Y] (p q : FinProbability Y) :
    0 ≤ p.transport q := by
  simpa [gap_const] using gap_le_transport p q (fun _ => 0) ((LipschitzWith.const 0).weaken (by norm_num))
lemma transport_le [PseudoMetricSpace Y] (p q : FinProbability Y) (b : ℝ)
    (h : ∀ f : Y → ℝ, LipschitzWith 1 f → p.gap q f ≤ b) : p.transport q ≤ b := by
  apply csSup_le (potential_values_nonempty p q)
  rintro r ⟨f, hf, rfl⟩
  exact h f hf
lemma transport_self [PseudoMetricSpace Y] (p : FinProbability Y) : p.transport p = 0 := by
  apply le_antisymm _ (transport_nonneg p p)
  apply transport_le
  intro f _
  simp [gap]
lemma transport_triangle [PseudoMetricSpace Y] (p q r : FinProbability Y) :
    p.transport r ≤ p.transport q + q.transport r := by
  apply transport_le
  intro f hf
  rw [gap_telescope p q r f]
  exact add_le_add (gap_le_transport p q f hf) (gap_le_transport q r f hf)
lemma transport_comm [PseudoMetricSpace Y] (p q : FinProbability Y) :
    p.transport q = q.transport p := by
  suffices ∀ p q : FinProbability Y, p.transport q ≤ q.transport p from
    le_antisymm (this p q) (this q p)
  intro p q
  apply transport_le
  intro f hf
  have h := gap_le_transport q p (-f) hf.neg
  simp only [gap, expectation_neg] at *
  linarith
lemma expectation_vertex_indicator [DecidableEq Y] (p : FinProbability Y) (v : Y) :
    p.expectation (fun y => if y = v then (1 : ℝ) else 0) = p.coeff v := by
  classical
  simp only [expectation, Finsupp.sum, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · exact (Finsupp.notMem_support_iff.mp h).symm
lemma coordinate_control [MetricSpace Y] (p q : FinProbability Y)
    (hdiscrete : ∀ y z : Y, y ≠ z → 1 ≤ dist y z) (v : Y) :
    |p.coeff v - q.coeff v| ≤ p.transport q := by
  classical
  let f : Y → ℝ := fun y => if y = v then 1 else 0
  have hf : LipschitzWith 1 f := by
    apply LipschitzWith.of_dist_le_mul
    intro y z
    simp only [NNReal.coe_one, one_mul]
    by_cases hy : y = v <;> by_cases hz : z = v
    · simp [f, hy, hz]
    · simpa [f, hy, hz] using hdiscrete y z (fun h => hz (h ▸ hy))
    · simpa [f, hy, hz] using hdiscrete y z (fun h => hy (h.symm ▸ hz))
    · simp [f, hy, hz]
  simpa only [gap, f, expectation_vertex_indicator] using abs_gap_le_transport p q f hf
lemma transport_eq_zero_iff [MetricSpace Y] (p q : FinProbability Y)
    (hdiscrete : ∀ y z : Y, y ≠ z → 1 ≤ dist y z) : p.transport q = 0 ↔ p = q := by
  constructor
  · intro h
    apply ext_coeff
    ext v
    have hv := coordinate_control p q hdiscrete v
    rw [h] at hv
    exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hv (abs_nonneg _)))
  · rintro rfl
    exact transport_self _
lemma expectation_eq_zero_of_support (p : FinProbability Y) (f : Y → ℝ)
    (hf : ∀ y ∈ p.coeff.support, f y = 0) : p.expectation f = 0 := by
  classical
  unfold expectation Finsupp.sum
  exact Finset.sum_eq_zero fun y hy => by
    change p.coeff y * f y = 0
    rw [hf y hy, mul_zero]
lemma exists_support_le_expectation (p : FinProbability Y) (f : Y → ℝ) :
    ∃ y ∈ p.coeff.support, f y ≤ p.expectation f := by
  classical
  by_contra! h
  have hlt : p.expectation (fun _ => p.expectation f) < p.expectation f := by
    unfold expectation Finsupp.sum
    apply Finset.sum_lt_sum
    · intro y hy
      exact (mul_lt_mul_of_pos_left (h y hy)
        (lt_of_le_of_ne (p.nonneg y) (Ne.symm (Finsupp.mem_support_iff.mp hy)))).le
    · obtain ⟨y, hy⟩ := p.coeff_support_nonempty
      exact ⟨y, hy, mul_lt_mul_of_pos_left (h y hy)
        (lt_of_le_of_ne (p.nonneg y) (Ne.symm (Finsupp.mem_support_iff.mp hy)))⟩
  rw [expectation_const] at hlt
  exact (lt_irrefl _ hlt)
lemma expectation_distance_support_le [MetricSpace Y] (c p : FinProbability Y) :
    p.expectation (fun y => Metric.infDist y (c.coeff.support : Set Y)) ≤
      c.transport p := by
  have hc : c.expectation (fun y => Metric.infDist y (c.coeff.support : Set Y)) = 0 := by
    apply expectation_eq_zero_of_support
    intro y hy
    exact Metric.infDist_zero_of_mem hy
  have hp : 0 ≤ p.expectation (fun y => Metric.infDist y (c.coeff.support : Set Y)) :=
    p.expectation_nonneg fun _ => Metric.infDist_nonneg
  have h := abs_gap_le_transport c p
    (fun y => Metric.infDist y (c.coeff.support : Set Y))
    (Metric.lipschitz_infDist_pt _)
  simpa only [gap, hc, zero_sub, abs_neg, abs_of_nonneg hp] using h
lemma exists_support_pair_dist_le [MetricSpace Y] (c p : FinProbability Y) :
    ∃ a ∈ c.coeff.support, ∃ v ∈ p.coeff.support, dist a v ≤ c.transport p := by
  obtain ⟨v, hv, hvl⟩ := exists_support_le_expectation p
    (fun y => Metric.infDist y (c.coeff.support : Set Y))
  obtain ⟨a, ha, hva⟩ := c.coeff.support.finite_toSet.isCompact.exists_infDist_eq_dist
    (by simpa using c.coeff_support_nonempty) v
  refine ⟨a, ha, v, hv, ?_⟩
  rw [dist_comm, ← hva]
  exact hvl.trans (expectation_distance_support_le c p)
noncomputable def rho [PseudoMetricSpace Y] (n : ℕ) (p q : FinProbability Y) : ℝ :=
  p.transport q / Real.sqrt (n : ℝ)
lemma rho_triangle [PseudoMetricSpace Y] (n : ℕ) (p q r : FinProbability Y) :
    rho n p r ≤ rho n p q + rho n q r := by
  unfold rho
  rw [← add_div]
  exact div_le_div_of_nonneg_right (transport_triangle p q r) (Real.sqrt_nonneg _)
lemma rho_comm [PseudoMetricSpace Y] (n : ℕ) (p q : FinProbability Y) :
    rho n p q = rho n q p := by rw [rho, rho, transport_comm p q]
lemma sqrt_mul_rho [PseudoMetricSpace Y] {n : ℕ} (hn : 0 < n) (p q : FinProbability Y) :
    Real.sqrt (n : ℝ) * rho n p q = p.transport q := by
  have hs : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by exact_mod_cast hn))
  unfold rho
  field_simp
lemma support_distance_rho [MetricSpace Y] {n : ℕ} (hn : 0 < n)
    (c p : FinProbability Y) :
    ∃ a ∈ c.coeff.support, ∃ v ∈ p.coeff.support,
      dist a v ≤ Real.sqrt (n : ℝ) * rho n c p := by
  rw [sqrt_mul_rho hn]
  exact exists_support_pair_dist_le c p
end FinProbability
end BassTrace.Sparse
end OAI

end
section
namespace OAI
namespace BassTrace.Sparse
open Set Filter
open scoped Topology
variable {E I : Type*} [AddCommGroup E] [Module ℝ E] [Fintype I]
def halfspacePolyhedron (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ) : Set E :=
  {x | ∀ i, a i x ≤ b i}
noncomputable def activeConstraints (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ) (x : E) : Finset I :=
  Finset.univ.filter fun i => a i x = b i
lemma mem_activeConstraints (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ) (x : E) (i : I) :
    i ∈ activeConstraints a b x ↔ a i x = b i := by
  classical
  simp [activeConstraints]
lemma exists_extrapolate_mem
    (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ) {x y : E}
    (hx : x ∈ halfspacePolyhedron a b)
    (hactive : activeConstraints a b x = activeConstraints a b y) :
    ∃ t : ℝ, 0 < t ∧ x + t • (x - y) ∈ halfspacePolyhedron a b := by
  have hi (i : I) : ∀ᶠ t : ℝ in 𝓝 0, a i (x + t • (x - y)) ≤ b i := by
    by_cases h : a i x = b i
    · have hyi : a i y = b i := by
        rw [← mem_activeConstraints, ← hactive, mem_activeConstraints]
        exact h
      filter_upwards [] with t
      simp only [map_add, map_smul, map_sub, smul_eq_mul, h, hyi, sub_self,
        mul_zero, add_zero, le_refl]
    · have hlt : a i x < b i := lt_of_le_of_ne (hx i) h
      have hc : Continuous (fun t : ℝ => a i x + t * (a i x - a i y)) := by fun_prop
      have he : ∀ᶠ t : ℝ in 𝓝 0, a i x + t * (a i x - a i y) < b i :=
        hc.continuousAt.eventually (gt_mem_nhds (by simpa using hlt))
      filter_upwards [he] with t ht
      simpa only [map_add, map_smul, map_sub, smul_eq_mul] using ht.le
  have hall : ∀ᶠ t : ℝ in 𝓝 0, ∀ i, a i (x + t • (x - y)) ≤ b i :=
    Filter.eventually_all.mpr hi
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hall
  refine ⟨δ / 2, by positivity, hball ?_⟩
  simp only [Metric.mem_ball, Real.dist_eq, sub_zero]
  rw [abs_of_pos (by positivity : 0 < δ / 2)]
  linarith
lemma activeConstraints_injOn_extremePoints
    (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ) :
    Set.InjOn (activeConstraints a b) ((halfspacePolyhedron a b).extremePoints ℝ) := by
  intro x hx y hy hactive
  obtain ⟨t, ht, hz⟩ := exists_extrapolate_mem a b hx.1 hactive
  have hsum : t + 1 ≠ 0 := by positivity
  have hseg : x ∈ openSegment ℝ y (x + t • (x - y)) := by
    apply mem_openSegment_iff_div.mpr
    refine ⟨t, 1, ht, by norm_num, ?_⟩
    simp only [smul_add, smul_sub, smul_smul]
    rw [show 1 / (t + 1) * t = t / (t + 1) by ring]
    calc
      _ = (1 / (t + 1) + t / (t + 1)) • x := by module
      _ = x := by rw [← add_div, add_comm 1 t, div_self hsum, one_smul]
  exact (hx.2 hy.1 hz hseg).symm
lemma finite_extremePoints_halfspacePolyhedron
    (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ) :
    ((halfspacePolyhedron a b).extremePoints ℝ).Finite := by
  classical
  exact Set.Finite.of_injOn (t := Set.univ) (Set.mapsTo_univ _ _)
    (activeConstraints_injOn_extremePoints a b) Set.finite_univ
noncomputable def polyhedronVertices (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ) : Finset E :=
  (finite_extremePoints_halfspacePolyhedron a b).toFinset
@[simp] lemma mem_polyhedronVertices
    (a : I → E →ₗ[ℝ] ℝ) (b : I → ℝ) (x : E) :
    x ∈ polyhedronVertices a b ↔ x ∈ (halfspacePolyhedron a b).extremePoints ℝ :=
  Set.Finite.mem_toFinset _
section Compact
variable [TopologicalSpace E] [T2Space E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
lemma exists_extreme_maximizer {s : Set E} (hs : IsCompact s) (hne : s.Nonempty)
    (f : E →L[ℝ] ℝ) :
    ∃ x ∈ s.extremePoints ℝ, ∀ y ∈ s, f y ≤ f x := by
  obtain ⟨x, hx, hxmax⟩ := hs.exists_isMaxOn hne f.continuous.continuousOn
  have hex : IsExposed ℝ s {x ∈ s | ∀ y ∈ s, f y ≤ f x} := fun _ => ⟨f, rfl⟩
  obtain ⟨z, hz⟩ := (hex.isCompact hs).extremePoints_nonempty ⟨x, hx, hxmax⟩
  exact ⟨z, hex.isExtreme.extremePoints_subset_extremePoints hz, hz.1.2⟩
end Compact
section Potential
variable {V : Type*} [Fintype V] [MetricSpace V]
def potentialSet : Set (V → ℝ) :=
  {l | (∑ v, l v) = 0 ∧ ∀ v w, |l v - l w| ≤ dist v w}
noncomputable def potentialLinear : (V × V) ⊕ Bool → (V → ℝ) →ₗ[ℝ] ℝ
  | .inl (v,w) => LinearMap.proj (R := ℝ) (φ := fun _ : V => ℝ) v - LinearMap.proj (R := ℝ) (φ := fun _ : V => ℝ) w
  | .inr false => ∑ v : V, LinearMap.proj (R := ℝ) (φ := fun _ : V => ℝ) v
  | .inr true => -∑ v : V, LinearMap.proj (R := ℝ) (φ := fun _ : V => ℝ) v
def potentialBound : (V × V) ⊕ Bool → ℝ
  | .inl (v,w) => dist v w
  | .inr _ => 0
lemma potentialSet_eq_halfspacePolyhedron :
    (potentialSet : Set (V → ℝ)) = halfspacePolyhedron potentialLinear potentialBound := by
  classical
  ext l
  constructor
  · rintro ⟨hzero, hdist⟩ (⟨v,w⟩ | b)
    · exact le_trans (le_abs_self _) (hdist v w)
    · cases b <;> simp [potentialLinear, potentialBound, hzero]
  · intro h
    have hle : (∑ v, l v) ≤ 0 := by simpa [potentialLinear, potentialBound] using h (.inr false)
    have hge : 0 ≤ ∑ v, l v := by simpa [potentialLinear, potentialBound] using h (.inr true)
    refine ⟨le_antisymm hle hge, fun v w => abs_le.mpr ⟨?_, ?_⟩⟩
    · have h' : l w - l v ≤ dist v w := by
        simpa [potentialLinear, potentialBound, dist_comm] using h (.inl (w,v))
      linarith
    · exact h (.inl (v,w))
lemma zero_mem_potentialSet : (0 : V → ℝ) ∈ potentialSet := by
  simp [potentialSet, dist_nonneg]
lemma isClosed_potentialSet : IsClosed (potentialSet : Set (V → ℝ)) := by
  have heq : (potentialSet : Set (V → ℝ)) =
      {l | (∑ v, l v) = 0} ∩ ⋂ v, ⋂ w, {l | |l v - l w| ≤ dist v w} := by
    ext l
    simp [potentialSet]
  rw [heq]
  apply IsClosed.inter
  · exact isClosed_eq (by fun_prop) continuous_const
  · exact isClosed_iInter fun v => isClosed_iInter fun w =>
      isClosed_le (by fun_prop) continuous_const
noncomputable def totalDistances : ℝ := ∑ v : V, ∑ w : V, dist v w
lemma dist_le_totalDistances (v w : V) : dist v w ≤ totalDistances (V := V) := by
  classical
  apply (Finset.single_le_sum (f := fun w' : V => dist v w') (fun _ _ => dist_nonneg) (Finset.mem_univ w)).trans
  exact Finset.single_le_sum (f := fun v' : V => ∑ w' : V, dist v' w')
    (fun _ _ => Finset.sum_nonneg fun _ _ => dist_nonneg) (Finset.mem_univ v)
lemma potential_coordinate_bound [Nonempty V] {l : V → ℝ} (hl : l ∈ potentialSet) (v : V) :
    |l v| ≤ totalDistances (V := V) := by
  classical
  have hmin : ∃ w, l w ≤ 0 := by
    by_contra! h
    have hp : 0 < ∑ w, l w := Finset.sum_pos (fun w _ => h w) Finset.univ_nonempty
    rw [hl.1] at hp
    exact lt_irrefl 0 hp
  have hmax : ∃ w, 0 ≤ l w := by
    by_contra! h
    have hp : ∑ w, l w < 0 := Finset.sum_neg (fun w _ => h w) Finset.univ_nonempty
    rw [hl.1] at hp
    exact lt_irrefl 0 hp
  obtain ⟨w, hw⟩ := hmin
  obtain ⟨z, hz⟩ := hmax
  have hvw := (hl.2 v w).trans (dist_le_totalDistances v w)
  have hvz := (hl.2 v z).trans (dist_le_totalDistances v z)
  rw [abs_le] at hvw hvz ⊢
  constructor <;> linarith
lemma isCompact_potentialSet [Nonempty V] : IsCompact (potentialSet : Set (V → ℝ)) := by
  apply IsCompact.of_isClosed_subset (s := Set.Icc (fun _ : V => -totalDistances (V := V))
    (fun _ : V => totalDistances (V := V))) isCompact_Icc isClosed_potentialSet
  intro l hl
  constructor <;> intro v
  · exact (abs_le.mp (potential_coordinate_bound hl v)).1
  · exact (abs_le.mp (potential_coordinate_bound hl v)).2
noncomputable def potentialVertices : Finset (V → ℝ) :=
  polyhedronVertices potentialLinear potentialBound
lemma mem_potentialVertices (l : V → ℝ) :
    l ∈ potentialVertices ↔ l ∈ (potentialSet : Set (V → ℝ)).extremePoints ℝ := by
  rw [potentialVertices, mem_polyhedronVertices, ← potentialSet_eq_halfspacePolyhedron]
lemma potentialVertices_subset (l : V → ℝ) (hl : l ∈ potentialVertices) : l ∈ potentialSet :=
  (mem_potentialVertices l).mp hl |>.1
lemma exists_potential_vertex_maximizer [Nonempty V] (f : (V → ℝ) →L[ℝ] ℝ) :
    ∃ l ∈ potentialVertices, ∀ k ∈ potentialSet, f k ≤ f l := by
  simpa only [mem_potentialVertices] using
    exists_extreme_maximizer isCompact_potentialSet ⟨0, zero_mem_potentialSet⟩ f
noncomputable def centerPotential (l : V → ℝ) (v : V) : ℝ :=
  l v - (∑ w, l w) / Fintype.card V
lemma centerPotential_mem [Nonempty V] {l : V → ℝ} (hl : LipschitzWith 1 l) :
    centerPotential l ∈ potentialSet := by
  classical
  have hc : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  constructor
  · simp only [centerPotential, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    field_simp
    ring
  · intro v w
    have h := hl.dist_le_mul v w
    simp only [Real.dist_eq, NNReal.coe_one, one_mul] at h
    convert h using 1
    unfold centerPotential
    congr 1
    ring
noncomputable def potentialPairing (k : V → ℝ) : (V → ℝ) →L[ℝ] ℝ :=
  ∑ v : V, (k v) • ContinuousLinearMap.proj v
omit [MetricSpace V] in
lemma potentialPairing_apply (k l : V → ℝ) :
    potentialPairing k l = ∑ v, k v * l v := by
  classical
  simp [potentialPairing]
omit [MetricSpace V] in
lemma pairing_centerPotential (k l : V → ℝ) (hk : ∑ v, k v = 0) :
    potentialPairing k (centerPotential l) = potentialPairing k l := by
  classical
  simp only [potentialPairing_apply, centerPotential, mul_sub, Finset.sum_sub_distrib,
    ← Finset.sum_mul, hk, zero_mul, sub_zero]
end Potential
variable {Y : Type*} [MetricSpace Y] (S : Finset Y)
lemma exists_global_potential_extension {l : S → ℝ} (hl : l ∈ potentialSet) :
    ∃ f : Y → ℝ, LipschitzWith 1 f ∧ ∀ v : S, f v = l v := by
  classical
  let p : Y → ℝ := fun y => if h : y ∈ S then l ⟨y,h⟩ else 0
  have hp : LipschitzOnWith 1 p (S : Set Y) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro v hv w hw
    change v ∈ S at hv
    change w ∈ S at hw
    simpa only [p, dite_eq_left hv, dite_eq_left hw, Real.dist_eq, NNReal.coe_one, one_mul, Subtype.dist_eq]
      using hl.2 ⟨v,hv⟩ ⟨w,hw⟩
  obtain ⟨f, hf, hpf⟩ := hp.extend_real
  refine ⟨f, hf, fun v => ?_⟩
  have h := hpf v.2
  simpa [p, v.2, eq_comm] using h
lemma exists_global_vertex_maximizer (hne : S.Nonempty) (k : S → ℝ)
    (hk : ∑ v, k v = 0) :
    ∃ l ∈ (potentialVertices : Finset (S → ℝ)),
      (∃ f : Y → ℝ, LipschitzWith 1 f ∧ ∀ v : S, f v = l v) ∧
      ∀ f : Y → ℝ, LipschitzWith 1 f →
        (∑ v : S, k v * f v) ≤ ∑ v : S, k v * l v := by
  have : Nonempty S := by
    obtain ⟨v, hv⟩ := hne
    exact ⟨⟨v,hv⟩⟩
  obtain ⟨l, hl, hmax⟩ := exists_potential_vertex_maximizer (potentialPairing k)
  refine ⟨l, hl, exists_global_potential_extension S (potentialVertices_subset l hl), ?_⟩
  intro f hf
  have hsub : LipschitzWith 1 (fun v : S => f v) := by
    apply LipschitzWith.of_dist_le_mul
    intro v w
    simpa only [NNReal.coe_one, one_mul, Subtype.dist_eq] using hf.dist_le_mul v.val w.val
  have hm := hmax (centerPotential (fun v : S => f v)) (centerPotential_mem hsub)
  rw [pairing_centerPotential k _ hk] at hm
  simpa only [potentialPairing_apply] using hm
end BassTrace.Sparse
end OAI

end
section
namespace OAI
noncomputable section
namespace BassTrace.Sparse
section
variable {Y : Type*}
private def vectorEmbedding : (Y →₀ ℝ) →ₗ[ℝ] lp (fun _ : Y => ℝ) 2 := by
  classical
  exact Finsupp.linearCombination ℝ (fun y => lp.single 2 y 1)
private lemma vectorEmbedding_apply (v : Y →₀ ℝ) (y : Y) :
    vectorEmbedding v y = v y := by
  classical
  simp only [vectorEmbedding,Finsupp.linearCombination_apply, Finsupp.sum,
    lp.coeFn_sum,lp.coeFn_smul,Finset.sum_apply,Pi.smul_apply,lp.single_apply]
  simp [Pi.single_apply,eq_comm]
private lemma vectorEmbedding_injective :
    Function.Injective (vectorEmbedding (Y := Y)) := by
  intro v w h
  ext y
  simpa only [vectorEmbedding_apply] using congrArg (fun f : lp (fun _ : Y => ℝ) 2 => f y) h
scoped instance realFinsuppNormedAddCommGroup : NormedAddCommGroup (Y →₀ ℝ) :=
  NormedAddCommGroup.induced _ _ vectorEmbedding vectorEmbedding_injective
scoped instance realFinsuppNormedSpace : NormedSpace ℝ (Y →₀ ℝ) :=
  NormedSpace.induced ℝ _ _ vectorEmbedding
open scoped BassTrace.Sparse
lemma coordinate_norm_le (v : Y →₀ ℝ) (y : Y) : ‖v y‖ ≤ ‖v‖ := by
  change ‖v y‖ ≤ ‖vectorEmbedding v‖
  rw [← vectorEmbedding_apply v y]
  exact lp.norm_apply_le_norm (by norm_num) _ _
def coordinateCLM (y : Y) : (Y →₀ ℝ) →L[ℝ] ℝ :=
  (Finsupp.lapply y).mkContinuous 1 (fun v => by simpa using coordinate_norm_le v y)
@[simp] lemma coordinateCLM_apply (y : Y) (v : Y →₀ ℝ) : coordinateCLM y v = v y := rfl
def finitePairingCLM (S : Finset Y) (a : Y → ℝ) : (Y →₀ ℝ) →L[ℝ] ℝ :=
  ∑ y ∈ S, a y • coordinateCLM (y : Y)
@[simp] lemma finitePairingCLM_apply (S : Finset Y) (a : Y → ℝ) (v : Y →₀ ℝ) :
    finitePairingCLM S a v = ∑ y ∈ S, a y * v y := by
  simp [finitePairingCLM]
end
open Set Finset MeasureTheory
open scoped BassTrace.Sparse ENNReal Classical
variable {Y Z : Type*} [DecidableEq Y] [DecidableEq Z]
def finsuppRelabelIsometry (e : Y ≃ Z) : (Y →₀ ℝ) ≃ₗᵢ[ℝ] (Z →₀ ℝ) where
  __ := Finsupp.domLCongr (R := ℝ) e
  norm_map' v := by
    change ‖vectorEmbedding (Finsupp.domLCongr (R := ℝ) e v)‖ = ‖vectorEmbedding v‖
    rw [lp.norm_eq_tsum_rpow (by norm_num),lp.norm_eq_tsum_rpow (by norm_num)]
    simp only [vectorEmbedding_apply]
    congr 1
    change (∑' z,‖v (e.symm z)‖ ^ (2 : ℝ)) = ∑' y,‖v y‖ ^ (2 : ℝ)
    exact e.symm.tsum_eq (fun y : Y => ‖v y‖ ^ (2 : ℝ))
end BassTrace.Sparse
end
end OAI

end
section
namespace OAI
noncomputable section
namespace BassTrace.Sparse
section
open Finset
open scoped BassTrace.Sparse
variable {Y : Type*} [MetricSpace Y]
namespace FinProbability
omit [MetricSpace Y] in
lemma expectation_on_finset (p : FinProbability Y) (S : Finset Y)
    (hp : p.coeff.support ⊆ S) (f : Y → ℝ) :
    p.expectation f = ∑ y : S, p.coeff y * f y := by
  rw [expectation,p.coeff.sum_of_support_subset hp _ (by intros; simp)]
  exact Finset.sum_subtype S (fun _ => Iff.rfl) _
omit [MetricSpace Y] in
lemma total_on_finset (p : FinProbability Y) (S : Finset Y)
    (hp : p.coeff.support ⊆ S) : ∑ y : S, p.coeff y = 1 := by
  simpa only [mul_one] using (p.expectation_on_finset S hp (fun _ => 1)).symm.trans
    (p.expectation_const 1)
omit [MetricSpace Y] in
lemma gap_on_finset (c p : FinProbability Y) (S : Finset Y)
    (hc : c.coeff.support ⊆ S) (hp : p.coeff.support ⊆ S) (f : Y → ℝ) :
    c.gap p f = ∑ y : S, (c.coeff y-p.coeff y)*f y := by
  rw [gap,c.expectation_on_finset S hc,p.expectation_on_finset S hp]
  simp only [sub_mul,Finset.sum_sub_distrib]
end FinProbability
def centerBranchValue (S : Finset Y) (c : FinProbability Y) (l : S → ℝ) : ℝ :=
  ∑ y : S, c.coeff y * l y
def ballBranch (S : Finset Y) (c : FinProbability Y) (n : ℕ) (l : S → ℝ) :
    (Y →₀ ℝ) →L[ℝ] ℝ :=
  ∑ y : S, ((centerBranchValue S c l - l y) / Real.sqrt n) • coordinateCLM (y : Y)
omit [MetricSpace Y] in
lemma ballBranch_apply (S : Finset Y) (c : FinProbability Y) (n : ℕ)
    (l : S → ℝ) (p : Y →₀ ℝ) :
    ballBranch S c n l p = ∑ y : S,
      ((centerBranchValue S c l-l y)/Real.sqrt n) * p y := by
  simp only [ballBranch,_root_.sum_apply,smul_apply,
    coordinateCLM_apply,smul_eq_mul]
omit [MetricSpace Y] in
lemma ballBranch_eq_pairing (S : Finset Y) (c p : FinProbability Y)
    (hp : p.coeff.support ⊆ S) (n : ℕ) (l : S → ℝ) :
    ballBranch S c n l p.coeff =
      (∑ y : S, (c.coeff y-p.coeff y)*l y) / Real.sqrt n := by
  rw [ballBranch_apply]
  simp_rw [div_mul_eq_mul_div,← Finset.sum_div,sub_mul]
  rw [Finset.sum_sub_distrib,← Finset.mul_sum,p.total_on_finset S hp,mul_one]
  simp only [centerBranchValue,Finset.sum_sub_distrib]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro y _
  exact mul_comm _ _
theorem exists_ballBranch_maximizer (S : Finset Y) (c p : FinProbability Y)
    (hc : c.coeff.support ⊆ S) (hp : p.coeff.support ⊆ S) (n : ℕ) :
    ∃ l ∈ (potentialVertices : Finset (S → ℝ)),
      FinProbability.rho n c p = ballBranch S c n l p.coeff ∧
      ∀ l' ∈ (potentialVertices : Finset (S → ℝ)),
        ballBranch S c n l' p.coeff ≤ FinProbability.rho n c p := by
  classical
  have hS : S.Nonempty := c.coeff_support_nonempty.mono hc
  let k : S → ℝ := fun y => c.coeff y-p.coeff y
  have hk : ∑ y, k y = 0 := by
    simp only [k,Finset.sum_sub_distrib,c.total_on_finset S hc,p.total_on_finset S hp,
      sub_self]
  obtain ⟨l,hl,⟨f,hf,hfl⟩,hmax⟩ := exists_global_vertex_maximizer S hS k hk
  have heq : c.transport p = ∑ y : S, k y*l y := by
    apply le_antisymm
    · apply FinProbability.transport_le
      intro g hg
      rw [c.gap_on_finset p S hc hp]
      exact hmax g hg
    · have hh := c.gap_le_transport p f hf
      rw [c.gap_on_finset p S hc hp] at hh
      simpa only [k,hfl] using hh
  refine ⟨l,hl,?_,?_⟩
  · rw [FinProbability.rho,heq,ballBranch_eq_pairing S c p hp]
  · intro l' hl'
    obtain ⟨g,hg,hgl⟩ := exists_global_potential_extension S (potentialVertices_subset l' hl')
    rw [ballBranch_eq_pairing S c p hp,FinProbability.rho]
    apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
    have hh := c.gap_le_transport p g hg
    rw [c.gap_on_finset p S hc hp] at hh
    simpa only [hgl] using hh
end
open Set Finset
open scoped BassTrace.Sparse
section
variable {Y : Type*}
def coefficientSum : (Y →₀ ℝ) →ₗ[ℝ] ℝ :=
  Finsupp.linearCombination ℝ (fun _ : Y => (1 : ℝ))
@[simp] lemma coefficientSum_apply (v : Y →₀ ℝ) :
    coefficientSum v = v.sum (fun _ r => r) := by
  simp [coefficientSum,Finsupp.linearCombination_apply]
@[simp] lemma coefficientSum_single (y : Y) (r : ℝ) :
    coefficientSum (Finsupp.single y r) = r := by simp
def probabilitySet (s : Finset Y) : Set (Y →₀ ℝ) :=
  {v | (∀ y, 0 ≤ v y) ∧ coefficientSum v = 1 ∧ v.support ⊆ s}
lemma convex_probabilitySet (s : Finset Y) : Convex ℝ (probabilitySet s) := by
  intro v hv w hw a b ha hb hab
  refine ⟨?_,?_,?_⟩
  · intro y
    change 0 ≤ a * v y + b * w y
    exact add_nonneg (mul_nonneg ha (hv.1 y)) (mul_nonneg hb (hw.1 y))
  · change coefficientSum (a • v + b • w) = 1
    rw [map_add,map_smul,map_smul,hv.2.1,hw.2.1]
    simpa using hab
  · intro y hy
    by_contra h
    have hv0 : v y = 0 := Finsupp.notMem_support_iff.mp (fun hy => h (hv.2.2 hy))
    have hw0 : w y = 0 := Finsupp.notMem_support_iff.mp (fun hy => h (hw.2.2 hy))
    exact (Finsupp.mem_support_iff.mp hy) (by simp [Finsupp.add_apply,Finsupp.smul_apply,hv0,hw0])
lemma single_mem_probabilitySet (s : Finset Y) {y : Y} (hy : y ∈ s) :
    Finsupp.single y (1 : ℝ) ∈ probabilitySet s := by
  classical
  refine ⟨?_, by simp, ?_⟩
  · intro z
    simp only [Finsupp.single_apply]
    split_ifs <;> norm_num
  · simpa using Finset.singleton_subset_iff.mpr hy
lemma sum_single_of_support_subset (s : Finset Y) (v : Y →₀ ℝ)
    (hv : v.support ⊆ s) :
    ∑ y ∈ s, v y • Finsupp.single y (1 : ℝ) = v := by
  classical
  ext z
  simp only [Finsupp.finsetSum_apply,Finsupp.smul_apply,smul_eq_mul,Finsupp.single_apply]
  by_cases hz : z ∈ s
  · simp [hz,eq_comm]
  · have hvz := Finsupp.notMem_support_iff.mp (fun h => hz (hv h))
    simp [hz,hvz,eq_comm]
lemma sum_coeff_of_support_subset (s : Finset Y) (v : Y →₀ ℝ)
    (hv : v.support ⊆ s) : ∑ y ∈ s, v y = coefficientSum v := by
  rw [coefficientSum_apply,Finsupp.sum]
  exact (Finset.sum_subset hv (fun y _ hy => Finsupp.notMem_support_iff.mp hy)).symm
lemma convexHull_single_eq_probabilitySet (s : Finset Y) :
    convexHull ℝ ((fun y : Y => Finsupp.single y (1 : ℝ)) '' (s : Set Y)) =
      probabilitySet s := by
  apply Set.Subset.antisymm
  · apply convexHull_min
    · rintro _ ⟨y,hy,rfl⟩
      exact single_mem_probabilitySet s hy
    · exact convex_probabilitySet s
  · intro v hv
    rw [← sum_single_of_support_subset s v hv.2.2]
    apply (convex_convexHull ℝ _).sum_mem
    · exact fun y _ => hv.1 y
    · exact (sum_coeff_of_support_subset s v hv.2.2).trans hv.2.1
    · intro y hy
      exact subset_convexHull ℝ _ ⟨y,hy,rfl⟩
lemma FinProbability.mem_geometric_simplex (p : FinProbability Y) (s : Finset Y) :
    p.coeff ∈ convexHull ℝ
        ((fun y : Y => Finsupp.single y (1 : ℝ)) '' (s : Set Y)) ↔
      p.coeff.support ⊆ s := by
  rw [convexHull_single_eq_probabilitySet]
  exact ⟨fun h => h.2.2,fun h => ⟨p.nonneg,by simpa using p.total,h⟩⟩
lemma probabilitySet_eq (s : Finset Y) :
    probabilitySet s = {v | ∃ p : FinProbability Y, p.coeff = v ∧ p.coeff.support ⊆ s} := by
  ext v
  constructor
  · intro h
    exact ⟨⟨v,h.1,by simpa using h.2.1⟩,rfl,h.2.2⟩
  · rintro ⟨p,rfl,hp⟩
    exact ⟨p.nonneg,by simpa using p.total,hp⟩
lemma geometric_simplex_compact (s : Finset Y) :
    IsCompact (probabilitySet s) := by
  rw [← convexHull_single_eq_probabilitySet]
  exact (s.finite_toSet.image _).isCompact_convexHull ℝ
end
section
variable {Y : Type*} [DecidableEq Y]
lemma onFinsupp_faces (K : PreAbstractSimplicialComplex Y) :
    (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).faces =
      (fun s : Finset Y => s.image (fun y => Finsupp.single y (1 : ℝ))) '' K.faces := rfl
lemma onFinsupp_space (K : PreAbstractSimplicialComplex Y) :
    (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space =
      {v | ∃ p : FinProbability Y, p.coeff = v ∧ p.coeff.support ∈ K.faces} := by
  ext v
  rw [Geometry.SimplicialComplex.mem_space_iff]
  constructor
  · rintro ⟨s,hs,hv⟩
    rw [onFinsupp_faces] at hs
    obtain ⟨t,ht,rfl⟩ := hs
    rw [Finset.coe_image,convexHull_single_eq_probabilitySet,probabilitySet_eq] at hv
    obtain ⟨p,hp,hpt⟩ := hv
    exact ⟨p,hp,(K.isRelLowerSet_faces ht).2 hpt p.coeff_support_nonempty⟩
  · rintro ⟨p,rfl,hp⟩
    refine ⟨p.coeff.support.image (fun y => Finsupp.single y (1 : ℝ)),?_,?_⟩
    · exact ⟨p.coeff.support,hp,rfl⟩
    · rw [Finset.coe_image,p.mem_geometric_simplex]
end
variable {Y : Type*} [MetricSpace Y]
abbrev FinProbability.rhoMetric (n : ℕ) (hn : 0 < n)
    (hd : ∀ y z : Y, y ≠ z → 1 ≤ dist y z) : MetricSpace (FinProbability Y) where
  dist := FinProbability.rho n
  dist_self p := by simp [FinProbability.rho,FinProbability.transport_self]
  dist_comm := FinProbability.rho_comm n
  dist_triangle := FinProbability.rho_triangle n
  eq_of_dist_eq_zero := by
    intro p q hpq
    apply (FinProbability.transport_eq_zero_iff p q hd).mp
    rw [← FinProbability.sqrt_mul_rho hn,hpq,mul_zero]
def simplexProbability (S : Finset Y) (v : probabilitySet S) : FinProbability Y :=
  ⟨v.val,v.property.1,by simpa using v.property.2.1⟩
lemma potentialVertices_nonempty (S : Finset Y) (hS : S.Nonempty) :
    (potentialVertices : Finset (S → ℝ)).Nonempty := by
  let : Nonempty S := hS.to_subtype
  obtain ⟨l,hl,_⟩ := exists_potential_vertex_maximizer (V := S) (0 : (S → ℝ) →L[ℝ] ℝ)
  exact ⟨l,hl⟩
lemma rho_eq_vertex_sup (S : Finset Y) (hS : S.Nonempty) (n : ℕ)
    (p q : FinProbability Y) (hp : p.coeff.support ⊆ S) (hq : q.coeff.support ⊆ S) :
    FinProbability.rho n p q =
      (potentialVertices : Finset (S → ℝ)).sup' (potentialVertices_nonempty S hS)
        (fun l => (∑ y : S, (p.coeff y-q.coeff y)*l y)/Real.sqrt n) := by
  obtain ⟨l,hl,heq,hmax⟩ := exists_ballBranch_maximizer S p q hp hq n
  apply le_antisymm
  · rw [heq,ballBranch_eq_pairing S p q hq]
    exact Finset.le_sup' (fun l => (∑ y : S, (p.coeff y-q.coeff y)*l y)/Real.sqrt n) hl
  · apply (Finset.sup'_le_iff _ _).mpr
    intro l' hl'
    rw [← ballBranch_eq_pairing S p q hq]
    exact hmax l' hl'
lemma continuous_simplexProbability (S : Finset Y) (n : ℕ) (hn : 0 < n)
    (hd : ∀ y z : Y, y ≠ z → 1 ≤ dist y z) :
    let := FinProbability.rhoMetric n hn hd
    Continuous (simplexProbability S) := by
  let := FinProbability.rhoMetric n hn hd
  by_cases hS : S.Nonempty
  · rw [continuous_iff_continuous_dist]
    have heq : (fun p : probabilitySet S × probabilitySet S =>
        dist (simplexProbability S p.1) (simplexProbability S p.2)) =
        fun p => (potentialVertices : Finset (S → ℝ)).sup' (potentialVertices_nonempty S hS)
          (fun l => (∑ y : S, (p.1.val y-p.2.val y)*l y)/Real.sqrt n) := by
      funext p
      exact rho_eq_vertex_sup S hS n _ _ p.1.property.2.2 p.2.property.2.2
    rw [heq]
    apply Continuous.finset_sup'_apply
    intro l _
    apply Continuous.div_const
    apply continuous_finsetSum
    intro y _
    apply Continuous.mul_const
    apply Continuous.sub
    · exact (coordinateCLM (y : Y)).continuous.comp (continuous_subtype_val.comp continuous_fst)
    · exact (coordinateCLM (y : Y)).continuous.comp (continuous_subtype_val.comp continuous_snd)
  · have : IsEmpty (probabilitySet S) := ⟨fun v => hS
        ((simplexProbability S v).coeff_support_nonempty.mono v.property.2.2)⟩
    exact continuous_iff_continuousAt.mpr (fun v => isEmptyElim v)
lemma isCompact_probability_simplex (S : Finset Y) (n : ℕ) (hn : 0 < n)
    (hd : ∀ y z : Y, y ≠ z → 1 ≤ dist y z) :
    let := FinProbability.rhoMetric n hn hd
    IsCompact {p : FinProbability Y | p.coeff.support ⊆ S} := by
  let := FinProbability.rhoMetric n hn hd
  let : CompactSpace (probabilitySet S) := isCompact_iff_compactSpace.mp (geometric_simplex_compact S)
  have heq : {p : FinProbability Y | p.coeff.support ⊆ S} =
      Set.range (simplexProbability S) := by
    ext p
    constructor
    · intro hp
      exact ⟨⟨p.coeff,p.nonneg,by simpa using p.total,hp⟩,rfl⟩
    · rintro ⟨v,rfl⟩
      exact v.property.2.2
  rw [heq]
  exact isCompact_range (continuous_simplexProbability S n hn hd)
end BassTrace.Sparse
end
end OAI

end
section
namespace OAI
noncomputable section
namespace BassTrace
namespace Sparse.GraphGeometry
section
open scoped BigOperators
open FinProbability
variable {Y : Type*} (Γ : SimpleGraph Y)
abbrev graphMetric (hΓ : Γ.Connected) : MetricSpace Y where
  dist a b := (Γ.dist a b : ℝ)
  dist_self a := by simp
  dist_comm a b := by rw [Γ.dist_comm]
  dist_triangle a b c := by
    exact_mod_cast (hΓ.preconnected a b).dist_triangle_left c
  eq_of_dist_eq_zero {a b} hab := by
    exact (hΓ.preconnected a b).dist_eq_zero_iff.mp (by exact_mod_cast hab)
lemma graphMetric_discrete (hΓ : Γ.Connected) (a b : Y) (hab : a ≠ b) :
    (1 : ℝ) ≤ (Γ.dist a b : ℝ) := by
  have hd : Γ.dist a b ≠ 0 := by
    intro he
    exact hab ((hΓ.preconnected a b).dist_eq_zero_iff.mp he)
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr hd
variable [DecidableEq Y] [Γ.LocallyFinite]
def neighborhood : ℕ → Y → Finset Y
  | 0, a => {a}
  | k+1, a => insert a ((Γ.neighborFinset a).biUnion (neighborhood k))
lemma walk_end_mem_neighborhood {a b : Y} (p : Γ.Walk a b) (k : ℕ)
    (hp : p.length ≤ k) : b ∈ neighborhood Γ k a := by
  induction k generalizing a b with
  | zero =>
    have he : a=b := p.eq_of_length_eq_zero (Nat.eq_zero_of_le_zero hp)
    simp [neighborhood,he]
  | succ k ih =>
    cases p with
    | nil => simp [neighborhood]
    | @cons a w b haw p =>
      apply Finset.mem_insert_of_mem
      apply Finset.mem_biUnion.mpr
      exact ⟨w,(Γ.mem_neighborFinset a w).mpr haw,ih p (by simpa using hp)⟩
lemma dist_le_mem_neighborhood (hΓ : Γ.Connected) {a b : Y} {k : ℕ}
    (hab : Γ.dist a b ≤ k) : b ∈ neighborhood Γ k a := by
  obtain ⟨p,_,hp⟩ := hΓ.exists_path_of_dist a b
  exact walk_end_mem_neighborhood Γ p k (hp ▸ hab)
omit [DecidableEq Y] [Γ.LocallyFinite] in
lemma connected_set_diameter (σ : Finset Y) {n : ℕ} (hcard : σ.card=n+1)
    (hc : (Γ.induce (σ : Set Y)).Connected) {a b : Y} (ha : a∈σ) (hb : b∈σ) :
    Γ.dist a b ≤ n := by
  obtain ⟨p,hp,_⟩ := hc.exists_path_of_dist ⟨a,ha⟩ ⟨b,hb⟩
  have hl := hp.length_lt
  have hl' : p.length < n+1 := by
    calc p.length < _ := hl
         _ = σ.card := Fintype.card_of_subtype σ (fun _ => Iff.rfl)
         _ = n+1 := hcard
  have hdist := SimpleGraph.dist_le (p.map (SimpleGraph.Embedding.induce (G := Γ) (σ : Set Y)).toHom)
  rw [SimpleGraph.Walk.length_map] at hdist
  exact hdist.trans (Nat.le_of_lt_succ hl')
lemma meeting_simplex_vertices (hΓ : Γ.Connected) {n : ℕ} (hn : 0<n)
    (c p : FinProbability Y) (σ : Finset Y) (hcard : σ.card=n+1)
    (hc : (Γ.induce (σ : Set Y)).Connected) (hp : p.coeff.support ⊆ σ)
    (s : ℝ) (hs : 0 ≤ s)
    (hball : @rho Y (graphMetric Γ hΓ).toPseudoMetricSpace n c p ≤ s) :
    σ ⊆ c.coeff.support.biUnion
      (neighborhood Γ (⌊s * Real.sqrt (n : ℝ)⌋₊+n)) := by
  let : MetricSpace Y := graphMetric Γ hΓ
  obtain ⟨a,ha,v,hv,hav⟩ := support_distance_rho hn c p
  have hle : (Γ.dist a v : ℝ) ≤ s * Real.sqrt (n : ℝ) := by
    change (Γ.dist a v : ℝ) ≤ Real.sqrt (n : ℝ) * rho n c p at hav
    calc _ ≤ Real.sqrt (n : ℝ) * rho n c p := hav
         _ ≤ Real.sqrt (n : ℝ) * s := mul_le_mul_of_nonneg_left hball (Real.sqrt_nonneg _)
         _ = _ := mul_comm _ _
  have hnat : Γ.dist a v ≤ ⌊s * Real.sqrt (n : ℝ)⌋₊ :=
    (Nat.le_floor_iff (mul_nonneg hs (Real.sqrt_nonneg _))).mpr hle
  intro w hw
  apply Finset.mem_biUnion.mpr
  refine ⟨a,ha,dist_le_mem_neighborhood Γ hΓ ?_⟩
  exact (hΓ.preconnected a v).dist_triangle_left w |>.trans
    (Nat.add_le_add hnat (connected_set_diameter Γ σ hcard hc (hp hv) hw))
theorem finitely_many_meeting_top_simplices (hΓ : Γ.Connected) {n : ℕ} (hn : 0<n)
    (tops : Set (Finset Y))
    (htop : ∀ σ∈tops, σ.card=n+1 ∧ (Γ.induce (σ : Set Y)).Connected)
    (c : FinProbability Y) (s : ℝ) (hs : 0 ≤ s) :
    {σ | σ∈tops ∧ ∃ p : FinProbability Y, p.coeff.support ⊆ σ ∧
      @rho Y (graphMetric Γ hΓ).toPseudoMetricSpace n c p ≤ s}.Finite := by
  let W := c.coeff.support.biUnion (neighborhood Γ (⌊s * Real.sqrt (n : ℝ)⌋₊+n))
  apply W.powerset.finite_toSet.subset
  rintro σ ⟨hσ,p,hp,hball⟩
  exact Finset.mem_powerset.mpr
    (meeting_simplex_vertices Γ hΓ hn c p σ (htop σ hσ).1 (htop σ hσ).2 hp s hs hball)
end
end Sparse.GraphGeometry
namespace Sparse
end Sparse
namespace Sparse.GraphGeometry
open Set Finset
open scoped BassTrace.Sparse Topology
variable {Y : Type*} [DecidableEq Y] (Γ : SimpleGraph Y) [Γ.LocallyFinite]
lemma finitely_many_top_simplices_at (hΓ : Γ.Connected) {n : ℕ}
    (tops : Set (Finset Y))
    (htop : ∀ σ ∈ tops, σ.card = n+1 ∧ (Γ.induce (σ : Set Y)).Connected) (v : Y) :
    {σ | σ ∈ tops ∧ v ∈ σ}.Finite := by
  apply (neighborhood Γ n v).powerset.finite_toSet.subset
  intro σ hσ
  apply Finset.mem_powerset.mpr
  intro w hw
  exact dist_le_mem_neighborhood Γ hΓ
    (connected_set_diameter Γ σ (htop σ hσ.1).1 (htop σ hσ.1).2 hσ.2 hw)
def affineRealization (tops : Set (Finset Y)) : Set (Y →₀ ℝ) :=
  ⋃ σ ∈ tops, probabilitySet σ
def affineProbability (tops : Set (Finset Y)) (v : affineRealization tops) : FinProbability Y where
  coeff := v.val
  nonneg := by
    obtain ⟨σ,_,hσ⟩ := Set.mem_iUnion₂.mp v.property
    exact hσ.1
  total := by
    obtain ⟨σ,_,hσ⟩ := Set.mem_iUnion₂.mp v.property
    simpa using hσ.2.1
omit [DecidableEq Y] in
@[simp] lemma affineProbability_coeff (tops : Set (Finset Y)) (v : affineRealization tops) :
    (affineProbability tops v).coeff = v.val := rfl
lemma locallyFinite_affine_top_simplices (hΓ : Γ.Connected) {n : ℕ}
    (tops : Set (Finset Y))
    (htop : ∀ σ ∈ tops, σ.card = n+1 ∧ (Γ.induce (σ : Set Y)).Connected) :
    LocallyFinite (fun σ : tops => {v : affineRealization tops | v.val ∈ probabilitySet σ.val}) := by
  intro p
  let q := affineProbability tops p
  obtain ⟨y,hy⟩ := q.coeff_support_nonempty
  have hpos : 0 < q.coeff y := lt_of_le_of_ne (q.nonneg y) (Finsupp.mem_support_iff.mp hy).symm
  let U : Set (affineRealization tops) := {v | 0 < v.val y}
  have hU : IsOpen U := isOpen_lt continuous_const
    ((coordinateCLM y).continuous.comp continuous_subtype_val)
  refine ⟨U,hU.mem_nhds hpos,?_⟩
  have hfin := finitely_many_top_simplices_at Γ hΓ tops htop y
  apply (hfin.preimage Subtype.val_injective.injOn).subset
  intro σ hσ
  obtain ⟨v,hv,hvU⟩ := hσ
  refine ⟨σ.property,hv.2.2 ?_⟩
  exact Finsupp.mem_support_iff.mpr (ne_of_gt hvU)
lemma continuous_affineProbability (hΓ : Γ.Connected) {n : ℕ} (hn : 0 < n)
    (tops : Set (Finset Y))
    (htop : ∀ σ ∈ tops, σ.card = n+1 ∧ (Γ.induce (σ : Set Y)).Connected) :
    letI := graphMetric Γ hΓ
    letI := FinProbability.rhoMetric n hn (graphMetric_discrete Γ hΓ)
    Continuous (affineProbability tops) := by
  let := graphMetric Γ hΓ
  let := FinProbability.rhoMetric n hn (graphMetric_discrete Γ hΓ)
  apply (locallyFinite_affine_top_simplices Γ hΓ tops htop).continuous
  · ext v
    simp only [Set.mem_iUnion,Set.mem_ofPred_eq,Set.mem_univ,iff_true]
    obtain ⟨σ,hσ,hv⟩ := Set.mem_iUnion₂.mp v.property
    exact ⟨⟨σ,hσ⟩,hv⟩
  · intro σ
    exact (geometric_simplex_compact σ.val).isClosed.preimage continuous_subtype_val
  · intro σ
    apply continuousOn_iff_continuous_domRestrict.mpr
    let f : {v : affineRealization tops | v.val ∈ probabilitySet σ.val} → probabilitySet σ.val :=
      fun v => ⟨v.val.val,v.property⟩
    have hf : Continuous f := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
    exact (continuous_simplexProbability σ.val n hn (graphMetric_discrete Γ hΓ)).comp hf
end Sparse.GraphGeometry
end BassTrace
end
end OAI

end
section
namespace OAI
noncomputable section
namespace BassTrace.Sparse.FinProbability
open Set Finset
variable {Y Z W : Type*}
def push (e : Y ≃ Z) (p : FinProbability Y) : FinProbability Z where
  coeff := Finsupp.equivMapDomain e p.coeff
  nonneg z := p.nonneg (e.symm z)
  total := by
    classical
    change ∑ z ∈ p.coeff.support.map e.toEmbedding, p.coeff (e.symm z) = 1
    rw [Finset.sum_map]
    simpa [Finsupp.sum] using p.total
@[simp] lemma push_coeff_apply (e : Y ≃ Z) (p : FinProbability Y) (z : Z) :
    (push e p).coeff z = p.coeff (e.symm z) := rfl
lemma push_support (e : Y ≃ Z) (p : FinProbability Y) :
    (push e p).coeff.support = p.coeff.support.map e.toEmbedding := rfl
@[simp] lemma push_refl (p : FinProbability Y) : push (Equiv.refl Y) p = p := by
  apply FinProbability.ext_coeff
  ext y
  rfl
@[simp] lemma push_symm_push (e : Y ≃ Z) (p : FinProbability Y) :
    push e.symm (push e p) = p := by
  apply FinProbability.ext_coeff
  ext y
  simp
lemma push_expectation (e : Y ≃ Z) (p : FinProbability Y) (f : Z → ℝ) :
    (push e p).expectation f = p.expectation (f ∘ e) := by
  classical
  unfold expectation Finsupp.sum
  rw [push_support,Finset.sum_map]
  simp
lemma push_gap (e : Y ≃ Z) (p q : FinProbability Y) (f : Z → ℝ) :
    (push e p).gap (push e q) f = p.gap q (f ∘ e) := by
  simp [gap,push_expectation]
lemma transport_push_le [PseudoMetricSpace Y] [PseudoMetricSpace Z]
    (e : Y ≃ Z) (he : LipschitzWith 1 e) (p q : FinProbability Y) :
    (push e p).transport (push e q) ≤ p.transport q := by
  apply transport_le
  intro f hf
  rw [push_gap]
  apply gap_le_transport
  simpa using hf.comp he
lemma transport_push [PseudoMetricSpace Y] [PseudoMetricSpace Z]
    (e : Y ≃ Z) (he : Isometry e) (p q : FinProbability Y) :
    (push e p).transport (push e q) = p.transport q := by
  apply le_antisymm (transport_push_le e he.lipschitzWith p q)
  have hei : Isometry e.symm := by
    intro z w
    simpa using (he (e.symm z) (e.symm w)).symm
  simpa using transport_push_le e.symm hei.lipschitzWith (push e p) (push e q)
lemma rho_push [PseudoMetricSpace Y] [PseudoMetricSpace Z]
    (e : Y ≃ Z) (he : Isometry e) (n : ℕ) (p q : FinProbability Y) :
    rho n (push e p) (push e q) = rho n p q := by
  simp [rho,transport_push e he]
end BassTrace.Sparse.FinProbability
namespace BassTrace.Sparse
open scoped Pointwise
variable {H Y : Type*} [Group H] [MulAction H Y]
scoped instance probabilityMulAction : MulAction H (FinProbability Y) where
  smul h p := p.push (MulAction.toPerm h)
  one_smul p := by
    apply FinProbability.ext_coeff
    ext y
    change p.coeff ((1 : H)⁻¹ • y) = p.coeff y
    simp
  mul_smul h k p := by
    apply FinProbability.ext_coeff
    ext y
    change p.coeff ((h * k)⁻¹ • y) = p.coeff (k⁻¹ • (h⁻¹ • y))
    simp [mul_smul]
open scoped BassTrace.Sparse
@[simp] lemma smul_probability_coeff (h : H) (p : FinProbability Y) (y : Y) :
    (h • p).coeff y = p.coeff (h⁻¹ • y) := rfl
lemma smul_probability_support (h : H) (p : FinProbability Y) :
    (h • p).coeff.support = p.coeff.support.map (MulAction.toPerm h).toEmbedding := rfl
lemma smul_probability_rho [PseudoMetricSpace Y]
    (hi : ∀ h : H, Isometry (fun y : Y => h • y))
    (h : H) (n : ℕ) (p q : FinProbability Y) :
    FinProbability.rho n (h • p) (h • q) = FinProbability.rho n p q :=
  FinProbability.rho_push (MulAction.toPerm h) (hi h) n p q
end BassTrace.Sparse
namespace BassTrace.Sparse.OrbitForms
open Set Finset
variable {H Y I : Type*} [Group H] [MulAction H Y]
def push (h : H) : (Y →₀ ℝ) ≃ₗ[ℝ] (Y →₀ ℝ) :=
  Finsupp.domLCongr (MulAction.toPerm h)
@[simp] lemma push_apply (h : H) (p : Y →₀ ℝ) (y : Y) :
    push h p y = p (h⁻¹ • y) := by rfl
@[simp] lemma push_one (p : Y →₀ ℝ) : push (1:H) p = p := by ext y; simp
lemma push_mul (h k : H) (p : Y →₀ ℝ) : push (h*k) p = push h (push k p) := by
  ext y
  simp [mul_smul]
@[simp] lemma push_inv_push (h : H) (p : Y →₀ ℝ) : push h⁻¹ (push h p) = p := by
  rw [← push_mul,inv_mul_cancel,push_one]
structure Data (I : Type*) (Y : Type*) where
  form : I → (Y →₀ ℝ) →ₗ[ℝ] ℝ
  support : I → Finset Y
  vanish : ∀ i p, (∀ y ∈ support i, p y = 0) → form i p = 0
variable (d : Data I Y)
def form (j : H × I) : (Y →₀ ℝ) →ₗ[ℝ] ℝ :=
  (d.form j.2).comp (push j.1⁻¹).toLinearMap
lemma form_translate (k h : H) (i : I) (p : Y →₀ ℝ) :
    form d (k*h,i) (push k p) = form d (h,i) p := by
  change d.form i (push (k*h)⁻¹ (push k p)) = d.form i (push h⁻¹ p)
  rw [mul_inv_rev,push_mul,push_inv_push]
lemma form_ne_zero_support {j : H × I} {p : Y →₀ ℝ} (hp : form d j p ≠ 0) :
    ∃ y ∈ d.support j.2, j.1 • y ∈ p.support := by
  by_contra! hh
  apply hp
  apply d.vanish
  intro y hy
  simpa using Finsupp.notMem_support_iff.mp (hh y hy)
variable [IsCancelSMul H Y]
lemma finite_form_ne_zero (i : I) (p : Y →₀ ℝ) :
    {h : H | form d (h,i) p ≠ 0}.Finite := by
  apply (Set.Finite.biUnion (d.support i).finite_toSet (fun y _ =>
    Set.Finite.preimage (fun h _ k _ he => IsCancelSMul.right_cancel h k y he)
      p.support.finite_toSet)).subset
  intro h hh
  obtain ⟨y,hy,hyp⟩ := form_ne_zero_support d hh
  exact Set.mem_iUnion₂.mpr ⟨y,hy,hyp⟩
variable [Fintype I]
lemma finite_relevant (s : Finset (Y →₀ ℝ)) :
    {j : H × I | ∃ p ∈ s, form d j p ≠ 0}.Finite := by
  classical
  have hi : (⋃ i : I, (fun h : H => (h,i)) ''
      (⋃ p ∈ (s : Set (Y →₀ ℝ)), {h : H | form d (h,i) p ≠ 0})).Finite := by
    apply Set.finite_iUnion
    intro i
    exact (Set.Finite.biUnion s.finite_toSet
      (fun p _ => finite_form_ne_zero d i p)).image _
  apply hi.subset
  rintro ⟨h,i⟩ ⟨p,hp,hh⟩
  exact Set.mem_iUnion.mpr ⟨i,h,Set.mem_iUnion₂.mpr ⟨p,hp,hh⟩,rfl⟩
def relevant (s : Finset (Y →₀ ℝ)) : Finset (H × I) := (finite_relevant d s).toFinset
@[simp] lemma mem_relevant (s : Finset (Y →₀ ℝ)) (j : H × I) :
    j ∈ relevant d s ↔ ∃ p ∈ s, form d j p ≠ 0 := by simp [relevant]
lemma irrelevant_vanish (s : Finset (Y →₀ ℝ)) (j : H × I)
    (hj : j ∉ relevant d s) : ∀ p ∈ convexHull ℝ (s : Set (Y →₀ ℝ)), form d j p = 0 := by
  have hs : (s : Set (Y →₀ ℝ)) ⊆ (form d j).ker := by
    intro p hp
    by_contra hh
    exact hj ((mem_relevant d s j).mpr ⟨p,hp,hh⟩)
  exact convexHull_min hs (form d j).ker.convex
lemma relevant_translate (k h : H) (i : I) (s : Finset (Y →₀ ℝ)) :
    (k*h,i) ∈ relevant d (s.map (push k).toEmbedding) ↔ (h,i) ∈ relevant d s := by
  simp only [mem_relevant]
  constructor
  · rintro ⟨p,hp,hh⟩
    obtain ⟨q,hq,rfl⟩ := Finset.mem_map.mp hp
    exact ⟨q,hq,by simpa [form_translate] using hh⟩
  · rintro ⟨p,hp,hh⟩
    exact ⟨push k p,Finset.mem_map.mpr ⟨p,hp,rfl⟩,by simpa [form_translate] using hh⟩
end BassTrace.Sparse.OrbitForms
namespace BassTrace.Sparse.BallOrbitForms
open Set Finset
open scoped BassTrace.Sparse
variable {H Y C : Type*} [Group H] [MulAction H Y] [MetricSpace Y]
variable (S : C → Finset Y) (c : C → FinProbability Y) (n : ℕ)
abbrev Index := Σ i : C, ↥(potentialVertices : Finset (S i → ℝ))
def data : OrbitForms.Data (Index S) Y where
  form j := (ballBranch (S j.1) (c j.1) n j.2.val).toLinearMap
  support j := S j.1
  vanish j p hp := by
    rw [ContinuousLinearMap.coe_coe,ballBranch_apply]
    apply Finset.sum_eq_zero
    intro y _
    rw [hp y y.property,mul_zero]
omit [MetricSpace Y] in
lemma push_coeff (h : H) (p : FinProbability Y) :
    OrbitForms.push h p.coeff = (h • p).coeff := by
  ext y
  rfl
lemma branch_apply (h : H) (j : Index S) (p : FinProbability Y) :
    OrbitForms.form (data S c n) (h,j) p.coeff =
      ballBranch (S j.1) (c j.1) n j.2.val (h⁻¹ • p).coeff := by
  change ballBranch (S j.1) (c j.1) n j.2.val (OrbitForms.push h⁻¹ p.coeff) = _
  rw [push_coeff]
lemma exists_maximizer (hi : ∀ h : H, Isometry (fun y : Y => h • y))
    (hc : ∀ i, (c i).coeff.support ⊆ S i) (h : H) (i : C)
    (p : FinProbability Y) (hp : (h⁻¹ • p).coeff.support ⊆ S i) :
    ∃ l : ↥(potentialVertices : Finset (S i → ℝ)),
      FinProbability.rho n (h • c i) p =
        OrbitForms.form (data S c n) (h,⟨i,l⟩) p.coeff ∧
      ∀ l' : ↥(potentialVertices : Finset (S i → ℝ)),
        OrbitForms.form (data S c n) (h,⟨i,l'⟩) p.coeff ≤
          FinProbability.rho n (h • c i) p := by
  have he : FinProbability.rho n (h • c i) p = FinProbability.rho n (c i) (h⁻¹ • p) := by
    simpa only [smul_inv_smul] using smul_probability_rho hi h n (c i) (h⁻¹ • p)
  obtain ⟨l,hl,heq,hmax⟩ := exists_ballBranch_maximizer (S i) (c i) (h⁻¹ • p) (hc i) hp n
  refine ⟨⟨l,hl⟩,?_,?_⟩
  · rw [branch_apply,he]
    exact heq
  · intro l'
    rw [branch_apply,he]
    exact hmax _ l'.property
lemma distance_eq_iff (hi : ∀ h : H, Isometry (fun y : Y => h • y))
    (hc : ∀ i, (c i).coeff.support ⊆ S i) (h : H) (i : C)
    (p : FinProbability Y) (hp : (h⁻¹ • p).coeff.support ⊆ S i) (t : ℝ) :
    FinProbability.rho n (h • c i) p = t ↔
      (∀ l : ↥(potentialVertices : Finset (S i → ℝ)),
        OrbitForms.form (data S c n) (h,⟨i,l⟩) p.coeff ≤ t) ∧
      ∃ l : ↥(potentialVertices : Finset (S i → ℝ)),
        OrbitForms.form (data S c n) (h,⟨i,l⟩) p.coeff = t := by
  obtain ⟨l,he,hm⟩ := exists_maximizer S c n hi hc h i p hp
  constructor
  · intro hh
    exact ⟨fun l' => hh ▸ hm l',l,he.symm.trans hh⟩
  · rintro ⟨hle,l',hlt⟩
    exact le_antisymm (he ▸ hle l) (hlt ▸ hm l')
end BassTrace.Sparse.BallOrbitForms
namespace BassTrace.Sparse.OrbitForms
open Set Finset
open scoped BassTrace.Sparse
variable {H Y I X : Type*} [Group H] [MulAction H Y] [IsCancelSMul H Y] [Fintype I]
variable (d : Data I Y) {t : ℝ} (ht : 0 < t)
def cuts : Cuts.UniversalCuts (Y →₀ ℝ) (H × I) where
  form := form d
  level := fun _ => t
  positive := fun _ => ht.le
  relevant := relevant d
  vanish := irrelevant_vanish d
variable [TopologicalSpace X] [MulAction H X]
def Equivariant {K : Geometry.SimplicialComplex ℝ (Y →₀ ℝ)}
    (T : Cuts.SubdivisionFamily X K) : Prop :=
  ∀ (k : H) (x : X) s, s ∈ (T.val x).complex.faces →
    s.map (push k).toEmbedding ∈ (T.val (k • x)).complex.faces
end BassTrace.Sparse.OrbitForms
end
end OAI

end
section
namespace OAI.BassTrace.Sparse.OrbitForms
open Set
variable {H I Y : Type*} [Group H] [MulAction H Y] [IsCancelSMul H Y] [Fintype I]
noncomputable section
open scoped Classical
def comparisons (d : Data I Y) : Data (I × I) Y where
  form j := d.form j.1 - d.form j.2
  support j := d.support j.1 ∪ d.support j.2
  vanish j p hp := by
    simp [d.vanish j.1 p (fun y hy => hp y (Finset.mem_union_left _ hy)),
      d.vanish j.2 p (fun y hy => hp y (Finset.mem_union_right _ hy))]
variable (d : Data I Y)
def winnerCuts : Cuts.UniversalCuts (Y →₀ ℝ) (H × (I × I)) where
  form := form (comparisons d)
  level := fun _ => 0
  positive := fun _ => le_rfl
  relevant := relevant (comparisons d)
  vanish := irrelevant_vanish (comparisons d)
end
end OAI.BassTrace.Sparse.OrbitForms
namespace OAI.BassTrace.Sparse.Cuts.Sequential
open Set
variable {V X J : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [TopologicalSpace X] [CompactSpace X] {K : Geometry.SimplicialComplex ℝ V}
theorem uniformRadius [Countable J] (T B : SubdivisionFamily X K) (hK : K.faces.Countable)
    (a : J → V → ℝ) {r R : ℝ} (h : r < R) :
    ∃ t ∈ Ioo r R, ∀ x j, ∀ v ∈ (T.val x).complex.vertices ∪ (B.val x).complex.vertices,
      a j v ≠ t := by
  let U := (⋃ x, (T.val x).complex.vertices) ∪ (⋃ x, (B.val x).complex.vertices)
  have hu : U.Countable := (T.countable_vertices hK).union (B.countable_vertices hK)
  have hb : (⋃ j, a j '' U).Countable := Set.countable_iUnion fun j => hu.image _
  obtain ⟨t,ht,hi⟩ := (hb.dense_compl ℝ).exists_mem_open isOpen_Ioo (nonempty_Ioo.mpr h)
  refine ⟨t,hi,?_⟩
  intro x j v hv he
  apply ht
  exact mem_iUnion.mpr ⟨j,v,hv.elim (fun hh => Or.inl (mem_iUnion.mpr ⟨x,hh⟩))
    (fun hh => Or.inr (mem_iUnion.mpr ⟨x,hh⟩)),he⟩
end OAI.BassTrace.Sparse.Cuts.Sequential
namespace OAI.BassTrace.Sparse.Cuts.UniversalCuts
noncomputable section
end
end OAI.BassTrace.Sparse.Cuts.UniversalCuts
end
section
namespace OAI
noncomputable section
namespace BassTrace
namespace Sparse
open Set
variable {H V I : Type*} [Group H] [PseudoMetricSpace V] [MulAction H V]
lemma finite_centers_of_compact {Q : Set V} (hQ : IsCompact Q) {r : ℝ} (hr : 0 < r) :
    ∃ C : Finset V, (C : Set V) ⊆ Q ∧ ∀ x ∈ Q, ∃ c ∈ C, dist x c < r := by
  classical
  obtain ⟨C,hC,hfin,hcov⟩ := hQ.elim_finite_subcover_image
    (b := Q) (c := fun c => Metric.ball c r) (fun _ _ => Metric.isOpen_ball) (by
      intro x hx
      exact Set.mem_iUnion₂.mpr ⟨x,hx,by simpa using hr⟩)
  refine ⟨hfin.toFinset,by simpa using hC,?_⟩
  intro x hx
  obtain ⟨c,hc,hxc⟩ := Set.mem_iUnion₂.mp (hcov hx)
  exact ⟨c,by simpa using hc,hxc⟩
theorem exists_finite_orbit_centers (S : Set V) (P : I → Set V) (F : Finset I)
    (hcompact : ∀ i ∈ F, IsCompact (P i)) (hPS : ∀ i ∈ F, P i ⊆ S)
    (hcover : ∀ x ∈ S, ∃ h : H, ∃ i ∈ F, ∃ y ∈ P i, h • y = x)
    (hisom : ∀ h : H, Isometry (fun x : V => h • x)) {r : ℝ} (hr : 0 < r) :
    ∃ C : Finset V, (C : Set V) ⊆ S ∧
      ∀ x ∈ S, ∃ h : H, ∃ c ∈ C, dist x (h • c) < r := by
  have hQ : IsCompact (⋃ i ∈ F, P i) := F.finite_toSet.isCompact_biUnion hcompact
  obtain ⟨C,hC,hcov⟩ := finite_centers_of_compact hQ hr
  refine ⟨C,?_,?_⟩
  · intro c hc
    obtain ⟨i,hi,hci⟩ := Set.mem_iUnion₂.mp (hC hc)
    exact hPS i hi hci
  · intro x hx
    obtain ⟨h,i,hi,y,hy,rfl⟩ := hcover x hx
    obtain ⟨c,hc,hyc⟩ := hcov y (Set.mem_iUnion₂.mpr ⟨i,hi,hy⟩)
    exact ⟨h,c,hc,by simpa only [(hisom h).dist_eq] using hyc⟩
end Sparse
namespace Sparse.GraphGeometry
open Set Finset
open scoped BassTrace.Sparse Classical
variable {Y : Type*} [DecidableEq Y]
lemma point_exists (K : PreAbstractSimplicialComplex Y)
    (v : (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space) :
    ∃ p : FinProbability Y, p.coeff = v.val ∧ p.coeff.support ∈ K.faces := by
  exact (show v.val ∈ {w | ∃ p : FinProbability Y, p.coeff=w ∧ p.coeff.support ∈ K.faces} from
    (onFinsupp_space K) ▸ v.property)
def pointProbability (K : PreAbstractSimplicialComplex Y)
    (v : (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space) : FinProbability Y :=
  Classical.choose (point_exists K v)
lemma pointProbability_coeff (K : PreAbstractSimplicialComplex Y)
    (v : (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space) :
    (pointProbability K v).coeff = v.val :=
  (Classical.choose_spec (point_exists K v)).1
lemma pointProbability_face (K : PreAbstractSimplicialComplex Y)
    (v : (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space) :
    (pointProbability K v).coeff.support ∈ K.faces :=
  (Classical.choose_spec (point_exists K v)).2
def supportPatch (K : PreAbstractSimplicialComplex Y) (W : Finset Y) : Set (Y →₀ ℝ) :=
  {v | v ∈ (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space ∧ v.support ⊆ W}
lemma supportPatch_marked (K : PreAbstractSimplicialComplex Y) (W : Finset Y) :
    Cuts.IsMarked (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K) (supportPatch K W) := by
  intro v hv
  obtain ⟨p,hp,hpK⟩ := (onFinsupp_space K) ▸ hv.1
  subst v
  refine ⟨p.coeff.support.image (fun y => Finsupp.single y (1:ℝ)),
    ⟨p.coeff.support,hpK,rfl⟩,?_,?_⟩
  · rw [Finset.coe_image,p.mem_geometric_simplex]
  · intro w hw
    have hw' := hw
    rw [Finset.coe_image,convexHull_single_eq_probabilitySet] at hw'
    exact ⟨(Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).convexHull_subset_space
      ⟨p.coeff.support,hpK,rfl⟩ hw,hw'.2.2.trans hv.2⟩
variable (Γ : SimpleGraph Y) [Γ.LocallyFinite]
def ballSupport (c : FinProbability Y) (n : ℕ) (R : ℝ) : Finset Y :=
  c.coeff.support ∪ c.coeff.support.biUnion
    (neighborhood Γ (⌊R * Real.sqrt (n : ℝ)⌋₊+n))
lemma ballSupport_center (c : FinProbability Y) (n : ℕ) (R : ℝ) :
    c.coeff.support ⊆ ballSupport Γ c n R := Finset.subset_union_left
lemma ballSupport_contains (hΓ : Γ.Connected) {n : ℕ} (hn : 0 < n)
    (K : PreAbstractSimplicialComplex Y)
    (hK : ∀ s ∈ K.faces, ∃ σ ∈ K.faces, s ⊆ σ ∧ σ.card=n+1 ∧
      (Γ.induce (σ : Set Y)).Connected)
    (c p : FinProbability Y) (hp : p.coeff.support ∈ K.faces)
    {R : ℝ} (hR : 0 ≤ R)
    (hball : @FinProbability.rho Y (graphMetric Γ hΓ).toPseudoMetricSpace n c p ≤ R) :
    p.coeff.support ⊆ ballSupport Γ c n R := by
  obtain ⟨σ,_,hs,hcard,hconn⟩ := hK _ hp
  exact hs.trans ((meeting_simplex_vertices Γ hΓ hn c p σ hcard hconn hs R hR hball).trans
    Finset.subset_union_right)
def originalTops (K : PreAbstractSimplicialComplex Y) (n : ℕ) : Set (Finset Y) :=
  {s | s ∈ K.faces ∧ s.card=n+1}
lemma onFinsupp_space_eq_affineRealization (K : PreAbstractSimplicialComplex Y) (n : ℕ)
    (hK : ∀ s ∈ K.faces, ∃ σ ∈ K.faces, s ⊆ σ ∧ σ.card=n+1) :
    (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space =
      affineRealization (originalTops K n) := by
  ext v
  rw [onFinsupp_space]
  constructor
  · rintro ⟨p,rfl,hp⟩
    obtain ⟨σ,hσ,hs,hcard⟩ := hK _ hp
    exact Set.mem_iUnion₂.mpr ⟨σ,⟨hσ,hcard⟩,p.nonneg,by simpa using p.total,hs⟩
  · intro hv
    obtain ⟨σ,hσ,hv⟩ := Set.mem_iUnion₂.mp hv
    rw [probabilitySet_eq] at hv
    obtain ⟨p,rfl,hp⟩ := hv
    exact ⟨p,rfl,(K.isRelLowerSet_faces hσ.1).2 hp p.coeff_support_nonempty⟩
lemma continuous_pointProbability (hΓ : Γ.Connected) {n : ℕ} (hn : 0 < n)
    (K : PreAbstractSimplicialComplex Y)
    (hK : ∀ s ∈ K.faces, ∃ σ ∈ K.faces, s ⊆ σ ∧ σ.card=n+1)
    (hconn : ∀ σ ∈ originalTops K n, (Γ.induce (σ : Set Y)).Connected) :
    letI := graphMetric Γ hΓ
    letI := FinProbability.rhoMetric n hn (graphMetric_discrete Γ hΓ)
    Continuous (pointProbability K) := by
  let := graphMetric Γ hΓ
  let := FinProbability.rhoMetric n hn (graphMetric_discrete Γ hΓ)
  let e : (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space →
      affineRealization (originalTops K n) := fun v =>
    ⟨v.val,(onFinsupp_space_eq_affineRealization K n hK) ▸ v.property⟩
  have he : Continuous e := continuous_subtype_val.subtype_mk _
  have hc := (continuous_affineProbability Γ hΓ hn (originalTops K n)
    (fun σ hσ => ⟨hσ.2,hconn σ hσ⟩)).comp he
  convert hc using 1
  funext v
  apply FinProbability.ext_coeff
  exact pointProbability_coeff K v
def centerDistance (hΓ : Γ.Connected) (K : PreAbstractSimplicialComplex Y)
    (n : ℕ) (c : FinProbability Y) (v : Y →₀ ℝ) : ℝ :=
  if hv : v ∈ (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space then
    @FinProbability.rho Y (graphMetric Γ hΓ).toPseudoMetricSpace n c (pointProbability K ⟨v,hv⟩)
  else 0
omit [Γ.LocallyFinite] in
lemma centerDistance_apply (hΓ : Γ.Connected) (K : PreAbstractSimplicialComplex Y)
    (n : ℕ) (c p : FinProbability Y) (hp : p.coeff.support ∈ K.faces) :
    centerDistance Γ hΓ K n c p.coeff =
      @FinProbability.rho Y (graphMetric Γ hΓ).toPseudoMetricSpace n c p := by
  have hv : p.coeff ∈ (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space := by
    rw [onFinsupp_space]
    exact ⟨p,rfl,hp⟩
  simp only [centerDistance,dite_eq_left hv]
  congr 1
  apply FinProbability.ext_coeff
  exact pointProbability_coeff K ⟨p.coeff,hv⟩
lemma continuousOn_centerDistance (hΓ : Γ.Connected) {n : ℕ} (hn : 0 < n)
    (K : PreAbstractSimplicialComplex Y)
    (hK : ∀ s ∈ K.faces, ∃ σ ∈ K.faces, s ⊆ σ ∧ σ.card=n+1)
    (hconn : ∀ σ ∈ originalTops K n, (Γ.induce (σ : Set Y)).Connected)
    (c : FinProbability Y) :
    ContinuousOn (centerDistance Γ hΓ K n c)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space := by
  let := graphMetric Γ hΓ
  let := FinProbability.rhoMetric n hn (graphMetric_discrete Γ hΓ)
  apply continuousOn_iff_continuous_domRestrict.mpr
  have hc := (continuous_const (y := c)).dist (continuous_pointProbability Γ hΓ hn K hK hconn)
  convert hc using 1
  funext v
  change centerDistance Γ hΓ K n c v.val = _
  simp only [centerDistance,dite_eq_left v.property]
  rfl
end Sparse.GraphGeometry
namespace Sparse.BallOrbitForms
open Set Finset
open scoped BassTrace.Sparse Classical
variable {H Y C : Type*} [Group H] [MulAction H Y] [DecidableEq Y] [MetricSpace Y]
variable (S : C → Finset Y) (c : C → FinProbability Y) (n : ℕ)
def branches (h : H) (i : C) : Finset (H × Index S) :=
  Finset.univ.image (fun l : ↥(potentialVertices : Finset (S i → ℝ)) => (h,⟨i,l⟩))
omit [Group H] [MulAction H Y] [DecidableEq Y] in
lemma mem_branches (h : H) (i : C) (j : H × Index S) :
    j ∈ branches S h i ↔ ∃ l : ↥(potentialVertices : Finset (S i → ℝ)), j=(h,⟨i,l⟩) := by
  simp [branches,eq_comm]
omit [DecidableEq Y] [MetricSpace Y] in
lemma inverse_support_iff (h : H) (p : FinProbability Y) (W : Finset Y) :
    (h⁻¹ • p).coeff.support ⊆ W ↔
      p.coeff.support ⊆ W.map (MulAction.toPerm h).toEmbedding := by
  have hh : p.coeff.support = (h⁻¹ • p).coeff.support.map (MulAction.toPerm h).toEmbedding := by
    rw [← smul_probability_support,smul_inv_smul]
  rw [hh,Finset.map_subset_map]
def translatedPatch (K : PreAbstractSimplicialComplex Y) (h : H) (i : C) : Set (Y →₀ ℝ) :=
  GraphGeometry.supportPatch K ((S i).map (MulAction.toPerm h).toEmbedding)
omit [MetricSpace Y] in
lemma translatedPatch_marked (K : PreAbstractSimplicialComplex Y) (h : H) (i : C) :
    Cuts.IsMarked (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K)
      (translatedPatch S K h i) := GraphGeometry.supportPatch_marked _ _
omit [MetricSpace Y] in
lemma translatedPatch_mem (K : PreAbstractSimplicialComplex Y) (h : H) (i : C)
    (p : FinProbability Y) :
    p.coeff ∈ translatedPatch S K h i ↔
      p.coeff ∈ (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space ∧
        (h⁻¹ • p).coeff.support ⊆ S i := by
  exact and_congr_right fun _ => (inverse_support_iff h p (S i)).symm
variable [IsCancelSMul H Y] [Fintype C]
lemma spherePatch_mem (hi : ∀ h : H, Isometry (fun y : Y => h • y))
    (hc : ∀ i, (c i).coeff.support ⊆ S i)
    (K : PreAbstractSimplicialComplex Y) (h : H) (i : C) (p : FinProbability Y)
    {t : ℝ} (ht : 0<t) :
    p.coeff ∈ ((OrbitForms.cuts (H := H) (data S c n) ht).spherePatch
        (translatedPatch S K h i) (branches S h i)) ↔
      p.coeff ∈ translatedPatch S K h i ∧ FinProbability.rho n (h • c i) p=t := by
  change (p.coeff ∈ translatedPatch S K h i ∧
      ∀ j ∈ branches S h i, OrbitForms.form (data S c n) j p.coeff ≤ t) ∧
      (∃ j ∈ branches S h i, OrbitForms.form (data S c n) j p.coeff=t) ↔ _
  constructor
  · rintro ⟨⟨hp,hle⟩,j,hj,he⟩
    obtain ⟨l,rfl⟩ := (mem_branches S h i j).mp hj
    refine ⟨hp,(distance_eq_iff S c n hi hc h i p ((translatedPatch_mem S K h i p).mp hp).2 t).mpr ?_⟩
    exact ⟨fun l' => hle _ ((mem_branches S h i _).mpr ⟨l',rfl⟩),l,he⟩
  · rintro ⟨hp,he⟩
    obtain ⟨hle,l,hl⟩ := (distance_eq_iff S c n hi hc h i p
      ((translatedPatch_mem S K h i p).mp hp).2 t).mp he
    refine ⟨⟨hp,?_⟩,(h,⟨i,l⟩),(mem_branches S h i _).mpr ⟨l,rfl⟩,hl⟩
    intro j hj
    obtain ⟨l',rfl⟩ := (mem_branches S h i j).mp hj
    exact hle l'
end Sparse.BallOrbitForms
namespace Sparse.GraphGeometry
open Set Finset
open scoped BassTrace.Sparse Classical
section
variable {H Y C : Type*} [Group H] [MulAction H Y] [IsCancelSMul H Y]
  [DecidableEq Y] [Fintype C]
variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)
variable [mY : MetricSpace Y] (hm : mY = graphMetric Γ hΓ)
variable {n : ℕ} (hn : 0<n) (K : PreAbstractSimplicialComplex Y)
variable (hK : ∀ s ∈ K.faces, ∃ σ ∈ K.faces, s ⊆ σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)
variable (hact : ∀ (h : H) s, s ∈ K.faces → s.map (MulAction.toPerm h).toEmbedding ∈ K.faces)
variable (hi : ∀ h : H, Isometry (fun y : Y => h • y))
include hn hK hact hi hm
omit [IsCancelSMul H Y] [Fintype C] in
lemma ballSupport_inverse (c : C → FinProbability Y) (h : H) (i : C)
    (p : FinProbability Y) (hp : p.coeff.support ∈ K.faces)
    {R : ℝ} (hR : 0≤R) (hball : FinProbability.rho n (h • c i) p ≤ R) :
    (h⁻¹ • p).coeff.support ⊆ ballSupport Γ (c i) n R := by
  subst mY
  let := graphMetric Γ hΓ
  have hp' : (h⁻¹ • p).coeff.support ∈ K.faces := by
    rw [smul_probability_support]
    exact hact h⁻¹ _ hp
  apply ballSupport_contains Γ hΓ hn K hK _ _ hp' hR
  have he := smul_probability_rho hi h⁻¹ n (h • c i) p
  rw [inv_smul_smul] at he
  rw [he]
  exact hball
lemma sphere_eq_patch (c : C → FinProbability Y) (h : H) (i : C)
    {R t : ℝ} (hR : 0≤R) (ht : 0<t) (htR : t≤R) :
    let S := fun i => ballSupport Γ (c i) n R
    (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space ∩
        {v | centerDistance Γ hΓ K n (h • c i) v=t} =
      (OrbitForms.cuts (H := H) (BallOrbitForms.data S c n) ht).spherePatch
        (BallOrbitForms.translatedPatch S K h i) (BallOrbitForms.branches S h i) := by
  subst mY
  let := graphMetric Γ hΓ
  let S := fun i => ballSupport Γ (c i) n R
  ext v
  constructor
  · rintro ⟨hv,he⟩
    change centerDistance Γ hΓ K n (h • c i) v = t at he
    let p := pointProbability K ⟨v,hv⟩
    have hp : p.coeff = v := pointProbability_coeff K _
    have hpK := pointProbability_face K ⟨v,hv⟩
    have he' : FinProbability.rho n (h • c i) p=t := by
      rw [← hp,centerDistance_apply Γ hΓ K n _ p hpK] at he
      exact he
    rw [← hp]
    apply (BallOrbitForms.spherePatch_mem S c n hi (fun i => ballSupport_center Γ (c i) n R) K h i p ht).mpr
    refine ⟨(BallOrbitForms.translatedPatch_mem S K h i p).mpr ⟨hp.symm ▸ hv,?_⟩,he'⟩
    exact ballSupport_inverse Γ hΓ rfl hn K hK hact hi c h i p hpK hR (he' ▸ htR)
  · intro hv
    have hvK : v ∈ (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space := hv.1.1.1
    let p := pointProbability K ⟨v,hvK⟩
    have hp : p.coeff=v := pointProbability_coeff K _
    rw [← hp] at hv ⊢
    obtain ⟨_,he⟩ := (BallOrbitForms.spherePatch_mem S c n hi
      (fun i => ballSupport_center Γ (c i) n R) K h i p ht).mp hv
    refine ⟨hp.symm ▸ hvK,?_⟩
    change centerDistance Γ hΓ K n (h • c i) p.coeff = t
    rw [centerDistance_apply Γ hΓ K n _ p (pointProbability_face K ⟨v,hvK⟩)]
    exact he
end
section
variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y]
variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)
variable [mY : MetricSpace Y] (hm : mY = graphMetric Γ hΓ)
variable {n : ℕ} (hn : 0<n) (K : PreAbstractSimplicialComplex Y)
def realizationDistance (n : ℕ) (p q : Y →₀ ℝ) : ℝ :=
  if hp : p ∈ (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space then
    if hq : q ∈ (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space then
      @FinProbability.rho Y (graphMetric Γ hΓ).toPseudoMetricSpace n
        (pointProbability K ⟨p,hp⟩) (pointProbability K ⟨q,hq⟩)
    else 0
  else 0
omit [Γ.LocallyFinite] [MetricSpace Y] in
lemma realizationDistance_apply (n : ℕ) (p q : FinProbability Y)
    (hp : p.coeff.support ∈ K.faces) (hq : q.coeff.support ∈ K.faces) :
    realizationDistance Γ hΓ K n p.coeff q.coeff =
      @FinProbability.rho Y (graphMetric Γ hΓ).toPseudoMetricSpace n p q := by
  have hp' : p.coeff ∈ (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space :=
    (onFinsupp_space K).symm ▸ ⟨p,rfl,hp⟩
  have hq' : q.coeff ∈ (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space :=
    (onFinsupp_space K).symm ▸ ⟨q,rfl,hq⟩
  simp only [realizationDistance,dite_eq_left hp',dite_eq_left hq']
  congr 1 <;> apply FinProbability.ext_coeff <;> exact pointProbability_coeff K _
omit [Γ.LocallyFinite] [MetricSpace Y] in
lemma realizationDistance_center_triangle (n : ℕ) (c : FinProbability Y)
    (p : Y →₀ ℝ) (hp : p ∈ (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space)
    (q : Y →₀ ℝ) (hq : q ∈ (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space) :
    realizationDistance Γ hΓ K n p q ≤ centerDistance Γ hΓ K n c p +
      centerDistance Γ hΓ K n c q := by
  let := graphMetric Γ hΓ
  simp only [realizationDistance,centerDistance,dite_eq_left hp,dite_eq_left hq]
  exact (FinProbability.rho_triangle n _ c _).trans_eq (by rw [FinProbability.rho_comm n _ c])
omit [DecidableEq Y] [Γ.LocallyFinite] in
include hm hn in
lemma exists_orbit_center_cover
    (hi : ∀ h : H, Isometry (fun y : Y => h • y))
    (F : Finset (Finset Y)) (hF : ∀ s ∈ F, s ∈ K.faces)
    (hrep : ∀ s ∈ K.faces, ∃ h : H, ∃ τ ∈ F, s = τ.map (MulAction.toPerm h).toEmbedding)
    {r : ℝ} (hr : 0<r) :
    ∃ C : Finset (FinProbability Y), (∀ c ∈ C, c.coeff.support ∈ K.faces) ∧
      ∀ p : FinProbability Y, p.coeff.support ∈ K.faces →
        ∃ h : H, ∃ c ∈ C, FinProbability.rho n p (h • c) < r := by
  subst mY
  let := graphMetric Γ hΓ
  let := FinProbability.rhoMetric n hn (graphMetric_discrete Γ hΓ)
  let S : Set (FinProbability Y) := {p | p.coeff.support ∈ K.faces}
  let P : Finset Y → Set (FinProbability Y) := fun s => {p | p.coeff.support ⊆ s}
  obtain ⟨C,hC,hcov⟩ := exists_finite_orbit_centers (H := H) S P F
    (fun s _ => isCompact_probability_simplex s n hn (graphMetric_discrete Γ hΓ))
    (fun s hs p hp => (K.isRelLowerSet_faces (hF s hs)).2 hp p.coeff_support_nonempty)
    (by
      intro p hp
      obtain ⟨h,τ,hτ,he⟩ := hrep p.coeff.support hp
      refine ⟨h,τ,hτ,h⁻¹ • p,?_,smul_inv_smul h p⟩
      change (h⁻¹ • p).coeff.support ⊆ τ
      rw [BallOrbitForms.inverse_support_iff]
      exact he.subset)
    (fun h => Isometry.of_dist_eq (fun p q => smul_probability_rho hi h n p q)) hr
  exact ⟨C,hC,hcov⟩
end
variable {H Y : Type*} [Group H] [MulAction H Y] [DecidableEq Y]
variable (K : PreAbstractSimplicialComplex Y)
variable (hact : ∀ (h : H) s, s ∈ K.faces → s.map (MulAction.toPerm h).toEmbedding ∈ K.faces)
include hact in
lemma space_push (h : H) (v : Y →₀ ℝ)
    (hv : v ∈ (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space) :
    OrbitForms.push h v ∈ (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space := by
  obtain ⟨p,rfl,hp⟩ := (onFinsupp_space K) ▸ hv
  rw [BallOrbitForms.push_coeff,onFinsupp_space]
  refine ⟨h • p,rfl,?_⟩
  rw [smul_probability_support]
  exact hact h _ hp
include hact in
lemma centerDistance_push (Γ : SimpleGraph Y) (hΓ : Γ.Connected)
    (hi : ∀ h : H, @Isometry Y Y (graphMetric Γ hΓ).toPseudoEMetricSpace
      (graphMetric Γ hΓ).toPseudoEMetricSpace (fun y => h • y))
    (n : ℕ) (h : H) (c : FinProbability Y) (v : Y →₀ ℝ)
    (hv : v ∈ (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space) :
    centerDistance Γ hΓ K n (h • c) (OrbitForms.push h v) =
      centerDistance Γ hΓ K n c v := by
  let := graphMetric Γ hΓ
  obtain ⟨p,rfl,hp⟩ := (onFinsupp_space K) ▸ hv
  have hhp : (h • p).coeff.support ∈ K.faces := by
    rw [smul_probability_support]
    exact hact h _ hp
  rw [BallOrbitForms.push_coeff,centerDistance_apply Γ hΓ K n _ _ hhp,
    centerDistance_apply Γ hΓ K n _ _ hp]
  exact smul_probability_rho hi h n c p
end Sparse.GraphGeometry
namespace Sparse.OrbitForms
open scoped BassTrace.Sparse
variable {H Y X : Type*} [Group H] [MulAction H Y] [TopologicalSpace X] [MulAction H X]
def MarkedEquivariant {K : Geometry.SimplicialComplex ℝ (Y →₀ ℝ)}
    {T : Cuts.SubdivisionFamily X K} (P : Cuts.MarkedFamily T) : Prop :=
  ∀ (k : H) (x : X) v, v ∈ P.val x → push k v ∈ P.val (k • x)
end Sparse.OrbitForms
end BassTrace
end
end OAI

end
section
namespace OAI
noncomputable section
namespace BassTrace
namespace Sparse.GraphGeometry
open Set Finset
open scoped BassTrace.Sparse Classical
section
variable {H Y C X : Type*} [Group H] [MulAction H Y] [IsCancelSMul H Y]
  [Countable H] [Countable Y] [DecidableEq Y] [Fintype C]
  [TopologicalSpace X] [CompactSpace X] [MulAction H X]
variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)
variable [mY : MetricSpace Y] (hm : mY = graphMetric Γ hΓ)
variable {n : ℕ} (hn : 0<n) (K : PreAbstractSimplicialComplex Y)
variable (hK : ∀ s ∈ K.faces, ∃ σ ∈ K.faces, s ⊆ σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)
variable (hact : ∀ (h : H) s, s ∈ K.faces → s.map (MulAction.toPerm h).toEmbedding ∈ K.faces)
variable (hi : ∀ h : H, Isometry (fun y : Y => h • y))
omit [Group H] [MulAction H Y] [IsCancelSMul H Y] [Countable H] [Fintype C]
    [TopologicalSpace X] [CompactSpace X] [MulAction H X]
    [Γ.LocallyFinite] [MetricSpace Y] in
lemma onFinsupp_faces_countable :
    (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).faces.Countable := by
  change (Finset.image (fun y => Finsupp.single y (1:ℝ)) '' K.faces).Countable
  exact (Set.to_countable K.faces).image _
end
end Sparse.GraphGeometry
namespace Sparse.OrbitForms
open Set Finset
variable {H Y X : Type*} [Group H] [MulAction H Y] [TopologicalSpace X] [MulAction H X]
structure MarkedPair (K : Geometry.SimplicialComplex ℝ (Y →₀ ℝ)) where
  T : Cuts.SubdivisionFamily X K
  P : Cuts.MarkedFamily T
  equivariant : Equivariant (H := H) T
  markedEquivariant : MarkedEquivariant (H := H) P
structure SeparatingFiltration (K : Geometry.SimplicialComplex ℝ (Y →₀ ℝ))
    (ρ : (Y →₀ ℝ) → (Y →₀ ℝ) → ℝ) (R : ℝ) (n : ℕ) where
  pair : ℕ → MarkedPair (H := H) (X := X) K
  top : ∀ x, ((pair n).T.val x).complex = K
  top_space : ∀ x, (pair n).P.val x = K.space
  finer : ∀ i, i < n → ∀ x,
    Cuts.Refines (((pair i).T.val x).complex) (((pair (i+1)).T.val x).complex)
  nested : ∀ i, i < n → ∀ x, (pair i).P.val x ⊆ (pair (i+1)).P.val x
  drop : ∀ i, i < n → ∀ x,
    Cuts.DimensionDrop (((pair (i+1)).T.val x).complex) (((pair i).T.val x).complex)
      ((pair (i+1)).P.val x) ((pair i).P.val x)
  diameter : ∀ i, i < n → ∀ x,
    Cuts.ComponentDiameter ρ ((pair (i+1)).P.val x \ (pair i).P.val x) (2*R)
def SeparatingFiltration.point {K : Geometry.SimplicialComplex ℝ (Y →₀ ℝ)}
    {ρ : (Y →₀ ℝ) → (Y →₀ ℝ) → ℝ} {R : ℝ} {n : ℕ}
    (Q : SeparatingFiltration (H := H) (X := X) K ρ R n) (x : X) :
    Cuts.PointFiltration K n where
  T := fun i => ((Q.pair i).T.val x).complex
  Z := fun i => (Q.pair i).P.val x
  top := Q.top x
  top_space := Q.top_space x
  marked := fun i _ => (Q.pair i).P.marked x
  finer := fun i hi => Q.finer i hi x
  nested := fun i hi => Q.nested i hi x
  drop := fun i hi => Q.drop i hi x
end Sparse.OrbitForms
namespace Sparse.GraphGeometry
open Set Finset
open scoped BassTrace.Sparse Classical
variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y]
  [TopologicalSpace X] [MulAction H X]
variable (K : PreAbstractSimplicialComplex Y)
variable (hact : ∀ (h : H) s, s ∈ K.faces → s.map (MulAction.toPerm h).toEmbedding ∈ K.faces)
include hact in
lemma onFinsupp_faces_push (h : H) (s : Finset (Y →₀ ℝ))
    (hs : s ∈ (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).faces) :
    s.map (OrbitForms.push h).toEmbedding ∈
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).faces := by
  obtain ⟨t,ht,rfl⟩ := hs
  refine ⟨t.map (MulAction.toPerm h).toEmbedding,hact h t ht,?_⟩
  simp only [Finset.map_eq_image,Finset.image_image]
  congr 1
  funext y
  exact (Finsupp.domLCongr_single (R := ℝ) (MulAction.toPerm h) y (1 : ℝ)).symm
def originalMarkedPair
    (hact : ∀ (h : H) s, s ∈ K.faces → s.map (MulAction.toPerm h).toEmbedding ∈ K.faces) :
    OrbitForms.MarkedPair (H := H) (X := X)
    (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K) where
  T := {
    val := fun _ => Cuts.Subdivision.original _
    localConstancy := fun _ _ => IsLocallyConstant.of_constant _ (fun _ _ => rfl) }
  P := {
    val := fun _ => (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space
    marked := fun _ => Cuts.isMarked_space _
    localConstancy := fun _ _ => IsLocallyConstant.of_constant _ (fun _ _ => rfl) }
  equivariant := fun h _ s hs => onFinsupp_faces_push K hact h s hs
  markedEquivariant := fun h _ v hv => space_push K hact h v hv
end Sparse.GraphGeometry
end BassTrace
end
end OAI

end
section
namespace OAI
namespace BassTrace.Sparse
open MeasureTheory Set
open scoped ENNReal
def standardSolidSimplex (n : ℕ) : Set (Fin n → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1}
def l1UnitPolytope (n : ℕ) : Set (Fin n → ℝ) := {x | ∑ i, |x i| ≤ 1}
def signReflection {n : ℕ} (ε : Fin n → Bool) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => if ε i then x i else -x i
def signChamber {n : ℕ} (ε : Fin n → Bool) : Set (Fin n → ℝ) :=
  signReflection ε ⁻¹' standardSolidSimplex n
lemma measurableSet_standardSolidSimplex (n : ℕ) :
    MeasurableSet (standardSolidSimplex n) := by
  change MeasurableSet ({x : Fin n → ℝ | ∀ i, 0 ≤ x i} ∩ {x | ∑ i, x i ≤ 1})
  apply MeasurableSet.inter
  · simp only [ofPred_forall]
    exact MeasurableSet.iInter fun i =>
      (show MeasurableSet {x : Fin n → ℝ | 0 ≤ x i} from
        measurableSet_le measurable_const (measurable_pi_apply i))
  · exact measurableSet_le (by fun_prop) measurable_const
lemma signReflection_measurePreserving {n : ℕ} (ε : Fin n → Bool) :
    MeasurePreserving (signReflection ε) := by
  unfold signReflection
  apply volume_preserving_pi (f := fun i t => if ε i then t else -t)
  intro i
  cases h : ε i
  · simpa only [h, Bool.false_eq_true, ↓reduceIte] using
      (Measure.measurePreserving_neg (volume : Measure ℝ))
  · simp only [↓reduceIte]
    exact MeasurePreserving.id (volume : Measure ℝ)
lemma measurableSet_signChamber {n : ℕ} (ε : Fin n → Bool) :
    MeasurableSet (signChamber ε) :=
  (signReflection_measurePreserving ε).measurable (measurableSet_standardSolidSimplex n)
lemma volume_signChamber {n : ℕ} (ε : Fin n → Bool) :
    volume (signChamber ε) = volume (standardSolidSimplex n) :=
  (signReflection_measurePreserving ε).measure_preimage
    (measurableSet_standardSolidSimplex n).nullMeasurableSet
lemma signChamber_mem_iff {n : ℕ} (ε : Fin n → Bool) (x : Fin n → ℝ) :
    x ∈ signChamber ε ↔
      (∀ i, if ε i then 0 ≤ x i else x i ≤ 0) ∧ x ∈ l1UnitPolytope n := by
  change ((∀ i, 0 ≤ if ε i then x i else -x i) ∧
    ∑ i, (if ε i then x i else -x i) ≤ 1) ↔ _
  have hcond : (∀ i, 0 ≤ if ε i then x i else -x i) ↔
      (∀ i, if ε i then 0 ≤ x i else x i ≤ 0) := by
    apply forall_congr'
    intro i
    cases ε i <;> simp
  rw [hcond]
  constructor
  · rintro ⟨h,hx⟩
    refine ⟨h,?_⟩
    change ∑ i, |x i| ≤ 1
    convert hx using 1
    apply Finset.sum_congr rfl
    intro i _
    have hi := h i
    cases he : ε i <;> simp only [he, ↓reduceIte] at hi ⊢
    · exact abs_of_nonpos hi
    · exact abs_of_nonneg hi
  · rintro ⟨h,hx⟩
    refine ⟨h,?_⟩
    change ∑ i, |x i| ≤ 1 at hx
    convert hx using 1
    apply Finset.sum_congr rfl
    intro i _
    have hi := h i
    cases he : ε i <;> simp only [he, ↓reduceIte] at hi ⊢
    · exact (abs_of_nonpos hi).symm
    · exact (abs_of_nonneg hi).symm
lemma union_signChamber (n : ℕ) :
    (⋃ ε : Fin n → Bool, signChamber ε) = l1UnitPolytope n := by
  classical
  ext x
  simp only [mem_iUnion,signChamber_mem_iff]
  constructor
  · rintro ⟨ε,_,hx⟩
    exact hx
  · intro hx
    refine ⟨fun i => decide (0 ≤ x i),?_,hx⟩
    intro i
    by_cases hi : 0 ≤ x i
    · simp [hi]
    · simp [hi, (not_le.mp hi).le]
lemma signChamber_aedisjoint {n : ℕ} :
    Pairwise (fun ε η : Fin n → Bool =>
      AEDisjoint (volume : Measure (Fin n → ℝ)) (signChamber ε) (signChamber η)) := by
  intro ε η hne
  obtain ⟨i,hi⟩ := Function.ne_iff.mp hne
  change volume (signChamber ε ∩ signChamber η) = 0
  apply measure_mono_null (t := {x | x i = 0})
  · intro x hx
    have hε := ((signChamber_mem_iff ε x).mp hx.1).1 i
    have hη := ((signChamber_mem_iff η x).mp hx.2).1 i
    cases he : ε i <;> cases hh : η i <;> simp_all <;> linarith
  · exact Measure.pi_hyperplane (fun _ : Fin n => (volume : Measure ℝ)) i 0
lemma volume_l1UnitPolytope (n : ℕ) :
    volume (l1UnitPolytope n) = ENNReal.ofReal ((2 : ℝ)^n / n.factorial) := by
  cases n with
  | zero =>
    have he : l1UnitPolytope 0 = Set.univ := by ext x; simp [l1UnitPolytope]
    rw [he, Measure.volume_pi_eq_dirac (fun i : Fin 0 => Fin.elim0 i)]
    simp
  | succ n =>
    have h := volume_sum_rpow_le (Fin (n+1)) (p := 1) (by norm_num) 1
    norm_num only [div_one, Real.rpow_one, Fintype.card_fin, ENNReal.ofReal_one,
      one_pow,one_mul] at h
    rw [Real.Gamma_two, mul_one, Real.Gamma_nat_eq_factorial] at h
    exact h
theorem volume_standardSolidSimplex (n : ℕ) :
    volume (standardSolidSimplex n) = ENNReal.ofReal (1 / (n.factorial : ℝ)) := by
  have hsum := measure_iUnion₀ (signChamber_aedisjoint (n := n))
    (fun ε => (measurableSet_signChamber ε).nullMeasurableSet)
  rw [union_signChamber, volume_l1UnitPolytope] at hsum
  simp only [volume_signChamber,tsum_fintype,Finset.sum_const,Finset.card_univ,
    Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,nsmul_eq_mul,
    Nat.cast_pow,Nat.cast_ofNat] at hsum
  have hc : (2 : ℝ≥0∞)^n ≠ 0 := by positivity
  have hf : (2 : ℝ≥0∞)^n ≠ ⊤ := by finiteness
  apply (ENNReal.mul_right_inj hc hf).mp
  rw [← hsum]
  conv_rhs => rw [show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by norm_num]
  rw [← ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring
end BassTrace.Sparse
end OAI

end
section
namespace OAI
namespace BassTrace.Sparse
section
open SimpleGraph
noncomputable def treeEdgeEquiv {n : ℕ} (Γ : SimpleGraph (Fin (n+1)))
    (hΓ : Γ.IsTree) : Fin n ≃ Γ.edgeSet := by
  classical
  apply Fintype.equivOfCardEq
  have h := hΓ.card_edgeFinset
  rw [Γ.edgeFinset_card, Fintype.card_fin] at h
  simp only [Fintype.card_fin]
  omega
def rootCoordinate {n : ℕ} (v : Fin (n+1)) : Fin n → ℤ :=
  fun i => if i.succ=v then 1 else 0
lemma rootCoordinate_zero (n : ℕ) : rootCoordinate (0 : Fin (n+1)) = 0 := by
  ext i
  simp [rootCoordinate]
lemma rootCoordinate_succ {n : ℕ} (v : Fin n) :
    rootCoordinate v.succ = Pi.single v 1 := by
  ext i
  simp [rootCoordinate,Pi.single_apply,eq_comm]
noncomputable def treeIncidence {n : ℕ} (Γ : SimpleGraph (Fin (n+1)))
    (hΓ : Γ.IsTree) : Matrix (Fin n) (Fin n) ℤ := fun i j =>
  rootCoordinate ((treeEdgeEquiv Γ hΓ j).val.out.1) i -
  rootCoordinate ((treeEdgeEquiv Γ hΓ j).val.out.2) i
lemma adjacent_difference_mem_span {n : ℕ} (Γ : SimpleGraph (Fin (n+1)))
    (hΓ : Γ.IsTree) {u v : Fin (n+1)} (huv : Γ.Adj u v) :
    rootCoordinate u - rootCoordinate v ∈
      Submodule.span ℤ (Set.range (treeIncidence Γ hΓ).col) := by
  classical
  let e : Γ.edgeSet := ⟨s(u,v),huv⟩
  let j := (treeEdgeEquiv Γ hΓ).symm e
  have hj : treeEdgeEquiv Γ hΓ j = e := (treeEdgeEquiv Γ hΓ).apply_symm_apply e
  have hc := Submodule.subset_span (R := ℤ) (Set.mem_range_self
    (f := (treeIncidence Γ hΓ).col) j)
  have he : s(e.val.out.1,e.val.out.2) = s(u,v) := e.val.out_eq
  rcases Sym2.eq_iff.mp he with h | h
  · have heq : rootCoordinate u - rootCoordinate v = (treeIncidence Γ hΓ).col j := by
      ext i
      simp [Matrix.col,treeIncidence,hj,h.1,h.2]
    rw [heq]
    exact hc
  · have heq : rootCoordinate u - rootCoordinate v = -(treeIncidence Γ hΓ).col j := by
      ext i
      simp [Matrix.col,treeIncidence,hj,h.1,h.2]
    rw [heq]
    exact Submodule.neg_mem _ hc
lemma walk_difference_mem_span {n : ℕ} (Γ : SimpleGraph (Fin (n+1)))
    (hΓ : Γ.IsTree) {u v : Fin (n+1)} (p : Γ.Walk u v) :
    rootCoordinate u - rootCoordinate v ∈
      Submodule.span ℤ (Set.range (treeIncidence Γ hΓ).col) := by
  induction p with
  | nil => simp
  | @cons u v w huv p ih =>
    have h := Submodule.add_mem _ (adjacent_difference_mem_span Γ hΓ huv) ih
    convert h using 1
    abel
lemma treeIncidence_span {n : ℕ} (Γ : SimpleGraph (Fin (n+1)))
    (hΓ : Γ.IsTree) : Submodule.span ℤ (Set.range (treeIncidence Γ hΓ).col) = ⊤ := by
  classical
  apply Submodule.eq_top_iff'.mpr
  intro x
  have hsingle (i : Fin n) : Pi.single i (1 : ℤ) ∈
      Submodule.span ℤ (Set.range (treeIncidence Γ hΓ).col) := by
    obtain ⟨p⟩ := hΓ.connected.preconnected i.succ 0
    simpa only [rootCoordinate_zero,sub_zero,rootCoordinate_succ] using
      walk_difference_mem_span Γ hΓ p
  have hx : x = ∑ i, x i • Pi.single i (1 : ℤ) := by
    ext j
    simp [Finset.sum_apply,Pi.single_apply]
  rw [hx]
  exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ (x i) (hsingle i))
theorem treeIncidence_isUnit_det {n : ℕ} (Γ : SimpleGraph (Fin (n+1)))
    (hΓ : Γ.IsTree) : IsUnit (treeIncidence Γ hΓ).det := by
  classical
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply Matrix.mulVec_surjective_iff_isUnit.mp
  apply (LinearMap.range_eq_top (f := (treeIncidence Γ hΓ).mulVecLin)).mp
  rw [Matrix.range_mulVecLin,treeIncidence_span]
theorem treeIncidence_abs_real_det {n : ℕ} (Γ : SimpleGraph (Fin (n+1)))
    (hΓ : Γ.IsTree) : |((treeIncidence Γ hΓ).map (Int.castRingHom ℝ)).det| = 1 := by
  classical
  change |((treeIncidence Γ hΓ).map (fun x => (x : ℝ))).det| = 1
  rw [← Int.cast_det]
  rcases Int.isUnit_iff.mp (treeIncidence_isUnit_det Γ hΓ) with h | h <;> simp [h]
open MeasureTheory Set
noncomputable def realTreeIncidence {n : ℕ} (Γ : SimpleGraph (Fin (n+1)))
    (hΓ : Γ.IsTree) : Matrix (Fin n) (Fin n) ℝ :=
  (treeIncidence Γ hΓ).map (Int.castRingHom ℝ)
lemma realTreeIncidence_det_ne_zero {n : ℕ} (Γ : SimpleGraph (Fin (n+1)))
    (hΓ : Γ.IsTree) : (realTreeIncidence Γ hΓ).det ≠ 0 := by
  intro h
  have hh := treeIncidence_abs_real_det Γ hΓ
  change |(realTreeIncidence Γ hΓ).det| = 1 at hh
  rw [h,abs_zero] at hh
  exact zero_ne_one hh
theorem treeChart_measurePreserving {n : ℕ} (Γ : SimpleGraph (Fin (n+1)))
    (hΓ : Γ.IsTree) : MeasurePreserving (Matrix.toLin' (realTreeIncidence Γ hΓ)) := by
  refine ⟨(Matrix.toLin' (realTreeIncidence Γ hΓ)).continuous_of_finiteDimensional.measurable,?_⟩
  rw [Real.map_matrix_volume_pi_eq_smul_volume_pi (realTreeIncidence_det_ne_zero Γ hΓ)]
  have hh := treeIncidence_abs_real_det Γ hΓ
  change |(realTreeIncidence Γ hΓ).det| = 1 at hh
  rw [abs_inv,hh,inv_one,ENNReal.ofReal_one,one_smul]
noncomputable def treeGradient {n : ℕ} (Γ : SimpleGraph (Fin (n+1)))
    (hΓ : Γ.IsTree) (ℓ : Fin (n+1) → ℝ) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun j =>
    (ℓ ((treeEdgeEquiv Γ hΓ j).val.out.1) - ℓ ((treeEdgeEquiv Γ hΓ j).val.out.2)) /
      Real.sqrt n)
lemma treeGradient_norm_le_one {n : ℕ} (hn : 0 < n)
    (Γ : SimpleGraph (Fin (n+1))) (hΓ : Γ.IsTree) (ℓ : Fin (n+1) → ℝ)
    (hℓ : ∀ u v, Γ.Adj u v → |ℓ u - ℓ v| ≤ 1) :
    ‖treeGradient Γ hΓ ℓ‖ ≤ 1 := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  apply (sq_le_sq₀ (norm_nonneg _) zero_le_one).mp
  rw [EuclideanSpace.real_norm_sq_eq]
  calc
    ∑ i, ((treeGradient Γ hΓ ℓ).ofLp i)^2 ≤ ∑ _i : Fin n, (1 : ℝ) / n := by
      apply Finset.sum_le_sum
      intro j _
      dsimp [treeGradient]
      rw [div_pow,Real.sq_sqrt hnR.le]
      apply div_le_div_of_nonneg_right _ hnR.le
      have hj := hℓ ((treeEdgeEquiv Γ hΓ j).val.out.1)
        ((treeEdgeEquiv Γ hΓ j).val.out.2)
        (by
          change s((treeEdgeEquiv Γ hΓ j).val.out.1,
            (treeEdgeEquiv Γ hΓ j).val.out.2) ∈ Γ.edgeSet
          have he : s((treeEdgeEquiv Γ hΓ j).val.out.1,
            (treeEdgeEquiv Γ hΓ j).val.out.2) = (treeEdgeEquiv Γ hΓ j).val :=
              (treeEdgeEquiv Γ hΓ j).val.out_eq
          rw [he]
          exact (treeEdgeEquiv Γ hΓ j).property)
      simpa only [sq_abs,one_pow] using
        (sq_le_sq₀ (abs_nonneg _) zero_le_one).mpr hj
    _ = 1^2 := by simp [ne_of_gt hnR]
lemma rootCoordinate_potential {n : ℕ} (ℓ : Fin (n+1) → ℝ) (v : Fin (n+1)) :
    (∑ i, (ℓ i.succ - ℓ 0) * (rootCoordinate v i : ℝ)) = ℓ v - ℓ 0 := by
  induction v using Fin.cases with
  | zero => simp [rootCoordinate_zero]
  | succ v => simp [rootCoordinate_succ,Pi.single_apply]
lemma treeChart_potential {n : ℕ} (Γ : SimpleGraph (Fin (n+1)))
    (hΓ : Γ.IsTree) (ℓ : Fin (n+1) → ℝ) (x : Fin n → ℝ) :
    (∑ i, (ℓ i.succ - ℓ 0) * ((Matrix.toLin' (realTreeIncidence Γ hΓ)) x) i) /
      Real.sqrt n =
    ∑ j, (treeGradient Γ hΓ ℓ).ofLp j * x j := by
  simp only [Matrix.toLin'_apply,Matrix.mulVec, dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [realTreeIncidence,Matrix.map_apply,treeIncidence,map_sub]
  have hcol (j : Fin n) :
      (∑ i, (ℓ i.succ - ℓ 0) *
        (((rootCoordinate ((treeEdgeEquiv Γ hΓ j).val.out.1) i : ℝ) -
          (rootCoordinate ((treeEdgeEquiv Γ hΓ j).val.out.2) i : ℝ)) * x j)) =
      (ℓ ((treeEdgeEquiv Γ hΓ j).val.out.1) -
        ℓ ((treeEdgeEquiv Γ hΓ j).val.out.2)) * x j := by
    simp only [← mul_assoc,← Finset.sum_mul,mul_sub,Finset.sum_sub_distrib,
      rootCoordinate_potential]
    ring
  change (∑ j, ∑ i, (ℓ i.succ - ℓ 0) *
    (((rootCoordinate ((treeEdgeEquiv Γ hΓ j).val.out.1) i : ℝ) -
      (rootCoordinate ((treeEdgeEquiv Γ hΓ j).val.out.2) i : ℝ)) * x j)) /
        Real.sqrt n = _
  simp_rw [hcol]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  dsimp [treeGradient]
  ring
noncomputable def treeSolidSimplex {n : ℕ} (Γ : SimpleGraph (Fin (n+1)))
    (hΓ : Γ.IsTree) : Set (Fin n → ℝ) :=
  (Matrix.toLin' (realTreeIncidence Γ hΓ)) ⁻¹' standardSolidSimplex n
lemma treeSolidSimplex_volume {n : ℕ} (Γ : SimpleGraph (Fin (n+1)))
    (hΓ : Γ.IsTree) : volume (treeSolidSimplex Γ hΓ) =
      ENNReal.ofReal (1 / (n.factorial : ℝ)) := by
  rw [treeSolidSimplex, (treeChart_measurePreserving Γ hΓ).measure_preimage
    (measurableSet_standardSolidSimplex n).nullMeasurableSet,
    volume_standardSolidSimplex]
end
open MeasureTheory Set Finset
open scoped ENNReal
noncomputable section
def barycentricParam {n : ℕ} (x : Fin n → ℝ) : Fin (n+1) → ℝ :=
  Fin.cases (1-∑ i, x i) x
@[simp] lemma barycentricParam_zero {n : ℕ} (x : Fin n → ℝ) :
    barycentricParam x 0 = 1-∑ i, x i := rfl
@[simp] lemma barycentricParam_succ {n : ℕ} (x : Fin n → ℝ) (i : Fin n) :
    barycentricParam x i.succ = x i := rfl
lemma sum_barycentricParam {n : ℕ} (x : Fin n → ℝ) :
    ∑ i, barycentricParam x i = 1 := by
  rw [Fin.sum_univ_succ]
  simp
lemma barycentricParam_injective (n : ℕ) :
    Function.Injective (@barycentricParam n) := by
  intro x y h
  funext i
  exact congrFun h i.succ
lemma range_barycentricParam (n : ℕ) :
    Set.range (@barycentricParam n) = {p | ∑ i, p i = 1} := by
  ext p
  constructor
  · rintro ⟨x,rfl⟩
    exact sum_barycentricParam x
  · intro hp
    refine ⟨fun i => p i.succ,?_⟩
    funext v
    induction v using Fin.cases with
    | zero =>
      change 1 - ∑ i : Fin n, p i.succ = p 0
      change ∑ i, p i = 1 at hp
      rw [Fin.sum_univ_succ] at hp
      linarith
    | succ v => rfl
lemma continuous_barycentricParam (n : ℕ) : Continuous (@barycentricParam n) := by
  apply continuous_pi
  intro i
  induction i using Fin.cases with
  | zero => exact continuous_const.sub (continuous_finsetSum _ fun _ _ => continuous_apply _)
  | succ i => exact continuous_apply i
def treeParam {n : ℕ} (T : SimpleGraph (Fin (n+1))) (hT : T.IsTree)
    (x : EuclideanSpace ℝ (Fin n)) : Fin (n+1) → ℝ :=
  barycentricParam (Matrix.toLin' (realTreeIncidence T hT) x.ofLp)
lemma treeParam_injective {n : ℕ} (T : SimpleGraph (Fin (n+1))) (hT : T.IsTree) :
    Function.Injective (treeParam T hT) := by
  intro x y h
  apply WithLp.ofLp_injective
  have he := barycentricParam_injective n h
  apply Matrix.mulVec_injective_iff_isUnit.mpr _ he
  exact (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (realTreeIncidence_det_ne_zero T hT))
lemma range_treeParam {n : ℕ} (T : SimpleGraph (Fin (n+1))) (hT : T.IsTree) :
    Set.range (treeParam T hT) = {p | ∑ i, p i = 1} := by
  have hsurj : Function.Surjective (fun x : EuclideanSpace ℝ (Fin n) =>
      Matrix.toLin' (realTreeIncidence T hT) x.ofLp) := by
    apply Function.Surjective.comp _ (WithLp.ofLp_surjective 2)
    exact Matrix.mulVec_surjective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (realTreeIncidence_det_ne_zero T hT)))
  rw [← range_barycentricParam n]
  exact hsurj.range_comp _
lemma continuous_treeParam {n : ℕ} (T : SimpleGraph (Fin (n+1))) (hT : T.IsTree) :
    Continuous (treeParam T hT) :=
  (continuous_barycentricParam n).comp
    ((Matrix.toLin' (realTreeIncidence T hT)).continuous_of_finiteDimensional.comp (PiLp.continuous_ofLp _ _))
def treeArea {n : ℕ} (T : SimpleGraph (Fin (n+1))) (hT : T.IsTree)
    (j : ℕ) (Q : Set (Fin (n+1) → ℝ)) : ℝ≥0∞ :=
  μHE[j] ((treeParam T hT) ⁻¹' Q)
lemma treeArea_mono {n : ℕ} (T : SimpleGraph (Fin (n+1))) (hT : T.IsTree)
    (j : ℕ) {Q W : Set (Fin (n+1) → ℝ)} (h : Q ⊆ W) :
    treeArea T hT j Q ≤ treeArea T hT j W := measure_mono (Set.preimage_mono h)
def fullBarycentricSimplex (n : ℕ) : Set (Fin (n+1) → ℝ) :=
  {p | (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1}
lemma barycentricParam_mem_simplex {n : ℕ} (x : Fin n → ℝ) :
    barycentricParam x ∈ fullBarycentricSimplex n ↔ x ∈ standardSolidSimplex n := by
  simp only [fullBarycentricSimplex,Set.mem_ofPred_eq,sum_barycentricParam,and_true]
  constructor
  · intro h
    exact ⟨fun i => h i.succ,by have hh := h 0; dsimp at hh; linarith⟩
  · rintro ⟨hx,hs⟩ i
    induction i using Fin.cases with
    | zero => change 0 ≤ 1-∑ i,x i; linarith
    | succ i => exact hx i
lemma treeArea_top_simplex {n : ℕ} (T : SimpleGraph (Fin (n+1))) (hT : T.IsTree) :
    treeArea T hT n (fullBarycentricSimplex n) = ENNReal.ofReal (1/(n.factorial : ℝ)) := by
  have he : (treeParam T hT) ⁻¹' fullBarycentricSimplex n =
      WithLp.ofLp ⁻¹' treeSolidSimplex T hT := by
    ext x
    exact barycentricParam_mem_simplex _
  rw [treeArea,he,EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
  rw [(PiLp.volume_preserving_ofLp (Fin n)).measure_preimage]
  · exact treeSolidSimplex_volume T hT
  · exact ((measurableSet_standardSolidSimplex n).preimage
      (Matrix.toLin' (realTreeIncidence T hT)).continuous_of_finiteDimensional.measurable).nullMeasurableSet
lemma hausdorff_zero_eq_count {E : Type*} [MetricSpace E] [MeasurableSpace E]
    [BorelSpace E] (Q : Set E) : μH[0] Q = Measure.count Q := by
  classical
  have hf (s : Finset E) : μH[0] (s : Set E) = (s.card : ℝ≥0∞) := by
    rw [← sum_measure_singleton]
    simp
  by_cases hQ : Q.Finite
  · rw [← hQ.coe_toFinset,hf,Measure.count_apply_finset]
  · rw [Measure.count_apply_infinite hQ]
    apply top_unique
    apply le_of_tendsto' ENNReal.tendsto_nat_nhds_top
    intro n
    obtain ⟨s,hs,hcard⟩ := Set.Infinite.exists_subset_card_eq hQ n
    calc
      (n : ℝ≥0∞) = μH[0] (s : Set E) := by rw [hf,hcard]
      _ ≤ μH[0] Q := measure_mono hs
lemma treeArea_zero {n : ℕ} (T : SimpleGraph (Fin (n+1))) (hT : T.IsTree)
    (Q : Set (Fin (n+1) → ℝ)) (hQ : Q ⊆ {p | ∑ i, p i=1}) :
    treeArea T hT 0 Q = Measure.count Q := by
  rw [treeArea,Measure.euclideanHausdorffMeasure_zero,hausdorff_zero_eq_count]
  rw [← Measure.count_injective_image (treeParam_injective T hT)]
  rw [Set.image_preimage_eq_inter_range,range_treeParam,Set.inter_eq_self_of_subset_left hQ]
def SpanningTree {n : ℕ} (Γ : SimpleGraph (Fin (n+1))) :=
  {T : SimpleGraph (Fin (n+1)) // T ≤ Γ ∧ T.IsTree}
instance {n : ℕ} (Γ : SimpleGraph (Fin (n+1))) : Fintype (SpanningTree Γ) := by
  classical
  unfold SpanningTree
  infer_instance
lemma nonempty_spanningTree {n : ℕ} {Γ : SimpleGraph (Fin (n+1))} (hΓ : Γ.Connected) :
    Nonempty (SpanningTree Γ) := by
  obtain ⟨T,hT,hTree⟩ := hΓ.exists_isTree_le
  exact ⟨⟨T,hT,hTree⟩⟩
def simplexArea {n : ℕ} (Γ : SimpleGraph (Fin (n+1)))
    (j : ℕ) (Q : Set (Fin (n+1) → ℝ)) : ℝ≥0∞ :=
  (∑ T : SpanningTree Γ, treeArea T.val T.property.2 j Q) / Fintype.card (SpanningTree Γ)
lemma simplexArea_mono {n : ℕ} (Γ : SimpleGraph (Fin (n+1)))
    (j : ℕ) {Q W : Set (Fin (n+1) → ℝ)} (h : Q ⊆ W) :
    simplexArea Γ j Q ≤ simplexArea Γ j W := by
  apply ENNReal.div_le_div_right
  exact Finset.sum_le_sum fun T _ => treeArea_mono T.val T.property.2 j h
lemma simplexArea_top_simplex {n : ℕ} (Γ : SimpleGraph (Fin (n+1))) (hΓ : Γ.Connected) :
    simplexArea Γ n (fullBarycentricSimplex n) = ENNReal.ofReal (1/(n.factorial : ℝ)) := by
  let := nonempty_spanningTree hΓ
  simp only [simplexArea,treeArea_top_simplex,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  rw [mul_comm]; exact ENNReal.mul_div_cancel_right (by exact_mod_cast Fintype.card_ne_zero) (by finiteness)
lemma simplexArea_zero {n : ℕ} (Γ : SimpleGraph (Fin (n+1))) (hΓ : Γ.Connected)
    (Q : Set (Fin (n+1) → ℝ)) (hQ : Q ⊆ {p | ∑ i, p i=1}) :
    simplexArea Γ 0 Q = Measure.count Q := by
  let := nonempty_spanningTree hΓ
  simp only [simplexArea,treeArea_zero _ _ Q hQ,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  rw [mul_comm]; exact ENNReal.mul_div_cancel_right (by exact_mod_cast Fintype.card_ne_zero) (by finiteness)
end
end BassTrace.Sparse
end OAI

end
section
namespace OAI
noncomputable section
namespace BassTrace.Sparse
open MeasureTheory Set Finset
open scoped ENNReal
section
def treeMatrixEquiv {n : ℕ} (T : SimpleGraph (Fin (n+1))) (hT : T.IsTree) :
    (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) :=
  LinearEquiv.ofBijective (Matrix.toLin' (realTreeIncidence T hT))
    ⟨Matrix.mulVec_injective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (realTreeIncidence_det_ne_zero T hT))),
     Matrix.mulVec_surjective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (realTreeIncidence_det_ne_zero T hT)))⟩
def independentCoordinates (n : ℕ) : (Fin (n+1) → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
  toFun p := fun i => p i.succ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def treeCoordinates {n : ℕ} (T : SimpleGraph (Fin (n+1))) (hT : T.IsTree) :
    (Fin (n+1) → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
  (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm.toLinearMap.comp
    ((treeMatrixEquiv T hT).symm.toLinearMap.comp (independentCoordinates n))
@[simp] lemma treeCoordinates_treeParam {n : ℕ} (T : SimpleGraph (Fin (n+1))) (hT : T.IsTree)
    (x : EuclideanSpace ℝ (Fin n)) : treeCoordinates T hT (treeParam T hT x) = x := by
  change (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm
    ((treeMatrixEquiv T hT).symm ((treeMatrixEquiv T hT) x.ofLp)) = x
  simp
lemma treeParam_treeCoordinates {n : ℕ} (T : SimpleGraph (Fin (n+1))) (hT : T.IsTree)
    (p : Fin (n+1) → ℝ) (hp : ∑ i,p i=1) : treeParam T hT (treeCoordinates T hT p) = p := by
  obtain ⟨x,rfl⟩ := (show p ∈ Set.range (treeParam T hT) by rw [range_treeParam]; exact hp)
  rw [treeCoordinates_treeParam]
lemma treeParam_preimage_eq_image {n : ℕ} (T : SimpleGraph (Fin (n+1))) (hT : T.IsTree)
    (Q : Set (Fin (n+1) → ℝ)) (hQ : Q ⊆ {p | ∑ i,p i=1}) :
    treeParam T hT ⁻¹' Q = treeCoordinates T hT '' Q := by
  ext x
  constructor
  · intro hx
    exact ⟨treeParam T hT x,hx,treeCoordinates_treeParam T hT x⟩
  · rintro ⟨p,hp,rfl⟩
    simpa only [Set.mem_preimage,treeParam_treeCoordinates T hT p (hQ hp)] using hp
lemma convex_sum_one (n : ℕ) : Convex ℝ {p : Fin (n+1) → ℝ | ∑ i,p i=1} := by
  intro x hx y hy a b _ _ hab
  change ∑ i,(a • x + b • y) i = 1
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,Finset.sum_add_distrib,← Finset.mul_sum]
  change ∑ i,x i=1 at hx
  change ∑ i,y i=1 at hy
  rw [hx,hy]
  simpa using hab
lemma treeParam_preimage_simplex {n : ℕ} (T : SimpleGraph (Fin (n+1))) (hT : T.IsTree)
    (s : Finset (Fin (n+1) → ℝ)) (hs : ∀ p ∈ s, ∑ i,p i=1) :
    treeParam T hT ⁻¹' convexHull ℝ (s : Set (Fin (n+1) → ℝ)) =
      convexHull ℝ (treeCoordinates T hT '' (s : Set (Fin (n+1) → ℝ))) := by
  rw [treeParam_preimage_eq_image T hT _ (convexHull_min (by exact hs) (convex_sum_one n))]
  exact (treeCoordinates T hT).toAffineMap.image_convexHull _
end
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma euclideanArea_eq_zero_of_dimH_lt {Q : Set E} {d : ℕ}
    (h : dimH Q < (d : ℝ≥0∞)) : μHE[d] Q = 0 := by
  have hh : μH[(d : ℝ)] Q = 0 := by
    apply hausdorffMeasure_of_dimH_lt (d := (d : NNReal))
    simpa using h
  rw [Measure.euclideanHausdorffMeasure_def,Measure.smul_apply,hh,smul_zero]
lemma euclideanArea_simplex_lt_top (s : Finset E) {d : ℕ} (hsd : s.card ≤ d+1) :
    μHE[d] (convexHull ℝ (s : Set E)) < ∞ := by
  classical
  by_cases hs : s.Nonempty
  · let Q := convexHull ℝ (s : Set E)
    let W := vectorSpan ℝ Q
    have hspan : W = vectorSpan ℝ (s : Set E) := by
      dsimp [W,Q]
      rw [← direction_affineSpan,affineSpan_convexHull,direction_affineSpan]
    have hdim : Module.finrank ℝ W ≤ d := by
      rw [hspan]
      have hc : Fintype.card s = (s.card-1)+1 := by
        rw [Fintype.card_coe]
        have := Finset.card_pos.mpr hs
        omega
      have hr := finrank_vectorSpan_range_le ℝ ((↑) : s → E) hc
      rw [Subtype.range_coe_subtype] at hr
      exact hr.trans (by omega)
    have hQcv : Convex ℝ Q := convex_convexHull ℝ _
    have hQne : Q.Nonempty := convexHull_nonempty_iff.mpr (Finset.coe_nonempty.mpr hs)
    rcases lt_or_eq_of_le hdim with hlt|heq
    · rw [euclideanArea_eq_zero_of_dimH_lt (by
        rw [Real.Convex.dimH_eq_finrank_vectorSpan hQcv hQne]
        exact_mod_cast hlt)]
      exact ENNReal.zero_lt_top
    · obtain ⟨c,hc⟩ := hQne
      let f : W → E := fun w => (w : E)+c
      have hf : Isometry f := by
        apply Isometry.of_dist_eq
        intro u v
        simp only [f,dist_add_right,Subtype.dist_eq]
      have hQr : Q ⊆ Set.range f := by
        intro p hp
        refine ⟨⟨p-c,vsub_mem_vectorSpan ℝ hp hc⟩,?_⟩
        dsimp [f]
        abel
      have hcompact : IsCompact (f ⁻¹' Q) :=
        hf.isClosedEmbedding.isCompact_preimage (s.finite_toSet.isCompact_convexHull (𝕜 := ℝ))
      have hh := hf.euclideanHausdorffMeasure_preimage (d := d) Q
      rw [Set.inter_eq_self_of_subset_left hQr] at hh
      rw [← hh,← heq,InnerProductSpace.euclideanHausdorffMeasure_eq_volume]
      exact hcompact.measure_lt_top
  · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    simp [he]
lemma treeArea_simplex_lt_top {n : ℕ} (T : SimpleGraph (Fin (n+1))) (hT : T.IsTree)
    (s : Finset (Fin (n+1) → ℝ)) (hs : ∀ p ∈ s, ∑ i,p i=1)
    {j : ℕ} (hc : s.card ≤ j+1) :
    treeArea T hT j (convexHull ℝ (s : Set (Fin (n+1) → ℝ))) < ∞ := by
  classical
  unfold treeArea
  rw [treeParam_preimage_simplex T hT s hs]
  rw [← Finset.coe_image]
  exact euclideanArea_simplex_lt_top _ ((Finset.card_image_le).trans hc)
lemma treeArea_iUnion_le {n : ℕ} (T : SimpleGraph (Fin (n+1))) (hT : T.IsTree)
    {I : Type*} (s : Finset I) (Q : I → Set (Fin (n+1) → ℝ)) (j : ℕ) :
    treeArea T hT j (⋃ i ∈ s, Q i) ≤ ∑ i ∈ s, treeArea T hT j (Q i) := by
  simp only [treeArea,Set.preimage_iUnion]
  exact measure_biUnion_finset_le s _
lemma treeArea_polyhedral_lt_top {n : ℕ} (T : SimpleGraph (Fin (n+1))) (hT : T.IsTree)
    (F : Finset (Finset (Fin (n+1) → ℝ))) {j : ℕ}
    (hs : ∀ s ∈ F, ∀ p ∈ s, ∑ i,p i=1) (hc : ∀ s ∈ F, s.card ≤ j+1)
    {Q : Set (Fin (n+1) → ℝ)}
    (hQ : Q ⊆ ⋃ s ∈ F, convexHull ℝ (s : Set (Fin (n+1) → ℝ))) :
    treeArea T hT j Q < ∞ := by
  exact lt_of_le_of_lt ((treeArea_mono T hT j hQ).trans (treeArea_iUnion_le T hT F _ j))
    (ENNReal.sum_lt_top.mpr fun s h => treeArea_simplex_lt_top T hT s (hs s h) (hc s h))
lemma simplexArea_polyhedral_lt_top {n : ℕ} (Γ : SimpleGraph (Fin (n+1))) (hΓ : Γ.Connected)
    (F : Finset (Finset (Fin (n+1) → ℝ))) {j : ℕ}
    (hs : ∀ s ∈ F, ∀ p ∈ s, ∑ i,p i=1) (hc : ∀ s ∈ F, s.card ≤ j+1)
    {Q : Set (Fin (n+1) → ℝ)}
    (hQ : Q ⊆ ⋃ s ∈ F, convexHull ℝ (s : Set (Fin (n+1) → ℝ))) :
    simplexArea Γ j Q < ∞ := by
  classical
  let := nonempty_spanningTree hΓ
  unfold simplexArea
  apply ENNReal.div_lt_top
  · exact ne_of_lt (ENNReal.sum_lt_top.mpr fun T _ => treeArea_polyhedral_lt_top T.val T.property.2 F hs hc hQ)
  · exact_mod_cast Fintype.card_ne_zero
end BassTrace.Sparse
end
end OAI

end
section
namespace OAI
noncomputable section
namespace BassTrace
namespace Sparse.Cuts
open Set Finset MeasureTheory
open scoped ENNReal
variable {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace X] {K : Geometry.SimplicialComplex ℝ V}
variable {T : SubdivisionFamily X K} (P : MarkedFamily T)
lemma MarkedFamily.trace_space (s : Finset V) (hs : s ∈ K.faces) (x : X) :
    (restrictComplex (geometricRestriction (T.val x).complex (P.val x))
      (convexHull ℝ (s : Set V))).space = P.val x ∩ convexHull ℝ (s : Set V) := by
  rw [restrictComplex_space_of_respects, (P.marked x).restriction_space]
  intro t ht
  exact (T.val x).respects s hs t ht.1
lemma MarkedFamily.localConstancy_inter (s : Finset V) (hs : s ∈ K.faces)
    (W : Set V) (hW : W ⊆ convexHull ℝ (s : Set V)) :
    IsLocallyConstant (fun x => P.val x ∩ W) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro x
  filter_upwards [(P.localConstancy s hs).eventually_eq x] with y hy
  have he : P.val y ∩ convexHull ℝ (s : Set V) = P.val x ∩ convexHull ℝ (s : Set V) := by
    rw [← P.trace_space s hs y, ← P.trace_space s hs x]
    congr 1
    exact Geometry.SimplicialComplex.ext hy
  have he' := congrArg (fun Q : Set V => Q ∩ W) he
  simpa only [Set.inter_assoc,Set.inter_eq_self_of_subset_right hW] using he'
def MarkedFamily.localArea {n : ℕ} (Γ : SimpleGraph (Fin (n+1)))
    (η : V →ₗ[ℝ] (Fin (n+1) → ℝ)) (W : Set V) (j : ℕ) (x : X) : ℝ≥0∞ :=
  simplexArea Γ j (η '' (P.val x ∩ W))
lemma MarkedFamily.localArea_locallyConstant {n : ℕ} (Γ : SimpleGraph (Fin (n+1)))
    (η : V →ₗ[ℝ] (Fin (n+1) → ℝ)) (s : Finset V) (hs : s ∈ K.faces)
    (W : Set V) (hW : W ⊆ convexHull ℝ (s : Set V)) (j : ℕ) :
    IsLocallyConstant (P.localArea Γ η W j) :=
  (P.localConstancy_inter s hs W hW).comp (fun Q => simplexArea Γ j (η '' Q))
lemma MarkedFamily.localArea_lt_top {n : ℕ} (Γ : SimpleGraph (Fin (n+1))) (hΓ : Γ.Connected)
    (η : V →ₗ[ℝ] (Fin (n+1) → ℝ)) (s : Finset V) (hs : s ∈ K.faces)
    (hη : ∀ p ∈ convexHull ℝ (s : Set V), ∑ i, η p i=1)
    (W : Set V) (hW : W ⊆ convexHull ℝ (s : Set V)) (j : ℕ) (x : X)
    (hd : ∀ t ∈ (T.val x).complex.faces,
      convexHull ℝ (t : Set V) ⊆ P.val x → t.card ≤ j+1) :
    P.localArea Γ η W j x < ∞ := by
  classical
  let L := restrictComplex (geometricRestriction (T.val x).complex (P.val x))
    (convexHull ℝ (s : Set V))
  have hf : L.faces.Finite := ((T.val x).finite s hs).subset (fun _ h => ⟨h.1.1,h.2⟩)
  let F := hf.toFinset
  let A := F.image (fun t => t.image η)
  have hA : ∀ t ∈ A, ∀ p ∈ t, ∑ i,p i=1 := by
    rintro t ht p hp
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hp
    have hl : u ∈ L.faces := hf.mem_toFinset.mp hu
    exact hη v (hl.2 hv)
  have hcard : ∀ t ∈ A, t.card ≤ j+1 := by
    rintro t ht
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp ht
    have hl : u ∈ L.faces := hf.mem_toFinset.mp hu
    exact (Finset.card_image_le).trans (hd u hl.1.1 hl.1.2)
  apply simplexArea_polyhedral_lt_top Γ hΓ A hA hcard
  rintro _ ⟨p,hp,rfl⟩
  have hpL : p ∈ L.space := by
    change p ∈ (restrictComplex (geometricRestriction (T.val x).complex (P.val x))
      (convexHull ℝ (s : Set V))).space
    rw [P.trace_space s hs x]
    exact ⟨hp.1,hW hp.2⟩
  obtain ⟨u,hu,hpu⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hpL
  apply Set.mem_iUnion₂.mpr
  refine ⟨u.image η,Finset.mem_image.mpr ⟨u,hf.mem_toFinset.mpr hu,rfl⟩,?_⟩
  rw [Finset.coe_image]
  change η.toAffineMap p ∈ convexHull ℝ (η.toAffineMap '' (u : Set V))
  rw [← η.toAffineMap.image_convexHull]
  exact ⟨p,hpu,rfl⟩
end Sparse.Cuts
namespace Sparse
section
open Set MeasureTheory
open scoped ENNReal
variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
omit [BorelSpace X] in
lemma IsLocallyConstant.lintegral_lt_top {f : X → ℝ≥0∞} (hf : IsLocallyConstant f)
    (hfin : ∀ x, f x < ∞) (μ : Measure X) [IsFiniteMeasure μ] :
    ∫⁻ x, f x ∂μ < ∞ := by
  classical
  let F := hf.range_finite.toFinset
  have hb (x : X) : f x ≤ ∑ t ∈ F,t :=
    show f x ≤ ∑ t ∈ hf.range_finite.toFinset, (fun t : ℝ≥0∞ => t) t from
      Finset.single_le_sum (f := fun t : ℝ≥0∞ => t) (fun _ _ => bot_le)
        (hf.range_finite.mem_toFinset.mpr (Set.mem_range_self x))
  apply lt_of_le_of_lt (lintegral_mono hb)
  rw [lintegral_const]
  apply ENNReal.mul_lt_top
  · apply ENNReal.sum_lt_top.mpr
    intro t ht
    obtain ⟨x,rfl⟩ := hf.range_finite.mem_toFinset.mp ht
    exact hfin x
  · exact measure_lt_top μ _
end
section
open Set Finset MeasureTheory
open scoped BassTrace.Sparse ENNReal Classical Pointwise
variable {H Y X : Type*} [Group H] [MulAction H Y] [IsCancelSMul H Y]
  [DecidableEq Y] [TopologicalSpace X] [CompactSpace X] [MulAction H X]
  [MeasurableSpace X] [BorelSpace X]
def simplexEnumeration {n : ℕ} (s : Finset Y) (hs : s.card=n+1) : Fin (n+1) ≃ s :=
  (Finset.equivFinOfCardEq hs).symm
def simplexVertices (s : Finset Y) : Finset (Y →₀ ℝ) :=
  s.image (fun y => Finsupp.single y (1 : ℝ))
def simplexCoordinates {n : ℕ} (s : Finset Y) (hs : s.card=n+1) :
    (Y →₀ ℝ) →ₗ[ℝ] (Fin (n+1) → ℝ) :=
  LinearMap.pi (fun i => Finsupp.lapply (simplexEnumeration s hs i).val)
lemma simplexCoordinates_sum {n : ℕ} (s : Finset Y) (hs : s.card=n+1)
    {p : Y →₀ ℝ} (hp : p ∈ convexHull ℝ (simplexVertices s : Set (Y →₀ ℝ))) :
    ∑ i, simplexCoordinates s hs p i = 1 := by
  have hprob : p ∈ probabilitySet s := by
    simpa only [simplexVertices,Finset.coe_image,convexHull_single_eq_probabilitySet] using hp
  calc
    (∑ i, simplexCoordinates s hs p i) = ∑ y : s,p y :=
      (simplexEnumeration s hs).sum_comp (fun y : s => p y)
    _ = ∑ y ∈ s,p y := Finset.sum_attach s (fun y => p y)
    _ = 1 := (sum_coeff_of_support_subset s p hprob.2.2).trans hprob.2.1
def simplexGraph {n : ℕ} (Γ : SimpleGraph Y) (s : Finset Y) (hs : s.card=n+1) :
    SimpleGraph (Fin (n+1)) := Γ.comap (fun i => (simplexEnumeration s hs i).val)
omit [DecidableEq Y] in
lemma simplexGraph_connected {n : ℕ} (Γ : SimpleGraph Y) (s : Finset Y) (hs : s.card=n+1)
    (hΓ : (Γ.induce (s : Set Y)).Connected) : (simplexGraph Γ s hs).Connected := by
  let e : simplexGraph Γ s hs ≃g Γ.induce (s : Set Y) := {
    toEquiv := simplexEnumeration s hs
    map_rel_iff' := by intro a b; rfl }
  exact e.connected_iff.mpr hΓ
def SourceTop (K : PreAbstractSimplicialComplex Y) (n : ℕ) :=
  {s : Finset Y // s ∈ K.faces ∧ s.card=n+1}
def sourceInterior (s : Finset Y) : Set (Y →₀ ℝ) :=
  intrinsicInterior ℝ (convexHull ℝ (simplexVertices s : Set (Y →₀ ℝ)))
def originalArea {K : PreAbstractSimplicialComplex Y} {n : ℕ}
    (Γ : SimpleGraph Y)
    (Q : OrbitForms.MarkedPair (H := H) (X := X) (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (σ : SourceTop K n) (j : ℕ) : X → ℝ≥0∞ :=
  Q.P.localArea (simplexGraph Γ σ.val σ.property.2) (simplexCoordinates σ.val σ.property.2)
    (sourceInterior σ.val) j
omit [IsCancelSMul H Y] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma originalArea_locallyConstant {K : PreAbstractSimplicialComplex Y} {n : ℕ}
    (Γ : SimpleGraph Y)
    (Q : OrbitForms.MarkedPair (H := H) (X := X) (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (σ : SourceTop K n) (j : ℕ) : IsLocallyConstant (originalArea Γ Q σ j) :=
  Q.P.localArea_locallyConstant _ _ (simplexVertices σ.val) ⟨σ.val,σ.property.1,rfl⟩
    _ intrinsicInterior_subset j
omit [IsCancelSMul H Y] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma originalArea_lt_top {K : PreAbstractSimplicialComplex Y} {n : ℕ}
    (Γ : SimpleGraph Y)
    (Q : OrbitForms.MarkedPair (H := H) (X := X) (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (σ : SourceTop K n) (hΓ : (Γ.induce (σ.val : Set Y)).Connected) (j : ℕ) (x : X)
    (hd : ∀ t ∈ (Q.T.val x).complex.faces,
      convexHull ℝ (t : Set (Y →₀ ℝ)) ⊆ Q.P.val x → t.card ≤ j+1) :
    originalArea Γ Q σ j x < ∞ :=
  Q.P.localArea_lt_top _ (simplexGraph_connected Γ σ.val σ.property.2 hΓ) _
    (simplexVertices σ.val) ⟨σ.val,σ.property.1,rfl⟩
    (fun _ hp => simplexCoordinates_sum σ.val σ.property.2 hp)
    _ intrinsicInterior_subset j x hd
lemma sourceTop_stabilizer_finite {K : PreAbstractSimplicialComplex Y} {n : ℕ}
    (σ : SourceTop K n) : Finite (MulAction.stabilizer H σ.val) := by
  obtain ⟨v,hv⟩ := Finset.card_pos.mp (by rw [σ.property.2]; omega : 0<σ.val.card)
  let f : MulAction.stabilizer H σ.val → σ.val := fun h => ⟨h.val • v,by
    have hh := Finset.smul_mem_smul_finset (a := h.val) hv
    rw [h.property] at hh
    exact hh⟩
  apply Finite.of_injective f
  intro h k he
  apply Subtype.ext
  exact IsCancelSMul.right_cancel h.val k.val v (congrArg Subtype.val he)
def normalizedArea {K : PreAbstractSimplicialComplex Y} {n : ℕ}
    (Γ : SimpleGraph Y) (μ : Measure X) (reps : Finset (SourceTop K n))
    (Q : OrbitForms.MarkedPair (H := H) (X := X) (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (j : ℕ) : ℝ≥0∞ :=
  ∑ σ ∈ reps, (Nat.card (MulAction.stabilizer H σ.val) : ℝ≥0∞)⁻¹ *
    ∫⁻ x, originalArea Γ Q σ j x ∂μ
omit [BorelSpace X] in
lemma normalizedArea_lt_top {K : PreAbstractSimplicialComplex Y} {n : ℕ}
    (Γ : SimpleGraph Y) (μ : Measure X) [IsFiniteMeasure μ] (reps : Finset (SourceTop K n))
    (hΓ : ∀ σ ∈ reps, (Γ.induce (σ.val : Set Y)).Connected)
    (Q : OrbitForms.MarkedPair (H := H) (X := X) (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (j : ℕ) (hd : ∀ x t, t ∈ (Q.T.val x).complex.faces →
      convexHull ℝ (t : Set (Y →₀ ℝ)) ⊆ Q.P.val x → t.card ≤ j+1) :
    normalizedArea Γ μ reps Q j < ∞ := by
  apply ENNReal.sum_lt_top.mpr
  intro σ hσ
  apply ENNReal.mul_lt_top
  · let := sourceTop_stabilizer_finite (H := H) σ
    apply ENNReal.inv_lt_top.mpr
    exact_mod_cast (Nat.card_pos : 0 < Nat.card (MulAction.stabilizer H σ.val))
  · exact IsLocallyConstant.lintegral_lt_top (originalArea_locallyConstant Γ Q σ j)
      (fun x => originalArea_lt_top Γ Q σ (hΓ σ hσ) j x (hd x)) μ
omit [BorelSpace X] in
lemma normalizedArea_filtration_lt_top {K : PreAbstractSimplicialComplex Y} {n : ℕ}
    (Γ : SimpleGraph Y) (μ : Measure X) [IsFiniteMeasure μ] (reps : Finset (SourceTop K n))
    (hΓ : ∀ σ ∈ reps, (Γ.induce (σ.val : Set Y)).Connected)
    {ρ : (Y →₀ ℝ) → (Y →₀ ℝ) → ℝ} {R : ℝ}
    (Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K) ρ R n)
    (hK : ∀ s ∈ K.faces,s.card ≤ n+1) {j : ℕ} (hj : j ≤ n) :
    normalizedArea Γ μ reps (Q.pair j) j < ∞ := by
  apply normalizedArea_lt_top Γ μ reps hΓ
  intro x t ht htp
  apply (Q.point x).dimension_bound _ hj ht htp
  rintro _ ⟨s,hs,rfl⟩
  exact Finset.card_image_le.trans (hK s hs)
end
lemma exists_nearMinimizer {A : Type*} [Nonempty A] (f : A → ℝ)
    (hf : ∀ a, 0 ≤ f a) {ε : ℝ} (hε : 0<ε) :
    ∃ a, ∀ b, f a ≤ f b+ε := by
  have hb : BddBelow (Set.range f) := ⟨0,by rintro _ ⟨a,rfl⟩; exact hf a⟩
  obtain ⟨_,⟨a,rfl⟩,ha⟩ := exists_lt_of_csInf_lt (Set.range_nonempty f)
    (lt_add_of_pos_right (sInf (Set.range f)) hε)
  refine ⟨a,fun b => ?_⟩
  exact ha.le.trans (by simpa only [add_comm] using add_le_add_right (csInf_le hb (Set.mem_range_self b)) ε)
end Sparse
end BassTrace
end
end OAI

end
section
namespace OAI.BassTrace.Sparse.Cuts
open Set Finset
lemma IsMarked.superlevel {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {K : Geometry.SimplicialComplex ℝ V} (f : V → ℝ) (r : ℝ) (hc : ContinuousOn f K.space)
    (hm : IsMarked K (K.space ∩ {p | f p = r})) : IsMarked K (K.space \ {p | f p < r}) := by
  classical
  intro x hx
  have hxr : r ≤ f x := le_of_not_gt hx.2
  rcases hxr.eq_or_lt with he|hx'
  · obtain ⟨F,hF,hxF,hsub⟩ := hm x ⟨hx.1,he.symm⟩
    exact ⟨F,hF,hxF,fun p hp => ⟨(hsub hp).1,not_lt.mpr (hsub hp).2.ge⟩⟩
  obtain ⟨F,hF,hxF⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx.1
  refine ⟨F,hF,hxF,fun y hy => ⟨K.convexHull_subset_space hF hy,?_⟩⟩
  intro hy'
  change f y < r at hy'
  have hs := (convex_convexHull ℝ (F : Set V)).segment_subset hy hxF
  obtain ⟨z,hz,he⟩ := (convex_segment y x).isPreconnected.intermediate_value
    (left_mem_segment ℝ y x) (right_mem_segment ℝ y x) (hc.mono (hs.trans (K.convexHull_subset_space hF))) ⟨hy'.le,hx'.le⟩
  obtain ⟨E,hE,hzE,hEq⟩ := hm z ⟨K.convexHull_subset_space hF (hs hz),he⟩
  obtain ⟨g,b,hb,hface⟩ := simplex_face_supporting F (F ∩ E) (K.indep hF) Finset.inter_subset_left
  rw [Finset.coe_inter,← K.convexHull_inter_convexHull hF hE] at hface
  have hg : g z = b := (hface.subset ⟨hs hz,hzE⟩).2
  obtain ⟨a,c,ha,hc',hac,hz'⟩ := hz
  have hapos : 0 < a := lt_of_le_of_ne ha (by rintro rfl; simp_all)
  have hgy := hb y hy
  have hgx := hb x hxF
  rw [← hz',map_add,map_smul,map_smul,smul_eq_mul,smul_eq_mul] at hg
  have hgy' : g y = b := by
    by_contra hn
    nlinarith [congrArg (fun u : ℝ => u*b) hac,mul_nonneg hc' (sub_nonneg.mpr hgx),mul_pos hapos (sub_pos.mpr (lt_of_le_of_ne hgy hn))]
  exact hy'.ne (hEq (hface.symm.subset ⟨hy,hgy'⟩).2).2
end OAI.BassTrace.Sparse.Cuts
namespace OAI
noncomputable section
namespace BassTrace
namespace Sparse.OrbitForms
open Set Finset
variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y]
  [TopologicalSpace X] [MulAction H X]
variable {K : Geometry.SimplicialComplex ℝ (Y →₀ ℝ)}
variable (ρ : (Y →₀ ℝ) → (Y →₀ ℝ) → ℝ) (R : ℝ)
structure EquivariantStep (Q : MarkedPair (H := H) (X := X) K) where
  step : Cuts.AdmissibleStep ρ R Q.T Q.P
  equivariant : Equivariant (H := H) step.next
  markedEquivariant : MarkedEquivariant (H := H) step.zero
def EquivariantStep.result {Q : MarkedPair (H := H) (X := X) K}
    (A : EquivariantStep ρ R Q) : MarkedPair (H := H) (X := X) K where
  T := A.step.next
  P := A.step.zero
  equivariant := A.equivariant
  markedEquivariant := A.markedEquivariant
def SeparatingFiltration.NearMinimal {n : ℕ}
    (Q : SeparatingFiltration (H := H) (X := X) K ρ R n)
    (cost : ℕ → MarkedPair (H := H) (X := X) K → ℝ) (ε : ℝ) : Prop :=
  ∀ i, i<n → ∀ A : EquivariantStep ρ R (Q.pair (i+1)),
    cost i (Q.pair i) ≤ cost i A.result + ε
omit [DecidableEq Y] in
theorem exists_nearMinimal_filtration {n : ℕ}
    (original : MarkedPair (H := H) (X := X) K)
    (htop : ∀ x, (original.T.val x).complex = K)
    (hspace : ∀ x, original.P.val x = K.space)
    (hex : ∀ Q : MarkedPair (H := H) (X := X) K, Nonempty (EquivariantStep ρ R Q))
    (cost : ℕ → MarkedPair (H := H) (X := X) K → ℝ)
    (hc : ∀ i Q, 0 ≤ cost i Q) {ε : ℝ} (hε : 0<ε) :
    ∃ Q : SeparatingFiltration (H := H) (X := X) K ρ R n,
      Q.NearMinimal ρ R cost ε := by
  let Pair := MarkedPair (H := H) (X := X) K
  have hm (i : ℕ) (Q : Pair) : ∃ A : EquivariantStep ρ R Q,
      ∀ B : EquivariantStep ρ R Q, cost i A.result ≤ cost i B.result+ε := by
    let := hex Q
    exact exists_nearMinimizer (fun A : EquivariantStep ρ R Q => cost i A.result)
      (fun A => hc i A.result) hε
  let step (i : ℕ) (Q : Pair) := (hm i Q).choose
  have hstep (i : ℕ) (Q : Pair) := (hm i Q).choose_spec
  let seq : ℕ → Pair := Nat.rec original (fun k Q => (step (n-(k+1)) Q).result)
  have hseq (k : ℕ) : seq (k+1) = (step (n-(k+1)) (seq k)).result := rfl
  let Q : SeparatingFiltration (H := H) (X := X) K ρ R n := {
    pair := fun i => seq (n-i)
    top := by intro x; rw [Nat.sub_self]; exact htop x
    top_space := by intro x; rw [Nat.sub_self]; exact hspace x
    finer := by
      intro i hi x
      rw [show n-i=(n-(i+1))+1 by omega,hseq]
      exact (step _ _).step.finer x
    nested := by
      intro i hi x
      rw [show n-i=(n-(i+1))+1 by omega,hseq]
      exact (step _ _).step.subset x
    drop := by
      intro i hi x
      rw [show n-i=(n-(i+1))+1 by omega,hseq]
      exact (step _ _).step.dimensionDrop x
    diameter := by
      intro i hi x
      rw [show n-i=(n-(i+1))+1 by omega,hseq]
      exact (step _ _).step.diameter x }
  refine ⟨Q,?_⟩
  intro i hi A
  change cost i (seq (n-i)) ≤ cost i A.result + ε
  rw [show n-i=(n-(i+1))+1 by omega,hseq,show n-(n-(i+1)+1)=i by omega]
  exact hstep i (seq (n-(i+1))) A
end Sparse.OrbitForms
namespace Sparse.GraphGeometry
end Sparse.GraphGeometry
namespace Sparse.OrbitForms
open Set Finset MeasureTheory
open scoped BassTrace.Sparse Classical ENNReal
variable {H Y X : Type*} [Group H] [MulAction H Y] [IsCancelSMul H Y]
  [DecidableEq Y] [TopologicalSpace X] [CompactSpace X] [MulAction H X] [MeasurableSpace X]
variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}
variable {ρ : (Y →₀ ℝ) → (Y →₀ ℝ) → ℝ} {R : ℝ}
omit [IsCancelSMul H Y] [CompactSpace X] [MeasurableSpace X] in
lemma step_dimension_bound
    (Q : SeparatingFiltration (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K) ρ R n)
    (hK : ∀ s ∈ K.faces, s.card ≤ n+1) {j : ℕ} (hj : j<n)
    (A : EquivariantStep ρ R (Q.pair (j+1))) (x : X)
    {t : Finset (Y →₀ ℝ)} (ht : t ∈ (A.result.T.val x).complex.faces)
    (htZ : convexHull ℝ (t : Set (Y →₀ ℝ)) ⊆ A.result.P.val x) : t.card ≤ j+1 := by
  obtain ⟨S,hS⟩ := A.step.finer x
  obtain ⟨F,hF,hFP,htF⟩ := S.carrier_marked ((Q.pair (j+1)).P.marked x)
    (hS.symm ▸ ht) (htZ.trans (A.step.subset x))
  have hdrop := A.step.dimensionDrop x F hF hFP t ht (Set.subset_inter htF htZ)
  have hdim := (Q.point x).dimension_bound
    (fun _ hs => by
      obtain ⟨s,hs,rfl⟩ := hs
      exact Finset.card_image_le.trans (hK s hs)) (by omega : j+1 ≤ n) hF hFP
  omega
lemma normalizedArea_step_lt_top
    (Γ : SimpleGraph Y) (μ : Measure X) [IsFiniteMeasure μ] (reps : Finset (SourceTop K n))
    (hΓ : ∀ σ ∈ reps, (Γ.induce (σ.val : Set Y)).Connected)
    (Q : SeparatingFiltration (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K) ρ R n)
    (hK : ∀ s ∈ K.faces, s.card ≤ n+1) {j : ℕ} (hj : j<n)
    (A : EquivariantStep ρ R (Q.pair (j+1))) :
    normalizedArea Γ μ reps A.result j < ∞ := by
  apply normalizedArea_lt_top Γ μ reps hΓ
  intro x t ht htp
  exact step_dimension_bound Q hK hj A x ht htp
end Sparse.OrbitForms
namespace Sparse.Cuts
open Set Finset
section
variable {V X I : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace X] {K : Geometry.SimplicialComplex ℝ V}
omit [TopologicalSpace X] in
lemma replacement_componentDiameter (ρ : V → V → ℝ) (P Z : Set V)
    (f : I → V → ℝ) (B : I → Set X) (x : X) {t R : ℝ}
    (hP : P ⊆ K.space)
    (hold : ComponentDiameter ρ (P \ Z) (2*R))
    (hc : ∀ i, ContinuousOn (f i) K.space)
    (hrho : ∀ i, ∀ p ∈ K.space, ∀ q ∈ K.space, ρ p q ≤ f i p+f i q)
    (ht : t ≤ R) :
    ComponentDiameter ρ
      (P \ replacementSet P Z (fun i => {p | f i p<t})
        (fun i => {p | f i p=t}) B x) (2*R) := by
  intro C hC hCP p hp q hq
  have hpP : ∀ y ∈ C, y ∈ P := fun y hy => (hCP hy).1
  have havoid : ∀ i, x ∈ B i → ∀ y ∈ C, f i y ≠ t := by
    intro i hix y hy hyt
    exact (hCP hy).2 (Or.inr ⟨hpP y hy,Set.mem_iUnion.mpr ⟨i,by
      simpa only [hix,ite_true,Set.mem_ofPred_eq] using hyt⟩⟩)
  by_cases hmeet : ∃ i, x ∈ B i ∧ ∃ y ∈ C, f i y<t
  · obtain ⟨i,hix,y,hy,hyt⟩ := hmeet
    have hall : ∀ z ∈ C, f i z<t := by
      intro z hz
      by_contra hzt
      obtain ⟨w,hw,hew⟩ := hC.intermediate_value hy hz
        ((hc i).mono (fun w hw => hP (hpP w hw))) ⟨hyt.le,le_of_not_gt hzt⟩
      exact havoid i hix w hw hew
    have h := hrho i p (hP (hpP p hp)) q (hP (hpP q hq))
    have hpt := hall p hp
    have hqt := hall q hq
    linarith
  · apply hold C hC _ p hp q hq
    intro y hy
    refine ⟨hpP y hy,?_⟩
    intro hyZ
    apply (hCP hy).2
    apply Or.inl
    refine ⟨hyZ,?_⟩
    intro hi
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hi
    by_cases hix : x ∈ B i
    · simp only [hix,ite_true] at hi
      exact hmeet ⟨i,hix,y,hy,hi⟩
    · simp only [hix,ite_false,Set.mem_empty_iff_false] at hi
end
variable {V X I J : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace X] {K : Geometry.SimplicialComplex ℝ V}
omit [TopologicalSpace X] in
lemma DimensionDrop.union_levels {T S : Geometry.SimplicialComplex ℝ V}
    {P Z W : Set V} (hdrop : DimensionDrop T S P Z)
    (hZ : IsMarked S Z) (a : J → V →ₗ[ℝ] ℝ) (b : J → ℝ)
    (hlevel : ∀ j, IsMarked S (S.space ∩ {p | a j p=b j}))
    (hgen : ∀ F ∈ T.faces, ∀ j, ∃ v ∈ F, a j v ≠ b j)
    (hW : W ⊆ Z ∪ ⋃ j, S.space ∩ {p | a j p=b j}) :
    DimensionDrop T S P W := by
  let A : Option J → Set V := fun o => match o with
    | none => Z
    | some j => S.space ∩ {p | a j p=b j}
  have hA (j : Option J) : IsMarked S (A j) := by
    cases j with
    | none => exact hZ
    | some j => exact hlevel j
  intro F hF hFP E hE hEW
  have hEA : convexHull ℝ (E : Set V) ⊆ ⋃ j, A j := by
    intro p hp
    rcases hW (hEW hp).2 with h | h
    · exact Set.mem_iUnion.mpr ⟨none,h⟩
    · obtain ⟨j,hj⟩ := Set.mem_iUnion.mp h
      exact Set.mem_iUnion.mpr ⟨some j,hj⟩
  obtain ⟨j,hj⟩ := IsMarked.face_in_union hA hE hEA
  cases j with
  | none => exact hdrop F hF hFP E hE (fun p hp => ⟨(hEW hp).1,hj hp⟩)
  | some j =>
    exact card_lt_of_generic_hyperplane (S.indep hE)
      ((subset_convexHull ℝ _).trans (fun p hp => (hEW hp).1)) (a j) (b j)
      (fun p hp => (hj (subset_convexHull ℝ _ hp)).2) (hgen F hF j)
namespace UniversalCuts
end UniversalCuts
end Sparse.Cuts
namespace Sparse.BallOrbitForms
end Sparse.BallOrbitForms
end BassTrace
end
end OAI

end
section
namespace OAI
noncomputable section
namespace BassTrace
namespace Sparse
open Set Finset
variable {H Y C : Type*} [Group H] [MulAction H Y] [IsCancelSMul H Y] [Fintype C]
lemma finite_translated_support_meeting (S : C → Finset Y) (s : Finset Y) :
    {j : H × C | ∃ w ∈ S j.2, j.1 • w ∈ s}.Finite := by
  have hi : (⋃ i : C, (fun h : H => (h,i)) ''
      (⋃ w ∈ (S i : Set Y), {h : H | h • w ∈ s})).Finite := by
    apply Set.finite_iUnion
    intro i
    apply Set.Finite.image
    apply Set.Finite.biUnion (S i).finite_toSet
    intro w _
    exact Set.Finite.preimage (fun h _ k _ he => IsCancelSMul.right_cancel h k w he)
      s.finite_toSet
  apply hi.subset
  rintro ⟨h,i⟩ ⟨w,hw,hs⟩
  exact Set.mem_iUnion.mpr ⟨i,h,Set.mem_iUnion₂.mpr ⟨w,hw,hs⟩,rfl⟩
end Sparse
namespace Sparse.GraphGeometry
open Set Finset
open scoped BassTrace.Sparse Classical
variable {H Y C : Type*} [Group H] [MulAction H Y] [IsCancelSMul H Y]
  [DecidableEq Y] [Fintype C]
variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)
variable [mY : MetricSpace Y] (hm : mY = graphMetric Γ hΓ)
variable {n : ℕ} (hn : 0<n) (K : PreAbstractSimplicialComplex Y)
variable (hK : ∀ s ∈ K.faces, ∃ σ ∈ K.faces, s ⊆ σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)
variable (hact : ∀ (h : H) s, s ∈ K.faces → s.map (MulAction.toPerm h).toEmbedding ∈ K.faces)
variable (hi : ∀ h : H, Isometry (fun y : Y => h • y))
include hm hn hK hact hi
lemma finite_ball_incidence (c : C → FinProbability Y) {R : ℝ} (hR : 0≤R)
    (s : Finset (Y →₀ ℝ)) (hs : s∈(Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).faces) :
    {j : H × C | ({v | centerDistance Γ hΓ K n (j.1 • c j.2) v≤R} ∩
      convexHull ℝ (s : Set (Y →₀ ℝ))).Nonempty}.Finite := by
  subst mY
  let := graphMetric Γ hΓ
  let S := fun i => ballSupport Γ (c i) n R
  obtain ⟨σ,hσ,rfl⟩ := hs
  apply (finite_translated_support_meeting (H := H) S σ).subset
  rintro ⟨h,i⟩ ⟨v,hv,hvs⟩
  have hvK : v∈(Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space :=
    (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).convexHull_subset_space ⟨σ,hσ,rfl⟩ hvs
  let p := pointProbability K ⟨v,hvK⟩
  have hp : p.coeff=v := pointProbability_coeff K _
  have hpK := pointProbability_face K ⟨v,hvK⟩
  have hpσ : p.coeff.support⊆σ := by
    rw [Finset.coe_image] at hvs
    have hh := (convexHull_single_eq_probabilitySet σ) ▸ hvs
    exact hp.symm ▸ hh.2.2
  have hball : FinProbability.rho n (h • c i) p≤R := by
    change centerDistance Γ hΓ K n (h • c i) v≤R at hv
    rw [← hp,centerDistance_apply Γ hΓ K n _ p hpK] at hv
    exact hv
  have hsub := ballSupport_inverse Γ hΓ rfl hn K hK hact hi c h i p hpK hR hball
  obtain ⟨y,hy⟩ := p.coeff_support_nonempty
  have hymap := (BallOrbitForms.inverse_support_iff h p (S i)).mp hsub hy
  obtain ⟨w,hw,he⟩ := Finset.mem_map.mp hymap
  refine ⟨w,hw,?_⟩
  have hey : h • w = y := he
  rw [hey]
  exact hpσ hy
end Sparse.GraphGeometry
namespace Sparse.Cuts.SubdivisionFamily
open Set Finset MeasureTheory
variable {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace X] [CompactSpace X]
variable {K : Geometry.SimplicialComplex ℝ V}
lemma countable_exceptional_levels (T : SubdivisionFamily X K) (hK : K.faces.Countable)
    {J : Type*} [Countable J] (a : J → V → ℝ) :
    {t : ℝ | ¬∀ x s, s ∈ (T.val x).complex.faces →
      ∀ j y, y ∈ s → a j y ≠ t}.Countable := by
  let bad : Set ℝ := ⋃ j, a j '' (⋃ x, (T.val x).complex.vertices)
  have hb : bad.Countable := Set.countable_iUnion fun j => (T.countable_vertices hK).image (a j)
  apply hb.mono
  intro t ht
  simp only [Set.mem_ofPred_eq,not_forall,not_not] at ht
  obtain ⟨x,s,hs,j,y,hy,he⟩ := ht
  exact Set.mem_iUnion.mpr ⟨j,y,Set.mem_iUnion.mpr ⟨x,
    (T.val x).complex.down_closed hs (Finset.singleton_subset_iff.mpr hy)
      (Finset.singleton_nonempty _)⟩,he⟩
end Sparse.Cuts.SubdivisionFamily
namespace Sparse.GraphGeometry
end Sparse.GraphGeometry
end BassTrace
end
end OAI

end
section
namespace OAI
noncomputable section
namespace BassTrace.Sparse
section
open MeasureTheory Set Finset
open scoped ENNReal
def treeAreaMeasure {n : ℕ} (T : SimpleGraph (Fin (n+1))) (hT : T.IsTree)
    (j : ℕ) : Measure (Fin (n+1) → ℝ) :=
  Measure.map (treeParam T hT) μHE[j]
lemma treeAreaMeasure_apply {n : ℕ} (T : SimpleGraph (Fin (n+1))) (hT : T.IsTree)
    (j : ℕ) (Q : Set (Fin (n+1) → ℝ)) :
    treeAreaMeasure T hT j Q = treeArea T hT j Q :=
  ((continuous_treeParam T hT).measurableEmbedding (treeParam_injective T hT)).map_apply _ _
def simplexAreaMeasure {n : ℕ} (Γ : SimpleGraph (Fin (n+1))) (j : ℕ) :
    Measure (Fin (n+1) → ℝ) :=
  (Fintype.card (SpanningTree Γ) : ℝ≥0∞)⁻¹ •
    ∑ T : SpanningTree Γ, treeAreaMeasure T.val T.property.2 j
lemma simplexAreaMeasure_apply {n : ℕ} (Γ : SimpleGraph (Fin (n+1))) (j : ℕ)
    (Q : Set (Fin (n+1) → ℝ)) : simplexAreaMeasure Γ j Q = simplexArea Γ j Q := by
  simp only [simplexAreaMeasure,Measure.smul_apply,Measure.finsetSum_apply,
    treeAreaMeasure_apply,smul_eq_mul,simplexArea,div_eq_mul_inv,mul_comm]
lemma measure_surgery_gain {E : Type*} [MeasurableSpace E] (μ : Measure E)
    (P Z U S : Set E) (hU : MeasurableSet U) :
    μ ((Z \ U) ∪ (P ∩ S)) + μ (Z ∩ U) ≤ μ Z + μ (P ∩ S) := by
  calc
    _ ≤ (μ (Z \ U) + μ (P ∩ S)) + μ (Z ∩ U) :=
      add_le_add_left (measure_union_le _ _) _
    _ = (μ (Z \ U) + μ (Z ∩ U)) + μ (P ∩ S) := by ac_rfl
    _ = _ := by rw [measure_sdiff_add_inter Z hU]
end
section
open Set Finset MeasureTheory
open scoped BassTrace.Sparse ENNReal Classical
section
variable {Y : Type*} [DecidableEq Y]
def simplexEmbed {n : ℕ} (s : Finset Y) (hs : s.card=n+1) :
    (Fin (n+1) → ℝ) →ₗ[ℝ] (Y →₀ ℝ) :=
  (Finsupp.lmapDomain ℝ ℝ (fun i => (simplexEnumeration s hs i).val)).comp
    (Finsupp.linearEquivFunOnFinite ℝ ℝ (Fin (n+1))).symm.toLinearMap
omit [DecidableEq Y] in
lemma simplexCoordinates_embed {n : ℕ} (s : Finset Y) (hs : s.card=n+1)
    (p : Fin (n+1) → ℝ) : simplexCoordinates s hs (simplexEmbed s hs p) = p := by
  ext i
  change (Finsupp.mapDomain (fun i => (simplexEnumeration s hs i).val)
    ((Finsupp.linearEquivFunOnFinite ℝ ℝ (Fin (n+1))).symm p))
    (simplexEnumeration s hs i).val = p i
  have hi : Function.Injective (fun i => (simplexEnumeration s hs i).val) :=
    Subtype.val_injective.comp (simplexEnumeration s hs).injective
  rw [Finsupp.mapDomain_apply_of_injective hi]
  exact congrFun ((Finsupp.linearEquivFunOnFinite ℝ ℝ (Fin (n+1))).apply_symm_apply p) i
omit [DecidableEq Y] in
lemma simplexEmbed_support {n : ℕ} (s : Finset Y) (hs : s.card=n+1)
    (p : Fin (n+1) → ℝ) : (simplexEmbed s hs p).support ⊆ s := by
  let f : Fin (n+1) ↪ Y := ⟨fun i => (simplexEnumeration s hs i).val,
    Subtype.val_injective.comp (simplexEnumeration s hs).injective⟩
  change (Finsupp.mapDomain f _).support ⊆ s
  rw [← Finsupp.embDomain_eq_mapDomain, Finsupp.support_embDomain]
  intro y hy
  obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hy
  exact (simplexEnumeration s hs i).property
lemma simplexEmbed_coordinates {n : ℕ} (s : Finset Y) (hs : s.card=n+1)
    {p : Y →₀ ℝ} (hp : p.support ⊆ s) :
    simplexEmbed s hs (simplexCoordinates s hs p) = p := by
  let q := simplexEmbed s hs (simplexCoordinates s hs p)
  have hq := simplexEmbed_support s hs (simplexCoordinates s hs p)
  ext y
  by_cases hy : y∈s
  · obtain ⟨i,hi⟩ := (simplexEnumeration s hs).surjective ⟨y,hy⟩
    have h := congrFun (simplexCoordinates_embed s hs (simplexCoordinates s hs p)) i
    change q (simplexEnumeration s hs i).val = p (simplexEnumeration s hs i).val at h
    simpa only [hi] using h
  · exact (Finsupp.notMem_support_iff.mp (fun h => hy (hq h))).trans
      (Finsupp.notMem_support_iff.mp (fun h => hy (hp h))).symm
omit [DecidableEq Y] in
lemma simplexEmbed_injective {n : ℕ} (s : Finset Y) (hs : s.card=n+1) :
    Function.Injective (simplexEmbed s hs) :=
  Function.HasLeftInverse.injective ⟨simplexCoordinates s hs,simplexCoordinates_embed s hs⟩
lemma simplexEmbed_preimage {n : ℕ} (s : Finset Y) (hs : s.card=n+1)
    (Q : Set (Y →₀ ℝ)) (hQ : ∀ p∈Q,p.support⊆s) :
    simplexEmbed s hs ⁻¹' Q = simplexCoordinates s hs '' Q := by
  ext p
  constructor
  · intro hp
    exact ⟨simplexEmbed s hs p,hp,simplexCoordinates_embed s hs p⟩
  · rintro ⟨q,hq,rfl⟩
    change simplexEmbed s hs (simplexCoordinates s hs q)∈Q
    rw [simplexEmbed_coordinates s hs (hQ q hq)]
    exact hq
def originalAreaMeasure {n : ℕ} (Γ : SimpleGraph (Fin (n+1)))
    (s : Finset Y) (hs : s.card=n+1) (j : ℕ) :
    @Measure (Y →₀ ℝ) (borel (Y →₀ ℝ)) :=
  @Measure.map _ _ _ (borel (Y →₀ ℝ)) (simplexEmbed s hs) (simplexAreaMeasure Γ j)
lemma originalAreaMeasure_apply {n : ℕ} (Γ : SimpleGraph (Fin (n+1)))
    (s : Finset Y) (hs : s.card=n+1) (j : ℕ)
    (Q : Set (Y →₀ ℝ)) (hQ : ∀ p∈Q,p.support⊆s) :
    originalAreaMeasure Γ s hs j Q = simplexArea Γ j (simplexCoordinates s hs '' Q) := by
  let : MeasurableSpace (Y →₀ ℝ) := borel (Y →₀ ℝ)
  let : BorelSpace (Y →₀ ℝ) := ⟨rfl⟩
  unfold originalAreaMeasure
  have he : MeasurableEmbedding (simplexEmbed s hs) :=
    (simplexEmbed s hs).continuous_of_finiteDimensional.measurableEmbedding
      (simplexEmbed_injective s hs)
  rw [he.map_apply, simplexEmbed_preimage s hs Q hQ,simplexAreaMeasure_apply]
end
variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y]
  [TopologicalSpace X] [MulAction H X]
lemma support_of_mem_sourceInterior (s : Finset Y) {p : Y →₀ ℝ}
    (hp : p∈sourceInterior s) : p.support⊆s := by
  have hh := intrinsicInterior_subset hp
  rw [show (simplexVertices s : Set (Y →₀ ℝ)) =
    (fun y => Finsupp.single y (1 : ℝ)) '' (s : Set Y) from Finset.coe_image] at hh
  rw [convexHull_single_eq_probabilitySet s] at hh
  exact hh.2.2
lemma originalArea_eq_measure {K : PreAbstractSimplicialComplex Y} {n : ℕ}
    (Γ : SimpleGraph Y)
    (Q : OrbitForms.MarkedPair (H := H) (X := X) (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (σ : SourceTop K n) (j : ℕ) (x : X) :
    originalArea Γ Q σ j x =
      originalAreaMeasure (simplexGraph Γ σ.val σ.property.2) σ.val σ.property.2 j
      (Q.P.val x ∩ sourceInterior σ.val) := by
  symm
  exact originalAreaMeasure_apply _ _ _ _ _
    (fun p hp => support_of_mem_sourceInterior σ.val hp.2)
end
section
open Finset Set MeasureTheory
variable {n : ℕ}
def relabelCoefficients (e : Equiv.Perm (Fin (n+1))) :
    (Fin (n+1) → ℝ) ≃ₗ[ℝ] (Fin (n+1) → ℝ) where
  toFun p := p ∘ e.symm
  invFun p := p ∘ e
  left_inv p := by ext i; simp
  right_inv p := by ext i; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
lemma sum_relabelCoefficients (e : Equiv.Perm (Fin (n+1))) (p : Fin (n+1) → ℝ) :
    ∑ i, relabelCoefficients e p i = ∑ i,p i := e.symm.sum_comp p
lemma relabelCoefficients_single (e : Equiv.Perm (Fin (n+1))) (i : Fin (n+1)) :
    relabelCoefficients e (Pi.single i 1) = Pi.single (e i) 1 := by
  ext j
  change (Pi.single i 1 : Fin (n+1) → ℝ) (e.symm j) = (Pi.single (e i) 1 : Fin (n+1) → ℝ) j
  simp only [Pi.single_apply]
  by_cases h : e.symm j = i
  · have he : j=e i := by simpa using congrArg e h
    simp [he]
  · have he : j≠e i := fun k => h (by simp [k])
    simp [h,he]
def edgeVector (u v : Fin (n+1)) : Fin (n+1) → ℝ := Pi.single u 1 - Pi.single v 1
lemma sum_edgeVector (u v : Fin (n+1)) : ∑ i, edgeVector u v i = 0 := by
  simp [edgeVector,Pi.sub_apply,Finset.sum_sub_distrib]
lemma relabel_edgeVector (e : Equiv.Perm (Fin (n+1))) (u v : Fin (n+1)) :
    relabelCoefficients e (edgeVector u v) = edgeVector (e u) (e v) := by
  simp only [edgeVector,map_sub,relabelCoefficients_single]
lemma coefficient_ext_total {p q : Fin (n+1) → ℝ}
    (hs : ∑ i,p i = ∑ i,q i) (he : ∀ i : Fin n,p i.succ=q i.succ) : p=q := by
  ext i
  induction i using Fin.cases with
  | zero =>
    rw [Fin.sum_univ_succ,Fin.sum_univ_succ] at hs
    have hsum := Finset.sum_congr (s₁ := Finset.univ) (by rfl : (Finset.univ : Finset (Fin n))=Finset.univ)
      (fun i _ => he i)
    linarith
  | succ i => exact he i
lemma treeParam_difference (T : SimpleGraph (Fin (n+1))) (hT : T.IsTree)
    (x y : EuclideanSpace ℝ (Fin n)) :
    treeParam T hT x - treeParam T hT y =
      ∑ j, (x.ofLp j-y.ofLp j) • edgeVector
        ((treeEdgeEquiv T hT j).val.out.1) ((treeEdgeEquiv T hT j).val.out.2) := by
  apply coefficient_ext_total
  · simp only [Pi.sub_apply,Finset.sum_sub_distrib]
    rw [show (∑ i,treeParam T hT x i)=1 from sum_barycentricParam _,
      show (∑ i,treeParam T hT y i)=1 from sum_barycentricParam _]
    simp only [sub_self,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum,sum_edgeVector,mul_zero,Finset.sum_const_zero]
  · intro i
    simp only [treeParam,barycentricParam,Pi.sub_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    change (∑ j, realTreeIncidence T hT i j * x.ofLp j) -
      (∑ j, realTreeIncidence T hT i j * y.ofLp j) = _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    have hc : realTreeIncidence T hT i j = edgeVector
        ((treeEdgeEquiv T hT j).val.out.1) ((treeEdgeEquiv T hT j).val.out.2) i.succ := by
      simp [realTreeIncidence,treeIncidence,rootCoordinate,edgeVector,Pi.single_apply]
    rw [hc]
    ring
lemma treeCoordinates_edgeVector (T : SimpleGraph (Fin (n+1))) (hT : T.IsTree) (j : Fin n) :
    treeCoordinates T hT (edgeVector ((treeEdgeEquiv T hT j).val.out.1)
      ((treeEdgeEquiv T hT j).val.out.2)) = WithLp.toLp 2 (Pi.single j 1) := by
  have hh := treeParam_difference T hT (WithLp.toLp 2 (Pi.single j 1)) 0
  have hh' : treeParam T hT (WithLp.toLp 2 (Pi.single j 1)) - treeParam T hT 0 =
      edgeVector ((treeEdgeEquiv T hT j).val.out.1) ((treeEdgeEquiv T hT j).val.out.2) := by
    simpa only [WithLp.ofLp_zero,Pi.zero_apply,sub_zero,Pi.single_apply,
      ite_smul,one_smul,zero_smul,Finset.sum_ite_eq',Finset.mem_univ,ite_true] using hh
  rw [← hh',map_sub,treeCoordinates_treeParam,treeCoordinates_treeParam,sub_zero]
def treeEdgePermutation (T U : SimpleGraph (Fin (n+1))) (hT : T.IsTree) (hU : U.IsTree)
    (e : T ≃g U) : Equiv.Perm (Fin n) :=
  (treeEdgeEquiv T hT).trans (e.mapEdgeSet.trans (treeEdgeEquiv U hU).symm)
lemma mapped_treeEdge_out (T U : SimpleGraph (Fin (n+1))) (hT : T.IsTree) (hU : U.IsTree)
    (e : T ≃g U) (j : Fin n) :
    (e ((treeEdgeEquiv T hT j).val.out.1) =
      (treeEdgeEquiv U hU (treeEdgePermutation T U hT hU e j)).val.out.1 ∧
     e ((treeEdgeEquiv T hT j).val.out.2) =
      (treeEdgeEquiv U hU (treeEdgePermutation T U hT hU e j)).val.out.2) ∨
    (e ((treeEdgeEquiv T hT j).val.out.1) =
      (treeEdgeEquiv U hU (treeEdgePermutation T U hT hU e j)).val.out.2 ∧
     e ((treeEdgeEquiv T hT j).val.out.2) =
      (treeEdgeEquiv U hU (treeEdgePermutation T U hT hU e j)).val.out.1) := by
  apply Sym2.eq_iff.mp
  have ho : s((treeEdgeEquiv U hU (treeEdgePermutation T U hT hU e j)).val.out.1,
      (treeEdgeEquiv U hU (treeEdgePermutation T U hT hU e j)).val.out.2) =
      (treeEdgeEquiv U hU (treeEdgePermutation T U hT hU e j)).val :=
    (treeEdgeEquiv U hU (treeEdgePermutation T U hT hU e j)).val.out_eq
  rw [ho]
  have h : treeEdgeEquiv U hU (treeEdgePermutation T U hT hU e j) =
      e.mapEdgeSet (treeEdgeEquiv T hT j) := by simp [treeEdgePermutation]
  rw [h]
  change s(e ((treeEdgeEquiv T hT j).val.out.1),e ((treeEdgeEquiv T hT j).val.out.2)) =
    Sym2.map e ((treeEdgeEquiv T hT j).val)
  have ho' : s((treeEdgeEquiv T hT j).val.out.1,(treeEdgeEquiv T hT j).val.out.2) =
      (treeEdgeEquiv T hT j).val := (treeEdgeEquiv T hT j).val.out_eq
  exact congrArg (Sym2.map e) ho'
lemma exists_treeEdge_signs (T U : SimpleGraph (Fin (n+1))) (hT : T.IsTree) (hU : U.IsTree)
    (e : T ≃g U) : ∃ ε : Fin n → ℝ, (∀ j, ε j ^ 2 = 1) ∧ ∀ j,
      relabelCoefficients e.toEquiv (edgeVector ((treeEdgeEquiv T hT j).val.out.1)
        ((treeEdgeEquiv T hT j).val.out.2)) = ε j •
      edgeVector ((treeEdgeEquiv U hU (treeEdgePermutation T U hT hU e j)).val.out.1)
        ((treeEdgeEquiv U hU (treeEdgePermutation T U hT hU e j)).val.out.2) := by
  classical
  have hh : ∀ j : Fin n, ∃ a : ℝ, a^2=1 ∧
      relabelCoefficients e.toEquiv (edgeVector ((treeEdgeEquiv T hT j).val.out.1)
        ((treeEdgeEquiv T hT j).val.out.2)) = a •
      edgeVector ((treeEdgeEquiv U hU (treeEdgePermutation T U hT hU e j)).val.out.1)
        ((treeEdgeEquiv U hU (treeEdgePermutation T U hT hU e j)).val.out.2) := by
    intro j
    rw [relabel_edgeVector]
    change ∃ a : ℝ, a^2=1 ∧ edgeVector (e ((treeEdgeEquiv T hT j).val.out.1))
        (e ((treeEdgeEquiv T hT j).val.out.2)) = a •
      edgeVector ((treeEdgeEquiv U hU (treeEdgePermutation T U hT hU e j)).val.out.1)
        ((treeEdgeEquiv U hU (treeEdgePermutation T U hT hU e j)).val.out.2)
    rcases mapped_treeEdge_out T U hT hU e j with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
    · refine ⟨1,by norm_num,?_⟩
      simpa only [one_smul] using congrArg₂ edgeVector h₁ h₂
    · refine ⟨-1,by norm_num,?_⟩
      rw [h₁,h₂]
      simp [edgeVector]
  choose ε hε he using hh
  exact ⟨ε,hε,he⟩
def signedEdgeMap (π : Equiv.Perm (Fin n)) (ε : Fin n → ℝ) :
    EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) where
  toFun x := WithLp.toLp 2 (fun j => ε (π.symm j) * x.ofLp (π.symm j))
  map_add' x y := by ext j; simp [mul_add]
  map_smul' a x := by ext j; simp [mul_left_comm]
lemma signedEdgeMap_isometry (π : Equiv.Perm (Fin n)) (ε : Fin n → ℝ)
    (hε : ∀ j, ε j ^ 2 = 1) : Isometry (signedEdgeMap π ε) := by
  apply AddMonoidHomClass.isometry_of_norm
  intro x
  have hsq : ‖signedEdgeMap π ε x‖ ^ 2 = ‖x‖ ^ 2 := by
    simp only [EuclideanSpace.real_norm_sq_eq]
    change (∑ j, (ε (π.symm j) * x.ofLp (π.symm j)) ^ 2) = ∑ j,x.ofLp j ^ 2
    simp_rw [mul_pow,hε,one_mul]
    exact π.symm.sum_comp (fun j : Fin n => x.ofLp j ^ 2)
  nlinarith [norm_nonneg (signedEdgeMap π ε x),norm_nonneg x]
lemma signedEdgeMap_sum (π : Equiv.Perm (Fin n)) (ε : Fin n → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : signedEdgeMap π ε x =
      ∑ j, (x.ofLp j * ε j) • WithLp.toLp 2 (Pi.single (π j) 1) := by
  ext k
  change ε (π.symm k) * x.ofLp (π.symm k) =
    (∑ j, (x.ofLp j * ε j) • (WithLp.toLp 2 (Pi.single (π j) 1) : EuclideanSpace ℝ (Fin n))).ofLp k
  simp only [WithLp.ofLp_sum,Finset.sum_apply,WithLp.ofLp_smul,Pi.smul_apply,smul_eq_mul,
    Pi.single_apply]
  rw [Finset.sum_eq_single (π.symm k)]
  · simp [mul_comm]
  · intro j _ hj
    have hne : k ≠ π j := fun he => hj (by simpa using congrArg π.symm he.symm)
    simp [hne]
  · simp
lemma treeTransition_sub (T U : SimpleGraph (Fin (n+1))) (hT : T.IsTree) (hU : U.IsTree)
    (e : T ≃g U) (ε : Fin n → ℝ)
    (he : ∀ j, relabelCoefficients e.toEquiv
      (edgeVector ((treeEdgeEquiv T hT j).val.out.1) ((treeEdgeEquiv T hT j).val.out.2)) =
      ε j • edgeVector ((treeEdgeEquiv U hU (treeEdgePermutation T U hT hU e j)).val.out.1)
        ((treeEdgeEquiv U hU (treeEdgePermutation T U hT hU e j)).val.out.2))
    (x y : EuclideanSpace ℝ (Fin n)) :
    treeCoordinates U hU (relabelCoefficients e.toEquiv (treeParam T hT x)) -
      treeCoordinates U hU (relabelCoefficients e.toEquiv (treeParam T hT y)) =
        signedEdgeMap (treeEdgePermutation T U hT hU e) ε (x-y) := by
  rw [← map_sub,← map_sub,treeParam_difference]
  simp_rw [map_sum,map_smul,he,map_smul,treeCoordinates_edgeVector,smul_smul]
  rw [signedEdgeMap_sum]
  rfl
lemma treeTransition_isometry (T U : SimpleGraph (Fin (n+1))) (hT : T.IsTree) (hU : U.IsTree)
    (e : T ≃g U) : Isometry (fun x =>
      treeCoordinates U hU (relabelCoefficients e.toEquiv (treeParam T hT x))) := by
  obtain ⟨ε,hε,he⟩ := exists_treeEdge_signs T U hT hU e
  apply Isometry.of_dist_eq
  intro x y
  rw [dist_eq_norm,treeTransition_sub T U hT hU e ε he,map_sub,← dist_eq_norm]
  exact (signedEdgeMap_isometry _ ε hε).dist_eq x y
lemma treeArea_relabel (T U : SimpleGraph (Fin (n+1))) (hT : T.IsTree) (hU : U.IsTree)
    (e : T ≃g U) (j : ℕ) (Q : Set (Fin (n+1) → ℝ))
    (hQ : Q ⊆ {p | ∑ i,p i=1}) :
    treeArea U hU j (relabelCoefficients e.toEquiv '' Q) = treeArea T hT j Q := by
  have hQ' : relabelCoefficients e.toEquiv '' Q ⊆ {p | ∑ i,p i=1} := by
    rintro _ ⟨p,hp,rfl⟩
    simpa only [Set.mem_ofPred_eq,sum_relabelCoefficients] using hQ hp
  unfold treeArea
  rw [treeParam_preimage_eq_image U hU _ hQ']
  have hset : treeCoordinates U hU '' (relabelCoefficients e.toEquiv '' Q) =
      (fun x => treeCoordinates U hU (relabelCoefficients e.toEquiv (treeParam T hT x))) ''
        (treeParam T hT ⁻¹' Q) := by
    ext z
    constructor
    · rintro ⟨_,⟨p,hp,rfl⟩,rfl⟩
      refine ⟨treeCoordinates T hT p,?_,?_⟩
      · simpa only [Set.mem_preimage,treeParam_treeCoordinates T hT p (hQ hp)] using hp
      · change treeCoordinates U hU (relabelCoefficients e.toEquiv (treeParam T hT (treeCoordinates T hT p))) = _
        rw [treeParam_treeCoordinates T hT p (hQ hp)]
    · rintro ⟨x,hx,rfl⟩
      exact ⟨_,⟨treeParam T hT x,hx,rfl⟩,rfl⟩
  rw [hset]
  exact (treeTransition_isometry T U hT hU e).euclideanHausdorffMeasure_image _
end
open MeasureTheory Set Finset
open scoped ENNReal
variable {n : ℕ}
def spanningTreeRelabel (Γ : SimpleGraph (Fin (n+1))) (e : Equiv.Perm (Fin (n+1))) :
    SpanningTree Γ ≃ SpanningTree (e.simpleGraph Γ) :=
  Equiv.subtypeEquiv e.simpleGraph (fun T => by
    constructor
    · rintro ⟨hle,ht⟩
      exact ⟨fun _ _ h => hle h, ((SimpleGraph.Iso.comap e.symm T).isTree_iff).mpr ht⟩
    · rintro ⟨hle,ht⟩
      refine ⟨?_,((SimpleGraph.Iso.comap e.symm T).isTree_iff).mp ht⟩
      intro v w hvw
      have h := hle (show (e.simpleGraph T).Adj (e v) (e w) by simpa using hvw)
      simpa using h)
lemma simplexArea_relabel (Γ : SimpleGraph (Fin (n+1)))
    (e : Equiv.Perm (Fin (n+1))) (j : ℕ) (Q : Set (Fin (n+1) → ℝ))
    (hQ : Q ⊆ {p | ∑ i,p i=1}) :
    simplexArea (e.simpleGraph Γ) j (relabelCoefficients e '' Q) = simplexArea Γ j Q := by
  unfold simplexArea
  rw [← Fintype.card_congr (spanningTreeRelabel Γ e)]
  congr 1
  rw [← (spanningTreeRelabel Γ e).sum_comp]
  apply Finset.sum_congr rfl
  intro T _
  exact treeArea_relabel T.val (e.simpleGraph T.val) T.property.2
    (spanningTreeRelabel Γ e T).property.2 (SimpleGraph.Iso.comap e.symm T.val).symm j Q hQ
end BassTrace.Sparse
end
end OAI

end
section
namespace OAI
noncomputable section
namespace BassTrace
namespace Sparse
section
open Set Finset MeasureTheory
open scoped BassTrace.Sparse ENNReal Classical
variable {Y Z : Type*} [DecidableEq Y] [DecidableEq Z]
lemma finsuppRelabel_single (e : Y ≃ Z) (y : Y) :
    Finsupp.domLCongr (R := ℝ) e (Finsupp.single y (1 : ℝ)) = Finsupp.single (e y) 1 := by
  ext z
  change (Finsupp.single y (1 : ℝ)) (e.symm z) = (Finsupp.single (e y) 1) z
  simp only [Finsupp.single_apply]
  have hh : y=e.symm z ↔ e y=z := ⟨fun h => by rw [h,Equiv.apply_symm_apply],
    fun h => by rw [←h,Equiv.symm_apply_apply]⟩
  simp [hh]
lemma simplexVertices_relabel (e : Y ≃ Z) (s : Finset Y) :
    (simplexVertices (s.map e.toEmbedding) : Set (Z →₀ ℝ)) =
      Finsupp.domLCongr (R := ℝ) e '' (simplexVertices s : Set (Y →₀ ℝ)) := by
  simp only [simplexVertices,Finset.coe_image,Finset.coe_map,Set.image_image]
  congr 1
  funext y
  exact (finsuppRelabel_single e y).symm
lemma sourceInterior_relabel (e : Y ≃ Z) (s : Finset Y) :
    sourceInterior (s.map e.toEmbedding) = Finsupp.domLCongr (R := ℝ) e '' sourceInterior s := by
  unfold sourceInterior
  rw [simplexVertices_relabel]
  have hh : convexHull ℝ (Finsupp.domLCongr (R := ℝ) e '' (simplexVertices s : Set (Y →₀ ℝ))) =
      (finsuppRelabelIsometry e).toAffineIsometryEquiv.toAffineIsometry ''
        convexHull ℝ (simplexVertices s : Set (Y →₀ ℝ)) :=
    ((Finsupp.domLCongr (R := ℝ) e).toLinearMap.image_convexHull _).symm
  rw [hh]
  exact (finsuppRelabelIsometry e).toAffineIsometryEquiv.toAffineIsometry.intrinsicInterior_image _
def simplexPermutation {n : ℕ} (e : Y ≃ Z) (s : Finset Y) (hs : s.card=n+1) :
    Equiv.Perm (Fin (n+1)) :=
  ((simplexEnumeration s hs).trans (Finset.equivMap e.toEmbedding s)).trans
    (simplexEnumeration (s.map e.toEmbedding) (by simpa using hs)).symm
omit [DecidableEq Y] [DecidableEq Z] in
lemma simplexEnumeration_permutation {n : ℕ} (e : Y ≃ Z) (s : Finset Y) (hs : s.card=n+1)
    (i : Fin (n+1)) :
    (simplexEnumeration (s.map e.toEmbedding) (by simpa using hs)
      (simplexPermutation e s hs i)).val = e (simplexEnumeration s hs i).val := by
  simp [simplexPermutation]
omit [DecidableEq Y] [DecidableEq Z] in
lemma simplexCoordinates_relabel {n : ℕ} (e : Y ≃ Z) (s : Finset Y) (hs : s.card=n+1)
    (p : Y →₀ ℝ) :
    simplexCoordinates (s.map e.toEmbedding) (by simpa using hs) (Finsupp.domLCongr (R := ℝ) e p) =
      relabelCoefficients (simplexPermutation e s hs) (simplexCoordinates s hs p) := by
  ext j
  obtain ⟨i,rfl⟩ := (simplexPermutation e s hs).surjective j
  change p (e.symm (simplexEnumeration (s.map e.toEmbedding) _ (simplexPermutation e s hs i)).val) =
    p (simplexEnumeration s hs ((simplexPermutation e s hs).symm (simplexPermutation e s hs i))).val
  rw [simplexEnumeration_permutation,Equiv.symm_apply_apply,Equiv.symm_apply_apply]
omit [DecidableEq Y] [DecidableEq Z] in
lemma simplexGraph_relabel {n : ℕ} (e : Y ≃ Z) (s : Finset Y) (hs : s.card=n+1)
    (Γ : SimpleGraph Y) (Δ : SimpleGraph Z)
    (he : ∀ u v,Δ.Adj (e u) (e v) ↔ Γ.Adj u v) :
    simplexGraph Δ (s.map e.toEmbedding) (by simpa using hs) =
      (simplexPermutation e s hs).simpleGraph (simplexGraph Γ s hs) := by
  ext a b
  obtain ⟨u,rfl⟩ := (simplexPermutation e s hs).surjective a
  obtain ⟨v,rfl⟩ := (simplexPermutation e s hs).surjective b
  change Δ.Adj (simplexEnumeration (s.map e.toEmbedding) _ (simplexPermutation e s hs u)).val
    (simplexEnumeration (s.map e.toEmbedding) _ (simplexPermutation e s hs v)).val ↔
    Γ.Adj (simplexEnumeration s hs ((simplexPermutation e s hs).symm (simplexPermutation e s hs u))).val
      (simplexEnumeration s hs ((simplexPermutation e s hs).symm (simplexPermutation e s hs v))).val
  rw [simplexEnumeration_permutation,simplexEnumeration_permutation,
    Equiv.symm_apply_apply,Equiv.symm_apply_apply]
  exact he _ _
omit [DecidableEq Z] in
lemma originalSimplexArea_relabel {n : ℕ} (e : Y ≃ Z) (s : Finset Y) (hs : s.card=n+1)
    (Γ : SimpleGraph Y) (Δ : SimpleGraph Z)
    (he : ∀ u v,Δ.Adj (e u) (e v) ↔ Γ.Adj u v) (j : ℕ)
    (Q : Set (Y →₀ ℝ)) (hQ : Q⊆convexHull ℝ (simplexVertices s : Set (Y →₀ ℝ))) :
    simplexArea (simplexGraph Δ (s.map e.toEmbedding) (by simpa using hs)) j
      (simplexCoordinates (s.map e.toEmbedding) (by simpa using hs) '' (Finsupp.domLCongr (R := ℝ) e '' Q)) =
      simplexArea (simplexGraph Γ s hs) j (simplexCoordinates s hs '' Q) := by
  rw [simplexGraph_relabel e s hs Γ Δ he,Set.image_image]
  have hi : (fun p => simplexCoordinates (s.map e.toEmbedding) (by simpa using hs)
      (Finsupp.domLCongr (R := ℝ) e p)) =
      (fun p => relabelCoefficients (simplexPermutation e s hs) (simplexCoordinates s hs p)) :=
    funext (simplexCoordinates_relabel e s hs)
  rw [hi,← Set.image_image]
  apply simplexArea_relabel
  rintro _ ⟨p,hp,rfl⟩
  exact simplexCoordinates_sum s hs (hQ hp)
end
open Finset Set
open scoped Pointwise Classical
variable {H Y : Type*} [Group H] [MulAction H Y] [DecidableEq Y]
variable (K : PreAbstractSimplicialComplex Y) (n : ℕ)
variable (hact : ∀ (h : H) s, s ∈ K.faces → s.map (MulAction.toPerm h).toEmbedding ∈ K.faces)
lemma smul_finset_eq_map (h : H) (s : Finset Y) :
    h • s=s.map (MulAction.toPerm h).toEmbedding := by
  ext y
  simp only [Finset.mem_smul_finset,Finset.mem_map]
  rfl
abbrev sourceTopAction : MulAction H (SourceTop K n) where
  smul h σ := ⟨h • σ.val,by rw [smul_finset_eq_map]; exact hact h σ.val σ.property.1,
    by simpa only [Finset.card_smul_finset] using σ.property.2⟩
  one_smul σ := Subtype.ext (one_smul H σ.val)
  mul_smul h k σ := Subtype.ext (mul_smul h k σ.val)
lemma sourceTop_stabilizer_eq (σ : SourceTop K n) :
    letI := sourceTopAction K n hact
    MulAction.stabilizer H σ=MulAction.stabilizer H σ.val := by
  let := sourceTopAction K n hact
  ext h
  change (h • σ=σ) ↔ h • σ.val=σ.val
  exact ⟨fun he => congrArg Subtype.val he,fun he => Subtype.ext he⟩
lemma finite_sourceTop_stabilizer [IsCancelSMul H Y] (σ : SourceTop K n) :
    letI := sourceTopAction K n hact
    Finite (MulAction.stabilizer H σ) := by
  let := sourceTopAction K n hact
  rw [sourceTop_stabilizer_eq K n hact]
  obtain ⟨v,hv⟩ := Finset.card_pos.mp (by rw [σ.property.2]; omega : 0<σ.val.card)
  let f : MulAction.stabilizer H σ.val → σ.val := fun h => ⟨h.val • v,by
    have hh := Finset.smul_mem_smul_finset (a := h.val) hv
    rw [h.property] at hh
    exact hh⟩
  apply Finite.of_injective f
  intro h k he
  exact Subtype.ext (IsCancelSMul.right_cancel h.val k.val v (congrArg Subtype.val he))
end Sparse
namespace Sparse.OrbitAreas
section
open scoped BigOperators Pointwise ENNReal
variable {H T : Type*} [Group H] [MulAction H T]
def representative (a : T) (b : MulAction.orbit H a) : H := b.property.choose
@[simp] lemma representative_smul (a : T) (b : MulAction.orbit H a) :
    representative a b • a = b.val := b.property.choose_spec
def orbitTimesStabilizer (a : T) : MulAction.orbit H a × MulAction.stabilizer H a ≃ H where
  toFun p := representative a p.1 * p.2.val
  invFun h := (⟨h • a,⟨h,rfl⟩⟩,⟨(representative a ⟨h • a,⟨h,rfl⟩⟩)⁻¹*h,by
    rw [MulAction.mem_stabilizer_iff,mul_smul]
    exact (eq_inv_smul_iff.mpr (representative_smul a ⟨h • a,⟨h,rfl⟩⟩)).symm⟩)
  left_inv p := by
    have he : (representative a p.1 * p.2.val) • a = p.1.val := by
      rw [mul_smul, p.2.property,representative_smul]
    apply Prod.ext
    · exact Subtype.ext he
    · apply Subtype.ext
      dsimp
      have hb : (⟨(representative a p.1 * p.2.val) • a,
          ⟨representative a p.1 * p.2.val,rfl⟩⟩ : MulAction.orbit H a) = p.1 := Subtype.ext he
      rw [hb,inv_mul_cancel_left]
  right_inv h := by simp
@[simp] lemma orbitTimesStabilizer_smul (a : T)
    (p : MulAction.orbit H a × MulAction.stabilizer H a) :
    orbitTimesStabilizer a p • a = p.1.val := by
  change (representative a p.1 * p.2.val) • a = _
  rw [mul_smul,p.2.property,representative_smul]
lemma sum_orbit_multiplicity (a : T) [Finite (MulAction.stabilizer H a)]
    (f : T → ℝ≥0∞) :
    (∑' h : H, f (h • a)) =
      (Nat.card (MulAction.stabilizer H a) : ℝ≥0∞) *
        ∑' b : MulAction.orbit H a, f b.val := by
  let := Fintype.ofFinite (MulAction.stabilizer H a)
  rw [← (orbitTimesStabilizer (H := H) a).tsum_eq (fun h => f (h • a))]
  simp only [orbitTimesStabilizer_smul]
  rw [ENNReal.tsum_prod (f := fun (b : MulAction.orbit H a) (_ : MulAction.stabilizer H a) => f b.val)]
  simp only [tsum_fintype,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  rw [ENNReal.tsum_mul_left,Nat.card_eq_fintype_card]
lemma normalized_orbit_sum (a : T) [Finite (MulAction.stabilizer H a)]
    (f : T → ℝ≥0∞) :
    (Nat.card (MulAction.stabilizer H a) : ℝ≥0∞)⁻¹ * (∑' h : H, f (h • a)) =
      ∑' b : MulAction.orbit H a, f b.val := by
  rw [sum_orbit_multiplicity,← mul_assoc]
  have hn : Nat.card (MulAction.stabilizer H a) ≠ 0 := Nat.card_pos.ne'
  rw [ENNReal.inv_mul_cancel (by exact_mod_cast hn) (by simp),one_mul]
lemma normalized_inverse_orbit_sum (a : T) [Finite (MulAction.stabilizer H a)]
    (f : T → ℝ≥0∞) :
    (Nat.card (MulAction.stabilizer H a) : ℝ≥0∞)⁻¹ * (∑' h : H, f (h⁻¹ • a)) =
      ∑' b : MulAction.orbit H a, f b.val := by
  have he : (∑' h : H, f (h⁻¹ • a)) = ∑' h : H, f (h • a) :=
    (Equiv.inv H).tsum_eq (fun h => f (h • a))
  rw [he]
  exact normalized_orbit_sum a f
lemma normalized_all_orbits (f : T → ℝ≥0∞)
    [∀ a : T, Finite (MulAction.stabilizer H a)] :
    (∑' o : MulAction.orbitRel.Quotient H T,
      (Nat.card (MulAction.stabilizer H o.out) : ℝ≥0∞)⁻¹ *
        ∑' h : H, f (h⁻¹ • o.out)) = ∑' a : T, f a := by
  simp only [normalized_inverse_orbit_sum]
  rw [← ENNReal.tsum_sigma]
  exact (MulAction.selfEquivSigmaOrbits H T).symm.tsum_eq f
end
section
open MeasureTheory Set
open scoped ENNReal
variable {H T X : Type*} [Group H] [MulAction H T] [MulAction H X]
  [Countable H] [Countable T] [MeasurableSpace X]
def orbitActivated (B : Set X) (f : T → X → ℝ≥0∞) (a : T) (h : H) (x : X) : ℝ≥0∞ :=
  B.indicator (f (h⁻¹ • a)) (h⁻¹ • x)
omit [Countable H] [Countable T] in
lemma measurable_orbitActivated (μ : Measure X)
    (hμ : ∀ h : H,MeasurePreserving (fun x : X => h • x) μ μ)
    (B : Set X) (hB : MeasurableSet B) (f : T → X → ℝ≥0∞)
    (hf : ∀ a,Measurable (f a)) (a : T) (h : H) :
    Measurable (orbitActivated B f a h) :=
  ((hf (h⁻¹ • a)).indicator hB).comp (hμ h⁻¹).measurable
omit [Countable H] [Countable T] in
lemma integral_orbitActivated (μ : Measure X)
    (hμ : ∀ h : H,MeasurePreserving (fun x : X => h • x) μ μ)
    (B : Set X) (hB : MeasurableSet B) (f : T → X → ℝ≥0∞)
    (hf : ∀ a,Measurable (f a)) (a : T) (h : H) :
    (∫⁻ x,orbitActivated B f a h x ∂μ) = ∫⁻ x in B,f (h⁻¹ • a) x ∂μ := by
  unfold orbitActivated
  rw [(hμ h⁻¹).lintegral_comp ((hf _).indicator hB), lintegral_indicator hB]
lemma normalized_activated_integral (μ : Measure X)
    (hμ : ∀ h : H,MeasurePreserving (fun x : X => h • x) μ μ)
    (B : Set X) (hB : MeasurableSet B) (f : T → X → ℝ≥0∞)
    (hf : ∀ a,Measurable (f a))
    [∀ a : T, Finite (MulAction.stabilizer H a)] :
    (∑' o : MulAction.orbitRel.Quotient H T,
      (Nat.card (MulAction.stabilizer H o.out) : ℝ≥0∞)⁻¹ *
        ∫⁻ x,∑' h : H,orbitActivated B f o.out h x ∂μ) =
      ∫⁻ x in B,∑' a : T,f a x ∂μ := by
  calc
    _ = ∑' o : MulAction.orbitRel.Quotient H T,
      (Nat.card (MulAction.stabilizer H o.out) : ℝ≥0∞)⁻¹ *
        ∑' h : H,∫⁻ x in B,f (h⁻¹ • o.out) x ∂μ := by
          apply tsum_congr
          intro o
          congr 1
          rw [lintegral_tsum (fun h => (measurable_orbitActivated μ hμ B hB f hf o.out h).aemeasurable)]
          exact tsum_congr (fun h => integral_orbitActivated μ hμ B hB f hf o.out h)
    _ = ∑' a : T,∫⁻ x in B,f a x ∂μ := normalized_all_orbits (fun a => ∫⁻ x in B,f a x ∂μ)
    _ = _ := (lintegral_tsum (fun a => (hf a).aemeasurable)).symm
end
open Set Finset MeasureTheory
open scoped Pointwise ENNReal Classical
variable {H T : Type*} [Group H] [MulAction H T]
variable [Finite (MulAction.orbitRel.Quotient H T)]
def orbitReps : Finset T :=
  letI := Fintype.ofFinite (MulAction.orbitRel.Quotient H T)
  (Finset.univ : Finset (MulAction.orbitRel.Quotient H T)).image Quotient.out
lemma sum_orbitReps (f : T → ℝ≥0∞) :
    (∑ a∈orbitReps (H := H) (T := T), f a) =
      ∑' o : MulAction.orbitRel.Quotient H T,f o.out := by
  let := Fintype.ofFinite (MulAction.orbitRel.Quotient H T)
  rw [tsum_fintype]
  exact Finset.sum_image (fun a _ b _ h => Quotient.out_injective h)
end Sparse.OrbitAreas
end BassTrace
end
end OAI

end
section
namespace OAI
noncomputable section
namespace BassTrace.Sparse
section
open MeasureTheory Set Finset
open scoped ENNReal
lemma measure_surgery_countable_gain {E A : Type*} [MeasurableSpace E] [Countable A]
    (μ : Measure E) (P Z : Set E) (U S : A → Set E)
    (hU : ∀ a,MeasurableSet (U a))
    (hd : Pairwise (fun a b => Disjoint (U a) (U b))) :
    μ ((Z \ ⋃ a,U a) ∪ (P ∩ ⋃ a,S a)) + ∑' a,μ (Z ∩ U a) ≤
      μ Z + ∑' a,μ (P ∩ S a) := by
  have hc : μ (Z ∩ ⋃ a,U a)=∑' a,μ (Z∩U a) := by
    calc
      μ (Z ∩ ⋃ a,U a) = (μ.restrict Z) (⋃ a,U a) := by
        rw [Measure.restrict_apply (MeasurableSet.iUnion hU),Set.inter_comm]
      _ = ∑' a,(μ.restrict Z) (U a) := measure_iUnion hd hU
      _ = _ := by
        apply tsum_congr
        intro a
        rw [Measure.restrict_apply (hU a),Set.inter_comm]
  rw [← hc]
  apply (measure_surgery_gain μ P Z _ _ (MeasurableSet.iUnion hU)).trans
  apply add_le_add_right
  rw [Set.inter_iUnion]
  exact measure_iUnion_le _
lemma countable_ball_area_jumps {E : Type*} [MeasurableSpace E] (μ : Measure E)
    (Z : Set E) {f : E → ℝ} (hf : Measurable f) :
    {t : ℝ | μ (Z ∩ {p | f p≤t}) ≠ μ (Z ∩ {p | f p<t})}.Countable := by
  have hh := countable_meas_le_ne_meas_lt (μ.restrict Z) (fun p => (-f p : ℝ))
  have hsub : {t : ℝ | μ (Z ∩ {p | f p≤t}) ≠ μ (Z ∩ {p | f p<t})} ⊆
      Neg.neg ⁻¹' {t : ℝ | (μ.restrict Z) {p | t≤ -f p} ≠
        (μ.restrict Z) {p | t < -f p}} := by
    intro t ht
    change μ (Z ∩ {p | f p≤t}) ≠ μ (Z ∩ {p | f p<t}) at ht
    change (μ.restrict Z) {p | -t≤ -f p} ≠ (μ.restrict Z) {p | -t < -f p}
    simpa only [neg_le_neg_iff,neg_lt_neg_iff,
      Measure.restrict_apply (measurableSet_le hf measurable_const),
      Measure.restrict_apply (measurableSet_lt hf measurable_const),Set.inter_comm] using ht
  exact (hh.preimage neg_injective).mono hsub
lemma nearMinimum_local_comparison {I I' M N ε : ℝ≥0∞}
    (hI : I<∞) (hmin : I≤I'+ε) (hgain : I'+M≤I+N) : M≤N+ε := by
  have hh : I+M≤I+(N+ε) := by
    calc
      I+M ≤ (I'+ε)+M := add_le_add_left hmin M
      _ = (I'+M)+ε := by ac_rfl
      _ ≤ (I+N)+ε := add_le_add_left hgain ε
      _ = I+(N+ε) := by ac_rfl
  exact (ENNReal.add_le_add_iff_left hI.ne).mp hh
lemma normalized_integrated_gain {X T : Type*} [MeasurableSpace X]
    (μ : Measure X) (reps : Finset T) (w : T → ℝ≥0∞)
    (old new removed inserted : T → X → ℝ≥0∞)
    (hnew : ∀ σ∈reps,Measurable (new σ))
    (hold : ∀ σ∈reps,Measurable (old σ))
    (hgain : ∀ σ∈reps, ∀ x,new σ x+removed σ x≤old σ x+inserted σ x) :
    (∑ σ∈reps,w σ*∫⁻ x,new σ x ∂μ) + (∑ σ∈reps,w σ*∫⁻ x,removed σ x ∂μ) ≤
      (∑ σ∈reps,w σ*∫⁻ x,old σ x ∂μ) + (∑ σ∈reps,w σ*∫⁻ x,inserted σ x ∂μ) := by
  rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro σ hσ
  rw [← mul_add,← mul_add]
  apply mul_le_mul_right
  rw [← lintegral_add_left (hnew σ hσ) _, ← lintegral_add_left (hold σ hσ) _]
  exact lintegral_mono (hgain σ hσ)
lemma ennreal_nearMinimum_of_real {I I' : ℝ≥0∞} {ε : ℝ}
    (hI : I≠∞) (hI' : I'≠∞) (hε : 0≤ε) (hmin : I.toReal≤I'.toReal+ε) :
    I≤I'+ENNReal.ofReal ε := by
  apply (ENNReal.toReal_le_toReal hI (ENNReal.add_ne_top.mpr ⟨hI',ENNReal.ofReal_ne_top⟩)).mp
  rw [ENNReal.toReal_add hI' ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hε]
  exact hmin
end
open Finset Set MeasureTheory
open scoped Pointwise Classical BassTrace.Sparse ENNReal
section
variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y]
  [TopologicalSpace X] [MulAction H X]
variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}
variable [hact : Fact (∀ (h : H) s, s ∈ K.faces → s.map (MulAction.toPerm h).toEmbedding ∈ K.faces)]
local instance : MulAction H (SourceTop K n) := sourceTopAction K n hact.out
omit hact in
lemma markedPair_image (Q : OrbitForms.MarkedPair (H := H) (X := X)
    (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K)) (h : H) (x : X) :
    Q.P.val (h • x)=OrbitForms.push h '' Q.P.val x := by
  apply Set.Subset.antisymm
  · intro p hp
    refine ⟨OrbitForms.push h⁻¹ p,?_,?_⟩
    · simpa only [inv_smul_smul] using Q.markedEquivariant h⁻¹ (h • x) p hp
    · simpa only [inv_inv] using OrbitForms.push_inv_push h⁻¹ p
  · rintro _ ⟨p,hp,rfl⟩
    exact Q.markedEquivariant h x p hp
def localOriginalArea (Γ : SimpleGraph Y)
    (Q : OrbitForms.MarkedPair (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (σ : SourceTop K n) (j : ℕ) (W : Set (Y →₀ ℝ)) (x : X) : ℝ≥0∞ :=
  simplexArea (simplexGraph Γ σ.val σ.property.2) j
    (simplexCoordinates σ.val σ.property.2 '' (Q.P.val x ∩ (sourceInterior σ.val ∩ W)))
omit hact in
lemma localOriginalArea_locallyConstant (Γ : SimpleGraph Y)
    (Q : OrbitForms.MarkedPair (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (σ : SourceTop K n) (j : ℕ) (W : Set (Y →₀ ℝ)) :
    IsLocallyConstant (localOriginalArea Γ Q σ j W) :=
  Q.P.localArea_locallyConstant _ _ (simplexVertices σ.val) ⟨σ.val,σ.property.1,rfl⟩
    _ (Set.inter_subset_left.trans intrinsicInterior_subset) j
include hact in
lemma localOriginalArea_covariant (Γ : SimpleGraph Y)
    (hΓ : ∀ (h : H) u v,Γ.Adj (h • u) (h • v) ↔ Γ.Adj u v)
    (Q : OrbitForms.MarkedPair (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (σ : SourceTop K n) (j : ℕ) (W : Set (Y →₀ ℝ)) (h : H) (x : X) :
    localOriginalArea Γ Q (h • σ) j (OrbitForms.push h '' W) (h • x) =
      localOriginalArea Γ Q σ j W x := by
  have hi : sourceInterior (h • σ).val=OrbitForms.push h '' sourceInterior σ.val := by
    change sourceInterior (h • σ.val)=_
    rw [smul_finset_eq_map]
    exact sourceInterior_relabel (MulAction.toPerm h) σ.val
  have he : Q.P.val (h • x) ∩ (sourceInterior (h • σ).val ∩ OrbitForms.push h '' W) =
      OrbitForms.push h '' (Q.P.val x ∩ (sourceInterior σ.val ∩ W)) := by
    rw [markedPair_image Q h x,hi,Set.image_inter (OrbitForms.push h).injective,
      Set.image_inter (OrbitForms.push h).injective]
  unfold localOriginalArea
  rw [he]
  change simplexArea (simplexGraph Γ (h • σ.val) _) j
    (simplexCoordinates (h • σ.val) _ ''
      (OrbitForms.push h '' (Q.P.val x ∩ (sourceInterior σ.val ∩ W)))) = _
  simpa only [← smul_finset_eq_map,OrbitForms.push] using originalSimplexArea_relabel (MulAction.toPerm h) σ.val σ.property.2 Γ Γ
    (hΓ h) j _ (fun _ hp => intrinsicInterior_subset hp.2.1)
end
section
variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y]
  [TopologicalSpace X] [MulAction H X]
variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}
variable [hact : Fact (∀ (h : H) s, s ∈ K.faces → s.map (MulAction.toPerm h).toEmbedding ∈ K.faces)]
local instance : MulAction H (SourceTop K n) := sourceTopAction K n hact.out
omit hact in
lemma localOriginalArea_eq_measure (Γ : SimpleGraph Y)
    (Q : OrbitForms.MarkedPair (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (σ : SourceTop K n) (j : ℕ) (W : Set (Y →₀ ℝ)) (x : X) :
    localOriginalArea Γ Q σ j W x =
      originalAreaMeasure (simplexGraph Γ σ.val σ.property.2) σ.val σ.property.2 j
        ((Q.P.val x ∩ sourceInterior σ.val) ∩ W) := by
  rw [originalAreaMeasure_apply _ _ _ _ _
    (fun p hp => support_of_mem_sourceInterior σ.val hp.1.2),Set.inter_assoc]
  rfl
omit hact in
lemma localOriginalArea_empty (Γ : SimpleGraph Y)
    (Q : OrbitForms.MarkedPair (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (σ : SourceTop K n) (j : ℕ) (x : X) :
    localOriginalArea Γ Q σ j ∅ x=0 := by
  rw [localOriginalArea_eq_measure]
  simp
def activeWindow (B : Set X) (W : Set (Y →₀ ℝ)) (h : H) (x : X) : Set (Y →₀ ℝ) :=
  if h⁻¹ • x∈B then OrbitForms.push h '' W else ∅
include hact in
lemma active_area_eq_orbitActivated (Γ : SimpleGraph Y)
    (hΓ : ∀ (h : H) u v,Γ.Adj (h • u) (h • v) ↔ Γ.Adj u v)
    (Q : OrbitForms.MarkedPair (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (σ : SourceTop K n) (j : ℕ) (B : Set X) (W : Set (Y →₀ ℝ)) (h : H) (x : X) :
    localOriginalArea Γ Q σ j (activeWindow B W h x) x =
      OrbitAreas.orbitActivated B (fun σ x => localOriginalArea Γ Q σ j W x) σ h x := by
  by_cases hx : h⁻¹ • x∈B
  · simp only [activeWindow,hx,ite_eq_left,OrbitAreas.orbitActivated,Set.indicator_of_mem hx]
    simpa only [smul_inv_smul] using
      localOriginalArea_covariant Γ hΓ Q (h⁻¹ • σ) j W h (h⁻¹ • x)
  · simp only [activeWindow,hx,OrbitAreas.orbitActivated,Set.indicator_of_notMem hx]
    exact localOriginalArea_empty Γ Q σ j x
omit hact in
lemma localArea_surgery_countable_gain [Countable H] (Γ : SimpleGraph Y)
    (P Z Z' : OrbitForms.MarkedPair (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (σ : SourceTop K n) (j : ℕ) (B : Set X) (U S : Set (Y →₀ ℝ)) (x : X)
    (hU : ∀ h : H, @MeasurableSet _ (borel (Y →₀ ℝ)) (activeWindow B U h x))
    (hd : Pairwise (fun h k : H => Disjoint (activeWindow B U h x) (activeWindow B U k x)))
    (hnew : Z'.P.val x = (Z.P.val x \ ⋃ h : H,activeWindow B U h x) ∪
      (P.P.val x ∩ ⋃ h : H,activeWindow B S h x)) :
    originalArea Γ Z' σ j x + ∑' h : H,localOriginalArea Γ Z σ j (activeWindow B U h x) x ≤
      originalArea Γ Z σ j x + ∑' h : H,localOriginalArea Γ P σ j (activeWindow B S h x) x := by
  let : MeasurableSpace (Y →₀ ℝ) := borel (Y →₀ ℝ)
  simp only [originalArea_eq_measure,localOriginalArea_eq_measure]
  have he : Z'.P.val x ∩ sourceInterior σ.val =
      ((Z.P.val x ∩ sourceInterior σ.val) \ ⋃ h : H,activeWindow B U h x) ∪
      ((P.P.val x ∩ sourceInterior σ.val) ∩ ⋃ h : H,activeWindow B S h x) := by
    rw [hnew]
    ext p
    simp only [Set.mem_inter_iff,Set.mem_union,Set.mem_sdiff]
    tauto
  rw [he]
  exact measure_surgery_countable_gain _ _ _ _ _ hU hd
end
variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y]
  [Countable H] [Countable Y] [IsCancelSMul H Y]
  [TopologicalSpace X] [MulAction H X] [MeasurableSpace X] [BorelSpace X]
variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}
variable [hact : Fact (∀ (h : H) s, s ∈ K.faces → s.map (MulAction.toPerm h).toEmbedding ∈ K.faces)]
local instance : MulAction H (SourceTop K n) := sourceTopAction K n hact.out
local instance : Countable (SourceTop K n) := inferInstanceAs (Countable {s : Finset Y // s∈K.faces ∧ s.card=n+1})
local instance (σ : SourceTop K n) : Finite (MulAction.stabilizer H σ) :=
  finite_sourceTop_stabilizer K n hact.out σ
variable [Finite (MulAction.orbitRel.Quotient H (SourceTop K n))]
lemma weighted_activated_originalArea (Γ : SimpleGraph Y)
    (Q : OrbitForms.MarkedPair (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (μ : Measure X) (hμ : ∀ h : H,MeasurePreserving (fun x : X => h • x) μ μ)
    (j : ℕ) (B : Set X) (hB : MeasurableSet B) (W : Set (Y →₀ ℝ)) :
    (∑ σ∈OrbitAreas.orbitReps (H := H) (T := SourceTop K n),
      (Nat.card (MulAction.stabilizer H σ.val) : ℝ≥0∞)⁻¹ *
        ∫⁻ x,∑' h : H,OrbitAreas.orbitActivated B
          (fun σ x => localOriginalArea Γ Q σ j W x) σ h x ∂μ) =
      ∫⁻ x in B,∑' σ : SourceTop K n,localOriginalArea Γ Q σ j W x ∂μ := by
  have hs (σ : SourceTop K n) : MulAction.stabilizer H σ.val=MulAction.stabilizer H σ :=
    (sourceTop_stabilizer_eq K n hact.out σ).symm
  simp_rw [hs]
  rw [OrbitAreas.sum_orbitReps]
  exact OrbitAreas.normalized_activated_integral μ hμ B hB _
    (fun σ => (localOriginalArea_locallyConstant Γ Q σ j W).continuous.measurable)
lemma normalizedArea_surgery_gain (Γ : SimpleGraph Y)
    (hΓ : ∀ (h : H) u v,Γ.Adj (h • u) (h • v) ↔ Γ.Adj u v)
    (P Z Z' : OrbitForms.MarkedPair (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (μ : Measure X) (hμ : ∀ h : H,MeasurePreserving (fun x : X => h • x) μ μ)
    (j : ℕ) (B : Set X) (hB : MeasurableSet B) (U S : Set (Y →₀ ℝ))
    (hU : ∀ (x : X) (h : H), @MeasurableSet _ (borel (Y →₀ ℝ)) (activeWindow B U h x))
    (hd : ∀ x, Pairwise (fun h k : H => Disjoint (activeWindow B U h x) (activeWindow B U k x)))
    (hnew : ∀ x,Z'.P.val x = (Z.P.val x \ ⋃ h : H,activeWindow B U h x) ∪
      (P.P.val x ∩ ⋃ h : H,activeWindow B S h x)) :
    normalizedArea Γ μ (OrbitAreas.orbitReps (H := H) (T := SourceTop K n)) Z' j +
        (∫⁻ x in B,∑' σ : SourceTop K n,localOriginalArea Γ Z σ j U x ∂μ) ≤
      normalizedArea Γ μ (OrbitAreas.orbitReps (H := H) (T := SourceTop K n)) Z j +
        (∫⁻ x in B,∑' σ : SourceTop K n,localOriginalArea Γ P σ j S x ∂μ) := by
  have hg := normalized_integrated_gain μ (OrbitAreas.orbitReps (H := H) (T := SourceTop K n))
    (fun σ => (Nat.card (MulAction.stabilizer H σ.val) : ℝ≥0∞)⁻¹)
    (fun σ x => originalArea Γ Z σ j x) (fun σ x => originalArea Γ Z' σ j x)
    (fun σ x => ∑' h : H,OrbitAreas.orbitActivated B
      (fun σ x => localOriginalArea Γ Z σ j U x) σ h x)
    (fun σ x => ∑' h : H,OrbitAreas.orbitActivated B
      (fun σ x => localOriginalArea Γ P σ j S x) σ h x)
    (fun σ _ => (originalArea_locallyConstant Γ Z' σ j).continuous.measurable)
    (fun σ _ => (originalArea_locallyConstant Γ Z σ j).continuous.measurable)
    (fun σ _ x => by
      simp_rw [← active_area_eq_orbitActivated Γ hΓ]
      exact localArea_surgery_countable_gain Γ P Z Z' σ j B U S x (hU x) (hd x) (hnew x))
  rw [weighted_activated_originalArea Γ Z μ hμ j B hB U,
    weighted_activated_originalArea Γ P μ hμ j B hB S] at hg
  exact hg
end BassTrace.Sparse
end
end OAI

end
section
namespace OAI
namespace BassTrace.Sparse
open MeasureTheory Set
open scoped ENNReal
lemma lintegral_affine_change (f : ℝ → ℝ≥0∞) (hf : Measurable f)
    {a : ℝ} (ha : a ≠ 0) (c : ℝ) :
    (∫⁻ t : ℝ, f t) = ENNReal.ofReal |a| * ∫⁻ s : ℝ, f (a * s + c) := by
  calc
    (∫⁻ t : ℝ, f t) = ∫⁻ t : ℝ, f (t + c) :=
      (lintegral_add_right_eq_self f c).symm
    _ = ENNReal.ofReal |a| * ∫⁻ s : ℝ, f (a * s + c) := by
      conv_lhs => rw [← Real.smul_map_volume_mul_left ha]
      have hh : Measurable (fun x : ℝ => f (x + c)) :=
        hf.comp (measurable_id.add_const c)
      rw [lintegral_smul_measure, lintegral_map hh (measurable_const_mul a)]
      rfl
section Product
variable {F : Type*} [MeasurableSpace F] (ν : Measure F) [SFinite ν]
def productSlice (Q : Set (ℝ × F)) (a c t : ℝ) : Set F :=
  {z | ((t - c) / a, z) ∈ Q}
lemma measurable_productSlice {Q : Set (ℝ × F)} (hQ : MeasurableSet Q) (a c : ℝ) :
    Measurable (fun t : ℝ => ν (productSlice Q a c t)) := by
  exact (measurable_measure_prodMk_left hQ).comp ((measurable_id.sub_const c).div_const a)
lemma affine_product_coarea {Q : Set (ℝ × F)} (hQ : MeasurableSet Q)
    {a : ℝ} (ha : 0 < a) (c r b : ℝ) :
    (∫⁻ t in Ioo r b, ν (productSlice Q a c t)) =
      ENNReal.ofReal a * (volume.prod ν)
        (Q ∩ {p | r < a * p.1 + c ∧ a * p.1 + c < b}) := by
  classical
  let g : ℝ → ℝ≥0∞ := (Ioo r b).indicator (fun t => ν (productSlice Q a c t))
  have hg : Measurable g := (measurable_productSlice ν hQ a c).indicator measurableSet_Ioo
  have hs : MeasurableSet (Q ∩ {p : ℝ × F | r < a * p.1 + c ∧ a * p.1 + c < b}) := by
    exact hQ.inter ((measurableSet_lt measurable_const
      ((measurable_fst.const_mul a).add_const c)).inter
      (measurableSet_lt ((measurable_fst.const_mul a).add_const c) measurable_const))
  rw [← lintegral_indicator measurableSet_Ioo]
  change (∫⁻ t, g t) = _
  rw [lintegral_affine_change g hg (ne_of_gt ha) c, abs_of_pos ha, Measure.prod_apply hs]
  congr 1
  apply lintegral_congr
  intro s
  have he : (a * s + c - c) / a = s := by field_simp; ring
  by_cases h : r < a * s + c ∧ a * s + c < b
  · have hset : Prod.mk s ⁻¹' (Q ∩ {p : ℝ × F | r < a * p.1 + c ∧ a * p.1 + c < b}) =
        {z | (s,z) ∈ Q} := by ext z; simp [h]
    have hmem : a * s + c ∈ Ioo r b := h
    simp only [g, Set.indicator_of_mem hmem, productSlice, he, hset]
  · have hset : Prod.mk s ⁻¹' (Q ∩ {p : ℝ × F | r < a * p.1 + c ∧ a * p.1 + c < b}) = ∅ := by
      ext z; simp [h]
    have hmem : a * s + c ∉ Ioo r b := h
    simp only [g, Set.indicator_of_notMem hmem, hset, measure_empty]
end Product
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
open scoped InnerProductSpace
noncomputable def normalParamIsometry (u : E) (hu : ‖u‖ = 1) :
    WithLp 2 (ℝ × (ℝ ∙ u)ᗮ) ≃ₗᵢ[ℝ] E :=
  (LinearIsometryEquiv.withLpProdCongr 2
    (LinearIsometryEquiv.toSpanUnitSingleton u hu)
    (LinearIsometryEquiv.refl ℝ (ℝ ∙ u)ᗮ)).trans
    (ℝ ∙ u).orthogonalDecomposition.symm
lemma normalParam_measurePreserving (u : E) (hu : ‖u‖ = 1) :
    MeasurePreserving (fun p : ℝ × (ℝ ∙ u)ᗮ => p.1 • u + (p.2 : E))
      (volume.prod volume) volume := by
  have h := (normalParamIsometry u hu).measurePreserving.comp
    (WithLp.volume_preserving_toLp ℝ (ℝ ∙ u)ᗮ)
  convert! h using 1
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma inner_normalParam (u : E) (hu : ‖u‖ = 1) (p : ℝ × (ℝ ∙ u)ᗮ) :
    ⟪u, p.1 • u + (p.2 : E)⟫_ℝ = p.1 := by
  rw [inner_add_right, inner_smul_right,
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp p.2.property,
    real_inner_self_eq_norm_sq, hu]
  ring
noncomputable def euclideanSliceArea (Q : Set E) (u : E) (a c t : ℝ) : ℝ≥0∞ :=
  volume {z : (ℝ ∙ u)ᗮ | ((t - c) / a) • u + (z : E) ∈ Q}
lemma euclidean_affine_coarea {Q : Set E} (hQ : MeasurableSet Q)
    (u : E) (hu : ‖u‖ = 1) {a : ℝ} (ha : 0 < a) (c r b : ℝ) :
    (∫⁻ t in Ioo r b, euclideanSliceArea Q u a c t) =
      ENNReal.ofReal a * volume
        (Q ∩ {p | r < a * ⟪u, p⟫_ℝ + c ∧ a * ⟪u, p⟫_ℝ + c < b}) := by
  let φ : ℝ × (ℝ ∙ u)ᗮ → E := fun p => p.1 • u + (p.2 : E)
  have hφ : MeasurePreserving φ (volume.prod volume) volume := normalParam_measurePreserving u hu
  have hset : MeasurableSet
      (Q ∩ {p | r < a * ⟪u, p⟫_ℝ + c ∧ a * ⟪u, p⟫_ℝ + c < b}) := by
    have hf : Measurable (fun p => a * ⟪u, p⟫_ℝ + c) := by fun_prop
    exact hQ.inter ((measurableSet_lt measurable_const hf).inter
      (measurableSet_lt hf measurable_const))
  have hpre :
      φ ⁻¹' (Q ∩ {p | r < a * ⟪u, p⟫_ℝ + c ∧ a * ⟪u, p⟫_ℝ + c < b}) =
      (φ ⁻¹' Q) ∩ {p | r < a * p.1 + c ∧ a * p.1 + c < b} := by
    ext p
    simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_ofPred_eq, φ,
      inner_normalParam u hu p]
  calc
    _ = ENNReal.ofReal a * (volume.prod volume)
        ((φ ⁻¹' Q) ∩ {p | r < a * p.1 + c ∧ a * p.1 + c < b}) :=
      affine_product_coarea volume (hφ.measurable hQ) ha c r b
    _ = _ := by rw [← hpre, hφ.measure_preimage hset.nullMeasurableSet]
lemma euclidean_affine_coarea_le {Q : Set E} (hQ : MeasurableSet Q)
    (u : E) (hu : ‖u‖ = 1) {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (c r b : ℝ) :
    (∫⁻ t in Ioo r b, euclideanSliceArea Q u a c t) ≤
      volume (Q ∩ {p | a * ⟪u, p⟫_ℝ + c ≤ b}) := by
  rw [euclidean_affine_coarea hQ u hu ha]
  calc
    _ ≤ 1 * volume (Q ∩ {p | r < a * ⟪u, p⟫_ℝ + c ∧ a * ⟪u, p⟫_ℝ + c < b}) := by
      gcongr
      simpa using ENNReal.ofReal_le_ofReal ha1
    _ ≤ _ := by
      rw [one_mul]
      exact measure_mono (fun p hp => ⟨hp.1, hp.2.2.le⟩)
end BassTrace.Sparse
end OAI

end
section
namespace OAI
namespace BassTrace.Sparse
section
open MeasureTheory Set
open scoped ENNReal InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
omit [MeasurableSpace E] [BorelSpace E] in
lemma orthogonal_unit_rank (u : E) (hu : ‖u‖ = 1) :
    Module.finrank ℝ (ℝ ∙ u)ᗮ = Module.finrank ℝ E - 1 := by
  have hne : u ≠ 0 := by intro h; simp [h] at hu
  have h := (ℝ ∙ u).finrank_add_finrank_orthogonal
  rw [finrank_span_singleton hne] at h
  omega
lemma euclideanSliceArea_eq_area (Q : Set E) (u : E) (hu : ‖u‖ = 1)
    {a : ℝ} (ha : a ≠ 0) (c t : ℝ) :
    euclideanSliceArea Q u a c t =
      μHE[Module.finrank ℝ E - 1] (Q ∩ {p | a * ⟪u,p⟫_ℝ + c = t}) := by
  let φ : (ℝ ∙ u)ᗮ → E := fun z => ((t-c)/a) • u + (z : E)
  have hφ : Isometry φ := (isometry_add_left (((t-c)/a) • u)).comp isometry_subtype_coe
  have himage : φ '' {z | φ z ∈ Q} = Q ∩ {p | a * ⟪u,p⟫_ℝ+c=t} := by
    ext p
    constructor
    · rintro ⟨z,hz,rfl⟩
      refine ⟨hz,?_⟩
      dsimp [φ]
      rw [inner_normalParam u hu (((t-c)/a),z)]
      field_simp
      ring
    · rintro ⟨hp,ht⟩
      change a * ⟪u,p⟫_ℝ+c=t at ht
      have hpu : ⟪u,p⟫_ℝ = (t-c)/a := by apply (eq_div_iff ha).mpr; linarith
      have hz : p - ((t-c)/a) • u ∈ (ℝ ∙ u)ᗮ := by
        apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
        rw [inner_sub_right,inner_smul_right,real_inner_self_eq_norm_sq,hu,hpu]
        ring
      refine ⟨⟨p - ((t-c)/a) • u,hz⟩,?_,?_⟩
      · dsimp [φ]
        simpa only [add_sub_cancel] using hp
      · dsimp [φ]
        abel
  rw [← himage,hφ.euclideanHausdorffMeasure_image]
  rw [← orthogonal_unit_rank u hu,InnerProductSpace.euclideanHausdorffMeasure_eq_volume]
  rfl
lemma euclidean_area_affine_coarea_le {Q : Set E} (hQ : MeasurableSet Q)
    (u : E) (hu : ‖u‖ = 1) {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (c r b : ℝ) :
    (∫⁻ t in Ioo r b, μHE[Module.finrank ℝ E - 1]
      (Q ∩ {p | a * ⟪u,p⟫_ℝ+c=t})) ≤
      μHE[Module.finrank ℝ E] (Q ∩ {p | a * ⟪u,p⟫_ℝ+c ≤ b}) := by
  simp_rw [← euclideanSliceArea_eq_area Q u hu ha.ne',
    InnerProductSpace.euclideanHausdorffMeasure_eq_volume]
  exact euclidean_affine_coarea_le hQ u hu ha ha1 c r b
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma euclidean_area_constant_slices (Q : Set E) (d : ℕ) (c r b : ℝ) :
    (∫⁻ t in Ioo r b, μHE[d] (Q ∩ { _p : E | c=t})) = 0 := by
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [ae_restrict_of_ae ((volume : Measure ℝ).ae_ne c)] with t ht
  have he : { _p : E | c=t} = ∅ := by ext p; simp [Ne.symm ht]
  simp only [he,inter_empty,measure_empty,Pi.zero_apply]
lemma euclidean_area_gradient_coarea_le {Q : Set E} (hQ : MeasurableSet Q)
    (g : E) (hg : ‖g‖ ≤ 1) (c r b : ℝ) :
    (∫⁻ t in Ioo r b, μHE[Module.finrank ℝ E - 1]
      (Q ∩ {p | ⟪g,p⟫_ℝ+c=t})) ≤
      μHE[Module.finrank ℝ E] (Q ∩ {p | ⟪g,p⟫_ℝ+c ≤ b}) := by
  by_cases hzero : g = 0
  · subst g
    simp only [inner_zero_left,zero_add]
    rw [euclidean_area_constant_slices]
    exact bot_le
  · let u := (‖g‖⁻¹ : ℝ) • g
    have ha : 0 < ‖g‖ := norm_pos_iff.mpr hzero
    have hu : ‖u‖ = 1 := by simp [u,norm_smul,ha.ne']
    have he (p : E) : ‖g‖ * ⟪u,p⟫_ℝ = ⟪g,p⟫_ℝ := by
      dsimp [u]
      rw [inner_smul_left]
      simp [ha.ne']
    simpa only [he] using euclidean_area_affine_coarea_le hQ u hu ha hg c r b
lemma measurable_euclidean_area_slices {Q : Set E} (hQ : MeasurableSet Q)
    (g : E) (c : ℝ) : Measurable (fun t : ℝ =>
      μHE[Module.finrank ℝ E - 1] (Q ∩ {p | ⟪g,p⟫_ℝ+c=t})) := by
  by_cases hz : g = 0
  · subst g
    have he : (fun t : ℝ => μHE[Module.finrank ℝ E - 1]
        (Q ∩ {p : E | ⟪(0:E),p⟫_ℝ+c=t})) =
        fun t => if t=c then μHE[Module.finrank ℝ E - 1] Q else 0 := by
      funext t
      by_cases ht : t=c
      · simp [ht]
      · simp [ht,Ne.symm ht]
    rw [he]
    exact Measurable.ite (measurableSet_singleton c) measurable_const measurable_const
  · let u := (‖g‖⁻¹ : ℝ) • g
    have ha : 0 < ‖g‖ := norm_pos_iff.mpr hz
    have hu : ‖u‖ = 1 := by simp [u,norm_smul,ha.ne']
    have he (p : E) : ‖g‖ * ⟪u,p⟫_ℝ = ⟪g,p⟫_ℝ := by
      dsimp [u]
      rw [inner_smul_left]
      simp [ha.ne']
    let φ : ℝ × (ℝ ∙ u)ᗮ → E := fun p => p.1 • u + (p.2 : E)
    have hφ : Continuous φ := by fun_prop
    have hm := measurable_productSlice (volume : Measure (ℝ ∙ u)ᗮ)
      (hQ.preimage hφ.measurable) ‖g‖ c
    convert hm using 1
    funext t
    change _ = euclideanSliceArea Q u ‖g‖ c t
    rw [euclideanSliceArea_eq_area Q u hu ha.ne']
    simp_rw [he]
end
section
open MeasureTheory Set
open scoped ENNReal InnerProductSpace
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace F] [BorelSpace F] in
lemma exists_restricted_gradient (e : F →ᵃⁱ[ℝ] E) (g : E) (c : ℝ) :
    ∃ g' : F, ‖g'‖ ≤ ‖g‖ ∧ ∀ x,
      ⟪g,e x⟫_ℝ+c = ⟪g',x⟫_ℝ+(⟪g,e 0⟫_ℝ+c) := by
  let l : F →L[ℝ] ℝ := (innerSL ℝ g).comp e.linearIsometry.toContinuousLinearMap
  let g' := (InnerProductSpace.toDual ℝ F).symm l
  have hg' (x : F) : ⟪g',x⟫_ℝ = ⟪g,e.linearIsometry x⟫_ℝ :=
    InnerProductSpace.toDual_symm_apply
  refine ⟨g',?_,?_⟩
  · calc ‖g'‖ = ‖l‖ := (InnerProductSpace.toDual ℝ F).symm.norm_map l
         _ ≤ ‖g‖ := by
           apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
           intro x
           change ‖⟪g,e.linearIsometry x⟫_ℝ‖ ≤ ‖g‖*‖x‖
           simpa only [e.linearIsometry.norm_map] using norm_inner_le_norm g (e.linearIsometry x)
  · intro x
    have he : e x = e.linearIsometry x + e 0 := by
      have hh := e.map_vadd (0:F) x
      simpa only [vadd_eq_add,add_zero] using hh
    rw [he,inner_add_right,hg']
    ring
omit [FiniteDimensional ℝ E] in
lemma euclidean_area_embedded_coarea {Q : Set F} (hQ : MeasurableSet Q)
    (e : F →ᵃⁱ[ℝ] E) (f : E → ℝ) (g : F) (hg : ‖g‖ ≤ 1) (c : ℝ)
    (hbranch : ∀ x ∈ Q, f (e x) = ⟪g,x⟫_ℝ+c) (r b : ℝ) :
    (∫⁻ t in Ioo r b, μHE[Module.finrank ℝ F - 1]
      ((e '' Q) ∩ {p | f p=t})) ≤
      μHE[Module.finrank ℝ F] ((e '' Q) ∩ {p | f p ≤ b}) := by
  have hslice (t : ℝ) : (e '' Q) ∩ {p | f p=t} =
      e '' (Q ∩ {x | ⟪g,x⟫_ℝ+c=t}) := by
    ext p
    constructor
    · rintro ⟨⟨x,hx,rfl⟩,ht⟩
      exact ⟨x,⟨hx,(hbranch x hx).symm.trans ht⟩,rfl⟩
    · rintro ⟨x,⟨hx,ht⟩,rfl⟩
      exact ⟨⟨x,hx,rfl⟩,(hbranch x hx).trans ht⟩
  have hball : (e '' Q) ∩ {p | f p ≤ b} =
      e '' (Q ∩ {x | ⟪g,x⟫_ℝ+c ≤ b}) := by
    ext p
    constructor
    · rintro ⟨⟨x,hx,rfl⟩,ht⟩
      exact ⟨x,⟨hx,by simpa only [Set.mem_ofPred_eq,← hbranch x hx] using ht⟩,rfl⟩
    · rintro ⟨x,⟨hx,ht⟩,rfl⟩
      exact ⟨⟨x,hx,rfl⟩,by simpa only [Set.mem_ofPred_eq,hbranch x hx] using ht⟩
  simp_rw [hslice,hball,e.isometry.euclideanHausdorffMeasure_image]
  exact euclidean_area_gradient_coarea_le hQ g hg c r b
omit [FiniteDimensional ℝ E] in
lemma measurable_embedded_slices {Q : Set F} (hQ : MeasurableSet Q)
    (e : F →ᵃⁱ[ℝ] E) (f : E → ℝ) (g : F) (c : ℝ)
    (hbranch : ∀ x ∈ Q, f (e x) = ⟪g,x⟫_ℝ+c) :
    Measurable (fun t : ℝ => μHE[Module.finrank ℝ F - 1]
      ((e '' Q) ∩ {p | f p=t})) := by
  have hslice (t : ℝ) : (e '' Q) ∩ {p | f p=t} =
      e '' (Q ∩ {x | ⟪g,x⟫_ℝ+c=t}) := by
    ext p
    constructor
    · rintro ⟨⟨x,hx,rfl⟩,ht⟩
      exact ⟨x,⟨hx,(hbranch x hx).symm.trans ht⟩,rfl⟩
    · rintro ⟨x,⟨hx,ht⟩,rfl⟩
      exact ⟨⟨x,hx,rfl⟩,(hbranch x hx).trans ht⟩
  simp_rw [hslice,e.isometry.euclideanHausdorffMeasure_image]
  exact measurable_euclidean_area_slices hQ g c
end
open MeasureTheory Set Finset
open scoped ENNReal InnerProductSpace
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
omit [MeasurableSpace E] [BorelSpace E] in
lemma extend_subspace_dimension (S : Submodule ℝ E) (d : ℕ)
    (hS : Module.finrank ℝ S ≤ d) (hd : d ≤ Module.finrank ℝ E) :
    ∃ W : Submodule ℝ E, S ≤ W ∧ Module.finrank ℝ W = d := by
  induction d, hS using Nat.le_induction with
  | base => exact ⟨S,le_rfl,rfl⟩
  | succ k hk ih =>
    obtain ⟨W,hSW,hW⟩ := ih (by omega)
    obtain ⟨v,hv⟩ := W.exists_of_finrank_lt (by omega)
    have hvW : v ∉ W := by simpa using hv 1 one_ne_zero
    exact ⟨W ⊔ Submodule.span ℝ {v},hSW.trans le_sup_left,by
      rw [Submodule.finrank_sup_span_singleton hvW,hW]⟩
omit [MeasurableSpace E] [BorelSpace E] in
lemma simplex_in_affine_isometry (s : Finset E) (hs : s.Nonempty) (d : ℕ)
    (hsd : s.card ≤ d+1) (hd : d ≤ Module.finrank ℝ E) :
    ∃ e : EuclideanSpace ℝ (Fin d) →ᵃⁱ[ℝ] E,
      convexHull ℝ (s : Set E) ⊆ Set.range e := by
  have hc : Fintype.card s = (s.card-1)+1 := by
    rw [Fintype.card_coe]; have := Finset.card_pos.mpr hs; omega
  have hdim := finrank_vectorSpan_range_le ℝ ((↑) : s → E) hc
  rw [Subtype.range_coe_subtype] at hdim
  obtain ⟨W,hW,hWd⟩ := extend_subspace_dimension (vectorSpan ℝ (s : Set E)) d
    (hdim.trans (by omega)) hd
  obtain ⟨c,hc⟩ := hs
  let b := (stdOrthonormalBasis ℝ W).reindex (finCongr hWd)
  let l : EuclideanSpace ℝ (Fin d) →ₗᵢ[ℝ] E := W.subtypeₗᵢ.comp b.repr.symm.toLinearIsometry
  let e : EuclideanSpace ℝ (Fin d) →ᵃⁱ[ℝ] E :=
    (AffineIsometryEquiv.vaddConst ℝ c).toAffineIsometry.comp l.toAffineIsometry
  refine ⟨e,?_⟩
  intro p hp
  have hspan : p-c ∈ W := by
    apply hW
    have hsp : vectorSpan ℝ (convexHull ℝ (s : Set E)) = vectorSpan ℝ (s : Set E) := by
      rw [← direction_affineSpan,affineSpan_convexHull,direction_affineSpan]
    rw [← hsp]
    exact vsub_mem_vectorSpan ℝ hp (subset_convexHull ℝ (s : Set E) hc)
  refine ⟨b.repr ⟨p-c,hspan⟩,?_⟩
  change (↑(b.repr.symm (b.repr ⟨p-c,hspan⟩)) : E)+c=p
  rw [b.repr.symm_apply_apply]
  simp
lemma simplex_piece_coarea (s : Finset E) (d : ℕ) (hsd : s.card ≤ d+1)
    (hd : d ≤ Module.finrank ℝ E) {Q : Set E} (hQ : MeasurableSet Q)
    (hQs : Q ⊆ convexHull ℝ (s : Set E)) (f : E → ℝ) (g : E) (hg : ‖g‖ ≤ 1)
    (c : ℝ) (hf : ∀ p ∈ Q, f p=⟪g,p⟫_ℝ+c) (r b : ℝ) :
    (∫⁻ t in Ioo r b, μHE[d-1] (Q ∩ {p | f p=t})) ≤
      μHE[d] (Q ∩ {p | f p ≤ b}) := by
  by_cases hs : s.Nonempty
  · obtain ⟨e,he⟩ := simplex_in_affine_isometry s hs d hsd hd
    have hQr : Q ⊆ Set.range e := hQs.trans he
    have heQ : e '' (e ⁻¹' Q) = Q := Set.image_preimage_eq_of_subset hQr
    obtain ⟨g',hg',hb⟩ := exists_restricted_gradient e g c
    have hbranch : ∀ x ∈ e ⁻¹' Q, f (e x)=⟪g',x⟫_ℝ+(⟪g,e 0⟫_ℝ+c) := by
      intro x hx; rw [hf _ hx,hb]
    have hh := euclidean_area_embedded_coarea (e.continuous.measurable hQ)
      e f g' (hg'.trans hg) (⟪g,e 0⟫_ℝ+c) hbranch r b
    simpa only [heQ,finrank_euclideanSpace_fin] using hh
  · have he : s=∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    have hQe : Q=∅ := by apply Set.eq_empty_of_subset_empty; simpa [he] using hQs
    simp [hQe]
lemma measurable_simplex_piece_slices (s : Finset E) (d : ℕ) (hsd : s.card ≤ d+1)
    (hd : d ≤ Module.finrank ℝ E) {Q : Set E} (hQ : MeasurableSet Q)
    (hQs : Q ⊆ convexHull ℝ (s : Set E)) (f : E → ℝ) (g : E)
    (c : ℝ) (hf : ∀ p ∈ Q, f p=⟪g,p⟫_ℝ+c) :
    Measurable (fun t : ℝ => μHE[d-1] (Q ∩ {p | f p=t})) := by
  by_cases hs : s.Nonempty
  · obtain ⟨e,he⟩ := simplex_in_affine_isometry s hs d hsd hd
    have hQr : Q ⊆ Set.range e := hQs.trans he
    have heQ : e '' (e ⁻¹' Q) = Q := Set.image_preimage_eq_of_subset hQr
    obtain ⟨g',_,hb⟩ := exists_restricted_gradient e g c
    have hbranch : ∀ x ∈ e ⁻¹' Q, f (e x)=⟪g',x⟫_ℝ+(⟪g,e 0⟫_ℝ+c) := by
      intro x hx; rw [hf _ hx,hb]
    have hh := measurable_embedded_slices (e.continuous.measurable hQ)
      e f g' (⟪g,e 0⟫_ℝ+c) hbranch
    simpa only [heQ,finrank_euclideanSpace_fin] using hh
  · have he : s=∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    have hQe : Q=∅ := by apply Set.eq_empty_of_subset_empty; simpa [he] using hQs
    simp only [hQe,Set.empty_inter,measure_empty]
    exact measurable_const
lemma finite_polyhedral_coarea {k : ℕ} (s : Fin k → Finset E) (d : ℕ)
    (hs : ∀ i, (s i).card ≤ d+1) (hd : d ≤ Module.finrank ℝ E)
    (Q : Fin k → Set E) (hQ : ∀ i, MeasurableSet (Q i))
    (hQs : ∀ i, Q i ⊆ convexHull ℝ (s i : Set E)) (f : E → ℝ)
    (g : Fin k → E) (hg : ∀ i, ‖g i‖ ≤ 1) (c : Fin k → ℝ)
    (hf : ∀ i p, p ∈ Q i → f p=⟪g i,p⟫_ℝ+c i) (r b : ℝ) :
    (∫⁻ t in Ioo r b, μHE[d-1] ((⋃ i, Q i) ∩ {p | f p=t})) ≤
      μHE[d] ((⋃ i, Q i) ∩ {p | f p ≤ b}) := by
  let W := disjointed Q
  have hW (i : Fin k) : MeasurableSet (W i) :=
    disjointedRec (fun _ j ht => ht.diff (hQ j)) (hQ i)
  have hsub (i : Fin k) : W i ⊆ Q i := disjointed_subset Q i
  have hcover : (⋃ i, W i) = ⋃ i, Q i := iUnion_disjointed
  have hdisj : Pairwise fun i j => Disjoint (W i) (W j) := disjoint_disjointed Q
  have hslice (t : ℝ) : ((⋃ i,W i) ∩ {p | f p=t}) =
      ⋃ i, W i ∩ {p | f p=t} := Set.iUnion_inter _ _
  have hball : ((⋃ i,W i) ∩ {p | f p ≤ b}) =
      ⋃ i, W i ∩ {p | f p ≤ b} := Set.iUnion_inter _ _
  have hm (i : Fin k) : MeasurableSet (W i ∩ {p | f p ≤ b}) := by
    have he : W i ∩ {p | f p ≤ b} = W i ∩ {p | ⟪g i,p⟫_ℝ+c i ≤ b} := by
      ext p; constructor <;> rintro ⟨hp,ht⟩
      · exact ⟨hp,by simpa only [Set.mem_ofPred_eq,← hf i p (hsub i hp)] using ht⟩
      · exact ⟨hp,by simpa only [Set.mem_ofPred_eq,hf i p (hsub i hp)] using ht⟩
    rw [he]
    exact (hW i).inter (measurableSet_le (by fun_prop) measurable_const)
  rw [← hcover]
  calc
    _ ≤ ∫⁻ t in Ioo r b, ∑ i, μHE[d-1] (W i ∩ {p | f p=t}) := by
      apply lintegral_mono
      intro t
      dsimp only
      rw [hslice]
      simpa only [tsum_fintype] using measure_iUnion_le (μ := μHE[d-1])
        (fun i => W i ∩ {p | f p=t})
    _ = ∑ i, ∫⁻ t in Ioo r b, μHE[d-1] (W i ∩ {p | f p=t}) := by
      apply lintegral_finsetSum
      intro i _
      exact measurable_simplex_piece_slices (s i) d (hs i) hd (hW i)
        ((hsub i).trans (hQs i)) f (g i) (c i) (fun p hp => hf i p (hsub i hp))
    _ ≤ ∑ i, μHE[d] (W i ∩ {p | f p ≤ b}) := by
      apply Finset.sum_le_sum
      intro i _
      exact simplex_piece_coarea (s i) d (hs i) hd (hW i)
        ((hsub i).trans (hQs i)) f (g i) (hg i) (c i) (fun p hp => hf i p (hsub i hp)) r b
    _ = _ := by
      rw [hball,measure_iUnion]
      · exact (tsum_fintype _).symm
      · intro i j hij
        exact (hdisj hij).mono inter_subset_left inter_subset_left
      · exact hm
lemma finite_affine_coarea {I : Type*} [Fintype I]
    (s : I → Finset E) (d : ℕ) (hs : ∀ i, (s i).card ≤ d+1)
    (hd : d ≤ Module.finrank ℝ E)
    (Q : I → Set E) (hQ : ∀ i, MeasurableSet (Q i))
    (hQs : ∀ i, Q i ⊆ convexHull ℝ (s i : Set E))
    (f : E → ℝ) (g : I → E) (hg : ∀ i, ‖g i‖ ≤ 1) (c : I → ℝ)
    (hf : ∀ i p, p ∈ Q i → f p = ⟪g i,p⟫_ℝ+c i) (r b : ℝ) :
    (∫⁻ t in Ioo r b, μHE[d-1] ((⋃ i, Q i) ∩ {p | f p=t})) ≤
      μHE[d] ((⋃ i, Q i) ∩ {p | f p ≤ b}) := by
  classical
  let e := (Fintype.equivFin I).symm
  have he : (⋃ j, Q (e j)) = ⋃ i, Q i := e.surjective.iUnion_comp Q
  rw [← he]
  exact finite_polyhedral_coarea (fun j => s (e j)) d (fun j => hs (e j)) hd
    (fun j => Q (e j)) (fun j => hQ (e j)) (fun j => hQs (e j)) f
    (fun j => g (e j)) (fun j => hg (e j)) (fun j => c (e j))
    (fun j => hf (e j)) r b
lemma finite_max_coarea {I J : Type*} [Fintype I] [Fintype J] [Nonempty J]
    (s : I → Finset E) (d : ℕ) (hs : ∀ i, (s i).card ≤ d+1)
    (hd : d ≤ Module.finrank ℝ E)
    (Q : I → Set E) (hQ : ∀ i, MeasurableSet (Q i))
    (hQs : ∀ i, Q i ⊆ convexHull ℝ (s i : Set E))
    (g : I → J → E) (hg : ∀ i j, ‖g i j‖ ≤ 1) (c : I → J → ℝ)
    (f : E → ℝ)
    (hf : ∀ i p, p ∈ Q i → f p = Finset.univ.sup' Finset.univ_nonempty
      (fun j => ⟪g i j,p⟫_ℝ+c i j)) (r b : ℝ) :
    (∫⁻ t in Ioo r b, μHE[d-1] ((⋃ i, Q i) ∩ {p | f p=t})) ≤
      μHE[d] ((⋃ i, Q i) ∩ {p | f p ≤ b}) := by
  classical
  let W (a : I × J) := Q a.1 ∩ ⋂ j, {p | ⟪g a.1 j,p⟫_ℝ+c a.1 j ≤
    ⟪g a.1 a.2,p⟫_ℝ+c a.1 a.2}
  have hW (a : I × J) : MeasurableSet (W a) := by
    exact (hQ a.1).inter (MeasurableSet.iInter fun j =>
      measurableSet_le (by fun_prop) (by fun_prop))
  have hWQ (a : I × J) : W a ⊆ Q a.1 := inter_subset_left
  have hcover : (⋃ a, W a) = ⋃ i, Q i := by
    apply Set.Subset.antisymm
    · simp only [iUnion_subset_iff]
      intro a
      exact (hWQ a).trans (subset_iUnion Q a.1)
    · intro p hp
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hp
      obtain ⟨j,_,hj⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
        (fun j => ⟪g i j,p⟫_ℝ+c i j)
      apply Set.mem_iUnion.mpr
      refine ⟨(i,j),hi,Set.mem_iInter.mpr ?_⟩
      intro l
      change ⟪g i l,p⟫_ℝ+c i l ≤ ⟪g i j,p⟫_ℝ+c i j
      rw [← hj]
      exact Finset.le_sup' (fun j => ⟪g i j,p⟫_ℝ+c i j) (Finset.mem_univ l)
  have hbranch (a : I × J) (p : E) (hp : p ∈ W a) :
      f p = ⟪g a.1 a.2,p⟫_ℝ+c a.1 a.2 := by
    rw [hf a.1 p hp.1]
    apply le_antisymm
    · exact Finset.sup'_le _ _ (fun j _ => Set.mem_iInter.mp hp.2 j)
    · exact Finset.le_sup' (fun j => ⟪g a.1 j,p⟫_ℝ+c a.1 j) (Finset.mem_univ a.2)
  rw [← hcover]
  exact finite_affine_coarea (fun a => s a.1) d (fun a => hs a.1) hd W hW
    (fun a => (hWQ a).trans (hQs a.1)) f (fun a => g a.1 a.2)
    (fun a => hg a.1 a.2) (fun a => c a.1 a.2) hbranch r b
lemma measurable_finite_polyhedral_slices {k : ℕ}
    (s : Fin k → Finset E) (d : ℕ) (hs : ∀ i, (s i).card ≤ d+1)
    (hd : d ≤ Module.finrank ℝ E)
    (Q : Fin k → Set E) (hQ : ∀ i, MeasurableSet (Q i))
    (hQs : ∀ i, Q i ⊆ convexHull ℝ (s i : Set E))
    (f : E → ℝ) (g : Fin k → E) (c : Fin k → ℝ)
    (hf : ∀ i p, p ∈ Q i → f p = ⟪g i,p⟫_ℝ+c i) :
    Measurable (fun t => μHE[d-1] ((⋃ i, Q i) ∩ {p | f p=t})) := by
  let W := disjointed Q
  have hW (i : Fin k) : MeasurableSet (W i) :=
    disjointedRec (fun _ j ht => ht.diff (hQ j)) (hQ i)
  have hsub (i : Fin k) : W i ⊆ Q i := disjointed_subset Q i
  have hcover : (⋃ i, W i) = ⋃ i, Q i := iUnion_disjointed
  have hdisj : Pairwise fun i j => Disjoint (W i) (W j) := disjoint_disjointed Q
  have hm (i : Fin k) (t : ℝ) : MeasurableSet (W i ∩ {p | f p=t}) := by
    have he : W i ∩ {p | f p=t} = W i ∩ {p | ⟪g i,p⟫_ℝ+c i=t} := by
      ext p
      constructor <;> rintro ⟨hp,ht⟩
      · exact ⟨hp,by simpa only [Set.mem_ofPred_eq,← hf i p (hsub i hp)] using ht⟩
      · exact ⟨hp,by simpa only [Set.mem_ofPred_eq,hf i p (hsub i hp)] using ht⟩
    rw [he]
    exact (hW i).inter (measurableSet_eq_fun (by fun_prop) measurable_const)
  have he (t : ℝ) : μHE[d-1] ((⋃ i,Q i) ∩ {p | f p=t}) =
      ∑ i, μHE[d-1] (W i ∩ {p | f p=t}) := by
    rw [← hcover,Set.iUnion_inter,measure_iUnion]
    · exact tsum_fintype _
    · intro i j hij
      exact (hdisj hij).mono inter_subset_left inter_subset_left
    · intro i
      exact hm i t
  simp_rw [he]
  apply Finset.measurable_sum
  intro i _
  exact measurable_simplex_piece_slices (s i) d (hs i) hd (hW i)
    ((hsub i).trans (hQs i)) f (g i) (c i) (fun p hp => hf i p (hsub i hp))
lemma measurable_finite_affine_slices {I : Type*} [Fintype I]
    (s : I → Finset E) (d : ℕ) (hs : ∀ i, (s i).card ≤ d+1)
    (hd : d ≤ Module.finrank ℝ E)
    (Q : I → Set E) (hQ : ∀ i, MeasurableSet (Q i))
    (hQs : ∀ i, Q i ⊆ convexHull ℝ (s i : Set E))
    (f : E → ℝ) (g : I → E) (c : I → ℝ)
    (hf : ∀ i p, p ∈ Q i → f p = ⟪g i,p⟫_ℝ+c i) :
    Measurable (fun t => μHE[d-1] ((⋃ i, Q i) ∩ {p | f p=t})) := by
  classical
  let e := (Fintype.equivFin I).symm
  have he : (⋃ j, Q (e j)) = ⋃ i, Q i := e.surjective.iUnion_comp Q
  rw [← he]
  exact measurable_finite_polyhedral_slices (fun j => s (e j)) d (fun j => hs (e j)) hd
    (fun j => Q (e j)) (fun j => hQ (e j)) (fun j => hQs (e j)) f
    (fun j => g (e j)) (fun j => c (e j)) (fun j => hf (e j))
lemma measurable_finite_max_slices {I J : Type*} [Fintype I] [Fintype J] [Nonempty J]
    (s : I → Finset E) (d : ℕ) (hs : ∀ i, (s i).card ≤ d+1)
    (hd : d ≤ Module.finrank ℝ E)
    (Q : I → Set E) (hQ : ∀ i, MeasurableSet (Q i))
    (hQs : ∀ i, Q i ⊆ convexHull ℝ (s i : Set E))
    (g : I → J → E) (c : I → J → ℝ) (f : E → ℝ)
    (hf : ∀ i p, p ∈ Q i → f p = Finset.univ.sup' Finset.univ_nonempty
      (fun j => ⟪g i j,p⟫_ℝ+c i j)) :
    Measurable (fun t => μHE[d-1] ((⋃ i, Q i) ∩ {p | f p=t})) := by
  classical
  let W (a : I × J) := Q a.1 ∩ ⋂ j, {p | ⟪g a.1 j,p⟫_ℝ+c a.1 j ≤
    ⟪g a.1 a.2,p⟫_ℝ+c a.1 a.2}
  have hW (a : I × J) : MeasurableSet (W a) := by
    exact (hQ a.1).inter (MeasurableSet.iInter fun j =>
      measurableSet_le (by fun_prop) (by fun_prop))
  have hWQ (a : I × J) : W a ⊆ Q a.1 := inter_subset_left
  have hcover : (⋃ a, W a) = ⋃ i, Q i := by
    apply Set.Subset.antisymm
    · simp only [iUnion_subset_iff]
      intro a
      exact (hWQ a).trans (subset_iUnion Q a.1)
    · intro p hp
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hp
      obtain ⟨j,_,hj⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
        (fun j => ⟪g i j,p⟫_ℝ+c i j)
      apply Set.mem_iUnion.mpr
      refine ⟨(i,j),hi,Set.mem_iInter.mpr ?_⟩
      intro l
      change ⟪g i l,p⟫_ℝ+c i l ≤ ⟪g i j,p⟫_ℝ+c i j
      rw [← hj]
      exact Finset.le_sup' (fun j => ⟪g i j,p⟫_ℝ+c i j) (Finset.mem_univ l)
  have hbranch (a : I × J) (p : E) (hp : p ∈ W a) :
      f p = ⟪g a.1 a.2,p⟫_ℝ+c a.1 a.2 := by
    rw [hf a.1 p hp.1]
    apply le_antisymm
    · exact Finset.sup'_le _ _ (fun j _ => Set.mem_iInter.mp hp.2 j)
    · exact Finset.le_sup' (fun j => ⟪g a.1 j,p⟫_ℝ+c a.1 j) (Finset.mem_univ a.2)
  rw [← hcover]
  exact measurable_finite_affine_slices (fun a => s a.1) d (fun a => hs a.1) hd W hW
    (fun a => (hWQ a).trans (hQs a.1)) f (fun a => g a.1 a.2)
    (fun a => c a.1 a.2) hbranch
end
end BassTrace.Sparse
end OAI

end
section
namespace OAI
noncomputable section
namespace BassTrace.Sparse
section
open MeasureTheory Set Finset
open scoped ENNReal InnerProductSpace
lemma barycentricParam_potential {n : ℕ} (ℓ : Fin (n+1) → ℝ) (x : Fin n → ℝ) :
    ∑ i, ℓ i * barycentricParam x i = ℓ 0 + ∑ i, (ℓ i.succ-ℓ 0)*x i := by
  rw [Fin.sum_univ_succ]
  simp only [barycentricParam_zero,barycentricParam_succ,sub_mul,Finset.sum_sub_distrib,
    ← Finset.mul_sum]
  ring
lemma treeParam_potential {n : ℕ} (T : SimpleGraph (Fin (n+1))) (hT : T.IsTree)
    (ℓ : Fin (n+1) → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    (∑ i, ℓ i * treeParam T hT x i) / Real.sqrt n =
      ⟪treeGradient T hT ℓ,x⟫_ℝ + ℓ 0 / Real.sqrt n := by
  rw [treeParam,barycentricParam_potential,add_div,treeChart_potential]
  rw [real_inner_comm]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  ring
lemma treeArea_coarea {n : ℕ} (hn : 0<n)
    (T : SimpleGraph (Fin (n+1))) (hT : T.IsTree)
    {I J : Type*} [Fintype I] [Fintype J] [Nonempty J]
    (s : I → Finset (Fin (n+1) → ℝ)) (d : ℕ) (hs : ∀ i, (s i).card≤d+1)
    (hd : d≤n) (hplane : ∀ i p, p∈s i → ∑ v,p v=1)
    (Q : I → Set (Fin (n+1) → ℝ)) (hQ : ∀ i, MeasurableSet (Q i))
    (hQs : ∀ i, Q i ⊆ convexHull ℝ (s i : Set (Fin (n+1) → ℝ)))
    (ℓ : I → J → Fin (n+1) → ℝ)
    (hℓ : ∀ i j u v, T.Adj u v → |ℓ i j u-ℓ i j v|≤1)
    (f : (Fin (n+1) → ℝ) → ℝ)
    (hf : ∀ i p, p∈Q i → f p=Finset.univ.sup' Finset.univ_nonempty
      (fun j => (∑ v,ℓ i j v*p v)/Real.sqrt n)) (r b : ℝ) :
    (∫⁻ t in Ioo r b, treeArea T hT (d-1) ((⋃ i,Q i) ∩ {p | f p=t})) ≤
      treeArea T hT d ((⋃ i,Q i) ∩ {p | f p≤b}) := by
  classical
  let s' i := (s i).image (treeCoordinates T hT)
  let Q' i := treeParam T hT ⁻¹' Q i
  have hQs' (i : I) : Q' i ⊆ convexHull ℝ (s' i : Set (EuclideanSpace ℝ (Fin n))) := by
    have hh := Set.preimage_mono (f := treeParam T hT) (hQs i)
    rw [treeParam_preimage_simplex T hT (s i) (hplane i)] at hh
    simpa only [s',Finset.coe_image] using hh
  have hh := finite_max_coarea s' d (fun i => (Finset.card_image_le).trans (hs i))
    (by simpa only [finrank_euclideanSpace_fin] using hd) Q'
    (fun i => (hQ i).preimage (continuous_treeParam T hT).measurable) hQs'
    (fun i j => treeGradient T hT (ℓ i j))
    (fun i j => treeGradient_norm_le_one hn T hT (ℓ i j) (hℓ i j))
    (fun i j => ℓ i j 0 / Real.sqrt n) (f ∘ treeParam T hT)
    (fun i p hp => by
      rw [Function.comp_apply,hf i _ hp]
      congr 1
      funext j
      exact treeParam_potential T hT (ℓ i j) p) r b
  simpa only [treeArea,Set.preimage_inter,Set.preimage_iUnion,Set.preimage_ofPred_eq,
    Function.comp_apply,Q'] using hh
lemma measurable_treeArea_slices {n : ℕ}
    (T : SimpleGraph (Fin (n+1))) (hT : T.IsTree)
    {I J : Type*} [Fintype I] [Fintype J] [Nonempty J]
    (s : I → Finset (Fin (n+1) → ℝ)) (d : ℕ) (hs : ∀ i, (s i).card≤d+1)
    (hd : d≤n) (hplane : ∀ i p, p∈s i → ∑ v,p v=1)
    (Q : I → Set (Fin (n+1) → ℝ)) (hQ : ∀ i, MeasurableSet (Q i))
    (hQs : ∀ i, Q i ⊆ convexHull ℝ (s i : Set (Fin (n+1) → ℝ)))
    (ℓ : I → J → Fin (n+1) → ℝ)
    (f : (Fin (n+1) → ℝ) → ℝ)
    (hf : ∀ i p, p∈Q i → f p=Finset.univ.sup' Finset.univ_nonempty
      (fun j => (∑ v,ℓ i j v*p v)/Real.sqrt n)) :
    Measurable (fun t => treeArea T hT (d-1) ((⋃ i,Q i) ∩ {p | f p=t})) := by
  classical
  let s' i := (s i).image (treeCoordinates T hT)
  let Q' i := treeParam T hT ⁻¹' Q i
  have hQs' (i : I) : Q' i ⊆ convexHull ℝ (s' i : Set (EuclideanSpace ℝ (Fin n))) := by
    have hh := Set.preimage_mono (f := treeParam T hT) (hQs i)
    rw [treeParam_preimage_simplex T hT (s i) (hplane i)] at hh
    simpa only [s',Finset.coe_image] using hh
  have hh := measurable_finite_max_slices s' d (fun i => (Finset.card_image_le).trans (hs i))
    (by simpa only [finrank_euclideanSpace_fin] using hd) Q'
    (fun i => (hQ i).preimage (continuous_treeParam T hT).measurable) hQs'
    (fun i j => treeGradient T hT (ℓ i j))
    (fun i j => ℓ i j 0 / Real.sqrt n) (f ∘ treeParam T hT)
    (fun i p hp => by
      rw [Function.comp_apply,hf i _ hp]
      congr 1
      funext j
      exact treeParam_potential T hT (ℓ i j) p)
  simpa only [treeArea,Set.preimage_inter,Set.preimage_iUnion,Set.preimage_ofPred_eq,
    Function.comp_apply,Q'] using hh
lemma simplexArea_coarea {n : ℕ} (hn : 0<n)
    (Γ : SimpleGraph (Fin (n+1)))
    {I J : Type*} [Fintype I] [Fintype J] [Nonempty J]
    (s : I → Finset (Fin (n+1) → ℝ)) (d : ℕ) (hs : ∀ i, (s i).card≤d+1)
    (hd : d≤n) (hplane : ∀ i p, p∈s i → ∑ v,p v=1)
    (Q : I → Set (Fin (n+1) → ℝ)) (hQ : ∀ i, MeasurableSet (Q i))
    (hQs : ∀ i, Q i ⊆ convexHull ℝ (s i : Set (Fin (n+1) → ℝ)))
    (ℓ : I → J → Fin (n+1) → ℝ)
    (hℓ : ∀ i j u v, Γ.Adj u v → |ℓ i j u-ℓ i j v|≤1)
    (f : (Fin (n+1) → ℝ) → ℝ)
    (hf : ∀ i p, p∈Q i → f p=Finset.univ.sup' Finset.univ_nonempty
      (fun j => (∑ v,ℓ i j v*p v)/Real.sqrt n)) (r b : ℝ) :
    (∫⁻ t in Ioo r b, simplexArea Γ (d-1) ((⋃ i,Q i) ∩ {p | f p=t})) ≤
      simplexArea Γ d ((⋃ i,Q i) ∩ {p | f p≤b}) := by
  classical
  have hm (T : SpanningTree Γ) := measurable_treeArea_slices T.val T.property.2
    s d hs hd hplane Q hQ hQs ℓ f hf
  simp only [simplexArea,div_eq_mul_inv]
  rw [lintegral_mul_const _ (Finset.measurable_sum _ (fun T _ => hm T)),
    lintegral_finsetSum _ (fun T _ => hm T)]
  apply mul_le_mul_left
  apply Finset.sum_le_sum
  intro T _
  exact treeArea_coarea hn T.val T.property.2 s d hs hd hplane Q hQ hQs ℓ
    (fun i j u v huv => hℓ i j u v (T.property.1 huv)) f hf r b
lemma measurable_simplexArea_slices {n : ℕ}
    (Γ : SimpleGraph (Fin (n+1)))
    {I J : Type*} [Fintype I] [Fintype J] [Nonempty J]
    (s : I → Finset (Fin (n+1) → ℝ)) (d : ℕ) (hs : ∀ i, (s i).card≤d+1)
    (hd : d≤n) (hplane : ∀ i p, p∈s i → ∑ v,p v=1)
    (Q : I → Set (Fin (n+1) → ℝ)) (hQ : ∀ i, MeasurableSet (Q i))
    (hQs : ∀ i, Q i ⊆ convexHull ℝ (s i : Set (Fin (n+1) → ℝ)))
    (ℓ : I → J → Fin (n+1) → ℝ)
    (f : (Fin (n+1) → ℝ) → ℝ)
    (hf : ∀ i p, p∈Q i → f p=Finset.univ.sup' Finset.univ_nonempty
      (fun j => (∑ v,ℓ i j v*p v)/Real.sqrt n)) :
    Measurable (fun t => simplexArea Γ (d-1) ((⋃ i,Q i) ∩ {p | f p=t})) := by
  classical
  unfold simplexArea
  apply Measurable.div_const
  exact Finset.measurable_sum _ (fun T _ => measurable_treeArea_slices T.val T.property.2
    s d hs hd hplane Q hQ hQs ℓ f hf)
end
open Set Finset MeasureTheory
open scoped BassTrace.Sparse ENNReal Classical
variable {Y : Type*} [DecidableEq Y]
lemma simplexEmbed_nonneg {n : ℕ} (s : Finset Y) (hs : s.card=n+1)
    {p : Fin (n+1) → ℝ} (hp : ∀ i,0≤p i) (y : Y) : 0 ≤ simplexEmbed s hs p y := by
  by_cases hy : y∈s
  · obtain ⟨i,hi⟩ := (simplexEnumeration s hs).surjective ⟨y,hy⟩
    have h := congrFun (simplexCoordinates_embed s hs p) i
    change simplexEmbed s hs p (simplexEnumeration s hs i).val = p i at h
    rw [hi] at h
    rw [h]
    exact hp i
  · rw [Finsupp.notMem_support_iff.mp (fun h => hy (simplexEmbed_support s hs p h))]
omit [DecidableEq Y] in
lemma simplexEmbed_total {n : ℕ} (s : Finset Y) (hs : s.card=n+1)
    (p : Fin (n+1) → ℝ) : (simplexEmbed s hs p).sum (fun _ r=>r)=∑ i,p i := by
  rw [Finsupp.sum_of_support_subset _ (simplexEmbed_support s hs p) _ (by intros; rfl)]
  rw [← (Finset.sum_attach s (fun y : Y => simplexEmbed s hs p y))]
  change (∑ y : s, simplexEmbed s hs p y.val) = _
  rw [← (simplexEnumeration s hs).sum_comp (fun y : s => simplexEmbed s hs p y.val)]
  congr 1
  funext i
  exact congrFun (simplexCoordinates_embed s hs p) i
def simplexPoint {n : ℕ} (s : Finset Y) (hs : s.card=n+1)
    (p : Fin (n+1) → ℝ) (hp : p∈fullBarycentricSimplex n) : FinProbability Y where
  coeff := simplexEmbed s hs p
  nonneg := simplexEmbed_nonneg s hs hp.1
  total := (simplexEmbed_total s hs p).trans hp.2
variable [MetricSpace Y]
def chartDistance {n : ℕ} (s : Finset Y) (hs : s.card=n+1) (c : FinProbability Y)
    (p : Fin (n+1) → ℝ) : ℝ :=
  if hp : p∈fullBarycentricSimplex n then FinProbability.rho n c (simplexPoint s hs p hp) else 0
lemma chartDistance_apply {n : ℕ} (s : Finset Y) (hs : s.card=n+1)
    (c : FinProbability Y) (p : Fin (n+1) → ℝ) (hp : p∈fullBarycentricSimplex n) :
    chartDistance s hs c p = FinProbability.rho n c (simplexPoint s hs p hp) := by
  simp only [chartDistance,dite_eq_left hp]
omit [MetricSpace Y] in
lemma ballBranch_coordinates {n : ℕ} (s S : Finset Y) (hs : s.card=n+1) (hsS : s⊆S)
    (c : FinProbability Y) (l : S→ℝ) (p : Fin (n+1) → ℝ) :
    ballBranch S c n l (simplexEmbed s hs p) =
      (∑ i,(centerBranchValue S c l-l ⟨(simplexEnumeration s hs i).val,
        hsS (simplexEnumeration s hs i).property⟩)*p i)/Real.sqrt n := by
  rw [ballBranch_apply]
  have hm : ∑ y : S,((centerBranchValue S c l-l y)/Real.sqrt n)*simplexEmbed s hs p y =
      ∑ y : s,((centerBranchValue S c l-l ⟨y.val,hsS y.property⟩)/Real.sqrt n)*
        simplexEmbed s hs p y := by
    apply Finset.sum_bij_ne_zero (fun y _ _ => ⟨y.val,by
      by_contra hy
      have hzero := Finsupp.notMem_support_iff.mp
        (fun h => hy (simplexEmbed_support s hs p h))
      simp [hzero] at *⟩)
    · intros; simp
    · intro a ha hna b hb hnb he
      exact Subtype.ext (congrArg (fun z : s => z.val) he)
    · intro y _ hy
      exact ⟨⟨y.val,hsS y.property⟩,by simp,by simpa using hy,rfl⟩
    · intros; rfl
  rw [hm,← (simplexEnumeration s hs).sum_comp]
  simp_rw [show ∀ i, simplexEmbed s hs p (simplexEnumeration s hs i).val=p i from
    fun i=>congrFun (simplexCoordinates_embed s hs p) i,
    div_mul_eq_mul_div,Finset.sum_div]
def distancePotential {n : ℕ} (s S : Finset Y) (hs : s.card=n+1) (hsS : s⊆S)
    (c : FinProbability Y) (l : S → ℝ) (i : Fin (n+1)) : ℝ :=
  centerBranchValue S c l-l ⟨(simplexEnumeration s hs i).val,
    hsS (simplexEnumeration s hs i).property⟩
omit [DecidableEq Y] in
lemma distancePotential_edge {n : ℕ} (s S : Finset Y) (hs : s.card=n+1)
    (hsS : s⊆S) (c : FinProbability Y) (l : S→ℝ) (hl : l∈potentialVertices)
    (u v : Fin (n+1))
    (huv : dist (simplexEnumeration s hs u).val (simplexEnumeration s hs v).val≤1) :
    |distancePotential s S hs hsS c l u-distancePotential s S hs hsS c l v|≤1 := by
  have hh := (potentialVertices_subset l hl).2
    ⟨(simplexEnumeration s hs v).val,hsS (simplexEnumeration s hs v).property⟩
    ⟨(simplexEnumeration s hs u).val,hsS (simplexEnumeration s hs u).property⟩
  unfold distancePotential
  rw [show ∀ a b d : ℝ,(a-b)-(a-d)=d-b from by intros; ring]
  exact hh.trans (by simpa only [Subtype.dist_eq,dist_comm] using huv)
lemma chartDistance_max {n : ℕ} (s S : Finset Y) (hs : s.card=n+1) (hsS : s⊆S)
    (c : FinProbability Y) (hc : c.coeff.support⊆S)
    [Nonempty (potentialVertices : Finset (S→ℝ))]
    (p : Fin (n+1) → ℝ) (hp : p∈fullBarycentricSimplex n) :
    chartDistance s hs c p=Finset.univ.sup' Finset.univ_nonempty
      (fun l : (potentialVertices : Finset (S→ℝ)) =>
        (∑ i,distancePotential s S hs hsS c l.val i*p i)/Real.sqrt n) := by
  have hpS : (simplexPoint s hs p hp).coeff.support⊆S :=
    (simplexEmbed_support s hs p).trans hsS
  obtain ⟨l,hl,heq,hmax⟩ := exists_ballBranch_maximizer S c (simplexPoint s hs p hp) hc hpS n
  rw [chartDistance_apply s hs c p hp]
  apply le_antisymm
  · rw [heq]
    change ballBranch S c n l (simplexEmbed s hs p)≤_
    rw [ballBranch_coordinates s S hs hsS]
    change (∑ i,distancePotential s S hs hsS c l i*p i)/Real.sqrt n ≤ _
    exact Finset.le_sup' (fun l : (potentialVertices : Finset (S→ℝ)) =>
      (∑ i,distancePotential s S hs hsS c l.val i*p i)/Real.sqrt n)
      (Finset.mem_univ (⟨l,hl⟩ : (potentialVertices : Finset (S→ℝ))))
  · apply Finset.sup'_le
    intro l _
    have hh := hmax l.val l.property
    change ballBranch S c n l.val (simplexEmbed s hs p)≤_ at hh
    simpa only [ballBranch_coordinates s S hs hsS,distancePotential] using hh
theorem graphBall_coarea {n : ℕ} (hn : 0<n)
    (σ : Finset Y) (hσ : σ.card=n+1) (c : FinProbability Y)
    (Γ : SimpleGraph (Fin (n+1)))
    (hΓ : ∀ u v, Γ.Adj u v →
      dist (simplexEnumeration σ hσ u).val (simplexEnumeration σ hσ v).val≤1)
    {I : Type*} [Fintype I]
    (s : I → Finset (Fin (n+1) → ℝ)) (d : ℕ) (hs : ∀ i,(s i).card≤d+1)
    (hd : d≤n) (hplane : ∀ i p,p∈s i → ∑ v,p v=1)
    (Q : I → Set (Fin (n+1) → ℝ)) (hQ : ∀ i,MeasurableSet (Q i))
    (hQs : ∀ i,Q i⊆convexHull ℝ (s i : Set (Fin (n+1) → ℝ)))
    (hfull : ∀ i,Q i⊆fullBarycentricSimplex n) (r b : ℝ) :
    (∫⁻ t in Ioo r b, simplexArea Γ (d-1) ((⋃ i,Q i) ∩ {p | chartDistance σ hσ c p=t})) ≤
      simplexArea Γ d ((⋃ i,Q i) ∩ {p | chartDistance σ hσ c p≤b}) := by
  let S := σ ∪ c.coeff.support
  have hσS : σ⊆S := Finset.subset_union_left
  have hcS : c.coeff.support⊆S := Finset.subset_union_right
  obtain ⟨l,hl,-⟩ := exists_ballBranch_maximizer S c c hcS hcS n
  let : Nonempty (potentialVertices : Finset (S→ℝ)) := ⟨⟨l,hl⟩⟩
  exact simplexArea_coarea hn Γ s d hs hd hplane Q hQ hQs
    (fun _ (l : (potentialVertices : Finset (S→ℝ))) => distancePotential σ S hσ hσS c l.val)
    (fun _ l u v huv => distancePotential_edge σ S hσ hσS c l.val l.property u v (hΓ u v huv))
    (chartDistance σ hσ c) (fun i p hp => chartDistance_max σ S hσ hσS c hcS p (hfull i hp)) r b
lemma measurable_graphBall_slices {n : ℕ}
    (σ : Finset Y) (hσ : σ.card=n+1) (c : FinProbability Y)
    (Γ : SimpleGraph (Fin (n+1))) {I : Type*} [Fintype I]
    (s : I → Finset (Fin (n+1) → ℝ)) (d : ℕ) (hs : ∀ i,(s i).card≤d+1)
    (hd : d≤n) (hplane : ∀ i p,p∈s i → ∑ v,p v=1)
    (Q : I → Set (Fin (n+1) → ℝ)) (hQ : ∀ i,MeasurableSet (Q i))
    (hQs : ∀ i,Q i⊆convexHull ℝ (s i : Set (Fin (n+1) → ℝ)))
    (hfull : ∀ i,Q i⊆fullBarycentricSimplex n) :
    Measurable (fun t => simplexArea Γ (d-1)
      ((⋃ i,Q i) ∩ {p | chartDistance σ hσ c p=t})) := by
  let S := σ ∪ c.coeff.support
  have hσS : σ⊆S := Finset.subset_union_left
  have hcS : c.coeff.support⊆S := Finset.subset_union_right
  obtain ⟨l,hl,-⟩ := exists_ballBranch_maximizer S c c hcS hcS n
  let : Nonempty (potentialVertices : Finset (S→ℝ)) := ⟨⟨l,hl⟩⟩
  exact measurable_simplexArea_slices Γ s d hs hd hplane Q hQ hQs
    (fun _ (l : (potentialVertices : Finset (S→ℝ))) => distancePotential σ S hσ hσS c l.val)
    (chartDistance σ hσ c) (fun i p hp => chartDistance_max σ S hσ hσS c hcS p (hfull i hp))
end BassTrace.Sparse
end
end OAI

end
section
namespace OAI
noncomputable section
namespace BassTrace
open Set MeasureTheory
namespace Sparse
section
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
lemma measurable_intrinsicInterior_finite_hull [MeasurableSpace V] [BorelSpace V]
    (s : Finset V) : MeasurableSet (intrinsicInterior ℝ (convexHull ℝ (s : Set V))) := by
  have hA : IsClosed ((affineSpan ℝ (convexHull ℝ (s : Set V))) : Set V) := by
    rw [affineSpan_convexHull]
    let := finiteDimensional_direction_affineSpan_of_finite ℝ s.finite_toSet
    exact (affineSpan ℝ (s : Set V)).closed_of_finiteDimensional
  exact (hA.isClosedEmbedding_subtypeVal.measurableEmbedding.measurableSet_image).mpr
    isOpen_interior.measurableSet
end
section
open Set Finset MeasureTheory
open scoped BassTrace.Sparse ENNReal Classical
variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y]
  [TopologicalSpace X] [MulAction H X]
variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}
lemma support_of_mem_original_hull (s : Finset Y) {p : Y →₀ ℝ}
    (hp : p∈convexHull ℝ (simplexVertices s : Set (Y →₀ ℝ))) : p.support⊆s := by
  have hprob : p∈probabilitySet s := by
    simpa only [simplexVertices,Finset.coe_image,convexHull_single_eq_probabilitySet] using hp
  exact hprob.2.2
lemma simplexCoordinates_full {n : ℕ} (s : Finset Y) (hs : s.card=n+1)
    {p : Y →₀ ℝ} (hp : p∈convexHull ℝ (simplexVertices s : Set (Y →₀ ℝ))) :
    simplexCoordinates s hs p∈fullBarycentricSimplex n := by
  have hprob : p∈probabilitySet s := by
    simpa only [simplexVertices,Finset.coe_image,convexHull_single_eq_probabilitySet] using hp
  exact ⟨fun i => hprob.1 _,simplexCoordinates_sum s hs hp⟩
lemma marked_chart_pieces (Q : OrbitForms.MarkedPair (H := H) (X := X)
    (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (σ : SourceTop K n) (d : ℕ) (x : X)
    (hd : ∀ t∈(Q.T.val x).complex.faces,
      convexHull ℝ (t : Set (Y →₀ ℝ))⊆Q.P.val x → t.card≤d+1) :
    ∃ (I : Type) (_ : Fintype I) (s : I → Finset (Fin (n+1) → ℝ))
      (A : I → Set (Fin (n+1) → ℝ)),
      (∀ i,(s i).card≤d+1) ∧
      (∀ i p,p∈s i → ∑ v,p v=1) ∧
      (∀ i,MeasurableSet (A i)) ∧
      (∀ i,A i⊆convexHull ℝ (s i : Set (Fin (n+1) → ℝ))) ∧
      (∀ i,A i⊆fullBarycentricSimplex n) ∧
      (⋃ i,A i)=simplexCoordinates σ.val σ.property.2 '' (Q.P.val x∩sourceInterior σ.val) := by
  let : MeasurableSpace (Y →₀ ℝ) := borel (Y →₀ ℝ)
  let : BorelSpace (Y →₀ ℝ) := ⟨rfl⟩
  let η := simplexCoordinates σ.val σ.property.2
  let e := simplexEmbed σ.val σ.property.2
  let L := Cuts.restrictComplex (Cuts.geometricRestriction (Q.T.val x).complex (Q.P.val x))
    (convexHull ℝ (simplexVertices σ.val : Set (Y →₀ ℝ)))
  have hf : L.faces.Finite := ((Q.T.val x).finite (simplexVertices σ.val)
    ⟨σ.val,σ.property.1,rfl⟩).subset (fun _ h => ⟨h.1.1,h.2⟩)
  let F := hf.toFinset
  let I := Fin F.card
  let α : I ≃ {t // t∈L.faces} :=
    (F.equivFin).symm.trans (Set.equivOfEq (by ext t; exact hf.mem_toFinset))
  let s (i : I) := (α i).val.image η
  let A (i : I) := convexHull ℝ (s i : Set (Fin (n+1) → ℝ)) ∩ e ⁻¹' sourceInterior σ.val
  have hsource (i : I) : convexHull ℝ ((α i).val : Set (Y →₀ ℝ)) ⊆
      convexHull ℝ (simplexVertices σ.val : Set (Y →₀ ℝ)) :=
    convexHull_min (α i).property.2 (convex_convexHull ℝ _)
  have himage (i : I) : convexHull ℝ (s i : Set (Fin (n+1) → ℝ)) =
      η '' convexHull ℝ ((α i).val : Set (Y →₀ ℝ)) := by
    change convexHull ℝ (((α i).val.image η : Finset (Fin (n+1) → ℝ)) : Set (Fin (n+1) → ℝ)) = _
    rw [Finset.coe_image,← η.image_convexHull]
  have hin (i : I) {p : Fin (n+1) → ℝ}
      (hp : p∈convexHull ℝ (s i : Set (Fin (n+1) → ℝ))) :
      e p∈convexHull ℝ ((α i).val : Set (Y →₀ ℝ)) := by
    rw [himage i] at hp
    obtain ⟨q,hq,rfl⟩ := hp
    change simplexEmbed σ.val σ.property.2 (simplexCoordinates σ.val σ.property.2 q)∈_
    rw [simplexEmbed_coordinates _ _ (support_of_mem_original_hull _ (hsource i hq))]
    exact hq
  refine ⟨I,inferInstance,s,A,?_,?_,?_,?_,?_,?_⟩
  · intro i
    exact Finset.card_image_le.trans (hd _ (α i).property.1.1 (α i).property.1.2)
  · intro i p hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    exact simplexCoordinates_sum _ _ ((α i).property.2 hq)
  · intro i
    exact ((s i).finite_toSet.isCompact_convexHull ℝ).isClosed.measurableSet.inter
      ((measurable_intrinsicInterior_finite_hull (simplexVertices σ.val)).preimage
        e.continuous_of_finiteDimensional.measurable)
  · exact fun _ => Set.inter_subset_left
  · intro i p hp
    have hp' := hp.1
    rw [himage i] at hp'
    obtain ⟨q,hq,rfl⟩ := hp'
    exact simplexCoordinates_full _ _ (hsource i hq)
  · apply Set.Subset.antisymm
    · intro p hp
      obtain ⟨i,hp⟩ := Set.mem_iUnion.mp hp
      refine ⟨e p,⟨(α i).property.1.2 (hin i hp.1),hp.2⟩,?_⟩
      exact simplexCoordinates_embed _ _ p
    · rintro _ ⟨p,hp,rfl⟩
      have hpL : p∈L.space := by
        change p∈(Cuts.restrictComplex (Cuts.geometricRestriction (Q.T.val x).complex (Q.P.val x))
          (convexHull ℝ (simplexVertices σ.val : Set (Y →₀ ℝ)))).space
        rw [Q.P.trace_space (simplexVertices σ.val) ⟨σ.val,σ.property.1,rfl⟩ x]
        exact ⟨hp.1,intrinsicInterior_subset hp.2⟩
      obtain ⟨t,ht,hpt⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hpL
      obtain ⟨i,hi⟩ := α.surjective ⟨t,ht⟩
      apply Set.mem_iUnion.mpr
      refine ⟨i,?_,?_⟩
      · rw [himage i,hi]
        exact ⟨p,hpt,rfl⟩
      · change simplexEmbed σ.val σ.property.2 (simplexCoordinates σ.val σ.property.2 p)∈sourceInterior σ.val
        rw [simplexEmbed_coordinates _ _ (support_of_mem_sourceInterior _ hp.2)]
        exact hp.2
end
open Set MeasureTheory
open scoped ENNReal
lemma IsLocallyConstant.measurable_uncurry {X A Y : Type*}
    [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    [MeasurableSpace Y] {f : X → A} (hf : IsLocallyConstant f)
    (F : A → Y → ℝ≥0∞) (hF : ∀ a∈Set.range f,Measurable (F a)) :
    Measurable (fun p : X×Y => F (f p.1) p.2) := by
  classical
  let S := hf.range_finite.toFinset
  have he : (fun p : X×Y => F (f p.1) p.2) =
      fun p => ∑ a∈S, ({q : X×Y | f q.1=a}.indicator (fun q=>F a q.2)) p := by
    funext p
    rw [Finset.sum_eq_single (f p.1)]
    · simp
    · intro a _ ha
      exact Set.indicator_of_notMem (by exact Ne.symm ha) _
    · intro h
      exact (h (hf.range_finite.mem_toFinset.mpr (Set.mem_range_self _))).elim
  rw [he]
  apply Finset.measurable_sum
  intro a ha
  apply ((hF a (hf.range_finite.mem_toFinset.mp ha)).comp measurable_snd).indicator
  exact ((hf.isClopen_fiber a).isOpen.measurableSet.preimage measurable_fst)
end Sparse
namespace Sparse.GraphGeometry
open Set Finset MeasureTheory
open scoped BassTrace.Sparse ENNReal Classical
section
variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y]
  [TopologicalSpace X] [MulAction H X]
variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}
variable (Γ : SimpleGraph Y) (hΓ : Γ.Connected)
omit [Group H] [MulAction H Y] [TopologicalSpace X] [MulAction H X] in
lemma chartDistance_coordinates (σ : SourceTop K n) (c : FinProbability Y)
    {p : Y →₀ ℝ} (hp : p∈sourceInterior σ.val) :
    letI := graphMetric Γ hΓ
    chartDistance σ.val σ.property.2 c (simplexCoordinates σ.val σ.property.2 p) =
      centerDistance Γ hΓ K n c p := by
  let := graphMetric Γ hΓ
  have hpK : p∈(Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space :=
    Geometry.SimplicialComplex.mem_space_iff.mpr
      ⟨simplexVertices σ.val,⟨σ.val,σ.property.1,rfl⟩,intrinsicInterior_subset hp⟩
  rw [chartDistance_apply _ _ _ _ (simplexCoordinates_full _ _ (intrinsicInterior_subset hp))]
  simp only [centerDistance,dite_eq_left hpK]
  congr 1
  apply FinProbability.ext_coeff
  change simplexEmbed σ.val σ.property.2 (simplexCoordinates σ.val σ.property.2 p) = _
  rw [simplexEmbed_coordinates _ _ (support_of_mem_sourceInterior _ hp),pointProbability_coeff]
omit [Group H] [MulAction H Y] [TopologicalSpace X] [MulAction H X] in
lemma coordinates_radius_inter (σ : SourceTop K n) (c : FinProbability Y)
    (A : Set (Y →₀ ℝ)) (hA : A⊆sourceInterior σ.val) (R : Set ℝ) :
    letI := graphMetric Γ hΓ
    simplexCoordinates σ.val σ.property.2 '' (A∩(centerDistance Γ hΓ K n c ⁻¹' R)) =
    (simplexCoordinates σ.val σ.property.2 '' A) ∩
      (chartDistance σ.val σ.property.2 c ⁻¹' R) := by
  let := graphMetric Γ hΓ
  ext p
  constructor
  · rintro ⟨q,⟨hq,hqR⟩,rfl⟩
    refine ⟨⟨q,hq,rfl⟩,?_⟩
    simpa only [Set.mem_preimage,chartDistance_coordinates Γ hΓ σ c (hA hq)] using hqR
  · rintro ⟨⟨q,hq,rfl⟩,hpR⟩
    refine ⟨q,⟨hq,?_⟩,rfl⟩
    simpa only [Set.mem_preimage,chartDistance_coordinates Γ hΓ σ c (hA hq)] using hpR
theorem marked_ball_coarea (hn : 0<n)
    (Q : OrbitForms.MarkedPair (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (σ : SourceTop K n) (c : FinProbability Y) (d : ℕ) (hdn : d≤n) (x : X)
    (hd : ∀ t∈(Q.T.val x).complex.faces,
      convexHull ℝ (t : Set (Y →₀ ℝ))⊆Q.P.val x → t.card≤d+1) (r b : ℝ) :
    (∫⁻ t in Ioo r b,localOriginalArea Γ Q σ (d-1)
      {v | centerDistance Γ hΓ K n c v=t} x) ≤
      localOriginalArea Γ Q σ d {v | centerDistance Γ hΓ K n c v≤b} x := by
  let := graphMetric Γ hΓ
  obtain ⟨I,hI,s,A,hs,hplane,hA,hAs,hfull,he⟩ := marked_chart_pieces Q σ d x hd
  let : Fintype I := hI
  have hgraph (u v : Fin (n+1)) (huv : (simplexGraph Γ σ.val σ.property.2).Adj u v) :
      dist (simplexEnumeration σ.val σ.property.2 u).val
        (simplexEnumeration σ.val σ.property.2 v).val≤1 := by
    change (Γ.dist _ _ : ℝ)≤1
    exact_mod_cast (SimpleGraph.dist_eq_one_iff_adj.mpr (show Γ.Adj _ _ from huv)).le
  have hc := graphBall_coarea hn σ.val σ.property.2 c
    (simplexGraph Γ σ.val σ.property.2) hgraph s d hs hdn hplane A hA hAs hfull r b
  rw [he] at hc
  convert hc using 1
  · congr 1
    funext t
    unfold localOriginalArea
    congr 1
    simpa only [Set.inter_assoc, Set.preimage, Set.mem_singleton_iff] using
      coordinates_radius_inter Γ hΓ σ c (Q.P.val x∩sourceInterior σ.val)
        Set.inter_subset_right {t}
  · unfold localOriginalArea
    congr 1
    simpa only [Set.inter_assoc, Set.preimage, Set.mem_Iic] using
      coordinates_radius_inter Γ hΓ σ c (Q.P.val x∩sourceInterior σ.val)
        Set.inter_subset_right (Iic b)
lemma measurable_marked_ball_slices
    (Q : OrbitForms.MarkedPair (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (σ : SourceTop K n) (c : FinProbability Y) (d : ℕ) (hdn : d≤n) (x : X)
    (hd : ∀ t∈(Q.T.val x).complex.faces,
      convexHull ℝ (t : Set (Y →₀ ℝ))⊆Q.P.val x → t.card≤d+1) :
    Measurable (fun t => localOriginalArea Γ Q σ (d-1)
      {v | centerDistance Γ hΓ K n c v=t} x) := by
  let := graphMetric Γ hΓ
  obtain ⟨I,hI,s,A,hs,hplane,hA,hAs,hfull,he⟩ := marked_chart_pieces Q σ d x hd
  let : Fintype I := hI
  have hc := measurable_graphBall_slices σ.val σ.property.2 c
    (simplexGraph Γ σ.val σ.property.2) s d hs hdn hplane A hA hAs hfull
  rw [he] at hc
  convert hc using 1
  funext t
  unfold localOriginalArea
  congr 1
  simpa only [Set.inter_assoc, Set.preimage, Set.mem_singleton_iff] using
    coordinates_radius_inter Γ hΓ σ c (Q.P.val x∩sourceInterior σ.val)
      Set.inter_subset_right {t}
end
variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y]
  [TopologicalSpace X] [MulAction H X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}
variable (Γ : SimpleGraph Y) (hΓ : Γ.Connected)
lemma measurable_marked_ball_slices_joint
    (Q : OrbitForms.MarkedPair (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (σ : SourceTop K n) (c : FinProbability Y) (d : ℕ) (hdn : d≤n)
    (hd : ∀ x t,t∈(Q.T.val x).complex.faces →
      convexHull ℝ (t : Set (Y →₀ ℝ))⊆Q.P.val x → t.card≤d+1) :
    Measurable (fun p : X×ℝ => localOriginalArea Γ Q σ (d-1)
      {v | centerDistance Γ hΓ K n c v=p.2} p.1) := by
  let f (x : X) := Q.P.val x∩sourceInterior σ.val
  have hf : IsLocallyConstant f := Q.P.localConstancy_inter (simplexVertices σ.val)
    ⟨σ.val,σ.property.1,rfl⟩ _ intrinsicInterior_subset
  let F (A : Set (Y →₀ ℝ)) (t : ℝ) := simplexArea (simplexGraph Γ σ.val σ.property.2)
    (d-1) (simplexCoordinates σ.val σ.property.2 ''
      (A ∩ {v | centerDistance Γ hΓ K n c v=t}))
  have hF : ∀ A∈Set.range f,Measurable (F A) := by
    rintro A ⟨x,rfl⟩
    simpa only [F,f,Set.inter_assoc,localOriginalArea] using
      measurable_marked_ball_slices Γ hΓ Q σ c d hdn x (hd x)
  simpa only [F,f,Set.inter_assoc,localOriginalArea] using BassTrace.Sparse.IsLocallyConstant.measurable_uncurry hf F hF
theorem integrated_marked_ball_coarea [Countable Y]
    (Q : OrbitForms.MarkedPair (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (μ : Measure X) [SFinite μ] (B : Set X) (c : FinProbability Y)
    (hn : 0<n) (d : ℕ) (hdn : d≤n)
    (hd : ∀ x t,t∈(Q.T.val x).complex.faces →
      convexHull ℝ (t : Set (Y →₀ ℝ))⊆Q.P.val x → t.card≤d+1) (r b : ℝ) :
    (∫⁻ t in Ioo r b, ∫⁻ x in B, ∑' σ : SourceTop K n,
      localOriginalArea Γ Q σ (d-1) {v | centerDistance Γ hΓ K n c v=t} x ∂μ) ≤
      ∫⁻ x in B, ∑' σ : SourceTop K n,
        localOriginalArea Γ Q σ d {v | centerDistance Γ hΓ K n c v≤b} x ∂μ := by
  let : Countable (SourceTop K n) :=
    inferInstanceAs (Countable {s : Finset Y // s∈K.faces ∧ s.card=n+1})
  have hm (σ : SourceTop K n) := measurable_marked_ball_slices_joint Γ hΓ Q σ c d hdn hd
  rw [← lintegral_lintegral_swap ((Measurable.tsum hm).aemeasurable)]
  apply lintegral_mono
  intro x
  dsimp only
  rw [lintegral_tsum (fun σ => (measurable_marked_ball_slices Γ hΓ Q σ c d hdn x (hd x)).aemeasurable)]
  exact ENNReal.tsum_le_tsum (fun σ => marked_ball_coarea Γ hΓ hn Q σ c d hdn x (hd x) r b)
end Sparse.GraphGeometry
end BassTrace
end
end OAI

end
section
namespace OAI
noncomputable section
namespace BassTrace
open Set MeasureTheory
namespace Sparse
open Set Finset MeasureTheory
open scoped BassTrace.Sparse Classical ENNReal
variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y]
  [TopologicalSpace X] [MulAction H X]
variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}
def OrbitForms.SeparatingFiltration.admissibleStep
    {ρ : (Y →₀ ℝ) → (Y →₀ ℝ) → ℝ} {R : ℝ}
    (Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K) ρ R n)
    {j : ℕ} (hj : j<n) : Cuts.AdmissibleStep ρ R (Q.pair (j+1)).T (Q.pair (j+1)).P where
  next := (Q.pair j).T
  finer := Q.finer j hj
  oldMarked := fun x => (Q.finer j hj x).preserves_marked ((Q.pair (j+1)).P.marked x)
  zero := (Q.pair j).P
  subset := Q.nested j hj
  dimensionDrop := Q.drop j hj
  diameter := Q.diameter j hj
end Sparse
namespace Sparse.GraphGeometry
open Set Finset MeasureTheory
open scoped BassTrace.Sparse Classical ENNReal
section
variable {Y : Type*} [DecidableEq Y] [Countable Y]
local instance : MeasurableSpace (Y →₀ ℝ) := borel (Y →₀ ℝ)
local instance : BorelSpace (Y →₀ ℝ) := ⟨rfl⟩
variable (K : PreAbstractSimplicialComplex Y)
lemma measurable_realization : MeasurableSet
    (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space := by
  have he : (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space =
      ⋃ s∈K.faces, convexHull ℝ (simplexVertices s : Set (Y →₀ ℝ)) := by
    ext p
    rw [Geometry.SimplicialComplex.mem_space_iff]
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨_,⟨s,hs,rfl⟩,hp⟩
      exact ⟨s,hs,hp⟩
    · rintro ⟨s,hs,hp⟩
      exact ⟨simplexVertices s,⟨s,hs,rfl⟩,hp⟩
  rw [he]
  exact MeasurableSet.iUnion fun s => MeasurableSet.iUnion fun _ =>
    ((simplexVertices s).finite_toSet.isCompact_convexHull ℝ).isClosed.measurableSet
variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)
variable {n : ℕ} (hn : 0<n)
variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)
include hn hK in
lemma measurable_centerDistance (c : FinProbability Y) :
    Measurable (centerDistance Γ hΓ K n c) := by
  have hc := continuousOn_centerDistance Γ hΓ hn K
    (fun s hs => by obtain ⟨σ,hσ,hsσ,hcard,-⟩ := hK s hs; exact ⟨σ,hσ,hsσ,hcard⟩)
    (fun σ hσ => by
      obtain ⟨τ,hτ,hστ,hcard,hconn⟩ := hK σ hσ.1
      have he : σ=τ := Finset.eq_of_subset_of_card_le hστ (by rw [hcard,hσ.2])
      exact he.symm ▸ hconn) c
  have hm := hc.measurable_piecewise (continuous_const (y := (0 : ℝ))).continuousOn (measurable_realization K)
  convert hm using 1
  funext p
  by_cases hp : p∈(Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space
  · simp only [Set.piecewise, hp,ite_eq_left]
  · simp [Set.piecewise,centerDistance,hp]
def ballWindow (c : FinProbability Y) (J : Set ℝ) : Set (Y →₀ ℝ) :=
  (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space ∩
    centerDistance Γ hΓ K n c ⁻¹' J
include hn hK in
lemma measurable_ballWindow (c : FinProbability Y) (J : Set ℝ) (hJ : MeasurableSet J) :
    MeasurableSet (ballWindow K Γ hΓ (n := n) c J) :=
  (measurable_realization K).inter (hJ.preimage (measurable_centerDistance K Γ hΓ hn hK c))
end
section
variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y] [Countable Y]
  [TopologicalSpace X] [MulAction H X]
variable (K : PreAbstractSimplicialComplex Y)
variable (hact : ∀ (h : H) s,s∈K.faces → s.map (MulAction.toPerm h).toEmbedding∈K.faces)
variable (Γ : SimpleGraph Y) (hΓ : Γ.Connected)
variable (hi : ∀ h : H,@Isometry Y Y (graphMetric Γ hΓ).toPseudoEMetricSpace
  (graphMetric Γ hΓ).toPseudoEMetricSpace (fun y=>h•y))
variable (n : ℕ)
omit [Countable Y] in
include hact hi in
lemma ballWindow_push (c : FinProbability Y) (J : Set ℝ) (h : H) :
    OrbitForms.push h '' ballWindow K Γ hΓ (n := n) c J =
      ballWindow K Γ hΓ (n := n) (h•c) J := by
  ext p
  constructor
  · rintro ⟨q,⟨hq,hqr⟩,rfl⟩
    refine ⟨space_push K hact h q hq,?_⟩
    simpa only [Set.mem_preimage,centerDistance_push K hact Γ hΓ hi n h c q hq] using hqr
  · rintro ⟨hp,hpr⟩
    have hq := space_push K hact h⁻¹ p hp
    refine ⟨OrbitForms.push h⁻¹ p,⟨hq,?_⟩,?_⟩
    · have he := centerDistance_push K hact Γ hΓ hi n h⁻¹ (h•c) p hp
      rw [inv_smul_smul] at he
      simpa only [Set.mem_preimage,he] using hpr
    · simpa only [inv_inv] using OrbitForms.push_inv_push h⁻¹ p
omit [Countable Y] in
lemma original_marked_subset_space
    (Q : OrbitForms.MarkedPair (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K)) (x : X) :
    Q.P.val x⊆(Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space := by
  intro p hp
  exact (Q.T.val x).space_eq ▸ ((Q.P.marked x).subset_space hp)
omit [Countable Y] in
lemma localOriginalArea_ballWindow
    (Q : OrbitForms.MarkedPair (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (σ : SourceTop K n) (j : ℕ) (c : FinProbability Y) (J : Set ℝ) (x : X) :
    localOriginalArea Γ Q σ j (ballWindow K Γ hΓ (n := n) c J) x =
      localOriginalArea Γ Q σ j (centerDistance Γ hΓ K n c ⁻¹' J) x := by
  unfold localOriginalArea
  congr 2
  ext p
  simp only [ballWindow,Set.mem_inter_iff]
  constructor
  · tauto
  · rintro ⟨hp,hi,hr⟩
    exact ⟨hp,hi,original_marked_subset_space K Q x hp,hr⟩
omit [Countable Y] in
include hact hi in
lemma replacement_ballWindow (P Z : OrbitForms.MarkedPair (H := H) (X := X)
    (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (c : FinProbability Y) (B : Set X) (t : ℝ) (x : X) :
    Cuts.replacementSet (P.P.val x) (Z.P.val x)
      (fun i : H×Unit => {v | centerDistance Γ hΓ K n (i.1•c) v<t})
      (fun i : H×Unit => {v | centerDistance Γ hΓ K n (i.1•c) v=t})
      (fun i : H×Unit => (fun x=>i.1⁻¹•x)⁻¹' B) x =
    (Z.P.val x \ ⋃ h : H,activeWindow B (ballWindow K Γ hΓ (n := n) c (Iio t)) h x) ∪
      (P.P.val x ∩ ⋃ h : H,activeWindow B (ballWindow K Γ hΓ (n := n) c {t}) h x) := by
  have hw (J : Set ℝ) (p : Y →₀ ℝ)
      (hp : p∈(Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space) :
      p∈Cuts.activatedUnion (fun i : H×Unit => centerDistance Γ hΓ K n (i.1•c) ⁻¹' J)
        (fun i : H×Unit => (fun x=>i.1⁻¹•x)⁻¹' B) x ↔
      p∈⋃ h : H,activeWindow B (ballWindow K Γ hΓ (n := n) c J) h x := by
    simp only [Cuts.activatedUnion,activeWindow,ballWindow_push K hact Γ hΓ hi n,
      Set.mem_iUnion,Prod.exists,Set.mem_preimage]
    constructor
    · rintro ⟨h,u,hh⟩
      refine ⟨h,?_⟩
      split_ifs at hh ⊢ with hx
      · exact ⟨hp,hh⟩
      · exact hh
    · rintro ⟨h,hh⟩
      refine ⟨h,(),?_⟩
      split_ifs at hh ⊢ with hx
      · exact hh.2
      · exact hh
  ext p
  simp only [Cuts.replacementSet,Set.mem_union,Set.mem_sdiff,Set.mem_inter_iff]
  constructor
  · rintro (⟨hz,hzout⟩ | ⟨hp,hpin⟩)
    · exact Or.inl ⟨hz,fun hh=>hzout ((hw (Iio t) p (original_marked_subset_space K Z x hz)).mpr hh)⟩
    · exact Or.inr ⟨hp,(hw {t} p (original_marked_subset_space K P x hp)).mp hpin⟩
  · rintro (⟨hz,hzout⟩ | ⟨hp,hpin⟩)
    · exact Or.inl ⟨hz,fun hh=>hzout ((hw (Iio t) p (original_marked_subset_space K Z x hz)).mp hh)⟩
    · exact Or.inr ⟨hp,(hw {t} p (original_marked_subset_space K P x hp)).mpr hpin⟩
end
end Sparse.GraphGeometry
namespace Sparse
open Set Finset MeasureTheory
open scoped BassTrace.Sparse Classical ENNReal
variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y]
  [TopologicalSpace X] [MulAction H X]
omit [DecidableEq Y] [TopologicalSpace X] in
lemma activeWindow_mono {U V : Set (Y →₀ ℝ)} (hUV : U⊆V) (B : Set X) (h : H) (x : X) :
    activeWindow B U h x⊆activeWindow B V h x := by
  unfold activeWindow
  split_ifs
  · exact Set.image_mono hUV
  · exact Set.Subset.refl _
end Sparse
namespace Sparse.GraphGeometry
open Set Finset MeasureTheory
open scoped BassTrace.Sparse Classical ENNReal
section
end
section
variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y] [Countable Y]
  [TopologicalSpace X] [CompactSpace X] [MulAction H X]
variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}
variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)
variable (hn : 0<n)
variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)
include hn hK in
lemma ae_local_ball_closed_eq_open
    (Q : OrbitForms.MarkedPair (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K)) (j : ℕ) (c : FinProbability Y) :
    ∀ᵐ t : ℝ,∀ (σ : SourceTop K n) x,
      localOriginalArea Γ Q σ j {v | centerDistance Γ hΓ K n c v≤t} x =
      localOriginalArea Γ Q σ j {v | centerDistance Γ hΓ K n c v<t} x := by
  let : MeasurableSpace (Y →₀ ℝ) := borel (Y →₀ ℝ)
  let : BorelSpace (Y →₀ ℝ) := ⟨rfl⟩
  let : Countable (SourceTop K n) :=
    inferInstanceAs (Countable {s : Finset Y // s∈K.faces ∧ s.card=n+1})
  apply ae_all_iff.mpr
  intro σ
  let f (x : X) := Q.P.val x∩sourceInterior σ.val
  have hf : IsLocallyConstant f := Q.P.localConstancy_inter (simplexVertices σ.val)
    ⟨σ.val,σ.property.1,rfl⟩ _ intrinsicInterior_subset
  let : Finite (Set.range f) := hf.range_finite.to_subtype
  let m := originalAreaMeasure (simplexGraph Γ σ.val σ.property.2) σ.val σ.property.2 j
  have ha (A : Set.range f) : ∀ᵐ t : ℝ,
      m (A.val∩{v | centerDistance Γ hΓ K n c v≤t}) =
      m (A.val∩{v | centerDistance Γ hΓ K n c v<t}) := by
    exact ae_iff.mpr ((countable_ball_area_jumps m A.val
      (measurable_centerDistance K Γ hΓ hn hK c)).measure_zero volume)
  filter_upwards [ae_all_iff.mpr ha] with t ht
  intro x
  simpa only [localOriginalArea_eq_measure,f,m] using ht ⟨f x,Set.mem_range_self x⟩
end
variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y]
  [TopologicalSpace X] [MulAction H X] [MeasurableSpace X]
variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}
variable (Γ : SimpleGraph Y) (hΓ : Γ.Connected)
def ballMass
    (Q : OrbitForms.MarkedPair (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (μ : Measure X) (B : Set X) (j : ℕ) (c : FinProbability Y) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ x in B,∑' σ : SourceTop K n,localOriginalArea Γ Q σ j
    {v | centerDistance Γ hΓ K n c v≤t} x ∂μ
lemma ballMass_mono
    (Q : OrbitForms.MarkedPair (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (μ : Measure X) (B : Set X) (j : ℕ) (c : FinProbability Y) :
    Monotone (ballMass (n := n) Γ hΓ Q μ B j c) := by
  intro s t hst
  unfold ballMass
  apply lintegral_mono
  intro x
  apply ENNReal.tsum_le_tsum
  intro σ
  simp only [localOriginalArea_eq_measure]
  exact measure_mono fun _ hp=>⟨hp.1,hp.2.trans hst⟩
end Sparse.GraphGeometry
end BassTrace
end
end OAI

end
section
namespace OAI
noncomputable section
namespace BassTrace
open Set MeasureTheory
namespace Sparse.GraphGeometry
open Set Finset MeasureTheory
open scoped BassTrace.Sparse Classical ENNReal
section
end
variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y]
  [TopologicalSpace X] [CompactSpace X] [MulAction H X]
  [MeasurableSpace X] [BorelSpace X]
variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}
variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)
variable (hn : 0<n)
variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)
def localTops (c : FinProbability Y) (b : ℝ) : Set (SourceTop K n) :=
  {σ | (sourceInterior σ.val∩{v | centerDistance Γ hΓ K n c v≤b}).Nonempty}
include hn hK in
lemma localTops_finite (c : FinProbability Y) (b : ℝ) (hb : 0≤b) :
    (localTops (K := K) (n := n) Γ hΓ c b).Finite := by
  have hconn (σ : Finset Y) (hs : σ∈K.faces ∧ σ.card=n+1) :
      (Γ.induce (σ : Set Y)).Connected := by
    obtain ⟨τ,hτ,hστ,hcard,hct⟩ := hK σ hs.1
    have he : σ=τ := Finset.eq_of_subset_of_card_le hστ (by rw [hcard,hs.2])
    exact he.symm ▸ hct
  have hfin := finitely_many_meeting_top_simplices Γ hΓ hn
    {σ : Finset Y | σ∈K.faces ∧ σ.card=n+1} (fun σ hs=>⟨hs.2,hconn σ hs⟩) c b hb
  apply (hfin.preimage (show Function.Injective (fun σ : SourceTop K n=>σ.val) from Subtype.val_injective).injOn).subset
  rintro σ ⟨v,hv,hvb⟩
  refine ⟨σ.property,?_⟩
  have hvK := (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).convexHull_subset_space
    (show simplexVertices σ.val∈(Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).faces from
      ⟨σ.val,σ.property.1,rfl⟩) (intrinsicInterior_subset hv)
  let p := pointProbability K ⟨v,hvK⟩
  have hp : p.coeff=v := pointProbability_coeff K ⟨v,hvK⟩
  refine ⟨p,?_,?_⟩
  · rw [hp]
    exact support_of_mem_sourceInterior σ.val hv
  · rw [← centerDistance_apply Γ hΓ K n c p (pointProbability_face K ⟨v,hvK⟩),hp]
    exact hvb
include hn hK in
lemma ballMass_lt_top
    (Q : OrbitForms.MarkedPair (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (μ : Measure X) [IsFiniteMeasure μ] (B : Set X) (j : ℕ)
    (hd : ∀ x t,t∈(Q.T.val x).complex.faces →
      convexHull ℝ (t : Set (Y →₀ ℝ))⊆Q.P.val x → t.card≤j+1)
    (c : FinProbability Y) (b : ℝ) (hb : 0≤b) :
    ballMass (n := n) Γ hΓ Q μ B j c b<∞ := by
  let F := (localTops_finite Γ hΓ hn hK c b hb).toFinset
  have hzero (σ : SourceTop K n) (hσ : σ∉F) (x : X) :
      localOriginalArea Γ Q σ j {v | centerDistance Γ hΓ K n c v≤b} x=0 := by
    rw [localOriginalArea_eq_measure]
    have he : (Q.P.val x∩sourceInterior σ.val)∩{v | centerDistance Γ hΓ K n c v≤b}=∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro v ⟨⟨_,hv⟩,hr⟩
      exact hσ ((localTops_finite Γ hΓ hn hK c b hb).mem_toFinset.mpr ⟨v,hv,hr⟩)
    rw [he,measure_empty]
  have hle (x : X) : (∑' σ : SourceTop K n,
        localOriginalArea Γ Q σ j {v | centerDistance Γ hΓ K n c v≤b} x) ≤
      ∑ σ∈F,originalArea Γ Q σ j x := by
    rw [tsum_eq_sum (s := F) (fun σ hσ=>hzero σ hσ x)]
    apply Finset.sum_le_sum
    intro σ _
    rw [localOriginalArea_eq_measure,originalArea_eq_measure]
    exact measure_mono Set.inter_subset_left
  apply lt_of_le_of_lt (lintegral_mono hle)
  rw [lintegral_finsetSum F (fun σ _=>(originalArea_locallyConstant Γ Q σ j).continuous.measurable)]
  apply ENNReal.sum_lt_top.mpr
  intro σ _
  apply IsLocallyConstant.lintegral_lt_top (originalArea_locallyConstant Γ Q σ j)
  intro x
  apply originalArea_lt_top Γ Q σ _ j x (hd x)
  obtain ⟨τ,hτ,hστ,hcard,hct⟩ := hK σ.val σ.property.1
  have he : σ.val=τ := Finset.eq_of_subset_of_card_le hστ (by rw [hcard,σ.property.2])
  exact he.symm ▸ hct
end Sparse.GraphGeometry
namespace Sparse.GraphCounting
open SimpleGraph
variable {Y : Type*} (Γ : SimpleGraph Y)
lemma extend_tour [DecidableEq Y] {v a b : Y} (p : Γ.Walk v v)
    (ha : a ∈ p.support) (hab : Γ.Adj a b) :
    ∃ q : Γ.Walk v v, q.length = p.length+2 ∧
      q.support.toFinset = insert b p.support.toFinset := by
  let q := (p.takeUntil a ha).append
    ((hab.toWalk.append hab.symm.toWalk).append (p.dropUntil a ha))
  refine ⟨q, ?_, ?_⟩
  · have hl := congrArg SimpleGraph.Walk.length (p.take_spec ha)
    simp only [Walk.length_append] at hl
    simp only [q, Walk.length_append, Adj.length_toWalk]
    omega
  · ext y
    have hm := congrArg (fun r : Γ.Walk v v => y ∈ r.support) (p.take_spec ha)
    simp only [Walk.mem_support_append_iff] at hm
    simp only [q, List.mem_toFinset, Finset.mem_insert, Walk.mem_support_append_iff,
      Adj.support_toWalk, List.mem_cons]
    have haa : a ∈ (p.takeUntil a ha).support := Walk.end_mem_support _
    have hh : y = a → y ∈ (p.takeUntil a ha).support := fun h => h ▸ haa
    tauto
lemma exists_tour_of_card [Fintype Y] [DecidableEq Y] (hΓ : Γ.Connected) (v : Y)
    (k : ℕ) (hk : k < Fintype.card Y) :
    ∃ p : Γ.Walk v v, p.length = 2*k ∧ p.support.toFinset.card = k+1 := by
  induction k with
  | zero => exact ⟨.nil, by simp, by simp⟩
  | succ k ih =>
    obtain ⟨p,hp,hpc⟩ := ih (by omega)
    have hs : p.support.toFinset ≠ Finset.univ := by
      intro he
      have hcc := congrArg Finset.card he
      simp only [Finset.card_univ,hpc] at hcc
      omega
    have hex : ∃ b, b ∉ p.support.toFinset := by
      by_contra! ht
      exact hs (Finset.eq_univ_of_forall ht)
    obtain ⟨b,hb⟩ := hex
    obtain ⟨r⟩ := hΓ.preconnected v b
    obtain ⟨d,_,hd1,hd2⟩ := r.exists_boundary_dart
      (p.support.toFinset : Set Y) (by simp) hb
    obtain ⟨q,hq,hqs⟩ := extend_tour Γ p (by simpa using hd1) d.adj
    refine ⟨q, by omega, ?_⟩
    rw [hqs,Finset.card_insert_of_notMem hd2,hpc]
theorem exists_covering_tour [Fintype Y] [DecidableEq Y] (hΓ : Γ.Connected)
    (v : Y) : ∃ p : Γ.Walk v v,
      p.length = 2*(Fintype.card Y-1) ∧ p.support.toFinset = Finset.univ := by
  have hn : 0 < Fintype.card Y := Fintype.card_pos_iff.mpr ⟨v⟩
  obtain ⟨p,hp,hpc⟩ := exists_tour_of_card Γ hΓ v (Fintype.card Y-1) (by omega)
  refine ⟨p,hp,Finset.eq_of_subset_of_card_le (Finset.subset_univ _) ?_⟩
  simp only [Finset.card_univ,hpc]
  omega
lemma connected_set_tour [DecidableEq Y] (s : Finset Y) (hc : (Γ.induce (s : Set Y)).Connected)
    (v : Y) (hv : v ∈ s) {n : ℕ} (hs : s.card=n+1) :
    ∃ p : Γ.Walk v v, p.length=2*n ∧ p.support.toFinset=s := by
  obtain ⟨p,hp,hps⟩ := exists_covering_tour (Γ.induce (s : Set Y)) hc ⟨v,hv⟩
  let f := (SimpleGraph.Embedding.induce (G := Γ) (s : Set Y)).toHom
  refine ⟨p.map f, ?_, ?_⟩
  · change (p.map f).length = 2*n
    rw [Walk.length_map,hp]
    have hcard : Fintype.card (s : Set Y) = s.card :=
      Fintype.card_of_subtype s (fun _ => Iff.rfl)
    rw [hcard,hs,Nat.add_sub_cancel]
  · change (p.map f).support.toFinset = s
    rw [Walk.support_map]
    ext y
    simp only [List.mem_toFinset,List.mem_map]
    constructor
    · rintro ⟨a,_,rfl⟩
      exact a.property
    · intro hy
      refine ⟨⟨y,hy⟩,?_,rfl⟩
      have hm : (⟨y,hy⟩ : (s : Set Y)) ∈ p.support.toFinset := hps ▸ Finset.mem_univ _
      exact List.mem_toFinset.mp hm
abbrev BasedWalk (v : Y) (n : ℕ) := {p : (b : Y) × Γ.Walk v b // p.2.length = n}
lemma basedWalk_zero_subsingleton (v : Y) : Subsingleton (BasedWalk Γ v 0) := by
  refine ⟨?_⟩
  rintro ⟨⟨b,p⟩,hp⟩ ⟨⟨c,q⟩,hq⟩
  have hb := p.eq_of_length_eq_zero hp
  have hc := q.eq_of_length_eq_zero hq
  subst b
  subst c
  have he : p = .nil := Walk.eq_nil_iff_nil.mpr (Walk.length_eq_zero_iff.mp hp)
  have hf : q = .nil := Walk.eq_nil_iff_nil.mpr (Walk.length_eq_zero_iff.mp hq)
  subst p
  subst q
  rfl
def basedWalkSucc (v : Y) (n : ℕ) :
    BasedWalk Γ v (n+1) → (w : Γ.neighborSet v) × BasedWalk Γ w n
  | ⟨⟨_,.cons h p⟩,hl⟩ => ⟨⟨_,h⟩,⟨⟨_,p⟩,by simpa using hl⟩⟩
def basedWalkCons (v : Y) (n : ℕ) :
    ((w : Γ.neighborSet v) × BasedWalk Γ w n) → BasedWalk Γ v (n+1)
  | ⟨⟨w,h⟩,⟨⟨b,p⟩,hp⟩⟩ => ⟨⟨b,.cons h p⟩,by change p.length+1=n+1; change p.length=n at hp; omega⟩
lemma basedWalkSucc_injective (v : Y) (n : ℕ) :
    Function.Injective (basedWalkSucc Γ v n) := by
  apply Function.LeftInverse.injective (g := basedWalkCons Γ v n)
  rintro ⟨⟨b,p⟩,hp⟩
  cases p with
  | nil => simp at hp
  | cons h p => rfl
lemma basedWalk_finite [Γ.LocallyFinite] (v : Y) (n : ℕ) : Finite (BasedWalk Γ v n) := by
  induction n generalizing v with
  | zero =>
    let := basedWalk_zero_subsingleton Γ v
    infer_instance
  | succ n ih =>
    let : ∀ w : Γ.neighborSet v, Finite (BasedWalk Γ w n) := fun w => ih w
    exact Finite.of_injective _ (basedWalkSucc_injective Γ v n)
lemma basedWalk_card_le [Γ.LocallyFinite] (D : ℕ)
    (hD : ∀ v, Fintype.card (Γ.neighborSet v) ≤ D) (v : Y) (n : ℕ) :
    Nat.card (BasedWalk Γ v n) ≤ D^n := by
  induction n generalizing v with
  | zero =>
    let := basedWalk_zero_subsingleton Γ v
    rw [Nat.card_of_subsingleton (⟨⟨v,.nil⟩,rfl⟩ : BasedWalk Γ v 0)]
    simp
  | succ n ih =>
    let : ∀ w : Γ.neighborSet v, Fintype (BasedWalk Γ w n) :=
      fun w => @Fintype.ofFinite _ (basedWalk_finite Γ w n)
    have hc := Nat.card_le_card_of_injective _ (basedWalkSucc_injective Γ v n)
    rw [Nat.card_eq_fintype_card (α := (w : Γ.neighborSet v) × BasedWalk Γ w n), Fintype.card_sigma] at hc
    calc Nat.card (BasedWalk Γ v (n+1)) ≤ _ := hc
         _ ≤ ∑ _w : Γ.neighborSet v, D^n := Finset.sum_le_sum fun w _ => by
           simpa only [Nat.card_eq_fintype_card] using ih w
         _ = Fintype.card (Γ.neighborSet v)*D^n := by simp
         _ ≤ D*D^n := Nat.mul_le_mul_right _ (hD v)
         _ = D^(n+1) := by rw [pow_succ, Nat.mul_comm]
abbrev ConnectedSets (v : Y) (n : ℕ) :=
  {s : Finset Y // v ∈ s ∧ s.card=n+1 ∧ (Γ.induce (s : Set Y)).Connected}
def connectedSetTour [DecidableEq Y] (v : Y) (n : ℕ) (s : ConnectedSets Γ v n) :
    Γ.Walk v v := (connected_set_tour Γ s.val s.property.2.2 v s.property.1
      s.property.2.1).choose
lemma connectedSetTour_length [DecidableEq Y] (v : Y) (n : ℕ) (s : ConnectedSets Γ v n) :
    (connectedSetTour Γ v n s).length=2*n :=
  (connected_set_tour Γ s.val s.property.2.2 v s.property.1 s.property.2.1).choose_spec.1
lemma connectedSetTour_support [DecidableEq Y] (v : Y) (n : ℕ) (s : ConnectedSets Γ v n) :
    (connectedSetTour Γ v n s).support.toFinset=s.val :=
  (connected_set_tour Γ s.val s.property.2.2 v s.property.1 s.property.2.1).choose_spec.2
def connectedSetEncoding [DecidableEq Y] (v : Y) (n : ℕ) :
    ConnectedSets Γ v n → BasedWalk Γ v (2*n) :=
  fun s => ⟨⟨v,connectedSetTour Γ v n s⟩,connectedSetTour_length Γ v n s⟩
lemma connectedSetEncoding_injective [DecidableEq Y] (v : Y) (n : ℕ) :
    Function.Injective (connectedSetEncoding Γ v n) := by
  intro s t he
  have hs := congrArg (fun w : BasedWalk Γ v (2*n) => w.val.2.support.toFinset) he
  change (connectedSetTour Γ v n s).support.toFinset =
    (connectedSetTour Γ v n t).support.toFinset at hs
  rw [connectedSetTour_support,connectedSetTour_support] at hs
  exact Subtype.ext hs
lemma connectedSets_finite [Γ.LocallyFinite] (v : Y) (n : ℕ) : Finite (ConnectedSets Γ v n) := by
  classical
  let := basedWalk_finite Γ v (2*n)
  exact Finite.of_injective _ (connectedSetEncoding_injective Γ v n)
theorem connectedSets_card_le [Γ.LocallyFinite] (D : ℕ)
    (hD : ∀ v, Fintype.card (Γ.neighborSet v) ≤ D) (v : Y) (n : ℕ) :
    Nat.card (ConnectedSets Γ v n) ≤ D^(2*n) := by
  classical
  let := basedWalk_finite Γ v (2*n)
  exact (Nat.card_le_card_of_injective _ (connectedSetEncoding_injective Γ v n)).trans
    (basedWalk_card_le Γ D hD v (2*n))
end Sparse.GraphCounting
namespace Sparse.GraphGeometry
open Set Finset
variable {Y : Type*} (Γ : SimpleGraph Y) [DecidableEq Y] [Γ.LocallyFinite]
lemma neighborhood_card_bound (D : ℕ) (hD : 2 ≤ D)
    (hdeg : ∀ v, Fintype.card (Γ.neighborSet v) ≤ D) (k : ℕ) (v : Y) :
    (neighborhood Γ k v).card + 1 ≤ D^(k+1) := by
  induction k generalizing v with
  | zero => simpa [neighborhood] using hD
  | succ k ih =>
    have hi : ((Γ.neighborFinset v).biUnion (neighborhood Γ k)).card ≤
        ∑ w ∈ Γ.neighborFinset v, (neighborhood Γ k w).card := Finset.card_biUnion_le
    have hn : (Γ.neighborFinset v).card ≤ D := by
      rw [SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborSet_eq_degree]
      exact hdeg v
    have hp := Finset.card_insert_le v ((Γ.neighborFinset v).biUnion (neighborhood Γ k))
    have hexp : 1 ≤ D^(k+1) := Nat.one_le_pow _ _ (by omega)
    have hraw : (neighborhood Γ (k+1) v).card + 1 ≤
        2 + (Γ.neighborFinset v).card * (D^(k+1)-1) := by
      change (insert v ((Γ.neighborFinset v).biUnion (neighborhood Γ k))).card +1 ≤ _
      have hb : (∑ w ∈ Γ.neighborFinset v, (neighborhood Γ k w).card) ≤
          (Γ.neighborFinset v).card * (D^(k+1)-1) := by
        calc
          _ ≤ ∑ _w ∈ Γ.neighborFinset v, (D^(k+1)-1) :=
            Finset.sum_le_sum fun w _ => by have hh := ih w; omega
          _ = _ := by simp
      omega
    calc
      _ ≤ 2 + (Γ.neighborFinset v).card * (D^(k+1)-1) := hraw
      _ ≤ 2 + D * (D^(k+1)-1) := by gcongr
      _ ≤ D * D^(k+1) := by
        have heq : D^(k+1)-1+1 = D^(k+1) := Nat.sub_add_cancel hexp
        nlinarith
      _ = D^(k+1+1) := (pow_succ' D (k+1)).symm
lemma neighborhood_card_le (D : ℕ) (hD : 2 ≤ D)
    (hdeg : ∀ v, Fintype.card (Γ.neighborSet v) ≤ D) (k : ℕ) (v : Y) :
    (neighborhood Γ k v).card ≤ D^(k+1) := by
  have h := neighborhood_card_bound Γ D hD hdeg k v
  omega
lemma supportNeighborhood_card_le (D : ℕ) (hD : 2 ≤ D)
    (hdeg : ∀ v, Fintype.card (Γ.neighborSet v) ≤ D) (k : ℕ) (A : Finset Y) :
    (A.biUnion (neighborhood Γ k)).card ≤ A.card * D^(k+1) := by
  calc
    _ ≤ ∑ v ∈ A, (neighborhood Γ k v).card := Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ A, D^(k+1) := Finset.sum_le_sum fun v _ =>
      neighborhood_card_le Γ D hD hdeg k v
    _ = _ := by simp
end Sparse.GraphGeometry
namespace Sparse.GraphCounting
open Set Finset
variable {Y : Type*} (Γ : SimpleGraph Y) [DecidableEq Y] [Γ.LocallyFinite]
abbrev ConnectedThrough (B : Finset Y) (n : ℕ) :=
  {s : Finset Y // s.card = n+1 ∧ (Γ.induce (s : Set Y)).Connected ∧
    ∃ v ∈ B, v ∈ s}
noncomputable def throughEncoding (B : Finset Y) (n : ℕ) :
    ConnectedThrough Γ B n → (v : B) × ConnectedSets Γ v n := fun s =>
  ⟨⟨s.property.2.2.choose,s.property.2.2.choose_spec.1⟩,
    ⟨s.val,s.property.2.2.choose_spec.2,s.property.1,s.property.2.1⟩⟩
omit [DecidableEq Y] [Γ.LocallyFinite] in
lemma throughEncoding_injective (B : Finset Y) (n : ℕ) :
    Function.Injective (throughEncoding Γ B n) := by
  intro s t h
  exact Subtype.ext (congrArg (fun p : (v : B) × ConnectedSets Γ v n => p.2.val) h)
omit [DecidableEq Y] in
lemma connectedThrough_finite (B : Finset Y) (n : ℕ) :
    Finite (ConnectedThrough Γ B n) := by
  let : ∀ v : B, Finite (ConnectedSets Γ v n) := fun v => connectedSets_finite Γ v n
  exact Finite.of_injective _ (throughEncoding_injective Γ B n)
omit [DecidableEq Y] in
theorem connectedThrough_card_le (D : ℕ)
    (hdeg : ∀ v, Fintype.card (Γ.neighborSet v) ≤ D) (B : Finset Y) (n : ℕ) :
    Nat.card (ConnectedThrough Γ B n) ≤ B.card * D^(2*n) := by
  let : ∀ v : B, Fintype (ConnectedSets Γ v n) :=
    fun v => @Fintype.ofFinite _ (connectedSets_finite Γ v n)
  have hc := Nat.card_le_card_of_injective _ (throughEncoding_injective Γ B n)
  rw [Nat.card_eq_fintype_card (α := (v : B) × ConnectedSets Γ v n),Fintype.card_sigma] at hc
  calc
    _ ≤ _ := hc
    _ ≤ ∑ _v : B, D^(2*n) := by
      apply Finset.sum_le_sum
      intro v _
      simpa only [Nat.card_eq_fintype_card] using connectedSets_card_le Γ D hdeg v n
    _ = _ := by simp
end Sparse.GraphCounting
namespace Sparse.GraphGeometry
open FinProbability
variable {Y : Type*} (Γ : SimpleGraph Y) [DecidableEq Y] [Γ.LocallyFinite]
lemma meeting_simplex_contact (hΓ : Γ.Connected) {n : ℕ} (hn : 0<n)
    (c p : FinProbability Y) (σ : Finset Y) (hp : p.coeff.support ⊆ σ)
    (s : ℝ) (hs : 0 ≤ s)
    (hball : @rho Y (graphMetric Γ hΓ).toPseudoMetricSpace n c p ≤ s) :
    ∃ v ∈ c.coeff.support.biUnion (neighborhood Γ ⌊s * Real.sqrt (n : ℝ)⌋₊), v ∈ σ := by
  let : MetricSpace Y := graphMetric Γ hΓ
  obtain ⟨a,ha,v,hv,hav⟩ := support_distance_rho hn c p
  have hle : (Γ.dist a v : ℝ) ≤ s * Real.sqrt (n : ℝ) := by
    change (Γ.dist a v : ℝ) ≤ Real.sqrt (n : ℝ) * rho n c p at hav
    calc _ ≤ Real.sqrt (n : ℝ) * rho n c p := hav
         _ ≤ Real.sqrt (n : ℝ) * s := mul_le_mul_of_nonneg_left hball (Real.sqrt_nonneg _)
         _ = _ := mul_comm _ _
  exact ⟨v,Finset.mem_biUnion.mpr ⟨a,ha,dist_le_mem_neighborhood Γ hΓ
    ((Nat.le_floor_iff (mul_nonneg hs (Real.sqrt_nonneg _))).mpr hle)⟩,hp hv⟩
abbrev MeetingTops (hΓ : Γ.Connected) (n : ℕ) (tops : Set (Finset Y))
    (c : FinProbability Y) (s : ℝ) :=
  {σ : Finset Y // σ ∈ tops ∧ ∃ p : FinProbability Y, p.coeff.support ⊆ σ ∧
    @rho Y (graphMetric Γ hΓ).toPseudoMetricSpace n c p ≤ s}
theorem meetingTops_card_le (hΓ : Γ.Connected) (D : ℕ) (hD : 2 ≤ D)
    (hdeg : ∀ v, Fintype.card (Γ.neighborSet v) ≤ D) {n : ℕ} (hn : 0<n)
    (tops : Set (Finset Y))
    (htop : ∀ σ∈tops, σ.card=n+1 ∧ (Γ.induce (σ : Set Y)).Connected)
    (c : FinProbability Y) (s : ℝ) (hs : 0 ≤ s) :
    Nat.card (MeetingTops Γ hΓ n tops c s) ≤
      c.coeff.support.card * D^(⌊s * Real.sqrt (n : ℝ)⌋₊+1) * D^(2*n) := by
  let B := c.coeff.support.biUnion (neighborhood Γ ⌊s * Real.sqrt (n : ℝ)⌋₊)
  let f : MeetingTops Γ hΓ n tops c s → GraphCounting.ConnectedThrough Γ B n := fun σ =>
    ⟨σ.val,(htop σ.val σ.property.1).1,(htop σ.val σ.property.1).2,by
      obtain ⟨p,hp,hball⟩ := σ.property.2
      exact meeting_simplex_contact Γ hΓ hn c p σ.val hp s hs hball⟩
  have hf : Function.Injective f := by
    intro σ τ h
    apply Subtype.ext
    exact congrArg (fun x : GraphCounting.ConnectedThrough Γ B n => x.val) h
  have : Finite (GraphCounting.ConnectedThrough Γ B n) :=
    GraphCounting.connectedThrough_finite Γ B n
  calc
    _ ≤ Nat.card (GraphCounting.ConnectedThrough Γ B n) := Nat.card_le_card_of_injective f hf
    _ ≤ B.card * D^(2*n) := GraphCounting.connectedThrough_card_le Γ D hdeg B n
    _ ≤ _ := Nat.mul_le_mul_right _ (supportNeighborhood_card_le Γ D hD hdeg _ _)
theorem meetingTops_card_le_uniform (hΓ : Γ.Connected) (D : ℕ) (hD : 2 ≤ D)
    (hdeg : ∀ v, Fintype.card (Γ.neighborSet v) ≤ D) {n : ℕ} (hn : 0<n)
    (tops : Set (Finset Y))
    (htop : ∀ σ∈tops, σ.card=n+1 ∧ (Γ.induce (σ : Set Y)).Connected)
    (c : FinProbability Y) (hc : c.coeff.support.card ≤ n+1) (s : ℝ) (hs : 0 ≤ s) :
    Nat.card (MeetingTops Γ hΓ n tops c s) ≤
      (n+1) * D^(⌊s * Real.sqrt (n : ℝ)⌋₊+1) * D^(2*n) := by
  exact (meetingTops_card_le Γ hΓ D hD hdeg hn tops htop c s hs).trans
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hc))
end Sparse.GraphGeometry
end BassTrace
end
end OAI

end
section
namespace OAI
noncomputable section
namespace BassTrace
open Set MeasureTheory
open Finset MeasureTheory intervalIntegral
namespace Sparse
noncomputable def dividedPower (n : ℕ) (t : ℝ) : ℝ :=
  t ^ n / (n.factorial : ℝ)
noncomputable def slicingError (n : ℕ) (t : ℝ) : ℝ :=
  ∑ i ∈ Finset.range n, dividedPower (i + 1) t
lemma continuous_dividedPower (n : ℕ) : Continuous (dividedPower n) := by
  unfold dividedPower
  fun_prop
lemma continuous_slicingError (n : ℕ) : Continuous (slicingError n) := by
  unfold slicingError
  exact continuous_finsetSum _ fun _ _ => continuous_dividedPower _
@[simp] lemma dividedPower_zero (t : ℝ) : dividedPower 0 t = 1 := by
  simp [dividedPower]
@[simp] lemma slicingError_zero (t : ℝ) : slicingError 0 t = 0 := by
  simp [slicingError]
@[simp] lemma dividedPower_one (t : ℝ) : dividedPower 1 t = t := by
  simp [dividedPower]
lemma integral_dividedPower (n : ℕ) (b : ℝ) :
    (∫ t in 0..b, dividedPower n t) = dividedPower (n + 1) b := by
  unfold dividedPower
  rw [intervalIntegral.integral_div, integral_pow, zero_pow (Nat.succ_ne_zero n),
    sub_zero, div_div, Nat.factorial_succ]
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
lemma integral_slicingError (n : ℕ) (b : ℝ) :
    (∫ t in 0..b, slicingError n t) + b = slicingError (n + 1) b := by
  unfold slicingError
  rw [intervalIntegral.integral_finsetSum (fun i _ =>
    (continuous_dividedPower (i + 1)).intervalIntegrable 0 b)]
  simp only [integral_dividedPower]
  rw [Finset.sum_range_succ']
  simp only [zero_add, dividedPower_one]
lemma integral_slicing_lower (n : ℕ) (b c ε : ℝ) :
    (∫ t in 0..b, c * dividedPower n t - ε * slicingError n t) - ε * b =
      c * dividedPower (n + 1) b - ε * slicingError (n + 1) b := by
  have hc : IntervalIntegrable (fun t => c * dividedPower n t) volume 0 b :=
    (continuous_const.mul (continuous_dividedPower n)).intervalIntegrable 0 b
  have he : IntervalIntegrable (fun t => ε * slicingError n t) volume 0 b :=
    (continuous_const.mul (continuous_slicingError n)).intervalIntegrable 0 b
  rw [intervalIntegral.integral_sub hc he,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_dividedPower]
  have h := integral_slicingError n b
  rw [← h]
  ring
theorem iterated_slicing_lower_bound
    (M : ℕ → ℝ → ℝ) (n : ℕ) (L ε : ℝ)
    (hmono : ∀ k, Monotone (M k))
    (hstep : ∀ k < n, ∀ b ∈ Set.Icc 0 L,
      (∫ t in 0..b, M k t) - ε * b ≤ M (k + 1) b) :
    ∀ k ≤ n, ∀ b ∈ Set.Icc 0 L,
      M 0 0 * dividedPower k b - ε * slicingError k b ≤ M k b := by
  intro k
  induction k with
  | zero =>
      intro _ b hb
      simpa using hmono 0 hb.1
  | succ k ih =>
      intro hk b hb
      have hk' : k ≤ n := Nat.le_trans (Nat.le_succ k) hk
      have hm :
          (∫ t in 0..b, M 0 0 * dividedPower k t - ε * slicingError k t) ≤
            ∫ t in 0..b, M k t := by
        apply intervalIntegral.integral_mono_on hb.1
          (((continuous_const.mul (continuous_dividedPower k)).sub
            (continuous_const.mul (continuous_slicingError k))).intervalIntegrable 0 b)
          (hmono k).intervalIntegrable
        intro t ht
        exact ih hk' t ⟨ht.1, ht.2.trans hb.2⟩
      have hs := hstep k (Nat.lt_of_succ_le hk) b hb
      rw [← integral_slicing_lower k b (M 0 0) ε]
      linarith
theorem absorb_nonempty_probability
    (A V μ M ε E : ℝ) (hVA : V < A) (hV : 0 ≤ V)
    (hμM : μ ≤ M) (hbound : A * M ≤ V * μ + ε * E) :
    M ≤ E / (A - V) * ε := by
  have hpos : 0 < A - V := sub_pos.mpr hVA
  have hmul : V * μ ≤ V * M := mul_le_mul_of_nonneg_left hμM hV
  have h : (A - V) * M ≤ ε * E := by nlinarith
  have h' : M ≤ (ε * E) / (A - V) := (le_div_iff₀ hpos).2 (by nlinarith)
  convert h' using 1
  ring
def volumeThreshold (D : ℕ) : ℕ := (4 * D ^ 3 + D + 3) ^ 2
lemma square_succ_le_two_pow {t : ℕ} (ht : 6 ≤ t) : (t + 1) ^ 2 ≤ 2 ^ t := by
  induction t, ht using Nat.le_induction with
  | base => norm_num
  | succ t ht ih =>
      rw [pow_succ (2 : ℕ) t]
      have hsq : (t + 1 + 1) ^ 2 ≤ 2 * (t + 1) ^ 2 := by nlinarith
      omega
lemma real_sqrt_lt_nat_sqrt_succ (n : ℕ) :
    Real.sqrt (n : ℝ) < (Nat.sqrt n : ℝ) + 1 := by
  have hs := Real.sq_sqrt (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hn : (n : ℝ) < ((Nat.sqrt n : ℝ) + 1) ^ 2 := by
    exact_mod_cast Nat.lt_succ_sqrt' n
  have ht : (0 : ℝ) ≤ Nat.sqrt n := Nat.cast_nonneg _
  nlinarith [Real.sqrt_nonneg (n : ℝ)]
lemma floor_radius_sqrt_bound (D n : ℕ) :
    ⌊(4 * (D : ℝ) ^ 2) * Real.sqrt (n : ℝ)⌋₊ ≤
      4 * D ^ 2 * (Nat.sqrt n + 1) := by
  have hnonneg : 0 ≤ (4 * (D : ℝ) ^ 2) * Real.sqrt (n : ℝ) := by positivity
  have hfloor := Nat.floor_le hnonneg
  have hroot := (real_sqrt_lt_nat_sqrt_succ n).le
  have hmul := mul_le_mul_of_nonneg_left hroot (by positivity : (0 : ℝ) ≤ 4 * (D : ℝ) ^ 2)
  have h : (⌊(4 * (D : ℝ) ^ 2) * Real.sqrt (n : ℝ)⌋₊ : ℝ) ≤
      4 * (D : ℝ) ^ 2 * ((Nat.sqrt n : ℝ) + 1) := hfloor.trans hmul
  exact_mod_cast h
theorem exponential_volume_margin (D n : ℕ) (hD : 2 ≤ D)
    (hn : volumeThreshold D ≤ n) :
    (n + 1) * D ^ (⌊(4 * (D : ℝ) ^ 2) * Real.sqrt (n : ℝ)⌋₊ + 1) < 2 ^ n := by
  let t := Nat.sqrt n
  have ht : 4 * D ^ 3 + D + 3 ≤ t := Nat.le_sqrt'.mpr hn
  have htp : 6 ≤ t := by
    have hcube : 1 ≤ D ^ 3 := Nat.one_le_pow 3 D (by omega)
    omega
  have hnt : n + 1 ≤ 2 ^ t :=
    (Nat.succ_le_succ_sqrt' n).trans (square_succ_le_two_pow htp)
  have hfloor := floor_radius_sqrt_bound D n
  have hbase : D ≤ 2 ^ D := (Nat.lt_two_pow_self (n := D)).le
  have hexp : t + D * (4 * D ^ 2 * (t + 1) + 1) < t ^ 2 := by
    have h1 : (4 * D ^ 3 + D + 3) * t ≤ t * t := Nat.mul_le_mul_right t ht
    have h2 : 4 * D ^ 3 + D + 3 ≤ 3 * t := by omega
    nlinarith
  calc
    (n + 1) * D ^ (⌊(4 * (D : ℝ) ^ 2) * Real.sqrt (n : ℝ)⌋₊ + 1)
        ≤ 2 ^ t * (2 ^ D) ^ (4 * D ^ 2 * (t + 1) + 1) := by
          apply Nat.mul_le_mul hnt
          exact (Nat.pow_le_pow_left hbase _).trans
            (Nat.pow_le_pow_right (by positivity) (Nat.add_le_add_right hfloor 1))
    _ = 2 ^ (t + D * (4 * D ^ 2 * (t + 1) + 1)) := by
      rw [← pow_mul, ← pow_add]
    _ < 2 ^ (t ^ 2) := Nat.pow_lt_pow_right (by omega) hexp
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) (Nat.sqrt_le' n)
theorem strict_volume_margin (D n : ℕ) (hD : 2 ≤ D)
    (hn : volumeThreshold D ≤ n) :
    ((n + 1 : ℕ) : ℝ) * (D : ℝ) ^
       (⌊(4 * (D : ℝ) ^ 2) * Real.sqrt (n : ℝ)⌋₊ + 1) *
       (D : ℝ) ^ (2 * n) / (n.factorial : ℝ) <
      (2 * (D : ℝ) ^ 2) ^ n / (n.factorial : ℝ) := by
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  apply (div_lt_div_iff_of_pos_right hf).2
  have h := exponential_volume_margin D n hD hn
  have hc : ((n + 1 : ℕ) : ℝ) * (D : ℝ) ^
      (⌊(4 * (D : ℝ) ^ 2) * Real.sqrt (n : ℝ)⌋₊ + 1) < (2 : ℝ) ^ n := by
    exact_mod_cast h
  have hDp : (0 : ℝ) < (D : ℝ) ^ (2 * n) := by positivity
  have hm := mul_lt_mul_of_pos_right hc hDp
  simpa only [mul_pow, pow_mul] using hm
end Sparse
namespace Sparse.GraphGeometry
open Set Finset MeasureTheory
open scoped BassTrace.Sparse Classical ENNReal
variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y]
  [TopologicalSpace X] [MulAction H X] [MeasurableSpace X]
variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}
variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)
variable (hn : 0<n)
variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)
omit [DecidableEq Y] [Γ.LocallyFinite] in
include hK in
lemma sourceTop_connected (σ : SourceTop K n) : (Γ.induce (σ.val : Set Y)).Connected := by
  obtain ⟨τ,_,hστ,hcard,hct⟩ := hK σ.val σ.property.1
  have he : σ.val=τ := Finset.eq_of_subset_of_card_le hστ (by rw [hcard,σ.property.2])
  exact he.symm ▸ hct
omit [MeasurableSpace X] [Γ.LocallyFinite] in
include hK in
lemma localOriginalArea_top_le
    (Q : OrbitForms.MarkedPair (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (σ : SourceTop K n) (W : Set (Y →₀ ℝ)) (x : X) :
    localOriginalArea Γ Q σ n W x ≤ ENNReal.ofReal (1/(n.factorial : ℝ)) := by
  rw [←simplexArea_top_simplex (simplexGraph Γ σ.val σ.property.2)
    (simplexGraph_connected Γ σ.val σ.property.2 (sourceTop_connected Γ hK σ))]
  apply simplexArea_mono
  rintro _ ⟨v,⟨_,hv,_⟩,rfl⟩
  exact simplexCoordinates_full _ _ (intrinsicInterior_subset hv)
include hn hK in
lemma localTops_card_le (D : ℕ) (hD : 2≤D)
    (hdeg : ∀ v,Fintype.card (Γ.neighborSet v)≤D)
    (c : FinProbability Y) (hc : c.coeff.support.card≤n+1) (b : ℝ) (hb : 0≤b) :
    Nat.card (localTops (K := K) (n := n) Γ hΓ c b) ≤
      (n+1)*D^(⌊b*Real.sqrt (n : ℝ)⌋₊+1)*D^(2*n) := by
  let tops : Set (Finset Y) := {s | s∈K.faces ∧ s.card=n+1}
  let f : localTops (K := K) (n := n) Γ hΓ c b → MeetingTops Γ hΓ n tops c b := fun σ=>by
    refine ⟨σ.val.val,σ.val.property,?_⟩
    obtain ⟨v,hv,hvb⟩ := σ.property
    have hvK := (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).convexHull_subset_space
      (show simplexVertices σ.val.val∈(Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).faces from
        ⟨σ.val.val,σ.val.property.1,rfl⟩) (intrinsicInterior_subset hv)
    let p := pointProbability K ⟨v,hvK⟩
    have hp : p.coeff=v := pointProbability_coeff K ⟨v,hvK⟩
    refine ⟨p,?_,?_⟩
    · rw [hp]; exact support_of_mem_sourceInterior _ hv
    · rw [←centerDistance_apply Γ hΓ K n c p (pointProbability_face K ⟨v,hvK⟩),hp]
      exact hvb
  have hf : Function.Injective f := by
    intro σ τ h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun s : MeetingTops Γ hΓ n tops c b=>s.val) h
  have hfin := finitely_many_meeting_top_simplices Γ hΓ hn tops
    (fun s hs=>⟨hs.2,sourceTop_connected Γ hK ⟨s,hs⟩⟩) c b hb
  let : Finite (MeetingTops Γ hΓ n tops c b) := hfin.to_subtype
  exact (Nat.card_le_card_of_injective f hf).trans
    (meetingTops_card_le_uniform Γ hΓ D hD hdeg hn tops
      (fun s hs=>⟨hs.2,sourceTop_connected Γ hK ⟨s,hs⟩⟩) c hc b hb)
include hn hK in
lemma ballMass_top_bound
    (Q : OrbitForms.MarkedPair (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (μ : Measure X) (B : Set X) (c : FinProbability Y)
    (hc : c.coeff.support.card≤n+1) (b : ℝ) (hb : 0≤b)
    (D : ℕ) (hD : 2≤D) (hdeg : ∀ v,Fintype.card (Γ.neighborSet v)≤D) :
    ballMass (n := n) Γ hΓ Q μ B n c b ≤
      ((n+1)*D^(⌊b*Real.sqrt (n : ℝ)⌋₊+1)*D^(2*n) : ℕ) *
        ENNReal.ofReal (1/(n.factorial : ℝ)) * μ B := by
  let F := (localTops_finite Γ hΓ hn hK c b hb).toFinset
  have hzero (σ : SourceTop K n) (hσ : σ∉F) (x : X) :
      localOriginalArea Γ Q σ n {v | centerDistance Γ hΓ K n c v≤b} x=0 := by
    rw [localOriginalArea_eq_measure]
    have he : (Q.P.val x∩sourceInterior σ.val)∩{v | centerDistance Γ hΓ K n c v≤b}=∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro v ⟨⟨_,hv⟩,hr⟩
      exact hσ ((localTops_finite Γ hΓ hn hK c b hb).mem_toFinset.mpr ⟨v,hv,hr⟩)
    rw [he,measure_empty]
  have hle (x : X) : (∑' σ : SourceTop K n,
        localOriginalArea Γ Q σ n {v | centerDistance Γ hΓ K n c v≤b} x) ≤
      (F.card : ℝ≥0∞)*ENNReal.ofReal (1/(n.factorial : ℝ)) := by
    rw [tsum_eq_sum (s := F) (fun σ hσ=>hzero σ hσ x)]
    simpa using Finset.sum_le_sum (s := F) (fun σ _=>localOriginalArea_top_le Γ hK Q σ _ x)
  have hcard : F.card≤(n+1)*D^(⌊b*Real.sqrt (n : ℝ)⌋₊+1)*D^(2*n) := by
    have h := localTops_card_le Γ hΓ hn hK D hD hdeg c hc b hb
    simpa only [Nat.card_coe_set_eq,Set.ncard_eq_toFinset_card _ (localTops_finite Γ hΓ hn hK c b hb),F] using h
  calc
    _ ≤ ∫⁻ _x in B, (F.card : ℝ≥0∞)*ENNReal.ofReal (1/(n.factorial : ℝ)) ∂μ := lintegral_mono hle
    _ = (F.card : ℝ≥0∞)*ENNReal.ofReal (1/(n.factorial : ℝ))*μ B := by simp
    _ ≤ _ := by gcongr
end Sparse.GraphGeometry
namespace Sparse
open Set MeasureTheory
open scoped ENNReal
lemma real_integral_of_mass_bound (F : ℝ → ℝ≥0∞) (hmono : Monotone F)
    (hfin : ∀ t,F t<∞) (r b ε : ℝ) (hrb : r≤b) (hε : 0≤ε)
    (C : ℝ≥0∞) (hC : C<∞)
    (h : (∫⁻ t in Ioo r b,F t)≤C+ENNReal.ofReal ε*ENNReal.ofReal (b-r)) :
    (∫ t in r..b,(F t).toReal)≤C.toReal+ε*(b-r) := by
  rw [intervalIntegral.integral_of_le hrb,integral_Ioc_eq_integral_Ioo,
    integral_toReal hmono.measurable.aemeasurable (Filter.Eventually.of_forall hfin)]
  have ht : C+ENNReal.ofReal ε*ENNReal.ofReal (b-r)≠∞ := by finiteness
  have hh := ENNReal.toReal_mono ht h
  rw [ENNReal.toReal_add hC.ne (by finiteness),ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hε,ENNReal.toReal_ofReal (sub_nonneg.mpr hrb)] at hh
  exact hh
theorem iterated_mass_bound (M : ℕ → ℝ → ℝ≥0∞) (n : ℕ) (r R ε : ℝ)
    (hrR : r≤R) (hε : 0≤ε) (hmono : ∀ k,Monotone (M k))
    (hfin : ∀ k t,M k t<∞)
    (hstep : ∀ k<n,∀ b∈Icc r R,
      (∫⁻ t in Ioo r b,M k t)≤M (k+1) b+ENNReal.ofReal ε*ENNReal.ofReal (b-r)) :
    (M 0 r).toReal*dividedPower n (R-r)-ε*slicingError n (R-r)≤(M n R).toReal := by
  let F : ℕ → ℝ → ℝ := fun k t=>(M k (r+t)).toReal
  have hFm k : Monotone (F k) := fun a b hab=>
    ENNReal.toReal_mono (hfin k _).ne (hmono k (add_le_add le_rfl hab))
  have hFs k (hk : k<n) b (hb : b∈Icc 0 (R-r)) :
      (∫ t in 0..b,F k t)-ε*b≤F (k+1) b := by
    have hle := real_integral_of_mass_bound (M k) (hmono k) (hfin k) r (r+b) ε
      (by linarith [hb.1]) hε (M (k+1) (r+b)) (hfin _ _) (hstep k hk _ ⟨by linarith [hb.1],by linarith [hb.2]⟩)
    have he : (∫ t in 0..b,F k t) = ∫ t in r..r+b,(M k t).toReal := by
      simpa only [F,add_zero] using intervalIntegral.integral_comp_add_left (a := 0) (b := b) (fun t=>(M k t).toReal) r
    rw [he]
    dsimp [F]
    linarith
  have hi := iterated_slicing_lower_bound F n (R-r) ε hFm hFs n le_rfl (R-r)
    ⟨sub_nonneg.mpr hrR,le_rfl⟩
  simpa only [F,add_zero,add_sub_cancel] using hi
end Sparse
namespace Sparse.GraphGeometry
open Set Finset MeasureTheory
open scoped BassTrace.Sparse Classical ENNReal
variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y] [Countable Y]
  [Countable H] [IsCancelSMul H Y]
  [TopologicalSpace X] [CompactSpace X] [MulAction H X] [ContinuousConstSMul H X]
  [MeasurableSpace X] [BorelSpace X]
variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}
variable [hact : Fact (∀ (h : H) s,s∈K.faces → s.map (MulAction.toPerm h).toEmbedding∈K.faces)]
local instance : MulAction H (SourceTop K n) := sourceTopAction K n hact.out
local instance : Countable (SourceTop K n) := inferInstanceAs (Countable {s : Finset Y // s∈K.faces ∧ s.card=n+1})
local instance (σ : SourceTop K n) : Finite (MulAction.stabilizer H σ) :=
  finite_sourceTop_stabilizer K n hact.out σ
variable [Finite (MulAction.orbitRel.Quotient H (SourceTop K n))]
variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)
variable (hΓaut : ∀ (h : H) u v,Γ.Adj (h•u) (h•v) ↔ Γ.Adj u v)
variable (hi : ∀ h : H,@Isometry Y Y (graphMetric Γ hΓ).toPseudoEMetricSpace
  (graphMetric Γ hΓ).toPseudoEMetricSpace (fun y=>h•y))
variable (hn : 0<n)
variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)
def ballVolumeBound (D n : ℕ) (R : ℝ) : ℝ :=
  ((n+1)*D^(⌊R*Real.sqrt (n : ℝ)⌋₊+1)*D^(2*n) : ℕ) / (n.factorial : ℝ)
end Sparse.GraphGeometry
end BassTrace
end
end OAI

end
section
namespace OAI
noncomputable section
namespace BassTrace
open Set MeasureTheory
open Finset MeasureTheory intervalIntegral
namespace Sparse.GraphGeometry
open Set Finset MeasureTheory
open scoped BassTrace.Sparse Classical ENNReal
section
variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y]
  [TopologicalSpace X] [MulAction H X]
variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}
variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)
variable (hn : 0<n)
variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)
def ballIntegrand
    (Q : OrbitForms.MarkedPair (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (j : ℕ) (c : FinProbability Y) (t : ℝ) (x : X) : ℝ≥0∞ :=
  ∑' σ : SourceTop K n,localOriginalArea Γ Q σ j
    {v | centerDistance Γ hΓ K n c v≤t} x
omit [Γ.LocallyFinite] in
lemma localOriginalArea_eq_zero_of_not_mem_localTops
    (Q : OrbitForms.MarkedPair (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (j : ℕ) (c : FinProbability Y) (b : ℝ) (σ : SourceTop K n)
    (hσ : σ∉localTops (K := K) (n := n) Γ hΓ c b) (x : X) :
    localOriginalArea Γ Q σ j {v | centerDistance Γ hΓ K n c v≤b} x=0 := by
  rw [localOriginalArea_eq_measure]
  have he : (Q.P.val x∩sourceInterior σ.val)∩{v | centerDistance Γ hΓ K n c v≤b}=∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro v ⟨⟨_,hv⟩,hr⟩
    exact hσ ⟨v,hv,hr⟩
  rw [he,measure_empty]
include hn hK in
lemma ballIntegrand_locallyConstant
    (Q : OrbitForms.MarkedPair (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (j : ℕ) (c : FinProbability Y) (b : ℝ) (hb : 0≤b) :
    IsLocallyConstant (ballIntegrand (n := n) Γ hΓ Q j c b) := by
  let F := (localTops_finite Γ hΓ hn hK c b hb).toFinset
  have he (x : X) : ballIntegrand (n := n) Γ hΓ Q j c b x =
      ∑ σ∈F,localOriginalArea Γ Q σ j {v | centerDistance Γ hΓ K n c v≤b} x := by
    apply tsum_eq_sum
    intro σ hσ
    exact localOriginalArea_eq_zero_of_not_mem_localTops Γ hΓ Q j c b σ
      (fun h=>hσ ((localTops_finite Γ hΓ hn hK c b hb).mem_toFinset.mpr h)) x
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro x
  have hall : ∀ᶠ y in nhds x,∀ σ∈F,
      localOriginalArea Γ Q σ j {v | centerDistance Γ hΓ K n c v≤b} y=
      localOriginalArea Γ Q σ j {v | centerDistance Γ hΓ K n c v≤b} x :=
    F.eventually_all.mpr fun σ _=>(localOriginalArea_locallyConstant Γ Q σ j _).eventually_eq x
  filter_upwards [hall] with y hy
  rw [he,he]
  exact Finset.sum_congr rfl hy
omit [Γ.LocallyFinite] in
include hK in
lemma localOriginalArea_zero_eq_count
    (Q : OrbitForms.MarkedPair (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (σ : SourceTop K n) (W : Set (Y →₀ ℝ)) (x : X) :
    localOriginalArea Γ Q σ 0 W x = Measure.count
      (simplexCoordinates σ.val σ.property.2 '' (Q.P.val x∩(sourceInterior σ.val∩W))) := by
  apply simplexArea_zero _ (simplexGraph_connected Γ σ.val σ.property.2 (sourceTop_connected Γ hK σ))
  rintro _ ⟨v,⟨_,hv,_⟩,rfl⟩
  exact simplexCoordinates_sum _ _ (intrinsicInterior_subset hv)
omit [Γ.LocallyFinite] in
include hK in
lemma one_le_ballIntegrand_of_ne_zero
    (Q : OrbitForms.MarkedPair (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (c : FinProbability Y) (b : ℝ) (x : X)
    (hx : ballIntegrand (n := n) Γ hΓ Q 0 c b x≠0) :
    1≤ballIntegrand (n := n) Γ hΓ Q 0 c b x := by
  have hex : ∃ σ : SourceTop K n,
      localOriginalArea Γ Q σ 0 {v | centerDistance Γ hΓ K n c v≤b} x≠0 := by
    by_contra! h
    exact hx (by simp only [ballIntegrand,h,tsum_zero])
  obtain ⟨σ,hσ⟩ := hex
  rw [localOriginalArea_zero_eq_count Γ hK] at hσ
  obtain ⟨v,hv⟩ := Measure.count_ne_zero_iff.mp hσ
  calc
    _ = Measure.count ({v} : Set (Fin (n+1) → ℝ)) := (Measure.count_singleton v).symm
    _ ≤ _ := measure_mono (singleton_subset_iff.mpr hv)
    _ = localOriginalArea Γ Q σ 0 {v | centerDistance Γ hΓ K n c v≤b} x :=
      (localOriginalArea_zero_eq_count Γ hK Q σ _ x).symm
    _ ≤ _ := ENNReal.le_tsum (f := fun τ : SourceTop K n =>
      localOriginalArea Γ Q τ 0 {v | centerDistance Γ hΓ K n c v≤b} x) σ
end
end Sparse.GraphGeometry
namespace Sparse
section
open Set TopologicalSpace
open scoped Pointwise Function
variable {H X : Type*} [Group H] [TopologicalSpace X] [MulAction H X]
lemma exists_clopen_disjoint_translate
    [T2Space X] [CompactSpace X] [TotallyDisconnectedSpace X]
    [ContinuousConstSMul H X] [IsCancelSMul H X]
    (x : X) (g : H) (hg : g ≠ 1) :
    ∃ U : Set X, IsClopen U ∧ x ∈ U ∧ Disjoint U (g • U) := by
  have hne : x ≠ g • x := by
    intro h
    exact hg (IsCancelSMul.eq_one_of_smul h.symm)
  obtain ⟨V, hV, hx, hgx⟩ := exists_isClopen_of_totally_separated hne
  refine ⟨V ∩ (fun y : X => g • y) ⁻¹' Vᶜ,
    hV.inter (hV.compl.preimage (continuous_const_smul g)), ⟨hx, hgx⟩, ?_⟩
  apply Set.disjoint_left.mpr
  intro y hy hgy
  obtain ⟨z, hz, rfl⟩ := hgy
  exact hz.2 hy.1
lemma exists_clopen_disjoint_translates
    [T2Space X] [CompactSpace X] [TotallyDisconnectedSpace X]
    [ContinuousConstSMul H X] [IsCancelSMul H X]
    (x : X) (s : Finset H) (hs : 1 ∉ s) :
    ∃ U : Set X, IsClopen U ∧ x ∈ U ∧ ∀ g ∈ s, Disjoint U (g • U) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨Set.univ, isClopen_univ, Set.mem_univ _, by simp⟩
  | @insert g s hgs ih =>
      have hgone : g ≠ 1 := by
        intro hg
        exact hs (by simp [hg])
      obtain ⟨U, hU, hxU, hUD⟩ := ih (fun h => hs (Finset.mem_insert_of_mem h))
      obtain ⟨V, hV, hxV, hVD⟩ := exists_clopen_disjoint_translate x g hgone
      refine ⟨U ∩ V, hU.inter hV, ⟨hxU, hxV⟩, ?_⟩
      intro k hk
      rcases Finset.mem_insert.mp hk with rfl | hk
      · exact hVD.mono Set.inter_subset_right (Set.smul_set_mono Set.inter_subset_right)
      · exact (hUD k hk).mono Set.inter_subset_left
          (Set.smul_set_mono Set.inter_subset_left)
theorem exists_separated_clopen_partition
    [T2Space X] [CompactSpace X] [TotallyDisconnectedSpace X]
    [ContinuousConstSMul H X] [IsCancelSMul H X]
    (s : Finset H) (hs : 1 ∉ s) :
    ∃ (n : ℕ) (W : Fin n → Clopens X),
      (Set.univ : Set X) ⊆ ⋃ j, (W j : Set X) ∧
      Pairwise (Disjoint on W) ∧
      ∀ j g, g ∈ s → Disjoint (W j : Set X) (g • (W j : Set X)) := by
  classical
  choose U hU hx hD using fun x : X => exists_clopen_disjoint_translates x s hs
  let V : X → Opens X := fun x => ⟨U x, (hU x).isOpen⟩
  have hcover : IsOpenCover V := by
    apply IsOpenCover.of_sets
    apply Set.eq_univ_of_forall
    intro x
    exact Set.mem_iUnion.mpr ⟨x, hx x⟩
  obtain ⟨n, W, hWsub, hWcover, hWdisj⟩ :=
    hcover.exists_finite_nonempty_disjoint_clopen_cover
  refine ⟨n, W, hWcover, hWdisj, ?_⟩
  intro j g hg
  obtain ⟨x, hjx⟩ := (hWsub j).2
  exact (hD x g hg).mono hjx (Set.smul_set_mono hjx)
end
open Set Finset
open scoped Pointwise Classical
variable {H Y : Type*} [Group H] [MulAction H Y] [IsCancelSMul H Y]
lemma finite_push_collisions (W : Finset Y) (U : Set (Y →₀ ℝ))
    (hU : ∀ p∈U,p≠0 ∧ p.support⊆W) :
    {h : H | ¬Disjoint U (OrbitForms.push h '' U)}.Finite := by
  have hf : (⋃ w∈(W : Set Y),{h : H | h•w∈W}).Finite := by
    apply W.finite_toSet.biUnion
    intro w _
    exact Set.Finite.preimage (fun h _ k _ he=>IsCancelSMul.right_cancel h k w he)
      W.finite_toSet
  apply hf.subset
  intro h hh
  obtain ⟨p,hp,q,hq,he⟩ := Set.not_disjoint_iff.mp hh
  obtain ⟨w,hw⟩ := Finsupp.support_nonempty_iff.mpr (hU q hq).1
  apply Set.mem_iUnion₂.mpr
  refine ⟨w,(hU q hq).2 hw,?_⟩
  apply (hU p hp).2
  rw [Finsupp.mem_support_iff,← he,OrbitForms.push_apply,inv_smul_smul]
  exact Finsupp.mem_support_iff.mp hw
variable {X : Type*} [TopologicalSpace X] [MulAction H X]
omit [IsCancelSMul H Y] [TopologicalSpace X] in
lemma activeWindows_disjoint (A : Set X) (U : Set (Y →₀ ℝ))
    (hA : ∀ g : H,g≠1 → ¬Disjoint U (OrbitForms.push g '' U) →
      Disjoint A (g•A)) :
    ∀ x,Pairwise (fun h k : H=>Disjoint
      (activeWindow A U h x) (activeWindow A U k x)) := by
  intro x h k hne
  by_cases hh : h⁻¹•x∈A
  · by_cases hk : k⁻¹•x∈A
    · simp only [activeWindow,hh,hk,ite_eq_left]
      apply Set.disjoint_left.mpr
      rintro p ⟨u,hu,rfl⟩ ⟨v,hv,he⟩
      have hd : h⁻¹*k≠1 := fun he=>hne (inv_mul_eq_one.mp he)
      have hc : ¬Disjoint U (OrbitForms.push (h⁻¹*k) '' U) := by
        apply Set.not_disjoint_iff.mpr
        refine ⟨u,hu,v,hv,?_⟩
        rw [OrbitForms.push_mul,he,OrbitForms.push_inv_push]
      have ha := Set.disjoint_left.mp (hA _ hd hc) hh
      apply ha
      refine ⟨k⁻¹•x,hk,?_⟩
      simp [mul_smul]
    · simp [activeWindow,hk]
  · simp [activeWindow,hh]
lemma exists_disjoint_active_partition
    [T2Space X] [CompactSpace X] [TotallyDisconnectedSpace X]
    [ContinuousConstSMul H X] [IsCancelSMul H X]
    (W : Finset Y) (U : Set (Y →₀ ℝ))
    (hU : ∀ p∈U,p≠0 ∧ p.support⊆W) :
    ∃ (m : ℕ) (A : Fin m → TopologicalSpace.Clopens X),
      (univ : Set X)⊆⋃ i,(A i : Set X) ∧
      Pairwise (fun i j=>Disjoint (A i : Set X) (A j : Set X)) ∧
      ∀ i x,Pairwise (fun h k : H=>Disjoint
        (activeWindow (A i : Set X) U h x) (activeWindow (A i : Set X) U k x)) := by
  let S := (show ({h : H | ¬Disjoint U (OrbitForms.push h '' U)} \ {1}).Finite from
    (finite_push_collisions W U hU).sdiff).toFinset
  have hS : 1∉S := by simp [S]
  obtain ⟨m,A,hcover,hdisj,hsep⟩ := exists_separated_clopen_partition (X := X) S hS
  refine ⟨m,A,hcover,?_,?_⟩
  · exact fun i j hij=>TopologicalSpace.Clopens.coe_disjoint.mpr (hdisj hij)
  · intro i
    apply activeWindows_disjoint
    intro g hg hc
    exact hsep i g (by simp [S,hg,hc])
end Sparse
namespace Sparse.GraphGeometry
section
open Set Finset MeasureTheory
open scoped BassTrace.Sparse Classical ENNReal
section
variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y]
  [IsCancelSMul H Y]
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [TotallyDisconnectedSpace X]
  [MulAction H X] [ContinuousConstSMul H X] [IsCancelSMul H X]
variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}
variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)
variable (hn : 0<n)
variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)
include hn hK in
lemma exists_disjoint_ball_partition (c : FinProbability Y) {R : ℝ} (hR : 0≤R) :
    ∃ (m : ℕ) (A : Fin m → TopologicalSpace.Clopens X),
      (univ : Set X)⊆⋃ i,(A i : Set X) ∧
      Pairwise (fun i j=>Disjoint (A i : Set X) (A j : Set X)) ∧
      ∀ i x,Pairwise (fun h k : H=>Disjoint
        (activeWindow (A i : Set X) (ballWindow K Γ hΓ (n := n) c (Iic R)) h x)
        (activeWindow (A i : Set X) (ballWindow K Γ hΓ (n := n) c (Iic R)) k x)) := by
  apply exists_disjoint_active_partition (ballSupport Γ c n R)
  rintro v ⟨hv,hball⟩
  let p := pointProbability K ⟨v,hv⟩
  have hp : p.coeff=v := pointProbability_coeff K _
  have hpK := pointProbability_face K ⟨v,hv⟩
  change centerDistance Γ hΓ K n c v≤R at hball
  rw [← hp,centerDistance_apply Γ hΓ K n _ p hpK] at hball
  rw [← hp]
  exact ⟨Finsupp.support_nonempty_iff.mp p.coeff_support_nonempty,
    ballSupport_contains Γ hΓ hn K hK c p hpK hR hball⟩
end
end
lemma ballVolume_strict_margin (D n : ℕ) (hD : 2≤D) (hn : volumeThreshold D≤n) :
    ballVolumeBound D n (4*(D : ℝ)^2)<
      dividedPower n (4*(D : ℝ)^2-2*(D : ℝ)^2) := by
  have he : 4*(D : ℝ)^2-2*(D : ℝ)^2=2*(D : ℝ)^2 := by ring
  simpa [ballVolumeBound,dividedPower,Nat.cast_mul,Nat.cast_pow,Nat.cast_add,he] using
    strict_volume_margin D n hD hn
end Sparse.GraphGeometry
end BassTrace
end
end OAI

end
section
namespace OAI
noncomputable section
namespace BassTrace
open Set MeasureTheory
open Finset MeasureTheory intervalIntegral
namespace Sparse
open Set Finset MeasureTheory
open scoped BassTrace.Sparse Classical ENNReal
section
variable {Y : Type*} [DecidableEq Y]
lemma affineSpan_simplex_constraints (s : Finset Y) {p : Y →₀ ℝ}
    (hp : p∈affineSpan ℝ (convexHull ℝ (simplexVertices s : Set (Y →₀ ℝ)))) :
    coefficientSum p=1 ∧ ∀ y∉s,p y=0 := by
  rw [affineSpan_convexHull] at hp
  refine affineSpan_induction (p := fun p : Y →₀ ℝ=>
    coefficientSum p=1 ∧ ∀ y∉s,p y=0) hp ?_ ?_
  · intro q hq
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hq
    refine ⟨by simp,?_⟩
    intro z hz
    simp [show y≠z from fun he=>hz (he ▸ hy)]
  · intro a u v w hu hv hw
    change coefficientSum (a•(u-v)+w)=1 ∧ ∀ y∉s,(a•(u-v)+w) y=0
    constructor
    · simp [map_add,map_smul,map_sub,hu.1,hv.1,hw.1]
    · intro y hy
      simp [hu.2 y hy,hv.2 y hy,hw.2 y hy]
lemma mem_sourceInterior_of_positive (s : Finset Y) (p : FinProbability Y)
    (hs : p.coeff.support⊆s) (hp : ∀ y∈s,0<p.coeff y) :
    p.coeff∈sourceInterior s := by
  let C := convexHull ℝ (simplexVertices s : Set (Y →₀ ℝ))
  have hC : C=probabilitySet s := by
    dsimp [C,simplexVertices]
    rw [Finset.coe_image,convexHull_single_eq_probabilitySet]
  have hpC : p.coeff∈C := hC ▸ ⟨p.nonneg,by simpa using p.total,hs⟩
  let q : affineSpan ℝ C := ⟨p.coeff,(subset_affineSpan ℝ C hpC)⟩
  let U : Set (affineSpan ℝ C) := ⋂ y : s,
    (fun v : affineSpan ℝ C=>v.val y.val) ⁻¹' Ioi 0
  have hU : IsOpen U := isOpen_iInter_of_finite fun y=>isOpen_Ioi.preimage
    ((coordinateCLM y.val).continuous.comp continuous_subtype_val)
  have hq : q∈U := Set.mem_iInter.mpr fun y=>hp y.val y.property
  have hUC : U⊆(Subtype.val ⁻¹' C) := by
    intro v hv
    have ha := affineSpan_simplex_constraints s v.property
    change v.val∈C
    apply (Set.ext_iff.mp hC v.val).mpr
    refine ⟨?_,ha.1,?_⟩
    · intro y
      by_cases hy : y∈s
      · exact (Set.mem_iInter.mp hv ⟨y,hy⟩).le
      · rw [ha.2 y hy]
    · intro y hy
      by_contra h
      exact Finsupp.mem_support_iff.mp hy (ha.2 y h)
  exact ⟨q,mem_interior_iff_mem_nhds.mpr
    (Filter.mem_of_superset (hU.mem_nhds hq) hUC),rfl⟩
lemma probability_mem_own_sourceInterior (p : FinProbability Y) :
    p.coeff∈sourceInterior p.coeff.support :=
  mem_sourceInterior_of_positive _ p subset_rfl fun y hy=>
    lt_of_le_of_ne (p.nonneg y) (Ne.symm (Finsupp.mem_support_iff.mp hy))
end
variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y]
  [TopologicalSpace X] [MulAction H X]
variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}
variable {ρ : (Y →₀ ℝ) → (Y →₀ ℝ) → ℝ} {R : ℝ}
open GraphGeometry
variable (Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
  (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K) ρ R n)
variable (hK : ∀ s∈K.faces,s.card≤n+1)
include hK in
lemma zero_mem_sourceTop_interior (x : X) {v : Y →₀ ℝ}
    (hv : v∈(Q.pair 0).P.val x) : ∃ σ : SourceTop K n,v∈sourceInterior σ.val := by
  have hvK : v∈(Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space :=
    ((Q.pair 0).T.val x).space_eq ▸ ((Q.pair 0).P.marked x).subset_space hv
  let p := pointProbability K ⟨v,hvK⟩
  have hp : p.coeff=v := pointProbability_coeff K _
  have hs := pointProbability_face K ⟨v,hvK⟩
  have hf : simplexVertices p.coeff.support∈
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).faces := ⟨_,hs,rfl⟩
  have hmem : v∈convexHull ℝ (simplexVertices p.coeff.support : Set (Y →₀ ℝ)) := by
    rw [← hp,simplexVertices,Finset.coe_image,p.mem_geometric_simplex]
  have hl := (Q.point x).card_lower_of_mem_zero (i := n) le_rfl hv
    (show simplexVertices p.coeff.support∈((Q.point x).T n).faces by
      change _∈((Q.pair n).T.val x).complex.faces
      rw [Q.top]; exact hf)
    (show convexHull ℝ (simplexVertices p.coeff.support : Set (Y →₀ ℝ))⊆(Q.point x).Z n by
      change _⊆(Q.pair n).P.val x
      rw [Q.top_space]
      exact (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).convexHull_subset_space hf) hmem
  have hlow : n+1≤p.coeff.support.card := hl.trans Finset.card_image_le
  have hcard : p.coeff.support.card=n+1 := le_antisymm (hK _ hs) hlow
  exact ⟨⟨p.coeff.support,hs,hcard⟩,hp ▸ probability_mem_own_sourceInterior p⟩
local instance : MeasurableSpace (Y →₀ ℝ) := borel (Y →₀ ℝ)
local instance : BorelSpace (Y →₀ ℝ) := ⟨rfl⟩
omit [Group H] [MulAction H Y] [TopologicalSpace X] [MulAction H X] in
lemma count_chart_image {n : ℕ} (s : Finset Y) (hs : s.card=n+1)
    (E : Set (Y →₀ ℝ)) (hE : ∀ p∈E,p.support⊆s) :
    Measure.count (simplexCoordinates s hs '' E)=Measure.count E := by
  have he : simplexEmbed s hs '' (simplexCoordinates s hs '' E)=E := by
    ext p
    constructor
    · rintro ⟨q,⟨v,hv,rfl⟩,rfl⟩
      rwa [simplexEmbed_coordinates s hs (hE v hv)]
    · intro hp
      exact ⟨simplexCoordinates s hs p,⟨p,hp,rfl⟩,simplexEmbed_coordinates s hs (hE p hp)⟩
  rw [← Measure.count_injective_image (simplexEmbed_injective s hs),he]
end Sparse
namespace Sparse.GraphGeometry
open Set Finset MeasureTheory
open scoped BassTrace.Sparse Classical ENNReal
section
variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y] [Countable Y]
  [TopologicalSpace X] [MulAction H X]
variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}
variable (Γ : SimpleGraph Y) (hΓ : Γ.Connected)
variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)
variable {ρ : (Y →₀ ℝ) → (Y →₀ ℝ) → ℝ} {R : ℝ}
variable (Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
  (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K) ρ R n)
local instance : MeasurableSpace (Y →₀ ℝ) := borel (Y →₀ ℝ)
local instance : BorelSpace (Y →₀ ℝ) := ⟨rfl⟩
local instance : Countable (SourceTop K n) := inferInstanceAs (Countable {s : Finset Y // s∈K.faces ∧ s.card=n+1})
include hK in
lemma zero_count_ball_le (x : X) (c : FinProbability Y) (b : ℝ) :
    Measure.count ((Q.pair 0).P.val x∩{v | centerDistance Γ hΓ K n c v≤b})≤
      ballIntegrand (n := n) Γ hΓ (Q.pair 0) 0 c b x := by
  have hd : ∀ s∈K.faces,s.card≤n+1 := by
    intro s hs
    obtain ⟨τ,_,hst,hc,_⟩ := hK s hs
    exact (Finset.card_le_card hst).trans_eq hc
  have hh : (Q.pair 0).P.val x∩{v | centerDistance Γ hΓ K n c v≤b}⊆
      ⋃ σ : SourceTop K n,(Q.pair 0).P.val x∩
        (sourceInterior σ.val∩{v | centerDistance Γ hΓ K n c v≤b}) := by
    rintro v ⟨hv,hb⟩
    obtain ⟨σ,hσ⟩ := zero_mem_sourceTop_interior Q hd x hv
    exact Set.mem_iUnion.mpr ⟨σ,hv,hσ,hb⟩
  calc
    _ ≤ _ := measure_mono hh
    _ ≤ ∑' σ : SourceTop K n,Measure.count ((Q.pair 0).P.val x∩
        (sourceInterior σ.val∩{v | centerDistance Γ hΓ K n c v≤b})) := measure_iUnion_le _
    _ = _ := by
      unfold ballIntegrand
      apply tsum_congr
      intro σ
      rw [localOriginalArea_zero_eq_count Γ hK,count_chart_image]
      exact fun p hp=>support_of_mem_sourceInterior _ hp.2.1
end
section
variable {Y : Type*} [DecidableEq Y]
variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}
variable (Γ : SimpleGraph Y) (hΓ : Γ.Connected) (hn : 0<n)
include hn in
lemma exists_finite_simplex_ball_cover (σ : SourceTop K n) {r : ℝ} (hr : 0<r) :
    ∃ C : Finset (FinProbability Y),
      (∀ c∈C,c.coeff.support⊆σ.val) ∧
      ∀ v∈convexHull ℝ (simplexVertices σ.val : Set (Y →₀ ℝ)),
        ∃ c∈C,centerDistance Γ hΓ K n c v≤r := by
  let := graphMetric Γ hΓ
  let := FinProbability.rhoMetric n hn (graphMetric_discrete Γ hΓ)
  let S : Set (FinProbability Y) := {p | p.coeff.support⊆σ.val}
  have hSc : IsCompact S := isCompact_probability_simplex σ.val n hn (graphMetric_discrete Γ hΓ)
  have hcover : S⊆⋃ p∈S,Metric.ball p r := by
    intro p hp
    exact Set.mem_iUnion₂.mpr ⟨p,hp,Metric.mem_ball_self hr⟩
  obtain ⟨T,hTS,hT,hcoverT⟩ := hSc.elim_finite_subcover_image
    (fun _ _=>Metric.isOpen_ball) hcover
  refine ⟨hT.toFinset,fun c hc=>hTS (hT.mem_toFinset.mp hc),?_⟩
  intro v hv
  have hvK : v∈(Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space :=
    (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).convexHull_subset_space
      ⟨σ.val,σ.property.1,rfl⟩ hv
  let p := pointProbability K ⟨v,hvK⟩
  have hp : p.coeff=v := pointProbability_coeff K _
  have hps : p.coeff.support⊆σ.val := by
    have hh := hv
    rw [simplexVertices,Finset.coe_image,convexHull_single_eq_probabilitySet,← hp] at hh
    exact hh.2.2
  obtain ⟨c,hc,hpc⟩ := Set.mem_iUnion₂.mp (hcoverT hps)
  refine ⟨c,hT.mem_toFinset.mpr hc,?_⟩
  rw [← hp,centerDistance_apply Γ hΓ K n c p (pointProbability_face K ⟨v,hvK⟩)]
  exact (FinProbability.rho_comm n p c) ▸ hpc.le
end
end Sparse.GraphGeometry
namespace Sparse
open Set Finset MeasureTheory
open scoped BassTrace.Sparse Classical ENNReal
variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y]
  [TopologicalSpace X] [MulAction H X]
variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}
variable {ρ : (Y →₀ ℝ) → (Y →₀ ℝ) → ℝ} {R : ℝ}
variable (Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
  (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K) ρ R n)
variable (hK : ∀ s∈K.faces,s.card≤n+1)
include hK in
lemma zero_inter_simplex_finite (σ : SourceTop K n) (x : X) :
    ((Q.pair 0).P.val x∩convexHull ℝ (simplexVertices σ.val : Set (Y →₀ ℝ))).Finite := by
  let L := Cuts.restrictComplex (Cuts.geometricRestriction ((Q.pair 0).T.val x).complex
    ((Q.pair 0).P.val x)) (convexHull ℝ (simplexVertices σ.val : Set (Y →₀ ℝ)))
  have hs : simplexVertices σ.val∈(Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).faces :=
    ⟨σ.val,σ.property.1,rfl⟩
  have hfin : L.faces.Finite := (((Q.pair 0).T.val x).finite _ hs).subset
    (fun t ht=>⟨ht.1.1,ht.2⟩)
  have hf : (⋃ t∈L.faces,(t : Set (Y →₀ ℝ))).Finite :=
    hfin.biUnion (fun t _=>t.finite_toSet)
  apply hf.subset
  intro v hv
  have hvL : v∈L.space := by
    change v∈(Cuts.restrictComplex (Cuts.geometricRestriction ((Q.pair 0).T.val x).complex
      ((Q.pair 0).P.val x)) (convexHull ℝ (simplexVertices σ.val : Set (Y →₀ ℝ)))).space
    rw [(Q.pair 0).P.trace_space _ hs]
    exact hv
  obtain ⟨t,ht,hvt⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hvL
  have hc : t.card≤0+1 := (Q.point x).dimension_bound
    (by rintro _ ⟨s,hs,rfl⟩; exact Finset.card_image_le.trans (hK s hs))
    (Nat.zero_le n) ht.1.1 ht.1.2
  obtain ⟨w,rfl⟩ := Finset.card_eq_one.mp (by
    exact Nat.le_antisymm hc (L.nonempty_of_mem_faces ht).card_pos)
  have he : v=w := by simpa using hvt
  exact Set.mem_iUnion₂.mpr ⟨{w},ht,by simp [he]⟩
end Sparse
namespace Sparse.GraphGeometry
end Sparse.GraphGeometry
end BassTrace
end
end OAI

end
section
open Set OAI OAI.BassTrace OAI.BassTrace.Sparse OAI.BassTrace.Sparse.Cuts OAI.BassTrace.Sparse.OrbitForms
open scoped Classical BassTrace.Sparse
namespace FT
variable {H X Y : Type} [Group H] [MulAction H X] [MulAction H Y] [TopologicalSpace X] [DecidableEq Y]
 {K : Geometry.SimplicialComplex ℝ (Y →₀ ℝ)} {n : ℕ} {ρ : (Y →₀ ℝ) → (Y →₀ ℝ) → ℝ} {R : ℝ}
 {count : (X → Set (Y →₀ ℝ)) → Prop}
theorem raw_iff : Raw (H:=H) K n (fun U=>ComponentDiameter ρ U (2*R)) count ↔
 ∃ Q : SeparatingFiltration (H:=H) (X:=X) K ρ R n,count (Q.pair 0).P.val := by
 classical
 constructor
 · rintro ⟨T,P,hc,hs,hm,hl,ha,hb,ht,hn⟩
   let mk {L B : Geometry.SimplicialComplex ℝ (Y →₀ ℝ)} (h : L.space=B.space ∧ (∀ s∈L.faces,∃ t∈B.faces,convexHull ℝ (s:Set (Y →₀ ℝ))⊆convexHull ℝ (t:Set (Y →₀ ℝ))) ∧ ∀ t∈B.faces,RespectsSet L (convexHull ℝ (t:Set (Y →₀ ℝ))) ∧ (Cuts.restrictComplex L (convexHull ℝ (t:Set (Y →₀ ℝ)))).faces.Finite) : Subdivision B :=
     ⟨L,h.1,h.2.1,fun t e=>(h.2.2 t e).1,fun t e=>(h.2.2 t e).2⟩
   let A (i : ℕ) : SubdivisionFamily X K := ⟨fun x=>mk (L:=T i x) (hs i x),fun t e=>(hl i t e).1⟩
   let B (i : ℕ) : MarkedPair (H:=H) (X:=X) K :=
     ⟨A i,⟨P i,hm i,fun t e=>(hl i t e).2⟩,ha i,hb i⟩
   exact ⟨⟨B,fun x=>(ht x).1,fun x=>(ht x).2,fun i e x=>⟨mk (L:=T i x) ((hn i e x).1),rfl⟩,
     fun i e x=>(hn i e x).2.1,fun i e x=>(hn i e x).2.2.1,fun i e x=>(hn i e x).2.2.2⟩,hc⟩
 · rintro ⟨Q,hc⟩
   refine ⟨fun i x=>((Q.pair i).T.val x).complex,fun i=>(Q.pair i).P.val,hc,?_,fun i=>(Q.pair i).P.marked,
     fun i t e=>⟨(Q.pair i).T.localConstancy t e,(Q.pair i).P.localConstancy t e⟩,
     fun i=>(Q.pair i).equivariant,fun i=>(Q.pair i).markedEquivariant,fun x=>⟨Q.top x,Q.top_space x⟩,?_⟩
   · intro i x
     let S := (Q.pair i).T.val x
     exact ⟨S.space_eq,S.carrier,fun t e=>⟨S.respects t e,S.finite t e⟩⟩
   · intro i e x
     refine ⟨?_,Q.nested i e x,Q.drop i e x,Q.diameter i e x⟩
     obtain ⟨S,hS⟩ := Q.finer i e x
     dsimp only
     rw [←hS]
     exact ⟨S.space_eq,S.carrier,fun t e=>⟨S.respects t e,S.finite t e⟩⟩
end FT
end
section
open Set MeasureTheory
open scoped Classical Pointwise
namespace FT
noncomputable def Leaf : Prop :=
∀ (H X Y : Type) [Group H] [Countable H] [Countable Y] [LinearOrder Y] [MulAction H Y] [IsCancelSMul H Y] [TopologicalSpace X] [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X] [MulAction H X] [ContinuousConstSMul H X] [IsCancelSMul H X] [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ], (∀ h:H,MeasurePreserving (fun x:X=>h•x) μ μ) →
 ∀ (G : SimpleGraph Y) [G.LocallyFinite], G.Connected → (∀ (h:H) u v,G.Adj (h•u) (h•v) ↔ G.Adj u v) → ∀ D n : ℕ,2≤D → (∀ y,Fintype.card (G.neighborSet y)≤D) → (4*D^3+D+3)^2≤n → ∀ (F : Finset (Finset Y)) (B : PreAbstractSimplicialComplex Y), (∀ t∈F,t.card=n+1 ∧ (G.induce (t:Set Y)).Connected) → B.faces={s | s.Nonempty ∧ ∃ h:H,∃ t∈F,s⊆h•t} →
 let K := Geometry.SimplicialComplex.onFinsupp (𝕜:=ℝ) B
 let V := Y →₀ ℝ
 letI := (letI : DecidableEq Y := Classical.decEq Y; TopologicalSpace.induced (Finsupp.linearCombination ℝ (fun y:Y=>lp.single 2 y (1:ℝ)) : V →ₗ[ℝ] lp (fun _:Y=>ℝ) 2) inferInstance)
 letI := borel V
 let E := fun (p:V) (f:Y→ℝ)=>p.sum fun y r=>r*f y
 let ok := fun U:Set V=>∀ A⊆U,IsPreconnected A → ∀ p∈A,∀ q∈A,sSup {r | ∃ f:Y→ℝ,(∀ u v,dist (f u) (f v)≤G.dist u v) ∧ E p f-E q f=r}/Real.sqrt n≤2*(4*(D:ℝ)^2)
 let I := {s : Finset Y // s∈B.faces ∧ s.card=n+1}
 ∃ C:I→ℝ,(∀ s,0≤C s) ∧ ∀ ε:ℝ,0<ε →
 let count := fun P:X→Set V=>∀ s:I,(∫ x,(Measure.count (P x∩convexHull ℝ ((s.val.image fun y=>Finsupp.single y (1:ℝ)):Set V))).toReal ∂μ)≤C s*ε
 let S := Geometry.SimplicialComplex ℝ V
 let c := fun s : Finset V => convexHull ℝ (s : Set V)
 let tr := fun (A : Set (Finset V)) (p : Set V) => {s ∈ A | (s : Set V) ⊆ p}
 let sub := fun (L B : S) => L.space=B.space ∧ (∀ s∈L.faces,∃ t∈B.faces,c s⊆c t) ∧
  ∀ t∈B.faces,(∀ s∈L.faces,c s∩c t=convexHull ℝ ((s:Set V)∩c t)) ∧ (tr L.faces (c t)).Finite
 let a := fun h : H => Finsupp.domLCongr (R:=ℝ) (MulAction.toPerm h : Y≃Y)
 ∃ (T : ℕ → X → S) (P : ℕ → X → Set V), count (P 0) ∧
 (∀ i x,sub (T i x) K) ∧ (∀ i x v,v∈P i x → ∃ s∈(T i x).faces,v∈c s ∧ c s⊆P i x) ∧
 (∀ i t,t∈K.faces → IsLocallyConstant (fun x=>tr (T i x).faces (c t)) ∧
  IsLocallyConstant (fun x=>tr {s∈(T i x).faces | c s⊆P i x} (c t))) ∧
 (∀ i h x s,s∈(T i x).faces → s.map (a h).toEmbedding∈(T i (h•x)).faces) ∧
 (∀ i h x v,v∈P i x → a h v∈P i (h•x)) ∧ (∀ x,T n x=K ∧ P n x=K.space) ∧
 ∀ i,i<n → ∀ x,sub (T i x) (T (i+1) x) ∧ P i x⊆P (i+1) x ∧
 (∀ t∈(T (i+1) x).faces,c t⊆P (i+1) x → ∀ s∈(T i x).faces,c s⊆c t∩P i x → s.card<t.card) ∧
 ok (P (i+1) x \ P i x)
end FT
end
section
namespace OAI
noncomputable section
namespace BassTrace
open Set MeasureTheory
open Finset MeasureTheory intervalIntegral
namespace Sparse.Cuts
open Set Finset
open scoped Classical
section
end
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {K : Geometry.SimplicialComplex ℝ V} {n : ℕ}
namespace PointFiltration
variable (Q : PointFiltration K n)
def FinalFace := {F : Finset V // F∈(Q.T 0).faces}
lemma final_mean_in_top (F : Q.FinalFace) : vertexMean F.val∈Q.Z n := by
  rw [Q.top_space]
  obtain ⟨S,hS⟩ := Q.refines (Nat.zero_le n) le_rfl
  have hF : F.val∈S.complex.faces := hS.symm ▸ F.property
  have hh := S.complex.convexHull_subset_space hF
    (vertexMean_mem_convexHull (S.complex.nonempty_of_mem_faces hF))
  rw [S.space_eq,Q.top] at hh
  exact hh
lemma exists_face_level (F : Q.FinalFace) : ∃ i,i≤n ∧ vertexMean F.val∈Q.Z i :=
  ⟨n,le_rfl,Q.final_mean_in_top F⟩
def faceLevel (F : Q.FinalFace) : ℕ := Nat.find (Q.exists_face_level F)
lemma faceLevel_le (F : Q.FinalFace) : Q.faceLevel F≤n :=
  (Nat.find_spec (Q.exists_face_level F)).1
lemma mean_mem_faceLevel (F : Q.FinalFace) : vertexMean F.val∈Q.Z (Q.faceLevel F) :=
  (Nat.find_spec (Q.exists_face_level F)).2
lemma mean_notMem_below_level (F : Q.FinalFace) {i : ℕ} (hi : i<Q.faceLevel F) :
    vertexMean F.val∉Q.Z i := by
  intro h
  exact Nat.not_lt_of_ge (Nat.find_min' (Q.exists_face_level F)
    ⟨hi.le.trans (Q.faceLevel_le F),h⟩) hi
def below (i : ℕ) : Set V := if i=0 then ∅ else Q.Z (i-1)
def stratum (i : ℕ) : Set V := Q.Z i \ Q.below i
def faceComponent (F : Q.FinalFace) : Set V :=
  connectedComponentIn (Q.stratum (Q.faceLevel F)) (vertexMean F.val)
lemma mean_mem_stratum (F : Q.FinalFace) :
    vertexMean F.val∈Q.stratum (Q.faceLevel F) := by
  refine ⟨Q.mean_mem_faceLevel F,?_⟩
  unfold below
  split_ifs with h
  · simp
  · exact Q.mean_notMem_below_level F (by omega)
lemma mean_mem_component (F : Q.FinalFace) : vertexMean F.val∈Q.faceComponent F :=
  mem_connectedComponentIn (Q.mean_mem_stratum F)
lemma faceComponent_subset (F : Q.FinalFace) : Q.faceComponent F⊆Q.stratum (Q.faceLevel F) :=
  connectedComponentIn_subset _ _
end PointFiltration
end Sparse.Cuts
namespace Sparse
open Set Finset
open scoped BassTrace.Sparse Classical
variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y]
  [TopologicalSpace X] [MulAction H X]
variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}
variable {ρ : (Y →₀ ℝ) → (Y →₀ ℝ) → ℝ} {R : ℝ}
variable (Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
  (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K) ρ R n)
variable (hK : ∀ s∈K.faces,s.card≤n+1)
include hK in
lemma zero_support_top (x : X) {v : Y →₀ ℝ}
    (hv : v∈(Q.pair 0).P.val x) : v.support∈K.faces ∧ v.support.card=n+1 := by
  have hvK : v∈(Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space :=
    ((Q.pair 0).T.val x).space_eq ▸ ((Q.pair 0).P.marked x).subset_space hv
  let p := GraphGeometry.pointProbability K ⟨v,hvK⟩
  have hp : p.coeff=v := GraphGeometry.pointProbability_coeff K _
  have hs : v.support∈K.faces := hp ▸ GraphGeometry.pointProbability_face K ⟨v,hvK⟩
  have hf : simplexVertices v.support∈
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).faces := ⟨_,hs,rfl⟩
  have hmem : v∈convexHull ℝ (simplexVertices v.support : Set (Y →₀ ℝ)) := by
    rw [← hp,simplexVertices,Finset.coe_image,p.mem_geometric_simplex]
  have hl := (Q.point x).card_lower_of_mem_zero (i := n) le_rfl hv
    (show simplexVertices v.support∈((Q.point x).T n).faces by
      change _∈((Q.pair n).T.val x).complex.faces
      rw [Q.top]; exact hf)
    (show convexHull ℝ (simplexVertices v.support : Set (Y →₀ ℝ))⊆(Q.point x).Z n by
      change _⊆(Q.pair n).P.val x
      rw [Q.top_space]
      exact (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).convexHull_subset_space hf) hmem
  exact ⟨hs,le_antisymm (hK _ hs) (hl.trans Finset.card_image_le)⟩
include hK in
lemma zero_isDiscrete (x : X) : IsDiscrete ((Q.pair 0).P.val x) := by
  apply isDiscrete_iff_forall_mem_exists_isOpen.mpr
  intro p hp
  let σ : SourceTop K n := ⟨p.support,zero_support_top Q hK x hp⟩
  let U : Set (Y →₀ ℝ) := ⋂ y : p.support,{q | q y.val≠0}
  have hU : IsOpen U := isOpen_iInter_of_finite fun y=>isOpen_ne.preimage
    (coordinateCLM y.val).continuous
  have hpU : p∈U := Set.mem_iInter.mpr fun y=>Finsupp.mem_support_iff.mp y.property
  let A := (Q.pair 0).P.val x∩convexHull ℝ (simplexVertices σ.val : Set (Y →₀ ℝ))
  have hA : A.Finite := zero_inter_simplex_finite Q hK σ x
  have hsub : U∩(Q.pair 0).P.val x⊆A := by
    rintro q ⟨hqU,hq⟩
    have hs : p.support⊆q.support := fun y hy=>Finsupp.mem_support_iff.mpr
      (Set.mem_iInter.mp hqU ⟨y,hy⟩)
    have he : p.support=q.support := Finset.eq_of_subset_of_card_le hs (by
      rw [(zero_support_top Q hK x hp).2,(zero_support_top Q hK x hq).2])
    have hqK : q∈(Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space :=
      ((Q.pair 0).T.val x).space_eq ▸ ((Q.pair 0).P.marked x).subset_space hq
    let r := GraphGeometry.pointProbability K ⟨q,hqK⟩
    refine ⟨hq,?_⟩
    change q∈convexHull ℝ (simplexVertices p.support : Set (Y →₀ ℝ))
    rw [show q=r.coeff from (GraphGeometry.pointProbability_coeff K ⟨q,hqK⟩).symm,
      simplexVertices,Finset.coe_image,r.mem_geometric_simplex]
    rw [GraphGeometry.pointProbability_coeff K ⟨q,hqK⟩]
    exact he.symm.subset
  refine ⟨U\(A\{p}),hU.sdiff (hA.sdiff.isClosed),?_⟩
  ext q
  constructor
  · rintro ⟨⟨hqu,hqa⟩,hq⟩
    by_contra hne
    exact hqa ⟨hsub ⟨hqu,hq⟩,hne⟩
  · intro hq
    have he : q=p := hq
    subst q
    exact ⟨⟨hpU,fun h=>h.2 rfl⟩,hp⟩
include hK in
lemma zero_component_subsingleton (x : X) (p : Y →₀ ℝ) :
    (connectedComponentIn ((Q.pair 0).P.val x) p).Subsingleton :=
  (isPreconnected_connectedComponentIn).isDiscrete_iff_subsingleton.mp
    ((zero_isDiscrete Q hK x).mono (connectedComponentIn_subset _ _))
end Sparse
namespace Sparse.GraphGeometry
open Set Finset
open Cuts.PointFiltration
open scoped BassTrace.Sparse Classical
variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y]
  [TopologicalSpace X] [MulAction H X]
variable {K : PreAbstractSimplicialComplex Y} {n : ℕ} {R : ℝ}
variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)
variable (Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
  (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K) (realizationDistance Γ hΓ K n) R n)
variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)
omit [DecidableEq Y] [Γ.LocallyFinite] in
include hK in
lemma original_card_bound : ∀ s∈K.faces,s.card≤n+1 := by
  intro s hs
  obtain ⟨σ,_,hst,hc,_⟩ := hK s hs
  exact (Finset.card_le_card hst).trans_eq hc
omit [Γ.LocallyFinite] in
lemma faceComponent_mem_space (x : X) (F : (Q.point x).FinalFace)
    {p : Y →₀ ℝ} (hp : p∈(Q.point x).faceComponent F) :
    p∈(Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space := by
  have hh := ((Q.point x).faceComponent_subset F hp).1
  have htop := (Q.point x).subset ((Q.point x).faceLevel_le F) le_rfl hh
  exact (Q.top_space x) ▸ htop
omit [Γ.LocallyFinite] in
include hK in
lemma faceComponent_distance (hR : 0≤R) (x : X) (F : (Q.point x).FinalFace)
    {p q : Y →₀ ℝ} (hp : p∈(Q.point x).faceComponent F)
    (hq : q∈(Q.point x).faceComponent F) :
    realizationDistance Γ hΓ K n p q≤2*R := by
  by_cases hz : (Q.point x).faceLevel F=0
  · have he : (Q.point x).faceComponent F=
        connectedComponentIn ((Q.pair 0).P.val x) (Cuts.vertexMean F.val) := by
      simp only [faceComponent,hz,stratum,below,ite_true,Set.sdiff_empty]
      rfl
    have heq : p=q := (zero_component_subsingleton Q (original_card_bound Γ hK) x _) (he ▸ hp) (he ▸ hq)
    subst q
    have hr : realizationDistance Γ hΓ K n p p=0 := by
      simp [realizationDistance,FinProbability.rho,FinProbability.transport_self]
    rw [hr]
    positivity
  · have hi : (Q.point x).faceLevel F-1<n := by
      have := (Q.point x).faceLevel_le F
      omega
    apply Q.diameter _ hi x ((Q.point x).faceComponent F)
      (isPreconnected_connectedComponentIn) ?_ p hp q hq
    have he : (Q.point x).stratum ((Q.point x).faceLevel F)=
        (Q.pair ((Q.point x).faceLevel F-1+1)).P.val x\
          (Q.pair ((Q.point x).faceLevel F-1)).P.val x := by
      have hi' : (Q.point x).faceLevel F-1+1=(Q.point x).faceLevel F := by omega
      rw [hi']
      simp only [stratum,below,ite_eq_right hz]
      rfl
    exact he ▸ (Q.point x).faceComponent_subset F
def labelWindow (n : ℕ) (R : ℝ) (s : Finset Y) : Finset Y :=
  s.biUnion (neighborhood Γ (⌊(2*R)*Real.sqrt (n : ℝ)⌋₊+n))
include hK in
lemma component_support_subset (hn : 0<n) (hR : 0≤R) (x : X)
    (F : (Q.point x).FinalFace) (s : Finset Y)
    (hFs : Cuts.vertexMean F.val∈convexHull ℝ (simplexVertices s : Set (Y →₀ ℝ)))
    {v : Y →₀ ℝ} (hv : v∈(Q.point x).faceComponent F) :
    v.support⊆labelWindow Γ n R s := by
  let p := pointProbability K ⟨Cuts.vertexMean F.val,
    faceComponent_mem_space Γ hΓ Q x F ((Q.point x).mean_mem_component F)⟩
  let q := pointProbability K ⟨v,faceComponent_mem_space Γ hΓ Q x F hv⟩
  have hp : p.coeff=Cuts.vertexMean F.val := pointProbability_coeff K _
  have hq : q.coeff=v := pointProbability_coeff K _
  obtain ⟨τ,hτ,hqτ,hcard,hconn⟩ := hK q.coeff.support (pointProbability_face K _)
  have hdist : @FinProbability.rho Y (graphMetric Γ hΓ).toPseudoMetricSpace n p q≤2*R := by
    rw [← realizationDistance_apply Γ hΓ K n p q (pointProbability_face K _) (pointProbability_face K _),hp,hq]
    exact faceComponent_distance Γ hΓ Q hK hR x F ((Q.point x).mean_mem_component F) hv
  have hmem := meeting_simplex_vertices Γ hΓ hn p q τ hcard hconn hqτ (2*R)
    (by positivity) hdist
  have hps : p.coeff.support⊆s := by
    rw [← hp,simplexVertices,Finset.coe_image,p.mem_geometric_simplex] at hFs
    exact hFs
  rw [← hq]
  exact hqτ.trans (hmem.trans (Finset.biUnion_subset_biUnion_of_subset_left _ hps))
end Sparse.GraphGeometry
namespace Sparse
open Set Finset
open scoped BassTrace.Sparse Classical
variable {Y : Type*}
def supportVertices (U : Set (Y →₀ ℝ)) : Set Y :=
  {y | ∃p∈U,y∈p.support}
variable {H X : Type*} [Group H] [MulAction H Y] [DecidableEq Y]
  [TopologicalSpace X] [MulAction H X]
variable {K : PreAbstractSimplicialComplex Y} {n : ℕ} {R : ℝ}
variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)
variable (Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
  (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K)
  (GraphGeometry.realizationDistance Γ hΓ K n) R n)
variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)
include hK in
lemma componentSupport_subset (hn : 0<n) (hR : 0≤R) (x : X)
    (F : (Q.point x).FinalFace) (s : Finset Y)
    (hFs : Cuts.vertexMean F.val∈convexHull ℝ (simplexVertices s : Set (Y →₀ ℝ))) :
    supportVertices ((Q.point x).faceComponent F)⊆
      (GraphGeometry.labelWindow Γ n R s : Set Y) := by
  rintro y ⟨p,hp,hy⟩
  exact GraphGeometry.component_support_subset Γ hΓ Q hK hn hR x F s hFs hp hy
include hK in
lemma componentSupport_finite (hn : 0<n) (hR : 0≤R) (x : X)
    (F : (Q.point x).FinalFace) :
    (supportVertices ((Q.point x).faceComponent F)).Finite := by
  have hmK := GraphGeometry.faceComponent_mem_space Γ hΓ Q x F ((Q.point x).mean_mem_component F)
  let p := GraphGeometry.pointProbability K ⟨Cuts.vertexMean F.val,hmK⟩
  have hp : p.coeff=Cuts.vertexMean F.val := GraphGeometry.pointProbability_coeff K _
  have hms : Cuts.vertexMean F.val∈convexHull ℝ
      (simplexVertices p.coeff.support : Set (Y →₀ ℝ)) := by
    rw [← hp,simplexVertices,Finset.coe_image,p.mem_geometric_simplex]
  exact (Finset.finite_toSet (GraphGeometry.labelWindow Γ n R p.coeff.support)).subset
    (componentSupport_subset Γ hΓ Q hK hn hR x F p.coeff.support hms)
end Sparse
end BassTrace
end
end OAI

end
section
namespace OAI
noncomputable section
namespace BassTrace
namespace Sparse
end Sparse
namespace Sparse.Cuts.PointFiltration
end Sparse.Cuts.PointFiltration
namespace Sparse.GraphGeometry
end Sparse.GraphGeometry
namespace Sparse.OrbitForms
namespace SeparatingFiltration
end SeparatingFiltration
end Sparse.OrbitForms
end BassTrace
end
end OAI

end
section
namespace OAI
namespace BassTrace.Sparse.Cuts
noncomputable section
namespace PointFiltration
end PointFiltration
end
end BassTrace.Sparse.Cuts
end OAI

end
section
namespace OAI
open Set MeasureTheory
open Finset MeasureTheory intervalIntegral
namespace BassTrace.FiniteAverage
open Set Finset MeasureTheory
open scoped Classical
noncomputable section
section AlgebraicNorm
end AlgebraicNorm
variable {X V W : Type*} [MeasurableSpace X]
  [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
variable (μ : Measure X)
def average (f : SimpleFunc X V) : V :=
  ∑v∈f.range, μ.real (f⁻¹' {v}) • v
section LocallyConstant
end LocallyConstant
end
end BassTrace.FiniteAverage
end OAI

end
section
namespace OAI
noncomputable section
namespace BassTrace.Paths
section
end
section
end
section
end
end BassTrace.Paths
end
end OAI

end
section
namespace OAI
noncomputable section
namespace BassTrace.Paths
section
end
section
end
end BassTrace.Paths
end
end OAI

end
section
namespace OAI
noncomputable section
namespace BassTrace.Detector
section
end
section
end
section
end
end BassTrace.Detector
end
end OAI

end
section
namespace OAI
noncomputable section
namespace BassTrace
namespace Detector
end Detector
namespace Oriented
end Oriented
namespace Detector
end Detector
end BassTrace
end
end OAI

end
section
namespace OAI
noncomputable section
namespace BassTrace
namespace RelativeExponents
end RelativeExponents
namespace Detector
section
end
section
end
end Detector
end BassTrace
end
end OAI

end
section
namespace OAI
noncomputable section
namespace BassTrace
namespace Detector
end Detector
namespace Paths
end Paths
namespace Detector
section
end
end Detector
end BassTrace
end
end OAI

end
section
namespace OAI
noncomputable section
namespace BassTrace.PathChains
section
end
end BassTrace.PathChains
end
end OAI

end
section
namespace OAI
noncomputable section
namespace BassTrace.Detector
section
end
end BassTrace.Detector
end
end OAI

end
section
namespace OAI
noncomputable section
namespace BassTrace.FreeParameter
section Probability
end Probability
namespace Character
end Character
end BassTrace.FreeParameter
end
end OAI

end
section
namespace OAI
noncomputable section
namespace BassTrace
section
end
end BassTrace
end
end OAI

end
section
namespace OAI
open Set MeasureTheory
open Finset MeasureTheory intervalIntegral
noncomputable section
namespace BassTrace.Sparse
section
open Set Finset
open scoped Classical Pointwise
variable {H Y : Type*} [Group H] [MulAction H Y]
def generatedComplex (T : Finset (Finset Y)) : PreAbstractSimplicialComplex Y where
  faces := {s | s.Nonempty ∧ ∃h : H,∃t∈T,s⊆h • t}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨hs.1,?_⟩
    intro t hts ht
    obtain ⟨h,u,hu,hsu⟩ := hs.2
    exact ⟨ht,h,u,hu,hts.trans hsu⟩
lemma generatedComplex_invariant (T : Finset (Finset Y)) (h : H) s
    (hs : s∈(generatedComplex (H := H) T).faces) :
    s.map (MulAction.toPerm h).toEmbedding∈(generatedComplex (H := H) T).faces := by
  rw [←smul_finset_eq_map]
  obtain ⟨hne,k,t,ht,hst⟩ := hs
  refine ⟨Finset.smul_finset_nonempty.mpr hne,h*k,t,ht,?_⟩
  rw [mul_smul]
  exact Finset.smul_finset_subset_smul_finset hst
lemma generatedComplex_top_mem (T : Finset (Finset Y)) {t : Finset Y}
    (ht : t∈T) (hne : t.Nonempty) : t∈(generatedComplex (H := H) T).faces :=
  ⟨hne,1,t,ht,by simp only [one_smul,Finset.Subset.refl]⟩
lemma connected_smul (Γ : SimpleGraph Y)
    (ha : ∀ (h : H) u v,Γ.Adj (h•u) (h•v) ↔ Γ.Adj u v)
    (h : H) (t : Finset Y) (hc : (Γ.induce (t : Set Y)).Connected) :
    (Γ.induce (↑(h • t) : Set Y)).Connected := by
  let f : Γ.induce (t : Set Y) →g Γ.induce (↑(h • t) : Set Y) := {
    toFun := fun y=>⟨h•y.val,Finset.smul_mem_smul_finset (a := h) y.property⟩
    map_rel' := fun hy=>(ha h _ _).mpr hy }
  apply hc.map f
  intro y
  obtain ⟨z,hz,he⟩ := Finset.mem_smul_finset.mp y.property
  exact ⟨⟨z,hz⟩,Subtype.ext he⟩
lemma generatedComplex_pure (T : Finset (Finset Y)) (n : ℕ) (Γ : SimpleGraph Y)
    (ha : ∀ (h : H) u v,Γ.Adj (h•u) (h•v) ↔ Γ.Adj u v)
    (hT : ∀t∈T,t.card=n+1 ∧ (Γ.induce (t : Set Y)).Connected) :
    ∀s∈(generatedComplex (H := H) T).faces,∃σ∈(generatedComplex (H := H) T).faces,
      s⊆σ ∧ σ.card=n+1 ∧ (Γ.induce (σ : Set Y)).Connected := by
  intro s hs
  obtain ⟨hne,h,t,ht,hst⟩ := hs
  refine ⟨h•t,⟨hne.mono hst,h,t,ht,subset_rfl⟩,hst,?_,connected_smul Γ ha h t (hT t ht).2⟩
  simpa only [Finset.card_smul_finset] using (hT t ht).1
def generatedReps (T : Finset (Finset Y)) : Finset (Finset Y) :=
  (T.biUnion Finset.powerset).filter (·.Nonempty)
lemma generatedReps_mem (T : Finset (Finset Y)) {s : Finset Y}
    (hs : s∈generatedReps T) : s∈(generatedComplex (H := H) T).faces := by
  obtain ⟨hs,hne⟩ := Finset.mem_filter.mp hs
  obtain ⟨t,ht,hst⟩ := Finset.mem_biUnion.mp hs
  exact ⟨hne,1,t,ht,by simpa only [one_smul] using Finset.mem_powerset.mp hst⟩
lemma generatedReps_complete (T : Finset (Finset Y)) {s : Finset Y}
    (hs : s∈(generatedComplex (H := H) T).faces) :
    ∃h : H,∃t∈generatedReps T,s=t.map (MulAction.toPerm h).toEmbedding := by
  obtain ⟨hne,h,t,ht,hst⟩ := hs
  refine ⟨h,h⁻¹•s,?_,?_⟩
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_biUnion.mpr ⟨t,ht,Finset.mem_powerset.mpr ?_⟩,
      Finset.smul_finset_nonempty.mpr hne⟩
    have hh := Finset.smul_finset_subset_smul_finset (a := h⁻¹) hst
    simpa only [inv_smul_smul] using hh
  · rw [←smul_finset_eq_map,smul_inv_smul]
lemma generatedTop_finite (T : Finset (Finset Y)) (n : ℕ)
    (hT : ∀t∈T,t.card=n+1) :
    letI := sourceTopAction (generatedComplex (H := H) T) n (generatedComplex_invariant T)
    Finite (MulAction.orbitRel.Quotient H (SourceTop (generatedComplex (H := H) T) n)) := by
  let := sourceTopAction (generatedComplex (H := H) T) n (generatedComplex_invariant T)
  let f : T → MulAction.orbitRel.Quotient H (SourceTop (generatedComplex (H := H) T) n) :=
    fun t=>Quotient.mk _ ⟨t.val,generatedComplex_top_mem T t.property
      (Finset.card_pos.mp (by rw [hT t t.property]; omega)),hT t t.property⟩
  apply Finite.of_surjective f
  intro q
  induction q using Quotient.inductionOn with | _ σ =>
    obtain ⟨hne,h,t,ht,hst⟩ := σ.property.1
    have he : σ.val=h•t := Finset.eq_of_subset_of_card_le hst (by
      rw [Finset.card_smul_finset,hT t ht,σ.property.2])
    refine ⟨⟨t,ht⟩,Quotient.sound ?_⟩
    apply MulAction.mem_orbit_iff.mpr
    refine ⟨h⁻¹,Subtype.ext ?_⟩
    change h⁻¹ • σ.val=t
    rw [he,inv_smul_smul]
end
section
open Set Finset
open scoped BassTrace.Sparse Classical
variable {Y : Type*}
variable {H X : Type*} [Group H] [MulAction H Y] [DecidableEq Y]
  [TopologicalSpace X] [MulAction H X]
variable {K : PreAbstractSimplicialComplex Y} {n : ℕ} {R : ℝ}
variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)
variable (Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
  (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K)
  (GraphGeometry.realizationDistance Γ hΓ K n) R n)
variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)
variable (hn : 0<n) (hR : 0≤R)
def componentVertices (x : X) (F : (Q.point x).FinalFace) : Finset Y :=
  (componentSupport_finite Γ hΓ Q hK hn hR x F).toFinset
@[simp] lemma mem_componentVertices (x : X) (F : (Q.point x).FinalFace) (y : Y) :
    y∈componentVertices Γ hΓ Q hK hn hR x F ↔
      y∈supportVertices ((Q.point x).faceComponent F) := Set.Finite.mem_toFinset _
end
end BassTrace.Sparse
namespace BassTrace.SubdivisionChains
section
open Set Finset
open scoped BassTrace.Sparse Classical
open Sparse Oriented ChainHomotopy Fundamental OrientedIncidence
variable {Y : Type*} [LinearOrder Y] [LinearOrder (Y →₀ ℝ)]
variable {K : PreAbstractSimplicialComplex Y}
variable (T : Cuts.Subdivision (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
def chart {k : ℕ} (v : Fin k → Y) : (Y →₀ ℝ) →ₗ[ℝ] (Fin k → ℝ) :=
  LinearMap.pi (fun i=>Finsupp.lapply (v i))
omit [LinearOrder Y] [LinearOrder (Y →₀ ℝ)] in
@[simp] lemma chart_apply {k : ℕ} (v : Fin k → Y) (p : Y →₀ ℝ) (i : Fin k) :
    chart v p i=p (v i) := rfl
def localTriangulation (s : Finset Y) :=
  Cuts.restrictComplex T.complex (convexHull ℝ (simplexVertices s : Set (Y →₀ ℝ)))
omit [LinearOrder (Y →₀ ℝ)] in
lemma localTriangulation_finite (s : Finset Y) (hs : s∈K.faces) :
    (localTriangulation T s).faces.Finite := T.finite (simplexVertices s) ⟨s,hs,rfl⟩
def tupleSubdivision (k : ℕ) (v : Fin (k+1) → Y) : Degree (Y →₀ ℝ) (k+1) :=
  if hs : Finset.univ.image v∈K.faces then
    chain (faces (localTriangulation T (Finset.univ.image v))
      (localTriangulation_finite T _ hs) (k+1)) (chart v)
  else 0
omit [LinearOrder Y] in
lemma chain_chart_perm {k : ℕ} (A : Finset (Set.powersetCard (Y →₀ ℝ) (k+1)))
    (v : Fin (k+1) → Y) (σ : Equiv.Perm (Fin (k+1))) :
    chain A (chart (v ∘ σ))=(Equiv.Perm.sign σ) • chain A (chart v) := by
  unfold chain
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro s _
  have he : Matrix.det (fun i=>chart (v ∘ σ) (vertices s i))=
      (Equiv.Perm.sign σ : ℝ)*Matrix.det (fun i=>chart v (vertices s i)) :=
    by exact Matrix.det_permute' σ (fun i j=>vertices s i (v j))
  rw [he]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · simp [h]
  · simp only [h,Units.val_neg,Units.val_one,Int.cast_neg,Int.cast_one,neg_one_mul,
      Real.sign_neg,Complex.ofReal_neg,Units.neg_smul,one_smul]
    exact _root_.neg_smul (Real.sign (Matrix.det (fun i=>chart v (vertices s i))) : ℂ)
      (basis (k+1) s)
lemma tupleSubdivision_perm (k : ℕ) (v : Fin (k+1) → Y)
    (σ : Equiv.Perm (Fin (k+1))) :
    tupleSubdivision T k (v ∘ σ)=(Equiv.Perm.sign σ) • tupleSubdivision T k v := by
  unfold tupleSubdivision
  simp only [tuple_image_perm]
  split_ifs with hs
  · exact chain_chart_perm _ v σ
  · simp
lemma tupleSubdivision_zero (k : ℕ) (v : Fin (k+1) → Y)
    (hv : ¬Function.Injective v) : tupleSubdivision T k v=0 := by
  unfold tupleSubdivision
  split_ifs with hs
  · unfold chain
    apply Finset.sum_eq_zero
    intro s _
    obtain ⟨i,j,hij,hne⟩ := Function.not_injective_iff.mp hv
    have hd : Matrix.det (fun a=>chart v (vertices s a))=0 :=
      Matrix.det_zero_of_column_eq hne (fun a=>congrArg (vertices s a) hij)
    rw [hd,Real.sign_zero,Complex.ofReal_zero,zero_smul]
  · rfl
def subdivisionValues (k : ℕ) : AltFunction Y (k+1) (Degree (Y →₀ ℝ) (k+1)) where
  toFun := tupleSubdivision T k
  perm := tupleSubdivision_perm T k
  zero := tupleSubdivision_zero T k
def subdivision : ∀ k, Degree Y k →ₗ[ℂ] Degree (Y →₀ ℝ) k
  | 0 => relabel 0 (fun y=>Finsupp.single y (1:ℝ))
  | k+1 => (subdivisionValues T k).lift
@[simp] lemma subdivision_wedge_succ (k : ℕ) (v : Fin (k+1) → Y) :
    subdivision T (k+1) (wedge (k+1) v)=tupleSubdivision T k v :=
  (subdivisionValues T k).lift_wedge v
end
end BassTrace.SubdivisionChains
end
end OAI

end
section
namespace OAI
noncomputable section
namespace BassTrace.BarycentricChains
end BassTrace.BarycentricChains
namespace BassTrace.Sparse
end BassTrace.Sparse
namespace BassTrace.PathChains
section
end
end BassTrace.PathChains
end
end OAI

end
section
namespace OAI
noncomputable section
namespace BassTrace.SubdivisionChains
end BassTrace.SubdivisionChains
namespace BassTrace.Sparse
end BassTrace.Sparse
namespace BassTrace.FiniteAverage
end BassTrace.FiniteAverage
namespace BassTrace.Sparse
end BassTrace.Sparse
end
end OAI

end
section
namespace OAI
noncomputable section
namespace BassTrace.BarycentricChains
section
end
section
end
section
namespace ActualFlags
end ActualFlags
end
section
end
end BassTrace.BarycentricChains
namespace BassTrace.BarycentricChains.ActualFlags
end BassTrace.BarycentricChains.ActualFlags
end
end OAI

end
section
namespace OAI
open Set MeasureTheory
open Finset MeasureTheory intervalIntegral
noncomputable section
namespace BassTrace.Sparse
section
end
end BassTrace.Sparse
namespace BassTrace.BarycentricChains
end BassTrace.BarycentricChains
namespace BassTrace.Sparse
end BassTrace.Sparse
namespace BassTrace.Sparse.GraphGeometry
section
end
open scoped Classical
lemma graphMetric_action_isometry {H Y : Type*} [Group H] [MulAction H Y]
    (Γ : SimpleGraph Y) (hΓ : Γ.Connected)
    (hAut : ∀(h : H) u v,Γ.Adj (h•u) (h•v) ↔ Γ.Adj u v) (h : H) :
    @Isometry Y Y (graphMetric Γ hΓ).toPseudoEMetricSpace
      (graphMetric Γ hΓ).toPseudoEMetricSpace (fun y=>h•y) := by
  let _ := graphMetric Γ hΓ
  have hle (h : H) (u v : Y) : Γ.dist (h•u) (h•v)≤Γ.dist u v := by
    let f : Γ →g Γ := ⟨fun y=>h•y,fun ha=>(hAut h _ _).mpr ha⟩
    obtain ⟨p,hp⟩ := hΓ.exists_walk_length_eq_dist u v
    calc _ ≤ (p.map f).length := SimpleGraph.dist_le _
         _ = _ := by rw [SimpleGraph.Walk.length_map,hp]
  apply Isometry.of_dist_eq
  intro u v
  change (Γ.dist (h•u) (h•v) : ℝ)=(Γ.dist u v : ℝ)
  congr 1
  apply le_antisymm (hle h u v)
  simpa only [inv_smul_smul] using hle h⁻¹ (h•u) (h•v)
end BassTrace.Sparse.GraphGeometry
end
end OAI

end
section
open Set
open scoped Classical
namespace GlobalCut
noncomputable section
def Target : Prop := ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V],
 let C := Geometry.SimplicialComplex ℝ V
 let c (s : Finset V) := convexHull ℝ (s : Set V)
 let hs (p : Set V) := ∃ (l : V →ₗ[ℝ] ℝ) (r : ℝ), p = {x | l x ≤ r}
 let act (s : Finset V) (A : Finset (Set V)) := (A.image (fun p => c s ∩ p)).filter (fun q => q.Nonempty ∧ q ≠ c s)
 ∃ F : Finset V → Finset (Set V) → C, ∀ (K : C) (A : Finset V → Finset (Set V)),
 (∀ s ∈ K.faces, ∀ p ∈ A s, hs p) → (∀ s ∈ K.faces, ∀ t ⊆ s, t.Nonempty → act t (A s) = act t (A t)) →
 ∃ G : C, G.faces = {u | ∃ s ∈ K.faces, u ∈ (F s (A s)).faces} ∧ G.space = K.space ∧
 ∀ s ∈ K.faces, let L := F s (A s)
 L.faces.Finite ∧ L.space = c s ∧ {u ∈ G.faces | (u : Set V) ⊆ c s} = L.faces ∧
 (∀ u ∈ G.faces, c u ∩ c s = convexHull ℝ ((u : Set V) ∩ c s)) ∧
 (∀ u ∈ L.faces, ∀ (l : V →ₗ[ℝ] ℝ) (r : ℝ), {x | l x ≤ r} ∈ A s → c u ⊆ {x | l x ≤ r} ∨ c u ⊆ {x | r ≤ l x}) ∧
 ∀ e : V ≃L[ℝ] V, (F (s.map e.toEquiv.toEmbedding) ((A s).image (fun p => e '' p))).faces = (fun u : Finset V => u.map e.toEquiv.toEmbedding) '' L.faces
end
end GlobalCut
end
section
open Set
namespace GlobalCut
open scoped Classical
variable {V I : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable (a : I → V →ₗ[ℝ] ℝ) (b : I → ℝ) (R : Finset V → Finset I)

noncomputable def arr (s : Finset V) := (R s).image (fun i => {x | a i x ≤ b i})
noncomputable def active (s : Finset V) (A : Finset (Set V)) :=
  (A.image (fun p => convexHull ℝ (s : Set V) ∩ p)).filter (fun q => q.Nonempty ∧ q ≠ convexHull ℝ (s : Set V))
lemma active_subset (t : Finset V) (hb : ∀ i, 0 ≤ b i)
    (hz : ∀ s i, i ∉ R s → ∀ x ∈ convexHull ℝ (s : Set V), a i x = 0) (u v : Finset V)
    (hv : t ⊆ v) : active t (arr a b R u) ⊆ active t (arr a b R v) := by
  intro q hq
  obtain ⟨hq,hn,hh⟩ := Finset.mem_filter.mp hq
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hp
  have hm : i ∈ R v := by
    by_contra h
    apply hh; apply Set.inter_eq_left.mpr; intro x hx
    change a i x ≤ b i; rw [hz v i h x (convexHull_mono hv hx)]; exact hb i
  exact Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ hm),hn,hh⟩
end GlobalCut
end
section
namespace OAI.BassTrace.Sparse.Cuts.Factory
open Set Finset GlobalCut
open scoped Classical
noncomputable section
variable (g : Target) {V J : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable (d : UniversalCuts V J) (K : Geometry.SimplicialComplex ℝ V)
abbrev A := arr d.form d.level d.relevant
abbrev L (s : Finset V) := (g V).choose s (A d s)
private def witness := (g V).choose_spec K (A d) (by
  intro s _ p hp; obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hp; exact ⟨_,_,rfl⟩) (by
  intro s _ t ht _; apply Finset.Subset.antisymm
  · exact active_subset _ _ _ t d.positive d.vanish s t (Finset.Subset.refl _)
  · exact active_subset _ _ _ t d.positive d.vanish t s ht)
def G := (witness g d K).choose
def spec := (witness g d K).choose_spec
lemma carrier {u} (hu : u ∈ (G g d K).faces) : ∃ s ∈ K.faces,
    convexHull ℝ (u : Set V) ⊆ convexHull ℝ (s : Set V) := by
  obtain ⟨s,hs,h⟩ := (spec g d K).1 ▸ hu
  refine ⟨s,hs,?_⟩
  have eq : (L g d s).space = convexHull ℝ (s : Set V) := ((spec g d K).2.2 s hs).2.1
  rw [← eq]; exact (L g d s).convexHull_subset_space h
lemma carrierIn {P : Set V} (hP : RespectsSet K P)
    {s : Finset V} (hs : s ∈ (G g d K).faces) (hsP : (s : Set V) ⊆ P) :
    ∃ t ∈ K.faces, (t : Set V) ⊆ P ∧
      convexHull ℝ (s : Set V) ⊆ convexHull ℝ (t : Set V) := by
  classical
  obtain ⟨t,ht,hst⟩ := carrier g d K hs
  have hv : (s : Set V) ⊆ convexHull ℝ (t : Set V) ∩ P :=
    subset_inter ((subset_convexHull ℝ _).trans hst) hsP
  have hne : (convexHull ℝ (t : Set V) ∩ P).Nonempty :=
    ((G g d K).nonempty_of_mem_faces hs).to_set.mono hv
  refine ⟨t.filter (· ∈ P),respectsSet_face hP ht hne,?_,?_⟩
  · intro x hx
    exact (Finset.mem_filter.mp hx).2
  · apply convexHull_min
    · simpa only [coe_filter_mem] using (hP t ht ▸ hv)
    · exact convex_convexHull ℝ _
lemma preserves {P : Set V} (hP : RespectsSet K P) :
    RespectsSet (G g d K) P := by
  classical
  intro s hs
  obtain ⟨t,ht,hst⟩ := carrier g d K hs
  by_cases hh : (convexHull ℝ (t : Set V) ∩ P).Nonempty
  · let u := t.filter (· ∈ P)
    have hu : u ∈ K.faces := respectsSet_face hP ht hh
    have huet : convexHull ℝ (u : Set V) = convexHull ℝ (t : Set V) ∩ P := by
      simpa only [u,coe_filter_mem] using (hP t ht).symm
    have htrace := ((spec g d K).2.2 u hu).2.2.2.1 s hs
    have hleft : convexHull ℝ (s : Set V) ∩ convexHull ℝ (u : Set V) =
        convexHull ℝ (s : Set V) ∩ P := by
      rw [huet]
      rw [← Set.inter_assoc,Set.inter_eq_left.mpr hst]
    have hv : (s : Set V) ∩ convexHull ℝ (u : Set V) = (s : Set V) ∩ P := by
      rw [huet]
      have hsub := (subset_convexHull ℝ (s : Set V)).trans hst
      rw [← Set.inter_assoc,Set.inter_eq_left.mpr hsub]
    simpa only [hleft,hv] using htrace
  · have he : convexHull ℝ (s : Set V) ∩ P = ∅ :=
      Set.eq_empty_iff_forall_notMem.mpr (fun y hy => hh ⟨y,hst hy.1,hy.2⟩)
    have hv : (s : Set V) ∩ P = ∅ :=
      Set.eq_empty_iff_forall_notMem.mpr (fun y hy => hh ⟨y,
        hst (subset_convexHull ℝ _ hy.1),hy.2⟩)
    rw [he,hv,convexHull_empty]
lemma restrictEq (t : Finset V) (ht : t ∈ K.faces) : (restrictComplex (G g d K) (convexHull ℝ (t : Set V))).faces = (L g d t).faces := ((spec g d K).2.2 t ht).2.2.1
lemma mem_iff {P : Set V}
    (hP : RespectsSet K P) (s : Finset V) :
    s ∈ (restrictComplex (G g d K) P).faces ↔
      ∃ t ∈ (restrictComplex K P).faces, s ∈ (L g d t).faces := by
  constructor
  · intro hs
    obtain ⟨t,ht,htP,hst⟩ := carrierIn g d K hP hs.1 hs.2
    refine ⟨t,⟨ht,htP⟩,?_⟩
    have hh : s ∈ (restrictComplex (G g d K)
        (convexHull ℝ (t : Set V))).faces :=
      ⟨hs.1,(subset_convexHull ℝ _).trans hst⟩
    rwa [restrictEq g d K t ht] at hh
  · rintro ⟨t,⟨ht,htP⟩,hst⟩
    have hh : s ∈ (restrictComplex (G g d K)
        (convexHull ℝ (t : Set V))).faces := by
      rw [restrictEq g d K t ht]
      exact hst
    have htrace := hP t ht
    have htconv : convexHull ℝ (t : Set V) ⊆ P := by
      have he : (t : Set V) ∩ P = t := Set.inter_eq_left.mpr htP
      rw [he] at htrace
      exact Set.inter_eq_left.mp htrace
    exact ⟨hh.1,hh.2.trans htconv⟩
lemma restrict_finite {K : Geometry.SimplicialComplex ℝ V} {P : Set V}
    (hP : RespectsSet K P) (hf : (restrictComplex K P).faces.Finite) :
    (restrictComplex (G g d K) P).faces.Finite := by
  have he : (restrictComplex (G g d K) P).faces =
      ⋃ t ∈ (restrictComplex K P).faces, (L g d t).faces := by
    ext s
    simp only [mem_iff g d K hP,Set.mem_iUnion,exists_prop]
  rw [he]
  exact hf.biUnion (fun t ht => ((spec g d K).2.2 t (show t ∈ K.faces from ht.1)).1)
def refine {K : Geometry.SimplicialComplex ℝ V} (T : Subdivision K) : Subdivision K where
  complex := G g d T.complex
  space_eq := (spec g d T.complex).2.1.trans T.space_eq
  carrier := by
    intro s hs
    obtain ⟨t,ht,hst⟩ := carrier g d T.complex hs
    obtain ⟨u,hu,htu⟩ := T.carrier t ht
    exact ⟨u,hu,hst.trans htu⟩
  respects := fun s hs => preserves g d T.complex (T.respects s hs)
  finite := fun s hs => restrict_finite g d (T.respects s hs) (T.finite s hs)
variable {X : Type} [TopologicalSpace X]
def refineFamily {K : Geometry.SimplicialComplex ℝ V} (T : SubdivisionFamily X K) :
    SubdivisionFamily X K where
  val := fun x => refine g d (T.val x)
  localConstancy := by
    intro s hs
    let F : Set (Finset V) → Set (Finset V) := fun A => ⋃ t ∈ A, (L g d t).faces
    have he (x : X) : (restrictComplex (refine g d (T.val x)).complex
        (convexHull ℝ (s : Set V))).faces = F
        ((restrictComplex (T.val x).complex (convexHull ℝ (s : Set V))).faces) := by
      ext u
      simp only [refine,mem_iff g d (T.val x).complex ((T.val x).respects s hs),F,Set.mem_iUnion,exists_prop]
    simp_rw [he]
    exact (T.localConstancy s hs).comp F
end
end OAI.BassTrace.Sparse.Cuts.Factory
end
section
namespace OAI.BassTrace.Sparse.OrbitForms
open Set
open scoped Classical BassTrace.Sparse
noncomputable section
variable {H I Y : Type} [Group H] [MulAction H Y] [IsCancelSMul H Y] [Fintype I]
variable (d : Data I Y) (k : H) (t : ℝ)

private def half (j : H × I) : Set (Y →₀ ℝ) := {p | form d j p ≤ t}
theorem transport_half (h : H) (i : I) : push k '' half d t (h,i) = half d t (k*h,i) := by
  ext p; constructor
  · rintro ⟨q,hq,rfl⟩; change form d (k*h,i) (push k q) ≤ t; rw [form_translate]; exact hq
  · intro hp; refine ⟨(push k).symm p, ?_, (push k).apply_symm_apply p⟩
    change form d (h,i) _ ≤ t
    rw [← form_translate d k h i, LinearEquiv.apply_symm_apply]; exact hp
theorem transport_arrangement (s : Finset (Y →₀ ℝ)) :
    ((relevant (H:=H) d s).image (half d t)).image (fun A => push k '' A) =
    (relevant (H:=H) d (s.map (push k).toEmbedding)).image (half d t) := by
  ext A; simp only [Finset.mem_image]; constructor
  · rintro ⟨_,⟨⟨h,i⟩,hj,rfl⟩,rfl⟩
    exact ⟨(k*h,i),(relevant_translate d k h i s).2 hj,(transport_half d k t h i).symm⟩
  · rintro ⟨⟨h,i⟩,hj,rfl⟩
    have hj' := (relevant_translate d k (k⁻¹*h) i s).1 (by simpa using hj)
    exact ⟨_,⟨_,hj',rfl⟩,by simpa using transport_half d k t (k⁻¹*h) i⟩
end
end OAI.BassTrace.Sparse.OrbitForms
end
section
namespace OAI.BassTrace.Sparse.Cuts.Factory
open Set Finset GlobalCut UniversalCuts
open scoped Classical
noncomputable section
variable (g : Target) {V J : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable (d : UniversalCuts V J) (K : Geometry.SimplicialComplex ℝ V)
lemma side {u} (hu : u ∈ (G g d K).faces) (j : J) :
    convexHull ℝ (u : Set V) ⊆ {x | d.form j x ≤ d.level j} ∨
    convexHull ℝ (u : Set V) ⊆ {x | d.level j ≤ d.form j x} := by
  obtain ⟨s,hs,h⟩ := (spec g d K).1 ▸ hu
  by_cases hj : j ∈ d.relevant s
  · exact ((spec g d K).2.2 s hs).2.2.2.2.1 u h _ _ (Finset.mem_image_of_mem _ hj)
  · left; intro x hx; change d.form j x ≤ _
    have he : (L g d s).space = convexHull ℝ (s : Set V) := ((spec g d K).2.2 s hs).2.1
    rw [d.vanish s j hj x (he ▸ (L g d s).convexHull_subset_space h hx)]; exact d.positive j
lemma marked_le (j : J) : IsMarked (G g d K) (K.space ∩ {x | d.form j x ≤ d.level j}) := by
  rw [← (show (G g d K).space = K.space from (spec g d K).2.1)]
  apply RespectsSet.isMarked; intro s hs
  rcases side g d K hs j with h|h
  · rw [Set.inter_eq_left.mpr h, Set.inter_eq_left.mpr ((subset_convexHull ℝ _).trans h)]
  · apply hull_inter_of_supporting_eq s _ _ (Set.Subset.refl _) (-d.form j) (-d.level j)
    · exact fun x hx => neg_le_neg (h hx)
    · ext x; apply and_congr_right; intro hx
      change d.form j x ≤ d.level j ↔ -(d.form j x) = -(d.level j)
      have hh := h hx; change d.level j ≤ d.form j x at hh; constructor <;> intro <;> linarith
lemma marked_eq (j : J) : IsMarked (G g d K) (K.space ∩ {x | d.form j x = d.level j}) := by
  rw [← (show (G g d K).space = K.space from (spec g d K).2.1)]
  apply RespectsSet.isMarked; intro s hs
  rcases side g d K hs j with h|h
  · exact convexHull_inter_supporting _ _ _ ((subset_convexHull ℝ _).trans h)
  · simpa only [LinearMap.neg_apply,neg_inj] using convexHull_inter_supporting (s : Set V) (-d.form j) (-d.level j) (fun x hx => neg_le_neg (h (subset_convexHull ℝ _ hx)))
lemma finer {K : Geometry.SimplicialComplex ℝ V} (T : Subdivision K) : Refines (refine g d T).complex T.complex := ⟨refine g d (.original T.complex),rfl⟩
lemma closedPatch_marked {S : Geometry.SimplicialComplex ℝ V} {P : Set V}
    (hP : IsMarked (G g d S) P) (A : Finset J) :
    IsMarked (G g d S) (d.closedPatch P A) := by
  have hh := hP.inter_iInter (I := A) (Q := fun j => {x | d.form j x ≤ d.level j})
    (fun j => by simpa only [(show (G g d S).space = S.space from (spec g d S).2.1)]
      using marked_le g d S j)
  convert hh using 1
  ext x
  simp only [closedPatch,Set.mem_inter_iff,Set.mem_ofPred_eq,Set.mem_iInter,Subtype.forall]
lemma spherePatch_marked {S : Geometry.SimplicialComplex ℝ V} {P : Set V}
    (hP : IsMarked (G g d S) P) (A : Finset J) :
    IsMarked (G g d S) (d.spherePatch P A) := by
  have hC := closedPatch_marked g d hP A
  have hh := hC.inter (IsMarked.iUnion (fun j : A => marked_eq g d S j))
  convert hh using 1
  ext x
  simp only [spherePatch,Set.mem_inter_iff,Set.mem_ofPred_eq,Set.mem_iUnion,Subtype.exists]
  constructor
  · rintro ⟨hx,j,hj,hh⟩
    exact ⟨hx,j,hj,(show (G g d S).space = S.space from (spec g d S).2.1) ▸ hC.subset_space hx,hh⟩
  · rintro ⟨hx,j,hj,_,hh⟩
    exact ⟨hx,j,hj,hh⟩
end
end OAI.BassTrace.Sparse.Cuts.Factory
end
section
open scoped Classical
namespace OAI.BassTrace.Sparse.Cuts.Factory
open UniversalCuts
noncomputable section
open Set
variable {V X I J : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [TopologicalSpace X] {K : Geometry.SimplicialComplex ℝ V}
variable (g : GlobalCut.Target) (d : UniversalCuts V J)
def thresholdStep (T B : SubdivisionFamily X K) (P : MarkedFamily T)
    (hb : ∀ x, Refines (B.val x).complex (T.val x).complex)
    (ρ : V → V → ℝ) (R t : ℝ) (f : I → V → ℝ)
    (patch : I → Set V) (A : I → Finset J)
    (hpatch : ∀ i, IsMarked K (patch i))
    (hsphere : ∀ i, K.space ∩ {p | f i p = t} = d.spherePatch (patch i) (A i))
    (hlevel : ∀ j, d.level j = t)
    (hgeneric : ∀ x F, F ∈ (T.val x).complex.faces → ∀ j, ∃ v ∈ F, d.form j v ≠ t)
    (hcont : ∀ i, ContinuousOn (f i) K.space)
    (hcover : ∀ p ∈ K.space, ∃ i, f i p < t)
    (htriangle : ∀ i p, p ∈ K.space → ∀ q, q ∈ K.space → ρ p q ≤ f i p + f i q)
    (ht : t ≤ R) : AdmissibleStep ρ R T P := by
  let S := refineFamily g d B
  have hfiner (x : X) : Refines (S.val x).complex (T.val x).complex :=
    (finer g d (B.val x)).trans (hb x)
  have hpatch' (x : X) (i : I) : IsMarked (S.val x).complex (patch i) := by
    exact (S.val x).preserves_marked (hpatch i)
  let W : Set V := ⋃ i, d.spherePatch (patch i) (A i)
  have hW (x : X) : IsMarked (S.val x).complex W :=
    IsMarked.iUnion fun i => spherePatch_marked g d (hpatch' x i) (A i)
  have hspace (x : X) : (T.val x).complex.space = K.space := (T.val x).space_eq
  have hP (x : X) : P.val x ⊆ K.space := by
    rw [← hspace x]
    exact (P.marked x).subset_space
  have hP' (x : X) : IsMarked (S.val x).complex (P.val x) :=
    (hfiner x).preserves_marked (P.marked x)
  let Z : MarkedFamily S := MarkedFamily.ofSets S (fun x => P.val x ∩ W)
    (fun x => (hP' x).inter (hW x)) (by
      intro s hs
      have hh := (P.set_localConstancy s hs).comp (fun Q => Q ∩ W)
      convert hh using 1
      ext x p
      simp only [Function.comp_apply,Set.mem_inter_iff]
      tauto)
  refine { next := S
           finer := hfiner
           oldMarked := hP'
           zero := Z
           subset := fun _ => Set.inter_subset_left
           dimensionDrop := ?_
           diameter := ?_ }
  · intro x F hF hFP E hE hEF
    let L := fun j : J => (B.val x).complex.space ∩ {p | d.form j p = d.level j}
    have hm (j) : IsMarked (S.val x).complex (L j) := marked_eq g d (B.val x).complex j
    obtain ⟨j,hj⟩ := IsMarked.face_in_union hm hE (by
      intro p hp
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp (hEF hp).2.2
      obtain ⟨j,_,he⟩ := hi.2
      exact Set.mem_iUnion.mpr ⟨j,(B.val x).space_eq.symm ▸ hP x (hEF hp).2.1,he⟩)
    apply card_lt_of_generic_hyperplane ((S.val x).complex.indep hE)
      ((subset_convexHull ℝ _).trans (fun p h => (hEF h).1)) (d.form j) t
      (fun p h => ((hj (subset_convexHull ℝ _ h)).2).trans (hlevel j)) (hgeneric x F hF j)
  · intro x
    have he : P.val x ∩ W = P.val x ∩ ⋃ i, {p | f i p = t} := by
      ext p
      simp only [W,Set.mem_inter_iff,Set.mem_iUnion]
      constructor
      · rintro ⟨hp,i,hi⟩
        exact ⟨hp,i,((hsphere i).symm ▸ hi).2⟩
      · rintro ⟨hp,i,hi⟩
        exact ⟨hp,i,(hsphere i) ▸ ⟨hP x hp,hi⟩⟩
    change ComponentDiameter ρ (P.val x \ (P.val x ∩ W)) (2*R)
    rw [he]
    exact sphereUnion_componentDiameter ρ (P.val x) (hP x) f t R hcont hcover htriangle ht
def replacementStep (T : SubdivisionFamily X K) (P : MarkedFamily T)
    (ρ : V → V → ℝ) (R t : ℝ) (old : AdmissibleStep ρ R T P)
    (f : I → V → ℝ) (patch : I → Set V) (A : I → Finset J)
    (B : I → Set X) (hB : ∀ i, IsClopen (B i))
    (hpatch : ∀ i, IsMarked K (patch i))
    (hsphere : ∀ i, K.space ∩ {p | f i p=t} = d.spherePatch (patch i) (A i))
    (hlevel : ∀ j, d.level j=t)
    (hgeneric : ∀ x F, F ∈ (T.val x).complex.faces → ∀ j, ∃ v ∈ F, d.form j v≠t)
    (hfinU : ∀ s ∈ K.faces,
      {i | ({p | f i p<t} ∩ convexHull ℝ (s : Set V)).Nonempty}.Finite)
    (hfinS : ∀ s ∈ K.faces,
      {i | (d.spherePatch (patch i) (A i) ∩ convexHull ℝ (s : Set V)).Nonempty}.Finite)
    (hcont : ∀ i, ContinuousOn (f i) K.space)
    (htriangle : ∀ i, ∀ p ∈ K.space, ∀ q ∈ K.space, ρ p q≤f i p+f i q)
    (ht : t≤R) : { A : AdmissibleStep ρ R T P // ∀ x, A.zero.val x = replacementSet (P.val x) (old.zero.val x)
      (fun i => {p | f i p<t}) (fun i => {p | f i p=t}) B x } := by
  let S := refineFamily g d old.next
  have hS (x : X) : Refines (S.val x).complex (old.next.val x).complex :=
    finer g d (old.next.val x)
  have hST (x : X) : Refines (S.val x).complex (T.val x).complex :=
    (hS x).trans (old.finer x)
  let P' := P.refine hST
  let Z' := old.zero.refine hS
  have hpatch' (x : X) (i : I) : IsMarked (S.val x).complex (patch i) :=
    (S.val x).preserves_marked (hpatch i)
  have hSph (x : X) (i : I) : IsMarked (S.val x).complex
      (d.spherePatch (patch i) (A i)) := spherePatch_marked g d (hpatch' x i) (A i)
  have hU (x : X) (i : I) : IsMarked (S.val x).complex
      ((S.val x).complex.space \ {p | f i p<t}) := by
    apply IsMarked.superlevel (f i) t
    · simpa only [(S.val x).space_eq] using hcont i
    · rw [(S.val x).space_eq, hsphere i]
      exact hSph x i
  let Z := P'.replacement Z' (fun i => {p | f i p<t})
    (fun i => d.spherePatch (patch i) (A i)) B hB hU hSph hfinU hfinS
  have hP (x : X) : P.val x ⊆ K.space := by
    rw [← (T.val x).space_eq]
    exact (P.marked x).subset_space
  have hZeq (x : X) : Z.val x = replacementSet (P.val x) (old.zero.val x)
      (fun i => {p | f i p<t}) (fun i => {p | f i p=t}) B x := by
    change replacementSet (P.val x) (old.zero.val x) _ _ _ _ = _
    unfold replacementSet activatedUnion
    ext p
    simp only [Set.mem_union,Set.mem_sdiff,Set.mem_inter_iff,Set.mem_iUnion]
    constructor
    · rintro (hp | ⟨hp,i,hi⟩)
      · exact Or.inl hp
      · apply Or.inr
        refine ⟨hp,i,?_⟩
        by_cases hix : x ∈ B i
        · simp only [hix,ite_true] at hi ⊢
          exact ((hsphere i).symm ▸ hi).2
        · simpa only [hix,ite_false] using hi
    · rintro (hp | ⟨hp,i,hi⟩)
      · exact Or.inl hp
      · apply Or.inr
        refine ⟨hp,i,?_⟩
        by_cases hix : x ∈ B i
        · simp only [hix,ite_true] at hi ⊢
          exact hsphere i ▸ ⟨hP x hp,hi⟩
        · simpa only [hix,ite_false] using hi
  refine ⟨{ next := S
            finer := hST
            oldMarked := fun x => (hST x).preserves_marked (P.marked x)
            zero := Z
            subset := fun x => replacementSet_subset (old.subset x) _ _ B x
            dimensionDrop := ?_
            diameter := ?_ }, hZeq⟩
  · intro x
    apply ((old.dimensionDrop x).refine (old.zero.marked x) (hS x) (old.finer x)).union_levels
      (Z'.marked x) d.form d.level
    · intro j
      have hh := marked_eq g d (old.next.val x).complex j
      change IsMarked (S.val x).complex
        ((old.next.val x).complex.space ∩ {p | d.form j p=d.level j}) at hh
      simpa only [(old.next.val x).space_eq,← (S.val x).space_eq] using hh
    · intro F hF j
      simpa only [hlevel j] using hgeneric x F hF j
    · intro p hp
      change p ∈ replacementSet (P.val x) (old.zero.val x) _ _ _ _ at hp
      rcases hp with hp | ⟨hp,hi⟩
      · exact Or.inl hp.1
      · obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hi
        apply Or.inr
        by_cases hix : x ∈ B i
        · simp only [hix,ite_true] at hi
          obtain ⟨j,hj,he⟩ := hi.2
          exact Set.mem_iUnion.mpr ⟨j,(S.val x).space_eq.symm ▸ hP x hp,he⟩
        · simp only [hix,ite_false,Set.mem_empty_iff_false] at hi
  · intro x
    rw [hZeq x]
    exact replacement_componentDiameter ρ (P.val x) (old.zero.val x) f B x
      (hP x) (old.diameter x) hcont htriangle ht
end
end OAI.BassTrace.Sparse.Cuts.Factory
end
section
namespace OAI.BassTrace.Sparse.OrbitForms
open Set Cuts.Factory
open scoped Classical BassTrace.Sparse
noncomputable section
variable (g : GlobalCut.Target) {H I Y X : Type} [Group H] [MulAction H Y] [IsCancelSMul H Y] [Fintype I] [TopologicalSpace X] [MulAction H X]
variable (d : Data I Y) {K : Geometry.SimplicialComplex ℝ (Y →₀ ℝ)}
lemma cov (D : Cuts.UniversalCuts (Y →₀ ℝ) (H × I)) (r : ℝ)
    (hA : ∀ s, A D s = (relevant (H:=H) d s).image (fun j => {p | form d j p ≤ r}))
    (T : Cuts.SubdivisionFamily X K) (hT : Equivariant (H := H) T) :
    Equivariant (H := H) (refineFamily g D T) := by
  classical
  intro k x u hu
  let e := (finsuppRelabelIsometry (MulAction.toPerm k : Y ≃ Y)).toContinuousLinearEquiv
  have hx := spec g D (T.val x).complex
  obtain ⟨s,hs,h⟩ := hx.1 ▸ hu
  apply (spec g D (T.val (k • x)).complex).1.symm.subset
  refine ⟨_,hT k x s hs,?_⟩
  have ha : ((A D s).image (fun p => e '' p)) = A D (s.map (push k).toEmbedding) := by
    rw [hA,hA]; exact transport_arrangement d k r s
  have he := ((hx.2.2 s hs).2.2.2.2.2 e).symm.subset (Set.mem_image_of_mem _ h)
  rw [ha] at he; exact he
end
end OAI.BassTrace.Sparse.OrbitForms
end
section
namespace OAI
noncomputable section
namespace BassTrace
namespace Sparse.GraphGeometry
open Set Finset
open scoped BassTrace.Sparse Classical
section
variable {H Y C X : Type} [Group H] [MulAction H Y] [IsCancelSMul H Y]
  [Countable H] [Countable Y] [DecidableEq Y] [Fintype C]
  [TopologicalSpace X] [CompactSpace X] [MulAction H X]
variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)
variable [mY : MetricSpace Y] (hm : mY = graphMetric Γ hΓ)
variable {n : ℕ} (hn : 0<n) (K : PreAbstractSimplicialComplex Y)
variable (hK : ∀ s ∈ K.faces, ∃ σ ∈ K.faces, s ⊆ σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)
variable (hact : ∀ (h : H) s, s ∈ K.faces → s.map (MulAction.toPerm h).toEmbedding ∈ K.faces)
variable (hi : ∀ h : H, Isometry (fun y : Y => h • y))
include hm hn hK hact hi in
theorem factory_center (g : GlobalCut.Target)
    (T : Cuts.SubdivisionFamily X (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (P : Cuts.MarkedFamily T) (hT : OrbitForms.Equivariant (H := H) T)
    (hP : OrbitForms.MarkedEquivariant (H := H) P)
    (c : C → FinProbability Y) {R : ℝ} (hR : 0<R)
    (hcover : ∀ p : FinProbability Y, p.coeff.support ∈ K.faces →
      ∃ h : H, ∃ i : C, FinProbability.rho n p (h • c i) < R/2) :
    ∃ A : Cuts.AdmissibleStep (realizationDistance Γ hΓ K n) R T P,
      OrbitForms.Equivariant (H := H) A.next ∧
      OrbitForms.MarkedEquivariant (H := H) A.zero := by
  subst mY
  let := graphMetric Γ hΓ
  let S := fun i => ballSupport Γ (c i) n R
  let d := BallOrbitForms.data S c n
  let W := OrbitForms.winnerCuts (H := H) d
  let B := Cuts.Factory.refineFamily g W T
  obtain ⟨t,ht,hgen⟩ := Cuts.Sequential.uniformRadius T B (onFinsupp_faces_countable K)
    (fun j : H × BallOrbitForms.Index S => OrbitForms.form d j) (by linarith : R/2<R)
  have ht0 : 0<t := lt_trans (by linarith) ht.1
  let D := OrbitForms.cuts (H := H) d ht0
  let A : Cuts.AdmissibleStep (realizationDistance Γ hΓ K n) R T P := by
    refine Cuts.Factory.thresholdStep g D T B P (fun x => Cuts.Factory.finer g W (T.val x)) (realizationDistance Γ hΓ K n) R t
      (fun i : H × C => centerDistance Γ hΓ K n (i.1 • c i.2))
      (fun i : H × C => BallOrbitForms.translatedPatch S K i.1 i.2)
      (fun i : H × C => BallOrbitForms.branches S i.1 i.2)
      (fun i => BallOrbitForms.translatedPatch_marked S K i.1 i.2)
      (fun i => sphere_eq_patch Γ hΓ rfl hn K hK hact hi c i.1 i.2 hR.le ht0 ht.2.le)
      (fun _ => rfl) ?_ ?_ ?_ ?_ ht.2.le
    · intro x F hF j
      obtain ⟨v,hv⟩ := (T.val x).complex.nonempty_of_mem_faces hF
      exact ⟨v,hv,hgen x j v (Or.inl ((T.val x).complex.down_closed hF (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty _)))⟩
    · intro i
      apply continuousOn_centerDistance Γ hΓ hn K
        (fun s hs => by obtain ⟨σ,hσ,hsσ,hcard,_⟩ := hK s hs; exact ⟨σ,hσ,hsσ,hcard⟩)
      intro σ hσ
      obtain ⟨τ,_,hστ,hτ,hconn⟩ := hK σ hσ.1
      have hσcard : σ.card=n+1 := hσ.2
      have he : σ=τ := Finset.eq_of_subset_of_card_le hστ (by omega)
      rw [he]
      exact hconn
    · intro v hv
      let p := pointProbability K ⟨v,hv⟩
      obtain ⟨h,i,hpi⟩ := hcover p (pointProbability_face K ⟨v,hv⟩)
      refine ⟨(h,i),?_⟩
      change centerDistance Γ hΓ K n (h • c i) v < t
      have he : p.coeff = v := pointProbability_coeff K ⟨v,hv⟩
      rw [← he, centerDistance_apply Γ hΓ K n _ _ (pointProbability_face K ⟨v,hv⟩)]
      rw [FinProbability.rho_comm n (h • c i) p]
      exact hpi.trans ht.1
    · intro i p hp q hq
      exact realizationDistance_center_triangle Γ hΓ K n (i.1 • c i.2) p hp q hq
  refine ⟨A,OrbitForms.cov g d D t (fun _ => rfl) B (OrbitForms.cov g (OrbitForms.comparisons d) W 0 (fun _ => rfl) T hT),?_⟩
  intro k x v hv
  change OrbitForms.push k v ∈ P.val (k • x) ∩
    ⋃ i : H × C, D.spherePatch (BallOrbitForms.translatedPatch S K i.1 i.2)
      (BallOrbitForms.branches S i.1 i.2)
  have hv' : v ∈ P.val x ∩
    ⋃ i : H × C, D.spherePatch (BallOrbitForms.translatedPatch S K i.1 i.2)
      (BallOrbitForms.branches S i.1 i.2) := hv
  obtain ⟨hPv,hv''⟩ := hv'
  obtain ⟨i,hi'⟩ := Set.mem_iUnion.mp hv''
  have hsp (j : H × C) := sphere_eq_patch Γ hΓ rfl hn K hK hact hi c
    j.1 j.2 hR.le ht0 ht.2.le
  have hvK := (hsp i).symm ▸ hi'
  refine ⟨hP k x v hPv,Set.mem_iUnion.mpr ⟨(k*i.1,i.2),?_⟩⟩
  rw [← hsp (k*i.1,i.2)]
  refine ⟨space_push K hact k v hvK.1,?_⟩
  change centerDistance Γ hΓ K n ((k*i.1) • c i.2) (OrbitForms.push k v) = t
  rw [mul_smul,centerDistance_push K hact Γ hΓ hi n k (i.1 • c i.2) v hvK.1]
  exact hvK.2
end
variable {H Y X : Type} [Group H] [MulAction H Y] [IsCancelSMul H Y]
  [Countable H] [Countable Y] [DecidableEq Y]
  [TopologicalSpace X] [CompactSpace X] [MulAction H X]
variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)
variable [mY : MetricSpace Y] (hm : mY = graphMetric Γ hΓ)
variable {n : ℕ} (hn : 0<n) (K : PreAbstractSimplicialComplex Y)
variable (hK : ∀ s ∈ K.faces, ∃ σ ∈ K.faces, s ⊆ σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)
variable (hact : ∀ (h : H) s, s ∈ K.faces → s.map (MulAction.toPerm h).toEmbedding ∈ K.faces)
variable (hi : ∀ h : H, Isometry (fun y : Y => h • y))
include hm hn hK hact hi in
theorem factory_exists_admissibleStep (g : GlobalCut.Target)
    (F : Finset (Finset Y)) (hF : ∀ s ∈ F, s ∈ K.faces)
    (hrep : ∀ s ∈ K.faces, ∃ h : H, ∃ τ ∈ F, s = τ.map (MulAction.toPerm h).toEmbedding)
    (T : Cuts.SubdivisionFamily X (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (P : Cuts.MarkedFamily T) (hT : OrbitForms.Equivariant (H := H) T)
    (hP : OrbitForms.MarkedEquivariant (H := H) P)
    {R : ℝ} (hR : 0<R) :
    ∃ A : Cuts.AdmissibleStep (realizationDistance Γ hΓ K n) R T P,
      OrbitForms.Equivariant (H := H) A.next ∧
      OrbitForms.MarkedEquivariant (H := H) A.zero := by
  obtain ⟨C,_,hcov⟩ := exists_orbit_center_cover Γ hΓ hm hn K hi F hF hrep
    (by linarith : 0 < R/2)
  exact factory_center Γ hΓ hm hn K hK hact hi g T P hT hP
    (fun c : C => c.val) hR (by
      intro p hp
      obtain ⟨h,c,hc,hd⟩ := hcov p hp
      exact ⟨h,⟨c,hc⟩,hd⟩)
end Sparse.GraphGeometry
namespace Sparse.GraphGeometry
open Set Finset
open scoped BassTrace.Sparse Classical
variable {H Y C X : Type} [Group H] [MulAction H Y] [IsCancelSMul H Y]
  [Countable H] [Countable Y] [DecidableEq Y] [Fintype C]
  [TopologicalSpace X] [CompactSpace X] [MulAction H X] [ContinuousConstSMul H X]
variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)
variable [mY : MetricSpace Y] (hm : mY = graphMetric Γ hΓ)
variable {n : ℕ} (hn : 0<n) (K : PreAbstractSimplicialComplex Y)
variable (hK : ∀ s ∈ K.faces, ∃ σ ∈ K.faces, s ⊆ σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)
variable (hact : ∀ (h : H) s, s ∈ K.faces → s.map (MulAction.toPerm h).toEmbedding ∈ K.faces)
variable (hi : ∀ h : H, Isometry (fun y : Y => h • y))
include hm hn hK hact hi
omit [Countable H] [Countable Y] [CompactSpace X] in
theorem factory_exists_ball_replacement (g : GlobalCut.Target)
    (T : Cuts.SubdivisionFamily X (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
    (P : Cuts.MarkedFamily T)
    {R t : ℝ} (hR : 0<R) (ht : 0<t) (htR : t≤R)
    (old : Cuts.AdmissibleStep (realizationDistance Γ hΓ K n) R T P)
    (hT : OrbitForms.Equivariant (H := H) old.next)
    (hP : OrbitForms.MarkedEquivariant (H := H) P)
    (hZ : OrbitForms.MarkedEquivariant (H := H) old.zero)
    (c : C → FinProbability Y) (B : C → Set X) (hB : ∀ i, IsClopen (B i))
    (hgeneric : ∀ x F, F ∈ (T.val x).complex.faces →
      ∀ j : H × BallOrbitForms.Index (fun i => ballSupport Γ (c i) n R),
      ∃ v∈F, OrbitForms.form (BallOrbitForms.data (fun i => ballSupport Γ (c i) n R) c n) j v≠t) :
    ∃ A : Cuts.AdmissibleStep (realizationDistance Γ hΓ K n) R T P,
      OrbitForms.Equivariant (H := H) A.next ∧
      OrbitForms.MarkedEquivariant (H := H) A.zero ∧
      ∀ x, A.zero.val x = Cuts.replacementSet (P.val x) (old.zero.val x)
        (fun j : H × C => {v | centerDistance Γ hΓ K n (j.1 • c j.2) v<t})
        (fun j : H × C => {v | centerDistance Γ hΓ K n (j.1 • c j.2) v=t})
        (fun j : H × C => (fun x => j.1⁻¹ • x) ⁻¹' B j.2) x := by
  subst mY
  let := graphMetric Γ hΓ
  let S := fun i => ballSupport Γ (c i) n R
  let d := BallOrbitForms.data S c n
  let D := OrbitForms.cuts (H := H) d ht
  let f := fun j : H × C => centerDistance Γ hΓ K n (j.1 • c j.2)
  let patch := fun j : H × C => BallOrbitForms.translatedPatch S K j.1 j.2
  let branches := fun j : H × C => BallOrbitForms.branches S j.1 j.2
  let act := fun j : H × C => (fun x => j.1⁻¹ • x) ⁻¹' B j.2
  have hsphere (j : H × C) := sphere_eq_patch Γ hΓ rfl hn K hK hact hi c
    j.1 j.2 hR.le ht htR
  have hfin (s) (hs : s∈(Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).faces) :=
    finite_ball_incidence Γ hΓ rfl hn K hK hact hi c hR.le s hs
  let W := OrbitForms.winnerCuts (H := H) d
  let V := Cuts.Factory.refineFamily g W old.next
  have hw (x : X) := Cuts.Factory.finer g W (old.next.val x)
  let pre : Cuts.AdmissibleStep (realizationDistance Γ hΓ K n) R T P := {
    next := V, finer := fun x => (hw x).trans (old.finer x),
    oldMarked := fun x => (hw x).preserves_marked (old.oldMarked x),
    zero := old.zero.refine hw, subset := old.subset,
    dimensionDrop := fun x => (old.dimensionDrop x).refine (old.zero.marked x) (hw x) (old.finer x),
    diameter := old.diameter }
  let packed : { A : Cuts.AdmissibleStep (realizationDistance Γ hΓ K n) R T P // ∀ x,
      A.zero.val x = Cuts.replacementSet (P.val x) (old.zero.val x)
        (fun j => {v | f j v<t}) (fun j => {v | f j v=t}) act x } := by
    refine Cuts.Factory.replacementStep g D T P (realizationDistance Γ hΓ K n) R t pre
      f patch branches act (fun j => (hB j.2).preimage (continuous_const_smul j.1⁻¹))
      (fun j => BallOrbitForms.translatedPatch_marked S K j.1 j.2)
      hsphere (fun _ => rfl) hgeneric ?_ ?_ ?_ ?_ htR
    · intro s hs
      apply (hfin s hs).subset
      rintro j ⟨v,hv,hvs⟩
      exact ⟨v,hv.le.trans htR,hvs⟩
    · intro s hs
      apply (hfin s hs).subset
      rintro j ⟨v,hv,hvs⟩
      rw [← hsphere j] at hv
      refine ⟨v,?_,hvs⟩
      change centerDistance Γ hΓ K n (j.1 • c j.2) v ≤ R
      rw [hv.2]
      exact htR
    · intro j
      apply continuousOn_centerDistance Γ hΓ hn K
        (fun s hs => by obtain ⟨σ,hσ,hsσ,hcard,_⟩ := hK s hs; exact ⟨σ,hσ,hsσ,hcard⟩)
      intro σ hσ
      obtain ⟨τ,_,hστ,hτ,hconn⟩ := hK σ hσ.1
      have hσcard : σ.card=n+1 := hσ.2
      have he : σ=τ := Finset.eq_of_subset_of_card_le hστ (by omega)
      rw [he]
      exact hconn
    · intro j p hp q hq
      exact realizationDistance_center_triangle Γ hΓ K n (j.1 • c j.2) p hp q hq
  let A := packed.val
  have hPk (x : X) : P.val x ⊆ (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space := by
    rw [← (T.val x).space_eq]
    exact (P.marked x).subset_space
  have hval := packed.property
  refine ⟨A,?_,?_,hval⟩
  · change OrbitForms.Equivariant (H := H) (Cuts.Factory.refineFamily g D V)
    exact OrbitForms.cov g d D t (fun _ => rfl) V (OrbitForms.cov g (OrbitForms.comparisons d) W 0 (fun _ => rfl) old.next hT)
  intro k x v hv
  rw [hval x] at hv
  rw [hval (k • x)]
  have hfk (j : H × C) (hvK : v∈(Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space) :
      f (k*j.1,j.2) (OrbitForms.push k v)=f j v := by
    dsimp only [f]
    rw [mul_smul,centerDistance_push K hact Γ hΓ hi n k (j.1 • c j.2) v hvK]
  have hactk (j : H × C) : k • x∈act (k*j.1,j.2) ↔ x∈act j := by
    change (k*j.1)⁻¹ • (k • x)∈B j.2 ↔ j.1⁻¹ • x∈B j.2
    rw [mul_inv_rev,mul_smul,inv_smul_smul]
  rcases hv with hv | ⟨hp,hj⟩
  · refine Or.inl ⟨hZ k x v hv.1,?_⟩
    intro hh
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hh
    by_cases hjx : k • x∈act j
    · simp only [hjx,ite_true] at hj
      apply hv.2
      apply Set.mem_iUnion.mpr
      refine ⟨(k⁻¹*j.1,j.2),?_⟩
      have ha : x∈act (k⁻¹*j.1,j.2) := by
        change (k⁻¹*j.1)⁻¹ • x∈B j.2
        change j.1⁻¹ • (k • x)∈B j.2 at hjx
        simpa only [mul_inv_rev,inv_inv,mul_smul] using hjx
      simp only [ha,ite_true]
      have he := hfk (k⁻¹*j.1,j.2) (hPk x (old.subset x hv.1))
      simp only [mul_inv_cancel_left] at he
      change f j (OrbitForms.push k v)<t at hj
      change f (k⁻¹*j.1,j.2) v<t
      rw [← he]
      exact hj
    · simp only [hjx,ite_false,Set.mem_empty_iff_false] at hj
  · obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hj
    refine Or.inr ⟨hP k x v hp,Set.mem_iUnion.mpr ⟨(k*j.1,j.2),?_⟩⟩
    by_cases hjx : x∈act j
    · have hjkx := (hactk j).mpr hjx
      simp only [hjx,ite_true] at hj
      simp only [hjkx,ite_true]
      change f (k*j.1,j.2) (OrbitForms.push k v)=t
      rw [hfk j (hPk x hp)]
      exact hj
    · simp only [hjx,ite_false,Set.mem_empty_iff_false] at hj
end Sparse.GraphGeometry
end BassTrace
end
end OAI

end
section
namespace OAI
noncomputable section
namespace BassTrace
open Set MeasureTheory
open Finset MeasureTheory intervalIntegral
namespace Sparse.GraphGeometry
open Set Finset MeasureTheory
open scoped BassTrace.Sparse Classical ENNReal
section
variable {H Y X : Type} [Group H] [MulAction H Y] [DecidableEq Y] [Countable Y]
  [Countable H] [IsCancelSMul H Y]
  [TopologicalSpace X] [CompactSpace X] [MulAction H X] [ContinuousConstSMul H X]
variable (K : PreAbstractSimplicialComplex Y)
variable (hact : ∀ (h : H) s,s∈K.faces → s.map (MulAction.toPerm h).toEmbedding∈K.faces)
variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)
variable (hi : ∀ h : H,@Isometry Y Y (graphMetric Γ hΓ).toPseudoEMetricSpace
  (graphMetric Γ hΓ).toPseudoEMetricSpace (fun y=>h•y))
variable {n : ℕ} (hn : 0<n)
variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)
include hn hK hact hi in
theorem g_ae_exists_ball_step (g : GlobalCut.Target) {R : ℝ} (hR : 0<R)
    (Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K)
      (realizationDistance Γ hΓ K n) R n)
    {j : ℕ} (hj : j<n) (c : FinProbability Y) (B : Set X) (hB : IsClopen B) :
    ∀ᵐ t : ℝ, 0<t → t≤R →
      ∃ A : OrbitForms.EquivariantStep (realizationDistance Γ hΓ K n) R (Q.pair (j+1)),
        ∀ x,A.result.P.val x =
          ((Q.pair j).P.val x \ ⋃ h : H,activeWindow B (ballWindow K Γ hΓ (n := n) c (Iio t)) h x) ∪
          ((Q.pair (j+1)).P.val x ∩ ⋃ h : H,activeWindow B (ballWindow K Γ hΓ (n := n) c {t}) h x) := by
  let := graphMetric Γ hΓ
  let S (_ : Unit) := ballSupport Γ c n R
  let d := BallOrbitForms.data S (fun _ : Unit=>c) n
  have hfaces : (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).faces.Countable :=
    (Set.to_countable K.faces).image (fun s=>simplexVertices s)
  have hb := (Q.pair (j+1)).T.countable_exceptional_levels hfaces (fun k : H×BallOrbitForms.Index S => fun v=>OrbitForms.form d k v)
  have hae : ∀ᵐ t : ℝ,∀ x F,F∈((Q.pair (j+1)).T.val x).complex.faces →
      ∀ k y,y∈F → OrbitForms.form d k y≠t := ae_iff.mpr (hb.measure_zero volume)
  filter_upwards [hae] with t htgen
  intro ht htR
  obtain ⟨A,hA,hZ,hval⟩ := factory_exists_ball_replacement (g := g) Γ hΓ rfl hn K hK hact hi
    (Q.pair (j+1)).T (Q.pair (j+1)).P hR ht htR (Q.admissibleStep hj)
    (Q.pair j).equivariant (Q.pair (j+1)).markedEquivariant (Q.pair j).markedEquivariant
    (fun _ :Unit=>c) (fun _ :Unit=>B) (fun _=>hB) (by
      intro x F hF k
      obtain ⟨v,hv⟩ := ((Q.pair (j+1)).T.val x).complex.nonempty_of_mem_faces hF
      exact ⟨v,hv,htgen x F hF k v hv⟩)
  refine ⟨⟨A,hA,hZ⟩,fun x=>?_⟩
  change A.zero.val x=_
  rw [hval x]
  exact replacement_ballWindow K hact Γ hΓ hi n (Q.pair (j+1)) (Q.pair j) c B t x
end
end Sparse.GraphGeometry
namespace Sparse.GraphGeometry
open Set Finset MeasureTheory
open scoped BassTrace.Sparse Classical ENNReal
section
variable {H Y X : Type} [Group H] [MulAction H Y] [DecidableEq Y] [Countable Y]
  [Countable H] [IsCancelSMul H Y]
  [TopologicalSpace X] [CompactSpace X] [MulAction H X] [ContinuousConstSMul H X]
  [MeasurableSpace X] [BorelSpace X]
variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}
variable [hact : Fact (∀ (h : H) s,s∈K.faces → s.map (MulAction.toPerm h).toEmbedding∈K.faces)]
local instance : MulAction H (SourceTop K n) := sourceTopAction K n hact.out
local instance : Countable (SourceTop K n) := inferInstanceAs (Countable {s : Finset Y // s∈K.faces ∧ s.card=n+1})
local instance (σ : SourceTop K n) : Finite (MulAction.stabilizer H σ) :=
  finite_sourceTop_stabilizer K n hact.out σ
variable [Finite (MulAction.orbitRel.Quotient H (SourceTop K n))]
variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)
variable (hΓaut : ∀ (h : H) u v,Γ.Adj (h•u) (h•v) ↔ Γ.Adj u v)
variable (hi : ∀ h : H,@Isometry Y Y (graphMetric Γ hΓ).toPseudoEMetricSpace
  (graphMetric Γ hΓ).toPseudoEMetricSpace (fun y=>h•y))
variable (hn : 0<n)
variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)
include hi hn hK hΓaut in
theorem g_ae_open_ball_comparison (g : GlobalCut.Target) (μ : Measure X) [IsFiniteMeasure μ]
    (hμ : ∀ h : H,MeasurePreserving (fun x : X=>h•x) μ μ)
    {R ε : ℝ} (hR : 0<R) (hε : 0≤ε)
    (Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K)
      (realizationDistance Γ hΓ K n) R n)
    (hmin : Q.NearMinimal (realizationDistance Γ hΓ K n) R
      (fun d P=>(normalizedArea Γ μ (OrbitAreas.orbitReps (H := H) (T := SourceTop K n)) P d).toReal) ε)
    {j : ℕ} (hj : j<n) (c : FinProbability Y) (B : Set X) (hB : IsClopen B)
    (hdisj : ∀ x,Pairwise (fun h k : H=>Disjoint
      (activeWindow B (ballWindow K Γ hΓ (n := n) c (Iic R)) h x)
      (activeWindow B (ballWindow K Γ hΓ (n := n) c (Iic R)) k x))) :
    ∀ᵐ t : ℝ,0<t → t≤R →
      (∫⁻ x in B,∑' σ : SourceTop K n,localOriginalArea Γ (Q.pair j) σ j
        {v | centerDistance Γ hΓ K n c v<t} x ∂μ) ≤
      (∫⁻ x in B,∑' σ : SourceTop K n,localOriginalArea Γ (Q.pair (j+1)) σ j
        {v | centerDistance Γ hΓ K n c v=t} x ∂μ)+ENNReal.ofReal ε := by
  let : MeasurableSpace (Y →₀ ℝ) := borel (Y →₀ ℝ)
  let : BorelSpace (Y →₀ ℝ) := ⟨rfl⟩
  have hKn (s) (hs : s∈K.faces) : s.card≤n+1 := by
    obtain ⟨τ,hτ,hst,hcard,-⟩ := hK s hs
    exact (Finset.card_le_card hst).trans_eq hcard
  have hconn (σ : SourceTop K n) : (Γ.induce (σ.val : Set Y)).Connected := by
    obtain ⟨τ,hτ,hst,hcard,hct⟩ := hK σ.val σ.property.1
    have he : σ.val=τ := Finset.eq_of_subset_of_card_le hst (by rw [hcard,σ.property.2])
    exact he.symm ▸ hct
  let reps := OrbitAreas.orbitReps (H := H) (T := SourceTop K n)
  have hfinite := normalizedArea_filtration_lt_top Γ μ reps (fun σ _=>hconn σ) Q hKn hj.le
  filter_upwards [g_ae_exists_ball_step (g := g) K hact.out Γ hΓ hi hn hK hR Q hj c B hB] with t htgen
  intro ht htR
  obtain ⟨A,hnew⟩ := htgen ht htR
  have hfinite' := OrbitForms.normalizedArea_step_lt_top Γ μ reps (fun σ _=>hconn σ) Q hKn hj A
  have hgain := normalizedArea_surgery_gain (n := n) Γ hΓaut (Q.pair (j+1)) (Q.pair j) A.result
    μ hμ j B hB.isOpen.measurableSet
    (ballWindow K Γ hΓ (n := n) c (Iio t)) (ballWindow K Γ hΓ (n := n) c {t})
    (by
      intro x h
      unfold activeWindow
      split_ifs
      · rw [ballWindow_push K hact.out Γ hΓ hi n]
        exact measurable_ballWindow K Γ hΓ hn hK (h•c) (Iio t) measurableSet_Iio
      · exact MeasurableSet.empty)
    (by
      intro x h k hhk
      have hsub : ballWindow K Γ hΓ (n := n) c (Iio t)⊆ballWindow K Γ hΓ (n := n) c (Iic R) :=
        fun _ hp=>⟨hp.1,hp.2.le.trans htR⟩
      exact (hdisj x hhk).mono (activeWindow_mono hsub B h x) (activeWindow_mono hsub B k x)) hnew
  have hle := nearMinimum_local_comparison hfinite
    (ennreal_nearMinimum_of_real hfinite.ne hfinite'.ne hε (hmin j hj A)) hgain
  simpa only [localOriginalArea_ballWindow,Set.preimage,Set.mem_Iio,Set.mem_singleton_iff] using hle
end
end Sparse.GraphGeometry
namespace Sparse.GraphGeometry
open Set Finset MeasureTheory
open scoped BassTrace.Sparse Classical ENNReal
section
variable {H Y X : Type} [Group H] [MulAction H Y] [DecidableEq Y] [Countable Y]
  [Countable H] [IsCancelSMul H Y]
  [TopologicalSpace X] [CompactSpace X] [MulAction H X] [ContinuousConstSMul H X]
  [MeasurableSpace X] [BorelSpace X]
variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}
variable [hact : Fact (∀ (h : H) s,s∈K.faces → s.map (MulAction.toPerm h).toEmbedding∈K.faces)]
local instance : MulAction H (SourceTop K n) := sourceTopAction K n hact.out
local instance : Countable (SourceTop K n) := inferInstanceAs (Countable {s : Finset Y // s∈K.faces ∧ s.card=n+1})
local instance (σ : SourceTop K n) : Finite (MulAction.stabilizer H σ) :=
  finite_sourceTop_stabilizer K n hact.out σ
variable [Finite (MulAction.orbitRel.Quotient H (SourceTop K n))]
variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)
variable (hΓaut : ∀ (h : H) u v,Γ.Adj (h•u) (h•v) ↔ Γ.Adj u v)
variable (hi : ∀ h : H,@Isometry Y Y (graphMetric Γ hΓ).toPseudoEMetricSpace
  (graphMetric Γ hΓ).toPseudoEMetricSpace (fun y=>h•y))
variable (hn : 0<n)
variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)
include hi hn hK hΓaut in
theorem g_ballMass_recurrence (g : GlobalCut.Target) (μ : Measure X) [IsFiniteMeasure μ]
    (hμ : ∀ h : H,MeasurePreserving (fun x : X=>h•x) μ μ)
    {R ε : ℝ} (hR : 0<R) (hε : 0≤ε)
    (Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K)
      (realizationDistance Γ hΓ K n) R n)
    (hmin : Q.NearMinimal (realizationDistance Γ hΓ K n) R
      (fun d P=>(normalizedArea Γ μ (OrbitAreas.orbitReps (H := H) (T := SourceTop K n)) P d).toReal) ε)
    {j : ℕ} (hj : j<n) (c : FinProbability Y) (B : Set X) (hB : IsClopen B)
    (hdisj : ∀ x,Pairwise (fun h k : H=>Disjoint
      (activeWindow B (ballWindow K Γ hΓ (n := n) c (Iic R)) h x)
      (activeWindow B (ballWindow K Γ hΓ (n := n) c (Iic R)) k x)))
    (r b : ℝ) (hr : 0≤r) (hb : b≤R) :
    (∫⁻ t in Ioo r b,ballMass (n := n) Γ hΓ (Q.pair j) μ B j c t) ≤
      ballMass (n := n) Γ hΓ (Q.pair (j+1)) μ B (j+1) c b +
        ENNReal.ofReal ε * ENNReal.ofReal (b-r) := by
  have hcomp := g_ae_open_ball_comparison (g := g) Γ hΓ hΓaut hi hn hK μ hμ hR hε Q hmin hj c B hB hdisj
  have heq := ae_local_ball_closed_eq_open Γ hΓ hn hK (Q.pair j) j c
  have hlocal : ∀ᵐ t ∂volume.restrict (Ioo r b),
      ballMass (n := n) Γ hΓ (Q.pair j) μ B j c t ≤
      (∫⁻ x in B,∑' σ : SourceTop K n,localOriginalArea Γ (Q.pair (j+1)) σ j
        {v | centerDistance Γ hΓ K n c v=t} x ∂μ)+ENNReal.ofReal ε := by
    filter_upwards [ae_restrict_of_ae hcomp,ae_restrict_of_ae heq,
      ae_restrict_mem measurableSet_Ioo] with t ht he htb
    have hc := ht (hr.trans_lt htb.1) (htb.2.le.trans hb)
    simpa only [ballMass,he] using hc
  have hdim : ∀ x t,t∈((Q.pair (j+1)).T.val x).complex.faces →
      convexHull ℝ (t : Set (Y →₀ ℝ))⊆(Q.pair (j+1)).P.val x → t.card≤j+1+1 := by
    intro x t ht htp
    apply (Q.point x).dimension_bound _ (by omega) ht htp
    rintro _ ⟨s,hs,rfl⟩
    obtain ⟨τ,hτ,hst,hcard,-⟩ := hK s hs
    exact Finset.card_image_le.trans ((Finset.card_le_card hst).trans_eq hcard)
  have hco := integrated_marked_ball_coarea Γ hΓ (Q.pair (j+1)) μ B c hn
    (j+1) (by omega) hdim r b
  simp only [Nat.add_sub_cancel] at hco
  calc
    _ ≤ ∫⁻ t in Ioo r b, (∫⁻ x in B,∑' σ : SourceTop K n,
          localOriginalArea Γ (Q.pair (j+1)) σ j
            {v | centerDistance Γ hΓ K n c v=t} x ∂μ)+ENNReal.ofReal ε :=
      lintegral_mono_ae hlocal
    _ = (∫⁻ t in Ioo r b, ∫⁻ x in B,∑' σ : SourceTop K n,
          localOriginalArea Γ (Q.pair (j+1)) σ j
            {v | centerDistance Γ hΓ K n c v=t} x ∂μ) +
        ENNReal.ofReal ε * ENNReal.ofReal (b-r) := by
      rw [lintegral_add_right _ measurable_const,lintegral_const,
        Measure.restrict_apply_univ,Real.volume_Ioo]
    _ ≤ _ := add_le_add hco le_rfl
end
end Sparse.GraphGeometry
namespace Sparse.GraphGeometry
open Set Finset MeasureTheory
open scoped BassTrace.Sparse Classical ENNReal
section
variable {H Y X : Type} [Group H] [MulAction H Y] [DecidableEq Y] [Countable Y]
  [Countable H] [IsCancelSMul H Y]
  [TopologicalSpace X] [CompactSpace X] [MulAction H X] [ContinuousConstSMul H X]
  [MeasurableSpace X] [BorelSpace X]
variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}
variable [hact : Fact (∀ (h : H) s,s∈K.faces → s.map (MulAction.toPerm h).toEmbedding∈K.faces)]
local instance : MulAction H (SourceTop K n) := sourceTopAction K n hact.out
local instance : Countable (SourceTop K n) := inferInstanceAs (Countable {s : Finset Y // s∈K.faces ∧ s.card=n+1})
local instance (σ : SourceTop K n) : Finite (MulAction.stabilizer H σ) :=
  finite_sourceTop_stabilizer K n hact.out σ
variable [Finite (MulAction.orbitRel.Quotient H (SourceTop K n))]
variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)
variable (hΓaut : ∀ (h : H) u v,Γ.Adj (h•u) (h•v) ↔ Γ.Adj u v)
variable (hi : ∀ h : H,@Isometry Y Y (graphMetric Γ hΓ).toPseudoEMetricSpace
  (graphMetric Γ hΓ).toPseudoEMetricSpace (fun y=>h•y))
variable (hn : 0<n)
variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)
include hi hn hK hΓaut in
theorem g_iterated_ball_volume (g : GlobalCut.Target) (μ : Measure X) [IsFiniteMeasure μ]
    (hμ : ∀ h : H,MeasurePreserving (fun x : X=>h•x) μ μ)
    {R ε : ℝ} (hR : 0<R) (hε : 0≤ε)
    (Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K)
      (realizationDistance Γ hΓ K n) R n)
    (hmin : Q.NearMinimal (realizationDistance Γ hΓ K n) R
      (fun d P=>(normalizedArea Γ μ (OrbitAreas.orbitReps (H := H) (T := SourceTop K n)) P d).toReal) ε)
    (c : FinProbability Y) (hc : c.coeff.support.card≤n+1) (B : Set X) (hB : IsClopen B)
    (hdisj : ∀ x,Pairwise (fun h k : H=>Disjoint
      (activeWindow B (ballWindow K Γ hΓ (n := n) c (Iic R)) h x)
      (activeWindow B (ballWindow K Γ hΓ (n := n) c (Iic R)) k x)))
    (r : ℝ) (hr : 0≤r) (hrR : r≤R)
    (D : ℕ) (hD : 2≤D) (hdeg : ∀ v,Fintype.card (Γ.neighborSet v)≤D) :
    dividedPower n (R-r) * (ballMass (n := n) Γ hΓ (Q.pair 0) μ B 0 c r).toReal ≤
      ballVolumeBound D n R * (μ B).toReal + ε*slicingError n (R-r) := by
  have hdim j (hj : j≤n) x t (ht : t∈((Q.pair j).T.val x).complex.faces)
      (htp : convexHull ℝ (t : Set (Y →₀ ℝ))⊆(Q.pair j).P.val x) : t.card≤j+1 := by
    apply (Q.point x).dimension_bound _ hj ht htp
    rintro _ ⟨s,hs,rfl⟩
    obtain ⟨τ,_,hst,hcard,_⟩ := hK s hs
    exact Finset.card_image_le.trans ((Finset.card_le_card hst).trans_eq hcard)
  let M : ℕ → ℝ → ℝ≥0∞ := fun j=>
    ballMass (n := n) Γ hΓ (Q.pair (min j n)) μ B (min j n) c
  have hmono j : Monotone (M j) := ballMass_mono Γ hΓ _ _ _ _ _
  have hfin j t : M j t<∞ := by
    apply lt_of_le_of_lt (hmono j (le_max_left t 0))
    exact ballMass_lt_top Γ hΓ hn hK _ μ B _ (hdim _ (min_le_right _ _)) c
      (max t 0) (le_max_right _ _)
  have hstep j (hj : j<n) b (hb : b∈Icc r R) :
      (∫⁻ t in Ioo r b,M j t)≤M (j+1) b+ENNReal.ofReal ε*ENNReal.ofReal (b-r) := by
    simpa only [M,min_eq_left hj.le,min_eq_left (Nat.succ_le_iff.mpr hj)] using
      g_ballMass_recurrence (g := g) Γ hΓ hΓaut hi hn hK μ hμ hR hε Q hmin hj c B hB hdisj r b hr hb.2
  have ht := iterated_mass_bound M n r R ε hrR hε hmono hfin hstep
  have htop := ballMass_top_bound Γ hΓ hn hK (Q.pair n) μ B c hc R hR.le D hD hdeg
  have htop' := ENNReal.toReal_mono (by finiteness) htop
  have hv : (ballMass (n := n) Γ hΓ (Q.pair n) μ B n c R).toReal ≤
      ballVolumeBound D n R * (μ B).toReal := by
    simpa [ballVolumeBound,ENNReal.toReal_mul,ENNReal.toReal_add,div_eq_mul_inv] using htop'
  simp only [M,min_self,zero_min] at ht
  nlinarith
end
end Sparse.GraphGeometry
namespace Sparse.GraphGeometry
open Set Finset MeasureTheory
open scoped BassTrace.Sparse Classical ENNReal
section
variable {H Y X : Type} [Group H] [MulAction H Y] [DecidableEq Y] [Countable Y]
  [Countable H] [IsCancelSMul H Y]
  [TopologicalSpace X] [CompactSpace X] [MulAction H X] [ContinuousConstSMul H X]
  [MeasurableSpace X] [BorelSpace X]
variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}
variable [hact : Fact (∀ (h : H) s,s∈K.faces → s.map (MulAction.toPerm h).toEmbedding∈K.faces)]
local instance : MulAction H (SourceTop K n) := sourceTopAction K n hact.out
local instance : Countable (SourceTop K n) := inferInstanceAs (Countable {s : Finset Y // s∈K.faces ∧ s.card=n+1})
local instance (σ : SourceTop K n) : Finite (MulAction.stabilizer H σ) :=
  finite_sourceTop_stabilizer K n hact.out σ
variable [Finite (MulAction.orbitRel.Quotient H (SourceTop K n))]
variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)
variable (hΓaut : ∀ (h : H) u v,Γ.Adj (h•u) (h•v) ↔ Γ.Adj u v)
variable (hi : ∀ h : H,@Isometry Y Y (graphMetric Γ hΓ).toPseudoEMetricSpace
  (graphMetric Γ hΓ).toPseudoEMetricSpace (fun y=>h•y))
variable (hn : 0<n)
variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)
include hi hn hK hΓaut in
theorem g_zero_ball_mass_bound (g : GlobalCut.Target) (μ : Measure X) [IsFiniteMeasure μ]
    (hμ : ∀ h : H,MeasurePreserving (fun x : X=>h•x) μ μ)
    {R ε : ℝ} (hR : 0<R) (hε : 0≤ε)
    (Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K)
      (realizationDistance Γ hΓ K n) R n)
    (hmin : Q.NearMinimal (realizationDistance Γ hΓ K n) R
      (fun d P=>(normalizedArea Γ μ (OrbitAreas.orbitReps (H := H) (T := SourceTop K n)) P d).toReal) ε)
    (c : FinProbability Y) (hc : c.coeff.support.card≤n+1) (A : Set X) (hA : IsClopen A)
    (hdisj : ∀ x,Pairwise (fun h k : H=>Disjoint
      (activeWindow A (ballWindow K Γ hΓ (n := n) c (Iic R)) h x)
      (activeWindow A (ballWindow K Γ hΓ (n := n) c (Iic R)) k x)))
    (r : ℝ) (hr : 0≤r) (hrR : r≤R)
    (D : ℕ) (hD : 2≤D) (hdeg : ∀ v,Fintype.card (Γ.neighborSet v)≤D)
    (hmargin : ballVolumeBound D n R<dividedPower n (R-r)) :
    (ballMass (n := n) Γ hΓ (Q.pair 0) μ A 0 c r).toReal ≤
      slicingError n (R-r)/(dividedPower n (R-r)-ballVolumeBound D n R)*ε := by
  let f := ballIntegrand (n := n) Γ hΓ (Q.pair 0) 0 c r
  let S : Set X := {x | f x≠0}
  have hS : IsClopen S :=
    (ballIntegrand_locallyConstant Γ hΓ hn hK (Q.pair 0) 0 c r hr).isClopen_fiber 0 |>.compl
  let B := A∩S
  have hB : IsClopen B := hA.inter hS
  have hwin (h : H) (x : X) : activeWindow B (ballWindow K Γ hΓ (n := n) c (Iic R)) h x ⊆
      activeWindow A (ballWindow K Γ hΓ (n := n) c (Iic R)) h x := by
    unfold activeWindow
    split_ifs with hb ha
    · exact subset_rfl
    · exact False.elim (ha hb.1)
    · exact empty_subset _
    · exact subset_rfl
  have hdisjB x : Pairwise (fun h k : H=>Disjoint
      (activeWindow B (ballWindow K Γ hΓ (n := n) c (Iic R)) h x)
      (activeWindow B (ballWindow K Γ hΓ (n := n) c (Iic R)) k x)) :=
    fun h k hk=>(hdisj x hk).mono (hwin h x) (hwin k x)
  have he : ballMass (n := n) Γ hΓ (Q.pair 0) μ B 0 c r =
      ballMass (n := n) Γ hΓ (Q.pair 0) μ A 0 c r := by
    have hh := setLIntegral_eq_of_support_subset (μ := μ.restrict A) (s := S) (f := f)
      (show Function.support f⊆S from subset_rfl)
    rw [Measure.restrict_restrict hS.isClosed.measurableSet,inter_comm] at hh
    exact hh
  have hμle : μ B≤ballMass (n := n) Γ hΓ (Q.pair 0) μ B 0 c r := by
    calc
      _ = ∫⁻ _x in B,(1 : ℝ≥0∞) ∂μ := by simp
      _ ≤ _ := setLIntegral_mono' hB.isClosed.measurableSet fun x hx=>
        one_le_ballIntegrand_of_ne_zero Γ hΓ hK (Q.pair 0) c r x hx.2
  have hdim x t (ht : t∈((Q.pair 0).T.val x).complex.faces)
      (htp : convexHull ℝ (t : Set (Y →₀ ℝ))⊆(Q.pair 0).P.val x) : t.card≤0+1 := by
    apply (Q.point x).dimension_bound _ (Nat.zero_le n) ht htp
    rintro _ ⟨s,hs,rfl⟩
    obtain ⟨τ,_,hst,hcard,_⟩ := hK s hs
    exact Finset.card_image_le.trans ((Finset.card_le_card hst).trans_eq hcard)
  have hf := ballMass_lt_top Γ hΓ hn hK (Q.pair 0) μ B 0 hdim c r hr
  have hμle' := ENNReal.toReal_mono hf.ne hμle
  have hv := g_iterated_ball_volume (g := g) Γ hΓ hΓaut hi hn hK μ hμ hR hε Q hmin c hc
    B hB hdisjB r hr hrR D hD hdeg
  rw [he] at hμle' hv
  exact absorb_nonempty_probability _ _ _ _ _ _ hmargin
    (by unfold ballVolumeBound; positivity) hμle' hv
end
end Sparse.GraphGeometry
namespace Sparse.GraphGeometry
open Set Finset MeasureTheory
open scoped BassTrace.Sparse Classical ENNReal
section
variable {H Y X : Type} [Group H] [MulAction H Y] [DecidableEq Y] [Countable Y]
  [Countable H] [IsCancelSMul H Y]
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [TotallyDisconnectedSpace X]
  [MulAction H X] [ContinuousConstSMul H X] [IsCancelSMul H X]
  [MeasurableSpace X] [BorelSpace X]
variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}
variable [hact : Fact (∀ (h : H) s,s∈K.faces → s.map (MulAction.toPerm h).toEmbedding∈K.faces)]
local instance : MulAction H (SourceTop K n) := sourceTopAction K n hact.out
local instance : Countable (SourceTop K n) := inferInstanceAs (Countable {s : Finset Y // s∈K.faces ∧ s.card=n+1})
local instance (σ : SourceTop K n) : Finite (MulAction.stabilizer H σ) :=
  finite_sourceTop_stabilizer K n hact.out σ
variable [Finite (MulAction.orbitRel.Quotient H (SourceTop K n))]
variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)
variable (hΓaut : ∀ (h : H) u v,Γ.Adj (h•u) (h•v) ↔ Γ.Adj u v)
variable (hi : ∀ h : H,@Isometry Y Y (graphMetric Γ hΓ).toPseudoEMetricSpace
  (graphMetric Γ hΓ).toPseudoEMetricSpace (fun y=>h•y))
variable (hn : 0<n)
variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)
include hi hn hK hΓaut in
theorem g_global_zero_ball_mass_bound (g : GlobalCut.Target) (μ : Measure X) [IsFiniteMeasure μ]
    (hμ : ∀ h : H,MeasurePreserving (fun x : X=>h•x) μ μ)
    {R : ℝ} (hR : 0<R) (c : FinProbability Y) (hc : c.coeff.support.card≤n+1)
    (r : ℝ) (hr : 0≤r) (hrR : r≤R)
    (D : ℕ) (hD : 2≤D) (hdeg : ∀ v,Fintype.card (Γ.neighborSet v)≤D)
    (hmargin : ballVolumeBound D n R<dividedPower n (R-r)) :
    ∃ C : ℝ,0≤C ∧ ∀ (ε : ℝ),0≤ε →
      ∀ Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
        (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K)
        (realizationDistance Γ hΓ K n) R n,
      Q.NearMinimal (realizationDistance Γ hΓ K n) R
        (fun d P=>(normalizedArea Γ μ (OrbitAreas.orbitReps (H := H) (T := SourceTop K n)) P d).toReal) ε →
      (ballMass (n := n) Γ hΓ (Q.pair 0) μ univ 0 c r).toReal≤C*ε := by
  obtain ⟨m,A,hcover,hdisj,hactive⟩ := exists_disjoint_ball_partition (H := H) (X := X) Γ hΓ hn hK c hR.le
  let C := slicingError n (R-r)/(dividedPower n (R-r)-ballVolumeBound D n R)
  have hC : 0≤C := by
    apply div_nonneg _ (sub_pos.mpr hmargin).le
    apply Finset.sum_nonneg
    intro i _
    exact div_nonneg (pow_nonneg (sub_nonneg.mpr hrR) _) (Nat.cast_nonneg _)
  refine ⟨m*C,mul_nonneg (Nat.cast_nonneg _) hC,?_⟩
  intro ε hε Q hmin
  have hdim x t (ht : t∈((Q.pair 0).T.val x).complex.faces)
      (htp : convexHull ℝ (t : Set (Y →₀ ℝ))⊆(Q.pair 0).P.val x) : t.card≤0+1 := by
    apply (Q.point x).dimension_bound _ (Nat.zero_le n) ht htp
    rintro _ ⟨s,hs,rfl⟩
    obtain ⟨τ,_,hst,hcard,_⟩ := hK s hs
    exact Finset.card_image_le.trans ((Finset.card_le_card hst).trans_eq hcard)
  have hu : (⋃ i,(A i : Set X))=univ := Set.eq_univ_iff_forall.mpr fun x=>hcover (Set.mem_univ x)
  have he : ballMass (n := n) Γ hΓ (Q.pair 0) μ univ 0 c r=
      ∑ i : Fin m,ballMass (n := n) Γ hΓ (Q.pair 0) μ (A i : Set X) 0 c r := by
    unfold ballMass
    rw [← hu,lintegral_iUnion (fun i=>(A i).isClosed.measurableSet) hdisj,tsum_fintype]
  rw [he,ENNReal.toReal_sum (fun i _=>(ballMass_lt_top Γ hΓ hn hK (Q.pair 0) μ
    (A i : Set X) 0 hdim c r hr).ne)]
  calc
    _ ≤ ∑ _i : Fin m,C*ε := Finset.sum_le_sum fun i _=>
      g_zero_ball_mass_bound (g := g) Γ hΓ hΓaut hi hn hK μ hμ hR hε Q hmin c hc
        (A i : Set X) (A i).isClopen (hactive i) r hr hrR D hD hdeg hmargin
    _ = (m*C)*ε := by simp [mul_assoc]
end
end Sparse.GraphGeometry
namespace Sparse.GraphGeometry
open Set Finset MeasureTheory
open scoped BassTrace.Sparse Classical
section
variable {H Y X : Type} [Group H] [MulAction H Y] [IsCancelSMul H Y]
  [Countable H] [Countable Y] [DecidableEq Y]
  [TopologicalSpace X] [CompactSpace X] [MulAction H X]
  [MeasurableSpace X]
variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)
variable [mY : MetricSpace Y] (hm : mY = graphMetric Γ hΓ)
variable {n : ℕ} (hn : 0<n) (K : PreAbstractSimplicialComplex Y)
variable (hK : ∀ s ∈ K.faces, ∃ σ ∈ K.faces, s ⊆ σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)
variable (hact : ∀ (h : H) s, s ∈ K.faces → s.map (MulAction.toPerm h).toEmbedding ∈ K.faces)
variable (hi : ∀ h : H, Isometry (fun y : Y => h • y))
include hm hn hK hact hi in
theorem g_exists_normalized_nearMinimal (g : GlobalCut.Target)
    (F : Finset (Finset Y)) (hF : ∀ s ∈ F, s ∈ K.faces)
    (hrep : ∀ s ∈ K.faces, ∃ h : H, ∃ τ ∈ F, s = τ.map (MulAction.toPerm h).toEmbedding)
    (μ : Measure X) (reps : Finset (SourceTop K n))
    {R ε : ℝ} (hR : 0<R) (hε : 0<ε) :
    ∃ Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K)
      (realizationDistance Γ hΓ K n) R n,
      Q.NearMinimal (realizationDistance Γ hΓ K n) R
        (fun j P => (normalizedArea Γ μ reps P j).toReal) ε := by
  apply OrbitForms.exists_nearMinimal_filtration
    (realizationDistance Γ hΓ K n) R (originalMarkedPair K hact)
    (fun _ => rfl) (fun _ => rfl)
  · intro Q
    obtain ⟨A,hA,hP⟩ := factory_exists_admissibleStep (g := g) Γ hΓ hm hn K hK hact hi F hF hrep
      Q.T Q.P Q.equivariant Q.markedEquivariant hR
    exact ⟨⟨A,hA,hP⟩⟩
  · exact fun _ _ => ENNReal.toReal_nonneg
  · exact hε
end
end Sparse.GraphGeometry
namespace Sparse.GraphGeometry
open Set Finset MeasureTheory
open scoped BassTrace.Sparse Classical ENNReal
section
variable {H Y X : Type} [Group H] [MulAction H Y] [DecidableEq Y] [Countable Y]
  [Countable H] [IsCancelSMul H Y]
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [TotallyDisconnectedSpace X]
  [MulAction H X] [ContinuousConstSMul H X] [IsCancelSMul H X]
  [MeasurableSpace X] [BorelSpace X]
variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}
variable [hact : Fact (∀ (h : H) s,s∈K.faces → s.map (MulAction.toPerm h).toEmbedding∈K.faces)]
local instance : MulAction H (SourceTop K n) := sourceTopAction K n hact.out
local instance : Countable (SourceTop K n) := inferInstanceAs (Countable {s : Finset Y // s∈K.faces ∧ s.card=n+1})
local instance (σ : SourceTop K n) : Finite (MulAction.stabilizer H σ) :=
  finite_sourceTop_stabilizer K n hact.out σ
variable [Finite (MulAction.orbitRel.Quotient H (SourceTop K n))]
variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)
variable (hΓaut : ∀ (h : H) u v,Γ.Adj (h•u) (h•v) ↔ Γ.Adj u v)
variable (hi : ∀ h : H,@Isometry Y Y (graphMetric Γ hΓ).toPseudoEMetricSpace
  (graphMetric Γ hΓ).toPseudoEMetricSpace (fun y=>h•y))
variable (hn : 0<n)
variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)
local instance : MeasurableSpace (Y →₀ ℝ) := borel (Y →₀ ℝ)
local instance : BorelSpace (Y →₀ ℝ) := ⟨rfl⟩
include hi hn hK hΓaut in
theorem g_expected_zero_count_bound (g : GlobalCut.Target) (μ : Measure X) [IsFiniteMeasure μ]
    (hμ : ∀ h : H,MeasurePreserving (fun x : X=>h•x) μ μ)
    (D : ℕ) (hD : 2≤D) (hdeg : ∀ v,Fintype.card (Γ.neighborSet v)≤D)
    (hlarge : volumeThreshold D≤n) (σ : SourceTop K n) :
    ∃ C : ℝ,0≤C ∧ ∀ (ε : ℝ),0≤ε →
      ∀ Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
        (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K)
        (realizationDistance Γ hΓ K n) (4*(D : ℝ)^2) n,
      Q.NearMinimal (realizationDistance Γ hΓ K n) (4*(D : ℝ)^2)
        (fun d P=>(normalizedArea Γ μ (OrbitAreas.orbitReps (H := H) (T := SourceTop K n)) P d).toReal) ε →
      (∫⁻ x,Measure.count ((Q.pair 0).P.val x∩
        convexHull ℝ (simplexVertices σ.val : Set (Y →₀ ℝ))) ∂μ).toReal≤C*ε := by
  have hDp : 0<(D : ℝ) := by exact_mod_cast (show 0<D by omega)
  have hRp : 0<4*(D : ℝ)^2 := by positivity
  have hrp : 0<2*(D : ℝ)^2 := by positivity
  have hrR : 2*(D : ℝ)^2≤4*(D : ℝ)^2 := by nlinarith [sq_nonneg (D : ℝ)]
  obtain ⟨T,hT,hcover⟩ := exists_finite_simplex_ball_cover Γ hΓ hn σ hrp
  have hc : ∀ c∈T,c.coeff.support.card≤n+1 := fun c hc=>
    (Finset.card_le_card (hT c hc)).trans_eq σ.property.2
  have hh : ∀ c : T,∃ C : ℝ,0≤C ∧ ∀ (ε : ℝ),0≤ε →
      ∀ Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
        (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K)
        (realizationDistance Γ hΓ K n) (4*(D : ℝ)^2) n,
      Q.NearMinimal (realizationDistance Γ hΓ K n) (4*(D : ℝ)^2)
        (fun d P=>(normalizedArea Γ μ (OrbitAreas.orbitReps (H := H) (T := SourceTop K n)) P d).toReal) ε →
      (ballMass (n := n) Γ hΓ (Q.pair 0) μ univ 0 c.val (2*(D : ℝ)^2)).toReal≤C*ε :=
    fun c=>g_global_zero_ball_mass_bound (g := g) Γ hΓ hΓaut hi hn hK μ hμ hRp c.val
      (hc c.val c.property) _ hrp.le hrR D hD hdeg (ballVolume_strict_margin D n hD hlarge)
  choose C hC hbound using hh
  refine ⟨∑ c : T,C c,Finset.sum_nonneg (fun c _=>hC c),?_⟩
  intro ε hε Q hmin
  have hdim x t (ht : t∈((Q.pair 0).T.val x).complex.faces)
      (htp : convexHull ℝ (t : Set (Y →₀ ℝ))⊆(Q.pair 0).P.val x) : t.card≤0+1 := by
    apply (Q.point x).dimension_bound _ (Nat.zero_le n) ht htp
    rintro _ ⟨s,hs,rfl⟩
    obtain ⟨τ,_,hst,hcard,_⟩ := hK s hs
    exact Finset.card_image_le.trans ((Finset.card_le_card hst).trans_eq hcard)
  have hf c : ballMass (n := n) Γ hΓ (Q.pair 0) μ univ 0 c (2*(D : ℝ)^2)<⊤ :=
    ballMass_lt_top Γ hΓ hn hK (Q.pair 0) μ univ 0 hdim c _ hrp.le
  have hp x : Measure.count ((Q.pair 0).P.val x∩
        convexHull ℝ (simplexVertices σ.val : Set (Y →₀ ℝ)))≤
      ∑ c : T,ballIntegrand (n := n) Γ hΓ (Q.pair 0) 0 c.val (2*(D : ℝ)^2) x := by
    have hsub : (Q.pair 0).P.val x∩
        convexHull ℝ (simplexVertices σ.val : Set (Y →₀ ℝ))⊆
        ⋃ c : T,(Q.pair 0).P.val x∩{v | centerDistance Γ hΓ K n c.val v≤2*(D : ℝ)^2} := by
      rintro v ⟨hv,hs⟩
      obtain ⟨c,hc,hcv⟩ := hcover v hs
      exact Set.mem_iUnion.mpr ⟨⟨c,hc⟩,hv,hcv⟩
    exact (measure_mono hsub).trans ((measure_iUnion_fintype_le _ _).trans
      (Finset.sum_le_sum fun c _=>zero_count_ball_le Γ hΓ hK Q x c.val _))
  have hint : (∫⁻ x,Measure.count ((Q.pair 0).P.val x∩
        convexHull ℝ (simplexVertices σ.val : Set (Y →₀ ℝ))) ∂μ)≤
      ∑ c : T,ballMass (n := n) Γ hΓ (Q.pair 0) μ univ 0 c.val (2*(D : ℝ)^2) := by
    apply (lintegral_mono hp).trans_eq
    rw [lintegral_finsetSum _ (fun c _=>(ballIntegrand_locallyConstant Γ hΓ hn hK
      (Q.pair 0) 0 c.val _ hrp.le).continuous.measurable)]
    apply Finset.sum_congr rfl
    intro c _
    simp only [ballMass,Measure.restrict_univ,ballIntegrand]
  calc
    _ ≤ (∑ c : T,ballMass (n := n) Γ hΓ (Q.pair 0) μ univ 0 c.val (2*(D : ℝ)^2)).toReal :=
      ENNReal.toReal_mono (by simp [ne_of_lt (hf _)]) hint
    _ = ∑ c : T,(ballMass (n := n) Γ hΓ (Q.pair 0) μ univ 0 c.val (2*(D : ℝ)^2)).toReal :=
      ENNReal.toReal_sum (fun c _=>(hf c.val).ne)
    _ ≤ ∑ c : T,C c*ε := Finset.sum_le_sum fun c _=>hbound c ε hε Q hmin
    _ = (∑ c : T,C c)*ε := (Finset.sum_mul ..).symm
end
end Sparse.GraphGeometry
namespace Sparse.GraphGeometry
open Set Finset MeasureTheory
open scoped BassTrace.Sparse Classical ENNReal
section
variable {H Y X : Type} [Group H] [MulAction H Y] [DecidableEq Y] [Countable Y]
  [Countable H] [IsCancelSMul H Y]
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [TotallyDisconnectedSpace X]
  [MulAction H X] [ContinuousConstSMul H X] [IsCancelSMul H X]
  [MeasurableSpace X] [BorelSpace X]
variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}
variable [hact : Fact (∀ (h : H) s,s∈K.faces → s.map (MulAction.toPerm h).toEmbedding∈K.faces)]
local instance : MulAction H (SourceTop K n) := sourceTopAction K n hact.out
local instance : Countable (SourceTop K n) := inferInstanceAs (Countable {s : Finset Y // s∈K.faces ∧ s.card=n+1})
local instance (σ : SourceTop K n) : Finite (MulAction.stabilizer H σ) :=
  finite_sourceTop_stabilizer K n hact.out σ
variable [Finite (MulAction.orbitRel.Quotient H (SourceTop K n))]
variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)
variable (hΓaut : ∀ (h : H) u v,Γ.Adj (h•u) (h•v) ↔ Γ.Adj u v)
variable (hi : ∀ h : H,@Isometry Y Y (graphMetric Γ hΓ).toPseudoEMetricSpace
  (graphMetric Γ hΓ).toPseudoEMetricSpace (fun y=>h•y))
variable (hn : 0<n)
variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)
local instance : MeasurableSpace (Y →₀ ℝ) := borel (Y →₀ ℝ)
local instance : BorelSpace (Y →₀ ℝ) := ⟨rfl⟩
include hi hn hK hΓaut in
theorem g_exists_sparse_zero_strata (g : GlobalCut.Target) (μ : Measure X) [IsFiniteMeasure μ]
    (hμ : ∀ h : H,MeasurePreserving (fun x : X=>h•x) μ μ)
    (D : ℕ) (hD : 2≤D) (hdeg : ∀ v,Fintype.card (Γ.neighborSet v)≤D)
    (hlarge : volumeThreshold D≤n)
    (F : Finset (Finset Y)) (hF : ∀ s∈F,s∈K.faces)
    (hrep : ∀ s∈K.faces,∃ h : H,∃ τ∈F,s=τ.map (MulAction.toPerm h).toEmbedding) :
    ∃ C : SourceTop K n → ℝ,(∀ σ,0≤C σ) ∧ ∀ ε : ℝ,0<ε →
      ∃ Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
        (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K)
        (realizationDistance Γ hΓ K n) (4*(D : ℝ)^2) n,
      ∀ σ : SourceTop K n,
        (∫ x,(Measure.count ((Q.pair 0).P.val x∩
          convexHull ℝ (simplexVertices σ.val : Set (Y →₀ ℝ)))).toReal ∂μ)≤C σ*ε := by
  have hall := g_expected_zero_count_bound (g := g) Γ hΓ hΓaut hi hn hK μ hμ D hD hdeg hlarge
  choose C hC hbound using hall
  refine ⟨C,hC,?_⟩
  intro ε hε
  let := graphMetric Γ hΓ
  have hDp : 0<(D : ℝ) := by exact_mod_cast (show 0<D by omega)
  have hRp : 0<4*(D : ℝ)^2 := by positivity
  obtain ⟨Q,hQ⟩ := g_exists_normalized_nearMinimal (g := g) Γ hΓ rfl hn K hK hact.out hi
    F hF hrep μ (OrbitAreas.orbitReps (H := H) (T := SourceTop K n)) hRp hε
  refine ⟨Q,?_⟩
  intro σ
  have hmeas : Measurable (fun x=>Measure.count ((Q.pair 0).P.val x∩
      convexHull ℝ (simplexVertices σ.val : Set (Y →₀ ℝ)))) :=
    (((Q.pair 0).P.localConstancy_inter (simplexVertices σ.val) ⟨_,σ.property.1,rfl⟩
      _ subset_rfl).comp (fun A=>Measure.count A)).continuous.measurable
  have hd : ∀ s∈K.faces,s.card≤n+1 := by
    intro s hs
    obtain ⟨τ,_,hst,hc,_⟩ := hK s hs
    exact (Finset.card_le_card hst).trans_eq hc
  have hfinite' x : Measure.count ((Q.pair 0).P.val x∩
      convexHull ℝ (simplexVertices σ.val : Set (Y →₀ ℝ)))<⊤ :=
    Measure.count_apply_lt_top.mpr (zero_inter_simplex_finite Q hd σ x)
  rw [integral_toReal hmeas.aemeasurable (Filter.Eventually.of_forall hfinite')]
  exact hbound σ ε hε.le Q hQ
end
end Sparse.GraphGeometry
end BassTrace
end
end OAI
end
section
open Set Finset MeasureTheory OAI OAI.BassTrace OAI.BassTrace.Sparse OAI.BassTrace.Sparse.GraphGeometry
open scoped Classical Pointwise BassTrace.Sparse
namespace GFT
variable {Y : Type} [LinearOrder Y] (G : SimpleGraph Y) [G.LocallyFinite] (hG:G.Connected)
 (K : PreAbstractSimplicialComplex Y) (n:ℕ)
noncomputable def dual (p q:Y→₀ℝ) := sSup {r | ∃ f:Y→ℝ,(∀ u v,dist (f u) (f v)≤G.dist u v) ∧
 (p.sum fun y a=>a*f y)-(q.sum fun y a=>a*f y)=r}/Real.sqrt n
lemma dual_eq {p q:Y→₀ℝ} (hp:p∈(Geometry.SimplicialComplex.onFinsupp (𝕜:=ℝ) K).space)
 (hq:q∈(Geometry.SimplicialComplex.onFinsupp (𝕜:=ℝ) K).space) :
 dual G n p q=realizationDistance G hG K n p q := by
 rw [realizationDistance,dif_pos hp,dif_pos hq]
 letI := graphMetric G hG
 unfold dual FinProbability.rho FinProbability.transport
 congr 2
 ext r
 simp only [mem_setOf_eq,lipschitzWith_iff_dist_le_mul,NNReal.coe_one,one_mul,
  FinProbability.gap,FinProbability.expectation,pointProbability_coeff]
 rfl
set_option maxHeartbeats 3000000 in
theorem g_produce (g : GlobalCut.Target) : FT.Leaf := by
 intro H X Y _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ μ _ hμ G _ hG ha D n hD hdeg hlarge T K hT he
 have he' : K=generatedComplex (H:=H) T := by ext s; change s∈K.faces ↔ _; rw [he]; dsimp [generatedComplex]; congr!
 subst K
 let K := generatedComplex (H := H) T
 letI : LinearOrder (Y →₀ ℝ) := linearOrderOfSTO WellOrderingRel
 letI : Fact (∀(h : H) s,s∈K.faces → s.map (MulAction.toPerm h).toEmbedding∈K.faces) :=
   ⟨generatedComplex_invariant T⟩
 let act : MulAction H (SourceTop K n) := sourceTopAction K n (generatedComplex_invariant T)
 letI : Finite (MulAction.orbitRel.Quotient H (SourceTop K n)) := by
   convert generatedTop_finite (H := H) T n (fun t ht => (hT t ht).1) using 1
   congr 3
   dsimp only [act]
   congr 1
   exact Subsingleton.elim _ _

 have hK := generatedComplex_pure T n G ha hT
 have hn : 0<n := lt_of_lt_of_le (by positivity) hlarge
 obtain ⟨C,hC,hzero⟩ := g_exists_sparse_zero_strata (g:=g) (H:=H) (X:=X) (K:=K) (n:=n) G hG ha (graphMetric_action_isometry G hG ha) hn hK μ hμ D hD hdeg hlarge (generatedReps T) (fun _ hs=>generatedReps_mem T hs) (fun _ hs=>generatedReps_complete T hs)
 refine ⟨C,hC,?_⟩
 intro ε hε
 obtain ⟨Q,hQ⟩ := hzero ε hε
 letI : MeasurableSpace (Y→₀ℝ) := borel _
 have hh := (FT.raw_iff (count:=fun P=>∀ σ : SourceTop K n,(∫ x,(Measure.count (P x∩convexHull ℝ (simplexVertices σ.val : Set (Y →₀ ℝ)))).toReal ∂μ)≤C σ*ε)).mpr ⟨Q,hQ⟩
 rcases hh with ⟨A,P,h0,hs,hm,hl,ha',hb,ht,hstep⟩
 refine ⟨A,P,?_,hs,hm,hl,ha',hb,ht,?_⟩
 · intro s
   convert h0 s using 1 <;> congr!
 intro i hi x
 obtain ⟨a,b,c,d⟩ := hstep i hi x
 refine ⟨a,b,c,?_⟩
 intro U hU hc p hp q hq
 have sp {v} (hv:v∈U) : v∈(Geometry.SimplicialComplex.onFinsupp (𝕜:=ℝ) K).space := by
   obtain ⟨t,ht',hv',_⟩ := hm _ x v (hU hv).1
   exact (hs _ x).1 ▸ (A _ x).convexHull_subset_space ht' hv'
 apply (dual_eq G hG K n (sp hp) (sp hq)).trans_le
 apply d U _ hU p hp q hq
 convert hc using 1 <;> congr!
end GFT
end
section
open Set MeasureTheory
namespace FT
theorem g_buildSmall (g : GlobalCut.Target) : Small := by
 intro H Y X _ _ _ _ _ _ _ _ _
 letI : MeasurableSpace X := borel X
 letI : BorelSpace X := ⟨rfl⟩
 intro μ hμ
 exact GFT.g_produce g H X Y μ.toMeasure hμ
end FT
end

open Set Geometry
open scoped Classical
namespace XCut
noncomputable section
def WeakFactory : Prop := ∀(V:Type)[NormedAddCommGroup V][NormedSpace ℝ V],let c (s:Finset V):=convexHull ℝ ↑s;let C:=SimplicialComplex ℝ V;let w s (A:Finset _):=(A.image (c s∩·)).filter fun q↦q.Nonempty∧q≠c s;∃Φ:_→_→C,∀L:C,∀A:_→Finset (Set V),(∀s∈L.faces,∀p∈A s,∃l:V→ₗ[ℝ]ℝ,∃r,p={x|l x≤r})→(∀s∈L.faces,∀t⊆s,t.Nonempty→w t (A s)=w t (A t))→∃M:C,M.space=L.space∧∀s∈L.faces,let N:=Φ s (A s);N.faces.Finite∧N.space=c s∧{u∈M.faces|↑u⊆c s}=N.faces∧(∀u∈M.faces,c u∩c s=convexHull ℝ (↑u∩c s))∧(∀u∈N.faces,∀(l:V→ₗ[ℝ]ℝ) r,{x|l x≤r}∈A s→c u⊆{x|l x≤r}∨c u⊆{x|r≤l x})∧∀e:V≃L[ℝ]V,(Φ (s.image e) ((A s).image (e ''·))).faces=(·.image e)''N.faces
theorem restoreFactory (g : WeakFactory) : GlobalCut.Target := by
 classical
 intro V _ _ C c hs act
 obtain ⟨F,hF⟩ := g V
 refine ⟨F,?_⟩
 intro K A hA hw
 obtain ⟨M,hM,h⟩ := hF K A hA hw
 let U := {u | ∃ s ∈ K.faces, u ∈ (F s (A s)).faces}
 have sub : U ⊆ M.faces := by
   rintro u ⟨s,hs,hu⟩
   have eqn := (h s hs).2.2.1
   rw [←eqn] at hu
   exact hu.1
 let N : C := { faces := U
                isRelLowerSet_faces := by
                  rintro u ⟨s,hs,hu⟩
                  exact ⟨(F s (A s)).nonempty_of_mem_faces hu,fun _ hsub hne => ⟨s,hs,(F s (A s)).down_closed hu hsub hne⟩⟩
                indep := fun h => M.indep (sub h)
                inter_subset_convexHull := fun h k => M.inter_subset_convexHull (sub h) (sub k) }
 refine ⟨N,rfl,?_,?_⟩
 · ext x
   constructor
   · intro hx
     obtain ⟨t,ht,hx⟩ := SimplicialComplex.mem_space_iff.mp hx
     exact hM ▸ M.convexHull_subset_space (sub ht) hx
   · intro hx
     obtain ⟨s,hs',hx⟩ := SimplicialComplex.mem_space_iff.mp hx
     have hh := (h s hs').2.1
     have hx' : x ∈ (F s (A s)).space := hh.symm ▸ hx
     obtain ⟨u,hu,hx⟩ := SimplicialComplex.mem_space_iff.mp hx'
     exact N.convexHull_subset_space (show u∈U from ⟨s,hs',hu⟩) hx
 · intro s hs
   obtain ⟨hf,hspace,htr,hi,hcut,hn⟩ := h s hs
   refine ⟨hf,hspace,?_,fun u hu => hi u (sub hu),hcut,?_⟩
   · ext u
     constructor
     · intro hu
       exact htr ▸ (show u ∈ {t ∈ M.faces | (t : Set V) ⊆ c s} from ⟨sub hu.1,hu.2⟩)
     · intro hu
       exact ⟨⟨s,hs,hu⟩,(show u ∈ {t ∈ M.faces | (t : Set V) ⊆ c s} from htr.symm ▸ hu).2⟩
   · intro e
     have he (t : Finset V) : t.map e.toEquiv.toEmbedding = t.image e := by
       ext u
       simp only [Finset.mem_map,Finset.mem_image]
       rfl
     simpa only [he] using hn e
end
end XCut

namespace XCut
theorem weakSmall (g : WeakFactory) : FT.Small := FT.g_buildSmall (restoreFactory g)
end XCut

open Set MeasureTheory Finsupp Geometry TopologicalSpace
open scoped Pointwise Classical
namespace XCut
noncomputable section
def Ha : Prop := ∀(H Y:Type)(X:Profinite.{0})[Group H][Countable H][Countable Y][LinearOrder Y][MulAction H Y][IsCancelSMul H Y][MulAction H X][ContinuousConstSMul H X][IsCancelSMul H X],letI:=borel X;∀μ:ProbabilityMeasure X,(∀h:H,MeasurePreserving (h•·:X→X) μ μ)→∀(G:SimpleGraph Y)[G.LocallyFinite],G.Connected→(∀(h:H) u v,G.Adj (h•u) (h•v)↔G.Adj u v)→∀D n:ℕ,2≤D→(∀y,G.degree y≤D)→(4*D^3+D+3)^2≤n→∀T:Finset (Finset Y),(∀t∈T,t.card=n+1∧(G.induce ↑t).Connected)→
 (∀(V:Type)[NormedAddCommGroup V][NormedSpace ℝ V],let c (s:Finset V):=convexHull ℝ ↑s;let C:=SimplicialComplex ℝ V;let w s (A:Finset _):=(A.image (c s∩·)).filter fun q↦q.Nonempty∧q≠c s;∃Φ:_→_→C,∀L:C,∀A:_→Finset (Set V),(∀s∈L.faces,∀p∈A s,∃l:V→ₗ[ℝ]ℝ,∃r,p={x|l x≤r})→(∀s∈L.faces,∀t⊆s,t.Nonempty→w t (A s)=w t (A t))→∃M:C,M.space=L.space∧∀s∈L.faces,let N:=Φ s (A s);N.faces.Finite∧N.space=c s∧{u∈M.faces|↑u⊆c s}=N.faces∧(∀u∈M.faces,c u∩c s=convexHull ℝ (↑u∩c s))∧(∀u∈N.faces,∀(l:V→ₗ[ℝ]ℝ) r,{x|l x≤r}∈A s→c u⊆{x|l x≤r}∨c u⊆{x|r≤l x})∧∀e:V≃L[ℝ]V,(Φ (s.image e) ((A s).image (e ''·))).faces=(·.image e)''N.faces)→
 let V:=Y→₀ℝ
 let S:=SimplicialComplex ℝ V
 let c (s:Finset V):=convexHull ℝ ↑s
 let a (h:H):=mapDomain (M:=ℝ) (h•·)
 ∀K:S,K.faces=(·.image (single · 1))''{s|s.Nonempty∧∃h:H,∃t∈T,s⊆h•t}→
 ∃C:Finset V→ℝ,∀ε>0,∃(Z:ℕ→X→S) (P:_→_→Set V),(∀s∈K.faces,s.card=n+1→∫x,((P 0 x∩c s).ncard:ℝ)∂μ≤C s*ε)∧(∀i x,∀v∈P i x,∃s∈(Z i x).faces,v∈c s∧c s⊆P i x)∧(∀i,∀t∈K.faces,IsLocallyConstant fun x↦({s∈(Z i x).faces|↑s⊆c t},P i x∩c t))∧(∀i h x,(·.image (a h))''(Z i x).faces⊆(Z i (h•x)).faces∧a h ''P i x⊆P i (h•x))∧(∀x,Z n x=K∧P n x=K.space)∧∀i<n,∀x,(Z i x).space=K.space∧(∀t∈(Z (i+1) x).faces,(∀s∈(Z i x).faces,c s∩c t=convexHull ℝ (↑s∩c t))∧{s∈(Z i x).faces|↑s⊆c t}.Finite)∧P i x⊆P (i+1) x∧(∀t∈(Z (i+1) x).faces,c t⊆P (i+1) x→∀s∈(Z i x).faces,c s⊆c t∩P i x→s.card<t.card)∧∀A⊆P (i+1) x\P i x,IsPreconnected ((linearCombination ℝ (lp.single 2 · (1:ℝ)))''A)→∀p∈A,∀q∈A,sSup {r|∃f:Y→ℝ,(∀u v,f u-f v≤G.dist u v)∧linearCombination ℝ f (p-q)=r}≤8*D^2*√n
end
end XCut
open Set MeasureTheory Finsupp
namespace XCut
lemma ncardReal {V : Type} [MeasurableSpace V] [MeasurableSingletonClass V] (u : Set V) :
    (u.ncard : ℝ) = (Measure.count u).toReal := by
  classical
  by_cases h : u.Finite
  · rw [Measure.count_apply_finite u h, ← Set.ncard_eq_toFinset_card u h]
    simp
  · rw [Set.Infinite.ncard h,Measure.count_apply_infinite h]; simp
lemma lipschitzDual {Y : Type} (G : SimpleGraph Y) (p q : Y →₀ ℝ) :
    {r | ∃ f : Y → ℝ, (∀ u v, f u-f v ≤ G.dist u v) ∧ linearCombination ℝ f (p-q)=r} =
    {r | ∃ f : Y → ℝ, (∀ u v, dist (f u) (f v) ≤ G.dist u v) ∧
        (p.sum fun y a => a*f y)-(q.sum fun y a => a*f y)=r} := by
  ext r
  simp only [mem_setOf_eq, map_sub,linearCombination_apply,smul_eq_mul,Real.dist_eq,abs_le]
  constructor
  · rintro ⟨f,h,k⟩
    refine ⟨f,fun u v => ⟨?_,h u v⟩,k⟩
    have hh := h v u
    rw [G.dist_comm (u:=v) (v:=u)] at hh
    linarith
  · rintro ⟨f,h,k⟩; exact ⟨f,fun u v => (h u v).2,k⟩
end XCut
open Set Geometry Finset
namespace XCut
noncomputable section
variable {V : Type} [AddCommGroup V] [Module ℝ V]

lemma tracePoint (L : SimplicialComplex ℝ V) (P Q : Set V) (hQ : Convex ℝ Q)
    (cov : ∀ x ∈ P, ∃ s ∈ L.faces, x ∈ convexHull ℝ (s : Set V) ∧ convexHull ℝ (s : Set V) ⊆ P)
    (hi : ∀ s ∈ L.faces, convexHull ℝ (s : Set V) ∩ Q = convexHull ℝ ((s : Set V) ∩ Q)) :
    P ∩ Q = ⋃ s ∈ {s ∈ {s ∈ L.faces | convexHull ℝ (s : Set V) ⊆ P} | (s : Set V) ⊆ Q}, convexHull ℝ (s : Set V) := by
  classical
  ext x
  constructor
  · rintro ⟨hp,hq⟩
    obtain ⟨s,hs,hx,hp'⟩ := cov x hp
    let u := s.filter (·∈Q)
    have eu : (u : Set V) = (s : Set V) ∩ Q := Set.ext fun _ => Finset.mem_filter
    have hu : x ∈ convexHull ℝ (u : Set V) := by rw [eu,←hi s hs]; exact ⟨hx,hq⟩
    have hn : u.Nonempty := by
      by_contra! hn
      simp [hn] at hu
    have su : u ⊆ s := Finset.filter_subset _ _
    exact mem_iUnion₂.mpr ⟨u,⟨⟨L.down_closed hs su hn, (convexHull_mono su).trans hp'⟩, fun _ hy => (Finset.mem_filter.mp hy).2⟩,hu⟩
  · intro hx
    obtain ⟨s,⟨⟨_,hp⟩,hq⟩,hs⟩ := mem_iUnion₂.mp hx
    exact ⟨hp hs,convexHull_min hq hQ hs⟩
end
end XCut
open Set MeasureTheory Geometry Finsupp OAI OAI.BassTrace OAI.BassTrace.Sparse
open scoped Pointwise Classical BassTrace.Sparse
noncomputable section
namespace XCut
set_option maxHeartbeats 800000 in
theorem producer : Ha := by
 classical
 intro H Y X _ _ _ _ _ _ _ _ _
 letI := borel X
 intro μ hμ G _ hG he D n hD hd hn T ht g V S c a K hk
 let B := generatedComplex (H := H) T
 have e : K = SimplicialComplex.onFinsupp (𝕜:=ℝ) B := by
   ext s
   change s∈K.faces ↔ _
   rw [hk,onFinsupp_faces]; dsimp [B,generatedComplex]; congr!
 subst K
 have hd' : ∀ y,Fintype.card (G.neighborSet y)≤D := by simpa only [SimpleGraph.card_neighborSet_eq_degree] using hd
 obtain ⟨C,hC,h⟩ := FT.g_buildSmall (restoreFactory g) H Y X μ hμ G hG he D n hD hd' hn T B ht (by dsimp [B,generatedComplex]; congr!)
 let f := fun s : Finset Y => s.image (single · (1:ℝ))
 let I := {s : Finset Y // s∈B.faces ∧ s.card=n+1}
 let j : I → Finset V := fun s => f s.val
 have inj : Function.Injective j := fun s t h => Subtype.ext (Finset.image_injective (Finsupp.single_left_injective (one_ne_zero : (1:ℝ)≠0)) h)
 refine ⟨fun u => if h : ∃i,j i=u then C h.choose else 0,?_⟩
 intro ε hε
 obtain ⟨Z,P,h0,hs,hm,hl,hA,hP,hN,hstep⟩ := h ε hε
 refine ⟨Z,P,?_,hm,?_,?_,hN,?_⟩
 · intro u hu hcard
   obtain ⟨s,hs',rfl⟩ := hu
   have ic : s.card=n+1 := by
     convert hcard using 1
     exact (Finset.card_image_of_injective _ (Finsupp.single_left_injective (one_ne_zero : (1:ℝ)≠0))).symm
   let b : I := ⟨s,hs',ic⟩
   have hb : ∃ i,j i=j b := ⟨b,rfl⟩
   change _ ≤ (if h : ∃ i,j i=j b then C h.choose else 0)*ε
   rw [dif_pos hb,inj hb.choose_spec]
   have hh := h0 b
   convert hh using 1
   apply integral_congr_ae; filter_upwards with x
   letI := borel (Y →₀ ℝ)
   letI : BorelSpace (Y →₀ ℝ) := ⟨rfl⟩
   convert ncardReal (V:=Y →₀ ℝ) (P 0 x ∩ c (j b)) using 1 <;> congr!
 · intro i t ht'
   obtain ⟨h1,h2⟩ := hl i t ht'
   apply h1.prodMk
   convert h2.comp (fun U : Set (Finset V) => ⋃ s ∈ U, c s) using 1
   funext x
   dsimp only [Function.comp_apply]
   exact tracePoint _ _ _ (convex_convexHull ℝ _) (hm i x) ((hs i x).2.2 t ht').1
 · intro i h x
   have act (v : V) : a h v = (Finsupp.domLCongr (R:=ℝ) (MulAction.toPerm h : Y ≃ Y)) v := by
     ext z
     exact Finsupp.mapDomain_equiv_apply (f:=MulAction.toPerm h) v z
   constructor
   · rintro _ ⟨s,hs',rfl⟩
     convert hA i h x s hs' using 1
     ext y
     simp only [Finset.mem_image,Finset.mem_map,act]; rfl
   · rintro _ ⟨v,hv,rfl⟩; rw [act]; exact hP i h x v hv
 · intro i hi x
   obtain ⟨hsub,hinc,hcard,hok⟩ := hstep i hi x
   refine ⟨(hs i x).1,hsub.2.2,hinc,hcard,?_⟩
   intro U hU hUc p hp q hq
   let m := (linearCombination ℝ (fun y : Y => lp.single 2 y (1:ℝ)))
   letI := TopologicalSpace.induced m inferInstance
   have hUc' : IsPreconnected U := (show Topology.IsInducing m from ⟨rfl⟩).isPreconnected_image.mp hUc
   have hh := hok U hU (by convert hUc' using 1 <;> congr!) p hp q hq
   rw [lipschitzDual]
   have hn' : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast (show 0<n by nlinarith [Nat.zero_le D]))
   have bound := (div_le_iff₀ hn').mp hh
   convert bound using 1 <;> first | ring | congr!
end XCut
end


theorem OMA.solution : OMA.R_mo_178849_R1.H2 := XCut.producer

/-
                                 Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "[]"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright [yyyy] [name of copyright owner]

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
-/
