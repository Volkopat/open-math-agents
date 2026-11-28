import OMAReductions.R_mo_178849_R1
/- Adapted from OpenAI openai/math 3344da59991ed94f9ba711217b29c1d760badfa6 with private Spark2 overlays (threshold, factory, GChain). -/
section
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
end
section
open Set Geometry Finset
namespace XCut
set_option maxHeartbeats 1000000 in
lemma genericPositive {E : Type} [AddCommGroup E] [Module ℝ E] {F T : Finset E}
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
lemma carrier {V : Type} [AddCommGroup V] [Module ℝ V] (L K : SimplicialComplex ℝ V)
    (he : L.space = K.space) (hr : ∀ t∈K.faces, ∀ s∈L.faces,
      convexHull ℝ (s : Set V) ∩ convexHull ℝ (t : Set V) = convexHull ℝ ((s : Set V) ∩ convexHull ℝ (t : Set V)))
    (s : Finset V) (hs : s ∈ L.faces) : ∃ t ∈ K.faces, convexHull ℝ (s : Set V) ⊆ convexHull ℝ (t : Set V) := by
 classical
 let w := fun _ : V => (s.card : ℝ)⁻¹
 have hc : (0 : ℝ) < s.card := by exact_mod_cast (L.nonempty_of_mem_faces hs).card_pos
 have hw (x : V) : 0 < w x := inv_pos.mpr hc
 have hsum : ∑ x ∈ s, w x = 1 := by simp only [w,Finset.sum_const,nsmul_eq_mul]; exact mul_inv_cancel₀ (ne_of_gt hc)
 have hm : (∑ x ∈ s,w x • x) ∈ convexHull ℝ (s : Set V) := (convex_convexHull ℝ (s : Set V)).sum_mem (fun x _ => (hw x).le) hsum (fun _ hx => subset_convexHull ℝ _ hx)
 have hmk : (∑ x ∈ s,w x • x) ∈ L.space := L.convexHull_subset_space hs hm
 rw [he] at hmk
 obtain ⟨t,ht,hp⟩ := SimplicialComplex.mem_space_iff.mp hmk
 let P : Set V := convexHull ℝ (t : Set V)
 have hi : (∑ x ∈ s,w x • x) ∈ convexHull ℝ ((s.filter (·∈P) : Finset V) : Set V) := by
   have hboth : (∑ x ∈ s, w x • x) ∈ convexHull ℝ (s : Set V) ∩ convexHull ℝ (t : Set V) := ⟨hm,hp⟩
   have hboth2 := (hr t ht s hs).le hboth
   have hh : ((s.filter (·∈P) : Finset V) : Set V) = (s : Set V) ∩ P := by
     apply Set.ext
     intro y
     change y ∈ s.filter (·∈P) ↔ y∈s ∧ y∈P
     exact Finset.mem_filter
   rw [hh]
   exact hboth2
 have hsub : s ⊆ s.filter (·∈P) := genericPositive (L.indep hs) (s.filter_subset (·∈P)) w (fun x _ => hw x) hsum hi
 refine ⟨t,ht,convexHull_min ?_ (convex_convexHull ℝ _)⟩
 intro x hx
 have hy : x ∈ s.filter (·∈P) := hsub (show x∈s from hx)
 have hz : x∈s ∧ x∈P := Finset.mem_filter.mp hy
 exact hz.2
end XCut
end
section
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
def Hb : Prop := ∀(H Y:Type)[Group H][Countable H][Countable Y][LinearOrder Y][MulAction H Y][IsCancelSMul H Y](_:Y)(G:SimpleGraph Y)[G.LocallyFinite],G.Connected→(∀(h:H) u v,G.Adj (h•u) (h•v)↔G.Adj u v)→∀D n:ℕ,2≤D→(∀y,G.degree y≤D)→(4*D^3+D+3)^2≤n→∀T:Finset (Finset Y),(∀t∈T,t.card=n+1∧(G.induce ↑t).Connected)→
(∀(X:Profinite.{0})[MulAction H X][ContinuousConstSMul H X][IsCancelSMul H X],letI:=borel X;∀μ:ProbabilityMeasure X,(∀h:H,MeasurePreserving (h•·:X→X) μ μ)→
 let V:=Y→₀ℝ
 let S:=SimplicialComplex ℝ V
 let c (s:Finset V):=convexHull ℝ ↑s
 let a (h:H):=mapDomain (M:=ℝ) (h•·)
 ∀K:S,K.faces=(·.image (single · 1))''{s|s.Nonempty∧∃h:H,∃t∈T,s⊆h•t}→
 ∃C:Finset V→ℝ,∀ε>0,∃(Z:ℕ→X→S) (P:_→_→Set V),(∀s∈K.faces,s.card=n+1→∫x,((P 0 x∩c s).ncard:ℝ)∂μ≤C s*ε)∧(∀i x,∀v∈P i x,∃s∈(Z i x).faces,v∈c s∧c s⊆P i x)∧(∀i,∀t∈K.faces,IsLocallyConstant fun x↦({s∈(Z i x).faces|↑s⊆c t},P i x∩c t))∧(∀i h x,(·.image (a h))''(Z i x).faces⊆(Z i (h•x)).faces∧a h ''P i x⊆P i (h•x))∧(∀x,Z n x=K∧P n x=K.space)∧∀i<n,∀x,(Z i x).space=K.space∧(∀t∈(Z (i+1) x).faces,(∀s∈(Z i x).faces,c s∩c t=convexHull ℝ (↑s∩c t))∧{s∈(Z i x).faces|↑s⊆c t}.Finite)∧P i x⊆P (i+1) x∧(∀t∈(Z (i+1) x).faces,c t⊆P (i+1) x→∀s∈(Z i x).faces,c s⊆c t∩P i x→s.card<t.card)∧∀A⊆P (i+1) x\P i x,IsPreconnected ((linearCombination ℝ (lp.single 2 · (1:ℝ)))''A)→∀p∈A,∀q∈A,sSup {r|∃f:Y→ℝ,(∀u v,f u-f v≤G.dist u v)∧linearCombination ℝ f (p-q)=r}≤8*D^2*√n)→
 let E:=fun k↦⋀[ℂ]^k (Y→₀ℂ)
 let w:=fun k (v:Fin k→Y)↦exteriorPower.ιMulti ℂ k fun i↦single (v i) (1:ℂ)
 let S:=fun k↦Submodule.span ℂ {x|∃v:Fin k→Y,(Finset.univ.image v∈insert ∅ {s:Finset Y|s.Nonempty∧∃h:H,∃t∈T,s⊆h•t})∧w k v=x}
 let a:=fun k (h:H)↦exteriorPower.map k (lmapDomain ℂ ℂ fun y:Y↦h•y)
 ∀d:∀k,E (k+1)→ₗ[ℂ] E k,(∀k v,d k (w (k+1) v)=∑i:Fin (k+1),(-1:ℂ)^i.val•w k (v ∘ i.succAbove))→∀(c:S (n+1)) (ψ:E (n+1)→ₗ[ℂ] ℂ) (δ:ℝ),0<δ→∃A:∀k,E k→ₗ[ℂ] E k,(∀x,A 0 x=x)∧(∀k x,x∈S (k+1)→d k (A (k+1) x)=A k (d k x))∧(∀k h x,x∈S k→a k h (A k x)=A k (a k h x))∧‖ψ (A (n+1) c)‖<δ
end
end XCut
end
section
namespace FT
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
theorem dite_eq_right {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort*} {t : c → α} {e : ¬c → α} : (dite c t e) = e hc := dif_neg hc
theorem Measurable.of_eval {α δ : Type*} {X : δ → Type*} [MeasurableSpace α] [∀ a, MeasurableSpace (X a)] {f : α → ∀ a, X a} (hf : ∀ a, Measurable fun c => f c a) : Measurable f := measurable_pi_lambda f hf
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
lemma contraction_square (α : M →ₗ[R] R) (x : ExteriorAlgebra R M) :
    contraction α (contraction α x) = 0 :=
  CliffordAlgebra.contractLeft_contractLeft α x
@[simp] lemma contraction_one (α : M →ₗ[R] R) :
    contraction α (1 : ExteriorAlgebra R M) = 0 :=
  CliffordAlgebra.contractLeft_one _ α
@[simp] lemma contraction_ι (α : M →ₗ[R] R) (v : M) :
    contraction α (ExteriorAlgebra.ι R v) = algebraMap R _ (α v) :=
  CliffordAlgebra.contractLeft_ι _ α v
lemma contraction_ι_mul (α : M →ₗ[R] R) (v : M) (x : ExteriorAlgebra R M) :
    contraction α (ExteriorAlgebra.ι R v * x) =
      α v • x - ExteriorAlgebra.ι R v * contraction α x :=
  CliffordAlgebra.contractLeft_ι_mul α v x
lemma cone_contraction (α : M →ₗ[R] R) {v : M} (hv : α v = 1)
    (x : ExteriorAlgebra R M) :
    contraction α (ExteriorAlgebra.ι R v * x) +
      ExteriorAlgebra.ι R v * contraction α x = x := by
  rw [contraction_ι_mul, hv, one_smul, sub_add_cancel]
lemma contraction_ιMulti_succ (α : M →ₗ[R] R) {n : ℕ} (v : Fin (n+1) → M) :
    contraction α (ExteriorAlgebra.ιMulti R (n+1) v) =
      α (v 0) • ExteriorAlgebra.ιMulti R n (fun i => v i.succ) -
        ExteriorAlgebra.ι R (v 0) *
          contraction α (ExteriorAlgebra.ιMulti R n (fun i => v i.succ)) := by
  rw [ExteriorAlgebra.ιMulti_succ_apply, contraction_ι_mul]
  rfl
lemma contraction_ιMulti (α : M →ₗ[R] R) (n : ℕ) (v : Fin (n+1) → M) :
    contraction α (ExteriorAlgebra.ιMulti R (n+1) v) =
      ∑ i : Fin (n+1), ((-1 : R)^i.val * α (v i)) •
        ExteriorAlgebra.ιMulti R n (fun j => v (i.succAbove j)) := by
  induction n with
  | zero =>
    rw [contraction_ιMulti_succ]
    simp
  | succ n ih =>
    rw [contraction_ιMulti_succ, ih]
    conv_rhs => rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero]
    rw [sub_eq_add_neg]
    congr 1
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [ExteriorAlgebra.ιMulti_succ_apply]
    simp only [Fin.val_succ, pow_succ, Matrix.vecTail, Function.comp_def, Fin.succ_succAbove_succ,
      Fin.succAbove_ne_zero_zero (Fin.succ_ne_zero i), mul_smul_comm,
      mul_neg, mul_one, neg_mul, neg_smul]
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
noncomputable def augmentation : Vectors Y →ₗ[ℂ] ℂ :=
  Finsupp.linearCombination ℂ (fun _ : Y => (1 : ℂ))
noncomputable def boundary : Algebra Y →ₗ[ℂ] Algebra Y :=
  contraction (augmentation Y)
@[simp] lemma augmentation_single (y : Y) (c : ℂ) :
    augmentation Y (Finsupp.single y c) = c := by
  simp [augmentation]
lemma boundary_square (x : Algebra Y) : boundary Y (boundary Y x) = 0 :=
  contraction_square _ x
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
lemma span_wedges (n : ℕ) :
    Submodule.span ℂ (Set.range (wedge (Y := Y) n)) = ⊤ := by
  apply top_unique
  rw [← (basis n).span_eq]
  apply Submodule.span_mono
  rintro _ ⟨s, rfl⟩
  exact ⟨_, (basis_eq_wedge n s).symm⟩
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
@[simp] lemma cone_coe (n : ℕ) (v : Y →₀ ℂ) (x : Degree Y n) :
    (cone n v x : Chains.Algebra Y) = ExteriorAlgebra.ι ℂ v * x := rfl
def d (n : ℕ) : Degree Y (n+1) →ₗ[ℂ] Degree Y n :=
  ((Chains.boundary Y).comp (Degree Y (n+1)).subtype).codRestrict _ fun x =>
    Chains.contraction_mem_exteriorPower (Chains.augmentation Y) n x.property
@[simp] lemma d_coe (n : ℕ) (x : Degree Y (n+1)) :
    (d n x : Chains.Algebra Y) = Chains.boundary Y x := rfl
lemma d_square (n : ℕ) (x : Degree Y (n+2)) : d n (d (n+1) x) = 0 := by
  ext
  exact Chains.boundary_square _ _
lemma d_cone_cycle (n : ℕ) (v : Y →₀ ℂ) (hv : Chains.augmentation Y v = 1)
    (x : Degree Y n) (hx : Chains.boundary Y x = 0) :
    d n (cone n v x) = x := by
  ext
  change Chains.boundary Y (ExteriorAlgebra.ι ℂ v * (x : Chains.Algebra Y)) = _
  have he : Chains.boundary Y (ExteriorAlgebra.ι ℂ v * (x : Chains.Algebra Y)) +
      ExteriorAlgebra.ι ℂ v * Chains.boundary Y x = (x : Chains.Algebra Y) :=
    Chains.cone_contraction (Chains.augmentation Y) hv (x : Chains.Algebra Y)
  simpa only [hx, mul_zero, add_zero] using he
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
@[simp] lemma coneLift_wedge {n : ℕ} (r : Degree Y n →ₗ[ℂ] Degree Y n)
    (v : Fin n → Y) :
    coneLift r (wedge n v) = cone n (average n v) (r (wedge n v)) :=
  (coneFunction r).lift_wedge v
omit [LinearOrder Y] in
lemma d_wedge (n : ℕ) (v : Fin (n+1) → Y) :
    d n (wedge (n+1) v) =
      ∑ i : Fin (n+1), (-1 : ℂ)^i.val • wedge n (fun j => v (i.succAbove j)) := by
  apply Subtype.ext
  change Chains.boundary Y (ExteriorAlgebra.ιMulti ℂ (n+1)
      (fun i => Finsupp.single (v i) 1)) = _
  rw [Chains.boundary, Chains.contraction_ιMulti]
  simp only [Chains.augmentation_single, mul_one, Submodule.coe_sum,
    Submodule.coe_smul, wedge, exteriorPower.ιMulti_apply_coe]
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
lemma vertices_range {n : ℕ} (s : Set.powersetCard V n) : Set.range (vertices s) = s.val :=
  Finset.range_orderEmbOfFin s.val s.property
def eraseFace {n : ℕ} (s : Set.powersetCard V (n+1)) (i : Fin (n+1)) :
    Set.powersetCard V n :=
  ⟨s.val.erase (vertices s i), by simp [Finset.card_erase_of_mem (vertices_mem s i)]⟩
@[simp] lemma eraseFace_val {n : ℕ} (s : Set.powersetCard V (n+1)) (i : Fin (n+1)) :
    (eraseFace s i).val = s.val.erase (vertices s i) := rfl
lemma vertices_eraseFace {n : ℕ} (s : Set.powersetCard V (n+1)) (i : Fin (n+1)) :
    vertices (eraseFace s i) = i.succAboveOrderEmb.comp (vertices s) := by
  symm
  apply Finset.orderEmbOfFin_unique' (eraseFace s i).property
  intro j
  apply Finset.mem_erase.mpr
  exact ⟨fun h => Fin.succAbove_ne i j ((vertices s).injective h),vertices_mem s _⟩
lemma boundary_basis (n : ℕ) (s : Set.powersetCard V (n+1)) :
    d n (basis (Y := V) (n+1) s) =
      ∑ i : Fin (n+1), (-1 : ℂ)^i.val • basis n (eraseFace s i) := by
  rw [basis_eq_wedge,d_wedge]
  apply Finset.sum_congr rfl
  intro i _
  rw [basis_eq_wedge]
  congr 2
  exact congrArg (fun e : Fin n ↪o V => (e : Fin n → V)) (vertices_eraseFace s i).symm
lemma boundary_basis_coefficient (n : ℕ) (s : Set.powersetCard V (n+1))
    (t : Set.powersetCard V n) :
    (basis n).repr (d n (basis (Y := V) (n+1) s)) t =
      ∑ i : Fin (n+1), if eraseFace s i = t then (-1 : ℂ)^i.val else 0 := by
  simp only [boundary_basis,map_sum,map_smul,Finsupp.finsetSum_apply,Finsupp.smul_apply,
    Module.Basis.repr_self,Finsupp.single_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp_all
end
open scoped BigOperators
open Oriented ChainHomotopy
variable {V : Type*} [LinearOrder V] {n : ℕ}
lemma insert_eraseFace (s : Set.powersetCard V (n+1)) (i : Fin (n+1)) :
    insert (vertices s i) (eraseFace s i).val = s.val :=
  Finset.insert_erase (vertices_mem s i)
lemma eraseFace_neq (s : Set.powersetCard V (n+1)) (i : Fin (n+1)) :
    vertices s i ∉ (eraseFace s i).val := Finset.notMem_erase _ _
lemma incidence_pair_injective (t : Set.powersetCard V n)
    {a b : Set.powersetCard V (n+1) × Fin (n+1)}
    (ha : eraseFace a.1 a.2 = t) (hb : eraseFace b.1 b.2 = t)
    (he : vertices a.1 a.2 = vertices b.1 b.2) : a = b := by
  have hs : a.1 = b.1 := by
    apply Subtype.ext
    rw [← insert_eraseFace a.1 a.2,← insert_eraseFace b.1 b.2,ha,hb,he]
  apply Prod.ext hs
  exact (vertices b.1).injective (by simpa only [hs] using he)
def incidencePairs (F : Finset (Set.powersetCard V (n+1))) (t : Set.powersetCard V n) :
    Finset (Set.powersetCard V (n+1) × Fin (n+1)) :=
  (F ×ˢ Finset.univ).filter fun p => eraseFace p.1 p.2 = t
def apexes (F : Finset (Set.powersetCard V (n+1))) (t : Set.powersetCard V n) : Finset V :=
  (incidencePairs F t).image fun p => vertices p.1 p.2
lemma mem_apexes (F : Finset (Set.powersetCard V (n+1))) (t : Set.powersetCard V n) (u : V) :
    u ∈ apexes F t ↔ u ∉ t.val ∧ ∃ s ∈ F, s.val = insert u t.val := by
  constructor
  · intro h
    obtain ⟨⟨s,i⟩,hp,rfl⟩ := Finset.mem_image.mp h
    obtain ⟨hp,ht⟩ := Finset.mem_filter.mp hp
    have hs := (Finset.mem_product.mp hp).1
    refine ⟨ht ▸ eraseFace_neq s i,s,hs,?_⟩
    rw [← insert_eraseFace s i,ht]
  · rintro ⟨hu,s,hs,he⟩
    have hus : u ∈ s.val := he ▸ Finset.mem_insert_self _ _
    obtain ⟨i,rfl⟩ := (show u ∈ Set.range (vertices s) from (vertices_range s).symm ▸ hus)
    apply Finset.mem_image.mpr
    refine ⟨(s,i),Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hs,Finset.mem_univ _⟩,?_⟩,rfl⟩
    apply Subtype.ext
    simp only [eraseFace_val,he,Finset.erase_insert hu]
lemma sum_incidencePairs (F : Finset (Set.powersetCard V (n+1))) (t : Set.powersetCard V n)
    {A : Type*} [AddCommMonoid A] (f : V → A) :
    ∑ p ∈ incidencePairs F t, f (vertices p.1 p.2) = ∑ u ∈ apexes F t, f u := by
  symm
  apply Finset.sum_image
  intro a ha b hb he
  exact incidence_pair_injective t (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2 he
lemma boundary_sum_coefficient (F : Finset (Set.powersetCard V (n+1)))
    (w : Set.powersetCard V (n+1) → ℂ) (t : Set.powersetCard V n) :
    (basis n).repr (d n (∑ s ∈ F, w s • basis (n+1) s)) t =
      ∑ p ∈ incidencePairs F t, w p.1 * (-1 : ℂ)^p.2.val := by
  simp only [map_sum,map_smul,Finsupp.finsetSum_apply,Finsupp.smul_apply,smul_eq_mul,
    boundary_basis_coefficient,Finset.mul_sum]
  rw [incidencePairs,Finset.sum_filter,Finset.sum_product]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp
end OrientedIncidence
namespace Sparse.Orientation
section
open scoped BigOperators
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
def facetForm (n : ℕ) (v : Fin n → (Fin (n+1) → ℝ)) : (Fin (n+1) → ℝ) →ₗ[ℝ] ℝ :=
  { toFun := fun x => Matrix.detRowAlternating.curryLeft x v
    map_add' := fun x y => by simp
    map_smul' := fun c x => by simp }
@[simp] lemma facetForm_apply (n : ℕ) (v : Fin n → (Fin (n+1) → ℝ))
    (x : Fin (n+1) → ℝ) : facetForm n v x = Matrix.det (Fin.cons x v) := rfl
lemma facetForm_vertex (n : ℕ) (v : Fin n → (Fin (n+1) → ℝ)) (j : Fin n) :
    facetForm n v (v j) = 0 := by
  rw [facetForm_apply]
  apply Matrix.det_zero_of_row_eq (i := 0) (j := j.succ) (Fin.succ_ne_zero j).symm
  simp
end
lemma det_cons_delete {n : ℕ} (v : Fin (n+1) → (Fin (n+1) → ℝ)) (i : Fin (n+1)) :
    Matrix.det (Fin.cons (v i) (fun j => v (i.succAbove j))) =
      (-1 : ℝ)^i.val * Matrix.det v := by
  have h := Matrix.detRowAlternating.neg_one_pow_smul_map_insertNth i (v i) (i.removeNth v)
  rw [Fin.insertNth_removeNth,Function.update_eq_self] at h
  change (-1 : ℤ) ^ i.val • Matrix.det v =
    Matrix.det (Fin.cons (v i) (fun j => v (i.succAbove j))) at h
  simpa only [zsmul_eq_mul,Int.cast_pow,Int.cast_neg,Int.cast_one] using h.symm
lemma realSign_negOnePow_mul (k : ℕ) (a : ℝ) :
    Real.sign ((-1 : ℝ)^k * a) = (-1 : ℝ)^k * Real.sign a := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, mul_neg_one,neg_mul,Real.sign_neg,ih,neg_mul]
lemma determinant_deletion_orientation {n : ℕ}
    (v : Fin (n+1) → (Fin (n+1) → ℝ)) (i : Fin (n+1)) :
    (Real.sign (Matrix.det v) : ℂ) * (-1 : ℂ)^i.val =
      (Real.sign (Matrix.det (Fin.cons (v i) (fun j => v (i.succAbove j)))) : ℂ) := by
  rw [det_cons_delete,realSign_negOnePow_mul]
  simp only [Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_neg,Complex.ofReal_one]
  exact mul_comm _ _
open scoped BigOperators
lemma det_cons_unit {n : ℕ} (v : Fin n → (Fin (n+1) → ℝ)) (i : Fin (n+1)) :
    Matrix.det (Fin.cons (Pi.single i 1) v) =
      (-1 : ℝ)^i.val * Matrix.det (fun j k => v j (i.succAbove k)) := by
  calc
    _ = ∑ j : Fin (n+1), (-1 : ℝ)^j.val * (if j = i then 1 else 0) *
        Matrix.det (fun a b => v a (j.succAbove b)) :=
      by
        have h := Matrix.det_succ_row_zero (Fin.cons (Pi.single i 1) v)
        change Matrix.det (Fin.cons (Pi.single i 1) v) =
          ∑ j : Fin (n+1), (-1 : ℝ)^j.val *
            (Pi.single i (1 : ℝ) : Fin (n+1) → ℝ) j *
            Matrix.det (fun a b => v a (j.succAbove b)) at h
        simpa only [Pi.single_apply] using h
    _ = _ := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hji
        simp [hji]
      · simp
lemma facetForm_on_unit {n : ℕ} (v : Fin n → (Fin (n+1) → ℝ)) (i : Fin (n+1)) :
    facetForm n v (Pi.single i 1) =
      (-1 : ℝ)^i.val * Matrix.det (fun j k => v j (i.succAbove k)) :=
  det_cons_unit v i
lemma facetForm_column_zero {n : ℕ} (v : Fin n → (Fin (n+1) → ℝ))
    (i : Fin (n+1)) (hi : ∀ j, v j i = 0) (k : Fin (n+1)) (hki : k ≠ i) :
    facetForm n v (Pi.single k 1) = 0 := by
  rw [facetForm_apply]
  apply Matrix.det_eq_zero_of_column_eq_zero i
  intro j
  cases j using Fin.cases with
  | zero => simp [hki.symm]
  | succ j => exact hi j
lemma linearMap_eq_coord_of_units {n : ℕ} (f : (Fin n → ℝ) →ₗ[ℝ] ℝ)
    (i : Fin n) (hf : ∀ k, k ≠ i → f (Pi.single k 1) = 0) (x : Fin n → ℝ) :
    f x = x i * f (Pi.single i 1) := by
  have hx : x = ∑ k : Fin n, x k • Pi.single k 1 := by
    funext j
    simp [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.single_apply]
  have hh := congrArg f hx
  rw [map_sum] at hh
  simp only [map_smul,smul_eq_mul] at hh
  rw [hh,Finset.sum_eq_single i]
  · intro k _ hki
    simp [hf k hki]
  · simp
lemma facet_boundary_term {n : ℕ} (v : Fin n → (Fin (n+1) → ℝ)) (i : Fin (n+1)) :
    (if ∀ k, k ≠ i → facetForm n v (Pi.single k 1) = 0
       then Real.sign (facetForm n v (Pi.single i 1)) else 0) =
    (if ∀ j, v j i = 0 then
       (-1 : ℝ)^i.val * Real.sign (Matrix.det (fun j k => v j (i.succAbove k))) else 0) := by
  by_cases hi : ∀ j, v j i = 0
  · rw [ite_eq_left hi,ite_eq_left (fun k hki => facetForm_column_zero v i hi k hki),
      facetForm_on_unit,realSign_negOnePow_mul]
  · rw [ite_eq_right hi]
    split_ifs with hf
    · have hz : facetForm n v (Pi.single i 1) = 0 := by
        by_contra hn
        apply hi
        intro j
        have h := linearMap_eq_coord_of_units (facetForm n v) i hf (v j)
        rw [facetForm_vertex] at h
        exact (mul_eq_zero.mp h.symm).resolve_right hn
      simp only [hz,Real.sign_zero]
    · rfl
end Sparse.Orientation
namespace Fundamental
open scoped BigOperators
open OrientedIncidence Oriented ChainHomotopy Sparse.Orientation
variable {V : Type*} [LinearOrder V] {n : ℕ}
def chain (F : Finset (Set.powersetCard V (n+1))) (p : V → (Fin (n+1) → ℝ)) :
    Oriented.Degree V (n+1) :=
  ∑ s ∈ F, (Real.sign (Matrix.det (fun i => p (vertices s i))) : ℂ) • basis (n+1) s
lemma boundary_coefficient (F : Finset (Set.powersetCard V (n+1)))
    (p : V → (Fin (n+1) → ℝ)) (t : Set.powersetCard V n) :
    (basis n).repr (d n (chain F p)) t =
      ∑ u ∈ apexes F t, (Real.sign (facetForm n (fun i => p (vertices t i)) (p u)) : ℂ) := by
  rw [chain,boundary_sum_coefficient]
  rw [← sum_incidencePairs F t]
  apply Finset.sum_congr rfl
  intro a ha
  have ht := (Finset.mem_filter.mp ha).2
  rw [determinant_deletion_orientation]
  congr 2
  rw [facetForm_apply]
  congr 1
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i =>
    simp only [Fin.cons_succ]
    have h := congrArg (fun e : Fin n ↪o V => e i) (vertices_eraseFace a.1 a.2)
    rw [ht] at h
    exact congrArg p h.symm
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
lemma exists_weights_of_mem_affineSpan {s : Finset E} {v : E}
    (hv : v ∈ affineSpan ℝ (s : Set E)) :
    ∃ w : E → ℝ, ∑ x ∈ s, w x = 1 ∧ v = ∑ x ∈ s, w x • x := by
  classical
  have hv' : v ∈ affineSpan ℝ (Set.range (fun x : s => (x : E))) := by simpa using hv
  obtain ⟨w, hw, hvw⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype hv'
  let w' : E → ℝ := fun x => if h : x ∈ s then w ⟨x, h⟩ else 0
  have hsum : ∑ x ∈ s, w' x = ∑ x : s, w x := by
    rw [← Finset.sum_attach]
    simp [w']
  refine ⟨w', hsum.trans hw, ?_⟩
  rw [Finset.affineCombination_eq_linear_combination _ _ _ hw] at hvw
  rw [← Finset.sum_attach]
  simpa [w'] using hvw
lemma exists_small_positive_weights {I : Type*} (s : Finset I) (w : I → ℝ)
    {c : ℝ} (hc : 0 < c) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ i ∈ s, 0 < δ * w i + (1-δ) * c := by
  have he : ∀ᶠ δ : ℝ in 𝓝 0, ∀ i ∈ s, 0 < δ * w i + (1-δ) * c := by
    apply (s.eventually_all).mpr
    intro i _
    have hcont : Continuous (fun δ : ℝ => δ * w i + (1-δ) * c) := by fun_prop
    exact hcont.continuousAt.eventually (eventually_gt_nhds (by simpa using hc))
  have he' := he.filter_mono (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  have hlt := (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono
    (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  have hpos : ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 < δ := self_mem_nhdsWithin
  exact (hpos.and (hlt.and he')).exists
lemma sum_weights_mem_convexHull (s : Finset E) {w : E → ℝ}
    (hw : ∀ x ∈ s, 0 ≤ w x) (hsum : ∑ x ∈ s, w x = 1) :
    ∑ x ∈ s, w x • x ∈ convexHull ℝ (s : Set E) :=
  (convex_convexHull ℝ (s : Set E)).sum_mem hw hsum
    (fun _ hx => subset_convexHull ℝ (s : Set E) hx)
end
section
open Set Finset
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
lemma same_side_cone_overlap [DecidableEq E] {F : Finset E} (hF : F.Nonempty) {u v : E}
    (huF : u ∉ F) (hvspan : v ∈ affineSpan ℝ ((insert u F : Finset E) : Set E))
    (f : E →ₗ[ℝ] ℝ) (b : ℝ) (hFb : ∀ x ∈ F, f x = b)
    (hu : b < f u) (hv : b < f v) :
    ∃ p, p ∈ convexHull ℝ ((insert u F : Finset E) : Set E) ∧
      p ∈ convexHull ℝ ((insert v F : Finset E) : Set E) ∧ b < f p := by
  classical
  obtain ⟨w, hw, hvw⟩ := exists_weights_of_mem_affineSpan hvspan
  have hsum : w u + ∑ x ∈ F, w x = 1 := by simpa [Finset.sum_insert huF] using hw
  have hfv : f v = w u * f u + (∑ x ∈ F, w x) * b := by
    rw [hvw, map_sum, Finset.sum_insert huF]
    simp only [map_smul, smul_eq_mul]
    rw [Finset.sum_congr rfl (fun x hx => congrArg (w x * ·) (hFb x hx))]
    rw [Finset.sum_mul]
  have hwu : 0 < w u := by
    have he : f v - b = w u * (f u - b) := by linear_combination hfv + b * hsum
    have hm : 0 < w u * (f u - b) := he ▸ sub_pos.mpr hv
    exact (mul_pos_iff_of_pos_right (sub_pos.mpr hu)).mp hm
  let c : ℝ := (F.card : ℝ)⁻¹
  have hc : 0 < c := inv_pos.mpr (Nat.cast_pos.mpr hF.card_pos)
  have hcsum : ∑ _x ∈ F, c = 1 := by
    simp [c, ne_of_gt (Nat.cast_pos.mpr hF.card_pos : (0 : ℝ) < F.card)]
  let q : E := ∑ x ∈ F, c • x
  have hq : q ∈ convexHull ℝ (F : Set E) :=
    sum_weights_mem_convexHull F (fun _ _ => hc.le) hcsum
  have hfq : f q = b := by
    change f (∑ x ∈ F, c • x) = b
    simp only [map_sum, map_smul, smul_eq_mul]
    rw [Finset.sum_congr rfl (fun x hx => congrArg (c * ·) (hFb x hx)),
      ← Finset.sum_mul, hcsum, one_mul]
  obtain ⟨δ, hδ, hδ1, hδw⟩ := exists_small_positive_weights F w hc
  let r : E → ℝ := fun x => if x = u then 0 else c
  have hrF (x : E) (hx : x ∈ F) : r x = c := by
    simp [r, ne_of_mem_of_not_mem hx huF]
  have hru : r u = 0 := by simp [r]
  have hrsum : ∑ x ∈ insert u F, r x = 1 := by
    rw [Finset.sum_insert huF, hru, zero_add]
    rw [Finset.sum_congr rfl hrF]
    exact hcsum
  have hrq : ∑ x ∈ insert u F, r x • x = q := by
    rw [Finset.sum_insert huF, hru, zero_smul, zero_add]
    exact Finset.sum_congr rfl (fun x hx => by rw [hrF x hx])
  let z : E → ℝ := fun x => δ * w x + (1-δ) * r x
  have hz : ∀ x ∈ insert u F, 0 ≤ z x := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · simp only [z, hru, mul_zero, add_zero]
      exact (mul_pos hδ hwu).le
    · simpa only [z, hrF x hx] using (hδw x hx).le
  have hzsum : ∑ x ∈ insert u F, z x = 1 := by
    simp only [z, Finset.sum_add_distrib, ← Finset.mul_sum, hw, hrsum]
    ring
  have hzp : ∑ x ∈ insert u F, z x • x = δ • v + (1-δ) • q := by
    simp only [z, add_smul, mul_smul, Finset.sum_add_distrib, ← Finset.smul_sum]
    rw [← hvw, hrq]
  refine ⟨δ • v + (1-δ) • q, ?_, ?_, ?_⟩
  · rw [← hzp]
    exact sum_weights_mem_convexHull _ hz hzsum
  · apply (convex_convexHull ℝ ((insert v F : Finset E) : Set E))
      (subset_convexHull ℝ _ (Finset.mem_insert_self v F))
      ((convexHull_mono (show (F : Set E) ⊆ ((insert v F : Finset E) : Set E) from
        Finset.subset_insert _ _)) hq) hδ.le (sub_nonneg.mpr hδ1.le)
    ring
  · simp only [map_add, map_smul, smul_eq_mul, hfq]
    nlinarith [mul_pos hδ (sub_pos.mpr hv)]
end
section
open Set Finset
open scoped Classical
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
lemma apex_notMem_affineSpan {F : Finset E} {u : E} (hu : u ∉ F)
    (h : AffineIndependent ℝ ((↑) : ↥(insert u F) → E)) :
    u ∉ affineSpan ℝ (F : Set E) := by
  let i : ↥(insert u F) := ⟨u, Finset.mem_insert_self _ _⟩
  have hnot := h.notMem_affineSpan_sdiff i Set.univ
  have he : ((↑) : ↥(insert u F) → E) '' (Set.univ \ {i}) = (F : Set E) := by
    ext x
    constructor
    · rintro ⟨j, hj, rfl⟩
      rcases Finset.mem_insert.mp j.property with hj' | hj'
      · exact False.elim (hj.2 (Set.mem_singleton_iff.mpr (Subtype.ext hj')))
      · exact hj'
    · intro hx
      refine ⟨⟨x, Finset.mem_insert_of_mem hx⟩, ⟨Set.mem_univ _, ?_⟩, rfl⟩
      intro hi
      have hxu : x = u := congrArg Subtype.val (Set.mem_singleton_iff.mp hi)
      exact hu (hxu ▸ hx)
  simpa only [he] using hnot
lemma exists_facet_form {F : Finset E} (hF : F.Nonempty) {u : E}
    (hu : u ∉ affineSpan ℝ (F : Set E)) :
    ∃ (f : E →ₗ[ℝ] ℝ) (b : ℝ), (∀ x ∈ F, f x = b) ∧ f u ≠ b := by
  obtain ⟨a, ha⟩ := hF
  have has : a ∈ affineSpan ℝ (F : Set E) := subset_affineSpan ℝ _ ha
  have hua : u - a ∉ (affineSpan ℝ (F : Set E)).direction := by
    simpa only [← AffineSubspace.vsub_right_mem_direction_iff_mem has u,
      vsub_eq_sub] using hu
  obtain ⟨f, hfu, hfker⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hua inferInstance
  refine ⟨f, f a, ?_, ?_⟩
  · intro x hx
    have hxa : x - a ∈ (affineSpan ℝ (F : Set E)).direction :=
      (AffineSubspace.vsub_right_mem_direction_iff_mem has x).mpr
        (subset_affineSpan ℝ _ hx)
    have hz : f (x-a) = 0 := by
      have hm : f (x-a) ∈ (affineSpan ℝ (F : Set E)).direction.map f :=
        Submodule.mem_map.mpr ⟨x-a, hxa, rfl⟩
      rw [hfker, Submodule.mem_bot] at hm
      exact hm
    simpa only [map_sub, sub_eq_zero] using hz
  · simpa only [map_sub, sub_ne_zero] using hfu
lemma affineForm_eq_on_convexHull {F : Finset E} (f : E →ₗ[ℝ] ℝ) (b : ℝ)
    (h : ∀ x ∈ F, f x = b) {p : E} (hp : p ∈ convexHull ℝ (F : Set E)) : f p = b := by
  have he : (F : Set E).EqOn f.toAffineMap (AffineMap.const ℝ E b) := h
  exact AffineMap.eqOn_affineSpan he (convexHull_subset_affineSpan _ hp)
lemma eq_of_facet_same_side (K : Geometry.SimplicialComplex ℝ E)
    {F : Finset E} (hF : F.Nonempty) {u v : E} (huF : u ∉ F) (hvF : v ∉ F)
    (huK : insert u F ∈ K.faces) (hvK : insert v F ∈ K.faces)
    (hspan : v ∈ affineSpan ℝ ((insert u F : Finset E) : Set E))
    (f : E →ₗ[ℝ] ℝ) (b : ℝ) (hFb : ∀ x ∈ F, f x = b)
    (hu : b < f u) (hv : b < f v) : u = v := by
  by_contra huv
  obtain ⟨p, hpu, hpv, hp⟩ := same_side_cone_overlap hF huF hspan f b hFb hu hv
  have hinter : ((insert u F : Finset E) : Set E) ∩
      ((insert v F : Finset E) : Set E) = (F : Set E) := by
    ext x
    simp only [Finset.coe_insert, Set.mem_inter_iff, Set.mem_insert_iff]
    aesop
  have hpf := K.inter_subset_convexHull huK hvK ⟨hpu, hpv⟩
  rw [hinter] at hpf
  exact (ne_of_gt hp) (affineForm_eq_on_convexHull f b hFb hpf)
lemma facet_apex_card_le_two (K : Geometry.SimplicialComplex ℝ E)
    {F A : Finset E} (hF : F.Nonempty)
    (hAK : ∀ u ∈ A, insert u F ∈ K.faces) (hAF : ∀ u ∈ A, u ∉ F)
    (hcarrier : ∀ u ∈ A, ∀ v ∈ A,
      affineSpan ℝ ((insert u F : Finset E) : Set E) =
        affineSpan ℝ ((insert v F : Finset E) : Set E)) : A.card ≤ 2 := by
  rcases A.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
  · simp
  obtain ⟨f, b, hFb, hab⟩ := exists_facet_form hF
    (apex_notMem_affineSpan (hAF a ha) (K.indep (hAK a ha)))
  have hne (u : E) (hu : u ∈ A) : f u ≠ b := by
    intro hub
    have hon : ((insert u F : Finset E) : Set E).EqOn
        f.toAffineMap (AffineMap.const ℝ E b) := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hub
      · exact hFb x hx
    have he := AffineMap.eqOn_affineSpan hon
    apply hab
    apply he
    rw [hcarrier u hu a ha]
    exact subset_affineSpan ℝ _ (Finset.mem_insert_self _ _)
  let side : A → Bool := fun u => decide (b < f u)
  have hinj : Function.Injective side := by
    intro u v huv
    apply Subtype.ext
    have hs : (b < f u) ↔ (b < f v) := by
      exact decide_eq_decide.mp huv
    have hspan : (v : E) ∈ affineSpan ℝ ((insert (u : E) F : Finset E) : Set E) := by
      rw [hcarrier u u.property v v.property]
      exact subset_affineSpan ℝ _ (Finset.mem_insert_self _ _)
    by_cases hu : b < f u
    · exact eq_of_facet_same_side K hF (hAF u u.property) (hAF v v.property)
        (hAK u u.property) (hAK v v.property) hspan f b hFb hu (hs.mp hu)
    · have hv : ¬ b < f v := fun hv => hu (hs.mpr hv)
      have hul : f u < b := lt_of_le_of_ne (le_of_not_gt hu) (hne u u.property)
      have hvl : f v < b := lt_of_le_of_ne (le_of_not_gt hv) (hne v v.property)
      exact eq_of_facet_same_side K hF (hAF u u.property) (hAF v v.property)
        (hAK u u.property) (hAK v v.property) hspan (-f) (-b)
        (fun x hx => congrArg Neg.neg (hFb x hx))
        (neg_lt_neg hul) (neg_lt_neg hvl)
  simpa using Fintype.card_le_of_injective side hinj
lemma affineSpan_eq_of_card_eq {s t : Finset E}
    (ht : AffineIndependent ℝ ((↑) : t → E))
    (hst : (t : Set E) ⊆ convexHull ℝ (s : Set E)) (hc : t.card = s.card) :
    affineSpan ℝ (t : Set E) = affineSpan ℝ (s : Set E) := by
  have hle : affineSpan ℝ (t : Set E) ≤ affineSpan ℝ (s : Set E) :=
    affineSpan_le.mpr (hst.trans (convexHull_subset_affineSpan _))
  by_contra hne
  have hlt := ht.card_lt_card_of_affineSpan_lt_affineSpan (lt_of_le_of_ne hle hne)
  omega
lemma facet_coface_card_le_two (K : Geometry.SimplicialComplex ℝ E)
    {F S : Finset E} {B : Finset (Finset E)} (hF : F.Nonempty)
    (hS : S.card = F.card + 1) (hB : ∀ t ∈ B, t ∈ K.faces)
    (hFB : ∀ t ∈ B, F ⊆ t ∧ t.card = F.card + 1)
    (hBS : ∀ t ∈ B, (t : Set E) ⊆ convexHull ℝ (S : Set E)) : B.card ≤ 2 := by
  have hex (t : B) : ∃ u ∉ F, insert u F = (t : Finset E) :=
    Finset.exists_eq_insert_iff.mpr ⟨(hFB t t.property).1, (hFB t t.property).2.symm⟩
  let apex : B → E := fun t => (hex t).choose
  have ha (t : B) : apex t ∉ F ∧ insert (apex t) F = (t : Finset E) :=
    (hex t).choose_spec
  let A : Finset E := Finset.univ.image apex
  have hAK : ∀ u ∈ A, insert u F ∈ K.faces := by
    intro u hu
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hu
    rw [(ha t).2]
    exact hB t t.property
  have hAF : ∀ u ∈ A, u ∉ F := by
    intro u hu
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hu
    exact (ha t).1
  have hsp (u : E) (hu : u ∈ A) :
      affineSpan ℝ ((insert u F : Finset E) : Set E) = affineSpan ℝ (S : Set E) := by
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hu
    rw [(ha t).2]
    exact affineSpan_eq_of_card_eq (K.indep (hB t t.property)) (hBS t t.property)
      ((hFB t t.property).2.trans hS.symm)
  have hA := facet_apex_card_le_two K hF hAK hAF
    (fun u hu v hv => (hsp u hu).trans (hsp v hv).symm)
  have hinj : Function.Injective apex := by
    intro t t' he
    apply Subtype.ext
    calc (t : Finset E) = insert (apex t) F := (ha t).2.symm
         _ = insert (apex t') F := by rw [he]
         _ = (t' : Finset E) := (ha t').2
  have hc : A.card = B.card := by simp [A, Finset.card_image_of_injective _ hinj]
  rwa [hc] at hA
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
lemma eventually_coface_at_positivePoint (K : Geometry.SimplicialComplex ℝ E)
    (hK : K.faces.Finite) {F : Finset E} (hF : F ∈ K.faces)
    (w : E → ℝ) (hw : ∀ x ∈ F, 0 < w x) (hws : ∑ x ∈ F, w x = 1) :
    ∀ᶠ q in 𝓝 (∑ x ∈ F, w x • x),
      ∀ T ∈ K.faces, q ∈ convexHull ℝ (T : Set E) → F ⊆ T := by
  classical
  apply (hK.eventually_all).mpr
  intro T hT
  by_cases hFT : F ⊆ T
  · exact Filter.Eventually.of_forall (fun _ _ => hFT)
  · have hnot : (∑ x ∈ F, w x • x) ∉ convexHull ℝ (T : Set E) := by
      intro hq
      exact hFT (simplex_contains_positivePoint K hF hT w hw hws hq)
    have hc : IsClosed (convexHull ℝ (T : Set E)) := (T.finite_toSet.isCompact_convexHull ℝ).isClosed
    have he : ∀ᶠ q in 𝓝 (∑ x ∈ F, w x • x), q ∉ convexHull ℝ (T : Set E) :=
      hc.isOpen_compl.mem_nhds hnot
    exact he.mono (fun _ hq hh => False.elim (hq hh))
end
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
theorem exists_facet_coface_on_side (K : Geometry.SimplicialComplex ℝ E)
    (hK : K.faces.Finite) (hconv : Convex ℝ K.space)
    {F : Finset E} (hF : F ∈ K.faces)
    (hdim : ∀ T ∈ K.faces, T.card ≤ F.card+1)
    (f : E →ₗ[ℝ] ℝ) (b : ℝ) (hFb : ∀ x ∈ F, f x = b)
    {v : E} (hv : v ∈ K.space) (hfv : b < f v) :
    ∃ u ∉ F, insert u F ∈ K.faces ∧ b < f u := by
  classical
  have hFn := K.nonempty_of_mem_faces hF
  let c : ℝ := (F.card : ℝ)⁻¹
  have hc : 0 < c := inv_pos.mpr (Nat.cast_pos.mpr hFn.card_pos)
  have hcs : ∑ _x ∈ F, c = 1 := by
    simp [c,ne_of_gt (Nat.cast_pos.mpr hFn.card_pos : (0:ℝ) < F.card)]
  let q : E := ∑ x ∈ F, c • x
  have hqF : q ∈ convexHull ℝ (F : Set E) :=
    sum_weights_mem_convexHull F (fun _ _ => hc.le) hcs
  have hfq : f q = b := affineForm_eq_on_convexHull f b hFb hqF
  have hev := eventually_coface_at_positivePoint K hK hF (fun _ => c) (fun _ _ => hc) hcs
  have hcont : Continuous (fun δ : ℝ => δ • v + (1-δ) • q) := by fun_prop
  have hlim : Filter.Tendsto (fun δ : ℝ => δ • v + (1-δ) • q) (𝓝 0) (𝓝 q) := by
    simpa using hcont.continuousAt.tendsto (x := 0)
  have he := (hlim.eventually hev).filter_mono (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
  have hlt := (eventually_lt_nhds (show (0:ℝ)<1 by norm_num)).filter_mono
    (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
  have hpos : ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 < δ := self_mem_nhdsWithin
  obtain ⟨δ,hδ,hδ1,hδK⟩ := (hpos.and (hlt.and he)).exists
  have hδq : δ • v + (1-δ) • q ∈ K.space :=
    hconv hv (K.convexHull_subset_space hF hqF) hδ.le (sub_nonneg.mpr hδ1.le) (by ring)
  have hfδ : b < f (δ • v + (1-δ) • q) := by
    simp only [map_add,map_smul,smul_eq_mul,hfq]
    nlinarith [mul_pos hδ (sub_pos.mpr hfv)]
  obtain ⟨T,hT,hδT⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hδq
  have hFT := hδK T hT hδT
  have hne : F ≠ T := by
    intro heq
    subst T
    have heq := affineForm_eq_on_convexHull f b hFb hδT
    exact (ne_of_gt hfδ) heq
  have hcT : F.card+1 = T.card := by
    have hltc := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hFT,hne⟩)
    have hh := hdim T hT
    omega
  obtain ⟨u,hu,rfl⟩ := Finset.exists_eq_insert_iff.mpr ⟨hFT,hcT⟩
  refine ⟨u,hu,hT,?_⟩
  by_contra hfu
  have hleft : convexHull ℝ ((insert u F : Finset E) : Set E) ⊆ {x | f x ≤ b} := by
    apply convexHull_min _ (convex_halfSpace_le f.isLinear b)
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact le_of_not_gt hfu
    · exact (hFb x hx).le
  exact (not_le_of_gt hfδ) (hleft hδT)
end
section
open Set Finset
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
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
    have he : (S ∩ {x | f x = b}).EqOn f.toAffineMap (AffineMap.const ℝ E b) := fun _ hy => hy.2
    exact AffineMap.eqOn_affineSpan he (convexHull_subset_affineSpan _ hx)
end
open Set Finset
open scoped Classical
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma full_face_affineSpan (K : Geometry.SimplicialComplex ℝ E) {S T : Finset E}
    (hspace : K.space ⊆ convexHull ℝ (S : Set E)) (hT : T ∈ K.faces)
    (hc : T.card = S.card) : affineSpan ℝ (T : Set E) = affineSpan ℝ (S : Set E) :=
  affineSpan_eq_of_card_eq (K.indep hT) ((subset_convexHull ℝ _).trans
    ((K.convexHull_subset_space hT).trans hspace)) hc
def facetApexes (K : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (F : Finset E) : Finset E :=
  (hK.toFinset.biUnion id).filter (fun u => u ∉ F ∧ insert u F ∈ K.faces)
@[simp] lemma mem_facetApexes (K : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (F : Finset E) (u : E) : u ∈ facetApexes K hK F ↔ u ∉ F ∧ insert u F ∈ K.faces := by
  simp only [facetApexes,Finset.mem_filter,Finset.mem_biUnion,Set.Finite.mem_toFinset,id_eq]
  exact ⟨fun h => h.2,fun h => ⟨⟨insert u F,h.2,Finset.mem_insert_self _ _⟩,h⟩⟩
lemma parent_card_bound (K : Geometry.SimplicialComplex ℝ E) {S : Finset E}
    (hspace : K.space ⊆ convexHull ℝ (S : Set E)) :
    ∀ T ∈ K.faces, T.card ≤ S.card := by
  intro T hT
  exact (K.indep hT).card_le_card_of_subset_affineSpan ((subset_convexHull ℝ _).trans
    ((K.convexHull_subset_space hT).trans (hspace.trans (convexHull_subset_affineSpan _))))
lemma facet_positive_apex_card (K : Geometry.SimplicialComplex ℝ E)
    (hK : K.faces.Finite) {S F : Finset E}
    (hspace : K.space = convexHull ℝ (S : Set E)) (hF : F ∈ K.faces)
    (hc : F.card+1 = S.card) (f : E →ₗ[ℝ] ℝ) (b : ℝ)
    (hFb : ∀ x ∈ F, f x = b) :
    ((facetApexes K hK F).filter (fun u => b < f u)).card =
      if ∃ v ∈ S, b < f v then 1 else 0 := by
  let A := (facetApexes K hK F).filter (fun u => b < f u)
  have hAc : A.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro u hu v hv
    obtain ⟨huA,hu⟩ := Finset.mem_filter.mp hu
    obtain ⟨hvA,hv⟩ := Finset.mem_filter.mp hv
    obtain ⟨huF,huK⟩ := (mem_facetApexes K hK F u).mp huA
    obtain ⟨hvF,hvK⟩ := (mem_facetApexes K hK F v).mp hvA
    apply eq_of_facet_same_side K (K.nonempty_of_mem_faces hF) huF hvF huK hvK _ f b hFb hu hv
    rw [full_face_affineSpan K hspace.subset huK (by simp [Finset.card_insert_of_notMem huF,hc])]
    exact convexHull_subset_affineSpan _ (hspace ▸ K.convexHull_subset_space hvK
      (subset_convexHull ℝ _ (Finset.mem_insert_self _ _)))
  have hAn : A.Nonempty ↔ ∃ v ∈ S, b < f v := by
    constructor
    · rintro ⟨u,hu⟩
      obtain ⟨huA,hu⟩ := Finset.mem_filter.mp hu
      have huK := ((mem_facetApexes K hK F u).mp huA).2
      by_contra hn
      push Not at hn
      have hh : convexHull ℝ (S : Set E) ⊆ {x | f x ≤ b} :=
        convexHull_min hn (convex_halfSpace_le f.isLinear b)
      exact (not_le_of_gt hu) (hh (hspace ▸ K.convexHull_subset_space huK
        (subset_convexHull ℝ _ (Finset.mem_insert_self _ _))))
    · rintro ⟨v,hv,hfv⟩
      obtain ⟨u,hu,huK,hfu⟩ := exists_facet_coface_on_side K hK
        (hspace.symm ▸ convex_convexHull ℝ (S : Set E)) hF
        (fun T hT => hc ▸ parent_card_bound K hspace.subset T hT) f b hFb
        (hspace.symm ▸ subset_convexHull ℝ (S : Set E) hv) hfv
      exact ⟨u,Finset.mem_filter.mpr ⟨(mem_facetApexes K hK F u).mpr ⟨hu,huK⟩,hfu⟩⟩
  change A.card = _
  split_ifs with h
  · have := (hAn.mpr h).card_pos
    omega
  · have := not_congr hAn |>.mpr h
    simp only [Finset.not_nonempty_iff_eq_empty.mp this,Finset.card_empty]
end BassTrace.Sparse
end
end OAI

end
section
namespace OAI
noncomputable section
namespace BassTrace
namespace Sparse
open Set Finset
open scoped Classical
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma sum_real_sign {A : Finset E} (f : E → ℝ) :
    ∑ u ∈ A, Real.sign (f u) =
      ((A.filter (fun u => 0 < f u)).card : ℝ) - ((A.filter (fun u => f u < 0)).card : ℝ) := by
  have he (u : E) : Real.sign (f u) =
      (if 0 < f u then (1 : ℝ) else 0) - (if f u < 0 then 1 else 0) := by
    rcases lt_trichotomy (f u) 0 with h | h | h
    · simp [Real.sign_of_neg h,h,not_lt_of_ge h.le]
    · simp [h]
    · simp [Real.sign_of_pos h,h,not_lt_of_ge h.le]
  simp_rw [he]
  rw [Finset.sum_sub_distrib,Finset.sum_boole,Finset.sum_boole]
lemma signed_facet_incidence (K : Geometry.SimplicialComplex ℝ E)
    (hK : K.faces.Finite) {S F : Finset E}
    (hspace : K.space = convexHull ℝ (S : Set E)) (hF : F ∈ K.faces)
    (hc : F.card+1 = S.card) (f : E →ₗ[ℝ] ℝ) (b : ℝ)
    (hFb : ∀ x ∈ F, f x = b) :
    ∑ u ∈ facetApexes K hK F, Real.sign (f u-b) =
      (if ∃ v ∈ S, b < f v then (1:ℝ) else 0) -
      (if ∃ v ∈ S, f v < b then (1:ℝ) else 0) := by
  rw [sum_real_sign]
  simp only [sub_pos,sub_neg]
  rw [facet_positive_apex_card K hK hspace hF hc f b hFb]
  have hn := facet_positive_apex_card K hK hspace hF hc (-f) (-b)
    (fun x hx => by simp [hFb x hx])
  simp only [LinearMap.neg_apply,neg_lt_neg_iff] at hn
  rw [hn]
  split_ifs <;> norm_num
lemma one_sided_parent_unique {S F : Finset E}
    (hF : AffineIndependent ℝ ((↑) : F → E)) (hc : F.card+1 = S.card)
    (hFS : (F : Set E) ⊆ convexHull ℝ (S : Set E))
    (f : E →ₗ[ℝ] ℝ) (b : ℝ) (hFb : ∀ x ∈ F, f x = b)
    (hSb : ∀ x ∈ S, f x ≤ b) (hne : ∃ x ∈ S, f x ≠ b) :
    ∃! v, v ∈ S ∧ f v ≠ b := by
  let T := S.filter (fun x => f x = b)
  have hFT : (F : Set E) ⊆ convexHull ℝ (T : Set E) := by
    intro x hx
    have hh : x ∈ convexHull ℝ (S : Set E) ∩ {x | f x = b} := ⟨hFS hx,hFb x hx⟩
    rw [convexHull_inter_supporting (S : Set E) f b hSb] at hh
    have heq : (S : Set E) ∩ {x | f x = b} = (T : Set E) := by
      ext y
      simp only [T,Set.mem_inter_iff,Set.mem_ofPred,Finset.mem_coe,Finset.mem_filter]
    rw [heq] at hh
    exact hh
  have hcard := hF.card_le_card_of_subset_affineSpan (hFT.trans (convexHull_subset_affineSpan _))
  have hcount := Finset.card_filter_add_card_filter_not (s := S) (fun x => f x = b)
  have hnot : (S.filter (fun x => f x ≠ b)).Nonempty := by
    obtain ⟨x,hx,hnx⟩ := hne
    exact ⟨x,Finset.mem_filter.mpr ⟨hx,hnx⟩⟩
  have hone : (S.filter (fun x => f x ≠ b)).card = 1 := by
    have := hnot.card_pos
    change T.card + (S.filter (fun x => f x ≠ b)).card = S.card at hcount
    omega
  obtain ⟨v,hv⟩ := Finset.card_eq_one.mp hone
  refine ⟨v,?_,?_⟩
  · have : v ∈ S.filter (fun x => f x ≠ b) := hv ▸ Finset.mem_singleton_self v
    exact Finset.mem_filter.mp this
  · intro w hw
    have : w ∈ S.filter (fun x => f x ≠ b) := Finset.mem_filter.mpr hw
    rw [hv,Finset.mem_singleton] at this
    exact this
end
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma parent_boundary_sign_sum {S F : Finset E}
    (hF : AffineIndependent ℝ ((↑) : F → E)) (hc : F.card+1 = S.card)
    (hFS : (F : Set E) ⊆ convexHull ℝ (S : Set E))
    (f : E →ₗ[ℝ] ℝ) (b : ℝ) (hFb : ∀ x ∈ F, f x = b) :
    ∑ v ∈ S, (if ∀ w ∈ S, w ≠ v → f w = b then Real.sign (f v-b) else 0) =
      (if ∃ v ∈ S, b < f v then (1:ℝ) else 0) -
      (if ∃ v ∈ S, f v < b then (1:ℝ) else 0) := by
  by_cases hp : ∃ v ∈ S, b < f v
  · obtain ⟨p,hpS,hpv⟩ := hp
    by_cases hn : ∃ v ∈ S, f v < b
    · obtain ⟨q,hqS,hqv⟩ := hn
      have hpq : p ≠ q := by intro h; subst q; linarith
      have hz (v : E) (_ : v ∈ S) :
          (if ∀ w ∈ S, w ≠ v → f w = b then Real.sign (f v-b) else 0) = 0 := by
        have hh : ¬ ∀ w ∈ S, w ≠ v → f w = b := by
          intro hh
          by_cases hv : p = v
          · have := hh q hqS (by simpa [← hv] using hpq.symm)
            linarith
          · have := hh p hpS hv
            linarith
        simp only [hh,ite_false]
      rw [Finset.sum_eq_zero hz]
      simp only [show ∃ v ∈ S, b < f v from ⟨p,hpS,hpv⟩,
        show ∃ v ∈ S, f v < b from ⟨q,hqS,hqv⟩,ite_true,sub_self]
    · have hs : ∀ w ∈ S, b ≤ f w := by
        intro w hw
        exact le_of_not_gt (fun hh => hn ⟨w,hw,hh⟩)
      obtain ⟨v,⟨hv,hvn⟩,huniq⟩ := one_sided_parent_unique hF hc hFS (-f) (-b)
        (fun x hx => by simp [hFb x hx])
        (fun x hx => by simpa only [LinearMap.neg_apply,neg_le_neg_iff] using hs x hx)
        ⟨p,hpS,by intro he; have hh : -f p = -b := he; linarith⟩
      have hvp : b < f v := by
        have hvne : f v ≠ b := by intro he; apply hvn; simp only [LinearMap.neg_apply,he]
        exact lt_of_le_of_ne (hs v hv) hvne.symm
      have hzero (w : E) (hw : w ∈ S) (hwv : w ≠ v) : f w = b := by
        by_contra hh
        exact hwv (huniq w ⟨hw,by intro he; have he : -f w = -b := he; exact hh (by linarith)⟩)
      rw [Finset.sum_eq_single v]
      · rw [ite_eq_left hzero]
        simp only [ite_true,Real.sign_of_pos (sub_pos.mpr hvp),
          show ∃ v ∈ S, b < f v from ⟨p,hpS,hpv⟩,hn,ite_false,sub_zero]
      · intro w hw hwv
        simp only [hzero w hw hwv,sub_self,Real.sign_zero,ite_self]
      · exact fun hh => (hh hv).elim
  · by_cases hn : ∃ v ∈ S, f v < b
    · obtain ⟨q,hqS,hqv⟩ := hn
      have hs : ∀ w ∈ S, f w ≤ b := by
        intro w hw
        exact le_of_not_gt (fun hh => hp ⟨w,hw,hh⟩)
      obtain ⟨v,⟨hv,hvn⟩,huniq⟩ := one_sided_parent_unique hF hc hFS f b hFb hs
        ⟨q,hqS,ne_of_lt hqv⟩
      have hvn : f v < b := lt_of_le_of_ne (hs v hv) hvn
      have hzero (w : E) (hw : w ∈ S) (hwv : w ≠ v) : f w = b := by
        by_contra hh
        exact hwv (huniq w ⟨hw,hh⟩)
      rw [Finset.sum_eq_single v]
      · rw [ite_eq_left hzero]
        simp only [ite_true,Real.sign_of_neg (sub_neg.mpr hvn),hp,
          show ∃ v ∈ S, f v < b from ⟨q,hqS,hqv⟩,ite_false,zero_sub]
      · intro w hw hwv
        simp only [hzero w hw hwv,sub_self,Real.sign_zero,ite_self]
      · exact fun hh => (hh hv).elim
    · have hs (w : E) (hw : w ∈ S) : f w = b :=
        le_antisymm (le_of_not_gt (fun hh => hp ⟨w,hw,hh⟩))
          (le_of_not_gt (fun hh => hn ⟨w,hw,hh⟩))
      rw [Finset.sum_eq_zero (fun w hw => by
        simp only [hs w hw,sub_self,Real.sign_zero,ite_self])]
      simp only [hp,hn,ite_false,sub_self]
lemma signed_facet_boundary (K : Geometry.SimplicialComplex ℝ E)
    (hK : K.faces.Finite) {S F : Finset E}
    (hspace : K.space = convexHull ℝ (S : Set E)) (hF : F ∈ K.faces)
    (hc : F.card+1 = S.card) (f : E →ₗ[ℝ] ℝ) (b : ℝ)
    (hFb : ∀ x ∈ F, f x = b) :
    ∑ u ∈ facetApexes K hK F, Real.sign (f u-b) =
      ∑ v ∈ S, (if ∀ w ∈ S, w ≠ v → f w = b then Real.sign (f v-b) else 0) := by
  rw [signed_facet_incidence K hK hspace hF hc f b hFb]
  symm
  exact parent_boundary_sign_sum (K.indep hF) hc
    (fun x hx => hspace ▸ K.convexHull_subset_space hF (subset_convexHull ℝ _ hx)) f b hFb
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
omit [LinearOrder E] in
@[simp] lemma mem_faces (K : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (k : ℕ) (s : Set.powersetCard E k) : s ∈ faces K hK k ↔ s.val ∈ K.faces := by
  classical
  simp only [faces,Finset.mem_subtype,Set.Finite.mem_toFinset]
lemma apexes_faces (K : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {n : ℕ} (t : Set.powersetCard E n) :
    apexes (faces K hK (n+1)) t = Sparse.facetApexes K hK t.val := by
  classical
  ext u
  rw [mem_apexes,Sparse.mem_facetApexes]
  constructor
  · rintro ⟨hu,s,hs,he⟩
    refine ⟨hu,?_⟩
    convert (mem_faces K hK _ s).mp hs using 1
    ext x
    simp [he]
  · rintro ⟨hu,hs⟩
    refine ⟨hu,⟨insert u t.val,?_⟩,?_,rfl⟩
    · simp [Finset.card_insert_of_notMem hu]
    · apply (mem_faces K hK _ _).mpr
      convert hs using 1
      ext x
      simp
theorem geometric_boundary_coefficient (K : Geometry.SimplicialComplex ℝ E)
    (hK : K.faces.Finite) {n : ℕ} {S : Finset E}
    (hspace : K.space = convexHull ℝ (S : Set E)) (hc : S.card = n+1)
    (p : E →ₗ[ℝ] (Fin (n+1) → ℝ)) (t : Set.powersetCard E n) (ht : t.val ∈ K.faces) :
    (basis n).repr (d n (chain (faces K hK (n+1)) p)) t =
      ∑ v ∈ S, (if ∀ w ∈ S, w ≠ v → facetForm n (fun i => p (vertices t i)) (p w) = 0
        then (Real.sign (facetForm n (fun i => p (vertices t i)) (p v)) : ℂ) else 0) := by
  rw [boundary_coefficient,apexes_faces]
  let f : E →ₗ[ℝ] ℝ := (facetForm n (fun i => p (vertices t i))).comp p
  have hf (x : E) (hx : x ∈ t.val) : f x = 0 := by
    obtain ⟨i,rfl⟩ := (show x ∈ Set.range (vertices t) from (vertices_range t).symm ▸ hx)
    exact facetForm_vertex n (fun i => p (vertices t i)) i
  have hh := Sparse.signed_facet_boundary K hK hspace ht (by rw [t.property,hc]) f 0 hf
  have hh := congrArg (fun r : ℝ => (r : ℂ)) hh
  simpa only [Complex.ofReal_sum,Complex.ofReal_sub,Complex.ofReal_zero,sub_zero,
    f,LinearMap.comp_apply,apply_ite,Complex.ofReal_zero] using hh
end
section
variable {V : Type*} [LinearOrder V]
lemma chain_coefficient {n : ℕ} (F : Finset (Set.powersetCard V (n+1)))
    (p : V → (Fin (n+1) → ℝ)) (t : Set.powersetCard V (n+1)) :
    (basis (n+1)).repr (chain F p) t =
      if t ∈ F then (Real.sign (Matrix.det (fun j => p (vertices t j))) : ℂ) else 0 := by
  simp only [chain,map_sum,map_smul,Finsupp.finsetSum_apply,Finsupp.smul_apply,
    Module.Basis.repr_self,Finsupp.single_apply,smul_eq_mul,mul_ite,mul_one,mul_zero,
    Finset.sum_ite_eq']
end
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [LinearOrder E]
lemma boundary_coefficient_nonface (K : Geometry.SimplicialComplex ℝ E)
    (hK : K.faces.Finite) {n : ℕ} (p : E → (Fin (n+2) → ℝ))
    (t : Set.powersetCard E (n+1)) (ht : t.val ∉ K.faces) :
    (basis (n+1)).repr (d (n+1) (chain (faces K hK (n+2)) p)) t = 0 := by
  classical
  rw [boundary_coefficient]
  have hem : apexes (faces K hK (n+2)) t = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro u hu
    obtain ⟨_,s,hs,he⟩ := (mem_apexes _ t u).mp hu
    apply ht
    apply K.down_closed ((mem_faces K hK _ s).mp hs)
    · intro x hx
      rw [he]
      exact Finset.mem_insert_of_mem hx
    · exact Finset.card_pos.mp (by rw [t.property]; omega)
  rw [hem,Finset.sum_empty]
def faceChain (K : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {n : ℕ} (p : E → (Fin (n+2) → ℝ)) (i : Fin (n+2)) : Degree E (n+1) := by
  classical
  exact chain ((faces K hK (n+1)).filter fun t => ∀ x ∈ t.val, p x i = 0)
    (fun x j => p x (i.succAbove j))
open scoped Classical
lemma faceChain_coefficient (K : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {n : ℕ} (p : E → (Fin (n+2) → ℝ)) (i : Fin (n+2)) (t : Set.powersetCard E (n+1)) :
    (basis (n+1)).repr (faceChain K hK p i) t =
      if t.val ∈ K.faces ∧ ∀ j, p (vertices t j) i = 0 then
        (Real.sign (Matrix.det (fun j k => p (vertices t j) (i.succAbove k))) : ℂ) else 0 := by
  classical
  rw [faceChain,chain_coefficient]
  congr 1
  rw [Finset.mem_filter,mem_faces]
  congr 1
  apply propext
  constructor
  · exact fun h j => h _ (vertices_mem t j)
  · intro h x hx
    obtain ⟨j,rfl⟩ := (show x ∈ Set.range (vertices t) from (vertices_range t).symm ▸ hx)
    exact h j
end
open scoped BigOperators Classical
open OrientedIncidence Oriented ChainHomotopy Sparse.Orientation
section
end
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [LinearOrder E]
omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma sum_enumeration {k : ℕ} (S : Finset E) (v : Fin k ↪ E)
    (hv : Set.range v = S) {A : Type*} [AddCommMonoid A] (f : E → A) :
    (∑ x ∈ S, f x) = ∑ i : Fin k, f (v i) := by
  have he : Finset.univ.image v = S := by
    apply Finset.coe_injective
    simpa only [Finset.coe_image,Finset.coe_univ,Set.image_univ] using hv
  rw [← he,Finset.sum_image v.injective.injOn]
omit [NormedAddCommGroup E] [NormedSpace ℝ E] [LinearOrder E] in
lemma forall_enumeration_except {k : ℕ} (S : Finset E) (v : Fin k ↪ E)
    (hv : Set.range v = S) (i : Fin k) (P : E → Prop) :
    (∀ x ∈ S, x ≠ v i → P x) ↔ ∀ j, j ≠ i → P (v j) := by
  constructor
  · intro h j hji
    exact h _ (show v j ∈ (S : Set E) from hv ▸ Set.mem_range_self j) (fun he => hji (v.injective he))
  · intro h x hx hxi
    obtain ⟨j,rfl⟩ := (show x ∈ Set.range v from hv.symm ▸ hx)
    exact h j (fun he => hxi (congrArg v he))
theorem boundary_chain_chart (K : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {n : ℕ} (S : Finset E) (v : Fin (n+2) ↪ E) (hv : Set.range v = S)
    (hspace : K.space = convexHull ℝ (S : Set E))
    (p : E →ₗ[ℝ] (Fin (n+2) → ℝ))
    (hp : ∀ i, p (v i) = Pi.single i 1) :
    d (n+1) (chain (faces K hK (n+2)) p) =
      ∑ i : Fin (n+2), (-1 : ℂ)^i.val • faceChain K hK p i := by
  have hcard : S.card = n+2 := by
    have he : Finset.univ.image v = S := by
      apply Finset.coe_injective
      simpa only [Finset.coe_image,Finset.coe_univ,Set.image_univ] using hv
    rw [← he]
    simpa using Finset.card_image_of_injective Finset.univ v.injective
  apply (basis (n+1)).repr.injective
  apply Finsupp.ext
  intro t
  simp only [map_sum,map_smul,Finsupp.finsetSum_apply,Finsupp.smul_apply,smul_eq_mul,
    faceChain_coefficient]
  by_cases ht : t.val ∈ K.faces
  · rw [geometric_boundary_coefficient K hK hspace hcard p t ht,sum_enumeration S v hv]
    simp only [ht,true_and]
    apply Finset.sum_congr rfl
    intro i _
    simp only [forall_enumeration_except S v hv, hp]
    have hh := congrArg (fun r : ℝ => (r : ℂ))
      (facet_boundary_term (fun j => p (vertices t j)) i)
    simpa only [apply_ite,Complex.ofReal_zero,Complex.ofReal_mul,Complex.ofReal_pow,
      Complex.ofReal_neg,Complex.ofReal_one,mul_ite,mul_zero] using hh
  · rw [boundary_coefficient_nonface K hK p t ht]
    simp only [ht,false_and,ite_false,mul_zero,Finset.sum_const_zero]
end
section
variable {V : Type*}
def term (n : ℕ) (p : V → (Fin n → ℝ)) (v : Fin n → V) : Degree V n :=
  (Real.sign (Matrix.det (fun j => p (v j))) : ℂ) • wedge n v
lemma term_perm (n : ℕ) (p : V → (Fin n → ℝ)) (v : Fin n → V)
    (σ : Equiv.Perm (Fin n)) : term n p (v ∘ σ) = term n p v := by
  unfold term
  have hdet : Matrix.det (fun j => p (v (σ j))) =
      (Equiv.Perm.sign σ : ℝ) * Matrix.det (fun j => p (v j)) := by
    have hh := Matrix.detRowAlternating.map_perm (fun j => p (v j)) σ
    change Matrix.det (fun j => p (v (σ j))) =
      (Equiv.Perm.sign σ) • Matrix.det (fun j => p (v j)) at hh
    simpa only [Units.smul_def,zsmul_eq_mul] using hh
  rw [wedge_perm]
  change (Real.sign (Matrix.det (fun j => p (v (σ j)))) : ℂ) •
    ((Equiv.Perm.sign σ) • wedge n v) = _
  rw [hdet]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with he | he
  · simp [he]
  · simp only [he,Int.cast_neg,Int.cast_one,Units.val_neg,Units.val_one,neg_one_mul,
      Real.sign_neg,Complex.ofReal_neg,neg_smul_neg,Units.neg_smul,one_smul]
end
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
lemma parent_face_chart {n : ℕ} (v : Fin (n+1) → E)
    (p : E →ₗ[ℝ] (Fin (n+1) → ℝ)) (hp : ∀ j, p (v j) = Pi.single j 1)
    (i : Fin (n+1)) :
    convexHull ℝ (Set.range v) ∩ {x | p x i = 0} =
      convexHull ℝ (Set.range (fun j => v (i.succAbove j))) := by
  have hs : Set.range v ∩ {x | p x i = 0} =
      Set.range (fun j => v (i.succAbove j)) := by
    ext x
    constructor
    · rintro ⟨⟨j,rfl⟩,hj⟩
      have hji : j ≠ i := by
        intro he
        subst j
        change p (v i) i = 0 at hj
        simp only [hp,Pi.single_eq_same,one_ne_zero] at hj
      obtain ⟨k,hk⟩ := Fin.exists_succAbove_eq hji
      exact ⟨k,congrArg v hk⟩
    · rintro ⟨j,rfl⟩
      exact ⟨⟨i.succAbove j,rfl⟩,by simp [hp]⟩
  have hh := Sparse.convexHull_inter_supporting (Set.range v)
    (-((LinearMap.proj i).comp p)) 0 (by
      rintro _ ⟨j,rfl⟩
      change -(p (v j) i) ≤ 0
      simp only [hp,Pi.single_apply]
      split_ifs <;> norm_num)
  simp only [LinearMap.neg_apply,LinearMap.comp_apply,LinearMap.proj_apply,neg_eq_zero] at hh
  exact hh.trans (congrArg (convexHull ℝ) hs)
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
@[simp] lemma vertexMap_single (f : Y → Z) (y : Y) (a : ℂ) :
    vertexMap f (Finsupp.single y a) = Finsupp.single (f y) a :=
  Finsupp.mapDomain_single
@[simp] lemma relabel_wedge (n : ℕ) (f : Y → Z) (v : Fin n → Y) :
    relabel n f (wedge n v) = wedge n (f ∘ v) := by
  simp only [relabel, wedge, exteriorPower.map_apply_ιMulti, Function.comp_def,
    vertexMap_single]
end ChainHomotopy
namespace Fundamental
open scoped BigOperators Classical
open OrientedIncidence Oriented ChainHomotopy Sparse.Orientation
variable {V W : Type*} [LinearOrder V] [LinearOrder W]
lemma term_eq_sorted {n : ℕ} (s : Set.powersetCard V n)
    (p : V → (Fin n → ℝ)) (v : Fin n → V) (hi : Function.Injective v)
    (hv : Set.range v = s.val) :
    term n p v = (Real.sign (Matrix.det (fun j => p (vertices s j))) : ℂ) • basis n s := by
  obtain ⟨t,σ,he⟩ := exists_sorted_perm v hi
  have hts : t = s := by
    apply Subtype.ext
    apply Finset.coe_injective
    rw [← vertices_range t,← hv,he]
    exact (σ.surjective.range_comp (vertices t)).symm
  subst t
  rw [he,term_perm]
  rw [basis_eq_wedge]
  rfl
def simplexMap (f : V ↪ W) (n : ℕ) : Set.powersetCard V n ↪ Set.powersetCard W n where
  toFun s := ⟨s.val.map f,by simp⟩
  inj' := by
    intro s t h
    apply Subtype.ext
    exact Finset.map_injective f (congrArg Subtype.val h)
omit [LinearOrder W] in
lemma simplexMap_range (f : V ↪ W) {n : ℕ} (s : Set.powersetCard V n) :
    Set.range (f ∘ vertices s) = (simplexMap f n s).val := by
  ext y
  constructor
  · rintro ⟨j,rfl⟩
    exact Finset.mem_map.mpr ⟨vertices s j,vertices_mem s j,rfl⟩
  · intro hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_map.mp hy
    obtain ⟨j,rfl⟩ := (show x ∈ Set.range (vertices s) from (vertices_range s).symm ▸ hx)
    exact ⟨j,rfl⟩
lemma chain_relabel {n : ℕ} (F : Finset (Set.powersetCard V (n+1)))
    (p : V → (Fin (n+1) → ℝ)) (q : W → (Fin (n+1) → ℝ))
    (f : V ↪ W) (hpq : ∀ x, q (f x) = p x) :
    relabel (n+1) f (chain F p) = chain (F.map (simplexMap f (n+1))) q := by
  simp only [chain,map_sum,Finset.sum_map]
  apply Finset.sum_congr rfl
  intro s _
  rw [basis_eq_wedge,map_smul,relabel_wedge]
  have hh := term_eq_sorted (simplexMap f (n+1) s) q (f ∘ vertices s)
    (f.injective.comp (vertices s).injective) (simplexMap_range f s)
  simpa only [term,Function.comp_apply,hpq] using hh
end Fundamental
namespace Sparse
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
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
lemma restrictComplex_finite (B : Geometry.SimplicialComplex ℝ E) (P : Set E)
    (hB : B.faces.Finite) : (restrictComplex B P).faces.Finite :=
  hB.subset (fun _ hs => hs.1)
end Sparse
namespace Fundamental
open scoped BigOperators Classical
open OrientedIncidence Oriented ChainHomotopy Sparse.Orientation
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [LinearOrder E]
lemma faceChain_eq_restrict (K : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {n : ℕ} (p : E → (Fin (n+2) → ℝ)) (i : Fin (n+2)) :
    faceChain K hK p i = chain
      (faces (Sparse.restrictComplex K {x | p x i = 0})
        (Sparse.restrictComplex_finite K _ hK) (n+1)) (fun x j => p x (i.succAbove j)) := by
  unfold faceChain
  congr 1
  ext s
  simp only [Finset.mem_filter,mem_faces,Sparse.restrictComplex]
  rfl
theorem boundary_chain_restrictions (K : Geometry.SimplicialComplex ℝ E)
    (hK : K.faces.Finite) {n : ℕ} (S : Finset E) (v : Fin (n+2) ↪ E)
    (hv : Set.range v = S) (hspace : K.space = convexHull ℝ (S : Set E))
    (p : E →ₗ[ℝ] (Fin (n+2) → ℝ)) (hp : ∀ i, p (v i) = Pi.single i 1) :
    d (n+1) (chain (faces K hK (n+2)) p) =
      ∑ i : Fin (n+2), (-1 : ℂ)^i.val • chain
        (faces (Sparse.restrictComplex K {x | p x i = 0})
          (Sparse.restrictComplex_finite K _ hK) (n+1))
        (fun x j => p x (i.succAbove j)) := by
  rw [boundary_chain_chart K hK S v hv hspace p hp]
  simp only [faceChain_eq_restrict]
omit [LinearOrder E] in
lemma faces_one_of_space_singleton (K : Geometry.SimplicialComplex ℝ E)
    (hK : K.faces.Finite) (x : E) (hspace : K.space = {x}) :
    faces K hK 1 = {⟨{x},by simp⟩} := by
  ext s
  rw [mem_faces,Finset.mem_singleton]
  constructor
  · intro hs
    apply Subtype.ext
    apply Finset.eq_singleton_iff_unique_mem.mpr
    have hsub : (s.val : Set E) ⊆ {x} := hspace ▸ K.subset_space hs
    obtain ⟨y,hy⟩ := K.nonempty_of_mem_faces hs
    have hyx : y=x := hsub hy
    subst y
    exact ⟨hy,fun _ hz => hsub hz⟩
  · rintro rfl
    have hx : x ∈ K.space := hspace.symm ▸ Set.mem_singleton x
    obtain ⟨s,hs,hxs⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx
    have hsub : (s : Set E) ⊆ {x} := hspace ▸ K.subset_space hs
    obtain ⟨y,hy⟩ := K.nonempty_of_mem_faces hs
    have hyx : y=x := hsub hy
    subst y
    exact K.down_closed hs (Finset.singleton_subset_iff.mpr hy) (Finset.singleton_nonempty x)
theorem augmentation_chain (K : Geometry.SimplicialComplex ℝ E)
    (hK : K.faces.Finite) (x : E) (hspace : K.space = {x})
    (p : E → (Fin 1 → ℝ)) (hp : p x 0 = 1) :
    d 0 (chain (faces K hK 1) p) = wedge 0 (Fin.elim0 : Fin 0 → E) := by
  rw [faces_one_of_space_singleton K hK x hspace]
  simp only [chain,Finset.sum_singleton,basis_eq_wedge,map_smul,d_wedge]
  have hv : ∀ j, vertices (⟨{x},by simp⟩ : Set.powersetCard E 1) j = x := by
    intro j
    exact Finset.mem_singleton.mp (vertices_mem (⟨{x},by simp⟩ : Set.powersetCard E 1) j)
  have hd : Matrix.det (show Matrix (Fin 1) (Fin 1) ℝ from fun _ => p x) = 1 := by
    exact (Matrix.det_fin_one _).trans hp
  simp only [hv]
  change (Real.sign (Matrix.det (fun _ : Fin 1 => p x)) : ℂ) •
    (∑ i : Fin 1, (-1 : ℂ)^i.val • wedge 0 (fun _ : Fin 0 => x)) = _
  rw [hd]
  simp only [Real.sign_one,Complex.ofReal_one,one_smul,Fin.sum_univ_one,Fin.val_zero,pow_zero]
  congr 1
  exact Subsingleton.elim _ _
end Fundamental
namespace Oriented
open scoped BigOperators
variable {Y A : Type*} [AddCommGroup A] [Module ℂ A]
instance {n : ℕ} : CoeFun (AltFunction Y n A) (fun _ => (Fin n → Y) → A) :=
  ⟨AltFunction.toFun⟩
end Oriented
namespace ChainHomotopy
section
open scoped BigOperators
open Oriented
variable {Y : Type*}
variable [LinearOrder Y]
structure Complex (Y : Type*) where
  faces : Set (Finset Y)
  empty_mem : ∅ ∈ faces
  down_closed : ∀ {s t}, s ∈ faces → t ⊆ s → t ∈ faces
def Complex.chains (K : Complex Y) (n : ℕ) : Submodule ℂ (Degree Y n) :=
  Submodule.span ℂ {x | ∃ v : Fin n → Y,
    (Finset.univ.image v) ∈ K.faces ∧ wedge n v = x}
end
section
open scoped BigOperators
open Oriented
variable {Y Z W : Type*}
variable [LinearOrder Y]
lemma relabel_coe (n : ℕ) (f : Y → Z) (x : Degree Y n) :
    (relabel n f x : Chains.Algebra Z) =
      ExteriorAlgebra.map (vertexMap f) (x : Chains.Algebra Y) := by
  have he : (Degree Z n).subtype.comp (relabel n f) =
      (ExteriorAlgebra.map (vertexMap f)).toLinearMap.comp (Degree Y n).subtype := by
    apply linearMap_ext_wedge
    intro v
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, AlgHom.toLinearMap_apply]
    rw [relabel_wedge]
    simp only [wedge, exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.map_apply_ιMulti,
      Function.comp_def, vertexMap_single]
  exact LinearMap.congr_fun he x
lemma relabel_cone (n : ℕ) (f : Y → Z) (v : Y →₀ ℂ) (x : Degree Y n) :
    relabel (n+1) f (cone n v x) = cone n (vertexMap f v) (relabel n f x) := by
  apply Subtype.ext
  simp only [relabel_coe, cone_coe, map_mul, ExteriorAlgebra.map_apply_ι]
@[simp] lemma relabel_id (n : ℕ) : relabel n (id : Y → Y) = LinearMap.id := by
  apply linearMap_ext_wedge
  intro v
  simp only [relabel_wedge, Function.id_comp, LinearMap.id_apply]
end
open scoped BigOperators
open Oriented
variable {Y H : Type*} [LinearOrder Y] [Monoid H] [MulAction H Y]
def Complex.IsInvariant (K : Complex Y) : Prop :=
  ∀ h : H, ∀ s ∈ K.faces, s.image (fun y => h • y) ∈ K.faces
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
@[simp] lemma labelMap_wedge_succ (b : Finset V → Y →₀ ℂ) (n : ℕ) (v : Fin (n+1) → V) :
    labelMap b (n+1) (wedge (n+1) v) =
      cone n (b (Finset.univ.image v)) (labelMap b n (d n (wedge (n+1) v))) := by
  rw [labelMap,AltFunction.lift_wedge]
  rfl
@[simp] lemma labelMap_wedge_zero (b : Finset V → Y →₀ ℂ) (v : Fin 0 → V) :
    labelMap b 0 (wedge 0 v) = wedge 0 (fun i => Fin.elim0 i) := by
  rw [labelMap,wedge,exteriorPower.map_apply_ιMulti]
  congr 1
  exact funext fun i => Fin.elim0 i
lemma labelMap_wedge_recursion (b : Finset V → Y →₀ ℂ) (n : ℕ) (v : Fin (n+1) → V) :
    labelMap b (n+1) (wedge (n+1) v) =
      ∑ i : Fin (n+1), (-1 : ℂ)^i.val •
        cone n (b (Finset.univ.image v))
          (labelMap b n (wedge n (fun j => v (i.succAbove j)))) := by
  rw [labelMap_wedge_succ,d_wedge,map_sum,map_sum]
  simp only [map_smul]
lemma boundary_degree_zero [LinearOrder Y] (x : Degree Y 0) :
    Chains.boundary Y (x : Chains.Algebra Y) = 0 := by
  have he : (Chains.boundary Y).comp (Degree Y 0).subtype = 0 := by
    apply linearMap_ext_wedge
    intro v
    simp [wedge,exteriorPower.ιMulti_apply_coe,Chains.boundary]
  exact LinearMap.congr_fun he x
lemma labelMap_chain [LinearOrder Y] (b : Finset V → Y →₀ ℂ)
    (hb : ∀ s : Finset V, s.Nonempty → Chains.augmentation Y (b s) = 1)
    (n : ℕ) (x : Degree V (n+1)) :
    d n (labelMap b (n+1) x) = labelMap b n (d n x) := by
  induction n with
  | zero =>
    have he : (d 0).comp (labelMap b 1) = (labelMap b 0).comp (d 0) := by
      apply linearMap_ext_wedge
      intro v
      simp only [LinearMap.comp_apply,labelMap_wedge_succ]
      exact d_cone_cycle 0 _ (hb _ (Finset.image_nonempty.mpr Finset.univ_nonempty)) _
        (boundary_degree_zero _)
    exact LinearMap.congr_fun he x
  | succ n ih =>
    have he : (d (n+1)).comp (labelMap b (n+2)) = (labelMap b (n+1)).comp (d (n+1)) := by
      apply linearMap_ext_wedge
      intro v
      simp only [LinearMap.comp_apply,labelMap_wedge_succ]
      apply d_cone_cycle
      · exact hb _ (Finset.image_nonempty.mpr Finset.univ_nonempty)
      · have hz : d n (labelMap b (n+1) (d (n+1) (wedge (n+2) v))) = 0 := by
          rw [ih,d_square,map_zero]
        exact congrArg Subtype.val hz
    exact LinearMap.congr_fun he x
lemma labelMap_local (b c : Finset V → Y →₀ ℂ) (s : Finset V)
    (hbc : ∀ t : Finset V, t ⊆ s → t.Nonempty → b t = c t)
    (n : ℕ) (v : Fin n → V) (hv : ∀ i, v i ∈ s) :
    labelMap b n (wedge n v) = labelMap c n (wedge n v) := by
  induction n with
  | zero => simp only [labelMap_wedge_zero]
  | succ n ih =>
    rw [labelMap_wedge_recursion,labelMap_wedge_recursion]
    have him : Finset.univ.image v ⊆ s := by
      intro y hy
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hy
      exact hv i
    rw [hbc _ him (Finset.image_nonempty.mpr Finset.univ_nonempty)]
    apply Finset.sum_congr rfl
    intro i _
    rw [ih (fun j => v (i.succAbove j)) (fun j => hv (i.succAbove j))]
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
lemma vertexMean_eq_centroid {s : Finset E} (hs : s.Nonempty) :
    vertexMean s = s.centroid ℝ id := by
  rw [Finset.centroid_def, Finset.affineCombination_eq_linear_combination _ _ _
    (s.sum_centroidWeights_eq_one_of_nonempty ℝ hs)]
  simp only [Finset.centroidWeights_apply, id_eq]
  exact Finset.smul_sum
lemma vertexMean_map {F : Type*} [AddCommGroup F] [Module ℝ F]
    (f : E ≃ᵃ[ℝ] F) {s : Finset E} (hs : s.Nonempty) :
    vertexMean (s.map f.toEquiv.toEmbedding) = f (vertexMean s) := by
  rw [vertexMean_eq_centroid hs, vertexMean_eq_centroid hs.map, Finset.centroid_map]
  simp only [Finset.centroid_def]
  convert (s.map_affineCombination id (s.centroidWeights ℝ)
    (s.sum_centroidWeights_eq_one_of_nonempty ℝ hs) f.toAffineMap).symm using 1 <;> rfl
section BoundedRay
end BoundedRay
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
end Trace
section GeneralBoundary
end GeneralBoundary
end BassTrace.Sparse.Cuts
end OAI

end
section
namespace OAI
namespace BassTrace.Sparse.Cuts
section CellVertices
end CellVertices
section Arrangements
end Arrangements
section ArrangementTriangulation
end ArrangementTriangulation
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
lemma isMarked_empty (K : Geometry.SimplicialComplex ℝ E) : IsMarked K ∅ := by
  intro x hx
  exact hx.elim
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
end
section
end
section
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
namespace SubdivisionFamily
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
lemma zero_carrier (hK : ∀ F ∈ K.faces, F.card ≤ n+1) {i : ℕ} (hi : i ≤ n)
    {z : V} (hz : z ∈ Q.Z 0) :
    ∃ F ∈ (Q.T i).faces, convexHull ℝ (F : Set V) ⊆ Q.Z i ∧
      z ∈ convexHull ℝ (F : Set V) ∧ F.card = i+1 ∧
      (∀ E ∈ (Q.T i).faces, z ∈ convexHull ℝ (E : Set V) → F ⊆ E) ∧
      (∀ E ∈ (Q.T i).faces, z ∈ convexHull ℝ (E : Set V) →
        E.card = i+1 → E = F) := by
  have hzi := Q.subset (Nat.zero_le i) hi hz
  obtain ⟨F,hF,hzF,hmin⟩ := exists_smallest_carrier (Q.T i)
    ((Q.marked i hi).subset_space hzi)
  obtain ⟨E,hE,hzE,hEZ⟩ := Q.marked i hi z hzi
  have hFZ := (convexHull_mono (hmin E hE hzE)).trans hEZ
  have hb := Q.dimension_bound hK hi hF hFZ
  have hl := Q.card_lower_of_mem_zero hi hz hF hFZ hzF
  have hc : F.card = i+1 := by omega
  refine ⟨F,hF,hFZ,hzF,hc,hmin,?_⟩
  intro E hE hzE hcard
  exact (Finset.eq_of_subset_of_card_le (hmin E hE hzE) (by omega)).symm
end PointFiltration
end
section
end
section
namespace UniversalCuts
end UniversalCuts
end
namespace MarkedFamily
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
namespace MarkedFamily
end MarkedFamily
end
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
section Compact
end Compact
section Potential
end Potential
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
end BassTrace.Sparse
end
end OAI

end
section
namespace OAI
noncomputable section
namespace BassTrace.Sparse
section
namespace FinProbability
end FinProbability
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
end
end Sparse.GraphGeometry
namespace Sparse
end Sparse
namespace Sparse.GraphGeometry
open Set Finset
open scoped BassTrace.Sparse Topology
variable {Y : Type*} [DecidableEq Y] (Γ : SimpleGraph Y) [Γ.LocallyFinite]
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
@[simp] lemma push_refl (p : FinProbability Y) : push (Equiv.refl Y) p = p := by
  apply FinProbability.ext_coeff
  ext y
  rfl
@[simp] lemma push_symm_push (e : Y ≃ Z) (p : FinProbability Y) :
    push e.symm (push e p) = p := by
  apply FinProbability.ext_coeff
  ext y
  simp
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
end BassTrace.Sparse.OrbitForms
namespace BassTrace.Sparse.BallOrbitForms
end BassTrace.Sparse.BallOrbitForms
namespace BassTrace.Sparse.OrbitForms
open Set Finset
open scoped BassTrace.Sparse
variable {H Y I X : Type*} [Group H] [MulAction H Y] [IsCancelSMul H Y] [Fintype I]
variable (d : Data I Y) {t : ℝ} (ht : 0 < t)
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
noncomputable section
end
end OAI.BassTrace.Sparse.OrbitForms
namespace OAI.BassTrace.Sparse.Cuts.Sequential
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
end Sparse.GraphGeometry
namespace Sparse.BallOrbitForms
end Sparse.BallOrbitForms
namespace Sparse.GraphGeometry
open Set Finset
open scoped BassTrace.Sparse Classical
section
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
end
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
section
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
end Sparse.GraphGeometry
end BassTrace
end
end OAI

end
section
namespace OAI
namespace BassTrace.Sparse
end BassTrace.Sparse
end OAI

end
section
namespace OAI
namespace BassTrace.Sparse
section
end
noncomputable section
end
end BassTrace.Sparse
end OAI

end
section
namespace OAI
noncomputable section
namespace BassTrace.Sparse
section
end
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
end Sparse.Cuts
namespace Sparse
section
end
section
open Set Finset MeasureTheory
open scoped BassTrace.Sparse ENNReal Classical Pointwise
variable {H Y X : Type*} [Group H] [MulAction H Y] [IsCancelSMul H Y]
  [DecidableEq Y] [TopologicalSpace X] [CompactSpace X] [MulAction H X]
  [MeasurableSpace X] [BorelSpace X]
def simplexVertices (s : Finset Y) : Finset (Y →₀ ℝ) :=
  s.image (fun y => Finsupp.single y (1 : ℝ))
def SourceTop (K : PreAbstractSimplicialComplex Y) (n : ℕ) :=
  {s : Finset Y // s ∈ K.faces ∧ s.card=n+1}
end
end Sparse
end BassTrace
end
end OAI

end
section
namespace OAI.BassTrace.Sparse.Cuts
end OAI.BassTrace.Sparse.Cuts
namespace OAI
noncomputable section
namespace BassTrace
namespace Sparse.OrbitForms
end Sparse.OrbitForms
namespace Sparse.GraphGeometry
end Sparse.GraphGeometry
namespace Sparse.OrbitForms
end Sparse.OrbitForms
namespace Sparse.Cuts
section
end
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
end Sparse
namespace Sparse.GraphGeometry
end Sparse.GraphGeometry
namespace Sparse.Cuts.SubdivisionFamily
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
end
section
section
end
end
section
end
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
end
section
end
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
end
section
end
section
end
end BassTrace.Sparse
end
end OAI

end
section
namespace OAI
namespace BassTrace.Sparse
section Product
end Product
end BassTrace.Sparse
end OAI

end
section
namespace OAI
namespace BassTrace.Sparse
section
end
section
end
noncomputable section
end
end BassTrace.Sparse
end OAI

end
section
namespace OAI
noncomputable section
namespace BassTrace.Sparse
section
end
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
section
end
end Sparse
namespace Sparse.GraphGeometry
section
end
end Sparse.GraphGeometry
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
namespace Sparse.GraphGeometry
section
end
section
end
end Sparse.GraphGeometry
namespace Sparse
end Sparse
namespace Sparse.GraphGeometry
section
end
section
end
end Sparse.GraphGeometry
end BassTrace
end
end OAI

end
section
namespace OAI
noncomputable section
namespace BassTrace
namespace Sparse.GraphGeometry
section
end
end Sparse.GraphGeometry
namespace Sparse.GraphCounting
end Sparse.GraphCounting
namespace Sparse.GraphGeometry
end Sparse.GraphGeometry
namespace Sparse.GraphCounting
end Sparse.GraphCounting
namespace Sparse.GraphGeometry
end Sparse.GraphGeometry
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
namespace Sparse.GraphGeometry
end Sparse.GraphGeometry
namespace Sparse
end Sparse
namespace Sparse.GraphGeometry
end Sparse.GraphGeometry
end BassTrace
end
end OAI

end
section
namespace OAI
noncomputable section
namespace BassTrace
namespace Sparse.GraphGeometry
section
end
end Sparse.GraphGeometry
namespace Sparse
section
end
end Sparse
namespace Sparse.GraphGeometry
section
section
end
end
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
section
end
end Sparse
namespace Sparse.GraphGeometry
section
end
section
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
namespace FT
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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma vertexMean_weight_sum {F : Finset E} (hF : F.Nonempty) :
    ∑ _x ∈ F, (F.card : ℝ)⁻¹ = 1 := by
  simp [ne_of_gt (Nat.cast_pos.mpr hF.card_pos : (0:ℝ)<F.card)]
lemma vertexMean_eq_sum (F : Finset E) :
    vertexMean F = ∑ x ∈ F, (F.card : ℝ)⁻¹ • x := by
  simp only [vertexMean,Finset.smul_sum]
lemma vertexMean_mem_marked_iff (K : Geometry.SimplicialComplex ℝ E)
    {Z : Set E} (hZ : IsMarked K Z) {F : Finset E} (hF : F ∈ K.faces) :
    vertexMean F ∈ Z ↔ convexHull ℝ (F : Set E) ⊆ Z := by
  constructor
  · intro hm
    obtain ⟨T,hT,hmt,hTZ⟩ := hZ _ hm
    rw [vertexMean_eq_sum] at hmt
    have hFT := simplex_contains_positivePoint K hF hT (fun _ => (F.card : ℝ)⁻¹)
      (fun _ _ => inv_pos.mpr (Nat.cast_pos.mpr (K.nonempty_of_mem_faces hF).card_pos))
      (vertexMean_weight_sum (K.nonempty_of_mem_faces hF)) hmt
    exact (convexHull_mono hFT).trans hTZ
  · exact fun hh => hh (vertexMean_mem_convexHull (K.nonempty_of_mem_faces hF))
lemma segment_vertexMean_avoids (K : Geometry.SimplicialComplex ℝ E)
    {Z : Set E} (hZ : IsMarked K Z) {F G : Finset E}
    (hF : F ∈ K.faces) (hG : G ∈ K.faces) (hFG : F ⊆ G)
    (hmF : vertexMean F ∉ Z) (hmG : vertexMean G ∉ Z) :
    Disjoint (segment ℝ (vertexMean F) (vertexMean G)) Z := by
  apply Set.disjoint_left.mpr
  rintro q ⟨a,b,ha,hb,hab,rfl⟩ hq
  by_cases hb0 : b=0
  · have ha1 : a=1 := by linarith
    simp only [ha1,hb0,one_smul,zero_smul,add_zero] at hq
    exact hmF hq
  have hbpos : 0<b := lt_of_le_of_ne hb (Ne.symm hb0)
  let u : E → ℝ := fun x => if x ∈ F then (F.card : ℝ)⁻¹ else 0
  let w : E → ℝ := fun x => a*u x + b*(G.card : ℝ)⁻¹
  have hu : ∑ x ∈ G, u x = 1 := by
    calc
      _ = ∑ x ∈ F, u x := (Finset.sum_subset hFG (fun x _ hx => by simp [u,hx])).symm
      _ = ∑ _x ∈ F, (F.card : ℝ)⁻¹ := Finset.sum_congr rfl (fun x hx => by simp [u,hx])
      _ = 1 := vertexMean_weight_sum (K.nonempty_of_mem_faces hF)
  have hvec : ∑ x ∈ G, u x • x = vertexMean F := by
    calc
      _ = ∑ x ∈ F, u x • x :=
        (Finset.sum_subset hFG (fun x _ hx => by simp [u,hx])).symm
      _ = ∑ x ∈ F, (F.card : ℝ)⁻¹ • x :=
        Finset.sum_congr rfl (fun x hx => by simp [u,hx])
      _ = _ := (vertexMean_eq_sum F).symm
  have hw : ∀ x ∈ G, 0 < w x := by
    intro x _
    have hux : 0 ≤ u x := by dsimp [u]; split_ifs <;> positivity
    exact add_pos_of_nonneg_of_pos (mul_nonneg ha hux)
      (mul_pos hbpos (inv_pos.mpr (Nat.cast_pos.mpr (K.nonempty_of_mem_faces hG).card_pos)))
  have hws : ∑ x ∈ G, w x = 1 := by
    simp only [w,Finset.sum_add_distrib,← Finset.mul_sum,hu,
      vertexMean_weight_sum (K.nonempty_of_mem_faces hG),mul_one]
    exact hab
  have heq : ∑ x ∈ G, w x • x = a • vertexMean F + b • vertexMean G := by
    simp only [w,add_smul,mul_smul,Finset.sum_add_distrib,← Finset.smul_sum,hvec,
      ← vertexMean_eq_sum]
  obtain ⟨T,hT,hqT,hTZ⟩ := hZ _ hq
  rw [← heq] at hqT
  have hGT := simplex_contains_positivePoint K hG hT w hw hws hqT
  exact hmG (hTZ (convexHull_mono hGT (vertexMean_mem_convexHull (K.nonempty_of_mem_faces hG))))
lemma vertexMean_components_eq (K : Geometry.SimplicialComplex ℝ E)
    {P Z : Set E} (hZ : IsMarked K Z) {F G : Finset E}
    (hF : F ∈ K.faces) (hG : G ∈ K.faces) (hFG : F ⊆ G)
    (hGP : convexHull ℝ (G : Set E) ⊆ P)
    (hmF : vertexMean F ∉ Z) (hmG : vertexMean G ∉ Z) :
    connectedComponentIn (P \ Z) (vertexMean F) =
      connectedComponentIn (P \ Z) (vertexMean G) := by
  have hsub : segment ℝ (vertexMean F) (vertexMean G) ⊆ P \ Z := by
    intro q hq
    refine ⟨?_,fun hqZ => Set.disjoint_left.mp (segment_vertexMean_avoids K hZ hF hG hFG hmF hmG) hq hqZ⟩
    exact hGP ((convex_convexHull ℝ (G : Set E)).segment_subset
      (convexHull_mono hFG (vertexMean_mem_convexHull (K.nonempty_of_mem_faces hF)))
      (vertexMean_mem_convexHull (K.nonempty_of_mem_faces hG)) hq)
  have hh := (convex_segment (vertexMean F) (vertexMean G)).isPreconnected.subset_connectedComponentIn
    (left_mem_segment ℝ _ _) hsub (right_mem_segment ℝ _ _)
  exact connectedComponentIn_eq hh
end
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {K : Geometry.SimplicialComplex ℝ V} {n : ℕ}
namespace PointFiltration
variable (Q : PointFiltration K n)
def FinalFace := {F : Finset V // F∈(Q.T 0).faces}
lemma final_marked (i : ℕ) (hi : i≤n) : IsMarked (Q.T 0) (Q.Z i) :=
  (Q.refines (Nat.zero_le i) hi).preserves_marked (Q.marked i hi)
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
lemma mean_mem_iff_level_le (F : Q.FinalFace) {i : ℕ} (hi : i≤n) :
    vertexMean F.val∈Q.Z i ↔ Q.faceLevel F ≤ i := by
  constructor
  · exact fun h=>Nat.find_min' (Q.exists_face_level F) ⟨hi,h⟩
  · exact fun h=>Q.subset h hi (Q.mean_mem_faceLevel F)
lemma hull_mem_iff_level_le (F : Q.FinalFace) {i : ℕ} (hi : i≤n) :
    convexHull ℝ (F.val : Set V)⊆Q.Z i ↔ Q.faceLevel F ≤ i := by
  rw [← vertexMean_mem_marked_iff (Q.T 0) (Q.final_marked i hi) F.property]
  exact Q.mean_mem_iff_level_le F hi
lemma faceLevel_mono (F G : Q.FinalFace) (hFG : F.val⊆G.val) :
    Q.faceLevel F≤Q.faceLevel G := by
  apply (Q.hull_mem_iff_level_le F (Q.faceLevel_le G)).mp
  exact (convexHull_mono hFG).trans
    ((Q.hull_mem_iff_level_le G (Q.faceLevel_le G)).mpr le_rfl)
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
lemma faceComponent_eq_of_level_eq (F G : Q.FinalFace) (hFG : F.val⊆G.val)
    (hlevel : Q.faceLevel F=Q.faceLevel G) : Q.faceComponent F=Q.faceComponent G := by
  have hi := Q.faceLevel_le G
  have hz : IsMarked (Q.T 0) (Q.below (Q.faceLevel G)) := by
    unfold below
    split_ifs
    · exact isMarked_empty _
    · exact Q.final_marked _ (by omega)
  have hP : convexHull ℝ (G.val : Set V)⊆Q.Z (Q.faceLevel G) :=
    (Q.hull_mem_iff_level_le G hi).mpr le_rfl
  have hFZ : vertexMean F.val∉Q.below (Q.faceLevel G) :=
    hlevel ▸ (Q.mean_mem_stratum F).2
  exact (by
    unfold faceComponent
    rw [hlevel]
    exact vertexMean_components_eq (Q.T 0) hz F.property G.property hFG hP hFZ
      (Q.mean_mem_stratum G).2)
lemma final_face_card_le_level (hK : ∀ F∈K.faces,F.card≤n+1) (F : Q.FinalFace) :
    F.val.card≤Q.faceLevel F+1 := by
  obtain ⟨S,hS⟩ := Q.refines (Nat.zero_le (Q.faceLevel F)) (Q.faceLevel_le F)
  obtain ⟨T,hT,hTZ,hFT⟩ := S.carrier_marked (Q.marked _ (Q.faceLevel_le F))
    (hS.symm ▸ F.property)
    ((Q.hull_mem_iff_level_le F (Q.faceLevel_le F)).mpr le_rfl)
  have hc := (Q.T 0).indep F.property |>.card_le_card_of_subset_affineSpan
    ((subset_convexHull ℝ _).trans (hFT.trans (convexHull_subset_affineSpan _)))
  exact hc.trans (Q.dimension_bound hK (Q.faceLevel_le F) hT hTZ)
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
omit [Γ.LocallyFinite] in
lemma componentSupport_nonempty (x : X) (F : (Q.point x).FinalFace) :
    (supportVertices ((Q.point x).faceComponent F)).Nonempty := by
  let p := GraphGeometry.pointProbability K ⟨Cuts.vertexMean F.val,
    GraphGeometry.faceComponent_mem_space Γ hΓ Q x F ((Q.point x).mean_mem_component F)⟩
  have hp := p.coeff_support_nonempty
  obtain ⟨y,hy⟩ := hp
  refine ⟨y,Cuts.vertexMean F.val,(Q.point x).mean_mem_component F,?_⟩
  have he : p.coeff=Cuts.vertexMean F.val := GraphGeometry.pointProbability_coeff K _
  exact he ▸ hy
end Sparse
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
open Set Finset
open scoped BassTrace.Sparse Classical
variable {Y X : Type*} [DecidableEq Y] [TopologicalSpace X]
variable {K : PreAbstractSimplicialComplex Y}
variable {T : Cuts.SubdivisionFamily X (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K)}
variable (P : Cuts.MarkedFamily T)
lemma marked_localConstancy_window (W : Finset Y) :
    IsLocallyConstant (fun x=>P.val x ∩ probabilitySet W) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro x
  let A := W.powerset.filter (fun s=>s∈K.faces)
  have hA : ∀ s∈A, ∀ᶠ y in nhds x,
      P.val y ∩ probabilitySet s=P.val x ∩ probabilitySet s := by
    intro s hs
    have hsK := (Finset.mem_filter.mp hs).2
    have hh := (P.localConstancy_inter (simplexVertices s) ⟨s,hsK,rfl⟩
      (convexHull ℝ (simplexVertices s : Set (Y →₀ ℝ))) subset_rfl).eventually_eq x
    simpa only [simplexVertices,Finset.coe_image,convexHull_single_eq_probabilitySet] using hh
  filter_upwards [(Filter.eventually_all_finite (Finset.finite_toSet A)).mpr hA] with y hy
  have he (z z' : X) (hz : ∀ s∈A,P.val z ∩ probabilitySet s=P.val z' ∩ probabilitySet s) :
      P.val z∩probabilitySet W⊆P.val z'∩probabilitySet W := by
    rintro p ⟨hp,hpW⟩
    have hpK : p∈(Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).space :=
      (T.val z).space_eq ▸ (P.marked z).subset_space hp
    let q := GraphGeometry.pointProbability K ⟨p,hpK⟩
    have hq : q.coeff=p := GraphGeometry.pointProbability_coeff K _
    have hsK : p.support∈K.faces := hq ▸ GraphGeometry.pointProbability_face K ⟨p,hpK⟩
    have hs : p.support∈A := Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr hpW.2.2,hsK⟩
    have hpp : p∈probabilitySet p.support := ⟨hpW.1,hpW.2.1,subset_rfl⟩
    exact ⟨((hz _ hs) ▸ (show p∈P.val z∩probabilitySet p.support from ⟨hp,hpp⟩)).1,hpW⟩
  exact Set.Subset.antisymm (he y x hy) (he x y (fun s hs=>(hy s hs).symm))
omit [DecidableEq Y] [TopologicalSpace X] in
lemma connectedComponentIn_inter_of_subset {V : Type*} [TopologicalSpace V]
    (S W : Set V) (p : V) (hp : p∈S)
    (hW : connectedComponentIn S p⊆W) :
    connectedComponentIn (S∩W) p=connectedComponentIn S p := by
  apply Set.Subset.antisymm (connectedComponentIn_mono p Set.inter_subset_left)
  exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
    (mem_connectedComponentIn hp) (fun _ h=>⟨connectedComponentIn_subset S p h,hW h⟩)
end Sparse
namespace Sparse.Cuts.PointFiltration
open Set Finset
open scoped Classical
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {K : Geometry.SimplicialComplex ℝ V} {n : ℕ}
variable (Q Q' : PointFiltration K n)
lemma faceLevel_eq_of_window (F : Finset V)
    (hF : F∈(Q.T 0).faces) (hF' : F∈(Q'.T 0).faces)
    (W : Set V) (hm : vertexMean F∈W)
    (hZ : ∀ i,i≤n → Q.Z i∩W=Q'.Z i∩W) :
    Q.faceLevel ⟨F,hF⟩=Q'.faceLevel ⟨F,hF'⟩ := by
  apply Nat.le_antisymm
  · apply (Q.mean_mem_iff_level_le ⟨F,hF⟩ (Q'.faceLevel_le ⟨F,hF'⟩)).mp
    exact ((hZ _ (Q'.faceLevel_le ⟨F,hF'⟩)).symm ▸
      (show vertexMean F∈Q'.Z (Q'.faceLevel ⟨F,hF'⟩)∩W from
        ⟨Q'.mean_mem_faceLevel ⟨F,hF'⟩,hm⟩)).1
  · apply (Q'.mean_mem_iff_level_le ⟨F,hF'⟩ (Q.faceLevel_le ⟨F,hF⟩)).mp
    exact ((hZ _ (Q.faceLevel_le ⟨F,hF⟩)) ▸
      (show vertexMean F∈Q.Z (Q.faceLevel ⟨F,hF⟩)∩W from
        ⟨Q.mean_mem_faceLevel ⟨F,hF⟩,hm⟩)).1
lemma stratum_inter_eq_of_window (W : Set V)
    (hZ : ∀ i,i≤n → Q.Z i∩W=Q'.Z i∩W) (i : ℕ) (hi : i≤n) :
    Q.stratum i∩W=Q'.stratum i∩W := by
  have he (A B : Set V) : (A\B)∩W=(A∩W)\(B∩W) := by ext p; simp; tauto
  unfold stratum
  rw [he,he,hZ i hi]
  congr 1
  unfold below
  split_ifs with hz
  · rfl
  · exact hZ (i-1) (by omega)
lemma faceComponent_eq_of_window (F : Finset V)
    (hF : F∈(Q.T 0).faces) (hF' : F∈(Q'.T 0).faces)
    (W : Set V)
    (hW : Q.faceComponent ⟨F,hF⟩⊆W) (hW' : Q'.faceComponent ⟨F,hF'⟩⊆W)
    (hZ : ∀ i,i≤n → Q.Z i∩W=Q'.Z i∩W) :
    Q.faceComponent ⟨F,hF⟩=Q'.faceComponent ⟨F,hF'⟩ := by
  have hlev := Q.faceLevel_eq_of_window Q' F hF hF' W
    (hW (Q.mean_mem_component ⟨F,hF⟩)) hZ
  change connectedComponentIn (Q.stratum (Q.faceLevel ⟨F,hF⟩)) (vertexMean F)=
    connectedComponentIn (Q'.stratum (Q'.faceLevel ⟨F,hF'⟩)) (vertexMean F)
  rw [← BassTrace.Sparse.connectedComponentIn_inter_of_subset
    (Q.stratum (Q.faceLevel ⟨F,hF⟩)) W (vertexMean F)
    (Q.mean_mem_stratum ⟨F,hF⟩) hW]
  rw [Q.stratum_inter_eq_of_window Q' W hZ _ (Q.faceLevel_le ⟨F,hF⟩),hlev]
  exact BassTrace.Sparse.connectedComponentIn_inter_of_subset
    (Q'.stratum (Q'.faceLevel ⟨F,hF'⟩)) W (vertexMean F)
    (Q'.mean_mem_stratum ⟨F,hF'⟩) hW'
end Sparse.Cuts.PointFiltration
namespace Sparse.GraphGeometry
open Set Finset
open scoped BassTrace.Sparse Classical
variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y]
  [TopologicalSpace X] [MulAction H X]
variable {K : PreAbstractSimplicialComplex Y} {n : ℕ} {R : ℝ}
variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)
variable (Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
  (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K) (realizationDistance Γ hΓ K n) R n)
variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)
include hK in
lemma component_subset_window (hn : 0<n) (hR : 0≤R) (x : X)
    (F : (Q.point x).FinalFace) (s : Finset Y)
    (hFs : Cuts.vertexMean F.val∈convexHull ℝ (simplexVertices s : Set (Y →₀ ℝ))) :
    (Q.point x).faceComponent F⊆probabilitySet (labelWindow Γ n R s) := by
  intro v hv
  let p := pointProbability K ⟨v,faceComponent_mem_space Γ hΓ Q x F hv⟩
  have hp : p.coeff=v := pointProbability_coeff K _
  have hh : v∈probabilitySet v.support := by
    rw [←hp]
    exact ⟨p.nonneg,by simpa only [coefficientSum_apply] using p.total,subset_rfl⟩
  exact ⟨hh.1,hh.2.1,component_support_subset Γ hΓ Q hK hn hR x F s hFs hv⟩
include hK in
lemma faceComponents_eq_local (hn : 0<n) (hR : 0≤R) (s : Finset Y) (hs : s∈K.faces)
    (x : X) : ∀ᶠ y in nhds x,
    (Cuts.restrictComplex ((Q.pair 0).T.val y).complex
      (convexHull ℝ (simplexVertices s : Set (Y →₀ ℝ)))).faces=
    (Cuts.restrictComplex ((Q.pair 0).T.val x).complex
      (convexHull ℝ (simplexVertices s : Set (Y →₀ ℝ)))).faces ∧
    ∀ (F : Finset (Y →₀ ℝ))
      (hFx : F∈((Q.pair 0).T.val x).complex.faces)
      (hFy : F∈((Q.pair 0).T.val y).complex.faces),
      convexHull ℝ (F : Set (Y →₀ ℝ))⊆
        convexHull ℝ (simplexVertices s : Set (Y →₀ ℝ)) →
      (Q.point y).faceComponent ⟨F,hFy⟩=(Q.point x).faceComponent ⟨F,hFx⟩ := by
  let W := probabilitySet (labelWindow Γ n R s)
  have hZ : ∀ i∈Finset.range (n+1), ∀ᶠ y in nhds x,
      (Q.point y).Z i∩W=(Q.point x).Z i∩W := by
    intro i _
    exact (marked_localConstancy_window (Q.pair i).P (labelWindow Γ n R s)).eventually_eq x
  filter_upwards [((Q.pair 0).T.localConstancy (simplexVertices s) ⟨s,hs,rfl⟩).eventually_eq x,
    (Filter.eventually_all_finite (Finset.finite_toSet (Finset.range (n+1)))).mpr hZ] with y hT hy
  refine ⟨hT,?_⟩
  intro F hFx hFy hFs
  have hm := hFs (Cuts.vertexMean_mem_convexHull
    (((Q.pair 0).T.val x).complex.nonempty_of_mem_faces hFx))
  apply (Q.point y).faceComponent_eq_of_window (Q.point x) F hFy hFx W
    (component_subset_window Γ hΓ Q hK hn hR y ⟨F,hFy⟩ s hm)
    (component_subset_window Γ hΓ Q hK hn hR x ⟨F,hFx⟩ s hm)
  intro i hi
  exact hy i (Finset.mem_range.mpr (by omega))
end Sparse.GraphGeometry
namespace Sparse.OrbitForms
open Set Finset
open scoped BassTrace.Sparse Classical
variable {H Y : Type*} [Group H] [MulAction H Y]
private def componentVectorEmbedding : (Y →₀ ℝ) →ₗ[ℝ] lp (fun _ : Y => ℝ) 2 :=
  Finsupp.linearCombination ℝ (fun y => lp.single 2 y 1)
private lemma componentVectorEmbedding_apply (v : Y →₀ ℝ) (y : Y) :
    componentVectorEmbedding v y = v y := by
  simp only [componentVectorEmbedding,Finsupp.linearCombination_apply, Finsupp.sum,
    lp.coeFn_sum,lp.coeFn_smul,Finset.sum_apply,Pi.smul_apply,lp.single_apply]
  simp [Pi.single_apply,eq_comm]
lemma push_norm (h : H) (p : Y →₀ ℝ) : ‖push h p‖=‖p‖ := by
  change ‖componentVectorEmbedding (push h p)‖=‖componentVectorEmbedding p‖
  rw [lp.norm_eq_tsum_rpow (by norm_num : 0<(2:ENNReal).toReal),
    lp.norm_eq_tsum_rpow (by norm_num : 0<(2:ENNReal).toReal)]
  congr 1
  simp only [componentVectorEmbedding_apply,push_apply]
  exact (Equiv.tsum_eq (MulAction.toPerm h⁻¹ : Y ≃ Y) (fun i=>‖p i‖ ^ (2:ENNReal).toReal))
def pushIsometry (h : H) : (Y →₀ ℝ) ≃ₗᵢ[ℝ] (Y →₀ ℝ) where
  __ := push h
  norm_map' := push_norm h
def pushHomeomorph (h : H) : (Y →₀ ℝ) ≃ₜ (Y →₀ ℝ) :=
  (pushIsometry h).toHomeomorph
variable {X : Type*} [TopologicalSpace X] [MulAction H X]
variable {K : Geometry.SimplicialComplex ℝ (Y →₀ ℝ)}
variable {ρ : (Y →₀ ℝ) → (Y →₀ ℝ) → ℝ} {R : ℝ} {n : ℕ}
variable (Q : SeparatingFiltration (H := H) (X := X) K ρ R n)
namespace SeparatingFiltration
def translateFace (h : H) (x : X) (F : (Q.point x).FinalFace) :
    (Q.point (h • x)).FinalFace :=
  ⟨F.val.map (push h).toEmbedding,(Q.pair 0).equivariant h x F.val F.property⟩
lemma translateFace_mean (h : H) (x : X) (F : (Q.point x).FinalFace) :
    Cuts.vertexMean (Q.translateFace h x F).val=push h (Cuts.vertexMean F.val) :=
  Cuts.vertexMean_map (push h).toAffineEquiv
    (((Q.pair 0).T.val x).complex.nonempty_of_mem_faces F.property)
lemma push_mem_marked_iff (h : H) (x : X) (i : ℕ) (p : Y →₀ ℝ) :
    push h p∈(Q.point (h • x)).Z i ↔ p∈(Q.point x).Z i := by
  constructor
  · intro hp
    have hh := (Q.pair i).markedEquivariant h⁻¹ (h • x) (push h p) hp
    change p∈(Q.pair i).P.val x
    simpa only [push_inv_push,inv_smul_smul] using hh
  · exact (Q.pair i).markedEquivariant h x p
lemma translateFace_level (h : H) (x : X) (F : (Q.point x).FinalFace) :
    (Q.point (h • x)).faceLevel (Q.translateFace h x F)=(Q.point x).faceLevel F := by
  apply Nat.le_antisymm
  · apply ((Q.point (h • x)).mean_mem_iff_level_le _ ((Q.point x).faceLevel_le F)).mp
    rw [Q.translateFace_mean,Q.push_mem_marked_iff]
    exact (Q.point x).mean_mem_faceLevel F
  · apply ((Q.point x).mean_mem_iff_level_le F ((Q.point (h • x)).faceLevel_le _)).mp
    have hh := (Q.point (h • x)).mean_mem_faceLevel (Q.translateFace h x F)
    rwa [Q.translateFace_mean,Q.push_mem_marked_iff] at hh
lemma push_mem_stratum_iff (h : H) (x : X) (i : ℕ) (p : Y →₀ ℝ) :
    push h p∈(Q.point (h • x)).stratum i ↔ p∈(Q.point x).stratum i := by
  simp only [Cuts.PointFiltration.stratum,Cuts.PointFiltration.below,Set.mem_sdiff,
    Q.push_mem_marked_iff]
  split_ifs <;> simp only [Set.mem_empty_iff_false,Q.push_mem_marked_iff]
lemma stratum_image (h : H) (x : X) (i : ℕ) :
    push h '' (Q.point x).stratum i=(Q.point (h • x)).stratum i := by
  ext p
  constructor
  · rintro ⟨q,hq,rfl⟩
    exact (Q.push_mem_stratum_iff h x i q).mpr hq
  · intro hp
    refine ⟨push h⁻¹ p,?_,?_⟩
    · have hh := (Q.push_mem_stratum_iff h⁻¹ (h • x) i p).mpr hp
      simpa only [inv_smul_smul] using hh
    · rw [←push_mul,mul_inv_cancel,push_one]
lemma translateFace_component (h : H) (x : X) (F : (Q.point x).FinalFace) :
    (Q.point (h • x)).faceComponent (Q.translateFace h x F)=
      push h '' (Q.point x).faceComponent F := by
  unfold Cuts.PointFiltration.faceComponent
  rw [Q.translateFace_level,Q.translateFace_mean]
  rw [←Q.stratum_image h x ((Q.point x).faceLevel F)]
  exact ((pushHomeomorph h).image_connectedComponentIn
    ((Q.point x).mean_mem_stratum F)).symm
end SeparatingFiltration
end Sparse.OrbitForms
end BassTrace
end
end OAI

end
section
namespace OAI
open Set MeasureTheory
open Finset MeasureTheory intervalIntegral
namespace BassTrace.Sparse.Cuts
open Set Finset
open scoped Classical
noncomputable section
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {K : Geometry.SimplicialComplex ℝ V} {n : ℕ}
namespace PointFiltration
variable (Q : PointFiltration K n)
lemma face_in_zero_carrier (hK : ∀ F ∈ K.faces, F.card ≤ n+1)
    {i : ℕ} (hi : i ≤ n) {z : V} (hz : z ∈ Q.Z 0) :
    ∃ S ∈ (Q.T i).faces, S.card = i+1 ∧ ∀ F ∈ (Q.T 0).faces,
      F.card = i+1 → convexHull ℝ (F : Set V) ⊆ Q.Z i → z ∈ F →
      convexHull ℝ (F : Set V) ⊆ convexHull ℝ (S : Set V) := by
  obtain ⟨S,hS,_,_,hc,_,huniq⟩ := Q.zero_carrier hK hi hz
  refine ⟨S,hS,hc,?_⟩
  intro F hF hFc hFZ hzF
  obtain ⟨D,hD⟩ := Q.refines (Nat.zero_le i) hi
  obtain ⟨U,hU,hUZ,hFU⟩ := D.carrier_marked (Q.marked i hi) (hD.symm ▸ hF) hFZ
  have hu := Q.dimension_bound hK hi hU hUZ
  have hlu := (Q.T 0).indep hF |>.card_le_card_of_subset_affineSpan
    ((subset_convexHull ℝ _).trans (hFU.trans (convexHull_subset_affineSpan _)))
  have hcU : U.card = i+1 := by omega
  have he : U = S := huniq U hU (hFU (subset_convexHull ℝ _ hzF)) hcU
  exact he ▸ hFU
lemma flagged_cofaces_card_le_two (hK : ∀ F ∈ K.faces, F.card ≤ n+1)
    {i : ℕ} (hi : i < n) {z : V} (hz : z ∈ Q.Z 0) {F : Finset V}
    (hFc : F.card = i+1) (hzF : z ∈ F) (B : Finset (Finset V))
    (hB : ∀ E ∈ B, E ∈ (Q.T 0).faces ∧ E.card = i+2 ∧
      convexHull ℝ (E : Set V) ⊆ Q.Z (i+1) ∧ F ⊆ E) : B.card ≤ 2 := by
  obtain ⟨S,_,hSc,hS⟩ := Q.face_in_zero_carrier hK (show i+1 ≤ n by omega) hz
  apply BassTrace.Sparse.facet_coface_card_le_two (Q.T 0) (S := S) ⟨z,hzF⟩
  · omega
  · exact fun E hE => (hB E hE).1
  · intro E hE
    obtain ⟨_,hc,_,hFE⟩ := hB E hE
    exact ⟨hFE,by omega⟩
  · intro E hE
    obtain ⟨hE,hc,hEZ,hFE⟩ := hB E hE
    exact (subset_convexHull ℝ _).trans (hS E hE (by omega) hEZ (hFE hzF))
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
variable (V : Type*) [AddCommGroup V] [Module ℝ V]
private abbrev BIndex := Module.Free.ChooseBasisIndex ℝ V
private def embedding : V →ₗ[ℝ] lp (fun _ : BIndex V=>ℝ) 2 :=
  (Finsupp.linearCombination ℝ (fun i=>lp.single 2 i 1)).comp
    (Module.Free.chooseBasis ℝ V).repr.toLinearMap
private lemma embedding_apply (v : V) (i : BIndex V) :
    embedding V v i=(Module.Free.chooseBasis ℝ V).repr v i := by
  simp only [embedding,LinearMap.comp_apply,LinearEquiv.coe_toLinearMap,
    Finsupp.linearCombination_apply,Finsupp.sum,lp.coeFn_sum,lp.coeFn_smul,
    Finset.sum_apply,Pi.smul_apply,lp.single_apply]
  simp [Pi.single_apply,eq_comm]
private lemma embedding_injective : Function.Injective (embedding V) := by
  intro v w h
  apply (Module.Free.chooseBasis ℝ V).repr.injective
  ext i
  simpa only [embedding_apply] using congrArg (fun f : lp (fun _ : BIndex V=>ℝ) 2=>f i) h
private abbrev algebraicNormedGroup : NormedAddCommGroup V :=
  NormedAddCommGroup.induced _ _ (embedding V) (embedding_injective V)
private abbrev algebraicNormedSpace : letI := algebraicNormedGroup V; NormedSpace ℝ V :=
  NormedSpace.induced ℝ _ _ (embedding V)
end AlgebraicNorm
variable {X V W : Type*} [MeasurableSpace X]
  [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
variable (μ : Measure X)
def average (f : SimpleFunc X V) : V :=
  ∑v∈f.range, μ.real (f⁻¹' {v}) • v
lemma average_add [IsFiniteMeasure μ] (f g : SimpleFunc X V) :
    average μ (f+g)=average μ f+average μ g := by
  let :=  algebraicNormedGroup V
  let :=  algebraicNormedSpace V
  simpa only [average,SimpleFunc.integral_eq] using
    SimpleFunc.integral_add (f.integrable_of_isFiniteMeasure) (g.integrable_of_isFiniteMeasure)
lemma average_map [IsFiniteMeasure μ] (L : V →ₗ[ℝ] W) (f : SimpleFunc X V) :
    average μ (f.map L)=L (average μ f) := by
  let :=  algebraicNormedGroup V
  let :=  algebraicNormedSpace V
  let :=  algebraicNormedGroup W
  let :=  algebraicNormedSpace W
  rw [average,← SimpleFunc.integral_eq,
    SimpleFunc.map_integral f L f.integrable_of_isFiniteMeasure L.map_zero]
  simp only [average,map_sum,map_smul]
lemma average_const [IsProbabilityMeasure μ] (v : V) :
    average μ (SimpleFunc.const X v)=v := by
  let :=  algebraicNormedGroup V
  let :=  algebraicNormedSpace V
  rw [average,← SimpleFunc.integral_eq,SimpleFunc.integral_const]
  simp
lemma average_precomp {Z : Type*} [MeasurableSpace Z] (ν : Measure Z)
    (h : Z → X) (hh : MeasurePreserving h ν μ) (hs : Function.Surjective h)
    (f : SimpleFunc X V) :
    average ν (f.comp h hh.measurable)=average μ f := by
  have he : (f.comp h hh.measurable).range=f.range := by
    ext v
    simp only [SimpleFunc.mem_range,Set.mem_range]
    constructor
    · rintro ⟨z,rfl⟩
      exact ⟨h z,rfl⟩
    · rintro ⟨x,rfl⟩
      obtain ⟨z,rfl⟩ := hs x
      exact ⟨z,rfl⟩
  unfold average
  rw [he]
  apply Finset.sum_congr rfl
  intro v _
  congr 1
  exact hh.measureReal_preimage (f.measurableSet_fiber v).nullMeasurableSet
section LocallyConstant
variable [TopologicalSpace X] [CompactSpace X] [OpensMeasurableSpace X]
variable {A : Type*}
def ofLocallyConstant (f : X → A) (hf : IsLocallyConstant f) : SimpleFunc X A where
  toFun := f
  measurableSet_fiber' v := (hf.isClopen_fiber v).isOpen.measurableSet
  finite_range' := hf.range_finite
@[simp] lemma ofLocallyConstant_apply (f : X → A) (hf : IsLocallyConstant f) (x : X) :
    ofLocallyConstant f hf x=f x := rfl
end LocallyConstant
variable [IsFiniteMeasure μ]
lemma average_complex_eq_integral (f : SimpleFunc X ℂ) :
    average μ f=∫x,f x∂μ := by
  rw [average,← SimpleFunc.integral_eq]
  exact f.integral_eq_integral f.integrable_of_isFiniteMeasure
lemma norm_average_le_integral_norm (f : SimpleFunc X ℂ) :
    ‖average μ f‖≤∫x,‖f x‖∂μ := by
  rw [average_complex_eq_integral]
  exact norm_integral_le_integral_norm _
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
open Set MeasureTheory
open Finset MeasureTheory intervalIntegral
noncomputable section
namespace BassTrace.FreeParameter
open Set MeasureTheory
open scoped Pointwise
universe u v
variable {H : Type u} [Group H] (S : Subgroup H)
noncomputable def residue (t : H) : S :=
  ⟨(Quotient.out (QuotientGroup.mk t : H ⧸ S))⁻¹ * t,
    QuotientGroup.leftRel_apply.mp
      (@Quotient.exact' _ (QuotientGroup.leftRel S) _ _ (Quotient.out_eq' _))⟩
lemma residue_out (q : H ⧸ S) : residue S q.out = 1 := by
  apply Subtype.ext
  simp [residue]
lemma residue_mul (t : H) (s : S) : residue S (t * s) = residue S t * s := by
  apply Subtype.ext
  simp [residue, QuotientGroup.mk_mul_of_mem _ s.property, mul_assoc]
lemma out_mul_residue (t : H) :
    (Quotient.out (QuotientGroup.mk t : H ⧸ S)) * residue S t = t := by
  simp [residue]
variable {C : Type v} [Group C] (χ : S →* C)
abbrev Offsets := (H ⧸ S) → C
noncomputable def encode (ω : Offsets S (C := C)) (t : H) : C :=
  ω (QuotientGroup.mk t) * χ (residue S t)
lemma encode_out (ω : Offsets S (C := C)) (q : H ⧸ S) :
    encode S χ ω q.out = ω q := by
  simp [encode, residue_out]
lemma encode_mul (ω : Offsets S (C := C)) (t : H) (s : S) :
    encode S χ ω (t * s) = encode S χ ω t * χ s := by
  simp [encode, QuotientGroup.mk_mul_of_mem _ s.property, residue_mul, mul_assoc]
lemma encode_injective : Function.Injective (encode S χ) := by
  intro ω η h
  funext q
  simpa only [encode_out] using congrFun h q.out
noncomputable def shift (h : H) (ω : Offsets S (C := C)) : Offsets S (C := C) :=
  fun q => encode S χ ω (h⁻¹ * q.out)
lemma encode_shift (h : H) (ω : Offsets S (C := C)) (t : H) :
    encode S χ (shift S χ h ω) t = encode S χ ω (h⁻¹ * t) := by
  change encode S χ ω (h⁻¹ * (QuotientGroup.mk t : H ⧸ S).out) *
    χ (residue S t) = _
  rw [← encode_mul, mul_assoc, out_mul_residue]
lemma shift_one (ω : Offsets S (C := C)) : shift S χ 1 ω = ω := by
  apply encode_injective S χ
  funext t
  simp [encode_shift]
lemma shift_mul (h k : H) (ω : Offsets S (C := C)) :
    shift S χ (h * k) ω = shift S χ h (shift S χ k ω) := by
  apply encode_injective S χ
  funext t
  simp [encode_shift, mul_assoc]
lemma shift_not_fixed (a : S) (ha : χ a ≠ 1) (ω : Offsets S (C := C)) :
    shift S χ (a : H) ω ≠ ω := by
  intro h
  have he := congrArg (fun η => encode S χ η (a : H)) h
  rw [encode_shift, inv_mul_cancel] at he
  have hm := encode_mul S χ ω 1 a
  simp only [one_mul] at hm
  rw [hm] at he
  exact ha ((mul_left_cancel (a := encode S χ ω 1)) (by simpa using he.symm))
lemma continuous_shift [TopologicalSpace C] [ContinuousMul C] (h : H) :
    Continuous (shift S χ h) := by
  apply continuous_pi
  intro q
  exact (continuous_apply _).mul continuous_const
lemma measurable_shift [MeasurableSpace C] [MeasurableMul₂ C] (h : H) :
    Measurable (shift S χ h) := by
  apply Measurable.of_eval
  intro q
  exact (measurable_pi_apply _).mul measurable_const
section Probability
variable [Fintype C] [MeasurableSpace C] [MeasurableSingletonClass C]
noncomputable def uniform : Measure C := (PMF.uniformOfFintype C).toMeasure
instance uniform_probability : IsProbabilityMeasure (uniform (C := C)) := by
  unfold uniform
  infer_instance
lemma uniform_map_equiv (e : C ≃ C) :
    (uniform (C := C)).map e = uniform := by
  apply Measure.ext_of_singleton
  intro c
  rw [Measure.map_apply (measurable_of_finite _) (measurableSet_singleton c)]
  have he : e ⁻¹' {c} = {e.symm c} := by
    ext x
    exact e.eq_symm_apply.symm
  rw [he]
  change (PMF.uniformOfFintype C).toMeasure {e.symm c} =
    (PMF.uniformOfFintype C).toMeasure {c}
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  simp
noncomputable def offsetMeasure : Measure (Offsets S (C := C)) :=
  Measure.infinitePi (fun _ : H ⧸ S => uniform (C := C))
instance offsetMeasure_probability : IsProbabilityMeasure (offsetMeasure S (C := C)) := by
  unfold offsetMeasure
  infer_instance
omit [MeasurableSingletonClass C] in
lemma reindex_measure (h : H) :
    (offsetMeasure S (C := C)).map (fun ω q => ω (h⁻¹ • q)) = offsetMeasure S := by
  have hr := Measure.infinitePi_map_piCongrLeft
    (fun _ : H ⧸ S => uniform (C := C)) (MulAction.toPerm (β := H ⧸ S) h)
  unfold offsetMeasure
  rw [← hr]
  congr 1
  funext ω q
  simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply]
lemma offsetMeasure_shift (h : H) :
    (offsetMeasure S (C := C)).map (shift S χ h) = offsetMeasure S := by
  let m : (H ⧸ S) → C := fun q => χ (residue S (h⁻¹ * q.out))
  have hm : ∀ q, Measurable (fun c : C => c * m q) :=
    fun _ => measurable_of_finite _
  have hp : (offsetMeasure S (C := C)).map (fun ω q => ω q * m q) =
      offsetMeasure S := by
    rw [offsetMeasure, Measure.infinitePi_map_pi _ hm]
    congr 1
    funext q
    exact uniform_map_equiv (Equiv.mulRight (m q))
  have hf : shift S χ h = (fun ω q => ω q * m q) ∘
      (fun ω q => ω (h⁻¹ • q)) := by
    funext ω q
    change ω (QuotientGroup.mk (h⁻¹ * q.out)) * _ = ω (h⁻¹ • q) * _
    rw [show (QuotientGroup.mk (h⁻¹ * q.out) : H ⧸ S) = h⁻¹ • q from
      MulAction.Quotient.mk_smul_out S h⁻¹ q]
  have hm' : Measurable (fun ω : Offsets S (C := C) => fun q => ω q * m q) :=
    Measurable.of_eval (fun q => (hm q).comp (measurable_pi_apply q))
  have hr' : Measurable (fun ω : Offsets S (C := C) => fun q => ω (h⁻¹ • q)) :=
    Measurable.of_eval (fun _ => measurable_pi_apply _)
  rw [hf, ← Measure.map_map hm' hr', reindex_measure, hp]
end Probability
structure Character (a : H) where
  Color : Type u
  [group : Group Color]
  [finite : Finite Color]
  value : Subgroup.zpowers a →* Color
  detects : value ⟨a, Subgroup.mem_zpowers a⟩ ≠ 1
instance {a : H} (F : Character a) : Group F.Color := F.group
instance {a : H} (F : Character a) : Finite F.Color := F.finite
lemma zpowers_subtype_generator (a : H) :
    Subgroup.zpowers (⟨a, Subgroup.mem_zpowers a⟩ : Subgroup.zpowers a) = ⊤ := by
  apply top_unique
  intro s _
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp s.property
  apply Subgroup.mem_zpowers_iff.mpr
  refine ⟨j, ?_⟩
  apply Subtype.ext
  exact hj
noncomputable def character (a : H) (ha : a ≠ 1) : Character a := by
  classical
  by_cases hf : IsOfFinOrder a
  · letI : Finite (Subgroup.zpowers a) := hf.finite_zpowers
    exact { Color := Subgroup.zpowers a
            group := inferInstance
            finite := inferInstance
            value := MonoidHom.id _
            detects := fun h => ha (congrArg Subtype.val h) }
  · letI : Infinite (Subgroup.zpowers a) := (infinite_zpowers.mpr hf).to_subtype
    let e := intEquivOfZPowersEqTop
      (⟨a, Subgroup.mem_zpowers a⟩ : Subgroup.zpowers a) (zpowers_subtype_generator a)
    let f : Subgroup.zpowers a →* ULift.{u} (Multiplicative (ZMod 2)) :=
      MulEquiv.ulift.symm.toMonoidHom.comp
        ((AddMonoidHom.toMultiplicative (Int.castAddHom (ZMod 2))).comp e.symm.toMonoidHom)
    refine { Color := ULift.{u} (Multiplicative (ZMod 2))
             group := inferInstance
             finite := inferInstance
             value := f
             detects := ?_ }
    intro he
    have he' := congrArg (fun z : ULift (Multiplicative (ZMod 2)) => z.down.toAdd) he
    have hx : e.symm ⟨a, Subgroup.mem_zpowers a⟩ = Multiplicative.ofAdd 1 :=
      intEquivOfZPowersEqTop_symm_self (zpowers_subtype_generator a)
    norm_num [f, hx] at he'
    exact (one_ne_zero : (1 : ZMod 2) ≠ 0) he'
namespace Character
variable {a : H} (F : Character a)
instance colorTopology : TopologicalSpace F.Color := ⊥
instance colorDiscrete : DiscreteTopology F.Color := ⟨rfl⟩
instance colorMeasurable : MeasurableSpace F.Color := ⊤
instance colorSingleton : MeasurableSingletonClass F.Color := ⟨fun _ => trivial⟩
instance colorBorel : BorelSpace F.Color := ⟨borel_eq_top_of_discrete.symm⟩
noncomputable instance colorFintype : Fintype F.Color := Fintype.ofFinite _
end Character
variable (H)
abbrev Space := (a : {a : H // a ≠ 1}) →
  Offsets (Subgroup.zpowers a.val) (C := (character a.val a.property).Color)
instance spaceTopology : TopologicalSpace (Space H) :=
  inferInstanceAs (TopologicalSpace ((a : {a : H // a ≠ 1}) →
    Offsets (Subgroup.zpowers a.val) (C := (character a.val a.property).Color)))
instance spaceMeasurable : MeasurableSpace (Space H) :=
  inferInstanceAs (MeasurableSpace ((a : {a : H // a ≠ 1}) →
    Offsets (Subgroup.zpowers a.val) (C := (character a.val a.property).Color)))
instance spaceCompact : CompactSpace (Space H) :=
  inferInstanceAs (CompactSpace ((a : {a : H // a ≠ 1}) →
    Offsets (Subgroup.zpowers a.val) (C := (character a.val a.property).Color)))
instance spaceT2 : T2Space (Space H) :=
  inferInstanceAs (T2Space ((a : {a : H // a ≠ 1}) →
    Offsets (Subgroup.zpowers a.val) (C := (character a.val a.property).Color)))
instance spaceTotallyDisconnected : TotallyDisconnectedSpace (Space H) :=
  inferInstanceAs (TotallyDisconnectedSpace ((a : {a : H // a ≠ 1}) →
    Offsets (Subgroup.zpowers a.val) (C := (character a.val a.property).Color)))
instance quotientCountable [Countable H] (S : Subgroup H) : Countable (H ⧸ S) :=
  (QuotientGroup.mk_surjective (s := S)).countable
instance spaceBorel [Countable H] : BorelSpace (Space H) :=
  inferInstanceAs (BorelSpace ((a : {a : H // a ≠ 1}) →
    Offsets (Subgroup.zpowers a.val) (C := (character a.val a.property).Color)))
noncomputable instance spaceAction : MulAction H (Space H) where
  smul h ω a := shift _ (character a.val a.property).value h (ω a)
  one_smul ω := funext fun a => shift_one _ _ (ω a)
  mul_smul h k ω := funext fun a => shift_mul _ _ h k (ω a)
instance spaceContinuous : ContinuousConstSMul H (Space H) where
  continuous_const_smul h := by
    apply continuous_pi
    intro a
    exact (continuous_shift _ _ h).comp (continuous_apply a)
instance spaceFree : IsCancelSMul H (Space H) := by
  apply isCancelSMul_iff_eq_one_of_smul_eq.mpr
  intro h ω he
  by_contra hn
  let a : {a : H // a ≠ 1} := ⟨h, hn⟩
  exact shift_not_fixed _ (character h hn).value
    ⟨h, Subgroup.mem_zpowers h⟩ (character h hn).detects (ω a) (congrFun he a)
noncomputable def probability : Measure (Space H) :=
  Measure.infinitePi (fun a : {a : H // a ≠ 1} =>
    offsetMeasure (Subgroup.zpowers a.val) (C := (character a.val a.property).Color))
instance probability_isProbability : IsProbabilityMeasure (probability H) := by
  have : ∀ a : {a : H // a ≠ 1}, IsProbabilityMeasure
      (offsetMeasure (Subgroup.zpowers a.val) (C := (character a.val a.property).Color)) :=
    fun a => offsetMeasure_probability _
  unfold probability
  infer_instance
lemma probability_preserving (h : H) :
    MeasurePreserving (fun ω : Space H => h • ω) (probability H) (probability H) := by
  have hm : ∀ a : {a : H // a ≠ 1},
      Measurable (shift (Subgroup.zpowers a.val) (character a.val a.property).value h) :=
    fun a => measurable_shift _ _ h
  refine ⟨Measurable.of_eval (fun a => (hm a).comp (measurable_pi_apply a)), ?_⟩
  change Measure.map (fun (ω : Space H) (a : {a : H // a ≠ 1}) =>
    shift _ (character a.val a.property).value h (ω a)) _ = _
  rw [probability, Measure.infinitePi_map_pi _ hm]
  congr 1
  funext a
  exact offsetMeasure_shift _ _ h
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
def uniformVector (s : Finset Y) : Y →₀ ℂ :=
  ∑y∈s,Finsupp.single y (s.card : ℂ)⁻¹
lemma uniformVector_sum (s : Finset Y) (hs : s.Nonempty) :
    (uniformVector s).sum (fun _ c=>c)=1 := by
  have hh : (Finsupp.linearCombination ℂ (fun _ : Y=>(1:ℂ))) (uniformVector s)=1 := by
    simp [uniformVector,Nat.ne_of_gt hs.card_pos]
  simpa only [Finsupp.linearCombination_apply,smul_eq_mul,mul_one] using hh
lemma uniformVector_nat (s : Finset Y) {Z : Type*} (e : Y ≃ Z) :
    uniformVector (s.map e.toEmbedding)=Finsupp.domLCongr (R := ℂ) e (uniformVector s) := by
  simp only [uniformVector,Finset.sum_map,Finset.card_map,map_sum]
  apply Finset.sum_congr rfl
  intro y _
  exact (Finsupp.domLCongr_single (R := ℂ) e y _).symm
lemma supportVertices_push {H : Type*} [Group H] [MulAction H Y]
    (h : H) (U : Set (Y →₀ ℝ)) :
    supportVertices (OrbitForms.push h '' U)= (fun y=>h • y) '' supportVertices U := by
  ext y
  constructor
  · rintro ⟨p,⟨q,hq,rfl⟩,hy⟩
    refine ⟨h⁻¹ • y,⟨q,hq,?_⟩,smul_inv_smul h y⟩
    simpa only [Finsupp.mem_support_iff,OrbitForms.push_apply] using hy
  · rintro ⟨z,⟨p,hp,hz⟩,rfl⟩
    refine ⟨OrbitForms.push h p,⟨p,hp,rfl⟩,?_⟩
    simpa only [Finsupp.mem_support_iff,OrbitForms.push_apply,inv_smul_smul] using hz
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
lemma componentVertices_nonempty (x : X) (F : (Q.point x).FinalFace) :
    (componentVertices Γ hΓ Q hK hn hR x F).Nonempty := by
  obtain ⟨y,hy⟩ := componentSupport_nonempty Γ hΓ Q x F
  exact ⟨y,(mem_componentVertices Γ hΓ Q hK hn hR x F y).mpr hy⟩
lemma componentVertices_nat (h : H) (x : X) (F : (Q.point x).FinalFace) :
    componentVertices Γ hΓ Q hK hn hR (h • x) (Q.translateFace h x F)=
      (componentVertices Γ hΓ Q hK hn hR x F).map (MulAction.toPerm h).toEmbedding := by
  ext y
  simp only [mem_componentVertices,Finset.mem_map,Equiv.coe_toEmbedding,MulAction.toPerm_apply]
  rw [Q.translateFace_component,supportVertices_push]
  rfl
def componentWeight (x : X) (F : (Q.point x).FinalFace) : Y →₀ ℂ :=
  uniformVector (componentVertices Γ hΓ Q hK hn hR x F)
lemma componentWeight_sum (x : X) (F : (Q.point x).FinalFace) :
    (componentWeight Γ hΓ Q hK hn hR x F).sum (fun _ c=>c)=1 :=
  uniformVector_sum _ (componentVertices_nonempty Γ hΓ Q hK hn hR x F)
lemma componentWeight_nat (h : H) (x : X) (F : (Q.point x).FinalFace) :
    componentWeight Γ hΓ Q hK hn hR (h • x) (Q.translateFace h x F)=
      Finsupp.domLCongr (R := ℂ) (MulAction.toPerm h) (componentWeight Γ hΓ Q hK hn hR x F) := by
  unfold componentWeight
  rw [componentVertices_nat,uniformVector_nat]
lemma componentWeight_eq_of_component (x y : X)
    (F : (Q.point x).FinalFace) (G : (Q.point y).FinalFace)
    (h : (Q.point x).faceComponent F=(Q.point y).faceComponent G) :
    componentWeight Γ hΓ Q hK hn hR x F=componentWeight Γ hΓ Q hK hn hR y G := by
  unfold componentWeight
  congr 1
  ext z
  simp only [mem_componentVertices,h]
end
open Set Finset
open scoped BassTrace.Sparse Classical
variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y]
  [TopologicalSpace X] [MulAction H X]
variable {K : PreAbstractSimplicialComplex Y} {n : ℕ} {R : ℝ}
variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)
variable (Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
  (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K)
  (GraphGeometry.realizationDistance Γ hΓ K n) R n)
variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)
variable (hn : 0<n) (hR : 0≤R) (y₀ : Y)
def faceWeight (x : X) (F : Finset (Y →₀ ℝ)) : Y →₀ ℂ :=
  if hF : F∈((Q.pair 0).T.val x).complex.faces then
    componentWeight Γ hΓ Q hK hn hR x ⟨F,hF⟩
  else Finsupp.single y₀ 1
lemma faceWeight_sum (x : X) (F : Finset (Y →₀ ℝ)) :
    (faceWeight Γ hΓ Q hK hn hR y₀ x F).sum (fun _ c=>c)=1 := by
  unfold faceWeight
  split_ifs
  · exact componentWeight_sum Γ hΓ Q hK hn hR x _
  · simp
lemma faceWeight_face (x : X) (F : (Q.point x).FinalFace) :
    faceWeight Γ hΓ Q hK hn hR y₀ x F.val=componentWeight Γ hΓ Q hK hn hR x F := by
  unfold faceWeight
  have hf : F.val∈((Q.pair 0).T.val x).complex.faces := F.property
  rw [dite_eq_left hf]
  rfl
lemma faceWeight_nat (h : H) (x : X) (F : (Q.point x).FinalFace) :
    faceWeight Γ hΓ Q hK hn hR y₀ (h • x) (F.val.map (OrbitForms.push h).toEmbedding)=
      Finsupp.domLCongr (R := ℂ) (MulAction.toPerm h)
        (faceWeight Γ hΓ Q hK hn hR y₀ x F.val) := by
  change faceWeight Γ hΓ Q hK hn hR y₀ (h • x) (Q.translateFace h x F).val=_
  rw [faceWeight_face,faceWeight_face,componentWeight_nat]
lemma faceWeight_nested_equal_level (x : X) (F G : (Q.point x).FinalFace)
    (hFG : F.val⊆G.val) (hlevel : (Q.point x).faceLevel F=(Q.point x).faceLevel G) :
    faceWeight Γ hΓ Q hK hn hR y₀ x F.val=faceWeight Γ hΓ Q hK hn hR y₀ x G.val := by
  rw [faceWeight_face,faceWeight_face]
  exact componentWeight_eq_of_component Γ hΓ Q hK hn hR x x F G
    ((Q.point x).faceComponent_eq_of_level_eq F G hFG hlevel)
lemma faceWeight_local (s : Finset Y) (hs : s∈K.faces) (x : X) : ∀ᶠ y in nhds x,
    (Cuts.restrictComplex ((Q.pair 0).T.val y).complex
      (convexHull ℝ (simplexVertices s : Set (Y →₀ ℝ)))).faces=
    (Cuts.restrictComplex ((Q.pair 0).T.val x).complex
      (convexHull ℝ (simplexVertices s : Set (Y →₀ ℝ)))).faces ∧
    ∀ F∈(Cuts.restrictComplex ((Q.pair 0).T.val x).complex
      (convexHull ℝ (simplexVertices s : Set (Y →₀ ℝ)))).faces,
      faceWeight Γ hΓ Q hK hn hR y₀ y F=faceWeight Γ hΓ Q hK hn hR y₀ x F := by
  filter_upwards [GraphGeometry.faceComponents_eq_local Γ hΓ Q hK hn hR s hs x] with y hy
  refine ⟨hy.1,?_⟩
  intro F hF
  have hF' : F∈(Cuts.restrictComplex ((Q.pair 0).T.val y).complex
      (convexHull ℝ (simplexVertices s : Set (Y →₀ ℝ)))).faces := hy.1.symm ▸ hF
  change F∈((Q.pair 0).T.val x).complex.faces ∧ _ at hF
  change F∈((Q.pair 0).T.val y).complex.faces ∧ _ at hF'
  rw [faceWeight,faceWeight,dite_eq_left hF.1,dite_eq_left hF'.1]
  exact componentWeight_eq_of_component Γ hΓ Q hK hn hR y x ⟨F,hF'.1⟩ ⟨F,hF.1⟩
    (hy.2 F hF.1 hF'.1 (convexHull_min hF.2 (convex_convexHull ℝ _)))
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
omit [LinearOrder (Y →₀ ℝ)] in
lemma chart_vertex {k : ℕ} (v : Fin k → Y) (hv : Function.Injective v) (j : Fin k) :
    chart v (Finsupp.single (v j) 1)=Pi.single j 1 := by
  ext i
  simp [chart_apply,Finsupp.single_apply,Pi.single_apply,hv.eq_iff,eq_comm]
def localTriangulation (s : Finset Y) :=
  Cuts.restrictComplex T.complex (convexHull ℝ (simplexVertices s : Set (Y →₀ ℝ)))
omit [LinearOrder (Y →₀ ℝ)] in
lemma localTriangulation_finite (s : Finset Y) (hs : s∈K.faces) :
    (localTriangulation T s).faces.Finite := T.finite (simplexVertices s) ⟨s,hs,rfl⟩
omit [LinearOrder (Y →₀ ℝ)] in
lemma localTriangulation_space (s : Finset Y) (hs : s∈K.faces) :
    (localTriangulation T s).space=convexHull ℝ (simplexVertices s : Set (Y →₀ ℝ)) := by
  rw [localTriangulation,Cuts.restrictComplex_space_of_respects _ _
    (T.respects (simplexVertices s) ⟨s,hs,rfl⟩),T.space_eq]
  exact Set.inter_eq_right.mpr
    ((Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).convexHull_subset_space ⟨s,hs,rfl⟩)
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
lemma subdivision_wedge_face (k : ℕ) (v : Fin (k+1) → Y)
    (hs : Finset.univ.image v∈K.faces) :
    subdivision T (k+1) (wedge (k+1) v)=
      chain (faces (localTriangulation T (Finset.univ.image v))
        (localTriangulation_finite T _ hs) (k+1)) (chart v) := by
  rw [subdivision_wedge_succ,tupleSubdivision,dite_eq_left hs]
end
open Set Finset
open scoped BassTrace.Sparse Classical
open Sparse Oriented ChainHomotopy Fundamental OrientedIncidence
variable {Y : Type*} [LinearOrder Y] [LinearOrder (Y →₀ ℝ)]
variable {K : PreAbstractSimplicialComplex Y}
variable (T : Cuts.Subdivision (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
omit [LinearOrder (Y →₀ ℝ)] in
lemma simplexVertices_image {k : ℕ} (v : Fin k → Y) :
    (simplexVertices (Finset.univ.image v) : Set (Y →₀ ℝ))=
      Set.range (fun i=>Finsupp.single (v i) (1:ℝ)) := by
  ext p
  simp only [simplexVertices,Finset.coe_image,Finset.coe_univ,Set.image_univ,Set.mem_image,
    Set.mem_range]
  constructor
  · rintro ⟨y,⟨i,rfl⟩,rfl⟩
    exact ⟨i,rfl⟩
  · rintro ⟨i,rfl⟩
    exact ⟨v i,⟨i,rfl⟩,rfl⟩
omit [LinearOrder (Y →₀ ℝ)] in
lemma localTriangulation_face {k : ℕ} (v : Fin (k+1) → Y)
    (hv : Function.Injective v) (i : Fin (k+1)) :
    Sparse.restrictComplex (localTriangulation T (Finset.univ.image v))
      {p | chart v p i=0}=
    localTriangulation T (Finset.univ.image (fun j=>v (i.succAbove j))) := by
  apply Geometry.SimplicialComplex.ext
  ext s
  change (s∈T.complex.faces ∧ (s : Set (Y →₀ ℝ))⊆
      convexHull ℝ (simplexVertices (Finset.univ.image v) : Set (Y →₀ ℝ))) ∧
      (s : Set (Y →₀ ℝ))⊆{p | chart v p i=0} ↔ s∈T.complex.faces ∧
      (s : Set (Y →₀ ℝ))⊆convexHull ℝ
        (simplexVertices (Finset.univ.image (fun j=>v (i.succAbove j))) : Set (Y →₀ ℝ))
  rw [simplexVertices_image,simplexVertices_image]
  rw [← parent_face_chart (fun j=>Finsupp.single (v j) (1:ℝ)) (chart v)
    (chart_vertex v hv) i,Set.subset_inter_iff]
  tauto
lemma subdivision_chain_wedge (k : ℕ) (v : Fin (k+1) → Y)
    (hs : Finset.univ.image v∈K.faces) :
    d k (subdivision T (k+1) (wedge (k+1) v))=
      subdivision T k (d k (wedge (k+1) v)) := by
  by_cases hv : Function.Injective v
  swap
  · rw [wedge_eq_zero_of_not_injective _ hv,map_zero,map_zero,map_zero,map_zero]
  cases k with
  | zero =>
    rw [subdivision_wedge_face T 0 v hs]
    have hsp : (localTriangulation T (Finset.univ.image v)).space=
        {Finsupp.single (v 0) (1:ℝ)} := by
      rw [localTriangulation_space T _ hs,simplexVertices_image]
      have he : Set.range (fun i : Fin 1=>Finsupp.single (v i) (1:ℝ))=
          {Finsupp.single (v 0) (1:ℝ)} := by simp
      rw [he,convexHull_singleton]
    rw [augmentation_chain _ _ _ hsp _ (by
      simpa only [Pi.single_eq_same] using congrFun (chart_vertex v hv 0) 0)]
    change wedge 0 (Fin.elim0 : Fin 0 → (Y →₀ ℝ))=
      relabel 0 (fun y : Y=>Finsupp.single y (1:ℝ)) (d 0 (wedge 1 v))
    rw [d_wedge]
    change _=relabel 0 _ (∑i : Fin 1,(-1:ℂ)^i.val •
      wedge 0 (fun j=>v (i.succAbove j)))
    rw [Fin.sum_univ_one]
    simp only [Fin.val_zero,pow_zero,one_smul,relabel_wedge]
    congr 1
    exact Subsingleton.elim _ _
  | succ k =>
    rw [subdivision_wedge_face T (k+1) v hs]
    let w : Fin (k+2) ↪ (Y →₀ ℝ) := ⟨fun i=>Finsupp.single (v i) 1,
      (Finsupp.single_left_injective (by norm_num : (1:ℝ)≠0)).comp hv⟩
    have hw : Set.range w=(simplexVertices (Finset.univ.image v) : Set (Y →₀ ℝ)) :=
      (simplexVertices_image v).symm
    rw [boundary_chain_restrictions _ _ _ w hw (localTriangulation_space T _ hs)
      (chart v) (chart_vertex v hv),d_wedge,map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul]
    congr 1
    have hsub : Finset.univ.image (fun j=>v (i.succAbove j))⊆Finset.univ.image v := by
      intro y hy
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hy
      exact Finset.mem_image.mpr ⟨i.succAbove j,Finset.mem_univ _,rfl⟩
    have hface := (K.isRelLowerSet_faces hs).2 hsub
      (Finset.image_nonempty.mpr Finset.univ_nonempty)
    rw [subdivision_wedge_face T k _ hface]
    congr 2
    exact localTriangulation_face T v hv i
end BassTrace.SubdivisionChains
end
end OAI

end
section
namespace OAI
open Set MeasureTheory
open Finset MeasureTheory intervalIntegral
noncomputable section
namespace BassTrace.BarycentricChains
open scoped BigOperators
open Oriented ChainHomotopy
variable {V W Y Z : Type*} [LinearOrder V] [LinearOrder W] [LinearOrder Y]
lemma labelMap_natural_local (b : Finset V → Y →₀ ℂ) (c : Finset W → Z →₀ ℂ)
    (f : V → W) (g : Y → Z) (s : Finset V)
    (hbc : ∀ t : Finset V,t⊆s → t.Nonempty → c (t.image f)=vertexMap g (b t))
    (n : ℕ) (v : Fin n → V) (hv : ∀i,v i∈s) :
    relabel n g (labelMap b n (wedge n v))=
      labelMap c n (wedge n (f ∘ v)) := by
  induction n with
  | zero =>
    simp only [labelMap_wedge_zero,relabel_wedge]
    congr 1
    exact funext fun i=>Fin.elim0 i
  | succ n ih =>
    rw [labelMap_wedge_recursion,labelMap_wedge_recursion,map_sum]
    have him : Finset.univ.image v⊆s := by
      intro y hy
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hy
      exact hv i
    have hh := hbc _ him (Finset.image_nonempty.mpr Finset.univ_nonempty)
    rw [← Finset.image_image,hh]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul,relabel_cone,ih (fun j=>v (i.succAbove j)) (fun j=>hv (i.succAbove j))]
    rfl
end BassTrace.BarycentricChains
namespace BassTrace.Sparse
open Set Finset MeasureTheory
open scoped BassTrace.Sparse Classical
open Oriented ChainHomotopy Fundamental BarycentricChains SubdivisionChains
variable {H Y X : Type*} [Group H] [MulAction H Y] [LinearOrder Y]
  [LinearOrder (Y →₀ ℝ)] [TopologicalSpace X] [MulAction H X]
variable {K : PreAbstractSimplicialComplex Y} {n : ℕ} {R : ℝ}
variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)
variable (Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
  (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K)
  (GraphGeometry.realizationDistance Γ hΓ K n) R n)
variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)
variable (hn : 0<n) (hR : 0≤R) (y₀ : Y)
def sparseChainFamily (x : X) (k : ℕ) : Degree Y k →ₗ[ℂ] Degree Y k :=
  (labelMap (faceWeight Γ hΓ Q hK hn hR y₀ x) k).comp
    (subdivision ((Q.pair 0).T.val x) k)
lemma sparseChainFamily_zero (x : X) :
    sparseChainFamily Γ hΓ Q hK hn hR y₀ x 0=LinearMap.id := by
  apply linearMap_ext_wedge
  intro v
  change labelMap (faceWeight Γ hΓ Q hK hn hR y₀ x) 0
    (relabel 0 (fun y : Y=>Finsupp.single y (1:ℝ)) (wedge 0 v))=wedge 0 v
  rw [relabel_wedge,labelMap_wedge_zero]
  congr 1
  exact Subsingleton.elim _ _
lemma sparseChainFamily_chain_face (x : X) (k : ℕ) (v : Fin (k+1) → Y)
    (hs : Finset.univ.image v∈K.faces) :
    d k (sparseChainFamily Γ hΓ Q hK hn hR y₀ x (k+1) (wedge (k+1) v))=
      sparseChainFamily Γ hΓ Q hK hn hR y₀ x k (d k (wedge (k+1) v)) := by
  unfold sparseChainFamily
  simp only [LinearMap.comp_apply]
  rw [labelMap_chain _ (fun s _=>by
    simpa only [Chains.augmentation,Finsupp.linearCombination_apply,smul_eq_mul,mul_one]
      using faceWeight_sum Γ hΓ Q hK hn hR y₀ x s),
    subdivision_chain_wedge _ k v hs]
def augmentedComplex (K : PreAbstractSimplicialComplex Y) : ChainHomotopy.Complex Y where
  faces := insert ∅ K.faces
  empty_mem := Set.mem_insert _ _
  down_closed := by
    intro s t hs hts
    by_cases ht : t.Nonempty
    · rcases hs with rfl | hs
      · exact False.elim (ht.ne_empty (Finset.subset_empty.mp hts))
      · exact Set.mem_insert_of_mem _ ((K.isRelLowerSet_faces hs).2 hts ht)
    · exact Set.mem_insert_iff.mpr (Or.inl (Finset.not_nonempty_iff_eq_empty.mp ht))
lemma sparseChainFamily_chain (x : X) (k : ℕ) (c : Degree Y (k+1))
    (hc : c∈(augmentedComplex K).chains (k+1)) :
    d k (sparseChainFamily Γ hΓ Q hK hn hR y₀ x (k+1) c)=
      sparseChainFamily Γ hΓ Q hK hn hR y₀ x k (d k c) := by
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨v,hv,rfl⟩ := hc
    have hv' : Finset.univ.image v∈K.faces := by
      rcases hv with hv | hv
      · exact False.elim ((Finset.image_nonempty.mpr Finset.univ_nonempty).ne_empty hv)
      · exact hv
    exact sparseChainFamily_chain_face Γ hΓ Q hK hn hR y₀ x k v hv'
  | zero => simp
  | add c e _ _ hc he => simp only [map_add,hc,he]
  | smul a c _ hc => simp only [map_smul,hc]
lemma sparseChainFamily_local_face (k : ℕ) (v : Fin (k+1) → Y)
    (hs : Finset.univ.image v∈K.faces) : IsLocallyConstant
      (fun x=>sparseChainFamily Γ hΓ Q hK hn hR y₀ x (k+1) (wedge (k+1) v)) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  filter_upwards [faceWeight_local Γ hΓ Q hK hn hR y₀ _ hs x] with y hy
  unfold sparseChainFamily
  simp only [LinearMap.comp_apply,subdivision_wedge_face _ _ _ hs]
  have he : faces (localTriangulation ((Q.pair 0).T.val y) (Finset.univ.image v))
      (localTriangulation_finite _ _ hs) (k+1)=
    faces (localTriangulation ((Q.pair 0).T.val x) (Finset.univ.image v))
      (localTriangulation_finite _ _ hs) (k+1) := by
    ext s
    simp only [mem_faces]
    exact Set.ext_iff.mp hy.1 s.val
  rw [he]
  simp only [chain,map_sum]
  apply Finset.sum_congr rfl
  intro s hss
  simp only [map_smul,basis_eq_wedge]
  congr 1
  apply labelMap_local _ _ s.val
  · intro t hts ht
    apply hy.2 t
    exact (localTriangulation ((Q.pair 0).T.val x) (Finset.univ.image v)).down_closed
      ((mem_faces _ _ _ s).mp hss) hts ht
  · exact fun i=>OrientedIncidence.vertices_mem s i
lemma sparseChainFamily_local (k : ℕ) (c : Degree Y k) : IsLocallyConstant
    (fun x=>sparseChainFamily Γ hΓ Q hK hn hR y₀ x k c) := by
  have hc : c∈Submodule.span ℂ (Set.range (wedge (Y := Y) k)) := by
    rw [span_wedges]
    trivial
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨v,rfl⟩ := hc
    cases k with
    | zero =>
      have he : (fun x => sparseChainFamily Γ hΓ Q hK hn hR y₀ x 0 (wedge 0 v)) =
          Function.const X (wedge 0 v) := by funext x; rw [sparseChainFamily_zero]; rfl
      rw [he]
      exact IsLocallyConstant.const _
    | succ k =>
      by_cases hs : Finset.univ.image v∈K.faces
      · exact sparseChainFamily_local_face Γ hΓ Q hK hn hR y₀ k v hs
      · have hz : ∀x,sparseChainFamily Γ hΓ Q hK hn hR y₀ x (k+1) (wedge (k+1) v)=0 := by
          intro x
          simp only [sparseChainFamily,LinearMap.comp_apply,subdivision_wedge_succ,
            tupleSubdivision,dite_eq_right hs,map_zero]
        have he : (fun x => sparseChainFamily Γ hΓ Q hK hn hR y₀ x (k+1) (wedge (k+1) v)) =
            Function.const X (0 : Degree Y (k+1)) := funext hz
        rw [he]
        exact IsLocallyConstant.const _
  | zero =>
    have he : (fun x => sparseChainFamily Γ hΓ Q hK hn hR y₀ x k 0) =
        Function.const X (0 : Degree Y k) := funext (fun _ => map_zero _)
    rw [he]
    exact IsLocallyConstant.const _
  | add a b _ _ ha hb => simpa only [map_add] using ha.comp₂ hb (· + ·)
  | smul r a _ ha => simpa only [map_smul,Function.comp_def] using ha.comp (r • ·)
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
open Set MeasureTheory
open Finset MeasureTheory intervalIntegral
noncomputable section
namespace BassTrace.SubdivisionChains
open Set Finset
open scoped BassTrace.Sparse Classical
open Sparse Oriented ChainHomotopy Fundamental OrientedIncidence Sparse.OrbitForms
variable {H Y X : Type*} [Group H] [MulAction H Y] [LinearOrder Y]
  [LinearOrder (Y →₀ ℝ)] [TopologicalSpace X] [MulAction H X]
variable {K : PreAbstractSimplicialComplex Y}
variable (P : MarkedPair (H := H) (X := X)
  (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K))
omit [LinearOrder (Y →₀ ℝ)] in
lemma originalHull_push (h : H) (s : Finset Y) :
    convexHull ℝ (simplexVertices (s.map (MulAction.toPerm h).toEmbedding) : Set (Y →₀ ℝ))=
      push h '' convexHull ℝ (simplexVertices s : Set (Y →₀ ℝ)) := by
  rw [simplexVertices_relabel]
  exact ((push h).toLinearMap.image_convexHull _).symm
omit [LinearOrder (Y →₀ ℝ)] in
lemma localFace_push (h : H) (x : X) (s : Finset Y) (F : Finset (Y →₀ ℝ))
    (hF : F∈(localTriangulation (P.T.val x) s).faces) :
    F.map (push h).toEmbedding∈
      (localTriangulation (P.T.val (h • x)) (s.map (MulAction.toPerm h).toEmbedding)).faces := by
  refine ⟨P.equivariant h x F hF.1,?_⟩
  rw [originalHull_push]
  intro p hp
  obtain ⟨q,hq,rfl⟩ := Finset.mem_map.mp hp
  exact ⟨q,hF.2 hq,rfl⟩
omit [LinearOrder Y] [LinearOrder (Y →₀ ℝ)] in
lemma map_push_inverse (h : H) (F : Finset (Y →₀ ℝ)) :
    (F.map (push h).toEmbedding).map (push h⁻¹).toEmbedding=F := by
  rw [Finset.map_map]
  have he : (push h).toEmbedding.trans (push h⁻¹).toEmbedding=Function.Embedding.refl (Y →₀ ℝ) :=
    Function.Embedding.ext (push_inv_push (Y := Y) h)
  rw [he,Finset.map_refl]
omit [LinearOrder Y] [LinearOrder (Y →₀ ℝ)] in
lemma map_action_inverse (h : H) (s : Finset Y) :
    (s.map (MulAction.toPerm h).toEmbedding).map (MulAction.toPerm h⁻¹).toEmbedding=s := by
  rw [Finset.map_map]
  have he : (MulAction.toPerm h).toEmbedding.trans (MulAction.toPerm h⁻¹).toEmbedding=
      Function.Embedding.refl Y := Function.Embedding.ext (fun y : Y => inv_smul_smul h y)
  rw [he,Finset.map_refl]
omit [LinearOrder (Y →₀ ℝ)] in
lemma local_faces_natural (h : H) (x : X) (s : Finset Y) (hs : s∈K.faces)
    (ht : s.map (MulAction.toPerm h).toEmbedding∈K.faces) (k : ℕ) :
    (faces (localTriangulation (P.T.val x) s) (localTriangulation_finite _ _ hs) k).map
      (simplexMap (push h).toEmbedding k)=
    faces (localTriangulation (P.T.val (h • x)) (s.map (MulAction.toPerm h).toEmbedding))
      (localTriangulation_finite _ _ ht) k := by
  ext F
  rw [Finset.mem_map,mem_faces]
  constructor
  · rintro ⟨E,hE,rfl⟩
    exact localFace_push P h x s E.val ((mem_faces _ _ _ E).mp hE)
  · intro hF
    refine ⟨⟨F.val.map (push h⁻¹).toEmbedding,by simp⟩,?_,?_⟩
    · rw [mem_faces]
      have hh := localFace_push P h⁻¹ (h • x) (s.map (MulAction.toPerm h).toEmbedding)
        F.val hF
      simpa only [map_action_inverse,inv_smul_smul] using hh
    · apply Subtype.ext
      change (F.val.map (push h⁻¹).toEmbedding).map (push h).toEmbedding=F.val
      simpa only [inv_inv] using map_push_inverse (Y := Y) h⁻¹ F.val
lemma subdivision_natural_face (h : H) (x : X) (k : ℕ) (v : Fin (k+1) → Y)
    (hs : Finset.univ.image v∈K.faces)
    (ht : (Finset.univ.image v).map (MulAction.toPerm h).toEmbedding∈K.faces) :
    relabel (k+1) (push h) (subdivision (P.T.val x) (k+1) (wedge (k+1) v))=
      subdivision (P.T.val (h • x)) (k+1) (wedge (k+1) (fun i=>h • v i)) := by
  have himage : Finset.univ.image (fun i=>h • v i)=
      (Finset.univ.image v).map (MulAction.toPerm h).toEmbedding := by
    simp only [Finset.map_eq_image,Finset.image_image,Function.comp_def,
      Equiv.coe_toEmbedding,MulAction.toPerm_apply]
  have htv : Finset.univ.image (fun i=>h • v i)∈K.faces := himage.symm ▸ ht
  rw [subdivision_wedge_face _ _ _ hs,subdivision_wedge_face _ _ _ htv]
  calc
    _ = chain ((faces (localTriangulation (P.T.val x) (Finset.univ.image v))
        (localTriangulation_finite _ _ hs) (k+1)).map (simplexMap (push h).toEmbedding (k+1)))
        (chart (fun i=>h • v i)) := by
      exact chain_relabel _ _ (chart (fun i=>h • v i)) (push h).toEmbedding (by
        intro p
        ext i
        change (push h p) (h • v i) = p (v i)
        rw [push_apply,inv_smul_smul])
    _ = _ := by
      congr 1
      simpa only [himage] using local_faces_natural P h x (Finset.univ.image v) hs ht (k+1)
end BassTrace.SubdivisionChains
namespace BassTrace.Sparse
open Set Finset MeasureTheory
open scoped BassTrace.Sparse Classical
open Oriented ChainHomotopy Fundamental BarycentricChains SubdivisionChains
variable {H Y X : Type*} [Group H] [MulAction H Y] [LinearOrder Y]
  [LinearOrder (Y →₀ ℝ)] [TopologicalSpace X] [MulAction H X]
variable {K : PreAbstractSimplicialComplex Y} {n : ℕ} {R : ℝ}
variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)
variable (Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
  (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K)
  (GraphGeometry.realizationDistance Γ hΓ K n) R n)
variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)
variable (hn : 0<n) (hR : 0≤R) (y₀ : Y)
omit [LinearOrder (Y →₀ ℝ)] [LinearOrder Y] in
lemma vertexMap_perm (h : H) (b : Y →₀ ℂ) :
    vertexMap (fun y=>h • y) b=Finsupp.domLCongr (R := ℂ) (MulAction.toPerm h) b := by
  ext y
  change Finsupp.mapDomain (MulAction.toPerm h) b y = _
  rw [Finsupp.mapDomain_equiv_apply]
  rfl
lemma sparseChainFamily_natural_face (h : H) (x : X) (k : ℕ) (v : Fin (k+1) → Y)
    (hs : Finset.univ.image v∈K.faces)
    (ht : (Finset.univ.image v).map (MulAction.toPerm h).toEmbedding∈K.faces) :
    relabel (k+1) (fun y=>h • y)
        (sparseChainFamily Γ hΓ Q hK hn hR y₀ x (k+1) (wedge (k+1) v))=
      sparseChainFamily Γ hΓ Q hK hn hR y₀ (h • x) (k+1)
        (wedge (k+1) (fun i=>h • v i)) := by
  unfold sparseChainFamily
  simp only [LinearMap.comp_apply]
  rw [←subdivision_natural_face (Q.pair 0) h x k v hs ht,subdivision_wedge_face _ _ _ hs]
  simp only [chain,map_sum]
  apply Finset.sum_congr rfl
  intro F hF
  simp only [map_smul,basis_eq_wedge,relabel_wedge]
  congr 1
  apply labelMap_natural_local _ _ _ _ F.val
  · intro t htF htn
    have htf : t∈((Q.pair 0).T.val x).complex.faces :=
      ((Q.pair 0).T.val x).complex.down_closed
        ((mem_faces _ _ _ F).mp hF).1 htF htn
    rw [vertexMap_perm]
    calc
      _ = faceWeight Γ hΓ Q hK hn hR y₀ (h • x)
          (t.map (OrbitForms.push h).toEmbedding) := by
        apply congrArg (faceWeight Γ hΓ Q hK hn hR y₀ (h • x))
        ext p
        simp only [Finset.mem_image,Finset.mem_map]
        rfl
      _ = _ := faceWeight_nat Γ hΓ Q hK hn hR y₀ h x ⟨t,htf⟩
  · exact fun i=>OrientedIncidence.vertices_mem F i
lemma sparseChainFamily_natural
    (hInv : (augmentedComplex K).IsInvariant (H := H))
    (h : H) (x : X) (k : ℕ) (c : Degree Y k)
    (hc : c∈(augmentedComplex K).chains k) :
    relabel k (fun y=>h • y) (sparseChainFamily Γ hΓ Q hK hn hR y₀ x k c)=
      sparseChainFamily Γ hΓ Q hK hn hR y₀ (h • x) k (relabel k (fun y=>h • y) c) := by
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨v,hv,rfl⟩:=hc
    cases k with
    | zero => rw [sparseChainFamily_zero,sparseChainFamily_zero]; rfl
    | succ k =>
      have hs : Finset.univ.image v∈K.faces := by
        rcases hv with hv | hv
        · exact False.elim ((Finset.image_nonempty.mpr Finset.univ_nonempty).ne_empty hv)
        · exact hv
      rw [relabel_wedge]
      apply sparseChainFamily_natural_face Γ hΓ Q hK hn hR y₀ h x k v hs
      have ht := hInv h (Finset.univ.image v) (Set.mem_insert_of_mem ∅ hs)
      rcases ht with ht | ht
      · exact False.elim ((Finset.image_nonempty.mpr (Finset.image_nonempty.mpr
          Finset.univ_nonempty)).ne_empty ht)
      · convert ht using 1
        ext y
        simp only [Finset.mem_image,Finset.mem_map]
        rfl
  | zero => simp
  | add c d _ _ hc hd => simp only [map_add,hc,hd]
  | smul a c _ hc => simp only [map_smul,hc]
end BassTrace.Sparse
namespace BassTrace.FiniteAverage
open Set Finset MeasureTheory
open scoped Classical
variable {X V W Z : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [OpensMeasurableSpace X]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup Z] [Module ℂ Z]
variable (μ : Measure X) [IsFiniteMeasure μ]
def locallyConstantLinearMap (F : X → V →ₗ[ℂ] W)
    (hF : ∀v,IsLocallyConstant (fun x=>F x v)) : V →ₗ[ℂ] W where
  toFun v := average μ (ofLocallyConstant _ (hF v))
  map_add' a b := by
    have he : ofLocallyConstant (fun x=>F x (a+b)) (hF (a+b)) =
        ofLocallyConstant (fun x=>F x a) (hF a)+ofLocallyConstant (fun x=>F x b) (hF b) := by
      ext x
      exact map_add (F x) a b
    rw [he,average_add]
  map_smul' r v := by
    let L : W →ₗ[ℝ] W := (r • (LinearMap.id : W →ₗ[ℂ] W)).restrictScalars ℝ
    have he : ofLocallyConstant (fun x=>F x (r • v)) (hF (r • v)) =
        (ofLocallyConstant (fun x=>F x v) (hF v)).map L := by
      ext x
      exact map_smul (F x) r v
    rw [he,average_map]
    rfl
lemma locallyConstantLinearMap_post (F : X → V →ₗ[ℂ] W)
    (hF : ∀v,IsLocallyConstant (fun x=>F x v)) (L : W →ₗ[ℂ] Z) (v : V) :
    L (locallyConstantLinearMap μ F hF v)=
      average μ ((ofLocallyConstant (fun x=>F x v) (hF v)).map L) :=
  (average_map μ (L.restrictScalars ℝ) _).symm
lemma locallyConstantLinearMap_const [IsProbabilityMeasure μ] (F : V →ₗ[ℂ] W) (v : V) :
    locallyConstantLinearMap μ (fun _=>F) (fun v=>IsLocallyConstant.const (F v)) v=F v := by
  change average μ (ofLocallyConstant _ _)=F v
  have he : ofLocallyConstant (fun _ : X=>F v) (IsLocallyConstant.const (F v)) =
      SimpleFunc.const X (F v) := by ext; rfl
  rw [he,average_const]
end BassTrace.FiniteAverage
namespace BassTrace.Sparse
open Set Finset MeasureTheory
open scoped BassTrace.Sparse Classical
open Oriented ChainHomotopy Fundamental BarycentricChains SubdivisionChains FiniteAverage
variable {H Y X : Type*} [Group H] [MulAction H Y] [LinearOrder Y]
  [LinearOrder (Y →₀ ℝ)] [TopologicalSpace X] [MulAction H X]
  [CompactSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
variable {K : PreAbstractSimplicialComplex Y} {n : ℕ} {R : ℝ}
variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)
variable (Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
  (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K)
  (GraphGeometry.realizationDistance Γ hΓ K n) R n)
variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)
variable (hn : 0<n) (hR : 0≤R) (y₀ : Y)
variable (μ : Measure X) [IsProbabilityMeasure μ]
def averagedSparseChain (k : ℕ) : Degree Y k →ₗ[ℂ] Degree Y k :=
  locallyConstantLinearMap μ (fun x=>sparseChainFamily Γ hΓ Q hK hn hR y₀ x k)
    (sparseChainFamily_local Γ hΓ Q hK hn hR y₀ k)
lemma averagedSparseChain_zero (c : Degree Y 0) :
    averagedSparseChain Γ hΓ Q hK hn hR y₀ μ 0 c=c := by
  unfold averagedSparseChain
  simp_rw [sparseChainFamily_zero]
  exact locallyConstantLinearMap_const μ LinearMap.id c
lemma averagedSparseChain_chain (k : ℕ) (c : Degree Y (k+1))
    (hc : c∈(augmentedComplex K).chains (k+1)) :
    d k (averagedSparseChain Γ hΓ Q hK hn hR y₀ μ (k+1) c)=
      averagedSparseChain Γ hΓ Q hK hn hR y₀ μ k (d k c) := by
  unfold averagedSparseChain
  rw [locallyConstantLinearMap_post]
  apply congrArg (FiniteAverage.average μ)
  apply SimpleFunc.ext
  intro x
  exact sparseChainFamily_chain Γ hΓ Q hK hn hR y₀ x k c hc
lemma averagedSparseChain_natural
    (hInv : (augmentedComplex K).IsInvariant (H := H))
    (hμ : ∀h : H,MeasurePreserving (fun x : X=>h • x) μ μ)
    (h : H) (k : ℕ) (c : Degree Y k) (hc : c∈(augmentedComplex K).chains k) :
    relabel k (fun y=>h • y) (averagedSparseChain Γ hΓ Q hK hn hR y₀ μ k c)=
      averagedSparseChain Γ hΓ Q hK hn hR y₀ μ k (relabel k (fun y=>h • y) c) := by
  unfold averagedSparseChain
  rw [locallyConstantLinearMap_post]
  let f := ofLocallyConstant
    (fun x=>sparseChainFamily Γ hΓ Q hK hn hR y₀ x k (relabel k (fun y=>h • y) c))
    (sparseChainFamily_local Γ hΓ Q hK hn hR y₀ k _)
  change FiniteAverage.average μ _=FiniteAverage.average μ f
  rw [←average_precomp μ μ (fun x : X=>h • x) (hμ h)
    (MulAction.bijective h).surjective f]
  apply congrArg (FiniteAverage.average μ)
  apply SimpleFunc.ext
  intro x
  exact sparseChainFamily_natural Γ hΓ Q hK hn hR y₀ hInv h x k c hc
end BassTrace.Sparse
end
end OAI

end
section
namespace OAI
open Set MeasureTheory
open Finset MeasureTheory intervalIntegral
noncomputable section
namespace BassTrace.BarycentricChains
section
open Set Finset
open scoped Classical
open Oriented ChainHomotopy OrientedIncidence
variable {V Y : Type*} [LinearOrder V]
lemma cone_square (k : ℕ) (b : Y →₀ ℂ) (c : Degree Y k) :
    cone (k+1) b (cone k b c)=0 := by
  apply Subtype.ext
  change ExteriorAlgebra.ι ℂ b * (ExteriorAlgebra.ι ℂ b * (c : Chains.Algebra Y))=0
  rw [←mul_assoc,ExteriorAlgebra.ι_sq_zero,zero_mul]
lemma vertices_image {k : ℕ} (s : Set.powersetCard V k) :
    Finset.univ.image (vertices s)=s.val := by
  apply Finset.coe_injective
  simpa only [Finset.coe_image,Finset.coe_univ,Set.image_univ] using vertices_range s
lemma labelMap_basis_recursion (b : Finset V → Y →₀ ℂ) (k : ℕ)
    (s : Set.powersetCard V (k+1)) :
    labelMap b (k+1) (basis (k+1) s)=
      cone k (b s.val) (∑i : Fin (k+1),(-1:ℂ)^i.val • labelMap b k (basis k (eraseFace s i))) := by
  rw [basis_eq_wedge,labelMap_wedge_succ,vertices_image,←basis_eq_wedge,
    boundary_basis,map_sum]
  simp only [map_smul]
def filteredLabel (b : Finset V → Y →₀ ℂ) (ℓ : Finset V → ℕ) :
    ∀k,Set.powersetCard V (k+1) → Degree Y (k+1)
  | 0,s => if ℓ s.val=0 then labelMap b 1 (basis 1 s) else 0
  | k+1,s => if ℓ s.val=k+1 then cone (k+1) (b s.val)
      (∑i : Fin (k+2),(-1:ℂ)^i.val • filteredLabel b ℓ k (eraseFace s i)) else 0
def filteredCount (ℓ : Finset V → ℕ) : ∀k,Set.powersetCard V (k+1) → ℕ
  | 0,s => if ℓ s.val=0 then 1 else 0
  | k+1,s => if ℓ s.val=k+1 then ∑i : Fin (k+2),filteredCount ℓ k (eraseFace s i) else 0
lemma labelMap_eq_filtered (b : Finset V → Y →₀ ℂ) (ℓ : Finset V → ℕ)
    (P : Set (Finset V))
    (hP : ∀s∈P,∀t⊆s,t.Nonempty→t∈P)
    (hcard : ∀s∈P,s.card≤ℓ s+1)
    (hmono : ∀s∈P,∀t∈P,t⊆s→ℓ t≤ℓ s)
    (heq : ∀s∈P,∀t∈P,t⊆s→ℓ t=ℓ s→b t=b s)
    (k : ℕ) (s : Set.powersetCard V (k+1)) (hs : s.val∈P) (hℓ : ℓ s.val=k) :
    labelMap b (k+1) (basis (k+1) s)=filteredLabel b ℓ k s := by
  induction k with
  | zero => simp only [filteredLabel,hℓ,ite_true]
  | succ k ih =>
    rw [filteredLabel,ite_eq_left hℓ,labelMap_basis_recursion,map_sum,map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul,map_smul]
    congr 1
    have hsub : (eraseFace s i).val⊆s.val := Finset.erase_subset _ _
    have hE : (eraseFace s i).val∈P := hP s.val hs _ hsub
      (Finset.card_pos.mp (by rw [(eraseFace s i).property]; omega))
    have hlow := hcard _ hE
    rw [(eraseFace s i).property] at hlow
    have hhigh := hmono s.val hs _ hE hsub
    rw [hℓ] at hhigh
    by_cases he : ℓ (eraseFace s i).val=k
    · rw [ih (eraseFace s i) hE he]
    · have he' : ℓ (eraseFace s i).val=k+1 := by omega
      have hb := heq s.val hs _ hE hsub (he'.trans hℓ.symm)
      rw [labelMap_basis_recursion,hb,cone_square]
      cases k <;> simp only [filteredLabel,ite_eq_right he,map_zero]
end
section
open Set Finset
open scoped Classical
open Oriented ChainHomotopy OrientedIncidence
variable {V : Type*} [LinearOrder V]
lemma eraseFace_injective {k : ℕ} (s : Set.powersetCard V (k+1)) :
    Function.Injective (eraseFace s) := by
  intro i j he
  apply (vertices s).injective
  exact (Finset.erase_inj s.val (vertices_mem s i)).mp (congrArg Subtype.val he)
lemma filteredCount_eq_zero (ℓ : Finset V → ℕ) (k : ℕ)
    (s : Set.powersetCard V (k+1)) (hs : ℓ s.val≠k) : filteredCount ℓ k s=0 := by
  cases k <;> simp only [filteredCount,ite_eq_right hs]
lemma filteredCount_pos_level (ℓ : Finset V → ℕ) (k : ℕ)
    (s : Set.powersetCard V (k+1)) (hs : 0<filteredCount ℓ k s) : ℓ s.val=k := by
  by_contra h
  rw [filteredCount_eq_zero ℓ k s h] at hs
  exact Nat.lt_irrefl 0 hs
lemma sum_facets_fiberwise (k : ℕ) (A : Finset (Set.powersetCard V (k+2)))
    (B : Finset (Set.powersetCard V (k+1)))
    (hAB : ∀s∈A,∀i,eraseFace s i∈B) (w : Set.powersetCard V (k+1) → ℕ) :
    ∑s∈A,∑i : Fin (k+2),w (eraseFace s i)=
      ∑t∈B,(incidencePairs A t).card*w t := by
  rw [←Finset.sum_product A Finset.univ (fun p=>w (eraseFace p.1 p.2))]
  symm
  calc
    _ = ∑t∈B,∑p∈incidencePairs A t,w (eraseFace p.1 p.2) := by
      apply Finset.sum_congr rfl
      intro t _
      rw [←Finset.sum_const_nat (s := incidencePairs A t)
        (f := fun p=>w (eraseFace p.1 p.2)) (fun p hp=>congrArg w (Finset.mem_filter.mp hp).2)]
    _ = _ := Finset.sum_fiberwise_of_maps_to
      (fun p hp=>hAB p.1 (Finset.mem_product.mp hp).1 p.2) _
lemma incidencePairs_card_le (k : ℕ) (A : Finset (Set.powersetCard V (k+2)))
    (t : Set.powersetCard V (k+1)) :
    (incidencePairs A t).card≤(A.filter (fun s=>t.val⊆s.val)).card := by
  apply Finset.card_le_card_of_injOn (fun p=>p.1)
  · intro p hp
    obtain ⟨hp,he⟩ := Finset.mem_filter.mp hp
    refine Finset.mem_filter.mpr ⟨(Finset.mem_product.mp hp).1,?_⟩
    rw [←he]
    exact Finset.erase_subset _ _
  · intro p hp q hq he
    apply Prod.ext he
    obtain ⟨_,hp⟩ := Finset.mem_filter.mp hp
    obtain ⟨_,hq⟩ := Finset.mem_filter.mp hq
    apply eraseFace_injective q.1
    simpa only [he] using hp.trans hq.symm
lemma filteredCount_sum_step (ℓ : Finset V → ℕ) (k : ℕ)
    (A : Finset (Set.powersetCard V (k+2))) (B : Finset (Set.powersetCard V (k+1)))
    (hAB : ∀s∈A,∀i,eraseFace s i∈B)
    (hbranch : ∀t∈B,0<filteredCount ℓ k t →
      ((A.filter (fun s=>ℓ s.val=k+1)).filter (fun s=>t.val⊆s.val)).card≤2) :
    ∑s∈A,filteredCount ℓ (k+1) s≤2*∑t∈B,filteredCount ℓ k t := by
  have he : (∑s∈A,filteredCount ℓ (k+1) s)=
      ∑s∈A.filter (fun s=>ℓ s.val=k+1),∑i : Fin (k+2),filteredCount ℓ k (eraseFace s i) := by
    simp only [filteredCount,Finset.sum_filter]
  rw [he,sum_facets_fiberwise k _ B (fun s hs=>hAB s (Finset.mem_filter.mp hs).1),
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t ht
  by_cases hw : 0<filteredCount ℓ k t
  · exact Nat.mul_le_mul_right _ ((incidencePairs_card_le k _ t).trans (hbranch t ht hw))
  · have hz : filteredCount ℓ k t=0 := by omega
    simp only [hz,mul_zero,le_refl]
end
section
open Set Finset
open scoped Classical
open OrientedIncidence Fundamental Sparse
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [LinearOrder V]
variable {K : Geometry.SimplicialComplex ℝ V} {n : ℕ}
namespace ActualFlags
variable (Q : Cuts.PointFiltration K n)
def level (s : Finset V) : ℕ := if hs : s∈(Q.T 0).faces then Q.faceLevel ⟨s,hs⟩ else 0
omit [LinearOrder V] in
lemma level_face (s : Finset V) (hs : s∈(Q.T 0).faces) :
    level Q s=Q.faceLevel ⟨s,hs⟩ := dite_eq_left hs
lemma count_pos_zero (k : ℕ) (s : Set.powersetCard V (k+1))
    (hs : s.val∈(Q.T 0).faces) (hp : 0<filteredCount (level Q) k s) :
    ∃z∈s.val,z∈Q.Z 0 := by
  induction k with
  | zero =>
    obtain ⟨z,hz⟩ := Finset.card_eq_one.mp s.property
    have hl := filteredCount_pos_level (level Q) 0 s hp
    rw [level_face Q s.val hs] at hl
    have hm := Q.mean_mem_faceLevel ⟨s.val,hs⟩
    rw [hl,hz] at hm
    simp only [Cuts.vertexMean,Finset.card_singleton,Nat.cast_one,inv_one,Finset.sum_singleton,one_smul] at hm
    exact ⟨z,hz.symm ▸ Finset.mem_singleton_self z,hm⟩
  | succ k ih =>
    rw [filteredCount] at hp
    split_ifs at hp with hl
    · obtain ⟨i,_,hi⟩ := Finset.sum_pos_iff.mp hp
      have hE : (eraseFace s i).val∈(Q.T 0).faces :=
        (Q.T 0).down_closed hs (Finset.erase_subset _ _)
          (Finset.card_pos.mp (by rw [(eraseFace s i).property]; omega))
      obtain ⟨z,hz,hZ⟩ := ih (eraseFace s i) hE hi
      exact ⟨z,Finset.erase_subset _ _ hz,hZ⟩
    · omega
lemma localFaces_erase (L : Geometry.SimplicialComplex ℝ V) (hL : L.faces.Finite)
    (k : ℕ) (s : Set.powersetCard V (k+2)) (hs : s∈faces L hL (k+2)) (i : Fin (k+2)) :
    eraseFace s i∈faces L hL (k+1) := by
  rw [mem_faces] at hs ⊢
  exact L.down_closed hs (Finset.erase_subset _ _)
    (Finset.card_pos.mp (by rw [(eraseFace s i).property]; omega))
lemma count_sum_step (hK : ∀s∈K.faces,s.card≤n+1)
    (L : Geometry.SimplicialComplex ℝ V) (hL : L.faces.Finite)
    (hLT : L.faces⊆(Q.T 0).faces) (k : ℕ) (hk : k<n) :
    ∑s∈faces L hL (k+2),filteredCount (level Q) (k+1) s≤
      2*∑t∈faces L hL (k+1),filteredCount (level Q) k t := by
  apply filteredCount_sum_step (level Q) k _ _ (localFaces_erase L hL k)
  intro t ht hp
  obtain ⟨z,hzt,hz⟩ := count_pos_zero Q k t (hLT ((mem_faces L hL _ t).mp ht)) hp
  let B := ((faces L hL (k+2)).filter (fun s=>level Q s.val=k+1)).filter (fun s=>t.val⊆s.val)
  have hh : (B.image Subtype.val).card≤2 := by
    apply Q.flagged_cofaces_card_le_two hK hk hz t.property hzt
    intro E hE
    obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hE
    obtain ⟨hs,hsub⟩ := Finset.mem_filter.mp hs
    obtain ⟨hs,hl⟩ := Finset.mem_filter.mp hs
    have hsf := hLT ((mem_faces L hL _ s).mp hs)
    refine ⟨hsf,s.property,?_,hsub⟩
    rw [level_face Q s.val hsf] at hl
    exact (Q.hull_mem_iff_level_le ⟨s.val,hsf⟩ (show k+1≤n by omega)).mpr hl.le
  simpa only [Finset.card_image_of_injective _ Subtype.val_injective] using hh
lemma count_sum_bound (hK : ∀s∈K.faces,s.card≤n+1)
    (L : Geometry.SimplicialComplex ℝ V) (hL : L.faces.Finite)
    (hLT : L.faces⊆(Q.T 0).faces) (k : ℕ) (hk : k≤n) :
    ∑s∈faces L hL (k+1),filteredCount (level Q) k s≤
      2^k * ((faces L hL 1).filter (fun s=>level Q s.val=0)).card := by
  induction k with
  | zero => simp [filteredCount]
  | succ k ih =>
    calc
      _ ≤ 2*∑s∈faces L hL (k+1),filteredCount (level Q) k s :=
        count_sum_step Q hK L hL hLT k (by omega)
      _ ≤ 2*(2^k * _) := Nat.mul_le_mul_left 2 (ih (by omega))
      _ = _ := by rw [pow_succ]; ac_rfl
end ActualFlags
end
section
open Set Finset
open scoped Classical
open Oriented ChainHomotopy OrientedIncidence Sparse
variable {V Y : Type*} [LinearOrder V]
def coneLeft (k : ℕ) (c : Degree Y k) : (Y →₀ ℂ) →ₗ[ℂ] Degree Y (k+1) where
  toFun b:=cone k b c
  map_add' a b:=by ext; simp only [cone_coe,map_add,add_mul,Submodule.coe_add]
  map_smul' r b:=by ext; simp only [cone_coe,map_smul,smul_mul_assoc,Submodule.coe_smul,RingHom.id_apply]
lemma cone_single_wedge (k : ℕ) (y : Y) (v : Fin k → Y) :
    cone k (Finsupp.single y 1) (wedge k v)=wedge (k+1) (Fin.cons y v) := by
  apply Subtype.ext
  simp only [cone_coe,wedge,exteriorPower.ιMulti_apply_coe,ExteriorAlgebra.ιMulti_succ_apply,
    Fin.cons_zero,Matrix.vecTail,Function.comp_def,Fin.cons_succ]
lemma cone_uniform_wedge (k : ℕ) (s : Finset Y) (v : Fin k → Y) :
    cone k (uniformVector s) (wedge k v)=
      ∑y∈s,(s.card : ℂ)⁻¹ • wedge (k+1) (Fin.cons y v) := by
  change coneLeft k (wedge k v) (uniformVector s)=_
  rw [uniformVector,map_sum]
  apply Finset.sum_congr rfl
  intro y _
  have he : Finsupp.single y (s.card : ℂ)⁻¹=(s.card : ℂ)⁻¹ • Finsupp.single y 1 := by simp
  rw [he,map_smul]
  exact congrArg ((s.card : ℂ)⁻¹ • ·) (cone_single_wedge k y v)
lemma norm_uniform_cone_wedge (k : ℕ) (W s : Finset Y) (hs : s.Nonempty) (hsW : s⊆W)
    (ψ : Degree Y (k+1) →ₗ[ℂ] ℂ) (M : ℝ)
    (hM : ∀v : Fin (k+1) → Y,(∀i,v i∈W)→‖ψ (wedge (k+1) v)‖≤M)
    (v : Fin k → Y) (hv : ∀i,v i∈W) :
    ‖ψ (cone k (uniformVector s) (wedge k v))‖≤M := by
  rw [cone_uniform_wedge,map_sum]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑_y∈s,(s.card : ℝ)⁻¹*M := by
      apply Finset.sum_le_sum
      intro y hy
      rw [map_smul,norm_smul,norm_inv,Complex.norm_natCast]
      apply mul_le_mul_of_nonneg_left (hM (Fin.cons y v) ?_) (inv_nonneg.mpr (Nat.cast_nonneg _))
      intro i
      exact Fin.cases (hsW hy) hv i
    _ = M := by
      rw [Finset.sum_const, nsmul_eq_mul, ←mul_assoc, mul_inv_cancel₀,one_mul]
      exact_mod_cast hs.card_pos.ne'
lemma filteredLabel_norm (b : Finset V → Y →₀ ℂ) (ℓ : Finset V → ℕ)
    (P : Set (Finset V)) (hP : ∀s∈P,∀t⊆s,t.Nonempty→t∈P)
    (W : Finset Y)
    (hb : ∀s∈P,∃t : Finset Y,t.Nonempty ∧ t⊆W ∧ b s=uniformVector t)
    (M : ℝ) (_hM0 : 0≤M)
    (k : ℕ) (s : Set.powersetCard V (k+1)) (hs : s.val∈P)
    (ψ : Degree Y (k+1) →ₗ[ℂ] ℂ)
    (hM : ∀v : Fin (k+1) → Y,(∀i,v i∈W)→‖ψ (wedge (k+1) v)‖≤M) :
    ‖ψ (filteredLabel b ℓ k s)‖≤M*(filteredCount ℓ k s : ℝ) := by
  induction k with
  | zero =>
    rw [filteredLabel,filteredCount]
    split_ifs with he
    · obtain ⟨t,ht,htW,hsb⟩:=hb s.val hs
      rw [labelMap_basis_recursion,Fin.sum_univ_one]
      simp only [Fin.val_zero,pow_zero,one_smul]
      rw [basis_eq_wedge,
        labelMap_wedge_zero,hsb,Nat.cast_one,mul_one]
      exact norm_uniform_cone_wedge 0 W t ht htW ψ M hM _ (fun i=>Fin.elim0 i)
    · simp only [map_zero,norm_zero,Nat.cast_zero,mul_zero,le_refl]
  | succ k ih =>
    rw [filteredLabel,filteredCount]
    split_ifs with he
    · obtain ⟨t,ht,htW,hsb⟩:=hb s.val hs
      rw [map_sum,map_sum,Nat.cast_sum,Finset.mul_sum]
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro i _
      rw [map_smul,map_smul,norm_smul,norm_pow,norm_neg,norm_one,one_pow,one_mul]
      apply ih (eraseFace s i)
        (hP s.val hs _ (Finset.erase_subset _ _)
          (Finset.card_pos.mp (by rw [(eraseFace s i).property]; omega)))
        (ψ.comp (cone (k+1) (b s.val)))
      intro v hv
      change ‖ψ (cone (k+1) (b s.val) (wedge (k+1) v))‖≤M
      rw [hsb]
      exact norm_uniform_cone_wedge (k+1) W t ht htW ψ M hM v hv
    · simpa only [map_zero,norm_zero,Nat.cast_zero,mul_zero] using (le_refl (0:ℝ))
end
open Set Finset
open scoped Classical
open Oriented ChainHomotopy OrientedIncidence Sparse Fundamental
variable {V Y : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [LinearOrder V]
variable {K : Geometry.SimplicialComplex ℝ V} {n : ℕ}
lemma norm_sign_complex_le (r : ℝ) : ‖(Real.sign r : ℂ)‖≤1 := by
  rcases Real.sign_apply_eq r with h|h|h <;> simp [h]
lemma labeled_chain_bound (Q : Cuts.PointFiltration K n)
    (hK : ∀s∈K.faces,s.card≤n+1)
    (L : Geometry.SimplicialComplex ℝ V) (hL : L.faces.Finite)
    (hLT : L.faces⊆(Q.T 0).faces)
    (b : Finset V → Y →₀ ℂ)
    (heq : ∀s∈L.faces,∀t∈L.faces,t⊆s→
      ActualFlags.level Q t=ActualFlags.level Q s→b t=b s)
    (W : Finset Y) (hb : ∀s∈L.faces,∃t : Finset Y,t.Nonempty ∧ t⊆W ∧ b s=uniformVector t)
    (p : V → (Fin (n+1) → ℝ))
    (ψ : Degree Y (n+1) →ₗ[ℂ] ℂ) (M : ℝ) (hM0 : 0≤M)
    (hM : ∀v : Fin (n+1) → Y,(∀i,v i∈W)→‖ψ (wedge (n+1) v)‖≤M) :
    ‖ψ (labelMap b (n+1) (chain (faces L hL (n+1)) p))‖≤
      M*(2^n * ((faces L hL 1).filter (fun s=>ActualFlags.level Q s.val=0)).card : ℕ) := by
  have hcard s (hs : s∈L.faces) : s.card≤ActualFlags.level Q s+1 := by
    rw [ActualFlags.level_face Q s (hLT hs)]
    exact Q.final_face_card_le_level hK ⟨s,hLT hs⟩
  have hmono s (hs : s∈L.faces) t (ht : t∈L.faces) (hts : t⊆s) :
      ActualFlags.level Q t≤ActualFlags.level Q s := by
    rw [ActualFlags.level_face Q t (hLT ht),ActualFlags.level_face Q s (hLT hs)]
    exact Q.faceLevel_mono ⟨t,hLT ht⟩ ⟨s,hLT hs⟩ hts
  calc
    _ ≤ ∑s∈faces L hL (n+1),‖ψ ((labelMap b (n+1))
        ((Real.sign (Matrix.det (fun i=>p (vertices s i))) : ℂ) • basis (n+1) s))‖ := by
      rw [chain,map_sum,map_sum]
      exact norm_sum_le _ _
    _ ≤ ∑s∈faces L hL (n+1),M*(filteredCount (ActualFlags.level Q) n s : ℝ) := by
      apply Finset.sum_le_sum
      intro s hs
      have hsf := (mem_faces L hL _ s).mp hs
      have hl : ActualFlags.level Q s.val=n := by
        have hlow := hcard s.val hsf
        rw [s.property] at hlow
        have hhigh := Q.faceLevel_le ⟨s.val,hLT hsf⟩
        rw [←ActualFlags.level_face Q s.val (hLT hsf)] at hhigh
        omega
      rw [map_smul,map_smul,norm_smul]
      apply (mul_le_of_le_one_left (norm_nonneg _) (norm_sign_complex_le _)).trans
      rw [labelMap_eq_filtered b (ActualFlags.level Q) L.faces
        (fun s hs t hts ht=>L.down_closed hs hts ht) hcard hmono heq n s hsf hl]
      exact filteredLabel_norm b (ActualFlags.level Q) L.faces
        (fun s hs t hts ht=>L.down_closed hs hts ht) W hb M hM0 n s hsf ψ hM
    _ = M*((∑s∈faces L hL (n+1),filteredCount (ActualFlags.level Q) n s : ℕ):ℝ) := by
      rw [Nat.cast_sum,Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (by exact_mod_cast ActualFlags.count_sum_bound Q hK L hL hLT n le_rfl) hM0
end BassTrace.BarycentricChains
namespace BassTrace.BarycentricChains.ActualFlags
open Set Finset MeasureTheory
open scoped Classical
open Sparse Fundamental
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {K : Geometry.SimplicialComplex ℝ V} {n : ℕ}
lemma singleton_mean (s : Set.powersetCard V 1) : s.val={Cuts.vertexMean s.val} := by
  obtain ⟨z,hz⟩ := Finset.card_eq_one.mp s.property
  simp only [hz,Cuts.vertexMean,Finset.card_singleton,Nat.cast_one,inv_one,Finset.sum_singleton,one_smul]
lemma zeroFaces_card_le (Q : Cuts.PointFiltration K n)
    (L : Geometry.SimplicialComplex ℝ V) (hL : L.faces.Finite)
    (hLT : L.faces⊆(Q.T 0).faces) (S : Set V) (hLS : L.space⊆S)
    (hfin : (Q.Z 0∩S).Finite) :
    ((faces L hL 1).filter (fun s=>level Q s.val=0)).card≤hfin.toFinset.card := by
  apply Finset.card_le_card_of_injOn (fun s=>Cuts.vertexMean s.val)
  · intro s hs
    obtain ⟨hs,hl⟩ := Finset.mem_filter.mp hs
    have hsf := (mem_faces L hL _ s).mp hs
    change Cuts.vertexMean s.val∈hfin.toFinset
    rw [Set.Finite.mem_toFinset]
    refine ⟨?_,hLS (L.convexHull_subset_space hsf
      (Cuts.vertexMean_mem_convexHull (L.nonempty_of_mem_faces hsf)))⟩
    rw [level_face Q s.val (hLT hsf)] at hl
    exact hl ▸ Q.mean_mem_faceLevel ⟨s.val,hLT hsf⟩
  · intro s _ t _ he
    apply Subtype.ext
    dsimp only at he
    rw [singleton_mean s,singleton_mean t,he]
lemma zeroFaces_real_le_count [MeasurableSpace V] [MeasurableSingletonClass V]
    (Q : Cuts.PointFiltration K n)
    (L : Geometry.SimplicialComplex ℝ V) (hL : L.faces.Finite)
    (hLT : L.faces⊆(Q.T 0).faces) (S : Set V) (hLS : L.space⊆S)
    (hfin : (Q.Z 0∩S).Finite) :
    (((faces L hL 1).filter (fun s=>level Q s.val=0)).card : ℝ)≤
      (Measure.count (Q.Z 0∩S)).toReal := by
  rw [Measure.count_apply_finite _ hfin,ENNReal.toReal_natCast]
  exact_mod_cast zeroFaces_card_le Q L hL hLT S hLS hfin
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
open Set Finset MeasureTheory
open scoped BassTrace.Sparse Classical
open Oriented ChainHomotopy Fundamental BarycentricChains SubdivisionChains
variable {H Y X : Type*} [Group H] [MulAction H Y] [LinearOrder Y]
  [LinearOrder (Y →₀ ℝ)] [TopologicalSpace X] [MulAction H X]
variable {K : PreAbstractSimplicialComplex Y} {n : ℕ} {R : ℝ}
variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)
variable (Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
  (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K)
  (GraphGeometry.realizationDistance Γ hΓ K n) R n)
variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)
variable (hn : 0<n) (hR : 0≤R) (y₀ : Y)
local instance : MeasurableSpace (Y →₀ ℝ) := borel (Y →₀ ℝ)
local instance : BorelSpace (Y →₀ ℝ) := ⟨rfl⟩
lemma sparseChainFamily_bound (x : X) (v : Fin (n+1) → Y)
    (hs : Finset.univ.image v∈K.faces) (hv : Function.Injective v)
    (ψ : Degree Y (n+1) →ₗ[ℂ] ℂ) (M : ℝ) (hM0 : 0≤M)
    (hM : ∀w : Fin (n+1) → Y,(∀i,w i∈GraphGeometry.labelWindow Γ n R (Finset.univ.image v))→
      ‖ψ (wedge (n+1) w)‖≤M) :
    ‖ψ (sparseChainFamily Γ hΓ Q hK hn hR y₀ x (n+1) (wedge (n+1) v))‖≤
      M*(2^n : ℕ)*(Measure.count ((Q.pair 0).P.val x∩
        convexHull ℝ (simplexVertices (Finset.univ.image v) : Set (Y →₀ ℝ)))).toReal := by
  let s := Finset.univ.image v
  let L := localTriangulation ((Q.pair 0).T.val x) s
  have hfin : L.faces.Finite := localTriangulation_finite ((Q.pair 0).T.val x) s hs
  have hLT : L.faces⊆((Q.point x).T 0).faces := fun _ h=>h.1
  have hd : ∀s∈K.faces,s.card≤n+1 := by
    intro s hs
    obtain ⟨t,_,hst,hc,_⟩ := hK s hs
    exact (Finset.card_le_card hst).trans_eq hc
  have hdim : ∀s∈(Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K).faces,s.card≤n+1 := by
    rintro _ ⟨s,hs,rfl⟩
    exact Finset.card_image_le.trans (hd s hs)
  have hLspace := localTriangulation_space ((Q.pair 0).T.val x) s hs
  have hsc : s.card=n+1 := by rw [Finset.card_image_of_injective _ hv,Finset.card_univ,Fintype.card_fin]
  have hzero := zero_inter_simplex_finite Q hd ⟨s,hs,hsc⟩ x
  have hbound := labeled_chain_bound (Q.point x) hdim L hfin hLT
    (faceWeight Γ hΓ Q hK hn hR y₀ x) (fun s hs t ht hts he=>by
      rw [ActualFlags.level_face (Q.point x) t (hLT ht),
        ActualFlags.level_face (Q.point x) s (hLT hs)] at he
      exact faceWeight_nested_equal_level Γ hΓ Q hK hn hR y₀ x
        ⟨t,hLT ht⟩ ⟨s,hLT hs⟩ hts he)
    (GraphGeometry.labelWindow Γ n R s) (fun F hF=>by
      refine ⟨componentVertices Γ hΓ Q hK hn hR x ⟨F,hLT hF⟩,
        componentVertices_nonempty Γ hΓ Q hK hn hR x _,?_,?_⟩
      · intro y hy
        exact componentSupport_subset Γ hΓ Q hK hn hR x ⟨F,hLT hF⟩ s
          ((convexHull_min hF.2 (convex_convexHull ℝ _))
            (Cuts.vertexMean_mem_convexHull (L.nonempty_of_mem_faces hF)))
          ((mem_componentVertices Γ hΓ Q hK hn hR x _ y).mp hy)
      · exact faceWeight_face Γ hΓ Q hK hn hR y₀ x ⟨F,hLT hF⟩)
    (chart v) ψ M hM0 hM
  change ‖ψ (labelMap _ (n+1) (subdivision _ (n+1) (wedge (n+1) v)))‖≤_
  rw [subdivision_wedge_succ,tupleSubdivision,dite_eq_left hs]
  apply hbound.trans
  rw [Nat.cast_mul,←mul_assoc]
  apply mul_le_mul_of_nonneg_left
    (ActualFlags.zeroFaces_real_le_count (Q.point x) L hfin hLT _ hLspace.subset hzero)
    (mul_nonneg hM0 (Nat.cast_nonneg _))
end
open Set Finset MeasureTheory
open scoped BassTrace.Sparse Classical
open Oriented ChainHomotopy Fundamental BarycentricChains SubdivisionChains
variable {H Y X : Type*} [Group H] [MulAction H Y] [LinearOrder Y]
  [LinearOrder (Y →₀ ℝ)] [TopologicalSpace X] [MulAction H X]
  [CompactSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
variable {K : PreAbstractSimplicialComplex Y} {n : ℕ} {R : ℝ}
variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)
variable (Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
  (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K)
  (GraphGeometry.realizationDistance Γ hΓ K n) R n)
variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)
variable (hn : 0<n) (hR : 0≤R) (y₀ : Y)
variable (μ : Measure X) [IsProbabilityMeasure μ]
local instance : MeasurableSpace (Y →₀ ℝ) := borel (Y →₀ ℝ)
local instance : BorelSpace (Y →₀ ℝ) := ⟨rfl⟩
lemma averagedSparseChain_bound (v : Fin (n+1) → Y)
    (hs : Finset.univ.image v∈K.faces) (hv : Function.Injective v)
    (ψ : Degree Y (n+1) →ₗ[ℂ] ℂ) (M : ℝ) (hM0 : 0≤M)
    (hM : ∀w : Fin (n+1) → Y,(∀i,w i∈GraphGeometry.labelWindow Γ n R (Finset.univ.image v))→
      ‖ψ (wedge (n+1) w)‖≤M) :
    ‖ψ (averagedSparseChain Γ hΓ Q hK hn hR y₀ μ (n+1) (wedge (n+1) v))‖≤
      M*(2^n : ℕ)*(∫x,(Measure.count ((Q.pair 0).P.val x∩
        convexHull ℝ (simplexVertices (Finset.univ.image v) : Set (Y →₀ ℝ)))).toReal ∂μ) := by
  unfold averagedSparseChain
  rw [FiniteAverage.locallyConstantLinearMap_post]
  apply (FiniteAverage.norm_average_le_integral_norm μ _).trans
  have hZ : IsLocallyConstant (fun x=>(Measure.count ((Q.pair 0).P.val x∩
      convexHull ℝ (simplexVertices (Finset.univ.image v) : Set (Y →₀ ℝ)))).toReal) :=
    ((Q.pair 0).P.localConstancy_inter (simplexVertices (Finset.univ.image v))
      ⟨_,hs,rfl⟩ _ subset_rfl).comp (fun A=>(Measure.count A).toReal)
  rw [← MeasureTheory.integral_const_mul]
  apply MeasureTheory.integral_mono
  · exact SimpleFunc.integrable_of_isFiniteMeasure _ |>.norm
  · exact (FiniteAverage.ofLocallyConstant _ hZ).integrable_of_isFiniteMeasure.const_mul _
  · intro x
    exact sparseChainFamily_bound Γ hΓ Q hK hn hR y₀ x v hs hv ψ M hM0 hM
end BassTrace.Sparse
namespace BassTrace.BarycentricChains
open Set Finset
open scoped Classical
open Oriented ChainHomotopy
lemma finite_norm_bound {I : Type*} [Finite I] (f : I → ℂ) :
    ∃M : ℝ,0≤M ∧ ∀i,‖f i‖≤M := by
  let _ := Fintype.ofFinite I
  refine ⟨∑i,‖f i‖,Finset.sum_nonneg (fun _ _=>norm_nonneg _),?_⟩
  intro i
  exact Finset.single_le_sum (fun _ _=>norm_nonneg _) (Finset.mem_univ i)
lemma exists_finite_wedge_bound {Y : Type*} (k : ℕ) (W : Finset Y)
    (ψ : Degree Y k →ₗ[ℂ] ℂ) :
    ∃M : ℝ,0≤M ∧ ∀v : Fin k → Y,(∀i,v i∈W)→‖ψ (wedge k v)‖≤M := by
  let f : (Fin k → {y // y∈W}) → ℂ := fun v=>ψ (wedge k (fun i=>(v i).val))
  obtain ⟨M,hM,h⟩ := finite_norm_bound f
  refine ⟨M,hM,?_⟩
  intro v hv
  exact h (fun i=>⟨v i,hv i⟩)
end BassTrace.BarycentricChains
namespace BassTrace.Sparse
open Set Finset MeasureTheory
open scoped BassTrace.Sparse Classical
open Oriented ChainHomotopy Fundamental BarycentricChains SubdivisionChains GraphGeometry
variable {H Y X : Type*} [Group H] [MulAction H Y] [LinearOrder Y]
  [LinearOrder (Y →₀ ℝ)] [TopologicalSpace X] [MulAction H X]
  [CompactSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
variable {K : PreAbstractSimplicialComplex Y} {n : ℕ} {R : ℝ}
variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)
variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)
variable (hn : 0<n) (hR : 0≤R) (y₀ : Y)
variable (μ : Measure X) [IsProbabilityMeasure μ]
local instance : MeasurableSpace (Y →₀ ℝ) := borel (Y →₀ ℝ)
local instance : BorelSpace (Y →₀ ℝ) := ⟨rfl⟩
lemma exists_chain_bound (C : SourceTop K n → ℝ) (hC : ∀σ,0≤C σ)
    (ψ : Degree Y (n+1) →ₗ[ℂ] ℂ) (c : Degree Y (n+1))
    (hc : c∈(augmentedComplex K).chains (n+1)) :
    ∃B : ℝ,0≤B ∧ ∀ε : ℝ,0<ε →
      ∀Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
        (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K)
        (realizationDistance Γ hΓ K n) R n,
      (∀σ : SourceTop K n,(∫x,(Measure.count ((Q.pair 0).P.val x∩
        convexHull ℝ (simplexVertices σ.val : Set (Y →₀ ℝ)))).toReal ∂μ)≤C σ*ε) →
      ‖ψ (averagedSparseChain Γ hΓ Q hK hn hR y₀ μ (n+1) c)‖≤B*ε := by
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨v,hv,rfl⟩ := hc
    by_cases hinj : Function.Injective v
    · have hs : Finset.univ.image v∈K.faces := by
        rcases hv with hv|hv
        · exact False.elim ((Finset.image_nonempty.mpr Finset.univ_nonempty).ne_empty hv)
        · exact hv
      have hsc : (Finset.univ.image v).card=n+1 := by
        rw [Finset.card_image_of_injective _ hinj,Finset.card_univ,Fintype.card_fin]
      let σ : SourceTop K n := ⟨Finset.univ.image v,hs,hsc⟩
      obtain ⟨M,hM0,hM⟩ := exists_finite_wedge_bound (n+1) (labelWindow Γ n R σ.val) ψ
      refine ⟨M*(2^n : ℕ)*C σ,mul_nonneg (mul_nonneg hM0 (Nat.cast_nonneg _)) (hC σ),?_⟩
      intro ε _ Q hQ
      apply (averagedSparseChain_bound Γ hΓ Q hK hn hR y₀ μ v hs hinj ψ M hM0 hM).trans
      calc
        _ ≤ M*(2^n : ℕ)*(C σ*ε) := mul_le_mul_of_nonneg_left (hQ σ)
          (mul_nonneg hM0 (Nat.cast_nonneg _))
        _ = _ := by ring
    · refine ⟨0,le_rfl,?_⟩
      intro ε _ Q _
      rw [wedge_eq_zero_of_not_injective _ hinj,map_zero,map_zero,norm_zero,zero_mul]
  | zero =>
    refine ⟨0,le_rfl,?_⟩
    intro ε _ Q _
    simp only [map_zero,norm_zero,zero_mul,le_refl]
  | add a b _ _ ha hb =>
    obtain ⟨A,hA,hA'⟩ := ha
    obtain ⟨B,hB,hB'⟩ := hb
    refine ⟨A+B,add_nonneg hA hB,?_⟩
    intro ε hε Q hQ
    rw [map_add,map_add,add_mul]
    exact (norm_add_le _ _).trans (add_le_add (hA' ε hε Q hQ) (hB' ε hε Q hQ))
  | smul r a _ ha =>
    obtain ⟨A,hA,hA'⟩ := ha
    refine ⟨‖r‖*A,mul_nonneg (norm_nonneg _) hA,?_⟩
    intro ε hε Q hQ
    rw [map_smul,map_smul,norm_smul,mul_assoc]
    exact mul_le_mul_of_nonneg_left (hA' ε hε Q hQ) (norm_nonneg _)
end BassTrace.Sparse
namespace BassTrace.Sparse.GraphGeometry
section
open Set Finset MeasureTheory
open scoped BassTrace.Sparse Classical ENNReal
open Oriented ChainHomotopy
variable {H Y X : Type*} [Group H] [MulAction H Y] [LinearOrder Y]
  [LinearOrder (Y →₀ ℝ)] [Countable Y] [Countable H] [IsCancelSMul H Y]
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
omit [LinearOrder (Y →₀ ℝ)] [Countable Y] [Countable H] [IsCancelSMul H Y] in
lemma augmentedComplex_invariant : (augmentedComplex K).IsInvariant (H := H) := by
  intro h s hs
  rcases hs with rfl|hs
  · exact Set.mem_insert_iff.mpr (Or.inl (by simp))
  · apply Set.mem_insert_of_mem
    have hh := hact.out h s hs
    rw [Finset.map_eq_image] at hh
    exact hh
end
end BassTrace.Sparse.GraphGeometry
end
end OAI

end
section
open Set Finset MeasureTheory OAI OAI.BassTrace OAI.BassTrace.Sparse OAI.BassTrace.Sparse.GraphGeometry
open scoped Classical Pointwise BassTrace.Sparse
namespace FT
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
end FT
end
section
namespace FT
end FT
end
section
namespace Width
end Width
end
section
namespace OAI
noncomputable section
namespace BassTrace.PathChains
end BassTrace.PathChains
namespace BassTrace
end BassTrace
end
end OAI

end
section
open Set Finset MeasureTheory OAI OAI.BassTrace
open OAI.BassTrace.Oriented OAI.BassTrace.ChainHomotopy OAI.BassTrace.Sparse
open OAI.BassTrace.Sparse.GraphGeometry
open scoped Pointwise Classical BassTrace.Sparse
namespace XCut
set_option maxHeartbeats 2000000 in
theorem consumer : Hb := by
  intro H Y _ _ _ _ _ _ y G _ hG ha D n hD hdeg hlarge T hT witness
  intro E w S a d' hd c ψ δ hδ
  have he : d'=d := by
    funext k
    apply linearMap_ext_wedge
    intro v
    exact (hd k v).trans (d_wedge k v).symm
  subst d'
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
  let μ := FreeParameter.probability H
  have hS (k : ℕ) : S k = (augmentedComplex K).chains k := by
    dsimp [S,Complex.chains,augmentedComplex,K,generatedComplex,w,wedge]
    congr!
  let cc : (augmentedComplex K).chains (n+1) := ⟨c.val,(hS _ ▸ c.property : c.val∈(augmentedComplex K).chains (n+1))⟩
  change Degree Y (n+1) →ₗ[ℂ] ℂ at ψ
  have hK := generatedComplex_pure T n G ha hT
  have hn : 0<n := lt_of_lt_of_le (by positivity) hlarge
  let R : ℝ := 4*(D:ℝ)^2
  have hR : 0≤R := by dsimp [R]; positivity
  let X := FreeParameter.Space H
  letI : MeasurableSpace (Y→₀ℝ) := borel _
  letI : BorelSpace (Y→₀ℝ) := ⟨rfl⟩
  let K' := Geometry.SimplicialComplex.onFinsupp (𝕜:=ℝ) K
  let X' := Profinite.of X
  have hμ : MeasurePreserving (fun x : X => (1:H) • x) μ μ := FreeParameter.probability_preserving H 1
  have wx := witness X'
  have eb : borel X' = (inferInstance : MeasurableSpace X) := BorelSpace.measurable_eq.symm
  dsimp only at wx
  rw [eb] at wx
  obtain ⟨C',hz⟩ := wx (⟨μ,inferInstance⟩ : ProbabilityMeasure X) (FreeParameter.probability_preserving H) K' (by rw [onFinsupp_faces]; dsimp [K,generatedComplex]; congr!)
  let C := fun s : SourceTop K n => max (C' (simplexVertices s.val)) 0
  have hC : ∀s,0≤C s := fun _ => le_max_right _ _
  have hzero (ε:ℝ) (hε:0<ε) : ∃ Q : OrbitForms.SeparatingFiltration (H:=H) (X:=X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜:=ℝ) K) (realizationDistance G hG K n) R n,
      ∀ σ : SourceTop K n,(∫ x,(Measure.count ((Q.pair 0).P.val x ∩ convexHull ℝ (simplexVertices σ.val : Set (Y →₀ ℝ)))).toReal ∂μ)≤C σ*ε := by
    apply (FT.raw_iff (count:=fun P=>∀ σ : SourceTop K n,(∫ x,(Measure.count (P x∩convexHull ℝ (simplexVertices σ.val : Set (Y →₀ ℝ)))).toReal ∂μ)≤C σ*ε)).mp
    obtain ⟨Z,P,h0,hm,hl,heq,hN,hs⟩ := hz ε hε
    let V := Y →₀ ℝ
    let cv (s : Finset V) := convexHull ℝ (s : Set V)
    have space (i) (hi:i≤n) (x:X) : (Z i x).space = K'.space := by
      rcases hi.eq_or_lt with e|lt
      · rw [e,(hN x).1]
      · exact (hs i lt x).1
    have sub (i) (hi:i<n) (x:X) : Cuts.Refines (Z i x) (Z (i+1) x) := by
      have h := (hs i hi x).2.1
      have e := (space i hi.le x).trans (space (i+1) hi x).symm
      exact ⟨⟨_,e,XCut.carrier _ _ e (fun t ht => (h t ht).1),fun t ht => (h t ht).1,fun t ht => (h t ht).2⟩,rfl⟩
    have subK (i) (hi:i≤n) (x:X) : Cuts.Refines (Z i x) K' := by
      induction hi using Nat.decreasingInduction with
      | self => rw [(hN x).1]; exact Cuts.refines_self _
      | of_succ i hi ih => exact (sub i hi x).trans ih
    let k := fun i => min i n
    refine ⟨fun i => Z (k i),fun i => P (k i),?_,?_,fun i => hm (k i),?_,?_,?_,?_,?_⟩
    · intro s
      have hb := h0 (simplexVertices s.val) (show simplexVertices s.val ∈ K'.faces from ⟨_,s.property.1,rfl⟩) (by simpa [simplexVertices,Finset.card_image_of_injective _ (Finsupp.single_left_injective (one_ne_zero : (1:ℝ)≠0))] using s.property.2)
      apply le_trans _ (mul_le_mul_of_nonneg_right (le_max_left _ _) hε.le)
      refine le_trans (le_of_eq ?_) hb
      apply integral_congr_ae; filter_upwards with x
      exact (ncardReal _).symm
    · intro i x
      obtain ⟨S,hS⟩ := subK (k i) (min_le_right ..) x
      dsimp only
      rw [←hS]
      exact ⟨S.space_eq,S.carrier,fun t ht => ⟨S.respects t ht,S.finite t ht⟩⟩
    · intro i t ht
      have loc := hl (k i) t ht
      refine ⟨loc.comp Prod.fst,?_⟩
      convert loc.comp (fun p : Set (Finset V) × Set V => {s∈p.1 | cv s⊆p.2}) using 1
      funext x; ext s
      change ((s∈_ ∧ cv s⊆_) ∧ (s : Set V)⊆cv t) ↔ (s∈_ ∧ (s : Set V)⊆cv t) ∧ cv s⊆_ ∩ cv t
      constructor
      · rintro ⟨⟨a,b⟩,c⟩; exact ⟨⟨a,c⟩,subset_inter b (convexHull_min c (convex_convexHull ℝ _))⟩
      · rintro ⟨⟨a,b⟩,c⟩; exact ⟨⟨a,c.trans inter_subset_left⟩,b⟩
    · intro i h x s hs'
      have hh := (heq (k i) h x).1 (mem_image_of_mem _ hs')
      convert hh using 1
      have eqv (v : V) : (Finsupp.domLCongr (R:=ℝ) (MulAction.toPerm h : Y ≃ Y)) v = Finsupp.mapDomain (h • ·) v := by
        ext w; exact (Finsupp.mapDomain_equiv_apply (f:=MulAction.toPerm h) _ _).symm
      ext z; simp only [Finset.mem_map,Finset.mem_image]; change (∃ v∈s, Finsupp.domLCongr (R:=ℝ) (MulAction.toPerm h : Y ≃ Y) v=z) ↔ _; simp only [eqv]
    · intro i h x v hv
      have hh := (heq (k i) h x).2 (mem_image_of_mem _ hv)
      convert hh using 1; ext z; exact (Finsupp.mapDomain_equiv_apply (f:=MulAction.toPerm h) _ _).symm
    · simpa [k] using hN
    · intro i hi x
      simp only [k,min_eq_left hi.le,min_eq_left (Nat.succ_le_of_lt hi)]
      obtain ⟨S,hS⟩ := sub i hi x
      obtain ⟨_,_,hnest,hcard,hdiam⟩ := hs i hi x
      refine ⟨?_,hnest,hcard,?_⟩
      · rw [←hS]; exact ⟨S.space_eq,S.carrier,fun t ht => ⟨S.respects t ht,S.finite t ht⟩⟩
      intro U hc hU p hp q hq
      have sp {v} (hv:v∈U) : v∈K'.space := by
        obtain ⟨t,ht',hv',_⟩ := hm _ x v (hU hv).1
        exact space _ hi x ▸ (Z _ x).convexHull_subset_space ht' hv'
      rw [←FT.dual_eq G hG K n (sp hp) (sp hq)]
      apply (div_le_iff₀ (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn))).mpr
      have h := hdiam U hU (by apply hc.image; apply Continuous.continuousOn; convert (continuous_induced_dom (f:=Finsupp.linearCombination ℝ (fun y:Y => lp.single 2 y (1:ℝ)))) using 1 <;> congr!
                               change TopologicalSpace.induced _ _ = TopologicalSpace.induced _ _
                               congr!
                               change (letI := Classical.decEq Y; Finsupp.linearCombination ℝ (fun y:Y => lp.single 2 y (1:ℝ))) = _
                               congr!) p hp q hq
      rw [lipschitzDual] at h
      convert h using 1 <;> first | ring | congr!
  obtain ⟨B,hB,hbound⟩ := exists_chain_bound (H := H) G hG hK hn hR y μ C hC ψ cc.val cc.property
  let ε : ℝ := δ/(B+1)
  have hε : 0<ε := div_pos hδ (by positivity)
  obtain ⟨Q,hQ⟩ := hzero ε hε
  refine ⟨averagedSparseChain G hG Q hK hn hR y μ,averagedSparseChain_zero G hG Q hK hn hR y μ,
    fun k x hx => averagedSparseChain_chain G hG Q hK hn hR y μ k x (hS _ ▸ hx),
    fun k h x hx => averagedSparseChain_natural G hG Q hK hn hR y μ augmentedComplex_invariant
      (FreeParameter.probability_preserving H) h k x (hS _ ▸ hx), (hbound ε hε Q hQ).trans_lt ?_⟩
  have : ε*(B+1)=δ := div_mul_cancel₀ _ (by positivity)
  linarith
end XCut
end

theorem OMA.solution : OMA.R_mo_178849_R1.H3 := XCut.consumer

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
