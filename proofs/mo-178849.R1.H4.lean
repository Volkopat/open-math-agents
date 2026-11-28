import OMAReductions.R_mo_178849_R1
/- Adapted from the OpenAI proof in openai/math@3344da59991ed94f9ba711217b29c1d760badfa6. -/
section
-- OAI.Compat
theorem ite_eq_left {c : Prop} {h : Decidable c} (hc : c) {α : Sort*} {t e : α} : (ite c t e) = t := if_pos hc
theorem ite_eq_right {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort*} {t e : α} : (ite c t e) = e := if_neg hc
theorem dite_eq_left {c : Prop} {h : Decidable c} (hc : c) {α : Sort*} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := dif_pos hc
theorem dite_eq_right {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort*} {t : c → α} {e : ¬c → α} : (dite c t e) = e hc := dif_neg hc
theorem Finsupp.mapDomain_apply_of_injective {α β M : Type*} [AddCommMonoid M] {f : α → β} (hf : f.Injective) (x : α →₀ M) (a : α) : Finsupp.mapDomain f x (f a) = x a := Finsupp.mapDomain_apply hf x a
theorem Measurable.of_eval {α δ : Type*} {X : δ → Type*} [MeasurableSpace α] [∀ a, MeasurableSpace (X a)] {f : α → ∀ a, X a} (hf : ∀ a, Measurable fun c => f c a) : Measurable f := measurable_pi_lambda f hf
def Set.equivOfEq {α : Type*} {s t : Set α} (h : s = t) : s ≃ t := Equiv.setCongr h
theorem AffineBasis.setFinite {ι k V P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V] [AddTorsor V P] [FiniteDimensional k V] {s : Set ι} (b : AffineBasis s k P) : s.Finite := b.finite_set
theorem Isometry.lipschitzWith {α β : Type*} [PseudoEMetricSpace α] [PseudoEMetricSpace β] {f : α → β} (h : Isometry f) : LipschitzWith 1 f := h.lipschitz
@[simp] theorem SimpleGraph.ncard_neighborSet {V : Type*} (G : SimpleGraph V) (v : V) [Fintype (G.neighborSet v)] : (G.neighborSet v).ncard = G.degree v := by
  simp [← Set.fintypeCard_eq_ncard, SimpleGraph.card_neighborSet_eq_degree]
end

section
-- OAI.RingTheory.BassTrace.TraceCoefficients
namespace OAI
namespace BassTrace
open scoped Classical
noncomputable def classCoefficient {G : Type*} [Group G]
    (g : G) (a : MonoidAlgebra ℂ G) : ℂ := by
  classical
  exact a.coeff.sum fun h z => if IsConj h g then z else 0
noncomputable def idempotentTraceCoefficient {G : Type*} [Group G]
    {q : ℕ} (e : Matrix (Fin q) (Fin q) (MonoidAlgebra ℂ G)) (g : G) : ℂ :=
  classCoefficient g (Matrix.trace e)
variable {G : Type*} [Group G]
@[simp] theorem classCoefficient_zero (g : G) :
    classCoefficient g 0 = 0 := by
  simp [classCoefficient]
@[simp] theorem classCoefficient_single (g h : G) (z : ℂ) :
    classCoefficient g (MonoidAlgebra.single h z) = if IsConj h g then z else 0 := by
  classical
  simp [classCoefficient, Finsupp.sum_single_index]
@[simp] theorem classCoefficient_add (g : G) (a b : MonoidAlgebra ℂ G) :
    classCoefficient g (a + b) = classCoefficient g a + classCoefficient g b := by
  classical
  apply Finsupp.sum_add_index
  · intro h _
    simp
  · intro h _ z w
    split_ifs <;> simp
@[simp] theorem classCoefficient_smul (g : G) (z : ℂ) (a : MonoidAlgebra ℂ G) :
    classCoefficient g (z • a) = z * classCoefficient g a := by
  classical
  unfold classCoefficient
  rw [MonoidAlgebra.coeff_smul, Finsupp.sum_smul_index (fun _ => by simp)]
  rw [Finsupp.sum, Finsupp.sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  split_ifs <;> simp
@[simp] theorem classCoefficient_sum {ι : Type*} (g : G) (s : Finset ι)
    (f : ι → MonoidAlgebra ℂ G) :
    classCoefficient g (∑ i ∈ s, f i) = ∑ i ∈ s, classCoefficient g (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, ih]
theorem classCoefficient_mul_comm (g : G) (a b : MonoidAlgebra ℂ G) :
    classCoefficient g (a * b) = classCoefficient g (b * a) := by
  induction a using MonoidAlgebra.induction_on with
  | of h =>
      induction b using MonoidAlgebra.induction_on with
      | of k =>
          have hconj : IsConj (h * k) (k * h) := by
            apply isConj_iff.mpr
            exact ⟨k, by simp [mul_assoc]⟩
          have hiff : IsConj (h * k) g ↔ IsConj (k * h) g :=
            ⟨hconj.symm.trans, hconj.trans⟩
          change classCoefficient g (MonoidAlgebra.single h 1 * MonoidAlgebra.single k 1) =
            classCoefficient g (MonoidAlgebra.single k 1 * MonoidAlgebra.single h 1)
          simp only [MonoidAlgebra.single_mul_single, classCoefficient_single, hiff]
      | add b c hb hc => simp only [mul_add, add_mul, classCoefficient_add, hb, hc]
      | smul z b hb => simp only [mul_smul_comm, smul_mul_assoc, classCoefficient_smul, hb]
  | add a c ha hc => simp only [add_mul, mul_add, classCoefficient_add, ha, hc]
  | smul z a ha => simp only [mul_smul_comm, smul_mul_assoc, classCoefficient_smul, ha]
theorem classCoefficient_matrix_mul_comm {ι κ : Type*} [Fintype ι] [Fintype κ]
    (g : G) (a : Matrix ι κ (MonoidAlgebra ℂ G))
    (b : Matrix κ ι (MonoidAlgebra ℂ G)) :
    classCoefficient g (Matrix.trace (a * b)) =
      classCoefficient g (Matrix.trace (b * a)) := by
  classical
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, classCoefficient_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact classCoefficient_mul_comm g _ _
end BassTrace
end OAI

end

section
-- OAI.RingTheory.BassTrace.ExteriorChains
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
lemma contraction_map (α : M →ₗ[R] R) (β : N →ₗ[R] R) (f : M →ₗ[R] N)
    (hf : ∀ v, β (f v) = α v) (x : ExteriorAlgebra R M) :
    contraction β (ExteriorAlgebra.map f x) =
      ExteriorAlgebra.map f (contraction α x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp [contraction, AlgHom.commutes]
  | add x y hx hy => simp only [map_add, hx, hy]
  | ι_mul x v hx =>
    change contraction β (ExteriorAlgebra.map f (ExteriorAlgebra.ι R v * x)) = _
    rw [map_mul, ExteriorAlgebra.map_apply_ι, contraction_ι_mul, contraction_ι_mul,
      hf, hx, map_sub, map_smul, map_mul, ExteriorAlgebra.map_apply_ι]
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
abbrev Degree (n : ℕ) := ⋀[ℂ]^n (Vectors Y)
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
lemma average_augmentation {n : ℕ} (hn : n ≠ 0) (v : Fin n → Y) :
    Chains.augmentation Y (average n v) = 1 := by
  simp [average, Nat.cast_ne_zero.mpr hn]
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
-- OAI.RingTheory.BassTrace.ChainMaps
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
variable {V W : Type*} [LinearOrder V] [LinearOrder W]
end Fundamental
namespace Sparse
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
end Sparse
namespace Fundamental
open scoped BigOperators Classical
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [LinearOrder E]
end Fundamental
namespace Oriented
open scoped BigOperators
variable {Y A : Type*} [AddCommGroup A] [Module ℂ A]
variable [LinearOrder Y]
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
lemma Complex.wedge_mem (K : Complex Y) {n : ℕ} (v : Fin n → Y)
    (hv : Finset.univ.image v ∈ K.faces) : wedge n v ∈ K.chains n :=
  Submodule.subset_span ⟨v, hv, rfl⟩
lemma Complex.d_mem (K : Complex Y) (n : ℕ) {x : Degree Y (n+1)}
    (hx : x ∈ K.chains (n+1)) : d n x ∈ K.chains n := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, hv, rfl⟩ := hx
    rw [d_wedge]
    apply Submodule.sum_mem
    intro i _
    apply Submodule.smul_mem
    apply K.wedge_mem
    apply K.down_closed hv
    intro y hy
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
  | smul a x _ hx => simpa only [map_smul] using Submodule.smul_mem _ a hx
lemma Complex.coneLift_fills (K : Complex Y) {n : ℕ} (hn : n ≠ 0)
    (r : Degree Y n →ₗ[ℂ] Degree Y n)
    (hr : ∀ x ∈ K.chains n, Chains.boundary Y (r x : Chains.Algebra Y) = 0)
    {x : Degree Y n} (hx : x ∈ K.chains n) : d n (coneLift r x) = r x := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, hv, rfl⟩ := hx
    rw [coneLift_wedge]
    exact d_cone_cycle n _ (average_augmentation hn v) _ (hr _ (K.wedge_mem v hv))
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul a x _ hx => simp only [map_smul, hx]
def homotopy (F : ∀ n, Degree Y n →ₗ[ℂ] Degree Y n) :
    ∀ n, Degree Y n →ₗ[ℂ] Degree Y (n+1)
  | 0 => 0
  | n+1 => coneLift (F (n+1) - LinearMap.id - (homotopy F n).comp (d n))
lemma homotopy_equation (K : Complex Y)
    (F : ∀ n, Degree Y n →ₗ[ℂ] Degree Y n)
    (hF0 : F 0 = LinearMap.id)
    (hF : ∀ n x, x ∈ K.chains (n+1) → d n (F (n+1) x) = F n (d n x))
    (n : ℕ) {x : Degree Y (n+1)} (hx : x ∈ K.chains (n+1)) :
    d (n+1) (homotopy F (n+1) x) = F (n+1) x - x - homotopy F n (d n x) := by
  induction n with
  | zero =>
    apply K.coneLift_fills (by omega) _ ?_ hx
    intro y hy
    simp only [homotopy, LinearMap.zero_comp, LinearMap.sub_apply,
      LinearMap.id_apply, LinearMap.zero_apply, sub_zero]
    change Chains.boundary Y (F 1 y - y : Degree Y 1) = 0
    have he := hF 0 y hy
    rw [hF0] at he
    have hz : d 0 (F 1 y - y) = 0 := by simp only [map_sub, he, LinearMap.id_apply, sub_self]
    exact congrArg Subtype.val hz
  | succ n ih =>
    apply K.coneLift_fills (by omega) _ ?_ hx
    intro y hy
    have he := hF (n+1) y hy
    have hp := ih (K.d_mem (n+1) hy)
    have hz : d (n+1) (F (n+2) y - y - homotopy F (n+1) (d (n+1) y)) = 0 := by
      rw [map_sub, map_sub, he, hp, d_square, map_zero, sub_zero, sub_self]
    exact congrArg Subtype.val hz
end
section
open scoped BigOperators
open Oriented
variable {Y Z W : Type*}
lemma vertexMap_average (n : ℕ) (f : Y → Z) (v : Fin n → Y) :
    vertexMap f (average n v) = average n (f ∘ v) := by
  simp only [average, map_smul, map_sum, vertexMap_single, Function.comp_apply]
lemma augmentation_vertexMap (f : Y → Z) (x : Y →₀ ℂ) :
    Chains.augmentation Z (vertexMap f x) = Chains.augmentation Y x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single y c => simp
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
lemma d_relabel (n : ℕ) (f : Y → Z) (x : Degree Y (n+1)) :
    d n (relabel (n+1) f x) = relabel n f (d n x) := by
  apply Subtype.ext
  simp only [d_coe, relabel_coe]
  exact Chains.contraction_map (Chains.augmentation Y) (Chains.augmentation Z)
    (vertexMap f) (augmentation_vertexMap f) x
@[simp] lemma relabel_id (n : ℕ) : relabel n (id : Y → Y) = LinearMap.id := by
  apply linearMap_ext_wedge
  intro v
  simp only [relabel_wedge, Function.id_comp, LinearMap.id_apply]
lemma coneLift_natural [LinearOrder Z] {n : ℕ}
    (r : Degree Y n →ₗ[ℂ] Degree Y n) (s : Degree Z n →ₗ[ℂ] Degree Z n)
    (f : Y → Z) (hf : ∀ x, relabel n f (r x) = s (relabel n f x)) (x : Degree Y n) :
    relabel (n+1) f (coneLift r x) = coneLift s (relabel n f x) := by
  have he : (relabel (n+1) f).comp (coneLift r) = (coneLift s).comp (relabel n f) := by
    apply linearMap_ext_wedge
    intro v
    simp only [LinearMap.comp_apply, coneLift_wedge, relabel_wedge,
      relabel_cone, vertexMap_average, hf]
  exact LinearMap.congr_fun he x
lemma homotopy_natural [LinearOrder Z]
    (F : ∀ n, Degree Y n →ₗ[ℂ] Degree Y n)
    (G : ∀ n, Degree Z n →ₗ[ℂ] Degree Z n) (f : Y → Z)
    (hf : ∀ n x, relabel n f (F n x) = G n (relabel n f x))
    (n : ℕ) (x : Degree Y n) :
    relabel (n+1) f (homotopy F n x) = homotopy G n (relabel n f x) := by
  induction n with
  | zero => simp only [homotopy, LinearMap.zero_apply, map_zero]
  | succ n ih =>
    apply coneLift_natural _ _ f ?_ x
    intro y
    simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
      map_sub, hf, ih, d_relabel]
end
open scoped BigOperators
open Oriented
variable {Y H : Type*} [LinearOrder Y] [Monoid H] [MulAction H Y]
def Complex.IsInvariant (K : Complex Y) : Prop :=
  ∀ h : H, ∀ s ∈ K.faces, s.image (fun y => h • y) ∈ K.faces
lemma Complex.relabel_mem (K : Complex Y) (hK : K.IsInvariant (H := H))
    (n : ℕ) (h : H) {x : Degree Y n} (hx : x ∈ K.chains n) :
    relabel n (fun y => h • y) x ∈ K.chains n := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, hv, rfl⟩ := hx
    rw [relabel_wedge]
    apply K.wedge_mem
    simpa only [Finset.image_image] using hK h (Finset.univ.image v) hv
  | zero => simp
  | add x y _ _ hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
  | smul a x _ hx => simpa only [map_smul] using Submodule.smul_mem _ a hx
def Complex.relations (K : Complex Y) (hK : K.IsInvariant (H := H)) (n : ℕ) :
    Submodule ℂ (K.chains n) :=
  Submodule.span ℂ (Set.range fun p : H × K.chains n =>
    (⟨relabel n (fun y => p.1 • y) p.2, K.relabel_mem hK n p.1 p.2.property⟩ : K.chains n) - p.2)
lemma coinvariant_cocycle_comparison (K : Complex Y) (hK : K.IsInvariant (H := H))
    (F : ∀ n, Degree Y n →ₗ[ℂ] Degree Y n)
    (hF0 : F 0 = LinearMap.id)
    (hF : ∀ n x, x ∈ K.chains (n+1) → d n (F (n+1) x) = F n (d n x))
    (hFeq : ∀ n (h : H) x,
      relabel n (fun y => h • y) (F n x) = F n (relabel n (fun y => h • y) x))
    (n : ℕ) (ψ : Degree Y (n+1) →ₗ[ℂ] ℂ)
    (hψ : ∀ (h : H) x, ψ (relabel (n+1) (fun y => h • y) x) = ψ x)
    (hψd : ∀ x, ψ (d (n+1) x) = 0)
    (c : K.chains (n+1))
    (hc : (⟨d n c, K.d_mem n c.property⟩ : K.chains n) ∈ K.relations hK n) :
    ψ (F (n+1) c) = ψ c := by
  let u : K.chains n →ₗ[ℂ] ℂ := (ψ.comp (homotopy F n)).comp (K.chains n).subtype
  have hu : ∀ x ∈ K.relations hK n, u x = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨h, y⟩, rfl⟩ := hx
      change ψ (homotopy F n (relabel n (fun y => h • y) (y : Degree Y n) - (y : Degree Y n))) = 0
      rw [map_sub, map_sub,
        ← homotopy_natural F F (fun y => h • y) (fun i => hFeq i h), hψ, sub_self]
    | zero => exact map_zero u
    | add x y _ _ hx hy => simp only [map_add, hx, hy, add_zero]
    | smul a x _ hx => simp only [map_smul, hx, smul_zero]
  have hzero : ψ (homotopy F n (d n c)) = 0 :=
    hu ⟨d n c, K.d_mem n c.property⟩ hc
  have he := congrArg ψ (homotopy_equation K F hF0 hF n c.property)
  rw [hψd, map_sub, map_sub, hzero, sub_zero] at he
  exact sub_eq_zero.mp he.symm
end ChainHomotopy
end BassTrace
end
end OAI

end

section
-- OAI.RingTheory.BassTrace.BarycentricChains
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
def Complex.projectionValues (K : Complex Y) (n : ℕ) : AltFunction Y n (K.chains n) := by
  classical
  refine {
  toFun := ?_, perm := ?_, zero := ?_ }
  · exact fun v => if hv : Finset.univ.image v ∈ K.faces then ⟨wedge n v, K.wedge_mem v hv⟩ else 0
  · intro v σ
    have he := tuple_image_perm v σ
    by_cases hv : Finset.univ.image v ∈ K.faces
    · simp only [he, dite_eq_left hv]
      apply Subtype.ext
      exact wedge_perm n v σ
    · simp only [he, dite_eq_right hv, smul_zero]
  · intro v hv
    split_ifs
    · apply Subtype.ext
      exact wedge_eq_zero_of_not_injective n hv
    · rfl
def Complex.projection (K : Complex Y) (n : ℕ) : Degree Y n →ₗ[ℂ] K.chains n :=
  (K.projectionValues n).lift
open Classical in
lemma Complex.projection_wedge (K : Complex Y) (n : ℕ) (v : Fin n → Y) :
    (K.projection n (wedge n v) : Degree Y n) =
      if Finset.univ.image v ∈ K.faces then wedge n v else 0 := by
  classical
  rw [projection, AltFunction.lift_wedge]
  dsimp only [Complex.projectionValues]
  split_ifs <;> rfl
lemma Complex.projection_self (K : Complex Y) (n : ℕ) {x : Degree Y n}
    (hx : x ∈ K.chains n) : (K.projection n x : Degree Y n) = x := by
  classical
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, hv, rfl⟩ := hx
    rw [K.projection_wedge, ite_eq_left hv]
  | zero => simp only [map_zero, Submodule.coe_zero]
  | add x y _ _ hx hy => simp only [map_add, Submodule.coe_add, hx, hy]
  | smul a x _ hx => simp only [map_smul, Submodule.coe_smul, hx]
lemma Complex.chains_zero (K : Complex Y) : K.chains 0 = ⊤ := by
  apply top_unique
  rw [← span_wedges 0]
  apply Submodule.span_le.mpr
  rintro x ⟨v, rfl⟩
  apply K.wedge_mem
  simpa using K.empty_mem
variable [Group H] [MulAction H Y]
lemma Complex.image_mem_iff (K : Complex Y) (hK : K.IsInvariant (H := H))
    (h : H) (s : Finset Y) : s.image (fun y => h • y) ∈ K.faces ↔ s ∈ K.faces := by
  constructor
  · intro hs
    have he := hK h⁻¹ _ hs
    simpa only [Finset.image_image, Function.comp_def, inv_smul_smul, Finset.image_id'] using he
  · exact hK h s
lemma Complex.projection_relabel (K : Complex Y) (hK : K.IsInvariant (H := H))
    (n : ℕ) (h : H) (x : Degree Y n) :
    (K.projection n (relabel n (fun y => h • y) x) : Degree Y n) =
      relabel n (fun y => h • y) (K.projection n x : Degree Y n) := by
  classical
  have he : ((K.chains n).subtype.comp (K.projection n)).comp
      (relabel n (fun y => h • y)) =
      (relabel n (fun y => h • y)).comp ((K.chains n).subtype.comp (K.projection n)) := by
    apply linearMap_ext_wedge
    intro v
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, relabel_wedge,
      K.projection_wedge]
    have he : Finset.univ.image ((fun y => h • y) ∘ v) ∈ K.faces ↔
        Finset.univ.image v ∈ K.faces := by
      rw [← Finset.image_image]
      exact K.image_mem_iff hK h _
    by_cases hv : Finset.univ.image v ∈ K.faces
    · rw [ite_eq_left (he.mpr hv), ite_eq_left hv, relabel_wedge]
    · rw [ite_eq_right (mt he.mp hv), ite_eq_right hv, map_zero]
  exact LinearMap.congr_fun he x
lemma source_coinvariant_comparison (K : Complex Y) (hK : K.IsInvariant (H := H))
    (F : ∀ n, K.chains n →ₗ[ℂ] Degree Y n)
    (hF0 : ∀ x, F 0 x = x)
    (hF : ∀ n (x : K.chains (n+1)), d n (F (n+1) x) =
      F n ⟨d n x, K.d_mem n x.property⟩)
    (hFeq : ∀ n (h : H) (x : K.chains n),
      relabel n (fun y => h • y) (F n x) =
        F n ⟨relabel n (fun y => h • y) x, K.relabel_mem hK n h x.property⟩)
    (n : ℕ) (ψ : Degree Y (n+1) →ₗ[ℂ] ℂ)
    (hψ : ∀ (h : H) x, ψ (relabel (n+1) (fun y => h • y) x) = ψ x)
    (hψd : ∀ x, ψ (d (n+1) x) = 0)
    (c : K.chains (n+1))
    (hc : (⟨d n c, K.d_mem n c.property⟩ : K.chains n) ∈ K.relations hK n) :
    ψ (F (n+1) c) = ψ c := by
  let G : ∀ n, Degree Y n →ₗ[ℂ] Degree Y n := fun n => (F n).comp (K.projection n)
  have hG0 : G 0 = LinearMap.id := by
    apply LinearMap.ext
    intro x
    change F 0 (K.projection 0 x) = x
    rw [hF0, K.projection_self 0]
    rw [K.chains_zero]
    trivial
  have hGK (n : ℕ) (x : K.chains n) : G n x = F n x := by
    apply congrArg (F n)
    apply Subtype.ext
    exact K.projection_self n x.property
  have hG (n : ℕ) (x : Degree Y (n+1)) (hx : x ∈ K.chains (n+1)) :
      d n (G (n+1) x) = G n (d n x) := by
    rw [hGK (n+1) ⟨x,hx⟩, hGK n ⟨d n x,K.d_mem n hx⟩]
    exact hF n ⟨x,hx⟩
  have hGeq (n : ℕ) (h : H) (x : Degree Y n) :
      relabel n (fun y => h • y) (G n x) = G n (relabel n (fun y => h • y) x) := by
    change relabel n (fun y => h • y) (F n (K.projection n x)) =
      F n (K.projection n (relabel n (fun y => h • y) x))
    rw [hFeq]
    apply congrArg (F n)
    apply Subtype.ext
    exact (K.projection_relabel hK n h x).symm
  have he := coinvariant_cocycle_comparison K hK G hG0 hG hGeq n ψ hψ hψd c hc
  rw [hGK] at he
  exact he
end ChainHomotopy
namespace BarycentricChains
open scoped BigOperators
open Oriented ChainHomotopy
variable {V Y : Type*} [LinearOrder V]
end BarycentricChains
end BassTrace
end
end OAI

end

section
-- OAI.RingTheory.BassTrace.OrbitAreas
namespace OAI
noncomputable section
namespace BassTrace
namespace Sparse
section
open Set Finset MeasureTheory
open scoped BassTrace.Sparse ENNReal Classical
variable {Y Z : Type*} [DecidableEq Y] [DecidableEq Z]
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
end Sparse
namespace Sparse.OrbitAreas
section
open scoped BigOperators Pointwise ENNReal
variable {H T : Type*} [Group H] [MulAction H T]
end
section
open MeasureTheory Set
open scoped ENNReal
variable {H T X : Type*} [Group H] [MulAction H T] [MulAction H X]
  [Countable H] [Countable T] [MeasurableSpace X]
end
open Set Finset MeasureTheory
open scoped Pointwise ENNReal Classical
variable {H T : Type*} [Group H] [MulAction H T]
variable [Finite (MulAction.orbitRel.Quotient H T)]
end Sparse.OrbitAreas
end BassTrace
end
end OAI

end

section
-- OAI.RingTheory.BassTrace.VolumeBounds
namespace OAI
noncomputable section
namespace BassTrace
open Set MeasureTheory
open Finset MeasureTheory intervalIntegral
namespace Sparse
def volumeThreshold (D : ℕ) : ℕ := (4 * D ^ 3 + D + 3) ^ 2
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
end Sparse.GraphGeometry
namespace Sparse
open Set MeasureTheory
open scoped ENNReal
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
variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)
variable (hΓaut : ∀ (h : H) u v,Γ.Adj (h•u) (h•v) ↔ Γ.Adj u v)
variable (hn : 0<n)
variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)
end Sparse.GraphGeometry
end BassTrace
end
end OAI

end

section
-- OAI.RingTheory.BassTrace.ClosedPaths
namespace OAI
noncomputable section
open Set MeasureTheory
open Finset MeasureTheory intervalIntegral
namespace BassTrace.Paths
open scoped BigOperators
section
variable {G ι : Type*} [Group G] [Fintype ι]
abbrev GroupMatrix := Matrix ι ι (MonoidAlgebra ℂ G)
abbrev ScalarMatrix := Matrix ι ι ℂ
def coefficient (e : GroupMatrix (G := G) (ι := ι)) (s : G) : ScalarMatrix (ι := ι) :=
  fun i j => (e i j).coeff s
def support (e : GroupMatrix (G := G) (ι := ι)) : Finset G := by
  classical
  exact Finset.univ.biUnion fun i => Finset.univ.biUnion fun j => (e i j).coeff.support
omit [Group G] in
lemma mem_support (e : GroupMatrix (G := G) (ι := ι)) (s : G) :
    s ∈ support e ↔ coefficient e s ≠ 0 := by
  classical
  simp only [support, Finset.mem_biUnion, Finset.mem_univ, true_and,
    Finsupp.mem_support_iff]
  constructor
  · rintro ⟨i,j,h⟩ he
    exact h (congrFun (congrFun he i) j)
  · intro h
    by_contra he
    apply h
    ext i j
    by_contra hij
    exact he ⟨i,j,hij⟩
omit [Group G] in
lemma entry_support_subset (e : GroupMatrix (G := G) (ι := ι)) (i j : ι) :
    (e i j).coeff.support ⊆ support e := by
  classical
  intro s hs
  simp only [support, Finset.mem_biUnion, Finset.mem_univ, true_and]
  exact ⟨i,j,hs⟩
lemma coefficient_mul (e f : GroupMatrix (G := G) (ι := ι)) (t : G) :
    coefficient (e*f) t = ∑ s ∈ support e, coefficient e s * coefficient f (s⁻¹*t) := by
  classical
  ext i j
  simp only [coefficient, Matrix.mul_apply, MonoidAlgebra.coeff_sum,
    Finsupp.finsetSum_apply, Matrix.sum_apply, MonoidAlgebra.coeff_mul_apply_left,
    Finsupp.sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_subset (entry_support_subset e i k)
  intro s _ hs
  rw [Finsupp.notMem_support_iff.mp hs, zero_mul]
def kernel (e : GroupMatrix (G := G) (ι := ι)) (h k : G) : ScalarMatrix (ι := ι) :=
  coefficient e (h⁻¹*k)
omit [Fintype ι] in
lemma kernel_left_invariant (e : GroupMatrix (G := G) (ι := ι)) (c h k : G) :
    kernel e (c*h) (c*k) = kernel e h k := by
  simp [kernel, mul_assoc]
lemma kernel_row_finite (e : GroupMatrix (G := G) (ι := ι)) (h : G) :
    Function.HasFiniteSupport (kernel e h) := by
  classical
  apply (support e).finite_toSet.image (fun s => h*s) |>.subset
  intro k hk
  refine ⟨h⁻¹*k, (mem_support e _).mpr hk, ?_⟩
  simp
lemma kernel_idempotent (e : GroupMatrix (G := G) (ι := ι)) (he : e*e=e) (h k : G) :
    (∑ s ∈ support e, kernel e h (h*s) * kernel e (h*s) k) = kernel e h k := by
  have hh := coefficient_mul e e (h⁻¹*k)
  rw [he] at hh
  simpa only [kernel, mul_inv_rev, inv_mul_cancel_left, mul_assoc] using hh.symm
lemma kernel_idempotent_finsum (e : GroupMatrix (G := G) (ι := ι)) (he : e*e=e)
    (h k : G) :
    (∑ᶠ u, kernel e h u * kernel e u k) = kernel e h k := by
  classical
  have hs : Function.support (fun u => kernel e h u * kernel e u k) ⊆
      (fun s => h*s) '' (support e : Set G) := by
    intro u hu
    refine ⟨h⁻¹*u, (mem_support e _).mpr ?_, by simp⟩
    intro hz
    exact hu (by change coefficient e (h⁻¹*u) * _ = 0; rw [hz, zero_mul])
  rw [finsum_eq_finsetSum_of_support_subset (f := fun u : G => kernel e h u * kernel e u k) (s := (support e).image (fun s => h*s))
    (by simpa only [Finset.coe_image] using hs)]
  rw [Finset.sum_image (fun a _ b _ hab => mul_left_cancel hab)]
  exact kernel_idempotent e he h k
end
section
variable {G : Type*} [Group G]
def pathSetoid (g : G) (n : ℕ) : Setoid (Fin (n+1) → G) where
  r h k := ∃ c : Subgroup.centralizer ({g} : Set G), ∀ i, (c : G)*h i = k i
  iseqv := ⟨fun h => ⟨1, by simp⟩, by
    rintro h k ⟨c,hc⟩
    refine ⟨c⁻¹, fun i => ?_⟩
    rw [← hc i]
    simp,
    by
    rintro h k l ⟨c,hc⟩ ⟨d,hd⟩
    refine ⟨d*c, fun i => ?_⟩
    change ((d:G)*(c:G))*h i = l i
    rw [mul_assoc,hc,hd]⟩
abbrev Orbit (g : G) (n : ℕ) := Quotient (pathSetoid g n)
def increment (g : G) (n : ℕ) (h : Fin (n+1) → G) (i : Fin (n+1)) : G :=
  (h i)⁻¹ * (if i = Fin.last n then g*h 0 else h (finRotate (n+1) i))
lemma increment_castSucc (g : G) (n : ℕ) (h : Fin (n+1) → G) (i : Fin n) :
    increment g n h i.castSucc = (h i.castSucc)⁻¹*h i.succ := by
  simp [increment,Fin.castSucc_ne_last]
lemma increment_last (g : G) (n : ℕ) (h : Fin (n+1) → G) :
    increment g n h (Fin.last n) = (h (Fin.last n))⁻¹*g*h 0 := by
  simp [increment,mul_assoc]
lemma increment_invariant (g : G) (n : ℕ)
    (c : Subgroup.centralizer ({g} : Set G)) (h : Fin (n+1) → G) :
    increment g n (fun i => c*h i) = increment g n h := by
  funext i
  have hc := Subgroup.mem_centralizer_singleton_iff.mp c.property
  simp only [increment]
  split_ifs
  · rw [← mul_assoc g, ← hc, mul_assoc (c:G)]
    simp [mul_assoc]
  · simp [mul_assoc]
lemma increment_eq_imp_related (g : G) (n : ℕ) (h k : Fin (n+1) → G)
    (he : increment g n h = increment g n k) : pathSetoid g n h k := by
  let c : G := k 0*(h 0)⁻¹
  have hk (i : Fin (n+1)) : k i = c*h i := by
    induction i using Fin.induction with
    | zero => simp [c]
    | succ i hi =>
      have hi' := congrFun he i.castSucc
      rw [increment_castSucc,increment_castSucc,hi] at hi'
      have hm := congrArg (fun z => (c*h i.castSucc)*z) hi'
      simpa [mul_assoc] using hm.symm
  have ht := congrFun he (Fin.last n)
  rw [increment_last,increment_last,hk (Fin.last n),hk 0] at ht
  have hcg := congrArg (fun z => h (Fin.last n)*z*(h 0)⁻¹) ht
  have hc' : g = c⁻¹*g*c := by simpa [mul_inv_rev,mul_assoc] using hcg
  have hc : c*g = g*c := by
    calc c*g = c*(c⁻¹*g*c) := congrArg (c*·) hc'
         _ = g*c := by group
  exact ⟨⟨c,Subgroup.mem_centralizer_singleton_iff.mpr hc⟩,fun i => (hk i).symm⟩
def orbitIncrement (g : G) (n : ℕ) : Orbit g n → (Fin (n+1) → G) :=
  Quotient.lift (increment g n) (by
    rintro h k ⟨c,hc⟩
    have hk : k = fun i => c*h i := funext fun i => (hc i).symm
    rw [hk,increment_invariant])
lemma orbitIncrement_injective (g : G) (n : ℕ) :
    Function.Injective (orbitIncrement g n) := by
  intro q r
  induction q using Quotient.inductionOn with | _ h =>
    induction r using Quotient.inductionOn with | _ k =>
      exact fun he => Quotient.sound (increment_eq_imp_related g n h k he)
variable {ι : Type*} [Fintype ι]
def weight (e : GroupMatrix (G := G) (ι := ι)) (g : G) (n : ℕ)
    (h : Fin (n+1) → G) : ℂ := by
  classical
  exact Matrix.trace (List.ofFn (fun i => coefficient e (increment g n h i))).prod
lemma weight_invariant (e : GroupMatrix (G := G) (ι := ι)) (g : G) (n : ℕ)
    (c : Subgroup.centralizer ({g} : Set G)) (h : Fin (n+1) → G) :
    weight e g n (fun i => c*h i) = weight e g n h := by
  classical
  simp only [weight,increment_invariant]
lemma weight_ne_zero_support (e : GroupMatrix (G := G) (ι := ι)) (g : G) (n : ℕ)
    (h : Fin (n+1) → G) (hw : weight e g n h ≠ 0) (i : Fin (n+1)) :
    increment g n h i ∈ support e := by
  classical
  apply (mem_support e _).mpr
  intro hi
  apply hw
  have hz : (0 : ScalarMatrix (ι := ι)) ∈
      List.ofFn (fun j => coefficient e (increment g n h j)) := by
    exact List.mem_ofFn.mpr ⟨i,hi⟩
  simp only [weight,List.prod_eq_zero hz,Matrix.trace_zero]
def orbitWeight (e : GroupMatrix (G := G) (ι := ι)) (g : G) (n : ℕ) :
    Orbit g n → ℂ := Quotient.lift (weight e g n) (by
  rintro h k ⟨c,hc⟩
  have hk : k = fun i => c*h i := funext fun i => (hc i).symm
  rw [hk,weight_invariant])
lemma orbitWeight_finite (e : GroupMatrix (G := G) (ι := ι)) (g : G) (n : ℕ) :
    Function.HasFiniteSupport (orbitWeight e g n) := by
  classical
  have hfinite : {f : Fin (n+1) → G | ∀ i, f i ∈ support e}.Finite := by
    exact Set.Finite.pi' (fun _ => (support e).finite_toSet)
  apply (hfinite.preimage (orbitIncrement_injective g n).injOn).subset
  intro q hq
  induction q using Quotient.inductionOn with | _ h =>
    exact weight_ne_zero_support e g n h hq
def pathVector (e : GroupMatrix (G := G) (ι := ι)) (g : G) (n : ℕ) :
    Orbit g n →₀ ℂ := Finsupp.ofSupportFinite (orbitWeight e g n) (orbitWeight_finite e g n)
end
section
variable {G : Type*} [Group G]
def twist (g : G) (n : ℕ) (h : Fin (n+1) → G) : Fin (n+1) → G :=
  Fin.snoc (fun i : Fin n => h i.succ) (g*h 0)
@[simp] lemma twist_castSucc (g : G) (n : ℕ) (h : Fin (n+1) → G) (i : Fin n) :
    twist g n h i.castSucc = h i.succ := by simp [twist]
@[simp] lemma twist_last (g : G) (n : ℕ) (h : Fin (n+1) → G) :
    twist g n h (Fin.last n) = g*h 0 := by simp [twist]
lemma rotate_castSucc (n : ℕ) (i : Fin n) :
    finRotate (n+1) i.castSucc = i.succ := finRotate_of_lt i.isLt
lemma increment_twist (g : G) (n : ℕ) (h : Fin (n+1) → G) :
    increment g n (twist g n h) = increment g n h ∘ finRotate (n+1) := by
  funext i
  cases n with
  | zero =>
    have hi : i = Fin.last 0 := Fin.ext (by omega)
    subst i
    simp only [Function.comp_apply,finRotate_last,increment_last,twist_last]
    have hz : (0 : Fin 1) = Fin.last 0 := rfl
    rw [hz,increment_last]
    simp [mul_assoc]
    exact twist_last g 0 h
  | succ n =>
    induction i using Fin.lastCases with
    | last =>
      simp only [increment_last,twist_last,Function.comp_apply,finRotate_last]
      have hz : (0 : Fin (n+1+1)) = (0 : Fin (n+1)).castSucc := rfl
      rw [hz,twist_castSucc,increment_castSucc]
      simp [mul_assoc]
    | cast i =>
      rw [increment_castSucc]
      simp only [Function.comp_apply,rotate_castSucc,twist_castSucc]
      induction i using Fin.lastCases with
      | last =>
        simp only [Fin.succ_last,twist_last,increment_last,mul_assoc]
      | cast i =>
        rw [← Fin.castSucc_succ,twist_castSucc,increment_castSucc]
variable {ι : Type*} [Fintype ι]
lemma weight_twist (e : GroupMatrix (G := G) (ι := ι)) (g : G) (n : ℕ)
    (h : Fin (n+1) → G) : weight e g n (twist g n h) = weight e g n h := by
  classical
  simp only [weight,increment_twist,Function.comp_apply]
  rw [List.ofFn_succ',List.ofFn_succ]
  simp only [rotate_castSucc,finRotate_last,List.prod_concat,List.prod_cons]
  exact Matrix.trace_mul_comm _ _
end
variable {G ι : Type*} [Group G] [Fintype ι]
def prefixProduct (e : GroupMatrix (G := G) (ι := ι)) {n : ℕ}
    (h : Fin (n+1) → G) : ScalarMatrix (ι := ι) := by
  classical
  exact (List.ofFn (fun i : Fin n => kernel e (h i.castSucc) (h i.succ))).prod
lemma weight_eq_prefix (e : GroupMatrix (G := G) (ι := ι)) (g : G) (n : ℕ)
    (h : Fin (n+1) → G) : weight e g n h =
      Matrix.trace (prefixProduct e h * kernel e (h (Fin.last n)) (g*h 0)) := by
  classical
  rw [weight,List.ofFn_succ',List.prod_concat]
  simp only [increment_castSucc,increment_last,prefixProduct,kernel,mul_assoc]
lemma prefixProduct_snoc (e : GroupMatrix (G := G) (ι := ι)) (n : ℕ)
    (h : Fin (n+1) → G) (u : G) :
    prefixProduct e (Fin.snoc h u) = prefixProduct e h * kernel e (h (Fin.last n)) u := by
  classical
  unfold prefixProduct
  rw [List.ofFn_succ',List.prod_concat]
  congr 1
  · congr 2
    funext i
    simp [← Fin.castSucc_succ]
  · simp
lemma weight_snoc (e : GroupMatrix (G := G) (ι := ι)) (g : G) (n : ℕ)
    (h : Fin (n+1) → G) (u : G) : weight e g (n+1) (Fin.snoc h u) =
    Matrix.trace (prefixProduct e h *
      (kernel e (h (Fin.last n)) u * kernel e u (g*h 0))) := by
  classical
  rw [weight_eq_prefix,prefixProduct_snoc]
  have hz : (0 : Fin (n+1+1)) = (0 : Fin (n+1)).castSucc := rfl
  simp only [Fin.snoc_last,mul_assoc,hz,Fin.snoc_castSucc]
lemma weight_snoc_finsum (e : GroupMatrix (G := G) (ι := ι)) (he : e*e=e)
    (g : G) (n : ℕ) (h : Fin (n+1) → G) :
    (∑ᶠ u : G, weight e g (n+1) (Fin.snoc h u)) = weight e g n h := by
  classical
  let f : ScalarMatrix (ι := ι) →ₗ[ℂ] ℂ :=
    (Matrix.traceLinearMap ι ℂ ℂ).comp (LinearMap.mulLeft ℂ (prefixProduct e h))
  have hs : Function.HasFiniteSupport (fun u =>
      kernel e (h (Fin.last n)) u * kernel e u (g*h 0)) := by
    apply (kernel_row_finite e (h (Fin.last n))).subset
    intro u hu hz
    apply hu
    dsimp only
    rw [hz,zero_mul]
  simp only [weight_snoc]
  rw [weight_eq_prefix]
  change (∑ᶠ u : G, f (kernel e (h (Fin.last n)) u * kernel e u (g*h 0))) = _
  rw [← map_finsum f hs,kernel_idempotent_finsum e he]
  rfl
end BassTrace.Paths
end
end OAI

end

section
-- OAI.RingTheory.BassTrace.PathWeights
namespace OAI
noncomputable section
open Set MeasureTheory
open Finset MeasureTheory intervalIntegral
namespace BassTrace.Paths
open scoped BigOperators
section
lemma mapDomain_apply_of_fibre {A B C M : Type*} [AddCommMonoid M]
    (v : A →₀ M) (d : A → B) (b : B) (j : C → A)
    (hj : Function.Injective j) (hf : ∀ a, d a = b ↔ a ∈ Set.range j) :
    (v.mapDomain d) b = ∑ᶠ c : C, v (j c) := by
  classical
  have hs : Function.support (fun a => if d a = b then v a else 0) ⊆ (v.support : Set A) := by
    intro a ha
    by_contra hnot
    apply ha
    simp [Finsupp.notMem_support_iff.mp hnot]
  calc
    (v.mapDomain d) b = ∑ a ∈ v.support, if d a = b then v a else 0 := by
      simp [Finsupp.mapDomain,Finsupp.sum,Finsupp.single_apply,eq_comm]
    _ = ∑ᶠ a : A, if d a = b then v a else 0 :=
      (finsum_eq_finsetSum_of_support_subset _ hs).symm
    _ = ∑ᶠ a ∈ Set.range j, v a := by simp only [finsum_eq_if,← hf]
    _ = ∑ᶠ c : C, v (j c) := finsum_mem_range hj
variable {G : Type*} [Group G]
def deleteLast (g : G) (n : ℕ) : Orbit g (n+1) → Orbit g n :=
  Quotient.map (fun h i => h i.castSucc) (by
    rintro h k ⟨c,hc⟩
    exact ⟨c,fun i => hc i.castSucc⟩)
def insertOrbit (g : G) (n : ℕ) (h : Fin (n+1) → G) (u : G) : Orbit g (n+1) :=
  Quotient.mk _ (Fin.snoc h u)
@[simp] lemma deleteLast_insertOrbit (g : G) (n : ℕ) (h : Fin (n+1) → G) (u : G) :
    deleteLast g n (insertOrbit g n h u) = Quotient.mk _ h := by
  change Quotient.mk (pathSetoid g n) (fun i : Fin (n+1) => Fin.snoc (α := fun _ => G) h u i.castSucc) = Quotient.mk (pathSetoid g n) h
  congr 1
  funext i
  exact Fin.snoc_castSucc (α := fun _ => G) u h i
lemma insertOrbit_injective (g : G) (n : ℕ) (h : Fin (n+1) → G) :
    Function.Injective (insertOrbit g n h) := by
  intro u v huv
  obtain ⟨c,hc⟩ := Quotient.exact huv
  have h0 := hc ((0 : Fin (n+1)).castSucc)
  simp only [Fin.snoc_castSucc] at h0
  have hc1 : (c:G) = 1 := mul_right_cancel (h0.trans (one_mul _).symm)
  have hl := hc (Fin.last (n+1))
  simpa only [Fin.snoc_last,hc1,one_mul] using hl
lemma deleteLast_fibre (g : G) (n : ℕ) (h : Fin (n+1) → G) (q : Orbit g (n+1)) :
    deleteLast g n q = Quotient.mk _ h ↔ q ∈ Set.range (insertOrbit g n h) := by
  constructor
  · induction q using Quotient.inductionOn with | _ k =>
      intro hq
      obtain ⟨c,hc⟩ := Quotient.exact hq
      refine ⟨c*k (Fin.last (n+1)), ?_⟩
      apply Eq.symm
      apply Quotient.sound
      refine ⟨c,fun i => ?_⟩
      induction i using Fin.lastCases with
      | last => simp
      | cast i => simpa only [Fin.snoc_castSucc] using hc i
  · rintro ⟨u,rfl⟩
    exact deleteLast_insertOrbit g n h u
variable {ι : Type*} [Fintype ι]
lemma pathVector_deleteLast (e : GroupMatrix (G := G) (ι := ι)) (he : e*e=e)
    (g : G) (n : ℕ) :
    (pathVector e g (n+1)).mapDomain (deleteLast g n) = pathVector e g n := by
  classical
  ext q
  induction q using Quotient.inductionOn with | _ h =>
    rw [mapDomain_apply_of_fibre _ _ _ (insertOrbit g n h)
      (insertOrbit_injective g n h) (deleteLast_fibre g n h)]
    change (∑ᶠ u, weight e g (n+1) (Fin.snoc h u)) = weight e g n h
    exact weight_snoc_finsum e he g n h
end
section
variable {G ι : Type*} [Group G] [Fintype ι]
def totalWeight (e : GroupMatrix (G := G) (ι := ι)) (g : G) (n : ℕ) : ℂ :=
  (pathVector e g n).sum fun _ z => z
lemma totalWeight_succ (e : GroupMatrix (G := G) (ι := ι)) (he : e*e=e)
    (g : G) (n : ℕ) : totalWeight e g (n+1) = totalWeight e g n := by
  unfold totalWeight
  rw [← pathVector_deleteLast e he g n]
  exact (Finsupp.sum_mapDomain_index (h := fun (_ : Orbit g n) (z : ℂ) => z)
    (fun _ => rfl) (fun _ _ _ => rfl)).symm
lemma totalWeight_eq_zeroDegree (e : GroupMatrix (G := G) (ι := ι)) (he : e*e=e)
    (g : G) (n : ℕ) : totalWeight e g n = totalWeight e g 0 := by
  induction n with
  | zero => rfl
  | succ n hn => rw [totalWeight_succ e he,hn]
def zeroConjugate (g : G) (q : Orbit g 0) : G := orbitIncrement g 0 q 0
lemma zeroConjugate_mk (g h : G) :
    zeroConjugate g (Quotient.mk _ (fun _ => h)) = h⁻¹*g*h := by
  change increment g 0 (fun _ => h) (Fin.last 0) = _
  exact increment_last g 0 _
lemma zeroConjugate_injective (g : G) : Function.Injective (zeroConjugate g) := by
  intro a b hab
  apply orbitIncrement_injective g 0
  funext i
  have hi : i = (0 : Fin 1) := Fin.ext (by omega)
  subst i
  exact hab
lemma range_zeroConjugate (g : G) : Set.range (zeroConjugate g) = {s | IsConj s g} := by
  ext s
  constructor
  · rintro ⟨q,rfl⟩
    induction q using Quotient.inductionOn with | _ h =>
      change IsConj (increment g 0 h (Fin.last 0)) g
      rw [increment_last]
      apply isConj_iff.mpr
      refine ⟨h 0, ?_⟩
      have hl : Fin.last 0 = (0 : Fin 1) := rfl
      rw [hl]
      group
  · intro hs
    obtain ⟨h,hh⟩ := isConj_iff.mp hs
    refine ⟨Quotient.mk _ (fun _ => h), ?_⟩
    rw [zeroConjugate_mk,← hh]
    group
lemma orbitWeight_zeroDegree (e : GroupMatrix (G := G) (ι := ι)) (g : G)
    (q : Orbit g 0) : orbitWeight e g 0 q = Matrix.trace (coefficient e (zeroConjugate g q)) := by
  classical
  induction q using Quotient.inductionOn with | _ h =>
    change weight e g 0 h = _
    simp only [weight,List.ofFn_succ,List.ofFn_zero,List.prod_cons,List.prod_nil,mul_one]
    rfl
lemma totalWeight_finsum (e : GroupMatrix (G := G) (ι := ι)) (g : G) (n : ℕ) :
    totalWeight e g n = ∑ᶠ q, orbitWeight e g n q := by
  classical
  exact (finsum_eq_finsetSum_of_support_subset _ (by
    intro q hq
    exact (Finsupp.mem_support_iff.mpr hq : q ∈ (pathVector e g n).support))).symm
lemma totalWeight_conjugacy (e : GroupMatrix (G := G) (ι := ι)) (he : e*e=e)
    (g : G) (n : ℕ) : totalWeight e g n =
    ∑ᶠ s ∈ {s : G | IsConj s g}, Matrix.trace (coefficient e s) := by
  rw [totalWeight_eq_zeroDegree e he,totalWeight_finsum]
  simp only [orbitWeight_zeroDegree]
  rw [← finsum_mem_range (f := fun s => Matrix.trace (coefficient e s)) (zeroConjugate_injective g),range_zeroConjugate]
end
variable {G : Type*} [Group G]
lemma twist_equivariant (g : G) (n : ℕ) (c : Subgroup.centralizer ({g} : Set G))
    (h : Fin (n+1) → G) : twist g n (fun i => c*h i) = fun i => c*twist g n h i := by
  funext i
  induction i using Fin.lastCases with
  | last =>
    simp only [twist_last]
    rw [← mul_assoc,← Subgroup.mem_centralizer_singleton_iff.mp c.property,mul_assoc]
  | cast i => simp only [twist_castSucc]
def orbitTwist (g : G) (n : ℕ) : Orbit g n → Orbit g n :=
  Quotient.map (twist g n) (by
    rintro h k ⟨c,hc⟩
    have hk : k = fun i => c*h i := funext fun i => (hc i).symm
    rw [hk,twist_equivariant]
    exact ⟨c,fun _ => rfl⟩)
lemma orbitIncrement_twist (g : G) (n : ℕ) (q : Orbit g n) :
    orbitIncrement g n (orbitTwist g n q) = orbitIncrement g n q ∘ finRotate (n+1) := by
  induction q using Quotient.inductionOn with | _ h => exact increment_twist g n h
lemma orbitTwist_injective (g : G) (n : ℕ) : Function.Injective (orbitTwist g n) := by
  intro a b hab
  apply orbitIncrement_injective g n
  have he := congrArg (orbitIncrement g n) hab
  rw [orbitIncrement_twist,orbitIncrement_twist] at he
  funext i
  obtain ⟨j,rfl⟩ := (finRotate (n+1)).surjective i
  exact congrFun he j
lemma twist_surjective (g : G) (n : ℕ) : Function.Surjective (twist g n) := by
  intro h
  refine ⟨Fin.cons (α := fun _ => G) (g⁻¹*h (Fin.last n)) (fun i => h i.castSucc), ?_⟩
  funext i
  induction i using Fin.lastCases with
  | last => simp
  | cast i => simp
lemma orbitTwist_surjective (g : G) (n : ℕ) : Function.Surjective (orbitTwist g n) := by
  intro q
  induction q using Quotient.inductionOn with | _ h =>
    obtain ⟨k,rfl⟩ := twist_surjective g n h
    exact ⟨Quotient.mk _ k,rfl⟩
variable {ι : Type*} [Fintype ι]
lemma orbitWeight_twist (e : GroupMatrix (G := G) (ι := ι)) (g : G) (n : ℕ)
    (q : Orbit g n) : orbitWeight e g n (orbitTwist g n q) = orbitWeight e g n q := by
  induction q using Quotient.inductionOn with | _ h => exact weight_twist e g n h
lemma pathVector_twist (e : GroupMatrix (G := G) (ι := ι)) (g : G) (n : ℕ) :
    (pathVector e g n).mapDomain (orbitTwist g n) = pathVector e g n := by
  ext q
  obtain ⟨p,rfl⟩ := orbitTwist_surjective g n q
  rw [Finsupp.mapDomain_apply_of_injective (orbitTwist_injective g n)]
  exact (orbitWeight_twist e g n p).symm
omit [Fintype ι] in
lemma delete_twist_tuple (g : G) (n : ℕ) (h : Fin (n+2) → G) (i : Fin (n+1)) :
    (fun j => twist g (n+1) h (i.castSucc.succAbove j)) =
      twist g n (fun j => h (i.succ.succAbove j)) := by
  funext j
  induction j using Fin.lastCases with
  | last => simp only [Fin.succAbove_ne_last_last (Fin.castSucc_ne_last i),twist_last,
      Fin.succAbove_ne_zero_zero (Fin.succ_ne_zero i)]
  | cast j =>
    rw [Fin.castSucc_succAbove_castSucc]
    simp only [twist_castSucc,Fin.succ_succAbove_succ]
def deleteEntry (g : G) (n : ℕ) (i : Fin (n+2)) : Orbit g (n+1) → Orbit g n :=
  Quotient.map (fun h j => h (i.succAbove j)) (by
    rintro h k ⟨c,hc⟩
    exact ⟨c,fun j => hc (i.succAbove j)⟩)
omit [Fintype ι] in
lemma deleteEntry_zero (g : G) (n : ℕ) :
    deleteEntry g n 0 = deleteLast g n ∘ orbitTwist g (n+1) := by
  funext q
  induction q using Quotient.inductionOn with | _ h =>
    change Quotient.mk (pathSetoid g n) (fun j => h j.succ) =
      Quotient.mk (pathSetoid g n) (fun j => twist g (n+1) h j.castSucc)
    simp only [twist_castSucc]
omit [Fintype ι] in
lemma deleteEntry_castSucc_twist (g : G) (n : ℕ) (i : Fin (n+1)) :
    deleteEntry g n i.castSucc ∘ orbitTwist g (n+1) =
      orbitTwist g n ∘ deleteEntry g n i.succ := by
  funext q
  induction q using Quotient.inductionOn with | _ h =>
    change Quotient.mk (pathSetoid g n) (fun j => twist g (n+1) h (i.castSucc.succAbove j)) =
      Quotient.mk (pathSetoid g n) (twist g n (fun j => h (i.succ.succAbove j)))
    rw [delete_twist_tuple]
lemma pathVector_deleteEntry (e : GroupMatrix (G := G) (ι := ι)) (he : e*e=e)
    (g : G) (n : ℕ) (i : Fin (n+2)) :
    (pathVector e g (n+1)).mapDomain (deleteEntry g n i) = pathVector e g n := by
  induction i using Fin.induction with
  | zero =>
    rw [deleteEntry_zero,Finsupp.mapDomain_comp,pathVector_twist,pathVector_deleteLast e he]
  | succ i hi =>
    apply Finsupp.mapDomain_injective (orbitTwist_injective g n)
    rw [← Finsupp.mapDomain_comp,← deleteEntry_castSucc_twist,Finsupp.mapDomain_comp,
      pathVector_twist,hi,pathVector_twist]
end BassTrace.Paths
end
end OAI

end

section
-- OAI.RingTheory.BassTrace.ExteriorDetector
namespace OAI
noncomputable section
open Set MeasureTheory
open Finset MeasureTheory intervalIntegral
namespace BassTrace.Detector
section
open scoped BigOperators
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
lemma ι_mul_ι_neg (u v : M) :
    ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R v =
      -(ExteriorAlgebra.ι R v * ExteriorAlgebra.ι R u) :=
  eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap u v)
lemma ι_commute_two (u v w : M) :
    Commute (ExteriorAlgebra.ι R u)
      (ExteriorAlgebra.ι R v * ExteriorAlgebra.ι R w) := by
  change _ * _ = _ * _
  calc
    _ = (ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R v) * ExteriorAlgebra.ι R w :=
      (mul_assoc _ _ _).symm
    _ = -(ExteriorAlgebra.ι R v * (ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R w)) := by
      rw [ι_mul_ι_neg u v, neg_mul, mul_assoc]
    _ = ExteriorAlgebra.ι R v * (ExteriorAlgebra.ι R w * ExteriorAlgebra.ι R u) := by
      rw [ι_mul_ι_neg u w, mul_neg, neg_neg]
    _ = _ := (mul_assoc _ _ _).symm
lemma ι_commute_degree_two (u : M) {b : ExteriorAlgebra R M} (hb : b ∈ ⋀[R]^2 M) :
    Commute (ExteriorAlgebra.ι R u) b := by
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree R 2] at hb
  induction hb using Submodule.span_induction with
  | mem b hb =>
    obtain ⟨v, rfl⟩ := hb
    simpa [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply,
      Matrix.vecTail] using ι_commute_two u (v 0) (v 1)
  | zero => exact Commute.zero_right _
  | add b c _ _ hb hc => exact hb.add_right hc
  | smul a b _ hb =>
    show ExteriorAlgebra.ι R u * (a • b) = (a • b) * ExteriorAlgebra.ι R u
    rw [mul_smul_comm, smul_mul_assoc, hb.eq]
lemma gauge_invariance (u v : M) {b : ExteriorAlgebra R M}
    (hb : b ∈ ⋀[R]^2 M) (m : ℕ) :
    ExteriorAlgebra.ι R u *
        (b + ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R v)^m =
      ExteriorAlgebra.ι R u * b^m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, ← mul_assoc, ih, mul_add, pow_succ, ← mul_assoc]
    have hcomm := (ι_commute_degree_two u hb).pow_right m
    have hz : ExteriorAlgebra.ι R u * b^m *
        (ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R v) = 0 := by
      rw [hcomm.eq, mul_assoc, ← mul_assoc (ExteriorAlgebra.ι R u),
        ExteriorAlgebra.ι_sq_zero, zero_mul, mul_zero]
    simp only [mul_assoc] at hz ⊢
    rw [hz, add_zero]
end
open scoped BigOperators
section
variable {I : Type*} [Fintype I]
abbrev CoordinateSpace (I : Type*) := I →₀ ℂ
abbrev CoordinateAlgebra (I : Type*) := ExteriorAlgebra ℂ (CoordinateSpace I)
def coordinate (i : I) : CoordinateSpace I := Finsupp.single i 1
def coordinateVector (a : I → ℂ) : CoordinateSpace I := ∑ i, a i • coordinate i
def rawTwoForm (B : I → I → ℂ) : CoordinateAlgebra I :=
  ∑ i, ∑ j, B i j • (ExteriorAlgebra.ι ℂ (coordinate i) * ExteriorAlgebra.ι ℂ (coordinate j))
def twoForm (B : I → I → ℂ) : CoordinateAlgebra I := (2 : ℂ)⁻¹ • rawTwoForm B
lemma rawTwoForm_add (A B : I → I → ℂ) :
    rawTwoForm (fun i j => A i j + B i j) = rawTwoForm A + rawTwoForm B := by
  simp only [rawTwoForm, add_smul, Finset.sum_add_distrib]
lemma rawTwoForm_sub (A B : I → I → ℂ) :
    rawTwoForm (fun i j => A i j - B i j) = rawTwoForm A - rawTwoForm B := by
  simp only [rawTwoForm, sub_smul, Finset.sum_sub_distrib]
lemma rawTwoForm_rank_one (a b : I → ℂ) :
    rawTwoForm (fun i j => a i * b j) =
      ExteriorAlgebra.ι ℂ (coordinateVector a) * ExteriorAlgebra.ι ℂ (coordinateVector b) := by
  simp only [rawTwoForm, coordinateVector, map_sum, map_smul, Finset.sum_mul,
    Finset.mul_sum, smul_mul_assoc, mul_smul_comm, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_comm]
lemma twoForm_add (A B : I → I → ℂ) :
    twoForm (fun i j => A i j + B i j) = twoForm A + twoForm B := by
  simp only [twoForm, rawTwoForm_add, smul_add]
lemma twoForm_decomposable (a b : I → ℂ) :
    twoForm (fun i j => a i * b j - b i * a j) =
      ExteriorAlgebra.ι ℂ (coordinateVector a) * ExteriorAlgebra.ι ℂ (coordinateVector b) := by
  rw [twoForm, rawTwoForm_sub, rawTwoForm_rank_one, rawTwoForm_rank_one,
    ι_mul_ι_neg (coordinateVector b) (coordinateVector a), sub_neg_eq_add]
  module
lemma twoForm_mem (B : I → I → ℂ) : twoForm B ∈ ⋀[ℂ]^2 (CoordinateSpace I) := by
  apply Submodule.smul_mem
  apply Submodule.sum_mem
  intro i _
  apply Submodule.sum_mem
  intro j _
  apply Submodule.smul_mem
  change _ ∈ (ExteriorAlgebra.ι ℂ).range^2
  rw [pow_two]
  exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ _) (LinearMap.mem_range_self _ _)
lemma twoForm_lift_change (B : I → I → ℂ) (r : I → ℂ) :
    twoForm (fun i j => B i j + r j - r i) = twoForm B +
      ExteriorAlgebra.ι ℂ (coordinateVector (fun _ : I => 1)) *
        ExteriorAlgebra.ι ℂ (coordinateVector r) := by
  have he : (fun i j => B i j + r j - r i) =
      (fun i j => B i j + ((1 : ℂ)*r j-r i*1)) := by funext i j; ring
  rw [he, twoForm_add, twoForm_decomposable]
lemma detector_form_lift_independent (B : I → I → ℂ) (r : I → ℂ) (m : ℕ) :
    ExteriorAlgebra.ι ℂ (coordinateVector (fun _ : I => 1)) *
        ((m.factorial : ℂ)⁻¹ • (twoForm (fun i j => B i j + r j - r i))^m) =
      ExteriorAlgebra.ι ℂ (coordinateVector (fun _ : I => 1)) *
        ((m.factorial : ℂ)⁻¹ • (twoForm B)^m) := by
  rw [twoForm_lift_change, mul_smul_comm, mul_smul_comm,
    gauge_invariance _ _ (twoForm_mem B)]
def coordinateMap {J : Type*} (f : I → J) : CoordinateSpace I →ₗ[ℂ] CoordinateSpace J :=
  Finsupp.lmapDomain ℂ ℂ f
omit [Fintype I] in
@[simp] lemma coordinateMap_coordinate {J : Type*} (f : I → J) (i : I) :
    coordinateMap f (coordinate i) = coordinate (f i) := Finsupp.mapDomain_single
lemma coordinateMap_vector {J : Type*} [Fintype J] (f : I ≃ J) (a : I → ℂ) :
    coordinateMap f (coordinateVector a) = coordinateVector (a ∘ f.symm) := by
  simp only [coordinateVector, map_sum, map_smul, coordinateMap_coordinate]
  simpa only [Equiv.symm_apply_apply, Function.comp_def] using
    Equiv.sum_comp f (fun j => a (f.symm j) • coordinate j)
lemma twoForm_map {J : Type*} [Fintype J] (f : I ≃ J) (B : J → J → ℂ) :
    ExteriorAlgebra.map (coordinateMap f) (twoForm (fun i j => B (f i) (f j))) =
      twoForm B := by
  simp only [twoForm, rawTwoForm, map_smul, map_sum, map_mul,
    ExteriorAlgebra.map_apply_ι, coordinateMap_coordinate]
  apply congrArg (fun x : CoordinateAlgebra J => (2 : ℂ)⁻¹ • x)
  calc
    _ = ∑ i : I, ∑ j : J, B (f i) j •
        (ExteriorAlgebra.ι ℂ (coordinate (f i)) * ExteriorAlgebra.ι ℂ (coordinate j)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Equiv.sum_comp f (fun j : J => B (f i) j •
        (ExteriorAlgebra.ι ℂ (coordinate (f i)) * ExteriorAlgebra.ι ℂ (coordinate j)))
    _ = _ := Equiv.sum_comp f (fun i : J => ∑ j : J, B i j •
        (ExteriorAlgebra.ι ℂ (coordinate i) * ExteriorAlgebra.ι ℂ (coordinate j)))
end
section
abbrev coordinateBasis (n : ℕ) : Module.Basis (Fin n) ℂ (CoordinateSpace (Fin n)) :=
  Finsupp.basisSingleOne
def topIndex (n : ℕ) : Set.powersetCard (Fin n) n :=
  Set.powersetCard.ofFinEmbEquiv ((OrderIso.refl (Fin n)).toOrderEmbedding)
lemma topIndex_val (n : ℕ) : (topIndex n).val = Finset.univ := by
  ext i
  simp only [Finset.mem_univ, iff_true]
  change i ∈ Set.powersetCard.ofFinEmbEquiv ((OrderIso.refl (Fin n)).toOrderEmbedding)
  rw [Set.powersetCard.mem_ofFinEmbEquiv_iff_mem_range]
  exact ⟨i, rfl⟩
lemma topIndex_unique (n : ℕ) (s : Set.powersetCard (Fin n) n) : s = topIndex n := by
  apply Subtype.ext
  rw [topIndex_val]
  apply Finset.eq_univ_of_card
  simp only [Fintype.card_fin]
  exact s.property
abbrev topBasis (n : ℕ) := (coordinateBasis n).exteriorPower n
def topVolume (n : ℕ) : ⋀[ℂ]^n (CoordinateSpace (Fin n)) :=
  exteriorPower.ιMulti ℂ n coordinate
lemma topBasis_topIndex (n : ℕ) : topBasis n (topIndex n) = topVolume n := by
  rw [exteriorPower.basis_apply]
  simp only [exteriorPower.ιMulti_family, topIndex, Equiv.symm_apply_apply]
  rfl
def topCoefficient (n : ℕ) : (⋀[ℂ]^n (CoordinateSpace (Fin n))) →ₗ[ℂ] ℂ :=
  (topBasis n).coord (topIndex n)
lemma topCoefficient_topVolume (n : ℕ) : topCoefficient n (topVolume n) = 1 := by
  rw [← topBasis_topIndex]
  change (topBasis n).repr (topBasis n (topIndex n)) (topIndex n) = 1
  rw [Module.Basis.repr_self, Finsupp.single_eq_same]
lemma top_scalar (n : ℕ) (x : ⋀[ℂ]^n (CoordinateSpace (Fin n))) :
    x = topCoefficient n x • topVolume n := by
  classical
  have hsum : (∑ s : Set.powersetCard (Fin n) n,
      (topBasis n).repr x s • topBasis n s) =
      (topBasis n).repr x (topIndex n) • topBasis n (topIndex n) := by
    apply Finset.sum_eq_single (topIndex n)
    · intro s _ hs; exact (hs (topIndex_unique n s)).elim
    · simp
  calc
    x = ∑ s, (topBasis n).repr x s • topBasis n s := ((topBasis n).sum_repr x).symm
    _ = _ := hsum
    _ = _ := by rw [topBasis_topIndex]; rfl
lemma homogeneous_mul {I : Type*} {n m : ℕ} {x y : CoordinateAlgebra I}
    (hx : x ∈ ⋀[ℂ]^n (CoordinateSpace I)) (hy : y ∈ ⋀[ℂ]^m (CoordinateSpace I)) :
    x*y ∈ ⋀[ℂ]^(n+m) (CoordinateSpace I) := by
  change _ ∈ (ExteriorAlgebra.ι ℂ).range^(n+m)
  rw [pow_add]
  exact Submodule.mul_mem_mul hx hy
lemma homogeneous_pow {I : Type*} {n : ℕ} {x : CoordinateAlgebra I}
    (hx : x ∈ ⋀[ℂ]^n (CoordinateSpace I)) (m : ℕ) :
    x^m ∈ ⋀[ℂ]^(n*m) (CoordinateSpace I) := by
  induction m with
  | zero => simp [ExteriorAlgebra.exteriorPower]
  | succ m ih =>
    rw [pow_succ, Nat.mul_succ]
    exact homogeneous_mul ih hx
def pfaffian (m : ℕ) (B : Fin (2*m) → Fin (2*m) → ℂ) : ℂ :=
  topCoefficient (2*m) ⟨(m.factorial : ℂ)⁻¹ • (twoForm B)^m,
    Submodule.smul_mem _ _ (homogeneous_pow (twoForm_mem B) m)⟩
lemma topVolume_map_perm (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    exteriorPower.map n (coordinateMap σ) (topVolume n) =
      σ.sign • topVolume n := by
  simp only [topVolume, exteriorPower.map_apply_ιMulti]
  have he : (coordinateMap σ) ∘ coordinate = coordinate ∘ σ := by
    funext i
    exact coordinateMap_coordinate _ _
  rw [he]
  exact (exteriorPower.ιMulti ℂ n).map_perm coordinate σ
lemma topCoefficient_map_perm (n : ℕ) (σ : Equiv.Perm (Fin n))
    (x : ⋀[ℂ]^n (CoordinateSpace (Fin n))) :
    topCoefficient n (exteriorPower.map n (coordinateMap σ) x) =
      σ.sign • topCoefficient n x := by
  conv_lhs => rw [top_scalar n x]
  rw [map_smul, topVolume_map_perm]
  simp only [Units.smul_def, map_zsmul, map_smul, topCoefficient_topVolume, smul_eq_mul]
  ring
end
lemma exteriorMap_coe {M N : Type*} [AddCommGroup M] [Module ℂ M]
    [AddCommGroup N] [Module ℂ N] (n : ℕ) (f : M →ₗ[ℂ] N) (x : ⋀[ℂ]^n M) :
    (exteriorPower.map n f x : ExteriorAlgebra ℂ N) =
      ExteriorAlgebra.map f (x : ExteriorAlgebra ℂ M) := by
  have he : (⋀[ℂ]^n N).subtype.comp (exteriorPower.map n f) =
      (ExteriorAlgebra.map f).toLinearMap.comp (⋀[ℂ]^n M).subtype := by
    apply exteriorPower.linearMap_ext
    ext v
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
      Submodule.subtype_apply, AlgHom.toLinearMap_apply, exteriorPower.map_apply_ιMulti,
      exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.map_apply_ιMulti]
  exact LinearMap.congr_fun he x
def multiplyVector {I : Type*} (n : ℕ) (v : CoordinateSpace I) :
    (⋀[ℂ]^n (CoordinateSpace I)) →ₗ[ℂ] ⋀[ℂ]^(n+1) (CoordinateSpace I) where
  toFun x := ⟨ExteriorAlgebra.ι ℂ v * x, by
    change _ ∈ (ExteriorAlgebra.ι ℂ).range ^ (n+1)
    rw [pow_succ']
    exact Submodule.mul_mem_mul (LinearMap.mem_range.mpr ⟨v, rfl⟩) x.property⟩
  map_add' x y := by apply Subtype.ext; exact mul_add _ _ _
  map_smul' a x := by apply Subtype.ext; exact mul_smul_comm _ _ _
@[simp] lemma multiplyVector_coe {I : Type*} (n : ℕ) (v : CoordinateSpace I)
    (x : ⋀[ℂ]^n (CoordinateSpace I)) :
    (multiplyVector n v x : CoordinateAlgebra I) = ExteriorAlgebra.ι ℂ v * x := rfl
def insertCoordinate {n : ℕ} (i : Fin (n+1)) :
    (⋀[ℂ]^n (CoordinateSpace (Fin n))) →ₗ[ℂ] ⋀[ℂ]^(n+1) (CoordinateSpace (Fin (n+1))) :=
  (multiplyVector n (coordinate i)).comp (exteriorPower.map n (coordinateMap i.succAbove))
lemma insertCoordinate_topVolume {n : ℕ} (i : Fin (n+1)) :
    insertCoordinate i (topVolume n) = (-1 : ℂ)^i.val • topVolume (n+1) := by
  apply Subtype.ext
  simp only [insertCoordinate, LinearMap.comp_apply, multiplyVector_coe,
    exteriorMap_coe, topVolume, exteriorPower.ιMulti_apply_coe,
    ExteriorAlgebra.map_apply_ιMulti, Submodule.coe_smul]
  have he : (coordinateMap i.succAbove) ∘ coordinate = fun j => coordinate (i.succAbove j) := by
    funext j
    exact coordinateMap_coordinate _ _
  rw [he]
  have hi : i.insertNth (coordinate i) (fun j => coordinate (i.succAbove j)) = coordinate := by
    exact Fin.insertNth_eq_iff.mpr ⟨rfl, rfl⟩
  have hh := (ExteriorAlgebra.ιMulti ℂ (n+1)).neg_one_pow_smul_map_insertNth i
    (coordinate i) (fun j => coordinate (i.succAbove j))
  rw [hi, ← Int.cast_smul_eq_zsmul ℂ] at hh
  simpa only [ExteriorAlgebra.ιMulti_succ_apply, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.vecTail, Function.comp_def, Int.cast_pow, Int.cast_neg, Int.cast_one] using hh.symm
lemma topCoefficient_insertCoordinate {n : ℕ} (i : Fin (n+1))
    (x : ⋀[ℂ]^n (CoordinateSpace (Fin n))) :
    topCoefficient (n+1) (insertCoordinate i x) = (-1 : ℂ)^i.val * topCoefficient n x := by
  conv_lhs => rw [top_scalar n x]
  rw [map_smul, insertCoordinate_topVolume, map_smul, map_smul, topCoefficient_topVolume]
  simp only [smul_eq_mul, one_mul, mul_comm]
def pfaffianForm {I : Type*} [Fintype I] (m : ℕ) (B : I → I → ℂ) :
    ⋀[ℂ]^(2*m) (CoordinateSpace I) :=
  ⟨(m.factorial : ℂ)⁻¹ • (twoForm B)^m,
    Submodule.smul_mem _ _ (homogeneous_pow (twoForm_mem B) m)⟩
def detectorForm {I : Type*} [Fintype I] (m : ℕ) (B : I → I → ℂ) :
    ⋀[ℂ]^(2*m+1) (CoordinateSpace I) :=
  multiplyVector (2*m) (coordinateVector (fun _ => 1)) (pfaffianForm m B)
def detector (m : ℕ) (B : Fin (2*m+1) → Fin (2*m+1) → ℂ) : ℂ :=
  topCoefficient (2*m+1) (detectorForm m B)
lemma detector_lift_independent (m : ℕ)
    (B : Fin (2*m+1) → Fin (2*m+1) → ℂ) (r : Fin (2*m+1) → ℂ) :
    detector m (fun i j => B i j + r j - r i) = detector m B := by
  apply congrArg (topCoefficient (2*m+1))
  apply Subtype.ext
  exact detector_form_lift_independent B r m
lemma pfaffianForm_map {I J : Type*} [Fintype I] [Fintype J] (f : I ≃ J)
    (m : ℕ) (B : J → J → ℂ) :
    exteriorPower.map (2*m) (coordinateMap f) (pfaffianForm m (fun i j => B (f i) (f j))) =
      pfaffianForm m B := by
  apply Subtype.ext
  simp only [exteriorMap_coe, pfaffianForm, map_smul, map_pow, twoForm_map]
lemma detectorForm_map {I J : Type*} [Fintype I] [Fintype J] (f : I ≃ J)
    (m : ℕ) (B : J → J → ℂ) :
    exteriorPower.map (2*m+1) (coordinateMap f) (detectorForm m (fun i j => B (f i) (f j))) =
      detectorForm m B := by
  apply Subtype.ext
  simp only [exteriorMap_coe, detectorForm, multiplyVector_coe, map_mul,
    ExteriorAlgebra.map_apply_ι, coordinateMap_vector, pfaffianForm, map_smul, map_pow, twoForm_map]
  rfl
lemma pfaffian_perm (m : ℕ) (B : Fin (2*m) → Fin (2*m) → ℂ) (σ : Equiv.Perm (Fin (2*m))) :
    pfaffian m (fun i j => B (σ i) (σ j)) = σ.sign • pfaffian m B := by
  have he := congrArg (topCoefficient (2*m)) (pfaffianForm_map σ m B)
  rw [topCoefficient_map_perm] at he
  change σ.sign • pfaffian m (fun i j => B (σ i) (σ j)) = pfaffian m B at he
  rw [← he, smul_smul, Int.units_mul_self, one_smul]
lemma detector_perm (m : ℕ) (B : Fin (2*m+1) → Fin (2*m+1) → ℂ)
    (σ : Equiv.Perm (Fin (2*m+1))) :
    detector m (fun i j => B (σ i) (σ j)) = σ.sign • detector m B := by
  have he := congrArg (topCoefficient (2*m+1)) (detectorForm_map σ m B)
  rw [topCoefficient_map_perm] at he
  change σ.sign • detector m (fun i j => B (σ i) (σ j)) = detector m B at he
  rw [← he, smul_smul, Int.units_mul_self, one_smul]
end BassTrace.Detector
end
end OAI

end

section
-- OAI.RingTheory.BassTrace.PfaffianDetector
namespace OAI
noncomputable section
namespace BassTrace
open Set MeasureTheory
open Finset MeasureTheory intervalIntegral
namespace Detector
open scoped BigOperators
lemma rawTwoForm_map {I J : Type*} [Fintype I] (f : I → J) (B : I → I → ℂ) :
    ExteriorAlgebra.map (coordinateMap f) (rawTwoForm B) =
      ∑ i, ∑ j, B i j • (ExteriorAlgebra.ι ℂ (coordinate (f i)) *
        ExteriorAlgebra.ι ℂ (coordinate (f j))) := by
  simp only [rawTwoForm, map_sum, map_smul, map_mul,
    ExteriorAlgebra.map_apply_ι, coordinateMap_coordinate]
lemma twoForm_row {n : ℕ} (B : Fin (n+1) → Fin (n+1) → ℂ)
    (hB : ∀ i j, B i j = -B j i) (i : Fin (n+1)) :
    twoForm B =
      ExteriorAlgebra.map (coordinateMap i.succAbove)
        (twoForm (fun k l => B (i.succAbove k) (i.succAbove l))) +
      ExteriorAlgebra.ι ℂ (coordinate i) * ExteriorAlgebra.ι ℂ (coordinateVector (B i)) := by
  let a (k l : Fin (n+1)) : CoordinateAlgebra (Fin (n+1)) :=
    B k l • (ExteriorAlgebra.ι ℂ (coordinate k) * ExteriorAlgebra.ι ℂ (coordinate l))
  have ha (k l) : a k l = a l k := by
    dsimp only [a]
    rw [hB k l, ι_mul_ι_neg (coordinate k) (coordinate l), neg_smul, smul_neg, neg_neg]
  have hai : a i i = 0 := by simp only [a, ExteriorAlgebra.ι_sq_zero, smul_zero]
  have hsum : (∑ k, ∑ l, a k l) =
      (∑ k : Fin n, ∑ l : Fin n, a (i.succAbove k) (i.succAbove l)) +
        (∑ l, a i l) + (∑ l, a i l) := by
    rw [Fin.sum_univ_succAbove (fun k => ∑ l, a k l) i]
    have he : (∑ k : Fin n, ∑ l, a (i.succAbove k) l) =
        (∑ k : Fin n, a (i.succAbove k) i) +
          ∑ k : Fin n, ∑ l : Fin n, a (i.succAbove k) (i.succAbove l) := by
      simp_rw [Fin.sum_univ_succAbove (fun l => a (i.succAbove _) l) i]
      rw [Finset.sum_add_distrib]
    rw [he]
    have hr : (∑ k : Fin n, a (i.succAbove k) i) = ∑ l, a i l := by
      conv_rhs => rw [Fin.sum_univ_succAbove (a i) i, hai, zero_add]
      exact Finset.sum_congr rfl fun k _ => ha _ _
    rw [hr]
    abel
  have hrow : (∑ l, a i l) =
      ExteriorAlgebra.ι ℂ (coordinate i) * ExteriorAlgebra.ι ℂ (coordinateVector (B i)) := by
    simp only [coordinateVector, map_sum, map_smul, Finset.mul_sum, mul_smul_comm, a]
  simp only [twoForm, map_smul, rawTwoForm_map]
  change (2 : ℂ)⁻¹ • (∑ k, ∑ l, a k l) = _
  rw [hsum, hrow]
  change (2 : ℂ)⁻¹ • (_ + _ + _) = (2 : ℂ)⁻¹ •
    (∑ k : Fin n, ∑ l : Fin n, a (i.succAbove k) (i.succAbove l)) + _
  module
lemma multiplyVector_pfaffian_minor (m : ℕ)
    (B : Fin (2*m+1) → Fin (2*m+1) → ℂ) (hB : ∀ i j, B i j = -B j i)
    (i : Fin (2*m+1)) :
    multiplyVector (2*m) (coordinate i) (pfaffianForm m B) =
      insertCoordinate i (pfaffianForm m (fun k l => B (i.succAbove k) (i.succAbove l))) := by
  apply Subtype.ext
  simp only [multiplyVector_coe, insertCoordinate, LinearMap.comp_apply, exteriorMap_coe,
    pfaffianForm, map_smul, map_pow]
  rw [twoForm_row B hB i, mul_smul_comm, mul_smul_comm]
  congr 1
  apply gauge_invariance
  have h := (exteriorPower.map 2 (coordinateMap i.succAbove)
    (⟨twoForm (fun k l => B (i.succAbove k) (i.succAbove l)), twoForm_mem _⟩ :
      ⋀[ℂ]^2 (CoordinateSpace (Fin (2*m))))).property
  simpa only [exteriorMap_coe] using h
lemma detector_pfaffian_sum (m : ℕ)
    (B : Fin (2*m+1) → Fin (2*m+1) → ℂ) (hB : ∀ i j, B i j = -B j i) :
    detector m B = ∑ i : Fin (2*m+1), (-1 : ℂ)^i.val *
      pfaffian m (fun k l => B (i.succAbove k) (i.succAbove l)) := by
  have he : detectorForm m B = ∑ i : Fin (2*m+1),
      multiplyVector (2*m) (coordinate i) (pfaffianForm m B) := by
    apply Subtype.ext
    simp only [detectorForm, multiplyVector_coe, Submodule.coe_sum, coordinateVector,
      one_smul, map_sum, Finset.sum_mul]
  unfold detector
  rw [he, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [multiplyVector_pfaffian_minor m B hB i, topCoefficient_insertCoordinate]
  rfl
end Detector
namespace Oriented
open scoped BigOperators
variable {Y A : Type*} [AddCommGroup A] [Module ℂ A]
instance {n : ℕ} : CoeFun (AltFunction Y n A) (fun _ => (Fin n → Y) → A) :=
  ⟨AltFunction.toFun⟩
variable [LinearOrder Y]
end Oriented
namespace Detector
open scoped BigOperators
lemma scalar_alt_zero {Y : Type*} {n : ℕ} (f : (Fin n → Y) → ℂ)
    (hf : ∀ v (σ : Equiv.Perm (Fin n)), f (v ∘ σ) = σ.sign • f v)
    (v : Fin n → Y) (hv : ¬ Function.Injective v) : f v = 0 := by
  classical
  obtain ⟨i, j, hvij, hij⟩ := Function.not_injective_iff.mp hv
  have he : v ∘ Equiv.swap i j = v := by
    funext k
    by_cases hki : k = i
    · subst k; simp [hvij]
    by_cases hkj : k = j
    · subst k; simp [hvij]
    simp [Equiv.swap_apply_of_ne_of_ne hki hkj]
  have hh := hf v (Equiv.swap i j)
  rw [he, Equiv.Perm.sign_swap hij] at hh
  change f v = (-1 : ℤ) • f v at hh
  have hn : f v = - f v := by simpa only [neg_one_zsmul] using hh
  linear_combination (1 / 2 : ℂ) * hn
def pfaffianAlt {Y : Type*} (m : ℕ) (β : Y → Y → ℂ) :
    Oriented.AltFunction Y (2*m) ℂ where
  toFun v := pfaffian m (fun i j => β (v i) (v j))
  perm v σ := pfaffian_perm m (fun i j => β (v i) (v j)) σ
  zero v hv := scalar_alt_zero (fun w => pfaffian m (fun i j => β (w i) (w j)))
    (fun w σ => pfaffian_perm m (fun i j => β (w i) (w j)) σ) v hv
def detectorAlt {Y : Type*} (m : ℕ) (β : Y → Y → ℂ) :
    Oriented.AltFunction Y (2*m+1) ℂ where
  toFun v := detector m (fun i j => β (v i) (v j))
  perm v σ := detector_perm m (fun i j => β (v i) (v j)) σ
  zero v hv := scalar_alt_zero (fun w => detector m (fun i j => β (w i) (w j)))
    (fun w σ => detector_perm m (fun i j => β (w i) (w j)) σ) v hv
open scoped BigOperators
open Oriented ChainHomotopy
variable {Y : Type*} [LinearOrder Y]
def cocycle (m : ℕ) (β : Y → Y → ℂ) : Degree Y (2*m+1) →ₗ[ℂ] ℂ :=
  (detectorAlt m β).lift
lemma cocycle_wedge (m : ℕ) (β : Y → Y → ℂ) (v : Fin (2*m+1) → Y) :
    cocycle m β (wedge (2*m+1) v) = detector m (fun i j => β (v i) (v j)) :=
  (detectorAlt m β).lift_wedge v
lemma cocycle_eq_coboundary (m : ℕ) (β : Y → Y → ℂ)
    (hβ : ∀ y z, β y z = -β z y) :
    cocycle m β = (pfaffianAlt m β).lift.comp (d (2*m)) := by
  apply linearMap_ext_wedge
  intro v
  rw [cocycle_wedge, detector_pfaffian_sum m _ (fun i j => hβ (v i) (v j))]
  simp only [LinearMap.comp_apply, d_wedge, map_sum, map_smul,
    AltFunction.lift_wedge, smul_eq_mul]
  rfl
lemma cocycle_closed (m : ℕ) (β : Y → Y → ℂ)
    (hβ : ∀ y z, β y z = -β z y) (x : Degree Y (2*m+2)) :
    cocycle m β (d (2*m+1) x) = 0 := by
  rw [cocycle_eq_coboundary m β hβ, LinearMap.comp_apply, d_square, map_zero]
end Detector
end BassTrace
end
end OAI

end

section
-- OAI.RingTheory.BassTrace.RelativeExponents
namespace OAI
noncomputable section
namespace BassTrace
open Set MeasureTheory
open Finset MeasureTheory intervalIntegral
namespace RelativeExponents
lemma exists_affine_function {L P : Type*} [Group L] [MulAction L P]
    (χ : L → ℝ) (hχ : ∀ a b, χ (a*b) = χ a + χ b)
    (hstab : ∀ (a : L) (p : P), a • p = p → χ a = 0) :
    ∃ B : P → ℝ, ∀ (a : L) (p : P), B (a • p) = B p + χ a := by
  classical
  let q (p : P) : MulAction.orbitRel.Quotient L P := Quotient.mk _ p
  have ht (p : P) : ∃ a : L, a • (q p).out = p := by
    exact Quotient.exact (Quotient.out_eq (q p)).symm
  let t (p : P) : L := (ht p).choose
  have htp (p : P) : t p • (q p).out = p := (ht p).choose_spec
  have hq (a : L) (p : P) : q (a • p) = q p := Quotient.sound ⟨a, rfl⟩
  have h1 : χ 1 = 0 := by have hh := hχ 1 1; simpa using hh
  have hinv (a : L) : χ a⁻¹ = -χ a := by
    have hh := hχ a⁻¹ a
    rw [inv_mul_cancel, h1] at hh
    linarith
  refine ⟨fun p => χ (t p), ?_⟩
  intro a p
  have he : ((t (a • p))⁻¹ * (a * t p)) • (q p).out = (q p).out := by
    rw [mul_smul, mul_smul, htp]
    have hr := htp (a • p)
    rw [hq] at hr
    calc
      _ = (t (a • p))⁻¹ • (t (a • p) • (q p).out) := congrArg _ hr.symm
      _ = _ := inv_smul_smul _ _
  have hz := hstab _ _ he
  rw [hχ, hχ, hinv] at hz
  linarith
variable {G : Type*} [Group G]
abbrev Positions (g : G) :=
  (Multiplicative ℤ × Multiplicative ℤ) × Subgroup.centralizer ({g} : Set G)
lemma centralizer_commutes (g : G) (c : Subgroup.centralizer ({g} : Set G)) :
    Commute g (c : G) :=
  (Subgroup.mem_centralizer_singleton_iff.mp c.property).symm
def positionHom (g : G) : Positions g →* G × G where
  toFun a := (g ^ Multiplicative.toAdd a.1.1 * a.2,
    g ^ Multiplicative.toAdd a.1.2 * a.2)
  map_one' := by simp
  map_mul' a b := by
    apply Prod.ext
    · change g ^ (Multiplicative.toAdd a.1.1 + Multiplicative.toAdd b.1.1) *
          ((a.2 : G) * b.2) = (g ^ Multiplicative.toAdd a.1.1 * a.2) *
          (g ^ Multiplicative.toAdd b.1.1 * b.2)
      rw [zpow_add]
      have hc := (centralizer_commutes g a.2).symm.zpow_right
        (Multiplicative.toAdd b.1.1)
      simp only [mul_assoc]
      rw [← mul_assoc (a.2 : G), hc.eq, mul_assoc]
    · change g ^ (Multiplicative.toAdd a.1.2 + Multiplicative.toAdd b.1.2) *
          ((a.2 : G) * b.2) = (g ^ Multiplicative.toAdd a.1.2 * a.2) *
          (g ^ Multiplicative.toAdd b.1.2 * b.2)
      rw [zpow_add]
      have hc := (centralizer_commutes g a.2).symm.zpow_right
        (Multiplicative.toAdd b.1.2)
      simp only [mul_assoc]
      rw [← mul_assoc (a.2 : G), hc.eq, mul_assoc]
def character (g : G) (a : Positions g) : ℝ :=
  ((Multiplicative.toAdd a.1.2 : ℤ) : ℝ) - ((Multiplicative.toAdd a.1.1 : ℤ) : ℝ)
lemma character_mul (g : G) (a b : Positions g) :
    character g (a*b) = character g a + character g b := by
  change (((Multiplicative.toAdd a.1.2 + Multiplicative.toAdd b.1.2 : ℤ) : ℝ) -
    ((Multiplicative.toAdd a.1.1 + Multiplicative.toAdd b.1.1 : ℤ) : ℝ)) = _
  simp only [character, Int.cast_add]
  ring
theorem exists_beta (g : G) (hg : ¬ IsOfFinOrder g) :
    ∃ β : G → G → ℝ,
      (∀ h k, β k h = -β h k) ∧
      (∀ (c : Subgroup.centralizer ({g} : Set G)) h k,
        β (c*h) (c*k) = β h k) ∧
      (∀ (r s : ℤ) h k, β (g^r*h) (g^s*k) = β h k + s - r) := by
  let : MulAction (Positions g) (G × G) := MulAction.compHom (G × G) (positionHom g)
  have hstab (a : Positions g) (p : G × G) (h : a • p = p) : character g a = 0 := by
    have hleft := congrArg Prod.fst h
    have hright := congrArg Prod.snd h
    change (g ^ Multiplicative.toAdd a.1.1 * a.2) * p.1 = p.1 at hleft
    change (g ^ Multiplicative.toAdd a.1.2 * a.2) * p.2 = p.2 at hright
    have hl : g ^ Multiplicative.toAdd a.1.1 * a.2 = 1 := by simpa only [mul_eq_right] using hleft
    have hr : g ^ Multiplicative.toAdd a.1.2 * a.2 = 1 := by simpa only [mul_eq_right] using hright
    have he : Multiplicative.toAdd a.1.1 = Multiplicative.toAdd a.1.2 :=
      injective_zpow_iff_not_isOfFinOrder.mpr hg (mul_right_cancel (hl.trans hr.symm))
    simp [character, he]
  obtain ⟨B, hB⟩ := exists_affine_function (character g) (character_mul g) hstab
  have hBc (c : Subgroup.centralizer ({g} : Set G)) (h k : G) :
      B (c*h,c*k) = B (h,k) := by
    have he := hB ((1,1),c) (h,k)
    simpa [positionHom, MulAction.compHom_smul_def, character] using he
  have hBp (r s : ℤ) (h k : G) : B (g^r*h,g^s*k) = B (h,k) + s - r := by
    have he := hB ((Multiplicative.ofAdd r,Multiplicative.ofAdd s),1) (h,k)
    simpa [positionHom, MulAction.compHom_smul_def, character, sub_eq_add_neg, add_assoc] using he
  refine ⟨fun h k => (B (h,k) - B (k,h))/2, ?_, ?_, ?_⟩
  · intro h k; ring
  · intro c h k; dsimp only; rw [hBc, hBc]
  · intro r s h k; dsimp only; rw [hBp, hBp]; ring
end RelativeExponents
namespace Detector
section
open scoped BigOperators
open Oriented ChainHomotopy
variable {G : Type*} [Group G]
def Vertex (g : G) := Quotient (QuotientGroup.rightRel (Subgroup.zpowers g))
def project (g : G) (h : G) : Vertex g := Quotient.mk _ h
def sectionLift (g : G) (y : Vertex g) : G := y.out
lemma project_sectionLift (g : G) (y : Vertex g) :
    project g (sectionLift g y) = y := Quotient.out_eq y
lemma project_eq_iff (g h k : G) :
    project g h = project g k ↔ ∃ r : ℤ, g^r*h = k := by
  constructor
  · intro he
    have hr := QuotientGroup.rightRel_apply.mp (Quotient.exact he)
    obtain ⟨r, hr⟩ := Subgroup.mem_zpowers_iff.mp hr
    exact ⟨r, (eq_mul_inv_iff_mul_eq.mp hr)⟩
  · rintro ⟨r, rfl⟩
    apply Quotient.sound
    apply QuotientGroup.rightRel_apply.mpr
    simp only [mul_inv_cancel_right]
    exact (Subgroup.zpowers g).zpow_mem (Subgroup.mem_zpowers g) r
lemma exists_section_power (g h : G) :
    ∃ r : ℤ, g^r*h = sectionLift g (project g h) := by
  apply (project_eq_iff g _ _).mp
  exact (project_sectionLift g _).symm
def centralizerAct (g : G) (c : Subgroup.centralizer ({g} : Set G)) :
    Vertex g → Vertex g := Quotient.lift (fun h => project g (c*h)) (by
  intro h k hhk
  obtain ⟨r, hr⟩ := (project_eq_iff g h k).mp (Quotient.sound hhk)
  apply (project_eq_iff g _ _).mpr
  refine ⟨r, ?_⟩
  have hc := (RelativeExponents.centralizer_commutes g c).zpow_left r
  rw [← mul_assoc, hc.eq, mul_assoc, hr])
@[simp] lemma centralizerAct_project (g : G)
    (c : Subgroup.centralizer ({g} : Set G)) (h : G) :
    centralizerAct g c (project g h) = project g (c*h) := rfl
lemma centralizerAct_one (g : G) (y : Vertex g) :
    centralizerAct g 1 y = y := by
  induction y using Quotient.inductionOn with | _ h =>
    change project g ((1:G)*h) = project g h
    rw [one_mul]
lemma centralizerAct_mul (g : G) (c d : Subgroup.centralizer ({g} : Set G))
    (y : Vertex g) : centralizerAct g (c*d) y =
      centralizerAct g c (centralizerAct g d y) := by
  induction y using Quotient.inductionOn with | _ h =>
    change project g (((c:G)*d)*h) = project g (c*(d*h))
    rw [mul_assoc]
lemma exists_complex_beta (g : G) (hg : ¬ IsOfFinOrder g) :
    ∃ β : G → G → ℂ,
      (∀ h k, β h k = -β k h) ∧
      (∀ (c : Subgroup.centralizer ({g} : Set G)) h k,
        β (c*h) (c*k) = β h k) ∧
      (∀ (r s : ℤ) h k, β (g^r*h) (g^s*k) = β h k + s - r) := by
  obtain ⟨β, hβ, hc, hl⟩ := RelativeExponents.exists_beta g hg
  refine ⟨fun h k => (β h k : ℂ), ?_, ?_, ?_⟩
  · intro h k
    simpa only [Complex.ofReal_neg] using congrArg Complex.ofReal (hβ k h)
  · intro c h k
    exact congrArg Complex.ofReal (hc c h k)
  · intro r s h k
    simp only [hl, Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_intCast]
lemma detector_section (g : G) (β : G → G → ℂ)
    (hl : ∀ (r s : ℤ) h k, β (g^r*h) (g^s*k) = β h k + s - r)
    (m : ℕ) (h : Fin (2*m+1) → G) :
    detector m (fun i j => β (sectionLift g (project g (h i)))
      (sectionLift g (project g (h j)))) =
      detector m (fun i j => β (h i) (h j)) := by
  choose r hr using fun i => exists_section_power g (h i)
  have hb : (fun i j => β (sectionLift g (project g (h i)))
      (sectionLift g (project g (h j)))) =
      (fun i j => β (h i) (h j) + (r j : ℂ) - (r i : ℂ)) := by
    funext i j
    rw [← hr i, ← hr j, hl]
  rw [hb]
  exact detector_lift_independent m (fun i j => β (h i) (h j)) (fun i => (r i : ℂ))
lemma detector_section_invariant (g : G) (β : G → G → ℂ)
    (hc : ∀ (c : Subgroup.centralizer ({g} : Set G)) h k,
      β (c*h) (c*k) = β h k)
    (hl : ∀ (r s : ℤ) h k, β (g^r*h) (g^s*k) = β h k + s - r)
    (m : ℕ) (c : Subgroup.centralizer ({g} : Set G)) (v : Fin (2*m+1) → Vertex g) :
    detector m (fun i j => β (sectionLift g (centralizerAct g c (v i)))
      (sectionLift g (centralizerAct g c (v j)))) =
      detector m (fun i j => β (sectionLift g (v i)) (sectionLift g (v j))) := by
  have hp (i) : centralizerAct g c (v i) =
      project g (c*sectionLift g (v i)) := by
    rw [← centralizerAct_project, project_sectionLift]
  simp only [hp]
  rw [detector_section g β hl m (fun i => c*sectionLift g (v i))]
  simp only [hc]
end
section
open Oriented ChainHomotopy
variable {G : Type*} [Group G]
def cosetCocycle (g : G) (m : ℕ) (β : G → G → ℂ) :
    Degree (Vertex g) (2*m+1) →ₗ[ℂ] ℂ := by
  classical
  letI : LinearOrder (Vertex g) := linearOrderOfSTO WellOrderingRel
  exact cocycle m (fun y z => β (sectionLift g y) (sectionLift g z))
lemma cosetCocycle_wedge (g : G) (m : ℕ) (β : G → G → ℂ)
    (v : Fin (2*m+1) → Vertex g) :
    cosetCocycle g m β (wedge (2*m+1) v) =
      detector m (fun i j => β (sectionLift g (v i)) (sectionLift g (v j))) := by
  classical
  let : LinearOrder (Vertex g) := linearOrderOfSTO WellOrderingRel
  unfold cosetCocycle
  exact cocycle_wedge _ _ _
lemma cosetCocycle_lifts (g : G) (m : ℕ) (β : G → G → ℂ)
    (hl : ∀ (r s : ℤ) h k, β (g^r*h) (g^s*k) = β h k + s - r)
    (h : Fin (2*m+1) → G) :
    cosetCocycle g m β (wedge (2*m+1) (project g ∘ h)) =
      detector m (fun i j => β (h i) (h j)) := by
  rw [cosetCocycle_wedge]
  exact detector_section g β hl m h
lemma cosetCocycle_closed (g : G) (m : ℕ) (β : G → G → ℂ)
    (hβ : ∀ y z, β y z = -β z y)
    (x : Degree (Vertex g) (2*m+2)) :
    cosetCocycle g m β (d (2*m+1) x) = 0 := by
  classical
  let : LinearOrder (Vertex g) := linearOrderOfSTO WellOrderingRel
  unfold cosetCocycle
  exact cocycle_closed m _ (fun y z => hβ _ _) x
lemma cosetCocycle_invariant (g : G) (m : ℕ) (β : G → G → ℂ)
    (hc : ∀ (c : Subgroup.centralizer ({g} : Set G)) h k,
      β (c*h) (c*k) = β h k)
    (hl : ∀ (r s : ℤ) h k, β (g^r*h) (g^s*k) = β h k + s - r)
    (c : Subgroup.centralizer ({g} : Set G))
    (x : Degree (Vertex g) (2*m+1)) :
    cosetCocycle g m β (relabel (2*m+1) (centralizerAct g c) x) =
      cosetCocycle g m β x := by
  classical
  let : LinearOrder (Vertex g) := linearOrderOfSTO WellOrderingRel
  have he : (cosetCocycle g m β).comp (relabel (2*m+1) (centralizerAct g c)) =
      cosetCocycle g m β := by
    apply linearMap_ext_wedge
    intro v
    simp only [LinearMap.comp_apply, relabel_wedge, cosetCocycle_wedge,
      Function.comp_apply]
    exact detector_section_invariant g β hc hl m c v
  exact LinearMap.congr_fun he x
end
open scoped BigOperators
lemma square_decomposable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (u v : M) :
    (ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R v) *
      (ExteriorAlgebra.ι R u * ExteriorAlgebra.ι R v) = 0 := by
  rw [mul_assoc, ← mul_assoc (ExteriorAlgebra.ι R v), ι_mul_ι_neg v u,
    neg_mul, mul_neg, ← mul_assoc, ← mul_assoc, ExteriorAlgebra.ι_sq_zero,
    zero_mul, zero_mul, neg_zero]
lemma nilpotent_binomial {A : Type*} [Ring A] (b c : A) (hc : Commute c b)
    (hz : c*c = 0) (m : ℕ) :
    (b+c)^(m+1) = b^(m+1) + (m+1) • (c*b^m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hlast : c*b^m*c = 0 := by
      rw [(hc.pow_right m).eq, mul_assoc, hz, mul_zero]
    calc
      (b+c)^(m+1+1) = (b^(m+1)+(m+1) • (c*b^m)) * (b+c) := by
        rw [pow_succ, ih]
      _ = b^(m+1+1) + c*b^(m+1) + (m+1) • (c*b^(m+1)) := by
        rw [add_mul, mul_add, mul_add, smul_mul_assoc, smul_mul_assoc, hlast,
          nsmul_zero, add_zero, ← pow_succ, (hc.pow_right (m+1)).eq.symm]
        simp only [mul_assoc, ← pow_succ]
      _ = b^(m+1+1) + (m+1+1) • (c*b^(m+1)) := by
        simp only [add_nsmul, one_nsmul]
        abel
lemma factorial_cancel (m : ℕ) :
    ((m+1).factorial : ℂ)⁻¹ * (m+1 : ℂ) = (m.factorial : ℂ)⁻¹ := by
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, mul_inv_rev]
  field_simp
lemma normalized_decomposable_update {I : Type*} (b : CoordinateAlgebra I)
    (hb : b ∈ ⋀[ℂ]^2 (CoordinateSpace I)) (u v : CoordinateSpace I) (m : ℕ) :
    ((m+1).factorial : ℂ)⁻¹ • (b+ExteriorAlgebra.ι ℂ u*ExteriorAlgebra.ι ℂ v)^(m+1) =
      ((m+1).factorial : ℂ)⁻¹ • b^(m+1) +
        (m.factorial : ℂ)⁻¹ • (ExteriorAlgebra.ι ℂ u*ExteriorAlgebra.ι ℂ v*b^m) := by
  have hc : Commute (ExteriorAlgebra.ι ℂ u*ExteriorAlgebra.ι ℂ v) b :=
    (ι_commute_degree_two u hb).mul_left (ι_commute_degree_two v hb)
  rw [nilpotent_binomial _ _ hc (square_decomposable u v), smul_add,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  simp only [Nat.cast_add, Nat.cast_one]
  rw [factorial_cancel]
lemma coordinateVector_minor {n : ℕ} (i : Fin (n+1)) :
    coordinateVector (fun _ : Fin (n+1) => (1 : ℂ)) = coordinate i +
      coordinateMap i.succAbove (coordinateVector (fun _ : Fin n => (1 : ℂ))) := by
  simp only [coordinateVector, one_smul, map_sum, coordinateMap_coordinate]
  exact Fin.sum_univ_succAbove coordinate i
lemma coordinateVector_indicator {I : Type*} [Fintype I] [DecidableEq I] (i : I) :
    coordinateVector (fun j => if j = i then (1 : ℂ) else 0) = coordinate i := by
  simp [coordinateVector, ite_smul]
lemma pfaffianForm_lift_basis (m : ℕ)
    (B : Fin (2*m+1+1) → Fin (2*m+1+1) → ℂ)
    (hB : ∀ k l, B k l = -B l k) (i : Fin (2*m+1+1)) :
    pfaffianForm (m+1) (fun k l => B k l + (if l = i then 1 else 0) -
      (if k = i then 1 else 0)) =
      pfaffianForm (m+1) B - insertCoordinate i
        (detectorForm m (fun k l => B (i.succAbove k) (i.succAbove l))) := by
  classical
  apply Subtype.ext
  let b := twoForm (fun k l => B (i.succAbove k) (i.succAbove l))
  let u := coordinateVector (fun _ : Fin (2*m+1+1) => (1 : ℂ))
  let u' := coordinateVector (fun _ : Fin (2*m+1) => (1 : ℂ))
  have hm : ExteriorAlgebra.map (coordinateMap i.succAbove) b ∈
      ⋀[ℂ]^2 (CoordinateSpace (Fin (2*m+1+1))) := by
    have h := (exteriorPower.map 2 (coordinateMap i.succAbove)
      (⟨b, twoForm_mem _⟩ : ⋀[ℂ]^2 (CoordinateSpace (Fin (2*m+1))))).property
    simpa only [exteriorMap_coe] using h
  have hc : ExteriorAlgebra.ι ℂ u * ExteriorAlgebra.ι ℂ (coordinate i) =
      -(ExteriorAlgebra.ι ℂ (coordinate i) *
        ExteriorAlgebra.ι ℂ (coordinateMap i.succAbove u')) := by
    rw [ι_mul_ι_neg, show u = coordinate i + coordinateMap i.succAbove u' from
      coordinateVector_minor i, map_add, mul_add, ExteriorAlgebra.ι_sq_zero, zero_add]
  have hcorr : ExteriorAlgebra.ι ℂ u * ExteriorAlgebra.ι ℂ (coordinate i) * (twoForm B)^m =
      -(ExteriorAlgebra.ι ℂ (coordinate i) *
        (ExteriorAlgebra.ι ℂ (coordinateMap i.succAbove u') *
          (ExteriorAlgebra.map (coordinateMap i.succAbove) b)^m)) := by
    rw [mul_assoc, twoForm_row B hB i, gauge_invariance _ _ hm,
      ← mul_assoc, hc, neg_mul, mul_assoc]
  simp only [pfaffianForm, Submodule.coe_sub, insertCoordinate, LinearMap.comp_apply,
    multiplyVector_coe, exteriorMap_coe, detectorForm, map_mul, map_smul, map_pow,
    ExteriorAlgebra.map_apply_ι]
  rw [twoForm_lift_change B (fun k => if k = i then 1 else 0), coordinateVector_indicator,
    normalized_decomposable_update _ (twoForm_mem B)]
  change _ + (m.factorial : ℂ)⁻¹ •
      (ExteriorAlgebra.ι ℂ u * ExteriorAlgebra.ι ℂ (coordinate i) * (twoForm B)^m) = _
  rw [hcorr, smul_neg, sub_eq_add_neg]
  congr 1
  rw [mul_smul_comm, mul_smul_comm]
lemma pfaffian_lift_basis (m : ℕ)
    (B : Fin (2*m+1+1) → Fin (2*m+1+1) → ℂ)
    (hB : ∀ k l, B k l = -B l k) (i : Fin (2*m+1+1)) :
    pfaffian (m+1) (fun k l => B k l + (if l = i then 1 else 0) -
      (if k = i then 1 else 0)) =
      pfaffian (m+1) B - (-1 : ℂ)^i.val *
        detector m (fun k l => B (i.succAbove k) (i.succAbove l)) := by
  have he := congrArg (topCoefficient (2*(m+1))) (pfaffianForm_lift_basis m B hB i)
  rw [map_sub] at he
  change pfaffian (m+1) _ = pfaffian (m+1) B -
    topCoefficient (2*m+1+1) (insertCoordinate i
      (detectorForm m (fun k l => B (i.succAbove k) (i.succAbove l)))) at he
  rw [topCoefficient_insertCoordinate] at he
  exact he
end Detector
end BassTrace
end
end OAI

end

section
-- OAI.RingTheory.BassTrace.TwistedPaths
namespace OAI
noncomputable section
namespace BassTrace
open Set MeasureTheory
open Finset MeasureTheory intervalIntegral
namespace Detector
open scoped BigOperators
variable {G : Type*} [Group G]
def twistedRotation (g : G) (n : ℕ) (h : Fin (n+1) → G) (i : Fin (n+1)) : G :=
  g ^ (if i = Fin.last n then (1 : ℤ) else 0) * h (finRotate (n+1) i)
lemma finRotate_castSucc {n : ℕ} (i : Fin n) : finRotate (n+1) i.castSucc = i.succ :=
  finRotate_of_lt i.isLt
lemma twistedRotation_castSucc (g : G) (n : ℕ) (h : Fin (n+1) → G) (i : Fin n) :
    twistedRotation g n h i.castSucc = h i.succ := by
  simp [twistedRotation, Fin.castSucc_ne_last]
lemma twistedRotation_last (g : G) (n : ℕ) (h : Fin (n+1) → G) :
    twistedRotation g n h (Fin.last n) = g*h 0 := by
  simp [twistedRotation]
lemma complex_sign_odd (m : ℕ) : (-1 : ℂ)^(2*m+1) = -1 := by
  rw [pow_add, pow_mul]
  norm_num
lemma rotation_pfaffian (m : ℕ) (B : Fin (2*m+1+1) → Fin (2*m+1+1) → ℂ) :
    pfaffian (m+1) (fun i j => B (finRotate _ i) (finRotate _ j)) =
      -pfaffian (m+1) B := by
  refine (pfaffian_perm (m+1) B (finRotate (2*m+1+1))).trans ?_
  change Equiv.Perm.sign (finRotate (2*m+1+1)) • pfaffian (m+1) B = _
  rw [sign_finRotate]
  have he : 2*m+1+1-1 = 2*m+1 := by omega
  rw [he, pow_add, pow_mul]
  norm_num [Units.smul_def]
lemma twisted_pfaffian (g : G) (β : G → G → ℂ)
    (hβ : ∀ x y, β x y = -β y x)
    (hlift : ∀ (r s : ℤ) x y, β (g^r*x) (g^s*y) = β x y + s - r)
    (m : ℕ) (h : Fin (2*m+1+1) → G) :
    pfaffian (m+1) (fun i j => β (twistedRotation g (2*m+1) h i)
        (twistedRotation g (2*m+1) h j)) =
      -pfaffian (m+1) (fun i j => β (h i) (h j)) +
        detector m (fun i j => β (h i.succ) (h j.succ)) := by
  classical
  let B : Fin (2*m+1+1) → Fin (2*m+1+1) → ℂ :=
    fun i j => β (h (finRotate _ i)) (h (finRotate _ j))
  have he : (fun i j => β (twistedRotation g (2*m+1) h i)
      (twistedRotation g (2*m+1) h j)) =
      (fun i j => B i j + (if j = Fin.last (2*m+1) then 1 else 0) -
        (if i = Fin.last (2*m+1) then 1 else 0)) := by
    funext i j
    simp only [twistedRotation, hlift, B, Int.cast_ite, Int.cast_one, Int.cast_zero]
  change pfaffian (m+1) ((fun i j => β (twistedRotation g (2*m+1) h i)
    (twistedRotation g (2*m+1) h j)) : Fin (2*m+1+1) → Fin (2*m+1+1) → ℂ) = _
  rw [he]
  refine (pfaffian_lift_basis m B (fun i j => hβ _ _) (Fin.last (2*m+1))).trans ?_
  have hm : (fun i j => B ((Fin.last (2*m+1)).succAbove i)
      ((Fin.last (2*m+1)).succAbove j)) = (fun i j => β (h i.succ) (h j.succ)) := by
    simp only [B, Fin.succAbove_last, finRotate_castSucc]
  rw [hm, Fin.val_last, complex_sign_odd, neg_one_mul, sub_neg_eq_add]
  exact congrArg (fun z => z + _) (rotation_pfaffian m (fun i j => β (h i) (h j)))
end Detector
namespace Paths
open scoped BigOperators
def weightedSum {A : Type*} (v : A →₀ ℂ) (f : A → ℂ) : ℂ :=
  v.sum fun a z => z*f a
lemma weightedSum_congr {A : Type*} (v : A →₀ ℂ) {f g : A → ℂ}
    (h : ∀ a, f a = g a) : weightedSum v f = weightedSum v g := by
  exact congrArg (weightedSum v) (funext h)
lemma weightedSum_add {A : Type*} (v : A →₀ ℂ) (f g : A → ℂ) :
    weightedSum v (fun a => f a+g a) = weightedSum v f+weightedSum v g := by
  simp only [weightedSum,Finsupp.sum,mul_add,Finset.sum_add_distrib]
lemma weightedSum_neg {A : Type*} (v : A →₀ ℂ) (f : A → ℂ) :
    weightedSum v (fun a => -f a) = -weightedSum v f := by
  simp only [weightedSum,Finsupp.sum,mul_neg,Finset.sum_neg_distrib]
lemma weightedSum_sum {A I : Type*} (v : A →₀ ℂ) (s : Finset I) (f : I → A → ℂ) :
    weightedSum v (fun a => ∑ i ∈ s, f i a) = ∑ i ∈ s, weightedSum v (f i) := by
  simp only [weightedSum,Finsupp.sum,Finset.mul_sum]
  rw [Finset.sum_comm]
lemma weightedSum_const_mul {A : Type*} (v : A →₀ ℂ) (c : ℂ) (f : A → ℂ) :
    weightedSum v (fun a => c*f a) = c*weightedSum v f := by
  simp only [weightedSum,Finsupp.sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring
lemma weightedSum_mapDomain {A B : Type*} (v : A →₀ ℂ) (f : A → B) (p : B → ℂ) :
    weightedSum (v.mapDomain f) p = weightedSum v (p ∘ f) := by
  exact Finsupp.sum_mapDomain_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)
variable {G ι : Type*} [Group G] [Fintype ι]
lemma weightedSum_twist (e : GroupMatrix (G := G) (ι := ι)) (g : G) (n : ℕ)
    (p : Orbit g n → ℂ) :
    weightedSum (pathVector e g n) (p ∘ orbitTwist g n) = weightedSum (pathVector e g n) p := by
  rw [← weightedSum_mapDomain,pathVector_twist]
lemma weightedSum_deleteEntry (e : GroupMatrix (G := G) (ι := ι)) (he : e*e=e)
    (g : G) (n : ℕ) (i : Fin (n+2)) (p : Orbit g n → ℂ) :
    weightedSum (pathVector e g (n+1)) (p ∘ deleteEntry g n i) =
      weightedSum (pathVector e g n) p := by
  rw [← weightedSum_mapDomain,pathVector_deleteEntry e he]
end Paths
namespace Detector
open scoped BigOperators
open BassTrace.Paths
section
variable {G : Type*} [Group G]
lemma twist_eq_twistedRotation (g : G) (n : ℕ) (h : Fin (n+1) → G) :
    twist g n h = twistedRotation g n h := by
  funext i
  induction i using Fin.lastCases with
  | last => simp only [twist_last,twistedRotation_last]
  | cast i => simp only [twist_castSucc,twistedRotation_castSucc]
variable (g : G) (β : G → G → ℂ)
    (hc : ∀ (c : Subgroup.centralizer ({g} : Set G)) h k, β (c*h) (c*k) = β h k)
def orbitPfaffian (m : ℕ) : Orbit g (2*m+1) → ℂ :=
  Quotient.lift (fun h => pfaffian (m+1) (fun i j => β (h i) (h j))) (by
    rintro h k ⟨c,hh⟩
    have hk : k = fun i => c*h i := funext fun i => (hh i).symm
    rw [hk]
    simp only [hc])
def orbitDetector (m : ℕ) : Orbit g (2*m) → ℂ :=
  Quotient.lift (fun h => detector m (fun i j => β (h i) (h j))) (by
    rintro h k ⟨c,hh⟩
    have hk : k = fun i => c*h i := funext fun i => (hh i).symm
    rw [hk]
    simp only [hc])
lemma orbitPfaffian_twist (hβ : ∀ x y, β x y = -β y x)
    (hl : ∀ (r s : ℤ) x y, β (g^r*x) (g^s*y) = β x y+s-r)
    (m : ℕ) (q : Orbit g (2*m+1)) :
    orbitPfaffian g β hc m (orbitTwist g (2*m+1) q) =
      -orbitPfaffian g β hc m q +
        orbitDetector g β hc m (deleteEntry g (2*m) 0 q) := by
  induction q using Quotient.inductionOn with | _ h =>
    change pfaffian (m+1) (fun i j => β (twist g (2*m+1) h i) (twist g (2*m+1) h j)) = _
    rw [twist_eq_twistedRotation,twisted_pfaffian g β hβ hl]
    rfl
variable {ι : Type*} [Fintype ι]
def pfaffianSum (e : GroupMatrix (G := G) (ι := ι)) : ℕ → ℂ
  | 0 => totalWeight e g 0
  | m+1 => weightedSum (pathVector e g (2*m+1)) (orbitPfaffian g β hc m)
def detectorSum (e : GroupMatrix (G := G) (ι := ι)) (m : ℕ) : ℂ :=
  weightedSum (pathVector e g (2*m)) (orbitDetector g β hc m)
lemma pfaffianSum_twist (e : GroupMatrix (G := G) (ι := ι)) (he : e*e=e)
    (hβ : ∀ x y, β x y = -β y x)
    (hl : ∀ (r s : ℤ) x y, β (g^r*x) (g^s*y) = β x y+s-r) (m : ℕ) :
    2*pfaffianSum g β hc e (m+1) = detectorSum g β hc e m := by
  have ht := weightedSum_twist e g (2*m+1) (orbitPfaffian g β hc m)
  have hv : weightedSum (pathVector e g (2*m+1))
      ((orbitPfaffian g β hc m) ∘ orbitTwist g (2*m+1)) =
      -pfaffianSum g β hc e (m+1) + detectorSum g β hc e m := by
    simp only [Function.comp_def]
    rw [weightedSum_congr _ (fun q => orbitPfaffian_twist g β hc hβ hl m q),
      weightedSum_add,weightedSum_neg]
    change -pfaffianSum g β hc e (m+1) + weightedSum _
      (orbitDetector g β hc m ∘ deleteEntry g (2*m) 0) = _
    rw [weightedSum_deleteEntry e he]
    rfl
  change _ = pfaffianSum g β hc e (m+1) at ht
  rw [ht] at hv
  linear_combination hv
end
lemma pfaffian_zero (B : Fin (2*0) → Fin (2*0) → ℂ) : pfaffian 0 B = 1 := by
  have ht : (⟨((0 : ℕ).factorial : ℂ)⁻¹ • (twoForm B)^0,
      Submodule.smul_mem _ _ (homogeneous_pow (twoForm_mem B) 0)⟩ :
      ⋀[ℂ]^(2*0) (CoordinateSpace (Fin (2*0)))) = topVolume 0 := by
    apply Subtype.ext
    simp [topVolume]
  exact (congrArg (topCoefficient 0) ht).trans (topCoefficient_topVolume 0)
lemma detector_zero (B : Fin (2*0+1) → Fin (2*0+1) → ℂ)
    (hB : ∀ i j, B i j = -B j i) : detector 0 B = 1 := by
  rw [detector_pfaffian_sum 0 B hB]
  simp [pfaffian_zero]
lemma alternating_sum_odd (m : ℕ) : ∑ i : Fin (2*m+1), (-1:ℂ)^i.val = 1 := by
  induction m with
  | zero => simp
  | succ m hm =>
    change (∑ i : Fin (2*m+1+1+1), (-1:ℂ)^i.val) = 1
    rw [Fin.sum_univ_castSucc,Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc,Fin.val_last,hm,pow_succ]
    ring
variable {G : Type*} [Group G] (g : G) (β : G → G → ℂ)
    (hc : ∀ (c : Subgroup.centralizer ({g} : Set G)) h k, β (c*h) (c*k) = β h k)
lemma orbitDetector_zero (hβ : ∀ x y, β x y = -β y x) (q : Orbit g 0) :
    orbitDetector g β hc 0 q = 1 := by
  induction q using Quotient.inductionOn with | _ h =>
    exact detector_zero _ (fun i j => hβ _ _)
lemma orbitDetector_succ (hβ : ∀ x y, β x y = -β y x) (m : ℕ)
    (q : Orbit g (2*(m+1))) : orbitDetector g β hc (m+1) q =
      ∑ i : Fin (2*(m+1)+1), (-1:ℂ)^i.val *
        orbitPfaffian g β hc m (deleteEntry g (2*m+1) i q) := by
  induction q using Quotient.inductionOn with | _ h =>
    exact detector_pfaffian_sum (m+1) _ (fun i j => hβ _ _)
variable {ι : Type*} [Fintype ι]
lemma detectorSum_eq_pfaffianSum (e : GroupMatrix (G := G) (ι := ι)) (he : e*e=e)
    (hβ : ∀ x y, β x y = -β y x) (m : ℕ) :
    detectorSum g β hc e m = pfaffianSum g β hc e m := by
  cases m with
  | zero =>
    unfold detectorSum
    rw [weightedSum_congr _ (orbitDetector_zero g β hc hβ)]
    simp only [weightedSum,mul_one,pfaffianSum,totalWeight]
  | succ m =>
    unfold detectorSum
    rw [weightedSum_congr _ (orbitDetector_succ g β hc hβ m),weightedSum_sum]
    simp only [weightedSum_const_mul]
    have hv (i : Fin (2*(m+1)+1)) : weightedSum (pathVector e g (2*(m+1)))
        (fun q => orbitPfaffian g β hc m (deleteEntry g (2*m+1) i q)) =
        pfaffianSum g β hc e (m+1) := by
      exact weightedSum_deleteEntry e he g (2*m+1) i (orbitPfaffian g β hc m)
    simp_rw [hv]
    rw [← Finset.sum_mul,alternating_sum_odd,one_mul]
lemma pfaffianSum_recurrence (e : GroupMatrix (G := G) (ι := ι)) (he : e*e=e)
    (hβ : ∀ x y, β x y = -β y x)
    (hl : ∀ (r s : ℤ) x y, β (g^r*x) (g^s*y) = β x y+s-r) (m : ℕ) :
    2*pfaffianSum g β hc e (m+1) = pfaffianSum g β hc e m := by
  rw [pfaffianSum_twist g β hc e he hβ hl,detectorSum_eq_pfaffianSum g β hc e he hβ]
lemma pfaffianSum_value (e : GroupMatrix (G := G) (ι := ι)) (he : e*e=e)
    (hβ : ∀ x y, β x y = -β y x)
    (hl : ∀ (r s : ℤ) x y, β (g^r*x) (g^s*y) = β x y+s-r) (m : ℕ) :
    pfaffianSum g β hc e m = (2:ℂ)⁻¹^m*totalWeight e g 0 := by
  induction m with
  | zero => simp [pfaffianSum]
  | succ m hm =>
    have hr := pfaffianSum_recurrence g β hc e he hβ hl m
    rw [hm] at hr
    rw [pow_succ]
    linear_combination (1/2:ℂ)*hr
lemma detectorSum_value (e : GroupMatrix (G := G) (ι := ι)) (he : e*e=e)
    (hβ : ∀ x y, β x y = -β y x)
    (hl : ∀ (r s : ℤ) x y, β (g^r*x) (g^s*y) = β x y+s-r) (m : ℕ) :
    detectorSum g β hc e m = (2:ℂ)⁻¹^m*totalWeight e g 0 := by
  rw [detectorSum_eq_pfaffianSum g β hc e he hβ,pfaffianSum_value g β hc e he hβ hl]
end Detector
end BassTrace
end
end OAI

end

section
-- OAI.RingTheory.BassTrace.PathComplex
namespace OAI
noncomputable section
open Set MeasureTheory
open Finset MeasureTheory intervalIntegral
namespace BassTrace.PathChains
section
open scoped BigOperators
open Oriented ChainHomotopy Paths Detector
variable {G : Type*} [Group G]
def relations (g : G) (n : ℕ) : Submodule ℂ (Degree (Vertex g) n) :=
  Submodule.span ℂ (Set.range fun p : Subgroup.centralizer ({g} : Set G) ×
    Degree (Vertex g) n => relabel n (centralizerAct g p.1) p.2-p.2)
abbrev Coinvariant (g : G) (n : ℕ) := Degree (Vertex g) n ⧸ relations g n
def quotientMap (g : G) (n : ℕ) : Degree (Vertex g) n →ₗ[ℂ] Coinvariant g n :=
  (relations g n).mkQ
lemma quotientMap_invariant (g : G) (n : ℕ)
    (c : Subgroup.centralizer ({g} : Set G)) (x : Degree (Vertex g) n) :
    quotientMap g n (relabel n (centralizerAct g c) x) = quotientMap g n x := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  exact (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.subset_span ⟨(c,x),rfl⟩)
lemma d_relations (g : G) (n : ℕ) {x : Degree (Vertex g) (n+1)}
    (hx : x ∈ relations g (n+1)) : d n x ∈ relations g n := by
  classical
  let : LinearOrder (Vertex g) := linearOrderOfSTO WellOrderingRel
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨c,y⟩,rfl⟩ := hx
    rw [map_sub,d_relabel]
    exact Submodule.subset_span ⟨(c,d n y),rfl⟩
  | zero => simp
  | add x y _ _ hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
  | smul a x _ hx => simpa only [map_smul] using Submodule.smul_mem _ a hx
def quotientD (g : G) (n : ℕ) : Coinvariant g (n+1) →ₗ[ℂ] Coinvariant g n :=
  (relations g (n+1)).liftQ ((quotientMap g n).comp (d n)) (by
    intro x hx
    change quotientMap g n (d n x) = 0
    exact (Submodule.Quotient.mk_eq_zero _).mpr (d_relations g n hx))
@[simp] lemma quotientD_mk (g : G) (n : ℕ) (x : Degree (Vertex g) (n+1)) :
    quotientD g n (quotientMap g (n+1) x) = quotientMap g n (d n x) := rfl
def pathProjection (g : G) (n : ℕ) : Orbit g n → Coinvariant g (n+1) :=
  Quotient.lift (fun h => quotientMap g (n+1) (wedge (n+1) (project g ∘ h))) (by
    intro h k hhk
    obtain ⟨c,hc⟩ := hhk
    have he : k = fun i => (c:G)*h i := funext fun i => (hc i).symm
    rw [he]
    simpa only [relabel_wedge, Function.comp_def, centralizerAct_project] using
      (quotientMap_invariant g (n+1) c (wedge (n+1) (project g ∘ h))).symm)
@[simp] lemma pathProjection_mk (g : G) (n : ℕ) (h : Fin (n+1) → G) :
    pathProjection g n (Quotient.mk _ h) =
      quotientMap g (n+1) (wedge (n+1) (project g ∘ h)) := rfl
lemma projected_twist (g : G) (n : ℕ) (h : Fin (n+1) → G) :
    project g ∘ twist g n h = (project g ∘ h) ∘ finRotate (n+1) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Function.comp_apply,twist_last,finRotate_last]
    apply (project_eq_iff g _ _).mpr
    exact ⟨-1,by simp [← mul_assoc]⟩
  · simp only [Function.comp_apply,twist_castSucc,rotate_castSucc]
lemma pathProjection_twist (g : G) (n : ℕ) (q : Orbit g n) :
    pathProjection g n (orbitTwist g n q) = (-1:ℂ)^n • pathProjection g n q := by
  induction q using Quotient.inductionOn with | _ h =>
    change quotientMap g (n+1) (wedge (n+1) (project g ∘ twist g n h)) = _
    rw [projected_twist,wedge_perm]
    simp [sign_finRotate,Units.smul_def,← Int.cast_smul_eq_zsmul ℂ]
variable {ι : Type*} [Fintype ι]
def pathChain (e : GroupMatrix (G := G) (ι := ι)) (g : G) (n : ℕ) :
    Coinvariant g (n+1) :=
  Finsupp.linearCombination ℂ (pathProjection g n) (pathVector e g n)
lemma pathChain_twist (e : GroupMatrix (G := G) (ι := ι)) (g : G) (n : ℕ) :
    pathChain e g n = (-1:ℂ)^n • pathChain e g n := by
  have hv := congrArg (Finsupp.linearCombination ℂ (pathProjection g n))
    (pathVector_twist e g n)
  rw [Finsupp.linearCombination_apply,Finsupp.sum_mapDomain_index] at hv
  swap
  · intro q; simp
  swap
  · intro q a b; exact add_smul a b _
  simp only [pathProjection_twist] at hv
  simp_rw [smul_comm _ ((-1:ℂ)^n)] at hv
  have hh : (pathVector e g n).sum (fun a b =>
      (-1:ℂ)^n • (b • pathProjection g n a)) = (-1:ℂ)^n • pathChain e g n := by
    simp only [pathChain,Finsupp.linearCombination_apply,Finsupp.sum,Finset.smul_sum]
  rw [hh] at hv
  exact hv.symm
lemma pathChain_odd (e : GroupMatrix (G := G) (ι := ι)) (g : G) (m : ℕ) :
    pathChain e g (2*m+1) = 0 := by
  have ht := pathChain_twist e g (2*m+1)
  rw [complex_sign_odd m,neg_one_smul] at ht
  have hz : (2:ℂ) • pathChain e g (2*m+1) = 0 := by
    rw [two_smul]
    exact eq_neg_iff_add_eq_zero.mp ht
  exact (smul_eq_zero.mp hz).resolve_left (by norm_num)
end
open scoped BigOperators
open Oriented ChainHomotopy Paths Detector
variable {G : Type*} [Group G]
lemma pathProjection_boundary (g : G) (n : ℕ) (q : Orbit g (n+1)) :
    quotientD g (n+1) (pathProjection g (n+1) q) =
      ∑ i : Fin (n+2), (-1:ℂ)^i.val • pathProjection g n (deleteEntry g n i q) := by
  induction q using Quotient.inductionOn with | _ h =>
    change quotientMap g (n+1) (d (n+1) (wedge (n+2) (project g ∘ h))) = _
    rw [d_wedge,map_sum]
    simp only [map_smul]
    rfl
variable {ι : Type*} [Fintype ι]
lemma pathChain_boundary (e : GroupMatrix (G := G) (ι := ι)) (he : e*e=e)
    (g : G) (n : ℕ) : quotientD g (n+1) (pathChain e g (n+1)) =
      ∑ i : Fin (n+2), (-1:ℂ)^i.val • pathChain e g n := by
  classical
  unfold pathChain
  rw [LinearMap.map_finsupp_linearCombination]
  simp only [Function.comp_apply,pathProjection_boundary,Finsupp.linearCombination_apply,Finsupp.sum]
  simp_rw [Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [smul_comm _ ((-1:ℂ)^i.val)]
  have heq : (Finsupp.linearCombination ℂ ((pathProjection g n) ∘ deleteEntry g n i))
      (pathVector e g (n+1)) = (Finsupp.linearCombination ℂ (pathProjection g n))
      (pathVector e g n) := by
    rw [← Finsupp.linearCombination_mapDomain, pathVector_deleteEntry e he]
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, Function.comp_apply] at heq
  simpa only [Finset.smul_sum] using congrArg (fun x => (-1:ℂ)^i.val • x) heq
theorem pathChain_even_cycle (e : GroupMatrix (G := G) (ι := ι)) (he : e*e=e)
    (g : G) (m : ℕ) : quotientD g (2*m+2) (pathChain e g (2*(m+1))) = 0 := by
  change quotientD g ((2*m+1)+1) (pathChain e g ((2*m+1)+1)) = 0
  rw [pathChain_boundary e he]
  simp only [pathChain_odd,smul_zero,Finset.sum_const_zero]
variable (g : G) (β : G → G → ℂ)
    (hc : ∀ (c : Subgroup.centralizer ({g} : Set G)) h k, β (c*h) (c*k) = β h k)
    (hl : ∀ (r s : ℤ) h k, β (g^r*h) (g^s*k) = β h k+s-r)
def quotientCocycle (m : ℕ) : Coinvariant g (2*m+1) →ₗ[ℂ] ℂ :=
  (relations g (2*m+1)).liftQ (cosetCocycle g m β) (by
    intro x hx
    change cosetCocycle g m β x = 0
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨c,y⟩,rfl⟩ := hx
      rw [map_sub,cosetCocycle_invariant g m β hc hl,sub_self]
    | zero => exact map_zero _
    | add x y _ _ hx hy => rw [map_add,hx,hy,add_zero]
    | smul a x _ hx => rw [map_smul,hx,smul_zero])
lemma quotientCocycle_pathProjection (m : ℕ) (q : Orbit g (2*m)) :
    quotientCocycle g β hc hl m (pathProjection g (2*m) q) = orbitDetector g β hc m q := by
  induction q using Quotient.inductionOn with | _ h =>
    exact cosetCocycle_lifts g m β hl h
lemma quotientCocycle_pairing (e : GroupMatrix (G := G) (ι := ι)) (he : e*e=e)
    (hβ : ∀ h k, β h k = -β k h) (m : ℕ) :
    quotientCocycle g β hc hl m (pathChain e g (2*m)) =
      (2:ℂ)⁻¹^m*totalWeight e g 0 := by
  unfold pathChain
  rw [LinearMap.map_finsupp_linearCombination]
  simp only [Function.comp_apply,quotientCocycle_pathProjection,Finsupp.linearCombination_apply,smul_eq_mul]
  exact detectorSum_value g β hc e he hβ hl m
end BassTrace.PathChains
end
end OAI

end

section
-- OAI.RingTheory.BassTrace.CentralizerGeometry
namespace OAI
noncomputable section
open Set MeasureTheory
open Finset MeasureTheory intervalIntegral
namespace BassTrace.Detector
section
variable {G : Type*} [Group G]
lemma SubtypeCentralizer_commutes (g : G) (c : Subgroup.centralizer ({g} : Set G)) :
    Commute g (c : G) := (Subgroup.mem_centralizer_singleton_iff.mp c.property).symm
abbrev Centralizer (g : G) := Subgroup.centralizer ({g} : Set G)
def generator (g : G) : Centralizer g :=
  ⟨g, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
@[simp] lemma generator_coe (g : G) : (generator g : G) = g := rfl
lemma generator_commutes (g : G) (c : Centralizer g) : Commute (generator g) c := by
  apply Subtype.ext
  exact (SubtypeCentralizer_commutes g c).eq
def cyclic (g : G) : Subgroup (Centralizer g) := Subgroup.zpowers (generator g)
instance cyclic_normal (g : G) : (cyclic g).Normal where
  conj_mem a ha c := by
    obtain ⟨r,rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    have hc := (generator_commutes g c).zpow_left r
    rw [← hc.eq,mul_inv_cancel_right]
    exact (Subgroup.zpowers (generator g)).zpow_mem (Subgroup.mem_zpowers _) r
abbrev ActingGroup (g : G) := Centralizer g ⧸ cyclic g
def centralizerPerm (g : G) : Centralizer g →* Equiv.Perm (Vertex g) where
  toFun c := {
    toFun := centralizerAct g c
    invFun := centralizerAct g c⁻¹
    left_inv y := by rw [← centralizerAct_mul,inv_mul_cancel,centralizerAct_one]
    right_inv y := by rw [← centralizerAct_mul,mul_inv_cancel,centralizerAct_one] }
  map_one' := Equiv.ext (centralizerAct_one g)
  map_mul' c d := Equiv.ext (centralizerAct_mul g c d)
lemma cyclic_le_ker (g : G) : cyclic g ≤ (centralizerPerm g).ker := by
  rintro c hc
  obtain ⟨r,rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
  apply Equiv.ext
  intro y
  induction y using Quotient.inductionOn with | _ h =>
    change project g (g^r*h) = project g h
    apply (project_eq_iff g _ _).mpr
    refine ⟨-r, ?_⟩
    simp [← mul_assoc]
def quotientPerm (g : G) : ActingGroup g →* Equiv.Perm (Vertex g) :=
  QuotientGroup.lift (cyclic g) (centralizerPerm g) (cyclic_le_ker g)
instance vertexAction (g : G) : MulAction (ActingGroup g) (Vertex g) :=
  MulAction.compHom (Vertex g) (quotientPerm g)
@[simp] lemma quotient_smul_project (g : G) (c : Centralizer g) (h : G) :
    (QuotientGroup.mk c : ActingGroup g) • project g h = project g (c*h) := rfl
lemma vertex_action_free (g : G) (a : ActingGroup g) (y : Vertex g)
    (ha : a • y = y) : a = 1 := by
  induction a using Quotient.inductionOn with | _ c =>
    induction y using Quotient.inductionOn with | _ h =>
      apply (QuotientGroup.eq_one_iff c).mpr
      change project g ((c:G)*h) = project g h at ha
      obtain ⟨r,hr⟩ := (project_eq_iff g _ _).mp ha
      have he : g^r*(c:G) = 1 := by
        apply mul_right_cancel (b := h)
        simpa only [mul_assoc,one_mul] using hr
      have hc : c = (generator g)^(-r) := by
        apply Subtype.ext
        change (c:G) = g^(-r)
        rw [zpow_neg]
        exact eq_inv_of_mul_eq_one_right he
      rw [hc]
      exact (cyclic g).zpow_mem (Subgroup.mem_zpowers _) _
lemma actingGroup_injective_orbit (g : G) (y : Vertex g) :
    Function.Injective (fun a : ActingGroup g => a • y) := by
  intro a b hab
  change a • y = b • y at hab
  have hh : (b⁻¹*a) • y = y := by rw [mul_smul,hab,inv_smul_smul]
  exact (inv_mul_eq_one.mp (vertex_action_free g _ y hh)).symm
end
open Set Finset
variable {G : Type*} [Group G]
def rightMul (g s : G) : Vertex g → Vertex g :=
  Quotient.map' (fun h => h*s) (by
    intro h k hk
    obtain ⟨r,hr⟩ := (project_eq_iff g h k).mp (Quotient.sound hk)
    apply Quotient.exact
    apply (project_eq_iff g _ _).mpr
    exact ⟨r,by rw [← mul_assoc,hr]⟩)
@[simp] lemma rightMul_project (g s h : G) : rightMul g s (project g h) = project g (h*s) := rfl
@[simp] lemma rightMul_one (g : G) (y : Vertex g) : rightMul g 1 y = y := by
  induction y using Quotient.inductionOn with | _ h =>
    change project g (h*1) = project g h
    rw [mul_one]
lemma rightMul_mul (g s t : G) (y : Vertex g) :
    rightMul g (s*t) y = rightMul g t (rightMul g s y) := by
  induction y using Quotient.inductionOn with | _ h =>
    change project g (h*(s*t)) = project g ((h*s)*t)
    rw [mul_assoc]
lemma smul_rightMul (g : G) (a : ActingGroup g) (s : G) (y : Vertex g) :
    a • rightMul g s y = rightMul g s (a • y) := by
  induction a using Quotient.inductionOn with | _ c =>
    induction y using Quotient.inductionOn with | _ h =>
      change project g ((c:G)*(h*s)) = project g (((c:G)*h)*s)
      rw [mul_assoc]
def supportGraph (g : G) (S : Finset G) (hS : ∀ s ∈ S, s⁻¹ ∈ S) : SimpleGraph (Vertex g) where
  Adj y z := y ≠ z ∧ ∃ s ∈ S, rightMul g s y = z
  symm := ⟨by
    rintro y z ⟨hne,s,hs,rfl⟩
    refine ⟨hne.symm,s⁻¹,hS s hs,?_⟩
    rw [← rightMul_mul,mul_inv_cancel,rightMul_one]⟩
  loopless := ⟨by rintro y ⟨h,_⟩; exact h rfl⟩
lemma supportGraph_adj (g : G) (S : Finset G) (hS : ∀ s ∈ S, s⁻¹ ∈ S) (y z : Vertex g) :
    (supportGraph g S hS).Adj y z ↔ y ≠ z ∧ ∃ s ∈ S, rightMul g s y = z := Iff.rfl
lemma supportGraph_smul (g : G) (S : Finset G) (hS : ∀ s ∈ S, s⁻¹ ∈ S)
    (a : ActingGroup g) (y z : Vertex g) :
    (supportGraph g S hS).Adj (a • y) (a • z) ↔ (supportGraph g S hS).Adj y z := by
  simp only [supportGraph_adj,Ne,smul_left_cancel_iff]
  constructor
  · rintro ⟨hne,s,hs,he⟩
    exact ⟨hne,s,hs,(MulAction.injective a) (by change a • rightMul g s y = a • z; rw [smul_rightMul]; exact he)⟩
  · rintro ⟨hne,s,hs,he⟩
    exact ⟨hne,s,hs,by rw [← smul_rightMul,he]⟩
lemma supportGraph_finite_neighbors (g : G) (S : Finset G) (hS : ∀ s ∈ S, s⁻¹ ∈ S)
    (y : Vertex g) : ((supportGraph g S hS).neighborSet y).Finite := by
  classical
  apply (S.image (fun s => rightMul g s y)).finite_toSet.subset
  rintro z ⟨_,s,hs,rfl⟩
  exact Finset.mem_image_of_mem _ hs
scoped instance supportGraphLocallyFinite (g : G) (S : Finset G)
    (hS : ∀ s ∈ S, s⁻¹ ∈ S) : (supportGraph g S hS).LocallyFinite :=
  fun y => (supportGraph_finite_neighbors g S hS y).fintype
open scoped BassTrace.Detector
lemma supportGraph_degree_le (g : G) (S : Finset G) (hS : ∀ s ∈ S, s⁻¹ ∈ S)
    (y : Vertex g) : (supportGraph g S hS).degree y ≤ S.card := by
  classical
  calc (supportGraph g S hS).degree y = ((supportGraph g S hS).neighborFinset y).card := rfl
    _ ≤ (S.image (fun s => rightMul g s y)).card := Finset.card_le_card (by
      intro z hz
      obtain ⟨_,s,hs,rfl⟩ := (SimpleGraph.mem_neighborFinset _ _ _).mp hz
      exact Finset.mem_image_of_mem _ hs)
    _ ≤ S.card := Finset.card_image_le
lemma supportGraph_reachable_rightMul (g : G) (S : Finset G)
    (hS : ∀ s ∈ S, s⁻¹ ∈ S) (s : G) (hs : s ∈ Subgroup.closure (S : Set G)) :
    ∀ y, (supportGraph g S hS).Reachable y (rightMul g s y) := by
  induction hs using Subgroup.closure_induction with
  | mem s hs =>
    intro y
    by_cases he : y = rightMul g s y
    · rw [← he]
    · exact (show (supportGraph g S hS).Adj y (rightMul g s y) from ⟨he,s,hs,rfl⟩).reachable
  | one => intro y; rw [rightMul_one]
  | mul a b ha hb ia ib =>
    intro y
    rw [rightMul_mul]
    exact (ia y).trans (ib (rightMul g a y))
  | inv a ha ia =>
    intro y
    have h := (ia (rightMul g a⁻¹ y)).symm
    simpa [← rightMul_mul] using h
lemma supportGraph_connected (g : G) (S : Finset G)
    (hS : ∀ s ∈ S, s⁻¹ ∈ S) (hgen : Subgroup.closure (S : Set G) = ⊤) :
    (supportGraph g S hS).Connected := by
  have : Nonempty (Vertex g) := ⟨project g 1⟩
  refine ⟨?_⟩
  intro y z
  induction y using Quotient.inductionOn with | _ a =>
    induction z using Quotient.inductionOn with | _ b =>
      have h := supportGraph_reachable_rightMul g S hS (a⁻¹*b) (by rw [hgen]; trivial) (project g a)
      change (supportGraph g S hS).Reachable (project g a) (project g b)
      simpa [mul_assoc] using h
scoped instance vertexIsCancelSMul (g : G) : IsCancelSMul (ActingGroup g) (Vertex g) where
  left_cancel' a _ _ he := (MulAction.injective a) he
  right_cancel' _ _ x he := (actingGroup_injective_orbit g x) he
end BassTrace.Detector
end
end OAI

end

section
-- OAI.RingTheory.BassTrace.FreeParameters
namespace OAI
open Set MeasureTheory
open Finset MeasureTheory intervalIntegral
noncomputable section
namespace BassTrace.FreeParameter
open Set MeasureTheory
open scoped Pointwise
universe u v
variable {H : Type u} [Group H] (S : Subgroup H)
variable {C : Type v} [Group C] (χ : S →* C)
section Probability
variable [Fintype C] [MeasurableSpace C] [MeasurableSingletonClass C]
end Probability
namespace Character
end Character
variable (H)
instance quotientCountable [Countable H] (S : Subgroup H) : Countable (H ⧸ S) :=
  (QuotientGroup.mk_surjective (s := S)).countable
end BassTrace.FreeParameter
end
end OAI

end

section
-- OAI.RingTheory.BassTrace.FiniteGenerators
namespace OAI
open Set MeasureTheory
open Finset MeasureTheory intervalIntegral
noncomputable section
namespace BassTrace
section
open scoped Classical BigOperators
variable {G : Type*} [Group G]
omit [Group G] in
lemma trace_coeff {ι : Type*} [Fintype ι] (e : Paths.GroupMatrix (G := G) (ι := ι)) (s : G) :
    (Matrix.trace e).coeff s=Matrix.trace (Paths.coefficient e s) := by
  simp only [Matrix.trace,Matrix.diag,MonoidAlgebra.coeff_sum,Finsupp.finsetSum_apply,Paths.coefficient]
lemma classCoefficient_eq_finsum (g : G) (a : MonoidAlgebra ℂ G) :
    classCoefficient g a=∑ᶠ s∈{s : G|IsConj s g},a.coeff s := by
  unfold classCoefficient
  simp only [Set.mem_ofPred_eq,finsum_eq_if]
  symm
  apply finsum_eq_sum_of_support_subset
  intro s hs
  by_contra h
  have hz := Finsupp.notMem_support_iff.mp h
  simp [hz] at hs
lemma totalWeight_eq_classCoefficient {ι : Type*} [Fintype ι]
    (e : Paths.GroupMatrix (G := G) (ι := ι)) (he : e*e=e) (g : G) :
    Paths.totalWeight e g 0=classCoefficient g (Matrix.trace e) := by
  rw [Paths.totalWeight_conjugacy e he g 0,classCoefficient_eq_finsum]
  simp only [trace_coeff]
lemma sum_conjugacy_invariant_zero (a : MonoidAlgebra ℂ G) (P : G→Prop)
    (hinv : ∀h k,IsConj h k→(P h↔P k))
    (hz : ∀h,P h→classCoefficient h a=0) :
    a.coeff.sum (fun h z=>if P h then z else 0)=0 := by
  rw [Finsupp.sum]
  rw [←Finset.sum_fiberwise_of_maps_to (s := a.coeff.support)
      (t := a.coeff.support.image ConjClasses.mk)
      (fun i hi=>Finset.mem_image_of_mem _ hi)]
  apply Finset.sum_eq_zero
  intro q hq
  obtain ⟨h,hh,rfl⟩ := Finset.mem_image.mp hq
  by_cases hp : P h
  · have he : (∑i∈a.coeff.support with ConjClasses.mk i=ConjClasses.mk h,
        if P i then a.coeff i else 0)=classCoefficient h a := by
      rw [classCoefficient,Finsupp.sum,Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      simp only [ConjClasses.mk_eq_mk_iff_isConj]
      by_cases hc : IsConj i h
      · simp only [hc,ite_eq_left,(hinv i h hc).mpr hp]
      · simp only [hc,ite_false]
    rw [he,hz h hp]
  · apply Finset.sum_eq_zero
    intro i hi
    have hc := ConjClasses.mk_eq_mk_iff_isConj.mp (Finset.mem_filter.mp hi).2
    simp only [(hinv i h hc).not.mpr hp,ite_false]
end
open scoped Classical BigOperators
variable {G : Type*} [Group G] {ι : Type*} [Fintype ι]
lemma exists_symmetric_generators [Group.FG G] (e : Paths.GroupMatrix (G := G) (ι := ι)) :
    ∃S : Finset G,(∀s∈S,s⁻¹∈S) ∧ Subgroup.closure (S : Set G)=⊤ ∧ Paths.support e⊆S := by
  obtain ⟨T,hT,hfin⟩ := Group.fg_iff.mp (inferInstance : Group.FG G)
  let U := hfin.toFinset ∪ Paths.support e
  let S := U ∪ U.image Inv.inv
  refine ⟨S,?_,?_,?_⟩
  · intro s hs
    rcases Finset.mem_union.mp hs with hs|hs
    · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hs)
    · obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hs
      exact Finset.mem_union_left _ (by simpa only [inv_inv] using hu)
  · apply top_unique
    rw [←hT]
    apply Subgroup.closure_mono
    intro s hs
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (hfin.mem_toFinset.mpr hs))
  · intro s hs
    exact Finset.mem_union_left _ (Finset.mem_union_right _ hs)
def restrictMatrix (K : Subgroup G) (e : Paths.GroupMatrix (G := G) (ι := ι)) :
    Paths.GroupMatrix (G := K) (ι := ι) :=
  fun i j=>MonoidAlgebra.comapDomain Subtype.val Subtype.val_injective (e i j)
lemma restrictMatrix_map (K : Subgroup G) (e : Paths.GroupMatrix (G := G) (ι := ι))
    (hs : ∀s∈Paths.support e,s∈K) :
    (restrictMatrix K e).map (MonoidAlgebra.mapDomainRingHom ℂ K.subtype)=e := by
  apply Matrix.ext
  intro i j
  apply MonoidAlgebra.mapDomain_comapDomain
  intro s hs'
  exact ⟨⟨s,hs s (Paths.entry_support_subset e i j hs')⟩,rfl⟩
lemma restrictMatrix_idempotent (K : Subgroup G) (e : Paths.GroupMatrix (G := G) (ι := ι))
    (he : e*e=e) (hs : ∀s∈Paths.support e,s∈K) :
    restrictMatrix K e * restrictMatrix K e=restrictMatrix K e := by
  have hi := MonoidAlgebra.mapDomain_injective (R := ℂ) (f := (K.subtype : K→G)) Subtype.val_injective
  have hh : (restrictMatrix K e * restrictMatrix K e).map (MonoidAlgebra.mapDomainRingHom ℂ K.subtype)=
      (restrictMatrix K e).map (MonoidAlgebra.mapDomainRingHom ℂ K.subtype) := by
    rw [Matrix.map_mul,restrictMatrix_map K e hs,he]
  apply Matrix.ext
  intro i j
  apply hi
  exact congrFun (congrFun hh i) j
lemma map_trace_restrict (K : Subgroup G) (e : Paths.GroupMatrix (G := G) (ι := ι))
    (hs : ∀s∈Paths.support e,s∈K) :
    MonoidAlgebra.mapDomainRingHom ℂ K.subtype (Matrix.trace (restrictMatrix K e))=Matrix.trace e := by
  simp only [Matrix.trace,Matrix.diag,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact congrFun (congrFun (restrictMatrix_map K e hs) i) i
lemma classCoefficient_map_subgroup (K : Subgroup G) (a : MonoidAlgebra ℂ K) (g : G) :
    classCoefficient g (MonoidAlgebra.mapDomainRingHom ℂ K.subtype a)=
      a.coeff.sum (fun h z=>if IsConj (h : G) g then z else 0) := by
  unfold classCoefficient
  rw [MonoidAlgebra.mapDomainRingHom_apply,MonoidAlgebra.coeff_mapDomain]
  apply Finsupp.sum_mapDomain_index
  · intro h; simp
  · intro h z w; split_ifs <;> simp
end BassTrace
end
end OAI

end

section
-- OAI.RingTheory.BassTrace.SubdivisionWeights
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
end
section
open Set Finset
open scoped BassTrace.Sparse Classical
variable {Y : Type*}
variable {H X : Type*} [Group H] [MulAction H Y] [DecidableEq Y]
  [TopologicalSpace X] [MulAction H X]
variable {K : PreAbstractSimplicialComplex Y} {n : ℕ} {R : ℝ}
variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)
variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)
variable (hn : 0<n) (hR : 0≤R)
end
open Set Finset
open scoped BassTrace.Sparse Classical
variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y]
  [TopologicalSpace X] [MulAction H X]
variable {K : PreAbstractSimplicialComplex Y} {n : ℕ} {R : ℝ}
variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)
variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)
variable (hn : 0<n) (hR : 0≤R) (y₀ : Y)
end BassTrace.Sparse
namespace BassTrace.SubdivisionChains
section
open Set Finset
open scoped BassTrace.Sparse Classical
variable {Y : Type*} [LinearOrder Y] [LinearOrder (Y →₀ ℝ)]
variable {K : PreAbstractSimplicialComplex Y}
end
open Set Finset
open scoped BassTrace.Sparse Classical
variable {Y : Type*} [LinearOrder Y] [LinearOrder (Y →₀ ℝ)]
variable {K : PreAbstractSimplicialComplex Y}
end BassTrace.SubdivisionChains
end
end OAI

end

section
-- OAI.RingTheory.BassTrace.SparseChains
namespace OAI
open Set MeasureTheory
open Finset MeasureTheory intervalIntegral
noncomputable section
namespace BassTrace.BarycentricChains
open scoped BigOperators
open Oriented ChainHomotopy
variable {V W Y Z : Type*} [LinearOrder V] [LinearOrder W] [LinearOrder Y]
end BassTrace.BarycentricChains
namespace BassTrace.Sparse
open Set Finset MeasureTheory
open scoped BassTrace.Sparse Classical
open Oriented ChainHomotopy Fundamental BarycentricChains SubdivisionChains
variable {H Y X : Type*} [Group H] [MulAction H Y] [LinearOrder Y]
  [LinearOrder (Y →₀ ℝ)] [TopologicalSpace X] [MulAction H X]
variable {K : PreAbstractSimplicialComplex Y} {n : ℕ} {R : ℝ}
variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)
variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)
variable (hn : 0<n) (hR : 0≤R) (y₀ : Y)
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
end BassTrace.Sparse
namespace BassTrace.PathChains
section
open Set Finset Oriented ChainHomotopy Paths Detector Sparse BarycentricChains
open scoped Classical Pointwise BassTrace.Detector
variable {G : Type*} [Group G] {ι : Type*} [Fintype ι]
lemma tuple_connected {Y : Type*} (Γ : SimpleGraph Y) (n : ℕ) (v : Fin (n+1) → Y)
    (hstep : ∀i : Fin n,v i.castSucc=v i.succ ∨ Γ.Adj (v i.castSucc) (v i.succ)) :
    (Γ.induce (↑(Finset.univ.image v) : Set Y)).Connected := by
  let u (i : Fin (n+1)) : (↑(Finset.univ.image v) : Set Y) :=
    ⟨v i,Finset.mem_image_of_mem v (Finset.mem_univ i)⟩
  have hr (i : Fin (n+1)) : (Γ.induce (↑(Finset.univ.image v) : Set Y)).Reachable (u 0) (u i) := by
    induction i using Fin.induction with
    | zero => exact SimpleGraph.Reachable.rfl
    | succ i hi =>
      apply hi.trans
      rcases hstep i with he|ha
      · have he' : u i.castSucc=u i.succ := Subtype.ext he
        rw [he']
      · exact (show (Γ.induce (↑(Finset.univ.image v) : Set Y)).Adj (u i.castSucc) (u i.succ) from ha).reachable
  have : Nonempty (↑(Finset.univ.image v) : Set Y) := ⟨u 0⟩
  refine ⟨?_⟩
  intro x y
  obtain ⟨i,_,hi⟩ := Finset.mem_image.mp x.property
  obtain ⟨j,_,hj⟩ := Finset.mem_image.mp y.property
  have hx : u i=x := Subtype.ext hi
  have hy : u j=y := Subtype.ext hj
  rw [←hx,←hy]
  exact (hr i).symm.trans (hr j)
lemma path_tuple_connected (e : GroupMatrix (G := G) (ι := ι)) (g : G)
    (S : Finset G) (hS : ∀s∈S,s⁻¹∈S) (heS : support e⊆S) (n : ℕ)
    (q : Orbit g n) (hq : q∈(pathVector e g n).support) :
    ((supportGraph g S hS).induce (↑(Finset.univ.image (project g ∘ q.out)) : Set (Vertex g))).Connected := by
  apply tuple_connected
  intro i
  by_cases he : project g (q.out i.castSucc)=project g (q.out i.succ)
  · exact Or.inl he
  · apply Or.inr
    refine ⟨he,increment g n q.out i.castSucc,heS ?_,?_⟩
    · apply weight_ne_zero_support e g n q.out
      have hw : orbitWeight e g n q ≠ 0 := Finsupp.mem_support_iff.mp hq
      rw [←Quotient.out_eq q] at hw
      exact hw
    · rw [increment_castSucc]
      change project g (q.out i.castSucc * ((q.out i.castSucc)⁻¹*q.out i.succ))=project g (q.out i.succ)
      rw [mul_inv_cancel_left]
def topPaths (e : GroupMatrix (G := G) (ι := ι)) (g : G) (n : ℕ) : Finset (Finset (Vertex g)) :=
  (((pathVector e g n).support).filter (fun q=>Function.Injective (project g ∘ q.out))).image
    (fun q=>Finset.univ.image (project g ∘ q.out))
lemma topPaths_mem (e : GroupMatrix (G := G) (ι := ι)) (g : G) (n : ℕ)
    (q : Orbit g n) (hq : q∈(pathVector e g n).support)
    (hi : Function.Injective (project g ∘ q.out)) :
    Finset.univ.image (project g ∘ q.out) ∈ topPaths e g n := by
  exact Finset.mem_image.mpr ⟨q,Finset.mem_filter.mpr ⟨hq,hi⟩,rfl⟩
def pathSupport (e : GroupMatrix (G := G) (ι := ι)) (g : G) (n : ℕ) :
    PreAbstractSimplicialComplex (Vertex g) := generatedComplex (H := ActingGroup g) (topPaths e g n)
lemma topPaths_card (e : GroupMatrix (G := G) (ι := ι)) (g : G) (n : ℕ)
    {t : Finset (Vertex g)} (ht : t∈topPaths e g n) : t.card=n+1 := by
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp ht
  rw [Finset.card_image_of_injective _ (Finset.mem_filter.mp hq).2,Finset.card_univ,Fintype.card_fin]
lemma pathSupport_pure (e : GroupMatrix (G := G) (ι := ι)) (g : G)
    (S : Finset G) (hS : ∀s∈S,s⁻¹∈S) (heS : support e⊆S) (n : ℕ) :
    ∀s∈(pathSupport e g n).faces,∃σ∈(pathSupport e g n).faces,s⊆σ ∧ σ.card=n+1 ∧
      ((supportGraph g S hS).induce (σ : Set (Vertex g))).Connected := by
  apply generatedComplex_pure
  · exact supportGraph_smul g S hS
  · intro t ht
    refine ⟨topPaths_card e g n ht,?_⟩
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp ht
    exact path_tuple_connected e g S hS heS n q (Finset.mem_filter.mp hq).1
def liftPath (e : GroupMatrix (G := G) (ι := ι)) (g : G) (n : ℕ) : Degree (Vertex g) (n+1) :=
  Finsupp.linearCombination ℂ (fun q : Orbit g n=>wedge (n+1) (project g ∘ q.out)) (pathVector e g n)
lemma liftPath_quotient (e : GroupMatrix (G := G) (ι := ι)) (g : G) (n : ℕ) :
    quotientMap g (n+1) (liftPath e g n)=pathChain e g n := by
  unfold liftPath pathChain
  rw [LinearMap.map_finsupp_linearCombination]
  congr 2
  funext q
  change quotientMap g (n+1) (wedge (n+1) (project g ∘ q.out))=pathProjection g n q
  rw [←pathProjection_mk,Quotient.out_eq]
lemma liftPath_mem (e : GroupMatrix (G := G) (ι := ι)) (g : G) (n : ℕ) [LinearOrder (Vertex g)] :
    liftPath e g n∈(augmentedComplex (pathSupport e g n)).chains (n+1) := by
  classical
  unfold liftPath Finsupp.linearCombination
  simp only [Finsupp.lsum_apply,Finsupp.sum]
  apply Submodule.sum_mem
  intro q hq
  change (pathVector e g n) q • wedge (n+1) (project g ∘ q.out) ∈ _
  by_cases hi : Function.Injective (project g ∘ q.out)
  · apply Submodule.smul_mem
    apply Complex.wedge_mem
    apply Set.mem_insert_of_mem
    apply generatedComplex_top_mem (topPaths e g n)
    · convert topPaths_mem e g n q hq hi using 1
      congr 1
      exact Subsingleton.elim _ _
    · exact Finset.image_nonempty.mpr Finset.univ_nonempty
  · simp only [wedge_eq_zero_of_not_injective _ hi,smul_zero]
    exact Submodule.zero_mem _
end
open Oriented ChainHomotopy Paths Detector Sparse BarycentricChains
open scoped Classical BassTrace.Detector
variable {G : Type*} [Group G]
lemma projection_path_relations (g : G) [LinearOrder (Vertex g)]
    (K : Complex (Vertex g)) (hK : K.IsInvariant (H := ActingGroup g)) (n : ℕ)
    (x : Degree (Vertex g) n) (hx : x∈relations g n) :
    K.projection n x∈K.relations hK n := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨c,z⟩,rfl⟩ := hx
    let h : ActingGroup g := QuotientGroup.mk c
    change K.projection n (relabel n (fun y=>h•y) z-z)∈K.relations hK n
    have hh : K.projection n (relabel n (fun y=>h•y) z-z)=
        (⟨relabel n (fun y=>h•y) (K.projection n z),K.relabel_mem hK n h (K.projection n z).property⟩ : K.chains n)-K.projection n z := by
      apply Subtype.ext
      simp only [map_sub,Submodule.coe_sub,K.projection_relabel hK]
    rw [hh]
    exact Submodule.subset_span ⟨(h,K.projection n z),rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx
lemma internal_path_cycle {ι : Type*} [Fintype ι]
    (e : GroupMatrix (G := G) (ι := ι)) (he : e*e=e) (g : G) (m : ℕ)
    [LinearOrder (Vertex g)]
    (hInv : (augmentedComplex (pathSupport e g (2*(m+1)))).IsInvariant (H := ActingGroup g)) :
    (⟨d (2*(m+1)) (liftPath e g (2*(m+1))),
      (augmentedComplex (pathSupport e g (2*(m+1)))).d_mem _ (liftPath_mem e g _)⟩ :
      (augmentedComplex (pathSupport e g (2*(m+1)))).chains (2*(m+1)))∈
      (augmentedComplex (pathSupport e g (2*(m+1)))).relations hInv (2*(m+1)) := by
  let K := augmentedComplex (pathSupport e g (2*(m+1)))
  have hcycle : quotientD g (2*(m+1)) (pathChain e g (2*(m+1)))=0 := by
    first | exact pathChain_even_cycle e he g m | (convert pathChain_even_cycle e he g m using 1; rfl)
  have hz : quotientMap g (2*(m+1)) (d (2*(m+1)) (liftPath e g (2*(m+1))))=0 := by
    rw [←quotientD_mk,liftPath_quotient]
    exact hcycle
  have hx := (Submodule.Quotient.mk_eq_zero _).mp hz
  have hp := projection_path_relations g K hInv (2*(m+1)) _ hx
  have hm := K.d_mem (2*(m+1)) (liftPath_mem e g _)
  convert hp using 1
  apply Subtype.ext
  exact (K.projection_self _ hm).symm
end BassTrace.PathChains
end
end OAI

end

section
-- OAI.RingTheory.BassTrace.SparseBounds
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
variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)
variable (hn : 0<n) (hR : 0≤R) (y₀ : Y)
end
open Set Finset MeasureTheory
open scoped BassTrace.Sparse Classical
open Oriented ChainHomotopy Fundamental BarycentricChains SubdivisionChains
variable {H Y X : Type*} [Group H] [MulAction H Y] [LinearOrder Y]
  [LinearOrder (Y →₀ ℝ)] [TopologicalSpace X] [MulAction H X]
  [CompactSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
variable {K : PreAbstractSimplicialComplex Y} {n : ℕ} {R : ℝ}
variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)
variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)
variable (hn : 0<n) (hR : 0≤R) (y₀ : Y)
variable (μ : Measure X) [IsProbabilityMeasure μ]
end BassTrace.Sparse
namespace BassTrace.BarycentricChains
open Set Finset
open scoped Classical
open Oriented ChainHomotopy
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
variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)
variable (hΓaut : ∀ (h : H) u v,Γ.Adj (h•u) (h•v) ↔ Γ.Adj u v)
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
open scoped Classical
end BassTrace.Sparse.GraphGeometry
end
end OAI

end

section
-- OAI.RingTheory.BassTrace.Definitions
namespace OAI
noncomputable section
namespace BassTrace
open scoped Classical
namespace K0
open scoped Classical BigOperators
section
variable {R : Type*} [Ring R]
variable {G : Type*} [_root_.Group G]
end
variable {G : Type*} [_root_.Group G]
def classTrace (a : MonoidAlgebra ℂ G) : ConjClasses G →₀ ℂ :=
  Finsupp.mapDomain ConjClasses.mk a.coeff
end K0
namespace RightProjective
open scoped Classical BigOperators
open MulOpposite
section
variable {R : Type*} [Ring R]
variable {M N : Type*} [AddCommGroup M] [Module Rᵐᵒᵖ M]
  [AddCommGroup N] [Module Rᵐᵒᵖ N]
end
open scoped Classical
universe u v
variable {R : Type u} [Ring R]
variable {G : Type u} [_root_.Group G]
end RightProjective
end BassTrace
end
end OAI

end

section
-- OAI.RingTheory.BassTrace.MatrixK0
namespace OAI
open Set MeasureTheory
open Finset MeasureTheory intervalIntegral
noncomputable section
namespace BassTrace.K0
section
open scoped Classical BigOperators
variable {R : Type*} [Ring R]
variable {G : Type*} [_root_.Group G]
end
section
open scoped Classical BigOperators
variable {G : Type*} [_root_.Group G]
lemma classTrace_apply (a : MonoidAlgebra ℂ G) (g : G) :
    classTrace a (ConjClasses.mk g)=classCoefficient g a := by
  unfold classTrace classCoefficient
  simp only [Finsupp.mapDomain,Finsupp.sum_apply,Finsupp.single_apply,
    ConjClasses.mk_eq_mk_iff_isConj]
end
open scoped Classical
end BassTrace.K0
end
end OAI

end

section
-- OAI.RingTheory.BassTrace.TraceRank
namespace OAI
open scoped Classical BigOperators
noncomputable section
namespace TorsionFreeBass
def TorsionFree (G : Type*) [Group G] : Prop := ∀ g : G, IsOfFinOrder g → g = 1
variable {G : Type*} [Group G]
def augmentation : MonoidAlgebra ℂ G →+* ℂ :=
  (MonoidAlgebra.lift ℂ ℂ G (1 : G →* ℂ)).toRingHom
lemma augmentation_apply (a : MonoidAlgebra ℂ G) :
    augmentation a = a.coeff.sum (fun _ z => z) := by
  simp [augmentation, MonoidAlgebra.lift_apply]
def canonicalTrace (a : MonoidAlgebra ℂ G) : ℂ := a.coeff 1
def matrixTrace {q : ℕ} (e : Matrix (Fin q) (Fin q) (MonoidAlgebra ℂ G)) : ℂ :=
  ∑ i, canonicalTrace (e i i)
lemma canonicalTrace_eq_classCoefficient (a : MonoidAlgebra ℂ G) :
    canonicalTrace a = BassTrace.classCoefficient 1 a := by
  simp [canonicalTrace, BassTrace.classCoefficient]
lemma matrixTrace_eq_classCoefficient {q : ℕ}
    (e : Matrix (Fin q) (Fin q) (MonoidAlgebra ℂ G)) :
    matrixTrace e = BassTrace.classCoefficient 1 (Matrix.trace e) := by
  simp [matrixTrace, Matrix.trace, Matrix.diag, canonicalTrace_eq_classCoefficient]
lemma classTrace_sum (a : MonoidAlgebra ℂ G) :
    (BassTrace.K0.classTrace a).sum (fun _ z => z) = augmentation a := by
  rw [augmentation_apply]
  simp [BassTrace.K0.classTrace, Finsupp.sum_mapDomain_index]
end TorsionFreeBass
end
end OAI

end

section
-- OAI.RingTheory.BassTrace.RegularRepresentation
namespace OAI
open scoped Classical BigOperators ComplexInnerProductSpace
noncomputable section
namespace TorsionFreeBass.Regular
abbrev Hilbert (G : Type*) := lp (fun _ : G => ℂ) 2
def permute {X : Type*} (s : Equiv.Perm X) : Hilbert X ≃ₗᵢ[ℂ] Hilbert X where
  toFun x := ⟨fun i => x (s.symm i), memℓp_gen <|
    (s.symm.summable_iff).mpr (x.2.summable (by norm_num))⟩
  invFun x := ⟨fun i => x (s i), memℓp_gen <|
    (s.summable_iff).mpr (x.2.summable (by norm_num))⟩
  left_inv x := by ext i; simp
  right_inv x := by ext i; simp
  map_add' x y := by ext i; rfl
  map_smul' a x := by ext i; rfl
  norm_map' x := by
    rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
    congr 1
    exact s.symm.tsum_eq (fun i => ‖x i‖ ^ (2 : ENNReal).toReal)
@[simp] lemma permute_apply {X : Type*} (s : Equiv.Perm X) (x : Hilbert X) (i : X) :
    permute s x i = x (s.symm i) := rfl
variable {G : Type*} [Group G]
def leftShift (g : G) : Hilbert G ≃ₗᵢ[ℂ] Hilbert G := permute (Equiv.mulLeft g)
def rightShift (g : G) : Hilbert G ≃ₗᵢ[ℂ] Hilbert G := permute (Equiv.mulRight g)
@[simp] lemma leftShift_apply (g : G) (x : Hilbert G) (h : G) :
    leftShift g x h = x (g⁻¹ * h) := rfl
@[simp] lemma rightShift_apply (g : G) (x : Hilbert G) (h : G) :
    rightShift g x h = x (h * g⁻¹) := rfl
lemma left_right_commute (g h : G) (x : Hilbert G) :
    leftShift g (rightShift h x) = rightShift h (leftShift g x) := by
  ext k
  simp [mul_assoc]
@[simp] lemma rightShift_inv (g : G) (x : Hilbert G) :
    rightShift g (rightShift g⁻¹ x) = x := by
  ext k
  simp [mul_assoc]
def leftRegular : G →* (Hilbert G →L[ℂ] Hilbert G) where
  toFun g := (leftShift g).toContinuousLinearEquiv.toContinuousLinearMap
  map_one' := by ext x h; simp
  map_mul' g h := by ext x k; simp [mul_assoc]
@[simp] lemma leftRegular_apply (g : G) (x : Hilbert G) :
    leftRegular g x = leftShift g x := rfl
def convolution : MonoidAlgebra ℂ G →ₐ[ℂ] (Hilbert G →L[ℂ] Hilbert G) :=
  MonoidAlgebra.lift ℂ _ G leftRegular
lemma convolution_apply (a : MonoidAlgebra ℂ G) (x : Hilbert G) :
    convolution a x = ∑ g ∈ a.coeff.support, a.coeff g • leftShift g x := by
  simp [convolution, MonoidAlgebra.lift_apply, Finsupp.sum]
lemma convolution_rightShift (a : MonoidAlgebra ℂ G) (g : G) (x : Hilbert G) :
    convolution a (rightShift g x) = rightShift g (convolution a x) := by
  simp only [convolution_apply, map_sum, map_smul, left_right_commute]
def delta (g : G) : Hilbert G := lp.single 2 g 1
omit [Group G] in
@[simp] lemma delta_apply (g h : G) : delta g h = if h = g then 1 else 0 := by
  simp [delta, lp.single_apply, Pi.single_apply]
@[simp] lemma leftShift_delta (g h : G) : leftShift g (delta h) = delta (g * h) := by
  ext k
  simp [inv_mul_eq_iff_eq_mul]
@[simp] lemma rightShift_delta (g h : G) : rightShift g (delta h) = delta (h * g) := by
  ext k
  simp [mul_inv_eq_iff_eq_mul]
lemma convolution_delta (a : MonoidAlgebra ℂ G) (g : G) :
    convolution a (delta 1) g = a.coeff g := by
  simp only [convolution_apply, leftShift_delta, mul_one, lp.coeFn_sum,
    Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, delta_apply,
    mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  split_ifs with hg
  · rfl
  · exact (Finsupp.notMem_support_iff.mp hg).symm
omit [Group G] in
lemma inner_delta (g : G) (x : Hilbert G) : inner ℂ (delta g) x = x g := by
  simp [delta, lp.inner_single_left]
lemma trace_commute (a : MonoidAlgebra ℂ G) (T : Hilbert G →L[ℂ] Hilbert G)
    (hT : ∀ g x, T (rightShift g x) = rightShift g (T x)) :
    T (convolution a (delta 1)) 1 = convolution a (T (delta 1)) 1 := by
  simp only [convolution_apply, map_sum, map_smul, leftShift_delta, mul_one]
  have hh (g : G) : T (delta g) = rightShift g (T (delta 1)) := by
    simpa only [rightShift_delta, one_mul] using hT g (delta 1)
  change (∑ g ∈ a.coeff.support, a.coeff g • T (delta g)) 1 =
    (∑ g ∈ a.coeff.support, a.coeff g • leftShift g (T (delta 1))) 1
  have heq (g : G) : T (delta g) 1 = leftShift g (T (delta 1)) 1 := by
    rw [hh]
    simp only [rightShift_apply, leftShift_apply, one_mul, mul_one]
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply, heq]
end TorsionFreeBass.Regular
end
open scoped Classical BigOperators ComplexInnerProductSpace
noncomputable section
namespace TorsionFreeBass.Regular
variable {G : Type*} [Group G]
lemma projection_rightShift (M : Submodule ℂ (Hilbert G)) [M.HasOrthogonalProjection]
    (hM : ∀ g x, x ∈ M → rightShift g x ∈ M) (g : G) (x : Hilbert G) :
    M.starProjection (rightShift g x) = rightShift g (M.starProjection x) := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact hM g _ (M.starProjection_apply_mem x)
  · intro w hw
    calc
      inner ℂ (rightShift g x - rightShift g (M.starProjection x)) w =
          inner ℂ (rightShift g (x - M.starProjection x))
            (rightShift g (rightShift g⁻¹ w)) := by rw [map_sub, rightShift_inv]
      _ = inner ℂ (x - M.starProjection x) (rightShift g⁻¹ w) :=
        (rightShift g).inner_map_map _ _
      _ = 0 := M.starProjection_inner_eq_zero x _ (hM _ _ hw)
theorem idempotent_eq_zero_of_coeff_one_eq_zero (a : MonoidAlgebra ℂ G)
    (ha : a * a = a) (hzero : a.coeff 1 = 0) : a = 0 := by
  let E := convolution a
  have hEE (x : Hilbert G) : E (E x) = E x := by
    change (convolution a * convolution a) x = convolution a x
    rw [← map_mul, ha]
  let M : Submodule ℂ (Hilbert G) := (E - 1).ker
  have memM (x : Hilbert G) : x ∈ M ↔ E x = x := by
    change (E - 1) x = 0 ↔ _
    simp only [sub_apply, one_apply_eq_self, sub_eq_zero]
  have hEP (x : Hilbert G) : E (M.starProjection x) = M.starProjection x :=
    (memM _).mp (M.starProjection_apply_mem x)
  have hPE (x : Hilbert G) : M.starProjection (E x) = E x :=
    Submodule.starProjection_eq_self_iff.mpr ((memM _).mpr (hEE x))
  have hM (g : G) (x : Hilbert G) (hx : x ∈ M) : rightShift g x ∈ M := by
    apply (memM _).mpr
    change convolution a (rightShift g x) = rightShift g x
    rw [convolution_rightShift, (memM x).mp hx]
  have hPcomm := projection_rightShift M hM
  have ht : (M.starProjection (delta 1)) 1 = 0 := by
    have h := trace_commute a M.starProjection hPcomm
    change M.starProjection (E (delta 1)) 1 = E (M.starProjection (delta 1)) 1 at h
    rw [hPE, hEP] at h
    rw [← h]
    exact (convolution_delta a 1).trans hzero
  have hPδ : M.starProjection (delta 1) = 0 := by
    apply (inner_self_eq_zero (𝕜 := ℂ)).mp
    rw [M.inner_starProjection_left_eq_right]
    rw [Submodule.starProjection_eq_self_iff.mpr (M.starProjection_apply_mem _)]
    exact (inner_delta _ _).trans ht
  have hPδg (g : G) : M.starProjection (delta g) = 0 := by
    have h := hPcomm g (delta 1)
    rw [rightShift_delta, one_mul, hPδ, map_zero] at h
    exact h
  have hP (x : Hilbert G) : M.starProjection x = 0 := by
    ext g
    have h := M.inner_starProjection_left_eq_right (delta g) x
    rw [hPδg, inner_zero_left, inner_delta] at h
    exact h.symm
  have hEδ : E (delta 1) = 0 := (hPE _).symm.trans (hP _)
  ext g
  change a.coeff g = 0
  rw [← convolution_delta]
  change E (delta 1) g = 0
  rw [hEδ]
  rfl
end TorsionFreeBass.Regular
end
end OAI

end

section
-- Public
open scoped Pointwise Classical
namespace Width
def H1 : Prop :=
  ∀ (H Y : Type) [Group H] [Countable H] [Countable Y] [LinearOrder Y]
    [MulAction H Y] [IsCancelSMul H Y] (_ : Y) (G : SimpleGraph Y) [G.LocallyFinite],
  G.Connected → (∀ (h : H) u v, G.Adj (h•u) (h•v) ↔ G.Adj u v) →
  ∀ (D n : ℕ), 2≤D → (∀ y, Fintype.card (G.neighborSet y)≤D) →
  (4*D^3+D+3)^2≤n → ∀ T : Finset (Finset Y),
  (∀ t∈T, t.card=n+1 ∧ (G.induce (t : Set Y)).Connected) →
  let E := fun k => ⋀[ℂ]^k (Y →₀ ℂ)
  let w := fun k (v : Fin k → Y) => exteriorPower.ιMulti ℂ k (fun i => Finsupp.single (v i) (1:ℂ))
  let S := fun k => Submodule.span ℂ {x | ∃ v : Fin k → Y,
    (Finset.univ.image v ∈ insert ∅ {s : Finset Y | s.Nonempty ∧ ∃ h : H, ∃ t∈T,s⊆h•t}) ∧ w k v=x}
  let a := fun k (h : H) => exteriorPower.map k (Finsupp.lmapDomain ℂ ℂ (fun y : Y => h•y))
  ∀ (d : ∀ k, E (k+1) →ₗ[ℂ] E k),
  (∀ k v, d k (w (k+1) v)=∑ i : Fin (k+1), (-1:ℂ)^i.val • w k (v ∘ i.succAbove)) →
  ∀ (c : S (n+1)) (ψ : E (n+1) →ₗ[ℂ] ℂ) (δ : ℝ), 0<δ →
  ∃ A : ∀ k, E k →ₗ[ℂ] E k, (∀ x, A 0 x=x) ∧
    (∀ k x, x∈S (k+1) → d k (A (k+1) x)=A k (d k x)) ∧
    (∀ k h x, x∈S k → a k h (A k x)=A k (a k h x)) ∧ ‖ψ (A (n+1) c)‖<δ
end Width
end

section
-- Consumer
open Set Finset MeasureTheory OAI OAI.BassTrace
open OAI.BassTrace.Oriented OAI.BassTrace.ChainHomotopy OAI.BassTrace.Sparse
open OAI.BassTrace.Sparse.GraphGeometry
open scoped Pointwise Classical
namespace Width
set_option maxHeartbeats 1000000 in
theorem consume (hh : H1) {H Y : Type} [Group H] [Countable H] [Countable Y] [LinearOrder Y]
    [MulAction H Y] [IsCancelSMul H Y] (y : Y) (G : SimpleGraph Y) [G.LocallyFinite]
    (hg : G.Connected) (ha : ∀ (h : H) u v,G.Adj (h•u) (h•v) ↔ G.Adj u v)
    (D n : ℕ) (hD : 2≤D) (hd : ∀ y,Fintype.card (G.neighborSet y)≤D)
    (hl : volumeThreshold D≤n) (T : Finset (Finset Y))
    (hT : ∀t∈T,t.card=n+1 ∧ (G.induce (t : Set Y)).Connected)
    (K := generatedComplex (H := H) T) (hK : K=generatedComplex (H := H) T := by rfl)
    (hI : (augmentedComplex K).IsInvariant (H := H))
    (ψ : Degree Y (n+1) →ₗ[ℂ] ℂ)
    (hψ : ∀(h : H) x,ψ (relabel (n+1) (fun y=>h•y) x)=ψ x)
    (hψd : ∀x,ψ (d (n+1) x)=0)
    (c : (augmentedComplex K).chains (n+1))
    (hc : (⟨d n c,(augmentedComplex K).d_mem n c.property⟩ : (augmentedComplex K).chains n)
      ∈(augmentedComplex K).relations hI n) : ψ c=0 := by
  subst K
  by_contra hn
  have hp := norm_pos_iff.mpr hn
  have hb := hh H Y y G hg ha D n hD hd hl T hT d d_wedge
  let S := fun k => Submodule.span ℂ {x | ∃ v : Fin k → Y,
    (Finset.univ.image v ∈ insert ∅ {s : Finset Y | s.Nonempty ∧ ∃ h : H, ∃ t∈T,s⊆h•t}) ∧ wedge k v=x}
  have hS k : S k = (augmentedComplex (generatedComplex (H := H) T)).chains k := by
    dsimp [S,Complex.chains,augmentedComplex,generatedComplex,wedge]; congr!
  have hm k (x : (augmentedComplex (generatedComplex (H := H) T)).chains k) : x.val ∈ S k := by rw [hS]; exact x.property
  obtain ⟨A,h0,hchain,hnat,hsmall⟩ := hb ⟨c.val, hm _ c⟩ ψ _ hp
  have he := source_coinvariant_comparison _ hI (fun k => (A k).comp ((augmentedComplex _).chains k).subtype)
    (fun x => h0 x) (fun k x => hchain k x (hm _ x))
    (fun k h x => hnat k h x (hm _ x)) n ψ hψ hψd c hc
  exact (ne_of_lt hsmall) (congrArg norm he)
end Width
end

section
-- MatrixWidth
namespace OAI
open Set MeasureTheory
open Finset MeasureTheory intervalIntegral
noncomputable section
namespace BassTrace.PathChains
open Set Finset Oriented ChainHomotopy Paths Detector Sparse BarycentricChains Sparse.GraphGeometry
open scoped Classical Pointwise BassTrace.Detector
variable {G : Type} [Group G] [Countable G] {ι : Type} [Fintype ι]
lemma totalWeight_zero_of_finite_generatorsWidth (hh : Width.H1)
    (e : GroupMatrix (G := G) (ι := ι)) (he : e*e=e)
    (S : Finset G) (hS : ∀s∈S,s⁻¹∈S) (hgen : Subgroup.closure (S : Set G)=⊤)
    (heS : support e⊆S) (g : G) (hg : ¬IsOfFinOrder g) : totalWeight e g 0=0 := by
  let H := ActingGroup g
  let Y := Vertex g
  have : Countable Y := inferInstanceAs (Countable (Quotient (QuotientGroup.rightRel (Subgroup.zpowers g))))
  have : Countable H := inferInstanceAs (Countable (ActingGroup g))
  let _ : LinearOrder Y := linearOrderOfSTO WellOrderingRel
  let D := max 2 S.card
  let M := volumeThreshold D
  let n := 2*(M+1)
  let K := pathSupport e g n
  let _ : Fact (∀(h : H) s,s∈K.faces → s.map (MulAction.toPerm h).toEmbedding∈K.faces) :=
    ⟨generatedComplex_invariant (topPaths e g n)⟩
  let Γ := supportGraph g S hS
  have hΓ : Γ.Connected := supportGraph_connected g S hS hgen
  have hAut : ∀(h : H) u v,Γ.Adj (h•u) (h•v) ↔ Γ.Adj u v := supportGraph_smul g S hS
  have hK := pathSupport_pure e g S hS heS n
  obtain ⟨β,hβ,hβc,hβl⟩ := exists_complex_beta g hg
  let ψ := cosetCocycle g (M+1) β
  have hInv : (augmentedComplex K).IsInvariant (H := H) := augmentedComplex_invariant
  have hinv (h : H) (c : Degree Y (n+1)) : ψ (relabel (n+1) (fun y=>h•y) c)=ψ c := by
    induction h using Quotient.inductionOn with | _ h =>
      exact cosetCocycle_invariant g (M+1) β hβc hβl h c
  let c : (augmentedComplex K).chains (n+1) := ⟨liftPath e g n,liftPath_mem e g n⟩
  have hT (t) (ht : t∈topPaths e g n) : t.card=n+1 ∧ (Γ.induce (t : Set Y)).Connected := by
    have hcard := topPaths_card e g n ht
    obtain ⟨s,_,hts,hsc,hcon⟩ := hK t (generatedComplex_top_mem _ ht (Finset.card_pos.mp (by omega)))
    exact ⟨hcard, (Finset.eq_of_subset_of_card_le hts (by omega)) ▸ hcon⟩
  have hv : ψ c=0 := Width.consume hh (H := H) (project g 1) Γ hΓ hAut D n (le_max_left _ _)
    (fun v=>by simpa only [SimpleGraph.card_neighborSet_eq_degree] using
      (supportGraph_degree_le g S hS v).trans (le_max_right 2 _)) (by dsimp [n,M]; omega)
    (topPaths e g n) hT K rfl hInv ψ hinv (cosetCocycle_closed g (M+1) β hβ) c (internal_path_cycle e he g M hInv)
  have hp : quotientCocycle g β hβc hβl (M+1) (pathChain e g (2*(M+1)))=0 := by
    rw [←liftPath_quotient]
    exact hv
  rw [quotientCocycle_pairing g β hβc hβl e he hβ (M+1)] at hp
  exact (mul_eq_zero.mp hp).resolve_left (pow_ne_zero _ (inv_ne_zero (by norm_num)))
end BassTrace.PathChains
namespace BassTrace
open scoped Classical BigOperators
lemma classCoefficient_zero_finitely_generatedWidth (hh : Width.H1) {G : Type} [Group G] [Countable G] [Group.FG G]
    {ι : Type} [Fintype ι] (e : Paths.GroupMatrix (G := G) (ι := ι))
    (he : e*e=e) (g : G) (hg : ¬IsOfFinOrder g) :
    classCoefficient g (Matrix.trace e)=0 := by
  obtain ⟨S,hS,hgen,heS⟩ := exists_symmetric_generators e
  rw [←totalWeight_eq_classCoefficient e he]
  exact PathChains.totalWeight_zero_of_finite_generatorsWidth hh e he S hS hgen heS g hg
theorem bassTraceWidth (hh : Width.H1) {G : Type} [Group G] {q : ℕ}
    (e : Matrix (Fin q) (Fin q) (MonoidAlgebra ℂ G))
    (he : e*e=e) (g : G) (hg : ¬IsOfFinOrder g) :
    idempotentTraceCoefficient e g=0 := by
  let K := Subgroup.closure (Paths.support e : Set G)
  have hs : ∀s∈Paths.support e,s∈K := fun _ hs=>Subgroup.subset_closure hs
  let _ : Group.FG K := Group.closure_finset_fg (Paths.support e)
  let _ : Countable K := by
    dsimp [K]
    rw [FreeGroup.closure_eq_range]
    exact (MonoidHom.rangeRestrict_surjective _).countable
  let a := Matrix.trace (restrictMatrix K e)
  change classCoefficient g (Matrix.trace e)=0
  rw [←map_trace_restrict K e hs,classCoefficient_map_subgroup]
  apply sum_conjugacy_invariant_zero a (fun h=>IsConj (h : G) g)
  · intro h k hc
    have hc' := K.subtype.map_isConj hc
    exact ⟨fun hh=>hc'.symm.trans hh,fun hk=>hc'.trans hk⟩
  · intro h hconj
    apply classCoefficient_zero_finitely_generatedWidth hh (restrictMatrix K e)
      (restrictMatrix_idempotent K e he hs) h
    intro ho
    exact hg (hconj.isOfFinOrder (K.subtype.isOfFinOrder ho))
end BassTrace
end
end OAI
end

section
-- RootWidth
namespace OAI
open scoped Classical BigOperators
noncomputable section
namespace TorsionFreeBass
variable {G : Type} [Group G]
lemma matrix_trace_eq_augmentationWidth (hh : Width.H1) (hG : TorsionFree G) {q : ℕ}
    (e : Matrix (Fin q) (Fin q) (MonoidAlgebra ℂ G)) (he : e * e = e) :
    matrixTrace e = augmentation (Matrix.trace e) := by
  let tr := BassTrace.K0.classTrace (Matrix.trace e)
  have htr (c : ConjClasses G) (hc : c ≠ ConjClasses.mk 1) : tr c = 0 := by
    obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective c
    rw [BassTrace.K0.classTrace_apply]
    apply BassTrace.bassTraceWidth hh e he g
    intro hg
    exact hc (congrArg ConjClasses.mk (hG g hg))
  rw [matrixTrace_eq_classCoefficient, ← BassTrace.K0.classTrace_apply,
    ← classTrace_sum]
  symm
  apply Finsupp.sum_eq_single (ConjClasses.mk (1 : G))
  · intro c _ hc
    exact htr c hc
  · simp
lemma scalar_trace_eq_augmentationWidth (hh : Width.H1) (hG : TorsionFree G)
    (e : MonoidAlgebra ℂ G) (he : e * e = e) : canonicalTrace e = augmentation e := by
  let b : Matrix (Fin 1) (Fin 1) (MonoidAlgebra ℂ G) := fun _ _ => e
  have hb : b * b = b := by
    apply Matrix.ext
    intro i j
    change (∑ _ : Fin 1, e * e) = e
    simpa using he
  simpa [matrixTrace, Matrix.trace, Matrix.diag, b] using matrix_trace_eq_augmentationWidth hh hG b hb
theorem complex_idempotentWidth (hh : Width.H1) (hG : TorsionFree G)
    (e : MonoidAlgebra ℂ G) (he : e * e = e) : e = 0 ∨ e = 1 := by
  have ht : e.coeff 1 = augmentation e := scalar_trace_eq_augmentationWidth hh hG e he
  have haug : augmentation e * (augmentation e - 1) = 0 := by
    rw [mul_sub, mul_one, ← map_mul, he, sub_self]
  rcases mul_eq_zero.mp haug with hz | ho
  · exact Or.inl (Regular.idempotent_eq_zero_of_coeff_one_eq_zero e he (ht.trans hz))
  · have ht' : e.coeff 1 = 1 := ht.trans (sub_eq_zero.mp ho)
    have hc : (1 - e) * (1 - e) = 1 - e := by
      rw [sub_mul, mul_sub, mul_sub, one_mul, one_mul, mul_one, he]
      abel
    have hz : (1 - e).coeff 1 = 0 := by simp [ht']
    exact Or.inr (sub_eq_zero.mp
      (Regular.idempotent_eq_zero_of_coeff_one_eq_zero (1 - e) hc hz)).symm
end TorsionFreeBass
end
end OAI
end

theorem OMA.solution : OMA.R_mo_178849_R1.H4 := by
  intro hw G _ hG e he
  exact OAI.TorsionFreeBass.complex_idempotentWidth hw hG e he

/- Upstream license (OpenAI/math):
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
