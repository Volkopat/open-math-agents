import OMAReductions.R_SidorenkoConjecture_sidorenko_conjecture_graphon_R1_H1_R1_H1_R1_H1_R1_H1_R1
import Mathlib
/-! Adapted from openai/math@3344da59991ed94f9ba711217b29c1d760badfa6 (Apache-2.0). -/
namespace OAI
namespace SidorenkoCounterexample
def faces : Fin 22 → Finset (Fin 13) := ![
  {0,1,3}, {0,1,9}, {0,2,3}, {0,2,9}, {1,3,10}, {1,7,10},
  {1,7,12}, {1,9,12}, {2,3,4}, {2,4,9}, {3,4,11}, {3,10,11},
  {4,8,9}, {4,8,11}, {5,6,7}, {5,6,11}, {5,7,10}, {5,10,11},
  {6,7,12}, {6,8,11}, {6,8,12}, {8,9,12}]
abbrev PatternVertex := Fin 13 ⊕ Fin 22
def incidence : PatternVertex → PatternVertex → Prop
  | .inl i, .inr j => i ∈ faces j
  | .inr j, .inl i => i ∈ faces j
  | _, _ => False
def H : SimpleGraph PatternVertex where
  Adj := incidence
  symm.symm := by intro u v; cases u <;> cases v <;> simp [incidence]
  loopless.irrefl := by intro u; cases u <;> simp [incidence]
end SidorenkoCounterexample
end OAI
namespace OAI
namespace SidorenkoCounterexample
open scoped BigOperators
open Module
section SubspaceCount
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Fintype K] [Finite V]
abbrev DimSubspace (K V : Type*) [Field K] [AddCommGroup V] [Module K V] (k : ℕ) :=
  {U : Submodule K V // finrank K U = k}
abbrev IndependentTuple (K V : Type*) [Field K] [AddCommGroup V] [Module K V] (k : ℕ) :=
  {s : Fin k → V // LinearIndependent K s}
omit [Fintype K] in
 theorem tuple_spans (k : ℕ) (U : DimSubspace K V k)
    (s : IndependentTuple K U.val k) :
    Submodule.span K (Set.range (fun i => (s.val i : V))) = U.val := by
  have hs : Submodule.span K (Set.range s.val) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_span_eq_card s.property, Fintype.card_fin, U.property]
  have h := congrArg (Submodule.map U.val.subtype) hs
  simpa only [Submodule.map_span, Submodule.map_top, Submodule.range_subtype,
    ← Set.range_comp, Function.comp_def, Submodule.subtype_apply] using h
noncomputable def tupleForget {k : ℕ}
    (s : Σ U : DimSubspace K V k, IndependentTuple K U.val k) :
    IndependentTuple K V k :=
  ⟨fun i => (s.2.val i : V), s.2.property.map' s.1.val.subtype
    (Submodule.ker_subtype _)⟩
omit [Fintype K] in
 theorem tupleForget_bijective (k : ℕ) :
    Function.Bijective (tupleForget (K := K) (V := V) (k := k)) := by
  constructor
  · rintro ⟨U,s⟩ ⟨W,t⟩ heq
    have hval : (fun i => (s.val i : V)) = (fun i => (t.val i : V)) :=
      congrArg Subtype.val heq
    have hUW : U = W := by
      apply Subtype.ext
      rw [← tuple_spans k U s, ← tuple_spans k W t, hval]
    subst W
    congr 1
    apply Subtype.ext
    funext i
    exact Subtype.ext (congrFun hval i)
  · intro s
    let U : DimSubspace K V k := ⟨Submodule.span K (Set.range s.val), by
      rw [finrank_span_eq_card s.property, Fintype.card_fin]⟩
    let t : Fin k → U.val := fun i => ⟨s.val i, Submodule.subset_span ⟨i,rfl⟩⟩
    have ht : LinearIndependent K t := LinearIndependent.of_comp U.val.subtype s.property
    refine ⟨⟨U,⟨t,ht⟩⟩, ?_⟩
    rfl
 theorem subspace_count_identity (k : ℕ) (hk : k ≤ finrank K V) :
    Nat.card (DimSubspace K V k) *
      (∏ i : Fin k, (Fintype.card K ^ k - Fintype.card K ^ i.val)) =
        ∏ i : Fin k, (Fintype.card K ^ finrank K V - Fintype.card K ^ i.val) := by
  classical
  let : Fintype (DimSubspace K V k) := Fintype.ofFinite _
  have h := Nat.card_congr (Equiv.ofBijective _ (tupleForget_bijective (K := K) (V := V) k))
  rw [Nat.card_sigma] at h
  have hcard (U : DimSubspace K V k) : Nat.card (IndependentTuple K U.val k) =
      ∏ i : Fin k, (Fintype.card K ^ k - Fintype.card K ^ i.val) := by
    rw [IndependentTuple, card_linearIndependent (by rw [U.property]), U.property]
  simp only [hcard, Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Nat.cast_id] at h
  rw [Nat.card_eq_fintype_card, h]
  exact card_linearIndependent hk
 theorem independent_tuple_count_pos (k : ℕ) :
    0 < ∏ i : Fin k, (Fintype.card K ^ k - Fintype.card K ^ i.val) := by
  apply Finset.prod_pos
  intro i _
  apply Nat.sub_pos_of_lt
  exact Nat.pow_lt_pow_right Fintype.one_lt_card i.isLt
 theorem subspace_count_real (k : ℕ) (hk : k ≤ finrank K V) :
    (Nat.card (DimSubspace K V k) : ℝ) =
      ∏ i : Fin k, ((Fintype.card K : ℝ) ^ finrank K V - (Fintype.card K : ℝ)^i.val) /
        ((Fintype.card K : ℝ)^k - (Fintype.card K : ℝ)^i.val) := by
  have h := subspace_count_identity (K := K) (V := V) k hk
  have hp := independent_tuple_count_pos (K := K) k
  have hle (i : Fin k) : Fintype.card K ^ i.val ≤ Fintype.card K ^ k :=
    Nat.pow_le_pow_right (by exact Fintype.card_pos) i.isLt.le
  have hle' (i : Fin k) : Fintype.card K ^ i.val ≤ Fintype.card K ^ finrank K V :=
    Nat.pow_le_pow_right (by exact Fintype.card_pos) (i.isLt.le.trans hk)
  have hr : (Nat.card (DimSubspace K V k) : ℝ) *
      (∏ i : Fin k, ((Fintype.card K : ℝ)^k - (Fintype.card K : ℝ)^i.val)) =
      ∏ i : Fin k, ((Fintype.card K : ℝ)^finrank K V - (Fintype.card K : ℝ)^i.val) := by
    have hc := congrArg (fun n : ℕ => (n : ℝ)) h
    simpa only [Nat.cast_mul, Nat.cast_prod, Nat.cast_sub (hle _),
      Nat.cast_sub (hle' _), Nat.cast_pow] using hc
  have hpr : (0 : ℝ) < ∏ i : Fin k, ((Fintype.card K : ℝ)^k -
      (Fintype.card K : ℝ)^i.val) := by
    have hpc : (0 : ℝ) < ((∏ i : Fin k, (Fintype.card K ^ k -
        Fintype.card K ^ i.val)) : ℕ) := by exact_mod_cast hp
    simpa only [Nat.cast_prod, Nat.cast_sub (hle _), Nat.cast_pow] using hpc
  rw [Finset.prod_div_distrib]
  exact (eq_div_iff hpr.ne').mpr hr
end SubspaceCount
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section FormCount
variable (K : Type*) [Field K]
def symmetricSubmodule (D : ℕ) : Submodule K (Matrix (Fin D) (Fin D) K) where
  carrier := {M | M.IsSymm}
  zero_mem' := Matrix.isSymm_zero
  add_mem' := fun hM hN => hM.add hN
  smul_mem' := fun a _ hM => hM.smul a
abbrev SymMatrix (D : ℕ) := symmetricSubmodule K D
def symMatrixCoordinates (D : ℕ) : SymMatrix K D ≃ (Sym2 (Fin D) → K) :=
  (Equiv.subtypeEquiv (Equiv.refl (Matrix (Fin D) (Fin D) K)) (fun M => by
    change M.IsSymm ↔ ∀ i j, M i j = M j i
    constructor
    · intro h i j
      exact (h.apply i j).symm
    · intro h
      ext i j
      exact h j i)).trans Sym2.lift
 theorem symMatrix_card [Fintype K] (D : ℕ) :
    Nat.card (SymMatrix K D) = Fintype.card K ^ ((D+1).choose 2) := by
  rw [Nat.card_congr (symMatrixCoordinates K D), Nat.card_fun,
    Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Sym2.card, Fintype.card_fin]
variable (V : Type*) [AddCommGroup V] [Module K V]
abbrev SymForm := {B : LinearMap.BilinForm K V // B.IsSymm}
noncomputable def symFormMatrix [FiniteDimensional K V] :
    SymForm K V ≃ SymMatrix K (finrank K V) :=
  Equiv.subtypeEquiv (LinearMap.BilinForm.toMatrix (Module.finBasis K V)).toEquiv
    (fun B => (B.isSymm_toMatrix_iff_isSymm (Module.finBasis K V)).symm)
instance symForm_finite [Finite K] [FiniteDimensional K V] : Finite (SymForm K V) :=
  Finite.of_equiv (SymMatrix K (finrank K V)) (symFormMatrix K V).symm
variable {K V}
def formRadicalEquiv (U : Submodule K V) :
    {B : SymForm K V // U ≤ B.val.ker} ≃ SymForm K (V ⧸ U) where
  toFun B := ⟨LinearMap.IsRefl.liftQ₂ B.val.val U B.val.property.isRefl B.property, by
    constructor
    intro x y
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      induction y using Submodule.Quotient.induction_on with
      | H y => exact B.val.property.eq x y⟩
  invFun C := ⟨⟨C.val.compl₁₂ U.mkQ U.mkQ, by
    constructor
    intro x y
    exact C.property.eq _ _⟩, by
      intro x hx
      apply LinearMap.mem_ker.mpr
      ext y
      change C.val (U.mkQ x) (U.mkQ y) = 0
      simp [(Submodule.Quotient.mk_eq_zero U).mpr hx]⟩
  left_inv B := by
    apply Subtype.ext
    apply Subtype.ext
    ext x y
    rfl
  right_inv C := by
    apply Subtype.ext
    ext x y
    rfl
end FormCount
end SidorenkoCounterexample
end OAI
namespace OAI
namespace SidorenkoCounterexample
open Module
section LagrangianCharts
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [FiniteDimensional K V]
def formGraph (U : Submodule K V) (B : LinearMap.BilinForm K U) :
    Submodule K (V × Module.Dual K V) where
  carrier := {p | ∃ u : U, u.val = p.1 ∧ p.2.comp U.subtype = B u}
  zero_mem' := ⟨0, rfl, by simp⟩
  add_mem' := by
    rintro p q ⟨u,hu,hf⟩ ⟨v,hv,hg⟩
    refine ⟨u+v, by simp [hu,hv], ?_⟩
    change (p.2+q.2).comp U.subtype = B (u+v)
    ext w
    simp only [LinearMap.add_comp, LinearMap.add_apply, map_add]
    exact congrArg (fun l : Module.Dual K U => l w) (congrArg₂ (·+·) hf hg)
  smul_mem' := by
    rintro a p ⟨u,hu,hf⟩
    refine ⟨a • u, by simp [hu], ?_⟩
    change (a • p.2).comp U.subtype = B (a • u)
    rw [map_smul, LinearMap.smul_comp, hf]
omit [FiniteDimensional K V] in
 theorem formGraph_fst_range (U : Submodule K V) (B : LinearMap.BilinForm K U) :
    (formGraph U B).map (LinearMap.fst K V (Module.Dual K V)) = U := by
  ext x
  constructor
  · rintro ⟨p,⟨u,hu,_⟩,hp⟩
    have hp' : p.1 = x := hp
    rw [← hp', ← hu]
    exact u.property
  · intro hx
    obtain ⟨f,hf⟩ := (Subspace.dualRestrict_surjective (W := U)) (B ⟨x,hx⟩)
    exact ⟨(x,f),⟨⟨x,hx⟩,rfl,hf⟩,rfl⟩
def formGraphProjection (U : Submodule K V) (B : LinearMap.BilinForm K U) :
    formGraph U B →ₗ[K] U where
  toFun p := ⟨p.val.1, by obtain ⟨u,hu,_⟩ := p.property; exact hu ▸ u.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
omit [FiniteDimensional K V] in
 theorem formGraphProjection_surj (U : Submodule K V) (B : LinearMap.BilinForm K U) :
    Function.Surjective (formGraphProjection U B) := by
  intro u
  obtain ⟨f,hf⟩ := Subspace.dualRestrict_surjective (W := U) (B u)
  exact ⟨⟨(u.val,f),u,rfl,hf⟩,rfl⟩
noncomputable def graphVerticalEquiv (U : Submodule K V) (B : LinearMap.BilinForm K U) :
    U.dualAnnihilator ≃ₗ[K] (formGraphProjection U B).ker where
  toFun f := ⟨⟨(0,f.val),0,rfl, by
    ext u
    simpa using ((Submodule.mem_dualAnnihilator (W := U) f.val).mp f.property) u u.property⟩, rfl⟩
  invFun p := ⟨p.val.val.2, by
    obtain ⟨u,hu,hf⟩ := p.val.property
    have hx : p.val.val.1 = 0 := congrArg Subtype.val p.property
    have hu0 : u = 0 := Subtype.ext (hu.trans hx)
    apply (Submodule.mem_dualAnnihilator (W := U) p.val.val.2).mpr
    intro x hxU
    have hf' := congrArg (fun l : Module.Dual K U => l ⟨x,hxU⟩) hf
    simpa [hu0] using hf'⟩
  left_inv _ := rfl
  right_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact (congrArg Subtype.val p.property).symm
    · rfl
  map_add' f g := by
    apply Subtype.ext
    apply Subtype.ext
    simp
  map_smul' a f := by
    apply Subtype.ext
    apply Subtype.ext
    simp
 theorem surjective_finrank_eq {E F : Type*} [AddCommGroup E] [Module K E]
    [AddCommGroup F] [Module K F] [FiniteDimensional K E]
    (p : E →ₗ[K] F) (hp : Function.Surjective p) :
    finrank K E = finrank K F + finrank K p.ker := by
  have h := LinearMap.finrank_range_add_finrank_ker p
  rw [LinearMap.range_eq_top.mpr hp, finrank_top] at h
  exact h.symm
 theorem formGraph_finrank (U : Submodule K V) (B : LinearMap.BilinForm K U) :
    finrank K (formGraph U B) = finrank K V := by
  have h := surjective_finrank_eq (K := K) (E := formGraph U B) (F := U)
    (formGraphProjection U B) (formGraphProjection_surj U B)
  rw [← (graphVerticalEquiv U B).finrank_eq] at h
  exact h.trans (Subspace.finrank_add_finrank_dualAnnihilator_eq U)
end LagrangianCharts
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section NormalCoordinates
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E) (L : Submodule K E)
 theorem self_orthogonal_twice_finrank (hω : ω.Nondegenerate)
    (hL : ω.orthogonal L = L) : 2 * finrank K L = finrank K E := by
  have h := LinearMap.BilinForm.finrank_orthogonal hω L
  rw [hL] at h
  have hle := Submodule.finrank_le L
  omega
end NormalCoordinates
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section PairCounts
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
end PairCounts
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section LinearGlue
variable {K E V : Type*} [Field K] [AddCommGroup E] [Module K E]
  [AddCommGroup V] [Module K V]
end LinearGlue
section PairLift
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable (U W : Submodule K V) (B : LinearMap.BilinForm K U) (C : LinearMap.BilinForm K W)
end PairLift
end SidorenkoCounterexample
end OAI
namespace OAI
namespace SidorenkoCounterexample
open scoped BigOperators
open Module
section UniformMaps
variable {K U W : Type*} [Field K] [AddCommGroup U] [Module K U]
  [AddCommGroup W] [Module K W] [Finite U] [Finite W]
noncomputable def preimageFiberEquiv (f : U →ₗ[K] W) (P : W → Prop) :
    {x : U // P (f x)} ≃ Σ y : {y : W // P y}, {x : U // f x = y.val} where
  toFun x := ⟨⟨f x.val,x.property⟩,⟨x.val,rfl⟩⟩
  invFun y := ⟨y.2.val, by simpa only [y.2.property] using y.1.property⟩
  left_inv _ := rfl
  right_inv y := by
    rcases y with ⟨⟨y,hy⟩,⟨x,hx⟩⟩
    cases hx
    rfl
 theorem surjective_linear_preimage_card (f : U →ₗ[K] W)
    (hf : Function.Surjective f) (P : W → Prop) :
    Nat.card {x : U // P (f x)} = Nat.card {y : W // P y} * Nat.card f.ker := by
  classical
  let : Fintype U := Fintype.ofFinite _
  let : Fintype W := Fintype.ofFinite _
  have hcard (y : W) : Nat.card {x : U // f x = y} = Nat.card f.ker := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    simpa [Fintype.card_subtype, LinearMap.mem_ker] using
      AddMonoidHom.card_fiber_eq_of_mem_range f (hf y) (hf 0)
  rw [Nat.card_congr (preimageFiberEquiv f P), Nat.card_sigma]
  simp only [hcard, Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Nat.card_eq_fintype_card, Nat.cast_id]
 theorem surjective_linear_card (f : U →ₗ[K] W) (hf : Function.Surjective f) :
    Nat.card U = Nat.card W * Nat.card f.ker := by
  have h := surjective_linear_preimage_card f hf (fun _ => True)
  simpa using h
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
end UniformMaps
section FiniteUnion
variable {T Ω : Type*} [Fintype T] [Finite Ω] [Nonempty Ω]
end FiniteUnion
section GoodMinors
variable {K V : Type*} [Field K] [Fintype K] [AddCommGroup V] [Module K V] [Finite V]
def symmetricFormSubmodule : Submodule K (LinearMap.BilinForm K V) where
  carrier := {B | B.IsSymm}
  zero_mem' := ⟨fun _ _ => rfl⟩
  add_mem' := fun hB hC => hB.add hC
  smul_mem' := fun a _ hB => hB.smul a
noncomputable instance : AddCommGroup (SymForm K V) := by
  change AddCommGroup (symmetricFormSubmodule (K := K) (V := V))
  exact Submodule.addCommGroup (R := K) (M := LinearMap.BilinForm K V) (symmetricFormSubmodule (K := K) (V := V))
noncomputable instance : Module K (SymForm K V) := by
  change Module K (symmetricFormSubmodule (K := K) (V := V))
  exact Submodule.module (symmetricFormSubmodule (K := K) (V := V))
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
end GoodMinors
end SidorenkoCounterexample
namespace SidorenkoCounterexample
section FormGluing
variable {K E V : Type*} [Field K] [AddCommGroup E] [Module K E]
    [AddCommGroup V] [Module K V]
 theorem symmetric_form_descend (f : E →ₗ[K] V) (B : LinearMap.BilinForm K E)
    (hB : B.IsSymm) (hk : f.ker ≤ B.ker) :
    ∃ C : LinearMap.BilinForm K V, C.IsSymm ∧ C.compl₁₂ f f = B := by
  obtain ⟨p,hp⟩ := f.range.subtype.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr f.range.subtype_injective)
  let e := f.quotKerEquivRange
  let Q := LinearMap.IsRefl.liftQ₂ B f.ker hB.isRefl hk
  let g : V →ₗ[K] (E ⧸ f.ker) := e.symm.toLinearMap.comp p
  have hg (x : E) : g (f x) = f.ker.mkQ x := by
    apply e.injective
    change e (e.symm (p (f x))) = e (f.ker.mkQ x)
    rw [e.apply_symm_apply]
    have hp' := LinearMap.congr_fun hp (f.rangeRestrict x)
    exact hp'
  refine ⟨Q.compl₁₂ g g, ?_, ?_⟩
  · constructor
    intro x y
    change Q (g x) (g y) = Q (g y) (g x)
    generalize g x = a, g y = b
    induction a using Submodule.Quotient.induction_on with
    | H a =>
      induction b using Submodule.Quotient.induction_on with
      | H b => exact hB.eq a b
  · apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    change Q (g (f x)) (g (f y)) = B x y
    rw [hg,hg]
    rfl
variable (U W : Submodule K V) (B : LinearMap.BilinForm K U) (C : LinearMap.BilinForm K W)
variable (p : U →ₗ[K] ↥(U ⊓ W)) (q : W →ₗ[K] ↥(U ⊓ W))
end FormGluing
section CyclicDifference
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
end CyclicDifference
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section PlantedDifference
variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]
noncomputable def symFormPull (f : V →ₗ[K] W) : SymForm K W →ₗ[K] SymForm K V where
  toFun B := ⟨B.val.compl₁₂ f f, by constructor; intro x y; exact B.property.eq (f x) (f y)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
theorem symFormPull_surjective (f : V →ₗ[K] W) (hf : Function.Injective f) :
    Function.Surjective (symFormPull f) := by
  intro B
  obtain ⟨C,hCs,hC⟩ := symmetric_form_descend f B.val B.property
    (by rw [LinearMap.ker_eq_bot.mpr hf]; exact bot_le)
  exact ⟨⟨C,hCs⟩,Subtype.ext hC⟩
variable (A₀ A₁ A₂ : Submodule K V)
end PlantedDifference
end SidorenkoCounterexample
namespace SidorenkoCounterexample
section ConstraintDensity
variable {K U W X : Type*} [Field K] [AddCommGroup U] [Module K U]
  [AddCommGroup W] [Module K W] [AddCommGroup X] [Module K X]
  [Finite U] [Finite W] [Finite X]
end ConstraintDensity
section ProductDensity
variable {U W X : Type*} [Finite U] [Finite W] [Finite X]
end ProductDensity
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section OriginalDifferences
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable (A₀ A₁ A₂ : Submodule K V)
end OriginalDifferences
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ActualLiftCost
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype K] [Finite V]
variable (A₀ A₁ A₂ : Submodule K V)
end ActualLiftCost
end SidorenkoCounterexample
end OAI
namespace OAI
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section Bounds
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype K] [Finite V]
theorem subspace_count_lower (k : ℕ) (hk : k ≤ finrank K V) :
    (Fintype.card K : ℝ)^(k*(finrank K V-k)) ≤ Nat.card (DimSubspace K V k) := by
  rw [subspace_count_real k hk]
  let q : ℝ := Fintype.card K
  have hq : 1 < q := by
    dsimp [q]
    exact_mod_cast (Fintype.one_lt_card (α := K))
  have hq0 : 0 < q := by linarith
  have hfac (i : Fin k) : q^(finrank K V-k) ≤
      (q^finrank K V-q^i.val)/(q^k-q^i.val) := by
    have hd : 0 < q^k-q^i.val := sub_pos.mpr (pow_lt_pow_right₀ hq i.isLt)
    have hid : q^finrank K V = q^(finrank K V-k)*q^k := by
      rw [←pow_add,Nat.sub_add_cancel hk]
    apply (le_div_iff₀ hd).mpr
    rw [hid]
    have hp : 1 ≤ q^(finrank K V-k) := one_le_pow₀ hq.le
    have hm := mul_le_mul_of_nonneg_right hp (pow_nonneg hq0.le i.val)
    nlinarith
  calc
    q^(k*(finrank K V-k)) = ∏ _i : Fin k, q^(finrank K V-k) := by
      simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,←pow_mul]
      rw [Nat.mul_comm]
    _ ≤ _ := Finset.prod_le_prod (fun _ _ => pow_nonneg hq0.le _) (fun i _ => hfac i)
end Bounds
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ContainingSubspaces
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable [Fintype K] [Finite V]
end ContainingSubspaces
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section TripleSubspaces
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [FiniteDimensional K V]
variable [Fintype K]
end TripleSubspaces
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section SpanCount
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable [Fintype K]
end SpanCount
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section PlantedSubspaceExponent
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype K]
end PlantedSubspaceExponent
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section DualPlantedBases
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
end DualPlantedBases
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section NullityAll
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype K] [Finite V]
end NullityAll
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section NullityAllLift
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype K] [Finite V]
variable (A₀ A₁ A₂ : Submodule K V)
end NullityAllLift
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section DualProfileLift
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {r p₀ p₁ p₂ n : ℕ}
end DualProfileLift
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ProfileConstraints
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
end ProfileConstraints
section DualLiftSum
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [Fintype K] [Finite V]
end DualLiftSum
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section CanonicalCoding
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
end CanonicalCoding
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ExtraFeasibility
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
end ExtraFeasibility
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section CanonicalParameterCount
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
abbrev FourDims (d : ℕ) := Fin (d+1) × Fin (d+1) × Fin (d+1) × Fin (d+1)
def BaseFeasible (r s₀ s₁ s₂ : ℕ) {d : ℕ} (θ : FourDims d) : Prop :=
  r ≤ θ.2.2.2.val ∧ θ.1.val+θ.2.1.val ≤ r ∧ θ.1.val+θ.2.2.1.val ≤ r ∧
  θ.2.1.val+θ.2.2.1.val ≤ r ∧ θ.2.2.2.val+(θ.1.val+θ.2.1.val+θ.2.2.1.val) ≤ 3*r ∧
  θ.1.val ≤ s₀ ∧ θ.2.1.val ≤ s₁ ∧ θ.2.2.1.val ≤ s₂ ∧
  (s₀-θ.1.val)+2*r ≤ d+θ.1.val ∧ (s₁-θ.2.1.val)+2*r ≤ d+θ.2.1.val ∧
  (s₂-θ.2.2.1.val)+2*r ≤ d+θ.2.2.1.val ∧
  (d-θ.2.2.2.val)+2*r ≤ d+θ.1.val ∧ (d-θ.2.2.2.val)+2*r ≤ d+θ.2.1.val ∧
  (d-θ.2.2.2.val)+2*r ≤ d+θ.2.2.1.val
abbrev BaseParameters (d r s₀ s₁ s₂ : ℕ) := {θ : FourDims d // BaseFeasible r s₀ s₁ s₂ θ}
end CanonicalParameterCount
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
noncomputable instance baseParametersFintype (d r s₀ s₁ s₂ : ℕ) : Fintype (BaseParameters d r s₀ s₁ s₂) := Fintype.ofFinite _
section CanonicalNumericalBound
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype K] [Finite V]
end CanonicalNumericalBound
end SidorenkoCounterexample
end OAI
namespace OAI
namespace SidorenkoCounterexample
open Module
section Reduction
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E) (S : Submodule K E)
end Reduction
section IsotropicExtension
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Finite E]
variable (ω : LinearMap.BilinForm K E)
end IsotropicExtension
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section QuotientExtension
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E) (S : Submodule K E)
end QuotientExtension
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ReductionLaws
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E) (S : Submodule K E)
variable [FiniteDimensional K E]
variable [Finite E]
end ReductionLaws
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section IsotropicTransitivity
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E] [Finite E]
variable (ω : LinearMap.BilinForm K E)
end IsotropicTransitivity
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section TransversePairs
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E)
end TransversePairs
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section PairTransitivity
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E)
end PairTransitivity
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section PairReduction
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E) (S : Submodule K E)
variable [FiniteDimensional K E]
end PairReduction
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section OrderedPairTransitivity
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E] [Finite E]
variable (ω : LinearMap.BilinForm K E)
end OrderedPairTransitivity
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section TripleBlocks
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E)
end TripleBlocks
end SidorenkoCounterexample
end OAI
namespace OAI
namespace SidorenkoCounterexample
open Module
section GeneralIsometry
variable {K E F : Type*} [Field K] [AddCommGroup E] [Module K E]
  [AddCommGroup F] [Module K F]
theorem orthogonal_map_isometry_between
    (ω : LinearMap.BilinForm K E) (η : LinearMap.BilinForm K F)
    (e : E ≃ₗ[K] F) (he : ∀ x y, η (e x) (e y) = ω x y)
    (U : Submodule K E) :
    η.orthogonal (U.map e.toLinearMap) = (ω.orthogonal U).map e.toLinearMap := by
  ext x
  constructor
  · intro hx
    refine ⟨e.symm x,?_,e.apply_symm_apply x⟩
    intro u hu
    rw [← he,e.apply_symm_apply]
    exact hx (e u) ⟨u,hu,rfl⟩
  · rintro ⟨y,hy,rfl⟩ _ ⟨u,hu,rfl⟩
    change η (e u) (e y) = 0
    rw [he]
    exact hy u hu
end GeneralIsometry
section Horizontal
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
end Horizontal
section TripleOneBlock
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E)
end TripleOneBlock
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section OrthogonalReduction
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E)
end OrthogonalReduction
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ReductionInStages
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E) (ha : ω.IsAlt)
end ReductionInStages
end SidorenkoCounterexample
namespace SidorenkoCounterexample
section ReductionIsometry
variable {K E F : Type*} [Field K] [AddCommGroup E] [Module K E]
  [AddCommGroup F] [Module K F]
end ReductionIsometry
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section OrthogonalIsometries
variable {K E F : Type*} [Field K] [AddCommGroup E] [Module K E]
  [AddCommGroup F] [Module K F] [FiniteDimensional K E] [FiniteDimensional K F]
end OrthogonalIsometries
end SidorenkoCounterexample
namespace SidorenkoCounterexample
section SplitHelpers
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
end SplitHelpers
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section TripleBlockData
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E)
end TripleBlockData
end SidorenkoCounterexample
namespace SidorenkoCounterexample
section MapTransport
variable {K E F E' F' : Type*} [Field K]
  [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]
  [AddCommGroup E'] [Module K E'] [AddCommGroup F'] [Module K F']
end MapTransport
open Module
section TripleOneBlockLift
variable {K E F : Type*} [Field K]
  [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]
  [FiniteDimensional K E] [FiniteDimensional K F]
end TripleOneBlockLift
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ReductionIntersections
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E) (S : Submodule K E)
end ReductionIntersections
section PairSum
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E)
end PairSum
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ClassificationPredicates
variable {K E F : Type*} [Field K]
  [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]
end ClassificationPredicates
section ResidualClassificationStep
variable {K E F : Type*} [Field K]
  [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]
  [FiniteDimensional K E] [FiniteDimensional K F]
end ResidualClassificationStep
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section FullClassification
variable {K E F : Type*} [Field K]
  [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]
  [FiniteDimensional K E] [FiniteDimensional K F]
end FullClassification
end SidorenkoCounterexample
end OAI
namespace OAI
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section NormSphere
variable {K E : Type*} [Field K] [Fintype K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E] [Finite E]
end NormSphere
section Isometries
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]
def BilinAut (B : LinearMap.BilinForm K E) :=
  {e : E ≃ₗ[K] E // ∀ x y, B (e x) (e y) = B x y}
instance (B : LinearMap.BilinForm K E) [Finite E] : Finite (BilinAut B) := by
  apply Finite.of_injective (fun e : BilinAut B => (e.val : E → E))
  intro e f h
  apply Subtype.ext
  exact LinearEquiv.ext (congrFun h)
variable [Finite E]
variable [Fintype K] [Invertible (2 : K)]
end Isometries
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section FormOrbits
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]
variable [Fintype K] [Finite E]
abbrev FormOrbit (B : LinearMap.BilinForm K E) :=
  {C : LinearMap.BilinForm K E // ∃ e : E ≃ₗ[K] E, C = B.comp e.toLinearMap e.toLinearMap}
instance linearAut_finite : Finite (E ≃ₗ[K] E) :=
  Finite.of_injective (fun e : E ≃ₗ[K] E => (e : E → E))
    (fun _ _ h => LinearEquiv.ext (congrFun h))
instance formOrbit_finite (B : LinearMap.BilinForm K E) : Finite (FormOrbit B) :=
  Finite.of_injective (fun C : FormOrbit B => fun x y => C.val x y) (by
    intro C D h
    apply Subtype.ext
    ext x y
    exact congrFun (congrFun h x) y)
variable [Invertible (2 : K)]
end FormOrbits
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section TransverseForms
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
end TransverseForms
section TransverseTripleCoordinates
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E)
end TransverseTripleCoordinates
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section FixedPairOrbit
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E) (L M N : Submodule K E)
abbrev FixedPairOrbit := {N' : Submodule K E //
  ∃ e : E ≃ₗ[K] E, (∀ x y, ω (e x) (e y) = ω x y) ∧
    L.map e.toLinearMap = L ∧ M.map e.toLinearMap = M ∧ N.map e.toLinearMap = N'}
variable [FiniteDimensional K E]
variable [Fintype K] [Finite E] [Invertible (2 : K)]
end FixedPairOrbit
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section UniformCountingBounds
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Fintype K] [Finite V]
end UniformCountingBounds
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section FullTripleOrbit
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E)
abbrev SymplecticLagrangian := {L : Submodule K E // ω.orthogonal L = L}
variable [FiniteDimensional K E]
end FullTripleOrbit
section CanonicalTripleMass
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Fintype K] [Finite V]
end CanonicalTripleMass
end SidorenkoCounterexample
end OAI
namespace OAI
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section GenericCounts
variable {K E F : Type*} [Field K] [AddCommGroup E] [Module K E]
  [AddCommGroup F] [Module K F]
noncomputable def symplecticLagrangianEquiv
    (ω : LinearMap.BilinForm K E) (η : LinearMap.BilinForm K F)
    (e : E ≃ₗ[K] F) (he : ∀ x y, η (e x) (e y) = ω x y) :
    SymplecticLagrangian ω ≃ SymplecticLagrangian η :=
  (Submodule.orderIsoMapComap e).toEquiv.subtypeEquiv (by
    intro U
    change ω.orthogonal U = U ↔ η.orthogonal (U.map e.toLinearMap) = U.map e.toLinearMap
    rw [orthogonal_map_isometry_between ω η e he]
    exact (Submodule.orderIsoMapComap e).injective.eq_iff.symm)
variable [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
end GenericCounts
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section IsotropicCounts
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
  [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
end IsotropicCounts
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section AvoidanceCounts
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
  [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
end AvoidanceCounts
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ContainmentAvoidance
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E)
variable [Fintype K] [Finite E]
end ContainmentAvoidance
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section CommonSpaceLift
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E) (S : Submodule K E)
end CommonSpaceLift
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section Decompositions
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable [Fintype K] [Finite E]
end Decompositions
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section TripleDecompositions
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable [Finite E]
variable [Fintype K]
end TripleDecompositions
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section UniformCounts
variable {A B C D E F : Type*}
end UniformCounts
section ExactPairs
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E) (S L M A B : Submodule K E)
end ExactPairs
end SidorenkoCounterexample
end OAI
namespace OAI
namespace SidorenkoCounterexample
open Module
section PairSpaceFacts
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
end PairSpaceFacts
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section GenericTransverseMass
variable {K E F : Type*} [Field K]
  [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]
variable [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
end GenericTransverseMass
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ResidualTransversality
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E)
end ResidualTransversality
section LagrangianTripleOrbit
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E) (L M N : SymplecticLagrangian ω)
end LagrangianTripleOrbit
section AvoidanceTripleCount
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
  [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E) (S : Submodule K E)
variable (ha : ω.IsAlt) (hω : ω.Nondegenerate) (hS : S ≤ ω.orthogonal S)
end AvoidanceTripleCount
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section AvoidanceTripleBound
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
  [Fintype K] [Finite E] [Invertible (2 : K)]
variable (ω : LinearMap.BilinForm K E) (S : Submodule K E)
end AvoidanceTripleBound
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section IsotropicExtension
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E] [Finite E]
variable (ω : LinearMap.BilinForm K E)
end IsotropicExtension
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section FixedPairs
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E) (L M N : SymplecticLagrangian ω)
variable [FiniteDimensional K E]
variable (ha : ω.IsAlt) (hω : ω.Nondegenerate)
end FixedPairs
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ConfigurationOrbit
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E)
variable [FiniteDimensional K E] [Finite E]
end ConfigurationOrbit
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section PairOrbitAssembly
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E) (L M N : SymplecticLagrangian ω)
variable [Finite E]
end PairOrbitAssembly
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ConfigurationCount
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
  [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
end ConfigurationCount
section FixedPairCount
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
  [Fintype K] [Finite E] [Invertible (2:K)]
variable (ω : LinearMap.BilinForm K E)
end FixedPairCount
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section PairMass
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E)
variable [Fintype K] [Finite E] [Invertible (2:K)]
end PairMass
end SidorenkoCounterexample
end OAI
namespace OAI
namespace SidorenkoCounterexample
open Module
section CommonOrbitGeometry
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E)
variable [Finite E]
end CommonOrbitGeometry
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section AllOrbitMass
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
  [Fintype K] [Finite E] [Invertible (2:K)]
variable (ω : LinearMap.BilinForm K E)
end AllOrbitMass
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ConfigurationUpper
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Finite E]
variable (ω : LinearMap.BilinForm K E)
end ConfigurationUpper
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section DecompositionTransitivity
variable {K E F : Type*} [Field K] [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]
variable [FiniteDimensional K E] [FiniteDimensional K F]
end DecompositionTransitivity
section ConfigTransitivity
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Finite E]
variable (ω : LinearMap.BilinForm K E)
end ConfigTransitivity
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ConfigurationBound
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
end ConfigurationBound
section CommonZeroProfiles
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E)
variable [Finite E]
end CommonZeroProfiles
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section CommonZeroMass
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
end CommonZeroMass
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ProfileQuotient
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E)
end ProfileQuotient
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section AllProfileMass
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
end AllProfileMass
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section GeneralPairCounts
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
end GeneralPairCounts
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ConditionalProfile
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E)
variable [Finite E]
variable [Fintype K]
end ConditionalProfile
end SidorenkoCounterexample
end OAI
namespace OAI
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section PlantedQuotient
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E) (S : Submodule K E)
end PlantedQuotient
section CenterDisintegration
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E)
end CenterDisintegration
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section GenericReducedCount
variable {K E V : Type*} [Field K] [AddCommGroup E] [Module K E]
  [AddCommGroup V] [Module K V]
variable (ω : LinearMap.BilinForm K E)
end GenericReducedCount
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section CommonCenterCounts
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
end CommonCenterCounts
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ReducedCenterInjection
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E)
end ReducedCenterInjection
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section ReducedCardBound
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
end ReducedCardBound
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section FullCenterCoding
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
abbrev CommonParameters (D r c : ℕ) := {u : Fin (c+1) // u.val ≤ r ∧ r-u.val ≤ D-c}
noncomputable instance (D r c : ℕ) : Fintype (CommonParameters D r c) := Fintype.ofFinite _
end FullCenterCoding
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section CommonCountSummation
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
end CommonCountSummation
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section FullProfileCenterBound
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
end FullProfileCenterBound
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section OrbitCenterProfile
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E)
end OrbitCenterProfile
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section PointwisePlanted
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
end PointwisePlanted
end SidorenkoCounterexample
end OAI
namespace OAI
namespace SidorenkoCounterexample
open scoped BigOperators
noncomputable def quadraticPart (c d δ v : ℝ) (p t : Fin 3 → ℝ) : ℝ :=
  (c*(d+δ)-δ*d+2*δ^2)/4 + (∑ i, (2*p i-t i)^2)/6 +
    δ*(∑ i, p i) - c*((∑ i, p i)+(∑ i, t i))/6 +
    ((d-3*δ)/2-(∑ i, p i))*v+v^2/2
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open scoped BigOperators
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open scoped BigOperators
structure TailTuple where
  c : ℕ
  u : ℕ
  v : ℕ
  p : Fin 3 → ℕ
  t : Fin 3 → ℕ
def TailTuple.s (a : TailTuple) (i : Fin 3) : ℕ := a.p i+a.t i
def TailTuple.h (a : TailTuple) (i : Fin 3) : ℕ := a.c+a.s i
noncomputable def TailTuple.delta (a : TailTuple) : ℝ := 2*a.u-a.c
noncomputable def TailTuple.P (a : TailTuple) : ℝ := ∑ i, (a.p i:ℝ)
noncomputable def TailTuple.T (a : TailTuple) : ℝ := ∑ i, (a.t i:ℝ)
noncomputable def TailTuple.Q (D : ℕ) (a : TailTuple) : ℝ :=
  quadraticPart a.c ((D:ℝ)-a.c) a.delta a.v (fun i => a.p i) (fun i => a.t i)
end SidorenkoCounterexample
namespace SidorenkoCounterexample
def pairVertices : Fin 33 → Finset (Fin 13) := ![{0,2}, {0,3}, {2,3}, {0,9}, {2,9}, {0,1}, {1,3}, {2,4}, {3,4}, {1,9}, {4,9}, {1,10}, {3,10}, {3,11}, {4,11}, {1,12}, {9,12}, {4,8}, {8,9}, {1,7}, {7,10}, {10,11}, {8,11}, {7,12}, {8,12}, {5,7}, {5,10}, {5,11}, {6,8}, {6,11}, {6,7}, {6,12}, {5,6}]
def facePair : Fin 22 → Fin 3 → Fin 33 := ![![5, 1, 6], ![5, 3, 9], ![0, 1, 2], ![0, 3, 4], ![6, 11, 12], ![19, 11, 20], ![19, 15, 23], ![9, 15, 16], ![2, 7, 8], ![7, 4, 10], ![8, 13, 14], ![12, 13, 21], ![17, 10, 18], ![17, 14, 22], ![32, 25, 30], ![32, 27, 29], ![25, 26, 20], ![26, 27, 21], ![30, 31, 23], ![28, 29, 22], ![28, 31, 24], ![18, 24, 16]]
def pairFace : Fin 33 → Fin 2 → Fin 22 := ![![2, 3], ![0, 2], ![2, 8], ![1, 3], ![3, 9], ![0, 1], ![0, 4], ![8, 9], ![8, 10], ![1, 7], ![9, 12], ![4, 5], ![4, 11], ![10, 11], ![10, 13], ![6, 7], ![7, 21], ![12, 13], ![12, 21], ![5, 6], ![5, 16], ![11, 17], ![13, 19], ![6, 18], ![20, 21], ![14, 16], ![16, 17], ![15, 17], ![19, 20], ![15, 19], ![14, 18], ![18, 20], ![14, 15]]
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open scoped BigOperators
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open scoped BigOperators
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open scoped BigOperators
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open scoped BigOperators
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open scoped BigOperators
end SidorenkoCounterexample
end OAI
namespace OAI
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section PairDifference
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable (A B : Submodule K V)
end PairDifference
section PairBaseCounts
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [Fintype K] [Finite V]
end PairBaseCounts
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
abbrev PairParameters (r h : ℕ) := {p : Fin (r+1) // p.val ≤ h ∧ h-p.val ≤ p.val}
noncomputable instance pairParametersFintype (r h : ℕ) : Fintype (PairParameters r h) := Fintype.ofFinite _
section PairLiftCounts
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable [Fintype K] [Finite V]
end PairLiftCounts
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open scoped BigOperators
section PairFinal
open Module
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype K] [Finite V]
end PairFinal
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section SymplecticPairPlanted
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E)
variable [Fintype K] [Finite E]
end SymplecticPairPlanted
section PairPointwise
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
end PairPointwise
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ActualProfile
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
end ActualProfile
end SidorenkoCounterexample
end OAI
namespace OAI
namespace SidorenkoCounterexample
open scoped BigOperators
section Sequential
variable {A : Type*} [Finite A]
end Sequential
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open scoped BigOperators
def faceVertex : Fin 22 → Fin 3 → Fin 13 := ![![0, 1, 3], ![0, 1, 9], ![0, 2, 3], ![0, 2, 9], ![1, 3, 10], ![1, 7, 10], ![1, 7, 12], ![1, 9, 12], ![2, 3, 4], ![2, 4, 9], ![3, 4, 11], ![3, 10, 11], ![4, 8, 9], ![4, 8, 11], ![5, 6, 7], ![5, 6, 11], ![5, 7, 10], ![5, 10, 11], ![6, 7, 12], ![6, 8, 11], ![6, 8, 12], ![8, 9, 12]]
def classFace : Fin 6 → Fin 11 → Fin 22 := ![![0, 1, 2, 4, 5, 16, 14, 18, 20, 19, 13], ![3, 9, 8, 10, 11, 17, 15, 12, 21, 7, 6], ![0, 2, 8, 9, 12, 4, 11, 5, 6, 18, 14], ![1, 3, 7, 21, 20, 19, 13, 10, 15, 17, 16], ![0, 1, 3, 9, 7, 6, 5, 16, 14, 15, 19], ![2, 8, 10, 11, 4, 17, 13, 12, 21, 20, 18]]
 theorem faceVertex_correct : ∀ j, faces j={faceVertex j 0,faceVertex j 1,faceVertex j 2} := by decide
 def classContains (c : Fin 6) (j : Fin 22) : Prop := ∃ n, classFace c n=j
 instance (c : Fin 6) (j : Fin 22) : Decidable (classContains c j) := inferInstanceAs (Decidable (∃ n, classFace c n=j))
 def classInternal (c : Fin 6) (e : Fin 33) : Prop := ∀ k, classContains c (pairFace e k)
 instance (c : Fin 6) (e : Fin 33) : Decidable (classInternal c e) := inferInstanceAs (Decidable (∀ k, classContains c (pairFace e k)))
 theorem faceVertex_injective : ∀ j, Function.Injective (faceVertex j) := by decide
 theorem faceVertex_pairs : ∀ j k, pairVertices (facePair j k)=
    (![ {faceVertex j 0,faceVertex j 1}, {faceVertex j 0,faceVertex j 2}, {faceVertex j 1,faceVertex j 2}] : Fin 3 → Finset (Fin 13)) k := by decide
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section RawProfile
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
end RawProfile
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section ExposureProfile
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E)
def PointProfile (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (L : Fin 13 → SymplecticLagrangian ω) : Prop :=
  (∀ j, finrank K ↥((faces j).inf fun i => (L i).val : Submodule K E)=c j) ∧
  (∀ e, finrank K ↥((pairVertices e).inf fun i => (L i).val : Submodule K E)=h e)
def LocalProfile (c u v w : ℕ) (L M N : SymplecticLagrangian ω) : Prop :=
  finrank K ↥((L.val ⊓ M.val) ⊓ N.val)=c ∧ finrank K ↥(L.val ⊓ M.val)=u ∧
  finrank K ↥(L.val ⊓ N.val)=v ∧ finrank K ↥(M.val ⊓ N.val)=w
 theorem PointProfile.local {c : Fin 22 → ℕ} {h : Fin 33 → ℕ} {L : Fin 13 → SymplecticLagrangian ω}
    (hL : PointProfile ω c h L) (j : Fin 22) (i k l : Fin 13) (e f g : Fin 33)
    (hj : faces j={i,k,l}) (he : pairVertices e={i,k}) (hf : pairVertices f={i,l})
    (hg : pairVertices g={k,l}) : LocalProfile ω (c j) (h e) (h f) (h g) (L i) (L k) (L l) := by
  classical
  unfold PointProfile at hL
  refine ⟨?_,?_,?_,?_⟩
  · have hh := hL.1 j
    rw [hj,Finset.inf_insert,Finset.inf_insert,Finset.inf_singleton,←inf_assoc] at hh
    exact hh
  · have hh := hL.2 e
    rw [he,Finset.inf_insert,Finset.inf_singleton] at hh
    exact hh
  · have hh := hL.2 f
    rw [hf,Finset.inf_insert,Finset.inf_singleton] at hh
    exact hh
  · have hh := hL.2 g
    rw [hg,Finset.inf_insert,Finset.inf_singleton] at hh
    exact hh
variable [Fintype K] [Finite E]
end ExposureProfile
section GlobalExposure
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
end GlobalExposure
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open scoped BigOperators
section ZeroSequential
variable {A : Type*} [Finite A]
end ZeroSequential
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section OrthogonalTuple
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E)
abbrev OrthogonalTuple (R : ℕ → ℕ → Prop) (n : ℕ) :=
  {x : Fin n → E // LinearIndependent K x ∧ ∀ i j : Fin n, i.val<j.val → R i.val j.val → ω (x i) (x j)=0}
variable [Fintype K] [Finite E]
end OrthogonalTuple
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section TupleRpow
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
end TupleRpow
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section AbstractTuple
variable {K E A : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E] [Fintype A]
variable (ω : LinearMap.BilinForm K E)
end AbstractTuple
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section ResidualCount
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
end ResidualCount
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section FamilySpan
variable {K E I : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype I]
variable [Finite E]
variable [Fintype K]
end FamilySpan
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section DirectFamilies
variable {K E I : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype I]
variable [Finite E]
variable (ω : LinearMap.BilinForm K E)
variable [Fintype K]
end DirectFamilies
end SidorenkoCounterexample
end OAI
namespace OAI
namespace SidorenkoCounterexample
open Module
section Span
variable {K V P : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype P] [DecidableEq P]
end Span
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section FiniteSpans
variable {K E I : Type*} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]
end FiniteSpans
def pairRelated (e f : Fin 33) : Prop := ¬Disjoint (pairVertices e) (pairVertices f)
instance (e f : Fin 33) : Decidable (pairRelated e f) := inferInstanceAs (Decidable (¬Disjoint _ _))
section GraphSpans
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable [FiniteDimensional K E]
end GraphSpans
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open scoped BigOperators
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open scoped BigOperators
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section Containment
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E)
variable [Fintype K] [Finite E]
end Containment
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section Nondirect
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E)
variable [Fintype K] [Finite E]
end Nondirect
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
abbrev FullTailChoice (D r c : ℕ) (s : Fin 3 → ℕ) :=
  Σ u : CommonParameters D r c, BaseParameters (D-c) (r-u.val.val) (s 0) (s 1) (s 2)
section Actual
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
end Actual
end SidorenkoCounterexample
end OAI
namespace OAI
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section PairBound
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
end PairBound
def FaceTailChoice (D r c : ℕ) (s : Fin 3 → ℕ) : Bool → Type
| true => FullTailChoice D r c s
| false => Unit
noncomputable instance faceTailChoiceFintype (D r c : ℕ) (s : Fin 3 → ℕ) (b : Bool) :
    Fintype (FaceTailChoice D r c s b) := by cases b <;> unfold FaceTailChoice <;> infer_instance
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section Actual
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
omit [Fintype K] [Finite E] in
 theorem PointProfile.faceLocal {c : Fin 22 → ℕ} {h : Fin 33 → ℕ} {L : Fin 13 → SymplecticLagrangian ω}
    (hL : PointProfile ω c h L) (j : Fin 22) :
    LocalProfile ω (c j) (h (facePair j 0)) (h (facePair j 1)) (h (facePair j 2))
      (L (faceVertex j 0)) (L (faceVertex j 1)) (L (faceVertex j 2)) := by
  apply PointProfile.local ω hL j (faceVertex j 0) (faceVertex j 1) (faceVertex j 2)
    (facePair j 0) (facePair j 1) (facePair j 2) (faceVertex_correct j)
  · exact faceVertex_pairs j 0
  · exact faceVertex_pairs j 1
  · exact faceVertex_pairs j 2
end Actual
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section Actual
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
end Actual
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section Actual
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
end Actual
section ActualProduct
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
end ActualProduct
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section ActiveFace
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
end ActiveFace
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section ActiveFaceBound
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
 theorem fin3_subsets (T : Finset (Fin 3)) : T=∅ ∨ T={0} ∨ T={1} ∨ T={2} ∨
    T={0,1} ∨ T={0,2} ∨ T={1,2} ∨ T=Finset.univ := by
  revert T; decide
end ActiveFaceBound
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
abbrev DimProfile (D : ℕ) := (Fin 22 → Fin (D+1)) × (Fin 33 → Fin (D+1))
def DimProfile.c {D : ℕ} (p : DimProfile D) (j : Fin 22) : ℕ := p.1 j
def DimProfile.h {D : ℕ} (p : DimProfile D) (e : Fin 33) : ℕ := p.2 e
section Integrated
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
end Integrated
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section IntegratedBound
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
end IntegratedBound
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section ActualProfile
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
  [Finite E]
variable (ω : LinearMap.BilinForm K E) (hω : ω.Nondegenerate)
variable (D : ℕ) (hD : 2 * D = finrank K E)
end ActualProfile
end SidorenkoCounterexample
end OAI
namespace OAI
section
namespace SidorenkoCounterexample
open Module LinearMap
section Forms
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
def radicalQuotientForm (B : LinearMap.BilinForm K V) (hB : B.IsSymm) :
    LinearMap.BilinForm K (V ⧸ B.ker) :=
  LinearMap.IsRefl.liftQ₂ B B.ker hB.isRefl le_rfl
@[simp] theorem radicalQuotientForm_mk (B : LinearMap.BilinForm K V) (hB : B.IsSymm)
    (x y : V) : radicalQuotientForm B hB
      (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) = B x y := rfl
theorem radicalQuotientForm_nondegenerate [FiniteDimensional K V]
    (B : LinearMap.BilinForm K V) (hB : B.IsSymm) :
    (radicalQuotientForm B hB).Nondegenerate := by
  apply LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot.mpr
  apply bot_unique
  intro x hx
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    apply (Submodule.Quotient.mk_eq_zero B.ker).mpr
    apply LinearMap.mem_ker.mpr
    ext y
    have h := congrArg (fun f => f (Submodule.Quotient.mk y)) hx
    exact h
theorem form_isSymm_neg (B : LinearMap.BilinForm K V) (hB : B.IsSymm) :
    (-B).IsSymm := by
  constructor
  intro x y
  change -(B x y) = -(B y x)
  rw [hB.eq x y]
def radicalNegEquiv (B : LinearMap.BilinForm K V) :
    (V ⧸ (-B).ker) ≃ₗ[K] (V ⧸ B.ker) :=
  Submodule.quotEquivOfEq _ _ (LinearMap.ker_neg B)
theorem radicalQuotientForm_neg (B : LinearMap.BilinForm K V) (hB : B.IsSymm)
    (x y : V ⧸ (-B).ker) :
    radicalQuotientForm (-B) (form_isSymm_neg B hB) x y =
      -(radicalQuotientForm B hB (radicalNegEquiv B x) (radicalNegEquiv B y)) := by
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    induction y using Submodule.Quotient.induction_on with
    | H y => rfl
variable [FiniteDimensional K V] [Fintype K] [DecidableEq K]
noncomputable def discriminantSign (B : LinearMap.BilinForm K V) (hB : B.IsSymm) : ℤ :=
  quadraticChar K ((radicalQuotientForm B hB).toMatrix
    (Module.finBasis K (V ⧸ B.ker))).det
theorem discriminantSign_ne_zero (B : LinearMap.BilinForm K V) (hB : B.IsSymm) :
    discriminantSign B hB ≠ 0 := by
  apply mt quadraticChar_eq_zero_iff.mp
  exact (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero _).mp
    (radicalQuotientForm_nondegenerate B hB)
theorem discriminantSign_cases (B : LinearMap.BilinForm K V) (hB : B.IsSymm) :
    discriminantSign B hB = 1 ∨ discriminantSign B hB = -1 := by
  apply quadraticChar_dichotomy
  exact (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero _).mp
    (radicalQuotientForm_nondegenerate B hB)
omit [FiniteDimensional K V] in
theorem determinant_character_basis_independent {ι : Type*}
    [Fintype ι] [DecidableEq ι] (b c : Basis ι K V) (B : LinearMap.BilinForm K V) :
    quadraticChar K (B.toMatrix b).det = quadraticChar K (B.toMatrix c).det := by
  have hu : (b.toMatrix c).det ≠ 0 := (b.isUnit_det c).ne_zero
  rw [← B.toMatrix_mul_basis_toMatrix b c, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transpose, map_mul, map_mul]
  have hsq := quadraticChar_sq_one (F := K) hu
  linear_combination -(quadraticChar K (B.toMatrix b).det) * hsq
omit [FiniteDimensional K V] in
theorem determinant_character_basis_independent_indices {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (b : Basis ι K V) (c : Basis κ K V) (B : LinearMap.BilinForm K V) :
    quadraticChar K (B.toMatrix b).det = quadraticChar K (B.toMatrix c).det := by
  classical
  let e := b.indexEquiv c
  have h : B.toMatrix (b.reindex e) = Matrix.reindex e e (B.toMatrix b) := by
    ext i j
    simp [LinearMap.BilinForm.toMatrix_apply, Matrix.reindex_apply]
  calc
    quadraticChar K (B.toMatrix b).det =
        quadraticChar K (B.toMatrix (b.reindex e)).det := by
      rw [h, Matrix.det_reindex_self]
    _ = quadraticChar K (B.toMatrix c).det :=
      determinant_character_basis_independent _ _ _
theorem discriminantSign_eq (B : LinearMap.BilinForm K V) (hB : B.IsSymm)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι K (V ⧸ B.ker)) :
    discriminantSign B hB = quadraticChar K ((radicalQuotientForm B hB).toMatrix b).det :=
  determinant_character_basis_independent_indices _ _ _
theorem discriminantSign_neg (B : LinearMap.BilinForm K V) (hB : B.IsSymm) :
    discriminantSign (-B) (form_isSymm_neg B hB) =
      quadraticChar K ((-1 : K) ^ finrank K (V ⧸ B.ker)) * discriminantSign B hB := by
  classical
  let b := Module.finBasis K (V ⧸ B.ker)
  rw [discriminantSign_eq (-B) (form_isSymm_neg B hB)
    (b.map (radicalNegEquiv B).symm)]
  have hm : (radicalQuotientForm (-B) (form_isSymm_neg B hB)).toMatrix
      (b.map (radicalNegEquiv B).symm) = -(radicalQuotientForm B hB).toMatrix b := by
    ext i j
    simp only [LinearMap.BilinForm.toMatrix_apply, Basis.map_apply, Matrix.neg_apply]
    rw [radicalQuotientForm_neg B hB]
    simp only [LinearEquiv.apply_symm_apply]
  rw [hm, Matrix.det_neg, map_mul, Fintype.card_fin]
  rfl
end Forms
section Pullback
variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]
 theorem pullback_isSymm (B : LinearMap.BilinForm K W) (hB : B.IsSymm)
    (f : V →ₗ[K] W) : LinearMap.BilinForm.IsSymm (B.compl₁₂ f f) := by
  constructor
  intro x y
  exact hB.eq (f x) (f y)
theorem pullback_ker (B : LinearMap.BilinForm K W) (hB : B.Nondegenerate)
    (f : V →ₗ[K] W) (hf : Function.Surjective f) :
    (B.compl₁₂ f f).ker = f.ker := by
  ext x
  simp only [LinearMap.mem_ker]
  constructor
  · intro hx
    apply hB.1
    intro y
    obtain ⟨z, rfl⟩ := hf y
    exact congrArg (fun g => g z) hx
  · intro hx
    ext y
    simp [hx]
noncomputable def pullbackQuotientEquiv (B : LinearMap.BilinForm K W)
    (hB : B.Nondegenerate) (f : V →ₗ[K] W) (hf : Function.Surjective f) :
    (V ⧸ (B.compl₁₂ f f).ker) ≃ₗ[K] W :=
  (Submodule.quotEquivOfEq _ _ (pullback_ker B hB f hf)).trans
    (f.quotKerEquivOfSurjective hf)
@[simp] theorem pullbackQuotientEquiv_mk (B : LinearMap.BilinForm K W)
    (hB : B.Nondegenerate) (f : V →ₗ[K] W) (hf : Function.Surjective f) (x : V) :
    pullbackQuotientEquiv B hB f hf (Submodule.Quotient.mk x) = f x := rfl
theorem pullbackQuotientForm (B : LinearMap.BilinForm K W)
    (hBs : B.IsSymm) (hB : B.Nondegenerate)
    (f : V →ₗ[K] W) (hf : Function.Surjective f)
    (x y : V ⧸ (B.compl₁₂ f f).ker) :
    radicalQuotientForm (B.compl₁₂ f f) (pullback_isSymm B hBs f) x y =
      B (pullbackQuotientEquiv B hB f hf x) (pullbackQuotientEquiv B hB f hf y) := by
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    induction y using Submodule.Quotient.induction_on with
    | H y => rfl
variable [FiniteDimensional K V] [Fintype K] [DecidableEq K]
theorem discriminantSign_pullback (B : LinearMap.BilinForm K W)
    (hBs : B.IsSymm) (hB : B.Nondegenerate)
    (f : V →ₗ[K] W) (hf : Function.Surjective f)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι K W) :
    discriminantSign (B.compl₁₂ f f) (pullback_isSymm B hBs f) =
      quadraticChar K (B.toMatrix b).det := by
  classical
  let e := pullbackQuotientEquiv B hB f hf
  rw [discriminantSign_eq _ _ (b.map e.symm)]
  congr 2
  ext i j
  simp only [LinearMap.BilinForm.toMatrix_apply, Basis.map_apply]
  rw [pullbackQuotientForm B hBs hB f hf]
  simp only [e, LinearEquiv.apply_symm_apply]
end Pullback
section MatrixForms
variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]
theorem matrix_bilin_eval (M : Matrix n n K) (x y : n → K) :
    M.toBilin' x y = (M.transpose.mulVec x) ⬝ᵥ y := by
  rw [Matrix.toBilin'_apply]
  simp only [dotProduct, Matrix.mulVec, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring
theorem matrix_bilin_ker (M : Matrix n n K) :
    M.toBilin'.ker = M.transpose.toLin'.ker := by
  ext x
  simp only [LinearMap.mem_ker, LinearMap.ext_iff, LinearMap.zero_apply,
    matrix_bilin_eval, Matrix.toLin'_apply]
  exact dotProduct_eq_zero_iff
theorem matrix_radical_quotient_rank (M : Matrix n n K) :
    finrank K ((n → K) ⧸ M.toBilin'.ker) = M.rank := by
  have h₁ := M.toBilin'.ker.finrank_quotient_add_finrank
  have h₂ := M.transpose.toLin'.finrank_range_add_finrank_ker
  rw [matrix_bilin_ker] at h₁
  have hr : finrank K M.transpose.toLin'.range = M.transpose.rank := rfl
  rw [hr, Matrix.rank_transpose] at h₂
  rw [matrix_bilin_ker]
  omega
theorem matrix_rank_neg (M : Matrix n n K) : (-M).rank = M.rank := by
  change finrank K (Matrix.toLin' (-M)).range = finrank K (Matrix.toLin' M).range
  rw [map_neg, LinearMap.range_neg]
end MatrixForms
end SidorenkoCounterexample
namespace SidorenkoCounterexample
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section FiniteLayer
variable (K : Type*) [Field K] (D : ℕ)
variable [Fintype K] [DecidableEq K]
noncomputable instance : Fintype (SymMatrix K D) := Fintype.ofFinite _
noncomputable def matrixSign (Z : SymMatrix K D) : ℤ :=
  discriminantSign Z.val.toBilin' (Matrix.isSymm_toBilin'_iff_isSymm.mpr Z.property)
theorem exists_matrix_of_nonsingular {r : ℕ} (hrD : r ≤ D)
    (R : Matrix (Fin r) (Fin r) K) (hRs : R.IsSymm) (hR : R.det ≠ 0) :
    ∃ Z : SymMatrix K D, Z.val.rank = r ∧
      matrixSign K D Z = quadraticChar K R.det := by
  classical
  let f : (Fin D → K) →ₗ[K] (Fin r → K) :=
    LinearMap.funLeft K K (Fin.castLE hrD)
  have hf : Function.Surjective f :=
    LinearMap.funLeft_surjective_of_injective K K _ (Fin.castLE_injective hrD)
  have hbs : R.toBilin'.IsSymm := Matrix.isSymm_toBilin'_iff_isSymm.mpr hRs
  have hb : R.toBilin'.Nondegenerate :=
    LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mpr hR
  let B : LinearMap.BilinForm K (Fin D → K) := R.toBilin'.compl₁₂ f f
  have hB : B.IsSymm := pullback_isSymm _ hbs f
  let Z : SymMatrix K D := ⟨B.toMatrix',
    LinearMap.BilinForm.isSymm_toMatrix'_iff_isSymm.mpr hB⟩
  have hz : Z.val.toBilin' = B := Matrix.toBilin'_toMatrix' B
  refine ⟨Z, ?_, ?_⟩
  · rw [← matrix_radical_quotient_rank, hz]
    calc
      finrank K ((Fin D → K) ⧸ B.ker) = finrank K (Fin r → K) :=
        (pullbackQuotientEquiv R.toBilin' hb f hf).finrank_eq
      _ = r := by simp
  · unfold matrixSign
    simp only [hz]
    have he := discriminantSign_pullback R.toBilin' hbs hb f hf
      (Pi.basisFun K (Fin r))
    convert he using 1
    exact congrArg (fun M : Matrix (Fin r) (Fin r) K => quadraticChar K M.det)
      (LinearMap.BilinForm.toMatrix'_toBilin' R).symm
theorem exists_matrix_rank_sign {r : ℕ} (hr : 0 < r) (hrD : r ≤ D)
    (hK : ringChar K ≠ 2) {ξ : ℤ} (hξ : ξ = 1 ∨ ξ = -1) :
    ∃ Z : SymMatrix K D, Z.val.rank = r ∧ matrixSign K D Z = ξ := by
  classical
  have ha : ∃ a : K, a ≠ 0 ∧ quadraticChar K a = ξ := by
    rcases hξ with rfl | rfl
    · exact ⟨1, one_ne_zero, map_one _⟩
    · obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one (F := K) hK
      refine ⟨a, ?_, ha⟩
      intro haz
      simp [haz] at ha
  obtain ⟨a, ha, hax⟩ := ha
  let i₀ : Fin r := ⟨0, hr⟩
  let R : Matrix (Fin r) (Fin r) K :=
    Matrix.diagonal fun i => if i = i₀ then a else 1
  have hdet : R.det = a := by
    simp [R, Matrix.det_diagonal]
  obtain ⟨Z, hz, hs⟩ := exists_matrix_of_nonsingular K D hrD R
    (Matrix.isSymm_diagonal _) (hdet ▸ ha)
  exact ⟨Z, hz, hs.trans (hdet ▸ hax)⟩
noncomputable def signedLayer (r : ℕ) (ξ : ℤ) : Finset (SymMatrix K D) := by
  classical
  exact Finset.univ.filter fun Z => Z.val.rank = r ∧ matrixSign K D Z = ξ
noncomputable def layerMass (r : ℕ) (ξ : ℤ) : ℝ :=
  (signedLayer K D r ξ).card / (Fintype.card (SymMatrix K D) : ℝ)
noncomputable def rankKernel (r : ℕ) (ξ : ℤ) (Z : SymMatrix K D) : ℝ := by
  classical
  exact if Z ∈ signedLayer K D r ξ then (layerMass K D r ξ)⁻¹ else 0
theorem matrixSign_neg (Z : SymMatrix K D) :
    matrixSign K D (-Z) = quadraticChar K ((-1 : K) ^ Z.val.rank) *
      matrixSign K D Z := by
  have hs := discriminantSign_neg Z.val.toBilin'
    (Matrix.isSymm_toBilin'_iff_isSymm.mpr Z.property)
  simpa only [matrixSign, Submodule.coe_neg, map_neg, matrix_radical_quotient_rank] using hs
@[simp] theorem mem_signedLayer (r : ℕ) (ξ : ℤ) (Z : SymMatrix K D) :
    Z ∈ signedLayer K D r ξ ↔ Z.val.rank = r ∧ matrixSign K D Z = ξ := by
  classical
  simp [signedLayer]
theorem signedLayer_nonempty {r : ℕ} (hr : 0 < r) (hrD : r ≤ D)
    (hK : ringChar K ≠ 2) {ξ : ℤ} (hξ : ξ = 1 ∨ ξ = -1) :
    (signedLayer K D r ξ).Nonempty := by
  obtain ⟨Z, hz, hs⟩ := exists_matrix_rank_sign K D hr hrD hK hξ
  exact ⟨Z, (mem_signedLayer K D r ξ Z).mpr ⟨hz, hs⟩⟩
theorem rankKernel_nonneg (r : ℕ) (ξ : ℤ) (Z : SymMatrix K D) :
    0 ≤ rankKernel K D r ξ Z := by
  classical
  unfold rankKernel layerMass
  split_ifs <;> positivity
theorem neg_mem_signedLayer (r : ℕ) (ξ : ℤ) (Z : SymMatrix K D) :
    -Z ∈ signedLayer K D r ξ ↔
      Z ∈ signedLayer K D r (quadraticChar K ((-1 : K) ^ r) * ξ) := by
  rw [mem_signedLayer, mem_signedLayer]
  have hc := quadraticChar_sq_one (F := K) (pow_ne_zero r (neg_ne_zero.mpr one_ne_zero))
  simp only [Submodule.coe_neg, matrix_rank_neg, matrixSign_neg]
  constructor
  · rintro ⟨hz, hs⟩
    rw [hz] at hs
    refine ⟨hz, ?_⟩
    linear_combination quadraticChar K ((-1 : K) ^ r) * hs -
      matrixSign K D Z * hc
  · rintro ⟨hz, hs⟩
    refine ⟨hz, ?_⟩
    rw [hz, hs]
    linear_combination ξ * hc
theorem signedLayer_card_neg (r : ℕ) (ξ : ℤ) :
    (signedLayer K D r ξ).card =
      (signedLayer K D r (quadraticChar K ((-1 : K) ^ r) * ξ)).card := by
  classical
  apply Finset.card_bij (fun Z _ => -Z)
  · intro Z hZ
    exact (neg_mem_signedLayer K D r ξ (-Z)).mp (by simpa using hZ)
  · intro Z _ W _ h
    exact neg_injective h
  · intro Z hZ
    exact ⟨-Z, (neg_mem_signedLayer K D r ξ Z).mpr hZ, neg_neg Z⟩
theorem rankKernel_neg (r : ℕ) (ξ : ℤ) (Z : SymMatrix K D) :
    rankKernel K D r ξ (-Z) =
      rankKernel K D r (quadraticChar K ((-1 : K) ^ r) * ξ) Z := by
  classical
  unfold rankKernel
  simp only [neg_mem_signedLayer]
  congr 1
  unfold layerMass
  rw [signedLayer_card_neg]
end FiniteLayer
noncomputable def uniformMean {A : Type*} [Fintype A] (f : A → ℝ) : ℝ :=
  (∑ a, f a) / Fintype.card A
theorem uniformMean_rankKernel {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (D r : ℕ) (hr : 0 < r) (hrD : r ≤ D) (hK : ringChar K ≠ 2)
    {ξ : ℤ} (hξ : ξ = 1 ∨ ξ = -1) :
    uniformMean (rankKernel K D r ξ) = 1 := by
  classical
  have hs := (signedLayer_nonempty K D hr hrD hK hξ).card_pos
  have hc := Fintype.card_pos (α := SymMatrix K D)
  unfold uniformMean rankKernel
  rw [Finset.sum_ite_mem]
  simp only [Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  unfold layerMass
  have hs' : ((signedLayer K D r ξ).card : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  have hc' : (Fintype.card (SymMatrix K D) : ℝ) ≠ 0 := by exact_mod_cast hc.ne'
  field_simp
abbrev OddPrime := {q : ℕ // q.Prime ∧ q ≠ 2}
instance (q : OddPrime) : Fact q.val.Prime := ⟨q.property.1⟩
def primeInfinity : Filter OddPrime := Filter.comap Subtype.val Filter.atTop
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module LinearMap
private theorem range_sup_complement {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] (f : V →ₗ[K] V) :
    LinearMap.range f ⊔ LinearMap.range (LinearMap.id - f) = ⊤ := by
  apply top_unique
  intro x _
  exact Submodule.mem_sup.mpr ⟨f x, ⟨x, rfl⟩, x-f x, ⟨x, rfl⟩, by abel⟩
theorem complementary_rank_iff {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (f : V →ₗ[K] V) :
    finrank K (LinearMap.range f) + finrank K (LinearMap.range (LinearMap.id-f)) =
      finrank K V ↔ IsIdempotentElem f := by
  constructor
  · intro h
    have hsum := Submodule.finrank_sup_add_finrank_inf_eq
      (LinearMap.range f) (LinearMap.range (LinearMap.id-f))
    rw [range_sup_complement, finrank_top] at hsum
    have hz : finrank K (LinearMap.range f ⊓ LinearMap.range (LinearMap.id-f) :
        Submodule K V) = 0 := by omega
    have hinf := Submodule.finrank_eq_zero.mp hz
    change f*f = f
    ext x
    have hx₁ : f x-f (f x) ∈ LinearMap.range f := ⟨x-f x, map_sub f x (f x)⟩
    have hx₂ : f x-f (f x) ∈ LinearMap.range (LinearMap.id-f) := ⟨f x, rfl⟩
    have hx : f x-f (f x) ∈ (⊥ : Submodule K V) := by
      rw [← hinf]
      exact ⟨hx₁, hx₂⟩
    have hzero : f x-f (f x) = 0 := hx
    exact (sub_eq_zero.mp hzero).symm
  · intro h
    rw [← h.ker_eq_range]
    exact f.finrank_range_add_finrank_ker
theorem matrix_complementary_rank_iff {K n : Type*} [Field K] [Fintype n]
    [DecidableEq n] (P : Matrix n n K) :
    P.rank + (1-P).rank = Fintype.card n ↔ P*P=P := by
  have h := complementary_rank_iff (Matrix.toLin' P)
  have hdim : finrank K (n → K) = Fintype.card n := Module.finrank_fintype_fun_eq_card K
  rw [← Matrix.toLin'_one, ← map_sub Matrix.toLin'] at h
  change P.rank+(1-P).rank = finrank K (n → K) ↔ IsIdempotentElem (Matrix.toLin' P) at h
  rw [hdim] at h
  rw [h]
  change (Matrix.toLin' P).comp (Matrix.toLin' P) = Matrix.toLin' P ↔ _
  rw [← Matrix.toLin'_mul, Matrix.toLin'.injective.eq_iff]
theorem half_rank_projection {K n : Type*} [Field K] [Fintype n] [DecidableEq n]
    (r : ℕ) (hdim : Fintype.card n = 2*r) (A B : Matrix n n K)
    (hB : B.det ≠ 0) (hA : A.rank = r) :
    (B-A).rank = r ↔ A*B⁻¹*A=A := by
  have hu : IsUnit B.det := isUnit_iff_ne_zero.mpr hB
  have hBi : B⁻¹.det ≠ 0 := by simpa [Matrix.det_nonsing_inv] using inv_ne_zero hB
  have hPr : (A*B⁻¹).rank = r := (Matrix.rank_mul_eq_left_of_det_ne_zero _ _ hBi).trans hA
  have hQr : (1-A*B⁻¹).rank = (B-A).rank := by
    rw [show 1-A*B⁻¹ = (B-A)*B⁻¹ by rw [sub_mul, Matrix.mul_nonsing_inv B hu]]
    exact Matrix.rank_mul_eq_left_of_det_ne_zero _ _ hBi
  have hmain := matrix_complementary_rank_iff (A*B⁻¹)
  rw [hPr, hQr, hdim] at hmain
  have hsum : r+(B-A).rank=2*r ↔ (B-A).rank=r := by omega
  rw [hsum] at hmain
  rw [hmain]
  constructor
  · intro h
    have hm := congrArg (fun M => M*B) h
    simpa only [Matrix.mul_assoc, Matrix.nonsing_inv_mul B hu, Matrix.mul_one] using hm
  · intro h
    calc
      (A*B⁻¹)*(A*B⁻¹) = (A*B⁻¹*A)*B⁻¹ := by simp only [Matrix.mul_assoc]
      _ = A*B⁻¹ := by rw [h]
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section Border
variable {K : Type*} [Field K]
def borderIndex (n : ℕ) : Fin (n+1) ≃ Fin n ⊕ PUnit.{1} :=
  (finSuccEquiv n).trans (Equiv.optionEquivSumPUnit (Fin n))
def borderRaw {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (z : Fin n → K) (a : K) :
    Matrix (Fin n ⊕ PUnit.{1}) (Fin n ⊕ PUnit.{1}) K :=
  Matrix.fromBlocks M (Matrix.of fun i _ => z i) (Matrix.of fun _ j => z j) (Matrix.of fun _ _ => a)
def symmetricBorder {n : ℕ} (M : SymMatrix K n) (z : Fin n → K) (a : K) : SymMatrix K (n+1) :=
  ⟨(borderRaw M.val z a).submatrix (borderIndex n) (borderIndex n), by
    ext i j
    change borderRaw M.val z a (borderIndex n j) (borderIndex n i) =
      borderRaw M.val z a (borderIndex n i) (borderIndex n j)
    cases borderIndex n i with
    | inl i => cases borderIndex n j with
      | inl j => exact M.property.apply i j
      | inr j => rfl
    | inr i => cases borderIndex n j <;> rfl⟩
def borderUnpack {n : ℕ} (M : SymMatrix K (n+1)) :
    SymMatrix K n × (Fin n → K) × K :=
  (⟨M.val.submatrix (fun i => (borderIndex n).symm (.inl i))
      (fun i => (borderIndex n).symm (.inl i)), by
      ext i j; exact M.property.apply _ _⟩,
   fun i => M.val ((borderIndex n).symm (.inl i)) ((borderIndex n).symm (.inr PUnit.unit)),
   M.val ((borderIndex n).symm (.inr PUnit.unit)) ((borderIndex n).symm (.inr PUnit.unit)))
def symmetricBorderEquiv (n : ℕ) :
    SymMatrix K (n+1) ≃ SymMatrix K n × (Fin n → K) × K where
  toFun := borderUnpack
  invFun x := symmetricBorder x.1 x.2.1 x.2.2
  left_inv M := by
    apply Subtype.ext
    ext i j
    obtain ⟨i,rfl⟩ := (borderIndex n).symm.surjective i
    obtain ⟨j,rfl⟩ := (borderIndex n).symm.surjective j
    cases i with
    | inl i => cases j with
      | inl j => simp [symmetricBorder,borderUnpack,borderRaw,Matrix.fromBlocks]
      | inr j => cases j; simp [symmetricBorder,borderUnpack,borderRaw,Matrix.fromBlocks]
    | inr i =>
      cases i
      cases j with
      | inl j =>
        simpa [symmetricBorder,borderUnpack,borderRaw,Matrix.fromBlocks] using
          (M.property.apply ((borderIndex n).symm (.inr PUnit.unit))
            ((borderIndex n).symm (.inl j)))
      | inr j => cases j; simp [symmetricBorder,borderUnpack,borderRaw,Matrix.fromBlocks]
  right_inv x := by
    rcases x with ⟨M,z,a⟩
    apply Prod.ext
    · apply Subtype.ext; ext i j; simp [symmetricBorder,borderUnpack,borderRaw,Matrix.fromBlocks]
    · apply Prod.ext
      · funext i; simp [symmetricBorder,borderUnpack,borderRaw,Matrix.fromBlocks]
      · simp [symmetricBorder,borderUnpack,borderRaw,Matrix.fromBlocks]
 theorem symmetricBorder_det {n : ℕ} (M : SymMatrix K n) (z : Fin n → K) (a : K)
    (hM : M.val.det ≠ 0) :
    (symmetricBorder M z a).val.det = M.val.det * (a - z ⬝ᵥ (M.val⁻¹.mulVec z)) := by
  classical
  let := Matrix.invertibleOfIsUnitDet M.val (isUnit_iff_ne_zero.mpr hM)
  rw [symmetricBorder,Matrix.det_submatrix_equiv_self]
  dsimp only [borderRaw]
  rw [Matrix.det_fromBlocks₁₁]
  congr 1
  rw [Matrix.det_unique]
  simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.of_apply,
    Matrix.invOf_eq_nonsing_inv, dotProduct, Matrix.mulVec, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [mul_assoc]
end Border
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open scoped BigOperators
section Mean
variable {A B : Type*} [Fintype A] [Fintype B]
theorem uniformMean_congr {f g : A → ℝ} (h : ∀ a, f a = g a) :
    uniformMean f = uniformMean g := by
  unfold uniformMean
  congr 1
  exact Finset.sum_congr rfl fun a _ => h a
theorem uniformMean_equiv (e : A ≃ B) (f : B → ℝ) :
    uniformMean (f ∘ e) = uniformMean f := by
  unfold uniformMean
  dsimp only [Function.comp_def]
  rw [Fintype.card_congr e, Equiv.sum_comp e f]
theorem uniformMean_prod (f : A × B → ℝ) :
    uniformMean f = uniformMean fun a => uniformMean fun b => f (a,b) := by
  unfold uniformMean
  rw [Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul]
  simp_rw [← Finset.sum_div]
  ring
theorem uniformMean_const [Nonempty A] (c : ℝ) : uniformMean (fun _ : A => c) = c := by
  simp [uniformMean, (Nat.cast_ne_zero.mpr (Fintype.card_ne_zero (α := A)) :
    (Fintype.card A : ℝ) ≠ 0)]
theorem uniformMean_add (f g : A → ℝ) :
    uniformMean (fun a => f a + g a) = uniformMean f + uniformMean g := by
  simp [uniformMean, Finset.sum_add_distrib, add_div]
theorem uniformMean_sub (f g : A → ℝ) :
    uniformMean (fun a => f a - g a) = uniformMean f - uniformMean g := by
  simp [uniformMean, Finset.sum_sub_distrib, sub_div]
theorem uniformMean_mul (c : ℝ) (f : A → ℝ) :
    uniformMean (fun a => c * f a) = c * uniformMean f := by
  simp [uniformMean, ← Finset.mul_sum, mul_div_assoc]
theorem uniformMean_mono {f g : A → ℝ} (h : ∀ a, f a ≤ g a) :
    uniformMean f ≤ uniformMean g := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact Finset.sum_le_sum fun a _ => h a
theorem uniformMean_nonneg {f : A → ℝ} (h : ∀ a, 0 ≤ f a) : 0 ≤ uniformMean f :=
  div_nonneg (Finset.sum_nonneg fun a _ => h a) (Nat.cast_nonneg _)
theorem abs_uniformMean_le (f : A → ℝ) :
    |uniformMean f| ≤ uniformMean fun a => |f a| := by
  unfold uniformMean
  rw [abs_div, abs_of_nonneg (show (0 : ℝ) ≤ Fintype.card A from Nat.cast_nonneg _)]
  exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs ..) (Nat.cast_nonneg _)
theorem uniformMean_bound [Nonempty A] {f : A → ℝ} {c : ℝ} (h : ∀ a, f a ≤ c) :
    uniformMean f ≤ c := by
  simpa only [uniformMean_const] using uniformMean_mono h
theorem uniformMean_indicator (p : A → Prop) [DecidablePred p] :
    uniformMean (fun a => if p a then 1 else 0) =
      (Fintype.card {a // p a} : ℝ) / Fintype.card A := by
  simp [uniformMean, Fintype.card_subtype, Finset.sum_boole]
end Mean
end SidorenkoCounterexample
end
end OAI
namespace OAI
section
namespace SidorenkoCounterexample
open scoped BigOperators
section Scalar
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
noncomputable def characterSignIndicator (ξ : ℤ) (a : K) : ℝ :=
  if quadraticChar K a = ξ then 1 else 0
 theorem characterSignIndicator_nonneg (ξ : ℤ) (a : K) : 0 ≤ characterSignIndicator ξ a := by
  unfold characterSignIndicator; split <;> norm_num
 theorem characterSignIndicator_le_one (ξ : ℤ) (a : K) : characterSignIndicator ξ a ≤ 1 := by
  unfold characterSignIndicator; split <;> norm_num
 theorem characterSignIndicator_formula {ξ : ℤ} (hξ : ξ = 1 ∨ ξ = -1) (a : K) :
    2 * characterSignIndicator ξ a =
      (if a = 0 then 0 else 1) + (ξ : ℝ) * (quadraticChar K a : ℝ) := by
  by_cases ha : a = 0
  · rcases hξ with rfl | rfl <;> simp [characterSignIndicator, ha]
  · rcases quadraticChar_dichotomy ha with hc | hc <;>
      rcases hξ with rfl | rfl <;> norm_num [characterSignIndicator, hc, ha]
omit [Field K] in
 theorem uniformMean_singleton (b : K) :
    uniformMean (fun a : K => if a = b then 1 else 0) = 1 / (Fintype.card K : ℝ) := by
  simp [uniformMean]
 theorem uniformMean_nonzero :
    uniformMean (fun a : K => if a = 0 then 0 else 1) = 1 - 1 / (Fintype.card K : ℝ) := by
  have h := uniformMean_sub (fun _ : K => (1 : ℝ)) (fun a => if a = 0 then 1 else 0)
  simp only [uniformMean_const, uniformMean_singleton] at h
  rw [← h]
  apply uniformMean_congr
  intro a; split <;> simp_all
 theorem uniformMean_character (hK : ringChar K ≠ 2) :
    uniformMean (fun a : K => (quadraticChar K a : ℝ)) = 0 := by
  unfold uniformMean
  have h : (∑ a : K, (quadraticChar K a : ℝ)) = 0 := by
    exact_mod_cast quadraticChar_sum_zero hK
  rw [h, zero_div]
 theorem uniformMean_characterSignIndicator (hK : ringChar K ≠ 2)
    {ξ : ℤ} (hξ : ξ = 1 ∨ ξ = -1) :
    uniformMean (characterSignIndicator (K := K) ξ) =
      (1 - 1 / (Fintype.card K : ℝ)) / 2 := by
  have h := uniformMean_congr (characterSignIndicator_formula (K := K) hξ)
  rw [uniformMean_mul, uniformMean_add, uniformMean_nonzero,
    uniformMean_mul, uniformMean_character hK, mul_zero, add_zero] at h
  linarith
 def scalarAffineEquiv (c b : K) (hc : c ≠ 0) : K ≃ K where
  toFun a := c * (a-b)
  invFun t := t/c+b
  left_inv a := by field_simp; ring
  right_inv t := by field_simp; ring
omit [DecidableEq K] in
 theorem uniformMean_affine (c b : K) (hc : c ≠ 0) (f : K → ℝ) :
    uniformMean (fun a => f (c * (a-b))) = uniformMean f :=
  uniformMean_equiv (scalarAffineEquiv c b hc) f
end Scalar
section MatrixSign
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
noncomputable def symmetricSingularProb (n : ℕ) : ℝ :=
  uniformMean fun M : SymMatrix K n => if M.val.det = 0 then 1 else 0
noncomputable def symmetricSignProb (n : ℕ) (ξ : ℤ) : ℝ :=
  uniformMean fun M : SymMatrix K n => characterSignIndicator ξ M.val.det
 theorem border_singularMean {n : ℕ} (M : SymMatrix K n) (z : Fin n → K)
    (hM : M.val.det ≠ 0) :
    uniformMean (fun a => if (symmetricBorder M z a).val.det = 0 then 1 else 0) =
      1 / (Fintype.card K : ℝ) := by
  simp_rw [symmetricBorder_det M z _ hM, mul_eq_zero, hM, false_or, sub_eq_zero]
  exact uniformMean_singleton _
 theorem border_signMean {n : ℕ} (M : SymMatrix K n) (z : Fin n → K)
    (hM : M.val.det ≠ 0) (hK : ringChar K ≠ 2) {ξ : ℤ} (hξ : ξ = 1 ∨ ξ = -1) :
    uniformMean (fun a => characterSignIndicator ξ (symmetricBorder M z a).val.det) =
      (1 - 1 / (Fintype.card K : ℝ)) / 2 := by
  simp_rw [symmetricBorder_det M z _ hM]
  rw [uniformMean_affine _ _ hM, uniformMean_characterSignIndicator hK hξ]
 theorem symmetricSingularProb_zero : symmetricSingularProb (K := K) 0 = 0 := by
  unfold symmetricSingularProb
  simp [Matrix.det_isEmpty, uniformMean]
 theorem symmetricSingularProb_succ (n : ℕ) :
    symmetricSingularProb (K := K) (n+1) ≤
      symmetricSingularProb (K := K) n + 1 / (Fintype.card K : ℝ) := by
  classical
  unfold symmetricSingularProb
  rw [← uniformMean_equiv (symmetricBorderEquiv (K := K) n).symm,
    uniformMean_prod]
  dsimp only [Function.comp_def, symmetricBorderEquiv, Equiv.coe_fn_symm_mk]
  calc
    _ ≤ uniformMean (fun M : SymMatrix K n =>
        (if M.val.det = 0 then 1 else 0) + 1 / (Fintype.card K : ℝ)) := by
      apply uniformMean_mono
      intro M
      rw [uniformMean_prod]
      by_cases hM : M.val.det = 0
      · simp only [hM, ite_true]
        apply le_trans (show uniformMean (fun z => uniformMean (fun a =>
          if (symmetricBorder M z a).val.det = 0 then 1 else 0)) ≤ 1 from
          uniformMean_bound fun z => uniformMean_bound fun a => by split <;> norm_num)
        have : (0 : ℝ) ≤ 1 / (Fintype.card K : ℝ) := by positivity
        linarith
      · simp only [hM, ite_false, zero_add]
        simp_rw [border_singularMean M _ hM]
        exact le_of_eq (uniformMean_const _)
    _ = _ := by rw [uniformMean_add, uniformMean_const]
 theorem symmetricSingularProb_bound (n : ℕ) :
    symmetricSingularProb (K := K) n ≤ n / (Fintype.card K : ℝ) := by
  induction n with
  | zero => simp [symmetricSingularProb_zero]
  | succ n ih =>
    calc
      _ ≤ symmetricSingularProb (K := K) n + 1 / (Fintype.card K : ℝ) :=
        symmetricSingularProb_succ n
      _ ≤ n / (Fintype.card K : ℝ) + 1 / (Fintype.card K : ℝ) := by linarith
      _ = _ := by push_cast; ring
 theorem symmetricSignProb_succ_error (n : ℕ) (hK : ringChar K ≠ 2)
    {ξ : ℤ} (hξ : ξ = 1 ∨ ξ = -1) :
    |symmetricSignProb (K := K) (n+1) ξ - 1/2| ≤
      symmetricSingularProb (K := K) n + 1 / (Fintype.card K : ℝ) := by
  classical
  have hq : (0 : ℝ) ≤ 1 / (Fintype.card K : ℝ) := by positivity
  unfold symmetricSignProb
  rw [← uniformMean_equiv (symmetricBorderEquiv (K := K) n).symm, uniformMean_prod]
  dsimp only [Function.comp_def, symmetricBorderEquiv, Equiv.coe_fn_symm_mk]
  rw [← uniformMean_const (A := SymMatrix K n) (1/2), ← uniformMean_sub]
  calc
    _ ≤ uniformMean (fun M : SymMatrix K n =>
      |uniformMean (fun za : (Fin n → K) × K =>
        characterSignIndicator ξ (symmetricBorder M za.1 za.2).val.det) - 1/2|) :=
      abs_uniformMean_le _
    _ ≤ uniformMean (fun M : SymMatrix K n =>
        (if M.val.det = 0 then 1 else 0) + 1 / (Fintype.card K : ℝ)) := by
      apply uniformMean_mono
      intro M
      rw [uniformMean_prod]
      by_cases hM : M.val.det = 0
      · simp only [hM, ite_true]
        have h0 := uniformMean_nonneg (fun z : Fin n → K =>
          uniformMean_nonneg fun a => characterSignIndicator_nonneg ξ
            (symmetricBorder M z a).val.det)
        have h1 := uniformMean_bound (fun z : Fin n → K =>
          uniformMean_bound fun a => characterSignIndicator_le_one ξ
            (symmetricBorder M z a).val.det)
        apply abs_le.mpr
        constructor <;> linarith
      · simp only [hM, ite_false, zero_add]
        simp_rw [border_signMean M _ hM hK hξ]
        rw [uniformMean_const]
        apply abs_le.mpr
        constructor <;> linarith
    _ = _ := by rw [uniformMean_add, uniformMean_const]; rfl
 theorem symmetricSignProb_error (n : ℕ) (hn : 0 < n) (hK : ringChar K ≠ 2)
    {ξ : ℤ} (hξ : ξ = 1 ∨ ξ = -1) :
    |symmetricSignProb (K := K) n ξ - 1/2| ≤ n / (Fintype.card K : ℝ) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  calc
    _ ≤ symmetricSingularProb (K := K) m + 1 / (Fintype.card K : ℝ) :=
      symmetricSignProb_succ_error m hK hξ
    _ ≤ m / (Fintype.card K : ℝ) + 1 / (Fintype.card K : ℝ) := by
      have := symmetricSingularProb_bound (K := K) m
      linarith
    _ = _ := by push_cast; ring
end MatrixSign
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module LinearMap
section NondegSign
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [FiniteDimensional K V] [Fintype K] [DecidableEq K]
theorem discriminantSign_nondegenerate (B : LinearMap.BilinForm K V)
    (hBs : B.IsSymm) (hB : B.Nondegenerate)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι K V) :
    discriminantSign B hBs = quadraticChar K (B.toMatrix b).det := by
  simpa only [LinearMap.compl₁₂_id_id] using
    discriminantSign_pullback B hBs hB LinearMap.id Function.surjective_id b
end NondegSign
section SumForms
variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]
def orthogonalSumForm (A : LinearMap.BilinForm K V) (B : LinearMap.BilinForm K W) :
    LinearMap.BilinForm K (V × W) :=
  A.compl₁₂ (LinearMap.fst K V W) (LinearMap.fst K V W) +
    B.compl₁₂ (LinearMap.snd K V W) (LinearMap.snd K V W)
@[simp] theorem orthogonalSumForm_apply (A : LinearMap.BilinForm K V)
    (B : LinearMap.BilinForm K W) (x y : V × W) :
    orthogonalSumForm A B x y = A x.1 y.1 + B x.2 y.2 := rfl
theorem orthogonalSumForm_isSymm (A : LinearMap.BilinForm K V)
    (B : LinearMap.BilinForm K W) (hA : A.IsSymm) (hB : B.IsSymm) :
    (orthogonalSumForm A B).IsSymm := by
  constructor
  intro x y
  simp only [orthogonalSumForm_apply, hA.eq x.1 y.1, hB.eq x.2 y.2]
theorem orthogonalSumForm_nondegenerate (A : LinearMap.BilinForm K V)
    (B : LinearMap.BilinForm K W) (hA : A.Nondegenerate) (hB : B.Nondegenerate) :
    (orthogonalSumForm A B).Nondegenerate := by
  constructor
  · intro x hx
    apply Prod.ext
    · apply hA.1
      intro y
      simpa using hx (y, 0)
    · apply hB.1
      intro y
      simpa using hx (0, y)
  · intro x hx
    apply Prod.ext
    · apply hA.2
      intro y
      simpa using hx (y, 0)
    · apply hB.2
      intro y
      simpa using hx (0, y)
theorem orthogonalSumForm_matrix (A : LinearMap.BilinForm K V)
    (B : LinearMap.BilinForm K W) {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (b : Basis ι K V) (c : Basis κ K W) :
    (orthogonalSumForm A B).toMatrix (b.prod c) =
      Matrix.fromBlocks (A.toMatrix b) 0 0 (B.toMatrix c) := by
  ext i j
  cases i <;> cases j <;>
    simp [LinearMap.BilinForm.toMatrix_apply, Basis.prod_apply]
variable [FiniteDimensional K V] [Fintype K] [DecidableEq K]
end SumForms
section PairSign
variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]
variable [Fintype K] [DecidableEq K]
end PairSign
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module LinearMap
section RadicalCount
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype K] [DecidableEq K]
omit [Fintype K] [DecidableEq K] in
 theorem symFormQuotient_nondegenerate_iff (U : Submodule K V) (C : SymForm K (V ⧸ U)) :
    (C.val.compl₁₂ U.mkQ U.mkQ).ker = U ↔ C.val.Nondegenerate := by
  constructor
  · intro h
    apply LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot.mpr
    apply bot_unique
    intro x hx
    obtain ⟨y, rfl⟩ := U.mkQ_surjective x
    apply (Submodule.Quotient.mk_eq_zero U).mpr
    rw [← h]
    apply LinearMap.mem_ker.mpr
    ext z
    exact congrArg (fun f => f (U.mkQ z)) hx
  · intro h
    rw [pullback_ker C.val h U.mkQ U.mkQ_surjective, Submodule.ker_mkQ]
 theorem discriminantSign_pullback_nondegenerate (U : Submodule K V)
    (C : SymForm K (V ⧸ U)) (hC : C.val.Nondegenerate) :
    discriminantSign (C.val.compl₁₂ U.mkQ U.mkQ)
      (pullback_isSymm C.val C.property U.mkQ) = discriminantSign C.val C.property := by
  rw [discriminantSign_pullback C.val C.property hC U.mkQ U.mkQ_surjective
    (Module.finBasis K (V ⧸ U)),
    discriminantSign_nondegenerate C.val C.property hC (Module.finBasis K (V ⧸ U))]
noncomputable def signedRadicalFiberEquiv (U : Submodule K V) (ξ : ℤ) :
    {B : SymForm K V // B.val.ker = U ∧ discriminantSign B.val B.property = ξ} ≃
      {C : SymForm K (V ⧸ U) // C.val.Nondegenerate ∧
        discriminantSign C.val C.property = ξ} := by
  let e : {B : SymForm K V // B.val.ker = U ∧ discriminantSign B.val B.property = ξ} ≃
      {B : {B : SymForm K V // U ≤ B.val.ker} //
        B.val.val.ker = U ∧ discriminantSign B.val.val B.val.property = ξ} :=
    { toFun := fun B => ⟨⟨B.val, le_of_eq B.property.1.symm⟩, B.property⟩
      invFun := fun B => ⟨B.val.val, B.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  refine e.trans ((formRadicalEquiv U).subtypeEquiv ?_)
  intro B
  let C := formRadicalEquiv U B
  have hback : C.val.compl₁₂ U.mkQ U.mkQ = B.val.val := rfl
  have hn : B.val.val.ker = U ↔ C.val.Nondegenerate := by
    rw [← hback]; exact symFormQuotient_nondegenerate_iff U C
  constructor
  · rintro ⟨hB,hξ⟩
    have hC := hn.mp hB
    refine ⟨hC, ?_⟩
    have hs := discriminantSign_pullback_nondegenerate U C hC
    change discriminantSign B.val.val B.val.property = discriminantSign C.val C.property at hs
    exact hs.symm.trans hξ
  · rintro ⟨hC,hξ⟩
    refine ⟨hn.mpr hC, ?_⟩
    have hs := discriminantSign_pullback_nondegenerate U C hC
    change discriminantSign B.val.val B.val.property = discriminantSign C.val C.property at hs
    exact hs.trans hξ
noncomputable def nonsingularSignedMatrixEquiv (ξ : ℤ) :
    {C : SymForm K V // C.val.Nondegenerate ∧ discriminantSign C.val C.property = ξ} ≃
      {M : SymMatrix K (finrank K V) // quadraticChar K M.val.det = ξ ∧ M.val.det ≠ 0} := by
  refine (symFormMatrix K V).subtypeEquiv ?_
  intro C
  have hn : C.val.Nondegenerate ↔ (C.val.toMatrix (Module.finBasis K V)).det ≠ 0 :=
    LinearMap.BilinForm.nondegenerate_iff_det_ne_zero (Module.finBasis K V)
  constructor
  · rintro ⟨hC,hξ⟩
    refine ⟨?_, hn.mp hC⟩
    change quadraticChar K (C.val.toMatrix (Module.finBasis K V)).det = ξ
    rw [← discriminantSign_nondegenerate C.val C.property hC (Module.finBasis K V)]
    exact hξ
  · rintro ⟨hξ,hC⟩
    refine ⟨hn.mpr hC, ?_⟩
    rw [discriminantSign_nondegenerate C.val C.property (hn.mpr hC) (Module.finBasis K V)]
    exact hξ
 theorem nonsingularSignedForm_card {r : ℕ} (hV : finrank K V = r)
    {ξ : ℤ} (hξ : ξ = 1 ∨ ξ = -1) :
    Nat.card {C : SymForm K V // C.val.Nondegenerate ∧ discriminantSign C.val C.property = ξ} =
      Nat.card {M : SymMatrix K r // quadraticChar K M.val.det = ξ} := by
  rw [Nat.card_congr (nonsingularSignedMatrixEquiv (K := K) (V := V) ξ), hV]
  apply Nat.card_congr
  apply Equiv.subtypeEquiv (Equiv.refl _)
  intro M
  simp only [Equiv.refl_apply, and_iff_left_iff_imp]
  intro h
  apply mt quadraticChar_eq_zero_iff.mpr
  rw [h]
  rcases hξ with rfl | rfl <;> norm_num
 theorem signedRadicalFiber_card (U : Submodule K V) {r : ℕ}
    (hU : finrank K (V ⧸ U) = r) {ξ : ℤ} (hξ : ξ = 1 ∨ ξ = -1) :
    Nat.card {B : SymForm K V // B.val.ker = U ∧ discriminantSign B.val B.property = ξ} =
      Nat.card {M : SymMatrix K r // quadraticChar K M.val.det = ξ} := by
  rw [Nat.card_congr (signedRadicalFiberEquiv U ξ)]
  exact nonsingularSignedForm_card hU hξ
end RadicalCount
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module LinearMap
open scoped BigOperators
section RankCard
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype K] [DecidableEq K]
noncomputable def signedNullityFiberEquiv (k : ℕ) (ξ : ℤ) :
    {B : SymForm K V // finrank K B.val.ker = k ∧ discriminantSign B.val B.property = ξ} ≃
      Σ U : DimSubspace K V k,
        {B : SymForm K V // B.val.ker = U.val ∧ discriminantSign B.val B.property = ξ} where
  toFun B := ⟨⟨B.val.val.ker, B.property.1⟩, ⟨B.val, rfl, B.property.2⟩⟩
  invFun UB := ⟨UB.2.val, by rw [UB.2.property.1]; exact UB.1.property, UB.2.property.2⟩
  left_inv _ := rfl
  right_inv := by
    rintro ⟨⟨U,hU⟩,⟨B,hB,hξ⟩⟩
    dsimp only
    change B.val.ker = U at hB
    subst U
    rfl
 theorem signedNullityForm_card (k : ℕ) (_hk : k ≤ finrank K V)
    {ξ : ℤ} (hξ : ξ = 1 ∨ ξ = -1) :
    Nat.card {B : SymForm K V // finrank K B.val.ker = k ∧ discriminantSign B.val B.property = ξ} =
      Nat.card (DimSubspace K V k) *
        Nat.card {M : SymMatrix K (finrank K V - k) // quadraticChar K M.val.det = ξ} := by
  classical
  let : Finite V := Module.finite_of_finite K
  let : Fintype (DimSubspace K V k) := Fintype.ofFinite _
  rw [Nat.card_congr (signedNullityFiberEquiv k ξ), Nat.card_sigma]
  have hf (U : DimSubspace K V k) :
      Nat.card {B : SymForm K V // B.val.ker = U.val ∧ discriminantSign B.val B.property = ξ} =
        Nat.card {M : SymMatrix K (finrank K V - k) // quadraticChar K M.val.det = ξ} := by
    apply signedRadicalFiber_card U.val _ hξ
    have := U.val.finrank_quotient_add_finrank
    rw [U.property] at this
    omega
  simp only [hf, Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Nat.card_eq_fintype_card, Nat.cast_id]
end RankCard
section LayerCard
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
noncomputable def matrixFormEquiv (D : ℕ) : SymMatrix K D ≃ SymForm K (Fin D → K) :=
  Equiv.subtypeEquiv Matrix.toBilin'.toEquiv
    (fun _M => Matrix.isSymm_toBilin'_iff_isSymm.symm)
 theorem signedLayer_card_exact (D r : ℕ) (hrD : r ≤ D) {ξ : ℤ} (hξ : ξ = 1 ∨ ξ = -1) :
    (signedLayer K D r ξ).card =
      Nat.card (DimSubspace K (Fin D → K) (D-r)) *
        Nat.card {M : SymMatrix K r // quadraticChar K M.val.det = ξ} := by
  classical
  have e : {M : SymMatrix K D // M.val.rank = r ∧ matrixSign K D M = ξ} ≃
      {B : SymForm K (Fin D → K) // finrank K B.val.ker = D-r ∧
        discriminantSign B.val B.property = ξ} := by
    apply (matrixFormEquiv D).subtypeEquiv
    intro M
    change (M.val.rank = r ∧ matrixSign K D M = ξ) ↔
      (finrank K M.val.toBilin'.ker = D-r ∧ matrixSign K D M = ξ)
    have h := M.val.toBilin'.ker.finrank_quotient_add_finrank
    rw [matrix_radical_quotient_rank] at h
    simp only [Module.finrank_pi, Fintype.card_fin] at h
    omega
  calc
    _ = Nat.card {M : SymMatrix K D // M.val.rank = r ∧ matrixSign K D M = ξ} := by
      simp only [signedLayer, Nat.card_eq_fintype_card, Fintype.card_subtype]
    _ = _ := by
      rw [Nat.card_congr e, signedNullityForm_card (D-r) (by simp) hξ]
      have hd : finrank K (Fin D → K) = D := by simp
      rw [hd, Nat.sub_sub_self hrD]
 theorem symmetricSignProb_card (r : ℕ) (ξ : ℤ) :
    symmetricSignProb (K := K) r ξ =
      (Nat.card {M : SymMatrix K r // quadraticChar K M.val.det = ξ} : ℝ) /
        (Fintype.card K : ℝ)^((r+1).choose 2) := by
  unfold symmetricSignProb characterSignIndicator
  rw [uniformMean_indicator, ← Nat.card_eq_fintype_card (α := SymMatrix K r), symMatrix_card]
  simp only [Nat.card_eq_fintype_card, Nat.cast_pow]
 theorem layerMass_exact (D r : ℕ) (hrD : r ≤ D) {ξ : ℤ} (hξ : ξ = 1 ∨ ξ = -1) :
    layerMass K D r ξ =
      (Nat.card (DimSubspace K (Fin D → K) (D-r)) : ℝ) *
        (Fintype.card K : ℝ)^((r+1).choose 2) * symmetricSignProb (K := K) r ξ /
        (Fintype.card K : ℝ)^((D+1).choose 2) := by
  unfold layerMass
  rw [signedLayer_card_exact D r hrD hξ, ← Nat.card_eq_fintype_card, symMatrix_card,
    symmetricSignProb_card]
  push_cast
  have hq : (Fintype.card K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp
end LayerCard
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module LinearMap
open scoped BigOperators
section Binary
variable {K : Type*} [Field K] [Fintype K]
theorem binary_norm_surjective (hK : ringChar K ≠ 2) (a b t : K)
    (ha : a ≠ 0) (hb : b ≠ 0) : ∃ x y : K, a*x^2+b*y^2=t := by
  open Polynomial in
  have hf : (C a * X^2 : K[X]).degree = 2 := degree_C_mul_X_pow 2 ha
  open Polynomial in
  have hg : (C b * X^2 - C t : K[X]).degree = 2 := by
    rw [degree_sub_C (by rw [degree_C_mul_X_pow 2 hb]; decide), degree_C_mul_X_pow 2 hb]
    norm_num
  obtain ⟨x,y,hxy⟩ := FiniteField.exists_root_sum_quadratic hf hg
    (FiniteField.odd_card_of_char_ne_two hK)
  refine ⟨x,y,?_⟩
  simpa only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
    ← add_sub_assoc, sub_eq_zero] using hxy
end Binary
section Norms
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]
theorem nondegenerate_ne_zero_of_pos (B : LinearMap.BilinForm K E)
    (hB : B.Nondegenerate) (hd : 0 < finrank K E) : B ≠ 0 := by
  intro h
  have hz : ∀ x : E, x=0 := by
    intro x
    apply hB.1
    intro y
    rw [h]
    rfl
  have hzdim : finrank K E=0 := (finrank_zero_iff_forall_zero).mpr hz
  omega
theorem orthogonal_line_finrank (B : LinearMap.BilinForm K E) {x : E}
    (hx : B x x ≠ 0) : finrank K (B.orthogonal (K ∙ x)) + 1 = finrank K E := by
  have hx0 : x ≠ 0 := by intro h; subst x; simp at hx
  have h := Submodule.finrank_add_eq_of_isCompl (B.isCompl_span_singleton_orthogonal hx)
  rw [finrank_span_singleton hx0] at h
  omega
variable [Fintype K]
theorem symmetric_norm_surjective (B : LinearMap.BilinForm K E) (hs : B.IsSymm)
    (hB : B.Nondegenerate) (hD : 2 ≤ finrank K E) (hK : ringChar K ≠ 2) (t : K) :
    ∃ v : E, B v v = t := by
  let : Invertible (2 : K) := invertibleOfNonzero (Ring.two_ne_zero hK)
  obtain ⟨x,hx⟩ := LinearMap.BilinForm.exists_bilinForm_self_ne_zero
    (nondegenerate_ne_zero_of_pos B hB (by omega)) (LinearMap.BilinForm.isSymm_iff.mp hs)
  let P := B.orthogonal (K ∙ x)
  have hPs : (B.restrict P).IsSymm := by constructor; intro u v; exact hs.eq _ _
  have hP := B.restrict_nondegenerate_orthogonal_spanSingleton hB hs.isRefl hx
  have hd : 0 < finrank K P := by have := orthogonal_line_finrank B hx; dsimp [P]; omega
  obtain ⟨y,hy⟩ := LinearMap.BilinForm.exists_bilinForm_self_ne_zero
    (nondegenerate_ne_zero_of_pos (B.restrict P) hP hd) (LinearMap.BilinForm.isSymm_iff.mp hPs)
  obtain ⟨a,b,hab⟩ := binary_norm_surjective hK (B x x) (B y.val y.val) t hx hy
  have hxy : B x y.val = 0 := y.property x (Submodule.mem_span_singleton_self x)
  have hyx : B y.val x = 0 := (hs.eq _ _).trans hxy
  refine ⟨a • x + b • y.val, ?_⟩
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    hxy, hyx, mul_zero, add_zero, zero_add]
  linear_combination hab
end Norms
section Equivalences
variable {K E F : Type*} [Field K] [AddCommGroup E] [Module K E]
  [AddCommGroup F] [Module K F]
def BilinEquivalent (B : LinearMap.BilinForm K E) (C : LinearMap.BilinForm K F) : Prop :=
  ∃ e : E ≃ₗ[K] F, ∀ x y, C (e x) (e y) = B x y
def scalarBilin (a : K) : LinearMap.BilinForm K K := a • LinearMap.mul K K
@[simp] theorem scalarBilin_apply (a x y : K) : scalarBilin a x y = a*x*y := by
  simp only [scalarBilin, LinearMap.smul_apply, LinearMap.mul_apply', smul_eq_mul]
  ring
theorem scalarBilin_symm (a : K) : (scalarBilin a).IsSymm := by
  constructor; intro x y; simp only [scalarBilin_apply]; ring
theorem scalarBilin_nondegenerate (a : K) (ha : a≠0) : (scalarBilin a).Nondegenerate := by
  constructor
  · intro x hx; have h := hx 1; simpa only [scalarBilin_apply, mul_one, mul_eq_zero,ha,false_or] using h
  · intro x hx; have h := hx 1; simpa only [scalarBilin_apply, mul_one, mul_eq_zero,ha,false_or] using h
noncomputable def lineOrthogonalEquiv (B : LinearMap.BilinForm K E) (x : E)
    (hx : B x x ≠ 0) : (K × B.orthogonal (K ∙ x)) ≃ₗ[K] E :=
  ((LinearEquiv.toSpanNonzeroSingleton K E x (by intro h; subst x; simp at hx)).prodCongr
    (LinearEquiv.refl K (B.orthogonal (K ∙ x)))).trans
    ((K ∙ x).prodEquivOfIsCompl _ (B.isCompl_span_singleton_orthogonal hx))
theorem lineOrthogonalEquiv_apply (B : LinearMap.BilinForm K E) (x : E)
    (hx : B x x ≠ 0) (z : K × B.orthogonal (K ∙ x)) :
    lineOrthogonalEquiv B x hx z = z.1 • x + z.2.val := rfl
theorem lineOrthogonalEquiv_form (B : LinearMap.BilinForm K E) (hs : B.IsSymm)
    (x : E) (hx : B x x ≠ 0) (z w : K × B.orthogonal (K ∙ x)) :
    B (lineOrthogonalEquiv B x hx z) (lineOrthogonalEquiv B x hx w) =
      B x x * z.1 * w.1 + B z.2.val w.2.val := by
  have h1 : B x w.2.val = 0 := w.2.property x (Submodule.mem_span_singleton_self x)
  have h2 : B z.2.val x = 0 := (hs.eq _ _).trans (z.2.property x (Submodule.mem_span_singleton_self x))
  rw [lineOrthogonalEquiv_apply, lineOrthogonalEquiv_apply]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    smul_eq_mul,h1,h2,mul_zero,add_zero,zero_add]
  ring
variable [FiniteDimensional K E] [FiniteDimensional K F] [Fintype K] [DecidableEq K]
theorem discriminantSign_isometry (B : LinearMap.BilinForm K E)
    (C : LinearMap.BilinForm K F) (hs : B.IsSymm) (ht : C.IsSymm)
    (hB : B.Nondegenerate) (hC : C.Nondegenerate)
    (e : E ≃ₗ[K] F) (he : ∀ x y, C (e x) (e y) = B x y) :
    discriminantSign B hs = discriminantSign C ht := by
  rw [discriminantSign_nondegenerate B hs hB (Module.finBasis K E),
    discriminantSign_nondegenerate C ht hC ((Module.finBasis K E).map e)]
  congr 2
  ext i j
  simp only [LinearMap.BilinForm.toMatrix_apply, Basis.map_apply, he]
theorem discriminantSign_orthogonalSum (B : LinearMap.BilinForm K E)
    (C : LinearMap.BilinForm K F) (hs : B.IsSymm) (ht : C.IsSymm)
    (hB : B.Nondegenerate) (hC : C.Nondegenerate) :
    discriminantSign (orthogonalSumForm B C) (orthogonalSumForm_isSymm B C hs ht) =
      discriminantSign B hs * discriminantSign C ht := by
  rw [discriminantSign_nondegenerate _ _ (orthogonalSumForm_nondegenerate B C hB hC)
      ((Module.finBasis K E).prod (Module.finBasis K F)), orthogonalSumForm_matrix,
    Matrix.det_fromBlocks_zero₂₁, map_mul,
    discriminantSign_nondegenerate B hs hB (Module.finBasis K E),
    discriminantSign_nondegenerate C ht hC (Module.finBasis K F)]
 theorem discriminantSign_scalar (a : K) (ha : a≠0) :
    discriminantSign (scalarBilin a) (scalarBilin_symm a) = quadraticChar K a := by
  rw [discriminantSign_nondegenerate _ _ (scalarBilin_nondegenerate a ha)
    (Basis.singleton Unit K), Matrix.det_unique]
  simp only [LinearMap.BilinForm.toMatrix_apply, Basis.singleton_apply, scalarBilin_apply, mul_one]
 theorem discriminantSign_line_complement (B : LinearMap.BilinForm K E)
    (hs : B.IsSymm) (hB : B.Nondegenerate) (x : E) (hx : B x x ≠ 0) :
    discriminantSign B hs = quadraticChar K (B x x) *
      discriminantSign (B.restrict (B.orthogonal (K ∙ x)))
        (by constructor; intro u v; exact hs.eq u.val v.val) := by
  let P := B.orthogonal (K ∙ x)
  have hp : (B.restrict P).IsSymm := by constructor; intro u v; exact hs.eq _ _
  have hP := B.restrict_nondegenerate_orthogonal_spanSingleton hB hs.isRefl hx
  have he : discriminantSign (orthogonalSumForm (scalarBilin (B x x)) (B.restrict P))
      (orthogonalSumForm_isSymm _ _ (scalarBilin_symm _) hp) = discriminantSign B hs :=
    discriminantSign_isometry _ _ _ hs
      (orthogonalSumForm_nondegenerate _ _ (scalarBilin_nondegenerate _ hx) hP) hB
      (lineOrthogonalEquiv B x hx) (fun z w => by
        simpa only [orthogonalSumForm_apply,scalarBilin_apply,LinearMap.BilinForm.restrict_apply,LinearMap.domRestrict_apply] using lineOrthogonalEquiv_form B hs x hx z w)
  rw [← he, discriminantSign_orthogonalSum _ _ (scalarBilin_symm _) hp (scalarBilin_nondegenerate _ hx) hP,
    discriminantSign_scalar _ hx]
end Equivalences
section Classification
variable {K E F : Type*} [Field K] [AddCommGroup E] [Module K E]
  [AddCommGroup F] [Module K F] [FiniteDimensional K E] [FiniteDimensional K F]
  [Fintype K] [DecidableEq K]
theorem scalarBilin_equivalent_of_sign (a b : K) (ha : a≠0) (hb : b≠0)
    (h : quadraticChar K a = quadraticChar K b) : BilinEquivalent (scalarBilin a) (scalarBilin b) := by
  have hc : quadraticChar K (a*b) = 1 := by
    rw [map_mul,h,←pow_two,quadraticChar_sq_one hb]
  obtain ⟨t,ht⟩ := (quadraticChar_one_iff_isSquare (mul_ne_zero ha hb)).mp hc
  have ht0 : t≠0 := by intro hz; rw [hz,mul_zero] at ht; exact mul_ne_zero ha hb ht
  have hscale : b*(t/b)^2=a := by
    field_simp
    linear_combination ht.symm
  refine ⟨LinearEquiv.smulOfNeZero K K (t/b) (div_ne_zero ht0 hb), ?_⟩
  intro x y
  simp only [LinearEquiv.smulOfNeZero_apply,smul_eq_mul,scalarBilin_apply]
  linear_combination x*y*hscale
omit [Fintype K] [DecidableEq K] in
theorem one_dimensional_form (B : LinearMap.BilinForm K E) (hD : finrank K E=1) :
    ∃ e : K ≃ₗ[K] E, ∀ s t : K, B (e s) (e t) = B (e 1) (e 1)*s*t := by
  let e := LinearEquiv.ofFinrankEq (R := K) K E (by simpa using hD.symm)
  refine ⟨e,?_⟩
  intro s t
  have hs : e s = s • e 1 := by rw [←map_smul]; simp
  have ht : e t = t • e 1 := by rw [←map_smul]; simp
  rw [hs,ht]
  simp only [map_smul,LinearMap.smul_apply,smul_eq_mul]
  ring
theorem one_dimensional_equivalent (B : LinearMap.BilinForm K E) (C : LinearMap.BilinForm K F)
    (hs : B.IsSymm) (ht : C.IsSymm) (hB : B.Nondegenerate) (hC : C.Nondegenerate)
    (hE : finrank K E=1) (hF : finrank K F=1)
    (h : discriminantSign B hs = discriminantSign C ht) : BilinEquivalent B C := by
  obtain ⟨e,he⟩ := one_dimensional_form B hE
  obtain ⟨f,hf⟩ := one_dimensional_form C hF
  have ha : B (e 1) (e 1)≠0 := by
    intro hz
    have he1 : e 1=0 := hB.1 _ (fun y => by
      obtain ⟨s,rfl⟩ := e.surjective y
      rw [he,hz]; simp)
    have : (1:K)=0 := e.injective (he1.trans e.map_zero.symm)
    exact one_ne_zero this
  have hb : C (f 1) (f 1)≠0 := by
    intro hz
    have hf1 : f 1=0 := hC.1 _ (fun y => by
      obtain ⟨s,rfl⟩ := f.surjective y
      rw [hf,hz]; simp)
    exact one_ne_zero (f.injective (hf1.trans f.map_zero.symm))
  have hsa := discriminantSign_isometry (scalarBilin (B (e 1) (e 1))) B
    (scalarBilin_symm _) hs (scalarBilin_nondegenerate _ ha) hB e
    (fun s t => by simpa only [scalarBilin_apply] using he s t)
  have hsb := discriminantSign_isometry (scalarBilin (C (f 1) (f 1))) C
    (scalarBilin_symm _) ht (scalarBilin_nondegenerate _ hb) hC f
    (fun s t => by simpa only [scalarBilin_apply] using hf s t)
  rw [discriminantSign_scalar _ ha] at hsa
  rw [discriminantSign_scalar _ hb] at hsb
  obtain ⟨g,hg⟩ := scalarBilin_equivalent_of_sign _ _ ha hb (hsa.trans (h.trans hsb.symm))
  refine ⟨e.symm.trans (g.trans f), ?_⟩
  intro x y
  change C (f (g (e.symm x))) (f (g (e.symm y))) = B x y
  rw [hf]
  have hg' := hg (e.symm x) (e.symm y)
  simp only [scalarBilin_apply] at hg'
  rw [hg']
  have hx := he (e.symm x) (e.symm y)
  simpa only [e.apply_symm_apply,scalarBilin_apply] using hx.symm
 theorem symmetric_equivalent_of_dim_sign (B : LinearMap.BilinForm K E)
    (C : LinearMap.BilinForm K F) (hs : B.IsSymm) (ht : C.IsSymm)
    (hB : B.Nondegenerate) (hC : C.Nondegenerate) (hK : ringChar K≠2)
    (hd : finrank K E = finrank K F)
    (h : discriminantSign B hs = discriminantSign C ht) : BilinEquivalent B C := by
  suffices ∀ n, finrank K E=n → finrank K F=n → BilinEquivalent B C by exact this _ rfl hd.symm
  intro n hnE hnF
  induction n using Nat.strong_induction_on generalizing E F with
  | h n ih =>
    by_cases hn0 : n=0
    · let e := LinearEquiv.ofFinrankEq E F (hnE.trans hnF.symm)
      have hzero : Subsingleton E := Module.finrank_zero_iff.mp (hnE.trans hn0)
      refine ⟨e,?_⟩
      intro x y
      have hx : x=0 := Subsingleton.elim _ _
      simp only [hx,map_zero,LinearMap.zero_apply]
    by_cases hn1 : n=1
    · exact one_dimensional_equivalent B C hs ht hB hC (hnE.trans hn1) (hnF.trans hn1) h
    have hn2 : 2≤n := by omega
    obtain ⟨x,hx⟩ := symmetric_norm_surjective B hs hB (by omega) hK 1
    obtain ⟨y,hy⟩ := symmetric_norm_surjective C ht hC (by omega) hK 1
    have hx0 : B x x≠0 := hx ▸ one_ne_zero
    have hy0 : C y y≠0 := hy ▸ one_ne_zero
    let P := B.orthogonal (K ∙ x)
    let Q := C.orthogonal (K ∙ y)
    have hp : (B.restrict P).IsSymm := by constructor; intro u v; exact hs.eq _ _
    have hq : (C.restrict Q).IsSymm := by constructor; intro u v; exact ht.eq _ _
    have hP := B.restrict_nondegenerate_orthogonal_spanSingleton hB hs.isRefl hx0
    have hQ := C.restrict_nondegenerate_orthogonal_spanSingleton hC ht.isRefl hy0
    have hdP : finrank K P=n-1 := by have := orthogonal_line_finrank B hx0; dsimp [P]; omega
    have hdQ : finrank K Q=n-1 := by have := orthogonal_line_finrank C hy0; dsimp [Q]; omega
    have hdPQ : finrank K P=finrank K Q := hdP.trans hdQ.symm
    have hsP := discriminantSign_line_complement B hs hB x hx0
    have hsQ := discriminantSign_line_complement C ht hC y hy0
    rw [hx,map_one,one_mul] at hsP
    rw [hy,map_one,one_mul] at hsQ
    have hh : discriminantSign (B.restrict P) hp = discriminantSign (C.restrict Q) hq :=
      hsP.symm.trans (h.trans hsQ)
    obtain ⟨g,hg⟩ := ih (n-1) (by omega) (B.restrict P) (C.restrict Q) hp hq hP hQ hdPQ hh hdP hdQ
    let e := (lineOrthogonalEquiv B x hx0).symm.trans
      (((LinearEquiv.refl K K).prodCongr g).trans (lineOrthogonalEquiv C y hy0))
    refine ⟨e,?_⟩
    intro v w
    let a := (lineOrthogonalEquiv B x hx0).symm v
    let b := (lineOrthogonalEquiv B x hx0).symm w
    change C (lineOrthogonalEquiv C y hy0 (a.1,g a.2))
      (lineOrthogonalEquiv C y hy0 (b.1,g b.2)) = B v w
    rw [lineOrthogonalEquiv_form C ht,hy]
    change 1*a.1*b.1 + (C.restrict Q) (g a.2) (g b.2) = B v w
    rw [hg]
    have he := lineOrthogonalEquiv_form B hs x hx0 a b
    rw [hx] at he
    simpa only [a,b,LinearEquiv.apply_symm_apply,LinearMap.BilinForm.restrict_apply,LinearMap.domRestrict_apply] using he.symm
end Classification
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section LinearMean
variable {K U W : Type*} [Field K] [AddCommGroup U] [Module K U]
  [AddCommGroup W] [Module K W] [Fintype U] [Fintype W]
theorem uniformMean_surjective_linear (f : U →ₗ[K] W) (hf : Function.Surjective f)
    (g : W → ℝ) : uniformMean (g ∘ f) = uniformMean g := by
  classical
  have hcard (y : W) : Fintype.card {x : U // f x = y} = Fintype.card f.ker := by
    simpa [Fintype.card_subtype, LinearMap.mem_ker] using
      AddMonoidHom.card_fiber_eq_of_mem_range f (hf y) (hf 0)
  have hc : Fintype.card U = Fintype.card W * Fintype.card f.ker := by
    simpa only [Nat.card_eq_fintype_card] using surjective_linear_card f hf
  unfold uniformMean
  simp only [Function.comp_def]
  rw [←Fintype.sum_fiberwise f (fun x => g (f x))]
  have hs (y : W) : (∑ x : {x : U // f x=y}, g (f x.val)) =
      (Fintype.card f.ker : ℝ)*g y := by
    have he (x : {x : U // f x=y}) : g (f x.val)=g y := congrArg g x.property
    simp only [he,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,hcard]
  simp only [hs]
  rw [←Finset.mul_sum, hc, Nat.cast_mul]
  have hk : (Fintype.card f.ker : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp
end LinearMean
section Forms
variable {K V : Type*} [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
noncomputable instance symForm_fintype : Fintype (SymForm K V) := Fintype.ofFinite _
noncomputable def formSignIndicator (ξ : ℤ) (Q : SymForm K V) : ℝ := by
  classical
  exact if Q.val.Nondegenerate then if discriminantSign Q.val Q.property = ξ then 1 else 0 else 0
noncomputable def formSingularIndicator (Q : SymForm K V) : ℝ := by
  classical
  exact if Q.val.Nondegenerate then 0 else 1
theorem formSignIndicator_matrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) {ξ : ℤ} (hξ : ξ=1 ∨ ξ = -1) (Q : SymForm K V) :
    formSignIndicator ξ Q = characterSignIndicator ξ (Q.val.toMatrix b).det := by
  by_cases h : Q.val.Nondegenerate
  · simp only [formSignIndicator,h,ite_true,characterSignIndicator,
      discriminantSign_nondegenerate Q.val Q.property h b]
  · have hd : (Q.val.toMatrix b).det=0 := by
      simpa only [LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b,not_not] using h
    rcases hξ with rfl | rfl <;>
      simp [formSignIndicator,h,characterSignIndicator,hd]
omit [Fintype K] [FiniteDimensional K V] in
theorem formSingularIndicator_matrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) (Q : SymForm K V) :
    formSingularIndicator Q = if (Q.val.toMatrix b).det=0 then 1 else 0 := by
  simp only [formSingularIndicator,LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b]
  split <;> simp_all
theorem formSignIndicator_nonneg (ξ : ℤ) (Q : SymForm K V) : 0 ≤ formSignIndicator ξ Q := by
  unfold formSignIndicator; split <;> (try split) <;> norm_num
theorem formSignIndicator_le_one (ξ : ℤ) (Q : SymForm K V) : formSignIndicator ξ Q ≤ 1 := by
  unfold formSignIndicator; split <;> (try split) <;> norm_num
theorem formSingularMean_bound :
    uniformMean (formSingularIndicator (K := K) (V := V)) ≤
      (finrank K V : ℝ)/(Fintype.card K : ℝ) := by
  have h := uniformMean_equiv (symFormMatrix K V)
    (fun M : SymMatrix K (finrank K V) => if M.val.det=0 then 1 else 0)
  have he : uniformMean (formSingularIndicator (K := K) (V := V)) =
      symmetricSingularProb (K := K) (finrank K V) := by
    unfold symmetricSingularProb
    rw [←h]; apply uniformMean_congr
    intro Q; exact formSingularIndicator_matrix (Module.finBasis K V) Q
  rw [he]; exact symmetricSingularProb_bound _
variable {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
omit [DecidableEq K] in
theorem uniformMean_restrict (f : W →ₗ[K] V) (hf : Function.Injective f)
    (g : SymForm K W → ℝ) :
    uniformMean (fun Q : SymForm K V => g (symFormPull f Q)) = uniformMean g :=
  uniformMean_surjective_linear (symFormPull f) (symFormPull_surjective f hf) g
end Forms
end SidorenkoCounterexample
end
end OAI
namespace OAI
section
namespace SidorenkoCounterexample
open Module LinearMap
section Projections
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
def FormSelfAdjoint (Q : LinearMap.BilinForm K V) (T : V →ₗ[K] V) : Prop :=
  ∀ x y, Q (T x) y = Q x (T y)
theorem selfAdjoint_projection_ker (Q : LinearMap.BilinForm K V) (hQ : Q.Nondegenerate)
    (T : V →ₗ[K] V) (hT : FormSelfAdjoint Q T) :
    T.ker = Q.orthogonal T.range := by
  ext x
  constructor
  · intro hx y hy
    obtain ⟨z,rfl⟩ := hy
    rw [hT,show T x=0 from hx,map_zero]
  · intro hx
    apply hQ.2
    intro y
    rw [←hT]
    exact hx (T y) ⟨y,rfl⟩
variable [FiniteDimensional K V]
theorem selfAdjoint_projection_nondegenerate (Q : LinearMap.BilinForm K V)
    (hs : Q.IsSymm) (hQ : Q.Nondegenerate) (T : V →ₗ[K] V)
    (hT : FormSelfAdjoint Q T) (hi : IsIdempotentElem T) :
    (Q.restrict T.range).Nondegenerate := by
  apply (Q.restrict_nondegenerate_iff_isCompl_orthogonal hs.isRefl).mpr
  rw [←selfAdjoint_projection_ker Q hQ T hT]
  exact hi.isCompl
noncomputable def formProjection (Q : LinearMap.BilinForm K V) (hs : Q.IsSymm)
    (U : Submodule K V) (hU : (Q.restrict U).Nondegenerate) : V →ₗ[K] V :=
  U.projection (Q.orthogonal U) (Q.isCompl_orthogonal_of_restrict_nondegenerate hs.isRefl hU)
theorem formProjection_idempotent (Q : LinearMap.BilinForm K V) (hs : Q.IsSymm)
    (U : Submodule K V) (hU : (Q.restrict U).Nondegenerate) :
    IsIdempotentElem (formProjection Q hs U hU) := Submodule.isIdempotentElem_projection _
theorem formProjection_range (Q : LinearMap.BilinForm K V) (hs : Q.IsSymm)
    (U : Submodule K V) (hU : (Q.restrict U).Nondegenerate) :
    (formProjection Q hs U hU).range=U := Submodule.range_projection _
theorem formProjection_selfAdjoint (Q : LinearMap.BilinForm K V) (hs : Q.IsSymm)
    (U : Submodule K V) (hU : (Q.restrict U).Nondegenerate) :
    FormSelfAdjoint Q (formProjection Q hs U hU) := by
  intro x y
  let h := Q.isCompl_orthogonal_of_restrict_nondegenerate hs.isRefl hU
  let p := U.projection (Q.orthogonal U) h
  have hx : x-p x ∈ Q.orthogonal U := Submodule.sub_projection_mem h x
  have hy : y-p y ∈ Q.orthogonal U := Submodule.sub_projection_mem h y
  have hpx : p x ∈ U := Submodule.projection_apply_mem h x
  have hpy : p y ∈ U := Submodule.projection_apply_mem h y
  have h1 := hy (p x) hpx
  have h2 := hx (p y) hpy
  simp only [map_sub] at h1 h2
  change Q (p x) y=Q x (p y)
  calc
    _ = Q (p x) (p y) := sub_eq_zero.mp h1
    _ = Q (p y) (p x) := hs.eq _ _
    _ = Q (p y) x := (sub_eq_zero.mp h2).symm
    _ = _ := hs.eq _ _
def SelfAdjointIdempotent (Q : LinearMap.BilinForm K V) :=
  {T : V →ₗ[K] V // IsIdempotentElem T ∧ FormSelfAdjoint Q T}
noncomputable def selfAdjointProjectionEquiv (Q : LinearMap.BilinForm K V)
    (hs : Q.IsSymm) (hQ : Q.Nondegenerate) :
    SelfAdjointIdempotent Q ≃ {U : Submodule K V // (Q.restrict U).Nondegenerate} where
  toFun T := ⟨T.val.range,selfAdjoint_projection_nondegenerate Q hs hQ T.val T.property.2 T.property.1⟩
  invFun U := ⟨formProjection Q hs U.val U.property,formProjection_idempotent Q hs U.val U.property,
    formProjection_selfAdjoint Q hs U.val U.property⟩
  left_inv T := by
    apply Subtype.ext
    let hU := selfAdjoint_projection_nondegenerate Q hs hQ T.val T.property.2 T.property.1
    apply ((formProjection_idempotent Q hs T.val.range hU).ext_iff T.property.1).mpr
    constructor
    · exact formProjection_range Q hs T.val.range hU
    · rw [selfAdjoint_projection_ker Q hQ _ (formProjection_selfAdjoint Q hs T.val.range hU),
        formProjection_range,←selfAdjoint_projection_ker Q hQ T.val T.property.2]
  right_inv U := Subtype.ext (formProjection_range Q hs U.val U.property)
end Projections
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module LinearMap
open scoped Matrix
section MatrixProjection
variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]
theorem matrix_formSelfAdjoint_iff (Q : Matrix n n K) (T : (n → K) →ₗ[K] (n → K)) :
    FormSelfAdjoint Q.toBilin' T ↔ T.toMatrix'ᵀ*Q=Q*T.toMatrix' := by
  change (∀ x y, Q.toBilin'.compLeft T x y = Q.toBilin'.compRight T x y) ↔ _
  rw [←LinearMap.BilinForm.ext_iff]
  rw [←LinearMap.BilinForm.toMatrix'.injective.eq_iff]
  simp only [LinearMap.BilinForm.toMatrix'_compLeft,LinearMap.BilinForm.toMatrix'_compRight,
    LinearMap.BilinForm.toMatrix'_toBilin']
theorem matrix_selfAdjoint_of_symmetric (Q A : Matrix n n K) (hQ : Q.IsSymm) (hA : A.IsSymm) :
    FormSelfAdjoint Q.toBilin' (A*Q).toLin' := by
  rw [matrix_formSelfAdjoint_iff,LinearMap.toMatrix'_toLin',Matrix.transpose_mul,hQ,hA,
    Matrix.mul_assoc]
theorem matrix_projection_idempotent (Q A : Matrix n n K) (hA : A*Q*A=A) :
    IsIdempotentElem (A*Q).toLin' := by
  change (A*Q).toLin'.comp (A*Q).toLin' = (A*Q).toLin'
  rw [←Matrix.toLin'_mul]
  congr 1
  rw [←Matrix.mul_assoc,hA]
def CenterProjection (Q : Matrix n n K) :=
  {A : Matrix n n K // A.IsSymm ∧ A*Q*A=A}
noncomputable def centerToProjection (Q : Matrix n n K) (hQ : Q.IsSymm)
    (A : CenterProjection Q) : SelfAdjointIdempotent Q.toBilin' :=
  ⟨(A.val*Q).toLin',matrix_projection_idempotent Q A.val A.property.2,
    matrix_selfAdjoint_of_symmetric Q A.val hQ A.property.1⟩
theorem projection_to_center_symmetric (Q : Matrix n n K) (hQ : Q.IsSymm)
    (hdet : Q.det≠0) (T : SelfAdjointIdempotent Q.toBilin') :
    (T.val.toMatrix'*Q⁻¹).IsSymm := by
  have h := (matrix_formSelfAdjoint_iff Q T.val).mp T.property.2
  have hu : IsUnit Q.det := isUnit_iff_ne_zero.mpr hdet
  change (T.val.toMatrix'*Q⁻¹)ᵀ=T.val.toMatrix'*Q⁻¹
  rw [Matrix.transpose_mul,hQ.inv]
  calc
    Q⁻¹*T.val.toMatrix'ᵀ = Q⁻¹*(T.val.toMatrix'ᵀ*Q)*Q⁻¹ := by
      simp only [Matrix.mul_assoc,Matrix.mul_nonsing_inv Q hu,Matrix.mul_one]
    _ = Q⁻¹*(Q*T.val.toMatrix')*Q⁻¹ := by rw [h]
    _ = _ := by rw [←Matrix.mul_assoc Q⁻¹ Q,Matrix.nonsing_inv_mul Q hu,Matrix.one_mul]
theorem projection_to_center_identity (Q : Matrix n n K) (hdet : Q.det≠0)
    (T : SelfAdjointIdempotent Q.toBilin') :
    (T.val.toMatrix'*Q⁻¹)*Q*(T.val.toMatrix'*Q⁻¹)=T.val.toMatrix'*Q⁻¹ := by
  have hi : T.val.toMatrix'*T.val.toMatrix'=T.val.toMatrix' := by
    rw [←LinearMap.toMatrix'_comp]
    exact congrArg LinearMap.toMatrix' T.property.1
  have hu : IsUnit Q.det := isUnit_iff_ne_zero.mpr hdet
  rw [Matrix.mul_assoc _ Q⁻¹ Q,Matrix.nonsing_inv_mul Q hu,Matrix.mul_one,
    ←Matrix.mul_assoc,hi]
noncomputable def centerProjectionEquiv (Q : Matrix n n K) (hQ : Q.IsSymm)
    (hdet : Q.det≠0) : CenterProjection Q ≃ SelfAdjointIdempotent Q.toBilin' where
  toFun := centerToProjection Q hQ
  invFun T := ⟨T.val.toMatrix'*Q⁻¹,projection_to_center_symmetric Q hQ hdet T,
    projection_to_center_identity Q hdet T⟩
  left_inv A := by
    apply Subtype.ext
    change (A.val*Q).toLin'.toMatrix'*Q⁻¹=A.val
    rw [LinearMap.toMatrix'_toLin',Matrix.mul_assoc,Matrix.mul_nonsing_inv Q
      (isUnit_iff_ne_zero.mpr hdet),Matrix.mul_one]
  right_inv T := by
    apply Subtype.ext
    change (T.val.toMatrix'*Q⁻¹*Q).toLin'=T.val
    rw [Matrix.mul_assoc,Matrix.nonsing_inv_mul Q (isUnit_iff_ne_zero.mpr hdet),Matrix.mul_one,
      Matrix.toLin'_toMatrix']
noncomputable def centerSubspaceEquiv (Q : Matrix n n K) (hQ : Q.IsSymm)
    (hdet : Q.det≠0) : CenterProjection Q ≃
      {U : Submodule K (n → K) // (Q.toBilin'.restrict U).Nondegenerate} :=
  (centerProjectionEquiv Q hQ hdet).trans
    (selfAdjointProjectionEquiv Q.toBilin' (Matrix.isSymm_toBilin'_iff_isSymm.mpr hQ)
      (Matrix.nondegenerate_toBilin'_iff.mpr (Matrix.nondegenerate_iff_det_ne_zero.mpr hdet)))
end MatrixProjection
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module LinearMap
open scoped Matrix
section Range
variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]
theorem matrix_toLin_surjective (Q : Matrix n n K) (hQ : Q.det≠0) :
    Function.Surjective Q.toLin' := by
  intro x
  refine ⟨Q⁻¹.toLin' x,?_⟩
  change (Q.toLin'.comp Q⁻¹.toLin') x=x
  rw [←Matrix.toLin'_mul,Matrix.mul_nonsing_inv Q (isUnit_iff_ne_zero.mpr hQ),Matrix.toLin'_one]
  rfl
theorem matrix_mul_range (A Q : Matrix n n K) (hQ : Q.det≠0) :
    (A*Q).toLin'.range=A.toLin'.range := by
  rw [Matrix.toLin'_mul,LinearMap.range_comp_of_range_eq_top _
    (LinearMap.range_eq_top.mpr (matrix_toLin_surjective Q hQ))]
theorem centerSubspaceEquiv_val (Q : Matrix n n K) (hQ : Q.IsSymm) (hdet : Q.det≠0)
    (A : CenterProjection Q) : (centerSubspaceEquiv Q hQ hdet A).val=A.val.toLin'.range :=
  matrix_mul_range A.val Q hdet
theorem center_restriction_nondegenerate (Q A : Matrix n n K) (hQ : Q.IsSymm)
    (hdet : Q.det≠0) (hA : A.IsSymm) (hi : A*Q*A=A) :
    (Q.toBilin'.restrict A.toLin'.range).Nondegenerate := by
  have h := (centerSubspaceEquiv Q hQ hdet ⟨A,hA,hi⟩).property
  rw [centerSubspaceEquiv_val Q hQ hdet ⟨A,hA,hi⟩] at h
  exact h
theorem center_form_pullback (Q A : Matrix n n K) (hA : A.IsSymm) (hi : A*Q*A=A) :
    (Q.toBilin'.restrict A.toLin'.range).compl₁₂ A.toLin'.rangeRestrict A.toLin'.rangeRestrict =
      A.toBilin' := by
  change Q.toBilin'.comp A.toLin' A.toLin' = _
  rw [Matrix.toBilin'_comp,hA,hi]
theorem center_second_equation (Q R A : Matrix n n K) (hA : A.IsSymm) (hi : A*Q*A=A) :
    A*R*A=A ↔ ((Q-R).toBilin'.restrict A.toLin'.range)=0 := by
  have hp : (Q-R).toBilin'.comp A.toLin' A.toLin' = (A-A*R*A).toBilin' := by
    rw [Matrix.toBilin'_comp,hA,mul_sub,sub_mul,hi]
  constructor
  · intro h
    rw [h,sub_self,map_zero] at hp
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    obtain ⟨x0,hx⟩ := x.property
    obtain ⟨y0,hy⟩ := y.property
    change (Q-R).toBilin' x.val y.val=0
    rw [←hx,←hy]
    exact congrArg (fun B : LinearMap.BilinForm K (n → K) => B x0 y0) hp
  · intro h
    have hz : (Q-R).toBilin'.comp A.toLin' A.toLin'=0 := by
      apply LinearMap.ext
      intro x
      apply LinearMap.ext
      intro y
      exact congrArg (fun B : LinearMap.BilinForm K A.toLin'.range =>
        B (A.toLin'.rangeRestrict x) (A.toLin'.rangeRestrict y)) h
    rw [hz] at hp
    have he := Matrix.toBilin'.injective (hp.symm.trans (map_zero Matrix.toBilin').symm)
    exact (sub_eq_zero.mp he).symm
variable [Fintype K] [DecidableEq K]
theorem center_discriminant (Q A : Matrix n n K) (hQ : Q.IsSymm) (hdet : Q.det≠0)
    (hA : A.IsSymm) (hi : A*Q*A=A) :
    discriminantSign A.toBilin' (Matrix.isSymm_toBilin'_iff_isSymm.mpr hA) =
      discriminantSign (Q.toBilin'.restrict A.toLin'.range)
        ((Matrix.isSymm_toBilin'_iff_isSymm.mpr hQ).restrict _) := by
  let f := A.toLin'.rangeRestrict
  let B := Q.toBilin'.restrict A.toLin'.range
  have hs : B.IsSymm := (Matrix.isSymm_toBilin'_iff_isSymm.mpr hQ).restrict _
  have hb : B.Nondegenerate := center_restriction_nondegenerate Q A hQ hdet hA hi
  have h := discriminantSign_pullback B hs hb f A.toLin'.surjective_rangeRestrict
    (Module.finBasis K A.toLin'.range)
  rw [discriminantSign_nondegenerate B hs hb (Module.finBasis K A.toLin'.range)]
  rw [←h]
  congr 1
  exact (center_form_pullback Q A hA hi).symm
end Range
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module LinearMap
open scoped Matrix
section FormSum
variable {K V : Type*} [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
theorem discriminantSign_complements (Q : LinearMap.BilinForm K V) (hs : Q.IsSymm)
    (hQ : Q.Nondegenerate) (U W : Submodule K V) (hc : IsCompl U W)
    (hU : (Q.restrict U).Nondegenerate) (hW : (Q.restrict W).Nondegenerate)
    (ho : ∀ u : U, ∀ w : W, Q u.val w.val=0) :
    discriminantSign Q hs = discriminantSign (Q.restrict U) (hs.restrict U) *
      discriminantSign (Q.restrict W) (hs.restrict W) := by
  have he := discriminantSign_isometry
    (orthogonalSumForm (Q.restrict U) (Q.restrict W)) Q
    (orthogonalSumForm_isSymm _ _ (hs.restrict U) (hs.restrict W)) hs
    (orthogonalSumForm_nondegenerate _ _ hU hW) hQ (U.prodEquivOfIsCompl W hc)
    (fun x y => by
      simp only [Submodule.coe_prodEquivOfIsCompl',map_add,LinearMap.add_apply,
        orthogonalSumForm_apply,LinearMap.BilinForm.restrict_apply,LinearMap.domRestrict_apply]
      rw [ho x.1 y.2,hs.eq x.2.val y.1.val,ho y.1 x.2]
      ring)
  rw [discriminantSign_orthogonalSum _ _ _ _ hU hW] at he
  exact he.symm
end FormSum
section Complement
variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]
theorem center_complement_equation (B A : Matrix n n K) (hB : B.det≠0)
    (hi : A*B⁻¹*A=A) : (B-A)*B⁻¹*(B-A)=B-A := by
  have hu : IsUnit B.det := isUnit_iff_ne_zero.mpr hB
  rw [sub_mul,Matrix.mul_nonsing_inv B hu,sub_mul,one_mul,mul_sub,hi,
    Matrix.mul_assoc A B⁻¹ B,Matrix.nonsing_inv_mul B hu,Matrix.mul_one]
  abel
theorem center_complement_ranges (B A : Matrix n n K) (hB : B.det≠0)
    (hi : A*B⁻¹*A=A) : IsCompl A.toLin'.range (B-A).toLin'.range := by
  let T := (A*B⁻¹).toLin'
  have ht := matrix_projection_idempotent B⁻¹ A hi
  have hiB : B⁻¹.det≠0 := by simpa only [Matrix.det_nonsing_inv, Ring.inverse_eq_inv] using inv_ne_zero hB
  have hr := matrix_mul_range A B⁻¹ hiB
  have hc : (B-A).toLin'.range = T.ker := by
    rw [ht.ker_eq_range,←matrix_mul_range (B-A) B⁻¹ hiB]
    congr 1
    change ((B-A)*B⁻¹).toLin' = LinearMap.id-(A*B⁻¹).toLin'
    rw [sub_mul,Matrix.mul_nonsing_inv B (isUnit_iff_ne_zero.mpr hB),map_sub,Matrix.toLin'_one]
  rw [hc]
  simpa only [T,hr] using (matrix_projection_idempotent B⁻¹ A hi).isCompl
theorem center_complement_orthogonal (B A : Matrix n n K) (hB : B.det≠0)
    (hA : A.IsSymm) (hi : A*B⁻¹*A=A) :
    ∀ u : A.toLin'.range, ∀ w : (B-A).toLin'.range, B⁻¹.toBilin' u.val w.val=0 := by
  have hp : B⁻¹.toBilin'.comp A.toLin' (B-A).toLin'=0 := by
    rw [Matrix.toBilin'_comp,hA,mul_sub,hi,
      Matrix.mul_assoc A B⁻¹ B,Matrix.nonsing_inv_mul B (isUnit_iff_ne_zero.mpr hB),
      Matrix.mul_one,sub_self,map_zero]
  intro u w
  obtain ⟨x,hx⟩ := u.property
  obtain ⟨y,hy⟩ := w.property
  rw [←hx,←hy]
  exact congrArg (fun Q : LinearMap.BilinForm K (n → K) => Q x y) hp
end Complement
section Signs
variable {K n : Type*} [Field K] [Fintype K] [DecidableEq K] [Fintype n] [DecidableEq n]
theorem quadraticChar_inverse {a : K} (ha : a≠0) : quadraticChar K a⁻¹=quadraticChar K a := by
  have hm : quadraticChar K a * quadraticChar K a⁻¹=1 := by
    rw [←map_mul,mul_inv_cancel₀ ha,map_one]
  rcases quadraticChar_dichotomy ha with h | h <;> rw [h] at hm ⊢ <;> linarith
theorem center_complement_sign (B A : Matrix n n K) (hs : B.IsSymm) (hB : B.det≠0)
    (hA : A.IsSymm) (hi : A*B⁻¹*A=A) :
    quadraticChar K B.det =
      discriminantSign A.toBilin' (Matrix.isSymm_toBilin'_iff_isSymm.mpr hA) *
        discriminantSign (B-A).toBilin' (Matrix.isSymm_toBilin'_iff_isSymm.mpr (hs.sub hA)) := by
  have hsQ : B⁻¹.IsSymm := hs.inv
  have hnQ : B⁻¹.det≠0 := by simpa only [Matrix.det_nonsing_inv, Ring.inverse_eq_inv] using inv_ne_zero hB
  have hiC := center_complement_equation B A hB hi
  rw [center_discriminant B⁻¹ A hsQ hnQ hA hi,
    center_discriminant B⁻¹ (B-A) hsQ hnQ (hs.sub hA) hiC]
  rw [←discriminantSign_complements B⁻¹.toBilin'
    (Matrix.isSymm_toBilin'_iff_isSymm.mpr hsQ)
    (Matrix.nondegenerate_toBilin'_iff.mpr (Matrix.nondegenerate_iff_det_ne_zero.mpr hnQ))
    A.toLin'.range (B-A).toLin'.range (center_complement_ranges B A hB hi)
    (center_restriction_nondegenerate B⁻¹ A hsQ hnQ hA hi)
    (center_restriction_nondegenerate B⁻¹ (B-A) hsQ hnQ (hs.sub hA) hiC)
    (center_complement_orthogonal B A hB hA hi)]
  rw [discriminantSign_nondegenerate _ _
    (Matrix.nondegenerate_toBilin'_iff.mpr (Matrix.nondegenerate_iff_det_ne_zero.mpr hnQ))
    (Pi.basisFun K n)]
  change quadraticChar K B.det = quadraticChar K (B⁻¹.toBilin'.toMatrix').det
  rw [LinearMap.BilinForm.toMatrix'_toBilin',Matrix.det_nonsing_inv,Ring.inverse_eq_inv,quadraticChar_inverse hB]
end Signs
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section Split
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
def dualKerEquiv (φ : V →ₗ[K] K) (x : V) (hx : φ x=1) : (φ.ker × K) ≃ₗ[K] V where
  toFun p := p.1.val+p.2 • x
  invFun y := (⟨y-φ y • x, by simp [LinearMap.mem_ker,hx]⟩,φ y)
  left_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      simp only [map_add,map_smul,smul_eq_mul,hx,mul_one,
        show φ p.1.val=0 from p.1.property,zero_add,add_sub_cancel_right]
    · simp [hx]
  right_inv y := by simp
  map_add' p q := by simp only [Prod.fst_add,Prod.snd_add,Submodule.coe_add,add_smul]; abel
  map_smul' a p := by simp only [Prod.smul_fst,Prod.smul_snd,Submodule.coe_smul,
    smul_add,smul_smul,smul_eq_mul,RingHom.id_apply]
@[simp] theorem dualKerEquiv_apply (φ : V →ₗ[K] K) (x : V) (hx : φ x=1)
    (p : φ.ker × K) : dualKerEquiv φ x hx p = p.1.val + p.2 • x := rfl
def rankOneForm (φ : V →ₗ[K] K) : SymForm K V :=
  ⟨(LinearMap.mul K K).compl₁₂ φ φ, by constructor; intro x y; exact mul_comm _ _⟩
@[simp] theorem rankOneForm_apply (φ : V →ₗ[K] K) (x y : V) :
    (rankOneForm φ).val x y = φ x * φ y := rfl
theorem dualKer_finrank [FiniteDimensional K V] (φ : V →ₗ[K] K) (x : V) (hx : φ x=1) :
    finrank K φ.ker+1=finrank K V := by
  have h := (dualKerEquiv φ x hx).finrank_eq
  simpa only [Module.finrank_prod,Module.finrank_self] using h
end Split
section Signs
variable {K V : Type*} [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
noncomputable def dualKerBasis (φ : V →ₗ[K] K) (x : V) (hx : φ x=1)
    {ι : Type*} (b : Basis ι K φ.ker) : Basis (ι ⊕ PUnit.{1}) K V :=
  (b.prod (Basis.singleton PUnit.{1} K)).map (dualKerEquiv φ x hx)
omit [Fintype K] [DecidableEq K] [FiniteDimensional K V] in
@[simp] theorem dualKerBasis_inl (φ : V →ₗ[K] K) (x : V) (hx : φ x=1)
    {ι : Type*} (b : Basis ι K φ.ker) (i : ι) : dualKerBasis φ x hx b (.inl i) = (b i).val := by
  simp [dualKerBasis,Basis.prod_apply]
omit [Fintype K] [DecidableEq K] [FiniteDimensional K V] in
@[simp] theorem dualKerBasis_inr (φ : V →ₗ[K] K) (x : V) (hx : φ x=1)
    {ι : Type*} (b : Basis ι K φ.ker) (i : PUnit.{1}) : dualKerBasis φ x hx b (.inr i) = x := by
  simp [dualKerBasis,Basis.prod_apply]
omit [Fintype K] [DecidableEq K] in
theorem rankOne_shift_matrix (φ : V →ₗ[K] K) (x : V) (hx : φ x=1)
    (Q : SymForm K V) (a : K) :
    (Q+a • rankOneForm φ).val.toMatrix (dualKerBasis φ x hx (Module.finBasis K φ.ker)) =
      borderRaw ((symFormPull φ.ker.subtype Q).val.toMatrix (Module.finBasis K φ.ker))
        (fun i => Q.val (Module.finBasis K φ.ker i).val x) (Q.val x x+a) := by
  ext i j
  cases i with
  | inl i => cases j with
    | inl j =>
      simp only [LinearMap.BilinForm.toMatrix_apply,dualKerBasis_inl,borderRaw,
        Matrix.fromBlocks_apply₁₁]
      change Q.val _ _ + a * (φ (Module.finBasis K φ.ker i).val * φ (Module.finBasis K φ.ker j).val) = _
      rw [show φ (Module.finBasis K φ.ker i).val=0 from (Module.finBasis K φ.ker i).property]
      simp only [zero_mul,mul_zero,add_zero]; rfl
    | inr j =>
      simp only [LinearMap.BilinForm.toMatrix_apply,dualKerBasis_inl,dualKerBasis_inr,borderRaw,
        Matrix.fromBlocks_apply₁₂,Matrix.of_apply]
      change Q.val _ x+a*(φ (Module.finBasis K φ.ker i).val * φ x) = _
      rw [show φ (Module.finBasis K φ.ker i).val=0 from (Module.finBasis K φ.ker i).property]
      simp
  | inr i => cases j with
    | inl j =>
      simp only [LinearMap.BilinForm.toMatrix_apply,dualKerBasis_inl,dualKerBasis_inr,borderRaw,
        Matrix.fromBlocks_apply₂₁,Matrix.of_apply]
      change Q.val x _+a*(φ x * φ (Module.finBasis K φ.ker j).val) = _
      rw [show φ (Module.finBasis K φ.ker j).val=0 from (Module.finBasis K φ.ker j).property]
      simpa using Q.property.eq x (Module.finBasis K φ.ker j).val
    | inr j =>
      simp only [LinearMap.BilinForm.toMatrix_apply,dualKerBasis_inr,borderRaw,
        Matrix.fromBlocks_apply₂₂,Matrix.of_apply]
      change Q.val x x+a*(φ x * φ x) = Q.val x x+a
      rw [hx,one_mul,mul_one]
theorem rankOne_shift_mean (φ : V →ₗ[K] K) (x : V) (hx : φ x=1)
    (Q : SymForm K V) (hQ : (symFormPull φ.ker.subtype Q).val.Nondegenerate)
    (hK : ringChar K ≠ 2) {ξ : ℤ} (hξ : ξ=1 ∨ ξ = -1) :
    uniformMean (fun a : K => formSignIndicator ξ (Q+a • rankOneForm φ)) =
      (1-1/(Fintype.card K : ℝ))/2 := by
  let b := Module.finBasis K φ.ker
  let M : SymMatrix K (finrank K φ.ker) := ⟨(symFormPull φ.ker.subtype Q).val.toMatrix b,
    ((symFormPull φ.ker.subtype Q).val.isSymm_toMatrix_iff_isSymm b).mpr
      (symFormPull φ.ker.subtype Q).property⟩
  let z : Fin (finrank K φ.ker) → K := fun i => Q.val (b i).val x
  have hM : M.val.det ≠ 0 := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp hQ
  have he (a : K) : formSignIndicator ξ (Q+a • rankOneForm φ) =
      characterSignIndicator ξ (M.val.det * (a- (z ⬝ᵥ (M.val⁻¹.mulVec z)-Q.val x x))) := by
    rw [formSignIndicator_matrix (dualKerBasis φ x hx b) hξ,rankOne_shift_matrix]
    have hd : (borderRaw M.val z (Q.val x x+a)).det =
        (symmetricBorder M z (Q.val x x+a)).val.det := by
      symm; exact Matrix.det_submatrix_equiv_self _ _
    rw [show (symFormPull φ.ker.subtype Q).val.toMatrix (Module.finBasis K φ.ker)=M.val from rfl,
      show (fun i => Q.val (Module.finBasis K φ.ker i).val x)=z from rfl,hd,
      symmetricBorder_det M z _ hM]
    congr 2; ring
  rw [uniformMean_congr he,uniformMean_affine _ _ hM,uniformMean_characterSignIndicator hK hξ]
end Signs
end SidorenkoCounterexample
end
end OAI
namespace OAI
section
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section Means
variable {A B : Type*} [Fintype A] [Fintype B]
theorem uniformMean_swap (f : A → B → ℝ) :
    uniformMean (fun a => uniformMean (f a)) =
      uniformMean (fun b => uniformMean fun a => f a b) := by
  unfold uniformMean
  simp only [←Finset.sum_div]
  rw [Finset.sum_comm]
  ring
variable [AddGroup A]
theorem uniformMean_translate (f : A → ℝ) (t : A) :
    uniformMean (fun a => f (a+t)) = uniformMean f := uniformMean_equiv (Equiv.addRight t) f
theorem uniformMean_average_translate [Nonempty B] (f : A → ℝ) (t : B → A) :
    uniformMean (fun a => uniformMean fun b => f (a+t b)) = uniformMean f := by
  rw [uniformMean_swap]
  simp_rw [uniformMean_translate,uniformMean_const]
end Means
section ShiftError
variable {K U : Type*} [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup U] [Module K U] [FiniteDimensional K U]
theorem rankOne_shift_error (φ : U →ₗ[K] K) (x : U) (hx : φ x=1)
    (Q : SymForm K U) (hK : ringChar K ≠ 2) {ξ : ℤ} (hξ : ξ=1 ∨ ξ= -1) :
    |uniformMean (fun a : K => formSignIndicator ξ (Q+a • rankOneForm φ))-1/2| ≤
      formSingularIndicator (symFormPull φ.ker.subtype Q)+1/(Fintype.card K : ℝ) := by
  have hq : 0 < (Fintype.card K : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  by_cases hQ : (symFormPull φ.ker.subtype Q).val.Nondegenerate
  · rw [rankOne_shift_mean φ x hx Q hQ hK hξ]
    simp only [formSingularIndicator,hQ,ite_true,zero_add]
    apply abs_le.mpr
    constructor <;> nlinarith [one_div_pos.mpr hq]
  · have h0 := uniformMean_nonneg fun a : K => formSignIndicator_nonneg ξ (Q+a • rankOneForm φ)
    have h1 := uniformMean_bound fun a : K => formSignIndicator_le_one ξ (Q+a • rankOneForm φ)
    simp only [formSingularIndicator,hQ,ite_false]
    apply abs_le.mpr
    constructor <;> linarith [one_div_pos.mpr hq]
theorem centered_formSign_abs (ξ : ℤ) (Q : SymForm K U) :
    |formSignIndicator ξ Q-1/2| ≤ 1 := by
  have h0 := formSignIndicator_nonneg ξ Q
  have h1 := formSignIndicator_le_one ξ Q
  exact abs_le.mpr ⟨by linarith,by linarith⟩
end ShiftError
section Separate
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
theorem equal_dimension_separating_dual (U W : Submodule K V)
    (hd : finrank K U=finrank K W) (hne : U≠W) :
    ∃ (φ : V →ₗ[K] K) (x : U), φ x.val=1 ∧ φ.comp W.subtype=0 := by
  have hle : ¬ U ≤ W := by
    intro h
    exact hne (Submodule.eq_of_le_of_finrank_eq h hd)
  have hex : ∃ x : V, x ∈ U ∧ x ∉ W := by
    by_contra! hn
    exact hle hn
  obtain ⟨x,hx,hxW⟩ := hex
  obtain ⟨φ,hφ,hW⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hxW inferInstance
  refine ⟨φ,(φ x)⁻¹ • (⟨x,hx⟩ : U),?_,?_⟩
  · simp only [Submodule.coe_smul,map_smul,smul_eq_mul,inv_mul_cancel₀ hφ]
  · ext w
    have hz : φ w.val ∈ W.map φ := Submodule.mem_map_of_mem w.property
    rw [hW] at hz
    exact hz
end Separate
section Covariance
variable {K V : Type*} [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
omit [Fintype K] [DecidableEq K] [FiniteDimensional K V] in
theorem rankOne_restrict (φ : V →ₗ[K] K) (U : Submodule K V) :
    symFormPull U.subtype (rankOneForm φ) = rankOneForm (φ.comp U.subtype) := rfl
omit [Fintype K] [DecidableEq K] [FiniteDimensional K V] in
theorem rankOne_restrict_zero (φ : V →ₗ[K] K) (W : Submodule K V)
    (h : φ.comp W.subtype=0) : symFormPull W.subtype (rankOneForm φ)=0 := by
  rw [rankOne_restrict,h]
  apply Subtype.ext
  ext x y
  change (0 : K)*0=0
  ring
theorem restriction_covariance_bound (U W : Submodule K V)
    (hd : finrank K U=finrank K W) (hne : U≠W) (hK : ringChar K ≠ 2)
    {ξ ζ : ℤ} (hξ : ξ=1 ∨ ξ= -1) :
    |uniformMean (fun Q : SymForm K V =>
      (formSignIndicator ξ (symFormPull U.subtype Q)-1/2) *
      (formSignIndicator ζ (symFormPull W.subtype Q)-1/2))| ≤
      (finrank K U : ℝ)/(Fintype.card K : ℝ) := by
  obtain ⟨φ,x,hx,hW⟩ := equal_dimension_separating_dual U W hd hne
  let f : SymForm K V → ℝ := fun Q => formSignIndicator ξ (symFormPull U.subtype Q)-1/2
  let g : SymForm K V → ℝ := fun Q => formSignIndicator ζ (symFormPull W.subtype Q)-1/2
  let R := rankOneForm φ
  let φU := φ.comp U.subtype
  have hxU : φU x=1 := hx
  have hg (Q : SymForm K V) (a : K) : g (Q+a • R)=g Q := by
    dsimp [g]
    rw [map_add,map_smul,rankOne_restrict_zero φ W hW,smul_zero,add_zero]
  have he : uniformMean (fun Q => f Q*g Q) =
      uniformMean (fun Q => (uniformMean fun a : K => f (Q+a • R))*g Q) := by
    rw [←uniformMean_average_translate (fun Q => f Q*g Q) (fun a : K => a • R)]
    apply uniformMean_congr
    intro Q
    simp only [hg]
    have h := uniformMean_mul (g Q) (fun a : K => f (Q+a • R))
    simpa only [mul_comm] using h
  have hf (Q : SymForm K V) : |uniformMean fun a : K => f (Q+a • R)| ≤
      formSingularIndicator (symFormPull φU.ker.subtype (symFormPull U.subtype Q))+
        1/(Fintype.card K : ℝ) := by
    dsimp only [f]
    simp only [map_add,map_smul]
    rw [uniformMean_sub,uniformMean_const]
    exact rankOne_shift_error φU x hxU (symFormPull U.subtype Q) hK hξ
  have hgs (Q : SymForm K V) : |g Q| ≤ 1 := centered_formSign_abs ζ _
  change |uniformMean (fun Q => f Q*g Q)| ≤ _
  rw [he]
  calc
    _ ≤ uniformMean (fun Q => |(uniformMean fun a : K => f (Q+a • R))*g Q|) := abs_uniformMean_le _
    _ ≤ uniformMean (fun Q => formSingularIndicator
        (symFormPull φU.ker.subtype (symFormPull U.subtype Q))+1/(Fintype.card K : ℝ)) := by
      apply uniformMean_mono
      intro Q
      rw [abs_mul]
      calc
        _ ≤ |uniformMean fun a : K => f (Q+a • R)| * 1 :=
          mul_le_mul_of_nonneg_left (hgs Q) (abs_nonneg _)
        _ ≤ _ := by simpa only [mul_one] using hf Q
    _ = uniformMean (formSingularIndicator (K := K) (V := φU.ker))+
          1/(Fintype.card K : ℝ) := by
      rw [uniformMean_add,uniformMean_const]
      rw [uniformMean_restrict U.subtype U.subtype_injective
        (fun T => formSingularIndicator (symFormPull φU.ker.subtype T)),
        uniformMean_restrict φU.ker.subtype φU.ker.subtype_injective]
    _ ≤ (finrank K φU.ker : ℝ)/(Fintype.card K : ℝ)+1/(Fintype.card K : ℝ) :=
      add_le_add formSingularMean_bound le_rfl
    _ = _ := by
      rw [←add_div,←Nat.cast_one,←Nat.cast_add,dualKer_finrank φU x hxU]
end Covariance
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section Variance
variable {A I : Type*} [Fintype A] [Fintype I] [Nonempty I]
omit [Nonempty I] in
theorem uniformMean_square (f : I → ℝ) :
    (uniformMean f)^2 = uniformMean fun i => uniformMean fun j => f i*f j := by
  simp only [uniformMean_mul]
  have h := uniformMean_mul (uniformMean f) f
  simpa only [mul_comm,sq] using h.symm
theorem uniformMean_abs_sq_le (f : A → ℝ) :
    (uniformMean fun a => |f a|)^2 ≤ uniformMean fun a => (f a)^2 := by
  simpa only [uniformMean,Finset.card_univ,sq_abs] using
    (sum_div_card_sq_le_sum_sq_div_card (s := Finset.univ) (f := fun a => |f a|))
theorem family_variance_bound (f : I → A → ℝ) (ε : ℝ) (hε : 0≤ε)
    (hb : ∀ i a, |f i a| ≤ 1)
    (hc : ∀ i j, i≠j → |uniformMean fun a => f i a*f j a| ≤ ε) [Nonempty A] :
    uniformMean (fun a => (uniformMean fun i => f i a)^2) ≤ ε+1/(Fintype.card I : ℝ) := by
  classical
  have he : uniformMean (fun a => (uniformMean fun i => f i a)^2) =
      uniformMean fun i => uniformMean fun j => uniformMean fun a => f i a*f j a := by
    simp only [uniformMean_square]
    rw [uniformMean_swap]
    apply uniformMean_congr
    intro i
    exact uniformMean_swap _
  rw [he]
  calc
    _ ≤ uniformMean (fun i => uniformMean fun j => ε+(if i=j then 1 else 0)) := by
      apply uniformMean_mono
      intro i
      apply uniformMean_mono
      intro j
      by_cases hij : i=j
      · subst j
        simp only [ite_true]
        apply (uniformMean_bound (fun a => ?_)).trans (le_add_of_nonneg_left hε)
        calc
          f i a*f i a ≤ |f i a| * |f i a| := le_abs_self _ |>.trans_eq (abs_mul _ _)
          _ ≤ 1*1 := mul_le_mul (hb i a) (hb i a) (abs_nonneg _) (by norm_num)
          _ = 1 := one_mul _
      · simp only [if_neg hij,add_zero]
        exact (le_abs_self _).trans (hc i j hij)
    _ = _ := by
      simp only [uniformMean_add,uniformMean_const]
      have hi (i : I) : uniformMean (fun j : I => if i=j then (1 : ℝ) else 0) =
          1/(Fintype.card I : ℝ) := by simp [uniformMean]
      simp only [hi,uniformMean_const]
end Variance
section Restriction
variable {K V I : Type*} [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype I] [Nonempty I]
theorem restriction_family_variance (U : I → Submodule K V) (hinj : Function.Injective U)
    (r : ℕ) (hd : ∀ i, finrank K (U i)=r) (hK : ringChar K ≠ 2)
    {ξ : ℤ} (hξ : ξ=1 ∨ ξ= -1) :
    uniformMean (fun Q : SymForm K V =>
      (uniformMean (fun i => formSignIndicator ξ (symFormPull (U i).subtype Q))-1/2)^2) ≤
      (r : ℝ)/(Fintype.card K : ℝ)+1/(Fintype.card I : ℝ) := by
  have h := family_variance_bound
    (fun i Q => formSignIndicator ξ (symFormPull (U i).subtype Q)-1/2)
    ((r : ℝ)/(Fintype.card K : ℝ)) (by positivity)
    (fun i Q => centered_formSign_abs ξ _)
    (fun i j hij => by
      have hne : U i≠U j := fun h => hij (hinj h)
      simpa only [hd] using restriction_covariance_bound (U i) (U j)
        ((hd i).trans (hd j).symm) hne hK hξ (ζ := ξ))
  simpa only [uniformMean_sub,uniformMean_const] using h
theorem restriction_family_L1_sq (U : I → Submodule K V) (hinj : Function.Injective U)
    (r : ℕ) (hd : ∀ i, finrank K (U i)=r) (hK : ringChar K ≠ 2)
    {ξ : ℤ} (hξ : ξ=1 ∨ ξ= -1) :
    (uniformMean (fun Q : SymForm K V =>
      |uniformMean (fun i => formSignIndicator ξ (symFormPull (U i).subtype Q))-1/2|))^2 ≤
      (r : ℝ)/(Fintype.card K : ℝ)+1/(Fintype.card I : ℝ) :=
  (uniformMean_abs_sq_le _).trans (restriction_family_variance U hinj r hd hK hξ)
end Restriction
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module
section AlternatingTwo
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
abbrev AltForm := {B : LinearMap.BilinForm K V // B.IsAlt}
instance altForm_finite [Finite K] [Finite V] : Finite (AltForm (K := K) (V := V)) :=
  Finite.of_injective (fun B : AltForm (K := K) (V := V) => fun x y => B.val x y) (by
    intro B C h
    apply Subtype.ext
    ext x y
    exact congrFun (congrFun h x) y)
def altFormToMap (B : AltForm (K := K) (V := V)) : V [⋀^Fin 2]→ₗ[K] K where
  toFun v := B.val (v 0) (v 1)
  map_update_add' v i x y := by
    fin_cases i <;> simp
  map_update_smul' v i c x := by
    fin_cases i <;> simp
  map_eq_zero_of_eq' v i j hij hne := by
    fin_cases i <;> fin_cases j <;> simp_all
    · exact B.property _
    · exact B.property _
omit [AddCommGroup V] in
private theorem update_vec_zero (x y z : V) : Function.update ![x,y] (0 : Fin 2) z = ![z,y] := by
  ext i
  fin_cases i <;> simp
omit [AddCommGroup V] in
private theorem update_vec_one (x y z : V) : Function.update ![x,y] (1 : Fin 2) z = ![x,z] := by
  ext i
  fin_cases i <;> simp
def mapToAltForm (f : V [⋀^Fin 2]→ₗ[K] K) : AltForm (K := K) (V := V) :=
  ⟨{ toFun := fun x => {
       toFun := fun y => f ![x,y]
       map_add' := fun y z => by
         simpa only [update_vec_zero, update_vec_one, smul_eq_mul, RingHom.id_apply] using f.map_update_add ![x,(0:V)] (1 : Fin 2) y z
       map_smul' := fun c y => by
         simpa only [update_vec_zero, update_vec_one, smul_eq_mul, RingHom.id_apply] using f.map_update_smul ![x,(0:V)] (1 : Fin 2) c y }
     map_add' := fun x y => by
       ext z
       change f ![x+y,z] = f ![x,z]+f ![y,z]
       simpa only [update_vec_zero, update_vec_one, smul_eq_mul, RingHom.id_apply] using f.map_update_add ![(0:V),z] (0 : Fin 2) x y
     map_smul' := fun c x => by
       ext z
       change f ![c • x,z] = c * f ![x,z]
       simpa only [update_vec_zero, update_vec_one, smul_eq_mul, RingHom.id_apply] using f.map_update_smul ![(0:V),z] (0 : Fin 2) c x },
    fun x => f.map_eq_zero_of_eq ![x,x] (by simp : (![x,x] : Fin 2 → V) 0 = ![x,x] 1) (by decide : (0 : Fin 2) ≠ 1)⟩
def altFormMapEquiv : AltForm (K := K) (V := V) ≃ (V [⋀^Fin 2]→ₗ[K] K) where
  toFun := altFormToMap
  invFun := mapToAltForm
  left_inv B := by apply Subtype.ext; ext x y; rfl
  right_inv f := by
    ext v
    change f ![v 0,v 1] = f v
    congr 1
    ext i
    fin_cases i <;> rfl
variable [FiniteDimensional K V] [Fintype K]
theorem altForm_card : Nat.card (AltForm (K := K) (V := V)) =
    Fintype.card K ^ (finrank K V).choose 2 := by
  rw [Nat.card_congr (altFormMapEquiv (K := K) (V := V)),
    Nat.card_congr (exteriorPower.alternatingMapLinearEquiv (R := K) (M := V) (N := K) (n := 2)).toEquiv]
  rw [Module.natCard_eq_pow_finrank (K := K), Subspace.dual_finrank_eq, exteriorPower.finrank_eq,
    Nat.card_eq_fintype_card]
end AlternatingTwo
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module
section OrthogonalCharts
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
def canonicalOrthogonal : LinearMap.BilinForm K (V × Module.Dual K V) where
  toFun p := {
    toFun := fun q => q.2 p.1 + p.2 q.1
    map_add' := by intros; simp; ring
    map_smul' := by intros; simp; ring }
  map_add' := by
    intro p q
    apply LinearMap.ext
    intro z
    change z.2 (p.1+q.1) + (p.2+q.2) z.1 =
      (z.2 p.1 + p.2 z.1) + (z.2 q.1 + q.2 z.1)
    simp
    ring
  map_smul' := by
    intro a p
    apply LinearMap.ext
    intro z
    change z.2 (a • p.1) + (a • p.2) z.1 = a * (z.2 p.1+p.2 z.1)
    simp
    ring
@[simp] theorem canonicalOrthogonal_apply (p q : V × Module.Dual K V) :
    canonicalOrthogonal p q = q.2 p.1 + p.2 q.1 := rfl
 theorem canonicalOrthogonal_symm : (canonicalOrthogonal (K := K) (V := V)).IsSymm := by
  constructor
  intro p q
  simp only [canonicalOrthogonal_apply, add_comm]
 theorem canonicalOrthogonal_nondegenerate :
    (canonicalOrthogonal (K := K) (V := V)).Nondegenerate := by
  have hleft : ∀ p : V × Module.Dual K V,
      (∀ q, canonicalOrthogonal p q = 0) → p = 0 := by
    rintro ⟨x,f⟩ hp
    have hx : x = 0 := (Module.forall_dual_apply_eq_zero_iff K x).mp (fun g => by
      simpa using hp (0,g))
    have hf : f = 0 := by
      ext y
      simpa using hp (y,0)
    simp [hx,hf]
  refine ⟨hleft, ?_⟩
  intros p hp
  apply hleft
  intro q
  exact canonicalOrthogonal_symm.isRefl _ _ (hp q)
variable [FiniteDimensional K V]
abbrev MaxOrthogonal := {L : Submodule K (V × Module.Dual K V) //
  canonicalOrthogonal.orthogonal L = L}
 theorem maxOrthogonal_finrank (L : MaxOrthogonal (K := K) (V := V)) :
    finrank K L.val = finrank K V := by
  have h := LinearMap.BilinForm.finrank_orthogonal canonicalOrthogonal_nondegenerate L.val
  rw [L.property, Module.finrank_prod, Subspace.dual_finrank_eq] at h
  have hle := Submodule.finrank_le L.val
  rw [Module.finrank_prod, Subspace.dual_finrank_eq] at hle
  omega
omit [FiniteDimensional K V] in
 theorem formGraph_orthogonal_isotropic (U : Submodule K V) (B : AltForm (K := K) (V := U)) :
    formGraph U B.val ≤ canonicalOrthogonal.orthogonal (formGraph U B.val) := by
  rintro p ⟨u,hu,hf⟩ q ⟨v,hv,hg⟩
  change p.2 q.1 + q.2 p.1 = 0
  rw [←hu,←hv]
  have hf' := congrArg (fun l : Module.Dual K U => l v) hf
  have hg' := congrArg (fun l : Module.Dual K U => l u) hg
  change p.2 v.val = B.val u v at hf'
  change q.2 u.val = B.val v u at hg'
  rw [hf',hg',← B.property.neg_eq u v]
  exact add_neg_cancel _
noncomputable def graphMaxOrthogonal (U : Submodule K V) (B : AltForm (K := K) (V := U)) :
    MaxOrthogonal (K := K) (V := V) :=
  ⟨formGraph U B.val, by
    apply (Submodule.eq_of_le_of_finrank_eq (formGraph_orthogonal_isotropic U B) _).symm
    rw [formGraph_finrank, LinearMap.BilinForm.finrank_orthogonal canonicalOrthogonal_nondegenerate,
      Module.finrank_prod, Subspace.dual_finrank_eq, formGraph_finrank, Nat.add_sub_cancel_left]⟩
 theorem graphMaxOrthogonal_form_injective (U : Submodule K V) :
    Function.Injective (graphMaxOrthogonal (K := K) U) := by
  intro B C h
  apply Subtype.ext
  apply LinearMap.ext
  intro u
  obtain ⟨f,hf⟩ := Subspace.dualRestrict_surjective (W := U) (B.val u)
  have hp : (u.val,f) ∈ formGraph U B.val := ⟨u,rfl,hf⟩
  have he : formGraph U B.val = formGraph U C.val := congrArg Subtype.val h
  rw [he] at hp
  obtain ⟨v,hv,hg⟩ := hp
  have hv' : v = u := Subtype.ext hv
  exact hf.symm.trans (hv' ▸ hg)
omit [FiniteDimensional K V] in
 theorem maxOrthogonal_pairing_zero (L : MaxOrthogonal (K := K) (V := V))
    {p q : V × Module.Dual K V} (hp : p ∈ L.val) (hq : q ∈ L.val) :
    canonicalOrthogonal p q = 0 := by
  have hq' : q ∈ canonicalOrthogonal.orthogonal L.val := L.property.symm ▸ hq
  exact hq' p hp
 theorem graphMaxOrthogonal_surjective (hK : ringChar K ≠ 2) :
    Function.Surjective (fun S : Σ U : Submodule K V, AltForm (K := K) (V := U) => graphMaxOrthogonal S.1 S.2) := by
  intro L
  let U := L.val.map (LinearMap.fst K V (Module.Dual K V))
  let p : L.val →ₗ[K] U := {
    toFun := fun x => ⟨x.val.1, ⟨x.val,x.property,rfl⟩⟩
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  have hp : Function.Surjective p := by
    rintro ⟨x,y,hy,hyx⟩
    exact ⟨⟨y,hy⟩,Subtype.ext hyx⟩
  obtain ⟨s,hs⟩ := p.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hp)
  have hsfst (u : U) : (s u).val.1 = u.val := congrArg Subtype.val (LinearMap.congr_fun hs u)
  let C : LinearMap.BilinForm K U :=
    (((LinearMap.snd K V (Module.Dual K V)).comp L.val.subtype).comp s).compl₂ U.subtype
  have hC : C.IsAlt := by
    intro u
    have h := maxOrthogonal_pairing_zero L (s u).property (s u).property
    change (s u).val.2 (s u).val.1 + (s u).val.2 (s u).val.1 = 0 at h
    rw [hsfst] at h
    change C u u + C u u = 0 at h
    exact (mul_eq_zero.mp ((two_mul (C u u)).trans h)).resolve_left (Ring.two_ne_zero hK)
  refine ⟨⟨U,⟨C,hC⟩⟩, ?_⟩
  apply Subtype.ext
  symm
  apply Submodule.eq_of_le_of_finrank_eq
  · intro x hx
    let u : U := ⟨x.1,⟨x,hx,rfl⟩⟩
    refine ⟨u,rfl,?_⟩
    apply LinearMap.ext
    intro y
    have h := maxOrthogonal_pairing_zero L hx (s y).property
    change (s y).val.2 x.1 + x.2 (s y).val.1 = 0 at h
    rw [hsfst] at h
    change x.2 y.val = (s u).val.2 y.val
    have hh : x.2 y.val = -(s y).val.2 u.val := (eq_neg_iff_add_eq_zero.mpr (by simpa only [add_comm] using h))
    exact hh.trans (hC.neg_eq y u)
  · exact (maxOrthogonal_finrank L).trans (formGraph_finrank U C).symm
noncomputable def maxOrthogonalGraphEquiv (hK : ringChar K ≠ 2) :
    (Σ U : Submodule K V, AltForm (K := K) (V := U)) ≃ MaxOrthogonal (K := K) (V := V) :=
  Equiv.ofBijective (fun S => graphMaxOrthogonal S.1 S.2) ⟨by
    rintro ⟨U,B⟩ ⟨W,C⟩ he
    have h : U = W := by
      rw [← formGraph_fst_range U B.val, ← formGraph_fst_range W C.val]
      exact congrArg (fun L : MaxOrthogonal (K := K) (V := V) =>
        L.val.map (LinearMap.fst K V (Module.Dual K V))) he
    cases h
    congr 1
    exact graphMaxOrthogonal_form_injective U he,
    graphMaxOrthogonal_surjective hK⟩
 theorem maxOrthogonal_card_sum [Fintype K] [Finite V] (hK : ringChar K ≠ 2) :
    letI := Fintype.ofFinite (Submodule K V)
    Nat.card (MaxOrthogonal (K := K) (V := V)) =
      ∑ U : Submodule K V, (Fintype.card K)^((finrank K U).choose 2) := by
  classical
  let := Fintype.ofFinite (Submodule K V)
  rw [← Nat.card_congr (maxOrthogonalGraphEquiv (K := K) (V := V) hK), Nat.card_sigma]
  simp only [altForm_card]
end OrthogonalCharts
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module
section SplitSign
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
 theorem canonicalOrthogonal_matrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) :
    canonicalOrthogonal.toMatrix (b.prod b.dualBasis) =
      Matrix.fromBlocks (0 : Matrix ι ι K) 1 1 0 := by
  ext i j
  cases i <;> cases j <;>
    simp [LinearMap.BilinForm.toMatrix_apply, Basis.prod_apply, Matrix.one_apply,
      Finsupp.single_apply, eq_comm]
 theorem hyperbolic_block_det {ι : Type*} [Fintype ι] [DecidableEq ι] :
    (Matrix.fromBlocks (0 : Matrix ι ι K) (1 : Matrix ι ι K) (1 : Matrix ι ι K) 0).det = (-1 : K) ^ Fintype.card ι := by
  have hmul : Matrix.fromBlocks (0 : Matrix ι ι K) (1 : Matrix ι ι K) (1 : Matrix ι ι K) 0 *
      Matrix.fromBlocks (1 : Matrix ι ι K) (1 : Matrix ι ι K) (0 : Matrix ι ι K) 1 =
      Matrix.fromBlocks (0 : Matrix ι ι K) (1 : Matrix ι ι K) (1 : Matrix ι ι K) 1 := by
    rw [Matrix.fromBlocks_multiply]
    simp
  have h := congrArg Matrix.det hmul
  rw [Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul,
    mul_one, Matrix.det_fromBlocks_one₂₂] at h
  simpa only [Matrix.one_mul, zero_sub, Matrix.det_neg, Matrix.det_one, mul_one] using h
variable [FiniteDimensional K V] [Fintype K] [DecidableEq K]
 theorem canonicalOrthogonal_sign :
    discriminantSign (canonicalOrthogonal (K := K) (V := V)) canonicalOrthogonal_symm =
      quadraticChar K ((-1 : K) ^ finrank K V) := by
  rw [discriminantSign_nondegenerate _ _ canonicalOrthogonal_nondegenerate
    ((Module.finBasis K V).prod (Module.finBasis K V).dualBasis),
    canonicalOrthogonal_matrix, hyperbolic_block_det, Fintype.card_fin]
 theorem split_form_equivalent {E : Type*} [AddCommGroup E] [Module K E]
    [FiniteDimensional K E] (B : LinearMap.BilinForm K E)
    (hs : B.IsSymm) (hB : B.Nondegenerate) (hK : ringChar K ≠ 2)
    (r : ℕ) (hd : finrank K E = 2*r)
    (hc : discriminantSign B hs = quadraticChar K ((-1 : K)^r)) :
    BilinEquivalent B (canonicalOrthogonal (K := K) (V := Fin r → K)) := by
  apply symmetric_equivalent_of_dim_sign B _ hs canonicalOrthogonal_symm hB
    canonicalOrthogonal_nondegenerate hK
  · simpa only [Module.finrank_prod, Subspace.dual_finrank_eq, Module.finrank_pi,
      Fintype.card_fin, two_mul] using hd
  · simpa only [canonicalOrthogonal_sign, Module.finrank_pi, Fintype.card_fin] using hc
 theorem split_form_card {E : Type*} [AddCommGroup E] [Module K E]
    [FiniteDimensional K E] (B : LinearMap.BilinForm K E)
    (hs : B.IsSymm) (hB : B.Nondegenerate) (hK : ringChar K ≠ 2)
    (r : ℕ) (hd : finrank K E = 2*r)
    (hc : discriminantSign B hs = quadraticChar K ((-1 : K)^r)) :
    Nat.card (SymplecticLagrangian B) =
      Nat.card (MaxOrthogonal (K := K) (V := Fin r → K)) := by
  obtain ⟨e,he⟩ := split_form_equivalent B hs hB hK r hd hc
  exact Nat.card_congr (symplecticLagrangianEquiv _ _ e he)
end SplitSign
end SidorenkoCounterexample
end
end OAI
namespace OAI
section
namespace SidorenkoCounterexample
open scoped BigOperators
open Module Filter
noncomputable def grassmannFactor (D k : ℕ) (q : ℝ) : ℝ :=
  ∏ i : Fin k, (1 - 1 / q^(D-i.val)) / (1 - 1 / q^(k-i.val))
theorem grassmann_single_factor (D k i : ℕ) (hik : i ≤ k) (hkD : k ≤ D)
    (q : ℝ) (hq : q ≠ 0) :
    (q^D - q^i)/(q^k-q^i) = q^(D-k) *
      ((1 - 1/q^(D-i)) / (1 - 1/q^(k-i))) := by
  have hf (n : ℕ) (hi : i ≤ n) : q^n-q^i=q^n*(1-1/q^(n-i)) := by
    rw [mul_sub, mul_one, mul_one_div, div_eq_mul_inv,
      ← pow_sub₀ q hq (Nat.sub_le n i), Nat.sub_sub_self hi]
  rw [hf D (hik.trans hkD), hf k hik, mul_div_mul_comm,
    div_eq_mul_inv (q^D), ← pow_sub₀ q hq hkD]
theorem subspace_count_normalized {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [Fintype K] [Finite V] (k : ℕ) (hk : k ≤ finrank K V) :
    (Nat.card (DimSubspace K V k) : ℝ) =
      (Fintype.card K : ℝ)^(k*(finrank K V-k)) *
        grassmannFactor (finrank K V) k (Fintype.card K) := by
  rw [subspace_count_real k hk]
  have hf (i : Fin k) := grassmann_single_factor (finrank K V) k i.val i.isLt.le hk
    (Fintype.card K : ℝ) (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  simp_rw [hf]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ← pow_mul, Nat.mul_comm (finrank K V-k) k]
  rfl
theorem inverse_power_tendsto_zero (n : ℕ) (hn : 0<n) :
    Tendsto (fun q : ℝ => 1/q^n) atTop (nhds 0) := by
  simpa only [one_div, inv_pow, zero_pow (Nat.ne_zero_of_lt hn)] using
    (tendsto_inv_atTop_zero (𝕜 := ℝ)).pow n
theorem grassmannFactor_tendsto (D k : ℕ) (hk : k ≤ D) :
    Tendsto (grassmannFactor D k) atTop (nhds 1) := by
  unfold grassmannFactor
  have h (i : Fin k) : Tendsto (fun q : ℝ =>
      (1 - 1/q^(D-i.val))/(1-1/q^(k-i.val))) atTop (nhds 1) := by
    have hD := inverse_power_tendsto_zero (D-i.val) (by omega)
    have hk' := inverse_power_tendsto_zero (k-i.val) (by omega)
    have ha : Tendsto (fun q : ℝ => 1-1/q^(D-i.val)) atTop (nhds (1-0:ℝ)) :=
      tendsto_const_nhds.sub hD
    have hb : Tendsto (fun q : ℝ => 1-1/q^(k-i.val)) atTop (nhds (1-0:ℝ)) :=
      tendsto_const_nhds.sub hk'
    have hc : Tendsto (fun q : ℝ =>
        (1-1/q^(D-i.val))/(1-1/q^(k-i.val))) atTop (nhds ((1-0:ℝ)/(1-0))) :=
      (ha.div hb (by norm_num)).congr (fun _ => rfl)
    simpa only [sub_zero, div_self (one_ne_zero : (1:ℝ) ≠ 0)] using hc
  simpa using tendsto_finsetProd Finset.univ (fun i _ => h i)
theorem triangular_nat_add (r k : ℕ) :
    (r+k+1).choose 2 = (r+1).choose 2 + (k+1).choose 2 + r*k := by
  have h : (((r+k+1).choose 2 : ℕ) : ℚ) =
      ((r+1).choose 2 : ℚ) + ((k+1).choose 2 : ℚ) + (r:ℚ)*k := by
    simp only [Nat.cast_choose_two, Nat.cast_add, Nat.cast_one]
    ring
  exact_mod_cast h
theorem layerMass_normalized {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (D r : ℕ) (hrD : r ≤ D) {ξ : ℤ} (hξ : ξ = 1 ∨ ξ = -1) :
    layerMass K D r ξ * (Fintype.card K : ℝ)^((D-r+1).choose 2) =
      grassmannFactor D (D-r) (Fintype.card K) * symmetricSignProb (K := K) r ξ := by
  rw [layerMass_exact D r hrD hξ, subspace_count_normalized _ (by simp)]
  simp only [Module.finrank_pi, Fintype.card_fin, Nat.sub_sub_self hrD]
  have he : (D+1).choose 2 = (r+1).choose 2 + (D-r+1).choose 2 + (D-r)*r := by
    simpa only [Nat.add_sub_of_le hrD, Nat.mul_comm r (D-r)] using triangular_nat_add r (D-r)
  rw [he, pow_add, pow_add]
  have hq : (Fintype.card K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp
theorem primeInfinity_real_tendsto :
    Tendsto (fun q : OddPrime => (q.val : ℝ)) primeInfinity atTop :=
  tendsto_natCast_atTop_atTop.comp Filter.tendsto_comap
theorem symmetricSignProb_tendsto (r : ℕ) (hr : 0<r) {ξ : ℤ} (hξ : ξ=1 ∨ ξ= -1) :
    Tendsto (fun q : OddPrime => symmetricSignProb (K := ZMod q.val) r ξ)
      primeInfinity (nhds (1/2)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun q : OddPrime => (r:ℝ)/q.val) primeInfinity (nhds 0) := by
    simpa only [div_eq_mul_inv,mul_zero, Function.comp_def] using
      ((tendsto_inv_atTop_zero (𝕜 := ℝ)).comp primeInfinity_real_tendsto).const_mul (r:ℝ)
  apply squeeze_zero (fun _ => norm_nonneg _) _ hlim
  intro q
  simpa only [Real.norm_eq_abs,ZMod.card] using
    symmetricSignProb_error (K := ZMod q.val) r hr
      (by simpa only [ZMod.ringChar_zmod_n] using q.property.2) hξ
theorem layerMass_tendsto (D r : ℕ) (hr : 0<r) (hrD : r ≤ D)
    {ξ : ℤ} (hξ : ξ=1 ∨ ξ= -1) :
    Tendsto (fun q : OddPrime => layerMass (ZMod q.val) D r ξ *
      (q.val:ℝ)^((D-r+1).choose 2)) primeInfinity (nhds (1/2)) := by
  have he (q : OddPrime) := layerMass_normalized (K := ZMod q.val) D r hrD hξ
  simp only [ZMod.card] at he
  simp_rw [he]
  simpa only [one_mul, Function.comp_def] using
    ((grassmannFactor_tendsto D (D-r) (Nat.sub_le ..)).comp
      primeInfinity_real_tendsto).mul (symmetricSignProb_tendsto r hr hξ)
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module Filter Topology
open scoped BigOperators
section CountDimension
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype K] [Finite V]
theorem maxOrthogonal_card_by_dimension (hK : ringChar K ≠ 2) :
    Nat.card (MaxOrthogonal (K := K) (V := V)) =
      ∑ k : Fin (finrank K V+1), Nat.card (DimSubspace K V k.val) *
        Fintype.card K ^ k.val.choose 2 := by
  classical
  let := Fintype.ofFinite (Submodule K V)
  let d : Submodule K V → Fin (finrank K V+1) :=
    fun U => ⟨finrank K U,Nat.lt_succ_of_le (Submodule.finrank_le U)⟩
  rw [maxOrthogonal_card_sum hK,← Fintype.sum_fiberwise d]
  apply Finset.sum_congr rfl
  intro k _
  have hc : Nat.card {U : Submodule K V // d U = k} = Nat.card (DimSubspace K V k.val) :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun U => by
      change (⟨finrank K U,_⟩ : Fin _)=k ↔ finrank K U=k.val
      exact Fin.ext_iff))
  have he (U : {U : Submodule K V // d U = k}) : finrank K U.val = k.val :=
    congrArg Fin.val U.property
  simp only [he,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,←Nat.card_eq_fintype_card,hc,Nat.cast_id]
end CountDimension
noncomputable def orthogonalFactor (r : ℕ) (q : ℝ) : ℝ :=
  ∑ k : Fin (r+1), grassmannFactor r k.val q / q^((r-k.val).choose 2)
theorem choose_two_add (a b : ℕ) : (a+b).choose 2 = a.choose 2+b.choose 2+a*b := by
  have h : (((a+b).choose 2 : ℕ) : ℚ) = (a.choose 2 : ℚ)+(b.choose 2 : ℚ)+(a:ℚ)*b := by
    simp only [Nat.cast_choose_two, Nat.cast_add]
    ring
  exact_mod_cast h
theorem maxOrthogonal_normalized {K : Type*} [Field K] [Fintype K]
    (hK : ringChar K ≠ 2) (r : ℕ) :
    (Nat.card (MaxOrthogonal (K := K) (V := Fin r → K)) : ℝ) /
      (Fintype.card K : ℝ)^r.choose 2 = orthogonalFactor r (Fintype.card K) := by
  classical
  rw [maxOrthogonal_card_by_dimension hK,Module.finrank_fin_fun]
  simp only [Nat.cast_sum,Nat.cast_mul,Nat.cast_pow]
  rw [Finset.sum_div]
  unfold orthogonalFactor
  apply Finset.sum_congr rfl
  intro k _
  rw [subspace_count_normalized k.val (by simp; omega)]
  simp only [Module.finrank_fin_fun]
  have hr : (k.val+(r-k.val)).choose 2 = r.choose 2 := by rw [Nat.add_sub_of_le (by omega)]
  have he : r.choose 2 = k.val.choose 2 + (r-k.val).choose 2 + k.val*(r-k.val) := by
    rw [←hr,choose_two_add]
  rw [he,pow_add,pow_add]
  have hq : (Fintype.card K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp
theorem orthogonalFactor_tendsto (r : ℕ) (hr : 0<r) :
    Tendsto (orthogonalFactor r) atTop (nhds 2) := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  have hrest (k : Fin n) : Tendsto (fun q : ℝ =>
      grassmannFactor (n+1) k.val q / q^((n+1-k.val).choose 2)) atTop (nhds 0) := by
    have hp : 0 < (n+1-k.val).choose 2 := Nat.choose_pos (by omega)
    have h := (grassmannFactor_tendsto (n+1) k.val (by omega)).mul
      (inverse_power_tendsto_zero _ hp)
    simpa only [one_mul,div_eq_mul_inv,one_div] using h
  have hsum := tendsto_finsetSum Finset.univ (fun k (_ : k ∈ Finset.univ) => hrest k)
  have hn : Tendsto (fun q : ℝ => grassmannFactor (n+1) n q /
      q^((n+1-n).choose 2)) atTop (nhds 1) := by
    simpa using grassmannFactor_tendsto (n+1) n (Nat.le_succ n)
  have hn1 : Tendsto (fun q : ℝ => grassmannFactor (n+1) (n+1) q /
      q^((n+1-(n+1)).choose 2)) atTop (nhds 1) := by
    simpa using grassmannFactor_tendsto (n+1) (n+1) le_rfl
  have h := (hsum.add hn).add hn1
  simp only [Finset.sum_const_zero,zero_add] at h
  norm_num only [one_add_one_eq_two] at h
  convert h using 1
  funext q
  unfold orthogonalFactor
  rw [Fin.sum_univ_castSucc,Fin.sum_univ_castSucc]
  rfl
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module LinearMap
open scoped Matrix BigOperators
section PairSigns
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] {D r : ℕ}
theorem signed_pair_compatibility (hd : D=2*r) (A B : SymMatrix K D)
    (hB : B.val.det≠0) (ha : A.val.rank=r) (hb : (A-B).val.rank=r) :
    quadraticChar K B.val.det = quadraticChar K ((-1 : K)^r) *
      matrixSign K D A * matrixSign K D (A-B) := by
  have hba : (B.val-A.val).rank=r := by
    have he : B.val-A.val= -(A-B).val := by simp
    rw [he,matrix_rank_neg,hb]
  have hi := (half_rank_projection r (by simpa using hd) A.val B.val hB ha).mp hba
  have hs := center_complement_sign B.val A.val B.property hB A.property hi
  have he : (⟨B.val-A.val,B.property.sub A.property⟩ : SymMatrix K D)= -(A-B) := by
    apply Subtype.ext; simp
  change quadraticChar K B.val.det = matrixSign K D A *
    matrixSign K D ⟨B.val-A.val,B.property.sub A.property⟩ at hs
  rw [he,matrixSign_neg,hb] at hs
  rw [hs]; ring
theorem signed_second_iff (hd : D=2*r) (A B : SymMatrix K D)
    (hB : B.val.det≠0) (ha : A.val.rank=r) {ξ ζ : ℤ} (hx : matrixSign K D A=ξ)
    (hm : quadraticChar K B.val.det=quadraticChar K ((-1 : K)^r)*ξ*ζ) :
    ((A-B).val.rank=r ∧ matrixSign K D (A-B)=ζ) ↔ A.val*B.val⁻¹*A.val=A.val := by
  have hr : (A-B).val.rank=r ↔ A.val*B.val⁻¹*A.val=A.val := by
    rw [←half_rank_projection r (by simpa using hd) A.val B.val hB ha]
    have he : (A-B).val= -(B.val-A.val) := by simp
    rw [he,matrix_rank_neg]
  constructor
  · exact fun h => hr.mp h.1
  · intro hi
    have hb := hr.mpr hi
    refine ⟨hb,?_⟩
    have hp := signed_pair_compatibility hd A B hB ha hb
    rw [hx,hm] at hp
    have hc : quadraticChar K ((-1 : K)^r)≠0 := by
      exact mt quadraticChar_eq_zero_iff.mp (pow_ne_zero r (neg_ne_zero.mpr (one_ne_zero : (1 : K)≠0)))
    have hn : ξ≠0 := by rw [←hx]; exact discriminantSign_ne_zero _ _
    exact mul_left_cancel₀ (mul_ne_zero hc hn) hp.symm
end PairSigns
section Equiv
variable {K n : Type*} [Field K] [Fintype K] [DecidableEq K] [Fintype n] [DecidableEq n]
omit [Fintype K] [DecidableEq K] in
theorem centerSubspaceEquiv_rank (Q : Matrix n n K) (hQ : Q.IsSymm) (hdet : Q.det≠0)
    (A : CenterProjection Q) : finrank K (centerSubspaceEquiv Q hQ hdet A).val = A.val.rank := by
  rw [centerSubspaceEquiv_val]
  rfl
theorem centerSubspaceEquiv_sign (Q : Matrix n n K) (hQ : Q.IsSymm) (hdet : Q.det≠0)
    (A : CenterProjection Q) :
    discriminantSign A.val.toBilin' (Matrix.isSymm_toBilin'_iff_isSymm.mpr A.property.1) =
    discriminantSign (Q.toBilin'.restrict (centerSubspaceEquiv Q hQ hdet A).val)
      ((Matrix.isSymm_toBilin'_iff_isSymm.mpr hQ).restrict _) := by
  rw [centerSubspaceEquiv_val]
  exact center_discriminant Q A.val hQ hdet A.property.1 A.property.2
end Equiv
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module LinearMap
open scoped Matrix BigOperators
section SignedProjector
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] {D r : ℕ}
def SignedProjector (Q : Matrix (Fin D) (Fin D) K) (r : ℕ) (ξ : ℤ) :=
  {A : CenterProjection Q // A.val.rank=r ∧
    discriminantSign A.val.toBilin' (Matrix.isSymm_toBilin'_iff_isSymm.mpr A.property.1)=ξ}
noncomputable def pairSignedCenterEquiv (hd : D=2*r) (B : SymMatrix K D)
    (hB : B.val.det≠0) (ξ ζ : ℤ)
    (hm : quadraticChar K B.val.det=quadraticChar K ((-1 : K)^r)*ξ*ζ) :
    {A : SymMatrix K D // A ∈ signedLayer K D r ξ ∧ A-B ∈ signedLayer K D r ζ} ≃
      SignedProjector B.val⁻¹ r ξ where
  toFun A :=
    ⟨⟨A.val.val,A.val.property,
      (signed_second_iff hd A.val B hB ((mem_signedLayer ..).mp A.property.1).1
        ((mem_signedLayer ..).mp A.property.1).2 hm).mp
        ((mem_signedLayer ..).mp A.property.2)⟩,
      ((mem_signedLayer ..).mp A.property.1).1,((mem_signedLayer ..).mp A.property.1).2⟩
  invFun A :=
    ⟨⟨A.val.val,A.val.property.1⟩,
      (mem_signedLayer ..).mpr A.property,
      (mem_signedLayer ..).mpr ((signed_second_iff hd ⟨A.val.val,A.val.property.1⟩ B hB
        A.property.1 A.property.2 hm).mpr A.val.property.2)⟩
  left_inv A := by apply Subtype.ext; rfl
  right_inv A := by apply Subtype.ext; rfl
noncomputable def signedProjectorSubspaceEquiv (Q : Matrix (Fin D) (Fin D) K)
    (hQ : Q.IsSymm) (hdet : Q.det≠0) (r : ℕ) (ξ : ℤ) :
    SignedProjector Q r ξ ≃
    {U : DimSubspace K (Fin D → K) r // (Q.toBilin'.restrict U.val).Nondegenerate ∧
      discriminantSign (Q.toBilin'.restrict U.val)
        ((Matrix.isSymm_toBilin'_iff_isSymm.mpr hQ).restrict U.val)=ξ} where
  toFun A :=
    ⟨⟨(centerSubspaceEquiv Q hQ hdet A.val).val,
      (centerSubspaceEquiv_rank Q hQ hdet A.val).trans A.property.1⟩,
      (centerSubspaceEquiv Q hQ hdet A.val).property,
      (centerSubspaceEquiv_sign Q hQ hdet A.val).symm.trans A.property.2⟩
  invFun U :=
    ⟨(centerSubspaceEquiv Q hQ hdet).symm ⟨U.val.val,U.property.1⟩,by
      constructor
      · rw [←centerSubspaceEquiv_rank Q hQ hdet,Equiv.apply_symm_apply]; exact U.val.property
      · rw [centerSubspaceEquiv_sign Q hQ hdet,Equiv.apply_symm_apply]; exact U.property.2⟩
  left_inv A := by
    apply Subtype.ext
    exact (centerSubspaceEquiv Q hQ hdet).symm_apply_apply A.val
  right_inv U := by
    apply Subtype.ext
    apply Subtype.ext
    change ((centerSubspaceEquiv Q hQ hdet)
      ((centerSubspaceEquiv Q hQ hdet).symm ⟨U.val.val,U.property.1⟩)).val=U.val.val
    rw [Equiv.apply_symm_apply]
end SignedProjector
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module LinearMap
open scoped Matrix BigOperators
section Isotropic
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
theorem restrict_eq_zero_iff_isotropic (L : LinearMap.BilinForm K V) (U : Submodule K V) :
    L.restrict U=0 ↔ U ≤ L.orthogonal U := by
  constructor
  · intro h x hx y hy
    have he := congrArg (fun B : LinearMap.BilinForm K U => B ⟨y,hy⟩ ⟨x,hx⟩) h
    exact he
  · intro h
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    exact h y.property x.val x.property
variable [FiniteDimensional K V]
theorem half_isotropic_iff_self (L : LinearMap.BilinForm K V) (hL : L.Nondegenerate)
    (r : ℕ) (hd : finrank K V=2*r) (U : Submodule K V) (hu : finrank K U=r) :
    L.restrict U=0 ↔ L.orthogonal U=U := by
  rw [restrict_eq_zero_iff_isotropic]
  constructor
  · intro h
    symm
    apply Submodule.eq_of_le_of_finrank_eq h
    have hr := L.finrank_orthogonal hL U
    omega
  · intro h; rw [h]
noncomputable def halfIsotropicEquiv (L : LinearMap.BilinForm K V) (hL : L.Nondegenerate)
    (r : ℕ) (hd : finrank K V=2*r) :
    {U : DimSubspace K V r // L.restrict U.val=0} ≃ SymplecticLagrangian L where
  toFun U := ⟨U.val.val,(half_isotropic_iff_self L hL r hd U.val.val U.val.property).mp U.property⟩
  invFun U := ⟨⟨U.val,by
    have h := self_orthogonal_twice_finrank L U.val hL U.property
    omega⟩,(restrict_eq_zero_iff_isotropic L U.val).mpr (by rw [U.property])⟩
  left_inv U := by apply Subtype.ext; rfl
  right_inv U := rfl
end Isotropic
section Triple
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] {D r : ℕ}
noncomputable def tripleSignedCenterEquiv (hd : D=2*r) (B C : SymMatrix K D)
    (hB : B.val.det≠0) (hC : C.val.det≠0) (ξ ζ θ : ℤ)
    (hmB : quadraticChar K B.val.det=quadraticChar K ((-1 : K)^r)*ξ*ζ)
    (hmC : quadraticChar K C.val.det=quadraticChar K ((-1 : K)^r)*ξ*θ) :
    {A : SymMatrix K D // A ∈ signedLayer K D r ξ ∧ A-B ∈ signedLayer K D r ζ ∧
      A-C ∈ signedLayer K D r θ} ≃
    {A : SignedProjector B.val⁻¹ r ξ // (B.val⁻¹-C.val⁻¹).toBilin'.restrict A.val.val.toLin'.range=0} where
  toFun A := ⟨pairSignedCenterEquiv hd B hB ξ ζ hmB ⟨A.val,A.property.1,A.property.2.1⟩,by
    apply (center_second_equation B.val⁻¹ C.val⁻¹ A.val.val A.val.property
      ((pairSignedCenterEquiv hd B hB ξ ζ hmB ⟨A.val,A.property.1,A.property.2.1⟩).val.property.2)).mp
    exact (signed_second_iff hd A.val C hC ((mem_signedLayer ..).mp A.property.1).1
      ((mem_signedLayer ..).mp A.property.1).2 hmC).mp ((mem_signedLayer ..).mp A.property.2.2)⟩
  invFun A :=
    let a := (pairSignedCenterEquiv hd B hB ξ ζ hmB).symm A.val
    ⟨a.val,a.property.1,a.property.2,(mem_signedLayer ..).mpr
      ((signed_second_iff hd a.val C hC ((mem_signedLayer ..).mp a.property.1).1
        ((mem_signedLayer ..).mp a.property.1).2 hmC).mpr
        ((center_second_equation B.val⁻¹ C.val⁻¹ A.val.val.val A.val.val.property.1
          A.val.val.property.2).mpr A.property))⟩
  left_inv A := by apply Subtype.ext; rfl
  right_inv A := by apply Subtype.ext; rfl
end Triple
end SidorenkoCounterexample
end
end OAI
namespace OAI
section
namespace SidorenkoCounterexample
open Module LinearMap
open scoped Matrix BigOperators
section Count
variable {I K V : Type*} [Fintype I] [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
theorem uniformMean_mul_card (f : I → ℝ) :
    (Fintype.card I : ℝ)*uniformMean f=∑ i, f i := by
  by_cases h : Fintype.card I=0
  · have := Fintype.card_eq_zero_iff.mp h
    simp [uniformMean]
  · unfold uniformMean
    field_simp
theorem restrictionSign_count (U : I → Submodule K V) (Q : SymForm K V) (ξ : ℤ) :
    (Nat.card {i : I // (Q.val.restrict (U i)).Nondegenerate ∧
      discriminantSign (Q.val.restrict (U i)) (Q.property.restrict (U i))=ξ} : ℝ) =
    (Fintype.card I : ℝ)*uniformMean (fun i => formSignIndicator ξ (symFormPull (U i).subtype Q)) := by
  classical
  rw [uniformMean_mul_card,Nat.card_eq_fintype_card,Fintype.card_subtype,←Finset.sum_boole]
  apply Finset.sum_congr rfl
  intro i _
  change (if (Q.val.restrict (U i)).Nondegenerate ∧
    discriminantSign (Q.val.restrict (U i)) (Q.property.restrict (U i))=ξ then 1 else 0 : ℝ) =
    if (Q.val.restrict (U i)).Nondegenerate then
      if discriminantSign (Q.val.restrict (U i)) (Q.property.restrict (U i))=ξ then 1 else 0 else 0
  split_ifs <;> simp_all
end Count
section Identities
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] {D r : ℕ}
noncomputable def signedProjectorIsotropicEquiv (Q : Matrix (Fin D) (Fin D) K)
    (hQ : Q.IsSymm) (hdet : Q.det≠0) (r : ℕ) (ξ : ℤ)
    (L : LinearMap.BilinForm K (Fin D → K)) :
    {A : SignedProjector Q r ξ // L.restrict A.val.val.toLin'.range=0} ≃
    {U : {U : DimSubspace K (Fin D → K) r // L.restrict U.val=0} //
      (Q.toBilin'.restrict U.val.val).Nondegenerate ∧
      discriminantSign (Q.toBilin'.restrict U.val.val)
        ((Matrix.isSymm_toBilin'_iff_isSymm.mpr hQ).restrict U.val.val)=ξ} where
  toFun A :=
    let U := signedProjectorSubspaceEquiv Q hQ hdet r ξ A.val
    ⟨⟨U.val,by
      change L.restrict (centerSubspaceEquiv Q hQ hdet A.val.val).val=0
      rw [centerSubspaceEquiv_val]; exact A.property⟩,U.property⟩
  invFun U :=
    let A := (signedProjectorSubspaceEquiv Q hQ hdet r ξ).symm ⟨U.val.val,U.property⟩
    ⟨A,by
      rw [←centerSubspaceEquiv_val Q hQ hdet]
      change L.restrict ((signedProjectorSubspaceEquiv Q hQ hdet r ξ) A).val.val=0
      rw [show (signedProjectorSubspaceEquiv Q hQ hdet r ξ) A=⟨U.val.val,U.property⟩ from
        Equiv.apply_symm_apply _ _]
      exact U.val.property⟩
  left_inv A := by
    apply Subtype.ext
    exact (signedProjectorSubspaceEquiv Q hQ hdet r ξ).symm_apply_apply A.val
  right_inv U := by
    apply Subtype.ext
    apply Subtype.ext
    change ((signedProjectorSubspaceEquiv Q hQ hdet r ξ)
      ((signedProjectorSubspaceEquiv Q hQ hdet r ξ).symm ⟨U.val.val,U.property⟩)).val=U.val.val
    rw [Equiv.apply_symm_apply]
noncomputable def pairRestrictionFraction (Q : SymMatrix K D) (r : ℕ) (ξ : ℤ) : ℝ := by
  classical
  let := Fintype.ofFinite (DimSubspace K (Fin D → K) r)
  exact uniformMean (fun U : DimSubspace K (Fin D → K) r =>
    formSignIndicator ξ (symFormPull U.val.subtype (matrixFormEquiv D Q)))
noncomputable def isotropicRestrictionFraction (Q : SymMatrix K D)
    (L : LinearMap.BilinForm K (Fin D → K)) (r : ℕ) (ξ : ℤ) : ℝ := by
  classical
  let := Fintype.ofFinite {U : DimSubspace K (Fin D → K) r // L.restrict U.val=0}
  exact uniformMean (fun U : {U : DimSubspace K (Fin D → K) r // L.restrict U.val=0} =>
    formSignIndicator ξ (symFormPull U.val.val.subtype (matrixFormEquiv D Q)))
theorem pairCenter_card (hd : D=2*r) (B : SymMatrix K D) (hB : B.val.det≠0)
    (ξ ζ : ℤ) (hm : quadraticChar K B.val.det=quadraticChar K ((-1 : K)^r)*ξ*ζ) :
    (Nat.card {A : SymMatrix K D // A ∈ signedLayer K D r ξ ∧ A-B ∈ signedLayer K D r ζ} : ℝ) =
    (Nat.card (DimSubspace K (Fin D → K) r) : ℝ) *
      pairRestrictionFraction (⟨B.val⁻¹,B.property.inv⟩ : SymMatrix K D) r ξ := by
  classical
  let := Fintype.ofFinite (DimSubspace K (Fin D → K) r)
  have hn : B.val⁻¹.det≠0 := by simpa [Matrix.det_nonsing_inv] using inv_ne_zero hB
  rw [Nat.card_congr ((pairSignedCenterEquiv hd B hB ξ ζ hm).trans
    (signedProjectorSubspaceEquiv B.val⁻¹ B.property.inv hn r ξ))]
  exact (restrictionSign_count (fun U : DimSubspace K (Fin D → K) r => U.val)
    (matrixFormEquiv D ⟨B.val⁻¹,B.property.inv⟩) ξ).trans (by
      rw [Nat.card_eq_fintype_card]; rfl)
theorem tripleCenter_card (hd : D=2*r) (B C : SymMatrix K D)
    (hB : B.val.det≠0) (hC : C.val.det≠0) (ξ ζ θ : ℤ)
    (hmB : quadraticChar K B.val.det=quadraticChar K ((-1 : K)^r)*ξ*ζ)
    (hmC : quadraticChar K C.val.det=quadraticChar K ((-1 : K)^r)*ξ*θ) :
    (Nat.card {A : SymMatrix K D // A ∈ signedLayer K D r ξ ∧ A-B ∈ signedLayer K D r ζ ∧
      A-C ∈ signedLayer K D r θ} : ℝ) =
    (Nat.card {U : DimSubspace K (Fin D → K) r //
      (B.val⁻¹-C.val⁻¹).toBilin'.restrict U.val=0} : ℝ) *
      isotropicRestrictionFraction (⟨B.val⁻¹,B.property.inv⟩ : SymMatrix K D)
        (B.val⁻¹-C.val⁻¹).toBilin' r ξ := by
  classical
  let := Fintype.ofFinite {U : DimSubspace K (Fin D → K) r //
    (B.val⁻¹-C.val⁻¹).toBilin'.restrict U.val=0}
  have hn : B.val⁻¹.det≠0 := by simpa [Matrix.det_nonsing_inv] using inv_ne_zero hB
  rw [Nat.card_congr ((tripleSignedCenterEquiv hd B C hB hC ξ ζ θ hmB hmC).trans
    (signedProjectorIsotropicEquiv B.val⁻¹ B.property.inv hn r ξ _))]
  exact (restrictionSign_count (fun U : {U : DimSubspace K (Fin D → K) r //
    (B.val⁻¹-C.val⁻¹).toBilin'.restrict U.val=0} => U.val.val)
    (matrixFormEquiv D ⟨B.val⁻¹,B.property.inv⟩) ξ).trans (by
      rw [Nat.card_eq_fintype_card]; rfl)
end Identities
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module Filter
open scoped BigOperators
section Coeff
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
noncomputable def pairCoefficient (r : ℕ) (ξ ζ : ℤ) : ℝ :=
  (Nat.card (DimSubspace K (Fin (2*r) → K) r) : ℝ) /
    (Fintype.card (SymMatrix K (2*r)) : ℝ) /
      (layerMass K (2*r) r ξ * layerMass K (2*r) r ζ)
noncomputable def tripleCoefficient (r : ℕ) (ξ ζ θ : ℤ) : ℝ :=
  (Nat.card (MaxOrthogonal (K := K) (V := Fin r → K)) : ℝ) /
    (Fintype.card (SymMatrix K (2*r)) : ℝ) /
      (layerMass K (2*r) r ξ * layerMass K (2*r) r ζ * layerMass K (2*r) r θ)
theorem pair_exponent_cancel (r : ℕ) :
    r*r+2*((r+1).choose 2)=(2*r+1).choose 2 := by
  have h := triangular_nat_add r r
  have he : r+r+1=2*r+1 := by omega
  rw [he] at h
  omega
theorem triple_exponent_cancel (r : ℕ) :
    r.choose 2+3*((r+1).choose 2)=(2*r+1).choose 2 := by
  have h : (r.choose 2 : ℚ)+3*((r+1).choose 2 : ℚ)=((2*r+1).choose 2 : ℚ) := by
    simp only [Nat.cast_choose_two,Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat]
    ring
  exact_mod_cast h
theorem pairCoefficient_normalized (r : ℕ) (ξ ζ : ℤ) :
    pairCoefficient (K := K) r ξ ζ =
      grassmannFactor (2*r) r (Fintype.card K) /
        ((layerMass K (2*r) r ξ * (Fintype.card K : ℝ)^((r+1).choose 2)) *
          (layerMass K (2*r) r ζ * (Fintype.card K : ℝ)^((r+1).choose 2))) := by
  unfold pairCoefficient
  rw [subspace_count_normalized r (by simp; omega),←Nat.card_eq_fintype_card (α := SymMatrix K (2*r)),symMatrix_card]
  simp only [Module.finrank_fin_fun,show 2*r-r=r by omega,Nat.cast_pow]
  rw [←pair_exponent_cancel,pow_add,pow_mul]
  have hq : (Fintype.card K : ℝ)≠0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp
  ring
theorem tripleCoefficient_normalized (hK : ringChar K≠2) (r : ℕ) (ξ ζ θ : ℤ) :
    tripleCoefficient (K := K) r ξ ζ θ =
      orthogonalFactor r (Fintype.card K) /
        ((layerMass K (2*r) r ξ * (Fintype.card K : ℝ)^((r+1).choose 2)) *
          (layerMass K (2*r) r ζ * (Fintype.card K : ℝ)^((r+1).choose 2)) *
          (layerMass K (2*r) r θ * (Fintype.card K : ℝ)^((r+1).choose 2))) := by
  have he := maxOrthogonal_normalized (K := K) hK r
  unfold tripleCoefficient
  rw [←he,←Nat.card_eq_fintype_card (α := SymMatrix K (2*r)),symMatrix_card,Nat.cast_pow,
    ←triple_exponent_cancel,pow_add,pow_mul]
  have hq : (Fintype.card K : ℝ)≠0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp
  ring
theorem pairCoefficient_nonneg (r : ℕ) (ξ ζ : ℤ) : 0≤pairCoefficient (K := K) r ξ ζ := by
  unfold pairCoefficient layerMass
  positivity
theorem tripleCoefficient_nonneg (r : ℕ) (ξ ζ θ : ℤ) : 0≤tripleCoefficient (K := K) r ξ ζ θ := by
  unfold tripleCoefficient layerMass
  positivity
end Coeff
theorem pairCoefficient_tendsto (r : ℕ) (hr : 0<r) {ξ ζ : ℤ}
    (hξ : ξ=1 ∨ ξ= -1) (hζ : ζ=1 ∨ ζ= -1) :
    Tendsto (fun q : OddPrime => pairCoefficient (K := ZMod q.val) r ξ ζ)
      primeInfinity (nhds 4) := by
  have hx := layerMass_tendsto (2*r) r hr (by omega) hξ
  have hz := layerMass_tendsto (2*r) r hr (by omega) hζ
  have hf := (grassmannFactor_tendsto (2*r) r (by omega)).comp primeInfinity_real_tendsto
  have h := hf.div (hx.mul hz) (by norm_num)
  simp only [show 2*r-r=r by omega,Function.comp_def] at h
  norm_num only at h
  simp_rw [pairCoefficient_normalized,ZMod.card]
  exact h
theorem tripleCoefficient_tendsto (r : ℕ) (hr : 0<r) {ξ ζ θ : ℤ}
    (hξ : ξ=1 ∨ ξ= -1) (hζ : ζ=1 ∨ ζ= -1) (hθ : θ=1 ∨ θ= -1) :
    Tendsto (fun q : OddPrime => tripleCoefficient (K := ZMod q.val) r ξ ζ θ)
      primeInfinity (nhds 16) := by
  have hx := layerMass_tendsto (2*r) r hr (by omega) hξ
  have hz := layerMass_tendsto (2*r) r hr (by omega) hζ
  have ht := layerMass_tendsto (2*r) r hr (by omega) hθ
  have hf := (orthogonalFactor_tendsto r hr).comp primeInfinity_real_tendsto
  have h := hf.div ((hx.mul hz).mul ht) (by norm_num)
  simp only [show 2*r-r=r by omega,Function.comp_def] at h
  norm_num only at h
  have he (q : OddPrime) := tripleCoefficient_normalized (K := ZMod q.val)
    (by simpa only [ZMod.ringChar_zmod_n] using q.property.2) r ξ ζ θ
  simp only [ZMod.card] at he
  simp_rw [he]
  exact h
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section Sizes
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
omit [DecidableEq K] in
theorem maxOrthogonal_card_lower (r : ℕ) :
    Fintype.card K ^ r.choose 2 ≤ Nat.card (MaxOrthogonal (K := K) (V := Fin r → K)) := by
  classical
  let : Finite (Module.Dual K (Fin r → K)) := Module.finite_of_finite K
  have h := Nat.card_le_card_of_injective (f := graphMaxOrthogonal (K := K) (⊤ : Submodule K (Fin r → K))) (graphMaxOrthogonal_form_injective
    (K := K) (⊤ : Submodule K (Fin r → K)))
  simpa only [altForm_card,finrank_top,Module.finrank_fin_fun] using h
theorem halfIsotropic_card (r : ℕ) (L : LinearMap.BilinForm K (Fin (2*r) → K))
    (hs : L.IsSymm) (hL : L.Nondegenerate) (hK : ringChar K≠2)
    (hc : discriminantSign L hs=quadraticChar K ((-1 : K)^r)) :
    Nat.card {U : DimSubspace K (Fin (2*r) → K) r // L.restrict U.val=0} =
      Nat.card (MaxOrthogonal (K := K) (V := Fin r → K)) := by
  rw [Nat.card_congr (halfIsotropicEquiv L hL r (by simp))]
  exact split_form_card L hs hL hK r (by simp) hc
omit [DecidableEq K] in
theorem pairFamily_card_ge (r : ℕ) (hr : 0<r) :
    (Fintype.card K : ℝ) ≤ Nat.card (DimSubspace K (Fin (2*r) → K) r) := by
  have h := subspace_count_lower (K := K) (V := Fin (2*r) → K) r (by simp; omega)
  simp only [Module.finrank_fin_fun,show 2*r-r=r by omega] at h
  apply le_trans _ h
  have hq : (1 : ℝ)≤Fintype.card K := by exact_mod_cast (Fintype.one_lt_card (α := K)).le
  simpa only [pow_one] using pow_le_pow_right₀ hq (show 1≤r*r from Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)))
theorem isotropicFamily_card_ge (r : ℕ) (hr : 1<r)
    (L : LinearMap.BilinForm K (Fin (2*r) → K)) (hs : L.IsSymm) (hL : L.Nondegenerate)
    (hK : ringChar K≠2) (hc : discriminantSign L hs=quadraticChar K ((-1 : K)^r)) :
    (Fintype.card K : ℝ) ≤ Nat.card {U : DimSubspace K (Fin (2*r) → K) r // L.restrict U.val=0} := by
  rw [halfIsotropic_card r L hs hL hK hc]
  have h : (Fintype.card K : ℝ)^r.choose 2 ≤ Nat.card (MaxOrthogonal (K := K) (V := Fin r → K)) := by
    exact_mod_cast maxOrthogonal_card_lower (K := K) r
  apply le_trans _ h
  have hq : (1 : ℝ)≤Fintype.card K := by exact_mod_cast (Fintype.one_lt_card (α := K)).le
  simpa only [pow_one] using pow_le_pow_right₀ hq (Nat.choose_pos (show 2≤r by omega))
end Sizes
section Bounds
variable {K I : Type*} [Field K] [Fintype K] [DecidableEq K] [Fintype I] {D r : ℕ}
theorem matrix_restriction_family_L1 (U : I → Submodule K (Fin D → K))
    (hinj : Function.Injective U) (hd : ∀ i, finrank K (U i)=r)
    (hc : (Fintype.card K : ℝ)≤Fintype.card I) (hK : ringChar K≠2)
    {ξ : ℤ} (hξ : ξ=1 ∨ ξ= -1) :
    uniformMean (fun Q : SymMatrix K D =>
      |uniformMean (fun i => formSignIndicator ξ (symFormPull (U i).subtype (matrixFormEquiv D Q)))-1/2|) ≤
        Real.sqrt (((r : ℝ)+1)/(Fintype.card K : ℝ)) := by
  have hq : (0 : ℝ)<Fintype.card K := Nat.cast_pos.mpr Fintype.card_pos
  have hi : (0 : ℝ)<Fintype.card I := hq.trans_le hc
  have : Nonempty I := Fintype.card_pos_iff.mp (Nat.cast_pos.mp hi)
  have he := uniformMean_equiv (matrixFormEquiv (K := K) D)
    (fun Q => |uniformMean (fun i => formSignIndicator ξ (symFormPull (U i).subtype Q))-1/2|)
  dsimp only [Function.comp_def] at he
  rw [he]
  have h := restriction_family_L1_sq U hinj r hd hK hξ
  have hiq : 1/(Fintype.card I : ℝ)≤1/(Fintype.card K : ℝ) := one_div_le_one_div_of_le hq hc
  have ht : (r : ℝ)/(Fintype.card K : ℝ)+1/(Fintype.card I : ℝ) ≤
      ((r : ℝ)+1)/(Fintype.card K : ℝ) := by rw [add_div]; linarith
  exact (Real.le_sqrt (uniformMean_nonneg (fun _ => abs_nonneg _)) (by positivity)).mpr (h.trans ht)
theorem pairRestrictionFraction_L1 (r : ℕ) (hr : 0<r) (hK : ringChar K≠2)
    {ξ : ℤ} (hξ : ξ=1 ∨ ξ= -1) :
    uniformMean (fun Q : SymMatrix K (2*r) => |pairRestrictionFraction Q r ξ-1/2|) ≤
      Real.sqrt (((r : ℝ)+1)/(Fintype.card K : ℝ)) := by
  classical
  let := Fintype.ofFinite (DimSubspace K (Fin (2*r) → K) r)
  exact matrix_restriction_family_L1 (fun U : DimSubspace K (Fin (2*r) → K) r => U.val)
    Subtype.val_injective (fun U => U.property)
    (by simpa only [Nat.card_eq_fintype_card] using pairFamily_card_ge (K := K) r hr) hK hξ
theorem isotropicRestrictionFraction_L1 (r : ℕ) (hr : 1<r)
    (L : LinearMap.BilinForm K (Fin (2*r) → K)) (hs : L.IsSymm) (hL : L.Nondegenerate)
    (hK : ringChar K≠2) (hc : discriminantSign L hs=quadraticChar K ((-1 : K)^r))
    {ξ : ℤ} (hξ : ξ=1 ∨ ξ= -1) :
    uniformMean (fun Q : SymMatrix K (2*r) => |isotropicRestrictionFraction Q L r ξ-1/2|) ≤
      Real.sqrt (((r : ℝ)+1)/(Fintype.card K : ℝ)) := by
  classical
  let := Fintype.ofFinite {U : DimSubspace K (Fin (2*r) → K) r // L.restrict U.val=0}
  exact matrix_restriction_family_L1 (fun U : {U : DimSubspace K (Fin (2*r) → K) r // L.restrict U.val=0} => U.val.val)
    (Subtype.val_injective.comp Subtype.val_injective) (fun U => U.val.property)
    (by simpa only [Nat.card_eq_fintype_card] using isotropicFamily_card_ge r hr L hs hL hK hc) hK hξ
end Bounds
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open scoped BigOperators
section Mean
variable {I A B : Type*} [Fintype I] [DecidableEq I] [Fintype A] [Fintype B]
omit [DecidableEq I] in
theorem uniformMean_sum (f : I → A → ℝ) :
    uniformMean (fun a => ∑ i, f i a)=∑ i, uniformMean (f i) := by
  unfold uniformMean
  rw [Finset.sum_comm,Finset.sum_div]
theorem uniformMean_mul_right (f : A → ℝ) (c : ℝ) :
    uniformMean (fun a => f a*c)=uniformMean f*c := by
  simpa only [mul_comm] using uniformMean_mul c f
end Mean
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open scoped BigOperators
open Module
section Inverting
variable {K : Type*} [Field K] [Fintype K]
noncomputable def symmetricInverse (D : ℕ) (M : SymMatrix K D) : SymMatrix K D :=
  by
  classical
  exact if M.val.det = 0 then M else ⟨M.val⁻¹, M.property.inv⟩
omit [Fintype K] in
 theorem symmetricInverse_involutive (D : ℕ) : Function.Involutive (symmetricInverse (K := K) D) := by
  classical
  intro M
  by_cases h : M.val.det = 0
  · have he : symmetricInverse D M = M := by simp only [symmetricInverse, h, ↓reduceIte]
    rw [he, he]
  · let M' : SymMatrix K D := ⟨M.val⁻¹, M.property.inv⟩
    have he : symmetricInverse D M = M' := by simp only [symmetricInverse, h, ↓reduceIte, M']
    have hn : M'.val.det ≠ 0 := (M.val.isUnit_nonsing_inv_det (isUnit_iff_ne_zero.mpr h)).ne_zero
    have he' : symmetricInverse D M' = ⟨M'.val⁻¹, M'.property.inv⟩ := by
      simp only [symmetricInverse, hn, ↓reduceIte]
    rw [he, he']
    exact Subtype.ext (M.val.nonsing_inv_nonsing_inv (isUnit_iff_ne_zero.mpr h))
noncomputable def symmetricInverseEquiv (D : ℕ) : SymMatrix K D ≃ SymMatrix K D :=
  (symmetricInverse_involutive D).toPerm
end Inverting
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module Classical
open scoped Matrix BigOperators
section Center
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
noncomputable def pairLocal (r : ℕ) (ξ ζ : ℤ) (B : SymMatrix K (2*r)) : ℝ :=
  uniformMean (fun A => rankKernel K (2*r) r ξ A * rankKernel K (2*r) r ζ (A-B))
noncomputable def tripleLocal (r : ℕ) (ξ ζ θ : ℤ) (B C : SymMatrix K (2*r)) : ℝ :=
  uniformMean (fun A => rankKernel K (2*r) r ξ A * rankKernel K (2*r) r ζ (A-B) *
    rankKernel K (2*r) r θ (A-C))
def pairMatch (r : ℕ) (ξ ζ : ℤ) (B : SymMatrix K (2*r)) : Prop :=
  quadraticChar K B.val.det=quadraticChar K ((-1 : K)^r)*ξ*ζ
def tripleMatch (r : ℕ) (ξ ζ θ : ℤ) (B C : SymMatrix K (2*r)) : Prop :=
  pairMatch r ξ ζ B ∧ pairMatch r ξ θ C ∧ pairMatch r ζ θ (C-B)
theorem pairLocal_card (r : ℕ) (ξ ζ : ℤ) (B : SymMatrix K (2*r)) :
    pairLocal r ξ ζ B =
      (Nat.card {A : SymMatrix K (2*r) // A ∈ signedLayer K (2*r) r ξ ∧
        A-B ∈ signedLayer K (2*r) r ζ} : ℝ) /
      (Fintype.card (SymMatrix K (2*r)) : ℝ) /
        (layerMass K (2*r) r ξ * layerMass K (2*r) r ζ) := by
  have he (A : SymMatrix K (2*r)) :
      rankKernel K (2*r) r ξ A * rankKernel K (2*r) r ζ (A-B) =
      (if A ∈ signedLayer K (2*r) r ξ ∧ A-B ∈ signedLayer K (2*r) r ζ then (1 : ℝ) else 0) *
        (layerMass K (2*r) r ξ * layerMass K (2*r) r ζ)⁻¹ := by
    unfold rankKernel
    split_ifs <;> simp_all [mul_comm]
  unfold pairLocal
  simp_rw [he]
  rw [uniformMean_mul_right,uniformMean_indicator,Nat.card_eq_fintype_card]
  rfl
theorem tripleLocal_card (r : ℕ) (ξ ζ θ : ℤ) (B C : SymMatrix K (2*r)) :
    tripleLocal r ξ ζ θ B C =
      (Nat.card {A : SymMatrix K (2*r) // A ∈ signedLayer K (2*r) r ξ ∧
        A-B ∈ signedLayer K (2*r) r ζ ∧ A-C ∈ signedLayer K (2*r) r θ} : ℝ) /
      (Fintype.card (SymMatrix K (2*r)) : ℝ) /
        (layerMass K (2*r) r ξ * layerMass K (2*r) r ζ * layerMass K (2*r) r θ) := by
  have he (A : SymMatrix K (2*r)) :
      rankKernel K (2*r) r ξ A * rankKernel K (2*r) r ζ (A-B) * rankKernel K (2*r) r θ (A-C) =
      (if A ∈ signedLayer K (2*r) r ξ ∧ A-B ∈ signedLayer K (2*r) r ζ ∧
        A-C ∈ signedLayer K (2*r) r θ then (1 : ℝ) else 0) *
        (layerMass K (2*r) r ξ * layerMass K (2*r) r ζ * layerMass K (2*r) r θ)⁻¹ := by
    unfold rankKernel
    split_ifs <;> simp_all [mul_comm,mul_assoc]
  unfold tripleLocal
  simp_rw [he]
  rw [uniformMean_mul_right,uniformMean_indicator,Nat.card_eq_fintype_card]
  rfl
theorem pairLocal_match (r : ℕ) (ξ ζ : ℤ) (B : SymMatrix K (2*r))
    (hB : B.val.det≠0) (hm : pairMatch r ξ ζ B) :
    pairLocal r ξ ζ B = pairCoefficient (K := K) r ξ ζ *
      pairRestrictionFraction (symmetricInverse (2*r) B) r ξ := by
  rw [pairLocal_card,pairCenter_card rfl B hB ξ ζ hm]
  simp only [symmetricInverse,hB,ite_false]
  unfold pairCoefficient
  ring
theorem pairLocal_mismatch (r : ℕ) (ξ ζ : ℤ) (B : SymMatrix K (2*r))
    (hB : B.val.det≠0) (hm : ¬pairMatch r ξ ζ B) : pairLocal r ξ ζ B=0 := by
  unfold pairLocal
  have he (A : SymMatrix K (2*r)) :
      rankKernel K (2*r) r ξ A * rankKernel K (2*r) r ζ (A-B)=0 := by
    unfold rankKernel
    split_ifs with hx hz
    · obtain ⟨ha,hs⟩ := (mem_signedLayer ..).mp hx
      obtain ⟨hb,ht⟩ := (mem_signedLayer ..).mp hz
      have h := signed_pair_compatibility rfl A B hB ha hb
      rw [hs,ht] at h
      exact (hm h).elim
    all_goals simp
  simp_rw [he]
  exact uniformMean_const 0
theorem tripleLocal_mismatch (r : ℕ) (ξ ζ θ : ℤ) (B C : SymMatrix K (2*r))
    (hB : B.val.det≠0) (hC : C.val.det≠0) (hBC : (C-B).val.det≠0)
    (hm : ¬tripleMatch r ξ ζ θ B C) : tripleLocal r ξ ζ θ B C=0 := by
  unfold tripleLocal
  have he (A : SymMatrix K (2*r)) :
      rankKernel K (2*r) r ξ A * rankKernel K (2*r) r ζ (A-B) * rankKernel K (2*r) r θ (A-C)=0 := by
    unfold rankKernel
    split_ifs with hx hz ht
    · obtain ⟨ha,hs⟩ := (mem_signedLayer ..).mp hx
      obtain ⟨hb,hz⟩ := (mem_signedLayer ..).mp hz
      obtain ⟨hc,ht⟩ := (mem_signedLayer ..).mp ht
      have h1 := signed_pair_compatibility rfl A B hB ha hb
      have h2 := signed_pair_compatibility rfl A C hC ha hc
      have h3 := signed_pair_compatibility rfl (A-B) (C-B) hBC hb (by simpa using hc)
      simp only [sub_sub_sub_cancel_right] at h3
      rw [hs,hz] at h1
      rw [hs,ht] at h2
      rw [hz,ht] at h3
      exact (hm ⟨h1,h2,h3⟩).elim
    all_goals simp
  simp_rw [he]
  exact uniformMean_const 0
omit [Fintype K] [DecidableEq K] in
theorem inverse_difference_det (D : ℕ) (B C : SymMatrix K D)
    (hB : B.val.det≠0) (hC : C.val.det≠0) :
    (B.val⁻¹-C.val⁻¹).det = B.val.det⁻¹ * (C-B).val.det * C.val.det⁻¹ := by
  rw [Matrix.inv_sub_inv (by
    exact iff_of_true ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hB))
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hC)))]
  simp only [Matrix.det_mul,Matrix.det_nonsing_inv,Ring.inverse_eq_inv,Submodule.coe_sub]
omit [Fintype K] [DecidableEq K] in
theorem inverse_difference_nondegenerate (D : ℕ) (B C : SymMatrix K D)
    (hB : B.val.det≠0) (hC : C.val.det≠0) (hBC : (C-B).val.det≠0) :
    (B.val⁻¹-C.val⁻¹).toBilin'.Nondegenerate := by
  apply Matrix.nondegenerate_toBilin'_iff.mpr
  apply Matrix.nondegenerate_iff_det_ne_zero.mpr
  rw [inverse_difference_det D B C hB hC]
  exact mul_ne_zero (mul_ne_zero (inv_ne_zero hB) hBC) (inv_ne_zero hC)
theorem matching_inverse_difference_split (r : ℕ) (B C : SymMatrix K (2*r))
    (hB : B.val.det≠0) (hC : C.val.det≠0) (hBC : (C-B).val.det≠0)
    {ξ ζ θ : ℤ} (hξ : ξ=1 ∨ ξ= -1) (hζ : ζ=1 ∨ ζ= -1) (hθ : θ=1 ∨ θ= -1)
    (hm : tripleMatch r ξ ζ θ B C) :
    discriminantSign (B.val⁻¹-C.val⁻¹).toBilin'
      (Matrix.isSymm_toBilin'_iff_isSymm.mpr (B.property.inv.sub C.property.inv)) =
        quadraticChar K ((-1 : K)^r) := by
  rw [discriminantSign_nondegenerate _ _ (inverse_difference_nondegenerate (2*r) B C hB hC hBC)
    (Pi.basisFun K (Fin (2*r)))]
  change quadraticChar K ((B.val⁻¹-C.val⁻¹).toBilin'.toMatrix').det = _
  rw [LinearMap.BilinForm.toMatrix'_toBilin',inverse_difference_det (2*r) B C hB hC,
    map_mul,map_mul,quadraticChar_inverse hB,quadraticChar_inverse hC]
  rw [hm.1,hm.2.1,hm.2.2]
  have hc := quadraticChar_sq_one (F := K) (pow_ne_zero r (neg_ne_zero.mpr one_ne_zero))
  have hx : ξ^2=1 := by rcases hξ with rfl | rfl <;> norm_num
  have hz : ζ^2=1 := by rcases hζ with rfl | rfl <;> norm_num
  have ht : θ^2=1 := by rcases hθ with rfl | rfl <;> norm_num
  calc
    _ = quadraticChar K ((-1 : K)^r) * (quadraticChar K ((-1 : K)^r))^2 * ξ^2 * ζ^2 * θ^2 := by ring
    _ = _ := by rw [hc,hx,hz,ht]; ring
theorem tripleLocal_match (hK : ringChar K≠2) (r : ℕ) (B C : SymMatrix K (2*r))
    (hB : B.val.det≠0) (hC : C.val.det≠0) (hBC : (C-B).val.det≠0)
    {ξ ζ θ : ℤ} (hξ : ξ=1 ∨ ξ= -1) (hζ : ζ=1 ∨ ζ= -1) (hθ : θ=1 ∨ θ= -1)
    (hm : tripleMatch r ξ ζ θ B C) :
    tripleLocal r ξ ζ θ B C = tripleCoefficient (K := K) r ξ ζ θ *
      isotropicRestrictionFraction (symmetricInverse (2*r) B) (B.val⁻¹-C.val⁻¹).toBilin' r ξ := by
  rw [tripleLocal_card,tripleCenter_card rfl B C hB hC ξ ζ θ hm.1 hm.2.1,
    halfIsotropic_card r _ (Matrix.isSymm_toBilin'_iff_isSymm.mpr (B.property.inv.sub C.property.inv))
      (inverse_difference_nondegenerate (2*r) B C hB hC hBC) hK
      (matching_inverse_difference_split r B C hB hC hBC hξ hζ hθ hm)]
  simp only [symmetricInverse,hB,ite_false]
  unfold tripleCoefficient
  ring
end Center
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module Classical
open scoped BigOperators
section Means
variable {A B : Type*} [Fintype A] [Fintype B]
theorem uniformMean_le_one {f : A → ℝ} (hf : ∀ a, f a ≤ 1) : uniformMean f ≤ 1 := by
  cases isEmpty_or_nonempty A
  · simp [uniformMean]
  · exact uniformMean_bound hf
variable [AddCommGroup A]
theorem uniformMean_subLeft (a : A) (f : A → ℝ) :
    uniformMean (fun x => f (a-x))=uniformMean f :=
  uniformMean_equiv (Equiv.subLeft a) f
end Means
section Range
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] {D : ℕ}
theorem pairRestrictionFraction_range (Q : SymMatrix K D) (r : ℕ) (ξ : ℤ) :
    0 ≤ pairRestrictionFraction Q r ξ ∧ pairRestrictionFraction Q r ξ ≤ 1 := by
  let := Fintype.ofFinite (DimSubspace K (Fin D → K) r)
  unfold pairRestrictionFraction
  exact ⟨uniformMean_nonneg (fun _ => formSignIndicator_nonneg _ _),
    uniformMean_le_one (fun _ => formSignIndicator_le_one _ _)⟩
theorem isotropicRestrictionFraction_range (Q : SymMatrix K D)
    (L : LinearMap.BilinForm K (Fin D → K)) (r : ℕ) (ξ : ℤ) :
    0 ≤ isotropicRestrictionFraction Q L r ξ ∧ isotropicRestrictionFraction Q L r ξ ≤ 1 := by
  let := Fintype.ofFinite {U : DimSubspace K (Fin D → K) r // L.restrict U.val=0}
  unfold isotropicRestrictionFraction
  exact ⟨uniformMean_nonneg (fun _ => formSignIndicator_nonneg _ _),
    uniformMean_le_one (fun _ => formSignIndicator_le_one _ _)⟩
omit [DecidableEq K] in
theorem uniformMean_inverse (f : SymMatrix K D → ℝ) :
    uniformMean (fun B => f (symmetricInverse D B))=uniformMean f :=
  uniformMean_equiv (symmetricInverseEquiv D) f
omit [DecidableEq K] in
theorem uniformMean_inverse_difference (f : SymMatrix K D → SymMatrix K D → ℝ) :
    uniformMean (fun B => uniformMean fun C =>
      f (symmetricInverse D B) (symmetricInverse D B-symmetricInverse D C)) =
        uniformMean (fun L => uniformMean fun Q => f Q L) := by
  calc
    _ = uniformMean (fun B => uniformMean fun T => f (symmetricInverse D B) (symmetricInverse D B-T)) := by
      apply uniformMean_congr
      intro B
      exact uniformMean_inverse (fun T => f (symmetricInverse D B) (symmetricInverse D B-T))
    _ = uniformMean (fun B => uniformMean fun L => f (symmetricInverse D B) L) := by
      apply uniformMean_congr
      intro B
      exact uniformMean_subLeft (symmetricInverse D B) (f (symmetricInverse D B))
    _ = uniformMean (fun Q => uniformMean fun L => f Q L) :=
      uniformMean_inverse (fun Q => uniformMean fun L => f Q L)
    _ = _ := uniformMean_swap _
end Range
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module Classical Filter
open scoped BigOperators
theorem scalar_fraction_error (c f m : ℝ) (hc : 0 ≤ c) :
    |c*f-m| ≤ |c/2-m|+c*|f-1/2| := by
  calc
    _ = |(c/2-m)+c*(f-1/2)| := by congr 1; ring
    _ ≤ |c/2-m|+|c*(f-1/2)| := abs_add_le _ _
    _ = _ := by rw [abs_mul,abs_of_nonneg hc]
section Error
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
def matrixSplit (r : ℕ) (L : SymMatrix K (2*r)) : Prop :=
  L.val.det≠0 ∧ discriminantSign L.val.toBilin'
    (Matrix.isSymm_toBilin'_iff_isSymm.mpr L.property)=quadraticChar K ((-1 : K)^r)
noncomputable def pairError (r : ℕ) (ξ ζ : ℤ) (B : SymMatrix K (2*r)) : ℝ :=
  if B.val.det≠0 then |pairLocal r ξ ζ B-(if pairMatch r ξ ζ B then 2 else 0)| else 0
noncomputable def tripleError (r : ℕ) (ξ ζ θ : ℤ) (B C : SymMatrix K (2*r)) : ℝ :=
  if B.val.det≠0 ∧ C.val.det≠0 ∧ (C-B).val.det≠0 then
    |tripleLocal r ξ ζ θ B C-(if tripleMatch r ξ ζ θ B C then 8 else 0)| else 0
noncomputable def splitFractionError (r : ℕ) (ξ : ℤ) (Q L : SymMatrix K (2*r)) : ℝ :=
  if matrixSplit r L then |isotropicRestrictionFraction Q L.val.toBilin' r ξ-1/2| else 0
theorem splitFractionError_nonneg (r : ℕ) (ξ : ℤ) (Q L : SymMatrix K (2*r)) :
    0 ≤ splitFractionError r ξ Q L := by unfold splitFractionError; split <;> positivity
theorem pairError_pointwise (r : ℕ) (ξ ζ : ℤ) (B : SymMatrix K (2*r)) :
    pairError r ξ ζ B ≤ |pairCoefficient (K := K) r ξ ζ/2-2|+
      pairCoefficient (K := K) r ξ ζ*|pairRestrictionFraction (symmetricInverse (2*r) B) r ξ-1/2| := by
  have hc := pairCoefficient_nonneg (K := K) r ξ ζ
  unfold pairError
  split_ifs with hB hm
  · rw [pairLocal_match r ξ ζ B hB hm]
    exact scalar_fraction_error _ _ _ hc
  · rw [pairLocal_mismatch r ξ ζ B hB hm]
    simp only [sub_zero,abs_zero]
    positivity
  · positivity
theorem tripleError_pointwise (hK : ringChar K≠2) (r : ℕ) {ξ ζ θ : ℤ}
    (hξ : ξ=1 ∨ ξ= -1) (hζ : ζ=1 ∨ ζ= -1) (hθ : θ=1 ∨ θ= -1)
    (B C : SymMatrix K (2*r)) :
    tripleError r ξ ζ θ B C ≤ |tripleCoefficient (K := K) r ξ ζ θ/2-8|+
      tripleCoefficient (K := K) r ξ ζ θ * splitFractionError r ξ
        (symmetricInverse (2*r) B) (symmetricInverse (2*r) B-symmetricInverse (2*r) C) := by
  have hc := tripleCoefficient_nonneg (K := K) r ξ ζ θ
  have hf := splitFractionError_nonneg r ξ (symmetricInverse (2*r) B)
    (symmetricInverse (2*r) B-symmetricInverse (2*r) C)
  unfold tripleError
  split_ifs with ht hm
  · obtain ⟨hB,hC,hBC⟩ := ht
    have hs : matrixSplit r (symmetricInverse (2*r) B-symmetricInverse (2*r) C) := by
      simp only [matrixSplit,symmetricInverse,hB,hC,ite_false,Submodule.coe_sub]
      exact ⟨Matrix.nondegenerate_iff_det_ne_zero.mp
        (Matrix.nondegenerate_toBilin'_iff.mp (inverse_difference_nondegenerate (2*r) B C hB hC hBC)),
        matching_inverse_difference_split r B C hB hC hBC hξ hζ hθ hm⟩
    rw [tripleLocal_match hK r B C hB hC hBC hξ hζ hθ hm,splitFractionError,if_pos hs]
    simp only [symmetricInverse,hB,hC,ite_false,Submodule.coe_sub]
    exact scalar_fraction_error _ _ _ hc
  · rw [tripleLocal_mismatch r ξ ζ θ B C ht.1 ht.2.1 ht.2.2 hm]
    simp only [sub_zero,abs_zero]
    positivity
  · positivity
theorem splitFractionError_mean (hK : ringChar K≠2) (r : ℕ) (hr : 1<r)
    {ξ : ℤ} (hξ : ξ=1 ∨ ξ= -1) (L : SymMatrix K (2*r)) :
    uniformMean (fun Q => splitFractionError r ξ Q L) ≤
      Real.sqrt (((r : ℝ)+1)/(Fintype.card K : ℝ)) := by
  by_cases h : matrixSplit r L
  · simp only [splitFractionError,h,ite_true]
    exact isotropicRestrictionFraction_L1 r hr _
      (Matrix.isSymm_toBilin'_iff_isSymm.mpr L.property)
      (Matrix.nondegenerate_toBilin'_iff.mpr (Matrix.nondegenerate_iff_det_ne_zero.mpr h.1))
      hK h.2 hξ
  · simp only [splitFractionError,h,ite_false,uniformMean_const]
    positivity
theorem pairError_mean (hK : ringChar K≠2) (r : ℕ) (hr : 0<r)
    {ξ ζ : ℤ} (hξ : ξ=1 ∨ ξ= -1) :
    uniformMean (pairError (K := K) r ξ ζ) ≤ |pairCoefficient (K := K) r ξ ζ/2-2|+
      pairCoefficient (K := K) r ξ ζ * Real.sqrt (((r : ℝ)+1)/(Fintype.card K : ℝ)) := by
  apply (uniformMean_mono (pairError_pointwise r ξ ζ)).trans
  rw [uniformMean_add,uniformMean_const,uniformMean_mul,
    uniformMean_inverse (fun Q => |pairRestrictionFraction Q r ξ-1/2|)]
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (pairRestrictionFraction_L1 r hr hK hξ)
    (pairCoefficient_nonneg (K := K) r ξ ζ))
theorem tripleError_mean (hK : ringChar K≠2) (r : ℕ) (hr : 1<r)
    {ξ ζ θ : ℤ} (hξ : ξ=1 ∨ ξ= -1) (hζ : ζ=1 ∨ ζ= -1) (hθ : θ=1 ∨ θ= -1) :
    uniformMean (fun B => uniformMean (fun C => tripleError (K := K) r ξ ζ θ B C)) ≤
      |tripleCoefficient (K := K) r ξ ζ θ/2-8|+
        tripleCoefficient (K := K) r ξ ζ θ * Real.sqrt (((r : ℝ)+1)/(Fintype.card K : ℝ)) := by
  apply (uniformMean_mono (fun B => uniformMean_mono (tripleError_pointwise hK r hξ hζ hθ B))).trans
  simp_rw [uniformMean_add,uniformMean_const,uniformMean_mul]
  rw [uniformMean_inverse_difference]
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (uniformMean_bound (splitFractionError_mean hK r hr hξ)) (tripleCoefficient_nonneg (K := K) r ξ ζ θ))
end Error
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module Classical Filter
open scoped BigOperators
section Bounds
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
theorem pairError_nonneg (r : ℕ) (ξ ζ : ℤ) (B : SymMatrix K (2*r)) : 0≤pairError r ξ ζ B := by
  unfold pairError; split <;> positivity
theorem tripleError_nonneg (r : ℕ) (ξ ζ θ : ℤ) (B C : SymMatrix K (2*r)) :
    0≤tripleError r ξ ζ θ B C := by unfold tripleError; split <;> positivity
theorem pairLocal_bound (r : ℕ) (ξ ζ : ℤ) (B : SymMatrix K (2*r)) (hB : B.val.det≠0) :
    pairLocal r ξ ζ B ≤ pairCoefficient (K := K) r ξ ζ := by
  by_cases hm : pairMatch r ξ ζ B
  · rw [pairLocal_match r ξ ζ B hB hm]
    exact mul_le_of_le_one_right (pairCoefficient_nonneg ..) (pairRestrictionFraction_range _ _ _).2
  · rw [pairLocal_mismatch r ξ ζ B hB hm]
    exact pairCoefficient_nonneg ..
theorem tripleLocal_bound (hK : ringChar K≠2) (r : ℕ) {ξ ζ θ : ℤ}
    (hξ : ξ=1 ∨ ξ= -1) (hζ : ζ=1 ∨ ζ= -1) (hθ : θ=1 ∨ θ= -1)
    (B C : SymMatrix K (2*r)) (hB : B.val.det≠0) (hC : C.val.det≠0) (hBC : (C-B).val.det≠0) :
    tripleLocal r ξ ζ θ B C ≤ tripleCoefficient (K := K) r ξ ζ θ := by
  by_cases hm : tripleMatch r ξ ζ θ B C
  · rw [tripleLocal_match hK r B C hB hC hBC hξ hζ hθ hm]
    exact mul_le_of_le_one_right (tripleCoefficient_nonneg ..) (isotropicRestrictionFraction_range _ _ _ _).2
  · rw [tripleLocal_mismatch r ξ ζ θ B C hB hC hBC hm]
    exact tripleCoefficient_nonneg ..
end Bounds
theorem localFraction_error_tendsto (r : ℕ) :
    Tendsto (fun q : OddPrime => Real.sqrt (((r : ℝ)+1)/(q.val : ℝ))) primeInfinity (nhds 0) := by
  have h := ((tendsto_inv_atTop_zero (𝕜 := ℝ)).comp primeInfinity_real_tendsto).const_mul ((r : ℝ)+1)
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp h
  simpa only [mul_zero,Real.sqrt_zero,Function.comp_def,←div_eq_mul_inv] using hs
theorem pairError_tendsto (r : ℕ) (hr : 0<r) {ξ ζ : ℤ}
    (hξ : ξ=1 ∨ ξ= -1) (hζ : ζ=1 ∨ ζ= -1) :
    Tendsto (fun q : OddPrime => uniformMean (pairError (K := ZMod q.val) r ξ ζ)) primeInfinity (nhds 0) := by
  have hc := pairCoefficient_tendsto r hr hξ hζ
  have ha := ((hc.div_const 2).sub_const 2).abs
  have hb := hc.mul (localFraction_error_tendsto r)
  have h := ha.add hb
  norm_num only at h
  apply squeeze_zero (fun q => uniformMean_nonneg (pairError_nonneg r ξ ζ)) (fun q => ?_) h
  simpa only [ZMod.card] using pairError_mean (K := ZMod q.val)
    (by simpa only [ZMod.ringChar_zmod_n] using q.property.2) r hr hξ
theorem tripleError_tendsto (r : ℕ) (hr : 1<r) {ξ ζ θ : ℤ}
    (hξ : ξ=1 ∨ ξ= -1) (hζ : ζ=1 ∨ ζ= -1) (hθ : θ=1 ∨ θ= -1) :
    Tendsto (fun q : OddPrime => uniformMean (fun B => uniformMean
      (fun C => tripleError (K := ZMod q.val) r ξ ζ θ B C))) primeInfinity (nhds 0) := by
  have hc := tripleCoefficient_tendsto r (by omega) hξ hζ hθ
  have ha := ((hc.div_const 2).sub_const 8).abs
  have hb := hc.mul (localFraction_error_tendsto r)
  have h := ha.add hb
  norm_num only at h
  apply squeeze_zero (fun q => uniformMean_nonneg fun B => uniformMean_nonneg (tripleError_nonneg r ξ ζ θ B))
    (fun q => ?_) h
  simpa only [ZMod.card] using tripleError_mean (K := ZMod q.val)
    (by simpa only [ZMod.ringChar_zmod_n] using q.property.2) r hr hξ hζ hθ
end SidorenkoCounterexample
end
end OAI
namespace OAI
section
namespace SidorenkoCounterexample
open scoped BigOperators
open Module
section Gauss
variable {K V : Type*} [Field K] [Fintype K]
  [AddCommGroup V] [Module K V] [Fintype V]
end Gauss
section Fourier
variable {K ι : Type*} [Field K] [Fintype K] [Fintype ι] [DecidableEq ι] [DecidableEq K]
variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]
variable {V : Type*} [AddCommGroup V] [Module K V] [Fintype V]
end Fourier
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open scoped BigOperators
open Module
section SignMoments
variable {K ι : Type*} [Field K] [Fintype K] [DecidableEq K]
  [Fintype ι] [DecidableEq ι]
variable {V : Type*} [AddCommGroup V] [Module K V] [Fintype V]
end SignMoments
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module LinearMap
open scoped Matrix BigOperators
section Mom
variable {K ι : Type*} [Field K] [Fintype K] [DecidableEq K]
  [Fintype ι] [DecidableEq ι] [Nonempty ι] {N : ℕ}
end Mom
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module Classical
open scoped Matrix BigOperators
section Span
variable {K I : Type*} [Field K] [Fintype K] [DecidableEq K]
  [Fintype I] [DecidableEq I] {N : ℕ}
end Span
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module Classical
open scoped BigOperators
section Star
variable {K I J W : Type*} [Field K] [AddCommGroup W] [Module K W]
def starDifference (v : I) (k : J → I) : (I → W) →ₗ[K] (J → W) where
  toFun X j := X v-X (k j)
  map_add' X Y := by ext j; simp only [Pi.add_apply]; abel
  map_smul' c X := by ext j; simp only [Pi.smul_apply,RingHom.id_apply,smul_sub]
theorem starDifference_surjective (v : I) (k : J → I) (hk : Function.Injective k)
    (hv : ∀ j, k j≠v) : Function.Surjective (starDifference (K := K) (W := W) v k) := by
  intro M
  refine ⟨Function.extend k (fun j => -M j) (fun _ => 0),?_⟩
  ext j
  change Function.extend k (fun j => -M j) (fun _ => (0 : W)) v-
    Function.extend k (fun j => -M j) (fun _ => (0 : W)) (k j)=M j
  rw [hk.extend_apply,Function.extend_apply' _ _ v (by simpa using hv)]
  simp
variable [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype W]
include K in
theorem uniformMean_starDifference (v : I) (k : J → I) (hk : Function.Injective k)
    (hv : ∀ j, k j≠v) (f : (J → W) → ℝ) :
    uniformMean (fun X : I → W => f (fun j => X v-X (k j)))=uniformMean f :=
  uniformMean_surjective_linear (starDifference (K := K) v k)
    (starDifference_surjective v k hk hv) f
end Star
section Border
variable {K I : Type*} [Field K] [Fintype K] [DecidableEq K] [Fintype I] [DecidableEq I]
end Border
end SidorenkoCounterexample
end
end OAI
namespace OAI
section
namespace SidorenkoCounterexample
open Module Classical
open scoped BigOperators
section StarMoment
variable {K I J : Type*} [Field K] [Fintype K] [DecidableEq K]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Nonempty J] {N : ℕ}
end StarMoment
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module Classical
open scoped BigOperators
def pairLeft : Fin 33 → Fin 13 := ![0,0,2,0,2,0,1,2,3,1,4,1,3,3,4,1,9,4,8,1,7,10,8,7,8,5,5,5,6,6,6,6,5]
def pairRight : Fin 33 → Fin 13 := ![2,3,3,9,9,1,3,4,4,9,9,10,10,11,11,12,12,8,9,7,10,11,11,12,12,7,10,11,8,11,7,12,6]
theorem pair_endpoints_ne : ∀ e, pairLeft e≠pairRight e := by decide
section Signs
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] {D : ℕ}
noncomputable def pairSign (X : Fin 13 → SymMatrix K D) (e : Fin 33) : ℝ :=
  quadraticChar K (X (pairLeft e)-X (pairRight e)).val.det
end Signs
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module Classical Filter
open scoped BigOperators
section Moment
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] {N : ℕ}
end Moment
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Classical Filter
open scoped BigOperators
section Product
variable {I : Type*} [DecidableEq I]
omit [DecidableEq I] in
theorem abs_prod_le_pow (s : Finset I) (f : I → ℝ) {C : ℝ} (_hC : 0≤C)
    (hf : ∀ i∈s, |f i|≤C) : |∏ i∈s, f i|≤C^s.card := by
  rw [Finset.abs_prod,←Finset.prod_const]
  exact Finset.prod_le_prod (fun _ _ => abs_nonneg _) hf
theorem product_difference_bound (s : Finset I) (f g : I → ℝ) {C : ℝ} (hC : 1≤C)
    (hf : ∀ i∈s, |f i|≤C) (hg : ∀ i∈s, |g i|≤C) :
    |(∏ i∈s, f i)-(∏ i∈s, g i)| ≤ C^s.card * ∑ i∈s, |f i-g i| := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hC0 : 0≤C := le_trans (by norm_num) hC
    have hf' := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hg' := fun i hi => hg i (Finset.mem_insert_of_mem hi)
    specialize ih hf' hg'
    rw [Finset.prod_insert ha,Finset.prod_insert ha,Finset.card_insert_of_notMem ha,
      Finset.sum_insert ha,pow_succ]
    calc
      _ = |f a*((∏ i∈s, f i)-(∏ i∈s, g i)) + (f a-g a)*(∏ i∈s, g i)| := by congr 1; ring
      _ ≤ |f a*((∏ i∈s, f i)-(∏ i∈s, g i))| + |(f a-g a)*(∏ i∈s, g i)| := abs_add_le _ _
      _ = |f a| * |(∏ i∈s, f i)-(∏ i∈s, g i)| + |f a-g a| * |∏ i∈s, g i| := by simp only [abs_mul]
      _ ≤ C*(C^s.card*∑ i∈s, |f i-g i|) + |f a-g a| * C^s.card :=
        add_le_add (mul_le_mul (hf a (Finset.mem_insert_self ..)) ih (abs_nonneg _) hC0)
          (mul_le_mul_of_nonneg_left (abs_prod_le_pow s g hC0 hg') (abs_nonneg _))
      _ ≤ _ := by
        have h : |f a-g a| * C^s.card ≤ C*(|f a-g a| * C^s.card) :=
          le_mul_of_one_le_left (mul_nonneg (abs_nonneg _) (pow_nonneg hC0 _)) hC
        nlinarith
end Product
section Mean
variable {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A]
theorem uniformMean_pi_product (f : I → A → ℝ) :
    uniformMean (fun x : I → A => ∏ i, f i (x i))=∏ i, uniformMean (f i) := by
  unfold uniformMean
  rw [←Fintype.prod_sum,Finset.prod_div_distrib,Finset.prod_const,Finset.card_univ,
    Fintype.card_fun,Nat.cast_pow]
end Mean
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module Classical Filter
open scoped BigOperators
section Difference
variable {K I W : Type*} [Field K] [Fintype I] [DecidableEq I]
  [AddCommGroup W] [Module K W] [Fintype W]
include K in
theorem uniformMean_point_difference (i k : I) (hik : i≠k) (f : W → ℝ) :
    uniformMean (fun X : I → W => f (X i-X k))=uniformMean f := by
  let L : (I → W) →ₗ[K] W :=
    { toFun := fun X => X i-X k
      map_add' := by intros; simp only [Pi.add_apply]; abel
      map_smul' := by intros; simp only [Pi.smul_apply,smul_sub,RingHom.id_apply] }
  have hL : Function.Surjective L := by
    intro w
    refine ⟨Function.update 0 i w,?_⟩
    change (Function.update (0 : I → W) i w) i-(Function.update (0 : I → W) i w) k=w
    simp [Function.update_of_ne hik.symm]
  exact uniformMean_surjective_linear L hL f
end Difference
section Pair
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] {D : ℕ}
noncomputable def pairSingular (X : Fin 13 → SymMatrix K D) (e : Fin 33) : ℝ :=
  if (X (pairLeft e)-X (pairRight e)).val.det=0 then 1 else 0
omit [Fintype K] in
theorem pairSingular_nonneg (X : Fin 13 → SymMatrix K D) (e : Fin 33) : 0≤pairSingular X e := by
  unfold pairSingular; split <;> norm_num
theorem pairSingular_mean (e : Fin 33) :
    uniformMean (fun X : Fin 13 → SymMatrix K D => pairSingular X e)≤(D : ℝ)/Fintype.card K := by
  unfold pairSingular
  rw [uniformMean_point_difference (K := K) _ _ (pair_endpoints_ne e)
    (fun B : SymMatrix K D => if B.val.det=0 then 1 else 0)]
  exact symmetricSingularProb_bound D
def fullTransverse (X : Fin 13 → SymMatrix K D) : Prop :=
  ∀ e : Fin 33, (X (pairLeft e)-X (pairRight e)).val.det≠0
omit [Fintype K] in
theorem nonTransverse_pointwise (X : Fin 13 → SymMatrix K D) :
    (if fullTransverse X then 0 else 1 : ℝ) ≤ ∑ e, pairSingular X e := by
  by_cases h : fullTransverse X
  · rw [if_pos h]; exact Finset.sum_nonneg fun e _ => pairSingular_nonneg X e
  · rw [if_neg h]
    obtain ⟨e,he⟩ := not_forall.mp h
    have he := not_not.mp he
    calc
      (1 : ℝ) = pairSingular X e := by rw [pairSingular,if_pos he]
      _ ≤ _ := Finset.single_le_sum (fun e _ => pairSingular_nonneg X e) (Finset.mem_univ e)
theorem nonTransverse_mean :
    uniformMean (fun X : Fin 13 → SymMatrix K D => if fullTransverse X then 0 else 1) ≤
      33*((D : ℝ)/Fintype.card K) := by
  apply (uniformMean_mono nonTransverse_pointwise).trans
  rw [uniformMean_sum]
  calc
    _ ≤ ∑ _e : Fin 33, (D : ℝ)/Fintype.card K := Finset.sum_le_sum fun e _ => pairSingular_mean e
    _ = _ := by simp
noncomputable def pairBool (X : Fin 13 → SymMatrix K D) (e : Fin 33) : Bool :=
  decide (pairSign X e=1)
def boolSign (b : Bool) : ℝ := if b then 1 else -1
@[simp] theorem boolSign_abs (b : Bool) : |boolSign b|=1 := by cases b <;> norm_num [boolSign]
@[simp] theorem boolSign_sq (b : Bool) : boolSign b^2=1 := by cases b <;> norm_num [boolSign]
theorem pairBool_error (X : Fin 13 → SymMatrix K D) (e : Fin 33) :
    |boolSign (pairBool X e)-pairSign X e| ≤ pairSingular X e := by
  by_cases hz : (X (pairLeft e)-X (pairRight e)).val.det=0
  · have he : pairSign X e=0 := by unfold pairSign; rw [hz]; norm_num
    rw [pairSingular,if_pos hz,he]
    simp
  · have he : pairSign X e=1 ∨ pairSign X e= -1 := by
      unfold pairSign
      rcases quadraticChar_dichotomy (F := K) hz with h | h <;> rw [h] <;> norm_num
    rw [pairSingular,if_neg hz]
    rcases he with he | he <;> norm_num [pairBool,he,boolSign]
end Pair
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module Classical
open scoped BigOperators
section Graph
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
end Graph
end SidorenkoCounterexample
end
end OAI
namespace OAI
section
namespace SidorenkoCounterexample
open Module Classical Filter
open scoped BigOperators
section Mean
variable {A B : Type*} [Fintype A] [Fintype B] [Nonempty B]
end Mean
section Norm
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
end Norm
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module Classical Filter
open scoped BigOperators
section Face
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
noncomputable def faceLocal (r : ℕ) (T : Finset (Fin 3)) (ξ : Fin 3 → ℤ)
    (X : Fin 3 → SymMatrix K (2*r)) : ℝ :=
  uniformMean (fun Y => ∏ k∈T, rankKernel K (2*r) r (ξ k) (X k-Y))
@[simp] theorem faceLocal_empty (r : ℕ) (ξ : Fin 3 → ℤ) (X : Fin 3 → SymMatrix K (2*r)) :
    faceLocal r ∅ ξ X=1 := by simp [faceLocal,uniformMean_const]
theorem faceLocal_singleton (hK : ringChar K≠2) (r : ℕ) (hr : 0<r)
    (ξ : Fin 3 → ℤ) (hξ : ∀ k, ξ k=1 ∨ ξ k= -1) (X : Fin 3 → SymMatrix K (2*r)) (k : Fin 3) :
    faceLocal r {k} ξ X=1 := by
  simp only [faceLocal,Finset.prod_singleton]
  rw [uniformMean_subLeft,uniformMean_rankKernel _ _ hr (by omega) hK (hξ k)]
theorem faceLocal_pair (r : ℕ) (ξ : Fin 3 → ℤ) (X : Fin 3 → SymMatrix K (2*r))
    (k l : Fin 3) (hkl : k≠l) :
    faceLocal r {k,l} ξ X=pairLocal r (ξ k) (ξ l) (X k-X l) := by
  simp only [faceLocal,Finset.prod_pair hkl,pairLocal]
  have he (Y : SymMatrix K (2*r)) : X l-Y=(X k-Y)-(X k-X l) := by abel
  simp_rw [he]
  exact uniformMean_subLeft (X k) (fun A => rankKernel K (2*r) r (ξ k) A *
    rankKernel K (2*r) r (ξ l) (A-(X k-X l)))
theorem faceLocal_full (r : ℕ) (ξ : Fin 3 → ℤ) (X : Fin 3 → SymMatrix K (2*r)) :
    faceLocal r Finset.univ ξ X=tripleLocal r (ξ 0) (ξ 1) (ξ 2) (X 0-X 1) (X 0-X 2) := by
  simp only [faceLocal,Fin.prod_univ_three,tripleLocal]
  have h1 (Y : SymMatrix K (2*r)) : X 1-Y=(X 0-Y)-(X 0-X 1) := by abel
  have h2 (Y : SymMatrix K (2*r)) : X 2-Y=(X 0-Y)-(X 0-X 2) := by abel
  simp_rw [h1,h2]
  exact uniformMean_subLeft (X 0) (fun A => rankKernel K (2*r) r (ξ 0) A *
    rankKernel K (2*r) r (ξ 1) (A-(X 0-X 1))*rankKernel K (2*r) r (ξ 2) (A-(X 0-X 2)))
noncomputable def pairPolynomial (r : ℕ) (ξ ζ : ℤ) (B : SymMatrix K (2*r)) : ℝ :=
  1+(quadraticChar K ((-1 : K)^r) : ℝ)*(quadraticChar K B.val.det : ℝ)*(ξ : ℝ)*(ζ : ℝ)
theorem signs_polynomial (c x ξ ζ : ℤ) (hc : c=1 ∨ c= -1) (hx : x=1 ∨ x= -1)
    (hξ : ξ=1 ∨ ξ= -1) (hζ : ζ=1 ∨ ζ= -1) :
    (1+(c : ℝ)*(x : ℝ)*(ξ : ℝ)*(ζ : ℝ))=(if x=c*ξ*ζ then 2 else 0) := by
  rcases hc with rfl|rfl <;> rcases hx with rfl|rfl <;>
    rcases hξ with rfl|rfl <;> rcases hζ with rfl|rfl <;> norm_num
theorem pairPolynomial_eq (r : ℕ) {ξ ζ : ℤ} (hξ : ξ=1 ∨ ξ= -1) (hζ : ζ=1 ∨ ζ= -1)
    (B : SymMatrix K (2*r)) (hB : B.val.det≠0) :
    pairPolynomial r ξ ζ B=if pairMatch r ξ ζ B then 2 else 0 := by
  have he := signs_polynomial _ _ _ _ (quadraticChar_dichotomy (F := K) (pow_ne_zero r (neg_ne_zero.mpr one_ne_zero)))
    (quadraticChar_dichotomy hB) hξ hζ
  unfold pairPolynomial pairMatch
  split_ifs with hm
  · rw [if_pos hm] at he; exact he
  · rw [if_neg hm] at he; exact he
noncomputable def facePolynomial (r : ℕ) (T : Finset (Fin 3)) (ξ : Fin 3 → ℤ)
    (X : Fin 3 → SymMatrix K (2*r)) : ℝ :=
  (if 0∈T ∧ 1∈T then pairPolynomial r (ξ 0) (ξ 1) (X 0-X 1) else 1)*
  (if 0∈T ∧ 2∈T then pairPolynomial r (ξ 0) (ξ 2) (X 0-X 2) else 1)*
  (if 1∈T ∧ 2∈T then pairPolynomial r (ξ 1) (ξ 2) (X 1-X 2) else 1)
def faceTransverse (r : ℕ) (X : Fin 3 → SymMatrix K (2*r)) : Prop :=
  (X 0-X 1).val.det≠0 ∧ (X 0-X 2).val.det≠0 ∧ (X 1-X 2).val.det≠0
theorem facePolynomial_full (r : ℕ) (ξ : Fin 3 → ℤ) (hξ : ∀ k, ξ k=1 ∨ ξ k= -1)
    (X : Fin 3 → SymMatrix K (2*r)) (hX : faceTransverse r X) :
    facePolynomial r Finset.univ ξ X=
      if tripleMatch r (ξ 0) (ξ 1) (ξ 2) (X 0-X 1) (X 0-X 2) then 8 else 0 := by
  unfold facePolynomial
  simp only [Finset.mem_univ,and_self,ite_true]
  rw [pairPolynomial_eq r (hξ 0) (hξ 1) _ hX.1,
    pairPolynomial_eq r (hξ 0) (hξ 2) _ hX.2.1,pairPolynomial_eq r (hξ 1) (hξ 2) _ hX.2.2]
  have he : X 0-X 2-(X 0-X 1)=X 1-X 2 := by abel
  simp only [tripleMatch,he]
  split_ifs <;> norm_num <;> tauto
noncomputable def faceError (r : ℕ) (ξ : Fin 3 → ℤ) (X : Fin 3 → SymMatrix K (2*r)) : ℝ :=
  pairError r (ξ 0) (ξ 1) (X 0-X 1)+pairError r (ξ 0) (ξ 2) (X 0-X 2)+
    pairError r (ξ 1) (ξ 2) (X 1-X 2)+tripleError r (ξ 0) (ξ 1) (ξ 2) (X 0-X 1) (X 0-X 2)
theorem faceError_nonneg (r : ℕ) (ξ : Fin 3 → ℤ) (X : Fin 3 → SymMatrix K (2*r)) :
    0≤faceError r ξ X := by
  exact add_nonneg (add_nonneg (add_nonneg (pairError_nonneg ..) (pairError_nonneg ..))
    (pairError_nonneg ..)) (tripleError_nonneg ..)
theorem faceLocal_error (hK : ringChar K≠2) (r : ℕ) (hr : 0<r) (T : Finset (Fin 3))
    (ξ : Fin 3 → ℤ) (hξ : ∀ k, ξ k=1 ∨ ξ k= -1)
    (X : Fin 3 → SymMatrix K (2*r)) (hX : faceTransverse r X) :
    |faceLocal r T ξ X-facePolynomial r T ξ X|≤faceError r ξ X := by
  have he : X 0-X 2-(X 0-X 1)=X 1-X 2 := by abel
  have hfull : (X 0-X 1).val.det≠0 ∧ (X 0-X 2).val.det≠0 ∧
      (X 0-X 2-(X 0-X 1)).val.det≠0 := by simpa only [he,faceTransverse] using hX
  have n01 := pairError_nonneg r (ξ 0) (ξ 1) (X 0-X 1)
  have n02 := pairError_nonneg r (ξ 0) (ξ 2) (X 0-X 2)
  have n12 := pairError_nonneg r (ξ 1) (ξ 2) (X 1-X 2)
  have nt := tripleError_nonneg r (ξ 0) (ξ 1) (ξ 2) (X 0-X 1) (X 0-X 2)
  rcases fin3_subsets T with ht|ht|ht|ht|ht|ht|ht|ht
  · subst T; simpa [facePolynomial] using faceError_nonneg r ξ X
  · subst T; rw [faceLocal_singleton hK r hr ξ hξ]; simpa [facePolynomial] using faceError_nonneg r ξ X
  · subst T; rw [faceLocal_singleton hK r hr ξ hξ]; simpa [facePolynomial] using faceError_nonneg r ξ X
  · subst T; rw [faceLocal_singleton hK r hr ξ hξ]; simpa [facePolynomial] using faceError_nonneg r ξ X
  · subst T
    rw [faceLocal_pair r ξ X 0 1 (by decide)]
    simp [facePolynomial, show (2 : Fin 3)≠0 from by decide, show (2 : Fin 3)≠1 from by decide]
    rw [pairPolynomial_eq r (hξ 0) (hξ 1) _ hX.1]
    have hp : pairError r (ξ 0) (ξ 1) (X 0-X 1)=
        |pairLocal r (ξ 0) (ξ 1) (X 0-X 1)-(if pairMatch r (ξ 0) (ξ 1) (X 0-X 1) then 2 else 0)| := by
      rw [pairError,if_pos hX.1]
    unfold faceError; linarith
  · subst T
    rw [faceLocal_pair r ξ X 0 2 (by decide)]
    simp [facePolynomial, show (1 : Fin 3)≠0 from by decide, show (1 : Fin 3)≠2 from by decide]
    rw [pairPolynomial_eq r (hξ 0) (hξ 2) _ hX.2.1]
    have hp : pairError r (ξ 0) (ξ 2) (X 0-X 2)=
        |pairLocal r (ξ 0) (ξ 2) (X 0-X 2)-(if pairMatch r (ξ 0) (ξ 2) (X 0-X 2) then 2 else 0)| := by
      rw [pairError,if_pos hX.2.1]
    unfold faceError; linarith
  · subst T
    rw [faceLocal_pair r ξ X 1 2 (by decide)]
    simp [facePolynomial, show (0 : Fin 3)≠1 from by decide, show (0 : Fin 3)≠2 from by decide]
    rw [pairPolynomial_eq r (hξ 1) (hξ 2) _ hX.2.2]
    have hp : pairError r (ξ 1) (ξ 2) (X 1-X 2)=
        |pairLocal r (ξ 1) (ξ 2) (X 1-X 2)-(if pairMatch r (ξ 1) (ξ 2) (X 1-X 2) then 2 else 0)| := by
      rw [pairError,if_pos hX.2.2]
    unfold faceError; linarith
  · subst T
    rw [faceLocal_full,facePolynomial_full r ξ hξ X hX]
    have hp : tripleError r (ξ 0) (ξ 1) (ξ 2) (X 0-X 1) (X 0-X 2)=
        |tripleLocal r (ξ 0) (ξ 1) (ξ 2) (X 0-X 1) (X 0-X 2)-
          (if tripleMatch r (ξ 0) (ξ 1) (ξ 2) (X 0-X 1) (X 0-X 2) then 8 else 0)| := by
      rw [tripleError,if_pos hfull]
    unfold faceError; linarith
end Face
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Classical Filter
open scoped BigOperators
section Boolean
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {A : Type*} [Fintype A]
end Boolean
section Convergence
variable {I Q : Type*} [Fintype I] [DecidableEq I] {l : Filter Q}
  {A : Q → Type*} [∀ q, Fintype (A q)] [∀ q, Nonempty (A q)]
end Convergence
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module Classical Filter
open scoped BigOperators
section Means
variable {K I W : Type*} [Field K] [Fintype I] [DecidableEq I]
  [AddCommGroup W] [Module K W] [Fintype W]
include K in
theorem uniformMean_two_differences (v : Fin 3 → I) (hv : Function.Injective v) (f : W → W → ℝ) :
    uniformMean (fun X : I → W => f (X (v 0)-X (v 1)) (X (v 0)-X (v 2)))=
      uniformMean (fun B : W => uniformMean (f B)) := by
  let k : Fin 2 → I := fun j => v j.succ
  have hk : Function.Injective k := hv.comp (Fin.succ_injective 2)
  have hn : ∀ j, k j≠v 0 := fun j => hv.ne (Fin.succ_ne_zero j)
  have he := uniformMean_starDifference (K := K) (W := W) (v 0) k hk hn (fun M => f (M 0) (M 1))
  change uniformMean (fun X : I → W => f (X (v 0)-X (v 1)) (X (v 0)-X (v 2))) =
    uniformMean (fun M : Fin 2 → W => f (M 0) (M 1)) at he
  rw [he,←uniformMean_equiv (finTwoArrowEquiv W).symm,uniformMean_prod]
  rfl
end Means
section Bounds
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
noncomputable def faceBound (r : ℕ) (ξ : Fin 3 → ℤ) : ℝ := 1+
  pairCoefficient (K := K) r (ξ 0) (ξ 1)+pairCoefficient (K := K) r (ξ 0) (ξ 2)+
  pairCoefficient (K := K) r (ξ 1) (ξ 2)+tripleCoefficient (K := K) r (ξ 0) (ξ 1) (ξ 2)
theorem faceBound_one (r : ℕ) (ξ : Fin 3 → ℤ) : 1≤faceBound (K := K) r ξ := by
  have := pairCoefficient_nonneg (K := K) r (ξ 0) (ξ 1)
  have := pairCoefficient_nonneg (K := K) r (ξ 0) (ξ 2)
  have := pairCoefficient_nonneg (K := K) r (ξ 1) (ξ 2)
  have := tripleCoefficient_nonneg (K := K) r (ξ 0) (ξ 1) (ξ 2)
  unfold faceBound; linarith
theorem faceLocal_nonneg (r : ℕ) (T : Finset (Fin 3)) (ξ : Fin 3 → ℤ)
    (X : Fin 3 → SymMatrix K (2*r)) : 0≤faceLocal r T ξ X := by
  exact uniformMean_nonneg fun Y => Finset.prod_nonneg fun k _ => rankKernel_nonneg ..
theorem faceLocal_bound (hK : ringChar K≠2) (r : ℕ) (hr : 0<r)
    (T : Finset (Fin 3)) (ξ : Fin 3 → ℤ) (hξ : ∀ k, ξ k=1 ∨ ξ k= -1)
    (X : Fin 3 → SymMatrix K (2*r)) (hX : faceTransverse r X) :
    faceLocal r T ξ X≤faceBound (K := K) r ξ := by
  have he : X 0-X 2-(X 0-X 1)=X 1-X 2 := by abel
  have n01 := pairCoefficient_nonneg (K := K) r (ξ 0) (ξ 1)
  have n02 := pairCoefficient_nonneg (K := K) r (ξ 0) (ξ 2)
  have n12 := pairCoefficient_nonneg (K := K) r (ξ 1) (ξ 2)
  have nt := tripleCoefficient_nonneg (K := K) r (ξ 0) (ξ 1) (ξ 2)
  rcases fin3_subsets T with ht|ht|ht|ht|ht|ht|ht|ht
  · subst T; rw [faceLocal_empty]; exact faceBound_one r ξ
  · subst T; rw [faceLocal_singleton hK r hr ξ hξ]; exact faceBound_one r ξ
  · subst T; rw [faceLocal_singleton hK r hr ξ hξ]; exact faceBound_one r ξ
  · subst T; rw [faceLocal_singleton hK r hr ξ hξ]; exact faceBound_one r ξ
  · subst T; rw [faceLocal_pair r ξ X 0 1 (by decide)]
    exact (pairLocal_bound r (ξ 0) (ξ 1) _ hX.1).trans (by unfold faceBound; linarith)
  · subst T; rw [faceLocal_pair r ξ X 0 2 (by decide)]
    exact (pairLocal_bound r (ξ 0) (ξ 2) _ hX.2.1).trans (by unfold faceBound; linarith)
  · subst T; rw [faceLocal_pair r ξ X 1 2 (by decide)]
    exact (pairLocal_bound r (ξ 1) (ξ 2) _ hX.2.2).trans (by unfold faceBound; linarith)
  · subst T; rw [faceLocal_full]
    exact (tripleLocal_bound hK r (hξ 0) (hξ 1) (hξ 2) _ _ hX.1 hX.2.1 (by rw [he]; exact hX.2.2)).trans
      (by unfold faceBound; linarith)
theorem pairPolynomial_abs_le (r : ℕ) {ξ ζ : ℤ} (hξ : ξ=1 ∨ ξ= -1) (hζ : ζ=1 ∨ ζ= -1)
    (B : SymMatrix K (2*r)) : |pairPolynomial r ξ ζ B|≤2 := by
  by_cases hb : B.val.det=0
  · unfold pairPolynomial; rw [hb]; norm_num
  · rw [pairPolynomial_eq r hξ hζ B hb]; split <;> norm_num
theorem facePolynomial_abs_le (r : ℕ) (T : Finset (Fin 3)) (ξ : Fin 3 → ℤ)
    (hξ : ∀ k, ξ k=1 ∨ ξ k= -1) (X : Fin 3 → SymMatrix K (2*r)) :
    |facePolynomial r T ξ X|≤8 := by
  have hpair (k l : Fin 3) : |if k∈T ∧ l∈T then pairPolynomial r (ξ k) (ξ l) (X k-X l) else 1|≤2 := by
    split
    · exact pairPolynomial_abs_le r (hξ k) (hξ l) _
    · norm_num
  unfold facePolynomial
  rw [abs_mul,abs_mul]
  have ha := mul_le_mul (hpair 0 1) (hpair 0 2) (abs_nonneg _) (by norm_num : (0:ℝ)≤2)
  have hb := mul_le_mul ha (hpair 1 2) (abs_nonneg _) (by norm_num : (0:ℝ)≤2*2)
  norm_num only at hb
  exact hb
end Bounds
theorem faceBound_tendsto (r : ℕ) (hr : 0<r) (ξ : Fin 3 → ℤ) (hξ : ∀ k, ξ k=1 ∨ ξ k= -1) :
    Tendsto (fun q : OddPrime => faceBound (K := ZMod q.val) r ξ) primeInfinity (nhds 29) := by
  have h01 := pairCoefficient_tendsto r hr (hξ 0) (hξ 1)
  have h02 := pairCoefficient_tendsto r hr (hξ 0) (hξ 2)
  have h12 := pairCoefficient_tendsto r hr (hξ 1) (hξ 2)
  have ht := tripleCoefficient_tendsto r hr (hξ 0) (hξ 1) (hξ 2)
  simpa only [faceBound,show (1:ℝ)+4+4+4+16=29 by norm_num] using
    (((h01.const_add 1).add h02).add h12).add ht
theorem faceError_mean_tendsto (r : ℕ) (hr : 1<r) (ξ : Fin 3 → ℤ) (hξ : ∀ k, ξ k=1 ∨ ξ k= -1)
    (v : Fin 3 → Fin 13) (hv : Function.Injective v) :
    Tendsto (fun q : OddPrime => uniformMean (fun X : Fin 13 → SymMatrix (ZMod q.val) (2*r) =>
      faceError r ξ (X ∘ v))) primeInfinity (nhds 0) := by
  have he (q : OddPrime) : uniformMean (fun X : Fin 13 → SymMatrix (ZMod q.val) (2*r) =>
      faceError r ξ (X ∘ v)) = uniformMean (pairError (K := ZMod q.val) r (ξ 0) (ξ 1))+
        uniformMean (pairError (K := ZMod q.val) r (ξ 0) (ξ 2))+
        uniformMean (pairError (K := ZMod q.val) r (ξ 1) (ξ 2))+
        uniformMean (fun B => uniformMean (fun C => tripleError (K := ZMod q.val) r (ξ 0) (ξ 1) (ξ 2) B C)) := by
    simp only [faceError,Function.comp_def,uniformMean_add]
    rw [uniformMean_point_difference (K := ZMod q.val) _ _ (hv.ne (by decide)) (pairError r (ξ 0) (ξ 1)),
      uniformMean_point_difference (K := ZMod q.val) _ _ (hv.ne (by decide)) (pairError r (ξ 0) (ξ 2)),
      uniformMean_point_difference (K := ZMod q.val) _ _ (hv.ne (by decide)) (pairError r (ξ 1) (ξ 2)),
      uniformMean_two_differences (K := ZMod q.val) v hv (tripleError r (ξ 0) (ξ 1) (ξ 2))]
  simp only [he]
  have h := (((pairError_tendsto r (by omega) (hξ 0) (hξ 1)).add
    (pairError_tendsto r (by omega) (hξ 0) (hξ 2))).add
    (pairError_tendsto r (by omega) (hξ 1) (hξ 2))).add
    (tripleError_tendsto r hr (hξ 0) (hξ 1) (hξ 2))
  simpa only [add_zero] using h
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module Classical
open scoped BigOperators
section ChartFace
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
instance canonicalDual_finite (D : ℕ) : Finite (Module.Dual K (Fin D → K)) :=
  Finite.of_injective (fun f : Module.Dual K (Fin D → K) => (f : (Fin D → K) → K)) DFunLike.coe_injective
end ChartFace
end SidorenkoCounterexample
end
end OAI
namespace OAI
section
namespace SidorenkoCounterexample
open Module Classical Filter
open scoped BigOperators
def slotLeft : Fin 3 → Fin 3 := ![0,0,1]
def slotRight : Fin 3 → Fin 3 := ![1,2,2]
theorem facePair_endpoints : ∀ j k,
    pairLeft (facePair j k)=faceVertex j (slotLeft k) ∧
    pairRight (facePair j k)=faceVertex j (slotRight k) := by decide
theorem fullTransverse_face {K : Type*} [Field K] {r : ℕ} (X : Fin 13 → SymMatrix K (2*r))
    (hX : fullTransverse X) (j : Fin 22) : faceTransverse r (X ∘ faceVertex j) := by
  have h (k : Fin 3) := hX (facePair j k)
  simp only [(facePair_endpoints j _).1,(facePair_endpoints j _).2] at h
  exact ⟨h 0,h 1,h 2⟩
noncomputable def boolFacePolynomial (c : ℝ) (T : Finset (Fin 3)) (ξ : Fin 3 → ℤ)
    (j : Fin 22) (η : Fin 33 → Bool) : ℝ :=
  ∏ k : Fin 3, if slotLeft k∈T ∧ slotRight k∈T then
    1+c*boolSign (η (facePair j k))*(ξ (slotLeft k) : ℝ)*(ξ (slotRight k) : ℝ) else 1
section FaceGraph
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
theorem pairBool_eq_sign {D : ℕ} (X : Fin 13 → SymMatrix K D) (hX : fullTransverse X) (e : Fin 33) :
    boolSign (pairBool X e)=pairSign X e := by
  have h := pairBool_error X e
  rw [pairSingular,if_neg (hX e)] at h
  exact sub_eq_zero.mp (abs_nonpos_iff.mp h)
theorem facePolynomial_bool (r : ℕ) (T : Finset (Fin 3)) (ξ : Fin 3 → ℤ)
    (X : Fin 13 → SymMatrix K (2*r)) (hX : fullTransverse X) (j : Fin 22) :
    facePolynomial r T ξ (X ∘ faceVertex j)=
      boolFacePolynomial (quadraticChar K ((-1 : K)^r)) T ξ j (pairBool X) := by
  unfold boolFacePolynomial
  simp_rw [pairBool_eq_sign X hX,pairSign,(facePair_endpoints j _).1,(facePair_endpoints j _).2]
  simp only [Fin.prod_univ_three,slotLeft,slotRight,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,facePolynomial,pairPolynomial,Function.comp_def]
  rfl
end FaceGraph
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module Classical Filter
open scoped BigOperators
section Global
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
noncomputable def configurationProduct (r : ℕ) (T : Fin 22 → Finset (Fin 3))
    (ξ : Fin 22 → Fin 3 → ℤ) (X : Fin 13 → SymMatrix K (2*r)) : ℝ :=
  ∏ j,faceLocal r (T j) (ξ j) (X ∘ faceVertex j)
theorem configurationProduct_nonneg (r : ℕ) (T : Fin 22 → Finset (Fin 3))
    (ξ : Fin 22 → Fin 3 → ℤ) (X : Fin 13 → SymMatrix K (2*r)) :
    0≤configurationProduct r T ξ X := Finset.prod_nonneg (fun _ _ => faceLocal_nonneg ..)
noncomputable def matrixSingularTail (r : ℕ) (T : Fin 22 → Finset (Fin 3))
    (ξ : Fin 22 → Fin 3 → ℤ) : ℝ :=
  uniformMean fun X : Fin 13 → SymMatrix K (2*r) =>
    if fullTransverse X then 0 else configurationProduct r T ξ X
end Global
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module Classical Filter
open scoped BigOperators
section GlobalProduct
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
noncomputable def configurationPolynomial (r : ℕ) (T : Fin 22 → Finset (Fin 3))
    (ξ : Fin 22 → Fin 3 → ℤ) (X : Fin 13 → SymMatrix K (2*r)) : ℝ :=
  ∏ j,facePolynomial r (T j) (ξ j) (X ∘ faceVertex j)
noncomputable def globalBound (r : ℕ) (ξ : Fin 22 → Fin 3 → ℤ) : ℝ :=
  8+∑ j,faceBound (K := K) r (ξ j)
theorem globalBound_eight (r : ℕ) (ξ : Fin 22 → Fin 3 → ℤ) : 8≤globalBound (K := K) r ξ := by
  have h := Finset.sum_nonneg (s := (Finset.univ : Finset (Fin 22)))
    (fun j _ => le_trans (by norm_num : (0:ℝ)≤1) (faceBound_one (K := K) r (ξ j)))
  unfold globalBound; linarith
theorem faceBound_le_global (r : ℕ) (ξ : Fin 22 → Fin 3 → ℤ) (j : Fin 22) :
    faceBound (K := K) r (ξ j)≤globalBound (K := K) r ξ := by
  have h := Finset.single_le_sum (s := (Finset.univ : Finset (Fin 22)))
    (fun k _ => le_trans (by norm_num : (0:ℝ)≤1) (faceBound_one (K := K) r (ξ k))) (Finset.mem_univ j)
  unfold globalBound; linarith
theorem configuration_difference_bound (hK : ringChar K≠2) (r : ℕ) (hr : 0<r)
    (T : Fin 22 → Finset (Fin 3)) (ξ : Fin 22 → Fin 3 → ℤ)
    (hξ : ∀ j i,ξ j i=1 ∨ ξ j i= -1) (X : Fin 13 → SymMatrix K (2*r)) (hX : fullTransverse X) :
    |configurationProduct r T ξ X-configurationPolynomial r T ξ X|≤
      globalBound (K := K) r ξ^22*∑ j,faceError r (ξ j) (X ∘ faceVertex j) := by
  have hC := globalBound_eight (K := K) r ξ
  have h := product_difference_bound Finset.univ
    (fun j => faceLocal r (T j) (ξ j) (X ∘ faceVertex j))
    (fun j => facePolynomial r (T j) (ξ j) (X ∘ faceVertex j)) (by linarith : 1≤globalBound (K := K) r ξ)
    (fun j _ => by
      rw [abs_of_nonneg (faceLocal_nonneg ..)]
      exact (faceLocal_bound hK r hr (T j) (ξ j) (hξ j) _ (fullTransverse_face X hX j)).trans (faceBound_le_global r ξ j))
    (fun j _ => (facePolynomial_abs_le r (T j) (ξ j) (hξ j) _).trans hC)
  simp only [Finset.card_univ,Fintype.card_fin] at h
  exact h.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ =>
    faceLocal_error hK r hr (T j) (ξ j) (hξ j) _ (fullTransverse_face X hX j))) (by positivity))
noncomputable def transverseDifference (r : ℕ) (T : Fin 22 → Finset (Fin 3))
    (ξ : Fin 22 → Fin 3 → ℤ) : ℝ :=
  uniformMean fun X : Fin 13 → SymMatrix K (2*r) =>
    if fullTransverse X then configurationProduct r T ξ X-configurationPolynomial r T ξ X else 0
theorem transverseDifference_bound (hK : ringChar K≠2) (r : ℕ) (hr : 0<r)
    (T : Fin 22 → Finset (Fin 3)) (ξ : Fin 22 → Fin 3 → ℤ)
    (hξ : ∀ j i,ξ j i=1 ∨ ξ j i= -1) :
    |transverseDifference (K := K) r T ξ|≤globalBound (K := K) r ξ^22*
      ∑ j,uniformMean (fun X : Fin 13 → SymMatrix K (2*r) => faceError r (ξ j) (X ∘ faceVertex j)) := by
  calc
    _ ≤ uniformMean (fun X : Fin 13 → SymMatrix K (2*r) =>
      |if fullTransverse X then configurationProduct r T ξ X-configurationPolynomial r T ξ X else 0|) := abs_uniformMean_le _
    _ ≤ uniformMean (fun X : Fin 13 → SymMatrix K (2*r) =>
        globalBound (K := K) r ξ^22*∑ j,faceError r (ξ j) (X ∘ faceVertex j)) := by
      apply uniformMean_mono; intro X
      split_ifs with hX
      · exact configuration_difference_bound hK r hr T ξ hξ X hX
      · rw [abs_zero]; exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun j _ => faceError_nonneg ..))
    _ = _ := by rw [uniformMean_mul,uniformMean_sum]
end GlobalProduct
theorem globalBound_tendsto (r : ℕ) (hr : 0<r) (ξ : Fin 22 → Fin 3 → ℤ)
    (hξ : ∀ j i,ξ j i=1 ∨ ξ j i= -1) : Tendsto
    (fun q : OddPrime => globalBound (K := ZMod q.val) r ξ) primeInfinity (nhds 646) := by
  have hs := (tendsto_finsetSum Finset.univ (fun j _ => faceBound_tendsto r hr (ξ j) (hξ j))).const_add 8
  norm_num only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hs
  exact hs
theorem transverseDifference_tendsto (r : ℕ) (hr : 1<r)
    (T : Fin 22 → Finset (Fin 3)) (ξ : Fin 22 → Fin 3 → ℤ)
    (hξ : ∀ j i,ξ j i=1 ∨ ξ j i= -1) : Tendsto
    (fun q : OddPrime => transverseDifference (K := ZMod q.val) r T ξ) primeInfinity (nhds 0) := by
  have he := tendsto_finsetSum Finset.univ (fun j _ =>
    faceError_mean_tendsto r hr (ξ j) (hξ j) (faceVertex j) (faceVertex_injective j))
  simp only [Finset.sum_const_zero] at he
  have ht := ((globalBound_tendsto r (by omega) ξ hξ).pow 22).mul he
  simp only [mul_zero] at ht
  apply squeeze_zero_norm (fun q => ?_) ht
  rw [Real.norm_eq_abs]
  exact transverseDifference_bound (by simpa only [ZMod.ringChar_zmod_n] using q.property.2) r (by omega) T ξ hξ
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module Classical Filter
open scoped BigOperators
noncomputable def boolConfiguration (c : ℝ) (T : Fin 22 → Finset (Fin 3))
    (ξ : Fin 22 → Fin 3 → ℤ) (η : Fin 33 → Bool) : ℝ :=
  ∏ j,boolFacePolynomial c (T j) (ξ j) j η
theorem boolFacePolynomial_abs_le (c : ℝ) (hc : |c|≤1) (T : Finset (Fin 3))
    (ξ : Fin 3 → ℤ) (hξ : ∀ i,ξ i=1 ∨ ξ i= -1) (j : Fin 22) (η : Fin 33 → Bool) :
    |boolFacePolynomial c T ξ j η|≤8 := by
  have hs (i) : |(ξ i : ℝ)|=1 := by rcases hξ i with h|h <;> simp [h]
  have h := abs_prod_le_pow Finset.univ
    (fun k : Fin 3 => if slotLeft k∈T ∧ slotRight k∈T then
      1+c*boolSign (η (facePair j k))*(ξ (slotLeft k) : ℝ)*(ξ (slotRight k) : ℝ) else 1)
    (by norm_num : (0:ℝ)≤2) (fun k _ => by
      split_ifs
      · calc
          _ ≤ |(1:ℝ)|+|c*boolSign (η (facePair j k))*(ξ (slotLeft k) : ℝ)*(ξ (slotRight k) : ℝ)| := abs_add_le _ _
          _ ≤ 2 := by simp only [abs_one,abs_mul,boolSign_abs,hs,mul_one]; linarith
      · norm_num)
  norm_num only [Finset.card_univ,Fintype.card_fin,show (2:ℝ)^3=8 by norm_num] at h
  exact h
theorem boolConfiguration_abs_le (c : ℝ) (hc : |c|≤1) (T : Fin 22 → Finset (Fin 3))
    (ξ : Fin 22 → Fin 3 → ℤ) (hξ : ∀ j i,ξ j i=1 ∨ ξ j i= -1) (η : Fin 33 → Bool) :
    |boolConfiguration c T ξ η|≤8^22 := by
  simpa only [boolConfiguration,Finset.card_univ,Fintype.card_fin] using
    abs_prod_le_pow Finset.univ (fun j => boolFacePolynomial c (T j) (ξ j) j η)
      (by norm_num : (0:ℝ)≤8) (fun j _ => boolFacePolynomial_abs_le c hc (T j) (ξ j) (hξ j) j η)
section GlobalBool
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
theorem configurationPolynomial_bool (r : ℕ) (T : Fin 22 → Finset (Fin 3))
    (ξ : Fin 22 → Fin 3 → ℤ) (X : Fin 13 → SymMatrix K (2*r)) (hX : fullTransverse X) :
    configurationPolynomial r T ξ X=
      boolConfiguration (quadraticChar K ((-1:K)^r)) T ξ (pairBool X) := by
  apply Finset.prod_congr rfl
  intro j _
  exact facePolynomial_bool r (T j) (ξ j) X hX j
noncomputable def boolSingular (r : ℕ) (T : Fin 22 → Finset (Fin 3))
    (ξ : Fin 22 → Fin 3 → ℤ) : ℝ :=
  uniformMean fun X : Fin 13 → SymMatrix K (2*r) => if fullTransverse X then 0 else
    boolConfiguration (quadraticChar K ((-1:K)^r)) T ξ (pairBool X)
theorem boolSingular_bound (r : ℕ) (T : Fin 22 → Finset (Fin 3))
    (ξ : Fin 22 → Fin 3 → ℤ) (hξ : ∀ j i,ξ j i=1 ∨ ξ j i= -1) :
    |boolSingular (K := K) r T ξ|≤8^22*(33*((2*r : ℕ):ℝ)/Fintype.card K) := by
  have hc : |(quadraticChar K ((-1:K)^r) : ℝ)|≤1 := by
    rcases quadraticChar_dichotomy (F := K) (pow_ne_zero r (neg_ne_zero.mpr one_ne_zero)) with h|h <;> simp [h]
  calc
    _ ≤ uniformMean (fun X : Fin 13 → SymMatrix K (2*r) =>
      |if fullTransverse X then 0 else boolConfiguration (quadraticChar K ((-1:K)^r)) T ξ (pairBool X)|) := abs_uniformMean_le _
    _ ≤ uniformMean (fun X : Fin 13 → SymMatrix K (2*r) =>
      8^22*(if fullTransverse X then 0 else 1)) := by
      apply uniformMean_mono; intro X; split_ifs
      · norm_num
      · simpa only [mul_one] using boolConfiguration_abs_le _ hc T ξ hξ (pairBool X)
    _ = 8^22*uniformMean (fun X : Fin 13 → SymMatrix K (2*r) => if fullTransverse X then 0 else 1) := uniformMean_mul _ _
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left (nonTransverse_mean (K := K) (D := 2*r)) (by positivity : (0:ℝ)≤8^22)
      simpa only [mul_div_assoc] using h
theorem configuration_mean_identity (r : ℕ) (T : Fin 22 → Finset (Fin 3))
    (ξ : Fin 22 → Fin 3 → ℤ) :
    uniformMean (configurationProduct (K := K) r T ξ)-uniformMean
      (fun X : Fin 13 → SymMatrix K (2*r) => boolConfiguration (quadraticChar K ((-1:K)^r)) T ξ (pairBool X)) =
      transverseDifference (K := K) r T ξ+matrixSingularTail (K := K) r T ξ-boolSingular (K := K) r T ξ := by
  rw [←uniformMean_sub]
  unfold transverseDifference matrixSingularTail boolSingular
  rw [←uniformMean_add,←uniformMean_sub]
  apply uniformMean_congr
  intro X
  by_cases hx : fullTransverse X
  · simp only [hx,ite_true,add_zero,sub_zero,configurationPolynomial_bool r T ξ X hx]
  · simp only [hx,ite_false,zero_add]
end GlobalBool
theorem boolSingular_tendsto (r : ℕ) (T : Fin 22 → Finset (Fin 3))
    (ξ : Fin 22 → Fin 3 → ℤ) (hξ : ∀ j i,ξ j i=1 ∨ ξ j i= -1) : Tendsto
    (fun q : OddPrime => boolSingular (K := ZMod q.val) r T ξ) primeInfinity (nhds 0) := by
  have hd : Tendsto (fun q : OddPrime => (33*((2*r : ℕ):ℝ))/(q.val:ℝ)) primeInfinity (nhds 0) :=
    tendsto_const_nhds.div_atTop primeInfinity_real_tendsto
  have ht := hd.const_mul (8^22 : ℝ)
  simp only [mul_zero] at ht
  apply squeeze_zero_norm (fun q => ?_) ht
  rw [Real.norm_eq_abs]
  simpa only [ZMod.card] using boolSingular_bound (K := ZMod q.val) r T ξ hξ
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
structure FiniteLaw (A : Type*) [Fintype A] where
  weight : A → ℝ
  nonneg : ∀ a,0≤weight a
  total : ∑ a,weight a=1
namespace FiniteLaw
variable {A B C I : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype I] [DecidableEq I]
noncomputable def mean (p : FiniteLaw A) (f : A → ℝ) : ℝ := ∑ a,p.weight a*f a
@[simp] theorem mean_const (p : FiniteLaw A) (c : ℝ) : p.mean (fun _ => c)=c := by
  rw [mean,←Finset.sum_mul,p.total,one_mul]
noncomputable def prod (p : FiniteLaw A) (q : FiniteLaw B) : FiniteLaw (A × B) where
  weight x := p.weight x.1*q.weight x.2
  nonneg _ := mul_nonneg (p.nonneg _) (q.nonneg _)
  total := by rw [Fintype.sum_prod_type]; simp_rw [←Finset.mul_sum,q.total,mul_one]; exact p.total
@[simp] theorem mean_prod (p : FiniteLaw A) (q : FiniteLaw B) (f : A × B → ℝ) :
    (p.prod q).mean f=p.mean (fun a => q.mean (fun b => f (a,b))) := by
  unfold mean prod; rw [Fintype.sum_prod_type]; simp_rw [Finset.mul_sum,mul_assoc]
noncomputable def independent (p : I → FiniteLaw A) : FiniteLaw (I → A) where
  weight x := ∏ i,(p i).weight (x i)
  nonneg x := Finset.prod_nonneg (fun i _ => (p i).nonneg (x i))
  total := by rw [←Fintype.prod_sum]; simp only [(p _).total,Finset.prod_const_one]
noncomputable def map (p : FiniteLaw A) (f : A → B) : FiniteLaw B where
  weight b := ∑ a,if f a=b then p.weight a else 0
  nonneg b := Finset.sum_nonneg (fun a _ => by split <;> simp only [p.nonneg,le_refl])
  total := by rw [Finset.sum_comm]; simpa using p.total
end FiniteLaw
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Classical
open scoped BigOperators symmDiff
section BooleanMoments
variable {K : Type*} [Fintype K] [DecidableEq K]
end BooleanMoments
end SidorenkoCounterexample
end
end OAI
namespace OAI
section
namespace SidorenkoCounterexample
open Classical
open scoped BigOperators symmDiff
abbrev ActCorner := Fin 22 × Fin 3
def cornerPoint (k : ActCorner) : Fin 13 := faceVertex k.1 k.2
end SidorenkoCounterexample
end
end OAI
namespace OAI
section
namespace SidorenkoCounterexample
open Classical
open scoped BigOperators symmDiff
section Coefficients
variable {K : Type*} [Fintype K] [DecidableEq K]
end Coefficients
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
variable {K : Type*} [Fintype K] [DecidableEq K]
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
section
variable {I L A : Type*} [Fintype I] [DecidableEq I] [Fintype L] [Fintype A]
end
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
variable {K : Type*} [Fintype K] [DecidableEq K]
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
section Expansion
variable {K : Type*} [Fintype K] [DecidableEq K]
end Expansion
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
section Fubini
variable {I J K A B : Type*} [Fintype I] [Fintype J] [Fintype K] [Fintype A] [Fintype B] [DecidableEq I] [DecidableEq J] [DecidableEq K]
end Fubini
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module Classical Filter
open scoped BigOperators
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module Classical Filter
open scoped BigOperators
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Filter
instance primeInfinity_neBot : NeBot primeInfinity := by
  apply Filter.comap_neBot
  intro s hs
  obtain ⟨N,hN⟩ := Filter.mem_atTop_sets.mp hs
  obtain ⟨q,hq,hprime⟩ := Nat.exists_infinite_primes (max N 3)
  refine ⟨⟨q,hprime,by omega⟩,hN q (by omega)⟩
end SidorenkoCounterexample
end
end OAI
namespace OAI
section
namespace SidorenkoCounterexample
open Classical Filter
open scoped BigOperators
section MatrixActivation
variable {F K : Type*} [Field F] [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
end MatrixActivation
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
section Types
variable {K : Type*} [Fintype K] [DecidableEq K]
end Types
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
section Typed
variable {A B K : Type*} [Fintype A] [Fintype B] [Fintype K] [DecidableEq K]
end Typed
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
section Kernel
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
noncomputable def kernelMean (π : FiniteLaw X) (ν : FiniteLaw Y) (W : X → Y → ℝ) : ℝ :=
  π.mean (fun x => ν.mean (W x))
noncomputable def bipartiteMoment (π : FiniteLaw X) (ν : FiniteLaw Y) (W : X → Y → ℝ) : ℝ :=
  (FiniteLaw.independent (fun _ : Fin 13 => π)).mean (fun x =>
    (FiniteLaw.independent (fun _ : Fin 22 => ν)).mean (fun y =>
      ∏ k : ActCorner,W (x (cornerPoint k)) (y k.1)))
end Kernel
namespace FiniteLaw
end FiniteLaw
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
section MatrixMean
variable {F K : Type*} [Field F] [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
end MatrixMean
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Classical Filter
open scoped BigOperators
section TypedMatrix
variable {A B K F : Type*} [Fintype A] [Fintype B] [Fintype K] [DecidableEq K]
  [Field F] [Fintype F] [DecidableEq F]
end TypedMatrix
end SidorenkoCounterexample
end
end OAI
namespace OAI
section
namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
namespace FiniteLaw
variable {A I : Type*} [Fintype A] [Fintype I] [DecidableEq I]
end FiniteLaw
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Classical Filter
open scoped BigOperators Topology
section Dilution
variable {A B K : Type*} [Fintype A] [Fintype B] [Fintype K] [DecidableEq K]
end Dilution
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
section PinningRound
variable {I J E C : Type*} [Fintype I] [Fintype J] [Fintype E] [Fintype C]
  [DecidableEq I] [DecidableEq J] [DecidableEq C]
end PinningRound
end SidorenkoCounterexample
end
end OAI
namespace OAI
section
namespace SidorenkoCounterexample
open scoped BigOperators
end SidorenkoCounterexample
end
end OAI
namespace OAI
section
namespace SidorenkoCounterexample
open scoped BigOperators
end SidorenkoCounterexample
end
end OAI
namespace OAI
section
namespace SidorenkoCounterexample
open scoped BigOperators
end SidorenkoCounterexample
end
end OAI
namespace OAI
section
namespace SidorenkoCounterexample
open scoped BigOperators
end SidorenkoCounterexample
end
end OAI
namespace OAI
section
namespace SidorenkoCounterexample
open scoped BigOperators
end SidorenkoCounterexample
end
end OAI
namespace OAI
section
namespace SidorenkoCounterexample
open scoped BigOperators
end SidorenkoCounterexample
end
end OAI
namespace OAI
section
namespace SidorenkoCounterexample
open scoped BigOperators
end SidorenkoCounterexample
end
end OAI
namespace OAI
section
namespace SidorenkoCounterexample
open scoped BigOperators
end SidorenkoCounterexample
end
end OAI
namespace OAI
section
namespace SidorenkoCounterexample
open scoped BigOperators
end SidorenkoCounterexample
end
end OAI
namespace OAI
section
namespace SidorenkoCounterexample
open Classical Filter
open scoped BigOperators Topology
section Mix
variable {A : Type*} [Fintype A]
end Mix
section Pin
variable {I J E C : Type*} [Fintype I] [Fintype J] [Fintype E] [Fintype C]
  [DecidableEq I] [DecidableEq J] [DecidableEq C]
end Pin
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Classical Filter
open scoped BigOperators Topology
section Weights
variable {A I : Type*} [Fintype A] [Nonempty A] [Fintype I]
end Weights
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
section Gibbs
variable {I J E : Type*} [Fintype I] [Fintype J] [Fintype E] [Nonempty I] [Nonempty J]
end Gibbs
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
end SidorenkoCounterexample
end
end OAI
namespace OAI
section
namespace SidorenkoCounterexample
open Classical Filter
open scoped BigOperators
structure OrientedKernel where
  X : Type
  Y : Type
  [finiteX : Fintype X]
  [finiteY : Fintype Y]
  [nonemptyX : Nonempty X]
  [nonemptyY : Nonempty Y]
  left : FiniteLaw X
  right : FiniteLaw Y
  value : X → Y → ℝ
  nonneg : ∀ x y,0≤value x y
  mean_one : kernelMean left right value=1
  gap : bipartiteMoment left right value*bipartiteMoment right left (fun y x => value x y)<1
instance (W : OrientedKernel) : Fintype W.X := W.finiteX
instance (W : OrientedKernel) : Fintype W.Y := W.finiteY
instance (W : OrientedKernel) : Nonempty W.X := W.nonemptyX
instance (W : OrientedKernel) : Nonempty W.Y := W.nonemptyY
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
section Cross
variable {A B C D X Y : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype X] [Fintype Y]
end Cross
structure SymmetricCounterKernel where
  Ω : Type
  [finite : Fintype Ω]
  [nonempty : Nonempty Ω]
  law : FiniteLaw Ω
  value : Ω → Ω → ℝ
  nonneg : ∀ x y,0≤value x y
  le_one : ∀ x y,value x y≤1
  symm : ∀ x y,value x y=value y x
  mean_pos : 0<kernelMean law law value
  gap : bipartiteMoment law law value<(kernelMean law law value)^66
instance (W : SymmetricCounterKernel) : Fintype W.Ω := W.finite
instance (W : SymmetricCounterKernel) : Nonempty W.Ω := W.nonempty
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
namespace FiniteLaw
section Marginal
variable {I J A B : Type*} [Fintype I] [Fintype J] [Fintype A] [Fintype B] [DecidableEq I] [DecidableEq J]
end Marginal
end FiniteLaw
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Classical
open scoped BigOperators
end SidorenkoCounterexample
end
end OAI
open OAI.SidorenkoCounterexample Filter
open scoped Classical
namespace LeafA
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
noncomputable def mass (D r : ℕ) : ℝ := uniformMean (fun Z : SymMatrix K D => if Z.val.rank = r then (1:ℝ) else 0)
lemma mass_eq (D r : ℕ) : mass (K:=K) D r = layerMass K D r 1 + layerMass K D r (-1) := by
  have h (s : ℤ) : uniformMean (fun Z : SymMatrix K D => if Z ∈ signedLayer K D r s then (1:ℝ) else 0) = layerMass K D r s := by
    unfold uniformMean layerMass
    rw [Finset.sum_ite_mem]; simp
  rw [← h, ← h, ←uniformMean_add]
  apply uniformMean_congr; intro Z
  have hs : matrixSign K D Z = 1 ∨ matrixSign K D Z = -1 := discriminantSign_cases _ _
  rcases hs with hs|hs <;> by_cases hz : Z.val.rank = r <;> simp [mem_signedLayer,hz,hs]
noncomputable def uk (D r : ℕ) (Z : SymMatrix K D) : ℝ := if Z.val.rank = r then (mass (K:=K) D r)⁻¹ else 0
lemma uk_nn (D r : ℕ) (Z : SymMatrix K D) : 0 ≤ uk D r Z := by
  have hm : 0 ≤ mass (K:=K) D r := uniformMean_nonneg (fun Z => by split <;> norm_num)
  unfold uk; split <;> positivity
lemma boundK (D r : ℕ) (hr : 0 < r) (hrD : r ≤ D) : ∀ᶠ q : OddPrime in primeInfinity,
    ∀ s : ℤ, (s=1 ∨ s= -1) → ∀ Z, rankKernel (ZMod q.val) D r s Z ≤ 8 * uk D r Z := by
  have H (s : ℤ) (hs : s=1 ∨ s= -1) := layerMass_tendsto D r hr hrD hs
  filter_upwards [(H 1 (Or.inl rfl)).eventually (lt_mem_nhds (by norm_num : (1/4:ℝ)<1/2)),
    (H 1 (Or.inl rfl)).eventually (gt_mem_nhds (by norm_num : (1/2:ℝ)<1)),
    (H (-1) (Or.inr rfl)).eventually (lt_mem_nhds (by norm_num : (1/4:ℝ)<1/2)),
    (H (-1) (Or.inr rfl)).eventually (gt_mem_nhds (by norm_num : (1/2:ℝ)<1))] with q ha hb hc hd
  have hp : 0 < (q.val:ℝ)^((D-r+1).choose 2) := pow_pos (by exact_mod_cast q.2.1.pos) _
  intro s hs Z
  have pa : 0 < layerMass (ZMod q.val) D r 1 := pos_of_mul_pos_left (lt_trans (by norm_num) ha) hp.le
  have pc : 0 < layerMass (ZMod q.val) D r (-1) := pos_of_mul_pos_left (lt_trans (by norm_num) hc) hp.le
  have hpos : 0 < layerMass (ZMod q.val) D r s := hs.elim (fun e => e ▸ pa) (fun e => e ▸ pc)
  have hm : 0 < mass (K:=ZMod q.val) D r := by rw [mass_eq]; exact add_pos pa pc
  by_cases hz : Z ∈ signedLayer (ZMod q.val) D r s
  · rw [rankKernel,if_pos hz,uk,if_pos ((mem_signedLayer _ _ _ _ _).mp hz).1]
    rw [←div_eq_mul_inv,inv_eq_one_div,div_le_div_iff₀ hpos hm,one_mul,mass_eq]
    apply (mul_le_mul_iff_left₀ hp).mp
    rcases hs with rfl|rfl <;> linarith only [ha,hb,hc,hd]
  · rw [rankKernel,if_neg hz]; exact mul_nonneg (by norm_num) (uk_nn ..)
end LeafA
open OAI.SidorenkoCounterexample Filter
open scoped Classical
namespace LeafA
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
noncomputable def uface (r : ℕ) (T : Finset (Fin 3)) (X : Fin 3 → SymMatrix K (2*r)) : ℝ :=
  uniformMean fun Y => ∏ k ∈ T, uk (2*r) r (X k-Y)
noncomputable def utail (r : ℕ) (T : Fin 22 → Finset (Fin 3)) : ℝ :=
  uniformMean fun X : Fin 13 → SymMatrix K (2*r) => if fullTransverse X then 0 else ∏ j, uface r (T j) (X ∘ faceVertex j)
lemma singlim (r : ℕ) (hr : 0<r) (T : Fin 22 → Finset (Fin 3)) (ξ : Fin 22 → Fin 3 → ℤ)
    (hs : ∀ j i, ξ j i=1 ∨ ξ j i= -1)
    (ht : Tendsto (fun q : OddPrime => utail (K:=ZMod q.val) r T) primeInfinity (nhds 0)) :
    Tendsto (fun q : OddPrime => matrixSingularTail (K:=ZMod q.val) r T ξ) primeInfinity (nhds 0) := by
  let C := ∏ j, (8:ℝ)^(T j).card
  have hu := tendsto_const_nhds.mul ht (a:=C)
  rw [mul_zero] at hu
  apply squeeze_zero' (Eventually.of_forall (fun q => uniformMean_nonneg (fun X => by split <;> simp [configurationProduct_nonneg]))) _ hu
  filter_upwards [boundK (2*r) r hr (by omega)] with q hq
  unfold utail
  rw [←uniformMean_mul]
  apply uniformMean_mono; intro X
  split_ifs with hx
  · simp
  change (∏ j, faceLocal r (T j) (ξ j) (X ∘ faceVertex j)) ≤ C * _
  unfold C
  rw [←Finset.prod_mul_distrib]
  apply Finset.prod_le_prod (fun j _ => faceLocal_nonneg ..); intro j _
  unfold faceLocal uface
  rw [←uniformMean_mul]; apply uniformMean_mono; intro Y
  rw [←Finset.prod_const,←Finset.prod_mul_distrib]
  exact Finset.prod_le_prod (fun k _ => rankKernel_nonneg ..) (fun k _ => hq _ (hs j k) _)
lemma nt_iff (r : ℕ) (X : Fin 13 → SymMatrix K (2*r)) : ¬ fullTransverse X ↔
    ∃ j k, ((X (faceVertex j (slotLeft k))).val - (X (faceVertex j (slotRight k))).val).det=0 := by
  unfold fullTransverse; push_neg
  constructor
  · rintro ⟨e,he⟩
    have cov : ∀ e : Fin 33, ∃ j k, facePair j k=e := by decide
    obtain ⟨j,k,rfl⟩ := cov e
    exact ⟨j,k,by simpa only [Submodule.coe_sub,(facePair_endpoints j k).1,(facePair_endpoints j k).2] using he⟩
  · rintro ⟨j,k,h⟩; exact ⟨facePair j k, by simpa only [Submodule.coe_sub,(facePair_endpoints j k).1,(facePair_endpoints j k).2] using h⟩
end LeafA
open OAI.SidorenkoCounterexample Filter LeafA
open scoped Classical
private theorem meanC {A : Type} {i j : Fintype A} {f g : A → ℝ} (h : ∀ a, f a=g a) : @uniformMean A i f = @uniformMean A j g := by
  cases Subsingleton.elim i j
  exact uniformMean_congr h

set_option maxHeartbeats 3000000 in
theorem OMA.solution : OMA.R_SidorenkoConjecture_sidorenko_conjecture_graphon_R1_H1_R1_H1_R1_H1_R1_H1_R1.H1 := by
  intro d hd hlarge
  obtain ⟨n,rfl⟩ := hd
  let r := 2*n
  have he : 4*n = 2*r := by dsimp [r]; omega
  rw [he] at *
  have hr : 1<r := by omega
  have hc (q : OddPrime) : quadraticChar (ZMod q.val) ((-1:ZMod q.val)^r)=1 := by simp [r,pow_mul]
  intro hyp
  refine ⟨fun q => SymMatrix (ZMod q.val) (2*r),fun _ => inferInstance,fun _ => inferInstance,
    fun q => rankKernel (ZMod q.val) (2*r) r,fun q s z => rankKernel_nonneg ..,?_,?_,?_⟩
  · intro q s hs
    exact uniformMean_rankKernel _ _ (by omega) (by omega) (by simpa only [ZMod.ringChar_zmod_n] using q.2.2) hs
  · intro q s z; simpa only [hc q,one_mul] using rankKernel_neg (ZMod q.val) (2*r) r s z
  · intro T ξ hs
    have hu : Tendsto (fun q : OddPrime => utail (K:=ZMod q.val) r T) primeInfinity (nhds 0) := by
      refine (hyp T).congr (fun q => ?_)
      unfold utail
      apply meanC; intro X
      by_cases hx : fullTransverse X
      · rw [if_pos hx]; split
        · rename_i hh; exact False.elim (((nt_iff r X).2 hh) hx)
        · rfl
      · rw [if_neg hx]; split
        swap
        · rename_i hh; exact False.elim (hh ((nt_iff r X).1 hx))
        apply Finset.prod_congr rfl; intro j _
        apply meanC; intro Y
        apply Finset.prod_congr rfl; intro k _
        simp only [uk,Function.comp_apply,Submodule.coe_sub,Nat.mul_div_cancel_left _ (by decide : 0<2)]
        split_ifs with ha hb hb
        · apply congrArg Inv.inv; apply meanC; intro; rfl
        · exact False.elim (hb ha)
        · exact False.elim (ha hb)
        · rfl
    have hl := ((transverseDifference_tendsto r hr T ξ hs).add (singlim r (by omega) T ξ hs hu)).sub (boolSingular_tendsto r T ξ hs)
    rw [zero_add,sub_zero] at hl
    refine hl.congr (fun q => ?_)
    dsimp only [Pi.sub_apply,Pi.add_apply]
    rw [←configuration_mean_identity (K:=ZMod q.val) r T ξ]
    apply congrArg₂ (· - ·)
    · symm
      change uniformMean (fun xy : (Fin 13 → SymMatrix (ZMod q.val) (2*r)) × (Fin 22 → SymMatrix (ZMod q.val) (2*r)) => ∏ j, ∏ k ∈ T j,rankKernel _ _ r (ξ j k) (xy.1 (faceVertex j k)-xy.2 j)) = _
      rw [uniformMean_prod]; apply uniformMean_congr; intro X
      rw [uniformMean_pi_product (fun j Y => ∏ k ∈ T j,rankKernel _ _ r (ξ j k) (X (faceVertex j k)-Y))]; rfl
    · apply meanC; intro X
      simp only [boolConfiguration,boolFacePolynomial,hc,Int.cast_one,one_mul,boolSign,pairBool,pairSign,Submodule.coe_sub,(facePair_endpoints _ _).1,(facePair_endpoints _ _).2,Int.cast_eq_one]
      rfl
