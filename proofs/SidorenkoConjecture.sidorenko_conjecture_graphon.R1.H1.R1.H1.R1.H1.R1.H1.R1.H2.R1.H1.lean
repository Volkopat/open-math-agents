import OMAReductions.R_SidorenkoConjecture_sidorenko_conjecture_graphon_R1_H1_R1_H1_R1_H1_R1_H1_R1_H2_R1
import Mathlib
/- Adapted from openai/math (Apache-2.0), 3344da59991ed94f9ba711217b29c1d760badfa6. -/
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
 theorem subspace_count_upper (k : ℕ) (hk : k ≤ finrank K V) :
    (Nat.card (DimSubspace K V k) : ℝ) ≤
      2^k * (Fintype.card K : ℝ)^(k * (finrank K V - k)) := by
  rw [subspace_count_real k hk]
  let q : ℝ := Fintype.card K
  have hq : 2 ≤ q := by
    have hcard : 2 ≤ Fintype.card K := Fintype.one_lt_card
    change (2 : ℝ) ≤ (Fintype.card K : ℝ)
    exact_mod_cast hcard
  have hq0 : 0 < q := by linarith
  have hpow (i : Fin k) : 2 * q^i.val ≤ q^k := by
    calc
      2 * q^i.val ≤ q * q^i.val := mul_le_mul_of_nonneg_right hq (pow_nonneg hq0.le _)
      _ = q^(i.val+1) := by rw [pow_succ]; ring
      _ ≤ q^k := pow_le_pow_right₀ (by linarith) i.isLt
  have hfac (i : Fin k) : (q^finrank K V - q^i.val)/(q^k-q^i.val) ≤
      2 * q^(finrank K V - k) := by
    have hid : q^finrank K V = q^(finrank K V - k) * q^k := by
      rw [← pow_add, Nat.sub_add_cancel hk]
    have hp : 0 < q^i.val := pow_pos hq0 _
    have hd : 0 < q^k-q^i.val := by linarith [hpow i]
    apply (div_le_iff₀ hd).mpr
    have hm := mul_le_mul_of_nonneg_left (hpow i) (pow_nonneg hq0.le (finrank K V-k))
    rw [hid]
    nlinarith
  calc
    (∏ i : Fin k, (q^finrank K V - q^i.val)/(q^k-q^i.val)) ≤
        ∏ _i : Fin k, 2 * q^(finrank K V-k) := by
      apply Finset.prod_le_prod
      · intro i _
        apply div_nonneg
        · exact sub_nonneg.mpr (pow_le_pow_right₀ (by linarith) (i.isLt.le.trans hk))
        · linarith [hpow i, pow_nonneg hq0.le i.val]
      · intro i _
        exact hfac i
    _ = 2^k * q^(k * (finrank K V-k)) := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_pow, ← pow_mul,
        Nat.mul_comm (finrank K V-k) k]
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
 theorem symForm_card [Fintype K] [FiniteDimensional K V] :
    Nat.card (SymForm K V) = Fintype.card K ^ ((finrank K V + 1).choose 2) := by
  rw [Nat.card_congr (symFormMatrix K V), symMatrix_card]
variable {K V}
 theorem symmetric_nullity_exponent (n u : ℕ) (hu : u ≤ n) :
    u*(n-u) + (n-u+1).choose 2 + (u+1).choose 2 = (n+1).choose 2 := by
  have h : ((u*(n-u) + (n-u+1).choose 2 + (u+1).choose 2 : ℕ) : ℚ) =
      ((n+1).choose 2 : ℚ) := by
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_choose_two, Nat.cast_one,
      Nat.cast_sub hu]
    ring
  exact_mod_cast h
end FormCount
end SidorenkoCounterexample
end OAI
namespace OAI
namespace SidorenkoCounterexample
open Module
section LagrangianCharts
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
def canonicalSymplectic : LinearMap.BilinForm K (V × Module.Dual K V) where
  toFun p := {
    toFun := fun q => q.2 p.1 - p.2 q.1
    map_add' := by intros; simp; ring
    map_smul' := by intros; simp; ring }
  map_add' := by
    intro p q
    apply LinearMap.ext
    intro z
    change z.2 (p.1+q.1) - (p.2+q.2) z.1 =
      (z.2 p.1 - p.2 z.1) + (z.2 q.1 - q.2 z.1)
    simp
    ring
  map_smul' := by
    intro a p
    apply LinearMap.ext
    intro z
    change z.2 (a • p.1) - (a • p.2) z.1 = a * (z.2 p.1-p.2 z.1)
    simp
    ring
@[simp] theorem canonicalSymplectic_apply (p q : V × Module.Dual K V) :
    canonicalSymplectic p q = q.2 p.1 - p.2 q.1 := rfl
 theorem canonicalSymplectic_alt : (canonicalSymplectic (K := K) (V := V)).IsAlt := by
  intro p
  simp
 theorem canonicalSymplectic_nondegenerate :
    (canonicalSymplectic (K := K) (V := V)).Nondegenerate := by
  have hleft : ∀ p : V × Module.Dual K V,
      (∀ q, canonicalSymplectic p q = 0) → p = 0 := by
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
  exact canonicalSymplectic_alt.isRefl _ _ (hp q)
variable [FiniteDimensional K V]
abbrev Lagrangian := {L : Submodule K (V × Module.Dual K V) //
  canonicalSymplectic.orthogonal L = L}
 theorem lagrangian_finrank (L : Lagrangian (K := K) (V := V)) :
    finrank K L.val = finrank K V := by
  have h := LinearMap.BilinForm.finrank_orthogonal canonicalSymplectic_nondegenerate L.val
  rw [L.property, Module.finrank_prod, Subspace.dual_finrank_eq] at h
  have hle := Submodule.finrank_le L.val
  rw [Module.finrank_prod, Subspace.dual_finrank_eq] at hle
  omega
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
omit [FiniteDimensional K V] in
 theorem formGraph_isotropic (U : Submodule K V) (B : SymForm K U) :
    formGraph U B.val ≤ canonicalSymplectic.orthogonal (formGraph U B.val) := by
  rintro p ⟨u,hu,hf⟩ q ⟨v,hv,hg⟩
  change p.2 q.1 - q.2 p.1 = 0
  rw [← hu, ← hv]
  have hf' := congrArg (fun l : Module.Dual K U => l v) hf
  have hg' := congrArg (fun l : Module.Dual K U => l u) hg
  exact sub_eq_zero.mpr (hf'.trans ((B.property.eq u v).trans hg'.symm))
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
noncomputable def graphLagrangian (U : Submodule K V) (B : SymForm K U) :
    Lagrangian (K := K) (V := V) :=
  ⟨formGraph U B.val, by
    apply (Submodule.eq_of_le_of_finrank_eq (formGraph_isotropic U B) _).symm
    rw [formGraph_finrank, LinearMap.BilinForm.finrank_orthogonal canonicalSymplectic_nondegenerate,
      Module.finrank_prod, Subspace.dual_finrank_eq, formGraph_finrank, Nat.add_sub_cancel_left]⟩
 theorem graphLagrangian_form_injective (U : Submodule K V) :
    Function.Injective (graphLagrangian (K := K) U) := by
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
 theorem lagrangian_pairing_zero (L : Lagrangian (K := K) (V := V))
    {p q : V × Module.Dual K V} (hp : p ∈ L.val) (hq : q ∈ L.val) :
    canonicalSymplectic p q = 0 := by
  have hq' : q ∈ canonicalSymplectic.orthogonal L.val := L.property.symm ▸ hq
  exact hq' p hp
 theorem graphLagrangian_surjective :
    Function.Surjective (fun S : Σ U : Submodule K V, SymForm K U => graphLagrangian S.1 S.2) := by
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
  have hC : C.IsSymm := by
    constructor
    intro u v
    change (s u).val.2 v.val = (s v).val.2 u.val
    have h := lagrangian_pairing_zero L (s u).property (s v).property
    change (s v).val.2 (s u).val.1 - (s u).val.2 (s v).val.1 = 0 at h
    rw [hsfst, hsfst] at h
    exact (sub_eq_zero.mp h).symm
  refine ⟨⟨U,⟨C,hC⟩⟩, ?_⟩
  apply Subtype.ext
  symm
  apply Submodule.eq_of_le_of_finrank_eq
  · intro x hx
    let u : U := ⟨x.1,⟨x,hx,rfl⟩⟩
    refine ⟨u,rfl,?_⟩
    apply LinearMap.ext
    intro y
    have h := lagrangian_pairing_zero L hx (s y).property
    change (s y).val.2 x.1 - x.2 (s y).val.1 = 0 at h
    rw [hsfst] at h
    change x.2 y.val = (s u).val.2 y.val
    exact (sub_eq_zero.mp h).symm.trans (hC.eq y u)
  · exact (lagrangian_finrank L).trans (formGraph_finrank U C).symm
noncomputable def lagrangianGraphEquiv :
    (Σ U : Submodule K V, SymForm K U) ≃ Lagrangian (K := K) (V := V) :=
  Equiv.ofBijective (fun S => graphLagrangian S.1 S.2) ⟨by
    rintro ⟨U,B⟩ ⟨W,C⟩ he
    have h : U = W := by
      rw [← formGraph_fst_range U B.val, ← formGraph_fst_range W C.val]
      exact congrArg (fun L : Lagrangian (K := K) (V := V) =>
        L.val.map (LinearMap.fst K V (Module.Dual K V))) he
    cases h
    congr 1
    exact graphLagrangian_form_injective U he,
    graphLagrangian_surjective⟩
 theorem lagrangian_card_sum [Fintype K] [Finite V] :
    letI := Fintype.ofFinite (Submodule K V)
    Nat.card (Lagrangian (K := K) (V := V)) =
      ∑ U : Submodule K V, (Fintype.card K)^((finrank K U+1).choose 2) := by
  classical
  let := Fintype.ofFinite (Submodule K V)
  rw [← Nat.card_congr (lagrangianGraphEquiv (K := K) (V := V)), Nat.card_sigma]
  simp only [symForm_card]
end LagrangianCharts
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section NormalCoordinates
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E) (L : Submodule K E)
def symplecticProjection : E →ₗ[K] Module.Dual K L := ω.flip.compl₂ L.subtype
 theorem symplecticProjection_surjective (hω : ω.Nondegenerate) :
    Function.Surjective (symplecticProjection ω L) := by
  intro f
  obtain ⟨g,hg⟩ := Subspace.dualRestrict_surjective (W := L) f
  let e := ω.flip.toDual (LinearMap.BilinForm.nondegenerate_flip_iff.mpr hω)
  refine ⟨e.symm g, ?_⟩
  apply LinearMap.ext
  intro l
  change ω.flip (e.symm g) l.val = f l
  have he : ω.flip (e.symm g) l.val = g l.val := by
    exact congrArg (fun f : Module.Dual K E => f l.val) (e.apply_symm_apply g)
  exact he.trans (LinearMap.congr_fun hg l)
omit [FiniteDimensional K E] in
 theorem symplecticProjection_ker (hL : ω.orthogonal L = L) :
    (symplecticProjection ω L).ker = L := by
  ext x
  rw [LinearMap.mem_ker]
  constructor
  · intro h
    rw [← hL]
    intro l hl
    exact LinearMap.congr_fun h ⟨l,hl⟩
  · intro hx
    apply LinearMap.ext
    intro l
    have hx' : x ∈ ω.orthogonal L := hL.symm ▸ hx
    exact hx' l.val l.property
 theorem exists_isotropic_section (h2 : (2 : K) ≠ 0) (ha : ω.IsAlt)
    (hω : ω.Nondegenerate) (hL : ω.orthogonal L = L) :
    ∃ s : Module.Dual K L →ₗ[K] E,
      (symplecticProjection ω L).comp s = LinearMap.id ∧
      ∀ f g, ω (s f) (s g) = 0 := by
  obtain ⟨s,hs⟩ := (symplecticProjection ω L).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (symplecticProjection_surjective ω L hω))
  let A : LinearMap.BilinForm K (Module.Dual K L) := ω.compl₁₂ s s
  let t : Module.Dual K L →ₗ[K] L :=
    (-(2 : K)⁻¹) • ((Module.evalEquiv K L).symm.toLinearMap.comp A)
  have ht (f g : Module.Dual K L) : g (t f) = -(2 : K)⁻¹ * ω (s f) (s g) := by
    simp [t,A]
  have hproj (f : Module.Dual K L) (l : L) : ω l.val (s f) = f l := by
    exact LinearMap.congr_fun (LinearMap.congr_fun hs f) l
  have hLL (l m : L) : ω l.val m.val = 0 := by
    have hm : m.val ∈ ω.orthogonal L := hL.symm ▸ m.property
    exact hm l.val l.property
  refine ⟨s + L.subtype.comp t, ?_, ?_⟩
  · apply LinearMap.ext
    intro f
    apply LinearMap.ext
    intro l
    change ω l.val (s f + (t f).val) = f l
    rw [map_add, hproj, hLL, add_zero]
  · intro f g
    change ω (s f + (t f).val) (s g + (t g).val) = 0
    simp only [map_add, LinearMap.add_apply]
    rw [hproj, hLL, ← ha.neg_eq (t g).val (s f), hproj, ht, ht,
      ← ha.neg_eq (s f) (s g)]
    field_simp
    ring
 theorem exists_lagrangian_coordinates (h2 : (2 : K) ≠ 0) (ha : ω.IsAlt)
    (hω : ω.Nondegenerate) (hL : ω.orthogonal L = L) :
    ∃ e : (L × Module.Dual K L) ≃ₗ[K] E,
      (∀ l : L, e (l,0) = l.val) ∧
      ∀ x y, ω (e x) (e y) = canonicalSymplectic x y := by
  obtain ⟨s,hs,hiso⟩ := exists_isotropic_section ω L h2 ha hω hL
  let e : (L × Module.Dual K L) →ₗ[K] E :=
    L.subtype.comp (LinearMap.fst K L (Module.Dual K L)) +
    s.comp (LinearMap.snd K L (Module.Dual K L))
  have hp (l : L) : symplecticProjection ω L l.val = 0 := by
    exact (symplecticProjection_ker ω L hL).ge l.property
  have heproj (x : L × Module.Dual K L) : symplecticProjection ω L (e x) = x.2 := by
    change symplecticProjection ω L (x.1.val + s x.2) = x.2
    rw [map_add, hp, zero_add]
    exact LinearMap.congr_fun hs x.2
  have hinj : Function.Injective e := by
    apply (LinearMap.ker_eq_bot).mp
    apply (Submodule.eq_bot_iff _).mpr
    intro x hx
    have hx0 : e x = 0 := hx
    have hf : x.2 = 0 := by rw [← heproj x, hx0, map_zero]
    apply Prod.ext
    · apply Subtype.ext
      simpa [e,hf] using hx0
    · exact hf
  have hsurj : Function.Surjective e := by
    intro x
    let f := symplecticProjection ω L x
    have hz : x - s f ∈ L := by
      apply (symplecticProjection_ker ω L hL).le
      rw [LinearMap.mem_ker, map_sub]
      exact sub_eq_zero.mpr (LinearMap.congr_fun hs f).symm
    refine ⟨(⟨x-s f,hz⟩,f), ?_⟩
    change x - s f + s f = x
    exact sub_add_cancel x (s f)
  refine ⟨LinearEquiv.ofBijective e ⟨hinj,hsurj⟩, ?_, ?_⟩
  · intro l
    change l.val + s 0 = l.val
    simp
  · rintro ⟨l,f⟩ ⟨m,g⟩
    change ω (l.val + s f) (m.val + s g) = g l - f m
    have hLL : ω l.val m.val = 0 := by
      have hm : m.val ∈ ω.orthogonal L := hL.symm ▸ m.property
      exact hm l.val l.property
    have hfg (f : Module.Dual K L) (l : L) : ω l.val (s f) = f l :=
      LinearMap.congr_fun (LinearMap.congr_fun hs f) l
    simp only [map_add, LinearMap.add_apply]
    rw [hLL, hfg,
      ← ha.neg_eq m.val (s f), hfg, hiso]
    ring
 theorem self_orthogonal_twice_finrank (hω : ω.Nondegenerate)
    (hL : ω.orthogonal L = L) : 2 * finrank K L = finrank K E := by
  have h := LinearMap.BilinForm.finrank_orthogonal hω L
  rw [hL] at h
  have hle := Submodule.finrank_le L
  omega
 theorem lagrangian_transitivity (h2 : (2 : K) ≠ 0) (ha : ω.IsAlt)
    (hω : ω.Nondegenerate) (hL : ω.orthogonal L = L)
    (M : Submodule K E) (hM : ω.orthogonal M = M) :
    ∃ e : E ≃ₗ[K] E, (∀ x y, ω (e x) (e y) = ω x y) ∧ L.map e.toLinearMap = M := by
  obtain ⟨eL,hEL,hωL⟩ := exists_lagrangian_coordinates ω L h2 ha hω hL
  obtain ⟨eM,hEM,hωM⟩ := exists_lagrangian_coordinates ω M h2 ha hω hM
  have hdim : finrank K L = finrank K M := by
    have h1 := self_orthogonal_twice_finrank ω L hω hL
    have h2 := self_orthogonal_twice_finrank ω M hω hM
    omega
  let f : L ≃ₗ[K] M := LinearEquiv.ofFinrankEq L M hdim
  let c : (L × Module.Dual K L) ≃ₗ[K] (M × Module.Dual K M) :=
    f.prodCongr f.symm.dualMap
  have hc (x y : L × Module.Dual K L) :
      canonicalSymplectic (c x) (c y) = canonicalSymplectic x y := by
    simp [c,canonicalSymplectic_apply]
  let e := eL.symm.trans (c.trans eM)
  have he (l : L) : e l.val = (f l).val := by
    change eM (c (eL.symm l.val)) = (f l).val
    rw [← hEL l, eL.symm_apply_apply]
    simpa [c] using hEM (f l)
  refine ⟨e, ?_, ?_⟩
  · intro x y
    change ω (eM (c (eL.symm x))) (eM (c (eL.symm y))) = ω x y
    rw [hωM, hc, ← hωL, eL.apply_symm_apply, eL.apply_symm_apply]
  · ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      change e y ∈ M
      rw [he ⟨y,hy⟩]
      exact (f ⟨y,hy⟩).property
    · intro hx
      let l := f.symm ⟨x,hx⟩
      refine ⟨l.val,l.property, ?_⟩
      change e l.val = x
      rw [he]
      exact congrArg Subtype.val (f.apply_symm_apply ⟨x,hx⟩)
omit [FiniteDimensional K E] in
 theorem orthogonal_map_of_isometry (e : E ≃ₗ[K] E)
    (he : ∀ x y, ω (e x) (e y) = ω x y) (U : Submodule K E) :
    ω.orthogonal (U.map e.toLinearMap) = (ω.orthogonal U).map e.toLinearMap := by
  ext x
  constructor
  · intro hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    intro u hu
    rw [← he, e.apply_symm_apply]
    exact hx (e u) ⟨u,hu,rfl⟩
  · rintro ⟨y,hy,rfl⟩ _ ⟨u,hu,rfl⟩
    change ω (e u) (e y) = 0
    rw [he]
    exact hy u hu
noncomputable def lagrangianIsometryEquiv (e : E ≃ₗ[K] E)
    (he : ∀ x y, ω (e x) (e y) = ω x y) :
    {U : Submodule K E // ω.orthogonal U = U} ≃
    {U : Submodule K E // ω.orthogonal U = U} :=
  (Submodule.orderIsoMapComap e).toEquiv.subtypeEquiv (by
    intro U
    change ω.orthogonal U = U ↔ ω.orthogonal (U.map e.toLinearMap) = U.map e.toLinearMap
    rw [orthogonal_map_of_isometry ω e he]
    exact (Submodule.orderIsoMapComap e).injective.eq_iff.symm)
end NormalCoordinates
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section PairCounts
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
def verticalSpace : Submodule K (V × Module.Dual K V) :=
  (LinearMap.fst K V (Module.Dual K V)).ker
omit [FiniteDimensional K V] in
@[simp] theorem mem_verticalSpace (p : V × Module.Dual K V) :
    p ∈ verticalSpace (K := K) ↔ p.1 = 0 := Iff.rfl
omit [FiniteDimensional K V] in
 theorem verticalSpace_graph : verticalSpace (K := K) (V := V) = formGraph ⊥ 0 := by
  ext p
  constructor
  · intro hp
    refine ⟨0,hp.symm,?_⟩
    ext u
    change p.2 u.val = 0
    have hu : u.val = 0 := u.property
    rw [hu,map_zero]
  · rintro ⟨u,hu,_⟩
    change p.1 = 0
    exact hu.symm.trans u.property
noncomputable def verticalLagrangian : Lagrangian (K := K) (V := V) :=
  ⟨verticalSpace, by
    rw [verticalSpace_graph]
    exact (graphLagrangian ⊥ ⟨0, LinearMap.BilinForm.isSymm_zero⟩).property⟩
noncomputable def graphVerticalIntersectionEquiv (U : Submodule K V)
    (B : LinearMap.BilinForm K U) :
    U.dualAnnihilator ≃ₗ[K] ↥(formGraph U B ⊓ verticalSpace (K := K) (V := V)) where
  toFun f := ⟨(0,f.val),⟨⟨0,rfl, by
    ext u
    simpa using ((Submodule.mem_dualAnnihilator (W := U) f.val).mp f.property) u u.property⟩,rfl⟩⟩
  invFun p := ⟨p.val.2, by
    obtain ⟨u,hu,hf⟩ := p.property.1
    have hu0 : u = 0 := Subtype.ext (hu.trans p.property.2)
    apply (Submodule.mem_dualAnnihilator (W := U) p.val.2).mpr
    intro x hxU
    have hf' := congrArg (fun l : Module.Dual K U => l ⟨x,hxU⟩) hf
    simpa [hu0] using hf'⟩
  left_inv _ := rfl
  right_inv p := by
    apply Subtype.ext
    exact Prod.ext p.property.2.symm rfl
  map_add' f g := by apply Subtype.ext; simp
  map_smul' a f := by apply Subtype.ext; simp
 theorem graph_vertical_intersection_finrank (U : Submodule K V)
    (B : LinearMap.BilinForm K U) :
    finrank K ↥(formGraph U B ⊓ verticalSpace (K := K) (V := V)) = finrank K V - finrank K U := by
  rw [← (graphVerticalIntersectionEquiv U B).finrank_eq]
  have h := Subspace.finrank_add_finrank_dualAnnihilator_eq U
  omega
noncomputable def pairStratumEquiv (h : ℕ) (hh : h ≤ finrank K V) :
    (Σ U : {U : Submodule K V // finrank K U = finrank K V-h}, SymForm K U.val) ≃
    {L : Lagrangian (K := K) (V := V) // finrank K ↥(L.val ⊓ verticalSpace (K := K) (V := V)) = h} := by
  classical
  let e : (Σ U : {U : Submodule K V // finrank K U = finrank K V-h}, SymForm K U.val) →
      Lagrangian (K := K) (V := V) := fun S => graphLagrangian S.1.val S.2
  have he (S) : finrank K ↥((e S).val ⊓ verticalSpace (K := K) (V := V)) = h := by
    exact (graph_vertical_intersection_finrank S.1.val S.2.val).trans (by
      rw [S.1.property, Nat.sub_sub_self hh])
  refine Equiv.ofBijective (fun S => ⟨e S,he S⟩) ⟨?_, ?_⟩
  · rintro ⟨⟨U,hU⟩,B⟩ ⟨⟨W,hW⟩,C⟩ hEq
    have h : graphLagrangian U B = graphLagrangian W C := congrArg Subtype.val hEq
    have hUW : U = W := by
      have hs : (⟨U,B⟩ : Σ U : Submodule K V, SymForm K U) = ⟨W,C⟩ :=
        (lagrangianGraphEquiv (K := K) (V := V)).injective h
      exact congrArg Sigma.fst hs
    cases hUW
    have hBC := graphLagrangian_form_injective U h
    cases hBC
    rfl
  · rintro ⟨L,hL⟩
    obtain ⟨⟨U,B⟩,hUB⟩ := graphLagrangian_surjective (K := K) (V := V) L
    have hU : finrank K U = finrank K V-h := by
      have hdim : finrank K V-finrank K U = h := by
        rw [← graph_vertical_intersection_finrank U B.val]
        have heq := congrArg (fun L : Lagrangian (K := K) (V := V) =>
          finrank K ↥(L.val ⊓ verticalSpace (K := K) (V := V))) hUB
        exact heq.trans hL
      have hle := Submodule.finrank_le U
      omega
    refine ⟨⟨⟨U,hU⟩,B⟩, Subtype.ext hUB⟩
 theorem vertical_pair_count [Fintype K] [Finite V] (h : ℕ) (hh : h ≤ finrank K V) :
    Nat.card {L : Lagrangian (K := K) (V := V) // finrank K ↥(L.val ⊓ verticalSpace (K := K) (V := V)) = h} =
    Nat.card {U : Submodule K V // finrank K U = finrank K V-h} *
      (Fintype.card K)^((finrank K V-h+1).choose 2) := by
  classical
  let := Fintype.ofFinite {U : Submodule K V // finrank K U = finrank K V-h}
  rw [← Nat.card_congr (pairStratumEquiv (K := K) (V := V) h hh), Nat.card_sigma]
  simp only [symForm_card]
  have hd (U : {U : Submodule K V // finrank K U = finrank K V-h}) :
      finrank K U.val = finrank K V-h := U.property
  simp_rw [hd]
  simp [Nat.card_eq_fintype_card]
omit [FiniteDimensional K V] in
 theorem pair_stratum_card_congr (A B : Lagrangian (K := K) (V := V))
    (e : (V × Module.Dual K V) ≃ₗ[K] (V × Module.Dual K V))
    (he : ∀ x y, canonicalSymplectic (e x) (e y) = canonicalSymplectic x y)
    (hAB : A.val.map e.toLinearMap = B.val) (h : ℕ) :
    Nat.card {L : Lagrangian (K := K) (V := V) // finrank K ↥(L.val ⊓ A.val) = h} =
    Nat.card {L : Lagrangian (K := K) (V := V) // finrank K ↥(L.val ⊓ B.val) = h} := by
  let f := lagrangianIsometryEquiv canonicalSymplectic e he
  apply Nat.card_congr (f.subtypeEquiv _)
  intro L
  have hdim : finrank K ↥((f L).val ⊓ B.val) = finrank K ↥(L.val ⊓ A.val) := by
    change finrank K ↥(L.val.map e.toLinearMap ⊓ B.val) = _
    rw [← hAB, ← Submodule.map_inf e.toLinearMap e.injective]
    exact (Submodule.equivMapOfInjective e.toLinearMap e.injective (L.val ⊓ A.val)).finrank_eq.symm
  rw [hdim]
 theorem lagrangian_pair_count [Fintype K] [Finite V] (h2 : (2 : K) ≠ 0)
    (A : Lagrangian (K := K) (V := V)) (h : ℕ) (hh : h ≤ finrank K V) :
    Nat.card {L : Lagrangian (K := K) (V := V) // finrank K ↥(L.val ⊓ A.val) = h} =
    Nat.card {U : Submodule K V // finrank K U = finrank K V-h} *
      (Fintype.card K)^((finrank K V-h+1).choose 2) := by
  obtain ⟨e,he,hAe⟩ := lagrangian_transitivity canonicalSymplectic A.val h2
    canonicalSymplectic_alt canonicalSymplectic_nondegenerate A.property
    verticalLagrangian.val verticalLagrangian.property
  exact (pair_stratum_card_congr A verticalLagrangian e he hAe h).trans
    (vertical_pair_count (K := K) (V := V) h hh)
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
def reductionKernel : Submodule K (ω.orthogonal S) := S.comap (ω.orthogonal S).subtype
abbrev ReducedSpace := (ω.orthogonal S) ⧸ reductionKernel ω S
private theorem restricted_alt (ha : ω.IsAlt) :
    (ω.compl₁₂ (ω.orthogonal S).subtype (ω.orthogonal S).subtype).IsAlt := by
  intro x
  exact ha x.val
private theorem reductionKernel_le_ker : reductionKernel ω S ≤
    (ω.compl₁₂ (ω.orthogonal S).subtype (ω.orthogonal S).subtype).ker := by
  intro x hx
  apply LinearMap.mem_ker.mpr
  ext y
  exact y.property x.val hx
def symplecticReductionForm (ha : ω.IsAlt) : LinearMap.BilinForm K (ReducedSpace ω S) :=
  LinearMap.IsRefl.liftQ₂
    (ω.compl₁₂ (ω.orthogonal S).subtype (ω.orthogonal S).subtype)
    (reductionKernel ω S) (restricted_alt ω S ha).isRefl (reductionKernel_le_ker ω S)
@[simp] theorem reductionForm_mk (ha : ω.IsAlt) (x y : ω.orthogonal S) :
    symplecticReductionForm ω S ha
      ((reductionKernel ω S).mkQ x) ((reductionKernel ω S).mkQ y) = ω x.val y.val := rfl
theorem symplecticReductionForm_alt (ha : ω.IsAlt) :
    (symplecticReductionForm ω S ha).IsAlt := by
  intro x
  induction x using Submodule.Quotient.induction_on with
  | H x => exact ha x.val
theorem symplecticReductionForm_nondegenerate [FiniteDimensional K E]
    (ha : ω.IsAlt) (hω : ω.Nondegenerate) :
    (symplecticReductionForm ω S ha).Nondegenerate := by
  have hl (x : ReducedSpace ω S)
      (hx : ∀ y, symplecticReductionForm ω S ha x y = 0) : x = 0 := by
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      apply (Submodule.Quotient.mk_eq_zero (reductionKernel ω S)).mpr
      change x.val ∈ S
      apply (ω.orthogonal_orthogonal hω ha.isRefl S).le
      intro y hy
      exact ha.isRefl _ _ (hx ((reductionKernel ω S).mkQ ⟨y,hy⟩))
  refine ⟨hl, ?_⟩
  intro x hx
  apply hl
  intro y
  exact (symplecticReductionForm_alt ω S ha).isRefl _ _ (hx y)
theorem reducedSpace_finrank [FiniteDimensional K E]
    (hω : ω.Nondegenerate) (hS : S ≤ ω.orthogonal S) :
    finrank K (ReducedSpace ω S) + 2 * finrank K S = finrank K E := by
  have hker : finrank K (reductionKernel ω S) = finrank K S :=
    (Submodule.comapSubtypeEquivOfLe hS).finrank_eq
  have hq := Submodule.finrank_quotient_add_finrank (reductionKernel ω S)
  have hp := ω.finrank_orthogonal hω S
  have hle := Submodule.finrank_le S
  change finrank K (ReducedSpace ω S) + finrank K (reductionKernel ω S) =
    finrank K (ω.orthogonal S) at hq
  rw [hker] at hq
  omega
def liftReduction (T : Submodule K (ReducedSpace ω S)) : Submodule K E :=
  (T.comap (reductionKernel ω S).mkQ).map (ω.orthogonal S).subtype
@[simp] theorem mem_liftReduction (T : Submodule K (ReducedSpace ω S)) (x : E) :
    x ∈ liftReduction ω S T ↔ ∃ hx : x ∈ ω.orthogonal S,
      (reductionKernel ω S).mkQ ⟨x,hx⟩ ∈ T := by
  constructor
  · rintro ⟨y,hy,hx⟩
    cases hx
    exact ⟨y.property,hy⟩
  · rintro ⟨hx,ht⟩
    exact ⟨⟨x,hx⟩,ht,rfl⟩
theorem le_liftReduction (hS : S ≤ ω.orthogonal S)
    (T : Submodule K (ReducedSpace ω S)) : S ≤ liftReduction ω S T := by
  intro x hx
  apply (mem_liftReduction ω S T x).mpr
  refine ⟨hS hx, ?_⟩
  have hz : (reductionKernel ω S).mkQ ⟨x,hS hx⟩ = 0 :=
    (Submodule.Quotient.mk_eq_zero (reductionKernel ω S)).mpr hx
  rw [hz]
  exact T.zero_mem
theorem orthogonal_liftReduction (ha : ω.IsAlt) (hS : S ≤ ω.orthogonal S)
    (T : Submodule K (ReducedSpace ω S)) :
    ω.orthogonal (liftReduction ω S T) =
      liftReduction ω S ((symplecticReductionForm ω S ha).orthogonal T) := by
  ext x
  constructor
  · intro hx
    have hxP : x ∈ ω.orthogonal S := by
      intro s hs
      exact hx s (le_liftReduction ω S hS T hs)
    apply (mem_liftReduction ω S _ x).mpr
    refine ⟨hxP, ?_⟩
    intro y hy
    induction y using Submodule.Quotient.induction_on with
    | H y =>
      exact hx y.val ((mem_liftReduction ω S T y.val).mpr ⟨y.property,hy⟩)
  · intro hx
    obtain ⟨hxP,hxQ⟩ := (mem_liftReduction ω S _ x).mp hx
    intro y hy
    obtain ⟨hyP,hyQ⟩ := (mem_liftReduction ω S T y).mp hy
    exact hxQ ((reductionKernel ω S).mkQ ⟨y,hyP⟩) hyQ
theorem liftReduction_lagrangian (ha : ω.IsAlt) (hS : S ≤ ω.orthogonal S)
    (T : Submodule K (ReducedSpace ω S))
    (hT : (symplecticReductionForm ω S ha).orthogonal T = T) :
    ω.orthogonal (liftReduction ω S T) = liftReduction ω S T := by
  rw [orthogonal_liftReduction ω S ha hS, hT]
def reduceSubspace (L : Submodule K E) : Submodule K (ReducedSpace ω S) :=
  (L.comap (ω.orthogonal S).subtype).map (reductionKernel ω S).mkQ
theorem reduce_lift (T : Submodule K (ReducedSpace ω S)) :
    reduceSubspace ω S (liftReduction ω S T) = T := by
  ext z
  induction z using Submodule.Quotient.induction_on with
  | H z =>
    constructor
    · rintro ⟨y,hy,heq⟩
      obtain ⟨hyP,hyT⟩ := (mem_liftReduction ω S T y.val).mp hy
      change (reductionKernel ω S).mkQ y ∈ T at hyT
      exact heq ▸ hyT
    · intro hz
      refine ⟨z,?_,rfl⟩
      exact (mem_liftReduction ω S T z.val).mpr ⟨z.property,hz⟩
theorem liftReduction_injective : Function.Injective (liftReduction ω S) := by
  intro T U h
  have hh := congrArg (reduceSubspace ω S) h
  simpa only [reduce_lift] using hh
theorem lift_reduce (L : Submodule K E) (hSL : S ≤ L) (hLP : L ≤ ω.orthogonal S) :
    liftReduction ω S (reduceSubspace ω S L) = L := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxP,y,hy,hyeq⟩ := (mem_liftReduction ω S _ x).mp hx
    have hz : (reductionKernel ω S).mkQ (y - ⟨x,hxP⟩) = 0 := by
      rw [map_sub,hyeq,sub_self]
    have hzS : y.val-x ∈ S := (Submodule.Quotient.mk_eq_zero (reductionKernel ω S)).mp hz
    have hxL := L.sub_mem hy (hSL hzS)
    simpa only [Submodule.subtype_apply, sub_sub_cancel] using hxL
  · intro hx
    apply (mem_liftReduction ω S _ x).mpr
    exact ⟨hLP hx,⟨⟨x,hLP hx⟩,hx,rfl⟩⟩
theorem lagrangian_le_orthogonal (L : Submodule K E)
    (hL : ω.orthogonal L = L) (hSL : S ≤ L) : L ≤ ω.orthogonal S := by
  intro x hx s hs
  have hxO : x ∈ ω.orthogonal L := hL.symm ▸ hx
  exact hxO s (hSL hs)
theorem reduce_lagrangian (ha : ω.IsAlt) (hS : S ≤ ω.orthogonal S)
    (L : Submodule K E) (hL : ω.orthogonal L = L) (hSL : S ≤ L) :
    (symplecticReductionForm ω S ha).orthogonal (reduceSubspace ω S L) =
      reduceSubspace ω S L := by
  apply liftReduction_injective ω S
  rw [← orthogonal_liftReduction ω S ha hS,
    lift_reduce ω S L hSL (lagrangian_le_orthogonal ω S L hL hSL),hL]
def containingLagrangianEquiv (ha : ω.IsAlt) (hS : S ≤ ω.orthogonal S) :
    {L : Submodule K E // ω.orthogonal L = L ∧ S ≤ L} ≃
      {T : Submodule K (ReducedSpace ω S) // (symplecticReductionForm ω S ha).orthogonal T = T} where
  toFun L := ⟨reduceSubspace ω S L.val,reduce_lagrangian ω S ha hS L.val L.property.1 L.property.2⟩
  invFun T := ⟨liftReduction ω S T.val,
    liftReduction_lagrangian ω S ha hS T.val T.property,le_liftReduction ω S hS T.val⟩
  left_inv L := Subtype.ext (lift_reduce ω S L.val L.property.2
    (lagrangian_le_orthogonal ω S L.val L.property.1 L.property.2))
  right_inv T := Subtype.ext (reduce_lift ω S T.val)
theorem orthogonal_sup_eq (U W : Submodule K E) :
    ω.orthogonal (U ⊔ W) = ω.orthogonal U ⊓ ω.orthogonal W := by
  ext x
  constructor
  · intro hx
    exact ⟨fun y hy => hx y ((le_sup_left : U ≤ U ⊔ W) hy), fun y hy => hx y ((le_sup_right : W ≤ U ⊔ W) hy)⟩
  · rintro ⟨hU,hW⟩ y hy
    obtain ⟨u,hu,w,hw,rfl⟩ := Submodule.mem_sup.mp hy
    simp only [map_add,LinearMap.add_apply,hU u hu,hW w hw,add_zero]
theorem orthogonal_inf_eq [FiniteDimensional K E] (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (U W : Submodule K E) :
    ω.orthogonal (U ⊓ W) = ω.orthogonal U ⊔ ω.orthogonal W := by
  have hinj : Function.Injective ω.orthogonal := by
    intro A B h
    have hh := congrArg ω.orthogonal h
    simpa only [ω.orthogonal_orthogonal hω ha.isRefl] using hh
  apply hinj
  rw [ω.orthogonal_orthogonal hω ha.isRefl, orthogonal_sup_eq,
    ω.orthogonal_orthogonal hω ha.isRefl,ω.orthogonal_orthogonal hω ha.isRefl]
theorem general_lagrangian_reduction [FiniteDimensional K E]
    (ha : ω.IsAlt) (hω : ω.Nondegenerate) (hS : S ≤ ω.orthogonal S)
    (L : Submodule K E) (hL : ω.orthogonal L = L) :
    (symplecticReductionForm ω S ha).orthogonal (reduceSubspace ω S L) =
      reduceSubspace ω S L := by
  let U := (L ⊓ ω.orthogonal S) ⊔ S
  have hUL : ω.orthogonal U = U := by
    dsimp only [U]
    rw [orthogonal_sup_eq, orthogonal_inf_eq ω ha hω, hL,
      ω.orthogonal_orthogonal hω ha.isRefl]
    apply le_antisymm
    · rintro x ⟨hx,hxP⟩
      obtain ⟨l,hl,s,hs,rfl⟩ := Submodule.mem_sup.mp hx
      have hlP : l ∈ ω.orthogonal S := by
        have h := (ω.orthogonal S).sub_mem hxP (hS hs)
        simpa only [add_sub_cancel_right] using h
      exact Submodule.mem_sup.mpr ⟨l,⟨hl,hlP⟩,s,hs,rfl⟩
    · rintro x hx
      obtain ⟨l,hl,s,hs,rfl⟩ := Submodule.mem_sup.mp hx
      exact ⟨Submodule.mem_sup.mpr ⟨l,hl.1,s,hs,rfl⟩,
        (ω.orthogonal S).add_mem hl.2 (hS hs)⟩
  have hUred : reduceSubspace ω S U = reduceSubspace ω S L := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      obtain ⟨l,hl,s,hs,hls⟩ := Submodule.mem_sup.mp hy
      refine ⟨⟨l,hl.2⟩,hl.1,?_⟩
      have hz : (reductionKernel ω S).mkQ ⟨s,hS hs⟩ = 0 :=
        (Submodule.Quotient.mk_eq_zero (reductionKernel ω S)).mpr hs
      have heq : y = (⟨l,hl.2⟩ : ω.orthogonal S) + ⟨s,hS hs⟩ :=
        Subtype.ext hls.symm
      rw [heq,map_add,hz,add_zero]
    · rintro ⟨y,hy,rfl⟩
      exact ⟨y,(le_sup_left : L ⊓ ω.orthogonal S ≤ U) ⟨hy,y.property⟩,rfl⟩
  rw [← hUred]
  exact reduce_lagrangian ω S ha hS U hUL le_sup_right
end Reduction
section IsotropicExtension
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Finite E]
variable (ω : LinearMap.BilinForm K E)
omit [Finite E] in
theorem isotropic_sup_line (ha : ω.IsAlt) (L : Submodule K E)
    (hL : L ≤ ω.orthogonal L) (x : E) (hx : x ∈ ω.orthogonal L) :
    L ⊔ K ∙ x ≤ ω.orthogonal (L ⊔ K ∙ x) := by
  intro y hy z hz
  obtain ⟨l,hl,v,hv,rfl⟩ := Submodule.mem_sup.mp hy
  obtain ⟨m,hm,w,hw,rfl⟩ := Submodule.mem_sup.mp hz
  obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hv
  obtain ⟨b,rfl⟩ := Submodule.mem_span_singleton.mp hw
  have hxl : ω x l = 0 := ha.isRefl _ _ (hx l hl)
  simp only [map_add,map_smul,LinearMap.add_apply,LinearMap.smul_apply,
    hL hl m hm,hx m hm,hxl,ha x,smul_zero,add_zero]
theorem exists_containing_lagrangian (ha : ω.IsAlt) (S : Submodule K E)
    (hS : S ≤ ω.orthogonal S) :
    ∃ L : Submodule K E, S ≤ L ∧ ω.orthogonal L = L := by
  classical
  let A : Set (Submodule K E) := {L | S ≤ L ∧ L ≤ ω.orthogonal L}
  obtain ⟨L,hL,hmax⟩ := (Set.toFinite A).exists_maximal ⟨S,le_rfl,hS⟩
  refine ⟨L,hL.1,le_antisymm ?_ hL.2⟩
  intro x hx
  have hU : (L ⊔ K ∙ x) ∈ A :=
    ⟨hL.1.trans le_sup_left,isotropic_sup_line ω ha L hL.2 x hx⟩
  exact hmax hU le_sup_left ((le_sup_right : K ∙ x ≤ L ⊔ K ∙ x) (Submodule.mem_span_singleton_self x))
end IsotropicExtension
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section QuotientExtension
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E) (S : Submodule K E)
omit [FiniteDimensional K E] in
theorem form_orthogonal_sum (ha : ω.IsAlt) (U : Submodule K E)
    (x y : U × ω.orthogonal U) :
    ω (x.1.val + x.2.val) (y.1.val + y.2.val) =
      ω x.1.val y.1.val + ω x.2.val y.2.val := by
  have hxy : ω x.1.val y.2.val = 0 := y.2.property x.1.val x.1.property
  have hyx : ω x.2.val y.1.val = 0 :=
    ha.isRefl _ _ (x.2.property y.1.val y.1.property)
  simp only [map_add, LinearMap.add_apply, hxy, hyx, add_zero, zero_add]
theorem exists_orthogonal_extension (ha : ω.IsAlt) (U : Submodule K E)
    (hU : (ω.restrict U).Nondegenerate) (f : U ≃ₗ[K] U)
    (hf : ∀ x y : U, ω (f x).val (f y).val = ω x.val y.val) :
    ∃ e : E ≃ₗ[K] E,
      (∀ x y, ω (e x) (e y) = ω x y) ∧
      (∀ x : U, e x.val = (f x).val) ∧
      (∀ x : ω.orthogonal U, e x.val = x.val) := by
  let c := U.prodEquivOfIsCompl (ω.orthogonal U)
    (ω.isCompl_orthogonal_of_restrict_nondegenerate ha.isRefl hU)
  let e := c.symm.trans ((f.prodCongr (LinearEquiv.refl K (ω.orthogonal U))).trans c)
  have he (x : U × ω.orthogonal U) : e (c x) = c (f x.1,x.2) := by
    simp [e]
  refine ⟨e, ?_, ?_, ?_⟩
  · intro x y
    obtain ⟨x,rfl⟩ := c.surjective x
    obtain ⟨y,rfl⟩ := c.surjective y
    rw [he,he]
    change ω ((f x.1).val + x.2.val) ((f y.1).val + y.2.val) =
      ω (x.1.val + x.2.val) (y.1.val + y.2.val)
    rw [form_orthogonal_sum ω ha U (f x.1,x.2) (f y.1,y.2),
      form_orthogonal_sum ω ha U x y,hf]
  · intro x
    have h := he (x,0)
    simpa [c] using h
  · intro x
    have h := he (0,x)
    simpa [c] using h
omit [FiniteDimensional K E] in
theorem reduction_section_isometry (ha : ω.IsAlt)
    (s : ReducedSpace ω S →ₗ[K] ω.orthogonal S)
    (hs : (reductionKernel ω S).mkQ.comp s = LinearMap.id)
    (x y : ReducedSpace ω S) :
    ω (s x).val (s y).val = symplecticReductionForm ω S ha x y := by
  have hx : (reductionKernel ω S).mkQ (s x) = x := LinearMap.congr_fun hs x
  have hy : (reductionKernel ω S).mkQ (s y) = y := LinearMap.congr_fun hs y
  calc
    _ = symplecticReductionForm ω S ha
      ((reductionKernel ω S).mkQ (s x)) ((reductionKernel ω S).mkQ (s y)) := rfl
    _ = _ := by rw [hx,hy]
theorem exists_reduction_isometry_extension (ha : ω.IsAlt)
    (hω : ω.Nondegenerate)
    (f : ReducedSpace ω S ≃ₗ[K] ReducedSpace ω S)
    (hf : ∀ x y, symplecticReductionForm ω S ha (f x) (f y) =
      symplecticReductionForm ω S ha x y) :
    ∃ e : E ≃ₗ[K] E,
      (∀ x y, ω (e x) (e y) = ω x y) ∧
      (∀ x : S, e x.val = x.val) ∧
      (∀ x : ω.orthogonal S, e x.val ∈ ω.orthogonal S) ∧
      (∀ x y : ω.orthogonal S, e x.val = y.val →
        (reductionKernel ω S).mkQ y = f ((reductionKernel ω S).mkQ x)) := by
  let π := (reductionKernel ω S).mkQ
  obtain ⟨s,hs⟩ := π.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (Submodule.mkQ_surjective _))
  let g : ReducedSpace ω S →ₗ[K] E := (ω.orthogonal S).subtype.comp s
  have hπ (x : ReducedSpace ω S) : π (s x) = x := LinearMap.congr_fun hs x
  have hg (x y : ReducedSpace ω S) : ω (g x) (g y) =
      symplecticReductionForm ω S ha x y :=
    reduction_section_isometry ω S ha s hs x y
  have hginj : Function.Injective g := by
    intro x y h
    have h' : s x = s y := Subtype.ext h
    simpa only [hπ] using congrArg π h'
  let U := g.range
  let j : ReducedSpace ω S ≃ₗ[K] U := LinearEquiv.ofInjective g hginj
  have hj (x : ReducedSpace ω S) : (j x).val = g x := rfl
  have hUn : (ω.restrict U).Nondegenerate := by
    have hn := symplecticReductionForm_nondegenerate ω S ha hω
    have left (x : U) (hx : ∀ y : U, ω x.val y.val = 0) : x = 0 := by
      obtain ⟨x,rfl⟩ := j.surjective x
      have hx0 : x = 0 := hn.1 x (fun y => by
        rw [← hg]
        exact hx (j y))
      simp [hx0]
    refine ⟨left, ?_⟩
    intro x hx
    apply left
    intro y
    exact ha.isRefl _ _ (hx y)
  let fU := j.symm.trans (f.trans j)
  have hfU (x y : U) : ω (fU x).val (fU y).val = ω x.val y.val := by
    obtain ⟨x,rfl⟩ := j.surjective x
    obtain ⟨y,rfl⟩ := j.surjective y
    change ω (j (f (j.symm (j x)))).val (j (f (j.symm (j y)))).val = ω (j x).val (j y).val
    simp only [j.symm_apply_apply,hj,hg,hf]
  obtain ⟨e,he,heU,heO⟩ := exists_orthogonal_extension ω ha U hUn fU hfU
  have hSO : S ≤ ω.orthogonal U := by
    intro x hx y hy
    obtain ⟨z,rfl⟩ := hy
    exact ha.isRefl _ _ ((s z).property x hx)
  have heS (x : S) : e x.val = x.val := heO ⟨x.val,hSO x.property⟩
  have heP (x : ω.orthogonal S) : e x.val ∈ ω.orthogonal S := by
    intro y hy
    have hyfix : e y = y := heS ⟨y,hy⟩
    rw [← hyfix,he]
    exact x.property y hy
  refine ⟨e,he,heS,heP,?_⟩
  intro x y hxy
  apply sub_eq_zero.mp
  apply (symplecticReductionForm_nondegenerate ω S ha hω).1
  intro z
  have hpair (a : ω.orthogonal S) (b : ReducedSpace ω S) :
      symplecticReductionForm ω S ha (π a) b = ω a.val (g b) := by
    calc
      _ = symplecticReductionForm ω S ha (π a) (π (s b)) := by rw [hπ]
      _ = _ := rfl
  have hegj (z : ReducedSpace ω S) : e (g z) = g (f z) := by
    have h := heU (j z)
    simpa only [fU,LinearEquiv.trans_apply,j.symm_apply_apply,hj] using h
  change symplecticReductionForm ω S ha (π y - f (π x)) z = 0
  rw [map_sub,LinearMap.sub_apply,sub_eq_zero]
  rw [hpair]
  calc
    ω y.val (g z) = ω (e x.val) (e (g (f.symm z))) := by
      rw [hxy,hegj,f.apply_symm_apply]
    _ = ω x.val (g (f.symm z)) := he _ _
    _ = symplecticReductionForm ω S ha (π x) (f.symm z) := (hpair x _).symm
    _ = symplecticReductionForm ω S ha (f (π x)) z := by
      simpa only [f.apply_symm_apply] using (hf (π x) (f.symm z)).symm
end QuotientExtension
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
theorem equal_fiber_card_identity {A B : Type*} [Finite A] [Finite B]
    (f : A → B) (b : B)
    (h : ∀ c : B, Nonempty ({a : A // f a = b} ≃ {a : A // f a = c})) :
    Nat.card {a : A // f a = b} * Nat.card B = Nat.card A := by
  classical
  let := Fintype.ofFinite A
  let := Fintype.ofFinite B
  have hc (c : B) : Nat.card {a : A // f a = c} = Nat.card {a : A // f a = b} :=
    (Nat.card_congr (h c).some).symm
  calc
    _ = ∑ c : B, Nat.card {a : A // f a = c} := by
      simp only [hc,Finset.sum_const,Finset.card_univ,smul_eq_mul,Nat.card_eq_fintype_card]
      exact Nat.mul_comm _ _
    _ = Nat.card (Σ c : B, {a : A // f a = c}) := by
      simp only [Nat.card_eq_fintype_card,Fintype.card_sigma]
    _ = Nat.card A := Nat.card_congr (Equiv.sigmaFiberEquiv f)
section ReductionLaws
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E) (S : Submodule K E)
theorem reduceSubspace_map (e : E ≃ₗ[K] E)
    (f : ReducedSpace ω S ≃ₗ[K] ReducedSpace ω S)
    (hP : (ω.orthogonal S).map e.toLinearMap = ω.orthogonal S)
    (hQ : ∀ x y : ω.orthogonal S, e x.val = y.val →
      (reductionKernel ω S).mkQ y = f ((reductionKernel ω S).mkQ x))
    (L : Submodule K E) :
    reduceSubspace ω S (L.map e.toLinearMap) =
      (reduceSubspace ω S L).map f.toLinearMap := by
  ext z
  constructor
  · rintro ⟨y,⟨x,hx,hxy⟩,rfl⟩
    have hxP : x ∈ ω.orthogonal S := by
      have hyP : y.val ∈ (ω.orthogonal S).map e.toLinearMap := hP.symm ▸ y.property
      obtain ⟨x',hx',hx'y⟩ := hyP
      have heq : x' = x := e.injective (hx'y.trans hxy.symm)
      exact heq ▸ hx'
    refine ⟨(reductionKernel ω S).mkQ ⟨x,hxP⟩,⟨⟨x,hxP⟩,hx,rfl⟩,?_⟩
    exact (hQ ⟨x,hxP⟩ y hxy).symm
  · rintro ⟨w,⟨x,hx,rfl⟩,rfl⟩
    have hyP : e x.val ∈ ω.orthogonal S := hP.le ⟨x.val,x.property,rfl⟩
    refine ⟨⟨e x.val,hyP⟩,⟨x.val,hx,rfl⟩,?_⟩
    exact hQ x ⟨e x.val,hyP⟩ rfl
theorem subspace_map_eq_of_fixed (e : E ≃ₗ[K] E) (U : Submodule K E)
    (h : ∀ x : U, e x.val = x.val) : U.map e.toLinearMap = U := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    change e y ∈ U
    rw [h ⟨y,hy⟩]
    exact hy
  · intro hx
    exact ⟨x,hx,h ⟨x,hx⟩⟩
abbrev AvoidanceSpace (A : Submodule K E) :=
  {L : Submodule K E // ω.orthogonal L = L ∧ L ⊓ S = A}
noncomputable def avoidanceIsometryEquiv (A : Submodule K E) (hAS : A ≤ S)
    (e : E ≃ₗ[K] E) (he : ∀ x y, ω (e x) (e y) = ω x y)
    (hS : ∀ x : S, e x.val = x.val) :
    AvoidanceSpace ω S A ≃ AvoidanceSpace ω S A := by
  have hSm := subspace_map_eq_of_fixed e S hS
  have hAm := subspace_map_eq_of_fixed e A (fun x => hS ⟨x.val,hAS x.property⟩)
  refine (Submodule.orderIsoMapComap e).toEquiv.subtypeEquiv ?_
  intro L
  change (ω.orthogonal L = L ∧ L ⊓ S = A) ↔
    (ω.orthogonal (L.map e.toLinearMap) = L.map e.toLinearMap ∧
      L.map e.toLinearMap ⊓ S = A)
  have hinj := (Submodule.orderIsoMapComap e).injective
  constructor
  · rintro ⟨hL,hLA⟩
    constructor
    · rw [orthogonal_map_of_isometry ω e he,hL]
    · calc
        L.map e.toLinearMap ⊓ S = L.map e.toLinearMap ⊓ S.map e.toLinearMap := by rw [hSm]
        _ = (L ⊓ S).map e.toLinearMap := (Submodule.map_inf e.toLinearMap e.injective).symm
        _ = A.map e.toLinearMap := congrArg (Submodule.map e.toLinearMap) hLA
        _ = A := hAm
  · rintro ⟨hL,hLA⟩
    constructor
    · apply hinj
      change (ω.orthogonal L).map e.toLinearMap = L.map e.toLinearMap
      rw [← orthogonal_map_of_isometry ω e he,hL]
    · apply hinj
      change (L ⊓ S).map e.toLinearMap = A.map e.toLinearMap
      rw [Submodule.map_inf e.toLinearMap e.injective,hSm,hAm,hLA]
variable [FiniteDimensional K E]
noncomputable def avoidanceReduction (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (hS : S ≤ ω.orthogonal S) (A : Submodule K E) :
    AvoidanceSpace ω S A →
      {T : Submodule K (ReducedSpace ω S) //
        (symplecticReductionForm ω S ha).orthogonal T = T} :=
  fun L => ⟨reduceSubspace ω S L.val,
    general_lagrangian_reduction ω S ha hω hS L.val L.property.1⟩
theorem avoidanceReduction_fiber_equiv (h2 : (2 : K) ≠ 0) (ha : ω.IsAlt)
    (hω : ω.Nondegenerate) (hS : S ≤ ω.orthogonal S)
    (A : Submodule K E) (hAS : A ≤ S)
    (T U : {T : Submodule K (ReducedSpace ω S) //
      (symplecticReductionForm ω S ha).orthogonal T = T}) :
    Nonempty ({L : AvoidanceSpace ω S A // avoidanceReduction ω S ha hω hS A L = T} ≃
      {L : AvoidanceSpace ω S A // avoidanceReduction ω S ha hω hS A L = U}) := by
  let B := symplecticReductionForm ω S ha
  obtain ⟨f,hf,hTU⟩ := lagrangian_transitivity B T.val h2
    (symplecticReductionForm_alt ω S ha)
    (symplecticReductionForm_nondegenerate ω S ha hω) T.property U.val U.property
  obtain ⟨e,he,heS,_,heQ⟩ := exists_reduction_isometry_extension ω S ha hω f hf
  let a := avoidanceIsometryEquiv ω S A hAS e he heS
  have hPm : (ω.orthogonal S).map e.toLinearMap = ω.orthogonal S := by
    rw [← orthogonal_map_of_isometry ω e he,subspace_map_eq_of_fixed e S heS]
  have hred (L : AvoidanceSpace ω S A) :
      (avoidanceReduction ω S ha hω hS A (a L)).val =
        (avoidanceReduction ω S ha hω hS A L).val.map f.toLinearMap :=
    reduceSubspace_map ω S e f hPm heQ L.val
  refine ⟨a.subtypeEquiv ?_⟩
  intro L
  constructor
  · intro hL
    apply Subtype.ext
    rw [hred,hL]
    exact hTU
  · intro hL
    apply Subtype.ext
    apply (Submodule.orderIsoMapComap f).injective
    change (avoidanceReduction ω S ha hω hS A L).val.map f.toLinearMap = T.val.map f.toLinearMap
    rw [← hred,hL,hTU]
variable [Finite E]
theorem avoidanceReduction_uniform (h2 : (2 : K) ≠ 0) (ha : ω.IsAlt)
    (hω : ω.Nondegenerate) (hS : S ≤ ω.orthogonal S)
    (A : Submodule K E) (hAS : A ≤ S)
    (T : {T : Submodule K (ReducedSpace ω S) //
      (symplecticReductionForm ω S ha).orthogonal T = T}) :
    Nat.card {L : AvoidanceSpace ω S A // avoidanceReduction ω S ha hω hS A L = T} *
      Nat.card {U : Submodule K (ReducedSpace ω S) //
        (symplecticReductionForm ω S ha).orthogonal U = U} =
        Nat.card (AvoidanceSpace ω S A) := by
  classical
  let := Fintype.ofFinite E
  let := Fintype.ofFinite (ω.orthogonal S)
  exact equal_fiber_card_identity (avoidanceReduction ω S ha hω hS A) T
    (avoidanceReduction_fiber_equiv ω S h2 ha hω hS A hAS T)
end ReductionLaws
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
theorem exists_linearEquiv_extension
    {K E F : Type*} [Field K] [AddCommGroup E] [Module K E]
    [AddCommGroup F] [Module K F] [FiniteDimensional K E] [FiniteDimensional K F]
    (U : Submodule K E) (W : Submodule K F)
    (hEF : finrank K E = finrank K F) (f : U ≃ₗ[K] W) :
    ∃ e : E ≃ₗ[K] F, ∀ u : U, e u.val = (f u).val := by
  obtain ⟨U',hU⟩ := U.exists_isCompl
  obtain ⟨W',hW⟩ := W.exists_isCompl
  let cU := Submodule.prodEquivOfIsCompl U U' hU
  let cW := Submodule.prodEquivOfIsCompl W W' hW
  have hdim : finrank K U' = finrank K W' := by
    have h1 := Submodule.finrank_add_eq_of_isCompl hU
    have h2 := Submodule.finrank_add_eq_of_isCompl hW
    have h3 := f.finrank_eq
    omega
  let g : U' ≃ₗ[K] W' := LinearEquiv.ofFinrankEq U' W' hdim
  let e := cU.symm.trans ((f.prodCongr g).trans cW)
  refine ⟨e, ?_⟩
  intro u
  have hu : cU (u,0) = u.val := by simp [cU]
  change cW ((f.prodCongr g) (cU.symm u.val)) = (f u).val
  rw [← hu, cU.symm_apply_apply]
  simp [cW]
theorem subspace_transitivity
    {K E F : Type*} [Field K] [AddCommGroup E] [Module K E]
    [AddCommGroup F] [Module K F] [FiniteDimensional K E] [FiniteDimensional K F]
    (U : Submodule K E) (W : Submodule K F)
    (hEF : finrank K E = finrank K F) (hUW : finrank K U = finrank K W) :
    ∃ e : E ≃ₗ[K] F, U.map e.toLinearMap = W := by
  let f : U ≃ₗ[K] W := LinearEquiv.ofFinrankEq U W hUW
  obtain ⟨e,he⟩ := exists_linearEquiv_extension U W hEF f
  refine ⟨e, ?_⟩
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    change e y ∈ W
    rw [he ⟨y,hy⟩]
    exact (f ⟨y,hy⟩).property
  · intro hx
    let u := f.symm ⟨x,hx⟩
    refine ⟨u.val,u.property, ?_⟩
    change e u.val = x
    rw [he]
    exact congrArg Subtype.val (f.apply_symm_apply ⟨x,hx⟩)
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section IsotropicTransitivity
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E] [Finite E]
variable (ω : LinearMap.BilinForm K E)
theorem isotropic_transitivity (h2 : (2 : K) ≠ 0) (ha : ω.IsAlt)
    (hω : ω.Nondegenerate) (S T : Submodule K E)
    (hS : S ≤ ω.orthogonal S) (hT : T ≤ ω.orthogonal T)
    (hST : finrank K S = finrank K T) :
    ∃ e : E ≃ₗ[K] E, (∀ x y, ω (e x) (e y) = ω x y) ∧ S.map e.toLinearMap = T := by
  obtain ⟨L,hSL,hL⟩ := exists_containing_lagrangian ω ha S hS
  obtain ⟨M,hTM,hM⟩ := exists_containing_lagrangian ω ha T hT
  obtain ⟨eL,hEL,hωL⟩ := exists_lagrangian_coordinates ω L h2 ha hω hL
  obtain ⟨eM,hEM,hωM⟩ := exists_lagrangian_coordinates ω M h2 ha hω hM
  have hdim : finrank K L = finrank K M := by
    have h1 := self_orthogonal_twice_finrank ω L hω hL
    have h2 := self_orthogonal_twice_finrank ω M hω hM
    omega
  let U := S.comap L.subtype
  let W := T.comap M.subtype
  have hUW : finrank K U = finrank K W := by
    exact (Submodule.comapSubtypeEquivOfLe hSL).finrank_eq.trans
      (hST.trans (Submodule.comapSubtypeEquivOfLe hTM).finrank_eq.symm)
  obtain ⟨f,hf⟩ := subspace_transitivity U W hdim hUW
  let c : (L × Module.Dual K L) ≃ₗ[K] (M × Module.Dual K M) :=
    f.prodCongr f.symm.dualMap
  have hc (x y : L × Module.Dual K L) :
      canonicalSymplectic (c x) (c y) = canonicalSymplectic x y := by
    simp [c,canonicalSymplectic_apply]
  let e := eL.symm.trans (c.trans eM)
  have he (l : L) : e l.val = (f l).val := by
    change eM (c (eL.symm l.val)) = (f l).val
    rw [← hEL l, eL.symm_apply_apply]
    simpa [c] using hEM (f l)
  refine ⟨e, ?_, ?_⟩
  · intro x y
    change ω (eM (c (eL.symm x))) (eM (c (eL.symm y))) = ω x y
    rw [hωM, hc, ← hωL, eL.apply_symm_apply, eL.apply_symm_apply]
  · ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      change e y ∈ T
      rw [he ⟨y,hSL hy⟩]
      have hfu : f ⟨y,hSL hy⟩ ∈ U.map f.toLinearMap := ⟨⟨y,hSL hy⟩,hy,rfl⟩
      exact hf.le hfu
    · intro hx
      have hw : (⟨x,hTM hx⟩ : M) ∈ W := hx
      obtain ⟨l,hl,hel⟩ := hf.ge hw
      refine ⟨l.val,hl, ?_⟩
      change e l.val = x
      rw [he]
      exact congrArg Subtype.val hel
end IsotropicTransitivity
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section TransversePairs
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E)
theorem transverse_isCompl (hω : ω.Nondegenerate)
    (L M : Submodule K E) (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M)
    (hLM : L ⊓ M = ⊥) : IsCompl L M := by
  have h1 := self_orthogonal_twice_finrank ω L hω hL
  have h2 := self_orthogonal_twice_finrank ω M hω hM
  apply (Submodule.isCompl_iff_disjoint L M (by omega)).mpr
  exact disjoint_iff.mpr hLM
theorem exists_transverse_pair_coordinates (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (L M : Submodule K E) (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M)
    (hLM : L ⊓ M = ⊥) :
    ∃ e : (L × Module.Dual K L) ≃ₗ[K] E,
      (∀ x, e x ∈ L ↔ x.2 = 0) ∧ (∀ x, e x ∈ M ↔ x.1 = 0) ∧
      ∀ x y, ω (e x) (e y) = canonicalSymplectic x y := by
  let p := (symplecticProjection ω L).comp M.subtype
  have hp : Function.Injective p := by
    apply (LinearMap.ker_eq_bot).mp
    apply (Submodule.eq_bot_iff _).mpr
    intro m hm
    apply Subtype.ext
    have hml : m.val ∈ L := (symplecticProjection_ker ω L hL).le hm
    have hz : m.val ∈ L ⊓ M := ⟨hml,m.property⟩
    change m.val = 0
    simpa only [hLM,Submodule.mem_bot] using hz
  have hd : finrank K M = finrank K (Module.Dual K L) := by
    rw [Subspace.dual_finrank_eq]
    have h1 := self_orthogonal_twice_finrank ω L hω hL
    have h2 := self_orthogonal_twice_finrank ω M hω hM
    omega
  let f : M ≃ₗ[K] Module.Dual K L := LinearEquiv.ofBijective p
    ⟨hp,(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mp hp⟩
  let d := Submodule.prodEquivOfIsCompl L M (transverse_isCompl ω hω L M hL hM hLM)
  let e := ((LinearEquiv.refl K L).prodCongr f.symm).trans d
  have he (x : L × Module.Dual K L) : e x = x.1.val + (f.symm x.2).val := rfl
  have hproj (x : L × Module.Dual K L) : symplecticProjection ω L (e x) = x.2 := by
    rw [he,map_add]
    have hl : symplecticProjection ω L x.1.val = 0 :=
      (symplecticProjection_ker ω L hL).ge x.1.property
    rw [hl,zero_add]
    exact f.apply_symm_apply x.2
  refine ⟨e, ?_, ?_, ?_⟩
  · intro x
    constructor
    · intro hx
      have hz : symplecticProjection ω L (e x) = 0 :=
        (symplecticProjection_ker ω L hL).ge hx
      rwa [hproj] at hz
    · intro hx
      apply (symplecticProjection_ker ω L hL).le
      change symplecticProjection ω L (e x) = 0
      rw [hproj,hx]
  · intro x
    constructor
    · intro hx
      have hv : x.1.val ∈ M := by
        have hh := M.sub_mem hx (f.symm x.2).property
        simpa only [he,add_sub_cancel_right] using hh
      have hz : x.1.val ∈ L ⊓ M := ⟨x.1.property,hv⟩
      apply Subtype.ext
      change x.1.val = 0
      simpa only [hLM,Submodule.mem_bot] using hz
    · intro hx
      rw [he,hx]
      simp
  · intro x y
    have hLL : ω x.1.val y.1.val = 0 := (hL.ge y.1.property) x.1.val x.1.property
    have hMM : ω (f.symm x.2).val (f.symm y.2).val = 0 :=
      (hM.ge (f.symm y.2).property) (f.symm x.2).val (f.symm x.2).property
    have hfg (g : Module.Dual K L) (l : L) : ω l.val (f.symm g).val = g l :=
      LinearMap.congr_fun (f.apply_symm_apply g) l
    rw [he,he]
    simp only [map_add,LinearMap.add_apply,hLL,hMM,
      ← ha.neg_eq y.1.val (f.symm x.2).val,hfg,canonicalSymplectic_apply]
    ring
end TransversePairs
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
 theorem subspace_map_eq_of_mem_iff
    {K E F : Type*} [Field K] [AddCommGroup E] [Module K E]
    [AddCommGroup F] [Module K F] (e : E ≃ₗ[K] F)
    (U : Submodule K E) (W : Submodule K F)
    (h : ∀ x, e x ∈ W ↔ x ∈ U) : U.map e.toLinearMap = W := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact (h y).mpr hy
  · intro hx
    refine ⟨e.symm x,(h (e.symm x)).mp ?_,e.apply_symm_apply x⟩
    simpa only [e.apply_symm_apply] using hx
section PairTransitivity
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E)
theorem transverse_pair_transitivity (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (L M L' M' : Submodule K E)
    (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M)
    (hL' : ω.orthogonal L' = L') (hM' : ω.orthogonal M' = M')
    (hLM : L ⊓ M = ⊥) (hLM' : L' ⊓ M' = ⊥) :
    ∃ e : E ≃ₗ[K] E, (∀ x y, ω (e x) (e y) = ω x y) ∧
      L.map e.toLinearMap = L' ∧ M.map e.toLinearMap = M' := by
  obtain ⟨eL,hEL,hEM,hωL⟩ := exists_transverse_pair_coordinates ω ha hω L M hL hM hLM
  obtain ⟨eM,hEL',hEM',hωM⟩ := exists_transverse_pair_coordinates ω ha hω L' M' hL' hM' hLM'
  have hdim : finrank K L = finrank K L' := by
    have h1 := self_orthogonal_twice_finrank ω L hω hL
    have h2 := self_orthogonal_twice_finrank ω L' hω hL'
    omega
  let f : L ≃ₗ[K] L' := LinearEquiv.ofFinrankEq L L' hdim
  let c : (L × Module.Dual K L) ≃ₗ[K] (L' × Module.Dual K L') :=
    f.prodCongr f.symm.dualMap
  have hc (x y : L × Module.Dual K L) :
      canonicalSymplectic (c x) (c y) = canonicalSymplectic x y := by
    simp [c,canonicalSymplectic_apply]
  let e := eL.symm.trans (c.trans eM)
  refine ⟨e, ?_, ?_, ?_⟩
  · intro x y
    change ω (eM (c (eL.symm x))) (eM (c (eL.symm y))) = ω x y
    rw [hωM, hc, ← hωL, eL.apply_symm_apply, eL.apply_symm_apply]
  · apply subspace_map_eq_of_mem_iff e
    intro x
    change eM (c (eL.symm x)) ∈ L' ↔ x ∈ L
    rw [hEL']
    change f.symm.dualMap ((eL.symm x).2) = 0 ↔ x ∈ L
    rw [LinearEquiv.map_eq_zero_iff]
    simpa only [eL.apply_symm_apply] using (hEL (eL.symm x)).symm
  · apply subspace_map_eq_of_mem_iff e
    intro x
    change eM (c (eL.symm x)) ∈ M' ↔ x ∈ M
    rw [hEM']
    change f ((eL.symm x).1) = 0 ↔ x ∈ M
    rw [LinearEquiv.map_eq_zero_iff]
    simpa only [eL.apply_symm_apply] using (hEM (eL.symm x)).symm
end PairTransitivity
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section PairReduction
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E) (S : Submodule K E)
theorem liftReduction_inf (T U : Submodule K (ReducedSpace ω S)) :
    liftReduction ω S (T ⊓ U) = liftReduction ω S T ⊓ liftReduction ω S U := by
  ext x
  simp only [mem_liftReduction,Submodule.mem_inf]
  tauto
theorem liftReduction_bot (hS : S ≤ ω.orthogonal S) :
    liftReduction ω S ⊥ = S := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxP,hxQ⟩ := (mem_liftReduction ω S ⊥ x).mp hx
    exact (Submodule.Quotient.mk_eq_zero (reductionKernel ω S)).mp hxQ
  · intro hx
    apply (mem_liftReduction ω S ⊥ x).mpr
    refine ⟨hS hx, ?_⟩
    exact (Submodule.Quotient.mk_eq_zero (reductionKernel ω S)).mpr hx
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
theorem pairing_from_lagrangian_surjective (ha : ω.IsAlt)
    (S N : Submodule K E) (hN : ω.orthogonal N = N) (hSN : S ⊓ N = ⊥) :
    Function.Surjective ((symplecticProjection ω S).comp N.subtype) := by
  let p := (symplecticProjection ω S).comp N.subtype
  apply LinearMap.dualMap_injective_iff.mp
  apply (LinearMap.ker_eq_bot).mp
  apply (Submodule.eq_bot_iff _).mpr
  intro z hz
  obtain ⟨s,rfl⟩ := (Module.evalEquiv K S).surjective z
  have hsN : s.val ∈ N := by
    apply hN.le
    intro n hn
    have hh := LinearMap.congr_fun (LinearMap.mem_ker.mp hz) (⟨n,hn⟩ : N)
    change ω s.val n = 0 at hh
    exact ha.isRefl _ _ hh
  have hs0 : s = 0 := by
    apply Subtype.ext
    change s.val = 0
    exact hSN.le ⟨s.property,hsN⟩
  rw [hs0,map_zero]
theorem exists_pair_block (ha : ω.IsAlt)
    (S N : Submodule K E) (hS : S ≤ ω.orthogonal S)
    (hN : ω.orthogonal N = N) (hSN : S ⊓ N = ⊥) :
    ∃ B : Submodule K E, (ω.restrict B).Nondegenerate ∧ S ≤ B ∧
      ∃ e : (S × Module.Dual K S) ≃ₗ[K] B,
        (∀ s : S, (e (s,0)).val = s.val) ∧
        (∀ f : Module.Dual K S, (e (0,f)).val ∈ N) ∧
        ∀ x y, ω (e x).val (e y).val = canonicalSymplectic x y := by
  let p := (symplecticProjection ω S).comp N.subtype
  obtain ⟨s,hs⟩ := p.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (pairing_from_lagrangian_surjective ω ha S N hN hSN))
  let g := N.subtype.comp s
  have hpair (l : S) (f : Module.Dual K S) : ω l.val (g f) = f l :=
    LinearMap.congr_fun (LinearMap.congr_fun hs f) l
  let f : (S × Module.Dual K S) →ₗ[K] E :=
    S.subtype.comp (LinearMap.fst K S (Module.Dual K S)) +
    g.comp (LinearMap.snd K S (Module.Dual K S))
  have hf (x : S × Module.Dual K S) : f x = x.1.val + g x.2 := rfl
  have hform (x y : S × Module.Dual K S) :
      ω (f x) (f y) = canonicalSymplectic x y := by
    have hSS : ω x.1.val y.1.val = 0 := hS y.1.property x.1.val x.1.property
    have hNN : ω (g x.2) (g y.2) = 0 := (hN.ge (s y.2).property) _ (s x.2).property
    rw [hf,hf]
    simp only [map_add,LinearMap.add_apply,hSS,hNN,
      ← ha.neg_eq y.1.val (g x.2),hpair,canonicalSymplectic_apply]
    ring
  have hinj : Function.Injective f := by
    apply (LinearMap.ker_eq_bot).mp
    apply (Submodule.eq_bot_iff _).mpr
    intro x hx
    apply canonicalSymplectic_nondegenerate.1
    intro y
    rw [← hform,hx]
    simp
  let B := f.range
  let e : (S × Module.Dual K S) ≃ₗ[K] B := LinearEquiv.ofInjective f hinj
  have he (x : S × Module.Dual K S) : (e x).val = f x := rfl
  have hleft (x : B) (hx : ∀ y : B, ω x.val y.val = 0) : x = 0 := by
    obtain ⟨z,rfl⟩ := e.surjective x
    have hz : z = 0 := canonicalSymplectic_nondegenerate.1 z (fun w => by
      rw [← hform]
      exact hx (e w))
    rw [hz,map_zero]
  refine ⟨B,⟨hleft, ?_⟩, ?_,e, ?_, ?_, ?_⟩
  · intro x hx
    apply hleft
    intro y
    exact ha.isRefl _ _ (hx y)
  · intro x hx
    refine ⟨(⟨x,hx⟩,0),?_⟩
    simp [hf]
  · intro l
    simp [he,hf]
  · intro l
    change (0 : E) + (s l).val ∈ N
    simpa only [zero_add] using (s l).property
  · intro x y
    exact hform x y
theorem forced_orthogonal_splitting (ha : ω.IsAlt)
    (B L : Submodule K E) (hB : (ω.restrict B).Nondegenerate)
    (hL : L ≤ ω.orthogonal L) (T : Submodule K B)
    (hT : (ω.restrict B).orthogonal T = T) (hTL : T.map B.subtype ≤ L) :
    L = T.map B.subtype ⊔ (L ⊓ ω.orthogonal B) := by
  let c := B.prodEquivOfIsCompl (ω.orthogonal B)
    (ω.isCompl_orthogonal_of_restrict_nondegenerate ha.isRefl hB)
  apply le_antisymm
  · intro x hx
    let b := (c.symm x).1
    let p := (c.symm x).2
    have hxp : b.val + p.val = x := c.apply_symm_apply x
    have hbT : b ∈ T := by
      apply hT.le
      intro t ht
      have htL : t.val ∈ L := hTL ⟨t,ht,rfl⟩
      have htx : ω t.val x = 0 := hL hx t.val htL
      have htp : ω t.val p.val = 0 := p.property t.val t.property
      rw [← hxp,map_add,htp,add_zero] at htx
      exact htx
    have hbL : b.val ∈ L := hTL ⟨b,hbT,rfl⟩
    have hpL : p.val ∈ L := by
      have hp : p.val = x - b.val := by rw [← hxp]; abel
      rw [hp]
      exact L.sub_mem hx hbL
    exact Submodule.mem_sup.mpr ⟨b.val,⟨b,hbT,rfl⟩,p.val,⟨hpL,p.property⟩,hxp⟩
  · exact sup_le hTL inf_le_left
theorem split_residual_lagrangian (ha : ω.IsAlt)
    (B L : Submodule K E) (hB : (ω.restrict B).Nondegenerate)
    (hL : ω.orthogonal L = L) (T : Submodule K B)
    (hT : (ω.restrict B).orthogonal T = T) (hTL : T.map B.subtype ≤ L) :
    (ω.restrict (ω.orthogonal B)).orthogonal
      (L.comap (ω.orthogonal B).subtype) = L.comap (ω.orthogonal B).subtype := by
  have hs := forced_orthogonal_splitting ω ha B L hB hL.ge T hT hTL
  ext x
  constructor
  · intro hx
    change x.val ∈ L
    apply hL.le
    intro y hy
    rw [hs] at hy
    obtain ⟨b,⟨bt,hbt,rfl⟩,p,hp,rfl⟩ := Submodule.mem_sup.mp hy
    rw [map_add,LinearMap.add_apply]
    have hb : ω bt.val x.val = 0 := x.property bt.val bt.property
    have hq : ω p x.val = 0 := hx (⟨p,hp.2⟩ : ω.orthogonal B) hp.1
    change ω bt.val x.val + ω p x.val = 0
    rw [hb,hq,add_zero]
  · intro hx y hy
    exact hL.ge hx y.val hy
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
def horizontalSpace : Submodule K (V × Module.Dual K V) :=
  (LinearMap.snd K V (Module.Dual K V)).ker
@[simp] theorem mem_horizontalSpace (p : V × Module.Dual K V) :
    p ∈ horizontalSpace (K := K) ↔ p.2 = 0 := Iff.rfl
theorem horizontalSpace_selforthogonal :
    canonicalSymplectic.orthogonal (horizontalSpace (K := K) (V := V)) = horizontalSpace := by
  ext x
  constructor
  · intro hx
    change x.2 = 0
    ext v
    have hh := hx (v,0) (by rfl)
    simpa only [canonicalSymplectic_apply,LinearMap.zero_apply,sub_zero] using hh
  · intro hx v hv
    change x.2 v.1 - v.2 x.1 = 0
    rw [(mem_horizontalSpace x).mp hx,(mem_horizontalSpace v).mp hv]
    simp
noncomputable def verticalSpaceEquiv : Module.Dual K V ≃ₗ[K]
    verticalSpace (K := K) (V := V) where
  toFun f := ⟨(0,f),rfl⟩
  invFun x := x.val.2
  map_add' _ _ := by ext <;> simp
  map_smul' a f := by ext <;> simp
  left_inv _ := rfl
  right_inv x := by
    apply Subtype.ext
    exact Prod.ext ((mem_verticalSpace x.val).mp x.property).symm rfl
end Horizontal
section TripleOneBlock
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E)
theorem triple_pair_block (ha : ω.IsAlt)
    (L M N : Submodule K E) (hL : ω.orthogonal L = L)
    (hM : ω.orthogonal M = M) (hN : ω.orthogonal N = N)
    (hzero : (L ⊓ M) ⊓ N = ⊥) :
    ∃ B Q : Submodule K E,
      (ω.restrict B).Nondegenerate ∧ (L ⊓ M) ≤ B ∧ Q ≤ B ∧ Q ≤ N ∧
      finrank K Q = finrank K ↥(L ⊓ M) ∧
      B = (L ⊓ M) ⊔ Q ∧
      L = (L ⊓ M) ⊔ (L ⊓ ω.orthogonal B) ∧
      M = (L ⊓ M) ⊔ (M ⊓ ω.orthogonal B) ∧
      N = Q ⊔ (N ⊓ ω.orthogonal B) ∧
      L ⊓ N ≤ ω.orthogonal B ∧ M ⊓ N ≤ ω.orthogonal B ∧
      (L ⊓ ω.orthogonal B) ⊓ (M ⊓ ω.orthogonal B) = ⊥ ∧
      (∀ A ∈ ({L,M,N} : Set (Submodule K E)),
        (ω.restrict (ω.orthogonal B)).orthogonal (A.comap (ω.orthogonal B).subtype) =
          A.comap (ω.orthogonal B).subtype) ∧
      ∃ e : (↥(L ⊓ M) × Module.Dual K ↥(L ⊓ M)) ≃ₗ[K] B,
        (∀ s : ↥(L ⊓ M), (e (s,0)).val = s.val) ∧
        (verticalSpace.map e.toLinearMap).map B.subtype = Q ∧
        ∀ x y, ω (e x).val (e y).val = canonicalSymplectic x y := by
  let S := L ⊓ M
  have hS : S ≤ ω.orthogonal S := by
    intro s hs t ht
    exact hL.ge hs.1 t ht.1
  obtain ⟨B,hB,hSB,e,heS,heN,heform⟩ := exists_pair_block ω ha S N hS hN hzero
  let T : Submodule K B := (horizontalSpace (K := K) (V := S)).map e.toLinearMap
  let U : Submodule K B := (verticalSpace (K := K) (V := S)).map e.toLinearMap
  let Q := U.map B.subtype
  have hT : (ω.restrict B).orthogonal T = T := by
    change (ω.restrict B).orthogonal (horizontalSpace.map e.toLinearMap) = horizontalSpace.map e.toLinearMap
    rw [orthogonal_map_isometry_between (canonicalSymplectic (K := K) (V := S))
      (ω.restrict B) e (fun x y => heform x y),horizontalSpace_selforthogonal]
  have hU : (ω.restrict B).orthogonal U = U := by
    change (ω.restrict B).orthogonal (verticalSpace.map e.toLinearMap) = verticalSpace.map e.toLinearMap
    rw [orthogonal_map_isometry_between (canonicalSymplectic (K := K) (V := S))
      (ω.restrict B) e (fun x y => heform x y)]
    exact congrArg (fun U : Submodule K (S × Module.Dual K S) => U.map e.toLinearMap)
      (verticalLagrangian (K := K) (V := S)).property
  have hTS : T.map B.subtype = S := by
    ext x
    constructor
    · rintro ⟨b,⟨z,hz,rfl⟩,rfl⟩
      obtain ⟨s,f⟩ := z
      have hf : f = 0 := hz
      subst f
      change (e (s,0)).val ∈ S
      rw [heS]
      exact s.property
    · intro hx
      refine ⟨e (⟨x,hx⟩,0),⟨(⟨x,hx⟩,0),rfl,rfl⟩,?_⟩
      exact heS ⟨x,hx⟩
  have hQN : Q ≤ N := by
    rintro x ⟨b,⟨z,hz,rfl⟩,rfl⟩
    obtain ⟨s,f⟩ := z
    have hs : s = 0 := hz
    subst s
    exact heN f
  have hQB : Q ≤ B := by rintro x ⟨b,_,rfl⟩; exact b.property
  have hdim : finrank K Q = finrank K S := by
    change finrank K (U.map B.subtype) = finrank K S
    rw [← (Submodule.equivMapOfInjective B.subtype B.injective_subtype U).finrank_eq]
    change finrank K (verticalSpace.map e.toLinearMap) = finrank K S
    rw [e.finrank_map_eq]
    rw [← (verticalSpaceEquiv (K := K) (V := S)).finrank_eq,Subspace.dual_finrank_eq]
  have hBQ : B = S ⊔ Q := by
    apply le_antisymm
    · intro x hx
      obtain ⟨z,hz⟩ := e.surjective ⟨x,hx⟩
      have hsum : x = z.1.val + (e (0,z.2)).val := by
        have headd := e.map_add (z.1,0) (0,z.2)
        have headd' := congrArg Subtype.val headd
        simp only [Prod.mk_add_mk,add_zero,zero_add] at headd'
        rw [hz] at headd'
        change x = (e (z.1,0)).val + (e (0,z.2)).val at headd'
        rw [heS] at headd'
        exact headd'
      rw [hsum]
      exact Submodule.add_mem_sup z.1.property ⟨e (0,z.2),⟨(0,z.2),rfl,rfl⟩,rfl⟩
    · exact sup_le hSB hQB
  have hsplitL : L = S ⊔ (L ⊓ ω.orthogonal B) := by
    simpa only [hTS] using forced_orthogonal_splitting ω ha B L hB hL.ge T hT
      (by rw [hTS]; exact inf_le_left)
  have hsplitM : M = S ⊔ (M ⊓ ω.orthogonal B) := by
    simpa only [hTS] using forced_orthogonal_splitting ω ha B M hB hM.ge T hT
      (by rw [hTS]; exact inf_le_right)
  have hsplitN : N = Q ⊔ (N ⊓ ω.orthogonal B) :=
    forced_orthogonal_splitting ω ha B N hB hN.ge U hU hQN
  have hsurvive (A : Submodule K E) (hA : ω.orthogonal A = A) (hSA : S ≤ A) :
      A ⊓ N ≤ ω.orthogonal B := by
    intro x hx b hb
    rw [hBQ] at hb
    obtain ⟨s,hs,q,hq,rfl⟩ := Submodule.mem_sup.mp hb
    simp only [map_add,LinearMap.add_apply]
    rw [hA.ge hx.1 s (hSA hs),hN.ge hx.2 q (hQN hq),add_zero]
  have hdisj : (L ⊓ ω.orthogonal B) ⊓ (M ⊓ ω.orthogonal B) = ⊥ := by
    apply (Submodule.eq_bot_iff _).mpr
    intro x hx
    have hb : x ∈ B := hSB ⟨hx.1.1,hx.2.1⟩
    exact (ω.isCompl_orthogonal_of_restrict_nondegenerate ha.isRefl hB).disjoint.le_bot
      ⟨hb,hx.1.2⟩
  refine ⟨B,Q,hB,hSB,hQB,hQN,hdim,hBQ,hsplitL,hsplitM,hsplitN,
    hsurvive L hL inf_le_left,hsurvive M hM inf_le_right,hdisj,?_,e,heS,rfl,heform⟩
  intro A hA
  rcases (show A = L ∨ A = M ∨ A = N from hA) with hA | hA | hA
  · subst A
    exact split_residual_lagrangian ω ha B L hB hL T hT (by rw [hTS]; exact inf_le_left)
  · subst A
    exact split_residual_lagrangian ω ha B M hB hM T hT (by rw [hTS]; exact inf_le_right)
  · subst A
    exact split_residual_lagrangian ω ha B N hB hN U hU hQN
end TripleOneBlock
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section OrthogonalReduction
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E)
theorem exists_complement_reduction_equiv (ha : ω.IsAlt)
    (S B : Submodule K E) (hB : (ω.restrict B).Nondegenerate)
    (hSB : S ≤ B) (hBS : B ⊓ ω.orthogonal S = S) :
    ∃ e : ω.orthogonal B ≃ₗ[K] ReducedSpace ω S,
      (∀ x : ω.orthogonal B, e x = (reductionKernel ω S).mkQ
        ⟨x.val,by intro s hs; exact x.property s (hSB hs)⟩) ∧
      (∀ x y, symplecticReductionForm ω S ha (e x) (e y) = ω x.val y.val) ∧
      ∀ L : Submodule K E, L = (L ⊓ B) ⊔ (L ⊓ ω.orthogonal B) →
        (L.comap (ω.orthogonal B).subtype).map e.toLinearMap = reduceSubspace ω S L := by
  let U := ω.orthogonal B
  have hUS : U ≤ ω.orthogonal S := by
    intro x hx s hs
    exact hx s (hSB hs)
  let f : U →ₗ[K] ReducedSpace ω S :=
    (reductionKernel ω S).mkQ.comp (Submodule.inclusion hUS)
  have hf (x : U) : f x = (reductionKernel ω S).mkQ ⟨x.val,hUS x.property⟩ := rfl
  have hc := ω.isCompl_orthogonal_of_restrict_nondegenerate ha.isRefl hB
  have hinj : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    apply (Submodule.eq_bot_iff _).mpr
    intro x hx
    have hxS : x.val ∈ S := (Submodule.Quotient.mk_eq_zero (reductionKernel ω S)).mp hx
    apply Subtype.ext
    exact hc.disjoint.le_bot ⟨hSB hxS,x.property⟩
  have hsurj : Function.Surjective f := by
    intro z
    induction z using Submodule.Quotient.induction_on with
    | H z =>
      have hz : z.val ∈ B ⊔ U := hc.sup_eq_top.symm ▸ Submodule.mem_top
      obtain ⟨b,hb,u,hu,hbu⟩ := Submodule.mem_sup.mp hz
      have hbS : b ∈ S := by
        apply hBS.le
        refine ⟨hb,?_⟩
        have hbval : b = z.val-u := by rw [←hbu]; abel
        rw [hbval]
        exact (ω.orthogonal S).sub_mem z.property (hUS hu)
      refine ⟨⟨u,hu⟩,?_⟩
      apply (Submodule.Quotient.eq (reductionKernel ω S)).mpr
      change u-z.val ∈ S
      have huval : u-z.val = -b := by rw [←hbu]; abel
      rw [huval]
      exact S.neg_mem hbS
  let e : U ≃ₗ[K] ReducedSpace ω S := LinearEquiv.ofBijective f ⟨hinj,hsurj⟩
  refine ⟨e,fun _ => rfl,fun _ _ => rfl,?_⟩
  intro L hL
  ext z
  constructor
  · rintro ⟨u,hu,rfl⟩
    exact ⟨⟨u.val,hUS u.property⟩,hu,rfl⟩
  · rintro ⟨x,hx,rfl⟩
    have hx' : x.val ∈ (L ⊓ B) ⊔ (L ⊓ U) := hL ▸ hx
    obtain ⟨b,hb,u,hu,hbu⟩ := Submodule.mem_sup.mp hx'
    have hbS : b ∈ S := by
      apply hBS.le
      refine ⟨hb.2,?_⟩
      have hbval : b = x.val-u := by rw [←hbu]; abel
      rw [hbval]
      exact (ω.orthogonal S).sub_mem x.property (hUS hu.2)
    refine ⟨⟨u,hu.2⟩,hu.1,?_⟩
    change (reductionKernel ω S).mkQ ⟨u,hUS hu.2⟩ = (reductionKernel ω S).mkQ x
    apply (Submodule.Quotient.eq (reductionKernel ω S)).mpr
    change u-x.val ∈ S
    have huval : u-x.val = -b := by rw [←hbu]; abel
    rw [huval]
    exact S.neg_mem hbS
end OrthogonalReduction
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ReductionInStages
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E) (ha : ω.IsAlt)
theorem exists_reduction_in_stages (S T : Submodule K E)
    (hST : S ≤ T) (hT : T ≤ ω.orthogonal T) :
    ∃ e : ReducedSpace ω T ≃ₗ[K]
        ReducedSpace (symplecticReductionForm ω S ha) (reduceSubspace ω S T),
      (∀ x y, symplecticReductionForm (symplecticReductionForm ω S ha)
          (reduceSubspace ω S T) (symplecticReductionForm_alt ω S ha) (e x) (e y) =
        symplecticReductionForm ω T ha x y) ∧
      ∀ L : Submodule K E,
        (reduceSubspace ω T L).map e.toLinearMap =
          reduceSubspace (symplecticReductionForm ω S ha)
            (reduceSubspace ω S T) (reduceSubspace ω S L) := by
  let α := symplecticReductionForm ω S ha
  let R := reduceSubspace ω S T
  have hPS : ω.orthogonal T ≤ ω.orthogonal S := by
    intro x hx s hs
    exact hx s (hST hs)
  have hmem (x : ω.orthogonal S) :
      (reductionKernel ω S).mkQ x ∈ α.orthogonal R ↔ x.val ∈ ω.orthogonal T := by
    constructor
    · intro hx t ht
      have htS : t ∈ ω.orthogonal S := hPS (hT ht)
      exact hx ((reductionKernel ω S).mkQ ⟨t,htS⟩) ⟨⟨t,htS⟩,ht,rfl⟩
    · intro hx z hz
      obtain ⟨t,ht,rfl⟩ := hz
      exact hx t.val ht
  let p : ω.orthogonal T →ₗ[K] α.orthogonal R :=
    { toFun := fun x => ⟨(reductionKernel ω S).mkQ ⟨x.val,hPS x.property⟩,
          (hmem _).mpr x.property⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        exact (reductionKernel ω S).mkQ.map_add
          ⟨x.val,hPS x.property⟩ ⟨y.val,hPS y.property⟩
      map_smul' := by
        intro c x
        apply Subtype.ext
        exact (reductionKernel ω S).mkQ.map_smul c ⟨x.val,hPS x.property⟩ }
  let g : ω.orthogonal T →ₗ[K] ReducedSpace α R := (reductionKernel α R).mkQ.comp p
  have hker : reductionKernel ω T ≤ g.ker := by
    intro x hx
    apply (Submodule.Quotient.mk_eq_zero (reductionKernel α R)).mpr
    exact ⟨⟨x.val,hPS x.property⟩,hx,rfl⟩
  let f : ReducedSpace ω T →ₗ[K] ReducedSpace α R := (reductionKernel ω T).liftQ g hker
  have hf (x : ω.orthogonal T) : f ((reductionKernel ω T).mkQ x) =
      (reductionKernel α R).mkQ (p x) := rfl
  have hinj : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    apply (Submodule.eq_bot_iff _).mpr
    intro z hz
    induction z using Submodule.Quotient.induction_on with
    | H x =>
      have hxR : (p x).val ∈ R :=
        (Submodule.Quotient.mk_eq_zero (reductionKernel α R)).mp hz
      obtain ⟨t,ht,heq⟩ := hxR
      have hdiff : t.val-x.val ∈ S :=
        (Submodule.Quotient.eq (reductionKernel ω S)).mp heq
      apply (Submodule.Quotient.mk_eq_zero (reductionKernel ω T)).mpr
      have hxT := T.sub_mem ht (hST hdiff)
      change x.val ∈ T
      simpa only [Submodule.subtype_apply,sub_sub_cancel] using hxT
  have hsurj : Function.Surjective f := by
    intro z
    induction z using Submodule.Quotient.induction_on with
    | H y =>
      obtain ⟨x,hx⟩ := (reductionKernel ω S).mkQ_surjective y.val
      have hxT : x.val ∈ ω.orthogonal T := (hmem x).mp (hx.symm ▸ y.property)
      refine ⟨(reductionKernel ω T).mkQ ⟨x.val,hxT⟩,?_⟩
      rw [hf]
      apply congrArg (reductionKernel α R).mkQ
      apply Subtype.ext
      exact hx
  let e : ReducedSpace ω T ≃ₗ[K] ReducedSpace α R := LinearEquiv.ofBijective f ⟨hinj,hsurj⟩
  refine ⟨e,?_,?_⟩
  · intro x y
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      induction y using Submodule.Quotient.induction_on with
      | H y => rfl
  · intro L
    ext z
    constructor
    · rintro ⟨y,⟨x,hx,rfl⟩,rfl⟩
      refine ⟨p x,?_,rfl⟩
      exact ⟨⟨x.val,hPS x.property⟩,hx,rfl⟩
    · rintro ⟨y,hy,rfl⟩
      obtain ⟨x,hx,hxy⟩ := hy
      have hxT : x.val ∈ ω.orthogonal T := (hmem x).mp (hxy.symm ▸ y.property)
      refine ⟨(reductionKernel ω T).mkQ ⟨x.val,hxT⟩,
        ⟨⟨x.val,hxT⟩,hx,rfl⟩,?_⟩
      change (reductionKernel α R).mkQ (p ⟨x.val,hxT⟩) = (reductionKernel α R).mkQ y
      congr 1
      apply Subtype.ext
      exact hxy
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
theorem exists_orthogonal_isometry_between
    (ω : LinearMap.BilinForm K E) (η : LinearMap.BilinForm K F)
    (ha : ω.IsAlt) (hb : η.IsAlt)
    (B : Submodule K E) (C : Submodule K F)
    (hB : (ω.restrict B).Nondegenerate) (hC : (η.restrict C).Nondegenerate)
    (f : B ≃ₗ[K] C) (g : ω.orthogonal B ≃ₗ[K] η.orthogonal C)
    (hf : ∀ x y, η (f x).val (f y).val = ω x.val y.val)
    (hg : ∀ x y, η (g x).val (g y).val = ω x.val y.val) :
    ∃ e : E ≃ₗ[K] F, (∀ x y, η (e x) (e y) = ω x y) ∧
      (∀ x : B, e x.val = (f x).val) ∧
      (∀ x : ω.orthogonal B, e x.val = (g x).val) := by
  let c := B.prodEquivOfIsCompl (ω.orthogonal B)
    (ω.isCompl_orthogonal_of_restrict_nondegenerate ha.isRefl hB)
  let d := C.prodEquivOfIsCompl (η.orthogonal C)
    (η.isCompl_orthogonal_of_restrict_nondegenerate hb.isRefl hC)
  let e := c.symm.trans ((f.prodCongr g).trans d)
  have he (x : B × ω.orthogonal B) : e (c x) = d (f x.1,g x.2) := by simp [e]
  refine ⟨e,?_,?_,?_⟩
  · intro x y
    obtain ⟨x,rfl⟩ := c.surjective x
    obtain ⟨y,rfl⟩ := c.surjective y
    rw [he,he]
    change η ((f x.1).val + (g x.2).val) ((f y.1).val + (g y.2).val) =
      ω (x.1.val + x.2.val) (y.1.val + y.2.val)
    rw [form_orthogonal_sum η hb C (f x.1,g x.2) (f y.1,g y.2),
      form_orthogonal_sum ω ha B x y,hf,hg]
  · intro x
    have h := he (x,0)
    simpa [c,d] using h
  · intro x
    have h := he (0,x)
    simpa [c,d] using h
omit [FiniteDimensional K E] [FiniteDimensional K F] in
theorem map_orthogonal_split (e : E ≃ₗ[K] F)
    (B : Submodule K E) (C : Submodule K F)
    (f : B ≃ₗ[K] C) (heB : ∀ x : B, e x.val = (f x).val)
    (U : Submodule K E) (W : Submodule K F)
    (g : U ≃ₗ[K] W) (heU : ∀ x : U, e x.val = (g x).val)
    (L : Submodule K E) (M : Submodule K F)
    (hL : L = (L ⊓ B) ⊔ (L ⊓ U)) (hM : M = (M ⊓ C) ⊔ (M ⊓ W))
    (hf : (L.comap B.subtype).map f.toLinearMap = M.comap C.subtype)
    (hg : (L.comap U.subtype).map g.toLinearMap = M.comap W.subtype) :
    L.map e.toLinearMap = M := by
  have hblock : (L ⊓ B).map e.toLinearMap = M ⊓ C := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      have hy : f ⟨x,hx.2⟩ ∈ M.comap C.subtype := hf.le ⟨⟨x,hx.2⟩,hx.1,rfl⟩
      change e x ∈ M ⊓ C
      rw [heB ⟨x,hx.2⟩]
      exact ⟨hy,(f ⟨x,hx.2⟩).property⟩
    · intro hy
      have hy' : (⟨y,hy.2⟩ : C) ∈ (L.comap B.subtype).map f.toLinearMap := hf.ge hy.1
      obtain ⟨x,hx,hxy⟩ := hy'
      refine ⟨x.val,⟨hx,x.property⟩,?_⟩
      change e x.val = y
      exact (heB x).trans (congrArg Subtype.val hxy)
  have hres : (L ⊓ U).map e.toLinearMap = M ⊓ W := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      have hy : g ⟨x,hx.2⟩ ∈ M.comap W.subtype := hg.le ⟨⟨x,hx.2⟩,hx.1,rfl⟩
      change e x ∈ M ⊓ W
      rw [heU ⟨x,hx.2⟩]
      exact ⟨hy,(g ⟨x,hx.2⟩).property⟩
    · intro hy
      have hy' : (⟨y,hy.2⟩ : W) ∈ (L.comap U.subtype).map g.toLinearMap := hg.ge hy.1
      obtain ⟨x,hx,hxy⟩ := hy'
      refine ⟨x.val,⟨hx,x.property⟩,?_⟩
      change e x.val = y
      exact (heU x).trans (congrArg Subtype.val hxy)
  calc
    L.map e.toLinearMap = ((L ⊓ B) ⊔ (L ⊓ U)).map e.toLinearMap := congrArg _ hL
    _ = (M ⊓ C) ⊔ (M ⊓ W) := by rw [Submodule.map_sup,hblock,hres]
    _ = M := hM.symm
end OrthogonalIsometries
end SidorenkoCounterexample
namespace SidorenkoCounterexample
section SplitHelpers
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
theorem split_inter_block (L A B U : Submodule K E)
    (hBU : Disjoint B U) (hAB : A ≤ B) (hL : L = A ⊔ (L ⊓ U)) :
    L ⊓ B = A := by
  apply le_antisymm
  · intro x hx
    have hxL : x ∈ A ⊔ (L ⊓ U) := hL ▸ hx.1
    obtain ⟨a,ha,u,hu,hau⟩ := Submodule.mem_sup.mp hxL
    have huB : u ∈ B := by
      have huval : u = x-a := by rw [←hau]; abel
      rw [huval]
      exact B.sub_mem hx.2 (hAB ha)
    have hu0 : u = 0 := hBU.le_bot ⟨huB,hu.2⟩
    rw [hu0,add_zero] at hau
    exact hau ▸ ha
  · exact le_inf (hL.symm ▸ le_sup_left) hAB
theorem split_over_block (L A B U : Submodule K E)
    (hAB : A ≤ B) (hL : L = A ⊔ (L ⊓ U)) :
    L = (L ⊓ B) ⊔ (L ⊓ U) := by
  apply le_antisymm
  · calc
      L = A ⊔ (L ⊓ U) := hL
      _ ≤ (L ⊓ B) ⊔ (L ⊓ U) :=
        sup_le_sup (le_inf (hL.symm ▸ le_sup_left) hAB) le_rfl
  · exact sup_le inf_le_left inf_le_left
end SplitHelpers
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section TripleBlockData
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E)
theorem triple_block_reduction_data (ha : ω.IsAlt)
    (L M N : Submodule K E) (hL : ω.orthogonal L = L)
    (hM : ω.orthogonal M = M) (hN : ω.orthogonal N = N)
    (hzero : (L ⊓ M) ⊓ N = ⊥) :
    ∃ B : Submodule K E, (ω.restrict B).Nondegenerate ∧
      ∃ e : (↥(L ⊓ M) × Module.Dual K ↥(L ⊓ M)) ≃ₗ[K] B,
      ∃ f : ω.orthogonal B ≃ₗ[K] ReducedSpace ω (L ⊓ M),
        (∀ x y, ω (e x).val (e y).val = canonicalSymplectic x y) ∧
        (∀ x y, symplecticReductionForm ω (L ⊓ M) ha (f x) (f y) = ω x.val y.val) ∧
        L.comap B.subtype = horizontalSpace.map e.toLinearMap ∧
        M.comap B.subtype = horizontalSpace.map e.toLinearMap ∧
        N.comap B.subtype = verticalSpace.map e.toLinearMap ∧
        ∀ A ∈ ({L,M,N} : Set (Submodule K E)),
          A = (A ⊓ B) ⊔ (A ⊓ ω.orthogonal B) ∧
          (A.comap (ω.orthogonal B).subtype).map f.toLinearMap =
            reduceSubspace ω (L ⊓ M) A := by
  obtain ⟨B,Q,hB,hSB,hQB,_hQN,_hdim,_hBQ,hSL,hSM,hSN,_hsL,_hsM,_hdisj,_hres,
    e,heS,heQ,heform⟩ := triple_pair_block ω ha L M N hL hM hN hzero
  let S := L ⊓ M
  let T : Submodule K B := horizontalSpace.map e.toLinearMap
  have hTS : T.map B.subtype = S := by
    ext x
    constructor
    · rintro ⟨b,⟨z,hz,rfl⟩,rfl⟩
      obtain ⟨s,g⟩ := z
      have hg : g = 0 := hz
      subst g
      change (e (s,0)).val ∈ S
      rw [heS]
      exact s.property
    · intro hx
      refine ⟨e (⟨x,hx⟩,0),⟨(⟨x,hx⟩,0),rfl,rfl⟩,?_⟩
      exact heS ⟨x,hx⟩
  have hT : (ω.restrict B).orthogonal T = T := by
    rw [orthogonal_map_isometry_between (canonicalSymplectic (K := K) (V := S))
      (ω.restrict B) e (fun x y => heform x y),horizontalSpace_selforthogonal]
  have hBS : B ⊓ ω.orthogonal S = S := by
    apply le_antisymm
    · intro x hx
      have hxT : (⟨x,hx.1⟩ : B) ∈ T := by
        apply hT.le
        intro b hb
        exact hx.2 b.val (hTS.le ⟨b,hb,rfl⟩)
      exact hTS.le ⟨⟨x,hx.1⟩,hxT,rfl⟩
    · refine le_inf hSB ?_
      intro s hs t ht
      exact hL.ge hs.1 t ht.1
  have hLU := split_over_block L S B (ω.orthogonal B) hSB hSL
  have hMU := split_over_block M S B (ω.orthogonal B) hSB hSM
  have hNU := split_over_block N Q B (ω.orthogonal B) hQB hSN
  obtain ⟨f,_hf,hfform,hfred⟩ := exists_complement_reduction_equiv ω ha S B hB hSB hBS
  have hcompl := ω.isCompl_orthogonal_of_restrict_nondegenerate ha.isRefl hB
  have hLB := split_inter_block L S B (ω.orthogonal B) hcompl.disjoint hSB hSL
  have hMB := split_inter_block M S B (ω.orthogonal B) hcompl.disjoint hSB hSM
  have hNB := split_inter_block N Q B (ω.orthogonal B) hcompl.disjoint hQB hSN
  refine ⟨B,hB,e,f,heform,hfform,?_,?_,?_,?_⟩
  · apply Submodule.map_injective_of_injective B.injective_subtype
    rw [Submodule.map_comap_subtype,inf_comm,hLB]
    exact hTS.symm
  · apply Submodule.map_injective_of_injective B.injective_subtype
    rw [Submodule.map_comap_subtype,inf_comm,hMB]
    exact hTS.symm
  · apply Submodule.map_injective_of_injective B.injective_subtype
    rw [Submodule.map_comap_subtype,inf_comm,hNB]
    exact heQ.symm
  · intro A hA
    rcases (show A = L ∨ A = M ∨ A = N from hA) with heq | heq | heq
    · subst A; exact ⟨hLU,hfred L hLU⟩
    · subst A; exact ⟨hMU,hfred M hMU⟩
    · subst A; exact ⟨hNU,hfred N hNU⟩
end TripleBlockData
end SidorenkoCounterexample
namespace SidorenkoCounterexample
section MapTransport
variable {K E F E' F' : Type*} [Field K]
  [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]
  [AddCommGroup E'] [Module K E'] [AddCommGroup F'] [Module K F']
theorem map_transport_equiv (u : E ≃ₗ[K] E') (v : F ≃ₗ[K] F')
    (r : E' ≃ₗ[K] F') (A : Submodule K E) (B : Submodule K F)
    (h : (A.map u.toLinearMap).map r.toLinearMap = B.map v.toLinearMap) :
    A.map (u.trans (r.trans v.symm)).toLinearMap = B := by
  apply Submodule.map_injective_of_injective v.injective
  calc
    (A.map (u.trans (r.trans v.symm)).toLinearMap).map v.toLinearMap =
        (A.map u.toLinearMap).map r.toLinearMap := by
      simp only [← Submodule.map_comp]
      congr 1
      ext x
      simp
    _ = B.map v.toLinearMap := h
theorem map_conjugate_equiv (u : E ≃ₗ[K] E') (v : F ≃ₗ[K] F')
    (r : E ≃ₗ[K] F) (A : Submodule K E) :
    (A.map u.toLinearMap).map (u.symm.trans (r.trans v)).toLinearMap =
      (A.map r.toLinearMap).map v.toLinearMap := by
  simp only [← Submodule.map_comp]
  congr 1
  ext x
  simp
end MapTransport
open Module
section TripleOneBlockLift
variable {K E F : Type*} [Field K]
  [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]
  [FiniteDimensional K E] [FiniteDimensional K F]
theorem triple_one_block_lift
    (ω : LinearMap.BilinForm K E) (η : LinearMap.BilinForm K F)
    (ha : ω.IsAlt) (hb : η.IsAlt)
    (L M N : Submodule K E) (L' M' N' : Submodule K F)
    (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M) (hN : ω.orthogonal N = N)
    (hL' : η.orthogonal L' = L') (hM' : η.orthogonal M' = M')
    (hN' : η.orthogonal N' = N')
    (hzero : (L ⊓ M) ⊓ N = ⊥) (hzero' : (L' ⊓ M') ⊓ N' = ⊥)
    (hdim : finrank K ↥(L ⊓ M) = finrank K ↥(L' ⊓ M'))
    (r : ReducedSpace ω (L ⊓ M) ≃ₗ[K] ReducedSpace η (L' ⊓ M'))
    (hr : ∀ x y, symplecticReductionForm η (L' ⊓ M') hb (r x) (r y) =
      symplecticReductionForm ω (L ⊓ M) ha x y)
    (hrL : (reduceSubspace ω (L ⊓ M) L).map r.toLinearMap =
      reduceSubspace η (L' ⊓ M') L')
    (hrM : (reduceSubspace ω (L ⊓ M) M).map r.toLinearMap =
      reduceSubspace η (L' ⊓ M') M')
    (hrN : (reduceSubspace ω (L ⊓ M) N).map r.toLinearMap =
      reduceSubspace η (L' ⊓ M') N') :
    ∃ e : E ≃ₗ[K] F, (∀ x y, η (e x) (e y) = ω x y) ∧
      L.map e.toLinearMap = L' ∧ M.map e.toLinearMap = M' ∧
      N.map e.toLinearMap = N' := by
  obtain ⟨B,hB,b,f,hbform,hfform,hLb,hMb,hNb,hsplit⟩ :=
    triple_block_reduction_data ω ha L M N hL hM hN hzero
  obtain ⟨C,hC,c,g,hcform,hgform,hLc,hMc,hNc,hsplit'⟩ :=
    triple_block_reduction_data η hb L' M' N' hL' hM' hN' hzero'
  let t : ↥(L ⊓ M) ≃ₗ[K] ↥(L' ⊓ M') := LinearEquiv.ofFinrankEq _ _ hdim
  let w := t.prodCongr t.symm.dualMap
  have hw (x y : ↥(L ⊓ M) × Module.Dual K ↥(L ⊓ M)) :
      canonicalSymplectic (w x) (w y) = canonicalSymplectic x y := by
    simp [w,canonicalSymplectic_apply]
  have hwH : horizontalSpace.map w.toLinearMap = horizontalSpace := by
    apply subspace_map_eq_of_mem_iff
    intro x
    change t.symm.dualMap x.2 = 0 ↔ x.2 = 0
    exact t.symm.dualMap.map_eq_zero_iff
  have hwV : verticalSpace.map w.toLinearMap = verticalSpace := by
    apply subspace_map_eq_of_mem_iff
    intro x
    change t x.1 = 0 ↔ x.1 = 0
    exact t.map_eq_zero_iff
  let u := b.symm.trans (w.trans c)
  let v := f.trans (r.trans g.symm)
  have hu (x y : B) : η (u x).val (u y).val = ω x.val y.val := by
    change η (c (w (b.symm x))).val (c (w (b.symm y))).val = _
    rw [hcform,hw,←hbform,b.apply_symm_apply,b.apply_symm_apply]
  have hv (x y : ω.orthogonal B) : η (v x).val (v y).val = ω x.val y.val := by
    rw [← hgform]
    change symplecticReductionForm η (L' ⊓ M') hb
      (g (g.symm (r (f x)))) (g (g.symm (r (f y)))) = _
    rw [g.apply_symm_apply,g.apply_symm_apply,hr,hfform]
  obtain ⟨e,he,heB,heU⟩ := exists_orthogonal_isometry_between ω η ha hb B C hB hC u v hu hv
  have hblockH : (horizontalSpace.map b.toLinearMap).map u.toLinearMap =
      horizontalSpace.map c.toLinearMap := by
    rw [map_conjugate_equiv b c w,hwH]
  have hblockV : (verticalSpace.map b.toLinearMap).map u.toLinearMap =
      verticalSpace.map c.toLinearMap := by
    rw [map_conjugate_equiv b c w,hwV]
  have hmap (A : Submodule K E) (A' : Submodule K F)
      (hA : A ∈ ({L,M,N} : Set (Submodule K E)))
      (hA' : A' ∈ ({L',M',N'} : Set (Submodule K F)))
      (hblock : (A.comap B.subtype).map u.toLinearMap = A'.comap C.subtype)
      (hres : (reduceSubspace ω (L ⊓ M) A).map r.toLinearMap =
        reduceSubspace η (L' ⊓ M') A') : A.map e.toLinearMap = A' := by
    obtain ⟨hAs,hAr⟩ := hsplit A hA
    obtain ⟨hAs',hAr'⟩ := hsplit' A' hA'
    apply map_orthogonal_split e B C u heB (ω.orthogonal B) (η.orthogonal C)
      v heU A A' hAs hAs' hblock
    apply map_transport_equiv f g r
    rw [hAr,hAr',hres]
  refine ⟨e,he,?_,?_,?_⟩
  · exact hmap L L' (by simp) (by simp) (by rw [hLb,hLc]; exact hblockH) hrL
  · exact hmap M M' (by simp) (by simp) (by rw [hMb,hMc]; exact hblockH) hrM
  · exact hmap N N' (by simp) (by simp) (by rw [hNb,hNc]; exact hblockV) hrN
end TripleOneBlockLift
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ReductionIntersections
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E) (S : Submodule K E)
@[simp] theorem reduceSubspace_self : reduceSubspace ω S S = ⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  rintro x ⟨y,hy,rfl⟩
  exact (Submodule.Quotient.mk_eq_zero (reductionKernel ω S)).mpr hy
theorem reduceSubspace_inf (L N : Submodule K E) (hSL : S ≤ L) :
    reduceSubspace ω S (L ⊓ N) =
      reduceSubspace ω S L ⊓ reduceSubspace ω S N := by
  apply le_antisymm
  · rintro x ⟨y,hy,rfl⟩
    exact ⟨⟨y,hy.1,rfl⟩,⟨y,hy.2,rfl⟩⟩
  · rintro x ⟨⟨l,hl,hlx⟩,⟨n,hn,hnx⟩⟩
    have heq : (reductionKernel ω S).mkQ (l-n) = 0 := by
      rw [map_sub,hlx,hnx,sub_self]
    have hln : l.val-n.val ∈ S :=
      (Submodule.Quotient.mk_eq_zero (reductionKernel ω S)).mp heq
    have hnL : n.val ∈ L := by
      have h := L.sub_mem hl (hSL hln)
      simpa using h
    exact ⟨n,⟨hnL,hn⟩,hnx⟩
theorem reduceSubspace_finrank_of_disjoint [FiniteDimensional K E]
    (A : Submodule K E) (hAP : A ≤ ω.orthogonal S) (hAS : Disjoint A S) :
    finrank K (reduceSubspace ω S A) = finrank K A := by
  let f : A →ₗ[K] ReducedSpace ω S :=
    (reductionKernel ω S).mkQ.comp ((Submodule.inclusion hAP))
  have hf : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    apply (Submodule.eq_bot_iff _).mpr
    intro x hx
    apply Subtype.ext
    have hxS : x.val ∈ S :=
      (Submodule.Quotient.mk_eq_zero (reductionKernel ω S)).mp hx
    exact hAS.le_bot ⟨x.property,hxS⟩
  have hfr : LinearMap.range f = reduceSubspace ω S A := by
    ext y
    constructor
    · rintro ⟨x,rfl⟩
      exact ⟨⟨x.val,hAP x.property⟩,x.property,rfl⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨⟨x.val,hx⟩,rfl⟩
  rw [←hfr]
  exact (LinearEquiv.ofInjective f hf).finrank_eq.symm
theorem reduceSubspace_sup (A B : Submodule K E)
    (hA : A ≤ ω.orthogonal S) (hB : B ≤ ω.orthogonal S) :
    reduceSubspace ω S (A ⊔ B) = reduceSubspace ω S A ⊔ reduceSubspace ω S B := by
  have hcomap : (A ⊔ B).comap (ω.orthogonal S).subtype =
      A.comap (ω.orthogonal S).subtype ⊔ B.comap (ω.orthogonal S).subtype := by
    ext x
    constructor
    · intro hx
      obtain ⟨a,ha,b,hb,hab⟩ := Submodule.mem_sup.mp hx
      exact Submodule.mem_sup.mpr
        ⟨⟨a,hA ha⟩,ha,⟨b,hB hb⟩,hb,Subtype.ext hab⟩
    · intro hx
      obtain ⟨a,ha,b,hb,rfl⟩ := Submodule.mem_sup.mp hx
      exact Submodule.mem_sup.mpr ⟨a.val,ha,b.val,hb,rfl⟩
  unfold reduceSubspace
  rw [hcomap,Submodule.map_sup]
end ReductionIntersections
section PairSum
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E)
def triplePairSum (L M N : Submodule K E) : Submodule K E :=
  (L ⊓ M) ⊔ (L ⊓ N) ⊔ (M ⊓ N)
theorem triplePairSum_isotropic (L M N : Submodule K E)
    (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M)
    (hN : ω.orthogonal N = N) :
    triplePairSum L M N ≤ ω.orthogonal (triplePairSum L M N) := by
  rw [triplePairSum,orthogonal_sup_eq,orthogonal_sup_eq]
  refine sup_le (sup_le (le_inf (le_inf ?_ ?_) ?_) (le_inf (le_inf ?_ ?_) ?_))
    (le_inf (le_inf ?_ ?_) ?_)
  all_goals intro x hx y hy
  · exact hL.ge hx.1 y hy.1
  · exact hL.ge hx.1 y hy.1
  · exact hM.ge hx.2 y hy.1
  · exact hL.ge hx.1 y hy.1
  · exact hL.ge hx.1 y hy.1
  · exact hN.ge hx.2 y hy.2
  · exact hM.ge hx.1 y hy.2
  · exact hN.ge hx.2 y hy.2
  · exact hM.ge hx.1 y hy.1
theorem triple_pair_reduction_intersections [FiniteDimensional K E]
    (L M N : Submodule K E)
    (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M)
    (hzero : (L ⊓ M) ⊓ N = ⊥) :
    let S := L ⊓ M
    let P := reduceSubspace ω S L
    let Q := reduceSubspace ω S M
    let R := reduceSubspace ω S N
    P ⊓ Q = ⊥ ∧
      P ⊓ R = reduceSubspace ω S (L ⊓ N) ∧
      Q ⊓ R = reduceSubspace ω S (M ⊓ N) ∧
      finrank K ↥(P ⊓ R) = finrank K ↥(L ⊓ N) ∧
      finrank K ↥(Q ⊓ R) = finrank K ↥(M ⊓ N) ∧
      triplePairSum P Q R = reduceSubspace ω S (triplePairSum L M N) := by
  dsimp only
  have hLM := reduceSubspace_inf ω (L ⊓ M) L M inf_le_left
  have hLN := reduceSubspace_inf ω (L ⊓ M) L N inf_le_left
  have hMN := reduceSubspace_inf ω (L ⊓ M) M N inf_le_right
  have hLP : L ≤ ω.orthogonal (L ⊓ M) := lagrangian_le_orthogonal ω _ L hL inf_le_left
  have hMP : M ≤ ω.orthogonal (L ⊓ M) := lagrangian_le_orthogonal ω _ M hM inf_le_right
  have hLNdis : Disjoint (L ⊓ N) (L ⊓ M) := by
    apply disjoint_iff.mpr
    apply (Submodule.eq_bot_iff _).mpr
    intro x hx
    exact hzero.le ⟨hx.2,hx.1.2⟩
  have hMNdis : Disjoint (M ⊓ N) (L ⊓ M) := by
    apply disjoint_iff.mpr
    apply (Submodule.eq_bot_iff _).mpr
    intro x hx
    exact hzero.le ⟨hx.2,hx.1.2⟩
  rw [←hLM,reduceSubspace_self,←hLN,←hMN]
  refine ⟨rfl,rfl,rfl,?_,?_,?_⟩
  · exact reduceSubspace_finrank_of_disjoint ω _ _ (inf_le_left.trans hLP) hLNdis
  · exact reduceSubspace_finrank_of_disjoint ω _ _ (inf_le_left.trans hMP) hMNdis
  · rw [triplePairSum,triplePairSum,
      reduceSubspace_sup ω _ _ _ (sup_le (inf_le_left.trans hLP)
        (inf_le_left.trans hLP)) (inf_le_left.trans hMP),
      reduceSubspace_sup ω _ _ _ (inf_le_left.trans hLP) (inf_le_left.trans hLP),
      reduceSubspace_self,←hLM,←hLN,←hMN,reduceSubspace_self]
end PairSum
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ClassificationPredicates
variable {K E F : Type*} [Field K]
  [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]
def TripleIsometry (ω : LinearMap.BilinForm K E) (η : LinearMap.BilinForm K F)
    (L M N : Submodule K E) (L' M' N' : Submodule K F) : Prop :=
  ∃ e : E ≃ₗ[K] F, (∀ x y, η (e x) (e y) = ω x y) ∧
    L.map e.toLinearMap = L' ∧ M.map e.toLinearMap = M' ∧ N.map e.toLinearMap = N'
def TripleResidualIsometry (ω : LinearMap.BilinForm K E) (η : LinearMap.BilinForm K F)
    (ha : ω.IsAlt) (hb : η.IsAlt)
    (L M N : Submodule K E) (L' M' N' : Submodule K F) : Prop :=
  TripleIsometry (symplecticReductionForm ω (triplePairSum L M N) ha)
    (symplecticReductionForm η (triplePairSum L' M' N') hb)
    (reduceSubspace ω (triplePairSum L M N) L)
    (reduceSubspace ω (triplePairSum L M N) M)
    (reduceSubspace ω (triplePairSum L M N) N)
    (reduceSubspace η (triplePairSum L' M' N') L')
    (reduceSubspace η (triplePairSum L' M' N') M')
    (reduceSubspace η (triplePairSum L' M' N') N')
theorem TripleResidualIsometry.swap_right
    {ω : LinearMap.BilinForm K E} {η : LinearMap.BilinForm K F}
    {ha : ω.IsAlt} {hb : η.IsAlt}
    {L M N : Submodule K E} {L' M' N' : Submodule K F}
    (h : TripleResidualIsometry ω η ha hb L M N L' M' N') :
    TripleResidualIsometry ω η ha hb L N M L' N' M' := by
  have hs : triplePairSum L N M = triplePairSum L M N := by unfold triplePairSum; ac_rfl
  have hs' : triplePairSum L' N' M' = triplePairSum L' M' N' := by unfold triplePairSum; ac_rfl
  unfold TripleResidualIsometry at *
  rw [hs,hs']
  obtain ⟨e,he,hL,hM,hN⟩ := h
  exact ⟨e,he,hL,hN,hM⟩
theorem TripleResidualIsometry.rotate
    {ω : LinearMap.BilinForm K E} {η : LinearMap.BilinForm K F}
    {ha : ω.IsAlt} {hb : η.IsAlt}
    {L M N : Submodule K E} {L' M' N' : Submodule K F}
    (h : TripleResidualIsometry ω η ha hb L M N L' M' N') :
    TripleResidualIsometry ω η ha hb M N L M' N' L' := by
  have hs : triplePairSum M N L = triplePairSum L M N := by unfold triplePairSum; ac_rfl
  have hs' : triplePairSum M' N' L' = triplePairSum L' M' N' := by unfold triplePairSum; ac_rfl
  unfold TripleResidualIsometry at *
  rw [hs,hs']
  obtain ⟨e,he,hL,hM,hN⟩ := h
  exact ⟨e,he,hM,hN,hL⟩
end ClassificationPredicates
section ResidualClassificationStep
variable {K E F : Type*} [Field K]
  [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]
  [FiniteDimensional K E] [FiniteDimensional K F]
theorem triple_residual_isometry_reduce_pair
    (ω : LinearMap.BilinForm K E) (η : LinearMap.BilinForm K F)
    (ha : ω.IsAlt) (hb : η.IsAlt)
    (L M N : Submodule K E) (L' M' N' : Submodule K F)
    (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M) (hN : ω.orthogonal N = N)
    (hL' : η.orthogonal L' = L') (hM' : η.orthogonal M' = M') (hN' : η.orthogonal N' = N')
    (hzero : (L ⊓ M) ⊓ N = ⊥) (hzero' : (L' ⊓ M') ⊓ N' = ⊥)
    (h : TripleResidualIsometry ω η ha hb L M N L' M' N') :
    TripleResidualIsometry (symplecticReductionForm ω (L ⊓ M) ha)
      (symplecticReductionForm η (L' ⊓ M') hb)
      (symplecticReductionForm_alt ω (L ⊓ M) ha)
      (symplecticReductionForm_alt η (L' ⊓ M') hb)
      (reduceSubspace ω (L ⊓ M) L) (reduceSubspace ω (L ⊓ M) M)
      (reduceSubspace ω (L ⊓ M) N) (reduceSubspace η (L' ⊓ M') L')
      (reduceSubspace η (L' ⊓ M') M') (reduceSubspace η (L' ⊓ M') N') := by
  have hs := (triple_pair_reduction_intersections ω L M N hL hM hzero).2.2.2.2.2
  have hs' := (triple_pair_reduction_intersections η L' M' N' hL' hM' hzero').2.2.2.2.2
  unfold TripleResidualIsometry
  rw [hs,hs']
  obtain ⟨u,hu,huA⟩ := exists_reduction_in_stages ω ha (L ⊓ M) (triplePairSum L M N)
    (le_sup_left.trans le_sup_left) (triplePairSum_isotropic ω L M N hL hM hN)
  obtain ⟨v,hv,hvA⟩ := exists_reduction_in_stages η hb (L' ⊓ M') (triplePairSum L' M' N')
    (le_sup_left.trans le_sup_left) (triplePairSum_isotropic η L' M' N' hL' hM' hN')
  obtain ⟨r,hr,hrL,hrM,hrN⟩ := h
  let e := u.symm.trans (r.trans v)
  refine ⟨e,?_,?_,?_,?_⟩
  · intro x y
    change symplecticReductionForm (symplecticReductionForm η (L' ⊓ M') hb)
      (reduceSubspace η (L' ⊓ M') (triplePairSum L' M' N'))
      (symplecticReductionForm_alt η (L' ⊓ M') hb)
      (v (r (u.symm x))) (v (r (u.symm y))) = _
    rw [hv,hr,←hu,u.apply_symm_apply,u.apply_symm_apply]
  · rw [←huA L,←hvA L',map_conjugate_equiv,hrL]
  · rw [←huA M,←hvA M',map_conjugate_equiv,hrM]
  · rw [←huA N,←hvA N',map_conjugate_equiv,hrN]
theorem triple_isometry_of_zero_pairs
    (ω : LinearMap.BilinForm K E) (η : LinearMap.BilinForm K F)
    (ha : ω.IsAlt) (hb : η.IsAlt)
    (L M N : Submodule K E) (L' M' N' : Submodule K F)
    (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M) (hN : ω.orthogonal N = N)
    (hL' : η.orthogonal L' = L') (hM' : η.orthogonal M' = M') (hN' : η.orthogonal N' = N')
    (hLM : L ⊓ M = ⊥) (hLN : L ⊓ N = ⊥) (hMN : M ⊓ N = ⊥)
    (hLM' : L' ⊓ M' = ⊥) (hLN' : L' ⊓ N' = ⊥) (hMN' : M' ⊓ N' = ⊥)
    (h : TripleResidualIsometry ω η ha hb L M N L' M' N') :
    TripleIsometry ω η L M N L' M' N' := by
  have hs : triplePairSum L M N = L ⊓ M := by simp [triplePairSum,hLM,hLN,hMN]
  have hs' : triplePairSum L' M' N' = L' ⊓ M' := by simp [triplePairSum,hLM',hLN',hMN']
  unfold TripleResidualIsometry at h
  rw [hs,hs'] at h
  obtain ⟨r,hr,hrL,hrM,hrN⟩ := h
  exact triple_one_block_lift ω η ha hb L M N L' M' N' hL hM hN hL' hM' hN'
    (by rw [hLM,bot_inf_eq]) (by rw [hLM',bot_inf_eq]) (by rw [hLM,hLM']; simp)
    r hr hrL hrM hrN
end ResidualClassificationStep
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section FullClassification
variable {K E F : Type*} [Field K]
  [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]
  [FiniteDimensional K E] [FiniteDimensional K F]
omit [FiniteDimensional K E] in
@[simp] theorem reduceSubspace_bot (ω : LinearMap.BilinForm K E) (S : Submodule K E) :
    reduceSubspace ω S ⊥ = ⊥ := by
  unfold reduceSubspace
  simp
theorem triple_isometry_of_two_zero_pairs
    (ω : LinearMap.BilinForm K E) (η : LinearMap.BilinForm K F)
    (ha : ω.IsAlt) (hb : η.IsAlt) (hω : ω.Nondegenerate) (hη : η.Nondegenerate)
    (L M N : Submodule K E) (L' M' N' : Submodule K F)
    (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M) (hN : ω.orthogonal N = N)
    (hL' : η.orthogonal L' = L') (hM' : η.orthogonal M' = M') (hN' : η.orthogonal N' = N')
    (hLM : L ⊓ M = ⊥) (hLN : L ⊓ N = ⊥)
    (hLM' : L' ⊓ M' = ⊥) (hLN' : L' ⊓ N' = ⊥)
    (hdim : finrank K ↥(M ⊓ N) = finrank K ↥(M' ⊓ N'))
    (h : TripleResidualIsometry ω η ha hb L M N L' M' N') :
    TripleIsometry ω η L M N L' M' N' := by
  have hz : (M ⊓ N) ⊓ L = ⊥ := by
    calc
      _ = (L ⊓ M) ⊓ N := by ac_rfl
      _ = ⊥ := by rw [hLM,bot_inf_eq]
  have hz' : (M' ⊓ N') ⊓ L' = ⊥ := by
    calc
      _ = (L' ⊓ M') ⊓ N' := by ac_rfl
      _ = ⊥ := by rw [hLM',bot_inf_eq]
  have hS : M ⊓ N ≤ ω.orthogonal (M ⊓ N) := by
    intro x hx y hy
    exact hM.ge hx.1 y hy.1
  have hS' : M' ⊓ N' ≤ η.orthogonal (M' ⊓ N') := by
    intro x hx y hy
    exact hM'.ge hx.1 y hy.1
  let α := symplecticReductionForm ω (M ⊓ N) ha
  let β := symplecticReductionForm η (M' ⊓ N') hb
  have ha' := symplecticReductionForm_alt ω (M ⊓ N) ha
  have hb' := symplecticReductionForm_alt η (M' ⊓ N') hb
  have hred := general_lagrangian_reduction ω (M ⊓ N) ha hω hS
  have hred' := general_lagrangian_reduction η (M' ⊓ N') hb hη hS'
  obtain ⟨hpq,hpr,hqr,_hd1,_hd2,_hs⟩ :=
    triple_pair_reduction_intersections ω M N L hM hN hz
  obtain ⟨hpq',hpr',hqr',_hd1',_hd2',_hs'⟩ :=
    triple_pair_reduction_intersections η M' N' L' hM' hN' hz'
  have hh := triple_residual_isometry_reduce_pair ω η ha hb M N L M' N' L'
    hM hN hL hM' hN' hL' hz hz' h.rotate
  obtain ⟨r,hr,hrM,hrN,hrL⟩ := triple_isometry_of_zero_pairs α β ha' hb'
    _ _ _ _ _ _ (hred M hM) (hred N hN) (hred L hL)
    (hred' M' hM') (hred' N' hN') (hred' L' hL') hpq
    (by rw [hpr,inf_comm M L,hLM,reduceSubspace_bot])
    (by rw [hqr,inf_comm N L,hLN,reduceSubspace_bot]) hpq'
    (by rw [hpr',inf_comm M' L',hLM',reduceSubspace_bot])
    (by rw [hqr',inf_comm N' L',hLN',reduceSubspace_bot]) hh
  obtain ⟨e,he,heM,heN,heL⟩ := triple_one_block_lift ω η ha hb M N L M' N' L'
    hM hN hL hM' hN' hL' hz hz' hdim r hr hrM hrN hrL
  exact ⟨e,he,heL,heM,heN⟩
theorem triple_isometry_of_one_zero_pair
    (ω : LinearMap.BilinForm K E) (η : LinearMap.BilinForm K F)
    (ha : ω.IsAlt) (hb : η.IsAlt) (hω : ω.Nondegenerate) (hη : η.Nondegenerate)
    (L M N : Submodule K E) (L' M' N' : Submodule K F)
    (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M) (hN : ω.orthogonal N = N)
    (hL' : η.orthogonal L' = L') (hM' : η.orthogonal M' = M') (hN' : η.orthogonal N' = N')
    (hLM : L ⊓ M = ⊥) (hLM' : L' ⊓ M' = ⊥)
    (hdimLN : finrank K ↥(L ⊓ N) = finrank K ↥(L' ⊓ N'))
    (hdimMN : finrank K ↥(M ⊓ N) = finrank K ↥(M' ⊓ N'))
    (h : TripleResidualIsometry ω η ha hb L M N L' M' N') :
    TripleIsometry ω η L M N L' M' N' := by
  have hz : (L ⊓ N) ⊓ M = ⊥ := by
    calc
      _ = (L ⊓ M) ⊓ N := by ac_rfl
      _ = ⊥ := by rw [hLM,bot_inf_eq]
  have hz' : (L' ⊓ N') ⊓ M' = ⊥ := by
    calc
      _ = (L' ⊓ M') ⊓ N' := by ac_rfl
      _ = ⊥ := by rw [hLM',bot_inf_eq]
  have hS : L ⊓ N ≤ ω.orthogonal (L ⊓ N) := by
    intro x hx y hy
    exact hL.ge hx.1 y hy.1
  have hS' : L' ⊓ N' ≤ η.orthogonal (L' ⊓ N') := by
    intro x hx y hy
    exact hL'.ge hx.1 y hy.1
  let α := symplecticReductionForm ω (L ⊓ N) ha
  let β := symplecticReductionForm η (L' ⊓ N') hb
  have ha' := symplecticReductionForm_alt ω (L ⊓ N) ha
  have hb' := symplecticReductionForm_alt η (L' ⊓ N') hb
  have hω' := symplecticReductionForm_nondegenerate ω (L ⊓ N) ha hω
  have hη' := symplecticReductionForm_nondegenerate η (L' ⊓ N') hb hη
  have hred := general_lagrangian_reduction ω (L ⊓ N) ha hω hS
  have hred' := general_lagrangian_reduction η (L' ⊓ N') hb hη hS'
  obtain ⟨hpq,hpr,_hqr,_hd1,hd2,_hs⟩ :=
    triple_pair_reduction_intersections ω L N M hL hN hz
  obtain ⟨hpq',hpr',_hqr',_hd1',hd2',_hs'⟩ :=
    triple_pair_reduction_intersections η L' N' M' hL' hN' hz'
  have hh := triple_residual_isometry_reduce_pair ω η ha hb L N M L' N' M'
    hL hN hM hL' hN' hM' hz hz' h.swap_right
  obtain ⟨r,hr,hrL,hrN,hrM⟩ := triple_isometry_of_two_zero_pairs α β ha' hb' hω' hη'
    _ _ _ _ _ _ (hred L hL) (hred N hN) (hred M hM)
    (hred' L' hL') (hred' N' hN') (hred' M' hM') hpq
    (by rw [hpr,hLM,reduceSubspace_bot]) hpq'
    (by rw [hpr',hLM',reduceSubspace_bot])
    (by rw [hd2,hd2',inf_comm N M,inf_comm N' M']; exact hdimMN) hh
  obtain ⟨e,he,heL,heN,heM⟩ := triple_one_block_lift ω η ha hb L N M L' N' M'
    hL hN hM hL' hN' hM' hz hz' hdimLN r hr hrL hrN hrM
  exact ⟨e,he,heL,heM,heN⟩
theorem triple_common_zero_classification
    (ω : LinearMap.BilinForm K E) (η : LinearMap.BilinForm K F)
    (ha : ω.IsAlt) (hb : η.IsAlt) (hω : ω.Nondegenerate) (hη : η.Nondegenerate)
    (L M N : Submodule K E) (L' M' N' : Submodule K F)
    (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M) (hN : ω.orthogonal N = N)
    (hL' : η.orthogonal L' = L') (hM' : η.orthogonal M' = M') (hN' : η.orthogonal N' = N')
    (hzero : (L ⊓ M) ⊓ N = ⊥) (hzero' : (L' ⊓ M') ⊓ N' = ⊥)
    (hdimLM : finrank K ↥(L ⊓ M) = finrank K ↥(L' ⊓ M'))
    (hdimLN : finrank K ↥(L ⊓ N) = finrank K ↥(L' ⊓ N'))
    (hdimMN : finrank K ↥(M ⊓ N) = finrank K ↥(M' ⊓ N'))
    (h : TripleResidualIsometry ω η ha hb L M N L' M' N') :
    TripleIsometry ω η L M N L' M' N' := by
  have hS : L ⊓ M ≤ ω.orthogonal (L ⊓ M) := by
    intro x hx y hy
    exact hL.ge hx.1 y hy.1
  have hS' : L' ⊓ M' ≤ η.orthogonal (L' ⊓ M') := by
    intro x hx y hy
    exact hL'.ge hx.1 y hy.1
  let α := symplecticReductionForm ω (L ⊓ M) ha
  let β := symplecticReductionForm η (L' ⊓ M') hb
  have ha' := symplecticReductionForm_alt ω (L ⊓ M) ha
  have hb' := symplecticReductionForm_alt η (L' ⊓ M') hb
  have hω' := symplecticReductionForm_nondegenerate ω (L ⊓ M) ha hω
  have hη' := symplecticReductionForm_nondegenerate η (L' ⊓ M') hb hη
  have hred := general_lagrangian_reduction ω (L ⊓ M) ha hω hS
  have hred' := general_lagrangian_reduction η (L' ⊓ M') hb hη hS'
  obtain ⟨hpq,_hpr,_hqr,hd1,hd2,_hs⟩ :=
    triple_pair_reduction_intersections ω L M N hL hM hzero
  obtain ⟨hpq',_hpr',_hqr',hd1',hd2',_hs'⟩ :=
    triple_pair_reduction_intersections η L' M' N' hL' hM' hzero'
  have hh := triple_residual_isometry_reduce_pair ω η ha hb L M N L' M' N'
    hL hM hN hL' hM' hN' hzero hzero' h
  obtain ⟨r,hr,hrL,hrM,hrN⟩ := triple_isometry_of_one_zero_pair α β ha' hb' hω' hη'
    _ _ _ _ _ _ (hred L hL) (hred M hM) (hred N hN)
    (hred' L' hL') (hred' M' hM') (hred' N' hN') hpq hpq'
    (by rw [hd1,hd1']; exact hdimLN) (by rw [hd2,hd2']; exact hdimMN) hh
  exact triple_one_block_lift ω η ha hb L M N L' M' N' hL hM hN hL' hM' hN'
    hzero hzero' hdimLM r hr hrL hrM hrN
end FullClassification
end SidorenkoCounterexample
end OAI
namespace OAI
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
theorem card_le_card_mul_of_fibers {A B : Type*} [Finite A] [Finite B]
    (f : A → B) (m : ℕ) (h : ∀ b, Nat.card {a : A // f a = b} ≤ m) :
    Nat.card A ≤ Nat.card B * m := by
  classical
  let := Fintype.ofFinite A
  let := Fintype.ofFinite B
  calc
    Nat.card A = Nat.card (Σ b : B, {a : A // f a = b}) :=
      (Nat.card_congr (Equiv.sigmaFiberEquiv f)).symm
    _ = ∑ b : B, Nat.card {a : A // f a = b} := by
      simp only [Nat.card_eq_fintype_card,Fintype.card_sigma]
    _ ≤ ∑ _b : B, m := Finset.sum_le_sum (fun b _ => h b)
    _ = Nat.card B * m := by simp [Nat.card_eq_fintype_card]
section NormSphere
variable {K E : Type*} [Field K] [Fintype K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E] [Finite E]
theorem square_fiber_card (a : K) : Nat.card {x : K // x^2 = a} ≤ 2 := by
  classical
  by_cases h : ∃ x : K, x^2 = a
  · obtain ⟨x,hx⟩ := h
    let f : {z : K // z^2 = a} → (↑({x,-x} : Finset K)) := fun z =>
      ⟨z.val,by
        have hh : z.val = x ∨ z.val = -x := sq_eq_sq_iff_eq_or_eq_neg.mp (z.property.trans hx.symm)
        simpa only [Finset.mem_insert,Finset.mem_singleton] using hh⟩
    have hf : Function.Injective f := by
      intro z w he
      apply Subtype.ext
      exact congrArg (fun t : ↑({x,-x} : Finset K) => (t : K)) he
    calc
      _ ≤ Nat.card (↑({x,-x} : Finset K)) := Nat.card_le_card_of_injective f hf
      _ = ({x,-x} : Finset K).card := by
        rw [Nat.card_eq_fintype_card]
        exact Fintype.card_coe _
      _ ≤ 2 := Finset.card_le_two
  · have he : IsEmpty {x : K // x^2 = a} := ⟨fun x => h ⟨x.val,x.property⟩⟩
    let := he
    simp
omit [FiniteDimensional K E] in
theorem norm_sphere_count (B : LinearMap.BilinForm K E) (hs : B.IsSymm)
    (x : E) (hx : B x x ≠ 0) (a : K) :
    Nat.card {v : E // B v v = a} ≤
      2 * Nat.card (B.orthogonal (K ∙ x)) := by
  classical
  have hx0 : x ≠ 0 := by intro hh; subst x; simp at hx
  let P := B.orthogonal (K ∙ x)
  let c : ((K ∙ x) × P) ≃ₗ[K] E :=
    (K ∙ x).prodEquivOfIsCompl P (B.isCompl_span_singleton_orthogonal hx)
  let e : (K × P) ≃ₗ[K] E :=
    ((LinearEquiv.toSpanNonzeroSingleton K E x hx0).prodCongr (LinearEquiv.refl K P)).trans c
  have he (z : K × P) : e z = z.1 • x + z.2.val := rfl
  have hnorm (z : K × P) : B (e z) (e z) = z.1^2 * B x x + B z.2.val z.2.val := by
    have h1 : B x z.2.val = 0 := z.2.property x (Submodule.mem_span_singleton_self x)
    have h2 : B z.2.val x = 0 := hs.eq _ _ ▸ h1
    rw [he]
    simp only [map_add,map_smul,LinearMap.add_apply,LinearMap.smul_apply,
      smul_eq_mul,h1,h2,mul_zero,add_zero,zero_add]
    ring
  let f : {v : E // B v v = a} → P := fun v => (e.symm v.val).2
  have hf (p : P) : Nat.card {v : {v : E // B v v = a} // f v = p} ≤ 2 := by
    let g : {v : {v : E // B v v = a} // f v = p} →
        {t : K // t^2 = (a - B p.val p.val) / B x x} := fun v =>
      ⟨(e.symm v.val.val).1,by
        have hh := hnorm (e.symm v.val.val)
        have hv : (e.symm v.val.val).2 = p := v.property
        rw [e.apply_symm_apply,v.val.property,hv] at hh
        apply (eq_div_iff hx).mpr
        linear_combination -hh⟩
    have hg : Function.Injective g := by
      intro v w h
      apply Subtype.ext
      apply Subtype.ext
      apply e.symm.injective
      apply Prod.ext
      · exact congrArg Subtype.val h
      · exact v.property.trans w.property.symm
    exact (Nat.card_le_card_of_injective g hg).trans (square_fiber_card _)
  exact (card_le_card_mul_of_fibers f 2 hf).trans_eq (Nat.mul_comm _ _)
theorem norm_sphere_count_pow (B : LinearMap.BilinForm K E) (hs : B.IsSymm)
    (x : E) (hx : B x x ≠ 0) (a : K) :
    Nat.card {v : E // B v v = a} ≤ 2 * Fintype.card K ^ (finrank K E - 1) := by
  have hx0 : x ≠ 0 := by intro hh; subst x; simp at hx
  have hd := Submodule.finrank_add_eq_of_isCompl (B.isCompl_span_singleton_orthogonal hx)
  rw [finrank_span_singleton hx0] at hd
  have hp : finrank K (B.orthogonal (K ∙ x)) = finrank K E - 1 := by omega
  have hc : Nat.card (B.orthogonal (K ∙ x)) = Fintype.card K ^ (finrank K E - 1) := by
    rw [Module.natCard_eq_pow_finrank (K := K), hp, Nat.card_eq_fintype_card]
  exact (norm_sphere_count B hs x hx a).trans_eq (congrArg (2 * ·) hc)
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
noncomputable def restrictBilinAut (B : LinearMap.BilinForm K E)
    (x : E) (e : BilinAut B) (hfix : e.val x = x) :
    BilinAut (B.restrict (B.orthogonal (K ∙ x))) := by
  let P := B.orthogonal (K ∙ x)
  have hp : ∀ z ∈ P, e.val z ∈ P := by
    intro z hz a ha
    obtain ⟨t,rfl⟩ := Submodule.mem_span_singleton.mp ha
    have hh : B x (e.val z) = 0 := by
      calc
        _ = B (e.val x) (e.val z) := by rw [hfix]
        _ = B x z := e.property x z
        _ = 0 := hz x (Submodule.mem_span_singleton_self x)
    simp [hh]
  let g : P →ₗ[K] P := e.val.toLinearMap.restrict hp
  have hg : Function.Injective g := by
    intro z w h
    apply Subtype.ext
    exact e.val.injective (congrArg Subtype.val h)
  let f : P ≃ₗ[K] P := LinearEquiv.ofBijective g
    ⟨hg,LinearMap.injective_iff_surjective.mp hg⟩
  refine ⟨f,?_⟩
  intro z w
  exact e.property z.val w.val
@[simp] theorem restrictBilinAut_apply (B : LinearMap.BilinForm K E)
    (x : E) (e : BilinAut B) (hfix : e.val x = x)
    (z : B.orthogonal (K ∙ x)) :
    ((restrictBilinAut B x e hfix).val z).val = e.val z.val := rfl
theorem restrictBilinAut_injective (B : LinearMap.BilinForm K E)
    (x : E) (hx : B x x ≠ 0) :
    Function.Injective (fun e : {e : BilinAut B // e.val x = x} =>
      restrictBilinAut B x e.val e.property) := by
  intro e f h
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.ext
  intro z
  have hz : z ∈ (K ∙ x) ⊔ B.orthogonal (K ∙ x) := by
    rw [(B.isCompl_span_singleton_orthogonal hx).sup_eq_top]
    trivial
  obtain ⟨a,ha,p,hp,rfl⟩ := Submodule.mem_sup.mp hz
  obtain ⟨t,rfl⟩ := Submodule.mem_span_singleton.mp ha
  have hh := congrArg (fun g : BilinAut (B.restrict (B.orthogonal (K ∙ x))) =>
    (g.val (⟨p,hp⟩ : B.orthogonal (K ∙ x))).val) h
  change e.val.val p = f.val.val p at hh
  simp only [map_add,map_smul,e.property,f.property,hh]
noncomputable def relativeBilinAut (B : LinearMap.BilinForm K E)
    (e f : BilinAut B) : BilinAut B :=
  ⟨e.val.trans f.val.symm,by
    intro x y
    have hf := f.property (f.val.symm (e.val x)) (f.val.symm (e.val y))
    simp only [LinearEquiv.apply_symm_apply] at hf
    exact hf.symm.trans (e.property x y)⟩
omit [FiniteDimensional K E] in
theorem relativeBilinAut_injective (B : LinearMap.BilinForm K E) (f : BilinAut B) :
    Function.Injective (fun e => relativeBilinAut B e f) := by
  intro e g h
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  have hh := congrArg (fun a : BilinAut B => f.val (a.val x)) h
  simpa only [relativeBilinAut,LinearEquiv.trans_apply,LinearEquiv.apply_symm_apply] using hh
variable [Finite E]
theorem bilinAut_eval_fiber_bound (B : LinearMap.BilinForm K E) (x y : E)
    (hx : B x x ≠ 0) :
    Nat.card {e : BilinAut B // e.val x = y} ≤
      Nat.card (BilinAut (B.restrict (B.orthogonal (K ∙ x)))) := by
  classical
  by_cases hn : Nonempty {e : BilinAut B // e.val x = y}
  · let e0 := hn.some
    let f : {e : BilinAut B // e.val x = y} → {e : BilinAut B // e.val x = x} := fun e =>
      ⟨relativeBilinAut B e.val e0.val,by
        change e0.val.val.symm (e.val.val x) = x
        exact (congrArg e0.val.val.symm (e.property.trans e0.property.symm)).trans
          (e0.val.val.symm_apply_apply x)⟩
    have hf : Function.Injective f := by
      intro e g h
      apply Subtype.ext
      apply relativeBilinAut_injective B e0.val
      exact congrArg Subtype.val h
    exact (Nat.card_le_card_of_injective f hf).trans
      (Nat.card_le_card_of_injective _ (restrictBilinAut_injective B x hx))
  · have : IsEmpty {e : BilinAut B // e.val x = y} := not_nonempty_iff.mp hn
    let := this
    simp
theorem bilinAut_step (B : LinearMap.BilinForm K E) (x : E) (hx : B x x ≠ 0) :
    Nat.card (BilinAut B) ≤ Nat.card {y : E // B y y = B x x} *
      Nat.card (BilinAut (B.restrict (B.orthogonal (K ∙ x)))) := by
  let s : BilinAut B → {y : E // B y y = B x x} := fun e => ⟨e.val x,e.property x x⟩
  apply card_le_card_mul_of_fibers s
  intro y
  let f : {e : BilinAut B // s e = y} → {e : BilinAut B // e.val x = y.val} :=
    fun e => ⟨e.val,congrArg Subtype.val e.property⟩
  have hf : Function.Injective f := by
    intro e g h
    apply Subtype.ext
    exact congrArg (fun t : {e : BilinAut B // e.val x = y.val} => t.val) h
  exact (Nat.card_le_card_of_injective f hf).trans (bilinAut_eval_fiber_bound B x y.val hx)
variable [Fintype K] [Invertible (2 : K)]
theorem bilinAut_card_bound (B : LinearMap.BilinForm K E) (hs : B.IsSymm)
    (hB : B.Nondegenerate) :
    Nat.card (BilinAut B) ≤ 2 ^ finrank K E * Fintype.card K ^ (finrank K E).choose 2 := by
  suffices ∀ d, finrank K E = d →
      Nat.card (BilinAut B) ≤ 2 ^ d * Fintype.card K ^ d.choose 2 by exact this _ rfl
  intro d hd
  induction d generalizing E with
  | zero =>
    have : Subsingleton E := Module.finrank_zero_iff.mp hd
    have : Subsingleton (BilinAut B) := by
      refine ⟨fun e f => ?_⟩
      apply Subtype.ext
      apply LinearEquiv.ext
      intro x
      exact Subsingleton.elim _ _
    simpa using Nat.card_le_card_of_injective (fun _ : BilinAut B => ())
      (fun _ _ _ => Subsingleton.elim _ _)
  | succ d ih =>
    have hB0 : B ≠ 0 := by
      intro hh
      have hz : ∀ x : E, x = 0 := by
        intro x
        apply hB.1
        intro y
        rw [hh]
        rfl
      have hh0 : finrank K E = 0 := (finrank_zero_iff_forall_zero).mpr hz
      omega
    obtain ⟨x,hx⟩ := LinearMap.BilinForm.exists_bilinForm_self_ne_zero hB0 (LinearMap.BilinForm.isSymm_iff.mp hs)
    have hx0 : x ≠ 0 := by intro hh; subst x; simp at hx
    let P := B.orthogonal (K ∙ x)
    have hP : finrank K P = d := by
      change finrank K (B.orthogonal (K ∙ x)) = d
      have hh := Submodule.finrank_add_eq_of_isCompl (B.isCompl_span_singleton_orthogonal hx)
      rw [finrank_span_singleton hx0,hd] at hh
      omega
    have hp := ih (B.restrict P) (by constructor; intro x y; exact hs.eq x.val y.val)
      (B.restrict_nondegenerate_orthogonal_spanSingleton hB hs.isRefl hx) hP
    have hn := norm_sphere_count_pow B hs x hx (B x x)
    rw [hd,Nat.add_sub_cancel] at hn
    calc
      _ ≤ Nat.card {y : E // B y y = B x x} * Nat.card (BilinAut (B.restrict P)) :=
        bilinAut_step B x hx
      _ ≤ (2 * Fintype.card K ^ d) * (2^d * Fintype.card K ^ d.choose 2) :=
        Nat.mul_le_mul hn hp
      _ = 2 ^ (d+1) * Fintype.card K ^ (d+1).choose 2 := by
        rw [Nat.choose_succ_succ,Nat.choose_one_right,pow_add,pow_succ]
        ring
end Isometries
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section FormOrbits
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]
noncomputable def linearAutTuple : (E ≃ₗ[K] E) →
    {v : Fin (finrank K E) → E // LinearIndependent K v} := fun e =>
  ⟨fun i => e (finBasis K E i), (finBasis K E).linearIndependent.map' e.toLinearMap
    (LinearMap.ker_eq_bot.mpr e.injective)⟩
theorem linearAutTuple_bijective : Function.Bijective (linearAutTuple (K := K) (E := E)) := by
  constructor
  · intro e f h
    apply LinearEquiv.toLinearMap_injective
    apply (finBasis K E).ext
    intro i
    exact congrFun (congrArg Subtype.val h) i
  · intro v
    have hspan : Submodule.span K (Set.range v.val) = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [finrank_span_eq_card v.property,Fintype.card_fin]
    let b : Basis (Fin (finrank K E)) K E := Basis.mk v.property (by rw [hspan])
    refine ⟨(finBasis K E).equiv b (Equiv.refl _),?_⟩
    apply Subtype.ext
    funext i
    simp [linearAutTuple,b]
variable [Fintype K] [Finite E]
theorem linearAut_card : Nat.card (E ≃ₗ[K] E) =
    ∏ i : Fin (finrank K E), (Fintype.card K ^ finrank K E - Fintype.card K ^ i.val) := by
  rw [Nat.card_congr (Equiv.ofBijective _ (linearAutTuple_bijective (K := K) (E := E)))]
  exact card_linearIndependent le_rfl
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
def formOrbitMap (B : LinearMap.BilinForm K E) (e : E ≃ₗ[K] E) : FormOrbit B :=
  ⟨B.comp e.toLinearMap e.toLinearMap,⟨e,rfl⟩⟩
omit [FiniteDimensional K E] [Fintype K] in
theorem formOrbit_fiber_bound (B : LinearMap.BilinForm K E) (C : FormOrbit B) :
    Nat.card {e : E ≃ₗ[K] E // formOrbitMap B e = C} ≤ Nat.card (BilinAut B) := by
  classical
  obtain ⟨e0,he0⟩ := C.property
  let f : {e : E ≃ₗ[K] E // formOrbitMap B e = C} → BilinAut B := fun e =>
    ⟨e0.symm.trans e.val,by
      intro x y
      have hh := congrArg (fun D : FormOrbit B => D.val (e0.symm x) (e0.symm y)) e.property
      change B (e.val (e0.symm x)) (e.val (e0.symm y)) = C.val (e0.symm x) (e0.symm y) at hh
      rw [he0] at hh
      simpa only [LinearMap.BilinForm.comp_apply,LinearEquiv.coe_coe,
        LinearEquiv.apply_symm_apply,LinearEquiv.trans_apply] using hh⟩
  apply Nat.card_le_card_of_injective f
  intro e g h
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  have hh := congrArg (fun a : BilinAut B => a.val (e0 x)) h
  simpa only [f,LinearEquiv.trans_apply,LinearEquiv.symm_apply_apply] using hh
omit [FiniteDimensional K E] in
theorem formOrbit_card_mul_bound (B : LinearMap.BilinForm K E) :
    Nat.card (E ≃ₗ[K] E) ≤ Nat.card (FormOrbit B) * Nat.card (BilinAut B) :=
  card_le_card_mul_of_fibers (formOrbitMap B) _ (formOrbit_fiber_bound B)
theorem linearAut_card_lower : Fintype.card K ^ (finrank K E * finrank K E) ≤
    2 ^ finrank K E * Nat.card (E ≃ₗ[K] E) := by
  rw [linearAut_card]
  have hq : 2 ≤ Fintype.card K := Fintype.one_lt_card
  have hfac (i : Fin (finrank K E)) : Fintype.card K ^ finrank K E ≤
      2 * (Fintype.card K ^ finrank K E - Fintype.card K ^ i.val) := by
    have hle : Fintype.card K ^ (i.val+1) ≤ Fintype.card K ^ finrank K E :=
      Nat.pow_le_pow_right (by omega) i.isLt
    have hh : 2 * Fintype.card K ^ i.val ≤ Fintype.card K ^ finrank K E := by
      calc
        _ ≤ Fintype.card K * Fintype.card K ^ i.val := Nat.mul_le_mul_right _ hq
        _ = Fintype.card K ^ (i.val+1) := by rw [pow_succ]; ring
        _ ≤ _ := hle
    omega
  calc
    _ = ∏ _i : Fin (finrank K E), Fintype.card K ^ finrank K E := by
      simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,←pow_mul]
    _ ≤ ∏ i : Fin (finrank K E), 2 * (Fintype.card K ^ finrank K E - Fintype.card K ^ i.val) :=
      Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun i _ => hfac i)
    _ = _ := by rw [Finset.prod_mul_distrib]; simp
variable [Invertible (2 : K)]
theorem formOrbit_card_lower (B : LinearMap.BilinForm K E) (hs : B.IsSymm)
    (hB : B.Nondegenerate) :
    Fintype.card K ^ (finrank K E+1).choose 2 ≤
      4 ^ finrank K E * Nat.card (FormOrbit B) := by
  let d := finrank K E
  let q := Fintype.card K
  have h1 := (linearAut_card_lower (K := K) (E := E)).trans
    (Nat.mul_le_mul_left (2^d) (formOrbit_card_mul_bound B))
  have h2 := Nat.mul_le_mul_left (2^d * Nat.card (FormOrbit B)) (bilinAut_card_bound B hs hB)
  have hh : q^(d*d) ≤ (4^d * Nat.card (FormOrbit B)) * q^d.choose 2 := by
    calc
      _ ≤ 2^d * (Nat.card (FormOrbit B) * Nat.card (BilinAut B)) := h1
      _ = (2^d * Nat.card (FormOrbit B)) * Nat.card (BilinAut B) := by ring
      _ ≤ (2^d * Nat.card (FormOrbit B)) * (2^d * q^d.choose 2) := h2
      _ = _ := by rw [show (4 : ℕ) = 2*2 from rfl,mul_pow]; ring
  have hd : d*d = (d+1).choose 2 + d.choose 2 := by
    have hc : ∀ n : ℕ, n*n = n + 2*n.choose 2 := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Nat.choose_succ_succ,Nat.choose_one_right]
        nlinarith
    rw [Nat.choose_succ_succ,Nat.choose_one_right]
    linear_combination hc d
  rw [hd,pow_add] at hh
  exact Nat.le_of_mul_le_mul_right hh (pow_pos Fintype.card_pos _)
end FormOrbits
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section TransverseForms
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
theorem fullGraph_injective : Function.Injective
    (fun B : LinearMap.BilinForm K V => B.graph) := by
  intro B C h
  change B.graph = C.graph at h
  apply LinearMap.ext
  intro x
  have hx : (x,B x) ∈ C.graph := by rw [← h]; rfl
  exact (C.mem_graph_iff _).mp hx
def formCoordinateEquiv (g : V ≃ₗ[K] V) :
    (V × Module.Dual K V) ≃ₗ[K] (V × Module.Dual K V) :=
  g.symm.prodCongr g.dualMap
theorem formCoordinateEquiv_isometry (g : V ≃ₗ[K] V) (x y : V × Module.Dual K V) :
    canonicalSymplectic (formCoordinateEquiv g x) (formCoordinateEquiv g y) =
      canonicalSymplectic x y := by
  simp [formCoordinateEquiv,canonicalSymplectic_apply]
theorem fullGraph_congruence (B : LinearMap.BilinForm K V) (g : V ≃ₗ[K] V) :
    B.graph.map (formCoordinateEquiv g).toLinearMap = (B.comp g.toLinearMap g.toLinearMap).graph := by
  apply subspace_map_eq_of_mem_iff
  intro x
  change g.dualMap x.2 = (B.comp g.toLinearMap g.toLinearMap) (g.symm x.1) ↔ x.2 = B x.1
  constructor
  · intro h
    ext y
    have hh := LinearMap.congr_fun h (g.symm y)
    simpa [LinearEquiv.dualMap_apply,LinearMap.BilinForm.comp_apply] using hh
  · intro h
    ext y
    simp [LinearEquiv.dualMap_apply,LinearMap.BilinForm.comp_apply,h]
end TransverseForms
section TransverseTripleCoordinates
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E)
theorem exists_transverse_triple_form (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (L M N : Submodule K E) (hL : ω.orthogonal L = L)
    (hM : ω.orthogonal M = M) (hN : ω.orthogonal N = N)
    (hLM : L ⊓ M = ⊥) (hLN : L ⊓ N = ⊥) (hMN : M ⊓ N = ⊥) :
    ∃ (e : (L × Module.Dual K L) ≃ₗ[K] E) (B : LinearMap.BilinForm K L),
      B.IsSymm ∧ B.Nondegenerate ∧
      (∀ x, e x ∈ L ↔ x.2 = 0) ∧ (∀ x, e x ∈ M ↔ x.1 = 0) ∧
      (∀ x, e x ∈ N ↔ x.2 = B x.1) ∧
      (∀ x y, ω (e x) (e y) = canonicalSymplectic x y) := by
  obtain ⟨e,heL,heM,heform⟩ := exists_transverse_pair_coordinates ω ha hω L M hL hM hLM
  let p : N →ₗ[K] L := (LinearMap.fst K L (Module.Dual K L)).comp
    (e.symm.toLinearMap.comp N.subtype)
  have hp : Function.Injective p := by
    apply (LinearMap.ker_eq_bot).mp
    apply (Submodule.eq_bot_iff _).mpr
    intro n hn
    have hm : n.val ∈ M := by
      have hh : e (e.symm n.val) ∈ M := (heM _).mpr hn
      simpa only [e.apply_symm_apply] using hh
    have hz : n.val ∈ M ⊓ N := ⟨hm,n.property⟩
    apply Subtype.ext
    change n.val = 0
    simpa only [hMN,Submodule.mem_bot] using hz
  have hd : finrank K N = finrank K L := by
    have h1 := self_orthogonal_twice_finrank ω N hω hN
    have h2 := self_orthogonal_twice_finrank ω L hω hL
    omega
  let a : N ≃ₗ[K] L := LinearEquiv.ofBijective p
    ⟨hp,(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mp hp⟩
  let B : LinearMap.BilinForm K L := (LinearMap.snd K L (Module.Dual K L)).comp
    (e.symm.toLinearMap.comp (N.subtype.comp a.symm.toLinearMap))
  have hcoord (x : L) : e.symm (a.symm x).val = (x,B x) := by
    apply Prod.ext
    · exact a.apply_symm_apply x
    · rfl
  have hNgraph (x : L × Module.Dual K L) : e x ∈ N ↔ x.2 = B x.1 := by
    constructor
    · intro hx
      let n : N := ⟨e x,hx⟩
      have haN : a n = x.1 := by
        change (e.symm (e x)).1 = x.1
        rw [e.symm_apply_apply]
      have hh := hcoord (a n)
      rw [a.symm_apply_apply,haN] at hh
      have hh' := congrArg Prod.snd hh
      change (e.symm (e x)).2 = B x.1 at hh'
      simpa only [e.symm_apply_apply] using hh'
    · intro hx
      have hh := congrArg e (hcoord x.1)
      rw [e.apply_symm_apply,← hx] at hh
      exact hh ▸ (a.symm x.1).property
  have hs : B.IsSymm := by
    constructor
    intro x y
    have hh := hN.ge ((a.symm y).property) (a.symm x).val ((a.symm x).property)
    rw [← e.apply_symm_apply (a.symm x).val,← e.apply_symm_apply (a.symm y).val,
      heform,hcoord,hcoord] at hh
    change B y x - B x y = 0 at hh
    exact (sub_eq_zero.mp hh).symm
  have hleft (x : L) (hx : ∀ y, B x y = 0) : x = 0 := by
    have hxB : B x = 0 := by ext y; exact hx y
    have hxL : (a.symm x).val ∈ L := by
      have hh := (heL (x,B x)).mpr hxB
      have hc := congrArg e (hcoord x)
      rw [e.apply_symm_apply] at hc
      exact hc.symm ▸ hh
    have hz : (a.symm x).val ∈ L ⊓ N := ⟨hxL,(a.symm x).property⟩
    have hn0 : a.symm x = 0 := Subtype.ext (by
      change (a.symm x).val = 0
      simpa only [hLN,Submodule.mem_bot] using hz)
    have hh := congrArg a hn0
    simpa only [a.apply_symm_apply,map_zero] using hh
  refine ⟨e,B,hs,⟨hleft,?_⟩,heL,heM,hNgraph,heform⟩
  intro x hx
  exact hleft x (fun y => (hs.eq x y).trans (hx y))
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
theorem fixedPairOrbit_form_injection (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M) (hN : ω.orthogonal N = N)
    (hLM : L ⊓ M = ⊥) (hLN : L ⊓ N = ⊥) (hMN : M ⊓ N = ⊥) :
    ∃ B : LinearMap.BilinForm K L, B.IsSymm ∧ B.Nondegenerate ∧
      ∃ f : FormOrbit B → FixedPairOrbit ω L M N, Function.Injective f := by
  classical
  obtain ⟨e,B,hs,hB,heL,heM,heN,heform⟩ :=
    exists_transverse_triple_form ω ha hω L M N hL hM hN hLM hLN hMN
  have hgood (C : FormOrbit B) :
      ∃ f : E ≃ₗ[K] E, (∀ x y, ω (f x) (f y) = ω x y) ∧
        L.map f.toLinearMap = L ∧ M.map f.toLinearMap = M ∧
        N.map f.toLinearMap = C.val.graph.map e.toLinearMap := by
    obtain ⟨g,hg⟩ := C.property
    let f := e.symm.trans ((formCoordinateEquiv g).trans e)
    refine ⟨f,?_,?_,?_,?_⟩
    · intro x y
      change ω (e (formCoordinateEquiv g (e.symm x)))
        (e (formCoordinateEquiv g (e.symm y)))=ω x y
      rw [heform,formCoordinateEquiv_isometry,←heform,e.apply_symm_apply,e.apply_symm_apply]
    · apply subspace_map_eq_of_mem_iff f
      intro x
      change e (formCoordinateEquiv g (e.symm x)) ∈ L ↔ x ∈ L
      rw [heL]
      change g.dualMap (e.symm x).2 = 0 ↔ x ∈ L
      rw [LinearEquiv.map_eq_zero_iff]
      simpa only [e.apply_symm_apply] using (heL (e.symm x)).symm
    · apply subspace_map_eq_of_mem_iff f
      intro x
      change e (formCoordinateEquiv g (e.symm x)) ∈ M ↔ x ∈ M
      rw [heM]
      change g.symm (e.symm x).1 = 0 ↔ x ∈ M
      rw [LinearEquiv.map_eq_zero_iff]
      simpa only [e.apply_symm_apply] using (heM (e.symm x)).symm
    · apply subspace_map_eq_of_mem_iff f
      intro x
      rw [Submodule.mem_map_equiv]
      change e.symm (e (formCoordinateEquiv g (e.symm x))) ∈ C.val.graph ↔ x ∈ N
      rw [e.symm_apply_apply,hg,←fullGraph_congruence,Submodule.mem_map_equiv]
      rw [LinearEquiv.symm_apply_apply,LinearMap.mem_graph_iff]
      simpa only [e.apply_symm_apply] using (heN (e.symm x)).symm
  let f : FormOrbit B → FixedPairOrbit ω L M N :=
    fun C => ⟨C.val.graph.map e.toLinearMap,hgood C⟩
  refine ⟨B,hs,hB,f,?_⟩
  intro C D h
  apply Subtype.ext
  apply fullGraph_injective
  exact Submodule.map_injective_of_injective e.injective (congrArg Subtype.val h)
variable [Fintype K] [Finite E] [Invertible (2 : K)]
theorem fixedPairOrbit_card_lower (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M) (hN : ω.orthogonal N = N)
    (hLM : L ⊓ M = ⊥) (hLN : L ⊓ N = ⊥) (hMN : M ⊓ N = ⊥) :
    Fintype.card K ^ (finrank K L+1).choose 2 ≤
      4 ^ finrank K L * Nat.card (FixedPairOrbit ω L M N) := by
  obtain ⟨B,hs,hB,f,hf⟩ := fixedPairOrbit_form_injection ω L M N ha hω hL hM hN hLM hLN hMN
  exact (formOrbit_card_lower B hs hB).trans
    (Nat.mul_le_mul_left _ (Nat.card_le_card_of_injective f hf))
end FixedPairOrbit
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section UniformCountingBounds
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Fintype K] [Finite V]
theorem lagrangian_card_by_dimension :
    Nat.card (Lagrangian (K := K) (V := V)) =
      ∑ k : Fin (finrank K V+1), Nat.card (DimSubspace K V k.val) *
        Fintype.card K ^ (k.val+1).choose 2 := by
  classical
  let := Fintype.ofFinite (Submodule K V)
  let d : Submodule K V → Fin (finrank K V+1) :=
    fun U => ⟨finrank K U,Nat.lt_succ_of_le (Submodule.finrank_le U)⟩
  rw [lagrangian_card_sum,← Fintype.sum_fiberwise d]
  apply Finset.sum_congr rfl
  intro k _
  have hc : Nat.card {U : Submodule K V // d U = k} = Nat.card (DimSubspace K V k.val) :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun U => by
      change (⟨finrank K U,_⟩ : Fin _)=k ↔ finrank K U=k.val
      exact Fin.ext_iff))
  have he (U : {U : Submodule K V // d U = k}) : finrank K U.val = k.val :=
    congrArg Fin.val U.property
  simp only [he,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,←Nat.card_eq_fintype_card,hc,Nat.cast_id]
noncomputable def lagrangianConstant (n : ℕ) : ℝ := (n+1) * 2^n
theorem lagrangianConstant_pos (n : ℕ) : 0 < lagrangianConstant n := by
  unfold lagrangianConstant
  positivity
theorem lagrangian_card_upper :
    (Nat.card (Lagrangian (K := K) (V := V)) : ℝ) ≤
      lagrangianConstant (finrank K V) * (Fintype.card K : ℝ)^((finrank K V+1).choose 2) := by
  rw [lagrangian_card_by_dimension,Nat.cast_sum]
  let n := finrank K V
  let q : ℝ := Fintype.card K
  have hq : 1 ≤ q := by
    dsimp [q]
    exact_mod_cast (Nat.succ_le_iff.mpr (Fintype.card_pos (α := K)))
  have hterm (k : Fin (n+1)) :
      (Nat.card (DimSubspace K V k.val) : ℝ) * q^(k.val+1).choose 2 ≤
        2^n*q^(n+1).choose 2 := by
    have hk : k.val ≤ n := Nat.le_of_lt_succ k.isLt
    have he : k.val*(n-k.val)+(k.val+1).choose 2 ≤ (n+1).choose 2 := by
      have hh := symmetric_nullity_exponent n (n-k.val) (Nat.sub_le n k.val)
      rw [Nat.sub_sub_self hk] at hh
      nlinarith
    calc
      _ ≤ (2^k.val*q^(k.val*(n-k.val)))*q^(k.val+1).choose 2 :=
        mul_le_mul_of_nonneg_right (subspace_count_upper k.val hk) (by positivity)
      _ = 2^k.val*q^(k.val*(n-k.val)+(k.val+1).choose 2) := by rw [pow_add]; ring
      _ ≤ 2^n*q^(n+1).choose 2 := mul_le_mul
        (pow_le_pow_right₀ (by norm_num) hk) (pow_le_pow_right₀ hq he) (by positivity) (by positivity)
  calc
    _ ≤ ∑ _k : Fin (n+1), 2^n*q^(n+1).choose 2 := by
      apply Finset.sum_le_sum
      intro k _
      simpa only [Nat.cast_mul,Nat.cast_pow] using hterm k
    _ = _ := by simp [lagrangianConstant,n,q]; ring
theorem lagrangian_card_lower :
    (Fintype.card K : ℝ)^((finrank K V+1).choose 2) ≤
      Nat.card (Lagrangian (K := K) (V := V)) := by
  let : Finite (Module.Dual K V) := Module.finite_of_finite K
  have h := Nat.card_le_card_of_injective (graphLagrangian (K := K) (V := V) (⊤ : Submodule K V))
    (graphLagrangian_form_injective (⊤ : Submodule K V))
  rw [symForm_card] at h
  simpa only [finrank_top,Nat.cast_pow] using (show
    ((Fintype.card K^((finrank K ↥(⊤ : Submodule K V)+1).choose 2) : ℕ) : ℝ) ≤
      (Nat.card (Lagrangian (K := K) (V := V)) : ℝ) from by exact_mod_cast h)
end UniformCountingBounds
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section FullTripleOrbit
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E)
abbrev SymplecticLagrangian := {L : Submodule K E // ω.orthogonal L = L}
abbrev OrderedTransversePair := {p : SymplecticLagrangian ω × SymplecticLagrangian ω //
  p.1.val ⊓ p.2.val = ⊥}
abbrev OrderedTripleOrbit (L M N : Submodule K E) :=
  {p : Submodule K E × Submodule K E × Submodule K E //
    ∃ e : E ≃ₗ[K] E, (∀ x y, ω (e x) (e y) = ω x y) ∧
      L.map e.toLinearMap = p.1 ∧ M.map e.toLinearMap = p.2.1 ∧
      N.map e.toLinearMap = p.2.2}
variable [FiniteDimensional K E]
theorem orderedTripleOrbit_pair_injection (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (L M N : Submodule K E) (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M)
    (hLM : L ⊓ M = ⊥) :
    ∃ f : OrderedTransversePair ω × FixedPairOrbit ω L M N → OrderedTripleOrbit ω L M N,
      Function.Injective f := by
  classical
  have ht (p : OrderedTransversePair ω) := transverse_pair_transitivity ω ha hω
    L M p.val.1.val p.val.2.val hL hM p.val.1.property p.val.2.property hLM p.property
  let e (p : OrderedTransversePair ω) := (ht p).choose
  have he (p) := (ht p).choose_spec
  have hgood (p : OrderedTransversePair ω) (N' : FixedPairOrbit ω L M N) :
      ∃ f : E ≃ₗ[K] E, (∀ x y, ω (f x) (f y) = ω x y) ∧
        L.map f.toLinearMap = p.val.1.val ∧ M.map f.toLinearMap = p.val.2.val ∧
        N.map f.toLinearMap = N'.val.map (e p).toLinearMap := by
    obtain ⟨g,hg,hgL,hgM,hgN⟩ := N'.property
    refine ⟨g.trans (e p),?_,?_,?_,?_⟩
    · intro x y
      exact ((he p).1 (g x) (g y)).trans (hg x y)
    · change L.map ((e p).toLinearMap.comp g.toLinearMap) = _
      rw [Submodule.map_comp,hgL]
      exact (he p).2.1
    · change M.map ((e p).toLinearMap.comp g.toLinearMap) = _
      rw [Submodule.map_comp,hgM]
      exact (he p).2.2
    · change N.map ((e p).toLinearMap.comp g.toLinearMap) = _
      rw [Submodule.map_comp,hgN]
  let f : OrderedTransversePair ω × FixedPairOrbit ω L M N → OrderedTripleOrbit ω L M N :=
    fun x => ⟨(x.1.val.1.val,x.1.val.2.val,x.2.val.map (e x.1).toLinearMap),hgood x.1 x.2⟩
  refine ⟨f,?_⟩
  rintro ⟨p,A⟩ ⟨q,B⟩ h
  have hv := congrArg Subtype.val h
  have hp : p = q := by
    apply Subtype.ext
    apply Prod.ext
    · exact Subtype.ext (congrArg Prod.fst hv)
    · exact Subtype.ext (congrArg (fun x => x.2.1) hv)
  subst q
  have hab : A = B := by
    apply Subtype.ext
    exact Submodule.map_injective_of_injective (e p).injective
      (congrArg (fun x => x.2.2) hv)
  subst B
  rfl
end FullTripleOrbit
section CanonicalTripleMass
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Fintype K] [Finite V]
 theorem transverse_to_card (h2 : (2 : K) ≠ 0) (A : Lagrangian (K := K) (V := V)) :
    Nat.card {B : Lagrangian (K := K) (V := V) // A.val ⊓ B.val = ⊥} =
      Fintype.card K^((finrank K V+1).choose 2) := by
  have h := lagrangian_pair_count h2 A 0 (Nat.zero_le _)
  have hc : Nat.card {U : Submodule K V // finrank K U = finrank K V} = 1 := by
    let : Unique {U : Submodule K V // finrank K U = finrank K V} :=
      ⟨⟨⊤,finrank_top K V⟩,fun U => Subtype.ext (Submodule.eq_top_of_finrank_eq U.property)⟩
    exact Nat.card_unique
  have he : {B : Lagrangian (K := K) (V := V) // A.val ⊓ B.val = ⊥} ≃
      {B : Lagrangian (K := K) (V := V) // finrank K ↥(B.val ⊓ A.val) = 0} :=
    Equiv.subtypeEquiv (Equiv.refl _) (by
      intro B
      change A.val ⊓ B.val = ⊥ ↔ finrank K ↥(B.val ⊓ A.val) = 0
      rw [Submodule.finrank_eq_zero,inf_comm])
  rw [Nat.card_congr he,h]
  simp only [Nat.sub_zero,hc,one_mul]
 theorem orderedTransversePair_card (h2 : (2 : K) ≠ 0) :
    Nat.card (OrderedTransversePair (canonicalSymplectic (K := K) (V := V))) = Nat.card (Lagrangian (K := K) (V := V)) *
      Fintype.card K^((finrank K V+1).choose 2) := by
  classical
  let : Finite (Module.Dual K V) := Module.finite_of_finite K
  let := Fintype.ofFinite (Lagrangian (K := K) (V := V))
  let e : OrderedTransversePair (canonicalSymplectic (K := K) (V := V)) ≃
      Σ A : Lagrangian (K := K) (V := V), {B : Lagrangian (K := K) (V := V) // A.val ⊓ B.val = ⊥} :=
    { toFun := fun p => ⟨p.val.1,⟨p.val.2,p.property⟩⟩
      invFun := fun p => ⟨(p.1,p.2.val),p.2.property⟩
      left_inv := fun p => rfl
      right_inv := fun p => rfl }
  rw [Nat.card_congr e,Nat.card_sigma]
  simp only [transverse_to_card h2,Finset.sum_const,Finset.card_univ,smul_eq_mul,
    Nat.card_eq_fintype_card]
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
 theorem symplecticLagrangian_card_bounds (h2 : (2 : K) ≠ 0)
    (ha : ω.IsAlt) (hω : ω.Nondegenerate) (D : ℕ) (hD : 2*D = finrank K E) :
    (Fintype.card K : ℝ)^((D+1).choose 2) ≤ Nat.card (SymplecticLagrangian ω) ∧
      (Nat.card (SymplecticLagrangian ω) : ℝ) ≤
        lagrangianConstant D * (Fintype.card K : ℝ)^((D+1).choose 2) := by
  obtain ⟨L,_,hL⟩ := exists_containing_lagrangian ω ha ⊥ bot_le
  have hd : finrank K L = D := by
    have h := self_orthogonal_twice_finrank ω L hω hL
    omega
  obtain ⟨e,_,he⟩ := exists_lagrangian_coordinates ω L h2 ha hω hL
  have hc := Nat.card_congr (symplecticLagrangianEquiv canonicalSymplectic ω e he)
  change Nat.card (Lagrangian (K := K) (V := L)) = _ at hc
  rw [←hc,←hd]
  exact ⟨lagrangian_card_lower,lagrangian_card_upper⟩
omit [Fintype K] in
 theorem symplecticLagrangian_card_pos (ha : ω.IsAlt) :
    0 < Nat.card (SymplecticLagrangian ω) := by
  obtain ⟨L,_,hL⟩ := exists_containing_lagrangian ω ha ⊥ bot_le
  let : Nonempty (SymplecticLagrangian ω) := ⟨⟨L,hL⟩⟩
  exact Nat.card_pos
omit [Fintype K] in
 theorem isotropic_finrank_le_half (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D = finrank K E) (S : Submodule K E)
    (hS : S ≤ ω.orthogonal S) : finrank K S ≤ D := by
  have h := ω.finrank_orthogonal hω S
  have hl := Submodule.finrank_mono hS
  omega
 theorem containingLagrangian_card_bounds (h2 : (2 : K) ≠ 0)
    (ha : ω.IsAlt) (hω : ω.Nondegenerate) (D : ℕ) (hD : 2*D = finrank K E)
    (S : Submodule K E) (hS : S ≤ ω.orthogonal S) :
    (Fintype.card K : ℝ)^((D-finrank K S+1).choose 2) ≤
        Nat.card {L : SymplecticLagrangian ω // S ≤ L.val} ∧
      (Nat.card {L : SymplecticLagrangian ω // S ≤ L.val} : ℝ) ≤
        lagrangianConstant (D-finrank K S) *
          (Fintype.card K : ℝ)^((D-finrank K S+1).choose 2) := by
  let e : {L : SymplecticLagrangian ω // S ≤ L.val} ≃
      {L : Submodule K E // ω.orthogonal L = L ∧ S ≤ L} :=
    { toFun := fun L => ⟨L.val.val,L.val.property,L.property⟩
      invFun := fun L => ⟨⟨L.val,L.property.1⟩,L.property.2⟩
      left_inv := fun L => rfl
      right_inv := fun L => rfl }
  have he := Nat.card_congr (e.trans (containingLagrangianEquiv ω S ha hS))
  have hc := reducedSpace_finrank ω S hω hS
  have hs := isotropic_finrank_le_half ω hω D hD S hS
  let : Finite (ReducedSpace ω S) := Module.finite_of_finite K
  rw [he]
  exact symplecticLagrangian_card_bounds (symplecticReductionForm ω S ha) h2
    (symplecticReductionForm_alt ω S ha) (symplecticReductionForm_nondegenerate ω S ha hω)
    (D-finrank K S) (by omega)
abbrev IsotropicDimspace (c : ℕ) :=
  {S : Submodule K E // S ≤ ω.orthogonal S ∧ finrank K S = c}
noncomputable def isotropicIncidenceEquiv (c : ℕ) :
    (Σ S : IsotropicDimspace ω c, {L : SymplecticLagrangian ω // S.val ≤ L.val}) ≃
    (Σ L : SymplecticLagrangian ω, DimSubspace K L.val c) where
  toFun p := ⟨p.2.val,⟨p.1.val.comap p.2.val.val.subtype,
    (Submodule.comapSubtypeEquivOfLe p.2.property).finrank_eq.trans p.1.property.2⟩⟩
  invFun p := ⟨⟨p.2.val.map p.1.val.subtype,by
      constructor
      · intro x hx y hy
        exact p.1.property.ge (Submodule.map_subtype_le p.1.val _ hx) y
          (Submodule.map_subtype_le p.1.val _ hy)
      · exact (Submodule.equivMapOfInjective p.1.val.subtype p.1.val.injective_subtype p.2.val).finrank_eq.symm.trans p.2.property⟩,
    ⟨p.1,Submodule.map_subtype_le p.1.val _⟩⟩
  left_inv p := by
    have hS : (p.1.val.comap p.2.val.val.subtype).map p.2.val.val.subtype = p.1.val := by
      rw [Submodule.map_comap_subtype,inf_of_le_right p.2.property]
    refine Sigma.ext (Subtype.ext hS) ?_
    apply (Subtype.heq_iff_coe_eq (fun L => ?_)).mpr
    · rfl
    · change (p.1.val.comap p.2.val.val.subtype).map p.2.val.val.subtype ≤ L.val ↔ p.1.val ≤ L.val
      rw [hS]
  right_inv p := by
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      apply Subtype.ext
      exact Submodule.comap_map_eq_of_injective p.1.val.injective_subtype p.2.val
omit [Fintype K] [Finite E] in
 theorem isotropic_incidence_card (c : ℕ) :
    Nat.card (Σ S : IsotropicDimspace ω c, {L : SymplecticLagrangian ω // S.val ≤ L.val}) =
      Nat.card (Σ L : SymplecticLagrangian ω, DimSubspace K L.val c) :=
  Nat.card_congr (isotropicIncidenceEquiv ω c)
end GenericCounts
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
def isotropicExponent (D c : ℕ) : ℕ :=
  (D+1).choose 2 + c*(D-c) - (D-c+1).choose 2
 theorem isotropicExponent_add (D c : ℕ) (hc : c ≤ D) :
    isotropicExponent D c + (D-c+1).choose 2 = (D+1).choose 2 + c*(D-c) := by
  have h := symmetric_nullity_exponent D c hc
  exact Nat.sub_add_cancel (by omega)
section IsotropicCounts
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
  [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
 theorem isotropic_card_bounds (h2 : (2 : K) ≠ 0)
    (ha : ω.IsAlt) (hω : ω.Nondegenerate) (D : ℕ) (hD : 2*D = finrank K E)
    (c : ℕ) (hc : c ≤ D) :
    (Fintype.card K : ℝ)^(isotropicExponent D c) ≤
        lagrangianConstant (D-c) * Nat.card (IsotropicDimspace ω c) ∧
      (Nat.card (IsotropicDimspace ω c) : ℝ) ≤
        (lagrangianConstant D * 2^c) * (Fintype.card K : ℝ)^(isotropicExponent D c) := by
  classical
  let := Fintype.ofFinite (IsotropicDimspace ω c)
  let := Fintype.ofFinite (SymplecticLagrangian ω)
  let q : ℝ := Fintype.card K
  have hq : 0 < q := by
    dsimp [q]
    exact_mod_cast Fintype.card_pos (α := K)
  have hdim (L : SymplecticLagrangian ω) : finrank K L.val = D := by
    have h := self_orthogonal_twice_finrank ω L.val hω L.property
    omega
  have hs (S : IsotropicDimspace ω c) :=
    containingLagrangian_card_bounds ω h2 ha hω D hD S.val S.property.1
  have hs' (S : IsotropicDimspace ω c) :
      q^((D-c+1).choose 2) ≤ Nat.card {L : SymplecticLagrangian ω // S.val ≤ L.val} ∧
      (Nat.card {L : SymplecticLagrangian ω // S.val ≤ L.val} : ℝ) ≤
        lagrangianConstant (D-c)*q^((D-c+1).choose 2) := by
    simpa only [S.property.2] using hs S
  have hsum : (∑ S : IsotropicDimspace ω c,
      (Nat.card {L : SymplecticLagrangian ω // S.val ≤ L.val} : ℝ)) =
        ∑ L : SymplecticLagrangian ω, (Nat.card (DimSubspace K L.val c) : ℝ) := by
    have h := isotropic_incidence_card ω c
    rw [Nat.card_sigma,Nat.card_sigma] at h
    exact_mod_cast h
  have hgrass (L : SymplecticLagrangian ω) :
      q^(c*(D-c)) ≤ Nat.card (DimSubspace K L.val c) ∧
        (Nat.card (DimSubspace K L.val c) : ℝ) ≤ 2^c*q^(c*(D-c)) := by
    have hcL : c ≤ finrank K L.val := (hdim L).symm ▸ hc
    constructor
    · simpa only [hdim L] using subspace_count_lower (K := K) (V := L.val) c hcL
    · simpa only [hdim L] using subspace_count_upper (K := K) (V := L.val) c hcL
  have hu : (Nat.card (IsotropicDimspace ω c) : ℝ)*q^((D-c+1).choose 2) ≤
      (Nat.card (SymplecticLagrangian ω) : ℝ)*(2^c*q^(c*(D-c))) := by
    calc
      _ = ∑ _S : IsotropicDimspace ω c, q^((D-c+1).choose 2) := by
        simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card]
      _ ≤ ∑ S : IsotropicDimspace ω c,
          (Nat.card {L : SymplecticLagrangian ω // S.val ≤ L.val} : ℝ) :=
        Finset.sum_le_sum (fun S _ => (hs' S).1)
      _ = _ := hsum
      _ ≤ ∑ _L : SymplecticLagrangian ω, 2^c*q^(c*(D-c)) :=
        Finset.sum_le_sum (fun L _ => (hgrass L).2)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card]
  have hl : (Nat.card (SymplecticLagrangian ω) : ℝ)*q^(c*(D-c)) ≤
      (Nat.card (IsotropicDimspace ω c) : ℝ)*(lagrangianConstant (D-c)*q^((D-c+1).choose 2)) := by
    calc
      _ = ∑ _L : SymplecticLagrangian ω, q^(c*(D-c)) := by
        simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card]
      _ ≤ ∑ L : SymplecticLagrangian ω, (Nat.card (DimSubspace K L.val c) : ℝ) :=
        Finset.sum_le_sum (fun L _ => (hgrass L).1)
      _ = _ := hsum.symm
      _ ≤ ∑ _S : IsotropicDimspace ω c, lagrangianConstant (D-c)*q^((D-c+1).choose 2) :=
        Finset.sum_le_sum (fun S _ => (hs' S).2)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card]
  have hlag := symplecticLagrangian_card_bounds ω h2 ha hω D hD
  have he : q^(isotropicExponent D c)*q^((D-c+1).choose 2) =
      q^((D+1).choose 2)*q^(c*(D-c)) := by
    rw [←pow_add,isotropicExponent_add D c hc,pow_add]
  constructor
  · apply (mul_le_mul_iff_left₀ (pow_pos hq ((D-c+1).choose 2))).mp
    calc
      _ = q^((D+1).choose 2)*q^(c*(D-c)) := he
      _ ≤ (Nat.card (SymplecticLagrangian ω) : ℝ)*q^(c*(D-c)) :=
        mul_le_mul_of_nonneg_right hlag.1 (by positivity)
      _ ≤ _ := hl
      _ = _ := by ring
  · apply (mul_le_mul_iff_left₀ (pow_pos hq ((D-c+1).choose 2))).mp
    calc
      _ ≤ _ := hu
      _ ≤ (lagrangianConstant D*q^((D+1).choose 2))*(2^c*q^(c*(D-c))) :=
        mul_le_mul_of_nonneg_right hlag.2 (by positivity)
      _ = (lagrangianConstant D*2^c)*(q^((D+1).choose 2)*q^(c*(D-c))) := by ring
      _ = _ := by rw [←he]; ring
end IsotropicCounts
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
 theorem lagrangianConstant_mono : Monotone lagrangianConstant := by
  intro m n h
  unfold lagrangianConstant
  exact mul_le_mul (by exact_mod_cast Nat.add_le_add_right h 1)
    (pow_le_pow_right₀ (by norm_num) h) (by positivity) (by positivity)
section AvoidanceCounts
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
  [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
theorem lagrangian_bad_intersection_card (h2 : (2 : K) ≠ 0)
    (ha : ω.IsAlt) (hω : ω.Nondegenerate) (D : ℕ) (hD : 2*D = finrank K E)
    (S : Submodule K E) (hS : S ≤ ω.orthogonal S) (hpos : 0 < finrank K S) :
    (Nat.card {L : SymplecticLagrangian ω // ¬ Disjoint L.val S} : ℝ) ≤
      (2*(Fintype.card K : ℝ)^(finrank K S-1)) *
        (lagrangianConstant (D-1)*(Fintype.card K : ℝ)^((D-1+1).choose 2)) := by
  classical
  let Line := DimSubspace K S 1
  let B := {L : SymplecticLagrangian ω // ¬ Disjoint L.val S}
  let Inc := Σ ℓ : Line, {L : SymplecticLagrangian ω // ℓ.val.map S.subtype ≤ L.val}
  let := Fintype.ofFinite Line
  have hex (L : B) : ∃ ℓ : Line, ℓ.val.map S.subtype ≤ L.val.val := by
    have hne : L.val.val ⊓ S ≠ ⊥ := by simpa only [disjoint_iff] using L.property
    obtain ⟨x,hx,hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    let v : S := ⟨x,hx.2⟩
    have hv : v ≠ 0 := by intro h; exact hx0 (congrArg Subtype.val h)
    refine ⟨⟨K ∙ v, finrank_span_singleton hv⟩,?_⟩
    rintro y ⟨z,hz,rfl⟩
    obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hz
    exact L.val.val.smul_mem a hx.1
  let f : B → Inc := fun L => ⟨(hex L).choose,⟨L.val,(hex L).choose_spec⟩⟩
  have hfi : Function.Injective f := by
    intro L M h
    apply Subtype.ext
    exact congrArg (fun i : Inc => i.2.val) h
  have hi (ℓ : Line) : (Nat.card {L : SymplecticLagrangian ω //
      ℓ.val.map S.subtype ≤ L.val} : ℝ) ≤
      lagrangianConstant (D-1)*(Fintype.card K : ℝ)^((D-1+1).choose 2) := by
    have hle : ℓ.val.map S.subtype ≤ S := by rintro x ⟨y,_,rfl⟩; exact y.property
    have hiso : ℓ.val.map S.subtype ≤ ω.orthogonal (ℓ.val.map S.subtype) :=
      hle.trans (hS.trans (ω.orthogonal_le hle))
    have hd : finrank K (ℓ.val.map S.subtype) = 1 := by
      exact (Submodule.equivMapOfInjective S.subtype S.subtype_injective ℓ.val).finrank_eq.symm.trans ℓ.property
    simpa only [hd] using (containingLagrangian_card_bounds ω h2 ha hω D hD
      (ℓ.val.map S.subtype) hiso).2
  have hinc : (Nat.card Inc : ℝ) ≤ (Nat.card Line : ℝ)*
      (lagrangianConstant (D-1)*(Fintype.card K : ℝ)^((D-1+1).choose 2)) := by
    rw [Nat.card_sigma,Nat.cast_sum]
    calc
      _ ≤ ∑ _ℓ : Line, lagrangianConstant (D-1)*(Fintype.card K : ℝ)^((D-1+1).choose 2) :=
        Finset.sum_le_sum (fun ℓ _ => hi ℓ)
      _ = _ := by simp [Nat.card_eq_fintype_card]
  have hl : (Nat.card Line : ℝ) ≤ 2*(Fintype.card K : ℝ)^(finrank K S-1) := by
    simpa [Line] using subspace_count_upper (K := K) (V := S) 1 hpos
  calc
    _ ≤ (Nat.card Inc : ℝ) := by exact_mod_cast Nat.card_le_card_of_injective f hfi
    _ ≤ _ := hinc
    _ ≤ _ := mul_le_mul_of_nonneg_right hl (by
      exact mul_nonneg (lagrangianConstant_pos _).le (by positivity))
theorem lagrangian_bad_intersection_scaled (h2 : (2 : K) ≠ 0)
    (ha : ω.IsAlt) (hω : ω.Nondegenerate) (D : ℕ) (hD : 2*D = finrank K E)
    (S : Submodule K E) (hS : S ≤ ω.orthogonal S) :
    (Nat.card {L : SymplecticLagrangian ω // ¬ Disjoint L.val S} : ℝ) *
      Fintype.card K ≤ 2*lagrangianConstant D*Nat.card (SymplecticLagrangian ω) := by
  classical
  let q : ℝ := Fintype.card K
  have hq : 1 ≤ q := by dsimp [q]; exact_mod_cast Fintype.card_pos (α := K)
  by_cases hp : 0 < finrank K S
  · have hs := isotropic_finrank_le_half ω hω D hD S hS
    have hDpos : 0 < D := lt_of_lt_of_le hp hs
    have he : (D-1+1).choose 2 + D = (D+1).choose 2 := by
      rw [Nat.sub_add_cancel hDpos, Nat.choose_succ_succ,Nat.choose_one_right]
      change D.choose 2 + D = D + D.choose 2
      omega
    have hpow : q^((finrank K S-1)+(D-1+1).choose 2+1) ≤ q^((D+1).choose 2) := by
      apply pow_le_pow_right₀ hq
      omega
    have hc : lagrangianConstant (D-1) ≤ lagrangianConstant D := lagrangianConstant_mono (Nat.sub_le _ _)
    calc
      _ ≤ (2*q^(finrank K S-1))*(lagrangianConstant (D-1)*q^((D-1+1).choose 2))*q :=
        mul_le_mul_of_nonneg_right (lagrangian_bad_intersection_card ω h2 ha hω D hD S hS hp) (by positivity)
      _ = 2*lagrangianConstant (D-1)*q^((finrank K S-1)+(D-1+1).choose 2+1) := by
        simp only [pow_add,pow_one]; ring
      _ ≤ 2*lagrangianConstant D*q^((D+1).choose 2) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hc (by norm_num)) hpow
          (by positivity) (by exact mul_nonneg (by norm_num) (lagrangianConstant_pos D).le)
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (symplecticLagrangian_card_bounds ω h2 ha hω D hD).1
        (mul_nonneg (by norm_num) (lagrangianConstant_pos D).le)
  · have hfin : finrank K S = 0 := by omega
    have hbot : S = ⊥ := Submodule.finrank_eq_zero.mp hfin
    have he : IsEmpty {L : SymplecticLagrangian ω // ¬ Disjoint L.val S} := by
      rw [hbot]
      exact ⟨fun L => L.property disjoint_bot_right⟩
    have := he
    simp only [Nat.card_of_isEmpty,Nat.cast_zero,zero_mul]
    exact mul_nonneg (mul_nonneg (by norm_num) (lagrangianConstant_pos D).le) (by positivity)
theorem lagrangian_disjoint_card_lower (h2 : (2 : K) ≠ 0)
    (ha : ω.IsAlt) (hω : ω.Nondegenerate) (D : ℕ) (hD : 2*D = finrank K E)
    (S : Submodule K E) (hS : S ≤ ω.orthogonal S)
    (hq : 4*lagrangianConstant D ≤ (Fintype.card K : ℝ)) :
    (Nat.card (SymplecticLagrangian ω) : ℝ) ≤
      2*Nat.card {L : SymplecticLagrangian ω // Disjoint L.val S} := by
  classical
  let := Fintype.ofFinite (SymplecticLagrangian ω)
  have hsum : Nat.card {L : SymplecticLagrangian ω // Disjoint L.val S} +
      Nat.card {L : SymplecticLagrangian ω // ¬ Disjoint L.val S} =
        Nat.card (SymplecticLagrangian ω) := by
    simp only [Nat.card_eq_fintype_card,Fintype.card_subtype_compl]
    exact Nat.add_sub_of_le (Fintype.card_subtype_le _)
  have hsumR := congrArg (fun n : ℕ => (n : ℝ)) hsum
  push_cast at hsumR
  have hbad := lagrangian_bad_intersection_scaled ω h2 ha hω D hD S hS
  have hC := lagrangianConstant_pos D
  have hbad0 : (0 : ℝ) ≤ Nat.card {L : SymplecticLagrangian ω // ¬ Disjoint L.val S} := by positivity
  nlinarith
end AvoidanceCounts
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ContainmentAvoidance
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E)
 theorem reduceSubspace_isotropic (ha : ω.IsAlt) (A S : Submodule K E)
    (hS : S ≤ ω.orthogonal S) :
    reduceSubspace ω A S ≤ (symplecticReductionForm ω A ha).orthogonal (reduceSubspace ω A S) := by
  rintro x ⟨x,hx,rfl⟩ y ⟨y,hy,rfl⟩
  exact hS hx y.val hy
noncomputable def containmentAvoidanceEquiv (ha : ω.IsAlt)
    (A S : Submodule K E) (hAS : A ≤ S) (hS : S ≤ ω.orthogonal S) :
    AvoidanceSpace ω S A ≃
      {L : SymplecticLagrangian (symplecticReductionForm ω A ha) //
        Disjoint L.val (reduceSubspace ω A S)} := by
  have hAP : A ≤ ω.orthogonal A := hAS.trans (hS.trans (ω.orthogonal_le hAS))
  have hSP : S ≤ ω.orthogonal A := hS.trans (ω.orthogonal_le hAS)
  let e := containingLagrangianEquiv ω A ha hAP
  let f : AvoidanceSpace ω S A →
      {L : SymplecticLagrangian (symplecticReductionForm ω A ha) //
        Disjoint L.val (reduceSubspace ω A S)} := fun L => by
    have hAL : A ≤ L.val := L.property.2.ge.trans inf_le_left
    refine ⟨e ⟨L.val,L.property.1,hAL⟩,?_⟩
    apply disjoint_iff.mpr
    change reduceSubspace ω A L.val ⊓ reduceSubspace ω A S = ⊥
    rw [← reduceSubspace_inf ω A L.val S hAL,L.property.2,reduceSubspace_self]
  have hfi : Function.Injective f := by
    intro L M hh
    apply Subtype.ext
    have he := e.injective (congrArg Subtype.val hh)
    exact congrArg (fun X : {T : Submodule K E // ω.orthogonal T = T ∧ A ≤ T} => X.val) he
  have hfs : Function.Surjective f := by
    intro L
    let T := e.symm L.val
    have hlast : T.val ⊓ S = A := by
      calc
        T.val ⊓ S = liftReduction ω A L.val.val ⊓ liftReduction ω A (reduceSubspace ω A S) := by
          rw [lift_reduce ω A S hAS hSP]
          rfl
        _ = liftReduction ω A (L.val.val ⊓ reduceSubspace ω A S) :=
          (liftReduction_inf ω A _ _).symm
        _ = A := by rw [L.property.eq_bot,liftReduction_bot ω A hAP]
    refine ⟨⟨T.val,T.property.1,hlast⟩,?_⟩
    apply Subtype.ext
    exact e.apply_symm_apply L.val
  exact Equiv.ofBijective f ⟨hfi,hfs⟩
variable [Fintype K] [Finite E]
 theorem avoidance_card_lower (h2 : (2 : K) ≠ 0) (ha : ω.IsAlt)
    (hω : ω.Nondegenerate) (D : ℕ) (hD : 2*D = finrank K E)
    (A S : Submodule K E) (hAS : A ≤ S) (hS : S ≤ ω.orthogonal S)
    (hq : 4*lagrangianConstant D ≤ (Fintype.card K : ℝ)) :
    (Nat.card {L : SymplecticLagrangian ω // A ≤ L.val} : ℝ) ≤
      2*Nat.card (AvoidanceSpace ω S A) := by
  have hAP : A ≤ ω.orthogonal A := hAS.trans (hS.trans (ω.orthogonal_le hAS))
  have hdim := reducedSpace_finrank ω A hω hAP
  have hle := isotropic_finrank_le_half ω hω D hD A hAP
  let Ω := symplecticReductionForm ω A ha
  have hΩa : Ω.IsAlt := symplecticReductionForm_alt ω A ha
  have hΩ : Ω.Nondegenerate := symplecticReductionForm_nondegenerate ω A ha hω
  let : Finite (ReducedSpace ω A) := Module.finite_of_finite K
  have h := lagrangian_disjoint_card_lower Ω h2 hΩa hΩ (D-finrank K A) (by omega)
    (reduceSubspace ω A S) (reduceSubspace_isotropic ω ha A S hS)
    ((mul_le_mul_of_nonneg_left (lagrangianConstant_mono (Nat.sub_le D _)) (by norm_num)).trans hq)
  have he₁ := Nat.card_congr (containmentAvoidanceEquiv ω ha A S hAS hS)
  have e₂ : {L : SymplecticLagrangian ω // A ≤ L.val} ≃
      {L : Submodule K E // ω.orthogonal L = L ∧ A ≤ L} :=
    { toFun := fun L => ⟨L.val.val,L.val.property,L.property⟩
      invFun := fun L => ⟨⟨L.val,L.property.1⟩,L.property.2⟩
      left_inv := fun L => rfl
      right_inv := fun L => rfl }
  have he₂ := Nat.card_congr (e₂.trans (containingLagrangianEquiv ω A ha hAP))
  rwa [he₁,he₂]
end ContainmentAvoidance
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section CommonSpaceLift
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E) (S : Submodule K E)
theorem triple_containing_isometry_lift (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (_hS : S ≤ ω.orthogonal S) (L M N L' M' N' : Submodule K E)
    (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M) (hN : ω.orthogonal N = N)
    (hL' : ω.orthogonal L' = L') (hM' : ω.orthogonal M' = M') (hN' : ω.orthogonal N' = N')
    (hSL : S ≤ L) (hSM : S ≤ M) (hSN : S ≤ N)
    (hSL' : S ≤ L') (hSM' : S ≤ M') (hSN' : S ≤ N')
    (hres : TripleIsometry (symplecticReductionForm ω S ha) (symplecticReductionForm ω S ha)
      (reduceSubspace ω S L) (reduceSubspace ω S M) (reduceSubspace ω S N)
      (reduceSubspace ω S L') (reduceSubspace ω S M') (reduceSubspace ω S N')) :
    TripleIsometry ω ω L M N L' M' N' := by
  obtain ⟨f,hf,hfL,hfM,hfN⟩ := hres
  obtain ⟨e,he,heS,heP,heQ⟩ := exists_reduction_isometry_extension ω S ha hω f hf
  have hSe : S.map e.toLinearMap = S := subspace_map_eq_of_fixed e S heS
  have hPe : (ω.orthogonal S).map e.toLinearMap = ω.orthogonal S := by
    rw [←orthogonal_map_of_isometry ω e he,hSe]
  have hmap (U W : Submodule K E) (hU : ω.orthogonal U = U)
      (hW : ω.orthogonal W = W) (hSU : S ≤ U) (hSW : S ≤ W)
      (hfU : (reduceSubspace ω S U).map f.toLinearMap = reduceSubspace ω S W) :
      U.map e.toLinearMap = W := by
    have hSUe : S ≤ U.map e.toLinearMap := by
      rw [←hSe]
      exact Submodule.map_mono hSU
    have hUe : ω.orthogonal (U.map e.toLinearMap) = U.map e.toLinearMap := by
      rw [orthogonal_map_of_isometry ω e he,hU]
    calc
      U.map e.toLinearMap = liftReduction ω S (reduceSubspace ω S (U.map e.toLinearMap)) :=
        (lift_reduce ω S _ hSUe (lagrangian_le_orthogonal ω S _ hUe hSUe)).symm
      _ = liftReduction ω S (reduceSubspace ω S W) := by
        rw [reduceSubspace_map ω S e f hPe heQ,hfU]
      _ = W := lift_reduce ω S W hSW (lagrangian_le_orthogonal ω S W hW hSW)
  exact ⟨e,he,hmap L L' hL hL' hSL hSL' hfL,
    hmap M M' hM hM' hSM hSM' hfM,hmap N N' hN hN' hSN hSN' hfN⟩
end CommonSpaceLift
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section Decompositions
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
 theorem submodule_map_trans (U : Submodule K E) (e f : E ≃ₗ[K] E) :
    U.map (e.trans f).toLinearMap = (U.map e.toLinearMap).map f.toLinearMap := by
  exact Submodule.map_comp _ _ _
 theorem submodule_map_symm_cancel (U : Submodule K E) (e : E ≃ₗ[K] E) :
    (U.map e.toLinearMap).map e.symm.toLinearMap = U := by
  rw [←Submodule.map_comp]
  simp
variable [Fintype K] [Finite E]
 theorem linearAut_card_upper : Nat.card (E ≃ₗ[K] E) ≤
    Fintype.card K ^ (finrank K E * finrank K E) := by
  rw [linearAut_card]
  calc
    _ ≤ ∏ _i : Fin (finrank K E), Fintype.card K ^ finrank K E :=
      Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun i _ => Nat.sub_le _ _)
    _ = _ := by simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,←pow_mul]
end Decompositions
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section TripleDecompositions
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
noncomputable def tripleSumEquiv (U V W : Submodule K E)
    (hU : IsCompl U (V ⊔ W)) (hVW : Disjoint V W) : (U × (V × W)) ≃ₗ[K] E := by
  let f := V.subtype.coprod W.subtype
  have hr : LinearMap.range f = V ⊔ W := by
    rw [LinearMap.range_coprod,Submodule.range_subtype,Submodule.range_subtype]
  have hk : LinearMap.ker f = ⊥ := by
    rw [LinearMap.ker_coprod_of_disjoint_range,Submodule.ker_subtype,Submodule.ker_subtype,Submodule.prod_bot]
    simpa only [Submodule.range_subtype] using hVW
  apply LinearEquiv.ofBijective (U.subtype.coprod f)
  constructor
  · rw [←LinearMap.ker_eq_bot,LinearMap.ker_coprod_of_disjoint_range,
      Submodule.ker_subtype,hk,Submodule.prod_bot]
    simpa only [Submodule.range_subtype,hr] using hU.disjoint
  · rw [←LinearMap.range_eq_top,LinearMap.range_coprod,Submodule.range_subtype,hr,hU.sup_eq_top]
@[simp] theorem tripleSumEquiv_apply (U V W : Submodule K E)
    (hU : IsCompl U (V ⊔ W)) (hVW : Disjoint V W) (u : U) (v : V) (w : W) :
    tripleSumEquiv U V W hU hVW (u,(v,w)) = u.val+(v.val+w.val) := rfl
abbrev TripleLinearOrbit (U V W : Submodule K E) :=
  {p : Submodule K E × Submodule K E × Submodule K E // ∃ e : E ≃ₗ[K] E,
    U.map e.toLinearMap = p.1 ∧ V.map e.toLinearMap = p.2.1 ∧ W.map e.toLinearMap = p.2.2}
abbrev TripleLinearStabilizer (U V W : Submodule K E) :=
  {e : E ≃ₗ[K] E // U.map e.toLinearMap = U ∧ V.map e.toLinearMap = V ∧ W.map e.toLinearMap = W}
def tripleLinearOrbitMap (U V W : Submodule K E) (e : E ≃ₗ[K] E) : TripleLinearOrbit U V W :=
  ⟨(U.map e.toLinearMap,V.map e.toLinearMap,W.map e.toLinearMap),e,rfl,rfl,rfl⟩
noncomputable def tripleLinearOrbitFiberEquiv (U V W : Submodule K E) (p : TripleLinearOrbit U V W) :
    {e : E ≃ₗ[K] E // tripleLinearOrbitMap U V W e = p} ≃ TripleLinearStabilizer U V W := by
  classical
  let e₀ := p.property.choose
  have hU := p.property.choose_spec.1
  have hV := p.property.choose_spec.2.1
  have hW := p.property.choose_spec.2.2
  have hm (e : {e : E ≃ₗ[K] E // tripleLinearOrbitMap U V W e = p}) :
      U.map e.val.toLinearMap = p.val.1 ∧ V.map e.val.toLinearMap = p.val.2.1 ∧
        W.map e.val.toLinearMap = p.val.2.2 := by
    exact ⟨congrArg (fun a : TripleLinearOrbit U V W => a.val.1) e.property,
      congrArg (fun a : TripleLinearOrbit U V W => a.val.2.1) e.property,
      congrArg (fun a : TripleLinearOrbit U V W => a.val.2.2) e.property⟩
  refine
    { toFun := fun e => ⟨e.val.trans e₀.symm,?_,?_,?_⟩
      invFun := fun e => ⟨e.val.trans e₀,?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · rw [submodule_map_trans,(hm _).1,←hU,submodule_map_symm_cancel]
  · rw [submodule_map_trans,(hm _).2.1,←hV,submodule_map_symm_cancel]
  · rw [submodule_map_trans,(hm _).2.2,←hW,submodule_map_symm_cancel]
  · apply Subtype.ext
    apply Prod.ext
    · change U.map (‹TripleLinearStabilizer U V W›.val.trans e₀).toLinearMap = p.val.1
      rw [submodule_map_trans]
      exact (congrArg (Submodule.map e₀.toLinearMap) ‹TripleLinearStabilizer U V W›.property.1).trans hU
    · apply Prod.ext
      · change V.map (‹TripleLinearStabilizer U V W›.val.trans e₀).toLinearMap = p.val.2.1
        rw [submodule_map_trans]
        exact (congrArg (Submodule.map e₀.toLinearMap) ‹TripleLinearStabilizer U V W›.property.2.1).trans hV
      · change W.map (‹TripleLinearStabilizer U V W›.val.trans e₀).toLinearMap = p.val.2.2
        rw [submodule_map_trans]
        exact (congrArg (Submodule.map e₀.toLinearMap) ‹TripleLinearStabilizer U V W›.property.2.2).trans hW
  · intro e
    apply Subtype.ext
    ext x
    simp
  · intro e
    apply Subtype.ext
    ext x
    simp
noncomputable def tripleLinearStabilizerRestriction (U V W : Submodule K E) :
    TripleLinearStabilizer U V W → (U ≃ₗ[K] U) × (V ≃ₗ[K] V) × (W ≃ₗ[K] W) := fun e =>
  (e.val.ofSubmodules U U e.property.1,e.val.ofSubmodules V V e.property.2.1,
    e.val.ofSubmodules W W e.property.2.2)
 theorem map_eq_of_restriction_aut (U : Submodule K E) (e : E ≃ₗ[K] E) (g : U ≃ₗ[K] U)
    (h : ∀ u : U, e u.val = (g u).val) : U.map e.toLinearMap = U := by
  ext x
  constructor
  · rintro ⟨u,hu,rfl⟩
    change e u ∈ U
    rw [h ⟨u,hu⟩]
    exact (g ⟨u,hu⟩).property
  · intro hx
    refine ⟨(g.symm ⟨x,hx⟩).val,(g.symm ⟨x,hx⟩).property,?_⟩
    exact (h _).trans (congrArg Subtype.val (g.apply_symm_apply ⟨x,hx⟩))
 theorem tripleLinearStabilizerRestriction_bijective (U V W : Submodule K E)
    (hU : IsCompl U (V ⊔ W)) (hVW : Disjoint V W) :
    Function.Bijective (tripleLinearStabilizerRestriction U V W) := by
  let c := tripleSumEquiv U V W hU hVW
  constructor
  · intro e f hh
    apply Subtype.ext
    ext x
    obtain ⟨⟨u,v,w⟩,rfl⟩ := c.surjective x
    have h₁ := congrArg (fun p : (U ≃ₗ[K] U) × (V ≃ₗ[K] V) × (W ≃ₗ[K] W) => (p.1 u).val) hh
    have h₂ := congrArg (fun p : (U ≃ₗ[K] U) × (V ≃ₗ[K] V) × (W ≃ₗ[K] W) => (p.2.1 v).val) hh
    have h₃ := congrArg (fun p : (U ≃ₗ[K] U) × (V ≃ₗ[K] V) × (W ≃ₗ[K] W) => (p.2.2 w).val) hh
    change e.val u.val = f.val u.val at h₁
    change e.val v.val = f.val v.val at h₂
    change e.val w.val = f.val w.val at h₃
    change e.val (u.val+(v.val+w.val)) = f.val (u.val+(v.val+w.val))
    simp only [map_add,h₁,h₂,h₃]
  · intro g
    let e : E ≃ₗ[K] E := c.symm.trans ((g.1.prodCongr (g.2.1.prodCongr g.2.2)).trans c)
    have heU (u : U) : e u.val = (g.1 u).val := by
      have hc : c (u,(0,0)) = u.val := by simp [c]
      change c ((g.1.prodCongr (g.2.1.prodCongr g.2.2)) (c.symm u.val)) = _
      rw [←hc,c.symm_apply_apply]
      simp [c]
    have heV (v : V) : e v.val = (g.2.1 v).val := by
      have hc : c (0,(v,0)) = v.val := by simp [c]
      change c ((g.1.prodCongr (g.2.1.prodCongr g.2.2)) (c.symm v.val)) = _
      rw [←hc,c.symm_apply_apply]
      simp [c]
    have heW (w : W) : e w.val = (g.2.2 w).val := by
      have hc : c (0,(0,w)) = w.val := by simp [c]
      change c ((g.1.prodCongr (g.2.1.prodCongr g.2.2)) (c.symm w.val)) = _
      rw [←hc,c.symm_apply_apply]
      simp [c]
    refine ⟨⟨e,map_eq_of_restriction_aut U e g.1 heU,
      map_eq_of_restriction_aut V e g.2.1 heV,map_eq_of_restriction_aut W e g.2.2 heW⟩,?_⟩
    apply Prod.ext
    · ext u
      exact heU u
    · apply Prod.ext
      · ext v
        exact heV v
      · ext w
        exact heW w
variable [Finite E]
 theorem tripleLinearOrbit_card_identity (U V W : Submodule K E)
    (hU : IsCompl U (V ⊔ W)) (hVW : Disjoint V W) :
    Nat.card (TripleLinearOrbit U V W) *
      (Nat.card (U ≃ₗ[K] U)*(Nat.card (V ≃ₗ[K] V)*Nat.card (W ≃ₗ[K] W))) = Nat.card (E ≃ₗ[K] E) := by
  classical
  let := Fintype.ofFinite (TripleLinearOrbit U V W)
  have hc : Nat.card (TripleLinearStabilizer U V W) =
      Nat.card (U ≃ₗ[K] U)*(Nat.card (V ≃ₗ[K] V)*Nat.card (W ≃ₗ[K] W)) := by
    rw [Nat.card_congr (Equiv.ofBijective _ (tripleLinearStabilizerRestriction_bijective U V W hU hVW)),
      Nat.card_prod,Nat.card_prod]
  have he := (Nat.card_congr (Equiv.sigmaFiberEquiv (tripleLinearOrbitMap U V W))).symm
  rw [Nat.card_sigma] at he
  have hf (p : TripleLinearOrbit U V W) : Nat.card {e : E ≃ₗ[K] E // tripleLinearOrbitMap U V W e = p} =
      Nat.card (U ≃ₗ[K] U)*(Nat.card (V ≃ₗ[K] V)*Nat.card (W ≃ₗ[K] W)) :=
    (Nat.card_congr (tripleLinearOrbitFiberEquiv U V W p)).trans hc
  simpa only [hf,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card,Nat.cast_id] using he.symm
variable [Fintype K]
 theorem tripleLinearOrbit_card_bounds (U V W : Submodule K E)
    (hU : IsCompl U (V ⊔ W)) (hVW : Disjoint V W) :
    (Fintype.card K : ℝ)^(2*(finrank K U*finrank K V+finrank K U*finrank K W+finrank K V*finrank K W)) ≤
      2^(finrank K E)*(Nat.card (TripleLinearOrbit U V W) : ℝ) ∧
    (Nat.card (TripleLinearOrbit U V W) : ℝ) ≤
      2^(finrank K E)*(Fintype.card K : ℝ)^(2*(finrank K U*finrank K V+finrank K U*finrank K W+finrank K V*finrank K W)) := by
  let u := finrank K U
  let v := finrank K V
  let w := finrank K W
  let n := finrank K E
  let q : ℝ := Fintype.card K
  have hn : u+(v+w) = n := by
    simpa only [Module.finrank_prod] using (tripleSumEquiv U V W hU hVW).finrank_eq
  have he : n*n = 2*(u*v+u*w+v*w) + (u*u+(v*v+w*w)) := by rw [←hn]; ring
  have hq : 0 < q := by dsimp [q]; exact_mod_cast Fintype.card_pos (α := K)
  have hi : (Nat.card (TripleLinearOrbit U V W) : ℝ)*
      ((Nat.card (U ≃ₗ[K] U) : ℝ)*(Nat.card (V ≃ₗ[K] V)*Nat.card (W ≃ₗ[K] W))) = Nat.card (E ≃ₗ[K] E) := by
    exact_mod_cast tripleLinearOrbit_card_identity U V W hU hVW
  have hu : (Nat.card (U ≃ₗ[K] U) : ℝ) ≤ q^(u*u) := by dsimp [q,u]; exact_mod_cast linearAut_card_upper (K := K) (E := U)
  have hv : (Nat.card (V ≃ₗ[K] V) : ℝ) ≤ q^(v*v) := by dsimp [q,v]; exact_mod_cast linearAut_card_upper (K := K) (E := V)
  have hw : (Nat.card (W ≃ₗ[K] W) : ℝ) ≤ q^(w*w) := by dsimp [q,w]; exact_mod_cast linearAut_card_upper (K := K) (E := W)
  have hl : q^(n*n) ≤ 2^n*(Nat.card (E ≃ₗ[K] E) : ℝ) := by dsimp [q,n]; exact_mod_cast linearAut_card_lower (K := K) (E := E)
  have hu' : q^(u*u) ≤ 2^u*(Nat.card (U ≃ₗ[K] U) : ℝ) := by dsimp [q,u]; exact_mod_cast linearAut_card_lower (K := K) (E := U)
  have hv' : q^(v*v) ≤ 2^v*(Nat.card (V ≃ₗ[K] V) : ℝ) := by dsimp [q,v]; exact_mod_cast linearAut_card_lower (K := K) (E := V)
  have hw' : q^(w*w) ≤ 2^w*(Nat.card (W ≃ₗ[K] W) : ℝ) := by dsimp [q,w]; exact_mod_cast linearAut_card_lower (K := K) (E := W)
  have hn' : (Nat.card (E ≃ₗ[K] E) : ℝ) ≤ q^(n*n) := by dsimp [q,n]; exact_mod_cast linearAut_card_upper (K := K) (E := E)
  constructor
  · apply (mul_le_mul_iff_left₀ (pow_pos hq (u*u+(v*v+w*w)))).mp
    calc
      _ = q^(n*n) := by rw [←pow_add,←he]
      _ ≤ _ := hl
      _ = 2^n*((Nat.card (TripleLinearOrbit U V W) : ℝ)*
          ((Nat.card (U ≃ₗ[K] U) : ℝ)*(Nat.card (V ≃ₗ[K] V)*Nat.card (W ≃ₗ[K] W)))) := by rw [hi]
      _ ≤ 2^n*((Nat.card (TripleLinearOrbit U V W) : ℝ)*(q^(u*u)*(q^(v*v)*q^(w*w)))) := by gcongr
      _ = _ := by simp only [pow_add]; ring
  · apply (mul_le_mul_iff_left₀ (pow_pos hq (u*u+(v*v+w*w)))).mp
    calc
      _ = (Nat.card (TripleLinearOrbit U V W) : ℝ)*(q^(u*u)*(q^(v*v)*q^(w*w))) := by simp only [pow_add]
      _ ≤ (Nat.card (TripleLinearOrbit U V W) : ℝ)*((2^u*Nat.card (U ≃ₗ[K] U))*((2^v*Nat.card (V ≃ₗ[K] V))*(2^w*Nat.card (W ≃ₗ[K] W)))) := by gcongr
      _ = 2^n*Nat.card (E ≃ₗ[K] E) := by rw [←hi,←hn]; simp only [pow_add]; ring
      _ ≤ 2^n*q^(n*n) := mul_le_mul_of_nonneg_left hn' (by positivity)
      _ = _ := by rw [he,pow_add]; ring
end TripleDecompositions
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section UniformCounts
variable {A B C D E F : Type*}
noncomputable def prodFiberEquiv (f : A → B) (g : C → D) (b : B) (d : D) :
    {x : A × C // (f x.1,g x.2) = (b,d)} ≃
      {a : A // f a = b} × {c : C // g c = d} where
  toFun x := (⟨x.val.1,congrArg Prod.fst x.property⟩,⟨x.val.2,congrArg Prod.snd x.property⟩)
  invFun x := ⟨(x.1.val,x.2.val),Prod.ext x.1.property x.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
 theorem uniform_prod_card [Finite A] [Finite B] [Finite C] [Finite D]
    (f : A → B) (g : C → D)
    (hf : ∀ b, Nat.card {a : A // f a = b} * Nat.card B = Nat.card A)
    (hg : ∀ d, Nat.card {c : C // g c = d} * Nat.card D = Nat.card C)
    (p : B × D) :
    Nat.card {x : A × C // (f x.1,g x.2) = p} * Nat.card (B × D) = Nat.card (A × C) := by
  rcases p with ⟨b,d⟩
  rw [Nat.card_congr (prodFiberEquiv f g b d),Nat.card_prod,Nat.card_prod,Nat.card_prod]
  calc
    _ = (Nat.card {a : A // f a = b} * Nat.card B) *
      (Nat.card {c : C // g c = d} * Nat.card D) := by ring
    _ = _ := by rw [hf,hg]
 theorem uniform_preimage_card [Finite A] [Finite B] (f : A → B)
    (hf : ∀ b, Nat.card {a : A // f a = b} * Nat.card B = Nat.card A) (P : B → Prop) :
    Nat.card {a : A // P (f a)} * Nat.card B = Nat.card {b : B // P b} * Nat.card A := by
  classical
  let := Fintype.ofFinite {b : B // P b}
  let e : {a : A // P (f a)} ≃ Σ b : {b : B // P b}, {a : A // f a = b.val} :=
    { toFun := fun a => ⟨⟨f a.val,a.property⟩,⟨a.val,rfl⟩⟩
      invFun := fun b => ⟨b.2.val,by rw [b.2.property]; exact b.1.property⟩
      left_inv := fun a => rfl
      right_inv := by rintro ⟨⟨b,hb⟩,a,ha⟩; dsimp at ha; subst b; rfl }
  rw [Nat.card_congr e,Nat.card_sigma,Finset.sum_mul]
  simp only [hf,Finset.sum_const,Finset.card_univ,smul_eq_mul,Nat.card_eq_fintype_card]
end UniformCounts
section ExactPairs
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E) (S L M A B : Submodule K E)
 theorem avoidance_exact_intersection
    (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M)
    (hLA : L ⊓ S = A) (hMB : M ⊓ S = B) (hAB : A ⊔ B = S)
    (hr : reduceSubspace ω S L ⊓ reduceSubspace ω S M = ⊥) :
    L ⊓ M = A ⊓ B := by
  apply le_antisymm
  · intro x hx
    have hxP : x ∈ ω.orthogonal S := by
      intro y hy
      rw [←hAB] at hy
      obtain ⟨a,ha,b,hb,rfl⟩ := Submodule.mem_sup.mp hy
      have haL : a ∈ L := (hLA.symm ▸ ha : a ∈ L ⊓ S).1
      have hbM : b ∈ M := (hMB.symm ▸ hb : b ∈ M ⊓ S).1
      rw [map_add,LinearMap.add_apply,(hL.ge hx.1) a haL,(hM.ge hx.2) b hbM,add_zero]
    have hxq : (reductionKernel ω S).mkQ ⟨x,hxP⟩ = 0 := by
      have hmem : (reductionKernel ω S).mkQ ⟨x,hxP⟩ ∈
          reduceSubspace ω S L ⊓ reduceSubspace ω S M :=
        ⟨⟨⟨x,hxP⟩,hx.1,rfl⟩,⟨⟨x,hxP⟩,hx.2,rfl⟩⟩
      simpa only [hr,Submodule.mem_bot] using hmem
    have hxS : x ∈ S := (Submodule.Quotient.mk_eq_zero (reductionKernel ω S)).mp hxq
    exact ⟨hLA ▸ (⟨hx.1,hxS⟩ : x ∈ L ⊓ S),hMB ▸ (⟨hx.2,hxS⟩ : x ∈ M ⊓ S)⟩
  · intro x hx
    exact ⟨(hLA.symm ▸ hx.1 : x ∈ L ⊓ S).1,(hMB.symm ▸ hx.2 : x ∈ M ⊓ S).1⟩
end ExactPairs
end SidorenkoCounterexample
end OAI
namespace OAI
namespace SidorenkoCounterexample
open Module
section PairSpaceFacts
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
 theorem triple_pairs_disjoint (L M N : Submodule K E) (h0 : (L ⊓ M) ⊓ N = ⊥) :
    Disjoint (L ⊓ M) ((L ⊓ N) ⊔ (M ⊓ N)) ∧ Disjoint (L ⊓ N) (M ⊓ N) := by
  constructor
  · apply disjoint_iff.mpr
    apply le_antisymm _ bot_le
    intro x hx
    exact h0.le ⟨hx.1,(show (L ⊓ N) ⊔ (M ⊓ N) ≤ N from sup_le inf_le_right inf_le_right) hx.2⟩
  · apply disjoint_iff.mpr
    apply le_antisymm _ bot_le
    intro x hx
    exact h0.le ⟨⟨hx.1.1,hx.2.1⟩,hx.1.2⟩
 theorem triple_own_avoidance (L M N : Submodule K E) (h0 : (L ⊓ M) ⊓ N = ⊥) :
    L ⊓ triplePairSum L M N = (L ⊓ M) ⊔ (L ⊓ N) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨u,hu,v,hv,hxuv⟩ := Submodule.mem_sup.mp hx.2
    have huL : u ∈ L := (show (L ⊓ M) ⊔ (L ⊓ N) ≤ L from sup_le inf_le_left inf_le_left) hu
    have hvL : v ∈ L := by
      have hh := L.sub_mem hx.1 huL
      rw [←hxuv,add_sub_cancel_left] at hh
      exact hh
    have hz : v = 0 := by simpa only [Submodule.mem_bot] using h0.le ⟨⟨hvL,hv.1⟩,hv.2⟩
    have hxu : u = x := by simpa only [hz,add_zero] using hxuv
    exact hxu ▸ hu
  · exact le_inf (sup_le inf_le_left inf_le_left) le_sup_left
 theorem reduction_intersection_of_split_kernel (ω : LinearMap.BilinForm K E)
    (S L M : Submodule K E) (hS : S ≤ ω.orthogonal S) (hsplit : (L ⊓ S) ⊔ (M ⊓ S) = S) :
    reduceSubspace ω S L ⊓ reduceSubspace ω S M = reduceSubspace ω S (L ⊓ M) := by
  apply le_antisymm
  · rintro x ⟨⟨l,hl,hlx⟩,⟨m,hm,hmx⟩⟩
    have heq : (reductionKernel ω S).mkQ (l-m) = 0 := by rw [map_sub,hlx,hmx,sub_self]
    have hdiff : l.val-m.val ∈ (L ⊓ S) ⊔ (M ⊓ S) := by
      rw [hsplit]
      exact (Submodule.Quotient.mk_eq_zero (reductionKernel ω S)).mp heq
    obtain ⟨a,ha,b,hb,hab⟩ := Submodule.mem_sup.mp hdiff
    have hla : l.val-a = m.val+b := by
      calc
        _ = (l.val-m.val)-a+m.val := by abel
        _ = (a+b)-a+m.val := by rw [hab]
        _ = _ := by abel
    have haP : a ∈ ω.orthogonal S := hS ha.2
    exact ⟨⟨l.val-a,(ω.orthogonal S).sub_mem l.property haP⟩,
      ⟨L.sub_mem hl ha.1,by change l.val-a ∈ M; rw [hla]; exact M.add_mem hm hb.1⟩,by
        change (reductionKernel ω S).mkQ (l-⟨a,haP⟩) = x
        have hz : (reductionKernel ω S).mkQ ⟨a,haP⟩ = 0 :=
          (Submodule.Quotient.mk_eq_zero (reductionKernel ω S)).mpr ha.2
        rw [map_sub,hz,sub_zero,hlx]⟩
  · rintro x ⟨y,hy,rfl⟩
    exact ⟨⟨y,hy.1,rfl⟩,⟨y,hy.2,rfl⟩⟩
end PairSpaceFacts
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section GenericTransverseMass
variable {K E F : Type*} [Field K]
  [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]
noncomputable def orderedTransversePairEquiv
    (ω : LinearMap.BilinForm K E) (η : LinearMap.BilinForm K F)
    (e : E ≃ₗ[K] F) (he : ∀ x y, η (e x) (e y) = ω x y) :
    OrderedTransversePair ω ≃ OrderedTransversePair η := by
  let c := symplecticLagrangianEquiv ω η e he
  refine (c.prodCongr c).subtypeEquiv ?_
  intro p
  change p.1.val ⊓ p.2.val = ⊥ ↔
    p.1.val.map e.toLinearMap ⊓ p.2.val.map e.toLinearMap = ⊥
  rw [←Submodule.map_inf e.toLinearMap e.injective,←Submodule.map_bot e.toLinearMap]
  exact (Submodule.map_injective_of_injective e.injective).eq_iff.symm
variable [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
 theorem symplectic_orderedTransversePair_card (h2 : (2 : K) ≠ 0)
    (ha : ω.IsAlt) (hω : ω.Nondegenerate) (D : ℕ) (hD : 2*D = finrank K E) :
    Nat.card (OrderedTransversePair ω) = Nat.card (SymplecticLagrangian ω) *
      Fintype.card K^((D+1).choose 2) := by
  obtain ⟨L,_,hL⟩ := exists_containing_lagrangian ω ha ⊥ bot_le
  have hd : finrank K L = D := by
    have h := self_orthogonal_twice_finrank ω L hω hL
    omega
  obtain ⟨e,_,he⟩ := exists_lagrangian_coordinates ω L h2 ha hω hL
  have hc := Nat.card_congr (symplecticLagrangianEquiv canonicalSymplectic ω e he)
  have hp := Nat.card_congr (orderedTransversePairEquiv canonicalSymplectic ω e he)
  rw [←hp,orderedTransversePair_card h2,hc,hd]
 theorem symplectic_transverseTriple_card_lower [Invertible (2 : K)]
    (ha : ω.IsAlt) (hω : ω.Nondegenerate) (D : ℕ) (hD : 2*D = finrank K E)
    (L M N : SymplecticLagrangian ω)
    (hLM : L.val ⊓ M.val = ⊥) (hLN : L.val ⊓ N.val = ⊥) (hMN : M.val ⊓ N.val = ⊥) :
    Nat.card (SymplecticLagrangian ω) * (Fintype.card K^((D+1).choose 2))^2 ≤
      4^D * Nat.card (OrderedTripleOrbit ω L.val M.val N.val) := by
  have hd : finrank K L.val = D := by
    have h := self_orthogonal_twice_finrank ω L.val hω L.property
    omega
  have hcard := fixedPairOrbit_card_lower ω L.val M.val N.val ha hω
    L.property M.property N.property hLM hLN hMN
  rw [hd] at hcard
  obtain ⟨f,hf⟩ := orderedTripleOrbit_pair_injection ω ha hω L.val M.val N.val
    L.property M.property hLM
  have hi := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod,symplectic_orderedTransversePair_card ω
    (isUnit_of_invertible (2 : K)).ne_zero ha hω D hD] at hi
  calc
    _ = (Nat.card (SymplecticLagrangian ω) * Fintype.card K^((D+1).choose 2)) *
        Fintype.card K^((D+1).choose 2) := by rw [pow_two]; ac_rfl
    _ ≤ (Nat.card (SymplecticLagrangian ω) * Fintype.card K^((D+1).choose 2)) *
        (4^D * Nat.card (FixedPairOrbit ω L.val M.val N.val)) := Nat.mul_le_mul_left _ hcard
    _ = 4^D * (Nat.card (SymplecticLagrangian ω) * Fintype.card K^((D+1).choose 2) *
        Nat.card (FixedPairOrbit ω L.val M.val N.val)) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ hi
 theorem symplectic_transverseTriple_probability_lower [Invertible (2 : K)]
    (ha : ω.IsAlt) (hω : ω.Nondegenerate) (D : ℕ) (hD : 2*D = finrank K E)
    (L M N : SymplecticLagrangian ω)
    (hLM : L.val ⊓ M.val = ⊥) (hLN : L.val ⊓ N.val = ⊥) (hMN : M.val ⊓ N.val = ⊥) :
    (Nat.card (SymplecticLagrangian ω) : ℝ)^3 ≤
      (4^D * lagrangianConstant D^2) * Nat.card (OrderedTripleOrbit ω L.val M.val N.val) := by
  have hb := (symplecticLagrangian_card_bounds ω (isUnit_of_invertible (2 : K)).ne_zero ha hω D hD).2
  have ho : (Nat.card (SymplecticLagrangian ω) : ℝ) *
      ((Fintype.card K : ℝ)^((D+1).choose 2))^2 ≤
      4^D * Nat.card (OrderedTripleOrbit ω L.val M.val N.val) := by
    exact_mod_cast symplectic_transverseTriple_card_lower ω ha hω D hD L M N hLM hLN hMN
  calc
    _ = (Nat.card (SymplecticLagrangian ω) : ℝ) * (Nat.card (SymplecticLagrangian ω) : ℝ)^2 := by ring
    _ ≤ (Nat.card (SymplecticLagrangian ω) : ℝ) *
      (lagrangianConstant D * (Fintype.card K : ℝ)^((D+1).choose 2))^2 := by gcongr
    _ = lagrangianConstant D^2 * ((Nat.card (SymplecticLagrangian ω) : ℝ) *
      ((Fintype.card K : ℝ)^((D+1).choose 2))^2) := by ring
    _ ≤ lagrangianConstant D^2 * (4^D * Nat.card (OrderedTripleOrbit ω L.val M.val N.val)) :=
      mul_le_mul_of_nonneg_left ho (sq_nonneg _)
    _ = _ := by ring
end GenericTransverseMass
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ResidualTransversality
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E)
 theorem reduceSubspace_eq_bot_of_le (S L : Submodule K E) (hLS : L ≤ S) :
    reduceSubspace ω S L = ⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  rintro x ⟨y,hy,rfl⟩
  exact (Submodule.Quotient.mk_eq_zero (reductionKernel ω S)).mpr (hLS hy)
 theorem triplePairSum_split (L M N : Submodule K E) :
    (L ⊓ triplePairSum L M N) ⊔ (M ⊓ triplePairSum L M N) = triplePairSum L M N := by
  apply le_antisymm (sup_le inf_le_right inf_le_right)
  unfold triplePairSum
  apply sup_le (sup_le _ _) _
  · exact (le_inf inf_le_left (le_sup_left.trans le_sup_left)).trans le_sup_left
  · exact (le_inf inf_le_left (le_sup_right.trans le_sup_left)).trans le_sup_left
  · exact (le_inf inf_le_left le_sup_right).trans le_sup_right
 theorem triplePairSum_reduce_pair (L M N : Submodule K E)
    (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M) (hN : ω.orthogonal N = N) :
    reduceSubspace ω (triplePairSum L M N) L ⊓
      reduceSubspace ω (triplePairSum L M N) M = ⊥ := by
  rw [reduction_intersection_of_split_kernel ω _ L M
    (triplePairSum_isotropic ω L M N hL hM hN) (triplePairSum_split L M N)]
  exact reduceSubspace_eq_bot_of_le ω _ _ (le_sup_left.trans le_sup_left)
 theorem triplePairSum_reductions_transverse (L M N : Submodule K E)
    (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M) (hN : ω.orthogonal N = N) :
    let S := triplePairSum L M N
    reduceSubspace ω S L ⊓ reduceSubspace ω S M = ⊥ ∧
    reduceSubspace ω S L ⊓ reduceSubspace ω S N = ⊥ ∧
    reduceSubspace ω S M ⊓ reduceSubspace ω S N = ⊥ := by
  dsimp only
  refine ⟨triplePairSum_reduce_pair ω L M N hL hM hN,?_,?_⟩
  · have hs : triplePairSum L N M = triplePairSum L M N := by
      unfold triplePairSum
      rw [inf_comm N M,sup_comm (L ⊓ N) (L ⊓ M)]
    have h := triplePairSum_reduce_pair ω L N M hL hN hM
    rw [hs] at h
    exact h
  · have hs : triplePairSum M N L = triplePairSum L M N := by
      unfold triplePairSum
      rw [inf_comm M L,inf_comm N L]
      ac_rfl
    have h := triplePairSum_reduce_pair ω M N L hM hN hL
    rw [hs] at h
    exact h
end ResidualTransversality
section LagrangianTripleOrbit
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E) (L M N : SymplecticLagrangian ω)
abbrev LagTripleOrbit := {p : SymplecticLagrangian ω × SymplecticLagrangian ω × SymplecticLagrangian ω //
  TripleIsometry ω ω L.val M.val N.val p.1.val p.2.1.val p.2.2.val}
 theorem orderedTripleOrbit_lagrangians (p : OrderedTripleOrbit ω L.val M.val N.val) :
    ω.orthogonal p.val.1 = p.val.1 ∧ ω.orthogonal p.val.2.1 = p.val.2.1 ∧
      ω.orthogonal p.val.2.2 = p.val.2.2 := by
  obtain ⟨e,he,hL,hM,hN⟩ := p.property
  rw [←hL,←hM,←hN,orthogonal_map_of_isometry ω e he,orthogonal_map_of_isometry ω e he,
    orthogonal_map_of_isometry ω e he,L.property,M.property,N.property]
  exact ⟨rfl,rfl,rfl⟩
noncomputable def lagTripleOrbitEquiv : LagTripleOrbit ω L M N ≃ OrderedTripleOrbit ω L.val M.val N.val where
  toFun p := ⟨(p.val.1.val,p.val.2.1.val,p.val.2.2.val),p.property⟩
  invFun p := ⟨(⟨p.val.1,(orderedTripleOrbit_lagrangians ω L M N p).1⟩,
    ⟨p.val.2.1,(orderedTripleOrbit_lagrangians ω L M N p).2.1⟩,
    ⟨p.val.2.2,(orderedTripleOrbit_lagrangians ω L M N p).2.2⟩),p.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
end LagrangianTripleOrbit
section AvoidanceTripleCount
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
  [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E) (S : Submodule K E)
variable (ha : ω.IsAlt) (hω : ω.Nondegenerate) (hS : S ≤ ω.orthogonal S)
noncomputable def avoidanceTripleReduction (A B C : Submodule K E) :
    (AvoidanceSpace ω S A × AvoidanceSpace ω S B × AvoidanceSpace ω S C) →
      SymplecticLagrangian (symplecticReductionForm ω S ha) ×
      SymplecticLagrangian (symplecticReductionForm ω S ha) ×
      SymplecticLagrangian (symplecticReductionForm ω S ha) := fun p =>
  (avoidanceReduction ω S ha hω hS A p.1,
    avoidanceReduction ω S ha hω hS B p.2.1,avoidanceReduction ω S ha hω hS C p.2.2)
 theorem avoidanceTripleReduction_uniform (h2 : (2 : K) ≠ 0)
    (A B C : Submodule K E) (hA : A ≤ S) (hB : B ≤ S) (hC : C ≤ S)
    (p : SymplecticLagrangian (symplecticReductionForm ω S ha) ×
      SymplecticLagrangian (symplecticReductionForm ω S ha) ×
      SymplecticLagrangian (symplecticReductionForm ω S ha)) :
    Nat.card {x // avoidanceTripleReduction ω S ha hω hS A B C x = p} *
      Nat.card (SymplecticLagrangian (symplecticReductionForm ω S ha) ×
        SymplecticLagrangian (symplecticReductionForm ω S ha) ×
        SymplecticLagrangian (symplecticReductionForm ω S ha)) =
      Nat.card (AvoidanceSpace ω S A × AvoidanceSpace ω S B × AvoidanceSpace ω S C) := by
  let : Finite (ReducedSpace ω S) := Module.finite_of_finite K
  exact uniform_prod_card _ _ (avoidanceReduction_uniform ω S h2 ha hω hS A hA)
    (uniform_prod_card _ _ (avoidanceReduction_uniform ω S h2 ha hω hS B hB)
      (avoidanceReduction_uniform ω S h2 ha hω hS C hC)) p
abbrev AvoidanceOrbitFiber (A B C : Submodule K E)
    (L M N : SymplecticLagrangian (symplecticReductionForm ω S ha)) :=
  {p : AvoidanceSpace ω S A × AvoidanceSpace ω S B × AvoidanceSpace ω S C //
    TripleIsometry (symplecticReductionForm ω S ha) (symplecticReductionForm ω S ha)
      L.val M.val N.val (reduceSubspace ω S p.1.val)
        (reduceSubspace ω S p.2.1.val) (reduceSubspace ω S p.2.2.val)}
include hω hS in
 theorem avoidanceOrbitFiber_card_identity (h2 : (2 : K) ≠ 0)
    (A B C : Submodule K E) (hA : A ≤ S) (hB : B ≤ S) (hC : C ≤ S)
    (L M N : SymplecticLagrangian (symplecticReductionForm ω S ha)) :
    Nat.card (AvoidanceOrbitFiber ω S ha A B C L M N) *
      Nat.card (SymplecticLagrangian (symplecticReductionForm ω S ha))^3 =
      Nat.card (OrderedTripleOrbit (symplecticReductionForm ω S ha) L.val M.val N.val) *
        (Nat.card (AvoidanceSpace ω S A) * (Nat.card (AvoidanceSpace ω S B) * Nat.card (AvoidanceSpace ω S C))) := by
  let : Finite (ReducedSpace ω S) := Module.finite_of_finite K
  have h := uniform_preimage_card (avoidanceTripleReduction ω S ha hω hS A B C)
    (avoidanceTripleReduction_uniform ω S ha hω hS h2 A B C hA hB hC)
    (fun p => TripleIsometry (symplecticReductionForm ω S ha) (symplecticReductionForm ω S ha)
      L.val M.val N.val p.1.val p.2.1.val p.2.2.val)
  change Nat.card (AvoidanceOrbitFiber ω S ha A B C L M N) * _ =
    Nat.card (LagTripleOrbit _ L M N) * _ at h
  rw [Nat.card_congr (lagTripleOrbitEquiv _ L M N)] at h
  simp only [Nat.card_prod] at h
  convert h using 1; ring
end AvoidanceTripleCount
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section AvoidanceTripleBound
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
  [Fintype K] [Finite E] [Invertible (2 : K)]
variable (ω : LinearMap.BilinForm K E) (S : Submodule K E)
 theorem avoidanceOrbitFiber_card_lower (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (hS : S ≤ ω.orthogonal S) (z : ℕ) (hz : 2*z = finrank K (ReducedSpace ω S))
    (A B C : Submodule K E) (hA : A ≤ S) (hB : B ≤ S) (hC : C ≤ S)
    (L M N : SymplecticLagrangian (symplecticReductionForm ω S ha))
    (hLM : L.val ⊓ M.val = ⊥) (hLN : L.val ⊓ N.val = ⊥) (hMN : M.val ⊓ N.val = ⊥) :
    (Nat.card (AvoidanceSpace ω S A) : ℝ) * (Nat.card (AvoidanceSpace ω S B) * Nat.card (AvoidanceSpace ω S C)) ≤
      (4^z * lagrangianConstant z^2) * Nat.card (AvoidanceOrbitFiber ω S ha A B C L M N) := by
  let : Finite (ReducedSpace ω S) := Module.finite_of_finite K
  let Ω := symplecticReductionForm ω S ha
  have hΩ := symplecticReductionForm_alt ω S ha
  have hp := symplecticLagrangian_card_pos Ω hΩ
  have hb := symplectic_transverseTriple_probability_lower Ω hΩ
    (symplecticReductionForm_nondegenerate ω S ha hω) z hz L M N hLM hLN hMN
  have hi : (Nat.card (AvoidanceOrbitFiber ω S ha A B C L M N) : ℝ) *
      (Nat.card (SymplecticLagrangian Ω) : ℝ)^3 =
      (Nat.card (OrderedTripleOrbit Ω L.val M.val N.val) : ℝ) *
        (Nat.card (AvoidanceSpace ω S A) * (Nat.card (AvoidanceSpace ω S B) * Nat.card (AvoidanceSpace ω S C))) := by
    exact_mod_cast avoidanceOrbitFiber_card_identity ω S ha hω hS
      (isUnit_of_invertible (2 : K)).ne_zero A B C hA hB hC L M N
  have hpos : 0 < (Nat.card (SymplecticLagrangian Ω) : ℝ)^3 := by exact pow_pos (by exact_mod_cast hp) _
  apply (mul_le_mul_iff_left₀ hpos).mp
  calc
    _ ≤ ((Nat.card (AvoidanceSpace ω S A) : ℝ) *
      (Nat.card (AvoidanceSpace ω S B) * Nat.card (AvoidanceSpace ω S C))) *
      ((4^z * lagrangianConstant z^2) * Nat.card (OrderedTripleOrbit Ω L.val M.val N.val)) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = (4^z * lagrangianConstant z^2) *
      ((Nat.card (OrderedTripleOrbit Ω L.val M.val N.val) : ℝ) *
        (Nat.card (AvoidanceSpace ω S A) * (Nat.card (AvoidanceSpace ω S B) * Nat.card (AvoidanceSpace ω S C)))) := by ring
    _ = _ := by rw [←hi]; ring
 theorem containmentOrbitFiber_card_lower (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (hS : S ≤ ω.orthogonal S) (D : ℕ) (hD : 2*D = finrank K E)
    (hq : 4 * lagrangianConstant D ≤ (Fintype.card K : ℝ))
    (A B C : Submodule K E) (hA : A ≤ S) (hB : B ≤ S) (hC : C ≤ S)
    (L M N : SymplecticLagrangian (symplecticReductionForm ω S ha))
    (hLM : L.val ⊓ M.val = ⊥) (hLN : L.val ⊓ N.val = ⊥) (hMN : M.val ⊓ N.val = ⊥) :
    (Nat.card {L : SymplecticLagrangian ω // A ≤ L.val} : ℝ) *
      (Nat.card {L : SymplecticLagrangian ω // B ≤ L.val} *
        Nat.card {L : SymplecticLagrangian ω // C ≤ L.val}) ≤
      (8 * (4^D * lagrangianConstant D^2)) * Nat.card (AvoidanceOrbitFiber ω S ha A B C L M N) := by
  have h2 := (isUnit_of_invertible (2 : K)).ne_zero
  have h₁ : (Nat.card {L : SymplecticLagrangian ω // A ≤ L.val} : ℝ) ≤
      2*Nat.card (AvoidanceSpace ω S A) := by
    exact_mod_cast avoidance_card_lower ω h2 ha hω D hD A S hA hS hq
  have h₂ : (Nat.card {L : SymplecticLagrangian ω // B ≤ L.val} : ℝ) ≤
      2*Nat.card (AvoidanceSpace ω S B) := by
    exact_mod_cast avoidance_card_lower ω h2 ha hω D hD B S hB hS hq
  have h₃ : (Nat.card {L : SymplecticLagrangian ω // C ≤ L.val} : ℝ) ≤
      2*Nat.card (AvoidanceSpace ω S C) := by
    exact_mod_cast avoidance_card_lower ω h2 ha hω D hD C S hC hS hq
  have hr := reducedSpace_finrank ω S hω hS
  have hs := isotropic_finrank_le_half ω hω D hD S hS
  have hb := avoidanceOrbitFiber_card_lower ω S ha hω hS (D-finrank K S) (by omega)
    A B C hA hB hC L M N hLM hLN hMN
  have hk : (4:ℝ)^(D-finrank K S) * lagrangianConstant (D-finrank K S)^2 ≤
      4^D * lagrangianConstant D^2 := by
    gcongr
    · norm_num
    · exact Nat.sub_le D _
    · exact le_of_lt (lagrangianConstant_pos _)
    · exact lagrangianConstant_mono (Nat.sub_le D _)
  calc
    _ ≤ ((2:ℝ)*Nat.card (AvoidanceSpace ω S A)) *
      ((2*Nat.card (AvoidanceSpace ω S B)) * (2*Nat.card (AvoidanceSpace ω S C))) := by gcongr
    _ = 8 * ((Nat.card (AvoidanceSpace ω S A) : ℝ) *
      (Nat.card (AvoidanceSpace ω S B) * Nat.card (AvoidanceSpace ω S C))) := by ring
    _ ≤ 8 * (((4:ℝ)^(D-finrank K S) * lagrangianConstant (D-finrank K S)^2) *
      Nat.card (AvoidanceOrbitFiber ω S ha A B C L M N)) := mul_le_mul_of_nonneg_left hb (by norm_num)
    _ ≤ 8 * ((4^D * lagrangianConstant D^2) *
      Nat.card (AvoidanceOrbitFiber ω S ha A B C L M N)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hk (by positivity)) (by norm_num)
    _ = _ := by ring
end AvoidanceTripleBound
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section IsotropicExtension
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E] [Finite E]
variable (ω : LinearMap.BilinForm K E)
 theorem exists_isotropic_isometry_extension (h2 : (2 : K) ≠ 0) (ha : ω.IsAlt)
    (hω : ω.Nondegenerate) (S T : Submodule K E)
    (hS : S ≤ ω.orthogonal S) (hT : T ≤ ω.orthogonal T) (g : S ≃ₗ[K] T) :
    ∃ e : E ≃ₗ[K] E, (∀ x y, ω (e x) (e y) = ω x y) ∧
      ∀ x : S, e x.val = (g x).val := by
  obtain ⟨L,hSL,hL⟩ := exists_containing_lagrangian ω ha S hS
  obtain ⟨M,hTM,hM⟩ := exists_containing_lagrangian ω ha T hT
  obtain ⟨eL,hEL,hωL⟩ := exists_lagrangian_coordinates ω L h2 ha hω hL
  obtain ⟨eM,hEM,hωM⟩ := exists_lagrangian_coordinates ω M h2 ha hω hM
  have hdim : finrank K L = finrank K M := by
    have h1 := self_orthogonal_twice_finrank ω L hω hL
    have h2 := self_orthogonal_twice_finrank ω M hω hM
    omega
  let U := S.comap L.subtype
  let W := T.comap M.subtype
  let g₀ : U ≃ₗ[K] W := (Submodule.comapSubtypeEquivOfLe hSL).trans
    (g.trans (Submodule.comapSubtypeEquivOfLe hTM).symm)
  obtain ⟨f,hf⟩ := exists_linearEquiv_extension U W hdim g₀
  let c : (L × Module.Dual K L) ≃ₗ[K] (M × Module.Dual K M) := f.prodCongr f.symm.dualMap
  have hc (x y : L × Module.Dual K L) :
      canonicalSymplectic (c x) (c y) = canonicalSymplectic x y := by
    simp [c,canonicalSymplectic_apply]
  let e := eL.symm.trans (c.trans eM)
  have he (l : L) : e l.val = (f l).val := by
    change eM (c (eL.symm l.val)) = (f l).val
    rw [←hEL l,eL.symm_apply_apply]
    simpa [c] using hEM (f l)
  refine ⟨e,?_,?_⟩
  · intro x y
    change ω (eM (c (eL.symm x))) (eM (c (eL.symm y))) = ω x y
    rw [hωM,hc,←hωL,eL.apply_symm_apply,eL.apply_symm_apply]
  · intro x
    let u : U := ⟨⟨x.val,hSL x.property⟩,x.property⟩
    change e u.val.val = (g x).val
    rw [he,hf u]
    rfl
end IsotropicExtension
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section FixedPairs
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E) (L M N : SymplecticLagrangian ω)
abbrev FixedPairTripleOrbit := {p : LagTripleOrbit ω L M N //
  p.val.1.val ⊓ p.val.2.1.val = L.val ⊓ M.val ∧
  p.val.1.val ⊓ p.val.2.2.val = L.val ⊓ N.val ∧
  p.val.2.1.val ⊓ p.val.2.2.val = M.val ⊓ N.val}
 theorem triplePair_inter_own (P Q R : Submodule K E) :
    (P ⊓ triplePairSum P Q R) ⊓ (Q ⊓ triplePairSum P Q R) = P ⊓ Q := by
  apply le_antisymm (inf_le_inf inf_le_left inf_le_left)
  intro x hx
  have hs : x ∈ triplePairSum P Q R :=
    (show P ⊓ Q ≤ triplePairSum P Q R from le_sup_left.trans le_sup_left) hx
  exact ⟨⟨hx.1,hs⟩,⟨hx.2,hs⟩⟩
 theorem triplePairSum_split_all (P Q R : Submodule K E) :
    let S := triplePairSum P Q R
    ((P ⊓ S) ⊔ (Q ⊓ S) = S) ∧ ((P ⊓ S) ⊔ (R ⊓ S) = S) ∧
      ((Q ⊓ S) ⊔ (R ⊓ S) = S) := by
  dsimp only
  have h₁ : triplePairSum P R Q = triplePairSum P Q R := by unfold triplePairSum; ac_rfl
  have h₂ : triplePairSum Q R P = triplePairSum P Q R := by unfold triplePairSum; ac_rfl
  exact ⟨triplePairSum_split P Q R,by simpa only [h₁] using triplePairSum_split P R Q,
    by simpa only [h₂] using triplePairSum_split Q R P⟩
 theorem triplePair_inter_all (P Q R : Submodule K E) :
    let S := triplePairSum P Q R
    ((P ⊓ S) ⊓ (Q ⊓ S) = P ⊓ Q) ∧ ((P ⊓ S) ⊓ (R ⊓ S) = P ⊓ R) ∧
      ((Q ⊓ S) ⊓ (R ⊓ S) = Q ⊓ R) := by
  dsimp only
  have h₁ : triplePairSum P R Q = triplePairSum P Q R := by unfold triplePairSum; ac_rfl
  have h₂ : triplePairSum Q R P = triplePairSum P Q R := by unfold triplePairSum; ac_rfl
  exact ⟨triplePair_inter_own P Q R,by simpa only [h₁] using triplePair_inter_own P R Q,
    by simpa only [h₂] using triplePair_inter_own Q R P⟩
variable [FiniteDimensional K E]
variable (ha : ω.IsAlt) (hω : ω.Nondegenerate)
noncomputable def tripleResidualLagrangian (P : SymplecticLagrangian ω) :
    SymplecticLagrangian (symplecticReductionForm ω (triplePairSum L.val M.val N.val) ha) :=
  ⟨reduceSubspace ω (triplePairSum L.val M.val N.val) P.val,
    general_lagrangian_reduction ω _ ha hω
      (triplePairSum_isotropic ω _ _ _ L.property M.property N.property) P.val P.property⟩
abbrev OwnAvoidanceOrbitFiber :=
  AvoidanceOrbitFiber ω (triplePairSum L.val M.val N.val) ha
    (L.val ⊓ triplePairSum L.val M.val N.val)
    (M.val ⊓ triplePairSum L.val M.val N.val)
    (N.val ⊓ triplePairSum L.val M.val N.val)
    (tripleResidualLagrangian ω L M N ha hω L)
    (tripleResidualLagrangian ω L M N ha hω M)
    (tripleResidualLagrangian ω L M N ha hω N)
 theorem ownAvoidanceOrbitFiber_pairs (p : OwnAvoidanceOrbitFiber ω L M N ha hω) :
    p.val.1.val ⊓ p.val.2.1.val = L.val ⊓ M.val ∧
    p.val.1.val ⊓ p.val.2.2.val = L.val ⊓ N.val ∧
    p.val.2.1.val ⊓ p.val.2.2.val = M.val ⊓ N.val := by
  let S := triplePairSum L.val M.val N.val
  have hs := triplePairSum_split_all L.val M.val N.val
  have hi := triplePair_inter_all L.val M.val N.val
  have ht := triplePairSum_reductions_transverse ω L.val M.val N.val L.property M.property N.property
  obtain ⟨e,he,h₁,h₂,h₃⟩ := p.property
  dsimp only [tripleResidualLagrangian] at h₁ h₂ h₃
  have hp₁ : reduceSubspace ω S p.val.1.val ⊓ reduceSubspace ω S p.val.2.1.val = ⊥ := by
    rw [←h₁,←h₂,←Submodule.map_inf e.toLinearMap e.injective,ht.1,Submodule.map_bot]
  have hp₂ : reduceSubspace ω S p.val.1.val ⊓ reduceSubspace ω S p.val.2.2.val = ⊥ := by
    rw [←h₁,←h₃,←Submodule.map_inf e.toLinearMap e.injective,ht.2.1,Submodule.map_bot]
  have hp₃ : reduceSubspace ω S p.val.2.1.val ⊓ reduceSubspace ω S p.val.2.2.val = ⊥ := by
    rw [←h₂,←h₃,←Submodule.map_inf e.toLinearMap e.injective,ht.2.2,Submodule.map_bot]
  refine ⟨?_,?_,?_⟩
  · exact (avoidance_exact_intersection ω S _ _ _ _ p.val.1.property.1 p.val.2.1.property.1
      p.val.1.property.2 p.val.2.1.property.2 hs.1 hp₁).trans hi.1
  · exact (avoidance_exact_intersection ω S _ _ _ _ p.val.1.property.1 p.val.2.2.property.1
      p.val.1.property.2 p.val.2.2.property.2 hs.2.1 hp₂).trans hi.2.1
  · exact (avoidance_exact_intersection ω S _ _ _ _ p.val.2.1.property.1 p.val.2.2.property.1
      p.val.2.1.property.2 p.val.2.2.property.2 hs.2.2 hp₃).trans hi.2.2
noncomputable def ownAvoidanceOrbitFiberEmbedding (h0 : (L.val ⊓ M.val) ⊓ N.val = ⊥) :
    OwnAvoidanceOrbitFiber ω L M N ha hω ↪ FixedPairTripleOrbit ω L M N where
  toFun p := by
    have hp := ownAvoidanceOrbitFiber_pairs ω L M N ha hω p
    have hs : triplePairSum p.val.1.val p.val.2.1.val p.val.2.2.val =
        triplePairSum L.val M.val N.val := by unfold triplePairSum; rw [hp.1,hp.2.1,hp.2.2]
    have hp0 : (p.val.1.val ⊓ p.val.2.1.val) ⊓ p.val.2.2.val = ⊥ := by
      calc
        _ = (p.val.1.val ⊓ p.val.2.1.val) ⊓ (p.val.1.val ⊓ p.val.2.2.val) := by ac_rfl
        _ = (L.val ⊓ M.val) ⊓ (L.val ⊓ N.val) := by rw [hp.1,hp.2.1]
        _ = (L.val ⊓ M.val) ⊓ N.val := by ac_rfl
        _ = ⊥ := h0
    have hr : TripleResidualIsometry ω ω ha ha L.val M.val N.val p.val.1.val p.val.2.1.val p.val.2.2.val := by
      unfold TripleResidualIsometry
      rw [hs]
      exact p.property
    have ho := triple_common_zero_classification ω ω ha ha hω hω _ _ _ _ _ _
      L.property M.property N.property p.val.1.property.1 p.val.2.1.property.1 p.val.2.2.property.1
      h0 hp0 (by rw [hp.1]) (by rw [hp.2.1]) (by rw [hp.2.2]) hr
    exact ⟨⟨(⟨p.val.1.val,p.val.1.property.1⟩,⟨p.val.2.1.val,p.val.2.1.property.1⟩,
      ⟨p.val.2.2.val,p.val.2.2.property.1⟩),ho⟩,hp⟩
  inj' := by
    intro p q h
    apply Subtype.ext
    have hval := congrArg (fun x : FixedPairTripleOrbit ω L M N =>
      (x.val.val.1.val,x.val.val.2.1.val,x.val.val.2.2.val)) h
    exact Prod.ext (Subtype.ext (congrArg Prod.fst hval))
      (Prod.ext (Subtype.ext (congrArg (fun x => x.2.1) hval))
        (Subtype.ext (congrArg (fun x => x.2.2) hval)))
end FixedPairs
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ConfigurationOrbit
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E)
 theorem subspace_map_extension (S T U : Submodule K E) (hU : U ≤ S)
    (e : E ≃ₗ[K] E) (g : S ≃ₗ[K] T) (he : ∀ x : S, e x.val = (g x).val) :
    U.map e.toLinearMap = ((U.comap S.subtype).map g.toLinearMap).map T.subtype := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact ⟨g ⟨y,hU hy⟩,⟨⟨y,hU hy⟩,hy,rfl⟩,(he ⟨y,hU hy⟩).symm⟩
  · rintro ⟨y,⟨z,hz,rfl⟩,rfl⟩
    exact ⟨z.val,hz,he z⟩
 theorem subtype_map_comap_of_le (S U : Submodule K E) (hU : U ≤ S) :
    (U.comap S.subtype).map S.subtype = U := by
  ext x
  exact ⟨fun ⟨y,hy,hyx⟩ => hyx ▸ hy,fun hx => ⟨⟨x,hU hx⟩,hx,rfl⟩⟩
 theorem subspace_comap_sup_of_le (S U V : Submodule K E) (hU : U ≤ S) (hV : V ≤ S) :
    (U ⊔ V).comap S.subtype = U.comap S.subtype ⊔ V.comap S.subtype := by
  apply Submodule.map_injective_of_injective S.subtype_injective
  rw [Submodule.map_sup,subtype_map_comap_of_le S U hU,subtype_map_comap_of_le S V hV,
    subtype_map_comap_of_le S (U ⊔ V) (sup_le hU hV)]
variable [FiniteDimensional K E] [Finite E]
 theorem triple_subspace_orbit_injection (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (S U V W : Submodule K E) (hS : S ≤ ω.orthogonal S)
    (hU : U ≤ S) (hV : V ≤ S) (hW : W ≤ S) (hsum : U ⊔ V ⊔ W = S) :
    ∃ f : IsotropicDimspace ω (finrank K S) ×
      TripleLinearOrbit (U.comap S.subtype) (V.comap S.subtype) (W.comap S.subtype) →
        OrderedTripleOrbit ω U V W, Function.Injective f := by
  classical
  have ht (T : IsotropicDimspace ω (finrank K S)) := isotropic_transitivity ω h2 ha hω
    S T.val hS T.property.1 T.property.2.symm
  let e (T : IsotropicDimspace ω (finrank K S)) := (ht T).choose
  have he (T) := (ht T).choose_spec
  have hgood (T : IsotropicDimspace ω (finrank K S))
      (p : TripleLinearOrbit (U.comap S.subtype) (V.comap S.subtype) (W.comap S.subtype)) :
      ∃ f : E ≃ₗ[K] E, (∀ x y, ω (f x) (f y) = ω x y) ∧
        U.map f.toLinearMap = (p.val.1.map S.subtype).map (e T).toLinearMap ∧
        V.map f.toLinearMap = (p.val.2.1.map S.subtype).map (e T).toLinearMap ∧
        W.map f.toLinearMap = (p.val.2.2.map S.subtype).map (e T).toLinearMap := by
    obtain ⟨g,hgU,hgV,hgW⟩ := p.property
    obtain ⟨r,hr,hrg⟩ := exists_isotropic_isometry_extension ω h2 ha hω S S hS hS g
    refine ⟨r.trans (e T),?_,?_,?_,?_⟩
    · intro x y
      exact ((he T).1 (r x) (r y)).trans (hr x y)
    · rw [submodule_map_trans,subspace_map_extension S S U hU r g hrg,hgU]
    · rw [submodule_map_trans,subspace_map_extension S S V hV r g hrg,hgV]
    · rw [submodule_map_trans,subspace_map_extension S S W hW r g hrg,hgW]
  let f : IsotropicDimspace ω (finrank K S) ×
      TripleLinearOrbit (U.comap S.subtype) (V.comap S.subtype) (W.comap S.subtype) →
        OrderedTripleOrbit ω U V W := fun p =>
    ⟨((p.2.val.1.map S.subtype).map (e p.1).toLinearMap,
      (p.2.val.2.1.map S.subtype).map (e p.1).toLinearMap,
      (p.2.val.2.2.map S.subtype).map (e p.1).toLinearMap),hgood p.1 p.2⟩
  have hsum' (p : TripleLinearOrbit (U.comap S.subtype) (V.comap S.subtype) (W.comap S.subtype)) :
      p.val.1 ⊔ p.val.2.1 ⊔ p.val.2.2 = ⊤ := by
    obtain ⟨g,hgU,hgV,hgW⟩ := p.property
    rw [←hgU,←hgV,←hgW,←Submodule.map_sup,←Submodule.map_sup,
      ←subspace_comap_sup_of_le S U V hU hV,
      ←subspace_comap_sup_of_le S (U ⊔ V) W (sup_le hU hV) hW,hsum]
    simp
  have hrecover (p) : (f p).val.1 ⊔ (f p).val.2.1 ⊔ (f p).val.2.2 = p.1.val := by
    change ((p.2.val.1.map S.subtype).map (e p.1).toLinearMap) ⊔
      ((p.2.val.2.1.map S.subtype).map (e p.1).toLinearMap) ⊔
      ((p.2.val.2.2.map S.subtype).map (e p.1).toLinearMap) = _
    rw [←Submodule.map_sup,←Submodule.map_sup,←Submodule.map_sup,←Submodule.map_sup,hsum']
    simpa only [Submodule.map_top,Submodule.range_subtype] using (he p.1).2
  refine ⟨f,?_⟩
  rintro ⟨T,p⟩ ⟨T',p'⟩ h
  have hT : T = T' := by
    apply Subtype.ext
    exact (hrecover (T,p)).symm.trans ((congrArg (fun x : OrderedTripleOrbit ω U V W =>
      x.val.1 ⊔ x.val.2.1 ⊔ x.val.2.2) h).trans (hrecover (T',p')))
  subst T'
  have hv := congrArg Subtype.val h
  have hinj := (Submodule.map_injective_of_injective (e T).injective).comp
    (Submodule.map_injective_of_injective S.subtype_injective)
  have hp : p = p' := Subtype.ext (Prod.ext (hinj (congrArg Prod.fst hv))
    (Prod.ext (hinj (congrArg (fun x => x.2.1) hv)) (hinj (congrArg (fun x => x.2.2) hv))))
  subst p'
  rfl
end ConfigurationOrbit
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section PairOrbitAssembly
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E) (L M N : SymplecticLagrangian ω)
 theorem fullTripleOrbit_fixedPair_injection :
    ∃ f : OrderedTripleOrbit ω (L.val ⊓ M.val) (L.val ⊓ N.val) (M.val ⊓ N.val) ×
      FixedPairTripleOrbit ω L M N → OrderedTripleOrbit ω L.val M.val N.val,
      Function.Injective f := by
  classical
  let e (p : OrderedTripleOrbit ω (L.val ⊓ M.val) (L.val ⊓ N.val) (M.val ⊓ N.val)) :=
    p.property.choose
  have he (p : OrderedTripleOrbit ω (L.val ⊓ M.val) (L.val ⊓ N.val) (M.val ⊓ N.val)) := p.property.choose_spec
  have hgood (p : OrderedTripleOrbit ω (L.val ⊓ M.val) (L.val ⊓ N.val) (M.val ⊓ N.val))
      (q : FixedPairTripleOrbit ω L M N) :
      TripleIsometry ω ω L.val M.val N.val (q.val.val.1.val.map (e p).toLinearMap)
        (q.val.val.2.1.val.map (e p).toLinearMap) (q.val.val.2.2.val.map (e p).toLinearMap) := by
    obtain ⟨g,hg,hgL,hgM,hgN⟩ := q.val.property
    refine ⟨g.trans (e p),?_,?_,?_,?_⟩
    · intro x y
      exact ((he p).1 (g x) (g y)).trans (hg x y)
    · rw [submodule_map_trans,hgL]
    · rw [submodule_map_trans,hgM]
    · rw [submodule_map_trans,hgN]
  let f : OrderedTripleOrbit ω (L.val ⊓ M.val) (L.val ⊓ N.val) (M.val ⊓ N.val) ×
      FixedPairTripleOrbit ω L M N → OrderedTripleOrbit ω L.val M.val N.val := fun p =>
    ⟨(p.2.val.val.1.val.map (e p.1).toLinearMap,
      p.2.val.val.2.1.val.map (e p.1).toLinearMap,
      p.2.val.val.2.2.val.map (e p.1).toLinearMap),hgood p.1 p.2⟩
  have hrec (p) : ((f p).val.1 ⊓ (f p).val.2.1,
      (f p).val.1 ⊓ (f p).val.2.2,(f p).val.2.1 ⊓ (f p).val.2.2) = p.1.val := by
    change ((p.2.val.val.1.val.map (e p.1).toLinearMap) ⊓ (p.2.val.val.2.1.val.map (e p.1).toLinearMap),
      (p.2.val.val.1.val.map (e p.1).toLinearMap) ⊓ (p.2.val.val.2.2.val.map (e p.1).toLinearMap),
      (p.2.val.val.2.1.val.map (e p.1).toLinearMap) ⊓ (p.2.val.val.2.2.val.map (e p.1).toLinearMap)) = _
    rw [←Submodule.map_inf (e p.1).toLinearMap (e p.1).injective,
      ←Submodule.map_inf (e p.1).toLinearMap (e p.1).injective,
      ←Submodule.map_inf (e p.1).toLinearMap (e p.1).injective,
      p.2.property.1,p.2.property.2.1,p.2.property.2.2,
      (he p.1).2.1,(he p.1).2.2.1,(he p.1).2.2.2]
  refine ⟨f,?_⟩
  rintro ⟨p,q⟩ ⟨p',q'⟩ h
  have hp : p = p' := by
    apply Subtype.ext
    exact (hrec (p,q)).symm.trans ((congrArg (fun x : OrderedTripleOrbit ω L.val M.val N.val =>
      (x.val.1 ⊓ x.val.2.1,x.val.1 ⊓ x.val.2.2,x.val.2.1 ⊓ x.val.2.2)) h).trans (hrec (p',q')))
  subst p'
  have hv := congrArg Subtype.val h
  have hinj := Submodule.map_injective_of_injective (e p).injective
  have hq : q = q' := Subtype.ext (Subtype.ext
    (Prod.ext (Subtype.ext (hinj (congrArg Prod.fst hv)))
      (Prod.ext (Subtype.ext (hinj (congrArg (fun x => x.2.1) hv)))
        (Subtype.ext (hinj (congrArg (fun x => x.2.2) hv))))))
  subst q'
  rfl
variable [Finite E]
 theorem fullTripleOrbit_fixedPair_card_lower :
    Nat.card (OrderedTripleOrbit ω (L.val ⊓ M.val) (L.val ⊓ N.val) (M.val ⊓ N.val)) *
        Nat.card (FixedPairTripleOrbit ω L M N) ≤ Nat.card (OrderedTripleOrbit ω L.val M.val N.val) := by
  obtain ⟨f,hf⟩ := fullTripleOrbit_fixedPair_injection ω L M N
  simpa only [Nat.card_prod] using Nat.card_le_card_of_injective f hf
end PairOrbitAssembly
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ConfigurationCount
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
  [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
 theorem triple_isotropic_orbit_card_lower (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D = finrank K E)
    (S U V W : Submodule K E) (hS : S ≤ ω.orthogonal S)
    (hU : U ≤ S) (hV : V ≤ S) (hW : W ≤ S) (hsum : U ⊔ V ⊔ W = S)
    (hdis : Disjoint U (V ⊔ W)) (hVW : Disjoint V W) :
    (Fintype.card K : ℝ)^(isotropicExponent D (finrank K S) +
      2*(finrank K U*finrank K V+finrank K U*finrank K W+finrank K V*finrank K W)) ≤
      (lagrangianConstant D * 2^D) * Nat.card (OrderedTripleOrbit ω U V W) := by
  let U' := U.comap S.subtype
  let V' := V.comap S.subtype
  let W' := W.comap S.subtype
  have hc : IsCompl U' (V' ⊔ W') := by
    constructor
    · apply disjoint_iff.mpr
      change U.comap S.subtype ⊓ (V.comap S.subtype ⊔ W.comap S.subtype) = ⊥
      rw [←subspace_comap_sup_of_le S V W hV hW,←Submodule.comap_inf,disjoint_iff.mp hdis]
      simp
    · apply codisjoint_iff.mpr
      change U.comap S.subtype ⊔ (V.comap S.subtype ⊔ W.comap S.subtype) = ⊤
      rw [←sup_assoc,←subspace_comap_sup_of_le S U V hU hV,
        ←subspace_comap_sup_of_le S (U ⊔ V) W (sup_le hU hV) hW,hsum]
      simp
  have hvw : Disjoint V' W' := by
    apply disjoint_iff.mpr
    change V.comap S.subtype ⊓ W.comap S.subtype = ⊥
    rw [←Submodule.comap_inf,disjoint_iff.mp hVW]
    simp
  have hu' : finrank K U' = finrank K U := (Submodule.comapSubtypeEquivOfLe hU).finrank_eq
  have hv' : finrank K V' = finrank K V := (Submodule.comapSubtypeEquivOfLe hV).finrank_eq
  have hw' : finrank K W' = finrank K W := (Submodule.comapSubtypeEquivOfLe hW).finrank_eq
  have hb := (tripleLinearOrbit_card_bounds U' V' W' hc hvw).1
  rw [hu',hv',hw'] at hb
  have hs := isotropic_finrank_le_half ω hω D hD S hS
  have hi := (isotropic_card_bounds ω h2 ha hω D hD (finrank K S) hs).1
  obtain ⟨f,hf⟩ := triple_subspace_orbit_injection ω h2 ha hω S U V W hS hU hV hW hsum
  have hcard : (Nat.card (IsotropicDimspace ω (finrank K S)) : ℝ)*
      Nat.card (TripleLinearOrbit U' V' W') ≤ Nat.card (OrderedTripleOrbit ω U V W) := by
    have hh := Nat.card_le_card_of_injective f hf
    rw [Nat.card_prod] at hh
    exact_mod_cast hh
  have hk : lagrangianConstant (D-finrank K S) * (2:ℝ)^(finrank K S) ≤ lagrangianConstant D * 2^D := by
    exact mul_le_mul (lagrangianConstant_mono (Nat.sub_le D _))
      (pow_le_pow_right₀ (by norm_num) hs) (by positivity)
      (le_of_lt (lagrangianConstant_pos D))
  calc
    _ = (Fintype.card K : ℝ)^isotropicExponent D (finrank K S) *
      (Fintype.card K : ℝ)^(2*(finrank K U*finrank K V+finrank K U*finrank K W+finrank K V*finrank K W)) := by rw [pow_add]
    _ ≤ (lagrangianConstant (D-finrank K S)*Nat.card (IsotropicDimspace ω (finrank K S))) *
      (2^(finrank K S)*Nat.card (TripleLinearOrbit U' V' W')) :=
        mul_le_mul hi hb (by positivity)
          (mul_nonneg (le_of_lt (lagrangianConstant_pos _)) (Nat.cast_nonneg _))
    _ = (lagrangianConstant (D-finrank K S)*2^(finrank K S))*
      ((Nat.card (IsotropicDimspace ω (finrank K S)) : ℝ)*Nat.card (TripleLinearOrbit U' V' W')) := by ring
    _ ≤ (lagrangianConstant D*2^D)*Nat.card (OrderedTripleOrbit ω U V W) :=
      mul_le_mul hk hcard (by positivity)
        (mul_nonneg (le_of_lt (lagrangianConstant_pos _)) (by positivity))
end ConfigurationCount
section FixedPairCount
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
  [Fintype K] [Finite E] [Invertible (2:K)]
variable (ω : LinearMap.BilinForm K E)
 theorem fixedPairTripleOrbit_card_lower (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D = finrank K E)
    (hq : 4*lagrangianConstant D ≤ (Fintype.card K : ℝ))
    (L M N : SymplecticLagrangian ω) (h0 : (L.val ⊓ M.val) ⊓ N.val = ⊥) :
    let S := triplePairSum L.val M.val N.val
    (Fintype.card K : ℝ)^((D-finrank K ↥(L.val ⊓ S)+1).choose 2 +
      (D-finrank K ↥(M.val ⊓ S)+1).choose 2 + (D-finrank K ↥(N.val ⊓ S)+1).choose 2) ≤
      (8 * (4^D * lagrangianConstant D^2)) * Nat.card (FixedPairTripleOrbit ω L M N) := by
  dsimp only
  let S := triplePairSum L.val M.val N.val
  have hs : S ≤ ω.orthogonal S := triplePairSum_isotropic ω _ _ _ L.property M.property N.property
  have his (P : SymplecticLagrangian ω) : P.val ⊓ S ≤ ω.orthogonal (P.val ⊓ S) := by
    intro x hx y hy
    exact P.property.ge hx.1 y hy.1
  have h2 := (isUnit_of_invertible (2:K)).ne_zero
  have h₁ := (containingLagrangian_card_bounds ω h2 ha hω D hD (L.val ⊓ S) (his L)).1
  have h₂ := (containingLagrangian_card_bounds ω h2 ha hω D hD (M.val ⊓ S) (his M)).1
  have h₃ := (containingLagrangian_card_bounds ω h2 ha hω D hD (N.val ⊓ S) (his N)).1
  have ht := triplePairSum_reductions_transverse ω L.val M.val N.val L.property M.property N.property
  have hb := containmentOrbitFiber_card_lower ω S ha hω hs D hD hq
    (L.val ⊓ S) (M.val ⊓ S) (N.val ⊓ S) inf_le_right inf_le_right inf_le_right
    (tripleResidualLagrangian ω L M N ha hω L)
    (tripleResidualLagrangian ω L M N ha hω M) (tripleResidualLagrangian ω L M N ha hω N)
    ht.1 ht.2.1 ht.2.2
  have he := ownAvoidanceOrbitFiberEmbedding ω L M N ha hω h0
  have hc : (Nat.card (OwnAvoidanceOrbitFiber ω L M N ha hω) : ℝ) ≤
      Nat.card (FixedPairTripleOrbit ω L M N) := by exact_mod_cast Nat.card_le_card_of_injective he he.injective
  calc
    _ = (Fintype.card K : ℝ)^((D-finrank K ↥(L.val ⊓ S)+1).choose 2) *
      ((Fintype.card K : ℝ)^((D-finrank K ↥(M.val ⊓ S)+1).choose 2) *
        (Fintype.card K : ℝ)^((D-finrank K ↥(N.val ⊓ S)+1).choose 2)) := by simp only [pow_add]; ring
    _ ≤ (Nat.card {P : SymplecticLagrangian ω // L.val ⊓ S ≤ P.val} : ℝ)*
      (Nat.card {P : SymplecticLagrangian ω // M.val ⊓ S ≤ P.val} *
        Nat.card {P : SymplecticLagrangian ω // N.val ⊓ S ≤ P.val}) := by gcongr
    _ ≤ _ := hb
    _ ≤ _ := mul_le_mul_of_nonneg_left hc (by positivity)
end FixedPairCount
end SidorenkoCounterexample
namespace SidorenkoCounterexample
theorem pair_cost_cancellation (D u v w : ℕ) (h : u+v+w ≤ D) :
    isotropicExponent D (u+v+w) + 2*(u*v+u*w+v*w) +
      ((D-(u+v)+1).choose 2 + (D-(u+w)+1).choose 2 + (D-(v+w)+1).choose 2) +
      ((u+1).choose 2 + (v+1).choose 2 + (w+1).choose 2) = 3*(D+1).choose 2 := by
  have hu : u+v ≤ D := by omega
  have hv : u+w ≤ D := by omega
  have hw : v+w ≤ D := by omega
  have hi := isotropicExponent_add D (u+v+w) h
  have hi' : (isotropicExponent D (u+v+w) : ℚ) =
      ((D+1).choose 2 : ℚ) + (u+v+w)*(D-(u+v+w)) - ((D-(u+v+w)+1).choose 2 : ℚ) := by
    have hiq := congrArg (fun x : ℕ => (x:ℚ)) hi
    simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_sub h] at hiq
    linarith
  apply @Nat.cast_injective ℚ
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,hi',Nat.cast_choose_two,Nat.cast_one,
    Nat.cast_sub hu,Nat.cast_sub hv,Nat.cast_sub hw,Nat.cast_sub h]
  ring
theorem common_cost_cancellation (D c : ℕ) (hc : c ≤ D) :
    isotropicExponent D c + 3*(D-c+1).choose 2 + (D+1)*c = 3*(D+1).choose 2 := by
  have hi := isotropicExponent_add D c hc
  have h : 2*((D-c+1).choose 2) + (D+1)*c + c*(D-c) = 2*((D+1).choose 2) := by
    apply @Nat.cast_injective ℚ
    simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_choose_two,Nat.cast_one,Nat.cast_sub hc]
    ring
  omega
open Module
section PairMass
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E)
 theorem finrank_sup_of_disjoint (U V : Submodule K E) (h : Disjoint U V) :
    finrank K ↥(U ⊔ V) = finrank K U + finrank K V := by
  have hh := U.finrank_sup_add_finrank_inf_eq V
  rw [disjoint_iff.mp h,finrank_bot,add_zero] at hh
  exact hh
 theorem triplePairSum_finrank (L M N : Submodule K E) (h0 : (L ⊓ M) ⊓ N = ⊥) :
    finrank K ↥(triplePairSum L M N) = finrank K ↥(L ⊓ M) + finrank K ↥(L ⊓ N) + finrank K ↥(M ⊓ N) := by
  have hd := triple_pairs_disjoint L M N h0
  change finrank K ↥(((L ⊓ M) ⊔ (L ⊓ N)) ⊔ (M ⊓ N)) = _
  rw [sup_assoc,finrank_sup_of_disjoint _ _ hd.1,finrank_sup_of_disjoint _ _ hd.2,add_assoc]
 theorem triplePairSum_inter_finrank (L M N : Submodule K E) (h0 : (L ⊓ M) ⊓ N = ⊥) :
    finrank K ↥(L ⊓ triplePairSum L M N) = finrank K ↥(L ⊓ M) + finrank K ↥(L ⊓ N) := by
  rw [triple_own_avoidance L M N h0]
  exact finrank_sup_of_disjoint _ _ ((triple_pairs_disjoint L M N h0).1.mono_right le_sup_left)
noncomputable def pairOrbitConstant (D : ℕ) : ℝ :=
  (lagrangianConstant D*2^D)*(8*(4^D*lagrangianConstant D^2))
 theorem pairOrbitConstant_pos (D : ℕ) : 0 < pairOrbitConstant D := by
  unfold pairOrbitConstant
  have h := lagrangianConstant_pos D
  positivity
variable [Fintype K] [Finite E] [Invertible (2:K)]
 theorem commonZeroOrbit_card_lower (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D = finrank K E)
    (hq : 4*lagrangianConstant D ≤ (Fintype.card K : ℝ))
    (L M N : SymplecticLagrangian ω) (h0 : (L.val ⊓ M.val) ⊓ N.val = ⊥) :
    (Fintype.card K : ℝ)^(3*(D+1).choose 2) ≤
      pairOrbitConstant D * (Fintype.card K : ℝ)^((finrank K ↥(L.val ⊓ M.val)+1).choose 2 +
        (finrank K ↥(L.val ⊓ N.val)+1).choose 2 + (finrank K ↥(M.val ⊓ N.val)+1).choose 2) *
      Nat.card (OrderedTripleOrbit ω L.val M.val N.val) := by
  let S := triplePairSum L.val M.val N.val
  let u := finrank K ↥(L.val ⊓ M.val)
  let v := finrank K ↥(L.val ⊓ N.val)
  let w := finrank K ↥(M.val ⊓ N.val)
  have hs : S ≤ ω.orthogonal S := triplePairSum_isotropic ω _ _ _ L.property M.property N.property
  have hdim : finrank K S = u+v+w := triplePairSum_finrank _ _ _ h0
  have hdimL : finrank K ↥(L.val ⊓ S) = u+v := triplePairSum_inter_finrank _ _ _ h0
  have h0M : (M.val ⊓ L.val) ⊓ N.val = ⊥ := by simpa only [inf_comm] using h0
  have h0N : (N.val ⊓ L.val) ⊓ M.val = ⊥ := by simpa only [inf_assoc,inf_left_comm,inf_comm] using h0
  have hSM : triplePairSum M.val L.val N.val = S := by dsimp [S,triplePairSum]; ac_rfl
  have hSN : triplePairSum N.val L.val M.val = S := by dsimp [S,triplePairSum]; ac_rfl
  have hdimM : finrank K ↥(M.val ⊓ S) = u+w := by
    have hh := triplePairSum_inter_finrank M.val L.val N.val h0M
    rw [hSM,inf_comm M.val L.val] at hh
    exact hh
  have hdimN : finrank K ↥(N.val ⊓ S) = v+w := by
    have hh := triplePairSum_inter_finrank N.val L.val M.val h0N
    rw [hSN,inf_comm N.val L.val,inf_comm N.val M.val] at hh
    exact hh
  have haD : u+v+w ≤ D := hdim ▸ isotropic_finrank_le_half ω hω D hD S hs
  have hd := triple_pairs_disjoint L.val M.val N.val h0
  have hc := triple_isotropic_orbit_card_lower ω (isUnit_of_invertible (2:K)).ne_zero ha hω D hD S
    (L.val ⊓ M.val) (L.val ⊓ N.val) (M.val ⊓ N.val) hs
    (le_sup_of_le_left le_sup_left) (le_sup_of_le_left le_sup_right) le_sup_right rfl hd.1 hd.2
  rw [hdim] at hc
  have hf := fixedPairTripleOrbit_card_lower ω ha hω D hD hq L M N h0
  change (Fintype.card K : ℝ)^((D-finrank K ↥(L.val ⊓ S)+1).choose 2 +
      (D-finrank K ↥(M.val ⊓ S)+1).choose 2 + (D-finrank K ↥(N.val ⊓ S)+1).choose 2) ≤ _ at hf
  rw [hdimL,hdimM,hdimN] at hf
  have hm : (Nat.card (OrderedTripleOrbit ω (L.val ⊓ M.val) (L.val ⊓ N.val) (M.val ⊓ N.val)) : ℝ) *
      Nat.card (FixedPairTripleOrbit ω L M N) ≤ Nat.card (OrderedTripleOrbit ω L.val M.val N.val) := by
    exact_mod_cast fullTripleOrbit_fixedPair_card_lower ω L M N
  have hn : 0 ≤ lagrangianConstant D*2^D := mul_nonneg (le_of_lt (lagrangianConstant_pos D)) (by positivity)
  have hp := mul_le_mul hc hf (by positivity)
    (mul_nonneg hn (Nat.cast_nonneg _))
  have hh : (Fintype.card K : ℝ)^(isotropicExponent D (u+v+w)+2*(u*v+u*w+v*w)+
      ((D-(u+v)+1).choose 2+(D-(u+w)+1).choose 2+(D-(v+w)+1).choose 2)) ≤
      pairOrbitConstant D * Nat.card (OrderedTripleOrbit ω L.val M.val N.val) := by
    calc
      _ ≤ (lagrangianConstant D*2^D)*Nat.card (OrderedTripleOrbit ω (L.val ⊓ M.val) (L.val ⊓ N.val) (M.val ⊓ N.val)) *
          ((8*(4^D*lagrangianConstant D^2))*Nat.card (FixedPairTripleOrbit ω L M N)) := by
        simpa only [pow_add] using hp
      _ = pairOrbitConstant D * ((Nat.card (OrderedTripleOrbit ω (L.val ⊓ M.val) (L.val ⊓ N.val) (M.val ⊓ N.val)) : ℝ)*
          Nat.card (FixedPairTripleOrbit ω L M N)) := by unfold pairOrbitConstant; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hm (le_of_lt (pairOrbitConstant_pos D))
  have hh' := mul_le_mul_of_nonneg_right hh
    (show 0 ≤ (Fintype.card K : ℝ)^((u+1).choose 2+(v+1).choose 2+(w+1).choose 2) by positivity)
  rw [←pow_add,pair_cost_cancellation D u v w haD] at hh'
  simpa only [mul_assoc,mul_left_comm,mul_comm] using hh'
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
 theorem reduceSubspace_finrank_containing (S A : Submodule K E)
    (hSA : S ≤ A) (hAP : A ≤ ω.orthogonal S) :
    finrank K (reduceSubspace ω S A) + finrank K S = finrank K A := by
  let f : A →ₗ[K] ReducedSpace ω S := (reductionKernel ω S).mkQ.comp (Submodule.inclusion hAP)
  have hk : LinearMap.ker f = S.comap A.subtype := by
    ext x
    exact Submodule.Quotient.mk_eq_zero (reductionKernel ω S)
  have hr : LinearMap.range f = reduceSubspace ω S A := by
    ext y
    constructor
    · rintro ⟨x,rfl⟩
      exact ⟨⟨x.val,hAP x.property⟩,x.property,rfl⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨⟨x.val,hx⟩,rfl⟩
  have hh := f.finrank_range_add_finrank_ker
  rw [hk,hr,(Submodule.comapSubtypeEquivOfLe hSA).finrank_eq] at hh
  exact hh
noncomputable def commonReductionLagrangian (S : Submodule K E) (ha : ω.IsAlt)
    (hS : S ≤ ω.orthogonal S) (L : SymplecticLagrangian ω) (hSL : S ≤ L.val) :
    SymplecticLagrangian (symplecticReductionForm ω S ha) :=
  ⟨reduceSubspace ω S L.val,reduce_lagrangian ω S ha hS L.val L.property hSL⟩
 theorem commonOrbit_injection [Finite E] (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (L M N : SymplecticLagrangian ω) :
    let S := (L.val ⊓ M.val) ⊓ N.val
    ∃ f : IsotropicDimspace ω (finrank K S) ×
      OrderedTripleOrbit (symplecticReductionForm ω S ha)
        (reduceSubspace ω S L.val) (reduceSubspace ω S M.val) (reduceSubspace ω S N.val) →
      OrderedTripleOrbit ω L.val M.val N.val, Function.Injective f := by
  dsimp only
  classical
  let S := (L.val ⊓ M.val) ⊓ N.val
  have hSL : S ≤ L.val := inf_le_left.trans inf_le_left
  have hSM : S ≤ M.val := inf_le_left.trans inf_le_right
  have hSN : S ≤ N.val := inf_le_right
  have hS : S ≤ ω.orthogonal S := by
    intro x hx y hy
    exact L.property.ge (hSL hx) y (hSL hy)
  let η := symplecticReductionForm ω S ha
  let L' := commonReductionLagrangian ω S ha hS L hSL
  let M' := commonReductionLagrangian ω S ha hS M hSM
  let N' := commonReductionLagrangian ω S ha hS N hSN
  have hzero : (L'.val ⊓ M'.val) ⊓ N'.val = ⊥ := by
    change (reduceSubspace ω S L.val ⊓ reduceSubspace ω S M.val) ⊓ reduceSubspace ω S N.val = ⊥
    rw [←reduceSubspace_inf ω S L.val M.val hSL,
      ←reduceSubspace_inf ω S (L.val ⊓ M.val) N.val inf_le_left]
    exact reduceSubspace_self ω S
  have ht (T : IsotropicDimspace ω (finrank K S)) := isotropic_transitivity ω h2 ha hω
    S T.val hS T.property.1 T.property.2.symm
  let e (T : IsotropicDimspace ω (finrank K S)) := (ht T).choose
  have he (T : IsotropicDimspace ω (finrank K S)) := (ht T).choose_spec
  let Orb := OrderedTripleOrbit η L'.val M'.val N'.val
  have hpLag (p : Orb) := orderedTripleOrbit_lagrangians η L' M' N' p
  have hpzero (p : Orb) : (p.val.1 ⊓ p.val.2.1) ⊓ p.val.2.2 = ⊥ := by
    obtain ⟨g,_,hgL,hgM,hgN⟩ := p.property
    rw [←hgL,←hgM,←hgN,←Submodule.map_inf g.toLinearMap g.injective,
      ←Submodule.map_inf g.toLinearMap g.injective,hzero,Submodule.map_bot]
  have hgood (p : Orb) : TripleIsometry ω ω L.val M.val N.val
      (liftReduction ω S p.val.1) (liftReduction ω S p.val.2.1) (liftReduction ω S p.val.2.2) := by
    apply triple_containing_isometry_lift ω S ha hω hS L.val M.val N.val
      (liftReduction ω S p.val.1) (liftReduction ω S p.val.2.1) (liftReduction ω S p.val.2.2)
      L.property M.property N.property
      (liftReduction_lagrangian ω S ha hS _ (hpLag p).1)
      (liftReduction_lagrangian ω S ha hS _ (hpLag p).2.1)
      (liftReduction_lagrangian ω S ha hS _ (hpLag p).2.2)
      hSL hSM hSN (le_liftReduction ω S hS _) (le_liftReduction ω S hS _) (le_liftReduction ω S hS _)
    rw [reduce_lift,reduce_lift,reduce_lift]
    exact p.property
  have hgood' (T : IsotropicDimspace ω (finrank K S)) (p : Orb) : TripleIsometry ω ω L.val M.val N.val
      ((liftReduction ω S p.val.1).map (e T).toLinearMap)
      ((liftReduction ω S p.val.2.1).map (e T).toLinearMap)
      ((liftReduction ω S p.val.2.2).map (e T).toLinearMap) := by
    obtain ⟨g,hg,hgL,hgM,hgN⟩ := hgood p
    refine ⟨g.trans (e T),?_,?_,?_,?_⟩
    · intro x y
      exact ((he T).1 (g x) (g y)).trans (hg x y)
    · rw [submodule_map_trans,hgL]
    · rw [submodule_map_trans,hgM]
    · rw [submodule_map_trans,hgN]
  let f : IsotropicDimspace ω (finrank K S) × Orb → OrderedTripleOrbit ω L.val M.val N.val := fun p =>
    ⟨((liftReduction ω S p.2.val.1).map (e p.1).toLinearMap,
      (liftReduction ω S p.2.val.2.1).map (e p.1).toLinearMap,
      (liftReduction ω S p.2.val.2.2).map (e p.1).toLinearMap),hgood' p.1 p.2⟩
  have hrec (p) : ((f p).val.1 ⊓ (f p).val.2.1) ⊓ (f p).val.2.2 = p.1.val := by
    change (((liftReduction ω S p.2.val.1).map (e p.1).toLinearMap) ⊓
      ((liftReduction ω S p.2.val.2.1).map (e p.1).toLinearMap)) ⊓
      ((liftReduction ω S p.2.val.2.2).map (e p.1).toLinearMap) = _
    rw [←Submodule.map_inf (e p.1).toLinearMap (e p.1).injective,
      ←Submodule.map_inf (e p.1).toLinearMap (e p.1).injective,
      ←liftReduction_inf,←liftReduction_inf,hpzero, liftReduction_bot ω S hS]
    exact (he p.1).2
  refine ⟨f,?_⟩
  rintro ⟨T,p⟩ ⟨T',p'⟩ h
  have hT : T = T' := by
    apply Subtype.ext
    exact (hrec (T,p)).symm.trans ((congrArg (fun x : OrderedTripleOrbit ω L.val M.val N.val =>
      (x.val.1 ⊓ x.val.2.1) ⊓ x.val.2.2) h).trans (hrec (T',p')))
  subst T'
  have hv := congrArg Subtype.val h
  have hinj := (Submodule.map_injective_of_injective (e T).injective).comp (liftReduction_injective ω S)
  have hp : p = p' := Subtype.ext (Prod.ext (hinj (congrArg Prod.fst hv))
    (Prod.ext (hinj (congrArg (fun x => x.2.1) hv)) (hinj (congrArg (fun x => x.2.2) hv))))
  subst p'
  rfl
variable [Finite E]
 theorem commonOrbit_card_lower (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (L M N : SymplecticLagrangian ω) :
    let S := (L.val ⊓ M.val) ⊓ N.val
    Nat.card (IsotropicDimspace ω (finrank K S)) *
      Nat.card (OrderedTripleOrbit (symplecticReductionForm ω S ha)
        (reduceSubspace ω S L.val) (reduceSubspace ω S M.val) (reduceSubspace ω S N.val)) ≤
      Nat.card (OrderedTripleOrbit ω L.val M.val N.val) := by
  obtain ⟨f,hf⟩ := commonOrbit_injection ω h2 ha hω L M N
  simpa only [Nat.card_prod] using Nat.card_le_card_of_injective f hf
end CommonOrbitGeometry
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section AllOrbitMass
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
  [Fintype K] [Finite E] [Invertible (2:K)]
variable (ω : LinearMap.BilinForm K E)
noncomputable def tripleDefect (D : ℕ) (L M N : Submodule K E) : ℕ :=
  let c := finrank K ↥((L ⊓ M) ⊓ N)
  (D+1)*c + ((finrank K ↥(L ⊓ M)-c+1).choose 2 +
    (finrank K ↥(L ⊓ N)-c+1).choose 2 + (finrank K ↥(M ⊓ N)-c+1).choose 2)
 theorem pairOrbitConstant_mono : Monotone pairOrbitConstant := by
  intro m n h
  unfold pairOrbitConstant
  have hm := lagrangianConstant_pos m
  have hn := lagrangianConstant_pos n
  have hc := lagrangianConstant_mono h
  gcongr <;> norm_num
noncomputable def orbitMassConstant (D : ℕ) : ℝ := lagrangianConstant D*pairOrbitConstant D
 theorem orbitMassConstant_pos (D : ℕ) : 0 < orbitMassConstant D :=
  mul_pos (lagrangianConstant_pos D) (pairOrbitConstant_pos D)
 theorem tripleOrbit_card_lower (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D = finrank K E)
    (hq : 4*lagrangianConstant D ≤ (Fintype.card K : ℝ))
    (L M N : SymplecticLagrangian ω) :
    (Fintype.card K : ℝ)^(3*(D+1).choose 2) ≤
      orbitMassConstant D * (Fintype.card K : ℝ)^(tripleDefect D L.val M.val N.val) *
        Nat.card (OrderedTripleOrbit ω L.val M.val N.val) := by
  let S := (L.val ⊓ M.val) ⊓ N.val
  have hSL : S ≤ L.val := inf_le_left.trans inf_le_left
  have hSM : S ≤ M.val := inf_le_left.trans inf_le_right
  have hSN : S ≤ N.val := inf_le_right
  have hS : S ≤ ω.orthogonal S := by
    intro x hx y hy
    exact L.property.ge (hSL hx) y (hSL hy)
  let c := finrank K S
  have hc : c ≤ D := isotropic_finrank_le_half ω hω D hD S hS
  let η := symplecticReductionForm ω S ha
  let L' := commonReductionLagrangian ω S ha hS L hSL
  let M' := commonReductionLagrangian ω S ha hS M hSM
  let N' := commonReductionLagrangian ω S ha hS N hSN
  let : Finite (ReducedSpace ω S) := Module.finite_of_finite K
  have hzero : (L'.val ⊓ M'.val) ⊓ N'.val = ⊥ := by
    change (reduceSubspace ω S L.val ⊓ reduceSubspace ω S M.val) ⊓ reduceSubspace ω S N.val = ⊥
    rw [←reduceSubspace_inf ω S L.val M.val hSL,
      ←reduceSubspace_inf ω S (L.val ⊓ M.val) N.val inf_le_left]
    exact reduceSubspace_self ω S
  have hdim : 2*(D-c) = finrank K (ReducedSpace ω S) := by
    have hh := reducedSpace_finrank ω S hω hS
    change _ + 2*c = _ at hh
    omega
  have hq' : 4*lagrangianConstant (D-c) ≤ (Fintype.card K : ℝ) :=
    (mul_le_mul_of_nonneg_left (lagrangianConstant_mono (Nat.sub_le D c)) (by norm_num)).trans hq
  have hp := commonZeroOrbit_card_lower η (symplecticReductionForm_alt ω S ha)
    (symplecticReductionForm_nondegenerate ω S ha hω) (D-c) hdim hq' L' M' N' hzero
  have hpair (P Q : SymplecticLagrangian ω) (hSP : S ≤ P.val) (hSQ : S ≤ Q.val) :
      finrank K ↥(reduceSubspace ω S P.val ⊓ reduceSubspace ω S Q.val) =
        finrank K ↥(P.val ⊓ Q.val)-c := by
    rw [←reduceSubspace_inf ω S P.val Q.val hSP]
    have hh := reduceSubspace_finrank_containing ω S (P.val ⊓ Q.val) (le_inf hSP hSQ)
      (inf_le_left.trans (lagrangian_le_orthogonal ω S P.val P.property hSP))
    change _ + c = _ at hh
    omega
  change (Fintype.card K : ℝ)^(3*(D-c+1).choose 2) ≤ pairOrbitConstant (D-c) *
    (Fintype.card K : ℝ)^((finrank K ↥(reduceSubspace ω S L.val ⊓ reduceSubspace ω S M.val)+1).choose 2 +
      (finrank K ↥(reduceSubspace ω S L.val ⊓ reduceSubspace ω S N.val)+1).choose 2 +
      (finrank K ↥(reduceSubspace ω S M.val ⊓ reduceSubspace ω S N.val)+1).choose 2) * _ at hp
  rw [hpair L M hSL hSM,hpair L N hSL hSN,hpair M N hSM hSN] at hp
  have h2 := (isUnit_of_invertible (2:K)).ne_zero
  have hi := (isotropic_card_bounds ω h2 ha hω D hD c hc).1
  have hm : (Nat.card (IsotropicDimspace ω c) : ℝ) *
    Nat.card (OrderedTripleOrbit η L'.val M'.val N'.val) ≤
      Nat.card (OrderedTripleOrbit ω L.val M.val N.val) := by
    exact_mod_cast commonOrbit_card_lower ω h2 ha hω L M N
  let δ := (finrank K ↥(L.val ⊓ M.val)-c+1).choose 2 +
    (finrank K ↥(L.val ⊓ N.val)-c+1).choose 2 + (finrank K ↥(M.val ⊓ N.val)-c+1).choose 2
  have hconst : lagrangianConstant (D-c)*pairOrbitConstant (D-c) ≤ orbitMassConstant D :=
    mul_le_mul (lagrangianConstant_mono (Nat.sub_le D c)) (pairOrbitConstant_mono (Nat.sub_le D c))
      (le_of_lt (pairOrbitConstant_pos _)) (le_of_lt (lagrangianConstant_pos _))
  have hm' := mul_le_mul hconst hm (by positivity) (le_of_lt (orbitMassConstant_pos D))
  have hbase : (Fintype.card K : ℝ)^(isotropicExponent D c+3*(D-c+1).choose 2) ≤
      orbitMassConstant D * (Fintype.card K : ℝ)^δ * Nat.card (OrderedTripleOrbit ω L.val M.val N.val) := by
    calc
      _ ≤ (lagrangianConstant (D-c)*Nat.card (IsotropicDimspace ω c)) *
        (pairOrbitConstant (D-c)*(Fintype.card K : ℝ)^δ * Nat.card (OrderedTripleOrbit η L'.val M'.val N'.val)) := by
          rw [pow_add]
          exact mul_le_mul hi hp (by positivity) (mul_nonneg (le_of_lt (lagrangianConstant_pos _)) (Nat.cast_nonneg _))
      _ = ((lagrangianConstant (D-c)*pairOrbitConstant (D-c))*
        ((Nat.card (IsotropicDimspace ω c) : ℝ)*Nat.card (OrderedTripleOrbit η L'.val M'.val N'.val)))*
          (Fintype.card K : ℝ)^δ := by ring
      _ ≤ (orbitMassConstant D*Nat.card (OrderedTripleOrbit ω L.val M.val N.val))*
          (Fintype.card K : ℝ)^δ := mul_le_mul_of_nonneg_right hm' (by positivity)
      _ = _ := by ring
  have hh := mul_le_mul_of_nonneg_right hbase (show 0 ≤ (Fintype.card K : ℝ)^((D+1)*c) by positivity)
  rw [←pow_add,common_cost_cancellation D c hc] at hh
  change _ ≤ orbitMassConstant D * (Fintype.card K : ℝ)^((D+1)*c+δ) * _
  rw [pow_add]
  calc
    _ ≤ (orbitMassConstant D*(Fintype.card K : ℝ)^δ*Nat.card (OrderedTripleOrbit ω L.val M.val N.val))*
      (Fintype.card K : ℝ)^((D+1)*c) := hh
    _ = _ := by ring
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
open Module Filter OAI.SidorenkoCounterexample

theorem OMA.solution : OMA.R_SidorenkoConjecture_sidorenko_conjecture_graphon_R1_H1_R1_H1_R1_H1_R1_H1_R1_H2_R1.H1 := by
  intro d
  let l := lagrangianConstant d
  have ht : Tendsto (fun q : {q : ℕ // q.Prime ∧ q ≠ 2} => (q.val : ℝ)) (comap (fun q => q.val) atTop) atTop := tendsto_natCast_atTop_atTop.comp Filter.tendsto_comap
  filter_upwards [ht.eventually (eventually_ge_atTop (4*l))] with q hq
  letI : Fact q.val.Prime := ⟨q.2.1⟩
  have h2 : (2 : ZMod q.val) ≠ 0 := Ring.two_ne_zero (by simpa only [ZMod.ringChar_zmod_n] using q.property.2)
  letI : Invertible (2:ZMod q.val) := invertibleOfNonzero h2
  dsimp only
  intro E _ _ _ w ha hw hd L M N
  have h := tripleOrbit_card_lower w ha hw d hd (by simpa only [ZMod.card] using hq) L M N
  simpa only [ZMod.card,orbitMassConstant,pairOrbitConstant,lagrangianConstant,tripleDefect,OrderedTripleOrbit] using h
