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
end NormalCoordinates
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section PairCounts
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
def verticalSpace : Submodule K (V × Module.Dual K V) :=
  (LinearMap.fst K V (Module.Dual K V)).ker
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
abbrev CenterStratum (r : ℕ) := {L : Lagrangian (K := K) (V := V) //
  finrank K ↥(L.val ⊓ verticalSpace (K := K) (V := V)) = r}
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
theorem fullGraph_selforthogonal (B : LinearMap.BilinForm K V) (hs : B.IsSymm) :
    canonicalSymplectic.orthogonal B.graph = B.graph := by
  ext x
  constructor
  · intro hx
    apply (B.mem_graph_iff x).mpr
    ext y
    have hh := hx (y,B y) (by rfl)
    change x.2 y - B y x.1 = 0 at hh
    exact (sub_eq_zero.mp hh).trans (hs.eq y x.1)
  · intro hx y hy
    have hx' := (B.mem_graph_iff x).mp hx
    have hy' := (B.mem_graph_iff y).mp hy
    change x.2 y.1 - y.2 x.1 = 0
    rw [hx',hy',hs.eq]
    exact sub_self _
theorem fullGraph_injective : Function.Injective
    (fun B : LinearMap.BilinForm K V => B.graph) := by
  intro B C h
  change B.graph = C.graph at h
  apply LinearMap.ext
  intro x
  have hx : (x,B x) ∈ C.graph := by rw [← h]; rfl
  exact (C.mem_graph_iff _).mp hx
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
abbrev SymplecticCenterStratum (Y : SymplecticLagrangian ω) (r : ℕ) :=
  {L : SymplecticLagrangian ω // finrank K ↥(L.val ⊓ Y.val) = r}
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
 def classContains (c : Fin 6) (j : Fin 22) : Prop := ∃ n, classFace c n=j
 instance (c : Fin 6) (j : Fin 22) : Decidable (classContains c j) := inferInstanceAs (Decidable (∃ n, classFace c n=j))
 def classInternal (c : Fin 6) (e : Fin 33) : Prop := ∀ k, classContains c (pairFace e k)
 instance (c : Fin 6) (e : Fin 33) : Decidable (classInternal c e) := inferInstanceAs (Decidable (∀ k, classContains c (pairFace e k)))
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
abbrev ActiveCenterSet (r : ℕ) (L : Fin 3 → SymplecticLagrangian ω) (T : Finset (Fin 3)) :=
  {Y : SymplecticLagrangian ω // ∀ i∈T,finrank K ↥((L i).val⊓Y.val)=r}
noncomputable def activeFaceDensity (r : ℕ) (A : SymplecticLagrangian ω)
    (L : Fin 3 → SymplecticLagrangian ω) (T : Finset (Fin 3)) : ℝ :=
  (Nat.card (ActiveCenterSet ω r L T):ℝ)/(Nat.card (SymplecticLagrangian ω):ℝ)*
    ((Nat.card (SymplecticLagrangian ω):ℝ)/Nat.card (SymplecticCenterStratum ω A r))^T.card
 omit [Fintype K] [Finite E] in
 theorem activeFaceDensity_nonneg (r : ℕ) (A : SymplecticLagrangian ω)
    (L : Fin 3 → SymplecticLagrangian ω) (T : Finset (Fin 3)) :
    0 ≤ activeFaceDensity ω r A L T := by unfold activeFaceDensity; positivity
end ActiveFace
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section ActiveFaceBound
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
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
variable [FiniteDimensional K V] [Fintype K] [DecidableEq K]
noncomputable def discriminantSign (B : LinearMap.BilinForm K V) (hB : B.IsSymm) : ℤ :=
  quadraticChar K ((radicalQuotientForm B hB).toMatrix
    (Module.finBasis K (V ⧸ B.ker))).det
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
@[simp] theorem mem_signedLayer (r : ℕ) (ξ : ℤ) (Z : SymMatrix K D) :
    Z ∈ signedLayer K D r ξ ↔ Z.val.rank = r ∧ matrixSign K D Z = ξ := by
  classical
  simp [signedLayer]
theorem signedLayer_nonempty {r : ℕ} (hr : 0 < r) (hrD : r ≤ D)
    (hK : ringChar K ≠ 2) {ξ : ℤ} (hξ : ξ = 1 ∨ ξ = -1) :
    (signedLayer K D r ξ).Nonempty := by
  obtain ⟨Z, hz, hs⟩ := exists_matrix_rank_sign K D hr hrD hK hξ
  exact ⟨Z, (mem_signedLayer K D r ξ Z).mpr ⟨hz, hs⟩⟩
theorem layerMass_pos {r : ℕ} (hr : 0 < r) (hrD : r ≤ D)
    (hK : ringChar K ≠ 2) {ξ : ℤ} (hξ : ξ = 1 ∨ ξ = -1) :
    0 < layerMass K D r ξ := by
  apply div_pos
  · exact_mod_cast (signedLayer_nonempty K D hr hrD hK hξ).card_pos
  · exact_mod_cast Fintype.card_pos (α := SymMatrix K D)
end FiniteLayer
noncomputable def uniformMean {A : Type*} [Fintype A] (f : A → ℝ) : ℝ :=
  (∑ a, f a) / Fintype.card A
abbrev OddPrime := {q : ℕ // q.Prime ∧ q ≠ 2}
instance (q : OddPrime) : Fact q.val.Prime := ⟨q.property.1⟩
def primeInfinity : Filter OddPrime := Filter.comap Subtype.val Filter.atTop
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module LinearMap
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
end Binary
section Norms
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]
variable [Fintype K]
end Norms
section Equivalences
variable {K E F : Type*} [Field K] [AddCommGroup E] [Module K E]
  [AddCommGroup F] [Module K F]
variable [FiniteDimensional K E] [FiniteDimensional K F] [Fintype K] [DecidableEq K]
end Equivalences
section Classification
variable {K E F : Type*} [Field K] [AddCommGroup E] [Module K E]
  [AddCommGroup F] [Module K F] [FiniteDimensional K E] [FiniteDimensional K F]
  [Fintype K] [DecidableEq K]
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
end LinearMean
section Forms
variable {K V : Type*} [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
noncomputable instance symForm_fintype : Fintype (SymForm K V) := Fintype.ofFinite _
variable {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
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
variable [FiniteDimensional K V]
end Projections
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module LinearMap
open scoped Matrix
section MatrixProjection
variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]
def CenterProjection (Q : Matrix n n K) :=
  {A : Matrix n n K // A.IsSymm ∧ A*Q*A=A}
end MatrixProjection
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module LinearMap
open scoped Matrix
section Range
variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]
variable [Fintype K] [DecidableEq K]
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
end FormSum
section Complement
variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]
end Complement
section Signs
variable {K n : Type*} [Field K] [Fintype K] [DecidableEq K] [Fintype n] [DecidableEq n]
end Signs
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section Split
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
end Split
section Signs
variable {K V : Type*} [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
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
variable [AddGroup A]
end Means
section ShiftError
variable {K U : Type*} [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup U] [Module K U] [FiniteDimensional K U]
end ShiftError
section Separate
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
end Separate
section Covariance
variable {K V : Type*} [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
end Covariance
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section Variance
variable {A I : Type*} [Fintype A] [Fintype I] [Nonempty I]
end Variance
section Restriction
variable {K V I : Type*} [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype I] [Nonempty I]
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
variable [FiniteDimensional K V] [Fintype K]
end AlternatingTwo
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module
section OrthogonalCharts
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [FiniteDimensional K V]
end OrthogonalCharts
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module
section SplitSign
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [FiniteDimensional K V] [Fintype K] [DecidableEq K]
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
end CountDimension
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module LinearMap
open scoped Matrix BigOperators
section PairSigns
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] {D r : ℕ}
end PairSigns
section Equiv
variable {K n : Type*} [Field K] [Fintype K] [DecidableEq K] [Fintype n] [DecidableEq n]
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
end SignedProjector
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module LinearMap
open scoped Matrix BigOperators
section Isotropic
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [FiniteDimensional K V]
end Isotropic
section Triple
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] {D r : ℕ}
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
end Count
section Identities
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] {D r : ℕ}
end Identities
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module Filter
open scoped BigOperators
section Coeff
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
end Coeff
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section Sizes
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
end Sizes
section Bounds
variable {K I : Type*} [Field K] [Fintype K] [DecidableEq K] [Fintype I] {D r : ℕ}
end Bounds
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open scoped BigOperators
section Mean
variable {I A B : Type*} [Fintype I] [DecidableEq I] [Fintype A] [Fintype B]
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
end Inverting
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module Classical
open scoped Matrix BigOperators
section Center
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
end Center
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module Classical
open scoped BigOperators
section Means
variable {A B : Type*} [Fintype A] [Fintype B]
variable [AddCommGroup A]
end Means
section Range
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] {D : ℕ}
end Range
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module Classical Filter
open scoped BigOperators
section Error
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
end Error
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module Classical Filter
open scoped BigOperators
section Bounds
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
end Bounds
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
variable [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype W]
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
section Signs
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] {D : ℕ}
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
end Product
section Mean
variable {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A]
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
end Difference
section Pair
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] {D : ℕ}
end Pair
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module Classical
open scoped BigOperators
section Graph
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
noncomputable def fullGraphIntersection (B C : LinearMap.BilinForm K V) :
    (B-C).ker ≃ₗ[K] ↥(B.graph⊓C.graph) where
  toFun x := ⟨(x.val,B x.val),by
    constructor
    · rfl
    · apply (C.mem_graph_iff _).mpr
      exact sub_eq_zero.mp (show B x.val-C x.val=0 from x.property)⟩
  invFun x := ⟨x.val.1,by
    have hb := (B.mem_graph_iff _).mp x.property.1
    have hc := (C.mem_graph_iff _).mp x.property.2
    change B x.val.1-C x.val.1=0
    rw [←hb,←hc,sub_self]⟩
  left_inv x := rfl
  right_inv x := by
    apply Subtype.ext
    exact Prod.ext rfl ((B.mem_graph_iff _).mp x.property.1).symm
  map_add' x y := by apply Subtype.ext; simp
  map_smul' c x := by apply Subtype.ext; simp
noncomputable def matrixLagrangian {D : ℕ} (M : SymMatrix K D) :
    SymplecticLagrangian (canonicalSymplectic (K := K) (V := Fin D → K)) :=
  ⟨M.val.toBilin'.graph, fullGraph_selforthogonal _ (Matrix.isSymm_toBilin'_iff_isSymm.mpr M.property)⟩
theorem matrixLagrangian_injective (D : ℕ) : Function.Injective (matrixLagrangian (K := K) (D := D)) := by
  intro A B h
  apply Subtype.ext
  apply Matrix.toBilin'.injective
  exact fullGraph_injective (congrArg Subtype.val h)
theorem matrixLagrangian_pair_rank (D : ℕ) (A B : SymMatrix K D) :
    finrank K ↥((matrixLagrangian A).val⊓(matrixLagrangian B).val)+(A-B).val.rank=D := by
  have h := ((A-B).val.toBilin').ker.finrank_quotient_add_finrank
  rw [matrix_radical_quotient_rank] at h
  have he := (fullGraphIntersection A.val.toBilin' B.val.toBilin').finrank_eq
  have hf : (A-B).val.toBilin'=A.val.toBilin'-B.val.toBilin' := by rw [Submodule.coe_sub,map_sub]
  rw [hf] at h
  simp only [Module.finrank_pi,Fintype.card_fin] at h
  change finrank K ↥(A.val.toBilin'.graph⊓B.val.toBilin'.graph)+(A-B).val.rank=D
  omega
theorem matrixLagrangian_pair_zero (D : ℕ) (A B : SymMatrix K D) :
    finrank K ↥((matrixLagrangian A).val⊓(matrixLagrangian B).val)=0 ↔ (A-B).val.det≠0 := by
  change finrank K ↥(A.val.toBilin'.graph⊓B.val.toBilin'.graph)=0 ↔ (A-B).val.det≠0
  rw [← (fullGraphIntersection A.val.toBilin' B.val.toBilin').finrank_eq]
  have hf : (A-B).val.toBilin'=A.val.toBilin'-B.val.toBilin' := by rw [Submodule.coe_sub,map_sub]
  rw [←hf,Submodule.finrank_eq_zero]
  exact LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot.symm.trans
    (Matrix.nondegenerate_toBilin'_iff.trans Matrix.nondegenerate_iff_det_ne_zero)
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
theorem uniformMean_injection (i : A → B) (hi : Function.Injective i) (f : B → ℝ)
    (hf : ∀ b,0≤f b) : uniformMean (f ∘ i) ≤
      ((Fintype.card B : ℝ)/Fintype.card A)*uniformMean f := by
  classical
  have hs : ∑ a, f (i a) ≤ ∑ b, f b := by
    rw [←Finset.sum_image (fun a _ b _ h => hi h)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun b _ _ => hf b)
  unfold uniformMean
  dsimp only [Function.comp_def]
  have hn : (Fintype.card B : ℝ)≠0 := by exact_mod_cast (Fintype.card_pos (α := B)).ne'
  have he : ((Fintype.card B : ℝ)/Fintype.card A)*((∑ b,f b)/Fintype.card B)=
      (∑ b,f b)/Fintype.card A := by
    calc
      _ = ((∑ b,f b)/Fintype.card A)*((Fintype.card B : ℝ)/Fintype.card B) := by ring
      _ = _ := by rw [div_self hn,mul_one]
  rw [he]
  exact div_le_div_of_nonneg_right hs (Nat.cast_nonneg _)
end Mean
section Norm
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
noncomputable def canonicalStratumMass (D r : ℕ) : ℝ :=
  (Nat.card (CenterStratum (K := K) (V := Fin D → K) r) : ℝ)/
    Nat.card (Lagrangian (K := K) (V := Fin D → K))
noncomputable def chartRatio (D : ℕ) : ℝ :=
  (Nat.card (Lagrangian (K := K) (V := Fin D → K)) : ℝ)/
    Fintype.card (SymMatrix K D)
omit [DecidableEq K] in
theorem chartRatio_nonneg (D : ℕ) : 0≤chartRatio (K := K) D := by unfold chartRatio; positivity
omit [DecidableEq K] in
theorem chartRatio_bound (D : ℕ) : chartRatio (K := K) D≤lagrangianConstant D := by
  have hc : (Fintype.card (SymMatrix K D) : ℝ)=(Fintype.card K : ℝ)^((D+1).choose 2) := by
    rw [←Nat.card_eq_fintype_card,symMatrix_card,Nat.cast_pow]
  have hn : (0 : ℝ)<(Fintype.card K : ℝ)^((D+1).choose 2) := by positivity
  unfold chartRatio
  rw [hc]
  apply (div_le_iff₀ hn).mpr
  simpa only [Module.finrank_pi,Fintype.card_fin] using lagrangian_card_upper (K := K) (V := Fin D → K)
omit [DecidableEq K] in
theorem canonicalStratum_card (D r : ℕ) (hr : r≤D) :
    Nat.card (CenterStratum (K := K) (V := Fin D → K) r) =
      Nat.card (DimSubspace K (Fin D → K) (D-r)) * (Fintype.card K)^((D-r+1).choose 2) := by
  have hD : r≤finrank K (Fin D → K) := by simpa only [Module.finrank_pi,Fintype.card_fin] using hr
  have h := vertical_pair_count (K := K) (V := Fin D → K) r hD
  simpa only [Module.finrank_pi,Fintype.card_fin,CenterStratum,DimSubspace] using h
omit [DecidableEq K] in
theorem canonicalLag_card_pos (D : ℕ) : (0 : ℝ)<Nat.card (Lagrangian (K := K) (V := Fin D → K)) := by
  exact lt_of_lt_of_le (by positivity) (lagrangian_card_lower (K := K) (V := Fin D → K))
omit [DecidableEq K] in
theorem canonicalStratumMass_pos (D r : ℕ) (hr : r≤D) : 0<canonicalStratumMass (K := K) D r := by
  have hl := subspace_count_lower (K := K) (V := Fin D → K) (D-r) (by simp)
  have hp : 0<(Nat.card (DimSubspace K (Fin D → K) (D-r)) : ℝ) := lt_of_lt_of_le (by positivity) hl
  unfold canonicalStratumMass
  rw [canonicalStratum_card D r hr,Nat.cast_mul,Nat.cast_pow]
  apply div_pos (mul_pos hp (by positivity))
  exact canonicalLag_card_pos (K := K) D
omit [DecidableEq K] in
theorem canonicalStratumMass_bound (D r : ℕ) (hr : r≤D) :
    canonicalStratumMass (K := K) D r*(Fintype.card K : ℝ)^((r+1).choose 2)≤2^(D-r) := by
  let n : ℝ := Nat.card (Lagrangian (K := K) (V := Fin D → K))
  have hn : 0<n := canonicalLag_card_pos (K := K) D
  have hc : (Nat.card (CenterStratum (K := K) (V := Fin D → K) r) : ℝ)=
      (Nat.card (DimSubspace K (Fin D → K) (D-r)) : ℝ)*(Fintype.card K : ℝ)^((D-r+1).choose 2) := by
    rw [canonicalStratum_card D r hr,Nat.cast_mul,Nat.cast_pow]
  have hu := subspace_count_upper (K := K) (V := Fin D → K) (D-r) (by simp)
  simp only [Module.finrank_pi,Fintype.card_fin,Nat.sub_sub_self hr] at hu
  have he : (D-r)*r+(D-r+1).choose 2+(r+1).choose 2=(D+1).choose 2 := by
    simpa only [Nat.mul_comm] using symmetric_nullity_exponent D r hr
  have hl : (Fintype.card K : ℝ)^((D+1).choose 2)≤n := by
    simpa only [Module.finrank_pi,Fintype.card_fin] using lagrangian_card_lower (K := K) (V := Fin D → K)
  change ((Nat.card (CenterStratum (K := K) (V := Fin D → K) r) : ℝ)/n)*_≤_
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hn).mpr
  rw [hc]
  calc
    _ ≤ (2^(D-r)*(Fintype.card K : ℝ)^((D-r)*r)) *
        (Fintype.card K : ℝ)^((D-r+1).choose 2)*(Fintype.card K : ℝ)^((r+1).choose 2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hu (by positivity)) (by positivity)
    _ = 2^(D-r)*(Fintype.card K : ℝ)^((D+1).choose 2) := by rw [mul_assoc,mul_assoc,←pow_add,←pow_add,←Nat.add_assoc,he]
    _ ≤ _ := mul_le_mul_of_nonneg_left hl (by positivity)
end Norm
theorem signed_normalization_eventually (r : ℕ) (hr : 0<r) {ξ : ℤ} (hξ : ξ=1 ∨ ξ= -1) :
    ∀ᶠ q : OddPrime in primeInfinity,
      canonicalStratumMass (K := ZMod q.val) (2*r) r /
        layerMass (ZMod q.val) (2*r) r ξ ≤ 4*2^r := by
  have h := (layerMass_tendsto (2*r) r hr (by omega) hξ).eventually (lt_mem_nhds (by norm_num : (1/4 : ℝ)<1/2))
  filter_upwards [h] with q hq
  have he : 2*r-r=r := by omega
  rw [he] at hq
  have hb := canonicalStratumMass_bound (K := ZMod q.val) (2*r) r (by omega)
  rw [he,ZMod.card] at hb
  have hp : (0:ℝ)<(q.val : ℝ)^((r+1).choose 2) := by exact pow_pos (by exact_mod_cast q.property.1.pos) _
  have hd : 0<layerMass (ZMod q.val) (2*r) r ξ := by nlinarith
  apply (div_le_iff₀ hd).mpr
  nlinarith [mul_pos hp hd, pow_pos (by norm_num : (0:ℝ)<2) r]
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module Classical Filter
open scoped BigOperators
section Face
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
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
end Means
section Bounds
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
end Bounds
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module Classical
open scoped BigOperators
section ChartFace
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
abbrev CanonicalLag (D : ℕ) := Lagrangian (K := K) (V := Fin D → K)
instance canonicalDual_finite (D : ℕ) : Finite (Module.Dual K (Fin D → K)) :=
  Finite.of_injective (fun f : Module.Dual K (Fin D → K) => (f : (Fin D → K) → K)) DFunLike.coe_injective
noncomputable def canonicalKernel (D r : ℕ) (A Y : CanonicalLag (K := K) D) : ℝ :=
  if finrank K ↥(A.val⊓Y.val)=r then (canonicalStratumMass (K := K) D r)⁻¹ else 0
omit [Fintype K] [DecidableEq K] in
theorem canonicalKernel_nonneg (D r : ℕ) (A Y : CanonicalLag (K := K) D) :
    0≤canonicalKernel D r A Y := by
  unfold canonicalKernel canonicalStratumMass
  split <;> positivity
omit [Fintype K] [DecidableEq K] in
theorem canonicalKernel_prod (D r : ℕ) (L : Fin 3 → CanonicalLag (K := K) D)
    (T : Finset (Fin 3)) (Y : CanonicalLag (K := K) D) :
    (∏ i∈T, canonicalKernel D r (L i) Y)=
      (if ∀ i∈T,finrank K ↥((L i).val⊓Y.val)=r then 1 else 0)*
        ((canonicalStratumMass (K := K) D r)⁻¹)^T.card := by
  by_cases h : ∀ i∈T,finrank K ↥((L i).val⊓Y.val)=r
  · rw [if_pos h,one_mul]
    calc
      _ = ∏ _i∈T, (canonicalStratumMass (K := K) D r)⁻¹ :=
        Finset.prod_congr rfl (fun i hi => by rw [canonicalKernel,if_pos (h i hi)])
      _ = _ := by rw [Finset.prod_const]
  · rw [if_neg h,zero_mul]
    push Not at h
    obtain ⟨i,hi,hh⟩ := h
    exact Finset.prod_eq_zero hi (by rw [canonicalKernel,if_neg hh])
omit [Fintype K] [DecidableEq K] in
theorem canonicalKernel_mean (D r : ℕ) [Fintype (CanonicalLag (K := K) D)]
    (L : Fin 3 → CanonicalLag (K := K) D) (T : Finset (Fin 3)) :
    uniformMean (fun Y => ∏ i∈T, canonicalKernel D r (L i) Y)=
      activeFaceDensity (canonicalSymplectic (K := K) (V := Fin D → K)) r
        (verticalLagrangian (K := K) (V := Fin D → K)) L T := by
  simp_rw [canonicalKernel_prod]
  rw [uniformMean_mul_right,uniformMean_indicator]
  unfold activeFaceDensity canonicalStratumMass
  simp only [inv_div,Nat.card_eq_fintype_card]
  rfl
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
section FaceGraph
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
end FaceGraph
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module Classical Filter
open scoped BigOperators
section Global
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
noncomputable def canonicalConfiguration (r : ℕ) (T : Fin 22 → Finset (Fin 3))
    (L : Fin 13 → CanonicalLag (K := K) (2*r)) : ℝ :=
  ∏ j,activeFaceDensity (canonicalSymplectic (K := K) (V := Fin (2*r) → K)) r
    (verticalLagrangian (K := K) (V := Fin (2*r) → K)) (L ∘ faceVertex j) (T j)
omit [Fintype K] [DecidableEq K] in
theorem canonicalConfiguration_nonneg (r : ℕ) (T : Fin 22 → Finset (Fin 3))
    (L : Fin 13 → CanonicalLag (K := K) (2*r)) : 0≤canonicalConfiguration r T L :=
  Finset.prod_nonneg (fun _ _ => activeFaceDensity_nonneg ..)
end Global
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module Classical Filter
open scoped BigOperators
section GlobalProduct
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
end GlobalProduct
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module Classical Filter
open scoped BigOperators
section GlobalBool
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
end GlobalBool
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

namespace OAI.SidorenkoCounterexample
open Classical Module Filter
section
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
noncomputable def umass (K : Type*) [Field K] [Fintype K] [DecidableEq K] (D r : ℕ) : ℝ :=
  uniformMean fun Z : SymMatrix K D => if Z.val.rank=r then 1 else 0
noncomputable def ukernel (r : ℕ) (Z : SymMatrix K (2*r)) : ℝ :=
  if Z.val.rank=r then (umass K (2*r) r)⁻¹ else 0
theorem uk_nonneg (r : ℕ) (Z : SymMatrix K (2*r)) : 0 ≤ ukernel r Z := by
  have hm : 0 ≤ umass K (2*r) r := uniformMean_nonneg (fun _ => by split <;> norm_num)
  unfold ukernel
  split <;> positivity
theorem layer_le_umass (r : ℕ) : layerMass K (2*r) r 1 ≤ umass K (2*r) r := by
  classical
  unfold umass layerMass
  simp only [uniformMean_indicator, Fintype.card_subtype]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Finset.card_le_card (show signedLayer K (2*r) r 1 ⊆ _ from fun z hz =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, ((mem_signedLayer _ _ _ _ _).mp hz).1⟩)
theorem uk_bound (r : ℕ) (A Y : SymMatrix K (2*r)) {C : ℝ}
    (hC : 0≤C) (hξ : canonicalStratumMass (K := K) (2*r) r / umass K (2*r) r≤C) :
    ukernel r (A-Y) ≤ C*canonicalKernel (2*r) r (matrixLagrangian A) (matrixLagrangian Y) := by
  have hm := canonicalStratumMass_pos (K := K) (2*r) r (by omega)
  unfold ukernel
  split_ifs with hAY
  · have hrank : (A-Y).val.rank=r := hAY
    have hdim := matrixLagrangian_pair_rank (2*r) A Y
    have hi : finrank K ↥((matrixLagrangian A).val⊓(matrixLagrangian Y).val)=r := by omega
    rw [canonicalKernel,if_pos hi]
    have he : (umass K (2*r) r)⁻¹ =
        (canonicalStratumMass (K := K) (2*r) r / umass K (2*r) r) *
          (canonicalStratumMass (K := K) (2*r) r)⁻¹ := by field_simp
    rw [he]
    exact mul_le_mul_of_nonneg_right hξ (inv_nonneg.mpr hm.le)
  · exact mul_nonneg hC (canonicalKernel_nonneg ..)

noncomputable def uface (r : ℕ) (T : Finset (Fin 3)) (X : Fin 3 → SymMatrix K (2*r)) :=
  uniformMean (fun Y => ∏ i∈T, ukernel r (X i-Y))
theorem uf_nonneg (r : ℕ) (T : Finset (Fin 3)) (X : Fin 3 → SymMatrix K (2*r)) : 0 ≤ uface r T X :=
  uniformMean_nonneg (fun _ => Finset.prod_nonneg (fun _ _ => uk_nonneg ..))
theorem uf_bound (r : ℕ) (T : Finset (Fin 3))
    (X : Fin 3 → SymMatrix K (2*r)) {C : ℝ} (hC : 1≤C)
    (hξ : canonicalStratumMass (K := K) (2*r) r / umass K (2*r) r≤C) :
    uface r T X ≤ C^3 * lagrangianConstant (2*r) *
      activeFaceDensity (canonicalSymplectic (K := K) (V := Fin (2*r) → K)) r
        (verticalLagrangian (K := K) (V := Fin (2*r) → K)) (matrixLagrangian ∘ X) T := by
  let :=  Fintype.ofFinite (CanonicalLag (K := K) (2*r))
  let : Nonempty (CanonicalLag (K := K) (2*r)) := ⟨verticalLagrangian⟩
  let f (Y : CanonicalLag (K := K) (2*r)) := ∏ i∈T, canonicalKernel (2*r) r (matrixLagrangian (X i)) Y
  have hf (Y) : 0≤f Y := Finset.prod_nonneg (fun i _ => canonicalKernel_nonneg ..)
  have hp (Y : SymMatrix K (2*r)) : (∏ i∈T,ukernel r (X i-Y))≤C^3*f (matrixLagrangian Y) := by
    calc
      _ ≤ ∏ i∈T,C*canonicalKernel (2*r) r (matrixLagrangian (X i)) (matrixLagrangian Y) :=
        Finset.prod_le_prod (fun _ _ => uk_nonneg ..)
          (fun i hi => uk_bound r (X i) Y (by linarith) hξ)
      _ = C^T.card*f (matrixLagrangian Y) := by rw [Finset.prod_mul_distrib,Finset.prod_const]
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hC (by have := Finset.card_le_univ T; simpa using this)) (hf _)
  have hi := uniformMean_injection (matrixLagrangian (K := K) (D := 2*r))
    (matrixLagrangian_injective (2*r)) f hf
  have he : ((Fintype.card (CanonicalLag (K := K) (2*r)) : ℝ)/Fintype.card (SymMatrix K (2*r)))=
      chartRatio (K := K) (2*r) := by rw [chartRatio,Nat.card_eq_fintype_card]
  rw [he] at hi
  change uface r T X ≤ _
  calc
    _ ≤ C^3*uniformMean (f ∘ matrixLagrangian) := by
      rw [←uniformMean_mul]; exact uniformMean_mono hp
    _ ≤ C^3*(chartRatio (K := K) (2*r)*uniformMean f) :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    _ ≤ C^3*(lagrangianConstant (2*r)*uniformMean f) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (chartRatio_bound (2*r)) (uniformMean_nonneg hf)) (by positivity)
    _ = _ := by rw [show uniformMean f=activeFaceDensity (canonicalSymplectic (K := K) (V := Fin (2*r) → K)) r
        (verticalLagrangian (K := K) (V := Fin (2*r) → K)) (matrixLagrangian ∘ X) T from canonicalKernel_mean (2*r) r _ T]; ring
theorem uc_bound (r : ℕ) (T : Fin 22 → Finset (Fin 3))
    (X : Fin 13 → SymMatrix K (2*r)) {C : ℝ} (hC : 1≤C)
    (hξ : canonicalStratumMass (K := K) (2*r) r / umass K (2*r) r≤C) :
    (∏ j, uface r (T j) (X ∘ faceVertex j)) ≤ (C^3*lagrangianConstant (2*r))^22 *
      canonicalConfiguration r T (matrixLagrangian ∘ X) := by
  calc
    _ ≤ ∏ j : Fin 22, (C^3*lagrangianConstant (2*r))*
      activeFaceDensity (canonicalSymplectic (K := K) (V := Fin (2*r) → K)) r
        (verticalLagrangian (K := K) (V := Fin (2*r) → K))
          (matrixLagrangian ∘ (X ∘ faceVertex j)) (T j) :=
      Finset.prod_le_prod (fun _ _ => uf_nonneg ..)
        (fun j _ => uf_bound r (T j) _ hC hξ)
    _ = _ := by rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin]; rfl

noncomputable def rawG (D r : ℕ) (T : Fin 22 → Finset (Fin 3))
    (P : Submodule K ((Fin D → K) × Module.Dual K (Fin D → K)) → Prop) : ℝ :=
  let L := {S // P S}
  letI := Fintype.ofFinite L
  let n := fun S : Submodule K ((Fin D → K) × Module.Dual K (Fin D → K)) => finrank K S
  let m := (Nat.card L:ℝ)/Nat.card {Y : L // n ((LinearMap.fst K _ _).ker ⊓ Y.1)=r}
  (∑ X : Fin 13 → L, if ∃ j k, n ((X (faceVertex j (slotLeft k))).1 ⊓ (X (faceVertex j (slotRight k))).1)≠0 then ∏ j, ((Nat.card {Y : L // ∀ k ∈ T j,n ((X (faceVertex j k)).1 ⊓ Y.1)=r}:ℝ)/Nat.card L*m^(T j).card) else 0)/(Nat.card L:ℝ)^13
abbrev explicitP (K : Type*) [Field K] (D : ℕ) (S : Submodule K ((Fin D → K) × Module.Dual K (Fin D → K))) :=
  ∀ x, x ∈ S ↔ ∀ y ∈ S, x.2 y.1 = y.2 x.1
theorem rawP_eq (D : ℕ) : explicitP K D = fun S => canonicalSymplectic.orthogonal S = S := by
  funext S; apply propext
  have hh (x) : x ∈ canonicalSymplectic.orthogonal S ↔ ∀ y ∈ S, x.2 y.1 = y.2 x.1 := by
    change (∀ y ∈ S, x.2 y.1 - y.2 x.1 = 0) ↔ _
    simp only [sub_eq_zero]
  exact ⟨fun h => Submodule.ext fun x => (hh x).trans (h x).symm, fun h x => (show x ∈ S ↔ x ∈ canonicalSymplectic.orthogonal S by rw [h]).trans (hh x)⟩
noncomputable def utail (r : ℕ) (T : Fin 22 → Finset (Fin 3)) :=
  uniformMean fun X : Fin 13 → SymMatrix K (2*r) => if ∃ j k, ((X (faceVertex j (slotLeft k)))-(X (faceVertex j (slotRight k)))).val.det=0 then ∏ j, uface r (T j) (X ∘ faceVertex j) else 0
theorem ut_bound (r : ℕ) (T : Fin 22 → Finset (Fin 3)) {C : ℝ} (hC : 1≤C)
    (hξ : canonicalStratumMass (K := K) (2*r) r / umass K (2*r) r ≤ C) :
    utail (K := K) r T ≤ ((C^3*lagrangianConstant (2*r))^22*lagrangianConstant (2*r)^13)*
      rawG (2*r) r T (explicitP K (2*r)) := by
  rw [rawP_eq]
  let := Fintype.ofFinite (CanonicalLag (K := K) (2*r))
  let : Nonempty (CanonicalLag (K := K) (2*r)) := ⟨verticalLagrangian⟩
  let f (L : Fin 13 → CanonicalLag (K := K) (2*r)) :=
    if ∃ j k, finrank K ↥((L (faceVertex j (slotLeft k))).val ⊓ (L (faceVertex j (slotRight k))).val) ≠ 0 then canonicalConfiguration r T L else 0
  have hf (L) : 0≤f L := by dsimp only [f]; split <;> simp only [canonicalConfiguration_nonneg,le_refl]
  have hj : Function.Injective (fun X : Fin 13 → SymMatrix K (2*r) => matrixLagrangian ∘ X) := by
    intro X Y h; funext i; exact matrixLagrangian_injective (2*r) (congrFun h i)
  have hi := uniformMean_injection (fun X : Fin 13 → SymMatrix K (2*r) => matrixLagrangian ∘ X) hj f hf
  have he : ((Fintype.card (Fin 13 → CanonicalLag (K := K) (2*r)) : ℝ)/
      Fintype.card (Fin 13 → SymMatrix K (2*r)))=(chartRatio (K := K) (2*r))^13 := by
    simp only [Fintype.card_fun,Fintype.card_fin,Nat.cast_pow,chartRatio,Nat.card_eq_fintype_card,div_pow]
  rw [he] at hi
  have hp (X : Fin 13 → SymMatrix K (2*r)) :
      (if ∃ j k, ((X (faceVertex j (slotLeft k)))-(X (faceVertex j (slotRight k)))).val.det=0 then ∏ j, uface r (T j) (X ∘ faceVertex j) else 0)≤
        (C^3*lagrangianConstant (2*r))^22*f (matrixLagrangian ∘ X) := by
    dsimp only [f]
    simp only [Function.comp_apply, ne_eq, matrixLagrangian_pair_zero, not_not]
    split <;> simp_all only [ite_true, ite_false, mul_zero, le_refl, uc_bound r T X hC hξ]
  have hC0 : 0≤(C^3*lagrangianConstant (2*r))^22 := by positivity
  calc
    _ ≤ (C^3*lagrangianConstant (2*r))^22*uniformMean (fun X => f (matrixLagrangian ∘ X)) := by
      rw [←uniformMean_mul]; exact uniformMean_mono hp
    _ ≤ (C^3*lagrangianConstant (2*r))^22*(chartRatio (K := K) (2*r)^13*uniformMean f) :=
      mul_le_mul_of_nonneg_left hi hC0
    _ ≤ (C^3*lagrangianConstant (2*r))^22*(lagrangianConstant (2*r)^13*uniformMean f) := by
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (chartRatio_nonneg (2*r)) (chartRatio_bound (2*r)) _) (uniformMean_nonneg hf)) hC0
    _ = _ := by rw [mul_assoc]; congr 2
                unfold uniformMean rawG
                rw [Fintype.card_fun,Fintype.card_fin,Nat.cast_pow, ←Nat.card_eq_fintype_card]
                have hh : Nat.card (SymplecticCenterStratum (canonicalSymplectic (K := K) (V := Fin (2*r) → K)) verticalLagrangian r) = Nat.card {Y : CanonicalLag (K := K) (2*r) // finrank K ↥((LinearMap.fst K _ _).ker ⊓ Y.val) = r} := by
                  apply Nat.card_congr
                  apply Equiv.subtypeEquivRight
                  intro Y
                  change (finrank K ↥(Y.val ⊓ (LinearMap.fst K _ _).ker) = r) ↔ _
                  rw [inf_comm]
                simp only [f, canonicalConfiguration, activeFaceDensity, hh]
                rfl
end
end OAI.SidorenkoCounterexample
namespace OAI.SidorenkoCounterexample
open scoped Classical
open Module Filter
noncomputable def rawM (d r : ℕ) (T : Fin 22 → Finset (Fin 3)) (q : OddPrime) :=
  let S := {A : Matrix (Fin d) (Fin d) (ZMod q.val) // A.IsSymm}
  uniformMean (fun X : Fin 13 → S => if ∃ j k, ((X (faceVertex j (slotLeft k))).val-(X (faceVertex j (slotRight k))).val).det=0 then ∏ j, uniformMean (fun Y : S => ∏ k ∈ T j, if ((X (faceVertex j k)).val-Y.val).rank=r then (uniformMean (fun Z : S => if Z.val.rank=r then (1:ℝ) else 0))⁻¹ else 0) else 0)
theorem umean_ext {A : Type*} {i j : Fintype A} {f g : A → ℝ} (h : ∀ a, f a = g a) : @uniformMean A i f = @uniformMean A j g := by
  cases Subsingleton.elim i j
  rw [funext h]
theorem rawM_eq (r : ℕ) (T : Fin 22 → Finset (Fin 3)) (q : OddPrime) : rawM (2*r) r T q = utail (K := ZMod q.val) r T := by
  apply umean_ext
  intro X
  split_ifs with h₁ h₂
  · apply Finset.prod_congr rfl
    intro j _
    apply umean_ext
    intro Y
    apply Finset.prod_congr rfl
    intro k _
    unfold ukernel
    split_ifs with h₃ h₄
    · congr 1
      apply umean_ext
      intro Z
      rfl
    · exfalso; apply_assumption; assumption
    · exfalso; apply_assumption; assumption
    · rfl
  · exfalso; apply_assumption; assumption
  · exfalso; apply_assumption; assumption
  · rfl
end OAI.SidorenkoCounterexample
open OAI.SidorenkoCounterexample Module Filter

set_option maxHeartbeats 3000000 in
theorem OMA.solution : OMA.R_SidorenkoConjecture_sidorenko_conjecture_graphon_R1_H1_R1_H1_R1_H1_R1_H1_R1_H2_R1.H3 := by
  intro d h4 hd h T
  change ∀ T, Tendsto (fun q : OddPrime => rawG d (d/2) T (explicitP (ZMod q.val) d)) primeInfinity (nhds 0) at h
  change Tendsto (rawM d (d/2) T) primeInfinity (nhds 0)
  obtain ⟨r,hr⟩ : ∃ r, d = 2*r := ⟨d/2, by omega⟩
  subst d
  have hr : 0 < r := by omega
  have he : 2*r/2 = r := by omega
  let C : ℝ := 4*2^r
  have hC : 1≤C := by dsimp [C]; have : 1≤(2:ℝ)^r := one_le_pow₀ (by norm_num); linarith
  have hG : Tendsto (fun q : OddPrime => rawG (2*r) r T (explicitP (ZMod q.val) (2*r))) primeInfinity (nhds 0) := by
    have hh := h T
    rw [he] at hh
    exact hh
  have ht := hG.const_mul ((C^3*lagrangianConstant (2*r))^22*lagrangianConstant (2*r)^13)
  simp only [mul_zero] at ht
  rw [he]
  simp_rw [show rawM (2*r) r T = fun q => utail (K := ZMod q.val) r T from funext (rawM_eq r T)]
  have hn (q : OddPrime) : 0 ≤ utail (K := ZMod q.val) r T := by
    apply uniformMean_nonneg
    intro X
    split
    · exact Finset.prod_nonneg (fun _ _ => uf_nonneg ..)
    · rfl
  apply squeeze_zero' (Eventually.of_forall hn) _ ht
  filter_upwards [signed_normalization_eventually r hr (ξ := 1) (Or.inl rfl)] with q hq
  apply ut_bound r T hC
  apply le_trans _ hq
  exact div_le_div_of_nonneg_left (canonicalStratumMass_pos (K := ZMod q.val) (2*r) r (by omega)).le
    (layerMass_pos _ _ hr (by omega) (by simpa only [ZMod.ringChar_zmod_n] using q.2.2) (Or.inl rfl)) (layer_le_umass _)

