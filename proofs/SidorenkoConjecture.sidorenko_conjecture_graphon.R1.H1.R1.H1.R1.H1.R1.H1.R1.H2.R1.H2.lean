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
 theorem T2x26 (k : ℕ) (hk : k ≤ finrank K V) :
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
 theorem radical_containment_card [Fintype K] [FiniteDimensional K V]
    (U : Submodule K V) :
    Nat.card {B : SymForm K V // U ≤ B.val.ker} =
      Fintype.card K ^ ((finrank K V - finrank K U + 1).choose 2) := by
  rw [Nat.card_congr (formRadicalEquiv U), symForm_card]
  congr 2
  have h := U.finrank_quotient_add_finrank
  omega
 theorem nullity_count_bound [Fintype K] [Finite V] (u : ℕ) :
    Nat.card {B : SymForm K V // u ≤ finrank K B.val.ker} ≤
      Nat.card (DimSubspace K V u) *
        Fintype.card K ^ ((finrank K V - u + 1).choose 2) := by
  classical
  let : Fintype (DimSubspace K V u) := Fintype.ofFinite _
  let f : (Σ U : DimSubspace K V u, {B : SymForm K V // U.val ≤ B.val.ker}) →
      {B : SymForm K V // u ≤ finrank K B.val.ker} := fun x =>
    ⟨x.2.val, by simpa only [x.1.property] using Submodule.finrank_mono x.2.property⟩
  have hf : Function.Surjective f := by
    intro B
    obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_finrank B.property
    let w : Fin u → V := fun i => (v i : V)
    have hw : LinearIndependent K w := hv.map' B.val.val.ker.subtype
      (Submodule.ker_subtype _)
    let U : DimSubspace K V u := ⟨Submodule.span K (Set.range w), by
      rw [finrank_span_eq_card hw, Fintype.card_fin]⟩
    have hU : U.val ≤ B.val.val.ker := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i,rfl⟩
      exact (v i).property
    exact ⟨⟨U,⟨B.val,hU⟩⟩, rfl⟩
  calc
    Nat.card {B : SymForm K V // u ≤ finrank K B.val.ker} ≤
        Nat.card (Σ U : DimSubspace K V u, {B : SymForm K V // U.val ≤ B.val.ker}) :=
      Nat.card_le_card_of_surjective f hf
    _ = _ := by
      rw [Nat.card_sigma]
      have hdim (U : DimSubspace K V u) : finrank K U.val = u := U.property
      simp only [radical_containment_card, hdim, Finset.sum_const,
        nsmul_eq_mul, Finset.card_univ, Nat.card_eq_fintype_card, Nat.cast_id]
 theorem symmetric_nullity_exponent (n u : ℕ) (hu : u ≤ n) :
    u*(n-u) + (n-u+1).choose 2 + (u+1).choose 2 = (n+1).choose 2 := by
  have h : ((u*(n-u) + (n-u+1).choose 2 + (u+1).choose 2 : ℕ) : ℚ) =
      ((n+1).choose 2 : ℚ) := by
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_choose_two, Nat.cast_one,
      Nat.cast_sub hu]
    ring
  exact_mod_cast h
 theorem symmetric_nullity_probability_bound [Fintype K] [Finite V]
    (u : ℕ) (hu : u ≤ finrank K V) :
    (Nat.card {B : SymForm K V // u ≤ finrank K B.val.ker} : ℝ) /
      Nat.card (SymForm K V) ≤ 2^u / (Fintype.card K : ℝ)^((u+1).choose 2) := by
  have hcount : (Nat.card {B : SymForm K V // u ≤ finrank K B.val.ker} : ℝ) ≤
      (Nat.card (DimSubspace K V u) : ℝ) *
        (Fintype.card K : ℝ)^((finrank K V-u+1).choose 2) := by
    exact_mod_cast nullity_count_bound (K := K) (V := V) u
  have hspace := T2x26 (K := K) (V := V) u hu
  have hq : (0 : ℝ) < Fintype.card K := by exact_mod_cast Fintype.card_pos (α := K)
  rw [symForm_card, Nat.cast_pow]
  apply (div_le_iff₀ (pow_pos hq _)).mpr
  calc
    (Nat.card {B : SymForm K V // u ≤ finrank K B.val.ker} : ℝ) ≤
        2^u * (Fintype.card K : ℝ)^(u*(finrank K V-u)) *
          (Fintype.card K : ℝ)^((finrank K V-u+1).choose 2) :=
      hcount.trans (mul_le_mul_of_nonneg_right hspace (pow_nonneg hq.le _))
    _ = 2^u / (Fintype.card K : ℝ)^((u+1).choose 2) *
        (Fintype.card K : ℝ)^((finrank K V+1).choose 2) := by
      rw [← symmetric_nullity_exponent (finrank K V) u hu]
      rw [pow_add, pow_add]
      field_simp
end FormCount
end SidorenkoCounterexample
end OAI
namespace OAI
namespace SidorenkoCounterexample
open Module
section LagrangianCharts
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
def T2x5 : LinearMap.BilinForm K (V × Module.Dual K V) where
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
    T2x5 p q = q.2 p.1 - p.2 q.1 := rfl
 theorem canonicalSymplectic_alt : (T2x5 (K := K) (V := V)).IsAlt := by
  intro p
  simp
 theorem T2x35 :
    (T2x5 (K := K) (V := V)).Nondegenerate := by
  have hleft : ∀ p : V × Module.Dual K V,
      (∀ q, T2x5 p q = 0) → p = 0 := by
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
  T2x5.orthogonal L = L}
 theorem lagrangian_finrank (L : Lagrangian (K := K) (V := V)) :
    finrank K L.val = finrank K V := by
  have h := LinearMap.BilinForm.finrank_orthogonal T2x35 L.val
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
    formGraph U B.val ≤ T2x5.orthogonal (formGraph U B.val) := by
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
noncomputable def T2x28 (U : Submodule K V) (B : SymForm K U) :
    Lagrangian (K := K) (V := V) :=
  ⟨formGraph U B.val, by
    apply (Submodule.eq_of_le_of_finrank_eq (formGraph_isotropic U B) _).symm
    rw [formGraph_finrank, LinearMap.BilinForm.finrank_orthogonal T2x35,
      Module.finrank_prod, Subspace.dual_finrank_eq, formGraph_finrank, Nat.add_sub_cancel_left]⟩
 theorem graphLagrangian_form_injective (U : Submodule K V) :
    Function.Injective (T2x28 (K := K) U) := by
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
    T2x5 p q = 0 := by
  have hq' : q ∈ T2x5.orthogonal L.val := L.property.symm ▸ hq
  exact hq' p hp
 theorem graphLagrangian_surjective :
    Function.Surjective (fun S : Σ U : Submodule K V, SymForm K U => T2x28 S.1 S.2) := by
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
  Equiv.ofBijective (fun S => T2x28 S.1 S.2) ⟨by
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
def T2x29 : E →ₗ[K] Module.Dual K L := ω.flip.compl₂ L.subtype
 theorem symplecticProjection_surjective (hω : ω.Nondegenerate) :
    Function.Surjective (T2x29 ω L) := by
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
 theorem T2x80 (hL : ω.orthogonal L = L) :
    (T2x29 ω L).ker = L := by
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
      (T2x29 ω L).comp s = LinearMap.id ∧
      ∀ f g, ω (s f) (s g) = 0 := by
  obtain ⟨s,hs⟩ := (T2x29 ω L).exists_rightInverse_of_surjective
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
 theorem T2x21 (h2 : (2 : K) ≠ 0) (ha : ω.IsAlt)
    (hω : ω.Nondegenerate) (hL : ω.orthogonal L = L) :
    ∃ e : (L × Module.Dual K L) ≃ₗ[K] E,
      (∀ l : L, e (l,0) = l.val) ∧
      ∀ x y, ω (e x) (e y) = T2x5 x y := by
  obtain ⟨s,hs,hiso⟩ := exists_isotropic_section ω L h2 ha hω hL
  let e : (L × Module.Dual K L) →ₗ[K] E :=
    L.subtype.comp (LinearMap.fst K L (Module.Dual K L)) +
    s.comp (LinearMap.snd K L (Module.Dual K L))
  have hp (l : L) : T2x29 ω L l.val = 0 := by
    exact (T2x80 ω L hL).ge l.property
  have heproj (x : L × Module.Dual K L) : T2x29 ω L (e x) = x.2 := by
    change T2x29 ω L (x.1.val + s x.2) = x.2
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
    let f := T2x29 ω L x
    have hz : x - s f ∈ L := by
      apply (T2x80 ω L hL).le
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
 theorem T2x6 (hω : ω.Nondegenerate)
    (hL : ω.orthogonal L = L) : 2 * finrank K L = finrank K E := by
  have h := LinearMap.BilinForm.finrank_orthogonal hω L
  rw [hL] at h
  have hle := Submodule.finrank_le L
  omega
 theorem lagrangian_transitivity (h2 : (2 : K) ≠ 0) (ha : ω.IsAlt)
    (hω : ω.Nondegenerate) (hL : ω.orthogonal L = L)
    (M : Submodule K E) (hM : ω.orthogonal M = M) :
    ∃ e : E ≃ₗ[K] E, (∀ x y, ω (e x) (e y) = ω x y) ∧ L.map e.toLinearMap = M := by
  obtain ⟨eL,hEL,hωL⟩ := T2x21 ω L h2 ha hω hL
  obtain ⟨eM,hEM,hωM⟩ := T2x21 ω M h2 ha hω hM
  have hdim : finrank K L = finrank K M := by
    have h1 := T2x6 ω L hω hL
    have h2 := T2x6 ω M hω hM
    omega
  let f : L ≃ₗ[K] M := LinearEquiv.ofFinrankEq L M hdim
  let c : (L × Module.Dual K L) ≃ₗ[K] (M × Module.Dual K M) :=
    f.prodCongr f.symm.dualMap
  have hc (x y : L × Module.Dual K L) :
      T2x5 (c x) (c y) = T2x5 x y := by
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
 theorem T2x61 (e : E ≃ₗ[K] E)
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
noncomputable def T2x45 (e : E ≃ₗ[K] E)
    (he : ∀ x y, ω (e x) (e y) = ω x y) :
    {U : Submodule K E // ω.orthogonal U = U} ≃
    {U : Submodule K E // ω.orthogonal U = U} :=
  (Submodule.orderIsoMapComap e).toEquiv.subtypeEquiv (by
    intro U
    change ω.orthogonal U = U ↔ ω.orthogonal (U.map e.toLinearMap) = U.map e.toLinearMap
    rw [T2x61 ω e he]
    exact (Submodule.orderIsoMapComap e).injective.eq_iff.symm)
end NormalCoordinates
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section PairCounts
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
def T2x63 : Submodule K (V × Module.Dual K V) :=
  (LinearMap.fst K V (Module.Dual K V)).ker
omit [FiniteDimensional K V] in
 theorem verticalSpace_graph : T2x63 (K := K) (V := V) = formGraph ⊥ 0 := by
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
  ⟨T2x63, by
    rw [verticalSpace_graph]
    exact (T2x28 ⊥ ⟨0, LinearMap.BilinForm.isSymm_zero⟩).property⟩
noncomputable def graphVerticalIntersectionEquiv (U : Submodule K V)
    (B : LinearMap.BilinForm K U) :
    U.dualAnnihilator ≃ₗ[K] ↥(formGraph U B ⊓ T2x63 (K := K) (V := V)) where
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
    finrank K ↥(formGraph U B ⊓ T2x63 (K := K) (V := V)) = finrank K V - finrank K U := by
  rw [← (graphVerticalIntersectionEquiv U B).finrank_eq]
  have h := Subspace.finrank_add_finrank_dualAnnihilator_eq U
  omega
noncomputable def pairStratumEquiv (h : ℕ) (hh : h ≤ finrank K V) :
    (Σ U : {U : Submodule K V // finrank K U = finrank K V-h}, SymForm K U.val) ≃
    {L : Lagrangian (K := K) (V := V) // finrank K ↥(L.val ⊓ T2x63 (K := K) (V := V)) = h} := by
  classical
  let e : (Σ U : {U : Submodule K V // finrank K U = finrank K V-h}, SymForm K U.val) →
      Lagrangian (K := K) (V := V) := fun S => T2x28 S.1.val S.2
  have he (S) : finrank K ↥((e S).val ⊓ T2x63 (K := K) (V := V)) = h := by
    exact (graph_vertical_intersection_finrank S.1.val S.2.val).trans (by
      rw [S.1.property, Nat.sub_sub_self hh])
  refine Equiv.ofBijective (fun S => ⟨e S,he S⟩) ⟨?_, ?_⟩
  · rintro ⟨⟨U,hU⟩,B⟩ ⟨⟨W,hW⟩,C⟩ hEq
    have h : T2x28 U B = T2x28 W C := congrArg Subtype.val hEq
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
          finrank K ↥(L.val ⊓ T2x63 (K := K) (V := V))) hUB
        exact heq.trans hL
      have hle := Submodule.finrank_le U
      omega
    refine ⟨⟨⟨U,hU⟩,B⟩, Subtype.ext hUB⟩
 theorem vertical_pair_count [Fintype K] [Finite V] (h : ℕ) (hh : h ≤ finrank K V) :
    Nat.card {L : Lagrangian (K := K) (V := V) // finrank K ↥(L.val ⊓ T2x63 (K := K) (V := V)) = h} =
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
    (he : ∀ x y, T2x5 (e x) (e y) = T2x5 x y)
    (hAB : A.val.map e.toLinearMap = B.val) (h : ℕ) :
    Nat.card {L : Lagrangian (K := K) (V := V) // finrank K ↥(L.val ⊓ A.val) = h} =
    Nat.card {L : Lagrangian (K := K) (V := V) // finrank K ↥(L.val ⊓ B.val) = h} := by
  let f := T2x45 T2x5 e he
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
  obtain ⟨e,he,hAe⟩ := lagrangian_transitivity T2x5 A.val h2
    canonicalSymplectic_alt T2x35 A.property
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
 theorem linear_functional_descend (f : E →ₗ[K] V) (g : E →ₗ[K] K)
    (hk : f.ker ≤ g.ker) : ∃ h : V →ₗ[K] K, h.comp f = g := by
  obtain ⟨p,hp⟩ := f.range.subtype.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr f.range.subtype_injective)
  let e := f.quotKerEquivRange
  let a : V →ₗ[K] E ⧸ f.ker := e.symm.toLinearMap.comp p
  have he (x : E) : a (f x) = f.ker.mkQ x := by
    apply e.injective
    change e (e.symm (p (f x))) = e (f.ker.mkQ x)
    rw [e.apply_symm_apply]
    exact LinearMap.congr_fun hp (f.rangeRestrict x)
  refine ⟨(f.ker.liftQ g hk).comp a, ?_⟩
  ext x
  change f.ker.liftQ g hk (a (f x)) = g x
  rw [he]
  rfl
 theorem linear_functional_glue (U W : Submodule K V) (f : U →ₗ[K] K) (g : W →ₗ[K] K)
    (hfg : ∀ x : ↥(U ⊓ W), f (Submodule.inclusion inf_le_left x) =
      g (Submodule.inclusion inf_le_right x)) :
    ∃ h : V →ₗ[K] K, h.comp U.subtype = f ∧ h.comp W.subtype = g := by
  let a : U × W →ₗ[K] V := U.subtype.comp (LinearMap.fst K U W) +
    W.subtype.comp (LinearMap.snd K U W)
  let b : U × W →ₗ[K] K := f.comp (LinearMap.fst K U W) + g.comp (LinearMap.snd K U W)
  have hab : a.ker ≤ b.ker := by
    rintro x hx
    have hh : x.1.val + x.2.val = 0 := hx
    have he : x.1.val = -x.2.val := eq_neg_of_add_eq_zero_left hh
    let s : ↥(U ⊓ W) := ⟨x.1.val,x.1.property,he ▸ W.neg_mem x.2.property⟩
    have h₁ : Submodule.inclusion (show U ⊓ W ≤ U from inf_le_left) s = x.1 := rfl
    have h₂ : Submodule.inclusion (show U ⊓ W ≤ W from inf_le_right) s = -x.2 := Subtype.ext he
    have hf := hfg s
    rw [h₁,h₂,map_neg] at hf
    change f x.1 + g x.2 = 0
    rw [hf,neg_add_cancel]
  obtain ⟨h,hh⟩ := linear_functional_descend a b hab
  refine ⟨h,?_,?_⟩ <;> ext x
  · have he := LinearMap.congr_fun hh (x,0)
    simpa [a,b] using he
  · have he := LinearMap.congr_fun hh (0,x)
    simpa [a,b] using he
end LinearGlue
section PairLift
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable (U W : Submodule K V) (B : LinearMap.BilinForm K U) (C : LinearMap.BilinForm K W)
def graphDifference : LinearMap.BilinForm K ↥(U ⊓ W) :=
  B.compl₁₂ (Submodule.inclusion inf_le_left) (Submodule.inclusion inf_le_left) -
  C.compl₁₂ (Submodule.inclusion inf_le_right) (Submodule.inclusion inf_le_right)
def graphPairProjection : ↥(formGraph U B ⊓ formGraph W C) →ₗ[K] ↥(graphDifference U W B C).ker where
  toFun p := ⟨⟨p.val.1,by
    obtain ⟨u,hu,_⟩ := p.property.1
    obtain ⟨w,hw,_⟩ := p.property.2
    exact ⟨hu ▸ u.property,hw ▸ w.property⟩⟩,by
    apply LinearMap.mem_ker.mpr
    ext z
    obtain ⟨u,hu,hf⟩ := p.property.1
    obtain ⟨w,hw,hg⟩ := p.property.2
    have e₁ : (Submodule.inclusion inf_le_left : ↥(U ⊓ W) →ₗ[K] U) ⟨p.val.1,by
      exact ⟨hu ▸ u.property,hw ▸ w.property⟩⟩ = u := Subtype.ext hu.symm
    have e₂ : (Submodule.inclusion inf_le_right : ↥(U ⊓ W) →ₗ[K] W) ⟨p.val.1,by
      exact ⟨hu ▸ u.property,hw ▸ w.property⟩⟩ = w := Subtype.ext hw.symm
    change B _ _ - C _ _ = 0
    rw [e₁,e₂]
    have h₁ := LinearMap.congr_fun hf (Submodule.inclusion inf_le_left z)
    have h₂ := LinearMap.congr_fun hg (Submodule.inclusion inf_le_right z)
    exact sub_eq_zero.mpr (h₁.symm.trans h₂)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
 theorem graphPairProjection_surjective : Function.Surjective (graphPairProjection U W B C) := by
  rintro ⟨x,hx⟩
  have hc (z : ↥(U ⊓ W)) : B (Submodule.inclusion inf_le_left x) (Submodule.inclusion inf_le_left z) =
      C (Submodule.inclusion inf_le_right x) (Submodule.inclusion inf_le_right z) := by
    have h := LinearMap.congr_fun (LinearMap.mem_ker.mp hx) z
    exact sub_eq_zero.mp h
  obtain ⟨f,hf,hg⟩ := linear_functional_glue U W (B (Submodule.inclusion inf_le_left x))
    (C (Submodule.inclusion inf_le_right x)) hc
  refine ⟨⟨(x.val,f),⟨⟨Submodule.inclusion inf_le_left x,rfl,hf⟩,
    ⟨Submodule.inclusion inf_le_right x,rfl,hg⟩⟩⟩,rfl⟩
noncomputable def graphPairKernelEquiv : (U ⊔ W).dualAnnihilator ≃ₗ[K]
    (graphPairProjection U W B C).ker where
  toFun f := ⟨⟨(0,f.val),⟨⟨0,rfl,by
    ext x
    change f.val x.val = B 0 x
    rw [map_zero,LinearMap.zero_apply]
    exact (Submodule.mem_dualAnnihilator (W := U ⊔ W) f.val).mp f.property x.val ((show U ≤ U ⊔ W from le_sup_left) x.property)⟩,
    ⟨0,rfl,by
    ext x
    change f.val x.val = C 0 x
    rw [map_zero,LinearMap.zero_apply]
    exact (Submodule.mem_dualAnnihilator (W := U ⊔ W) f.val).mp f.property x.val ((show W ≤ U ⊔ W from le_sup_right) x.property)⟩⟩⟩,rfl⟩
  invFun p := ⟨p.val.val.2, by
    apply (Submodule.mem_dualAnnihilator (W := U ⊔ W) p.val.val.2).mpr
    have hzero : p.val.val.1 = 0 := congrArg (fun z : (graphDifference U W B C).ker => z.val.val) p.property
    obtain ⟨u,hu,hf⟩ := p.val.property.1
    obtain ⟨w,hw,hg⟩ := p.val.property.2
    have hu0 : u = 0 := Subtype.ext (hu.trans hzero)
    have hw0 : w = 0 := Subtype.ext (hw.trans hzero)
    intro x hx
    obtain ⟨y,hy,z,hz,rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add]
    have h₁ := LinearMap.congr_fun hf ⟨y,hy⟩
    have h₂ := LinearMap.congr_fun hg ⟨z,hz⟩
    simp only [hu0,hw0,map_zero,LinearMap.zero_apply,LinearMap.comp_apply,Submodule.subtype_apply] at h₁ h₂
    rw [h₁,h₂,add_zero]⟩
  left_inv _ := rfl
  right_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext (congrArg (fun z : (graphDifference U W B C).ker => z.val.val) p.property).symm rfl
  map_add' _ _ := by apply Subtype.ext; apply Subtype.ext; simp
  map_smul' _ _ := by apply Subtype.ext; apply Subtype.ext; simp
 theorem T2x43 [FiniteDimensional K V] :
    finrank K ↥(formGraph U B ⊓ formGraph W C) =
      finrank K ↥(U.dualAnnihilator ⊓ W.dualAnnihilator) + finrank K (graphDifference U W B C).ker := by
  have h := LinearMap.finrank_range_add_finrank_ker (K := K)
    (V := ↥(formGraph U B ⊓ formGraph W C)) (V₂ := ↥(graphDifference U W B C).ker)
    (graphPairProjection U W B C)
  rw [LinearMap.range_eq_top.mpr (graphPairProjection_surjective U W B C),finrank_top] at h
  rw [←(graphPairKernelEquiv U W B C).finrank_eq] at h
  rw [Submodule.dualAnnihilator_sup_eq] at h
  omega
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
 theorem surjective_linear_probability (f : U →ₗ[K] W)
    (hf : Function.Surjective f) (P : W → Prop) :
    (Nat.card {x : U // P (f x)} : ℝ) / Nat.card U =
      (Nat.card {y : W // P y} : ℝ) / Nat.card W := by
  rw [surjective_linear_preimage_card f hf P, surjective_linear_card f hf]
  have hk : (Nat.card f.ker : ℝ) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := f.ker)).ne'
  push_cast
  exact mul_div_mul_right _ _ hk
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
def glueCross (U W : Submodule K V) (B : LinearMap.BilinForm K U)
    (C : LinearMap.BilinForm K W)
    (p : U →ₗ[K] ↥(U ⊓ W)) (q : W →ₗ[K] ↥(U ⊓ W)) :
    U →ₗ[K] W →ₗ[K] K :=
  B.compl₂ ((Submodule.inclusion inf_le_left).comp q) +
  LinearMap.comp C ((Submodule.inclusion inf_le_right).comp p) -
  (B.compl₁₂ (Submodule.inclusion inf_le_left) (Submodule.inclusion inf_le_left)).compl₁₂ p q
variable (U W : Submodule K V) (B : LinearMap.BilinForm K U) (C : LinearMap.BilinForm K W)
variable (p : U →ₗ[K] ↥(U ⊓ W)) (q : W →ₗ[K] ↥(U ⊓ W))
 theorem glueCross_left (hp : p.comp (Submodule.inclusion inf_le_left) = LinearMap.id)
    (s : ↥(U ⊓ W)) (w : W) :
    glueCross U W B C p q (Submodule.inclusion inf_le_left s) w =
      C (Submodule.inclusion inf_le_right s) w := by
  have hps := LinearMap.congr_fun hp s
  change p (Submodule.inclusion inf_le_left s) = s at hps
  change B (Submodule.inclusion inf_le_left s) (Submodule.inclusion inf_le_left (q w)) +
    C (Submodule.inclusion inf_le_right (p (Submodule.inclusion inf_le_left s))) w -
    B (Submodule.inclusion inf_le_left (p (Submodule.inclusion inf_le_left s)))
      (Submodule.inclusion inf_le_left (q w)) = _
  rw [hps]
  ring
 theorem glueCross_right (hq : q.comp (Submodule.inclusion inf_le_right) = LinearMap.id)
    (hBC : B.compl₁₂ (Submodule.inclusion inf_le_left) (Submodule.inclusion inf_le_left) =
      C.compl₁₂ (Submodule.inclusion inf_le_right) (Submodule.inclusion inf_le_right))
    (u : U) (s : ↥(U ⊓ W)) :
    glueCross U W B C p q u (Submodule.inclusion inf_le_right s) =
      B u (Submodule.inclusion inf_le_left s) := by
  have hqs := LinearMap.congr_fun hq s
  change q (Submodule.inclusion inf_le_right s) = s at hqs
  have hc := LinearMap.congr_fun (LinearMap.congr_fun hBC (p u)) s
  change B (Submodule.inclusion inf_le_left (p u)) (Submodule.inclusion inf_le_left s) =
    C (Submodule.inclusion inf_le_right (p u)) (Submodule.inclusion inf_le_right s) at hc
  change B u (Submodule.inclusion inf_le_left (q (Submodule.inclusion inf_le_right s))) +
    C (Submodule.inclusion inf_le_right (p u)) (Submodule.inclusion inf_le_right s) -
    B (Submodule.inclusion inf_le_left (p u))
      (Submodule.inclusion inf_le_left (q (Submodule.inclusion inf_le_right s))) = _
  rw [hqs]
  rw [hc]
  ring
 theorem symmetric_form_glue (hB : B.IsSymm) (hC : C.IsSymm)
    (hBC : B.compl₁₂ (Submodule.inclusion inf_le_left) (Submodule.inclusion inf_le_left) =
      C.compl₁₂ (Submodule.inclusion inf_le_right) (Submodule.inclusion inf_le_right)) :
    ∃ F : LinearMap.BilinForm K V, F.IsSymm ∧
      F.compl₁₂ U.subtype U.subtype = B ∧ F.compl₁₂ W.subtype W.subtype = C := by
  let i : ↥(U ⊓ W) →ₗ[K] U := Submodule.inclusion inf_le_left
  let j : ↥(U ⊓ W) →ₗ[K] W := Submodule.inclusion inf_le_right
  have hi : Function.Injective i := by
    intro x y h
    exact Subtype.ext (congrArg (fun u : U => u.val) h)
  have hj : Function.Injective j := by
    intro x y h
    exact Subtype.ext (congrArg (fun w : W => w.val) h)
  obtain ⟨p,hp⟩ := i.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hi)
  obtain ⟨q,hq⟩ := j.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hj)
  let A := glueCross U W B C p q
  let fst := LinearMap.fst K U W
  let snd := LinearMap.snd K U W
  let D : LinearMap.BilinForm K (U × W) :=
    B.compl₁₂ fst fst + C.compl₁₂ snd snd +
    A.compl₁₂ fst snd + A.flip.compl₁₂ snd fst
  have hD (x y : U × W) : D x y = B x.1 y.1 + C x.2 y.2 + A x.1 y.2 + A y.1 x.2 := rfl
  have hDs : D.IsSymm := by
    constructor
    intro x y
    rw [hD,hD,hB.eq x.1 y.1,hC.eq x.2 y.2]
    ring
  let f : U × W →ₗ[K] V := U.subtype.comp fst + W.subtype.comp snd
  have hf (x : U × W) : f x = x.1.val + x.2.val := rfl
  have hk : f.ker ≤ D.ker := by
    intro x hx
    have hsum : x.1.val + x.2.val = 0 := hx
    have hxW : x.1.val ∈ W := by
      have hh : x.1.val = -x.2.val := eq_neg_of_add_eq_zero_left hsum
      rw [hh]
      exact W.neg_mem x.2.property
    let s : ↥(U ⊓ W) := ⟨x.1.val, x.1.property, hxW⟩
    have hxs : x = (i s, -j s) := by
      apply Prod.ext
      · rfl
      · apply Subtype.ext
        exact (eq_neg_of_add_eq_zero_right hsum)
    apply LinearMap.mem_ker.mpr
    apply LinearMap.ext
    intro y
    change D x y = 0
    rw [hxs,hD]
    change B (i s) y.1 + C (-j s) y.2 + A (i s) y.2 + A y.1 (-j s) = 0
    simp only [map_neg, LinearMap.neg_apply]
    rw [glueCross_left U W B C p q hp,
      glueCross_right U W B C p q hq hBC, hB.eq]
    ring
  obtain ⟨F,hFs,hDF⟩ := symmetric_form_descend f D hDs hk
  refine ⟨F,hFs,?_,?_⟩
  · apply LinearMap.ext
    intro u
    apply LinearMap.ext
    intro v
    have h := LinearMap.congr_fun (LinearMap.congr_fun hDF (u,0)) (v,0)
    change F (f (u,0)) (f (v,0)) = D (u,0) (v,0) at h
    simpa [hf,hD] using h
  · apply LinearMap.ext
    intro u
    apply LinearMap.ext
    intro v
    have h := LinearMap.congr_fun (LinearMap.congr_fun hDF (0,u)) (0,v)
    change F (f (0,u)) (f (0,v)) = D (0,u) (0,v) at h
    simpa [hf,hD] using h
theorem symmetric_form_glue_pointwise (hB : B.IsSymm) (hC : C.IsSymm)
    (hc : ∀ (x y : V) (hxU : x ∈ U) (hxW : x ∈ W) (hyU : y ∈ U) (hyW : y ∈ W),
      B ⟨x,hxU⟩ ⟨y,hyU⟩ = C ⟨x,hxW⟩ ⟨y,hyW⟩) :
    ∃ F : LinearMap.BilinForm K V, F.IsSymm ∧
      F.compl₁₂ U.subtype U.subtype = B ∧ F.compl₁₂ W.subtype W.subtype = C := by
  apply symmetric_form_glue U W B C hB hC
  ext x y
  exact hc x y x.property.1 x.property.2 y.property.1 y.property.2
end FormGluing
section CyclicDifference
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
theorem cyclic_difference_exists (A₀ A₁ A₂ : Submodule K V)
    (D₀ : LinearMap.BilinForm K ↥(A₁ ⊓ A₂))
    (D₁ : LinearMap.BilinForm K ↥(A₂ ⊓ A₀))
    (D₂ : LinearMap.BilinForm K ↥(A₀ ⊓ A₁))
    (hD₀ : D₀.IsSymm) (hD₁ : D₁.IsSymm) (hD₂ : D₂.IsSymm)
    (hc : ∀ (x y : V) (hx₀ : x ∈ A₀) (hx₁ : x ∈ A₁) (hx₂ : x ∈ A₂)
      (hy₀ : y ∈ A₀) (hy₁ : y ∈ A₁) (hy₂ : y ∈ A₂),
      D₀ ⟨x,hx₁,hx₂⟩ ⟨y,hy₁,hy₂⟩ + D₁ ⟨x,hx₂,hx₀⟩ ⟨y,hy₂,hy₀⟩ +
        D₂ ⟨x,hx₀,hx₁⟩ ⟨y,hy₀,hy₁⟩ = 0) :
    ∃ F G : LinearMap.BilinForm K V, F.IsSymm ∧ G.IsSymm ∧
      (F-G).compl₁₂ (A₁ ⊓ A₂).subtype (A₁ ⊓ A₂).subtype = D₀ ∧
      G.compl₁₂ (A₂ ⊓ A₀).subtype (A₂ ⊓ A₀).subtype = D₁ ∧
      (-F).compl₁₂ (A₀ ⊓ A₁).subtype (A₀ ⊓ A₁).subtype = D₂ := by
  let S := (A₁ ⊓ A₂) ⊓ (A₀ ⊓ A₁)
  let i : S →ₗ[K] ↥(A₁ ⊓ A₂) := Submodule.inclusion inf_le_left
  let j : S →ₗ[K] ↥(A₀ ⊓ A₁) := Submodule.inclusion inf_le_right
  let T : LinearMap.BilinForm K S := (-D₂).compl₁₂ j j
  have hT : T.IsSymm := by
    constructor
    intro x y
    change -(D₂ (j x) (j y)) = -(D₂ (j y) (j x))
    rw [hD₂.eq]
  have hi : i.ker = ⊥ := LinearMap.ker_eq_bot.mpr (by
    intro x y h
    exact Subtype.ext (congrArg (fun u : ↥(A₁ ⊓ A₂) => u.val) h))
  obtain ⟨H,hHs,hH⟩ := symmetric_form_descend i T hT (by rw [hi]; exact bot_le)
  have hHval (x y : V) (hx₀ : x ∈ A₀) (hx₁ : x ∈ A₁) (hx₂ : x ∈ A₂)
      (hy₀ : y ∈ A₀) (hy₁ : y ∈ A₁) (hy₂ : y ∈ A₂) :
      H ⟨x,hx₁,hx₂⟩ ⟨y,hy₁,hy₂⟩ = -D₂ ⟨x,hx₀,hx₁⟩ ⟨y,hy₀,hy₁⟩ :=
    LinearMap.congr_fun (LinearMap.congr_fun hH ⟨x,⟨hx₁,hx₂⟩,hx₀,hx₁⟩)
      ⟨y,⟨hy₁,hy₂⟩,hy₀,hy₁⟩
  have hneg : (-D₂).IsSymm := by
    constructor
    intro x y
    change -(D₂ x y) = -(D₂ y x)
    rw [hD₂.eq]
  obtain ⟨F,hFs,hF₀,hF₂⟩ := symmetric_form_glue_pointwise
    (A₁ ⊓ A₂) (A₀ ⊓ A₁) H (-D₂) hHs hneg (by
      intro x y hx hy hx' hy'
      exact hHval x y hy.1 hx.1 hx.2 hy'.1 hx'.1 hx'.2)
  have hsub : (H-D₀).IsSymm := by
    constructor
    intro x y
    change H x y - D₀ x y = H y x - D₀ y x
    rw [hHs.eq,hD₀.eq]
  obtain ⟨G,hGs,hG₀,hG₁⟩ := symmetric_form_glue_pointwise
    (A₁ ⊓ A₂) (A₂ ⊓ A₀) (H-D₀) D₁ hsub hD₁ (by
      intro x y hx hy hx' hy'
      change H ⟨x,hx⟩ ⟨y,hx'⟩ - D₀ ⟨x,hx⟩ ⟨y,hx'⟩ = D₁ ⟨x,hy⟩ ⟨y,hy'⟩
      rw [hHval x y hy.2 hx.1 hx.2 hy'.2 hx'.1 hx'.2]
      have h := hc x y hy.2 hx.1 hx.2 hy'.2 hx'.1 hx'.2
      linear_combination -h)
  refine ⟨F,G,hFs,hGs,?_,hG₁,?_⟩
  · ext x y
    have hf := LinearMap.congr_fun (LinearMap.congr_fun hF₀ x) y
    have hg := LinearMap.congr_fun (LinearMap.congr_fun hG₀ x) y
    change F x y = H x y at hf
    change G x y = H x y - D₀ x y at hg
    change F x y - G x y = D₀ x y
    rw [hf,hg]
    ring
  · ext x y
    have hf := LinearMap.congr_fun (LinearMap.congr_fun hF₂ x) y
    change F x y = -D₂ x y at hf
    change -(F x y) = D₂ x y
    rw [hf,neg_neg]
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
abbrev DifferenceTargets := SymForm K ↥(A₁ ⊓ A₂) ×
  (SymForm K ↥(A₂ ⊓ A₀) × SymForm K ↥(A₀ ⊓ A₁))
abbrev CommonSpace := ↥((A₀ ⊓ A₁) ⊓ A₂)
def commonInclusion₀ : CommonSpace A₀ A₁ A₂ →ₗ[K] ↥(A₁ ⊓ A₂) :=
  Submodule.inclusion (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
def commonInclusion₁ : CommonSpace A₀ A₁ A₂ →ₗ[K] ↥(A₂ ⊓ A₀) :=
  Submodule.inclusion (le_inf inf_le_right (inf_le_left.trans inf_le_left))
def commonInclusion₂ : CommonSpace A₀ A₁ A₂ →ₗ[K] ↥(A₀ ⊓ A₁) :=
  Submodule.inclusion inf_le_left
noncomputable def cyclicDifferenceMap : (Fin 3 → SymForm K V) →ₗ[K]
    DifferenceTargets A₀ A₁ A₂ :=
  let p (i : Fin 3) : (Fin 3 → SymForm K V) →ₗ[K] SymForm K V := LinearMap.proj i
  ((symFormPull (A₁ ⊓ A₂).subtype).comp (p 1 - p 2)).prod
    (((symFormPull (A₂ ⊓ A₀).subtype).comp (p 2 - p 0)).prod
      ((symFormPull (A₀ ⊓ A₁).subtype).comp (p 0 - p 1)))
noncomputable def differenceConstraint : DifferenceTargets A₀ A₁ A₂ →ₗ[K]
    SymForm K (CommonSpace A₀ A₁ A₂) :=
  (symFormPull (commonInclusion₀ A₀ A₁ A₂)).comp (LinearMap.fst K _ _) +
  (symFormPull (commonInclusion₁ A₀ A₁ A₂)).comp
    ((LinearMap.fst K _ _).comp (LinearMap.snd K _ _)) +
  (symFormPull (commonInclusion₂ A₀ A₁ A₂)).comp
    ((LinearMap.snd K _ _).comp (LinearMap.snd K _ _))
theorem differenceConstraint_surjective :
    Function.Surjective (differenceConstraint A₀ A₁ A₂) := by
  intro B
  have hi : Function.Injective (commonInclusion₀ A₀ A₁ A₂) := by
    intro x y h
    exact Subtype.ext (congrArg (fun z : ↥(A₁ ⊓ A₂) => z.val) h)
  obtain ⟨C,hC⟩ := symFormPull_surjective (commonInclusion₀ A₀ A₁ A₂) hi B
  refine ⟨(C,0,0), ?_⟩
  change symFormPull (commonInclusion₀ A₀ A₁ A₂) C +
    symFormPull (commonInclusion₁ A₀ A₁ A₂) 0 +
    symFormPull (commonInclusion₂ A₀ A₁ A₂) 0 = B
  simp [hC]
theorem cyclicDifference_range :
    (cyclicDifferenceMap A₀ A₁ A₂).range = (differenceConstraint A₀ A₁ A₂).ker := by
  apply le_antisymm
  · rintro D ⟨F,rfl⟩
    apply LinearMap.mem_ker.mpr
    apply Subtype.ext
    ext x y
    change (F 1).val x y - (F 2).val x y +
      ((F 2).val x y - (F 0).val x y) +
      ((F 0).val x y - (F 1).val x y) = 0
    ring
  · intro D hD
    have hcon := LinearMap.mem_ker.mp hD
    obtain ⟨F,G,hFs,hGs,hFG,hG,hF⟩ := cyclic_difference_exists A₀ A₁ A₂
      D.1.val D.2.1.val D.2.2.val D.1.property D.2.1.property D.2.2.property (by
        intro x y hx₀ hx₁ hx₂ hy₀ hy₁ hy₂
        exact congrArg (fun B : SymForm K (CommonSpace A₀ A₁ A₂) =>
          B.val ⟨x,⟨hx₀,hx₁⟩,hx₂⟩ ⟨y,⟨hy₀,hy₁⟩,hy₂⟩) hcon)
    refine ⟨![0,⟨F,hFs⟩,⟨G,hGs⟩], ?_⟩
    apply Prod.ext
    · apply Subtype.ext
      exact hFG
    · apply Prod.ext
      · apply Subtype.ext
        ext x y
        change G x y - 0 = D.2.1.val x y
        rw [sub_zero]
        exact LinearMap.congr_fun (LinearMap.congr_fun hG x) y
      · apply Subtype.ext
        ext x y
        change 0 - F x y = D.2.2.val x y
        rw [zero_sub]
        exact LinearMap.congr_fun (LinearMap.congr_fun hF x) y
end PlantedDifference
end SidorenkoCounterexample
namespace SidorenkoCounterexample
section ConstraintDensity
variable {K U W X : Type*} [Field K] [AddCommGroup U] [Module K U]
  [AddCommGroup W] [Module K W] [AddCommGroup X] [Module K X]
  [Finite U] [Finite W] [Finite X]
theorem linear_constraint_probability_bound (f : U →ₗ[K] W) (c : W →ₗ[K] X)
    (hc : Function.Surjective c) (hfc : f.range = c.ker) (P : W → Prop) :
    (Nat.card {u : U // P (f u)} : ℝ) / Nat.card U ≤
      (Nat.card X : ℝ) * (Nat.card {w : W // P w} : ℝ) / Nat.card W := by
  have hprob := surjective_linear_probability f.rangeRestrict (by rintro ⟨w,u,rfl⟩; exact ⟨u,rfl⟩)
    (fun w : f.range => P w.val)
  have hinj : Function.Injective (fun w : {w : f.range // P w.val} =>
      (⟨w.val.val,w.property⟩ : {w : W // P w})) := by
    intro a b h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : {w : W // P w} => z.val) h
  have hcard := Nat.card_le_card_of_injective _ hinj
  have htotal := surjective_linear_card c hc
  have hx : (Nat.card X : ℝ) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := X)).ne'
  have hk : (Nat.card c.ker : ℝ) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := c.ker)).ne'
  calc
    (Nat.card {u : U // P (f u)} : ℝ) / Nat.card U =
        (Nat.card {w : f.range // P w.val} : ℝ) / Nat.card f.range := hprob
    _ ≤ (Nat.card {w : W // P w} : ℝ) / Nat.card f.range :=
      div_le_div_of_nonneg_right (by exact_mod_cast hcard) (Nat.cast_nonneg _)
    _ = (Nat.card X : ℝ) * (Nat.card {w : W // P w} : ℝ) / Nat.card W := by
      rw [hfc,htotal]
      push_cast
      field_simp
end ConstraintDensity
section ProductDensity
variable {U W X : Type*} [Finite U] [Finite W] [Finite X]
def triplePredicateEquiv (P : U → Prop) (Q : W → Prop) (R : X → Prop) :
    {z : U × (W × X) // P z.1 ∧ Q z.2.1 ∧ R z.2.2} ≃
      {u : U // P u} × ({w : W // Q w} × {x : X // R x}) where
  toFun z := (⟨z.val.1,z.property.1⟩,⟨z.val.2.1,z.property.2.1⟩,⟨z.val.2.2,z.property.2.2⟩)
  invFun z := ⟨(z.1.val,z.2.1.val,z.2.2.val),z.1.property,z.2.1.property,z.2.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
omit [Finite U] [Finite W] [Finite X] in
theorem triple_predicate_probability (P : U → Prop) (Q : W → Prop) (R : X → Prop) :
    (Nat.card {z : U × (W × X) // P z.1 ∧ Q z.2.1 ∧ R z.2.2} : ℝ) /
      Nat.card (U × (W × X)) =
    ((Nat.card {u : U // P u} : ℝ) / Nat.card U) *
      ((Nat.card {w : W // Q w} : ℝ) / Nat.card W) *
      ((Nat.card {x : X // R x} : ℝ) / Nat.card X) := by
  rw [Nat.card_congr (triplePredicateEquiv P Q R)]
  simp only [Nat.card_prod, Nat.cast_mul]
  ring
end ProductDensity
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section OriginalDifferences
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable (A₀ A₁ A₂ : Submodule K V)
abbrev OriginalForms := SymForm K A₀ × (SymForm K A₁ × SymForm K A₂)
noncomputable def ambientRestrictions : (Fin 3 → SymForm K V) →ₗ[K]
    OriginalForms A₀ A₁ A₂ :=
  let p (i : Fin 3) : (Fin 3 → SymForm K V) →ₗ[K] SymForm K V := LinearMap.proj i
  ((symFormPull A₀.subtype).comp (p 0)).prod
    (((symFormPull A₁.subtype).comp (p 1)).prod ((symFormPull A₂.subtype).comp (p 2)))
noncomputable def T2x33 : OriginalForms A₀ A₁ A₂ →ₗ[K]
    DifferenceTargets A₀ A₁ A₂ :=
  let p₀ : OriginalForms A₀ A₁ A₂ →ₗ[K] SymForm K A₀ := LinearMap.fst K _ _
  let p₁ : OriginalForms A₀ A₁ A₂ →ₗ[K] SymForm K A₁ :=
    (LinearMap.fst K _ _).comp (LinearMap.snd K _ _)
  let p₂ : OriginalForms A₀ A₁ A₂ →ₗ[K] SymForm K A₂ :=
    (LinearMap.snd K _ _).comp (LinearMap.snd K _ _)
  ((symFormPull (Submodule.inclusion inf_le_left : ↥(A₁ ⊓ A₂) →ₗ[K] A₁)).comp p₁ -
    (symFormPull (Submodule.inclusion inf_le_right : ↥(A₁ ⊓ A₂) →ₗ[K] A₂)).comp p₂).prod
  (((symFormPull (Submodule.inclusion inf_le_left : ↥(A₂ ⊓ A₀) →ₗ[K] A₂)).comp p₂ -
    (symFormPull (Submodule.inclusion inf_le_right : ↥(A₂ ⊓ A₀) →ₗ[K] A₀)).comp p₀).prod
   ((symFormPull (Submodule.inclusion inf_le_left : ↥(A₀ ⊓ A₁) →ₗ[K] A₀)).comp p₀ -
    (symFormPull (Submodule.inclusion inf_le_right : ↥(A₀ ⊓ A₁) →ₗ[K] A₁)).comp p₁))
theorem ambientRestrictions_surjective : Function.Surjective (ambientRestrictions A₀ A₁ A₂) := by
  intro B
  obtain ⟨F₀,h₀⟩ := symFormPull_surjective A₀.subtype A₀.subtype_injective B.1
  obtain ⟨F₁,h₁⟩ := symFormPull_surjective A₁.subtype A₁.subtype_injective B.2.1
  obtain ⟨F₂,h₂⟩ := symFormPull_surjective A₂.subtype A₂.subtype_injective B.2.2
  refine ⟨![F₀,F₁,F₂], ?_⟩
  change (symFormPull A₀.subtype F₀,symFormPull A₁.subtype F₁,symFormPull A₂.subtype F₂) = B
  rw [h₀,h₁,h₂]
theorem originalDifference_comp_restriction :
    (T2x33 A₀ A₁ A₂).comp (ambientRestrictions A₀ A₁ A₂) =
      cyclicDifferenceMap A₀ A₁ A₂ := by
  apply LinearMap.ext
  intro F
  apply Prod.ext
  · apply Subtype.ext
    ext x y
    rfl
  · apply Prod.ext
    · apply Subtype.ext
      ext x y
      rfl
    · apply Subtype.ext
      ext x y
      rfl
theorem originalCyclicDifference_range :
    (T2x33 A₀ A₁ A₂).range = (differenceConstraint A₀ A₁ A₂).ker := by
  have h : (cyclicDifferenceMap A₀ A₁ A₂).range =
      (T2x33 A₀ A₁ A₂).range := by
    rw [← originalDifference_comp_restriction, LinearMap.range_comp,
      LinearMap.range_eq_top.mpr (ambientRestrictions_surjective A₀ A₁ A₂), Submodule.map_top]
  exact h.symm.trans (cyclicDifference_range A₀ A₁ A₂)
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
 theorem containment_quotient_finrank (S U : Submodule K V) (hS : S ≤ U) :
    finrank K (U.map S.mkQ) + finrank K S = finrank K U := by
  have h := LinearMap.finrank_range_add_finrank_ker (S.mkQ.comp U.subtype)
  rw [LinearMap.range_comp,Submodule.range_subtype,LinearMap.ker_comp,Submodule.ker_mkQ] at h
  rw [(Submodule.comapSubtypeEquivOfLe hS).finrank_eq] at h
  exact h
noncomputable def containingSubspaceEquiv (S : Submodule K V) (r : ℕ) (hr : finrank K S ≤ r) :
    {U : DimSubspace K V r // S ≤ U.val} ≃ DimSubspace K (V ⧸ S) (r-finrank K S) where
  toFun U := ⟨U.val.val.map S.mkQ,by
    have h := containment_quotient_finrank S U.val.val U.property
    rw [U.val.property] at h
    omega⟩
  invFun Q := ⟨⟨Q.val.comap S.mkQ,by
    have h := containment_quotient_finrank S (Q.val.comap S.mkQ) (Submodule.le_comap_mkQ _ _)
    rw [Submodule.map_comap_eq_self (by simp),Q.property] at h
    omega⟩,Submodule.le_comap_mkQ _ _⟩
  left_inv U := by
    apply Subtype.ext
    apply Subtype.ext
    change (U.val.val.map S.mkQ).comap S.mkQ = U.val.val
    simp only [Submodule.comap_map_mkQ, sup_eq_right.mpr U.property]
  right_inv Q := by
    apply Subtype.ext
    exact (S.comapMkQRelIso).symm_apply_apply Q.val
variable [Fintype K] [Finite V]
 omit [Finite V] in
 theorem containingSubspace_card_bounds (S : Submodule K V) (r : ℕ)
    (hr : finrank K S ≤ r) (hrD : r ≤ finrank K V) :
    (Fintype.card K : ℝ)^((r-finrank K S)*(finrank K V-r)) ≤
        Nat.card {U : DimSubspace K V r // S ≤ U.val} ∧
    (Nat.card {U : DimSubspace K V r // S ≤ U.val} : ℝ) ≤
        2^r*(Fintype.card K : ℝ)^((r-finrank K S)*(finrank K V-r)) := by
  let : Finite (V ⧸ S) := Module.finite_of_finite K
  have hD := S.finrank_quotient_add_finrank
  have hle : r-finrank K S ≤ finrank K (V ⧸ S) := by omega
  have he : finrank K (V ⧸ S)-(r-finrank K S) = finrank K V-r := by omega
  rw [Nat.card_congr (containingSubspaceEquiv S r hr)]
  constructor
  · simpa only [he] using (subspace_count_lower (K := K) (V := V ⧸ S) (r-finrank K S) hle)
  · have h := T2x26 (K := K) (V := V ⧸ S) (r-finrank K S) hle
    rw [he] at h
    exact h.trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (Nat.sub_le r _)) (by positivity))
end ContainingSubspaces
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section TripleSubspaces
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
abbrev T2x46 (r p₀ p₁ p₂ : ℕ) :=
  {R : DimSubspace K V r × DimSubspace K V r × DimSubspace K V r //
    (R.1.val ⊓ R.2.1.val) ⊓ R.2.2.val = ⊥ ∧
    finrank K ↥(R.1.val ⊓ R.2.1.val) = p₀ ∧
    finrank K ↥(R.1.val ⊓ R.2.2.val) = p₁ ∧
    finrank K ↥(R.2.1.val ⊓ R.2.2.val) = p₂}
abbrev T2x50 (p₀ p₁ p₂ : ℕ) :=
  {P : DimSubspace K V p₀ × DimSubspace K V p₁ × DimSubspace K V p₂ //
    Disjoint P.1.val P.2.1.val ∧ Disjoint P.1.val P.2.2.val ∧ Disjoint P.2.1.val P.2.2.val}
abbrev T2x79 {p₀ p₁ p₂ : ℕ} (r : ℕ) (P : T2x50 (K := K) (V := V) p₀ p₁ p₂) :=
  {R : DimSubspace K V r // P.val.1.val ⊔ P.val.2.1.val ≤ R.val} ×
  {R : DimSubspace K V r // P.val.1.val ⊔ P.val.2.2.val ≤ R.val} ×
  {R : DimSubspace K V r // P.val.2.1.val ⊔ P.val.2.2.val ≤ R.val}
 theorem triple_pairwise_disjoint (L M N : Submodule K V) (hc : (L ⊓ M) ⊓ N = ⊥) :
    Disjoint (L ⊓ M) (L ⊓ N) ∧ Disjoint (L ⊓ M) (M ⊓ N) ∧ Disjoint (L ⊓ N) (M ⊓ N) := by
  refine ⟨disjoint_iff.mpr (le_antisymm ?_ bot_le),disjoint_iff.mpr (le_antisymm ?_ bot_le),
    disjoint_iff.mpr (le_antisymm ?_ bot_le)⟩
  · intro x hx
    exact hc.le ⟨hx.1,hx.2.2⟩
  · intro x hx
    exact hc.le ⟨hx.1,hx.2.2⟩
  · intro x hx
    exact hc.le ⟨⟨hx.1.1,hx.2.1⟩,hx.1.2⟩
noncomputable def subspaceProfile_to_config {r p₀ p₁ p₂ : ℕ}
    (R : T2x46 (K := K) (V := V) r p₀ p₁ p₂) :
    Σ P : T2x50 (K := K) (V := V) p₀ p₁ p₂, T2x79 r P :=
  ⟨⟨(⟨R.val.1.val ⊓ R.val.2.1.val,R.property.2.1⟩,
    ⟨R.val.1.val ⊓ R.val.2.2.val,R.property.2.2.1⟩,
    ⟨R.val.2.1.val ⊓ R.val.2.2.val,R.property.2.2.2⟩),
    triple_pairwise_disjoint _ _ _ R.property.1⟩,
   ⟨R.val.1,sup_le inf_le_left inf_le_left⟩,
   ⟨R.val.2.1,sup_le inf_le_right inf_le_left⟩,
   ⟨R.val.2.2,sup_le inf_le_right inf_le_right⟩⟩
 theorem subspaceProfile_to_config_injective (r p₀ p₁ p₂ : ℕ) :
    Function.Injective (subspaceProfile_to_config (K := K) (V := V) (r := r) (p₀ := p₀) (p₁ := p₁) (p₂ := p₂)) := by
  intro R S h
  let f : (Σ P : T2x50 (K := K) (V := V) p₀ p₁ p₂, T2x79 r P) →
      DimSubspace K V r × DimSubspace K V r × DimSubspace K V r := fun p => (p.2.1.val,p.2.2.1.val,p.2.2.2.val)
  exact Subtype.ext (congrArg f h)
variable [FiniteDimensional K V]
 theorem disjoint_sup_finrank (U W : Submodule K V) (h : Disjoint U W) :
    finrank K ↥(U ⊔ W) = finrank K U + finrank K W := by
  have hh := Submodule.finrank_sup_add_finrank_inf_eq U W
  rw [h.eq_bot,finrank_bot,add_zero] at hh
  exact hh
variable [Fintype K]
 theorem pairSubspaceConfig_card_upper (p₀ p₁ p₂ : ℕ)
    (h₀ : p₀ ≤ finrank K V) (h₁ : p₁ ≤ finrank K V) (h₂ : p₂ ≤ finrank K V) :
    (Nat.card (T2x50 (K := K) (V := V) p₀ p₁ p₂) : ℝ) ≤
      2^(p₀+p₁+p₂)*(Fintype.card K : ℝ)^(p₀*(finrank K V-p₀)+p₁*(finrank K V-p₁)+p₂*(finrank K V-p₂)) := by
  let : Finite V := Module.finite_of_finite K
  have hc : Nat.card (T2x50 (K := K) (V := V) p₀ p₁ p₂) ≤
      Nat.card (DimSubspace K V p₀ × DimSubspace K V p₁ × DimSubspace K V p₂) :=
    Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  have hh : (Nat.card (T2x50 (K := K) (V := V) p₀ p₁ p₂) : ℝ) ≤
      (Nat.card (DimSubspace K V p₀) : ℝ) * Nat.card (DimSubspace K V p₁) * Nat.card (DimSubspace K V p₂) := by
    rw [Nat.card_prod, Nat.card_prod] at hc
    exact_mod_cast (hc.trans_eq (Nat.mul_assoc _ _ _).symm)
  calc
    _ ≤ _ := hh
    _ ≤ (2^p₀*(Fintype.card K : ℝ)^(p₀*(finrank K V-p₀))) *
      (2^p₁*(Fintype.card K : ℝ)^(p₁*(finrank K V-p₁))) *
      (2^p₂*(Fintype.card K : ℝ)^(p₂*(finrank K V-p₂))) := by
      exact mul_le_mul (mul_le_mul (T2x26 p₀ h₀) (T2x26 p₁ h₁)
        (by positivity) (by positivity)) (T2x26 p₂ h₂) (by positivity) (by positivity)
    _ = _ := by simp only [pow_add]; ring
 theorem subspaceTripleCompletion_card_upper {p₀ p₁ p₂ : ℕ} (r : ℕ)
    (P : T2x50 (K := K) (V := V) p₀ p₁ p₂)
    (hr : r ≤ finrank K V) (h₀ : p₀+p₁ ≤ r) (h₁ : p₀+p₂ ≤ r) (h₂ : p₁+p₂ ≤ r) :
    (Nat.card (T2x79 r P) : ℝ) ≤
      2^(3*r)*(Fintype.card K : ℝ)^((r-(p₀+p₁))*(finrank K V-r)+
        (r-(p₀+p₂))*(finrank K V-r)+(r-(p₁+p₂))*(finrank K V-r)) := by
  let : Finite V := Module.finite_of_finite K
  have d₀ : finrank K ↥(P.val.1.val ⊔ P.val.2.1.val) = p₀+p₁ := by
    rw [disjoint_sup_finrank _ _ P.property.1,P.val.1.property,P.val.2.1.property]
  have d₁ : finrank K ↥(P.val.1.val ⊔ P.val.2.2.val) = p₀+p₂ := by
    rw [disjoint_sup_finrank _ _ P.property.2.1,P.val.1.property,P.val.2.2.property]
  have d₂ : finrank K ↥(P.val.2.1.val ⊔ P.val.2.2.val) = p₁+p₂ := by
    rw [disjoint_sup_finrank _ _ P.property.2.2,P.val.2.1.property,P.val.2.2.property]
  have a₀ := (containingSubspace_card_bounds (P.val.1.val ⊔ P.val.2.1.val) r (by omega) hr).2
  have a₁ := (containingSubspace_card_bounds (P.val.1.val ⊔ P.val.2.2.val) r (by omega) hr).2
  have a₂ := (containingSubspace_card_bounds (P.val.2.1.val ⊔ P.val.2.2.val) r (by omega) hr).2
  rw [d₀] at a₀
  rw [d₁] at a₁
  rw [d₂] at a₂
  have h := mul_le_mul (mul_le_mul a₀ a₁ (by positivity) (by positivity)) a₂ (by positivity) (by positivity)
  simpa only [T2x79,Nat.card_prod,Nat.cast_mul,pow_add,pow_mul,show 3*r=r+r+r by omega,
    mul_assoc,mul_left_comm,mul_comm] using h
noncomputable def T2x38 (n r p₀ p₁ p₂ : ℕ) : ℕ :=
  p₀*(n-p₀)+p₁*(n-p₁)+p₂*(n-p₂) +
  ((r-(p₀+p₁))*(n-r)+(r-(p₀+p₂))*(n-r)+(r-(p₁+p₂))*(n-r))
 theorem subspaceTripleProfile_card_upper (r p₀ p₁ p₂ : ℕ)
    (hr : r ≤ finrank K V) (h₀ : p₀+p₁ ≤ r) (h₁ : p₀+p₂ ≤ r) (h₂ : p₁+p₂ ≤ r) :
    (Nat.card (T2x46 (K := K) (V := V) r p₀ p₁ p₂) : ℝ) ≤
      2^(p₀+p₁+p₂+3*r)*(Fintype.card K : ℝ)^(T2x38 (finrank K V) r p₀ p₁ p₂) := by
  classical
  let : Finite V := Module.finite_of_finite K
  let := Fintype.ofFinite (T2x50 (K := K) (V := V) p₀ p₁ p₂)
  have hc : (Nat.card (T2x46 (K := K) (V := V) r p₀ p₁ p₂) : ℝ) ≤
      Nat.card (Σ P : T2x50 (K := K) (V := V) p₀ p₁ p₂, T2x79 r P) := by
    exact_mod_cast Nat.card_le_card_of_injective _ (subspaceProfile_to_config_injective (K := K) (V := V) r p₀ p₁ p₂)
  let e := (r-(p₀+p₁))*(finrank K V-r)+(r-(p₀+p₂))*(finrank K V-r)+(r-(p₁+p₂))*(finrank K V-r)
  calc
    _ ≤ _ := hc
    _ = ∑ P : T2x50 (K := K) (V := V) p₀ p₁ p₂, (Nat.card (T2x79 r P) : ℝ) := by
      rw [Nat.card_sigma,Nat.cast_sum]
    _ ≤ ∑ _P : T2x50 (K := K) (V := V) p₀ p₁ p₂, 2^(3*r)*(Fintype.card K : ℝ)^e :=
      Finset.sum_le_sum (fun P _ => subspaceTripleCompletion_card_upper r P hr h₀ h₁ h₂)
    _ = (Nat.card (T2x50 (K := K) (V := V) p₀ p₁ p₂) : ℝ)*(2^(3*r)*(Fintype.card K : ℝ)^e) := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card]
    _ ≤ (2^(p₀+p₁+p₂)*(Fintype.card K : ℝ)^(p₀*(finrank K V-p₀)+p₁*(finrank K V-p₁)+p₂*(finrank K V-p₂))) *
      (2^(3*r)*(Fintype.card K : ℝ)^e) := mul_le_mul_of_nonneg_right
        (pairSubspaceConfig_card_upper p₀ p₁ p₂ (by omega) (by omega) (by omega)) (by positivity)
    _ = _ := by dsimp [e,T2x38]; simp only [pow_add]; ring
end TripleSubspaces
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section SpanCount
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
noncomputable def restrictDimSubspace (Z : Submodule K V) {r : ℕ} (R : DimSubspace K V r) (h : R.val ≤ Z) :
    DimSubspace K Z r :=
  ⟨R.val.comap Z.subtype, (Submodule.comapSubtypeEquivOfLe h).finrank_eq.trans R.property⟩
noncomputable def restrictTripleProfile (Z : Submodule K V) {r p₀ p₁ p₂ : ℕ}
    (R : T2x46 (K := K) (V := V) r p₀ p₁ p₂)
    (h : R.val.1.val ⊔ R.val.2.1.val ⊔ R.val.2.2.val ≤ Z) :
    T2x46 (K := K) (V := Z) r p₀ p₁ p₂ := by
  have h₀ : R.val.1.val ≤ Z := le_trans (le_trans le_sup_left le_sup_left) h
  have h₁ : R.val.2.1.val ≤ Z := le_trans (le_trans le_sup_right le_sup_left) h
  have h₂ : R.val.2.2.val ≤ Z := le_trans le_sup_right h
  refine ⟨(restrictDimSubspace Z R.val.1 h₀, restrictDimSubspace Z R.val.2.1 h₁,
    restrictDimSubspace Z R.val.2.2 h₂), ?_, ?_, ?_, ?_⟩
  · change (R.val.1.val.comap Z.subtype ⊓ R.val.2.1.val.comap Z.subtype) ⊓ R.val.2.2.val.comap Z.subtype = ⊥
    rw [←Submodule.comap_inf,←Submodule.comap_inf,R.property.1,Submodule.comap_bot]
    exact LinearMap.ker_eq_bot.mpr Z.injective_subtype
  · change finrank K ↥(R.val.1.val.comap Z.subtype ⊓ R.val.2.1.val.comap Z.subtype) = p₀
    rw [←Submodule.comap_inf,(Submodule.comapSubtypeEquivOfLe (inf_le_left.trans h₀) :
      (R.val.1.val ⊓ R.val.2.1.val).comap Z.subtype ≃ₗ[K] ↥(R.val.1.val ⊓ R.val.2.1.val)).finrank_eq]
    exact R.property.2.1
  · change finrank K ↥(R.val.1.val.comap Z.subtype ⊓ R.val.2.2.val.comap Z.subtype) = p₁
    rw [←Submodule.comap_inf,(Submodule.comapSubtypeEquivOfLe (inf_le_left.trans h₀) :
      (R.val.1.val ⊓ R.val.2.2.val).comap Z.subtype ≃ₗ[K] ↥(R.val.1.val ⊓ R.val.2.2.val)).finrank_eq]
    exact R.property.2.2.1
  · change finrank K ↥(R.val.2.1.val.comap Z.subtype ⊓ R.val.2.2.val.comap Z.subtype) = p₂
    rw [←Submodule.comap_inf,(Submodule.comapSubtypeEquivOfLe (inf_le_left.trans h₁) :
      (R.val.2.1.val ⊓ R.val.2.2.val).comap Z.subtype ≃ₗ[K] ↥(R.val.2.1.val ⊓ R.val.2.2.val)).finrank_eq]
    exact R.property.2.2.2
abbrev T2x9 (r p₀ p₁ p₂ n : ℕ) :=
  {R : T2x46 (K := K) (V := V) r p₀ p₁ p₂ //
    finrank K ↥(R.val.1.val ⊔ R.val.2.1.val ⊔ R.val.2.2.val) = n}
noncomputable def spanProfileInjection (r p₀ p₁ p₂ n : ℕ)
    (R : T2x9 (K := K) (V := V) r p₀ p₁ p₂ n) :
    Σ Z : DimSubspace K V n, T2x46 (K := K) (V := Z.val) r p₀ p₁ p₂ :=
  ⟨⟨R.val.val.1.val ⊔ R.val.val.2.1.val ⊔ R.val.val.2.2.val,R.property⟩,
   restrictTripleProfile _ R.val le_rfl⟩
 omit [FiniteDimensional K V] in
 theorem spanProfileInjection_injective (r p₀ p₁ p₂ n : ℕ) :
    Function.Injective (spanProfileInjection (K := K) (V := V) r p₀ p₁ p₂ n) := by
  intro R S h
  let recover : (Σ Z : DimSubspace K V n, T2x46 (K := K) (V := Z.val) r p₀ p₁ p₂) →
      Submodule K V × Submodule K V × Submodule K V := fun ZR =>
    (ZR.2.val.1.val.map ZR.1.val.subtype,ZR.2.val.2.1.val.map ZR.1.val.subtype,
      ZR.2.val.2.2.val.map ZR.1.val.subtype)
  have he (T : T2x9 (K := K) (V := V) r p₀ p₁ p₂ n) :
      recover (spanProfileInjection r p₀ p₁ p₂ n T) =
      (T.val.val.1.val,T.val.val.2.1.val,T.val.val.2.2.val) := by
    let Z := T.val.val.1.val ⊔ T.val.val.2.1.val ⊔ T.val.val.2.2.val
    change ((T.val.val.1.val.comap Z.subtype).map Z.subtype,
      (T.val.val.2.1.val.comap Z.subtype).map Z.subtype,
      (T.val.val.2.2.val.comap Z.subtype).map Z.subtype) = _
    rw [Submodule.map_comap_subtype,Submodule.map_comap_subtype,Submodule.map_comap_subtype]
    rw [inf_eq_right.mpr (le_trans le_sup_left le_sup_left),
      inf_eq_right.mpr (le_trans le_sup_right le_sup_left),inf_eq_right.mpr le_sup_right]
  have hh := congrArg recover h
  rw [he,he] at hh
  apply Subtype.ext
  apply Subtype.ext
  exact Prod.ext (Subtype.ext (congrArg Prod.fst hh))
    (Prod.ext (Subtype.ext (congrArg (fun z => z.2.1) hh)) (Subtype.ext (congrArg (fun z => z.2.2) hh)))
variable [Fintype K]
 theorem subspaceTripleSpanProfile_card_upper (r p₀ p₁ p₂ n : ℕ)
    (hn : n ≤ finrank K V) (hr : r ≤ n)
    (h₀ : p₀+p₁ ≤ r) (h₁ : p₀+p₂ ≤ r) (h₂ : p₁+p₂ ≤ r) :
    (Nat.card (T2x9 (K := K) (V := V) r p₀ p₁ p₂ n) : ℝ) ≤
      2^(n+p₀+p₁+p₂+3*r)*(Fintype.card K : ℝ)^
        (n*(finrank K V-n)+T2x38 n r p₀ p₁ p₂) := by
  classical
  let : Finite V := Module.finite_of_finite K
  let := Fintype.ofFinite (DimSubspace K V n)
  have hc : (Nat.card (T2x9 (K := K) (V := V) r p₀ p₁ p₂ n) : ℝ) ≤
      Nat.card (Σ Z : DimSubspace K V n, T2x46 (K := K) (V := Z.val) r p₀ p₁ p₂) := by
    exact_mod_cast Nat.card_le_card_of_injective _ (spanProfileInjection_injective (K := K) (V := V) r p₀ p₁ p₂ n)
  calc
    _ ≤ _ := hc
    _ = ∑ Z : DimSubspace K V n, (Nat.card (T2x46 (K := K) (V := Z.val) r p₀ p₁ p₂) : ℝ) := by
      rw [Nat.card_sigma,Nat.cast_sum]
    _ ≤ ∑ _Z : DimSubspace K V n, 2^(p₀+p₁+p₂+3*r)*(Fintype.card K : ℝ)^(T2x38 n r p₀ p₁ p₂) := by
      apply Finset.sum_le_sum
      intro Z _
      simpa only [Z.property] using subspaceTripleProfile_card_upper (K := K) (V := Z.val) r p₀ p₁ p₂
        (by simpa only [Z.property] using hr) h₀ h₁ h₂
    _ = (Nat.card (DimSubspace K V n) : ℝ) *
        (2^(p₀+p₁+p₂+3*r)*(Fintype.card K : ℝ)^(T2x38 n r p₀ p₁ p₂)) := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card]
    _ ≤ (2^n*(Fintype.card K : ℝ)^(n*(finrank K V-n))) *
        (2^(p₀+p₁+p₂+3*r)*(Fintype.card K : ℝ)^(T2x38 n r p₀ p₁ p₂)) :=
      mul_le_mul_of_nonneg_right (T2x26 n hn) (by positivity)
    _ = _ := by simp only [pow_add]; ring
end SpanCount
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section PlantedSubspaceExponent
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype K]
 theorem subspace_span_cost_identity (d n r p₀ p₁ p₂ : ℕ)
    (hn : n ≤ d) (hr : r ≤ n)
    (h₀ : p₀+p₁ ≤ r) (h₁ : p₀+p₂ ≤ r) (h₂ : p₁+p₂ ≤ r) :
    ((n*(d-n)+T2x38 n r p₀ p₁ p₂ : ℕ) : ℝ) - (3*r*(d-r) : ℕ) =
      -((d:ℝ)-2*r)*(p₀+p₁+p₂) - ((p₀:ℝ)^2+p₁^2+p₂^2) - ((d:ℝ)-n)*(3*r-n-(p₀+p₁+p₂)) := by
  have hp₀ : p₀ ≤ n := (Nat.le_add_right p₀ p₁).trans (h₀.trans hr)
  have hp₁ : p₁ ≤ n := (Nat.le_add_left p₁ p₀).trans (h₀.trans hr)
  have hp₂ : p₂ ≤ n := (Nat.le_add_left p₂ p₀).trans (h₁.trans hr)
  simp only [T2x38,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,
    Nat.cast_sub hn,Nat.cast_sub hr,Nat.cast_sub (hr.trans hn),
    Nat.cast_sub hp₀,Nat.cast_sub hp₁,Nat.cast_sub hp₂,Nat.cast_sub h₀,Nat.cast_sub h₁,Nat.cast_sub h₂]
  ring
 theorem subspace_span_probability_bound (r p₀ p₁ p₂ n : ℕ)
    (hn : n ≤ finrank K V) (hr : r ≤ n)
    (h₀ : p₀+p₁ ≤ r) (h₁ : p₀+p₂ ≤ r) (h₂ : p₁+p₂ ≤ r) :
    (Nat.card (T2x9 (K := K) (V := V) r p₀ p₁ p₂ n) : ℝ) /
      (Nat.card (DimSubspace K V r) : ℝ)^3 ≤
      2^(n+p₀+p₁+p₂+3*r)*(Fintype.card K : ℝ)^(
        -((finrank K V:ℝ)-2*r)*(p₀+p₁+p₂) - ((p₀:ℝ)^2+p₁^2+p₂^2) -
          ((finrank K V:ℝ)-n)*(3*r-n-(p₀+p₁+p₂))) := by
  let : Finite V := Module.finite_of_finite K
  let q : ℝ := Fintype.card K
  have hq : 0 < q := by dsimp [q]; exact_mod_cast Fintype.card_pos (α := K)
  have hcount := subspaceTripleSpanProfile_card_upper (K := K) (V := V) r p₀ p₁ p₂ n hn hr h₀ h₁ h₂
  have hden : q^(3*r*(finrank K V-r)) ≤ (Nat.card (DimSubspace K V r) : ℝ)^3 := by
    have hu := subspace_count_lower (K := K) (V := V) r (hr.trans hn)
    have hh := pow_le_pow_left₀ (pow_nonneg hq.le _) hu 3
    simpa only [←pow_mul,Nat.mul_comm 3 r,Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using hh
  have hp : 0 < (Nat.card (DimSubspace K V r) : ℝ)^3 := lt_of_lt_of_le (pow_pos hq _) hden
  have hdiv : (Nat.card (T2x9 (K := K) (V := V) r p₀ p₁ p₂ n) : ℝ) /
        (Nat.card (DimSubspace K V r) : ℝ)^3 ≤
      (2^(n+p₀+p₁+p₂+3*r)*q^(n*(finrank K V-n)+T2x38 n r p₀ p₁ p₂)) /
        q^(3*r*(finrank K V-r)) := by
    exact div_le_div₀ (by positivity) hcount (pow_pos hq _) hden
  refine hdiv.trans_eq ?_
  rw [mul_div_assoc,←Real.rpow_natCast q (n*(finrank K V-n)+T2x38 n r p₀ p₁ p₂),
    ←Real.rpow_natCast q (3*r*(finrank K V-r)),←Real.rpow_sub hq,
    subspace_span_cost_identity (finrank K V) n r p₀ p₁ p₂ hn hr h₀ h₁ h₂]
end PlantedSubspaceExponent
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section DualPlantedBases
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
 theorem coannihilator_finrank (R : Submodule K (Module.Dual K V)) :
    finrank K R.dualCoannihilator + finrank K R = finrank K V := by
  have h := Subspace.finrank_add_finrank_dualAnnihilator_eq R.dualCoannihilator
  rwa [Subspace.dualCoannihilator_dualAnnihilator_eq] at h
noncomputable def dualDimSubspaceEquiv (r : ℕ) (hr : r ≤ finrank K V) :
    DimSubspace K V (finrank K V-r) ≃ DimSubspace K (Module.Dual K V) r where
  toFun U := ⟨U.val.dualAnnihilator, by
    have h := Subspace.finrank_add_finrank_dualAnnihilator_eq U.val
    rw [U.property] at h
    omega⟩
  invFun R := ⟨R.val.dualCoannihilator, by
    have h := coannihilator_finrank R.val
    rw [R.property] at h
    omega⟩
  left_inv U := Subtype.ext Subspace.dualAnnihilator_dualCoannihilator_eq
  right_inv R := Subtype.ext Subspace.dualCoannihilator_dualAnnihilator_eq
 theorem coannihilator_common_finrank (R₀ R₁ R₂ : Submodule K (Module.Dual K V)) :
    finrank K ↥((R₀.dualCoannihilator ⊓ R₁.dualCoannihilator) ⊓ R₂.dualCoannihilator) =
      finrank K V - finrank K ↥((R₀ ⊔ R₁) ⊔ R₂) := by
  rw [←Submodule.dualCoannihilator_sup_eq,←Submodule.dualCoannihilator_sup_eq]
  have h := coannihilator_finrank ((R₀ ⊔ R₁) ⊔ R₂)
  omega
noncomputable def dualGraph (R : Submodule K (Module.Dual K V))
    (B : SymForm K R.dualCoannihilator) : Lagrangian (K := K) (V := V) :=
  T2x28 R.dualCoannihilator B
 theorem dualGraph_vertical_subspace (R : Submodule K (Module.Dual K V))
    (B : SymForm K R.dualCoannihilator) (f : Module.Dual K V) :
    ((0,f) : V × Module.Dual K V) ∈ (dualGraph R B).val ↔ f ∈ R := by
  change (∃ u : R.dualCoannihilator, u.val = 0 ∧ _ = B.val u) ↔ _
  constructor
  · rintro ⟨u,hu,hf⟩
    have hu0 : u = 0 := Subtype.ext hu
    have hf0 : f ∈ R.dualCoannihilator.dualAnnihilator := by
      apply (Submodule.mem_dualAnnihilator (W := R.dualCoannihilator) f).mpr
      intro x hx
      have h := congrArg (fun l : Module.Dual K R.dualCoannihilator => l ⟨x,hx⟩) hf
      simpa [hu0] using h
    simpa only [Subspace.dualCoannihilator_dualAnnihilator_eq] using hf0
  · intro hf
    refine ⟨0,rfl,?_⟩
    ext x
    change f x.val = B.val 0 x
    rw [map_zero,LinearMap.zero_apply]
    have hx := (Submodule.mem_dualCoannihilator (Φ := R) x.val).mp x.property
    exact hx f hf
 theorem dualGraph_common_zero (R₀ R₁ R₂ : Submodule K (Module.Dual K V))
    (F : OriginalForms R₀.dualCoannihilator R₁.dualCoannihilator R₂.dualCoannihilator)
    (h : ((dualGraph R₀ F.1).val ⊓ (dualGraph R₁ F.2.1).val) ⊓ (dualGraph R₂ F.2.2).val = ⊥) :
    (R₀ ⊓ R₁) ⊓ R₂ = ⊥ := by
  apply le_antisymm _ bot_le
  intro f hf
  have hm : ((0,f) : V × Module.Dual K V) ∈
      ((dualGraph R₀ F.1).val ⊓ (dualGraph R₁ F.2.1).val) ⊓ (dualGraph R₂ F.2.2).val :=
    ⟨⟨(dualGraph_vertical_subspace R₀ F.1 f).mpr hf.1.1,
       (dualGraph_vertical_subspace R₁ F.2.1 f).mpr hf.1.2⟩,
       (dualGraph_vertical_subspace R₂ F.2.2 f).mpr hf.2⟩
  have hz := h.le hm
  exact congrArg Prod.snd hz
end DualPlantedBases
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section NullityAll
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype K] [Finite V]
 theorem T2x73 (t : ℕ) :
    (Nat.card {B : SymForm K V // t ≤ finrank K B.val.ker} : ℝ) / Nat.card (SymForm K V) ≤
      2^t / (Fintype.card K : ℝ)^((t+1).choose 2) := by
  by_cases ht : t ≤ finrank K V
  · exact symmetric_nullity_probability_bound t ht
  · have : IsEmpty {B : SymForm K V // t ≤ finrank K B.val.ker} :=
      ⟨fun B => ht (B.property.trans (Submodule.finrank_le B.val.val.ker))⟩
    rw [Nat.card_of_isEmpty,Nat.cast_zero,zero_div]
    positivity
end NullityAll
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section NullityAllLift
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype K] [Finite V]
variable (A₀ A₁ A₂ : Submodule K V)
theorem planted_nullity_probability_bound_all
    (t₀ t₁ t₂ : ℕ) :
    (Nat.card {F : OriginalForms A₀ A₁ A₂ //
      t₀ ≤ finrank K (T2x33 A₀ A₁ A₂ F).1.val.ker ∧
      t₁ ≤ finrank K (T2x33 A₀ A₁ A₂ F).2.1.val.ker ∧
      t₂ ≤ finrank K (T2x33 A₀ A₁ A₂ F).2.2.val.ker} : ℝ) /
      Nat.card (OriginalForms A₀ A₁ A₂) ≤
    (Fintype.card K : ℝ)^((finrank K (CommonSpace A₀ A₁ A₂)+1).choose 2) *
      ((2^t₀ / (Fintype.card K : ℝ)^((t₀+1).choose 2)) *
       (2^t₁ / (Fintype.card K : ℝ)^((t₁+1).choose 2)) *
       (2^t₂ / (Fintype.card K : ℝ)^((t₂+1).choose 2))) := by
  have hc := linear_constraint_probability_bound
    (T2x33 A₀ A₁ A₂) (differenceConstraint A₀ A₁ A₂)
    (differenceConstraint_surjective A₀ A₁ A₂) (originalCyclicDifference_range A₀ A₁ A₂)
    (fun D => t₀ ≤ finrank K D.1.val.ker ∧ t₁ ≤ finrank K D.2.1.val.ker ∧
      t₂ ≤ finrank K D.2.2.val.ker)
  have hp := triple_predicate_probability
    (fun B : SymForm K ↥(A₁ ⊓ A₂) => t₀ ≤ finrank K B.val.ker)
    (fun B : SymForm K ↥(A₂ ⊓ A₀) => t₁ ≤ finrank K B.val.ker)
    (fun B : SymForm K ↥(A₀ ⊓ A₁) => t₂ ≤ finrank K B.val.ker)
  rw [mul_div_assoc, hp, symForm_card, Nat.cast_pow] at hc
  refine hc.trans ?_
  have hb₀ := T2x73 (K := K) (V := ↥(A₁ ⊓ A₂)) t₀
  have hb₁ := T2x73 (K := K) (V := ↥(A₂ ⊓ A₀)) t₁
  have hb₂ := T2x73 (K := K) (V := ↥(A₀ ⊓ A₁)) t₂
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact mul_le_mul (mul_le_mul hb₀ hb₁ (by positivity) (by positivity)) hb₂
    (by positivity) (by positivity)
 theorem lift_pair_profile_probability_bound_all (t₀ t₁ t₂ : ℕ)
 :
    (Nat.card {F : OriginalForms A₀ A₁ A₂ //
      finrank K ↥(A₁.dualAnnihilator ⊓ A₂.dualAnnihilator) + t₀ ≤
        finrank K ↥((T2x28 A₁ F.2.1).val ⊓ (T2x28 A₂ F.2.2).val) ∧
      finrank K ↥(A₂.dualAnnihilator ⊓ A₀.dualAnnihilator) + t₁ ≤
        finrank K ↥((T2x28 A₂ F.2.2).val ⊓ (T2x28 A₀ F.1).val) ∧
      finrank K ↥(A₀.dualAnnihilator ⊓ A₁.dualAnnihilator) + t₂ ≤
        finrank K ↥((T2x28 A₀ F.1).val ⊓ (T2x28 A₁ F.2.1).val)} : ℝ) /
      Nat.card (OriginalForms A₀ A₁ A₂) ≤
    (Fintype.card K : ℝ)^((finrank K (CommonSpace A₀ A₁ A₂)+1).choose 2) *
      ((2^t₀ / (Fintype.card K : ℝ)^((t₀+1).choose 2)) *
       (2^t₁ / (Fintype.card K : ℝ)^((t₁+1).choose 2)) *
       (2^t₂ / (Fintype.card K : ℝ)^((t₂+1).choose 2))) := by
  have he (F : OriginalForms A₀ A₁ A₂) :
      (finrank K ↥(A₁.dualAnnihilator ⊓ A₂.dualAnnihilator) + t₀ ≤
        finrank K ↥((T2x28 A₁ F.2.1).val ⊓ (T2x28 A₂ F.2.2).val) ∧
      finrank K ↥(A₂.dualAnnihilator ⊓ A₀.dualAnnihilator) + t₁ ≤
        finrank K ↥((T2x28 A₂ F.2.2).val ⊓ (T2x28 A₀ F.1).val) ∧
      finrank K ↥(A₀.dualAnnihilator ⊓ A₁.dualAnnihilator) + t₂ ≤
        finrank K ↥((T2x28 A₀ F.1).val ⊓ (T2x28 A₁ F.2.1).val)) ↔
      (t₀ ≤ finrank K (T2x33 A₀ A₁ A₂ F).1.val.ker ∧
      t₁ ≤ finrank K (T2x33 A₀ A₁ A₂ F).2.1.val.ker ∧
      t₂ ≤ finrank K (T2x33 A₀ A₁ A₂ F).2.2.val.ker) := by
    change (_ ≤ finrank K ↥(formGraph A₁ F.2.1.val ⊓ formGraph A₂ F.2.2.val) ∧
      _ ≤ finrank K ↥(formGraph A₂ F.2.2.val ⊓ formGraph A₀ F.1.val) ∧
      _ ≤ finrank K ↥(formGraph A₀ F.1.val ⊓ formGraph A₁ F.2.1.val)) ↔ _
    rw [T2x43,T2x43,T2x43]
    simp only [Nat.add_le_add_iff_left]
    rfl
  rw [Nat.card_congr (Equiv.subtypeEquivRight he)]
  exact planted_nullity_probability_bound_all A₀ A₁ A₂ t₀ t₁ t₂
end NullityAllLift
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section DualProfileLift
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {r p₀ p₁ p₂ n : ℕ}
abbrev DualProfileForms (R : T2x9 (K := K) (V := Module.Dual K V) r p₀ p₁ p₂ n) :=
  OriginalForms R.val.val.1.val.dualCoannihilator R.val.val.2.1.val.dualCoannihilator
    R.val.val.2.2.val.dualCoannihilator
abbrev DualLiftEvent (R : T2x9 (K := K) (V := Module.Dual K V) r p₀ p₁ p₂ n)
    (t₀ t₁ t₂ : ℕ) :=
  {F : DualProfileForms R //
    p₂+t₂ ≤ finrank K ↥((dualGraph R.val.val.2.1.val F.2.1).val ⊓ (dualGraph R.val.val.2.2.val F.2.2).val) ∧
    p₁+t₁ ≤ finrank K ↥((dualGraph R.val.val.2.2.val F.2.2).val ⊓ (dualGraph R.val.val.1.val F.1).val) ∧
    p₀+t₀ ≤ finrank K ↥((dualGraph R.val.val.1.val F.1).val ⊓ (dualGraph R.val.val.2.1.val F.2.1).val)}
 theorem dualProfileForms_card [Fintype K] [Finite V]
    (R : T2x9 (K := K) (V := Module.Dual K V) r p₀ p₁ p₂ n) :
    Nat.card (DualProfileForms R) = (Fintype.card K)^(3*((finrank K V-r+1).choose 2)) := by
  have hdim (S : DimSubspace K (Module.Dual K V) r) : finrank K S.val.dualCoannihilator = finrank K V-r := by
    have h := coannihilator_finrank S.val
    rw [S.property] at h
    omega
  simp only [DualProfileForms,OriginalForms,Nat.card_prod,symForm_card,hdim,←pow_add]
  congr 1
  omega
 theorem dual_lift_probability_bound [Fintype K] [Finite V]
    (R : T2x9 (K := K) (V := Module.Dual K V) r p₀ p₁ p₂ n)
    (t₀ t₁ t₂ : ℕ) :
    (Nat.card (DualLiftEvent R t₀ t₁ t₂) : ℝ) / Nat.card (DualProfileForms R) ≤
      2^(t₀+t₁+t₂) * (Fintype.card K : ℝ)^((finrank K V-n+1).choose 2) /
        (Fintype.card K : ℝ)^((t₀+1).choose 2+(t₁+1).choose 2+(t₂+1).choose 2) := by
  let A₀ := R.val.val.1.val.dualCoannihilator
  let A₁ := R.val.val.2.1.val.dualCoannihilator
  let A₂ := R.val.val.2.2.val.dualCoannihilator
  have h₀ : finrank K ↥(A₁.dualAnnihilator ⊓ A₂.dualAnnihilator) = p₂ := by
    dsimp only [A₁,A₂]
    rw [Subspace.dualCoannihilator_dualAnnihilator_eq,Subspace.dualCoannihilator_dualAnnihilator_eq]
    exact R.val.property.2.2.2
  have h₁ : finrank K ↥(A₂.dualAnnihilator ⊓ A₀.dualAnnihilator) = p₁ := by
    dsimp only [A₂,A₀]
    rw [Subspace.dualCoannihilator_dualAnnihilator_eq,Subspace.dualCoannihilator_dualAnnihilator_eq,inf_comm]
    exact R.val.property.2.2.1
  have h₂ : finrank K ↥(A₀.dualAnnihilator ⊓ A₁.dualAnnihilator) = p₀ := by
    dsimp only [A₀,A₁]
    rw [Subspace.dualCoannihilator_dualAnnihilator_eq,Subspace.dualCoannihilator_dualAnnihilator_eq]
    exact R.val.property.2.1
  have hv : finrank K (CommonSpace A₀ A₁ A₂) = finrank K V-n := by
    exact (coannihilator_common_finrank _ _ _).trans (by rw [R.property])
  have hb := lift_pair_profile_probability_bound_all A₀ A₁ A₂ t₂ t₁ t₀
  rw [h₀,h₁,h₂,hv] at hb
  refine hb.trans_eq ?_
  simp only [pow_add]
  ring
end DualProfileLift
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ProfileConstraints
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
 theorem subspace_profile_constraints {r p₀ p₁ p₂ n : ℕ}
    (R : T2x9 (K := K) (V := V) r p₀ p₁ p₂ n) :
    n ≤ finrank K V ∧ r ≤ n ∧ p₀+p₁ ≤ r ∧ p₀+p₂ ≤ r ∧ p₁+p₂ ≤ r ∧
      n+(p₀+p₁+p₂) ≤ 3*r := by
  let A := R.val.val.1.val
  let B := R.val.val.2.1.val
  let C := R.val.val.2.2.val
  have hdis := triple_pairwise_disjoint A B C R.val.property.1
  have hdA : finrank K A = r := R.val.val.1.property
  have hdB : finrank K B = r := R.val.val.2.1.property
  have hdC : finrank K C = r := R.val.val.2.2.property
  have hp₀ : finrank K ↥(A ⊓ B) = p₀ := R.val.property.2.1
  have hp₁ : finrank K ↥(A ⊓ C) = p₁ := R.val.property.2.2.1
  have hp₂ : finrank K ↥(B ⊓ C) = p₂ := R.val.property.2.2.2
  have hn : finrank K ↥((A ⊔ B) ⊔ C) = n := R.property
  have ha : p₀+p₁ ≤ r := by
    have h := Submodule.finrank_mono (show (A ⊓ B) ⊔ (A ⊓ C) ≤ A from sup_le inf_le_left inf_le_left)
    rwa [disjoint_sup_finrank _ _ hdis.1,hp₀,hp₁,hdA] at h
  have hb : p₀+p₂ ≤ r := by
    have h := Submodule.finrank_mono (show (A ⊓ B) ⊔ (B ⊓ C) ≤ B from sup_le inf_le_right inf_le_left)
    rwa [disjoint_sup_finrank _ _ hdis.2.1,hp₀,hp₂,hdB] at h
  have hc : p₁+p₂ ≤ r := by
    have h := Submodule.finrank_mono (show (A ⊓ C) ⊔ (B ⊓ C) ≤ C from sup_le inf_le_right inf_le_right)
    rwa [disjoint_sup_finrank _ _ hdis.2.2,hp₁,hp₂,hdC] at h
  refine ⟨hn ▸ Submodule.finrank_le _,?_,ha,hb,hc,?_⟩
  · have h := Submodule.finrank_mono (show A ≤ (A ⊔ B) ⊔ C from le_trans le_sup_left le_sup_left)
    rwa [hdA,hn] at h
  · have h₁ := Submodule.finrank_sup_add_finrank_inf_eq A B
    have h₂ := Submodule.finrank_sup_add_finrank_inf_eq (A ⊔ B) C
    have h₃ := Submodule.finrank_mono (show (A ⊓ C) ⊔ (B ⊓ C) ≤ (A ⊔ B) ⊓ C from
      sup_le (inf_le_inf le_sup_left le_rfl) (inf_le_inf le_sup_right le_rfl))
    rw [disjoint_sup_finrank _ _ hdis.2.2,hp₁,hp₂] at h₃
    rw [hdA,hdB,hp₀] at h₁
    rw [hn,hdC] at h₂
    omega
end ProfileConstraints
section DualLiftSum
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [Fintype K] [Finite V]
 theorem center_stratum_cube (r : ℕ) (hr : r ≤ finrank K V) :
    (Nat.card {L : Lagrangian (K := K) (V := V) //
      finrank K ↥(L.val ⊓ T2x63 (K := K) (V := V)) = r} : ℝ)^3 =
      (Nat.card (DimSubspace K (Module.Dual K V) r) : ℝ)^3 *
        (Fintype.card K : ℝ)^(3*((finrank K V-r+1).choose 2)) := by
  rw [vertical_pair_count r hr,Nat.cast_mul,Nat.cast_pow,mul_pow,
    Nat.card_congr (dualDimSubspaceEquiv (K := K) (V := V) r hr),←pow_mul,Nat.mul_comm _ 3]
 theorem dual_lift_sum_probability_bound (r p₀ p₁ p₂ n t₀ t₁ t₂ : ℕ) (hr : r ≤ finrank K V) :
    (Nat.card (Σ R : T2x9 (K := K) (V := Module.Dual K V) r p₀ p₁ p₂ n,
      DualLiftEvent R t₀ t₁ t₂) : ℝ) /
      (Nat.card {L : Lagrangian (K := K) (V := V) //
        finrank K ↥(L.val ⊓ T2x63 (K := K) (V := V)) = r} : ℝ)^3 ≤
    ((Nat.card (T2x9 (K := K) (V := Module.Dual K V) r p₀ p₁ p₂ n) : ℝ) /
      (Nat.card (DimSubspace K (Module.Dual K V) r) : ℝ)^3) *
    (2^(t₀+t₁+t₂) * (Fintype.card K : ℝ)^((finrank K V-n+1).choose 2) /
      (Fintype.card K : ℝ)^((t₀+1).choose 2+(t₁+1).choose 2+(t₂+1).choose 2)) := by
  classical
  let : Finite (Module.Dual K V) := Module.finite_of_finite K
  let RType := T2x9 (K := K) (V := Module.Dual K V) r p₀ p₁ p₂ n
  let : Fintype RType := Fintype.ofFinite _
  let q : ℝ := Fintype.card K
  let f := 3*((finrank K V-r+1).choose 2)
  let b : ℝ := 2^(t₀+t₁+t₂)*q^((finrank K V-n+1).choose 2)/
    q^((t₀+1).choose 2+(t₁+1).choose 2+(t₂+1).choose 2)
  have hq : 0 < q := by dsimp [q]; exact_mod_cast Fintype.card_pos (α := K)
  have hF : 0 < q^f := pow_pos hq _
  have hb (R : RType) : (Nat.card (DualLiftEvent R t₀ t₁ t₂) : ℝ) ≤ b*q^f := by
    have h := dual_lift_probability_bound R t₀ t₁ t₂
    rw [dualProfileForms_card,Nat.cast_pow] at h
    exact (div_le_iff₀ hF).mp h
  have hc : (Nat.card (Σ R : RType, DualLiftEvent R t₀ t₁ t₂) : ℝ) ≤
      (Nat.card RType : ℝ)*b*q^f := by
    rw [Nat.card_sigma,Nat.cast_sum]
    calc
      _ ≤ ∑ _R : RType, b*q^f := Finset.sum_le_sum (fun R _ => hb R)
      _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul,Finset.card_univ,Nat.card_eq_fintype_card]; ring
  rw [center_stratum_cube r hr]
  refine (div_le_div_of_nonneg_right hc (by positivity)).trans_eq ?_
  change (Nat.card RType : ℝ)*b*q^f / ((Nat.card (DimSubspace K (Module.Dual K V) r) : ℝ)^3*q^f) = _
  rw [mul_div_mul_right _ _ hF.ne']
  ring
end DualLiftSum
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section CanonicalCoding
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
abbrev T2x59 (r : ℕ) := {L : Lagrangian (K := K) (V := V) //
  finrank K ↥(L.val ⊓ T2x63 (K := K) (V := V)) = r}
noncomputable def dualPairStratumEquiv (r : ℕ) (hr : r ≤ finrank K V) :
    (Σ R : DimSubspace K (Module.Dual K V) r, SymForm K R.val.dualCoannihilator) ≃
      T2x59 (K := K) (V := V) r :=
  (Equiv.sigmaCongrLeft (β := fun U : DimSubspace K V (finrank K V-r) => SymForm K U.val)
    (dualDimSubspaceEquiv (K := K) (V := V) r hr).symm).trans (pairStratumEquiv r hr)
abbrev DualBaseTriple (r : ℕ) := DimSubspace K (Module.Dual K V) r ×
  DimSubspace K (Module.Dual K V) r × DimSubspace K (Module.Dual K V) r
abbrev DualBaseForms {r : ℕ} (R : DualBaseTriple (K := K) (V := V) r) :=
  OriginalForms R.1.val.dualCoannihilator R.2.1.val.dualCoannihilator R.2.2.val.dualCoannihilator
noncomputable def dualBaseTripleGraph {r : ℕ} (R : DualBaseTriple (K := K) (V := V) r)
    (F : DualBaseForms R) : Lagrangian (K := K) (V := V) × Lagrangian (K := K) (V := V) × Lagrangian (K := K) (V := V) :=
  (dualGraph R.1.val F.1,dualGraph R.2.1.val F.2.1,dualGraph R.2.2.val F.2.2)
noncomputable def dualTripleStratumEquiv (r : ℕ) (hr : r ≤ finrank K V) :
    (Σ R : DualBaseTriple (K := K) (V := V) r, DualBaseForms R) ≃
      T2x59 (K := K) (V := V) r × T2x59 (K := K) (V := V) r × T2x59 (K := K) (V := V) r :=
  let e : (Σ R : DualBaseTriple (K := K) (V := V) r, DualBaseForms R) ≃
      (Σ R : DimSubspace K (Module.Dual K V) r, SymForm K R.val.dualCoannihilator) ×
      (Σ R : DimSubspace K (Module.Dual K V) r, SymForm K R.val.dualCoannihilator) ×
      (Σ R : DimSubspace K (Module.Dual K V) r, SymForm K R.val.dualCoannihilator) :=
    { toFun := fun RF => (⟨RF.1.1,RF.2.1⟩,⟨RF.1.2.1,RF.2.2.1⟩,⟨RF.1.2.2,RF.2.2.2⟩)
      invFun := fun p => ⟨(p.1.1,p.2.1.1,p.2.2.1),(p.1.2,p.2.1.2,p.2.2.2)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  e.trans ((dualPairStratumEquiv r hr).prodCongr ((dualPairStratumEquiv r hr).prodCongr (dualPairStratumEquiv r hr)))
 theorem T2x70 (R S : Submodule K (Module.Dual K V))
    (F : SymForm K R.dualCoannihilator) (G : SymForm K S.dualCoannihilator) :
    finrank K ↥(R ⊓ S) ≤ finrank K ↥((dualGraph R F).val ⊓ (dualGraph S G).val) := by
  change _ ≤ finrank K ↥(formGraph R.dualCoannihilator F.val ⊓ formGraph S.dualCoannihilator G.val)
  rw [T2x43,
    Subspace.dualCoannihilator_dualAnnihilator_eq,Subspace.dualCoannihilator_dualAnnihilator_eq]
  exact Nat.le_add_right _ _
abbrev CanonicalLiftProfile (r s₀ s₁ s₂ : ℕ) :=
  {RF : Σ R : DualBaseTriple (K := K) (V := V) r, DualBaseForms R //
    let L := dualBaseTripleGraph RF.1 RF.2
    (L.1.val ⊓ L.2.1.val) ⊓ L.2.2.val = ⊥ ∧
    finrank K ↥(L.1.val ⊓ L.2.1.val) = s₀ ∧
    finrank K ↥(L.1.val ⊓ L.2.2.val) = s₁ ∧
    finrank K ↥(L.2.1.val ⊓ L.2.2.val) = s₂}
end CanonicalCoding
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ExtraFeasibility
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
 theorem coannihilator_pair_finrank (R S : Submodule K (Module.Dual K V)) :
    finrank K ↥(R.dualCoannihilator ⊓ S.dualCoannihilator) + finrank K R + finrank K S =
      finrank K V + finrank K ↥(R ⊓ S) := by
  rw [←Submodule.dualCoannihilator_sup_eq]
  have h := coannihilator_finrank (R ⊔ S)
  have hg := Submodule.finrank_sup_add_finrank_inf_eq R S
  omega
 theorem dualGraph_pair_finrank_le (R S : Submodule K (Module.Dual K V))
    (F : SymForm K R.dualCoannihilator) (G : SymForm K S.dualCoannihilator) :
    finrank K ↥((dualGraph R F).val ⊓ (dualGraph S G).val) ≤
      finrank K ↥(R ⊓ S)+finrank K ↥(R.dualCoannihilator ⊓ S.dualCoannihilator) := by
  change finrank K ↥(formGraph R.dualCoannihilator F.val ⊓ formGraph S.dualCoannihilator G.val) ≤ _
  rw [T2x43,
    Subspace.dualCoannihilator_dualAnnihilator_eq,Subspace.dualCoannihilator_dualAnnihilator_eq]
  exact Nat.add_le_add_left (Submodule.finrank_le _) _
 theorem dualGraph_pair_extra_feasible {r s : ℕ} (R S : DimSubspace K (Module.Dual K V) r)
    (F : SymForm K R.val.dualCoannihilator) (G : SymForm K S.val.dualCoannihilator)
    (hs : finrank K ↥((dualGraph R.val F).val ⊓ (dualGraph S.val G).val) = s) :
    (s-finrank K ↥(R.val ⊓ S.val))+2*r ≤ finrank K V+finrank K ↥(R.val ⊓ S.val) := by
  have h₁ := T2x70 R.val S.val F G
  have h₂ := dualGraph_pair_finrank_le R.val S.val F G
  have h₃ := coannihilator_pair_finrank R.val S.val
  rw [hs] at h₁ h₂
  rw [R.property,S.property] at h₃
  omega
 theorem dual_common_pair_extra_feasible {r p₀ p₁ p₂ n : ℕ}
    (R : T2x9 (K := K) (V := Module.Dual K V) r p₀ p₁ p₂ n) :
    (finrank K V-n)+2*r ≤ finrank K V+p₀ ∧
    (finrank K V-n)+2*r ≤ finrank K V+p₁ ∧
    (finrank K V-n)+2*r ≤ finrank K V+p₂ := by
  let A := R.val.val.1.val
  let B := R.val.val.2.1.val
  let C := R.val.val.2.2.val
  have hdA : finrank K A = r := R.val.val.1.property
  have hdB : finrank K B = r := R.val.val.2.1.property
  have hdC : finrank K C = r := R.val.val.2.2.property
  have hp₀ : finrank K ↥(A ⊓ B) = p₀ := R.val.property.2.1
  have hp₁ : finrank K ↥(A ⊓ C) = p₁ := R.val.property.2.2.1
  have hp₂ : finrank K ↥(B ⊓ C) = p₂ := R.val.property.2.2.2
  have hn : finrank K ↥((A ⊔ B) ⊔ C) = n := R.property
  have hv := coannihilator_common_finrank A B C
  rw [hn] at hv
  have h₀ := Submodule.finrank_mono (show (A.dualCoannihilator ⊓ B.dualCoannihilator) ⊓ C.dualCoannihilator ≤
    A.dualCoannihilator ⊓ B.dualCoannihilator from inf_le_left)
  have h₁ := Submodule.finrank_mono (show (A.dualCoannihilator ⊓ B.dualCoannihilator) ⊓ C.dualCoannihilator ≤
    A.dualCoannihilator ⊓ C.dualCoannihilator from inf_le_inf inf_le_left le_rfl)
  have h₂ := Submodule.finrank_mono (show (A.dualCoannihilator ⊓ B.dualCoannihilator) ⊓ C.dualCoannihilator ≤
    B.dualCoannihilator ⊓ C.dualCoannihilator from inf_le_inf inf_le_right le_rfl)
  rw [hv] at h₀ h₁ h₂
  have hc₀ := coannihilator_pair_finrank A B
  have hc₁ := coannihilator_pair_finrank A C
  have hc₂ := coannihilator_pair_finrank B C
  rw [hdA,hdB,hp₀] at hc₀
  rw [hdA,hdC,hp₁] at hc₁
  rw [hdB,hdC,hp₂] at hc₂
  omega
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
noncomputable def canonicalLiftFourDims {r s₀ s₁ s₂ : ℕ}
    (P : CanonicalLiftProfile (K := K) (V := V) r s₀ s₁ s₂) : FourDims (finrank K V) :=
  let bound (R : Submodule K (Module.Dual K V)) : finrank K R < finrank K V+1 := by
    have h := Submodule.finrank_le R
    rw [Subspace.dual_finrank_eq] at h
    omega
  (⟨finrank K ↥(P.val.1.1.val ⊓ P.val.1.2.1.val),bound _⟩,
   ⟨finrank K ↥(P.val.1.1.val ⊓ P.val.1.2.2.val),bound _⟩,
   ⟨finrank K ↥(P.val.1.2.1.val ⊓ P.val.1.2.2.val),bound _⟩,
   ⟨finrank K ↥((P.val.1.1.val ⊔ P.val.1.2.1.val) ⊔ P.val.1.2.2.val),bound _⟩)
noncomputable def canonicalLiftSubspaces {r s₀ s₁ s₂ : ℕ}
    (P : CanonicalLiftProfile (K := K) (V := V) r s₀ s₁ s₂) :
    T2x9 (K := K) (V := Module.Dual K V) r
      (canonicalLiftFourDims P).1.val (canonicalLiftFourDims P).2.1.val
      (canonicalLiftFourDims P).2.2.1.val (canonicalLiftFourDims P).2.2.2.val :=
  ⟨⟨P.val.1,dualGraph_common_zero _ _ _ P.val.2 P.property.1,rfl,rfl,rfl⟩,rfl⟩
 theorem canonicalLift_feasible {r s₀ s₁ s₂ : ℕ}
    (P : CanonicalLiftProfile (K := K) (V := V) r s₀ s₁ s₂) :
    BaseFeasible r s₀ s₁ s₂ (canonicalLiftFourDims P) := by
  have hc := subspace_profile_constraints (canonicalLiftSubspaces P)
  refine ⟨hc.2.1,hc.2.2.1,hc.2.2.2.1,hc.2.2.2.2.1,hc.2.2.2.2.2,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (T2x70 _ _ P.val.2.1 P.val.2.2.1).trans_eq P.property.2.1
  · exact (T2x70 _ _ P.val.2.1 P.val.2.2.2).trans_eq P.property.2.2.1
  · exact (T2x70 _ _ P.val.2.2.1 P.val.2.2.2).trans_eq P.property.2.2.2
  · exact dualGraph_pair_extra_feasible P.val.1.1 P.val.1.2.1 P.val.2.1 P.val.2.2.1 P.property.2.1
  · exact dualGraph_pair_extra_feasible P.val.1.1 P.val.1.2.2 P.val.2.1 P.val.2.2.2 P.property.2.2.1
  · exact dualGraph_pair_extra_feasible P.val.1.2.1 P.val.1.2.2 P.val.2.2.1 P.val.2.2.2 P.property.2.2.2
  · exact dual_common_pair_extra_feasible (canonicalLiftSubspaces P)
 theorem dualGraph_pair_gap_bound (R S : Submodule K (Module.Dual K V))
    (F : SymForm K R.dualCoannihilator) (G : SymForm K S.dualCoannihilator)
    {p s : ℕ} (hp : finrank K ↥(R ⊓ S) = p)
    (hs : finrank K ↥((dualGraph R F).val ⊓ (dualGraph S G).val) = s) :
    p+(s-p) ≤ finrank K ↥((dualGraph R F).val ⊓ (dualGraph S G).val) := by
  have h := T2x70 R S F G
  rw [hp,hs] at h
  rw [hs]
  omega
noncomputable def dualLift_of_exactDims {r p₀ p₁ p₂ n s₀ s₁ s₂ : ℕ}
    (R : T2x9 (K := K) (V := Module.Dual K V) r p₀ p₁ p₂ n)
    (F : DualProfileForms R)
    (hs₀ : finrank K ↥((dualGraph R.val.val.1.val F.1).val ⊓ (dualGraph R.val.val.2.1.val F.2.1).val) = s₀)
    (hs₁ : finrank K ↥((dualGraph R.val.val.1.val F.1).val ⊓ (dualGraph R.val.val.2.2.val F.2.2).val) = s₁)
    (hs₂ : finrank K ↥((dualGraph R.val.val.2.1.val F.2.1).val ⊓ (dualGraph R.val.val.2.2.val F.2.2).val) = s₂) :
    DualLiftEvent R (s₀-p₀) (s₁-p₁) (s₂-p₂) :=
  ⟨F,dualGraph_pair_gap_bound _ _ F.2.1 F.2.2 R.val.property.2.2.2 hs₂,
    by
      have h := dualGraph_pair_gap_bound _ _ F.1 F.2.2 R.val.property.2.2.1 hs₁
      rwa [inf_comm] at h,
    dualGraph_pair_gap_bound _ _ F.1 F.2.1 R.val.property.2.1 hs₀⟩
noncomputable def canonicalLiftCoding {r s₀ s₁ s₂ : ℕ}
    (P : CanonicalLiftProfile (K := K) (V := V) r s₀ s₁ s₂) :
    Σ θ : BaseParameters (finrank K V) r s₀ s₁ s₂,
      Σ R : T2x9 (K := K) (V := Module.Dual K V)
        r θ.val.1.val θ.val.2.1.val θ.val.2.2.1.val θ.val.2.2.2.val,
        DualLiftEvent R (s₀-θ.val.1.val) (s₁-θ.val.2.1.val) (s₂-θ.val.2.2.1.val) :=
  ⟨⟨canonicalLiftFourDims P,canonicalLift_feasible P⟩,canonicalLiftSubspaces P,
    dualLift_of_exactDims (canonicalLiftSubspaces P) P.val.2 P.property.2.1 P.property.2.2.1 P.property.2.2.2⟩
 theorem canonicalLiftCoding_injective (r s₀ s₁ s₂ : ℕ) :
    Function.Injective (canonicalLiftCoding (K := K) (V := V) (r := r) (s₀ := s₀) (s₁ := s₁) (s₂ := s₂)) := by
  let recover : (Σ θ : BaseParameters (finrank K V) r s₀ s₁ s₂,
      Σ R : T2x9 (K := K) (V := Module.Dual K V)
        r θ.val.1.val θ.val.2.1.val θ.val.2.2.1.val θ.val.2.2.2.val,
        DualLiftEvent R (s₀-θ.val.1.val) (s₁-θ.val.2.1.val) (s₂-θ.val.2.2.1.val)) →
      Σ R : DualBaseTriple (K := K) (V := V) r, DualBaseForms R :=
    fun T => ⟨T.2.1.val.val,T.2.2.val⟩
  intro P Q h
  exact Subtype.ext (congrArg recover h)
abbrev CenterTripleProfile (r s₀ s₁ s₂ : ℕ) :=
  {L : T2x59 (K := K) (V := V) r × T2x59 (K := K) (V := V) r × T2x59 (K := K) (V := V) r //
    (L.1.val.val ⊓ L.2.1.val.val) ⊓ L.2.2.val.val = ⊥ ∧
    finrank K ↥(L.1.val.val ⊓ L.2.1.val.val) = s₀ ∧
    finrank K ↥(L.1.val.val ⊓ L.2.2.val.val) = s₁ ∧
    finrank K ↥(L.2.1.val.val ⊓ L.2.2.val.val) = s₂}
noncomputable def canonicalCenterProfileEquiv (r s₀ s₁ s₂ : ℕ) (hr : r ≤ finrank K V) :
    CanonicalLiftProfile (K := K) (V := V) r s₀ s₁ s₂ ≃ CenterTripleProfile (K := K) (V := V) r s₀ s₁ s₂ :=
  Equiv.subtypeEquiv (dualTripleStratumEquiv r hr) (fun _ => Iff.rfl)
end CanonicalParameterCount
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
noncomputable instance baseParametersFintype (d r s₀ s₁ s₂ : ℕ) : Fintype (BaseParameters d r s₀ s₁ s₂) := Fintype.ofFinite _
def T2x74 (d r s₀ s₁ s₂ : ℕ) (θ : FourDims d) : ℝ :=
  -((d:ℝ)-2*r)*(θ.1.val+θ.2.1.val+θ.2.2.1.val) -
    ((θ.1.val:ℝ)^2+θ.2.1.val^2+θ.2.2.1.val^2) -
    ((d:ℝ)-θ.2.2.2.val)*(3*r-θ.2.2.2.val-(θ.1.val+θ.2.1.val+θ.2.2.1.val)) +
    ((d-θ.2.2.2.val+1).choose 2 : ℕ) -
    (((s₀-θ.1.val+1).choose 2+(s₁-θ.2.1.val+1).choose 2+(s₂-θ.2.2.1.val+1).choose 2 : ℕ) : ℝ)
def T2x58 (r s₀ s₁ s₂ : ℕ) {d : ℕ} (θ : FourDims d) : ℝ :=
  2^(θ.2.2.2.val+θ.1.val+θ.2.1.val+θ.2.2.1.val+3*r+(s₀-θ.1.val)+(s₁-θ.2.1.val)+(s₂-θ.2.2.1.val))
section CanonicalNumericalBound
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype K] [Finite V]
 theorem reducedPlanted_bound_one (r s₀ s₁ s₂ : ℕ)
    (θ : BaseParameters (finrank K V) r s₀ s₁ s₂) :
    (Nat.card (Σ R : T2x9 (K := K) (V := Module.Dual K V)
        r θ.val.1.val θ.val.2.1.val θ.val.2.2.1.val θ.val.2.2.2.val,
        DualLiftEvent R (s₀-θ.val.1.val) (s₁-θ.val.2.1.val) (s₂-θ.val.2.2.1.val)) : ℝ) /
      (Nat.card (T2x59 (K := K) (V := V) r) : ℝ)^3 ≤
    T2x58 r s₀ s₁ s₂ θ.val *
      (Fintype.card K : ℝ)^(T2x74 (finrank K V) r s₀ s₁ s₂ θ.val) := by
  let p₀ := θ.val.1.val
  let p₁ := θ.val.2.1.val
  let p₂ := θ.val.2.2.1.val
  let n := θ.val.2.2.2.val
  let t₀ := s₀-p₀
  let t₁ := s₁-p₁
  let t₂ := s₂-p₂
  have hn : n ≤ finrank K V := Nat.le_of_lt_succ θ.val.2.2.2.isLt
  have hcon := θ.property
  have hr : r ≤ n := hcon.1
  have hh := dual_lift_sum_probability_bound (K := K) (V := V) r p₀ p₁ p₂ n t₀ t₁ t₂ (hr.trans hn)
  have hp := subspace_span_probability_bound (K := K) (V := Module.Dual K V) r p₀ p₁ p₂ n
    (by rwa [Subspace.dual_finrank_eq]) hr hcon.2.1 hcon.2.2.1 hcon.2.2.2.1
  rw [Subspace.dual_finrank_eq] at hp
  refine hh.trans ((mul_le_mul_of_nonneg_right hp (by positivity)).trans_eq ?_)
  let q : ℝ := Fintype.card K
  have hq : 0 < q := by dsimp [q]; exact_mod_cast Fintype.card_pos (α := K)
  let e : ℝ := -((finrank K V:ℝ)-2*r)*(p₀+p₁+p₂) - ((p₀:ℝ)^2+p₁^2+p₂^2) -
    ((finrank K V:ℝ)-n)*(3*r-n-(p₀+p₁+p₂))
  change (2^(n+p₀+p₁+p₂+3*r) * q^e) *
    (2^(t₀+t₁+t₂)*q^((finrank K V-n+1).choose 2)/q^((t₀+1).choose 2+(t₁+1).choose 2+(t₂+1).choose 2)) = _
  have he : T2x74 (finrank K V) r s₀ s₁ s₂ θ.val =
      e+((finrank K V-n+1).choose 2 : ℕ)-(((t₀+1).choose 2+(t₁+1).choose 2+(t₂+1).choose 2 : ℕ) : ℝ) := rfl
  rw [he,Real.rpow_sub hq (e+((finrank K V-n+1).choose 2 : ℕ))
    (((t₀+1).choose 2+(t₁+1).choose 2+(t₂+1).choose 2 : ℕ) : ℝ),
    Real.rpow_add hq e ((finrank K V-n+1).choose 2 : ℕ),Real.rpow_natCast,Real.rpow_natCast]
  simp only [T2x58, pow_add]
  change _ = 2^n*2^p₀*2^p₁*2^p₂*2^(3*r)*2^t₀*2^t₁*2^t₂ * _
  ring
 theorem canonical_center_profile_probability_bound (r s₀ s₁ s₂ : ℕ) (hr : r ≤ finrank K V) :
    (Nat.card (CenterTripleProfile (K := K) (V := V) r s₀ s₁ s₂) : ℝ) /
      (Nat.card (T2x59 (K := K) (V := V) r) : ℝ)^3 ≤
    ∑ θ : BaseParameters (finrank K V) r s₀ s₁ s₂,
      T2x58 r s₀ s₁ s₂ θ.val *
        (Fintype.card K : ℝ)^(T2x74 (finrank K V) r s₀ s₁ s₂ θ.val) := by
  classical
  let : Finite (Module.Dual K V) := Module.finite_of_finite K
  have hi := Nat.card_le_card_of_injective _ (canonicalLiftCoding_injective (K := K) (V := V) r s₀ s₁ s₂)
  rw [Nat.card_congr (canonicalCenterProfileEquiv r s₀ s₁ s₂ hr),Nat.card_sigma] at hi
  have hi' := (Nat.cast_le (α := ℝ)).mpr hi
  rw [Nat.cast_sum] at hi'
  refine (div_le_div_of_nonneg_right hi' (by positivity)).trans ?_
  rw [Finset.sum_div]
  exact Finset.sum_le_sum (fun θ _ => reducedPlanted_bound_one r s₀ s₁ s₂ θ)
end CanonicalNumericalBound
end SidorenkoCounterexample
end OAI
namespace OAI
namespace SidorenkoCounterexample
open Module
section Reduction
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E) (S : Submodule K E)
def T2x8 : Submodule K (ω.orthogonal S) := S.comap (ω.orthogonal S).subtype
abbrev T2x20 := (ω.orthogonal S) ⧸ T2x8 ω S
private theorem restricted_alt (ha : ω.IsAlt) :
    (ω.compl₁₂ (ω.orthogonal S).subtype (ω.orthogonal S).subtype).IsAlt := by
  intro x
  exact ha x.val
private theorem reductionKernel_le_ker : T2x8 ω S ≤
    (ω.compl₁₂ (ω.orthogonal S).subtype (ω.orthogonal S).subtype).ker := by
  intro x hx
  apply LinearMap.mem_ker.mpr
  ext y
  exact y.property x.val hx
def T2x2 (ha : ω.IsAlt) : LinearMap.BilinForm K (T2x20 ω S) :=
  LinearMap.IsRefl.liftQ₂
    (ω.compl₁₂ (ω.orthogonal S).subtype (ω.orthogonal S).subtype)
    (T2x8 ω S) (restricted_alt ω S ha).isRefl (reductionKernel_le_ker ω S)
@[simp] theorem reductionForm_mk (ha : ω.IsAlt) (x y : ω.orthogonal S) :
    T2x2 ω S ha
      ((T2x8 ω S).mkQ x) ((T2x8 ω S).mkQ y) = ω x.val y.val := rfl
theorem T2x81 (ha : ω.IsAlt) :
    (T2x2 ω S ha).IsAlt := by
  intro x
  induction x using Submodule.Quotient.induction_on with
  | H x => exact ha x.val
theorem T2x13 [FiniteDimensional K E]
    (ha : ω.IsAlt) (hω : ω.Nondegenerate) :
    (T2x2 ω S ha).Nondegenerate := by
  have hl (x : T2x20 ω S)
      (hx : ∀ y, T2x2 ω S ha x y = 0) : x = 0 := by
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      apply (Submodule.Quotient.mk_eq_zero (T2x8 ω S)).mpr
      change x.val ∈ S
      apply (ω.orthogonal_orthogonal hω ha.isRefl S).le
      intro y hy
      exact ha.isRefl _ _ (hx ((T2x8 ω S).mkQ ⟨y,hy⟩))
  refine ⟨hl, ?_⟩
  intro x hx
  apply hl
  intro y
  exact (T2x81 ω S ha).isRefl _ _ (hx y)
theorem reducedSpace_finrank [FiniteDimensional K E]
    (hω : ω.Nondegenerate) (hS : S ≤ ω.orthogonal S) :
    finrank K (T2x20 ω S) + 2 * finrank K S = finrank K E := by
  have hker : finrank K (T2x8 ω S) = finrank K S :=
    (Submodule.comapSubtypeEquivOfLe hS).finrank_eq
  have hq := Submodule.finrank_quotient_add_finrank (T2x8 ω S)
  have hp := ω.finrank_orthogonal hω S
  have hle := Submodule.finrank_le S
  change finrank K (T2x20 ω S) + finrank K (T2x8 ω S) =
    finrank K (ω.orthogonal S) at hq
  rw [hker] at hq
  omega
def T2x65 (T : Submodule K (T2x20 ω S)) : Submodule K E :=
  (T.comap (T2x8 ω S).mkQ).map (ω.orthogonal S).subtype
@[simp] theorem T2x54 (T : Submodule K (T2x20 ω S)) (x : E) :
    x ∈ T2x65 ω S T ↔ ∃ hx : x ∈ ω.orthogonal S,
      (T2x8 ω S).mkQ ⟨x,hx⟩ ∈ T := by
  constructor
  · rintro ⟨y,hy,hx⟩
    cases hx
    exact ⟨y.property,hy⟩
  · rintro ⟨hx,ht⟩
    exact ⟨⟨x,hx⟩,ht,rfl⟩
theorem le_liftReduction (hS : S ≤ ω.orthogonal S)
    (T : Submodule K (T2x20 ω S)) : S ≤ T2x65 ω S T := by
  intro x hx
  apply (T2x54 ω S T x).mpr
  refine ⟨hS hx, ?_⟩
  have hz : (T2x8 ω S).mkQ ⟨x,hS hx⟩ = 0 :=
    (Submodule.Quotient.mk_eq_zero (T2x8 ω S)).mpr hx
  rw [hz]
  exact T.zero_mem
theorem orthogonal_liftReduction (ha : ω.IsAlt) (hS : S ≤ ω.orthogonal S)
    (T : Submodule K (T2x20 ω S)) :
    ω.orthogonal (T2x65 ω S T) =
      T2x65 ω S ((T2x2 ω S ha).orthogonal T) := by
  ext x
  constructor
  · intro hx
    have hxP : x ∈ ω.orthogonal S := by
      intro s hs
      exact hx s (le_liftReduction ω S hS T hs)
    apply (T2x54 ω S _ x).mpr
    refine ⟨hxP, ?_⟩
    intro y hy
    induction y using Submodule.Quotient.induction_on with
    | H y =>
      exact hx y.val ((T2x54 ω S T y.val).mpr ⟨y.property,hy⟩)
  · intro hx
    obtain ⟨hxP,hxQ⟩ := (T2x54 ω S _ x).mp hx
    intro y hy
    obtain ⟨hyP,hyQ⟩ := (T2x54 ω S T y).mp hy
    exact hxQ ((T2x8 ω S).mkQ ⟨y,hyP⟩) hyQ
theorem liftReduction_lagrangian (ha : ω.IsAlt) (hS : S ≤ ω.orthogonal S)
    (T : Submodule K (T2x20 ω S))
    (hT : (T2x2 ω S ha).orthogonal T = T) :
    ω.orthogonal (T2x65 ω S T) = T2x65 ω S T := by
  rw [orthogonal_liftReduction ω S ha hS, hT]
def T2x3 (L : Submodule K E) : Submodule K (T2x20 ω S) :=
  (L.comap (ω.orthogonal S).subtype).map (T2x8 ω S).mkQ
theorem reduce_lift (T : Submodule K (T2x20 ω S)) :
    T2x3 ω S (T2x65 ω S T) = T := by
  ext z
  induction z using Submodule.Quotient.induction_on with
  | H z =>
    constructor
    · rintro ⟨y,hy,heq⟩
      obtain ⟨hyP,hyT⟩ := (T2x54 ω S T y.val).mp hy
      change (T2x8 ω S).mkQ y ∈ T at hyT
      exact heq ▸ hyT
    · intro hz
      refine ⟨z,?_,rfl⟩
      exact (T2x54 ω S T z.val).mpr ⟨z.property,hz⟩
theorem liftReduction_injective : Function.Injective (T2x65 ω S) := by
  intro T U h
  have hh := congrArg (T2x3 ω S) h
  simpa only [reduce_lift] using hh
theorem lift_reduce (L : Submodule K E) (hSL : S ≤ L) (hLP : L ≤ ω.orthogonal S) :
    T2x65 ω S (T2x3 ω S L) = L := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxP,y,hy,hyeq⟩ := (T2x54 ω S _ x).mp hx
    have hz : (T2x8 ω S).mkQ (y - ⟨x,hxP⟩) = 0 := by
      rw [map_sub,hyeq,sub_self]
    have hzS : y.val-x ∈ S := (Submodule.Quotient.mk_eq_zero (T2x8 ω S)).mp hz
    have hxL := L.sub_mem hy (hSL hzS)
    simpa only [Submodule.subtype_apply, sub_sub_cancel] using hxL
  · intro hx
    apply (T2x54 ω S _ x).mpr
    exact ⟨hLP hx,⟨⟨x,hLP hx⟩,hx,rfl⟩⟩
theorem T2x25 (L : Submodule K E)
    (hL : ω.orthogonal L = L) (hSL : S ≤ L) : L ≤ ω.orthogonal S := by
  intro x hx s hs
  have hxO : x ∈ ω.orthogonal L := hL.symm ▸ hx
  exact hxO s (hSL hs)
theorem reduce_lagrangian (ha : ω.IsAlt) (hS : S ≤ ω.orthogonal S)
    (L : Submodule K E) (hL : ω.orthogonal L = L) (hSL : S ≤ L) :
    (T2x2 ω S ha).orthogonal (T2x3 ω S L) =
      T2x3 ω S L := by
  apply liftReduction_injective ω S
  rw [← orthogonal_liftReduction ω S ha hS,
    lift_reduce ω S L hSL (T2x25 ω S L hL hSL),hL]
def containingLagrangianEquiv (ha : ω.IsAlt) (hS : S ≤ ω.orthogonal S) :
    {L : Submodule K E // ω.orthogonal L = L ∧ S ≤ L} ≃
      {T : Submodule K (T2x20 ω S) // (T2x2 ω S ha).orthogonal T = T} where
  toFun L := ⟨T2x3 ω S L.val,reduce_lagrangian ω S ha hS L.val L.property.1 L.property.2⟩
  invFun T := ⟨T2x65 ω S T.val,
    liftReduction_lagrangian ω S ha hS T.val T.property,le_liftReduction ω S hS T.val⟩
  left_inv L := Subtype.ext (lift_reduce ω S L.val L.property.2
    (T2x25 ω S L.val L.property.1 L.property.2))
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
    (T2x2 ω S ha).orthogonal (T2x3 ω S L) =
      T2x3 ω S L := by
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
  have hUred : T2x3 ω S U = T2x3 ω S L := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      obtain ⟨l,hl,s,hs,hls⟩ := Submodule.mem_sup.mp hy
      refine ⟨⟨l,hl.2⟩,hl.1,?_⟩
      have hz : (T2x8 ω S).mkQ ⟨s,hS hs⟩ = 0 :=
        (Submodule.Quotient.mk_eq_zero (T2x8 ω S)).mpr hs
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
theorem T2x72 (ha : ω.IsAlt) (S : Submodule K E)
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
    (s : T2x20 ω S →ₗ[K] ω.orthogonal S)
    (hs : (T2x8 ω S).mkQ.comp s = LinearMap.id)
    (x y : T2x20 ω S) :
    ω (s x).val (s y).val = T2x2 ω S ha x y := by
  have hx : (T2x8 ω S).mkQ (s x) = x := LinearMap.congr_fun hs x
  have hy : (T2x8 ω S).mkQ (s y) = y := LinearMap.congr_fun hs y
  calc
    _ = T2x2 ω S ha
      ((T2x8 ω S).mkQ (s x)) ((T2x8 ω S).mkQ (s y)) := rfl
    _ = _ := by rw [hx,hy]
theorem exists_reduction_isometry_extension (ha : ω.IsAlt)
    (hω : ω.Nondegenerate)
    (f : T2x20 ω S ≃ₗ[K] T2x20 ω S)
    (hf : ∀ x y, T2x2 ω S ha (f x) (f y) =
      T2x2 ω S ha x y) :
    ∃ e : E ≃ₗ[K] E,
      (∀ x y, ω (e x) (e y) = ω x y) ∧
      (∀ x : S, e x.val = x.val) ∧
      (∀ x : ω.orthogonal S, e x.val ∈ ω.orthogonal S) ∧
      (∀ x y : ω.orthogonal S, e x.val = y.val →
        (T2x8 ω S).mkQ y = f ((T2x8 ω S).mkQ x)) := by
  let π := (T2x8 ω S).mkQ
  obtain ⟨s,hs⟩ := π.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (Submodule.mkQ_surjective _))
  let g : T2x20 ω S →ₗ[K] E := (ω.orthogonal S).subtype.comp s
  have hπ (x : T2x20 ω S) : π (s x) = x := LinearMap.congr_fun hs x
  have hg (x y : T2x20 ω S) : ω (g x) (g y) =
      T2x2 ω S ha x y :=
    reduction_section_isometry ω S ha s hs x y
  have hginj : Function.Injective g := by
    intro x y h
    have h' : s x = s y := Subtype.ext h
    simpa only [hπ] using congrArg π h'
  let U := g.range
  let j : T2x20 ω S ≃ₗ[K] U := LinearEquiv.ofInjective g hginj
  have hj (x : T2x20 ω S) : (j x).val = g x := rfl
  have hUn : (ω.restrict U).Nondegenerate := by
    have hn := T2x13 ω S ha hω
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
  apply (T2x13 ω S ha hω).1
  intro z
  have hpair (a : ω.orthogonal S) (b : T2x20 ω S) :
      T2x2 ω S ha (π a) b = ω a.val (g b) := by
    calc
      _ = T2x2 ω S ha (π a) (π (s b)) := by rw [hπ]
      _ = _ := rfl
  have hegj (z : T2x20 ω S) : e (g z) = g (f z) := by
    have h := heU (j z)
    simpa only [fU,LinearEquiv.trans_apply,j.symm_apply_apply,hj] using h
  change T2x2 ω S ha (π y - f (π x)) z = 0
  rw [map_sub,LinearMap.sub_apply,sub_eq_zero]
  rw [hpair]
  calc
    ω y.val (g z) = ω (e x.val) (e (g (f.symm z))) := by
      rw [hxy,hegj,f.apply_symm_apply]
    _ = ω x.val (g (f.symm z)) := he _ _
    _ = T2x2 ω S ha (π x) (f.symm z) := (hpair x _).symm
    _ = T2x2 ω S ha (f (π x)) z := by
      simpa only [f.apply_symm_apply] using (hf (π x) (f.symm z)).symm
end QuotientExtension
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ReductionLaws
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E) (S : Submodule K E)
theorem reduceSubspace_map (e : E ≃ₗ[K] E)
    (f : T2x20 ω S ≃ₗ[K] T2x20 ω S)
    (hP : (ω.orthogonal S).map e.toLinearMap = ω.orthogonal S)
    (hQ : ∀ x y : ω.orthogonal S, e x.val = y.val →
      (T2x8 ω S).mkQ y = f ((T2x8 ω S).mkQ x))
    (L : Submodule K E) :
    T2x3 ω S (L.map e.toLinearMap) =
      (T2x3 ω S L).map f.toLinearMap := by
  ext z
  constructor
  · rintro ⟨y,⟨x,hx,hxy⟩,rfl⟩
    have hxP : x ∈ ω.orthogonal S := by
      have hyP : y.val ∈ (ω.orthogonal S).map e.toLinearMap := hP.symm ▸ y.property
      obtain ⟨x',hx',hx'y⟩ := hyP
      have heq : x' = x := e.injective (hx'y.trans hxy.symm)
      exact heq ▸ hx'
    refine ⟨(T2x8 ω S).mkQ ⟨x,hxP⟩,⟨⟨x,hxP⟩,hx,rfl⟩,?_⟩
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
variable [FiniteDimensional K E]
variable [Finite E]
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
  obtain ⟨L,hSL,hL⟩ := T2x72 ω ha S hS
  obtain ⟨M,hTM,hM⟩ := T2x72 ω ha T hT
  obtain ⟨eL,hEL,hωL⟩ := T2x21 ω L h2 ha hω hL
  obtain ⟨eM,hEM,hωM⟩ := T2x21 ω M h2 ha hω hM
  have hdim : finrank K L = finrank K M := by
    have h1 := T2x6 ω L hω hL
    have h2 := T2x6 ω M hω hM
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
      T2x5 (c x) (c y) = T2x5 x y := by
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
  have h1 := T2x6 ω L hω hL
  have h2 := T2x6 ω M hω hM
  apply (Submodule.isCompl_iff_disjoint L M (by omega)).mpr
  exact disjoint_iff.mpr hLM
theorem exists_transverse_pair_coordinates (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (L M : Submodule K E) (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M)
    (hLM : L ⊓ M = ⊥) :
    ∃ e : (L × Module.Dual K L) ≃ₗ[K] E,
      (∀ x, e x ∈ L ↔ x.2 = 0) ∧ (∀ x, e x ∈ M ↔ x.1 = 0) ∧
      ∀ x y, ω (e x) (e y) = T2x5 x y := by
  let p := (T2x29 ω L).comp M.subtype
  have hp : Function.Injective p := by
    apply (LinearMap.ker_eq_bot).mp
    apply (Submodule.eq_bot_iff _).mpr
    intro m hm
    apply Subtype.ext
    have hml : m.val ∈ L := (T2x80 ω L hL).le hm
    have hz : m.val ∈ L ⊓ M := ⟨hml,m.property⟩
    change m.val = 0
    simpa only [hLM,Submodule.mem_bot] using hz
  have hd : finrank K M = finrank K (Module.Dual K L) := by
    rw [Subspace.dual_finrank_eq]
    have h1 := T2x6 ω L hω hL
    have h2 := T2x6 ω M hω hM
    omega
  let f : M ≃ₗ[K] Module.Dual K L := LinearEquiv.ofBijective p
    ⟨hp,(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mp hp⟩
  let d := Submodule.prodEquivOfIsCompl L M (transverse_isCompl ω hω L M hL hM hLM)
  let e := ((LinearEquiv.refl K L).prodCongr f.symm).trans d
  have he (x : L × Module.Dual K L) : e x = x.1.val + (f.symm x.2).val := rfl
  have hproj (x : L × Module.Dual K L) : T2x29 ω L (e x) = x.2 := by
    rw [he,map_add]
    have hl : T2x29 ω L x.1.val = 0 :=
      (T2x80 ω L hL).ge x.1.property
    rw [hl,zero_add]
    exact f.apply_symm_apply x.2
  refine ⟨e, ?_, ?_, ?_⟩
  · intro x
    constructor
    · intro hx
      have hz : T2x29 ω L (e x) = 0 :=
        (T2x80 ω L hL).ge hx
      rwa [hproj] at hz
    · intro hx
      apply (T2x80 ω L hL).le
      change T2x29 ω L (e x) = 0
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
    have h1 := T2x6 ω L hω hL
    have h2 := T2x6 ω L' hω hL'
    omega
  let f : L ≃ₗ[K] L' := LinearEquiv.ofFinrankEq L L' hdim
  let c : (L × Module.Dual K L) ≃ₗ[K] (L' × Module.Dual K L') :=
    f.prodCongr f.symm.dualMap
  have hc (x y : L × Module.Dual K L) :
      T2x5 (c x) (c y) = T2x5 x y := by
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
theorem liftReduction_inf (T U : Submodule K (T2x20 ω S)) :
    T2x65 ω S (T ⊓ U) = T2x65 ω S T ⊓ T2x65 ω S U := by
  ext x
  simp only [T2x54,Submodule.mem_inf]
  tauto
theorem liftReduction_bot (hS : S ≤ ω.orthogonal S) :
    T2x65 ω S ⊥ = S := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxP,hxQ⟩ := (T2x54 ω S ⊥ x).mp hx
    exact (Submodule.Quotient.mk_eq_zero (T2x8 ω S)).mp hxQ
  · intro hx
    apply (T2x54 ω S ⊥ x).mpr
    refine ⟨hS hx, ?_⟩
    exact (Submodule.Quotient.mk_eq_zero (T2x8 ω S)).mpr hx
theorem reduced_pair_transverse (hS : S ≤ ω.orthogonal S)
    (L M : Submodule K E) (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M)
    (hLM : L ⊓ M = S) :
    T2x3 ω S L ⊓ T2x3 ω S M = ⊥ := by
  have hSL : S ≤ L := hLM.ge.trans inf_le_left
  have hSM : S ≤ M := hLM.ge.trans inf_le_right
  apply liftReduction_injective ω S
  rw [liftReduction_inf,lift_reduce ω S L hSL (T2x25 ω S L hL hSL),
    lift_reduce ω S M hSM (T2x25 ω S M hM hSM),
    liftReduction_bot ω S hS,hLM]
variable [FiniteDimensional K E]
theorem pair_transitivity_fixed_intersection (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (hS : S ≤ ω.orthogonal S) (L M L' M' : Submodule K E)
    (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M)
    (hL' : ω.orthogonal L' = L') (hM' : ω.orthogonal M' = M')
    (hLM : L ⊓ M = S) (hLM' : L' ⊓ M' = S) :
    ∃ e : E ≃ₗ[K] E, (∀ x y, ω (e x) (e y) = ω x y) ∧
      L.map e.toLinearMap = L' ∧ M.map e.toLinearMap = M' := by
  have hSL : S ≤ L := hLM.ge.trans inf_le_left
  have hSM : S ≤ M := hLM.ge.trans inf_le_right
  have hSL' : S ≤ L' := hLM'.ge.trans inf_le_left
  have hSM' : S ≤ M' := hLM'.ge.trans inf_le_right
  let Ω := T2x2 ω S ha
  have hΩa : Ω.IsAlt := T2x81 ω S ha
  have hΩ : Ω.Nondegenerate := T2x13 ω S ha hω
  obtain ⟨f,hf,hfL,hfM⟩ := transverse_pair_transitivity Ω hΩa hΩ
    (T2x3 ω S L) (T2x3 ω S M)
    (T2x3 ω S L') (T2x3 ω S M')
    (reduce_lagrangian ω S ha hS L hL hSL)
    (reduce_lagrangian ω S ha hS M hM hSM)
    (reduce_lagrangian ω S ha hS L' hL' hSL')
    (reduce_lagrangian ω S ha hS M' hM' hSM')
    (reduced_pair_transverse ω S hS L M hL hM hLM)
    (reduced_pair_transverse ω S hS L' M' hL' hM' hLM')
  obtain ⟨e,he,heS,heP,heQ⟩ := exists_reduction_isometry_extension ω S ha hω f hf
  have hSe : S.map e.toLinearMap = S := subspace_map_eq_of_fixed e S heS
  have hPe : (ω.orthogonal S).map e.toLinearMap = ω.orthogonal S := by
    rw [← T2x61 ω e he,hSe]
  have hmap (U W : Submodule K E) (hU : ω.orthogonal U = U)
      (hW : ω.orthogonal W = W) (hSU : S ≤ U) (hSW : S ≤ W)
      (hfU : (T2x3 ω S U).map f.toLinearMap = T2x3 ω S W) :
      U.map e.toLinearMap = W := by
    have hSUe : S ≤ U.map e.toLinearMap := by
      rw [← hSe]
      exact Submodule.map_mono hSU
    have hUe : ω.orthogonal (U.map e.toLinearMap) = U.map e.toLinearMap := by
      rw [T2x61 ω e he,hU]
    calc
      U.map e.toLinearMap = T2x65 ω S (T2x3 ω S (U.map e.toLinearMap)) :=
        (lift_reduce ω S _ hSUe (T2x25 ω S _ hUe hSUe)).symm
      _ = T2x65 ω S (T2x3 ω S W) := by
        rw [reduceSubspace_map ω S e f hPe heQ,hfU]
      _ = W := lift_reduce ω S W hSW (T2x25 ω S W hW hSW)
  exact ⟨e,he,hmap L L' hL hL' hSL hSL' hfL,hmap M M' hM hM' hSM hSM' hfM⟩
end PairReduction
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section OrderedPairTransitivity
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E] [Finite E]
variable (ω : LinearMap.BilinForm K E)
theorem ordered_pair_transitivity (h2 : (2 : K) ≠ 0) (ha : ω.IsAlt)
    (hω : ω.Nondegenerate) (L M L' M' : Submodule K E)
    (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M)
    (hL' : ω.orthogonal L' = L') (hM' : ω.orthogonal M' = M')
    (hdim : finrank K ↥(L ⊓ M) = finrank K ↥(L' ⊓ M')) :
    ∃ e : E ≃ₗ[K] E, (∀ x y, ω (e x) (e y) = ω x y) ∧
      L.map e.toLinearMap = L' ∧ M.map e.toLinearMap = M' := by
  have hi (U V : Submodule K E) (hU : ω.orthogonal U = U) :
      U ⊓ V ≤ ω.orthogonal (U ⊓ V) := by
    intro x hx y hy
    exact (hU.ge hx.1) y hy.1
  obtain ⟨e0,he0,hS⟩ := isotropic_transitivity ω h2 ha hω
    (L ⊓ M) (L' ⊓ M') (hi L M hL) (hi L' M' hL') hdim
  have hLe : ω.orthogonal (L.map e0.toLinearMap) = L.map e0.toLinearMap := by
    rw [T2x61 ω e0 he0,hL]
  have hMe : ω.orthogonal (M.map e0.toLinearMap) = M.map e0.toLinearMap := by
    rw [T2x61 ω e0 he0,hM]
  have hLM : L.map e0.toLinearMap ⊓ M.map e0.toLinearMap = L' ⊓ M' := by
    rw [← Submodule.map_inf e0.toLinearMap e0.injective,hS]
  obtain ⟨e1,he1,hL1,hM1⟩ := pair_transitivity_fixed_intersection ω (L' ⊓ M') ha hω
    (hi L' M' hL') (L.map e0.toLinearMap) (M.map e0.toLinearMap) L' M'
    hLe hMe hL' hM' hLM rfl
  refine ⟨e0.trans e1, ?_, ?_, ?_⟩
  · intro x y
    exact (he1 (e0 x) (e0 y)).trans (he0 x y)
  · change L.map (e1.toLinearMap.comp e0.toLinearMap) = L'
    rw [Submodule.map_comp,hL1]
  · change M.map (e1.toLinearMap.comp e0.toLinearMap) = M'
    rw [Submodule.map_comp,hM1]
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
@[simp] theorem reduceSubspace_self : T2x3 ω S S = ⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  rintro x ⟨y,hy,rfl⟩
  exact (Submodule.Quotient.mk_eq_zero (T2x8 ω S)).mpr hy
theorem reduceSubspace_inf (L N : Submodule K E) (hSL : S ≤ L) :
    T2x3 ω S (L ⊓ N) =
      T2x3 ω S L ⊓ T2x3 ω S N := by
  apply le_antisymm
  · rintro x ⟨y,hy,rfl⟩
    exact ⟨⟨y,hy.1,rfl⟩,⟨y,hy.2,rfl⟩⟩
  · rintro x ⟨⟨l,hl,hlx⟩,⟨n,hn,hnx⟩⟩
    have heq : (T2x8 ω S).mkQ (l-n) = 0 := by
      rw [map_sub,hlx,hnx,sub_self]
    have hln : l.val-n.val ∈ S :=
      (Submodule.Quotient.mk_eq_zero (T2x8 ω S)).mp heq
    have hnL : n.val ∈ L := by
      have h := L.sub_mem hl (hSL hln)
      simpa using h
    exact ⟨n,⟨hnL,hn⟩,hnx⟩
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
noncomputable def T2x1 (n : ℕ) : ℝ := (n+1) * 2^n
theorem T2x10 (n : ℕ) : 0 < T2x1 n := by
  unfold T2x1
  positivity
theorem lagrangian_card_upper :
    (Nat.card (Lagrangian (K := K) (V := V)) : ℝ) ≤
      T2x1 (finrank K V) * (Fintype.card K : ℝ)^((finrank K V+1).choose 2) := by
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
        mul_le_mul_of_nonneg_right (T2x26 k.val hk) (by positivity)
      _ = 2^k.val*q^(k.val*(n-k.val)+(k.val+1).choose 2) := by rw [pow_add]; ring
      _ ≤ 2^n*q^(n+1).choose 2 := mul_le_mul
        (pow_le_pow_right₀ (by norm_num) hk) (pow_le_pow_right₀ hq he) (by positivity) (by positivity)
  calc
    _ ≤ ∑ _k : Fin (n+1), 2^n*q^(n+1).choose 2 := by
      apply Finset.sum_le_sum
      intro k _
      simpa only [Nat.cast_mul,Nat.cast_pow] using hterm k
    _ = _ := by simp [T2x1,n,q]; ring
theorem lagrangian_card_lower :
    (Fintype.card K : ℝ)^((finrank K V+1).choose 2) ≤
      Nat.card (Lagrangian (K := K) (V := V)) := by
  let : Finite (Module.Dual K V) := Module.finite_of_finite K
  have h := Nat.card_le_card_of_injective (T2x28 (K := K) (V := V) (⊤ : Submodule K V))
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
abbrev T2x0 := {L : Submodule K E // ω.orthogonal L = L}
abbrev T2x15 (L M N : Submodule K E) :=
  {p : Submodule K E × Submodule K E × Submodule K E //
    ∃ e : E ≃ₗ[K] E, (∀ x y, ω (e x) (e y) = ω x y) ∧
      L.map e.toLinearMap = p.1 ∧ M.map e.toLinearMap = p.2.1 ∧
      N.map e.toLinearMap = p.2.2}
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
    T2x0 ω ≃ T2x0 η :=
  (Submodule.orderIsoMapComap e).toEquiv.subtypeEquiv (by
    intro U
    change ω.orthogonal U = U ↔ η.orthogonal (U.map e.toLinearMap) = U.map e.toLinearMap
    rw [orthogonal_map_isometry_between ω η e he]
    exact (Submodule.orderIsoMapComap e).injective.eq_iff.symm)
variable [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
 theorem T2x18 (h2 : (2 : K) ≠ 0)
    (ha : ω.IsAlt) (hω : ω.Nondegenerate) (D : ℕ) (hD : 2*D = finrank K E) :
    (Fintype.card K : ℝ)^((D+1).choose 2) ≤ Nat.card (T2x0 ω) ∧
      (Nat.card (T2x0 ω) : ℝ) ≤
        T2x1 D * (Fintype.card K : ℝ)^((D+1).choose 2) := by
  obtain ⟨L,_,hL⟩ := T2x72 ω ha ⊥ bot_le
  have hd : finrank K L = D := by
    have h := T2x6 ω L hω hL
    omega
  obtain ⟨e,_,he⟩ := T2x21 ω L h2 ha hω hL
  have hc := Nat.card_congr (symplecticLagrangianEquiv T2x5 ω e he)
  change Nat.card (Lagrangian (K := K) (V := L)) = _ at hc
  rw [←hc,←hd]
  exact ⟨lagrangian_card_lower,lagrangian_card_upper⟩
omit [Fintype K] in
 theorem T2x16 (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D = finrank K E) (S : Submodule K E)
    (hS : S ≤ ω.orthogonal S) : finrank K S ≤ D := by
  have h := ω.finrank_orthogonal hω S
  have hl := Submodule.finrank_mono hS
  omega
 theorem T2x76 (h2 : (2 : K) ≠ 0)
    (ha : ω.IsAlt) (hω : ω.Nondegenerate) (D : ℕ) (hD : 2*D = finrank K E)
    (S : Submodule K E) (hS : S ≤ ω.orthogonal S) :
    (Fintype.card K : ℝ)^((D-finrank K S+1).choose 2) ≤
        Nat.card {L : T2x0 ω // S ≤ L.val} ∧
      (Nat.card {L : T2x0 ω // S ≤ L.val} : ℝ) ≤
        T2x1 (D-finrank K S) *
          (Fintype.card K : ℝ)^((D-finrank K S+1).choose 2) := by
  let e : {L : T2x0 ω // S ≤ L.val} ≃
      {L : Submodule K E // ω.orthogonal L = L ∧ S ≤ L} :=
    { toFun := fun L => ⟨L.val.val,L.val.property,L.property⟩
      invFun := fun L => ⟨⟨L.val,L.property.1⟩,L.property.2⟩
      left_inv := fun L => rfl
      right_inv := fun L => rfl }
  have he := Nat.card_congr (e.trans (containingLagrangianEquiv ω S ha hS))
  have hc := reducedSpace_finrank ω S hω hS
  have hs := T2x16 ω hω D hD S hS
  let : Finite (T2x20 ω S) := Module.finite_of_finite K
  rw [he]
  exact T2x18 (T2x2 ω S ha) h2
    (T2x81 ω S ha) (T2x13 ω S ha hω)
    (D-finrank K S) (by omega)
abbrev T2x4 (c : ℕ) :=
  {S : Submodule K E // S ≤ ω.orthogonal S ∧ finrank K S = c}
noncomputable def isotropicIncidenceEquiv (c : ℕ) :
    (Σ S : T2x4 ω c, {L : T2x0 ω // S.val ≤ L.val}) ≃
    (Σ L : T2x0 ω, DimSubspace K L.val c) where
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
    Nat.card (Σ S : T2x4 ω c, {L : T2x0 ω // S.val ≤ L.val}) =
      Nat.card (Σ L : T2x0 ω, DimSubspace K L.val c) :=
  Nat.card_congr (isotropicIncidenceEquiv ω c)
end GenericCounts
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
def T2x19 (D c : ℕ) : ℕ :=
  (D+1).choose 2 + c*(D-c) - (D-c+1).choose 2
 theorem isotropicExponent_add (D c : ℕ) (hc : c ≤ D) :
    T2x19 D c + (D-c+1).choose 2 = (D+1).choose 2 + c*(D-c) := by
  have h := symmetric_nullity_exponent D c hc
  exact Nat.sub_add_cancel (by omega)
section IsotropicCounts
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
  [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
 theorem isotropic_card_bounds (h2 : (2 : K) ≠ 0)
    (ha : ω.IsAlt) (hω : ω.Nondegenerate) (D : ℕ) (hD : 2*D = finrank K E)
    (c : ℕ) (hc : c ≤ D) :
    (Fintype.card K : ℝ)^(T2x19 D c) ≤
        T2x1 (D-c) * Nat.card (T2x4 ω c) ∧
      (Nat.card (T2x4 ω c) : ℝ) ≤
        (T2x1 D * 2^c) * (Fintype.card K : ℝ)^(T2x19 D c) := by
  classical
  let := Fintype.ofFinite (T2x4 ω c)
  let := Fintype.ofFinite (T2x0 ω)
  let q : ℝ := Fintype.card K
  have hq : 0 < q := by
    dsimp [q]
    exact_mod_cast Fintype.card_pos (α := K)
  have hdim (L : T2x0 ω) : finrank K L.val = D := by
    have h := T2x6 ω L.val hω L.property
    omega
  have hs (S : T2x4 ω c) :=
    T2x76 ω h2 ha hω D hD S.val S.property.1
  have hs' (S : T2x4 ω c) :
      q^((D-c+1).choose 2) ≤ Nat.card {L : T2x0 ω // S.val ≤ L.val} ∧
      (Nat.card {L : T2x0 ω // S.val ≤ L.val} : ℝ) ≤
        T2x1 (D-c)*q^((D-c+1).choose 2) := by
    simpa only [S.property.2] using hs S
  have hsum : (∑ S : T2x4 ω c,
      (Nat.card {L : T2x0 ω // S.val ≤ L.val} : ℝ)) =
        ∑ L : T2x0 ω, (Nat.card (DimSubspace K L.val c) : ℝ) := by
    have h := isotropic_incidence_card ω c
    rw [Nat.card_sigma,Nat.card_sigma] at h
    exact_mod_cast h
  have hgrass (L : T2x0 ω) :
      q^(c*(D-c)) ≤ Nat.card (DimSubspace K L.val c) ∧
        (Nat.card (DimSubspace K L.val c) : ℝ) ≤ 2^c*q^(c*(D-c)) := by
    have hcL : c ≤ finrank K L.val := (hdim L).symm ▸ hc
    constructor
    · simpa only [hdim L] using subspace_count_lower (K := K) (V := L.val) c hcL
    · simpa only [hdim L] using T2x26 (K := K) (V := L.val) c hcL
  have hu : (Nat.card (T2x4 ω c) : ℝ)*q^((D-c+1).choose 2) ≤
      (Nat.card (T2x0 ω) : ℝ)*(2^c*q^(c*(D-c))) := by
    calc
      _ = ∑ _S : T2x4 ω c, q^((D-c+1).choose 2) := by
        simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card]
      _ ≤ ∑ S : T2x4 ω c,
          (Nat.card {L : T2x0 ω // S.val ≤ L.val} : ℝ) :=
        Finset.sum_le_sum (fun S _ => (hs' S).1)
      _ = _ := hsum
      _ ≤ ∑ _L : T2x0 ω, 2^c*q^(c*(D-c)) :=
        Finset.sum_le_sum (fun L _ => (hgrass L).2)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card]
  have hl : (Nat.card (T2x0 ω) : ℝ)*q^(c*(D-c)) ≤
      (Nat.card (T2x4 ω c) : ℝ)*(T2x1 (D-c)*q^((D-c+1).choose 2)) := by
    calc
      _ = ∑ _L : T2x0 ω, q^(c*(D-c)) := by
        simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card]
      _ ≤ ∑ L : T2x0 ω, (Nat.card (DimSubspace K L.val c) : ℝ) :=
        Finset.sum_le_sum (fun L _ => (hgrass L).1)
      _ = _ := hsum.symm
      _ ≤ ∑ _S : T2x4 ω c, T2x1 (D-c)*q^((D-c+1).choose 2) :=
        Finset.sum_le_sum (fun S _ => (hs' S).2)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card]
  have hlag := T2x18 ω h2 ha hω D hD
  have he : q^(T2x19 D c)*q^((D-c+1).choose 2) =
      q^((D+1).choose 2)*q^(c*(D-c)) := by
    rw [←pow_add,isotropicExponent_add D c hc,pow_add]
  constructor
  · apply (mul_le_mul_iff_left₀ (pow_pos hq ((D-c+1).choose 2))).mp
    calc
      _ = q^((D+1).choose 2)*q^(c*(D-c)) := he
      _ ≤ (Nat.card (T2x0 ω) : ℝ)*q^(c*(D-c)) :=
        mul_le_mul_of_nonneg_right hlag.1 (by positivity)
      _ ≤ _ := hl
      _ = _ := by ring
  · apply (mul_le_mul_iff_left₀ (pow_pos hq ((D-c+1).choose 2))).mp
    calc
      _ ≤ _ := hu
      _ ≤ (T2x1 D*q^((D+1).choose 2))*(2^c*q^(c*(D-c))) :=
        mul_le_mul_of_nonneg_right hlag.2 (by positivity)
      _ = (T2x1 D*2^c)*(q^((D+1).choose 2)*q^(c*(D-c))) := by ring
      _ = _ := by rw [←he]; ring
end IsotropicCounts
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
 theorem lagrangianConstant_mono : Monotone T2x1 := by
  intro m n h
  unfold T2x1
  exact mul_le_mul (by exact_mod_cast Nat.add_le_add_right h 1)
    (pow_le_pow_right₀ (by norm_num) h) (by positivity) (by positivity)
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
 theorem T2x31 (U : Submodule K E) (e f : E ≃ₗ[K] E) :
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
abbrev T2x14 (U V W : Submodule K E) :=
  {p : Submodule K E × Submodule K E × Submodule K E // ∃ e : E ≃ₗ[K] E,
    U.map e.toLinearMap = p.1 ∧ V.map e.toLinearMap = p.2.1 ∧ W.map e.toLinearMap = p.2.2}
abbrev T2x48 (U V W : Submodule K E) :=
  {e : E ≃ₗ[K] E // U.map e.toLinearMap = U ∧ V.map e.toLinearMap = V ∧ W.map e.toLinearMap = W}
def tripleLinearOrbitMap (U V W : Submodule K E) (e : E ≃ₗ[K] E) : T2x14 U V W :=
  ⟨(U.map e.toLinearMap,V.map e.toLinearMap,W.map e.toLinearMap),e,rfl,rfl,rfl⟩
noncomputable def tripleLinearOrbitFiberEquiv (U V W : Submodule K E) (p : T2x14 U V W) :
    {e : E ≃ₗ[K] E // tripleLinearOrbitMap U V W e = p} ≃ T2x48 U V W := by
  classical
  let e₀ := p.property.choose
  have hU := p.property.choose_spec.1
  have hV := p.property.choose_spec.2.1
  have hW := p.property.choose_spec.2.2
  have hm (e : {e : E ≃ₗ[K] E // tripleLinearOrbitMap U V W e = p}) :
      U.map e.val.toLinearMap = p.val.1 ∧ V.map e.val.toLinearMap = p.val.2.1 ∧
        W.map e.val.toLinearMap = p.val.2.2 := by
    exact ⟨congrArg (fun a : T2x14 U V W => a.val.1) e.property,
      congrArg (fun a : T2x14 U V W => a.val.2.1) e.property,
      congrArg (fun a : T2x14 U V W => a.val.2.2) e.property⟩
  refine
    { toFun := fun e => ⟨e.val.trans e₀.symm,?_,?_,?_⟩
      invFun := fun e => ⟨e.val.trans e₀,?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · rw [T2x31,(hm _).1,←hU,submodule_map_symm_cancel]
  · rw [T2x31,(hm _).2.1,←hV,submodule_map_symm_cancel]
  · rw [T2x31,(hm _).2.2,←hW,submodule_map_symm_cancel]
  · apply Subtype.ext
    apply Prod.ext
    · change U.map (‹T2x48 U V W›.val.trans e₀).toLinearMap = p.val.1
      rw [T2x31]
      exact (congrArg (Submodule.map e₀.toLinearMap) ‹T2x48 U V W›.property.1).trans hU
    · apply Prod.ext
      · change V.map (‹T2x48 U V W›.val.trans e₀).toLinearMap = p.val.2.1
        rw [T2x31]
        exact (congrArg (Submodule.map e₀.toLinearMap) ‹T2x48 U V W›.property.2.1).trans hV
      · change W.map (‹T2x48 U V W›.val.trans e₀).toLinearMap = p.val.2.2
        rw [T2x31]
        exact (congrArg (Submodule.map e₀.toLinearMap) ‹T2x48 U V W›.property.2.2).trans hW
  · intro e
    apply Subtype.ext
    ext x
    simp
  · intro e
    apply Subtype.ext
    ext x
    simp
noncomputable def tripleLinearStabilizerRestriction (U V W : Submodule K E) :
    T2x48 U V W → (U ≃ₗ[K] U) × (V ≃ₗ[K] V) × (W ≃ₗ[K] W) := fun e =>
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
    Nat.card (T2x14 U V W) *
      (Nat.card (U ≃ₗ[K] U)*(Nat.card (V ≃ₗ[K] V)*Nat.card (W ≃ₗ[K] W))) = Nat.card (E ≃ₗ[K] E) := by
  classical
  let := Fintype.ofFinite (T2x14 U V W)
  have hc : Nat.card (T2x48 U V W) =
      Nat.card (U ≃ₗ[K] U)*(Nat.card (V ≃ₗ[K] V)*Nat.card (W ≃ₗ[K] W)) := by
    rw [Nat.card_congr (Equiv.ofBijective _ (tripleLinearStabilizerRestriction_bijective U V W hU hVW)),
      Nat.card_prod,Nat.card_prod]
  have he := (Nat.card_congr (Equiv.sigmaFiberEquiv (tripleLinearOrbitMap U V W))).symm
  rw [Nat.card_sigma] at he
  have hf (p : T2x14 U V W) : Nat.card {e : E ≃ₗ[K] E // tripleLinearOrbitMap U V W e = p} =
      Nat.card (U ≃ₗ[K] U)*(Nat.card (V ≃ₗ[K] V)*Nat.card (W ≃ₗ[K] W)) :=
    (Nat.card_congr (tripleLinearOrbitFiberEquiv U V W p)).trans hc
  simpa only [hf,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card,Nat.cast_id] using he.symm
variable [Fintype K]
 theorem tripleLinearOrbit_card_bounds (U V W : Submodule K E)
    (hU : IsCompl U (V ⊔ W)) (hVW : Disjoint V W) :
    (Fintype.card K : ℝ)^(2*(finrank K U*finrank K V+finrank K U*finrank K W+finrank K V*finrank K W)) ≤
      2^(finrank K E)*(Nat.card (T2x14 U V W) : ℝ) ∧
    (Nat.card (T2x14 U V W) : ℝ) ≤
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
  have hi : (Nat.card (T2x14 U V W) : ℝ)*
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
      _ = 2^n*((Nat.card (T2x14 U V W) : ℝ)*
          ((Nat.card (U ≃ₗ[K] U) : ℝ)*(Nat.card (V ≃ₗ[K] V)*Nat.card (W ≃ₗ[K] W)))) := by rw [hi]
      _ ≤ 2^n*((Nat.card (T2x14 U V W) : ℝ)*(q^(u*u)*(q^(v*v)*q^(w*w)))) := by gcongr
      _ = _ := by simp only [pow_add]; ring
  · apply (mul_le_mul_iff_left₀ (pow_pos hq (u*u+(v*v+w*w)))).mp
    calc
      _ = (Nat.card (T2x14 U V W) : ℝ)*(q^(u*u)*(q^(v*v)*q^(w*w))) := by simp only [pow_add]
      _ ≤ (Nat.card (T2x14 U V W) : ℝ)*((2^u*Nat.card (U ≃ₗ[K] U))*((2^v*Nat.card (V ≃ₗ[K] V))*(2^w*Nat.card (W ≃ₗ[K] W)))) := by gcongr
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
variable (ω : LinearMap.BilinForm K E) (L M N : T2x0 ω)
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
 theorem exists_isotropic_isometry_extension (h2 : (2 : K) ≠ 0) (ha : ω.IsAlt)
    (hω : ω.Nondegenerate) (S T : Submodule K E)
    (hS : S ≤ ω.orthogonal S) (hT : T ≤ ω.orthogonal T) (g : S ≃ₗ[K] T) :
    ∃ e : E ≃ₗ[K] E, (∀ x y, ω (e x) (e y) = ω x y) ∧
      ∀ x : S, e x.val = (g x).val := by
  obtain ⟨L,hSL,hL⟩ := T2x72 ω ha S hS
  obtain ⟨M,hTM,hM⟩ := T2x72 ω ha T hT
  obtain ⟨eL,hEL,hωL⟩ := T2x21 ω L h2 ha hω hL
  obtain ⟨eM,hEM,hωM⟩ := T2x21 ω M h2 ha hω hM
  have hdim : finrank K L = finrank K M := by
    have h1 := T2x6 ω L hω hL
    have h2 := T2x6 ω M hω hM
    omega
  let U := S.comap L.subtype
  let W := T.comap M.subtype
  let g₀ : U ≃ₗ[K] W := (Submodule.comapSubtypeEquivOfLe hSL).trans
    (g.trans (Submodule.comapSubtypeEquivOfLe hTM).symm)
  obtain ⟨f,hf⟩ := exists_linearEquiv_extension U W hdim g₀
  let c : (L × Module.Dual K L) ≃ₗ[K] (M × Module.Dual K M) := f.prodCongr f.symm.dualMap
  have hc (x y : L × Module.Dual K L) :
      T2x5 (c x) (c y) = T2x5 x y := by
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
variable (ω : LinearMap.BilinForm K E) (L M N : T2x0 ω)
variable [FiniteDimensional K E]
variable (ha : ω.IsAlt) (hω : ω.Nondegenerate)
end FixedPairs
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ConfigurationOrbit
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E)
 theorem T2x39 (S T U : Submodule K E) (hU : U ≤ S)
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
    ∃ f : T2x4 ω (finrank K S) ×
      T2x14 (U.comap S.subtype) (V.comap S.subtype) (W.comap S.subtype) →
        T2x15 ω U V W, Function.Injective f := by
  classical
  have ht (T : T2x4 ω (finrank K S)) := isotropic_transitivity ω h2 ha hω
    S T.val hS T.property.1 T.property.2.symm
  let e (T : T2x4 ω (finrank K S)) := (ht T).choose
  have he (T) := (ht T).choose_spec
  have hgood (T : T2x4 ω (finrank K S))
      (p : T2x14 (U.comap S.subtype) (V.comap S.subtype) (W.comap S.subtype)) :
      ∃ f : E ≃ₗ[K] E, (∀ x y, ω (f x) (f y) = ω x y) ∧
        U.map f.toLinearMap = (p.val.1.map S.subtype).map (e T).toLinearMap ∧
        V.map f.toLinearMap = (p.val.2.1.map S.subtype).map (e T).toLinearMap ∧
        W.map f.toLinearMap = (p.val.2.2.map S.subtype).map (e T).toLinearMap := by
    obtain ⟨g,hgU,hgV,hgW⟩ := p.property
    obtain ⟨r,hr,hrg⟩ := exists_isotropic_isometry_extension ω h2 ha hω S S hS hS g
    refine ⟨r.trans (e T),?_,?_,?_,?_⟩
    · intro x y
      exact ((he T).1 (r x) (r y)).trans (hr x y)
    · rw [T2x31,T2x39 S S U hU r g hrg,hgU]
    · rw [T2x31,T2x39 S S V hV r g hrg,hgV]
    · rw [T2x31,T2x39 S S W hW r g hrg,hgW]
  let f : T2x4 ω (finrank K S) ×
      T2x14 (U.comap S.subtype) (V.comap S.subtype) (W.comap S.subtype) →
        T2x15 ω U V W := fun p =>
    ⟨((p.2.val.1.map S.subtype).map (e p.1).toLinearMap,
      (p.2.val.2.1.map S.subtype).map (e p.1).toLinearMap,
      (p.2.val.2.2.map S.subtype).map (e p.1).toLinearMap),hgood p.1 p.2⟩
  have hsum' (p : T2x14 (U.comap S.subtype) (V.comap S.subtype) (W.comap S.subtype)) :
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
    exact (hrecover (T,p)).symm.trans ((congrArg (fun x : T2x15 ω U V W =>
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
variable (ω : LinearMap.BilinForm K E) (L M N : T2x0 ω)
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
theorem pair_cost_cancellation (D u v w : ℕ) (h : u+v+w ≤ D) :
    T2x19 D (u+v+w) + 2*(u*v+u*w+v*w) +
      ((D-(u+v)+1).choose 2 + (D-(u+w)+1).choose 2 + (D-(v+w)+1).choose 2) +
      ((u+1).choose 2 + (v+1).choose 2 + (w+1).choose 2) = 3*(D+1).choose 2 := by
  have hu : u+v ≤ D := by omega
  have hv : u+w ≤ D := by omega
  have hw : v+w ≤ D := by omega
  have hi := isotropicExponent_add D (u+v+w) h
  have hi' : (T2x19 D (u+v+w) : ℚ) =
      ((D+1).choose 2 : ℚ) + (u+v+w)*(D-(u+v+w)) - ((D-(u+v+w)+1).choose 2 : ℚ) := by
    have hiq := congrArg (fun x : ℕ => (x:ℚ)) hi
    simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_sub h] at hiq
    linarith
  apply @Nat.cast_injective ℚ
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,hi',Nat.cast_choose_two,Nat.cast_one,
    Nat.cast_sub hu,Nat.cast_sub hv,Nat.cast_sub hw,Nat.cast_sub h]
  ring
theorem common_cost_cancellation (D c : ℕ) (hc : c ≤ D) :
    T2x19 D c + 3*(D-c+1).choose 2 + (D+1)*c = 3*(D+1).choose 2 := by
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
noncomputable def pairOrbitConstant (D : ℕ) : ℝ :=
  (T2x1 D*2^D)*(8*(4^D*T2x1 D^2))
 theorem pairOrbitConstant_pos (D : ℕ) : 0 < pairOrbitConstant D := by
  unfold pairOrbitConstant
  have h := T2x10 D
  positivity
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
 theorem reduceSubspace_finrank_containing (S A : Submodule K E)
    (hSA : S ≤ A) (hAP : A ≤ ω.orthogonal S) :
    finrank K (T2x3 ω S A) + finrank K S = finrank K A := by
  let f : A →ₗ[K] T2x20 ω S := (T2x8 ω S).mkQ.comp (Submodule.inclusion hAP)
  have hk : LinearMap.ker f = S.comap A.subtype := by
    ext x
    exact Submodule.Quotient.mk_eq_zero (T2x8 ω S)
  have hr : LinearMap.range f = T2x3 ω S A := by
    ext y
    constructor
    · rintro ⟨x,rfl⟩
      exact ⟨⟨x.val,hAP x.property⟩,x.property,rfl⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨⟨x.val,hx⟩,rfl⟩
  have hh := f.finrank_range_add_finrank_ker
  rw [hk,hr,(Submodule.comapSubtypeEquivOfLe hSA).finrank_eq] at hh
  exact hh
noncomputable def T2x53 (S : Submodule K E) (ha : ω.IsAlt)
    (hS : S ≤ ω.orthogonal S) (L : T2x0 ω) (hSL : S ≤ L.val) :
    T2x0 (T2x2 ω S ha) :=
  ⟨T2x3 ω S L.val,reduce_lagrangian ω S ha hS L.val L.property hSL⟩
variable [Finite E]
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
noncomputable def orbitMassConstant (D : ℕ) : ℝ := T2x1 D*pairOrbitConstant D
 theorem orbitMassConstant_pos (D : ℕ) : 0 < orbitMassConstant D :=
  mul_pos (T2x10 D) (pairOrbitConstant_pos D)
def TB2_Good (D : ℕ) : Prop := ∀ L M N : T2x0 ω,
    (Fintype.card K : ℝ)^(3*(D+1).choose 2) ≤
      orbitMassConstant D * (Fintype.card K : ℝ)^(tripleDefect D L.val M.val N.val) *
        Nat.card (T2x15 ω L.val M.val N.val)
end AllOrbitMass
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ConfigurationUpper
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Finite E]
variable (ω : LinearMap.BilinForm K E)
 theorem triple_subspace_orbit_surjection (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (S U V W : Submodule K E) (hS : S ≤ ω.orthogonal S)
    (hU : U ≤ S) (hV : V ≤ S) (hW : W ≤ S) (_hsum : U ⊔ V ⊔ W = S) :
    ∃ f : T2x4 ω (finrank K S) ×
      T2x14 (U.comap S.subtype) (V.comap S.subtype) (W.comap S.subtype) →
        T2x15 ω U V W, Function.Surjective f := by
  classical
  have ht (T : T2x4 ω (finrank K S)) := isotropic_transitivity ω h2 ha hω
    S T.val hS T.property.1 T.property.2.symm
  let e (T : T2x4 ω (finrank K S)) := (ht T).choose
  have he (T) := (ht T).choose_spec
  have hgood (T : T2x4 ω (finrank K S))
      (p : T2x14 (U.comap S.subtype) (V.comap S.subtype) (W.comap S.subtype)) :
      ∃ f : E ≃ₗ[K] E, (∀ x y, ω (f x) (f y) = ω x y) ∧
        U.map f.toLinearMap = (p.val.1.map S.subtype).map (e T).toLinearMap ∧
        V.map f.toLinearMap = (p.val.2.1.map S.subtype).map (e T).toLinearMap ∧
        W.map f.toLinearMap = (p.val.2.2.map S.subtype).map (e T).toLinearMap := by
    obtain ⟨g,hgU,hgV,hgW⟩ := p.property
    obtain ⟨r,hr,hrg⟩ := exists_isotropic_isometry_extension ω h2 ha hω S S hS hS g
    refine ⟨r.trans (e T),?_,?_,?_,?_⟩
    · intro x y
      exact ((he T).1 (r x) (r y)).trans (hr x y)
    · rw [T2x31,T2x39 S S U hU r g hrg,hgU]
    · rw [T2x31,T2x39 S S V hV r g hrg,hgV]
    · rw [T2x31,T2x39 S S W hW r g hrg,hgW]
  let f : T2x4 ω (finrank K S) ×
      T2x14 (U.comap S.subtype) (V.comap S.subtype) (W.comap S.subtype) →
        T2x15 ω U V W := fun p =>
    ⟨((p.2.val.1.map S.subtype).map (e p.1).toLinearMap,
      (p.2.val.2.1.map S.subtype).map (e p.1).toLinearMap,
      (p.2.val.2.2.map S.subtype).map (e p.1).toLinearMap),hgood p.1 p.2⟩
  refine ⟨f,?_⟩
  intro p
  obtain ⟨g,hg,hgU,hgV,hgW⟩ := p.property
  have hT : S.map g.toLinearMap ≤ ω.orthogonal (S.map g.toLinearMap) := by
    rw [T2x61 ω g hg]
    exact Submodule.map_mono hS
  let T : T2x4 ω (finrank K S) :=
    ⟨S.map g.toLinearMap,hT,g.finrank_map_eq S⟩
  let r := g.trans (e T).symm
  have hrS : S.map r.toLinearMap = S := by
    rw [T2x31]
    change T.val.map (e T).symm.toLinearMap = S
    rw [←(he T).2,submodule_map_symm_cancel]
  let rS : S ≃ₗ[K] S := r.ofSubmodules S S hrS
  let q := tripleLinearOrbitMap (U.comap S.subtype) (V.comap S.subtype) (W.comap S.subtype) rS
  have heq : r.trans (e T) = g := by
    ext x
    simp only [r,LinearEquiv.trans_apply,LinearEquiv.apply_symm_apply]
  have hmap (A : Submodule K E) (hA : A ≤ S) :
      ((((A.comap S.subtype).map rS.toLinearMap).map S.subtype).map (e T).toLinearMap) = A.map g.toLinearMap := by
    rw [←T2x39 S S A hA r rS (fun _ => rfl),←T2x31,heq]
  refine ⟨(T,q),Subtype.ext ?_⟩
  change (((((U.comap S.subtype).map rS.toLinearMap).map S.subtype).map (e T).toLinearMap),
    ((((V.comap S.subtype).map rS.toLinearMap).map S.subtype).map (e T).toLinearMap),
    ((((W.comap S.subtype).map rS.toLinearMap).map S.subtype).map (e T).toLinearMap)) = p.val
  rw [hmap U hU,hmap V hV,hmap W hW,hgU,hgV,hgW]
 theorem triple_subspace_orbit_card_identity (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (S U V W : Submodule K E) (hS : S ≤ ω.orthogonal S)
    (hU : U ≤ S) (hV : V ≤ S) (hW : W ≤ S) (hsum : U ⊔ V ⊔ W = S) :
    Nat.card (T2x15 ω U V W) = Nat.card (T2x4 ω (finrank K S)) *
      Nat.card (T2x14 (U.comap S.subtype) (V.comap S.subtype) (W.comap S.subtype)) := by
  apply le_antisymm
  · obtain ⟨f,hf⟩ := triple_subspace_orbit_surjection ω h2 ha hω S U V W hS hU hV hW hsum
    simpa only [Nat.card_prod] using Nat.card_le_card_of_surjective f hf
  · obtain ⟨f,hf⟩ := triple_subspace_orbit_injection ω h2 ha hω S U V W hS hU hV hW hsum
    simpa only [Nat.card_prod] using Nat.card_le_card_of_injective f hf
end ConfigurationUpper
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section DecompositionTransitivity
variable {K E F : Type*} [Field K] [AddCommGroup E] [Module K E] [AddCommGroup F] [Module K F]
 theorem subspace_map_eq_of_restriction_equiv (U : Submodule K E) (V : Submodule K F)
    (e : E ≃ₗ[K] F) (g : U ≃ₗ[K] V) (h : ∀ x : U, e x.val = (g x).val) :
    U.map e.toLinearMap = V := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    change e (⟨x,hx⟩ : U).val ∈ V
    rw [h ⟨x,hx⟩]
    exact (g ⟨x,hx⟩).property
  · intro hy
    obtain ⟨x,hx⟩ := g.surjective ⟨y,hy⟩
    exact ⟨x.val,x.property,(h x).trans (congrArg Subtype.val hx)⟩
variable [FiniteDimensional K E] [FiniteDimensional K F]
 theorem triple_decomposition_equiv (U V W : Submodule K E) (U' V' W' : Submodule K F)
    (hU : IsCompl U (V ⊔ W)) (hVW : Disjoint V W)
    (hU' : IsCompl U' (V' ⊔ W')) (hVW' : Disjoint V' W')
    (hu : finrank K U = finrank K U') (hv : finrank K V = finrank K V') (hw : finrank K W = finrank K W') :
    ∃ e : E ≃ₗ[K] F, U.map e.toLinearMap = U' ∧ V.map e.toLinearMap = V' ∧ W.map e.toLinearMap = W' := by
  let gu := LinearEquiv.ofFinrankEq U U' hu
  let gv := LinearEquiv.ofFinrankEq V V' hv
  let gw := LinearEquiv.ofFinrankEq W W' hw
  let a := tripleSumEquiv U V W hU hVW
  let b := tripleSumEquiv U' V' W' hU' hVW'
  let e := a.symm.trans ((gu.prodCongr (gv.prodCongr gw)).trans b)
  have heU (x : U) : e x.val = (gu x).val := by
    have hax : a (x,(0,0)) = x.val := by simp [a]
    rw [←hax]
    simp [e,b]
  have heV (x : V) : e x.val = (gv x).val := by
    have hax : a (0,(x,0)) = x.val := by simp [a]
    rw [←hax]
    simp [e,b]
  have heW (x : W) : e x.val = (gw x).val := by
    have hax : a (0,(0,x)) = x.val := by simp [a]
    rw [←hax]
    simp [e,b]
  exact ⟨e,subspace_map_eq_of_restriction_equiv U U' e gu heU,
    subspace_map_eq_of_restriction_equiv V V' e gv heV,subspace_map_eq_of_restriction_equiv W W' e gw heW⟩
end DecompositionTransitivity
section ConfigTransitivity
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Finite E]
variable (ω : LinearMap.BilinForm K E)
 omit [Finite E] in
 theorem triple_comap_isCompl (S U V W : Submodule K E)
    (hU : U ≤ S) (hV : V ≤ S) (hW : W ≤ S)
    (hsum : U ⊔ V ⊔ W = S) (hdis : Disjoint U (V ⊔ W)) :
    IsCompl (U.comap S.subtype) (V.comap S.subtype ⊔ W.comap S.subtype) := by
  constructor
  · apply disjoint_iff.mpr
    rw [←subspace_comap_sup_of_le S V W hV hW,←Submodule.comap_inf,disjoint_iff.mp hdis]
    simp
  · apply codisjoint_iff.mpr
    rw [←sup_assoc,←subspace_comap_sup_of_le S U V hU hV,
      ←subspace_comap_sup_of_le S (U ⊔ V) W (sup_le hU hV) hW,hsum]
    simp
 theorem triple_isotropic_config_transitivity (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (U V W U' V' W' : Submodule K E)
    (hS : U ⊔ V ⊔ W ≤ ω.orthogonal (U ⊔ V ⊔ W))
    (hS' : U' ⊔ V' ⊔ W' ≤ ω.orthogonal (U' ⊔ V' ⊔ W'))
    (hdis : Disjoint U (V ⊔ W)) (hVW : Disjoint V W)
    (hdis' : Disjoint U' (V' ⊔ W')) (hVW' : Disjoint V' W')
    (hu : finrank K U = finrank K U') (hv : finrank K V = finrank K V') (hw : finrank K W = finrank K W') :
    TripleIsometry ω ω U V W U' V' W' := by
  let S := U ⊔ V ⊔ W
  let T := U' ⊔ V' ⊔ W'
  have hU : U ≤ S := le_sup_of_le_left le_sup_left
  have hV : V ≤ S := le_sup_of_le_left le_sup_right
  have hW : W ≤ S := le_sup_right
  have hU' : U' ≤ T := le_sup_of_le_left le_sup_left
  have hV' : V' ≤ T := le_sup_of_le_left le_sup_right
  have hW' : W' ≤ T := le_sup_right
  have hd : Disjoint (V.comap S.subtype) (W.comap S.subtype) := by
    apply disjoint_iff.mpr
    rw [←Submodule.comap_inf,hVW.eq_bot]
    simp
  have hd' : Disjoint (V'.comap T.subtype) (W'.comap T.subtype) := by
    apply disjoint_iff.mpr
    rw [←Submodule.comap_inf,hVW'.eq_bot]
    simp
  obtain ⟨g,hgU,hgV,hgW⟩ := triple_decomposition_equiv
    (U.comap S.subtype) (V.comap S.subtype) (W.comap S.subtype)
    (U'.comap T.subtype) (V'.comap T.subtype) (W'.comap T.subtype)
    (triple_comap_isCompl S U V W hU hV hW rfl hdis) hd
    (triple_comap_isCompl T U' V' W' hU' hV' hW' rfl hdis') hd'
    (by rw [(Submodule.comapSubtypeEquivOfLe hU).finrank_eq,(Submodule.comapSubtypeEquivOfLe hU').finrank_eq]; exact hu)
    (by rw [(Submodule.comapSubtypeEquivOfLe hV).finrank_eq,(Submodule.comapSubtypeEquivOfLe hV').finrank_eq]; exact hv)
    (by rw [(Submodule.comapSubtypeEquivOfLe hW).finrank_eq,(Submodule.comapSubtypeEquivOfLe hW').finrank_eq]; exact hw)
  obtain ⟨e,he,heg⟩ := exists_isotropic_isometry_extension ω h2 ha hω S T hS hS' g
  refine ⟨e,he,?_,?_,?_⟩
  · rw [T2x39 S T U hU e g heg,hgU,subtype_map_comap_of_le T U' hU']
  · rw [T2x39 S T V hV e g heg,hgV,subtype_map_comap_of_le T V' hV']
  · rw [T2x39 S T W hW e g heg,hgW,subtype_map_comap_of_le T W' hW']
end ConfigTransitivity
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ConfigurationBound
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
 theorem triple_isotropic_orbit_card_upper (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D = finrank K E)
    (S U V W : Submodule K E) (hS : S ≤ ω.orthogonal S)
    (hU : U ≤ S) (hV : V ≤ S) (hW : W ≤ S) (hsum : U ⊔ V ⊔ W = S)
    (hdis : Disjoint U (V ⊔ W)) (hVW : Disjoint V W) :
    (Nat.card (T2x15 ω U V W) : ℝ) ≤
      (T2x1 D * 4^D) * (Fintype.card K : ℝ)^(T2x19 D (finrank K S) +
        2*(finrank K U*finrank K V+finrank K U*finrank K W+finrank K V*finrank K W)) := by
  have hconst := T2x10 D
  let U' := U.comap S.subtype
  let V' := V.comap S.subtype
  let W' := W.comap S.subtype
  have hc : IsCompl U' (V' ⊔ W') := triple_comap_isCompl S U V W hU hV hW hsum hdis
  have hvw : Disjoint V' W' := by
    apply disjoint_iff.mpr
    change V.comap S.subtype ⊓ W.comap S.subtype = ⊥
    rw [←Submodule.comap_inf,disjoint_iff.mp hVW]
    simp
  have hu' : finrank K U' = finrank K U := (Submodule.comapSubtypeEquivOfLe hU).finrank_eq
  have hv' : finrank K V' = finrank K V := (Submodule.comapSubtypeEquivOfLe hV).finrank_eq
  have hw' : finrank K W' = finrank K W := (Submodule.comapSubtypeEquivOfLe hW).finrank_eq
  have hb := (tripleLinearOrbit_card_bounds U' V' W' hc hvw).2
  rw [hu',hv',hw'] at hb
  have hs := T2x16 ω hω D hD S hS
  have hi := (isotropic_card_bounds ω h2 ha hω D hD (finrank K S) hs).2
  have hk : (2:ℝ)^(finrank K S) * 2^(finrank K S) ≤ 4^D := by
    calc
      _ = (4:ℝ)^(finrank K S) := by rw [←mul_pow]; norm_num
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) hs
  rw [triple_subspace_orbit_card_identity ω h2 ha hω S U V W hS hU hV hW hsum,Nat.cast_mul]
  calc
    _ ≤ ((T2x1 D*2^(finrank K S))*(Fintype.card K : ℝ)^T2x19 D (finrank K S)) *
      (2^(finrank K S)*(Fintype.card K : ℝ)^(2*(finrank K U*finrank K V+finrank K U*finrank K W+finrank K V*finrank K W))) :=
        mul_le_mul hi hb (Nat.cast_nonneg _) (by positivity)
    _ = (T2x1 D*(2^(finrank K S)*2^(finrank K S))) * (Fintype.card K : ℝ)^(T2x19 D (finrank K S) +
        2*(finrank K U*finrank K V+finrank K U*finrank K W+finrank K V*finrank K W)) := by rw [pow_add]; ring
    _ ≤ _ := by gcongr
end ConfigurationBound
section CommonZeroProfiles
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E)
abbrev T2x30 (L M N : T2x0 ω) :=
  {p : T2x0 ω × T2x0 ω × T2x0 ω //
    (p.1.val ⊓ p.2.1.val) ⊓ p.2.2.val = ⊥ ∧
    finrank K ↥(p.1.val ⊓ p.2.1.val) = finrank K ↥(L.val ⊓ M.val) ∧
    finrank K ↥(p.1.val ⊓ p.2.2.val) = finrank K ↥(L.val ⊓ N.val) ∧
    finrank K ↥(p.2.1.val ⊓ p.2.2.val) = finrank K ↥(M.val ⊓ N.val)}
variable [Finite E]
 omit [FiniteDimensional K E] in
 theorem commonZeroProfile_injection (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (L M N : T2x0 ω) (h0 : (L.val ⊓ M.val) ⊓ N.val = ⊥) :
    ∃ f : T2x30 ω L M N →
      T2x15 ω (L.val ⊓ M.val) (L.val ⊓ N.val) (M.val ⊓ N.val) ×
      {P : T2x0 ω // (L.val ⊓ M.val) ⊔ (L.val ⊓ N.val) ≤ P.val} ×
      {P : T2x0 ω // (L.val ⊓ M.val) ⊔ (M.val ⊓ N.val) ≤ P.val} ×
      {P : T2x0 ω // (L.val ⊓ N.val) ⊔ (M.val ⊓ N.val) ≤ P.val},
      Function.Injective f := by
  classical
  let O := T2x15 ω (L.val ⊓ M.val) (L.val ⊓ N.val) (M.val ⊓ N.val)
  have ht (p : T2x30 ω L M N) :
      TripleIsometry ω ω (L.val ⊓ M.val) (L.val ⊓ N.val) (M.val ⊓ N.val)
        (p.val.1.val ⊓ p.val.2.1.val) (p.val.1.val ⊓ p.val.2.2.val) (p.val.2.1.val ⊓ p.val.2.2.val) := by
    have hd := triple_pairs_disjoint L.val M.val N.val h0
    have hd' := triple_pairs_disjoint p.val.1.val p.val.2.1.val p.val.2.2.val p.property.1
    exact triple_isotropic_config_transitivity ω h2 ha hω _ _ _ _ _ _
      (triplePairSum_isotropic ω _ _ _ L.property M.property N.property)
      (triplePairSum_isotropic ω _ _ _ p.val.1.property p.val.2.1.property p.val.2.2.property)
      hd.1 hd.2 hd'.1 hd'.2 p.property.2.1.symm p.property.2.2.1.symm p.property.2.2.2.symm
  let orb (p : T2x30 ω L M N) : O :=
    ⟨(p.val.1.val ⊓ p.val.2.1.val,p.val.1.val ⊓ p.val.2.2.val,p.val.2.1.val ⊓ p.val.2.2.val),ht p⟩
  let e (o : O) := o.property.choose
  have he (o : O) := o.property.choose_spec
  have hes (o : O) (x y : E) : ω ((e o).symm x) ((e o).symm y) = ω x y := by
    simpa only [e,LinearEquiv.apply_symm_apply] using ((he o).1 ((e o).symm x) ((e o).symm y)).symm
  let g (o : O) := T2x45 ω (e o).symm (hes o)
  have hg (o : O) (P : T2x0 ω) : (g o P).val = P.val.map (e o).symm.toLinearMap := rfl
  have hpL (p : T2x30 ω L M N) :
      (L.val ⊓ M.val) ⊔ (L.val ⊓ N.val) ≤ (g (orb p) p.val.1).val := by
    rw [hg,←Submodule.orderIsoMapComap_symm_apply']
    apply (Submodule.orderIsoMapComap (e (orb p))).le_symm_apply.mpr
    change ((L.val ⊓ M.val) ⊔ (L.val ⊓ N.val)).map (e (orb p)).toLinearMap ≤ p.val.1.val
    rw [Submodule.map_sup,(he (orb p)).2.1,(he (orb p)).2.2.1]
    exact sup_le inf_le_left inf_le_left
  have hpM (p : T2x30 ω L M N) :
      (L.val ⊓ M.val) ⊔ (M.val ⊓ N.val) ≤ (g (orb p) p.val.2.1).val := by
    rw [hg,←Submodule.orderIsoMapComap_symm_apply']
    apply (Submodule.orderIsoMapComap (e (orb p))).le_symm_apply.mpr
    change ((L.val ⊓ M.val) ⊔ (M.val ⊓ N.val)).map (e (orb p)).toLinearMap ≤ p.val.2.1.val
    rw [Submodule.map_sup,(he (orb p)).2.1,(he (orb p)).2.2.2]
    exact sup_le inf_le_right inf_le_left
  have hpN (p : T2x30 ω L M N) :
      (L.val ⊓ N.val) ⊔ (M.val ⊓ N.val) ≤ (g (orb p) p.val.2.2).val := by
    rw [hg,←Submodule.orderIsoMapComap_symm_apply']
    apply (Submodule.orderIsoMapComap (e (orb p))).le_symm_apply.mpr
    change ((L.val ⊓ N.val) ⊔ (M.val ⊓ N.val)).map (e (orb p)).toLinearMap ≤ p.val.2.2.val
    rw [Submodule.map_sup,(he (orb p)).2.2.1,(he (orb p)).2.2.2]
    exact sup_le inf_le_right inf_le_right
  let f (p : T2x30 ω L M N) :=
    (orb p,(⟨g (orb p) p.val.1,hpL p⟩ : {P : T2x0 ω // (L.val ⊓ M.val) ⊔ (L.val ⊓ N.val) ≤ P.val}),
      (⟨g (orb p) p.val.2.1,hpM p⟩ : {P : T2x0 ω // (L.val ⊓ M.val) ⊔ (M.val ⊓ N.val) ≤ P.val}),
      (⟨g (orb p) p.val.2.2,hpN p⟩ : {P : T2x0 ω // (L.val ⊓ N.val) ⊔ (M.val ⊓ N.val) ≤ P.val}))
  refine ⟨f,?_⟩
  intro p q hpq
  have ho : orb p = orb q := congrArg Prod.fst hpq
  have hL : g (orb p) p.val.1 = g (orb p) q.val.1 := by
    simpa only [f,ho] using congrArg (fun r => r.2.1.val) hpq
  have hM : g (orb p) p.val.2.1 = g (orb p) q.val.2.1 := by
    simpa only [f,ho] using congrArg (fun r => r.2.2.1.val) hpq
  have hN : g (orb p) p.val.2.2 = g (orb p) q.val.2.2 := by
    simpa only [f,ho] using congrArg (fun r => r.2.2.2.val) hpq
  exact Subtype.ext (Prod.ext ((g (orb p)).injective hL)
    (Prod.ext ((g (orb p)).injective hM) ((g (orb p)).injective hN)))
end CommonZeroProfiles
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
noncomputable def T2x22 (D : ℕ) : ℝ := T2x1 D^4 * 4^D
 theorem profileMassConstant_pos (D : ℕ) : 0 < T2x22 D := by
  unfold T2x22
  have := T2x10 D
  positivity
 theorem profileMassConstant_mono : Monotone T2x22 := by
  intro a b hab
  unfold T2x22
  exact mul_le_mul (pow_le_pow_left₀ (le_of_lt (T2x10 a)) (lagrangianConstant_mono hab) 4)
    (pow_le_pow_right₀ (by norm_num) hab) (by positivity) (by positivity)
section CommonZeroMass
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
 theorem commonZeroProfile_card_upper (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D = finrank K E)
    (L M N : T2x0 ω) (h0 : (L.val ⊓ M.val) ⊓ N.val = ⊥) :
    (Fintype.card K : ℝ)^((finrank K ↥(L.val ⊓ M.val)+1).choose 2 +
      (finrank K ↥(L.val ⊓ N.val)+1).choose 2 + (finrank K ↥(M.val ⊓ N.val)+1).choose 2) *
      Nat.card (T2x30 ω L M N) ≤ T2x22 D * (Fintype.card K : ℝ)^(3*(D+1).choose 2) := by
  have hconst := T2x10 D
  let u := finrank K ↥(L.val ⊓ M.val)
  let v := finrank K ↥(L.val ⊓ N.val)
  let w := finrank K ↥(M.val ⊓ N.val)
  let S := triplePairSum L.val M.val N.val
  let A := (L.val ⊓ M.val) ⊔ (L.val ⊓ N.val)
  let B := (L.val ⊓ M.val) ⊔ (M.val ⊓ N.val)
  let C := (L.val ⊓ N.val) ⊔ (M.val ⊓ N.val)
  have hA : A ≤ L.val := sup_le inf_le_left inf_le_left
  have hB : B ≤ M.val := sup_le inf_le_right inf_le_left
  have hC : C ≤ N.val := sup_le inf_le_right inf_le_right
  have his (P : T2x0 ω) (T : Submodule K E) (hT : T ≤ P.val) : T ≤ ω.orthogonal T := by
    intro x hx y hy
    exact P.property.ge (hT hx) y (hT hy)
  have hd := triple_pairs_disjoint L.val M.val N.val h0
  have hdimA : finrank K A = u+v := finrank_sup_of_disjoint _ _ (hd.1.mono_right le_sup_left)
  have hdimB : finrank K B = u+w := finrank_sup_of_disjoint _ _ (hd.1.mono_right le_sup_right)
  have hdimC : finrank K C = v+w := finrank_sup_of_disjoint _ _ hd.2
  have hdim : finrank K S = u+v+w := triplePairSum_finrank L.val M.val N.val h0
  have hs : S ≤ ω.orthogonal S := triplePairSum_isotropic ω _ _ _ L.property M.property N.property
  have haD : u+v+w ≤ D := hdim ▸ T2x16 ω hω D hD S hs
  have hc := triple_isotropic_orbit_card_upper ω h2 ha hω D hD S
    (L.val ⊓ M.val) (L.val ⊓ N.val) (M.val ⊓ N.val) hs
    (le_sup_of_le_left le_sup_left) (le_sup_of_le_left le_sup_right) le_sup_right rfl hd.1 hd.2
  rw [hdim] at hc
  have hcont (P : T2x0 ω) (T : Submodule K E) (hT : T ≤ P.val) :
      (Nat.card {Q : T2x0 ω // T ≤ Q.val} : ℝ) ≤
        T2x1 D * (Fintype.card K : ℝ)^((D-finrank K T+1).choose 2) :=
    ((T2x76 ω h2 ha hω D hD T (his P T hT)).2).trans
      (mul_le_mul_of_nonneg_right (lagrangianConstant_mono (Nat.sub_le _ _)) (by positivity))
  have h₁ := hcont L A hA
  have h₂ := hcont M B hB
  have h₃ := hcont N C hC
  rw [hdimA] at h₁
  rw [hdimB] at h₂
  rw [hdimC] at h₃
  obtain ⟨f,hf⟩ := commonZeroProfile_injection ω h2 ha hω L M N h0
  have hcard : (Nat.card (T2x30 ω L M N) : ℝ) ≤
      Nat.card (T2x15 ω (L.val ⊓ M.val) (L.val ⊓ N.val) (M.val ⊓ N.val)) *
        ((Nat.card {Q : T2x0 ω // A ≤ Q.val} : ℝ) *
          (Nat.card {Q : T2x0 ω // B ≤ Q.val} * Nat.card {Q : T2x0 ω // C ≤ Q.val})) := by
    have hh := Nat.card_le_card_of_injective f hf
    rw [Nat.card_prod,Nat.card_prod,Nat.card_prod] at hh
    exact_mod_cast hh
  have hb : (Nat.card (T2x30 ω L M N) : ℝ) ≤
      T2x22 D * (Fintype.card K : ℝ)^(T2x19 D (u+v+w)+2*(u*v+u*w+v*w)+
        ((D-(u+v)+1).choose 2+(D-(u+w)+1).choose 2+(D-(v+w)+1).choose 2)) := by
    calc
      _ ≤ _ := hcard
      _ ≤ ((T2x1 D*4^D)*(Fintype.card K : ℝ)^(T2x19 D (u+v+w)+2*(u*v+u*w+v*w))) *
        ((T2x1 D*(Fintype.card K : ℝ)^((D-(u+v)+1).choose 2))*
          ((T2x1 D*(Fintype.card K : ℝ)^((D-(u+w)+1).choose 2))*
            (T2x1 D*(Fintype.card K : ℝ)^((D-(v+w)+1).choose 2)))) := by
          gcongr
      _ = _ := by unfold T2x22; simp only [pow_add]; ring
  have hh := mul_le_mul_of_nonneg_right hb
    (show 0 ≤ (Fintype.card K : ℝ)^((u+1).choose 2+(v+1).choose 2+(w+1).choose 2) by positivity)
  rw [mul_assoc,←pow_add,pair_cost_cancellation D u v w haD] at hh
  simpa only [mul_comm] using hh
end CommonZeroMass
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ProfileQuotient
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E)
abbrev T2x24 (c u v w : ℕ) :=
  {p : T2x0 ω × T2x0 ω × T2x0 ω //
    finrank K ↥((p.1.val ⊓ p.2.1.val) ⊓ p.2.2.val) = c ∧
    finrank K ↥(p.1.val ⊓ p.2.1.val) = u ∧
    finrank K ↥(p.1.val ⊓ p.2.2.val) = v ∧
    finrank K ↥(p.2.1.val ⊓ p.2.2.val) = w}
noncomputable def T2x57 {c u v w : ℕ} (p : T2x24 ω c u v w) : T2x4 ω c :=
  ⟨(p.val.1.val ⊓ p.val.2.1.val) ⊓ p.val.2.2.val,
    (by intro x hx y hy; exact p.val.1.property.ge hx.1.1 y hy.1.1),p.property.1⟩
 theorem reducePair_finrank (S : Submodule K E) (P Q : T2x0 ω)
    (hSP : S ≤ P.val) (hSQ : S ≤ Q.val) :
    finrank K ↥(T2x3 ω S P.val ⊓ T2x3 ω S Q.val) =
      finrank K ↥(P.val ⊓ Q.val)-finrank K S := by
  rw [←reduceSubspace_inf ω S P.val Q.val hSP]
  have hh := reduceSubspace_finrank_containing ω S (P.val ⊓ Q.val) (le_inf hSP hSQ)
    (inf_le_left.trans (T2x25 ω S P.val P.property hSP))
  omega
 omit [FiniteDimensional K E] in
 theorem T2x62 (S : Submodule K E) :
    Function.Injective (fun P : {P : T2x0 ω // S ≤ P.val} => T2x3 ω S P.val.val) := by
  intro P Q h
  apply Subtype.ext
  apply Subtype.ext
  have hh := congrArg (T2x65 ω S) h
  simpa only [lift_reduce ω S P.val.val P.property (T2x25 ω S P.val.val P.val.property P.property),
    lift_reduce ω S Q.val.val Q.property (T2x25 ω S Q.val.val Q.val.property Q.property)] using hh
 theorem fixedCommonProfile_injection (ha : ω.IsAlt) {c u v w : ℕ}
    (S : T2x4 ω c)
    (p₀ : {p : T2x24 ω c u v w // T2x57 ω p = S}) :
    ∃ L M N : T2x0 (T2x2 ω S.val ha),
      (L.val ⊓ M.val) ⊓ N.val = ⊥ ∧
      finrank K ↥(L.val ⊓ M.val) = u-c ∧
      finrank K ↥(L.val ⊓ N.val) = v-c ∧
      finrank K ↥(M.val ⊓ N.val) = w-c ∧
      ∃ f : {p : T2x24 ω c u v w // T2x57 ω p = S} →
        T2x30 (T2x2 ω S.val ha) L M N, Function.Injective f := by
  let F := {p : T2x24 ω c u v w // T2x57 ω p = S}
  have heq (p : F) : (p.val.val.1.val ⊓ p.val.val.2.1.val) ⊓ p.val.val.2.2.val = S.val :=
    congrArg Subtype.val p.property
  have hL (p : F) : S.val ≤ p.val.val.1.val := (heq p).symm ▸ inf_le_left.trans inf_le_left
  have hM (p : F) : S.val ≤ p.val.val.2.1.val := (heq p).symm ▸ inf_le_left.trans inf_le_right
  have hN (p : F) : S.val ≤ p.val.val.2.2.val := (heq p).symm ▸ inf_le_right
  let L (p : F) := T2x53 ω S.val ha S.property.1 p.val.val.1 (hL p)
  let M (p : F) := T2x53 ω S.val ha S.property.1 p.val.val.2.1 (hM p)
  let N (p : F) := T2x53 ω S.val ha S.property.1 p.val.val.2.2 (hN p)
  have hzero (p : F) : ((L p).val ⊓ (M p).val) ⊓ (N p).val = ⊥ := by
    change (T2x3 ω S.val p.val.val.1.val ⊓ T2x3 ω S.val p.val.val.2.1.val) ⊓
      T2x3 ω S.val p.val.val.2.2.val = ⊥
    rw [←reduceSubspace_inf ω S.val _ _ (hL p),←reduceSubspace_inf ω S.val _ _ (le_inf (hL p) (hM p)),heq p]
    exact reduceSubspace_self ω S.val
  have hu (p : F) : finrank K ↥((L p).val ⊓ (M p).val) = u-c := by
    change finrank K ↥(T2x3 ω S.val p.val.val.1.val ⊓ T2x3 ω S.val p.val.val.2.1.val) = _
    rw [reducePair_finrank ω S.val _ _ (hL p) (hM p),p.val.property.2.1,S.property.2]
  have hv (p : F) : finrank K ↥((L p).val ⊓ (N p).val) = v-c := by
    change finrank K ↥(T2x3 ω S.val p.val.val.1.val ⊓ T2x3 ω S.val p.val.val.2.2.val) = _
    rw [reducePair_finrank ω S.val _ _ (hL p) (hN p),p.val.property.2.2.1,S.property.2]
  have hw (p : F) : finrank K ↥((M p).val ⊓ (N p).val) = w-c := by
    change finrank K ↥(T2x3 ω S.val p.val.val.2.1.val ⊓ T2x3 ω S.val p.val.val.2.2.val) = _
    rw [reducePair_finrank ω S.val _ _ (hM p) (hN p),p.val.property.2.2.2,S.property.2]
  let f (p : F) : T2x30 (T2x2 ω S.val ha) (L p₀) (M p₀) (N p₀) :=
    ⟨(L p,M p,N p),hzero p,(hu p).trans (hu p₀).symm,(hv p).trans (hv p₀).symm,(hw p).trans (hw p₀).symm⟩
  refine ⟨L p₀,M p₀,N p₀,hzero p₀,hu p₀,hv p₀,hw p₀,f,?_⟩
  intro p q hpq
  have heL : (L p).val = (L q).val := congrArg (fun r => r.val.1.val) hpq
  have heM : (M p).val = (M q).val := congrArg (fun r => r.val.2.1.val) hpq
  have heN : (N p).val = (N q).val := congrArg (fun r => r.val.2.2.val) hpq
  have hpL : p.val.val.1 = q.val.val.1 := congrArg Subtype.val
    (T2x62 ω S.val (a₁ := ⟨p.val.val.1,hL p⟩) (a₂ := ⟨q.val.val.1,hL q⟩) heL)
  have hpM : p.val.val.2.1 = q.val.val.2.1 := congrArg Subtype.val
    (T2x62 ω S.val (a₁ := ⟨p.val.val.2.1,hM p⟩) (a₂ := ⟨q.val.val.2.1,hM q⟩) heM)
  have hpN : p.val.val.2.2 = q.val.val.2.2 := congrArg Subtype.val
    (T2x62 ω S.val (a₁ := ⟨p.val.val.2.2,hN p⟩) (a₂ := ⟨q.val.val.2.2,hN q⟩) heN)
  exact Subtype.ext (Subtype.ext (Prod.ext hpL (Prod.ext hpM hpN)))
end ProfileQuotient
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section AllProfileMass
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
 theorem fixedCommonProfile_card_upper (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D = finrank K E) {c u v w : ℕ} (S : T2x4 ω c) :
    (Fintype.card K : ℝ)^((u-c+1).choose 2+(v-c+1).choose 2+(w-c+1).choose 2) *
      Nat.card {p : T2x24 ω c u v w // T2x57 ω p = S} ≤
        T2x22 (D-c) * (Fintype.card K : ℝ)^(3*(D-c+1).choose 2) := by
  classical
  let F := {p : T2x24 ω c u v w // T2x57 ω p = S}
  by_cases hF : Nonempty F
  · obtain ⟨p₀⟩ := hF
    obtain ⟨L,M,N,hzero,hu,hv,hw,f,hf⟩ := fixedCommonProfile_injection ω ha S p₀
    let : Finite (T2x20 ω S.val) := Module.finite_of_finite K
    have hc : c ≤ D := S.property.2 ▸ T2x16 ω hω D hD S.val S.property.1
    have hdim : 2*(D-c) = finrank K (T2x20 ω S.val) := by
      have hh := reducedSpace_finrank ω S.val hω S.property.1
      rw [S.property.2,←hD] at hh
      omega
    have hp := commonZeroProfile_card_upper (T2x2 ω S.val ha) h2
      (T2x81 ω S.val ha) (T2x13 ω S.val ha hω)
      (D-c) hdim L M N hzero
    rw [hu,hv,hw] at hp
    have hc : (Nat.card F : ℝ) ≤ Nat.card (T2x30 (T2x2 ω S.val ha) L M N) := by
      exact_mod_cast Nat.card_le_card_of_injective f hf
    exact (mul_le_mul_of_nonneg_left hc (by positivity)).trans hp
  · have h_empty : IsEmpty F := not_nonempty_iff.mp hF
    have hc : Nat.card F = 0 := Nat.card_eq_zero.mpr (Or.inl h_empty)
    change _ * (Nat.card F : ℝ) ≤ _
    rw [hc,Nat.cast_zero,mul_zero]
    exact mul_nonneg (le_of_lt (profileMassConstant_pos _)) (by positivity)
noncomputable def T2x11 (D : ℕ) : ℝ := T2x1 D * 2^D * T2x22 D
 theorem T2x88 (D : ℕ) : 0 < T2x11 D :=
  mul_pos (mul_pos (T2x10 _) (by positivity)) (profileMassConstant_pos _)
 theorem tripleProfile_card_upper (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D = finrank K E) (c u v w : ℕ) (hc : c ≤ D) :
    (Fintype.card K : ℝ)^((D+1)*c + ((u-c+1).choose 2+(v-c+1).choose 2+(w-c+1).choose 2)) *
      Nat.card (T2x24 ω c u v w) ≤ T2x11 D * (Fintype.card K : ℝ)^(3*(D+1).choose 2) := by
  classical
  let := Fintype.ofFinite (T2x4 ω c)
  let δ := (u-c+1).choose 2+(v-c+1).choose 2+(w-c+1).choose 2
  let q : ℝ := Fintype.card K
  have hi := (isotropic_card_bounds ω h2 ha hω D hD c hc).2
  have hsum : (Nat.card (T2x24 ω c u v w) : ℝ) =
      ∑ S : T2x4 ω c, (Nat.card {p : T2x24 ω c u v w // T2x57 ω p = S} : ℝ) := by
    have hh := (Nat.card_congr (Equiv.sigmaFiberEquiv (T2x57 ω (c := c) (u := u) (v := v) (w := w)))).symm
    rw [Nat.card_sigma] at hh
    exact_mod_cast hh
  have hbase : q^δ * Nat.card (T2x24 ω c u v w) ≤
      (Nat.card (T2x4 ω c) : ℝ) * (T2x22 (D-c)*q^(3*(D-c+1).choose 2)) := by
    rw [hsum,Finset.mul_sum]
    calc
      _ ≤ ∑ _S : T2x4 ω c, T2x22 (D-c)*q^(3*(D-c+1).choose 2) :=
        Finset.sum_le_sum (fun S _ => fixedCommonProfile_card_upper ω h2 ha hω D hD S)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card]
  have hk : (T2x1 D*2^c)*T2x22 (D-c) ≤ T2x11 D := by
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hc) (le_of_lt (T2x10 _)))
      (profileMassConstant_mono (Nat.sub_le D c)) (le_of_lt (profileMassConstant_pos _))
      (mul_nonneg (le_of_lt (T2x10 _)) (by positivity))
  have hconst := T2x88 D
  calc
    _ = q^((D+1)*c) * (q^δ * Nat.card (T2x24 ω c u v w)) := by rw [pow_add,mul_assoc]
    _ ≤ q^((D+1)*c) * ((Nat.card (T2x4 ω c) : ℝ)*(T2x22 (D-c)*q^(3*(D-c+1).choose 2))) :=
      mul_le_mul_of_nonneg_left hbase (by positivity)
    _ ≤ q^((D+1)*c) * (((T2x1 D*2^c)*q^T2x19 D c)*(T2x22 (D-c)*q^(3*(D-c+1).choose 2))) := by
      gcongr
      exact mul_nonneg (le_of_lt (profileMassConstant_pos _)) (by positivity)
    _ = ((T2x1 D*2^c)*T2x22 (D-c))*q^(T2x19 D c+3*(D-c+1).choose 2+(D+1)*c) := by
      simp only [pow_add]; ring
    _ = ((T2x1 D*2^c)*T2x22 (D-c))*q^(3*(D+1).choose 2) := by
      rw [common_cost_cancellation D c hc]
    _ ≤ _ := mul_le_mul_of_nonneg_right hk (by positivity)
end AllProfileMass
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section GeneralPairCounts
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
 theorem symplectic_pair_count (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (A : T2x0 ω) (h : ℕ) (hh : h ≤ finrank K A.val) :
    Nat.card {L : T2x0 ω // finrank K ↥(L.val ⊓ A.val) = h} =
      Nat.card (DimSubspace K A.val (finrank K A.val-h)) * (Fintype.card K)^((finrank K A.val-h+1).choose 2) := by
  classical
  obtain ⟨e,_,he⟩ := T2x21 ω A.val h2 ha hω A.property
  let f := symplecticLagrangianEquiv T2x5 ω e he
  let A₀ := f.symm A
  have hm : A₀.val.map e.toLinearMap = A.val := congrArg Subtype.val (f.apply_symm_apply A)
  have hd (L : Lagrangian (K := K) (V := A.val)) :
      finrank K ↥((f L).val ⊓ A.val) = finrank K ↥(L.val ⊓ A₀.val) := by
    change finrank K ↥(L.val.map e.toLinearMap ⊓ A.val) = _
    calc
      _ = finrank K ↥(L.val.map e.toLinearMap ⊓ A₀.val.map e.toLinearMap) :=
        congrArg (fun S : Submodule K E => finrank K ↥(L.val.map e.toLinearMap ⊓ S)) hm.symm
      _ = _ := by rw [←Submodule.map_inf e.toLinearMap e.injective]; exact e.finrank_map_eq _
  have hc : Nat.card {L : Lagrangian (K := K) (V := A.val) // finrank K ↥(L.val ⊓ A₀.val) = h} =
      Nat.card {L : T2x0 ω // finrank K ↥(L.val ⊓ A.val) = h} :=
    Nat.card_congr (f.subtypeEquiv (fun L => by rw [hd]))
  rw [←hc]
  exact lagrangian_pair_count h2 A₀ h hh
 theorem symplectic_pair_card_bounds (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D = finrank K E) (A : T2x0 ω) (h : ℕ) (hh : h ≤ D) :
    (Fintype.card K : ℝ)^((D+1).choose 2) ≤ (Fintype.card K : ℝ)^((h+1).choose 2) *
      Nat.card {L : T2x0 ω // finrank K ↥(L.val ⊓ A.val) = h} ∧
    (Fintype.card K : ℝ)^((h+1).choose 2) *
      Nat.card {L : T2x0 ω // finrank K ↥(L.val ⊓ A.val) = h} ≤
        2^D*(Fintype.card K : ℝ)^((D+1).choose 2) := by
  have hd : finrank K A.val = D := by
    have h := T2x6 ω A.val hω A.property
    omega
  have hhA : h ≤ finrank K A.val := by omega
  have hcount := symplectic_pair_count ω h2 ha hω A h hhA
  rw [hd] at hcount
  rw [hcount,Nat.cast_mul,Nat.cast_pow]
  have hl := subspace_count_lower (K := K) (V := A.val) (D-h) (by omega)
  have hu := T2x26 (K := K) (V := A.val) (D-h) (by omega)
  rw [hd,Nat.sub_sub_self hh] at hl hu
  have he : (Fintype.card K : ℝ)^((h+1).choose 2) *
      ((Fintype.card K : ℝ)^((D-h)*h)*(Fintype.card K : ℝ)^((D-h+1).choose 2)) =
      (Fintype.card K : ℝ)^((D+1).choose 2) := by
    rw [←pow_add,←pow_add]
    congr 1
    have hexp := symmetric_nullity_exponent D h hh
    rw [Nat.mul_comm h (D-h)] at hexp
    omega
  constructor
  · rw [←he]
    gcongr
  · calc
      _ ≤ (Fintype.card K : ℝ)^((h+1).choose 2) *
        ((2^(D-h)*(Fintype.card K : ℝ)^((D-h)*h))*(Fintype.card K : ℝ)^((D-h+1).choose 2)) := by gcongr
      _ = 2^(D-h)*(Fintype.card K : ℝ)^((D+1).choose 2) := by rw [←he]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num) (Nat.sub_le D h)) (by positivity)
abbrev T2x66 (h : ℕ) := {p : T2x0 ω × T2x0 ω //
  finrank K ↥(p.1.val ⊓ p.2.val) = h}
noncomputable def orderedPairDimEquiv (h : ℕ) : T2x66 ω h ≃
    Σ A : T2x0 ω, {L : T2x0 ω // finrank K ↥(L.val ⊓ A.val) = h} where
  toFun p := ⟨p.val.1,⟨p.val.2,by rw [inf_comm]; exact p.property⟩⟩
  invFun p := ⟨(p.1,p.2.val),by rw [inf_comm]; exact p.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
 theorem orderedPairDim_card_lower (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D = finrank K E) (h : ℕ) (hh : h ≤ D) :
    (Fintype.card K : ℝ)^(2*(D+1).choose 2) ≤ (Fintype.card K : ℝ)^((h+1).choose 2) * Nat.card (T2x66 ω h) := by
  classical
  let := Fintype.ofFinite (T2x0 ω)
  have hc : (Nat.card (T2x66 ω h) : ℝ) =
      ∑ A : T2x0 ω, (Nat.card {L : T2x0 ω // finrank K ↥(L.val ⊓ A.val) = h} : ℝ) := by
    rw [Nat.card_congr (orderedPairDimEquiv ω h),Nat.card_sigma,Nat.cast_sum]
  rw [hc,Finset.mul_sum]
  have he : 2*(D+1).choose 2 = (D+1).choose 2+(D+1).choose 2 := by omega
  rw [he,pow_add]
  calc
    _ ≤ (Nat.card (T2x0 ω) : ℝ)*(Fintype.card K : ℝ)^((D+1).choose 2) :=
      mul_le_mul_of_nonneg_right (T2x18 ω h2 ha hω D hD).1 (by positivity)
    _ = ∑ _A : T2x0 ω, (Fintype.card K : ℝ)^((D+1).choose 2) := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card]
    _ ≤ _ := Finset.sum_le_sum (fun A _ => (symplectic_pair_card_bounds ω h2 ha hω D hD A h hh).1)
end GeneralPairCounts
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ConditionalProfile
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E)
abbrev T2x75 (L M : T2x0 ω) (c v w : ℕ) :=
  {N : T2x0 ω // finrank K ↥((L.val ⊓ M.val) ⊓ N.val) = c ∧
    finrank K ↥(L.val ⊓ N.val) = v ∧ finrank K ↥(M.val ⊓ N.val) = w}
 omit [FiniteDimensional K E] in
 theorem pairCompletion_card_congr (L M L' M' : T2x0 ω)
    (e : E ≃ₗ[K] E) (he : ∀ x y, ω (e x) (e y) = ω x y)
    (hL : L.val.map e.toLinearMap = L'.val) (hM : M.val.map e.toLinearMap = M'.val) (c v w : ℕ) :
    Nat.card (T2x75 ω L M c v w) = Nat.card (T2x75 ω L' M' c v w) := by
  let f := T2x45 ω e he
  have hp (A B : Submodule K E) : finrank K ↥(A.map e.toLinearMap ⊓ B.map e.toLinearMap) = finrank K ↥(A ⊓ B) := by
    rw [←Submodule.map_inf e.toLinearMap e.injective]
    exact e.finrank_map_eq _
  have hc (P : T2x0 ω) : finrank K ↥((L'.val ⊓ M'.val) ⊓ (f P).val) =
      finrank K ↥((L.val ⊓ M.val) ⊓ P.val) := by
    change finrank K ↥((L'.val ⊓ M'.val) ⊓ P.val.map e.toLinearMap) = _
    rw [←hL,←hM,←Submodule.map_inf e.toLinearMap e.injective,hp]
  have hv (P : T2x0 ω) : finrank K ↥(L'.val ⊓ (f P).val) = finrank K ↥(L.val ⊓ P.val) := by
    change finrank K ↥(L'.val ⊓ P.val.map e.toLinearMap) = _
    rw [←hL,hp]
  have hw (P : T2x0 ω) : finrank K ↥(M'.val ⊓ (f P).val) = finrank K ↥(M.val ⊓ P.val) := by
    change finrank K ↥(M'.val ⊓ P.val.map e.toLinearMap) = _
    rw [←hM,hp]
  exact Nat.card_congr (f.subtypeEquiv (fun P => by rw [hc,hv,hw]))
noncomputable def profilePairCompletionEquiv (c u v w : ℕ) : T2x24 ω c u v w ≃
    Σ p : T2x66 ω u, T2x75 ω p.val.1 p.val.2 c v w where
  toFun p := ⟨⟨(p.val.1,p.val.2.1),p.property.2.1⟩,⟨p.val.2.2,p.property.1,p.property.2.2⟩⟩
  invFun p := ⟨(p.1.val.1,p.1.val.2,p.2.val),p.2.property.1,p.1.property,p.2.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
variable [Finite E]
 theorem tripleProfile_completion_card (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (L M : T2x0 ω) (c v w : ℕ) :
    Nat.card (T2x24 ω c (finrank K ↥(L.val ⊓ M.val)) v w) =
      Nat.card (T2x66 ω (finrank K ↥(L.val ⊓ M.val))) * Nat.card (T2x75 ω L M c v w) := by
  classical
  let := Fintype.ofFinite (T2x66 ω (finrank K ↥(L.val ⊓ M.val)))
  rw [Nat.card_congr (profilePairCompletionEquiv ω c (finrank K ↥(L.val ⊓ M.val)) v w),Nat.card_sigma]
  have hc (p : T2x66 ω (finrank K ↥(L.val ⊓ M.val))) :
      Nat.card (T2x75 ω p.val.1 p.val.2 c v w) = Nat.card (T2x75 ω L M c v w) := by
    obtain ⟨e,he,hL,hM⟩ := ordered_pair_transitivity ω h2 ha hω
      p.val.1.val p.val.2.val L.val M.val p.val.1.property p.val.2.property L.property M.property p.property
    exact pairCompletion_card_congr ω p.val.1 p.val.2 L M e he hL hM c v w
  simp only [hc,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card]
  simp only [Nat.cast_id]
variable [Fintype K]
 theorem conditionalProfile_card_upper (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D = finrank K E) (L M : T2x0 ω) (c v w : ℕ) (hc : c ≤ D) :
    (Fintype.card K : ℝ)^((D+1)*c + ((finrank K ↥(L.val ⊓ M.val)-c+1).choose 2+
      (v-c+1).choose 2+(w-c+1).choose 2)) * Nat.card (T2x75 ω L M c v w) ≤
        T2x11 D * (Fintype.card K : ℝ)^((finrank K ↥(L.val ⊓ M.val)+1).choose 2+(D+1).choose 2) := by
  let u := finrank K ↥(L.val ⊓ M.val)
  let δ := (D+1)*c + ((u-c+1).choose 2+(v-c+1).choose 2+(w-c+1).choose 2)
  let q : ℝ := Fintype.card K
  have hq : 0 < q := by dsimp [q]; exact_mod_cast Fintype.card_pos (α := K)
  have hu : u ≤ D := by
    have h := T2x6 ω L.val hω L.property
    have hle := Submodule.finrank_mono (show L.val ⊓ M.val ≤ L.val from inf_le_left)
    dsimp [u]
    omega
  have hp := orderedPairDim_card_lower ω h2 ha hω D hD u hu
  have ht := tripleProfile_card_upper ω h2 ha hω D hD c u v w hc
  have hi : (Nat.card (T2x24 ω c u v w) : ℝ) =
      (Nat.card (T2x66 ω u) : ℝ)*Nat.card (T2x75 ω L M c v w) := by
    exact_mod_cast tripleProfile_completion_card ω h2 ha hω L M c v w
  apply (mul_le_mul_iff_right₀ (pow_pos hq (2*(D+1).choose 2))).mp
  calc
    _ = q^δ*(q^(2*(D+1).choose 2)*Nat.card (T2x75 ω L M c v w)) := by ring
    _ ≤ q^δ*((q^((u+1).choose 2)*Nat.card (T2x66 ω u))*Nat.card (T2x75 ω L M c v w)) := by gcongr
    _ = q^((u+1).choose 2)*(q^δ*Nat.card (T2x24 ω c u v w)) := by rw [hi]; ring
    _ ≤ q^((u+1).choose 2)*(T2x11 D*q^(3*(D+1).choose 2)) :=
      mul_le_mul_of_nonneg_left ht (by positivity)
    _ = q^(2*(D+1).choose 2)*(T2x11 D*q^((u+1).choose 2+(D+1).choose 2)) := by
      have he : 3*(D+1).choose 2 = 2*(D+1).choose 2+(D+1).choose 2 := by omega
      rw [he,pow_add,pow_add]
      ring
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
 theorem reduceSubspace_finrank_general (A : Submodule K E) (hAP : A ≤ ω.orthogonal S) :
    finrank K (T2x3 ω S A) + finrank K ↥(S ⊓ A) = finrank K A := by
  let f : A →ₗ[K] T2x20 ω S := (T2x8 ω S).mkQ.comp (Submodule.inclusion hAP)
  have hk : LinearMap.ker f = (S ⊓ A).comap A.subtype := by
    ext x
    constructor
    · intro hx
      exact ⟨(Submodule.Quotient.mk_eq_zero (T2x8 ω S)).mp hx,x.property⟩
    · intro hx
      exact (Submodule.Quotient.mk_eq_zero (T2x8 ω S)).mpr hx.1
  have hr : LinearMap.range f = T2x3 ω S A := by
    ext y
    constructor
    · rintro ⟨x,rfl⟩
      exact ⟨⟨x.val,hAP x.property⟩,x.property,rfl⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨⟨x.val,hx⟩,rfl⟩
  have hh := f.finrank_range_add_finrank_ker
  rw [hk,hr,(Submodule.comapSubtypeEquivOfLe (inf_le_right : S ⊓ A ≤ A)).finrank_eq] at hh
  exact hh
 theorem reduce_center_intersection_finrank (L Y : Submodule K E)
    (hSL : S ≤ L) (hLP : L ≤ ω.orthogonal S) :
    finrank K ↥(T2x3 ω S L ⊓ T2x3 ω S Y) + finrank K ↥(S ⊓ Y) =
      finrank K ↥(L ⊓ Y) := by
  rw [←reduceSubspace_inf ω S L Y hSL]
  have hh := reduceSubspace_finrank_general ω S (L ⊓ Y) (inf_le_left.trans hLP)
  have he : S ⊓ (L ⊓ Y) = S ⊓ Y := by rw [←inf_assoc,inf_eq_left.mpr hSL]
  rwa [he] at hh
end PlantedQuotient
section CenterDisintegration
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E)
abbrev T2x69 (r : ℕ) (L M N : Submodule K E) :=
  {Y : T2x0 ω // finrank K ↥(L ⊓ Y.val) = r ∧
    finrank K ↥(M ⊓ Y.val) = r ∧ finrank K ↥(N ⊓ Y.val) = r}
noncomputable def tripleCenterIsometryEquiv (r : ℕ) (L M N : Submodule K E)
    (e : E ≃ₗ[K] E) (he : ∀ x y, ω (e x) (e y) = ω x y) :
    T2x69 ω r L M N ≃
    T2x69 ω r (L.map e.toLinearMap) (M.map e.toLinearMap) (N.map e.toLinearMap) := by
  let f := T2x45 ω e he
  refine f.subtypeEquiv ?_
  intro Y
  change (_ ∧ _ ∧ _) ↔ (finrank K ↥(L.map e.toLinearMap ⊓ Y.val.map e.toLinearMap) = r ∧
    finrank K ↥(M.map e.toLinearMap ⊓ Y.val.map e.toLinearMap) = r ∧
    finrank K ↥(N.map e.toLinearMap ⊓ Y.val.map e.toLinearMap) = r)
  rw [←Submodule.map_inf e.toLinearMap e.injective,←Submodule.map_inf e.toLinearMap e.injective,
    ←Submodule.map_inf e.toLinearMap e.injective,e.finrank_map_eq,e.finrank_map_eq,e.finrank_map_eq]
 theorem tripleCenter_orbit_card (r : ℕ) (L M N : Submodule K E)
    (P : T2x15 ω L M N) :
    Nat.card (T2x69 ω r P.val.1 P.val.2.1 P.val.2.2) =
      Nat.card (T2x69 ω r L M N) := by
  obtain ⟨e,he,hL,hM,hN⟩ := P.property
  rw [←hL,←hM,←hN]
  exact (Nat.card_congr (tripleCenterIsometryEquiv ω r L M N e he)).symm
 theorem tripleCenterOrbit_card [Finite E] (r : ℕ) (L M N : Submodule K E) :
    Nat.card (Σ P : T2x15 ω L M N, T2x69 ω r P.val.1 P.val.2.1 P.val.2.2) =
      Nat.card (T2x15 ω L M N) * Nat.card (T2x69 ω r L M N) := by
  classical
  let := Fintype.ofFinite (T2x15 ω L M N)
  rw [Nat.card_sigma]
  simp_rw [tripleCenter_orbit_card ω r L M N]
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul,Nat.card_eq_fintype_card]
end CenterDisintegration
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section GenericReducedCount
variable {K E V : Type*} [Field K] [AddCommGroup E] [Module K E]
  [AddCommGroup V] [Module K V]
variable (ω : LinearMap.BilinForm K E)
abbrev T2x7 (Y : T2x0 ω) (r : ℕ) :=
  {L : T2x0 ω // finrank K ↥(L.val ⊓ Y.val) = r}
abbrev SymplecticCenterProfile (Y : T2x0 ω) (r s₀ s₁ s₂ : ℕ) :=
  {L : T2x7 ω Y r × T2x7 ω Y r × T2x7 ω Y r //
    (L.1.val.val ⊓ L.2.1.val.val) ⊓ L.2.2.val.val = ⊥ ∧
    finrank K ↥(L.1.val.val ⊓ L.2.1.val.val) = s₀ ∧
    finrank K ↥(L.1.val.val ⊓ L.2.2.val.val) = s₁ ∧
    finrank K ↥(L.2.1.val.val ⊓ L.2.2.val.val) = s₂}
 theorem exists_center_coordinates [FiniteDimensional K E] (h2 : (2:K) ≠ 0)
    (ha : ω.IsAlt) (hω : ω.Nondegenerate) (Y : T2x0 ω) :
    ∃ e : (Y.val × Module.Dual K Y.val) ≃ₗ[K] E,
      (∀ x y, ω (e x) (e y) = T2x5 x y) ∧
      (T2x63 (K := K) (V := Y.val)).map e.toLinearMap = Y.val := by
  obtain ⟨e,_,he⟩ := T2x21 ω Y.val h2 ha hω Y.property
  let f := symplecticLagrangianEquiv T2x5 ω e he
  let A := f.symm Y
  have hm : A.val.map e.toLinearMap = Y.val := congrArg Subtype.val (f.apply_symm_apply Y)
  obtain ⟨a,ha,hA⟩ := lagrangian_transitivity T2x5 verticalLagrangian.val h2
    canonicalSymplectic_alt T2x35 verticalLagrangian.property A.val A.property
  refine ⟨a.trans e,?_,?_⟩
  · intro x y
    change ω (e (a x)) (e (a y)) = _
    rw [he,ha]
  · change T2x63.map (e.toLinearMap.comp a.toLinearMap) = _
    rw [Submodule.map_comp]
    change (verticalLagrangian.val.map a.toLinearMap).map e.toLinearMap = _
    rw [hA,hm]
 theorem T2x83 (e : V ≃ₗ[K] E) (A B : Submodule K V) :
    finrank K ↥(A.map e.toLinearMap ⊓ B.map e.toLinearMap) = finrank K ↥(A ⊓ B) := by
  rw [←Submodule.map_inf e.toLinearMap e.injective]
  exact e.finrank_map_eq _
 theorem map_common_zero_iff (e : V ≃ₗ[K] E) (A B C : Submodule K V) :
    (A.map e.toLinearMap ⊓ B.map e.toLinearMap) ⊓ C.map e.toLinearMap = ⊥ ↔ (A ⊓ B) ⊓ C = ⊥ := by
  rw [←Submodule.map_inf e.toLinearMap e.injective,←Submodule.map_inf e.toLinearMap e.injective]
  constructor
  · intro h
    apply (Submodule.orderIsoMapComap e).injective
    simpa only [Submodule.orderIsoMapComap_apply,Submodule.map_bot] using h
  · intro h
    rw [h,Submodule.map_bot]
noncomputable def symplecticCenterStratumEquiv (Y : T2x0 ω)
    (e : (V × Module.Dual K V) ≃ₗ[K] E)
    (he : ∀ x y, ω (e x) (e y) = T2x5 x y)
    (hY : (T2x63 (K := K) (V := V)).map e.toLinearMap = Y.val) (r : ℕ) :
    T2x59 (K := K) (V := V) r ≃ T2x7 ω Y r :=
  (symplecticLagrangianEquiv T2x5 ω e he).subtypeEquiv (by
    intro L
    change finrank K ↥(L.val ⊓ T2x63) = r ↔ finrank K ↥(L.val.map e.toLinearMap ⊓ Y.val) = r
    rw [←hY,T2x83])
noncomputable def symplecticCenterProfileEquiv (Y : T2x0 ω)
    (e : (V × Module.Dual K V) ≃ₗ[K] E)
    (he : ∀ x y, ω (e x) (e y) = T2x5 x y)
    (hY : (T2x63 (K := K) (V := V)).map e.toLinearMap = Y.val) (r s₀ s₁ s₂ : ℕ) :
    CenterTripleProfile (K := K) (V := V) r s₀ s₁ s₂ ≃ SymplecticCenterProfile ω Y r s₀ s₁ s₂ :=
  let f := symplecticCenterStratumEquiv ω Y e he hY r
  (f.prodCongr (f.prodCongr f)).subtypeEquiv (by
    intro L
    change (_ ∧ _ ∧ _ ∧ _) ↔
      ((L.1.val.val.map e.toLinearMap ⊓ L.2.1.val.val.map e.toLinearMap) ⊓ L.2.2.val.val.map e.toLinearMap = ⊥ ∧
      finrank K ↥(L.1.val.val.map e.toLinearMap ⊓ L.2.1.val.val.map e.toLinearMap) = s₀ ∧
      finrank K ↥(L.1.val.val.map e.toLinearMap ⊓ L.2.2.val.val.map e.toLinearMap) = s₁ ∧
      finrank K ↥(L.2.1.val.val.map e.toLinearMap ⊓ L.2.2.val.val.map e.toLinearMap) = s₂)
    rw [map_common_zero_iff,T2x83,T2x83,T2x83])
 theorem symplectic_center_profile_probability_bound [Fintype K] [Finite E]
    (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (Y : T2x0 ω) (r s₀ s₁ s₂ : ℕ) (hr : r ≤ finrank K Y.val) :
    (Nat.card (SymplecticCenterProfile ω Y r s₀ s₁ s₂) : ℝ) /
      (Nat.card (T2x7 ω Y r) : ℝ)^3 ≤
    ∑ θ : BaseParameters (finrank K Y.val) r s₀ s₁ s₂,
      T2x58 r s₀ s₁ s₂ θ.val *
        (Fintype.card K : ℝ)^(T2x74 (finrank K Y.val) r s₀ s₁ s₂ θ.val) := by
  obtain ⟨e,he,hY⟩ := exists_center_coordinates ω h2 ha hω Y
  rw [←Nat.card_congr (symplecticCenterProfileEquiv ω Y e he hY r s₀ s₁ s₂),
    ←Nat.card_congr (symplecticCenterStratumEquiv ω Y e he hY r)]
  exact canonical_center_profile_probability_bound r s₀ s₁ s₂ hr
 theorem symplectic_profile_pair_sum_le [Fintype K] [Finite E]
    (hω : ω.Nondegenerate) (D : ℕ) (hD : 2*D = finrank K E)
    (L M N : T2x0 ω) (h0 : (L.val ⊓ M.val) ⊓ N.val = ⊥) :
    finrank K ↥(L.val ⊓ M.val)+finrank K ↥(L.val ⊓ N.val)+finrank K ↥(M.val ⊓ N.val) ≤ D := by
  rw [←triplePairSum_finrank _ _ _ h0]
  exact T2x16 ω hω D hD _ (triplePairSum_isotropic ω _ _ _ L.property M.property N.property)
end GenericReducedCount
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section CommonCenterCounts
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
abbrev T2x71 (S : Submodule K E) (u : ℕ) :=
  {Y : T2x0 ω // finrank K ↥(S ⊓ Y.val) = u}
 theorem commonCenter_card_upper (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D = finrank K E) (S : Submodule K E)
    (hS : S ≤ ω.orthogonal S) (u : ℕ) (hu : u ≤ finrank K S) :
    (Nat.card (T2x71 ω S u) : ℝ) ≤
      2^u * T2x1 (D-u) *
        (Fintype.card K : ℝ)^(u*(finrank K S-u)+(D-u+1).choose 2) := by
  classical
  let B := T2x71 ω S u
  let Inc := Σ U : DimSubspace K S u, {Y : T2x0 ω // U.val.map S.subtype ≤ Y.val}
  let f (Y : B) : Inc :=
    ⟨⟨(S ⊓ Y.val.val).comap S.subtype,
      (Submodule.comapSubtypeEquivOfLe (inf_le_left : S ⊓ Y.val.val ≤ S)).finrank_eq.trans Y.property⟩,
      ⟨Y.val,by rintro x ⟨y,hy,rfl⟩; exact hy.2⟩⟩
  have hf : Function.Injective f := by
    intro Y Z h
    exact Subtype.ext (congrArg (fun i : Inc => i.2.val) h)
  have hb (U : DimSubspace K S u) :
      (Nat.card {Y : T2x0 ω // U.val.map S.subtype ≤ Y.val} : ℝ) ≤
      T2x1 (D-u)*(Fintype.card K : ℝ)^((D-u+1).choose 2) := by
    have hle : U.val.map S.subtype ≤ S := by rintro x ⟨y,_,rfl⟩; exact y.property
    have his : U.val.map S.subtype ≤ ω.orthogonal (U.val.map S.subtype) :=
      hle.trans (hS.trans (ω.orthogonal_le hle))
    have hd : finrank K (U.val.map S.subtype) = u :=
      (Submodule.equivMapOfInjective S.subtype S.subtype_injective U.val).finrank_eq.symm.trans U.property
    simpa only [hd] using (T2x76 ω h2 ha hω D hD _ his).2
  let := Fintype.ofFinite (DimSubspace K S u)
  have hi : (Nat.card Inc : ℝ) ≤ (Nat.card (DimSubspace K S u) : ℝ)*
      (T2x1 (D-u)*(Fintype.card K : ℝ)^((D-u+1).choose 2)) := by
    rw [Nat.card_sigma,Nat.cast_sum]
    calc
      _ ≤ ∑ U : DimSubspace K S u, T2x1 (D-u)*(Fintype.card K : ℝ)^((D-u+1).choose 2) :=
        Finset.sum_le_sum (fun U _ => hb U)
      _ = _ := by simp [Nat.card_eq_fintype_card]
  calc
    _ ≤ (Nat.card Inc : ℝ) := Nat.cast_le.mpr (Nat.card_le_card_of_injective f hf)
    _ ≤ _ := hi
    _ ≤ (2^u*(Fintype.card K : ℝ)^(u*(finrank K S-u))) *
        (T2x1 (D-u)*(Fintype.card K : ℝ)^((D-u+1).choose 2)) :=
      mul_le_mul_of_nonneg_right (T2x26 u hu)
        (mul_nonneg (T2x10 (D-u)).le (by positivity))
    _ = _ := by rw [pow_add]; ring
end CommonCenterCounts
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ReducedCenterInjection
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E)
abbrev T2x37 (c h₀ h₁ h₂ : ℕ) (S : T2x4 ω c)
    (Y : T2x0 ω) (r : ℕ) :=
  {p : T2x24 ω c h₀ h₁ h₂ // T2x57 ω p = S ∧
    finrank K ↥(p.val.1.val ⊓ Y.val) = r ∧
    finrank K ↥(p.val.2.1.val ⊓ Y.val) = r ∧
    finrank K ↥(p.val.2.2.val ⊓ Y.val) = r}
noncomputable def generalReductionLagrangian (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (S : Submodule K E) (hS : S ≤ ω.orthogonal S) (Y : T2x0 ω) :
    T2x0 (T2x2 ω S ha) :=
  ⟨T2x3 ω S Y.val,general_lagrangian_reduction ω S ha hω hS Y.val Y.property⟩
 theorem fixedCommonCenter_injection (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    {c h₀ h₁ h₂ r u : ℕ} (S : T2x4 ω c) (Y : T2x71 ω S.val u) :
    ∃ f : T2x37 ω c h₀ h₁ h₂ S Y.val r →
      SymplecticCenterProfile (T2x2 ω S.val ha)
        (generalReductionLagrangian ω ha hω S.val S.property.1 Y.val)
        (r-u) (h₀-c) (h₁-c) (h₂-c), Function.Injective f := by
  let F := T2x37 ω c h₀ h₁ h₂ S Y.val r
  let Y' := generalReductionLagrangian ω ha hω S.val S.property.1 Y.val
  have heq (p : F) : (p.val.val.1.val ⊓ p.val.val.2.1.val) ⊓ p.val.val.2.2.val = S.val :=
    congrArg Subtype.val p.property.1
  have hL (p : F) : S.val ≤ p.val.val.1.val := (le_of_eq (heq p).symm).trans (inf_le_left.trans inf_le_left)
  have hM (p : F) : S.val ≤ p.val.val.2.1.val := (le_of_eq (heq p).symm).trans (inf_le_left.trans inf_le_right)
  have hN (p : F) : S.val ≤ p.val.val.2.2.val := (le_of_eq (heq p).symm).trans inf_le_right
  let L (p : F) := T2x53 ω S.val ha S.property.1 p.val.val.1 (hL p)
  let M (p : F) := T2x53 ω S.val ha S.property.1 p.val.val.2.1 (hM p)
  let N (p : F) := T2x53 ω S.val ha S.property.1 p.val.val.2.2 (hN p)
  have hd (P : T2x0 ω) (hSP : S.val ≤ P.val)
      (hPr : finrank K ↥(P.val ⊓ Y.val.val) = r) :
      finrank K ↥((T2x53 ω S.val ha S.property.1 P hSP).val ⊓ Y'.val) = r-u := by
    have hh := reduce_center_intersection_finrank ω S.val P.val Y.val.val hSP
      (T2x25 ω S.val P.val P.property hSP)
    rw [Y.property,hPr] at hh
    change finrank K ↥(T2x3 ω S.val P.val ⊓ T2x3 ω S.val Y.val.val) = _
    omega
  let L' (p : F) : T2x7 (T2x2 ω S.val ha) Y' (r-u) :=
    ⟨L p,hd _ _ p.property.2.1⟩
  let M' (p : F) : T2x7 (T2x2 ω S.val ha) Y' (r-u) :=
    ⟨M p,hd _ _ p.property.2.2.1⟩
  let N' (p : F) : T2x7 (T2x2 ω S.val ha) Y' (r-u) :=
    ⟨N p,hd _ _ p.property.2.2.2⟩
  have hzero (p : F) : ((L p).val ⊓ (M p).val) ⊓ (N p).val = ⊥ := by
    change (T2x3 ω S.val p.val.val.1.val ⊓ T2x3 ω S.val p.val.val.2.1.val) ⊓
      T2x3 ω S.val p.val.val.2.2.val = ⊥
    rw [←reduceSubspace_inf ω S.val _ _ (hL p),←reduceSubspace_inf ω S.val _ _ (le_inf (hL p) (hM p)),heq p]
    exact reduceSubspace_self ω S.val
  have hp0 (p : F) : finrank K ↥((L p).val ⊓ (M p).val) = h₀-c := by
    change finrank K ↥(T2x3 ω S.val p.val.val.1.val ⊓ T2x3 ω S.val p.val.val.2.1.val) = _
    rw [reducePair_finrank ω S.val _ _ (hL p) (hM p),p.val.property.2.1,S.property.2]
  have hp1 (p : F) : finrank K ↥((L p).val ⊓ (N p).val) = h₁-c := by
    change finrank K ↥(T2x3 ω S.val p.val.val.1.val ⊓ T2x3 ω S.val p.val.val.2.2.val) = _
    rw [reducePair_finrank ω S.val _ _ (hL p) (hN p),p.val.property.2.2.1,S.property.2]
  have hp2 (p : F) : finrank K ↥((M p).val ⊓ (N p).val) = h₂-c := by
    change finrank K ↥(T2x3 ω S.val p.val.val.2.1.val ⊓ T2x3 ω S.val p.val.val.2.2.val) = _
    rw [reducePair_finrank ω S.val _ _ (hM p) (hN p),p.val.property.2.2.2,S.property.2]
  let f (p : F) : SymplecticCenterProfile (T2x2 ω S.val ha) Y'
      (r-u) (h₀-c) (h₁-c) (h₂-c) :=
    ⟨(L' p,M' p,N' p),hzero p,hp0 p,hp1 p,hp2 p⟩
  refine ⟨f,?_⟩
  intro p q hpq
  have heL : (L p).val = (L q).val := congrArg (fun r => r.val.1.val.val) hpq
  have heM : (M p).val = (M q).val := congrArg (fun r => r.val.2.1.val.val) hpq
  have heN : (N p).val = (N q).val := congrArg (fun r => r.val.2.2.val.val) hpq
  have hpL : p.val.val.1 = q.val.val.1 := congrArg Subtype.val
    (T2x62 ω S.val (a₁ := ⟨p.val.val.1,hL p⟩) (a₂ := ⟨q.val.val.1,hL q⟩) heL)
  have hpM : p.val.val.2.1 = q.val.val.2.1 := congrArg Subtype.val
    (T2x62 ω S.val (a₁ := ⟨p.val.val.2.1,hM p⟩) (a₂ := ⟨q.val.val.2.1,hM q⟩) heM)
  have hpN : p.val.val.2.2 = q.val.val.2.2 := congrArg Subtype.val
    (T2x62 ω S.val (a₁ := ⟨p.val.val.2.2,hN p⟩) (a₂ := ⟨q.val.val.2.2,hN q⟩) heN)
  exact Subtype.ext (Subtype.ext (Prod.ext hpL (Prod.ext hpM hpN)))
end ReducedCenterInjection
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
noncomputable def T2x44 (d r s₀ s₁ s₂ : ℕ) (q : ℝ) : ℝ :=
  ∑ θ : BaseParameters d r s₀ s₁ s₂,
    T2x58 r s₀ s₁ s₂ θ.val * q^(T2x74 d r s₀ s₁ s₂ θ.val)
 theorem reducedPlantedSum_nonneg (d r s₀ s₁ s₂ : ℕ) (q : ℝ) (hq : 0 ≤ q) :
    0 ≤ T2x44 d r s₀ s₁ s₂ q := by
  unfold T2x44
  apply Finset.sum_nonneg
  intro θ _
  unfold T2x58
  positivity
section ReducedCardBound
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
 theorem symplectic_center_profile_card_upper (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D = finrank K E) (Y : T2x0 ω)
    (r s₀ s₁ s₂ : ℕ) (hr : r ≤ D) :
    (Fintype.card K : ℝ)^(3*((r+1).choose 2)) *
      (Nat.card (SymplecticCenterProfile ω Y r s₀ s₁ s₂) : ℝ) ≤
      2^(3*D)*(Fintype.card K : ℝ)^(3*((D+1).choose 2))*
        T2x44 D r s₀ s₁ s₂ (Fintype.card K) := by
  have hd : finrank K Y.val = D := by
    have hh := T2x6 ω Y.val hω Y.property
    omega
  have hp := symplectic_pair_card_bounds ω h2 ha hω D hD Y r hr
  have hq : (0:ℝ) < Fintype.card K := Nat.cast_pos.mpr Fintype.card_pos
  have hc : (0:ℝ) < Nat.card (T2x7 ω Y r) := by
    have hn : (0:ℝ) < (Fintype.card K : ℝ)^((r+1).choose 2) *
      Nat.card (T2x7 ω Y r) := (by positivity : (0:ℝ) <
        (Fintype.card K : ℝ)^((D+1).choose 2)).trans_le hp.1
    exact (mul_pos_iff_of_pos_left (pow_pos hq _)).mp hn
  have hb := symplectic_center_profile_probability_bound ω h2 ha hω Y r s₀ s₁ s₂ (by omega)
  rw [hd] at hb
  change (_ / _) ≤ T2x44 D r s₀ s₁ s₂ (Fintype.card K) at hb
  have hcount := (div_le_iff₀ (pow_pos hc 3)).mp hb
  have hpair : ((Fintype.card K : ℝ)^((r+1).choose 2) *
      Nat.card (T2x7 ω Y r))^3 ≤
      (2^D*(Fintype.card K : ℝ)^((D+1).choose 2))^3 := by
    exact pow_le_pow_left₀ (by positivity) hp.2 3
  calc
    _ ≤ (Fintype.card K : ℝ)^(3*((r+1).choose 2)) *
        (T2x44 D r s₀ s₁ s₂ (Fintype.card K)*
          (Nat.card (T2x7 ω Y r) : ℝ)^3) :=
      mul_le_mul_of_nonneg_left hcount (by positivity)
    _ = ((Fintype.card K : ℝ)^((r+1).choose 2) *
        Nat.card (T2x7 ω Y r))^3 *
        T2x44 D r s₀ s₁ s₂ (Fintype.card K) := by
      rw [mul_pow,←pow_mul,Nat.mul_comm 3]; ring
    _ ≤ (2^D*(Fintype.card K : ℝ)^((D+1).choose 2))^3 *
        T2x44 D r s₀ s₁ s₂ (Fintype.card K) :=
      mul_le_mul_of_nonneg_right hpair (reducedPlantedSum_nonneg _ _ _ _ _ _ (by positivity))
    _ = _ := by rw [mul_pow,←pow_mul,←pow_mul]; congr 2 <;> rw [Nat.mul_comm]
 theorem fixedCommonCenter_card_upper (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D = finrank K E) {c h₀ h₁ h₂ r u : ℕ}
    (S : T2x4 ω c) (Y : T2x71 ω S.val u) (hr : r-u ≤ D-c) :
    (Fintype.card K : ℝ)^(3*((r-u+1).choose 2)) *
      (Nat.card (T2x37 ω c h₀ h₁ h₂ S Y.val r) : ℝ) ≤
      2^(3*(D-c))*(Fintype.card K : ℝ)^(3*((D-c+1).choose 2))*
        T2x44 (D-c) (r-u) (h₀-c) (h₁-c) (h₂-c) (Fintype.card K) := by
  let := Module.finite_of_finite K (M := T2x20 ω S.val)
  have hc := T2x16 ω hω D hD S.val S.property.1
  rw [S.property.2] at hc
  have hd := reducedSpace_finrank ω S.val hω S.property.1
  rw [S.property.2] at hd
  obtain ⟨f,hf⟩ := fixedCommonCenter_injection ω ha hω (h₀ := h₀) (h₁ := h₁) (h₂ := h₂) (r := r) S Y
  have hh := symplectic_center_profile_card_upper (T2x2 ω S.val ha) h2
    (T2x81 ω S.val ha) (T2x13 ω S.val ha hω)
    (D-c) (by omega) (generalReductionLagrangian ω ha hω S.val S.property.1 Y.val)
    (r-u) (h₀-c) (h₁-c) (h₂-c) hr
  exact (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (Nat.card_le_card_of_injective f hf)) (by positivity)).trans hh
end ReducedCardBound
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section FullCenterCoding
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
abbrev T2x27 (D r c : ℕ) := {u : Fin (c+1) // u.val ≤ r ∧ r-u.val ≤ D-c}
noncomputable instance (D r c : ℕ) : Fintype (T2x27 D r c) := Fintype.ofFinite _
abbrev ProfileCenterSet (c h₀ h₁ h₂ r : ℕ) :=
  Σ p : T2x24 ω c h₀ h₁ h₂, T2x69 ω r p.val.1.val p.val.2.1.val p.val.2.2.val
abbrev PlantedCommonData (D c h₀ h₁ h₂ r : ℕ) :=
  Σ S : T2x4 ω c, Σ u : T2x27 D r c,
    Σ Y : T2x71 ω S.val u.val.val, T2x37 ω c h₀ h₁ h₂ S Y.val r
 theorem profileCenter_injection (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D = finrank K E) (c h₀ h₁ h₂ r : ℕ) :
    ∃ f : ProfileCenterSet ω c h₀ h₁ h₂ r → PlantedCommonData ω D c h₀ h₁ h₂ r,
      Function.Injective f := by
  let F := ProfileCenterSet ω c h₀ h₁ h₂ r
  let S (p : F) := T2x57 ω p.1
  let u (p : F) := finrank K ↥((S p).val ⊓ p.2.val.val)
  have hS (p : F) : (S p).val ≤ p.1.val.1.val := inf_le_left.trans inf_le_left
  have hu (p : F) : u p ≤ c :=
    (Submodule.finrank_mono (inf_le_left : (S p).val ⊓ p.2.val.val ≤ (S p).val)).trans_eq (S p).property.2
  have hur (p : F) : u p ≤ r :=
    (Submodule.finrank_mono (inf_le_inf_right p.2.val.val (hS p))).trans_eq p.2.property.1
  have hdr (p : F) : r-u p ≤ D-c := by
    have hi := (S p).property.1
    have hc := T2x16 ω hω D hD (S p).val hi
    have hd := reducedSpace_finrank ω (S p).val hω hi
    rw [(S p).property.2,hD.symm] at hd
    rw [(S p).property.2] at hc
    let Y' := generalReductionLagrangian ω ha hω (S p).val hi p.2.val
    let := Module.finite_of_finite K (M := T2x20 ω (S p).val)
    have hy := T2x6 (T2x2 ω (S p).val ha) Y'.val
      (T2x13 ω (S p).val ha hω) Y'.property
    have he := reduce_center_intersection_finrank ω (S p).val p.1.val.1.val p.2.val.val
      (hS p) (T2x25 ω (S p).val p.1.val.1.val p.1.val.1.property (hS p))
    rw [p.2.property.1] at he
    have hm := Submodule.finrank_mono (inf_le_right :
      T2x3 ω (S p).val p.1.val.1.val ⊓ Y'.val ≤ Y'.val)
    change finrank K ↥(T2x3 ω (S p).val p.1.val.1.val ⊓ Y'.val) + u p = r at he
    omega
  let f (p : F) : PlantedCommonData ω D c h₀ h₁ h₂ r :=
    ⟨S p,⟨⟨u p,by have := hu p; omega⟩,hur p,hdr p⟩,⟨p.2.val,rfl⟩,
      ⟨p.1,rfl,p.2.property⟩⟩
  refine ⟨f,?_⟩
  intro p q hpq
  have hprofile : p.1 = q.1 := congrArg (fun x : PlantedCommonData ω D c h₀ h₁ h₂ r => x.2.2.2.val) hpq
  have hcenter : p.2.val = q.2.val := congrArg (fun x : PlantedCommonData ω D c h₀ h₁ h₂ r => x.2.2.1.val) hpq
  cases p with
  | mk p Y =>
    cases q with
    | mk q Z =>
      dsimp only at hprofile hcenter
      subst q
      exact congrArg (Sigma.mk p) (Subtype.ext hcenter)
end FullCenterCoding
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
 theorem unweight_count_bound {q x C y : ℝ} (hq : 0 < q) (a b : ℕ)
    (h : q^a*x ≤ C*q^b*y) : x ≤ C*q^((b:ℝ)-a)*y := by
  apply le_of_mul_le_mul_left (a := q^a) ?_ (pow_pos hq _)
  refine h.trans_eq ?_
  rw [Real.rpow_sub hq,Real.rpow_natCast,Real.rpow_natCast]
  field_simp
section CommonCountSummation
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
 theorem fixedCommonCenter_card_rpow_upper (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D = finrank K E) {c h₀ h₁ h₂ r u : ℕ}
    (S : T2x4 ω c) (Y : T2x71 ω S.val u) (hr : r-u ≤ D-c) :
    (Nat.card (T2x37 ω c h₀ h₁ h₂ S Y.val r) : ℝ) ≤
      2^(3*(D-c))*(Fintype.card K : ℝ)^((3*((D-c+1).choose 2):ℕ)-(3*((r-u+1).choose 2):ℝ))*
        T2x44 (D-c) (r-u) (h₀-c) (h₁-c) (h₂-c) (Fintype.card K) :=
by
  simpa only [Nat.cast_mul,Nat.cast_ofNat] using
    unweight_count_bound (Nat.cast_pos.mpr Fintype.card_pos) _ _
      (fixedCommonCenter_card_upper ω h2 ha hω D hD (h₀ := h₀) (h₁ := h₁) (h₂ := h₂) S Y hr)
 theorem commonData_fixed_card_upper (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D = finrank K E) {c h₀ h₁ h₂ r : ℕ}
    (S : T2x4 ω c) (u : T2x27 D r c) :
    (Nat.card (Σ Y : T2x71 ω S.val u.val.val,
      T2x37 ω c h₀ h₁ h₂ S Y.val r) : ℝ) ≤
      (2^u.val.val*T2x1 (D-u.val.val))*2^(3*(D-c)) *
        (Fintype.card K : ℝ)^((u.val.val*(c-u.val.val)+(D-u.val.val+1).choose 2:ℕ)+
          (3*((D-c+1).choose 2):ℕ)-(3*((r-u.val.val+1).choose 2):ℝ))*
        T2x44 (D-c) (r-u.val.val) (h₀-c) (h₁-c) (h₂-c) (Fintype.card K) := by
  classical
  let := Fintype.ofFinite (T2x71 ω S.val u.val.val)
  have hq : (0:ℝ) < Fintype.card K := Nat.cast_pos.mpr Fintype.card_pos
  let A : ℝ := 2^(3*(D-c))*(Fintype.card K : ℝ)^((3*((D-c+1).choose 2):ℕ)-(3*((r-u.val.val+1).choose 2):ℝ))*
        T2x44 (D-c) (r-u.val.val) (h₀-c) (h₁-c) (h₂-c) (Fintype.card K)
  have hA : 0 ≤ A := mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg hq.le _))
    (reducedPlantedSum_nonneg _ _ _ _ _ _ hq.le)
  have hu : u.val.val ≤ finrank K S.val := by rw [S.property.2]; exact Nat.le_of_lt_succ u.val.isLt
  have hc := commonCenter_card_upper ω h2 ha hω D hD S.val S.property.1 u.val.val hu
  rw [S.property.2] at hc
  calc
    _ = ∑ Y : T2x71 ω S.val u.val.val,
        (Nat.card (T2x37 ω c h₀ h₁ h₂ S Y.val r) : ℝ) := by rw [Nat.card_sigma,Nat.cast_sum]
    _ ≤ ∑ _Y : T2x71 ω S.val u.val.val, A :=
      Finset.sum_le_sum (fun Y _ => fixedCommonCenter_card_rpow_upper ω h2 ha hω D hD S Y u.property.2)
    _ = (Nat.card (T2x71 ω S.val u.val.val) : ℝ)*A := by simp [Nat.card_eq_fintype_card]
    _ ≤ (2^u.val.val*T2x1 (D-u.val.val)*
        (Fintype.card K : ℝ)^(u.val.val*(c-u.val.val)+(D-u.val.val+1).choose 2))*A :=
      mul_le_mul_of_nonneg_right hc hA
    _ = _ := by
      let a := u.val.val*(c-u.val.val)+(D-u.val.val+1).choose 2
      let b := 3*((D-c+1).choose 2)
      let e : ℝ := 3*((r-u.val.val+1).choose 2:ℝ)
      change (_*(Fintype.card K : ℝ)^a)*A = _*(Fintype.card K : ℝ)^((a:ℝ)+b-e)*_
      rw [show (a:ℝ)+b-e = a+((b:ℝ)-e) by ring,Real.rpow_add hq,Real.rpow_natCast]
      dsimp [A,a,b,e]
      ring
end CommonCountSummation
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
noncomputable def commonPlantedTerm (D c r h₀ h₁ h₂ : ℕ) (u : T2x27 D r c) (q : ℝ) : ℝ :=
  (2^u.val.val*T2x1 (D-u.val.val))*2^(3*(D-c)) *
    q^((u.val.val*(c-u.val.val)+(D-u.val.val+1).choose 2:ℕ)+
      (3*((D-c+1).choose 2):ℕ)-(3*((r-u.val.val+1).choose 2):ℝ))*
    T2x44 (D-c) (r-u.val.val) (h₀-c) (h₁-c) (h₂-c) q
 theorem commonPlantedTerm_nonneg (D c r h₀ h₁ h₂ : ℕ) (u : T2x27 D r c) (q : ℝ)
    (hq : 0 ≤ q) : 0 ≤ commonPlantedTerm D c r h₀ h₁ h₂ u q := by
  unfold commonPlantedTerm
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by positivity)
    (T2x10 _).le) (by positivity)) (Real.rpow_nonneg hq _))
    (reducedPlantedSum_nonneg _ _ _ _ _ _ hq)
section FullProfileCenterBound
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
 theorem profileCenter_card_upper (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D = finrank K E) (c h₀ h₁ h₂ r : ℕ) (hc : c ≤ D) :
    (Nat.card (ProfileCenterSet ω c h₀ h₁ h₂ r) : ℝ) ≤
      (T2x1 D*2^c)*(Fintype.card K : ℝ)^(T2x19 D c) *
        ∑ u : T2x27 D r c, commonPlantedTerm D c r h₀ h₁ h₂ u (Fintype.card K) := by
  classical
  let := Fintype.ofFinite (T2x4 ω c)
  obtain ⟨f,hf⟩ := profileCenter_injection ω ha hω D hD c h₀ h₁ h₂ r
  have hs (S : T2x4 ω c) :
      (Nat.card (Σ u : T2x27 D r c, Σ Y : T2x71 ω S.val u.val.val,
        T2x37 ω c h₀ h₁ h₂ S Y.val r) : ℝ) ≤
      ∑ u : T2x27 D r c, commonPlantedTerm D c r h₀ h₁ h₂ u (Fintype.card K) := by
    rw [Nat.card_sigma,Nat.cast_sum]
    exact Finset.sum_le_sum (fun u _ => commonData_fixed_card_upper ω h2 ha hω D hD S u)
  calc
    _ ≤ (Nat.card (PlantedCommonData ω D c h₀ h₁ h₂ r) : ℝ) :=
      Nat.cast_le.mpr (Nat.card_le_card_of_injective f hf)
    _ = ∑ S : T2x4 ω c,
        (Nat.card (Σ u : T2x27 D r c, Σ Y : T2x71 ω S.val u.val.val,
          T2x37 ω c h₀ h₁ h₂ S Y.val r) : ℝ) := by rw [Nat.card_sigma,Nat.cast_sum]
    _ ≤ ∑ _S : T2x4 ω c,
        ∑ u : T2x27 D r c, commonPlantedTerm D c r h₀ h₁ h₂ u (Fintype.card K) :=
      Finset.sum_le_sum (fun S _ => hs S)
    _ = (Nat.card (T2x4 ω c) : ℝ)*
        ∑ u : T2x27 D r c, commonPlantedTerm D c r h₀ h₁ h₂ u (Fintype.card K) := by
      simp [Nat.card_eq_fintype_card]
    _ ≤ _ := mul_le_mul_of_nonneg_right (isotropic_card_bounds ω h2 ha hω D hD c hc).2
      (Finset.sum_nonneg (fun u _ => commonPlantedTerm_nonneg _ _ _ _ _ _ _ _ (by positivity)))
end FullProfileCenterBound
end SidorenkoCounterexample
namespace SidorenkoCounterexample
 theorem normalized_count_ratio_bound {p t s O Z T A L C B : ℝ}
    (hp : 0 < p) (hA : 0 < A) (hZ : 0 ≤ Z) (hT : 0 ≤ T) (_hO : 0 ≤ O)
    (hL : 0 ≤ L) (hC : 0 ≤ C) (_hB : 0 ≤ B) (hs : 0 ≤ s) (_ht : 0 ≤ t)
    (hOrbit : p^3 ≤ C*s*O) (hCenter : O*Z ≤ T)
    (hPair : p ≤ t*A) (hLag : L ≤ B*p) :
    Z*L^2/A^3 ≤ C*B^2*s*t^3*T/p^4 := by
  have hbar : p^3*Z ≤ C*s*T := by
    calc
      _ ≤ (C*s*O)*Z := mul_le_mul_of_nonneg_right hOrbit hZ
      _ = (C*s)*(O*Z) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hCenter (mul_nonneg hC hs)
  have hl : L^2 ≤ (B*p)^2 := pow_le_pow_left₀ hL hLag 2
  have htt : p^3 ≤ (t*A)^3 := pow_le_pow_left₀ hp.le hPair 3
  apply (div_le_div_iff₀ (pow_pos hA 3) (pow_pos hp 4)).mpr
  calc
    Z*L^2*p^4 ≤ Z*(B*p)^2*p^4 := by gcongr
    _ = (p^3*Z)*B^2*p^3 := by ring
    _ ≤ (C*s*T)*B^2*(t*A)^3 := by
      exact mul_le_mul (mul_le_mul_of_nonneg_right hbar (sq_nonneg B)) htt
        (by positivity) (by positivity)
    _ = _ := by ring
open Module
section OrbitCenterProfile
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E)
 omit [FiniteDimensional K E] in
 theorem orbit_member_profile (L M N : T2x0 ω)
    (P : T2x15 ω L.val M.val N.val) :
    ω.orthogonal P.val.1 = P.val.1 ∧ ω.orthogonal P.val.2.1 = P.val.2.1 ∧
    ω.orthogonal P.val.2.2 = P.val.2.2 ∧
    finrank K ↥((P.val.1 ⊓ P.val.2.1) ⊓ P.val.2.2) = finrank K ↥((L.val ⊓ M.val) ⊓ N.val) ∧
    finrank K ↥(P.val.1 ⊓ P.val.2.1) = finrank K ↥(L.val ⊓ M.val) ∧
    finrank K ↥(P.val.1 ⊓ P.val.2.2) = finrank K ↥(L.val ⊓ N.val) ∧
    finrank K ↥(P.val.2.1 ⊓ P.val.2.2) = finrank K ↥(M.val ⊓ N.val) := by
  obtain ⟨e,he,hL,hM,hN⟩ := P.property
  rw [←hL,←hM,←hN]
  refine ⟨(T2x45 ω e he L).property,
    (T2x45 ω e he M).property,
    (T2x45 ω e he N).property,?_,T2x83 e _ _,T2x83 e _ _,T2x83 e _ _⟩
  rw [←Submodule.map_inf e.toLinearMap e.injective,←Submodule.map_inf e.toLinearMap e.injective,e.finrank_map_eq]
omit [FiniteDimensional K E] in
 theorem orbitCenter_profile_injection (L M N : T2x0 ω) (r : ℕ) :
    ∃ f : (Σ P : T2x15 ω L.val M.val N.val,
      T2x69 ω r P.val.1 P.val.2.1 P.val.2.2) →
      ProfileCenterSet ω (finrank K ↥((L.val ⊓ M.val) ⊓ N.val))
        (finrank K ↥(L.val ⊓ M.val)) (finrank K ↥(L.val ⊓ N.val)) (finrank K ↥(M.val ⊓ N.val)) r,
      Function.Injective f := by
  let F := Σ P : T2x15 ω L.val M.val N.val,
      T2x69 ω r P.val.1 P.val.2.1 P.val.2.2
  let G := ProfileCenterSet ω (finrank K ↥((L.val ⊓ M.val) ⊓ N.val))
        (finrank K ↥(L.val ⊓ M.val)) (finrank K ↥(L.val ⊓ N.val)) (finrank K ↥(M.val ⊓ N.val)) r
  let f (p : F) : G :=
    let hp := orbit_member_profile ω L M N p.1
    ⟨⟨(⟨p.1.val.1,hp.1⟩,⟨p.1.val.2.1,hp.2.1⟩,⟨p.1.val.2.2,hp.2.2.1⟩),hp.2.2.2⟩,p.2⟩
  refine ⟨f,?_⟩
  intro p q h
  have he : p.1 = q.1 := Subtype.ext (congrArg (fun s : G => (s.1.val.1.val,s.1.val.2.1.val,s.1.val.2.2.val)) h)
  have hy : p.2.val = q.2.val := congrArg (fun s : G => s.2.val) h
  cases p with
  | mk p Y =>
    cases q with
    | mk q Z =>
      dsimp only at he hy
      subst q
      exact congrArg (Sigma.mk p) (Subtype.ext hy)
 omit [FiniteDimensional K E] in
 theorem orbit_center_count_le_profile [Finite E] (L M N : T2x0 ω) (r : ℕ) :
    Nat.card (T2x15 ω L.val M.val N.val) * Nat.card (T2x69 ω r L.val M.val N.val) ≤
      Nat.card (ProfileCenterSet ω (finrank K ↥((L.val ⊓ M.val) ⊓ N.val))
        (finrank K ↥(L.val ⊓ M.val)) (finrank K ↥(L.val ⊓ N.val)) (finrank K ↥(M.val ⊓ N.val)) r) := by
  rw [←tripleCenterOrbit_card]
  obtain ⟨f,hf⟩ := orbitCenter_profile_injection ω L M N r
  exact Nat.card_le_card_of_injective f hf
end OrbitCenterProfile
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section PointwisePlanted
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
noncomputable def tripleFaceDensity (r : ℕ) (A L M N : T2x0 ω) : ℝ :=
  (Nat.card (T2x69 ω r L.val M.val N.val) : ℝ)*
    (Nat.card (T2x0 ω) : ℝ)^2 /
    (Nat.card (T2x7 ω A r) : ℝ)^3
 theorem symplectic_center_stratum_card_pos (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D = finrank K E) (A : T2x0 ω) (r : ℕ) (hr : r ≤ D) :
    (0:ℝ) < Nat.card (T2x7 ω A r) := by
  have hp := (symplectic_pair_card_bounds ω h2 ha hω D hD A r hr).1
  have hq : (0:ℝ) < Fintype.card K := Nat.cast_pos.mpr Fintype.card_pos
  have hn : (0:ℝ) < (Fintype.card K : ℝ)^((r+1).choose 2) *
      Nat.card (T2x7 ω A r) := (by positivity : (0:ℝ) <
        (Fintype.card K : ℝ)^((D+1).choose 2)).trans_le hp
  exact (mul_pos_iff_of_pos_left (pow_pos hq _)).mp hn
 theorem tripleFaceDensity_profile_bound [Invertible (2:K)]
    (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D = finrank K E) (hOrbitGood : TB2_Good ω D) (hq : 4*T2x1 D ≤ (Fintype.card K : ℝ))
    (r : ℕ) (hr : r ≤ D) (A L M N : T2x0 ω) :
    tripleFaceDensity ω r A L M N ≤
      (orbitMassConstant D*(T2x1 D)^2) *
        (Fintype.card K : ℝ)^((tripleDefect D L.val M.val N.val : ℝ)+
          (3*((r+1).choose 2):ℕ)-(4*((D+1).choose 2):ℕ)) *
        (Nat.card (ProfileCenterSet ω (finrank K ↥((L.val ⊓ M.val) ⊓ N.val))
          (finrank K ↥(L.val ⊓ M.val)) (finrank K ↥(L.val ⊓ N.val)) (finrank K ↥(M.val ⊓ N.val)) r) : ℝ) := by
  let q : ℝ := Fintype.card K
  have hq0 : 0 < q := Nat.cast_pos.mpr Fintype.card_pos
  have hOrbit := hOrbitGood L M N
  have hCenter := orbit_center_count_le_profile ω L M N r
  have hPair := (symplectic_pair_card_bounds ω h2 ha hω D hD A r hr).1
  have hLag := (T2x18 ω h2 ha hω D hD).2
  have hi := normalized_count_ratio_bound
    (p := q^((D+1).choose 2)) (t := q^((r+1).choose 2))
    (s := q^(tripleDefect D L.val M.val N.val))
    (O := Nat.card (T2x15 ω L.val M.val N.val))
    (Z := Nat.card (T2x69 ω r L.val M.val N.val))
    (T := Nat.card (ProfileCenterSet ω (finrank K ↥((L.val ⊓ M.val) ⊓ N.val))
      (finrank K ↥(L.val ⊓ M.val)) (finrank K ↥(L.val ⊓ N.val)) (finrank K ↥(M.val ⊓ N.val)) r))
    (A := Nat.card (T2x7 ω A r)) (L := Nat.card (T2x0 ω))
    (C := orbitMassConstant D) (B := T2x1 D)
    (pow_pos hq0 _) (symplectic_center_stratum_card_pos ω h2 ha hω D hD A r hr)
    (by positivity) (by positivity) (by positivity) (by positivity)
    (orbitMassConstant_pos D).le (T2x10 D).le (by positivity) (by positivity)
    (by simpa only [←pow_mul,Nat.mul_comm] using hOrbit)
    (by exact_mod_cast hCenter) hPair hLag
  refine hi.trans_eq ?_
  change _ = _*q^((tripleDefect D L.val M.val N.val : ℝ)+(3*((r+1).choose 2):ℕ)-(4*((D+1).choose 2):ℕ))*_
  rw [Real.rpow_sub hq0,Real.rpow_add hq0,Real.rpow_natCast,Real.rpow_natCast,Real.rpow_natCast]
  simp only [pow_mul,pow_succ]
  ring
 theorem tripleFaceDensity_full_bound [Invertible (2:K)]
    (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D = finrank K E) (hOrbitGood : TB2_Good ω D) (hq : 4*T2x1 D ≤ (Fintype.card K : ℝ))
    (r : ℕ) (hr : r ≤ D) (A L M N : T2x0 ω) :
    let c := finrank K ↥((L.val ⊓ M.val) ⊓ N.val)
    let h₀ := finrank K ↥(L.val ⊓ M.val)
    let h₁ := finrank K ↥(L.val ⊓ N.val)
    let h₂ := finrank K ↥(M.val ⊓ N.val)
    tripleFaceDensity ω r A L M N ≤
      (orbitMassConstant D*(T2x1 D)^2) *
        (Fintype.card K : ℝ)^((tripleDefect D L.val M.val N.val : ℝ)+
          (3*((r+1).choose 2):ℕ)-(4*((D+1).choose 2):ℕ)) *
        ((T2x1 D*2^c)*(Fintype.card K : ℝ)^(T2x19 D c) *
          ∑ u : T2x27 D r c, commonPlantedTerm D c r h₀ h₁ h₂ u (Fintype.card K)) := by
  dsimp only
  have hc : finrank K ↥((L.val ⊓ M.val) ⊓ N.val) ≤ D :=
    T2x16 ω hω D hD _ (by intro x hx y hy; exact L.property.ge hx.1.1 y hy.1.1)
  have hh := profileCenter_card_upper ω h2 ha hω D hD
    (finrank K ↥((L.val ⊓ M.val) ⊓ N.val))
    (finrank K ↥(L.val ⊓ M.val)) (finrank K ↥(L.val ⊓ N.val)) (finrank K ↥(M.val ⊓ N.val)) r hc
  have hq0 : (0:ℝ) ≤ Fintype.card K := by positivity
  exact (tripleFaceDensity_profile_bound ω h2 ha hω D hD hOrbitGood hq r hr A L M N).trans
    (mul_le_mul_of_nonneg_left hh (mul_nonneg (mul_nonneg (orbitMassConstant_pos D).le (sq_nonneg _))
      (Real.rpow_nonneg hq0 _)))
end PointwisePlanted
end SidorenkoCounterexample
end OAI
namespace OAI
namespace SidorenkoCounterexample
private theorem quadratic_ge_right (A B C x b : ℝ)
    (hA : 0 ≤ A) (hxb : x ≤ b) (hderiv : 2 * A * b + B ≤ 0) :
    A * b ^ 2 + B * b + C ≤ A * x ^ 2 + B * x + C := by
  have h : 0 ≤ -A * (x + b) - B := by
    nlinarith [mul_nonneg hA (sub_nonneg.mpr hxb)]
  have := mul_nonneg (sub_nonneg.mpr hxb) h
  nlinarith
private theorem quadratic_ge_endpoints (A B C a b x k : ℝ)
    (hA : A ≤ 0) (hax : a ≤ x) (hxb : x ≤ b)
    (ha : k ≤ A * a ^ 2 + B * a + C)
    (hb : k ≤ A * b ^ 2 + B * b + C) :
    k ≤ A * x ^ 2 + B * x + C := by
  by_cases hab : a = b
  · have : x = a := by linarith
    simpa [this] using ha
  have hab' : 0 < b - a := sub_pos.mpr (lt_of_le_of_ne (hax.trans hxb) hab)
  have h₁ := mul_nonneg (sub_nonneg.mpr hxb) (sub_nonneg.mpr ha)
  have h₂ := mul_nonneg (sub_nonneg.mpr hax) (sub_nonneg.mpr hb)
  have h₃ := mul_nonneg (mul_nonneg (neg_nonneg.mpr hA)
    (mul_nonneg (sub_nonneg.mpr hax) (sub_nonneg.mpr hxb)))
    (le_of_lt hab')
  have hsum : 0 ≤ (b - a) * (A * x ^ 2 + B * x + C - k) := by
    nlinarith only [h₁, h₂, h₃]
  exact le_of_sub_nonneg ((nonneg_of_mul_nonneg_right hsum hab'))
theorem coercivity_scalar_pos (P T δ : ℝ) (hP : 0 ≤ P) (hδ : 0 ≤ δ)
    (_hT : 0 ≤ T) (hTP : T ≤ P + 3 * δ) :
    (P ^ 2 + δ ^ 2) / 18 ≤
      3 * δ ^ 2 / 4 + (2 * P - T) ^ 2 / 18 + (5 * P - T) * δ / 6 -
        (min (P / 3 + δ) ((P - T + 3 * δ) / 2)) ^ 2 / 2 := by
  have hPd := mul_nonneg hP hδ
  by_cases ht : T ≤ P / 3 + δ
  · rw [min_eq_left (by linarith)]
    have hmono := quadratic_ge_right (1/18) (-2*P/9-δ/6)
      (3*δ^2/4+2*P^2/9+5*P*δ/6-(P/3+δ)^2/2)
      T (P/3+δ) (by norm_num) ht (by nlinarith)
    nlinarith [sq_nonneg P, sq_nonneg δ]
  · rw [min_eq_right (by linarith)]
    have hl : P / 3 + δ ≤ T := by linarith
    have hem := quadratic_ge_endpoints (-5/72) (P/36+7*δ/12)
      (7*P^2/72+P*δ/12-3*δ^2/8) (P/3+δ) (P+3*δ) T
      ((P^2+δ^2)/18) (by norm_num) hl hTP
      (by nlinarith [sq_nonneg P, sq_nonneg δ])
      (by nlinarith [sq_nonneg P, sq_nonneg δ])
    nlinarith only [hem]
theorem coercivity_scalar_neg (x T y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (_hT : 0 ≤ T) (hTx : T ≤ x) :
    (x ^ 2 + y ^ 2) / 18 ≤
      y ^ 2 / 4 + (2*x-T)*y/3 + (2*x-T)^2/18 -
        (min (x/3) ((x-T)/2))^2/2 := by
  have hxy := mul_nonneg hx hy
  by_cases ht : T ≤ x/3
  · rw [min_eq_left (by linarith)]
    have hmono := quadratic_ge_right (1/18) (-2*x/9-y/3)
      (y^2/4+2*x*y/3+x^2/6) T (x/3) (by norm_num) ht (by nlinarith)
    nlinarith [sq_nonneg x, sq_nonneg y]
  · rw [min_eq_right (by linarith)]
    have hem := quadratic_ge_endpoints (-5/72) (x/36-y/3)
      (y^2/4+2*x*y/3+7*x^2/72) (x/3) x T ((x^2+y^2)/18)
      (by norm_num) (by linarith) hTx
      (by nlinarith [sq_nonneg x, sq_nonneg y])
      (by nlinarith [sq_nonneg x, sq_nonneg y])
    nlinarith only [hem]
noncomputable def scalarForm (c d P T δ : ℝ) : ℝ :=
  (c*(d+δ)-δ*d+2*δ^2)/4 + (2*P-T)^2/18 + δ*P - c*(P+T)/6 -
    (min (P/3+δ) ((P-T+3*δ)/2))^2/2
theorem coercivity_scalar (c d P T δ : ℝ) (hc : |δ| ≤ c)
    (hd : P + T ≤ d) (hP : 0 ≤ P) (hT : 0 ≤ T) (hTP : T ≤ P+3*δ) :
    (P^2+T^2+δ^2)/342 + (c-|δ|)*(d+3*δ)/12 ≤ scalarForm c d P T δ := by
  have hsplit : scalarForm |δ| d P T δ + (c-|δ|)*(d+3*δ)/12 ≤
      scalarForm c d P T δ := by
    have hm := mul_nonneg (sub_nonneg.mpr hc) (sub_nonneg.mpr hd)
    dsimp [scalarForm]
    nlinarith only [hm]
  suffices h : (P^2+T^2+δ^2)/342 ≤ scalarForm |δ| d P T δ by linarith only [h, hsplit]
  by_cases hδ : 0 ≤ δ
  · rw [abs_of_nonneg hδ]
    have hs := coercivity_scalar_pos P T δ hP hδ hT hTP
    have hsquare := mul_nonneg (sub_nonneg.mpr hTP) (show 0 ≤ P+3*δ+T by linarith)
    have hsize : P^2+T^2+δ^2 ≤ 19*(P^2+δ^2) := by
      nlinarith only [hsquare, sq_nonneg (P-3*δ), sq_nonneg P]
    dsimp [scalarForm]
    nlinarith only [hs, hsize]
  · have hδ' : δ ≤ 0 := le_of_not_ge hδ
    rw [abs_of_nonpos hδ']
    have hx : 0 ≤ P+3*δ := by linarith
    have hs := coercivity_scalar_neg (P+3*δ) T (-δ) hx (neg_nonneg.mpr hδ') hT hTP
    rw [show (P+3*δ)/3 = P/3+δ by ring,
      show (P+3*δ-T)/2 = (P-T+3*δ)/2 by ring] at hs
    have hsquare := mul_nonneg (sub_nonneg.mpr hTP) (show 0 ≤ P+3*δ+T by linarith)
    have hsize : P^2+T^2+δ^2 ≤ 19*((P+3*δ)^2+δ^2) := by
      nlinarith only [hsquare, sq_nonneg (P+6*δ), sq_nonneg (P+3*δ)]
    have hdim := mul_nonneg (neg_nonneg.mpr hδ') (sub_nonneg.mpr hd)
    dsimp [scalarForm]
    nlinarith only [hs, hsize, hdim]
open scoped BigOperators
noncomputable def quadraticPart (c d δ v : ℝ) (p t : Fin 3 → ℝ) : ℝ :=
  (c*(d+δ)-δ*d+2*δ^2)/4 + (∑ i, (2*p i-t i)^2)/6 +
    δ*(∑ i, p i) - c*((∑ i, p i)+(∑ i, t i))/6 +
    ((d-3*δ)/2-(∑ i, p i))*v+v^2/2
private theorem three_sq (z : Fin 3 → ℝ) : (∑ i, z i)^2 ≤ 3*∑ i, (z i)^2 := by
  simp only [Fin.sum_univ_three]
  nlinarith [sq_nonneg (z 0-z 1), sq_nonneg (z 0-z 2), sq_nonneg (z 1-z 2)]
theorem coercivity (c d δ v : ℝ) (p t : Fin 3 → ℝ)
    (hc : |δ| ≤ c) (hd : (∑ i, p i)+(∑ i, t i) ≤ d)
    (hp : ∀ i, 0 ≤ p i) (ht : ∀ i, 0 ≤ t i) (hv : 0 ≤ v)
    (htp : ∀ i, t i ≤ p i+δ) (hvp : ∀ i, v ≤ p i+δ)
    (hw : 0 ≤ (d-3*δ)/2-(∑ i, p i)+v) :
    ((∑ i, p i)^2+(∑ i, t i)^2+δ^2)/342 + (c-|δ|)*(d+3*δ)/12 ≤
      quadraticPart c d δ v p t := by
  let P := ∑ i, p i
  let T := ∑ i, t i
  have hP : 0 ≤ P := Finset.sum_nonneg fun i _ => hp i
  have hT : 0 ≤ T := Finset.sum_nonneg fun i _ => ht i
  have hTP : T ≤ P+3*δ := by
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ => htp i)
    simpa [Finset.sum_add_distrib, P, T] using hh
  have hvP : v ≤ P/3+δ := by
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hvp i)
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] at hh
    change (3:ℝ)*v ≤ P+3*δ at hh
    linarith only [hh]
  let m := min (P/3+δ) ((P-T+3*δ)/2)
  let k := (d-3*δ)/2-P
  have hm : 0 ≤ m := le_min (by linarith only [hv, hvP]) (by linarith only [hTP])
  have hkm : -k ≤ m := by
    apply le_min
    · dsimp [k]
      change 0 ≤ (d-3*δ)/2-P+v at hw
      linarith only [hw, hvP]
    · dsimp [k]
      change P+T ≤ d at hd
      linarith only [hd]
  have hvquad : -m^2/2 ≤ k*v+v^2/2 := by
    by_cases hk : 0 ≤ k
    · nlinarith only [mul_nonneg hk hv, sq_nonneg v, sq_nonneg m]
    · have hh₁ : 0 ≤ m+k := by linarith only [hkm]
      have hh₂ : 0 ≤ m-k := by linarith only [hm, hk]
      nlinarith only [mul_nonneg hh₁ hh₂, sq_nonneg (v+k)]
  have hsq := three_sq (fun i => 2*p i-t i)
  have hsum : (∑ i, (2*p i-t i)) = 2*P-T := by
    simp [Finset.sum_sub_distrib, Finset.mul_sum, P, T]
  rw [hsum] at hsq
  have hscalar := coercivity_scalar c d P T δ hc hd hP hT hTP
  change (P^2+T^2+δ^2)/342 + (c-|δ|)*(d+3*δ)/12 ≤ _
  calc
    _ ≤ scalarForm c d P T δ := hscalar
    _ ≤ quadraticPart c d δ v p t := by
      dsimp [scalarForm, quadraticPart]
      change _ ≤ (c*(d+δ)-δ*d+2*δ^2)/4 + (∑ i, (2*p i-t i)^2)/6 +
        δ*P-c*(P+T)/6+k*v+v^2/2
      change - (min (P/3+δ) ((P-T+3*δ)/2))^2/2 ≤ _ at hvquad
      nlinarith only [hsq, hvquad]
noncomputable def triangular (n : ℝ) : ℝ := n*(n+1)/2
noncomputable def baseline (c d : ℝ) (p t : Fin 3 → ℝ) : ℝ :=
  ((d+c+1)*c + ∑ i, triangular (p i+t i))/2 -
    (∑ i, triangular (c+p i+t i))/6
noncomputable def plantedGain (c d δ v : ℝ) (p t : Fin 3 → ℝ) : ℝ :=
  ((d+c)/2+c+1)*((c+δ)/2)-2*((c+δ)/2)^2 +
    (∑ i, triangular (p i+t i)) - δ*(∑ i, p i) - (∑ i, (p i)^2) -
    v*((d-3*δ)/2-(∑ i, p i)+v) - (∑ i, triangular (t i)) + triangular v
theorem slack_identity (c d δ v : ℝ) (p t : Fin 3 → ℝ) :
    baseline c d p t - plantedGain c d δ v p t =
    (c*(d+δ-1)-δ*(d+2)+2*δ^2)/4 +
    (∑ i, ((2*p i-t i)*(2*p i-t i-1)/6 + δ*p i-c*(p i+t i)/6)) +
    v*((d-3*δ)/2-(∑ i, p i)+v) - triangular v := by
  simp only [baseline, plantedGain, triangular, Fin.sum_univ_three]
  ring
theorem slack_quadratic (c d δ v : ℝ) (p t : Fin 3 → ℝ) :
    baseline c d p t - plantedGain c d δ v p t =
    quadraticPart c d δ v p t - c/4 - δ/2 -
      (2*(∑ i, p i)-(∑ i, t i))/6-v/2 := by
  rw [slack_identity]
  simp only [quadraticPart, triangular, Fin.sum_univ_three]
  ring
theorem slack_uniform_linear (c d δ v M : ℝ) (p t : Fin 3 → ℝ)
    (hc : 0 ≤ c) (hδ : δ ≤ c) (hv : v ≤ M)
    (hP : (∑ i, p i) ≤ 3*(M-c)) (hT : 0 ≤ ∑ i, t i) :
    quadraticPart c d δ v p t - 3*M/2 ≤
      baseline c d p t - plantedGain c d δ v p t := by
  rw [slack_quadratic]
  linarith only [hc, hδ, hv, hP, hT]
theorem slack_leading_coefficient (c d δ v : ℝ) (p t : Fin 3 → ℝ) :
    baseline c d p t - plantedGain c d δ v p t =
    ((c-δ+2*v)/4)*d + baseline c 0 p t - plantedGain c 0 δ v p t := by
  simp only [baseline, plantedGain, triangular, Fin.sum_univ_three]
  ring
theorem slack_integer_regime (c d : ℝ) (p t : Fin 3 → ℝ) :
    baseline c d p t - plantedGain c d c 0 p t =
    (3*c^2-3*c)/4 +
      (∑ i, ((2*p i-t i)^2+(c-1)*(2*p i-t i)+3*c*p i))/6 := by
  simp only [baseline, plantedGain, triangular, Fin.sum_univ_three]
  ring
theorem slack_pos_of_two_le (c d : ℝ) (p t : Fin 3 → ℝ)
    (hc : 2 ≤ c) (hp : ∀ i, 0 ≤ p i) :
    0 < baseline c d p t - plantedGain c d c 0 p t := by
  rw [slack_integer_regime]
  have hi (i : Fin 3) : -(c-1)^2/4 ≤
      (2*p i-t i)^2+(c-1)*(2*p i-t i)+3*c*p i := by
    have hh := mul_nonneg (show 0 ≤ c by linarith) (hp i)
    nlinarith only [hh, sq_nonneg (2*p i-t i+(c-1)/2)]
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hi i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hh
  have hpos : 0 < (c-1)*(5*c+1) := mul_pos (by linarith) (by linarith)
  nlinarith only [hh, hpos]
theorem integer_pair_slack (p t : ℤ) (hp : 0 ≤ p) (ht : 0 ≤ t) (htp : t ≤ p) :
    0 ≤ (2*p-t)*(2*p-t-1) ∧
      ((2*p-t)*(2*p-t-1) = 0 ↔ (p=0 ∧ t=0) ∨ (p=1 ∧ t=1)) := by
  have hn : 0 ≤ 2*p-t := by omega
  constructor
  · by_cases hz : 2*p-t = 0
    · simp [hz]
    · exact mul_nonneg hn (by omega)
  · rw [mul_eq_zero]
    constructor
    · intro h
      rcases h with h | h
      · left; omega
      · right; omega
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> norm_num
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open scoped BigOperators
noncomputable def faceBaseline (D c : ℝ) (s : Fin 3 → ℝ) : ℝ :=
  ((D+1)*c + ∑ i, triangular (s i))/2 - (∑ i, triangular (c+s i))/6
 theorem triangular_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ triangular x := by
  unfold triangular; positivity
 theorem triangular_pos {x : ℝ} (hx : 0 < x) : 0 < triangular x := by
  unfold triangular; positivity
 theorem triangular_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    triangular x ≤ triangular y := by
  have h := mul_nonneg (sub_nonneg.mpr hxy) (show 0 ≤ y+x+1 by linarith)
  dsimp [triangular]; nlinarith only [h]
 theorem triangular_nat (n : ℕ) : ((n+1).choose 2 : ℝ) = triangular n := by
  rw [Nat.cast_choose_two]
  simp only [Nat.cast_add,Nat.cast_one]
  unfold triangular
  ring
 theorem faceBaseline_lower (D c : ℝ) (s : Fin 3 → ℝ) (k : Fin 3)
    (hc : 0 ≤ c) (hs : ∀ i, 0 ≤ s i) (hD : (∑ i, s i) ≤ D-c) :
    triangular (c+s k)/3 + triangular c/6 +
      ((∑ i, triangular (s i))-triangular (s k))/3 ≤ faceBaseline D c s := by
  have hm : s k ≤ ∑ i, s i := Finset.single_le_sum (fun i _ => hs i) (Finset.mem_univ k)
  have hn := mul_nonneg hc (show 0 ≤ 3*(D-c)-(∑ i, s i)-2*s k by linarith)
  have he : faceBaseline D c s - (triangular (c+s k)/3 + triangular c/6 +
      ((∑ i, triangular (s i))-triangular (s k))/3) =
      c*(3*(D-c)-(∑ i, s i)-2*s k)/6 := by
    simp only [faceBaseline,triangular,Fin.sum_univ_three]
    ring
  linarith only [hn,he]
 theorem half_triangular_bounds (h : ℕ) :
    0 ≤ triangular (h:ℝ)/3-triangular (h/2:ℕ) ∧
    (h:ℝ)^2/24-(h:ℝ)/12 ≤ triangular (h:ℝ)/3-triangular (h/2:ℕ) ∧
    (triangular (h:ℝ)/3-triangular (h/2:ℕ) = 0 ↔ h=0 ∨ h=2) := by
  have hd := Nat.mod_add_div h 2
  have hr := Nat.mod_lt h (by norm_num : 0<2)
  have hq : 0 ≤ (h/2:ℕ) := Nat.zero_le _
  have hqr : (0:ℝ) ≤ (h/2:ℕ) := Nat.cast_nonneg _
  rcases (show h%2=0 ∨ h%2=1 by omega) with he | he
  · have hh : h=2*(h/2) := by omega
    have hh' : (h:ℝ)=2*(h/2:ℕ) := by exact_mod_cast hh
    have hn : (h/2:ℕ)=0 ∨ (h/2:ℕ)=1 ∨ 2 ≤ h/2 := by omega
    rcases hn with hn | hn | hn
    · have hz : h=0 := by omega
      subst h; norm_num [triangular]
    · have hz : h=2 := by omega
      subst h; norm_num [triangular]
    · have hn' : (2:ℝ) ≤ (h/2:ℕ) := by exact_mod_cast hn
      have hp : 0 < (h/2:ℕ)*( (h/2:ℕ)-1 : ℝ) := mul_pos (by linarith) (by linarith)
      dsimp [triangular]
      constructor
      · nlinarith only [hh',hp]
      constructor
      · nlinarith only [hh',sq_nonneg ((h/2:ℕ):ℝ)]
      constructor
      · intro hz; nlinarith only [hh',hp,hz]
      · intro hz; rcases hz with hz | hz <;> omega
  · have hh : h=2*(h/2)+1 := by omega
    have hh' : (h:ℝ)=2*(h/2:ℕ)+1 := by exact_mod_cast hh
    have hp : 0 < ((h/2:ℕ):ℝ)+1 := by positivity
    have hp' := mul_pos hp (show (0:ℝ) < (h/2:ℕ)+2 by positivity)
    dsimp [triangular]
    constructor
    · nlinarith only [hh',hp',sq_nonneg ((h/2:ℕ):ℝ)]
    constructor
    · nlinarith only [hh',sq_nonneg ((h/2:ℕ):ℝ),hqr]
    constructor
    · intro hz; nlinarith only [hh',hp',hz]
    · intro hz; rcases hz with hz | hz <;> omega
 theorem lower_active_slack (D c : ℕ) (s : Fin 3 → ℕ) (k : Fin 3) (g : ℝ)
    (hD : (∑ i, s i) ≤ D-c) (hcD : c ≤ D)
    (_hk : ∀ i, s i ≤ s k) (hg : g ≤ triangular ((c+s k)/2:ℕ)) :
    0 ≤ faceBaseline D c (fun i => s i)-g ∧
    ((c+s k:ℕ):ℝ)^2/24-((c+s k:ℕ):ℝ)/12 ≤ faceBaseline D c (fun i => s i)-g ∧
    (faceBaseline D c (fun i => s i)-g = 0 →
      c=0 ∧ (∀ i, i≠k → s i=0) ∧ (s k=0 ∨ s k=2)) := by
  have hD' : (∑ i, (s i:ℝ)) ≤ (D:ℝ)-c := by exact_mod_cast hD
  have hb := faceBaseline_lower (D:ℝ) c (fun i => s i) k (by positivity) (fun i => by positivity) hD'
  have hh := half_triangular_bounds (c+s k)
  have he : 0 ≤ (∑ i, triangular (s i))-triangular (s k) := by
    exact sub_nonneg.mpr (Finset.single_le_sum (fun i _ => triangular_nonneg (Nat.cast_nonneg _)) (Finset.mem_univ k))
  have hct : 0 ≤ triangular (c:ℝ) := triangular_nonneg (Nat.cast_nonneg _)
  simp only [Nat.cast_add] at hh
  refine ⟨by linarith [hh.1],by simp only [Nat.cast_add]; linarith [hh.2.1],?_⟩
  intro hz
  have hc : c=0 := by
    by_contra hc
    have hp := triangular_pos (show (0:ℝ)<c by exact_mod_cast Nat.pos_of_ne_zero hc)
    linarith [hh.1]
  subst c
  simp only [Nat.cast_zero,zero_add] at hb hh hg hz
  have hothers : (∑ i, triangular (s i))-triangular (s k) = 0 := by
    have hz0 : triangular (0:ℝ)=0 := by norm_num [triangular]
    rw [hz0] at hb
    linarith [hh.1]
  refine ⟨rfl,?_,?_⟩
  · intro i hik
    have hle : triangular (s i)+triangular (s k) ≤ ∑ j, triangular (s j) := by
      have hsub : ({i,k}:Finset (Fin 3)) ⊆ Finset.univ := Finset.subset_univ _
      have hx := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => triangular_nonneg (Nat.cast_nonneg (s j)))
      simpa only [Finset.sum_pair hik] using hx
    have hi0 : triangular (s i)=0 := by linarith [triangular_nonneg (Nat.cast_nonneg (s i))]
    by_contra hi
    have hp := triangular_pos (show (0:ℝ)<s i by exact_mod_cast Nat.pos_of_ne_zero hi)
    linarith
  · apply (half_triangular_bounds (s k)).2.2.mp
    have hz0 : triangular (0:ℝ)=0 := by norm_num [triangular]
    rw [hz0] at hb
    linarith [(half_triangular_bounds (s k)).1]
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
def TailTuple.maxH (a : TailTuple) : ℕ := Finset.univ.sup a.h
noncomputable def TailTuple.delta (a : TailTuple) : ℝ := 2*a.u-a.c
noncomputable def TailTuple.P (a : TailTuple) : ℝ := ∑ i, (a.p i:ℝ)
noncomputable def TailTuple.T (a : TailTuple) : ℝ := ∑ i, (a.t i:ℝ)
noncomputable def TailTuple.Q (D : ℕ) (a : TailTuple) : ℝ :=
  quadraticPart a.c ((D:ℝ)-a.c) a.delta a.v (fun i => a.p i) (fun i => a.t i)
noncomputable def TailTuple.energy (D : ℕ) (a : TailTuple) : ℝ :=
  (a.P^2+a.T^2+a.delta^2)/342 + ((a.c:ℝ)-|a.delta|)*((D:ℝ)-a.c+3*a.delta)/12
noncomputable def tailGain (D : ℕ) (full : Bool) (a : TailTuple) : ℝ :=
  if full then plantedGain a.c ((D:ℝ)-a.c) a.delta a.v (fun i => a.p i) (fun i => a.t i)
  else triangular (a.maxH/2:ℕ)
noncomputable def tailSlack (D : ℕ) (full : Bool) (a : TailTuple) : ℝ :=
  faceBaseline D a.c (fun i => a.s i)-tailGain D full a
noncomputable def tailEnergy (D : ℕ) (full : Bool) (a : TailTuple) : ℝ :=
  if full then a.energy D else (a.maxH:ℝ)^2/24
def T2x47 (D : ℕ) (full : Bool) (a : TailTuple) : Prop :=
  a.c ≤ D ∧ (∑ i, a.s i) ≤ D-a.c ∧ (full=true →
    a.u ≤ a.c ∧
    (∀ i, (a.t i:ℝ) ≤ a.p i+a.delta) ∧
    (∀ i, (a.v:ℝ) ≤ a.p i+a.delta) ∧
    0 ≤ (((D:ℝ)-a.c-3*a.delta)/2)-a.P+a.v)
 theorem TailTuple.h_le_max (a : TailTuple) (i : Fin 3) : a.h i ≤ a.maxH :=
  Finset.le_sup (Finset.mem_univ i)
 theorem TailTuple.exists_max (a : TailTuple) : ∃ i, a.maxH=a.h i := by
  obtain ⟨i,_,hi⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty a.h
  exact ⟨i,hi⟩
 theorem TailTuple.c_le_max (a : TailTuple) : a.c ≤ a.maxH :=
  (Nat.le_add_right a.c (a.s 0)).trans (a.h_le_max 0)
 theorem TailTuple.p_le_h (a : TailTuple) (i : Fin 3) : a.p i ≤ a.h i := by
  unfold TailTuple.h TailTuple.s; omega
 theorem TailTuple.t_le_h (a : TailTuple) (i : Fin 3) : a.t i ≤ a.h i := by
  unfold TailTuple.h TailTuple.s; omega
 theorem TailTuple.delta_abs_le (a : TailTuple) (hu : a.u ≤ a.c) : |a.delta| ≤ (a.c:ℝ) := by
  have hu' : (a.u:ℝ) ≤ a.c := by exact_mod_cast hu
  rw [abs_le]
  dsimp [TailTuple.delta]
  constructor <;> linarith [(Nat.cast_nonneg a.u : (0:ℝ) ≤ a.u)]
 theorem TailTuple.baseline (D : ℕ) (a : TailTuple) :
    faceBaseline D a.c (fun i => a.s i) =
      baseline a.c ((D:ℝ)-a.c) (fun i => a.p i) (fun i => a.t i) := by
  simp only [faceBaseline,SidorenkoCounterexample.baseline,TailTuple.s,Nat.cast_add,sub_add_cancel,add_assoc]
 theorem T2x47.sum_le {D : ℕ} {full : Bool} {a : TailTuple}
    (ha : T2x47 D full a) : a.P+a.T ≤ (D:ℝ)-a.c := by
  have hh : (∑ i, (a.s i:ℝ)) ≤ (D:ℝ)-a.c := by
    have hc : ((D-a.c:ℕ):ℝ) = (D:ℝ)-a.c := Nat.cast_sub ha.1
    rw [←hc,←Nat.cast_sum]
    exact_mod_cast ha.2.1
  simpa only [TailTuple.s,Nat.cast_add,Finset.sum_add_distrib,TailTuple.P,TailTuple.T] using hh
 theorem T2x47.d_delta_nonneg {D : ℕ} {a : TailTuple}
    (ha : T2x47 D true a) : 0 ≤ (D:ℝ)-a.c+3*a.delta := by
  have ht := Finset.sum_le_sum (s := Finset.univ) (fun i _ => (ha.2.2 rfl).2.1 i)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul] at ht
  change a.T ≤ a.P+3*a.delta at ht
  have hT : 0 ≤ a.T := Finset.sum_nonneg (fun i _ => Nat.cast_nonneg _)
  linarith [ha.sum_le]
 theorem T2x47.energy_nonneg {D : ℕ} {a : TailTuple}
    (ha : T2x47 D true a) :
    0 ≤ a.energy D ∧ (a.P^2+a.T^2+a.delta^2)/342 ≤ a.energy D := by
  have h := mul_nonneg (sub_nonneg.mpr (a.delta_abs_le (ha.2.2 rfl).1)) ha.d_delta_nonneg
  dsimp [TailTuple.energy]
  constructor
  · positivity
  · linarith only [h]
 theorem T2x47.coercivity {D : ℕ} {a : TailTuple}
    (ha : T2x47 D true a) : a.energy D ≤ a.Q D := by
  apply SidorenkoCounterexample.coercivity
  · exact a.delta_abs_le (ha.2.2 rfl).1
  · exact ha.sum_le
  · intro i; positivity
  · intro i; positivity
  · positivity
  · exact (ha.2.2 rfl).2.1
  · exact (ha.2.2 rfl).2.2.1
  · exact (ha.2.2 rfl).2.2.2
 theorem T2x47.v_le_max {D : ℕ} {a : TailTuple}
    (ha : T2x47 D true a) : a.v ≤ a.maxH := by
  have hv := (ha.2.2 rfl).2.2.1 0
  have hδ := le_abs_self a.delta |>.trans (a.delta_abs_le (ha.2.2 rfl).1)
  have hp : (a.p 0:ℝ) ≤ a.h 0-a.c := by
    dsimp [TailTuple.h,TailTuple.s]; push_cast; linarith [(Nat.cast_nonneg (a.t 0) : (0:ℝ) ≤ a.t 0)]
  have hh : (a.h 0:ℝ) ≤ a.maxH := by exact_mod_cast a.h_le_max 0
  have hv' : (a.v:ℝ) ≤ a.maxH := by linarith
  exact_mod_cast hv'
 theorem tailEnergy_nonneg {D : ℕ} {full : Bool} {a : TailTuple}
    (ha : T2x47 D full a) : 0 ≤ tailEnergy D full a := by
  cases full
  · simp only [tailEnergy,Bool.false_eq_true,ite_false]; positivity
  · exact ha.energy_nonneg.1
 theorem tailSlack_energy_lower {D : ℕ} {full : Bool} {a : TailTuple} (M : ℝ)
    (ha : T2x47 D full a) (hM : (a.maxH:ℝ) ≤ M) :
    tailEnergy D full a-3*M/2 ≤ tailSlack D full a := by
  cases full
  · obtain ⟨k,hk⟩ := a.exists_max
    have hsk (i : Fin 3) : a.s i ≤ a.s k := by
      have hh := a.h_le_max i
      rw [hk] at hh
      exact Nat.le_of_add_le_add_left hh
    have hh := lower_active_slack D a.c a.s k (triangular (a.maxH/2:ℕ)) ha.2.1 ha.1 hsk
      (by rw [hk]; rfl)
    simp only [tailSlack,tailGain,tailEnergy,Bool.false_eq_true,ite_false]
    rw [hk] at hh ⊢
    have hhM : (a.c+a.s k:ℕ) ≤ M := by simpa only [hk,TailTuple.h] using hM
    have hMn : 0 ≤ M := (Nat.cast_nonneg a.maxH).trans hM
    change ((a.c+a.s k:ℕ):ℝ)^2/24-3*M/2 ≤ _
    linarith [hh.2.1]
  · have hc : (a.c:ℝ) ≤ M := le_trans (by exact_mod_cast a.c_le_max) hM
    have hv : (a.v:ℝ) ≤ M := le_trans (by exact_mod_cast ha.v_le_max) hM
    have hP : a.P ≤ 3*(M-a.c) := by
      have hi (i : Fin 3) : (a.p i:ℝ) ≤ M-a.c := by
        have hh : (a.h i:ℝ) ≤ M := le_trans (by exact_mod_cast a.h_le_max i) hM
        dsimp [TailTuple.h,TailTuple.s] at hh
        push_cast at hh
        linarith [(Nat.cast_nonneg (a.t i) : (0:ℝ) ≤ a.t i)]
      have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hi i)
      simpa only [TailTuple.P,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat] using hh
    have hδ : a.delta ≤ (a.c:ℝ) := (le_abs_self _).trans (a.delta_abs_le (ha.2.2 rfl).1)
    have hh := slack_uniform_linear (a.c:ℝ) ((D:ℝ)-a.c) a.delta (a.v:ℝ) M
      (fun i => (a.p i:ℝ)) (fun i => (a.t i:ℝ)) (by positivity) hδ hv hP
      (Finset.sum_nonneg (fun i _ => Nat.cast_nonneg _))
    have hh' := sub_le_sub_right ha.coercivity (3*M/2)
    simpa only [tailSlack,tailGain,tailEnergy,ite_true,a.baseline D,TailTuple.Q] using hh'.trans hh
end SidorenkoCounterexample
namespace SidorenkoCounterexample
def T2x12 : Fin 33 → Finset (Fin 13) := ![{0,2}, {0,3}, {2,3}, {0,9}, {2,9}, {0,1}, {1,3}, {2,4}, {3,4}, {1,9}, {4,9}, {1,10}, {3,10}, {3,11}, {4,11}, {1,12}, {9,12}, {4,8}, {8,9}, {1,7}, {7,10}, {10,11}, {8,11}, {7,12}, {8,12}, {5,7}, {5,10}, {5,11}, {6,8}, {6,11}, {6,7}, {6,12}, {5,6}]
def facePair : Fin 22 → Fin 3 → Fin 33 := ![![5, 1, 6], ![5, 3, 9], ![0, 1, 2], ![0, 3, 4], ![6, 11, 12], ![19, 11, 20], ![19, 15, 23], ![9, 15, 16], ![2, 7, 8], ![7, 4, 10], ![8, 13, 14], ![12, 13, 21], ![17, 10, 18], ![17, 14, 22], ![32, 25, 30], ![32, 27, 29], ![25, 26, 20], ![26, 27, 21], ![30, 31, 23], ![28, 29, 22], ![28, 31, 24], ![18, 24, 16]]
def pairFace : Fin 33 → Fin 2 → Fin 22 := ![![2, 3], ![0, 2], ![2, 8], ![1, 3], ![3, 9], ![0, 1], ![0, 4], ![8, 9], ![8, 10], ![1, 7], ![9, 12], ![4, 5], ![4, 11], ![10, 11], ![10, 13], ![6, 7], ![7, 21], ![12, 13], ![12, 21], ![5, 6], ![5, 16], ![11, 17], ![13, 19], ![6, 18], ![20, 21], ![14, 16], ![16, 17], ![15, 17], ![19, 20], ![15, 19], ![14, 18], ![18, 20], ![14, 15]]
def pairParent : Fin 33 → Fin 33 := ![0, 0, 0, 0, 0, 1, 1, 2, 2, 3, 4, 6, 6, 8, 8, 9, 9, 10, 10, 11, 11, 12, 14, 15, 16, 20, 20, 21, 22, 22, 23, 23, 25]
def pairBridge : Fin 33 → Fin 22 := ![2, 2, 2, 3, 3, 0, 0, 8, 8, 1, 9, 4, 4, 10, 10, 7, 7, 12, 12, 5, 5, 11, 13, 6, 21, 16, 16, 17, 19, 19, 18, 18, 14]
def faceBit : Fin 22 → Fin 3 → Bool := ![![false, false, false], ![false, true, false], ![false, false, true], ![true, true, false], ![false, false, true], ![false, false, false], ![true, false, false], ![true, true, false], ![true, false, true], ![true, false, false], ![true, true, true], ![true, false, true], ![true, false, true], ![false, true, true], ![false, false, false], ![true, true, false], ![false, true, false], ![true, true, true], ![false, false, true], ![false, true, false], ![false, true, true], ![true, true, true]]
def separationCount (e : Fin 33) : ℕ := (Finset.univ.filter fun b => faceBit (pairFace e 0) b ≠ faceBit (pairFace e 1) b).card
 theorem faces_card : ∀ j, (faces j).card = 3 := by decide
 theorem pairVertices_card : ∀ e, (T2x12 e).card = 2 := by decide
 theorem pairVertices_injective : Function.Injective T2x12 := by decide
 theorem facePair_injective : ∀ j, Function.Injective (facePair j) := by decide
 theorem facePair_correct : ∀ j e, T2x12 e ⊆ faces j ↔ ∃ k, facePair j k=e := by decide
 theorem pairParent_lt : ∀ e, e≠0 → (pairParent e).val < e.val := by decide
 theorem pairBridge_self : ∀ e, T2x12 e ⊆ faces (pairBridge e) := by decide
 theorem pairBridge_parent : ∀ e, T2x12 (pairParent e) ⊆ faces (pairBridge e) := by decide
 theorem separationCount_pos : ∀ e, 1 ≤ separationCount e := by decide
 theorem separationCount_root : separationCount 0=3 := by decide
 theorem separationCount_le : ∀ e, separationCount e ≤ 3 := by decide
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open scoped BigOperators
 theorem nonnegative_interval_sq (a b M : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (haM : a ≤ M) (hbM : b ≤ M) : (a-b)^2 ≤ M^2 := by
  have hM : 0 ≤ M := ha.trans haM
  have hab : |a-b| ≤ M := abs_le.mpr ⟨by linarith,by linarith⟩
  have hh := (sq_le_sq₀ (abs_nonneg _) hM).2 hab
  simpa only [sq_abs] using hh
 theorem tail_pair_energy {D : ℕ} {full : Bool} {a : TailTuple}
    (ha : T2x47 D full a) (i k : Fin 3) :
    ((a.h i:ℝ)-a.h k)^2 ≤ 684*tailEnergy D full a := by
  cases full
  · have hm (j : Fin 3) : (a.h j:ℝ) ≤ a.maxH := by exact_mod_cast a.h_le_max j
    have hh := nonnegative_interval_sq (a.h i) (a.h k) a.maxH (by positivity) (by positivity) (hm i) (hm k)
    simp only [tailEnergy,Bool.false_eq_true,ite_false]
    nlinarith [sq_nonneg (a.maxH:ℝ)]
  · have hs (j : Fin 3) : (a.s j:ℝ) ≤ a.P+a.T := by
      have hh : (a.s j:ℝ) ≤ ∑ k, (a.s k:ℝ) :=
        Finset.single_le_sum (fun k _ => Nat.cast_nonneg (a.s k)) (Finset.mem_univ j)
      simpa only [TailTuple.s,Nat.cast_add,Finset.sum_add_distrib,TailTuple.P,TailTuple.T] using hh
    have hh := nonnegative_interval_sq (a.s i) (a.s k) (a.P+a.T) (by positivity) (by positivity) (hs i) (hs k)
    have he := ha.energy_nonneg.2
    simp only [tailEnergy,ite_true]
    simp only [TailTuple.h,Nat.cast_add]
    nlinarith only [hh,he,sq_nonneg (a.P-a.T),sq_nonneg a.delta]
 theorem parent_energy_bound {n : ℕ} (p : Fin (n+1) → Fin (n+1))
    (hp : ∀ i, i≠0 → (p i).val < i.val) (f : Fin (n+1) → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hstep : ∀ i, (f i-f (p i))^2 ≤ K) (i : Fin (n+1)) :
    (f i-f 0)^2 ≤ (4:ℝ)^i.val*K := by
  have hmain : ∀ m, ∀ i : Fin (n+1), i.val=m → (f i-f 0)^2 ≤ (4:ℝ)^i.val*K := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro i him
      by_cases hi : i=0
      · subst i; simpa using hK
      · have hpm : (p i).val < m := by simpa only [him] using hp i hi
        have hind := ih (p i).val hpm (p i) rfl
        have hpow : (4:ℝ)^((p i).val+1) ≤ (4:ℝ)^i.val :=
          pow_le_pow_right₀ (by norm_num) (hp i hi)
        have hone : (1:ℝ) ≤ (4:ℝ)^(p i).val := one_le_pow₀ (by norm_num)
        have hc := mul_le_mul_of_nonneg_right hpow hK
        have hk' := mul_le_mul_of_nonneg_right hone hK
        rw [pow_succ] at hc
        have hh := hstep i
        nlinarith only [hind,hc,hk',hh,sq_nonneg ((f i-f (p i))-(f (p i)-f 0))]
  exact hmain i.val i rfl
noncomputable def T2x32 (h : Fin 33 → ℕ) : ℝ :=
  ∑ e, ((separationCount e:ℝ)-1)/6*triangular (h e)
def GlobalTailFeasible (D : ℕ) (full : Fin 22 → Bool) (a : Fin 22 → TailTuple)
    (h : Fin 33 → ℕ) : Prop :=
  (∀ j, T2x47 D (full j) (a j)) ∧ ∀ j k, (a j).h k=h (facePair j k)
 theorem separationExcess_nonneg (h : Fin 33 → ℕ) : 0 ≤ T2x32 h := by
  apply Finset.sum_nonneg
  intro e _
  have he : (1:ℝ) ≤ separationCount e := by exact_mod_cast separationCount_pos e
  exact mul_nonneg (by linarith) (triangular_nonneg (Nat.cast_nonneg _))
 theorem separationExcess_root (h : Fin 33 → ℕ) :
    (h 0:ℝ)^2/6 ≤ T2x32 h := by
  have hn (e : Fin 33) : 0 ≤ ((separationCount e:ℝ)-1)/6*triangular (h e) := by
    have hh : (1:ℝ) ≤ separationCount e := by exact_mod_cast separationCount_pos e
    exact mul_nonneg (by linarith) (triangular_nonneg (Nat.cast_nonneg _))
  have he : ((separationCount 0:ℝ)-1)/6*triangular (h 0) ≤ T2x32 h :=
    Finset.single_le_sum (fun e _ => hn e) (Finset.mem_univ (0 : Fin 33))
  rw [separationCount_root] at he
  norm_num only [Nat.cast_ofNat] at he
  dsimp [triangular] at he
  nlinarith [(Nat.cast_nonneg (h 0) : (0:ℝ) ≤ h 0)]
 theorem global_tail_budget (D : ℕ) (full : Fin 22 → Bool) (a : Fin 22 → TailTuple)
    (h : Fin 33 → ℕ) (ha : GlobalTailFeasible D full a h)
    (htotal : (∑ j, tailSlack D (full j) (a j))+T2x32 h ≤ 0) :
    (∑ j, tailEnergy D (full j) (a j))+T2x32 h ≤
      33*((Finset.univ.sup h:ℕ):ℝ) := by
  let M : ℝ := (Finset.univ.sup h:ℕ)
  have hM (j : Fin 22) : ((a j).maxH:ℝ) ≤ M := by
    have hh : (a j).maxH ≤ Finset.univ.sup h := by
      apply Finset.sup_le
      intro k _
      rw [ha.2 j k]
      exact Finset.le_sup (Finset.mem_univ _)
    change ((a j).maxH:ℝ) ≤ ((Finset.univ.sup h:ℕ):ℝ)
    exact_mod_cast hh
  have hi := Finset.sum_le_sum (s := Finset.univ) (fun j _ => tailSlack_energy_lower M (ha.1 j) (hM j))
  simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hi
  change (∑ j, tailEnergy D (full j) (a j))-22*(3*M/2) ≤ _ at hi
  change (∑ j, tailEnergy D (full j) (a j))+T2x32 h ≤ 33*M
  linarith only [hi,htotal]
def tailPairBound : ℕ := 2*4^32*22572+396
 theorem global_tail_pair_bound (D : ℕ) (full : Fin 22 → Bool) (a : Fin 22 → TailTuple)
    (h : Fin 33 → ℕ) (ha : GlobalTailFeasible D full a h)
    (htotal : (∑ j, tailSlack D (full j) (a j))+T2x32 h ≤ 0) :
    ∀ e, h e ≤ tailPairBound := by
  let M : ℝ := (Finset.univ.sup h:ℕ)
  have hM : 0 ≤ M := Nat.cast_nonneg _
  have hb := global_tail_budget D full a h ha htotal
  change (∑ j, tailEnergy D (full j) (a j))+T2x32 h ≤ 33*M at hb
  have he0 : 0 ≤ T2x32 h := separationExcess_nonneg h
  have hen (j : Fin 22) : 0 ≤ tailEnergy D (full j) (a j) := tailEnergy_nonneg (ha.1 j)
  have hes : 0 ≤ ∑ j, tailEnergy D (full j) (a j) := Finset.sum_nonneg (fun j _ => hen j)
  have he (j : Fin 22) : tailEnergy D (full j) (a j) ≤ 33*M := by
    have hh := Finset.single_le_sum (fun j _ => hen j) (Finset.mem_univ j)
    linarith
  have hroot : (h 0:ℝ)^2 ≤ 198*M := by linarith [separationExcess_root h]
  have hstep (e : Fin 33) : ((h e:ℝ)-h (pairParent e))^2 ≤ 22572*M := by
    obtain ⟨i,hi⟩ := (facePair_correct (pairBridge e) e).mp (pairBridge_self e)
    obtain ⟨k,hk⟩ := (facePair_correct (pairBridge e) (pairParent e)).mp (pairBridge_parent e)
    have hh := tail_pair_energy (ha.1 (pairBridge e)) i k
    rw [ha.2,ha.2,hi,hk] at hh
    linarith [he (pairBridge e)]
  obtain ⟨em,_,hem⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty h
  have hem' : (h em:ℝ)=M := by
    dsimp [M]; exact_mod_cast hem.symm
  have hg := parent_energy_bound pairParent pairParent_lt (fun e => (h e:ℝ)) (22572*M) (by positivity) hstep em
  have hp : (4:ℝ)^em.val ≤ (4:ℝ)^32 := pow_le_pow_right₀ (by norm_num) (by omega)
  have hgp := mul_le_mul_of_nonneg_right hp (show 0 ≤ 22572*M by positivity)
  have htotalM : M^2 ≤ (tailPairBound:ℝ)*M := by
    rw [hem'] at hg
    simp only [tailPairBound,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
    nlinarith only [hg,hgp,hroot,sq_nonneg (M-2*(h 0:ℝ))]
  have hMB : M ≤ (tailPairBound:ℝ) := by
    by_contra hnot
    have hdiff : 0 < M-(tailPairBound:ℝ) := by linarith
    have hMp : 0 < M := lt_of_le_of_lt (Nat.cast_nonneg _) (lt_of_not_ge hnot)
    have hp := mul_pos hMp hdiff
    nlinarith only [hp,htotalM]
  intro e
  have heM : (h e:ℝ) ≤ M := by
    dsimp [M]; exact_mod_cast (Finset.le_sup (f := h) (Finset.mem_univ e))
  exact_mod_cast heM.trans hMB
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open scoped BigOperators
structure TailBox (B : ℕ) where
  c : Fin (B+1)
  u : Fin (B+1)
  v : Fin (B+1)
  p : Fin 3 → Fin (B+1)
  t : Fin 3 → Fin (B+1)
  deriving Fintype
def TailBox.tuple {B : ℕ} (b : TailBox B) : TailTuple :=
  ⟨b.c,b.u,b.v,fun i => b.p i,fun i => b.t i⟩
noncomputable def tailRemainder (a : TailTuple) : ℝ :=
  baseline a.c 0 (fun i => a.p i) (fun i => a.t i)-
    plantedGain a.c 0 a.delta a.v (fun i => a.p i) (fun i => a.t i)
noncomputable def tailLinear (a : TailTuple) : ℝ := ((a.c:ℝ)-a.u+a.v)/2
noncomputable def tailRemainderBound (B : ℕ) : ℝ :=
  ∑ b : TailBox B, |tailRemainder b.tuple|
 theorem tailRemainderBound_nonneg (B : ℕ) : 0 ≤ tailRemainderBound B :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)
 theorem tailSlack_linear (D : ℕ) (a : TailTuple) :
    tailSlack D true a=tailLinear a*((D:ℝ)-a.c)+tailRemainder a := by
  simp only [tailSlack,tailGain,ite_true,a.baseline D]
  rw [slack_leading_coefficient]
  dsimp [tailLinear,tailRemainder,TailTuple.delta]
  ring
 theorem tailLinear_nonneg {a : TailTuple} (hu : a.u ≤ a.c) : 0 ≤ tailLinear a := by
  have hu' : (a.u:ℝ) ≤ a.c := by exact_mod_cast hu
  dsimp [tailLinear]
  linarith [show (0:ℝ) ≤ a.v by positivity]
 theorem tailLinear_half {a : TailTuple} (hu : a.u ≤ a.c)
    (hbad : ¬(a.u=a.c ∧ a.v=0)) : 1/2 ≤ tailLinear a := by
  have hh : a.u+1 ≤ a.c+a.v := by omega
  have hh' : (a.u:ℝ)+1 ≤ a.c+a.v := by exact_mod_cast hh
  dsimp [tailLinear]; linarith
 theorem tailRemainder_bounded {D B : ℕ} {a : TailTuple}
    (ha : T2x47 D true a) (hB : a.maxH ≤ B) :
    |tailRemainder a| ≤ tailRemainderBound B := by
  have hc : a.c ≤ B := a.c_le_max.trans hB
  have hu : a.u ≤ B := (ha.2.2 rfl).1.trans hc
  have hv : a.v ≤ B := ha.v_le_max.trans hB
  have hp (i : Fin 3) : a.p i ≤ B := (a.p_le_h i).trans ((a.h_le_max i).trans hB)
  have ht (i : Fin 3) : a.t i ≤ B := (a.t_le_h i).trans ((a.h_le_max i).trans hB)
  let b : TailBox B := ⟨⟨a.c,by omega⟩,⟨a.u,by omega⟩,⟨a.v,by omega⟩,
    fun i => ⟨a.p i,by have := hp i; omega⟩,fun i => ⟨a.t i,by have := ht i; omega⟩⟩
  have hb : b.tuple=a := by cases a; rfl
  rw [←hb]
  exact Finset.single_le_sum (f := fun x : TailBox B => |tailRemainder x.tuple|)
    (fun _ _ => abs_nonneg _) (Finset.mem_univ b)
 theorem tailSlack_lower_nonneg {D : ℕ} {a : TailTuple}
    (ha : T2x47 D false a) : 0 ≤ tailSlack D false a := by
  obtain ⟨k,hk⟩ := a.exists_max
  have hsk (i : Fin 3) : a.s i ≤ a.s k := by
    have hh := a.h_le_max i
    rw [hk] at hh
    exact Nat.le_of_add_le_add_left hh
  exact (lower_active_slack D a.c a.s k (triangular (a.maxH/2:ℕ)) ha.2.1 ha.1 hsk
    (by rw [hk]; rfl)).1
 theorem global_maxH_bound {D : ℕ} {full : Fin 22 → Bool} {a : Fin 22 → TailTuple}
    {h : Fin 33 → ℕ} (ha : GlobalTailFeasible D full a h)
    (htotal : (∑ j, tailSlack D (full j) (a j))+T2x32 h ≤ 0) (j : Fin 22) :
    (a j).maxH ≤ tailPairBound := by
  have hb := global_tail_pair_bound D full a h ha htotal
  apply Finset.sup_le
  intro k _
  rw [ha.2]
  exact hb _
 theorem eventually_integer_regime : ∃ D₀ : ℕ, ∀ D ≥ D₀,
    ∀ (full : Fin 22 → Bool) (a : Fin 22 → TailTuple) (h : Fin 33 → ℕ),
    GlobalTailFeasible D full a h →
    (∑ j, tailSlack D (full j) (a j))+T2x32 h ≤ 0 →
    ∀ j, full j=true → (a j).u=(a j).c ∧ (a j).v=0 := by
  let B := tailPairBound
  let R := tailRemainderBound B
  have hR : 0 ≤ R := tailRemainderBound_nonneg B
  obtain ⟨D₀,hD₀⟩ := exists_nat_gt ((B:ℝ)+44*R)
  refine ⟨D₀,?_⟩
  intro D hD full a h ha htotal
  have hD' : (B:ℝ)+44*R < D := lt_of_lt_of_le hD₀ (by exact_mod_cast hD)
  have hB (j : Fin 22) : (a j).maxH ≤ B := global_maxH_bound ha htotal j
  have hc (j : Fin 22) : ((a j).c:ℝ) ≤ B := by
    exact_mod_cast (a j).c_le_max.trans (hB j)
  have hrem (j : Fin 22) (hj : full j=true) : -R ≤ tailRemainder (a j) := by
    have hh := tailRemainder_bounded (D := D) (by simpa only [hj] using ha.1 j) (hB j)
    exact (abs_le.mp hh).1
  have hs (j : Fin 22) : -R ≤ tailSlack D (full j) (a j) := by
    cases hj : full j with
    | false =>
      have hh := tailSlack_lower_nonneg (by simpa only [hj] using ha.1 j)
      linarith only [hR,hh]
    | true =>
      have haj : T2x47 D true (a j) := by simpa only [hj] using ha.1 j
      rw [tailSlack_linear]
      have hdn : 0 ≤ (D:ℝ)-(a j).c := sub_nonneg.mpr (by exact_mod_cast haj.1)
      have hh := mul_nonneg (tailLinear_nonneg (haj.2.2 rfl).1) hdn
      linarith only [hh,hrem j hj]
  intro j hj
  by_contra hbad
  have haj : T2x47 D true (a j) := by simpa only [hj] using ha.1 j
  have hA := tailLinear_half (haj.2.2 rfl).1 hbad
  have hdn : 0 ≤ (D:ℝ)-(a j).c := by
    have hcD : ((a j).c:ℝ) ≤ D := by exact_mod_cast haj.1
    linarith
  have hmul := mul_le_mul_of_nonneg_right hA hdn
  have hsl : (D:ℝ)/2-(B:ℝ)/2-R ≤ tailSlack D (full j) (a j) := by
    rw [hj,tailSlack_linear]
    linarith only [hmul,hrem j hj,hc j]
  have hsum : tailSlack D (full j) (a j)+R ≤ ∑ k, (tailSlack D (full k) (a k)+R) :=
    Finset.single_le_sum (f := fun k : Fin 22 => tailSlack D (full k) (a k)+R)
      (fun k _ => by linarith only [hs k]) (Finset.mem_univ j)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat] at hsum
  linarith only [hsum,hsl,htotal,separationExcess_nonneg h,hD']
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open scoped BigOperators
 theorem delta_integer_regime (a : TailTuple) (hu : a.u=a.c) : a.delta=(a.c:ℝ) := by
  dsimp [TailTuple.delta]; rw [hu]; ring
 theorem tailSlack_integer (D : ℕ) (a : TailTuple) (hu : a.u=a.c) (hv : a.v=0) :
    tailSlack D true a = baseline a.c ((D:ℝ)-a.c) (fun i => a.p i) (fun i => a.t i)-
      plantedGain a.c ((D:ℝ)-a.c) a.c 0 (fun i => a.p i) (fun i => a.t i) := by
  simp only [tailSlack,tailGain,ite_true,a.baseline D,delta_integer_regime a hu,hv,Nat.cast_zero]
 theorem integer_slack_classification {D : ℕ} {a : TailTuple}
    (ha : T2x47 D true a) (hu : a.u=a.c) (hv : a.v=0) :
    0 ≤ tailSlack D true a ∧ (tailSlack D true a=0 →
      (a.c=0 ∧ ∀ i, (a.p i=0 ∧ a.t i=0) ∨ (a.p i=1 ∧ a.t i=1)) ∨
      (a.c=1 ∧ ∀ i, a.p i=0 ∧ a.t i=0)) := by
  rw [tailSlack_integer D a hu hv]
  by_cases hc0 : a.c=0
  · have he : baseline a.c ((D:ℝ)-a.c) (fun i => a.p i) (fun i => a.t i)-
        plantedGain a.c ((D:ℝ)-a.c) a.c 0 (fun i => a.p i) (fun i => a.t i) =
        (∑ i : Fin 3, (2*(a.p i:ℝ)-a.t i)*(2*(a.p i:ℝ)-a.t i-1))/6 := by
      rw [slack_integer_regime,hc0]
      simp only [Nat.cast_zero,Fin.sum_univ_three]; ring
    rw [he]
    have hi (i : Fin 3) : 0 ≤ (2*(a.p i:ℝ)-a.t i)*(2*(a.p i:ℝ)-a.t i-1) ∧
        ((2*(a.p i:ℝ)-a.t i)*(2*(a.p i:ℝ)-a.t i-1)=0 →
          (a.p i=0 ∧ a.t i=0) ∨ (a.p i=1 ∧ a.t i=1)) := by
      have ht := (ha.2.2 rfl).2.1 i
      rw [delta_integer_regime a hu,hc0,Nat.cast_zero,add_zero] at ht
      have ht' : (a.t i:ℤ) ≤ a.p i := by exact_mod_cast ht
      have hh := integer_pair_slack (a.p i) (a.t i) (by positivity) (by positivity) ht'
      refine ⟨by exact_mod_cast hh.1,?_⟩
      intro hz
      have hz' : (2*(a.p i:ℤ)-a.t i)*(2*(a.p i:ℤ)-a.t i-1)=0 := by exact_mod_cast hz
      have hh' := hh.2.mp hz'
      exact_mod_cast hh'
    have hsum : 0 ≤ ∑ i : Fin 3, (2*(a.p i:ℝ)-a.t i)*(2*(a.p i:ℝ)-a.t i-1) :=
      Finset.sum_nonneg (fun i _ => (hi i).1)
    refine ⟨by positivity,fun hz => Or.inl ⟨hc0,?_⟩⟩
    intro i
    apply (hi i).2
    have hh := Finset.single_le_sum (f := fun k : Fin 3 =>
      (2*(a.p k:ℝ)-a.t k)*(2*(a.p k:ℝ)-a.t k-1))
      (fun k _ => (hi k).1) (Finset.mem_univ i)
    linarith only [hh,hz,(hi i).1]
  · by_cases hc1 : a.c=1
    · have he : baseline a.c ((D:ℝ)-a.c) (fun i => a.p i) (fun i => a.t i)-
          plantedGain a.c ((D:ℝ)-a.c) a.c 0 (fun i => a.p i) (fun i => a.t i) =
          (∑ i : Fin 3, ((2*(a.p i:ℝ)-a.t i)^2+3*a.p i))/6 := by
        rw [slack_integer_regime,hc1]
        simp only [Nat.cast_one,Fin.sum_univ_three]; ring
      rw [he]
      have hi (i : Fin 3) : 0 ≤ (2*(a.p i:ℝ)-a.t i)^2+3*a.p i := by positivity
      have hsum : 0 ≤ ∑ i : Fin 3, ((2*(a.p i:ℝ)-a.t i)^2+3*a.p i) :=
        Finset.sum_nonneg (fun i _ => hi i)
      refine ⟨by positivity,fun hz => Or.inr ⟨hc1,?_⟩⟩
      intro i
      have hh := Finset.single_le_sum (f := fun k : Fin 3 =>
        (2*(a.p k:ℝ)-a.t k)^2+3*a.p k) (fun k _ => hi k) (Finset.mem_univ i)
      have hp : a.p i=0 := by
        have hn : (0:ℝ) ≤ a.p i := Nat.cast_nonneg _
        have hz' : (a.p i:ℝ)=0 := by nlinarith only [hh,hz,hn,sq_nonneg (2*(a.p i:ℝ)-a.t i)]
        exact_mod_cast hz'
      refine ⟨hp,?_⟩
      simp only [hp,Nat.cast_zero,mul_zero,add_zero,zero_sub,neg_sq] at hh
      have ht' : (a.t i:ℝ)=0 := by nlinarith only [hh,hz,sq_nonneg (a.t i:ℝ)]
      exact_mod_cast ht'
    · have hc : (2:ℝ) ≤ a.c := by
        have hh : 2 ≤ a.c := by omega
        exact_mod_cast hh
      have hh := slack_pos_of_two_le a.c ((D:ℝ)-a.c) (fun i => a.p i) (fun i => a.t i)
        hc (fun i => by positivity)
      exact ⟨hh.le,fun hz => (ne_of_gt hh hz).elim⟩
def FaceResidue (a : TailTuple) : Prop :=
  (a.c=0 ∧ ∀ i, a.h i=0 ∨ a.h i=2) ∨ (a.c=1 ∧ ∀ i, a.h i=1)
 theorem full_zero_face_residue {D : ℕ} {a : TailTuple} (ha : T2x47 D true a)
    (hu : a.u=a.c) (hv : a.v=0) (hz : tailSlack D true a=0) : FaceResidue a := by
  rcases (integer_slack_classification ha hu hv).2 hz with ⟨hc,hh⟩ | ⟨hc,hh⟩
  · left; refine ⟨hc,fun i => ?_⟩
    rcases hh i with ⟨hp,ht⟩ | ⟨hp,ht⟩
    · left; simp only [TailTuple.h,TailTuple.s,hc,hp,ht]
    · right; simp only [TailTuple.h,TailTuple.s,hc,hp,ht]
  · right; refine ⟨hc,fun i => ?_⟩
    simp only [TailTuple.h,TailTuple.s,hc,(hh i).1,(hh i).2]
 theorem lower_zero_face_residue {D : ℕ} {a : TailTuple}
    (ha : T2x47 D false a) (hz : tailSlack D false a=0) : FaceResidue a := by
  obtain ⟨k,hk⟩ := a.exists_max
  have hsk (i : Fin 3) : a.s i ≤ a.s k := by
    have hh := a.h_le_max i
    rw [hk] at hh
    exact Nat.le_of_add_le_add_left hh
  have hh := (lower_active_slack D a.c a.s k (triangular (a.maxH/2:ℕ)) ha.2.1 ha.1 hsk
    (by rw [hk]; rfl)).2.2 hz
  left; refine ⟨hh.1,fun i => ?_⟩
  by_cases hik : i=k
  · subst i; simpa only [TailTuple.h,hh.1,zero_add] using hh.2.2
  · left; simp only [TailTuple.h,hh.1,hh.2.1 i hik,add_zero]
 theorem FaceResidue.one_iff {a : TailTuple} (ha : FaceResidue a) (i k : Fin 3) :
    a.h i=1 ↔ a.h k=1 := by
  rcases ha with ⟨_,hh⟩ | ⟨_,hh⟩
  · have hi := hh i; have hk := hh k
    constructor <;> intro h <;> omega
  · rw [hh i,hh k]
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open scoped BigOperators
 theorem pair_incidence_card : ∀ e : Fin 33,
    (Finset.univ.filter fun p : Fin 22 × Fin 3 => facePair p.1 p.2=e).card=2 := by decide
 theorem sum_face_pairs (f : Fin 33 → ℝ) :
    (∑ j : Fin 22, ∑ k : Fin 3, f (facePair j k))=2*∑ e, f e := by
  rw [←Fintype.sum_prod_type (fun p : Fin 22 × Fin 3 => f (facePair p.1 p.2))]
  rw [←Finset.sum_fiberwise Finset.univ (fun p : Fin 22 × Fin 3 => facePair p.1 p.2)]
  have he (e : Fin 33) : (∑ p ∈ Finset.univ.filter (fun p : Fin 22 × Fin 3 => facePair p.1 p.2=e),
      f (facePair p.1 p.2))=2*f e := by
    calc _ = ∑ _p ∈ Finset.univ.filter (fun p : Fin 22 × Fin 3 => facePair p.1 p.2=e), f e := by
            apply Finset.sum_congr rfl
            intro p hp
            rw [(Finset.mem_filter.mp hp).2]
         _ = _ := by rw [Finset.sum_const,pair_incidence_card]; simp only [nsmul_eq_mul,Nat.cast_ofNat]
  simp_rw [he]
  rw [Finset.mul_sum]
 theorem residue_root_zero (h : Fin 33 → ℕ) (he : T2x32 h=0) : h 0=0 := by
  have hh := separationExcess_root h
  rw [he] at hh
  have h0 : (h 0:ℝ)=0 := by nlinarith [sq_nonneg (h 0:ℝ)]
  exact_mod_cast h0
 theorem residue_propagation (a : Fin 22 → TailTuple) (h : Fin 33 → ℕ)
    (hh : ∀ j k, (a j).h k=h (facePair j k)) (ha : ∀ j, FaceResidue (a j))
    (hroot : h 0=0) : ∀ e, h e ≠ 1 := by
  have hstep (e : Fin 33) : h e=1 ↔ h (pairParent e)=1 := by
    obtain ⟨i,hi⟩ := (facePair_correct (pairBridge e) e).mp (pairBridge_self e)
    obtain ⟨k,hk⟩ := (facePair_correct (pairBridge e) (pairParent e)).mp (pairBridge_parent e)
    have hs := (ha (pairBridge e)).one_iff i k
    rw [hh,hh,hi,hk] at hs
    exact hs
  have hmain : ∀ m, ∀ e : Fin 33, e.val=m → h e≠1 := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro e hem he
      by_cases he0 : e=0
      · subst e; omega
      · have hp : (pairParent e).val < m := by simpa only [hem] using pairParent_lt e he0
        exact ih (pairParent e).val hp (pairParent e) rfl ((hstep e).mp he)
  intro e
  exact hmain e.val e rfl
 theorem uniform_tail_dichotomy : ∃ D₀ : ℕ, ∀ D ≥ D₀,
    ∀ (full : Fin 22 → Bool) (a : Fin 22 → TailTuple) (h : Fin 33 → ℕ),
    GlobalTailFeasible D full a h →
    (∑ j, tailSlack D (full j) (a j))+T2x32 h ≤ 0 →
    (∀ j, (a j).c=0) ∧ (∀ e, h e=0 ∨ h e=2) ∧
    (∀ j, tailSlack D (full j) (a j)=0) ∧ T2x32 h=0 ∧
    (∑ j, tailGain D (full j) (a j))=(2/3:ℝ)*∑ e, triangular (h e) := by
  obtain ⟨D₀,hD₀⟩ := eventually_integer_regime
  refine ⟨D₀,?_⟩
  intro D hD full a h ha htotal
  have hreg := hD₀ D hD full a h ha htotal
  have hn (j : Fin 22) : 0 ≤ tailSlack D (full j) (a j) := by
    cases hj : full j with
    | false => exact tailSlack_lower_nonneg (by simpa only [hj] using ha.1 j)
    | true => exact (integer_slack_classification (by simpa only [hj] using ha.1 j)
        (hreg j hj).1 (hreg j hj).2).1
  have hsn : 0 ≤ ∑ j, tailSlack D (full j) (a j) := Finset.sum_nonneg (fun j _ => hn j)
  have he : T2x32 h=0 := by linarith [separationExcess_nonneg h]
  have hsz : (∑ j, tailSlack D (full j) (a j))=0 := by linarith
  have hz (j : Fin 22) : tailSlack D (full j) (a j)=0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hn j)).mp hsz j (Finset.mem_univ j)
  have hr (j : Fin 22) : FaceResidue (a j) := by
    cases hj : full j with
    | false => exact lower_zero_face_residue (by simpa only [hj] using ha.1 j) (by simpa only [hj] using hz j)
    | true =>
        exact full_zero_face_residue (by simpa only [hj] using ha.1 j)
          (hreg j hj).1 (hreg j hj).2 (by simpa only [hj] using hz j)
  have hnone := residue_propagation a h ha.2 hr (residue_root_zero h he)
  have hface (j : Fin 22) : (a j).c=0 ∧ ∀ k, (a j).h k=0 ∨ (a j).h k=2 := by
    rcases hr j with hh | ⟨_hc,hh⟩
    · exact hh
    · exact (hnone (facePair j 0) (by rw [←ha.2]; exact hh 0)).elim
  refine ⟨fun j => (hface j).1,?_,hz,he,?_⟩
  · intro e
    obtain ⟨k,hk⟩ := (facePair_correct (pairBridge e) e).mp (pairBridge_self e)
    have hh := (hface (pairBridge e)).2 k
    rwa [ha.2,hk] at hh
  · have hg (j : Fin 22) : tailGain D (full j) (a j)=
        (1/3:ℝ)*∑ k, triangular (h (facePair j k)) := by
      have hh := sub_eq_zero.mp (hz j)
      change faceBaseline D (a j).c (fun k => (a j).s k)=tailGain D (full j) (a j) at hh
      rw [←hh]
      have hk (k : Fin 3) : (a j).s k=h (facePair j k) := by
        have hk := ha.2 j k
        simpa only [TailTuple.h,(hface j).1,zero_add] using hk
      simp only [faceBaseline,(hface j).1,Nat.cast_zero,mul_zero,zero_add,hk]
      ring
    simp_rw [hg]
    rw [←Finset.mul_sum,sum_face_pairs (fun e => triangular (h e))]
    ring
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open scoped BigOperators
def T2x82 (D r c : ℕ) (s : Fin 3 → ℕ)
    (u : T2x27 D r c)
    (θ : BaseParameters (D-c) (r-u.val.val) (s 0) (s 1) (s 2)) : TailTuple where
  c := c
  u := u.val.val
  v := D-c-θ.val.2.2.2.val
  p := ![θ.val.1.val,θ.val.2.1.val,θ.val.2.2.1.val]
  t := ![s 0-θ.val.1.val,s 1-θ.val.2.1.val,s 2-θ.val.2.2.1.val]
theorem plantedTailTuple_s (D r c : ℕ) (s : Fin 3 → ℕ)
    (u : T2x27 D r c)
    (θ : BaseParameters (D-c) (r-u.val.val) (s 0) (s 1) (s 2)) (i : Fin 3) :
    (T2x82 D r c s u θ).s i = s i := by
  have h := θ.property
  unfold BaseFeasible at h
  fin_cases i <;> simp [T2x82,TailTuple.s] <;> omega
theorem plantedTailTuple_feasible (D r c : ℕ) (hD : D=2*r) (hc : c ≤ D)
    (s : Fin 3 → ℕ) (hs : (∑ i, s i) ≤ D-c)
    (u : T2x27 D r c)
    (θ : BaseParameters (D-c) (r-u.val.val) (s 0) (s 1) (s 2)) :
    T2x47 D true (T2x82 D r c s u θ) := by
  have hu := u.property.1
  have huc : u.val.val ≤ c := Nat.le_of_lt_succ u.val.isLt
  have hθ := θ.property
  unfold BaseFeasible at hθ
  have hn : θ.val.2.2.2.val ≤ D-c := Nat.le_of_lt_succ θ.val.2.2.2.isLt
  have hdc : ((D-c:ℕ):ℝ) = (D:ℝ)-c := Nat.cast_sub hc
  have hru : ((r-u.val.val:ℕ):ℝ) = (r:ℝ)-u.val.val := Nat.cast_sub hu
  have hDs : (D:ℝ)=2*r := by exact_mod_cast hD
  refine ⟨hc,?_,fun _ => ⟨huc,?_,?_,?_⟩⟩
  · change (∑ i, (T2x82 D r c s u θ).s i) ≤ D-c
    simpa only [plantedTailTuple_s] using hs
  · intro i
    fin_cases i
    all_goals dsimp [T2x82,TailTuple.delta]
    · have hh := hθ.2.2.2.2.2.2.2.2.1
      have hh' : ((s 0-θ.val.1.val:ℕ):ℝ)+2*(r-u.val.val:ℕ) ≤ (D-c:ℕ)+θ.val.1.val := by exact_mod_cast hh
      rw [hdc,hru] at hh'; linarith
    · have hh := hθ.2.2.2.2.2.2.2.2.2.1
      have hh' : ((s 1-θ.val.2.1.val:ℕ):ℝ)+2*(r-u.val.val:ℕ) ≤ (D-c:ℕ)+θ.val.2.1.val := by exact_mod_cast hh
      rw [hdc,hru] at hh'; linarith
    · have hh := hθ.2.2.2.2.2.2.2.2.2.2.1
      have hh' : ((s 2-θ.val.2.2.1.val:ℕ):ℝ)+2*(r-u.val.val:ℕ) ≤ (D-c:ℕ)+θ.val.2.2.1.val := by exact_mod_cast hh
      rw [hdc,hru] at hh'; linarith
  · intro i
    fin_cases i
    all_goals dsimp [T2x82,TailTuple.delta]
    · have hh := hθ.2.2.2.2.2.2.2.2.2.2.2.1
      have hh' : ((D-c-θ.val.2.2.2.val:ℕ):ℝ)+2*(r-u.val.val:ℕ) ≤ (D-c:ℕ)+θ.val.1.val := by exact_mod_cast hh
      rw [hdc,hru] at hh'; linarith
    · have hh := hθ.2.2.2.2.2.2.2.2.2.2.2.2.1
      have hh' : ((D-c-θ.val.2.2.2.val:ℕ):ℝ)+2*(r-u.val.val:ℕ) ≤ (D-c:ℕ)+θ.val.2.1.val := by exact_mod_cast hh
      rw [hdc,hru] at hh'; linarith
    · have hh := hθ.2.2.2.2.2.2.2.2.2.2.2.2.2
      have hh' : ((D-c-θ.val.2.2.2.val:ℕ):ℝ)+2*(r-u.val.val:ℕ) ≤ (D-c:ℕ)+θ.val.2.2.1.val := by exact_mod_cast hh
      rw [hdc,hru] at hh'; linarith
  · have hh := hθ.2.2.2.2.1
    have hh' : (θ.val.2.2.2.val:ℝ)+(θ.val.1.val+θ.val.2.1.val+θ.val.2.2.1.val) ≤ 3*(r-u.val.val:ℕ) := by exact_mod_cast hh
    rw [hru] at hh'
    simp only [T2x82,TailTuple.delta,TailTuple.P,Fin.sum_univ_three,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,Nat.cast_sub hn,hdc]
    linarith
noncomputable def fullPlantedExponent (D c r : ℕ) (s : Fin 3 → ℕ)
    (u : T2x27 D r c)
    (θ : BaseParameters (D-c) (r-u.val.val) (s 0) (s 1) (s 2)) : ℝ :=
  ((D:ℝ)+1)*c+(∑ i, triangular (s i))+3*triangular r-4*triangular D+
    T2x19 D c+(u.val.val:ℝ)*(c-u.val.val:ℕ)+triangular (D-u.val.val:ℕ)+
    3*triangular (D-c:ℕ)-3*triangular (r-u.val.val:ℕ)+
    T2x74 (D-c) (r-u.val.val) (s 0) (s 1) (s 2) θ.val
theorem fullPlantedExponent_eq (D c r : ℕ) (hD : D=2*r) (hc : c ≤ D)
    (s : Fin 3 → ℕ) (u : T2x27 D r c)
    (θ : BaseParameters (D-c) (r-u.val.val) (s 0) (s 1) (s 2)) :
    fullPlantedExponent D c r s u θ = tailGain D true (T2x82 D r c s u θ) := by
  have hu := u.property.1
  have huc : u.val.val ≤ c := Nat.le_of_lt_succ u.val.isLt
  have huD : u.val.val ≤ D := huc.trans hc
  have hθ := θ.property
  unfold BaseFeasible at hθ
  have hn : θ.val.2.2.2.val ≤ D-c := Nat.le_of_lt_succ θ.val.2.2.2.isLt
  have hiso : (T2x19 D c:ℝ) + triangular (D-c:ℕ) = triangular D+(c:ℝ)*(D-c:ℕ) := by
    have hh := congrArg (Nat.cast : ℕ → ℝ) (isotropicExponent_add D c hc)
    simpa only [Nat.cast_add,Nat.cast_mul,triangular_nat] using hh
  have hDs : (D:ℝ)=2*r := by exact_mod_cast hD
  have h0 : θ.val.1.val ≤ s 0 := hθ.2.2.2.2.2.1
  have h1 : θ.val.2.1.val ≤ s 1 := hθ.2.2.2.2.2.2.1
  have h2 : θ.val.2.2.1.val ≤ s 2 := hθ.2.2.2.2.2.2.2.1
  unfold fullPlantedExponent tailGain plantedGain T2x82 TailTuple.delta T2x74
  simp only [ite_true,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,Nat.cast_add,triangular_nat,Nat.cast_sub hn,Nat.cast_sub hc,
    Nat.cast_sub hu,Nat.cast_sub huc,Nat.cast_sub huD,Nat.cast_sub h0,Nat.cast_sub h1,Nat.cast_sub h2]
  rw [Nat.cast_sub hc] at hiso
  dsimp [triangular] at hiso ⊢
  rw [show (T2x19 D c:ℝ) = _ from (eq_sub_iff_add_eq.mpr hiso)]
  rw [hDs]
  ring
end SidorenkoCounterexample
end OAI
namespace OAI
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
 theorem real_card_sigma_le {B : Type*} [Finite B] {C : B → Type*} [∀ b, Finite (C b)]
    (m : ℝ) (h : ∀ b, (Nat.card (C b) : ℝ) ≤ m) :
    (Nat.card (Σ b, C b) : ℝ) ≤ Nat.card B*m := by
  classical
  let := Fintype.ofFinite B
  let _ (b : B) := Fintype.ofFinite (C b)
  simp only [Nat.card_eq_fintype_card,Fintype.card_sigma,Nat.cast_sum]
  calc
    (∑ b, (Fintype.card (C b):ℝ)) ≤ ∑ _b : B, m := Finset.sum_le_sum (fun b _ => by simpa only [Nat.card_eq_fintype_card] using h b)
    _ = (Fintype.card B:ℝ)*m := by simp
section PairDifference
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable (A B : Submodule K V)
noncomputable def pairFormDifference : (SymForm K A × SymForm K B) →ₗ[K] SymForm K ↥(A ⊓ B) :=
  (symFormPull (Submodule.inclusion inf_le_left : ↥(A ⊓ B) →ₗ[K] A)).comp (LinearMap.fst K _ _) -
    (symFormPull (Submodule.inclusion inf_le_right : ↥(A ⊓ B) →ₗ[K] B)).comp (LinearMap.snd K _ _)
 theorem pairFormDifference_surjective : Function.Surjective (pairFormDifference A B) := by
  intro F
  obtain ⟨G,hG⟩ := symFormPull_surjective
    (Submodule.inclusion inf_le_left : ↥(A ⊓ B) →ₗ[K] A) (Submodule.inclusion_injective _) F
  refine ⟨(G,0),?_⟩
  change symFormPull _ G-symFormPull _ 0=F
  rw [map_zero,sub_zero,hG]
 theorem pairFormDifference_nullity_bound [Fintype K] [Finite V] (t : ℕ)
    (ht : t ≤ finrank K ↥(A ⊓ B)) :
    (Nat.card {FG : SymForm K A × SymForm K B //
      t ≤ finrank K (graphDifference A B FG.1.val FG.2.val).ker} : ℝ) /
        Nat.card (SymForm K A × SymForm K B) ≤
      2^t/(Fintype.card K : ℝ)^((t+1).choose 2) := by
  change (Nat.card {FG : SymForm K A × SymForm K B //
      t ≤ finrank K (pairFormDifference A B FG).val.ker} : ℝ) / _ ≤ _
  rw [surjective_linear_probability (pairFormDifference A B) (pairFormDifference_surjective A B) (fun F => t ≤ finrank K F.val.ker)]
  exact symmetric_nullity_probability_bound t ht
end PairDifference
section PairBaseCounts
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
abbrev T2x40 (r p : ℕ) :=
  {R : DimSubspace K V r × DimSubspace K V r // finrank K ↥(R.1.val ⊓ R.2.val) = p}
abbrev PairBaseCode (r p : ℕ) :=
  Σ R : DimSubspace K V r, Σ P : DimSubspace K R.val p,
    {S : DimSubspace K V r // P.val.map R.val.subtype ≤ S.val}
noncomputable def pairBaseCode {r p : ℕ} (RS : T2x40 (K := K) (V := V) r p) :
    PairBaseCode (K := K) (V := V) r p := by
  let R := RS.val.1
  let S := RS.val.2
  let P := (R.val ⊓ S.val).comap R.val.subtype
  have hP : finrank K P = p := by
    rw [(Submodule.comapSubtypeEquivOfLe (inf_le_left : R.val ⊓ S.val ≤ R.val)).finrank_eq]
    exact RS.property
  refine ⟨R,⟨P,hP⟩,S,?_⟩
  intro x hx
  obtain ⟨y,hy,rfl⟩ := hx
  exact hy.2
 theorem pairBaseCode_injective (r p : ℕ) :
    Function.Injective (pairBaseCode (K := K) (V := V) (r := r) (p := p)) := by
  intro a b h
  apply Subtype.ext
  exact congrArg (fun c : PairBaseCode (K := K) (V := V) r p => (c.1,c.2.2.val)) h
variable [Fintype K] [Finite V]
 theorem subspacePairProfile_card_upper (r p : ℕ) (hr : r ≤ finrank K V) (hp : p ≤ r) :
    (Nat.card (T2x40 (K := K) (V := V) r p) : ℝ) ≤
      (2^r*(Fintype.card K : ℝ)^(r*(finrank K V-r))) *
        ((2^p*(Fintype.card K : ℝ)^(p*(r-p))) *
          (2^r*(Fintype.card K : ℝ)^((r-p)*(finrank K V-r)))) := by
  have hq : (0:ℝ) ≤ Fintype.card K := by positivity
  have hP (R : DimSubspace K V r) (P : DimSubspace K R.val p) :
      (Nat.card {S : DimSubspace K V r // P.val.map R.val.subtype ≤ S.val} : ℝ) ≤
        2^r*(Fintype.card K : ℝ)^((r-p)*(finrank K V-r)) := by
    have hd : finrank K (P.val.map R.val.subtype) = p :=
      (Submodule.finrank_map_subtype_eq R.val P.val).trans P.property
    have hh := (containingSubspace_card_bounds (P.val.map R.val.subtype) r (by rwa [hd]) hr).2
    rwa [hd] at hh
  have hR (R : DimSubspace K V r) :
      (Nat.card (Σ P : DimSubspace K R.val p,
        {S : DimSubspace K V r // P.val.map R.val.subtype ≤ S.val}) : ℝ) ≤
        (2^p*(Fintype.card K : ℝ)^(p*(r-p))) *
          (2^r*(Fintype.card K : ℝ)^((r-p)*(finrank K V-r))) := by
    refine (real_card_sigma_le _ (hP R)).trans ?_
    have hc := T2x26 (K := K) (V := R.val) p (by rwa [R.property])
    rw [R.property] at hc
    exact mul_le_mul_of_nonneg_right hc (by positivity)
  have hc : (Nat.card (T2x40 (K := K) (V := V) r p) : ℝ) ≤
      Nat.card (PairBaseCode (K := K) (V := V) r p) := by
    exact_mod_cast Nat.card_le_card_of_injective _ (pairBaseCode_injective (K := K) (V := V) r p)
  refine (hc.trans (real_card_sigma_le _ hR)).trans ?_
  exact mul_le_mul_of_nonneg_right (T2x26 r hr) (by positivity)
 theorem subspacePairProfile_probability_bound (r p : ℕ) (hD : finrank K V = 2*r) (hp : p ≤ r) :
    (Fintype.card K : ℝ)^(p*p) * Nat.card (T2x40 (K := K) (V := V) r p) ≤
      2^(2*r+p)*(Nat.card (DimSubspace K V r):ℝ)^2 := by
  have hr : r ≤ finrank K V := by omega
  have hc := subspacePairProfile_card_upper (K := K) (V := V) r p hr hp
  rw [hD,show 2*r-r=r by omega] at hc
  have hl := subspace_count_lower (K := K) (V := V) r hr
  rw [hD,show 2*r-r=r by omega] at hl
  have hexp : p*p+r*r+(p*(r-p)+(r-p)*r)=2*(r*r) := by
    have hs := Nat.sub_add_cancel hp
    nlinarith
  have htwo : r+(p+r)=2*r+p := by omega
  let q : ℝ := Fintype.card K
  calc
    q^(p*p)*Nat.card (T2x40 (K := K) (V := V) r p) ≤
        q^(p*p)*((2^r*q^(r*r))*((2^p*q^(p*(r-p)))*(2^r*q^((r-p)*r)))) :=
      mul_le_mul_of_nonneg_left hc (by positivity)
    _ = 2^(2*r+p)*(q^(r*r))^2 := by
      rw [show q^(p*p)*((2^r*q^(r*r))*((2^p*q^(p*(r-p)))*(2^r*q^((r-p)*r)))) =
        (2^r*(2^p*2^r))*(q^(p*p)*q^(r*r)*(q^(p*(r-p))*q^((r-p)*r))) by ring]
      rw [←pow_add,←pow_add,htwo,←pow_add,←pow_add,←pow_add,hexp,pow_mul]
      rw [pow_mul]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hl 2) (by positivity)
end PairBaseCounts
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
abbrev T2x77 (r h : ℕ) := {p : Fin (r+1) // p.val ≤ h ∧ h-p.val ≤ p.val}
noncomputable instance pairParametersFintype (r h : ℕ) : Fintype (T2x77 r h) := Fintype.ofFinite _
section PairLiftCounts
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
abbrev DualPairBase (r : ℕ) := DimSubspace K (Module.Dual K V) r × DimSubspace K (Module.Dual K V) r
abbrev DualPairForms {r : ℕ} (R : DualPairBase (K := K) (V := V) r) :=
  SymForm K R.1.val.dualCoannihilator × SymForm K R.2.val.dualCoannihilator
abbrev CanonicalPairProfile (r h : ℕ) :=
  {RF : Σ R : DualPairBase (K := K) (V := V) r, DualPairForms R //
    finrank K ↥((dualGraph RF.1.1.val RF.2.1).val ⊓ (dualGraph RF.1.2.val RF.2.2).val) = h}
abbrev DualPairLiftEvent {r p : ℕ} (R : T2x40 (K := K) (V := Module.Dual K V) r p) (t : ℕ) :=
  {F : DualPairForms R.val // t ≤ finrank K (graphDifference _ _ F.1.val F.2.val).ker}
abbrev CenterPairProfile (r h : ℕ) :=
  {L : T2x59 (K := K) (V := V) r × T2x59 (K := K) (V := V) r //
    finrank K ↥(L.1.val.val ⊓ L.2.val.val) = h}
noncomputable def dualPairProductEquiv (r : ℕ) (hr : r ≤ finrank K V) :
    (Σ R : DualPairBase (K := K) (V := V) r, DualPairForms R) ≃
      T2x59 (K := K) (V := V) r × T2x59 (K := K) (V := V) r :=
  ( { toFun := fun RF => (⟨RF.1.1,RF.2.1⟩,⟨RF.1.2,RF.2.2⟩)
      invFun := fun P => ⟨(P.1.1,P.2.1),(P.1.2,P.2.2)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl } :
      (Σ R : DualPairBase (K := K) (V := V) r, DualPairForms R) ≃
        (Σ R : DimSubspace K (Module.Dual K V) r, SymForm K R.val.dualCoannihilator) ×
        (Σ R : DimSubspace K (Module.Dual K V) r, SymForm K R.val.dualCoannihilator)).trans
    ((dualPairStratumEquiv r hr).prodCongr (dualPairStratumEquiv r hr))
noncomputable def canonicalPairProfileEquiv (r h : ℕ) (hr : r ≤ finrank K V) :
    CanonicalPairProfile (K := K) (V := V) r h ≃ CenterPairProfile (K := K) (V := V) r h :=
  (dualPairProductEquiv r hr).subtypeEquiv (fun _ => Iff.rfl)
noncomputable def canonicalPairParameter {r h : ℕ} (hD : finrank K V=2*r)
    (P : CanonicalPairProfile (K := K) (V := V) r h) : T2x77 r h := by
  let p := finrank K ↥(P.val.1.1.val ⊓ P.val.1.2.val)
  have hpr : p ≤ r := (Submodule.finrank_mono inf_le_left).trans_eq P.val.1.1.property
  have hph : p ≤ h := by
    simpa only [P.property] using T2x70 P.val.1.1.val P.val.1.2.val P.val.2.1 P.val.2.2
  have ht := dualGraph_pair_extra_feasible P.val.1.1 P.val.1.2 P.val.2.1 P.val.2.2 P.property
  refine ⟨⟨p,by omega⟩,hph,?_⟩
  dsimp [p] at *
  omega
 theorem dualGraph_pair_kernel_exact (R S : Submodule K (Module.Dual K V))
    (F : SymForm K R.dualCoannihilator) (G : SymForm K S.dualCoannihilator) :
    finrank K ↥((dualGraph R F).val ⊓ (dualGraph S G).val) =
      finrank K ↥(R ⊓ S)+finrank K (graphDifference _ _ F.val G.val).ker := by
  have hh := T2x43 R.dualCoannihilator S.dualCoannihilator F.val G.val
  rw [Subspace.dualCoannihilator_dualAnnihilator_eq (W := R),
    Subspace.dualCoannihilator_dualAnnihilator_eq (W := S)] at hh
  exact hh
 theorem dualGraph_pair_kernel_ge (R S : Submodule K (Module.Dual K V))
    (F : SymForm K R.dualCoannihilator) (G : SymForm K S.dualCoannihilator) (h : ℕ)
    (hh : finrank K ↥((dualGraph R F).val ⊓ (dualGraph S G).val) = h) :
    h-finrank K ↥(R ⊓ S) ≤ finrank K (graphDifference _ _ F.val G.val).ker := by
  rw [dualGraph_pair_kernel_exact] at hh
  omega
noncomputable def canonicalPairCoding {r h : ℕ} (hD : finrank K V=2*r)
    (P : CanonicalPairProfile (K := K) (V := V) r h) :
    Σ p : T2x77 r h, Σ R : T2x40 (K := K) (V := Module.Dual K V) r p.val.val,
      DualPairLiftEvent R (h-p.val.val) :=
  ⟨canonicalPairParameter hD P,⟨P.val.1,rfl⟩,P.val.2,
    dualGraph_pair_kernel_ge _ _ _ _ h P.property⟩
 theorem canonicalPairCoding_injective {r h : ℕ} (hD : finrank K V=2*r) :
    Function.Injective (canonicalPairCoding (K := K) (V := V) (h := h) hD) := by
  let recover : (Σ p : T2x77 r h, Σ R : T2x40 (K := K) (V := Module.Dual K V) r p.val.val,
      DualPairLiftEvent R (h-p.val.val)) → Σ R : DualPairBase (K := K) (V := V) r, DualPairForms R :=
    fun T => ⟨T.2.1.val,T.2.2.val⟩
  intro P Q hh
  exact Subtype.ext (congrArg recover hh)
variable [Fintype K] [Finite V]
omit [Finite V] in
 theorem dualPairForms_card {r : ℕ} (R : DualPairBase (K := K) (V := V) r) :
    Nat.card (DualPairForms R) = Fintype.card K ^ (2*((finrank K V-r+1).choose 2)) := by
  have h₁ := coannihilator_finrank R.1.val
  have h₂ := coannihilator_finrank R.2.val
  rw [R.1.property] at h₁
  rw [R.2.property] at h₂
  have hd₁ : finrank K R.1.val.dualCoannihilator=finrank K V-r := by omega
  have hd₂ : finrank K R.2.val.dualCoannihilator=finrank K V-r := by omega
  simp only [DualPairForms,Nat.card_prod,symForm_card,hd₁,hd₂,←pow_add,two_mul]
 theorem center_stratum_square (r : ℕ) (hr : r ≤ finrank K V) :
    (Nat.card (T2x59 (K := K) (V := V) r):ℝ)^2 =
      (Nat.card (DimSubspace K (Module.Dual K V) r):ℝ)^2 *
        (Fintype.card K:ℝ)^(2*((finrank K V-r+1).choose 2)) := by
  rw [vertical_pair_count r hr,Nat.cast_mul,Nat.cast_pow,mul_pow,
    Nat.card_congr (dualDimSubspaceEquiv (K := K) (V := V) r hr),←pow_mul,Nat.mul_comm _ 2]
 theorem dualPairLift_probability_bound {r p : ℕ} (hD : finrank K V=2*r)
    (R : T2x40 (K := K) (V := Module.Dual K V) r p) (t : ℕ) (ht : t ≤ p) :
    (Nat.card (DualPairLiftEvent R t):ℝ)/Nat.card (DualPairForms R.val) ≤
      2^t/(Fintype.card K:ℝ)^((t+1).choose 2) := by
  have hd := coannihilator_pair_finrank R.val.1.val R.val.2.val
  rw [R.val.1.property,R.val.2.property,R.property,hD] at hd
  exact pairFormDifference_nullity_bound _ _ t (by omega)
 theorem pairPlanted_bound_one (r h : ℕ) (hD : finrank K V=2*r) (p : T2x77 r h) :
    (Nat.card (Σ R : T2x40 (K := K) (V := Module.Dual K V) r p.val.val,
      DualPairLiftEvent R (h-p.val.val)):ℝ) /
      (Nat.card (T2x59 (K := K) (V := V) r):ℝ)^2 ≤
        2^(2*r+p.val.val+(h-p.val.val)) /
          (Fintype.card K:ℝ)^(p.val.val*p.val.val+(h-p.val.val+1).choose 2) := by
  classical
  let := Module.finite_of_finite K (M := Module.Dual K V)
  let RType := T2x40 (K := K) (V := Module.Dual K V) r p.val.val
  let q : ℝ := Fintype.card K
  let f := 2*((finrank K V-r+1).choose 2)
  let b : ℝ := 2^(h-p.val.val)/q^((h-p.val.val+1).choose 2)
  have hq : 0 < q := by dsimp [q]; exact_mod_cast Fintype.card_pos (α := K)
  have hforms (R : RType) : (Nat.card (DualPairLiftEvent R (h-p.val.val)):ℝ) ≤ b*q^f := by
    have hh := dualPairLift_probability_bound hD R (h-p.val.val) p.property.2
    rw [dualPairForms_card,Nat.cast_pow] at hh
    exact (div_le_iff₀ (pow_pos hq _)).mp hh
  have hc := real_card_sigma_le _ hforms
  have hr : r ≤ finrank K V := by omega
  have hg : 0 < (Nat.card (DimSubspace K (Module.Dual K V) r):ℝ) := by
    have hh := subspace_count_lower (K := K) (V := Module.Dual K V) r (by rw [Subspace.dual_finrank_eq]; exact hr)
    exact lt_of_lt_of_le (by positivity) hh
  have hp := subspacePairProfile_probability_bound (K := K) (V := Module.Dual K V) r p.val.val
    (by rwa [Subspace.dual_finrank_eq]) (by omega)
  rw [center_stratum_square r hr]
  calc
    _ ≤ (Nat.card RType:ℝ)*(b*q^f)/((Nat.card (DimSubspace K (Module.Dual K V) r):ℝ)^2*q^f) :=
      div_le_div_of_nonneg_right hc (by positivity)
    _ = ((Nat.card RType:ℝ)/(Nat.card (DimSubspace K (Module.Dual K V) r):ℝ)^2)*b := by
      field_simp
    _ ≤ (2^(2*r+p.val.val)/q^(p.val.val*p.val.val))*b := by
      apply mul_le_mul_of_nonneg_right _ (by dsimp [b]; positivity)
      apply (div_le_div_iff₀ (sq_pos_of_pos hg) (pow_pos hq _)).mpr
      simpa only [mul_comm] using hp
    _ = _ := by dsimp [b]; rw [div_mul_div_comm,←pow_add,←pow_add]
end PairLiftCounts
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open scoped BigOperators
 theorem two_active_gain_bound (h p : ℕ) (hph : p ≤ h) (htp : h-p ≤ p) :
    ((h+1).choose 2 : ℝ) ≤ p*p+((h-p+1).choose 2 : ℕ)+((h/2+1).choose 2 : ℕ) := by
  rw [triangular_nat,triangular_nat,triangular_nat]
  have he : ((h-p : ℕ):ℝ)=(h:ℝ)-p := Nat.cast_sub hph
  rw [he]
  unfold triangular
  have hh : h=2*(h/2) ∨ h=2*(h/2)+1 := by omega
  have ha : (0:ℝ) ≤ h/2 := by positivity
  rcases hh with hh|hh
  · have hh' : (h:ℝ)=2*(h/2 : ℕ) := by exact_mod_cast hh
    have hpa : h/2 ≤ p := by omega
    by_cases hp : p=h/2
    · have hp' : (p:ℝ)=(h/2 : ℕ) := by exact_mod_cast hp
      nlinarith
    · have hp' : (h/2 : ℕ)+1 ≤ (p:ℝ) := by exact_mod_cast (show h/2+1 ≤ p by omega)
      have hm := mul_nonneg (sub_nonneg.mpr (show ((h/2 : ℕ):ℝ) ≤ p by linarith))
        (sub_nonneg.mpr (show (1:ℝ) ≤ p-(h/2 : ℕ) by linarith))
      have hm' := mul_nonneg (show (0:ℝ) ≤ (h/2 : ℕ) by positivity)
        (sub_nonneg.mpr (show ((h/2 : ℕ):ℝ) ≤ p by linarith))
      nlinarith
  · have hh' : (h:ℝ)=2*(h/2 : ℕ)+1 := by exact_mod_cast hh
    have hp' : (h/2 : ℕ)+1 ≤ (p:ℝ) := by exact_mod_cast (show h/2+1 ≤ p by omega)
    have hm := mul_nonneg (show (0:ℝ) ≤ (h/2 : ℕ) by positivity)
      (sub_nonneg.mpr (show (h/2 : ℕ)+1 ≤ (p:ℝ) from hp'))
    nlinarith [sq_nonneg ((p:ℝ)-(h/2 : ℕ)-1)]
section PairFinal
open Module
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype K] [Finite V]
 theorem canonical_center_pair_probability_bound (r h : ℕ) (hD : finrank K V=2*r) :
    (Nat.card (CenterPairProfile (K := K) (V := V) r h):ℝ) /
      (Nat.card (T2x59 (K := K) (V := V) r):ℝ)^2 ≤
    ∑ p : T2x77 r h, 2^(2*r+p.val.val+(h-p.val.val)) /
      (Fintype.card K:ℝ)^(p.val.val*p.val.val+(h-p.val.val+1).choose 2) := by
  classical
  let := Module.finite_of_finite K (M := Module.Dual K V)
  have hr : r ≤ finrank K V := by omega
  rw [←Nat.card_congr (canonicalPairProfileEquiv r h hr)]
  have hc := Nat.card_le_card_of_injective _ (canonicalPairCoding_injective (K := K) (V := V) (h := h) hD)
  have hh : (Nat.card (CanonicalPairProfile (K := K) (V := V) r h):ℝ) ≤
      Nat.card (Σ p : T2x77 r h, Σ R : T2x40 (K := K) (V := Module.Dual K V) r p.val.val,
        DualPairLiftEvent R (h-p.val.val)) := by exact_mod_cast hc
  refine (div_le_div_of_nonneg_right hh (by positivity)).trans ?_
  rw [Nat.card_sigma,Nat.cast_sum,Finset.sum_div]
  exact Finset.sum_le_sum (fun p _ => pairPlanted_bound_one r h hD p)
 theorem canonical_center_pair_gain_bound (r h : ℕ) (hD : finrank K V=2*r) :
    (Fintype.card K:ℝ)^((h+1).choose 2) *
      ((Nat.card (CenterPairProfile (K := K) (V := V) r h):ℝ) /
        (Nat.card (T2x59 (K := K) (V := V) r):ℝ)^2) ≤
      (Nat.card (T2x77 r h):ℝ)*2^(2*r+h)*(Fintype.card K:ℝ)^((h/2+1).choose 2) := by
  have hq : (1:ℝ) ≤ Fintype.card K := by exact_mod_cast Fintype.card_pos (α := K)
  have hqpos : (0:ℝ) < Fintype.card K := by positivity
  have hh := canonical_center_pair_probability_bound (K := K) (V := V) r h hD
  refine (mul_le_mul_of_nonneg_left hh (by positivity)).trans ?_
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑ _p : T2x77 r h, 2^(2*r+h)*(Fintype.card K:ℝ)^((h/2+1).choose 2) := by
      apply Finset.sum_le_sum
      intro p _
      have hs : p.val.val+(h-p.val.val)=h := Nat.add_sub_of_le p.property.1
      have hg : (h+1).choose 2 ≤ p.val.val*p.val.val+(h-p.val.val+1).choose 2+(h/2+1).choose 2 := by
        have hb := two_active_gain_bound h p.val.val p.property.1 p.property.2
        exact_mod_cast hb
      rw [show 2*r+p.val.val+(h-p.val.val)=2*r+h by omega]
      rw [←mul_div_assoc]
      apply (div_le_iff₀ (pow_pos hqpos _)).mpr
      calc
        _ ≤ 2^(2*r+h)*(Fintype.card K:ℝ)^(p.val.val*p.val.val+(h-p.val.val+1).choose 2+(h/2+1).choose 2) := by
          rw [mul_comm]; exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hq hg) (by positivity)
        _ = _ := by rw [pow_add]; ring
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Nat.card_eq_fintype_card]; ring
end PairFinal
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section SymplecticPairPlanted
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E)
abbrev PairCenterSet (r : ℕ) (L M : Submodule K E) :=
  {Y : T2x0 ω // finrank K ↥(L ⊓ Y.val)=r ∧ finrank K ↥(M ⊓ Y.val)=r}
abbrev T2x86 (Y : T2x0 ω) (r h : ℕ) :=
  {L : T2x7 ω Y r × T2x7 ω Y r //
    finrank K ↥(L.1.val.val ⊓ L.2.val.val)=h}
noncomputable def symplecticCenterPairProfileEquiv {V : Type*} [AddCommGroup V] [Module K V]
    (Y : T2x0 ω) (e : (V × Module.Dual K V) ≃ₗ[K] E)
    (he : ∀ x y, ω (e x) (e y)=T2x5 x y)
    (hY : (T2x63 (K := K) (V := V)).map e.toLinearMap=Y.val) (r h : ℕ) :
    CenterPairProfile (K := K) (V := V) r h ≃ T2x86 ω Y r h :=
  let f := symplecticCenterStratumEquiv ω Y e he hY r
  (f.prodCongr f).subtypeEquiv (by
    intro L
    change _ ↔ finrank K ↥(L.1.val.val.map e.toLinearMap ⊓ L.2.val.val.map e.toLinearMap)=h
    rw [T2x83])
noncomputable def pairCenterIsometryEquiv (r : ℕ) (L M : Submodule K E)
    (e : E ≃ₗ[K] E) (he : ∀ x y, ω (e x) (e y)=ω x y) :
    PairCenterSet ω r L M ≃ PairCenterSet ω r (L.map e.toLinearMap) (M.map e.toLinearMap) :=
  (T2x45 ω e he).subtypeEquiv (by
    intro Y
    change (_ ∧ _) ↔ (finrank K ↥(L.map e.toLinearMap ⊓ Y.val.map e.toLinearMap)=r ∧
      finrank K ↥(M.map e.toLinearMap ⊓ Y.val.map e.toLinearMap)=r)
    rw [T2x83,T2x83])
noncomputable def pairCenterProfileEquiv (r h : ℕ) :
    (Σ p : T2x66 ω h, PairCenterSet ω r p.val.1.val p.val.2.val) ≃
      Σ Y : T2x0 ω, T2x86 ω Y r h where
  toFun P := ⟨P.2.val,⟨(⟨P.1.val.1,P.2.property.1⟩,⟨P.1.val.2,P.2.property.2⟩),P.1.property⟩⟩
  invFun P := ⟨⟨(P.2.val.1.val,P.2.val.2.val),P.2.property⟩,
    ⟨P.1,P.2.val.1.property,P.2.val.2.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
variable [Fintype K] [Finite E]
 omit [Fintype K] in
 theorem pairCenter_profile_card (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (r : ℕ) (L M : T2x0 ω) :
    Nat.card (Σ Y : T2x0 ω,
      T2x86 ω Y r (finrank K ↥(L.val ⊓ M.val))) =
    Nat.card (T2x66 ω (finrank K ↥(L.val ⊓ M.val))) * Nat.card (PairCenterSet ω r L.val M.val) := by
  classical
  let := Fintype.ofFinite (T2x66 ω (finrank K ↥(L.val ⊓ M.val)))
  rw [←Nat.card_congr (pairCenterProfileEquiv ω r (finrank K ↥(L.val ⊓ M.val))),Nat.card_sigma]
  have hc (p : T2x66 ω (finrank K ↥(L.val ⊓ M.val))) :
      Nat.card (PairCenterSet ω r p.val.1.val p.val.2.val)=Nat.card (PairCenterSet ω r L.val M.val) := by
    obtain ⟨e,he,hL,hM⟩ := ordered_pair_transitivity ω h2 ha hω
      p.val.1.val p.val.2.val L.val M.val p.val.1.property p.val.2.property L.property M.property p.property
    have hh := Nat.card_congr (pairCenterIsometryEquiv ω r p.val.1.val p.val.2.val e he)
    rwa [hL,hM] at hh
  simp only [hc,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card,Nat.cast_id]
 omit [Fintype K] in
 theorem symplectic_center_stratum_card_eq (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (A B : T2x0 ω) (r : ℕ) :
    Nat.card (T2x7 ω A r)=Nat.card (T2x7 ω B r) := by
  obtain ⟨e,he,hA⟩ := lagrangian_transitivity ω A.val h2 ha hω A.property B.val B.property
  exact Nat.card_congr ((T2x45 ω e he).subtypeEquiv (by
    intro L
    change _ ↔ finrank K ↥(L.val.map e.toLinearMap ⊓ B.val)=r
    rw [←hA,T2x83]))
 theorem symplectic_center_pair_gain_bound (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (r : ℕ) (hD : finrank K E=2*(2*r)) (Y : T2x0 ω) (h : ℕ) :
    (Fintype.card K:ℝ)^((h+1).choose 2)*
      ((Nat.card (T2x86 ω Y r h):ℝ)/
        (Nat.card (T2x7 ω Y r):ℝ)^2) ≤
      (Nat.card (T2x77 r h):ℝ)*2^(2*r+h)*(Fintype.card K:ℝ)^((h/2+1).choose 2) := by
  obtain ⟨e,he,hY⟩ := exists_center_coordinates ω h2 ha hω Y
  rw [←Nat.card_congr (symplecticCenterPairProfileEquiv ω Y e he hY r h),
    ←Nat.card_congr (symplecticCenterStratumEquiv ω Y e he hY r)]
  have hd := T2x6 ω Y.val hω Y.property
  exact canonical_center_pair_gain_bound r h (by omega)
noncomputable def pairFaceDensity (r : ℕ) (A L M : T2x0 ω) : ℝ :=
  (Nat.card (PairCenterSet ω r L.val M.val):ℝ)*(Nat.card (T2x0 ω):ℝ) /
    (Nat.card (T2x7 ω A r):ℝ)^2
end SymplecticPairPlanted
 theorem normalized_pair_gain (L A O Z T C B : ℝ) (hL : 0<L) (hA : 0<A) (hZ : 0≤Z)
    (hC : 0≤C) (hMass : L^2≤C*(T*O)) (hGain : T*O*Z≤L*A^2*B) :
    Z*L/A^2≤C*B := by
  apply (div_le_iff₀ (sq_pos_of_pos hA)).mpr
  apply (mul_le_mul_iff_right₀ hL).mp
  calc
    L*(Z*L) = Z*L^2 := by ring
    _ ≤ Z*(C*(T*O)) := mul_le_mul_of_nonneg_left hMass hZ
    _ = C*(T*O*Z) := by ring
    _ ≤ C*(L*A^2*B) := mul_le_mul_of_nonneg_left hGain hC
    _ = L*(C*B*A^2) := by ring
section PairPointwise
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
 theorem pairFaceDensity_gain_bound (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (r : ℕ) (hD : 2*(2*r)=finrank K E) (A L M : T2x0 ω) :
    pairFaceDensity ω r A L M ≤
      (T2x1 (2*r))^2 *
        ((Nat.card (T2x77 r (finrank K ↥(L.val ⊓ M.val))):ℝ)*
          2^(2*r+finrank K ↥(L.val ⊓ M.val))*
          (Fintype.card K:ℝ)^((finrank K ↥(L.val ⊓ M.val)/2+1).choose 2)) := by
  classical
  let := Fintype.ofFinite (T2x0 ω)
  let h := finrank K ↥(L.val ⊓ M.val)
  let q : ℝ := Fintype.card K
  let a : ℝ := Nat.card (T2x7 ω A r)
  let b : ℝ := (Nat.card (T2x77 r h):ℝ)*2^(2*r+h)*q^((h/2+1).choose 2)
  have hdim := T2x6 ω L.val hω L.property
  have hh : h≤2*r := by have hb := Submodule.finrank_mono (show L.val ⊓ M.val ≤ L.val from inf_le_left); dsimp [h]; omega
  have ha0 : 0<a := symplectic_center_stratum_card_pos ω h2 ha hω (2*r) hD A r (by omega)
  have hq : 0<q := by dsimp [q]; exact_mod_cast Fintype.card_pos (α := K)
  have hLag := T2x18 ω h2 ha hω (2*r) hD
  have hL : (0:ℝ)<Nat.card (T2x0 ω) := (pow_pos hq _).trans_le hLag.1
  have hMass : (Nat.card (T2x0 ω):ℝ)^2 ≤
      (T2x1 (2*r))^2*(q^((h+1).choose 2)*Nat.card (T2x66 ω h)) := by
    calc
      _ ≤ (T2x1 (2*r)*q^((2*r+1).choose 2))^2 := pow_le_pow_left₀ (by positivity) hLag.2 2
      _ = (T2x1 (2*r))^2*q^(2*((2*r+1).choose 2)) := by rw [mul_pow,←pow_mul,Nat.mul_comm _ 2]
      _ ≤ _ := mul_le_mul_of_nonneg_left (orderedPairDim_card_lower ω h2 ha hω (2*r) hD h hh) (by positivity)
  have hg (Y : T2x0 ω) :
      q^((h+1).choose 2)*(Nat.card (T2x86 ω Y r h):ℝ) ≤ a^2*b := by
    have hc := symplectic_center_pair_gain_bound ω h2 ha hω r hD.symm Y h
    rw [←symplectic_center_stratum_card_eq ω h2 ha hω A Y r,←mul_div_assoc] at hc
    exact (div_le_iff₀ (sq_pos_of_pos ha0)).mp hc |>.trans_eq (mul_comm _ _)
  have hGain : q^((h+1).choose 2)*(Nat.card (T2x66 ω h):ℝ)*Nat.card (PairCenterSet ω r L.val M.val) ≤
      (Nat.card (T2x0 ω):ℝ)*a^2*b := by
    rw [mul_assoc,←Nat.cast_mul,←pairCenter_profile_card ω h2 ha hω r L M,Nat.card_sigma,Nat.cast_sum,Finset.mul_sum]
    calc
      _ ≤ ∑ _Y : T2x0 ω, a^2*b := Finset.sum_le_sum (fun Y _ => hg Y)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card]; ring
  exact normalized_pair_gain _ _ _ _ _ _ _ hL ha0 (by positivity) (by positivity) hMass hGain
end PairPointwise
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ActualProfile
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
 theorem actual_profile_pair_sum_le (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D c u v w : ℕ) (hD : 2*D=finrank K E) (p : T2x24 ω c u v w) :
    (u-c)+(v-c)+(w-c) ≤ D-c := by
  let S := T2x57 ω p
  obtain ⟨L,M,N,hzero,hu,hv,hw,_⟩ := fixedCommonProfile_injection ω ha S ⟨p,rfl⟩
  let : Finite (T2x20 ω S.val) := Module.finite_of_finite K
  have hc : c≤D := S.property.2 ▸ T2x16 ω hω D hD S.val S.property.1
  have hd : 2*(D-c)=finrank K (T2x20 ω S.val) := by
    have hh := reducedSpace_finrank ω S.val hω S.property.1
    rw [S.property.2,←hD] at hh
    omega
  simpa only [hu,hv,hw] using symplectic_profile_pair_sum_le
    (T2x2 ω S.val ha) (T2x13 ω S.val ha hω) (D-c) hd L M N hzero
end ActualProfile
end SidorenkoCounterexample
end OAI
namespace OAI
namespace SidorenkoCounterexample
open scoped BigOperators
section Sequential
variable {A : Type*} [Finite A]
def SeqValid (k : ℕ) (R : (Fin k → A) → Prop)
    (P : (n : ℕ) → (Fin (k+n) → A) → A → Prop) :
    (n : ℕ) → (Fin (k+n) → A) → Prop
  | 0,x => R x
  | n+1,x => SeqValid k R P n (Fin.init x) ∧ P n (Fin.init x) (x (Fin.last (k+n)))
abbrev ValidSeq (k : ℕ) (R : (Fin k → A) → Prop)
    (P : (n : ℕ) → (Fin (k+n) → A) → A → Prop) (n : ℕ) :=
  {x : Fin (k+n) → A // SeqValid k R P n x}
noncomputable def validSeqSuccEquiv (k : ℕ) (R : (Fin k → A) → Prop)
    (P : (n : ℕ) → (Fin (k+n) → A) → A → Prop) (n : ℕ) :
    ValidSeq k R P (n+1) ≃ Σ x : ValidSeq k R P n, {a : A // P n x.val a} where
  toFun x := ⟨⟨Fin.init x.val,x.property.1⟩,⟨x.val (Fin.last (k+n)),x.property.2⟩⟩
  invFun x := ⟨Fin.snoc (α := fun _ => A) x.1.val x.2.val,by
    have hs : Fin.snoc (α := fun _ => A) x.1.val x.2.val (Fin.last (k+n))=x.2.val := Fin.snoc_last (α := fun _ => A) x.2.val x.1.val
    change SeqValid k R P n (Fin.init (Fin.snoc (α := fun _ => A) x.1.val x.2.val)) ∧
      P n (Fin.init (Fin.snoc (α := fun _ => A) x.1.val x.2.val)) (Fin.snoc (α := fun _ => A) x.1.val x.2.val (Fin.last (k+n)))
    rw [Fin.init_snoc,hs]
    exact ⟨x.1.property,x.2.property⟩⟩
  left_inv x := Subtype.ext (Fin.snoc_init_self x.val)
  right_inv x := by
    rcases x with ⟨⟨x,hx⟩,⟨a,ha⟩⟩
    dsimp
    apply Sigma.ext
    · apply Subtype.ext
      exact Fin.init_snoc (α := fun _ => A) a x
    · apply (Subtype.heq_iff_coe_eq
        (p := fun b => P n (Fin.init (Fin.snoc (α := fun _ => A) x a)) b)
        (q := fun b => P n x b) (fun b => by rw [Fin.init_snoc])).mpr
      exact Fin.snoc_last (α := fun _ => A) a x
 theorem validSeq_card_bound (k : ℕ) (R : (Fin k → A) → Prop)
    (P : (n : ℕ) → (Fin (k+n) → A) → A → Prop) (B : ℕ → ℝ)
    (hB : ∀ n, 0≤B n) (hb : ∀ n (x : ValidSeq k R P n), (Nat.card {a : A // P n x.val a}:ℝ) ≤ B n)
    (n : ℕ) : (Nat.card (ValidSeq k R P n):ℝ) ≤
      Nat.card {x : Fin k → A // R x} * ∏ i : Fin n, B i.val := by
  classical
  induction n with
  | zero => simp only [Fin.prod_univ_zero,mul_one]; exact le_rfl
  | succ n ih =>
    let := Fintype.ofFinite (ValidSeq k R P n)
    rw [Nat.card_congr (validSeqSuccEquiv k R P n),Nat.card_sigma,Nat.cast_sum]
    calc
      _ ≤ ∑ _x : ValidSeq k R P n, B n := Finset.sum_le_sum (fun x _ => hb n x)
      _ = (Nat.card (ValidSeq k R P n):ℝ)*B n := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card]
      _ ≤ (Nat.card {x : Fin k → A // R x} * ∏ i : Fin n, B i.val)*B n := mul_le_mul_of_nonneg_right ih (hB n)
      _ = _ := by rw [Fin.prod_univ_castSucc]; simp only [Fin.val_castSucc,Fin.val_last]; ring
end Sequential
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open scoped BigOperators
def faceVertex : Fin 22 → Fin 3 → Fin 13 := ![![0, 1, 3], ![0, 1, 9], ![0, 2, 3], ![0, 2, 9], ![1, 3, 10], ![1, 7, 10], ![1, 7, 12], ![1, 9, 12], ![2, 3, 4], ![2, 4, 9], ![3, 4, 11], ![3, 10, 11], ![4, 8, 9], ![4, 8, 11], ![5, 6, 7], ![5, 6, 11], ![5, 7, 10], ![5, 10, 11], ![6, 7, 12], ![6, 8, 11], ![6, 8, 12], ![8, 9, 12]]
def classFace : Fin 6 → Fin 11 → Fin 22 := ![![0, 1, 2, 4, 5, 16, 14, 18, 20, 19, 13], ![3, 9, 8, 10, 11, 17, 15, 12, 21, 7, 6], ![0, 2, 8, 9, 12, 4, 11, 5, 6, 18, 14], ![1, 3, 7, 21, 20, 19, 13, 10, 15, 17, 16], ![0, 1, 3, 9, 7, 6, 5, 16, 14, 15, 19], ![2, 8, 10, 11, 4, 17, 13, 12, 21, 20, 18]]
def classPoint : Fin 6 → Fin 13 → Fin 13 := ![![0, 1, 3, 9, 2, 10, 7, 5, 6, 12, 8, 11, 4], ![0, 2, 9, 4, 3, 11, 10, 5, 6, 8, 12, 1, 7], ![0, 1, 3, 2, 4, 9, 8, 10, 11, 7, 12, 6, 5], ![0, 1, 9, 2, 12, 8, 6, 11, 4, 3, 5, 10, 7], ![0, 1, 3, 9, 2, 4, 12, 7, 10, 5, 6, 11, 8], ![0, 2, 3, 4, 11, 10, 1, 5, 8, 9, 12, 6, 7]]
def classOldZero : Fin 6 → Fin 10 → Fin 13 := ![![0, 0, 1, 1, 6, 7, 8, 8, 8, 10], ![1, 1, 4, 4, 6, 7, 3, 9, 2, 11], ![0, 3, 3, 4, 1, 2, 1, 1, 9, 11], ![0, 1, 2, 5, 6, 5, 8, 6, 10, 10], ![0, 0, 4, 1, 1, 1, 7, 9, 9, 10], ![1, 2, 2, 2, 5, 3, 3, 8, 8, 11]]
def classOldOne : Fin 6 → Fin 10 → Fin 13 := ![![1, 2, 2, 5, 5, 6, 6, 9, 10, 11], ![2, 3, 3, 5, 5, 5, 2, 2, 10, 10], ![2, 2, 4, 5, 2, 7, 7, 9, 10, 9], ![2, 2, 4, 4, 5, 7, 7, 7, 7, 11], ![1, 3, 3, 3, 6, 7, 8, 7, 10, 11], ![2, 3, 4, 5, 4, 4, 8, 9, 10, 10]]
def classOldPair : Fin 6 → Fin 10 → Fin 33 := ![![5, 1, 6, 11, 20, 25, 30, 31, 28, 22], ![4, 7, 8, 13, 21, 27, 10, 18, 16, 15], ![1, 2, 7, 10, 6, 12, 11, 19, 23, 30], ![3, 9, 16, 24, 28, 22, 14, 29, 27, 26], ![5, 3, 4, 9, 15, 19, 20, 25, 32, 29], ![2, 8, 13, 12, 21, 14, 17, 18, 24, 31]]
def classNewPairZero : Fin 6 → Fin 10 → Fin 33 := ![![3, 0, 11, 19, 25, 32, 31, 28, 29, 17], ![7, 2, 13, 12, 26, 32, 17, 24, 9, 19], ![0, 7, 4, 17, 11, 13, 19, 15, 30, 32], ![0, 15, 18, 28, 29, 17, 8, 32, 26, 25], ![3, 0, 7, 15, 19, 11, 25, 32, 27, 28], ![7, 13, 12, 6, 26, 17, 10, 24, 28, 30]]
def classNewPairOne : Fin 6 → Fin 10 → Fin 33 := ![![9, 2, 12, 20, 26, 30, 23, 24, 22, 14], ![10, 8, 14, 21, 27, 29, 18, 16, 15, 23], ![2, 8, 10, 18, 12, 21, 20, 23, 31, 25], ![4, 16, 24, 31, 22, 14, 13, 27, 21, 20], ![9, 4, 10, 16, 23, 20, 26, 30, 29, 22], ![8, 14, 21, 11, 27, 22, 18, 16, 31, 23]]
 theorem faceVertex_correct : ∀ j, faces j={faceVertex j 0,faceVertex j 1,faceVertex j 2} := by decide
 theorem classPoint_bijective : ∀ c, Function.Bijective (classPoint c) := by decide
 theorem classOldZero_lt : ∀ c n, (classOldZero c n).val<3+n.val := by decide
 theorem classOldOne_lt : ∀ c n, (classOldOne c n).val<3+n.val := by decide
 theorem classRoot_correct : ∀ c, faces (classFace c 0)={classPoint c 0,classPoint c 1,classPoint c 2} := by decide
 theorem classStep_correct : ∀ c n, faces (classFace c n.succ)=
    {classPoint c (classOldZero c n),classPoint c (classOldOne c n),classPoint c ⟨3+n.val,by omega⟩} := by decide
 theorem classOldPair_correct : ∀ c n, T2x12 (classOldPair c n)=
    {classPoint c (classOldZero c n),classPoint c (classOldOne c n)} := by decide
 theorem classNewPairZero_correct : ∀ c n, T2x12 (classNewPairZero c n)=
    {classPoint c (classOldZero c n),classPoint c ⟨3+n.val,by omega⟩} := by decide
 theorem classNewPairOne_correct : ∀ c n, T2x12 (classNewPairOne c n)=
    {classPoint c (classOldOne c n),classPoint c ⟨3+n.val,by omega⟩} := by decide
 def classContains (c : Fin 6) (j : Fin 22) : Prop := ∃ n, classFace c n=j
 instance (c : Fin 6) (j : Fin 22) : Decidable (classContains c j) := inferInstanceAs (Decidable (∃ n, classFace c n=j))
 def classInternal (c : Fin 6) (e : Fin 33) : Prop := ∀ k, classContains c (pairFace e k)
 instance (c : Fin 6) (e : Fin 33) : Decidable (classInternal c e) := inferInstanceAs (Decidable (∀ k, classContains c (pairFace e k)))
 theorem classFace_occurs : ∀ j, (Finset.univ.filter fun cn : Fin 6 × Fin 11 => classFace cn.1 cn.2=j).card=3 := by decide
 theorem classStep_pairs : ∀ c n, Finset.image (facePair (classFace c n.succ)) Finset.univ =
    {classOldPair c n,classNewPairZero c n,classNewPairOne c n} := by decide
 theorem classStep_pairs_distinct : ∀ c n, classOldPair c n≠classNewPairZero c n ∧
    classOldPair c n≠classNewPairOne c n ∧ classNewPairZero c n≠classNewPairOne c n := by decide
 theorem faceVertex_pairs : ∀ j k, T2x12 (facePair j k)=
    (![ {faceVertex j 0,faceVertex j 1}, {faceVertex j 0,faceVertex j 2}, {faceVertex j 1,faceVertex j 2}] : Fin 3 → Finset (Fin 13)) k := by decide
 theorem classRootPairZero : ∀ c, T2x12 (facePair (classFace c 0) 0)={classPoint c 0,classPoint c 1} := by decide
 theorem classRootPairOne : ∀ c, T2x12 (facePair (classFace c 0) 1)={classPoint c 0,classPoint c 2} := by decide
 theorem classRootPairTwo : ∀ c, T2x12 (facePair (classFace c 0) 2)={classPoint c 1,classPoint c 2} := by decide
 theorem classTree_occurs : ∀ e, (Finset.univ.filter fun cn : Fin 6 × Fin 10 => classOldPair cn.1 cn.2=e).card=3-separationCount e := by decide
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
 theorem inverse_power_inequality (q C L N : ℝ) (a : ℕ) (hq : 0<q)
    (h : q^a*N≤C*L) : N≤C*L*q^(-(a:ℝ)) := by
  rw [Real.rpow_neg hq.le,Real.rpow_natCast,←div_eq_mul_inv]
  apply (le_div_iff₀ (pow_pos hq a)).mpr
  simpa only [mul_comm] using h
section RawProfile
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
def T2x87 (D c u v w : ℕ) : ℕ :=
  (D+1)*c+((u-c+1).choose 2+(v-c+1).choose 2+(w-c+1).choose 2)
 theorem tripleProfile_card_raw (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D=finrank K E) (c u v w : ℕ) (hc : c≤D) :
    (Nat.card (T2x24 ω c u v w):ℝ) ≤ T2x11 D *
      (Nat.card (T2x0 ω):ℝ)^3 * (Fintype.card K:ℝ)^(-(T2x87 D c u v w:ℝ)) := by
  have hq : 0<(Fintype.card K:ℝ) := by exact_mod_cast Fintype.card_pos (α:=K)
  have hb := (T2x18 ω h2 ha hω D hD).1
  apply inverse_power_inequality _ _ _ _ _ hq
  calc
    _ ≤ T2x11 D*(Fintype.card K:ℝ)^(3*(D+1).choose 2) :=
      tripleProfile_card_upper ω h2 ha hω D hD c u v w hc
    _ ≤ _ := by
      gcongr
      · exact (T2x88 D).le
      · rw [mul_comm 3, pow_mul]
        exact pow_le_pow_left₀ (by positivity) hb 3
 theorem conditionalProfile_card_raw (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D=finrank K E) (L M : T2x0 ω) (c v w : ℕ) (hc : c≤D) :
    (Nat.card (T2x75 ω L M c v w):ℝ) ≤ T2x11 D *
      (Nat.card (T2x0 ω):ℝ) * (Fintype.card K:ℝ)^
        (((finrank K ↥(L.val ⊓ M.val)+1).choose 2:ℝ)-(T2x87 D c (finrank K ↥(L.val ⊓ M.val)) v w:ℝ)) := by
  have hq : 0<(Fintype.card K:ℝ) := by exact_mod_cast Fintype.card_pos (α:=K)
  have hb := (T2x18 ω h2 ha hω D hD).1
  have hh := conditionalProfile_card_upper ω h2 ha hω D hD L M c v w hc
  have hh' : (Fintype.card K:ℝ)^(T2x87 D c (finrank K ↥(L.val ⊓ M.val)) v w)*
      (Nat.card (T2x75 ω L M c v w):ℝ) ≤ T2x11 D*
        ((Nat.card (T2x0 ω):ℝ)*(Fintype.card K:ℝ)^((finrank K ↥(L.val ⊓ M.val)+1).choose 2)) := by
    change (Fintype.card K:ℝ)^(T2x87 D c (finrank K ↥(L.val ⊓ M.val)) v w)*
      (Nat.card (T2x75 ω L M c v w):ℝ) ≤ _ at hh
    refine hh.trans ?_
    rw [pow_add]
    calc
      _ ≤ T2x11 D*((Fintype.card K:ℝ)^((finrank K ↥(L.val ⊓ M.val)+1).choose 2)*
        (Nat.card (T2x0 ω):ℝ)) := by gcongr; exact (T2x88 D).le
      _ = _ := by ring
  have hh'' := inverse_power_inequality _ _ _ _ _ hq hh'
  convert hh'' using 1
  rw [Real.rpow_sub hq,Real.rpow_natCast,Real.rpow_natCast]
  rw [Real.rpow_neg hq.le,Real.rpow_natCast]
  ring
end RawProfile
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
noncomputable def tupleThreeEquiv {A : Type*} : (Fin 3 → A) ≃ A × A × A where
  toFun x := (x 0,x 1,x 2)
  invFun x := ![x.1,x.2.1,x.2.2]
  left_inv x := by funext i; fin_cases i <;> rfl
  right_inv _ := rfl
def T2x49 (D : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (j : Fin 22) : ℕ :=
  (D+1)*c j+∑ k : Fin 3, (h (facePair j k)-c j+1).choose 2
 theorem root_natural_cost (D : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (j : Fin 22) :
    T2x87 D (c j) (h (facePair j 0)) (h (facePair j 1)) (h (facePair j 2))=T2x49 D c h j := by
  simp only [T2x87,T2x49,Fin.sum_univ_three]
 theorem step_natural_cost (D : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (κ : Fin 6) (n : Fin 10) :
    T2x87 D (c (classFace κ n.succ)) (h (classOldPair κ n))
      (h (classNewPairZero κ n)) (h (classNewPairOne κ n))=T2x49 D c h (classFace κ n.succ) := by
  let f (e : Fin 33) := (h e-c (classFace κ n.succ)+1).choose 2
  have hs : (∑ e ∈ Finset.univ.image (facePair (classFace κ n.succ)), f e)=
      ∑ k : Fin 3, f (facePair (classFace κ n.succ) k) :=
    Finset.sum_image (fun a _ b _ hab => facePair_injective _ hab)
  rw [classStep_pairs] at hs
  obtain ⟨h01,h02,h12⟩ := classStep_pairs_distinct κ n
  simp only [Finset.sum_insert,Finset.mem_insert,Finset.mem_singleton,h01,h02,h12,
    or_self,not_false_eq_true,Finset.sum_singleton] at hs
  unfold T2x87 T2x49
  change _ = (D+1)*c (classFace κ n.succ)+∑ k, f (facePair (classFace κ n.succ) k)
  rw [←hs]
  simp only [f]
  omega
section ExposureProfile
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E)
def T2x23 (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (L : Fin 13 → T2x0 ω) : Prop :=
  (∀ j, finrank K ↥((faces j).inf fun i => (L i).val : Submodule K E)=c j) ∧
  (∀ e, finrank K ↥((T2x12 e).inf fun i => (L i).val : Submodule K E)=h e)
def LocalProfile (c u v w : ℕ) (L M N : T2x0 ω) : Prop :=
  finrank K ↥((L.val ⊓ M.val) ⊓ N.val)=c ∧ finrank K ↥(L.val ⊓ M.val)=u ∧
  finrank K ↥(L.val ⊓ N.val)=v ∧ finrank K ↥(M.val ⊓ N.val)=w
 theorem T2x23.local {c : Fin 22 → ℕ} {h : Fin 33 → ℕ} {L : Fin 13 → T2x0 ω}
    (hL : T2x23 ω c h L) (j : Fin 22) (i k l : Fin 13) (e f g : Fin 33)
    (hj : faces j={i,k,l}) (he : T2x12 e={i,k}) (hf : T2x12 f={i,l})
    (hg : T2x12 g={k,l}) : LocalProfile ω (c j) (h e) (h f) (h g) (L i) (L k) (L l) := by
  classical
  unfold T2x23 at hL
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
def classRootConstraint (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (κ : Fin 6) (x : Fin 3 → T2x0 ω) : Prop :=
  LocalProfile ω (c (classFace κ 0)) (h (facePair (classFace κ 0) 0))
    (h (facePair (classFace κ 0) 1)) (h (facePair (classFace κ 0) 2)) (x 0) (x 1) (x 2)
def T2x42 (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (κ : Fin 6)
    (n : ℕ) (x : Fin (3+n) → T2x0 ω) (Y : T2x0 ω) : Prop :=
  if hn : n<10 then
    LocalProfile ω (c (classFace κ ⟨n+1,by omega⟩)) (h (classOldPair κ ⟨n,hn⟩))
      (h (classNewPairZero κ ⟨n,hn⟩)) (h (classNewPairOne κ ⟨n,hn⟩))
      (x ⟨(classOldZero κ ⟨n,hn⟩).val,classOldZero_lt κ ⟨n,hn⟩⟩)
      (x ⟨(classOldOne κ ⟨n,hn⟩).val,classOldOne_lt κ ⟨n,hn⟩⟩) Y
  else False
noncomputable def rootConstraintEquiv (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (κ : Fin 6) :
    {x : Fin 3 → T2x0 ω // classRootConstraint ω c h κ x} ≃
      T2x24 ω (c (classFace κ 0)) (h (facePair (classFace κ 0) 0))
        (h (facePair (classFace κ 0) 1)) (h (facePair (classFace κ 0) 2)) :=
  tupleThreeEquiv.subtypeEquiv (fun _ => Iff.rfl)
variable [Fintype K] [Finite E]
noncomputable def classStepBound (D : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (κ : Fin 6) (n : ℕ) : ℝ :=
  if hn : n<10 then T2x11 D*(Nat.card (T2x0 ω):ℝ)*
    (Fintype.card K:ℝ)^(((h (classOldPair κ ⟨n,hn⟩)+1).choose 2:ℝ)-(T2x49 D c h (classFace κ ⟨n+1,by omega⟩):ℝ))
  else 0
 omit [Finite E] in
 theorem classStepBound_nonneg (D : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (κ : Fin 6) (n : ℕ) :
    0≤classStepBound ω D c h κ n := by
  unfold classStepBound
  split_ifs
  · exact mul_nonneg (mul_nonneg (T2x88 D).le (by positivity)) (Real.rpow_nonneg (by positivity) _)
  · exact le_rfl
 theorem classStep_card_bound (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D=finrank K E) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (hc : ∀ j, c j≤D)
    (κ : Fin 6) (n : ℕ) (x : Fin (3+n) → T2x0 ω) :
    (Nat.card {Y : T2x0 ω // T2x42 ω c h κ n x Y}:ℝ) ≤ classStepBound ω D c h κ n := by
  classical
  by_cases hn : n<10
  · let L := x ⟨(classOldZero κ ⟨n,hn⟩).val,classOldZero_lt κ ⟨n,hn⟩⟩
    let M := x ⟨(classOldOne κ ⟨n,hn⟩).val,classOldOne_lt κ ⟨n,hn⟩⟩
    let j : Fin 22 := classFace κ ⟨n+1,by omega⟩
    let e := classOldPair κ ⟨n,hn⟩
    let f := classNewPairZero κ ⟨n,hn⟩
    let g := classNewPairOne κ ⟨n,hn⟩
    have hp : ∀ Y, T2x42 ω c h κ n x Y ↔ LocalProfile ω (c j) (h e) (h f) (h g) L M Y := by
      intro Y; simp only [T2x42,dif_pos hn]; rfl
    by_cases hh : finrank K ↥(L.val ⊓ M.val)=h e
    · have heq : Nat.card {Y // T2x42 ω c h κ n x Y}=Nat.card (T2x75 ω L M (c j) (h f) (h g)) := by
        apply Nat.card_congr
        exact Equiv.subtypeEquivRight (fun Y => by rw [hp]; exact ⟨fun hY => ⟨hY.1,hY.2.2⟩,fun hY => ⟨hY.1,hh,hY.2⟩⟩)
      rw [heq]
      have hb := conditionalProfile_card_raw ω h2 ha hω D hD L M (c j) (h f) (h g) (hc j)
      rw [hh] at hb
      have hcost := step_natural_cost D c h κ ⟨n,hn⟩
      change T2x87 D (c j) (h e) (h f) (h g)=T2x49 D c h j at hcost
      rw [hcost] at hb
      simpa only [classStepBound,dif_pos hn, e,j] using hb
    · have hem : IsEmpty {Y // T2x42 ω c h κ n x Y} := ⟨fun Y => hh ((hp Y.val).mp Y.property).2.1⟩
      have hz := Nat.card_eq_zero.mpr (Or.inl hem)
      rw [hz,Nat.cast_zero]
      exact classStepBound_nonneg ω D c h κ n
  · have hem : IsEmpty {Y // T2x42 ω c h κ n x Y} :=
      ⟨fun Y => by simpa only [T2x42,dif_neg hn] using Y.property⟩
    rw [Nat.card_eq_zero.mpr (Or.inl hem),Nat.cast_zero,classStepBound,dif_neg hn]
noncomputable def classPrefix (κ : Fin 6) (L : Fin 13 → T2x0 ω)
    (n : ℕ) (hn : n≤10) : Fin (3+n) → T2x0 ω :=
  fun i => L (classPoint κ ⟨i.val,by omega⟩)
 omit [Fintype K] [Finite E] in
 theorem classPrefix_valid {c : Fin 22 → ℕ} {h : Fin 33 → ℕ}
    {L : Fin 13 → T2x0 ω} (hL : T2x23 ω c h L)
    (κ : Fin 6) (n : ℕ) (hn : n≤10) :
    SeqValid 3 (classRootConstraint ω c h κ) (T2x42 ω c h κ) n (classPrefix ω κ L n hn) := by
  induction n with
  | zero =>
    exact T2x23.local ω hL _ _ _ _ _ _ _ (classRoot_correct κ)
      (classRootPairZero κ) (classRootPairOne κ) (classRootPairTwo κ)
  | succ n ih =>
    have hn' : n<10 := by omega
    refine ⟨?_,?_⟩
    · exact ih (by omega)
    · simp only [T2x42,dif_pos hn']
      exact T2x23.local ω hL _ _ _ _ _ _ _ (classStep_correct κ ⟨n,hn'⟩)
        (classOldPair_correct κ ⟨n,hn'⟩) (classNewPairZero_correct κ ⟨n,hn'⟩)
        (classNewPairOne_correct κ ⟨n,hn'⟩)
noncomputable def pointProfile_class_injection (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (κ : Fin 6) :
    {L : Fin 13 → T2x0 ω // T2x23 ω c h L} ↪
      ValidSeq 3 (classRootConstraint ω c h κ) (T2x42 ω c h κ) 10 where
  toFun L := ⟨classPrefix ω κ L.val 10 le_rfl,classPrefix_valid ω L.property κ 10 le_rfl⟩
  inj' := by
    intro L M hm
    apply Subtype.ext
    funext i
    obtain ⟨j,hj⟩ := (classPoint_bijective κ).2 i
    have hh := congrFun (congrArg Subtype.val hm) j
    change L.val (classPoint κ j)=M.val (classPoint κ j) at hh
    simpa only [hj] using hh
 theorem classRoot_card_bound (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D=finrank K E) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (hc : ∀ j, c j≤D)
    (κ : Fin 6) : (Nat.card {x : Fin 3 → T2x0 ω // classRootConstraint ω c h κ x}:ℝ) ≤
      T2x11 D*(Nat.card (T2x0 ω):ℝ)^3*
        (Fintype.card K:ℝ)^(-(T2x49 D c h (classFace κ 0):ℝ)) := by
  rw [Nat.card_congr (rootConstraintEquiv ω c h κ)]
  have hb := tripleProfile_card_raw ω h2 ha hω D hD (c (classFace κ 0))
    (h (facePair (classFace κ 0) 0)) (h (facePair (classFace κ 0) 1))
    (h (facePair (classFace κ 0) 2)) (hc _)
  simpa only [root_natural_cost] using hb
noncomputable def classExponent (D : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (κ : Fin 6) : ℝ :=
  -(∑ i : Fin 11, (T2x49 D c h (classFace κ i):ℝ))+
    ∑ i : Fin 10, ((h (classOldPair κ i)+1).choose 2:ℝ)
 omit [Finite E] in
 theorem classStepBound_product (D : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (κ : Fin 6) :
    (∏ n : Fin 10, classStepBound ω D c h κ n.val)=
      (T2x11 D*(Nat.card (T2x0 ω):ℝ))^10*
        (Fintype.card K:ℝ)^(∑ n : Fin 10,
          (((h (classOldPair κ n)+1).choose 2:ℝ)-(T2x49 D c h (classFace κ n.succ):ℝ))) := by
  have hq : 0<(Fintype.card K:ℝ) := by exact_mod_cast Fintype.card_pos (α:=K)
  simp only [classStepBound,dif_pos (Fin.isLt _),Fin.eta,Finset.prod_mul_distrib,
    Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  rw [Real.rpow_sum_of_pos hq,mul_pow]
  rfl
 theorem pointProfile_class_card_bound (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D=finrank K E) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (hc : ∀ j, c j≤D)
    (κ : Fin 6) : (Nat.card {L : Fin 13 → T2x0 ω // T2x23 ω c h L}:ℝ) ≤
      (T2x11 D)^11*(Nat.card (T2x0 ω):ℝ)^13*
        (Fintype.card K:ℝ)^(classExponent D c h κ) := by
  have hq : 0<(Fintype.card K:ℝ) := by exact_mod_cast Fintype.card_pos (α:=K)
  have hs := validSeq_card_bound 3 (classRootConstraint ω c h κ) (T2x42 ω c h κ)
    (classStepBound ω D c h κ) (classStepBound_nonneg ω D c h κ)
    (fun n x => classStep_card_bound ω h2 ha hω D hD c h hc κ n x.val) 10
  have hr := classRoot_card_bound ω h2 ha hω D hD c h hc κ
  have hi : (Nat.card {L : Fin 13 → T2x0 ω // T2x23 ω c h L}:ℝ) ≤
      Nat.card (ValidSeq 3 (classRootConstraint ω c h κ) (T2x42 ω c h κ) 10) := by
    exact_mod_cast Nat.card_le_card_of_injective _ (pointProfile_class_injection ω c h κ).injective
  calc
    _ ≤ _ := hi.trans hs
    _ ≤ (T2x11 D*(Nat.card (T2x0 ω):ℝ)^3*
        (Fintype.card K:ℝ)^(-(T2x49 D c h (classFace κ 0):ℝ)))*
        ∏ n : Fin 10,classStepBound ω D c h κ n.val :=
      mul_le_mul_of_nonneg_right hr (Finset.prod_nonneg fun n _ => classStepBound_nonneg ω D c h κ n.val)
    _ = _ := by
      rw [classStepBound_product]
      have he : -(T2x49 D c h (classFace κ 0):ℝ)+
          (∑ n : Fin 10, (((h (classOldPair κ n)+1).choose 2:ℝ)-
            (T2x49 D c h (classFace κ n.succ):ℝ)))=classExponent D c h κ := by
        unfold classExponent
        rw [Fin.sum_univ_succ (fun i : Fin 11 => (T2x49 D c h (classFace κ i):ℝ)),Finset.sum_sub_distrib]
        ring
      rw [←he,Real.rpow_add hq]
      ring
end ExposureProfile
 theorem sum_class_faces (f : Fin 22 → ℝ) :
    (∑ κ : Fin 6, ∑ n : Fin 11, f (classFace κ n))=3*∑ j, f j := by
  rw [←Fintype.sum_prod_type (fun p : Fin 6 × Fin 11 => f (classFace p.1 p.2))]
  rw [←Finset.sum_fiberwise Finset.univ (fun p : Fin 6 × Fin 11 => classFace p.1 p.2)]
  have he (j : Fin 22) : (∑ p ∈ Finset.univ.filter (fun p : Fin 6 × Fin 11 => classFace p.1 p.2=j),
      f (classFace p.1 p.2))=3*f j := by
    calc _ = ∑ _p ∈ Finset.univ.filter (fun p : Fin 6 × Fin 11 => classFace p.1 p.2=j), f j := by
            apply Finset.sum_congr rfl
            intro p hp
            rw [(Finset.mem_filter.mp hp).2]
         _ = _ := by rw [Finset.sum_const,classFace_occurs]; simp only [nsmul_eq_mul,Nat.cast_ofNat]
  simp_rw [he]
  rw [Finset.mul_sum]
 theorem sum_class_old_pairs (f : Fin 33 → ℝ) :
    (∑ κ : Fin 6, ∑ n : Fin 10, f (classOldPair κ n))=∑ e, (3-(separationCount e:ℝ))*f e := by
  rw [←Fintype.sum_prod_type (fun p : Fin 6 × Fin 10 => f (classOldPair p.1 p.2))]
  rw [←Finset.sum_fiberwise Finset.univ (fun p : Fin 6 × Fin 10 => classOldPair p.1 p.2)]
  apply Finset.sum_congr rfl
  intro e _
  calc _ = ∑ _p ∈ Finset.univ.filter (fun p : Fin 6 × Fin 10 => classOldPair p.1 p.2=e), f e := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [(Finset.mem_filter.mp hp).2]
       _ = _ := by rw [Finset.sum_const,classTree_occurs]; simp only [nsmul_eq_mul,Nat.cast_sub (separationCount_le e),Nat.cast_ofNat]
noncomputable def profileCost (D : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) : ℝ :=
  (∑ j, (T2x49 D c h j:ℝ))/2-(∑ e, (3-(separationCount e:ℝ))*triangular (h e))/6
 theorem sum_class_exponent (D : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) :
    (∑ κ, classExponent D c h κ)= -6*profileCost D c h := by
  simp only [classExponent,Finset.sum_add_distrib,Finset.sum_neg_distrib,triangular_nat]
  rw [sum_class_faces (fun j => (T2x49 D c h j:ℝ)),sum_class_old_pairs (fun e => triangular (h e))]
  unfold profileCost
  ring
section GlobalExposure
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
 theorem pointProfile_card_bound (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D=finrank K E) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (hc : ∀ j, c j≤D) :
    (Nat.card {L : Fin 13 → T2x0 ω // T2x23 ω c h L}:ℝ) ≤
      (T2x11 D)^11*(Nat.card (T2x0 ω):ℝ)^13*
        (Fintype.card K:ℝ)^(-profileCost D c h) := by
  have hq : 0<(Fintype.card K:ℝ) := by exact_mod_cast Fintype.card_pos (α:=K)
  have hb := Finset.prod_le_prod (s:=Finset.univ) (f:=fun _κ : Fin 6 =>
      (Nat.card {L : Fin 13 → T2x0 ω // T2x23 ω c h L}:ℝ))
    (fun _κ _ => Nat.cast_nonneg _) (fun κ _ => pointProfile_class_card_bound ω h2 ha hω D hD c h hc κ)
  simp only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin] at hb
  rw [←Real.rpow_sum_of_pos hq,sum_class_exponent] at hb
  have he : -6*profileCost D c h=(-profileCost D c h)*(6:ℕ) := by norm_num; ring
  rw [he,Real.rpow_mul_natCast hq.le] at hb
  have hC := T2x88 D
  apply (pow_le_pow_iff_left₀ (Nat.cast_nonneg _) (by positivity) (by norm_num : (6:ℕ)≠0)).mp
  simpa only [mul_pow] using hb
end GlobalExposure
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open scoped BigOperators
section ZeroSequential
variable {A : Type*} [Finite A]
def ZeroSeqValid (P : (n : ℕ) → (Fin n → A) → A → Prop) :
    (n : ℕ) → (Fin n → A) → Prop
  | 0,_ => True
  | n+1,x => ZeroSeqValid P n (Fin.init x) ∧ P n (Fin.init x) (x (Fin.last n))
abbrev ZeroValidSeq (P : (n : ℕ) → (Fin n → A) → A → Prop) (n : ℕ) :=
  {x : Fin n → A // ZeroSeqValid P n x}
noncomputable def zeroValidSeqSuccEquiv
    (P : (n : ℕ) → (Fin n → A) → A → Prop) (n : ℕ) :
    ZeroValidSeq P (n+1) ≃ Σ x : ZeroValidSeq P n, {a : A // P n x.val a} where
  toFun x := ⟨⟨Fin.init x.val,x.property.1⟩,⟨x.val (Fin.last n),x.property.2⟩⟩
  invFun x := ⟨Fin.snoc (α := fun _ => A) x.1.val x.2.val,by
    have hs : Fin.snoc (α := fun _ => A) x.1.val x.2.val (Fin.last n)=x.2.val := Fin.snoc_last (α := fun _ => A) x.2.val x.1.val
    change ZeroSeqValid P n (Fin.init (Fin.snoc (α := fun _ => A) x.1.val x.2.val)) ∧
      P n (Fin.init (Fin.snoc (α := fun _ => A) x.1.val x.2.val)) (Fin.snoc (α := fun _ => A) x.1.val x.2.val (Fin.last n))
    rw [Fin.init_snoc,hs]
    exact ⟨x.1.property,x.2.property⟩⟩
  left_inv x := Subtype.ext (Fin.snoc_init_self x.val)
  right_inv x := by
    rcases x with ⟨⟨x,hx⟩,⟨a,ha⟩⟩
    dsimp
    apply Sigma.ext
    · apply Subtype.ext
      exact Fin.init_snoc (α := fun _ => A) a x
    · apply (Subtype.heq_iff_coe_eq
        (p := fun b => P n (Fin.init (Fin.snoc (α := fun _ => A) x a)) b)
        (q := fun b => P n x b) (fun b => by rw [Fin.init_snoc])).mpr
      exact Fin.snoc_last (α := fun _ => A) a x
 theorem zeroValidSeq_card_bound
    (P : (n : ℕ) → (Fin n → A) → A → Prop) (B : ℕ → ℝ)
    (hB : ∀ n, 0≤B n) (hb : ∀ n (x : ZeroValidSeq P n), (Nat.card {a : A // P n x.val a}:ℝ) ≤ B n)
    (n : ℕ) : (Nat.card (ZeroValidSeq P n):ℝ) ≤
      ∏ i : Fin n, B i.val := by
  classical
  induction n with
  | zero =>
    rw [Fin.prod_univ_zero]
    norm_num [ZeroValidSeq,ZeroSeqValid,Nat.card_eq_fintype_card,Fintype.card_subtype]
  | succ n ih =>
    let := Fintype.ofFinite (ZeroValidSeq P n)
    rw [Nat.card_congr (zeroValidSeqSuccEquiv P n),Nat.card_sigma,Nat.cast_sum]
    calc
      _ ≤ ∑ _x : ZeroValidSeq P n, B n := Finset.sum_le_sum (fun x _ => hb n x)
      _ = (Nat.card (ZeroValidSeq P n):ℝ)*B n := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card]
      _ ≤ (∏ i : Fin n, B i.val)*B n := mul_le_mul_of_nonneg_right ih (hB n)
      _ = _ := by rw [Fin.prod_univ_castSucc]; simp only [Fin.val_castSucc,Fin.val_last]
end ZeroSequential
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section OrthogonalTuple
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E)
def OrthogonalStep (R : ℕ → ℕ → Prop) (n : ℕ) (x : Fin n → E) (y : E) : Prop :=
  LinearIndependent K (Fin.snoc (α := fun _ => E) x y) ∧ ∀ i : Fin n, R i.val n → ω (x i) y=0
abbrev OrthogonalTuple (R : ℕ → ℕ → Prop) (n : ℕ) :=
  {x : Fin n → E // LinearIndependent K x ∧ ∀ i j : Fin n, i.val<j.val → R i.val j.val → ω (x i) (x j)=0}
 theorem orthogonalSeq_independent (R : ℕ → ℕ → Prop) (n : ℕ)
    (x : ZeroValidSeq (OrthogonalStep ω R) n) : LinearIndependent K x.val := by
  cases n with
  | zero =>
    exact linearIndependent_empty_type
  | succ n =>
    have hx := x.property.2.1
    rwa [Fin.snoc_init_self] at hx
 theorem orthogonalTuple_valid (R : ℕ → ℕ → Prop) (n : ℕ) (x : OrthogonalTuple ω R n) :
    ZeroSeqValid (OrthogonalStep ω R) n x.val := by
  induction n with
  | zero => trivial
  | succ n ih =>
    have hli : LinearIndependent K (Fin.init x.val) := x.property.1.comp Fin.castSucc (Fin.castSucc_injective n)
    have hrel : ∀ i j : Fin n, i.val<j.val → R i.val j.val → ω (Fin.init x.val i) (Fin.init x.val j)=0 := by
      intro i j hij hr
      exact x.property.2 i.castSucc j.castSucc hij hr
    refine ⟨ih ⟨Fin.init x.val,hli,hrel⟩,?_,?_⟩
    · simpa only [Fin.snoc_init_self] using x.property.1
    · intro i hir
      exact x.property.2 i.castSucc (Fin.last n) i.isLt (by simpa only [Fin.val_castSucc,Fin.val_last,Nat.zero_add] using hir)
noncomputable def orthogonalTupleToSeq (R : ℕ → ℕ → Prop) (n : ℕ) :
    OrthogonalTuple ω R n ↪ ZeroValidSeq (OrthogonalStep ω R) n where
  toFun x := ⟨x.val,orthogonalTuple_valid ω R n x⟩
  inj' := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : ZeroValidSeq (OrthogonalStep ω R) n => z.val) h
noncomputable def T2x51 (R : ℕ → ℕ → Prop) (n : ℕ) : ℕ :=
  Nat.card {i : Fin n // R i.val n}
variable [Fintype K] [Finite E]
 theorem independent_orthogonal_card (hω : ω.Nondegenerate) {n : ℕ} (x : Fin n → E)
    (hx : LinearIndependent K x) (s : Finset (Fin n)) :
    Nat.card {y : E // ∀ i∈s, ω (x i) y=0}=(Fintype.card K)^(finrank K E-s.card) := by
  classical
  let z : s → E := fun i => x i.val
  let S : Submodule K E := Submodule.span K (Set.range z)
  have hli : LinearIndependent K z := hx.comp (fun i : s => i.val) Subtype.val_injective
  have hdim : finrank K S=s.card := by rw [finrank_span_eq_card hli,Fintype.card_coe]
  have he : {y : E // ∀ i∈s, ω (x i) y=0} ≃ ω.orthogonal S :=
    Equiv.subtypeEquivRight (fun y => by
      constructor
      · intro hy
        rw [LinearMap.BilinForm.mem_orthogonal_iff]
        have hh : S ≤ LinearMap.ker (ω.flip y) := by
          apply Submodule.span_le.mpr
          rintro _ ⟨i,rfl⟩
          exact hy i.val i.property
        intro v hv
        exact hh hv
      · intro hy i hi
        exact hy (x i) (Submodule.subset_span ⟨⟨i,hi⟩,rfl⟩))
  rw [Nat.card_congr he,Module.natCard_eq_pow_finrank (K := K),Nat.card_eq_fintype_card,
    ω.finrank_orthogonal hω S,hdim]
 theorem orthogonalStep_card_bound (hω : ω.Nondegenerate) (R : ℕ → ℕ → Prop)
    (n : ℕ) (x : ZeroValidSeq (OrthogonalStep ω R) n) :
    (Nat.card {y : E // OrthogonalStep ω R n x.val y}:ℝ) ≤
      (Fintype.card K:ℝ)^(finrank K E-T2x51 R n) := by
  classical
  let s : Finset (Fin n) := Finset.univ.filter fun i => R i.val n
  have he : s.card=T2x51 R n := by
    rw [T2x51,Nat.card_eq_fintype_card,Fintype.card_subtype]
  have hi : Nat.card {y : E // OrthogonalStep ω R n x.val y} ≤ Nat.card {y : E // ∀ i∈s, ω (x.val i) y=0} :=
    Nat.card_le_card_of_injective (fun y => ⟨y.val,fun i hi => y.property.2 i (Finset.mem_filter.mp hi).2⟩)
      (by
        intro a b h
        apply Subtype.ext
        exact congrArg (fun z : {y : E // ∀ i∈s, ω (x.val i) y=0} => z.val) h)
  rw [independent_orthogonal_card ω hω x.val (orthogonalSeq_independent ω R n x),he] at hi
  exact_mod_cast hi
 theorem orthogonalTuple_card_bound (hω : ω.Nondegenerate) (R : ℕ → ℕ → Prop) (n : ℕ) :
    (Nat.card (OrthogonalTuple ω R n):ℝ) ≤
      (Fintype.card K:ℝ)^(∑ i : Fin n, (finrank K E-T2x51 R i.val)) := by
  classical
  have hs := zeroValidSeq_card_bound (OrthogonalStep ω R)
    (fun i => (Fintype.card K:ℝ)^(finrank K E-T2x51 R i))
    (fun _ => by positivity) (orthogonalStep_card_bound ω hω R) n
  rw [Finset.prod_pow_eq_pow_sum] at hs
  have hh : (Nat.card (OrthogonalTuple ω R n):ℝ) ≤ Nat.card (ZeroValidSeq (OrthogonalStep ω R) n) := by
    exact_mod_cast Nat.card_le_card_of_injective _ (orthogonalTupleToSeq ω R n).injective
  exact hh.trans hs
end OrthogonalTuple
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
noncomputable def constraintPairCount (R : ℕ → ℕ → Prop) (n : ℕ) : ℕ := by
  classical
  exact ∑ j : Fin n, ∑ i : Fin n, if i.val<j.val ∧ R i.val j.val then 1 else 0
 theorem sum_priorConstraintCount (R : ℕ → ℕ → Prop) (n : ℕ) :
    (∑ i : Fin n, T2x51 R i.val)=constraintPairCount R n := by
  classical
  apply Finset.sum_congr rfl
  intro j _
  let e : {i : Fin j.val // R i.val j.val} ≃ {i : Fin n // i.val<j.val ∧ R i.val j.val} :=
    { toFun := fun i => ⟨⟨i.val.val,lt_trans (by simpa only [Nat.zero_add] using i.val.isLt) j.isLt⟩,by simpa only [Nat.zero_add] using i.val.isLt,i.property⟩
      invFun := fun i => ⟨⟨i.val.val,by simpa only [Nat.zero_add] using i.property.1⟩,i.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [T2x51,Nat.card_congr e,Nat.card_eq_fintype_card,Fintype.card_subtype]
  simp only [Finset.sum_boole,Nat.cast_id]
section TupleRpow
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
 theorem orthogonalTuple_card_rpow (hω : ω.Nondegenerate) (R : ℕ → ℕ → Prop) (n : ℕ)
    (hn : n≤finrank K E) :
    (Nat.card {x : Fin n → E // LinearIndependent K x ∧
      ∀ i j : Fin n, i.val<j.val → R i.val j.val → ω (x i) (x j)=0}:ℝ) ≤
      (Fintype.card K:ℝ)^((n:ℝ)*finrank K E-constraintPairCount R n) := by
  classical
  have hb := orthogonalTuple_card_bound ω hω R n
  have hle (i : Fin n) : T2x51 R i.val≤finrank K E := by
    have hh : Nat.card {j : Fin i.val // R j.val i.val} ≤ Nat.card (Fin i.val) :=
      Nat.card_le_card_of_injective _ Subtype.val_injective
    simp only [Nat.card_eq_fintype_card,Fintype.card_fin] at hh
    simpa only [T2x51,Nat.card_eq_fintype_card] using hh.trans (i.isLt.le.trans hn)
  have he : ((∑ i : Fin n, (finrank K E-T2x51 R i.val):ℕ):ℝ)=
      (n:ℝ)*finrank K E-constraintPairCount R n := by
    rw [Nat.cast_sum]
    simp only [Nat.cast_sub (hle _),Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,
      Fintype.card_fin,nsmul_eq_mul,←Nat.cast_sum,sum_priorConstraintCount]
  rw [←Real.rpow_natCast,he] at hb
  unfold OrthogonalTuple at hb
  exact hb
end TupleRpow
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
 theorem nat_card_subtype_sum {A : Type*} [Fintype A] (P : A → Prop) [DecidablePred P] :
    Nat.card {a : A // P a}=∑ a : A, if P a then (1:ℕ) else 0 := by
  classical
  simp only [Nat.card_eq_fintype_card,Fintype.card_subtype,Finset.sum_boole,Nat.cast_id]
 theorem double_constraintPairCount (R : ℕ → ℕ → Prop) (n : ℕ)
    (hR : ∀ i j, R i j → R j i) :
    2*constraintPairCount R n = Nat.card {p : Fin n × Fin n // p.1≠p.2 ∧ R p.1.val p.2.val} := by
  classical
  rw [nat_card_subtype_sum,Fintype.sum_prod_type]
  have he (i j : Fin n) :
      (if i≠j ∧ R i.val j.val then (1:ℕ) else 0)=
      (if i.val<j.val ∧ R i.val j.val then 1 else 0)+
      (if j.val < i.val ∧ R j.val i.val then 1 else 0) := by
    have hr : R i.val j.val ↔ R j.val i.val := ⟨hR _ _,hR _ _⟩
    rcases lt_trichotomy i.val j.val with h|h|h
    · have hne : i≠j := fun hh => by subst j; exact (lt_irrefl _ h)
      simp [hne,h,not_lt.mpr h.le]
    · have hij : i=j := Fin.ext h
      simp [hij]
    · have hne : i≠j := fun hh => by subst j; exact (lt_irrefl _ h)
      simp [hne,h,not_lt.mpr h.le,←hr]
  simp_rw [he,Finset.sum_add_distrib]
  rw [Finset.sum_comm (f:=fun i j : Fin n => if i.val<j.val ∧ R i.val j.val then (1:ℕ) else 0)]
  unfold constraintPairCount
  omega
section AbstractTuple
variable {K E A : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E] [Fintype A]
variable (ω : LinearMap.BilinForm K E)
abbrev ConstrainedTuple (R : A → A → Prop) :=
  {x : A → E // LinearIndependent K x ∧ ∀ a b, R a b → ω (x a) (x b)=0}
noncomputable def enumeratedRelation (R : A → A → Prop) (e : Fin (Fintype.card A) ≃ A) : ℕ → ℕ → Prop :=
  fun i j => ∃ (hi : i<Fintype.card A) (hj : j<Fintype.card A), R (e ⟨i,hi⟩) (e ⟨j,hj⟩)
 theorem enumeratedRelation_symm (R : A → A → Prop) (hR : ∀ a b, R a b → R b a)
    (e : Fin (Fintype.card A) ≃ A) (i j : ℕ) :
    enumeratedRelation R e i j → enumeratedRelation R e j i := by
  rintro ⟨hi,hj,h⟩
  exact ⟨hj,hi,hR _ _ h⟩
 theorem constrainedTuple_card_rpow (hω : ω.Nondegenerate) (R : A → A → Prop)
    (hR : ∀ a b, R a b → R b a) (hn : Fintype.card A≤finrank K E) :
    (Nat.card (ConstrainedTuple ω R):ℝ) ≤
      (Fintype.card K:ℝ)^((Fintype.card A:ℝ)*finrank K E-
        (Nat.card {p : A×A // p.1≠p.2 ∧ R p.1 p.2}:ℝ)/2) := by
  classical
  let e : Fin (Fintype.card A) ≃ A := (Fintype.equivFin A).symm
  let Q := enumeratedRelation R e
  have hb := orthogonalTuple_card_rpow ω hω Q (Fintype.card A) hn
  let f : ConstrainedTuple ω R →
      {x : Fin (Fintype.card A) → E // LinearIndependent K x ∧ ∀ i j, i.val<j.val → Q i.val j.val → ω (x i) (x j)=0} :=
    fun x => ⟨fun i=>x.val (e i),x.property.1.comp e e.injective,by
      intro i j _ hij
      obtain ⟨hi,hj,h⟩ := hij
      exact x.property.2 _ _ h⟩
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    funext a
    have hh := congrArg (fun z => z.val (e.symm a)) h
    simpa only [f,Equiv.apply_symm_apply] using hh
  have hc := Nat.card_le_card_of_injective f hf
  have he : {p : Fin (Fintype.card A) × Fin (Fintype.card A) // p.1≠p.2 ∧ Q p.1.val p.2.val} ≃
      {p : A×A // p.1≠p.2 ∧ R p.1 p.2} :=
    (e.prodCongr e).subtypeEquiv (by
      intro p
      change (p.1≠p.2 ∧ enumeratedRelation R e p.1.val p.2.val) ↔ (e p.1≠e p.2 ∧ R (e p.1) (e p.2))
      simp only [e.injective.ne_iff,enumeratedRelation]
      constructor
      · rintro ⟨hne,hi,hj,h⟩
        exact ⟨hne,h⟩
      · rintro ⟨hne,h⟩
        exact ⟨hne,p.1.isLt,p.2.isLt,h⟩)
  have hd := double_constraintPairCount Q (Fintype.card A) (enumeratedRelation_symm R hR e)
  rw [Nat.card_congr he] at hd
  have hd' : (constraintPairCount Q (Fintype.card A):ℝ)=
      (Nat.card {p : A×A // p.1≠p.2 ∧ R p.1 p.2}:ℝ)/2 := by
    have hdc : (2:ℝ)*constraintPairCount Q (Fintype.card A)=(Nat.card {p : A×A // p.1≠p.2 ∧ R p.1 p.2}:ℝ) := by exact_mod_cast hd
    linarith
  rw [hd'] at hb
  exact (by exact_mod_cast hc : (Nat.card (ConstrainedTuple ω R):ℝ)≤_).trans hb
end AbstractTuple
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section ResidualCount
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
 theorem independentTuples_card_lower (k : ℕ) (hE : finrank K E=k) :
    (Fintype.card K:ℝ)^(k*k) ≤ 2^k*(Nat.card (IndependentTuple K E k):ℝ) := by
  classical
  have hq : (2:ℝ)≤Fintype.card K := by exact_mod_cast (Fintype.one_lt_card (α:=K))
  have hq0 : (0:ℝ)<Fintype.card K := by linarith
  have hle (i : Fin k) : Fintype.card K ^ i.val ≤ Fintype.card K ^ k :=
    Nat.pow_le_pow_right Fintype.card_pos i.isLt.le
  have hp (i : Fin k) : (Fintype.card K:ℝ)^k ≤
      2*((Fintype.card K:ℝ)^k-(Fintype.card K:ℝ)^i.val) := by
    have h₁ : 2*(Fintype.card K:ℝ)^i.val ≤ (Fintype.card K:ℝ)^(i.val+1) := by
      rw [pow_succ]
      nlinarith [pow_nonneg hq0.le i.val]
    have h₂ : (Fintype.card K:ℝ)^(i.val+1) ≤ (Fintype.card K:ℝ)^k :=
      pow_le_pow_right₀ (by linarith) i.isLt
    linarith
  have h := Finset.prod_le_prod (s:=Finset.univ) (fun _i : Fin k => fun _ => pow_nonneg hq0.le k)
    (fun i _ => hp i)
  rw [IndependentTuple,card_linearIndependent (by omega),hE,Nat.cast_prod]
  simp only [Nat.cast_sub (hle _),Nat.cast_pow]
  simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,←pow_mul,Finset.prod_mul_distrib] using h
variable (ω : LinearMap.BilinForm K E)
 theorem containingLagrangian_card_rpow (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D=finrank K E) (S : Submodule K E) :
    (Nat.card {L : T2x0 ω // S≤L.val}:ℝ) ≤
      T2x1 D * (Nat.card (T2x0 ω):ℝ) *
        (Fintype.card K:ℝ)^(-(D:ℝ)*finrank K S+(finrank K S:ℝ)*(finrank K S-1)/2) := by
  classical
  have hq : 0<(Fintype.card K:ℝ) := by exact_mod_cast Fintype.card_pos (α:=K)
  by_cases his : S≤ω.orthogonal S
  · have hs := T2x16 ω hω D hD S his
    have h := (T2x76 ω h2 ha hω D hD S his).2
    have hl := (T2x18 ω h2 ha hω D hD).1
    have hC := lagrangianConstant_mono (Nat.sub_le D (finrank K S))
    have he : (((D-finrank K S+1).choose 2:ℕ):ℝ) =
        ((D+1).choose 2:ℕ) + (-(D:ℝ)*finrank K S+(finrank K S:ℝ)*(finrank K S-1)/2) := by
      rw [Nat.cast_choose_two,Nat.cast_choose_two]
      simp only [Nat.cast_add,Nat.cast_one,Nat.cast_sub hs]
      ring
    rw [←Real.rpow_natCast,he,Real.rpow_add hq] at h
    calc
      _ ≤ _ := h
      _ ≤ _ := by
        rw [Real.rpow_natCast,←mul_assoc]
        exact mul_le_mul_of_nonneg_right (mul_le_mul hC hl (by positivity) (T2x10 D).le) (Real.rpow_nonneg hq.le _)
  · have hz : Nat.card {L : T2x0 ω // S≤L.val}=0 := by
      let : IsEmpty {L : T2x0 ω // S≤L.val} := ⟨fun L => his (by
        calc
          S ≤ L.val.val := L.property
          _ = ω.orthogonal L.val.val := L.val.property.symm
          _ ≤ ω.orthogonal S := ω.orthogonal_le L.property)⟩
      exact Nat.card_eq_zero.mpr (Or.inl inferInstance)
    rw [hz,Nat.cast_zero]
    exact mul_nonneg (mul_nonneg (T2x10 D).le (Nat.cast_nonneg _)) (Real.rpow_nonneg hq.le _)
end ResidualCount
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section FamilySpan
variable {K E I : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype I]
variable [Finite E]
abbrev FamilySpanStratum (h : I → ℕ) (k : ℕ) :=
  {A : (i : I) → DimSubspace K E (h i) // finrank K ↥(⨆ i, (A i).val)=k}
noncomputable def familySpanCoding (h : I → ℕ) (k : ℕ) (A : FamilySpanStratum (K:=K) (E:=E) h k) :
    Σ W : DimSubspace K E k, (i : I) → DimSubspace K W.val (h i) :=
  ⟨⟨⨆ i, (A.val i).val,A.property⟩,fun i => restrictDimSubspace (⨆ i, (A.val i).val)
    (A.val i) (le_iSup (fun i => (A.val i).val) i)⟩
omit [Fintype I] [Finite E] in
 theorem familySpanCoding_injective (h : I → ℕ) (k : ℕ) :
    Function.Injective (familySpanCoding (K:=K) (E:=E) h k) := by
  let recover : (Σ W : DimSubspace K E k, (i : I) → DimSubspace K W.val (h i)) → (I → Submodule K E) :=
    fun x i => (x.2 i).val.map x.1.val.subtype
  have he (A : FamilySpanStratum (K:=K) (E:=E) h k) : recover (familySpanCoding h k A)=fun i => (A.val i).val := by
    funext i
    change ((A.val i).val.comap (⨆ j, (A.val j).val).subtype).map (⨆ j, (A.val j).val).subtype = _
    rw [Submodule.map_comap_subtype]
    exact inf_eq_right.mpr (le_iSup (fun j => (A.val j).val) i)
  intro A B hAB
  have hh := congrArg recover hAB
  rw [he,he] at hh
  apply Subtype.ext
  funext i
  exact Subtype.ext (congrFun hh i)
variable [Fintype K]
 theorem familySpan_card_upper (h : I → ℕ) (k : ℕ) (hk : k≤finrank K E) (hh : ∀ i, h i≤k) :
    (Nat.card (FamilySpanStratum (K:=K) (E:=E) h k):ℝ) ≤
      2^(k+∑ i, h i)*(Fintype.card K:ℝ)^(k*(finrank K E-k)+∑ i, h i*(k-h i)) := by
  classical
  let := Fintype.ofFinite (DimSubspace K E k)
  have hf (W : DimSubspace K E k) :
      (Nat.card ((i : I) → DimSubspace K W.val (h i)):ℝ) ≤
      (2:ℝ)^(∑ i, h i)*(Fintype.card K:ℝ)^(∑ i, h i*(k-h i)) := by
    rw [Nat.card_pi,Nat.cast_prod]
    have hh' (i : I) := T2x26 (K:=K) (V:=W.val) (h i) (by rw [W.property];exact hh i)
    simp only [W.property] at hh'
    have hp := Finset.prod_le_prod (s:=Finset.univ) (fun i _ => Nat.cast_nonneg (Nat.card (DimSubspace K W.val (h i)))) (fun i _ => hh' i)
    simpa only [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum] using hp
  have hs := real_card_sigma_le (B:=DimSubspace K E k) _ hf
  have hi : (Nat.card (FamilySpanStratum (K:=K) (E:=E) h k):ℝ) ≤
      Nat.card (Σ W : DimSubspace K E k, (i : I) → DimSubspace K W.val (h i)) := by
    exact_mod_cast Nat.card_le_card_of_injective _ (familySpanCoding_injective (K:=K) (E:=E) h k)
  calc
    _ ≤ _ := hi.trans hs
    _ ≤ (2^k*(Fintype.card K:ℝ)^(k*(finrank K E-k))) *
        (2^(∑ i, h i)*(Fintype.card K:ℝ)^(∑ i, h i*(k-h i))) :=
      mul_le_mul_of_nonneg_right (T2x26 k hk) (by positivity)
    _ = _ := by rw [pow_add,pow_add];ring
end FamilySpan
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section DirectFamilies
variable {K E I : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype I]
variable [Finite E]
variable (ω : LinearMap.BilinForm K E)
abbrev DirectFamily (h : I → ℕ) (R : I → I → Prop) :=
  {A : (i : I) → DimSubspace K E (h i) // iSupIndep (fun i => (A i).val) ∧
    ∀ i j, R i j → ∀ x∈(A i).val, ∀ y∈(A j).val, ω x y=0}
abbrev FamilyBases {h : I → ℕ} {R : I → I → Prop} (A : DirectFamily ω h R) :=
  (i : I) → IndependentTuple K (A.val i).val (h i)
omit [Fintype I] in
 theorem directFamilyBases_independent {h : I → ℕ} {R : I → I → Prop}
    (A : DirectFamily ω h R) (b : FamilyBases ω A) :
    LinearIndependent K (fun x : Σ i, Fin (h i) => (((b x.1).val x.2 : (A.val x.1).val):E)) := by
  classical
  apply linearIndependent_iUnion_finite (f := fun (i : I) (a : Fin (h i)) => ((b i).val a:E))
  · intro i
    exact (b i).property.map' (A.val i).val.subtype (Submodule.ker_subtype _)
  · intro i t _ hi
    have he (j : I) : Submodule.span K (Set.range (fun a => (((b j).val a : (A.val j).val):E)))=(A.val j).val :=
      tuple_spans (h j) (A.val j) (b j)
    simp_rw [he]
    exact A.property.1.disjoint_biSup hi
noncomputable def directBasisForget (h : I → ℕ) (R : I → I → Prop)
    (x : Σ A : DirectFamily ω h R, FamilyBases ω A) :
    ConstrainedTuple ω (fun a b : Σ i, Fin (h i) => R a.1 b.1) :=
  ⟨fun a => ((x.2 a.1).val a.2:E),directFamilyBases_independent ω x.1 x.2,
    fun a b hr => x.1.property.2 a.1 b.1 hr _ ((x.2 a.1).val a.2).property _ ((x.2 b.1).val b.2).property⟩
omit [Fintype I] in
 theorem directBasisForget_injective (h : I → ℕ) (R : I → I → Prop) :
    Function.Injective (directBasisForget ω h R) := by
  rintro ⟨A,s⟩ ⟨B,t⟩ hh
  have hv (i : I) (a : Fin (h i)) : ((s i).val a:E)=((t i).val a:E) :=
    congrArg (fun x : ConstrainedTuple ω (fun a b : Σ i, Fin (h i) => R a.1 b.1) => x.val ⟨i,a⟩) hh
  have hAB : A=B := by
    apply Subtype.ext
    funext i
    apply Subtype.ext
    rw [←tuple_spans (h i) (A.val i) (s i),←tuple_spans (h i) (B.val i) (t i)]
    congr 2
    exact funext (hv i)
  subst B
  congr 1
  funext i
  apply Subtype.ext
  funext a
  exact Subtype.ext (hv i a)
variable [Fintype K]
 theorem familyBases_card_lower {h : I → ℕ} {R : I → I → Prop} (A : DirectFamily ω h R) :
    (Fintype.card K:ℝ)^(∑ i, h i*h i) ≤ 2^(∑ i, h i)*(Nat.card (FamilyBases ω A):ℝ) := by
  classical
  have hp := Finset.prod_le_prod (s:=Finset.univ)
    (fun i _ => pow_nonneg (Nat.cast_nonneg (Fintype.card K)) (h i*h i))
    (fun i _ => independentTuples_card_lower (E:=(A.val i).val) (h i) (A.val i).property)
  rw [FamilyBases,Nat.card_pi,Nat.cast_prod]
  simpa only [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum] using hp
 theorem directFamily_card_bound (hω : ω.Nondegenerate) (h : I → ℕ) (R : I → I → Prop)
    (hR : ∀ i j, R i j → R j i) (hn : (∑ i, h i)≤finrank K E) :
    (Nat.card (DirectFamily ω h R):ℝ) ≤ 2^(∑ i,h i)*
      (Fintype.card K:ℝ)^((finrank K E:ℝ)*(∑ i, h i)-
        (Nat.card {p : (Σ i, Fin (h i))×(Σ i, Fin (h i)) // p.1≠p.2 ∧ R p.1.1 p.2.1}:ℝ)/2-
        ∑ i, (h i:ℝ)^2) := by
  classical
  let := Fintype.ofFinite (DirectFamily ω h R)
  have hq : 0<(Fintype.card K:ℝ) := by exact_mod_cast Fintype.card_pos (α:=K)
  have hb := constrainedTuple_card_rpow ω hω (fun a b : Σ i, Fin (h i) => R a.1 b.1)
    (fun a b hr => hR _ _ hr) (by simpa only [Fintype.card_sigma,Fintype.card_fin] using hn)
  have hf : (Nat.card (Σ A : DirectFamily ω h R, FamilyBases ω A):ℝ) ≤
      Nat.card (ConstrainedTuple ω (fun a b : Σ i, Fin (h i) => R a.1 b.1)) := by
    exact_mod_cast Nat.card_le_card_of_injective _ (directBasisForget_injective ω h R)
  have hl : (Nat.card (DirectFamily ω h R):ℝ)*(Fintype.card K:ℝ)^(∑ i, h i*h i) ≤
      2^(∑ i, h i)*(Nat.card (Σ A : DirectFamily ω h R, FamilyBases ω A):ℝ) := by
    rw [Nat.card_sigma,Nat.cast_sum,Finset.mul_sum]
    calc
      _ = ∑ _A : DirectFamily ω h R, (Fintype.card K:ℝ)^(∑ i, h i*h i) := by
        simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card]
      _ ≤ _ := Finset.sum_le_sum (fun A _ => familyBases_card_lower ω A)
  have hm := hl.trans (mul_le_mul_of_nonneg_left (hf.trans hb) (by positivity : (0:ℝ)≤2^(∑ i,h i)))
  have he : ((∑ i, h i*h i:ℕ):ℝ)=∑ i, (h i:ℝ)^2 := by simp only [Nat.cast_sum,Nat.cast_mul,pow_two]
  rw [←Real.rpow_natCast,he] at hm
  have hsum : (Fintype.card (Σ i, Fin (h i)):ℝ)=∑ i, (h i:ℝ) := by simp only [Fintype.card_sigma,Fintype.card_fin,Nat.cast_sum]
  rw [hsum] at hm
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hq _)).mpr at hm
  rw [mul_div_assoc,←Real.rpow_sub hq] at hm
  simpa only [Nat.cast_sum,mul_comm (∑ i, (h i:ℝ)) (finrank K E:ℝ)] using hm
end DirectFamilies
end SidorenkoCounterexample
end OAI
namespace OAI
namespace SidorenkoCounterexample
open Module
section Span
variable {K V P : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype P] [DecidableEq P]
def localSpan (s : Finset (Finset P)) (H : Finset P → Submodule K V) (i : P) :
    Submodule K V := (s.filter fun e => i ∈ e).sup H
omit [FiniteDimensional K V] [Fintype P] in
private theorem localSpan_le (s : Finset (Finset P)) (H : Finset P → Submodule K V)
    (i : P) : localSpan s H i ≤ s.sup H :=
  Finset.sup_mono (Finset.filter_subset _ _)
omit [FiniteDimensional K V] [Fintype P] in
private theorem localSpan_insert (s : Finset (Finset P)) (e : Finset P)
    (H : Finset P → Submodule K V) (i : P) :
    localSpan (insert e s) H i = if i ∈ e then H e ⊔ localSpan s H i
      else localSpan s H i := by
  classical
  simp only [localSpan, Finset.filter_insert]
  split_ifs <;> simp
private theorem local_rank_insert (s : Finset (Finset P)) (e : Finset P)
    (H : Finset P → Submodule K V) :
    (∑ i, finrank K (localSpan (insert e s) H i)) +
      (∑ i ∈ e, finrank K (H e ⊓ localSpan s H i : Submodule K V)) =
    (∑ i, finrank K (localSpan s H i)) + e.card * finrank K (H e) := by
  classical
  have heq (i : P) : finrank K (localSpan (insert e s) H i) +
      (if i ∈ e then finrank K (H e ⊓ localSpan s H i : Submodule K V) else 0) =
      finrank K (localSpan s H i) + (if i ∈ e then finrank K (H e) else 0) := by
    by_cases hi : i ∈ e
    · rw [localSpan_insert, if_pos hi, if_pos hi, if_pos hi]
      exact (Submodule.finrank_sup_add_finrank_inf_eq (H e) (localSpan s H i)).trans (Nat.add_comm _ _)
    · rw [localSpan_insert, if_neg hi, if_neg hi, if_neg hi]
  have h := congrArg (fun f : P → ℕ => ∑ i, f i) (funext heq)
  simpa only [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.sum_const,
    smul_eq_mul, Finset.univ_inter] using h
theorem span_inequality_with_rigidity (s : Finset (Finset P))
    (H : Finset P → Submodule K V) (hs : ∀ e ∈ s, e.card = 2) :
    2 * finrank K (s.sup H : Submodule K V) ≤ ∑ i, finrank K (localSpan s H i) ∧
    ((∑ i, finrank K (localSpan s H i)) = 2 * finrank K (s.sup H : Submodule K V) →
      s.SupIndep H) := by
  classical
  induction s using Finset.induction with
  | empty =>
    rw [Finset.sup_empty]
    constructor
    · simp
    · intro _
      exact Finset.supIndep_empty H
  | @insert e s he ih =>
    have hse : ∀ f ∈ s, f.card = 2 := fun f hf => hs f (Finset.mem_insert_of_mem hf)
    obtain ⟨hbound, hrigid⟩ := ih hse
    have hecard := hs e (Finset.mem_insert_self _ _)
    obtain ⟨a, b, hab, heab⟩ := Finset.card_eq_two.mp hecard
    have hr := local_rank_insert s e H
    rw [hecard, heab] at hr
    simp only [Finset.sum_pair hab] at hr
    rw [← heab] at hr
    have hg := Submodule.finrank_sup_add_finrank_inf_eq (H e) (s.sup H)
    have hda := Submodule.finrank_mono
      (inf_le_inf_left (H e) (localSpan_le s H a))
    have hdb := Submodule.finrank_mono
      (inf_le_inf_left (H e) (localSpan_le s H b))
    rw [Finset.sup_insert]
    constructor
    · omega
    · intro heq
      have hold : (∑ i, finrank K (localSpan s H i)) = 2 * finrank K (s.sup H : Submodule K V) := by omega
      have hA : finrank K (H e ⊓ localSpan s H a : Submodule K V) =
          finrank K (H e ⊓ s.sup H : Submodule K V) := by omega
      have hB : finrank K (H e ⊓ localSpan s H b : Submodule K V) =
          finrank K (H e ⊓ s.sup H : Submodule K V) := by omega
      have hind := hrigid hold
      have hfilters : Disjoint (s.filter fun f => a ∈ f) (s.filter fun f => b ∈ f) := by
        rw [Finset.disjoint_left]
        intro f hfa hfb
        obtain ⟨hf, haf⟩ := Finset.mem_filter.mp hfa
        have hbf := (Finset.mem_filter.mp hfb).2
        have hef : e ⊆ f := by
          rw [heab]
          intro x hx
          rcases Finset.mem_insert.mp hx with hxa | hxb
          · exact hxa ▸ haf
          · exact (Finset.mem_singleton.mp hxb) ▸ hbf
        have heqf : e = f := Finset.eq_of_subset_of_card_le hef (by rw [hse f hf, hecard])
        exact he (heqf.symm ▸ hf)
      have hdis : Disjoint (localSpan s H a) (localSpan s H b) :=
        hind.disjoint_sup_sup (Finset.filter_subset _ _) (Finset.filter_subset _ _) hfilters
      have hAe := Submodule.eq_of_le_of_finrank_eq
        (inf_le_inf_left (H e) (localSpan_le s H a)) hA
      have hBe := Submodule.eq_of_le_of_finrank_eq
        (inf_le_inf_left (H e) (localSpan_le s H b)) hB
      have hnew : Disjoint (H e) (s.sup H) := by
        rw [disjoint_iff_inf_le]
        calc
          H e ⊓ s.sup H ≤ localSpan s H a ⊓ localSpan s H b := by
            exact le_inf (hAe ▸ inf_le_right) (hBe ▸ inf_le_right)
          _ ≤ ⊥ := hdis.le_bot
      exact hind.insert hnew
theorem strict_span_inequality (s : Finset (Finset P)) (H : Finset P → Submodule K V)
    (hs : ∀ e ∈ s, e.card = 2) (hn : ¬s.SupIndep H) :
    2 * finrank K (s.sup H : Submodule K V) + 1 ≤ ∑ i, finrank K (localSpan s H i) := by
  obtain ⟨hb, hr⟩ := span_inequality_with_rigidity s H hs
  have hne : (∑ i, finrank K (localSpan s H i)) ≠ 2 * finrank K (s.sup H : Submodule K V) :=
    fun h => hn (hr h)
  omega
end Span
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section FiniteSpans
variable {K E I : Type*} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]
 theorem finrank_finset_sup_le (s : Finset I) (A : I → Submodule K E) :
    finrank K ↥(s.sup A) ≤ ∑ i∈s, finrank K (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sup_insert,Finset.sum_insert hi]
    have := Submodule.finrank_sup_add_finrank_inf_eq (A i) (s.sup A)
    omega
 theorem finrank_finite_iSup_le [Fintype I] (A : I → Submodule K E) :
    finrank K ↥(⨆ i,A i) ≤ ∑ i, finrank K (A i) := by
  have hh := finrank_finset_sup_le Finset.univ A
  exact (le_of_eq (congrArg (fun S : Submodule K E=>finrank K S)
    (Finset.sup_univ_eq_iSup A).symm)).trans hh
 theorem finrank_finset_sup_direct (s : Finset I) (A : I → Submodule K E)
    (ha : iSupIndep A) : finrank K ↥(s.sup A) = ∑ i∈s, finrank K (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hd : Disjoint (A i) (s.sup A) := by
      rw [Finset.sup_eq_iSup]
      exact ha.disjoint_biSup hi
    have hh := Submodule.finrank_sup_add_finrank_inf_eq (A i) (s.sup A)
    rw [hd.eq_bot,finrank_bot,add_zero] at hh
    rw [Finset.sup_insert,Finset.sum_insert hi,hh,ih]
end FiniteSpans
def T2x17 (i : Fin 13) : Finset (Fin 33) := Finset.univ.filter (fun e => i∈T2x12 e)
def pairRelated (e f : Fin 33) : Prop := ¬Disjoint (T2x12 e) (T2x12 f)
instance (e f : Fin 33) : Decidable (pairRelated e f) := inferInstanceAs (Decidable (¬Disjoint _ _))
 theorem pairRelated_symm (e f : Fin 33) : pairRelated e f → pairRelated f e := by
  unfold pairRelated; intro h hf; exact h hf.symm
 theorem incidentPairs_card_le : ∀ i, (T2x17 i).card≤6 := by decide
 theorem pair_shared_card : ∀ e f, (Finset.univ.filter (fun i => e∈T2x17 i ∧ f∈T2x17 i)).card =
    if e=f then 2 else if pairRelated e f then 1 else 0 := by decide
 theorem sum_incident (f : Fin 33 → ℝ) :
    (∑ i : Fin 13, ∑ e∈T2x17 i, f e)=2*∑ e,f e := by
  simp only [T2x17,Finset.sum_filter]
  rw [Finset.sum_comm]
  have hh (e : Fin 33) : (∑ i : Fin 13, if i∈T2x12 e then f e else 0)=2*f e := by
    rw [←Finset.sum_filter,Finset.sum_const]
    have hc : (Finset.univ.filter (fun i=>i∈T2x12 e)).card=2 := by
      have he : Finset.univ.filter (fun i=>i∈T2x12 e)=T2x12 e := by ext i; simp
      rw [he,pairVertices_card]
    rw [hc]; simp only [nsmul_eq_mul,Nat.cast_ofNat]
  simp_rw [hh]
  rw [Finset.mul_sum]
noncomputable def T2x41 (h : Fin 33 → ℕ) (i : Fin 13) : ℕ := ∑ e∈T2x17 i,h e
 theorem localPairDim_le (h : Fin 33 → ℕ) (hh : ∀ e,h e≤2) (i : Fin 13) : T2x41 h i≤2*(T2x17 i).card := by
  unfold T2x41
  calc _ ≤ ∑ _e∈T2x17 i, 2 := Finset.sum_le_sum (fun e _=>hh e)
       _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul,Nat.cast_id]; omega
 theorem localPairDim_le_twelve (h : Fin 33 → ℕ) (hh : ∀ e,h e≤2) (i : Fin 13) : T2x41 h i≤12 := by
  have := localPairDim_le h hh i
  have := incidentPairs_card_le i
  omega
section GraphSpans
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
noncomputable def T2x55 (A : Fin 33 → Submodule K E) (i : Fin 13) : Submodule K E :=
  (T2x17 i).sup A
 theorem incidentSpan_le {A : Fin 33 → Submodule K E} {i : Fin 13} {L : Submodule K E}
    (h : ∀ e, i∈T2x12 e → A e≤L) : T2x55 A i≤L := by
  apply Finset.sup_le
  intro e he
  exact h e (Finset.mem_filter.mp he).2
variable [FiniteDimensional K E]
 theorem incidentSpan_finrank_le (h : Fin 33 → ℕ) (A : (e : Fin 33) → DimSubspace K E (h e)) (i : Fin 13) :
    finrank K (T2x55 (fun e=>(A e).val) i)≤T2x41 h i := by
  unfold T2x55 T2x41
  calc _ ≤ ∑ e∈T2x17 i, finrank K (A e).val := finrank_finset_sup_le _ _
       _ = _ := Finset.sum_congr rfl (fun e _ => (A e).property)
 theorem incidentSpan_finrank_direct (h : Fin 33 → ℕ) (A : (e : Fin 33) → DimSubspace K E (h e))
    (ha : iSupIndep (fun e=>(A e).val)) (i : Fin 13) :
    finrank K (T2x55 (fun e=>(A e).val) i)=T2x41 h i := by
  unfold T2x55 T2x41
  calc _ = ∑ e∈T2x17 i, finrank K (A e).val := finrank_finset_sup_direct _ _ ha
       _ = _ := Finset.sum_congr rfl (fun e _ => (A e).property)
noncomputable def extendPairSpace (A : Fin 33 → Submodule K E) : Finset (Fin 13) → Submodule K E :=
  Function.extend T2x12 A (fun _=>⊥)
omit [FiniteDimensional K E] in
 theorem extendPairSpace_apply (A : Fin 33 → Submodule K E) (e : Fin 33) :
    extendPairSpace A (T2x12 e)=A e := pairVertices_injective.extend_apply _ _ _
omit [FiniteDimensional K E] in
 theorem extend_global_span (A : Fin 33 → Submodule K E) :
    (Finset.univ.image T2x12).sup (extendPairSpace A)=⨆ e,A e := by
  rw [Finset.sup_image]
  simp only [Function.comp_def,extendPairSpace_apply,Finset.sup_eq_iSup,Finset.mem_univ,iSup_pos]
omit [FiniteDimensional K E] in
 theorem extend_local_span (A : Fin 33 → Submodule K E) (i : Fin 13) :
    localSpan (Finset.univ.image T2x12) (extendPairSpace A) i=T2x55 A i := by
  unfold localSpan T2x55 T2x17
  rw [Finset.filter_image,Finset.sup_image]
  simp only [Function.comp_def,extendPairSpace_apply]
 theorem indexed_strict_span (A : Fin 33 → Submodule K E) (ha : ¬iSupIndep A) :
    2*finrank K ↥(⨆ e,A e)+1≤∑ i,finrank K (T2x55 A i) := by
  have hn : ¬(Finset.univ.image T2x12).SupIndep (extendPairSpace A) := by
    intro hs
    have hi := hs.independent
    have hj := hi.comp (f := fun e : Fin 33 => (⟨T2x12 e,Finset.mem_image.mpr ⟨e,Finset.mem_univ _,rfl⟩⟩ : ↥(Finset.univ.image T2x12))) (by
      intro e f hef
      exact pairVertices_injective (congrArg Subtype.val hef))
    apply ha
    simpa only [Function.comp_def,extendPairSpace_apply] using hj
  have hb := strict_span_inequality (Finset.univ.image T2x12) (extendPairSpace A)
    (by intro e he; obtain ⟨f,_,rfl⟩:=Finset.mem_image.mp he; exact pairVertices_card f) hn
  rw [extend_global_span] at hb
  have hs : (∑ i : Fin 13,finrank K (localSpan (Finset.univ.image T2x12) (extendPairSpace A) i))=∑ i,finrank K (T2x55 A i) :=
    Finset.sum_congr rfl (fun i _ => congrArg (fun S : Submodule K E => finrank K S) (extend_local_span A i))
  rw [hs] at hb
  exact hb
end GraphSpans
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open scoped BigOperators
 theorem pairRelated_self (e : Fin 33) : pairRelated e e := by
  intro he
  have hb := disjoint_self.mp he
  have hc := pairVertices_card e
  rw [hb] at hc
  simp at hc
 theorem related_label_count (h : Fin 33 → ℕ) :
    (Nat.card {p : (Σ e, Fin (h e))×(Σ e, Fin (h e)) // p.1≠p.2 ∧ pairRelated p.1.1 p.2.1}:ℝ)=
      (∑ e, ∑ f, if pairRelated e f then (h e:ℝ)*h f else 0)-∑ e,(h e:ℝ) := by
  classical
  rw [nat_card_subtype_sum,Nat.cast_sum,Fintype.sum_prod_type]
  have he (a b : Σ e, Fin (h e)) :
      (if a≠b ∧ pairRelated a.1 b.1 then (1:ℝ) else 0)=
        (if pairRelated a.1 b.1 then (1:ℝ) else 0)-(if a=b then 1 else 0) := by
    by_cases hab : a=b
    · subst b; simp [pairRelated_self]
    · by_cases hr : pairRelated a.1 b.1 <;> simp [hab,hr]
  simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  simp only [he,Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true,Finset.sum_const,Finset.card_univ,
    nsmul_eq_mul,mul_one,Fintype.card_sigma,Fintype.card_fin,Nat.cast_sum]
  congr 1
  simp_rw [Fintype.sum_sigma]
  simp [Finset.sum_const,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro f _
  by_cases hr : pairRelated e f <;> simp [hr]
 theorem sum_local_products (f g : Fin 33 → ℝ) :
    (∑ i : Fin 13, (∑ e∈T2x17 i,f e)*(∑ e∈T2x17 i,g e))=
      ∑ e,∑ a, ((Finset.univ.filter (fun i=>e∈T2x17 i ∧ a∈T2x17 i)).card:ℝ)*f e*g a := by
  classical
  have hf (i : Fin 13) : (∑ e∈T2x17 i,∑ a∈T2x17 i,f e*g a)=
      ∑ e : Fin 33,∑ a : Fin 33, if e∈T2x17 i ∧ a∈T2x17 i then f e*g a else 0 := by
    symm
    simp only [ite_and]
    simp_rw [Finset.sum_ite_irrel,Finset.sum_ite_mem]
    simp only [Finset.sum_const_zero, Finset.sum_ite_mem, Finset.univ_inter]
  have hp (i : Fin 13) : (∑ e∈T2x17 i,f e)*(∑ e∈T2x17 i,g e)=
      ∑ e∈T2x17 i,∑ a∈T2x17 i,f e*g a := by
    rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum]
  simp_rw [hp,hf]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [←Finset.sum_filter,Finset.sum_const]
  simp only [nsmul_eq_mul,mul_assoc]
 theorem sum_local_squares (h : Fin 33 → ℕ) :
    (∑ i : Fin 13,(T2x41 h i:ℝ)^2)=
      (∑ e,(h e:ℝ)^2)+(∑ e,∑ f,if pairRelated e f then (h e:ℝ)*h f else 0) := by
  classical
  have he : (∑ i : Fin 13,(T2x41 h i:ℝ)^2)=
      ∑ i : Fin 13,(∑ e∈T2x17 i,(h e:ℝ))*(∑ e∈T2x17 i,(h e:ℝ)) := by
    simp only [T2x41,Nat.cast_sum,pow_two]
  rw [he,sum_local_products]
  have hp (e f : Fin 33) :
      ((Finset.univ.filter (fun i=>e∈T2x17 i ∧ f∈T2x17 i)).card:ℝ)*(h e:ℝ)*h f=
      (if e=f then (h e:ℝ)^2 else 0)+(if pairRelated e f then (h e:ℝ)*h f else 0) := by
    rw [pair_shared_card]
    by_cases hef : e=f
    · subst f; simp only [ite_true,pairRelated_self,Nat.cast_ofNat,pow_two]; ring
    · by_cases hr : pairRelated e f <;> simp [hef,hr]
  simp_rw [hp,Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]
 theorem sum_localPairDim (h : Fin 33 → ℕ) : (∑ i,(T2x41 h i:ℝ))=2*∑ e,(h e:ℝ) := by
  simpa only [T2x41,Nat.cast_sum] using sum_incident (fun e=>(h e:ℝ))
 theorem residual_direct_exponent (D : ℕ) (h : Fin 33 → ℕ) :
    2*(D:ℝ)*(∑ e,(h e:ℝ))-
      (Nat.card {p : (Σ e, Fin (h e))×(Σ e, Fin (h e)) // p.1≠p.2 ∧ pairRelated p.1.1 p.2.1}:ℝ)/2-
      (∑ e,(h e:ℝ)^2)+(∑ i : Fin 13, (-(D:ℝ)*T2x41 h i+(T2x41 h i:ℝ)*(T2x41 h i-1)/2))=
      -∑ e,triangular (h e) := by
  rw [related_label_count]
  have hl : (∑ i : Fin 13, (-(D:ℝ)*T2x41 h i+(T2x41 h i:ℝ)*(T2x41 h i-1)/2))=
      -(D:ℝ)*(∑ i,(T2x41 h i:ℝ))+((∑ i,(T2x41 h i:ℝ)^2)-(∑ i,(T2x41 h i:ℝ)))/2 := by
    simp only [mul_sub,mul_one,sub_div,←pow_two]
    simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.sum_div,Finset.mul_sum]
  rw [hl,sum_localPairDim,sum_local_squares]
  have ht : (∑ e,triangular (h e))=((∑ e,(h e:ℝ)^2)+(∑ e,(h e:ℝ)))/2 := by
    unfold triangular
    simp only [mul_add,mul_one,←pow_two]
    rw [←Finset.sum_div,Finset.sum_add_distrib]
  rw [ht]
  ring
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open scoped BigOperators
 theorem degree_choose_sum : (∑ i : Fin 13,(2*(T2x17 i).card).choose 2)=618 := by decide
 theorem local_choose_sum_bound (ki : Fin 13 → ℕ) (hk : ∀ i,ki i≤2*(T2x17 i).card) :
    (∑ i : Fin 13, (ki i:ℝ)*(ki i-1)/2)≤618 := by
  have hb : (∑ i : Fin 13,(ki i).choose 2)≤618 := by
    rw [←degree_choose_sum]
    exact Finset.sum_le_sum (fun i _=>Nat.choose_le_choose 2 (hk i))
  have hc : (∑ i : Fin 13, ((ki i).choose 2:ℝ))≤618 := by exact_mod_cast hb
  simpa only [Nat.cast_choose_two] using hc
 theorem residual_nondirect_exponent (D k : ℕ) (h : Fin 33 → ℕ) (ki : Fin 13 → ℕ)
    (hh : ∀ e,h e=0 ∨ h e=2) (hk : ∀ i,ki i≤2*(T2x17 i).card)
    (hs : 2*k+1≤∑ i,ki i) :
    (k:ℝ)*(2*D-k)+(∑ e,(h e:ℝ)*(k-h e))+
      (∑ i : Fin 13, (-(D:ℝ)*ki i+(ki i:ℝ)*(ki i-1)/2))≤-(D:ℝ)+1575 := by
  have hsq (e : Fin 33) : (h e:ℝ)^2=2*(h e:ℝ) := by rcases hh e with he|he <;> rw [he] <;> norm_num
  have hle (e : Fin 33) : (h e:ℝ)≤2 := by rcases hh e with he|he <;> rw [he] <;> norm_num
  have hb : (∑ e,(h e:ℝ))≤66 := by
    calc _ ≤ ∑ _e : Fin 33,(2:ℝ) := Finset.sum_le_sum (fun e _=>hle e)
         _ = _ := by norm_num
  have hn : 0≤∑ e,(h e:ℝ) := Finset.sum_nonneg (fun _ _=>Nat.cast_nonneg _)
  have hs' : 2*(k:ℝ)+1≤∑ i,(ki i:ℝ) := by exact_mod_cast hs
  have hc := local_choose_sum_bound ki hk
  have hh' : (∑ e,(h e:ℝ)*(k-h e))=(k:ℝ)*(∑ e,(h e:ℝ))-2*(∑ e,(h e:ℝ)) := by
    simp_rw [mul_sub,←pow_two,hsq]
    rw [Finset.sum_sub_distrib,←Finset.sum_mul,←Finset.mul_sum]
    ring
  have hg : (∑ i : Fin 13, (-(D:ℝ)*ki i+(ki i:ℝ)*(ki i-1)/2))=
      -(D:ℝ)*(∑ i,(ki i:ℝ))+(∑ i : Fin 13,(ki i:ℝ)*(ki i-1)/2) := by
    rw [Finset.sum_add_distrib,←Finset.mul_sum]
  rw [hh',hg]
  have hd := mul_nonneg (Nat.cast_nonneg D) (sub_nonneg.mpr hs')
  have hm := mul_nonneg hn (sub_nonneg.mpr hb)
  nlinarith [sq_nonneg ((k:ℝ)-(∑ e,(h e:ℝ))/2)]
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section Containment
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E)
noncomputable def pairSpaces (L : Fin 13 → T2x0 ω) (e : Fin 33) : Submodule K E :=
  (T2x12 e).inf (fun i=>(L i).val)
 theorem pairSpaces_le (L : Fin 13 → T2x0 ω) (e : Fin 33) (i : Fin 13)
    (hi : i∈T2x12 e) : pairSpaces ω L e≤(L i).val := Finset.inf_le hi
 theorem incidentPairSpaces_le (L : Fin 13 → T2x0 ω) (i : Fin 13) :
    T2x55 (pairSpaces ω L) i≤(L i).val :=
  incidentSpan_le (fun e he=>pairSpaces_le ω L e i he)
 theorem pairSpaces_orthogonal (L : Fin 13 → T2x0 ω) (e f : Fin 33)
    (hr : pairRelated e f) {x y : E} (hx : x∈pairSpaces ω L e) (hy : y∈pairSpaces ω L f) : ω x y=0 := by
  classical
  obtain ⟨i,he,hf⟩ := Finset.not_disjoint_iff.mp hr
  have hxi := pairSpaces_le ω L e i he hx
  have hyi := pairSpaces_le ω L f i hf hy
  have hyO : y∈ω.orthogonal (L i).val := (L i).property.symm ▸ hyi
  exact hyO x hxi
abbrev PairDimProfile (h : Fin 33 → ℕ) :=
  {L : Fin 13 → T2x0 ω // ∀ e,finrank K (pairSpaces ω L e)=h e}
abbrev DirectPairProfile (h : Fin 33 → ℕ) :=
  {L : PairDimProfile ω h // iSupIndep (pairSpaces ω L.val)}
abbrev T2x84 (A : Fin 33 → Submodule K E) :=
  (i : Fin 13) → {L : T2x0 ω // T2x55 A i≤L.val}
noncomputable def directPairProfileCoding (h : Fin 33 → ℕ) (L : DirectPairProfile ω h) :
    Σ A : DirectFamily ω h pairRelated, T2x84 ω (fun e=>(A.val e).val) :=
  ⟨⟨fun e=>⟨pairSpaces ω L.val.val e,L.val.property e⟩,L.property,
    fun e f hr _ hx _ hy=>pairSpaces_orthogonal ω L.val.val e f hr hx hy⟩,
    fun i=>⟨L.val.val i,incidentPairSpaces_le ω L.val.val i⟩⟩
 theorem directPairProfileCoding_injective (h : Fin 33 → ℕ) :
    Function.Injective (directPairProfileCoding ω h) := by
  let recover : (Σ A : DirectFamily ω h pairRelated, T2x84 ω (fun e=>(A.val e).val)) →
      (Fin 13 → T2x0 ω) := fun x i=>(x.2 i).val
  intro x y hxy
  exact Subtype.ext (Subtype.ext (congrArg recover hxy))
noncomputable def containmentExponent (D : ℕ) (ki : Fin 13 → ℕ) : ℝ :=
  ∑ i, (-(D:ℝ)*ki i+(ki i:ℝ)*(ki i-1)/2)
variable [Fintype K] [Finite E]
 theorem familyContainment_card_bound (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D=finrank K E) (A : Fin 33 → Submodule K E) (ki : Fin 13 → ℕ)
    (hk : ∀ i,finrank K (T2x55 A i)=ki i) :
    (Nat.card (T2x84 ω A):ℝ) ≤ (T2x1 D)^13*
      (Nat.card (T2x0 ω):ℝ)^13*(Fintype.card K:ℝ)^(containmentExponent D ki) := by
  have hq : 0<(Fintype.card K:ℝ) := by exact_mod_cast Fintype.card_pos (α:=K)
  have hp (i : Fin 13) : (Nat.card {L : T2x0 ω // T2x55 A i≤L.val}:ℝ) ≤
      T2x1 D*(Nat.card (T2x0 ω):ℝ)*
        (Fintype.card K:ℝ)^(-(D:ℝ)*ki i+(ki i:ℝ)*(ki i-1)/2) := by
    simpa only [hk i] using containingLagrangian_card_rpow ω h2 ha hω D hD (T2x55 A i)
  have hh := Finset.prod_le_prod (s:=Finset.univ) (fun i _=>Nat.cast_nonneg (Nat.card {L : T2x0 ω // T2x55 A i≤L.val})) (fun i _=>hp i)
  rw [T2x84,Nat.card_pi,Nat.cast_prod]
  calc _ ≤ _ := hh
       _ = _ := by
        rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,
          mul_pow,←Real.rpow_sum_of_pos hq]
        rfl
 theorem directPairProfile_card_bound (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D=finrank K E) (h : Fin 33 → ℕ) (hn : (∑ e,h e)≤2*D) :
    (Nat.card (DirectPairProfile ω h):ℝ) ≤
      2^(∑ e,h e)*(T2x1 D)^13*(Nat.card (T2x0 ω):ℝ)^13*
        (Fintype.card K:ℝ)^(-(∑ e,triangular (h e))) := by
  have hq : 0<(Fintype.card K:ℝ) := by exact_mod_cast Fintype.card_pos (α:=K)
  have hs : ∀ A : DirectFamily ω h pairRelated, (Nat.card (T2x84 ω (fun e=>(A.val e).val)):ℝ) ≤
      (T2x1 D)^13*(Nat.card (T2x0 ω):ℝ)^13*
        (Fintype.card K:ℝ)^(containmentExponent D (T2x41 h)) := by
    intro A
    exact familyContainment_card_bound ω h2 ha hω D hD _ _ (incidentSpan_finrank_direct h A.val A.property.1)
  have hi : (Nat.card (DirectPairProfile ω h):ℝ)≤
      Nat.card (Σ A : DirectFamily ω h pairRelated,T2x84 ω (fun e=>(A.val e).val)) := by
    exact_mod_cast Nat.card_le_card_of_injective _ (directPairProfileCoding_injective ω h)
  have hn' : (∑ e,h e)≤finrank K E := hD ▸ hn
  have hf := directFamily_card_bound ω hω h pairRelated pairRelated_symm hn'
  rw [←hD,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_sum] at hf
  have hc : 0 ≤ (T2x1 D)^13*(Nat.card (T2x0 ω):ℝ)^13*
      (Fintype.card K:ℝ)^(containmentExponent D (T2x41 h)) :=
    mul_nonneg (mul_nonneg (pow_nonneg (T2x10 D).le _)
      (pow_nonneg (Nat.cast_nonneg _) _)) (Real.rpow_nonneg hq.le _)
  calc _ ≤ _ := hi.trans (real_card_sigma_le _ hs)
       _ ≤ _ := mul_le_mul_of_nonneg_right hf hc
       _ = _ := by
        have he := residual_direct_exponent D h
        change _+containmentExponent D (T2x41 h)=_ at he
        rw [←he,Real.rpow_add hq]
        ring
end Containment
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section Nondirect
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E)
variable [Fintype K] [Finite E]
abbrev LocalFamilyStratum (h : Fin 33 → ℕ) (k : ℕ) (ki : Fin 13 → ℕ) :=
  {A : FamilySpanStratum (K:=K) (E:=E) h k // ∀ i,finrank K (T2x55 (fun e=>(A.val e).val) i)=ki i}
abbrev PairSpanStratum (h : Fin 33 → ℕ) (k : ℕ) (ki : Fin 13 → ℕ) :=
  {L : PairDimProfile ω h // finrank K ↥(⨆ e,pairSpaces ω L.val e)=k ∧
    ∀ i,finrank K (T2x55 (pairSpaces ω L.val) i)=ki i}
noncomputable def pairSpanStratumCoding (h : Fin 33 → ℕ) (k : ℕ) (ki : Fin 13 → ℕ)
    (L : PairSpanStratum ω h k ki) :
    Σ A : LocalFamilyStratum (K:=K) (E:=E) h k ki, T2x84 ω (fun e=>(A.val.val e).val) :=
  ⟨⟨⟨fun e=>⟨pairSpaces ω L.val.val e,L.val.property e⟩,L.property.1⟩,L.property.2⟩,
    fun i=>⟨L.val.val i,incidentPairSpaces_le ω L.val.val i⟩⟩
omit [Fintype K] [Finite E] in
 theorem pairSpanStratumCoding_injective (h : Fin 33 → ℕ) (k : ℕ) (ki : Fin 13 → ℕ) :
    Function.Injective (pairSpanStratumCoding ω h k ki) := by
  let recover : (Σ A : LocalFamilyStratum (K:=K) (E:=E) h k ki,
      T2x84 ω (fun e=>(A.val.val e).val)) → (Fin 13 → T2x0 ω) :=
    fun x i=>(x.2 i).val
  intro x y hxy
  exact Subtype.ext (Subtype.ext (congrArg recover hxy))
 theorem localFamilyStratum_card_bound (h : Fin 33 → ℕ) (k : ℕ) (ki : Fin 13 → ℕ)
    (hk : k≤finrank K E) (hh : ∀ e,h e≤k) :
    (Nat.card (LocalFamilyStratum (K:=K) (E:=E) h k ki):ℝ)≤
      2^(k+∑ e,h e)*(Fintype.card K:ℝ)^(k*(finrank K E-k)+∑ e,h e*(k-h e)) := by
  have hi : Nat.card (LocalFamilyStratum (K:=K) (E:=E) h k ki)≤
      Nat.card (FamilySpanStratum (K:=K) (E:=E) h k) :=
    Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  exact (Nat.cast_le.mpr hi).trans (familySpan_card_upper h k hk hh)
 theorem familySpan_exponent_cast (h : Fin 33 → ℕ) (k n : ℕ) (hk : k≤n) (hh : ∀ e,h e≤k) :
    ((k*(n-k)+∑ e,h e*(k-h e):ℕ):ℝ)=
      (k:ℝ)*(n-k)+∑ e,(h e:ℝ)*(k-h e) := by
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_sub hk,Nat.cast_sum,Nat.cast_sub (hh _)]
 theorem pairSpanStratum_card_bound (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D=finrank K E) (h : Fin 33 → ℕ) (k : ℕ) (ki : Fin 13 → ℕ)
    (hk : k≤2*D) (hh : ∀ e,h e≤k) :
    (Nat.card (PairSpanStratum ω h k ki):ℝ)≤
      2^(k+∑ e,h e)*(T2x1 D)^13*(Nat.card (T2x0 ω):ℝ)^13*
      (Fintype.card K:ℝ)^((k:ℝ)*(2*D-k)+(∑ e,(h e:ℝ)*(k-h e))+containmentExponent D ki) := by
  have hq : 0<(Fintype.card K:ℝ) := by exact_mod_cast Fintype.card_pos (α:=K)
  have hs : ∀ A : LocalFamilyStratum (K:=K) (E:=E) h k ki,
      (Nat.card (T2x84 ω (fun e=>(A.val.val e).val)):ℝ) ≤
      (T2x1 D)^13*(Nat.card (T2x0 ω):ℝ)^13*
        (Fintype.card K:ℝ)^(containmentExponent D ki) := by
    intro A
    exact familyContainment_card_bound ω h2 ha hω D hD _ _ A.property
  have hi : (Nat.card (PairSpanStratum ω h k ki):ℝ)≤
      Nat.card (Σ A : LocalFamilyStratum (K:=K) (E:=E) h k ki,T2x84 ω (fun e=>(A.val.val e).val)) := by
    exact_mod_cast Nat.card_le_card_of_injective _ (pairSpanStratumCoding_injective ω h k ki)
  have hn : k≤finrank K E := hD ▸ hk
  have hf := localFamilyStratum_card_bound h k ki hn hh
  rw [←Real.rpow_natCast (Fintype.card K:ℝ),familySpan_exponent_cast h k _ hn hh,←hD,
    Nat.cast_mul,Nat.cast_ofNat] at hf
  have hc : 0 ≤ (T2x1 D)^13*(Nat.card (T2x0 ω):ℝ)^13*
      (Fintype.card K:ℝ)^(containmentExponent D ki) :=
    mul_nonneg (mul_nonneg (pow_nonneg (T2x10 D).le _)
      (pow_nonneg (Nat.cast_nonneg _) _)) (Real.rpow_nonneg hq.le _)
  calc _ ≤ _ := hi.trans (real_card_sigma_le _ hs)
       _ ≤ _ := mul_le_mul_of_nonneg_right hf hc
       _ = _ := by simp only [Real.rpow_add hq];ring
 theorem residual_h_sum_le (h : Fin 33 → ℕ) (hh : ∀ e,h e=0 ∨ h e=2) : (∑ e,h e)≤66 := by
  calc _ ≤ ∑ _e : Fin 33,2 := Finset.sum_le_sum (fun e _=>by rcases hh e with he|he <;> omega)
       _ = _ := by decide
omit [Fintype K] in
 theorem pairProfile_global_dim_le (h : Fin 33 → ℕ) (L : PairDimProfile ω h) :
    finrank K ↥(⨆ e,pairSpaces ω L.val e)≤∑ e,h e := by
  have hh := finrank_finite_iSup_le (pairSpaces ω L.val)
  simpa only [L.property] using hh
omit [Fintype K] in
 theorem pairProfile_local_dim_le (h : Fin 33 → ℕ) (L : PairDimProfile ω h) (i : Fin 13) :
    finrank K (T2x55 (pairSpaces ω L.val) i)≤T2x41 h i :=
  incidentSpan_finrank_le h (fun e=>⟨_,L.property e⟩) i
abbrev T2x60 := Fin 67 × (Fin 13 → Fin 13)
noncomputable def pairProfileDimension (h : Fin 33 → ℕ) (hh : ∀ e,h e=0 ∨ h e=2)
    (L : PairDimProfile ω h) : T2x60 :=
  (⟨finrank K ↥(⨆ e,pairSpaces ω L.val e),by
    have := (pairProfile_global_dim_le ω h L).trans (residual_h_sum_le h hh); omega⟩,
   fun i=>⟨finrank K (T2x55 (pairSpaces ω L.val) i),by
    have := (pairProfile_local_dim_le ω h L i).trans (localPairDim_le_twelve h (fun e=>by rcases hh e with he|he <;> omega) i)
    omega⟩)
abbrev T2x78 (h : Fin 33 → ℕ) :=
  {L : PairDimProfile ω h // ¬iSupIndep (pairSpaces ω L.val)}
noncomputable def nondirectDimension (h : Fin 33 → ℕ) (hh : ∀ e,h e=0 ∨ h e=2)
    (L : T2x78 ω h) : T2x60 := pairProfileDimension ω h hh L.val
noncomputable def nondirectFiberInjection (h : Fin 33 → ℕ) (hh : ∀ e,h e=0 ∨ h e=2)
    (b : T2x60) (L : {L : T2x78 ω h // nondirectDimension ω h hh L=b}) :
    PairSpanStratum ω h b.1.val (fun i=>(b.2 i).val) := by
  refine ⟨L.val.val,?_,?_⟩
  · exact congrArg (fun b : T2x60=>b.1.val) L.property
  · intro i
    exact congrArg (fun b : T2x60=>(b.2 i).val) L.property
omit [Fintype K] in
 theorem nondirectFiberInjection_injective (h : Fin 33 → ℕ) (hh : ∀ e,h e=0 ∨ h e=2)
    (b : T2x60) : Function.Injective (nondirectFiberInjection ω h hh b) := by
  intro x y hxy
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun X : PairSpanStratum ω h b.1.val (fun i=>(b.2 i).val)=>X.val) hxy
 theorem pairStratum_residual_bound (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D=finrank K E) (h : Fin 33 → ℕ) (hh : ∀ e,h e=0 ∨ h e=2)
    (b : T2x60) (hk : b.1.val≤2*D) (he : ∀ e,h e≤b.1.val)
    (hki : ∀ i,(b.2 i).val≤2*(T2x17 i).card) (hs : 2*b.1.val+1≤∑ i,(b.2 i).val) :
    (Nat.card (PairSpanStratum ω h b.1.val (fun i=>(b.2 i).val)):ℝ)≤
      2^132*(T2x1 D)^13*(Nat.card (T2x0 ω):ℝ)^13*
        (Fintype.card K:ℝ)^(-(D:ℝ)+1575) := by
  have hf := pairSpanStratum_card_bound ω h2 ha hω D hD h b.1.val (fun i=>(b.2 i).val) hk he
  have hq : 1≤(Fintype.card K:ℝ) := by exact_mod_cast Fintype.card_pos (α:=K)
  have hfexp := Real.rpow_le_rpow_of_exponent_le hq
    (residual_nondirect_exponent D b.1.val h (fun i=>(b.2 i).val) hh hki hs)
  have hbpow : (2:ℝ)^(b.1.val+∑ e,h e)≤2^132 := by
    apply pow_le_pow_right₀ (by norm_num)
    have := b.1.isLt
    have := residual_h_sum_le h hh
    omega
  have hC := pow_nonneg (T2x10 D).le 13
  have hL : 0≤(Nat.card (T2x0 ω):ℝ)^13 := pow_nonneg (Nat.cast_nonneg _) _
  have hP : (0:ℝ)≤2^132 := pow_nonneg (by norm_num) _
  refine hf.trans ?_
  exact mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hbpow hC) hL)
    hfexp (Real.rpow_nonneg (le_trans (by norm_num) hq) _) (mul_nonneg (mul_nonneg hP hC) hL)
 theorem nondirectFiber_card_bound (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D=finrank K E) (h : Fin 33 → ℕ) (hh : ∀ e,h e=0 ∨ h e=2)
    (b : T2x60) :
    (Nat.card {L : T2x78 ω h // nondirectDimension ω h hh L=b}:ℝ)≤
      2^132*(T2x1 D)^13*(Nat.card (T2x0 ω):ℝ)^13*
        (Fintype.card K:ℝ)^(-(D:ℝ)+1575) := by
  classical
  by_cases hex : Nonempty {L : T2x78 ω h // nondirectDimension ω h hh L=b}
  · obtain ⟨L⟩ := hex
    let A := pairSpaces ω L.val.val.val
    have hb := (nondirectFiberInjection ω h hh b L).property
    change finrank K ↥(⨆ e,pairSpaces ω L.val.val.val e)=b.1.val ∧
      (∀ i,finrank K (T2x55 (pairSpaces ω L.val.val.val) i)=(b.2 i).val) at hb
    have hk : b.1.val≤2*D := by
      rw [hD,←hb.1]
      exact Submodule.finrank_le _
    have he : ∀ e,h e≤b.1.val := by
      intro e
      rw [←L.val.val.property e,←hb.1]
      exact Submodule.finrank_mono (le_iSup (pairSpaces ω L.val.val.val) e)
    have hki : ∀ i,(b.2 i).val≤2*(T2x17 i).card := by
      intro i
      rw [←hb.2 i]
      exact (pairProfile_local_dim_le ω h L.val.val i).trans
        (localPairDim_le h (fun e=>by rcases hh e with he|he <;> omega) i)
    have hs : 2*b.1.val+1≤∑ i,(b.2 i).val := by
      have hs := indexed_strict_span A L.val.property
      change 2*finrank K ↥(⨆ e,pairSpaces ω L.val.val.val e)+1≤
        ∑ i,finrank K (T2x55 (pairSpaces ω L.val.val.val) i) at hs
      simpa only [hb.1,hb.2] using hs
    have hi : (Nat.card {L : T2x78 ω h // nondirectDimension ω h hh L=b}:ℝ)≤
        Nat.card (PairSpanStratum ω h b.1.val (fun i=>(b.2 i).val)) := by
      exact_mod_cast Nat.card_le_card_of_injective _ (nondirectFiberInjection_injective ω h hh b)
    exact hi.trans (pairStratum_residual_bound ω h2 ha hω D hD h hh b hk he hki hs)
  · have : IsEmpty {L : T2x78 ω h // nondirectDimension ω h hh L=b} := not_nonempty_iff.mp hex
    rw [Nat.card_of_isEmpty,Nat.cast_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) _)
      (pow_nonneg (T2x10 D).le _)) (pow_nonneg (Nat.cast_nonneg _) _))
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)
 theorem nondirectPairProfile_card_bound (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D=finrank K E) (h : Fin 33 → ℕ) (hh : ∀ e,h e=0 ∨ h e=2) :
    (Nat.card (T2x78 ω h):ℝ)≤
      (67*13^13)*2^132*(T2x1 D)^13*(Nat.card (T2x0 ω):ℝ)^13*
        (Fintype.card K:ℝ)^(-(D:ℝ)+1575) := by
  have he := Nat.card_congr (Equiv.sigmaFiberEquiv (nondirectDimension ω h hh))
  rw [←he]
  have hb := real_card_sigma_le _ (nondirectFiber_card_bound ω h2 ha hω D hD h hh)
  convert hb using 1
  simp only [T2x60,Nat.card_prod,Nat.card_fin,Nat.card_fun,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  ring
end Nondirect
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
abbrev FullTailChoice (D r c : ℕ) (s : Fin 3 → ℕ) :=
  Σ u : T2x27 D r c, BaseParameters (D-c) (r-u.val.val) (s 0) (s 1) (s 2)
noncomputable def fullTailConstant (D r c : ℕ) (s : Fin 3 → ℕ)
    (x : FullTailChoice D r c s) : ℝ :=
  (orbitMassConstant D*(T2x1 D)^2)*(T2x1 D*2^c)*
    ((2^x.1.val.val*T2x1 (D-x.1.val.val))*2^(3*(D-c)))*
    T2x58 (r-x.1.val.val) (s 0) (s 1) (s 2) x.2.val
 theorem fullTailConstant_nonneg (D r c : ℕ) (s : Fin 3 → ℕ) (x : FullTailChoice D r c s) :
    0 ≤ fullTailConstant D r c s x := by
  have h₀ := (orbitMassConstant_pos D).le
  have h₁ := (T2x10 D).le
  have h₂ := (T2x10 (D-x.1.val.val)).le
  unfold fullTailConstant T2x58
  positivity
noncomputable def fullTailMajorant (D r c : ℕ) (s : Fin 3 → ℕ) (q : ℝ) : ℝ :=
  ∑ x : FullTailChoice D r c s,
    fullTailConstant D r c s x * q^(tailGain D true (T2x82 D r c s x.1 x.2))
 theorem fullTailMajorant_eq (D r c : ℕ) (s : Fin 3 → ℕ) (q : ℝ)
    (hD : D=2*r) (hc : c≤D) (hq : 0<q) :
    fullTailMajorant D r c s q =
      (orbitMassConstant D*(T2x1 D)^2)*
      q^(((D:ℝ)+1)*c+(∑ i,triangular (s i))+3*triangular r-4*triangular D)*
      ((T2x1 D*2^c)*q^(T2x19 D c)*
        ∑ u : T2x27 D r c,
          ((2^u.val.val*T2x1 (D-u.val.val))*2^(3*(D-c)))*
          q^((u.val.val:ℝ)*(c-u.val.val:ℕ)+triangular (D-u.val.val:ℕ)+
            3*triangular (D-c:ℕ)-3*triangular (r-u.val.val:ℕ))*
          T2x44 (D-c) (r-u.val.val) (s 0) (s 1) (s 2) q) := by
  classical
  unfold fullTailMajorant
  rw [Fintype.sum_sigma]
  simp_rw [←fullPlantedExponent_eq D c r hD hc s,fullPlantedExponent,Real.rpow_add hq,
    Real.rpow_sub hq,T2x44,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro θ _
  unfold fullTailConstant
  simp only [Real.rpow_add hq,Real.rpow_sub hq,Real.rpow_natCast]
  ring
section Actual
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
 theorem tripleFaceDensity_tail_bound [Invertible (2:K)]
    (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D r : ℕ) (hD : 2*D=finrank K E) (hr : D=2*r)
    (hOrbitGood : TB2_Good ω D) (hq : 4*T2x1 D≤(Fintype.card K:ℝ)) (A L M N : T2x0 ω) :
    let c := finrank K ↥((L.val⊓M.val)⊓N.val)
    let s : Fin 3 → ℕ := ![finrank K ↥(L.val⊓M.val)-c,finrank K ↥(L.val⊓N.val)-c,
      finrank K ↥(M.val⊓N.val)-c]
    tripleFaceDensity ω r A L M N ≤ fullTailMajorant D r c s (Fintype.card K) := by
  dsimp only
  have hc : finrank K ↥((L.val⊓M.val)⊓N.val)≤D :=
    T2x16 ω hω D hD _ (by intro x hx y hy; exact L.property.ge hx.1.1 y hy.1.1)
  have hq0 : (0:ℝ)<Fintype.card K := by exact_mod_cast Fintype.card_pos (α:=K)
  rw [fullTailMajorant_eq _ _ _ _ _ hr hc hq0]
  have hh := tripleFaceDensity_full_bound ω h2 ha hω D hD hOrbitGood hq r (by omega) A L M N
  dsimp only at hh
  refine hh.trans_eq ?_
  simp only [tripleDefect,commonPlantedTerm,Fin.sum_univ_three,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,
    Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat,triangular_nat]
end Actual
end SidorenkoCounterexample
end OAI
namespace OAI
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
def lowerTailTuple (c : ℕ) (s : Fin 3 → ℕ) : TailTuple := ⟨c,0,0,s,fun _=>0⟩
 theorem lowerTailTuple_s (c : ℕ) (s : Fin 3 → ℕ) (i : Fin 3) :
    (lowerTailTuple c s).s i=s i := Nat.add_zero _
 theorem lowerTailTuple_feasible (D c : ℕ) (s : Fin 3 → ℕ) (hc : c≤D) (hs : (∑ i,s i)≤D-c) :
    T2x47 D false (lowerTailTuple c s) := by
  refine ⟨hc,?_,by simp⟩
  change (∑ i,s i+0)≤D-c
  simpa only [Nat.add_zero] using hs
noncomputable def lowerTailConstant (D r : ℕ) : ℝ :=
  max 1 ((T2x1 D)^2*(r+1)*2^(2*D))
 theorem lowerTailConstant_pos (D r : ℕ) : 0<lowerTailConstant D r :=
  lt_of_lt_of_le zero_lt_one (le_max_left _ _)
 theorem pairParameters_card_le (r h : ℕ) : Nat.card (T2x77 r h)≤r+1 := by
  exact (Nat.card_le_card_of_injective _ Subtype.val_injective).trans_eq (Nat.card_fin _)
section PairBound
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
 theorem pairFaceDensity_lower_tail (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D r : ℕ) (hD : 2*D=finrank K E) (hr : D=2*r) (c : ℕ) (s : Fin 3 → ℕ)
    (A L M : T2x0 ω) (i : Fin 3)
    (hh : finrank K ↥(L.val⊓M.val)=c+s i) :
    pairFaceDensity ω r A L M≤lowerTailConstant D r*
      (Fintype.card K:ℝ)^(tailGain D false (lowerTailTuple c s)) := by
  have hq : (1:ℝ)≤Fintype.card K := by exact_mod_cast Fintype.card_pos (α:=K)
  have hb := pairFaceDensity_gain_bound ω h2 ha hω r (hr ▸ hD) A L M
  rw [←hr] at hb
  have hd : finrank K ↥(L.val⊓M.val)≤D :=
    T2x16 ω hω D hD _ (by intro x hx y hy; exact L.property.ge hx.1 y hy.1)
  have hcard : (Nat.card (T2x77 r (finrank K ↥(L.val⊓M.val))):ℝ)≤r+1 := by
    exact_mod_cast pairParameters_card_le r (finrank K ↥(L.val⊓M.val))
  have hpow : (2:ℝ)^(D+finrank K ↥(L.val⊓M.val))≤2^(2*D) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hH : finrank K ↥(L.val⊓M.val)≤(lowerTailTuple c s).maxH := by
    rw [hh]
    exact (lowerTailTuple c s).h_le_max i
  have hg : ((finrank K ↥(L.val⊓M.val)/2+1).choose 2:ℝ) ≤
      tailGain D false (lowerTailTuple c s) := by
    simp only [tailGain,Bool.false_eq_true,reduceIte,triangular_nat]
    exact triangular_mono (by positivity) (by exact_mod_cast Nat.div_le_div_right hH)
  have hp : (Fintype.card K:ℝ)^((finrank K ↥(L.val⊓M.val)/2+1).choose 2) ≤
      (Fintype.card K:ℝ)^(tailGain D false (lowerTailTuple c s)) := by
    rw [←Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hq hg
  calc
    _ ≤ _ := hb
    _ ≤ ((T2x1 D)^2*((r:ℝ)+1)*2^(2*D))*
        (Fintype.card K:ℝ)^(tailGain D false (lowerTailTuple c s)) := by
      have hs := mul_le_mul (mul_le_mul hcard hpow (by positivity) (by positivity)) hp (by positivity)
        (mul_nonneg (by positivity) (by positivity))
      have hi := mul_le_mul_of_nonneg_left hs (sq_nonneg (T2x1 D))
      nlinarith only [hi]
    _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (by positivity) _)
end PairBound
def FaceTailChoice (D r c : ℕ) (s : Fin 3 → ℕ) : Bool → Type
| true => FullTailChoice D r c s
| false => Unit
noncomputable instance faceTailChoiceFintype (D r c : ℕ) (s : Fin 3 → ℕ) (b : Bool) :
    Fintype (FaceTailChoice D r c s b) := by cases b <;> unfold FaceTailChoice <;> infer_instance
noncomputable def faceTailTuple (D r c : ℕ) (s : Fin 3 → ℕ) :
    (b : Bool) → FaceTailChoice D r c s b → TailTuple
| true,x => T2x82 D r c s x.1 x.2
| false,_ => lowerTailTuple c s
noncomputable def faceTailConstant (D r c : ℕ) (s : Fin 3 → ℕ) :
    (b : Bool) → FaceTailChoice D r c s b → ℝ
| true,x => fullTailConstant D r c s x
| false,_ => lowerTailConstant D r
 theorem faceTailConstant_pos (D r c : ℕ) (s : Fin 3 → ℕ) (b : Bool)
    (x : FaceTailChoice D r c s b) : 0≤faceTailConstant D r c s b x := by
  cases b
  · exact (lowerTailConstant_pos D r).le
  · exact fullTailConstant_nonneg D r c s x
 theorem faceTailTuple_c (D r c : ℕ) (s : Fin 3 → ℕ) (b : Bool)
    (x : FaceTailChoice D r c s b) : (faceTailTuple D r c s b x).c=c := by cases b <;> rfl
 theorem faceTailTuple_s (D r c : ℕ) (s : Fin 3 → ℕ) (b : Bool)
    (x : FaceTailChoice D r c s b) (i : Fin 3) : (faceTailTuple D r c s b x).s i=s i := by
  cases b
  · exact lowerTailTuple_s _ _ _
  · exact plantedTailTuple_s _ _ _ _ _ _ _
 theorem faceTailTuple_feasible (D r c : ℕ) (s : Fin 3 → ℕ) (hr : D=2*r)
    (hc : c≤D) (hs : (∑ i,s i)≤D-c) (b : Bool) (x : FaceTailChoice D r c s b) :
    T2x47 D b (faceTailTuple D r c s b x) := by
  cases b
  · exact lowerTailTuple_feasible D c s hc hs
  · exact plantedTailTuple_feasible D r c hr hc s hs x.1 x.2
noncomputable def T2x85 (D r c : ℕ) (s : Fin 3 → ℕ) (b : Bool) (q : ℝ) : ℝ :=
  ∑ x : FaceTailChoice D r c s b,
    faceTailConstant D r c s b x*q^(tailGain D b (faceTailTuple D r c s b x))
 theorem faceTailMajorant_true (D r c : ℕ) (s : Fin 3 → ℕ) (q : ℝ) :
    T2x85 D r c s true q=fullTailMajorant D r c s q := rfl
 theorem faceTailMajorant_false (D r c : ℕ) (s : Fin 3 → ℕ) (q : ℝ) :
    T2x85 D r c s false q=lowerTailConstant D r*q^(tailGain D false (lowerTailTuple c s)) := by
  let : Unique (FaceTailChoice D r c s false) := inferInstanceAs (Unique Unit)
  rw [T2x85,Fintype.sum_unique]
  rfl
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
def profileS (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (j : Fin 22) (i : Fin 3) : ℕ := h (facePair j i)-c j
def GeometricProfile (D : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) : Prop :=
  (∀ j,c j≤D) ∧ (∀ j i,c j≤h (facePair j i)) ∧ ∀ j,(∑ i,profileS c h j i)≤D-c j
section Actual
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
omit [Fintype K] [Finite E] in
 theorem T2x23.faceLocal {c : Fin 22 → ℕ} {h : Fin 33 → ℕ} {L : Fin 13 → T2x0 ω}
    (hL : T2x23 ω c h L) (j : Fin 22) :
    LocalProfile ω (c j) (h (facePair j 0)) (h (facePair j 1)) (h (facePair j 2))
      (L (faceVertex j 0)) (L (faceVertex j 1)) (L (faceVertex j 2)) := by
  apply T2x23.local ω hL j (faceVertex j 0) (faceVertex j 1) (faceVertex j 2)
    (facePair j 0) (facePair j 1) (facePair j 2) (faceVertex_correct j)
  · exact faceVertex_pairs j 0
  · exact faceVertex_pairs j 1
  · exact faceVertex_pairs j 2
 theorem T2x23.geometric (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D=finrank K E) {c : Fin 22 → ℕ} {h : Fin 33 → ℕ}
    {L : Fin 13 → T2x0 ω} (hL : T2x23 ω c h L) : GeometricProfile D c h := by
  have hl := hL.faceLocal ω
  have hc (j : Fin 22) : c j≤D := by
    rw [←(hl j).1]
    exact T2x16 ω hω D hD _
      (by intro x hx y hy; exact (L (faceVertex j 0)).property.ge hx.1.1 y hy.1.1)
  refine ⟨hc,?_,?_⟩
  · intro j i
    have hp := hl j
    fin_cases i
    · change c j≤h (facePair j 0)
      rw [←hp.1,←hp.2.1]; exact Submodule.finrank_mono inf_le_left
    · change c j≤h (facePair j 1)
      rw [←hp.1,←hp.2.2.1]; exact Submodule.finrank_mono (inf_le_inf inf_le_left le_rfl)
    · change c j≤h (facePair j 2)
      rw [←hp.1,←hp.2.2.2]; exact Submodule.finrank_mono (inf_le_inf inf_le_right le_rfl)
  · intro j
    have hp := actual_profile_pair_sum_le ω ha hω D (c j) (h (facePair j 0))
      (h (facePair j 1)) (h (facePair j 2)) hD
      ⟨⟨L (faceVertex j 0),L (faceVertex j 1),L (faceVertex j 2)⟩,hl j⟩
    simpa only [profileS,Fin.sum_univ_three] using hp
end Actual
 theorem profileCost_baseline (D : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ)
    (hc : ∀ j i,c j≤h (facePair j i)) :
    profileCost D c h=(∑ j,faceBaseline D (c j) (fun i=>profileS c h j i))+T2x32 h := by
  have he (j : Fin 22) (i : Fin 3) : (c j:ℝ)+((h (facePair j i)-c j:ℕ):ℝ)=(h (facePair j i):ℝ) := by
    rw [Nat.cast_sub (hc j i)]
    ring
  unfold profileCost T2x49 faceBaseline
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_sum,triangular_nat,Finset.sum_sub_distrib,
    ←Finset.sum_div,profileS,he]
  rw [sum_face_pairs (fun e=>triangular (h e))]
  unfold T2x32
  simp only [div_mul_eq_mul_div,←Finset.sum_div,sub_mul,Finset.sum_sub_distrib,one_mul,←Finset.mul_sum]
  ring
abbrev T2x34 (D r : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (full : Fin 22 → Bool) :=
  (j : Fin 22) → FaceTailChoice D r (c j) (profileS c h j) (full j)
noncomputable def globalTailTuple (D r : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (full : Fin 22 → Bool)
    (x : T2x34 D r c h full) (j : Fin 22) : TailTuple :=
  faceTailTuple D r (c j) (profileS c h j) (full j) (x j)
noncomputable def globalTailConstant (D r : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (full : Fin 22 → Bool)
    (x : T2x34 D r c h full) : ℝ := ∏ j,faceTailConstant D r (c j) (profileS c h j) (full j) (x j)
noncomputable def T2x52 (D r : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (full : Fin 22 → Bool)
    (x : T2x34 D r c h full) : ℝ := ∑ j,tailGain D (full j) (globalTailTuple D r c h full x j)
 theorem globalTailConstant_nonneg (D r : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (full : Fin 22 → Bool)
    (x : T2x34 D r c h full) : 0≤globalTailConstant D r c h full x :=
  Finset.prod_nonneg (fun j _=>faceTailConstant_pos D r (c j) (profileS c h j) (full j) (x j))
 theorem globalTailTuple_feasible (D r : ℕ) (hr : D=2*r) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ)
    (hp : GeometricProfile D c h) (full : Fin 22 → Bool) (x : T2x34 D r c h full) :
    GlobalTailFeasible D full (globalTailTuple D r c h full x) h := by
  refine ⟨fun j=>faceTailTuple_feasible D r (c j) (profileS c h j) hr (hp.1 j) (hp.2.2 j) (full j) (x j),?_⟩
  intro j i
  simp only [globalTailTuple,TailTuple.h,faceTailTuple_c,faceTailTuple_s,profileS]
  exact Nat.add_sub_of_le (hp.2.1 j i)
 theorem globalTailGain_cost (D r : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ)
    (hp : GeometricProfile D c h) (full : Fin 22 → Bool) (x : T2x34 D r c h full) :
    profileCost D c h-T2x52 D r c h full x=
      (∑ j,tailSlack D (full j) (globalTailTuple D r c h full x j))+T2x32 h := by
  rw [profileCost_baseline D c h hp.2.1]
  simp only [tailSlack,globalTailTuple,faceTailTuple_c,faceTailTuple_s,Finset.sum_sub_distrib,T2x52]
  ring
 theorem prod_faceTailMajorant (D r : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (full : Fin 22 → Bool)
    (q : ℝ) (hq : 0<q) :
    (∏ j,T2x85 D r (c j) (profileS c h j) (full j) q)=
      ∑ x : T2x34 D r c h full,globalTailConstant D r c h full x*q^(T2x52 D r c h full x) := by
  classical
  unfold T2x85
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.prod_mul_distrib,←Real.rpow_sum_of_pos hq]
  rfl
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
noncomputable def residualDirectConstant (D : ℕ) (h : Fin 33 → ℕ) : ℝ :=
  2^(∑ e,h e)*(T2x1 D)^13
noncomputable def T2x68 (D : ℕ) : ℝ :=
  (67*13^13)*2^132*(T2x1 D)^13
 theorem residualDirectConstant_nonneg (D : ℕ) (h : Fin 33 → ℕ) : 0≤residualDirectConstant D h := by
  exact mul_nonneg (pow_nonneg (by norm_num) _) (pow_nonneg (T2x10 D).le _)
 theorem residualNondirectConstant_nonneg (D : ℕ) : 0≤T2x68 D := by
  exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg (by norm_num) _))
    (pow_nonneg (by norm_num) _)) (pow_nonneg (T2x10 D).le _)
section Actual
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
omit [Fintype K] in
 theorem pairDimProfile_card_split (h : Fin 33 → ℕ) :
    Nat.card (PairDimProfile ω h)=Nat.card (DirectPairProfile ω h)+Nat.card (T2x78 ω h) := by
  classical
  exact (Nat.card_congr (Equiv.sumCompl (fun L : PairDimProfile ω h=>iSupIndep (pairSpaces ω L.val)))).symm.trans Nat.card_sum
 theorem pairDimProfile_residual_card_bound (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D=finrank K E) (h : Fin 33 → ℕ) (hh : ∀ e,h e=0 ∨ h e=2) (hlarge : 33≤D) :
    (Nat.card (PairDimProfile ω h):ℝ)≤(Nat.card (T2x0 ω):ℝ)^13*
      (residualDirectConstant D h*(Fintype.card K:ℝ)^(-(∑ e,triangular (h e)))+
        T2x68 D*(Fintype.card K:ℝ)^(-(D:ℝ)+1575)) := by
  rw [pairDimProfile_card_split,Nat.cast_add]
  have hd := directPairProfile_card_bound ω h2 ha hω D hD h
    ((residual_h_sum_le h hh).trans (by omega))
  have hn := nondirectPairProfile_card_bound ω h2 ha hω D hD h hh
  exact (add_le_add hd hn).trans_eq (by unfold residualDirectConstant T2x68;ring)
omit [Fintype K] in
 theorem pointProfile_card_le_pair (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) :
    Nat.card {L : Fin 13 → T2x0 ω // T2x23 ω c h L}≤Nat.card (PairDimProfile ω h) := by
  let f : {L : Fin 13 → T2x0 ω // T2x23 ω c h L} → PairDimProfile ω h :=
    fun L=>⟨L.val,L.property.2⟩
  exact Nat.card_le_card_of_injective f (fun x y hxy=>Subtype.ext (congrArg (fun L : PairDimProfile ω h=>L.val) hxy))
noncomputable def T2x56 (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) : ℝ :=
  (Nat.card {L : Fin 13 → T2x0 ω // T2x23 ω c h L}:ℝ)/(Nat.card (T2x0 ω):ℝ)^13
 theorem lagrangianRealCard_pos (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D=finrank K E) : (0:ℝ)<Nat.card (T2x0 ω) := by
  have hq : (0:ℝ)<Fintype.card K := by exact_mod_cast Fintype.card_pos (α:=K)
  exact (pow_pos hq _).trans_le (T2x18 ω h2 ha hω D hD).1
 theorem normalizedPointProfileCount_exposure (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D=finrank K E) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (hc : ∀ j,c j≤D) :
    T2x56 ω c h≤(T2x11 D)^11*(Fintype.card K:ℝ)^(-profileCost D c h) := by
  apply (div_le_iff₀ (pow_pos (lagrangianRealCard_pos ω h2 ha hω D hD) 13)).mpr
  exact (pointProfile_card_bound ω h2 ha hω D hD c h hc).trans_eq (by ring)
 theorem normalizedPointProfileCount_residual (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D=finrank K E) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ)
    (hh : ∀ e,h e=0 ∨ h e=2) (hlarge : 33≤D) :
    T2x56 ω c h≤
      residualDirectConstant D h*(Fintype.card K:ℝ)^(-(∑ e,triangular (h e)))+
        T2x68 D*(Fintype.card K:ℝ)^(-(D:ℝ)+1575) := by
  apply (div_le_iff₀ (pow_pos (lagrangianRealCard_pos ω h2 ha hω D hD) 13)).mpr
  have hi : (Nat.card {L : Fin 13 → T2x0 ω // T2x23 ω c h L}:ℝ)≤Nat.card (PairDimProfile ω h) :=
    by exact_mod_cast pointProfile_card_le_pair ω c h
  exact (hi.trans (pairDimProfile_residual_card_bound ω h2 ha hω D hD h hh hlarge)).trans_eq (mul_comm _ _)
end Actual
 theorem residual_triangular_sum_le (h : Fin 33 → ℕ) (hh : ∀ e,h e=0 ∨ h e=2) :
    (∑ e,triangular (h e))≤99 := by
  calc _ ≤ ∑ _e : Fin 33,(3:ℝ) := by
         apply Finset.sum_le_sum
         intro e _
         rcases hh e with he|he <;> norm_num [he,triangular]
       _ = _ := by norm_num
 theorem singular_triangular_sum_pos (h : Fin 33 → ℕ) (hs : ∃ e,h e≠0) :
    0<(∑ e,triangular (h e)) := by
  obtain ⟨e,he⟩ := hs
  exact (triangular_pos (by exact_mod_cast Nat.pos_of_ne_zero he)).trans_le
    (Finset.single_le_sum (fun f _=>triangular_nonneg (Nat.cast_nonneg _)) (Finset.mem_univ e))
 theorem globalTail_dichotomy : ∃ D₀ : ℕ, 1642≤D₀ ∧ ∀ D≥D₀,
    ∀ (r : ℕ), D=2*r → ∀ (c : Fin 22 → ℕ) (h : Fin 33 → ℕ), GeometricProfile D c h →
    ∀ (full : Fin 22 → Bool) (x : T2x34 D r c h full),
    0<profileCost D c h-T2x52 D r c h full x ∨
      ((∀ j,c j=0) ∧ (∀ e,h e=0 ∨ h e=2) ∧
        T2x52 D r c h full x=(2/3:ℝ)*∑ e,triangular (h e)) := by
  obtain ⟨D₀,hD₀⟩ := uniform_tail_dichotomy
  refine ⟨max 1642 D₀,le_max_left _ _,?_⟩
  intro D hD r hr c h hp full x
  by_cases hs : 0<profileCost D c h-T2x52 D r c h full x
  · exact Or.inl hs
  · right
    have hi := hD₀ D ((le_max_right _ _).trans hD) full (globalTailTuple D r c h full x) h
      (globalTailTuple_feasible D r hr c h hp full x)
      (by rw [←globalTailGain_cost D r c h hp full x]; exact le_of_not_gt hs)
    exact ⟨by simpa only [globalTailTuple,faceTailTuple_c] using hi.1,hi.2.1,hi.2.2.2.2⟩
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
noncomputable def T2x67 (D r : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ)
    (full : Fin 22 → Bool) (x : T2x34 D r c h full) (q : ℝ) : ℝ :=
  if 0<profileCost D c h-T2x52 D r c h full x then
    (T2x11 D)^11*q^(T2x52 D r c h full x-profileCost D c h)
  else residualDirectConstant D h*q^(-(∑ e,triangular (h e))/3)+
    T2x68 D*q^(-(D:ℝ)+1641)
 theorem profileTermMajorant_nonneg (D r : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ)
    (full : Fin 22 → Bool) (x : T2x34 D r c h full) (q : ℝ) (hq : 0≤q) :
    0≤T2x67 D r c h full x q := by
  unfold T2x67
  split
  · exact mul_nonneg (pow_nonneg (T2x88 D).le _) (Real.rpow_nonneg hq _)
  · exact add_nonneg (mul_nonneg (residualDirectConstant_nonneg D h) (Real.rpow_nonneg hq _))
      (mul_nonneg (residualNondirectConstant_nonneg D) (Real.rpow_nonneg hq _))
 theorem negative_rpow_tendsto_zero (e : ℝ) (he : e<0) :
    Filter.Tendsto (fun q : ℝ=>q^e) Filter.atTop (nhds 0) := by
  simpa only [neg_neg] using tendsto_rpow_neg_atTop (neg_pos.mpr he)
 theorem profileTermMajorant_tendsto_zero (D r : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ)
    (full : Fin 22 → Bool) (x : T2x34 D r c h full) (hD : 1642≤D) (hh : ∃ e,h e≠0) :
    Filter.Tendsto (T2x67 D r c h full x) Filter.atTop (nhds 0) := by
  unfold T2x67
  split_ifs with hs
  · have he : T2x52 D r c h full x-profileCost D c h<0 := by linarith
    convert (negative_rpow_tendsto_zero _ he).const_mul ((T2x11 D)^11) using 1; simp
  · have he : -(∑ e,triangular (h e))/3<0 := by have := singular_triangular_sum_pos h hh; linarith
    have hD' : -(D:ℝ)+1641<0 := by
      have hDc : (1642:ℝ)≤D := by exact_mod_cast hD
      linarith
    convert ((negative_rpow_tendsto_zero _ he).const_mul (residualDirectConstant D h)).add
      ((negative_rpow_tendsto_zero _ hD').const_mul (T2x68 D)) using 1; simp
 theorem residual_gain_bound (q N A B D S G : ℝ) (hq : 1≤q) (hB : 0≤B)
    (hN : N≤A*q^(-S)+B*q^(-D+1575)) (hg : G=(2/3:ℝ)*S) (hS : S≤99) :
    N*q^G≤A*q^(-S/3)+B*q^(-D+1641) := by
  have hq0 : 0<q := zero_lt_one.trans_le hq
  rw [hg]
  have he : -D+1575+(2/3:ℝ)*S≤-D+1641 := by linarith
  calc _ ≤ (A*q^(-S)+B*q^(-D+1575))*q^((2/3:ℝ)*S) :=
        mul_le_mul_of_nonneg_right hN (Real.rpow_nonneg hq0.le _)
       _ = A*q^(-S/3)+B*q^(-D+1575+(2/3:ℝ)*S) := by
        rw [add_mul,mul_assoc,mul_assoc,←Real.rpow_add hq0,←Real.rpow_add hq0,
          show -S+(2/3:ℝ)*S=-S/3 by ring]
       _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hq he) hB)
section Actual
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
 theorem normalizedPointProfile_term_bound (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D r : ℕ) (hD : 2*D=finrank K E) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (hc : ∀ j,c j≤D)
    (full : Fin 22 → Bool) (x : T2x34 D r c h full) (hlarge : 33≤D)
    (hdich : 0<profileCost D c h-T2x52 D r c h full x ∨
      ((∀ e,h e=0 ∨ h e=2) ∧ T2x52 D r c h full x=(2/3:ℝ)*∑ e,triangular (h e))) :
    T2x56 ω c h*(Fintype.card K:ℝ)^(T2x52 D r c h full x)≤
      T2x67 D r c h full x (Fintype.card K) := by
  have hq0 : (0:ℝ)<Fintype.card K := by exact_mod_cast Fintype.card_pos (α:=K)
  have hq1 : (1:ℝ)≤Fintype.card K := by exact_mod_cast Fintype.card_pos (α:=K)
  unfold T2x67
  split_ifs with hs
  · calc _ ≤ ((T2x11 D)^11*(Fintype.card K:ℝ)^(-profileCost D c h))*
          (Fintype.card K:ℝ)^(T2x52 D r c h full x) :=
        mul_le_mul_of_nonneg_right (normalizedPointProfileCount_exposure ω h2 ha hω D hD c h hc)
          (Real.rpow_nonneg hq0.le _)
         _ = _ := by rw [mul_assoc,←Real.rpow_add hq0]; congr 2; ring
  · obtain ⟨hh,hg⟩ := hdich.resolve_left hs
    exact residual_gain_bound _ _ _ _ _ _ _ hq1 (residualNondirectConstant_nonneg D)
      (normalizedPointProfileCount_residual ω h2 ha hω D hD c h hh hlarge) hg
      (residual_triangular_sum_le h hh)
end Actual
noncomputable def profileTailMajorant (D r : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ)
    (full : Fin 22 → Bool) (q : ℝ) : ℝ :=
  ∑ x : T2x34 D r c h full,globalTailConstant D r c h full x*T2x67 D r c h full x q
 theorem profileTailMajorant_tendsto_zero (D r : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ)
    (full : Fin 22 → Bool) (hD : 1642≤D) (hh : ∃ e,h e≠0) :
    Filter.Tendsto (profileTailMajorant D r c h full) Filter.atTop (nhds 0) := by
  have ht (x : T2x34 D r c h full) : Filter.Tendsto
      (fun q=>globalTailConstant D r c h full x*T2x67 D r c h full x q) Filter.atTop (nhds 0) := by
    convert (profileTermMajorant_tendsto_zero D r c h full x hD hh).const_mul
      (globalTailConstant D r c h full x) using 1; simp
  change Filter.Tendsto (fun q=>∑ x : T2x34 D r c h full,
    globalTailConstant D r c h full x*T2x67 D r c h full x q) _ _
  simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ (fun x _=>ht x)
section ActualProduct
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
 theorem normalizedPointProfile_product_bound (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D r : ℕ) (hD : 2*D=finrank K E) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (hc : ∀ j,c j≤D)
    (full : Fin 22 → Bool) (hlarge : 33≤D)
    (hdich : ∀ x : T2x34 D r c h full, 0<profileCost D c h-T2x52 D r c h full x ∨
      ((∀ e,h e=0 ∨ h e=2) ∧ T2x52 D r c h full x=(2/3:ℝ)*∑ e,triangular (h e))) :
    T2x56 ω c h*(∏ j,T2x85 D r (c j) (profileS c h j) (full j) (Fintype.card K))≤
      profileTailMajorant D r c h full (Fintype.card K) := by
  have hq : (0:ℝ)<Fintype.card K := by exact_mod_cast Fintype.card_pos (α:=K)
  rw [prod_faceTailMajorant _ _ _ _ _ _ hq,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  have ht := mul_le_mul_of_nonneg_left
    (normalizedPointProfile_term_bound ω h2 ha hω D r hD c h hc full x hlarge (hdich x))
    (globalTailConstant_nonneg D r c h full x)
  exact (le_of_eq (by ring)).trans ht
end ActualProduct
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section ActiveFace
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
abbrev ActiveCenterSet (r : ℕ) (L : Fin 3 → T2x0 ω) (T : Finset (Fin 3)) :=
  {Y : T2x0 ω // ∀ i∈T,finrank K ↥((L i).val⊓Y.val)=r}
noncomputable def T2x36 (r : ℕ) (A : T2x0 ω)
    (L : Fin 3 → T2x0 ω) (T : Finset (Fin 3)) : ℝ :=
  (Nat.card (ActiveCenterSet ω r L T):ℝ)/(Nat.card (T2x0 ω):ℝ)*
    ((Nat.card (T2x0 ω):ℝ)/Nat.card (T2x7 ω A r))^T.card
 omit [Fintype K] [Finite E] in
 theorem activeFaceDensity_nonneg (r : ℕ) (A : T2x0 ω)
    (L : Fin 3 → T2x0 ω) (T : Finset (Fin 3)) :
    0 ≤ T2x36 ω r A L T := by unfold T2x36; positivity
 omit [Fintype K] in
 theorem lagrangian_card_pos (A : T2x0 ω) :
    (0:ℝ)<Nat.card (T2x0 ω) := by
  let : Nonempty (T2x0 ω) := ⟨A⟩
  exact_mod_cast Nat.card_pos
 omit [Fintype K] in
 theorem activeFaceDensity_empty (r : ℕ) (A : T2x0 ω)
    (L : Fin 3 → T2x0 ω) : T2x36 ω r A L ∅=1 := by
  have hc : Nat.card (ActiveCenterSet ω r L ∅)=Nat.card (T2x0 ω) :=
    Nat.card_congr (Equiv.subtypeUnivEquiv (by simp))
  simp only [T2x36,hc,Finset.card_empty,pow_zero,mul_one]
  exact div_self (lagrangian_card_pos ω A).ne'
 theorem activeFaceDensity_singleton (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D r : ℕ) (hD : 2*D=finrank K E) (hr : r ≤ D) (A : T2x0 ω)
    (L : Fin 3 → T2x0 ω) (i : Fin 3) : T2x36 ω r A L {i}=1 := by
  classical
  have hc : Nat.card (ActiveCenterSet ω r L {i})=Nat.card (T2x7 ω (L i) r) :=
    Nat.card_congr (Equiv.subtypeEquivRight (by
      intro Y
      simp only [Finset.mem_singleton,forall_eq]
      rw [inf_comm]))
  rw [symplectic_center_stratum_card_eq ω h2 ha hω (L i) A r] at hc
  simp only [T2x36,hc,Finset.card_singleton,pow_one]
  have hL := (lagrangian_card_pos ω A).ne'
  have hA := (symplectic_center_stratum_card_pos ω h2 ha hω D hD A r hr).ne'
  field_simp
 omit [Fintype K] in
 theorem activeFaceDensity_pair (r : ℕ) (A : T2x0 ω)
    (L : Fin 3 → T2x0 ω) (i k : Fin 3) (hik : i≠k) :
    T2x36 ω r A L {i,k}=pairFaceDensity ω r A (L i) (L k) := by
  classical
  have hc : Nat.card (ActiveCenterSet ω r L {i,k})=Nat.card (PairCenterSet ω r (L i).val (L k).val) :=
    Nat.card_congr (Equiv.subtypeEquivRight (by intro Y; simp))
  simp only [T2x36,hc,Finset.card_pair hik,pairFaceDensity]
  have hL := (lagrangian_card_pos ω A).ne'
  field_simp
 omit [Fintype K] in
 theorem activeFaceDensity_full (r : ℕ) (A : T2x0 ω)
    (L : Fin 3 → T2x0 ω) :
    T2x36 ω r A L Finset.univ=tripleFaceDensity ω r A (L 0) (L 1) (L 2) := by
  classical
  have hc : Nat.card (ActiveCenterSet ω r L Finset.univ)=Nat.card (T2x69 ω r (L 0).val (L 1).val (L 2).val) :=
    Nat.card_congr (Equiv.subtypeEquivRight (by intro Y; simp [Fin.forall_fin_succ]))
  simp only [T2x36,hc,Finset.card_univ,Fintype.card_fin,tripleFaceDensity]
  have hL := (lagrangian_card_pos ω A).ne'
  field_simp
 theorem one_le_lowerTailMajorant (D r c : ℕ) (s : Fin 3 → ℕ) (q : ℝ) (hq : 1 ≤ q) :
    1 ≤ T2x85 D r c s false q := by
  rw [faceTailMajorant_false]
  have hc : 1 ≤ lowerTailConstant D r := le_max_left _ _
  have hg : 0 ≤ tailGain D false (lowerTailTuple c s) := by
    simp only [tailGain,Bool.false_eq_true,reduceIte]
    exact triangular_nonneg (by positivity)
  exact one_le_mul_of_one_le_of_one_le hc (Real.one_le_rpow hq hg)
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
 theorem activeFaceDensity_lower_bound (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D r : ℕ) (hD : 2*D=finrank K E) (hr : D=2*r) (c : ℕ) (s : Fin 3 → ℕ)
    (A : T2x0 ω) (L : Fin 3 → T2x0 ω)
    (hL : LocalProfile ω c (c+s 0) (c+s 1) (c+s 2) (L 0) (L 1) (L 2))
    (T : Finset (Fin 3)) (hT : T≠Finset.univ) :
    T2x36 ω r A L T ≤ T2x85 D r c s false (Fintype.card K) := by
  have hq : (1:ℝ) ≤ Fintype.card K := by exact_mod_cast Fintype.card_pos (α:=K)
  have hr' : r ≤ D := by omega
  rcases fin3_subsets T with ht|ht|ht|ht|ht|ht|ht|ht
  · rw [ht,activeFaceDensity_empty]; exact one_le_lowerTailMajorant D r c s _ hq
  · rw [ht,activeFaceDensity_singleton ω h2 ha hω D r hD hr']; exact one_le_lowerTailMajorant D r c s _ hq
  · rw [ht,activeFaceDensity_singleton ω h2 ha hω D r hD hr']; exact one_le_lowerTailMajorant D r c s _ hq
  · rw [ht,activeFaceDensity_singleton ω h2 ha hω D r hD hr']; exact one_le_lowerTailMajorant D r c s _ hq
  · rw [ht,activeFaceDensity_pair ω r A L 0 1 (by decide),faceTailMajorant_false]
    exact pairFaceDensity_lower_tail ω h2 ha hω D r hD hr c s A (L 0) (L 1) 0 hL.2.1
  · rw [ht,activeFaceDensity_pair ω r A L 0 2 (by decide),faceTailMajorant_false]
    exact pairFaceDensity_lower_tail ω h2 ha hω D r hD hr c s A (L 0) (L 2) 1 hL.2.2.1
  · rw [ht,activeFaceDensity_pair ω r A L 1 2 (by decide),faceTailMajorant_false]
    exact pairFaceDensity_lower_tail ω h2 ha hω D r hD hr c s A (L 1) (L 2) 2 hL.2.2.2
  · exact (hT ht).elim
 theorem activeFaceDensity_tail_bound [Invertible (2:K)]
    (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D r : ℕ) (hD : 2*D=finrank K E) (hr : D=2*r) (c : ℕ) (s : Fin 3 → ℕ)
    (hOrbitGood : TB2_Good ω D) (hq : 4*T2x1 D ≤ (Fintype.card K:ℝ))
    (A : T2x0 ω) (L : Fin 3 → T2x0 ω)
    (hL : LocalProfile ω c (c+s 0) (c+s 1) (c+s 2) (L 0) (L 1) (L 2))
    (T : Finset (Fin 3)) :
    T2x36 ω r A L T ≤ T2x85 D r c s (decide (T=Finset.univ)) (Fintype.card K) := by
  classical
  by_cases ht : T=Finset.univ
  · simp only [ht,decide_true,faceTailMajorant_true,activeFaceDensity_full]
    have hb := tripleFaceDensity_tail_bound ω h2 ha hω D r hD hr hOrbitGood hq A (L 0) (L 1) (L 2)
    dsimp only at hb
    rw [hL.1,hL.2.1,hL.2.2.1,hL.2.2.2] at hb
    have hs : ![c+s 0-c,c+s 1-c,c+s 2-c]=s := by funext i; fin_cases i <;> simp
    rwa [hs] at hb
  · simp only [ht,decide_false]
    exact activeFaceDensity_lower_bound ω h2 ha hω D r hD hr c s A L hL T ht
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
noncomputable def profileActiveDensity (r : ℕ) (A : T2x0 ω)
    (T : Fin 22 → Finset (Fin 3)) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) : ℝ := by
  classical
  let := Fintype.ofFinite {L : Fin 13 → T2x0 ω // T2x23 ω c h L}
  exact (∑ L : {L : Fin 13 → T2x0 ω // T2x23 ω c h L},
    ∏ j,T2x36 ω r A (fun i=>L.val (faceVertex j i)) (T j))/(Nat.card (T2x0 ω):ℝ)^13
 theorem profileActiveDensity_bound [Invertible (2:K)]
    (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D r : ℕ) (hD : 2*D=finrank K E) (hr : D=2*r)
    (hOrbitGood : TB2_Good ω D) (hq : 4*T2x1 D ≤ (Fintype.card K:ℝ))
    (A : T2x0 ω) (T : Fin 22 → Finset (Fin 3)) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) :
    profileActiveDensity ω r A T c h ≤ T2x56 ω c h*
      ∏ j,T2x85 D r (c j) (profileS c h j) (decide (T j=Finset.univ)) (Fintype.card K) := by
  classical
  let := Fintype.ofFinite {L : Fin 13 → T2x0 ω // T2x23 ω c h L}
  unfold profileActiveDensity T2x56
  rw [div_mul_eq_mul_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc _  ≤  ∑ _L : {L : Fin 13 → T2x0 ω // T2x23 ω c h L},
      ∏ j,T2x85 D r (c j) (profileS c h j) (decide (T j=Finset.univ)) (Fintype.card K) := by
        apply Finset.sum_le_sum
        intro L _
        apply Finset.prod_le_prod
        · intro j _; exact activeFaceDensity_nonneg ω r A _ (T j)
        · intro j _
          have hl := L.property.faceLocal ω j
          have hp := L.property.geometric ω ha hω D hD
          have hs (i : Fin 3) : c j+profileS c h j i=h (facePair j i) :=
            Nat.add_sub_of_le (hp.2.1 j i)
          exact activeFaceDensity_tail_bound ω h2 ha hω D r hD hr (c j) (profileS c h j) hOrbitGood hq A
            (fun i=>L.val (faceVertex j i)) (by simpa only [hs] using hl) (T j)
       _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card]
end Integrated
 theorem profileTailMajorant_nonneg (D r : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ)
    (full : Fin 22 → Bool) (q : ℝ) (hq : 0 ≤ q) : 0 ≤ profileTailMajorant D r c h full q := by
  exact Finset.sum_nonneg (fun x _=>mul_nonneg (globalTailConstant_nonneg _ _ _ _ _ _)
    (profileTermMajorant_nonneg _ _ _ _ _ _ _ hq))
noncomputable def integratedTailMajorant (D r : ℕ) (full : Fin 22 → Bool) (q : ℝ) : ℝ := by
  classical
  exact ∑ p : DimProfile D, if ∃ e,p.h e≠0 then profileTailMajorant D r p.c p.h full q else 0
 theorem integratedTailMajorant_tendsto_zero (D r : ℕ) (full : Fin 22 → Bool) (hD : 1642 ≤ D) :
    Filter.Tendsto (integratedTailMajorant D r full) Filter.atTop (nhds 0) := by
  classical
  have ht (p : DimProfile D) : Filter.Tendsto
      (fun q=>if ∃ e,p.h e≠0 then profileTailMajorant D r p.c p.h full q else 0) Filter.atTop (nhds 0) := by
    by_cases hp : ∃ e,p.h e≠0
    · simpa only [hp,reduceIte] using profileTailMajorant_tendsto_zero D r p.c p.h full hD hp
    · simpa only [hp,reduceIte] using (tendsto_const_nhds (x:=(0:ℝ)) (f:=Filter.atTop))
  change Filter.Tendsto (fun q=>∑ p : DimProfile D, if ∃ e,p.h e≠0 then profileTailMajorant D r p.c p.h full q else 0) _ _
  simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ (fun p _=>ht p)
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
noncomputable def T2x64 : ℕ := Classical.choose globalTail_dichotomy
 theorem singularTailThreshold_large : 1642 ≤ T2x64 := (Classical.choose_spec globalTail_dichotomy).1
 theorem singularTailThreshold_dichotomy (D : ℕ) (hD : T2x64 ≤ D)
    (r : ℕ) (hr : D=2*r) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (hp : GeometricProfile D c h)
    (full : Fin 22 → Bool) (x : T2x34 D r c h full) :
    0<profileCost D c h-T2x52 D r c h full x ∨
      ((∀ e,h e=0 ∨ h e=2) ∧ T2x52 D r c h full x=(2/3:ℝ)*∑ e,triangular (h e)) := by
  rcases (Classical.choose_spec globalTail_dichotomy).2 D hD r hr c h hp full x with hs|hs
  · exact Or.inl hs
  · exact Or.inr hs.2
section IntegratedBound
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
 theorem profileActiveDensity_tail_bound [Invertible (2:K)]
    (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D r : ℕ) (hD : 2*D=finrank K E) (hr : D=2*r) (hlarge : T2x64 ≤ D)
    (hOrbitGood : TB2_Good ω D) (hq : 4*T2x1 D ≤ (Fintype.card K:ℝ))
    (A : T2x0 ω) (T : Fin 22 → Finset (Fin 3)) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) :
    profileActiveDensity ω r A T c h ≤ profileTailMajorant D r c h (fun j=>decide (T j=Finset.univ)) (Fintype.card K) := by
  classical
  by_cases hp : Nonempty {L : Fin 13 → T2x0 ω // T2x23 ω c h L}
  · obtain ⟨L⟩ := hp
    have hg := L.property.geometric ω ha hω D hD
    refine (profileActiveDensity_bound ω h2 ha hω D r hD hr hOrbitGood hq A T c h).trans ?_
    apply normalizedPointProfile_product_bound ω h2 ha hω D r hD c h hg.1 _
      (by have := singularTailThreshold_large; omega)
    exact singularTailThreshold_dichotomy D hlarge r hr c h hg _
  · let : IsEmpty {L : Fin 13 → T2x0 ω // T2x23 ω c h L} := not_nonempty_iff.mp hp
    have hz : profileActiveDensity ω r A T c h=0 := by simp [profileActiveDensity]
    rw [hz]
    exact profileTailMajorant_nonneg _ _ _ _ _ _ (Nat.cast_nonneg _)
noncomputable def integratedActiveTail (D r : ℕ) (A : T2x0 ω)
    (T : Fin 22 → Finset (Fin 3)) : ℝ := by
  classical
  exact ∑ p : DimProfile D, if ∃ e,p.h e≠0 then profileActiveDensity ω r A T p.c p.h else 0
 theorem integratedActiveTail_bound [Invertible (2:K)]
    (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D r : ℕ) (hD : 2*D=finrank K E) (hr : D=2*r) (hlarge : T2x64 ≤ D)
    (hOrbitGood : TB2_Good ω D) (hq : 4*T2x1 D ≤ (Fintype.card K:ℝ))
    (A : T2x0 ω) (T : Fin 22 → Finset (Fin 3)) :
    integratedActiveTail ω D r A T ≤ integratedTailMajorant D r (fun j=>decide (T j=Finset.univ)) (Fintype.card K) := by
  classical
  unfold integratedActiveTail integratedTailMajorant
  apply Finset.sum_le_sum
  intro p _
  split_ifs
  · exact profileActiveDensity_tail_bound ω h2 ha hω D r hD hr hlarge hOrbitGood hq A T p.c p.h
  · rfl
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
include hω hD in
theorem finite_inf_lagrangians_finrank_le (L : Fin 13 → T2x0 ω)
    (s : Finset (Fin 13)) (hs : s.Nonempty) :
    finrank K ↥(s.inf fun i => (L i).val : Submodule K E) ≤ D := by
  obtain ⟨i, hi⟩ := hs
  have hd := T2x6 ω (L i).val hω (L i).property
  have hb : (s.inf fun i => (L i).val : Submodule K E) ≤ (L i).val := Finset.inf_le hi
  have := Submodule.finrank_mono hb
  omega
noncomputable def configProfile (L : Fin 13 → T2x0 ω) : DimProfile D :=
  (fun j => ⟨finrank K ↥((faces j).inf fun i => (L i).val : Submodule K E),
    Nat.lt_succ_of_le (finite_inf_lagrangians_finrank_le ω hω D hD L (faces j)
      (Finset.card_pos.mp (by rw [faces_card]; omega)))⟩,
   fun e => ⟨finrank K ↥((T2x12 e).inf fun i => (L i).val : Submodule K E),
    Nat.lt_succ_of_le (finite_inf_lagrangians_finrank_le ω hω D hD L (T2x12 e)
      (Finset.card_pos.mp (by rw [pairVertices_card]; omega)))⟩)
theorem configProfile_property (L : Fin 13 → T2x0 ω) :
    T2x23 ω (configProfile ω hω D hD L).c (configProfile ω hω D hD L).h L :=
  ⟨fun _ => rfl, fun _ => rfl⟩
theorem configProfile_eq_iff (L : Fin 13 → T2x0 ω) (p : DimProfile D) :
    configProfile ω hω D hD L = p ↔ T2x23 ω p.c p.h L := by
  constructor
  · intro h; rw [← h]; exact configProfile_property ω hω D hD L
  · intro h
    apply Prod.ext
    · funext j; exact Fin.ext (h.1 j)
    · funext e; exact Fin.ext (h.2 e)
noncomputable def actualSingularTail (r : ℕ) (A : T2x0 ω)
    (T : Fin 22 → Finset (Fin 3)) : ℝ := by
  classical
  let := Fintype.ofFinite (Fin 13 → T2x0 ω)
  exact (∑ L : Fin 13 → T2x0 ω,
    if ∃ e, finrank K ↥((T2x12 e).inf fun i => (L i).val : Submodule K E) ≠ 0
    then ∏ j, T2x36 ω r A (fun i => L (faceVertex j i)) (T j) else 0) /
      (Nat.card (T2x0 ω) : ℝ)^13
 include hω hD in
 theorem actualSingularTail_eq_integrated (r : ℕ) (A : T2x0 ω)
    (T : Fin 22 → Finset (Fin 3)) :
    actualSingularTail ω r A T = integratedActiveTail ω D r A T := by
  classical
  let := Fintype.ofFinite (Fin 13 → T2x0 ω)
  let := fun p : DimProfile D => Fintype.ofFinite
    {L : Fin 13 → T2x0 ω // T2x23 ω p.c p.h L}
  let w (L : Fin 13 → T2x0 ω) : ℝ :=
    ∏ j, T2x36 ω r A (fun i => L (faceVertex j i)) (T j)
  let f (L : Fin 13 → T2x0 ω) : ℝ :=
    if ∃ e, (configProfile ω hω D hD L).h e ≠ 0 then w L else 0
  have he (p : DimProfile D) :
      (∑ L : {L // configProfile ω hω D hD L = p}, f L.val) =
      if ∃ e, p.h e ≠ 0 then
        ∑ L : {L // T2x23 ω p.c p.h L}, w L.val else 0 := by
    let e : {L // configProfile ω hω D hD L = p} ≃ {L // T2x23 ω p.c p.h L} :=
      Equiv.subtypeEquivRight (fun L => configProfile_eq_iff ω hω D hD L p)
    have hf (L : {L // configProfile ω hω D hD L = p}) :
        f L.val = if ∃ e, p.h e ≠ 0 then w (e L).val else 0 := by
      dsimp only [f]; rw [L.property]; rfl
    simp_rw [hf]
    by_cases hp : ∃ e, p.h e ≠ 0
    · simp only [hp,reduceIte]; exact Equiv.sum_comp e (fun L => w L.val)
    · simp only [hp,reduceIte,Finset.sum_const_zero]
  have hsum : (∑ L, f L) = ∑ p : DimProfile D,
      if ∃ e, p.h e ≠ 0 then ∑ L : {L // T2x23 ω p.c p.h L}, w L.val else 0 := by
    rw [← Fintype.sum_fiberwise (configProfile ω hω D hD) f]
    exact Finset.sum_congr rfl (fun p _ => he p)
  change (∑ L, f L) / (Nat.card (T2x0 ω) : ℝ)^13 =
    ∑ p : DimProfile D, if ∃ e, p.h e ≠ 0 then
      (∑ L : {L // T2x23 ω p.c p.h L}, w L.val) /
        (Nat.card (T2x0 ω) : ℝ)^13 else 0
  rw [hsum,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro p _
  split_ifs <;> simp
 theorem actualSingularTail_nonneg (r : ℕ) (A : T2x0 ω)
    (T : Fin 22 → Finset (Fin 3)) : 0 ≤ actualSingularTail ω r A T := by
  classical
  unfold actualSingularTail
  apply div_nonneg _ (by positivity)
  apply Finset.sum_nonneg
  intro L _
  split_ifs
  · exact Finset.prod_nonneg (fun j _ => activeFaceDensity_nonneg ω r A _ (T j))
  · rfl
 include hω hD in
 theorem actualSingularTail_bound [Fintype K] [Invertible (2 : K)]
    (h2 : (2 : K) ≠ 0) (ha : ω.IsAlt) (r : ℕ) (hr : D = 2*r)
    (hlarge : T2x64 ≤ D)
    (hOrbitGood : TB2_Good ω D) (hq : 4*T2x1 D ≤ (Fintype.card K : ℝ))
    (A : T2x0 ω) (T : Fin 22 → Finset (Fin 3)) :
    actualSingularTail ω r A T ≤
      integratedTailMajorant D r (fun j => decide (T j = Finset.univ)) (Fintype.card K) := by
  rw [actualSingularTail_eq_integrated ω hω D hD]
  exact integratedActiveTail_bound ω h2 ha hω D r hD hr hlarge hOrbitGood hq A T
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
variable [FiniteDimensional K V] [Fintype K] [DecidableEq K]
noncomputable def discriminantSign (B : LinearMap.BilinForm K V) (hB : B.IsSymm) : ℤ :=
  quadraticChar K ((radicalQuotientForm B hB).toMatrix
    (Module.finBasis K (V ⧸ B.ker))).det
end Forms
section Pullback
variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]
variable [FiniteDimensional K V] [Fintype K] [DecidableEq K]
end Pullback
section MatrixForms
variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]
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
noncomputable def signedLayer (r : ℕ) (ξ : ℤ) : Finset (SymMatrix K D) := by
  classical
  exact Finset.univ.filter fun Z => Z.val.rank = r ∧ matrixSign K D Z = ξ
noncomputable def layerMass (r : ℕ) (ξ : ℤ) : ℝ :=
  (signedLayer K D r ξ).card / (Fintype.card (SymMatrix K D) : ℝ)
noncomputable def rankKernel (r : ℕ) (ξ : ℤ) (Z : SymMatrix K D) : ℝ := by
  classical
  exact if Z ∈ signedLayer K D r ξ then (layerMass K D r ξ)⁻¹ else 0
@[simp] theorem mem_signedLayer (r : ℕ) (ξ : ℤ) (Z : SymMatrix K D) :
    Z ∈ signedLayer K D r ξ ↔ Z.val.rank = r ∧ matrixSign K D Z = ξ := by
  classical
  simp [signedLayer]
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
end Border
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open scoped BigOperators
section Mean
variable {A B : Type*} [Fintype A] [Fintype B]
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
end Scalar
section MatrixSign
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
end MatrixSign
end SidorenkoCounterexample
end
section
namespace SidorenkoCounterexample
open Module LinearMap
section NondegSign
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable [FiniteDimensional K V] [Fintype K] [DecidableEq K]
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
end RadicalCount
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module LinearMap
open scoped BigOperators
section RankCard
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype K] [DecidableEq K]
end RankCard
section LayerCard
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
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
theorem primeInfinity_real_tendsto :
    Tendsto (fun q : OddPrime => (q.val : ℝ)) primeInfinity atTop :=
  tendsto_natCast_atTop_atTop.comp Filter.tendsto_comap
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
def pairLeft : Fin 33 → Fin 13 := ![0,0,2,0,2,0,1,2,3,1,4,1,3,3,4,1,9,4,8,1,7,10,8,7,8,5,5,5,6,6,6,6,5]
def pairRight : Fin 33 → Fin 13 := ![2,3,3,9,9,1,3,4,4,9,9,10,10,11,11,12,12,8,9,7,10,11,11,12,12,7,10,11,8,11,7,12,6]
theorem pair_endpoints : ∀ e, T2x12 e={pairLeft e,pairRight e} := by decide
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
noncomputable def prod (p : FiniteLaw A) (q : FiniteLaw B) : FiniteLaw (A × B) where
  weight x := p.weight x.1*q.weight x.2
  nonneg _ := mul_nonneg (p.nonneg _) (q.nonneg _)
  total := by rw [Fintype.sum_prod_type]; simp_rw [←Finset.mul_sum,q.total,mul_one]; exact p.total
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
namespace OAI.SidorenkoCounterexample
open Classical Module Filter
section
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
noncomputable def rawG (D r : ℕ) (T : Fin 22 → Finset (Fin 3))
    (P : Submodule K ((Fin D → K) × Module.Dual K (Fin D → K)) → Prop) : ℝ :=
  let L := {S // P S}
  letI := Fintype.ofFinite L
  let n := fun S : Submodule K ((Fin D → K) × Module.Dual K (Fin D → K)) => finrank K S
  let m := (Nat.card L:ℝ)/Nat.card {Y : L // n ((LinearMap.fst K _ _).ker ⊓ Y.1)=r}
  (∑ X : Fin 13 → L, if ∃ j k, n ((X (faceVertex j (slotLeft k))).1 ⊓ (X (faceVertex j (slotRight k))).1)≠0 then ∏ j, ((Nat.card {Y : L // ∀ k ∈ T j,n ((X (faceVertex j k)).1 ⊓ Y.1)=r}:ℝ)/Nat.card L*m^(T j).card) else 0)/(Nat.card L:ℝ)^13
abbrev explicitP (K : Type*) [Field K] (D : ℕ) (S : Submodule K ((Fin D → K) × Module.Dual K (Fin D → K))) :=
  ∀ x, x ∈ S ↔ ∀ y ∈ S, x.2 y.1 = y.2 x.1
theorem rawP_eq (D : ℕ) : explicitP K D = fun S => T2x5.orthogonal S = S := by
  funext S; apply propext
  have hh (x) : x ∈ T2x5.orthogonal S ↔ ∀ y ∈ S, x.2 y.1 = y.2 x.1 := by
    change (∀ y ∈ S, x.2 y.1 - y.2 x.1 = 0) ↔ _
    simp only [sub_eq_zero]
  exact ⟨fun h => Submodule.ext fun x => (hh x).trans (h x).symm, fun h x => (show x ∈ S ↔ x ∈ T2x5.orthogonal S by rw [h]).trans (hh x)⟩
theorem TB2_eq (D r : ℕ) (T : Fin 22 → Finset (Fin 3)) : rawG D r T (explicitP K D) = actualSingularTail (T2x5 (K := K) (V := Fin D → K)) r verticalLagrangian T := by
  classical
  rw [rawP_eq]
  unfold rawG actualSingularTail
  dsimp only
  apply congrArg (fun x : ℝ => x / _)
  apply Finset.sum_congr (by ext; simp)
  intro X _
  have hs : ∀ e : Fin 33, ∃ j k, facePair j k = e := by decide
  have he (j k) : (T2x12 (facePair j k)).inf (fun i => (X i).val) = (X (faceVertex j (slotLeft k))).val ⊓ (X (faceVertex j (slotRight k))).val := by
    rw [pair_endpoints,(facePair_endpoints j k).1,(facePair_endpoints j k).2]; simp
  have hi : (∃ j k, finrank K ↥((X (faceVertex j (slotLeft k))).val ⊓ (X (faceVertex j (slotRight k))).val) ≠ 0) ↔ (∃ e, finrank K ↥((T2x12 e).inf fun i => (X i).val) ≠ 0) := by
    constructor
    · rintro ⟨j,k,h⟩; exact ⟨facePair j k,by rwa [he]⟩
    · rintro ⟨e,h⟩; obtain ⟨j,k,rfl⟩ := hs e; exact ⟨j,k,by rwa [he] at h⟩
  rw [if_congr hi rfl rfl]
  split
  · apply Finset.prod_congr rfl
    intro j _
    let L := T2x0 (T2x5 (K := K) (V := Fin D → K))
    let V := (LinearMap.fst K (Fin D → K) (Module.Dual K (Fin D → K))).ker
    have hh : Nat.card {Y : L // finrank K ↥(V ⊓ Y.val) = r} = Nat.card {Y : L // finrank K ↥(Y.val ⊓ V) = r} := Nat.card_congr (Equiv.subtypeEquivRight (fun Y => by rw [inf_comm]))
    change _ * ((Nat.card L : ℝ) / Nat.card {Y : L // finrank K ↥(V ⊓ Y.val) = r}) ^ _ = _
    rw [hh]
    rfl
  · rfl
end
end OAI.SidorenkoCounterexample
open Module Filter OAI.SidorenkoCounterexample
def TB2_good (d : ℕ) (q : OddPrime) : Prop := haveI : Fact q.val.Prime := ⟨q.2.1⟩; let K := ZMod q.val; ∀(E : Type)[AddCommGroup E][Module K E][Finite E](w : LinearMap.BilinForm K E),w.IsAlt → w.Nondegenerate → 2*d=finrank K E → ∀ L M N : {S : Submodule K E // w.orthogonal S=S},
    let n := fun S : Submodule K E => finrank K S
    let c := n (L.1⊓M.1⊓N.1)
    let b := fun S => (n S-c+1).choose 2
    let a : ℝ := (d+1)*2^d
    (q.val:ℝ)^(3*(d+1).choose 2) ≤ (a*((a*2^d)*(8*(4^d*a^2))))*(q.val:ℝ)^((d+1)*c+(b (L.1⊓M.1)+b (L.1⊓N.1)+b (M.1⊓N.1)))*Nat.card {p : Submodule K E × Submodule K E × Submodule K E // ∃ e : E ≃ₗ[K] E,(∀ x y,w (e x) (e y)=w x y) ∧ L.1.map e.toLinearMap=p.1 ∧ M.1.map e.toLinearMap=p.2.1 ∧ N.1.map e.toLinearMap=p.2.2}

theorem TB2_dim (n : ℕ) (q : OddPrime) : 2*n=finrank (ZMod q.val) ((Fin n → ZMod q.val) × Module.Dual (ZMod q.val) (Fin n → ZMod q.val)) := by
  rw [Module.finrank_prod,Subspace.dual_finrank_eq,Module.finrank_pi,Fintype.card_fin]; omega

theorem OMA.solution : OMA.R_SidorenkoConjecture_sidorenko_conjecture_graphon_R1_H1_R1_H1_R1_H1_R1_H1_R1_H2_R1.H2 := by
  classical
  let r := 2*(T2x64+12)
  have hlarge : T2x64 ≤ 2*r := by dsimp [r]; omega
  refine ⟨2*r, ⟨T2x64+12, by dsimp [r]; omega⟩, by dsimp [r]; omega, ?_⟩
  intro T
  let F := primeInfinity ⊓ principal {q : OddPrime | TB2_good (2*r) q}
  have htq : Tendsto (fun q : OddPrime => (q.val : ℝ)) F atTop := primeInfinity_real_tendsto.mono_left inf_le_left
  have he : 2*r/2 = r := by omega
  change Tendsto (fun q : OddPrime => rawG (2*r) (2*r/2) T (explicitP (ZMod q.val) (2*r))) F (nhds 0)
  simp only [he,TB2_eq]
  have ht := (integratedTailMajorant_tendsto_zero (2*r) r (fun j => decide (T j=Finset.univ)) (singularTailThreshold_large.trans hlarge)).comp htq
  apply squeeze_zero' (Eventually.of_forall (fun q => actualSingularTail_nonneg _ r _ T)) _ ht
  have hgood : ∀ᶠ q in F, TB2_good (2*r) q := Filter.mem_inf_of_right (by exact Filter.mem_principal_self _)
  filter_upwards [htq.eventually (eventually_ge_atTop (4*T2x1 (2*r))), hgood] with q hq hg
  have h2 : (2 : ZMod q.val)≠0 := Ring.two_ne_zero (by simpa only [ZMod.ringChar_zmod_n] using q.property.2)
  let : Invertible (2 : ZMod q.val) := invertibleOfNonzero h2
  let w := T2x5 (K := ZMod q.val) (V := Fin (2*r) → ZMod q.val)
  have hD : 2*(2*r)=finrank (ZMod q.val) ((Fin (2*r) → ZMod q.val) × Module.Dual (ZMod q.val) (Fin (2*r) → ZMod q.val)) := TB2_dim _ _
  have hb : TB2_Good w (2*r) := by
    intro L M N
    simpa only [ZMod.card,orbitMassConstant,pairOrbitConstant,T2x1,tripleDefect,T2x15] using hg _ w canonicalSymplectic_alt T2x35 hD L M N
  have h := actualSingularTail_bound w T2x35 (2*r) hD h2 canonicalSymplectic_alt r rfl hlarge hb (by simpa only [ZMod.card] using hq) verticalLagrangian T
  simpa only [Function.comp_def,ZMod.card] using h
