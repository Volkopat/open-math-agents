import OMAReductions.R_SidorenkoConjecture_sidorenko_conjecture_graphon_R1_H1_R1_H1_R1_H1_R2
import Mathlib
/-! Adapted under Apache-2.0 from openai/math Sidorenko formalization. -/
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
  have hspace := subspace_count_upper (K := K) (V := V) u hu
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
omit [FiniteDimensional K E] in
@[simp] theorem symplecticProjection_apply (x : E) (l : L) :
    symplecticProjection ω L x l = ω l.val x := rfl
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
 theorem graph_pair_intersection_finrank [FiniteDimensional K V] :
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
noncomputable def weightedCombination (t : ι → K) : (ι → W) →ₗ[K] W :=
  ∑ i, t i • LinearMap.proj i
omit [Finite W] in
 theorem weightedCombination_surjective (t : ι → K) (ht : t ≠ 0) :
    Function.Surjective (weightedCombination (W := W) t) := by
  classical
  obtain ⟨i,hi⟩ : ∃ i, t i ≠ 0 := by simpa [funext_iff] using ht
  intro w
  refine ⟨Pi.single i ((t i)⁻¹ • w), ?_⟩
  simp [weightedCombination, Pi.single_apply, hi]
end UniformMaps
section FiniteUnion
variable {T Ω : Type*} [Fintype T] [Finite Ω] [Nonempty Ω]
omit [Nonempty Ω] in
 theorem finite_union_card_bound (A : T → Ω → Prop) :
    Nat.card {x : Ω // ∃ t, A t x} ≤ ∑ t, Nat.card {x : Ω // A t x} := by
  let f : (Σ t : T, {x : Ω // A t x}) → {x : Ω // ∃ t, A t x} :=
    fun x => ⟨x.2.val,⟨x.1,x.2.property⟩⟩
  have hf : Function.Surjective f := by
    rintro ⟨x,t,ht⟩
    exact ⟨⟨t,⟨x,ht⟩⟩,rfl⟩
  exact (Nat.card_le_card_of_surjective f hf).trans_eq Nat.card_sigma
 theorem finite_union_probability_bound (A : T → Ω → Prop) (C : ℝ)
    (hA : ∀ t, (Nat.card {x : Ω // A t x} : ℝ) / Nat.card Ω ≤ C) :
    (Nat.card {x : Ω // ∃ t, A t x} : ℝ) / Nat.card Ω ≤ (Fintype.card T : ℝ)*C := by
  have hc : (0:ℝ) < Nat.card Ω := by exact_mod_cast Nat.card_pos (α := Ω)
  calc
    _ ≤ (∑ t, (Nat.card {x : Ω // A t x} : ℝ)) / Nat.card Ω := by
      apply div_le_div_of_nonneg_right _ hc.le
      exact_mod_cast finite_union_card_bound A
    _ = ∑ t, (Nat.card {x : Ω // A t x} : ℝ) / Nat.card Ω := Finset.sum_div ..
    _ ≤ ∑ _t : T, C := Finset.sum_le_sum (fun t _ => hA t)
    _ = _ := by simp
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
 theorem symmetric_combination_nullity_bound (t : ι → K) (ht : t ≠ 0)
    (u : ℕ) (hu : u ≤ finrank K V) :
    (Nat.card {Q : ι → SymForm K V //
      u ≤ finrank K (weightedCombination t Q).val.ker} : ℝ) /
      Nat.card (ι → SymForm K V) ≤ 2^u / (Fintype.card K : ℝ)^((u+1).choose 2) := by
  rw [surjective_linear_probability (weightedCombination t)
    (weightedCombination_surjective t ht) (fun B : SymForm K V => u ≤ finrank K B.val.ker)]
  exact symmetric_nullity_probability_bound u hu
 theorem symmetric_bad_span_bound (u : ℕ) (hu : u ≤ finrank K V) :
    (Nat.card {Q : ι → SymForm K V // ∃ t : ι → K, t ≠ 0 ∧
      u ≤ finrank K (weightedCombination t Q).val.ker} : ℝ) /
      Nat.card (ι → SymForm K V) ≤
      (Fintype.card K : ℝ)^(Fintype.card ι) *
        (2^u / (Fintype.card K : ℝ)^((u+1).choose 2)) := by
  classical
  let T := {t : ι → K // t ≠ 0}
  have heq : {Q : ι → SymForm K V // ∃ t : ι → K, t ≠ 0 ∧
      u ≤ finrank K (weightedCombination t Q).val.ker} ≃
      {Q : ι → SymForm K V // ∃ t : T,
      u ≤ finrank K (weightedCombination t.val Q).val.ker} :=
    Equiv.subtypeEquiv (Equiv.refl _) (fun Q => by
      constructor
      · rintro ⟨t,ht,h⟩
        exact ⟨⟨t,ht⟩,h⟩
      · rintro ⟨t,h⟩
        exact ⟨t.val,t.property,h⟩)
  rw [Nat.card_congr heq]
  refine (finite_union_probability_bound
    (fun t : T => fun Q : ι → SymForm K V =>
      u ≤ finrank K (weightedCombination t.val Q).val.ker)
    _ (fun t => symmetric_combination_nullity_bound t.val t.property u hu)).trans ?_
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  have hcard : Fintype.card T ≤ Fintype.card (ι → K) := Fintype.card_subtype_le _
  rw [Fintype.card_fun] at hcard
  exact_mod_cast hcard
 theorem symmetric_low_rank_span_bound (s : ℕ) (hs : s ≤ finrank K V) :
    (Nat.card {Q : ι → SymForm K V // ∃ t : ι → K, t ≠ 0 ∧
      finrank K (weightedCombination t Q).val.range ≤ s} : ℝ) /
      Nat.card (ι → SymForm K V) ≤
      (Fintype.card K : ℝ)^(Fintype.card ι) *
        (2^(finrank K V-s) / (Fintype.card K : ℝ)^((finrank K V-s+1).choose 2)) := by
  have heq : {Q : ι → SymForm K V // ∃ t : ι → K, t ≠ 0 ∧
      finrank K (weightedCombination t Q).val.range ≤ s} ≃
      {Q : ι → SymForm K V // ∃ t : ι → K, t ≠ 0 ∧
      finrank K V-s ≤ finrank K (weightedCombination t Q).val.ker} :=
    Equiv.subtypeEquiv (Equiv.refl _) (fun Q => by
      apply exists_congr
      intro t
      change (t ≠ 0 ∧ finrank K (weightedCombination t Q).val.range ≤ s) ↔
        (t ≠ 0 ∧ finrank K V-s ≤ finrank K (weightedCombination t Q).val.ker)
      have h : finrank K (weightedCombination t Q).val.range +
          finrank K (weightedCombination t Q).val.ker = finrank K V :=
        (weightedCombination t Q).val.finrank_range_add_finrank_ker
      apply and_congr_right
      intro ht
      constructor
      · intro hr
        omega
      · intro hk
        omega)
  rw [Nat.card_congr heq]
  exact symmetric_bad_span_bound (finrank K V-s) (Nat.sub_le _ _)
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
 theorem symmetric_form_extend (U : Submodule K V) (B : LinearMap.BilinForm K U)
    (hB : B.IsSymm) :
    ∃ C : LinearMap.BilinForm K V, C.IsSymm ∧ C.compl₁₂ U.subtype U.subtype = B := by
  apply symmetric_form_descend U.subtype B hB
  rw [Submodule.ker_subtype]
  exact bot_le
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
noncomputable def originalCyclicDifference : OriginalForms A₀ A₁ A₂ →ₗ[K]
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
    (originalCyclicDifference A₀ A₁ A₂).comp (ambientRestrictions A₀ A₁ A₂) =
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
    (originalCyclicDifference A₀ A₁ A₂).range = (differenceConstraint A₀ A₁ A₂).ker := by
  have h : (cyclicDifferenceMap A₀ A₁ A₂).range =
      (originalCyclicDifference A₀ A₁ A₂).range := by
    rw [← originalDifference_comp_restriction, LinearMap.range_comp,
      LinearMap.range_eq_top.mpr (ambientRestrictions_surjective A₀ A₁ A₂), Submodule.map_top]
  exact h.symm.trans (cyclicDifference_range A₀ A₁ A₂)
theorem planted_nullity_probability_bound [Fintype K] [Finite V]
    (t₀ t₁ t₂ : ℕ) (h₀ : t₀ ≤ finrank K ↥(A₁ ⊓ A₂))
    (h₁ : t₁ ≤ finrank K ↥(A₂ ⊓ A₀)) (h₂ : t₂ ≤ finrank K ↥(A₀ ⊓ A₁)) :
    (Nat.card {F : OriginalForms A₀ A₁ A₂ //
      t₀ ≤ finrank K (originalCyclicDifference A₀ A₁ A₂ F).1.val.ker ∧
      t₁ ≤ finrank K (originalCyclicDifference A₀ A₁ A₂ F).2.1.val.ker ∧
      t₂ ≤ finrank K (originalCyclicDifference A₀ A₁ A₂ F).2.2.val.ker} : ℝ) /
      Nat.card (OriginalForms A₀ A₁ A₂) ≤
    (Fintype.card K : ℝ)^((finrank K (CommonSpace A₀ A₁ A₂)+1).choose 2) *
      ((2^t₀ / (Fintype.card K : ℝ)^((t₀+1).choose 2)) *
       (2^t₁ / (Fintype.card K : ℝ)^((t₁+1).choose 2)) *
       (2^t₂ / (Fintype.card K : ℝ)^((t₂+1).choose 2))) := by
  have hc := linear_constraint_probability_bound
    (originalCyclicDifference A₀ A₁ A₂) (differenceConstraint A₀ A₁ A₂)
    (differenceConstraint_surjective A₀ A₁ A₂) (originalCyclicDifference_range A₀ A₁ A₂)
    (fun D => t₀ ≤ finrank K D.1.val.ker ∧ t₁ ≤ finrank K D.2.1.val.ker ∧
      t₂ ≤ finrank K D.2.2.val.ker)
  have hp := triple_predicate_probability
    (fun B : SymForm K ↥(A₁ ⊓ A₂) => t₀ ≤ finrank K B.val.ker)
    (fun B : SymForm K ↥(A₂ ⊓ A₀) => t₁ ≤ finrank K B.val.ker)
    (fun B : SymForm K ↥(A₀ ⊓ A₁) => t₂ ≤ finrank K B.val.ker)
  rw [mul_div_assoc, hp, symForm_card, Nat.cast_pow] at hc
  refine hc.trans ?_
  have hb₀ := symmetric_nullity_probability_bound (K := K) (V := ↥(A₁ ⊓ A₂)) t₀ h₀
  have hb₁ := symmetric_nullity_probability_bound (K := K) (V := ↥(A₂ ⊓ A₀)) t₁ h₁
  have hb₂ := symmetric_nullity_probability_bound (K := K) (V := ↥(A₀ ⊓ A₁)) t₂ h₂
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact mul_le_mul (mul_le_mul hb₀ hb₁ (by positivity) (by positivity)) hb₂
    (by positivity) (by positivity)
end OriginalDifferences
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ActualLiftCost
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [Fintype K] [Finite V]
variable (A₀ A₁ A₂ : Submodule K V)
end ActualLiftCost
end SidorenkoCounterexample
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
  · have h := subspace_count_upper (K := K) (V := V ⧸ S) (r-finrank K S) hle
    rw [he] at h
    exact h.trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (Nat.sub_le r _)) (by positivity))
end ContainingSubspaces
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section TripleSubspaces
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
abbrev SubspaceTripleProfile (r p₀ p₁ p₂ : ℕ) :=
  {R : DimSubspace K V r × DimSubspace K V r × DimSubspace K V r //
    (R.1.val ⊓ R.2.1.val) ⊓ R.2.2.val = ⊥ ∧
    finrank K ↥(R.1.val ⊓ R.2.1.val) = p₀ ∧
    finrank K ↥(R.1.val ⊓ R.2.2.val) = p₁ ∧
    finrank K ↥(R.2.1.val ⊓ R.2.2.val) = p₂}
abbrev PairSubspaceConfig (p₀ p₁ p₂ : ℕ) :=
  {P : DimSubspace K V p₀ × DimSubspace K V p₁ × DimSubspace K V p₂ //
    Disjoint P.1.val P.2.1.val ∧ Disjoint P.1.val P.2.2.val ∧ Disjoint P.2.1.val P.2.2.val}
abbrev SubspaceTripleCompletion {p₀ p₁ p₂ : ℕ} (r : ℕ) (P : PairSubspaceConfig (K := K) (V := V) p₀ p₁ p₂) :=
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
    (R : SubspaceTripleProfile (K := K) (V := V) r p₀ p₁ p₂) :
    Σ P : PairSubspaceConfig (K := K) (V := V) p₀ p₁ p₂, SubspaceTripleCompletion r P :=
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
  let f : (Σ P : PairSubspaceConfig (K := K) (V := V) p₀ p₁ p₂, SubspaceTripleCompletion r P) →
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
    (Nat.card (PairSubspaceConfig (K := K) (V := V) p₀ p₁ p₂) : ℝ) ≤
      2^(p₀+p₁+p₂)*(Fintype.card K : ℝ)^(p₀*(finrank K V-p₀)+p₁*(finrank K V-p₁)+p₂*(finrank K V-p₂)) := by
  let : Finite V := Module.finite_of_finite K
  have hc : Nat.card (PairSubspaceConfig (K := K) (V := V) p₀ p₁ p₂) ≤
      Nat.card (DimSubspace K V p₀ × DimSubspace K V p₁ × DimSubspace K V p₂) :=
    Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  have hh : (Nat.card (PairSubspaceConfig (K := K) (V := V) p₀ p₁ p₂) : ℝ) ≤
      (Nat.card (DimSubspace K V p₀) : ℝ) * Nat.card (DimSubspace K V p₁) * Nat.card (DimSubspace K V p₂) := by
    rw [Nat.card_prod, Nat.card_prod] at hc
    exact_mod_cast (hc.trans_eq (Nat.mul_assoc _ _ _).symm)
  calc
    _ ≤ _ := hh
    _ ≤ (2^p₀*(Fintype.card K : ℝ)^(p₀*(finrank K V-p₀))) *
      (2^p₁*(Fintype.card K : ℝ)^(p₁*(finrank K V-p₁))) *
      (2^p₂*(Fintype.card K : ℝ)^(p₂*(finrank K V-p₂))) := by
      exact mul_le_mul (mul_le_mul (subspace_count_upper p₀ h₀) (subspace_count_upper p₁ h₁)
        (by positivity) (by positivity)) (subspace_count_upper p₂ h₂) (by positivity) (by positivity)
    _ = _ := by simp only [pow_add]; ring
 theorem subspaceTripleCompletion_card_upper {p₀ p₁ p₂ : ℕ} (r : ℕ)
    (P : PairSubspaceConfig (K := K) (V := V) p₀ p₁ p₂)
    (hr : r ≤ finrank K V) (h₀ : p₀+p₁ ≤ r) (h₁ : p₀+p₂ ≤ r) (h₂ : p₁+p₂ ≤ r) :
    (Nat.card (SubspaceTripleCompletion r P) : ℝ) ≤
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
  simpa only [SubspaceTripleCompletion,Nat.card_prod,Nat.cast_mul,pow_add,pow_mul,show 3*r=r+r+r by omega,
    mul_assoc,mul_left_comm,mul_comm] using h
noncomputable def subspaceTripleExponent (n r p₀ p₁ p₂ : ℕ) : ℕ :=
  p₀*(n-p₀)+p₁*(n-p₁)+p₂*(n-p₂) +
  ((r-(p₀+p₁))*(n-r)+(r-(p₀+p₂))*(n-r)+(r-(p₁+p₂))*(n-r))
 theorem subspaceTripleProfile_card_upper (r p₀ p₁ p₂ : ℕ)
    (hr : r ≤ finrank K V) (h₀ : p₀+p₁ ≤ r) (h₁ : p₀+p₂ ≤ r) (h₂ : p₁+p₂ ≤ r) :
    (Nat.card (SubspaceTripleProfile (K := K) (V := V) r p₀ p₁ p₂) : ℝ) ≤
      2^(p₀+p₁+p₂+3*r)*(Fintype.card K : ℝ)^(subspaceTripleExponent (finrank K V) r p₀ p₁ p₂) := by
  classical
  let : Finite V := Module.finite_of_finite K
  let := Fintype.ofFinite (PairSubspaceConfig (K := K) (V := V) p₀ p₁ p₂)
  have hc : (Nat.card (SubspaceTripleProfile (K := K) (V := V) r p₀ p₁ p₂) : ℝ) ≤
      Nat.card (Σ P : PairSubspaceConfig (K := K) (V := V) p₀ p₁ p₂, SubspaceTripleCompletion r P) := by
    exact_mod_cast Nat.card_le_card_of_injective _ (subspaceProfile_to_config_injective (K := K) (V := V) r p₀ p₁ p₂)
  let e := (r-(p₀+p₁))*(finrank K V-r)+(r-(p₀+p₂))*(finrank K V-r)+(r-(p₁+p₂))*(finrank K V-r)
  calc
    _ ≤ _ := hc
    _ = ∑ P : PairSubspaceConfig (K := K) (V := V) p₀ p₁ p₂, (Nat.card (SubspaceTripleCompletion r P) : ℝ) := by
      rw [Nat.card_sigma,Nat.cast_sum]
    _ ≤ ∑ _P : PairSubspaceConfig (K := K) (V := V) p₀ p₁ p₂, 2^(3*r)*(Fintype.card K : ℝ)^e :=
      Finset.sum_le_sum (fun P _ => subspaceTripleCompletion_card_upper r P hr h₀ h₁ h₂)
    _ = (Nat.card (PairSubspaceConfig (K := K) (V := V) p₀ p₁ p₂) : ℝ)*(2^(3*r)*(Fintype.card K : ℝ)^e) := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card]
    _ ≤ (2^(p₀+p₁+p₂)*(Fintype.card K : ℝ)^(p₀*(finrank K V-p₀)+p₁*(finrank K V-p₁)+p₂*(finrank K V-p₂))) *
      (2^(3*r)*(Fintype.card K : ℝ)^e) := mul_le_mul_of_nonneg_right
        (pairSubspaceConfig_card_upper p₀ p₁ p₂ (by omega) (by omega) (by omega)) (by positivity)
    _ = _ := by dsimp [e,subspaceTripleExponent]; simp only [pow_add]; ring
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
    (R : SubspaceTripleProfile (K := K) (V := V) r p₀ p₁ p₂)
    (h : R.val.1.val ⊔ R.val.2.1.val ⊔ R.val.2.2.val ≤ Z) :
    SubspaceTripleProfile (K := K) (V := Z) r p₀ p₁ p₂ := by
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
abbrev SubspaceTripleSpanProfile (r p₀ p₁ p₂ n : ℕ) :=
  {R : SubspaceTripleProfile (K := K) (V := V) r p₀ p₁ p₂ //
    finrank K ↥(R.val.1.val ⊔ R.val.2.1.val ⊔ R.val.2.2.val) = n}
noncomputable def spanProfileInjection (r p₀ p₁ p₂ n : ℕ)
    (R : SubspaceTripleSpanProfile (K := K) (V := V) r p₀ p₁ p₂ n) :
    Σ Z : DimSubspace K V n, SubspaceTripleProfile (K := K) (V := Z.val) r p₀ p₁ p₂ :=
  ⟨⟨R.val.val.1.val ⊔ R.val.val.2.1.val ⊔ R.val.val.2.2.val,R.property⟩,
   restrictTripleProfile _ R.val le_rfl⟩
 omit [FiniteDimensional K V] in
 theorem spanProfileInjection_injective (r p₀ p₁ p₂ n : ℕ) :
    Function.Injective (spanProfileInjection (K := K) (V := V) r p₀ p₁ p₂ n) := by
  intro R S h
  let recover : (Σ Z : DimSubspace K V n, SubspaceTripleProfile (K := K) (V := Z.val) r p₀ p₁ p₂) →
      Submodule K V × Submodule K V × Submodule K V := fun ZR =>
    (ZR.2.val.1.val.map ZR.1.val.subtype,ZR.2.val.2.1.val.map ZR.1.val.subtype,
      ZR.2.val.2.2.val.map ZR.1.val.subtype)
  have he (T : SubspaceTripleSpanProfile (K := K) (V := V) r p₀ p₁ p₂ n) :
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
    (Nat.card (SubspaceTripleSpanProfile (K := K) (V := V) r p₀ p₁ p₂ n) : ℝ) ≤
      2^(n+p₀+p₁+p₂+3*r)*(Fintype.card K : ℝ)^
        (n*(finrank K V-n)+subspaceTripleExponent n r p₀ p₁ p₂) := by
  classical
  let : Finite V := Module.finite_of_finite K
  let := Fintype.ofFinite (DimSubspace K V n)
  have hc : (Nat.card (SubspaceTripleSpanProfile (K := K) (V := V) r p₀ p₁ p₂ n) : ℝ) ≤
      Nat.card (Σ Z : DimSubspace K V n, SubspaceTripleProfile (K := K) (V := Z.val) r p₀ p₁ p₂) := by
    exact_mod_cast Nat.card_le_card_of_injective _ (spanProfileInjection_injective (K := K) (V := V) r p₀ p₁ p₂ n)
  calc
    _ ≤ _ := hc
    _ = ∑ Z : DimSubspace K V n, (Nat.card (SubspaceTripleProfile (K := K) (V := Z.val) r p₀ p₁ p₂) : ℝ) := by
      rw [Nat.card_sigma,Nat.cast_sum]
    _ ≤ ∑ _Z : DimSubspace K V n, 2^(p₀+p₁+p₂+3*r)*(Fintype.card K : ℝ)^(subspaceTripleExponent n r p₀ p₁ p₂) := by
      apply Finset.sum_le_sum
      intro Z _
      simpa only [Z.property] using subspaceTripleProfile_card_upper (K := K) (V := Z.val) r p₀ p₁ p₂
        (by simpa only [Z.property] using hr) h₀ h₁ h₂
    _ = (Nat.card (DimSubspace K V n) : ℝ) *
        (2^(p₀+p₁+p₂+3*r)*(Fintype.card K : ℝ)^(subspaceTripleExponent n r p₀ p₁ p₂)) := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card]
    _ ≤ (2^n*(Fintype.card K : ℝ)^(n*(finrank K V-n))) *
        (2^(p₀+p₁+p₂+3*r)*(Fintype.card K : ℝ)^(subspaceTripleExponent n r p₀ p₁ p₂)) :=
      mul_le_mul_of_nonneg_right (subspace_count_upper n hn) (by positivity)
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
    ((n*(d-n)+subspaceTripleExponent n r p₀ p₁ p₂ : ℕ) : ℝ) - (3*r*(d-r) : ℕ) =
      -((d:ℝ)-2*r)*(p₀+p₁+p₂) - ((p₀:ℝ)^2+p₁^2+p₂^2) - ((d:ℝ)-n)*(3*r-n-(p₀+p₁+p₂)) := by
  have hp₀ : p₀ ≤ n := (Nat.le_add_right p₀ p₁).trans (h₀.trans hr)
  have hp₁ : p₁ ≤ n := (Nat.le_add_left p₁ p₀).trans (h₀.trans hr)
  have hp₂ : p₂ ≤ n := (Nat.le_add_left p₂ p₀).trans (h₁.trans hr)
  simp only [subspaceTripleExponent,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,
    Nat.cast_sub hn,Nat.cast_sub hr,Nat.cast_sub (hr.trans hn),
    Nat.cast_sub hp₀,Nat.cast_sub hp₁,Nat.cast_sub hp₂,Nat.cast_sub h₀,Nat.cast_sub h₁,Nat.cast_sub h₂]
  ring
 theorem subspace_span_probability_bound (r p₀ p₁ p₂ n : ℕ)
    (hn : n ≤ finrank K V) (hr : r ≤ n)
    (h₀ : p₀+p₁ ≤ r) (h₁ : p₀+p₂ ≤ r) (h₂ : p₁+p₂ ≤ r) :
    (Nat.card (SubspaceTripleSpanProfile (K := K) (V := V) r p₀ p₁ p₂ n) : ℝ) /
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
  have hdiv : (Nat.card (SubspaceTripleSpanProfile (K := K) (V := V) r p₀ p₁ p₂ n) : ℝ) /
        (Nat.card (DimSubspace K V r) : ℝ)^3 ≤
      (2^(n+p₀+p₁+p₂+3*r)*q^(n*(finrank K V-n)+subspaceTripleExponent n r p₀ p₁ p₂)) /
        q^(3*r*(finrank K V-r)) := by
    exact div_le_div₀ (by positivity) hcount (pow_pos hq _) hden
  refine hdiv.trans_eq ?_
  rw [mul_div_assoc,←Real.rpow_natCast q (n*(finrank K V-n)+subspaceTripleExponent n r p₀ p₁ p₂),
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
  graphLagrangian R.dualCoannihilator B
 theorem dualGraph_vertical_dim (R : Submodule K (Module.Dual K V))
    (B : SymForm K R.dualCoannihilator) :
    finrank K ↥((dualGraph R B).val ⊓ verticalSpace (K := K) (V := V)) = finrank K R := by
  change finrank K ↥(formGraph R.dualCoannihilator B.val ⊓ verticalSpace (K := K) (V := V)) = _
  rw [graph_vertical_intersection_finrank]
  have h := coannihilator_finrank R
  omega
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
 theorem symmetric_nullity_probability_bound_all (t : ℕ) :
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
      t₀ ≤ finrank K (originalCyclicDifference A₀ A₁ A₂ F).1.val.ker ∧
      t₁ ≤ finrank K (originalCyclicDifference A₀ A₁ A₂ F).2.1.val.ker ∧
      t₂ ≤ finrank K (originalCyclicDifference A₀ A₁ A₂ F).2.2.val.ker} : ℝ) /
      Nat.card (OriginalForms A₀ A₁ A₂) ≤
    (Fintype.card K : ℝ)^((finrank K (CommonSpace A₀ A₁ A₂)+1).choose 2) *
      ((2^t₀ / (Fintype.card K : ℝ)^((t₀+1).choose 2)) *
       (2^t₁ / (Fintype.card K : ℝ)^((t₁+1).choose 2)) *
       (2^t₂ / (Fintype.card K : ℝ)^((t₂+1).choose 2))) := by
  have hc := linear_constraint_probability_bound
    (originalCyclicDifference A₀ A₁ A₂) (differenceConstraint A₀ A₁ A₂)
    (differenceConstraint_surjective A₀ A₁ A₂) (originalCyclicDifference_range A₀ A₁ A₂)
    (fun D => t₀ ≤ finrank K D.1.val.ker ∧ t₁ ≤ finrank K D.2.1.val.ker ∧
      t₂ ≤ finrank K D.2.2.val.ker)
  have hp := triple_predicate_probability
    (fun B : SymForm K ↥(A₁ ⊓ A₂) => t₀ ≤ finrank K B.val.ker)
    (fun B : SymForm K ↥(A₂ ⊓ A₀) => t₁ ≤ finrank K B.val.ker)
    (fun B : SymForm K ↥(A₀ ⊓ A₁) => t₂ ≤ finrank K B.val.ker)
  rw [mul_div_assoc, hp, symForm_card, Nat.cast_pow] at hc
  refine hc.trans ?_
  have hb₀ := symmetric_nullity_probability_bound_all (K := K) (V := ↥(A₁ ⊓ A₂)) t₀
  have hb₁ := symmetric_nullity_probability_bound_all (K := K) (V := ↥(A₂ ⊓ A₀)) t₁
  have hb₂ := symmetric_nullity_probability_bound_all (K := K) (V := ↥(A₀ ⊓ A₁)) t₂
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact mul_le_mul (mul_le_mul hb₀ hb₁ (by positivity) (by positivity)) hb₂
    (by positivity) (by positivity)
 theorem lift_pair_profile_probability_bound_all (t₀ t₁ t₂ : ℕ)
 :
    (Nat.card {F : OriginalForms A₀ A₁ A₂ //
      finrank K ↥(A₁.dualAnnihilator ⊓ A₂.dualAnnihilator) + t₀ ≤
        finrank K ↥((graphLagrangian A₁ F.2.1).val ⊓ (graphLagrangian A₂ F.2.2).val) ∧
      finrank K ↥(A₂.dualAnnihilator ⊓ A₀.dualAnnihilator) + t₁ ≤
        finrank K ↥((graphLagrangian A₂ F.2.2).val ⊓ (graphLagrangian A₀ F.1).val) ∧
      finrank K ↥(A₀.dualAnnihilator ⊓ A₁.dualAnnihilator) + t₂ ≤
        finrank K ↥((graphLagrangian A₀ F.1).val ⊓ (graphLagrangian A₁ F.2.1).val)} : ℝ) /
      Nat.card (OriginalForms A₀ A₁ A₂) ≤
    (Fintype.card K : ℝ)^((finrank K (CommonSpace A₀ A₁ A₂)+1).choose 2) *
      ((2^t₀ / (Fintype.card K : ℝ)^((t₀+1).choose 2)) *
       (2^t₁ / (Fintype.card K : ℝ)^((t₁+1).choose 2)) *
       (2^t₂ / (Fintype.card K : ℝ)^((t₂+1).choose 2))) := by
  have he (F : OriginalForms A₀ A₁ A₂) :
      (finrank K ↥(A₁.dualAnnihilator ⊓ A₂.dualAnnihilator) + t₀ ≤
        finrank K ↥((graphLagrangian A₁ F.2.1).val ⊓ (graphLagrangian A₂ F.2.2).val) ∧
      finrank K ↥(A₂.dualAnnihilator ⊓ A₀.dualAnnihilator) + t₁ ≤
        finrank K ↥((graphLagrangian A₂ F.2.2).val ⊓ (graphLagrangian A₀ F.1).val) ∧
      finrank K ↥(A₀.dualAnnihilator ⊓ A₁.dualAnnihilator) + t₂ ≤
        finrank K ↥((graphLagrangian A₀ F.1).val ⊓ (graphLagrangian A₁ F.2.1).val)) ↔
      (t₀ ≤ finrank K (originalCyclicDifference A₀ A₁ A₂ F).1.val.ker ∧
      t₁ ≤ finrank K (originalCyclicDifference A₀ A₁ A₂ F).2.1.val.ker ∧
      t₂ ≤ finrank K (originalCyclicDifference A₀ A₁ A₂ F).2.2.val.ker) := by
    change (_ ≤ finrank K ↥(formGraph A₁ F.2.1.val ⊓ formGraph A₂ F.2.2.val) ∧
      _ ≤ finrank K ↥(formGraph A₂ F.2.2.val ⊓ formGraph A₀ F.1.val) ∧
      _ ≤ finrank K ↥(formGraph A₀ F.1.val ⊓ formGraph A₁ F.2.1.val)) ↔ _
    rw [graph_pair_intersection_finrank,graph_pair_intersection_finrank,graph_pair_intersection_finrank]
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
abbrev DualProfileForms (R : SubspaceTripleSpanProfile (K := K) (V := Module.Dual K V) r p₀ p₁ p₂ n) :=
  OriginalForms R.val.val.1.val.dualCoannihilator R.val.val.2.1.val.dualCoannihilator
    R.val.val.2.2.val.dualCoannihilator
abbrev DualLiftEvent (R : SubspaceTripleSpanProfile (K := K) (V := Module.Dual K V) r p₀ p₁ p₂ n)
    (t₀ t₁ t₂ : ℕ) :=
  {F : DualProfileForms R //
    p₂+t₂ ≤ finrank K ↥((dualGraph R.val.val.2.1.val F.2.1).val ⊓ (dualGraph R.val.val.2.2.val F.2.2).val) ∧
    p₁+t₁ ≤ finrank K ↥((dualGraph R.val.val.2.2.val F.2.2).val ⊓ (dualGraph R.val.val.1.val F.1).val) ∧
    p₀+t₀ ≤ finrank K ↥((dualGraph R.val.val.1.val F.1).val ⊓ (dualGraph R.val.val.2.1.val F.2.1).val)}
 theorem dualProfileForms_card [Fintype K] [Finite V]
    (R : SubspaceTripleSpanProfile (K := K) (V := Module.Dual K V) r p₀ p₁ p₂ n) :
    Nat.card (DualProfileForms R) = (Fintype.card K)^(3*((finrank K V-r+1).choose 2)) := by
  have hdim (S : DimSubspace K (Module.Dual K V) r) : finrank K S.val.dualCoannihilator = finrank K V-r := by
    have h := coannihilator_finrank S.val
    rw [S.property] at h
    omega
  simp only [DualProfileForms,OriginalForms,Nat.card_prod,symForm_card,hdim,←pow_add]
  congr 1
  omega
 theorem dual_lift_probability_bound [Fintype K] [Finite V]
    (R : SubspaceTripleSpanProfile (K := K) (V := Module.Dual K V) r p₀ p₁ p₂ n)
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
    (R : SubspaceTripleSpanProfile (K := K) (V := V) r p₀ p₁ p₂ n) :
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
      finrank K ↥(L.val ⊓ verticalSpace (K := K) (V := V)) = r} : ℝ)^3 =
      (Nat.card (DimSubspace K (Module.Dual K V) r) : ℝ)^3 *
        (Fintype.card K : ℝ)^(3*((finrank K V-r+1).choose 2)) := by
  rw [vertical_pair_count r hr,Nat.cast_mul,Nat.cast_pow,mul_pow,
    Nat.card_congr (dualDimSubspaceEquiv (K := K) (V := V) r hr),←pow_mul,Nat.mul_comm _ 3]
 theorem dual_lift_sum_probability_bound (r p₀ p₁ p₂ n t₀ t₁ t₂ : ℕ) (hr : r ≤ finrank K V) :
    (Nat.card (Σ R : SubspaceTripleSpanProfile (K := K) (V := Module.Dual K V) r p₀ p₁ p₂ n,
      DualLiftEvent R t₀ t₁ t₂) : ℝ) /
      (Nat.card {L : Lagrangian (K := K) (V := V) //
        finrank K ↥(L.val ⊓ verticalSpace (K := K) (V := V)) = r} : ℝ)^3 ≤
    ((Nat.card (SubspaceTripleSpanProfile (K := K) (V := Module.Dual K V) r p₀ p₁ p₂ n) : ℝ) /
      (Nat.card (DimSubspace K (Module.Dual K V) r) : ℝ)^3) *
    (2^(t₀+t₁+t₂) * (Fintype.card K : ℝ)^((finrank K V-n+1).choose 2) /
      (Fintype.card K : ℝ)^((t₀+1).choose 2+(t₁+1).choose 2+(t₂+1).choose 2)) := by
  classical
  let : Finite (Module.Dual K V) := Module.finite_of_finite K
  let RType := SubspaceTripleSpanProfile (K := K) (V := Module.Dual K V) r p₀ p₁ p₂ n
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
abbrev CenterStratum (r : ℕ) := {L : Lagrangian (K := K) (V := V) //
  finrank K ↥(L.val ⊓ verticalSpace (K := K) (V := V)) = r}
noncomputable def dualPairStratumEquiv (r : ℕ) (hr : r ≤ finrank K V) :
    (Σ R : DimSubspace K (Module.Dual K V) r, SymForm K R.val.dualCoannihilator) ≃
      CenterStratum (K := K) (V := V) r :=
  (Equiv.sigmaCongrLeft (β := fun U : DimSubspace K V (finrank K V-r) => SymForm K U.val)
    (dualDimSubspaceEquiv (K := K) (V := V) r hr).symm).trans (pairStratumEquiv r hr)
 theorem dualPairStratumEquiv_apply (r : ℕ) (hr : r ≤ finrank K V)
    (R : DimSubspace K (Module.Dual K V) r) (F : SymForm K R.val.dualCoannihilator) :
    (dualPairStratumEquiv r hr ⟨R,F⟩).val = dualGraph R.val F := rfl
abbrev DualBaseTriple (r : ℕ) := DimSubspace K (Module.Dual K V) r ×
  DimSubspace K (Module.Dual K V) r × DimSubspace K (Module.Dual K V) r
abbrev DualBaseForms {r : ℕ} (R : DualBaseTriple (K := K) (V := V) r) :=
  OriginalForms R.1.val.dualCoannihilator R.2.1.val.dualCoannihilator R.2.2.val.dualCoannihilator
noncomputable def dualBaseTripleGraph {r : ℕ} (R : DualBaseTriple (K := K) (V := V) r)
    (F : DualBaseForms R) : Lagrangian (K := K) (V := V) × Lagrangian (K := K) (V := V) × Lagrangian (K := K) (V := V) :=
  (dualGraph R.1.val F.1,dualGraph R.2.1.val F.2.1,dualGraph R.2.2.val F.2.2)
noncomputable def dualTripleStratumEquiv (r : ℕ) (hr : r ≤ finrank K V) :
    (Σ R : DualBaseTriple (K := K) (V := V) r, DualBaseForms R) ≃
      CenterStratum (K := K) (V := V) r × CenterStratum (K := K) (V := V) r × CenterStratum (K := K) (V := V) r :=
  let e : (Σ R : DualBaseTriple (K := K) (V := V) r, DualBaseForms R) ≃
      (Σ R : DimSubspace K (Module.Dual K V) r, SymForm K R.val.dualCoannihilator) ×
      (Σ R : DimSubspace K (Module.Dual K V) r, SymForm K R.val.dualCoannihilator) ×
      (Σ R : DimSubspace K (Module.Dual K V) r, SymForm K R.val.dualCoannihilator) :=
    { toFun := fun RF => (⟨RF.1.1,RF.2.1⟩,⟨RF.1.2.1,RF.2.2.1⟩,⟨RF.1.2.2,RF.2.2.2⟩)
      invFun := fun p => ⟨(p.1.1,p.2.1.1,p.2.2.1),(p.1.2,p.2.1.2,p.2.2.2)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  e.trans ((dualPairStratumEquiv r hr).prodCongr ((dualPairStratumEquiv r hr).prodCongr (dualPairStratumEquiv r hr)))
 theorem dualTripleStratumEquiv_graph (r : ℕ) (hr : r ≤ finrank K V)
    (RF : Σ R : DualBaseTriple (K := K) (V := V) r, DualBaseForms R) :
    ((dualTripleStratumEquiv r hr RF).1.val,(dualTripleStratumEquiv r hr RF).2.1.val,
      (dualTripleStratumEquiv r hr RF).2.2.val) = dualBaseTripleGraph RF.1 RF.2 := rfl
 theorem dualGraph_pair_finrank_ge (R S : Submodule K (Module.Dual K V))
    (F : SymForm K R.dualCoannihilator) (G : SymForm K S.dualCoannihilator) :
    finrank K ↥(R ⊓ S) ≤ finrank K ↥((dualGraph R F).val ⊓ (dualGraph S G).val) := by
  change _ ≤ finrank K ↥(formGraph R.dualCoannihilator F.val ⊓ formGraph S.dualCoannihilator G.val)
  rw [graph_pair_intersection_finrank,
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
  rw [graph_pair_intersection_finrank,
    Subspace.dualCoannihilator_dualAnnihilator_eq,Subspace.dualCoannihilator_dualAnnihilator_eq]
  exact Nat.add_le_add_left (Submodule.finrank_le _) _
 theorem dualGraph_pair_extra_feasible {r s : ℕ} (R S : DimSubspace K (Module.Dual K V) r)
    (F : SymForm K R.val.dualCoannihilator) (G : SymForm K S.val.dualCoannihilator)
    (hs : finrank K ↥((dualGraph R.val F).val ⊓ (dualGraph S.val G).val) = s) :
    (s-finrank K ↥(R.val ⊓ S.val))+2*r ≤ finrank K V+finrank K ↥(R.val ⊓ S.val) := by
  have h₁ := dualGraph_pair_finrank_ge R.val S.val F G
  have h₂ := dualGraph_pair_finrank_le R.val S.val F G
  have h₃ := coannihilator_pair_finrank R.val S.val
  rw [hs] at h₁ h₂
  rw [R.property,S.property] at h₃
  omega
 theorem dual_common_pair_extra_feasible {r p₀ p₁ p₂ n : ℕ}
    (R : SubspaceTripleSpanProfile (K := K) (V := Module.Dual K V) r p₀ p₁ p₂ n) :
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
    SubspaceTripleSpanProfile (K := K) (V := Module.Dual K V) r
      (canonicalLiftFourDims P).1.val (canonicalLiftFourDims P).2.1.val
      (canonicalLiftFourDims P).2.2.1.val (canonicalLiftFourDims P).2.2.2.val :=
  ⟨⟨P.val.1,dualGraph_common_zero _ _ _ P.val.2 P.property.1,rfl,rfl,rfl⟩,rfl⟩
 theorem canonicalLift_feasible {r s₀ s₁ s₂ : ℕ}
    (P : CanonicalLiftProfile (K := K) (V := V) r s₀ s₁ s₂) :
    BaseFeasible r s₀ s₁ s₂ (canonicalLiftFourDims P) := by
  have hc := subspace_profile_constraints (canonicalLiftSubspaces P)
  refine ⟨hc.2.1,hc.2.2.1,hc.2.2.2.1,hc.2.2.2.2.1,hc.2.2.2.2.2,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (dualGraph_pair_finrank_ge _ _ P.val.2.1 P.val.2.2.1).trans_eq P.property.2.1
  · exact (dualGraph_pair_finrank_ge _ _ P.val.2.1 P.val.2.2.2).trans_eq P.property.2.2.1
  · exact (dualGraph_pair_finrank_ge _ _ P.val.2.2.1 P.val.2.2.2).trans_eq P.property.2.2.2
  · exact dualGraph_pair_extra_feasible P.val.1.1 P.val.1.2.1 P.val.2.1 P.val.2.2.1 P.property.2.1
  · exact dualGraph_pair_extra_feasible P.val.1.1 P.val.1.2.2 P.val.2.1 P.val.2.2.2 P.property.2.2.1
  · exact dualGraph_pair_extra_feasible P.val.1.2.1 P.val.1.2.2 P.val.2.2.1 P.val.2.2.2 P.property.2.2.2
  · exact dual_common_pair_extra_feasible (canonicalLiftSubspaces P)
 theorem dualGraph_pair_gap_bound (R S : Submodule K (Module.Dual K V))
    (F : SymForm K R.dualCoannihilator) (G : SymForm K S.dualCoannihilator)
    {p s : ℕ} (hp : finrank K ↥(R ⊓ S) = p)
    (hs : finrank K ↥((dualGraph R F).val ⊓ (dualGraph S G).val) = s) :
    p+(s-p) ≤ finrank K ↥((dualGraph R F).val ⊓ (dualGraph S G).val) := by
  have h := dualGraph_pair_finrank_ge R S F G
  rw [hp,hs] at h
  rw [hs]
  omega
noncomputable def dualLift_of_exactDims {r p₀ p₁ p₂ n s₀ s₁ s₂ : ℕ}
    (R : SubspaceTripleSpanProfile (K := K) (V := Module.Dual K V) r p₀ p₁ p₂ n)
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
      Σ R : SubspaceTripleSpanProfile (K := K) (V := Module.Dual K V)
        r θ.val.1.val θ.val.2.1.val θ.val.2.2.1.val θ.val.2.2.2.val,
        DualLiftEvent R (s₀-θ.val.1.val) (s₁-θ.val.2.1.val) (s₂-θ.val.2.2.1.val) :=
  ⟨⟨canonicalLiftFourDims P,canonicalLift_feasible P⟩,canonicalLiftSubspaces P,
    dualLift_of_exactDims (canonicalLiftSubspaces P) P.val.2 P.property.2.1 P.property.2.2.1 P.property.2.2.2⟩
 theorem canonicalLiftCoding_injective (r s₀ s₁ s₂ : ℕ) :
    Function.Injective (canonicalLiftCoding (K := K) (V := V) (r := r) (s₀ := s₀) (s₁ := s₁) (s₂ := s₂)) := by
  let recover : (Σ θ : BaseParameters (finrank K V) r s₀ s₁ s₂,
      Σ R : SubspaceTripleSpanProfile (K := K) (V := Module.Dual K V)
        r θ.val.1.val θ.val.2.1.val θ.val.2.2.1.val θ.val.2.2.2.val,
        DualLiftEvent R (s₀-θ.val.1.val) (s₁-θ.val.2.1.val) (s₂-θ.val.2.2.1.val)) →
      Σ R : DualBaseTriple (K := K) (V := V) r, DualBaseForms R :=
    fun T => ⟨T.2.1.val.val,T.2.2.val⟩
  intro P Q h
  exact Subtype.ext (congrArg recover h)
abbrev CenterTripleProfile (r s₀ s₁ s₂ : ℕ) :=
  {L : CenterStratum (K := K) (V := V) r × CenterStratum (K := K) (V := V) r × CenterStratum (K := K) (V := V) r //
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
def reducedPlantedExponent (d r s₀ s₁ s₂ : ℕ) (θ : FourDims d) : ℝ :=
  -((d:ℝ)-2*r)*(θ.1.val+θ.2.1.val+θ.2.2.1.val) -
    ((θ.1.val:ℝ)^2+θ.2.1.val^2+θ.2.2.1.val^2) -
    ((d:ℝ)-θ.2.2.2.val)*(3*r-θ.2.2.2.val-(θ.1.val+θ.2.1.val+θ.2.2.1.val)) +
    ((d-θ.2.2.2.val+1).choose 2 : ℕ) -
    (((s₀-θ.1.val+1).choose 2+(s₁-θ.2.1.val+1).choose 2+(s₂-θ.2.2.1.val+1).choose 2 : ℕ) : ℝ)
def reducedPlantedConstant (r s₀ s₁ s₂ : ℕ) {d : ℕ} (θ : FourDims d) : ℝ :=
  2^(θ.2.2.2.val+θ.1.val+θ.2.1.val+θ.2.2.1.val+3*r+(s₀-θ.1.val)+(s₁-θ.2.1.val)+(s₂-θ.2.2.1.val))
section CanonicalNumericalBound
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype K] [Finite V]
 theorem reducedPlanted_bound_one (r s₀ s₁ s₂ : ℕ)
    (θ : BaseParameters (finrank K V) r s₀ s₁ s₂) :
    (Nat.card (Σ R : SubspaceTripleSpanProfile (K := K) (V := Module.Dual K V)
        r θ.val.1.val θ.val.2.1.val θ.val.2.2.1.val θ.val.2.2.2.val,
        DualLiftEvent R (s₀-θ.val.1.val) (s₁-θ.val.2.1.val) (s₂-θ.val.2.2.1.val)) : ℝ) /
      (Nat.card (CenterStratum (K := K) (V := V) r) : ℝ)^3 ≤
    reducedPlantedConstant r s₀ s₁ s₂ θ.val *
      (Fintype.card K : ℝ)^(reducedPlantedExponent (finrank K V) r s₀ s₁ s₂ θ.val) := by
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
  have he : reducedPlantedExponent (finrank K V) r s₀ s₁ s₂ θ.val =
      e+((finrank K V-n+1).choose 2 : ℕ)-(((t₀+1).choose 2+(t₁+1).choose 2+(t₂+1).choose 2 : ℕ) : ℝ) := rfl
  rw [he,Real.rpow_sub hq (e+((finrank K V-n+1).choose 2 : ℕ))
    (((t₀+1).choose 2+(t₁+1).choose 2+(t₂+1).choose 2 : ℕ) : ℝ),
    Real.rpow_add hq e ((finrank K V-n+1).choose 2 : ℕ),Real.rpow_natCast,Real.rpow_natCast]
  simp only [reducedPlantedConstant, pow_add]
  change _ = 2^n*2^p₀*2^p₁*2^p₂*2^(3*r)*2^t₀*2^t₁*2^t₂ * _
  ring
 theorem canonical_center_profile_probability_bound (r s₀ s₁ s₂ : ℕ) (hr : r ≤ finrank K V) :
    (Nat.card (CenterTripleProfile (K := K) (V := V) r s₀ s₁ s₂) : ℝ) /
      (Nat.card (CenterStratum (K := K) (V := V) r) : ℝ)^3 ≤
    ∑ θ : BaseParameters (finrank K V) r s₀ s₁ s₂,
      reducedPlantedConstant r s₀ s₁ s₂ θ.val *
        (Fintype.card K : ℝ)^(reducedPlantedExponent (finrank K V) r s₀ s₁ s₂ θ.val) := by
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
theorem liftReduction_le (T : Submodule K (ReducedSpace ω S)) :
    liftReduction ω S T ≤ ω.orthogonal S := by
  rintro x ⟨y,hy,rfl⟩
  exact y.property
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
theorem reduced_pair_transverse (hS : S ≤ ω.orthogonal S)
    (L M : Submodule K E) (hL : ω.orthogonal L = L) (hM : ω.orthogonal M = M)
    (hLM : L ⊓ M = S) :
    reduceSubspace ω S L ⊓ reduceSubspace ω S M = ⊥ := by
  have hSL : S ≤ L := hLM.ge.trans inf_le_left
  have hSM : S ≤ M := hLM.ge.trans inf_le_right
  apply liftReduction_injective ω S
  rw [liftReduction_inf,lift_reduce ω S L hSL (lagrangian_le_orthogonal ω S L hL hSL),
    lift_reduce ω S M hSM (lagrangian_le_orthogonal ω S M hM hSM),
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
  let Ω := symplecticReductionForm ω S ha
  have hΩa : Ω.IsAlt := symplecticReductionForm_alt ω S ha
  have hΩ : Ω.Nondegenerate := symplecticReductionForm_nondegenerate ω S ha hω
  obtain ⟨f,hf,hfL,hfM⟩ := transverse_pair_transitivity Ω hΩa hΩ
    (reduceSubspace ω S L) (reduceSubspace ω S M)
    (reduceSubspace ω S L') (reduceSubspace ω S M')
    (reduce_lagrangian ω S ha hS L hL hSL)
    (reduce_lagrangian ω S ha hS M hM hSM)
    (reduce_lagrangian ω S ha hS L' hL' hSL')
    (reduce_lagrangian ω S ha hS M' hM' hSM')
    (reduced_pair_transverse ω S hS L M hL hM hLM)
    (reduced_pair_transverse ω S hS L' M' hL' hM' hLM')
  obtain ⟨e,he,heS,heP,heQ⟩ := exists_reduction_isometry_extension ω S ha hω f hf
  have hSe : S.map e.toLinearMap = S := subspace_map_eq_of_fixed e S heS
  have hPe : (ω.orthogonal S).map e.toLinearMap = ω.orthogonal S := by
    rw [← orthogonal_map_of_isometry ω e he,hSe]
  have hmap (U W : Submodule K E) (hU : ω.orthogonal U = U)
      (hW : ω.orthogonal W = W) (hSU : S ≤ U) (hSW : S ≤ W)
      (hfU : (reduceSubspace ω S U).map f.toLinearMap = reduceSubspace ω S W) :
      U.map e.toLinearMap = W := by
    have hSUe : S ≤ U.map e.toLinearMap := by
      rw [← hSe]
      exact Submodule.map_mono hSU
    have hUe : ω.orthogonal (U.map e.toLinearMap) = U.map e.toLinearMap := by
      rw [orthogonal_map_of_isometry ω e he,hU]
    calc
      U.map e.toLinearMap = liftReduction ω S (reduceSubspace ω S (U.map e.toLinearMap)) :=
        (lift_reduce ω S _ hSUe (lagrangian_le_orthogonal ω S _ hUe hSUe)).symm
      _ = liftReduction ω S (reduceSubspace ω S W) := by
        rw [reduceSubspace_map ω S e f hPe heQ,hfU]
      _ = W := lift_reduce ω S W hSW (lagrangian_le_orthogonal ω S W hW hSW)
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
    rw [orthogonal_map_of_isometry ω e0 he0,hL]
  have hMe : ω.orthogonal (M.map e0.toLinearMap) = M.map e0.toLinearMap := by
    rw [orthogonal_map_of_isometry ω e0 he0,hM]
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
theorem exists_reduction_isometry_between
    (ω : LinearMap.BilinForm K E) (η : LinearMap.BilinForm K F)
    (ha : ω.IsAlt) (hb : η.IsAlt) (e : E ≃ₗ[K] F)
    (he : ∀ x y, η (e x) (e y) = ω x y)
    (S : Submodule K E) (T : Submodule K F) (hST : S.map e.toLinearMap = T) :
    ∃ f : ReducedSpace ω S ≃ₗ[K] ReducedSpace η T,
      (∀ x y, symplecticReductionForm η T hb (f x) (f y) =
        symplecticReductionForm ω S ha x y) ∧
      ∀ L : Submodule K E,
        (reduceSubspace ω S L).map f.toLinearMap = reduceSubspace η T (L.map e.toLinearMap) := by
  have hP : (ω.orthogonal S).map e.toLinearMap = η.orthogonal T := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩ t ht
      rw [←hST] at ht
      obtain ⟨s,hs,rfl⟩ := ht
      change η (e s) (e x) = 0
      rw [he]
      exact hx s hs
    · intro hy
      refine ⟨e.symm y,?_,e.apply_symm_apply y⟩
      intro s hs
      rw [←he,e.apply_symm_apply]
      exact hy (e s) (hST.le ⟨s,hs,rfl⟩)
  let p : ω.orthogonal S ≃ₗ[K] η.orthogonal T := e.ofSubmodules _ _ hP
  have hp (x : ω.orthogonal S) : (p x).val = e x.val := rfl
  have hker : (reductionKernel ω S).map p.toLinearMap = reductionKernel η T := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact hST.le ⟨x.val,hx,rfl⟩
    · intro hy
      obtain ⟨x,rfl⟩ := p.surjective y
      have hex : e x.val ∈ T := hy
      rw [←hST] at hex
      obtain ⟨s,hs,hse⟩ := hex
      have hsx : s = x.val := e.injective hse
      refine ⟨x,?_,rfl⟩
      change x.val ∈ S
      exact hsx ▸ hs
  let f := Submodule.Quotient.equiv (reductionKernel ω S) (reductionKernel η T) p hker
  have hf (x : ω.orthogonal S) : f ((reductionKernel ω S).mkQ x) =
      (reductionKernel η T).mkQ (p x) := rfl
  refine ⟨f,?_,?_⟩
  · intro x y
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      induction y using Submodule.Quotient.induction_on with
      | H y => exact he x.val y.val
  · intro L
    ext z
    constructor
    · rintro ⟨y,⟨x,hx,rfl⟩,rfl⟩
      refine ⟨p x,?_,rfl⟩
      exact ⟨x.val,hx,rfl⟩
    · rintro ⟨y,hy,rfl⟩
      obtain ⟨x,rfl⟩ := p.surjective y
      obtain ⟨l,hl,hlx⟩ := hy
      have hlx' : l = x.val := e.injective hlx
      refine ⟨(reductionKernel ω S).mkQ x,⟨x,?_,rfl⟩,rfl⟩
      change x.val ∈ L
      exact hlx' ▸ hl
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
      Finset.prod_le_prod' (fun i _ => hfac i)
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
theorem fixedPairOrbit_selforthogonal (hN : ω.orthogonal N = N)
    (N' : FixedPairOrbit ω L M N) : ω.orthogonal N'.val = N'.val := by
  obtain ⟨e,he,_,_,hne⟩ := N'.property
  rw [←hne,orthogonal_map_of_isometry ω e he,hN]
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
abbrev PairLinearOrbit (U V : Submodule K E) :=
  {p : Submodule K E × Submodule K E // ∃ e : E ≃ₗ[K] E,
    U.map e.toLinearMap = p.1 ∧ V.map e.toLinearMap = p.2}
abbrev PairLinearStabilizer (U V : Submodule K E) :=
  {e : E ≃ₗ[K] E // U.map e.toLinearMap = U ∧ V.map e.toLinearMap = V}
def pairLinearOrbitMap (U V : Submodule K E) (e : E ≃ₗ[K] E) : PairLinearOrbit U V :=
  ⟨(U.map e.toLinearMap,V.map e.toLinearMap),e,rfl,rfl⟩
 theorem submodule_map_trans (U : Submodule K E) (e f : E ≃ₗ[K] E) :
    U.map (e.trans f).toLinearMap = (U.map e.toLinearMap).map f.toLinearMap := by
  exact Submodule.map_comp _ _ _
 theorem submodule_map_symm_cancel (U : Submodule K E) (e : E ≃ₗ[K] E) :
    (U.map e.toLinearMap).map e.symm.toLinearMap = U := by
  rw [←Submodule.map_comp]
  simp
noncomputable def pairLinearOrbitFiberEquiv (U V : Submodule K E) (p : PairLinearOrbit U V) :
    {e : E ≃ₗ[K] E // pairLinearOrbitMap U V e = p} ≃ PairLinearStabilizer U V := by
  classical
  let e₀ := p.property.choose
  have hU := p.property.choose_spec.1
  have hV := p.property.choose_spec.2
  have hm (e : {e : E ≃ₗ[K] E // pairLinearOrbitMap U V e = p}) :
      U.map e.val.toLinearMap = p.val.1 ∧ V.map e.val.toLinearMap = p.val.2 := by
    exact ⟨congrArg (fun a : PairLinearOrbit U V => a.val.1) e.property,
      congrArg (fun a : PairLinearOrbit U V => a.val.2) e.property⟩
  refine
    { toFun := fun e => ⟨e.val.trans e₀.symm,?_,?_⟩
      invFun := fun e => ⟨e.val.trans e₀,?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · rw [submodule_map_trans,(hm _).1,←hU,submodule_map_symm_cancel]
  · rw [submodule_map_trans,(hm _).2,←hV,submodule_map_symm_cancel]
  · apply Subtype.ext
    apply Prod.ext
    · change U.map (‹PairLinearStabilizer U V›.val.trans e₀).toLinearMap = p.val.1
      rw [submodule_map_trans]
      exact (congrArg (Submodule.map e₀.toLinearMap) ‹PairLinearStabilizer U V›.property.1).trans hU
    · change V.map (‹PairLinearStabilizer U V›.val.trans e₀).toLinearMap = p.val.2
      rw [submodule_map_trans]
      exact (congrArg (Submodule.map e₀.toLinearMap) ‹PairLinearStabilizer U V›.property.2).trans hV
  · intro e
    apply Subtype.ext
    ext x
    simp
  · intro e
    apply Subtype.ext
    ext x
    simp
noncomputable def pairLinearStabilizerRestriction (U V : Submodule K E) :
    PairLinearStabilizer U V → (U ≃ₗ[K] U) × (V ≃ₗ[K] V) := fun e =>
  (e.val.ofSubmodules U U e.property.1,e.val.ofSubmodules V V e.property.2)
 theorem pairLinearStabilizerRestriction_bijective (U V : Submodule K E) (hUV : IsCompl U V) :
    Function.Bijective (pairLinearStabilizerRestriction U V) := by
  constructor
  · intro e f hh
    apply Subtype.ext
    ext x
    have hx : x ∈ U ⊔ V := by rw [hUV.sup_eq_top]; trivial
    obtain ⟨u,hu,v,hv,rfl⟩ := Submodule.mem_sup.mp hx
    have hU := congrArg (fun p : (U ≃ₗ[K] U) × (V ≃ₗ[K] V) => (p.1 ⟨u,hu⟩).val) hh
    have hV := congrArg (fun p : (U ≃ₗ[K] U) × (V ≃ₗ[K] V) => (p.2 ⟨v,hv⟩).val) hh
    change e.val u = f.val u at hU
    change e.val v = f.val v at hV
    simp only [map_add,hU,hV]
  · intro g
    let c := Submodule.prodEquivOfIsCompl U V hUV
    let e : E ≃ₗ[K] E := c.symm.trans ((g.1.prodCongr g.2).trans c)
    have heU (u : U) : e u.val = (g.1 u).val := by
      have hc : c (u,0) = u.val := by simp [c]
      change c ((g.1.prodCongr g.2) (c.symm u.val)) = _
      rw [←hc,c.symm_apply_apply]
      simp [c]
    have heV (v : V) : e v.val = (g.2 v).val := by
      have hc : c (0,v) = v.val := by simp [c]
      change c ((g.1.prodCongr g.2) (c.symm v.val)) = _
      rw [←hc,c.symm_apply_apply]
      simp [c]
    have hU : U.map e.toLinearMap = U := by
      ext x
      constructor
      · rintro ⟨u,hu,rfl⟩
        change e u ∈ U
        rw [heU ⟨u,hu⟩]
        exact (g.1 ⟨u,hu⟩).property
      · intro hx
        refine ⟨(g.1.symm ⟨x,hx⟩).val,(g.1.symm ⟨x,hx⟩).property,?_⟩
        exact (heU _).trans (congrArg Subtype.val (g.1.apply_symm_apply ⟨x,hx⟩))
    have hV : V.map e.toLinearMap = V := by
      ext x
      constructor
      · rintro ⟨v,hv,rfl⟩
        change e v ∈ V
        rw [heV ⟨v,hv⟩]
        exact (g.2 ⟨v,hv⟩).property
      · intro hx
        refine ⟨(g.2.symm ⟨x,hx⟩).val,(g.2.symm ⟨x,hx⟩).property,?_⟩
        exact (heV _).trans (congrArg Subtype.val (g.2.apply_symm_apply ⟨x,hx⟩))
    refine ⟨⟨e,hU,hV⟩,?_⟩
    apply Prod.ext
    · ext u
      exact heU u
    · ext v
      exact heV v
variable [Fintype K] [Finite E]
 omit [Fintype K] in
 theorem pairLinearOrbit_card_identity (U V : Submodule K E) (hUV : IsCompl U V) :
    Nat.card (PairLinearOrbit U V) *
      (Nat.card (U ≃ₗ[K] U)*Nat.card (V ≃ₗ[K] V)) = Nat.card (E ≃ₗ[K] E) := by
  classical
  let := Fintype.ofFinite (PairLinearOrbit U V)
  have hc : Nat.card (PairLinearStabilizer U V) =
      Nat.card (U ≃ₗ[K] U)*Nat.card (V ≃ₗ[K] V) := by
    rw [Nat.card_congr (Equiv.ofBijective _ (pairLinearStabilizerRestriction_bijective U V hUV)),Nat.card_prod]
  have he := (Nat.card_congr (Equiv.sigmaFiberEquiv (pairLinearOrbitMap U V))).symm
  rw [Nat.card_sigma] at he
  have hf (p : PairLinearOrbit U V) : Nat.card {e : E ≃ₗ[K] E // pairLinearOrbitMap U V e = p} =
      Nat.card (U ≃ₗ[K] U)*Nat.card (V ≃ₗ[K] V) :=
    (Nat.card_congr (pairLinearOrbitFiberEquiv U V p)).trans hc
  simpa only [hf,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card,Nat.cast_id] using he.symm
 theorem linearAut_card_upper : Nat.card (E ≃ₗ[K] E) ≤
    Fintype.card K ^ (finrank K E * finrank K E) := by
  rw [linearAut_card]
  calc
    _ ≤ ∏ _i : Fin (finrank K E), Fintype.card K ^ finrank K E :=
      Finset.prod_le_prod' (fun i _ => Nat.sub_le _ _)
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
 theorem triple_subspace_orbit_surjection (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (S U V W : Submodule K E) (hS : S ≤ ω.orthogonal S)
    (hU : U ≤ S) (hV : V ≤ S) (hW : W ≤ S) (_hsum : U ⊔ V ⊔ W = S) :
    ∃ f : IsotropicDimspace ω (finrank K S) ×
      TripleLinearOrbit (U.comap S.subtype) (V.comap S.subtype) (W.comap S.subtype) →
        OrderedTripleOrbit ω U V W, Function.Surjective f := by
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
  refine ⟨f,?_⟩
  intro p
  obtain ⟨g,hg,hgU,hgV,hgW⟩ := p.property
  have hT : S.map g.toLinearMap ≤ ω.orthogonal (S.map g.toLinearMap) := by
    rw [orthogonal_map_of_isometry ω g hg]
    exact Submodule.map_mono hS
  let T : IsotropicDimspace ω (finrank K S) :=
    ⟨S.map g.toLinearMap,hT,g.finrank_map_eq S⟩
  let r := g.trans (e T).symm
  have hrS : S.map r.toLinearMap = S := by
    rw [submodule_map_trans]
    change T.val.map (e T).symm.toLinearMap = S
    rw [←(he T).2,submodule_map_symm_cancel]
  let rS : S ≃ₗ[K] S := r.ofSubmodules S S hrS
  let q := tripleLinearOrbitMap (U.comap S.subtype) (V.comap S.subtype) (W.comap S.subtype) rS
  have heq : r.trans (e T) = g := by
    ext x
    simp only [r,LinearEquiv.trans_apply,LinearEquiv.apply_symm_apply]
  have hmap (A : Submodule K E) (hA : A ≤ S) :
      ((((A.comap S.subtype).map rS.toLinearMap).map S.subtype).map (e T).toLinearMap) = A.map g.toLinearMap := by
    rw [←subspace_map_extension S S A hA r rS (fun _ => rfl),←submodule_map_trans,heq]
  refine ⟨(T,q),Subtype.ext ?_⟩
  change (((((U.comap S.subtype).map rS.toLinearMap).map S.subtype).map (e T).toLinearMap),
    ((((V.comap S.subtype).map rS.toLinearMap).map S.subtype).map (e T).toLinearMap),
    ((((W.comap S.subtype).map rS.toLinearMap).map S.subtype).map (e T).toLinearMap)) = p.val
  rw [hmap U hU,hmap V hV,hmap W hW,hgU,hgV,hgW]
 theorem triple_subspace_orbit_card_identity (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (S U V W : Submodule K E) (hS : S ≤ ω.orthogonal S)
    (hU : U ≤ S) (hV : V ≤ S) (hW : W ≤ S) (hsum : U ⊔ V ⊔ W = S) :
    Nat.card (OrderedTripleOrbit ω U V W) = Nat.card (IsotropicDimspace ω (finrank K S)) *
      Nat.card (TripleLinearOrbit (U.comap S.subtype) (V.comap S.subtype) (W.comap S.subtype)) := by
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
  · rw [subspace_map_extension S T U hU e g heg,hgU,subtype_map_comap_of_le T U' hU']
  · rw [subspace_map_extension S T V hV e g heg,hgV,subtype_map_comap_of_le T V' hV']
  · rw [subspace_map_extension S T W hW e g heg,hgW,subtype_map_comap_of_le T W' hW']
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
    (Nat.card (OrderedTripleOrbit ω U V W) : ℝ) ≤
      (lagrangianConstant D * 4^D) * (Fintype.card K : ℝ)^(isotropicExponent D (finrank K S) +
        2*(finrank K U*finrank K V+finrank K U*finrank K W+finrank K V*finrank K W)) := by
  have hconst := lagrangianConstant_pos D
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
  have hs := isotropic_finrank_le_half ω hω D hD S hS
  have hi := (isotropic_card_bounds ω h2 ha hω D hD (finrank K S) hs).2
  have hk : (2:ℝ)^(finrank K S) * 2^(finrank K S) ≤ 4^D := by
    calc
      _ = (4:ℝ)^(finrank K S) := by rw [←mul_pow]; norm_num
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) hs
  rw [triple_subspace_orbit_card_identity ω h2 ha hω S U V W hS hU hV hW hsum,Nat.cast_mul]
  calc
    _ ≤ ((lagrangianConstant D*2^(finrank K S))*(Fintype.card K : ℝ)^isotropicExponent D (finrank K S)) *
      (2^(finrank K S)*(Fintype.card K : ℝ)^(2*(finrank K U*finrank K V+finrank K U*finrank K W+finrank K V*finrank K W))) :=
        mul_le_mul hi hb (Nat.cast_nonneg _) (by positivity)
    _ = (lagrangianConstant D*(2^(finrank K S)*2^(finrank K S))) * (Fintype.card K : ℝ)^(isotropicExponent D (finrank K S) +
        2*(finrank K U*finrank K V+finrank K U*finrank K W+finrank K V*finrank K W)) := by rw [pow_add]; ring
    _ ≤ _ := by gcongr
end ConfigurationBound
section CommonZeroProfiles
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E)
abbrev CommonZeroDimProfile (L M N : SymplecticLagrangian ω) :=
  {p : SymplecticLagrangian ω × SymplecticLagrangian ω × SymplecticLagrangian ω //
    (p.1.val ⊓ p.2.1.val) ⊓ p.2.2.val = ⊥ ∧
    finrank K ↥(p.1.val ⊓ p.2.1.val) = finrank K ↥(L.val ⊓ M.val) ∧
    finrank K ↥(p.1.val ⊓ p.2.2.val) = finrank K ↥(L.val ⊓ N.val) ∧
    finrank K ↥(p.2.1.val ⊓ p.2.2.val) = finrank K ↥(M.val ⊓ N.val)}
variable [Finite E]
 omit [FiniteDimensional K E] in
 theorem commonZeroProfile_injection (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (L M N : SymplecticLagrangian ω) (h0 : (L.val ⊓ M.val) ⊓ N.val = ⊥) :
    ∃ f : CommonZeroDimProfile ω L M N →
      OrderedTripleOrbit ω (L.val ⊓ M.val) (L.val ⊓ N.val) (M.val ⊓ N.val) ×
      {P : SymplecticLagrangian ω // (L.val ⊓ M.val) ⊔ (L.val ⊓ N.val) ≤ P.val} ×
      {P : SymplecticLagrangian ω // (L.val ⊓ M.val) ⊔ (M.val ⊓ N.val) ≤ P.val} ×
      {P : SymplecticLagrangian ω // (L.val ⊓ N.val) ⊔ (M.val ⊓ N.val) ≤ P.val},
      Function.Injective f := by
  classical
  let O := OrderedTripleOrbit ω (L.val ⊓ M.val) (L.val ⊓ N.val) (M.val ⊓ N.val)
  have ht (p : CommonZeroDimProfile ω L M N) :
      TripleIsometry ω ω (L.val ⊓ M.val) (L.val ⊓ N.val) (M.val ⊓ N.val)
        (p.val.1.val ⊓ p.val.2.1.val) (p.val.1.val ⊓ p.val.2.2.val) (p.val.2.1.val ⊓ p.val.2.2.val) := by
    have hd := triple_pairs_disjoint L.val M.val N.val h0
    have hd' := triple_pairs_disjoint p.val.1.val p.val.2.1.val p.val.2.2.val p.property.1
    exact triple_isotropic_config_transitivity ω h2 ha hω _ _ _ _ _ _
      (triplePairSum_isotropic ω _ _ _ L.property M.property N.property)
      (triplePairSum_isotropic ω _ _ _ p.val.1.property p.val.2.1.property p.val.2.2.property)
      hd.1 hd.2 hd'.1 hd'.2 p.property.2.1.symm p.property.2.2.1.symm p.property.2.2.2.symm
  let orb (p : CommonZeroDimProfile ω L M N) : O :=
    ⟨(p.val.1.val ⊓ p.val.2.1.val,p.val.1.val ⊓ p.val.2.2.val,p.val.2.1.val ⊓ p.val.2.2.val),ht p⟩
  let e (o : O) := o.property.choose
  have he (o : O) := o.property.choose_spec
  have hes (o : O) (x y : E) : ω ((e o).symm x) ((e o).symm y) = ω x y := by
    simpa only [e,LinearEquiv.apply_symm_apply] using ((he o).1 ((e o).symm x) ((e o).symm y)).symm
  let g (o : O) := lagrangianIsometryEquiv ω (e o).symm (hes o)
  have hg (o : O) (P : SymplecticLagrangian ω) : (g o P).val = P.val.map (e o).symm.toLinearMap := rfl
  have hpL (p : CommonZeroDimProfile ω L M N) :
      (L.val ⊓ M.val) ⊔ (L.val ⊓ N.val) ≤ (g (orb p) p.val.1).val := by
    rw [hg,←Submodule.orderIsoMapComap_symm_apply']
    apply (Submodule.orderIsoMapComap (e (orb p))).le_symm_apply.mpr
    change ((L.val ⊓ M.val) ⊔ (L.val ⊓ N.val)).map (e (orb p)).toLinearMap ≤ p.val.1.val
    rw [Submodule.map_sup,(he (orb p)).2.1,(he (orb p)).2.2.1]
    exact sup_le inf_le_left inf_le_left
  have hpM (p : CommonZeroDimProfile ω L M N) :
      (L.val ⊓ M.val) ⊔ (M.val ⊓ N.val) ≤ (g (orb p) p.val.2.1).val := by
    rw [hg,←Submodule.orderIsoMapComap_symm_apply']
    apply (Submodule.orderIsoMapComap (e (orb p))).le_symm_apply.mpr
    change ((L.val ⊓ M.val) ⊔ (M.val ⊓ N.val)).map (e (orb p)).toLinearMap ≤ p.val.2.1.val
    rw [Submodule.map_sup,(he (orb p)).2.1,(he (orb p)).2.2.2]
    exact sup_le inf_le_right inf_le_left
  have hpN (p : CommonZeroDimProfile ω L M N) :
      (L.val ⊓ N.val) ⊔ (M.val ⊓ N.val) ≤ (g (orb p) p.val.2.2).val := by
    rw [hg,←Submodule.orderIsoMapComap_symm_apply']
    apply (Submodule.orderIsoMapComap (e (orb p))).le_symm_apply.mpr
    change ((L.val ⊓ N.val) ⊔ (M.val ⊓ N.val)).map (e (orb p)).toLinearMap ≤ p.val.2.2.val
    rw [Submodule.map_sup,(he (orb p)).2.2.1,(he (orb p)).2.2.2]
    exact sup_le inf_le_right inf_le_right
  let f (p : CommonZeroDimProfile ω L M N) :=
    (orb p,(⟨g (orb p) p.val.1,hpL p⟩ : {P : SymplecticLagrangian ω // (L.val ⊓ M.val) ⊔ (L.val ⊓ N.val) ≤ P.val}),
      (⟨g (orb p) p.val.2.1,hpM p⟩ : {P : SymplecticLagrangian ω // (L.val ⊓ M.val) ⊔ (M.val ⊓ N.val) ≤ P.val}),
      (⟨g (orb p) p.val.2.2,hpN p⟩ : {P : SymplecticLagrangian ω // (L.val ⊓ N.val) ⊔ (M.val ⊓ N.val) ≤ P.val}))
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
noncomputable def profileMassConstant (D : ℕ) : ℝ := lagrangianConstant D^4 * 4^D
 theorem profileMassConstant_pos (D : ℕ) : 0 < profileMassConstant D := by
  unfold profileMassConstant
  have := lagrangianConstant_pos D
  positivity
 theorem profileMassConstant_mono : Monotone profileMassConstant := by
  intro a b hab
  unfold profileMassConstant
  exact mul_le_mul (pow_le_pow_left₀ (le_of_lt (lagrangianConstant_pos a)) (lagrangianConstant_mono hab) 4)
    (pow_le_pow_right₀ (by norm_num) hab) (by positivity) (by positivity)
section CommonZeroMass
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
 theorem commonZeroProfile_card_upper (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D = finrank K E)
    (L M N : SymplecticLagrangian ω) (h0 : (L.val ⊓ M.val) ⊓ N.val = ⊥) :
    (Fintype.card K : ℝ)^((finrank K ↥(L.val ⊓ M.val)+1).choose 2 +
      (finrank K ↥(L.val ⊓ N.val)+1).choose 2 + (finrank K ↥(M.val ⊓ N.val)+1).choose 2) *
      Nat.card (CommonZeroDimProfile ω L M N) ≤ profileMassConstant D * (Fintype.card K : ℝ)^(3*(D+1).choose 2) := by
  have hconst := lagrangianConstant_pos D
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
  have his (P : SymplecticLagrangian ω) (T : Submodule K E) (hT : T ≤ P.val) : T ≤ ω.orthogonal T := by
    intro x hx y hy
    exact P.property.ge (hT hx) y (hT hy)
  have hd := triple_pairs_disjoint L.val M.val N.val h0
  have hdimA : finrank K A = u+v := finrank_sup_of_disjoint _ _ (hd.1.mono_right le_sup_left)
  have hdimB : finrank K B = u+w := finrank_sup_of_disjoint _ _ (hd.1.mono_right le_sup_right)
  have hdimC : finrank K C = v+w := finrank_sup_of_disjoint _ _ hd.2
  have hdim : finrank K S = u+v+w := triplePairSum_finrank L.val M.val N.val h0
  have hs : S ≤ ω.orthogonal S := triplePairSum_isotropic ω _ _ _ L.property M.property N.property
  have haD : u+v+w ≤ D := hdim ▸ isotropic_finrank_le_half ω hω D hD S hs
  have hc := triple_isotropic_orbit_card_upper ω h2 ha hω D hD S
    (L.val ⊓ M.val) (L.val ⊓ N.val) (M.val ⊓ N.val) hs
    (le_sup_of_le_left le_sup_left) (le_sup_of_le_left le_sup_right) le_sup_right rfl hd.1 hd.2
  rw [hdim] at hc
  have hcont (P : SymplecticLagrangian ω) (T : Submodule K E) (hT : T ≤ P.val) :
      (Nat.card {Q : SymplecticLagrangian ω // T ≤ Q.val} : ℝ) ≤
        lagrangianConstant D * (Fintype.card K : ℝ)^((D-finrank K T+1).choose 2) :=
    ((containingLagrangian_card_bounds ω h2 ha hω D hD T (his P T hT)).2).trans
      (mul_le_mul_of_nonneg_right (lagrangianConstant_mono (Nat.sub_le _ _)) (by positivity))
  have h₁ := hcont L A hA
  have h₂ := hcont M B hB
  have h₃ := hcont N C hC
  rw [hdimA] at h₁
  rw [hdimB] at h₂
  rw [hdimC] at h₃
  obtain ⟨f,hf⟩ := commonZeroProfile_injection ω h2 ha hω L M N h0
  have hcard : (Nat.card (CommonZeroDimProfile ω L M N) : ℝ) ≤
      Nat.card (OrderedTripleOrbit ω (L.val ⊓ M.val) (L.val ⊓ N.val) (M.val ⊓ N.val)) *
        ((Nat.card {Q : SymplecticLagrangian ω // A ≤ Q.val} : ℝ) *
          (Nat.card {Q : SymplecticLagrangian ω // B ≤ Q.val} * Nat.card {Q : SymplecticLagrangian ω // C ≤ Q.val})) := by
    have hh := Nat.card_le_card_of_injective f hf
    rw [Nat.card_prod,Nat.card_prod,Nat.card_prod] at hh
    exact_mod_cast hh
  have hb : (Nat.card (CommonZeroDimProfile ω L M N) : ℝ) ≤
      profileMassConstant D * (Fintype.card K : ℝ)^(isotropicExponent D (u+v+w)+2*(u*v+u*w+v*w)+
        ((D-(u+v)+1).choose 2+(D-(u+w)+1).choose 2+(D-(v+w)+1).choose 2)) := by
    calc
      _ ≤ _ := hcard
      _ ≤ ((lagrangianConstant D*4^D)*(Fintype.card K : ℝ)^(isotropicExponent D (u+v+w)+2*(u*v+u*w+v*w))) *
        ((lagrangianConstant D*(Fintype.card K : ℝ)^((D-(u+v)+1).choose 2))*
          ((lagrangianConstant D*(Fintype.card K : ℝ)^((D-(u+w)+1).choose 2))*
            (lagrangianConstant D*(Fintype.card K : ℝ)^((D-(v+w)+1).choose 2)))) := by
          gcongr
      _ = _ := by unfold profileMassConstant; simp only [pow_add]; ring
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
abbrev TripleDimProfile (c u v w : ℕ) :=
  {p : SymplecticLagrangian ω × SymplecticLagrangian ω × SymplecticLagrangian ω //
    finrank K ↥((p.1.val ⊓ p.2.1.val) ⊓ p.2.2.val) = c ∧
    finrank K ↥(p.1.val ⊓ p.2.1.val) = u ∧
    finrank K ↥(p.1.val ⊓ p.2.2.val) = v ∧
    finrank K ↥(p.2.1.val ⊓ p.2.2.val) = w}
noncomputable def tripleProfileCommon {c u v w : ℕ} (p : TripleDimProfile ω c u v w) : IsotropicDimspace ω c :=
  ⟨(p.val.1.val ⊓ p.val.2.1.val) ⊓ p.val.2.2.val,
    (by intro x hx y hy; exact p.val.1.property.ge hx.1.1 y hy.1.1),p.property.1⟩
 theorem reducePair_finrank (S : Submodule K E) (P Q : SymplecticLagrangian ω)
    (hSP : S ≤ P.val) (hSQ : S ≤ Q.val) :
    finrank K ↥(reduceSubspace ω S P.val ⊓ reduceSubspace ω S Q.val) =
      finrank K ↥(P.val ⊓ Q.val)-finrank K S := by
  rw [←reduceSubspace_inf ω S P.val Q.val hSP]
  have hh := reduceSubspace_finrank_containing ω S (P.val ⊓ Q.val) (le_inf hSP hSQ)
    (inf_le_left.trans (lagrangian_le_orthogonal ω S P.val P.property hSP))
  omega
 omit [FiniteDimensional K E] in
 theorem reduceLagrangian_injective (S : Submodule K E) :
    Function.Injective (fun P : {P : SymplecticLagrangian ω // S ≤ P.val} => reduceSubspace ω S P.val.val) := by
  intro P Q h
  apply Subtype.ext
  apply Subtype.ext
  have hh := congrArg (liftReduction ω S) h
  simpa only [lift_reduce ω S P.val.val P.property (lagrangian_le_orthogonal ω S P.val.val P.val.property P.property),
    lift_reduce ω S Q.val.val Q.property (lagrangian_le_orthogonal ω S Q.val.val Q.val.property Q.property)] using hh
 theorem fixedCommonProfile_injection (ha : ω.IsAlt) {c u v w : ℕ}
    (S : IsotropicDimspace ω c)
    (p₀ : {p : TripleDimProfile ω c u v w // tripleProfileCommon ω p = S}) :
    ∃ L M N : SymplecticLagrangian (symplecticReductionForm ω S.val ha),
      (L.val ⊓ M.val) ⊓ N.val = ⊥ ∧
      finrank K ↥(L.val ⊓ M.val) = u-c ∧
      finrank K ↥(L.val ⊓ N.val) = v-c ∧
      finrank K ↥(M.val ⊓ N.val) = w-c ∧
      ∃ f : {p : TripleDimProfile ω c u v w // tripleProfileCommon ω p = S} →
        CommonZeroDimProfile (symplecticReductionForm ω S.val ha) L M N, Function.Injective f := by
  let F := {p : TripleDimProfile ω c u v w // tripleProfileCommon ω p = S}
  have heq (p : F) : (p.val.val.1.val ⊓ p.val.val.2.1.val) ⊓ p.val.val.2.2.val = S.val :=
    congrArg Subtype.val p.property
  have hL (p : F) : S.val ≤ p.val.val.1.val := (heq p).symm ▸ inf_le_left.trans inf_le_left
  have hM (p : F) : S.val ≤ p.val.val.2.1.val := (heq p).symm ▸ inf_le_left.trans inf_le_right
  have hN (p : F) : S.val ≤ p.val.val.2.2.val := (heq p).symm ▸ inf_le_right
  let L (p : F) := commonReductionLagrangian ω S.val ha S.property.1 p.val.val.1 (hL p)
  let M (p : F) := commonReductionLagrangian ω S.val ha S.property.1 p.val.val.2.1 (hM p)
  let N (p : F) := commonReductionLagrangian ω S.val ha S.property.1 p.val.val.2.2 (hN p)
  have hzero (p : F) : ((L p).val ⊓ (M p).val) ⊓ (N p).val = ⊥ := by
    change (reduceSubspace ω S.val p.val.val.1.val ⊓ reduceSubspace ω S.val p.val.val.2.1.val) ⊓
      reduceSubspace ω S.val p.val.val.2.2.val = ⊥
    rw [←reduceSubspace_inf ω S.val _ _ (hL p),←reduceSubspace_inf ω S.val _ _ (le_inf (hL p) (hM p)),heq p]
    exact reduceSubspace_self ω S.val
  have hu (p : F) : finrank K ↥((L p).val ⊓ (M p).val) = u-c := by
    change finrank K ↥(reduceSubspace ω S.val p.val.val.1.val ⊓ reduceSubspace ω S.val p.val.val.2.1.val) = _
    rw [reducePair_finrank ω S.val _ _ (hL p) (hM p),p.val.property.2.1,S.property.2]
  have hv (p : F) : finrank K ↥((L p).val ⊓ (N p).val) = v-c := by
    change finrank K ↥(reduceSubspace ω S.val p.val.val.1.val ⊓ reduceSubspace ω S.val p.val.val.2.2.val) = _
    rw [reducePair_finrank ω S.val _ _ (hL p) (hN p),p.val.property.2.2.1,S.property.2]
  have hw (p : F) : finrank K ↥((M p).val ⊓ (N p).val) = w-c := by
    change finrank K ↥(reduceSubspace ω S.val p.val.val.2.1.val ⊓ reduceSubspace ω S.val p.val.val.2.2.val) = _
    rw [reducePair_finrank ω S.val _ _ (hM p) (hN p),p.val.property.2.2.2,S.property.2]
  let f (p : F) : CommonZeroDimProfile (symplecticReductionForm ω S.val ha) (L p₀) (M p₀) (N p₀) :=
    ⟨(L p,M p,N p),hzero p,(hu p).trans (hu p₀).symm,(hv p).trans (hv p₀).symm,(hw p).trans (hw p₀).symm⟩
  refine ⟨L p₀,M p₀,N p₀,hzero p₀,hu p₀,hv p₀,hw p₀,f,?_⟩
  intro p q hpq
  have heL : (L p).val = (L q).val := congrArg (fun r => r.val.1.val) hpq
  have heM : (M p).val = (M q).val := congrArg (fun r => r.val.2.1.val) hpq
  have heN : (N p).val = (N q).val := congrArg (fun r => r.val.2.2.val) hpq
  have hpL : p.val.val.1 = q.val.val.1 := congrArg Subtype.val
    (reduceLagrangian_injective ω S.val (a₁ := ⟨p.val.val.1,hL p⟩) (a₂ := ⟨q.val.val.1,hL q⟩) heL)
  have hpM : p.val.val.2.1 = q.val.val.2.1 := congrArg Subtype.val
    (reduceLagrangian_injective ω S.val (a₁ := ⟨p.val.val.2.1,hM p⟩) (a₂ := ⟨q.val.val.2.1,hM q⟩) heM)
  have hpN : p.val.val.2.2 = q.val.val.2.2 := congrArg Subtype.val
    (reduceLagrangian_injective ω S.val (a₁ := ⟨p.val.val.2.2,hN p⟩) (a₂ := ⟨q.val.val.2.2,hN q⟩) heN)
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
    (D : ℕ) (hD : 2*D = finrank K E) {c u v w : ℕ} (S : IsotropicDimspace ω c) :
    (Fintype.card K : ℝ)^((u-c+1).choose 2+(v-c+1).choose 2+(w-c+1).choose 2) *
      Nat.card {p : TripleDimProfile ω c u v w // tripleProfileCommon ω p = S} ≤
        profileMassConstant (D-c) * (Fintype.card K : ℝ)^(3*(D-c+1).choose 2) := by
  classical
  let F := {p : TripleDimProfile ω c u v w // tripleProfileCommon ω p = S}
  by_cases hF : Nonempty F
  · obtain ⟨p₀⟩ := hF
    obtain ⟨L,M,N,hzero,hu,hv,hw,f,hf⟩ := fixedCommonProfile_injection ω ha S p₀
    let : Finite (ReducedSpace ω S.val) := Module.finite_of_finite K
    have hc : c ≤ D := S.property.2 ▸ isotropic_finrank_le_half ω hω D hD S.val S.property.1
    have hdim : 2*(D-c) = finrank K (ReducedSpace ω S.val) := by
      have hh := reducedSpace_finrank ω S.val hω S.property.1
      rw [S.property.2,←hD] at hh
      omega
    have hp := commonZeroProfile_card_upper (symplecticReductionForm ω S.val ha) h2
      (symplecticReductionForm_alt ω S.val ha) (symplecticReductionForm_nondegenerate ω S.val ha hω)
      (D-c) hdim L M N hzero
    rw [hu,hv,hw] at hp
    have hc : (Nat.card F : ℝ) ≤ Nat.card (CommonZeroDimProfile (symplecticReductionForm ω S.val ha) L M N) := by
      exact_mod_cast Nat.card_le_card_of_injective f hf
    exact (mul_le_mul_of_nonneg_left hc (by positivity)).trans hp
  · have h_empty : IsEmpty F := not_nonempty_iff.mp hF
    have hc : Nat.card F = 0 := Nat.card_eq_zero.mpr (Or.inl h_empty)
    change _ * (Nat.card F : ℝ) ≤ _
    rw [hc,Nat.cast_zero,mul_zero]
    exact mul_nonneg (le_of_lt (profileMassConstant_pos _)) (by positivity)
noncomputable def fullProfileConstant (D : ℕ) : ℝ := lagrangianConstant D * 2^D * profileMassConstant D
 theorem fullProfileConstant_pos (D : ℕ) : 0 < fullProfileConstant D :=
  mul_pos (mul_pos (lagrangianConstant_pos _) (by positivity)) (profileMassConstant_pos _)
 theorem tripleProfile_card_upper (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D = finrank K E) (c u v w : ℕ) (hc : c ≤ D) :
    (Fintype.card K : ℝ)^((D+1)*c + ((u-c+1).choose 2+(v-c+1).choose 2+(w-c+1).choose 2)) *
      Nat.card (TripleDimProfile ω c u v w) ≤ fullProfileConstant D * (Fintype.card K : ℝ)^(3*(D+1).choose 2) := by
  classical
  let := Fintype.ofFinite (IsotropicDimspace ω c)
  let δ := (u-c+1).choose 2+(v-c+1).choose 2+(w-c+1).choose 2
  let q : ℝ := Fintype.card K
  have hi := (isotropic_card_bounds ω h2 ha hω D hD c hc).2
  have hsum : (Nat.card (TripleDimProfile ω c u v w) : ℝ) =
      ∑ S : IsotropicDimspace ω c, (Nat.card {p : TripleDimProfile ω c u v w // tripleProfileCommon ω p = S} : ℝ) := by
    have hh := (Nat.card_congr (Equiv.sigmaFiberEquiv (tripleProfileCommon ω (c := c) (u := u) (v := v) (w := w)))).symm
    rw [Nat.card_sigma] at hh
    exact_mod_cast hh
  have hbase : q^δ * Nat.card (TripleDimProfile ω c u v w) ≤
      (Nat.card (IsotropicDimspace ω c) : ℝ) * (profileMassConstant (D-c)*q^(3*(D-c+1).choose 2)) := by
    rw [hsum,Finset.mul_sum]
    calc
      _ ≤ ∑ _S : IsotropicDimspace ω c, profileMassConstant (D-c)*q^(3*(D-c+1).choose 2) :=
        Finset.sum_le_sum (fun S _ => fixedCommonProfile_card_upper ω h2 ha hω D hD S)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card]
  have hk : (lagrangianConstant D*2^c)*profileMassConstant (D-c) ≤ fullProfileConstant D := by
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hc) (le_of_lt (lagrangianConstant_pos _)))
      (profileMassConstant_mono (Nat.sub_le D c)) (le_of_lt (profileMassConstant_pos _))
      (mul_nonneg (le_of_lt (lagrangianConstant_pos _)) (by positivity))
  have hconst := fullProfileConstant_pos D
  calc
    _ = q^((D+1)*c) * (q^δ * Nat.card (TripleDimProfile ω c u v w)) := by rw [pow_add,mul_assoc]
    _ ≤ q^((D+1)*c) * ((Nat.card (IsotropicDimspace ω c) : ℝ)*(profileMassConstant (D-c)*q^(3*(D-c+1).choose 2))) :=
      mul_le_mul_of_nonneg_left hbase (by positivity)
    _ ≤ q^((D+1)*c) * (((lagrangianConstant D*2^c)*q^isotropicExponent D c)*(profileMassConstant (D-c)*q^(3*(D-c+1).choose 2))) := by
      gcongr
      exact mul_nonneg (le_of_lt (profileMassConstant_pos _)) (by positivity)
    _ = ((lagrangianConstant D*2^c)*profileMassConstant (D-c))*q^(isotropicExponent D c+3*(D-c+1).choose 2+(D+1)*c) := by
      simp only [pow_add]; ring
    _ = ((lagrangianConstant D*2^c)*profileMassConstant (D-c))*q^(3*(D+1).choose 2) := by
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
    (A : SymplecticLagrangian ω) (h : ℕ) (hh : h ≤ finrank K A.val) :
    Nat.card {L : SymplecticLagrangian ω // finrank K ↥(L.val ⊓ A.val) = h} =
      Nat.card (DimSubspace K A.val (finrank K A.val-h)) * (Fintype.card K)^((finrank K A.val-h+1).choose 2) := by
  classical
  obtain ⟨e,_,he⟩ := exists_lagrangian_coordinates ω A.val h2 ha hω A.property
  let f := symplecticLagrangianEquiv canonicalSymplectic ω e he
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
      Nat.card {L : SymplecticLagrangian ω // finrank K ↥(L.val ⊓ A.val) = h} :=
    Nat.card_congr (f.subtypeEquiv (fun L => by rw [hd]))
  rw [←hc]
  exact lagrangian_pair_count h2 A₀ h hh
 theorem symplectic_pair_card_bounds (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D = finrank K E) (A : SymplecticLagrangian ω) (h : ℕ) (hh : h ≤ D) :
    (Fintype.card K : ℝ)^((D+1).choose 2) ≤ (Fintype.card K : ℝ)^((h+1).choose 2) *
      Nat.card {L : SymplecticLagrangian ω // finrank K ↥(L.val ⊓ A.val) = h} ∧
    (Fintype.card K : ℝ)^((h+1).choose 2) *
      Nat.card {L : SymplecticLagrangian ω // finrank K ↥(L.val ⊓ A.val) = h} ≤
        2^D*(Fintype.card K : ℝ)^((D+1).choose 2) := by
  have hd : finrank K A.val = D := by
    have h := self_orthogonal_twice_finrank ω A.val hω A.property
    omega
  have hhA : h ≤ finrank K A.val := by omega
  have hcount := symplectic_pair_count ω h2 ha hω A h hhA
  rw [hd] at hcount
  rw [hcount,Nat.cast_mul,Nat.cast_pow]
  have hl := subspace_count_lower (K := K) (V := A.val) (D-h) (by omega)
  have hu := subspace_count_upper (K := K) (V := A.val) (D-h) (by omega)
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
abbrev OrderedPairDim (h : ℕ) := {p : SymplecticLagrangian ω × SymplecticLagrangian ω //
  finrank K ↥(p.1.val ⊓ p.2.val) = h}
noncomputable def orderedPairDimEquiv (h : ℕ) : OrderedPairDim ω h ≃
    Σ A : SymplecticLagrangian ω, {L : SymplecticLagrangian ω // finrank K ↥(L.val ⊓ A.val) = h} where
  toFun p := ⟨p.val.1,⟨p.val.2,by rw [inf_comm]; exact p.property⟩⟩
  invFun p := ⟨(p.1,p.2.val),by rw [inf_comm]; exact p.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
 theorem orderedPairDim_card_lower (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D = finrank K E) (h : ℕ) (hh : h ≤ D) :
    (Fintype.card K : ℝ)^(2*(D+1).choose 2) ≤ (Fintype.card K : ℝ)^((h+1).choose 2) * Nat.card (OrderedPairDim ω h) := by
  classical
  let := Fintype.ofFinite (SymplecticLagrangian ω)
  have hc : (Nat.card (OrderedPairDim ω h) : ℝ) =
      ∑ A : SymplecticLagrangian ω, (Nat.card {L : SymplecticLagrangian ω // finrank K ↥(L.val ⊓ A.val) = h} : ℝ) := by
    rw [Nat.card_congr (orderedPairDimEquiv ω h),Nat.card_sigma,Nat.cast_sum]
  rw [hc,Finset.mul_sum]
  have he : 2*(D+1).choose 2 = (D+1).choose 2+(D+1).choose 2 := by omega
  rw [he,pow_add]
  calc
    _ ≤ (Nat.card (SymplecticLagrangian ω) : ℝ)*(Fintype.card K : ℝ)^((D+1).choose 2) :=
      mul_le_mul_of_nonneg_right (symplecticLagrangian_card_bounds ω h2 ha hω D hD).1 (by positivity)
    _ = ∑ _A : SymplecticLagrangian ω, (Fintype.card K : ℝ)^((D+1).choose 2) := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card]
    _ ≤ _ := Finset.sum_le_sum (fun A _ => (symplectic_pair_card_bounds ω h2 ha hω D hD A h hh).1)
end GeneralPairCounts
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ConditionalProfile
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E)
abbrev PairCompletion (L M : SymplecticLagrangian ω) (c v w : ℕ) :=
  {N : SymplecticLagrangian ω // finrank K ↥((L.val ⊓ M.val) ⊓ N.val) = c ∧
    finrank K ↥(L.val ⊓ N.val) = v ∧ finrank K ↥(M.val ⊓ N.val) = w}
 omit [FiniteDimensional K E] in
 theorem pairCompletion_card_congr (L M L' M' : SymplecticLagrangian ω)
    (e : E ≃ₗ[K] E) (he : ∀ x y, ω (e x) (e y) = ω x y)
    (hL : L.val.map e.toLinearMap = L'.val) (hM : M.val.map e.toLinearMap = M'.val) (c v w : ℕ) :
    Nat.card (PairCompletion ω L M c v w) = Nat.card (PairCompletion ω L' M' c v w) := by
  let f := lagrangianIsometryEquiv ω e he
  have hp (A B : Submodule K E) : finrank K ↥(A.map e.toLinearMap ⊓ B.map e.toLinearMap) = finrank K ↥(A ⊓ B) := by
    rw [←Submodule.map_inf e.toLinearMap e.injective]
    exact e.finrank_map_eq _
  have hc (P : SymplecticLagrangian ω) : finrank K ↥((L'.val ⊓ M'.val) ⊓ (f P).val) =
      finrank K ↥((L.val ⊓ M.val) ⊓ P.val) := by
    change finrank K ↥((L'.val ⊓ M'.val) ⊓ P.val.map e.toLinearMap) = _
    rw [←hL,←hM,←Submodule.map_inf e.toLinearMap e.injective,hp]
  have hv (P : SymplecticLagrangian ω) : finrank K ↥(L'.val ⊓ (f P).val) = finrank K ↥(L.val ⊓ P.val) := by
    change finrank K ↥(L'.val ⊓ P.val.map e.toLinearMap) = _
    rw [←hL,hp]
  have hw (P : SymplecticLagrangian ω) : finrank K ↥(M'.val ⊓ (f P).val) = finrank K ↥(M.val ⊓ P.val) := by
    change finrank K ↥(M'.val ⊓ P.val.map e.toLinearMap) = _
    rw [←hM,hp]
  exact Nat.card_congr (f.subtypeEquiv (fun P => by rw [hc,hv,hw]))
noncomputable def profilePairCompletionEquiv (c u v w : ℕ) : TripleDimProfile ω c u v w ≃
    Σ p : OrderedPairDim ω u, PairCompletion ω p.val.1 p.val.2 c v w where
  toFun p := ⟨⟨(p.val.1,p.val.2.1),p.property.2.1⟩,⟨p.val.2.2,p.property.1,p.property.2.2⟩⟩
  invFun p := ⟨(p.1.val.1,p.1.val.2,p.2.val),p.2.property.1,p.1.property,p.2.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
variable [Finite E]
 theorem tripleProfile_completion_card (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (L M : SymplecticLagrangian ω) (c v w : ℕ) :
    Nat.card (TripleDimProfile ω c (finrank K ↥(L.val ⊓ M.val)) v w) =
      Nat.card (OrderedPairDim ω (finrank K ↥(L.val ⊓ M.val))) * Nat.card (PairCompletion ω L M c v w) := by
  classical
  let := Fintype.ofFinite (OrderedPairDim ω (finrank K ↥(L.val ⊓ M.val)))
  rw [Nat.card_congr (profilePairCompletionEquiv ω c (finrank K ↥(L.val ⊓ M.val)) v w),Nat.card_sigma]
  have hc (p : OrderedPairDim ω (finrank K ↥(L.val ⊓ M.val))) :
      Nat.card (PairCompletion ω p.val.1 p.val.2 c v w) = Nat.card (PairCompletion ω L M c v w) := by
    obtain ⟨e,he,hL,hM⟩ := ordered_pair_transitivity ω h2 ha hω
      p.val.1.val p.val.2.val L.val M.val p.val.1.property p.val.2.property L.property M.property p.property
    exact pairCompletion_card_congr ω p.val.1 p.val.2 L M e he hL hM c v w
  simp only [hc,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card]
  simp only [Nat.cast_id]
variable [Fintype K]
end ConditionalProfile
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section PlantedQuotient
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E) (S : Submodule K E)
 theorem reduceSubspace_finrank_general (A : Submodule K E) (hAP : A ≤ ω.orthogonal S) :
    finrank K (reduceSubspace ω S A) + finrank K ↥(S ⊓ A) = finrank K A := by
  let f : A →ₗ[K] ReducedSpace ω S := (reductionKernel ω S).mkQ.comp (Submodule.inclusion hAP)
  have hk : LinearMap.ker f = (S ⊓ A).comap A.subtype := by
    ext x
    constructor
    · intro hx
      exact ⟨(Submodule.Quotient.mk_eq_zero (reductionKernel ω S)).mp hx,x.property⟩
    · intro hx
      exact (Submodule.Quotient.mk_eq_zero (reductionKernel ω S)).mpr hx.1
  have hr : LinearMap.range f = reduceSubspace ω S A := by
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
    finrank K ↥(reduceSubspace ω S L ⊓ reduceSubspace ω S Y) + finrank K ↥(S ⊓ Y) =
      finrank K ↥(L ⊓ Y) := by
  rw [←reduceSubspace_inf ω S L Y hSL]
  have hh := reduceSubspace_finrank_general ω S (L ⊓ Y) (inf_le_left.trans hLP)
  have he : S ⊓ (L ⊓ Y) = S ⊓ Y := by rw [←inf_assoc,inf_eq_left.mpr hSL]
  rwa [he] at hh
end PlantedQuotient
section CenterDisintegration
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E)
abbrev TripleCenterSet (r : ℕ) (L M N : Submodule K E) :=
  {Y : SymplecticLagrangian ω // finrank K ↥(L ⊓ Y.val) = r ∧
    finrank K ↥(M ⊓ Y.val) = r ∧ finrank K ↥(N ⊓ Y.val) = r}
noncomputable def tripleCenterIsometryEquiv (r : ℕ) (L M N : Submodule K E)
    (e : E ≃ₗ[K] E) (he : ∀ x y, ω (e x) (e y) = ω x y) :
    TripleCenterSet ω r L M N ≃
    TripleCenterSet ω r (L.map e.toLinearMap) (M.map e.toLinearMap) (N.map e.toLinearMap) := by
  let f := lagrangianIsometryEquiv ω e he
  refine f.subtypeEquiv ?_
  intro Y
  change (_ ∧ _ ∧ _) ↔ (finrank K ↥(L.map e.toLinearMap ⊓ Y.val.map e.toLinearMap) = r ∧
    finrank K ↥(M.map e.toLinearMap ⊓ Y.val.map e.toLinearMap) = r ∧
    finrank K ↥(N.map e.toLinearMap ⊓ Y.val.map e.toLinearMap) = r)
  rw [←Submodule.map_inf e.toLinearMap e.injective,←Submodule.map_inf e.toLinearMap e.injective,
    ←Submodule.map_inf e.toLinearMap e.injective,e.finrank_map_eq,e.finrank_map_eq,e.finrank_map_eq]
 theorem tripleCenter_orbit_card (r : ℕ) (L M N : Submodule K E)
    (P : OrderedTripleOrbit ω L M N) :
    Nat.card (TripleCenterSet ω r P.val.1 P.val.2.1 P.val.2.2) =
      Nat.card (TripleCenterSet ω r L M N) := by
  obtain ⟨e,he,hL,hM,hN⟩ := P.property
  rw [←hL,←hM,←hN]
  exact (Nat.card_congr (tripleCenterIsometryEquiv ω r L M N e he)).symm
 theorem tripleCenterOrbit_card [Finite E] (r : ℕ) (L M N : Submodule K E) :
    Nat.card (Σ P : OrderedTripleOrbit ω L M N, TripleCenterSet ω r P.val.1 P.val.2.1 P.val.2.2) =
      Nat.card (OrderedTripleOrbit ω L M N) * Nat.card (TripleCenterSet ω r L M N) := by
  classical
  let := Fintype.ofFinite (OrderedTripleOrbit ω L M N)
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
abbrev SymplecticCenterStratum (Y : SymplecticLagrangian ω) (r : ℕ) :=
  {L : SymplecticLagrangian ω // finrank K ↥(L.val ⊓ Y.val) = r}
abbrev SymplecticCenterProfile (Y : SymplecticLagrangian ω) (r s₀ s₁ s₂ : ℕ) :=
  {L : SymplecticCenterStratum ω Y r × SymplecticCenterStratum ω Y r × SymplecticCenterStratum ω Y r //
    (L.1.val.val ⊓ L.2.1.val.val) ⊓ L.2.2.val.val = ⊥ ∧
    finrank K ↥(L.1.val.val ⊓ L.2.1.val.val) = s₀ ∧
    finrank K ↥(L.1.val.val ⊓ L.2.2.val.val) = s₁ ∧
    finrank K ↥(L.2.1.val.val ⊓ L.2.2.val.val) = s₂}
 theorem exists_center_coordinates [FiniteDimensional K E] (h2 : (2:K) ≠ 0)
    (ha : ω.IsAlt) (hω : ω.Nondegenerate) (Y : SymplecticLagrangian ω) :
    ∃ e : (Y.val × Module.Dual K Y.val) ≃ₗ[K] E,
      (∀ x y, ω (e x) (e y) = canonicalSymplectic x y) ∧
      (verticalSpace (K := K) (V := Y.val)).map e.toLinearMap = Y.val := by
  obtain ⟨e,_,he⟩ := exists_lagrangian_coordinates ω Y.val h2 ha hω Y.property
  let f := symplecticLagrangianEquiv canonicalSymplectic ω e he
  let A := f.symm Y
  have hm : A.val.map e.toLinearMap = Y.val := congrArg Subtype.val (f.apply_symm_apply Y)
  obtain ⟨a,ha,hA⟩ := lagrangian_transitivity canonicalSymplectic verticalLagrangian.val h2
    canonicalSymplectic_alt canonicalSymplectic_nondegenerate verticalLagrangian.property A.val A.property
  refine ⟨a.trans e,?_,?_⟩
  · intro x y
    change ω (e (a x)) (e (a y)) = _
    rw [he,ha]
  · change verticalSpace.map (e.toLinearMap.comp a.toLinearMap) = _
    rw [Submodule.map_comp]
    change (verticalLagrangian.val.map a.toLinearMap).map e.toLinearMap = _
    rw [hA,hm]
 theorem map_pair_finrank (e : V ≃ₗ[K] E) (A B : Submodule K V) :
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
noncomputable def symplecticCenterStratumEquiv (Y : SymplecticLagrangian ω)
    (e : (V × Module.Dual K V) ≃ₗ[K] E)
    (he : ∀ x y, ω (e x) (e y) = canonicalSymplectic x y)
    (hY : (verticalSpace (K := K) (V := V)).map e.toLinearMap = Y.val) (r : ℕ) :
    CenterStratum (K := K) (V := V) r ≃ SymplecticCenterStratum ω Y r :=
  (symplecticLagrangianEquiv canonicalSymplectic ω e he).subtypeEquiv (by
    intro L
    change finrank K ↥(L.val ⊓ verticalSpace) = r ↔ finrank K ↥(L.val.map e.toLinearMap ⊓ Y.val) = r
    rw [←hY,map_pair_finrank])
noncomputable def symplecticCenterProfileEquiv (Y : SymplecticLagrangian ω)
    (e : (V × Module.Dual K V) ≃ₗ[K] E)
    (he : ∀ x y, ω (e x) (e y) = canonicalSymplectic x y)
    (hY : (verticalSpace (K := K) (V := V)).map e.toLinearMap = Y.val) (r s₀ s₁ s₂ : ℕ) :
    CenterTripleProfile (K := K) (V := V) r s₀ s₁ s₂ ≃ SymplecticCenterProfile ω Y r s₀ s₁ s₂ :=
  let f := symplecticCenterStratumEquiv ω Y e he hY r
  (f.prodCongr (f.prodCongr f)).subtypeEquiv (by
    intro L
    change (_ ∧ _ ∧ _ ∧ _) ↔
      ((L.1.val.val.map e.toLinearMap ⊓ L.2.1.val.val.map e.toLinearMap) ⊓ L.2.2.val.val.map e.toLinearMap = ⊥ ∧
      finrank K ↥(L.1.val.val.map e.toLinearMap ⊓ L.2.1.val.val.map e.toLinearMap) = s₀ ∧
      finrank K ↥(L.1.val.val.map e.toLinearMap ⊓ L.2.2.val.val.map e.toLinearMap) = s₁ ∧
      finrank K ↥(L.2.1.val.val.map e.toLinearMap ⊓ L.2.2.val.val.map e.toLinearMap) = s₂)
    rw [map_common_zero_iff,map_pair_finrank,map_pair_finrank,map_pair_finrank])
 theorem symplectic_center_profile_probability_bound [Fintype K] [Finite E]
    (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (Y : SymplecticLagrangian ω) (r s₀ s₁ s₂ : ℕ) (hr : r ≤ finrank K Y.val) :
    (Nat.card (SymplecticCenterProfile ω Y r s₀ s₁ s₂) : ℝ) /
      (Nat.card (SymplecticCenterStratum ω Y r) : ℝ)^3 ≤
    ∑ θ : BaseParameters (finrank K Y.val) r s₀ s₁ s₂,
      reducedPlantedConstant r s₀ s₁ s₂ θ.val *
        (Fintype.card K : ℝ)^(reducedPlantedExponent (finrank K Y.val) r s₀ s₁ s₂ θ.val) := by
  obtain ⟨e,he,hY⟩ := exists_center_coordinates ω h2 ha hω Y
  rw [←Nat.card_congr (symplecticCenterProfileEquiv ω Y e he hY r s₀ s₁ s₂),
    ←Nat.card_congr (symplecticCenterStratumEquiv ω Y e he hY r)]
  exact canonical_center_profile_probability_bound r s₀ s₁ s₂ hr
end GenericReducedCount
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section CommonCenterCounts
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
abbrev CommonCenterSet (S : Submodule K E) (u : ℕ) :=
  {Y : SymplecticLagrangian ω // finrank K ↥(S ⊓ Y.val) = u}
 theorem commonCenter_card_upper (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D = finrank K E) (S : Submodule K E)
    (hS : S ≤ ω.orthogonal S) (u : ℕ) (hu : u ≤ finrank K S) :
    (Nat.card (CommonCenterSet ω S u) : ℝ) ≤
      2^u * lagrangianConstant (D-u) *
        (Fintype.card K : ℝ)^(u*(finrank K S-u)+(D-u+1).choose 2) := by
  classical
  let B := CommonCenterSet ω S u
  let Inc := Σ U : DimSubspace K S u, {Y : SymplecticLagrangian ω // U.val.map S.subtype ≤ Y.val}
  let f (Y : B) : Inc :=
    ⟨⟨(S ⊓ Y.val.val).comap S.subtype,
      (Submodule.comapSubtypeEquivOfLe (inf_le_left : S ⊓ Y.val.val ≤ S)).finrank_eq.trans Y.property⟩,
      ⟨Y.val,by rintro x ⟨y,hy,rfl⟩; exact hy.2⟩⟩
  have hf : Function.Injective f := by
    intro Y Z h
    exact Subtype.ext (congrArg (fun i : Inc => i.2.val) h)
  have hb (U : DimSubspace K S u) :
      (Nat.card {Y : SymplecticLagrangian ω // U.val.map S.subtype ≤ Y.val} : ℝ) ≤
      lagrangianConstant (D-u)*(Fintype.card K : ℝ)^((D-u+1).choose 2) := by
    have hle : U.val.map S.subtype ≤ S := by rintro x ⟨y,_,rfl⟩; exact y.property
    have his : U.val.map S.subtype ≤ ω.orthogonal (U.val.map S.subtype) :=
      hle.trans (hS.trans (ω.orthogonal_le hle))
    have hd : finrank K (U.val.map S.subtype) = u :=
      (Submodule.equivMapOfInjective S.subtype S.subtype_injective U.val).finrank_eq.symm.trans U.property
    simpa only [hd] using (containingLagrangian_card_bounds ω h2 ha hω D hD _ his).2
  let := Fintype.ofFinite (DimSubspace K S u)
  have hi : (Nat.card Inc : ℝ) ≤ (Nat.card (DimSubspace K S u) : ℝ)*
      (lagrangianConstant (D-u)*(Fintype.card K : ℝ)^((D-u+1).choose 2)) := by
    rw [Nat.card_sigma,Nat.cast_sum]
    calc
      _ ≤ ∑ U : DimSubspace K S u, lagrangianConstant (D-u)*(Fintype.card K : ℝ)^((D-u+1).choose 2) :=
        Finset.sum_le_sum (fun U _ => hb U)
      _ = _ := by simp [Nat.card_eq_fintype_card]
  calc
    _ ≤ (Nat.card Inc : ℝ) := Nat.cast_le.mpr (Nat.card_le_card_of_injective f hf)
    _ ≤ _ := hi
    _ ≤ (2^u*(Fintype.card K : ℝ)^(u*(finrank K S-u))) *
        (lagrangianConstant (D-u)*(Fintype.card K : ℝ)^((D-u+1).choose 2)) :=
      mul_le_mul_of_nonneg_right (subspace_count_upper u hu)
        (mul_nonneg (lagrangianConstant_pos (D-u)).le (by positivity))
    _ = _ := by rw [pow_add]; ring
end CommonCenterCounts
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ReducedCenterInjection
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]
variable (ω : LinearMap.BilinForm K E)
abbrev FixedCommonCenterProfile (c h₀ h₁ h₂ : ℕ) (S : IsotropicDimspace ω c)
    (Y : SymplecticLagrangian ω) (r : ℕ) :=
  {p : TripleDimProfile ω c h₀ h₁ h₂ // tripleProfileCommon ω p = S ∧
    finrank K ↥(p.val.1.val ⊓ Y.val) = r ∧
    finrank K ↥(p.val.2.1.val ⊓ Y.val) = r ∧
    finrank K ↥(p.val.2.2.val ⊓ Y.val) = r}
noncomputable def generalReductionLagrangian (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (S : Submodule K E) (hS : S ≤ ω.orthogonal S) (Y : SymplecticLagrangian ω) :
    SymplecticLagrangian (symplecticReductionForm ω S ha) :=
  ⟨reduceSubspace ω S Y.val,general_lagrangian_reduction ω S ha hω hS Y.val Y.property⟩
 theorem fixedCommonCenter_injection (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    {c h₀ h₁ h₂ r u : ℕ} (S : IsotropicDimspace ω c) (Y : CommonCenterSet ω S.val u) :
    ∃ f : FixedCommonCenterProfile ω c h₀ h₁ h₂ S Y.val r →
      SymplecticCenterProfile (symplecticReductionForm ω S.val ha)
        (generalReductionLagrangian ω ha hω S.val S.property.1 Y.val)
        (r-u) (h₀-c) (h₁-c) (h₂-c), Function.Injective f := by
  let F := FixedCommonCenterProfile ω c h₀ h₁ h₂ S Y.val r
  let Y' := generalReductionLagrangian ω ha hω S.val S.property.1 Y.val
  have heq (p : F) : (p.val.val.1.val ⊓ p.val.val.2.1.val) ⊓ p.val.val.2.2.val = S.val :=
    congrArg Subtype.val p.property.1
  have hL (p : F) : S.val ≤ p.val.val.1.val := (le_of_eq (heq p).symm).trans (inf_le_left.trans inf_le_left)
  have hM (p : F) : S.val ≤ p.val.val.2.1.val := (le_of_eq (heq p).symm).trans (inf_le_left.trans inf_le_right)
  have hN (p : F) : S.val ≤ p.val.val.2.2.val := (le_of_eq (heq p).symm).trans inf_le_right
  let L (p : F) := commonReductionLagrangian ω S.val ha S.property.1 p.val.val.1 (hL p)
  let M (p : F) := commonReductionLagrangian ω S.val ha S.property.1 p.val.val.2.1 (hM p)
  let N (p : F) := commonReductionLagrangian ω S.val ha S.property.1 p.val.val.2.2 (hN p)
  have hd (P : SymplecticLagrangian ω) (hSP : S.val ≤ P.val)
      (hPr : finrank K ↥(P.val ⊓ Y.val.val) = r) :
      finrank K ↥((commonReductionLagrangian ω S.val ha S.property.1 P hSP).val ⊓ Y'.val) = r-u := by
    have hh := reduce_center_intersection_finrank ω S.val P.val Y.val.val hSP
      (lagrangian_le_orthogonal ω S.val P.val P.property hSP)
    rw [Y.property,hPr] at hh
    change finrank K ↥(reduceSubspace ω S.val P.val ⊓ reduceSubspace ω S.val Y.val.val) = _
    omega
  let L' (p : F) : SymplecticCenterStratum (symplecticReductionForm ω S.val ha) Y' (r-u) :=
    ⟨L p,hd _ _ p.property.2.1⟩
  let M' (p : F) : SymplecticCenterStratum (symplecticReductionForm ω S.val ha) Y' (r-u) :=
    ⟨M p,hd _ _ p.property.2.2.1⟩
  let N' (p : F) : SymplecticCenterStratum (symplecticReductionForm ω S.val ha) Y' (r-u) :=
    ⟨N p,hd _ _ p.property.2.2.2⟩
  have hzero (p : F) : ((L p).val ⊓ (M p).val) ⊓ (N p).val = ⊥ := by
    change (reduceSubspace ω S.val p.val.val.1.val ⊓ reduceSubspace ω S.val p.val.val.2.1.val) ⊓
      reduceSubspace ω S.val p.val.val.2.2.val = ⊥
    rw [←reduceSubspace_inf ω S.val _ _ (hL p),←reduceSubspace_inf ω S.val _ _ (le_inf (hL p) (hM p)),heq p]
    exact reduceSubspace_self ω S.val
  have hp0 (p : F) : finrank K ↥((L p).val ⊓ (M p).val) = h₀-c := by
    change finrank K ↥(reduceSubspace ω S.val p.val.val.1.val ⊓ reduceSubspace ω S.val p.val.val.2.1.val) = _
    rw [reducePair_finrank ω S.val _ _ (hL p) (hM p),p.val.property.2.1,S.property.2]
  have hp1 (p : F) : finrank K ↥((L p).val ⊓ (N p).val) = h₁-c := by
    change finrank K ↥(reduceSubspace ω S.val p.val.val.1.val ⊓ reduceSubspace ω S.val p.val.val.2.2.val) = _
    rw [reducePair_finrank ω S.val _ _ (hL p) (hN p),p.val.property.2.2.1,S.property.2]
  have hp2 (p : F) : finrank K ↥((M p).val ⊓ (N p).val) = h₂-c := by
    change finrank K ↥(reduceSubspace ω S.val p.val.val.2.1.val ⊓ reduceSubspace ω S.val p.val.val.2.2.val) = _
    rw [reducePair_finrank ω S.val _ _ (hM p) (hN p),p.val.property.2.2.2,S.property.2]
  let f (p : F) : SymplecticCenterProfile (symplecticReductionForm ω S.val ha) Y'
      (r-u) (h₀-c) (h₁-c) (h₂-c) :=
    ⟨(L' p,M' p,N' p),hzero p,hp0 p,hp1 p,hp2 p⟩
  refine ⟨f,?_⟩
  intro p q hpq
  have heL : (L p).val = (L q).val := congrArg (fun r => r.val.1.val.val) hpq
  have heM : (M p).val = (M q).val := congrArg (fun r => r.val.2.1.val.val) hpq
  have heN : (N p).val = (N q).val := congrArg (fun r => r.val.2.2.val.val) hpq
  have hpL : p.val.val.1 = q.val.val.1 := congrArg Subtype.val
    (reduceLagrangian_injective ω S.val (a₁ := ⟨p.val.val.1,hL p⟩) (a₂ := ⟨q.val.val.1,hL q⟩) heL)
  have hpM : p.val.val.2.1 = q.val.val.2.1 := congrArg Subtype.val
    (reduceLagrangian_injective ω S.val (a₁ := ⟨p.val.val.2.1,hM p⟩) (a₂ := ⟨q.val.val.2.1,hM q⟩) heM)
  have hpN : p.val.val.2.2 = q.val.val.2.2 := congrArg Subtype.val
    (reduceLagrangian_injective ω S.val (a₁ := ⟨p.val.val.2.2,hN p⟩) (a₂ := ⟨q.val.val.2.2,hN q⟩) heN)
  exact Subtype.ext (Subtype.ext (Prod.ext hpL (Prod.ext hpM hpN)))
end ReducedCenterInjection
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
noncomputable def reducedPlantedSum (d r s₀ s₁ s₂ : ℕ) (q : ℝ) : ℝ :=
  ∑ θ : BaseParameters d r s₀ s₁ s₂,
    reducedPlantedConstant r s₀ s₁ s₂ θ.val * q^(reducedPlantedExponent d r s₀ s₁ s₂ θ.val)
 theorem reducedPlantedSum_nonneg (d r s₀ s₁ s₂ : ℕ) (q : ℝ) (hq : 0 ≤ q) :
    0 ≤ reducedPlantedSum d r s₀ s₁ s₂ q := by
  unfold reducedPlantedSum
  apply Finset.sum_nonneg
  intro θ _
  unfold reducedPlantedConstant
  positivity
section ReducedCardBound
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
 theorem symplectic_center_profile_card_upper (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D = finrank K E) (Y : SymplecticLagrangian ω)
    (r s₀ s₁ s₂ : ℕ) (hr : r ≤ D) :
    (Fintype.card K : ℝ)^(3*((r+1).choose 2)) *
      (Nat.card (SymplecticCenterProfile ω Y r s₀ s₁ s₂) : ℝ) ≤
      2^(3*D)*(Fintype.card K : ℝ)^(3*((D+1).choose 2))*
        reducedPlantedSum D r s₀ s₁ s₂ (Fintype.card K) := by
  have hd : finrank K Y.val = D := by
    have hh := self_orthogonal_twice_finrank ω Y.val hω Y.property
    omega
  have hp := symplectic_pair_card_bounds ω h2 ha hω D hD Y r hr
  have hq : (0:ℝ) < Fintype.card K := Nat.cast_pos.mpr Fintype.card_pos
  have hc : (0:ℝ) < Nat.card (SymplecticCenterStratum ω Y r) := by
    have hn : (0:ℝ) < (Fintype.card K : ℝ)^((r+1).choose 2) *
      Nat.card (SymplecticCenterStratum ω Y r) := (by positivity : (0:ℝ) <
        (Fintype.card K : ℝ)^((D+1).choose 2)).trans_le hp.1
    exact (mul_pos_iff_of_pos_left (pow_pos hq _)).mp hn
  have hb := symplectic_center_profile_probability_bound ω h2 ha hω Y r s₀ s₁ s₂ (by omega)
  rw [hd] at hb
  change (_ / _) ≤ reducedPlantedSum D r s₀ s₁ s₂ (Fintype.card K) at hb
  have hcount := (div_le_iff₀ (pow_pos hc 3)).mp hb
  have hpair : ((Fintype.card K : ℝ)^((r+1).choose 2) *
      Nat.card (SymplecticCenterStratum ω Y r))^3 ≤
      (2^D*(Fintype.card K : ℝ)^((D+1).choose 2))^3 := by
    exact pow_le_pow_left₀ (by positivity) hp.2 3
  calc
    _ ≤ (Fintype.card K : ℝ)^(3*((r+1).choose 2)) *
        (reducedPlantedSum D r s₀ s₁ s₂ (Fintype.card K)*
          (Nat.card (SymplecticCenterStratum ω Y r) : ℝ)^3) :=
      mul_le_mul_of_nonneg_left hcount (by positivity)
    _ = ((Fintype.card K : ℝ)^((r+1).choose 2) *
        Nat.card (SymplecticCenterStratum ω Y r))^3 *
        reducedPlantedSum D r s₀ s₁ s₂ (Fintype.card K) := by
      rw [mul_pow,←pow_mul,Nat.mul_comm 3]; ring
    _ ≤ (2^D*(Fintype.card K : ℝ)^((D+1).choose 2))^3 *
        reducedPlantedSum D r s₀ s₁ s₂ (Fintype.card K) :=
      mul_le_mul_of_nonneg_right hpair (reducedPlantedSum_nonneg _ _ _ _ _ _ (by positivity))
    _ = _ := by rw [mul_pow,←pow_mul,←pow_mul]; congr 2 <;> rw [Nat.mul_comm]
 theorem fixedCommonCenter_card_upper (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D = finrank K E) {c h₀ h₁ h₂ r u : ℕ}
    (S : IsotropicDimspace ω c) (Y : CommonCenterSet ω S.val u) (hr : r-u ≤ D-c) :
    (Fintype.card K : ℝ)^(3*((r-u+1).choose 2)) *
      (Nat.card (FixedCommonCenterProfile ω c h₀ h₁ h₂ S Y.val r) : ℝ) ≤
      2^(3*(D-c))*(Fintype.card K : ℝ)^(3*((D-c+1).choose 2))*
        reducedPlantedSum (D-c) (r-u) (h₀-c) (h₁-c) (h₂-c) (Fintype.card K) := by
  let := Module.finite_of_finite K (M := ReducedSpace ω S.val)
  have hc := isotropic_finrank_le_half ω hω D hD S.val S.property.1
  rw [S.property.2] at hc
  have hd := reducedSpace_finrank ω S.val hω S.property.1
  rw [S.property.2] at hd
  obtain ⟨f,hf⟩ := fixedCommonCenter_injection ω ha hω (h₀ := h₀) (h₁ := h₁) (h₂ := h₂) (r := r) S Y
  have hh := symplectic_center_profile_card_upper (symplecticReductionForm ω S.val ha) h2
    (symplecticReductionForm_alt ω S.val ha) (symplecticReductionForm_nondegenerate ω S.val ha hω)
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
abbrev CommonParameters (D r c : ℕ) := {u : Fin (c+1) // u.val ≤ r ∧ r-u.val ≤ D-c}
noncomputable instance (D r c : ℕ) : Fintype (CommonParameters D r c) := Fintype.ofFinite _
abbrev ProfileCenterSet (c h₀ h₁ h₂ r : ℕ) :=
  Σ p : TripleDimProfile ω c h₀ h₁ h₂, TripleCenterSet ω r p.val.1.val p.val.2.1.val p.val.2.2.val
abbrev PlantedCommonData (D c h₀ h₁ h₂ r : ℕ) :=
  Σ S : IsotropicDimspace ω c, Σ u : CommonParameters D r c,
    Σ Y : CommonCenterSet ω S.val u.val.val, FixedCommonCenterProfile ω c h₀ h₁ h₂ S Y.val r
 theorem profileCenter_injection (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D = finrank K E) (c h₀ h₁ h₂ r : ℕ) :
    ∃ f : ProfileCenterSet ω c h₀ h₁ h₂ r → PlantedCommonData ω D c h₀ h₁ h₂ r,
      Function.Injective f := by
  let F := ProfileCenterSet ω c h₀ h₁ h₂ r
  let S (p : F) := tripleProfileCommon ω p.1
  let u (p : F) := finrank K ↥((S p).val ⊓ p.2.val.val)
  have hS (p : F) : (S p).val ≤ p.1.val.1.val := inf_le_left.trans inf_le_left
  have hu (p : F) : u p ≤ c :=
    (Submodule.finrank_mono (inf_le_left : (S p).val ⊓ p.2.val.val ≤ (S p).val)).trans_eq (S p).property.2
  have hur (p : F) : u p ≤ r :=
    (Submodule.finrank_mono (inf_le_inf_right p.2.val.val (hS p))).trans_eq p.2.property.1
  have hdr (p : F) : r-u p ≤ D-c := by
    have hi := (S p).property.1
    have hc := isotropic_finrank_le_half ω hω D hD (S p).val hi
    have hd := reducedSpace_finrank ω (S p).val hω hi
    rw [(S p).property.2,hD.symm] at hd
    rw [(S p).property.2] at hc
    let Y' := generalReductionLagrangian ω ha hω (S p).val hi p.2.val
    let := Module.finite_of_finite K (M := ReducedSpace ω (S p).val)
    have hy := self_orthogonal_twice_finrank (symplecticReductionForm ω (S p).val ha) Y'.val
      (symplecticReductionForm_nondegenerate ω (S p).val ha hω) Y'.property
    have he := reduce_center_intersection_finrank ω (S p).val p.1.val.1.val p.2.val.val
      (hS p) (lagrangian_le_orthogonal ω (S p).val p.1.val.1.val p.1.val.1.property (hS p))
    rw [p.2.property.1] at he
    have hm := Submodule.finrank_mono (inf_le_right :
      reduceSubspace ω (S p).val p.1.val.1.val ⊓ Y'.val ≤ Y'.val)
    change finrank K ↥(reduceSubspace ω (S p).val p.1.val.1.val ⊓ Y'.val) + u p = r at he
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
    (S : IsotropicDimspace ω c) (Y : CommonCenterSet ω S.val u) (hr : r-u ≤ D-c) :
    (Nat.card (FixedCommonCenterProfile ω c h₀ h₁ h₂ S Y.val r) : ℝ) ≤
      2^(3*(D-c))*(Fintype.card K : ℝ)^((3*((D-c+1).choose 2):ℕ)-(3*((r-u+1).choose 2):ℝ))*
        reducedPlantedSum (D-c) (r-u) (h₀-c) (h₁-c) (h₂-c) (Fintype.card K) :=
by
  simpa only [Nat.cast_mul,Nat.cast_ofNat] using
    unweight_count_bound (Nat.cast_pos.mpr Fintype.card_pos) _ _
      (fixedCommonCenter_card_upper ω h2 ha hω D hD (h₀ := h₀) (h₁ := h₁) (h₂ := h₂) S Y hr)
 theorem commonData_fixed_card_upper (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D = finrank K E) {c h₀ h₁ h₂ r : ℕ}
    (S : IsotropicDimspace ω c) (u : CommonParameters D r c) :
    (Nat.card (Σ Y : CommonCenterSet ω S.val u.val.val,
      FixedCommonCenterProfile ω c h₀ h₁ h₂ S Y.val r) : ℝ) ≤
      (2^u.val.val*lagrangianConstant (D-u.val.val))*2^(3*(D-c)) *
        (Fintype.card K : ℝ)^((u.val.val*(c-u.val.val)+(D-u.val.val+1).choose 2:ℕ)+
          (3*((D-c+1).choose 2):ℕ)-(3*((r-u.val.val+1).choose 2):ℝ))*
        reducedPlantedSum (D-c) (r-u.val.val) (h₀-c) (h₁-c) (h₂-c) (Fintype.card K) := by
  classical
  let := Fintype.ofFinite (CommonCenterSet ω S.val u.val.val)
  have hq : (0:ℝ) < Fintype.card K := Nat.cast_pos.mpr Fintype.card_pos
  let A : ℝ := 2^(3*(D-c))*(Fintype.card K : ℝ)^((3*((D-c+1).choose 2):ℕ)-(3*((r-u.val.val+1).choose 2):ℝ))*
        reducedPlantedSum (D-c) (r-u.val.val) (h₀-c) (h₁-c) (h₂-c) (Fintype.card K)
  have hA : 0 ≤ A := mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg hq.le _))
    (reducedPlantedSum_nonneg _ _ _ _ _ _ hq.le)
  have hu : u.val.val ≤ finrank K S.val := by rw [S.property.2]; exact Nat.le_of_lt_succ u.val.isLt
  have hc := commonCenter_card_upper ω h2 ha hω D hD S.val S.property.1 u.val.val hu
  rw [S.property.2] at hc
  calc
    _ = ∑ Y : CommonCenterSet ω S.val u.val.val,
        (Nat.card (FixedCommonCenterProfile ω c h₀ h₁ h₂ S Y.val r) : ℝ) := by rw [Nat.card_sigma,Nat.cast_sum]
    _ ≤ ∑ _Y : CommonCenterSet ω S.val u.val.val, A :=
      Finset.sum_le_sum (fun Y _ => fixedCommonCenter_card_rpow_upper ω h2 ha hω D hD S Y u.property.2)
    _ = (Nat.card (CommonCenterSet ω S.val u.val.val) : ℝ)*A := by simp [Nat.card_eq_fintype_card]
    _ ≤ (2^u.val.val*lagrangianConstant (D-u.val.val)*
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
noncomputable def commonPlantedTerm (D c r h₀ h₁ h₂ : ℕ) (u : CommonParameters D r c) (q : ℝ) : ℝ :=
  (2^u.val.val*lagrangianConstant (D-u.val.val))*2^(3*(D-c)) *
    q^((u.val.val*(c-u.val.val)+(D-u.val.val+1).choose 2:ℕ)+
      (3*((D-c+1).choose 2):ℕ)-(3*((r-u.val.val+1).choose 2):ℝ))*
    reducedPlantedSum (D-c) (r-u.val.val) (h₀-c) (h₁-c) (h₂-c) q
 theorem commonPlantedTerm_nonneg (D c r h₀ h₁ h₂ : ℕ) (u : CommonParameters D r c) (q : ℝ)
    (hq : 0 ≤ q) : 0 ≤ commonPlantedTerm D c r h₀ h₁ h₂ u q := by
  unfold commonPlantedTerm
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by positivity)
    (lagrangianConstant_pos _).le) (by positivity)) (Real.rpow_nonneg hq _))
    (reducedPlantedSum_nonneg _ _ _ _ _ _ hq)
section FullProfileCenterBound
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
 theorem profileCenter_card_upper (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D = finrank K E) (c h₀ h₁ h₂ r : ℕ) (hc : c ≤ D) :
    (Nat.card (ProfileCenterSet ω c h₀ h₁ h₂ r) : ℝ) ≤
      (lagrangianConstant D*2^c)*(Fintype.card K : ℝ)^(isotropicExponent D c) *
        ∑ u : CommonParameters D r c, commonPlantedTerm D c r h₀ h₁ h₂ u (Fintype.card K) := by
  classical
  let := Fintype.ofFinite (IsotropicDimspace ω c)
  obtain ⟨f,hf⟩ := profileCenter_injection ω ha hω D hD c h₀ h₁ h₂ r
  have hs (S : IsotropicDimspace ω c) :
      (Nat.card (Σ u : CommonParameters D r c, Σ Y : CommonCenterSet ω S.val u.val.val,
        FixedCommonCenterProfile ω c h₀ h₁ h₂ S Y.val r) : ℝ) ≤
      ∑ u : CommonParameters D r c, commonPlantedTerm D c r h₀ h₁ h₂ u (Fintype.card K) := by
    rw [Nat.card_sigma,Nat.cast_sum]
    exact Finset.sum_le_sum (fun u _ => commonData_fixed_card_upper ω h2 ha hω D hD S u)
  calc
    _ ≤ (Nat.card (PlantedCommonData ω D c h₀ h₁ h₂ r) : ℝ) :=
      Nat.cast_le.mpr (Nat.card_le_card_of_injective f hf)
    _ = ∑ S : IsotropicDimspace ω c,
        (Nat.card (Σ u : CommonParameters D r c, Σ Y : CommonCenterSet ω S.val u.val.val,
          FixedCommonCenterProfile ω c h₀ h₁ h₂ S Y.val r) : ℝ) := by rw [Nat.card_sigma,Nat.cast_sum]
    _ ≤ ∑ _S : IsotropicDimspace ω c,
        ∑ u : CommonParameters D r c, commonPlantedTerm D c r h₀ h₁ h₂ u (Fintype.card K) :=
      Finset.sum_le_sum (fun S _ => hs S)
    _ = (Nat.card (IsotropicDimspace ω c) : ℝ)*
        ∑ u : CommonParameters D r c, commonPlantedTerm D c r h₀ h₁ h₂ u (Fintype.card K) := by
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
 theorem orbit_member_profile (L M N : SymplecticLagrangian ω)
    (P : OrderedTripleOrbit ω L.val M.val N.val) :
    ω.orthogonal P.val.1 = P.val.1 ∧ ω.orthogonal P.val.2.1 = P.val.2.1 ∧
    ω.orthogonal P.val.2.2 = P.val.2.2 ∧
    finrank K ↥((P.val.1 ⊓ P.val.2.1) ⊓ P.val.2.2) = finrank K ↥((L.val ⊓ M.val) ⊓ N.val) ∧
    finrank K ↥(P.val.1 ⊓ P.val.2.1) = finrank K ↥(L.val ⊓ M.val) ∧
    finrank K ↥(P.val.1 ⊓ P.val.2.2) = finrank K ↥(L.val ⊓ N.val) ∧
    finrank K ↥(P.val.2.1 ⊓ P.val.2.2) = finrank K ↥(M.val ⊓ N.val) := by
  obtain ⟨e,he,hL,hM,hN⟩ := P.property
  rw [←hL,←hM,←hN]
  refine ⟨(lagrangianIsometryEquiv ω e he L).property,
    (lagrangianIsometryEquiv ω e he M).property,
    (lagrangianIsometryEquiv ω e he N).property,?_,map_pair_finrank e _ _,map_pair_finrank e _ _,map_pair_finrank e _ _⟩
  rw [←Submodule.map_inf e.toLinearMap e.injective,←Submodule.map_inf e.toLinearMap e.injective,e.finrank_map_eq]
omit [FiniteDimensional K E] in
 theorem orbitCenter_profile_injection (L M N : SymplecticLagrangian ω) (r : ℕ) :
    ∃ f : (Σ P : OrderedTripleOrbit ω L.val M.val N.val,
      TripleCenterSet ω r P.val.1 P.val.2.1 P.val.2.2) →
      ProfileCenterSet ω (finrank K ↥((L.val ⊓ M.val) ⊓ N.val))
        (finrank K ↥(L.val ⊓ M.val)) (finrank K ↥(L.val ⊓ N.val)) (finrank K ↥(M.val ⊓ N.val)) r,
      Function.Injective f := by
  let F := Σ P : OrderedTripleOrbit ω L.val M.val N.val,
      TripleCenterSet ω r P.val.1 P.val.2.1 P.val.2.2
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
 theorem orbit_center_count_le_profile [Finite E] (L M N : SymplecticLagrangian ω) (r : ℕ) :
    Nat.card (OrderedTripleOrbit ω L.val M.val N.val) * Nat.card (TripleCenterSet ω r L.val M.val N.val) ≤
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
noncomputable def tripleFaceDensity (r : ℕ) (A L M N : SymplecticLagrangian ω) : ℝ :=
  (Nat.card (TripleCenterSet ω r L.val M.val N.val) : ℝ)*
    (Nat.card (SymplecticLagrangian ω) : ℝ)^2 /
    (Nat.card (SymplecticCenterStratum ω A r) : ℝ)^3
 omit [Fintype K] [Finite E] in
 theorem tripleFaceDensity_nonneg (r : ℕ) (A L M N : SymplecticLagrangian ω) :
    0 ≤ tripleFaceDensity ω r A L M N := by unfold tripleFaceDensity; positivity
 theorem symplectic_center_stratum_card_pos (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D = finrank K E) (A : SymplecticLagrangian ω) (r : ℕ) (hr : r ≤ D) :
    (0:ℝ) < Nat.card (SymplecticCenterStratum ω A r) := by
  have hp := (symplectic_pair_card_bounds ω h2 ha hω D hD A r hr).1
  have hq : (0:ℝ) < Fintype.card K := Nat.cast_pos.mpr Fintype.card_pos
  have hn : (0:ℝ) < (Fintype.card K : ℝ)^((r+1).choose 2) *
      Nat.card (SymplecticCenterStratum ω A r) := (by positivity : (0:ℝ) <
        (Fintype.card K : ℝ)^((D+1).choose 2)).trans_le hp
  exact (mul_pos_iff_of_pos_left (pow_pos hq _)).mp hn
 theorem tripleFaceDensity_profile_bound [Invertible (2:K)]
    (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D = finrank K E) (hq : 4*lagrangianConstant D ≤ (Fintype.card K : ℝ))
    (r : ℕ) (hr : r ≤ D) (A L M N : SymplecticLagrangian ω) :
    tripleFaceDensity ω r A L M N ≤
      (orbitMassConstant D*(lagrangianConstant D)^2) *
        (Fintype.card K : ℝ)^((tripleDefect D L.val M.val N.val : ℝ)+
          (3*((r+1).choose 2):ℕ)-(4*((D+1).choose 2):ℕ)) *
        (Nat.card (ProfileCenterSet ω (finrank K ↥((L.val ⊓ M.val) ⊓ N.val))
          (finrank K ↥(L.val ⊓ M.val)) (finrank K ↥(L.val ⊓ N.val)) (finrank K ↥(M.val ⊓ N.val)) r) : ℝ) := by
  let q : ℝ := Fintype.card K
  have hq0 : 0 < q := Nat.cast_pos.mpr Fintype.card_pos
  have hOrbit := tripleOrbit_card_lower ω ha hω D hD hq L M N
  have hCenter := orbit_center_count_le_profile ω L M N r
  have hPair := (symplectic_pair_card_bounds ω h2 ha hω D hD A r hr).1
  have hLag := (symplecticLagrangian_card_bounds ω h2 ha hω D hD).2
  have hi := normalized_count_ratio_bound
    (p := q^((D+1).choose 2)) (t := q^((r+1).choose 2))
    (s := q^(tripleDefect D L.val M.val N.val))
    (O := Nat.card (OrderedTripleOrbit ω L.val M.val N.val))
    (Z := Nat.card (TripleCenterSet ω r L.val M.val N.val))
    (T := Nat.card (ProfileCenterSet ω (finrank K ↥((L.val ⊓ M.val) ⊓ N.val))
      (finrank K ↥(L.val ⊓ M.val)) (finrank K ↥(L.val ⊓ N.val)) (finrank K ↥(M.val ⊓ N.val)) r))
    (A := Nat.card (SymplecticCenterStratum ω A r)) (L := Nat.card (SymplecticLagrangian ω))
    (C := orbitMassConstant D) (B := lagrangianConstant D)
    (pow_pos hq0 _) (symplectic_center_stratum_card_pos ω h2 ha hω D hD A r hr)
    (by positivity) (by positivity) (by positivity) (by positivity)
    (orbitMassConstant_pos D).le (lagrangianConstant_pos D).le (by positivity) (by positivity)
    (by simpa only [←pow_mul,Nat.mul_comm] using hOrbit)
    (by exact_mod_cast hCenter) hPair hLag
  refine hi.trans_eq ?_
  change _ = _*q^((tripleDefect D L.val M.val N.val : ℝ)+(3*((r+1).choose 2):ℕ)-(4*((D+1).choose 2):ℕ))*_
  rw [Real.rpow_sub hq0,Real.rpow_add hq0,Real.rpow_natCast,Real.rpow_natCast,Real.rpow_natCast]
  simp only [pow_mul,pow_succ]
  ring
 theorem tripleFaceDensity_full_bound [Invertible (2:K)]
    (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D = finrank K E) (hq : 4*lagrangianConstant D ≤ (Fintype.card K : ℝ))
    (r : ℕ) (hr : r ≤ D) (A L M N : SymplecticLagrangian ω) :
    let c := finrank K ↥((L.val ⊓ M.val) ⊓ N.val)
    let h₀ := finrank K ↥(L.val ⊓ M.val)
    let h₁ := finrank K ↥(L.val ⊓ N.val)
    let h₂ := finrank K ↥(M.val ⊓ N.val)
    tripleFaceDensity ω r A L M N ≤
      (orbitMassConstant D*(lagrangianConstant D)^2) *
        (Fintype.card K : ℝ)^((tripleDefect D L.val M.val N.val : ℝ)+
          (3*((r+1).choose 2):ℕ)-(4*((D+1).choose 2):ℕ)) *
        ((lagrangianConstant D*2^c)*(Fintype.card K : ℝ)^(isotropicExponent D c) *
          ∑ u : CommonParameters D r c, commonPlantedTerm D c r h₀ h₁ h₂ u (Fintype.card K)) := by
  dsimp only
  have hc : finrank K ↥((L.val ⊓ M.val) ⊓ N.val) ≤ D :=
    isotropic_finrank_le_half ω hω D hD _ (by intro x hx y hy; exact L.property.ge hx.1.1 y hy.1.1)
  have hh := profileCenter_card_upper ω h2 ha hω D hD
    (finrank K ↥((L.val ⊓ M.val) ⊓ N.val))
    (finrank K ↥(L.val ⊓ M.val)) (finrank K ↥(L.val ⊓ N.val)) (finrank K ↥(M.val ⊓ N.val)) r hc
  have hq0 : (0:ℝ) ≤ Fintype.card K := by positivity
  exact (tripleFaceDensity_profile_bound ω h2 ha hω D hD hq r hr A L M N).trans
    (mul_le_mul_of_nonneg_left hh (mul_nonneg (mul_nonneg (orbitMassConstant_pos D).le (sq_nonneg _))
      (Real.rpow_nonneg hq0 _)))
end PointwisePlanted
end SidorenkoCounterexample
namespace SidorenkoCounterexample
noncomputable def triangular (n : ℝ) : ℝ := n*(n+1)/2
noncomputable def plantedGain (c d δ v : ℝ) (p t : Fin 3 → ℝ) : ℝ :=
  ((d+c)/2+c+1)*((c+δ)/2)-2*((c+δ)/2)^2 +
    (∑ i, triangular (p i+t i)) - δ*(∑ i, p i) - (∑ i, (p i)^2) -
    v*((d-3*δ)/2-(∑ i, p i)+v) - (∑ i, triangular (t i)) + triangular v
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open scoped BigOperators
noncomputable def faceBaseline (D c : ℝ) (s : Fin 3 → ℝ) : ℝ :=
  ((D+1)*c + ∑ i, triangular (s i))/2 - (∑ i, triangular (c+s i))/6
 theorem triangular_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ triangular x := by
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
noncomputable def tailGain (D : ℕ) (full : Bool) (a : TailTuple) : ℝ :=
  if full then plantedGain a.c ((D:ℝ)-a.c) a.delta a.v (fun i => a.p i) (fun i => a.t i)
  else triangular (a.maxH/2:ℕ)
def TailFeasible (D : ℕ) (full : Bool) (a : TailTuple) : Prop :=
  a.c ≤ D ∧ (∑ i, a.s i) ≤ D-a.c ∧ (full=true →
    a.u ≤ a.c ∧
    (∀ i, (a.t i:ℝ) ≤ a.p i+a.delta) ∧
    (∀ i, (a.v:ℝ) ≤ a.p i+a.delta) ∧
    0 ≤ (((D:ℝ)-a.c-3*a.delta)/2)-a.P+a.v)
 theorem TailTuple.h_le_max (a : TailTuple) (i : Fin 3) : a.h i ≤ a.maxH :=
  Finset.le_sup (Finset.mem_univ i)
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open scoped BigOperators
def plantedTailTuple (D r c : ℕ) (s : Fin 3 → ℕ)
    (u : CommonParameters D r c)
    (θ : BaseParameters (D-c) (r-u.val.val) (s 0) (s 1) (s 2)) : TailTuple where
  c := c
  u := u.val.val
  v := D-c-θ.val.2.2.2.val
  p := ![θ.val.1.val,θ.val.2.1.val,θ.val.2.2.1.val]
  t := ![s 0-θ.val.1.val,s 1-θ.val.2.1.val,s 2-θ.val.2.2.1.val]
theorem plantedTailTuple_s (D r c : ℕ) (s : Fin 3 → ℕ)
    (u : CommonParameters D r c)
    (θ : BaseParameters (D-c) (r-u.val.val) (s 0) (s 1) (s 2)) (i : Fin 3) :
    (plantedTailTuple D r c s u θ).s i = s i := by
  have h := θ.property
  unfold BaseFeasible at h
  fin_cases i <;> simp [plantedTailTuple,TailTuple.s] <;> omega
theorem plantedTailTuple_feasible (D r c : ℕ) (hD : D=2*r) (hc : c ≤ D)
    (s : Fin 3 → ℕ) (hs : (∑ i, s i) ≤ D-c)
    (u : CommonParameters D r c)
    (θ : BaseParameters (D-c) (r-u.val.val) (s 0) (s 1) (s 2)) :
    TailFeasible D true (plantedTailTuple D r c s u θ) := by
  have hu := u.property.1
  have huc : u.val.val ≤ c := Nat.le_of_lt_succ u.val.isLt
  have hθ := θ.property
  unfold BaseFeasible at hθ
  have hn : θ.val.2.2.2.val ≤ D-c := Nat.le_of_lt_succ θ.val.2.2.2.isLt
  have hdc : ((D-c:ℕ):ℝ) = (D:ℝ)-c := Nat.cast_sub hc
  have hru : ((r-u.val.val:ℕ):ℝ) = (r:ℝ)-u.val.val := Nat.cast_sub hu
  have hDs : (D:ℝ)=2*r := by exact_mod_cast hD
  refine ⟨hc,?_,fun _ => ⟨huc,?_,?_,?_⟩⟩
  · change (∑ i, (plantedTailTuple D r c s u θ).s i) ≤ D-c
    simpa only [plantedTailTuple_s] using hs
  · intro i
    fin_cases i
    all_goals dsimp [plantedTailTuple,TailTuple.delta]
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
    all_goals dsimp [plantedTailTuple,TailTuple.delta]
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
    simp only [plantedTailTuple,TailTuple.delta,TailTuple.P,Fin.sum_univ_three,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,Nat.cast_sub hn,hdc]
    linarith
noncomputable def fullPlantedExponent (D c r : ℕ) (s : Fin 3 → ℕ)
    (u : CommonParameters D r c)
    (θ : BaseParameters (D-c) (r-u.val.val) (s 0) (s 1) (s 2)) : ℝ :=
  ((D:ℝ)+1)*c+(∑ i, triangular (s i))+3*triangular r-4*triangular D+
    isotropicExponent D c+(u.val.val:ℝ)*(c-u.val.val:ℕ)+triangular (D-u.val.val:ℕ)+
    3*triangular (D-c:ℕ)-3*triangular (r-u.val.val:ℕ)+
    reducedPlantedExponent (D-c) (r-u.val.val) (s 0) (s 1) (s 2) θ.val
theorem fullPlantedExponent_eq (D c r : ℕ) (hD : D=2*r) (hc : c ≤ D)
    (s : Fin 3 → ℕ) (u : CommonParameters D r c)
    (θ : BaseParameters (D-c) (r-u.val.val) (s 0) (s 1) (s 2)) :
    fullPlantedExponent D c r s u θ = tailGain D true (plantedTailTuple D r c s u θ) := by
  have hu := u.property.1
  have huc : u.val.val ≤ c := Nat.le_of_lt_succ u.val.isLt
  have huD : u.val.val ≤ D := huc.trans hc
  have hθ := θ.property
  unfold BaseFeasible at hθ
  have hn : θ.val.2.2.2.val ≤ D-c := Nat.le_of_lt_succ θ.val.2.2.2.isLt
  have hiso : (isotropicExponent D c:ℝ) + triangular (D-c:ℕ) = triangular D+(c:ℝ)*(D-c:ℕ) := by
    have hh := congrArg (Nat.cast : ℕ → ℝ) (isotropicExponent_add D c hc)
    simpa only [Nat.cast_add,Nat.cast_mul,triangular_nat] using hh
  have hDs : (D:ℝ)=2*r := by exact_mod_cast hD
  have h0 : θ.val.1.val ≤ s 0 := hθ.2.2.2.2.2.1
  have h1 : θ.val.2.1.val ≤ s 1 := hθ.2.2.2.2.2.2.1
  have h2 : θ.val.2.2.1.val ≤ s 2 := hθ.2.2.2.2.2.2.2.1
  unfold fullPlantedExponent tailGain plantedGain plantedTailTuple TailTuple.delta reducedPlantedExponent
  simp only [ite_true,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,Nat.cast_add,triangular_nat,Nat.cast_sub hn,Nat.cast_sub hc,
    Nat.cast_sub hu,Nat.cast_sub huc,Nat.cast_sub huD,Nat.cast_sub h0,Nat.cast_sub h1,Nat.cast_sub h2]
  rw [Nat.cast_sub hc] at hiso
  dsimp [triangular] at hiso ⊢
  rw [show (isotropicExponent D c:ℝ) = _ from (eq_sub_iff_add_eq.mpr hiso)]
  rw [hDs]
  ring
end SidorenkoCounterexample
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
 theorem pairFormDifference_graph (F : SymForm K A) (G : SymForm K B) :
    (pairFormDifference A B (F,G)).val = graphDifference A B F.val G.val := rfl
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
abbrev SubspacePairProfile (r p : ℕ) :=
  {R : DimSubspace K V r × DimSubspace K V r // finrank K ↥(R.1.val ⊓ R.2.val) = p}
abbrev PairBaseCode (r p : ℕ) :=
  Σ R : DimSubspace K V r, Σ P : DimSubspace K R.val p,
    {S : DimSubspace K V r // P.val.map R.val.subtype ≤ S.val}
noncomputable def pairBaseCode {r p : ℕ} (RS : SubspacePairProfile (K := K) (V := V) r p) :
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
    (Nat.card (SubspacePairProfile (K := K) (V := V) r p) : ℝ) ≤
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
    have hc := subspace_count_upper (K := K) (V := R.val) p (by rwa [R.property])
    rw [R.property] at hc
    exact mul_le_mul_of_nonneg_right hc (by positivity)
  have hc : (Nat.card (SubspacePairProfile (K := K) (V := V) r p) : ℝ) ≤
      Nat.card (PairBaseCode (K := K) (V := V) r p) := by
    exact_mod_cast Nat.card_le_card_of_injective _ (pairBaseCode_injective (K := K) (V := V) r p)
  refine (hc.trans (real_card_sigma_le _ hR)).trans ?_
  exact mul_le_mul_of_nonneg_right (subspace_count_upper r hr) (by positivity)
 theorem subspacePairProfile_probability_bound (r p : ℕ) (hD : finrank K V = 2*r) (hp : p ≤ r) :
    (Fintype.card K : ℝ)^(p*p) * Nat.card (SubspacePairProfile (K := K) (V := V) r p) ≤
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
    q^(p*p)*Nat.card (SubspacePairProfile (K := K) (V := V) r p) ≤
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
abbrev PairParameters (r h : ℕ) := {p : Fin (r+1) // p.val ≤ h ∧ h-p.val ≤ p.val}
noncomputable instance pairParametersFintype (r h : ℕ) : Fintype (PairParameters r h) := Fintype.ofFinite _
section PairLiftCounts
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
abbrev DualPairBase (r : ℕ) := DimSubspace K (Module.Dual K V) r × DimSubspace K (Module.Dual K V) r
abbrev DualPairForms {r : ℕ} (R : DualPairBase (K := K) (V := V) r) :=
  SymForm K R.1.val.dualCoannihilator × SymForm K R.2.val.dualCoannihilator
abbrev CanonicalPairProfile (r h : ℕ) :=
  {RF : Σ R : DualPairBase (K := K) (V := V) r, DualPairForms R //
    finrank K ↥((dualGraph RF.1.1.val RF.2.1).val ⊓ (dualGraph RF.1.2.val RF.2.2).val) = h}
abbrev DualPairLiftEvent {r p : ℕ} (R : SubspacePairProfile (K := K) (V := Module.Dual K V) r p) (t : ℕ) :=
  {F : DualPairForms R.val // t ≤ finrank K (graphDifference _ _ F.1.val F.2.val).ker}
abbrev CenterPairProfile (r h : ℕ) :=
  {L : CenterStratum (K := K) (V := V) r × CenterStratum (K := K) (V := V) r //
    finrank K ↥(L.1.val.val ⊓ L.2.val.val) = h}
noncomputable def dualPairProductEquiv (r : ℕ) (hr : r ≤ finrank K V) :
    (Σ R : DualPairBase (K := K) (V := V) r, DualPairForms R) ≃
      CenterStratum (K := K) (V := V) r × CenterStratum (K := K) (V := V) r :=
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
    (P : CanonicalPairProfile (K := K) (V := V) r h) : PairParameters r h := by
  let p := finrank K ↥(P.val.1.1.val ⊓ P.val.1.2.val)
  have hpr : p ≤ r := (Submodule.finrank_mono inf_le_left).trans_eq P.val.1.1.property
  have hph : p ≤ h := by
    simpa only [P.property] using dualGraph_pair_finrank_ge P.val.1.1.val P.val.1.2.val P.val.2.1 P.val.2.2
  have ht := dualGraph_pair_extra_feasible P.val.1.1 P.val.1.2 P.val.2.1 P.val.2.2 P.property
  refine ⟨⟨p,by omega⟩,hph,?_⟩
  dsimp [p] at *
  omega
 theorem dualGraph_pair_kernel_exact (R S : Submodule K (Module.Dual K V))
    (F : SymForm K R.dualCoannihilator) (G : SymForm K S.dualCoannihilator) :
    finrank K ↥((dualGraph R F).val ⊓ (dualGraph S G).val) =
      finrank K ↥(R ⊓ S)+finrank K (graphDifference _ _ F.val G.val).ker := by
  have hh := graph_pair_intersection_finrank R.dualCoannihilator S.dualCoannihilator F.val G.val
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
    Σ p : PairParameters r h, Σ R : SubspacePairProfile (K := K) (V := Module.Dual K V) r p.val.val,
      DualPairLiftEvent R (h-p.val.val) :=
  ⟨canonicalPairParameter hD P,⟨P.val.1,rfl⟩,P.val.2,
    dualGraph_pair_kernel_ge _ _ _ _ h P.property⟩
 theorem canonicalPairCoding_injective {r h : ℕ} (hD : finrank K V=2*r) :
    Function.Injective (canonicalPairCoding (K := K) (V := V) (h := h) hD) := by
  let recover : (Σ p : PairParameters r h, Σ R : SubspacePairProfile (K := K) (V := Module.Dual K V) r p.val.val,
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
    (Nat.card (CenterStratum (K := K) (V := V) r):ℝ)^2 =
      (Nat.card (DimSubspace K (Module.Dual K V) r):ℝ)^2 *
        (Fintype.card K:ℝ)^(2*((finrank K V-r+1).choose 2)) := by
  rw [vertical_pair_count r hr,Nat.cast_mul,Nat.cast_pow,mul_pow,
    Nat.card_congr (dualDimSubspaceEquiv (K := K) (V := V) r hr),←pow_mul,Nat.mul_comm _ 2]
 theorem dualPairLift_probability_bound {r p : ℕ} (hD : finrank K V=2*r)
    (R : SubspacePairProfile (K := K) (V := Module.Dual K V) r p) (t : ℕ) (ht : t ≤ p) :
    (Nat.card (DualPairLiftEvent R t):ℝ)/Nat.card (DualPairForms R.val) ≤
      2^t/(Fintype.card K:ℝ)^((t+1).choose 2) := by
  have hd := coannihilator_pair_finrank R.val.1.val R.val.2.val
  rw [R.val.1.property,R.val.2.property,R.property,hD] at hd
  exact pairFormDifference_nullity_bound _ _ t (by omega)
 theorem pairPlanted_bound_one (r h : ℕ) (hD : finrank K V=2*r) (p : PairParameters r h) :
    (Nat.card (Σ R : SubspacePairProfile (K := K) (V := Module.Dual K V) r p.val.val,
      DualPairLiftEvent R (h-p.val.val)):ℝ) /
      (Nat.card (CenterStratum (K := K) (V := V) r):ℝ)^2 ≤
        2^(2*r+p.val.val+(h-p.val.val)) /
          (Fintype.card K:ℝ)^(p.val.val*p.val.val+(h-p.val.val+1).choose 2) := by
  classical
  let := Module.finite_of_finite K (M := Module.Dual K V)
  let RType := SubspacePairProfile (K := K) (V := Module.Dual K V) r p.val.val
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
      (Nat.card (CenterStratum (K := K) (V := V) r):ℝ)^2 ≤
    ∑ p : PairParameters r h, 2^(2*r+p.val.val+(h-p.val.val)) /
      (Fintype.card K:ℝ)^(p.val.val*p.val.val+(h-p.val.val+1).choose 2) := by
  classical
  let := Module.finite_of_finite K (M := Module.Dual K V)
  have hr : r ≤ finrank K V := by omega
  rw [←Nat.card_congr (canonicalPairProfileEquiv r h hr)]
  have hc := Nat.card_le_card_of_injective _ (canonicalPairCoding_injective (K := K) (V := V) (h := h) hD)
  have hh : (Nat.card (CanonicalPairProfile (K := K) (V := V) r h):ℝ) ≤
      Nat.card (Σ p : PairParameters r h, Σ R : SubspacePairProfile (K := K) (V := Module.Dual K V) r p.val.val,
        DualPairLiftEvent R (h-p.val.val)) := by exact_mod_cast hc
  refine (div_le_div_of_nonneg_right hh (by positivity)).trans ?_
  rw [Nat.card_sigma,Nat.cast_sum,Finset.sum_div]
  exact Finset.sum_le_sum (fun p _ => pairPlanted_bound_one r h hD p)
 theorem canonical_center_pair_gain_bound (r h : ℕ) (hD : finrank K V=2*r) :
    (Fintype.card K:ℝ)^((h+1).choose 2) *
      ((Nat.card (CenterPairProfile (K := K) (V := V) r h):ℝ) /
        (Nat.card (CenterStratum (K := K) (V := V) r):ℝ)^2) ≤
      (Nat.card (PairParameters r h):ℝ)*2^(2*r+h)*(Fintype.card K:ℝ)^((h/2+1).choose 2) := by
  have hq : (1:ℝ) ≤ Fintype.card K := by exact_mod_cast Fintype.card_pos (α := K)
  have hqpos : (0:ℝ) < Fintype.card K := by positivity
  have hh := canonical_center_pair_probability_bound (K := K) (V := V) r h hD
  refine (mul_le_mul_of_nonneg_left hh (by positivity)).trans ?_
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑ _p : PairParameters r h, 2^(2*r+h)*(Fintype.card K:ℝ)^((h/2+1).choose 2) := by
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
  {Y : SymplecticLagrangian ω // finrank K ↥(L ⊓ Y.val)=r ∧ finrank K ↥(M ⊓ Y.val)=r}
abbrev SymplecticCenterPairProfile (Y : SymplecticLagrangian ω) (r h : ℕ) :=
  {L : SymplecticCenterStratum ω Y r × SymplecticCenterStratum ω Y r //
    finrank K ↥(L.1.val.val ⊓ L.2.val.val)=h}
noncomputable def symplecticCenterPairProfileEquiv {V : Type*} [AddCommGroup V] [Module K V]
    (Y : SymplecticLagrangian ω) (e : (V × Module.Dual K V) ≃ₗ[K] E)
    (he : ∀ x y, ω (e x) (e y)=canonicalSymplectic x y)
    (hY : (verticalSpace (K := K) (V := V)).map e.toLinearMap=Y.val) (r h : ℕ) :
    CenterPairProfile (K := K) (V := V) r h ≃ SymplecticCenterPairProfile ω Y r h :=
  let f := symplecticCenterStratumEquiv ω Y e he hY r
  (f.prodCongr f).subtypeEquiv (by
    intro L
    change _ ↔ finrank K ↥(L.1.val.val.map e.toLinearMap ⊓ L.2.val.val.map e.toLinearMap)=h
    rw [map_pair_finrank])
noncomputable def pairCenterIsometryEquiv (r : ℕ) (L M : Submodule K E)
    (e : E ≃ₗ[K] E) (he : ∀ x y, ω (e x) (e y)=ω x y) :
    PairCenterSet ω r L M ≃ PairCenterSet ω r (L.map e.toLinearMap) (M.map e.toLinearMap) :=
  (lagrangianIsometryEquiv ω e he).subtypeEquiv (by
    intro Y
    change (_ ∧ _) ↔ (finrank K ↥(L.map e.toLinearMap ⊓ Y.val.map e.toLinearMap)=r ∧
      finrank K ↥(M.map e.toLinearMap ⊓ Y.val.map e.toLinearMap)=r)
    rw [map_pair_finrank,map_pair_finrank])
noncomputable def pairCenterProfileEquiv (r h : ℕ) :
    (Σ p : OrderedPairDim ω h, PairCenterSet ω r p.val.1.val p.val.2.val) ≃
      Σ Y : SymplecticLagrangian ω, SymplecticCenterPairProfile ω Y r h where
  toFun P := ⟨P.2.val,⟨(⟨P.1.val.1,P.2.property.1⟩,⟨P.1.val.2,P.2.property.2⟩),P.1.property⟩⟩
  invFun P := ⟨⟨(P.2.val.1.val,P.2.val.2.val),P.2.property⟩,
    ⟨P.1,P.2.val.1.property,P.2.val.2.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
variable [Fintype K] [Finite E]
 omit [Fintype K] in
 theorem pairCenter_profile_card (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (r : ℕ) (L M : SymplecticLagrangian ω) :
    Nat.card (Σ Y : SymplecticLagrangian ω,
      SymplecticCenterPairProfile ω Y r (finrank K ↥(L.val ⊓ M.val))) =
    Nat.card (OrderedPairDim ω (finrank K ↥(L.val ⊓ M.val))) * Nat.card (PairCenterSet ω r L.val M.val) := by
  classical
  let := Fintype.ofFinite (OrderedPairDim ω (finrank K ↥(L.val ⊓ M.val)))
  rw [←Nat.card_congr (pairCenterProfileEquiv ω r (finrank K ↥(L.val ⊓ M.val))),Nat.card_sigma]
  have hc (p : OrderedPairDim ω (finrank K ↥(L.val ⊓ M.val))) :
      Nat.card (PairCenterSet ω r p.val.1.val p.val.2.val)=Nat.card (PairCenterSet ω r L.val M.val) := by
    obtain ⟨e,he,hL,hM⟩ := ordered_pair_transitivity ω h2 ha hω
      p.val.1.val p.val.2.val L.val M.val p.val.1.property p.val.2.property L.property M.property p.property
    have hh := Nat.card_congr (pairCenterIsometryEquiv ω r p.val.1.val p.val.2.val e he)
    rwa [hL,hM] at hh
  simp only [hc,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card,Nat.cast_id]
 omit [Fintype K] in
 theorem symplectic_center_stratum_card_eq (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (A B : SymplecticLagrangian ω) (r : ℕ) :
    Nat.card (SymplecticCenterStratum ω A r)=Nat.card (SymplecticCenterStratum ω B r) := by
  obtain ⟨e,he,hA⟩ := lagrangian_transitivity ω A.val h2 ha hω A.property B.val B.property
  exact Nat.card_congr ((lagrangianIsometryEquiv ω e he).subtypeEquiv (by
    intro L
    change _ ↔ finrank K ↥(L.val.map e.toLinearMap ⊓ B.val)=r
    rw [←hA,map_pair_finrank]))
 theorem symplectic_center_pair_gain_bound (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (r : ℕ) (hD : finrank K E=2*(2*r)) (Y : SymplecticLagrangian ω) (h : ℕ) :
    (Fintype.card K:ℝ)^((h+1).choose 2)*
      ((Nat.card (SymplecticCenterPairProfile ω Y r h):ℝ)/
        (Nat.card (SymplecticCenterStratum ω Y r):ℝ)^2) ≤
      (Nat.card (PairParameters r h):ℝ)*2^(2*r+h)*(Fintype.card K:ℝ)^((h/2+1).choose 2) := by
  obtain ⟨e,he,hY⟩ := exists_center_coordinates ω h2 ha hω Y
  rw [←Nat.card_congr (symplecticCenterPairProfileEquiv ω Y e he hY r h),
    ←Nat.card_congr (symplecticCenterStratumEquiv ω Y e he hY r)]
  have hd := self_orthogonal_twice_finrank ω Y.val hω Y.property
  exact canonical_center_pair_gain_bound r h (by omega)
noncomputable def pairFaceDensity (r : ℕ) (A L M : SymplecticLagrangian ω) : ℝ :=
  (Nat.card (PairCenterSet ω r L.val M.val):ℝ)*(Nat.card (SymplecticLagrangian ω):ℝ) /
    (Nat.card (SymplecticCenterStratum ω A r):ℝ)^2
 omit [Fintype K] [Finite E] in
 theorem pairFaceDensity_nonneg (r : ℕ) (A L M : SymplecticLagrangian ω) :
    0 ≤ pairFaceDensity ω r A L M := by unfold pairFaceDensity; positivity
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
    (r : ℕ) (hD : 2*(2*r)=finrank K E) (A L M : SymplecticLagrangian ω) :
    pairFaceDensity ω r A L M ≤
      (lagrangianConstant (2*r))^2 *
        ((Nat.card (PairParameters r (finrank K ↥(L.val ⊓ M.val))):ℝ)*
          2^(2*r+finrank K ↥(L.val ⊓ M.val))*
          (Fintype.card K:ℝ)^((finrank K ↥(L.val ⊓ M.val)/2+1).choose 2)) := by
  classical
  let := Fintype.ofFinite (SymplecticLagrangian ω)
  let h := finrank K ↥(L.val ⊓ M.val)
  let q : ℝ := Fintype.card K
  let a : ℝ := Nat.card (SymplecticCenterStratum ω A r)
  let b : ℝ := (Nat.card (PairParameters r h):ℝ)*2^(2*r+h)*q^((h/2+1).choose 2)
  have hdim := self_orthogonal_twice_finrank ω L.val hω L.property
  have hh : h≤2*r := by have hb := Submodule.finrank_mono (show L.val ⊓ M.val ≤ L.val from inf_le_left); dsimp [h]; omega
  have ha0 : 0<a := symplectic_center_stratum_card_pos ω h2 ha hω (2*r) hD A r (by omega)
  have hq : 0<q := by dsimp [q]; exact_mod_cast Fintype.card_pos (α := K)
  have hLag := symplecticLagrangian_card_bounds ω h2 ha hω (2*r) hD
  have hL : (0:ℝ)<Nat.card (SymplecticLagrangian ω) := (pow_pos hq _).trans_le hLag.1
  have hMass : (Nat.card (SymplecticLagrangian ω):ℝ)^2 ≤
      (lagrangianConstant (2*r))^2*(q^((h+1).choose 2)*Nat.card (OrderedPairDim ω h)) := by
    calc
      _ ≤ (lagrangianConstant (2*r)*q^((2*r+1).choose 2))^2 := pow_le_pow_left₀ (by positivity) hLag.2 2
      _ = (lagrangianConstant (2*r))^2*q^(2*((2*r+1).choose 2)) := by rw [mul_pow,←pow_mul,Nat.mul_comm _ 2]
      _ ≤ _ := mul_le_mul_of_nonneg_left (orderedPairDim_card_lower ω h2 ha hω (2*r) hD h hh) (by positivity)
  have hg (Y : SymplecticLagrangian ω) :
      q^((h+1).choose 2)*(Nat.card (SymplecticCenterPairProfile ω Y r h):ℝ) ≤ a^2*b := by
    have hc := symplectic_center_pair_gain_bound ω h2 ha hω r hD.symm Y h
    rw [←symplectic_center_stratum_card_eq ω h2 ha hω A Y r,←mul_div_assoc] at hc
    exact (div_le_iff₀ (sq_pos_of_pos ha0)).mp hc |>.trans_eq (mul_comm _ _)
  have hGain : q^((h+1).choose 2)*(Nat.card (OrderedPairDim ω h):ℝ)*Nat.card (PairCenterSet ω r L.val M.val) ≤
      (Nat.card (SymplecticLagrangian ω):ℝ)*a^2*b := by
    rw [mul_assoc,←Nat.cast_mul,←pairCenter_profile_card ω h2 ha hω r L M,Nat.card_sigma,Nat.cast_sum,Finset.mul_sum]
    calc
      _ ≤ ∑ _Y : SymplecticLagrangian ω, a^2*b := Finset.sum_le_sum (fun Y _ => hg Y)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card]; ring
  exact normalized_pair_gain _ _ _ _ _ _ _ hL ha0 (by positivity) (by positivity) hMass hGain
end PairPointwise
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ExposureProfile
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E)
def LocalProfile (c u v w : ℕ) (L M N : SymplecticLagrangian ω) : Prop :=
  finrank K ↥((L.val ⊓ M.val) ⊓ N.val)=c ∧ finrank K ↥(L.val ⊓ M.val)=u ∧
  finrank K ↥(L.val ⊓ N.val)=v ∧ finrank K ↥(M.val ⊓ N.val)=w
end ExposureProfile
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
abbrev FullTailChoice (D r c : ℕ) (s : Fin 3 → ℕ) :=
  Σ u : CommonParameters D r c, BaseParameters (D-c) (r-u.val.val) (s 0) (s 1) (s 2)
noncomputable def fullTailConstant (D r c : ℕ) (s : Fin 3 → ℕ)
    (x : FullTailChoice D r c s) : ℝ :=
  (orbitMassConstant D*(lagrangianConstant D)^2)*(lagrangianConstant D*2^c)*
    ((2^x.1.val.val*lagrangianConstant (D-x.1.val.val))*2^(3*(D-c)))*
    reducedPlantedConstant (r-x.1.val.val) (s 0) (s 1) (s 2) x.2.val
 theorem fullTailConstant_nonneg (D r c : ℕ) (s : Fin 3 → ℕ) (x : FullTailChoice D r c s) :
    0 ≤ fullTailConstant D r c s x := by
  have h₀ := (orbitMassConstant_pos D).le
  have h₁ := (lagrangianConstant_pos D).le
  have h₂ := (lagrangianConstant_pos (D-x.1.val.val)).le
  unfold fullTailConstant reducedPlantedConstant
  positivity
noncomputable def fullTailMajorant (D r c : ℕ) (s : Fin 3 → ℕ) (q : ℝ) : ℝ :=
  ∑ x : FullTailChoice D r c s,
    fullTailConstant D r c s x * q^(tailGain D true (plantedTailTuple D r c s x.1 x.2))
 theorem fullTailMajorant_nonneg (D r c : ℕ) (s : Fin 3 → ℕ) (q : ℝ) (hq : 0≤q) :
    0 ≤ fullTailMajorant D r c s q := by
  apply Finset.sum_nonneg
  intro x _
  exact mul_nonneg (fullTailConstant_nonneg _ _ _ _ _) (Real.rpow_nonneg hq _)
 theorem fullTailMajorant_eq (D r c : ℕ) (s : Fin 3 → ℕ) (q : ℝ)
    (hD : D=2*r) (hc : c≤D) (hq : 0<q) :
    fullTailMajorant D r c s q =
      (orbitMassConstant D*(lagrangianConstant D)^2)*
      q^(((D:ℝ)+1)*c+(∑ i,triangular (s i))+3*triangular r-4*triangular D)*
      ((lagrangianConstant D*2^c)*q^(isotropicExponent D c)*
        ∑ u : CommonParameters D r c,
          ((2^u.val.val*lagrangianConstant (D-u.val.val))*2^(3*(D-c)))*
          q^((u.val.val:ℝ)*(c-u.val.val:ℕ)+triangular (D-u.val.val:ℕ)+
            3*triangular (D-c:ℕ)-3*triangular (r-u.val.val:ℕ))*
          reducedPlantedSum (D-c) (r-u.val.val) (s 0) (s 1) (s 2) q) := by
  classical
  unfold fullTailMajorant
  rw [Fintype.sum_sigma]
  simp_rw [←fullPlantedExponent_eq D c r hD hc s,fullPlantedExponent,Real.rpow_add hq,
    Real.rpow_sub hq,reducedPlantedSum,Finset.mul_sum]
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
    (hq : 4*lagrangianConstant D≤(Fintype.card K:ℝ)) (A L M N : SymplecticLagrangian ω) :
    let c := finrank K ↥((L.val⊓M.val)⊓N.val)
    let s : Fin 3 → ℕ := ![finrank K ↥(L.val⊓M.val)-c,finrank K ↥(L.val⊓N.val)-c,
      finrank K ↥(M.val⊓N.val)-c]
    tripleFaceDensity ω r A L M N ≤ fullTailMajorant D r c s (Fintype.card K) := by
  dsimp only
  have hc : finrank K ↥((L.val⊓M.val)⊓N.val)≤D :=
    isotropic_finrank_le_half ω hω D hD _ (by intro x hx y hy; exact L.property.ge hx.1.1 y hy.1.1)
  have hq0 : (0:ℝ)<Fintype.card K := by exact_mod_cast Fintype.card_pos (α:=K)
  rw [fullTailMajorant_eq _ _ _ _ _ hr hc hq0]
  have hh := tripleFaceDensity_full_bound ω h2 ha hω D hD hq r (by omega) A L M N
  dsimp only at hh
  refine hh.trans_eq ?_
  simp only [tripleDefect,commonPlantedTerm,Fin.sum_univ_three,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,
    Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat,triangular_nat]
end Actual
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
def lowerTailTuple (c : ℕ) (s : Fin 3 → ℕ) : TailTuple := ⟨c,0,0,s,fun _=>0⟩
 theorem lowerTailTuple_s (c : ℕ) (s : Fin 3 → ℕ) (i : Fin 3) :
    (lowerTailTuple c s).s i=s i := Nat.add_zero _
 theorem lowerTailTuple_feasible (D c : ℕ) (s : Fin 3 → ℕ) (hc : c≤D) (hs : (∑ i,s i)≤D-c) :
    TailFeasible D false (lowerTailTuple c s) := by
  refine ⟨hc,?_,by simp⟩
  change (∑ i,s i+0)≤D-c
  simpa only [Nat.add_zero] using hs
noncomputable def lowerTailConstant (D r : ℕ) : ℝ :=
  max 1 ((lagrangianConstant D)^2*(r+1)*2^(2*D))
 theorem lowerTailConstant_pos (D r : ℕ) : 0<lowerTailConstant D r :=
  lt_of_lt_of_le zero_lt_one (le_max_left _ _)
 theorem pairParameters_card_le (r h : ℕ) : Nat.card (PairParameters r h)≤r+1 := by
  exact (Nat.card_le_card_of_injective _ Subtype.val_injective).trans_eq (Nat.card_fin _)
section PairBound
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
 theorem pairFaceDensity_lower_tail (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D r : ℕ) (hD : 2*D=finrank K E) (hr : D=2*r) (c : ℕ) (s : Fin 3 → ℕ)
    (A L M : SymplecticLagrangian ω) (i : Fin 3)
    (hh : finrank K ↥(L.val⊓M.val)=c+s i) :
    pairFaceDensity ω r A L M≤lowerTailConstant D r*
      (Fintype.card K:ℝ)^(tailGain D false (lowerTailTuple c s)) := by
  have hq : (1:ℝ)≤Fintype.card K := by exact_mod_cast Fintype.card_pos (α:=K)
  have hb := pairFaceDensity_gain_bound ω h2 ha hω r (hr ▸ hD) A L M
  rw [←hr] at hb
  have hd : finrank K ↥(L.val⊓M.val)≤D :=
    isotropic_finrank_le_half ω hω D hD _ (by intro x hx y hy; exact L.property.ge hx.1 y hy.1)
  have hcard : (Nat.card (PairParameters r (finrank K ↥(L.val⊓M.val))):ℝ)≤r+1 := by
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
    _ ≤ ((lagrangianConstant D)^2*((r:ℝ)+1)*2^(2*D))*
        (Fintype.card K:ℝ)^(tailGain D false (lowerTailTuple c s)) := by
      have hs := mul_le_mul (mul_le_mul hcard hpow (by positivity) (by positivity)) hp (by positivity)
        (mul_nonneg (by positivity) (by positivity))
      have hi := mul_le_mul_of_nonneg_left hs (sq_nonneg (lagrangianConstant D))
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
| true,x => plantedTailTuple D r c s x.1 x.2
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
    TailFeasible D b (faceTailTuple D r c s b x) := by
  cases b
  · exact lowerTailTuple_feasible D c s hc hs
  · exact plantedTailTuple_feasible D r c hr hc s hs x.1 x.2
noncomputable def faceTailMajorant (D r c : ℕ) (s : Fin 3 → ℕ) (b : Bool) (q : ℝ) : ℝ :=
  ∑ x : FaceTailChoice D r c s b,
    faceTailConstant D r c s b x*q^(tailGain D b (faceTailTuple D r c s b x))
 theorem faceTailMajorant_true (D r c : ℕ) (s : Fin 3 → ℕ) (q : ℝ) :
    faceTailMajorant D r c s true q=fullTailMajorant D r c s q := rfl
 theorem faceTailMajorant_false (D r c : ℕ) (s : Fin 3 → ℕ) (q : ℝ) :
    faceTailMajorant D r c s false q=lowerTailConstant D r*q^(tailGain D false (lowerTailTuple c s)) := by
  let : Unique (FaceTailChoice D r c s false) := inferInstanceAs (Unique Unit)
  rw [faceTailMajorant,Fintype.sum_unique]
  rfl
 theorem faceTailMajorant_nonneg (D r c : ℕ) (s : Fin 3 → ℕ) (b : Bool) (q : ℝ) (hq : 0≤q) :
    0≤faceTailMajorant D r c s b q := by
  apply Finset.sum_nonneg
  intro x _
  exact mul_nonneg (faceTailConstant_pos _ _ _ _ _ _) (Real.rpow_nonneg hq _)
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
 omit [Fintype K] in
 theorem lagrangian_card_pos (A : SymplecticLagrangian ω) :
    (0:ℝ)<Nat.card (SymplecticLagrangian ω) := by
  let : Nonempty (SymplecticLagrangian ω) := ⟨A⟩
  exact_mod_cast Nat.card_pos
 omit [Fintype K] in
 theorem activeFaceDensity_empty (r : ℕ) (A : SymplecticLagrangian ω)
    (L : Fin 3 → SymplecticLagrangian ω) : activeFaceDensity ω r A L ∅=1 := by
  have hc : Nat.card (ActiveCenterSet ω r L ∅)=Nat.card (SymplecticLagrangian ω) :=
    Nat.card_congr (Equiv.subtypeUnivEquiv (by simp))
  simp only [activeFaceDensity,hc,Finset.card_empty,pow_zero,mul_one]
  exact div_self (lagrangian_card_pos ω A).ne'
 theorem activeFaceDensity_singleton (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D r : ℕ) (hD : 2*D=finrank K E) (hr : r ≤ D) (A : SymplecticLagrangian ω)
    (L : Fin 3 → SymplecticLagrangian ω) (i : Fin 3) : activeFaceDensity ω r A L {i}=1 := by
  classical
  have hc : Nat.card (ActiveCenterSet ω r L {i})=Nat.card (SymplecticCenterStratum ω (L i) r) :=
    Nat.card_congr (Equiv.subtypeEquivRight (by
      intro Y
      simp only [Finset.mem_singleton,forall_eq]
      rw [inf_comm]))
  rw [symplectic_center_stratum_card_eq ω h2 ha hω (L i) A r] at hc
  simp only [activeFaceDensity,hc,Finset.card_singleton,pow_one]
  have hL := (lagrangian_card_pos ω A).ne'
  have hA := (symplectic_center_stratum_card_pos ω h2 ha hω D hD A r hr).ne'
  field_simp
 omit [Fintype K] in
 theorem activeFaceDensity_pair (r : ℕ) (A : SymplecticLagrangian ω)
    (L : Fin 3 → SymplecticLagrangian ω) (i k : Fin 3) (hik : i≠k) :
    activeFaceDensity ω r A L {i,k}=pairFaceDensity ω r A (L i) (L k) := by
  classical
  have hc : Nat.card (ActiveCenterSet ω r L {i,k})=Nat.card (PairCenterSet ω r (L i).val (L k).val) :=
    Nat.card_congr (Equiv.subtypeEquivRight (by intro Y; simp))
  simp only [activeFaceDensity,hc,Finset.card_pair hik,pairFaceDensity]
  have hL := (lagrangian_card_pos ω A).ne'
  field_simp
 omit [Fintype K] in
 theorem activeFaceDensity_full (r : ℕ) (A : SymplecticLagrangian ω)
    (L : Fin 3 → SymplecticLagrangian ω) :
    activeFaceDensity ω r A L Finset.univ=tripleFaceDensity ω r A (L 0) (L 1) (L 2) := by
  classical
  have hc : Nat.card (ActiveCenterSet ω r L Finset.univ)=Nat.card (TripleCenterSet ω r (L 0).val (L 1).val (L 2).val) :=
    Nat.card_congr (Equiv.subtypeEquivRight (by intro Y; simp [Fin.forall_fin_succ]))
  simp only [activeFaceDensity,hc,Finset.card_univ,Fintype.card_fin,tripleFaceDensity]
  have hL := (lagrangian_card_pos ω A).ne'
  field_simp
 theorem one_le_lowerTailMajorant (D r c : ℕ) (s : Fin 3 → ℕ) (q : ℝ) (hq : 1 ≤ q) :
    1 ≤ faceTailMajorant D r c s false q := by
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
    (A : SymplecticLagrangian ω) (L : Fin 3 → SymplecticLagrangian ω)
    (hL : LocalProfile ω c (c+s 0) (c+s 1) (c+s 2) (L 0) (L 1) (L 2))
    (T : Finset (Fin 3)) (hT : T≠Finset.univ) :
    activeFaceDensity ω r A L T ≤ faceTailMajorant D r c s false (Fintype.card K) := by
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
    (hq : 4*lagrangianConstant D ≤ (Fintype.card K:ℝ))
    (A : SymplecticLagrangian ω) (L : Fin 3 → SymplecticLagrangian ω)
    (hL : LocalProfile ω c (c+s 0) (c+s 1) (c+s 2) (L 0) (L 1) (L 2))
    (T : Finset (Fin 3)) :
    activeFaceDensity ω r A L T ≤ faceTailMajorant D r c s (decide (T=Finset.univ)) (Fintype.card K) := by
  classical
  by_cases ht : T=Finset.univ
  · simp only [ht,decide_true,faceTailMajorant_true,activeFaceDensity_full]
    have hb := tripleFaceDensity_tail_bound ω h2 ha hω D r hD hr hq A (L 0) (L 1) (L 2)
    dsimp only at hb
    rw [hL.1,hL.2.1,hL.2.2.1,hL.2.2.2] at hb
    have hs : ![c+s 0-c,c+s 1-c,c+s 2-c]=s := by funext i; fin_cases i <;> simp
    rwa [hs] at hb
  · simp only [ht,decide_false]
    exact activeFaceDensity_lower_bound ω h2 ha hω D r hD hr c s A L hL T ht
end ActiveFaceBound
end SidorenkoCounterexample
end OAI
open Module Filter

def TargetH3 : Prop :=
 let tri (x : ℝ) := x*(x+1)/2
 let nc (A : Type) := (Nat.card A : ℝ)
 let Q := {q : ℕ // q.Prime ∧ q ≠ 2}
 let V D (q : Q) := Fin D → ZMod q.1
 let E D q := V D q × Dual (ZMod q.1) (V D q)
 let rk {D} {q : Q} (U : Submodule (ZMod q.1) (E D q)) := finrank (ZMod q.1) U
 let Lag D (q : Q) := {L : Submodule (ZMod q.1) (E D q) // ∀ w, (∀ x ∈ L, w.2 x.1 - x.2 w.1 = 0) ↔ w ∈ L}
 let afD D r (q : Q) (L : Fin 3 → Lag D q) (T : Finset (Fin 3)) :=
  nc {Y : Lag D q // ∀ i ∈ T, rk ((L i).1 ⊓ Y.1) = r} / nc (Lag D q) *
   (nc (Lag D q) / nc {M : Lag D q // rk (M.1 ⊓ LinearMap.ker (.fst _ _ _)) = r})^T.card
 let pGain (D c u v : ℕ) (b : Bool) (pv tv : Fin 3 → ℕ) :=
  let δ : ℝ := 2*(u : ℝ)-c; let d : ℝ := (D : ℝ)-c; let P : ℝ := ∑ i, (pv i : ℝ)
  if b then ((d+c)/2+c+1)*((c+δ)/2) - 2*((c+δ)/2)^2 + (∑ i, tri ((pv i : ℝ)+tv i)) -
   δ*P - (∑ i, (pv i : ℝ)^2) - (v : ℝ)*((d-3*δ)/2-P+v) - (∑ i, tri (tv i)) + tri v
  else tri (((Finset.univ.sup fun i => c+(pv i+tv i))/2 : ℕ) : ℝ)
 let feas (D c u v : ℕ) (b : Bool) (pv tv : Fin 3 → ℕ) :=
  let δ : ℝ := 2*(u : ℝ)-c
  c ≤ D ∧ (∑ i, (pv i+tv i)) ≤ D-c ∧ (b = true → u ≤ c ∧ (∀ i, (tv i : ℝ) ≤ pv i+δ) ∧
   (∀ i, (v : ℝ) ≤ pv i+δ) ∧ 0 ≤ ((D : ℝ)-c-3*δ)/2-(∑ i, (pv i : ℝ))+v)
 ∀ (r c : ℕ) (s : Fin 3 → ℕ) b, c ≤ 2*r → (∑ i, s i) ≤ 2*r-c →
  ∃ (Q₀ m : ℕ) (w : Fin m → ℝ) (u v : Fin m → ℕ) (pv tv : Fin m → Fin 3 → ℕ),
   (∀ l, 0 ≤ w l) ∧ (∀ l, feas (2*r) c (u l) (v l) b (pv l) (tv l)) ∧ (∀ l k, pv l k+tv l k = s k) ∧
   ∀ q, Q₀ ≤ q.1 → ∀ L T, decide (T = .univ) = b →
    rk (((L 0).1 ⊓ (L 1).1) ⊓ (L 2).1) = c → rk ((L 0).1 ⊓ (L 1).1) = c+s 0 →
    rk ((L 0).1 ⊓ (L 2).1) = c+s 1 → rk ((L 1).1 ⊓ (L 2).1) = c+s 2 →
    afD (2*r) r q L T ≤ ∑ l, w l * (q.1 : ℝ)^pGain (2*r) c (u l) (v l) b (pv l) (tv l)

theorem leaf3_proved : TargetH3 := by
  intro r c s b hc hs
  let D := 2 * r
  let Choice := OAI.SidorenkoCounterexample.FaceTailChoice D r c s b
  let m := Fintype.card Choice
  let e : Fin m ≃ Choice := (Fintype.equivFin Choice).symm
  let Q₀ := Nat.ceil (4 * OAI.SidorenkoCounterexample.lagrangianConstant D)
  refine ⟨Q₀, m,
    fun l => OAI.SidorenkoCounterexample.faceTailConstant D r c s b (e l),
    fun l => (OAI.SidorenkoCounterexample.faceTailTuple D r c s b (e l)).u,
    fun l => (OAI.SidorenkoCounterexample.faceTailTuple D r c s b (e l)).v,
    fun l => (OAI.SidorenkoCounterexample.faceTailTuple D r c s b (e l)).p,
    fun l => (OAI.SidorenkoCounterexample.faceTailTuple D r c s b (e l)).t,
    ?_, ?_, ?_, ?_⟩
  · intro l
    exact OAI.SidorenkoCounterexample.faceTailConstant_pos D r c s b (e l)
  · intro l
    have hf := OAI.SidorenkoCounterexample.faceTailTuple_feasible D r c s rfl hc hs b (e l)
    have htc := OAI.SidorenkoCounterexample.faceTailTuple_c D r c s b (e l)
    simpa only [OAI.SidorenkoCounterexample.TailFeasible, OAI.SidorenkoCounterexample.TailTuple.s,
      OAI.SidorenkoCounterexample.TailTuple.delta, OAI.SidorenkoCounterexample.TailTuple.P, htc] using hf
  · intro l k
    exact OAI.SidorenkoCounterexample.faceTailTuple_s D r c s b (e l) k
  · intro q hq₀ L T hb hc0 h01 h02 h12
    let : Fact q.1.Prime := ⟨q.2.1⟩
    have h2 : (2 : ZMod q.1) ≠ 0 :=
      Ring.two_ne_zero (by simpa only [ZMod.ringChar_zmod_n] using q.2.2)
    let : Invertible (2 : ZMod q.1) := invertibleOfNonzero h2
    let : Finite (Dual (ZMod q.1) (Fin D → ZMod q.1)) := Module.finite_of_finite (ZMod q.1)
    have hD : 2 * D = finrank (ZMod q.1) ((Fin D → ZMod q.1) × Dual (ZMod q.1) (Fin D → ZMod q.1)) := by
      rw [Module.finrank_prod, Subspace.dual_finrank_eq, Module.finrank_pi, Fintype.card_fin]
      ring
    have hq : 4 * OAI.SidorenkoCounterexample.lagrangianConstant D ≤ (Fintype.card (ZMod q.1) : ℝ) := by
      rw [ZMod.card]
      exact (Nat.le_ceil _).trans (Nat.cast_le.mpr hq₀)
    let ω := OAI.SidorenkoCounterexample.canonicalSymplectic (K := ZMod q.1) (V := Fin D → ZMod q.1)
    let eLag : OAI.SidorenkoCounterexample.SymplecticLagrangian ω ≃
        {M : Submodule (ZMod q.1) ((Fin D → ZMod q.1) × Dual (ZMod q.1) (Fin D → ZMod q.1)) //
          ∀ w, (∀ x ∈ M, w.2 x.1 - x.2 w.1 = 0) ↔ w ∈ M} :=
      Equiv.subtypeEquivRight (fun M => by
        simp only [SetLike.ext_iff, LinearMap.BilinForm.mem_orthogonal_iff, ω,
          OAI.SidorenkoCounterexample.canonicalSymplectic_apply])
    have hc1 : Nat.card {Y : {M : Submodule (ZMod q.1) ((Fin D → ZMod q.1) × Dual (ZMod q.1) (Fin D → ZMod q.1)) //
          ∀ w, (∀ x ∈ M, w.2 x.1 - x.2 w.1 = 0) ↔ w ∈ M} //
          ∀ i ∈ T, finrank (ZMod q.1) ↥((L i).1 ⊓ Y.1) = r} =
        Nat.card (OAI.SidorenkoCounterexample.ActiveCenterSet ω r (eLag.symm ∘ L) T) :=
      Nat.card_congr (Equiv.subtypeEquiv eLag.symm (fun Y => Iff.rfl))
    have hc2 : Nat.card {M : Submodule (ZMod q.1) ((Fin D → ZMod q.1) × Dual (ZMod q.1) (Fin D → ZMod q.1)) //
          ∀ w, (∀ x ∈ M, w.2 x.1 - x.2 w.1 = 0) ↔ w ∈ M} =
        Nat.card (OAI.SidorenkoCounterexample.SymplecticLagrangian ω) :=
      Nat.card_congr eLag.symm
    have hc3 : Nat.card {M : {M : Submodule (ZMod q.1) ((Fin D → ZMod q.1) × Dual (ZMod q.1) (Fin D → ZMod q.1)) //
          ∀ w, (∀ x ∈ M, w.2 x.1 - x.2 w.1 = 0) ↔ w ∈ M} //
          finrank (ZMod q.1) ↥(M.1 ⊓ LinearMap.ker (.fst _ _ _)) = r} =
        Nat.card (OAI.SidorenkoCounterexample.SymplecticCenterStratum ω
          (OAI.SidorenkoCounterexample.verticalLagrangian (K := ZMod q.1) (V := Fin D → ZMod q.1)) r) :=
      Nat.card_congr (Equiv.subtypeEquiv eLag.symm (fun M => Iff.rfl))
    have haf :
        (Nat.card {Y : {M : Submodule (ZMod q.1) ((Fin D → ZMod q.1) × Dual (ZMod q.1) (Fin D → ZMod q.1)) //
            ∀ w, (∀ x ∈ M, w.2 x.1 - x.2 w.1 = 0) ↔ w ∈ M} //
            ∀ i ∈ T, finrank (ZMod q.1) ↥((L i).1 ⊓ Y.1) = r} : ℝ) /
          (Nat.card {M : Submodule (ZMod q.1) ((Fin D → ZMod q.1) × Dual (ZMod q.1) (Fin D → ZMod q.1)) //
            ∀ w, (∀ x ∈ M, w.2 x.1 - x.2 w.1 = 0) ↔ w ∈ M} : ℝ) *
          ((Nat.card {M : Submodule (ZMod q.1) ((Fin D → ZMod q.1) × Dual (ZMod q.1) (Fin D → ZMod q.1)) //
            ∀ w, (∀ x ∈ M, w.2 x.1 - x.2 w.1 = 0) ↔ w ∈ M} : ℝ) /
          (Nat.card {M : {M : Submodule (ZMod q.1) ((Fin D → ZMod q.1) × Dual (ZMod q.1) (Fin D → ZMod q.1)) //
            ∀ w, (∀ x ∈ M, w.2 x.1 - x.2 w.1 = 0) ↔ w ∈ M} //
            finrank (ZMod q.1) ↥(M.1 ⊓ LinearMap.ker (.fst _ _ _)) = r} : ℝ)) ^ T.card =
        OAI.SidorenkoCounterexample.activeFaceDensity ω r
          (OAI.SidorenkoCounterexample.verticalLagrangian (K := ZMod q.1) (V := Fin D → ZMod q.1))
          (eLag.symm ∘ L) T := by
      dsimp only [OAI.SidorenkoCounterexample.activeFaceDensity]
      rw [hc1, hc2, hc3]
    have hbound := OAI.SidorenkoCounterexample.activeFaceDensity_tail_bound ω h2
      OAI.SidorenkoCounterexample.canonicalSymplectic_alt
      OAI.SidorenkoCounterexample.canonicalSymplectic_nondegenerate
      D r hD rfl c s hq
      (OAI.SidorenkoCounterexample.verticalLagrangian (K := ZMod q.1) (V := Fin D → ZMod q.1))
      (eLag.symm ∘ L) ⟨hc0, h01, h02, h12⟩ T
    dsimp only
    rw [haf]
    refine hbound.trans_eq ?_
    rw [hb, ZMod.card]
    unfold OAI.SidorenkoCounterexample.faceTailMajorant
    rw [← Equiv.sum_comp e]
    apply Finset.sum_congr rfl
    intro l _
    have htc := OAI.SidorenkoCounterexample.faceTailTuple_c D r c s b (e l)
    cases b
    · have hh : (OAI.SidorenkoCounterexample.faceTailTuple D r c s false (e l)).h =
          fun i => c + ((OAI.SidorenkoCounterexample.faceTailTuple D r c s false (e l)).p i +
            (OAI.SidorenkoCounterexample.faceTailTuple D r c s false (e l)).t i) := by
        funext i
        simp only [OAI.SidorenkoCounterexample.TailTuple.h, OAI.SidorenkoCounterexample.TailTuple.s, htc]
      dsimp only [OAI.SidorenkoCounterexample.tailGain, OAI.SidorenkoCounterexample.triangular,
        OAI.SidorenkoCounterexample.TailTuple.maxH]
      simp only [Bool.false_eq_true, reduceIte, hh]
    · simp only [D, OAI.SidorenkoCounterexample.tailGain, OAI.SidorenkoCounterexample.plantedGain,
        OAI.SidorenkoCounterexample.triangular, OAI.SidorenkoCounterexample.TailTuple.delta,
        htc, reduceIte]

theorem OMA.solution : OMA.R_SidorenkoConjecture_sidorenko_conjecture_graphon_R1_H1_R1_H1_R1_H1_R2.H3 := leaf3_proved
