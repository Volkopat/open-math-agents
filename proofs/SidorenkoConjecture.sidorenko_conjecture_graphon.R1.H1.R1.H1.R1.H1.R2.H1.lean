import OMAReductions.R_SidorenkoConjecture_sidorenko_conjecture_graphon_R1_H1_R1_H1_R1_H1_R2
import Mathlib
/-! Adapted under Apache-2.0 from openai/math Sidorenko formalization. -/

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

noncomputable def homCount {V W : Type*} (F : SimpleGraph V) (G : SimpleGraph W) : ℕ :=
  Nat.card {f : V → W // ∀ u v, F.Adj u v → G.Adj (f u) (f v)}

noncomputable def homDensity {V W : Type*} (F : SimpleGraph V) (G : SimpleGraph W) : ℝ :=
  (homCount F G : ℝ) / (Nat.card W : ℝ) ^ Nat.card V

noncomputable def edgeDensity {W : Type*} (G : SimpleGraph W) : ℝ :=
  2 * (Nat.card G.edgeSet : ℝ) / (Nat.card W : ℝ) ^ 2

end SidorenkoCounterexample

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
open scoped BigOperators
section SpanCount
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

noncomputable def restrictDimSubspace (Z : Submodule K V) {r : ℕ} (R : DimSubspace K V r) (h : R.val ≤ Z) :
    DimSubspace K Z r :=
  ⟨R.val.comap Z.subtype, (Submodule.comapSubtypeEquivOfLe h).finrank_eq.trans R.property⟩
end SpanCount
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

 theorem orderedTransverseTriple_card_lower [Invertible (2 : K)]
    (L M N : Lagrangian (K := K) (V := V))
    (hLM : L.val ⊓ M.val = ⊥) (hLN : L.val ⊓ N.val = ⊥) (hMN : M.val ⊓ N.val = ⊥) :
    Nat.card (Lagrangian (K := K) (V := V)) *
        (Fintype.card K^((finrank K V+1).choose 2)) ^ 2 ≤
      4^finrank K V * Nat.card (OrderedTripleOrbit (canonicalSymplectic (K := K) (V := V)) L.val M.val N.val) := by
  let : Finite (Module.Dual K V) := Module.finite_of_finite K
  have hcard := fixedPairOrbit_card_lower (canonicalSymplectic (K := K) (V := V)) L.val M.val N.val
    canonicalSymplectic_alt canonicalSymplectic_nondegenerate
    L.property M.property N.property hLM hLN hMN
  rw [lagrangian_finrank L] at hcard
  obtain ⟨f,hf⟩ := orderedTripleOrbit_pair_injection (canonicalSymplectic (K := K) (V := V)) canonicalSymplectic_alt
    canonicalSymplectic_nondegenerate L.val M.val N.val L.property M.property hLM
  have hi := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod,orderedTransversePair_card (isUnit_of_invertible (2 : K)).ne_zero] at hi
  calc
    _ = (Nat.card (Lagrangian (K := K) (V := V)) * Fintype.card K^((finrank K V+1).choose 2)) *
        Fintype.card K^((finrank K V+1).choose 2) := by rw [pow_two]; ac_rfl
    _ ≤ (Nat.card (Lagrangian (K := K) (V := V)) * Fintype.card K^((finrank K V+1).choose 2)) *
        (4^finrank K V * Nat.card (FixedPairOrbit (canonicalSymplectic (K := K) (V := V)) L.val M.val N.val)) := Nat.mul_le_mul_left _ hcard
    _ = 4^finrank K V * (Nat.card (Lagrangian (K := K) (V := V)) *
        Fintype.card K^((finrank K V+1).choose 2) * Nat.card (FixedPairOrbit (canonicalSymplectic (K := K) (V := V)) L.val M.val N.val)) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ hi
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

theorem pairLinearOrbit_card_bounds (U V : Submodule K E) (hUV : IsCompl U V) :
    (Fintype.card K : ℝ)^(2*finrank K U*finrank K V) ≤
      2^(finrank K E)*(Nat.card (PairLinearOrbit U V) : ℝ) ∧
    (Nat.card (PairLinearOrbit U V) : ℝ) ≤
      2^(finrank K E)*(Fintype.card K : ℝ)^(2*finrank K U*finrank K V) := by
  let u := finrank K U
  let v := finrank K V
  let n := finrank K E
  let q : ℝ := Fintype.card K
  have hn : u+v = n := Submodule.finrank_add_eq_of_isCompl hUV
  have he : n*n = 2*u*v + (u*u+v*v) := by rw [←hn]; ring
  have hq : 0 < q := by dsimp [q]; exact_mod_cast Fintype.card_pos (α := K)
  have hi : (Nat.card (PairLinearOrbit U V) : ℝ)*
      ((Nat.card (U ≃ₗ[K] U) : ℝ)*Nat.card (V ≃ₗ[K] V)) = Nat.card (E ≃ₗ[K] E) := by
    exact_mod_cast pairLinearOrbit_card_identity U V hUV
  have hu : (Nat.card (U ≃ₗ[K] U) : ℝ) ≤ q^(u*u) := by dsimp [q,u,v,n]; exact_mod_cast linearAut_card_upper (K := K) (E := U)
  have hv : (Nat.card (V ≃ₗ[K] V) : ℝ) ≤ q^(v*v) := by dsimp [q,u,v,n]; exact_mod_cast linearAut_card_upper (K := K) (E := V)
  have hl : q^(n*n) ≤ 2^n*(Nat.card (E ≃ₗ[K] E) : ℝ) := by dsimp [q,u,v,n]; exact_mod_cast linearAut_card_lower (K := K) (E := E)
  have hu' : q^(u*u) ≤ 2^u*(Nat.card (U ≃ₗ[K] U) : ℝ) := by dsimp [q,u,v,n]; exact_mod_cast linearAut_card_lower (K := K) (E := U)
  have hv' : q^(v*v) ≤ 2^v*(Nat.card (V ≃ₗ[K] V) : ℝ) := by dsimp [q,u,v,n]; exact_mod_cast linearAut_card_lower (K := K) (E := V)
  have hn' : (Nat.card (E ≃ₗ[K] E) : ℝ) ≤ q^(n*n) := by dsimp [q,u,v,n]; exact_mod_cast linearAut_card_upper (K := K) (E := E)
  constructor
  · apply (mul_le_mul_iff_left₀ (pow_pos hq (u*u+v*v))).mp
    calc
      _ = q^(n*n) := by rw [←pow_add,←he]
      _ ≤ _ := hl
      _ = 2^n*((Nat.card (PairLinearOrbit U V) : ℝ)*
          ((Nat.card (U ≃ₗ[K] U) : ℝ)*Nat.card (V ≃ₗ[K] V))) := by rw [hi]
      _ ≤ 2^n*((Nat.card (PairLinearOrbit U V) : ℝ)*(q^(u*u)*q^(v*v))) := by gcongr
      _ = _ := by rw [←pow_add]; ring
  · apply (mul_le_mul_iff_left₀ (pow_pos hq (u*u+v*v))).mp
    calc
      _ = (Nat.card (PairLinearOrbit U V) : ℝ)*(q^(u*u)*q^(v*v)) := by rw [pow_add]
      _ ≤ (Nat.card (PairLinearOrbit U V) : ℝ)*((2^u*Nat.card (U ≃ₗ[K] U))*(2^v*Nat.card (V ≃ₗ[K] V))) := by gcongr
      _ = 2^n*Nat.card (E ≃ₗ[K] E) := by rw [←hi,←hn,pow_add]; ring
      _ ≤ 2^n*q^(n*n) := mul_le_mul_of_nonneg_left hn' (by positivity)
      _ = _ := by rw [he,pow_add]; ring

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
 theorem conditionalProfile_card_upper (h2 : (2:K) ≠ 0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D = finrank K E) (L M : SymplecticLagrangian ω) (c v w : ℕ) (hc : c ≤ D) :
    (Fintype.card K : ℝ)^((D+1)*c + ((finrank K ↥(L.val ⊓ M.val)-c+1).choose 2+
      (v-c+1).choose 2+(w-c+1).choose 2)) * Nat.card (PairCompletion ω L M c v w) ≤
        fullProfileConstant D * (Fintype.card K : ℝ)^((finrank K ↥(L.val ⊓ M.val)+1).choose 2+(D+1).choose 2) := by
  let u := finrank K ↥(L.val ⊓ M.val)
  let δ := (D+1)*c + ((u-c+1).choose 2+(v-c+1).choose 2+(w-c+1).choose 2)
  let q : ℝ := Fintype.card K
  have hq : 0 < q := by dsimp [q]; exact_mod_cast Fintype.card_pos (α := K)
  have hu : u ≤ D := by
    have h := self_orthogonal_twice_finrank ω L.val hω L.property
    have hle := Submodule.finrank_mono (show L.val ⊓ M.val ≤ L.val from inf_le_left)
    dsimp [u]
    omega
  have hp := orderedPairDim_card_lower ω h2 ha hω D hD u hu
  have ht := tripleProfile_card_upper ω h2 ha hω D hD c u v w hc
  have hi : (Nat.card (TripleDimProfile ω c u v w) : ℝ) =
      (Nat.card (OrderedPairDim ω u) : ℝ)*Nat.card (PairCompletion ω L M c v w) := by
    exact_mod_cast tripleProfile_completion_card ω h2 ha hω L M c v w
  apply (mul_le_mul_iff_right₀ (pow_pos hq (2*(D+1).choose 2))).mp
  calc
    _ = q^δ*(q^(2*(D+1).choose 2)*Nat.card (PairCompletion ω L M c v w)) := by ring
    _ ≤ q^δ*((q^((u+1).choose 2)*Nat.card (OrderedPairDim ω u))*Nat.card (PairCompletion ω L M c v w)) := by gcongr
    _ = q^((u+1).choose 2)*(q^δ*Nat.card (TripleDimProfile ω c u v w)) := by rw [hi]; ring
    _ ≤ q^((u+1).choose 2)*(fullProfileConstant D*q^(3*(D+1).choose 2)) :=
      mul_le_mul_of_nonneg_left ht (by positivity)
    _ = q^(2*(D+1).choose 2)*(fullProfileConstant D*q^((u+1).choose 2+(D+1).choose 2)) := by
      have he : 3*(D+1).choose 2 = 2*(D+1).choose 2+(D+1).choose 2 := by omega
      rw [he,pow_add,pow_add]
      ring
end ConditionalProfile
end SidorenkoCounterexample

namespace SidorenkoCounterexample
open Module
section SymplecticPairSum
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E)
 theorem symplectic_profile_pair_sum_le [Fintype K] [Finite E]
    (hω : ω.Nondegenerate) (D : ℕ) (hD : 2*D = finrank K E)
    (L M N : SymplecticLagrangian ω) (h0 : (L.val ⊓ M.val) ⊓ N.val = ⊥) :
    finrank K ↥(L.val ⊓ M.val)+finrank K ↥(L.val ⊓ N.val)+finrank K ↥(M.val ⊓ N.val) ≤ D := by
  rw [←triplePairSum_finrank _ _ _ h0]
  exact isotropic_finrank_le_half ω hω D hD _ (triplePairSum_isotropic ω _ _ _ L.property M.property N.property)

end SymplecticPairSum
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

end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
section ActualProfile
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
 theorem actual_profile_pair_sum_le (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D c u v w : ℕ) (hD : 2*D=finrank K E) (p : TripleDimProfile ω c u v w) :
    (u-c)+(v-c)+(w-c) ≤ D-c := by
  let S := tripleProfileCommon ω p
  obtain ⟨L,M,N,hzero,hu,hv,hw,_⟩ := fixedCommonProfile_injection ω ha S ⟨p,rfl⟩
  let : Finite (ReducedSpace ω S.val) := Module.finite_of_finite K
  have hc : c≤D := S.property.2 ▸ isotropic_finrank_le_half ω hω D hD S.val S.property.1
  have hd : 2*(D-c)=finrank K (ReducedSpace ω S.val) := by
    have hh := reducedSpace_finrank ω S.val hω S.property.1
    rw [S.property.2,←hD] at hh
    omega
  simpa only [hu,hv,hw] using symplectic_profile_pair_sum_le
    (symplecticReductionForm ω S.val ha) (symplecticReductionForm_nondegenerate ω S.val ha hω) (D-c) hd L M N hzero
end ActualProfile
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open scoped BigOperators
noncomputable def triangular (n : ℝ) : ℝ := n*(n+1)/2
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
end SidorenkoCounterexample
namespace SidorenkoCounterexample

def pairVertices : Fin 33 → Finset (Fin 13) := ![{0,2}, {0,3}, {2,3}, {0,9}, {2,9}, {0,1}, {1,3}, {2,4}, {3,4}, {1,9}, {4,9}, {1,10}, {3,10}, {3,11}, {4,11}, {1,12}, {9,12}, {4,8}, {8,9}, {1,7}, {7,10}, {10,11}, {8,11}, {7,12}, {8,12}, {5,7}, {5,10}, {5,11}, {6,8}, {6,11}, {6,7}, {6,12}, {5,6}]
def facePair : Fin 22 → Fin 3 → Fin 33 := ![![5, 1, 6], ![5, 3, 9], ![0, 1, 2], ![0, 3, 4], ![6, 11, 12], ![19, 11, 20], ![19, 15, 23], ![9, 15, 16], ![2, 7, 8], ![7, 4, 10], ![8, 13, 14], ![12, 13, 21], ![17, 10, 18], ![17, 14, 22], ![32, 25, 30], ![32, 27, 29], ![25, 26, 20], ![26, 27, 21], ![30, 31, 23], ![28, 29, 22], ![28, 31, 24], ![18, 24, 16]]
def pairFace : Fin 33 → Fin 2 → Fin 22 := ![![2, 3], ![0, 2], ![2, 8], ![1, 3], ![3, 9], ![0, 1], ![0, 4], ![8, 9], ![8, 10], ![1, 7], ![9, 12], ![4, 5], ![4, 11], ![10, 11], ![10, 13], ![6, 7], ![7, 21], ![12, 13], ![12, 21], ![5, 6], ![5, 16], ![11, 17], ![13, 19], ![6, 18], ![20, 21], ![14, 16], ![16, 17], ![15, 17], ![19, 20], ![15, 19], ![14, 18], ![18, 20], ![14, 15]]
def pairParent : Fin 33 → Fin 33 := ![0, 0, 0, 0, 0, 1, 1, 2, 2, 3, 4, 6, 6, 8, 8, 9, 9, 10, 10, 11, 11, 12, 14, 15, 16, 20, 20, 21, 22, 22, 23, 23, 25]
def pairBridge : Fin 33 → Fin 22 := ![2, 2, 2, 3, 3, 0, 0, 8, 8, 1, 9, 4, 4, 10, 10, 7, 7, 12, 12, 5, 5, 11, 13, 6, 21, 16, 16, 17, 19, 19, 18, 18, 14]
def faceBit : Fin 22 → Fin 3 → Bool := ![![false, false, false], ![false, true, false], ![false, false, true], ![true, true, false], ![false, false, true], ![false, false, false], ![true, false, false], ![true, true, false], ![true, false, true], ![true, false, false], ![true, true, true], ![true, false, true], ![true, false, true], ![false, true, true], ![false, false, false], ![true, true, false], ![false, true, false], ![true, true, true], ![false, false, true], ![false, true, false], ![false, true, true], ![true, true, true]]
def separationCount (e : Fin 33) : ℕ := (Finset.univ.filter fun b => faceBit (pairFace e 0) b ≠ faceBit (pairFace e 1) b).card

 theorem faces_card : ∀ j, (faces j).card = 3 := by decide
 theorem pairVertices_card : ∀ e, (pairVertices e).card = 2 := by decide
 theorem pairVertices_injective : Function.Injective pairVertices := by decide
 theorem facePair_injective : ∀ j, Function.Injective (facePair j) := by decide
 theorem facePair_correct : ∀ j e, pairVertices e ⊆ faces j ↔ ∃ k, facePair j k=e := by decide
 theorem pairFace_correct : ∀ e j, pairVertices e ⊆ faces j ↔ ∃ k, pairFace e k=j := by decide
 theorem pairFace_injective : ∀ e, Function.Injective (pairFace e) := by decide
 theorem pairParent_lt : ∀ e, e≠0 → (pairParent e).val < e.val := by decide
 theorem pairBridge_self : ∀ e, pairVertices e ⊆ faces (pairBridge e) := by decide
 theorem pairBridge_parent : ∀ e, pairVertices (pairParent e) ⊆ faces (pairBridge e) := by decide
 theorem separationCount_pos : ∀ e, 1 ≤ separationCount e := by decide
 theorem separationCount_root : separationCount 0=3 := by decide
 theorem separationCount_le : ∀ e, separationCount e ≤ 3 := by decide
 theorem root_pair : pairVertices 0={0,2} := by rfl

end SidorenkoCounterexample

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
def classParent : Fin 6 → Fin 10 → Fin 11 := ![![0, 0, 0, 3, 4, 5, 6, 7, 8, 9], ![0, 1, 2, 3, 4, 5, 1, 7, 8, 9], ![0, 1, 2, 3, 0, 5, 5, 7, 8, 9], ![0, 0, 2, 3, 4, 5, 6, 5, 8, 9], ![0, 1, 2, 1, 4, 5, 6, 7, 8, 9], ![0, 1, 2, 3, 3, 2, 6, 7, 8, 9]]

 theorem faceVertex_correct : ∀ j, faces j={faceVertex j 0,faceVertex j 1,faceVertex j 2} := by decide
 theorem classPoint_bijective : ∀ c, Function.Bijective (classPoint c) := by decide
 theorem classFace_injective : ∀ c, Function.Injective (classFace c) := by decide
 theorem classOldZero_lt : ∀ c n, (classOldZero c n).val<3+n.val := by decide
 theorem classOldOne_lt : ∀ c n, (classOldOne c n).val<3+n.val := by decide
 theorem classRoot_correct : ∀ c, faces (classFace c 0)={classPoint c 0,classPoint c 1,classPoint c 2} := by decide
 theorem classStep_correct : ∀ c n, faces (classFace c n.succ)=
    {classPoint c (classOldZero c n),classPoint c (classOldOne c n),classPoint c ⟨3+n.val,by omega⟩} := by decide
 theorem classOldPair_correct : ∀ c n, pairVertices (classOldPair c n)=
    {classPoint c (classOldZero c n),classPoint c (classOldOne c n)} := by decide
 theorem classNewPairZero_correct : ∀ c n, pairVertices (classNewPairZero c n)=
    {classPoint c (classOldZero c n),classPoint c ⟨3+n.val,by omega⟩} := by decide
 theorem classNewPairOne_correct : ∀ c n, pairVertices (classNewPairOne c n)=
    {classPoint c (classOldOne c n),classPoint c ⟨3+n.val,by omega⟩} := by decide
 theorem classParent_lt : ∀ c n, (classParent c n).val<n.val+1 := by decide
 theorem classOldPair_parent : ∀ c n, pairVertices (classOldPair c n) ⊆ faces (classFace c (classParent c n)) := by decide
 theorem classOldPair_injective : ∀ c, Function.Injective (classOldPair c) := by decide
 def classContains (c : Fin 6) (j : Fin 22) : Prop := ∃ n, classFace c n=j
 instance (c : Fin 6) (j : Fin 22) : Decidable (classContains c j) := inferInstanceAs (Decidable (∃ n, classFace c n=j))
 def classInternal (c : Fin 6) (e : Fin 33) : Prop := ∀ k, classContains c (pairFace e k)
 instance (c : Fin 6) (e : Fin 33) : Decidable (classInternal c e) := inferInstanceAs (Decidable (∀ k, classContains c (pairFace e k)))
 theorem classFace_occurs : ∀ j, (Finset.univ.filter fun cn : Fin 6 × Fin 11 => classFace cn.1 cn.2=j).card=3 := by decide
 theorem classInternal_occurs : ∀ e, (Finset.univ.filter fun c => classInternal c e).card=3-separationCount e := by decide
 theorem classOldPair_internal : ∀ c n, classInternal c (classOldPair c n) := by decide
 theorem classStep_pairs : ∀ c n, Finset.image (facePair (classFace c n.succ)) Finset.univ =
    {classOldPair c n,classNewPairZero c n,classNewPairOne c n} := by decide
 theorem classStep_pairs_distinct : ∀ c n, classOldPair c n≠classNewPairZero c n ∧
    classOldPair c n≠classNewPairOne c n ∧ classNewPairZero c n≠classNewPairOne c n := by decide

 theorem faceVertex_injective : ∀ j, Function.Injective (faceVertex j) := by decide
 theorem faceVertex_pairs : ∀ j k, pairVertices (facePair j k)=
    (![ {faceVertex j 0,faceVertex j 1}, {faceVertex j 0,faceVertex j 2}, {faceVertex j 1,faceVertex j 2}] : Fin 3 → Finset (Fin 13)) k := by decide
 theorem classRootPairZero : ∀ c, pairVertices (facePair (classFace c 0) 0)={classPoint c 0,classPoint c 1} := by decide
 theorem classRootPairOne : ∀ c, pairVertices (facePair (classFace c 0) 1)={classPoint c 0,classPoint c 2} := by decide
 theorem classRootPairTwo : ∀ c, pairVertices (facePair (classFace c 0) 2)={classPoint c 1,classPoint c 2} := by decide
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
def naturalProfileCost (D c u v w : ℕ) : ℕ :=
  (D+1)*c+((u-c+1).choose 2+(v-c+1).choose 2+(w-c+1).choose 2)
 theorem tripleProfile_card_raw (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D=finrank K E) (c u v w : ℕ) (hc : c≤D) :
    (Nat.card (TripleDimProfile ω c u v w):ℝ) ≤ fullProfileConstant D *
      (Nat.card (SymplecticLagrangian ω):ℝ)^3 * (Fintype.card K:ℝ)^(-(naturalProfileCost D c u v w:ℝ)) := by
  have hq : 0<(Fintype.card K:ℝ) := by exact_mod_cast Fintype.card_pos (α:=K)
  have hb := (symplecticLagrangian_card_bounds ω h2 ha hω D hD).1
  apply inverse_power_inequality _ _ _ _ _ hq
  calc
    _ ≤ fullProfileConstant D*(Fintype.card K:ℝ)^(3*(D+1).choose 2) :=
      tripleProfile_card_upper ω h2 ha hω D hD c u v w hc
    _ ≤ _ := by
      gcongr
      · exact (fullProfileConstant_pos D).le
      · rw [mul_comm 3, pow_mul]
        exact pow_le_pow_left₀ (by positivity) hb 3
 theorem conditionalProfile_card_raw (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D=finrank K E) (L M : SymplecticLagrangian ω) (c v w : ℕ) (hc : c≤D) :
    (Nat.card (PairCompletion ω L M c v w):ℝ) ≤ fullProfileConstant D *
      (Nat.card (SymplecticLagrangian ω):ℝ) * (Fintype.card K:ℝ)^
        (((finrank K ↥(L.val ⊓ M.val)+1).choose 2:ℝ)-(naturalProfileCost D c (finrank K ↥(L.val ⊓ M.val)) v w:ℝ)) := by
  have hq : 0<(Fintype.card K:ℝ) := by exact_mod_cast Fintype.card_pos (α:=K)
  have hb := (symplecticLagrangian_card_bounds ω h2 ha hω D hD).1
  have hh := conditionalProfile_card_upper ω h2 ha hω D hD L M c v w hc
  have hh' : (Fintype.card K:ℝ)^(naturalProfileCost D c (finrank K ↥(L.val ⊓ M.val)) v w)*
      (Nat.card (PairCompletion ω L M c v w):ℝ) ≤ fullProfileConstant D*
        ((Nat.card (SymplecticLagrangian ω):ℝ)*(Fintype.card K:ℝ)^((finrank K ↥(L.val ⊓ M.val)+1).choose 2)) := by
    change (Fintype.card K:ℝ)^(naturalProfileCost D c (finrank K ↥(L.val ⊓ M.val)) v w)*
      (Nat.card (PairCompletion ω L M c v w):ℝ) ≤ _ at hh
    refine hh.trans ?_
    rw [pow_add]
    calc
      _ ≤ fullProfileConstant D*((Fintype.card K:ℝ)^((finrank K ↥(L.val ⊓ M.val)+1).choose 2)*
        (Nat.card (SymplecticLagrangian ω):ℝ)) := by gcongr; exact (fullProfileConstant_pos D).le
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

def faceNaturalCost (D : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (j : Fin 22) : ℕ :=
  (D+1)*c j+∑ k : Fin 3, (h (facePair j k)-c j+1).choose 2
 theorem root_natural_cost (D : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (j : Fin 22) :
    naturalProfileCost D (c j) (h (facePair j 0)) (h (facePair j 1)) (h (facePair j 2))=faceNaturalCost D c h j := by
  simp only [naturalProfileCost,faceNaturalCost,Fin.sum_univ_three]
 theorem step_natural_cost (D : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (κ : Fin 6) (n : Fin 10) :
    naturalProfileCost D (c (classFace κ n.succ)) (h (classOldPair κ n))
      (h (classNewPairZero κ n)) (h (classNewPairOne κ n))=faceNaturalCost D c h (classFace κ n.succ) := by
  let f (e : Fin 33) := (h e-c (classFace κ n.succ)+1).choose 2
  have hs : (∑ e ∈ Finset.univ.image (facePair (classFace κ n.succ)), f e)=
      ∑ k : Fin 3, f (facePair (classFace κ n.succ) k) :=
    Finset.sum_image (fun a _ b _ hab => facePair_injective _ hab)
  rw [classStep_pairs] at hs
  obtain ⟨h01,h02,h12⟩ := classStep_pairs_distinct κ n
  simp only [Finset.sum_insert,Finset.mem_insert,Finset.mem_singleton,h01,h02,h12,
    or_self,not_false_eq_true,Finset.sum_singleton] at hs
  unfold naturalProfileCost faceNaturalCost
  change _ = (D+1)*c (classFace κ n.succ)+∑ k, f (facePair (classFace κ n.succ) k)
  rw [←hs]
  simp only [f]
  omega
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

def classRootConstraint (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (κ : Fin 6) (x : Fin 3 → SymplecticLagrangian ω) : Prop :=
  LocalProfile ω (c (classFace κ 0)) (h (facePair (classFace κ 0) 0))
    (h (facePair (classFace κ 0) 1)) (h (facePair (classFace κ 0) 2)) (x 0) (x 1) (x 2)

def classStepConstraint (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (κ : Fin 6)
    (n : ℕ) (x : Fin (3+n) → SymplecticLagrangian ω) (Y : SymplecticLagrangian ω) : Prop :=
  if hn : n<10 then
    LocalProfile ω (c (classFace κ ⟨n+1,by omega⟩)) (h (classOldPair κ ⟨n,hn⟩))
      (h (classNewPairZero κ ⟨n,hn⟩)) (h (classNewPairOne κ ⟨n,hn⟩))
      (x ⟨(classOldZero κ ⟨n,hn⟩).val,classOldZero_lt κ ⟨n,hn⟩⟩)
      (x ⟨(classOldOne κ ⟨n,hn⟩).val,classOldOne_lt κ ⟨n,hn⟩⟩) Y
  else False
noncomputable def rootConstraintEquiv (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (κ : Fin 6) :
    {x : Fin 3 → SymplecticLagrangian ω // classRootConstraint ω c h κ x} ≃
      TripleDimProfile ω (c (classFace κ 0)) (h (facePair (classFace κ 0) 0))
        (h (facePair (classFace κ 0) 1)) (h (facePair (classFace κ 0) 2)) :=
  tupleThreeEquiv.subtypeEquiv (fun _ => Iff.rfl)

variable [Fintype K] [Finite E]
noncomputable def classStepBound (D : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (κ : Fin 6) (n : ℕ) : ℝ :=
  if hn : n<10 then fullProfileConstant D*(Nat.card (SymplecticLagrangian ω):ℝ)*
    (Fintype.card K:ℝ)^(((h (classOldPair κ ⟨n,hn⟩)+1).choose 2:ℝ)-(faceNaturalCost D c h (classFace κ ⟨n+1,by omega⟩):ℝ))
  else 0
 omit [Finite E] in
 theorem classStepBound_nonneg (D : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (κ : Fin 6) (n : ℕ) :
    0≤classStepBound ω D c h κ n := by
  unfold classStepBound
  split_ifs
  · exact mul_nonneg (mul_nonneg (fullProfileConstant_pos D).le (by positivity)) (Real.rpow_nonneg (by positivity) _)
  · exact le_rfl
 theorem classStep_card_bound (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D=finrank K E) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (hc : ∀ j, c j≤D)
    (κ : Fin 6) (n : ℕ) (x : Fin (3+n) → SymplecticLagrangian ω) :
    (Nat.card {Y : SymplecticLagrangian ω // classStepConstraint ω c h κ n x Y}:ℝ) ≤ classStepBound ω D c h κ n := by
  classical
  by_cases hn : n<10
  · let L := x ⟨(classOldZero κ ⟨n,hn⟩).val,classOldZero_lt κ ⟨n,hn⟩⟩
    let M := x ⟨(classOldOne κ ⟨n,hn⟩).val,classOldOne_lt κ ⟨n,hn⟩⟩
    let j : Fin 22 := classFace κ ⟨n+1,by omega⟩
    let e := classOldPair κ ⟨n,hn⟩
    let f := classNewPairZero κ ⟨n,hn⟩
    let g := classNewPairOne κ ⟨n,hn⟩
    have hp : ∀ Y, classStepConstraint ω c h κ n x Y ↔ LocalProfile ω (c j) (h e) (h f) (h g) L M Y := by
      intro Y; simp only [classStepConstraint,dif_pos hn]; rfl
    by_cases hh : finrank K ↥(L.val ⊓ M.val)=h e
    · have heq : Nat.card {Y // classStepConstraint ω c h κ n x Y}=Nat.card (PairCompletion ω L M (c j) (h f) (h g)) := by
        apply Nat.card_congr
        exact Equiv.subtypeEquivRight (fun Y => by rw [hp]; exact ⟨fun hY => ⟨hY.1,hY.2.2⟩,fun hY => ⟨hY.1,hh,hY.2⟩⟩)
      rw [heq]
      have hb := conditionalProfile_card_raw ω h2 ha hω D hD L M (c j) (h f) (h g) (hc j)
      rw [hh] at hb
      have hcost := step_natural_cost D c h κ ⟨n,hn⟩
      change naturalProfileCost D (c j) (h e) (h f) (h g)=faceNaturalCost D c h j at hcost
      rw [hcost] at hb
      simpa only [classStepBound,dif_pos hn, e,j] using hb
    · have hem : IsEmpty {Y // classStepConstraint ω c h κ n x Y} := ⟨fun Y => hh ((hp Y.val).mp Y.property).2.1⟩
      have hz := Nat.card_eq_zero.mpr (Or.inl hem)
      rw [hz,Nat.cast_zero]
      exact classStepBound_nonneg ω D c h κ n
  · have hem : IsEmpty {Y // classStepConstraint ω c h κ n x Y} :=
      ⟨fun Y => by simpa only [classStepConstraint,dif_neg hn] using Y.property⟩
    rw [Nat.card_eq_zero.mpr (Or.inl hem),Nat.cast_zero,classStepBound,dif_neg hn]

noncomputable def classPrefix (κ : Fin 6) (L : Fin 13 → SymplecticLagrangian ω)
    (n : ℕ) (hn : n≤10) : Fin (3+n) → SymplecticLagrangian ω :=
  fun i => L (classPoint κ ⟨i.val,by omega⟩)
 omit [Fintype K] [Finite E] in
 theorem classPrefix_valid {c : Fin 22 → ℕ} {h : Fin 33 → ℕ}
    {L : Fin 13 → SymplecticLagrangian ω} (hL : PointProfile ω c h L)
    (κ : Fin 6) (n : ℕ) (hn : n≤10) :
    SeqValid 3 (classRootConstraint ω c h κ) (classStepConstraint ω c h κ) n (classPrefix ω κ L n hn) := by
  induction n with
  | zero =>
    exact PointProfile.local ω hL _ _ _ _ _ _ _ (classRoot_correct κ)
      (classRootPairZero κ) (classRootPairOne κ) (classRootPairTwo κ)
  | succ n ih =>
    have hn' : n<10 := by omega
    refine ⟨?_,?_⟩
    · exact ih (by omega)
    · simp only [classStepConstraint,dif_pos hn']
      exact PointProfile.local ω hL _ _ _ _ _ _ _ (classStep_correct κ ⟨n,hn'⟩)
        (classOldPair_correct κ ⟨n,hn'⟩) (classNewPairZero_correct κ ⟨n,hn'⟩)
        (classNewPairOne_correct κ ⟨n,hn'⟩)
noncomputable def pointProfile_class_injection (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (κ : Fin 6) :
    {L : Fin 13 → SymplecticLagrangian ω // PointProfile ω c h L} ↪
      ValidSeq 3 (classRootConstraint ω c h κ) (classStepConstraint ω c h κ) 10 where
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
    (κ : Fin 6) : (Nat.card {x : Fin 3 → SymplecticLagrangian ω // classRootConstraint ω c h κ x}:ℝ) ≤
      fullProfileConstant D*(Nat.card (SymplecticLagrangian ω):ℝ)^3*
        (Fintype.card K:ℝ)^(-(faceNaturalCost D c h (classFace κ 0):ℝ)) := by
  rw [Nat.card_congr (rootConstraintEquiv ω c h κ)]
  have hb := tripleProfile_card_raw ω h2 ha hω D hD (c (classFace κ 0))
    (h (facePair (classFace κ 0) 0)) (h (facePair (classFace κ 0) 1))
    (h (facePair (classFace κ 0) 2)) (hc _)
  simpa only [root_natural_cost] using hb

noncomputable def classExponent (D : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (κ : Fin 6) : ℝ :=
  -(∑ i : Fin 11, (faceNaturalCost D c h (classFace κ i):ℝ))+
    ∑ i : Fin 10, ((h (classOldPair κ i)+1).choose 2:ℝ)
 omit [Finite E] in
 theorem classStepBound_product (D : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (κ : Fin 6) :
    (∏ n : Fin 10, classStepBound ω D c h κ n.val)=
      (fullProfileConstant D*(Nat.card (SymplecticLagrangian ω):ℝ))^10*
        (Fintype.card K:ℝ)^(∑ n : Fin 10,
          (((h (classOldPair κ n)+1).choose 2:ℝ)-(faceNaturalCost D c h (classFace κ n.succ):ℝ))) := by
  have hq : 0<(Fintype.card K:ℝ) := by exact_mod_cast Fintype.card_pos (α:=K)
  simp only [classStepBound,dif_pos (Fin.isLt _),Fin.eta,Finset.prod_mul_distrib,
    Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  rw [Real.rpow_sum_of_pos hq,mul_pow]
  rfl
 theorem pointProfile_class_card_bound (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D=finrank K E) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (hc : ∀ j, c j≤D)
    (κ : Fin 6) : (Nat.card {L : Fin 13 → SymplecticLagrangian ω // PointProfile ω c h L}:ℝ) ≤
      (fullProfileConstant D)^11*(Nat.card (SymplecticLagrangian ω):ℝ)^13*
        (Fintype.card K:ℝ)^(classExponent D c h κ) := by
  have hq : 0<(Fintype.card K:ℝ) := by exact_mod_cast Fintype.card_pos (α:=K)
  have hs := validSeq_card_bound 3 (classRootConstraint ω c h κ) (classStepConstraint ω c h κ)
    (classStepBound ω D c h κ) (classStepBound_nonneg ω D c h κ)
    (fun n x => classStep_card_bound ω h2 ha hω D hD c h hc κ n x.val) 10
  have hr := classRoot_card_bound ω h2 ha hω D hD c h hc κ
  have hi : (Nat.card {L : Fin 13 → SymplecticLagrangian ω // PointProfile ω c h L}:ℝ) ≤
      Nat.card (ValidSeq 3 (classRootConstraint ω c h κ) (classStepConstraint ω c h κ) 10) := by
    exact_mod_cast Nat.card_le_card_of_injective _ (pointProfile_class_injection ω c h κ).injective
  calc
    _ ≤ _ := hi.trans hs
    _ ≤ (fullProfileConstant D*(Nat.card (SymplecticLagrangian ω):ℝ)^3*
        (Fintype.card K:ℝ)^(-(faceNaturalCost D c h (classFace κ 0):ℝ)))*
        ∏ n : Fin 10,classStepBound ω D c h κ n.val :=
      mul_le_mul_of_nonneg_right hr (Finset.prod_nonneg fun n _ => classStepBound_nonneg ω D c h κ n.val)
    _ = _ := by
      rw [classStepBound_product]
      have he : -(faceNaturalCost D c h (classFace κ 0):ℝ)+
          (∑ n : Fin 10, (((h (classOldPair κ n)+1).choose 2:ℝ)-
            (faceNaturalCost D c h (classFace κ n.succ):ℝ)))=classExponent D c h κ := by
        unfold classExponent
        rw [Fin.sum_univ_succ (fun i : Fin 11 => (faceNaturalCost D c h (classFace κ i):ℝ)),Finset.sum_sub_distrib]
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
  (∑ j, (faceNaturalCost D c h j:ℝ))/2-(∑ e, (3-(separationCount e:ℝ))*triangular (h e))/6
 theorem sum_class_exponent (D : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) :
    (∑ κ, classExponent D c h κ)= -6*profileCost D c h := by
  simp only [classExponent,Finset.sum_add_distrib,Finset.sum_neg_distrib,triangular_nat]
  rw [sum_class_faces (fun j => (faceNaturalCost D c h j:ℝ)),sum_class_old_pairs (fun e => triangular (h e))]
  unfold profileCost
  ring

section GlobalExposure
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
 theorem pointProfile_card_bound (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D=finrank K E) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (hc : ∀ j, c j≤D) :
    (Nat.card {L : Fin 13 → SymplecticLagrangian ω // PointProfile ω c h L}:ℝ) ≤
      (fullProfileConstant D)^11*(Nat.card (SymplecticLagrangian ω):ℝ)^13*
        (Fintype.card K:ℝ)^(-profileCost D c h) := by
  have hq : 0<(Fintype.card K:ℝ) := by exact_mod_cast Fintype.card_pos (α:=K)
  have hb := Finset.prod_le_prod (s:=Finset.univ) (f:=fun _κ : Fin 6 =>
      (Nat.card {L : Fin 13 → SymplecticLagrangian ω // PointProfile ω c h L}:ℝ))
    (fun _κ _ => Nat.cast_nonneg _) (fun κ _ => pointProfile_class_card_bound ω h2 ha hω D hD c h hc κ)
  simp only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin] at hb
  rw [←Real.rpow_sum_of_pos hq,sum_class_exponent] at hb
  have he : -6*profileCost D c h=(-profileCost D c h)*(6:ℕ) := by norm_num; ring
  rw [he,Real.rpow_mul_natCast hq.le] at hb
  have hC := fullProfileConstant_pos D
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
noncomputable def priorConstraintCount (R : ℕ → ℕ → Prop) (n : ℕ) : ℕ :=
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
      (Fintype.card K:ℝ)^(finrank K E-priorConstraintCount R n) := by
  classical
  let s : Finset (Fin n) := Finset.univ.filter fun i => R i.val n
  have he : s.card=priorConstraintCount R n := by
    rw [priorConstraintCount,Nat.card_eq_fintype_card,Fintype.card_subtype]
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
      (Fintype.card K:ℝ)^(∑ i : Fin n, (finrank K E-priorConstraintCount R i.val)) := by
  classical
  have hs := zeroValidSeq_card_bound (OrthogonalStep ω R)
    (fun i => (Fintype.card K:ℝ)^(finrank K E-priorConstraintCount R i))
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
    (∑ i : Fin n, priorConstraintCount R i.val)=constraintPairCount R n := by
  classical
  apply Finset.sum_congr rfl
  intro j _
  let e : {i : Fin j.val // R i.val j.val} ≃ {i : Fin n // i.val<j.val ∧ R i.val j.val} :=
    { toFun := fun i => ⟨⟨i.val.val,lt_trans (by simpa only [Nat.zero_add] using i.val.isLt) j.isLt⟩,by simpa only [Nat.zero_add] using i.val.isLt,i.property⟩
      invFun := fun i => ⟨⟨i.val.val,by simpa only [Nat.zero_add] using i.property.1⟩,i.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [priorConstraintCount,Nat.card_congr e,Nat.card_eq_fintype_card,Fintype.card_subtype]
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
  have hle (i : Fin n) : priorConstraintCount R i.val≤finrank K E := by
    have hh : Nat.card {j : Fin i.val // R j.val i.val} ≤ Nat.card (Fin i.val) :=
      Nat.card_le_card_of_injective _ Subtype.val_injective
    simp only [Nat.card_eq_fintype_card,Fintype.card_fin] at hh
    simpa only [priorConstraintCount,Nat.card_eq_fintype_card] using hh.trans (i.isLt.le.trans hn)
  have he : ((∑ i : Fin n, (finrank K E-priorConstraintCount R i.val):ℕ):ℝ)=
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
    (Nat.card {L : SymplecticLagrangian ω // S≤L.val}:ℝ) ≤
      lagrangianConstant D * (Nat.card (SymplecticLagrangian ω):ℝ) *
        (Fintype.card K:ℝ)^(-(D:ℝ)*finrank K S+(finrank K S:ℝ)*(finrank K S-1)/2) := by
  classical
  have hq : 0<(Fintype.card K:ℝ) := by exact_mod_cast Fintype.card_pos (α:=K)
  by_cases his : S≤ω.orthogonal S
  · have hs := isotropic_finrank_le_half ω hω D hD S his
    have h := (containingLagrangian_card_bounds ω h2 ha hω D hD S his).2
    have hl := (symplecticLagrangian_card_bounds ω h2 ha hω D hD).1
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
        exact mul_le_mul_of_nonneg_right (mul_le_mul hC hl (by positivity) (lagrangianConstant_pos D).le) (Real.rpow_nonneg hq.le _)
  · have hz : Nat.card {L : SymplecticLagrangian ω // S≤L.val}=0 := by
      let : IsEmpty {L : SymplecticLagrangian ω // S≤L.val} := ⟨fun L => his (by
        calc
          S ≤ L.val.val := L.property
          _ = ω.orthogonal L.val.val := L.val.property.symm
          _ ≤ ω.orthogonal S := ω.orthogonal_le L.property)⟩
      exact Nat.card_eq_zero.mpr (Or.inl inferInstance)
    rw [hz,Nat.cast_zero]
    exact mul_nonneg (mul_nonneg (lagrangianConstant_pos D).le (Nat.cast_nonneg _)) (Real.rpow_nonneg hq.le _)
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
    have hh' (i : I) := subspace_count_upper (K:=K) (V:=W.val) (h i) (by rw [W.property];exact hh i)
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
      mul_le_mul_of_nonneg_right (subspace_count_upper k hk) (by positivity)
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

theorem span_inequality (s : Finset (Finset P)) (H : Finset P → Submodule K V)
    (hs : ∀ e ∈ s, e.card = 2) :
    2 * finrank K (s.sup H : Submodule K V) ≤ ∑ i, finrank K (localSpan s H i) :=
  (span_inequality_with_rigidity s H hs).1

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

def incidentPairs (i : Fin 13) : Finset (Fin 33) := Finset.univ.filter (fun e => i∈pairVertices e)
def pairRelated (e f : Fin 33) : Prop := ¬Disjoint (pairVertices e) (pairVertices f)
instance (e f : Fin 33) : Decidable (pairRelated e f) := inferInstanceAs (Decidable (¬Disjoint _ _))
 theorem pairRelated_symm (e f : Fin 33) : pairRelated e f → pairRelated f e := by
  unfold pairRelated; intro h hf; exact h hf.symm
 theorem incidentPairs_card : ∀ i, (incidentPairs i).card = (![4,6,4,6,5,4,5,5,5,6,5,6,5] : Fin 13 → ℕ) i := by decide
 theorem incidentPairs_card_le : ∀ i, (incidentPairs i).card≤6 := by decide
 theorem pair_shared_card : ∀ e f, (Finset.univ.filter (fun i => e∈incidentPairs i ∧ f∈incidentPairs i)).card =
    if e=f then 2 else if pairRelated e f then 1 else 0 := by decide
 theorem incident_pair_card (e : Fin 33) : (Finset.univ.filter (fun i => e∈incidentPairs i)).card=2 := by
  have he : Finset.univ.filter (fun i => e∈incidentPairs i)=pairVertices e := by
    ext i; simp only [Finset.mem_filter,Finset.mem_univ,true_and,incidentPairs]
  rw [he,pairVertices_card]
 theorem sum_incident (f : Fin 33 → ℝ) :
    (∑ i : Fin 13, ∑ e∈incidentPairs i, f e)=2*∑ e,f e := by
  simp only [incidentPairs,Finset.sum_filter]
  rw [Finset.sum_comm]
  have hh (e : Fin 33) : (∑ i : Fin 13, if i∈pairVertices e then f e else 0)=2*f e := by
    rw [←Finset.sum_filter,Finset.sum_const]
    have hc : (Finset.univ.filter (fun i=>i∈pairVertices e)).card=2 := by
      have he : Finset.univ.filter (fun i=>i∈pairVertices e)=pairVertices e := by ext i; simp
      rw [he,pairVertices_card]
    rw [hc]; simp only [nsmul_eq_mul,Nat.cast_ofNat]
  simp_rw [hh]
  rw [Finset.mul_sum]
noncomputable def localPairDim (h : Fin 33 → ℕ) (i : Fin 13) : ℕ := ∑ e∈incidentPairs i,h e
 theorem localPairDim_le (h : Fin 33 → ℕ) (hh : ∀ e,h e≤2) (i : Fin 13) : localPairDim h i≤2*(incidentPairs i).card := by
  unfold localPairDim
  calc _ ≤ ∑ _e∈incidentPairs i, 2 := Finset.sum_le_sum (fun e _=>hh e)
       _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul,Nat.cast_id]; omega
 theorem localPairDim_le_twelve (h : Fin 33 → ℕ) (hh : ∀ e,h e≤2) (i : Fin 13) : localPairDim h i≤12 := by
  have := localPairDim_le h hh i
  have := incidentPairs_card_le i
  omega
section GraphSpans
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
noncomputable def incidentSpan (A : Fin 33 → Submodule K E) (i : Fin 13) : Submodule K E :=
  (incidentPairs i).sup A
 theorem incidentSpan_le {A : Fin 33 → Submodule K E} {i : Fin 13} {L : Submodule K E}
    (h : ∀ e, i∈pairVertices e → A e≤L) : incidentSpan A i≤L := by
  apply Finset.sup_le
  intro e he
  exact h e (Finset.mem_filter.mp he).2
variable [FiniteDimensional K E]
 theorem incidentSpan_finrank_le (h : Fin 33 → ℕ) (A : (e : Fin 33) → DimSubspace K E (h e)) (i : Fin 13) :
    finrank K (incidentSpan (fun e=>(A e).val) i)≤localPairDim h i := by
  unfold incidentSpan localPairDim
  calc _ ≤ ∑ e∈incidentPairs i, finrank K (A e).val := finrank_finset_sup_le _ _
       _ = _ := Finset.sum_congr rfl (fun e _ => (A e).property)
 theorem incidentSpan_finrank_direct (h : Fin 33 → ℕ) (A : (e : Fin 33) → DimSubspace K E (h e))
    (ha : iSupIndep (fun e=>(A e).val)) (i : Fin 13) :
    finrank K (incidentSpan (fun e=>(A e).val) i)=localPairDim h i := by
  unfold incidentSpan localPairDim
  calc _ = ∑ e∈incidentPairs i, finrank K (A e).val := finrank_finset_sup_direct _ _ ha
       _ = _ := Finset.sum_congr rfl (fun e _ => (A e).property)
noncomputable def extendPairSpace (A : Fin 33 → Submodule K E) : Finset (Fin 13) → Submodule K E :=
  Function.extend pairVertices A (fun _=>⊥)
omit [FiniteDimensional K E] in
 theorem extendPairSpace_apply (A : Fin 33 → Submodule K E) (e : Fin 33) :
    extendPairSpace A (pairVertices e)=A e := pairVertices_injective.extend_apply _ _ _
omit [FiniteDimensional K E] in
 theorem extend_global_span (A : Fin 33 → Submodule K E) :
    (Finset.univ.image pairVertices).sup (extendPairSpace A)=⨆ e,A e := by
  rw [Finset.sup_image]
  simp only [Function.comp_def,extendPairSpace_apply,Finset.sup_eq_iSup,Finset.mem_univ,iSup_pos]
omit [FiniteDimensional K E] in
 theorem extend_local_span (A : Fin 33 → Submodule K E) (i : Fin 13) :
    localSpan (Finset.univ.image pairVertices) (extendPairSpace A) i=incidentSpan A i := by
  unfold localSpan incidentSpan incidentPairs
  rw [Finset.filter_image,Finset.sup_image]
  simp only [Function.comp_def,extendPairSpace_apply]
 theorem indexed_strict_span (A : Fin 33 → Submodule K E) (ha : ¬iSupIndep A) :
    2*finrank K ↥(⨆ e,A e)+1≤∑ i,finrank K (incidentSpan A i) := by
  have hn : ¬(Finset.univ.image pairVertices).SupIndep (extendPairSpace A) := by
    intro hs
    have hi := hs.independent
    have hj := hi.comp (f := fun e : Fin 33 => (⟨pairVertices e,Finset.mem_image.mpr ⟨e,Finset.mem_univ _,rfl⟩⟩ : ↥(Finset.univ.image pairVertices))) (by
      intro e f hef
      exact pairVertices_injective (congrArg Subtype.val hef))
    apply ha
    simpa only [Function.comp_def,extendPairSpace_apply] using hj
  have hb := strict_span_inequality (Finset.univ.image pairVertices) (extendPairSpace A)
    (by intro e he; obtain ⟨f,_,rfl⟩:=Finset.mem_image.mp he; exact pairVertices_card f) hn
  rw [extend_global_span] at hb
  have hs : (∑ i : Fin 13,finrank K (localSpan (Finset.univ.image pairVertices) (extendPairSpace A) i))=∑ i,finrank K (incidentSpan A i) :=
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
    (∑ i : Fin 13, (∑ e∈incidentPairs i,f e)*(∑ e∈incidentPairs i,g e))=
      ∑ e,∑ a, ((Finset.univ.filter (fun i=>e∈incidentPairs i ∧ a∈incidentPairs i)).card:ℝ)*f e*g a := by
  classical
  have hf (i : Fin 13) : (∑ e∈incidentPairs i,∑ a∈incidentPairs i,f e*g a)=
      ∑ e : Fin 33,∑ a : Fin 33, if e∈incidentPairs i ∧ a∈incidentPairs i then f e*g a else 0 := by
    symm
    simp only [ite_and]
    simp_rw [Finset.sum_ite_irrel,Finset.sum_ite_mem]
    simp only [Finset.sum_const_zero, Finset.sum_ite_mem, Finset.univ_inter]
  have hp (i : Fin 13) : (∑ e∈incidentPairs i,f e)*(∑ e∈incidentPairs i,g e)=
      ∑ e∈incidentPairs i,∑ a∈incidentPairs i,f e*g a := by
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
    (∑ i : Fin 13,(localPairDim h i:ℝ)^2)=
      (∑ e,(h e:ℝ)^2)+(∑ e,∑ f,if pairRelated e f then (h e:ℝ)*h f else 0) := by
  classical
  have he : (∑ i : Fin 13,(localPairDim h i:ℝ)^2)=
      ∑ i : Fin 13,(∑ e∈incidentPairs i,(h e:ℝ))*(∑ e∈incidentPairs i,(h e:ℝ)) := by
    simp only [localPairDim,Nat.cast_sum,pow_two]
  rw [he,sum_local_products]
  have hp (e f : Fin 33) :
      ((Finset.univ.filter (fun i=>e∈incidentPairs i ∧ f∈incidentPairs i)).card:ℝ)*(h e:ℝ)*h f=
      (if e=f then (h e:ℝ)^2 else 0)+(if pairRelated e f then (h e:ℝ)*h f else 0) := by
    rw [pair_shared_card]
    by_cases hef : e=f
    · subst f; simp only [ite_true,pairRelated_self,Nat.cast_ofNat,pow_two]; ring
    · by_cases hr : pairRelated e f <;> simp [hef,hr]
  simp_rw [hp,Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]

 theorem sum_localPairDim (h : Fin 33 → ℕ) : (∑ i,(localPairDim h i:ℝ))=2*∑ e,(h e:ℝ) := by
  simpa only [localPairDim,Nat.cast_sum] using sum_incident (fun e=>(h e:ℝ))

 theorem residual_direct_exponent (D : ℕ) (h : Fin 33 → ℕ) :
    2*(D:ℝ)*(∑ e,(h e:ℝ))-
      (Nat.card {p : (Σ e, Fin (h e))×(Σ e, Fin (h e)) // p.1≠p.2 ∧ pairRelated p.1.1 p.2.1}:ℝ)/2-
      (∑ e,(h e:ℝ)^2)+(∑ i : Fin 13, (-(D:ℝ)*localPairDim h i+(localPairDim h i:ℝ)*(localPairDim h i-1)/2))=
      -∑ e,triangular (h e) := by
  rw [related_label_count]
  have hl : (∑ i : Fin 13, (-(D:ℝ)*localPairDim h i+(localPairDim h i:ℝ)*(localPairDim h i-1)/2))=
      -(D:ℝ)*(∑ i,(localPairDim h i:ℝ))+((∑ i,(localPairDim h i:ℝ)^2)-(∑ i,(localPairDim h i:ℝ)))/2 := by
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
 theorem degree_choose_sum : (∑ i : Fin 13,(2*(incidentPairs i).card).choose 2)=618 := by decide
 theorem local_choose_sum_bound (ki : Fin 13 → ℕ) (hk : ∀ i,ki i≤2*(incidentPairs i).card) :
    (∑ i : Fin 13, (ki i:ℝ)*(ki i-1)/2)≤618 := by
  have hb : (∑ i : Fin 13,(ki i).choose 2)≤618 := by
    rw [←degree_choose_sum]
    exact Finset.sum_le_sum (fun i _=>Nat.choose_le_choose 2 (hk i))
  have hc : (∑ i : Fin 13, ((ki i).choose 2:ℝ))≤618 := by exact_mod_cast hb
  simpa only [Nat.cast_choose_two] using hc
 theorem residual_nondirect_exponent (D k : ℕ) (h : Fin 33 → ℕ) (ki : Fin 13 → ℕ)
    (hh : ∀ e,h e=0 ∨ h e=2) (hk : ∀ i,ki i≤2*(incidentPairs i).card)
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
noncomputable def pairSpaces (L : Fin 13 → SymplecticLagrangian ω) (e : Fin 33) : Submodule K E :=
  (pairVertices e).inf (fun i=>(L i).val)
 theorem pairSpaces_le (L : Fin 13 → SymplecticLagrangian ω) (e : Fin 33) (i : Fin 13)
    (hi : i∈pairVertices e) : pairSpaces ω L e≤(L i).val := Finset.inf_le hi
 theorem incidentPairSpaces_le (L : Fin 13 → SymplecticLagrangian ω) (i : Fin 13) :
    incidentSpan (pairSpaces ω L) i≤(L i).val :=
  incidentSpan_le (fun e he=>pairSpaces_le ω L e i he)
 theorem pairSpaces_orthogonal (L : Fin 13 → SymplecticLagrangian ω) (e f : Fin 33)
    (hr : pairRelated e f) {x y : E} (hx : x∈pairSpaces ω L e) (hy : y∈pairSpaces ω L f) : ω x y=0 := by
  classical
  obtain ⟨i,he,hf⟩ := Finset.not_disjoint_iff.mp hr
  have hxi := pairSpaces_le ω L e i he hx
  have hyi := pairSpaces_le ω L f i hf hy
  have hyO : y∈ω.orthogonal (L i).val := (L i).property.symm ▸ hyi
  exact hyO x hxi
abbrev PairDimProfile (h : Fin 33 → ℕ) :=
  {L : Fin 13 → SymplecticLagrangian ω // ∀ e,finrank K (pairSpaces ω L e)=h e}
abbrev DirectPairProfile (h : Fin 33 → ℕ) :=
  {L : PairDimProfile ω h // iSupIndep (pairSpaces ω L.val)}
abbrev FamilyContainment (A : Fin 33 → Submodule K E) :=
  (i : Fin 13) → {L : SymplecticLagrangian ω // incidentSpan A i≤L.val}
noncomputable def directPairProfileCoding (h : Fin 33 → ℕ) (L : DirectPairProfile ω h) :
    Σ A : DirectFamily ω h pairRelated, FamilyContainment ω (fun e=>(A.val e).val) :=
  ⟨⟨fun e=>⟨pairSpaces ω L.val.val e,L.val.property e⟩,L.property,
    fun e f hr _ hx _ hy=>pairSpaces_orthogonal ω L.val.val e f hr hx hy⟩,
    fun i=>⟨L.val.val i,incidentPairSpaces_le ω L.val.val i⟩⟩
 theorem directPairProfileCoding_injective (h : Fin 33 → ℕ) :
    Function.Injective (directPairProfileCoding ω h) := by
  let recover : (Σ A : DirectFamily ω h pairRelated, FamilyContainment ω (fun e=>(A.val e).val)) →
      (Fin 13 → SymplecticLagrangian ω) := fun x i=>(x.2 i).val
  intro x y hxy
  exact Subtype.ext (Subtype.ext (congrArg recover hxy))
noncomputable def containmentExponent (D : ℕ) (ki : Fin 13 → ℕ) : ℝ :=
  ∑ i, (-(D:ℝ)*ki i+(ki i:ℝ)*(ki i-1)/2)
variable [Fintype K] [Finite E]
 theorem familyContainment_card_bound (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D=finrank K E) (A : Fin 33 → Submodule K E) (ki : Fin 13 → ℕ)
    (hk : ∀ i,finrank K (incidentSpan A i)=ki i) :
    (Nat.card (FamilyContainment ω A):ℝ) ≤ (lagrangianConstant D)^13*
      (Nat.card (SymplecticLagrangian ω):ℝ)^13*(Fintype.card K:ℝ)^(containmentExponent D ki) := by
  have hq : 0<(Fintype.card K:ℝ) := by exact_mod_cast Fintype.card_pos (α:=K)
  have hp (i : Fin 13) : (Nat.card {L : SymplecticLagrangian ω // incidentSpan A i≤L.val}:ℝ) ≤
      lagrangianConstant D*(Nat.card (SymplecticLagrangian ω):ℝ)*
        (Fintype.card K:ℝ)^(-(D:ℝ)*ki i+(ki i:ℝ)*(ki i-1)/2) := by
    simpa only [hk i] using containingLagrangian_card_rpow ω h2 ha hω D hD (incidentSpan A i)
  have hh := Finset.prod_le_prod (s:=Finset.univ) (fun i _=>Nat.cast_nonneg (Nat.card {L : SymplecticLagrangian ω // incidentSpan A i≤L.val})) (fun i _=>hp i)
  rw [FamilyContainment,Nat.card_pi,Nat.cast_prod]
  calc _ ≤ _ := hh
       _ = _ := by
        rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,
          mul_pow,←Real.rpow_sum_of_pos hq]
        rfl
 theorem directPairProfile_card_bound (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D=finrank K E) (h : Fin 33 → ℕ) (hn : (∑ e,h e)≤2*D) :
    (Nat.card (DirectPairProfile ω h):ℝ) ≤
      2^(∑ e,h e)*(lagrangianConstant D)^13*(Nat.card (SymplecticLagrangian ω):ℝ)^13*
        (Fintype.card K:ℝ)^(-(∑ e,triangular (h e))) := by
  have hq : 0<(Fintype.card K:ℝ) := by exact_mod_cast Fintype.card_pos (α:=K)
  have hs : ∀ A : DirectFamily ω h pairRelated, (Nat.card (FamilyContainment ω (fun e=>(A.val e).val)):ℝ) ≤
      (lagrangianConstant D)^13*(Nat.card (SymplecticLagrangian ω):ℝ)^13*
        (Fintype.card K:ℝ)^(containmentExponent D (localPairDim h)) := by
    intro A
    exact familyContainment_card_bound ω h2 ha hω D hD _ _ (incidentSpan_finrank_direct h A.val A.property.1)
  have hi : (Nat.card (DirectPairProfile ω h):ℝ)≤
      Nat.card (Σ A : DirectFamily ω h pairRelated,FamilyContainment ω (fun e=>(A.val e).val)) := by
    exact_mod_cast Nat.card_le_card_of_injective _ (directPairProfileCoding_injective ω h)
  have hn' : (∑ e,h e)≤finrank K E := hD ▸ hn
  have hf := directFamily_card_bound ω hω h pairRelated pairRelated_symm hn'
  rw [←hD,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_sum] at hf
  have hc : 0 ≤ (lagrangianConstant D)^13*(Nat.card (SymplecticLagrangian ω):ℝ)^13*
      (Fintype.card K:ℝ)^(containmentExponent D (localPairDim h)) :=
    mul_nonneg (mul_nonneg (pow_nonneg (lagrangianConstant_pos D).le _)
      (pow_nonneg (Nat.cast_nonneg _) _)) (Real.rpow_nonneg hq.le _)
  calc _ ≤ _ := hi.trans (real_card_sigma_le _ hs)
       _ ≤ _ := mul_le_mul_of_nonneg_right hf hc
       _ = _ := by
        have he := residual_direct_exponent D h
        change _+containmentExponent D (localPairDim h)=_ at he
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
  {A : FamilySpanStratum (K:=K) (E:=E) h k // ∀ i,finrank K (incidentSpan (fun e=>(A.val e).val) i)=ki i}
abbrev PairSpanStratum (h : Fin 33 → ℕ) (k : ℕ) (ki : Fin 13 → ℕ) :=
  {L : PairDimProfile ω h // finrank K ↥(⨆ e,pairSpaces ω L.val e)=k ∧
    ∀ i,finrank K (incidentSpan (pairSpaces ω L.val) i)=ki i}
noncomputable def pairSpanStratumCoding (h : Fin 33 → ℕ) (k : ℕ) (ki : Fin 13 → ℕ)
    (L : PairSpanStratum ω h k ki) :
    Σ A : LocalFamilyStratum (K:=K) (E:=E) h k ki, FamilyContainment ω (fun e=>(A.val.val e).val) :=
  ⟨⟨⟨fun e=>⟨pairSpaces ω L.val.val e,L.val.property e⟩,L.property.1⟩,L.property.2⟩,
    fun i=>⟨L.val.val i,incidentPairSpaces_le ω L.val.val i⟩⟩
omit [Fintype K] [Finite E] in
 theorem pairSpanStratumCoding_injective (h : Fin 33 → ℕ) (k : ℕ) (ki : Fin 13 → ℕ) :
    Function.Injective (pairSpanStratumCoding ω h k ki) := by
  let recover : (Σ A : LocalFamilyStratum (K:=K) (E:=E) h k ki,
      FamilyContainment ω (fun e=>(A.val.val e).val)) → (Fin 13 → SymplecticLagrangian ω) :=
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
      2^(k+∑ e,h e)*(lagrangianConstant D)^13*(Nat.card (SymplecticLagrangian ω):ℝ)^13*
      (Fintype.card K:ℝ)^((k:ℝ)*(2*D-k)+(∑ e,(h e:ℝ)*(k-h e))+containmentExponent D ki) := by
  have hq : 0<(Fintype.card K:ℝ) := by exact_mod_cast Fintype.card_pos (α:=K)
  have hs : ∀ A : LocalFamilyStratum (K:=K) (E:=E) h k ki,
      (Nat.card (FamilyContainment ω (fun e=>(A.val.val e).val)):ℝ) ≤
      (lagrangianConstant D)^13*(Nat.card (SymplecticLagrangian ω):ℝ)^13*
        (Fintype.card K:ℝ)^(containmentExponent D ki) := by
    intro A
    exact familyContainment_card_bound ω h2 ha hω D hD _ _ A.property
  have hi : (Nat.card (PairSpanStratum ω h k ki):ℝ)≤
      Nat.card (Σ A : LocalFamilyStratum (K:=K) (E:=E) h k ki,FamilyContainment ω (fun e=>(A.val.val e).val)) := by
    exact_mod_cast Nat.card_le_card_of_injective _ (pairSpanStratumCoding_injective ω h k ki)
  have hn : k≤finrank K E := hD ▸ hk
  have hf := localFamilyStratum_card_bound h k ki hn hh
  rw [←Real.rpow_natCast (Fintype.card K:ℝ),familySpan_exponent_cast h k _ hn hh,←hD,
    Nat.cast_mul,Nat.cast_ofNat] at hf
  have hc : 0 ≤ (lagrangianConstant D)^13*(Nat.card (SymplecticLagrangian ω):ℝ)^13*
      (Fintype.card K:ℝ)^(containmentExponent D ki) :=
    mul_nonneg (mul_nonneg (pow_nonneg (lagrangianConstant_pos D).le _)
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
    finrank K (incidentSpan (pairSpaces ω L.val) i)≤localPairDim h i :=
  incidentSpan_finrank_le h (fun e=>⟨_,L.property e⟩) i
abbrev ResidualDimensionBox := Fin 67 × (Fin 13 → Fin 13)
noncomputable def pairProfileDimension (h : Fin 33 → ℕ) (hh : ∀ e,h e=0 ∨ h e=2)
    (L : PairDimProfile ω h) : ResidualDimensionBox :=
  (⟨finrank K ↥(⨆ e,pairSpaces ω L.val e),by
    have := (pairProfile_global_dim_le ω h L).trans (residual_h_sum_le h hh); omega⟩,
   fun i=>⟨finrank K (incidentSpan (pairSpaces ω L.val) i),by
    have := (pairProfile_local_dim_le ω h L i).trans (localPairDim_le_twelve h (fun e=>by rcases hh e with he|he <;> omega) i)
    omega⟩)
abbrev NonDirectPairProfile (h : Fin 33 → ℕ) :=
  {L : PairDimProfile ω h // ¬iSupIndep (pairSpaces ω L.val)}
noncomputable def nondirectDimension (h : Fin 33 → ℕ) (hh : ∀ e,h e=0 ∨ h e=2)
    (L : NonDirectPairProfile ω h) : ResidualDimensionBox := pairProfileDimension ω h hh L.val
noncomputable def nondirectFiberInjection (h : Fin 33 → ℕ) (hh : ∀ e,h e=0 ∨ h e=2)
    (b : ResidualDimensionBox) (L : {L : NonDirectPairProfile ω h // nondirectDimension ω h hh L=b}) :
    PairSpanStratum ω h b.1.val (fun i=>(b.2 i).val) := by
  refine ⟨L.val.val,?_,?_⟩
  · exact congrArg (fun b : ResidualDimensionBox=>b.1.val) L.property
  · intro i
    exact congrArg (fun b : ResidualDimensionBox=>(b.2 i).val) L.property
omit [Fintype K] in
 theorem nondirectFiberInjection_injective (h : Fin 33 → ℕ) (hh : ∀ e,h e=0 ∨ h e=2)
    (b : ResidualDimensionBox) : Function.Injective (nondirectFiberInjection ω h hh b) := by
  intro x y hxy
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun X : PairSpanStratum ω h b.1.val (fun i=>(b.2 i).val)=>X.val) hxy
 theorem pairStratum_residual_bound (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D=finrank K E) (h : Fin 33 → ℕ) (hh : ∀ e,h e=0 ∨ h e=2)
    (b : ResidualDimensionBox) (hk : b.1.val≤2*D) (he : ∀ e,h e≤b.1.val)
    (hki : ∀ i,(b.2 i).val≤2*(incidentPairs i).card) (hs : 2*b.1.val+1≤∑ i,(b.2 i).val) :
    (Nat.card (PairSpanStratum ω h b.1.val (fun i=>(b.2 i).val)):ℝ)≤
      2^132*(lagrangianConstant D)^13*(Nat.card (SymplecticLagrangian ω):ℝ)^13*
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
  have hC := pow_nonneg (lagrangianConstant_pos D).le 13
  have hL : 0≤(Nat.card (SymplecticLagrangian ω):ℝ)^13 := pow_nonneg (Nat.cast_nonneg _) _
  have hP : (0:ℝ)≤2^132 := pow_nonneg (by norm_num) _
  refine hf.trans ?_
  exact mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hbpow hC) hL)
    hfexp (Real.rpow_nonneg (le_trans (by norm_num) hq) _) (mul_nonneg (mul_nonneg hP hC) hL)
 theorem nondirectFiber_card_bound (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D=finrank K E) (h : Fin 33 → ℕ) (hh : ∀ e,h e=0 ∨ h e=2)
    (b : ResidualDimensionBox) :
    (Nat.card {L : NonDirectPairProfile ω h // nondirectDimension ω h hh L=b}:ℝ)≤
      2^132*(lagrangianConstant D)^13*(Nat.card (SymplecticLagrangian ω):ℝ)^13*
        (Fintype.card K:ℝ)^(-(D:ℝ)+1575) := by
  classical
  by_cases hex : Nonempty {L : NonDirectPairProfile ω h // nondirectDimension ω h hh L=b}
  · obtain ⟨L⟩ := hex
    let A := pairSpaces ω L.val.val.val
    have hb := (nondirectFiberInjection ω h hh b L).property
    change finrank K ↥(⨆ e,pairSpaces ω L.val.val.val e)=b.1.val ∧
      (∀ i,finrank K (incidentSpan (pairSpaces ω L.val.val.val) i)=(b.2 i).val) at hb
    have hk : b.1.val≤2*D := by
      rw [hD,←hb.1]
      exact Submodule.finrank_le _
    have he : ∀ e,h e≤b.1.val := by
      intro e
      rw [←L.val.val.property e,←hb.1]
      exact Submodule.finrank_mono (le_iSup (pairSpaces ω L.val.val.val) e)
    have hki : ∀ i,(b.2 i).val≤2*(incidentPairs i).card := by
      intro i
      rw [←hb.2 i]
      exact (pairProfile_local_dim_le ω h L.val.val i).trans
        (localPairDim_le h (fun e=>by rcases hh e with he|he <;> omega) i)
    have hs : 2*b.1.val+1≤∑ i,(b.2 i).val := by
      have hs := indexed_strict_span A L.val.property
      change 2*finrank K ↥(⨆ e,pairSpaces ω L.val.val.val e)+1≤
        ∑ i,finrank K (incidentSpan (pairSpaces ω L.val.val.val) i) at hs
      simpa only [hb.1,hb.2] using hs
    have hi : (Nat.card {L : NonDirectPairProfile ω h // nondirectDimension ω h hh L=b}:ℝ)≤
        Nat.card (PairSpanStratum ω h b.1.val (fun i=>(b.2 i).val)) := by
      exact_mod_cast Nat.card_le_card_of_injective _ (nondirectFiberInjection_injective ω h hh b)
    exact hi.trans (pairStratum_residual_bound ω h2 ha hω D hD h hh b hk he hki hs)
  · have : IsEmpty {L : NonDirectPairProfile ω h // nondirectDimension ω h hh L=b} := not_nonempty_iff.mp hex
    rw [Nat.card_of_isEmpty,Nat.cast_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) _)
      (pow_nonneg (lagrangianConstant_pos D).le _)) (pow_nonneg (Nat.cast_nonneg _) _))
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)
 theorem nondirectPairProfile_card_bound (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D=finrank K E) (h : Fin 33 → ℕ) (hh : ∀ e,h e=0 ∨ h e=2) :
    (Nat.card (NonDirectPairProfile ω h):ℝ)≤
      (67*13^13)*2^132*(lagrangianConstant D)^13*(Nat.card (SymplecticLagrangian ω):ℝ)^13*
        (Fintype.card K:ℝ)^(-(D:ℝ)+1575) := by
  have he := Nat.card_congr (Equiv.sigmaFiberEquiv (nondirectDimension ω h hh))
  rw [←he]
  have hb := real_card_sigma_le _ (nondirectFiber_card_bound ω h2 ha hω D hD h hh)
  convert hb using 1
  simp only [ResidualDimensionBox,Nat.card_prod,Nat.card_fin,Nat.card_fun,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  ring
end Nondirect
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
 theorem PointProfile.faceLocal {c : Fin 22 → ℕ} {h : Fin 33 → ℕ} {L : Fin 13 → SymplecticLagrangian ω}
    (hL : PointProfile ω c h L) (j : Fin 22) :
    LocalProfile ω (c j) (h (facePair j 0)) (h (facePair j 1)) (h (facePair j 2))
      (L (faceVertex j 0)) (L (faceVertex j 1)) (L (faceVertex j 2)) := by
  apply PointProfile.local ω hL j (faceVertex j 0) (faceVertex j 1) (faceVertex j 2)
    (facePair j 0) (facePair j 1) (facePair j 2) (faceVertex_correct j)
  · exact faceVertex_pairs j 0
  · exact faceVertex_pairs j 1
  · exact faceVertex_pairs j 2
 theorem PointProfile.geometric (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D=finrank K E) {c : Fin 22 → ℕ} {h : Fin 33 → ℕ}
    {L : Fin 13 → SymplecticLagrangian ω} (hL : PointProfile ω c h L) : GeometricProfile D c h := by
  have hl := hL.faceLocal ω
  have hc (j : Fin 22) : c j≤D := by
    rw [←(hl j).1]
    exact isotropic_finrank_le_half ω hω D hD _
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
end SidorenkoCounterexample
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
noncomputable def residualDirectConstant (D : ℕ) (h : Fin 33 → ℕ) : ℝ :=
  2^(∑ e,h e)*(lagrangianConstant D)^13
noncomputable def residualNondirectConstant (D : ℕ) : ℝ :=
  (67*13^13)*2^132*(lagrangianConstant D)^13
 theorem residualDirectConstant_nonneg (D : ℕ) (h : Fin 33 → ℕ) : 0≤residualDirectConstant D h := by
  exact mul_nonneg (pow_nonneg (by norm_num) _) (pow_nonneg (lagrangianConstant_pos D).le _)
 theorem residualNondirectConstant_nonneg (D : ℕ) : 0≤residualNondirectConstant D := by
  exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg (by norm_num) _))
    (pow_nonneg (by norm_num) _)) (pow_nonneg (lagrangianConstant_pos D).le _)
section Actual
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Fintype K] [Finite E]
variable (ω : LinearMap.BilinForm K E)
omit [Fintype K] in
 theorem pairDimProfile_card_split (h : Fin 33 → ℕ) :
    Nat.card (PairDimProfile ω h)=Nat.card (DirectPairProfile ω h)+Nat.card (NonDirectPairProfile ω h) := by
  classical
  exact (Nat.card_congr (Equiv.sumCompl (fun L : PairDimProfile ω h=>iSupIndep (pairSpaces ω L.val)))).symm.trans Nat.card_sum
 theorem pairDimProfile_residual_card_bound (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D=finrank K E) (h : Fin 33 → ℕ) (hh : ∀ e,h e=0 ∨ h e=2) (hlarge : 33≤D) :
    (Nat.card (PairDimProfile ω h):ℝ)≤(Nat.card (SymplecticLagrangian ω):ℝ)^13*
      (residualDirectConstant D h*(Fintype.card K:ℝ)^(-(∑ e,triangular (h e)))+
        residualNondirectConstant D*(Fintype.card K:ℝ)^(-(D:ℝ)+1575)) := by
  rw [pairDimProfile_card_split,Nat.cast_add]
  have hd := directPairProfile_card_bound ω h2 ha hω D hD h
    ((residual_h_sum_le h hh).trans (by omega))
  have hn := nondirectPairProfile_card_bound ω h2 ha hω D hD h hh
  exact (add_le_add hd hn).trans_eq (by unfold residualDirectConstant residualNondirectConstant;ring)
omit [Fintype K] in
 theorem pointProfile_card_le_pair (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) :
    Nat.card {L : Fin 13 → SymplecticLagrangian ω // PointProfile ω c h L}≤Nat.card (PairDimProfile ω h) := by
  let f : {L : Fin 13 → SymplecticLagrangian ω // PointProfile ω c h L} → PairDimProfile ω h :=
    fun L=>⟨L.val,L.property.2⟩
  exact Nat.card_le_card_of_injective f (fun x y hxy=>Subtype.ext (congrArg (fun L : PairDimProfile ω h=>L.val) hxy))
noncomputable def normalizedPointProfileCount (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) : ℝ :=
  (Nat.card {L : Fin 13 → SymplecticLagrangian ω // PointProfile ω c h L}:ℝ)/(Nat.card (SymplecticLagrangian ω):ℝ)^13
omit [Fintype K] [Finite E] in
 theorem normalizedPointProfileCount_nonneg (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) :
    0≤normalizedPointProfileCount ω c h := by unfold normalizedPointProfileCount; positivity
 theorem lagrangianRealCard_pos (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D=finrank K E) : (0:ℝ)<Nat.card (SymplecticLagrangian ω) := by
  have hq : (0:ℝ)<Fintype.card K := by exact_mod_cast Fintype.card_pos (α:=K)
  exact (pow_pos hq _).trans_le (symplecticLagrangian_card_bounds ω h2 ha hω D hD).1
 theorem normalizedPointProfileCount_exposure (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D=finrank K E) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (hc : ∀ j,c j≤D) :
    normalizedPointProfileCount ω c h≤(fullProfileConstant D)^11*(Fintype.card K:ℝ)^(-profileCost D c h) := by
  apply (div_le_iff₀ (pow_pos (lagrangianRealCard_pos ω h2 ha hω D hD) 13)).mpr
  exact (pointProfile_card_bound ω h2 ha hω D hD c h hc).trans_eq (by ring)
 theorem normalizedPointProfileCount_residual (h2 : (2:K)≠0) (ha : ω.IsAlt) (hω : ω.Nondegenerate)
    (D : ℕ) (hD : 2*D=finrank K E) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ)
    (hh : ∀ e,h e=0 ∨ h e=2) (hlarge : 33≤D) :
    normalizedPointProfileCount ω c h≤
      residualDirectConstant D h*(Fintype.card K:ℝ)^(-(∑ e,triangular (h e)))+
        residualNondirectConstant D*(Fintype.card K:ℝ)^(-(D:ℝ)+1575) := by
  apply (div_le_iff₀ (pow_pos (lagrangianRealCard_pos ω h2 ha hω D hD) 13)).mpr
  have hi : (Nat.card {L : Fin 13 → SymplecticLagrangian ω // PointProfile ω c h L}:ℝ)≤Nat.card (PairDimProfile ω h) :=
    by exact_mod_cast pointProfile_card_le_pair ω c h
  exact (hi.trans (pairDimProfile_residual_card_bound ω h2 ha hω D hD h hh hlarge)).trans_eq (mul_comm _ _)
end Actual
end SidorenkoCounterexample
end OAI

open Module Filter

def TargetH1 : Prop :=
  let t : Fin 22 → Fin 3 → Fin 13 := ![![0,1,3],![0,1,9],![0,2,3],![0,2,9],![1,3,10],![1,7,10],![1,7,12],![1,9,12],![2,3,4],![2,4,9],![3,4,11],![3,10,11],![4,8,9],![4,8,11],![5,6,7],![5,6,11],![5,7,10],![5,10,11],![6,7,12],![6,8,11],![6,8,12],![8,9,12]]
  let p : Fin 22 → Fin 3 → Fin 33 := ![![5,1,6],![5,3,9],![0,1,2],![0,3,4],![6,11,12],![19,11,20],![19,15,23],![9,15,16],![2,7,8],![7,4,10],![8,13,14],![12,13,21],![17,10,18],![17,14,22],![32,25,30],![32,27,29],![25,26,20],![26,27,21],![30,31,23],![28,29,22],![28,31,24],![18,24,16]]
  let sL : Fin 3 → Fin 3 := ![0,0,1]
  let sR : Fin 3 → Fin 3 := ![1,2,2]
  let sep : Fin 33 → ℕ := ![3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,1,1,1,1,1,2,1,1,2,1,1,1,1,1,2]
  let tri (x : ℝ) := x*(x+1)/2
  let Q := {q : ℕ // q.Prime ∧ q ≠ 2}
  let V D (q : Q) := Fin D → ZMod q.1
  let E D q := V D q × Dual (ZMod q.1) (V D q)
  let rk {D} {q : Q} (U : Submodule (ZMod q.1) (E D q)) := finrank (ZMod q.1) U
  let Lag D (q : Q) := {L : Submodule (ZMod q.1) (E D q) // ∀ w, (∀ x ∈ L, w.2 x.1 - x.2 w.1 = 0) ↔ w ∈ L}
  let ptP D (q : Q) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (L : Fin 13 → Lag D q) :=
    (∀ j, rk (((L (t j 0)).1 ⊓ (L (t j 1)).1) ⊓ (L (t j 2)).1) = c j) ∧
    (∀ j k, rk ((L (t j (sL k))).1 ⊓ (L (t j (sR k))).1) = h (p j k))
  let pCnt D (q : Q) c h := (Nat.card {L // ptP D q c h L} : ℝ) / (Nat.card (Lag D q) : ℝ)^13
  let pCost (D : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) :=
    (∑ j, (((D+1)*c j + ∑ k, (h (p j k)-c j+1).choose 2 : ℕ) : ℝ))/2 - (∑ e, (3-(sep e : ℝ))*tri (h e))/6
  ∀ D c h,
    (∀ q, Nonempty {L // ptP D q c h L} → (∀ j, c j ≤ D) ∧ (∀ j k, c j ≤ h (p j k)) ∧ ∀ j, (∑ k, (h (p j k)-c j)) ≤ D-c j) ∧
    ((∀ j, c j ≤ D) → ∃ C₁ ≥ 0, ∀ q, pCnt D q c h ≤ C₁*(q.1 : ℝ)^(-pCost D c h)) ∧
    (33 ≤ D → (∀ e, h e = 0 ∨ h e = 2) → ∃ C₂ ≥ 0, ∀ q, pCnt D q c h ≤ C₂*((q.1 : ℝ)^(-(∑ e, tri (h e))) + (q.1 : ℝ)^(-(D : ℝ)+1575)))

section Leaf1Bridge
open OAI.SidorenkoCounterexample

private noncomputable def lag_equiv_symp (D : ℕ) (q : {q : ℕ // q.Prime ∧ q ≠ 2}) [Fact q.1.Prime] :
    SymplecticLagrangian (canonicalSymplectic (K := ZMod q.1) (V := Fin D → ZMod q.1)) ≃
      {L : Submodule (ZMod q.1) ((Fin D → ZMod q.1) × Dual (ZMod q.1) (Fin D → ZMod q.1)) //
        ∀ w, (∀ x ∈ L, w.2 x.1 - x.2 w.1 = 0) ↔ w ∈ L} :=
  Equiv.subtypeEquivRight (fun L => by
    change (canonicalSymplectic (K := ZMod q.1) (V := Fin D → ZMod q.1)).orthogonal L = L ↔ _
    rw [SetLike.ext_iff]
    rfl)

private theorem facePair_covers :
    ∀ e : Fin 33, ∃ j : Fin 22, ∃ k : Fin 3, facePair j k = e := by decide

private theorem facePair_vertices :
    ∀ j : Fin 22, ∀ k : Fin 3,
      pairVertices (facePair j k) =
        {faceVertex j ((![0, 0, 1] : Fin 3 → Fin 3) k),
         faceVertex j ((![1, 2, 2] : Fin 3 → Fin 3) k)} := by decide

private theorem sep_eq_separationCount :
    (![3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,1,1,1,1,1,2,1,1,2,1,1,1,1,1,2] : Fin 33 → ℕ) =
      separationCount := by
  funext e
  revert e
  decide

theorem leaf1_proved : TargetH1 := by
  intro D c h
  let t : Fin 22 → Fin 3 → Fin 13 := ![![0,1,3],![0,1,9],![0,2,3],![0,2,9],![1,3,10],![1,7,10],![1,7,12],![1,9,12],![2,3,4],![2,4,9],![3,4,11],![3,10,11],![4,8,9],![4,8,11],![5,6,7],![5,6,11],![5,7,10],![5,10,11],![6,7,12],![6,8,11],![6,8,12],![8,9,12]]
  let p : Fin 22 → Fin 3 → Fin 33 := ![![5,1,6],![5,3,9],![0,1,2],![0,3,4],![6,11,12],![19,11,20],![19,15,23],![9,15,16],![2,7,8],![7,4,10],![8,13,14],![12,13,21],![17,10,18],![17,14,22],![32,25,30],![32,27,29],![25,26,20],![26,27,21],![30,31,23],![28,29,22],![28,31,24],![18,24,16]]
  let sL : Fin 3 → Fin 3 := ![0,0,1]
  let sR : Fin 3 → Fin 3 := ![1,2,2]
  have ht_eq : t = faceVertex := rfl
  have hp_eq : p = facePair := rfl
  have hLag_card : ∀ (q : {q : ℕ // q.Prime ∧ q ≠ 2}) [Fact q.1.Prime],
      Nat.card {L : Submodule (ZMod q.1) ((Fin D → ZMod q.1) × Dual (ZMod q.1) (Fin D → ZMod q.1)) //
        ∀ w, (∀ x ∈ L, w.2 x.1 - x.2 w.1 = 0) ↔ w ∈ L} =
      Nat.card (SymplecticLagrangian (canonicalSymplectic (K := ZMod q.1) (V := Fin D → ZMod q.1))) :=
    fun q _ => (Nat.card_congr (lag_equiv_symp D q)).symm
  have hPt_equiv : ∀ (q : {q : ℕ // q.Prime ∧ q ≠ 2}) [Fact q.1.Prime],
      {L : Fin 13 → SymplecticLagrangian (canonicalSymplectic (K := ZMod q.1) (V := Fin D → ZMod q.1)) //
        PointProfile (canonicalSymplectic (K := ZMod q.1) (V := Fin D → ZMod q.1)) c h L} ≃
      {L : Fin 13 → {L : Submodule (ZMod q.1) ((Fin D → ZMod q.1) × Dual (ZMod q.1) (Fin D → ZMod q.1)) //
        ∀ w, (∀ x ∈ L, w.2 x.1 - x.2 w.1 = 0) ↔ w ∈ L} //
        (∀ j, finrank (ZMod q.1) ↥(((L (t j 0)).1 ⊓ (L (t j 1)).1) ⊓ (L (t j 2)).1) = c j) ∧
        (∀ j k, finrank (ZMod q.1) ↥((L (t j (sL k))).1 ⊓ (L (t j (sR k))).1) = h (p j k))} := by
    intro q _
    let e := Equiv.piCongrRight (fun _ : Fin 13 => lag_equiv_symp D q)
    refine e.subtypeEquiv ?_
    intro L
    constructor
    · intro hL
      refine ⟨?_, ?_⟩
      · intro j
        have hj := hL.1 j
        rw [faceVertex_correct j, Finset.inf_insert, Finset.inf_insert, Finset.inf_singleton, ← inf_assoc] at hj
        exact hj
      · intro j k
        have he := hL.2 (p j k)
        rw [hp_eq, facePair_vertices j k, Finset.inf_insert, Finset.inf_singleton] at he
        exact he
    · intro hL
      refine ⟨?_, ?_⟩
      · intro j
        rw [faceVertex_correct j, Finset.inf_insert, Finset.inf_insert, Finset.inf_singleton, ← inf_assoc]
        exact hL.1 j
      · intro e0
        obtain ⟨j, k, rfl⟩ := facePair_covers e0
        rw [facePair_vertices j k, Finset.inf_insert, Finset.inf_singleton]
        exact hL.2 j k
  have hPt_card : ∀ (q : {q : ℕ // q.Prime ∧ q ≠ 2}) [Fact q.1.Prime],
      Nat.card {L : Fin 13 → {L : Submodule (ZMod q.1) ((Fin D → ZMod q.1) × Dual (ZMod q.1) (Fin D → ZMod q.1)) //
        ∀ w, (∀ x ∈ L, w.2 x.1 - x.2 w.1 = 0) ↔ w ∈ L} //
        (∀ j, finrank (ZMod q.1) ↥(((L (t j 0)).1 ⊓ (L (t j 1)).1) ⊓ (L (t j 2)).1) = c j) ∧
        (∀ j k, finrank (ZMod q.1) ↥((L (t j (sL k))).1 ⊓ (L (t j (sR k))).1) = h (p j k))} =
      Nat.card {L : Fin 13 → SymplecticLagrangian (canonicalSymplectic (K := ZMod q.1) (V := Fin D → ZMod q.1)) //
        PointProfile (canonicalSymplectic (K := ZMod q.1) (V := Fin D → ZMod q.1)) c h L} :=
    fun q _ => (Nat.card_congr (hPt_equiv q)).symm
  have hCost_eq :
      profileCost D c h =
        (∑ j, (((D+1)*c j + ∑ k, (h (p j k)-c j+1).choose 2 : ℕ) : ℝ))/2 -
          (∑ e, (3-((![3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,1,1,1,1,1,2,1,1,2,1,1,1,1,1,2] : Fin 33 → ℕ) e : ℝ))*(fun x : ℝ => x*(x+1)/2) (h e))/6 := by
    rw [sep_eq_separationCount]
    rfl
  have hDim : ∀ (q : {q : ℕ // q.Prime ∧ q ≠ 2}),
      letI : Fact q.1.Prime := ⟨q.2.1⟩
      2 * D = finrank (ZMod q.1) ((Fin D → ZMod q.1) × Dual (ZMod q.1) (Fin D → ZMod q.1)) := by
    intro q
    let : Fact q.1.Prime := ⟨q.2.1⟩
    rw [finrank_prod]
    simp
    ring
  have h2_ne : ∀ (q : {q : ℕ // q.Prime ∧ q ≠ 2}),
      letI : Fact q.1.Prime := ⟨q.2.1⟩
      (2 : ZMod q.1) ≠ 0 := by
    intro q
    let : Fact q.1.Prime := ⟨q.2.1⟩
    intro h2z
    have hdvd : q.1 ∣ 2 := (ZMod.natCast_eq_zero_iff 2 q.1).mp (by simpa using h2z)
    have hle : q.1 ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    have hge : 2 ≤ q.1 := q.2.1.two_le
    exact q.2.2 (le_antisymm hle hge)
  refine ⟨?_, ?_, ?_⟩
  · intro q hne
    let : Fact q.1.Prime := ⟨q.2.1⟩
    let : Finite (Dual (ZMod q.1) (Fin D → ZMod q.1)) := Module.finite_of_finite (ZMod q.1)
    obtain ⟨L⟩ := hne
    have hL' := (hPt_equiv q).symm L
    have hg := PointProfile.geometric (canonicalSymplectic (K := ZMod q.1) (V := Fin D → ZMod q.1))
      canonicalSymplectic_alt canonicalSymplectic_nondegenerate D (hDim q) hL'.property
    refine ⟨hg.1, ?_, ?_⟩
    · intro j k
      exact hg.2.1 j k
    · intro j
      have hg2 := hg.2.2 j
      simp only [profileS] at hg2
      exact hg2
  · intro hc
    refine ⟨(fullProfileConstant D) ^ 11, pow_nonneg (fullProfileConstant_pos D).le 11, ?_⟩
    intro q
    let : Fact q.1.Prime := ⟨q.2.1⟩
    let : Finite (Dual (ZMod q.1) (Fin D → ZMod q.1)) := Module.finite_of_finite (ZMod q.1)
    have hE := normalizedPointProfileCount_exposure (canonicalSymplectic (K := ZMod q.1) (V := Fin D → ZMod q.1))
      (h2_ne q) canonicalSymplectic_alt canonicalSymplectic_nondegenerate D (hDim q) c h hc
    change (Nat.card _ : ℝ) / (Nat.card _ : ℝ) ^ 13 ≤ _
    rw [hPt_card q, hLag_card q]
    change normalizedPointProfileCount (canonicalSymplectic (K := ZMod q.1) (V := Fin D → ZMod q.1)) c h ≤ _
    simp only [ZMod.card] at hE
    rw [hCost_eq] at hE
    exact hE
  · intro hD hh
    refine ⟨max (residualDirectConstant D h) (residualNondirectConstant D),
      le_max_of_le_left (residualDirectConstant_nonneg D h), ?_⟩
    intro q
    let : Fact q.1.Prime := ⟨q.2.1⟩
    let : Finite (Dual (ZMod q.1) (Fin D → ZMod q.1)) := Module.finite_of_finite (ZMod q.1)
    have hR := normalizedPointProfileCount_residual (canonicalSymplectic (K := ZMod q.1) (V := Fin D → ZMod q.1))
      (h2_ne q) canonicalSymplectic_alt canonicalSymplectic_nondegenerate D (hDim q) c h hh hD
    change (Nat.card _ : ℝ) / (Nat.card _ : ℝ) ^ 13 ≤ _
    rw [hPt_card q, hLag_card q]
    change normalizedPointProfileCount (canonicalSymplectic (K := ZMod q.1) (V := Fin D → ZMod q.1)) c h ≤ _
    simp only [ZMod.card] at hR
    calc normalizedPointProfileCount (canonicalSymplectic (K := ZMod q.1) (V := Fin D → ZMod q.1)) c h
        ≤ residualDirectConstant D h * (q.1 : ℝ) ^ (-(∑ e, triangular (h e))) +
            residualNondirectConstant D * (q.1 : ℝ) ^ (-(D : ℝ) + 1575) := hR
      _ ≤ max (residualDirectConstant D h) (residualNondirectConstant D) * (q.1 : ℝ) ^ (-(∑ e, triangular (h e))) +
            max (residualDirectConstant D h) (residualNondirectConstant D) * (q.1 : ℝ) ^ (-(D : ℝ) + 1575) := by
          refine add_le_add ?_ ?_
          · exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
          · exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      _ = max (residualDirectConstant D h) (residualNondirectConstant D) *
            ((q.1 : ℝ) ^ (-(∑ e, triangular (h e))) + (q.1 : ℝ) ^ (-(D : ℝ) + 1575)) := by ring

end Leaf1Bridge

theorem OMA.solution : OMA.R_SidorenkoConjecture_sidorenko_conjecture_graphon_R1_H1_R1_H1_R1_H1_R2.H1 := leaf1_proved
