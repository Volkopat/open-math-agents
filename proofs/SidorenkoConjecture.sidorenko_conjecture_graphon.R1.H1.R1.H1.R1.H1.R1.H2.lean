import OMAReductions.R_SidorenkoConjecture_sidorenko_conjecture_graphon_R1_H1_R1_H1_R1_H1_R1
import Mathlib

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
 theorem lift_pair_profile_probability_bound (t₀ t₁ t₂ : ℕ)
    (h₀ : t₀ ≤ finrank K ↥(A₁ ⊓ A₂)) (h₁ : t₁ ≤ finrank K ↥(A₂ ⊓ A₀))
    (h₂ : t₂ ≤ finrank K ↥(A₀ ⊓ A₁)) :
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
  exact planted_nullity_probability_bound A₀ A₁ A₂ t₀ t₁ t₂ h₀ h₁ h₂
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

end OAI

namespace OAI
namespace SidorenkoCounterexample
open Module
section CanonicalCoding
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
abbrev CenterStratum (r : ℕ) := {L : Lagrangian (K := K) (V := V) //
  finrank K ↥(L.val ⊓ verticalSpace (K := K) (V := V)) = r}

end CanonicalCoding
end SidorenkoCounterexample
end OAI

namespace OAI
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
end SidorenkoCounterexample
end OAI

namespace OAI
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

end OAI

namespace OAI
namespace SidorenkoCounterexample
open Module
section FullTripleOrbit
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable (ω : LinearMap.BilinForm K E)
abbrev SymplecticLagrangian := {L : Submodule K E // ω.orthogonal L = L}

end FullTripleOrbit
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

end GenericCounts
end SidorenkoCounterexample
end OAI

namespace OAI

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
end OAI

namespace OAI
namespace SidorenkoCounterexample

def pairVertices : Fin 33 → Finset (Fin 13) := ![{0,2}, {0,3}, {2,3}, {0,9}, {2,9}, {0,1}, {1,3}, {2,4}, {3,4}, {1,9}, {4,9}, {1,10}, {3,10}, {3,11}, {4,11}, {1,12}, {9,12}, {4,8}, {8,9}, {1,7}, {7,10}, {10,11}, {8,11}, {7,12}, {8,12}, {5,7}, {5,10}, {5,11}, {6,8}, {6,11}, {6,7}, {6,12}, {5,6}]
def facePair : Fin 22 → Fin 3 → Fin 33 := ![![5, 1, 6], ![5, 3, 9], ![0, 1, 2], ![0, 3, 4], ![6, 11, 12], ![19, 11, 20], ![19, 15, 23], ![9, 15, 16], ![2, 7, 8], ![7, 4, 10], ![8, 13, 14], ![12, 13, 21], ![17, 10, 18], ![17, 14, 22], ![32, 25, 30], ![32, 27, 29], ![25, 26, 20], ![26, 27, 21], ![30, 31, 23], ![28, 29, 22], ![28, 31, 24], ![18, 24, 16]]
 theorem pairVertices_card : ∀ e, (pairVertices e).card = 2 := by decide
 theorem pairVertices_injective : Function.Injective pairVertices := by decide
 theorem facePair_injective : ∀ j, Function.Injective (facePair j) := by decide

end SidorenkoCounterexample
end OAI

namespace OAI
namespace SidorenkoCounterexample
def faceVertex : Fin 22 → Fin 3 → Fin 13 := ![![0, 1, 3], ![0, 1, 9], ![0, 2, 3], ![0, 2, 9], ![1, 3, 10], ![1, 7, 10], ![1, 7, 12], ![1, 9, 12], ![2, 3, 4], ![2, 4, 9], ![3, 4, 11], ![3, 10, 11], ![4, 8, 9], ![4, 8, 11], ![5, 6, 7], ![5, 6, 11], ![5, 7, 10], ![5, 10, 11], ![6, 7, 12], ![6, 8, 11], ![6, 8, 12], ![8, 9, 12]]
 theorem faceVertex_injective : ∀ j, Function.Injective (faceVertex j) := by decide

end SidorenkoCounterexample
end OAI

namespace OAI
namespace SidorenkoCounterexample
def incidentPairs (i : Fin 13) : Finset (Fin 33) := Finset.univ.filter (fun e => i∈pairVertices e)
 theorem incidentPairs_card_le : ∀ i, (incidentPairs i).card≤6 := by decide

end SidorenkoCounterexample
end OAI

namespace OAI
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
end OAI

namespace OAI
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
end OAI

namespace OAI
namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section ActualProfile
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Finite E]
variable (ω : LinearMap.BilinForm K E)
noncomputable def actualSingularTail (r : ℕ) (A : SymplecticLagrangian ω)
    (T : Fin 22 → Finset (Fin 3)) : ℝ := by
  classical
  let := Fintype.ofFinite (Fin 13 → SymplecticLagrangian ω)
  exact (∑ L : Fin 13 → SymplecticLagrangian ω,
    if ∃ e, finrank K ↥((pairVertices e).inf fun i => (L i).val : Submodule K E) ≠ 0
    then ∏ j, activeFaceDensity ω r A (fun i => L (faceVertex j i)) (T j) else 0) /
      (Nat.card (SymplecticLagrangian ω) : ℝ)^13

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

theorem radicalQuotientForm_isSymm (B : LinearMap.BilinForm K V) (hB : B.IsSymm) :
    (radicalQuotientForm B hB).IsSymm := by
  constructor
  intro x y
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    induction y using Submodule.Quotient.induction_on with
    | H y => exact hB.eq x y

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

theorem discriminantSign_sq (B : LinearMap.BilinForm K V) (hB : B.IsSymm) :
    discriminantSign B hB ^ 2 = 1 := by
  apply quadraticChar_sq_one
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

def MainClaim : Prop := ∃ n : ℕ, 0 < n ∧ ∃ G : SimpleGraph (Fin n),
    (∃ u v, G.Adj u v) ∧ homDensity H G < (edgeDensity G) ^ 66

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

theorem layerMass_pos {r : ℕ} (hr : 0 < r) (hrD : r ≤ D)
    (hK : ringChar K ≠ 2) {ξ : ℤ} (hξ : ξ = 1 ∨ ξ = -1) :
    0 < layerMass K D r ξ := by
  apply div_pos
  · exact_mod_cast (signedLayer_nonempty K D hr hrD hK hξ).card_pos
  · exact_mod_cast Fintype.card_pos (α := SymMatrix K D)

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

def corners : Finset (Fin 13 × Fin 22) :=
  Finset.univ.filter fun c => c.1 ∈ faces c.2

def modelPointPairs : Finset (Finset (Fin 13)) :=
  Finset.univ.biUnion fun j => (faces j).powersetCard 2

abbrev ModelPair := {e : Finset (Fin 13) // e ∈ modelPointPairs}

noncomputable def layerCorrelation (D : ℕ) (q : OddPrime)
    (B : Finset (Fin 13 × Fin 22)) (ξ : Fin 13 × Fin 22 → ℤ) : ℝ :=
  uniformMean fun xy : (Fin 13 → SymMatrix (ZMod q.val) D) ×
      (Fin 22 → SymMatrix (ZMod q.val) D) =>
    ∏ c ∈ B, rankKernel (ZMod q.val) D (D / 2) (ξ c) (xy.1 c.1 - xy.2 c.2)

noncomputable def signModelCorrelation (D : ℕ) (q : OddPrime)
    (B : Finset (Fin 13 × Fin 22)) (ξ : Fin 13 × Fin 22 → ℤ) : ℝ := by
  classical
  let c₀ : ℝ := quadraticChar (ZMod q.val) ((-1) ^ (D / 2))
  exact uniformMean fun η : ModelPair → Bool =>
    ∏ j : Fin 22, ∏ e : ModelPair,
      if e.val ⊆ faces j ∧ (∀ i ∈ e.val, (i,j) ∈ B) then
        1 + c₀ * (if η e then 1 else -1) * ∏ i ∈ e.val, (ξ (i,j) : ℝ)
      else 1

def RankLayerLimit : Prop := ∃ D₀ : ℕ, 0 < D₀ ∧
  ∀ D : ℕ, D₀ ≤ D → Even D →
    ∀ B : Finset (Fin 13 × Fin 22), B ⊆ corners →
      ∀ ξ : Fin 13 × Fin 22 → ℤ, (∀ c ∈ B, ξ c = 1 ∨ ξ c = -1) →
        Filter.Tendsto (fun q : OddPrime =>
          layerCorrelation D q B ξ - signModelCorrelation D q B ξ)
          primeInfinity (nhds 0)

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

 theorem symmetricSingularProb_nonneg (n : ℕ) : 0 ≤ symmetricSingularProb (K := K) n := by
  apply uniformMean_nonneg; intro M; split <;> norm_num

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

 theorem symmetricSignProb_nonneg (n : ℕ) (ξ : ℤ) : 0 ≤ symmetricSignProb (K := K) n ξ :=
  uniformMean_nonneg fun _ => characterSignIndicator_nonneg ..

 theorem symmetricSignProb_le_one (n : ℕ) (ξ : ℤ) : symmetricSignProb (K := K) n ξ ≤ 1 :=
  uniformMean_bound fun _ => characterSignIndicator_le_one ..

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

theorem discriminantSign_add (A B : LinearMap.BilinForm K V)
    (hA : A.IsSymm) (hB : B.IsSymm) (hS : (A+B).Nondegenerate)
    (hdim : finrank K (V ⧸ A.ker) + finrank K (V ⧸ B.ker) = finrank K V) :
    discriminantSign (A+B) (hA.add hB) = discriminantSign A hA * discriminantSign B hB := by
  classical
  let AQ := radicalQuotientForm A hA
  let BQ := radicalQuotientForm B hB
  let C := orthogonalSumForm AQ BQ
  have hCs : C.IsSymm := orthogonalSumForm_isSymm _ _
    (radicalQuotientForm_isSymm A hA) (radicalQuotientForm_isSymm B hB)
  have hC : C.Nondegenerate := orthogonalSumForm_nondegenerate _ _
    (radicalQuotientForm_nondegenerate A hA) (radicalQuotientForm_nondegenerate B hB)
  let f : V →ₗ[K] (V ⧸ A.ker) × (V ⧸ B.ker) := A.ker.mkQ.prod B.ker.mkQ
  have hfi : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    apply bot_unique
    intro x hx
    change f x = 0 at hx
    have ha : A x = 0 := (Submodule.Quotient.mk_eq_zero A.ker).mp (congrArg Prod.fst hx)
    have hb : B x = 0 := (Submodule.Quotient.mk_eq_zero B.ker).mp (congrArg Prod.snd hx)
    apply hS.1
    intro y
    simp only [LinearMap.add_apply, ha, hb, LinearMap.zero_apply, add_zero]
  have hfs : Function.Surjective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
      simpa only [Module.finrank_prod] using hdim.symm)).mp hfi
  have he : C.compl₁₂ f f = A+B := by ext x y; rfl
  let b := Module.finBasis K (V ⧸ A.ker)
  let c := Module.finBasis K (V ⧸ B.ker)
  have hs := discriminantSign_pullback C hCs hC f hfs (b.prod c)
  simp only [he] at hs
  rw [hs]
  change quadraticChar K ((orthogonalSumForm AQ BQ).toMatrix (b.prod c)).det = _
  rw [orthogonalSumForm_matrix, Matrix.det_fromBlocks_zero₂₁, map_mul]
  rfl

end SumForms
section PairSign
variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]
variable [Fintype K] [DecidableEq K]

theorem half_rank_pair_sign (r : ℕ) (hdim : Fintype.card n = 2*r)
    (A B : Matrix n n K) (hAs : A.IsSymm) (hBs : B.IsSymm)
    (hB : B.det ≠ 0) (hAr : A.rank = r) (hCr : (A-B).rank = r) :
    quadraticChar K B.det = quadraticChar K ((-1 : K)^r) *
      discriminantSign A.toBilin' (Matrix.isSymm_toBilin'_iff_isSymm.mpr hAs) *
      discriminantSign (A-B).toBilin' (Matrix.isSymm_toBilin'_iff_isSymm.mpr (hAs.sub hBs)) := by
  classical
  have hAs' := Matrix.isSymm_toBilin'_iff_isSymm.mpr hAs
  have hCs' := Matrix.isSymm_toBilin'_iff_isSymm.mpr (hBs.sub hAs)
  have hadd : A.toBilin' + (B-A).toBilin' = B.toBilin' := by
    rw [← map_add, add_sub_cancel]
  have hBs' := Matrix.isSymm_toBilin'_iff_isSymm.mpr hBs
  have hBnd : B.toBilin'.Nondegenerate :=
    LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mpr hB
  have hdim' : finrank K ((n → K) ⧸ A.toBilin'.ker) +
      finrank K ((n → K) ⧸ (B-A).toBilin'.ker) = finrank K (n → K) := by
    rw [matrix_radical_quotient_rank, matrix_radical_quotient_rank,
      show B-A = -(A-B) by abel, matrix_rank_neg, hAr, hCr, Module.finrank_pi, hdim]
    omega
  have hs := discriminantSign_add A.toBilin' (B-A).toBilin' hAs' hCs'
    (hadd.symm ▸ hBnd) hdim'
  simp only [hadd] at hs
  have hb := discriminantSign_nondegenerate B.toBilin' hBs' hBnd (Pi.basisFun K n)
  have hb' : discriminantSign B.toBilin' hBs' = quadraticChar K B.det := by
    simpa only [show B.toBilin'.toMatrix (Pi.basisFun K n) = B from
      LinearMap.BilinForm.toMatrix'_toBilin' B] using hb
  rw [hb'] at hs
  have hn := discriminantSign_neg (A-B).toBilin'
    (Matrix.isSymm_toBilin'_iff_isSymm.mpr (hAs.sub hBs))
  rw [matrix_radical_quotient_rank, hCr] at hn
  have hneg : -(A-B).toBilin' = (B-A).toBilin' := by
    rw [show B-A = -(A-B) by abel, map_neg]
  simp only [hneg] at hn
  rw [hs, hn]
  ring
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

omit [Fintype K] [DecidableEq K] [FiniteDimensional K V] in
theorem formSingularIndicator_nonneg (Q : SymForm K V) : 0 ≤ formSingularIndicator Q := by
  unfold formSingularIndicator; split <;> norm_num

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

theorem formSignMean_error (hK : ringChar K ≠ 2) (hd : 0 < finrank K V)
    {ξ : ℤ} (hξ : ξ=1 ∨ ξ = -1) :
    |uniformMean (formSignIndicator (K := K) (V := V) ξ)-1/2| ≤
      (finrank K V : ℝ)/(Fintype.card K : ℝ) := by
  have h := uniformMean_equiv (symFormMatrix K V)
    (fun M : SymMatrix K (finrank K V) => characterSignIndicator ξ M.val.det)
  have he : uniformMean (formSignIndicator (K := K) (V := V) ξ) =
      symmetricSignProb (K := K) (finrank K V) ξ := by
    unfold symmetricSignProb
    rw [←h]; apply uniformMean_congr
    intro Q; exact formSignIndicator_matrix (Module.finBasis K V) hξ Q
  rw [he]; exact symmetricSignProb_error _ hd hK hξ

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

 theorem split_form_normalized {K E : Type*} [Field K] [Fintype K] [DecidableEq K]
    [AddCommGroup E] [Module K E] [FiniteDimensional K E]
    (B : LinearMap.BilinForm K E) (hs : B.IsSymm) (hB : B.Nondegenerate)
    (hK : ringChar K ≠ 2) (r : ℕ) (hd : finrank K E=2*r)
    (hc : discriminantSign B hs = quadraticChar K ((-1 : K)^r)) :
    (Nat.card (SymplecticLagrangian B) : ℝ)/(Fintype.card K : ℝ)^r.choose 2 =
      orthogonalFactor r (Fintype.card K) := by
  rw [split_form_card B hs hB hK r hd hc]
  exact maxOrthogonal_normalized hK r
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

noncomputable def centerPredicateEquiv (Q : Matrix n n K) (hQ : Q.IsSymm) (hdet : Q.det≠0)
    (P : Submodule K (n → K) → Prop) :
    {A : CenterProjection Q // P A.val.toLin'.range} ≃
    {U : Submodule K (n → K) // (Q.toBilin'.restrict U).Nondegenerate ∧ P U} :=
  ((centerSubspaceEquiv Q hQ hdet).subtypeEquiv (fun A => by
    rw [centerSubspaceEquiv_val])).trans
    (Equiv.subtypeSubtypeEquivSubtypeInter _ _)
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

theorem uniformMean_coordinate [Nonempty A] (i : I) (f : A → ℝ) :
    uniformMean (fun x : I → A => f (x i))=uniformMean f := by
  classical
  rw [←uniformMean_equiv (Equiv.piSplitAt i (fun _ : I => A)).symm,uniformMean_prod]
  simp only [Function.comp_def,Equiv.piSplitAt,Equiv.coe_fn_symm_mk]
  simp [uniformMean_const]

theorem uniformMean_update [Nonempty A] (i : I) (f : (I → A) → ℝ) :
    uniformMean f=uniformMean (fun x : I → A => uniformMean (fun a : A => f (Function.update x i a))) := by
  classical
  let e := Equiv.funSplitAt i A
  have he (x : A × ({j : I // j≠i} → A)) (a : A) :
      Function.update (e.symm x) i a=e.symm (a,x.2) := by
    ext j
    by_cases hj : j=i
    · subst j; simp [e,Equiv.funSplitAt,Equiv.piSplitAt]
    · simp [e,Equiv.funSplitAt,Equiv.piSplitAt,hj]
  rw [←uniformMean_equiv e.symm,uniformMean_prod]
  conv_rhs => rw [←uniformMean_equiv e.symm,uniformMean_prod]
  simp only [Function.comp_def,he]
  rw [uniformMean_const]
  exact uniformMean_swap _

theorem uniformMean_mul_right (f : A → ℝ) (c : ℝ) :
    uniformMean (fun a => f a*c)=uniformMean f*c := by
  simpa only [mul_comm] using uniformMean_mul c f

theorem uniformMean_ite_le [Nonempty A] (P : A → Prop) [DecidablePred P]
    (f : A → ℝ) (b : ℝ) (hf : ∀ a, P a → f a≤b) (hb : 0≤b) :
    uniformMean (fun a => if P a then f a else 0)≤b := by
  apply uniformMean_bound
  intro a
  split_ifs with h
  · exact hf a h
  · exact hb
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
theorem pairLocal_nonneg (r : ℕ) (ξ ζ : ℤ) (B : SymMatrix K (2*r)) : 0≤pairLocal r ξ ζ B :=
  uniformMean_nonneg fun _ => mul_nonneg (rankKernel_nonneg ..) (rankKernel_nonneg ..)
theorem tripleLocal_nonneg (r : ℕ) (ξ ζ θ : ℤ) (B C : SymMatrix K (2*r)) :
    0≤tripleLocal r ξ ζ θ B C :=
  uniformMean_nonneg fun _ => mul_nonneg
    (mul_nonneg (rankKernel_nonneg ..) (rankKernel_nonneg ..)) (rankKernel_nonneg ..)
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

 theorem char_conj (ψ : AddChar K ℂ) (a : K) :
    star (ψ a) = (ψ a)⁻¹ := (Complex.inv_eq_conj (ψ.norm_apply a)).symm

omit [Module K V] in
 theorem character_differencing (ψ : AddChar K ℂ) (f : V → K) :
    ‖∑ x, ψ (f x)‖ ^ 2 = ‖∑ u, ∑ z, ψ (f (z+u) - f z)‖ := by
  classical
  have h : (∑ u, ∑ z, ψ (f (z+u) - f z)) =
      (∑ x, ψ (f x)) * star (∑ x, ψ (f x)) := by
    simp only [AddChar.map_sub_eq_div, div_eq_mul_inv, ← char_conj]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul]
    have ht (z : V) : (∑ u, ψ (f (z+u))) = ∑ x, ψ (f x) :=
      Fintype.sum_equiv (Equiv.addLeft z) _ _ (fun _ => rfl)
    simp only [ht, ← Finset.mul_sum, star_sum]
  rw [h, norm_mul, norm_star, pow_two]

omit [Fintype K] in
 theorem linear_character_sum_zero (ψ : AddChar K ℂ) (hψ : ψ ≠ 0)
    (f : V →ₗ[K] K) (hf : f ≠ 0) : ∑ x, ψ (f x) = 0 := by
  classical
  have hsurj : Function.Surjective f := by
    have hex : ∃ x, f x ≠ 0 := by
      by_contra! h
      exact hf (LinearMap.ext h)
    obtain ⟨x, hx⟩ := hex
    intro a
    refine ⟨(a / f x) • x, ?_⟩
    simp [hx]
  change ∑ x, (ψ.compAddMonoidHom f.toAddMonoidHom) x = 0
  apply AddChar.sum_eq_zero_iff_ne_zero.mpr
  intro heq
  apply hψ
  ext a
  obtain ⟨x, rfl⟩ := hsurj a
  exact congrArg (fun χ : AddChar V ℂ => χ x) heq

omit [Fintype K] [Fintype V] in

 theorem quadratic_difference (B : LinearMap.BilinForm K V) (hB : B.IsSymm)
    (l : V →ₗ[K] K) (c : K) (z u : V) :
    (B (z+u) (z+u) + l (z+u) + c) - (B z z + l z + c) =
      B u u + l u + (2 : K) * B u z := by
  simp only [map_add, LinearMap.add_apply, hB.eq z u]
  ring

 theorem quadratic_gauss_bound (ψ : AddChar K ℂ) (hψ : ψ ≠ 0)
    (hodd : (2 : K) ≠ 0) (B : LinearMap.BilinForm K V) (hB : B.IsSymm)
    (l : V →ₗ[K] K) (c : K) :
    ‖∑ x, ψ (B x x + l x + c)‖ ^ 2 ≤
      (Fintype.card V : ℝ) * Nat.card B.ker := by
  classical
  rw [character_differencing]
  simp only [quadratic_difference B hB, AddChar.map_add_eq_mul]
  have hi (u : V) : (∑ z, ψ ((2:K) * B u z)) =
      if u ∈ B.ker then (Fintype.card V : ℂ) else 0 := by
    by_cases hu : u ∈ B.ker
    · have hz : B u = 0 := LinearMap.mem_ker.mp hu
      simp [hu, hz]
    · rw [if_neg hu]
      exact linear_character_sum_zero ψ hψ ((2:K) • B u) (by
        intro heq
        apply hu
        apply LinearMap.mem_ker.mpr
        exact (smul_eq_zero.mp heq).resolve_left hodd)
  simp only [← Finset.mul_sum, hi]
  calc
    ‖∑ u, ψ (B u u) * ψ (l u) *
        (if u ∈ B.ker then (Fintype.card V : ℂ) else 0)‖ ≤
        ∑ u, ‖ψ (B u u) * ψ (l u) *
        (if u ∈ B.ker then (Fintype.card V : ℂ) else 0)‖ := norm_sum_le _ _
    _ = (Fintype.card V : ℝ) * Nat.card B.ker := by
      simp only [norm_mul, AddChar.norm_apply, one_mul]
      simp only [apply_ite norm, Complex.norm_natCast, norm_zero]
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero,
        Finset.sum_const, nsmul_eq_mul]
      rw [mul_comm]
      congr 1
      rw [Nat.card_eq_fintype_card]
      simp [Fintype.card_subtype]

 theorem normalized_quadratic_gauss_bound (ψ : AddChar K ℂ) (hψ : ψ ≠ 0)
    (hodd : (2 : K) ≠ 0) (B : LinearMap.BilinForm K V) (hB : B.IsSymm)
    (l : V →ₗ[K] K) (c : K) :
    ‖(Fintype.card V : ℂ)⁻¹ * ∑ x, ψ (B x x + l x + c)‖ ^ 2 ≤
      1 / (Fintype.card K : ℝ) ^ finrank K B.range := by
  classical
  have h := quadratic_gauss_bound ψ hψ hodd B hB l c
  have hv : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  have hk : (0 : ℝ) < Fintype.card K := by exact_mod_cast Fintype.card_pos
  have hc : (Fintype.card V : ℝ) =
      (Fintype.card K : ℝ) ^ finrank K B.range * Nat.card B.ker := by
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := K) (V := V),
      Module.card_eq_pow_finrank (K := K) (V := B.ker)]
    push_cast
    rw [← pow_add, B.finrank_range_add_finrank_ker]
  simp only [norm_mul, norm_inv, Complex.norm_natCast, mul_pow]
  calc
    (Fintype.card V : ℝ)⁻¹ ^ 2 * ‖∑ x, ψ (B x x + l x + c)‖ ^ 2 ≤
      (Fintype.card V : ℝ)⁻¹ ^ 2 *
        ((Fintype.card V : ℝ) * Nat.card B.ker) :=
      mul_le_mul_of_nonneg_left h (sq_nonneg _)
    _ = 1 / (Fintype.card K : ℝ) ^ finrank K B.range := by
      have hp := pow_pos hk (finrank K B.range)
      field_simp
      nlinarith [hc]

end Gauss
section Fourier
variable {K ι : Type*} [Field K] [Fintype K] [Fintype ι] [DecidableEq ι] [DecidableEq K]

noncomputable def coordinatePairing (v : ι → K) : (ι → K) →ₗ[K] K where
  toFun t := t ⬝ᵥ v
  map_add' := fun _ _ => add_dotProduct _ _ _
  map_smul' := fun _ _ => smul_dotProduct _ _ _

 theorem coordinate_character_sum (ψ : AddChar K ℂ) (hψ : ψ ≠ 0)
    (v : ι → K) :
    ∑ t : ι → K, ψ (t ⬝ᵥ v) = if v = 0 then (Fintype.card (ι → K) : ℂ) else 0 := by
  classical
  split_ifs with hv
  · simp [hv]
  · apply linear_character_sum_zero ψ hψ (coordinatePairing v)
    intro h
    apply hv
    apply dotProduct_eq_zero_iff.mp
    intro t
    simpa [coordinatePairing, dotProduct_comm] using
      congrArg (fun f : (ι → K) →ₗ[K] K => f t) h

noncomputable def finiteFourier (ψ : AddChar K ℂ) (μ : (ι → K) → ℝ)
    (t : ι → K) : ℂ := ∑ x, (μ x : ℂ) * ψ (t ⬝ᵥ x)

 theorem finite_parseval (ψ : AddChar K ℂ) (hψ : ψ ≠ 0)
    (μ : (ι → K) → ℝ) :
    ∑ t, ‖finiteFourier ψ μ t‖ ^ 2 =
      (Fintype.card (ι → K) : ℝ) * ∑ x, (μ x)^2 := by
  classical
  apply Complex.ofReal_injective
  have hn (z : ℂ) : ((‖z‖^2 : ℝ) : ℂ) = z * star z := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]; rfl
  have hs (x : ℝ) : star (x : ℂ) = x := by simp
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, hn, finiteFourier,
    star_sum, star_mul, hs,
    char_conj, Finset.sum_mul, Finset.mul_sum]
  have he (x y : ι → K) :
      (∑ t, (μ x : ℂ) * ψ (t ⬝ᵥ x) * ((ψ (t ⬝ᵥ y))⁻¹ * μ y)) =
      (μ x : ℂ) * μ y * (if x = y then (Fintype.card (ι → K) : ℂ) else 0) := by
    calc
      _ = (μ x : ℂ) * μ y * ∑ t, ψ (t ⬝ᵥ (x-y)) := by
        simp only [dotProduct_sub, AddChar.map_sub_eq_div, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t _
        ring
      _ = _ := by rw [coordinate_character_sum ψ hψ]; simp only [sub_eq_zero]
  rw [Finset.sum_comm]
  conv_lhs => enter [2, x]; rw [Finset.sum_comm]
  simp only [he]
  simp [Finset.sum_ite_eq', pow_two, mul_comm, mul_assoc]

 theorem finiteFourier_sub_uniform (ψ : AddChar K ℂ) (hψ : ψ ≠ 0)
    (μ : (ι → K) → ℝ) (hμ : ∑ x, μ x = 1) (t : ι → K) :
    finiteFourier ψ (fun x => μ x - (Fintype.card (ι → K) : ℝ)⁻¹) t =
      if t = 0 then 0 else finiteFourier ψ μ t := by
  classical
  have hc : (Fintype.card (ι → K) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp only [finiteFourier, Complex.ofReal_sub, sub_mul, Finset.sum_sub_distrib,
    ← Finset.mul_sum, Complex.ofReal_inv, Complex.ofReal_natCast]
  have hs : ∑ x : ι → K, ψ (t ⬝ᵥ x) =
      if t = 0 then (Fintype.card (ι → K) : ℂ) else 0 := by
    simpa only [dotProduct_comm] using coordinate_character_sum ψ hψ t
  rw [hs]
  split_ifs with ht
  · simp [ht, ← Complex.ofReal_sum, hμ]
  · simp

 theorem finite_fourier_l1_bound (ψ : AddChar K ℂ) (hψ : ψ ≠ 0)
    (μ : (ι → K) → ℝ) (hμ : ∑ x, μ x = 1) :
    (∑ x, |μ x - (Fintype.card (ι → K) : ℝ)⁻¹|)^2 ≤
      ∑ t, if t = 0 then 0 else ‖finiteFourier ψ μ t‖^2 := by
  classical
  have hp := finite_parseval ψ hψ (fun x => μ x - (Fintype.card (ι → K) : ℝ)⁻¹)
  simp only [finiteFourier_sub_uniform ψ hψ μ hμ] at hp
  have hs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun _ : ι → K => (1:ℝ))
    (fun x => |μ x - (Fintype.card (ι → K) : ℝ)⁻¹|)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one, sq_abs] at hs
  rw [← hp] at hs
  simpa only [apply_ite norm, norm_zero, ite_pow, zero_pow (by decide : 2 ≠ 0)] using hs

 theorem finite_fourier_l1_of_uniform_bound (ψ : AddChar K ℂ) (hψ : ψ ≠ 0)
    (μ : (ι → K) → ℝ) (hμ : ∑ x, μ x = 1) (ε : ℝ) (hε : 0 ≤ ε)
    (hf : ∀ t ≠ 0, ‖finiteFourier ψ μ t‖ ^ 2 ≤ ε) :
    (∑ x, |μ x - (Fintype.card (ι → K) : ℝ)⁻¹|)^2 ≤
      (Fintype.card (ι → K) : ℝ) * ε := by
  classical
  refine (finite_fourier_l1_bound ψ hψ μ hμ).trans ?_
  calc
    _ ≤ ∑ _t : ι → K, ε := by
      apply Finset.sum_le_sum
      intro t _
      split_ifs with ht
      · exact hε
      · exact hf t ht
    _ = _ := by simp

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

noncomputable def uniformLaw (f : Ω → ι → K) (x : ι → K) : ℝ :=
  (Fintype.card Ω : ℝ)⁻¹ * ∑ v, if f v = x then 1 else 0

omit [Field K] in
 theorem uniformLaw_sum (f : Ω → ι → K) : ∑ x, uniformLaw f x = 1 := by
  classical
  simp only [uniformLaw, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  simp

omit [Field K] [Nonempty Ω] in
 theorem uniformLaw_average (f : Ω → ι → K) (g : (ι → K) → ℝ) :
    ∑ x, uniformLaw f x * g x = (Fintype.card Ω : ℝ)⁻¹ * ∑ v, g (f v) := by
  classical
  simp only [uniformLaw, mul_assoc, ← Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  simp

omit [Nonempty Ω] in
 theorem finiteFourier_uniformLaw (ψ : AddChar K ℂ) (f : Ω → ι → K) (t : ι → K) :
    finiteFourier ψ (uniformLaw f) t =
      (Fintype.card Ω : ℂ)⁻¹ * ∑ v, ψ (t ⬝ᵥ f v) := by
  classical
  simp only [finiteFourier, uniformLaw, Complex.ofReal_mul, Complex.ofReal_inv,
    Complex.ofReal_natCast, Complex.ofReal_sum, mul_assoc, ← Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro v _
  simp only [apply_ite, Complex.ofReal_one, Complex.ofReal_zero, ite_mul, one_mul, zero_mul]
  simp

variable {V : Type*} [AddCommGroup V] [Module K V] [Fintype V]

noncomputable def quadraticMap (B : ι → LinearMap.BilinForm K V)
    (l : ι → V →ₗ[K] K) (c : ι → K) (v : V) (i : ι) : K :=
  B i v v + l i v + c i

omit [Fintype K] [DecidableEq ι] [DecidableEq K] [Fintype V] in
 theorem quadraticMap_frequency (B : ι → LinearMap.BilinForm K V)
    (l : ι → V →ₗ[K] K) (c t : ι → K) (v : V) :
    t ⬝ᵥ quadraticMap B l c v =
      (∑ i, t i • B i) v v + (∑ i, t i • l i) v + ∑ i, t i * c i := by
  simp [dotProduct, quadraticMap, Finset.sum_add_distrib, mul_add]

 theorem quadraticMap_fourier_bound (ψ : AddChar K ℂ) (hψ : ψ ≠ 0)
    (hodd : (2:K) ≠ 0) (B : ι → LinearMap.BilinForm K V)
    (hB : ∀ i, (B i).IsSymm) (l : ι → V →ₗ[K] K) (c t : ι → K) :
    ‖finiteFourier ψ (uniformLaw (quadraticMap B l c)) t‖^2 ≤
      1 / (Fintype.card K : ℝ) ^ finrank K (∑ i, t i • B i).range := by
  rw [finiteFourier_uniformLaw]
  simp only [quadraticMap_frequency]
  apply normalized_quadratic_gauss_bound ψ hψ hodd
  constructor
  intro x y
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [(hB i).eq]

 theorem quadraticMap_joint_l1_bound (ψ : AddChar K ℂ) (hψ : ψ ≠ 0)
    (hodd : (2:K) ≠ 0) (B : ι → LinearMap.BilinForm K V)
    (hB : ∀ i, (B i).IsSymm) (l : ι → V →ₗ[K] K) (c : ι → K)
    (hrank : ∀ t : ι → K, t ≠ 0 →
      Fintype.card ι + 1 ≤ finrank K (∑ i, t i • B i).range) :
    (∑ x, |uniformLaw (quadraticMap B l c) x -
      (Fintype.card (ι → K) : ℝ)⁻¹|)^2 ≤ 1 / (Fintype.card K : ℝ) := by
  have hq : (1:ℝ) ≤ Fintype.card K := by exact_mod_cast Fintype.card_pos (α := K)
  have hf (t : ι → K) (ht : t ≠ 0) :
      ‖finiteFourier ψ (uniformLaw (quadraticMap B l c)) t‖^2 ≤
        1 / (Fintype.card K : ℝ)^(Fintype.card ι+1) := by
    refine (quadraticMap_fourier_bound ψ hψ hodd B hB l c t).trans ?_
    exact one_div_le_one_div_of_le (pow_pos (by linarith) _)
      (pow_le_pow_right₀ hq (hrank t ht))
  have hh := finite_fourier_l1_of_uniform_bound ψ hψ _
    (uniformLaw_sum (quadraticMap B l c)) _ (by positivity) hf
  convert hh using 1
  rw [Fintype.card_fun, Nat.cast_pow, pow_succ]
  have hq0 : (Fintype.card K : ℝ) ≠ 0 := by linarith
  field_simp

end Fourier
end SidorenkoCounterexample

namespace SidorenkoCounterexample
open scoped BigOperators
open Module
section SignMoments
variable {K ι : Type*} [Field K] [Fintype K] [DecidableEq K]
  [Fintype ι] [DecidableEq ι]

noncomputable def characterProduct (x : ι → K) : ℝ := ∏ i, (quadraticChar K (x i) : ℝ)

omit [DecidableEq ι] in
 theorem characterProduct_abs_le (x : ι → K) : |characterProduct x| ≤ 1 := by
  rw [characterProduct, Finset.abs_prod]
  exact Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun i _ => by
    have h := quadraticChar_dichotomy (F := K) (a := x i)
    by_cases hx : x i = 0
    · simp [hx]
    · rcases h hx with h | h <;> simp [h])

 theorem characterProduct_sum [Nonempty ι] (hodd : ringChar K ≠ 2) :
    ∑ x : ι → K, characterProduct x = 0 := by
  rw [show (∑ x : ι → K, characterProduct x) =
    ∏ _i : ι, ∑ a : K, (quadraticChar K a : ℝ) from (Fintype.prod_sum (fun (_i : ι) (a : K) => (quadraticChar K a : ℝ))).symm]
  have hz : ∑ a : K, (quadraticChar K a : ℝ) = 0 := by
    exact_mod_cast quadraticChar_sum_zero hodd
  rw [hz]
  simp

omit [Field K] [DecidableEq K] in
 theorem bounded_test_l1 (μ ν : (ι → K) → ℝ) (g : (ι → K) → ℝ)
    (hg : ∀ x, |g x| ≤ 1) :
    |(∑ x, μ x * g x) - ∑ x, ν x * g x| ≤ ∑ x, |μ x-ν x| := by
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  apply Finset.sum_le_sum
  intro x _
  rw [← sub_mul, abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (hg x)

variable {V : Type*} [AddCommGroup V] [Module K V] [Fintype V]

 theorem quadraticMap_character_moment [Nonempty ι]
    (ψ : AddChar K ℂ) (hψ : ψ ≠ 0) (hodd : (2:K) ≠ 0)
    (B : ι → LinearMap.BilinForm K V) (hB : ∀ i, (B i).IsSymm)
    (l : ι → V →ₗ[K] K) (c : ι → K)
    (hrank : ∀ t : ι → K, t ≠ 0 →
      Fintype.card ι + 1 ≤ finrank K (∑ i, t i • B i).range) :
    ((Fintype.card V : ℝ)⁻¹ * ∑ v, characterProduct (quadraticMap B l c v))^2 ≤
      1 / (Fintype.card K : ℝ) := by
  have hc : ringChar K ≠ 2 := by
    intro h
    apply hodd
    simpa using (ringChar.spec K 2).mpr (by rw [h])
  have hz : ∑ x : ι → K, (Fintype.card (ι → K) : ℝ)⁻¹ * characterProduct x = 0 := by
    rw [← Finset.mul_sum, characterProduct_sum hc, mul_zero]
  have hb := bounded_test_l1 (uniformLaw (quadraticMap B l c))
    (fun _ => (Fintype.card (ι → K) : ℝ)⁻¹) characterProduct characterProduct_abs_le
  rw [uniformLaw_average, hz, sub_zero] at hb
  have hf := quadraticMap_joint_l1_bound ψ hψ hodd B hB l c hrank
  have hh := ((sq_le_sq₀ (abs_nonneg _) (Finset.sum_nonneg (fun _ _ => abs_nonneg _))).mpr hb).trans hf
  simpa only [sq_abs] using hh

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

omit [Fintype K] [DecidableEq K] in
theorem matrix_form_rank (M : Matrix (Fin N) (Fin N) K) :
    finrank K M.toBilin'.range=M.rank := by
  rw [←matrix_radical_quotient_rank]
  exact M.toBilin'.quotKerEquivRange.finrank_eq.symm

omit [Fintype K] [DecidableEq K] in
theorem schur_polynomial (M : SymMatrix K N) (z w : Fin N → K) (a : K) :
    a-(z-w) ⬝ᵥ M.val⁻¹.mulVec (z-w) =
      (-M.val⁻¹.toBilin') z z + (2 • (M.val⁻¹.toBilin' w)) z +
        (a-M.val⁻¹.toBilin' w w) := by
  have hs := Matrix.isSymm_toBilin'_iff_isSymm.mpr M.property.inv
  have he : (z-w) ⬝ᵥ M.val⁻¹.mulVec (z-w) = M.val⁻¹.toBilin' (z-w) (z-w) := by
    rw [matrix_bilin_eval,M.property.inv,dotProduct_comm]
  rw [he]
  simp only [map_sub,LinearMap.sub_apply,LinearMap.neg_apply,LinearMap.smul_apply]
  rw [hs.eq z w]
  ring

omit [Fintype K] [DecidableEq K] [DecidableEq ι] [Nonempty ι] in
theorem inverse_form_span_rank (M : ι → SymMatrix K N) (t : ι → K) :
    finrank K (∑ i, t i • (-((M i).val⁻¹.toBilin'))).range =
      (∑ i, t i • (M i).val⁻¹).rank := by
  have he : (∑ i, t i • (-((M i).val⁻¹.toBilin'))) =
      (-(∑ i, t i • (M i).val⁻¹)).toBilin' := by
    simp only [map_neg,map_sum,map_smul]
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    simp
  rw [he,matrix_form_rank,matrix_rank_neg]

theorem schur_sign_moment (hodd : ringChar K≠2)
    (M : ι → SymMatrix K N) (hM : ∀ i, (M i).val.det≠0)
    (w : ι → Fin N → K) (a : ι → K)
    (hrank : ∀ t : ι → K, t≠0 →
      Fintype.card ι+1≤(∑ i, t i • (M i).val⁻¹).rank) :
    (uniformMean (fun z : Fin N → K =>
      ∏ i, (quadraticChar K (symmetricBorder (M i) (z-w i) (a i)).val.det : ℝ)))^2 ≤
      1/(Fintype.card K : ℝ) := by
  obtain ⟨ψ,hψ⟩ := (AddChar.exists_apply_ne_zero (a := (1 : K))).mpr one_ne_zero
  have hp : ψ≠0 := by intro h; apply hψ; simp [h]
  have htwo : (2 : K)≠0 := by
    exact Ring.two_ne_zero hodd
  let B : ι → LinearMap.BilinForm K (Fin N → K) := fun i => -(M i).val⁻¹.toBilin'
  let l : ι → (Fin N → K) →ₗ[K] K := fun i => 2 • ((M i).val⁻¹.toBilin' (w i))
  let c : ι → K := fun i => a i-(M i).val⁻¹.toBilin' (w i) (w i)
  have hB : ∀ i, (B i).IsSymm := fun i =>
    (Matrix.isSymm_toBilin'_iff_isSymm.mpr (M i).property.inv).neg
  have hb := quadraticMap_character_moment ψ hp htwo B hB l c (fun t ht => by
    rw [inverse_form_span_rank M t]; exact hrank t ht)
  have hb' : (uniformMean (fun z => characterProduct (quadraticMap B l c z)))^2 ≤
      1/(Fintype.card K : ℝ) := by
    simpa only [uniformMean,div_eq_mul_inv,mul_comm] using hb
  have he (z : Fin N → K) : (∏ i, (quadraticChar K
      (symmetricBorder (M i) (z-w i) (a i)).val.det : ℝ)) =
      characterProduct (fun i => (M i).val.det) * characterProduct (quadraticMap B l c z) := by
    unfold characterProduct
    rw [←Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    rw [symmetricBorder_det _ _ _ (hM i),map_mul,Int.cast_mul,schur_polynomial]
    rfl
  simp_rw [he]
  rw [uniformMean_mul,mul_pow]
  have hc := characterProduct_abs_le (fun i => (M i).val.det)
  have hc2 : characterProduct (fun i => (M i).val.det)^2≤1 := by
    simpa only [sq_abs,one_pow] using (sq_le_sq₀ (abs_nonneg _) zero_le_one).mpr hc
  exact (mul_le_of_le_one_left (sq_nonneg _) hc2).trans hb'
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

omit [Fintype K] [DecidableEq K] [DecidableEq I] in
theorem matrix_combination_form_rank (t : I → K) (Q : I → SymMatrix K N) :
    finrank K (weightedCombination t (fun i => matrixFormEquiv N (Q i))).val.range =
      (∑ i, t i • (Q i).val).rank := by
  have he : (weightedCombination t (fun i => matrixFormEquiv N (Q i))).val =
      (∑ i, t i • (Q i).val).toBilin' := by
    simp only [weightedCombination, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply]
    change (symmetricFormSubmodule (K := K) (V := Fin N → K)).subtype
      (∑ i, t i • matrixFormEquiv N (Q i)) = _
    calc
      _ = ∑ i, (symmetricFormSubmodule (K := K) (V := Fin N → K)).subtype
          (t i • matrixFormEquiv N (Q i)) := map_sum _ _ _
      _ = _ := by
        simp only [map_sum,map_smul]
        apply Finset.sum_congr rfl
        intro i _
        exact map_smul (symmetricFormSubmodule (K := K) (V := Fin N → K)).subtype (t i) (matrixFormEquiv N (Q i))
  rw [he,matrix_form_rank]

theorem matrix_low_rank_span_bound (s : ℕ) (hs : s ≤ N) :
    uniformMean (fun Q : I → SymMatrix K N => if ∃ t : I → K, t≠0 ∧
      (∑ i, t i • (Q i).val).rank ≤ s then 1 else 0)  ≤ 
      (Fintype.card K : ℝ)^(Fintype.card I) *
        (2^(N-s)/(Fintype.card K : ℝ)^((N-s+1).choose 2)) := by
  classical
  let e : (I → SymMatrix K N) ≃ (I → SymForm K (Fin N → K)) :=
    Equiv.piCongrRight (fun _ => matrixFormEquiv N)
  have hp (Q : I → SymMatrix K N) : (∃ t : I → K, t≠0 ∧
      (∑ i, t i • (Q i).val).rank ≤ s) ↔
      ∃ t : I → K, t≠0 ∧ finrank K (weightedCombination t (e Q)).val.range ≤ s := by
    apply exists_congr
    intro t
    rw [show finrank K (weightedCombination t (e Q)).val.range =
      (∑ i, t i • (Q i).val).rank from matrix_combination_form_rank t Q]
  simp_rw [hp]
  rw [←Function.comp_def (fun Q : I → SymForm K (Fin N → K) => if ∃ t : I → K, t≠0 ∧
    finrank K (weightedCombination t Q).val.range ≤ s then (1 : ℝ) else 0) e,
    uniformMean_equiv e,uniformMean_indicator]
  simpa only [Nat.card_eq_fintype_card,Module.finrank_fin_fun] using
    (symmetric_low_rank_span_bound (K := K) (V := Fin N → K) (ι := I) s (by simpa using hs))

noncomputable def goodMinors (M : I → SymMatrix K N) : Prop :=
  (∀ i, (M i).val.det≠0) ∧ ∀ t : I → K, t≠0 →
    Fintype.card I+1 ≤ (∑ i, t i • (M i).val⁻¹).rank

noncomputable def minorBadBound (N s : ℕ) (q : ℝ) : ℝ :=
  (s : ℝ)*N/q + q^s*(2^(N-s)/q^((N-s+1).choose 2))

theorem badMinors_bound (hN : Fintype.card I ≤ N) :
    uniformMean (fun M : I → SymMatrix K N => if goodMinors M then 0 else 1)  ≤ 
      minorBadBound N (Fintype.card I) (Fintype.card K) := by
  classical
  let P (Q : I → SymMatrix K N) : Prop := ∃ t : I → K, t≠0 ∧
    (∑ i, t i • (Q i).val).rank ≤ Fintype.card I
  let e : (I → SymMatrix K N) ≃ (I → SymMatrix K N) :=
    Equiv.piCongrRight (fun _ => symmetricInverseEquiv N)
  have he (M : I → SymMatrix K N) (hM : ∀ i, (M i).val.det≠0) (i : I) :
      (e M i).val=(M i).val⁻¹ := by simp [e,symmetricInverseEquiv,symmetricInverse,hM i]
  have hp (M : I → SymMatrix K N) :
      (if goodMinors M then (0 : ℝ) else 1)  ≤ 
        (∑ i, if (M i).val.det=0 then 1 else 0)+(if P (e M) then 1 else 0) := by
    by_cases hg : goodMinors M
    · simp only [if_pos hg]; positivity
    · simp only [if_neg hg]
      by_cases hM : ∀ i, (M i).val.det≠0
      · have hr : P (e M) := by
          simp only [goodMinors,not_and,not_forall] at hg
          obtain ⟨t,ht⟩ := hg hM
          obtain ⟨htt1,htt2⟩ := ht
          refine ⟨t,htt1,?_⟩
          simp only [he M hM]
          omega
        simp only [if_pos hr]
        have : (0 : ℝ) ≤ ∑ i, if (M i).val.det=0 then (1 : ℝ) else 0 := by positivity
        linarith
      · push Not at hM
        obtain ⟨i,hi⟩ := hM
        have hb : (1 : ℝ) ≤ ∑ j, if (M j).val.det=0 then (1 : ℝ) else 0 := by
          simpa only [hi,ite_true] using Finset.single_le_sum
            (fun j (_ : j ∈ Finset.univ) => by positivity : ∀ j ∈ Finset.univ, 0 ≤ (if (M j).val.det=0 then (1 : ℝ) else 0))
            (Finset.mem_univ i)
        exact hb.trans (le_add_of_nonneg_right (by positivity))
  apply (uniformMean_mono hp).trans
  rw [uniformMean_add,uniformMean_sum]
  have hs (i : I) : uniformMean (fun M : I → SymMatrix K N => if (M i).val.det=0 then (1 : ℝ) else 0)  ≤ 
      (N : ℝ)/(Fintype.card K : ℝ) := by
    rw [uniformMean_coordinate i (fun A : SymMatrix K N => if A.val.det = 0 then (1 : ℝ) else 0)]
    exact symmetricSingularProb_bound (K := K) N
  have hb : uniformMean (fun M => if P (e M) then (1 : ℝ) else 0)  ≤ 
      (Fintype.card K : ℝ)^(Fintype.card I) *
        (2^(N-Fintype.card I)/(Fintype.card K : ℝ)^((N-Fintype.card I+1).choose 2)) := by
    rw [←Function.comp_def (fun M => if P M then (1 : ℝ) else 0) e,uniformMean_equiv]
    exact matrix_low_rank_span_bound (Fintype.card I) hN
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hs i)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hsum
  unfold minorBadBound
  rw [←mul_div_assoc] at hsum
  exact add_le_add hsum hb
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

omit [Fintype K] [DecidableEq K] in
theorem symmetricBorder_sub {N : ℕ} (W V : SymMatrix K N) (z w : Fin N → K) (a b : K) :
    symmetricBorder W z a-symmetricBorder V w b=symmetricBorder (W-V) (z-w) (a-b) := by
  apply Subtype.ext
  ext i j
  change borderRaw W.val z a (borderIndex N i) (borderIndex N j)-
    borderRaw V.val w b (borderIndex N i) (borderIndex N j)=
      borderRaw (W-V).val (z-w) (a-b) (borderIndex N i) (borderIndex N j)
  cases borderIndex N i <;> cases borderIndex N j <;> rfl

theorem uniformMean_pi_prod {A B : Type*} [Fintype A] [Fintype B]
    (f : (I → A × B) → ℝ) :
    uniformMean f=uniformMean fun a : I → A => uniformMean fun b : I → B => f (fun i => (a i,b i)) := by
  rw [←uniformMean_equiv (Equiv.arrowProdEquivProdArrow I (fun _ => A) (fun _ => B)).symm,
    uniformMean_prod]
  rfl

omit [DecidableEq K] in
theorem uniformMean_bordered (N : ℕ) (f : (I → SymMatrix K (N+1)) → ℝ) :
    uniformMean f=uniformMean (fun W : I → SymMatrix K N =>
      uniformMean (fun z : I → (Fin N → K) => uniformMean (fun a : I → K =>
        f (fun i => symmetricBorder (W i) (z i) (a i))))) := by
  rw [←uniformMean_equiv (Equiv.piCongrRight (fun _ : I => (symmetricBorderEquiv (K := K) N).symm))]
  rw [uniformMean_pi_prod]
  apply uniformMean_congr
  intro W
  rw [uniformMean_pi_prod]
  rfl
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

noncomputable def starSign (v : I) (k : J → I) (W : I → SymMatrix K N)
    (z : I → (Fin N → K)) (a : I → K) : ℝ :=
  ∏ j, (quadraticChar K (symmetricBorder (W v-W (k j)) (z v-z (k j)) (a v-a (k j))).val.det : ℝ)

omit [Fintype I] [DecidableEq I] [DecidableEq J] [Nonempty J] in
theorem starSign_abs_le (v : I) (k : J → I) (W : I → SymMatrix K N)
    (z : I → (Fin N → K)) (a : I → K) : |starSign v k W z a| ≤ 1 :=
  characterProduct_abs_le _

omit [Fintype I] in
theorem starSign_update_bound (hK : ringChar K≠2) (v : I) (k : J → I)
    (hv : ∀ j, k j≠v) (W : I → SymMatrix K N) (z : I → (Fin N → K)) (a : I → K)
    (hW : goodMinors (fun j => W v-W (k j))) :
    |uniformMean (fun z' => starSign v k W (Function.update z v z') a)| ≤
      Real.sqrt (1/(Fintype.card K : ℝ)) := by
  have he (z' : Fin N → K) : starSign v k W (Function.update z v z') a =
      ∏ j, (quadraticChar K (symmetricBorder (W v-W (k j)) (z'-z (k j)) (a v-a (k j))).val.det : ℝ) := by
    simp only [starSign,Function.update_self,Function.update_of_ne (hv _)]
  simp_rw [he]
  apply (Real.le_sqrt (abs_nonneg _) (by positivity)).mpr
  rw [sq_abs]
  exact schur_sign_moment hK (fun j => W v-W (k j)) hW.1 (fun j => z (k j))
    (fun j => a v-a (k j)) hW.2

omit [Fintype I] in
theorem testedStar_update_bound (hK : ringChar K≠2) (v : I) (k : J → I)
    (hv : ∀ j, k j≠v) (W : I → SymMatrix K N) (z : I → (Fin N → K)) (a : I → K)
    (R : (I → (Fin N → K)) → ℝ) (hR : ∀ z, |R z| ≤ 1)
    (hRi : ∀ z', R (Function.update z v z')=R z) :
    |uniformMean (fun z' => R (Function.update z v z') * starSign v k W (Function.update z v z') a)| ≤
      Real.sqrt (1/(Fintype.card K : ℝ)) +
        (if goodMinors (fun j => W v-W (k j)) then 0 else 1) := by
  simp_rw [hRi]
  rw [uniformMean_mul,abs_mul]
  by_cases hW : goodMinors (fun j => W v-W (k j))
  · rw [if_pos hW,add_zero]
    exact (mul_le_of_le_one_left (abs_nonneg _) (hR z)).trans (starSign_update_bound hK v k hv W z a hW)
  · rw [if_neg hW]
    apply le_trans _ (le_add_of_nonneg_left (Real.sqrt_nonneg _))
    apply (mul_le_of_le_one_left (abs_nonneg _) (hR z)).trans
    exact (abs_uniformMean_le _).trans (uniformMean_bound fun z' => starSign_abs_le v k W _ a)

theorem testedStar_mean_bound (hK : ringChar K≠2) (v : I) (k : J → I)
    (hk : Function.Injective k) (hv : ∀ j, k j≠v) (hN : Fintype.card J ≤ N)
    (R : (I → SymMatrix K N) → (I → (Fin N → K)) → (I → K) → ℝ)
    (hR : ∀ W z a, |R W z a| ≤ 1)
    (hRi : ∀ W z a z', R W (Function.update z v z') a=R W z a) :
    |uniformMean (fun W => uniformMean fun a => uniformMean fun z => R W z a * starSign v k W z a)| ≤
       Real.sqrt (1/(Fintype.card K : ℝ)) + minorBadBound N (Fintype.card J) (Fintype.card K) := by
  have hpoint (W : I → SymMatrix K N) (a : I → K) :
      |uniformMean (fun z => R W z a * starSign v k W z a)| ≤
        Real.sqrt (1/(Fintype.card K : ℝ)) +
          (if goodMinors (fun j => W v-W (k j)) then 0 else 1) := by
    rw [uniformMean_update v]
    apply (abs_uniformMean_le _).trans
    exact uniformMean_bound (fun z => testedStar_update_bound hK v k hv W z a (fun z => R W z a)
      (fun z => hR W z a) (hRi W z a))
  apply (abs_uniformMean_le _).trans
  calc
    _ ≤ uniformMean (fun W : I → SymMatrix K N => Real.sqrt (1/(Fintype.card K : ℝ)) +
        (if goodMinors (fun j => W v-W (k j)) then 0 else 1)) := by
      apply uniformMean_mono
      intro W
      exact (abs_uniformMean_le _).trans (uniformMean_bound (hpoint W))
    _ = Real.sqrt (1/(Fintype.card K : ℝ)) +
        uniformMean (fun M : J → SymMatrix K N => if goodMinors M then 0 else 1) := by
      rw [uniformMean_add,uniformMean_const]
      congr 1
      exact uniformMean_starDifference (K := K) v k hk hv
        (fun M : J → SymMatrix K N => if goodMinors M then 0 else 1)
    _ ≤ _ := add_le_add le_rfl (badMinors_bound (K := K) hN)
end StarMoment
end SidorenkoCounterexample

end

section

namespace SidorenkoCounterexample
open Module Classical
open scoped BigOperators

def pairLeft : Fin 33 → Fin 13 := ![0,0,2,0,2,0,1,2,3,1,4,1,3,3,4,1,9,4,8,1,7,10,8,7,8,5,5,5,6,6,6,6,5]
def pairRight : Fin 33 → Fin 13 := ![2,3,3,9,9,1,3,4,4,9,9,10,10,11,11,12,12,8,9,7,10,11,11,12,12,7,10,11,8,11,7,12,6]
theorem pair_endpoints : ∀ e, pairVertices e={pairLeft e,pairRight e} := by decide
theorem pair_endpoints_ne : ∀ e, pairLeft e≠pairRight e := by decide

def pairOther (v : Fin 13) (e : Fin 33) : Fin 13 := if pairLeft e=v then pairRight e else pairLeft e

theorem pairOther_ne (v : Fin 13) (e : Fin 33) (_hv : v∈pairVertices e) : pairOther v e≠v := by
  unfold pairOther
  split_ifs with h
  · simpa only [h] using (pair_endpoints_ne e).symm
  · exact h

theorem pair_vertices_other (v : Fin 13) (e : Fin 33) (hv : v∈pairVertices e) :
    pairVertices e={v,pairOther v e} := by
  rw [pair_endpoints] at hv ⊢
  simp only [Finset.mem_insert,Finset.mem_singleton] at hv
  unfold pairOther
  split_ifs with h
  · rw [h]
  · rcases hv with h' | h'
    · exact (h h'.symm).elim
    · rw [h']; exact Finset.pair_comm _ _

def selectedIncident (F : Finset (Fin 33)) (v : Fin 13) : Finset (Fin 33) :=
  F.filter (fun e => v∈pairVertices e)

theorem selectedIncident_card (F : Finset (Fin 33)) (v : Fin 13) : (selectedIncident F v).card ≤ 6 := by
  apply le_trans (Finset.card_le_card ?_) (incidentPairs_card_le v)
  intro e he
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp he).2⟩

theorem pairOther_injective (F : Finset (Fin 33)) (v : Fin 13) :
    Function.Injective (fun e : selectedIncident F v => pairOther v e.val) := by
  intro e f h
  dsimp only at h
  apply Subtype.ext
  apply pairVertices_injective
  rw [pair_vertices_other v e.val (Finset.mem_filter.mp e.property).2,
    pair_vertices_other v f.val (Finset.mem_filter.mp f.property).2,h]

section Signs
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] {D : ℕ}
noncomputable def pairSign (X : Fin 13 → SymMatrix K D) (e : Fin 33) : ℝ :=
  quadraticChar K (X (pairLeft e)-X (pairRight e)).val.det

theorem pairSign_abs_le (X : Fin 13 → SymMatrix K D) (e : Fin 33) : |pairSign X e| ≤ 1 := by
  unfold pairSign
  by_cases h : (X (pairLeft e)-X (pairRight e)).val.det=0
  · rw [h]; norm_num
  · rcases quadraticChar_dichotomy (F := K) h with h | h <;> rw [h] <;> norm_num

omit [Fintype K] [DecidableEq K] in
theorem determinant_difference_even (hD : Even D) (A B : SymMatrix K D) :
    (A-B).val.det=(B-A).val.det := by
  have he : A-B= -(B-A) := by abel
  rw [he,Submodule.coe_neg,Matrix.det_neg,Fintype.card_fin,hD.neg_pow,one_pow,one_mul]

theorem pairSign_other (hD : Even D) (X : Fin 13 → SymMatrix K D)
    (v : Fin 13) (e : Fin 33) (hv : v∈pairVertices e) :
    pairSign X e=quadraticChar K (X v-X (pairOther v e)).val.det := by
  rw [pair_endpoints] at hv
  simp only [Finset.mem_insert,Finset.mem_singleton] at hv
  unfold pairSign pairOther
  split_ifs with h
  · rw [h]
  · rcases hv with h' | h'
    · exact (h h'.symm).elim
    · rw [h',determinant_difference_even hD]

theorem pairSign_product_abs_le (F : Finset (Fin 33)) (X : Fin 13 → SymMatrix K D) :
    |∏ e∈F, pairSign X e| ≤ 1 := by
  rw [Finset.abs_prod]
  exact Finset.prod_le_one (fun e _ => abs_nonneg _) (fun e _ => pairSign_abs_le X e)
end Signs
end SidorenkoCounterexample

end

section

namespace SidorenkoCounterexample
open Module Classical Filter
open scoped BigOperators
section Moment
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] {N : ℕ}

noncomputable def nonincidentProduct (F : Finset (Fin 33)) (v : Fin 13)
    (W : Fin 13 → SymMatrix K N) (z : Fin 13 → (Fin N → K)) (a : Fin 13 → K) : ℝ :=
  ∏ e∈F\selectedIncident F v, pairSign (fun i => symmetricBorder (W i) (z i) (a i)) e

theorem nonincidentProduct_abs_le (F : Finset (Fin 33)) (v : Fin 13)
    (W : Fin 13 → SymMatrix K N) (z : Fin 13 → (Fin N → K)) (a : Fin 13 → K) :
    |nonincidentProduct F v W z a| ≤ 1 := pairSign_product_abs_le _ _

theorem nonincidentProduct_update (F : Finset (Fin 33)) (v : Fin 13)
    (W : Fin 13 → SymMatrix K N) (z : Fin 13 → (Fin N → K)) (a : Fin 13 → K)
    (z' : Fin N → K) : nonincidentProduct F v W (Function.update z v z') a=
      nonincidentProduct F v W z a := by
  apply Finset.prod_congr rfl
  intro e he
  obtain ⟨heF,heN⟩ := Finset.mem_sdiff.mp he
  have hv : v∉pairVertices e := by
    intro h
    exact heN (Finset.mem_filter.mpr ⟨heF,h⟩)
  have hl : pairLeft e≠v := by
    intro h; apply hv; rw [pair_endpoints, h]; simp
  have hr : pairRight e≠v := by
    intro h; apply hv; rw [pair_endpoints, h]; simp
  simp only [pairSign,Function.update_of_ne hl,Function.update_of_ne hr]

theorem pairSign_product_split (hN : Even (N+1)) (F : Finset (Fin 33)) (v : Fin 13)
    (W : Fin 13 → SymMatrix K N) (z : Fin 13 → (Fin N → K)) (a : Fin 13 → K) :
    (∏ e∈F, pairSign (fun i => symmetricBorder (W i) (z i) (a i)) e)=
      nonincidentProduct F v W z a * starSign v
        (fun e : selectedIncident F v => pairOther v e.val) W z a := by
  have he : starSign v (fun e : selectedIncident F v => pairOther v e.val) W z a=
      ∏ e∈selectedIncident F v, pairSign (fun i => symmetricBorder (W i) (z i) (a i)) e := by
    rw [←Finset.prod_coe_sort]
    apply Finset.prod_congr rfl
    intro e _
    rw [pairSign_other hN _ v e.val (Finset.mem_filter.mp e.property).2]
    rw [symmetricBorder_sub]
  rw [he]
  exact (Finset.prod_sdiff (Finset.filter_subset _ _)).symm

theorem pairSign_moment_bound (hK : ringChar K≠2) (hN : Even (N+1))
    (F : Finset (Fin 33)) (v : Fin 13) (hne : (selectedIncident F v).Nonempty)
    (hc : (selectedIncident F v).card ≤ N) :
    |uniformMean (fun X : Fin 13 → SymMatrix K (N+1) => ∏ e∈F, pairSign X e)| ≤
      Real.sqrt (1/(Fintype.card K : ℝ)) +
        minorBadBound N (selectedIncident F v).card (Fintype.card K) := by
  let : Nonempty (selectedIncident F v) := ⟨⟨hne.choose,hne.choose_spec⟩⟩
  rw [uniformMean_bordered]
  simp_rw [pairSign_product_split hN F v]
  have he (W : Fin 13 → SymMatrix K N) := uniformMean_swap
    (fun z a => nonincidentProduct F v W z a * starSign v
      (fun e : selectedIncident F v => pairOther v e.val) W z a)
  simp_rw [he]
  simpa only [Fintype.card_coe] using testedStar_mean_bound hK v _ (pairOther_injective F v)
    (fun e => pairOther_ne v e.val (Finset.mem_filter.mp e.property).2)
    (by simpa using hc) (nonincidentProduct F v)
    (nonincidentProduct_abs_le F v) (nonincidentProduct_update F v)
end Moment

 theorem minorBadBound_tendsto (N s : ℕ) (h : s<(N-s+1).choose 2) :
    Tendsto (minorBadBound N s) atTop (nhds 0) := by
  have ha : Tendsto (fun q : ℝ => (s : ℝ)*N/q) atTop (nhds 0) := by
    simpa only [mul_zero,div_eq_mul_inv] using
      (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul ((s : ℝ)*N)
  have hb : Tendsto (fun q : ℝ => q^s*(2^(N-s)/q^((N-s+1).choose 2))) atTop (nhds 0) := by
    have ht := (inverse_power_tendsto_zero ((N-s+1).choose 2-s) (by omega)).const_mul ((2 : ℝ)^(N-s))
    simp only [mul_zero] at ht
    apply ht.congr' (eventually_atTop.mpr ⟨1,fun q hq => ?_⟩)
    have hq0 : q≠0 := by linarith
    have hn : (N-s+1).choose 2=s+((N-s+1).choose 2-s) := by omega
    rw [hn,pow_add]
    field_simp
    congr 1; omega
  change Tendsto (fun q : ℝ => (s : ℝ)*N/q + q^s*(2^(N-s)/q^((N-s+1).choose 2))) atTop (nhds 0)
  simpa only [add_zero] using ha.add hb

 theorem sign_moment_dimension (N s : ℕ) (hN : 11≤N) (hs : s≤6) :
    s≤N ∧ s<(N-s+1).choose 2 := by
  have hd : 6≤N-s+1 := by omega
  have hc := Nat.choose_le_choose 2 hd
  rw [show (6:ℕ).choose 2=15 by decide] at hc
  omega

theorem pairSign_moment_tendsto (D : ℕ) (hD : Even D) (hbig : 12≤D)
    (F : Finset (Fin 33)) (hF : F.Nonempty) :
    Tendsto (fun q : OddPrime => uniformMean (fun X : Fin 13 → SymMatrix (ZMod q.val) D =>
      ∏ e∈F, pairSign X e)) primeInfinity (nhds 0) := by
  obtain ⟨e,he⟩ := hF
  let v := pairLeft e
  have hi : (selectedIncident F v).Nonempty := by
    refine ⟨e,Finset.mem_filter.mpr ⟨he,?_⟩⟩
    rw [pair_endpoints]; exact Finset.mem_insert_self _ _
  have hn : D=D-1+1 := by omega
  have hn' : Even (D-1+1) := hn ▸ hD
  have hc := sign_moment_dimension (D-1) (selectedIncident F v).card (by omega) (selectedIncident_card F v)
  have ht : Tendsto (fun q : OddPrime => Real.sqrt (1/(q.val : ℝ)) +
      minorBadBound (D-1) (selectedIncident F v).card q.val) primeInfinity (nhds 0) := by
    have ha := Real.continuous_sqrt.continuousAt.tendsto.comp
      ((inverse_power_tendsto_zero 1 (by omega)).comp primeInfinity_real_tendsto)
    simpa only [pow_one,Real.sqrt_zero,add_zero,Function.comp_def] using ha.add
      ((minorBadBound_tendsto (D-1) _ hc.2).comp primeInfinity_real_tendsto)
  apply squeeze_zero_norm (fun q => ?_) ht
  rw [Real.norm_eq_abs]
  conv_lhs => rw [hn]
  simpa only [ZMod.card] using pairSign_moment_bound
    (K := ZMod q.val) (by simpa only [ZMod.ringChar_zmod_n] using q.property.2) hn' F v hi hc.1
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

theorem product_difference_unit (s : Finset I) (f g : I → ℝ)
    (hf : ∀ i∈s, |f i|≤1) (hg : ∀ i∈s, |g i|≤1) :
    |(∏ i∈s, f i)-(∏ i∈s, g i)| ≤ ∑ i∈s, |f i-g i| := by
  simpa only [one_pow,one_mul] using product_difference_bound s f g (le_refl 1) hf hg
end Product
section Mean
variable {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A]
omit [Fintype I] [DecidableEq I] in
theorem uniformMean_finset_sum (s : Finset I) (f : I → A → ℝ) :
    uniformMean (fun a => ∑ i∈s, f i a)=∑ i∈s, uniformMean (f i) := by
  unfold uniformMean
  rw [Finset.sum_comm,Finset.sum_div]

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

theorem pairBool_moment_error (F : Finset (Fin 33)) :
    |uniformMean (fun X : Fin 13 → SymMatrix K D => ∏ e∈F, boolSign (pairBool X e))-
      uniformMean (fun X : Fin 13 → SymMatrix K D => ∏ e∈F, pairSign X e)| ≤
        (F.card : ℝ)*((D : ℝ)/Fintype.card K) := by
  rw [←uniformMean_sub]
  apply (abs_uniformMean_le _).trans
  calc
    _ ≤ uniformMean (fun X : Fin 13 → SymMatrix K D => ∑ e∈F, pairSingular X e) := by
      apply uniformMean_mono
      intro X
      exact (product_difference_unit F _ _ (by simp) (fun e _ => pairSign_abs_le X e)).trans
        (Finset.sum_le_sum fun e _ => pairBool_error X e)
    _ = ∑ e∈F, uniformMean (fun X : Fin 13 → SymMatrix K D => pairSingular X e) := uniformMean_finset_sum _ _
    _ ≤ ∑ _e∈F, (D : ℝ)/Fintype.card K := Finset.sum_le_sum fun e _ => pairSingular_mean e
    _ = _ := by simp
end Pair

theorem pairBool_moment_tendsto (D : ℕ) (hD : Even D) (hbig : 12≤D)
    (F : Finset (Fin 33)) (hF : F.Nonempty) :
    Tendsto (fun q : OddPrime => uniformMean (fun X : Fin 13 → SymMatrix (ZMod q.val) D =>
      ∏ e∈F, boolSign (pairBool X e))) primeInfinity (nhds 0) := by
  have hm := pairSign_moment_tendsto D hD hbig F hF
  have hb : Tendsto (fun q : OddPrime => (F.card : ℝ)*((D : ℝ)/(q.val : ℝ))) primeInfinity (nhds 0) := by
    simpa only [mul_zero,Function.comp_def,div_eq_mul_inv] using
      (((tendsto_inv_atTop_zero (𝕜 := ℝ)).comp primeInfinity_real_tendsto).const_mul (D : ℝ)).const_mul (F.card : ℝ)
  have he : Tendsto (fun q : OddPrime =>
      uniformMean (fun X : Fin 13 → SymMatrix (ZMod q.val) D => ∏ e∈F, boolSign (pairBool X e))-
      uniformMean (fun X : Fin 13 → SymMatrix (ZMod q.val) D => ∏ e∈F, pairSign X e)) primeInfinity (nhds 0) := by
    apply squeeze_zero_norm (fun q => ?_) hb
    simpa only [Real.norm_eq_abs,ZMod.card] using pairBool_moment_error (K := ZMod q.val) (D := D) F
  simpa only [sub_add_cancel,add_zero] using he.add hm
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
noncomputable def boolMonomial (F : Finset I) (η : I → Bool) : ℝ := ∏ i∈F, boolSign (η i)

omit [Fintype I] [DecidableEq I] in
@[simp] theorem boolMonomial_empty (η : I → Bool) : boolMonomial ∅ η=1 := by simp [boolMonomial]
theorem bool_factor (a b : Bool) : 1+boolSign a*boolSign b=if a=b then 2 else 0 := by
  cases a <;> cases b <;> norm_num [boolSign]

omit [DecidableEq I] in
theorem bool_indicator_product (η ε : I → Bool) :
    (if η=ε then 1 else 0 : ℝ) = (2^Fintype.card I : ℝ)⁻¹ *
      ∏ i, (1+boolSign (η i)*boolSign (ε i)) := by
  simp_rw [bool_factor]
  by_cases h : η=ε
  · subst ε
    simp
  · rw [if_neg h]
    obtain ⟨i,hi⟩ := Function.ne_iff.mp h
    have hp : (∏ i, (if η i=ε i then 2 else 0 : ℝ))=0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)
    rw [hp,mul_zero]

omit [DecidableEq I] in
theorem bool_indicator_expansion (η ε : I → Bool) :
    (if η=ε then 1 else 0 : ℝ) = (2^Fintype.card I : ℝ)⁻¹ *
      ∑ F : Finset I, boolMonomial F η * boolMonomial F ε := by
  rw [bool_indicator_product,Finset.prod_one_add]
  simp only [Finset.powerset_univ,Finset.prod_mul_distrib,boolMonomial]

variable {A : Type*} [Fintype A]
omit [DecidableEq I] in
theorem bool_law_expansion (T : A → I → Bool) (ε : I → Bool) :
    uniformMean (fun a => if T a=ε then 1 else 0)=
      (2^Fintype.card I : ℝ)⁻¹ * ∑ F : Finset I,
        (uniformMean fun a => boolMonomial F (T a))*boolMonomial F ε := by
  simp_rw [bool_indicator_expansion]
  rw [uniformMean_mul,uniformMean_sum]
  simp_rw [uniformMean_mul_right]

theorem uniformMean_test_fibers (T : A → I → Bool) (g : (I → Bool) → ℝ) :
    uniformMean (fun a => g (T a))=
      ∑ ε : I → Bool, g ε * uniformMean (fun a => if T a=ε then 1 else 0) := by
  have he (a : A) : g (T a)=∑ ε : I → Bool, g ε*(if T a=ε then 1 else 0) := by simp
  simp_rw [he]
  rw [uniformMean_sum]
  apply Finset.sum_congr rfl
  intro ε _
  rw [uniformMean_mul]
end Boolean
section Convergence
variable {I Q : Type*} [Fintype I] [DecidableEq I] {l : Filter Q}
  {A : Q → Type*} [∀ q, Fintype (A q)] [∀ q, Nonempty (A q)]

theorem boolean_law_tendsto (T : (q : Q) → A q → I → Bool)
    (h : ∀ F : Finset I, F.Nonempty → Tendsto
      (fun q => uniformMean (fun a => boolMonomial F (T q a))) l (nhds 0))
    (ε : I → Bool) : Tendsto
      (fun q => uniformMean (fun a => if T q a=ε then 1 else 0)) l
        (nhds ((Fintype.card (I → Bool) : ℝ)⁻¹)) := by
  have hm (F : Finset I) : Tendsto
      (fun q => (uniformMean fun a => boolMonomial F (T q a))*boolMonomial F ε) l
        (nhds (if F=∅ then (1:ℝ) else 0)) := by
    by_cases hF : F=∅
    · subst F; simp only [boolMonomial_empty,uniformMean_const,mul_one,↓reduceIte]; exact tendsto_const_nhds
    · simpa only [hF,ite_false,zero_mul] using (h F (Finset.nonempty_iff_ne_empty.mpr hF)).mul_const (boolMonomial F ε)
  have hs := (tendsto_finsetSum Finset.univ (fun F _ => hm F)).const_mul ((2^Fintype.card I : ℝ)⁻¹)
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true,mul_one] at hs
  simp only [bool_law_expansion,Fintype.card_fun,Fintype.card_bool,Nat.cast_pow,Nat.cast_ofNat]
  exact hs

theorem boolean_test_tendsto (T : (q : Q) → A q → I → Bool)
    (h : ∀ F : Finset I, F.Nonempty → Tendsto
      (fun q => uniformMean (fun a => boolMonomial F (T q a))) l (nhds 0))
    (g : (I → Bool) → ℝ) : Tendsto
      (fun q => uniformMean (fun a => g (T q a))) l (nhds (uniformMean g)) := by
  have hm (ε : I → Bool) := (boolean_law_tendsto T h ε).const_mul (g ε)
  have hs := tendsto_finsetSum Finset.univ (fun ε _ => hm ε)
  have he (q : Q) : uniformMean (fun a => g (T q a)) =
      ∑ ε : I → Bool, g ε * uniformMean (fun a => if T q a=ε then 1 else 0) :=
    uniformMean_test_fibers (T q) g
  simp only [he]
  convert hs using 1
  simp only [uniformMean,div_eq_mul_inv,Finset.sum_mul]
end Convergence

theorem pairBool_test_tendsto (D : ℕ) (hD : Even D) (hbig : 12≤D) (g : (Fin 33 → Bool) → ℝ) :
    Tendsto (fun q : OddPrime => uniformMean (fun X : Fin 13 → SymMatrix (ZMod q.val) D =>
      g (pairBool X))) primeInfinity (nhds (uniformMean g)) := by
  have hm (F : Finset (Fin 33)) (hF : F.Nonempty) :
      Tendsto (fun q : OddPrime => uniformMean (fun X : Fin 13 → SymMatrix (ZMod q.val) D =>
        boolMonomial F (pairBool X))) primeInfinity (nhds 0) := by
    simpa only [boolMonomial] using pairBool_moment_tendsto D hD hbig F hF
  exact boolean_test_tendsto (I := Fin 33) (Q := OddPrime) (l := primeInfinity)
    (A := fun q : OddPrime => Fin 13 → SymMatrix (ZMod q.val) D)
    (fun (q : OddPrime) (X : Fin 13 → SymMatrix (ZMod q.val) D) => pairBool X) hm g
end SidorenkoCounterexample

end

end OAI

section R1H2Bridge
open OAI.SidorenkoCounterexample

private lemma r1h2_facePair_endpoints :
    ∀ (j : Fin 22) (k : Fin 3),
      pairLeft (facePair j k) = faceVertex j ((![0,0,1] : Fin 3 → Fin 3) k) ∧
      pairRight (facePair j k) = faceVertex j ((![1,2,2] : Fin 3 → Fin 3) k) := by
  decide

theorem OMA.solution : OMA.R_SidorenkoConjecture_sidorenko_conjecture_graphon_R1_H1_R1_H1_R1_H1_R1.H2 := by
  unfold OMA.R_SidorenkoConjecture_sidorenko_conjecture_graphon_R1_H1_R1_H1_R1_H1_R1.H2
  dsimp only
  intro d he hd f
  let sL : Fin 3 → Fin 3 := ![0,0,1]
  let sR : Fin 3 → Fin 3 := ![1,2,2]
  let t : Fin 22 → Fin 3 → Fin 13 := ![![0,1,3],![0,1,9],![0,2,3],![0,2,9],![1,3,10],![1,7,10],![1,7,12],![1,9,12],![2,3,4],![2,4,9],![3,4,11],![3,10,11],![4,8,9],![4,8,11],![5,6,7],![5,6,11],![5,7,10],![5,10,11],![6,7,12],![6,8,11],![6,8,12],![8,9,12]]
  let p : Fin 22 → Fin 3 → Fin 33 := ![![5,1,6],![5,3,9],![0,1,2],![0,3,4],![6,11,12],![19,11,20],![19,15,23],![9,15,16],![2,7,8],![7,4,10],![8,13,14],![12,13,21],![17,10,18],![17,14,22],![32,25,30],![32,27,29],![25,26,20],![26,27,21],![30,31,23],![28,29,22],![28,31,24],![18,24,16]]
  let g : (Fin 33 → Bool) → ℝ := fun η => f (fun j k => η (p j k))
  have ht := pairBool_test_tendsto d he hd g
  have hlim : uniformMean g =
      (∑ η : Fin 33 → Bool, f (fun j k => η (p j k))) / (Fintype.card (Fin 33 → Bool) : ℝ) := by
    unfold uniformMean g
    congr 1
  rw [hlim] at ht
  refine ht.congr (fun q => ?_)
  haveI : Fact q.val.Prime := ⟨q.2.1⟩
  haveI : NeZero q.val := ⟨q.2.1.ne_zero⟩
  let S := {A : Matrix (Fin d) (Fin d) (ZMod q.val) // A.IsSymm}
  let eMat : S ≃ SymMatrix (ZMod q.val) d := Equiv.subtypeEquivRight (fun _ => Iff.rfl)
  let eFn : (Fin 13 → S) ≃ (Fin 13 → SymMatrix (ZMod q.val) d) := Equiv.piCongrRight (fun _ => eMat)
  change uniformMean (fun X : Fin 13 → SymMatrix (ZMod q.val) d => g (pairBool X)) =
    uniformMean (fun X : Fin 13 → S => f (fun j k =>
      decide (quadraticChar (ZMod q.val) ((X (t j (sL k))).val - (X (t j (sR k))).val).det = 1)))
  rw [← uniformMean_equiv eFn (fun X => g (pairBool X))]
  apply uniformMean_congr
  intro X
  dsimp only [Function.comp_def, g]
  congr 1
  funext j k
  have hep := r1h2_facePair_endpoints j k
  have hdet :
      (((eFn X) (pairLeft (facePair j k)) - (eFn X) (pairRight (facePair j k))).val.det) =
      ((X (t j (sL k))).val - (X (t j (sR k))).val).det := by
    have hl : ((eFn X) (pairLeft (facePair j k))).val = (X (t j (sL k))).val := by
      change (X (pairLeft (facePair j k))).val = (X (t j (sL k))).val
      rw [hep.1]; rfl
    have hr : ((eFn X) (pairRight (facePair j k))).val = (X (t j (sR k))).val := by
      change (X (pairRight (facePair j k))).val = (X (t j (sR k))).val
      rw [hep.2]; rfl
    rw [Submodule.coe_sub, hl, hr]
  have hiff :
      (pairSign (eFn X) (facePair j k) = 1) ↔
      (quadraticChar (ZMod q.val) ((X (t j (sL k))).val - (X (t j (sR k))).val).det = 1) := by
    unfold pairSign
    rw [hdet]
    convert Int.cast_eq_one
    infer_instance
  rw [show p j k = facePair j k from rfl]
  unfold pairBool
  by_cases hp1 : pairSign (eFn X) (facePair j k) = 1
  · have hp2 := hiff.mp hp1
    rw [decide_eq_true hp1, decide_eq_true hp2]
  · have hp2 := mt hiff.mpr hp1
    rw [decide_eq_false hp1, decide_eq_false hp2]
end R1H2Bridge
