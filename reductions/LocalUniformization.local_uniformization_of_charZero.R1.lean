import FormalConjectures.Wikipedia.LocalUniformization
import Mathlib

/-!
  Reduction of Zariski's local uniformization theorem in characteristic zero
  (LocalUniformization.local_uniformization_of_charZero) to two disjoint Type 0 hypotheses
  for non-divisorial valuations in transcendence degree at least two:

    H1 : Rank-1 (archimedean) valuations over Type 0 fields of characteristic zero
         with trdeg_k(ResidueField O) + 1 < trdeg_k(F) (Zariski 1940 §§1-3).
    H2 : Composite (higher-rank) valuations over Type 0 fields of characteristic zero
         with trdeg_k(ResidueField O) + 1 < trdeg_k(F) (Zariski 1940 §4).

  This file proves in full:
    1. Existence of an affine model inside any valuation subring containing k, and
       transport of HasLocalUniformization across compatible field equivalences.
    2. Complete local uniformization whenever trdeg_k(F) ≤ trdeg_k(ResidueField O) + 1,
       which settles all algebraic extensions (trdeg = 0), all algebraic curves (trdeg = 1)
       via integral closures as Dedekind domains, all trivial valuations (O = ⊤), and
       all divisorial valuations (trdeg_k(ResidueField O) = trdeg_k(F) - 1) in every
       dimension.
    3. Preservation of regular local rings under arbitrary characteristic-zero field
       base change k₀ → k (finite-generator descent + induction on simple transcendental
       and simple separable algebraic extensions + flat local Going-Down).
    4. Full universe and countability descent (k : Type u, F : Type v) → (k₀ F₀ : Type 0)
       by descending defining equations of an affine model to a finitely generated
       countable subfield k₀ ⊆ k, proving linear disjointness k ⊗[k₀] F₀ ↪ F,
       shrinking to Type 0, and ascending the uniformizing model back to (k, F).
-/

open IsLocalRing Polynomial
open scoped TensorProduct Pointwise

namespace OMA.R_LocalUniformization_local_uniformization_of_charZero_R1

def H1 : Prop :=
  ∀ (k F : Type) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] [CharZero k]
    (𝒪 : ValuationSubring F) [Algebra k 𝒪] [IsScalarTower k 𝒪 F],
    Algebra.trdeg k (IsLocalRing.ResidueField 𝒪) + 1 < Algebra.trdeg k F →
    (∀ 𝒪' : ValuationSubring F, 𝒪 < 𝒪' → 𝒪' = ⊤) →
    𝒪.HasLocalUniformization k

def H2 : Prop :=
  ∀ (k F : Type) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] [CharZero k]
    (𝒪 : ValuationSubring F) [Algebra k 𝒪] [IsScalarTower k 𝒪 F],
    Algebra.trdeg k (IsLocalRing.ResidueField 𝒪) + 1 < Algebra.trdeg k F →
    (∃ 𝒪' : ValuationSubring F, 𝒪 < 𝒪' ∧ 𝒪' < ⊤) →
    𝒪.HasLocalUniformization k

section

/- Section 1: Affine models, fraction fields, and transport of HasLocalUniformization -/

private lemma isFractionRing_of_adjoin_eq_top
    {k : Type*} {F : Type*} [Field k] [Field F] [Algebra k F]
    (A : Subalgebra k F)
    (hgen : IntermediateField.adjoin k (A : Set F) = ⊤) :
    IsFractionRing A F := by
  let S : IntermediateField k F :=
    { carrier := { x : F | ∃ (a b : A), b ≠ 0 ∧ (b : F) * x = (a : F) }
      mul_mem' := by
        rintro x y ⟨a₁, b₁, hb₁, h₁⟩ ⟨a₂, b₂, hb₂, h₂⟩
        refine ⟨a₁ * a₂, b₁ * b₂, mul_ne_zero hb₁ hb₂, ?_⟩
        push_cast
        calc ((b₁ : F) * (b₂ : F)) * (x * y)
            = ((b₁ : F) * x) * ((b₂ : F) * y) := by ring
          _ = (a₁ : F) * (a₂ : F) := by rw [h₁, h₂]
      one_mem' := ⟨1, 1, one_ne_zero, by simp⟩
      add_mem' := by
        rintro x y ⟨a₁, b₁, hb₁, h₁⟩ ⟨a₂, b₂, hb₂, h₂⟩
        refine ⟨a₁ * b₂ + a₂ * b₁, b₁ * b₂, mul_ne_zero hb₁ hb₂, ?_⟩
        push_cast
        calc ((b₁ : F) * (b₂ : F)) * (x + y)
            = ((b₁ : F) * x) * (b₂ : F) + ((b₂ : F) * y) * (b₁ : F) := by ring
          _ = (a₁ : F) * (b₂ : F) + (a₂ : F) * (b₁ : F) := by rw [h₁, h₂]
      zero_mem' := ⟨0, 1, one_ne_zero, by simp⟩
      inv_mem' := by
        rintro x ⟨a, b, hb, h⟩
        by_cases hx : x = 0
        · subst hx
          exact ⟨0, 1, one_ne_zero, by simp⟩
        · have ha : a ≠ 0 := by
            intro ha0
            have hb0 : (b : F) ≠ 0 := fun h0 => hb (Subtype.ext h0)
            have hmul : (b : F) * x = 0 := by simpa [ha0] using h
            exact (mul_ne_zero hb0 hx) hmul
          refine ⟨b, a, ha, ?_⟩
          calc (a : F) * x⁻¹ = ((b : F) * x) * x⁻¹ := by rw [h]
            _ = (b : F) := by rw [mul_assoc, mul_inv_cancel₀ hx, mul_one]
      algebraMap_mem' := fun c => ⟨algebraMap k A c, 1, one_ne_zero, by simp⟩ }
  have hAS : (A : Set F) ⊆ (S : Set F) := fun x hx => ⟨⟨x, hx⟩, 1, one_ne_zero, by simp⟩
  have htop : S = ⊤ := top_le_iff.mp (hgen ▸ IntermediateField.adjoin_le_iff.mpr hAS)
  refine ⟨?_, ?_, ?_⟩
  · intro y
    have hy : (y : A) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp y.2
    have hyF : ((y : A) : F) ≠ 0 := fun h0 => hy (Subtype.ext h0)
    exact isUnit_iff_ne_zero.mpr hyF
  · intro x
    have hx : x ∈ S := by rw [htop]; trivial
    obtain ⟨a, b, hb, h⟩ := hx
    refine ⟨(a, ⟨b, mem_nonZeroDivisors_iff_ne_zero.mpr hb⟩), ?_⟩
    change x * (b : F) = (a : F)
    rw [mul_comm]
    exact h
  · intro x y hxy
    refine ⟨1, ?_⟩
    have h1 : (x : F) = (y : F) := hxy
    simp [Subtype.ext h1]

private lemma exists_affine_model_in_valuationSubring
    (k : Type*) (F : Type*) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F]
    (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) :
    ∃ (A : Subalgebra k F),
      (∀ a : A, (a : F) ∈ 𝒪) ∧ Algebra.FiniteType k A ∧ IsFractionRing A F := by
  classical
  obtain ⟨s, hs⟩ := IntermediateField.fg_top k F
  let t : Finset F := s.image fun x => if x ∈ 𝒪 then x else x⁻¹
  have ht_in : ∀ x ∈ (t : Set F), x ∈ 𝒪 := by
    intro x hx
    rw [Finset.mem_coe, Finset.mem_image] at hx
    obtain ⟨y, _, rfl⟩ := hx
    split_ifs with hy
    · exact hy
    · exact (𝒪.mem_or_inv_mem y).resolve_left hy
  let A : Subalgebra k F := Algebra.adjoin k (t : Set F)
  have hA_in : ∀ a : A, (a : F) ∈ 𝒪 := by
    rintro ⟨a, ha⟩
    refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ ha
    · intro x hx; exact ht_in x hx
    · intro c; exact hk c
    · intro x y _ _ hx hy; exact add_mem hx hy
    · intro x y _ _ hx hy; exact mul_mem hx hy
  have hfin : Algebra.FiniteType k A := Algebra.FiniteType.adjoin_of_finite t.finite_toSet
  have htop : IntermediateField.adjoin k (A : Set F) = ⊤ := by
    rw [eq_top_iff, ← hs, IntermediateField.adjoin_le_iff]
    intro x hx
    by_cases hxo : x ∈ 𝒪
    · have hxt : x ∈ (t : Set F) := by
        rw [Finset.mem_coe, Finset.mem_image]
        exact ⟨x, hx, by simp [hxo]⟩
      exact IntermediateField.subset_adjoin k (A : Set F) (Algebra.subset_adjoin hxt)
    · have hxinv_t : x⁻¹ ∈ (t : Set F) := by
        rw [Finset.mem_coe, Finset.mem_image]
        exact ⟨x, hx, by simp [hxo]⟩
      have hxinv_mem : x⁻¹ ∈ IntermediateField.adjoin k (A : Set F) :=
        IntermediateField.subset_adjoin k (A : Set F) (Algebra.subset_adjoin hxinv_t)
      simpa using (IntermediateField.adjoin k (A : Set F)).inv_mem hxinv_mem
  exact ⟨A, hA_in, hfin, isFractionRing_of_adjoin_eq_top A htop⟩

private lemma mem_centerOn_iff_zero_or_inv_notMem
    {k : Type*} {F : Type*} [Field k] [Field F] [Algebra k F]
    (𝒪 : ValuationSubring F) (A : Subalgebra k F) (hA : ∀ a : A, (a : F) ∈ 𝒪) (a : A) :
    a ∈ 𝒪.centerOn A hA ↔ (a : F) = 0 ∨ (a : F)⁻¹ ∉ 𝒪 := by
  change (⟨(a : F), hA a⟩ : 𝒪) ∈ maximalIdeal 𝒪 ↔ _
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  constructor
  · intro hnu
    by_cases ha0 : (a : F) = 0
    · exact Or.inl ha0
    · right
      intro hinv
      apply hnu
      refine isUnit_iff_exists_inv.mpr ⟨⟨(a : F)⁻¹, hinv⟩, Subtype.ext ?_⟩
      exact mul_inv_cancel₀ ha0
  · rintro (ha0 | hinv) hu
    · obtain ⟨u, hu'⟩ := isUnit_iff_exists_inv.mp hu
      have h1 : (a : F) * (u : F) = 1 := congrArg Subtype.val hu'
      rw [ha0, zero_mul] at h1
      exact zero_ne_one h1
    · obtain ⟨u, hu'⟩ := isUnit_iff_exists_inv.mp hu
      have h1 : (a : F) * (u : F) = 1 := congrArg Subtype.val hu'
      have hu_eq : (u : F) = (a : F)⁻¹ := eq_inv_of_mul_eq_one_right h1
      exact hinv (hu_eq ▸ u.2)

private lemma hasLocalUniformization_of_ringEquiv
    {k₁ k₂ F₁ F₂ : Type*} [Field k₁] [Field k₂] [Field F₁] [Field F₂]
    [Algebra k₁ F₁] [Algebra k₂ F₂]
    (ek : k₁ ≃+* k₂) (eF : F₁ ≃+* F₂)
    (hcompat : ∀ c : k₁, eF (algebraMap k₁ F₁ c) = algebraMap k₂ F₂ (ek c))
    (𝒪₁ : ValuationSubring F₁) (𝒪₂ : ValuationSubring F₂)
    (h𝒪 : ∀ x : F₁, x ∈ 𝒪₁ ↔ eF x ∈ 𝒪₂)
    (hLU : 𝒪₁.HasLocalUniformization k₁) :
    𝒪₂.HasLocalUniformization k₂ := by
  classical
  obtain ⟨A₁, hA₁, hfin₁, hfrac₁, hreg₁⟩ := hLU
  let A₂ : Subalgebra k₂ F₂ :=
    { carrier := eF '' (A₁ : Set F₁)
      mul_mem' := by
        rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
        exact ⟨x * y, A₁.mul_mem hx hy, map_mul eF x y⟩
      one_mem' := ⟨1, A₁.one_mem, map_one eF⟩
      add_mem' := by
        rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
        exact ⟨x + y, A₁.add_mem hx hy, map_add eF x y⟩
      zero_mem' := ⟨0, A₁.zero_mem, map_zero eF⟩
      algebraMap_mem' := fun c => by
        refine ⟨algebraMap k₁ F₁ (ek.symm c), A₁.algebraMap_mem _, ?_⟩
        rw [hcompat, ek.apply_symm_apply] }
  have hA₂ : ∀ a : A₂, (a : F₂) ∈ 𝒪₂ := by
    rintro ⟨_, x, hx, rfl⟩
    exact (h𝒪 x).mp (hA₁ ⟨x, hx⟩)
  let eA : A₁ ≃+* A₂ :=
    { toFun := fun x => ⟨eF x.1, x.1, x.2, rfl⟩
      invFun := fun y => ⟨eF.symm y.1, by
        rcases y.2 with ⟨x, hx, hxy⟩
        rw [← hxy, eF.symm_apply_apply]
        exact hx⟩
      left_inv := fun x => Subtype.ext (eF.symm_apply_apply x.1)
      right_inv := fun y => Subtype.ext (eF.apply_symm_apply y.1)
      map_mul' := fun x y => Subtype.ext (map_mul eF x.1 y.1)
      map_add' := fun x y => Subtype.ext (map_add eF x.1 y.1) }
  have hfin₂ : Algebra.FiniteType k₂ A₂ := by
    obtain ⟨s, hs⟩ := hfin₁.out
    refine ⟨⟨s.image eA, eq_top_iff.mpr fun y _ => ?_⟩⟩
    have hx : eA.symm y ∈ Algebra.adjoin k₁ (s : Set A₁) := by rw [hs]; trivial
    have hmap : ∀ x ∈ Algebra.adjoin k₁ (s : Set A₁),
        eA x ∈ Algebra.adjoin k₂ ((s.image eA : Finset A₂) : Set A₂) := by
      intro x hx'
      refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hx'
      · intro z hz
        exact Algebra.subset_adjoin (Finset.mem_coe.mpr (Finset.mem_image_of_mem eA hz))
      · intro c
        have hc : eA (algebraMap k₁ A₁ c) = algebraMap k₂ A₂ (ek c) := Subtype.ext (hcompat c)
        rw [hc]
        exact Subalgebra.algebraMap_mem _ _
      · intro u v _ _ hu hv; rw [map_add]; exact add_mem hu hv
      · intro u v _ _ hu hv; rw [map_mul]; exact mul_mem hu hv
    simpa [eA.apply_symm_apply] using hmap (eA.symm y) hx
  have hfrac₂ : IsFractionRing A₂ F₂ := by
    refine ⟨?_, ?_, ?_⟩
    · intro y
      have hy : (y : A₂) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp y.2
      exact isUnit_iff_ne_zero.mpr fun h0 => hy (Subtype.ext h0)
    · intro x
      obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors A₁) (eF.symm x)
      have hb0 : (b : A₁) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp b.2
      have heb0 : eA b ≠ 0 := fun h => hb0 (eA.injective (by rw [h, map_zero]))
      refine ⟨(eA a, ⟨eA b, mem_nonZeroDivisors_iff_ne_zero.mpr heb0⟩), ?_⟩
      change x * eF (b : A₁).1 = eF a.1
      have h1 := congrArg eF hab
      simp only [map_mul, eF.apply_symm_apply] at h1
      exact h1
    · intro x y hxy
      exact ⟨1, by simp [Subtype.ext (show (x : F₂) = (y : F₂) from hxy)]⟩
  have hcomap : (𝒪₂.centerOn A₂ hA₂).comap eA.toRingHom = 𝒪₁.centerOn A₁ hA₁ := by
    ext a
    rw [Ideal.mem_comap, mem_centerOn_iff_zero_or_inv_notMem, mem_centerOn_iff_zero_or_inv_notMem]
    change (eF a.1 = 0 ∨ (eF a.1)⁻¹ ∉ 𝒪₂) ↔ (a.1 = 0 ∨ a.1⁻¹ ∉ 𝒪₁)
    rw [map_eq_zero_iff eF eF.injective, ← map_inv₀ eF, ← h𝒪 a.1⁻¹]
  have hpc : (𝒪₁.centerOn A₁ hA₁).primeCompl.map eA.toRingHom.toMonoidHom =
      (𝒪₂.centerOn A₂ hA₂).primeCompl := by
    ext y
    simp only [Submonoid.mem_map, Ideal.mem_primeCompl_iff]
    constructor
    · rintro ⟨x, hx, rfl⟩ hmem
      exact hx (by rw [← hcomap]; exact hmem)
    · intro hy
      refine ⟨eA.symm y, fun hx => hy ?_, eA.apply_symm_apply y⟩
      have h1 : eA.symm y ∈ (𝒪₂.centerOn A₂ hA₂).comap eA.toRingHom := by
        rw [hcomap]; exact hx
      rw [Ideal.mem_comap] at h1
      change eA (eA.symm y) ∈ 𝒪₂.centerOn A₂ hA₂ at h1
      rwa [eA.apply_symm_apply] at h1
  let eLoc : Localization.AtPrime (𝒪₁.centerOn A₁ hA₁) ≃+*
      Localization.AtPrime (𝒪₂.centerOn A₂ hA₂) :=
    IsLocalization.ringEquivOfRingEquiv _ _ eA hpc
  have hreg₂ : IsRegularLocalRing (Localization.AtPrime (𝒪₂.centerOn A₂ hA₂)) :=
    IsRegularLocalRing.of_ringEquiv eLoc
  exact ⟨A₂, hA₂, hfin₂, hfrac₂, hreg₂⟩

/- Section 2: Curves, algebraic extensions, and divisorial valuations in Type 0 -/

private lemma hasLocalUniformization_of_isAlgebraic
    (k F : Type) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F]
    (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪)
    (halg : Algebra.IsAlgebraic k F) :
    𝒪.HasLocalUniformization k := by
  let : Algebra k 𝒪 := ((algebraMap k F).codRestrict 𝒪 hk).toAlgebra
  have : IsScalarTower k 𝒪 F := IsScalarTower.of_algebraMap_eq' rfl
  have htop : 𝒪 = ⊤ := by
    ext x
    simp only [ValuationSubring.mem_top, iff_true]
    have hint_k : IsIntegral k x := (halg.isAlgebraic x).isIntegral
    have hint_O : IsIntegral 𝒪 x := hint_k.tower_top
    obtain ⟨y, hy⟩ := (isIntegrallyClosed_iff F).mp (inferInstance : IsIntegrallyClosed 𝒪) hint_O
    exact hy ▸ y.2
  subst htop
  obtain ⟨A, _, hfin, hfrac⟩ := exists_affine_model_in_valuationSubring k F ⊤ hk
  exact LocalUniformization.hasLocalUniformization_top A

private lemma hasLocalUniformization_of_trdeg_eq_one
    (k F : Type) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] [CharZero k]
    (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪)
    (htr : Algebra.trdeg k F = 1) :
    𝒪.HasLocalUniformization k := by
  classical
  obtain ⟨s, hs⟩ := exists_finset_isTranscendenceBasis k F
  have hcard : s.card = 1 := by
    have hmk : (Cardinal.mk s : Cardinal) = 1 := by
      simpa [htr] using hs.cardinalMk_eq_trdeg
    simpa [Cardinal.mk_fintype] using hmk
  obtain ⟨t₀, rfl⟩ := Finset.card_eq_one.mp hcard
  have ht₀_indep : ¬ IsAlgebraic k t₀ := by
    intro halg
    have h1 := hs.1
    rw [algebraicIndependent_iff_injective_aeval] at h1
    have hev_left : ∀ q : k[X],
        MvPolynomial.aeval (fun _ : ({t₀} : Finset F) => Polynomial.X (R := k))
          (Polynomial.aeval (R := k) (MvPolynomial.X (R := k)
            (⟨t₀, Finset.mem_singleton_self t₀⟩ : ({t₀} : Finset F))) q) = q := by
      intro q
      induction q using Polynomial.induction_on' with
      | add q₁ q₂ hq₁ hq₂ => rw [map_add, map_add, hq₁, hq₂]
      | monomial n a =>
        rw [Polynomial.aeval_monomial, map_mul, map_pow, AlgHom.commutes, MvPolynomial.aeval_X,
          Polynomial.algebraMap_eq, Polynomial.C_mul_X_pow_eq_monomial]
    have hev_right : ∀ q : k[X],
        MvPolynomial.aeval ((↑) : ({t₀} : Finset F) → F)
          (Polynomial.aeval (R := k) (MvPolynomial.X (R := k)
            (⟨t₀, Finset.mem_singleton_self t₀⟩ : ({t₀} : Finset F))) q) =
          Polynomial.aeval t₀ q := by
      intro q
      induction q using Polynomial.induction_on' with
      | add q₁ q₂ hq₁ hq₂ => rw [map_add, map_add, map_add, hq₁, hq₂]
      | monomial n a =>
        rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, map_mul, map_pow,
          AlgHom.commutes, MvPolynomial.aeval_X]
    obtain ⟨p, hp0, hp⟩ := halg
    let P : MvPolynomial ({t₀} : Finset F) k :=
      Polynomial.aeval (R := k) (MvPolynomial.X (R := k)
        (⟨t₀, Finset.mem_singleton_self t₀⟩ : ({t₀} : Finset F))) p
    have hP0 : P ≠ 0 := by
      intro h0
      have h0' := congrArg (MvPolynomial.aeval (fun _ : ({t₀} : Finset F) => Polynomial.X (R := k))) h0
      rw [hev_left p, map_zero] at h0'
      exact hp0 h0'
    have hPev : MvPolynomial.aeval ((↑) : ({t₀} : Finset F) → F) P = 0 := by
      rw [hev_right p]
      exact hp
    exact hP0 (h1 (by simpa using hPev))
  let t : F := if t₀ ∈ 𝒪 then t₀ else t₀⁻¹
  have ht_in : t ∈ 𝒪 := by
    dsimp only [t]
    split_ifs with h
    · exact h
    · exact (𝒪.mem_or_inv_mem t₀).resolve_left h
  have hK_eq : IntermediateField.adjoin k ({t} : Set F) =
      IntermediateField.adjoin k ({t₀} : Set F) := by
    dsimp only [t]
    split_ifs
    · rfl
    · apply le_antisymm
      · rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
        exact (IntermediateField.adjoin k ({t₀} : Set F)).inv_mem
          (IntermediateField.subset_adjoin k _ (Set.mem_singleton t₀))
      · rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
        simpa using (IntermediateField.adjoin k ({t₀⁻¹} : Set F)).inv_mem
          (IntermediateField.subset_adjoin k _ (Set.mem_singleton t₀⁻¹))
  have ht_trans : ¬ IsAlgebraic k t := by
    intro halg
    have : Algebra.IsAlgebraic k (IntermediateField.adjoin k ({t} : Set F)) :=
      IntermediateField.isAlgebraic_adjoin_simple halg.isIntegral
    have ht₀_mem : t₀ ∈ IntermediateField.adjoin k ({t} : Set F) := by
      rw [hK_eq]
      exact IntermediateField.subset_adjoin k _ (Set.mem_singleton t₀)
    have ht₀_alg : IsAlgebraic k (⟨t₀, ht₀_mem⟩ : IntermediateField.adjoin k ({t} : Set F)) :=
      Algebra.IsAlgebraic.isAlgebraic _
    exact ht₀_indep (ht₀_alg.algHom (IntermediateField.val _))
  let A₁ : Subalgebra k F := Algebra.adjoin k ({t} : Set F)
  let K : IntermediateField k F := IntermediateField.adjoin k ({t} : Set F)
  have haeval_inj : Function.Injective (Polynomial.aeval (R := k) t) := by
    rw [injective_iff_map_eq_zero]
    intro p hp
    by_contra hp0
    exact ht_trans ⟨p, hp0, hp⟩
  have haeval_range : (Polynomial.aeval (R := k) t).range = A₁ := by
    ext x
    rw [AlgHom.mem_range]
    change (∃ p : k[X], Polynomial.aeval t p = x) ↔ x ∈ Algebra.adjoin k ({t} : Set F)
    rw [Algebra.adjoin_singleton_eq_range_aeval]
    rfl
  let ePoly : k[X] ≃ₐ[k] A₁ :=
    (AlgEquiv.ofInjective (Polynomial.aeval (R := k) t) haeval_inj).trans
      (Subalgebra.equivOfEq _ _ haeval_range)
  have hPIR : IsPrincipalIdealRing A₁ :=
    IsPrincipalIdealRing.of_surjective ePoly.toRingHom ePoly.surjective
  have hDed₁ : IsDedekindDomain A₁ := inferInstance
  have hA₁_le_K : A₁ ≤ K.toSubalgebra := IntermediateField.algebra_adjoin_le_adjoin k {t}
  let : Algebra A₁ K := ((Subalgebra.inclusion hA₁_le_K).toRingHom).toAlgebra
  have : IsScalarTower A₁ K F := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower k A₁ K := IsScalarTower.of_algebraMap_eq' rfl
  have hfrac_A₁_K : IsFractionRing A₁ K := by
    refine ⟨?_, ?_, ?_⟩
    · intro y
      have hy : (y : A₁) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp y.2
      refine isUnit_iff_ne_zero.mpr fun h0 => hy ?_
      have h0F : ((y : A₁) : F) = 0 := congrArg Subtype.val h0
      exact Subtype.ext h0F
    · intro x
      have hx : (x : F) ∈ IntermediateField.adjoin k ({t} : Set F) := x.2
      rw [IntermediateField.mem_adjoin_simple_iff] at hx
      obtain ⟨p, q, hpq⟩ := hx
      by_cases hq0 : Polynomial.aeval t q = 0
      · rw [hq0, div_zero] at hpq
        refine ⟨(0, 1), ?_⟩
        apply Subtype.ext
        change (x : F) * 1 = 0
        rw [mul_one, ← hpq]
      · have hqA : Polynomial.aeval t q ∈ A₁ := by
          rw [← haeval_range]; exact ⟨q, rfl⟩
        have hpA : Polynomial.aeval t p ∈ A₁ := by
          rw [← haeval_range]; exact ⟨p, rfl⟩
        have hqne : (⟨Polynomial.aeval t q, hqA⟩ : A₁) ≠ 0 := fun h => hq0 (congrArg Subtype.val h)
        refine ⟨(⟨Polynomial.aeval t p, hpA⟩, ⟨⟨Polynomial.aeval t q, hqA⟩,
          mem_nonZeroDivisors_iff_ne_zero.mpr hqne⟩), ?_⟩
        apply Subtype.ext
        change (x : F) * Polynomial.aeval t q = Polynomial.aeval t p
        rw [hpq, div_mul_cancel₀ _ hq0]
    · intro x y hxy
      have hxyF : (x : F) = (y : F) := congrArg (fun z : K => (z : F)) hxy
      exact ⟨1, by simp [Subtype.ext hxyF]⟩
  have hK_alg_F : Algebra.IsAlgebraic K F := by
    have h1 := hs.isAlgebraic_field
    have hrange : Set.range ((↑) : ({t₀} : Finset F) → F) = ({t₀} : Set F) := by
      ext x; simp
    rw [hrange, ← hK_eq] at h1
    exact h1
  have : Algebra.EssFiniteType K F := Algebra.EssFiniteType.of_comp k K F
  have hFinDim : FiniteDimensional K F := by
    obtain ⟨u, hu⟩ := IntermediateField.fg_top K F
    have hfin : FiniteDimensional K (IntermediateField.adjoin K (u : Set F)) :=
      IntermediateField.finiteDimensional_adjoin fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
    rw [hu] at hfin
    exact Module.Finite.equiv IntermediateField.topEquiv.toLinearEquiv
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
  have : Algebra.IsSeparable K F := inferInstance
  let B_sub : Subalgebra A₁ F := integralClosure A₁ F
  let B : Subalgebra k F := B_sub.restrictScalars k
  have hA₁_in_O : ∀ a : A₁, (a : F) ∈ 𝒪 := by
    rintro ⟨a, ha⟩
    refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ ha
    · intro x hx
      have hxt : x = t := Set.mem_singleton_iff.mp hx
      subst hxt
      exact ht_in
    · intro c; exact hk c
    · intro x y _ _ hx hy; exact add_mem hx hy
    · intro x y _ _ hx hy; exact mul_mem hx hy
  let : Algebra A₁ 𝒪 := ((A₁.val.toRingHom).codRestrict 𝒪 hA₁_in_O).toAlgebra
  have : IsScalarTower A₁ 𝒪 F := IsScalarTower.of_algebraMap_eq' rfl
  have hB_in_O : ∀ b : B, (b : F) ∈ 𝒪 := by
    rintro ⟨b, hb⟩
    have hint_O : IsIntegral 𝒪 b := hb.tower_top
    obtain ⟨y, hy⟩ := (isIntegrallyClosed_iff F).mp (inferInstance : IsIntegrallyClosed 𝒪) hint_O
    exact hy ▸ y.2
  have hDed_Bsub : IsDedekindDomain B_sub := integralClosure.isDedekindDomain A₁ K F
  have hDed_B : IsDedekindDomain B := hDed_Bsub
  have hReg_B : IsRegularRing B := inferInstance
  have hModFin : Module.Finite A₁ B_sub := IsIntegralClosure.finite A₁ K F B_sub
  have hFT_k_B : Algebra.FiniteType k B := by
    obtain ⟨u, hu⟩ := Module.Finite.fg_top (R := A₁) (M := B_sub)
    let tB : B := ⟨t, algebraMap_mem B_sub ⟨t, Algebra.subset_adjoin (Set.mem_singleton t)⟩⟩
    let genB : Finset B := insert tB (u.image fun b => (⟨b.1, b.2⟩ : B))
    refine ⟨⟨genB, eq_top_iff.mpr fun b _ => ?_⟩⟩
    have hb_span : (⟨b.1, b.2⟩ : B_sub) ∈ Submodule.span A₁ (u : Set B_sub) := by
      rw [hu]; trivial
    have hA₁_sub : ∀ a : A₁, (⟨a.1, algebraMap_mem B_sub a⟩ : B) ∈
        Algebra.adjoin k (genB : Set B) := by
      rintro ⟨a, ha⟩
      refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ ha
      · intro x hx
        have hxt : x = t := Set.mem_singleton_iff.mp hx
        subst hxt
        exact Algebra.subset_adjoin (Finset.mem_coe.mpr (Finset.mem_insert_self tB _))
      · intro c; exact Subalgebra.algebraMap_mem _ c
      · intro x y _ _ hx hy; exact add_mem hx hy
      · intro x y _ _ hx hy; exact mul_mem hx hy
    have hspan_mem : ∀ x : B_sub, x ∈ Submodule.span A₁ (u : Set B_sub) →
        (⟨x.1, x.2⟩ : B) ∈ Algebra.adjoin k (genB : Set B) := by
      intro x hx
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
      · intro y hy
        exact Algebra.subset_adjoin (Finset.mem_coe.mpr
          (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨y, hy, rfl⟩)))
      · exact zero_mem _
      · intro y z _ _ hy hz; exact add_mem hy hz
      · intro a y _ hy
        have hmul : (⟨(a • y).1, (a • y).2⟩ : B) =
            (⟨a.1, algebraMap_mem B_sub a⟩ : B) * (⟨y.1, y.2⟩ : B) := rfl
        rw [hmul]
        exact mul_mem (hA₁_sub a) hy
    exact hspan_mem ⟨b.1, b.2⟩ hb_span
  have hFrac_Bsub : IsFractionRing B_sub F :=
    IsIntegralClosure.isFractionRing_of_finite_extension A₁ K F (integralClosure A₁ F)
  have hFrac_B : IsFractionRing B F := by
    refine ⟨?_, ?_, ?_⟩
    · intro y
      have hy : (y : B) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp y.2
      exact isUnit_iff_ne_zero.mpr fun h0 => hy (Subtype.ext h0)
    · intro x
      obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors B_sub) x
      have hb0 : (b : B_sub) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp b.2
      have hbB0 : (⟨b.1.1, b.1.2⟩ : B) ≠ 0 := fun h => hb0 (Subtype.ext (congrArg Subtype.val h))
      refine ⟨(⟨a.1, a.2⟩, ⟨⟨b.1.1, b.1.2⟩, mem_nonZeroDivisors_iff_ne_zero.mpr hbB0⟩), hab⟩
    · intro x y hxy
      exact ⟨1, by simp [Subtype.ext (show (x : F) = (y : F) from hxy)]⟩
  exact ValuationSubring.hasLocalUniformization_of_isRegularRing 𝒪 B hB_in_O

private lemma hasLocalUniformization_of_trdeg_le_residue_add_one
    (k F : Type) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] [CharZero k]
    (𝒪 : ValuationSubring F) [Algebra k 𝒪] [IsScalarTower k 𝒪 F]
    (hle : Algebra.trdeg k F ≤ Algebra.trdeg k (IsLocalRing.ResidueField 𝒪) + 1) :
    𝒪.HasLocalUniformization k := by
  classical
  have hk : ∀ x : k, algebraMap k F x ∈ 𝒪 := fun x => by
    rw [IsScalarTower.algebraMap_apply k 𝒪 F]
    exact (algebraMap k 𝒪 x).2
  have hlift_aeval : ∀ {ι : Type} (f : ι → 𝒪) (P : MvPolynomial ι k),
      ((MvPolynomial.aeval f P : 𝒪) : F) = MvPolynomial.aeval (fun i => (f i : F)) P := by
    intro ι f P
    induction P using MvPolynomial.induction_on with
    | C a =>
      simp only [MvPolynomial.aeval_C]
      exact (IsScalarTower.algebraMap_apply k 𝒪 F a).symm
    | add p q hp hq =>
      rw [map_add, map_add]
      exact congrArg₂ (· + ·) hp hq
    | mul_X p i hp =>
      rw [map_mul, map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_X]
      exact congrArg (· * (f i : F)) hp
  have hres_aeval : ∀ {ι : Type} (f : ι → 𝒪) (P : MvPolynomial ι k),
      IsLocalRing.residue 𝒪 (MvPolynomial.aeval f P) =
        MvPolynomial.aeval (fun i => IsLocalRing.residue 𝒪 (f i)) P := by
    intro ι f P
    induction P using MvPolynomial.induction_on with
    | C a =>
      rw [MvPolynomial.aeval_C, MvPolynomial.aeval_C]
      exact (IsScalarTower.algebraMap_apply k 𝒪 (IsLocalRing.ResidueField 𝒪) a).symm
    | add p q hp hq =>
      rw [map_add, map_add, map_add, hp, hq]
    | mul_X p i hp =>
      rw [map_mul, map_mul, map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_X, hp]
  have htr_res_le : Algebra.trdeg k (IsLocalRing.ResidueField 𝒪) ≤ Algebra.trdeg k F := by
    obtain ⟨s, hs⟩ := exists_isTranscendenceBasis k (IsLocalRing.ResidueField 𝒪)
    rw [← hs.cardinalMk_eq_trdeg]
    have hlift : ∀ x : s, ∃ y : 𝒪, IsLocalRing.residue 𝒪 y = x.1 := fun x =>
      Ideal.Quotient.mk_surjective x.1
    choose lift hlift_eq using hlift
    have hindep : AlgebraicIndependent k (fun x : s => (lift x : F)) := by
      rw [algebraicIndependent_iff_injective_aeval, injective_iff_map_eq_zero]
      intro P hP
      have hP_O : MvPolynomial.aeval lift P = 0 := by
        apply Subtype.ext
        rw [hlift_aeval lift P, hP]
        rfl
      have hP_res : MvPolynomial.aeval ((↑) : s → IsLocalRing.ResidueField 𝒪) P = 0 := by
        have hmap := congrArg (IsLocalRing.residue 𝒪) hP_O
        rw [map_zero, hres_aeval lift P] at hmap
        have hfun : (fun x : s => IsLocalRing.residue 𝒪 (lift x)) = ((↑) : s → IsLocalRing.ResidueField 𝒪) :=
          funext hlift_eq
        rwa [hfun] at hmap
      exact (algebraicIndependent_iff_injective_aeval.mp hs.1) (by simpa using hP_res)
    exact hindep.cardinalMk_le_trdeg
  have hFinRes : FinTrdeg k (IsLocalRing.ResidueField 𝒪) :=
    FinTrdeg.of_trdeg (htr_res_le.trans_lt (trdeg_lt_aleph0 k F))
  obtain ⟨sRes, hsRes⟩ := exists_finset_isTranscendenceBasis k (IsLocalRing.ResidueField 𝒪)
  have hlift : ∀ x : sRes, ∃ y : 𝒪, IsLocalRing.residue 𝒪 y = x.1 := fun x =>
    Ideal.Quotient.mk_surjective x.1
  choose t ht_res using hlift
  have ht_indep : AlgebraicIndependent k (fun x : sRes => (t x : F)) := by
    rw [algebraicIndependent_iff_injective_aeval, injective_iff_map_eq_zero]
    intro P hP
    have hP_O : MvPolynomial.aeval t P = 0 := by
      apply Subtype.ext
      rw [hlift_aeval t P, hP]
      rfl
    have hP_res : MvPolynomial.aeval ((↑) : sRes → IsLocalRing.ResidueField 𝒪) P = 0 := by
      have hmap := congrArg (IsLocalRing.residue 𝒪) hP_O
      rw [map_zero, hres_aeval t P] at hmap
      have hfun : (fun x : sRes => IsLocalRing.residue 𝒪 (t x)) = ((↑) : sRes → IsLocalRing.ResidueField 𝒪) :=
        funext ht_res
      rwa [hfun] at hmap
    exact (algebraicIndependent_iff_injective_aeval.mp hsRes.1) (by simpa using hP_res)
  let A_base : Subalgebra k F := Algebra.adjoin k (Set.range fun x : sRes => (t x : F))
  let K₁ : IntermediateField k F := IntermediateField.adjoin k (Set.range fun x : sRes => (t x : F))
  have hA_base_in_O : ∀ a : A_base, (a : F) ∈ 𝒪 := by
    rintro ⟨a, ha⟩
    refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ ha
    · rintro _ ⟨i, rfl⟩; exact (t i).2
    · intro c; exact hk c
    · intro x y _ _ hx hy; exact add_mem hx hy
    · intro x y _ _ hx hy; exact mul_mem hx hy
  have hA_base_unit : ∀ a : A_base, (a : F) ≠ 0 → IsUnit (⟨(a : F), hA_base_in_O a⟩ : 𝒪) := by
    intro a ha0
    have hmem : (a : F) ∈ (MvPolynomial.aeval (R := k) (fun x : sRes => (t x : F))).range := by
      rw [MvPolynomial.aeval_range]
      exact a.2
    obtain ⟨P, hP⟩ := hmem
    have hP0 : P ≠ 0 := fun h0 => ha0 (by rw [← hP, h0, map_zero])
    have hres_ne : IsLocalRing.residue 𝒪 ⟨(a : F), hA_base_in_O a⟩ ≠ 0 := by
      have heq_O : (⟨(a : F), hA_base_in_O a⟩ : 𝒪) = MvPolynomial.aeval t P := by
        apply Subtype.ext
        rw [hlift_aeval t P]
        exact hP.symm
      rw [heq_O, hres_aeval t P]
      have hfun : (fun x : sRes => IsLocalRing.residue 𝒪 (t x)) = ((↑) : sRes → IsLocalRing.ResidueField 𝒪) :=
        funext ht_res
      rw [hfun]
      intro h0
      exact hP0 ((algebraicIndependent_iff_injective_aeval.mp hsRes.1) (by simpa using h0))
    rw [← notMem_maximalIdeal]
    intro hm
    exact hres_ne ((IsLocalRing.residue_eq_zero_iff _).mpr hm)
  have hA_base_le_K₁ : A_base ≤ K₁.toSubalgebra := IntermediateField.algebra_adjoin_le_adjoin k _
  have hK₁_frac : ∀ x : K₁, ∃ a b : A_base, (b : F) ≠ 0 ∧ (b : F) * (x : F) = (a : F) := by
    have htop : IntermediateField.adjoin k (A_base : Set F) = K₁ := by
      apply le_antisymm
      · exact IntermediateField.adjoin_le_iff.mpr hA_base_le_K₁
      · exact IntermediateField.adjoin_le_iff.mpr fun _ hx =>
          IntermediateField.subset_adjoin k (A_base : Set F) (Algebra.subset_adjoin hx)
    let S : IntermediateField k F :=
      { carrier := { x : F | ∃ (a b : A_base), (b : F) ≠ 0 ∧ (b : F) * x = (a : F) }
        mul_mem' := by
          rintro x y ⟨a₁, b₁, hb₁, h₁⟩ ⟨a₂, b₂, hb₂, h₂⟩
          refine ⟨a₁ * a₂, b₁ * b₂, mul_ne_zero hb₁ hb₂, ?_⟩
          push_cast
          calc ((b₁ : F) * (b₂ : F)) * (x * y) = ((b₁ : F) * x) * ((b₂ : F) * y) := by ring
            _ = (a₁ : F) * (a₂ : F) := by rw [h₁, h₂]
        one_mem' := ⟨1, 1, one_ne_zero, by simp⟩
        add_mem' := by
          rintro x y ⟨a₁, b₁, hb₁, h₁⟩ ⟨a₂, b₂, hb₂, h₂⟩
          refine ⟨a₁ * b₂ + a₂ * b₁, b₁ * b₂, mul_ne_zero hb₁ hb₂, ?_⟩
          push_cast
          calc ((b₁ : F) * (b₂ : F)) * (x + y)
              = ((b₁ : F) * x) * (b₂ : F) + ((b₂ : F) * y) * (b₁ : F) := by ring
            _ = (a₁ : F) * (b₂ : F) + (a₂ : F) * (b₁ : F) := by rw [h₁, h₂]
        zero_mem' := ⟨0, 1, one_ne_zero, by simp⟩
        inv_mem' := by
          rintro x ⟨a, b, hb, h⟩
          by_cases hx : x = 0
          · subst hx; exact ⟨0, 1, one_ne_zero, by simp⟩
          · have ha0 : (a : F) ≠ 0 := by rw [← h]; exact mul_ne_zero hb hx
            refine ⟨b, a, ha0, ?_⟩
            calc (a : F) * x⁻¹ = ((b : F) * x) * x⁻¹ := by rw [h]
              _ = (b : F) := by rw [mul_assoc, mul_inv_cancel₀ hx, mul_one]
        algebraMap_mem' := fun c => ⟨algebraMap k A_base c, 1, one_ne_zero, by simp⟩ }
    have hleS : K₁ ≤ S := by
      rw [← htop, IntermediateField.adjoin_le_iff]
      intro x hx
      exact ⟨⟨x, hx⟩, 1, one_ne_zero, by simp⟩
    intro x
    exact hleS x.2
  have hK₁_in_O : ∀ x : K₁, (x : F) ∈ 𝒪 := by
    intro x
    obtain ⟨a, b, hb0, hab⟩ := hK₁_frac x
    have hbu := hA_base_unit b hb0
    obtain ⟨u, hu⟩ := isUnit_iff_exists_inv.mp hbu
    have huF : (b : F) * (u : F) = 1 := congrArg Subtype.val hu
    have hx_eq : (x : F) = (a : F) * (u : F) := by
      calc (x : F) = 1 * (x : F) := (one_mul _).symm
        _ = ((u : F) * (b : F)) * (x : F) := by rw [mul_comm (u : F), huF]
        _ = (u : F) * ((b : F) * (x : F)) := by rw [mul_assoc]
        _ = (a : F) * (u : F) := by rw [hab, mul_comm]
    rw [hx_eq]
    exact mul_mem (hA_base_in_O a) u.2
  have htr_K₁ : Algebra.trdeg k K₁ = Algebra.trdeg k (IsLocalRing.ResidueField 𝒪) := by
    have htK₁_val : ∀ P : MvPolynomial sRes k,
        K₁.val (MvPolynomial.aeval (fun x : sRes => (⟨(t x : F),
          IntermediateField.subset_adjoin k _ ⟨x, rfl⟩⟩ : K₁)) P) =
          MvPolynomial.aeval (fun x : sRes => (t x : F)) P := by
      intro P
      induction P using MvPolynomial.induction_on with
      | C c => simp
      | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
      | mul_X p i hp => rw [map_mul, map_mul, map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_X, hp]; rfl
    have htK₁_indep : AlgebraicIndependent k (fun x : sRes => (⟨(t x : F),
        IntermediateField.subset_adjoin k _ ⟨x, rfl⟩⟩ : K₁)) := by
      rw [algebraicIndependent_iff_injective_aeval] at ht_indep ⊢
      intro p q hpq
      apply ht_indep
      have h1 := congrArg K₁.val hpq
      rwa [htK₁_val p, htK₁_val q] at h1
    have htK₁_alg : Algebra.IsAlgebraic
        (Algebra.adjoin k (Set.range fun x : sRes => (⟨(t x : F),
          IntermediateField.subset_adjoin k _ ⟨x, rfl⟩⟩ : K₁))) K₁ := by
      refine ⟨fun x => ?_⟩
      obtain ⟨a, b, hb0, hab⟩ := hK₁_frac x
      have hsub : ∀ z : A_base,
          (⟨(z : F), hA_base_le_K₁ z.2⟩ : K₁) ∈
            Algebra.adjoin k (Set.range fun y : sRes => (⟨(t y : F),
              IntermediateField.subset_adjoin k _ ⟨y, rfl⟩⟩ : K₁)) := by
        rintro ⟨z, hz⟩
        refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hz
        · rintro _ ⟨i, rfl⟩
          exact Algebra.subset_adjoin ⟨i, rfl⟩
        · intro c
          exact Subalgebra.algebraMap_mem _ c
        · intro u v _ _ h1 h2; exact add_mem h1 h2
        · intro u v _ _ h1 h2; exact mul_mem h1 h2
      let a' : Algebra.adjoin k (Set.range fun y : sRes => (⟨(t y : F),
          IntermediateField.subset_adjoin k _ ⟨y, rfl⟩⟩ : K₁)) := ⟨⟨a.1, hA_base_le_K₁ a.2⟩, hsub a⟩
      let b' : Algebra.adjoin k (Set.range fun y : sRes => (⟨(t y : F),
          IntermediateField.subset_adjoin k _ ⟨y, rfl⟩⟩ : K₁)) := ⟨⟨b.1, hA_base_le_K₁ b.2⟩, hsub b⟩
      refine ⟨Polynomial.C b' * Polynomial.X - Polynomial.C a', ?_, ?_⟩
      · intro h0
        have h1 := congrArg (fun p => Polynomial.coeff p 1) h0
        simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_X_one, mul_one,
          Polynomial.coeff_C_succ, sub_zero, Polynomial.coeff_zero] at h1
        exact hb0 (congrArg (fun u => ((u.1 : K₁) : F)) h1)
      · simp only [map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X]
        apply Subtype.ext
        change (b : F) * (x : F) - (a : F) = 0
        rw [hab, sub_self]
    have htb : IsTranscendenceBasis k (fun x : sRes => (⟨(t x : F),
        IntermediateField.subset_adjoin k _ ⟨x, rfl⟩⟩ : K₁)) :=
      (isTranscendenceBasis_iff_algebraicIndependent_isAlgebraic.mpr ⟨htK₁_indep, htK₁_alg⟩)
    rw [← htb.cardinalMk_eq_trdeg, hsRes.cardinalMk_eq_trdeg]
  have htr_K₁_F_le : Algebra.trdeg K₁ F ≤ 1 := by
    have hadd : Algebra.trdeg k K₁ + Algebra.trdeg K₁ F = Algebra.trdeg k F := trdeg_add_eq k K₁
    rw [htr_K₁] at hadd
    have hlt_res : Algebra.trdeg k (IsLocalRing.ResidueField 𝒪) < Cardinal.aleph0 :=
      trdeg_lt_aleph0 k (IsLocalRing.ResidueField 𝒪)
    have hlt_F : Algebra.trdeg k F < Cardinal.aleph0 := trdeg_lt_aleph0 k F
    obtain ⟨n, hn⟩ := Cardinal.lt_aleph0.mp hlt_res
    obtain ⟨m, hm⟩ := Cardinal.lt_aleph0.mp hlt_F
    have hlt_rel : Algebra.trdeg K₁ F < Cardinal.aleph0 := by
      have : Algebra.trdeg K₁ F ≤ Algebra.trdeg k F := by rw [← hadd]; exact le_add_self
      exact this.trans_lt hlt_F
    obtain ⟨r, hr⟩ := Cardinal.lt_aleph0.mp hlt_rel
    rw [hn, hr, hm] at hadd
    rw [hn, hm] at hle
    have hadd_nat : n + r = m := by exact_mod_cast hadd
    have hle_nat : m ≤ n + 1 := by exact_mod_cast hle
    have hr_le : r ≤ 1 := by omega
    rw [hr]
    exact_mod_cast hr_le
  have : Algebra.EssFiniteType K₁ F := Algebra.EssFiniteType.of_comp k K₁ F
  have : CharZero K₁ := charZero_of_injective_algebraMap (algebraMap k K₁).injective
  have hLU_K₁ : 𝒪.HasLocalUniformization K₁ := by
    have hlt_rel : Algebra.trdeg K₁ F < Cardinal.aleph0 := trdeg_lt_aleph0 K₁ F
    obtain ⟨r, hr⟩ := Cardinal.lt_aleph0.mp hlt_rel
    rw [hr] at htr_K₁_F_le
    have hr_le : r ≤ 1 := by exact_mod_cast htr_K₁_F_le
    by_cases hr0 : r = 0
    · have halg : Algebra.IsAlgebraic K₁ F := trdeg_eq_zero_iff.mp (by rw [hr, hr0]; simp)
      exact hasLocalUniformization_of_isAlgebraic K₁ F 𝒪 hK₁_in_O halg
    · have hr1 : r = 1 := by omega
      exact hasLocalUniformization_of_trdeg_eq_one K₁ F 𝒪 hK₁_in_O (by rw [hr, hr1]; simp)
  obtain ⟨B₁, hB₁_in, hB₁_fin, hB₁_frac, hB₁_reg⟩ := hLU_K₁
  obtain ⟨u, hu⟩ := hB₁_fin.out
  let genSet : Finset F := (Finset.univ.image fun x : sRes => (t x : F)) ∪ u.image Subtype.val
  let A : Subalgebra k F := Algebra.adjoin k (genSet : Set F)
  have hA_in_O : ∀ a : A, (a : F) ∈ 𝒪 := by
    rintro ⟨a, ha⟩
    refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ ha
    · intro x hx
      rw [Finset.mem_coe, Finset.mem_union] at hx
      rcases hx with hx | hx
      · rw [Finset.mem_image] at hx; obtain ⟨i, _, rfl⟩ := hx; exact (t i).2
      · rw [Finset.mem_image] at hx; obtain ⟨b, _, rfl⟩ := hx; exact hB₁_in b
    · intro c; exact hk c
    · intro x y _ _ hx hy; exact add_mem hx hy
    · intro x y _ _ hx hy; exact mul_mem hx hy
  have hA_fin : Algebra.FiniteType k A := Algebra.FiniteType.adjoin_of_finite genSet.finite_toSet
  have hA_le_B₁ : (A : Set F) ⊆ (B₁ : Set F) := by
    intro x hx
    refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hx
    · intro y hy
      rw [Finset.mem_coe, Finset.mem_union] at hy
      rcases hy with hy | hy
      · rw [Finset.mem_image] at hy
        obtain ⟨i, _, rfl⟩ := hy
        have hti : (t i : F) ∈ K₁ := IntermediateField.subset_adjoin k _ ⟨i, rfl⟩
        exact B₁.algebraMap_mem ⟨(t i : F), hti⟩
      · rw [Finset.mem_image] at hy
        obtain ⟨b, _, rfl⟩ := hy
        exact b.2
    · intro c
      exact B₁.algebraMap_mem (algebraMap k K₁ c)
    · intro x y _ _ hx hy; exact B₁.add_mem hx hy
    · intro x y _ _ hx hy; exact B₁.mul_mem hx hy
  have hA_base_le_A : (A_base : Set F) ⊆ (A : Set F) := by
    intro x hx
    refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨i, rfl⟩
      apply Algebra.subset_adjoin
      rw [Finset.mem_coe, Finset.mem_union]
      exact Or.inl (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
    · intro c; exact A.algebraMap_mem c
    · intro x y _ _ hx hy; exact A.add_mem hx hy
    · intro x y _ _ hx hy; exact A.mul_mem hx hy
  have hB₁_clear : ∀ b : B₁, ∃ (a : A) (s : A_base),
      (s : F) ≠ 0 ∧ (s : F) * (b : F) = (a : F) := by
    intro b
    have hb_mem : b ∈ Algebra.adjoin K₁ (u : Set B₁) := by rw [hu]; trivial
    refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hb_mem
    · intro x hx
      refine ⟨⟨(x : F), Algebra.subset_adjoin ?_⟩, 1, one_ne_zero, by simp⟩
      rw [Finset.mem_coe, Finset.mem_union]
      exact Or.inr (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
    · intro c
      obtain ⟨a, s, hs0, has⟩ := hK₁_frac c
      exact ⟨⟨(a : F), hA_base_le_A a.2⟩, s, hs0, has⟩
    · rintro x y _ _ ⟨a₁, s₁, hs₁, h₁⟩ ⟨a₂, s₂, hs₂, h₂⟩
      refine ⟨a₁ * ⟨(s₂ : F), hA_base_le_A s₂.2⟩ + a₂ * ⟨(s₁ : F), hA_base_le_A s₁.2⟩,
        s₁ * s₂, mul_ne_zero hs₁ hs₂, ?_⟩
      push_cast
      calc ((s₁ : F) * (s₂ : F)) * ((x : F) + (y : F))
          = ((s₁ : F) * (x : F)) * (s₂ : F) + ((s₂ : F) * (y : F)) * (s₁ : F) := by ring
        _ = (a₁ : F) * (s₂ : F) + (a₂ : F) * (s₁ : F) := by rw [h₁, h₂]
    · rintro x y _ _ ⟨a₁, s₁, hs₁, h₁⟩ ⟨a₂, s₂, hs₂, h₂⟩
      refine ⟨a₁ * a₂, s₁ * s₂, mul_ne_zero hs₁ hs₂, ?_⟩
      push_cast
      calc ((s₁ : F) * (s₂ : F)) * ((x : F) * (y : F))
          = ((s₁ : F) * (x : F)) * ((s₂ : F) * (y : F)) := by ring
        _ = (a₁ : F) * (a₂ : F) := by rw [h₁, h₂]
  have hA_frac : IsFractionRing A F := by
    refine ⟨?_, ?_, ?_⟩
    · intro y
      have hy : (y : A) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp y.2
      exact isUnit_iff_ne_zero.mpr fun h0 => hy (Subtype.ext h0)
    · intro x
      obtain ⟨⟨b, c⟩, hbc⟩ := IsLocalization.surj (nonZeroDivisors B₁) x
      have hc0 : (c : B₁) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp c.2
      obtain ⟨ab, sb, hsb0, hab⟩ := hB₁_clear b
      obtain ⟨ac, sc, hsc0, hac⟩ := hB₁_clear c
      have hac0 : (ac : F) ≠ 0 := by
        rw [← hac]
        exact mul_ne_zero hsc0 fun h0 => hc0 (Subtype.ext h0)
      let den : A := ac * ⟨(sb : F), hA_base_le_A sb.2⟩
      have hden0 : den ≠ 0 := by
        intro h0
        have hF : (ac : F) * (sb : F) = 0 := congrArg Subtype.val h0
        exact mul_ne_zero hac0 hsb0 hF
      refine ⟨(ab * ⟨(sc : F), hA_base_le_A sc.2⟩, ⟨den, mem_nonZeroDivisors_iff_ne_zero.mpr hden0⟩), ?_⟩
      change x * ((ac : F) * (sb : F)) = (ab : F) * (sc : F)
      have hbcF : x * (c : B₁).1 = (b : F) := hbc
      calc x * ((ac : F) * (sb : F))
          = x * (((sc : F) * (c : B₁).1) * (sb : F)) := by rw [hac]
        _ = (sc : F) * (sb : F) * (x * (c : B₁).1) := by ring
        _ = (sc : F) * ((sb : F) * (b : F)) := by rw [hbcF]; ring
        _ = (ab : F) * (sc : F) := by rw [hab, mul_comm]
    · intro x y hxy
      exact ⟨1, by simp [Subtype.ext (show (x : F) = (y : F) from hxy)]⟩
  let ι : A →+* B₁ :=
    { toFun := fun a => ⟨(a : F), hA_le_B₁ a.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hcomap : (𝒪.centerOn B₁ hB₁_in).comap ι = 𝒪.centerOn A hA_in_O := by
    ext a
    rw [Ideal.mem_comap, mem_centerOn_iff_zero_or_inv_notMem, mem_centerOn_iff_zero_or_inv_notMem]
    rfl
  have hpc_le : (𝒪.centerOn A hA_in_O).primeCompl ≤
      Submonoid.comap ι.toMonoidHom (𝒪.centerOn B₁ hB₁_in).primeCompl := by
    intro a ha
    change ι a ∉ 𝒪.centerOn B₁ hB₁_in
    intro hmem
    exact ha (by rw [← hcomap]; exact hmem)
  let φ : Localization.AtPrime (𝒪.centerOn A hA_in_O) →+*
      Localization.AtPrime (𝒪.centerOn B₁ hB₁_in) :=
    IsLocalization.map (Localization.AtPrime (𝒪.centerOn B₁ hB₁_in)) ι hpc_le
  have hφ_inj : Function.Injective φ := by
    have hA_toF : (𝒪.centerOn A hA_in_O).primeCompl ≤ nonZeroDivisors A := fun a ha =>
      mem_nonZeroDivisors_iff_ne_zero.mpr fun h0 => ha (h0 ▸ Ideal.zero_mem _)
    have hB₁_toF : (𝒪.centerOn B₁ hB₁_in).primeCompl ≤ nonZeroDivisors B₁ := fun b hb =>
      mem_nonZeroDivisors_iff_ne_zero.mpr fun h0 => hb (h0 ▸ Ideal.zero_mem _)
    let fA : Localization.AtPrime (𝒪.centerOn A hA_in_O) →+* F :=
      IsLocalization.lift (M := (𝒪.centerOn A hA_in_O).primeCompl) (g := algebraMap A F)
        (fun y => IsLocalization.map_units F ⟨y.1, hA_toF y.2⟩)
    let fB : Localization.AtPrime (𝒪.centerOn B₁ hB₁_in) →+* F :=
      IsLocalization.lift (M := (𝒪.centerOn B₁ hB₁_in).primeCompl) (g := algebraMap B₁ F)
        (fun y => IsLocalization.map_units F ⟨y.1, hB₁_toF y.2⟩)
    have hfA_mk : ∀ (a : A) (s : (𝒪.centerOn A hA_in_O).primeCompl),
        fA (IsLocalization.mk' _ a s) * (s.1 : F) = (a : F) := by
      intro a s
      have h1 : fA (algebraMap A (Localization.AtPrime (𝒪.centerOn A hA_in_O)) s.1) = (s.1 : F) :=
        IsLocalization.lift_eq _ s.1
      rw [← h1, ← map_mul, mul_comm, IsLocalization.mk'_spec']
      exact IsLocalization.lift_eq _ a
    have hfA_inj : Function.Injective fA := by
      intro x y hxy
      obtain ⟨a₁, s₁, rfl⟩ := IsLocalization.exists_mk'_eq (𝒪.centerOn A hA_in_O).primeCompl x
      obtain ⟨a₂, s₂, rfl⟩ := IsLocalization.exists_mk'_eq (𝒪.centerOn A hA_in_O).primeCompl y
      rw [IsLocalization.mk'_eq_iff_eq]
      have heq : (s₂.1 : F) * (a₁ : F) = (s₁.1 : F) * (a₂ : F) := by
        calc (s₂.1 : F) * (a₁ : F)
            = (s₂.1 : F) * (fA (IsLocalization.mk' _ a₁ s₁) * (s₁.1 : F)) := by rw [hfA_mk]
          _ = (s₁.1 : F) * (fA (IsLocalization.mk' _ a₂ s₂) * (s₂.1 : F)) := by rw [hxy]; ring
          _ = (s₁.1 : F) * (a₂ : F) := by rw [hfA_mk]
      have hAeq : (s₂ : A) * a₁ = (s₁ : A) * a₂ := Subtype.ext heq
      rw [hAeq]
    have hcomp : fB.comp φ = fA := by
      apply IsLocalization.ringHom_ext (𝒪.centerOn A hA_in_O).primeCompl
      ext a
      change fB (φ (algebraMap A _ a)) = fA (algebraMap A _ a)
      have h1 : φ (algebraMap A (Localization.AtPrime (𝒪.centerOn A hA_in_O)) a) =
          algebraMap B₁ (Localization.AtPrime (𝒪.centerOn B₁ hB₁_in)) (ι a) :=
        IsLocalization.map_eq hpc_le a
      have h2 : fB (algebraMap B₁ (Localization.AtPrime (𝒪.centerOn B₁ hB₁_in)) (ι a)) = (a : F) :=
        IsLocalization.lift_eq _ (ι a)
      have h3 : fA (algebraMap A (Localization.AtPrime (𝒪.centerOn A hA_in_O)) a) = (a : F) :=
        IsLocalization.lift_eq _ a
      rw [h1, h2, h3]
    intro x y hxy
    apply hfA_inj
    rw [← hcomp, RingHom.comp_apply, RingHom.comp_apply, hxy]
  have hφ_surj : Function.Surjective φ := by
    intro z
    obtain ⟨b, c, rfl⟩ := IsLocalization.exists_mk'_eq (𝒪.centerOn B₁ hB₁_in).primeCompl z
    obtain ⟨ab, sb, hsb0, hab⟩ := hB₁_clear b
    obtain ⟨ac, sc, hsc0, hac⟩ := hB₁_clear c.1
    have hsbA_nmem : (⟨(sb : F), hA_base_le_A sb.2⟩ : A) ∉ 𝒪.centerOn A hA_in_O := by
      change (⟨(sb : F), hA_base_in_O sb⟩ : 𝒪) ∉ maximalIdeal 𝒪
      rw [notMem_maximalIdeal]
      exact hA_base_unit sb hsb0
    have hscA_nmem : (⟨(sc : F), hA_base_le_A sc.2⟩ : A) ∉ 𝒪.centerOn A hA_in_O := by
      change (⟨(sc : F), hA_base_in_O sc⟩ : 𝒪) ∉ maximalIdeal 𝒪
      rw [notMem_maximalIdeal]
      exact hA_base_unit sc hsc0
    have hac_nmem : ac ∉ 𝒪.centerOn A hA_in_O := by
      intro hmem
      have hmemB : ι ac ∈ 𝒪.centerOn B₁ hB₁_in := by rw [← hcomap] at hmem; exact hmem
      have hsc_nmemB : ι ⟨(sc : F), hA_base_le_A sc.2⟩ ∉ 𝒪.centerOn B₁ hB₁_in := fun h =>
        hscA_nmem (by rw [← hcomap]; exact h)
      have heqB : ι ac = ι ⟨(sc : F), hA_base_le_A sc.2⟩ * c.1 := Subtype.ext hac.symm
      rw [heqB] at hmemB
      rcases (inferInstance : (𝒪.centerOn B₁ hB₁_in).IsPrime).mem_or_mem hmemB with h1 | h2
      · exact hsc_nmemB h1
      · exact c.2 h2
    let numA : A := ab * ⟨(sc : F), hA_base_le_A sc.2⟩
    let denA : A := ac * ⟨(sb : F), hA_base_le_A sb.2⟩
    have hdenA_mem : denA ∈ (𝒪.centerOn A hA_in_O).primeCompl :=
      (𝒪.centerOn A hA_in_O).primeCompl.mul_mem hac_nmem hsbA_nmem
    refine ⟨IsLocalization.mk' _ numA ⟨denA, hdenA_mem⟩, ?_⟩
    have hmap_mk : φ (IsLocalization.mk' (Localization.AtPrime (𝒪.centerOn A hA_in_O))
        numA ⟨denA, hdenA_mem⟩) =
        IsLocalization.mk' (Localization.AtPrime (𝒪.centerOn B₁ hB₁_in))
          (ι numA) ⟨ι denA, hpc_le hdenA_mem⟩ :=
      IsLocalization.map_mk' hpc_le numA ⟨denA, hdenA_mem⟩
    rw [hmap_mk, IsLocalization.mk'_eq_iff_eq]
    have heqB : c.1 * ι numA = ι denA * b := by
      apply Subtype.ext
      change (c.1 : F) * ((ab : F) * (sc : F)) = ((ac : F) * (sb : F)) * (b : F)
      calc (c.1 : F) * ((ab : F) * (sc : F))
          = (ab : F) * ((sc : F) * (c.1 : F)) := by ring
        _ = (ab : F) * (ac : F) := by rw [hac]
        _ = ((sb : F) * (b : F)) * (ac : F) := by rw [hab]
        _ = ((ac : F) * (sb : F)) * (b : F) := by ring
    exact congrArg (algebraMap B₁ (Localization.AtPrime (𝒪.centerOn B₁ hB₁_in))) heqB
  let eLoc : Localization.AtPrime (𝒪.centerOn A hA_in_O) ≃+*
      Localization.AtPrime (𝒪.centerOn B₁ hB₁_in) :=
    RingEquiv.ofBijective φ ⟨hφ_inj, hφ_surj⟩
  have hA_reg : IsRegularLocalRing (Localization.AtPrime (𝒪.centerOn A hA_in_O)) :=
    @IsRegularLocalRing.of_ringEquiv _ _ hB₁_reg _ _ eLoc.symm
  exact ⟨A, hA_in_O, hA_fin, hA_frac, hA_reg⟩

/- Section 3: Base-change preservation of IsRegularLocalRing in characteristic zero -/

private lemma ringKrullDim_le_of_flat_local
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)] [Module.Flat R S] :
    ringKrullDim R ≤ ringKrullDim S := by
  rw [ringKrullDim, ringKrullDim, Order.krullDim, Order.krullDim]
  refine iSup_le fun c => ?_
  have hmax : (maximalIdeal S).comap (algebraMap R S) = maximalIdeal R :=
    IsLocalRing.maximalIdeal_comap (algebraMap R S)
  have hlast_le : c.last.asIdeal ≤ maximalIdeal R :=
    IsLocalRing.le_maximalIdeal c.last.isPrime.ne_top
  by_cases heq : c.last.asIdeal = maximalIdeal R
  · have hlo : (maximalIdeal S).LiesOver c.last.asIdeal := ⟨by rw [heq, ← hmax]⟩
    obtain ⟨L, hL_len, _, _⟩ := Ideal.exists_ltSeries_of_hasGoingDown c (maximalIdeal S)
    exact le_iSup_of_le L (by simp [hL_len])
  · have hlt : c.last < (⟨maximalIdeal R, (maximalIdeal.isMaximal R).isPrime⟩ : PrimeSpectrum R) :=
      lt_of_le_of_ne hlast_le fun h => heq (congrArg PrimeSpectrum.asIdeal h)
    let c1 : LTSeries (PrimeSpectrum R) :=
      c.snoc ⟨maximalIdeal R, (maximalIdeal.isMaximal R).isPrime⟩ hlt
    have hlo : (maximalIdeal S).LiesOver c1.last.asIdeal := ⟨by
      show c1.last.asIdeal = (maximalIdeal S).comap (algebraMap R S)
      have hlast : c1.last.asIdeal = maximalIdeal R := by simp [c1]
      exact hlast.trans hmax.symm⟩
    obtain ⟨L, hL_len, _, _⟩ := Ideal.exists_ltSeries_of_hasGoingDown c1 (maximalIdeal S)
    refine le_iSup_of_le L ?_
    have hlen : c.length ≤ L.length := by
      rw [hL_len]
      simp [c1]
    exact WithBot.coe_le_coe.mpr (ENat.natCast_le_natCast.mpr hlen)

private lemma isRegularLocalRing_of_flat_local_map_maximalIdeal
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing S] [IsNoetherianRing S]
    [IsLocalHom (algebraMap R S)] [Module.Flat R S] [IsRegularLocalRing R]
    (hmax : (maximalIdeal R).map (algebraMap R S) = maximalIdeal S) :
    IsRegularLocalRing S := by
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  have hreg : ((maximalIdeal R).spanFinrank : WithBot ℕ∞) = ringKrullDim R :=
    (isRegularLocalRing_iff R).mp inferInstance
  have hdim : ringKrullDim R ≤ ringKrullDim S := ringKrullDim_le_of_flat_local
  refine le_trans ?_ (hreg.symm ▸ hdim)
  have fg' := (maximalIdeal R).fg_of_isNoetherianRing
  have fg := Submodule.FG.finite_generators fg'
  have hspan : Ideal.span (algebraMap R S '' (maximalIdeal R).generators) = maximalIdeal S := by
    rw [← Ideal.map_span, Ideal.span, (maximalIdeal R).span_generators, hmax]
  have hle_nat : (maximalIdeal S).spanFinrank ≤ (maximalIdeal R).spanFinrank := by
    rw [← hspan, ← Submodule.FG.generators_ncard fg']
    exact (Submodule.spanFinrank_span_le_ncard_of_finite (fg.image _)).trans
      (Set.ncard_image_le fg)
  exact_mod_cast hle_nat

private lemma isRegularLocalRing_adjoinRoot_monic_separable
    {K R : Type*} [Field K] [CommRing R] [Algebra K R] [IsRegularLocalRing R]
    (f : K[X]) (hf_monic : f.Monic) (hf_sep : IsCoprime f (Polynomial.derivative f))
    (Q : Ideal (AdjoinRoot (f.map (algebraMap K R)))) [Q.IsPrime]
    (hQ : Q.comap (algebraMap R (AdjoinRoot (f.map (algebraMap K R)))) = maximalIdeal R) :
    IsRegularLocalRing (Localization.AtPrime Q) := by
  classical
  let fR : R[X] := f.map (algebraMap K R)
  have hfR_monic : fR.Monic := hf_monic.map (algebraMap K R)
  let S := AdjoinRoot fR
  have : Module.Free R S := hfR_monic.free_adjoinRoot
  have : Module.Flat R S := inferInstance
  have : IsNoetherianRing S :=
    isNoetherianRing_of_surjective R[X] S (AdjoinRoot.mk fR) Ideal.Quotient.mk_surjective
  have : Module.Flat R (Localization.AtPrime Q) :=
    Module.Flat.trans R S (Localization.AtPrime Q)
  have : IsLocalHom (algebraMap R (Localization.AtPrime Q)) := by
    refine ⟨fun r hr => ?_⟩
    by_contra hnu
    have hrm : r ∈ maximalIdeal R := (IsLocalRing.mem_maximalIdeal r).mpr hnu
    have hrQ : algebraMap R S r ∈ Q := by
      rw [← hQ] at hrm
      exact hrm
    have hrLoc : algebraMap R (Localization.AtPrime Q) r ∈
        maximalIdeal (Localization.AtPrime Q) := by
      rw [IsScalarTower.algebraMap_apply R S (Localization.AtPrime Q),
        ← Localization.AtPrime.map_eq_maximalIdeal]
      exact Ideal.mem_map_of_mem _ hrQ
    exact (IsLocalRing.mem_maximalIdeal _).mp hrLoc hr
  apply isRegularLocalRing_of_flat_local_map_maximalIdeal (R := R) (S := Localization.AtPrime Q)
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap, IsLocalRing.maximalIdeal_comap]
  · rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_le_iff_le_comap]
    intro q hq
    let κ := IsLocalRing.ResidueField R
    let π : R[X] →+* κ[X] := Polynomial.mapRingHom (IsLocalRing.residue R)
    have hπ_surj : Function.Surjective π := Polynomial.map_surjective _ Ideal.Quotient.mk_surjective
    let mk : R[X] →+* S := AdjoinRoot.mk fR
    have hmk_surj : Function.Surjective mk := Ideal.Quotient.mk_surjective
    let Q₀ : Ideal R[X] := Q.comap mk
    have : Q₀.IsPrime := Ideal.IsPrime.comap mk
    have hQ₀_C : Q₀.comap Polynomial.C = maximalIdeal R := by
      ext r
      rw [Ideal.mem_comap, Ideal.mem_comap, ← hQ, Ideal.mem_comap]
      rfl
    have hker_le_mapC : RingHom.ker π ≤ (maximalIdeal R).map Polynomial.C := by
      intro p hp
      rw [RingHom.mem_ker] at hp
      rw [Polynomial.as_sum_range_C_mul_X_pow p]
      refine Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ?_)
      have hci : IsLocalRing.residue R (p.coeff i) = 0 := by
        have h1 := congrArg (fun g : κ[X] => g.coeff i) hp
        simpa only [π, Polynomial.coe_mapRingHom, Polynomial.coeff_map, Polynomial.coeff_zero] using h1
      exact (IsLocalRing.residue_eq_zero_iff _).mp hci
    have hker_le_Q₀ : RingHom.ker π ≤ Q₀ :=
      hker_le_mapC.trans (Ideal.map_le_iff_le_comap.mpr hQ₀_C.ge)
    let Qbar : Ideal κ[X] := Q₀.map π
    have hQbar_comap : Qbar.comap π = Q₀ := by
      apply le_antisymm
      · intro p hp
        rw [Ideal.mem_comap] at hp
        have hmem_img : π p ∈ π '' (Q₀ : Set R[X]) := by
          have heq : (Qbar : Set κ[X]) = π '' (Q₀ : Set R[X]) := by
            ext y
            constructor
            · intro hy
              refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
              · rintro _ ⟨a, ha, rfl⟩; exact ⟨a, ha, rfl⟩
              · exact ⟨0, Q₀.zero_mem, map_zero π⟩
              · rintro _ _ _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
                exact ⟨a + b, Q₀.add_mem ha hb, map_add π a b⟩
              · rintro c _ _ ⟨a, ha, rfl⟩
                obtain ⟨c₀, rfl⟩ := hπ_surj c
                exact ⟨c₀ * a, Q₀.mul_mem_left c₀ ha, map_mul π c₀ a⟩
            · rintro ⟨a, ha, rfl⟩; exact Ideal.mem_map_of_mem π ha
          exact heq ▸ hp
        obtain ⟨a, ha, hap⟩ := hmem_img
        have hsub : p - a ∈ RingHom.ker π := by
          rw [RingHom.mem_ker, map_sub, hap, sub_self]
        have hadd : p = (p - a) + a := by ring
        rw [hadd]
        exact Q₀.add_mem (hker_le_Q₀ hsub) ha
      · exact Ideal.le_comap_map
    have hQbar_prime : Qbar.IsPrime := by
      constructor
      · intro htop
        have h1 : (1 : R[X]) ∈ Qbar.comap π := by rw [Ideal.mem_comap, map_one, htop]; trivial
        rw [hQbar_comap] at h1
        exact (inferInstance : Q₀.IsPrime).ne_top (Ideal.eq_top_of_isUnit_mem Q₀ h1 isUnit_one)
      · intro x y hxy
        obtain ⟨x₀, rfl⟩ := hπ_surj x
        obtain ⟨y₀, rfl⟩ := hπ_surj y
        rw [← map_mul] at hxy
        have hmem : x₀ * y₀ ∈ Q₀ := hQbar_comap ▸ hxy
        rcases (inferInstance : Q₀.IsPrime).mem_or_mem hmem with hx | hy
        · exact Or.inl (Ideal.mem_map_of_mem π hx)
        · exact Or.inr (Ideal.mem_map_of_mem π hy)
    let fbar : κ[X] := π fR
    have hfbar_eq : fbar = f.map ((IsLocalRing.residue R).comp (algebraMap K R)) := by
      change fR.map (IsLocalRing.residue R) = _
      dsimp only [fR]
      rw [Polynomial.map_map]
    have hfbar_mem : fbar ∈ Qbar := by
      refine Ideal.mem_map_of_mem π ?_
      change mk fR ∈ Q
      rw [AdjoinRoot.mk_self]
      exact Q.zero_mem
    obtain ⟨gbar, hQbar_span⟩ := IsPrincipalIdealRing.principal Qbar
    have hgbar_nunit : ¬ IsUnit gbar := by
      intro hu
      apply hQbar_prime.ne_top
      rw [hQbar_span]
      exact Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span (Set.mem_singleton gbar)) hu
    have hgbar_dvd_fbar : gbar ∣ fbar := by
      rw [hQbar_span, Ideal.mem_span_singleton] at hfbar_mem
      exact hfbar_mem
    obtain ⟨hbar, hfbar_fac⟩ := hgbar_dvd_fbar
    have hhbar_nmem : hbar ∉ Qbar := by
      intro hh
      rw [hQbar_span, Ideal.mem_span_singleton] at hh
      obtain ⟨w, rfl⟩ := hh
      obtain ⟨u, v, huv⟩ := hf_sep
      let φK : K →+* κ := (IsLocalRing.residue R).comp (algebraMap K R)
      have huv_bar : u.map φK * fbar + v.map φK * Polynomial.derivative fbar = 1 := by
        have h1 := congrArg (Polynomial.map φK) huv
        simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_one] at h1
        rw [← Polynomial.derivative_map, ← hfbar_eq] at h1
        exact h1
      have hdg1 : gbar ∣ fbar := ⟨gbar * w, hfbar_fac⟩
      have hdg2 : gbar ∣ Polynomial.derivative fbar := by
        rw [hfbar_fac, Polynomial.derivative_mul, Polynomial.derivative_mul]
        refine dvd_add ?_ ?_
        · exact ⟨Polynomial.derivative gbar * w, by ring⟩
        · exact ⟨Polynomial.derivative gbar * w + gbar * Polynomial.derivative w, by ring⟩
      have hd1 : gbar ∣ 1 := by
        rw [← huv_bar]
        exact dvd_add (dvd_mul_of_dvd_right hdg1 _) (dvd_mul_of_dvd_right hdg2 _)
      exact hgbar_nunit (isUnit_of_dvd_one hd1)
    obtain ⟨h₀, hh₀⟩ := hπ_surj hbar
    obtain ⟨q₀, hq₀⟩ := hmk_surj q
    have hq₀_mem : q₀ ∈ Q₀ := by
      change mk q₀ ∈ Q
      rwa [hq₀]
    have hπq₀_mem : π q₀ ∈ Qbar := Ideal.mem_map_of_mem π hq₀_mem
    rw [hQbar_span, Ideal.mem_span_singleton] at hπq₀_mem
    obtain ⟨cbar, hπq₀_eq⟩ := hπq₀_mem
    obtain ⟨c₀, hc₀⟩ := hπ_surj cbar
    have hprod_ker : h₀ * q₀ - c₀ * fR ∈ RingHom.ker π := by
      rw [RingHom.mem_ker, map_sub, map_mul, map_mul, hh₀, hπq₀_eq, hc₀]
      change hbar * (gbar * cbar) - cbar * fbar = 0
      rw [hfbar_fac]
      ring
    have hprod_mapC : h₀ * q₀ - c₀ * fR ∈ (maximalIdeal R).map Polynomial.C :=
      hker_le_mapC hprod_ker
    have hprod_S : mk h₀ * q ∈ (maximalIdeal R).map (algebraMap R S) := by
      have hmk_mem : mk (h₀ * q₀ - c₀ * fR) ∈
          ((maximalIdeal R).map Polynomial.C).map mk :=
        Ideal.mem_map_of_mem mk hprod_mapC
      rw [Ideal.map_map] at hmk_mem
      have hcomp_eq : mk.comp Polynomial.C = algebraMap R S := rfl
      rw [hcomp_eq, map_sub, map_mul, map_mul, hq₀, AdjoinRoot.mk_self, mul_zero, sub_zero] at hmk_mem
      exact hmk_mem
    have hh_nmem : mk h₀ ∉ Q := by
      intro hm
      have hm0 : h₀ ∈ Q₀ := hm
      exact hhbar_nmem (hh₀ ▸ Ideal.mem_map_of_mem π hm0)
    have hunit : IsUnit (algebraMap S (Localization.AtPrime Q) (mk h₀)) :=
      IsLocalization.map_units (Localization.AtPrime Q) (⟨mk h₀, hh_nmem⟩ : Q.primeCompl)
    obtain ⟨u, hu⟩ := hunit
    have hprod_Loc : algebraMap S (Localization.AtPrime Q) (mk h₀ * q) ∈
        (maximalIdeal R).map (algebraMap R (Localization.AtPrime Q)) := by
      have h1 := Ideal.mem_map_of_mem (algebraMap S (Localization.AtPrime Q)) hprod_S
      rw [Ideal.map_map] at h1
      have hcomp : (algebraMap S (Localization.AtPrime Q)).comp (algebraMap R S) =
          algebraMap R (Localization.AtPrime Q) :=
        (IsScalarTower.algebraMap_eq R S (Localization.AtPrime Q)).symm
      rwa [hcomp] at h1
    rw [map_mul, ← hu] at hprod_Loc
    have hq_Loc : algebraMap S (Localization.AtPrime Q) q =
        (↑u⁻¹ : Localization.AtPrime Q) * (↑u * algebraMap S (Localization.AtPrime Q) q) := by
      rw [← mul_assoc, Units.inv_mul, one_mul]
    rw [Ideal.mem_comap, hq_Loc]
    exact Ideal.mul_mem_left _ _ hprod_Loc

private lemma localize_tensor_at_base_prime
    {K L R : Type*} [Field K] [Field L] [Algebra K L] [CommRing R] [Algebra K R]
    (𝔭 : Ideal R) [𝔭.IsPrime]
    (Q : Ideal (L ⊗[K] R)) [Q.IsPrime]
    (hQ : Q.comap (Algebra.TensorProduct.includeRight (R := K) (A := L) (B := R)).toRingHom = 𝔭) :
    ∃ (Q₀ : Ideal (L ⊗[K] Localization.AtPrime 𝔭)) (_ : Q₀.IsPrime),
      Q₀.comap (Algebra.TensorProduct.includeRight (R := K) (A := L)
        (B := Localization.AtPrime 𝔭)).toRingHom = maximalIdeal (Localization.AtPrime 𝔭) ∧
      Nonempty (Localization.AtPrime Q ≃+* Localization.AtPrime Q₀) := by
  classical
  let R₀ := Localization.AtPrime 𝔭
  let j : L ⊗[K] R →ₐ[L] L ⊗[K] R₀ :=
    Algebra.TensorProduct.map (AlgHom.id L L) (IsScalarTower.toAlgHom K R R₀)
  let : Algebra (L ⊗[K] R) (L ⊗[K] R₀) := j.toRingHom.toAlgebra
  let M : Submonoid (L ⊗[K] R) :=
    𝔭.primeCompl.map (Algebra.TensorProduct.includeRight (R := K) (A := L) (B := R)).toRingHom.toMonoidHom
  have hM_loc : IsLocalization M (L ⊗[K] R₀) := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨_, s, hs, rfl⟩
      change IsUnit (j (1 ⊗ₜ[K] s))
      have hu : IsUnit (algebraMap R R₀ s) := IsLocalization.map_units R₀ ⟨s, hs⟩
      obtain ⟨u, hu'⟩ := hu
      refine isUnit_iff_exists_inv.mpr ⟨(1 : L) ⊗ₜ[K] (↑u⁻¹ : R₀), ?_⟩
      change ((1 : L) ⊗ₜ[K] algebraMap R R₀ s) * ((1 : L) ⊗ₜ[K] (↑u⁻¹ : R₀)) = 1
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← hu', Units.mul_inv]
      rfl
    · intro z
      induction z using TensorProduct.induction_on with
      | zero => exact ⟨(0, 1), by simp⟩
      | tmul l r₀ =>
        obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj 𝔭.primeCompl r₀
        refine ⟨(l ⊗ₜ[K] r, ⟨(1 : L) ⊗ₜ[K] s.1, s.1, s.2, rfl⟩), ?_⟩
        change (l ⊗ₜ[K] r₀) * ((1 : L) ⊗ₜ[K] algebraMap R R₀ s.1) = l ⊗ₜ[K] algebraMap R R₀ r
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, hrs]
      | add z₁ z₂ ih₁ ih₂ =>
        obtain ⟨⟨x₁, m₁⟩, h₁⟩ := ih₁
        obtain ⟨⟨x₂, m₂⟩, h₂⟩ := ih₂
        refine ⟨(x₁ * m₂.1 + x₂ * m₁.1, m₁ * m₂), ?_⟩
        change (z₁ + z₂) * j (m₁.1 * m₂.1) = j (x₁ * m₂.1 + x₂ * m₁.1)
        rw [map_mul, map_add, map_mul, map_mul, add_mul]
        have h1' : z₁ * j m₁.1 = j x₁ := h₁
        have h2' : z₂ * j m₂.1 = j x₂ := h₂
        calc z₁ * (j m₁.1 * j m₂.1) + z₂ * (j m₁.1 * j m₂.1)
            = (z₁ * j m₁.1) * j m₂.1 + (z₂ * j m₂.1) * j m₁.1 := by ring
          _ = j x₁ * j m₂.1 + j x₂ * j m₁.1 := by rw [h1', h2']
    · intro x y hxy
      let b := Module.Free.chooseBasis K L
      let ι := Module.Free.ChooseBasisIndex K L
      let eR : L ⊗[K] R ≃ₗ[K] (ι →₀ R) :=
        ((b.repr.rTensor R).trans (TensorProduct.finsuppLeft K K K R ι)).trans
          (Finsupp.mapRange.linearEquiv (TensorProduct.lid K R))
      let eR₀ : L ⊗[K] R₀ ≃ₗ[K] (ι →₀ R₀) :=
        ((b.repr.rTensor R₀).trans (TensorProduct.finsuppLeft K K K R₀ ι)).trans
          (Finsupp.mapRange.linearEquiv (TensorProduct.lid K R₀))
      have heR_tmul : ∀ (l : L) (r : R) (i : ι), eR (l ⊗ₜ[K] r) i = b.repr l i • r := by
        intro l r i
        simp only [eR, LinearEquiv.trans_apply, LinearEquiv.rTensor_tmul,
          Finsupp.mapRange.linearEquiv_apply, Finsupp.mapRange_apply,
          TensorProduct.finsuppLeft_apply_tmul_apply, TensorProduct.lid_tmul]
      have heR₀_tmul : ∀ (l : L) (r₀ : R₀) (i : ι), eR₀ (l ⊗ₜ[K] r₀) i = b.repr l i • r₀ := by
        intro l r₀ i
        simp only [eR₀, LinearEquiv.trans_apply, LinearEquiv.rTensor_tmul,
          Finsupp.mapRange.linearEquiv_apply, Finsupp.mapRange_apply,
          TensorProduct.finsuppLeft_apply_tmul_apply, TensorProduct.lid_tmul]
      have hcomm : ∀ (w : L ⊗[K] R) (i : ι), eR₀ (j w) i = algebraMap R R₀ (eR w i) := by
        intro w i
        induction w using TensorProduct.induction_on with
        | zero => simp
        | tmul l r =>
          change eR₀ (l ⊗ₜ[K] algebraMap R R₀ r) i = algebraMap R R₀ (eR (l ⊗ₜ[K] r) i)
          rw [heR₀_tmul, heR_tmul, Algebra.smul_def, Algebra.smul_def, map_mul,
            IsScalarTower.algebraMap_apply K R R₀]
        | add w₁ w₂ h₁ h₂ => simp [h₁, h₂]
      let w : L ⊗[K] R := x - y
      have hjw : j w = 0 := by
        change j (x - y) = 0
        rw [map_sub]
        exact sub_eq_zero.mpr hxy
      have hex_s : ∀ i ∈ (eR w).support, ∃ s : 𝔭.primeCompl, s.1 * (eR w i) = 0 := by
        intro i _
        have h0 : algebraMap R R₀ (eR w i) = 0 := by
          rw [← hcomm w i, hjw, map_zero, Finsupp.zero_apply]
        obtain ⟨s, hs⟩ := IsLocalization.exists_of_eq (M := 𝔭.primeCompl)
          (by simpa using h0 : algebraMap R R₀ (eR w i) = algebraMap R R₀ 0)
        exact ⟨s, by simpa using hs⟩
      choose sfn hsfn using hex_s
      let sProd : 𝔭.primeCompl := ∏ i ∈ (eR w).support.attach, sfn i.1 i.2
      refine ⟨⟨(1 : L) ⊗ₜ[K] sProd.1, sProd.1, sProd.2, rfl⟩, ?_⟩
      apply sub_eq_zero.mp
      rw [← mul_sub]
      apply eR.injective
      rw [map_zero]
      ext i
      have hmul_eR : ∀ (r : R) (u : L ⊗[K] R),
          eR (((1 : L) ⊗ₜ[K] r) * u) i = r * eR u i := by
        intro r u
        induction u using TensorProduct.induction_on with
        | zero => simp
        | tmul l a =>
          rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, heR_tmul, heR_tmul,
            Algebra.smul_def, Algebra.smul_def]
          ring
        | add u₁ u₂ h₁ h₂ => simp [mul_add, h₁, h₂]
      rw [hmul_eR, Finsupp.zero_apply]
      by_cases hi : i ∈ (eR w).support
      · have hdvd : (sfn i hi).1 ∣ sProd.1 := by
          have hmem : (⟨i, hi⟩ : { j // j ∈ (eR w).support }) ∈ (eR w).support.attach :=
            Finset.mem_attach _ _
          have h1 := Finset.dvd_prod_of_mem (fun p : { j // j ∈ (eR w).support } => (sfn p.1 p.2).1) hmem
          simpa [sProd, Submonoid.coe_finsetProd] using h1
        obtain ⟨c, hc⟩ := hdvd
        rw [hc, mul_comm _ c, mul_assoc]
        change c * ((sfn i hi).1 * eR w i) = 0
        rw [hsfn i hi, mul_zero]
      · rw [Finsupp.notMem_support_iff.mp hi, mul_zero]
  have hdisj : Disjoint (M : Set (L ⊗[K] R)) (Q : Set (L ⊗[K] R)) := by
    rw [Set.disjoint_left]
    rintro _ ⟨s, hs, rfl⟩ hmem
    exact hs (hQ ▸ hmem)
  let Q₀ : Ideal (L ⊗[K] R₀) := Q.map j.toRingHom
  have hQ₀_prime : Q₀.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M (L ⊗[K] R₀) Q inferInstance hdisj
  have hQ₀_comap_j : Q₀.comap j.toRingHom = Q :=
    IsLocalization.under_map_of_isPrime_disjoint M (L ⊗[K] R₀) inferInstance hdisj
  have hQ₀_comap_R₀ : Q₀.comap (Algebra.TensorProduct.includeRight (R := K) (A := L)
      (B := R₀)).toRingHom = maximalIdeal R₀ := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    apply le_antisymm
    · intro r₀ hr₀
      obtain ⟨r, s, rfl⟩ := IsLocalization.exists_mk'_eq 𝔭.primeCompl r₀
      have h1 : (1 : L) ⊗ₜ[K] algebraMap R R₀ r ∈ Q₀ := by
        have hmul : (1 : L) ⊗ₜ[K] algebraMap R R₀ r =
            ((1 : L) ⊗ₜ[K] IsLocalization.mk' R₀ r s) * ((1 : L) ⊗ₜ[K] algebraMap R R₀ s.1) := by
          rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_comm, IsLocalization.mk'_spec']
        rw [hmul]
        exact Q₀.mul_mem_right _ hr₀
      have hrp : r ∈ 𝔭 := by
        rw [← hQ, Ideal.mem_comap, ← hQ₀_comap_j, Ideal.mem_comap]
        exact h1
      have hmk : IsLocalization.mk' R₀ r s =
          IsLocalization.mk' R₀ 1 s * algebraMap R R₀ r := by
        rw [IsLocalization.mk'_eq_mul_mk'_one, mul_comm]
      rw [hmk]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hrp)
    · rw [Ideal.map_le_iff_le_comap]
      intro r hr
      rw [Ideal.mem_comap, Ideal.mem_comap]
      have hrQ : (1 : L) ⊗ₜ[K] r ∈ Q := by
        rw [← hQ] at hr
        exact hr
      exact Ideal.mem_map_of_mem j.toRingHom hrQ
  have hLoc : IsLocalization Q.primeCompl (Localization.AtPrime Q₀) := by
    have h1 : IsLocalization (Q₀.comap j.toRingHom).primeCompl (Localization.AtPrime Q₀) :=
      IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M
        (Localization.AtPrime Q₀) Q₀
    have hpc_eq : (Q₀.comap j.toRingHom).primeCompl = Q.primeCompl := by
      ext z
      simp only [Ideal.mem_primeCompl_iff, hQ₀_comap_j]
    exact hpc_eq ▸ h1
  let eLoc : Localization.AtPrime Q ≃+* Localization.AtPrime Q₀ :=
    (IsLocalization.algEquiv Q.primeCompl (Localization.AtPrime Q)
      (Localization.AtPrime Q₀)).toRingEquiv
  exact ⟨Q₀, hQ₀_prime, hQ₀_comap_R₀, ⟨eLoc⟩⟩

private lemma isRegularLocalRing_baseChange_simple_transcendental
    {K L R : Type*} [Field K] [Field L] [Algebra K L] [CommRing R] [Algebra K R]
    (t : L) (ht_trans : ¬ IsIntegral K t) (ht_gen : IntermediateField.adjoin K ({t} : Set L) = ⊤)
    (𝔭 : Ideal R) [𝔭.IsPrime] [IsRegularLocalRing (Localization.AtPrime 𝔭)]
    (Q : Ideal (L ⊗[K] R)) [Q.IsPrime]
    (hQ : Q.comap (Algebra.TensorProduct.includeRight (R := K) (A := L) (B := R)).toRingHom = 𝔭) :
    IsRegularLocalRing (Localization.AtPrime Q) := by
  classical
  obtain ⟨Q₀, hQ₀_prime, hQ₀_comap, ⟨eLoc⟩⟩ := localize_tensor_at_base_prime 𝔭 Q hQ
  let R₀ := Localization.AtPrime 𝔭
  have haeval_inj : Function.Injective (Polynomial.aeval (R := K) t) := by
    rw [injective_iff_map_eq_zero]
    intro p hp
    by_contra hp0
    exact ht_trans (IsAlgebraic.isIntegral ⟨p, hp0, hp⟩)
  let : Algebra K[X] L := (Polynomial.aeval (R := K) t).toRingHom.toAlgebra
  have : IsScalarTower K K[X] L :=
    IsScalarTower.of_algebraMap_eq fun c => (Polynomial.aeval_C t c).symm
  have hfrac_KL : IsFractionRing K[X] L := by
    refine ⟨?_, ?_, ?_⟩
    · intro y
      have hy0 : (y : K[X]) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp y.2
      refine isUnit_iff_ne_zero.mpr fun h0 => hy0 ?_
      change Polynomial.aeval t y.1 = 0 at h0
      exact haeval_inj (by rw [h0, map_zero])
    · intro x
      have hx : x ∈ IntermediateField.adjoin K ({t} : Set L) := by rw [ht_gen]; trivial
      rw [IntermediateField.mem_adjoin_simple_iff] at hx
      obtain ⟨p, q, hpq⟩ := hx
      by_cases hq0 : q = 0
      · rw [hq0, map_zero, div_zero] at hpq
        exact ⟨(0, 1), by simp [← hpq]⟩
      · refine ⟨(p, ⟨q, mem_nonZeroDivisors_iff_ne_zero.mpr hq0⟩), ?_⟩
        change x * Polynomial.aeval t q = Polynomial.aeval t p
        have hqne : Polynomial.aeval t q ≠ 0 := fun h0 => hq0 (haeval_inj (by simpa using h0))
        rw [hpq, div_mul_cancel₀ _ hqne]
    · intro x y hxy
      exact ⟨1, by simp [haeval_inj hxy]⟩
  let fPoly : R₀[X] →ₐ[K] L ⊗[K] R₀ :=
    (Algebra.TensorProduct.map (IsScalarTower.toAlgHom K K[X] L) (AlgHom.id K R₀)).comp
      ((Algebra.TensorProduct.comm K R₀ K[X]).toAlgHom.comp
        ((polyEquivTensor K R₀).toAlgHom))
  let : Algebra R₀[X] (L ⊗[K] R₀) := fPoly.toRingHom.toAlgebra
  let M : Submonoid R₀[X] :=
    (nonZeroDivisors K[X]).map (Polynomial.mapRingHom (algebraMap K R₀)).toMonoidHom
  have hfPoly_map : ∀ p : K[X], fPoly (p.map (algebraMap K R₀)) = (Polynomial.aeval t p) ⊗ₜ[K] (1 : R₀) := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p₁ p₂ h₁ h₂ => simp [h₁, h₂, TensorProduct.add_tmul]
    | monomial n c =>
      have h1 : polyEquivTensor K R₀ (Polynomial.monomial n (algebraMap K R₀ c)) =
          (algebraMap K R₀ c) ⊗ₜ[K] (Polynomial.X ^ n : K[X]) := by
        apply (polyEquivTensor K R₀).symm.injective
        rw [AlgEquiv.symm_apply_apply, polyEquivTensor_symm_apply_tmul_eq_smul, Polynomial.map_pow,
          Polynomial.map_X, Algebra.smul_def, Polynomial.algebraMap_eq,
          Polynomial.C_mul_X_pow_eq_monomial]
      change (Algebra.TensorProduct.map (IsScalarTower.toAlgHom K K[X] L) (AlgHom.id K R₀))
        ((Algebra.TensorProduct.comm K R₀ K[X])
          (polyEquivTensor K R₀ ((Polynomial.monomial n c).map (algebraMap K R₀)))) = _
      rw [Polynomial.map_monomial, h1, Algebra.TensorProduct.comm_tmul,
        Algebra.TensorProduct.map_tmul]
      change (Polynomial.aeval t (Polynomial.X ^ n)) ⊗ₜ[K] (algebraMap K R₀ c) =
        (Polynomial.aeval t (Polynomial.monomial n c)) ⊗ₜ[K] (1 : R₀)
      rw [Polynomial.aeval_monomial, map_pow, Polynomial.aeval_X, Algebra.algebraMap_eq_smul_one,
        ← TensorProduct.smul_tmul, Algebra.smul_def, mul_comm]
  have hfPoly_C : ∀ r₀ : R₀, fPoly (Polynomial.C r₀) = (1 : L) ⊗ₜ[K] r₀ := by
    intro r₀
    have h1 : polyEquivTensor K R₀ (Polynomial.C r₀) = r₀ ⊗ₜ[K] (1 : K[X]) := by
      apply (polyEquivTensor K R₀).symm.injective
      rw [AlgEquiv.symm_apply_apply, polyEquivTensor_symm_apply_tmul_eq_smul, Polynomial.map_one,
        Algebra.smul_def, mul_one, Polynomial.algebraMap_eq]
    change (Algebra.TensorProduct.map (IsScalarTower.toAlgHom K K[X] L) (AlgHom.id K R₀))
      ((Algebra.TensorProduct.comm K R₀ K[X]) (polyEquivTensor K R₀ (Polynomial.C r₀))) = _
    rw [h1, Algebra.TensorProduct.comm_tmul, Algebra.TensorProduct.map_tmul]
    simp
  have hM_loc : IsLocalization M (L ⊗[K] R₀) := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨_, p, hp, rfl⟩
      change IsUnit (fPoly (p.map (algebraMap K R₀)))
      rw [hfPoly_map]
      have hp0 : p ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hp
      have hpL : Polynomial.aeval t p ≠ 0 := fun h0 => hp0 (haeval_inj (by simpa using h0))
      refine isUnit_iff_exists_inv.mpr ⟨(Polynomial.aeval t p)⁻¹ ⊗ₜ[K] (1 : R₀), ?_⟩
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_inv_cancel₀ hpL, one_mul]
      rfl
    · intro z
      induction z using TensorProduct.induction_on with
      | zero => exact ⟨(0, 1), by simp⟩
      | tmul l r₀ =>
        obtain ⟨⟨p, q⟩, hpq⟩ := IsLocalization.surj (nonZeroDivisors K[X]) l
        refine ⟨(Polynomial.C r₀ * p.map (algebraMap K R₀),
          ⟨q.1.map (algebraMap K R₀), q.1, q.2, rfl⟩), ?_⟩
        change (l ⊗ₜ[K] r₀) * fPoly (q.1.map (algebraMap K R₀)) =
          fPoly (Polynomial.C r₀ * p.map (algebraMap K R₀))
        rw [map_mul, hfPoly_C, hfPoly_map, hfPoly_map, Algebra.TensorProduct.tmul_mul_tmul,
          Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
        have hpq' : l * Polynomial.aeval t q.1 = Polynomial.aeval t p := hpq
        rw [hpq']
      | add z₁ z₂ ih₁ ih₂ =>
        obtain ⟨⟨x₁, m₁⟩, h₁⟩ := ih₁
        obtain ⟨⟨x₂, m₂⟩, h₂⟩ := ih₂
        refine ⟨(x₁ * m₂.1 + x₂ * m₁.1, m₁ * m₂), ?_⟩
        change (z₁ + z₂) * fPoly (m₁.1 * m₂.1) = fPoly (x₁ * m₂.1 + x₂ * m₁.1)
        rw [map_mul, map_add, map_mul, map_mul, add_mul]
        have h1' : z₁ * fPoly m₁.1 = fPoly x₁ := h₁
        have h2' : z₂ * fPoly m₂.1 = fPoly x₂ := h₂
        calc z₁ * (fPoly m₁.1 * fPoly m₂.1) + z₂ * (fPoly m₁.1 * fPoly m₂.1)
            = (z₁ * fPoly m₁.1) * fPoly m₂.1 + (z₂ * fPoly m₂.1) * fPoly m₁.1 := by ring
          _ = fPoly x₁ * fPoly m₂.1 + fPoly x₂ * fPoly m₁.1 := by rw [h1', h2']
    · intro x y hxy
      have hinj_map : Function.Injective
          (Algebra.TensorProduct.map (IsScalarTower.toAlgHom K K[X] L) (AlgHom.id K R₀)) := by
        have hlin : (Algebra.TensorProduct.map (IsScalarTower.toAlgHom K K[X] L)
            (AlgHom.id K R₀)).toLinearMap =
            LinearMap.rTensor R₀ (IsScalarTower.toAlgHom K K[X] L).toLinearMap := by
          ext p r₀; simp
        intro a b hab
        have h1 : LinearMap.rTensor R₀ (IsScalarTower.toAlgHom K K[X] L).toLinearMap a =
            LinearMap.rTensor R₀ (IsScalarTower.toAlgHom K K[X] L).toLinearMap b := by
          rw [← hlin]
          exact hab
        exact Module.Flat.rTensor_preserves_injective_linearMap _ haeval_inj h1
      have hxy' : x = y := (polyEquivTensor K R₀).injective
        ((Algebra.TensorProduct.comm K R₀ K[X]).injective (hinj_map hxy))
      exact ⟨1, by simp [hxy']⟩
  let Qpoly : Ideal R₀[X] := Q₀.comap fPoly.toRingHom
  have : Qpoly.IsPrime := Ideal.IsPrime.comap fPoly.toRingHom
  have hQpoly_C : Qpoly.comap Polynomial.C = maximalIdeal R₀ := by
    ext r₀
    rw [Ideal.mem_comap, Ideal.mem_comap, ← hQ₀_comap, Ideal.mem_comap]
    change fPoly (Polynomial.C r₀) ∈ Q₀ ↔ (1 : L) ⊗ₜ[K] r₀ ∈ Q₀
    rw [hfPoly_C]
  have hRegPoly : IsRegularLocalRing (Localization.AtPrime Qpoly) :=
    Polynomial.isRegularLocalRing_localization_atPrime_of_comap_eq_maximalIdeal R₀ Qpoly hQpoly_C
  have hLocPoly : IsLocalization.AtPrime (Localization.AtPrime Q₀) Qpoly :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M
      (Localization.AtPrime Q₀) Q₀
  let ePolyLoc : Localization.AtPrime Qpoly ≃+* Localization.AtPrime Q₀ :=
    (IsLocalization.algEquiv Qpoly.primeCompl (Localization.AtPrime Qpoly)
      (Localization.AtPrime Q₀)).toRingEquiv
  have hRegQ₀ : IsRegularLocalRing (Localization.AtPrime Q₀) :=
    @IsRegularLocalRing.of_ringEquiv _ _ hRegPoly _ _ ePolyLoc
  exact @IsRegularLocalRing.of_ringEquiv _ _ hRegQ₀ _ _ eLoc.symm

private lemma isRegularLocalRing_baseChange_simple_algebraic
    {K L R : Type*} [Field K] [CharZero K] [Field L] [Algebra K L] [CommRing R] [Algebra K R]
    (α : L) (hα : IsIntegral K α) (hα_gen : IntermediateField.adjoin K ({α} : Set L) = ⊤)
    (𝔭 : Ideal R) [𝔭.IsPrime] [IsRegularLocalRing (Localization.AtPrime 𝔭)]
    (Q : Ideal (L ⊗[K] R)) [Q.IsPrime]
    (hQ : Q.comap (Algebra.TensorProduct.includeRight (R := K) (A := L) (B := R)).toRingHom = 𝔭) :
    IsRegularLocalRing (Localization.AtPrime Q) := by
  classical
  obtain ⟨Q₀, hQ₀_prime, hQ₀_comap, ⟨eLoc⟩⟩ := localize_tensor_at_base_prime 𝔭 Q hQ
  let R₀ := Localization.AtPrime 𝔭
  let f : K[X] := minpoly K α
  have hf_monic : f.Monic := minpoly.monic hα
  have hf_irred : Irreducible f := minpoly.irreducible hα
  have hf_sep : IsCoprime f (Polynomial.derivative f) := hf_irred.separable
  let eL : AdjoinRoot f ≃ₐ[K] L :=
    (IntermediateField.adjoinRootEquivAdjoin K hα).trans
      ((IntermediateField.equivOfEq hα_gen).trans IntermediateField.topEquiv)
  let e1 : L ⊗[K] R₀ ≃ₐ[K] R₀ ⊗[K] AdjoinRoot f :=
    (Algebra.TensorProduct.congr eL.symm (AlgEquiv.refl)).trans
      (Algebra.TensorProduct.comm K (AdjoinRoot f) R₀)
  let fR₀ : R₀[X] := f.map (algebraMap K R₀)
  let fwd : R₀ ⊗[K] AdjoinRoot f →ₐ[R₀] AdjoinRoot fR₀ :=
    Algebra.TensorProduct.lift (Algebra.ofId R₀ (AdjoinRoot fR₀))
      (AdjoinRoot.liftAlgHom f (Algebra.ofId K (AdjoinRoot fR₀))
        (AdjoinRoot.root fR₀) (by
          rw [Polynomial.eval₂_eq_eval_map]
          have hmap : f.map (algebraMap K (AdjoinRoot fR₀)) =
              fR₀.map (AdjoinRoot.of fR₀) := by
            dsimp only [fR₀]
            rw [Polynomial.map_map]
            rfl
          change Polynomial.eval (AdjoinRoot.root fR₀) (f.map (algebraMap K (AdjoinRoot fR₀))) = 0
          rw [hmap, ← Polynomial.eval₂_eq_eval_map, AdjoinRoot.eval₂_root]))
      (fun _ _ => Commute.all _ _)
  let bwd : AdjoinRoot fR₀ →ₐ[R₀] R₀ ⊗[K] AdjoinRoot f :=
    AdjoinRoot.liftAlgHom fR₀ (Algebra.TensorProduct.includeLeft : R₀ →ₐ[R₀] R₀ ⊗[K] AdjoinRoot f)
      ((1 : R₀) ⊗ₜ[K] AdjoinRoot.root f) (by
        dsimp only [fR₀]
        rw [Polynomial.eval₂_map]
        have hcomp : (Algebra.TensorProduct.includeLeft (R := K) (S := R₀) (A := R₀)
            (B := AdjoinRoot f)).toRingHom.comp (algebraMap K R₀) =
            (Algebra.TensorProduct.includeRight (R := K) (A := R₀)
              (B := AdjoinRoot f)).toRingHom.comp (algebraMap K (AdjoinRoot f)) := by
          ext c
          change (algebraMap K R₀ c) ⊗ₜ[K] (1 : AdjoinRoot f) =
            (1 : R₀) ⊗ₜ[K] (algebraMap K (AdjoinRoot f) c)
          rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
            TensorProduct.smul_tmul]
        change Polynomial.eval₂ ((Algebra.TensorProduct.includeLeft (R := K) (S := R₀) (A := R₀)
            (B := AdjoinRoot f)).toRingHom.comp (algebraMap K R₀))
          ((1 : R₀) ⊗ₜ[K] AdjoinRoot.root f) f = 0
        have hroot_eq : (1 : R₀) ⊗ₜ[K] AdjoinRoot.root f =
            (Algebra.TensorProduct.includeRight (R := K) (A := R₀)
              (B := AdjoinRoot f)).toRingHom (AdjoinRoot.root f) := rfl
        rw [hcomp, hroot_eq, ← Polynomial.hom_eval₂]
        have hroot : Polynomial.eval₂ (algebraMap K (AdjoinRoot f)) (AdjoinRoot.root f) f = 0 :=
          AdjoinRoot.eval₂_root f
        rw [hroot, map_zero])
  let e2 : R₀ ⊗[K] AdjoinRoot f ≃ₐ[R₀] AdjoinRoot fR₀ :=
    AlgEquiv.ofAlgHom fwd bwd
      (by
        apply AdjoinRoot.algHom_ext
        simp [fwd, bwd])
      (by
        apply Algebra.TensorProduct.ext'
        intro r₀ x
        induction x using AdjoinRoot.induction_on with
        | ih p =>
          induction p using Polynomial.induction_on' with
          | add p₁ p₂ h₁ h₂ => simp [map_add, TensorProduct.tmul_add, h₁, h₂]
          | monomial n c =>
            have hmk_mon : AdjoinRoot.mk f (Polynomial.monomial n c) =
                AdjoinRoot.of f c * AdjoinRoot.root f ^ n := by
              rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow]
              rfl
            rw [hmk_mon]
            simp only [fwd, bwd, AlgHom.comp_apply, Algebra.TensorProduct.lift_tmul,
              map_mul, map_pow, AdjoinRoot.liftAlgHom_of, AdjoinRoot.liftAlgHom_root,
              Algebra.ofId_apply, IsScalarTower.algebraMap_apply K R₀ (AdjoinRoot fR₀),
              AlgHom.commutes]
            change (r₀ ⊗ₜ[K] (1 : AdjoinRoot f)) *
              (((algebraMap K R₀ c) ⊗ₜ[K] (1 : AdjoinRoot f)) *
                ((1 : R₀) ⊗ₜ[K] AdjoinRoot.root f) ^ n) =
              r₀ ⊗ₜ[K] (AdjoinRoot.of f c * AdjoinRoot.root f ^ n)
            have hpow : ∀ m : ℕ, ((1 : R₀) ⊗ₜ[K] AdjoinRoot.root f) ^ m =
                (1 : R₀) ⊗ₜ[K] (AdjoinRoot.root f ^ m) := by
              intro m
              induction m with
              | zero => rfl
              | succ m ihm => rw [pow_succ, ihm, Algebra.TensorProduct.tmul_mul_tmul, one_mul, pow_succ]
            rw [hpow n, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
              mul_one, one_mul, one_mul]
            rw [mul_comm r₀, ← Algebra.smul_def, TensorProduct.smul_tmul, Algebra.smul_def]
            rfl)
  let eTot : L ⊗[K] R₀ ≃+* AdjoinRoot fR₀ := e1.toRingEquiv.trans e2.toRingEquiv
  have heTot_R₀ : ∀ r₀ : R₀, eTot ((1 : L) ⊗ₜ[K] r₀) = algebraMap R₀ (AdjoinRoot fR₀) r₀ := by
    intro r₀
    change e2 (e1 ((1 : L) ⊗ₜ[K] r₀)) = algebraMap R₀ (AdjoinRoot fR₀) r₀
    have h1 : e1 ((1 : L) ⊗ₜ[K] r₀) = r₀ ⊗ₜ[K] (1 : AdjoinRoot f) := by simp [e1]
    rw [h1]
    simp [e2, fwd]
  let Q_adj : Ideal (AdjoinRoot fR₀) := Q₀.comap eTot.symm.toRingHom
  have : Q_adj.IsPrime := Ideal.IsPrime.comap eTot.symm.toRingHom
  have hQ_adj_comap : Q_adj.comap (algebraMap R₀ (AdjoinRoot fR₀)) = maximalIdeal R₀ := by
    ext r₀
    rw [Ideal.mem_comap, Ideal.mem_comap, ← hQ₀_comap, Ideal.mem_comap]
    have h1 : eTot.symm (algebraMap R₀ (AdjoinRoot fR₀) r₀) = (1 : L) ⊗ₜ[K] r₀ := by
      rw [← heTot_R₀, eTot.symm_apply_apply]
    change eTot.symm (algebraMap R₀ (AdjoinRoot fR₀) r₀) ∈ Q₀ ↔ (1 : L) ⊗ₜ[K] r₀ ∈ Q₀
    rw [h1]
  have hRegAdj : IsRegularLocalRing (Localization.AtPrime Q_adj) :=
    isRegularLocalRing_adjoinRoot_monic_separable f hf_monic hf_sep Q_adj hQ_adj_comap
  have hpc : Q_adj.primeCompl.map eTot.symm.toRingHom.toMonoidHom = Q₀.primeCompl := by
    ext y
    simp only [Submonoid.mem_map, Ideal.mem_primeCompl_iff]
    constructor
    · rintro ⟨x, hx, rfl⟩ hmem
      exact hx hmem
    · intro hy
      refine ⟨eTot y, fun hx => hy ?_, eTot.symm_apply_apply y⟩
      have h1 : eTot.symm (eTot y) ∈ Q₀ := hx
      rwa [eTot.symm_apply_apply] at h1
  let eAdjLoc : Localization.AtPrime Q_adj ≃+* Localization.AtPrime Q₀ :=
    IsLocalization.ringEquivOfRingEquiv _ _ eTot.symm hpc
  have hRegQ₀ : IsRegularLocalRing (Localization.AtPrime Q₀) :=
    @IsRegularLocalRing.of_ringEquiv _ _ hRegAdj _ _ eAdjLoc
  exact @IsRegularLocalRing.of_ringEquiv _ _ hRegQ₀ _ _ eLoc.symm

private lemma isRegularLocalRing_baseChange_simple_step
    {k₀ K₁ K₂ B₀ : Type*} [Field k₀] [CharZero k₀]
    [Field K₁] [Algebra k₀ K₁] [Field K₂] [Algebra k₀ K₂] [Algebra K₁ K₂] [IsScalarTower k₀ K₁ K₂]
    [CommRing B₀] [Algebra k₀ B₀]
    (𝔭₀ : Ideal B₀) [𝔭₀.IsPrime]
    (hIH : ∀ (Q₁ : Ideal (K₁ ⊗[k₀] B₀)) [Q₁.IsPrime],
      Q₁.comap (Algebra.TensorProduct.includeRight (R := k₀) (A := K₁) (B := B₀)).toRingHom = 𝔭₀ →
      IsRegularLocalRing (Localization.AtPrime Q₁))
    (α : K₂) (hgen : IntermediateField.adjoin K₁ ({α} : Set K₂) = ⊤)
    (Q : Ideal (K₂ ⊗[k₀] B₀)) [Q.IsPrime]
    (hQ : Q.comap (Algebra.TensorProduct.includeRight (R := k₀) (A := K₂) (B := B₀)).toRingHom = 𝔭₀) :
    IsRegularLocalRing (Localization.AtPrime Q) := by
  classical
  have : CharZero K₁ := charZero_of_injective_algebraMap (algebraMap k₀ K₁).injective
  let eCancel : K₂ ⊗[K₁] (K₁ ⊗[k₀] B₀) ≃ₐ[K₂] K₂ ⊗[k₀] B₀ :=
    Algebra.TensorProduct.cancelBaseChange k₀ K₁ K₂ K₂ B₀
  let Q₂ : Ideal (K₂ ⊗[K₁] (K₁ ⊗[k₀] B₀)) := Q.comap eCancel.toRingHom
  have : Q₂.IsPrime := Ideal.IsPrime.comap eCancel.toRingHom
  let Q₁ : Ideal (K₁ ⊗[k₀] B₀) :=
    Q₂.comap (Algebra.TensorProduct.includeRight (R := K₁) (A := K₂)
      (B := K₁ ⊗[k₀] B₀)).toRingHom
  have : Q₁.IsPrime := Ideal.IsPrime.comap _
  have hQ₁_comap : Q₁.comap (Algebra.TensorProduct.includeRight (R := k₀) (A := K₁)
      (B := B₀)).toRingHom = 𝔭₀ := by
    ext b
    rw [Ideal.mem_comap, Ideal.mem_comap, Ideal.mem_comap, ← hQ, Ideal.mem_comap]
    change eCancel ((1 : K₂) ⊗ₜ[K₁] ((1 : K₁) ⊗ₜ[k₀] b)) ∈ Q ↔ (1 : K₂) ⊗ₜ[k₀] b ∈ Q
    rw [Algebra.TensorProduct.cancelBaseChange_tmul, one_smul]
  have hReg₁ : IsRegularLocalRing (Localization.AtPrime Q₁) := hIH Q₁ hQ₁_comap
  have hReg₂ : IsRegularLocalRing (Localization.AtPrime Q₂) := by
    by_cases hint : IsIntegral K₁ α
    · exact isRegularLocalRing_baseChange_simple_algebraic α hint hgen Q₁ Q₂ rfl
    · exact isRegularLocalRing_baseChange_simple_transcendental α hint hgen Q₁ Q₂ rfl
  have hpc : Q₂.primeCompl.map eCancel.toRingHom.toMonoidHom = Q.primeCompl := by
    ext y
    simp only [Submonoid.mem_map, Ideal.mem_primeCompl_iff]
    constructor
    · rintro ⟨x, hx, rfl⟩ hmem
      exact hx hmem
    · intro hy
      refine ⟨eCancel.symm y, fun hx => hy ?_, eCancel.apply_symm_apply y⟩
      have h1 : eCancel (eCancel.symm y) ∈ Q := hx
      rwa [eCancel.apply_symm_apply] at h1
  let eLoc : Localization.AtPrime Q₂ ≃+* Localization.AtPrime Q :=
    IsLocalization.ringEquivOfRingEquiv _ _ eCancel.toRingEquiv hpc
  exact @IsRegularLocalRing.of_ringEquiv _ _ hReg₂ _ _ eLoc

private lemma isRegularLocalRing_baseChange_fg
    {k₀ B₀ : Type*} [Field k₀] [CharZero k₀] [CommRing B₀] [Algebra k₀ B₀]
    (𝔭₀ : Ideal B₀) [𝔭₀.IsPrime] [IsRegularLocalRing (Localization.AtPrime 𝔭₀)]
    (n : ℕ) :
    ∀ (K : Type*) [Field K] [Algebra k₀ K] (s : Finset K),
      s.card ≤ n →
      IntermediateField.adjoin k₀ (s : Set K) = ⊤ →
      ∀ (Q : Ideal (K ⊗[k₀] B₀)) [Q.IsPrime],
        Q.comap (Algebra.TensorProduct.includeRight (R := k₀) (A := K) (B := B₀)).toRingHom = 𝔭₀ →
        IsRegularLocalRing (Localization.AtPrime Q) := by
  classical
  induction n with
  | zero =>
    intro K _ _ s hcard hgen Q _ hQ
    have hs0 : s = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hcard)
    subst hs0
    have htop_bot : (⊤ : IntermediateField k₀ K) = ⊥ := by
      rw [← hgen]; simp [IntermediateField.adjoin_empty]
    let eK : K ≃ₐ[k₀] k₀ :=
      IntermediateField.topEquiv.symm.trans
        ((IntermediateField.equivOfEq htop_bot).trans (IntermediateField.botEquiv k₀ K))
    let eB : K ⊗[k₀] B₀ ≃ₐ[k₀] B₀ :=
      (Algebra.TensorProduct.congr eK (AlgEquiv.refl)).trans (Algebra.TensorProduct.lid k₀ B₀)
    have hcomap : 𝔭₀.comap eB.toRingHom = Q := by
      ext z
      rw [Ideal.mem_comap, ← hQ, Ideal.mem_comap]
      have hz : z = (1 : K) ⊗ₜ[k₀] eB z := by
        apply eB.injective
        simp [eB]
      conv_rhs => rw [hz]
      rfl
    have hpc : Q.primeCompl.map eB.toRingHom.toMonoidHom = 𝔭₀.primeCompl := by
      ext y
      simp only [Submonoid.mem_map, Ideal.mem_primeCompl_iff]
      constructor
      · rintro ⟨x, hx, rfl⟩ hmem
        exact hx (by rw [← hcomap]; exact hmem)
      · intro hy
        refine ⟨eB.symm y, fun hx => hy ?_, eB.apply_symm_apply y⟩
        have h1 : eB.symm y ∈ 𝔭₀.comap eB.toRingHom := by rw [hcomap]; exact hx
        rw [Ideal.mem_comap] at h1
        change eB (eB.symm y) ∈ 𝔭₀ at h1
        rwa [eB.apply_symm_apply] at h1
    let eLoc : Localization.AtPrime Q ≃+* Localization.AtPrime 𝔭₀ :=
      IsLocalization.ringEquivOfRingEquiv _ _ eB.toRingEquiv hpc
    exact IsRegularLocalRing.of_ringEquiv eLoc.symm
  | succ n ih =>
    intro K _ _ s hcard hgen Q _ hQ
    by_cases hs : s.Nonempty
    · obtain ⟨a, ha⟩ := hs
      let s' : Finset K := s.erase a
      have hs'_card : s'.card ≤ n := by
        have h1 : s'.card + 1 = s.card := Finset.card_erase_add_one ha
        omega
      let K₁ : IntermediateField k₀ K := IntermediateField.adjoin k₀ (s' : Set K)
      let s₁ : Finset K₁ := s'.attach.image fun x =>
        ⟨x.1, IntermediateField.subset_adjoin k₀ (s' : Set K) x.2⟩
      have hs₁_card : s₁.card ≤ n := (Finset.card_image_le).trans (by simpa using hs'_card)
      have hs₁_gen : IntermediateField.adjoin k₀ (s₁ : Set K₁) = ⊤ := by
        rw [eq_top_iff]
        rintro ⟨x, hx⟩ _
        let S : IntermediateField k₀ K :=
          { carrier := { y : K | ∃ z : IntermediateField.adjoin k₀ (s₁ : Set K₁), (z.1 : K) = y }
            mul_mem' := by rintro _ _ ⟨z₁, rfl⟩ ⟨z₂, rfl⟩; exact ⟨z₁ * z₂, rfl⟩
            one_mem' := ⟨1, rfl⟩
            add_mem' := by rintro _ _ ⟨z₁, rfl⟩ ⟨z₂, rfl⟩; exact ⟨z₁ + z₂, rfl⟩
            zero_mem' := ⟨0, rfl⟩
            inv_mem' := by rintro _ ⟨z, rfl⟩; exact ⟨z⁻¹, rfl⟩
            algebraMap_mem' := fun c => ⟨algebraMap k₀ _ c, rfl⟩ }
        have hle : K₁ ≤ S := IntermediateField.adjoin_le_iff.mpr fun y hy => by
          have hy_s₁ : (⟨y, IntermediateField.subset_adjoin k₀ (s' : Set K) hy⟩ : K₁) ∈ s₁ :=
            Finset.mem_image.mpr ⟨⟨y, hy⟩, Finset.mem_attach _ _, rfl⟩
          exact ⟨⟨_, IntermediateField.subset_adjoin k₀ (s₁ : Set K₁) hy_s₁⟩, rfl⟩
        obtain ⟨z, hz⟩ := hle hx
        have hzx : z.1 = ⟨x, hx⟩ := Subtype.ext hz
        rw [← hzx]
        exact z.2
      have hgen_step : IntermediateField.adjoin K₁ ({a} : Set K) = ⊤ := by
        rw [eq_top_iff]
        intro x _
        have hx : x ∈ IntermediateField.adjoin k₀ (s : Set K) := by rw [hgen]; trivial
        have hle : IntermediateField.adjoin k₀ (s : Set K) ≤
            (IntermediateField.adjoin K₁ ({a} : Set K)).restrictScalars k₀ := by
          rw [IntermediateField.adjoin_le_iff]
          intro y hy
          by_cases hya : y = a
          · subst hya
            exact IntermediateField.subset_adjoin K₁ _ (Set.mem_singleton y)
          · have hy' : y ∈ (s' : Set K) := Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hya, hy⟩)
            have hyK₁ : y ∈ K₁ := IntermediateField.subset_adjoin k₀ _ hy'
            exact IntermediateField.algebraMap_mem (IntermediateField.adjoin K₁ ({a} : Set K)) (⟨y, hyK₁⟩ : K₁)
        exact hle hx
      exact isRegularLocalRing_baseChange_simple_step (K₁ := K₁) (K₂ := K) 𝔭₀
        (fun Q₁ _ hQ₁ => ih K₁ s₁ hs₁_card hs₁_gen Q₁ hQ₁) a hgen_step Q hQ
    · have hs0 : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      have hle0 : s.card ≤ n := by simp [hs0]
      exact ih K s hle0 hgen Q hQ

private lemma flat_tensor_sub_field
    {k₀ k₁ k B₀ : Type*} [Field k₀] [Field k₁] [Field k]
    [Algebra k₀ k₁] [Algebra k₀ k] [Algebra k₁ k] [IsScalarTower k₀ k₁ k]
    [CommRing B₀] [Algebra k₀ B₀]
    [Algebra (k₁ ⊗[k₀] B₀) (k ⊗[k₀] B₀)]
    (halg : ∀ r, algebraMap (k₁ ⊗[k₀] B₀) (k ⊗[k₀] B₀) r =
      Algebra.TensorProduct.map (IsScalarTower.toAlgHom k₀ k₁ k) (AlgHom.id k₀ B₀) r) :
    Module.Flat (k₁ ⊗[k₀] B₀) (k ⊗[k₀] B₀) := by
  let eCancel : k ⊗[k₁] (k₁ ⊗[k₀] B₀) ≃ₐ[k] k ⊗[k₀] B₀ :=
    Algebra.TensorProduct.cancelBaseChange k₀ k₁ k k B₀
  have : Module.Flat k₁ k := inferInstance
  have : Module.Flat (k₁ ⊗[k₀] B₀) ((k₁ ⊗[k₀] B₀) ⊗[k₁] k) :=
    Module.Flat.baseChange k₁ (k₁ ⊗[k₀] B₀) k
  let eDirect : ((k₁ ⊗[k₀] B₀) ⊗[k₁] k) ≃ₗ[k₁ ⊗[k₀] B₀] (k ⊗[k₀] B₀) :=
    { toFun := fun x => eCancel (TensorProduct.comm k₁ (k₁ ⊗[k₀] B₀) k x)
      invFun := fun y => TensorProduct.comm k₁ k (k₁ ⊗[k₀] B₀) (eCancel.symm y)
      left_inv := fun x => by simp
      right_inv := fun y => by simp
      map_add' := fun x y => by simp
      map_smul' := fun r x => by
        induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul a c =>
          simp only [RingHom.id_apply, TensorProduct.smul_tmul', TensorProduct.comm_tmul,
            smul_eq_mul]
          rw [Algebra.smul_def r (eCancel (c ⊗ₜ[k₁] a)), halg r]
          change eCancel (c ⊗ₜ[k₁] (r * a)) =
            Algebra.TensorProduct.map (IsScalarTower.toAlgHom k₀ k₁ k) (AlgHom.id k₀ B₀) r *
              eCancel (c ⊗ₜ[k₁] a)
          have hmul : c ⊗ₜ[k₁] (r * a) = ((1 : k) ⊗ₜ[k₁] r) * (c ⊗ₜ[k₁] a) := by
            rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
          rw [hmul, map_mul]
          congr 1
          induction r using TensorProduct.induction_on with
          | zero => simp
          | tmul c₁ b =>
            dsimp only [eCancel]
            rw [Algebra.TensorProduct.cancelBaseChange_tmul, Algebra.TensorProduct.map_tmul]
            change (c₁ • (1 : k)) ⊗ₜ[k₀] b = (algebraMap k₁ k c₁) ⊗ₜ[k₀] b
            rw [Algebra.smul_def, mul_one]
          | add r₁ r₂ h₁ h₂ => simp [TensorProduct.tmul_add, map_add, h₁, h₂]
        | add x y hx hy => simp [smul_add, hx, hy] }
  exact Module.Flat.of_linearEquiv eDirect.symm

private lemma isLocalHom_localization_map_atPrime
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (Q : Ideal S) [Q.IsPrime] (Q₁ : Ideal R) [Q₁.IsPrime]
    (hQ₁_def : Q₁ = Q.comap f)
    (hpc_le : Q₁.primeCompl ≤ Submonoid.comap f.toMonoidHom Q.primeCompl) :
    IsLocalHom (IsLocalization.map (Localization.AtPrime Q) f hpc_le :
      Localization.AtPrime Q₁ →+* Localization.AtPrime Q) := by
  refine ⟨fun x hx => ?_⟩
  obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq Q₁.primeCompl x
  by_contra hnu
  have ham : IsLocalization.mk' (Localization.AtPrime Q₁) a s ∈
      maximalIdeal (Localization.AtPrime Q₁) := (IsLocalRing.mem_maximalIdeal _).mpr hnu
  have haQ₁ : a ∈ Q₁ := by
    rw [← IsLocalization.AtPrime.under_maximalIdeal (Localization.AtPrime Q₁) Q₁,
      Ideal.under_def, Ideal.mem_comap]
    have hmul : algebraMap R (Localization.AtPrime Q₁) a =
        algebraMap R (Localization.AtPrime Q₁) s.1 *
          IsLocalization.mk' (Localization.AtPrime Q₁) a s :=
      (IsLocalization.mk'_spec' _ a s).symm
    rw [hmul]
    exact Ideal.mul_mem_left _ _ ham
  have haQ : f a ∈ Q := by rw [hQ₁_def] at haQ₁; exact haQ₁
  have hmap_mem : IsLocalization.map (Localization.AtPrime Q) f hpc_le
      (IsLocalization.mk' (Localization.AtPrime Q₁) a s) ∈
      maximalIdeal (Localization.AtPrime Q) := by
    have hmk1 : IsLocalization.map (Localization.AtPrime Q) f hpc_le
        (IsLocalization.mk' (Localization.AtPrime Q₁) a s) =
        IsLocalization.mk' (Localization.AtPrime Q) (f a) (⟨f s.1, hpc_le s.2⟩ : Q.primeCompl) :=
      IsLocalization.map_mk' hpc_le a s
    rw [hmk1, ← Localization.AtPrime.map_eq_maximalIdeal]
    have hmk : IsLocalization.mk' (Localization.AtPrime Q) (f a) (⟨f s.1, hpc_le s.2⟩ : Q.primeCompl) =
        IsLocalization.mk' (Localization.AtPrime Q) (1 : S) (⟨f s.1, hpc_le s.2⟩ : Q.primeCompl) *
          algebraMap S (Localization.AtPrime Q) (f a) := by
      rw [IsLocalization.mk'_eq_mul_mk'_one, mul_comm]
    rw [hmk]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ haQ)
  exact (IsLocalRing.mem_maximalIdeal _).mp hmap_mem hx

private lemma isRegularLocalRing_of_flat_localization_map_aux
    {R S : Type*} [CommRing R] [CommRing S] [IsNoetherianRing S]
    [Algebra R S] [Module.Flat R S]
    (Q : Ideal S) [Q.IsPrime] (Q₁ : Ideal R) [Q₁.IsPrime]
    (hQ_eq_map : Q₁.map (algebraMap R S) = Q)
    [IsRegularLocalRing (Localization.AtPrime Q₁)]
    (locMap : Localization.AtPrime Q₁ →+* Localization.AtPrime Q)
    (h1 : ∀ x : R, locMap (algebraMap R (Localization.AtPrime Q₁) x) =
      algebraMap S (Localization.AtPrime Q) (algebraMap R S x))
    [IsLocalHom locMap] :
    IsRegularLocalRing (Localization.AtPrime Q) := by
  let : Algebra (Localization.AtPrime Q₁) (Localization.AtPrime Q) := locMap.toAlgebra
  have : IsScalarTower R (Localization.AtPrime Q₁) (Localization.AtPrime Q) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      rw [IsScalarTower.algebraMap_apply R S (Localization.AtPrime Q)]
      exact (h1 x).symm
  have hFlat_total : Module.Flat R (Localization.AtPrime Q) :=
    Module.Flat.trans R S (Localization.AtPrime Q)
  have hFlat_loc : Module.Flat (Localization.AtPrime Q₁) (Localization.AtPrime Q) :=
    (Module.flat_iff_of_isLocalization (Localization.AtPrime Q₁) Q₁.primeCompl
      (Localization.AtPrime Q)).mpr hFlat_total
  apply isRegularLocalRing_of_flat_local_map_maximalIdeal
    (R := Localization.AtPrime Q₁) (S := Localization.AtPrime Q)
  have hcomp : locMap.comp (algebraMap R (Localization.AtPrime Q₁)) =
      (algebraMap S (Localization.AtPrime Q)).comp (algebraMap R S) :=
    RingHom.ext h1
  calc (maximalIdeal (Localization.AtPrime Q₁)).map locMap
      = (Q₁.map (algebraMap R (Localization.AtPrime Q₁))).map locMap := by
        rw [Localization.AtPrime.map_eq_maximalIdeal]
    _ = Q₁.map (locMap.comp (algebraMap R (Localization.AtPrime Q₁))) := Ideal.map_map _ _
    _ = Q₁.map ((algebraMap S (Localization.AtPrime Q)).comp (algebraMap R S)) :=
        congrArg (fun f => Q₁.map f) hcomp
    _ = (Q₁.map (algebraMap R S)).map (algebraMap S (Localization.AtPrime Q)) :=
        (Ideal.map_map _ _).symm
    _ = Q.map (algebraMap S (Localization.AtPrime Q)) :=
        congrArg (fun I => I.map (algebraMap S (Localization.AtPrime Q))) hQ_eq_map
    _ = maximalIdeal (Localization.AtPrime Q) := Localization.AtPrime.map_eq_maximalIdeal

private lemma isRegularLocalRing_of_flat_localization_map
    {R S : Type*} [CommRing R] [CommRing S] [IsNoetherianRing S]
    [Algebra R S] [Module.Flat R S]
    (Q : Ideal S) [Q.IsPrime] (Q₁ : Ideal R) [Q₁.IsPrime]
    (hQ₁_def : Q₁ = Q.comap (algebraMap R S))
    (hQ_eq_map : Q₁.map (algebraMap R S) = Q)
    [IsRegularLocalRing (Localization.AtPrime Q₁)] :
    IsRegularLocalRing (Localization.AtPrime Q) := by
  have hpc_le : Q₁.primeCompl ≤ Submonoid.comap (algebraMap R S).toMonoidHom Q.primeCompl := by
    intro x hx
    change algebraMap R S x ∉ Q
    intro hmem
    exact hx (by rw [hQ₁_def]; exact hmem)
  have : IsLocalHom (IsLocalization.map (Localization.AtPrime Q) (algebraMap R S) hpc_le :
      Localization.AtPrime Q₁ →+* Localization.AtPrime Q) :=
    isLocalHom_localization_map_atPrime (algebraMap R S) Q Q₁ hQ₁_def hpc_le
  exact isRegularLocalRing_of_flat_localization_map_aux Q Q₁ hQ_eq_map
    (IsLocalization.map (Localization.AtPrime Q) (algebraMap R S) hpc_le)
    (fun x => IsLocalization.map_eq hpc_le x)

private lemma isRegularLocalRing_baseChange_sub_field
    {k₀ k₁ k B₀ : Type*} [Field k₀] [Field k₁] [Field k]
    [Algebra k₀ k₁] [Algebra k₀ k] [Algebra k₁ k] [IsScalarTower k₀ k₁ k]
    [CommRing B₀] [Algebra k₀ B₀] [Algebra.FiniteType k₀ B₀]
    (Q : Ideal (k ⊗[k₀] B₀)) [Q.IsPrime]
    (Q₁ : Ideal (k₁ ⊗[k₀] B₀)) [Q₁.IsPrime]
    (hQ₁_def : Q₁ = Q.comap (Algebra.TensorProduct.map
      (IsScalarTower.toAlgHom k₀ k₁ k) (AlgHom.id k₀ B₀)).toRingHom)
    (hQ_eq_map : Q₁.map (Algebra.TensorProduct.map
      (IsScalarTower.toAlgHom k₀ k₁ k) (AlgHom.id k₀ B₀)).toRingHom = Q)
    [IsRegularLocalRing (Localization.AtPrime Q₁)] :
    IsRegularLocalRing (Localization.AtPrime Q) := by
  have : Algebra.FiniteType k (k ⊗[k₀] B₀) := inferInstance
  have : IsNoetherianRing (k ⊗[k₀] B₀) := Algebra.FiniteType.isNoetherianRing k (k ⊗[k₀] B₀)
  let : Algebra (k₁ ⊗[k₀] B₀) (k ⊗[k₀] B₀) :=
    (Algebra.TensorProduct.map (IsScalarTower.toAlgHom k₀ k₁ k) (AlgHom.id k₀ B₀)).toRingHom.toAlgebra
  have : Module.Flat (k₁ ⊗[k₀] B₀) (k ⊗[k₀] B₀) := flat_tensor_sub_field fun _ => rfl
  exact isRegularLocalRing_of_flat_localization_map Q Q₁ hQ₁_def hQ_eq_map

private lemma isRegularLocalRing_baseChange_field_aux
    {k₀ K₁ k B₀ : Type*} [Field k₀] [CharZero k₀] [Field K₁] [Field k]
    [Algebra k₀ K₁] [Algebra k₀ k] [Algebra K₁ k] [IsScalarTower k₀ K₁ k]
    [CommRing B₀] [Algebra k₀ B₀] [Algebra.FiniteType k₀ B₀]
    (𝔭₀ : Ideal B₀) [𝔭₀.IsPrime] [IsRegularLocalRing (Localization.AtPrime 𝔭₀)]
    (s₁ : Finset K₁) (hs₁_gen : IntermediateField.adjoin k₀ (s₁ : Set K₁) = ⊤)
    (Q : Ideal (k ⊗[k₀] B₀)) [Q.IsPrime]
    (hQ : Q.comap (Algebra.TensorProduct.includeRight (R := k₀) (A := k) (B := B₀)).toRingHom = 𝔭₀)
    (g : Finset (k ⊗[k₀] B₀)) (hg_span : Ideal.span (g : Set (k ⊗[k₀] B₀)) = Q)
    (hg_mem : ∀ q ∈ g, q ∈ Set.range (Algebra.TensorProduct.map
      (IsScalarTower.toAlgHom k₀ K₁ k) (AlgHom.id k₀ B₀))) :
    IsRegularLocalRing (Localization.AtPrime Q) := by
  classical
  let ι : K₁ ⊗[k₀] B₀ →ₐ[k₀] k ⊗[k₀] B₀ :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom k₀ K₁ k) (AlgHom.id k₀ B₀)
  let Q₁ : Ideal (K₁ ⊗[k₀] B₀) := Q.comap ι.toRingHom
  have : Q₁.IsPrime := Ideal.IsPrime.comap ι.toRingHom
  have hQ₁_comap : Q₁.comap (Algebra.TensorProduct.includeRight (R := k₀) (A := K₁)
      (B := B₀)).toRingHom = 𝔭₀ := by
    ext b
    rw [Ideal.mem_comap, Ideal.mem_comap, ← hQ, Ideal.mem_comap]
    have h1 : ι.toRingHom (Algebra.TensorProduct.includeRight (R := k₀) (A := K₁) (B := B₀) b) =
        Algebra.TensorProduct.includeRight (R := k₀) (A := k) (B := B₀) b := by
      change ι ((1 : K₁) ⊗ₜ[k₀] b) = (1 : k) ⊗ₜ[k₀] b
      dsimp only [ι]
      rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]
    change ι.toRingHom (Algebra.TensorProduct.includeRight (R := k₀) (A := K₁) (B := B₀) b) ∈ Q ↔
      Algebra.TensorProduct.includeRight (R := k₀) (A := k) (B := B₀) b ∈ Q
    rw [h1]
  have hReg₁ : IsRegularLocalRing (Localization.AtPrime Q₁) :=
    isRegularLocalRing_baseChange_fg 𝔭₀ s₁.card K₁ s₁ le_rfl hs₁_gen Q₁ hQ₁_comap
  have hQ_eq_map : Q₁.map ι.toRingHom = Q := by
    apply le_antisymm
    · exact Ideal.map_le_iff_le_comap.mpr le_rfl
    · rw [← hg_span, Ideal.span_le]
      intro q hqg
      obtain ⟨y', hy'⟩ := hg_mem q hqg
      have hy'_mem : y' ∈ Q₁ := by
        rw [Ideal.mem_comap]
        change ι y' ∈ Q
        rw [hy', ← hg_span]
        exact Ideal.subset_span hqg
      rw [← hy']
      exact Ideal.mem_map_of_mem ι.toRingHom hy'_mem
  exact isRegularLocalRing_baseChange_sub_field Q Q₁ rfl hQ_eq_map

private lemma isRegularLocalRing_baseChange_field
    {k₀ k B₀ : Type*} [Field k₀] [CharZero k₀] [Field k] [Algebra k₀ k]
    [CommRing B₀] [Algebra k₀ B₀] [Algebra.FiniteType k₀ B₀]
    (𝔭₀ : Ideal B₀) [𝔭₀.IsPrime] [IsRegularLocalRing (Localization.AtPrime 𝔭₀)]
    (Q : Ideal (k ⊗[k₀] B₀)) [Q.IsPrime]
    (hQ : Q.comap (Algebra.TensorProduct.includeRight (R := k₀) (A := k) (B := B₀)).toRingHom = 𝔭₀) :
    IsRegularLocalRing (Localization.AtPrime Q) := by
  classical
  have : Algebra.FiniteType k (k ⊗[k₀] B₀) := inferInstance
  have : IsNoetherianRing (k ⊗[k₀] B₀) := Algebra.FiniteType.isNoetherianRing k (k ⊗[k₀] B₀)
  obtain ⟨g, hg_span⟩ := Q.fg_of_isNoetherianRing
  have hex_fin : ∀ x : k ⊗[k₀] B₀, ∃ s : Finset k,
      x ∈ Set.range (Algebra.TensorProduct.map
        (IntermediateField.adjoin k₀ (s : Set k)).val (AlgHom.id k₀ B₀)) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨∅, 0, map_zero _⟩
    | tmul c b =>
      refine ⟨{c}, (⟨c, IntermediateField.subset_adjoin k₀ _ (by simp)⟩) ⊗ₜ[k₀] b, rfl⟩
    | add x₁ x₂ ih₁ ih₂ =>
      obtain ⟨s₁, y₁, hy₁⟩ := ih₁
      obtain ⟨s₂, y₂, hy₂⟩ := ih₂
      refine ⟨s₁ ∪ s₂, ?_⟩
      let K₁ := IntermediateField.adjoin k₀ (s₁ : Set k)
      let K₂ := IntermediateField.adjoin k₀ (s₂ : Set k)
      let K₁₂ := IntermediateField.adjoin k₀ ((s₁ ∪ s₂ : Finset k) : Set k)
      have h1 : K₁ ≤ K₁₂ := IntermediateField.adjoin.mono k₀ _ _ (by simp)
      have h2 : K₂ ≤ K₁₂ := IntermediateField.adjoin.mono k₀ _ _ (by simp)
      let i₁ : K₁ ⊗[k₀] B₀ →ₐ[k₀] K₁₂ ⊗[k₀] B₀ :=
        Algebra.TensorProduct.map (IntermediateField.inclusion h1) (AlgHom.id k₀ B₀)
      let i₂ : K₂ ⊗[k₀] B₀ →ₐ[k₀] K₁₂ ⊗[k₀] B₀ :=
        Algebra.TensorProduct.map (IntermediateField.inclusion h2) (AlgHom.id k₀ B₀)
      refine ⟨i₁ y₁ + i₂ y₂, ?_⟩
      rw [map_add]
      have hc₁ : (Algebra.TensorProduct.map K₁₂.val (AlgHom.id k₀ B₀)) (i₁ y₁) =
          (Algebra.TensorProduct.map K₁.val (AlgHom.id k₀ B₀)) y₁ := by
        change ((Algebra.TensorProduct.map K₁₂.val (AlgHom.id k₀ B₀)).comp i₁) y₁ = _
        congr 1
        ext <;> rfl
      have hc₂ : (Algebra.TensorProduct.map K₁₂.val (AlgHom.id k₀ B₀)) (i₂ y₂) =
          (Algebra.TensorProduct.map K₂.val (AlgHom.id k₀ B₀)) y₂ := by
        change ((Algebra.TensorProduct.map K₁₂.val (AlgHom.id k₀ B₀)).comp i₂) y₂ = _
        congr 1
        ext <;> rfl
      rw [hc₁, hc₂, hy₁, hy₂]
  choose sOf hsOf using hex_fin
  let s : Finset k := g.biUnion sOf
  let k₁ : IntermediateField k₀ k := IntermediateField.adjoin k₀ (s : Set k)
  let s₁ : Finset k₁ := s.attach.image fun x =>
    ⟨x.1, IntermediateField.subset_adjoin k₀ (s : Set k) x.2⟩
  have hs₁_gen : IntermediateField.adjoin k₀ (s₁ : Set k₁) = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨x, hx⟩ _
    let S : IntermediateField k₀ k :=
      { carrier := { y : k | ∃ z : IntermediateField.adjoin k₀ (s₁ : Set k₁), (z.1 : k) = y }
        mul_mem' := by rintro _ _ ⟨z₁, rfl⟩ ⟨z₂, rfl⟩; exact ⟨z₁ * z₂, rfl⟩
        one_mem' := ⟨1, rfl⟩
        add_mem' := by rintro _ _ ⟨z₁, rfl⟩ ⟨z₂, rfl⟩; exact ⟨z₁ + z₂, rfl⟩
        zero_mem' := ⟨0, rfl⟩
        inv_mem' := by rintro _ ⟨z, rfl⟩; exact ⟨z⁻¹, rfl⟩
        algebraMap_mem' := fun c => ⟨algebraMap k₀ _ c, rfl⟩ }
    have hle : k₁ ≤ S := IntermediateField.adjoin_le_iff.mpr fun y hy => by
      have hy_s₁ : (⟨y, IntermediateField.subset_adjoin k₀ (s : Set k) hy⟩ : k₁) ∈ s₁ :=
        Finset.mem_image.mpr ⟨⟨y, hy⟩, Finset.mem_attach _ _, rfl⟩
      exact ⟨⟨_, IntermediateField.subset_adjoin k₀ (s₁ : Set k₁) hy_s₁⟩, rfl⟩
    obtain ⟨z, hz⟩ := hle hx
    have hzx : z.1 = ⟨x, hx⟩ := Subtype.ext hz
    rw [← hzx]
    exact z.2
  have hg_mem : ∀ q ∈ g, q ∈ Set.range (Algebra.TensorProduct.map
      (IsScalarTower.toAlgHom k₀ k₁ k) (AlgHom.id k₀ B₀)) := by
    intro q hqg
    obtain ⟨y, hy⟩ := hsOf q
    have hle : IntermediateField.adjoin k₀ ((sOf q : Finset k) : Set k) ≤ k₁ :=
      IntermediateField.adjoin.mono k₀ _ _ (by
        intro x hx
        exact Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨q, hqg, hx⟩))
    refine ⟨Algebra.TensorProduct.map (IntermediateField.inclusion hle) (AlgHom.id k₀ B₀) y, ?_⟩
    refine Eq.trans ?_ hy
    change ((Algebra.TensorProduct.map (IsScalarTower.toAlgHom k₀ k₁ k) (AlgHom.id k₀ B₀)).comp
      (Algebra.TensorProduct.map (IntermediateField.inclusion hle) (AlgHom.id k₀ B₀))) y = _
    congr 1
    ext <;> rfl
  exact isRegularLocalRing_baseChange_field_aux (K₁ := k₁) 𝔭₀ s₁ hs₁_gen Q hQ g hg_span hg_mem

/- Section 4: Countable subfield descent (Type u, Type v) → (Type 0, Type 0) -/

private lemma countable_subfield_closure
    {K : Type*} [Field K] (S : Set K) (hS : S.Countable) :
    Countable (Subfield.closure S) := by
  let step : Set K → Set K := fun T =>
    T ∪ (T + T) ∪ (-T) ∪ (T * T) ∪ (Inv.inv '' T)
  have hstep : ∀ T : Set K, T.Countable → (step T).Countable := by
    intro T hT
    have hadd : (T + T).Countable := by
      have h1 : (T ×ˢ T).Countable := hT.prod hT
      have h2 : ((fun p : K × K => p.1 + p.2) '' (T ×ˢ T)).Countable := h1.image _
      have heq : (T + T) = (fun p : K × K => p.1 + p.2) '' (T ×ˢ T) := by
        ext x; simp [Set.mem_add]
      rwa [heq]
    have hneg : (-T).Countable := by
      have heq : (-T) = (fun x : K => -x) '' T := by ext x; simp
      rw [heq]; exact hT.image _
    have hmul : (T * T).Countable := by
      have h1 : (T ×ˢ T).Countable := hT.prod hT
      have h2 : ((fun p : K × K => p.1 * p.2) '' (T ×ˢ T)).Countable := h1.image _
      have heq : (T * T) = (fun p : K × K => p.1 * p.2) '' (T ×ˢ T) := by
        ext x; simp [Set.mem_mul]
      rwa [heq]
    exact (((hT.union hadd).union hneg).union hmul).union (hT.image _)
  let seq : ℕ → Set K := Nat.rec (S ∪ {0, 1}) (fun _ T => step T)
  have hseq_mono : ∀ n, seq n ⊆ seq (n + 1) := fun n x hx =>
    Or.inl (Or.inl (Or.inl (Or.inl hx)))
  have hseq_le : ∀ {m n}, m ≤ n → seq m ⊆ seq n := by
    intro m n hmn
    induction hmn with
    | refl => exact subset_rfl
    | step _ ih => exact ih.trans (hseq_mono _)
  have hseq_cnt : ∀ n, (seq n).Countable := by
    intro n
    induction n with
    | zero => exact hS.union ((Set.countable_singleton 0).union (Set.countable_singleton 1))
    | succ n ih => exact hstep _ ih
  let U : Subfield K :=
    { carrier := ⋃ n, seq n
      zero_mem' := Set.mem_iUnion.mpr ⟨0, Or.inr (Or.inl rfl)⟩
      one_mem' := Set.mem_iUnion.mpr ⟨0, Or.inr (Or.inr rfl)⟩
      add_mem' := by
        rintro x y hx hy
        obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hx
        obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hy
        refine Set.mem_iUnion.mpr ⟨max m n + 1, Or.inl (Or.inl (Or.inl (Or.inr ?_)))⟩
        exact ⟨x, hseq_le (le_max_left m n) hm, y, hseq_le (le_max_right m n) hn, rfl⟩
      neg_mem' := by
        rintro x hx
        obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hx
        refine Set.mem_iUnion.mpr ⟨m + 1, Or.inl (Or.inl (Or.inr ?_))⟩
        exact Set.neg_mem_neg.mpr hm
      mul_mem' := by
        rintro x y hx hy
        obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hx
        obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hy
        refine Set.mem_iUnion.mpr ⟨max m n + 1, Or.inl (Or.inr ?_)⟩
        exact ⟨x, hseq_le (le_max_left m n) hm, y, hseq_le (le_max_right m n) hn, rfl⟩
      inv_mem' := by
        rintro x hx
        obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hx
        exact Set.mem_iUnion.mpr ⟨m + 1, Or.inr ⟨x, hm, rfl⟩⟩ }
  have hle : Subfield.closure S ≤ U :=
    Subfield.closure_le.mpr fun x hx => Set.mem_iUnion.mpr ⟨0, Or.inl hx⟩
  have hU_cnt : (U : Set K).Countable := Set.countable_iUnion hseq_cnt
  exact (hU_cnt.mono hle).to_subtype

private lemma local_uniformization_type0
    (h1 : H1) (h2 : H2)
    (k F : Type) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] [CharZero k]
    (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) :
    𝒪.HasLocalUniformization k := by
  let : Algebra k 𝒪 := ((algebraMap k F).codRestrict 𝒪 hk).toAlgebra
  have : IsScalarTower k 𝒪 F := IsScalarTower.of_algebraMap_eq' rfl
  by_cases hle : Algebra.trdeg k F ≤ Algebra.trdeg k (IsLocalRing.ResidueField 𝒪) + 1
  · exact hasLocalUniformization_of_trdeg_le_residue_add_one k F 𝒪 hle
  · have hlt : Algebra.trdeg k (IsLocalRing.ResidueField 𝒪) + 1 < Algebra.trdeg k F :=
      lt_of_not_ge hle
    by_cases hrank1 : ∀ 𝒪' : ValuationSubring F, 𝒪 < 𝒪' → 𝒪' = ⊤
    · exact h1 k F 𝒪 hlt hrank1
    · push Not at hrank1
      obtain ⟨𝒪', hlt', hne'⟩ := hrank1
      exact h2 k F 𝒪 hlt ⟨𝒪', hlt', lt_of_le_of_ne le_top hne'⟩

private lemma local_uniformization_of_countable
    (h1 : H1) (h2 : H2)
    (k : Type*) (F : Type*) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F]
    [CharZero k] [Countable k] [Countable F]
    (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪) :
    𝒪.HasLocalUniformization k := by
  classical
  have : Small.{0} k := inferInstance
  have : Small.{0} F := inferInstance
  let ek : Shrink.{0} k ≃+* k := Shrink.ringEquiv.{0} k
  let eF : Shrink.{0} F ≃+* F := Shrink.ringEquiv.{0} F
  let k0 := Shrink.{0} k
  let F0 := Shrink.{0} F
  let : Algebra k0 F0 := ((eF.symm.toRingHom.comp (algebraMap k F)).comp ek.toRingHom).toAlgebra
  have hcompat : ∀ c : k0, eF (algebraMap k0 F0 c) = algebraMap k F (ek c) := fun c => by
    change eF (eF.symm (algebraMap k F (ek c))) = algebraMap k F (ek c)
    exact eF.apply_symm_apply _
  have : CharZero k0 := by
    let : Algebra k k0 := ek.symm.toRingHom.toAlgebra
    exact charZero_of_injective_algebraMap (R := k) (A := k0) ek.symm.injective
  have hEss0 : Algebra.EssFiniteType k0 F0 := by
    rw [Algebra.essFiniteType_iff]
    obtain ⟨σ, hσ⟩ := (Algebra.essFiniteType_iff k F).mp (inferInstance : Algebra.EssFiniteType k F)
    refine ⟨σ.image eF.symm, fun s => ?_⟩
    obtain ⟨t, ht, htu, hst⟩ := hσ (eF s)
    have hmap : ∀ x ∈ Algebra.adjoin k (σ : Set F),
        eF.symm x ∈ Algebra.adjoin k0 ((σ.image eF.symm : Finset F0) : Set F0) := by
      intro x hx
      refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hx
      · intro y hy
        exact Algebra.subset_adjoin (Finset.mem_coe.mpr (Finset.mem_image_of_mem eF.symm hy))
      · intro c
        have hc : eF.symm (algebraMap k F c) = algebraMap k0 F0 (ek.symm c) := by
          apply eF.injective
          rw [eF.apply_symm_apply, hcompat, ek.apply_symm_apply]
        rw [hc]
        exact Subalgebra.algebraMap_mem _ _
      · intro u v _ _ hu hv; rw [map_add]; exact add_mem hu hv
      · intro u v _ _ hu hv; rw [map_mul]; exact mul_mem hu hv
    refine ⟨eF.symm t, hmap t ht, htu.map eF.symm.toRingHom, ?_⟩
    have hprod : s * eF.symm t = eF.symm (eF s * t) := by
      rw [map_mul, eF.symm_apply_apply]
    rw [hprod]
    exact hmap _ hst
  let 𝒪0 : ValuationSubring F0 := 𝒪.comap eF.toRingHom
  have hk0 : ∀ x : k0, algebraMap k0 F0 x ∈ 𝒪0 := fun x => by
    rw [ValuationSubring.mem_comap]
    change eF (algebraMap k0 F0 x) ∈ 𝒪
    rw [hcompat]
    exact hk (ek x)
  have hLU0 : 𝒪0.HasLocalUniformization k0 := local_uniformization_type0 h1 h2 k0 F0 𝒪0 hk0
  exact hasLocalUniformization_of_ringEquiv ek eF hcompat 𝒪0 𝒪 (fun _ => Iff.rfl) hLU0

private lemma tensor_lift_injective_of_mvPoly_ker
    {k₀ k A₀' A₀ : Type*} [Field k₀] [Field k] [Algebra k₀ k]
    [CommRing A₀'] [Algebra k₀ A₀'] [CommRing A₀] [Algebra k₀ A₀] [Algebra k A₀]
    [IsScalarTower k₀ k A₀] (m : ℕ)
    (ιA : A₀' →ₐ[k₀] A₀)
    (φ₀ : MvPolynomial (Fin m) k₀ →ₐ[k₀] A₀') (hφ₀_surj : Function.Surjective φ₀)
    (φ : MvPolynomial (Fin m) k →ₐ[k] A₀) (hφ_surj : Function.Surjective φ)
    (hφ_comp : ∀ p : MvPolynomial (Fin m) k₀,
      φ (MvPolynomial.map (algebraMap k₀ k) p) = ιA (φ₀ p))
    (hI_eq : (RingHom.ker φ₀.toRingHom).map (MvPolynomial.map (algebraMap k₀ k)) =
      RingHom.ker φ.toRingHom) :
    Function.Injective
      (Algebra.TensorProduct.lift (Algebra.ofId k A₀) ιA (fun _ _ => Commute.all _ _)) := by
  let I₀ := RingHom.ker φ₀.toRingHom
  let I := RingHom.ker φ.toRingHom
  let eQ₀ : (MvPolynomial (Fin m) k₀ ⧸ I₀) ≃ₐ[k₀] A₀' :=
    Ideal.quotientKerAlgEquivOfSurjective hφ₀_surj
  let eQ : (MvPolynomial (Fin m) k ⧸ I) ≃ₐ[k] A₀ :=
    Ideal.quotientKerAlgEquivOfSurjective hφ_surj
  let eT1 : k ⊗[k₀] A₀' ≃ₐ[k] k ⊗[k₀] (MvPolynomial (Fin m) k₀ ⧸ I₀) :=
    Algebra.TensorProduct.congr (AlgEquiv.refl) eQ₀.symm
  let eT2 : k ⊗[k₀] (MvPolynomial (Fin m) k₀ ⧸ I₀) ≃ₐ[k]
      (k ⊗[k₀] MvPolynomial (Fin m) k₀) ⧸
        I₀.map (Algebra.TensorProduct.includeRight (R := k₀) (A := k)
          (B := MvPolynomial (Fin m) k₀)).toRingHom :=
    Algebra.TensorProduct.tensorQuotientEquiv k (MvPolynomial (Fin m) k₀) k I₀
  let eMv : k ⊗[k₀] MvPolynomial (Fin m) k₀ ≃ₐ[k] MvPolynomial (Fin m) k :=
    MvPolynomial.algebraTensorAlgEquiv k₀ k
  have hmap_I₀ : (I₀.map (Algebra.TensorProduct.includeRight (R := k₀) (A := k)
      (B := MvPolynomial (Fin m) k₀)).toRingHom).map (eMv : _ →+* _) = I := by
    dsimp only [I₀, I]
    rw [Ideal.map_map, ← hI_eq]
    congr 1
    ext p
    · simp [eMv]
    · simp [eMv]
  let eT3 : ((k ⊗[k₀] MvPolynomial (Fin m) k₀) ⧸
        I₀.map (Algebra.TensorProduct.includeRight (R := k₀) (A := k)
          (B := MvPolynomial (Fin m) k₀)).toRingHom) ≃ₐ[k]
      (MvPolynomial (Fin m) k ⧸ I) :=
    Ideal.quotientEquivAlg _ _ eMv hmap_I₀.symm
  let eAll : k ⊗[k₀] A₀' ≃ₐ[k] A₀ := ((eT1.trans eT2).trans eT3).trans eQ
  have heq : Algebra.TensorProduct.lift (Algebra.ofId k A₀) ιA (fun _ _ => Commute.all _ _) =
      eAll.toAlgHom := by
    apply Algebra.TensorProduct.ext'
    intro c a
    obtain ⟨p, rfl⟩ := hφ₀_surj a
    have h1 : eT1 (c ⊗ₜ[k₀] φ₀ p) = c ⊗ₜ[k₀] Ideal.Quotient.mk I₀ p := by
      change c ⊗ₜ[k₀] eQ₀.symm (φ₀ p) = c ⊗ₜ[k₀] Ideal.Quotient.mk I₀ p
      congr 1
      apply eQ₀.injective
      rw [eQ₀.apply_symm_apply]
      rfl
    have h2 : eAll (c ⊗ₜ[k₀] φ₀ p) = eQ (Ideal.Quotient.mk I (eMv (c ⊗ₜ[k₀] p))) := by
      change eQ (eT3 (eT2 (eT1 (c ⊗ₜ[k₀] φ₀ p)))) = _
      rw [h1]
      rfl
    change algebraMap k A₀ c * ιA (φ₀ p) = eAll (c ⊗ₜ[k₀] φ₀ p)
    rw [h2]
    change algebraMap k A₀ c * ιA (φ₀ p) = φ (eMv (c ⊗ₜ[k₀] p))
    rw [MvPolynomial.algebraTensorAlgEquiv_tmul, map_smul, Algebra.smul_def, hφ_comp]
  rw [heq]
  exact eAll.injective

private lemma ascend_uniformization_opaque
    {k₀ k F₀ F : Type*} [Field k₀] [CharZero k₀] [Field k] [Field F₀] [Field F]
    [Algebra k₀ k] [Algebra k₀ F₀] [Algebra k₀ F] [Algebra k F] [Algebra F₀ F]
    [IsScalarTower k₀ k F] [IsScalarTower k₀ F₀ F]
    (𝒪 : ValuationSubring F) (hk : ∀ x : k, algebraMap k F x ∈ 𝒪)
    (hμF_inj : Function.Injective
      (Algebra.TensorProduct.lift (Algebra.ofId k F)
        (IsScalarTower.toAlgHom k₀ F₀ F) (fun _ _ => Commute.all _ _)))
    (hgenF : IntermediateField.adjoin k (Set.range (algebraMap F₀ F)) = ⊤)
    (hLU₀ : (𝒪.comap (algebraMap F₀ F)).HasLocalUniformization k₀) :
    𝒪.HasLocalUniformization k := by
  classical
  let 𝒪₀ : ValuationSubring F₀ := 𝒪.comap (algebraMap F₀ F)
  obtain ⟨B₀, hB₀_in, hB₀_fin, hB₀_frac, hB₀_reg⟩ := hLU₀
  let μF : k ⊗[k₀] F₀ →ₐ[k] F :=
    Algebra.TensorProduct.lift (Algebra.ofId k F)
      (IsScalarTower.toAlgHom k₀ F₀ F) (fun _ _ => Commute.all _ _)
  let ιB₀ : k ⊗[k₀] B₀ →ₐ[k] k ⊗[k₀] F₀ :=
    Algebra.TensorProduct.map (AlgHom.id k k) B₀.val
  have hιB₀_inj : Function.Injective ιB₀ := by
    have : Module.Flat k₀ k := inferInstance
    have hlin : ιB₀.toLinearMap = LinearMap.lTensor k B₀.val.toLinearMap := by
      ext c b; simp [ιB₀]
    intro x y hxy
    have h1 : LinearMap.lTensor k B₀.val.toLinearMap x =
        LinearMap.lTensor k B₀.val.toLinearMap y := by
      rw [← hlin]; exact hxy
    exact Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective h1
  let μB : k ⊗[k₀] B₀ →ₐ[k] F := μF.comp ιB₀
  have hμB_inj : Function.Injective μB := hμF_inj.comp hιB₀_inj
  let B : Subalgebra k F := μB.range
  let eB : k ⊗[k₀] B₀ ≃ₐ[k] B := AlgEquiv.ofInjective μB hμB_inj
  have hB_in : ∀ b : B, (b : F) ∈ 𝒪 := by
    rintro ⟨_, z, rfl⟩
    change μB z ∈ 𝒪
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact zero_mem 𝒪
    | tmul c b₀ =>
      change algebraMap k F c * algebraMap F₀ F (b₀ : F₀) ∈ 𝒪
      exact mul_mem (hk c) (hB₀_in b₀)
    | add z₁ z₂ h₁ h₂ => rw [map_add]; exact add_mem h₁ h₂
  have : Algebra.FiniteType k (k ⊗[k₀] B₀) := inferInstance
  have hB_fin : Algebra.FiniteType k B := Algebra.FiniteType.of_surjective eB.toAlgHom eB.surjective
  have hB_frac : IsFractionRing B F := by
    apply isFractionRing_of_adjoin_eq_top B
    rw [eq_top_iff, ← hgenF, IntermediateField.adjoin_le_iff]
    rintro _ ⟨f₀, rfl⟩
    obtain ⟨⟨b₁, b₂⟩, hb₁₂⟩ := IsLocalization.surj (nonZeroDivisors B₀) f₀
    have hb₁B : algebraMap F₀ F (b₁ : F₀) ∈ B := ⟨(1 : k) ⊗ₜ[k₀] b₁, by simp [μB, μF, ιB₀]⟩
    have hb₂B : algebraMap F₀ F (b₂.1 : F₀) ∈ B := ⟨(1 : k) ⊗ₜ[k₀] b₂.1, by simp [μB, μF, ιB₀]⟩
    have hb₂0 : algebraMap F₀ F (b₂.1 : F₀) ≠ 0 := by
      have h0 : (b₂ : B₀) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp b₂.2
      exact fun h => h0 (Subtype.ext ((algebraMap F₀ F).injective (h.trans (map_zero _).symm)))
    have hdiv : algebraMap F₀ F f₀ = algebraMap F₀ F (b₁ : F₀) / algebraMap F₀ F (b₂.1 : F₀) := by
      have hmul0 : f₀ * (b₂.1 : F₀) = (b₁ : F₀) := hb₁₂
      have hF : algebraMap F₀ F f₀ * algebraMap F₀ F (b₂.1 : F₀) = algebraMap F₀ F (b₁ : F₀) := by
        rw [← map_mul, hmul0]
      rw [← hF, mul_div_cancel_right₀ _ hb₂0]
    rw [hdiv]
    exact div_mem (IntermediateField.subset_adjoin k _ hb₁B)
      (IntermediateField.subset_adjoin k _ hb₂B)
  let Q : Ideal (k ⊗[k₀] B₀) := (𝒪.centerOn B hB_in).comap eB.toRingHom
  have : Q.IsPrime := Ideal.IsPrime.comap eB.toRingHom
  have hQ_comap : Q.comap (Algebra.TensorProduct.includeRight (R := k₀) (A := k) (B := B₀)).toRingHom =
      𝒪₀.centerOn B₀ hB₀_in := by
    ext b₀
    rw [Ideal.mem_comap, Ideal.mem_comap, mem_centerOn_iff_zero_or_inv_notMem,
      mem_centerOn_iff_zero_or_inv_notMem]
    have hval : (eB ((1 : k) ⊗ₜ[k₀] b₀) : F) = algebraMap F₀ F (b₀ : F₀) := by
      change μB ((1 : k) ⊗ₜ[k₀] b₀) = algebraMap F₀ F (b₀ : F₀)
      simp [μB, μF, ιB₀]
    change ((eB ((1 : k) ⊗ₜ[k₀] b₀) : F) = 0 ∨ ((eB ((1 : k) ⊗ₜ[k₀] b₀) : F))⁻¹ ∉ 𝒪) ↔
      ((b₀ : F₀) = 0 ∨ (b₀ : F₀)⁻¹ ∉ 𝒪₀)
    rw [hval]
    rw [map_eq_zero_iff _ (algebraMap F₀ F).injective, ← map_inv₀ (algebraMap F₀ F)]
    rfl
  have hRegQ : IsRegularLocalRing (Localization.AtPrime Q) :=
    isRegularLocalRing_baseChange_field (𝒪₀.centerOn B₀ hB₀_in) Q hQ_comap
  have hpc : Q.primeCompl.map eB.toRingHom.toMonoidHom = (𝒪.centerOn B hB_in).primeCompl := by
    ext y
    simp only [Submonoid.mem_map, Ideal.mem_primeCompl_iff]
    constructor
    · rintro ⟨x, hx, rfl⟩ hmem
      exact hx hmem
    · intro hy
      refine ⟨eB.symm y, fun hx => hy ?_, eB.apply_symm_apply y⟩
      have h1 : eB (eB.symm y) ∈ 𝒪.centerOn B hB_in := hx
      rwa [eB.apply_symm_apply] at h1
  let eLoc : Localization.AtPrime Q ≃+* Localization.AtPrime (𝒪.centerOn B hB_in) :=
    IsLocalization.ringEquivOfRingEquiv _ _ eB.toRingEquiv hpc
  have hB_reg : IsRegularLocalRing (Localization.AtPrime (𝒪.centerOn B hB_in)) :=
    @IsRegularLocalRing.of_ringEquiv _ _ hRegQ _ _ eLoc
  exact ⟨B, hB_in, hB_fin, hB_frac, hB_reg⟩

private lemma tensor_field_lift_injective
    {k₀ k F : Type*} [Field k₀] [Field k] [Field F]
    [Algebra k₀ k] [Algebra k₀ F] [Algebra k F] [IsScalarTower k₀ k F]
    (A₀' : Subalgebra k₀ F) (F₀ : IntermediateField k₀ F) (hA₀'_le_F₀ : A₀' ≤ F₀.toSubalgebra)
    (A₀ : Subalgebra k F) (ιA₀' : A₀' →ₐ[k₀] A₀)
    (hι_val : ∀ a : A₀', (ιA₀' a : F) = (a : F))
    (hF₀_frac : ∀ x : F₀, ∃ a b : A₀', (b : F) ≠ 0 ∧ (b : F) * (x : F) = (a : F))
    (hμA_inj : Function.Injective (Algebra.TensorProduct.lift (Algebra.ofId k A₀) ιA₀'
      (fun _ _ => Commute.all _ _))) :
    Function.Injective (Algebra.TensorProduct.lift (Algebra.ofId k F)
      (IsScalarTower.toAlgHom k₀ F₀ F) (fun _ _ => Commute.all _ _)) := by
  let μA : k ⊗[k₀] A₀' →ₐ[k] A₀ :=
    Algebra.TensorProduct.lift (Algebra.ofId k A₀) ιA₀' (fun _ _ => Commute.all _ _)
  let μF : k ⊗[k₀] F₀ →ₐ[k] F :=
    Algebra.TensorProduct.lift (Algebra.ofId k F) (IsScalarTower.toAlgHom k₀ F₀ F)
      (fun _ _ => Commute.all _ _)
  rw [injective_iff_map_eq_zero]
  intro z hz
  have hclear : ∀ w : k ⊗[k₀] F₀, ∃ (d : A₀') (u : k ⊗[k₀] A₀'),
      (d : F) ≠ 0 ∧
      ((1 : k) ⊗ₜ[k₀] (⟨(d : F), hA₀'_le_F₀ d.2⟩ : F₀)) * w =
        Algebra.TensorProduct.map (AlgHom.id k k)
          (Subalgebra.inclusion hA₀'_le_F₀) u := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => exact ⟨1, 0, one_ne_zero, by simp⟩
    | tmul c f =>
      obtain ⟨a, d, hd0, had⟩ := hF₀_frac f
      refine ⟨d, c ⊗ₜ[k₀] a, hd0, ?_⟩
      simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul, Algebra.TensorProduct.map_tmul,
        AlgHom.id_apply]
      congr 1
      exact Subtype.ext had
    | add w₁ w₂ ih₁ ih₂ =>
      obtain ⟨d₁, u₁, hd₁, hu₁⟩ := ih₁
      obtain ⟨d₂, u₂, hd₂, hu₂⟩ := ih₂
      refine ⟨d₁ * d₂, ((1 : k) ⊗ₜ[k₀] d₂) * u₁ + ((1 : k) ⊗ₜ[k₀] d₁) * u₂,
        mul_ne_zero hd₁ hd₂, ?_⟩
      rw [map_add, map_mul, map_mul, mul_add]
      have hinc : ∀ d : A₀',
          Algebra.TensorProduct.map (AlgHom.id k k) (Subalgebra.inclusion hA₀'_le_F₀)
            ((1 : k) ⊗ₜ[k₀] d) = (1 : k) ⊗ₜ[k₀] (⟨(d : F), hA₀'_le_F₀ d.2⟩ : F₀) := fun _ => rfl
      rw [hinc d₂, hinc d₁, ← hu₁, ← hu₂]
      have hd_mul : (1 : k) ⊗ₜ[k₀] (⟨((d₁ * d₂ : A₀') : F), hA₀'_le_F₀ (d₁ * d₂).2⟩ : F₀) =
          ((1 : k) ⊗ₜ[k₀] (⟨(d₁ : F), hA₀'_le_F₀ d₁.2⟩ : F₀)) *
            ((1 : k) ⊗ₜ[k₀] (⟨(d₂ : F), hA₀'_le_F₀ d₂.2⟩ : F₀)) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
        rfl
      rw [hd_mul]
      ring
  obtain ⟨d, u, hd0, hu⟩ := hclear z
  have hμA_u : μA u = 0 := by
    apply Subtype.ext
    change (μA u : F) = 0
    have hcomm : ∀ v : k ⊗[k₀] A₀', (μA v : F) =
        μF (Algebra.TensorProduct.map (AlgHom.id k k) (Subalgebra.inclusion hA₀'_le_F₀) v) := by
      intro v
      induction v using TensorProduct.induction_on with
      | zero =>
        rw [map_zero, map_zero, map_zero]
        rfl
      | tmul c a =>
        rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
        dsimp only [μA, μF]
        rw [Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.lift_tmul]
        change algebraMap k F c * (ιA₀' a : F) = algebraMap k F c * (a : F)
        rw [hι_val]
      | add u₁ u₂ h₁ h₂ =>
        rw [map_add, map_add, map_add]
        exact congrArg₂ (· + ·) h₁ h₂
    rw [hcomm u, ← hu, map_mul, hz, mul_zero]
  have hu0 : u = 0 := hμA_inj (by rw [hμA_u, map_zero])
  rw [hu0, map_zero] at hu
  let dF₀ : F₀ := ⟨(d : F), hA₀'_le_F₀ d.2⟩
  have hdF₀ : dF₀ ≠ 0 := fun h0 => hd0 (congrArg Subtype.val h0)
  have hinv := congrArg (fun w => ((1 : k) ⊗ₜ[k₀] dF₀⁻¹) * w) hu
  change ((1 : k) ⊗ₜ[k₀] dF₀⁻¹) * (((1 : k) ⊗ₜ[k₀] dF₀) * z) =
      ((1 : k) ⊗ₜ[k₀] dF₀⁻¹) * 0 at hinv
  rw [← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
    inv_mul_cancel₀ hdF₀, mul_zero] at hinv
  have hone : ((1 : k) ⊗ₜ[k₀] (1 : F₀)) = (1 : k ⊗[k₀] F₀) := rfl
  rw [hone, one_mul] at hinv
  exact hinv

end

theorem main : H1 → H2 → type_of% @LocalUniformization.local_uniformization_of_charZero := by
  intro h1 h2 k F _ _ _ _ _ 𝒪 hk
  classical
  obtain ⟨A₀, hA₀_in, hA₀_fin, hA₀_frac⟩ := exists_affine_model_in_valuationSubring k F 𝒪 hk
  obtain ⟨sFin, hsFin⟩ := hA₀_fin.out
  let m : ℕ := sFin.card
  let eIdx : Fin m ≃ sFin := (Fintype.equivFinOfCardEq (Fintype.card_coe sFin)).symm
  let gen : Fin m → A₀ := fun i => (eIdx i).1
  let φ : MvPolynomial (Fin m) k →ₐ[k] A₀ := MvPolynomial.aeval gen
  have hφ_surj : Function.Surjective φ := by
    intro a
    have ha : a ∈ Algebra.adjoin k (sFin : Set A₀) := by rw [hsFin]; trivial
    refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ ha
    · intro x hx
      refine ⟨MvPolynomial.X (eIdx.symm ⟨x, hx⟩), ?_⟩
      simp [φ, gen]
    · intro c; exact ⟨MvPolynomial.C c, by simp [φ]⟩
    · rintro x y _ _ ⟨px, rfl⟩ ⟨py, rfl⟩; exact ⟨px + py, map_add φ px py⟩
    · rintro x y _ _ ⟨px, rfl⟩ ⟨py, rfl⟩; exact ⟨px * py, map_mul φ px py⟩
  let I : Ideal (MvPolynomial (Fin m) k) := RingHom.ker φ.toRingHom
  have : IsNoetherianRing (MvPolynomial (Fin m) k) := inferInstance
  obtain ⟨G, hG_span⟩ := I.fg_of_isNoetherianRing
  let C : Finset k := G.biUnion fun f => f.support.image f.coeff
  let k₀ : Subfield k := Subfield.closure (C : Set k)
  have hcnt_k₀ : Countable k₀ := countable_subfield_closure (C : Set k) C.countable_toSet
  let A₀' : Subalgebra k₀ F := Algebra.adjoin k₀ (Set.range fun i : Fin m => (gen i : F))
  let F₀ : IntermediateField k₀ F := IntermediateField.adjoin k₀ (Set.range fun i : Fin m => (gen i : F))
  have hA₀'_le_F₀ : A₀' ≤ F₀.toSubalgebra := IntermediateField.algebra_adjoin_le_adjoin k₀ _
  have hA₀'_le_A₀ : (A₀' : Set F) ⊆ (A₀ : Set F) := by
    intro x hx
    refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨i, rfl⟩; exact (gen i).2
    · intro c; exact A₀.algebraMap_mem (c : k)
    · intro x y _ _ hx hy; exact A₀.add_mem hx hy
    · intro x y _ _ hx hy; exact A₀.mul_mem hx hy
  let φ₀ : MvPolynomial (Fin m) k₀ →ₐ[k₀] A₀' :=
    MvPolynomial.aeval fun i : Fin m =>
      (⟨(gen i : F), Algebra.subset_adjoin ⟨i, rfl⟩⟩ : A₀')
  have hφ₀_surj : Function.Surjective φ₀ := by
    rintro ⟨a, ha⟩
    refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ ha
    · rintro _ ⟨i, rfl⟩; exact ⟨MvPolynomial.X i, by simp [φ₀]⟩
    · intro c
      refine ⟨MvPolynomial.C c, Subtype.ext ?_⟩
      simp [φ₀]
    · rintro x y _ _ ⟨px, hpx⟩ ⟨py, hpy⟩
      refine ⟨px + py, Subtype.ext ?_⟩
      change ((φ₀ (px + py) : A₀') : F) = x + y
      rw [map_add]
      exact congrArg₂ (· + ·) (congrArg Subtype.val hpx) (congrArg Subtype.val hpy)
    · rintro x y _ _ ⟨px, hpx⟩ ⟨py, hpy⟩
      refine ⟨px * py, Subtype.ext ?_⟩
      change ((φ₀ (px * py) : A₀') : F) = x * y
      rw [map_mul]
      exact congrArg₂ (· * ·) (congrArg Subtype.val hpx) (congrArg Subtype.val hpy)
  have hcnt_A₀' : Countable A₀' := by
    have hcnt_mv : Countable (MvPolynomial (Fin m) k₀) := by
      let toF : MvPolynomial (Fin m) k₀ → ((Fin m →₀ ℕ) →₀ k₀) := fun p =>
        Finsupp.onFinset p.support (fun d => p.coeff d) (fun d hd => MvPolynomial.mem_support_iff.mpr hd)
      have htoF_inj : Function.Injective toF := by
        intro p q hpq
        ext d
        have h1 := congrArg (fun f => f d) hpq
        simpa [toF] using h1
      exact htoF_inj.countable
    exact Function.Surjective.countable hφ₀_surj
  have hF₀_frac : ∀ x : F₀, ∃ a b : A₀', (b : F) ≠ 0 ∧ (b : F) * (x : F) = (a : F) := by
    let S : IntermediateField k₀ F :=
      { carrier := { x : F | ∃ (a b : A₀'), (b : F) ≠ 0 ∧ (b : F) * x = (a : F) }
        mul_mem' := by
          rintro x y ⟨a₁, b₁, hb₁, h₁⟩ ⟨a₂, b₂, hb₂, h₂⟩
          refine ⟨a₁ * a₂, b₁ * b₂, mul_ne_zero hb₁ hb₂, ?_⟩
          push_cast
          calc ((b₁ : F) * (b₂ : F)) * (x * y) = ((b₁ : F) * x) * ((b₂ : F) * y) := by ring
            _ = (a₁ : F) * (a₂ : F) := by rw [h₁, h₂]
        one_mem' := ⟨1, 1, one_ne_zero, by simp⟩
        add_mem' := by
          rintro x y ⟨a₁, b₁, hb₁, h₁⟩ ⟨a₂, b₂, hb₂, h₂⟩
          refine ⟨a₁ * b₂ + a₂ * b₁, b₁ * b₂, mul_ne_zero hb₁ hb₂, ?_⟩
          push_cast
          calc ((b₁ : F) * (b₂ : F)) * (x + y)
              = ((b₁ : F) * x) * (b₂ : F) + ((b₂ : F) * y) * (b₁ : F) := by ring
            _ = (a₁ : F) * (b₂ : F) + (a₂ : F) * (b₁ : F) := by rw [h₁, h₂]
        zero_mem' := ⟨0, 1, one_ne_zero, by simp⟩
        inv_mem' := by
          rintro x ⟨a, b, hb, h⟩
          by_cases hx : x = 0
          · subst hx; exact ⟨0, 1, one_ne_zero, by simp⟩
          · have ha0 : (a : F) ≠ 0 := by rw [← h]; exact mul_ne_zero hb hx
            refine ⟨b, a, ha0, ?_⟩
            calc (a : F) * x⁻¹ = ((b : F) * x) * x⁻¹ := by rw [h]
              _ = (b : F) := by rw [mul_assoc, mul_inv_cancel₀ hx, mul_one]
        algebraMap_mem' := fun c => ⟨algebraMap k₀ A₀' c, 1, one_ne_zero, by simp⟩ }
    have hleS : F₀ ≤ S := IntermediateField.adjoin_le_iff.mpr fun _ ⟨i, hi⟩ =>
      ⟨⟨(gen i : F), Algebra.subset_adjoin ⟨i, rfl⟩⟩, 1, one_ne_zero, by simp [hi]⟩
    intro x
    exact hleS x.2
  have hcnt_F₀ : Countable F₀ := by
    let surj : A₀' × A₀' → F₀ := fun p =>
      ⟨(p.1 : F) / (p.2 : F), F₀.div_mem (hA₀'_le_F₀ p.1.2) (hA₀'_le_F₀ p.2.2)⟩
    have hsurj : Function.Surjective surj := by
      intro x
      obtain ⟨a, b, hb0, hab⟩ := hF₀_frac x
      refine ⟨(a, b), Subtype.ext ?_⟩
      change (a : F) / (b : F) = (x : F)
      rw [← hab, mul_div_cancel_left₀ _ hb0]
    exact Function.Surjective.countable hsurj
  have hEss_F₀ : Algebra.EssFiniteType k₀ F₀ := by
    rw [IntermediateField.essFiniteType_iff]
    refine ⟨Finset.univ.image fun i : Fin m => (gen i : F), ?_⟩
    simp [F₀]
  let I₀ : Ideal (MvPolynomial (Fin m) k₀) := RingHom.ker φ₀.toRingHom
  let jPoly : MvPolynomial (Fin m) k₀ →+* MvPolynomial (Fin m) k :=
    MvPolynomial.map (algebraMap k₀ k)
  let ιA₀' : A₀' →ₐ[k₀] A₀ :=
    { toFun := fun a => ⟨(a : F), hA₀'_le_A₀ a.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  have hφ_comp : ∀ p : MvPolynomial (Fin m) k₀, φ (jPoly p) = ιA₀' (φ₀ p) := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C c =>
      apply Subtype.ext
      change (φ (MvPolynomial.map (algebraMap k₀ k) (MvPolynomial.C c)) : F) =
        (φ₀ (MvPolynomial.C c) : F)
      rw [MvPolynomial.map_C]
      simp [φ, φ₀]
      rfl
    | add p₁ p₂ h₁ h₂ =>
      rw [map_add, map_add, map_add, map_add, h₁, h₂]
    | mul_X p₁ i h₁ =>
      rw [map_mul, map_mul, map_mul, map_mul, h₁]
      congr 1
      apply Subtype.ext
      change (φ (MvPolynomial.map (algebraMap k₀ k) (MvPolynomial.X i)) : F) =
        (φ₀ (MvPolynomial.X i) : F)
      rw [MvPolynomial.map_X]
      simp [φ, φ₀]
  have hI_eq_map : I₀.map jPoly = I := by
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro p hp
      rw [Ideal.mem_comap, RingHom.mem_ker]
      change φ (jPoly p) = 0
      rw [hφ_comp]
      have hp0 : φ₀ p = 0 := hp
      rw [hp0, map_zero]
    · rw [← hG_span, Ideal.span_le]
      intro f hfG
      have hcoeff : ∀ d : Fin m →₀ ℕ, f.coeff d ∈ k₀ := by
        intro d
        by_cases hd : d ∈ f.support
        · exact Subfield.subset_closure (Finset.mem_coe.mpr
            (Finset.mem_biUnion.mpr ⟨f, hfG, Finset.mem_image_of_mem f.coeff hd⟩))
        · rw [MvPolynomial.notMem_support_iff.mp hd]
          exact k₀.zero_mem
      let f₀ : MvPolynomial (Fin m) k₀ :=
        ∑ d ∈ f.support, MvPolynomial.monomial d ⟨f.coeff d, hcoeff d⟩
      have hf₀_map : jPoly f₀ = f := by
        dsimp only [f₀, jPoly]
        rw [map_sum]
        conv_rhs => rw [f.as_sum]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [MvPolynomial.map_monomial]
        rfl
      have hf₀_mem : f₀ ∈ I₀ := by
        rw [RingHom.mem_ker]
        apply Subtype.ext
        have h1 : ιA₀' (φ₀ f₀) = φ f := by rw [← hf₀_map, hφ_comp]
        have hfI : f ∈ I := by rw [← hG_span]; exact Ideal.subset_span hfG
        have hf0 : φ f = 0 := hfI
        rw [hf0] at h1
        exact congrArg (fun a : A₀ => (a : F)) h1
      rw [← hf₀_map]
      exact Ideal.mem_map_of_mem jPoly hf₀_mem
  have hμA_inj := tensor_lift_injective_of_mvPoly_ker m ιA₀' φ₀ hφ₀_surj φ hφ_surj hφ_comp hI_eq_map
  have hμF_inj :=
    tensor_field_lift_injective A₀' F₀ hA₀'_le_F₀ A₀ ιA₀' (fun _ => rfl) hF₀_frac hμA_inj
  have hgenF : IntermediateField.adjoin k (Set.range (algebraMap F₀ F)) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors A₀) x
    have hA₀_sub : ∀ y : A₀, (y : F) ∈ IntermediateField.adjoin k (Set.range (algebraMap F₀ F)) := by
      intro y
      have hy : y ∈ Algebra.adjoin k (sFin : Set A₀) := by rw [hsFin]; trivial
      refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hy
      · intro z hz
        have hmem : (z : F) ∈ F₀ :=
          IntermediateField.subset_adjoin k₀ _ ⟨eIdx.symm ⟨z, hz⟩, by simp [gen]⟩
        exact IntermediateField.subset_adjoin k _ ⟨⟨(z : F), hmem⟩, rfl⟩
      · intro c; exact IntermediateField.algebraMap_mem _ c
      · intro u v _ _ hu hv; exact add_mem hu hv
      · intro u v _ _ hu hv; exact mul_mem hu hv
    have hb0 : ((b : A₀) : F) ≠ 0 := fun h0 =>
      (mem_nonZeroDivisors_iff_ne_zero.mp b.2) (Subtype.ext h0)
    have hx_eq : x = (a : F) / ((b : A₀) : F) := by
      have hF : x * ((b : A₀) : F) = (a : F) := hab
      rw [← hF, mul_div_cancel_right₀ _ hb0]
    rw [hx_eq]
    exact div_mem (hA₀_sub a) (hA₀_sub b.1)
  have hLU₀ : (𝒪.comap (algebraMap F₀ F)).HasLocalUniformization k₀ :=
    local_uniformization_of_countable h1 h2 k₀ F₀ (𝒪.comap (algebraMap F₀ F)) (fun c => hk (c : k))
  exact ascend_uniformization_opaque (k₀ := k₀) (F₀ := F₀) 𝒪 hk hμF_inj hgenF hLU₀

end OMA.R_LocalUniformization_local_uniformization_of_charZero_R1
