import OMAReductions.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1
import Mathlib

/-! It suffices to approximate the fundamental units, and sometimes one root of unity,
by global relative norms at the specified finite place. The image of the local norm
on units is open by the inverse function theorem and hence closed. The product over
cosets of the local Galois group turns each global norm into a local norm.

The dense Galois completion lemmas are from @ysanatomic, OMA PR #8922. The canonical
map between completions is adapted from AdicCompletionMap.lean in n-yamaguchi-0729/ClassFieldTheory
(revision 2e6280f9d2579705a0cc6c76ec68c2b60f9c601a, Apache 2.0). -/

-- Dense-field and completion lemmas from the merged OMA PR #8922.
namespace TunnellDenseCompletions
open Polynomial IsDedekindDomain NumberField
open scoped Classical WithZero WithZeroTopology ValuativeRel

/- A completion generated densely by a finite Galois field is itself a finite
Galois extension of the completed base. -/
theorem dense_galois {D N V W : Type} [Field D] [Field N] [Algebra D N]
    [FiniteDimensional D N] [IsGalois D N] [NontriviallyNormedField V] [CompleteSpace V]
    [Field W] [UniformSpace W] [T2Space W] [IsTopologicalRing W]
    [Algebra D V] [Algebra V W] [Algebra D W] [IsScalarTower D V W]
    [ContinuousSMul V W] (j : N →ₐ[D] W) (hd : DenseRange j) :
    FiniteDimensional V W ∧ IsGalois V W := by
  classical
  obtain ⟨p, hp, hs⟩ := IsGalois.is_separable_splitting_field D N
  let q := p.map (algebraMap D V)
  have hroots : q.rootSet W = p.rootSet W := by
    simp only [q, Polynomial.rootSet, Polynomial.aroots, Polynomial.map_map,
      ← IsScalarTower.algebraMap_eq]
  have hsplit : (q.map (algebraMap V W)).Splits := by
    rw [show q = p.map (algebraMap D V) from rfl, Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
    exact Polynomial.Splits.of_algHom (Polynomial.IsSplittingField.splits N p) j
  let E := IntermediateField.adjoin V (q.rootSet W)
  haveI : q.IsSplittingField V E := IntermediateField.adjoin_rootSet_isSplittingField hsplit
  haveI : FiniteDimensional V E := Polynomial.IsSplittingField.finiteDimensional E q
  have hclosed : IsClosed (E : Set W) := E.toSubalgebra.toSubmodule.closed_of_finiteDimensional
  have hsub : j.range ≤ E.toSubalgebra.restrictScalars D := by
    rw [← Polynomial.IsSplittingField.adjoin_rootSet_eq_range N p j, Algebra.adjoin_le_iff]
    intro x hx
    exact IntermediateField.subset_adjoin V _ (hroots.symm ▸ hx)
  have htop : E = ⊤ := by
    apply top_unique
    intro x _
    exact hd.induction_on (p := fun y => y ∈ E) x hclosed (fun n => hsub ⟨n,rfl⟩)
  haveI : q.IsSplittingField V W := isSplittingField_iff_intermediateField.mpr ⟨hsplit, htop⟩
  exact ⟨Polynomial.IsSplittingField.finiteDimensional W q,
    IsGalois.of_separable_splitting_field (p:=q) hp.map⟩

theorem fields {D N : Type} [Field D] [NumberField D] [Field N] [NumberField N]
    [Algebra D N] [FiniteDimensional D N] [IsGalois D N]
    (v : HeightOneSpectrum (𝓞 D)) (t : HeightOneSpectrum (𝓞 N))
    (f : v.adicCompletion D →+* t.adicCompletion N) (hf : Continuous f)
    (hc : ∀ c : D, f (algebraMap D _ c) = algebraMap N _ (algebraMap D N c)) :
    letI : Algebra (v.adicCompletion D) (t.adicCompletion N) := f.toAlgebra
    FiniteDimensional (v.adicCompletion D) (t.adicCompletion N) ∧ IsGalois (v.adicCompletion D) (t.adicCompletion N) := by
  let V := v.adicCompletion D
  let W := t.adicCompletion N
  letI : NontriviallyNormedField V := Valued.toNontriviallyNormedField V ℤᵐ⁰
  letI : Algebra V W := f.toAlgebra
  letI : Algebra D W := ((algebraMap N W).comp (algebraMap D N)).toAlgebra
  letI : IsScalarTower D V W := IsScalarTower.of_algebraMap_eq fun x => (hc x).symm
  letI : ContinuousSMul V W := continuousSMul_of_algebraMap V W hf
  let j : N →ₐ[D] W := ⟨algebraMap N W,fun _ => rfl⟩
  exact dense_galois (V:=V) j (t.denseRange_algebraMap N)

end TunnellDenseCompletions

-- The construction via mapRingHom is adapted from AdicCompletionMap.lean in
-- n-yamaguchi-0729/ClassFieldTheory, revision 2e6280f9d2579705a0cc6c76ec68c2b60f9c601a.
-- Here the prime is specified by a LiesOver instance and the lift is unique.
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField

namespace TunnellReciprocity

theorem existsUnique_completionMap {D N : Type} [Field D] [NumberField D]
    [Field N] [NumberField N] [Algebra D N]
    (v : HeightOneSpectrum (𝓞 D)) (t : HeightOneSpectrum (𝓞 N))
    [t.asIdeal.LiesOver v.asIdeal] :
    ∃! f : v.adicCompletion D →+* t.adicCompletion N, Continuous f ∧
      ∀ c : D, f (algebraMap D (v.adicCompletion D) c) =
        algebraMap N (t.adicCompletion N) (algebraMap D N c) := by
  let g := algebraMap (WithVal (v.valuation D)) (WithVal (t.valuation N))
  have hg : Continuous g := (uniformContinuous_algebraMap_liesOver D N v t).continuous
  let f := (adicCompletion.equiv N t).symm.toRingHom.comp
    ((UniformSpace.Completion.mapRingHom g hg).comp (adicCompletion.equiv D v).toRingHom)
  have hf : Continuous f := (adicCompletion.continuous_ofCompletion N t).comp
    (UniformSpace.Completion.continuous_map.comp (adicCompletion.continuous_toCompletion D v))
  have hc (c : D) : f (algebraMap D (v.adicCompletion D) c) =
      algebraMap N (t.adicCompletion N) (algebraMap D N c) := by
    apply adicCompletion.ext
    exact UniformSpace.Completion.mapRingHom_coe hg ((WithVal.equiv (v.valuation D)).symm c)
  refine ⟨f, ⟨hf, hc⟩, ?_⟩
  intro j hj
  apply DFunLike.ext'
  apply (v.denseRange_algebraMap D).equalizer hj.1 hf
  exact funext fun c => (hj.2 c).trans (hc c).symm

end TunnellReciprocity

namespace TunnellReciprocity
open scoped Classical IsMulCommutative

lemma prod_over_restriction {G L M : Type*} [CommGroup G] [Group L] [CommMonoid M]
    [Fintype G] [Fintype L] (r : L →* G) (hi : Function.Injective r) (k : G → M) :
    let H := r.range
    ∏ g : G, k g = ∏ q : G ⧸ H, ∏ s : L, k (r s * q.out) := by
  classical
  let H := r.range
  let π := QuotientGroup.mk' H
  have hr (s : L) : π (r s) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr ⟨s, rfl⟩
  have hout (q : G ⧸ H) : π q.out = q := Quotient.out_eq' q
  let φ (p : (G ⧸ H) × L) := r p.2 * p.1.out
  have hπ (q : G ⧸ H) (s : L) : π (φ (q, s)) = q := by
    simp only [φ, map_mul, hr, one_mul, hout]
  have hinj : Function.Injective φ := by
    rintro ⟨q, a⟩ ⟨t, b⟩ h
    have eq : q = t := (hπ q a).symm.trans ((congrArg π h).trans (hπ t b))
    subst t
    exact Prod.ext rfl (hi (mul_right_cancel h))
  have hsur : Function.Surjective φ := by
    intro g
    let q := π g
    have mem : g / q.out ∈ r.range := by
      apply (QuotientGroup.eq_one_iff _).mp
      change π (g / q.out) = 1
      rw [map_div, hout]
      exact div_self' _
    obtain ⟨s, hs⟩ := mem
    exact ⟨(q, s), by simp [φ, hs]⟩
  let e := Equiv.ofBijective φ ⟨hinj, hsur⟩
  calc
    (∏ g : G, k g) = ∏ p : (G ⧸ H) × L, k (e p) := (e.prod_comp k).symm
    _ = _ := Fintype.prod_prod_type _
end TunnellReciprocity
namespace TunnellReciprocity
open NumberField IsDedekindDomain
open scoped Classical NumberField IsMulCommutative WithZero WithZeroTopology ValuativeRel

/-- Group the global conjugates by cosets of the local Galois group to realize
a global norm as a norm from any compatible completion. -/
theorem degree_and_norm {D N : Type} [Field D] [NumberField D] [Field N] [NumberField N]
    [Algebra D N] [FiniteDimensional D N] [IsAbelianGalois D N]
    (v : HeightOneSpectrum (𝓞 D)) (t : HeightOneSpectrum (𝓞 N))
    (f : v.adicCompletion D →+* t.adicCompletion N) (hf : Continuous f)
    (hc : ∀ c : D, f (algebraMap D _ c) = algebraMap N _ (algebraMap D N c)) :
    letI : Algebra (v.adicCompletion D) (t.adicCompletion N) := f.toAlgebra
    Module.finrank (v.adicCompletion D) (t.adicCompletion N) ∣ Module.finrank D N ∧
    ∀ a : Nˣ, ∃ b : (t.adicCompletion N)ˣ, Algebra.norm (v.adicCompletion D) (b : t.adicCompletion N) =
      algebraMap D (v.adicCompletion D) (Algebra.norm D (a : N)) := by
  classical
  let V := v.adicCompletion D
  let W := t.adicCompletion N
  letI : NontriviallyNormedField V := Valued.toNontriviallyNormedField V ℤᵐ⁰
  letI : Algebra V W := f.toAlgebra
  letI : Algebra D W := ((algebraMap N W).comp (algebraMap D N)).toAlgebra
  letI : IsScalarTower D V W := IsScalarTower.of_algebraMap_eq fun c => (hc c).symm
  letI : IsScalarTower D N W := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : ContinuousSMul V W := continuousSMul_of_algebraMap V W hf
  obtain ⟨hfin, hgal⟩ := TunnellDenseCompletions.fields v t f hf hc
  letI : FiniteDimensional V W := hfin
  letI : IsGalois V W := hgal
  let r : Gal(W/V) →* Gal(N/D) :=
    (AlgEquiv.restrictNormalHom (F := D) (K₁ := W) N).comp (AlgEquiv.restrictScalarsHom D)
  have hres (s : Gal(W/V)) (b : N) : algebraMap N W (r s b) = s (algebraMap N W b) :=
    (s.restrictScalars D).restrictNormal_commutes N b
  have hr : Function.Injective r := by
    intro s z hz
    apply DFunLike.ext'
    apply (t.denseRange_algebraMap N).equalizer
      s.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional
      z.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional
    funext b
    exact (hres s b).symm.trans ((congrArg (fun j : Gal(N/D) => algebraMap N W (j b)) hz).trans (hres z b))
  refine ⟨?_, ?_⟩
  · simpa only [IsGalois.card_aut_eq_finrank] using Subgroup.card_dvd_of_injective r hr
  intro a
  let Q := Gal(N/D) ⧸ r.range
  let j := algebraMap N W
  let b : W := ∏ q : Q, j (q.out (a : N))
  have hb : b ≠ 0 := Finset.prod_ne_zero_iff.mpr fun q _ => by simp [j, a.ne_zero]
  refine ⟨Units.mk0 b hb, ?_⟩
  change Algebra.norm V b = algebraMap D V (Algebra.norm D (a : N))
  apply (algebraMap V W).injective
  calc
    algebraMap V W (Algebra.norm V b)
        = ∏ s : Gal(W/V), s b := Algebra.norm_eq_prod_automorphisms V b
    _ = ∏ q : Q, ∏ s : Gal(W/V), s (j (q.out (a : N))) := by
      simp only [b, map_prod]; exact Finset.prod_comm
    _ = ∏ q : Q, ∏ s : Gal(W/V), j ((r s * q.out) (a : N)) := by
      apply Finset.prod_congr rfl
      intro q _
      apply Finset.prod_congr rfl
      intro s _
      exact (hres s (q.out (a : N))).symm
    _ = ∏ g : Gal(N/D), j (g (a : N)) :=
      (prod_over_restriction r hr (fun g => j (g (a : N)))).symm
    _ = j (algebraMap D N (Algebra.norm D (a : N))) := by
      rw [Algebra.norm_eq_prod_automorphisms, map_prod]
    _ = algebraMap V W (algebraMap D V (Algebra.norm D (a : N))) := (hc _).symm

end TunnellReciprocity

namespace TunnellReciprocity
open Filter
open scoped Topology

lemma powers_near_one (V : Type*) [NontriviallyNormedField V] [CompleteSpace V] [CharZero V]
    {n : ℕ} (hn : n ≠ 0) :
    ∀ᶠ x : V in 𝓝 1, ∃ a : V, a ^ n = x := by
  have hd : HasStrictDerivAt (fun x : V => x ^ n) (n : V) 1 := by
    simpa using hasStrictDerivAt_pow n (1 : V)
  have hinv := hd.eventually_right_inverse (Nat.cast_ne_zero.mpr hn)
  simp only [one_pow] at hinv
  filter_upwards [hinv] with x hx using ⟨_, hx⟩

lemma normUnits_isClopen (V W : Type*) [NontriviallyNormedField V] [CompleteSpace V] [CharZero V]
    [Field W] [Algebra V W] [FiniteDimensional V W] :
    IsClopen ((Units.map (Algebra.norm V (S := W))).range : Set Vˣ) := by
  let H := (Units.map (Algebra.norm V (S := W))).range
  have near := powers_near_one V (Module.finrank_pos (R := V) (M := W)).ne'
  have cont : Tendsto ((↑) : Vˣ → V) (𝓝 1) (𝓝 1) := Units.continuous_val.continuousAt
  have hOpen : IsOpen (H : Set Vˣ) := by
    apply H.isOpen_of_mem_nhds (g := 1)
    filter_upwards [cont.eventually near] with x hx
    obtain ⟨a, ha⟩ := hx
    have hne : a ≠ 0 := by
      intro h
      rw [h, zero_pow (Module.finrank_pos (R := V) (M := W)).ne'] at ha
      exact x.ne_zero ha.symm
    refine ⟨Units.map (algebraMap V W).toMonoidHom (Units.mk0 a hne), Units.ext ?_⟩
    exact (Algebra.norm_algebraMap (R := V) (S := W) a).trans ha
  exact ⟨H.isClosed_of_isOpen hOpen, hOpen⟩

end TunnellReciprocity

namespace TunnellReciprocity
open NumberField IsDedekindDomain
open scoped NumberField

theorem unit_norm_of_coprime_order {V W : Type*} [Field V] [Field W] [Algebra V W]
    (x : Vˣ) (h : (Module.finrank V W).Coprime (orderOf x)) :
    ∃ y : Wˣ, Algebra.norm V (y : W) = x.val := by
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime h
  refine ⟨Units.map (algebraMap V W).toMonoidHom (x ^ m), ?_⟩
  change Algebra.norm V (algebraMap V W ((x ^ m : Vˣ) : V)) = (x : V)
  rw [Algebra.norm_algebraMap]
  simpa only [Units.val_pow_eq_pow_val, ← pow_mul, Nat.mul_comm m] using congrArg Units.val hm

theorem existsAbove {D N : Type} [Field D] [NumberField D] [Field N] [NumberField N]
    [Algebra D N] (v : HeightOneSpectrum (𝓞 D)) :
    ∃ t : HeightOneSpectrum (𝓞 N), t.asIdeal.LiesOver v.asIdeal := by
  let q := Classical.choice (inferInstance : Nonempty (Ideal.primesOver v.asIdeal (𝓞 N)))
  exact ⟨⟨q.val, q.property.1, Ideal.ne_bot_of_mem_primesOver v.ne_bot q.property⟩, q.property.2⟩

end TunnellReciprocity

namespace OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R2
open NumberField IsDedekindDomain TunnellReciprocity
open scoped NumberField WithZero WithZeroTopology ValuativeRel

/-- When the global degree shares a prime with the number of roots of unity,
one generator of the torsion subgroup must be approximable by global norms. -/
def H1 : Prop :=
  ∀ (D N : Type) [Field D] [NumberField D] [Field N] [NumberField N] [Algebra D N]
    [FiniteDimensional D N] [IsAbelianGalois D N] (v : HeightOneSpectrum (𝓞 D)),
    (∀ i : InfinitePlace D, i.IsComplex) →
    (∀ s : HeightOneSpectrum (𝓞 D), s ≠ v → ∀ t : HeightOneSpectrum (𝓞 N),
      t.asIdeal.LiesOver s.asIdeal → t.asIdeal.ramificationIdx (𝓞 D) = 1) →
    let V := v.adicCompletion D
    let loc := Units.map ((algebraMap D V).comp (algebraMap (𝓞 D) D)).toMonoidHom
    let norms := (Units.map (algebraMap D V).toMonoidHom).comp (Units.map (Algebra.norm D (S := N)))
    ¬ (Module.finrank D N).Coprime (NumberField.Units.torsionOrder D) →
    ∃ g : NumberField.Units.torsion D, (∀ z, z ∈ Subgroup.zpowers g) ∧
      loc g.val ∈ closure (Set.range norms)

/-- Approximate each unit in a fundamental system by global norms at the same place. -/
def H2 : Prop :=
  ∀ (D N : Type) [Field D] [NumberField D] [Field N] [NumberField N] [Algebra D N]
    [FiniteDimensional D N] [IsAbelianGalois D N] (v : HeightOneSpectrum (𝓞 D)),
    (∀ i : InfinitePlace D, i.IsComplex) →
    (∀ s : HeightOneSpectrum (𝓞 D), s ≠ v → ∀ t : HeightOneSpectrum (𝓞 N),
      t.asIdeal.LiesOver s.asIdeal → t.asIdeal.ramificationIdx (𝓞 D) = 1) →
    let V := v.adicCompletion D
    let loc := Units.map ((algebraMap D V).comp (algebraMap (𝓞 D) D)).toMonoidHom
    let norms := (Units.map (algebraMap D V).toMonoidHom).comp (Units.map (Algebra.norm D (S := N)))
    ∀ i : Fin (NumberField.Units.rank D),
      loc (NumberField.Units.fundSystem D i) ∈ closure (Set.range norms)

theorem main : H1 → H2 → OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1.H2 := by
  classical
  intro tors free D N _ _ _ _ _ _ _ v complex unram u
  obtain ⟨t, ht⟩ := existsAbove (N := N) v
  letI := ht
  obtain ⟨f, ⟨hf, hc⟩, _⟩ := existsUnique_completionMap v t
  refine ⟨t, ht, f, hf, hc, ?_⟩
  let V := v.adicCompletion D
  let W := t.adicCompletion N
  letI : NontriviallyNormedField V := Valued.toNontriviallyNormedField V ℤᵐ⁰
  letI : CharZero V := charZero_of_injective_algebraMap (algebraMap D V).injective
  letI : Algebra V W := f.toAlgebra
  letI : FiniteDimensional V W := (TunnellDenseCompletions.fields v t f hf hc).1
  obtain ⟨dvd, glob⟩ := degree_and_norm v t f hf hc
  let loc := Units.map ((algebraMap D V).comp (algebraMap (𝓞 D) D)).toMonoidHom
  let norms := (Units.map (algebraMap D V).toMonoidHom).comp (Units.map (Algebra.norm D (S := N)))
  let H := (Units.map (Algebra.norm V (S := W))).range
  let U := H.comap loc
  have approx : closure (Set.range norms) ⊆ (H : Set Vˣ) := by
    apply closure_minimal _ (normUnits_isClopen V W).1
    rintro z ⟨a, rfl⟩
    obtain ⟨b, hb⟩ := glob a
    exact ⟨b, Units.ext hb⟩
  have hfree : Subgroup.closure (Set.range (NumberField.Units.fundSystem D)) ≤ U := by
    apply U.closure_le.mpr
    rintro x ⟨i, rfl⟩
    exact approx (free D N v complex unram i)
  have htors : NumberField.Units.torsion D ≤ U := by
    by_cases co : (Module.finrank D N).Coprime (NumberField.Units.torsionOrder D)
    · intro x hx
      let z : NumberField.Units.torsion D := ⟨x, hx⟩
      have ord : orderOf x ∣ NumberField.Units.torsionOrder D := by
        have ho : orderOf x = orderOf z :=
          orderOf_injective (NumberField.Units.torsion D).subtype Subtype.val_injective z
        rw [ho]; exact orderOf_dvd_natCard z
      obtain ⟨b, hb⟩ := unit_norm_of_coprime_order (W := W) (loc x)
        (Nat.Coprime.of_dvd dvd ((orderOf_map_dvd loc x).trans ord) co)
      exact ⟨b, Units.ext hb⟩
    · obtain ⟨g, gen, close⟩ := tors D N v complex unram co
      have hg : g.val ∈ U := approx close
      intro x hx
      obtain ⟨m, hm⟩ := gen ⟨x, hx⟩
      have he : g.val ^ m = x := congrArg Subtype.val hm
      rw [← he]
      exact U.zpow_mem hg m
  have hall : (⊤ : Subgroup (𝓞 D)ˣ) ≤ U := by
    rw [← NumberField.Units.closure_fundSystem_sup_torsion_eq_top D]
    exact sup_le hfree htors
  obtain ⟨y, hy⟩ := hall (Subgroup.mem_top u)
  exact ⟨y, congrArg Units.val hy⟩

end OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R2
