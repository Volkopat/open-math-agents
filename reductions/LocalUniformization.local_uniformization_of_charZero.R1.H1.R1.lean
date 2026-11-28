import OMAReductions.R_LocalUniformization_local_uniformization_of_charZero_R1
import Mathlib

/-!
# Rank-1 Characteristic-Zero Local Uniformization: Zero-Dimensional Center Reduction

We reduce `OMA.R_LocalUniformization_local_uniformization_of_charZero_R1.H1` (Zariski 1940,
rank-1 characteristic-zero local uniformization with `trdeg k (ResidueField O) + 1 < trdeg k F`)
to two decoupled `Type 0` theorems on rank-1 valuations with **zero-dimensional center**
(`Algebra.IsAlgebraic k (IsLocalRing.ResidueField O)` and `2 <= Algebra.trdeg k F`):

1. `H1`: Discrete rank-1 characteristic-zero local uniformization with zero-dimensional center
   (`IsDiscreteValuationRing O`, formal-branch / power-series uniformization, Zariski 1940).
2. `H2`: Non-discrete rank-1 characteristic-zero local uniformization with zero-dimensional center
   (`not IsDiscreteValuationRing O`, dense value group / Perron algorithm, Zariski 1940).

In `main`, we prove completely from scratch in Lean 4:
- Non-triviality `O != top` from `trdeg k (ResidueField O) + 1 < trdeg k F < aleph0`.
- Lifting a finite transcendence basis `s` of `ResidueField O` over `k` to elements of `O`,
  proving that every nonzero polynomial in the lifted elements over `k` is a unit of `O`,
  and constructing the intermediate field `k' = k(S) <= O`.
- Verification that `CharZero k'`, `Algebra.EssFiniteType k' F`,
  `Algebra.IsAlgebraic k' (IsLocalRing.ResidueField O)` (zero-dimensional center), and
  `2 <= Algebra.trdeg k' F` via transcendence degree additivity.
- Descent of local uniformization `O.HasLocalUniformization k' -> O.HasLocalUniformization k`:
  given a finite-type `k'`-model `A' <= O` regular at `O.centerOn A'`, we construct a finite-type
  `k`-model `A = k[S, G] <= O` with `IsFractionRing A F` and prove a ring isomorphism
  `Localization.AtPrime (O.centerOn A) ~= Localization.AtPrime (O.centerOn A')`, transporting
  `IsRegularLocalRing` via `IsRegularLocalRing.of_ringEquiv`.
-/

namespace OMA.R_LocalUniformization_local_uniformization_of_charZero_R1_H1_R1

open IsLocalRing ValuationSubring

/-- Discrete rank-1 characteristic-zero local uniformization with zero-dimensional center
(Zariski 1940): every discrete valuation subring `𝒪` of a finitely generated characteristic-zero
field extension `F / k` with algebraic residue field and `2 <= trdeg k F` has local
uniformization over `k`. -/
def H1 : Prop :=
  ∀ (k F : Type) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] [CharZero k]
    (𝒪 : ValuationSubring F) [Algebra k 𝒪] [IsScalarTower k 𝒪 F],
    IsDiscreteValuationRing 𝒪 →
    Algebra.IsAlgebraic k (IsLocalRing.ResidueField 𝒪) →
    (2 : Cardinal) ≤ Algebra.trdeg k F →
    𝒪.HasLocalUniformization k

/-- Non-discrete rank-1 characteristic-zero local uniformization with zero-dimensional center
(Zariski 1940, Perron algorithm): every non-discrete rank-1 valuation subring `𝒪` of a finitely
generated characteristic-zero field extension `F / k` with algebraic residue field and
`2 <= trdeg k F` has local uniformization over `k`. -/
def H2 : Prop :=
  ∀ (k F : Type) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F] [CharZero k]
    (𝒪 : ValuationSubring F) [Algebra k 𝒪] [IsScalarTower k 𝒪 F],
    ¬ IsDiscreteValuationRing 𝒪 →
    𝒪 ≠ ⊤ →
    (∀ 𝒪' : ValuationSubring F, 𝒪 < 𝒪' → 𝒪' = ⊤) →
    Algebra.IsAlgebraic k (IsLocalRing.ResidueField 𝒪) →
    (2 : Cardinal) ≤ Algebra.trdeg k F →
    𝒪.HasLocalUniformization k

section Helpers

private lemma valuationSubring_ne_top_of_trdeg_lt
    (k F : Type) [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F]
    (𝒪 : ValuationSubring F) [Algebra k 𝒪] [IsScalarTower k 𝒪 F]
    (htrdeg : Algebra.trdeg k (IsLocalRing.ResidueField 𝒪) + 1 < Algebra.trdeg k F) :
    𝒪 ≠ ⊤ := by
  intro htop
  have hmem : ∀ x : F, x ∈ 𝒪 := fun x => htop ▸ ValuationSubring.mem_top x
  let f : F →ₐ[k] 𝒪 :=
    { toFun := fun x => ⟨x, hmem x⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      commutes' := fun c => Subtype.ext (IsScalarTower.algebraMap_apply k 𝒪 F c) }
  let ρ : F →ₐ[k] IsLocalRing.ResidueField 𝒪 :=
    (IsScalarTower.toAlgHom k 𝒪 (IsLocalRing.ResidueField 𝒪)).comp f
  have hρ_bij : Function.Bijective ρ := by
    refine ⟨RingHom.injective ρ.toRingHom, fun y => ?_⟩
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
    exact ⟨(x : F), rfl⟩
  let e : F ≃ₐ[k] IsLocalRing.ResidueField 𝒪 := AlgEquiv.ofBijective ρ hρ_bij
  have heq : Algebra.trdeg k F = Algebra.trdeg k (IsLocalRing.ResidueField 𝒪) :=
    e.trdeg_eq
  have hlt_al : Algebra.trdeg k F < Cardinal.aleph0 := trdeg_lt_aleph0 k F
  obtain ⟨n, hn⟩ := Cardinal.lt_aleph0.mp hlt_al
  rw [← heq, hn] at htrdeg
  have hnat : n + 1 < n := by exact_mod_cast htrdeg
  omega

private lemma mem_intermediateField_adjoin_div
    {k F : Type*} [Field k] [Field F] [Algebra k F] (S : Set F)
    {x : F} (hx : x ∈ IntermediateField.adjoin k S) :
    ∃ a b : Algebra.adjoin k S, (b : F) ≠ 0 ∧ x = (a : F) / (b : F) := by
  let R₀ : Subalgebra k F := Algebra.adjoin k S
  let K₀ : Subfield F :=
    { carrier := {z : F | ∃ a b : R₀, (b : F) ≠ 0 ∧ z = (a : F) / (b : F)}
      zero_mem' := ⟨0, 1, one_ne_zero, by simp⟩
      one_mem' := ⟨1, 1, one_ne_zero, by simp⟩
      add_mem' := by
        rintro _ _ ⟨a₁, b₁, hb₁, rfl⟩ ⟨a₂, b₂, hb₂, rfl⟩
        refine ⟨a₁ * b₂ + a₂ * b₁, b₁ * b₂, mul_ne_zero hb₁ hb₂, ?_⟩
        push_cast
        field_simp
      neg_mem' := by
        rintro _ ⟨a, b, hb, rfl⟩
        refine ⟨-a, b, hb, ?_⟩
        push_cast
        ring
      mul_mem' := by
        rintro _ _ ⟨a₁, b₁, hb₁, rfl⟩ ⟨a₂, b₂, hb₂, rfl⟩
        refine ⟨a₁ * a₂, b₁ * b₂, mul_ne_zero hb₁ hb₂, ?_⟩
        push_cast
        ring
      inv_mem' := by
        rintro _ ⟨a, b, hb, rfl⟩
        by_cases ha : (a : F) = 0
        · refine ⟨0, 1, one_ne_zero, ?_⟩
          simp [ha]
        · refine ⟨b, a, ha, ?_⟩
          field_simp }
  let K' : IntermediateField k F :=
    K₀.toIntermediateField fun c => ⟨algebraMap k R₀ c, 1, one_ne_zero, by simp⟩
  have hle : IntermediateField.adjoin k S ≤ K' :=
    IntermediateField.adjoin_le_iff.mpr fun z hz =>
      ⟨⟨z, Algebra.subset_adjoin hz⟩, 1, one_ne_zero, by simp⟩
  exact hle hx

private lemma adjoin_lift_units_in_valuationSubring
    (k F : Type) [Field k] [Field F] [Algebra k F]
    (𝒪 : ValuationSubring F) [Algebra k 𝒪] [IsScalarTower k 𝒪 F]
    {ι : Type} (b : ι → IsLocalRing.ResidueField 𝒪)
    (hb : AlgebraicIndependent k b)
    (lift : ι → 𝒪) (hlift : ∀ i, IsLocalRing.residue 𝒪 (lift i) = b i) :
    let liftF : ι → F := fun i => (lift i : F)
    (∀ r : Algebra.adjoin k (Set.range liftF), (r : F) ∈ 𝒪) ∧
    (∀ r : Algebra.adjoin k (Set.range liftF), (r : F) ≠ 0 →
      𝒪.valuation (r : F) = 1 ∧ (r : F)⁻¹ ∈ 𝒪) := by
  intro liftF
  have hsub : ∀ r : Algebra.adjoin k (Set.range liftF), (r : F) ∈ 𝒪 := by
    intro r
    have hr := r.2
    refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hr
    · rintro _ ⟨i, rfl⟩
      exact (lift i).2
    · intro c
      rw [IsScalarTower.algebraMap_apply k 𝒪 F c]
      exact (algebraMap k 𝒪 c).2
    · intro x y _ _ hx hy
      exact 𝒪.toSubring.add_mem hx hy
    · intro x y _ _ hx hy
      exact 𝒪.toSubring.mul_mem hx hy
  refine ⟨hsub, fun r hr0 => ?_⟩
  have hrange : (r : F) ∈ (MvPolynomial.aeval liftF : MvPolynomial ι k →ₐ[k] F).range := by
    rw [← Algebra.adjoin_range_eq_range_aeval]
    exact r.2
  obtain ⟨P, hP⟩ := hrange
  have hPne : P ≠ 0 := by
    intro h0
    apply hr0
    rw [← hP, h0, map_zero]
  let val𝒪 : 𝒪 := MvPolynomial.aeval lift P
  have hval_eq : (val𝒪 : F) = (r : F) := by
    rw [← hP]
    exact AlgHom.congr_fun
      (MvPolynomial.comp_aeval lift (IsScalarTower.toAlgHom k 𝒪 F)) P
  have hres_ne : IsLocalRing.residue 𝒪 val𝒪 ≠ 0 := by
    have hres_eq : IsLocalRing.residue 𝒪 val𝒪 = MvPolynomial.aeval b P := by
      have h1 := AlgHom.congr_fun
        (MvPolynomial.comp_aeval lift
          (IsScalarTower.toAlgHom k 𝒪 (IsLocalRing.ResidueField 𝒪))) P
      have hfun : (fun i => (IsScalarTower.toAlgHom k 𝒪 (IsLocalRing.ResidueField 𝒪)) (lift i)) = b :=
        funext hlift
      rw [hfun] at h1
      exact h1
    rw [hres_eq]
    intro hzero
    exact hPne ((algebraicIndependent_iff.mp hb) P hzero)
  have hnot_max : val𝒪 ∉ IsLocalRing.maximalIdeal 𝒪 := by
    intro hmem
    apply hres_ne
    exact (IsLocalRing.residue_eq_zero_iff val𝒪).mpr hmem
  have hval_le : 𝒪.valuation (r : F) ≤ 1 := by
    rw [← hval_eq]
    exact ValuationSubring.valuation_le_one 𝒪 val𝒪
  have hval_not_lt : ¬ (𝒪.valuation (r : F) < 1) := by
    rw [← hval_eq, ← ValuationSubring.valuation_lt_one_iff]
    exact hnot_max
  have hval_one : 𝒪.valuation (r : F) = 1 := le_antisymm hval_le (not_lt.mp hval_not_lt)
  have hinv : (r : F)⁻¹ ∈ 𝒪 := by
    have hu : IsUnit val𝒪 := (IsLocalRing.notMem_maximalIdeal).mp hnot_max
    obtain ⟨u, hu_eq⟩ := hu
    have hprod : (r : F) * ((u⁻¹ : 𝒪ˣ) : F) = 1 := by
      rw [← hval_eq, ← hu_eq]
      exact_mod_cast congrArg Subtype.val u.mul_inv
    have hinv_eq : (r : F)⁻¹ = ((u⁻¹ : 𝒪ˣ) : F) := by
      apply mul_left_cancel₀ hr0
      rw [mul_inv_cancel₀ hr0, hprod]
    rw [hinv_eq]
    exact (u⁻¹ : 𝒪ˣ).1.2
  exact ⟨hval_one, hinv⟩

private lemma hasLocalUniformization_of_adjoin_units
    (k F : Type) [Field k] [Field F] [Algebra k F]
    (𝒪 : ValuationSubring F) [Algebra k 𝒪] [IsScalarTower k 𝒪 F]
    {ι : Type} [Finite ι] (liftF : ι → F)
    (hR₀_mem : ∀ r : Algebra.adjoin k (Set.range liftF), (r : F) ∈ 𝒪)
    (hR₀_unit : ∀ r : Algebra.adjoin k (Set.range liftF), (r : F) ≠ 0 →
      𝒪.valuation (r : F) = 1 ∧ (r : F)⁻¹ ∈ 𝒪)
    (hU : 𝒪.HasLocalUniformization (IntermediateField.adjoin k (Set.range liftF))) :
    𝒪.HasLocalUniformization k := by
  classical
  let k' : IntermediateField k F := IntermediateField.adjoin k (Set.range liftF)
  let R₀ : Subalgebra k F := Algebra.adjoin k (Set.range liftF)
  obtain ⟨A', hA', hft', hfrac', hreg'⟩ := hU
  obtain ⟨G, hG⟩ := Algebra.FiniteType.out (R := k') (A := A')
  let G_F : Finset F := G.image Subtype.val
  let S_all : Set F := Set.range liftF ∪ (G_F : Set F)
  let A : Subalgebra k F := Algebra.adjoin k S_all
  have hS_fin : S_all.Finite := (Set.finite_range liftF).union G_F.finite_toSet
  have hft : Algebra.FiniteType k A := Algebra.FiniteType.adjoin_of_finite hS_fin
  have hA : ∀ a : A, (a : F) ∈ 𝒪 := by
    intro a
    refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ a.2
    · rintro z (⟨i, rfl⟩ | hz)
      · exact hR₀_mem ⟨liftF i, Algebra.subset_adjoin ⟨i, rfl⟩⟩
      · rcases Finset.mem_image.mp hz with ⟨g, _, rfl⟩
        exact hA' g
    · intro c
      rw [IsScalarTower.algebraMap_apply k 𝒪 F c]
      exact (algebraMap k 𝒪 c).2
    · intro x y _ _ hx hy; exact 𝒪.toSubring.add_mem hx hy
    · intro x y _ _ hx hy; exact 𝒪.toSubring.mul_mem hx hy
  have hR₀_le_A : R₀ ≤ A := Algebra.adjoin_mono Set.subset_union_left
  have hA_le_A' : ∀ a : A, (a : F) ∈ A' := by
    intro a
    refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ a.2
    · rintro z (⟨i, rfl⟩ | hz)
      · exact A'.algebraMap_mem ⟨liftF i, IntermediateField.subset_adjoin k _ ⟨i, rfl⟩⟩
      · rcases Finset.mem_image.mp hz with ⟨g, _, rfl⟩
        exact g.2
    · intro c
      exact A'.algebraMap_mem (algebraMap k k' c)
    · intro x y _ _ hx hy; exact A'.add_mem hx hy
    · intro x y _ _ hx hy; exact A'.mul_mem hx hy
  have hexists_denom : ∀ x : A', ∃ b : R₀, (b : F) ≠ 0 ∧ (b : F) * (x : F) ∈ A := by
    intro x
    have hx : x ∈ Algebra.adjoin k' (G : Set A') := by rw [hG]; trivial
    refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hx
    · intro g hg
      refine ⟨1, one_ne_zero, ?_⟩
      simp only [Subalgebra.coe_one, one_mul]
      exact Algebra.subset_adjoin (Or.inr (Finset.mem_image.mpr ⟨g, hg, rfl⟩))
    · intro c
      obtain ⟨a, b, hb0, hdiv⟩ := mem_intermediateField_adjoin_div (Set.range liftF) c.2
      refine ⟨b, hb0, ?_⟩
      have hmul : (b : F) * (algebraMap k' A' c : F) = (a : F) := by
        change (b : F) * (c : F) = (a : F)
        rw [hdiv, mul_div_cancel₀ _ hb0]
      rw [hmul]
      exact hR₀_le_A a.2
    · rintro x₁ x₂ _ _ ⟨b₁, hb₁, hm₁⟩ ⟨b₂, hb₂, hm₂⟩
      refine ⟨b₁ * b₂, mul_ne_zero hb₁ hb₂, ?_⟩
      have hmul : ((b₁ * b₂ : R₀) : F) * ((x₁ + x₂ : A') : F) =
          (b₂ : F) * ((b₁ : F) * (x₁ : F)) + (b₁ : F) * ((b₂ : F) * (x₂ : F)) := by
        push_cast; ring
      rw [hmul]
      exact A.add_mem (A.mul_mem (hR₀_le_A b₂.2) hm₁) (A.mul_mem (hR₀_le_A b₁.2) hm₂)
    · rintro x₁ x₂ _ _ ⟨b₁, hb₁, hm₁⟩ ⟨b₂, hb₂, hm₂⟩
      refine ⟨b₁ * b₂, mul_ne_zero hb₁ hb₂, ?_⟩
      have hmul : ((b₁ * b₂ : R₀) : F) * ((x₁ * x₂ : A') : F) =
          ((b₁ : F) * (x₁ : F)) * ((b₂ : F) * (x₂ : F)) := by
        push_cast; ring
      rw [hmul]
      exact A.mul_mem hm₁ hm₂
  have hfrac : IsFractionRing A F := by
    refine (isLocalization_iff (nonZeroDivisors A) F).mpr ⟨?_, ?_, ?_⟩
    · intro a
      have ha : (a : A) ≠ 0 := nonZeroDivisors.ne_zero a.2
      exact isUnit_iff_ne_zero.mpr fun h => ha (Subtype.ext h)
    · intro z
      obtain ⟨⟨x, y⟩, hy⟩ := IsLocalization.surj (nonZeroDivisors A') z
      have hy0 : (y : F) ≠ 0 := by
        have hyn : (y : A') ≠ 0 := nonZeroDivisors.ne_zero y.2
        exact_mod_cast hyn
      obtain ⟨b₁, hb₁, hm₁⟩ := hexists_denom x
      obtain ⟨b₂, hb₂, hm₂⟩ := hexists_denom (y : A')
      let numA : A := ⟨(b₂ : F) * ((b₁ : F) * (x : F)), A.mul_mem (hR₀_le_A b₂.2) hm₁⟩
      let denA : A := ⟨(b₁ : F) * ((b₂ : F) * (y : F)), A.mul_mem (hR₀_le_A b₁.2) hm₂⟩
      have hden0 : denA ≠ 0 := by
        intro h0
        have hF : (denA : F) = 0 := congrArg Subtype.val h0
        exact mul_ne_zero hb₁ (mul_ne_zero hb₂ hy0) hF
      refine ⟨⟨numA, ⟨denA, mem_nonZeroDivisors_of_ne_zero hden0⟩⟩, ?_⟩
      have hzy : z * (y : F) = (x : F) := hy
      change z * ((b₁ : F) * ((b₂ : F) * (y : F))) = (b₂ : F) * ((b₁ : F) * (x : F))
      linear_combination (b₁ : F) * (b₂ : F) * hzy
    · intro a₁ a₂ h
      exact ⟨1, by simpa using Subtype.ext h⟩
  let ι : A →+* A' :=
    { toFun := fun a => ⟨(a : F), hA_le_A' a⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hι_inj : Function.Injective ι :=
    fun a₁ a₂ h => Subtype.ext (congrArg (Subtype.val : A' → F) h)
  have hM_le : (𝒪.centerOn A hA).primeCompl ≤
      Submonoid.comap ι (𝒪.centerOn A' hA').primeCompl := by
    intro a ha
    change ι a ∉ 𝒪.centerOn A' hA'
    rw [ValuationSubring.mem_centerOn_iff]
    change ¬ (𝒪.valuation (a : F) < 1)
    rwa [← ValuationSubring.mem_centerOn_iff 𝒪 A hA a]
  let L := Localization.AtPrime (𝒪.centerOn A hA)
  let L' := Localization.AtPrime (𝒪.centerOn A' hA')
  let Φ : L →+* L' := IsLocalization.map L' ι hM_le
  have hΦ_inj : Function.Injective Φ := by
    intro z₁ z₂ hΦeq
    obtain ⟨⟨a₁, s₁⟩, rfl⟩ := IsLocalization.mk'_surjective (𝒪.centerOn A hA).primeCompl z₁
    obtain ⟨⟨a₂, s₂⟩, rfl⟩ := IsLocalization.mk'_surjective (𝒪.centerOn A hA).primeCompl z₂
    simp only [Φ, IsLocalization.map_mk'] at hΦeq
    obtain ⟨c, hc⟩ := IsLocalization.eq.mp hΦeq
    have hc0 : (c : A') ≠ 0 := fun h0 => c.2 (h0.symm ▸ (𝒪.centerOn A' hA').zero_mem)
    have heq' : ι (s₂ : A) * ι a₁ = ι (s₁ : A) * ι a₂ := mul_left_cancel₀ hc0 hc
    have heqA : (s₂ : A) * a₁ = (s₁ : A) * a₂ := hι_inj (by simpa [map_mul] using heq')
    exact IsLocalization.eq.mpr ⟨1, by rw [OneMemClass.coe_one, one_mul, one_mul, heqA]⟩
  have hΦ_surj : Function.Surjective Φ := by
    intro w
    obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalization.mk'_surjective (𝒪.centerOn A' hA').primeCompl w
    obtain ⟨b₁, hb₁, hm₁⟩ := hexists_denom x
    obtain ⟨b₂, hb₂, hm₂⟩ := hexists_denom (s : A')
    let u : A := ⟨(b₂ : F) * ((b₁ : F) * (x : F)), A.mul_mem (hR₀_le_A b₂.2) hm₁⟩
    let t : A := ⟨(b₁ : F) * ((b₂ : F) * (s : F)), A.mul_mem (hR₀_le_A b₁.2) hm₂⟩
    have hs_val : 𝒪.valuation ((s : A') : F) = 1 := by
      have hnotlt : ¬ (𝒪.valuation ((s : A') : F) < 1) := by
        rw [← ValuationSubring.mem_centerOn_iff 𝒪 A' hA' (s : A')]
        exact s.2
      exact le_antisymm (ValuationSubring.valuation_le_one 𝒪 ⟨(s : F), hA' (s : A')⟩)
        (not_lt.mp hnotlt)
    have ht_mem : t ∈ (𝒪.centerOn A hA).primeCompl := by
      change t ∉ 𝒪.centerOn A hA
      rw [ValuationSubring.mem_centerOn_iff]
      have hvt : 𝒪.valuation (t : F) = 1 := by
        change 𝒪.valuation ((b₁ : F) * ((b₂ : F) * ((s : A') : F))) = 1
        rw [map_mul, map_mul, (hR₀_unit b₁ hb₁).1, (hR₀_unit b₂ hb₂).1, hs_val, mul_one, mul_one]
      rw [hvt]
      exact lt_irrefl 1
    refine ⟨IsLocalization.mk' L u ⟨t, ht_mem⟩, ?_⟩
    simp only [Φ, IsLocalization.map_mk']
    refine IsLocalization.eq.mpr ⟨1, ?_⟩
    simp only [OneMemClass.coe_one, one_mul]
    apply Subtype.ext
    change ((s : A') : F) * ((b₂ : F) * ((b₁ : F) * (x : F))) =
      ((b₁ : F) * ((b₂ : F) * ((s : A') : F))) * (x : F)
    ring
  let eqv := Equiv.ofBijective Φ ⟨hΦ_inj, hΦ_surj⟩
  have hreg : IsRegularLocalRing (Localization.AtPrime (𝒪.centerOn A hA)) :=
    @IsRegularLocalRing.of_ringEquiv
      (Localization.AtPrime (𝒪.centerOn A' hA')) _ hreg'
      (Localization.AtPrime (𝒪.centerOn A hA)) _
      { toEquiv := eqv.symm
        map_mul' := fun x y => eqv.injective (by
          change Φ (eqv.symm (x * y)) = Φ (eqv.symm x * eqv.symm y)
          rw [Φ.map_mul]
          change eqv (eqv.symm (x * y)) = eqv (eqv.symm x) * eqv (eqv.symm y)
          rw [eqv.apply_symm_apply, eqv.apply_symm_apply, eqv.apply_symm_apply])
        map_add' := fun x y => eqv.injective (by
          change Φ (eqv.symm (x + y)) = Φ (eqv.symm x + eqv.symm y)
          rw [Φ.map_add]
          change eqv (eqv.symm (x + y)) = eqv (eqv.symm x) + eqv (eqv.symm y)
          rw [eqv.apply_symm_apply, eqv.apply_symm_apply, eqv.apply_symm_apply]) }
  exact ⟨A, hA, hft, hfrac, hreg⟩

end Helpers

theorem main : H1 → H2 →
    OMA.R_LocalUniformization_local_uniformization_of_charZero_R1.H1 := by
  intro h1 h2 k F _ _ _ _ _ 𝒪 _ _ htrdeg hrank1
  have h𝒪_ne_top : 𝒪 ≠ ⊤ := valuationSubring_ne_top_of_trdeg_lt k F 𝒪 htrdeg
  have htrdegF_fin : Algebra.trdeg k F < Cardinal.aleph0 := trdeg_lt_aleph0 k F
  have htrdegRes_fin : Algebra.trdeg k (IsLocalRing.ResidueField 𝒪) < Cardinal.aleph0 := by
    have hle : Algebra.trdeg k (IsLocalRing.ResidueField 𝒪) ≤
        Algebra.trdeg k (IsLocalRing.ResidueField 𝒪) + 1 := self_le_add_right _ _
    exact (hle.trans_lt htrdeg).trans htrdegF_fin
  have : FinTrdeg k (IsLocalRing.ResidueField 𝒪) := FinTrdeg.of_trdeg htrdegRes_fin
  obtain ⟨s, hs⟩ := exists_finset_isTranscendenceBasis k (IsLocalRing.ResidueField 𝒪)
  let lift : s → 𝒪 := fun x => (IsLocalRing.residue_surjective x.1).choose
  have hlift : ∀ x : s, IsLocalRing.residue 𝒪 (lift x) = x.1 :=
    fun x => (IsLocalRing.residue_surjective x.1).choose_spec
  let liftF : s → F := fun x => (lift x : F)
  obtain ⟨hR₀_mem, hR₀_unit⟩ :=
    adjoin_lift_units_in_valuationSubring k F 𝒪 ((↑) : s → IsLocalRing.ResidueField 𝒪) hs.1 lift hlift
  let k' : IntermediateField k F := IntermediateField.adjoin k (Set.range liftF)
  have hk'_mem : ∀ x : k', (x : F) ∈ 𝒪 := by
    intro x
    obtain ⟨a, b, hb0, hdiv⟩ := mem_intermediateField_adjoin_div (Set.range liftF) x.2
    rw [hdiv, div_eq_mul_inv]
    exact 𝒪.toSubring.mul_mem (hR₀_mem a) (hR₀_unit b hb0).2
  let k'_to_𝒪 : k' →+* 𝒪 := k'.val.toRingHom.codRestrict 𝒪.toSubring hk'_mem
  let : Algebra k' 𝒪 := k'_to_𝒪.toAlgebra
  have : IsScalarTower k' 𝒪 F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : IsScalarTower k k' 𝒪 := IsScalarTower.of_algebraMap_eq fun c =>
    Subtype.ext (IsScalarTower.algebraMap_apply k 𝒪 F c).symm
  have : CharZero k' :=
    ⟨fun m n hmn => Nat.cast_injective (R := k) (RingHom.injective (algebraMap k k') (by simpa using hmn))⟩
  have : Algebra.EssFiniteType k' F := Algebra.EssFiniteType.of_comp (R := k) (S := k') (T := F)
  let ρ : k' →ₐ[k] IsLocalRing.ResidueField 𝒪 :=
    IsScalarTower.toAlgHom k k' (IsLocalRing.ResidueField 𝒪)
  have hρ_lift : ∀ x : s, ρ ⟨liftF x, IntermediateField.subset_adjoin k _ ⟨x, rfl⟩⟩ = x.1 := by
    intro x
    change IsLocalRing.residue 𝒪 (lift x) = x.1
    exact hlift x
  have htrdeg_k' : Algebra.trdeg k k' = Algebra.trdeg k (IsLocalRing.ResidueField 𝒪) := by
    let g : s → k' := fun x => ⟨liftF x, IntermediateField.subset_adjoin k _ ⟨x, rfl⟩⟩
    have hg_indep : AlgebraicIndependent k g := by
      have hcomp : (ρ ∘ g) = ((↑) : s → IsLocalRing.ResidueField 𝒪) := by
        funext x; exact hρ_lift x
      exact AlgebraicIndependent.of_comp ρ (hcomp ▸ hs.1)
    have hR₀_in_adjoin : ∀ r : Algebra.adjoin k (Set.range liftF),
        ∃ r' : Algebra.adjoin k (Set.range g), ((r' : k') : F) = (r : F) := by
      intro r
      refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ r.2
      · rintro _ ⟨i, rfl⟩
        exact ⟨⟨g i, Algebra.subset_adjoin ⟨i, rfl⟩⟩, rfl⟩
      · intro c
        exact ⟨algebraMap k _ c, rfl⟩
      · rintro _ _ _ _ ⟨r₁, h₁⟩ ⟨r₂, h₂⟩
        exact ⟨r₁ + r₂, by push_cast; rw [h₁, h₂]⟩
      · rintro _ _ _ _ ⟨r₁, h₁⟩ ⟨r₂, h₂⟩
        exact ⟨r₁ * r₂, by push_cast; rw [h₁, h₂]⟩
    have hg_alg : Algebra.IsAlgebraic (Algebra.adjoin k (Set.range g)) k' := by
      refine ⟨fun x => ?_⟩
      obtain ⟨a, b, hb0, hdiv⟩ := mem_intermediateField_adjoin_div (Set.range liftF) x.2
      obtain ⟨a', ha'⟩ := hR₀_in_adjoin a
      obtain ⟨b', hb'⟩ := hR₀_in_adjoin b
      have hb'0 : b' ≠ 0 := by
        intro h0
        apply hb0
        rw [← hb', h0]
        rfl
      refine ⟨Polynomial.C b' * Polynomial.X - Polynomial.C a', ?_, ?_⟩
      · intro h0
        have hcoeff := congrArg (fun p => Polynomial.coeff p 1) h0
        simp [Polynomial.coeff_C] at hcoeff
        exact hb'0 hcoeff
      · simp only [map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X]
        apply sub_eq_zero.mpr
        apply Subtype.ext
        change ((b' : k') : F) * (x : F) = ((a' : k') : F)
        rw [hb', ha', hdiv, mul_div_cancel₀ _ hb0]
    have hg_basis : IsTranscendenceBasis k g :=
      hg_indep.isTranscendenceBasis_iff_isAlgebraic.mpr hg_alg
    rw [← hg_basis.cardinalMk_eq_trdeg, ← hs.cardinalMk_eq_trdeg]
  have htrdeg_ge2 : (2 : Cardinal) ≤ Algebra.trdeg k' F := by
    have hadd : Algebra.trdeg k k' + Algebra.trdeg k' F = Algebra.trdeg k F := trdeg_add_eq k k'
    have hfinF : Algebra.trdeg k F < Cardinal.aleph0 := htrdegF_fin
    obtain ⟨d, hd⟩ := Cardinal.lt_aleph0.mp hfinF
    obtain ⟨t, ht⟩ := Cardinal.lt_aleph0.mp (htrdeg_k'.symm ▸ htrdegRes_fin)
    have hfin_k'F : Algebra.trdeg k' F < Cardinal.aleph0 := trdeg_lt_aleph0 k' F
    obtain ⟨e, he⟩ := Cardinal.lt_aleph0.mp hfin_k'F
    rw [ht, he, hd] at hadd
    rw [← htrdeg_k', ht, hd] at htrdeg
    have hadd_nat : t + e = d := by exact_mod_cast hadd
    have hlt_nat : t + 1 < d := by exact_mod_cast htrdeg
    rw [he]
    exact_mod_cast (show 2 ≤ e by omega)
  have halg_res : Algebra.IsAlgebraic k' (IsLocalRing.ResidueField 𝒪) := by
    have hle : IntermediateField.adjoin k (Set.range ((↑) : s → IsLocalRing.ResidueField 𝒪)) ≤
        ρ.fieldRange := by
      rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨x, rfl⟩
      exact ⟨⟨liftF x, IntermediateField.subset_adjoin k _ ⟨x, rfl⟩⟩, hρ_lift x⟩
    let : Algebra (IntermediateField.adjoin k (Set.range ((↑) : s → IsLocalRing.ResidueField 𝒪)))
        ρ.fieldRange := (IntermediateField.inclusion hle).toRingHom.toAlgebra
    have : IsScalarTower
        (IntermediateField.adjoin k (Set.range ((↑) : s → IsLocalRing.ResidueField 𝒪)))
        ρ.fieldRange (IsLocalRing.ResidueField 𝒪) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    have halg_s := hs.isAlgebraic_field
    refine ⟨fun y => ?_⟩
    have hy : IsAlgebraic (IntermediateField.adjoin k (Set.range ((↑) : s → IsLocalRing.ResidueField 𝒪))) y :=
      halg_s.isAlgebraic y
    have hy_range : IsAlgebraic ρ.fieldRange y := hy.tower_top ρ.fieldRange
    obtain ⟨p, hp0, hpeval⟩ := hy_range
    let eρ : k' ≃ₐ[k] ρ.fieldRange := AlgEquiv.ofInjectiveField ρ
    refine ⟨p.map eρ.symm.toRingHom, ?_, ?_⟩
    · intro h0
      apply hp0
      have := congrArg (Polynomial.map eρ.toRingHom) h0
      simpa [Polynomial.map_map] using this
    · rw [Polynomial.aeval_def, Polynomial.eval₂_map]
      have hcomp : (algebraMap k' (IsLocalRing.ResidueField 𝒪)).comp eρ.symm.toRingHom =
          algebraMap ρ.fieldRange (IsLocalRing.ResidueField 𝒪) := by
        ext z
        have hz : ρ (eρ.symm z) = (z : IsLocalRing.ResidueField 𝒪) := by
          have := eρ.apply_symm_apply z
          exact congrArg Subtype.val this
        exact hz
      rw [hcomp]
      exact hpeval
  have hU_k' : 𝒪.HasLocalUniformization k' := by
    by_cases hDVR : IsDiscreteValuationRing 𝒪
    · exact h1 k' F 𝒪 hDVR halg_res htrdeg_ge2
    · exact h2 k' F 𝒪 hDVR h𝒪_ne_top hrank1 halg_res htrdeg_ge2
  exact hasLocalUniformization_of_adjoin_units k F 𝒪 liftF hR₀_mem hR₀_unit hU_k'

end OMA.R_LocalUniformization_local_uniformization_of_charZero_R1_H1_R1
