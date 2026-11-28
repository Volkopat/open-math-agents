import OMAReductions.R_ArtinPrimitiveRootsConjecture_conditional_artin_primitive_roots_parts_i_R1_H1_R1
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.Data.ZMod.QuotientRing

/-!
Proof of `OMA.R_ArtinPrimitiveRootsConjecture_conditional_artin_primitive_roots_parts_i_R1_H1_R1.H1`:
1. Kummer-Dedekind complete-splitting characterization at rational primes `p ∤ a * k` via the
   Galois decomposition group action on the integral roots of `X^k - a`.
2. Discriminant upper bound via the two-step different ideal tower `ℚ ⊆ ℚ(ζ_k) ⊆ K`.
-/

open scoped Pointwise
open Polynomial NumberField

namespace ArtinH1Proof

/-- If `x ∈ B` generates `L / K` and satisfies `x ^ k = c` for `c ∈ A` (`k ≥ 1`), then
`k * c` (mapped into `B`) belongs to `differentIdeal A B`. -/
lemma nat_mul_mem_differentIdeal
    (A K B L : Type*) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [CommRing B] [IsDedekindDomain B] [Algebra A B] [Module.IsTorsionFree A B]
    [Field L] [Algebra K L] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsIntegralClosure B A L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    {x : B} (hx_gen : Algebra.adjoin K ({algebraMap B L x} : Set L) = ⊤)
    {k : ℕ} (hk : 1 ≤ k) {c : A} (hx_pow : x ^ k = algebraMap A B c) :
    algebraMap A B ((k : A) * c) ∈ differentIdeal A B := by
  have hx_int : IsIntegral A x := IsIntegralClosure.isIntegral A L x
  let P : A[X] := X ^ k - C c
  have hP_aeval : aeval x P = 0 := by
    simp [P, hx_pow]
  obtain ⟨Q, hPQ⟩ := minpoly.isIntegrallyClosed_dvd hx_int hP_aeval
  have hderiv : aeval x (derivative P) =
      aeval x (derivative (minpoly A x)) * aeval x Q := by
    rw [hPQ, derivative_mul, map_add, map_mul, map_mul, minpoly.aeval A x, zero_mul, add_zero]
  have hderivP : derivative P = C (k : A) * X ^ (k - 1) := by
    simp [P, derivative_X_pow]
  have hmem_d : aeval x (derivative (minpoly A x)) ∈ differentIdeal A B :=
    aeval_derivative_mem_differentIdeal A K L x hx_gen
  have hkx : algebraMap A B (k : A) * x ^ (k - 1) =
      aeval x (derivative (minpoly A x)) * aeval x Q := by
    simpa [hderivP] using hderiv
  have hk_pow : x ^ (k - 1) * x = x ^ k := by
    rw [← pow_succ, Nat.sub_add_cancel hk]
  have heq : algebraMap A B ((k : A) * c) =
      aeval x (derivative (minpoly A x)) * (aeval x Q * x) := by
    calc
      algebraMap A B ((k : A) * c)
        = algebraMap A B (k : A) * algebraMap A B c := map_mul _ _ _
      _ = algebraMap A B (k : A) * x ^ k := by rw [← hx_pow]
      _ = (algebraMap A B (k : A) * x ^ (k - 1)) * x := by rw [mul_assoc, hk_pow]
      _ = aeval x (derivative (minpoly A x)) * (aeval x Q * x) := by rw [hkx, mul_assoc]
  rw [heq]
  exact Ideal.mul_mem_right _ _ hmem_d

/-- Pairwise distinct elements mapped into a field give a squarefree product of linear factors, so
if a separable polynomial factors as `∏ s ∈ S, (X - C (g s))`, then `g` is injective on `S`. -/
lemma injOn_of_separable_eq_prod {F α : Type*} [Field F] [DecidableEq α]
    {S : Finset α} {g : α → F} {f : F[X]}
    (hsep : f.Separable) (hprod : f = ∏ s ∈ S, (X - C (g s))) :
    Set.InjOn g (S : Set α) := by
  intro x hx y hy hxy
  by_contra hne
  rw [Finset.mem_coe] at hx hy
  have hy_er : y ∈ S.erase x := Finset.mem_erase.mpr ⟨Ne.symm hne, hy⟩
  have hfac1 : ∏ s ∈ S, (X - C (g s)) =
      (X - C (g x)) * ∏ s ∈ S.erase x, (X - C (g s)) :=
    (Finset.mul_prod_erase S (fun s => X - C (g s)) hx).symm
  have hfac2 : ∏ s ∈ S.erase x, (X - C (g s)) =
      (X - C (g y)) * ∏ s ∈ (S.erase x).erase y, (X - C (g s)) :=
    (Finset.mul_prod_erase (S.erase x) (fun s => X - C (g s)) hy_er).symm
  have hdvd : (X - C (g x)) * (X - C (g x)) ∣ f := by
    refine ⟨∏ s ∈ (S.erase x).erase y, (X - C (g s)), ?_⟩
    rw [hprod, hfac1, hfac2, hxy, mul_assoc]
  have hu : IsUnit (X - C (g x)) := hsep.squarefree (X - C (g x)) hdvd
  have hdeg := Polynomial.natDegree_eq_zero_of_isUnit hu
  rw [Polynomial.natDegree_X_sub_C] at hdeg
  exact one_ne_zero hdeg

/-- Part 1 of `H1` for any splitting field `L` of `X^k - C (a : ℚ)` over `ℚ`. -/
theorem splits_zmod_iff_ncard_primesOver_eq_finrank_aux
    (a : ℤ) (ha : a ≠ 0) (k : ℕ) (hk2 : 2 ≤ k)
    (L : Type*) [Field L] [NumberField L]
    [Polynomial.IsSplittingField ℚ L (X ^ k - C (a : ℚ))]
    (p : ℕ) (hp : p.Prime) (hpa : ¬ (p : ℤ) ∣ a) (hpk : ¬ p ∣ k) :
    (X ^ k - C (a : ZMod p)).Splits ↔
      (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 L)).ncard = Module.finrank ℚ L := by
  classical
  let f : ℚ[X] := X ^ k - C (a : ℚ)
  have _ : Polynomial.IsSplittingField ℚ L f := inferInstance
  have hk0 : k ≠ 0 := by omega
  have haQ : (a : ℚ) ≠ 0 := Int.cast_ne_zero.mpr ha
  have hkQ : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hk0
  have hf_sep : f.Separable := Polynomial.separable_X_pow_sub_C (a : ℚ) hkQ haQ
  have _ : IsGalois ℚ L := IsGalois.of_separable_splitting_field hf_sep
  let _ : Fact p.Prime := ⟨hp⟩
  -- Integral roots of `X^k - a` in `𝓞 L`
  have hfL_eq : f.map (algebraMap ℚ L) = X ^ k - C (a : L) := by simp [f]
  have hfL_monic : (f.map (algebraMap ℚ L)).Monic := by
    rw [hfL_eq]; exact Polynomial.monic_X_pow_sub_C _ hk0
  have hfL_splits : (f.map (algebraMap ℚ L)).Splits := Polynomial.IsSplittingField.splits L f
  have hfL_sep : (f.map (algebraMap ℚ L)).Separable := hf_sep.map
  have hroots_nodup : (f.map (algebraMap ℚ L)).roots.Nodup := Polynomial.nodup_roots hfL_sep
  have hfL_deg : (f.map (algebraMap ℚ L)).natDegree = k := by
    rw [hfL_eq, Polynomial.natDegree_X_pow_sub_C]
  have hfL_ne : f.map (algebraMap ℚ L) ≠ 0 := by
    intro h0; have hdeg := congrArg Polynomial.natDegree h0
    rw [hfL_deg, Polynomial.natDegree_zero] at hdeg
    exact hk0 hdeg
  let RL : Finset L := (f.map (algebraMap ℚ L)).roots.toFinset
  have hRL_mem : ∀ x : L, x ∈ RL ↔ x ^ k = (a : L) := by
    intro x
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hfL_ne, Polynomial.IsRoot.def, hfL_eq]
    simp only [eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero]
  have hRL_int : ∀ x ∈ RL, IsIntegral ℤ x := by
    intro x hx
    refine ⟨X ^ k - C a, Polynomial.monic_X_pow_sub_C a hk0, ?_⟩
    rw [eval₂_sub, eval₂_X_pow, eval₂_C, eq_intCast, (hRL_mem x).mp hx, sub_self]
  let toInt : {x : L // x ∈ RL} → 𝓞 L := fun x => ⟨x.1, hRL_int x.1 x.2⟩
  have htoInt_inj : Function.Injective toInt := fun x y hxy =>
    Subtype.ext (congrArg (fun z : 𝓞 L => (z : L)) hxy)
  let SO : Finset (𝓞 L) := RL.attach.image toInt
  have hSO_mem : ∀ β : 𝓞 L, β ∈ SO ↔ (β : L) ∈ RL := by
    intro β
    constructor
    · intro hβ
      rcases Finset.mem_image.mp hβ with ⟨x, _, rfl⟩
      exact x.2
    · intro hβ
      exact Finset.mem_image.mpr ⟨⟨β.1, hβ⟩, Finset.mem_attach _ _, Subtype.ext rfl⟩
  have hSO_prod : (X ^ k - C (a : 𝓞 L) : (𝓞 L)[X]) = ∏ β ∈ SO, (X - C β) := by
    apply Polynomial.map_injective (algebraMap (𝓞 L) L) NumberField.RingOfIntegers.coe_injective
    have lhs_eq : (X ^ k - C (a : 𝓞 L) : (𝓞 L)[X]).map (algebraMap (𝓞 L) L) =
        f.map (algebraMap ℚ L) := by
      simp [hfL_eq]
    have rhs_eq : (∏ β ∈ SO, (X - C β : (𝓞 L)[X])).map (algebraMap (𝓞 L) L) =
        ((f.map (algebraMap ℚ L)).roots.map (X - C ·)).prod := by
      rw [Polynomial.map_prod]
      simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
      rw [Finset.prod_image (fun x _ y _ hxy => htoInt_inj hxy)]
      have hatt : ∏ x ∈ RL.attach, (X - C (algebraMap (𝓞 L) L (toInt x))) =
          ∏ x ∈ RL, (X - C x) :=
        Finset.prod_attach RL (fun x : L => X - C x)
      rw [hatt]
      change ((RL.val).map (fun x : L => X - C x)).prod = _
      dsimp only [RL]
      rw [Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hroots_nodup]
    rw [lhs_eq, rhs_eq]
    exact hfL_splits.eq_prod_roots_of_monic hfL_monic
  -- Prime ideal setup above `(p)`
  let pZ : Ideal ℤ := Ideal.span {(p : ℤ)}
  have hpZ_ne_bot : pZ ≠ ⊥ := by
    simp [pZ, hp.ne_zero]
  have _ : pZ.IsPrime :=
    (Ideal.span_singleton_prime (Nat.cast_ne_zero.mpr hp.ne_zero)).mpr (Nat.prime_iff_prime_int.mp hp)
  have _ : pZ.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hpZ_ne_bot
  let _ : MulSemiringAction (L ≃ₐ[ℚ] L) (𝓞 L) :=
    IsIntegralClosure.MulSemiringAction ℤ ℚ L (𝓞 L)
  have _ : IsGaloisGroup (L ≃ₐ[ℚ] L) ℤ (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing _ _ _ ℚ L
  obtain ⟨P, hP_over⟩ := (inferInstance : Nonempty (pZ.primesOver (𝓞 L)))
  have _ : P.IsPrime := hP_over.1
  have _ : P.LiesOver pZ := hP_over.2
  have hpZ_le_comap : pZ ≤ P.comap (algebraMap ℤ (𝓞 L)) := le_of_eq hP_over.2.1
  have hP_ne_bot : P ≠ ⊥ := by
    intro hbot
    have hp_mem : (p : ℤ) ∈ pZ := Ideal.mem_span_singleton_self _
    have hp_in_P : algebraMap ℤ (𝓞 L) (p : ℤ) ∈ P := hpZ_le_comap hp_mem
    rw [hbot] at hp_in_P
    have hp0 : (algebraMap ℤ (𝓞 L) (p : ℤ)) = 0 := hp_in_P
    exact (Nat.cast_ne_zero.mpr hp.ne_zero : ((p : ℕ) : 𝓞 L) ≠ 0) (by simpa using hp0)
  have _ : P.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hP_ne_bot
  let FP := (𝓞 L) ⧸ P
  let _ : Field FP := Ideal.Quotient.field P
  let π : 𝓞 L →+* FP := Ideal.Quotient.mk P
  let φ : ZMod p →+* FP :=
    (Ideal.quotientMap P (algebraMap ℤ (𝓞 L)) hpZ_le_comap).comp
      (Int.quotientSpanNatEquivZMod p).symm.toRingHom
  have hφ_intCast : ∀ n : ℤ, φ (n : ZMod p) = π (n : 𝓞 L) := by
    intro n
    have h1 := RingHom.congr_fun (Int.quotientSpanNatEquivZMod_comp_castRingHom p) n
    dsimp only [RingHom.comp_apply, Int.coe_castRingHom, RingEquiv.coe_toRingHom] at h1
    dsimp only [φ, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    rw [h1]
    rfl
  let fp : (ZMod p)[X] := X ^ k - C (a : ZMod p)
  have hfp_map : fp.map φ = ∏ β ∈ SO, (X - C (π β)) := by
    have h1 : fp.map φ = (X ^ k - C (a : 𝓞 L) : (𝓞 L)[X]).map π := by
      dsimp only [fp]
      simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
      rw [hφ_intCast a]
    rw [h1, hSO_prod, Polynomial.map_prod]
    simp
  have hcard_gal : Nat.card (L ≃ₐ[ℚ] L) = Module.finrank ℚ L := IsGalois.card_aut_eq_finrank ℚ L
  have hsmul_coe : ∀ (σ : L ≃ₐ[ℚ] L) (β : 𝓞 L), ((σ • β : 𝓞 L) : L) = σ (β : L) := by
    intro σ β
    exact algebraMap_galRestrictHom_apply ℤ ℚ L (𝓞 L) σ β
  constructor
  · -- `(→)` If `fp` splits over `ZMod p`, the decomposition group of `P` is trivial.
    intro hfp_splits
    have ha_zmod : (a : ZMod p) ≠ 0 := by rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hfp_sep : fp.Separable := Polynomial.separable_X_pow_sub_C' p k (a : ZMod p) hpk ha_zmod
    have hfp_monic : fp.Monic := Polynomial.monic_X_pow_sub_C (a : ZMod p) hk0
    have hπ_inj : Set.InjOn π (SO : Set (𝓞 L)) :=
      injOn_of_separable_eq_prod hfp_sep.map hfp_map
    have hfp_roots : fp.map φ = (fp.roots.map (fun r => X - C (φ r))).prod := by
      have heq_fp : fp = (fp.roots.map (X - C ·)).prod :=
        hfp_splits.eq_prod_roots_of_monic hfp_monic
      conv_lhs => rw [heq_fp]
      rw [Polynomial.map_multiset_prod]
      simp
    have hπ_in_Z : ∀ β ∈ SO, ∃ n : ℤ, β - (n : 𝓞 L) ∈ P := by
      intro β hβ
      have hev0 : eval (π β) (fp.map φ) = 0 := by
        rw [hfp_map, Polynomial.eval_prod]
        exact Finset.prod_eq_zero hβ (by simp)
      rw [hfp_roots, Polynomial.eval_multiset_prod, Multiset.prod_eq_zero_iff,
        Multiset.mem_map] at hev0
      obtain ⟨u, hu, hu0⟩ := hev0
      rw [Multiset.mem_map] at hu
      obtain ⟨r, _, rfl⟩ := hu
      simp only [eval_sub, eval_X, eval_C, sub_eq_zero] at hu0
      obtain ⟨n, rfl⟩ := ZMod.intCast_surjective r
      rw [hφ_intCast n] at hu0
      exact ⟨n, Ideal.Quotient.eq.mp hu0⟩
    have hstab_bot : MulAction.stabilizer (L ≃ₐ[ℚ] L) P = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro σ hσ
      have hσP : σ • P = P := hσ
      have hfix_SO : ∀ β ∈ SO, σ • β = β := by
        intro β hβ
        obtain ⟨n, hnP⟩ := hπ_in_Z β hβ
        have hsmulP : σ • (β - (n : 𝓞 L)) ∈ P := by
          rw [← hσP]
          exact Ideal.smul_mem_pointwise_smul σ (β - (n : 𝓞 L)) P hnP
        have hsmul_int : σ • (n : 𝓞 L) = (n : 𝓞 L) := by
          apply NumberField.RingOfIntegers.coe_injective
          change ((σ • (n : 𝓞 L) : 𝓞 L) : L) = ((n : 𝓞 L) : L)
          rw [hsmul_coe]
          simp
        have hsmul_eq : σ • (β - (n : 𝓞 L)) = σ • β - (n : 𝓞 L) := by
          rw [smul_sub, hsmul_int]
        rw [hsmul_eq] at hsmulP
        have hdiff : σ • β - β ∈ P := by
          have := P.sub_mem hsmulP hnP
          convert this using 1; ring
        have hπ_eq : π (σ • β) = π β := Ideal.Quotient.eq.mpr hdiff
        have hσβ_SO : σ • β ∈ SO := by
          rw [hSO_mem, hRL_mem]
          have hβ_pow : (β : L) ^ k = (a : L) := (hRL_mem (β : L)).mp ((hSO_mem β).mp hβ)
          rw [hsmul_coe, ← map_pow, hβ_pow, map_intCast]
        exact hπ_inj hσβ_SO hβ hπ_eq
      have hf_ne0 : f ≠ 0 := by
        intro h0
        have hdeg := congrArg Polynomial.natDegree h0
        rw [Polynomial.natDegree_X_pow_sub_C, Polynomial.natDegree_zero] at hdeg
        exact hk0 hdeg
      have hfix_rootSet : ∀ x ∈ f.rootSet L, σ x = x := by
        intro x hx
        have hx_RL : x ∈ RL := by
          rw [Polynomial.mem_rootSet_of_ne hf_ne0] at hx
          rw [hRL_mem]
          rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, hfL_eq] at hx
          simpa [sub_eq_zero] using hx
        let β : 𝓞 L := ⟨x, hRL_int x hx_RL⟩
        have hβ_SO : β ∈ SO := (hSO_mem β).mpr hx_RL
        have h1 : ((σ • β : 𝓞 L) : L) = (β : L) :=
          congrArg (fun z : 𝓞 L => (z : L)) (hfix_SO β hβ_SO)
        rwa [hsmul_coe] at h1
      apply AlgEquiv.ext
      intro y
      have hy_adjoin : y ∈ Algebra.adjoin ℚ (f.rootSet L : Set L) := by
        rw [Polynomial.IsSplittingField.adjoin_rootSet L f]
        exact Algebra.mem_top
      refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hy_adjoin
      · intro x hx; exact hfix_rootSet x hx
      · intro q; simp
      · intro u v _ _ hu hv; simp [hu, hv]
      · intro u v _ _ hu hv; simp [hu, hv]
    have horb_eq : MulAction.orbit (L ≃ₐ[ℚ] L) P = pZ.primesOver (𝓞 L) :=
      Algebra.IsInvariant.orbit_eq_primesOver ℤ (𝓞 L) (L ≃ₐ[ℚ] L) pZ P
    have horb_card := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (L ≃ₐ[ℚ] L) P)
    rw [Nat.card_prod, hstab_bot, Subgroup.card_bot, mul_one, hcard_gal] at horb_card
    rw [← horb_eq, ← Nat.card_coe_set_eq]
    exact horb_card
  · -- `(←)` Complete splitting in `𝓞 L` implies `f(P/p) = 1`, so `ZMod p ≃+* FP`.
    intro hncard
    have hfund := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn pZ (𝓞 L) (L ≃ₐ[ℚ] L)
    rw [hncard, hcard_gal] at hfund
    have hfin_pos : 0 < Module.finrank ℚ L := Module.finrank_pos
    have hef1 : pZ.ramificationIdxIn (𝓞 L) * pZ.inertiaDegIn (𝓞 L) = 1 := by
      nlinarith
    have hf1 : pZ.inertiaDegIn (𝓞 L) = 1 := Nat.eq_one_of_mul_eq_one_left hef1
    have hfP1 : P.inertiaDeg ℤ = 1 := by
      rw [← Ideal.inertiaDegIn_eq_inertiaDeg pZ P (L ≃ₐ[ℚ] L), hf1]
    have hnormP : Ideal.absNorm P = p := by
      have h1 := Ideal.absNorm_eq_pow_inertiaDeg' P hp
      have h2 : pZ.inertiaDeg' P = P.inertiaDeg ℤ := by
        rw [Ideal.inertiaDeg'_algebraMap, Ideal.inertiaDeg_eq_of_isMaximal (p := pZ)]
      rw [h2, hfP1, pow_one] at h1
      exact h1
    have hcard_FP : Nat.card FP = p := by
      simpa [FP, Ideal.absNorm_apply, Submodule.cardQuot_apply] using hnormP
    have hcard_ne0 : Nat.card FP ≠ 0 := by
      rw [hcard_FP]; exact hp.ne_zero
    have _ : Finite FP := Nat.finite_of_card_ne_zero hcard_ne0
    let _ : Fintype FP := Fintype.ofFinite FP
    have hbij : Function.Bijective φ := by
      rw [Fintype.bijective_iff_injective_and_card]
      refine ⟨φ.injective, ?_⟩
      rw [ZMod.card p, ← Nat.card_eq_fintype_card, hcard_FP]
    let eφ : ZMod p ≃+* FP := RingEquiv.ofBijective φ hbij
    have hmap_splits : (fp.map eφ.toRingHom).Splits := by
      change (fp.map φ).Splits
      rw [hfp_map]
      exact Polynomial.Splits.prod fun β _ => Polynomial.Splits.X_sub_C _
    have hback := hmap_splits.map eφ.symm.toRingHom
    rw [Polynomial.map_map] at hback
    have hcomp : eφ.symm.toRingHom.comp eφ.toRingHom = RingHom.id (ZMod p) := by
      ext z; exact eφ.symm_apply_apply z
    rwa [hcomp, Polynomial.map_id] at hback

/-- Part 2 of `H1` for any splitting field `L` of `X^k - C (a : ℚ)` over `ℚ`. -/
theorem log_abs_discr_le_aux
    (a : ℤ) (ha : a ≠ 0) (k : ℕ) (hk2 : 2 ≤ k)
    (L : Type*) [Field L] [NumberField L]
    [Polynomial.IsSplittingField ℚ L (X ^ k - C (a : ℚ))] :
    Real.log |(NumberField.discr L : ℝ)| ≤
      4 * (Module.finrank ℚ L : ℝ) * Real.log ((k : ℝ) * (a.natAbs : ℝ) + 2) := by
  classical
  let f : ℚ[X] := X ^ k - C (a : ℚ)
  have _ : Polynomial.IsSplittingField ℚ L f := inferInstance
  have hk0 : k ≠ 0 := by omega
  have hk1 : 1 ≤ k := by omega
  have _ : NeZero k := ⟨hk0⟩
  have haQ : (a : ℚ) ≠ 0 := Int.cast_ne_zero.mpr ha
  have hkQ : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hk0
  have hf_sep : f.Separable := Polynomial.separable_X_pow_sub_C (a : ℚ) hkQ haQ
  have hfL_eq : f.map (algebraMap ℚ L) = X ^ k - C (a : L) := by simp [f]
  have hfL_splits : (f.map (algebraMap ℚ L)).Splits := Polynomial.IsSplittingField.splits L f
  have hfL_sep : (f.map (algebraMap ℚ L)).Separable := hf_sep.map
  have hroots_nodup : (f.map (algebraMap ℚ L)).roots.Nodup := Polynomial.nodup_roots hfL_sep
  have hfL_deg : (f.map (algebraMap ℚ L)).natDegree = k := by
    rw [hfL_eq, Polynomial.natDegree_X_pow_sub_C]
  have hfL_ne : f.map (algebraMap ℚ L) ≠ 0 := by
    intro h0; have hdeg := congrArg Polynomial.natDegree h0
    rw [hfL_deg, Polynomial.natDegree_zero] at hdeg
    exact hk0 hdeg
  let RL : Finset L := (f.map (algebraMap ℚ L)).roots.toFinset
  have hRL_card : RL.card = k := by
    rw [Multiset.toFinset_card_of_nodup hroots_nodup]
    exact (Polynomial.splits_iff_card_roots.mp hfL_splits).trans hfL_deg
  obtain ⟨α, hα_RL⟩ : RL.Nonempty := Finset.card_pos.mp (by omega)
  have hRL_pow : ∀ x ∈ RL, x ^ k = (a : L) := by
    intro x hx
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hfL_ne, Polynomial.IsRoot.def, hfL_eq] at hx
    simpa [sub_eq_zero] using hx
  have hα_pow : α ^ k = (a : L) := hRL_pow α hα_RL
  have haL : (a : L) ≠ 0 := Int.cast_ne_zero.mpr ha
  have hRL_ne : ∀ x ∈ RL, x ≠ 0 := by
    intro x hx h0
    have hxp := hRL_pow x hx
    rw [h0, zero_pow hk0] at hxp
    exact haL hxp.symm
  have hα_ne : α ≠ 0 := hRL_ne α hα_RL
  -- Primitive `k`-th root of unity `ζ ∈ L`
  let toUnit : RL → rootsOfUnity k L := fun x =>
    ⟨Units.mk0 (x.1 / α) (div_ne_zero (hRL_ne x.1 x.2) hα_ne), by
      rw [mem_rootsOfUnity]
      ext
      simp only [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one, div_pow,
        hRL_pow x.1 x.2, hα_pow, div_self haL]⟩
  have htoUnit_inj : Function.Injective toUnit := by
    intro x y hxy
    have hval : x.1 / α = y.1 / α := by
      have := congrArg (fun u : rootsOfUnity k L => ((u : Lˣ) : L)) hxy
      simpa [toUnit] using this
    exact Subtype.ext ((div_left_inj' hα_ne).mp hval)
  have hcard_rootsU : Nat.card (rootsOfUnity k L) = k := by
    apply le_antisymm (card_rootsOfUnity L k)
    have h1 : Nat.card RL ≤ Nat.card (rootsOfUnity k L) :=
      Nat.card_le_card_of_injective toUnit htoUnit_inj
    rwa [Nat.card_eq_fintype_card, Fintype.card_coe, hRL_card] at h1
  obtain ⟨ζ, hζ_prim⟩ := card_rootsOfUnity_eq_iff_exists_isPrimitiveRoot.mp hcard_rootsU
  have hζ_pow : ζ ^ k = 1 := hζ_prim.pow_eq_one
  -- Intermediate field `F = ℚ(ζ)`
  let F : IntermediateField ℚ L := IntermediateField.adjoin ℚ ({ζ} : Set L)
  let _ : NumberField F := NumberField.of_module_finite ℚ F
  let ζF : F := ⟨ζ, IntermediateField.mem_adjoin_simple_self ℚ ζ⟩
  have hζF_pow : ζF ^ k = 1 := Subtype.ext hζ_pow
  have hζF_int : IsIntegral ℤ ζF :=
    ⟨X ^ k - 1, Polynomial.monic_X_pow_sub_C 1 hk0,
      by rw [eval₂_sub, eval₂_X_pow, eval₂_one, hζF_pow, sub_self]⟩
  let ζO : 𝓞 F := ⟨ζF, hζF_int⟩
  have hζO_pow : ζO ^ k = algebraMap ℤ (𝓞 F) 1 := by
    apply NumberField.RingOfIntegers.coe_injective
    rw [map_pow, map_one]
    exact hζF_pow
  have hζ_alg : IsAlgebraic ℚ ζ :=
    IsIntegral.isAlgebraic ⟨X ^ k - 1, Polynomial.monic_X_pow_sub_C 1 hk0,
      by rw [eval₂_sub, eval₂_X_pow, eval₂_one, hζ_pow, sub_self]⟩
  have hζF_gen : Algebra.adjoin ℚ ({algebraMap (𝓞 F) F ζO} : Set F) = ⊤ := by
    change Algebra.adjoin ℚ ({ζF} : Set F) = ⊤
    rw [eq_top_iff]
    intro y _
    have hy : y.1 ∈ F.toSubalgebra := y.2
    rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hζ_alg] at hy
    have hsub : ∀ z : L, z ∈ Algebra.adjoin ℚ ({ζ} : Set L) →
        ∃ w : F, w ∈ Algebra.adjoin ℚ ({ζF} : Set F) ∧ w.1 = z := by
      intro z hz
      refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hz
      · intro u hu
        rw [Set.mem_singleton_iff] at hu
        subst hu
        exact ⟨ζF, Algebra.self_mem_adjoin_singleton ℚ ζF, rfl⟩
      · intro q
        exact ⟨algebraMap ℚ F q, Subalgebra.algebraMap_mem _ q, rfl⟩
      · rintro u v _ _ ⟨wu, hwu, rfl⟩ ⟨wv, hwv, rfl⟩
        exact ⟨wu + wv, Subalgebra.add_mem _ hwu hwv, rfl⟩
      · rintro u v _ _ ⟨wu, hwu, rfl⟩ ⟨wv, hwv, rfl⟩
        exact ⟨wu * wv, Subalgebra.mul_mem _ hwu hwv, rfl⟩
    obtain ⟨w, hw, hwy⟩ := hsub y.1 hy
    have hw_eq : w = y := Subtype.ext hwy
    rwa [← hw_eq]
  -- Step 1: `|discr F| ≤ k ^ [F : ℚ]`
  have hk_mem_dF : ((k : ℕ) : 𝓞 F) ∈ differentIdeal ℤ (𝓞 F) := by
    have h := nat_mul_mem_differentIdeal ℤ ℚ (𝓞 F) F hζF_gen hk1 hζO_pow
    simpa using h
  have hdiscrF_le : (NumberField.discr F).natAbs ≤ k ^ Module.finrank ℚ F := by
    have hle : Ideal.span {((k : ℕ) : 𝓞 F)} ≤ differentIdeal ℤ (𝓞 F) :=
      Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hk_mem_dF)
    have hdvd := Ideal.absNorm_dvd_absNorm_of_le hle
    rw [NumberField.absNorm_differentIdeal F (𝓞 F), Ideal.absNorm_span_natCast,
      NumberField.RingOfIntegers.rank F] at hdvd
    exact Nat.le_of_dvd (pow_pos (by omega) _) hdvd
  -- Step 2: `L = F(α)` and `absNorm (differentIdeal (𝓞 F) (𝓞 L)) ≤ (k * |a|) ^ [L : ℚ]`
  have hα_intZ : IsIntegral ℤ α := by
    refine ⟨X ^ k - C a, Polynomial.monic_X_pow_sub_C a hk0, ?_⟩
    rw [eval₂_sub, eval₂_X_pow, eval₂_C, eq_intCast, hα_pow, sub_self]
  let αO : 𝓞 L := ⟨α, hα_intZ⟩
  have hIC_FL : IsIntegralClosure (𝓞 L) (𝓞 F) L :=
    { algebraMap_injective := NumberField.RingOfIntegers.coe_injective
      isIntegral_iff := fun {y} =>
        ⟨fun hy => ⟨⟨y, isIntegral_trans _ hy⟩, rfl⟩,
         fun ⟨z, hz⟩ => hz ▸ z.2.tower_top⟩ }
  let _ : IsIntegralClosure (𝓞 L) (𝓞 F) L := hIC_FL
  have hαO_pow : αO ^ k = algebraMap (𝓞 F) (𝓞 L) (a : 𝓞 F) := by
    apply NumberField.RingOfIntegers.coe_injective
    change α ^ k = algebraMap (𝓞 F) L (a : 𝓞 F)
    simpa using hα_pow
  have hf_ne0 : f ≠ 0 := by
    intro h0
    have hdeg := congrArg Polynomial.natDegree h0
    rw [Polynomial.natDegree_X_pow_sub_C, Polynomial.natDegree_zero] at hdeg
    exact hk0 hdeg
  have hαL_gen : Algebra.adjoin F ({algebraMap (𝓞 L) L αO} : Set L) = ⊤ := by
    change Algebra.adjoin F ({α} : Set L) = ⊤
    have hroot_sub : (f.rootSet L : Set L) ⊆ (Algebra.adjoin F ({α} : Set L) : Set L) := by
      intro x hx
      have hx_pow : x ^ k = (a : L) := by
        rw [Polynomial.mem_rootSet_of_ne hf_ne0] at hx
        rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, hfL_eq] at hx
        simpa [sub_eq_zero] using hx
      have hdiv_pow : (x / α) ^ k = 1 := by
        rw [div_pow, hx_pow, hα_pow, div_self haL]
      obtain ⟨i, _, hi_eq⟩ := hζ_prim.eq_pow_of_pow_eq_one hdiv_pow
      have hx_eq : x = α * (algebraMap F L ζF) ^ i := by
        have hζ_val : algebraMap F L ζF = ζ := rfl
        rw [hζ_val, hi_eq]
        exact (mul_div_cancel₀ x hα_ne).symm
      rw [hx_eq]
      exact Subalgebra.mul_mem _ (Algebra.self_mem_adjoin_singleton F α)
        (Subalgebra.pow_mem _ (Subalgebra.algebraMap_mem _ ζF) i)
    have hleQ : Algebra.adjoin ℚ (f.rootSet L : Set L) ≤
        (Algebra.adjoin F ({α} : Set L)).restrictScalars ℚ :=
      Algebra.adjoin_le_iff.mpr hroot_sub
    rw [Polynomial.IsSplittingField.adjoin_rootSet L f] at hleQ
    rw [eq_top_iff]
    intro y _
    exact hleQ (Algebra.mem_top : y ∈ (⊤ : Subalgebra ℚ L))
  have hka_mem_dFL : ((k * a.natAbs : ℕ) : 𝓞 L) ∈ differentIdeal (𝓞 F) (𝓞 L) := by
    have hmem := nat_mul_mem_differentIdeal (𝓞 F) F (𝓞 L) L hαL_gen hk1 hαO_pow
    have hmem' : ((k : ℤ) * a : 𝓞 L) ∈ differentIdeal (𝓞 F) (𝓞 L) := by
      convert hmem using 1
      apply NumberField.RingOfIntegers.coe_injective
      push_cast
      rfl
    rcases Int.natAbs_eq a with ha_eq | ha_eq
    · have hZ : ((k * a.natAbs : ℕ) : ℤ) = (k : ℤ) * a := by
        rw [Nat.cast_mul, ← ha_eq]
      have hcast : ((k * a.natAbs : ℕ) : 𝓞 L) = ((k : ℤ) * a : 𝓞 L) := by
        rw [← Int.cast_natCast, hZ, Int.cast_mul]
      rwa [hcast]
    · have hZ : ((k * a.natAbs : ℕ) : ℤ) = -((k : ℤ) * a) := by
        rw [Nat.cast_mul]
        conv_rhs => rw [ha_eq]
        ring
      have hcast : ((k * a.natAbs : ℕ) : 𝓞 L) = -(((k : ℤ) * a : 𝓞 L)) := by
        rw [← Int.cast_natCast, hZ, Int.cast_neg, Int.cast_mul]
      rw [hcast]
      exact (differentIdeal (𝓞 F) (𝓞 L)).neg_mem hmem'
  have hdFL_le : (differentIdeal (𝓞 F) (𝓞 L)).absNorm ≤
      (k * a.natAbs) ^ Module.finrank ℚ L := by
    have hle : Ideal.span {((k * a.natAbs : ℕ) : 𝓞 L)} ≤ differentIdeal (𝓞 F) (𝓞 L) :=
      Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hka_mem_dFL)
    have hdvd := Ideal.absNorm_dvd_absNorm_of_le hle
    rw [Ideal.absNorm_span_natCast, NumberField.RingOfIntegers.rank L] at hdvd
    have ha_pos : 0 < a.natAbs := Int.natAbs_pos.mpr ha
    exact Nat.le_of_dvd (pow_pos (Nat.mul_pos (by omega) ha_pos) _) hdvd
  -- Combine Step 1 & Step 2 via the tower discriminant formula
  have htower := NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow F (𝓞 F) L (𝓞 L)
  have hdiscrF_pow : (NumberField.discr F).natAbs ^ Module.finrank F L ≤ k ^ Module.finrank ℚ L := by
    calc
      (NumberField.discr F).natAbs ^ Module.finrank F L
        ≤ (k ^ Module.finrank ℚ F) ^ Module.finrank F L := Nat.pow_le_pow_left hdiscrF_le _
      _ = k ^ (Module.finrank ℚ F * Module.finrank F L) := (pow_mul k _ _).symm
      _ = k ^ Module.finrank ℚ L := by rw [Module.finrank_mul_finrank ℚ F L]
  have hdiscrL_nat : (NumberField.discr L).natAbs ≤
      (k * a.natAbs + 2) ^ (4 * Module.finrank ℚ L) := by
    have hmul : (NumberField.discr L).natAbs ≤
        ((k * a.natAbs) * k) ^ Module.finrank ℚ L := by
      rw [htower, mul_pow]
      exact Nat.mul_le_mul hdFL_le hdiscrF_pow
    have hbase : (k * a.natAbs) * k ≤ (k * a.natAbs + 2) ^ 4 := by
      have ha1 : 1 ≤ a.natAbs := Int.natAbs_pos.mpr ha
      have h1 : k ≤ k * a.natAbs + 2 := by nlinarith
      have h2 : k * a.natAbs ≤ k * a.natAbs + 2 := by omega
      have h3 : 1 ≤ k * a.natAbs + 2 := by omega
      calc
        (k * a.natAbs) * k ≤ (k * a.natAbs + 2) * (k * a.natAbs + 2) := Nat.mul_le_mul h2 h1
        _ = (k * a.natAbs + 2) ^ 2 * 1 * 1 := by ring
        _ ≤ (k * a.natAbs + 2) ^ 2 * (k * a.natAbs + 2) * (k * a.natAbs + 2) :=
            Nat.mul_le_mul (Nat.mul_le_mul_left _ h3) h3
        _ = (k * a.natAbs + 2) ^ 4 := by ring
    calc
      (NumberField.discr L).natAbs
        ≤ ((k * a.natAbs) * k) ^ Module.finrank ℚ L := hmul
      _ ≤ ((k * a.natAbs + 2) ^ 4) ^ Module.finrank ℚ L := Nat.pow_le_pow_left hbase _
      _ = (k * a.natAbs + 2) ^ (4 * Module.finrank ℚ L) := (pow_mul _ 4 _).symm
  -- Take real logarithms
  have hdiscr_pos : 0 < (NumberField.discr L).natAbs :=
    Int.natAbs_pos.mpr (NumberField.discr_ne_zero L)
  have habs_eq : |(NumberField.discr L : ℝ)| = ((NumberField.discr L).natAbs : ℝ) := by
    rw [← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]
  rw [habs_eq]
  have hcast_le : ((NumberField.discr L).natAbs : ℝ) ≤
      ((k : ℝ) * (a.natAbs : ℝ) + 2) ^ (4 * Module.finrank ℚ L) := by
    exact_mod_cast hdiscrL_nat
  have hlog := Real.log_le_log (by exact_mod_cast hdiscr_pos) hcast_le
  rw [Real.log_pow] at hlog
  push_cast at hlog
  linarith

end ArtinH1Proof

theorem OMA.solution :
    OMA.R_ArtinPrimitiveRootsConjecture_conditional_artin_primitive_roots_parts_i_R1_H1_R1.H1 := by
  intro a ha k _ hk2
  let K := (X ^ k - C (a : ℚ)).SplittingField
  let _ : NumberField K := NumberField.of_module_finite ℚ K
  let _ : Polynomial.IsSplittingField ℚ K (X ^ k - C (a : ℚ)) :=
    Polynomial.IsSplittingField.splittingField (X ^ k - C (a : ℚ))
  exact ⟨fun p hp hpa hpk =>
      ArtinH1Proof.splits_zmod_iff_ncard_primesOver_eq_finrank_aux a ha k hk2 K p hp hpa hpk,
    ArtinH1Proof.log_abs_discr_le_aux a ha k hk2 K⟩
