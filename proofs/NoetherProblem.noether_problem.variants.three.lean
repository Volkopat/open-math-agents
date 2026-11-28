import FormalConjectures.Wikipedia.NoetherProblem

/-!
Original proof by @Volkopat (PR #3542); transcendence-basis helpers simplified
using Mathlib.

Proof of NoetherProblem.noether_problem.variants.three:
For any field K and any subgroup H of K-automorphisms of K(X_0, X_1, X_2) permuting the 3
indeterminates, the fixed field L^H is purely transcendental over K (in every characteristic).
-/

namespace OMA.Noether3

open MvPolynomial NoetherProblem Equiv

private abbrev A3 (K : Type) [Field K] := MvPolynomial (Fin 3) K
private abbrev FR3 (K : Type) [Field K] := FractionRing (A3 K)

private noncomputable def permAut (K : Type) [Field K] (σ : Perm (Fin 3)) :
    FR3 K ≃ₐ[K] FR3 K :=
  IsFractionRing.algEquivOfAlgEquiv (MvPolynomial.renameEquiv K σ)

private lemma permAut_algebraMap {K : Type} [Field K] (σ : Perm (Fin 3)) (a : A3 K) :
    permAut K σ (algebraMap (A3 K) (FR3 K) a) = algebraMap (A3 K) (FR3 K) (rename σ a) := by
  rw [permAut, IsFractionRing.algEquivOfAlgEquiv_algebraMap]
  rfl

private lemma permAut_X {K : Type} [Field K] (σ : Perm (Fin 3)) (i : Fin 3) :
    permAut K σ (algebraMap (A3 K) (FR3 K) (X i)) = algebraMap (A3 K) (FR3 K) (X (σ i)) := by
  rw [permAut_algebraMap, rename_X]

private lemma permAut_one {K : Type} [Field K] : permAut K (1 : Perm (Fin 3)) = 1 := by
  ext y
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := A3 K) y
  rw [map_div₀, permAut_algebraMap, permAut_algebraMap]
  simp [Perm.coe_one, rename_id]

private lemma permAut_mul {K : Type} [Field K] (σ τ : Perm (Fin 3)) :
    permAut K (σ * τ) = permAut K σ * permAut K τ := by
  ext y
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := A3 K) y
  rw [AlgEquiv.mul_apply, map_div₀, map_div₀, map_div₀]
  simp only [permAut_algebraMap, rename_rename]
  rfl

private noncomputable def permAutHom (K : Type) [Field K] :
    Perm (Fin 3) →* (FR3 K ≃ₐ[K] FR3 K) where
  toFun := permAut K
  map_one' := permAut_one
  map_mul' := permAut_mul

private lemma permAutHom_injective (K : Type) [Field K] :
    Function.Injective (permAutHom K) := by
  intro σ τ h
  ext i
  have h1 : permAut K σ (algebraMap (A3 K) (FR3 K) (X i)) =
      permAut K τ (algebraMap (A3 K) (FR3 K) (X i)) :=
    congrArg (fun f : FR3 K ≃ₐ[K] FR3 K => f (algebraMap (A3 K) (FR3 K) (X i))) h
  rw [permAut_X, permAut_X] at h1
  have h2 : (X (σ i) : A3 K) = X (τ i) := IsFractionRing.injective (A3 K) (FR3 K) h1
  have h3 := congrArg (MvPolynomial.eval (Pi.single (σ i) (1 : K))) h2
  simp only [eval_X, Pi.single_eq_same] at h3
  by_contra hne
  have hne' : σ i ≠ τ i := fun he => hne (congrArg Fin.val he)
  rw [Pi.single_eq_of_ne (Ne.symm hne')] at h3
  exact one_ne_zero h3

private lemma mem_intermediateField_of_mem_X {K : Type} [Field K]
    (E : IntermediateField K (FR3 K))
    (hX : ∀ i : Fin 3, algebraMap (A3 K) (FR3 K) (X i) ∈ E) :
    E = ⊤ := by
  rw [eq_top_iff]
  intro y _
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := A3 K) y
  have hpoly : ∀ p : A3 K, algebraMap (A3 K) (FR3 K) p ∈ E := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C k =>
      change algebraMap (A3 K) (FR3 K) (algebraMap K (A3 K) k) ∈ E
      rw [← IsScalarTower.algebraMap_apply K (A3 K) (FR3 K)]
      exact E.algebraMap_mem k
    | add p q hp hq =>
      rw [map_add]
      exact E.add_mem hp hq
    | mul_X p i hp =>
      rw [map_mul]
      exact E.mul_mem hp (hX i)
  exact E.div_mem (hpoly a) (hpoly b)

private lemma xFun_isTranscendenceBasis (K : Type) [Field K] :
    IsTranscendenceBasis K (fun i : Fin 3 => algebraMap (A3 K) (FR3 K) (X i)) := by
  have : Algebra.IsAlgebraic (A3 K) (FR3 K) :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors (A3 K))
  exact (IsTranscendenceBasis.mvPolynomial (Fin 3) K).algebraMap_comp

open scoped IntermediateField.algebraAdjoinAdjoin in
private lemma algebraicIndependent_of_isAlgebraic_adjoin {K : Type} [Field K]
    (f : Fin 3 → FR3 K)
    (halg : Algebra.IsAlgebraic (IntermediateField.adjoin K (Set.range f)) (FR3 K)) :
    AlgebraicIndependent K f := by
  have : Algebra.IsAlgebraic (Algebra.adjoin K (Set.range f)) (FR3 K) :=
    Algebra.IsAlgebraic.trans _ (IntermediateField.adjoin K (Set.range f)) _
  apply (Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite K f ?_).1
  have htr := (xFun_isTranscendenceBasis K).lift_cardinalMk_eq_trdeg
  simpa only [Cardinal.lift_id] using htr.le

private lemma isRational_of_adjoin_fin3 {K : Type} [Field K]
    (f : Fin 3 → FR3 K)
    (halg : Algebra.IsAlgebraic (IntermediateField.adjoin K (Set.range f)) (FR3 K)) :
    IsRationalExtension K (IntermediateField.adjoin K (Set.range f)) (Fin 3) := by
  exact ⟨⟨(algebraicIndependent_of_isAlgebraic_adjoin f halg).aevalEquivField.symm⟩⟩

private lemma intermediateField_eq_of_finrank_le {K L : Type*} [Field K] [Field L] [Algebra K L]
    {E F : IntermediateField K L} (hEF : E ≤ F) [FiniteDimensional E L]
    {n : ℕ} (hn : 0 < n) (hE : Module.finrank E L ≤ n) (hF : Module.finrank F L = n) :
    E = F := by
  letI : Algebra E F := (IntermediateField.inclusion hEF).toRingHom.toAlgebra
  haveI : IsScalarTower E F L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : FiniteDimensional E F := FiniteDimensional.left E F L
  haveI : FiniteDimensional F L := FiniteDimensional.right E F L
  have hmul := Module.finrank_mul_finrank E F L
  rw [hF] at hmul
  have hpos_EF : 0 < Module.finrank E F := Module.finrank_pos
  have hfin_EF_eq_one : Module.finrank E F = 1 := by nlinarith
  apply le_antisymm hEF
  intro y hy
  have hrange : LinearMap.range (Algebra.linearMap E F) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have hinj : Function.Injective (Algebra.linearMap E F) :=
      RingHom.injective (algebraMap E F)
    rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_self, hfin_EF_eq_one]
  have hmem : (⟨y, hy⟩ : F) ∈ LinearMap.range (Algebra.linearMap E F) := by
    rw [hrange]; trivial
  obtain ⟨z, hz⟩ := hmem
  have : (z : L) = y := congrArg Subtype.val hz
  rw [← this]
  exact z.2

private lemma aeval_cubic_apply {K L : Type*} [Field K] [Field L] [Algebra K L]
    {E : IntermediateField K L} (a b c : E) (z : L) :
    Polynomial.aeval z (Polynomial.X ^ 3 + Polynomial.C a * Polynomial.X ^ 2 +
      Polynomial.C b * Polynomial.X + Polynomial.C c) =
      z ^ 3 + (a : L) * z ^ 2 + (b : L) * z + (c : L) := by
  rw [map_add, map_add, map_add, map_mul, map_mul, map_pow, map_pow,
    Polynomial.aeval_X, Polynomial.aeval_C, Polynomial.aeval_C, Polynomial.aeval_C]
  rfl

/-- Key engine: if H ≤ Aut_K(FR3 K) is a finite subgroup, f : Fin 3 → FR3 K lands in fixedField H,
and FR3 K = K(f)(α) where α satisfies a nonzero polynomial over K(f) of degree ≤ |H|,
then fixedField H = K(f) and is purely transcendental over K. -/
private lemma fixedField_isRational_of_single_gen {K : Type} [Field K]
    (H : Subgroup (FR3 K ≃ₐ[K] FR3 K)) [Fintype H]
    (f : Fin 3 → FR3 K)
    (hf : ∀ i, f i ∈ IntermediateField.fixedField H)
    (α : FR3 K)
    (P : Polynomial (IntermediateField.adjoin K (Set.range f)))
    (hP0 : P ≠ 0)
    (hPdeg : P.natDegree ≤ Fintype.card H)
    (hPα : Polynomial.aeval α P = 0)
    (hgen : ∀ i : Fin 3, algebraMap (A3 K) (FR3 K) (X i) ∈
      IntermediateField.adjoin (IntermediateField.adjoin K (Set.range f)) ({α} : Set (FR3 K))) :
    IsRationalExtension K (IntermediateField.fixedField H) (Fin 3) := by
  classical
  let E := IntermediateField.adjoin K (Set.range f)
  let F := IntermediateField.fixedField H
  have hEF : E ≤ F := by
    rw [IntermediateField.adjoin_le_iff]
    rintro y ⟨i, rfl⟩
    exact hf i
  have htop : IntermediateField.adjoin E ({α} : Set (FR3 K)) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    have hKtop : (IntermediateField.adjoin E ({α} : Set (FR3 K))).restrictScalars K = ⊤ :=
      mem_intermediateField_of_mem_X _ hgen
    have : y ∈ (IntermediateField.adjoin E ({α} : Set (FR3 K))).restrictScalars K := by
      rw [hKtop]; trivial
    exact this
  have halgα : IsAlgebraic E α := ⟨P, hP0, hPα⟩
  have hint : IsIntegral E α := isAlgebraic_iff_isIntegral.mp halgα
  haveI hfd_adj : FiniteDimensional E (IntermediateField.adjoin E ({α} : Set (FR3 K))) :=
    IntermediateField.adjoin.finiteDimensional hint
  have hEqvTop : IntermediateField.adjoin E ({α} : Set (FR3 K)) ≃ₗ[E] FR3 K :=
    ((IntermediateField.equivOfEq htop).trans IntermediateField.topEquiv).toLinearEquiv
  haveI hfd_E : FiniteDimensional E (FR3 K) := hEqvTop.finiteDimensional
  have hfin_E_le : Module.finrank E (FR3 K) ≤ Fintype.card H := by
    rw [← hEqvTop.finrank_eq, IntermediateField.adjoin.finrank hint]
    exact (Polynomial.natDegree_le_of_dvd (minpoly.dvd E α hPα) hP0).trans hPdeg
  have hfin_F : Module.finrank F (FR3 K) = Fintype.card H :=
    FixedPoints.finrank_eq_card H (FR3 K)
  have hEF_eq : E = F :=
    intermediateField_eq_of_finrank_le hEF (Fintype.card_pos_iff.mpr ⟨1⟩) hfin_E_le hfin_F
  have halg_E : Algebra.IsAlgebraic E (FR3 K) := Algebra.IsAlgebraic.of_finite E (FR3 K)
  have hrat_E : IsRationalExtension K E (Fin 3) := isRational_of_adjoin_fin3 f halg_E
  obtain ⟨eE⟩ := hrat_E.pure_transcendental
  exact ⟨⟨(IntermediateField.equivOfEq hEF_eq.symm).trans eE⟩⟩

/-- Case |G| = 6: full symmetric group S_3 via esymmAlgEquiv. -/
private lemma prod_rename_symm {K : Type} [Field K] (q : A3 K) (τ : Perm (Fin 3)) :
    rename τ (∏ σ : Perm (Fin 3), rename σ q) = ∏ σ : Perm (Fin 3), rename σ q := by
  rw [map_prod]
  simp_rw [rename_rename]
  exact Fintype.prod_equiv (Equiv.mulLeft τ) (fun σ => rename (⇑τ ∘ ⇑σ) q)
    (fun σ => rename ⇑σ q) (fun σ => by simp [Perm.coe_mul])

private lemma fixedField_full_symm {K : Type} [Field K]
    (H : Subgroup (FR3 K ≃ₐ[K] FR3 K))
    (hH : ∀ σ : Perm (Fin 3), permAut K σ ∈ H)
    (hHsub : ∀ h ∈ H, ∃ σ : Perm (Fin 3), h = permAut K σ) :
    IsRationalExtension K (IntermediateField.fixedField H) (Fin 3) := by
  classical
  set E := IntermediateField.fixedField H
  let s := esymmAlgEquiv (Fin 3) K (Fintype.card_fin 3)
  let f : A3 K →+* FR3 K := (algebraMap (A3 K) (FR3 K)).comp
    ((symmetricSubalgebra (Fin 3) K).val.toRingHom.comp (s : A3 K →+* symmetricSubalgebra (Fin 3) K))
  have hf : ∀ p, f p = algebraMap (A3 K) (FR3 K) (s p : A3 K) := fun _ => rfl
  have fmem : ∀ p, f p ∈ E := by
    intro p
    rw [IntermediateField.mem_fixedField_iff]
    intro h hh
    obtain ⟨σ, rfl⟩ := hHsub h hh
    rw [hf, permAut_algebraMap, (s p).2 σ]
  let g : A3 K →+* E := f.codRestrict E fmem
  have hg : ∀ p, (g p : FR3 K) = algebraMap (A3 K) (FR3 K) (s p : A3 K) := fun _ => rfl
  have ginj : Function.Injective g := by
    intro p q hpq
    have h1 : (g p : FR3 K) = g q := congrArg Subtype.val hpq
    rw [hg, hg] at h1
    exact s.injective (Subtype.ext (IsFractionRing.injective (A3 K) (FR3 K) h1))
  letI : Algebra (A3 K) E := g.toAlgebra
  have hgalg : ∀ p, algebraMap (A3 K) E p = g p := fun _ => rfl
  have : FaithfulSMul (A3 K) E := (faithfulSMul_iff_algebraMap_injective (A3 K) E).mpr ginj
  have hsurj : ∀ z : E, ∃ x y : A3 K, z = algebraMap (A3 K) E x / algebraMap (A3 K) E y := by
    intro z
    have hz : ∀ σ : Perm (Fin 3), permAut K σ (z : FR3 K) = z := fun σ =>
      (IntermediateField.mem_fixedField_iff H (z : FR3 K)).mp z.2 (permAut K σ) (hH σ)
    obtain ⟨p, q, hq, hpq⟩ := IsFractionRing.div_surjective (A := A3 K) (z : FR3 K)
    have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
    have haq : algebraMap (A3 K) (FR3 K) q ≠ 0 := by
      intro h; exact hq0 (IsFractionRing.injective (A3 K) (FR3 K) (h.trans (map_zero _).symm))
    set R := ∏ σ ∈ Finset.univ.erase (1 : Perm (Fin 3)), rename σ q with hRd
    set Q := ∏ σ : Perm (Fin 3), rename σ q with hQd
    have hQ : Q = q * R := by
      rw [hQd, hRd, ← Finset.mul_prod_erase Finset.univ (fun σ : Perm (Fin 3) => rename σ q)
        (Finset.mem_univ 1)]
      simp [Perm.coe_one, rename_id]
    have hQsym : Q.IsSymmetric := fun τ => prod_rename_symm q τ
    have hQ0 : Q ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      intro σ _
      exact (rename_injective _ σ.injective).ne_iff' (map_zero _) |>.mpr hq0
    have hkey : algebraMap (A3 K) (FR3 K) (p * R) = (z : FR3 K) * algebraMap (A3 K) (FR3 K) Q := by
      rw [← hpq, hQ, map_mul, map_mul, div_mul_eq_mul_div, eq_div_iff haq]
      ring
    have hPsym : (p * R).IsSymmetric := by
      intro τ
      apply IsFractionRing.injective (A3 K) (FR3 K)
      rw [← permAut_algebraMap, hkey, map_mul, hz τ, permAut_algebraMap, hQsym τ]
    refine ⟨s.symm ⟨p * R, hPsym⟩, s.symm ⟨Q, hQsym⟩, ?_⟩
    have hgy : g (s.symm ⟨Q, hQsym⟩) ≠ 0 := by
      rw [Ne, ← map_zero g]
      intro h
      have := ginj h
      rw [← map_zero s.symm] at this
      exact hQ0 (congrArg Subtype.val (s.symm.injective this))
    rw [hgalg, hgalg, eq_div_iff hgy]
    apply Subtype.ext
    rw [IntermediateField.coe_mul, hg, hg]
    simp only [AlgEquiv.apply_symm_apply, hkey]
  have : IsFractionRing (A3 K) E := IsFractionRing.of_field (A3 K) E hsurj
  let eqv : FR3 K ≃ₐ[A3 K] E := IsLocalization.algEquiv (nonZeroDivisors (A3 K)) (FR3 K) E
  have hcomm : ∀ k : K, eqv.toRingEquiv (algebraMap K (FR3 K) k) = algebraMap K E k := by
    intro k
    rw [IsScalarTower.algebraMap_apply K (A3 K) (FR3 K) k]
    change eqv (algebraMap (A3 K) (FR3 K) (algebraMap K (A3 K) k)) = _
    rw [AlgEquiv.commutes, hgalg]
    apply Subtype.ext
    rw [hg, AlgEquiv.commutes]
    change algebraMap (A3 K) (FR3 K) (algebraMap K (A3 K) k) = _
    rw [← IsScalarTower.algebraMap_apply K (A3 K) (FR3 K)]
    rfl
  exact ⟨⟨(AlgEquiv.ofRingEquiv (f := eqv.toRingEquiv) hcomm).symm⟩⟩

/-- Helper: algebraic distinctness of X_0, X_1, X_2 in FR3 K. -/
private lemma x_sub_ne_zero {K : Type} [Field K] {i j : Fin 3} (hij : i ≠ j) :
    algebraMap (A3 K) (FR3 K) (X i) - algebraMap (A3 K) (FR3 K) (X j) ≠ 0 := by
  intro h
  have h1 : algebraMap (A3 K) (FR3 K) (X i) = algebraMap (A3 K) (FR3 K) (X j) := sub_eq_zero.mp h
  have h2 : (X i : A3 K) = X j := IsFractionRing.injective (A3 K) (FR3 K) h1
  have h3 := congrArg (MvPolynomial.eval (Pi.single i (1 : K))) h2
  simp only [eval_X, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hij)] at h3
  exact one_ne_zero h3

private lemma x_sum_ne_zero {K : Type} [Field K] :
    algebraMap (A3 K) (FR3 K) (X 0) + algebraMap (A3 K) (FR3 K) (X 1) +
      algebraMap (A3 K) (FR3 K) (X 2) ≠ 0 := by
  intro h
  have h1 : algebraMap (A3 K) (FR3 K) (X 0 + X 1 + X 2) = 0 := by simpa [map_add] using h
  have h2 : (X 0 + X 1 + X 2 : A3 K) = 0 :=
    IsFractionRing.injective (A3 K) (FR3 K) (h1.trans (map_zero _).symm)
  have h3 := congrArg (MvPolynomial.eval (Pi.single (0 : Fin 3) (1 : K))) h2
  simp [eval_X] at h3

/-- Helpers for quadratic and cubic polynomials over a field. -/
private lemma natDegree_C_mul_X_le' {E : Type*} [Field E] (a : E) :
    (Polynomial.C a * Polynomial.X : Polynomial E).natDegree ≤ 1 :=
  (Polynomial.natDegree_C_mul_le a Polynomial.X).trans (by simp)

private lemma natDegree_quad_le {E : Type*} [Field E] (a b : E) :
    (Polynomial.X ^ 2 + Polynomial.C a * Polynomial.X + Polynomial.C b : Polynomial E).natDegree ≤ 2 := by
  calc (Polynomial.X ^ 2 + Polynomial.C a * Polynomial.X + Polynomial.C b).natDegree
      ≤ max (Polynomial.X ^ 2 + Polynomial.C a * Polynomial.X).natDegree (Polynomial.C b).natDegree :=
        Polynomial.natDegree_add_le _ _
    _ ≤ 2 := by
      rw [max_le_iff]; refine ⟨?_, by simp⟩
      calc (Polynomial.X ^ 2 + Polynomial.C a * Polynomial.X).natDegree
          ≤ max (Polynomial.X ^ 2 : Polynomial E).natDegree (Polynomial.C a * Polynomial.X).natDegree :=
            Polynomial.natDegree_add_le _ _
        _ ≤ 2 := by
          rw [max_le_iff]; exact ⟨by simp, (natDegree_C_mul_X_le' a).trans (by norm_num)⟩

private lemma quad_ne_zero {E : Type*} [Field E] (a b : E) :
    (Polynomial.X ^ 2 + Polynomial.C a * Polynomial.X + Polynomial.C b : Polynomial E) ≠ 0 := by
  intro h
  have hc := congrArg (fun q => Polynomial.coeff q 2) h
  simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow] at hc

private lemma natDegree_cubic_le {E : Type*} [Field E] (a b c : E) :
    (Polynomial.X ^ 3 + Polynomial.C a * Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X +
      Polynomial.C c : Polynomial E).natDegree ≤ 3 := by
  calc (Polynomial.X ^ 3 + Polynomial.C a * Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X +
        Polynomial.C c).natDegree
      ≤ max (Polynomial.X ^ 3 + Polynomial.C a * Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X).natDegree
          (Polynomial.C c).natDegree := Polynomial.natDegree_add_le _ _
    _ ≤ 3 := by
      rw [max_le_iff]; refine ⟨?_, by simp⟩
      calc (Polynomial.X ^ 3 + Polynomial.C a * Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X).natDegree
          ≤ max (Polynomial.X ^ 3 + Polynomial.C a * Polynomial.X ^ 2).natDegree
              (Polynomial.C b * Polynomial.X).natDegree := Polynomial.natDegree_add_le _ _
        _ ≤ 3 := by
          rw [max_le_iff]; refine ⟨?_, (natDegree_C_mul_X_le' b).trans (by norm_num)⟩
          calc (Polynomial.X ^ 3 + Polynomial.C a * Polynomial.X ^ 2).natDegree
              ≤ max (Polynomial.X ^ 3 : Polynomial E).natDegree (Polynomial.C a * Polynomial.X ^ 2).natDegree :=
                Polynomial.natDegree_add_le _ _
            _ ≤ 3 := by
              rw [max_le_iff]; refine ⟨by simp, ?_⟩
              exact (Polynomial.natDegree_C_mul_le _ _).trans (by simp)

private lemma cubic_ne_zero {E : Type*} [Field E] (a b c : E) :
    (Polynomial.X ^ 3 + Polynomial.C a * Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X +
      Polynomial.C c : Polynomial E) ≠ 0 := by
  intro h
  have hc := congrArg (fun q => Polynomial.coeff q 3) h
  simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow] at hc

/-- Case |G| = 2: G = ⟨swap 0 1⟩. -/
private lemma fixedField_swap01 {K : Type} [Field K]
    (H : Subgroup (FR3 K ≃ₐ[K] FR3 K)) [Fintype H]
    (hcard : Fintype.card H = 2)
    (hHsub : ∀ h ∈ H, h = 1 ∨ h = permAut K (Equiv.swap 0 1)) :
    IsRationalExtension K (IntermediateField.fixedField H) (Fin 3) := by
  classical
  set x0 : FR3 K := algebraMap (A3 K) (FR3 K) (X 0)
  set x1 : FR3 K := algebraMap (A3 K) (FR3 K) (X 1)
  set x2 : FR3 K := algebraMap (A3 K) (FR3 K) (X 2)
  have hτ0 : permAut K (Equiv.swap 0 1) x0 = x1 := by simp [x0, x1, permAut_X]
  have hτ1 : permAut K (Equiv.swap 0 1) x1 = x0 := by simp [x0, x1, permAut_X]
  have hτ2 : permAut K (Equiv.swap 0 1) x2 = x2 := by
    have : (Equiv.swap (0 : Fin 3) 1) 2 = 2 := by decide
    simp only [x2, permAut_X, this]
  let f : Fin 3 → FR3 K := ![x0 + x1, x0 * x1, x2]
  have hf : ∀ i, f i ∈ IntermediateField.fixedField H := by
    intro i
    rw [IntermediateField.mem_fixedField_iff]
    intro h hh
    rcases hHsub h hh with rfl | rfl
    · rfl
    · fin_cases i
      · change permAut K (Equiv.swap 0 1) (x0 + x1) = x0 + x1
        rw [map_add, hτ0, hτ1]; ring
      · change permAut K (Equiv.swap 0 1) (x0 * x1) = x0 * x1
        rw [map_mul, hτ0, hτ1]; ring
      · change permAut K (Equiv.swap 0 1) x2 = x2
        exact hτ2
  set E := IntermediateField.adjoin K (Set.range f)
  let e0 : E := ⟨f 0, IntermediateField.subset_adjoin K _ ⟨0, rfl⟩⟩
  let e1 : E := ⟨f 1, IntermediateField.subset_adjoin K _ ⟨1, rfl⟩⟩
  let e2 : E := ⟨f 2, IntermediateField.subset_adjoin K _ ⟨2, rfl⟩⟩
  let P : Polynomial E := Polynomial.X ^ 2 + Polynomial.C (-e0) * Polynomial.X + Polynomial.C e1
  have hPα : Polynomial.aeval x0 P = 0 := by
    simp only [P, map_add, map_pow, map_mul, map_neg, Polynomial.aeval_X, Polynomial.aeval_C]
    change x0 ^ 2 + -(x0 + x1) * x0 + x0 * x1 = 0
    ring
  have hgen : ∀ i : Fin 3, algebraMap (A3 K) (FR3 K) (X i) ∈
      IntermediateField.adjoin E ({x0} : Set (FR3 K)) := by
    intro i
    have hx0 : x0 ∈ IntermediateField.adjoin E ({x0} : Set (FR3 K)) :=
      IntermediateField.subset_adjoin E _ rfl
    have he0 : x0 + x1 ∈ IntermediateField.adjoin E ({x0} : Set (FR3 K)) :=
      (IntermediateField.adjoin E ({x0} : Set (FR3 K))).algebraMap_mem e0
    have he2 : x2 ∈ IntermediateField.adjoin E ({x0} : Set (FR3 K)) :=
      (IntermediateField.adjoin E ({x0} : Set (FR3 K))).algebraMap_mem e2
    fin_cases i
    · exact hx0
    · have : x1 = (x0 + x1) - x0 := by ring
      change x1 ∈ _
      rw [this]
      exact sub_mem he0 hx0
    · exact he2
  exact fixedField_isRational_of_single_gen H f hf x0 P (quad_ne_zero _ _)
    (by rw [hcard]; exact natDegree_quad_le _ _) hPα hgen

set_option maxHeartbeats 800000 in
/-- Case |G| = 3: G = A_3 = ⟨(0 1 2)⟩. Works in every characteristic (splits on (3 : FR3 K) = 0). -/
private lemma fixedField_A3 {K : Type} [Field K]
    (H : Subgroup (FR3 K ≃ₐ[K] FR3 K)) [Fintype H]
    (hcard : Fintype.card H = 3)
    (hHsub : ∀ h ∈ H, h = 1 ∨ h = permAut K (Equiv.swap 0 1 * Equiv.swap 1 2) ∨
      h = permAut K ((Equiv.swap 0 1 * Equiv.swap 1 2) * (Equiv.swap 0 1 * Equiv.swap 1 2))) :
    IsRationalExtension K (IntermediateField.fixedField H) (Fin 3) := by
  classical
  set σ : Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 1 2
  set x0 : FR3 K := algebraMap (A3 K) (FR3 K) (X 0)
  set x1 : FR3 K := algebraMap (A3 K) (FR3 K) (X 1)
  set x2 : FR3 K := algebraMap (A3 K) (FR3 K) (X 2)
  have hσ0 : permAut K σ x0 = x1 := by
    have : σ 0 = 1 := by decide
    simp only [x0, x1, permAut_X, this]
  have hσ1 : permAut K σ x1 = x2 := by
    have : σ 1 = 2 := by decide
    simp only [x1, x2, permAut_X, this]
  have hσ2 : permAut K σ x2 = x0 := by
    have : σ 2 = 0 := by decide
    simp only [x2, x0, permAut_X, this]
  have hfix_of_σ : ∀ y : FR3 K, permAut K σ y = y → y ∈ IntermediateField.fixedField H := by
    intro y hy
    rw [IntermediateField.mem_fixedField_iff]
    intro h hh
    rcases hHsub h hh with rfl | rfl | rfl
    · rfl
    · exact hy
    · rw [permAut_mul, AlgEquiv.mul_apply, hy, hy]
  by_cases hchar3 : (3 : FR3 K) = 0
  · -- Characteristic 3: e1 = x0 + x1 + x2, U = (x1 - x2) / e1, f = ![e1, U^3 - U, x0 + e1 * U^2]
    set e1 : FR3 K := x0 + x1 + x2
    have he1_ne : e1 ≠ 0 := x_sum_ne_zero
    set U : FR3 K := (x1 - x2) / e1
    have hσe1 : permAut K σ e1 = e1 := by
      simp only [e1, map_add, hσ0, hσ1, hσ2]; ring
    have hσU : permAut K σ U = U - 1 := by
      simp only [U, map_div₀, map_sub, hσ1, hσ2, hσe1]
      field_simp [he1_ne]
      linear_combination x2 * hchar3
    let f : Fin 3 → FR3 K := ![e1, U ^ 3 - U, x0 + e1 * U ^ 2]
    have hf : ∀ i, f i ∈ IntermediateField.fixedField H := by
      intro i
      apply hfix_of_σ
      fin_cases i
      · change permAut K σ e1 = e1
        exact hσe1
      · change permAut K σ (U ^ 3 - U) = U ^ 3 - U
        rw [map_sub, map_pow, hσU]
        linear_combination (U - U ^ 2) * hchar3
      · change permAut K σ (x0 + e1 * U ^ 2) = x0 + e1 * U ^ 2
        rw [map_add, map_mul, map_pow, hσ0, hσe1, hσU]
        have hdiff : x1 - x0 + e1 * (1 - 2 * U) = 0 := by
          simp only [U]
          field_simp [he1_ne]
          simp only [e1]
          linear_combination x2 * hchar3
        linear_combination hdiff
    set E := IntermediateField.adjoin K (Set.range f)
    let g0 : E := ⟨f 0, IntermediateField.subset_adjoin K _ ⟨0, rfl⟩⟩
    let g1 : E := ⟨f 1, IntermediateField.subset_adjoin K _ ⟨1, rfl⟩⟩
    let g2 : E := ⟨f 2, IntermediateField.subset_adjoin K _ ⟨2, rfl⟩⟩
    let P : Polynomial E :=
      Polynomial.X ^ 3 + Polynomial.C 0 * Polynomial.X ^ 2 + Polynomial.C (-1) * Polynomial.X +
        Polynomial.C (-g1)
    have hPα : Polynomial.aeval U P = 0 := by
      simp only [P, map_add, map_mul, map_pow, map_neg, map_one, map_zero,
        Polynomial.aeval_X, Polynomial.aeval_C]
      change U ^ 3 + 0 * U ^ 2 + -1 * U + -(U ^ 3 - U) = 0
      ring
    have hgen : ∀ i : Fin 3, algebraMap (A3 K) (FR3 K) (X i) ∈
        IntermediateField.adjoin E ({U} : Set (FR3 K)) := by
      intro i
      set M := IntermediateField.adjoin E ({U} : Set (FR3 K))
      have hU : U ∈ M := IntermediateField.subset_adjoin E _ rfl
      have hg0 : e1 ∈ M := M.algebraMap_mem g0
      have hg2 : x0 + e1 * U ^ 2 ∈ M := M.algebraMap_mem g2
      have hx0 : x0 ∈ M := by
        have : x0 = (x0 + e1 * U ^ 2) - e1 * U ^ 2 := by ring
        rw [this]; exact sub_mem hg2 (mul_mem hg0 (pow_mem hU 2))
      have hx1 : x1 ∈ M := by
        have : x1 = -(e1 - x0 + e1 * U) := by
          simp only [U]
          field_simp [he1_ne]
          simp only [e1]
          linear_combination x1 * hchar3
        rw [this]; exact neg_mem (add_mem (sub_mem hg0 hx0) (mul_mem hg0 hU))
      fin_cases i
      · exact hx0
      · exact hx1
      · have : x2 = e1 - x0 - x1 := by simp only [e1]; ring
        change x2 ∈ M
        rw [this]; exact sub_mem (sub_mem hg0 hx0) hx1
    exact fixedField_isRational_of_single_gen H f hf U P (cubic_ne_zero _ _ _)
      (by rw [hcard]; exact natDegree_cubic_le _ _ _) hPα hgen
  · -- Characteristic ≠ 3: w = x1 - x2, Z = (x0 - x1) / w
    set w : FR3 K := x1 - x2
    have hw_ne : w ≠ 0 := x_sub_ne_zero (by decide)
    set Z : FR3 K := (x0 - x1) / w
    have hZ_ne : Z ≠ 0 := div_ne_zero (x_sub_ne_zero (by decide)) hw_ne
    have hZ1_ne : Z + 1 ≠ 0 := by
      intro h
      have h1 : x0 - x2 = 0 := by
        have h2 : (x0 - x1) / w + 1 = 0 := h
        field_simp [hw_ne] at h2
        simp only [w] at h2
        linear_combination h2
      exact x_sub_ne_zero (by decide) h1
    have hZ2_ne : Z ^ 2 + Z + 1 ≠ 0 := by
      intro h
      have hpoly : (x0 - x1) ^ 2 + (x0 - x1) * (x1 - x2) + (x1 - x2) ^ 2 = 0 := by
        have h2 : ((x0 - x1) / w) ^ 2 + (x0 - x1) / w + 1 = 0 := h
        field_simp [hw_ne] at h2
        simp only [w] at h2
        linear_combination h2
      have hA : algebraMap (A3 K) (FR3 K)
          ((X 0 - X 1) ^ 2 + (X 0 - X 1) * (X 1 - X 2) + (X 1 - X 2) ^ 2) = 0 := by
        simpa [x0, x1, x2, map_add, map_sub, map_mul, map_pow] using hpoly
      have hA0 : ((X 0 - X 1) ^ 2 + (X 0 - X 1) * (X 1 - X 2) + (X 1 - X 2) ^ 2 : A3 K) = 0 :=
        IsFractionRing.injective (A3 K) (FR3 K) (hA.trans (map_zero _).symm)
      have hev := congrArg (MvPolynomial.eval (Pi.single (0 : Fin 3) (1 : K))) hA0
      simp [eval_X] at hev
    have hσw : permAut K σ w = -(Z + 1) * w := by
      have h1 : permAut K σ w = x2 - x0 := by rw [show w = x1 - x2 from rfl, map_sub, hσ1, hσ2]
      rw [h1]
      have hZw : Z * w = x0 - x1 := div_mul_cancel₀ _ hw_ne
      rw [show -(Z + 1) * w = -(Z * w) - w from by ring, hZw]
      simp only [w]; ring
    have hσZ : permAut K σ Z = -1 / (Z + 1) := by
      have h1 : permAut K σ Z = (x1 - x2) / permAut K σ w := by
        rw [show Z = (x0 - x1) / w from rfl, map_div₀, map_sub, hσ0, hσ1]
      rw [h1, hσw]
      change w / (-(Z + 1) * w) = -1 / (Z + 1)
      field_simp [hw_ne, hZ1_ne]
    let f : Fin 3 → FR3 K :=
      ![x0 + x1 + x2, (Z ^ 3 - 3 * Z - 1) / (Z * (Z + 1)), w * (Z ^ 2 + Z + 1) ^ 2 / (Z * (Z + 1))]
    have hf : ∀ i, f i ∈ IntermediateField.fixedField H := by
      intro i
      apply hfix_of_σ
      fin_cases i
      · change permAut K σ (x0 + x1 + x2) = x0 + x1 + x2
        rw [map_add, map_add, hσ0, hσ1, hσ2]; ring
      · change permAut K σ ((Z ^ 3 - 3 * Z - 1) / (Z * (Z + 1))) = (Z ^ 3 - 3 * Z - 1) / (Z * (Z + 1))
        simp only [map_div₀, map_sub, map_mul, map_pow, map_add, map_one, map_ofNat, hσZ]
        field_simp [hZ_ne, hZ1_ne]; ring
      · change permAut K σ (w * (Z ^ 2 + Z + 1) ^ 2 / (Z * (Z + 1))) =
          w * (Z ^ 2 + Z + 1) ^ 2 / (Z * (Z + 1))
        simp only [map_div₀, map_mul, map_pow, map_add, map_one, hσw, hσZ]
        field_simp [hZ_ne, hZ1_ne]; ring
    set E := IntermediateField.adjoin K (Set.range f)
    let g0 : E := ⟨f 0, IntermediateField.subset_adjoin K _ ⟨0, rfl⟩⟩
    let g1 : E := ⟨f 1, IntermediateField.subset_adjoin K _ ⟨1, rfl⟩⟩
    let g2 : E := ⟨f 2, IntermediateField.subset_adjoin K _ ⟨2, rfl⟩⟩
    let P : Polynomial E :=
      Polynomial.X ^ 3 + Polynomial.C (-g1) * Polynomial.X ^ 2 +
        Polynomial.C (-(g1 + 3)) * Polynomial.X + Polynomial.C (-1)
    have hPα : Polynomial.aeval Z P = 0 := by
      rw [show P = _ from rfl, aeval_cubic_apply]
      change Z ^ 3 + -((Z ^ 3 - 3 * Z - 1) / (Z * (Z + 1))) * Z ^ 2 +
        -(((Z ^ 3 - 3 * Z - 1) / (Z * (Z + 1))) + 3) * Z + -1 = 0
      field_simp [hZ_ne, hZ1_ne]; ring
    have hgen : ∀ i : Fin 3, algebraMap (A3 K) (FR3 K) (X i) ∈
        IntermediateField.adjoin E ({Z} : Set (FR3 K)) := by
      intro i
      set M := IntermediateField.adjoin E ({Z} : Set (FR3 K))
      have hZ : Z ∈ M := IntermediateField.subset_adjoin E _ rfl
      have hg0 : x0 + x1 + x2 ∈ M := M.algebraMap_mem g0
      have hg2 : w * (Z ^ 2 + Z + 1) ^ 2 / (Z * (Z + 1)) ∈ M := M.algebraMap_mem g2
      have hw : w ∈ M := by
        have hZ2' : Z * (Z + 1) + 1 ≠ 0 := by convert hZ2_ne using 1; ring
        have : w = (w * (Z ^ 2 + Z + 1) ^ 2 / (Z * (Z + 1))) * (Z * (Z + 1)) / (Z ^ 2 + Z + 1) ^ 2 := by
          field_simp [hZ_ne, hZ1_ne, hZ2_ne, hZ2']
        rw [this]
        exact div_mem (mul_mem hg2 (mul_mem hZ (add_mem hZ M.one_mem)))
          (pow_mem (add_mem (add_mem (pow_mem hZ 2) hZ) M.one_mem) 2)
      have hx0 : x0 ∈ M := by
        have hZw : Z * w = x0 - x1 := div_mul_cancel₀ _ hw_ne
        have : x0 = ((x0 + x1 + x2) + (2 * Z + 1) * w) / 3 := by
          rw [eq_div_iff hchar3, show (2 * Z + 1) * w = 2 * (Z * w) + w from by ring, hZw]
          simp only [w]; ring
        rw [this]
        exact div_mem (add_mem hg0 (mul_mem (add_mem (mul_mem (M.algebraMap_mem (2 : E)) hZ) M.one_mem) hw))
          (M.algebraMap_mem (3 : E))
      have hx1 : x1 ∈ M := by
        have hZw : Z * w = x0 - x1 := div_mul_cancel₀ _ hw_ne
        have : x1 = x0 - Z * w := by rw [hZw]; ring
        rw [this]; exact sub_mem hx0 (mul_mem hZ hw)
      fin_cases i
      · exact hx0
      · exact hx1
      · have : x2 = x1 - w := by simp only [w]; ring
        change x2 ∈ M
        rw [this]; exact sub_mem hx1 hw
    exact fixedField_isRational_of_single_gen H f hf Z P (cubic_ne_zero _ _ _)
      (by rw [hcard]; exact natDegree_cubic_le _ _ _) hPα hgen

/-- Classification of subgroups of Perm (Fin 3) by cardinality. -/
private lemma subgroup_perm_fin3_cases (G : Subgroup (Perm (Fin 3))) :
    G = ⊥ ∨
    G = ⊤ ∨
    (∃ τ : Perm (Fin 3), ∃ π : Perm (Fin 3), π * τ * π⁻¹ = Equiv.swap 0 1 ∧
      (∀ σ ∈ G, σ = 1 ∨ σ = τ) ∧ Nat.card G = 2) ∨
    ((∀ σ ∈ G, σ = 1 ∨ σ = Equiv.swap 0 1 * Equiv.swap 1 2 ∨
      σ = (Equiv.swap 0 1 * Equiv.swap 1 2) * (Equiv.swap 0 1 * Equiv.swap 1 2)) ∧
      Nat.card G = 3) := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  have hdvd : Fintype.card G ∣ Fintype.card (Perm (Fin 3)) := by
    simpa [Nat.card_eq_fintype_card] using Subgroup.card_subgroup_dvd_card G
  have h6 : Fintype.card (Perm (Fin 3)) = 6 := by decide
  rw [h6] at hdvd
  have hpos : 0 < Fintype.card G := Fintype.card_pos_iff.mpr ⟨1⟩
  have hcases : Fintype.card G = 1 ∨ Fintype.card G = 2 ∨ Fintype.card G = 3 ∨ Fintype.card G = 6 := by
    have hle : Fintype.card G ≤ 6 := Nat.le_of_dvd (by decide) hdvd
    interval_cases h : Fintype.card G <;> simp_all
  rcases hcases with h1 | h2 | h3 | h6'
  · left
    rw [eq_bot_iff]
    intro σ hσ
    have hsub : Subsingleton G := Fintype.card_le_one_iff_subsingleton.mp (le_of_eq h1)
    exact congrArg Subtype.val (Subsingleton.elim (⟨σ, hσ⟩ : G) 1)
  · right; right; left
    have hne : ∃ τ ∈ G, τ ≠ 1 := by
      by_contra hall
      push Not at hall
      have hsub : Subsingleton G := ⟨fun a b => Subtype.ext ((hall a.1 a.2).trans (hall b.1 b.2).symm)⟩
      have := Fintype.card_le_one_iff_subsingleton.mpr hsub
      omega
    obtain ⟨τ, hτG, hτne⟩ := hne
    have hall : ∀ σ ∈ G, σ = 1 ∨ σ = τ := by
      intro σ hσ
      by_contra h
      push Not at h
      have h3 : ({(1 : G), ⟨τ, hτG⟩, ⟨σ, hσ⟩} : Finset G).card = 3 := by
        apply Finset.card_eq_three.mpr
        exact ⟨1, ⟨τ, hτG⟩, ⟨σ, hσ⟩, fun e => hτne (congrArg Subtype.val e).symm,
          fun e => h.1 (congrArg Subtype.val e).symm,
          fun e => h.2 (congrArg Subtype.val e).symm, rfl⟩
      have hle := Finset.card_le_univ ({(1 : G), ⟨τ, hτG⟩, ⟨σ, hσ⟩} : Finset G)
      omega
    have hτsq : τ * τ = 1 := by
      rcases hall (τ * τ) (G.mul_mem hτG hτG) with h | h
      · exact h
      · exfalso; exact hτne (mul_left_cancel (a := τ) (by simpa using h))
    have hconj_all : ∀ x : Perm (Fin 3), x ≠ 1 → x * x = 1 →
        ∃ π : Perm (Fin 3), π * x * π⁻¹ = Equiv.swap 0 1 := by decide
    obtain ⟨π, hπ⟩ := hconj_all τ hτne hτsq
    exact ⟨τ, π, hπ, hall, by rw [Nat.card_eq_fintype_card, h2]⟩
  · right; right; right
    refine ⟨?_, by rw [Nat.card_eq_fintype_card, h3]⟩
    intro σ hσ
    have hpow : σ ^ 3 = 1 := by
      have : (⟨σ, hσ⟩ : G) ^ Fintype.card G = 1 := pow_card_eq_one
      rw [h3] at this
      exact congrArg Subtype.val this
    have h3_all : ∀ x : Perm (Fin 3), x ^ 3 = 1 →
        x = 1 ∨ x = Equiv.swap 0 1 * Equiv.swap 1 2 ∨
        x = (Equiv.swap 0 1 * Equiv.swap 1 2) * (Equiv.swap 0 1 * Equiv.swap 1 2) := by decide
    exact h3_all σ hpow
  · right; left
    rw [eq_top_iff]
    intro σ _
    have huniv : (Finset.univ.filter (fun x : Perm (Fin 3) => x ∈ G)) = Finset.univ := by
      apply Finset.eq_univ_of_card
      have : (Finset.univ.filter (fun x : Perm (Fin 3) => x ∈ G)).card = Fintype.card G := by
        rw [Fintype.card_subtype]
      rw [this, h6', Fintype.card_perm]; decide
    have : σ ∈ Finset.univ.filter (fun x : Perm (Fin 3) => x ∈ G) := by rw [huniv]; exact Finset.mem_univ σ
    exact (Finset.mem_filter.mp this).2

end OMA.Noether3

open OMA.Noether3 MvPolynomial NoetherProblem Equiv in
theorem OMA.solution : type_of% @NoetherProblem.noether_problem.variants.three := by
  intro K L ι _ _ _ _ _ hι e H hH
  classical
  -- Transport e : L ≃ₐ[K] FractionRing (MvPolynomial ι K) to e3 : L ≃ₐ[K] FR3 K
  let eqι : ι ≃ Fin 3 := Fintype.equivFinOfCardEq hι
  let renameFR : FractionRing (MvPolynomial ι K) ≃ₐ[K] FR3 K :=
    IsFractionRing.algEquivOfAlgEquiv (MvPolynomial.renameEquiv K eqι)
  let e3 : L ≃ₐ[K] FR3 K := e.trans renameFR
  -- Transport H to H3 ≤ (FR3 K ≃ₐ[K] FR3 K) via AlgEquiv.autCongr e3
  let H3 : Subgroup (FR3 K ≃ₐ[K] FR3 K) := H.map (AlgEquiv.autCongr e3).toMonoidHom
  have hH3_perm : ∀ h ∈ H3, ∃ σ : Perm (Fin 3), h = permAut K σ := by
    rintro h ⟨g, hg, rfl⟩
    obtain ⟨σ₀, rfl⟩ := hH g hg
    refine ⟨eqι.symm.trans (σ₀.trans eqι), ?_⟩
    ext y
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := A3 K) y
    simp only [e3, MulEquiv.coe_toMonoidHom, AlgEquiv.autCongr_apply, AlgEquiv.trans_apply,
      AlgEquiv.symm_trans_apply, map_div₀]
    have hconj : ∀ (g : FractionRing (MvPolynomial ι K) ≃ₐ[K] FractionRing (MvPolynomial ι K))
        (z : FractionRing (MvPolynomial ι K)), e ((e.autCongr.symm g) (e.symm z)) = g z := by
      intro g z
      change e (e.symm (g (e (e.symm z)))) = g z
      simp
    rw [hconj, hconj]
    have hsymm : ∀ p : A3 K, renameFR.symm (algebraMap (A3 K) (FR3 K) p) =
        algebraMap (MvPolynomial ι K) (FractionRing (MvPolynomial ι K)) (rename eqι.symm p) := by
      intro p
      apply renameFR.injective
      rw [AlgEquiv.apply_symm_apply]
      have h1 : renameFR (algebraMap (MvPolynomial ι K) (FractionRing (MvPolynomial ι K)) (rename eqι.symm p)) =
          algebraMap (A3 K) (FR3 K) ((MvPolynomial.renameEquiv K eqι) (rename eqι.symm p)) :=
        IsFractionRing.algEquivOfAlgEquiv_algebraMap (MvPolynomial.renameEquiv K eqι) (rename eqι.symm p)
      rw [h1]
      congr 1
      change p = rename eqι (rename eqι.symm p)
      rw [rename_rename]
      simp
    rw [hsymm a, hsymm b]
    simp only [renameFR, IsFractionRing.algEquivOfAlgEquiv_algebraMap, permAut_algebraMap]
    change algebraMap (A3 K) (FR3 K) (rename eqι (rename σ₀ (rename eqι.symm a))) /
      algebraMap (A3 K) (FR3 K) (rename eqι (rename σ₀ (rename eqι.symm b))) =
      algebraMap (A3 K) (FR3 K) (rename (eqι.symm.trans (σ₀.trans eqι)) a) /
      algebraMap (A3 K) (FR3 K) (rename (eqι.symm.trans (σ₀.trans eqι)) b)
    simp only [rename_rename]
    rfl
  -- Pull back H3 along permAutHom K to get G ≤ Perm (Fin 3)
  let G : Subgroup (Perm (Fin 3)) := H3.comap (permAutHom K)
  letI : Fintype G := Fintype.ofFinite G
  -- fixedField H ≃ₐ[K] fixedField H3 via e3
  have heqv_fixed : IntermediateField.fixedField H ≃ₐ[K] IntermediateField.fixedField H3 :=
    { toFun := fun x => ⟨e3 x.1, by
        rw [IntermediateField.mem_fixedField_iff]
        rintro h ⟨g, hg, rfl⟩
        change e3 (g (e3.symm (e3 x.1))) = e3 x.1
        rw [AlgEquiv.symm_apply_apply, (IntermediateField.mem_fixedField_iff H x.1).mp x.2 g hg]⟩
      invFun := fun y => ⟨e3.symm y.1, by
        rw [IntermediateField.mem_fixedField_iff]
        intro g hg
        have hy := (IntermediateField.mem_fixedField_iff H3 y.1).mp y.2 (AlgEquiv.autCongr e3 g)
          ⟨g, hg, rfl⟩
        have h1 : e3 (g (e3.symm y.1)) = y.1 := hy
        have h2 := congrArg e3.symm h1
        simpa using h2⟩
      left_inv := fun x => Subtype.ext (e3.symm_apply_apply x.1)
      right_inv := fun y => Subtype.ext (e3.apply_symm_apply y.1)
      map_mul' := fun x y => Subtype.ext (map_mul e3 x.1 y.1)
      map_add' := fun x y => Subtype.ext (map_add e3 x.1 y.1)
      commutes' := fun k => Subtype.ext (e3.commutes k) }
  -- It suffices to prove IsRationalExtension K (fixedField H3) (Fin 3)
  suffices hrat3 : IsRationalExtension K (IntermediateField.fixedField H3) (Fin 3) by
    obtain ⟨eF⟩ := hrat3.pure_transcendental
    exact ⟨Fin 3, ⟨⟨heqv_fixed.trans eF⟩⟩⟩
  rcases subgroup_perm_fin3_cases G with hbot | htop | ⟨τ, π, hπ, hall2, hcard2⟩ | ⟨hall3, hcard3⟩
  · -- |G| = 1: H3 = ⊥
    have hH3_top : IntermediateField.fixedField H3 = ⊤ := by
      rw [eq_top_iff]
      intro y _
      rw [IntermediateField.mem_fixedField_iff]
      intro h hh
      obtain ⟨σ, rfl⟩ := hH3_perm h hh
      have hσ1 : σ = 1 := by
        have : σ ∈ G := hh
        rw [hbot] at this
        exact this
      rw [hσ1, permAut_one]; rfl
    exact ⟨⟨(IntermediateField.equivOfEq hH3_top).trans IntermediateField.topEquiv⟩⟩
  · -- |G| = 6: H3 = full S_3
    exact fixedField_full_symm H3 (fun σ => by
      have : σ ∈ G := by rw [htop]; trivial
      exact this) hH3_perm
  · -- |G| = 2: conjugate H3 by permAut K π so τ becomes swap 0 1
    let φ : FR3 K ≃ₐ[K] FR3 K := permAut K π
    let H3' : Subgroup (FR3 K ≃ₐ[K] FR3 K) := H3.map (AlgEquiv.autCongr φ).toMonoidHom
    have hH3'_sub : ∀ h ∈ H3', h = 1 ∨ h = permAut K (Equiv.swap 0 1) := by
      rintro h ⟨g, hg, rfl⟩
      obtain ⟨σ, rfl⟩ := hH3_perm g hg
      have hσG : σ ∈ G := hg
      rcases hall2 σ hσG with rfl | hστ
      · left; ext y; simp [permAut_one]
      · right
        rw [hστ]
        change permAut K π * permAut K τ * (permAut K π)⁻¹ = permAut K (Equiv.swap 0 1)
        have hinv : (permAut K π)⁻¹ = permAut K π⁻¹ :=
          (map_inv (permAutHom K) π).symm
        rw [hinv, ← permAut_mul, ← permAut_mul, hπ]
    have hbij : Function.Bijective (fun x : G =>
        (⟨AlgEquiv.autCongr φ (permAutHom K x.1), ⟨permAutHom K x.1, x.2, rfl⟩⟩ : H3')) := by
      constructor
      · intro a b hab
        have h1 := congrArg Subtype.val hab
        exact Subtype.ext (permAutHom_injective K ((AlgEquiv.autCongr φ).injective h1))
      · rintro ⟨h, g, hg, rfl⟩
        obtain ⟨σ, rfl⟩ := hH3_perm g hg
        exact ⟨⟨σ, hg⟩, rfl⟩
    letI : Fintype H3' := Fintype.ofEquiv G (Equiv.ofBijective _ hbij)
    have hcardH3' : Fintype.card H3' = 2 := by
      rw [← Fintype.card_of_bijective hbij, ← Nat.card_eq_fintype_card, hcard2]
    have hrat' := fixedField_swap01 H3' hcardH3' hH3'_sub
    obtain ⟨eF⟩ := hrat'.pure_transcendental
    let heqv' : IntermediateField.fixedField H3 ≃ₐ[K] IntermediateField.fixedField H3' :=
      { toFun := fun x => ⟨φ x.1, by
          rw [IntermediateField.mem_fixedField_iff]
          rintro h ⟨g, hg, rfl⟩
          change φ (g (φ.symm (φ x.1))) = φ x.1
          rw [AlgEquiv.symm_apply_apply, (IntermediateField.mem_fixedField_iff H3 x.1).mp x.2 g hg]⟩
        invFun := fun y => ⟨φ.symm y.1, by
          rw [IntermediateField.mem_fixedField_iff]
          intro g hg
          have hy := (IntermediateField.mem_fixedField_iff H3' y.1).mp y.2 (AlgEquiv.autCongr φ g)
            ⟨g, hg, rfl⟩
          have h2 := congrArg φ.symm hy
          simpa using h2⟩
        left_inv := fun x => Subtype.ext (φ.symm_apply_apply x.1)
        right_inv := fun y => Subtype.ext (φ.apply_symm_apply y.1)
        map_mul' := fun x y => Subtype.ext (map_mul φ x.1 y.1)
        map_add' := fun x y => Subtype.ext (map_add φ x.1 y.1)
        commutes' := fun k => Subtype.ext (φ.commutes k) }
    exact ⟨⟨heqv'.trans eF⟩⟩
  · -- |G| = 3: H3 = A_3
    have hbij : Function.Bijective (fun x : G => (⟨permAutHom K x.1, x.2⟩ : H3)) := by
      constructor
      · intro a b hab; exact Subtype.ext (permAutHom_injective K (congrArg Subtype.val hab))
      · rintro ⟨h, hh⟩
        obtain ⟨σ, rfl⟩ := hH3_perm h hh
        exact ⟨⟨σ, hh⟩, rfl⟩
    letI : Fintype H3 := Fintype.ofEquiv G (Equiv.ofBijective _ hbij)
    have hcardH3 : Fintype.card H3 = 3 := by
      rw [← Fintype.card_of_bijective hbij, ← Nat.card_eq_fintype_card, hcard3]
    have hH3_sub : ∀ h ∈ H3, h = 1 ∨ h = permAut K (Equiv.swap 0 1 * Equiv.swap 1 2) ∨
        h = permAut K ((Equiv.swap 0 1 * Equiv.swap 1 2) * (Equiv.swap 0 1 * Equiv.swap 1 2)) := by
      intro h hh
      obtain ⟨σ, rfl⟩ := hH3_perm h hh
      rcases hall3 σ hh with rfl | rfl | rfl
      · exact Or.inl permAut_one
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
    exact fixedField_A3 H3 hcardH3 hH3_sub
