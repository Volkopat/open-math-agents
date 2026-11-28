import OMAReductions.R_SerreMultiplicityConjectures_supportDim_add_supportDim_le_ringKrullDim_R1
import Mathlib

/-!
Noetherianity and quotient Krull dimension invariance for maximal-ideal adic completion
of a Noetherian local ring.
-/

namespace SerreCompletionDim

open Ideal IsLocalRing Module TensorProduct

section Helpers

private def quotMap {A B : Type*} [CommRing A] [CommRing B] (I : Ideal A) (J : Ideal B)
    (f : A →+* B) (h : I ≤ J.comap f) : A ⧸ I →+* B ⧸ J :=
  Ideal.Quotient.lift I ((Ideal.Quotient.mk J).comp f) fun _ ha =>
    Ideal.Quotient.eq_zero_iff_mem.mpr (h ha)

private lemma quotMap_mk {A B : Type*} [CommRing A] [CommRing B] (I : Ideal A) (J : Ideal B)
    (f : A →+* B) (h : I ≤ J.comap f) (a : A) :
    quotMap I J f h (Ideal.Quotient.mk I a) = Ideal.Quotient.mk J (f a) :=
  rfl

end Helpers

section NoetherianCompletion

private lemma trunc_aeval_compat {A : Type*} [CommRing A] {s : Finset A}
    {m n : ℕ} (hle : m ≤ n)
    (hpow : ∀ k, MvPolynomial.idealOfVars (↥s) A ^ k ≤
      ((Ideal.span (s : Set A)) ^ k).comap
        (MvPolynomial.aeval (Subtype.val : ↥s → A)).toRingHom) :
    (Ideal.Quotient.factorPow (Ideal.span (s : Set A)) hle).comp
      ((quotMap (MvPolynomial.idealOfVars (↥s) A ^ n) ((Ideal.span (s : Set A)) ^ n)
        (MvPolynomial.aeval (Subtype.val : ↥s → A)).toRingHom (hpow n)).comp
        (MvPowerSeries.truncTotalAlgHom (↥s) A n).toRingHom) =
    (quotMap (MvPolynomial.idealOfVars (↥s) A ^ m) ((Ideal.span (s : Set A)) ^ m)
      (MvPolynomial.aeval (Subtype.val : ↥s → A)).toRingHom (hpow m)).comp
      (MvPowerSeries.truncTotalAlgHom (↥s) A m).toRingHom := by
  ext p
  change Ideal.Quotient.factorPow (Ideal.span (s : Set A)) hle
      (Ideal.Quotient.mk ((Ideal.span (s : Set A)) ^ n)
        ((MvPolynomial.aeval (Subtype.val : ↥s → A)) (MvPowerSeries.truncTotal n p))) =
    Ideal.Quotient.mk ((Ideal.span (s : Set A)) ^ m)
      ((MvPolynomial.aeval (Subtype.val : ↥s → A)) (MvPowerSeries.truncTotal m p))
  rw [Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk, Ideal.Quotient.eq, ← map_sub]
  exact hpow m (MvPowerSeries.truncTotal_sub_truncTotal_mem_pow_idealOfVars hle le_rfl p)

theorem adicCompletion_isNoetherianRing (A : Type*) [CommRing A] [IsNoetherianRing A]
    (J : Ideal A) : IsNoetherianRing (AdicCompletion J A) := by
  classical
  have hJfg : J.FG := Ideal.fg_of_isNoetherianRing J
  obtain ⟨s, hs⟩ := hJfg
  subst hs
  let J0 : Ideal A := Ideal.span (s : Set A)
  let φ : MvPolynomial (↥s) A →ₐ[A] A := MvPolynomial.aeval (Subtype.val : ↥s → A)
  have hmapV : (MvPolynomial.idealOfVars (↥s) A).map φ.toRingHom = J0 := by
    rw [MvPolynomial.idealOfVars, Ideal.map_span]
    congr 1
    ext x
    simp [φ]
  have hpow : ∀ k : ℕ, MvPolynomial.idealOfVars (↥s) A ^ k ≤ (J0 ^ k).comap φ.toRingHom := by
    intro k
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow, hmapV]
  let f : (n : ℕ) → MvPowerSeries (↥s) A →+* A ⧸ J0 ^ n := fun n =>
    (quotMap (MvPolynomial.idealOfVars (↥s) A ^ n) (J0 ^ n) φ.toRingHom (hpow n)).comp
      (MvPowerSeries.truncTotalAlgHom (↥s) A n).toRingHom
  let Ψ : MvPowerSeries (↥s) A →+* AdicCompletion J0 A :=
    AdicCompletion.liftRingHom J0 f (fun {m n} hle => trunc_aeval_compat hle hpow)
  have hΨ_C : ∀ a : A, Ψ (MvPowerSeries.C a) = algebraMap A (AdicCompletion J0 A) a := by
    intro a
    apply AdicCompletion.ext_evalₐ
    intro n
    rw [AdicCompletion.evalₐ_liftRingHom, AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_of]
    have hC : MvPowerSeries.C (σ := ↥s) a =
        ((MvPolynomial.C a : MvPolynomial (↥s) A) : MvPowerSeries (↥s) A) :=
      (MvPolynomial.coe_C a).symm
    have hcommC : MvPowerSeries.truncTotalAlgHom (↥s) A n (MvPowerSeries.C a) =
        Ideal.Quotient.mk _ (MvPolynomial.C a) := by
      rw [hC]
      exact (MvPowerSeries.truncTotalAlgHom (↥s) A n).commutes (MvPolynomial.C a)
    change quotMap _ _ φ.toRingHom (hpow n)
      (MvPowerSeries.truncTotalAlgHom (↥s) A n (MvPowerSeries.C a)) = _
    rw [hcommC, quotMap_mk]
    simp [φ]
  have hΨ_X : ∀ i : ↥s, Ψ (MvPowerSeries.X i) = algebraMap A (AdicCompletion J0 A) i.val := by
    intro i
    apply AdicCompletion.ext_evalₐ
    intro n
    rw [AdicCompletion.evalₐ_liftRingHom, AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_of]
    have hX : MvPowerSeries.X i =
        ((MvPolynomial.X i : MvPolynomial (↥s) A) : MvPowerSeries (↥s) A) :=
      (MvPolynomial.coe_X i).symm
    have hcommX : MvPowerSeries.truncTotalAlgHom (↥s) A n (MvPowerSeries.X i) =
        Ideal.Quotient.mk _ (MvPolynomial.X i) := by
      rw [hX]
      exact (MvPowerSeries.truncTotalAlgHom (↥s) A n).commutes (MvPolynomial.X i)
    change quotMap _ _ φ.toRingHom (hpow n)
      (MvPowerSeries.truncTotalAlgHom (↥s) A n (MvPowerSeries.X i)) = _
    rw [hcommX, quotMap_mk]
    simp [φ]
  let K : Ideal (MvPowerSeries (↥s) A) := Ideal.span (Set.range (MvPowerSeries.X : ↥s → _))
  have hKmap : K.map Ψ = J0.map (algebraMap A (AdicCompletion J0 A)) := by
    dsimp only [K, J0]
    rw [Ideal.map_span, Ideal.map_span]
    congr 1
    ext z
    simp only [Set.mem_image, Set.mem_range, Finset.mem_coe]
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i.val, i.property, (hΨ_X i).symm⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨MvPowerSeries.X ⟨a, ha⟩, ⟨⟨a, ha⟩, rfl⟩, hΨ_X ⟨a, ha⟩⟩
  have hJ0_complete : IsAdicComplete (J0.map (algebraMap A (AdicCompletion J0 A)))
      (AdicCompletion J0 A) := AdicCompletion.isAdicComplete_self J0 ⟨s, rfl⟩
  have hHaus : IsHausdorff (K.map Ψ) (AdicCompletion J0 A) := by
    rw [hKmap]
    exact hJ0_complete.toIsHausdorff
  have hModSurj : Function.Surjective ((Ideal.Quotient.mk (K.map Ψ)).comp Ψ) := by
    intro q
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalOneₐ J0 y)
    refine ⟨MvPowerSeries.C a, ?_⟩
    simp only [RingHom.coe_comp, Function.comp_apply, hΨ_C]
    rw [Ideal.Quotient.eq, hKmap, ← AdicCompletion.ker_evalOneₐ_eq_map J0 ⟨s, rfl⟩,
      RingHom.mem_ker, map_sub]
    change AdicCompletion.evalOneₐ J0 (algebraMap A (AdicCompletion J0 A) a) -
      AdicCompletion.evalOneₐ J0 y = 0
    simp [AdicCompletion.algebraMap_apply, AdicCompletion.evalOneₐ_of, ha]
  have hSurj : Function.Surjective Ψ :=
    surjective_of_mk_map_comp_surjective Ψ hModSurj
  exact isNoetherianRing_of_surjective (MvPowerSeries (↥s) A) (AdicCompletion J0 A) Ψ hSurj

end NoetherianCompletion

section QuotientAndKrull

theorem adicCompletion_quotient_equiv (R : Type*) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (I : Ideal R) (hI : I ≠ ⊤) [IsLocalRing (R ⧸ I)] :
    Nonempty ((AdicCompletion (maximalIdeal R) R ⧸
      I.map (algebraMap R (AdicCompletion (maximalIdeal R) R))) ≃+*
      AdicCompletion (maximalIdeal (R ⧸ I)) (R ⧸ I)) := by
  have hIle : I ≤ maximalIdeal R := IsLocalRing.le_maximalIdeal hI
  have hMaxMap : ((maximalIdeal R).map (Ideal.Quotient.mk I)).IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
      (by simpa using hIle)
  have hMaxEq : maximalIdeal (R ⧸ I) = (maximalIdeal R).map (Ideal.Quotient.mk I) :=
    (IsLocalRing.eq_maximalIdeal hMaxMap).symm
  have hpow : ∀ n : ℕ, maximalIdeal R ^ n ≤
      (maximalIdeal (R ⧸ I) ^ n).comap (Ideal.Quotient.mk I) := by
    intro n
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow, hMaxEq]
  let g : (n : ℕ) → AdicCompletion (maximalIdeal R) R →+*
      (R ⧸ I) ⧸ maximalIdeal (R ⧸ I) ^ n := fun n =>
    (quotMap (maximalIdeal R ^ n) (maximalIdeal (R ⧸ I) ^ n) (Ideal.Quotient.mk I) (hpow n)).comp
      (AdicCompletion.evalₐ (maximalIdeal R) n).toRingHom
  have hg_compat : ∀ {m n : ℕ} (hle : m ≤ n),
      (Ideal.Quotient.factorPow (maximalIdeal (R ⧸ I)) hle).comp (g n) = g m := by
    intro m n hle
    ext x
    obtain ⟨c, rfl⟩ := AdicCompletion.mk_surjective (maximalIdeal R) R x
    have hev : ∀ k, g k (AdicCompletion.mk (maximalIdeal R) R c) =
        Ideal.Quotient.mk (maximalIdeal (R ⧸ I) ^ k) (Ideal.Quotient.mk I (c.val k)) := by
      intro k
      change quotMap _ _ (Ideal.Quotient.mk I) (hpow k)
        (AdicCompletion.evalₐ (maximalIdeal R) k (AdicCompletion.mk (maximalIdeal R) R c)) = _
      rw [AdicCompletion.evalₐ_mk, quotMap_mk]
    simp only [RingHom.coe_comp, Function.comp_apply, hev, Ideal.Quotient.factorPow,
      Ideal.Quotient.factor_mk]
    have hcm : Ideal.Quotient.mk (maximalIdeal R ^ m) (c.val n) =
        Ideal.Quotient.mk (maximalIdeal R ^ m) (c.val m) :=
      AdicCompletion.Ideal.mk_eq_mk (maximalIdeal R) hle c
    rw [Ideal.Quotient.eq] at hcm ⊢
    rw [← map_sub]
    exact hpow m hcm
  let πHat : AdicCompletion (maximalIdeal R) R →+*
      AdicCompletion (maximalIdeal (R ⧸ I)) (R ⧸ I) :=
    AdicCompletion.liftRingHom (maximalIdeal (R ⧸ I)) g hg_compat
  have hsmul_eq : ∀ n : ℕ,
      (maximalIdeal R ^ n • (⊤ : Submodule R (R ⧸ I))).restrictScalars R =
      ((maximalIdeal (R ⧸ I) ^ n • (⊤ : Submodule (R ⧸ I) (R ⧸ I))).restrictScalars R) := by
    intro n
    ext q
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
    simp only [Submodule.restrictScalars_mem, Ideal.smul_top_eq_map]
    have hL : Ideal.map (algebraMap R (R ⧸ I)) (maximalIdeal R ^ n) = maximalIdeal (R ⧸ I) ^ n := by
      change Ideal.map (Ideal.Quotient.mk I) (maximalIdeal R ^ n) = _
      rw [Ideal.map_pow, hMaxEq]
    have hR : Ideal.map (algebraMap (R ⧸ I) (R ⧸ I)) (maximalIdeal (R ⧸ I) ^ n) =
        maximalIdeal (R ⧸ I) ^ n := Ideal.map_id _
    rw [hL, hR]
  have hSurj : Function.Surjective πHat := by
    intro y
    obtain ⟨b', rfl⟩ := AdicCompletion.mk_surjective (maximalIdeal (R ⧸ I)) (R ⧸ I) y
    let b : AdicCompletion.AdicCauchySequence (maximalIdeal R) (R ⧸ I) :=
      ⟨b'.val, fun {m n} hle => by
        have hp := b'.property hle
        rw [SModEq.sub_mem] at hp ⊢
        exact (congrArg (fun S : Submodule R (R ⧸ I) => b'.val m - b'.val n ∈ S)
          (hsmul_eq m)).mpr hp⟩
    obtain ⟨x, hx⟩ := AdicCompletion.map_surjective (maximalIdeal R) I.mkQ_surjective
      (AdicCompletion.mk (maximalIdeal R) (R ⧸ I) b)
    refine ⟨x, ?_⟩
    obtain ⟨c, rfl⟩ := AdicCompletion.mk_surjective (maximalIdeal R) R x
    apply AdicCompletion.ext_evalₐ
    intro n
    rw [AdicCompletion.evalₐ_liftRingHom, AdicCompletion.evalₐ_mk]
    have hcn : Submodule.Quotient.mk (p := (maximalIdeal R ^ n • ⊤ : Submodule R (R ⧸ I)))
        (I.mkQ (c n)) =
        Submodule.Quotient.mk (p := (maximalIdeal R ^ n • ⊤ : Submodule R (R ⧸ I))) (b n) := by
      have hcn0 := congrArg (fun u => u.val n) hx
      simpa [AdicCompletion.map_val_apply] using hcn0
    rw [Submodule.Quotient.eq] at hcn
    have hmemA : I.mkQ (c.val n) - b'.val n ∈
        (maximalIdeal (R ⧸ I) ^ n • (⊤ : Submodule (R ⧸ I) (R ⧸ I))) :=
      (congrArg (fun S : Submodule R (R ⧸ I) => I.mkQ (c.val n) - b'.val n ∈ S) (hsmul_eq n)).mp hcn
    have hgk : g n (AdicCompletion.mk (maximalIdeal R) R c) =
        Ideal.Quotient.mk (maximalIdeal (R ⧸ I) ^ n) (Ideal.Quotient.mk I (c.val n)) := by
      change quotMap _ _ (Ideal.Quotient.mk I) (hpow n)
        (AdicCompletion.evalₐ (maximalIdeal R) n (AdicCompletion.mk (maximalIdeal R) R c)) = _
      rw [AdicCompletion.evalₐ_mk, quotMap_mk]
    rw [hgk, Ideal.Quotient.eq]
    simpa using hmemA
  have hKer : RingHom.ker πHat = I.map (algebraMap R (AdicCompletion (maximalIdeal R) R)) := by
    apply le_antisymm
    · intro x hx
      rw [RingHom.mem_ker] at hx
      have hmap0 : AdicCompletion.map (maximalIdeal R) I.mkQ x = 0 := by
        obtain ⟨c, rfl⟩ := AdicCompletion.mk_surjective (maximalIdeal R) R x
        ext n
        have hgn : g n (AdicCompletion.mk (maximalIdeal R) R c) = 0 := by
          have := congrArg (AdicCompletion.evalₐ (maximalIdeal (R ⧸ I)) n) hx
          simpa [πHat] using this
        have hgk : g n (AdicCompletion.mk (maximalIdeal R) R c) =
            Ideal.Quotient.mk (maximalIdeal (R ⧸ I) ^ n) (Ideal.Quotient.mk I (c.val n)) := by
          change quotMap _ _ (Ideal.Quotient.mk I) (hpow n)
            (AdicCompletion.evalₐ (maximalIdeal R) n (AdicCompletion.mk (maximalIdeal R) R c)) = _
          rw [AdicCompletion.evalₐ_mk, quotMap_mk]
        rw [hgk, Ideal.Quotient.eq_zero_iff_mem] at hgn
        have hmemA : I.mkQ (c.val n) ∈
            (maximalIdeal (R ⧸ I) ^ n • (⊤ : Submodule (R ⧸ I) (R ⧸ I))) := by
          simpa using hgn
        have hmemR : I.mkQ (c.val n) ∈ (maximalIdeal R ^ n • (⊤ : Submodule R (R ⧸ I))) :=
          (congrArg (fun S : Submodule R (R ⧸ I) => I.mkQ (c.val n) ∈ S) (hsmul_eq n)).mpr hmemA
        simpa [AdicCompletion.map_val_apply, Submodule.Quotient.mk_eq_zero] using hmemR
      obtain ⟨w, rfl⟩ := (AdicCompletion.map_exact I.injective_subtype
        (LinearMap.exact_subtype_mkQ I) I.mkQ_surjective x).mp hmap0
      let eI := AdicCompletion.ofTensorProductEquivOfFiniteNoetherian (maximalIdeal R) I
      let eR := AdicCompletion.ofTensorProductEquivOfFiniteNoetherian (maximalIdeal R) R
      obtain ⟨t, rfl⟩ : ∃ t, eI t = w := ⟨eI.symm w, eI.apply_symm_apply w⟩
      have hcompat := congrArg (fun L => eR (L t))
        (AdicCompletion.tensor_map_id_left_eq_map (maximalIdeal R) I.subtype)
      simp only [eR, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.apply_symm_apply] at hcompat
      let idHat : AdicCompletion (maximalIdeal R) R →ₗ[AdicCompletion (maximalIdeal R) R]
          AdicCompletion (maximalIdeal R) R := LinearMap.id
      change eR (AlgebraTensorModule.map idHat I.subtype t) =
        AdicCompletion.map (maximalIdeal R) I.subtype (eI t) at hcompat
      rw [← hcompat]
      have hmem_t : ∀ s : AdicCompletion (maximalIdeal R) R ⊗[R] I,
          eR (AlgebraTensorModule.map idHat I.subtype s) ∈
            I.map (algebraMap R (AdicCompletion (maximalIdeal R) R)) := by
        intro s
        induction s using TensorProduct.induction_on with
        | zero => simp
        | tmul u v =>
          have hval : eR (AlgebraTensorModule.map idHat I.subtype (u ⊗ₜ[R] v)) =
              u * algebraMap R (AdicCompletion (maximalIdeal R) R) v.val := by
            have h1 : eR (AlgebraTensorModule.map idHat I.subtype (u ⊗ₜ[R] v)) =
                u • AdicCompletion.of (maximalIdeal R) R v.val :=
              AdicCompletion.ofTensorProduct_tmul (maximalIdeal R) R u v.val
            rw [h1, AdicCompletion.algebraMap_apply]
            exact Subtype.ext (funext fun n => smul_eq_mul (u.val n) _)
          rw [hval]
          exact Ideal.mul_mem_left _ u (Ideal.mem_map_of_mem _ v.property)
        | add t1 t2 ih1 ih2 =>
          rw [map_add, map_add]
          exact Ideal.add_mem _ ih1 ih2
      exact hmem_t t
    · rw [Ideal.map_le_iff_le_comap]
      intro r hr
      rw [Ideal.mem_comap, RingHom.mem_ker]
      apply AdicCompletion.ext_evalₐ
      intro n
      rw [AdicCompletion.evalₐ_liftRingHom, map_zero]
      change quotMap _ _ (Ideal.Quotient.mk I) (hpow n)
        (AdicCompletion.evalₐ (maximalIdeal R) n (algebraMap R (AdicCompletion (maximalIdeal R) R) r)) = 0
      rw [AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_of, quotMap_mk]
      simp [Ideal.Quotient.eq_zero_iff_mem.mpr hr]
  exact ⟨(Ideal.quotEquivOfEq hKer.symm).trans (RingHom.quotientKerEquivOfSurjective hSurj)⟩

private lemma bot_height_eq_zero_of_isMaximal {B : Type*} [CommRing B]
    (m : Ideal B) [hm : m.IsMaximal] :
    ((m.map (Ideal.Quotient.mk m)).height) = 0 := by
  have hbot : m.map (Ideal.Quotient.mk m) = ⊥ := by
    rw [Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
  rw [hbot]
  have hDom : IsDomain (B ⧸ m) := Ideal.Quotient.isDomain m
  have hPrimeBot : (⊥ : Ideal (B ⧸ m)).IsPrime := Ideal.isPrime_bot
  rw [(⟨⊥, hPrimeBot⟩ : PrimeSpectrum (B ⧸ m)).height_eq_orderHeight]
  rw [Order.height_eq_zero]
  intro q _
  exact bot_le

theorem ringKrullDim_adicCompletion_eq (A : Type*) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] :
    ringKrullDim (AdicCompletion (maximalIdeal A) A) = ringKrullDim A := by
  let B := AdicCompletion (maximalIdeal A) A
  have hNoethB : IsNoetherianRing B := adicCompletion_isNoetherianRing A (maximalIdeal A)
  have hOver : (maximalIdeal B).LiesOver (maximalIdeal A) :=
    ⟨(IsLocalRing.maximalIdeal_comap (algebraMap A B)).symm⟩
  have hHeight := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown
    (maximalIdeal A) (maximalIdeal B)
  have hMapEq : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B :=
    (AdicCompletion.maximalIdeal_eq_map (R := A)).symm
  rw [hMapEq, bot_height_eq_zero_of_isMaximal (maximalIdeal B), add_zero] at hHeight
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := B),
    ← IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := A), hHeight]

end QuotientAndKrull

end SerreCompletionDim

theorem OMA.solution :
    OMA.R_SerreMultiplicityConjectures_supportDim_add_supportDim_le_ringKrullDim_R1.H1 := by
  intro R _ _ _
  refine ⟨SerreCompletionDim.adicCompletion_isNoetherianRing R (IsLocalRing.maximalIdeal R), ?_⟩
  intro I
  by_cases hI : I = ⊤
  · subst hI
    rw [Ideal.map_top]
    have hSub1 : Subsingleton (AdicCompletion (IsLocalRing.maximalIdeal R) R ⧸
        (⊤ : Ideal (AdicCompletion (IsLocalRing.maximalIdeal R) R))) :=
      Ideal.Quotient.subsingleton_iff.mpr rfl
    have hSub2 : Subsingleton (R ⧸ (⊤ : Ideal R)) :=
      Ideal.Quotient.subsingleton_iff.mpr rfl
    rw [ringKrullDim_eq_bot_of_subsingleton, ringKrullDim_eq_bot_of_subsingleton]
  · have hNontriv : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
    have hLocalQ : IsLocalRing (R ⧸ I) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    obtain ⟨e⟩ := SerreCompletionDim.adicCompletion_quotient_equiv R I hI
    rw [ringKrullDim_eq_of_ringEquiv e, SerreCompletionDim.ringKrullDim_adicCompletion_eq (R ⧸ I)]
