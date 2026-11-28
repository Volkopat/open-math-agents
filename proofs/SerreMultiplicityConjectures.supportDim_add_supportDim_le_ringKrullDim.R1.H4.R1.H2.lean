import OMAReductions.R_SerreMultiplicityConjectures_supportDim_add_supportDim_le_ringKrullDim_R1_H4_R1
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.LocalRing.Length
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Homological change-of-rings sequence along a regular hypersurface

Constructs the Gysin / change-of-rings exact sequence between Tor over a regular
local ring `S` and Tor over its regular hypersurface quotient `R = S / (g)` when
`g` lies in both ideals `P` and `Q`.

The regular-domain, base-change projective resolution, and Tor long-exact-sequence
infrastructure is adapted under Apache-2.0 from the merged proof
`proofs/SerreMultiplicityConjectures.supportDim_add_supportDim_le_ringKrullDim.R1.H4.lean`.
-/

open IsLocalRing Module Ideal CategoryTheory Limits MonoidalCategory TensorProduct

namespace SerreH2Proof

section RegularLocal

lemma isRegularLocalRing_quotient_span_singleton
    {R : Type*} [CommRing R] [IsRegularLocalRing R]
    {n : ℕ} (hdim : (maximalIdeal R).spanFinrank = n + 1)
    {x : R} (hx : x ∈ maximalIdeal R) (hx2 : x ∉ maximalIdeal R ^ 2) :
    let I := Ideal.span ({x} : Set R)
    let _ : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr
      (fun h => (maximalIdeal.isMaximal R).ne_top
        (top_unique (h ▸ Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hx))))
    let _ : IsLocalRing (R ⧸ I) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    IsRegularLocalRing (R ⧸ I) ∧ (maximalIdeal (R ⧸ I)).spanFinrank = n := by
  classical
  intro I _ _
  have hI_le : I ≤ maximalIdeal R := Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hx)
  have hm_map : (maximalIdeal R).map (Ideal.Quotient.mk I) = maximalIdeal (R ⧸ I) :=
    IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hkrull_R : ringKrullDim R = (n + 1 : ℕ) := by
    rw [← IsRegularLocalRing.spanFinrank_maximalIdeal (R := R), hdim]
  have hspan_le_n : (maximalIdeal (R ⧸ I)).spanFinrank ≤ n := by
    let k := ResidueField R
    have hfinrank : Module.finrank k (CotangentSpace R) = n + 1 := by
      have h1 := (IsRegularLocalRing.iff_finrank_cotangentSpace R).mp inferInstance
      rw [hkrull_R] at h1
      exact_mod_cast h1
    let v : CotangentSpace R := (maximalIdeal R).toCotangent ⟨x, hx⟩
    have hv : v ≠ 0 := by
      intro h0
      rw [Ideal.toCotangent_eq_zero] at h0
      exact hx2 (by simpa [pow_two] using h0)
    let L : Submodule k (CotangentSpace R) := Submodule.span k {v}
    have hL_rank : Module.finrank k L = 1 := finrank_span_singleton hv
    let Q := CotangentSpace R ⧸ L
    have hQ_rank : Module.finrank k Q = n := by
      have hadd := Submodule.finrank_quotient_add_finrank L
      dsimp only [Q]
      omega
    let b := Module.finBasisOfFinrankEq k Q hQ_rank
    have hlift (i : Fin n) : ∃ y : maximalIdeal R,
        L.mkQ ((maximalIdeal R).toCotangent y) = b i := by
      obtain ⟨w, hw⟩ := Submodule.mkQ_surjective L (b i)
      obtain ⟨y, hy⟩ := Ideal.toCotangent_surjective (maximalIdeal R) w
      exact ⟨y, by rw [hy, hw]⟩
    choose y hy using hlift
    let yf : Fin n → R := fun i => (y i : R)
    let s : Set (maximalIdeal R) := insert ⟨x, hx⟩ (Set.range y)
    have hspan_cot : Submodule.span k ((maximalIdeal R).toCotangent '' s) = ⊤ := by
      rw [eq_top_iff]
      intro w _
      have hbw : L.mkQ w ∈ Submodule.span k (Set.range b) := by
        rw [b.span_eq]; exact Submodule.mem_top
      rw [Submodule.mem_span_range_iff_exists_fun] at hbw
      obtain ⟨c, hc⟩ := hbw
      have hdiff : w - ∑ i : Fin n, c i • (maximalIdeal R).toCotangent (y i) ∈ L := by
        rw [← Submodule.ker_mkQ L, LinearMap.mem_ker, map_sub, map_sum]
        simp_rw [map_smul, hy]
        rw [hc, sub_self]
      rw [Submodule.mem_span_singleton] at hdiff
      obtain ⟨a, ha⟩ := hdiff
      have hw_eq : w = a • v + ∑ i : Fin n, c i • (maximalIdeal R).toCotangent (y i) := by
        rw [ha]; abel
      rw [hw_eq]
      refine Submodule.add_mem _ ?_ ?_
      · exact Submodule.smul_mem _ a (Submodule.subset_span ⟨⟨x, hx⟩, Set.mem_insert _ _, rfl⟩)
      · exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ (c i)
          (Submodule.subset_span ⟨y i, Set.mem_insert_of_mem _ ⟨i, rfl⟩, rfl⟩)
    have hspan_top : Submodule.span R s = ⊤ :=
      (CotangentSpace.span_image_eq_top_iff).mp hspan_cot
    have hm_eq : maximalIdeal R = Ideal.span (insert x (Set.range yf)) := by
      have hmap := congrArg (Submodule.map (maximalIdeal R).subtype) hspan_top
      rw [Submodule.map_top, Submodule.range_subtype, Submodule.map_span] at hmap
      convert hmap.symm using 2
      ext z
      simp [s, yf, eq_comm]
    have hmq_eq : maximalIdeal (R ⧸ I) =
        Ideal.span (Set.range (fun i : Fin n => Ideal.Quotient.mk I (yf i))) := by
      rw [← hm_map, hm_eq, Ideal.map_span]
      apply le_antisymm
      · rw [Ideal.span_le]
        rintro _ ⟨z, hz, rfl⟩
        rcases hz with rfl | ⟨i, rfl⟩
        · have hx0 : Ideal.Quotient.mk I z = 0 :=
            Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
          rw [hx0]
          exact Submodule.zero_mem _
        · exact Ideal.subset_span ⟨i, rfl⟩
      · rw [Ideal.span_le]
        rintro _ ⟨i, rfl⟩
        exact Ideal.subset_span ⟨yf i, Or.inr ⟨i, rfl⟩, rfl⟩
    rw [hmq_eq]
    calc (Ideal.span (Set.range (fun i : Fin n => Ideal.Quotient.mk I (yf i)))).spanFinrank
        ≤ (Set.range (fun i : Fin n => Ideal.Quotient.mk I (yf i))).ncard :=
          Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_range _)
      _ ≤ n := by
          have h1 : (Set.range (fun i : Fin n => Ideal.Quotient.mk I (yf i))) =
              ((Finset.univ.image (fun i : Fin n => Ideal.Quotient.mk I (yf i))) : Set (R ⧸ I)) := by
            ext z; simp
          rw [h1, Set.ncard_coe_finset]
          exact Finset.card_image_le.trans (by simp)
  have hI_sf : I.spanFinrank ≤ 1 := by
    simpa [I] using Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_singleton x)
  have hI_jac : I ≤ Ring.jacobson R := by
    rw [Ring.jacobson_eq_sInf_isMaximal]
    exact le_sInf fun m hm => (IsLocalRing.eq_maximalIdeal hm).symm ▸ hI_le
  have hkd := ringKrullDim_le_ringKrullDim_quotient_add_spanFinrank I hI_jac
  have hkd_ge : (n : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ I) := by
    rw [hkrull_R] at hkd
    have h1 : (I.spanFinrank : WithBot ℕ∞) ≤ 1 := by exact_mod_cast hI_sf
    have h2 : ((n + 1 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ I) + 1 :=
      hkd.trans (add_le_add le_rfl h1)
    cases hd : ringKrullDim (R ⧸ I) with
    | bot =>
      rw [hd] at h2
      simp at h2
    | coe a =>
      rw [hd] at h2
      have h2' : ((n + 1 : ℕ) : ℕ∞) ≤ a + 1 := WithBot.coe_le_coe.mp h2
      have ha : (n : ℕ∞) ≤ a := by
        cases a with
        | top => exact le_top
        | coe m =>
          norm_cast at h2' ⊢
          omega
      exact WithBot.coe_le_coe.mpr ha
  have hreg : IsRegularLocalRing (R ⧸ I) :=
    IsRegularLocalRing.of_spanFinrank_maximalIdeal_le (R ⧸ I)
      ((Nat.cast_le.mpr hspan_le_n).trans hkd_ge)
  have hkd_le : ringKrullDim (R ⧸ I) ≤ (n : WithBot ℕ∞) := by
    rw [← IsRegularLocalRing.spanFinrank_maximalIdeal (R := R ⧸ I)]
    exact_mod_cast hspan_le_n
  have heq : ((maximalIdeal (R ⧸ I)).spanFinrank : WithBot ℕ∞) = (n : WithBot ℕ∞) := by
    rw [IsRegularLocalRing.spanFinrank_maximalIdeal (R := R ⧸ I)]
    exact le_antisymm hkd_le hkd_ge
  exact ⟨hreg, by exact_mod_cast heq⟩

lemma maximalIdeal_not_le_sq {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {n : ℕ} (hdim : (maximalIdeal R).spanFinrank = n + 1) :
    ¬ (maximalIdeal R ≤ maximalIdeal R ^ 2) := by
  intro hle
  have hm_bot : maximalIdeal R = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R) (maximalIdeal R)
      (IsNoetherian.noetherian _)
      (by simpa [smul_eq_mul, pow_two] using hle)
      (IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal R) bot_ne_top).ge
  have h0 : (maximalIdeal R).spanFinrank = 0 := by simp [hm_bot]
  omega

/-- Every regular local ring is an integral domain. -/
theorem isDomain_of_isRegularLocalRing_aux (d : ℕ) :
    ∀ (R : Type*) [CommRing R] [IsRegularLocalRing R],
      (maximalIdeal R).spanFinrank = d → IsDomain R := by
  induction d with
  | zero =>
    intro R _ _ h0
    have hm_bot : maximalIdeal R = ⊥ := by
      have h1 : Module.finrank (ResidueField R) (CotangentSpace R) = 0 := by
        have h2 := (IsRegularLocalRing.iff_finrank_cotangentSpace R).mp inferInstance
        rw [← IsRegularLocalRing.spanFinrank_maximalIdeal (R := R), h0] at h2
        exact_mod_cast h2
      have hsub : Subsingleton (CotangentSpace R) :=
        Module.finrank_zero_iff.mp h1
      have hfield : IsField R := subsingleton_cotangentSpace_iff.mp hsub
      exact (IsLocalRing.isField_iff_maximalIdeal_eq).mp hfield
    let _ : Field R := (IsLocalRing.isField_iff_maximalIdeal_eq.mpr hm_bot).toField
    infer_instance
  | succ n ih =>
    intro R _ _ hdim
    have hm_ne_sq := maximalIdeal_not_le_sq hdim
    have hm_not_min (p : Ideal R) (hp : p ∈ minimalPrimes R) : ¬ (maximalIdeal R ≤ p) := by
      intro hle
      have hp_prime : p.IsPrime := hp.1.1
      have hp_eq : p = maximalIdeal R :=
        le_antisymm (IsLocalRing.le_maximalIdeal hp_prime.ne_top) hle
      have hkd0 : Ring.KrullDimLE 0 R := by
        rw [Ring.krullDimLE_zero_iff]
        intro q hq
        have hqp : q ≤ p := hp_eq ▸ IsLocalRing.le_maximalIdeal hq.ne_top
        have heq : q = p := le_antisymm hqp (hp.2 ⟨hq, bot_le⟩ hqp)
        rw [heq, hp_eq]
        exact maximalIdeal.isMaximal R
      have hle0 : ringKrullDim R ≤ 0 := Ring.krullDimLE_iff.mp hkd0
      rw [← IsRegularLocalRing.spanFinrank_maximalIdeal (R := R), hdim] at hle0
      have : (n + 1 : ℕ) ≤ 0 := by exact_mod_cast hle0
      omega
    have hfin : (minimalPrimes R).Finite := minimalPrimes.finite_of_isNoetherianRing R
    have hex : ∃ x ∈ maximalIdeal R, x ∉ maximalIdeal R ^ 2 ∧ ∀ p ∈ minimalPrimes R, x ∉ p := by
      by_contra! hall
      have hsub' : (maximalIdeal R : Set R) ⊆
          ⋃ I ∈ insert (maximalIdeal R ^ 2) (minimalPrimes R), (I : Set R) := by
        intro x hx
        by_cases hx2 : x ∈ maximalIdeal R ^ 2
        · exact Set.mem_biUnion (Set.mem_insert _ _) hx2
        · obtain ⟨p, hp, hxp⟩ := hall x hx hx2
          exact Set.mem_biUnion (Set.mem_insert_of_mem _ hp) hxp
      have havoid := Ideal.subset_union_prime_finite (I := maximalIdeal R)
        (hfin.insert (maximalIdeal R ^ 2))
        (maximalIdeal R ^ 2) (maximalIdeal R ^ 2)
        (fun I hI hne1 _ => by
          rcases Set.mem_insert_iff.mp hI with rfl | hmin
          · exact (hne1 rfl).elim
          · exact hmin.1.1)
      obtain ⟨I, hI, hle⟩ := havoid.mp hsub'
      rcases Set.mem_insert_iff.mp hI with rfl | hmin
      · exact hm_ne_sq hle
      · exact hm_not_min I hmin hle
    obtain ⟨x, hx, hx2, hx_min⟩ := hex
    let I := Ideal.span ({x} : Set R)
    have hI_le : I ≤ maximalIdeal R := Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hx)
    have hI_ne : I ≠ ⊤ := fun h => (maximalIdeal.isMaximal R).ne_top (top_unique (h ▸ hI_le))
    let _ : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI_ne
    let _ : IsLocalRing (R ⧸ I) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    obtain ⟨hreg_q, hdim_q⟩ := isRegularLocalRing_quotient_span_singleton hdim hx hx2
    have hdom_q : IsDomain (R ⧸ I) := ih (R ⧸ I) hdim_q
    have hI_prime : I.IsPrime := (Ideal.Quotient.isDomain_iff_prime I).mp hdom_q
    obtain ⟨p, hp_min, hp_le⟩ := Ideal.exists_minimalPrimes_le (I := ⊥) (J := I) bot_le
    have hp_prime : p.IsPrime := hp_min.1.1
    have hp_le_mul : p ≤ maximalIdeal R • p := by
      intro y hy
      have hyI : y ∈ I := hp_le hy
      rw [Ideal.mem_span_singleton] at hyI
      obtain ⟨r, rfl⟩ := hyI
      have hr : r ∈ p := (hp_prime.mem_or_mem hy).resolve_left (hx_min p hp_min)
      simpa [smul_eq_mul] using Submodule.smul_mem_smul hx hr
    have hp_bot : p = ⊥ :=
      Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R) p
        (IsNoetherian.noetherian p)
        hp_le_mul
        (IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal R) bot_ne_top).ge
    have hbot_prime : (⊥ : Ideal R).IsPrime := hp_bot ▸ hp_prime
    let _ : NoZeroDivisors R := ⟨fun {a b} hab => by
      have hmem : a * b ∈ (⊥ : Ideal R) := by simpa using hab
      rcases hbot_prime.mem_or_mem hmem with ha | hb
      · exact Or.inl (by simpa using ha)
      · exact Or.inr (by simpa using hb)⟩
    exact NoZeroDivisors.to_isDomain R

theorem isDomain_of_isRegularLocalRing (R : Type*) [CommRing R] [IsRegularLocalRing R] :
    IsDomain R :=
  isDomain_of_isRegularLocalRing_aux (maximalIdeal R).spanFinrank R rfl


end RegularLocal

/-- Helper map `(R ⧸ I) ⊗[R] M →ₗ[R] M ⧸ (I • ⊤)` detecting membership in `I • ⊤`. -/
lemma mem_ideal_smul_top_of_one_tmul_eq_zero {R : Type} [CommRing R] (I : Ideal R)
    {M : Type} [AddCommGroup M] [Module R M] {m : M}
    (h0 : (1 : R ⧸ I) ⊗ₜ[R] m = 0) : m ∈ I • (⊤ : Submodule R M) := by
  let f₀ : R →ₗ[R] M →ₗ[R] (M ⧸ (I • (⊤ : Submodule R M))) :=
    { toFun := fun a =>
        { toFun := fun z => Submodule.Quotient.mk (a • z)
          map_add' := fun z₁ z₂ => by simp [smul_add]
          map_smul' := fun s z => by simp only [RingHom.id_apply, smul_comm a s z]; rfl }
      map_add' := fun a₁ a₂ => by ext z; simp [add_smul]
      map_smul' := fun s a => by
        ext z
        simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, smul_eq_mul,
          mul_smul, RingHom.id_apply]
        rfl }
  let f : (R ⧸ I) →ₗ[R] M →ₗ[R] (M ⧸ (I • (⊤ : Submodule R M))) :=
    Submodule.liftQ I f₀ (fun a ha => by
      rw [LinearMap.mem_ker]
      ext z
      simp only [f₀, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.zero_apply]
      exact (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.smul_mem_smul ha Submodule.mem_top))
  have hf0 := congrArg (TensorProduct.lift f) h0
  simp only [TensorProduct.lift.tmul, map_zero] at hf0
  have h1 : f (1 : R ⧸ I) m = Submodule.Quotient.mk m := by
    change f (Submodule.Quotient.mk (1 : R)) m = _
    rw [Submodule.liftQ_apply]
    simp [f₀]
  rw [h1] at hf0
  exact (Submodule.Quotient.mk_eq_zero _).mp hf0

lemma exists_one_tmul_eq {R : Type} [CommRing R] (I : Ideal R)
    {M : Type} [AddCommGroup M] [Module R M] (w : (R ⧸ I) ⊗[R] M) :
    ∃ z : M, (1 : R ⧸ I) ⊗ₜ[R] z = w := by
  induction w using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul c z =>
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
    refine ⟨a • z, ?_⟩
    rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
    rfl
  | add w₁ w₂ ih₁ ih₂ =>
    obtain ⟨z₁, hz₁⟩ := ih₁
    obtain ⟨z₂, hz₂⟩ := ih₂
    exact ⟨z₁ + z₂, by rw [TensorProduct.tmul_add, hz₁, hz₂]⟩


section TorLES

/-- Abbreviation for `Tor_i^R(M, N)` in `ModuleCat.{0} R`. -/
noncomputable abbrev torMod (R : Type) [CommRing R]
    (M N : Type) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (i : ℕ) : ModuleCat.{0} R :=
  ((Tor (ModuleCat.{0} R) i).obj (ModuleCat.of R M)).obj (ModuleCat.of R N)

/-- Functorial map on `Tor_i^R(M, -)` induced by a linear map `f : A →ₗ[R] B`. -/
noncomputable def torMap {R : Type} [CommRing R]
    (M : Type) [AddCommGroup M] [Module R M]
    {A B : Type} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    (f : A →ₗ[R] B) (i : ℕ) :
    torMod R M A i →ₗ[R] torMod R M B i :=
  (((Tor (ModuleCat.{0} R) i).obj (ModuleCat.of R M)).map (ModuleCat.ofHom f)).hom

/-- `Tor_0^R(M, N) ≃ₗ[R] M ⊗[R] N`. -/
noncomputable def torZeroEquiv (R : Type) [CommRing R]
    (M N : Type) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] :
    torMod R M N 0 ≃ₗ[R] (M ⊗[R] N) :=
  (((tensoringLeft (ModuleCat.{0} R)).obj (ModuleCat.of R M)).leftDerivedZeroIsoSelf.app
    (ModuleCat.of R N)).toLinearEquiv

lemma torZeroEquiv_naturality {R : Type} [CommRing R]
    (M : Type) [AddCommGroup M] [Module R M]
    {A B : Type} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    (f : A →ₗ[R] B) (x : torMod R M A 0) :
    torZeroEquiv R M B (torMap M f 0 x) = LinearMap.lTensor M f (torZeroEquiv R M A x) := by
  have hnat := (((tensoringLeft (ModuleCat.{0} R)).obj
    (ModuleCat.of R M)).leftDerivedZeroIsoSelf.hom.naturality (ModuleCat.ofHom f))
  exact congrArg (fun φ : torMod R M A 0 ⟶ ModuleCat.of R (M ⊗[R] B) => φ.hom x) hnat

lemma tor_succ_subsingleton_of_projective {R : Type} [CommRing R]
    (M N : Type) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Projective R N] (i : ℕ) :
    Subsingleton (torMod R M N (i + 1)) :=
  ModuleCat.isZero_iff_subsingleton.mp
    (isZero_Tor_succ_of_projective (ModuleCat.{0} R) (ModuleCat.of R M) (ModuleCat.of R N) i)

/-- Build a `ProjectiveResolution` from a projective chain complex whose `H_0` is `B` via `ε`
and `H_{n+1} = 0`. -/
noncomputable def projectiveResolutionOfExact {R : Type} [CommRing R]
    (B : Type) [AddCommGroup B] [Module R B]
    (K : ChainComplex (ModuleCat.{0} R) ℕ)
    (hproj : ∀ n, Module.Projective R (K.X n))
    (ε : (K.X 0) →ₗ[R] B)
    (hε_surj : Function.Surjective ε)
    (hε_comp : ∀ x : K.X 1, ε ((K.d 1 0).hom x) = 0)
    (hε_exact : ∀ x : K.X 0, ε x = 0 → ∃ y : K.X 1, (K.d 1 0).hom y = x)
    (hexact : ∀ n : ℕ, ∀ x : K.X (n + 1), (K.d (n + 1) n).hom x = 0 →
      ∃ y : K.X (n + 2), (K.d (n + 2) (n + 1)).hom y = x) :
    ProjectiveResolution (ModuleCat.of R B) := by
  let π : K ⟶ (ChainComplex.single₀ (ModuleCat.{0} R)).obj (ModuleCat.of R B) :=
    (ChainComplex.toSingle₀Equiv K (ModuleCat.of R B)).symm
      ⟨ModuleCat.ofHom ε, by ext x; exact hε_comp x⟩
  have hπ0 : (π.f 0).hom = ε := by
    change ((ChainComplex.toSingle₀Equiv K (ModuleCat.of R B)).symm
      ⟨ModuleCat.ofHom ε, _⟩ |>.f 0).hom = ε
    rw [ChainComplex.toSingle₀Equiv_symm_apply_f_zero]
    rfl
  have hq : QuasiIso π := by
    rw [quasiIso_iff]
    intro n
    cases n with
    | zero =>
      rw [quasiIsoAt_iff_isIso_homologyMap]
      -- In degree 0, both K.sc 0 and single₀.sc 0 have g = 0, so homologyι is an iso to opcycles!
      have hK_g0 : (K.sc 0).g = 0 := K.shape 0 _ (by simp)
      have hS_g0 : (((ChainComplex.single₀ (ModuleCat.{0} R)).obj (ModuleCat.of R B)).sc 0).g = 0 :=
        ((ChainComplex.single₀ (ModuleCat.{0} R)).obj (ModuleCat.of R B)).shape 0 _ (by simp)
      have _ : IsIso (K.homologyι 0) := ShortComplex.isIso_homologyι (K.sc 0) hK_g0
      have _ : IsIso (((ChainComplex.single₀ (ModuleCat.{0} R)).obj (ModuleCat.of R B)).homologyι 0) :=
        ShortComplex.isIso_homologyι _ hS_g0
      have hcomm : (HomologicalComplex.homologyMap π 0 ≫
          ((ChainComplex.single₀ (ModuleCat.{0} R)).obj (ModuleCat.of R B)).homologyι 0) =
          (K.homologyι 0 ≫ HomologicalComplex.opcyclesMap π 0) :=
        HomologicalComplex.homologyι_naturality π 0
      have hop_bij : Function.Bijective (HomologicalComplex.opcyclesMap π 0).hom := by
        constructor
        · intro u v huv
          have hp_surj : Function.Surjective (K.pOpcycles 0) :=
            (ModuleCat.epi_iff_surjective (K.pOpcycles 0)).mp inferInstance
          obtain ⟨x, rfl⟩ := hp_surj u
          obtain ⟨y, rfl⟩ := hp_surj v
          have hsub : HomologicalComplex.opcyclesMap π 0 (K.pOpcycles 0 (x - y)) = 0 := by
            change (HomologicalComplex.opcyclesMap π 0).hom ((K.pOpcycles 0).hom (x - y)) = 0
            rw [map_sub, map_sub, huv, sub_self]
          have hnat : (HomologicalComplex.opcyclesMap π 0).hom ((K.pOpcycles 0).hom (x - y)) =
              (((ChainComplex.single₀ (ModuleCat.{0} R)).obj (ModuleCat.of R B)).pOpcycles 0).hom
                ((π.f 0).hom (x - y)) :=
            congrArg (fun φ : K.X 0 ⟶
              ((ChainComplex.single₀ (ModuleCat.{0} R)).obj (ModuleCat.of R B)).opcycles 0 =>
                φ.hom (x - y))
              (ShortComplex.p_opcyclesMap ((HomologicalComplex.shortComplexFunctor _ _ 0).map π))
          rw [hnat] at hsub
          have hmem := (ShortComplex.moduleCat_pOpcycles_eq_zero_iff _ _).mp hsub
          have hSf0 : (((ChainComplex.single₀ (ModuleCat.{0} R)).obj (ModuleCat.of R B)).sc 0).f = 0 := by
            simp [HomologicalComplex.sc]; rfl
          obtain ⟨w, hw⟩ := hmem
          have hε0 : ε (x - y) = 0 := by
            rw [← hπ0]
            have hw0 : ((((ChainComplex.single₀ (ModuleCat.{0} R)).obj (ModuleCat.of R B)).sc 0).f).hom w = 0 := by
              rw [hSf0]; rfl
            exact hw.symm.trans hw0
          obtain ⟨z, hz⟩ := hε_exact (x - y) hε0
          have h0 : (K.pOpcycles 0).hom (x - y) = 0 := by
            rw [← hz]
            exact congrArg (fun φ : K.X 1 ⟶ K.opcycles 0 => φ.hom z) (K.d_pOpcycles 1 0)
          rw [map_sub] at h0
          exact sub_eq_zero.mp h0
        · intro w
          have hpS_surj : Function.Surjective
              (((ChainComplex.single₀ (ModuleCat.{0} R)).obj (ModuleCat.of R B)).pOpcycles 0) :=
            (ModuleCat.epi_iff_surjective _).mp inferInstance
          obtain ⟨b, rfl⟩ := hpS_surj w
          obtain ⟨x, hx⟩ := hε_surj b
          refine ⟨K.pOpcycles 0 x, ?_⟩
          have hnat : (HomologicalComplex.opcyclesMap π 0).hom ((K.pOpcycles 0).hom x) =
              (((ChainComplex.single₀ (ModuleCat.{0} R)).obj (ModuleCat.of R B)).pOpcycles 0).hom
                ((π.f 0).hom x) :=
            congrArg (fun φ : K.X 0 ⟶
              ((ChainComplex.single₀ (ModuleCat.{0} R)).obj (ModuleCat.of R B)).opcycles 0 =>
                φ.hom x)
              (ShortComplex.p_opcyclesMap ((HomologicalComplex.shortComplexFunctor _ _ 0).map π))
          change (HomologicalComplex.opcyclesMap π 0).hom ((K.pOpcycles 0).hom x) = _
          rw [hnat]
          have hxb : (π.f 0).hom x = b := by
            have h1 : (π.f 0).hom x = ε x := LinearMap.congr_fun hπ0 x
            exact h1.trans hx
          exact congrArg
            (((ChainComplex.single₀ (ModuleCat.{0} R)).obj (ModuleCat.of R B)).pOpcycles 0).hom hxb
      have hop_iso : IsIso (HomologicalComplex.opcyclesMap π 0) :=
        ⟨ModuleCat.ofHom (LinearEquiv.ofBijective _ hop_bij).symm.toLinearMap,
          by ext u; exact (LinearEquiv.ofBijective _ hop_bij).left_inv u,
          by ext v; exact (LinearEquiv.ofBijective _ hop_bij).right_inv v⟩
      have hmul : HomologicalComplex.homologyMap π 0 =
          K.homologyι 0 ≫ HomologicalComplex.opcyclesMap π 0 ≫
            inv (((ChainComplex.single₀ (ModuleCat.{0} R)).obj (ModuleCat.of R B)).homologyι 0) := by
        rw [← Category.assoc, ← hcomm, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
      rw [hmul]
      infer_instance
    | succ m =>
      rw [quasiIsoAt_iff_exactAt' π (m + 1) (ChainComplex.exactAt_succ_single_obj _ _)]
      rw [HomologicalComplex.exactAt_iff' K (m + 2) (m + 1) m (by simp) (by simp)]
      rw [ShortComplex.moduleCat_exact_iff]
      exact hexact m
  exact
    { complex := K
      projective := fun n => by
        let _ := hproj n
        infer_instance
      π := π
      quasiIso := hq }

/-- Exactness of `torMap` and connecting homomorphism for a short exact sequence `0 → A → B → C → 0`. -/
lemma horseshoe_tor_les {R : Type} [CommRing R]
    (M : Type) [AddCommGroup M] [Module R M]
    {A B C : Type} [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
    (i : A →ₗ[R] B) (p : B →ₗ[R] C)
    (hi : Function.Injective i) (hp : Function.Surjective p)
    (hip : LinearMap.range i = LinearMap.ker p) :
    ∃ δ : ∀ n : ℕ, torMod R M C (n + 1) →ₗ[R] torMod R M A n,
      (∀ n, Function.Exact (δ n) (torMap M i n)) ∧
      (∀ n, Function.Exact (torMap M i n) (torMap M p n)) ∧
      (∀ n, Function.Exact (torMap M p (n + 1)) (δ n)) := by
  let PA : ProjectiveResolution (ModuleCat.of R A) := projectiveResolution (ModuleCat.of R A)
  let PC : ProjectiveResolution (ModuleCat.of R C) := projectiveResolution (ModuleCat.of R C)
  have hPA_proj (n : ℕ) : Module.Projective R (PA.complex.X n) :=
    ModuleCat.projective_of_module_projective (P := PA.complex.X n)
  have hPC_proj (n : ℕ) : Module.Projective R (PC.complex.X n) :=
    ModuleCat.projective_of_module_projective (P := PC.complex.X n)
  let εA : PA.complex.X 0 →ₗ[R] A := (PA.π.f 0).hom
  let εC : PC.complex.X 0 →ₗ[R] C := (PC.π.f 0).hom
  have hεA_surj : Function.Surjective εA :=
    (ModuleCat.epi_iff_surjective (PA.π.f 0)).mp inferInstance
  have hεC_surj : Function.Surjective εC :=
    (ModuleCat.epi_iff_surjective (PC.π.f 0)).mp inferInstance
  have hεA_comp (x : PA.complex.X 1) : εA ((PA.complex.d 1 0).hom x) = 0 :=
    congrArg (fun φ : PA.complex.X 1 ⟶ ModuleCat.of R A => φ.hom x) PA.complex_d_comp_π_f_zero
  have hεC_comp (x : PC.complex.X 1) : εC ((PC.complex.d 1 0).hom x) = 0 :=
    congrArg (fun φ : PC.complex.X 1 ⟶ ModuleCat.of R C => φ.hom x) PC.complex_d_comp_π_f_zero
  have hε_exact_of_res {X : Type} [AddCommGroup X] [Module R X]
      (PX : ProjectiveResolution (ModuleCat.of R X)) (x : PX.complex.X 0)
      (hx : (PX.π.f 0).hom x = 0) :
      ∃ y : PX.complex.X 1, (PX.complex.d 1 0).hom y = x := by
    -- Since PX.isColimitCokernelCofork is a colimit, the canonical quotient map factors through π.f 0!
    let Q := PX.complex.X 0 ⧸ LinearMap.range (PX.complex.d 1 0).hom
    let q : PX.complex.X 0 ⟶ ModuleCat.of R Q := ModuleCat.ofHom (LinearMap.range (PX.complex.d 1 0).hom).mkQ
    have hqw : (PX.complex.d 1 0 ≫ q) = 0 := by
      ext z; exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨z, rfl⟩
    let desc : ModuleCat.of R X ⟶ ModuleCat.of R Q :=
      PX.isColimitCokernelCofork.desc (CokernelCofork.ofπ q hqw)
    have hfac : (PX.π.f 0 ≫ desc) = q :=
      PX.isColimitCokernelCofork.fac (CokernelCofork.ofπ q hqw) WalkingParallelPair.one
    have hqx : q.hom x = 0 := by
      have h1 : desc.hom ((PX.π.f 0).hom x) = q.hom x :=
        congrArg (fun φ : PX.complex.X 0 ⟶ ModuleCat.of R Q => φ.hom x) hfac
      have hx0 : (PX.π.f 0).hom x = (0 : X) := hx
      rw [← h1, hx0]
      exact map_zero desc.hom
    exact (Submodule.Quotient.mk_eq_zero _).mp hqx
  have hεA_exact := hε_exact_of_res PA
  have hεC_exact := hε_exact_of_res PC
  have hPA_exact (n : ℕ) (x : PA.complex.X (n + 1)) (hx : (PA.complex.d (n + 1) n).hom x = 0) :
      ∃ y : PA.complex.X (n + 2), (PA.complex.d (n + 2) (n + 1)).hom y = x :=
    (ShortComplex.moduleCat_exact_iff _).mp (PA.exact_succ n) x hx
  have hPC_exact (n : ℕ) (x : PC.complex.X (n + 1)) (hx : (PC.complex.d (n + 1) n).hom x = 0) :
      ∃ y : PC.complex.X (n + 2), (PC.complex.d (n + 2) (n + 1)).hom y = x :=
    (ShortComplex.moduleCat_exact_iff _).mp (PC.exact_succ n) x hx
  have hPA_dd (n : ℕ) (x : PA.complex.X (n + 2)) :
      (PA.complex.d (n + 1) n).hom ((PA.complex.d (n + 2) (n + 1)).hom x) = 0 :=
    congrArg (fun φ : PA.complex.X (n + 2) ⟶ PA.complex.X n => φ.hom x)
      (PA.complex.d_comp_d (n + 2) (n + 1) n)
  have hPC_dd (n : ℕ) (x : PC.complex.X (n + 2)) :
      (PC.complex.d (n + 1) n).hom ((PC.complex.d (n + 2) (n + 1)).hom x) = 0 :=
    congrArg (fun φ : PC.complex.X (n + 2) ⟶ PC.complex.X n => φ.hom x)
      (PC.complex.d_comp_d (n + 2) (n + 1) n)
  -- Lift εC to s0 : PC.X 0 → B with p ∘ s0 = εC
  let _ := hPC_proj 0
  obtain ⟨s0, hs0⟩ := Module.projective_lifting_property p εC hp
  let εB : (PA.complex.X 0 × PC.complex.X 0) →ₗ[R] B := (i.comp εA).coprod s0
  -- Base lift h0 : PC.X 1 → PA.X 0
  have h_step0 : ∃ h0 : PC.complex.X 1 →ₗ[R] PA.complex.X 0,
      ∀ c : PC.complex.X 1, i (εA (h0 c)) + s0 ((PC.complex.d 1 0).hom c) = 0 := by
    let _ := hPC_proj 1
    let neg_s0_dC : PC.complex.X 1 →ₗ[R] LinearMap.ker p :=
      LinearMap.codRestrict (LinearMap.ker p) (-(s0.comp (PC.complex.d 1 0).hom)) (fun c => by
        rw [LinearMap.mem_ker, LinearMap.neg_apply, map_neg, LinearMap.comp_apply]
        have h1 : p (s0 ((PC.complex.d 1 0).hom c)) = εC ((PC.complex.d 1 0).hom c) :=
          LinearMap.congr_fun hs0 _
        rw [h1, hεC_comp, neg_zero])
    let mapA : PA.complex.X 0 →ₗ[R] LinearMap.ker p :=
      LinearMap.codRestrict (LinearMap.ker p) (i.comp εA) (fun a => by
        rw [LinearMap.mem_ker, LinearMap.comp_apply, ← LinearMap.mem_ker, ← hip]
        exact ⟨εA a, rfl⟩)
    have hmapA_surj : Function.Surjective mapA := by
      rintro ⟨b, hb⟩
      rw [← hip] at hb
      obtain ⟨a, rfl⟩ := hb
      obtain ⟨x, rfl⟩ := hεA_surj a
      exact ⟨x, rfl⟩
    obtain ⟨h0, hh0⟩ := Module.projective_lifting_property mapA neg_s0_dC hmapA_surj
    refine ⟨h0, fun c => ?_⟩
    have hc := congrArg Subtype.val (LinearMap.congr_fun hh0 c)
    change i (εA (h0 c)) = -(s0 ((PC.complex.d 1 0).hom c)) at hc
    rw [hc, neg_add_cancel]
  -- Inductive lift step
  have h_next : ∀ (n : ℕ) (hcur : PC.complex.X (n + 1) →ₗ[R] PA.complex.X n),
      (∀ c : PC.complex.X (n + 2), ∃ a : PA.complex.X (n + 1),
        (PA.complex.d (n + 1) n).hom a = -(hcur ((PC.complex.d (n + 2) (n + 1)).hom c))) →
      ∃ hnxt : PC.complex.X (n + 2) →ₗ[R] PA.complex.X (n + 1),
        ∀ c : PC.complex.X (n + 2),
          (PA.complex.d (n + 1) n).hom (hnxt c) + hcur ((PC.complex.d (n + 2) (n + 1)).hom c) = 0 := by
    intro n hcur hpre
    let _ := hPC_proj (n + 2)
    let targ : PC.complex.X (n + 2) →ₗ[R] LinearMap.range (PA.complex.d (n + 1) n).hom :=
      LinearMap.codRestrict _ (-(hcur.comp (PC.complex.d (n + 2) (n + 1)).hom)) (fun c => hpre c)
    obtain ⟨hnxt, hhnxt⟩ := Module.projective_lifting_property
      (LinearMap.rangeRestrict (PA.complex.d (n + 1) n).hom) targ
      (LinearMap.surjective_rangeRestrict _)
    refine ⟨hnxt, fun c => ?_⟩
    have hc := congrArg Subtype.val (LinearMap.congr_fun hhnxt c)
    change (PA.complex.d (n + 1) n).hom (hnxt c) = -(hcur ((PC.complex.d (n + 2) (n + 1)).hom c)) at hc
    rw [hc, neg_add_cancel]
  -- Build h n : PC.X (n + 1) → PA.X n together with the preimage invariant
  let buildAux : ∀ n : ℕ,
      Σ' (h : PC.complex.X (n + 1) →ₗ[R] PA.complex.X n),
        ∀ c : PC.complex.X (n + 2), ∃ a : PA.complex.X (n + 1),
          (PA.complex.d (n + 1) n).hom a = -(h ((PC.complex.d (n + 2) (n + 1)).hom c)) :=
    Nat.rec
      ⟨Classical.choose h_step0, fun c => by
        have h0 := Classical.choose_spec h_step0 ((PC.complex.d 2 1).hom c)
        rw [hPC_dd 0 c, map_zero, add_zero] at h0
        have he : εA (-(Classical.choose h_step0 ((PC.complex.d 2 1).hom c))) = 0 := by
          rw [map_neg, hi (h0.trans (map_zero i).symm), neg_zero]
        exact hεA_exact _ he⟩
      (fun n prev =>
        let hex := h_next n prev.1 prev.2
        ⟨Classical.choose hex, fun c => by
          have h1 := Classical.choose_spec hex ((PC.complex.d (n + 3) (n + 2)).hom c)
          rw [hPC_dd (n + 1) c, map_zero, add_zero] at h1
          have hneg : (PA.complex.d (n + 1) n).hom
              (-(Classical.choose hex ((PC.complex.d (n + 3) (n + 2)).hom c))) = 0 := by
            rw [map_neg, h1, neg_zero]
          exact hPA_exact n _ hneg⟩)
  let h (n : ℕ) : PC.complex.X (n + 1) →ₗ[R] PA.complex.X n := (buildAux n).1
  have hh0 (c : PC.complex.X 1) :
      i (εA (h 0 c)) + s0 ((PC.complex.d 1 0).hom c) = 0 :=
    Classical.choose_spec h_step0 c
  have hh_succ (n : ℕ) (c : PC.complex.X (n + 2)) :
      (PA.complex.d (n + 1) n).hom (h (n + 1) c) +
        h n ((PC.complex.d (n + 2) (n + 1)).hom c) = 0 :=
    Classical.choose_spec (h_next n (buildAux n).1 (buildAux n).2) c
  -- Build the chain complex KB with KB.X n = PA.X n × PC.X n
  let dB (n : ℕ) : ModuleCat.of R (PA.complex.X (n + 1) × PC.complex.X (n + 1)) ⟶
      ModuleCat.of R (PA.complex.X n × PC.complex.X n) :=
    ModuleCat.ofHom
      { toFun := fun x => ((PA.complex.d (n + 1) n).hom x.1 + h n x.2, (PC.complex.d (n + 1) n).hom x.2)
        map_add' := fun x y => by
          ext
          · change (PA.complex.d (n + 1) n).hom (x.1 + y.1) + h n (x.2 + y.2) =
              ((PA.complex.d (n + 1) n).hom x.1 + h n x.2) + ((PA.complex.d (n + 1) n).hom y.1 + h n y.2)
            rw [map_add, map_add]; abel
          · exact map_add (PC.complex.d (n + 1) n).hom x.2 y.2
        map_smul' := fun r x => by
          ext
          · change (PA.complex.d (n + 1) n).hom (r • x.1) + h n (r • x.2) =
              r • ((PA.complex.d (n + 1) n).hom x.1 + h n x.2)
            rw [map_smul, map_smul, smul_add]
          · exact map_smul (PC.complex.d (n + 1) n).hom r x.2 }
  have hdB_sq (n : ℕ) : (dB (n + 1) ≫ dB n) = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    rintro ⟨a, c⟩
    ext
    · change (PA.complex.d (n + 1) n).hom ((PA.complex.d (n + 2) (n + 1)).hom a + h (n + 1) c) +
        h n ((PC.complex.d (n + 2) (n + 1)).hom c) = 0
      rw [map_add, hPA_dd n a, zero_add, hh_succ n c]
    · change (PC.complex.d (n + 1) n).hom ((PC.complex.d (n + 2) (n + 1)).hom c) = 0
      exact hPC_dd n c
  let KB : ChainComplex (ModuleCat.{0} R) ℕ :=
    ChainComplex.of (fun n => ModuleCat.of R (PA.complex.X n × PC.complex.X n)) dB hdB_sq
  -- Short exact sequence of chain complexes 0 → PA → KB → PC → 0
  let ιK : PA.complex ⟶ KB :=
    { f := fun n => ModuleCat.ofHom (LinearMap.inl R (PA.complex.X n) (PC.complex.X n))
      comm' := fun n m hnm => by
        cases hnm
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro a
        ext
        · change ((KB.d (m + 1) m).hom (a, 0)).1 = (PA.complex.d (m + 1) m).hom a
          simp [KB, ChainComplex.of_d, dB]
        · change ((KB.d (m + 1) m).hom (a, 0)).2 = 0
          simp [KB, ChainComplex.of_d, dB] }
  let πK : KB ⟶ PC.complex :=
    { f := fun n => ModuleCat.ofHom (LinearMap.snd R (PA.complex.X n) (PC.complex.X n))
      comm' := fun n m hnm => by
        cases hnm
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        rintro ⟨a, c⟩
        change (PC.complex.d (m + 1) m).hom c = ((KB.d (m + 1) m).hom (a, c)).2
        simp [KB, ChainComplex.of_d, dB] }
  have hS_zero : (ιK ≫ πK) = 0 := by
    ext n a
    rfl
  let SK : ShortComplex (ChainComplex (ModuleCat.{0} R) ℕ) := ShortComplex.mk ιK πK hS_zero
  -- Check KB is a ProjectiveResolution of B via εB!
  have hKB_proj (n : ℕ) : Module.Projective R (KB.X n) := by
    let _ := hPA_proj n
    let _ := hPC_proj n
    change Module.Projective R (PA.complex.X n × PC.complex.X n)
    infer_instance
  have hps0 (c : PC.complex.X 0) : p (s0 c) = εC c := LinearMap.congr_fun hs0 c
  have hεB_surj : Function.Surjective εB := fun b => by
    obtain ⟨c, hc⟩ := hεC_surj (p b)
    have hker : b - s0 c ∈ LinearMap.ker p := by
      rw [LinearMap.mem_ker, map_sub, hps0 c, hc, sub_self]
    rw [← hip] at hker
    obtain ⟨a0, ha0⟩ := hker
    obtain ⟨a, rfl⟩ := hεA_surj a0
    refine ⟨(a, c), ?_⟩
    change i (εA a) + s0 c = b
    rw [ha0, sub_add_cancel]
  have hεB_comp (x : KB.X 1) : εB ((KB.d 1 0).hom x) = 0 := by
    rcases x with ⟨a, c⟩
    change i (εA ((PA.complex.d 1 0).hom a + h 0 c)) + s0 ((PC.complex.d 1 0).hom c) = 0
    rw [map_add, map_add, hεA_comp a, map_zero, zero_add, hh0 c]
  have hεB_exact (x : KB.X 0) (hx : εB x = 0) : ∃ y : KB.X 1, (KB.d 1 0).hom y = x := by
    rcases x with ⟨a, c⟩
    change i (εA a) + s0 c = 0 at hx
    have hpc : εC c = 0 := by
      have hp0 := congrArg p hx
      rw [map_add, map_zero, hps0 c] at hp0
      have hi0 : p (i (εA a)) = 0 := by
        rw [← LinearMap.mem_ker, ← hip]; exact ⟨εA a, rfl⟩
      rw [hi0, zero_add] at hp0
      exact hp0
    obtain ⟨c1, hc1⟩ := hεC_exact c hpc
    have ha_ker : εA (a - h 0 c1) = 0 := by
      apply hi
      rw [map_zero, map_sub, map_sub]
      have h1 := hh0 c1
      rw [hc1] at h1
      have hia : i (εA a) = - s0 c := eq_neg_of_add_eq_zero_left hx
      have hih : i (εA (h 0 c1)) = - s0 c := eq_neg_of_add_eq_zero_left h1
      rw [hia, hih, sub_self]
    obtain ⟨a1, ha1⟩ := hεA_exact _ ha_ker
    refine ⟨(a1, c1), ?_⟩
    change ((PA.complex.d 1 0).hom a1 + h 0 c1, (PC.complex.d 1 0).hom c1) = (a, c)
    ext
    · rw [ha1, sub_add_cancel]
    · exact hc1
  have hKB_exact (n : ℕ) (x : KB.X (n + 1)) (hx : (KB.d (n + 1) n).hom x = 0) :
      ∃ y : KB.X (n + 2), (KB.d (n + 2) (n + 1)).hom y = x := by
    rcases x with ⟨a, c⟩
    have hx' : ((PA.complex.d (n + 1) n).hom a + h n c, (PC.complex.d (n + 1) n).hom c) = (0, 0) := by
      simpa [KB, ChainComplex.of_d, dB] using hx
    have hx1 : (PA.complex.d (n + 1) n).hom a + h n c = 0 := congrArg Prod.fst hx'
    have hx2 : (PC.complex.d (n + 1) n).hom c = 0 := congrArg Prod.snd hx'
    obtain ⟨c1, hc1⟩ := hPC_exact n c hx2
    have ha_ker : (PA.complex.d (n + 1) n).hom (a - h (n + 1) c1) = 0 := by
      rw [map_sub]
      have h1 := hh_succ n c1
      rw [hc1] at h1
      have h2 : (PA.complex.d (n + 1) n).hom a = - h n c := eq_neg_of_add_eq_zero_left hx1
      have h3 : (PA.complex.d (n + 1) n).hom (h (n + 1) c1) = - h n c := eq_neg_of_add_eq_zero_left h1
      rw [h2, h3, sub_self]
    obtain ⟨a1, ha1⟩ := hPA_exact n _ ha_ker
    refine ⟨(a1, c1), ?_⟩
    have hd_eq : (KB.d (n + 2) (n + 1)).hom (a1, c1) =
        ((PA.complex.d (n + 2) (n + 1)).hom a1 + h (n + 1) c1,
          (PC.complex.d (n + 2) (n + 1)).hom c1) :=
      congrArg (fun φ : KB.X (n + 2) ⟶ KB.X (n + 1) => φ.hom (a1, c1))
        (ChainComplex.of_d _ dB (n + 1))
    rw [hd_eq]
    ext
    · rw [ha1, sub_add_cancel]
    · exact hc1
  let PB : ProjectiveResolution (ModuleCat.of R B) :=
    projectiveResolutionOfExact B KB hKB_proj εB hεB_surj hεB_comp hεB_exact hKB_exact
  have hcomm_i : (ιK.f 0 ≫ PB.π.f 0) = (PA.π.f 0 ≫ ModuleCat.ofHom i) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    change εB (a, 0) = i (εA a)
    simp [εB]
  have hcomm_p : (πK.f 0 ≫ PC.π.f 0) = (PB.π.f 0 ≫ ModuleCat.ofHom p) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    rintro ⟨a, c⟩
    change εC c = p (εB (a, c))
    simp only [εB, LinearMap.coprod_apply, map_add, LinearMap.comp_apply]
    have hi0 : p (i (εA a)) = 0 := by
      rw [← LinearMap.mem_ker, ← hip]; exact ⟨εA a, rfl⟩
    rw [hi0, zero_add, hps0 c]
  let F := (tensoringLeft (ModuleCat.{0} R)).obj (ModuleCat.of R M)
  let SM : ShortComplex (ChainComplex (ModuleCat.{0} R) ℕ) :=
    SK.map (F.mapHomologicalComplex (ComplexShape.down ℕ))
  have hSM_exact : SM.ShortExact := by
    apply HomologicalComplex.shortExact_of_degreewise_shortExact
    intro n
    let split_n : (SK.map (HomologicalComplex.eval _ _ n)).Splitting :=
      { r := ModuleCat.ofHom (LinearMap.fst R (PA.complex.X n) (PC.complex.X n))
        s := ModuleCat.ofHom (LinearMap.inr R (PA.complex.X n) (PC.complex.X n))
        f_r := by apply ModuleCat.hom_ext; apply LinearMap.ext; intro a; rfl
        s_g := by apply ModuleCat.hom_ext; apply LinearMap.ext; intro c; rfl
        id := by
          apply ModuleCat.hom_ext; apply LinearMap.ext; rintro ⟨a, c⟩
          change (a, 0) + (0, c) = (a, c)
          ext <;> simp }
    let split_Mn : (SM.map (HomologicalComplex.eval _ _ n)).Splitting :=
      split_n.map F
    exact split_Mn.shortExact
  let eA (n : ℕ) : torMod R M A n ≅ SM.X₁.homology n := PA.isoLeftDerivedObj F n
  let eB (n : ℕ) : torMod R M B n ≅ SM.X₂.homology n := PB.isoLeftDerivedObj F n
  let eC (n : ℕ) : torMod R M C n ≅ SM.X₃.homology n := PC.isoLeftDerivedObj F n
  let δ (n : ℕ) : torMod R M C (n + 1) →ₗ[R] torMod R M A n :=
    ((eC (n + 1)).hom ≫ hSM_exact.δ (n + 1) n rfl ≫ (eA n).inv).hom
  have htor_i_hom (n : ℕ) (x : torMod R M A n) :
      (eB n).hom.hom (torMap M i n x) = (HomologicalComplex.homologyMap SM.f n).hom ((eA n).hom.hom x) :=
    congrArg (fun φ : torMod R M A n ⟶ SM.X₂.homology n => φ.hom x)
      (ProjectiveResolution.isoLeftDerivedObj_hom_naturality (ModuleCat.ofHom i) PA PB ιK hcomm_i F n)
  have htor_p_hom (n : ℕ) (x : torMod R M B n) :
      (eC n).hom.hom (torMap M p n x) = (HomologicalComplex.homologyMap SM.g n).hom ((eB n).hom.hom x) :=
    congrArg (fun φ : torMod R M B n ⟶ SM.X₃.homology n => φ.hom x)
      (ProjectiveResolution.isoLeftDerivedObj_hom_naturality (ModuleCat.ofHom p) PB PC πK hcomm_p F n)
  have iso_hom_inv {X Y : ModuleCat.{0} R} (e : X ≅ Y) (y : Y) :
      e.hom.hom (e.inv.hom y) = y :=
    congrArg (fun φ : Y ⟶ Y => φ.hom y) e.inv_hom_id
  have iso_inv_hom {X Y : ModuleCat.{0} R} (e : X ≅ Y) (x : X) :
      e.inv.hom (e.hom.hom x) = x :=
    congrArg (fun φ : X ⟶ X => φ.hom x) e.hom_inv_id
  refine ⟨δ, ?_, ?_, ?_⟩
  · intro n x
    have hex := (ShortComplex.moduleCat_exact_iff _).mp (hSM_exact.homology_exact₁ (n + 1) n rfl)
    have h1 : torMap M i n x = 0 ↔
        (HomologicalComplex.homologyMap SM.f n).hom ((eA n).hom.hom x) = 0 := by
      rw [← htor_i_hom n x]
      exact (eB n).toLinearEquiv.map_eq_zero_iff.symm
    rw [h1]
    constructor
    · intro hx
      obtain ⟨y, hy⟩ := hex ((eA n).hom.hom x) hx
      refine ⟨(eC (n + 1)).inv.hom y, ?_⟩
      change (eA n).inv.hom ((hSM_exact.δ (n + 1) n rfl).hom ((eC (n + 1)).hom.hom ((eC (n + 1)).inv.hom y))) = x
      rw [iso_hom_inv (eC (n + 1)) y, hy]
      exact iso_inv_hom (eA n) x
    · rintro ⟨z, rfl⟩
      have hcomp := congrArg (fun φ : SM.X₃.homology (n + 1) ⟶ SM.X₂.homology n =>
        φ.hom ((eC (n + 1)).hom.hom z)) (hSM_exact.δ_comp (n + 1) n rfl)
      change (HomologicalComplex.homologyMap SM.f n).hom
        ((eA n).hom.hom ((eA n).inv.hom ((hSM_exact.δ (n + 1) n rfl).hom ((eC (n + 1)).hom.hom z)))) = 0
      rw [iso_hom_inv (eA n)]
      exact hcomp
  · intro n x
    have hex := (ShortComplex.moduleCat_exact_iff _).mp (hSM_exact.homology_exact₂ n)
    have h1 : torMap M p n x = 0 ↔
        (HomologicalComplex.homologyMap SM.g n).hom ((eB n).hom.hom x) = 0 := by
      rw [← htor_p_hom n x]
      exact (eC n).toLinearEquiv.map_eq_zero_iff.symm
    rw [h1]
    constructor
    · intro hx
      obtain ⟨y, hy⟩ := hex ((eB n).hom.hom x) hx
      refine ⟨(eA n).inv.hom y, ?_⟩
      apply (eB n).toLinearEquiv.injective
      change (eB n).hom.hom (torMap M i n ((eA n).inv.hom y)) = (eB n).hom.hom x
      rw [htor_i_hom n, iso_hom_inv (eA n) y, hy]
    · rintro ⟨z, rfl⟩
      rw [htor_i_hom n]
      have hzero : (HomologicalComplex.homologyMap SM.f n ≫ HomologicalComplex.homologyMap SM.g n) = 0 := by
        rw [← HomologicalComplex.homologyMap_comp, SM.zero, HomologicalComplex.homologyMap_zero]
      exact congrArg (fun φ : SM.X₁.homology n ⟶ SM.X₃.homology n => φ.hom ((eA n).hom.hom z)) hzero
  · intro n x
    have hex := (ShortComplex.moduleCat_exact_iff _).mp (hSM_exact.homology_exact₃ (n + 1) n rfl)
    have h1 : δ n x = 0 ↔
        (hSM_exact.δ (n + 1) n rfl).hom ((eC (n + 1)).hom.hom x) = 0 := by
      change (eA n).inv.hom ((hSM_exact.δ (n + 1) n rfl).hom ((eC (n + 1)).hom.hom x)) = 0 ↔ _
      exact (eA n).toLinearEquiv.symm.map_eq_zero_iff
    rw [h1]
    constructor
    · intro hx
      obtain ⟨y, hy⟩ := hex ((eC (n + 1)).hom.hom x) hx
      refine ⟨(eB (n + 1)).inv.hom y, ?_⟩
      apply (eC (n + 1)).toLinearEquiv.injective
      change (eC (n + 1)).hom.hom (torMap M p (n + 1) ((eB (n + 1)).inv.hom y)) = (eC (n + 1)).hom.hom x
      rw [htor_p_hom (n + 1), iso_hom_inv (eB (n + 1)) y, hy]
    · rintro ⟨z, rfl⟩
      rw [htor_p_hom (n + 1)]
      exact congrArg (fun φ : SM.X₂.homology (n + 1) ⟶ SM.X₁.homology n =>
        φ.hom ((eB (n + 1)).hom.hom z)) (hSM_exact.comp_δ (n + 1) n rfl)


end TorLES

section ChangeOfRings

noncomputable def liftBaseChange {S R X A : Type} [CommRing S] [CommRing R] [Algebra S R]
    [AddCommGroup X] [Module S X] [AddCommMonoid A] [Module S A] [Module R A] [IsScalarTower S R A]
    (f : X →ₗ[S] A) : (R ⊗[S] X) →ₗ[R] A :=
  TensorProduct.AlgebraTensorModule.lift
    { toFun := fun r =>
        { toFun := fun x => r • f x
          map_add' := fun x y => by rw [map_add, smul_add]
          map_smul' := fun s x => by
            change r • f (s • x) = s • (r • f x)
            rw [map_smul, smul_comm] }
      map_add' := fun r₁ r₂ => by ext x; exact add_smul r₁ r₂ (f x)
      map_smul' := fun c r => by ext x; exact mul_smul c r (f x) }

/-- Base change of a projective module is projective. -/
lemma projective_baseChange {S R X : Type} [CommRing S] [CommRing R] [Algebra S R]
    [AddCommGroup X] [Module S X] [Module.Projective S X] :
    Module.Projective R (R ⊗[S] X) := by
  refine Module.Projective.of_lifting_property' fun {A B} _ _ _ _ f g hf => ?_
  let _ : Module S A := Module.compHom A (algebraMap S R)
  let _ : Module S B := Module.compHom B (algebraMap S R)
  have _ : IsScalarTower S R A := ⟨fun s r a => by
    rw [Algebra.smul_def, mul_smul]; rfl⟩
  have _ : IsScalarTower S R B := ⟨fun s r b => by
    rw [Algebra.smul_def, mul_smul]; rfl⟩
  let gS : X →ₗ[S] B :=
    { toFun := fun x => g (1 ⊗ₜ[S] x)
      map_add' := fun x y => by rw [TensorProduct.tmul_add, map_add]
      map_smul' := fun s x => by
        change g (1 ⊗ₜ[S] (s • x)) = algebraMap S R s • g (1 ⊗ₜ[S] x)
        rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_one,
          ← mul_one (algebraMap S R s), ← smul_eq_mul, ← TensorProduct.smul_tmul', map_smul,
          smul_eq_mul, mul_one] }
  obtain ⟨hS, hhS⟩ := Module.projective_lifting_property (f.restrictScalars S) gS hf
  let h : (R ⊗[S] X) →ₗ[R] A := liftBaseChange hS
  refine ⟨h, ?_⟩
  apply TensorProduct.AlgebraTensorModule.ext
  intro r x
  change f (r • hS x) = g (r ⊗ₜ[S] x)
  rw [map_smul]
  have h1 : f (hS x) = g (1 ⊗ₜ[S] x) := LinearMap.congr_fun hhS x
  rw [h1, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- Over a domain `S`, a nonzero element `g : S` acts injectively on any projective `S`-module. -/
lemma smul_injective_of_projective_domain {S X : Type} [CommRing S] [IsDomain S]
    [AddCommGroup X] [Module S X] [Module.Projective S X]
    {g : S} (hg : g ≠ 0) :
    Function.Injective (fun x : X => g • x) := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property
    (Finsupp.linearCombination S (id : X → X)) LinearMap.id
    (Finsupp.linearCombination_id_surjective S X)
  intro x y hxy
  change g • x = g • y at hxy
  have h0 : g • (x - y) = 0 := by rw [smul_sub, hxy, sub_self]
  have hs0 : g • s (x - y) = 0 := by rw [← map_smul, h0, map_zero]
  have hsz : s (x - y) = 0 := by
    ext z
    have hz : g * (s (x - y)) z = 0 := congrArg (fun f : X →₀ S => f z) hs0
    exact (mul_eq_zero.mp hz).resolve_left hg
  have hxy0 : x - y = 0 := by
    have h1 : Finsupp.linearCombination S (id : X → X) (s (x - y)) = x - y :=
      LinearMap.congr_fun hs (x - y)
    rw [hsz, map_zero] at h1
    exact h1.symm
  exact sub_eq_zero.mp hxy0

/-- Concrete homology at `0` of a chain complex in `ModuleCat R` as `X_0 ⧸ range (d 1 0)`. -/
lemma homology_zero_equiv_quot_range {R : Type} [CommRing R]
    (K : ChainComplex (ModuleCat.{0} R) ℕ) :
    Nonempty (K.homology 0 ≃ₗ[R] (K.X 0 ⧸ LinearMap.range (K.d 1 0).hom)) := by
  have hg0 : (K.sc' 1 0 0).g = 0 := K.shape 0 0 (by simp)
  have _ : IsIso (K.sc' 1 0 0).homologyι := ShortComplex.isIso_homologyι (K.sc' 1 0 0) hg0
  let e1 : K.homology 0 ≅ (K.sc' 1 0 0).homology :=
    K.homologyIsoSc' 1 0 0 (ChainComplex.prev ℕ 0) ChainComplex.next_nat_zero
  let e2 : (K.sc' 1 0 0).homology ≅ (K.sc' 1 0 0).opcycles := asIso (K.sc' 1 0 0).homologyι
  let e3 : (K.sc' 1 0 0).opcycles ≅ ModuleCat.of R (K.X 0 ⧸ LinearMap.range (K.d 1 0).hom) :=
    (K.sc' 1 0 0).moduleCatOpcyclesIso
  exact ⟨(e1 ≪≫ e2 ≪≫ e3).toLinearEquiv⟩

/-- Concrete homology at `k + 1` of a chain complex in `ModuleCat R` transported along linear
equivalences `e0, e1, e2`. -/
lemma homology_succ_equiv_of_iso {R : Type} [CommRing R]
    (K : ChainComplex (ModuleCat.{0} R) ℕ) (k : ℕ)
    {A₀ A₁ A₂ : Type} [AddCommGroup A₀] [Module R A₀]
    [AddCommGroup A₁] [Module R A₁] [AddCommGroup A₂] [Module R A₂]
    (e₀ : A₀ ≃ₗ[R] K.X k) (e₁ : A₁ ≃ₗ[R] K.X (k + 1)) (e₂ : A₂ ≃ₗ[R] K.X (k + 2))
    (f : A₂ →ₗ[R] A₁) (g : A₁ →ₗ[R] A₀)
    (hf : ∀ x, e₁ (f x) = (K.d (k + 2) (k + 1)).hom (e₂ x))
    (hg : ∀ x, e₀ (g x) = (K.d (k + 1) k).hom (e₁ x)) :
    Nonempty (K.homology (k + 1) ≃ₗ[R]
      (LinearMap.ker g ⧸ (LinearMap.range f).comap (LinearMap.ker g).subtype)) := by
  let eH : K.homology (k + 1) ≅ (K.sc' (k + 2) (k + 1) k).moduleCatLeftHomologyData.H :=
    K.homologyIsoSc' (k + 2) (k + 1) k (ChainComplex.prev ℕ (k + 1)) (ChainComplex.next_nat_succ k) ≪≫
      (K.sc' (k + 2) (k + 1) k).moduleCatHomologyIso
  let eKer : LinearMap.ker g ≃ₗ[R] LinearMap.ker (K.d (k + 1) k).hom :=
    { toFun := fun x => ⟨e₁ x.1, by
        rw [LinearMap.mem_ker, ← hg x.1, x.2, map_zero]⟩
      invFun := fun y => ⟨e₁.symm y.1, by
        rw [LinearMap.mem_ker]
        apply e₀.injective
        rw [map_zero, hg, e₁.apply_symm_apply]
        exact y.2⟩
      map_add' := fun x y => Subtype.ext (map_add e₁ x.1 y.1)
      map_smul' := fun r x => Subtype.ext (map_smul e₁ r x.1)
      left_inv := fun x => Subtype.ext (e₁.symm_apply_apply x.1)
      right_inv := fun y => Subtype.ext (e₁.apply_symm_apply y.1) }
  have hsub : Submodule.map eKer.toLinearMap ((LinearMap.range f).comap (LinearMap.ker g).subtype) =
      LinearMap.range (K.sc' (k + 2) (k + 1) k).moduleCatToCycles := by
    ext ⟨y, hy⟩
    constructor
    · rintro ⟨⟨x, hx⟩, ⟨a, ha⟩, heq⟩
      refine ⟨e₂ a, Subtype.ext ?_⟩
      change (K.d (k + 2) (k + 1)).hom (e₂ a) = y
      rw [← hf a, ha]
      exact congrArg Subtype.val heq
    · rintro ⟨z, hz⟩
      have hz' : (K.d (k + 2) (k + 1)).hom z = y := congrArg Subtype.val hz
      let z' : K.X (k + 2) := z
      have hker_f : f (e₂.symm z') ∈ LinearMap.ker g := by
        rw [LinearMap.mem_ker]
        apply e₀.injective
        rw [map_zero, hg, hf, e₂.apply_symm_apply z']
        change (K.d (k + 1) k).hom ((K.d (k + 2) (k + 1)).hom z) = 0
        rw [hz']
        exact hy
      refine ⟨⟨f (e₂.symm z'), hker_f⟩, ⟨e₂.symm z', rfl⟩, Subtype.ext ?_⟩
      change e₁ (f (e₂.symm z')) = y
      rw [hf, e₂.apply_symm_apply z']
      exact hz'
  let eQ := Submodule.quotEquivOfEq _ _ hsub
  let eQuot : (LinearMap.ker g ⧸ (LinearMap.range f).comap (LinearMap.ker g).subtype) ≃ₗ[R]
      (K.sc' (k + 2) (k + 1) k).moduleCatLeftHomologyData.H :=
    (Submodule.Quotient.equiv _ _ eKer rfl).trans eQ
  exact ⟨eH.toLinearEquiv.trans eQuot.symm⟩

/-- Base-change cancellation `M ⊗[R] (R ⊗[S] X) ≃ₗ[S] M ⊗[S] X` for a surjective `S → R`. -/
noncomputable def baseChangeTensorEquiv
    {S R M X : Type} [CommRing S] [CommRing R] [Algebra S R]
    [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower S R M]
    [AddCommGroup X] [Module S X]
    (hsurj : Function.Surjective (algebraMap S R)) :
    (M ⊗[R] (R ⊗[S] X)) ≃ₗ[S] (M ⊗[S] X) := by
  let _ : SMulCommClass R S M := ⟨fun r s m => by
    obtain ⟨a, rfl⟩ := hsurj r
    rw [algebraMap_smul, algebraMap_smul, smul_comm]⟩
  let _ : SMulCommClass S R M := SMulCommClass.symm R S M
  let _ : Module R (M ⊗[S] X) := TensorProduct.leftModule
  let _ : IsScalarTower S R (M ⊗[S] X) := ⟨fun s r t => by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul m x =>
      change ((s • r) • m) ⊗ₜ[S] x = s • ((r • m) ⊗ₜ[S] x)
      rw [smul_assoc, TensorProduct.smul_tmul']
    | add t₁ t₂ ih₁ ih₂ => rw [smul_add, smul_add, smul_add, ih₁, ih₂]⟩
  let inner (m : M) : (R ⊗[S] X) →ₗ[R] (M ⊗[S] X) :=
    liftBaseChange
      { toFun := fun x => m ⊗ₜ[S] x
        map_add' := fun x₁ x₂ => TensorProduct.tmul_add m x₁ x₂
        map_smul' := fun s x => TensorProduct.tmul_smul s m x }
  let fwdR : (M ⊗[R] (R ⊗[S] X)) →ₗ[R] (M ⊗[S] X) :=
    TensorProduct.lift
      { toFun := inner
        map_add' := fun m₁ m₂ => by
          apply TensorProduct.AlgebraTensorModule.ext; intro r x
          change (r • (m₁ + m₂)) ⊗ₜ[S] x = (r • m₁) ⊗ₜ[S] x + (r • m₂) ⊗ₜ[S] x
          rw [smul_add, TensorProduct.add_tmul]
        map_smul' := fun c m => by
          apply TensorProduct.AlgebraTensorModule.ext; intro r x
          change (r • (c • m)) ⊗ₜ[S] x = (c • (r • m)) ⊗ₜ[S] x
          rw [smul_comm] }
  let bwdS : (M ⊗[S] X) →ₗ[S] (M ⊗[R] (R ⊗[S] X)) :=
    TensorProduct.lift
      (LinearMap.mk₂ S (fun m x => m ⊗ₜ[R] ((1 : R) ⊗ₜ[S] x))
        (fun m₁ m₂ x => TensorProduct.add_tmul m₁ m₂ _)
        (fun s m x => (TensorProduct.smul_tmul' s m ((1 : R) ⊗ₜ[S] x)).symm)
        (fun m x₁ x₂ => by rw [TensorProduct.tmul_add, TensorProduct.tmul_add])
        (fun s m x => by
          change m ⊗ₜ[R] ((1 : R) ⊗ₜ[S] (s • x)) = s • (m ⊗ₜ[R] ((1 : R) ⊗ₜ[S] x))
          rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_one,
            ← mul_one (algebraMap S R s), ← smul_eq_mul, ← TensorProduct.smul_tmul',
            TensorProduct.tmul_smul]
          exact algebraMap_smul R s (m ⊗ₜ[R] ((1 : R) ⊗ₜ[S] x))))
  refine LinearEquiv.ofLinearMap (fwdR.restrictScalars S) bwdS ?_ ?_
  · apply TensorProduct.ext'
    intro m x
    change ((1 : R) • m) ⊗ₜ[S] x = m ⊗ₜ[S] x
    rw [one_smul]
  · apply LinearMap.ext
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul m u =>
      induction u using TensorProduct.induction_on with
      | zero => simp
      | tmul r x =>
        change (r • m) ⊗ₜ[R] ((1 : R) ⊗ₜ[S] x) = m ⊗ₜ[R] (r ⊗ₜ[S] x)
        rw [TensorProduct.smul_tmul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      | add u₁ u₂ ih₁ ih₂ =>
        simp only [LinearMap.comp_apply, LinearMap.id_apply, TensorProduct.tmul_add, map_add] at ih₁ ih₂ ⊢
        rw [ih₁, ih₂]
    | add t₁ t₂ ih₁ ih₂ =>
      simp only [LinearMap.comp_apply, LinearMap.id_apply, map_add] at ih₁ ih₂ ⊢
      rw [ih₁, ih₂]

lemma baseChangeTensorEquiv_comm
    {S R M X Y : Type} [CommRing S] [CommRing R] [Algebra S R]
    [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower S R M]
    [AddCommGroup X] [Module S X] [AddCommGroup Y] [Module S Y]
    (hsurj : Function.Surjective (algebraMap S R))
    (f : X →ₗ[S] Y) (t : M ⊗[R] (R ⊗[S] X)) :
    baseChangeTensorEquiv hsurj (LinearMap.lTensor M (LinearMap.baseChange R f) t) =
      LinearMap.lTensor M f (baseChangeTensorEquiv hsurj t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul m u =>
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul r x => rfl
    | add u₁ u₂ ih₁ ih₂ =>
      simp only [TensorProduct.tmul_add, map_add] at ih₁ ih₂ ⊢
      rw [ih₁, ih₂]
  | add t₁ t₂ ih₁ ih₂ => rw [map_add, map_add, map_add, map_add, ih₁, ih₂]



noncomputable def toSLinear {S R : Type} [CommRing S] [CommRing R] [Algebra S R]
    {X : ModuleCat.{0} R} {Y : Type} [AddCommGroup Y] [Module S Y] [Module R Y]
    [IsScalarTower S R Y] (f : S →+* R) (hf : f = algebraMap S R) (φ : X →ₗ[R] Y) :
    ((ModuleCat.restrictScalars f).obj X) →ₗ[S] Y where
  toFun x := φ x
  map_add' x₁ x₂ := φ.map_add x₁ x₂
  map_smul' s x :=
    let x' : X := x
    (φ.map_smul (f s) x').trans (by rw [hf, algebraMap_smul]; rfl)

noncomputable def fromSLinear {S R : Type} [CommRing S] [CommRing R] [Algebra S R]
    {X : ModuleCat.{0} R} {Y : Type} [AddCommGroup Y] [Module S Y] [Module R Y]
    [IsScalarTower S R Y] (f : S →+* R) (hf : f = algebraMap S R) (ψ : Y →ₗ[R] X) :
    Y →ₗ[S] ((ModuleCat.restrictScalars f).obj X) where
  toFun := ψ
  map_add' := ψ.map_add
  map_smul' s y := by
    change ψ (s • y) = f s • ψ y
    rw [hf, ← algebraMap_smul R s y, ψ.map_smul]

noncomputable def equivSLinear {S R : Type} [CommRing S] [CommRing R] [Algebra S R]
    {X : ModuleCat.{0} R} {Y : Type} [AddCommGroup Y] [Module S Y] [Module R Y]
    [IsScalarTower S R Y] (f : S →+* R) (hf : f = algebraMap S R) (e : X ≃ₗ[R] Y) :
    ((ModuleCat.restrictScalars f).obj X) ≃ₗ[S] Y :=
  LinearEquiv.ofLinearMap (toSLinear f hf e.toLinearMap) (fromSLinear f hf e.symm.toLinearMap)
    (LinearMap.ext fun y => e.apply_symm_apply y)
    (LinearMap.ext fun x => e.symm_apply_apply (x : X))

lemma exact_of_surj_inj {A₁ A₂ A₃ B₁ B₂ B₃ : Type*} [Zero A₃] [Zero B₃]
    (p₁ : B₁ → A₁) (hp₁ : Function.Surjective p₁)
    (e₂ : A₂ ≃ B₂)
    (i₃ : A₃ → B₃) (hi₃ : ∀ x, i₃ x = 0 ↔ x = 0)
    (u : A₁ → A₂) (v : A₂ → A₃) (huv : Function.Exact u v)
    (u' : B₁ → B₂) (v' : B₂ → B₃)
    (hu' : ∀ b₁, u' b₁ = e₂ (u (p₁ b₁)))
    (hv' : ∀ b₂, v' b₂ = i₃ (v (e₂.symm b₂))) :
    Function.Exact u' v' := by
  intro b₂
  rw [hv', hi₃]
  constructor
  · intro hv0
    obtain ⟨a₁, ha₁⟩ := (huv (e₂.symm b₂)).mp hv0
    obtain ⟨b₁, rfl⟩ := hp₁ a₁
    refine ⟨b₁, ?_⟩
    rw [hu', ha₁, e₂.apply_symm_apply]
  · rintro ⟨b₁, rfl⟩
    rw [hu', e₂.symm_apply_apply]
    exact (huv (u (p₁ b₁))).mpr ⟨p₁ b₁, rfl⟩

set_option maxHeartbeats 1200000 in
theorem serre_h2_aux
    (S : Type) [CommRing S] [IsDomain S]
    (g : S) (hg_ne : g ≠ 0)
    (R : Type) [CommRing R] [Algebra S R]
    (f : S →+* R) (hf : f = algebraMap S R)
    (hsurj : Function.Surjective (algebraMap S R))
    (hsurj_tmul : ∀ {X : Type} [AddCommGroup X] [Module S X] (u : R ⊗[S] X),
      ∃ x : X, (1 : R) ⊗ₜ[S] x = u)
    (hone_tmul_zero_iff : ∀ {X : Type} [AddCommGroup X] [Module S X] (x : X),
      (1 : R) ⊗ₜ[S] x = 0 ↔ ∃ y : X, g • y = x)
    (M : Type) [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower S R M]
    (N : Type) [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower S R N]
    (hgN : ∀ n : N, g • n = 0) :
    let A := fun i => torMod S M N i
    let BS := fun i => (ModuleCat.restrictScalars f).obj (torMod R M N i)
    ∃ (_zeroEquiv : A 0 ≃ₗ[S] BS 0),
    ∃ (fromQuot : ∀ i, BS i →ₗ[S] A (i + 1)),
    ∃ (toQuot : ∀ i, A (i + 1) →ₗ[S] BS (i + 1)),
    ∃ (connect : ∀ i, BS (i + 2) →ₗ[S] BS i),
    (∀ i, Function.Exact (fromQuot i) (toQuot i)) ∧
    (∀ i, Function.Exact (toQuot (i + 1)) (connect i)) ∧
    (∀ i, Function.Exact (connect i) (fromQuot i)) ∧
    (Function.Surjective (toQuot 0)) := by
  intro A BS
  let PN : ProjectiveResolution (ModuleCat.of S N) := projectiveResolution (ModuleCat.of S N)
  have hPN_proj (n : ℕ) : Module.Projective S (PN.complex.X n) :=
    ModuleCat.projective_of_module_projective (P := PN.complex.X n)
  have hPN_reg (n : ℕ) : Function.Injective (fun x : PN.complex.X n => g • x) := by
    let _ := hPN_proj n
    exact smul_injective_of_projective_domain hg_ne
  let εP : PN.complex.X 0 →ₗ[S] N := (PN.π.f 0).hom
  have hεP_surj : Function.Surjective εP :=
    (ModuleCat.epi_iff_surjective (PN.π.f 0)).mp inferInstance
  have hεP_comp (x : PN.complex.X 1) : εP ((PN.complex.d 1 0).hom x) = 0 :=
    congrArg (fun φ : PN.complex.X 1 ⟶ ModuleCat.of S N => φ.hom x) PN.complex_d_comp_π_f_zero
  have hεP_exact (x : PN.complex.X 0) (hx : εP x = 0) :
      ∃ y : PN.complex.X 1, (PN.complex.d 1 0).hom y = x := by
    let Quot := PN.complex.X 0 ⧸ LinearMap.range (PN.complex.d 1 0).hom
    let q : PN.complex.X 0 ⟶ ModuleCat.of S Quot :=
      ModuleCat.ofHom (LinearMap.range (PN.complex.d 1 0).hom).mkQ
    have hqw : (PN.complex.d 1 0 ≫ q) = 0 := by
      ext z; exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨z, rfl⟩
    let desc : ModuleCat.of S N ⟶ ModuleCat.of S Quot :=
      PN.isColimitCokernelCofork.desc (CokernelCofork.ofπ q hqw)
    have hfac : (PN.π.f 0 ≫ desc) = q :=
      PN.isColimitCokernelCofork.fac (CokernelCofork.ofπ q hqw) WalkingParallelPair.one
    have hqx : q.hom x = 0 := by
      have h1 : desc.hom ((PN.π.f 0).hom x) = q.hom x :=
        congrArg (fun φ : PN.complex.X 0 ⟶ ModuleCat.of S Quot => φ.hom x) hfac
      have hx0 : (PN.π.f 0).hom x = (0 : N) := hx
      rw [← h1, hx0]
      exact map_zero desc.hom
    exact (Submodule.Quotient.mk_eq_zero _).mp hqx
  have hPN_exact (n : ℕ) (x : PN.complex.X (n + 1)) (hx : (PN.complex.d (n + 1) n).hom x = 0) :
      ∃ y : PN.complex.X (n + 2), (PN.complex.d (n + 2) (n + 1)).hom y = x :=
    (ShortComplex.moduleCat_exact_iff _).mp (PN.exact_succ n) x hx
  have hPN_dd (n : ℕ) (x : PN.complex.X (n + 2)) :
      (PN.complex.d (n + 1) n).hom ((PN.complex.d (n + 2) (n + 1)).hom x) = 0 :=
    congrArg (fun φ : PN.complex.X (n + 2) ⟶ PN.complex.X n => φ.hom x)
      (PN.complex.d_comp_d (n + 2) (n + 1) n)
  -- Define (R ⊗[S] PN.complex.X n) = R ⊗[S] PN.complex.X n and dQ n : (R ⊗[S] PN.complex.X (n+1)) →ₗ[R] (R ⊗[S] PN.complex.X n)
  have hQ_proj (n : ℕ) : Module.Projective R ((R ⊗[S] PN.complex.X n)) := by
    let _ := hPN_proj n
    exact projective_baseChange
  let dQ (n : ℕ) : (R ⊗[S] PN.complex.X (n + 1)) →ₗ[R] (R ⊗[S] PN.complex.X n) :=
    LinearMap.baseChange R (PN.complex.d (n + 1) n).hom
  have hdQ_tmul (n : ℕ) (r : R) (x : PN.complex.X (n + 1)) :
      dQ n (r ⊗ₜ[S] x) = r ⊗ₜ[S] ((PN.complex.d (n + 1) n).hom x) := rfl
  have hdQ_sq (n : ℕ) (u : (R ⊗[S] PN.complex.X (n + 2))) : dQ n (dQ (n + 1) u) = 0 := by
    obtain ⟨x, rfl⟩ := hsurj_tmul u
    rw [hdQ_tmul, hdQ_tmul, hPN_dd n x, TensorProduct.tmul_zero]
  -- Step 2: Augmentation εQ : (R ⊗[S] PN.complex.X 0) →ₗ[R] N and exactness of Q_•
  let εQ : (R ⊗[S] PN.complex.X 0) →ₗ[R] N := liftBaseChange εP
  have hεQ_tmul (r : R) (x : PN.complex.X 0) : εQ (r ⊗ₜ[S] x) = r • εP x := rfl
  have hεQ_surj : Function.Surjective εQ := fun n => by
    obtain ⟨x, rfl⟩ := hεP_surj n
    exact ⟨1 ⊗ₜ[S] x, by rw [hεQ_tmul, one_smul]⟩
  have hεQ_comp (u : (R ⊗[S] PN.complex.X 1)) : εQ (dQ 0 u) = 0 := by
    obtain ⟨x, rfl⟩ := hsurj_tmul u
    rw [hdQ_tmul, hεQ_tmul, hεP_comp x, smul_zero]
  have hεQ_exact (u : (R ⊗[S] PN.complex.X 0)) (hu : εQ u = 0) : ∃ v : (R ⊗[S] PN.complex.X 1), dQ 0 v = u := by
    obtain ⟨x, rfl⟩ := hsurj_tmul u
    rw [hεQ_tmul, one_smul] at hu
    obtain ⟨y, hy⟩ := hεP_exact x hu
    exact ⟨1 ⊗ₜ[S] y, by rw [hdQ_tmul, hy]⟩
  have hQ_exact_ge2 (n : ℕ) (u : (R ⊗[S] PN.complex.X (n + 2))) (hu : dQ (n + 1) u = 0) :
      ∃ v : (R ⊗[S] PN.complex.X (n + 3)), dQ (n + 2) v = u := by
    obtain ⟨x, rfl⟩ := hsurj_tmul u
    rw [hdQ_tmul] at hu
    obtain ⟨y, hy⟩ := (hone_tmul_zero_iff _).mp hu
    have hdy : (PN.complex.d (n + 1) n).hom y = 0 := by
      apply hPN_reg n
      dsimp only
      rw [smul_zero, ← map_smul, hy, hPN_dd n x]
    obtain ⟨z, hz⟩ := hPN_exact n y hdy
    have hdxz : (PN.complex.d (n + 2) (n + 1)).hom (x - g • z) = 0 := by
      rw [map_sub, map_smul, hz, hy, sub_self]
    obtain ⟨w, hw⟩ := hPN_exact (n + 1) (x - g • z) hdxz
    refine ⟨1 ⊗ₜ[S] w, ?_⟩
    rw [hdQ_tmul, hw, TensorProduct.tmul_sub]
    have hgz0 : (1 : R) ⊗ₜ[S] (g • z) = 0 := (hone_tmul_zero_iff _).mpr ⟨z, rfl⟩
    rw [hgz0, sub_zero]
  -- Step 3: Define B0, Z1, B1 and the 3 short exact sequences over R
  let B0 : Submodule R (R ⊗[S] PN.complex.X 0) := LinearMap.range (dQ 0)
  let _ : AddCommGroup B0 := Submodule.addCommGroup B0
  let Z1 : Submodule R (R ⊗[S] PN.complex.X 1) := LinearMap.ker (dQ 0)
  let _ : AddCommGroup Z1 := Submodule.addCommGroup Z1
  let dQ1_to_Z1 : (R ⊗[S] PN.complex.X 2) →ₗ[R] Z1 := LinearMap.codRestrict Z1 (dQ 1) (fun u => hdQ_sq 0 u)
  let B1 : Submodule R Z1 := LinearMap.range dQ1_to_Z1
  let _ : AddCommGroup B1 := Submodule.addCommGroup B1
  -- Construct ψ : Z1 →ₗ[R] N with ker ψ = B1 and ψ surjective
  have hZ1_exists_y (u : Z1) :
      ∃ y : PN.complex.X 0, ∃ x : PN.complex.X 1,
        (1 : R) ⊗ₜ[S] x = u.1 ∧ g • y = (PN.complex.d 1 0).hom x := by
    obtain ⟨x, hx⟩ := hsurj_tmul u.1
    have h0 : (1 : R) ⊗ₜ[S] (PN.complex.d 1 0).hom x = 0 := by
      rw [← hdQ_tmul 0 1 x, hx]
      exact u.2
    obtain ⟨y, hy⟩ := (hone_tmul_zero_iff _).mp h0
    exact ⟨y, x, hx, hy⟩
  have hψ_well_def (u : Z1) (x₁ x₂ : PN.complex.X 1) (y₁ y₂ : PN.complex.X 0)
      (hx₁ : (1 : R) ⊗ₜ[S] x₁ = u.1) (hx₂ : (1 : R) ⊗ₜ[S] x₂ = u.1)
      (hy₁ : g • y₁ = (PN.complex.d 1 0).hom x₁)
      (hy₂ : g • y₂ = (PN.complex.d 1 0).hom x₂) :
      εP y₁ = εP y₂ := by
    have hdiff0 : (1 : R) ⊗ₜ[S] (x₁ - x₂) = 0 := by
      rw [TensorProduct.tmul_sub, hx₁, hx₂, sub_self]
    obtain ⟨z, hz⟩ := (hone_tmul_zero_iff _).mp hdiff0
    have hy_diff : y₁ - y₂ = (PN.complex.d 1 0).hom z := by
      apply hPN_reg 0
      dsimp only
      rw [smul_sub, hy₁, hy₂, ← map_sub, ← hz, map_smul]
    have hε0 : εP (y₁ - y₂) = 0 := by rw [hy_diff, hεP_comp z]
    rw [map_sub] at hε0
    exact sub_eq_zero.mp hε0
  let ψFun (u : Z1) : N := εP (Classical.choose (hZ1_exists_y u))
  have hψ_eq (u : Z1) (x : PN.complex.X 1) (y : PN.complex.X 0)
      (hx : (1 : R) ⊗ₜ[S] x = u.1) (hy : g • y = (PN.complex.d 1 0).hom x) :
      ψFun u = εP y := by
    have hspec := Classical.choose_spec (hZ1_exists_y u)
    obtain ⟨x0, hx0, hy0⟩ := hspec
    exact hψ_well_def u x0 x _ y hx0 hx hy0 hy
  let ψ : Z1 →ₗ[R] N :=
    { toFun := ψFun
      map_add' := fun u₁ u₂ => by
        obtain ⟨y₁, x₁, hx₁, hy₁⟩ := hZ1_exists_y u₁
        obtain ⟨y₂, x₂, hx₂, hy₂⟩ := hZ1_exists_y u₂
        rw [hψ_eq u₁ x₁ y₁ hx₁ hy₁, hψ_eq u₂ x₂ y₂ hx₂ hy₂, ← map_add]
        exact hψ_eq (u₁ + u₂) (x₁ + x₂) (y₁ + y₂)
          (by rw [TensorProduct.tmul_add, hx₁, hx₂]; rfl)
          (by rw [smul_add, map_add, hy₁, hy₂])
      map_smul' := fun r u => by
        obtain ⟨s, rfl⟩ := hsurj r
        obtain ⟨y, x, hx, hy⟩ := hZ1_exists_y u
        rw [hψ_eq u x y hx hy]
        change ψFun ((algebraMap S R s) • u) = (algebraMap S R s) • εP y
        rw [algebraMap_smul R s (εP y), ← map_smul]
        exact hψ_eq ((algebraMap S R s) • u) (s • x) (s • y)
          (by
            change (1 : R) ⊗ₜ[S] (s • x) = (algebraMap S R s) • u.1
            rw [← hx, ← TensorProduct.smul_tmul, Algebra.smul_def, mul_one,
              ← mul_one (algebraMap S R s), ← smul_eq_mul, ← TensorProduct.smul_tmul',
              smul_eq_mul, mul_one])
          (by rw [smul_comm, hy, map_smul]) }
  have hψ_surj : Function.Surjective ψ := fun n => by
    obtain ⟨y, rfl⟩ := hεP_surj n
    have hgy : εP (g • y) = 0 := by rw [map_smul]; exact hgN (εP y)
    obtain ⟨x, hx⟩ := hεP_exact (g • y) hgy
    have hu_mem : (1 : R) ⊗ₜ[S] x ∈ Z1 := by
      rw [LinearMap.mem_ker, hdQ_tmul, hx]
      exact (hone_tmul_zero_iff _).mpr ⟨y, rfl⟩
    refine ⟨⟨(1 : R) ⊗ₜ[S] x, hu_mem⟩, ?_⟩
    exact hψ_eq ⟨(1 : R) ⊗ₜ[S] x, hu_mem⟩ x y rfl hx.symm
  have hB1_eq_ker_ψ : B1 = LinearMap.ker ψ := by
    ext u
    constructor
    · rintro ⟨w, rfl⟩
      obtain ⟨z, rfl⟩ := hsurj_tmul w
      rw [LinearMap.mem_ker]
      have h1 : ψ (dQ1_to_Z1 (1 ⊗ₜ[S] z)) = εP 0 :=
        hψ_eq (dQ1_to_Z1 (1 ⊗ₜ[S] z)) ((PN.complex.d 2 1).hom z) 0 rfl
          (by rw [smul_zero, hPN_dd 0 z])
      rw [h1, map_zero]
    · intro hu
      rw [LinearMap.mem_ker] at hu
      obtain ⟨y, x, hx, hy⟩ := hZ1_exists_y u
      have hεy : εP y = 0 := (hψ_eq u x y hx hy).symm.trans hu
      obtain ⟨z, hz⟩ := hεP_exact y hεy
      have hdxz : (PN.complex.d 1 0).hom (x - g • z) = 0 := by
        rw [map_sub, map_smul, hz, hy, sub_self]
      obtain ⟨w, hw⟩ := hPN_exact 0 (x - g • z) hdxz
      refine ⟨1 ⊗ₜ[S] w, Subtype.ext ?_⟩
      change dQ 1 (1 ⊗ₜ[S] w) = u.1
      rw [hdQ_tmul, hw, TensorProduct.tmul_sub, (hone_tmul_zero_iff _).mpr ⟨z, rfl⟩, sub_zero, hx]
  -- Exactness of SES 1, SES 2, SES 3
  have hSES1 : LinearMap.range B0.subtype = LinearMap.ker εQ := by
    rw [Submodule.range_subtype]
    ext u
    exact ⟨by rintro ⟨v, rfl⟩; exact hεQ_comp v, fun hu => hεQ_exact u hu⟩
  have hSES2 : LinearMap.range Z1.subtype = LinearMap.ker (dQ 0).rangeRestrict := by
    rw [Submodule.range_subtype]
    ext u
    simp [Z1, LinearMap.mem_ker]
  have hSES3 : LinearMap.range B1.subtype = LinearMap.ker ψ := by
    rw [Submodule.range_subtype]
    exact hB1_eq_ker_ψ
  -- Step 4: Shifted complex Q_shift is a ProjectiveResolution of B1 over R
  let dQ_shift (n : ℕ) : ModuleCat.of R ((R ⊗[S] PN.complex.X (n + 3))) ⟶ ModuleCat.of R ((R ⊗[S] PN.complex.X (n + 2))) :=
    ModuleCat.ofHom (dQ (n + 2))
  have hdQ_shift_sq (n : ℕ) : (dQ_shift (n + 1) ≫ dQ_shift n) = 0 := by
    apply ModuleCat.hom_ext; apply LinearMap.ext; intro u; exact hdQ_sq (n + 2) u
  let Qshift : ChainComplex (ModuleCat.{0} R) ℕ :=
    ChainComplex.of (fun n => ModuleCat.of R ((R ⊗[S] PN.complex.X (n + 2)))) dQ_shift hdQ_shift_sq
  have hQshift_d (n : ℕ) : (Qshift.d (n + 1) n).hom = dQ (n + 2) := by
    change (ChainComplex.of.d (fun k => ModuleCat.of R ((R ⊗[S] PN.complex.X (k + 2)))) dQ_shift (n + 1) n).hom =
      dQ (n + 2)
    rw [ChainComplex.of_d]
    rfl
  let p2 : (R ⊗[S] PN.complex.X 2) →ₗ[R] B1 := dQ1_to_Z1.rangeRestrict
  have hp2_surj : Function.Surjective p2 := dQ1_to_Z1.surjective_rangeRestrict
  have hp2_comp (u : Qshift.X 1) : p2 ((Qshift.d 1 0).hom u) = 0 := by
    rw [hQshift_d 0]
    apply Subtype.ext; apply Subtype.ext
    exact hdQ_sq 1 u
  have hp2_exact (u : Qshift.X 0) (hu : p2 u = 0) :
      ∃ v : Qshift.X 1, (Qshift.d 1 0).hom v = u := by
    rw [hQshift_d 0]
    have h0 : dQ 1 u = 0 := congrArg (fun z : B1 => z.1.1) hu
    exact hQ_exact_ge2 0 u h0
  have hQshift_exact (n : ℕ) (u : Qshift.X (n + 1)) (hu : (Qshift.d (n + 1) n).hom u = 0) :
      ∃ v : Qshift.X (n + 2), (Qshift.d (n + 2) (n + 1)).hom v = u := by
    rw [hQshift_d n] at hu
    rw [hQshift_d (n + 1)]
    exact hQ_exact_ge2 (n + 1) u hu
  let PB1 : ProjectiveResolution (ModuleCat.of R B1) :=
    projectiveResolutionOfExact B1 Qshift (fun n => hQ_proj (n + 2)) p2
      hp2_surj hp2_comp hp2_exact hQshift_exact
  -- Step 5: S-linear isomorphism M ⊗[R] (R ⊗[S] PN.complex.X n) ≃ₗ[S] M ⊗[S] PN.complex.X n
  let eMQ (n : ℕ) : (M ⊗[R] (R ⊗[S] PN.complex.X n)) ≃ₗ[S] (M ⊗[S] PN.complex.X n) :=
    baseChangeTensorEquiv (S := S) (R := R) (M := M) (X := PN.complex.X n) hsurj
  have heMQ_comm (n : ℕ) (t : M ⊗[R] (R ⊗[S] PN.complex.X (n + 1))) :
      eMQ n (LinearMap.lTensor M (dQ n) t) =
        LinearMap.lTensor M (PN.complex.d (n + 1) n).hom (eMQ (n + 1) t) :=
    baseChangeTensorEquiv_comm (S := S) (R := R) (M := M) hsurj
      (PN.complex.d (n + 1) n).hom t
  -- Step 6: Express Tor^S(M, N) via M ⊗_R Q_•
  let FS := (tensoringLeft (ModuleCat.{0} S)).obj (ModuleCat.of S M)
  let KSN : ChainComplex (ModuleCat.{0} S) ℕ := (FS.mapHomologicalComplex _).obj PN.complex
  have hTorS_iso (i : ℕ) : Nonempty (torMod S M N i ≃ₗ[S] KSN.homology i) :=
    ⟨(PN.isoLeftDerivedObj FS i).toLinearEquiv⟩
  have hTorS_zero : Nonempty (torMod S M N 0 ≃ₗ[S] ((M ⊗[R] (R ⊗[S] PN.complex.X 0)) ⧸ LinearMap.range (LinearMap.lTensor M (dQ 0)))) := by
    obtain ⟨e1⟩ := hTorS_iso 0
    obtain ⟨e2⟩ := homology_zero_equiv_quot_range KSN
    let q : KSN.X 0 →ₗ[S] ((M ⊗[R] (R ⊗[S] PN.complex.X 0)) ⧸ LinearMap.range (LinearMap.lTensor M (dQ 0))) :=
      ((Submodule.mkQ (LinearMap.range (LinearMap.lTensor M (dQ 0)))).restrictScalars S).comp
        (eMQ 0).symm.toLinearMap
    have hq_surj : Function.Surjective q :=
      (Submodule.mkQ_surjective _).comp (eMQ 0).symm.surjective
    have hq_ker : LinearMap.ker q = LinearMap.range (KSN.d 1 0).hom := by
      ext y
      change Submodule.Quotient.mk ((eMQ 0).symm y) = 0 ↔ y ∈ LinearMap.range (KSN.d 1 0).hom
      rw [Submodule.Quotient.mk_eq_zero]
      constructor
      · rintro ⟨t, ht⟩
        let y' : M ⊗[S] PN.complex.X 0 := y
        refine ⟨eMQ 1 t, ?_⟩
        change LinearMap.lTensor M (PN.complex.d 1 0).hom (eMQ 1 t) = y'
        rw [← heMQ_comm 0 t, ht, (eMQ 0).apply_symm_apply y']
      · rintro ⟨z, rfl⟩
        let z' : M ⊗[S] PN.complex.X 1 := z
        refine ⟨(eMQ 1).symm z', ?_⟩
        apply (eMQ 0).injective
        rw [heMQ_comm 0, (eMQ 1).apply_symm_apply z']
        exact ((eMQ 0).apply_symm_apply (LinearMap.lTensor M (PN.complex.d 1 0).hom z')).symm
    let eQ0 : (KSN.X 0 ⧸ LinearMap.range (KSN.d 1 0).hom) ≃ₗ[S]
        ((M ⊗[R] (R ⊗[S] PN.complex.X 0)) ⧸ LinearMap.range (LinearMap.lTensor M (dQ 0))) :=
      (Submodule.quotEquivOfEq _ _ hq_ker.symm).trans (q.quotKerEquivOfSurjective hq_surj)
    exact ⟨e1.trans (e2.trans eQ0)⟩

  -- S-linear homology equivalences for Tor^S(M, N)_(k+1)
  let K_R (k : ℕ) := LinearMap.ker (LinearMap.lTensor M (dQ k))
  let R_R (k : ℕ) : Submodule R (K_R k) :=
    (LinearMap.range (LinearMap.lTensor M (dQ (k + 1)))).comap (K_R k).subtype
  have hTorS_succ_equiv (k : ℕ) :
      Nonempty (torMod S M N (k + 1) ≃ₗ[S] (K_R k ⧸ R_R k)) := by
    obtain ⟨e1⟩ := hTorS_iso (k + 1)
    let fS := (LinearMap.lTensor M (dQ (k + 1))).restrictScalars S
    let gS := (LinearMap.lTensor M (dQ k)).restrictScalars S
    obtain ⟨e2⟩ := homology_succ_equiv_of_iso KSN k (eMQ k) (eMQ (k + 1)) (eMQ (k + 2))
      fS gS (fun t => heMQ_comm (k + 1) t) (fun t => heMQ_comm k t)
    let q : LinearMap.ker gS →ₗ[S] (K_R k ⧸ R_R k) :=
      { toFun := fun u => Submodule.Quotient.mk ⟨u.1, u.2⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hq_surj : Function.Surjective q := fun w => by
      obtain ⟨⟨u, hu⟩, rfl⟩ := Submodule.Quotient.mk_surjective (R_R k) w
      exact ⟨⟨u, hu⟩, rfl⟩
    have hq_ker : LinearMap.ker q = (LinearMap.range fS).comap (LinearMap.ker gS).subtype := by
      ext ⟨u, hu⟩
      change Submodule.Quotient.mk (⟨u, hu⟩ : K_R k) = 0 ↔ u ∈ LinearMap.range fS
      rw [Submodule.Quotient.mk_eq_zero]
      rfl
    let e3 : (LinearMap.ker gS ⧸ (LinearMap.range fS).comap (LinearMap.ker gS).subtype) ≃ₗ[S]
        (K_R k ⧸ R_R k) :=
      (Submodule.quotEquivOfEq _ _ hq_ker.symm).trans (q.quotKerEquivOfSurjective hq_surj)
    exact ⟨e1.trans (e2.trans e3)⟩
  let eTorS_succ (k : ℕ) : torMod S M N (k + 1) ≃ₗ[S] (K_R k ⧸ R_R k) :=
    Classical.choice (hTorS_succ_equiv k)
  -- Compare Tor^R_{m+1}(M, B1) with K_R (m+2) / R_R (m+2)
  let FR := (tensoringLeft (ModuleCat.{0} R)).obj (ModuleCat.of R M)
  let KRB1 : ChainComplex (ModuleCat.{0} R) ℕ := (FR.mapHomologicalComplex _).obj PB1.complex
  have hTorB1_equiv (m : ℕ) :
      Nonempty (torMod R M B1 (m + 1) ≃ₗ[R] (K_R (m + 2) ⧸ R_R (m + 2))) := by
    have eR1 : torMod R M B1 (m + 1) ≃ₗ[R] KRB1.homology (m + 1) :=
      (PB1.isoLeftDerivedObj FR (m + 1)).toLinearEquiv
    obtain ⟨eR2⟩ := homology_succ_equiv_of_iso KRB1 m
      (LinearEquiv.refl R (M ⊗[R] (R ⊗[S] PN.complex.X (m + 2))))
      (LinearEquiv.refl R (M ⊗[R] (R ⊗[S] PN.complex.X (m + 3))))
      (LinearEquiv.refl R (M ⊗[R] (R ⊗[S] PN.complex.X (m + 4))))
      (LinearMap.lTensor M (dQ (m + 3)))
      (LinearMap.lTensor M (dQ (m + 2)))
      (fun t => by
        change LinearMap.lTensor M (dQ (m + 3)) t = LinearMap.lTensor M (Qshift.d (m + 2) (m + 1)).hom t
        rw [hQshift_d (m + 1)])
      (fun t => by
        change LinearMap.lTensor M (dQ (m + 2)) t = LinearMap.lTensor M (Qshift.d (m + 1) m).hom t
        rw [hQshift_d m])
    exact ⟨eR1.trans eR2⟩
  let eB1_S (m : ℕ) : ((ModuleCat.restrictScalars f).obj (torMod R M B1 (m + 1))) ≃ₗ[S] A (m + 3) :=
    (equivSLinear f hf (Classical.choice (hTorB1_equiv m))).trans (eTorS_succ (m + 2)).symm
  -- Long exact sequences for SES 1, SES 2, SES 3
  obtain ⟨δ1, hδ1_1, hδ1_2, hδ1_3⟩ := horseshoe_tor_les (R := R) M (A := B0) B0.subtype εQ
    (Submodule.subtype_injective B0) hεQ_surj hSES1
  obtain ⟨δ2, hδ2_1, hδ2_2, hδ2_3⟩ := horseshoe_tor_les (R := R) M (A := Z1) (C := B0)
    Z1.subtype (dQ 0).rangeRestrict
    (Submodule.subtype_injective Z1) (dQ 0).surjective_rangeRestrict hSES2
  obtain ⟨δ3, hδ3_1, hδ3_2, hδ3_3⟩ := horseshoe_tor_les (R := R) M (A := B1) (B := Z1) (C := N)
    B1.subtype ψ (Submodule.subtype_injective B1) hψ_surj hSES3
  have hTorB0_equiv (k : ℕ) :
      Nonempty (torMod R M N (k + 2) ≃ₗ[R] torMod R M B0 (k + 1)) := by
    let _ := hQ_proj 0
    have _ : Subsingleton (torMod R M ((R ⊗[S] PN.complex.X 0)) (k + 1)) :=
      tor_succ_subsingleton_of_projective M ((R ⊗[S] PN.complex.X 0)) k
    have _ : Subsingleton (torMod R M ((R ⊗[S] PN.complex.X 0)) (k + 2)) :=
      tor_succ_subsingleton_of_projective M ((R ⊗[S] PN.complex.X 0)) (k + 1)
    have hbij : Function.Bijective (δ1 (k + 1)) := by
      constructor
      · rw [injective_iff_map_eq_zero]
        intro x hx
        obtain ⟨z, hz⟩ := (hδ1_3 (k + 1) x).mp hx
        rw [Subsingleton.elim z 0, map_zero] at hz
        exact hz.symm
      · intro y
        exact (hδ1_1 (k + 1) y).mp (Subsingleton.elim _ _)
    exact ⟨LinearEquiv.ofBijective (δ1 (k + 1)) hbij⟩
  have hTorZ1_equiv (k : ℕ) :
      Nonempty (torMod R M N (k + 3) ≃ₗ[R] torMod R M Z1 (k + 1)) := by
    let _ := hQ_proj 1
    have _ : Subsingleton (torMod R M ((R ⊗[S] PN.complex.X 1)) (k + 1)) :=
      tor_succ_subsingleton_of_projective M ((R ⊗[S] PN.complex.X 1)) k
    have _ : Subsingleton (torMod R M ((R ⊗[S] PN.complex.X 1)) (k + 2)) :=
      tor_succ_subsingleton_of_projective M ((R ⊗[S] PN.complex.X 1)) (k + 1)
    have hbij : Function.Bijective (δ2 (k + 1)) := by
      constructor
      · rw [injective_iff_map_eq_zero]
        intro x hx
        obtain ⟨z, hz⟩ := (hδ2_3 (k + 1) x).mp hx
        rw [Subsingleton.elim z 0, map_zero] at hz
        exact hz.symm
      · intro y
        exact (hδ2_1 (k + 1) y).mp (Subsingleton.elim _ _)
    obtain ⟨e1⟩ := hTorB0_equiv (k + 1)
    exact ⟨e1.trans (LinearEquiv.ofBijective (δ2 (k + 1)) hbij)⟩
  let eZ (m : ℕ) : torMod R M N (m + 3) ≃ₗ[R] torMod R M Z1 (m + 1) :=
    Classical.choice (hTorZ1_equiv m)
  -- Low-degree maps α, β, γ, Lp1, Lp2
  let α : (M ⊗[R] B1) →ₗ[R] (M ⊗[R] Z1) := LinearMap.lTensor M B1.subtype
  let β : (M ⊗[R] Z1) →ₗ[R] (M ⊗[R] (R ⊗[S] PN.complex.X 1)) := LinearMap.lTensor M Z1.subtype
  let γ : (M ⊗[R] B0) →ₗ[R] (M ⊗[R] (R ⊗[S] PN.complex.X 0)) := LinearMap.lTensor M B0.subtype
  let Lp1 : (M ⊗[R] (R ⊗[S] PN.complex.X 1)) →ₗ[R] (M ⊗[R] B0) := LinearMap.lTensor M (dQ 0).rangeRestrict
  let Lp2 : (M ⊗[R] (R ⊗[S] PN.complex.X 2)) →ₗ[R] (M ⊗[R] B1) := LinearMap.lTensor M p2
  have hLp1_surj : Function.Surjective Lp1 :=
    LinearMap.lTensor_surjective M (dQ 0).surjective_rangeRestrict
  have hLp2_surj : Function.Surjective Lp2 :=
    LinearMap.lTensor_surjective M hp2_surj
  have hd0_fac : LinearMap.lTensor M (dQ 0) = γ.comp Lp1 := by
    rw [← LinearMap.lTensor_comp]; rfl
  have hd1_fac : LinearMap.lTensor M (dQ 1) = (β.comp α).comp Lp2 := by
    rw [LinearMap.comp_assoc, ← LinearMap.lTensor_comp, ← LinearMap.lTensor_comp]; rfl
  have hker_Lp1 : LinearMap.ker Lp1 = LinearMap.range β :=
    LinearMap.exact_iff.mp (lTensor_exact M (LinearMap.exact_iff.mpr hSES2.symm)
      (dQ 0).surjective_rangeRestrict)
  have hker_Lp2 : LinearMap.ker Lp2 = LinearMap.range (LinearMap.lTensor M (dQ 2)) := by
    have hex_d2 : Function.Exact (dQ 2) p2 := fun u => by
      constructor
      · intro hu
        have h0 : dQ 1 u = 0 := congrArg (fun z : B1 => z.1.1) hu
        exact hQ_exact_ge2 0 u h0
      · rintro ⟨v, rfl⟩
        apply Subtype.ext; apply Subtype.ext; exact hdQ_sq 1 v
    exact LinearMap.exact_iff.mp (lTensor_exact M hex_d2 hp2_surj)
  have hrange_d1 : LinearMap.range (LinearMap.lTensor M (dQ 1)) = LinearMap.range (β.comp α) := by
    ext y
    constructor
    · rintro ⟨u, rfl⟩; exact ⟨Lp2 u, (LinearMap.congr_fun hd1_fac u).symm⟩
    · rintro ⟨b, rfl⟩; obtain ⟨u, rfl⟩ := hLp2_surj b; exact ⟨u, LinearMap.congr_fun hd1_fac u⟩
  -- Equivalence zeroEquiv : A 0 ≃ₗ[S] BS 0
  have hzeroEquiv : Nonempty (A 0 ≃ₗ[S] BS 0) := by
    obtain ⟨eS0⟩ := hTorS_zero
    have hrange_d0 : LinearMap.range (LinearMap.lTensor M (dQ 0)) = LinearMap.range γ := by
      rw [hd0_fac, LinearMap.range_comp, LinearMap.range_eq_top.mpr hLp1_surj, Submodule.map_top]
    have hsurj_ε : Function.Surjective (LinearMap.lTensor M εQ) :=
      LinearMap.lTensor_surjective M hεQ_surj
    have hker_ε : LinearMap.ker (LinearMap.lTensor M εQ) = LinearMap.range γ :=
      LinearMap.exact_iff.mp (lTensor_exact M (LinearMap.exact_iff.mpr hSES1.symm) hεQ_surj)
    let eR0 : ((M ⊗[R] (R ⊗[S] PN.complex.X 0)) ⧸ LinearMap.range (LinearMap.lTensor M (dQ 0))) ≃ₗ[R]
        (M ⊗[R] N) :=
      (Submodule.quotEquivOfEq _ _ (hrange_d0.trans hker_ε.symm)).trans
        ((LinearMap.lTensor M εQ).quotKerEquivOfSurjective hsurj_ε)
    let eBS0 : BS 0 ≃ₗ[S]
        ((M ⊗[R] (R ⊗[S] PN.complex.X 0)) ⧸ LinearMap.range (LinearMap.lTensor M (dQ 0))) :=
      equivSLinear f hf ((torZeroEquiv R M N).trans eR0.symm)
    exact ⟨eS0.trans eBS0.symm⟩
  -- Equivalences for BS 0, BS 1, BS 2, A 2
  let eCoker : ((M ⊗[R] Z1) ⧸ LinearMap.range α) ≃ₗ[R] (M ⊗[R] N) := by
    have hsurj_ψ : Function.Surjective (LinearMap.lTensor M ψ) :=
      LinearMap.lTensor_surjective M hψ_surj
    have hker_ψ : LinearMap.ker (LinearMap.lTensor M ψ) = LinearMap.range α :=
      LinearMap.exact_iff.mp (lTensor_exact M (LinearMap.exact_iff.mpr hSES3.symm) hψ_surj)
    exact (Submodule.quotEquivOfEq _ _ hker_ψ.symm).trans
      ((LinearMap.lTensor M ψ).quotKerEquivOfSurjective hsurj_ψ)
  let eB0_coker : BS 0 ≃ₗ[S] ((M ⊗[R] Z1) ⧸ LinearMap.range α) :=
    equivSLinear f hf ((torZeroEquiv R M N).trans eCoker.symm)
  let eR_kerγ : torMod R M N 1 ≃ₗ[R] LinearMap.ker γ := by
    let _ := hQ_proj 0
    have _ : Subsingleton (torMod R M ((R ⊗[S] PN.complex.X 0)) 1) :=
      tor_succ_subsingleton_of_projective M ((R ⊗[S] PN.complex.X 0)) 0
    have hmap_ker (x : torMod R M N 1) :
        torZeroEquiv R M B0 (δ1 0 x) ∈ LinearMap.ker γ := by
      rw [LinearMap.mem_ker]
      change LinearMap.lTensor M B0.subtype (torZeroEquiv R M B0 (δ1 0 x)) = 0
      rw [← torZeroEquiv_naturality, (hδ1_1 0 (δ1 0 x)).mpr ⟨x, rfl⟩, map_zero]
    let φ := LinearMap.codRestrict (LinearMap.ker γ)
      ((torZeroEquiv R M B0).toLinearMap.comp (δ1 0)) hmap_ker
    have hbij : Function.Bijective φ := by
      constructor
      · rw [injective_iff_map_eq_zero]
        intro x hx
        have h0 : δ1 0 x = 0 := (torZeroEquiv R M B0).injective
          ((congrArg Subtype.val hx).trans (map_zero _).symm)
        obtain ⟨z, hz⟩ := (hδ1_3 0 x).mp h0
        rw [Subsingleton.elim z 0, map_zero] at hz
        exact hz.symm
      · rintro ⟨y, hy⟩
        have h0 : torMap M B0.subtype 0 ((torZeroEquiv R M B0).symm y) = 0 := by
          apply (torZeroEquiv R M _).injective
          rw [map_zero, torZeroEquiv_naturality, (torZeroEquiv R M B0).apply_symm_apply]
          exact hy
        obtain ⟨x, hx⟩ := (hδ1_1 0 _).mp h0
        refine ⟨x, Subtype.ext ?_⟩
        change torZeroEquiv R M B0 (δ1 0 x) = y
        rw [hx, (torZeroEquiv R M B0).apply_symm_apply]
    exact LinearEquiv.ofBijective φ hbij
  let eB1_kerγ : BS 1 ≃ₗ[S] LinearMap.ker γ := equivSLinear f hf eR_kerγ
  let eR_kerβ : torMod R M N 2 ≃ₗ[R] LinearMap.ker β := by
    let _ := hQ_proj 1
    have _ : Subsingleton (torMod R M ((R ⊗[S] PN.complex.X 1)) 1) :=
      tor_succ_subsingleton_of_projective M ((R ⊗[S] PN.complex.X 1)) 0
    let eB0_0 := Classical.choice (hTorB0_equiv 0)
    have hmap_ker (x : torMod R M B0 1) :
        torZeroEquiv R M Z1 (δ2 0 x) ∈ LinearMap.ker β := by
      rw [LinearMap.mem_ker]
      change LinearMap.lTensor M Z1.subtype (torZeroEquiv R M Z1 (δ2 0 x)) = 0
      rw [← torZeroEquiv_naturality, (hδ2_1 0 (δ2 0 x)).mpr ⟨x, rfl⟩, map_zero]
    let φ := LinearMap.codRestrict (LinearMap.ker β)
      ((torZeroEquiv R M Z1).toLinearMap.comp (δ2 0)) hmap_ker
    have hbij : Function.Bijective φ := by
      constructor
      · rw [injective_iff_map_eq_zero]
        intro x hx
        have h0 : δ2 0 x = 0 := (torZeroEquiv R M Z1).injective
          ((congrArg Subtype.val hx).trans (map_zero _).symm)
        obtain ⟨z, hz⟩ := (hδ2_3 0 x).mp h0
        rw [Subsingleton.elim z 0, map_zero] at hz
        exact hz.symm
      · rintro ⟨y, hy⟩
        have h0 : torMap M Z1.subtype 0 ((torZeroEquiv R M Z1).symm y) = 0 := by
          apply (torZeroEquiv R M _).injective
          rw [map_zero, torZeroEquiv_naturality, (torZeroEquiv R M Z1).apply_symm_apply]
          exact hy
        obtain ⟨x, hx⟩ := (hδ2_1 0 _).mp h0
        refine ⟨x, Subtype.ext ?_⟩
        change torZeroEquiv R M Z1 (δ2 0 x) = y
        rw [hx, (torZeroEquiv R M Z1).apply_symm_apply]
    exact eB0_0.trans (LinearEquiv.ofBijective φ hbij)
  let eB2_kerβ : BS 2 ≃ₗ[S] LinearMap.ker β := equivSLinear f hf eR_kerβ
  let eA2_kerβα : A 2 ≃ₗ[S] LinearMap.ker (β.comp α) := by
    let φ : K_R 1 →ₗ[R] LinearMap.ker (β.comp α) :=
      LinearMap.codRestrict (LinearMap.ker (β.comp α)) (Lp2.comp (K_R 1).subtype) (fun u => by
        change (β.comp α) (Lp2 u.1) = 0
        exact (LinearMap.congr_fun hd1_fac u.1).symm.trans u.2)
    have hφ_surj : Function.Surjective φ := by
      rintro ⟨b, hb⟩
      obtain ⟨u, rfl⟩ := hLp2_surj b
      exact ⟨⟨u, (LinearMap.congr_fun hd1_fac u).trans hb⟩, rfl⟩
    have hφ_ker : LinearMap.ker φ = R_R 1 := by
      ext ⟨u, hu⟩
      rw [LinearMap.mem_ker, Subtype.ext_iff]
      change Lp2 u = 0 ↔ u ∈ LinearMap.range (LinearMap.lTensor M (dQ 2))
      rw [← LinearMap.mem_ker, hker_Lp2]
    let eR : (K_R 1 ⧸ R_R 1) ≃ₗ[R] LinearMap.ker (β.comp α) :=
      (Submodule.quotEquivOfEq _ _ hφ_ker.symm).trans (φ.quotKerEquivOfSurjective hφ_surj)
    exact (eTorS_succ 1).trans (eR.restrictScalars S)
  -- Concrete low-degree core maps and their exactness
  have hβ_le_K0 : LinearMap.range β ≤ K_R 0 := by
    rw [← hker_Lp1]
    intro u hu
    change LinearMap.lTensor M (dQ 0) u = 0
    rw [LinearMap.congr_fun hd0_fac u, LinearMap.comp_apply, LinearMap.mem_ker.mp hu, map_zero]
  let β_to_H1 : ((M ⊗[R] Z1) ⧸ LinearMap.range α) →ₗ[R] (K_R 0 ⧸ R_R 0) :=
    (LinearMap.range α).liftQ
      ((R_R 0).mkQ.comp (LinearMap.codRestrict (K_R 0) β (fun z => hβ_le_K0 ⟨z, rfl⟩)))
      (by
        intro z hz
        rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
          Submodule.Quotient.mk_eq_zero]
        obtain ⟨u, rfl⟩ := hz
        change β (α u) ∈ LinearMap.range (LinearMap.lTensor M (dQ 1))
        rw [hrange_d1]
        exact ⟨u, rfl⟩)
  let g1 : (K_R 0 ⧸ R_R 0) →ₗ[R] LinearMap.ker γ :=
    (R_R 0).liftQ
      (LinearMap.codRestrict (LinearMap.ker γ) (Lp1.comp (K_R 0).subtype) (fun u => by
        change γ (Lp1 u.1) = 0
        exact (LinearMap.congr_fun hd0_fac u.1).symm.trans u.2))
      (by
        rintro ⟨u, hu⟩ huR
        rw [LinearMap.mem_ker]
        apply Subtype.ext
        change Lp1 u = 0
        have hmem : u ∈ LinearMap.range (β.comp α) := hrange_d1 ▸ huR
        obtain ⟨b, rfl⟩ := hmem
        have : β (α b) ∈ LinearMap.range β := ⟨α b, rfl⟩
        rw [← hker_Lp1] at this
        exact this)
  have hg1_surj : Function.Surjective g1 := by
    rintro ⟨b, hb⟩
    obtain ⟨u, rfl⟩ := hLp1_surj b
    exact ⟨Submodule.Quotient.mk ⟨u, (LinearMap.congr_fun hd0_fac u).trans hb⟩, rfl⟩
  have hex_H1 : Function.Exact β_to_H1 g1 := by
    intro y
    obtain ⟨⟨u, hu⟩, rfl⟩ := Submodule.Quotient.mk_surjective (R_R 0) y
    constructor
    · intro hy
      have h0 : Lp1 u = 0 := congrArg Subtype.val hy
      have huβ : u ∈ LinearMap.range β := by rw [← hker_Lp1]; exact h0
      obtain ⟨z, rfl⟩ := huβ
      exact ⟨Submodule.Quotient.mk z, rfl⟩
    · rintro ⟨w, hw⟩
      rw [← hw]
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective (LinearMap.range α) w
      apply Subtype.ext
      change Lp1 (β z) = 0
      rw [← LinearMap.mem_ker, hker_Lp1]
      exact ⟨z, rfl⟩
  let partial0 : LinearMap.ker β →ₗ[R] ((M ⊗[R] Z1) ⧸ LinearMap.range α) :=
    (LinearMap.range α).mkQ.comp (LinearMap.ker β).subtype
  have hex_coker : Function.Exact partial0 β_to_H1 := by
    intro w
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective (LinearMap.range α) w
    constructor
    · intro hw
      have hmem : β z ∈ LinearMap.range (LinearMap.lTensor M (dQ 1)) :=
        (Submodule.Quotient.mk_eq_zero (R_R 0)).mp hw
      rw [hrange_d1] at hmem
      obtain ⟨u, hu⟩ := hmem
      have hz' : z - α u ∈ LinearMap.ker β := by
        rw [LinearMap.mem_ker, map_sub, ← LinearMap.comp_apply β α u, hu, sub_self]
      refine ⟨⟨z - α u, hz'⟩, ?_⟩
      change Submodule.Quotient.mk (z - α u) = Submodule.Quotient.mk z
      rw [Submodule.Quotient.eq]
      exact ⟨-u, by rw [map_neg]; abel⟩
    · rintro ⟨⟨z', hz'⟩, hzw⟩
      rw [← hzw]
      change Submodule.Quotient.mk (⟨β z', _⟩ : K_R 0) = 0
      rw [Submodule.Quotient.mk_eq_zero]
      change β z' ∈ LinearMap.range (LinearMap.lTensor M (dQ 1))
      rw [LinearMap.mem_ker.mp hz']
      exact zero_mem _
  let α_ker : LinearMap.ker (β.comp α) →ₗ[R] LinearMap.ker β :=
    LinearMap.codRestrict (LinearMap.ker β) (α.comp (LinearMap.ker (β.comp α)).subtype)
      (fun u => u.2)
  have hex_kerβ : Function.Exact α_ker partial0 := by
    rintro ⟨z, hz⟩
    constructor
    · intro hp0
      have hmem : z ∈ LinearMap.range α := (Submodule.Quotient.mk_eq_zero _).mp hp0
      obtain ⟨u, rfl⟩ := hmem
      exact ⟨⟨u, hz⟩, rfl⟩
    · rintro ⟨⟨u, hu⟩, huz⟩
      have hu_eq : α u = z := congrArg Subtype.val huz
      exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨u, hu_eq⟩
  let δ3_to_ker : torMod R M N 1 →ₗ[R] LinearMap.ker (β.comp α) :=
    LinearMap.codRestrict (LinearMap.ker (β.comp α))
      ((torZeroEquiv R M B1).toLinearMap.comp (δ3 0))
      (fun x => by
        rw [LinearMap.mem_ker, LinearMap.comp_apply]
        have hα0 : α (torZeroEquiv R M B1 (δ3 0 x)) = 0 := by
          change LinearMap.lTensor M B1.subtype (torZeroEquiv R M B1 (δ3 0 x)) = 0
          rw [← torZeroEquiv_naturality, (hδ3_1 0 (δ3 0 x)).mpr ⟨x, rfl⟩, map_zero]
        change β (α (torZeroEquiv R M B1 (δ3 0 x))) = 0
        rw [hα0, map_zero])
  have hex_kerβα : Function.Exact δ3_to_ker α_ker := by
    rintro ⟨u, hu⟩
    constructor
    · intro hα0
      have hu0 : α u = 0 := congrArg Subtype.val hα0
      have ht0 : torMap M B1.subtype 0 ((torZeroEquiv R M B1).symm u) = 0 := by
        apply (torZeroEquiv R M Z1).injective
        rw [map_zero, torZeroEquiv_naturality, (torZeroEquiv R M B1).apply_symm_apply]
        exact hu0
      obtain ⟨x, hx⟩ := (hδ3_1 0 _).mp ht0
      refine ⟨x, Subtype.ext ?_⟩
      change torZeroEquiv R M B1 (δ3 0 x) = u
      rw [hx, (torZeroEquiv R M B1).apply_symm_apply]
    · rintro ⟨x, hx⟩
      rw [← hx]
      apply Subtype.ext
      change LinearMap.lTensor M B1.subtype (torZeroEquiv R M B1 (δ3 0 x)) = 0
      rw [← torZeroEquiv_naturality, (hδ3_1 0 (δ3 0 x)).mpr ⟨x, rfl⟩, map_zero]
  have hex_B1 : Function.Exact ((torMap M ψ 1).comp (eZ 0).toLinearMap) δ3_to_ker := by
    intro x
    have h0_iff : δ3_to_ker x = 0 ↔ δ3 0 x = 0 := by
      constructor
      · intro h
        exact (torZeroEquiv R M B1).injective
          ((congrArg Subtype.val h).trans (map_zero _).symm)
      · intro h
        apply Subtype.ext
        change torZeroEquiv R M B1 (δ3 0 x) = 0
        rw [h, map_zero]
    rw [h0_iff]
    constructor
    · intro hx
      obtain ⟨z, hz⟩ := (hδ3_3 0 x).mp hx
      exact ⟨(eZ 0).symm z, by simp [hz]⟩
    · rintro ⟨w, rfl⟩
      exact (hδ3_3 0 _).mpr ⟨eZ 0 w, rfl⟩
  -- Assemble the four families of S-linear maps
  let fromQuot : ∀ i, BS i →ₗ[S] A (i + 1)
    | 0 => (eTorS_succ 0).symm.toLinearMap.comp ((β_to_H1.restrictScalars S).comp eB0_coker.toLinearMap)
    | 1 => eA2_kerβα.symm.toLinearMap.comp (toSLinear f hf δ3_to_ker)
    | m + 2 => (eB1_S m).toLinearMap.comp (((ModuleCat.restrictScalars f).map (ModuleCat.ofHom (δ3 (m + 1)))).hom)
  let toQuot : ∀ i, A (i + 1) →ₗ[S] BS (i + 1)
    | 0 => eB1_kerγ.symm.toLinearMap.comp ((g1.restrictScalars S).comp (eTorS_succ 0).toLinearMap)
    | 1 => eB2_kerβ.symm.toLinearMap.comp ((α_ker.restrictScalars S).comp eA2_kerβα.toLinearMap)
    | m + 2 => (((ModuleCat.restrictScalars f).map
        (ModuleCat.ofHom ((eZ m).symm.toLinearMap.comp (torMap M B1.subtype (m + 1))))).hom).comp
        (eB1_S m).symm.toLinearMap
  let connect : ∀ i, BS (i + 2) →ₗ[S] BS i
    | 0 => eB0_coker.symm.toLinearMap.comp ((partial0.restrictScalars S).comp eB2_kerβ.toLinearMap)
    | m + 1 => ((ModuleCat.restrictScalars f).map
        (ModuleCat.ofHom ((torMap M ψ (m + 1)).comp (eZ m).toLinearMap))).hom
  refine ⟨Classical.choice hzeroEquiv, fromQuot, toQuot, connect, ?_, ?_, ?_, ?_⟩
  · intro i
    match i with
    | 0 =>
      exact exact_of_surj_inj eB0_coker eB0_coker.surjective (eTorS_succ 0).symm.toEquiv
        eB1_kerγ.symm (fun x => eB1_kerγ.symm.map_eq_zero_iff)
        β_to_H1 g1 hex_H1 (fromQuot 0) (toQuot 0)
        (fun _ => rfl) (fun x => by simp [toQuot])
    | 1 =>
      exact exact_of_surj_inj id Function.surjective_id eA2_kerβα.symm.toEquiv
        eB2_kerβ.symm (fun x => eB2_kerβ.symm.map_eq_zero_iff)
        δ3_to_ker α_ker hex_kerβα (fromQuot 1) (toQuot 1)
        (fun _ => rfl) (fun x => by simp [toQuot])
    | m + 2 =>
      exact exact_of_surj_inj id Function.surjective_id (eB1_S m).toEquiv
        (eZ m).symm (fun x => (eZ m).symm.map_eq_zero_iff)
        (δ3 (m + 1)) (torMap M B1.subtype (m + 1)) (hδ3_1 (m + 1))
        (fromQuot (m + 2)) (toQuot (m + 2))
        (fun _ => rfl) (fun _ => rfl)
  · intro i
    match i with
    | 0 =>
      exact exact_of_surj_inj eA2_kerβα eA2_kerβα.surjective eB2_kerβ.symm.toEquiv
        eB0_coker.symm (fun x => eB0_coker.symm.map_eq_zero_iff)
        α_ker partial0 hex_kerβ (toQuot 1) (connect 0)
        (fun _ => rfl) (fun x => by simp [connect])
    | m + 1 =>
      exact exact_of_surj_inj (eB1_S m).symm (eB1_S m).symm.surjective (eZ m).symm.toEquiv
        id (fun _ => Iff.rfl)
        (torMap M B1.subtype (m + 1)) (torMap M ψ (m + 1)) (hδ3_2 (m + 1))
        (toQuot (m + 2)) (connect (m + 1))
        (fun _ => rfl)
        (fun x => by
          change torMap M ψ (m + 1) (eZ m x) = torMap M ψ (m + 1) ((eZ m).symm.toEquiv.symm x)
          rfl)
  · intro i
    match i with
    | 0 =>
      exact exact_of_surj_inj eB2_kerβ eB2_kerβ.surjective eB0_coker.symm.toEquiv
        (eTorS_succ 0).symm (fun x => (eTorS_succ 0).symm.map_eq_zero_iff)
        partial0 β_to_H1 hex_coker (connect 0) (fromQuot 0)
        (fun _ => rfl) (fun x => by simp [fromQuot])
    | 1 =>
      exact exact_of_surj_inj id Function.surjective_id (Equiv.refl _)
        eA2_kerβα.symm (fun x => eA2_kerβα.symm.map_eq_zero_iff)
        ((torMap M ψ 1).comp (eZ 0).toLinearMap) δ3_to_ker hex_B1
        (connect 1) (fromQuot 1)
        (fun _ => rfl) (fun _ => rfl)
    | m + 2 =>
      exact exact_of_surj_inj (eZ (m + 1)) (eZ (m + 1)).surjective (Equiv.refl _)
        (eB1_S m) (fun x => (eB1_S m).map_eq_zero_iff)
        (torMap M ψ (m + 2)) (δ3 (m + 1)) (hδ3_3 (m + 1))
        (connect (m + 2)) (fromQuot (m + 2))
        (fun _ => rfl) (fun _ => rfl)
  · exact eB1_kerγ.symm.surjective.comp (hg1_surj.comp (eTorS_succ 0).surjective)

noncomputable def quotMapLinearEquiv {S : Type} [CommRing S] (I P : Ideal S) (hIP : I ≤ P) :
    let f := Ideal.Quotient.mk I
    let R := S ⧸ I
    let _ : Module R (S ⧸ P) :=
      Module.compHom (S ⧸ P) (Ideal.Quotient.lift I (Module.toAddMonoidEnd S (S ⧸ P))
        (fun a ha => AddMonoidHom.ext fun m => by
          obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective m
          change Ideal.Quotient.mk P (a * s) = 0
          exact Ideal.Quotient.eq_zero_iff_mem.mpr (P.mul_mem_right s (hIP ha))))
    (S ⧸ P) ≃ₗ[R] (R ⧸ P.map f) := by
  intro f R _
  let fwd : S ⧸ P →+* R ⧸ P.map f :=
    Ideal.Quotient.lift P ((Ideal.Quotient.mk (P.map f)).comp f) (fun a ha =>
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem f ha))
  let π : R →+* S ⧸ P :=
    Ideal.Quotient.lift I (Ideal.Quotient.mk P) (fun a ha =>
      Ideal.Quotient.eq_zero_iff_mem.mpr (hIP ha))
  let bwd : R ⧸ P.map f →+* S ⧸ P :=
    Ideal.Quotient.lift (P.map f) π (fun r hr => by
      rw [Ideal.mem_map_iff_of_surjective f Ideal.Quotient.mk_surjective] at hr
      obtain ⟨a, haP, rfl⟩ := hr
      exact Ideal.Quotient.eq_zero_iff_mem.mpr haP)
  refine
    { toFun := fwd
      invFun := bwd
      map_add' := fwd.map_add
      map_smul' := fun r x => by
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
        obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
        change fwd (Ideal.Quotient.mk P (a * s)) =
          Ideal.Quotient.mk (P.map f) (f a * f s)
        rw [← map_mul f]
        rfl
      left_inv := fun x => by
        obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
        rfl
      right_inv := fun y => by
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
        obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective r
        rfl }

theorem serre_h2_main :
    OMA.R_SerreMultiplicityConjectures_supportDim_add_supportDim_le_ringKrullDim_R1_H4_R1.H2 := by
  intro S _ _ g _ hg_ne _ P Q hgP hgQ
  dsimp only
  let _ : IsDomain S := isDomain_of_isRegularLocalRing S
  let I : Ideal S := Ideal.span {g}
  let f := Ideal.Quotient.mk I
  let R := S ⧸ I
  have hI_le_P : I ≤ P := Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hgP)
  have hI_le_Q : I ≤ Q := Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hgQ)
  have hM_annP : ∀ a ∈ P, ∀ m : S ⧸ P, a • m = 0 := fun a ha m => by
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective m
    change Ideal.Quotient.mk P (a * s) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (P.mul_mem_right s ha)
  have hN_annQ : ∀ a ∈ Q, ∀ n : S ⧸ Q, a • n = 0 := fun a ha n => by
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective n
    change Ideal.Quotient.mk Q (a * s) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Q.mul_mem_right s ha)
  let _ : Module R (S ⧸ P) :=
    Module.compHom (S ⧸ P) (Ideal.Quotient.lift I (Module.toAddMonoidEnd S (S ⧸ P))
      (fun a ha => AddMonoidHom.ext fun m => hM_annP a (hI_le_P ha) m))
  let _ : Module R (S ⧸ Q) :=
    Module.compHom (S ⧸ Q) (Ideal.Quotient.lift I (Module.toAddMonoidEnd S (S ⧸ Q))
      (fun a ha => AddMonoidHom.ext fun n => hN_annQ a (hI_le_Q ha) n))
  let _ : IsScalarTower S R (S ⧸ P) :=
    ⟨fun s r m => by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
      change (s * a) • m = s • (a • m)
      exact mul_smul s a m⟩
  let _ : IsScalarTower S R (S ⧸ Q) :=
    ⟨fun s r n => by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
      change (s * a) • n = s • (a • n)
      exact mul_smul s a n⟩
  have htmul_zero : ∀ {X : Type} [AddCommGroup X] [Module S X] (x : X),
      (1 : R) ⊗ₜ[S] x = 0 ↔ ∃ y : X, g • y = x := by
    intro X _ _ x
    constructor
    · intro h0
      have hmem : x ∈ I • (⊤ : Submodule S X) := mem_ideal_smul_top_of_one_tmul_eq_zero I h0
      have hle : I • (⊤ : Submodule S X) ≤ LinearMap.range (g • (LinearMap.id : X →ₗ[S] X)) := by
        rw [Submodule.smul_le]
        rintro a ha y -
        obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton.mp ha
        exact ⟨s • y, by change g • (s • y) = (g * s) • y; rw [mul_smul]⟩
      obtain ⟨y, hy⟩ := hle hmem
      exact ⟨y, hy⟩
    · rintro ⟨y, rfl⟩
      rw [← TensorProduct.smul_tmul]
      have hg0 : g • (1 : R) = 0 := by
        change Ideal.Quotient.mk I (g * 1) = 0
        rw [mul_one]
        exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
      rw [hg0, TensorProduct.zero_tmul]
  obtain ⟨zEq, fq, tq, cn, hex1, hex2, hex3, hsurj0⟩ :=
    serre_h2_aux S g hg_ne R f rfl Ideal.Quotient.mk_surjective
      (fun {X} _ _ u => exists_one_tmul_eq I u)
      htmul_zero (S ⧸ P) (S ⧸ Q) (hN_annQ g hgQ)
  let eM : (S ⧸ P) ≃ₗ[R] (R ⧸ P.map f) := quotMapLinearEquiv I P hI_le_P
  let eN : (S ⧸ Q) ≃ₗ[R] (R ⧸ Q.map f) := quotMapLinearEquiv I Q hI_le_Q
  let eB (i : ℕ) : ((ModuleCat.restrictScalars f).obj (torMod R (S ⧸ P) (S ⧸ Q) i)) ≃ₗ[S]
      ((ModuleCat.restrictScalars f).obj (torMod R (R ⧸ P.map f) (R ⧸ Q.map f) i)) :=
    ((ModuleCat.restrictScalars f).mapIso
      ((((Tor (ModuleCat.{0} R) i).mapIso eM.toModuleIso).app (ModuleCat.of R (S ⧸ Q))) ≪≫
        (((Tor (ModuleCat.{0} R) i).obj (ModuleCat.of R (R ⧸ P.map f))).mapIso eN.toModuleIso))).toLinearEquiv
  let fromQuot' (i : ℕ) := (fq i).comp (eB i).symm.toLinearMap
  let toQuot' (i : ℕ) := (eB (i + 1)).toLinearMap.comp (tq i)
  let connect' (i : ℕ) := (eB i).toLinearMap.comp ((cn i).comp (eB (i + 2)).symm.toLinearMap)
  refine ⟨zEq.trans (eB 0), fromQuot', toQuot', connect', ?_, ?_, ?_, ?_⟩
  · intro i
    exact exact_of_surj_inj (eB i).symm (eB i).symm.surjective (Equiv.refl _)
      (eB (i + 1)) (fun x => (eB (i + 1)).map_eq_zero_iff)
      (fq i) (tq i) (hex1 i) (fromQuot' i) (toQuot' i)
      (fun _ => rfl) (fun _ => rfl)
  · intro i
    exact exact_of_surj_inj id Function.surjective_id (eB (i + 2)).toEquiv
      (eB i) (fun x => (eB i).map_eq_zero_iff)
      (tq (i + 1)) (cn i) (hex2 i) (toQuot' (i + 1)) (connect' i)
      (fun _ => rfl)
      (fun x => by simp [connect'])
  · intro i
    exact exact_of_surj_inj (eB (i + 2)).symm (eB (i + 2)).symm.surjective (eB i).toEquiv
      id (fun _ => Iff.rfl)
      (cn i) (fq i) (hex3 i) (connect' i) (fromQuot' i)
      (fun _ => rfl)
      (fun x => by simp [fromQuot'])
  · exact (eB 1).surjective.comp hsurj0

end ChangeOfRings

end SerreH2Proof

theorem OMA.solution :
    OMA.R_SerreMultiplicityConjectures_supportDim_add_supportDim_le_ringKrullDim_R1_H4_R1.H2 :=
  SerreH2Proof.serre_h2_main
