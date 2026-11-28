import FormalConjectures.Paper.AuslanderReiten
import Mathlib

/-!
# The Auslander–Reiten conjecture for Noetherian normal domains

Localize at a prime of least height where the module fails to be free. Normality
gives two regular elements there, so the first nonzero residue-field extension
with coefficients in the ring has degree at least two.

The local argument follows the syzygy and transpose strategy of K. Kimura,
“Auslander–Reiten conjecture for normal rings” (arXiv:2304.03956). We implement
the degree shifts by embedding modules with zero socle into products of their
stalks on the punctured spectrum. At the final step a nonzero socle element
applied to one generator of a minimal presentation gives a matrix with nonzero
trace. Ext vanishing would factor that matrix in a way that forces its trace to vanish.
-/

universe u

open CategoryTheory CategoryTheory.Abelian

namespace OMA.Normal

variable {R : Type u} [CommRing R]

private theorem extends_of_ext_one (S : ShortComplex (ModuleCat.{u} R)) (hs : S.ShortExact)
    (N : ModuleCat.{u} R) (h : Subsingleton (Ext S.X₃ N 1)) (a : S.X₁ ⟶ N) :
    ∃ b : S.X₂ ⟶ N, CategoryStruct.comp S.f b = a := by
  obtain ⟨v, hv⟩ := Ext.contravariant_sequence_exact₁ hs N (Ext.mk₀ a)
    (show 1 + 0 = 1 by rfl) (Subsingleton.eq_zero _)
  obtain ⟨b, rfl⟩ := (Ext.mk₀_bijective S.X₂ N).surjective v
  rw [Ext.mk₀_comp_mk₀, (Ext.mk₀_bijective _ _).injective.eq_iff] at hv
  exact ⟨b, hv⟩

private theorem ext_one_of_extends (S : ShortComplex (ModuleCat.{u} R)) (hs : S.ShortExact)
    [Projective S.X₂] (N : ModuleCat.{u} R)
    (h : ∀ a : S.X₁ ⟶ N, ∃ b : S.X₂ ⟶ N, CategoryStruct.comp S.f b = a) : Subsingleton (Ext S.X₃ N 1) := by
  have := Ext.subsingleton_of_projective S.X₂ N 0
  suffices hz : ∀ x : Ext S.X₃ N 1, x = 0 from ⟨fun x y => (hz x).trans (hz y).symm⟩
  intro x
  obtain ⟨z, rfl⟩ := Ext.contravariant_sequence_exact₃ hs N x (Subsingleton.eq_zero _) (add_zero 1)
  obtain ⟨a, rfl⟩ := (Ext.mk₀_bijective S.X₁ N).surjective z
  obtain ⟨b, rfl⟩ := h a
  rw [← Ext.mk₀_comp_mk₀]
  exact hs.extClass_comp_assoc _

private theorem shift_down (S : ShortComplex (ModuleCat.{u} R)) (hs : S.ShortExact)
    [Projective S.X₂] (N : ModuleCat.{u} R) (n : ℕ)
    (h : Subsingleton (Ext S.X₃ N (n+2))) : Subsingleton (Ext S.X₁ N (n+1)) := by
  have := Ext.subsingleton_of_projective S.X₂ N n
  have hz (x : Ext S.X₁ N (n+1)) : x = 0 := by
    obtain ⟨b, hb⟩ := Ext.contravariant_sequence_exact₁ hs N x (show 1+(n+1)=n+2 by omega)
      (Subsingleton.eq_zero _)
    simpa [Subsingleton.eq_zero b] using hb.symm
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

private theorem shift_up (S : ShortComplex (ModuleCat.{u} R)) (hs : S.ShortExact)
    [Projective S.X₂] (N : ModuleCat.{u} R) (n : ℕ)
    (h : Subsingleton (Ext S.X₁ N (n+1))) : Subsingleton (Ext S.X₃ N (n+2)) := by
  have := Ext.subsingleton_of_projective S.X₂ N (n+1)
  have hz (x : Ext S.X₃ N (n+2)) : x = 0 := by
    obtain ⟨b, hb⟩ := Ext.contravariant_sequence_exact₃ hs N x (Subsingleton.eq_zero _)
      (show 1+(n+1)=n+2 by omega)
    simpa [Subsingleton.eq_zero b] using hb.symm
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

private theorem localize_extension (U : Submonoid R)
    {K P N : ModuleCat.{u} R} [Module.FinitePresentation R K]
    {L : ModuleCat.{u} (Localization U)} [Module R L] [IsScalarTower R (Localization U) L]
    (j : N →ₗ[R] L) [IsLocalizedModule U j] (i : K →ₗ[R] P)
    (he : ∀ a : K →ₗ[R] N, ∃ b : P →ₗ[R] N, b.comp i = a)
    (a : LocalizedModule U K →ₗ[Localization U] L) :
    ∃ b : LocalizedModule U P →ₗ[Localization U] L, b.comp (LocalizedModule.map U i) = a := by
  let loc (X : ModuleCat.{u} R) := IsLocalizedModule.mapExtendScalars U
    (LocalizedModule.mkLinearMap U X) j (Localization U)
  obtain ⟨⟨a', s⟩, eq : s.val • a = loc K a'⟩ := IsLocalizedModule.surj U (loc K) a
  obtain ⟨b', rfl⟩ := he a'
  have comp_eq : (loc P b').comp (LocalizedModule.map U i) = loc K (b'.comp i) := by
    ext z
    induction z using LocalizedModule.induction_on with
    | _ x t =>
      simp only [LinearMap.comp_apply, LocalizedModule.map_mk]
      simp only [loc, IsLocalizedModule.mapExtendScalars_apply_apply, IsLocalizedModule.mk_eq_mk',
        IsLocalizedModule.map_mk', LinearMap.comp_apply]
  refine ⟨IsLocalization.mk' (Localization U) 1 s • loc P b', ?_⟩
  rw [LinearMap.smul_comp, comp_eq, ← eq, ← IsScalarTower.algebraMap_smul (Localization U) s.val,
    smul_smul, IsLocalization.mk'_spec, map_one, one_smul]

theorem localized_ext [IsNoetherianRing R] (U : Submonoid R) (M N : ModuleCat.{u} R)
    [Module.Finite R M] (L : ModuleCat.{u} (Localization U))
    [Module R L] [IsScalarTower R (Localization U) L]
    (j : N →ₗ[R] L) [IsLocalizedModule U j] (n : ℕ)
    (h : Subsingleton (Ext M N (n+1))) :
    Subsingleton (Ext (ModuleCat.of (Localization U) (LocalizedModule U M)) L (n+1)) := by
  induction n generalizing M
  all_goals
    obtain ⟨P, _, _, _, _, f, hf⟩ := Module.exists_finite_presentation R M
    let i := (LinearMap.ker f).subtype
    let K := ModuleCat.of R (LinearMap.ker f)
    let F := ModuleCat.of R P
    let S := f.shortComplexKer
    have hs : S.ShortExact := LinearMap.shortExact_shortComplexKer hf
    let A := Localization U
    let g := LocalizedModule.map U i
    let q := LocalizedModule.map U f
    have ex : Function.Exact g q := LocalizedModule.map_exact U _ _ f.exact_subtype_ker_map
    let T := ModuleCat.shortComplexOfCompEqZero g q ex.linearMap_comp_eq_zero
    have ht := ModuleCat.shortComplex_shortExact T ex
      (LocalizedModule.map_injective U i (LinearMap.ker f).subtype_injective)
      (LocalizedModule.map_surjective U f hf)
    have : Module.Free A (LocalizedModule U P) :=
      Module.free_of_isLocalizedModule (Rₛ := A) U (LocalizedModule.mkLinearMap U P)
    change Subsingleton (Ext T.X₃ L _)
  case zero =>
      apply ext_one_of_extends T ht L
      intro a
      have : Module.FinitePresentation R K := Module.finitePresentation_of_finite R K
      obtain ⟨b, hb⟩ := localize_extension (K := K) (P := F) U j i
        (fun a => by
          obtain ⟨b, hb⟩ := extends_of_ext_one S hs N h (ModuleCat.ofHom a)
          exact ⟨b.hom, congrArg ModuleCat.Hom.hom hb⟩) a.hom
      exact ⟨ModuleCat.ofHom b, ModuleCat.hom_ext hb⟩
  case succ =>
    apply shift_up T ht L
    change Subsingleton (Ext (ModuleCat.of (Localization U) (LocalizedModule U K)) L _)
    apply_assumption
    exact shift_down S hs N _ h

-- Coordinatewise retraction argument from the supplied regular-local proof.
private theorem extends_to_free_kernel (S : ShortComplex (ModuleCat.{u} R))
    (hS : S.ShortExact) [Module.Finite R S.X₁] [Module.Free R S.X₁]
    (h : Subsingleton (Ext S.X₃ (ModuleCat.of R R) 1)) :
    ∃ r : S.X₂ ⟶ S.X₁, CategoryStruct.comp S.f r = 𝟙 S.X₁ := by
  classical
  let Z := ModuleCat.of R R
  have extend (a : S.X₁ ⟶ Z) : ∃ b : S.X₂ ⟶ Z, CategoryStruct.comp S.f b = a :=
    extends_of_ext_one S hS Z h a
  let I := Module.Free.ChooseBasisIndex R S.X₁
  let : Fintype I := Module.Free.ChooseBasisIndex.fintype R S.X₁
  let e : S.X₁ ≃ₗ[R] (I → R) := (Module.Free.chooseBasis R S.X₁).equivFun
  have point (i : I) : ∃ b : S.X₂ ⟶ Z,
      CategoryStruct.comp S.f b = ModuleCat.ofHom ((LinearMap.proj i).comp e.toLinearMap) :=
    extend _
  choose b hb using point
  let r : S.X₂ ⟶ S.X₁ := ModuleCat.ofHom
    (e.symm.toLinearMap.comp (LinearMap.pi fun i => (b i).hom))
  refine ⟨r, ?_⟩
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply e.injective
  funext i
  change e (e.symm (fun j => b j (S.f x))) i = e x i
  rw [e.apply_symm_apply]
  exact congrArg (fun f : S.X₁ ⟶ Z => f x) (hb i)

private theorem free_of_ext_pid [IsDomain R] [IsPrincipalIdealRing R] [IsLocalRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M]
    (h : Subsingleton (Ext M (ModuleCat.of R R) 1)) : Module.Free R M := by
  obtain ⟨P, _, _, _, _, f, hf⟩ := Module.exists_finite_presentation R M
  let S := f.shortComplexKer
  have hs : S.ShortExact := LinearMap.shortExact_shortComplexKer hf
  have : Module.Free R (LinearMap.ker f) := inferInstance
  obtain ⟨r, hr⟩ := extends_to_free_kernel S hs h
  let splitting := ShortComplex.Splitting.ofExactOfRetraction S hs.exact r hr hs.epi_g
  have : Projective M := (Retract.mk splitting.s S.g splitting.s_g).projective
  have : Module.Projective R M := ModuleCat.projective_of_module_projective M
  exact Module.free_of_flat_of_isLocalRing

/-- Vanishing against the ring gives vanishing against any finite free target. -/
theorem ext_finite_free (X P : ModuleCat.{u} R) [Module.Free R P] [Module.Finite R P]
    (n : ℕ) (h : Subsingleton (Ext X (ModuleCat.of R R) n)) : Subsingleton (Ext X P n) := by
  classical
  let I := Module.Free.ChooseBasisIndex R P
  let : Fintype I := Module.Free.ChooseBasisIndex.fintype R P
  let B := Module.Free.chooseBasis R P
  let Z := ModuleCat.of R R
  let π (i : I) : P ⟶ Z := ModuleCat.ofHom (B.coord i)
  let ι (i : I) : Z ⟶ P := ModuleCat.ofHom (LinearMap.toSpanSingleton R P (B i))
  have total : ∑ i, CategoryStruct.comp (π i) (ι i) = 𝟙 P := by
    apply ModuleCat.homAddEquiv.injective
    rw [map_sum]
    ext x
    rw [LinearMap.sum_apply]
    exact B.sum_repr x
  have hz (e : Ext X P n) : e = 0 := by
    rw [← e.comp_mk₀_id, ← total, Ext.mk₀_sum, Ext.comp_sum]
    apply Finset.sum_eq_zero
    intro i _
    rw [← Ext.mk₀_comp_mk₀, ← Ext.comp_assoc_of_second_deg_zero]
    simp [Subsingleton.eq_zero (e.comp (Ext.mk₀ (π i)) (add_zero n))]
  exact ⟨fun a b => (hz a).trans (hz b).symm⟩

/-- Positive self extensions vanish for the kernel of a finite free cover when the
corresponding self and ring extensions vanish for its cokernel. -/
theorem syzygy_self_ext (S : ShortComplex (ModuleCat.{u} R)) (hs : S.ShortExact)
    [Module.Free R S.X₂] [Module.Finite R S.X₂] (n : ℕ)
    (hr : Subsingleton (Ext S.X₃ (ModuleCat.of R R) (n+2)))
    (hm : Subsingleton (Ext S.X₃ S.X₃ (n+1))) : Subsingleton (Ext S.X₁ S.X₁ (n+1)) := by
  have := ext_finite_free S.X₃ S.X₂ _ hr
  apply shift_down S hs S.X₁ n
  have hz (a : Ext S.X₃ S.X₁ (n+2)) : a = 0 := by
    obtain ⟨b, hb⟩ := Ext.covariant_sequence_exact₁ S.X₃ hs a (Subsingleton.eq_zero _)
      (show (n+1)+1=n+2 by rfl)
    simpa [Subsingleton.eq_zero b] using hb.symm
  exact ⟨fun a b => (hz a).trans (hz b).symm⟩

open IsLocalRing

-- The determinant argument below is adapted from Andrew Yang,
-- Mathlib/RingTheory/DiscreteValuationRing/TFAE.lean (Apache-2.0, 2022).
private theorem principal_of_colon [IsNoetherianRing R] [IsDomain R] [IsIntegrallyClosed R]
    [IsLocalRing R] {a b : R} (ha₁ : a ∈ maximalIdeal R) (ha₂ : a ≠ 0)
    (hb₂ : b ∉ Ideal.span {a})
    (hb₃ : ∀ m ∈ maximalIdeal R, ∃ k : R, k * a = b * m) :
    (maximalIdeal R).IsPrincipal := by
  have hb₄ : b ≠ 0 := by rintro rfl; apply hb₂; exact zero_mem _
  let K := FractionRing R
  let x : K := algebraMap R K b / algebraMap R K a
  let M := Submodule.map (Algebra.linearMap R K) (maximalIdeal R)
  have ha₃ : algebraMap R K a ≠ 0 := IsFractionRing.to_map_eq_zero_iff.not.mpr ha₂
  by_cases hx : ∀ y ∈ M, x * y ∈ M
  · have := isIntegral_of_smul_mem_submodule M ?_ ?_ x hx
    · obtain ⟨y, e⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral this
      refine (hb₂ (Ideal.mem_span_singleton'.mpr ⟨y, ?_⟩)).elim
      apply IsFractionRing.injective R K
      rw [map_mul, e, div_mul_cancel₀ _ ha₃]
    · rw [Submodule.ne_bot_iff]; refine ⟨_, ⟨a, ha₁, rfl⟩, ?_⟩
      exact (IsFractionRing.to_map_eq_zero_iff (K := K)).not.mpr ha₂
    · apply Submodule.FG.map; exact IsNoetherian.noetherian _
  · have :
        (M.map (DistribSMul.toLinearMap R K x)).comap (Algebra.linearMap R K) = ⊤ := by
      contrapose! hx with h
      rintro m' ⟨m, hm, rfl : algebraMap R K m = m'⟩
      obtain ⟨k, hk⟩ := hb₃ m hm
      have hk' : x * algebraMap R K m = algebraMap R K k := by
        rw [← mul_div_right_comm, ← map_mul, ← hk, map_mul, mul_div_cancel_right₀ _ ha₃]
      exact ⟨k, le_maximalIdeal h ⟨_, ⟨_, hm, rfl⟩, hk'⟩, hk'.symm⟩
    obtain ⟨y, hy₁, hy₂⟩ : ∃ y ∈ maximalIdeal R, b * y = a := by
      rw [Ideal.eq_top_iff_one, Submodule.mem_comap] at this
      obtain ⟨_, ⟨y, hy, rfl⟩, hy' : x * algebraMap R K y = algebraMap R K 1⟩ := this
      rw [map_one, ← mul_div_right_comm, div_eq_one_iff_eq ha₃, ← map_mul] at hy'
      exact ⟨y, hy, IsFractionRing.injective R K hy'⟩
    refine ⟨⟨y, ?_⟩⟩
    apply le_antisymm
    · intro m hm; obtain ⟨k, hk⟩ := hb₃ m hm; rw [← hy₂, mul_comm, mul_assoc] at hk
      rw [← mul_left_cancel₀ hb₄ hk, mul_comm]; exact Ideal.mem_span_singleton'.mpr ⟨_, rfl⟩
    · rwa [Submodule.span_le, Set.singleton_subset_iff]

theorem regular_pair [IsNoetherianRing R] [IsDomain R] [IsIntegrallyClosed R] [IsLocalRing R]
    (hd : 1 < ringKrullDim R) :
    ∃ x ∈ maximalIdeal R, x ≠ 0 ∧ ∃ y ∈ maximalIdeal R,
      IsSMulRegular (R ⧸ Ideal.span {x}) y := by
  have hnp : ¬ (maximalIdeal R).IsPrincipal := by
    intro h
    have : IsPrincipalIdealRing R :=
      ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain R).out 4 0).mp h
    exact hd.not_ge (by simpa using Ring.krullDimLE_iff.mp (inferInstance : Ring.KrullDimLE 1 R))
  have hnb : maximalIdeal R ≠ ⊥ := by
    rintro e
    exact hnp (e ▸ inferInstanceAs (⊥ : Ideal R).IsPrincipal)
  obtain ⟨a, ha, h0⟩ := (Submodule.ne_bot_iff _).mp hnb
  refine ⟨a, ha, h0, ?_⟩
  let I := Ideal.span {a}
  let Q := R ⧸ I
  by_contra! h
  have incl : (maximalIdeal R : Set R) ⊆ ⋃ p ∈ associatedPrimes R Q, (p : Set R) := by
    rw [biUnion_associatedPrimes_eq_compl_regular R Q]
    exact fun r hr => h r hr
  obtain ⟨p, hp, hle⟩ := (Ideal.subset_union_prime_finite (associatedPrimes.finite R Q)
    (f := id) 0 0 (fun _ hi _ _ => hi.1)).mp incl
  have eq : p = maximalIdeal R := (le_maximalIdeal hp.1.ne_top).antisymm hle
  obtain ⟨_, z, hz⟩ := (isAssociatedPrime_iff.mp hp)
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
  have hb : b ∉ I := by
    intro hb
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hb, Submodule.colon_singleton_zero] at hz
    exact hp.1.ne_top hz
  apply hnp (principal_of_colon ha h0 hb ?_)
  intro m hm
  have e : m ∈ (⊥ : Submodule R Q).colon {(Ideal.Quotient.mk I) b} := hz ▸ eq ▸ hm
  rw [Submodule.mem_colon_singleton, Submodule.mem_bot, Algebra.smul_def,
    Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem] at e
  simpa only [mul_comm m b] using Ideal.mem_span_singleton'.mp e


private abbrev Punctured (R : Type u) [CommRing R] [IsLocalRing R] :=
  {p : PrimeSpectrum R // p.asIdeal ≠ maximalIdeal R}

private noncomputable def diagonal [IsLocalRing R] (K : ModuleCat.{u} R) :=
  LinearMap.pi fun p : Punctured R => LocalizedModule.mkLinearMap p.1.asIdeal.primeCompl K

/-- A module with zero socle embeds into the product of its stalks away from the
closed point, even if the module is infinitely generated. -/
private theorem diagonal_injective [IsNoetherianRing R] [IsLocalRing R] (K : ModuleCat.{u} R)
    (hk : Subsingleton (Ext (ModuleCat.of R (ResidueField R)) K 0)) :
    Function.Injective (diagonal K) := by
  have h0 := Ext.addEquiv₀.subsingleton_congr.mp hk
  have : Subsingleton ((ResidueField R) →ₗ[R] K) :=
    (ModuleCat.homAddEquiv (M := ModuleCat.of R (ResidueField R)) (N := K)).symm.subsingleton
  apply LinearMap.ker_eq_bot.mp
  refine le_antisymm ?_ bot_le
  intro z hz
  change z = 0
  by_contra hn
  obtain ⟨p, hp, hzp⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing R z hn
  have hpm : p ≠ maximalIdeal R := by
    rintro rfl
    obtain ⟨_, f, hf⟩ := (isAssociatedPrime_iff_exists_injective_linearMap _ _).mp hp
    change ResidueField R →ₗ[R] K at f
    rw [Subsingleton.eq_zero f] at hf
    have e : (1 : ResidueField R) = 0 := @hf (1 : ResidueField R) 0 rfl
    exact (one_ne_zero : (1 : ResidueField R) ≠ 0) e
  let q : Punctured R := ⟨⟨p, hp.isPrime⟩, hpm⟩
  have zero := congrFun (LinearMap.mem_ker.mp hz) q
  obtain ⟨r, hr, h⟩ := LocalizedModule.mem_ker_mkLinearMap_iff.mp zero
  exact hr (hzp (Submodule.mem_colon_singleton.mpr h))

private theorem localized_kernel_retract [IsNoetherianRing R] (U : Submonoid R)
    {P M : ModuleCat.{u} R} [Module.Free R P] (f : P →ₗ[R] M) (hf : Function.Surjective f)
    (hp : Module.Projective (Localization U) (LocalizedModule U M)) :
    Module.Projective (Localization U) (LocalizedModule U (LinearMap.ker f)) ∧
    ∃ r : LocalizedModule U P →ₗ[Localization U] LocalizedModule U (LinearMap.ker f),
      r.comp (LocalizedModule.map U (LinearMap.ker f).subtype) = LinearMap.id := by
  let i := (LinearMap.ker f).subtype
  let g := LocalizedModule.map U i
  let q := LocalizedModule.map U f
  have ex : Function.Exact g q := LocalizedModule.map_exact U _ _ f.exact_subtype_ker_map
  let T := ModuleCat.shortComplexOfCompEqZero g q ex.linearMap_comp_eq_zero
  have ht := ModuleCat.shortComplex_shortExact T ex
    (LocalizedModule.map_injective U i (LinearMap.ker f).subtype_injective)
    (LocalizedModule.map_surjective U f hf)
  let split := ht.splittingOfProjective
  have : Module.Free (Localization U) (LocalizedModule U P) :=
    Module.free_of_isLocalizedModule (Rₛ := Localization U) U (LocalizedModule.mkLinearMap U P)
  have : Projective T.X₁ := (Retract.mk T.f split.r split.f_r).projective
  exact ⟨ModuleCat.projective_of_module_projective T.X₁, split.r.hom,
    congrArg ModuleCat.Hom.hom split.f_r⟩

/-- Ext into a product of modules over localizations vanishes when the source
becomes projective in each of those localizations. -/
theorem ext_into_local_product [IsNoetherianRing R] {J : Type u}
    (U : J → Submonoid R) (L : J → ModuleCat.{u} R)
    (units : ∀ j (s : U j), IsUnit (algebraMap R (Module.End R (L j)) s))
    (M : ModuleCat.{u} R) [Module.Finite R M]
    (hm : ∀ j, Module.Projective (Localization (U j)) (LocalizedModule (U j) M)) (n : ℕ) :
    Subsingleton (Ext M (ModuleCat.of R ((j : J) → L j)) (n+1)) := by
  induction n generalizing M
  all_goals
    obtain ⟨P, _, _, _, _, f, hf⟩ := Module.exists_finite_presentation R M
    let F := ModuleCat.of R P
    let S := f.shortComplexKer
    have hs := LinearMap.shortExact_shortComplexKer hf
    have dec (j : J) := localized_kernel_retract (P := F) (M := M) (U j) f hf (hm j)
  case zero =>
    apply ext_one_of_extends S hs
    intro a
    choose r hr using fun j => (dec j).2
    let b (j : J) := IsLocalizedModule.lift (U j) (LocalizedModule.mkLinearMap (U j) (LinearMap.ker f))
      ((LinearMap.proj j).comp a.hom) (units j)
    refine ⟨ModuleCat.ofHom (LinearMap.pi fun j => (b j).comp (((r j).restrictScalars R).comp
      (LocalizedModule.mkLinearMap (U j) P))), ?_⟩
    apply ModuleCat.hom_ext
    ext x j
    let z := LocalizedModule.mkLinearMap (U j) (LinearMap.ker f) x
    have e := LinearMap.congr_fun (hr j) z
    simp only [LinearMap.comp_apply, z, LocalizedModule.mkLinearMap_apply, LocalizedModule.map_mk,
      LinearMap.id_apply] at e
    change b j (r j (LocalizedModule.mk (f.ker.subtype x) 1)) = _
    rw [e]
    exact IsLocalizedModule.lift_apply ..
  case succ =>
    apply shift_up S hs
    apply_assumption
    exact fun j => (dec j).1


private abbrev HomObj (X Y : ModuleCat.{u} R) := ModuleCat.of R (X →ₗ[R] Y)

private theorem hom_short_exact (X : ModuleCat.{u} R)
    (S : ShortComplex (ModuleCat.{u} R)) (hs : S.ShortExact)
    (h : Subsingleton (Ext X S.X₁ 1)) :
    ∃ T : ShortComplex (ModuleCat.{u} R), T.ShortExact ∧
      T.X₁ = HomObj X S.X₁ ∧ T.X₂ = HomObj X S.X₂ ∧ T.X₃ = HomObj X S.X₃ := by
  let f : (X →ₗ[R] S.X₁) →ₗ[R] (X →ₗ[R] S.X₂) := LinearMap.llcomp R X S.X₁ S.X₂ S.f.hom
  let g : (X →ₗ[R] S.X₂) →ₗ[R] (X →ₗ[R] S.X₃) := LinearMap.llcomp R X S.X₂ S.X₃ S.g.hom
  have ex : Function.Exact f g := by
    intro b
    constructor
    · intro hb
      have hh : (Ext.mk₀ (ModuleCat.ofHom b)).comp (Ext.mk₀ S.g) (add_zero 0) = 0 := by
        rw [Ext.mk₀_comp_mk₀]
        convert Ext.mk₀_zero X S.X₃ using 2
        exact ModuleCat.hom_ext hb
      obtain ⟨a, ha⟩ := Ext.covariant_sequence_exact₂ X hs _ hh
      obtain ⟨a, rfl⟩ := (Ext.mk₀_bijective X S.X₁).surjective a
      rw [Ext.mk₀_comp_mk₀, (Ext.mk₀_bijective _ _).injective.eq_iff] at ha
      exact ⟨a.hom, congrArg ModuleCat.Hom.hom ha⟩
    · rintro ⟨a, rfl⟩
      ext z
      exact DFunLike.congr_fun (congrArg ModuleCat.Hom.hom S.zero) (a z)
  let T := ModuleCat.shortComplexOfCompEqZero f g ex.linearMap_comp_eq_zero
  refine ⟨T, ModuleCat.shortComplex_shortExact T ex ?_ ?_, rfl, rfl, rfl⟩
  · intro a b hab
    apply LinearMap.ext
    intro z
    exact (ModuleCat.mono_iff_injective S.f).mp hs.mono_f (LinearMap.congr_fun hab z)
  · intro c
    obtain ⟨b, hb⟩ := Ext.covariant_sequence_exact₃ X hs (Ext.mk₀ (ModuleCat.ofHom c)) rfl
      (Subsingleton.eq_zero _)
    obtain ⟨b, rfl⟩ := (Ext.mk₀_bijective X S.X₂).surjective b
    rw [Ext.mk₀_comp_mk₀, (Ext.mk₀_bijective _ _).injective.eq_iff] at hb
    exact ⟨b.hom, congrArg ModuleCat.Hom.hom hb⟩

private theorem shift_coeff (X : ModuleCat.{u} R) (S : ShortComplex (ModuleCat.{u} R))
    (hs : S.ShortExact) (n : ℕ) (mid₀ : Subsingleton (Ext X S.X₂ n))
    (mid₁ : Subsingleton (Ext X S.X₂ (n+1))) :
    Subsingleton (Ext X S.X₃ n) ↔ Subsingleton (Ext X S.X₁ (n+1)) := by
  constructor
  · intro h
    have hz (a : Ext X S.X₁ (n+1)) : a = 0 := by
      obtain ⟨b, hb⟩ := Ext.covariant_sequence_exact₁ X hs a (Subsingleton.eq_zero _) rfl
      simpa [Subsingleton.eq_zero b] using hb.symm
    exact ⟨fun a b => (hz a).trans (hz b).symm⟩
  · intro h
    have hz (a : Ext X S.X₃ n) : a = 0 := by
      obtain ⟨b, hb⟩ := Ext.covariant_sequence_exact₃ X hs a rfl (Subsingleton.eq_zero _)
      simpa [Subsingleton.eq_zero b] using hb.symm
    exact ⟨fun a b => (hz a).trans (hz b).symm⟩

private abbrev StalkProd [IsLocalRing R] (K : ModuleCat.{u} R) :=
  ModuleCat.of R ((p : Punctured R) → LocalizedModule p.1.asIdeal.primeCompl K)

private def OnPuncture [IsLocalRing R] (X : ModuleCat.{u} R) :=
  ∀ p : Punctured R, Module.Projective (Localization.AtPrime p.1.asIdeal)
    (LocalizedModule p.1.asIdeal.primeCompl X)

private theorem ext_stalk_prod [IsNoetherianRing R] [IsLocalRing R] (K X : ModuleCat.{u} R)
    [Module.Finite R X] (hx : OnPuncture X) (n : ℕ) : Subsingleton (Ext X (StalkProd K) (n+1)) :=
  ext_into_local_product (fun p : Punctured R => p.1.asIdeal.primeCompl)
    (fun p => ModuleCat.of R (LocalizedModule p.1.asIdeal.primeCompl K))
    (fun p => IsLocalizedModule.map_units (LocalizedModule.mkLinearMap p.1.asIdeal.primeCompl K))
    X hx n

private theorem residue_ext_stalk_prod [IsNoetherianRing R] [IsLocalRing R] (K : ModuleCat.{u} R)
    (n : ℕ) : Subsingleton (Ext (ModuleCat.of R (ResidueField R)) (StalkProd K) n) := by
  let k := ModuleCat.of R (ResidueField R)
  have ann (p : Punctured R) : ∃ s : p.1.asIdeal.primeCompl, ∀ x : k, s.val • x = 0 := by
    have le := IsLocalRing.le_maximalIdeal p.1.isPrime.ne_top
    obtain ⟨s, hm, hp⟩ := SetLike.not_le_iff_exists.mp (lt_of_le_of_ne le p.2).not_ge
    refine ⟨⟨s, hp⟩, fun x => ?_⟩
    change residue R s * x = 0
    rw [(residue_eq_zero_iff _).mpr hm, zero_mul]
  cases n with
  | zero =>
    have hz (a : k →ₗ[R] StalkProd K) : a = 0 := by
      ext x p
      obtain ⟨s, hs⟩ := ann p
      apply IsLocalizedModule.smul_injective (LocalizedModule.mkLinearMap p.1.asIdeal.primeCompl K) s
      change (s.val • a x) p = s.val • (0 : LocalizedModule p.1.asIdeal.primeCompl K)
      rw [← a.map_smul, hs, map_zero, smul_zero]
      rfl
    have : Subsingleton (k →ₗ[R] StalkProd K) := ⟨fun a b => (hz a).trans (hz b).symm⟩
    exact (Ext.addEquiv₀.trans (ModuleCat.homAddEquiv (M := k) (N := StalkProd K))).subsingleton
  | succ n =>
    apply ext_stalk_prod K k _ n
    intro p
    obtain ⟨s, hs⟩ := ann p
    have : Subsingleton (LocalizedModule p.1.asIdeal.primeCompl k) :=
      LocalizedModule.subsingleton_iff.mpr fun x => ⟨s.val, s.2, hs x⟩
    infer_instance

private theorem ext_hom_stalk_prod [IsLocalRing R] [IsNoetherianRing R] (W X K : ModuleCat.{u} R)
    [Module.Finite R W] (hw : OnPuncture W) (n : ℕ) :
    Subsingleton (Ext W (HomObj X (StalkProd K)) (n+1)) := by
  let L (p : Punctured R) := LocalizedModule p.1.asIdeal.primeCompl K
  let Y (p : Punctured R) := ModuleCat.of R (X →ₗ[R] L p)
  have units (p : Punctured R) (s : p.1.asIdeal.primeCompl) :
      IsUnit (algebraMap R (Module.End R (Y p)) s) := by
    have u := IsLocalizedModule.map_units (LocalizedModule.mkLinearMap p.1.asIdeal.primeCompl K) s
    apply (Module.End.isUnit_iff _).mpr
    constructor
    · intro f g eq
      ext x
      exact ((Module.End.isUnit_iff _).mp u).1 (LinearMap.congr_fun eq x)
    · intro f
      refine ⟨u.unit⁻¹.val.comp f, ?_⟩
      ext x
      exact Module.End.isUnit_apply_inv_apply_of_isUnit u (f x)
  have hprod := ext_into_local_product (fun p : Punctured R => p.1.asIdeal.primeCompl) Y units W hw n
  let e : ((p : Punctured R) → X →ₗ[R] L p) ≃ₗ[R] (X →ₗ[R] StalkProd K) :=
    LinearEquiv.linearMapPi R
  let ei : ModuleCat.of R ((p : Punctured R) → Y p) ≅ HomObj X (StalkProd K) := e.toModuleIso
  exact ((Abelian.extFunctorObj W (n+1)).mapIso ei).addCommGroupIsoToAddEquiv.subsingleton_congr.mp hprod

/-- Shift a nonzero residue-field extension down to a socle element, simultaneously
shifting the extension with Hom coefficients down to degree one. -/
private theorem test_module [IsLocalRing R] [IsNoetherianRing R]
    (X W : ModuleCat.{u} R) [Module.Finite R X] [Module.Finite R W]
    (xf : OnPuncture X) (wf : OnPuncture W) (t : ℕ) (K : ModuleCat.{u} R)
    (ht : ¬ Subsingleton (Ext (ModuleCat.of R (ResidueField R)) K t))
    (lo : ∀ i < t, Subsingleton (Ext (ModuleCat.of R (ResidueField R)) K i))
    (hx : ∀ i < t, Subsingleton (Ext X K (i+1)))
    (hw : Subsingleton (Ext W (HomObj X K) (t+1))) :
    ∃ Z : ModuleCat.{u} R, ¬ Subsingleton (Ext (ModuleCat.of R (ResidueField R)) Z 0) ∧
      Subsingleton (Ext W (HomObj X Z) 1) := by
  let k := ModuleCat.of R (ResidueField R)
  induction t generalizing K with
  | zero => exact ⟨K, ht, hw⟩
  | succ t ih =>
    let d := diagonal K
    let B := StalkProd K
    let K' := ModuleCat.of R (B ⧸ LinearMap.range d)
    let ex := LinearMap.exact_map_mkQ_range d
    let S := ModuleCat.shortComplexOfCompEqZero d (LinearMap.range d).mkQ ex.linearMap_comp_eq_zero
    have hs := ModuleCat.shortComplex_shortExact S ex (diagonal_injective K (lo 0 (by omega)))
      (LinearMap.range d).mkQ_surjective
    have step (i : ℕ) : Subsingleton (Ext k K' i) ↔ Subsingleton (Ext k K (i+1)) :=
      shift_coeff k S hs i (residue_ext_stalk_prod K i) (residue_ext_stalk_prod K (i+1))
    apply ih K' (mt (step t).mp ht) (fun i hi => (step i).mpr (lo (i+1) (by omega)))
    · intro i hi
      exact (shift_coeff X S hs (i+1) (ext_stalk_prod K X xf i) (ext_stalk_prod K X xf (i+1))).mpr
        (hx (i+1) (by omega))
    · obtain ⟨T, hT, h₁, h₂, h₃⟩ := hom_short_exact X S hs (hx 0 (by omega))
      have s := shift_coeff W T hT (t+1)
      rw [h₁, h₂, h₃] at s
      exact (s (ext_hom_stalk_prod W X K wf t) (ext_hom_stalk_prod W X K wf (t+1))).mpr hw

open scoped TensorProduct in
private theorem minimal_cover [IsLocalRing R] (M : ModuleCat.{u} R) [Module.Finite R M] :
    ∃ (I : Type u) (_ : Fintype I) (f : (I → R) →ₗ[R] M), Function.Surjective f ∧
      ∀ c ∈ LinearMap.ker f, ∀ i, c i ∈ maximalIdeal R := by
  classical
  have : Module.Free (ResidueField R) ((ResidueField R) ⊗[R] M) :=
    Module.Free.of_divisionRing _ _
  let I := Module.Free.ChooseBasisIndex (ResidueField R) ((ResidueField R) ⊗[R] M)
  let : Fintype I := Module.Free.ChooseBasisIndex.fintype (ResidueField R) ((ResidueField R) ⊗[R] M)
  let b := Module.Free.chooseBasis (ResidueField R) ((ResidueField R) ⊗[R] M)
  let g := TensorProduct.mk R (ResidueField R) M 1
  choose v hv using fun i : I => TensorProduct.mk_surjective R M (ResidueField R) Ideal.Quotient.mk_surjective (b i)
  refine ⟨I, inferInstance, Fintype.linearCombination R v, ?_, ?_⟩
  · rw [← LinearMap.range_eq_top, Fintype.range_linearCombination]
    exact span_eq_top_of_tmul_eq_basis v b hv
  · intro c hc i
    have eq := congrArg g (LinearMap.mem_ker.mp hc)
    simp only [Fintype.linearCombination_apply, map_sum, map_smul, map_zero] at eq
    apply (residue_eq_zero_iff _).mp
    apply Fintype.linearIndependent_iff.mp b.linearIndependent (fun j => residue R (c j)) _ i
    simpa only [← IsLocalRing.ResidueField.algebraMap_eq, algebraMap_smul,
      ← hv] using eq

private abbrev DualObj (M : ModuleCat.{u} R) := ModuleCat.of R (Module.Dual R M)

private theorem dual_kernel_exact {P M : ModuleCat.{u} R} (f : P →ₗ[R] M)
    (hf : Function.Surjective f) (h : Subsingleton (Ext M (ModuleCat.of R R) 1)) :
    Function.Surjective (LinearMap.ker f).subtype.dualMap := by
  intro a
  obtain ⟨b, hb⟩ := extends_of_ext_one f.shortComplexKer (LinearMap.shortExact_shortComplexKer hf)
    (ModuleCat.of R R) h (ModuleCat.ofHom a)
  exact ⟨b.hom, congrArg ModuleCat.Hom.hom hb⟩

private theorem eval_kernel_injective {P M : ModuleCat.{u} R} [Module.IsReflexive R P]
    (f : P →ₗ[R] M) : Function.Injective (Module.Dual.eval R (LinearMap.ker f)) := by
  intro a b eq
  apply Subtype.ext
  apply (Module.bijective_dual_eval R P).1
  ext l
  exact LinearMap.congr_fun eq ((LinearMap.ker f).subtype.dualMap l)

private theorem reflexive_kernel {P M : ModuleCat.{u} R} [Module.IsReflexive R P]
    (f : P →ₗ[R] M) (hf : Function.Surjective f) (h : Subsingleton (Ext M (ModuleCat.of R R) 1))
    (hin : Function.Injective (Module.Dual.eval R M)) : Module.IsReflexive R (LinearMap.ker f) := by
  refine ⟨eval_kernel_injective f, ?_⟩
  intro k
  let i := (LinearMap.ker f).subtype
  obtain ⟨p, eq⟩ := (Module.bijective_dual_eval R P).2 (i.dualMap.dualMap k)
  have fp : f p = 0 := by
    apply hin
    ext l
    have e := LinearMap.congr_fun eq (f.dualMap l)
    have zero : i.dualMap (f.dualMap l) = 0 := by
      ext x
      change l (f x.val) = 0
      rw [x.property, map_zero]
    change l (f p) = k (i.dualMap (f.dualMap l)) at e
    change l (f p) = l 0
    rw [map_zero]
    simpa only [zero, map_zero] using e
  refine ⟨⟨p, fp⟩, ?_⟩
  ext l
  obtain ⟨b, rfl⟩ := dual_kernel_exact f hf h l
  exact LinearMap.congr_fun eq b

private theorem dual_ext_kernel {P M : ModuleCat.{u} R} [Module.Free R P] [Module.Finite R P]
    [Module.IsReflexive R M] (f : P →ₗ[R] M) (hf : Function.Surjective f)
    (h : Subsingleton (Ext M (ModuleCat.of R R) 1)) (t : ℕ)
    (hd : ∀ j < t, Subsingleton (Ext (DualObj M) (ModuleCat.of R R) (j+1))) :
    ∀ j < t+1, Subsingleton (Ext (ModuleCat.of R (Module.Dual R (LinearMap.ker f)))
      (ModuleCat.of R R) (j+1)) := by
  let i := (LinearMap.ker f).subtype
  have ex : Function.Exact f.dualMap i.dualMap :=
    LinearMap.exact_lcomp_of_exact_of_surjective R f.exact_subtype_ker_map hf
  let S := ModuleCat.shortComplexOfCompEqZero f.dualMap i.dualMap ex.linearMap_comp_eq_zero
  have hs := ModuleCat.shortComplex_shortExact S ex (LinearMap.dualMap_injective_of_surjective hf)
    (dual_kernel_exact f hf h)
  intro j hj
  cases j with
  | zero =>
    apply ext_one_of_extends S hs
    intro a
    obtain ⟨m, em⟩ := (Module.bijective_dual_eval R M).2 a.hom
    obtain ⟨p, hp⟩ := hf m
    refine ⟨ModuleCat.ofHom (Module.Dual.eval R P p), ?_⟩
    apply ModuleCat.hom_ext
    ext y
    exact (congrArg y hp).trans (LinearMap.congr_fun em y)
  | succ j => exact shift_up S hs _ j (hd j (by omega))

private structure Vanishing [IsLocalRing R] (M : ModuleCat.{u} R) : Prop where
  ring_ext : ∀ n, Subsingleton (Ext M (ModuleCat.of R R) (n+1))
  self_ext : ∀ n, Subsingleton (Ext M M (n+1))
  puncture : OnPuncture M

private theorem kernel_vanishing [IsLocalRing R] [IsNoetherianRing R] {P M : ModuleCat.{u} R}
    [Module.Free R P] [Module.Finite R P] (f : P →ₗ[R] M) (hf : Function.Surjective f)
    (v : Vanishing M) : Vanishing (ModuleCat.of R (LinearMap.ker f)) := by
  let S := f.shortComplexKer
  have hs := LinearMap.shortExact_shortComplexKer hf
  exact ⟨fun n => shift_down S hs _ n (v.ring_ext (n+1)),
    fun n => syzygy_self_ext S hs n (v.ring_ext (n+1)) (v.self_ext n),
    fun p => (localized_kernel_retract (P := P) (M := M) p.1.asIdeal.primeCompl f hf
      (v.puncture p)).1⟩

private theorem free_from_kernel [IsLocalRing R] [IsNoetherianRing R] {P M : ModuleCat.{u} R}
    [Module.Free R P] [Module.Finite R P] [Module.Finite R M] (f : P →ₗ[R] M)
    (hf : Function.Surjective f) (v : Vanishing M) (hk : Module.Free R (LinearMap.ker f)) :
    Module.Free R M := by
  let S := f.shortComplexKer
  have hs := LinearMap.shortExact_shortComplexKer hf
  obtain ⟨r, hr⟩ := extends_to_free_kernel S hs (v.ring_ext 0)
  let split := ShortComplex.Splitting.ofExactOfRetraction S hs.exact r hr hs.epi_g
  have : Projective M := (Retract.mk split.s S.g split.s_g).projective
  have : Module.Projective R M := ModuleCat.projective_of_module_projective M
  exact Module.free_of_flat_of_isLocalRing

private theorem high_syzygy [IsLocalRing R] [IsNoetherianRing R] (M : ModuleCat.{u} R)
    [Module.Finite R M] (v : Vanishing M) (n : ℕ) :
    ∃ W : ModuleCat.{u} R, Module.Finite R W ∧ Vanishing W ∧ Module.IsReflexive R W ∧
      (∀ j < n, Subsingleton (Ext (DualObj W) (ModuleCat.of R R) (j+1))) ∧
      (Module.Free R W → Module.Free R M) := by
  induction n with
  | zero =>
    obtain ⟨P, _, _, _, _, f, hf⟩ := Module.exists_finite_presentation R M
    let K := ModuleCat.of R (LinearMap.ker f)
    have vk := kernel_vanishing (P := ModuleCat.of R P) (M := M) f hf v
    obtain ⟨Q, _, _, _, _, g, hg⟩ := Module.exists_finite_presentation R K
    exact ⟨ModuleCat.of R (LinearMap.ker g), inferInstance,
      kernel_vanishing (P := ModuleCat.of R Q) (M := K) g hg vk,
      reflexive_kernel (P := ModuleCat.of R Q) (M := K) g hg (vk.ring_ext 0)
        (eval_kernel_injective (P := ModuleCat.of R P) (M := M) f),
      fun _ h => (Nat.not_lt_zero _ h).elim,
      fun h => free_from_kernel (P := ModuleCat.of R P) (M := M) f hf v
        (free_from_kernel (P := ModuleCat.of R Q) (M := K) g hg vk h)⟩
  | succ n ih =>
    obtain ⟨W, hfin, vw, href, hdual, descend⟩ := ih
    obtain ⟨P, _, _, _, _, f, hf⟩ := Module.exists_finite_presentation R W
    let F := ModuleCat.of R P
    exact ⟨ModuleCat.of R (LinearMap.ker f), inferInstance, kernel_vanishing (P := F) f hf vw,
      reflexive_kernel (P := F) f hf (vw.ring_ext 0) (Module.bijective_dual_eval R W).1,
      dual_ext_kernel (P := F) f hf (vw.ring_ext 0) n hdual,
      fun h => descend (free_from_kernel (P := F) f hf vw h)⟩

private theorem dual_on_puncture [IsLocalRing R] [IsNoetherianRing R] (X : ModuleCat.{u} R)
    [Module.Finite R X] (hx : OnPuncture X) : OnPuncture (DualObj X) := by
  intro p
  have : Module.Projective (Localization.AtPrime p.1.asIdeal)
      (LocalizedModule p.1.asIdeal.primeCompl X) := hx p
  have : Module.Flat (Localization.AtPrime p.1.asIdeal) (LocalizedModule p.1.asIdeal.primeCompl X) :=
    Module.Flat.of_projective
  have : Module.Free (Localization.AtPrime p.1.asIdeal) (LocalizedModule p.1.asIdeal.primeCompl X) :=
    Module.free_of_flat_of_isLocalRing
  have : Module.FinitePresentation R X := Module.finitePresentation_of_finite R X
  let A := Localization.AtPrime p.1.asIdeal
  let j := IsLocalizedModule.mapExtendScalars p.1.asIdeal.primeCompl
    (LocalizedModule.mkLinearMap p.1.asIdeal.primeCompl X) (Algebra.linearMap R A) A
  have mem : p.1 ∈ Module.freeLocus R (Module.Dual R X) :=
    (Module.mem_freeLocus_of_isLocalization p.1 A _ j).mpr inferInstance
  exact @Module.Projective.of_free (Localization.AtPrime p.1.asIdeal) _
    (LocalizedModule p.1.asIdeal.primeCompl (DualObj X)) _ _ mem

private def matrixAction {I J : Type u} [Fintype I] (D : I → J → R) (K : ModuleCat.{u} R) :
    (I → K) →ₗ[R] (J → K) :=
  LinearMap.pi fun j => ∑ i, D i j • LinearMap.proj i

private theorem matrixAction_apply {I J : Type u} [Fintype I] (D : I → J → R)
    (K : ModuleCat.{u} R) (v : I → K) (j : J) : matrixAction D K v j = ∑ i, D i j • v i := by
  simp [matrixAction, LinearMap.sum_apply]

private theorem matrixAction_single {I J : Type u} [Fintype I] [DecidableEq I] (D : I → J → R)
    (i : I) (j : J) : matrixAction D (ModuleCat.of R R) (Pi.single i 1) j = D i j := by
  rw [matrixAction_apply, Finset.sum_eq_single i]
  · simp only [Pi.single_eq_same, smul_eq_mul, mul_one]
  · intro l _ h
    rw [Pi.single_eq_of_ne h, smul_zero]
  · simp

private noncomputable def homMatrixKernel {I J : Type u} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (D : I → J → R) (X K : ModuleCat.{u} R)
    (q : (I → R) →ₗ[R] X) (hq : Function.Surjective q)
    (ex : Function.Exact (matrixAction (fun j i => D i j) (ModuleCat.of R R)) q) :
    (X →ₗ[R] K) ≃ₗ[R] LinearMap.ker (matrixAction D K) := by
  let a := matrixAction (fun j i => D i j) (ModuleCat.of R R)
  let e := LinearEquiv.piRing R K I R
  let f := e.toLinearMap.comp (q.lcomp R K)
  have inj : Function.Injective f := by
    intro h h' eq
    have eq' : q.lcomp R K h = q.lcomp R K h' := e.injective eq
    ext x
    obtain ⟨v, rfl⟩ := hq x
    exact LinearMap.congr_fun eq' v
  have eqr : LinearMap.range f = LinearMap.ker (matrixAction D K) := by
    ext v
    have ev (j : J) : e.symm v (a (Pi.single j 1)) = matrixAction D K v j := by
      rw [matrixAction_apply]
      change (LinearEquiv.piRing R K I R).symm v _ = _
      rw [LinearEquiv.piRing_symm_apply]
      exact Finset.sum_congr rfl fun i _ =>
        congrArg (fun r : R => r • v i) (matrixAction_single (fun l m => D m l) j i)
    have he : (a.lcomp R K) (e.symm v) = 0 ↔ matrixAction D K v = 0 := by
      constructor
      · intro h
        ext j
        have e' := LinearMap.congr_fun h (Pi.single j 1)
        change e.symm v (a (Pi.single j 1)) = 0 at e'
        exact (ev j).symm.trans e'
      · intro h
        apply LinearMap.pi_ext
        intro j x
        have ej : a (Pi.single j x) = x • a (Pi.single j 1) := by
          rw [← map_smul]
          congr 1
          ext l
          by_cases eh : l = j
          · subst l
            simp
          · simp [Pi.single_eq_of_ne eh]
        change e.symm v (a (Pi.single j x)) = 0
        rw [ej, map_smul]
        have zero : e.symm v (a (Pi.single j 1)) = 0 := by
          exact (ev j).trans (congrFun h j)
        rw [zero, smul_zero]
    rw [LinearMap.mem_ker, ← he, LinearMap.exact_lcomp_of_exact_of_surjective K ex hq (e.symm v)]
    constructor
    · rintro ⟨l, rfl⟩
      exact ⟨l, (e.symm_apply_apply _).symm⟩
    · rintro ⟨l, eq⟩
      exact ⟨l, (e.eq_symm_apply).mp eq⟩
  exact (LinearEquiv.ofInjective f inj).trans (LinearEquiv.ofEq _ _ eqr)

/-- The dual of a second syzygy has the transposed presentation matrix. -/
private theorem transposePresentation {I J : Type u} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (W : ModuleCat.{u} R)
    (f : (J → R) →ₗ[R] W) (hf : Function.Surjective f)
    (g : (I → R) →ₗ[R] LinearMap.ker f) (hg : Function.Surjective g)
    (hW : Subsingleton (Ext W (ModuleCat.of R R) 1))
    (hK : Subsingleton (Ext (ModuleCat.of R (LinearMap.ker f)) (ModuleCat.of R R) 1)) :
    let D (i : I) (j : J) := (g (Pi.single i 1)).val j
    ∃ q : (I → R) →ₗ[R] Module.Dual R (LinearMap.ker g), Function.Surjective q ∧
      Function.Exact (matrixAction (fun j i => D i j) (ModuleCat.of R R)) q := by
  let D (i : I) (j : J) := (g (Pi.single i 1)).val j
  let e := LinearEquiv.piRing R R I R
  let e' := LinearEquiv.piRing R R J R
  let i := (LinearMap.ker f).subtype
  let q := (LinearMap.ker g).subtype.dualMap.comp e.symm.toLinearMap
  have sur := dual_kernel_exact (P := ModuleCat.of R (I → R)) (M := ModuleCat.of R (LinearMap.ker f)) g hg hK
  refine ⟨q, sur.comp e.symm.surjective, ?_⟩
  let ex := LinearMap.exact_lcomp_of_exact_of_surjective R g.exact_subtype_ker_map hg
  have diag (l : J → R) : matrixAction (fun j i => D i j) (ModuleCat.of R R) l =
      e (g.dualMap (i.dualMap (e'.symm l))) := by
    ext m
    simp only [matrixAction_apply, e, e', LinearEquiv.piRing_apply, LinearMap.dualMap_apply,
      LinearEquiv.piRing_symm_apply]
    rfl
  intro v
  change (LinearMap.ker g).subtype.dualMap (e.symm v) = 0 ↔ _
  rw [show (LinearMap.ker g).subtype.dualMap = (LinearMap.ker g).subtype.lcomp R R from rfl, ex]
  constructor
  · rintro ⟨l, hl⟩
    obtain ⟨l', rfl⟩ := dual_kernel_exact (P := ModuleCat.of R (J → R)) (M := W) f hf hW l
    refine ⟨e' l', ?_⟩
    rw [diag, e'.symm_apply_apply]
    exact (e.eq_symm_apply).mp hl
  · rintro ⟨l, rfl⟩
    refine ⟨i.dualMap (e'.symm l), ?_⟩
    rw [diag, e.symm_apply_apply]
    rfl

/-- A nonzero socle element detects a nonsplit extension at a minimal relation
matrix. The last equality in the proof takes the trace in both orders. -/
private theorem matrix_obstruction [IsLocalRing R] {I J : Type u}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] (i₀ : I)
    (D : I → J → R) (K : ModuleCat.{u} R) (z : K) (hn : z ≠ 0)
    (hsoc : ∀ r ∈ maximalIdeal R, r • z = 0)
    (hD : ∀ i j, D i j ∈ maximalIdeal R)
    (hmin : ∀ v ∈ LinearMap.ker (matrixAction D (ModuleCat.of R R)), ∀ i, v i ∈ maximalIdeal R) :
    ¬ Subsingleton (Ext
      (ModuleCat.of R ((J → R) ⧸ LinearMap.range (matrixAction D (ModuleCat.of R R))))
      (ModuleCat.of R (LinearMap.ker (matrixAction D K))) 1) := by
  intro h
  let d := matrixAction D (ModuleCat.of R R)
  let T := LinearMap.ker (matrixAction D K)
  let z₀ : T := ⟨Pi.single i₀ z, by
    ext j
    change matrixAction D K _ j = 0
    rw [matrixAction_apply, Finset.sum_eq_single i₀]
    · rw [Pi.single_eq_same]
      exact hsoc _ (hD i₀ j)
    · intro i _ hi
      rw [Pi.single_eq_of_ne hi, smul_zero]
    · exact fun hn => (hn (Finset.mem_univ _)).elim⟩
  let φ := (LinearMap.toSpanSingleton R T z₀).comp (LinearMap.proj i₀ : (I → R) →ₗ[R] R)
  have vanish : LinearMap.ker d ≤ LinearMap.ker φ := by
    intro x hx
    apply Subtype.ext
    ext i
    change x i₀ • (Pi.single i₀ z : I → K) i = 0
    by_cases e : i = i₀
    · subst i
      rw [Pi.single_eq_same]
      exact hsoc _ (hmin x hx i₀)
    · rw [Pi.single_eq_of_ne e, smul_zero]
  let φ' := ((LinearMap.ker d).liftQ φ vanish).comp d.quotKerEquivRange.symm.toLinearMap
  let V := LinearMap.range d
  let S := ModuleCat.shortComplexOfCompEqZero V.subtype V.mkQ (LinearMap.exact_subtype_mkQ V).linearMap_comp_eq_zero
  have hS := ModuleCat.shortComplex_shortExact S (LinearMap.exact_subtype_mkQ V)
    V.subtype_injective V.mkQ_surjective
  obtain ⟨b, hb⟩ := extends_of_ext_one S hS (ModuleCat.of R T) h (ModuleCat.ofHom φ')
  let eI (i : I) : I → R := fun j => if i = j then 1 else 0
  let eJ (i : J) : J → R := fun j => if i = j then 1 else 0
  have de (i : I) (j : J) : d (eI i) j = D i j := by
    simp [d, matrixAction_apply, eI, smul_eq_mul, mul_ite]
  have ev (i : I) : b (d (eI i)) = φ (eI i) := by
    have hh := congrArg (fun f : S.X₁ ⟶ ModuleCat.of R T => f (d.rangeRestrict (eI i))) hb
    change b (d (eI i)) = (LinearMap.ker d).liftQ φ vanish
      (d.quotKerEquivRange.symm ⟨d (eI i), _⟩) at hh
    rwa [LinearMap.quotKerEquivRange_symm_apply_image] at hh
  have row (i : I) : (∑ j, D i j • (b (eJ j)).1 i) = if i = i₀ then z else 0 := by
    have col := LinearMap.pi_apply_eq_sum_univ b.hom (d (eI i))
    have sumEq := congrArg (fun v : T => v.1 i) col
    simp only [de, Submodule.coe_sum, Finset.sum_apply, SetLike.val_smul,
      Pi.smul_apply] at sumEq
    rw [← sumEq, ev]
    change (if i = i₀ then (1 : R) else 0) • (Pi.single i₀ z : I → K) i = _
    by_cases hi : i = i₀
    · subst i
      rw [if_pos rfl, one_smul, Pi.single_eq_same, if_pos rfl]
    · rw [if_neg hi, zero_smul, if_neg hi]
  have col (j : J) : ∑ i, D i j • (b (eJ j)).1 i = 0 := by
    simpa only [matrixAction_apply, Pi.zero_apply] using congrFun (b (eJ j)).2 j
  apply hn
  calc
    z = ∑ i, (if i = i₀ then z else 0) := by simp
    _ = ∑ i, ∑ j, D i j • (b (eJ j)).1 i := Finset.sum_congr rfl fun i _ => (row i).symm
    _ = ∑ j, ∑ i, D i j • (b (eJ j)).1 i := Finset.sum_comm
    _ = 0 := by simp [col]

open scoped Pointwise

open RingTheory.Sequence in
theorem exists_first_residue_ext [IsNoetherianRing R] [IsDomain R] [IsIntegrallyClosed R]
    [IsLocalRing R] (hd : 1 < ringKrullDim R) :
    ∃ t : ℕ, 2 ≤ t ∧ ¬ Subsingleton (Ext (ModuleCat.of R (ResidueField R)) (ModuleCat.of R R) t) ∧
      ∀ i < t, Subsingleton (Ext (ModuleCat.of R (ResidueField R)) (ModuleCat.of R R) i) := by
  classical
  let k := ModuleCat.of R (ResidueField R)
  let A := ModuleCat.of R R
  let m := maximalIdeal R
  have sm : m • (⊤ : Submodule R R) < ⊤ := by simpa [m] using (maximalIdeal.isMaximal R).lt_top
  have supp : Module.support R k = PrimeSpectrum.zeroLocus m := by
    change Module.support R (R ⧸ m) = _
    rw [Module.support_eq_zeroLocus, Ideal.annihilator_quotient]
  have ex : ∃ i, ¬ Subsingleton (Ext k A i) := by
    by_contra! hz
    let d := m.spanFinrank
    obtain ⟨rs, len, _, reg⟩ := ModuleCat.exists_isRegular_of_exists_subsingleton_ext m (d+1)
      A sm k supp (fun i _ => hz i)
    have proper : Ideal.ofList rs ≠ ⊤ := by
      have h := reg.2
      simpa [A] using Ne.symm h
    have : Nontrivial (R ⧸ Ideal.ofList rs) := Ideal.Quotient.nontrivial_iff.mpr proper
    have hdim := ringKrullDim_add_length_eq_ringKrullDim_of_isRegular rs reg
    have lo : (d+1 : ℕ) ≤ ringKrullDim R := by
      rw [← hdim, len]
      simpa only [zero_add] using add_le_add_left
        (ringKrullDim_nonneg_of_nontrivial (R := R ⧸ Ideal.ofList rs)) (↑(d + 1 : ℕ))
    have e : ((d+1 : ℕ) : WithBot ℕ∞) ≤ d := lo.trans (ringKrullDim_le_spanFinrank_maximalIdeal R)
    exact (Nat.not_succ_le_self d) (by exact_mod_cast e)
  obtain ⟨x, hx, hx0, y, hy, hyreg⟩ := regular_pair hd
  have mem : ∀ r ∈ [x, y], r ∈ m := by simpa [m] using And.intro hx hy
  have hy' : IsSMulRegular (QuotSMulTop x R) y := by
    change IsSMulRegular (R ⧸ x • (⊤ : Ideal R)) y
    have he : Ideal.span {x} = x • (⊤ : Ideal R) := by simp [← Submodule.ideal_span_singleton_smul]
    rw [← he]
    exact hyreg
  have reg : IsRegular R [x,y] := IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal R mem <|
    (isWeaklyRegular_cons_iff R x [y]).mpr
      ⟨fun _ _ e => mul_left_cancel₀ hx0 e, (isWeaklyRegular_singleton_iff _ _).mpr hy'⟩
  have van := ModuleCat.subsingleton_ext_of_exists_isRegular m k supp.subset A sm [x,y] mem reg
  change ∃ t, 2 ≤ t ∧ ¬ Subsingleton (Ext k A t) ∧ ∀ i < t, Subsingleton (Ext k A i)
  refine ⟨Nat.find ex, ?_, Nat.find_spec ex, fun i hi => not_not.mp (Nat.find_min ex hi)⟩
  exact Nat.le_of_not_lt fun hn => Nat.find_spec ex (van (Nat.find ex) hn)

private theorem transport_ext {X X' Y Y' : ModuleCat.{u} R} (e : X ≅ X') (f : Y ≅ Y') (n : ℕ)
    (h : Subsingleton (Ext X Y n)) : Subsingleton (Ext X' Y' n) := by
  let a := ((Abelian.extFunctor n).mapIso e.symm.op).app Y
  let b := (Abelian.extFunctorObj X' n).mapIso f
  exact (a.trans b).addCommGroupIsoToAddEquiv.subsingleton_congr.mp h

private theorem socle_element [IsLocalRing R] (Z : ModuleCat.{u} R)
    (hn : ¬ Subsingleton (Ext (ModuleCat.of R (ResidueField R)) Z 0)) :
    ∃ z : Z, z ≠ 0 ∧ ∀ r ∈ maximalIdeal R, r • z = 0 := by
  let k := ModuleCat.of R (ResidueField R)
  have nh : ¬ Subsingleton (k →ₗ[R] Z) := fun h =>
    hn ((Ext.addEquiv₀.trans (ModuleCat.homAddEquiv (M := k) (N := Z))).subsingleton_congr.mpr h)
  obtain ⟨a, ha⟩ : ∃ a : k →ₗ[R] Z, a ≠ 0 := by
    by_contra! h
    exact nh ⟨fun x y => (h x).trans (h y).symm⟩
  obtain ⟨x, hx⟩ : ∃ x : k, a x ≠ 0 := by
    by_contra! h
    exact ha (LinearMap.ext h)
  refine ⟨a x, hx, fun r hr => ?_⟩
  rw [← a.map_smul]
  change a (residue R r * x) = 0
  rw [(residue_eq_zero_iff _).mpr hr, zero_mul, map_zero]

private theorem punctured_free [IsNoetherianRing R] [IsDomain R] [IsIntegrallyClosed R]
    [IsLocalRing R] (M : ModuleCat.{u} R) [Module.Finite R M] (dim : 1 < ringKrullDim R)
    (v : Vanishing M) : Module.Free R M := by
  classical
  obtain ⟨t, ht, nonzero, low⟩ := exists_first_residue_ext dim
  obtain ⟨n, rfl⟩ : ∃ n, t = n+2 := ⟨t-2, by omega⟩
  obtain ⟨W, wfin, vw, wref, wd, descend⟩ := high_syzygy M v (n+2)
  apply descend
  obtain ⟨J, fj, f, hf, fmin⟩ := minimal_cover W
  let P := ModuleCat.of R (J → R)
  let K := ModuleCat.of R (LinearMap.ker f)
  have vk := kernel_vanishing (P := P) (M := W) f hf vw
  obtain ⟨I, fi, g, hg, gmin⟩ := minimal_cover K
  let Q := ModuleCat.of R (I → R)
  let Y := ModuleCat.of R (LinearMap.ker g)
  by_cases empty : IsEmpty I
  · have : Subsingleton K := hg.subsingleton
    exact free_from_kernel (P := P) (M := W) f hf vw (inferInstanceAs (Module.Free R K))
  obtain ⟨i₀⟩ := not_isEmpty_iff.mp empty
  have kr : Module.IsReflexive R K :=
    reflexive_kernel (P := P) (M := W) f hf (vw.ring_ext 0) (Module.bijective_dual_eval R W).1
  have yr : Module.IsReflexive R Y :=
    reflexive_kernel (P := Q) (M := K) g hg (vk.ring_ext 0) (Module.bijective_dual_eval R K).1
  have kd := dual_ext_kernel (P := P) (M := W) f hf (vw.ring_ext 0) _ wd
  have yd := dual_ext_kernel (P := Q) (M := K) g hg (vk.ring_ext 0) _ kd
  let X := DualObj Y
  have : Module.Finite R X := Module.Finite.of_surjective (LinearMap.ker g).subtype.dualMap
    (dual_kernel_exact (P := Q) (M := K) g hg (vk.ring_ext 0))
  have vy := kernel_vanishing (P := Q) (M := K) g hg vk
  have xf := dual_on_puncture Y vy.puncture
  have fr (j : ℕ) := ext_finite_free W P (j+1) (vw.ring_ext j)
  have gr (j : ℕ) := ext_finite_free W Q (j+1) (vw.ring_ext j)
  have sk := (shift_coeff W f.shortComplexKer (LinearMap.shortExact_shortComplexKer hf)
    (n+1) (fr n) (fr (n+1))).mp (vw.self_ext n)
  have sy := (shift_coeff W g.shortComplexKer (LinearMap.shortExact_shortComplexKer hg)
    (n+2) (gr (n+1)) (gr (n+2))).mp sk
  let ev : Y ≅ HomObj X (ModuleCat.of R R) := (Module.evalEquiv R Y).toModuleIso
  obtain ⟨Z, hz, he⟩ := test_module X W xf vw.puncture (n+2) (ModuleCat.of R R) nonzero low
    (fun j hj => yd j (by omega)) (transport_ext (Iso.refl W) ev _ sy)
  obtain ⟨z, hn, hkill⟩ := socle_element Z hz
  let D (i : I) (j : J) := (g (Pi.single i 1)).val j
  let d := matrixAction D (ModuleCat.of R R)
  have de : d = f.ker.subtype.comp g := by
    apply LinearMap.pi_ext
    intro i r
    have eq : Pi.single i r = r • (Pi.single i 1 : I → R) := by
      ext l
      by_cases hi : l = i <;> simp [hi]
    rw [eq, map_smul, map_smul]
    congr 1
    ext j
    exact matrixAction_single D i j
  have ex : Function.Exact d f := by
    rw [de, LinearMap.exact_iff, LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr hg),
      Submodule.range_subtype]
  let ew : ModuleCat.of R ((J → R) ⧸ LinearMap.range d) ≅ W :=
    (ex.linearEquivOfSurjective hf).toModuleIso
  obtain ⟨q, hq, hex⟩ := transposePresentation W f hf g hg (vw.ring_ext 0) (vk.ring_ext 0)
  let eqZ : HomObj X Z ≅ ModuleCat.of R (LinearMap.ker (matrixAction D Z)) :=
    (homMatrixKernel D X Z q hq hex).toModuleIso
  have hmin (c : I → R) (hc : c ∈ LinearMap.ker d) : ∀ i, c i ∈ maximalIdeal R := by
    apply gmin c
    apply Subtype.ext
    exact (congrArg (fun l : (I → R) →ₗ[R] (J → R) => l c) de.symm).trans hc
  exact (matrix_obstruction i₀ D Z z hn hkill
    (fun i j => fmin _ (g (Pi.single i 1)).property j) hmin
    (transport_ext ew.symm eqZ 1 he)).elim

theorem projective_of_punctured_case [IsNoetherianRing R] [IsDomain R] [IsIntegrallyClosed R]
    (M : ModuleCat.{u} R) [Module.Finite R M]
    (hr : ∀ n, Subsingleton (Ext M (ModuleCat.of R R) (n+1)))
    (hm : ∀ n, Subsingleton (Ext M M (n+1)))
    (localCase : ∀ (A : Type u) [CommRing A] [IsNoetherianRing A] [IsDomain A]
      [IsIntegrallyClosed A] [IsLocalRing A] (N : ModuleCat.{u} A) [Module.Finite A N],
      1 < ringKrullDim A →
      (∀ q : PrimeSpectrum A, q.asIdeal ≠ IsLocalRing.maximalIdeal A → q ∈ Module.freeLocus A N) →
      (∀ n, Subsingleton (Ext N (ModuleCat.of A A) (n+1))) →
      (∀ n, Subsingleton (Ext N N (n+1))) → Module.Free A N) :
    Module.Projective R M := by
  have : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
  rw [← Module.freeLocus_eq_univ_iff, Set.eq_univ_iff_forall]
  intro p
  let ht (q : PrimeSpectrum R) := q.asIdeal.height.toNat
  induction p using (measure ht).wf.induction with
  | h p ih =>
    let U := p.asIdeal.primeCompl
    let A := Localization.AtPrime p.asIdeal
    let N := ModuleCat.of A (LocalizedModule U M)
    have : IsIntegrallyClosed A :=
      isIntegrallyClosed_of_isLocalization A U p.asIdeal.primeCompl_le_nonZeroDivisors
    have er (n : ℕ) : Subsingleton (Ext N (ModuleCat.of A A) (n+1)) :=
      localized_ext U M (ModuleCat.of R R) (ModuleCat.of A A) (Algebra.linearMap R A) n (hr n)
    change Module.Free A N
    by_cases low : ringKrullDim A ≤ 1
    · have dim : Ring.KrullDimLE 1 A := Ring.krullDimLE_iff.mpr (by simpa using low)
      have : Ring.DimensionLEOne A :=
        ⟨fun hp h => (Ring.krullDimLE_one_iff_of_isPrime_bot.mp dim) _ hp h⟩
      have : IsDedekindDomain A := { }
      exact free_of_ext_pid N (er 0)
    · apply localCase A N (lt_of_not_ge low) _ er
      · intro n
        exact localized_ext U M M N (LocalizedModule.mkLinearMap U M) n (hm n)
      · intro q hq
        change q ∈ Module.freeLocus (Localization U) (LocalizedModule U M)
        rw [Module.freeLocus_localization]
        let q' := PrimeSpectrum.comap (algebraMap R A) q
        apply ih q'
        have le : q'.asIdeal ≤ p.asIdeal := by
          rw [← Localization.AtPrime.under_maximalIdeal (I := p.asIdeal)]
          exact Ideal.comap_mono (IsLocalRing.le_maximalIdeal q.isPrime.ne_top)
        have lt : q'.asIdeal < p.asIdeal := lt_of_le_of_ne le
          (fun e => hq (Localization.AtPrime.eq_maximalIdeal_iff_under_eq.mp e))
        have lt' := Ideal.height_strict_mono_of_isPrime lt
        change q'.asIdeal.height.toNat < p.asIdeal.height.toNat
        exact_mod_cast (show (q'.asIdeal.height.toNat : ℕ∞) < p.asIdeal.height.toNat by
          simpa only [ENat.natCast_toNat_eq_self.mpr (q'.asIdeal.height_ne_top q'.isPrime.ne_top),
            ENat.natCast_toNat_eq_self.mpr (p.asIdeal.height_ne_top p.isPrime.ne_top)] using lt')

end OMA.Normal

theorem OMA.solution : type_of% @AuslanderReiten.auslander_reiten.variants.normal := by
  intro R _ _ M _ _ _ _ _ hr hm
  apply OMA.Normal.projective_of_punctured_case (ModuleCat.of R M)
    (fun i => hr (i+1) (by omega)) (fun i => hm (i+1) (by omega))
  intro A _ _ _ _ _ N _ hd hp er em
  apply OMA.Normal.punctured_free N hd
  refine ⟨er, em, fun p => ?_⟩
  exact @Module.Projective.of_free (Localization.AtPrime p.1.asIdeal) _
    (LocalizedModule p.1.asIdeal.primeCompl N) _ _ (hp p.1 p.2)
