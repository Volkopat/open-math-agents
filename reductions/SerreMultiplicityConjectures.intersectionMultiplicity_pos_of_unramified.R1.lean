import FormalConjectures.Wikipedia.SerreMultiplicityConjectures
import Mathlib

/-!
Serre Positivity in Mixed Characteristic (Unramified): Reduction

This file reduces the unramified mixed-characteristic Serre positivity theorem
from arbitrary finitely generated modules `M, N` over an unramified regular local ring `R`
in an arbitrary universe `u` to four canonical `Type 0` theorems:

1. `H1`: `m`-adic completion of a Noetherian local ring is Noetherian and preserves quotient
   Krull dimensions.
2. `H2`: Additivity of `Module.intersectionMultiplicity` on short exact sequences of finite
   modules over a regular local ring (in both arguments).
3. `H3`: Cohen structure theorem for complete unramified mixed-characteristic regular local
   rings (`S ≃+* MvPowerSeries (Fin n) V` over a complete DVR `V` with uniformizer `p`).
4. `H4`: Serre non-negativity and positivity for prime quotients of `MvPowerSeries (Fin n) V`
   over a complete DVR `V`.

In `main`, we prove:
- Flat base change of `CategoryTheory.Tor` and `Module.intersectionMultiplicity` along any
  flat local homomorphism `A →+* R` with `m_A R = m_R` (`A : Type 0`, `R : Type u`).
- Countable syzygy-closed regular local descent from `(R, M, N)` in `Type u` to `(A, M₀, N₀)`
  in `Type 0` with `R` faithfully flat over `A`.
- Completion reduction `A → AdicCompletion (maximalIdeal A) A` via `H1`.
- Transport along `e : MvPowerSeries (Fin n) V ≃+* S` via `H3`.
- Double prime-filtration induction reducing arbitrary finite modules to prime quotients
  via `H2` and `H4`.
-/

namespace OMA.R_SerreMultiplicityConjectures_intersectionMultiplicity_pos_of_unramified_R1

open CategoryTheory Limits MonoidalCategory TensorProduct IsLocalRing

universe u

/-- `m`-adic completion of a Noetherian local ring is Noetherian and preserves the Krull dimension
of every quotient `A ⧸ I`. -/
def H1 : Prop :=
  ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A],
    IsNoetherianRing (AdicCompletion (maximalIdeal A) A) ∧
    ∀ (I : Ideal A),
      ringKrullDim (AdicCompletion (maximalIdeal A) A ⧸
        I.map (algebraMap A (AdicCompletion (maximalIdeal A) A))) =
      ringKrullDim (A ⧸ I)

/-- Additivity of Serre's intersection multiplicity on short exact sequences of finite modules
over a regular local ring, in both arguments. -/
def H2 : Prop :=
  ∀ (R : Type) [CommRing R] [IsRegularLocalRing R]
    (M₁ M₂ M₃ N : Type) [AddCommGroup M₁] [Module R M₁] [Module.Finite R M₁]
    [AddCommGroup M₂] [Module R M₂] [Module.Finite R M₂]
    [AddCommGroup M₃] [Module R M₃] [Module.Finite R M₃]
    [AddCommGroup N] [Module R N] [Module.Finite R N]
    (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃),
    Function.Injective f → Function.Exact f g → Function.Surjective g →
    IsFiniteLength R (M₂ ⊗[R] N) →
    Module.intersectionMultiplicity R M₂ N =
      Module.intersectionMultiplicity R M₁ N + Module.intersectionMultiplicity R M₃ N ∧
    Module.intersectionMultiplicity R N M₂ =
      Module.intersectionMultiplicity R N M₁ + Module.intersectionMultiplicity R N M₃

/-- Cohen's structure theorem for complete unramified mixed-characteristic regular local rings:
every such ring is isomorphic to a formal power series ring `V[[X₁, …, Xₙ]]` over a complete
discrete valuation ring `V` with uniformizer `p`. -/
def H3 : Prop :=
  ∀ (S : Type) [CommRing S] [IsRegularLocalRing S] [IsAdicComplete (maximalIdeal S) S]
    (p : ℕ) [CharP (ResidueField S) p],
    (p : S) ∉ maximalIdeal S ^ 2 →
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V)
      (_ : IsAdicComplete (maximalIdeal V) V) (n : ℕ),
      maximalIdeal V = Ideal.span {(p : V)} ∧
      Nonempty (MvPowerSeries (Fin n) V ≃+* S)

/-- Serre's non-negativity and positivity theorem for prime quotients of a formal power series
ring `V[[X₁, …, Xₙ]]` over a complete discrete valuation ring `V`. -/
def H4 : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [IsAdicComplete (maximalIdeal V) V]
    (n : ℕ) [IsRegularLocalRing (MvPowerSeries (Fin n) V)]
    (P Q : Ideal (MvPowerSeries (Fin n) V)) [P.IsPrime] [Q.IsPrime],
    IsFiniteLength (MvPowerSeries (Fin n) V)
      ((MvPowerSeries (Fin n) V ⧸ P) ⊗[MvPowerSeries (Fin n) V]
        (MvPowerSeries (Fin n) V ⧸ Q)) →
    0 ≤ Module.intersectionMultiplicity (MvPowerSeries (Fin n) V)
          (MvPowerSeries (Fin n) V ⧸ P) (MvPowerSeries (Fin n) V ⧸ Q) ∧
    (ringKrullDim (MvPowerSeries (Fin n) V ⧸ P) +
       ringKrullDim (MvPowerSeries (Fin n) V ⧸ Q) =
       ringKrullDim (MvPowerSeries (Fin n) V) →
     0 < Module.intersectionMultiplicity (MvPowerSeries (Fin n) V)
           (MvPowerSeries (Fin n) V ⧸ P) (MvPowerSeries (Fin n) V ⧸ Q))

section

/- Section 1: Flat base change for `Tor`, `interMult`, `IsFiniteLength`, `annihilator`, and `supportDim` -/

private lemma flat_baseChange_tor_iso
    (A : Type) [CommRing A] (R : Type u) [CommRing R] [Algebra A R] [Module.Flat A R]
    (M₀ N₀ : Type) [AddCommGroup M₀] [Module A M₀] [AddCommGroup N₀] [Module A N₀]
    (i : ℕ) :
    Nonempty
      ((R ⊗[A] (((Tor (ModuleCat.{0} A) i).obj (ModuleCat.of A M₀)).obj (ModuleCat.of A N₀))) ≃ₗ[R]
        (((Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R (R ⊗[A] M₀))).obj
          (ModuleCat.of R (R ⊗[A] N₀)))) := by
  let F : ModuleCat.{0} A ⥤ ModuleCat.{u} R := {
    obj := fun M => ModuleCat.of R (R ⊗[A] M)
    map := fun g => ModuleCat.ofHom (LinearMap.baseChange R g.hom)
    map_id := fun _ => by ext x; simp
    map_comp := fun _ _ => by ext x; simp
  }
  have hFAdd : F.Additive := {
    map_add := fun {X Y g₁ g₂} => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact LinearMap.congr_fun (LinearMap.baseChange_add (A := R) g₁.hom g₂.hom) x
  }
  have hFExact : ∀ (S : ShortComplex (ModuleCat.{0} A)), S.Exact → (S.map F).Exact := by
    intro S hS
    rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hS ⊢
    exact Module.Flat.lTensor_exact (R := A) (M := R) hS
  have hFLim : PreservesFiniteLimits F :=
    (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono F).mpr fun S hS => by
      refine ⟨hFExact S hS.exact, ?_⟩
      rw [ModuleCat.mono_iff_injective]
      exact Module.Flat.lTensor_preserves_injective_linearMap S.f.hom
        ((ModuleCat.mono_iff_injective S.f).mp hS.mono_f)
  have hFColim : PreservesFiniteColimits F :=
    (Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi F).mpr fun S hS => by
      refine ⟨hFExact S hS.exact, ?_⟩
      rw [ModuleCat.epi_iff_surjective]
      exact LinearMap.lTensor_surjective R ((ModuleCat.epi_iff_surjective S.g).mp hS.epi_g)
  have hFHom : F.PreservesHomology := inferInstance
  have hFProj : F.PreservesProjectiveObjects := {
    projective_obj := fun {X} hX => by
      have : Module.Projective A X := (IsProjective.iff_projective (R := A) X).mpr hX
      have : Module.Projective R (R ⊗[A] X) := Module.Projective.tensorProduct
      exact (IsProjective.iff_projective (R := R) (F.obj X)).mp this
  }
  let L_A := (tensoringLeft (ModuleCat.{0} A)).obj (ModuleCat.of A M₀)
  let L_R := (tensoringLeft (ModuleCat.{u} R)).obj (ModuleCat.of R (R ⊗[A] M₀))
  let compEquiv : ∀ (Q : ModuleCat.{0} A),
      (L_A ⋙ F).obj Q ≃ₗ[R] (F ⋙ L_R).obj Q := fun Q =>
    ((AlgebraTensorModule.assoc A A R R M₀ Q).symm).trans
      ((AlgebraTensorModule.cancelBaseChange A R R (R ⊗[A] M₀) Q).symm)
  let compIso : ∀ (Q : ModuleCat.{0} A), (L_A ⋙ F).obj Q ≅ (F ⋙ L_R).obj Q := fun Q =>
    { hom := ModuleCat.ofHom (X := (L_A ⋙ F).obj Q) (Y := (F ⋙ L_R).obj Q)
        (compEquiv Q).toLinearMap
      inv := ModuleCat.ofHom (X := (F ⋙ L_R).obj Q) (Y := (L_A ⋙ F).obj Q)
        (compEquiv Q).symm.toLinearMap
      hom_inv_id := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        exact (compEquiv Q).symm_apply_apply x
      inv_hom_id := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        exact (compEquiv Q).apply_symm_apply x }
  have hnat : ∀ {Q₁ Q₂ : ModuleCat.{0} A} (g : Q₁ ⟶ Q₂),
      CategoryStruct.comp ((L_A ⋙ F).map g) (compIso Q₂).hom =
        CategoryStruct.comp (compIso Q₁).hom ((F ⋙ L_R).map g) := by
    intro Q₁ Q₂ g
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x₁ x₂ hx₁ hx₂ =>
      rw [map_add, map_add, hx₁, hx₂]
    | tmul r z =>
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add z₁ z₂ hz₁ hz₂ =>
        rw [TensorProduct.tmul_add, map_add, map_add, hz₁, hz₂]
      | tmul m q =>
        change compEquiv Q₂ (r ⊗ₜ[A] (m ⊗ₜ[A] g q)) =
          (LinearMap.lTensor (R ⊗[A] M₀) (LinearMap.baseChange R g.hom))
            (compEquiv Q₁ (r ⊗ₜ[A] (m ⊗ₜ[A] q)))
        rfl
  let P : ProjectiveResolution (ModuleCat.of A N₀) := projectiveResolution (ModuleCat.of A N₀)
  let FP : ProjectiveResolution (F.obj (ModuleCat.of A N₀)) := F.mapProjectiveResolution P
  let iso1 : F.obj (((Tor (ModuleCat.{0} A) i).obj (ModuleCat.of A M₀)).obj (ModuleCat.of A N₀)) ≅
      F.obj ((HomologicalComplex.homologyFunctor (ModuleCat.{0} A) _ i).obj
        ((L_A.mapHomologicalComplex _).obj P.complex)) :=
    F.mapIso (P.isoLeftDerivedObj L_A i)
  let K := (L_A.mapHomologicalComplex _).obj P.complex
  let iso2 : F.obj ((HomologicalComplex.homologyFunctor (ModuleCat.{0} A) _ i).obj K) ≅
      (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) _ i).obj
        ((F.mapHomologicalComplex _).obj K) :=
    ((K.sc i).mapHomologyIso F).symm
  let cpxIso : (F.mapHomologicalComplex _).obj K ≅
      (L_R.mapHomologicalComplex _).obj FP.complex :=
    HomologicalComplex.Hom.isoOfComponents
      (fun n => compIso (P.complex.X n))
      (fun i j _ => (hnat (P.complex.d i j)).symm)
  let iso3 : (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) _ i).obj
        ((F.mapHomologicalComplex _).obj K) ≅
      (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) _ i).obj
        ((L_R.mapHomologicalComplex _).obj FP.complex) :=
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) _ i).mapIso cpxIso
  let iso4 : (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) _ i).obj
        ((L_R.mapHomologicalComplex _).obj FP.complex) ≅
      ((Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R (R ⊗[A] M₀))).obj
        (ModuleCat.of R (R ⊗[A] N₀)) :=
    (FP.isoLeftDerivedObj L_R i).symm
  exact ⟨(iso1 ≪≫ iso2 ≪≫ iso3 ≪≫ iso4).toLinearEquiv⟩

private lemma interMult_congr
    {R : Type u} [CommRing R]
    {M₁ M₂ N₁ N₂ : Type u} [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
    [AddCommGroup N₁] [Module R N₁] [AddCommGroup N₂] [Module R N₂]
    (eM : M₁ ≃ₗ[R] M₂) (eN : N₁ ≃ₗ[R] N₂) :
    Module.intersectionMultiplicity R M₁ N₁ = Module.intersectionMultiplicity R M₂ N₂ := by
  unfold Module.intersectionMultiplicity
  congr 1
  ext i
  congr 2
  let iso : ((Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R M₁)).obj (ModuleCat.of R N₁) ≅
      ((Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R M₂)).obj (ModuleCat.of R N₂) :=
    (((Tor (ModuleCat.{u} R) i).mapIso eM.toModuleIso).app _) ≪≫
      (((Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R M₂)).mapIso eN.toModuleIso)
  exact congrArg ENat.toNat iso.toLinearEquiv.length_eq

private lemma flat_baseChange_interMult
    (A : Type) [CommRing A] [IsLocalRing A]
    (R : Type u) [CommRing R] [IsLocalRing R] [Algebra A R]
    [IsLocalHom (algebraMap A R)] [Module.Flat A R]
    (hm : (maximalIdeal A).map (algebraMap A R) = maximalIdeal R)
    (M₀ N₀ : Type) [AddCommGroup M₀] [Module A M₀] [AddCommGroup N₀] [Module A N₀]
    (M N : Type u) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (eM : R ⊗[A] M₀ ≃ₗ[R] M) (eN : R ⊗[A] N₀ ≃ₗ[R] N) :
    Module.intersectionMultiplicity R M N = Module.intersectionMultiplicity A M₀ N₀ := by
  rw [← interMult_congr eM eN]
  unfold Module.intersectionMultiplicity
  congr 1
  ext i
  congr 2
  obtain ⟨eTor⟩ := flat_baseChange_tor_iso A R M₀ N₀ i
  rw [← eTor.length_eq, IsLocalRing.length_baseChange A R, hm]
  have hlen1 : Module.length R (R ⧸ maximalIdeal R) = 1 := by
    have hsimple : IsSimpleModule R (R ⧸ maximalIdeal R) :=
      isSimpleModule_iff_quot_maximal.mpr ⟨maximalIdeal R, inferInstance, ⟨LinearEquiv.refl R _⟩⟩
    exact Module.length_eq_one_iff.mpr hsimple
  rw [hlen1, mul_one]

private lemma flat_baseChange_isFiniteLength_tensor_iff
    (A : Type) [CommRing A] [IsLocalRing A]
    (R : Type u) [CommRing R] [IsLocalRing R] [Algebra A R]
    [IsLocalHom (algebraMap A R)] [Module.Flat A R]
    (hm : (maximalIdeal A).map (algebraMap A R) = maximalIdeal R)
    (M₀ N₀ : Type) [AddCommGroup M₀] [Module A M₀] [AddCommGroup N₀] [Module A N₀]
    (M N : Type u) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (eM : R ⊗[A] M₀ ≃ₗ[R] M) (eN : R ⊗[A] N₀ ≃ₗ[R] N) :
    IsFiniteLength R (M ⊗[R] N) ↔ IsFiniteLength A (M₀ ⊗[A] N₀) := by
  let e : R ⊗[A] (M₀ ⊗[A] N₀) ≃ₗ[R] M ⊗[R] N :=
    ((AlgebraTensorModule.assoc A A R R M₀ N₀).symm).trans
      (((AlgebraTensorModule.cancelBaseChange A R R (R ⊗[A] M₀) N₀).symm).trans
        (AlgebraTensorModule.congr eM eN))
  rw [← Module.length_ne_top_iff, ← Module.length_ne_top_iff, ← e.length_eq,
    IsLocalRing.length_baseChange A R, hm]
  have hlen1 : Module.length R (R ⧸ maximalIdeal R) = 1 := by
    have hsimple : IsSimpleModule R (R ⧸ maximalIdeal R) :=
      isSimpleModule_iff_quot_maximal.mpr ⟨maximalIdeal R, inferInstance, ⟨LinearEquiv.refl R _⟩⟩
    exact Module.length_eq_one_iff.mpr hsimple
  rw [hlen1, mul_one]

private lemma annihilator_baseChange
    (A : Type) [CommRing A] (R : Type u) [CommRing R] [Algebra A R] [Module.Flat A R]
    (M₀ : Type) [AddCommGroup M₀] [Module A M₀] [Module.Finite A M₀] :
    Module.annihilator R (R ⊗[A] M₀) = (Module.annihilator A M₀).map (algebraMap A R) := by
  classical
  apply le_antisymm
  · obtain ⟨s, hs⟩ := ‹Module.Finite A M₀›
    let φ : A →ₗ[A] (s → M₀) := {
      toFun := fun a i => a • (i : M₀)
      map_add' := fun a b => by ext i; exact add_smul a b (i : M₀)
      map_smul' := fun a b => by ext i; exact mul_smul a b (i : M₀)
    }
    have hker : LinearMap.ker φ = Module.annihilator A M₀ := by
      ext a
      simp only [LinearMap.mem_ker, funext_iff, Pi.zero_apply, Module.mem_annihilator, φ,
        LinearMap.coe_mk, AddHom.coe_mk]
      constructor
      · intro h m
        have hm : m ∈ Submodule.span A (s : Set M₀) := by rw [hs]; trivial
        refine Submodule.span_induction ?_ ?_ ?_ ?_ hm
        · intro x hx; exact h ⟨x, hx⟩
        · exact smul_zero a
        · intro x y _ _ hx hy; rw [smul_add, hx, hy, add_zero]
        · intro c x _ hx; rw [smul_comm, hx, smul_zero]
      · intro h i; exact h (i : M₀)
    have hexact : Function.Exact (Module.annihilator A M₀).subtype φ := by
      rw [LinearMap.exact_iff, hker, Submodule.range_subtype]
    have hflat := Module.Flat.lTensor_exact (R := A) (M := R) hexact
    intro r hr
    rw [Module.mem_annihilator] at hr
    have hzero : (LinearMap.lTensor R φ) (r ⊗ₜ[A] (1 : A)) = 0 := by
      have hdecomp : ∀ w : R ⊗[A] (s → M₀),
          w = ∑ i : s, (LinearMap.lTensor R (LinearMap.single A (fun _ : s => M₀) i))
            ((LinearMap.lTensor R (LinearMap.proj (R := A) (φ := fun _ : s => M₀) i)) w) := by
        intro w
        induction w using TensorProduct.induction_on with
        | zero => simp
        | add w₁ w₂ hw₁ hw₂ =>
          conv_lhs => rw [hw₁, hw₂]
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun i _ => by simp
        | tmul r' v =>
          have hv : v = ∑ i : s, LinearMap.single A (fun _ : s => M₀) i (v i) := by
            ext j; simp [LinearMap.single_apply, Finset.sum_apply]
          calc r' ⊗ₜ[A] v = r' ⊗ₜ[A] (∑ i : s, LinearMap.single A (fun _ : s => M₀) i (v i)) := by
                rw [← hv]
            _ = ∑ i : s, r' ⊗ₜ[A] (LinearMap.single A (fun _ : s => M₀) i (v i)) := by
                rw [TensorProduct.tmul_sum]
            _ = _ := by rfl
      rw [hdecomp ((LinearMap.lTensor R φ) (r ⊗ₜ[A] (1 : A)))]
      refine Finset.sum_eq_zero fun i _ => ?_
      have hcomp : (LinearMap.lTensor R (LinearMap.proj (R := A) (φ := fun _ : s => M₀) i))
          ((LinearMap.lTensor R φ) (r ⊗ₜ[A] (1 : A))) = r ⊗ₜ[A] (i : M₀) := by
        simp [φ]
      rw [hcomp]
      have h2 := hr (1 ⊗ₜ[A] (i : M₀))
      have h3 : r ⊗ₜ[A] (i : M₀) = 0 := by
        simpa [TensorProduct.smul_tmul', mul_one] using h2
      rw [h3, map_zero]
    obtain ⟨z, hz⟩ := (hflat (r ⊗ₜ[A] (1 : A))).mp hzero
    have hrid := congrArg (Algebra.TensorProduct.rid A R R) hz
    have hlhs : Algebra.TensorProduct.rid A R R (r ⊗ₜ[A] (1 : A)) = r := by simp
    rw [hlhs] at hrid
    rw [← hrid]
    clear hz hzero hrid hr
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z₁ z₂ hz₁ hz₂ =>
      rw [map_add, map_add]
      exact Ideal.add_mem _ hz₁ hz₂
    | tmul r' a =>
      have hval : Algebra.TensorProduct.rid A R R
          ((LinearMap.lTensor R (Module.annihilator A M₀).subtype) (r' ⊗ₜ[A] a)) =
          r' * algebraMap A R a.1 := by
        simp [Algebra.smul_def, mul_comm]
      rw [hval]
      exact Ideal.mul_mem_left _ r' (Ideal.mem_map_of_mem _ a.2)
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, Module.mem_annihilator]
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact smul_zero _
    | add x₁ x₂ hx₁ hx₂ => rw [smul_add, hx₁, hx₂, add_zero]
    | tmul r m =>
      change (algebraMap A R a * r) ⊗ₜ[A] m = 0
      rw [← Algebra.smul_def, TensorProduct.smul_tmul,
        Module.mem_annihilator.mp ha m, TensorProduct.tmul_zero]

private lemma supportDim_le_of_flat_local
    (A : Type) [CommRing A] [IsLocalRing A]
    (R : Type u) [CommRing R] [IsLocalRing R] [Algebra A R]
    [IsLocalHom (algebraMap A R)] [Module.Flat A R]
    (M₀ : Type) [AddCommGroup M₀] [Module A M₀] [Module.Finite A M₀]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (eM : R ⊗[A] M₀ ≃ₗ[R] M) :
    Module.supportDim A M₀ ≤ Module.supportDim R M := by
  by_cases hsub : Subsingleton M₀
  · rw [Module.supportDim_eq_bot_of_subsingleton]
    exact bot_le
  have hnt₀ : Nontrivial M₀ := not_subsingleton_iff_nontrivial.mp hsub
  have hff : Module.FaithfullyFlat A R := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hinj : Function.Injective (TensorProduct.mk A R M₀ 1) :=
    Module.FaithfullyFlat.tensorProduct_mk_injective M₀
  have hntM : Nontrivial M := by
    obtain ⟨x, y, hxy⟩ := exists_pair_ne M₀
    exact ⟨⟨eM (1 ⊗ₜ[A] x), eM (1 ⊗ₜ[A] y), fun h => hxy (hinj (eM.injective h))⟩⟩
  have _ : Nonempty (Module.support A M₀) := (Module.nonempty_support_of_nontrivial (R := A) (M := M₀)).to_subtype
  have _ : Nonempty (Module.support R M) := (Module.nonempty_support_of_nontrivial (R := R) (M := M)).to_subtype
  simp only [Module.supportDim, Order.krullDim_eq_iSup_length]
  apply WithBot.coe_le_coe.mpr
  apply iSup_le
  intro l
  let l' : LTSeries (PrimeSpectrum A) := l.map Subtype.val (fun _ _ h => h)
  obtain ⟨Q, hQp, hQlo⟩ :=
    Ideal.exists_isPrime_liesOver_of_faithfullyFlat (B := R) l'.last.asIdeal
  obtain ⟨L, hLlen, _, hLmap⟩ := Ideal.exists_ltSeries_of_hasGoingDown l' Q
  have hLmem : ∀ k : Fin (L.length + 1), L k ∈ Module.support R M := by
    intro k
    rw [Module.mem_support_iff_of_finite]
    have hannM : Module.annihilator R M = (Module.annihilator A M₀).map (algebraMap A R) := by
      rw [← annihilator_baseChange A R M₀]
      ext r
      simp only [Module.mem_annihilator]
      constructor
      · intro h x; apply eM.injective; rw [map_smul, map_zero]; exact h (eM x)
      · intro h y; obtain ⟨x, rfl⟩ := eM.surjective y; rw [← map_smul, h x, map_zero]
    rw [hannM, Ideal.map_le_iff_le_comap]
    have hl'len : l'.length = l.length := rfl
    have hk_lt : k.1 < l'.length + 1 := by omega
    have hk_l : k.1 < l.length + 1 := by omega
    have hidx : k.1 < L.toList.length := by rw [RelSeries.length_toList]; exact k.2
    have hidx' : k.1 < l'.toList.length := by rw [RelSeries.length_toList]; exact hk_lt
    have hcomap : PrimeSpectrum.comap (algebraMap A R) (L k) = l' ⟨k.1, hk_lt⟩ := by
      have h1 : (List.map (PrimeSpectrum.comap (algebraMap A R)) L.toList)[k.1]'(by simpa using hidx) =
          l'.toList[k.1]'hidx' := by simp [hLmap]
      rw [List.getElem_map] at h1
      simpa [RelSeries.toList_getElem] using h1
    have hsupp := (l ⟨k.1, hk_l⟩).2
    rw [Module.mem_support_iff_of_finite] at hsupp
    have heq : (L k).asIdeal.comap (algebraMap A R) = (l ⟨k.1, hk_l⟩).1.asIdeal :=
      congrArg PrimeSpectrum.asIdeal hcomap
    rw [heq]
    exact hsupp
  let L' : LTSeries (Module.support R M) := {
    length := L.length
    toFun := fun k => ⟨L k, hLmem k⟩
    step := fun i => L.step i
  }
  have hlen : L'.length = l.length := hLlen
  calc (l.length : ℕ∞) = (L'.length : ℕ∞) := by rw [hlen]
    _ ≤ ⨆ p : LTSeries (Module.support R M), (p.length : ℕ∞) :=
        le_iSup (fun p : LTSeries (Module.support R M) => (p.length : ℕ∞)) L'

/- Section 2: Countable faithfully flat regular local descent (`Type u` → `Type 0`) -/

private lemma exists_ltSeries_of_krullDim_eq_nat
    {α : Type*} [Preorder α] {n : ℕ} (h : Order.krullDim α = (n : WithBot ℕ∞)) :
    ∃ l : LTSeries α, l.length = n := by
  have hne : Nonempty α := by
    by_contra hmt
    rw [not_nonempty_iff] at hmt
    rw [Order.krullDim_eq_bot] at h
    exact WithBot.bot_ne_coe h
  rw [Order.krullDim_eq_iSup_length] at h
  have h' : (⨆ l : LTSeries α, (l.length : ℕ∞)) = (n : ℕ∞) := WithBot.coe_injective h
  by_contra hno
  have hle : ∀ l : LTSeries α, l.length < n := by
    intro l
    have h1 : (l.length : ℕ∞) ≤ (n : ℕ∞) := h' ▸ le_iSup (fun p : LTSeries α => (p.length : ℕ∞)) l
    have h2 : l.length ≤ n := Nat.cast_le.mp h1
    exact lt_of_le_of_ne h2 (fun heq => hno ⟨l, heq⟩)
  cases n with
  | zero =>
    obtain ⟨a⟩ := hne
    exact Nat.not_lt_zero _ (hle (RelSeries.singleton _ a))
  | succ m =>
    have hsup : (⨆ l : LTSeries α, (l.length : ℕ∞)) ≤ (m : ℕ∞) := by
      apply iSup_le
      intro l
      exact Nat.cast_le.mpr (Nat.lt_succ_iff.mp (hle l))
    rw [h'] at hsup
    have : m + 1 ≤ m := Nat.cast_le.mp hsup
    omega

private lemma countable_subring_closure {R : Type u} [CommRing R] {s : Set R} (hs : s.Countable) :
    (Subring.closure s : Set R).Countable := by
  let step : Set R → Set R := fun t =>
    t ∪ ((fun p : R × R => p.1 + p.2) '' (t ×ˢ t)) ∪
      ((fun p : R × R => p.1 * p.2) '' (t ×ˢ t)) ∪
      ((fun x : R => -x) '' t)
  let L : ℕ → Set R := Nat.rec (s ∪ {0, 1}) (fun _ t => step t)
  have hL_count : ∀ n, (L n).Countable := by
    intro n
    induction n with
    | zero => exact hs.union ((Set.countable_singleton 0).union (Set.countable_singleton 1))
    | succ n ih =>
      exact ((ih.union ((ih.prod ih).image _)).union ((ih.prod ih).image _)).union (ih.image _)
  have hL_step : ∀ n, L n ⊆ L (n + 1) := fun n x hx => Or.inl (Or.inl (Or.inl hx))
  have hL_mono : Monotone L := monotone_nat_of_le_succ hL_step
  let U : Set R := ⋃ n : ℕ, L n
  let B : Subring R := {
    carrier := U
    zero_mem' := Set.mem_iUnion.mpr ⟨0, Or.inr (Or.inl rfl)⟩
    one_mem' := Set.mem_iUnion.mpr ⟨0, Or.inr (Or.inr rfl)⟩
    add_mem' := fun {a b} ha hb => by
      obtain ⟨m, hm⟩ := Set.mem_iUnion.mp ha
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hb
      refine Set.mem_iUnion.mpr ⟨max m n + 1, Or.inl (Or.inl (Or.inr ?_))⟩
      exact ⟨(a, b), ⟨hL_mono (le_max_left m n) hm, hL_mono (le_max_right m n) hn⟩, rfl⟩
    mul_mem' := fun {a b} ha hb => by
      obtain ⟨m, hm⟩ := Set.mem_iUnion.mp ha
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hb
      refine Set.mem_iUnion.mpr ⟨max m n + 1, Or.inl (Or.inr ?_)⟩
      exact ⟨(a, b), ⟨hL_mono (le_max_left m n) hm, hL_mono (le_max_right m n) hn⟩, rfl⟩
    neg_mem' := fun {a} ha => by
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp ha
      exact Set.mem_iUnion.mpr ⟨n + 1, Or.inr ⟨a, hn, rfl⟩⟩
  }
  have hsub : (Subring.closure s : Set R) ⊆ U := by
    change Subring.closure s ≤ B
    rw [Subring.closure_le]
    intro x hx
    exact Set.mem_iUnion.mpr ⟨0, Or.inl hx⟩
  exact (Set.countable_iUnion hL_count).mono hsub

private lemma baseChange_quotient_span_equiv
    (A : Type) [CommRing A] (R : Type u) [CommRing R] [Algebra A R]
    (a b : ℕ) (rows₀ : Fin b → (Fin a → A)) :
    Nonempty
      ((R ⊗[A] ((Fin a → A) ⧸ Submodule.span A (Set.range rows₀))) ≃ₗ[R]
        ((Fin a → R) ⧸ Submodule.span R
          (Set.range (fun i : Fin b => fun j : Fin a => algebraMap A R (rows₀ i j))))) := by
  let K₀ : Submodule A (Fin a → A) := Submodule.span A (Set.range rows₀)
  let rowsR : Fin b → (Fin a → R) := fun i j => algebraMap A R (rows₀ i j)
  let KR : Submodule R (Fin a → R) := Submodule.span R (Set.range rowsR)
  let eFin : R ⊗[A] (Fin a → A) ≃ₗ[R] (Fin a → R) :=
    TensorProduct.piScalarRight A R R (Fin a)
  have heFin_tmul : ∀ (r : R) (v : Fin a → A) (j : Fin a),
      eFin (r ⊗ₜ[A] v) j = r * algebraMap A R (v j) := by
    intro r v j
    simp [eFin, Algebra.smul_def, mul_comm]
  let fwdBilin : R →ₗ[R] ((Fin a → A) ⧸ K₀) →ₗ[A] ((Fin a → R) ⧸ KR) := {
    toFun := fun r =>
      K₀.liftQ
        { toFun := fun v => Submodule.Quotient.mk (fun j => r * algebraMap A R (v j))
          map_add' := fun v w => by
            rw [← Submodule.Quotient.mk_add]
            congr 1; ext j; simp [mul_add]
          map_smul' := fun c v => by
            simp only [RingHom.id_apply]
            conv_rhs => rw [← algebraMap_smul R c, ← Submodule.Quotient.mk_smul]
            congr 1; ext j
            simp only [Pi.smul_apply, smul_eq_mul, map_mul]
            ring }
        (by
          intro v hv
          rw [LinearMap.mem_ker]
          change Submodule.Quotient.mk (fun j => r * algebraMap A R (v j)) = 0
          rw [Submodule.Quotient.mk_eq_zero]
          refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
          · rintro _ ⟨i, rfl⟩
            have h1 : (fun j => r * algebraMap A R (rows₀ i j)) = r • rowsR i := by
              ext j; rfl
            rw [h1]
            exact Submodule.smul_mem KR r (Submodule.subset_span ⟨i, rfl⟩)
          · have h0 : (fun j : Fin a => r * algebraMap A R ((0 : Fin a → A) j)) = 0 := by
              ext j; simp
            rw [h0]; exact KR.zero_mem
          · intro x y _ _ hx hy
            have hadd : (fun j => r * algebraMap A R ((x + y) j)) =
                (fun j => r * algebraMap A R (x j)) + (fun j => r * algebraMap A R (y j)) := by
              ext j; simp [mul_add]
            rw [hadd]; exact KR.add_mem hx hy
          · intro c x _ hx
            have hsm : (fun j => r * algebraMap A R ((c • x) j)) =
                (algebraMap A R c) • (fun j => r * algebraMap A R (x j)) := by
              ext j; simp only [Pi.smul_apply, smul_eq_mul, map_mul]; ring
            rw [hsm]; exact KR.smul_mem _ hx)
    map_add' := fun r₁ r₂ => by
      apply LinearMap.ext
      intro v
      induction v using Submodule.Quotient.induction_on with
      | _ v =>
        change Submodule.Quotient.mk (p := KR) (fun j => (r₁ + r₂) * algebraMap A R (v j)) =
          Submodule.Quotient.mk (p := KR) (fun j => r₁ * algebraMap A R (v j)) +
            Submodule.Quotient.mk (p := KR) (fun j => r₂ * algebraMap A R (v j))
        rw [← Submodule.Quotient.mk_add]
        congr 1; ext j; simp only [Pi.add_apply]; ring
    map_smul' := fun r₁ r₂ => by
      apply LinearMap.ext
      intro v
      induction v using Submodule.Quotient.induction_on with
      | _ v =>
        simp only [RingHom.id_apply, smul_eq_mul]
        change Submodule.Quotient.mk (p := KR) (fun j => (r₁ * r₂) * algebraMap A R (v j)) =
          r₁ • Submodule.Quotient.mk (p := KR) (fun j => r₂ * algebraMap A R (v j))
        rw [← Submodule.Quotient.mk_smul]
        congr 1; ext j; simp [mul_assoc]
  }
  let fwd : R ⊗[A] ((Fin a → A) ⧸ K₀) →ₗ[R] ((Fin a → R) ⧸ KR) :=
    AlgebraTensorModule.lift fwdBilin
  let bwd0 : (Fin a → R) →ₗ[R] R ⊗[A] ((Fin a → A) ⧸ K₀) :=
    (LinearMap.baseChange R K₀.mkQ).comp eFin.symm.toLinearMap
  have hbwd_ker : KR ≤ LinearMap.ker bwd0 := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    have hpre : eFin (1 ⊗ₜ[A] rows₀ i) = rowsR i := by
      ext j; rw [heFin_tmul, one_mul]
    rw [← hpre]
    change (LinearMap.baseChange R K₀.mkQ) (eFin.symm (eFin (1 ⊗ₜ[A] rows₀ i))) = 0
    rw [LinearEquiv.symm_apply_apply, LinearMap.baseChange_tmul]
    have hzero : K₀.mkQ (rows₀ i) = 0 :=
      (Submodule.Quotient.mk_eq_zero K₀).mpr (Submodule.subset_span ⟨i, rfl⟩)
    rw [hzero, TensorProduct.tmul_zero]
  let bwd : ((Fin a → R) ⧸ KR) →ₗ[R] R ⊗[A] ((Fin a → A) ⧸ K₀) := KR.liftQ bwd0 hbwd_ker
  have hleft : ∀ x, bwd (fwd x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x₁ x₂ hx₁ hx₂ => rw [map_add, map_add, hx₁, hx₂]
    | tmul r u =>
      induction u using Submodule.Quotient.induction_on with
      | _ v =>
        change bwd0 (fun j => r * algebraMap A R (v j)) = r ⊗ₜ[A] Submodule.Quotient.mk v
        have hpre : eFin (r ⊗ₜ[A] v) = fun j => r * algebraMap A R (v j) := by
          ext j; exact heFin_tmul r v j
        rw [← hpre]
        change (LinearMap.baseChange R K₀.mkQ) (eFin.symm (eFin (r ⊗ₜ[A] v))) = _
        rw [LinearEquiv.symm_apply_apply, LinearMap.baseChange_tmul]
        rfl
  have hright : ∀ y, fwd (bwd y) = y := by
    intro y
    induction y using Submodule.Quotient.induction_on with
    | _ w =>
      have hw : w = eFin (eFin.symm w) := (eFin.apply_symm_apply w).symm
      rw [hw]
      generalize eFin.symm w = z
      induction z using TensorProduct.induction_on with
      | zero => simp [bwd, bwd0]
      | add z₁ z₂ hz₁ hz₂ =>
        rw [map_add, Submodule.Quotient.mk_add, map_add, map_add, hz₁, hz₂]
      | tmul r v =>
        change fwd (bwd0 (eFin (r ⊗ₜ[A] v))) = Submodule.Quotient.mk (eFin (r ⊗ₜ[A] v))
        change fwd ((LinearMap.baseChange R K₀.mkQ) (eFin.symm (eFin (r ⊗ₜ[A] v)))) = _
        rw [LinearEquiv.symm_apply_apply, LinearMap.baseChange_tmul]
        have h1 : fwd (r ⊗ₜ[A] K₀.mkQ v) =
            Submodule.Quotient.mk (fun j => r * algebraMap A R (v j)) := rfl
        rw [h1]
        congr 1; ext j; exact (heFin_tmul r v j).symm
  exact ⟨LinearEquiv.ofLinearMap fwd bwd (LinearMap.ext hright) (LinearMap.ext hleft)⟩

private lemma exists_countable_flat_subring
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (S₀ : Set R) (hS₀_count : S₀.Countable) :
    ∃ (R₀ : Subring R), Countable R₀ ∧ S₀ ⊆ (R₀ : Set R) ∧
      IsLocalHom (algebraMap R₀ R) ∧ IsLocalRing R₀ ∧
      Module.Flat R₀ R ∧ IsNoetherianRing R₀ := by
  classical
  let syzGen : ∀ (n : ℕ) (f : Fin n → R), Finset (Fin n → R) := fun n f =>
    let φ : (Fin n → R) →ₗ[R] R := {
      toFun := fun v => ∑ i : Fin n, f i * v i
      map_add' := fun v w => by simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun r v => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => by ring
    }
    (IsNoetherian.noetherian (LinearMap.ker φ)).choose
  have hsyzGen : ∀ (n : ℕ) (f : Fin n → R),
      Submodule.span R (syzGen n f : Set (Fin n → R)) =
      LinearMap.ker ({
        toFun := fun v : Fin n → R => ∑ i : Fin n, f i * v i
        map_add' := fun v w => by simp [mul_add, Finset.sum_add_distrib]
        map_smul' := fun r v => by
          simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => by ring
      } : (Fin n → R) →ₗ[R] R) := fun n f =>
    (IsNoetherian.noetherian _).choose_spec
  let stepSet : Subring R → Set R := fun B =>
    (B : Set R) ∪
    Set.range (fun u : { b : B // IsUnit (b : R) } => ((u.2.unit⁻¹ : Rˣ) : R)) ∪
    ⋃ (q : Σ n : ℕ, Fin n → B), ⋃ (v : syzGen q.1 (fun i => (q.2 i : R))),
      Set.range (v.1 : Fin q.1 → R)
  have hstep_count : ∀ B : Subring R, (B : Set R).Countable → (stepSet B).Countable := by
    intro B hB
    have _ : Countable B := hB.to_subtype
    have h1 : (Set.range (fun u : { b : B // IsUnit (b : R) } => ((u.2.unit⁻¹ : Rˣ) : R))).Countable :=
      Set.countable_range _
    have h2 : (⋃ (q : Σ n : ℕ, Fin n → B), ⋃ (v : syzGen q.1 (fun i => (q.2 i : R))),
        Set.range (v.1 : Fin q.1 → R)).Countable := by
      refine Set.countable_iUnion fun q => ?_
      refine Set.countable_iUnion fun v => ?_
      exact Set.countable_range _
    exact (hB.union h1).union h2
  let T : ℕ → Subring R := Nat.rec (Subring.closure S₀) (fun _ B => Subring.closure (stepSet B))
  have hT_count : ∀ k, (SetLike.coe (T k)).Countable := by
    intro k
    induction k with
    | zero => exact countable_subring_closure hS₀_count
    | succ k ih => exact countable_subring_closure (hstep_count (T k) ih)
  have hT_step : ∀ k, T k ≤ T (k + 1) := by
    intro k x hx
    exact Subring.subset_closure (Or.inl (Or.inl (show x ∈ SetLike.coe (T k) from hx)))
  have hT_mono : Monotone T := monotone_nat_of_le_succ hT_step
  let R₀ : Subring R := ⨆ k : ℕ, T k
  have hR₀_mem : ∀ x : R, x ∈ R₀ ↔ ∃ k : ℕ, x ∈ T k := fun x =>
    Subring.mem_iSup_of_directed hT_mono.directed_le
  have hR₀_count : (R₀ : Set R).Countable := by
    have heq : (R₀ : Set R) = ⋃ k : ℕ, SetLike.coe (T k) := by
      ext x; simp only [SetLike.mem_coe, Set.mem_iUnion, hR₀_mem]
    rw [heq]
    exact Set.countable_iUnion hT_count
  have hcnt : Countable R₀ := hR₀_count.to_subtype
  have hS₀_sub : S₀ ⊆ (R₀ : Set R) := fun x hx =>
    (hR₀_mem x).mpr ⟨0, Subring.subset_closure hx⟩
  have hlocalHom₀ : IsLocalHom (algebraMap R₀ R) := by
    constructor
    intro b hb
    obtain ⟨k, hk⟩ := (hR₀_mem b.1).mp b.2
    have hinv_mem : ((hb.unit⁻¹ : Rˣ) : R) ∈ T (k + 1) :=
      Subring.subset_closure (Or.inl (Or.inr ⟨⟨⟨b.1, hk⟩, hb⟩, rfl⟩))
    have hinvR₀ : ((hb.unit⁻¹ : Rˣ) : R) ∈ R₀ := (hR₀_mem _).mpr ⟨k + 1, hinv_mem⟩
    refine isUnit_iff_exists_inv.mpr ⟨⟨((hb.unit⁻¹ : Rˣ) : R), hinvR₀⟩, ?_⟩
    ext
    exact hb.unit.mul_inv
  have hloc₀ : IsLocalRing R₀ := (algebraMap R₀ R).domain_isLocalRing
  have hflat₀ : Module.Flat R₀ R := by
    apply Module.Flat.of_forall_isTrivialRelation
    intro l f x hrel
    have hex_k : ∃ k : ℕ, ∀ i : Fin l, (f i : R) ∈ T k := by
      have : ∀ i : Fin l, ∃ k : ℕ, (f i : R) ∈ T k := fun i => (hR₀_mem _).mp (f i).2
      choose fk hfk using this
      refine ⟨Finset.univ.sup fk, fun i => hT_mono (Finset.le_sup (Finset.mem_univ i)) (hfk i)⟩
    obtain ⟨k, hk⟩ := hex_k
    let f_k : Fin l → T k := fun i => ⟨(f i : R), hk i⟩
    let G := syzGen l (fun i => (f_k i : R))
    have hx_mem : x ∈ Submodule.span R (G : Set (Fin l → R)) := by
      rw [hsyzGen l (fun i => (f_k i : R)), LinearMap.mem_ker]
      exact hrel
    rw [Finsupp.mem_span_iff_linearCombination] at hx_mem
    obtain ⟨c, hc⟩ := hx_mem
    let m : ℕ := G.card
    let eG : Fin m ≃ G := (Fintype.equivFinOfCardEq (Fintype.card_coe G)).symm
    have hmem_coord : ∀ (j : Fin m) (i : Fin l), (eG j).1 i ∈ R₀ := fun j i => by
      have h1 : (eG j).1 i ∈ T (k + 1) := by
        apply Subring.subset_closure
        right
        refine Set.mem_iUnion.mpr ⟨⟨l, f_k⟩, ?_⟩
        refine Set.mem_iUnion.mpr ⟨eG j, ?_⟩
        exact ⟨i, rfl⟩
      exact (hR₀_mem _).mpr ⟨k + 1, h1⟩
    refine ⟨m, fun i j => ⟨(eG j).1 i, hmem_coord j i⟩, fun j => c (eG j), ?_, ?_⟩
    · intro i
      have hci := congrFun hc.symm i
      rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype] at hci
      · rw [hci]
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        calc ∑ g : G, c g * g.1 i
            = ∑ j : Fin m, c (eG j) * (eG j).1 i := (Equiv.sum_comp eG (fun g : G => c g * g.1 i)).symm
          _ = ∑ j : Fin m, (⟨(eG j).1 i, hmem_coord j i⟩ : R₀) • c (eG j) := by
              refine Finset.sum_congr rfl fun j _ => ?_
              change c (eG j) * (eG j).1 i = (eG j).1 i * c (eG j)
              ring
      · intro _; exact zero_smul R _
    · intro j
      apply Subtype.ext
      have hkerj : (eG j).1 ∈ Submodule.span R (G : Set (Fin l → R)) :=
        Submodule.subset_span (eG j).2
      rw [hsyzGen l (fun i => (f_k i : R)), LinearMap.mem_ker] at hkerj
      simpa [f_k] using hkerj
  have hff₀ : Module.FaithfullyFlat R₀ R := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hnoeth₀ : IsNoetherianRing R₀ := by
    rw [IsNoetherianRing, ← monotone_stabilizes_iff_noetherian]
    intro f
    let g : ℕ →o Submodule R R := {
      toFun := fun n => Ideal.map (algebraMap R₀ R) (f n)
      monotone' := fun _ _ h => Ideal.map_mono (f.monotone h)
    }
    obtain ⟨N, hN⟩ := monotone_stabilizes_iff_noetherian.mpr (inferInstance : IsNoetherian R R) g
    refine ⟨N, fun n hn => ?_⟩
    exact Ideal.map_injective_of_faithfullyFlat (A := R₀) (B := R) (hN n hn)
  exact ⟨R₀, hcnt, hS₀_sub, hlocalHom₀, hloc₀, hflat₀, hnoeth₀⟩

private lemma descent_via_opaque_ring
    (A : Type) [CommRing A] [IsRegularLocalRing A]
    (R : Type u) [CommRing R] [IsRegularLocalRing R] [Algebra A R]
    [IsLocalHom (algebraMap A R)] [Module.Flat A R]
    (hmax_mapA : (maximalIdeal A).map (algebraMap A R) = maximalIdeal R)
    (hdimA_eq : ringKrullDim A = ringKrullDim R)
    (M N : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] [Module.Finite R N]
    (p : ℕ) [CharP (ResidueField R) p] (hp : (p : R) ∉ maximalIdeal R ^ 2)
    (hfin : IsFiniteLength R (M ⊗[R] N))
    (hdim : Module.supportDim R M + Module.supportDim R N = ringKrullDim R)
    (aM bM aN bN dM dN : ℕ)
    (rowsM₀ : Fin bM → (Fin aM → A)) (rowsN₀ : Fin bN → (Fin aN → A))
    (eM_pres : ((Fin aM → R) ⧸ Submodule.span R
      (Set.range (fun i : Fin bM => fun j : Fin aM => algebraMap A R (rowsM₀ i j)))) ≃ₗ[R] M)
    (eN_pres : ((Fin aN → R) ⧸ Submodule.span R
      (Set.range (fun i : Fin bN => fun j : Fin aN => algebraMap A R (rowsN₀ i j)))) ≃ₗ[R] N)
    (hdimM : Module.supportDim R M = (dM : WithBot ℕ∞))
    (hdimN : Module.supportDim R N = (dN : WithBot ℕ∞))
    (cM : LTSeries (Module.support R M)) (hcM_len : cM.length = dM)
    (cN : LTSeries (Module.support R N)) (hcN_len : cN.length = dN)
    (wM₀ : Fin dM → A)
    (hwM_mem : ∀ i : Fin dM, algebraMap A R (wM₀ i) ∈ (cM ⟨i.1 + 1, by omega⟩).1.asIdeal)
    (hwM_nmem : ∀ i : Fin dM, algebraMap A R (wM₀ i) ∉ (cM ⟨i.1, by omega⟩).1.asIdeal)
    (wN₀ : Fin dN → A)
    (hwN_mem : ∀ i : Fin dN, algebraMap A R (wN₀ i) ∈ (cN ⟨i.1 + 1, by omega⟩).1.asIdeal)
    (hwN_nmem : ∀ i : Fin dN, algebraMap A R (wN₀ i) ∉ (cN ⟨i.1, by omega⟩).1.asIdeal) :
    ∃ (M₀ N₀ : Type) (_ : AddCommGroup M₀) (_ : Module A M₀) (_ : Module.Finite A M₀)
      (_ : AddCommGroup N₀) (_ : Module A N₀) (_ : Module.Finite A N₀),
      CharP (ResidueField A) p ∧
      (p : A) ∉ maximalIdeal A ^ 2 ∧
      IsFiniteLength A (M₀ ⊗[A] N₀) ∧
      Module.supportDim A M₀ + Module.supportDim A N₀ = ringKrullDim A ∧
      Module.intersectionMultiplicity R M N = Module.intersectionMultiplicity A M₀ N₀ := by
  have hcharA : CharP (ResidueField A) p :=
    (RingHom.charP_iff_charP (IsLocalRing.ResidueField.map (algebraMap A R)) p).mpr inferInstance
  have hpA : (p : A) ∉ maximalIdeal A ^ 2 := by
    intro hmem
    apply hp
    have h1 : algebraMap A R (p : A) ∈ (maximalIdeal A ^ 2).map (algebraMap A R) :=
      Ideal.mem_map_of_mem _ hmem
    rw [map_natCast, Ideal.map_pow, hmax_mapA] at h1
    exact h1
  let M₀ : Type := (Fin aM → A) ⧸ Submodule.span A (Set.range rowsM₀)
  let N₀ : Type := (Fin aN → A) ⧸ Submodule.span A (Set.range rowsN₀)
  obtain ⟨eM₀⟩ := baseChange_quotient_span_equiv A R aM bM rowsM₀
  obtain ⟨eN₀⟩ := baseChange_quotient_span_equiv A R aN bN rowsN₀
  let eM : R ⊗[A] M₀ ≃ₗ[R] M := eM₀.trans eM_pres
  let eN : R ⊗[A] N₀ ≃ₗ[R] N := eN₀.trans eN_pres
  have hdimM₀_ge : (dM : WithBot ℕ∞) ≤ Module.supportDim A M₀ := by
    have hannM : Module.annihilator R M = (Module.annihilator A M₀).map (algebraMap A R) := by
      rw [← annihilator_baseChange A R M₀]
      ext r
      simp only [Module.mem_annihilator]
      constructor
      · intro h x; apply eM.injective; rw [map_smul, map_zero]; exact h (eM x)
      · intro h y; obtain ⟨x, rfl⟩ := eM.surjective y; rw [← map_smul, h x, map_zero]
    have hmem : ∀ i : Fin (dM + 1),
        PrimeSpectrum.comap (algebraMap A R) (cM ⟨i.1, by omega⟩).1 ∈ Module.support A M₀ := by
      intro i
      rw [Module.mem_support_iff_of_finite]
      have hsup := (cM ⟨i.1, by omega⟩).2
      rw [Module.mem_support_iff_of_finite, hannM, Ideal.map_le_iff_le_comap] at hsup
      exact hsup
    let cM₀ : LTSeries (Module.support A M₀) := {
      length := dM
      toFun := fun i => ⟨PrimeSpectrum.comap (algebraMap A R) (cM ⟨i.1, by omega⟩).1, hmem i⟩
      step := fun i => by
        change (cM ⟨i.1, by omega⟩).1.asIdeal.comap (algebraMap A R) <
          (cM ⟨i.1 + 1, by omega⟩).1.asIdeal.comap (algebraMap A R)
        refine lt_of_le_of_ne (Ideal.comap_mono (cM.monotone (by
          show (⟨i.1, _⟩ : Fin (cM.length + 1)) ≤ ⟨i.1 + 1, _⟩; exact Nat.le_succ _))) ?_
        intro heq
        have h1 : wM₀ i ∈ (cM ⟨i.1 + 1, by omega⟩).1.asIdeal.comap (algebraMap A R) :=
          hwM_mem i
        rw [← heq] at h1
        exact hwM_nmem i h1
    }
    have _ : Nonempty (Module.support A M₀) := ⟨cM₀ 0⟩
    rw [Module.supportDim, Order.krullDim_eq_iSup_length]
    exact WithBot.coe_le_coe.mpr (le_iSup (fun l : LTSeries (Module.support A M₀) => (l.length : ℕ∞)) cM₀)
  have hdimN₀_ge : (dN : WithBot ℕ∞) ≤ Module.supportDim A N₀ := by
    have hannN : Module.annihilator R N = (Module.annihilator A N₀).map (algebraMap A R) := by
      rw [← annihilator_baseChange A R N₀]
      ext r
      simp only [Module.mem_annihilator]
      constructor
      · intro h x; apply eN.injective; rw [map_smul, map_zero]; exact h (eN x)
      · intro h y; obtain ⟨x, rfl⟩ := eN.surjective y; rw [← map_smul, h x, map_zero]
    have hmem : ∀ i : Fin (dN + 1),
        PrimeSpectrum.comap (algebraMap A R) (cN ⟨i.1, by omega⟩).1 ∈ Module.support A N₀ := by
      intro i
      rw [Module.mem_support_iff_of_finite]
      have hsup := (cN ⟨i.1, by omega⟩).2
      rw [Module.mem_support_iff_of_finite, hannN, Ideal.map_le_iff_le_comap] at hsup
      exact hsup
    let cN₀ : LTSeries (Module.support A N₀) := {
      length := dN
      toFun := fun i => ⟨PrimeSpectrum.comap (algebraMap A R) (cN ⟨i.1, by omega⟩).1, hmem i⟩
      step := fun i => by
        change (cN ⟨i.1, by omega⟩).1.asIdeal.comap (algebraMap A R) <
          (cN ⟨i.1 + 1, by omega⟩).1.asIdeal.comap (algebraMap A R)
        refine lt_of_le_of_ne (Ideal.comap_mono (cN.monotone (by
          show (⟨i.1, _⟩ : Fin (cN.length + 1)) ≤ ⟨i.1 + 1, _⟩; exact Nat.le_succ _))) ?_
        intro heq
        have h1 : wN₀ i ∈ (cN ⟨i.1 + 1, by omega⟩).1.asIdeal.comap (algebraMap A R) :=
          hwN_mem i
        rw [← heq] at h1
        exact hwN_nmem i h1
    }
    have _ : Nonempty (Module.support A N₀) := ⟨cN₀ 0⟩
    rw [Module.supportDim, Order.krullDim_eq_iSup_length]
    exact WithBot.coe_le_coe.mpr (le_iSup (fun l : LTSeries (Module.support A N₀) => (l.length : ℕ∞)) cN₀)
  have hdimM₀_eq : Module.supportDim A M₀ = Module.supportDim R M :=
    le_antisymm (supportDim_le_of_flat_local A R M₀ M eM) (hdimM ▸ hdimM₀_ge)
  have hdimN₀_eq : Module.supportDim A N₀ = Module.supportDim R N :=
    le_antisymm (supportDim_le_of_flat_local A R N₀ N eN) (hdimN ▸ hdimN₀_ge)
  have hfinA : IsFiniteLength A (M₀ ⊗[A] N₀) :=
    (flat_baseChange_isFiniteLength_tensor_iff A R hmax_mapA M₀ N₀ M N eM eN).mp hfin
  have hdimA_sum : Module.supportDim A M₀ + Module.supportDim A N₀ = ringKrullDim A := by
    rw [hdimM₀_eq, hdimN₀_eq, hdim, hdimA_eq]
  have hinterA : Module.intersectionMultiplicity R M N = Module.intersectionMultiplicity A M₀ N₀ :=
    flat_baseChange_interMult A R hmax_mapA M₀ N₀ M N eM eN
  exact ⟨M₀, N₀, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, hcharA, hpA, hfinA, hdimA_sum, hinterA⟩

private lemma exists_countable_flat_descent
    (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (M N : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] [Module.Finite R N]
    (p : ℕ) [CharP (ResidueField R) p] (hp : (p : R) ∉ maximalIdeal R ^ 2)
    (hfin : IsFiniteLength R (M ⊗[R] N))
    (hdim : Module.supportDim R M + Module.supportDim R N = ringKrullDim R) :
    ∃ (A : Type) (_ : CommRing A) (_ : IsRegularLocalRing A)
      (M₀ N₀ : Type) (_ : AddCommGroup M₀) (_ : Module A M₀) (_ : Module.Finite A M₀)
      (_ : AddCommGroup N₀) (_ : Module A N₀) (_ : Module.Finite A N₀),
      CharP (ResidueField A) p ∧
      (p : A) ∉ maximalIdeal A ^ 2 ∧
      IsFiniteLength A (M₀ ⊗[A] N₀) ∧
      Module.supportDim A M₀ + Module.supportDim A N₀ = ringKrullDim A ∧
      Module.intersectionMultiplicity R M N = Module.intersectionMultiplicity A M₀ N₀ := by
  classical
  -- Step 1: Collect finite seed S₀ in R
  let d : ℕ := (maximalIdeal R).spanFinrank
  have hdimR : ringKrullDim R = (d : WithBot ℕ∞) :=
    (IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)).symm
  obtain ⟨gMax, hgMax_card, hgMax_span⟩ :=
    (IsNoetherian.noetherian (maximalIdeal R)).exists_span_finset_card_eq_spanFinrank
  obtain ⟨cR, hcR_len⟩ := exists_ltSeries_of_krullDim_eq_nat hdimR
  have hwR_ex : ∀ i : Fin d, ∃ w : R,
      w ∈ (cR ⟨i.1 + 1, by omega⟩).asIdeal ∧ w ∉ (cR ⟨i.1, by omega⟩).asIdeal := fun i => by
    have hlt : (cR ⟨i.1, by omega⟩).asIdeal < (cR ⟨i.1 + 1, by omega⟩).asIdeal :=
      cR.strictMono (by show (⟨i.1, _⟩ : Fin (cR.length + 1)) < ⟨i.1 + 1, _⟩; exact Nat.lt_succ_self _)
    exact SetLike.exists_of_lt hlt
  choose wR hwR_mem hwR_nmem using hwR_ex
  -- Finite presentations of M and N
  obtain ⟨aM, πM, hπM⟩ := Module.Finite.exists_fin' R M
  obtain ⟨sKM, hsKM⟩ := IsNoetherian.noetherian (LinearMap.ker πM)
  let bM : ℕ := sKM.card
  let eKM : Fin bM ≃ sKM := (Fintype.equivFinOfCardEq (Fintype.card_coe sKM)).symm
  let rowsM : Fin bM → (Fin aM → R) := fun i => (eKM i).1
  have hrowsM_span : Submodule.span R (Set.range rowsM) = LinearMap.ker πM := by
    rw [← hsKM]
    congr 1
    ext x
    simp only [Set.mem_range, Finset.mem_coe, rowsM]
    constructor
    · rintro ⟨i, rfl⟩; exact (eKM i).2
    · intro hx; exact ⟨eKM.symm ⟨x, hx⟩, by simp⟩
  let eM_pres : ((Fin aM → R) ⧸ Submodule.span R (Set.range rowsM)) ≃ₗ[R] M :=
    (Submodule.quotEquivOfEq _ _ hrowsM_span).trans (LinearMap.quotKerEquivOfSurjective πM hπM)
  obtain ⟨aN, πN, hπN⟩ := Module.Finite.exists_fin' R N
  obtain ⟨sKN, hsKN⟩ := IsNoetherian.noetherian (LinearMap.ker πN)
  let bN : ℕ := sKN.card
  let eKN : Fin bN ≃ sKN := (Fintype.equivFinOfCardEq (Fintype.card_coe sKN)).symm
  let rowsN : Fin bN → (Fin aN → R) := fun i => (eKN i).1
  have hrowsN_span : Submodule.span R (Set.range rowsN) = LinearMap.ker πN := by
    rw [← hsKN]
    congr 1
    ext x
    simp only [Set.mem_range, Finset.mem_coe, rowsN]
    constructor
    · rintro ⟨i, rfl⟩; exact (eKN i).2
    · intro hx; exact ⟨eKN.symm ⟨x, hx⟩, by simp⟩
  let eN_pres : ((Fin aN → R) ⧸ Submodule.span R (Set.range rowsN)) ≃ₗ[R] N :=
    (Submodule.quotEquivOfEq _ _ hrowsN_span).trans (LinearMap.quotKerEquivOfSurjective πN hπN)
  -- Support dimensions dM, dN and witnessing prime chains
  have hdM_ne_bot : Module.supportDim R M ≠ ⊥ := by
    intro h
    rw [h, WithBot.bot_add, hdimR] at hdim
    exact WithBot.bot_ne_coe hdim
  have hdN_ne_bot : Module.supportDim R N ≠ ⊥ := by
    intro h
    rw [h, WithBot.add_bot, hdimR] at hdim
    exact WithBot.bot_ne_coe hdim
  have hdM_le : Module.supportDim R M ≤ (d : WithBot ℕ∞) := by
    rw [← hdimR]; exact Module.supportDim_le_ringKrullDim R M
  have hdN_le : Module.supportDim R N ≤ (d : WithBot ℕ∞) := by
    rw [← hdimR]; exact Module.supportDim_le_ringKrullDim R N
  obtain ⟨eMdim, heMdim⟩ := WithBot.ne_bot_iff_exists.mp hdM_ne_bot
  obtain ⟨eNdim, heNdim⟩ := WithBot.ne_bot_iff_exists.mp hdN_ne_bot
  have heM_lt_top : eMdim ≠ ⊤ := by
    intro htop
    rw [← heMdim, htop] at hdM_le
    exact ENat.natCast_ne_top d (top_unique (WithBot.coe_le_coe.mp hdM_le))
  have heN_lt_top : eNdim ≠ ⊤ := by
    intro htop
    rw [← heNdim, htop] at hdN_le
    exact ENat.natCast_ne_top d (top_unique (WithBot.coe_le_coe.mp hdN_le))
  obtain ⟨dM, hdM_eq⟩ := Option.ne_none_iff_exists'.mp heM_lt_top
  obtain ⟨dN, hdN_eq⟩ := Option.ne_none_iff_exists'.mp heN_lt_top
  have hdimM : Module.supportDim R M = (dM : WithBot ℕ∞) := by
    rw [← heMdim]; exact congrArg WithBot.some hdM_eq
  have hdimN : Module.supportDim R N = (dN : WithBot ℕ∞) := by
    rw [← heNdim]; exact congrArg WithBot.some hdN_eq
  obtain ⟨cM, hcM_len⟩ := exists_ltSeries_of_krullDim_eq_nat hdimM
  obtain ⟨cN, hcN_len⟩ := exists_ltSeries_of_krullDim_eq_nat hdimN
  have hwM_ex : ∀ i : Fin dM, ∃ w : R,
      w ∈ (cM ⟨i.1 + 1, by omega⟩).1.asIdeal ∧ w ∉ (cM ⟨i.1, by omega⟩).1.asIdeal := fun i => by
    have hlt : (cM ⟨i.1, by omega⟩).1.asIdeal < (cM ⟨i.1 + 1, by omega⟩).1.asIdeal :=
      cM.strictMono (by show (⟨i.1, _⟩ : Fin (cM.length + 1)) < ⟨i.1 + 1, _⟩; exact Nat.lt_succ_self _)
    exact SetLike.exists_of_lt hlt
  choose wM hwM_mem hwM_nmem using hwM_ex
  have hwN_ex : ∀ i : Fin dN, ∃ w : R,
      w ∈ (cN ⟨i.1 + 1, by omega⟩).1.asIdeal ∧ w ∉ (cN ⟨i.1, by omega⟩).1.asIdeal := fun i => by
    have hlt : (cN ⟨i.1, by omega⟩).1.asIdeal < (cN ⟨i.1 + 1, by omega⟩).1.asIdeal :=
      cN.strictMono (by show (⟨i.1, _⟩ : Fin (cN.length + 1)) < ⟨i.1 + 1, _⟩; exact Nat.lt_succ_self _)
    exact SetLike.exists_of_lt hlt
  choose wN hwN_mem hwN_nmem using hwN_ex
  -- Finite seed S₀
  let S₀ : Set R :=
    (gMax : Set R) ∪ Set.range wR ∪ Set.range wM ∪ Set.range wN ∪
    Set.range (fun p : Fin bM × Fin aM => rowsM p.1 p.2) ∪
    Set.range (fun p : Fin bN × Fin aN => rowsN p.1 p.2)
  have hS₀_count : S₀.Countable :=
    (((((gMax.countable_toSet.union (Set.countable_range wR)).union
      (Set.countable_range wM)).union (Set.countable_range wN)).union
      (Set.countable_range _)).union (Set.countable_range _))
  -- Step 2: Obtain opaque countable flat local Noetherian subring R₀
  obtain ⟨R₀, _, hS₀_sub, hlocalHom₀, _, hflat₀, hnoeth₀⟩ :=
    exists_countable_flat_subring R S₀ hS₀_count
  have hff₀ : Module.FaithfullyFlat R₀ R := Module.FaithfullyFlat.of_flat_of_isLocalHom
  -- Step 3: Maximal ideal and regular local ring properties of R₀
  have hgMax_in_R₀ : ∀ x ∈ gMax, x ∈ R₀ := fun x hx =>
    hS₀_sub (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hx)))))
  let gMax₀ : Finset R₀ := gMax.attach.image (fun x => ⟨x.1, hgMax_in_R₀ x.1 x.2⟩)
  have hgMax₀_card : gMax₀.card ≤ d := by
    change gMax₀.card ≤ (maximalIdeal R).spanFinrank
    rw [← hgMax_card]
    exact Finset.card_image_le.trans (by simp)
  have hgMax₀_sub : (gMax₀ : Set R₀) ⊆ (maximalIdeal R₀ : Set R₀) := by
    intro x hx
    rw [Finset.mem_coe, Finset.mem_image] at hx
    obtain ⟨⟨y, hy⟩, _, rfl⟩ := hx
    have hym : y ∈ maximalIdeal R := by rw [← hgMax_span]; exact Ideal.subset_span hy
    show (⟨y, hgMax_in_R₀ y hy⟩ : R₀) ∈ maximalIdeal R₀
    rw [← IsLocalRing.maximalIdeal_comap (algebraMap R₀ R)]
    exact hym
  have hmax_map : (maximalIdeal R₀).map (algebraMap R₀ R) = maximalIdeal R := by
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      exact le_of_eq (IsLocalRing.maximalIdeal_comap (algebraMap R₀ R)).symm
    · rw [← hgMax_span, Ideal.span_le]
      intro y hy
      have hy0 : (⟨y, hgMax_in_R₀ y hy⟩ : R₀) ∈ maximalIdeal R₀ :=
        hgMax₀_sub (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨⟨y, hy⟩, Finset.mem_attach _ _, rfl⟩))
      exact Ideal.mem_map_of_mem (algebraMap R₀ R) hy0
  have hmax₀_span : Ideal.span (gMax₀ : Set R₀) = maximalIdeal R₀ := by
    apply Ideal.map_injective_of_faithfullyFlat (A := R₀) (B := R)
    rw [hmax_map, Ideal.map_span, ← hgMax_span]
    congr 1
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [Finset.mem_coe, Finset.mem_image] at hx
      obtain ⟨⟨z, hz⟩, _, rfl⟩ := hx
      exact hz
    · intro hy
      exact ⟨⟨y, hgMax_in_R₀ y hy⟩,
        Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨⟨y, hy⟩, Finset.mem_attach _ _, rfl⟩), rfl⟩
  have hspan_le : (maximalIdeal R₀).spanFinrank ≤ d := by
    rw [← hmax₀_span]
    calc (Ideal.span (gMax₀ : Set R₀)).spanFinrank ≤ (gMax₀ : Set R₀).ncard :=
          Submodule.spanFinrank_span_le_ncard_of_finite gMax₀.finite_toSet
      _ = gMax₀.card := Set.ncard_coe_finset gMax₀
      _ ≤ d := hgMax₀_card
  have hdim₀_ge : (d : WithBot ℕ∞) ≤ ringKrullDim R₀ := by
    let cR₀ : LTSeries (PrimeSpectrum R₀) := {
      length := d
      toFun := fun i => PrimeSpectrum.comap (algebraMap R₀ R) (cR ⟨i.1, by omega⟩)
      step := fun i => by
        change (cR ⟨i.1, by omega⟩).asIdeal.comap (algebraMap R₀ R) <
          (cR ⟨i.1 + 1, by omega⟩).asIdeal.comap (algebraMap R₀ R)
        refine lt_of_le_of_ne (Ideal.comap_mono (cR.monotone (by
          show (⟨i.1, _⟩ : Fin (cR.length + 1)) ≤ ⟨i.1 + 1, _⟩; exact Nat.le_succ _))) ?_
        intro heq
        have hw_in : wR i ∈ R₀ :=
          hS₀_sub (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨i, rfl⟩)))))
        have h1 : (⟨wR i, hw_in⟩ : R₀) ∈ (cR ⟨i.1 + 1, by omega⟩).asIdeal.comap (algebraMap R₀ R) :=
          hwR_mem i
        rw [← heq] at h1
        exact hwR_nmem i h1
    }
    rw [ringKrullDim, Order.krullDim_eq_iSup_length]
    exact WithBot.coe_le_coe.mpr (le_iSup (fun l : LTSeries (PrimeSpectrum R₀) => (l.length : ℕ∞)) cR₀)
  have hdim₀_le : ringKrullDim R₀ ≤ ((maximalIdeal R₀).spanFinrank : WithBot ℕ∞) :=
    ringKrullDim_le_spanFinrank_maximalIdeal R₀
  have hreg₀ : IsRegularLocalRing R₀ :=
    IsRegularLocalRing.of_spanFinrank_maximalIdeal_le (R := R₀)
      ((WithBot.coe_le_coe.mpr (Nat.cast_le.mpr hspan_le)).trans hdim₀_ge)
  have hdim₀_eq : ringKrullDim R₀ = (d : WithBot ℕ∞) :=
    le_antisymm (hdim₀_le.trans (WithBot.coe_le_coe.mpr (Nat.cast_le.mpr hspan_le))) hdim₀_ge
  -- Step 4: Transfer R₀ to Type 0 via Shrink.{0} and delegate to opaque helper
  let A : Type := Shrink.{0} R₀
  let eA : A ≃+* R₀ := Shrink.ringEquiv.{0} R₀
  let _ : Algebra A R := (R₀.subtype.comp eA.toRingHom).toAlgebra
  have hregA : IsRegularLocalRing A := IsRegularLocalRing.of_ringEquiv eA.symm
  have hlocalA : IsLocalHom (algebraMap A R) := by
    constructor
    intro a ha
    have h1 : IsUnit (eA a) := hlocalHom₀.map_nonunit (eA a) ha
    have h2 : IsUnit (eA.symm (eA a)) := h1.map eA.symm.toRingHom
    rwa [eA.symm_apply_apply] at h2
  have hflatA : Module.Flat A R := by
    apply Module.Flat.of_forall_isTrivialRelation
    intro l f x hrel
    have hrel₀ : ∑ i : Fin l, (eA (f i)) • x i = 0 := hrel
    obtain ⟨k, a, y, hxy, hfa⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hrel₀
    refine ⟨k, fun i j => eA.symm (a i j), y, fun i => ?_, fun j => ?_⟩
    · have h1 : ∀ j, algebraMap A R (eA.symm (a i j)) = algebraMap R₀ R (a i j) := fun j => by
        change (eA (eA.symm (a i j)) : R) = (a i j : R); simp
      simpa [Algebra.smul_def, h1] using hxy i
    · apply eA.injective
      simpa [map_sum, map_mul] using hfa j
  have hmax_mapA : (maximalIdeal A).map (algebraMap A R) = maximalIdeal R := by
    have heq : (maximalIdeal A).map eA.toRingHom = maximalIdeal R₀ :=
      IsLocalRing.map_ringEquiv_maximalIdeal eA
    change (maximalIdeal A).map (R₀.subtype.comp eA.toRingHom) = maximalIdeal R
    rw [← Ideal.map_map, heq]
    exact hmax_map
  have hdimA_eq : ringKrullDim A = ringKrullDim R := by
    rw [ringKrullDim_eq_of_ringEquiv eA, hdim₀_eq, hdimR]
  have hrowsM_in : ∀ (i : Fin bM) (j : Fin aM), rowsM i j ∈ R₀ := fun i j =>
    hS₀_sub (Or.inl (Or.inr ⟨(i, j), rfl⟩))
  have hrowsN_in : ∀ (i : Fin bN) (j : Fin aN), rowsN i j ∈ R₀ := fun i j =>
    hS₀_sub (Or.inr ⟨(i, j), rfl⟩)
  let rowsM₀ : Fin bM → (Fin aM → A) := fun i j => eA.symm ⟨rowsM i j, hrowsM_in i j⟩
  let rowsN₀ : Fin bN → (Fin aN → A) := fun i j => eA.symm ⟨rowsN i j, hrowsN_in i j⟩
  have hrowsM_eq : (fun i : Fin bM => fun j : Fin aM => algebraMap A R (rowsM₀ i j)) = rowsM := by
    ext i j; change (eA (eA.symm ⟨rowsM i j, hrowsM_in i j⟩) : R) = rowsM i j; simp
  have hrowsN_eq : (fun i : Fin bN => fun j : Fin aN => algebraMap A R (rowsN₀ i j)) = rowsN := by
    ext i j; change (eA (eA.symm ⟨rowsN i j, hrowsN_in i j⟩) : R) = rowsN i j; simp
  let wM₀ : Fin dM → A := fun i =>
    eA.symm ⟨wM i, hS₀_sub (Or.inl (Or.inl (Or.inl (Or.inr ⟨i, rfl⟩))))⟩
  let wN₀ : Fin dN → A := fun i =>
    eA.symm ⟨wN i, hS₀_sub (Or.inl (Or.inl (Or.inr ⟨i, rfl⟩)))⟩
  have hwM_eq : ∀ i, algebraMap A R (wM₀ i) = wM i := fun i => by
    change (eA (eA.symm ⟨wM i, _⟩) : R) = wM i; simp
  have hwN_eq : ∀ i, algebraMap A R (wN₀ i) = wN i := fun i => by
    change (eA (eA.symm ⟨wN i, _⟩) : R) = wN i; simp
  obtain ⟨M₀, N₀, _, _, _, _, _, _, hcharA, hpA, hfinA, hdimA_sum, hinterA⟩ :=
    descent_via_opaque_ring A R hmax_mapA hdimA_eq M N p hp hfin hdim aM bM aN bN dM dN
      rowsM₀ rowsN₀
      ((Submodule.quotEquivOfEq _ _ (by rw [hrowsM_eq])).trans eM_pres)
      ((Submodule.quotEquivOfEq _ _ (by rw [hrowsN_eq])).trans eN_pres)
      hdimM hdimN cM hcM_len cN hcN_len
      wM₀ (fun i => by rw [hwM_eq]; exact hwM_mem i) (fun i => by rw [hwM_eq]; exact hwM_nmem i)
      wN₀ (fun i => by rw [hwN_eq]; exact hwN_mem i) (fun i => by rw [hwN_eq]; exact hwN_nmem i)
  exact ⟨A, inferInstance, hregA, M₀, N₀, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, hcharA, hpA, hfinA, hdimA_sum, hinterA⟩

/- Section 3: Completion step using `H1` -/

private lemma completion_reduction (h1 : H1)
    (A : Type) [CommRing A] [IsRegularLocalRing A]
    (M₀ N₀ : Type) [AddCommGroup M₀] [Module A M₀] [Module.Finite A M₀]
    [AddCommGroup N₀] [Module A N₀] [Module.Finite A N₀]
    (p : ℕ) [CharP (ResidueField A) p] (hp : (p : A) ∉ maximalIdeal A ^ 2)
    (hfin : IsFiniteLength A (M₀ ⊗[A] N₀))
    (hdim : Module.supportDim A M₀ + Module.supportDim A N₀ = ringKrullDim A) :
    ∃ (S : Type) (_ : CommRing S) (_ : IsRegularLocalRing S)
      (_ : IsAdicComplete (maximalIdeal S) S)
      (M₁ N₁ : Type) (_ : AddCommGroup M₁) (_ : Module S M₁) (_ : Module.Finite S M₁)
      (_ : AddCommGroup N₁) (_ : Module S N₁) (_ : Module.Finite S N₁),
      CharP (ResidueField S) p ∧
      (p : S) ∉ maximalIdeal S ^ 2 ∧
      IsFiniteLength S (M₁ ⊗[S] N₁) ∧
      Module.supportDim S M₁ + Module.supportDim S N₁ = ringKrullDim S ∧
      Module.intersectionMultiplicity A M₀ N₀ = Module.intersectionMultiplicity S M₁ N₁ := by
  let S : Type := AdicCompletion (maximalIdeal A) A
  obtain ⟨hNoethS, hDimQuot⟩ := h1 A
  have hmaxS : (maximalIdeal A).map (algebraMap A S) = maximalIdeal S :=
    (AdicCompletion.maximalIdeal_eq_map (R := A)).symm
  have hffS : Module.FaithfullyFlat A S := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hdimS : ringKrullDim S = ringKrullDim A := by
    have hbot := hDimQuot ⊥
    rw [Ideal.map_bot] at hbot
    rw [← ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot S), hbot,
      ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot A)]
  have hregS : IsRegularLocalRing S := by
    rw [isRegularLocalRing_iff, hdimS, AdicCompletion.spanFinrank_maximalIdeal_eq]
    exact IsRegularLocalRing.spanFinrank_maximalIdeal
  have hcharS : CharP (ResidueField S) p :=
    (RingHom.charP_iff_charP (IsLocalRing.ResidueField.map (algebraMap A S)) p).mp inferInstance
  have hpS : (p : S) ∉ maximalIdeal S ^ 2 := by
    intro hmem
    apply hp
    rw [← hmaxS, ← Ideal.map_pow] at hmem
    have hcomap : (p : A) ∈ ((maximalIdeal A ^ 2).map (algebraMap A S)).comap (algebraMap A S) := by
      rw [Ideal.mem_comap, map_natCast]; exact hmem
    rwa [Ideal.comap_map_eq_self_of_faithfullyFlat] at hcomap
  let M₁ : Type := S ⊗[A] M₀
  let N₁ : Type := S ⊗[A] N₀
  have hfinS : IsFiniteLength S (M₁ ⊗[S] N₁) :=
    (flat_baseChange_isFiniteLength_tensor_iff A S hmaxS M₀ N₀ M₁ N₁
      (LinearEquiv.refl S _) (LinearEquiv.refl S _)).mpr hfin
  have hdimM₁ : Module.supportDim S M₁ = Module.supportDim A M₀ := by
    rw [Module.supportDim_eq_ringKrullDim_quotient_annihilator,
      Module.supportDim_eq_ringKrullDim_quotient_annihilator,
      annihilator_baseChange A S M₀, hDimQuot]
  have hdimN₁ : Module.supportDim S N₁ = Module.supportDim A N₀ := by
    rw [Module.supportDim_eq_ringKrullDim_quotient_annihilator,
      Module.supportDim_eq_ringKrullDim_quotient_annihilator,
      annihilator_baseChange A S N₀, hDimQuot]
  have hdimS_sum : Module.supportDim S M₁ + Module.supportDim S N₁ = ringKrullDim S := by
    rw [hdimM₁, hdimN₁, hdim, hdimS]
  have hinterS : Module.intersectionMultiplicity A M₀ N₀ = Module.intersectionMultiplicity S M₁ N₁ :=
    (flat_baseChange_interMult A S hmaxS M₀ N₀ M₁ N₁
      (LinearEquiv.refl S _) (LinearEquiv.refl S _)).symm
  exact ⟨S, inferInstance, hregS, inferInstance, M₁, N₁, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, hcharS, hpS, hfinS, hdimS_sum, hinterS⟩

/- Section 4: Ring-isomorphism transport (`S ≃+* MvPowerSeries (Fin n) V`) -/

private lemma ringEquiv_transport
    (T S : Type) [CommRing T] [IsRegularLocalRing T] [CommRing S] [IsRegularLocalRing S]
    (e : T ≃+* S)
    (M₁ N₁ : Type) [AddCommGroup M₁] [Module S M₁] [Module.Finite S M₁]
    [AddCommGroup N₁] [Module S N₁] [Module.Finite S N₁]
    (hfin : IsFiniteLength S (M₁ ⊗[S] N₁))
    (hdim : Module.supportDim S M₁ + Module.supportDim S N₁ = ringKrullDim S) :
    ∃ (M₂ N₂ : Type) (_ : AddCommGroup M₂) (_ : Module T M₂) (_ : Module.Finite T M₂)
      (_ : AddCommGroup N₂) (_ : Module T N₂) (_ : Module.Finite T N₂),
      IsFiniteLength T (M₂ ⊗[T] N₂) ∧
      Module.supportDim T M₂ + Module.supportDim T N₂ = ringKrullDim T ∧
      Module.intersectionMultiplicity S M₁ N₁ = Module.intersectionMultiplicity T M₂ N₂ := by
  let _ : Algebra T S := e.toRingHom.toAlgebra
  have hlocal : IsLocalHom (algebraMap T S) := by
    constructor
    intro x hx
    have hinv : IsUnit (e.symm (e x)) := hx.map e.symm.toRingHom
    rwa [e.symm_apply_apply] at hinv
  have hmax : (maximalIdeal T).map (algebraMap T S) = maximalIdeal S :=
    IsLocalRing.map_ringEquiv_maximalIdeal e
  have hflat : Module.Flat T S := by
    have eTS : T ≃ₗ[T] S := {
      toFun := e
      invFun := e.symm
      left_inv := e.symm_apply_apply
      right_inv := e.apply_symm_apply
      map_add' := e.map_add
      map_smul' := fun t x => by change e (t * x) = e t * e x; exact e.map_mul t x
    }
    exact Module.Flat.of_linearEquiv eTS.symm
  -- Restrict scalars of M₁ and N₁ along e : T →+* S
  let M₂ : Type := M₁
  let N₂ : Type := N₁
  let _ : AddCommGroup M₂ := inferInstanceAs (AddCommGroup M₁)
  let _ : AddCommGroup N₂ := inferInstanceAs (AddCommGroup N₁)
  let _ : Module T M₂ := Module.compHom M₁ e.toRingHom
  let _ : Module T N₂ := Module.compHom N₁ e.toRingHom
  have hfinM₂ : Module.Finite T M₂ := by
    obtain ⟨s, hs⟩ := ‹Module.Finite S M₁›
    refine ⟨s, ?_⟩
    rw [eq_top_iff]
    intro m _
    have hm : m ∈ Submodule.span S (s : Set M₁) := by rw [hs]; trivial
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hm
    · intro x hx; exact Submodule.subset_span hx
    · exact Submodule.zero_mem _
    · intro x y _ _ hx hy; exact Submodule.add_mem _ hx hy
    · intro r x _ hx
      have hsm : r • x = (e.symm r) • (x : M₂) := by
        change r • x = e (e.symm r) • x; rw [e.apply_symm_apply]
      rw [hsm]
      exact Submodule.smul_mem _ _ hx
  have hfinN₂ : Module.Finite T N₂ := by
    obtain ⟨s, hs⟩ := ‹Module.Finite S N₁›
    refine ⟨s, ?_⟩
    rw [eq_top_iff]
    intro m _
    have hm : m ∈ Submodule.span S (s : Set N₁) := by rw [hs]; trivial
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hm
    · intro x hx; exact Submodule.subset_span hx
    · exact Submodule.zero_mem _
    · intro x y _ _ hx hy; exact Submodule.add_mem _ hx hy
    · intro r x _ hx
      have hsm : r • x = (e.symm r) • (x : N₂) := by
        change r • x = e (e.symm r) • x; rw [e.apply_symm_apply]
      rw [hsm]
      exact Submodule.smul_mem _ _ hx
  let mkEquiv : ∀ (X : Type) [AddCommGroup X] [Module S X],
      let _ : Module T X := Module.compHom X e.toRingHom
      S ⊗[T] X ≃ₗ[S] X := fun X _ _ => by
    let _ : Module T X := Module.compHom X e.toRingHom
    let _ : IsScalarTower T S X := {
      smul_assoc := fun t s x => by
        change (e t * s) • x = e t • s • x
        exact mul_smul (e t) s x
    }
    let fwd : S ⊗[T] X →ₗ[S] X :=
      AlgebraTensorModule.lift
        { toFun := fun s =>
            { toFun := fun x => s • x
              map_add' := smul_add s
              map_smul' := fun t x => by
                change s • (e t • x) = e t • (s • x)
                rw [smul_comm] }
          map_add' := fun s₁ s₂ => LinearMap.ext fun x => add_smul s₁ s₂ x
          map_smul' := fun s₁ s₂ => LinearMap.ext fun x => mul_smul s₁ s₂ x }
    let bwd : X →ₗ[S] S ⊗[T] X :=
      { toFun := fun x => (1 : S) ⊗ₜ[T] x
        map_add' := fun x y => TensorProduct.tmul_add 1 x y
        map_smul' := fun s x => by
          have h1 : (1 : S) ⊗ₜ[T] (s • x) = (1 : S) ⊗ₜ[T] ((e.symm s) • x) := by
            congr 1; change s • x = e (e.symm s) • x; rw [e.apply_symm_apply]
          rw [h1, ← TensorProduct.smul_tmul]
          change (e (e.symm s) * 1) ⊗ₜ[T] x = (s * 1) ⊗ₜ[T] x
          rw [e.apply_symm_apply] }
    refine LinearEquiv.ofLinearMap fwd bwd (LinearMap.ext fun x => ?_) (LinearMap.ext fun z => ?_)
    · change (1 : S) • x = x; exact one_smul S x
    · induction z using TensorProduct.induction_on with
      | zero => simp
      | add z₁ z₂ hz₁ hz₂ => rw [map_add, map_add, hz₁, hz₂]
      | tmul s x =>
        change (1 : S) ⊗ₜ[T] (s • x) = s ⊗ₜ[T] x
        have h1 : (1 : S) ⊗ₜ[T] (s • x) = (1 : S) ⊗ₜ[T] ((e.symm s) • x) := by
          congr 1; change s • x = e (e.symm s) • x; rw [e.apply_symm_apply]
        rw [h1, ← TensorProduct.smul_tmul]
        change (e (e.symm s) * 1) ⊗ₜ[T] x = s ⊗ₜ[T] x
        rw [e.apply_symm_apply, mul_one]
  let eM : S ⊗[T] M₂ ≃ₗ[S] M₁ := mkEquiv M₁
  let eN : S ⊗[T] N₂ ≃ₗ[S] N₁ := mkEquiv N₁
  have hfinT : IsFiniteLength T (M₂ ⊗[T] N₂) :=
    (flat_baseChange_isFiniteLength_tensor_iff T S hmax M₂ N₂ M₁ N₁ eM eN).mp hfin
  have hinterT : Module.intersectionMultiplicity S M₁ N₁ = Module.intersectionMultiplicity T M₂ N₂ :=
    flat_baseChange_interMult T S hmax M₂ N₂ M₁ N₁ eM eN
  have hdimM : Module.supportDim T M₂ = Module.supportDim S M₁ := by
    rw [Module.supportDim_eq_ringKrullDim_quotient_annihilator,
      Module.supportDim_eq_ringKrullDim_quotient_annihilator]
    have hann : Module.annihilator S M₁ = (Module.annihilator T M₂).map e.toRingHom := by
      change Module.annihilator S M₁ = (Module.annihilator T M₂).map (algebraMap T S)
      rw [← annihilator_baseChange T S M₂]
      ext s
      simp only [Module.mem_annihilator]
      constructor
      · intro h x; apply eM.injective; rw [map_smul, map_zero]; exact h (eM x)
      · intro h y; obtain ⟨x, rfl⟩ := eM.surjective y; rw [← map_smul, h x, map_zero]
    exact ringKrullDim_eq_of_ringEquiv
      (Ideal.quotientEquiv (Module.annihilator T M₂) (Module.annihilator S M₁) e hann)
  have hdimN : Module.supportDim T N₂ = Module.supportDim S N₁ := by
    rw [Module.supportDim_eq_ringKrullDim_quotient_annihilator,
      Module.supportDim_eq_ringKrullDim_quotient_annihilator]
    have hann : Module.annihilator S N₁ = (Module.annihilator T N₂).map e.toRingHom := by
      change Module.annihilator S N₁ = (Module.annihilator T N₂).map (algebraMap T S)
      rw [← annihilator_baseChange T S N₂]
      ext s
      simp only [Module.mem_annihilator]
      constructor
      · intro h x; apply eN.injective; rw [map_smul, map_zero]; exact h (eN x)
      · intro h y; obtain ⟨x, rfl⟩ := eN.surjective y; rw [← map_smul, h x, map_zero]
    exact ringKrullDim_eq_of_ringEquiv
      (Ideal.quotientEquiv (Module.annihilator T N₂) (Module.annihilator S N₁) e hann)
  have hdimT : Module.supportDim T M₂ + Module.supportDim T N₂ = ringKrullDim T := by
    rw [hdimM, hdimN, hdim, ringKrullDim_eq_of_ringEquiv e]
  exact ⟨M₂, N₂, inferInstance, inferInstance, hfinM₂, inferInstance, inferInstance, hfinN₂,
    hfinT, hdimT, hinterT⟩

/- Section 5: Support, finite length, and prime filtration over `T = MvPowerSeries (Fin n) V` -/

private lemma support_tensor_subset_inter
    {T : Type} [CommRing T]
    {M N : Type} [AddCommGroup M] [Module T M] [Module.Finite T M]
    [AddCommGroup N] [Module T N] [Module.Finite T N] :
    Module.support T (M ⊗[T] N) ⊆ Module.support T M ∩ Module.support T N := by
  intro q hq
  rw [Module.mem_support_iff_of_finite] at hq
  refine ⟨?_, ?_⟩
  · rw [Module.mem_support_iff_of_finite]
    intro r hr
    apply hq
    rw [Module.mem_annihilator]
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact smul_zero r
    | add x₁ x₂ hx₁ hx₂ => rw [smul_add, hx₁, hx₂, add_zero]
    | tmul m n =>
      rw [TensorProduct.smul_tmul', Module.mem_annihilator.mp hr m, TensorProduct.zero_tmul]
  · rw [Module.mem_support_iff_of_finite]
    intro r hr
    apply hq
    rw [Module.mem_annihilator]
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact smul_zero r
    | add x₁ x₂ hx₁ hx₂ => rw [smul_add, hx₁, hx₂, add_zero]
    | tmul m n =>
      rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul,
        Module.mem_annihilator.mp hr n, TensorProduct.tmul_zero]

private lemma inter_subset_support_tensor
    {T : Type} [CommRing T]
    {M N : Type} [AddCommGroup M] [Module T M] [Module.Finite T M]
    [AddCommGroup N] [Module T N] [Module.Finite T N] :
    Module.support T M ∩ Module.support T N ⊆ Module.support T (M ⊗[T] N) := by
  rintro q ⟨hqM, hqN⟩
  let Rq := Localization.AtPrime q.asIdeal
  let k := IsLocalRing.ResidueField Rq
  have nt_of_equiv : ∀ {α β : Type} (e : α ≃ β), Nontrivial α → Nontrivial β := fun e h =>
    ⟨let ⟨a, b, hab⟩ := h.exists_pair_ne; ⟨e a, e b, fun h' => hab (e.injective h')⟩⟩
  have hntM : Nontrivial (LocalizedModule q.asIdeal.primeCompl M) :=
    (Module.mem_support_iff (R := T) (M := M)).mp hqM
  have hntN : Nontrivial (LocalizedModule q.asIdeal.primeCompl N) :=
    (Module.mem_support_iff (R := T) (M := N)).mp hqN
  let Mq := Rq ⊗[T] M
  let Nq := Rq ⊗[T] N
  have _ : Nontrivial Mq :=
    nt_of_equiv (IsLocalizedModule.iso q.asIdeal.primeCompl (TensorProduct.mk T Rq M 1)).toEquiv hntM
  have _ : Nontrivial Nq :=
    nt_of_equiv (IsLocalizedModule.iso q.asIdeal.primeCompl (TensorProduct.mk T Rq N 1)).toEquiv hntN
  have _ : Nontrivial (k ⊗[Rq] Mq) := by
    let eMk : k ⊗[Rq] Mq ≃ₗ[Rq] Mq ⧸ (maximalIdeal Rq • (⊤ : Submodule Rq Mq)) :=
      TensorProduct.quotTensorEquivQuotSMul Mq (maximalIdeal Rq)
    have hqnt : Nontrivial (Mq ⧸ (maximalIdeal Rq • (⊤ : Submodule Rq Mq))) := by
      rw [Submodule.Quotient.nontrivial_iff, ne_comm]
      exact Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator (IsLocalRing.maximalIdeal_le_jacobson _)
    exact nt_of_equiv eMk.symm.toEquiv hqnt
  have _ : Nontrivial (k ⊗[Rq] Nq) := by
    let eNk : k ⊗[Rq] Nq ≃ₗ[Rq] Nq ⧸ (maximalIdeal Rq • (⊤ : Submodule Rq Nq)) :=
      TensorProduct.quotTensorEquivQuotSMul Nq (maximalIdeal Rq)
    have hqnt : Nontrivial (Nq ⧸ (maximalIdeal Rq • (⊤ : Submodule Rq Nq))) := by
      rw [Submodule.Quotient.nontrivial_iff, ne_comm]
      exact Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator (IsLocalRing.maximalIdeal_le_jacobson _)
    exact nt_of_equiv eNk.symm.toEquiv hqnt
  have hntMNk : Nontrivial ((k ⊗[Rq] Mq) ⊗[k] (k ⊗[Rq] Nq)) := by
    obtain ⟨x, hx⟩ := exists_ne (0 : k ⊗[Rq] Mq)
    obtain ⟨y, hy⟩ := exists_ne (0 : k ⊗[Rq] Nq)
    let bM := Module.Basis.ofVectorSpace k (k ⊗[Rq] Mq)
    let bN := Module.Basis.ofVectorSpace k (k ⊗[Rq] Nq)
    have hneM : Nonempty (Module.Basis.ofVectorSpaceIndex k (k ⊗[Rq] Mq)) := by
      by_contra hempty
      rw [not_nonempty_iff] at hempty
      exact hx (bM.repr.injective (Subsingleton.elim _ _))
    have hneN : Nonempty (Module.Basis.ofVectorSpaceIndex k (k ⊗[Rq] Nq)) := by
      by_contra hempty
      rw [not_nonempty_iff] at hempty
      exact hy (bN.repr.injective (Subsingleton.elim _ _))
    obtain ⟨i⟩ := hneM
    obtain ⟨j⟩ := hneN
    exact ⟨⟨(bM.tensorProduct bN) (i, j), 0, (bM.tensorProduct bN).ne_zero (i, j)⟩⟩
  let e1 : k ⊗[Rq] (Mq ⊗[Rq] Nq) ≃ₗ[k] (k ⊗[Rq] Mq) ⊗[k] (k ⊗[Rq] Nq) :=
    ((AlgebraTensorModule.assoc Rq Rq k k Mq Nq).symm).trans
      ((AlgebraTensorModule.cancelBaseChange Rq k k (k ⊗[Rq] Mq) Nq).symm)
  let e2 : Rq ⊗[T] (M ⊗[T] N) ≃ₗ[Rq] Mq ⊗[Rq] Nq :=
    ((AlgebraTensorModule.assoc T T Rq Rq M N).symm).trans
      ((AlgebraTensorModule.cancelBaseChange T Rq Rq Mq N).symm)
  let e3 : k ⊗[Rq] (Rq ⊗[T] (M ⊗[T] N)) ≃ₗ[k] (k ⊗[Rq] Mq) ⊗[k] (k ⊗[Rq] Nq) :=
    (AlgebraTensorModule.congr (LinearEquiv.refl k k) e2).trans e1
  have _ : Nontrivial (k ⊗[Rq] (Rq ⊗[T] (M ⊗[T] N))) := nt_of_equiv e3.symm.toEquiv hntMNk
  rw [Module.mem_support_iff_of_finite]
  intro r hr
  by_contra hrq
  have hunit : IsUnit (algebraMap T Rq r) :=
    IsLocalization.map_units Rq (⟨r, hrq⟩ : q.asIdeal.primeCompl)
  have hunitk : IsUnit (algebraMap Rq k (algebraMap T Rq r)) :=
    hunit.map (algebraMap Rq k)
  obtain ⟨z, hz⟩ := exists_ne (0 : k ⊗[Rq] (Rq ⊗[T] (M ⊗[T] N)))
  have hkill : (algebraMap Rq k (algebraMap T Rq r)) • z = 0 := by
    clear hz
    induction z using TensorProduct.induction_on with
    | zero => exact smul_zero _
    | add z₁ z₂ hz₁ hz₂ => rw [smul_add, hz₁, hz₂, add_zero]
    | tmul c w =>
      induction w using TensorProduct.induction_on with
      | zero => simp
      | add w₁ w₂ hw₁ hw₂ => rw [TensorProduct.tmul_add, smul_add, hw₁, hw₂, add_zero]
      | tmul s u =>
        calc (algebraMap Rq k (algebraMap T Rq r)) • (c ⊗ₜ[Rq] (s ⊗ₜ[T] u))
            = (algebraMap Rq k (algebraMap T Rq r) * c) ⊗ₜ[Rq] (s ⊗ₜ[T] u) := rfl
          _ = ((algebraMap T Rq r) • c) ⊗ₜ[Rq] (s ⊗ₜ[T] u) := by rw [Algebra.smul_def]
          _ = c ⊗ₜ[Rq] ((algebraMap T Rq r) • (s ⊗ₜ[T] u)) := TensorProduct.smul_tmul _ c _
          _ = c ⊗ₜ[Rq] ((algebraMap T Rq r * s) ⊗ₜ[T] u) := rfl
          _ = c ⊗ₜ[Rq] ((r • s) ⊗ₜ[T] u) := by rw [Algebra.smul_def]
          _ = c ⊗ₜ[Rq] (s ⊗ₜ[T] (r • u)) := by rw [TensorProduct.smul_tmul]
          _ = 0 := by rw [Module.mem_annihilator.mp hr u, TensorProduct.tmul_zero, TensorProduct.tmul_zero]
  exact hz (by
    have hinv := congrArg (fun v => ((hunitk.unit⁻¹ : kˣ) : k) • v) hkill
    rw [smul_zero, smul_smul] at hinv
    have hmul1 : ((hunitk.unit⁻¹ : kˣ) : k) * algebraMap Rq k (algebraMap T Rq r) = 1 := by
      have hu : (hunitk.unit : k) = algebraMap Rq k (algebraMap T Rq r) := hunitk.unit_spec
      calc ((hunitk.unit⁻¹ : kˣ) : k) * algebraMap Rq k (algebraMap T Rq r)
          = ((hunitk.unit⁻¹ : kˣ) : k) * (hunitk.unit : k) := by rw [hu]
        _ = 1 := Units.inv_mul hunitk.unit
    rw [hmul1, one_smul] at hinv
    exact hinv)

private lemma isFiniteLength_iff_supportDim_le_zero
    {T : Type} [CommRing T] [IsNoetherianRing T]
    {X : Type} [AddCommGroup X] [Module T X] [Module.Finite T X] :
    IsFiniteLength T X ↔ Module.supportDim T X ≤ 0 := by
  rw [Module.supportDim_eq_ringKrullDim_quotient_annihilator]
  constructor
  · intro hfin
    have hArtX : IsArtinian T X := (isFiniteLength_iff_isNoetherian_isArtinian.mp hfin).2
    obtain ⟨s, hs⟩ := ‹Module.Finite T X›
    let φ : T →ₗ[T] (s → X) := {
      toFun := fun t i => t • (i : X)
      map_add' := fun a b => by ext i; exact add_smul a b (i : X)
      map_smul' := fun a b => by ext i; exact mul_smul a b (i : X)
    }
    have hker : LinearMap.ker φ = Module.annihilator T X := by
      ext t
      simp only [LinearMap.mem_ker, funext_iff, Pi.zero_apply, Module.mem_annihilator, φ,
        LinearMap.coe_mk, AddHom.coe_mk]
      constructor
      · intro h x
        have hx : x ∈ Submodule.span T (s : Set X) := by rw [hs]; trivial
        refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
        · intro y hy; exact h ⟨y, hy⟩
        · exact smul_zero t
        · intro y z _ _ hy hz; rw [smul_add, hy, hz, add_zero]
        · intro c y _ hy; rw [smul_comm, hy, smul_zero]
      · intro h i; exact h (i : X)
    let emb : (T ⧸ Module.annihilator T X) →ₗ[T] (s → X) :=
      (Module.annihilator T X).liftQ φ (le_of_eq hker.symm)
    have hemb_inj : Function.Injective emb := by
      rw [← LinearMap.ker_eq_bot, Submodule.ker_liftQ, hker, Submodule.mkQ_map_self]
    have hArtQ_T : IsArtinian T (T ⧸ Module.annihilator T X) :=
      isArtinian_of_injective emb hemb_inj
    have hArtQ : IsArtinianRing (T ⧸ Module.annihilator T X) := by
      rw [IsArtinianRing]
      exact isArtinian_of_tower T hArtQ_T
    have hdimLE : Ring.KrullDimLE 0 (T ⧸ Module.annihilator T X) :=
      (isArtinianRing_iff_krullDimLE_zero (R := T ⧸ Module.annihilator T X)).mp hArtQ
    exact (Ring.krullDimLE_iff (R := T ⧸ Module.annihilator T X) (n := 0)).mp hdimLE
  · intro hdim0
    have hdimLE : Ring.KrullDimLE 0 (T ⧸ Module.annihilator T X) :=
      (Ring.krullDimLE_iff (R := T ⧸ Module.annihilator T X) (n := 0)).mpr hdim0
    have hArtQ : IsArtinianRing (T ⧸ Module.annihilator T X) :=
      (isArtinianRing_iff_krullDimLE_zero (R := T ⧸ Module.annihilator T X)).mpr hdimLE
    let actHom : (T ⧸ Module.annihilator T X) →+* AddMonoid.End X :=
      Ideal.Quotient.lift (Module.annihilator T X) (Module.toAddMonoidEnd T X) (by
        intro t ht
        ext x
        exact Module.mem_annihilator.mp ht x)
    let _ : Module (T ⧸ Module.annihilator T X) X := {
      smul := fun r x => actHom r x
      one_smul := fun x => by change actHom 1 x = x; rw [map_one]; rfl
      mul_smul := fun r s x => by change actHom (r * s) x = actHom r (actHom s x); rw [map_mul]; rfl
      smul_zero := fun r => (actHom r).map_zero
      smul_add := fun r x y => (actHom r).map_add x y
      add_smul := fun r s x => by change actHom (r + s) x = actHom r x + actHom s x; rw [map_add]; rfl
      zero_smul := fun x => by change actHom 0 x = 0; rw [map_zero]; rfl
    }
    have hsmul_mk : ∀ (t : T) (x : X),
        (Ideal.Quotient.mk (Module.annihilator T X) t) • x = t • x := fun _ _ => rfl
    have hfinQ : Module.Finite (T ⧸ Module.annihilator T X) X := by
      obtain ⟨s, hs⟩ := ‹Module.Finite T X›
      refine ⟨s, ?_⟩
      rw [eq_top_iff]
      intro x _
      have hx : x ∈ Submodule.span T (s : Set X) := by rw [hs]; trivial
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
      · intro y hy; exact Submodule.subset_span hy
      · exact Submodule.zero_mem _
      · intro y z _ _ hy hz; exact Submodule.add_mem _ hy hz
      · intro t y _ hy
        rw [← hsmul_mk t y]
        exact Submodule.smul_mem _ _ hy
    have hArtQX : IsArtinian (T ⧸ Module.annihilator T X) X := inferInstance
    have hArtX : IsArtinian T X := by
      let e : Submodule T X ≃o Submodule (T ⧸ Module.annihilator T X) X := {
        toFun := fun N => {
          carrier := N
          add_mem' := N.add_mem
          zero_mem' := N.zero_mem
          smul_mem' := fun r x hx => by
            obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective r
            rw [hsmul_mk t x]
            exact N.smul_mem t hx
        }
        invFun := fun N => {
          carrier := N
          add_mem' := N.add_mem
          zero_mem' := N.zero_mem
          smul_mem' := fun t x hx => by
            rw [← hsmul_mk t x]
            exact N.smul_mem (Ideal.Quotient.mk (Module.annihilator T X) t) hx
        }
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_rel_iff' := Iff.rfl
      }
      let embLT : ((· < ·) : Submodule T X → Submodule T X → Prop) ↪r
          ((· < ·) : Submodule (T ⧸ Module.annihilator T X) X →
            Submodule (T ⧸ Module.annihilator T X) X → Prop) := {
        toFun := e
        inj' := e.injective
        map_rel_iff' := e.lt_iff_lt
      }
      exact (isArtinian_iff T X).mpr (RelEmbedding.wellFounded embLT ((isArtinian_iff _ X).mp hArtQX))
    exact isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, hArtX⟩

private lemma isFiniteLength_tensor_of_injective
    {T : Type} [CommRing T] [IsNoetherianRing T]
    {L₁ L₂ N : Type} [AddCommGroup L₁] [Module T L₁] [Module.Finite T L₁]
    [AddCommGroup L₂] [Module T L₂] [Module.Finite T L₂]
    [AddCommGroup N] [Module T N] [Module.Finite T N]
    (f : L₁ →ₗ[T] L₂) (hf : Function.Injective f)
    (hfin : IsFiniteLength T (L₂ ⊗[T] N)) :
    IsFiniteLength T (L₁ ⊗[T] N) := by
  rw [isFiniteLength_iff_supportDim_le_zero] at hfin ⊢
  have hsub : Module.support T (L₁ ⊗[T] N) ⊆ Module.support T (L₂ ⊗[T] N) :=
    support_tensor_subset_inter.trans
      ((Set.inter_subset_inter_left _ (Module.support_subset_of_injective f hf)).trans
        inter_subset_support_tensor)
  exact (Order.krullDim_le_of_strictMono (fun a => ⟨a.1, hsub a.2⟩) (fun _ _ h => h)).trans hfin

private lemma isFiniteLength_tensor_of_surjective
    {T : Type} [CommRing T]
    {L₂ L₃ N : Type} [AddCommGroup L₂] [Module T L₂] [AddCommGroup L₃] [Module T L₃]
    [AddCommGroup N] [Module T N]
    (g : L₂ →ₗ[T] L₃) (hg : Function.Surjective g)
    (hfin : IsFiniteLength T (L₂ ⊗[T] N)) :
    IsFiniteLength T (L₃ ⊗[T] N) :=
  hfin.of_surjective (LinearMap.rTensor_surjective N hg)

private lemma supportDim_eq_max_of_exact
    {T : Type} [CommRing T]
    {L₁ L₂ L₃ : Type} [AddCommGroup L₁] [Module T L₁] [AddCommGroup L₂] [Module T L₂]
    [AddCommGroup L₃] [Module T L₃]
    (f : L₁ →ₗ[T] L₂) (g : L₂ →ₗ[T] L₃)
    (hf : Function.Injective f) (hfg : Function.Exact f g) (hg : Function.Surjective g) :
    Module.supportDim T L₂ = max (Module.supportDim T L₁) (Module.supportDim T L₃) := by
  apply le_antisymm
  · by_cases hsub : Subsingleton L₂
    · rw [Module.supportDim_eq_bot_of_subsingleton]; exact bot_le
    have hnt : Nontrivial L₂ := not_subsingleton_iff_nontrivial.mp hsub
    have _ : Nonempty (Module.support T L₂) :=
      (Module.nonempty_support_of_nontrivial (R := T) (M := L₂)).to_subtype
    have hsupp := Module.support_of_exact hfg hf hg
    rw [Module.supportDim, Order.krullDim_eq_iSup_length]
    have hle : ∀ l : LTSeries (Module.support T L₂),
        (l.length : WithBot ℕ∞) ≤ max (Module.supportDim T L₁) (Module.supportDim T L₃) := by
      intro l
      have h0 : (l 0).1 ∈ Module.support T L₁ ∪ Module.support T L₃ := by
        rw [← hsupp]; exact (l 0).2
      rcases h0 with h1 | h3
      · have hall : ∀ k : Fin (l.length + 1), (l k).1 ∈ Module.support T L₁ := fun k =>
          Module.mem_support_mono (l.monotone (Fin.zero_le k)) h1
        let l₁ : LTSeries (Module.support T L₁) := {
          length := l.length
          toFun := fun k => ⟨(l k).1, hall k⟩
          step := fun i => l.step i
        }
        have _ : Nonempty (Module.support T L₁) := ⟨l₁ 0⟩
        refine le_trans ?_ (le_max_left _ _)
        rw [Module.supportDim, Order.krullDim_eq_iSup_length]
        exact WithBot.coe_le_coe.mpr
          (le_iSup (fun p : LTSeries (Module.support T L₁) => (p.length : ℕ∞)) l₁)
      · have hall : ∀ k : Fin (l.length + 1), (l k).1 ∈ Module.support T L₃ := fun k =>
          Module.mem_support_mono (l.monotone (Fin.zero_le k)) h3
        let l₃ : LTSeries (Module.support T L₃) := {
          length := l.length
          toFun := fun k => ⟨(l k).1, hall k⟩
          step := fun i => l.step i
        }
        have _ : Nonempty (Module.support T L₃) := ⟨l₃ 0⟩
        refine le_trans ?_ (le_max_right _ _)
        rw [Module.supportDim, Order.krullDim_eq_iSup_length]
        exact WithBot.coe_le_coe.mpr
          (le_iSup (fun p : LTSeries (Module.support T L₃) => (p.length : ℕ∞)) l₃)
    -- Lift iSup in ℕ∞ to WithBot ℕ∞
    cases hm : max (Module.supportDim T L₁) (Module.supportDim T L₃) with
    | bot =>
      obtain ⟨x⟩ := (inferInstance : Nonempty (Module.support T L₂))
      have := hle (RelSeries.singleton _ x)
      rw [hm] at this
      exact absurd (le_bot_iff.mp this) (WithBot.coe_ne_bot)
    | coe c =>
      apply WithBot.coe_le_coe.mpr
      apply iSup_le
      intro l
      have := hle l
      rw [hm] at this
      exact WithBot.coe_le_coe.mp this
  · exact max_le (Module.supportDim_le_of_injective f hf) (Module.supportDim_le_of_surjective g hg)

private lemma prime_filtration_ind
    (T : Type) [CommRing T] [IsNoetherianRing T]
    (M : Type) [AddCommGroup M] [Module T M] [Module.Finite T M]
    (P_pred : ∀ (L : Type) [AddCommGroup L] [Module T L] [Module.Finite T L], Prop)
    (h_subsingleton : ∀ (L : Type) [AddCommGroup L] [Module T L] [Module.Finite T L],
      Subsingleton L → P_pred L)
    (h_iso : ∀ (L₁ L₂ : Type) [AddCommGroup L₁] [Module T L₁] [Module.Finite T L₁]
      [AddCommGroup L₂] [Module T L₂] [Module.Finite T L₂],
      (L₁ ≃ₗ[T] L₂) → P_pred L₁ → P_pred L₂)
    (h_ext : ∀ (L₁ L₂ L₃ : Type) [AddCommGroup L₁] [Module T L₁] [Module.Finite T L₁]
      [AddCommGroup L₂] [Module T L₂] [Module.Finite T L₂]
      [AddCommGroup L₃] [Module T L₃] [Module.Finite T L₃]
      (f : L₁ →ₗ[T] L₂) (g : L₂ →ₗ[T] L₃),
      Function.Injective f → Function.Exact f g → Function.Surjective g →
      P_pred L₁ → P_pred L₃ → P_pred L₂)
    (h_prime : ∀ (Q : Ideal T) [Q.IsPrime], P_pred (T ⧸ Q)) :
    P_pred M := by
  let S : Set (Submodule T M) := { L | P_pred L }
  have hbot : (⊥ : Submodule T M) ∈ S := h_subsingleton _ inferInstance
  obtain ⟨L₀, hL₀_mem, hL₀_max⟩ :=
    set_has_maximal_iff_noetherian.mpr (inferInstance : IsNoetherian T M) S ⟨⊥, hbot⟩
  have htop : L₀ = ⊤ := by
    by_contra hne
    have hnt : Nontrivial (M ⧸ L₀) := Submodule.Quotient.nontrivial_iff.mpr hne
    obtain ⟨x, hx⟩ := exists_ne (0 : M ⧸ L₀)
    obtain ⟨Q, hQass, _⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing T x hx
    obtain ⟨hQp, y, hQy⟩ := (isAssociatedPrime_iff (R := T) (I := Q) (M := M ⧸ L₀)).mp hQass
    let _ : Q.IsPrime := hQp
    have hy0 : y ≠ 0 := by
      intro h0
      apply hQp.ne_top
      rw [hQy, h0]
      ext r; simp
    let smulMap : T →ₗ[T] (M ⧸ L₀) := LinearMap.toSpanSingleton T (M ⧸ L₀) y
    have hker : LinearMap.ker smulMap = Q := by
      rw [hQy]
      ext r
      simp [smulMap, Submodule.mem_colon_singleton]
    let eQ : (T ⧸ Q) ≃ₗ[T] Submodule.span T {y} :=
      (Submodule.quotEquivOfEq Q (LinearMap.ker smulMap) hker.symm).trans
        ((smulMap.quotKerEquivRange).trans
          (LinearEquiv.ofEq _ _ (LinearMap.span_singleton_eq_range T (M ⧸ L₀) y).symm))
    let L₁ : Submodule T M := (Submodule.span T {y}).comap L₀.mkQ
    have hL₀_le : L₀ ≤ L₁ := by
      intro m hm
      rw [Submodule.mem_comap, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero L₀).mpr hm]
      exact Submodule.zero_mem _
    have hL₀_lt : L₀ < L₁ := by
      refine lt_of_le_of_ne hL₀_le ?_
      intro heq
      obtain ⟨m, hm⟩ := Submodule.mkQ_surjective L₀ y
      have hm1 : m ∈ L₁ := by rw [Submodule.mem_comap, hm]; exact Submodule.subset_span rfl
      rw [← heq] at hm1
      exact hy0 (hm.symm.trans ((Submodule.Quotient.mk_eq_zero L₀).mpr hm1))
    let f : L₀ →ₗ[T] L₁ := Submodule.inclusion hL₀_le
    let g0 : L₁ →ₗ[T] Submodule.span T {y} := {
      toFun := fun m => ⟨L₀.mkQ m.1, m.2⟩
      map_add' := fun a b => by ext; exact map_add L₀.mkQ a.1 b.1
      map_smul' := fun r a => by ext; exact map_smul L₀.mkQ r a.1
    }
    let g : L₁ →ₗ[T] (T ⧸ Q) := eQ.symm.toLinearMap.comp g0
    have hf : Function.Injective f := Submodule.inclusion_injective hL₀_le
    have hg0_surj : Function.Surjective g0 := by
      rintro ⟨z, hz⟩
      obtain ⟨m, hm⟩ := Submodule.mkQ_surjective L₀ z
      exact ⟨⟨m, by rw [Submodule.mem_comap, hm]; exact hz⟩, by ext; exact hm⟩
    have hg : Function.Surjective g := eQ.symm.surjective.comp hg0_surj
    have hfg : Function.Exact f g := by
      intro m
      constructor
      · intro hm
        have hg0 : g0 m = 0 := eQ.symm.injective (by simpa [g] using hm)
        have hmk : L₀.mkQ m.1 = 0 := congrArg Subtype.val hg0
        have hmL₀ : m.1 ∈ L₀ := (Submodule.Quotient.mk_eq_zero L₀).mp hmk
        exact ⟨⟨m.1, hmL₀⟩, rfl⟩
      · rintro ⟨a, rfl⟩
        change eQ.symm (g0 (f a)) = 0
        have hg0 : g0 (f a) = 0 := Subtype.ext ((Submodule.Quotient.mk_eq_zero L₀).mpr a.2)
        rw [hg0, map_zero]
    have hL₁_mem : L₁ ∈ S := h_ext L₀ L₁ (T ⧸ Q) f g hf hfg hg hL₀_mem (h_prime Q)
    exact hL₀_max L₁ hL₁_mem hL₀_lt
  have htop_mem : (⊤ : Submodule T M) ∈ S := htop ▸ hL₀_mem
  exact h_iso (⊤ : Submodule T M) M Submodule.topEquiv htop_mem

private lemma interMult_eq_zero_of_subsingleton_left
    {T : Type} [CommRing T]
    {M N : Type} [AddCommGroup M] [Module T M] [AddCommGroup N] [Module T N]
    [Subsingleton M] :
    Module.intersectionMultiplicity T M N = 0 := by
  have hM := ModuleCat.isZero_of_subsingleton (ModuleCat.of T M)
  have hTor : ∀ i : ℕ, IsZero (((Tor (ModuleCat.{0} T) i).obj (ModuleCat.of T M)).obj
      (ModuleCat.of T N)) := fun i => by
    refine IsZero.of_iso ?_ ((projectiveResolution (ModuleCat.of T N)).isoLeftDerivedObj _ i)
    exact ShortComplex.isZero_homology_of_isZero_X₂ _
      (((tensoringRight (ModuleCat.{0} T)).obj _).map_isZero hM)
  unfold Module.intersectionMultiplicity
  refine finsum_eq_zero_of_forall_eq_zero fun i => ?_
  have := ModuleCat.isZero_iff_subsingleton.mp (hTor i)
  simp

private lemma interMult_eq_zero_of_subsingleton_right
    {T : Type} [CommRing T]
    {M N : Type} [AddCommGroup M] [Module T M] [AddCommGroup N] [Module T N]
    [Subsingleton N] :
    Module.intersectionMultiplicity T M N = 0 := by
  have hN := ModuleCat.isZero_of_subsingleton (ModuleCat.of T N)
  have hProj : Projective (ModuleCat.of T N) := hN.projective
  have hTor : ∀ i : ℕ, IsZero (((Tor (ModuleCat.{0} T) i).obj (ModuleCat.of T M)).obj
      (ModuleCat.of T N)) := fun i => by
    refine IsZero.of_iso ?_
      ((ProjectiveResolution.self (ModuleCat.of T N)).isoLeftDerivedObj _ i)
    have hX : IsZero (((ProjectiveResolution.self (ModuleCat.of T N)).complex).X i) := by
      cases i with
      | zero => exact hN
      | succ n => exact HomologicalComplex.isZero_single_obj_X _ _ _ _ (by simp)
    exact ShortComplex.isZero_homology_of_isZero_X₂ _
      (((tensoringLeft (ModuleCat.{0} T)).obj (ModuleCat.of T M)).map_isZero hX)
  unfold Module.intersectionMultiplicity
  refine finsum_eq_zero_of_forall_eq_zero fun i => ?_
  have := ModuleCat.isZero_iff_subsingleton.mp (hTor i)
  simp

private lemma pos_of_mvPowerSeries_dvr (h2 : H2) (h4 : H4)
    (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [IsAdicComplete (maximalIdeal V) V]
    (n : ℕ) [IsRegularLocalRing (MvPowerSeries (Fin n) V)]
    (M N : Type) [AddCommGroup M] [Module (MvPowerSeries (Fin n) V) M]
    [Module.Finite (MvPowerSeries (Fin n) V) M]
    [AddCommGroup N] [Module (MvPowerSeries (Fin n) V) N]
    [Module.Finite (MvPowerSeries (Fin n) V) N]
    (hfin : IsFiniteLength (MvPowerSeries (Fin n) V) (M ⊗[MvPowerSeries (Fin n) V] N))
    (hdim : Module.supportDim (MvPowerSeries (Fin n) V) M +
      Module.supportDim (MvPowerSeries (Fin n) V) N =
      ringKrullDim (MvPowerSeries (Fin n) V)) :
    0 < Module.intersectionMultiplicity (MvPowerSeries (Fin n) V) M N := by
  let T := MvPowerSeries (Fin n) V
  -- Step 1: Prime quotient on the left, arbitrary finite module on the right
  have hPrimeLeft : ∀ (P : Ideal T) [P.IsPrime]
      (L : Type) [AddCommGroup L] [Module T L] [Module.Finite T L],
      IsFiniteLength T ((T ⧸ P) ⊗[T] L) →
      0 ≤ Module.intersectionMultiplicity T (T ⧸ P) L ∧
      (ringKrullDim (T ⧸ P) + Module.supportDim T L = ringKrullDim T →
        0 < Module.intersectionMultiplicity T (T ⧸ P) L) := by
    intro P _ L _ _ _
    refine prime_filtration_ind T L
      (fun X _ _ _ =>
        IsFiniteLength T ((T ⧸ P) ⊗[T] X) →
        0 ≤ Module.intersectionMultiplicity T (T ⧸ P) X ∧
        (ringKrullDim (T ⧸ P) + Module.supportDim T X = ringKrullDim T →
          0 < Module.intersectionMultiplicity T (T ⧸ P) X))
      ?_ ?_ ?_ ?_
    · intro X _ _ _ hsub _
      refine ⟨?_, ?_⟩
      · rw [interMult_eq_zero_of_subsingleton_right]
      · intro hsum
        rw [Module.supportDim_eq_bot_of_subsingleton, WithBot.add_bot] at hsum
        have hne : ringKrullDim T ≠ ⊥ := by
          rw [← Module.supportDim_self_eq_ringKrullDim]
          exact Module.supportDim_ne_bot_of_nontrivial T T
        exact absurd hsum.symm hne
    · intro X₁ X₂ _ _ _ _ _ _ e hX₁ hfin₂
      have hfin₁ : IsFiniteLength T ((T ⧸ P) ⊗[T] X₁) :=
        (AlgebraTensorModule.congr (LinearEquiv.refl T _) e.symm).isFiniteLength hfin₂
      obtain ⟨hnn, hpos⟩ := hX₁ hfin₁
      rw [← interMult_congr (LinearEquiv.refl T (T ⧸ P)) e]
      refine ⟨hnn, fun hsum => hpos ?_⟩
      rwa [Module.supportDim_eq_of_equiv e]
    · intro X₁ X₂ X₃ _ _ _ _ _ _ _ _ _ f g hf hfg hg hX₁ hX₃ hfin₂
      have hfin₂' : IsFiniteLength T (X₂ ⊗[T] (T ⧸ P)) :=
        (TensorProduct.comm T (T ⧸ P) X₂).isFiniteLength hfin₂
      have hfin₁ : IsFiniteLength T ((T ⧸ P) ⊗[T] X₁) :=
        (TensorProduct.comm T X₁ (T ⧸ P)).isFiniteLength
          (isFiniteLength_tensor_of_injective f hf hfin₂')
      have hfin₃ : IsFiniteLength T ((T ⧸ P) ⊗[T] X₃) :=
        (TensorProduct.comm T X₃ (T ⧸ P)).isFiniteLength
          (isFiniteLength_tensor_of_surjective g hg hfin₂')
      obtain ⟨hnn₁, hpos₁⟩ := hX₁ hfin₁
      obtain ⟨hnn₃, hpos₃⟩ := hX₃ hfin₃
      have hadd := (h2 T X₁ X₂ X₃ (T ⧸ P) f g hf hfg hg hfin₂').2
      rw [hadd]
      refine ⟨add_nonneg hnn₁ hnn₃, fun hsum => ?_⟩
      have hmax := supportDim_eq_max_of_exact f g hf hfg hg
      rcases le_total (Module.supportDim T X₁) (Module.supportDim T X₃) with hle | hle
      · rw [max_eq_right hle] at hmax
        rw [hmax] at hsum
        exact add_pos_of_nonneg_of_pos hnn₁ (hpos₃ hsum)
      · rw [max_eq_left hle] at hmax
        rw [hmax] at hsum
        exact add_pos_of_pos_of_nonneg (hpos₁ hsum) hnn₃
    · intro Q _
      rw [Module.supportDim_quotient_eq_ringKrullDim Q]
      exact h4 V n P Q
  -- Step 2: Arbitrary finite module on the left, fixed N on the right
  have hGen : ∀ (L : Type) [AddCommGroup L] [Module T L] [Module.Finite T L],
      IsFiniteLength T (L ⊗[T] N) →
      0 ≤ Module.intersectionMultiplicity T L N ∧
      (Module.supportDim T L + Module.supportDim T N = ringKrullDim T →
        0 < Module.intersectionMultiplicity T L N) := by
    intro L _ _ _
    refine prime_filtration_ind T L
      (fun X _ _ _ =>
        IsFiniteLength T (X ⊗[T] N) →
        0 ≤ Module.intersectionMultiplicity T X N ∧
        (Module.supportDim T X + Module.supportDim T N = ringKrullDim T →
          0 < Module.intersectionMultiplicity T X N))
      ?_ ?_ ?_ ?_
    · intro X _ _ _ hsub _
      refine ⟨?_, ?_⟩
      · rw [interMult_eq_zero_of_subsingleton_left]
      · intro hsum
        rw [Module.supportDim_eq_bot_of_subsingleton, WithBot.bot_add] at hsum
        have hne : ringKrullDim T ≠ ⊥ := by
          rw [← Module.supportDim_self_eq_ringKrullDim]
          exact Module.supportDim_ne_bot_of_nontrivial T T
        exact absurd hsum.symm hne
    · intro X₁ X₂ _ _ _ _ _ _ e hX₁ hfin₂
      have hfin₁ : IsFiniteLength T (X₁ ⊗[T] N) :=
        (AlgebraTensorModule.congr e.symm (LinearEquiv.refl T _)).isFiniteLength hfin₂
      obtain ⟨hnn, hpos⟩ := hX₁ hfin₁
      rw [← interMult_congr e (LinearEquiv.refl T N)]
      refine ⟨hnn, fun hsum => hpos ?_⟩
      rwa [Module.supportDim_eq_of_equiv e]
    · intro X₁ X₂ X₃ _ _ _ _ _ _ _ _ _ f g hf hfg hg hX₁ hX₃ hfin₂
      have hfin₁ : IsFiniteLength T (X₁ ⊗[T] N) :=
        isFiniteLength_tensor_of_injective f hf hfin₂
      have hfin₃ : IsFiniteLength T (X₃ ⊗[T] N) :=
        isFiniteLength_tensor_of_surjective g hg hfin₂
      obtain ⟨hnn₁, hpos₁⟩ := hX₁ hfin₁
      obtain ⟨hnn₃, hpos₃⟩ := hX₃ hfin₃
      have hadd := (h2 T X₁ X₂ X₃ N f g hf hfg hg hfin₂).1
      rw [hadd]
      refine ⟨add_nonneg hnn₁ hnn₃, fun hsum => ?_⟩
      have hmax := supportDim_eq_max_of_exact f g hf hfg hg
      rcases le_total (Module.supportDim T X₁) (Module.supportDim T X₃) with hle | hle
      · rw [max_eq_right hle] at hmax
        rw [hmax] at hsum
        exact add_pos_of_nonneg_of_pos hnn₁ (hpos₃ hsum)
      · rw [max_eq_left hle] at hmax
        rw [hmax] at hsum
        exact add_pos_of_pos_of_nonneg (hpos₁ hsum) hnn₃
    · intro P _ hfinP
      have hP := hPrimeLeft P N hfinP
      rw [Module.supportDim_quotient_eq_ringKrullDim P]
      exact hP
  exact (hGen M hfin).2 hdim

end

theorem main : H1 → H2 → H3 → H4 →
    type_of% @SerreMultiplicityConjectures.intersectionMultiplicity_pos_of_unramified := by
  intro h1 h2 h3 h4 R _ _ M N _ _ _ _ _ _ p _ hp h hdim
  obtain ⟨A, _, _, M₀, N₀, _, _, _, _, _, _, hcharA, hpA, hfinA, hdimA, hinterA⟩ :=
    exists_countable_flat_descent R M N p hp h hdim
  obtain ⟨S, _, _, _, M₁, N₁, _, _, _, _, _, _, hcharS, hpS, hfinS, hdimS, hinterS⟩ :=
    completion_reduction h1 A M₀ N₀ p hpA hfinA hdimA
  obtain ⟨V, _, _, _, _, n, _, ⟨e⟩⟩ := h3 S p hpS
  have hregT : IsRegularLocalRing (MvPowerSeries (Fin n) V) :=
    IsRegularLocalRing.of_ringEquiv e.symm
  obtain ⟨M₂, N₂, _, _, _, _, _, _, hfinT, hdimT, hinterT⟩ :=
    ringEquiv_transport (MvPowerSeries (Fin n) V) S e M₁ N₁ hfinS hdimS
  rw [hinterA, hinterS, hinterT]
  exact pos_of_mvPowerSeries_dvr h2 h4 V n M₂ N₂ hfinT hdimT

end OMA.R_SerreMultiplicityConjectures_intersectionMultiplicity_pos_of_unramified_R1
