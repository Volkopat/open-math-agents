import OMAStatements.S_wp_bass_quillen_conjecture
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Finiteness.Projective
import Mathlib.RingTheory.LocalProperties.Projective
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

-- Reduction wp-bass-quillen-conjecture.R1 of Bass–Quillen conjecture
-- Credit: @tongenspace

/-!
# Reduction of the Bass–Quillen conjecture to the local case and univariate Quillen patching

Following D. Quillen, *Projective modules over polynomial rings*, Invent. Math. 36 (1976),
167–171, and T. Y. Lam, *Serre's Problem on Projective Modules* (2006), Ch. V:

* `H1` is the **Local Bass–Quillen conjecture**: over every regular local ring `R`, every finitely
  generated projective module over `R[t₁, ..., tₙ]` is free.
* `H2` is the **Univariate Quillen Patching Theorem** (Quillen 1976, Theorem 1): over any
  commutative ring `R`, a finitely generated projective `R[X]`-module whose localization at every
  maximal ideal `m` of `R` is free over `Rₘ[X]` is extended from a finitely generated projective
  `R`-module.
* `main` proves that `H1` and `H2` together imply the full multivariate Bass–Quillen conjecture
  over arbitrary regular Noetherian commutative rings `A`: `H1` implies local freeness at every
  maximal ideal of `A` via `IsRegularRing` and `MvPolynomial.isLocalization`, and induction on `n`
  using `MvPolynomial.finSuccEquiv` and `H2` yields extension from a finitely generated projective
  `A`-module.
-/

namespace OMA.R_wp_bass_quillen_conjecture_R1

open scoped TensorProduct

/-- Local Bass–Quillen conjecture: over every regular local ring `R`, every finitely generated
projective module over `R[t₁, ..., tₙ]` is free. -/
def H1 : Prop :=
  ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] (n : ℕ)
    (P : Type) [AddCommGroup P] [Module (MvPolynomial (Fin n) R) P]
    [Module.Finite (MvPolynomial (Fin n) R) P]
    [Module.Projective (MvPolynomial (Fin n) R) P],
    Module.Free (MvPolynomial (Fin n) R) P

/-- Univariate Quillen patching theorem (Quillen 1976, Theorem 1): a finitely generated projective
`R[X]`-module whose localization at every maximal ideal `m` of `R` is free over `Rₘ[X]` is
extended from a finitely generated projective `R`-module. -/
def H2 : Prop :=
  ∀ (R : Type) [CommRing R]
    (P : Type) [AddCommGroup P] [Module (Polynomial R) P]
    [Module.Finite (Polynomial R) P] [Module.Projective (Polynomial R) P],
    (∀ (m : Ideal R) [m.IsMaximal],
      Module.Free (Localization (Algebra.algebraMapSubmonoid (Polynomial R) m.primeCompl))
        (LocalizedModule (Algebra.algebraMapSubmonoid (Polynomial R) m.primeCompl) P)) →
    ∃ (M : Type) (_ : AddCommGroup M) (_ : Module R M),
      Module.Finite R M ∧ Module.Projective R M ∧
      Nonempty (P ≃ₗ[Polynomial R] Polynomial R ⊗[R] M)

lemma moduleFinite_compHom {R S : Type} [CommRing R] [CommRing S] (e : R ≃+* S)
    (P : Type) [AddCommGroup P] [Module S P] [hfin : Module.Finite S P] :
    let _ : Module R P := Module.compHom P e.toRingHom
    Module.Finite R P := by
  let _ : Module R P := Module.compHom P e.toRingHom
  obtain ⟨t, ht⟩ := hfin.fg_top
  refine ⟨⟨t, ?_⟩⟩
  rw [eq_top_iff]
  intro x _
  have hx : x ∈ Submodule.span S (t : Set P) := by rw [ht]; trivial
  refine Submodule.span_induction (fun y hy => Submodule.subset_span hy)
    (Submodule.zero_mem _) (fun _ _ _ _ ih1 ih2 => Submodule.add_mem _ ih1 ih2)
    (fun s y _ ih => ?_) hx
  have hsmul : s • y = (e.symm s) • y := by
    change s • y = e (e.symm s) • y
    simp
  rw [hsmul]
  exact Submodule.smul_mem _ (e.symm s) ih

lemma moduleProjective_compHom {R S : Type} [CommRing R] [CommRing S] (e : R ≃+* S)
    (P : Type) [AddCommGroup P] [Module S P] [Module.Finite S P] [Module.Projective S P] :
    let _ : Module R P := Module.compHom P e.toRingHom
    Module.Projective R P := by
  let _ : Module R P := Module.compHom P e.toRingHom
  obtain ⟨k, f, g, _, _, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective S P
  let f' : (Fin k → R) →ₗ[R] P :=
    { toFun := fun v => f (fun i => e (v i))
      map_add' := fun v w => by
        have : (fun i => e ((v + w) i)) = (fun i => e (v i)) + (fun i => e (w i)) := by
          ext i; simp [map_add]
        rw [this, map_add]
      map_smul' := fun r v => by
        have : (fun i => e ((r • v) i)) = e r • (fun i => e (v i)) := by
          ext i; simp [map_mul]
        rw [this, map_smul]; rfl }
  let g' : P →ₗ[R] (Fin k → R) :=
    { toFun := fun x i => e.symm (g x i)
      map_add' := fun x y => by ext i; simp [map_add]
      map_smul' := fun r x => by
        ext i
        change e.symm (g (e r • x) i) = r * e.symm (g x i)
        rw [map_smul, Pi.smul_apply, smul_eq_mul, map_mul, RingEquiv.symm_apply_apply] }
  refine Module.Projective.of_split g' f' ?_
  ext x
  change f (fun i => e (e.symm (g x i))) = x
  have : (fun i => e (e.symm (g x i))) = g x := by ext i; simp
  rw [this]
  exact congrArg (fun h => h x) hfg

lemma moduleFree_of_compHom {R S : Type} [CommRing R] [CommRing S] (e : R ≃+* S)
    (P : Type) [AddCommGroup P] [Module S P] :
    (let _ : Module R P := Module.compHom P e.toRingHom; Module.Free R P) → Module.Free S P := by
  intro hfree
  let _ : Module R P := Module.compHom P e.toRingHom
  let b := Module.Free.chooseBasis R P
  let ι := Module.Free.ChooseBasisIndex R P
  let eP : P ≃ₗ[S] (ι →₀ S) :=
    { toFun := fun x => (b.repr x).mapRange e (map_zero e)
      invFun := fun v => b.repr.symm (v.mapRange e.symm (map_zero e.symm))
      left_inv := fun x => by
        dsimp only
        have h : ((b.repr x).mapRange e (map_zero e)).mapRange e.symm (map_zero e.symm) = b.repr x := by
          ext i; simp
        rw [h, LinearEquiv.symm_apply_apply]
      right_inv := fun v => by
        dsimp only
        rw [LinearEquiv.apply_symm_apply]
        ext i; simp
      map_add' := fun x y => by
        rw [map_add]
        ext i; simp [map_add]
      map_smul' := fun s x => by
        have hsmul : s • x = (e.symm s) • x := by
          change s • x = e (e.symm s) • x; simp
        rw [hsmul, map_smul]
        ext i
        simp [map_mul] }
  exact Module.Free.of_equiv eP.symm

lemma localizedModule_finite {R : Type} [CommRing R] (S : Submonoid R)
    (P : Type) [AddCommGroup P] [Module R P] [Module.Finite R P] :
    Module.Finite (Localization S) (LocalizedModule S P) := by
  let e := (LocalizedModule.equivTensorProduct S P).symm
  exact Module.Finite.equiv e

lemma baseChange_free_of_localized_free {R₁ L₂ : Type} [CommRing R₁] [CommRing L₂]
    (S₁ : Submonoid R₁) (g : R₁ →+* L₂) (hg : ∀ s ∈ S₁, IsUnit (g s))
    (P : Type) [AddCommGroup P] [Module R₁ P]
    (hfree : Module.Free (Localization S₁) (LocalizedModule S₁ P)) :
    let _ : Algebra R₁ L₂ := g.toAlgebra
    Module.Free L₂ (L₂ ⊗[R₁] P) := by
  let _ : Algebra R₁ L₂ := g.toAlgebra
  let φ : Localization S₁ →+* L₂ := IsLocalization.lift (M := S₁) (S := Localization S₁) (g := g)
    (fun s => hg s.1 s.2)
  let _ : Algebra (Localization S₁) L₂ := φ.toAlgebra
  have _ : IsScalarTower R₁ (Localization S₁) L₂ :=
    IsScalarTower.of_algebraMap_eq fun r => by
      change g r = φ (algebraMap R₁ (Localization S₁) r)
      exact (IsLocalization.lift_eq (M := S₁) (S := Localization S₁) _ r).symm
  let e1 : L₂ ⊗[Localization S₁] (Localization S₁ ⊗[R₁] P) ≃ₗ[L₂] L₂ ⊗[R₁] P :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange R₁ (Localization S₁) L₂ L₂ P
  let e2 : Localization S₁ ⊗[R₁] P ≃ₗ[Localization S₁] LocalizedModule S₁ P :=
    (LocalizedModule.equivTensorProduct S₁ P).symm
  have _ : Module.Free (Localization S₁) (Localization S₁ ⊗[R₁] P) :=
    Module.Free.of_equiv e2.symm
  have _ : Module.Free L₂ (L₂ ⊗[Localization S₁] (Localization S₁ ⊗[R₁] P)) :=
    Module.Free.of_basis ((Module.Free.chooseBasis (Localization S₁) _).baseChange L₂)
  exact Module.Free.of_equiv e1

lemma baseChange_ringEquiv_free {R₁ R₂ L₂ : Type} [CommRing R₁] [CommRing R₂] [CommRing L₂]
    [Algebra R₂ L₂] (e : R₁ ≃+* R₂)
    (P : Type) [AddCommGroup P] [Module R₁ P]
    (hfree : let _ : Algebra R₁ L₂ := ((algebraMap R₂ L₂).comp e.toRingHom).toAlgebra;
      Module.Free L₂ (L₂ ⊗[R₁] P)) :
    let _ : Module R₂ P := Module.compHom P e.symm.toRingHom
    Module.Free L₂ (L₂ ⊗[R₂] P) := by
  let _ : Algebra R₁ L₂ := ((algebraMap R₂ L₂).comp e.toRingHom).toAlgebra
  let _ : Module R₂ P := Module.compHom P e.symm.toRingHom
  let toF : (L₂ ⊗[R₁] P) →ₗ[L₂] (L₂ ⊗[R₂] P) :=
    TensorProduct.AlgebraTensorModule.lift
      { toFun := fun l =>
          { toFun := fun x => l ⊗ₜ[R₂] x
            map_add' := fun x y => TensorProduct.tmul_add l x y
            map_smul' := fun r x => by
              change l ⊗ₜ[R₂] (r • x) = (algebraMap R₂ L₂ (e r) • l) ⊗ₜ[R₂] x
              have hr : r • x = (e r : R₂) • x := by
                change r • x = (e.symm (e r)) • x; simp
              rw [hr, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def]
              rfl }
        map_add' := fun l₁ l₂ => by ext x; exact TensorProduct.add_tmul l₁ l₂ x
        map_smul' := fun a l => by ext x; rfl }
  let invF : (L₂ ⊗[R₂] P) →ₗ[L₂] (L₂ ⊗[R₁] P) :=
    TensorProduct.AlgebraTensorModule.lift
      { toFun := fun l =>
          { toFun := fun x => l ⊗ₜ[R₁] x
            map_add' := fun x y => TensorProduct.tmul_add l x y
            map_smul' := fun s x => by
              change l ⊗ₜ[R₁] ((e.symm s) • x) = s • (l ⊗ₜ[R₁] x)
              rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul']
              congr 1
              rw [Algebra.smul_def, Algebra.smul_def]
              change (algebraMap R₂ L₂ (e (e.symm s))) * l = algebraMap R₂ L₂ s * l
              simp }
        map_add' := fun l₁ l₂ => by ext x; exact TensorProduct.add_tmul l₁ l₂ x
        map_smul' := fun a l => by ext x; rfl }
  let eqv : (L₂ ⊗[R₁] P) ≃ₗ[L₂] (L₂ ⊗[R₂] P) :=
    LinearEquiv.ofLinearMap toF invF
      (by
        apply LinearMap.ext; intro t
        induction t using TensorProduct.induction_on with
        | zero => simp
        | tmul l x => rfl
        | add u v ihu ihv => simp [map_add, ihu, ihv])
      (by
        apply LinearMap.ext; intro t
        induction t using TensorProduct.induction_on with
        | zero => simp
        | tmul l x => rfl
        | add u v ihu ihv => simp [map_add, ihu, ihv])
  exact Module.Free.of_equiv eqv

lemma localized_free_of_H1 (h1 : H1) (A : Type) [CommRing A] [IsRegularRing A] (n : ℕ)
    (P : Type) [AddCommGroup P] [Module (MvPolynomial (Fin n) A) P]
    [Module.Finite (MvPolynomial (Fin n) A) P]
    [Module.Projective (MvPolynomial (Fin n) A) P]
    (m : Ideal A) [m.IsMaximal] :
    Module.Free
      (Localization (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) A) m.primeCompl))
      (LocalizedModule (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) A) m.primeCompl) P) := by
  have _ : IsRegularLocalRing (Localization.AtPrime m) :=
    IsRegularRing.isRegularLocalRing_localization m
  let S_poly : Submonoid (MvPolynomial (Fin n) A) :=
    Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) A) m.primeCompl
  let L := Localization S_poly
  let PL := LocalizedModule S_poly P
  have _ : Module.Finite L PL := localizedModule_finite S_poly P
  let _ : Algebra (MvPolynomial (Fin n) A) (MvPolynomial (Fin n) (Localization.AtPrime m)) :=
    MvPolynomial.algebraMvPolynomial
  have hS : S_poly = m.primeCompl.map (MvPolynomial.C (σ := Fin n)) := rfl
  have _ : IsLocalization S_poly (MvPolynomial (Fin n) (Localization.AtPrime m)) := by
    rw [hS]
    exact MvPolynomial.isLocalization m.primeCompl (Localization.AtPrime m)
  let e : MvPolynomial (Fin n) (Localization.AtPrime m) ≃+* L :=
    (IsLocalization.algEquiv S_poly L (MvPolynomial (Fin n) (Localization.AtPrime m))).toRingEquiv.symm
  let _ : Module (MvPolynomial (Fin n) (Localization.AtPrime m)) PL := Module.compHom PL e.toRingHom
  have _ : Module.Finite (MvPolynomial (Fin n) (Localization.AtPrime m)) PL :=
    moduleFinite_compHom e PL
  have _ : Module.Projective (MvPolynomial (Fin n) (Localization.AtPrime m)) PL :=
    moduleProjective_compHom e PL
  have hfree : Module.Free (MvPolynomial (Fin n) (Localization.AtPrime m)) PL :=
    h1 (Localization.AtPrime m) n PL
  exact moduleFree_of_compHom e PL hfree

lemma extend_of_locally_free (h2 : H2) :
    ∀ (n : ℕ) (A : Type) [CommRing A]
      (P : Type) [AddCommGroup P] [Module (MvPolynomial (Fin n) A) P]
      [Module.Finite (MvPolynomial (Fin n) A) P]
      [Module.Projective (MvPolynomial (Fin n) A) P],
      (∀ (m : Ideal A) [m.IsMaximal],
        Module.Free
          (Localization (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) A) m.primeCompl))
          (LocalizedModule (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) A) m.primeCompl) P)) →
      ∃ (M : Type) (_ : AddCommGroup M) (_ : Module A M),
        Module.Finite A M ∧ Module.Projective A M ∧
        Nonempty (P ≃ₗ[MvPolynomial (Fin n) A] MvPolynomial (Fin n) A ⊗[A] M) := by
  intro n
  induction n with
  | zero =>
    intro A _ P _ _ _ _ _
    let e : MvPolynomial (Fin 0) A ≃ₐ[A] A := MvPolynomial.isEmptyAlgEquiv A (Fin 0)
    let hModA : Module A P := Module.compHom P e.symm.toRingHom
    have _ : IsScalarTower A (MvPolynomial (Fin 0) A) P :=
      IsScalarTower.of_algebraMap_smul fun a x => by
        change (e.symm a) • x = (algebraMap A (MvPolynomial (Fin 0) A) a) • x
        have ha : e.symm a = algebraMap A (MvPolynomial (Fin 0) A) a := e.symm.commutes a
        rw [ha]
    have hfin : Module.Finite A P := moduleFinite_compHom e.symm.toRingEquiv P
    have hproj : Module.Projective A P := moduleProjective_compHom e.symm.toRingEquiv P
    refine ⟨P, inferInstance, hModA, hfin, hproj, ⟨?_⟩⟩
    have heq_alg : ∀ p : MvPolynomial (Fin 0) A,
        p = algebraMap A (MvPolynomial (Fin 0) A) (e p) := fun p => by
      have h1 := e.symm_apply_apply p
      have h2 := e.symm.commutes (e p)
      change e.symm (e p) = algebraMap A (MvPolynomial (Fin 0) A) (e p) at h2
      exact h1.symm.trans h2
    let toF : P →ₗ[MvPolynomial (Fin 0) A] (MvPolynomial (Fin 0) A ⊗[A] P) :=
      { toFun := fun x => (1 : MvPolynomial (Fin 0) A) ⊗ₜ[A] x
        map_add' := fun x y => TensorProduct.tmul_add 1 x y
        map_smul' := fun p x => by
          have hpx : p • x = (e p : A) • x := by
            change p • x = (e.symm (e p)) • x
            simp
          rw [hpx, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, ← heq_alg p]
          rfl }
    let invF : (MvPolynomial (Fin 0) A ⊗[A] P) →ₗ[MvPolynomial (Fin 0) A] P :=
      TensorProduct.AlgebraTensorModule.lift
        { toFun := fun p =>
            { toFun := fun x => p • x
              map_add' := fun x y => smul_add p x y
              map_smul' := fun a x => by
                change p • (e.symm a • x) = e.symm a • (p • x)
                rw [smul_smul, smul_smul, mul_comm] }
          map_add' := fun p q => by ext x; exact add_smul p q x
          map_smul' := fun p q => by ext x; exact mul_smul p q x }
    exact LinearEquiv.ofLinearMap toF invF
      (by
        apply LinearMap.ext; intro t
        induction t using TensorProduct.induction_on with
        | zero => simp
        | tmul p x =>
          change (1 : MvPolynomial (Fin 0) A) ⊗ₜ[A] (p • x) = p ⊗ₜ[A] x
          have hpx : p • x = (e p : A) • x := by
            change p • x = (e.symm (e p)) • x; simp
          rw [hpx, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one,
            ← heq_alg p]
        | add u v ihu ihv => simp [map_add, ihu, ihv])
      (by
        apply LinearMap.ext; intro x
        change (1 : MvPolynomial (Fin 0) A) • x = x
        exact one_smul _ x)
  | succ n ih =>
    intro A _ P _ _ _ _ hloc
    let B := MvPolynomial (Fin n) A
    let R₁ := MvPolynomial (Fin (n + 1)) A
    let e : R₁ ≃ₐ[A] Polynomial B := MvPolynomial.finSuccEquiv A n
    let hModPB : Module (Polynomial B) P := Module.compHom P e.symm.toRingHom
    have _ : Module.Finite (Polynomial B) P := moduleFinite_compHom e.symm.toRingEquiv P
    have _ : Module.Projective (Polynomial B) P := moduleProjective_compHom e.symm.toRingEquiv P
    have hB_loc : ∀ (M_B : Ideal B) [M_B.IsMaximal],
        Module.Free (Localization (Algebra.algebraMapSubmonoid (Polynomial B) M_B.primeCompl))
          (LocalizedModule (Algebra.algebraMapSubmonoid (Polynomial B) M_B.primeCompl) P) := by
      intro M_B _
      let p : Ideal A := M_B.comap (algebraMap A B)
      have hp_prime : p.IsPrime := Ideal.IsPrime.comap (algebraMap A B)
      obtain ⟨m, hm_max, hpm⟩ := Ideal.exists_le_maximal p hp_prime.ne_top
      have _ : m.IsMaximal := hm_max
      let S_A := Algebra.algebraMapSubmonoid R₁ m.primeCompl
      let S_B := Algebra.algebraMapSubmonoid (Polynomial B) M_B.primeCompl
      let L_B := Localization S_B
      let g₂ : Polynomial B →+* L_B := algebraMap (Polynomial B) L_B
      have hg_units : ∀ s ∈ S_A, IsUnit ((g₂.comp e.toRingHom) s) := by
        rintro _ ⟨a, ha, rfl⟩
        have haB : algebraMap A B a ∈ M_B.primeCompl := fun hmem =>
          ha (hpm hmem)
        have heq : e.toRingHom (algebraMap A R₁ a) = algebraMap B (Polynomial B) (algebraMap A B a) := by
          change e (algebraMap A R₁ a) = Polynomial.C (algebraMap A B a)
          rw [e.commutes a]
          rfl
        change IsUnit (g₂ (e.toRingHom (algebraMap A R₁ a)))
        rw [heq]
        have hmemSB : algebraMap B (Polynomial B) (algebraMap A B a) ∈ S_B :=
          ⟨algebraMap A B a, haB, rfl⟩
        exact IsLocalization.map_units (M := S_B) L_B ⟨_, hmemSB⟩
      have hfree1 := baseChange_free_of_localized_free (R₁ := R₁) (L₂ := L_B) S_A
        (g₂.comp e.toRingHom) hg_units P (hloc m)
      have hfree2 : Module.Free L_B (L_B ⊗[Polynomial B] P) :=
        baseChange_ringEquiv_free (R₁ := R₁) (R₂ := Polynomial B) (L₂ := L_B)
          e.toRingEquiv P hfree1
      exact Module.Free.of_equiv (LocalizedModule.equivTensorProduct S_B P).symm
    obtain ⟨Q, hQgrp, hQmod, hQfin, hQproj, ⟨iso1⟩⟩ := h2 B P hB_loc
    let _ := hQgrp; let _ := hQmod; have _ := hQfin; have _ := hQproj
    have hQ_loc : ∀ (m : Ideal A) [m.IsMaximal],
        Module.Free (Localization (Algebra.algebraMapSubmonoid B m.primeCompl))
          (LocalizedModule (Algebra.algebraMapSubmonoid B m.primeCompl) Q) := by
      intro m _
      let S_A := Algebra.algebraMapSubmonoid R₁ m.primeCompl
      let S_Q := Algebra.algebraMapSubmonoid B m.primeCompl
      let L_Q := Localization S_Q
      let ev0 : Polynomial B →+* B := Polynomial.evalRingHom 0
      let g₂ : Polynomial B →+* L_Q := (algebraMap B L_Q).comp ev0
      have hg_units : ∀ s ∈ S_A, IsUnit ((g₂.comp e.toRingHom) s) := by
        rintro _ ⟨a, ha, rfl⟩
        have heq : ev0 (e.toRingHom (algebraMap A R₁ a)) = algebraMap A B a := by
          change Polynomial.eval 0 (e (algebraMap A R₁ a)) = algebraMap A B a
          rw [e.commutes a]
          change Polynomial.eval 0 (Polynomial.C (algebraMap A B a)) = algebraMap A B a
          exact Polynomial.eval_C
        change IsUnit (algebraMap B L_Q (ev0 (e.toRingHom (algebraMap A R₁ a))))
        rw [heq]
        have hmemSQ : algebraMap A B a ∈ S_Q := ⟨a, ha, rfl⟩
        exact IsLocalization.map_units (M := S_Q) L_Q ⟨_, hmemSQ⟩
      have hfree1 := baseChange_free_of_localized_free (R₁ := R₁) (L₂ := L_Q) S_A
        (g₂.comp e.toRingHom) hg_units P (hloc m)
      let _ : Algebra (Polynomial B) L_Q := g₂.toAlgebra
      have _ : IsScalarTower B (Polynomial B) L_Q :=
        IsScalarTower.of_algebraMap_eq fun b => by
          change algebraMap B L_Q b = algebraMap B L_Q (Polynomial.eval 0 (Polynomial.C b))
          rw [Polynomial.eval_C]
      have hfree2 : Module.Free L_Q (L_Q ⊗[Polynomial B] P) :=
        baseChange_ringEquiv_free (R₁ := R₁) (R₂ := Polynomial B) (L₂ := L_Q)
          e.toRingEquiv P hfree1
      let eqv1 : (L_Q ⊗[Polynomial B] P) ≃ₗ[L_Q] (L_Q ⊗[Polynomial B] (Polynomial B ⊗[B] Q)) :=
        LinearEquiv.ofLinearMap (iso1.toLinearMap.baseChange L_Q) (iso1.symm.toLinearMap.baseChange L_Q)
          (by rw [← LinearMap.baseChange_comp, LinearEquiv.comp_coe, LinearEquiv.symm_trans_self,
            LinearEquiv.refl_toLinearMap, LinearMap.baseChange_id])
          (by rw [← LinearMap.baseChange_comp, LinearEquiv.comp_coe, LinearEquiv.self_trans_symm,
            LinearEquiv.refl_toLinearMap, LinearMap.baseChange_id])
      let eqv2 : (L_Q ⊗[Polynomial B] (Polynomial B ⊗[B] Q)) ≃ₗ[L_Q] (L_Q ⊗[B] Q) :=
        TensorProduct.AlgebraTensorModule.cancelBaseChange B (Polynomial B) L_Q L_Q Q
      let eqv3 : (L_Q ⊗[B] Q) ≃ₗ[L_Q] LocalizedModule S_Q Q :=
        (LocalizedModule.equivTensorProduct S_Q Q).symm
      exact Module.Free.of_equiv ((eqv1.trans eqv2).trans eqv3)
    obtain ⟨M, hMgr, hMmod, hMfin, hMproj, ⟨iso2⟩⟩ := ih A Q hQ_loc
    let _ := hMgr; let _ := hMmod; have _ := hMfin; have _ := hMproj
    refine ⟨M, hMgr, hMmod, hMfin, hMproj, ⟨?_⟩⟩
    let iso2_bc : (Polynomial B ⊗[B] Q) ≃ₗ[Polynomial B] (Polynomial B ⊗[B] (B ⊗[A] M)) :=
      LinearEquiv.ofLinearMap (iso2.toLinearMap.baseChange (Polynomial B))
        (iso2.symm.toLinearMap.baseChange (Polynomial B))
        (by rw [← LinearMap.baseChange_comp, LinearEquiv.comp_coe, LinearEquiv.symm_trans_self,
          LinearEquiv.refl_toLinearMap, LinearMap.baseChange_id])
        (by rw [← LinearMap.baseChange_comp, LinearEquiv.comp_coe, LinearEquiv.self_trans_symm,
          LinearEquiv.refl_toLinearMap, LinearMap.baseChange_id])
    let iso12 : P ≃ₗ[Polynomial B] (Polynomial B ⊗[B] (B ⊗[A] M)) := iso1.trans iso2_bc
    let isoPB : P ≃ₗ[Polynomial B] (Polynomial B ⊗[A] M) :=
      iso12.trans (TensorProduct.AlgebraTensorModule.cancelBaseChange A B (Polynomial B) (Polynomial B) M)
    let eT : (Polynomial B ⊗[A] M) ≃ₗ[A] (R₁ ⊗[A] M) :=
      TensorProduct.congr e.symm.toLinearEquiv (LinearEquiv.refl A M)
    have heT_smul : ∀ (r : R₁) (t : Polynomial B ⊗[A] M), eT (e r • t) = r • eT t := by
      intro r t
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul f m =>
        change (e.symm (e r * f)) ⊗ₜ[A] m = (r * e.symm f) ⊗ₜ[A] m
        rw [map_mul, e.symm_apply_apply]
      | add x y ihx ihy => simp [smul_add, map_add, ihx, ihy]
    exact
      { toFun := fun x => eT (isoPB x)
        invFun := fun y => isoPB.symm (eT.symm y)
        left_inv := fun x => by simp
        right_inv := fun y => by simp
        map_add' := fun x y => by simp
        map_smul' := fun r x => by
          have hr : r • x = (e r : Polynomial B) • x := by
            change r • x = (e.symm (e r)) • x; simp
          change eT (isoPB (r • x)) = r • eT (isoPB x)
          rw [hr, isoPB.map_smul, heT_smul] }

theorem main : H1 → H2 → type_of% @OMA.S_wp_bass_quillen_conjecture.main := by
  intro h1 h2 A _ _ n r
  constructor
  · intro P _ _ ⟨hPfin, hPproj, hPrank⟩
    obtain ⟨M, hMgr, hMmod, hMfin, hMproj, ⟨e⟩⟩ :=
      extend_of_locally_free h2 n A P (fun m _ => localized_free_of_H1 h1 A n P m)
    let _ := hMgr; let _ := hMmod; have _ := hMfin; have _ := hMproj
    refine ⟨M, hMgr, hMmod, ⟨hMfin, hMproj, ?_⟩, ⟨e⟩⟩
    intro p
    let ev0 : MvPolynomial (Fin n) A →+* A := MvPolynomial.eval 0
    let q : PrimeSpectrum (MvPolynomial (Fin n) A) := p.comap ev0
    have hcomap : q.comap (algebraMap A (MvPolynomial (Fin n) A)) = p := by
      ext x
      change MvPolynomial.eval 0 (MvPolynomial.C x) ∈ p.asIdeal ↔ x ∈ p.asIdeal
      simp
    have h1eq : Module.rankAtStalk P q = Module.rankAtStalk (MvPolynomial (Fin n) A ⊗[A] M) q :=
      congrFun (Module.rankAtStalk_eq_of_equiv e) q
    have h2eq : Module.rankAtStalk (MvPolynomial (Fin n) A ⊗[A] M) q =
        Module.rankAtStalk M (q.comap (algebraMap A (MvPolynomial (Fin n) A))) :=
      Module.rankAtStalk_baseChange (R := A) (M := M) (S := MvPolynomial (Fin n) A) q
    rw [← hcomap, ← h2eq, ← h1eq]
    exact hPrank q
  · intro M N _ _ _ _ _ _ ⟨e⟩
    let ev0 : MvPolynomial (Fin n) A →+* A := MvPolynomial.eval 0
    let _ : Algebra (MvPolynomial (Fin n) A) A := ev0.toAlgebra
    have _ : IsScalarTower A (MvPolynomial (Fin n) A) A :=
      IsScalarTower.of_algebraMap_eq fun a => by
        change a = MvPolynomial.eval 0 (MvPolynomial.C a)
        exact (MvPolynomial.eval_C a).symm
    let ebc : (A ⊗[MvPolynomial (Fin n) A] (MvPolynomial (Fin n) A ⊗[A] M)) ≃ₗ[A]
        (A ⊗[MvPolynomial (Fin n) A] (MvPolynomial (Fin n) A ⊗[A] N)) :=
      LinearEquiv.ofLinearMap (e.toLinearMap.baseChange A) (e.symm.toLinearMap.baseChange A)
        (by rw [← LinearMap.baseChange_comp, LinearEquiv.comp_coe, LinearEquiv.symm_trans_self,
          LinearEquiv.refl_toLinearMap, LinearMap.baseChange_id])
        (by rw [← LinearMap.baseChange_comp, LinearEquiv.comp_coe, LinearEquiv.self_trans_symm,
          LinearEquiv.refl_toLinearMap, LinearMap.baseChange_id])
    let cM : (A ⊗[MvPolynomial (Fin n) A] (MvPolynomial (Fin n) A ⊗[A] M)) ≃ₗ[A] (A ⊗[A] M) :=
      TensorProduct.AlgebraTensorModule.cancelBaseChange A (MvPolynomial (Fin n) A) A A M
    let cN : (A ⊗[MvPolynomial (Fin n) A] (MvPolynomial (Fin n) A ⊗[A] N)) ≃ₗ[A] (A ⊗[A] N) :=
      TensorProduct.AlgebraTensorModule.cancelBaseChange A (MvPolynomial (Fin n) A) A A N
    exact ⟨((TensorProduct.lid A M).symm.trans cM.symm).trans
      (ebc.trans (cN.trans (TensorProduct.lid A N)))⟩

end OMA.R_wp_bass_quillen_conjecture_R1
