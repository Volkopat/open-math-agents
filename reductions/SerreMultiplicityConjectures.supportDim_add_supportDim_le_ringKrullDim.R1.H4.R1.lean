import OMAReductions.R_SerreMultiplicityConjectures_supportDim_add_supportDim_le_ringKrullDim_R1
import Mathlib

/-!
# Euler cancellation along a regular hypersurface

The change-of-rings long exact sequence gives maps between Tor over the ambient
ring and Tor over its hypersurface quotient. Exactness expresses each ambient
length as a sum of two consecutive terms. Their alternating sum telescopes.
The quotient by the sum of the two ideals is Artinian because it is supported
at the closed point. The remaining steps concern bounded finite-length Tor
over a regular local ring and the change-of-rings exact sequence itself.
-/
namespace OMA.R_SerreMultiplicityConjectures_supportDim_add_supportDim_le_ringKrullDim_R1_H4_R1
open Finset CategoryTheory MonoidalCategory
open scoped TensorProduct

/-- Euler cancellation for a bounded two-row spectral sequence with identical rows.
The numbers d(i) are the ranks (lengths of images) of the differentials from (i,0) to (i-2,1). -/
lemma two_rows (a b d : ℕ → ℤ) (N : ℕ) (hb : ∀ i ≥ N, b i = 0) (hd : ∀ i ≥ N, d i = 0)
    (start : a 0 = b 0 - d 1) (steps : ∀ i, a (i+1) = b (i+1)+b i-d (i+1)-d (i+2)) :
    ∑ᶠ i : ℕ, (-1:ℤ)^i*a i = 0 := by
  let c (i : ℕ) := b i - d (i+1)
  have recurrence (i : ℕ) : a (i+1) = c (i+1)+c i := by
    dsimp [c]
    rw [steps]
    ring
  have vanish (i : ℕ) (hi : N ≤ i) : c i=0 := by simp [c,hb i hi,hd (i+1) (by omega)]
  have partialSum (k : ℕ) : ∑ i ∈ range (k+1), (-1:ℤ)^i*a i = (-1:ℤ)^k*c k := by
    induction k with
    | zero => simpa [c] using start
    | succ k ih =>
      rw [sum_range_succ,ih,recurrence,pow_succ]
      ring
  rw [finsum_eq_sum_of_support_subset (s := range (N+1))]
  · rw [partialSum,vanish N le_rfl,mul_zero]
  · intro i hi
    by_contra hn
    have idx : N < i := by simpa using hn
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
    exact hi (by change (-1:ℤ)^(j+1)*a (j+1)=0; rw [recurrence,vanish j (by omega),vanish (j+1) (by omega)]; simp)

/-- The degree zero identification fixes the initial term in the Euler sum. -/
lemma tor_zero_length {S : Type} [CommRing S] (P Q : Ideal S) :
    Module.length S (((Tor (ModuleCat S) 0).obj (ModuleCat.of S (S ⧸ P))).obj
      (ModuleCat.of S (S ⧸ Q))) = Module.length S (S ⧸ (P ⊔ Q)) := by
  let e : ((Tor (ModuleCat S) 0).obj (ModuleCat.of S (S ⧸ P))).obj (ModuleCat.of S (S ⧸ Q)) ≅
      ModuleCat.of S (S ⧸ P) ⊗ ModuleCat.of S (S ⧸ Q) :=
    ((tensoringLeft (ModuleCat S)).obj _).leftDerivedZeroIsoSelf.app _
  rw [e.toLinearEquiv.length_eq]
  let t := (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (S ⧸ P) Q).symm
  exact ((t.toLinearEquiv.restrictScalars S).trans
    ((DoubleQuot.quotQuotEquivQuotSupₐ S P Q).toLinearEquiv)).length_eq

/-- A quotient supported at the closed point of a noetherian local ring has finite length. -/
lemma length_finite {S : Type} [CommRing S] [IsNoetherianRing S] [IsLocalRing S]
    (I : Ideal S) (rad : I.radical = IsLocalRing.maximalIdeal S) :
    Module.length S (S ⧸ I) ≠ ⊤ := by
  have minimal : IsLocalRing.maximalIdeal S ∈ I.minimalPrimes := by
    refine ⟨⟨inferInstance,rad ▸ I.le_radical⟩,?_⟩
    intro J hJ _
    have h := Ideal.radical_mono hJ.2
    rwa [rad,hJ.1.radical] at h
  letI := IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing I minimal
  haveI : IsArtinian S (S ⧸ I) := isArtinian_of_surjective_algebraMap (Ideal.Quotient.mk_surjective (I := I))
  exact Module.length_ne_top

lemma length_zero_finite {S : Type} [CommRing S] [IsNoetherianRing S] [IsLocalRing S]
    (P Q : Ideal S) (rad : (P ⊔ Q).radical = IsLocalRing.maximalIdeal S) :
    Module.length S (((Tor (ModuleCat S) 0).obj (ModuleCat.of S (S ⧸ P))).obj
      (ModuleCat.of S (S ⧸ Q))) ≠ ⊤ := by
  rw [tor_zero_length]
  exact length_finite _ rad

lemma split_length {S : Type} [CommRing S] {U V W : Type}
    [AddCommGroup U] [Module S U] [AddCommGroup V] [Module S V] [AddCommGroup W] [Module S W]
    (f : U →ₗ[S] V) (g : V →ₗ[S] W) (h : Function.Exact f g)
    (hf : IsFiniteLength S (LinearMap.range f)) (hg : IsFiniteLength S (LinearMap.range g)) :
    ((Module.length S V).toNat : ℤ) = ((Module.length S (LinearMap.range f)).toNat : ℤ) + (Module.length S (LinearMap.range g)).toNat := by
  have ex : Function.Exact (LinearMap.range f).subtype g.rangeRestrict := by
    rw [LinearMap.exact_iff,Submodule.range_subtype,LinearMap.ker_rangeRestrict]
    exact (LinearMap.exact_iff.mp h)
  have e := Module.length_eq_add_of_exact _ _ (Submodule.subtype_injective _) g.surjective_rangeRestrict ex
  simp only [e,ENat.toNat_add (Module.length_ne_top_iff.mpr hf) (Module.length_ne_top_iff.mpr hg),Nat.cast_add]

theorem change_euler {S : Type} [CommRing S] (A B : ℕ → ModuleCat.{0} S)
    (zeroEquiv : A 0 ≃ₗ[S] B 0)
    (fromQuot : ∀ i, B i →ₗ[S] A (i+1))
    (toQuot : ∀ i, A (i+1) →ₗ[S] B (i+1))
    (connect : ∀ i, B (i+2) →ₗ[S] B i)
    (atAmbient : ∀ i, Function.Exact (fromQuot i) (toQuot i))
    (atQuot : ∀ i, Function.Exact (toQuot (i+1)) (connect i))
    (atLower : ∀ i, Function.Exact (connect i) (fromQuot i))
    (ontoOne : Function.Surjective (toQuot 0)) (fin : ∀ i, IsFiniteLength S (B i))
    (hi : ∃ N, ∀ i ≥ N, Subsingleton (B i)) :
    ∑ᶠ i : ℕ, (-1:ℤ)^i * ((Module.length S (A i)).toNat : ℤ) = 0 := by
  let r (i : ℕ) := ((Module.length S (LinearMap.range (connect i))).toNat : ℤ)
  let d : ℕ → ℤ | 0 | 1 => 0 | i+2 => r i
  have sf (i) := (fin i).of_surjective (f := (fromQuot i).rangeRestrict) (fromQuot i).surjective_rangeRestrict
  have st (i) := (fin (i+1)).of_injective (f := (LinearMap.range (toQuot i)).subtype) (Submodule.subtype_injective _)
  have sc (i) := (fin i).of_injective (f := (LinearMap.range (connect i)).subtype) (Submodule.subtype_injective _)
  have a (i) := split_length (fromQuot i) (toQuot i) (atAmbient i) (sf i) (st i)
  have b (i) := split_length (toQuot (i+1)) (connect i) (atQuot i) (st (i+1)) (sc i)
  have c (i) := split_length (connect i) (fromQuot i) (atLower i) (sc i) (sf i)
  obtain ⟨N,hN⟩ := hi
  apply two_rows (b := fun i => ((Module.length S (B i)).toNat : ℤ)) (d := d) (N := N+2)
  · intro i h
    haveI := hN i (by omega)
    simp
  · intro i h
    obtain ⟨j,rfl⟩ : ∃ j, i = j+2 := ⟨i-2,by omega⟩
    haveI := hN j (by omega)
    simp [d,r]
  · simp only [d,sub_zero,zeroEquiv.length_eq]
  · intro i
    cases i with
    | zero =>
      have first : ((Module.length S (LinearMap.range (toQuot 0))).toNat : ℤ) = ((Module.length S (B 1)).toNat : ℤ) := by
        let e := LinearEquiv.ofBijective (LinearMap.range (toQuot 0)).subtype
          ⟨Subtype.val_injective, fun x => ⟨⟨x,ontoOne x⟩,rfl⟩⟩
        exact congrArg (fun n : ℕ∞ => (n.toNat:ℤ)) e.length_eq
      dsimp only [d,r]
      linarith only [a 0,c 0,first]
    | succ i =>
      dsimp only [d,r]
      linarith only [a (i+1),c (i+1),b i]

/-- Properly intersecting cyclic modules over a regular local ring have finite-length Tor,
and all sufficiently high Tor groups vanish. -/
def H1 : Prop := ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] (P Q : Ideal R),
    Module.length R (R ⧸ (P ⊔ Q)) ≠ ⊤ →
    let T := fun i => ((Tor (ModuleCat.{0} R) i).obj (ModuleCat.of R (R ⧸ P))).obj (ModuleCat.of R (R ⧸ Q))
    (∀ i, IsFiniteLength R (T i)) ∧ ∃ N, ∀ i ≥ N, Subsingleton (T i)

/-- The homological change-of-rings sequence for a regular parameter lying in both ideals. -/
def H2 : Prop := ∀ (S : Type) [CommRing S] [IsRegularLocalRing S]
    (g : S), g ∈ IsLocalRing.maximalIdeal S → g ≠ 0 → IsRegularLocalRing (S ⧸ Ideal.span {g}) →
    ∀ (P Q : Ideal S), g ∈ P → g ∈ Q →
    let f := Ideal.Quotient.mk (Ideal.span {g})
    let R := S ⧸ Ideal.span {g}
    let A := fun i => ((Tor (ModuleCat.{0} S) i).obj (ModuleCat.of S (S ⧸ P))).obj (ModuleCat.of S (S ⧸ Q))
    let B := fun i => (ModuleCat.restrictScalars f).obj (((Tor (ModuleCat.{0} R) i).obj (ModuleCat.of R (R ⧸ P.map f))).obj (ModuleCat.of R (R ⧸ Q.map f)))
    ∃ (zeroEquiv : A 0 ≃ₗ[S] B 0),
    ∃ (fromQuot : ∀ i, B i →ₗ[S] A (i+1)),
    ∃ (toQuot : ∀ i, A (i+1) →ₗ[S] B (i+1)),
    ∃ (connect : ∀ i, B (i+2) →ₗ[S] B i),
    (∀ i, Function.Exact (fromQuot i) (toQuot i)) ∧
    (∀ i, Function.Exact (toQuot (i+1)) (connect i)) ∧
    (∀ i, Function.Exact (connect i) (fromQuot i)) ∧
    (Function.Surjective (toQuot 0))

theorem main : H1 → H2 → OMA.R_SerreMultiplicityConjectures_supportDim_add_supportDim_le_ringKrullDim_R1.H4 := by
  intro h1 h2 S _ _ g hgm hg hreg P Q _ _ hgp hgq hr
  let I := Ideal.span {g}
  let f := Ideal.Quotient.mk I
  let R := S ⧸ I
  let P' := P.map f
  let Q' := Q.map f
  letI : IsRegularLocalRing R := hreg
  have sub : I ≤ P ⊔ Q := (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hgp)).trans le_sup_left
  have fin : Module.length R (R ⧸ (P' ⊔ Q')) ≠ ⊤ := by
    change Module.length (S ⧸ I) ((S ⧸ I) ⧸ (P.map f ⊔ Q.map f)) ≠ ⊤
    rw [← Ideal.map_sup,← Module.length_eq_of_surjective (S := S) (Ideal.Quotient.mk_surjective (I := I))]
    have e := (DoubleQuot.quotQuotEquivQuotSupₐ S I (P ⊔ Q)).toLinearEquiv.length_eq
    change Module.length S ((S ⧸ I) ⧸ (P ⊔ Q).map f) = _ at e
    rw [e,sup_eq_right.mpr sub]
    exact length_finite _ hr
  obtain ⟨finite,bdd⟩ := h1 R P' Q' fin
  obtain ⟨zeroEquiv, fromQuot, toQuot, connect, atAmbient, atQuot, atLower, ontoOne⟩ := h2 S g hgm hg hreg P Q hgp hgq
  let B := fun i => ((Tor (ModuleCat.{0} R) i).obj (ModuleCat.of R (R ⧸ P'))).obj (ModuleCat.of R (R ⧸ Q'))
  have fin' (i) : IsFiniteLength S ((ModuleCat.restrictScalars f).obj (B i)) := by
    rw [← Module.length_ne_top_iff]
    change Module.length S ((ModuleCat.restrictScalars f).obj (B i)) ≠ ⊤
    let M := B i
    change Module.length S ((ModuleCat.restrictScalars f).obj M) ≠ ⊤
    letI : Module S M := Module.compHom M f
    haveI : IsScalarTower S R M := ⟨fun s r m => by change (f s*r) • m = f s • (r • m); rw [mul_smul]⟩
    change Module.length S M ≠ ⊤
    rw [Module.length_eq_of_surjective (R := R) (Ideal.Quotient.mk_surjective (I := I))]
    exact Module.length_ne_top_iff.mpr (finite i)
  exact change_euler _ _ zeroEquiv fromQuot toQuot connect atAmbient atQuot atLower ontoOne fin' bdd

end OMA.R_SerreMultiplicityConjectures_supportDim_add_supportDim_le_ringKrullDim_R1_H4_R1
