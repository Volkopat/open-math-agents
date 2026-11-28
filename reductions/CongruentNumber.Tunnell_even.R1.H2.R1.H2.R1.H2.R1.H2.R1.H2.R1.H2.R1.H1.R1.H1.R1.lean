import OMAReductions.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H1_R1
import Mathlib


/-! The cyclic Herbrand quotient and the norm bound for prime-degree Kummer extensions imply both cyclic class-field conditions. Determinant norms descend through coprime cyclotomic base change and compose along the cyclic tower. -/

namespace OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H1_R1_H1_R1

section

open NumberField IsDedekindDomain
open scoped TensorProduct NumberField Classical

def H1 : Prop :=
  (
∀(D N:Type)[Field D][NumberField D][Field N][NumberField N][Algebra D N]
   [FiniteDimensional D N][IsGalois D N](g:Gal(N/D)),(∀ s,s∈Subgroup.zpowers g) →
   let A:=AdeleRing (𝓞 D) D
   let T:=A⊗[D]N
   let P:=(Units.map (algebraMap D A).toMonoidHom).range ⊔ (Units.map (Algebra.norm A (S:=T))).range
   let q:=QuotientGroup.mk' (Units.map (Algebra.TensorProduct.includeRight (R:=D) (A:=A) (B:=N)).toMonoidHom).range
   let a(s:Gal(N/D)):=Units.mapEquiv (Algebra.TensorProduct.congr (AlgEquiv.refl (R:=A) (A₁:=A)) s).toMulEquiv
   let n:=q.comp (∏ s:Gal(N/D),(a s).toMonoidHom)
   let b:=q.comp ((a g).toMonoidHom / MonoidHom.id Tˣ)
   let k:=b.range.relIndex (n.ker.map q)
   0<k ∧ P.index=Module.finrank D N*k
)

end

section

open NumberField IsDedekindDomain
open scoped TensorProduct NumberField Classical
open scoped NumberField TensorProduct Classical

def H2 : Prop :=
  (
∀ (D M:Type) [Field D] [NumberField D] [Field M] [NumberField M] [Algebra D M] [FiniteDimensional D M],
  let T:=AdeleRing (𝓞 D) D ⊗[D] M
  letI : Algebra M T:=Algebra.TensorProduct.rightAlgebra
  Nonempty (T≃ₐ[M]AdeleRing (𝓞 M) M)
) ∧
  (
∀(D:Type)[Field D][NumberField D](p:ℕ),p.Prime → (primitiveRoots p D).Nonempty →
   let V:=HeightOneSpectrum (𝓞 D)
   let A:=AdeleRing (𝓞 D) D
   let U(S T:Finset V):=Subgroup.closure {a:Aˣ |
     (∀ w:InfinitePlace D,∃ y:w.Completion,y^p=a.val.1 w) ∧
     (∀ v∈S,∃ y:v.adicCompletion D,y^p=a.val.2 v) ∧
     ∀ v:V,v∉S∪T → a.val.2 v∈v.adicCompletionIntegers D ∧ (a⁻¹).val.2 v∈v.adicCompletionIntegers D}
   let J(F:Finset V):=Subgroup.closure {a:Aˣ | ∀ v:V,v∉F → a.val.2 v∈v.adicCompletionIntegers D ∧ (a⁻¹).val.2 v∈v.adicCompletionIntegers D}
   ∀ S T:Finset V,(∀ v:V,v.asIdeal ∣ Ideal.span {(p:𝓞 D)} → v∈S) →
      (U S T).relIndex (J (S∪T))=p^(2*(Nat.card (InfinitePlace D)+S.card))
) ∧
  (
∀(D:Type)[Field D][NumberField D](p:ℕ),p.Prime → (primitiveRoots p D).Nonempty →
   ∀ F:Finset (HeightOneSpectrum (𝓞 D)),
     let E:=(F:Set (HeightOneSpectrum (𝓞 D))).unit D
     (powMonoidHom p:E→*E).range.index=p^(Nat.card (InfinitePlace D)+F.card)
)

end

section

open NumberField IsDedekindDomain
open scoped NumberField TensorProduct Classical

def H3 : Prop :=
  (
(∀(D N:Type)[Field D][NumberField D][Field N][NumberField N][Algebra D N]
    [FiniteDimensional D N][IsGalois D N][IsCyclic Gal(N/D)],
    let A:=AdeleRing (𝓞 D) D
    (Units.map (algebraMap D A).toMonoidHom).range ⊔ (Units.map (Algebra.norm A (S:=A⊗[D]N))).range=⊤ →
    Module.finrank D N=1) →
  ∀(D:Type)[Field D][NumberField D](E:IntermediateField D (SeparableClosure D))
   [FiniteDimensional D E][IsGalois D E],
   let p:=Module.finrank D E
   p.Prime → (primitiveRoots p D).Nonempty →
   letI:NumberField E:=NumberField.of_module_finite D E
   let V:=HeightOneSpectrum (𝓞 D)
   let A:=AdeleRing (𝓞 D) D
   let U(S T:Finset V):=Subgroup.closure {a:Aˣ |
     (∀ w:InfinitePlace D,∃ y:w.Completion,y^p=a.val.1 w) ∧
     (∀ v∈S,∃ y:v.adicCompletion D,y^p=a.val.2 v) ∧
     ∀ v:V,v∉S∪T → a.val.2 v∈v.adicCompletionIntegers D ∧ (a⁻¹).val.2 v∈v.adicCompletionIntegers D}
   let split(v:V):=∀ t:HeightOneSpectrum (𝓞 E),t.asIdeal.LiesOver v.asIdeal → ∀ g:Gal(E/D),
     HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapAlgEquiv g).toRingEquiv t=t → g=1
   let unram(v:V):=∀ t:HeightOneSpectrum (𝓞 E),t.asIdeal.LiesOver v.asIdeal → Algebra.IsUnramifiedAt (𝓞 D) t.asIdeal
   let J(F:Finset V):=Subgroup.closure {a:Aˣ | ∀ v:V,v∉F → a.val.2 v∈v.adicCompletionIntegers D ∧ (a⁻¹).val.2 v∈v.adicCompletionIntegers D}
   let j:=Units.map (algebraMap D A).toMonoidHom
   ∃ S T:Finset V, (∀ v∈T,split v) ∧ (∀ v:V,v∉S∪T → unram v) ∧ Disjoint S T ∧
     T.card+1=Nat.card (InfinitePlace D)+S.card ∧ (∀ v:V,v.asIdeal ∣ Ideal.span {(p:𝓞 D)} → v∈S) ∧
     j.range⊔J (S∪T)=⊤ ∧ let E:=(↑(S∪T):Set V).unit D
     (J (S∪T)).comap j=E ∧ (U S T).comap j=(powMonoidHom p:E→*E).range.map E.subtype
)

end

section

open NumberField IsDedekindDomain
open scoped NumberField TensorProduct Classical

def H4 : Prop :=
  (
∀(D:Type)[Field D][NumberField D](E:IntermediateField D (SeparableClosure D))
   [FiniteDimensional D E][IsGalois D E],
   let p:=Module.finrank D E
   p.Prime → (primitiveRoots p D).Nonempty →
   letI:NumberField E:=NumberField.of_module_finite D E
   let V:=HeightOneSpectrum (𝓞 D)
   let A:=AdeleRing (𝓞 D) D
   let U(S T:Finset V):=Subgroup.closure {a:Aˣ |
     (∀ w:InfinitePlace D,∃ y:w.Completion,y^p=a.val.1 w) ∧
     (∀ v∈S,∃ y:v.adicCompletion D,y^p=a.val.2 v) ∧
     ∀ v:V,v∉S∪T → a.val.2 v∈v.adicCompletionIntegers D ∧ (a⁻¹).val.2 v∈v.adicCompletionIntegers D}
   let split(v:V):=∀ t:HeightOneSpectrum (𝓞 E),t.asIdeal.LiesOver v.asIdeal → ∀ g:Gal(E/D),
     HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapAlgEquiv g).toRingEquiv t=t → g=1
   let unram(v:V):=∀ t:HeightOneSpectrum (𝓞 E),t.asIdeal.LiesOver v.asIdeal → Algebra.IsUnramifiedAt (𝓞 D) t.asIdeal
   ∀ S T:Finset V, (∀ v∈T,split v) → (∀ v:V,v∉S∪T → unram v) →
     U S T ≤ (Units.map (Algebra.norm A (S:=A⊗[D]E))).range
)

end

end OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H1_R1_H1_R1

section
open NumberField IsDedekindDomain
open scoped NumberField Classical TensorProduct IsMulCommutative
open scoped TensorProduct NumberField Classical

 
namespace OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H1_R1_H1_R1
open NumberField IsDedekindDomain
open scoped TensorProduct NumberField Classical
noncomputable section




theorem tower_dvd {X Y Z : Type*} [CommGroup X] [CommGroup Y] [CommGroup Z]
    (f : Y →* X) (g : Z →* Y) (A : Subgroup X) (B : Subgroup Y)
    (hB : B.map f ≤ A) :
    (A ⊔ (f.comp g).range).index ∣ (B ⊔ g.range).index * (A ⊔ f.range).index := by
  let L := A ⊔ (f.comp g).range
  let M := A ⊔ f.range
  have hf : (f.comp g).range ≤ f.range := by rintro _ ⟨z,rfl⟩; exact ⟨g z,rfl⟩
  have hlm : L ≤ M := sup_le_sup_left hf A
  have hm : L ⊔ f.range=M := by change (A ⊔ _) ⊔ _ = _; rw [sup_assoc,sup_eq_right.mpr hf]
  have hi : (L.comap f).index = L.relIndex M := by rw [Subgroup.index_comap,←hm,Subgroup.relIndex_sup_left]
  have hsub : B ⊔ g.range ≤ L.comap f := by
    apply sup_le
    · exact Subgroup.map_le_iff_le_comap.mp (hB.trans le_sup_left)
    · rintro _ ⟨z,rfl⟩
      exact (show (f.comp g).range ≤ L from le_sup_right) ⟨z,rfl⟩
  change L.index ∣ _ * M.index
  rw [←Subgroup.relIndex_mul_index hlm]
  rw [← hi]
  exact Nat.mul_dvd_mul (Subgroup.index_dvd_of_le hsub) dvd_rfl

section Tower
variable (K M L : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Field L] [NumberField L]
  [Algebra K M] [Algebra M L] [Algebra K L] [IsScalarTower K M L]
  [FiniteDimensional K M] [FiniteDimensional M L]
theorem norm_data (base : (
∀ (D M:Type) [Field D] [NumberField D] [Field M] [NumberField M] [Algebra D M] [FiniteDimensional D M],
  let T:=AdeleRing (𝓞 D) D ⊗[D] M
  letI : Algebra M T:=Algebra.TensorProduct.rightAlgebra
  Nonempty (T≃ₐ[M]AdeleRing (𝓞 M) M)
)) :
    ∃ (j : ((AdeleRing (𝓞 K) K))ˣ →* ((AdeleRing (𝓞 M) M))ˣ) (f : ((AdeleRing (𝓞 M) M))ˣ →* ((AdeleRing (𝓞 K) K))ˣ),
      (∀ x, f (j x) = x ^ Module.finrank K M) ∧ f.range = ((Units.map (Algebra.norm (AdeleRing (𝓞 K) K) (S:=(AdeleRing (𝓞 K) K) ⊗[K] M)))).range ∧
      ((Units.map (algebraMap M (AdeleRing (𝓞 M) M)).toMonoidHom)).range.map f ≤ ((Units.map (algebraMap K (AdeleRing (𝓞 K) K)).toMonoidHom)).range ∧ (f.comp ((Units.map (Algebra.norm (AdeleRing (𝓞 M) M) (S:=(AdeleRing (𝓞 M) M) ⊗[M] L))))).range = ((Units.map (Algebra.norm (AdeleRing (𝓞 K) K) (S:=(AdeleRing (𝓞 K) K) ⊗[K] L)))).range := by
  letI : Algebra M (((AdeleRing (𝓞 K) K) ⊗[K] M)) := Algebra.TensorProduct.rightAlgebra
  letI : Nontrivial ((AdeleRing (𝓞 K) K)) := (AdeleRing.algebraMap_injective (R:=𝓞 K) (K:=K)).nontrivial
  let R := (AdeleRing (𝓞 K) K)
  let T := ((AdeleRing (𝓞 K) K) ⊗[K] M)
  let W := T ⊗[M] L
  letI : Algebra L W := Algebra.TensorProduct.rightAlgebra
  letI : Algebra L (R ⊗[K] L) := Algebra.TensorProduct.rightAlgebra
  let e₁ := (Algebra.TensorProduct.commRight M L T).symm
  let e₂ := Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[M] L)
    (Algebra.TensorProduct.commRight K M R).symm
  let e₃ := Algebra.TensorProduct.cancelBaseChange K M L L R
  let e₄ := Algebra.TensorProduct.commRight K L R
  let eflat : W ≃ₐ[R] R ⊗[K] L := { e₁.toRingEquiv.trans (e₂.toRingEquiv.trans
      (e₃.toRingEquiv.trans e₄.toRingEquiv)) with
    commutes' := by
      intro a
      change e₄ (e₃ (e₂ (e₁ ((a ⊗ₜ[K] (1:M)) ⊗ₜ[M] (1:L))))) = a ⊗ₜ[K] (1:L)
      simp [e₁,e₂,e₃,e₄] }
  let flat := Units.mapEquiv eflat.toMulEquiv
  let e := (base K M).some
  let u := Units.mapEquiv e.toMulEquiv
  let E := Algebra.TensorProduct.congr e (AlgEquiv.refl (R:=M) (A₁:=L))
  let U := Units.mapEquiv E.toMulEquiv
  let f := ((Units.map (Algebra.norm (AdeleRing (𝓞 K) K) (S:=(AdeleRing (𝓞 K) K) ⊗[K] M)))).comp u.symm.toMonoidHom
  let g := (Units.map (Algebra.norm (AdeleRing (𝓞 M) M) (S:=(AdeleRing (𝓞 M) M) ⊗[M] L)))
  have hB : ((Units.map (algebraMap M (AdeleRing (𝓞 M) M)).toMonoidHom)).range.map f ≤ ((Units.map (algebraMap K (AdeleRing (𝓞 K) K)).toMonoidHom)).range := by
    rintro _ ⟨_,⟨m,rfl⟩,rfl⟩
    refine ⟨Units.map (Algebra.norm K) m,?_⟩
    apply Units.ext
    change algebraMap K ((AdeleRing (𝓞 K) K)) (Algebra.norm K (m:M)) = Algebra.norm ((AdeleRing (𝓞 K) K)) (e.symm (algebraMap M ((AdeleRing (𝓞 M) M)) (m:M)))
    rw [e.symm.commutes]
    exact by
      symm
      classical
      let b := Module.Free.chooseBasis K M
      let bA := b.baseChange ((AdeleRing (𝓞 K) K))
      rw [Algebra.norm_eq_matrix_det bA,Algebra.norm_eq_matrix_det b,(algebraMap K ((AdeleRing (𝓞 K) K))).map_det]
      congr 1
      ext i j
      simp [bA,b,Algebra.smul_def,Algebra.leftMulMatrix_eq_repr_mul,
        Algebra.TensorProduct.right_algebraMap_apply,Algebra.TensorProduct.tmul_mul_tmul]
  have hr : f.range=((Units.map (Algebra.norm (AdeleRing (𝓞 K) K) (S:=(AdeleRing (𝓞 K) K) ⊗[K] M)))).range := by
    ext x
    constructor
    · rintro ⟨y,rfl⟩;exact ⟨u.symm y,rfl⟩
    · rintro ⟨y,rfl⟩;exact ⟨u y,congrArg ((Units.map (Algebra.norm (AdeleRing (𝓞 K) K) (S:=(AdeleRing (𝓞 K) K) ⊗[K] M)))) (u.symm_apply_apply y)⟩
  have normU (z : Wˣ) : f (g (U z)) =
      (Units.map (Algebra.norm (AdeleRing (𝓞 K) K) (S:=(AdeleRing (𝓞 K) K) ⊗[K] L))) (flat z) := by
    have hcompat : (algebraMap ((AdeleRing (𝓞 M) M)) (((AdeleRing (𝓞 M) M) ⊗[M] L))).comp e.toRingHom =
        E.toRingHom.comp (algebraMap (((AdeleRing (𝓞 K) K) ⊗[K] M)) (W)) := by
      apply DFunLike.ext _ _
      intro x
      change e x ⊗ₜ[M] (1:L) = E (x ⊗ₜ[M] (1:L))
      rfl
    have ht := Algebra.norm_eq_of_equiv_equiv e.toRingEquiv E.toRingEquiv hcompat z.val
    apply Units.ext
    change Algebra.norm ((AdeleRing (𝓞 K) K)) (e.symm (Algebra.norm ((AdeleRing (𝓞 M) M)) (E z.val))) =
      Algebra.norm ((AdeleRing (𝓞 K) K)) (eflat z.val)
    exact (congrArg (Algebra.norm ((AdeleRing (𝓞 K) K))) ht.symm).trans
      (Algebra.norm_norm.trans (Algebra.norm_eq_of_algEquiv (eflat) z.val).symm)
  have hfg : (f.comp g).range=((Units.map (Algebra.norm (AdeleRing (𝓞 K) K) (S:=(AdeleRing (𝓞 K) K) ⊗[K] L)))).range := by
    ext x
    constructor
    · rintro ⟨y,rfl⟩
      obtain ⟨z,rfl⟩ := U.surjective y
      exact ⟨_,(normU z).symm⟩
    · rintro ⟨y,rfl⟩
      obtain ⟨z,rfl⟩ := (flat).surjective y
      exact ⟨_,normU z⟩
  let j := u.toMonoidHom.comp (Units.map (algebraMap ((AdeleRing (𝓞 K) K)) (((AdeleRing (𝓞 K) K) ⊗[K] M))).toMonoidHom)
  refine ⟨j,f,?_,hr,hB,hfg⟩
  intro x
  change (Units.map (Algebra.norm (AdeleRing (𝓞 K) K) (S:=(AdeleRing (𝓞 K) K) ⊗[K] M))) (u.symm (u _))=_
  rw [u.symm_apply_apply]
  apply Units.ext
  change Algebra.norm ((AdeleRing (𝓞 K) K)) (algebraMap ((AdeleRing (𝓞 K) K)) ((AdeleRing (𝓞 K) K) ⊗[K] M) x.val)=x.val^_
  rw [Algebra.norm_algebraMap,Module.finrank_baseChange]

theorem norm_tower (base : (
∀ (D M:Type) [Field D] [NumberField D] [Field M] [NumberField M] [Algebra D M] [FiniteDimensional D M],
  let T:=AdeleRing (𝓞 D) D ⊗[D] M
  letI : Algebra M T:=Algebra.TensorProduct.rightAlgebra
  Nonempty (T≃ₐ[M]AdeleRing (𝓞 M) M)
)) : ((Units.map (algebraMap K (AdeleRing (𝓞 K) K)).toMonoidHom).range ⊔ (Units.map (Algebra.norm (AdeleRing (𝓞 K) K) (S:=(AdeleRing (𝓞 K) K) ⊗[K] L))).range).index ∣ ((Units.map (algebraMap M (AdeleRing (𝓞 M) M)).toMonoidHom).range ⊔ (Units.map (Algebra.norm (AdeleRing (𝓞 M) M) (S:=(AdeleRing (𝓞 M) M) ⊗[M] L))).range).index * ((Units.map (algebraMap K (AdeleRing (𝓞 K) K)).toMonoidHom).range ⊔ (Units.map (Algebra.norm (AdeleRing (𝓞 K) K) (S:=(AdeleRing (𝓞 K) K) ⊗[K] M))).range).index := by
  obtain ⟨_,f,_,hr,hB,hfg⟩ := norm_data K M L base
  simpa only [hr,hfg] using tower_dvd f ((Units.map (Algebra.norm (AdeleRing (𝓞 M) M) (S:=(AdeleRing (𝓞 M) M) ⊗[M] L)))) ((Units.map (algebraMap K (AdeleRing (𝓞 K) K)).toMonoidHom)).range ((Units.map (algebraMap M (AdeleRing (𝓞 M) M)).toMonoidHom)).range hB

end Tower
theorem coprime_mem {X : Type*} [CommGroup X] (H:Subgroup X) (x:X) {d p:ℕ} (hc:d.Coprime p)
    (hm:x^d∈H) (hn:x^p∈H): x∈H := by
  let q:=QuotientGroup.mk' H
  have hd : orderOf (q x) ∣ d := orderOf_dvd_of_pow_eq_one (by rw [←map_pow];exact (QuotientGroup.eq_one_iff _).mpr hm)
  have hp : orderOf (q x) ∣ p := orderOf_dvd_of_pow_eq_one (by rw [←map_pow];exact (QuotientGroup.eq_one_iff _).mpr hn)
  exact (QuotientGroup.eq_one_iff _).mp (orderOf_eq_one_iff.mp (Nat.dvd_one.mp (hc.gcd_eq_one ▸ Nat.dvd_gcd hd hp)))
theorem coprime_index (base : (
∀ (D M:Type) [Field D] [NumberField D] [Field M] [NumberField M] [Algebra D M] [FiniteDimensional D M],
  let T:=AdeleRing (𝓞 D) D ⊗[D] M
  letI : Algebra M T:=Algebra.TensorProduct.rightAlgebra
  Nonempty (T≃ₐ[M]AdeleRing (𝓞 M) M)
)) (K M L N : Type) [Field K] [NumberField K]
    [Field M] [NumberField M] [Field L] [NumberField L] [Field N] [NumberField N]
    [Algebra K L] [Algebra K M] [Algebra L N] [Algebra M N] [Algebra K N]
    [IsScalarTower K L N] [IsScalarTower K M N] [FiniteDimensional K L] [FiniteDimensional K M]
    [FiniteDimensional L N] [FiniteDimensional M N] (hc:(Module.finrank K M).Coprime (Module.finrank K L)) :
    ((Units.map (algebraMap K (AdeleRing (𝓞 K) K)).toMonoidHom).range ⊔ (Units.map (Algebra.norm (AdeleRing (𝓞 K) K) (S:=(AdeleRing (𝓞 K) K) ⊗[K] L))).range).index ∣ ((Units.map (algebraMap M (AdeleRing (𝓞 M) M)).toMonoidHom).range ⊔ (Units.map (Algebra.norm (AdeleRing (𝓞 M) M) (S:=(AdeleRing (𝓞 M) M) ⊗[M] N))).range).index := by
  letI : Nontrivial ((AdeleRing (𝓞 K) K)) := (AdeleRing.algebraMap_injective (R:=𝓞 K) (K:=K)).nontrivial
  obtain ⟨j,f,hpow,_,hf,hfg⟩ := norm_data K M N base
  obtain ⟨_,f',_,hr',_,he'⟩ := norm_data K L N base
  have hm : (((Units.map (algebraMap M (AdeleRing (𝓞 M) M)).toMonoidHom).range ⊔ (Units.map (Algebra.norm (AdeleRing (𝓞 M) M) (S:=(AdeleRing (𝓞 M) M) ⊗[M] N))).range)).map f ≤ ((Units.map (algebraMap K (AdeleRing (𝓞 K) K)).toMonoidHom).range ⊔ (Units.map (Algebra.norm (AdeleRing (𝓞 K) K) (S:=(AdeleRing (𝓞 K) K) ⊗[K] N))).range) := by
    rw [Subgroup.map_sup,show ((Units.map (Algebra.norm (AdeleRing (𝓞 M) M) (S:=(AdeleRing (𝓞 M) M) ⊗[M] N)))).range.map f=(f.comp ((Units.map (Algebra.norm (AdeleRing (𝓞 M) M) (S:=(AdeleRing (𝓞 M) M) ⊗[M] N))))).range from MonoidHom.map_range _ _,hfg]
    exact sup_le_sup_right hf _
  have hsub : ((Units.map (algebraMap K (AdeleRing (𝓞 K) K)).toMonoidHom).range ⊔ (Units.map (Algebra.norm (AdeleRing (𝓞 K) K) (S:=(AdeleRing (𝓞 K) K) ⊗[K] N))).range) ≤ ((Units.map (algebraMap K (AdeleRing (𝓞 K) K)).toMonoidHom).range ⊔ (Units.map (Algebra.norm (AdeleRing (𝓞 K) K) (S:=(AdeleRing (𝓞 K) K) ⊗[K] L))).range) := by
    apply sup_le_sup_left
    rw [←he',←hr']
    rintro _ ⟨x,rfl⟩
    exact ⟨_,rfl⟩
  have hinc : (((Units.map (algebraMap M (AdeleRing (𝓞 M) M)).toMonoidHom).range ⊔ (Units.map (Algebra.norm (AdeleRing (𝓞 M) M) (S:=(AdeleRing (𝓞 M) M) ⊗[M] N))).range)).comap j ≤ ((Units.map (algebraMap K (AdeleRing (𝓞 K) K)).toMonoidHom).range ⊔ (Units.map (Algebra.norm (AdeleRing (𝓞 K) K) (S:=(AdeleRing (𝓞 K) K) ⊗[K] L))).range) := by
    intro x hx
    apply coprime_mem _ x hc
    · rw [←hpow]
      exact hsub (hm ⟨j x,hx,rfl⟩)
    · apply (show ((Units.map (Algebra.norm (AdeleRing (𝓞 K) K) (S:=(AdeleRing (𝓞 K) K) ⊗[K] L)))).range ≤ ((Units.map (algebraMap K (AdeleRing (𝓞 K) K)).toMonoidHom).range ⊔ (Units.map (Algebra.norm (AdeleRing (𝓞 K) K) (S:=(AdeleRing (𝓞 K) K) ⊗[K] L))).range) from le_sup_right)
      refine ⟨Units.map (algebraMap ((AdeleRing (𝓞 K) K)) ((AdeleRing (𝓞 K) K)⊗[K]L)).toMonoidHom x,?_⟩
      apply Units.ext
      change Algebra.norm ((AdeleRing (𝓞 K) K)) (algebraMap ((AdeleRing (𝓞 K) K)) ((AdeleRing (𝓞 K) K)⊗[K]L) x.val)=x.val^_
      rw [Algebra.norm_algebraMap,Module.finrank_baseChange]
  apply (Subgroup.index_dvd_of_le hinc).trans
  rw [Subgroup.index_comap]
  exact Subgroup.relIndex_dvd_index_of_normal _ _
theorem degree_one (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] (h : Module.finrank K L=1) : ((Units.map (algebraMap K (AdeleRing (𝓞 K) K)).toMonoidHom).range ⊔ (Units.map (Algebra.norm (AdeleRing (𝓞 K) K) (S:=(AdeleRing (𝓞 K) K) ⊗[K] L))).range).index=1 := by
  letI : Nontrivial ((AdeleRing (𝓞 K) K)) := (AdeleRing.algebraMap_injective (R:=𝓞 K) (K:=K)).nontrivial
  have hs : Function.Surjective ((Units.map (Algebra.norm (AdeleRing (𝓞 K) K) (S:=(AdeleRing (𝓞 K) K) ⊗[K] L)))) := by
    intro x
    use Units.map (algebraMap ((AdeleRing (𝓞 K) K)) ((AdeleRing (𝓞 K) K) ⊗[K] L)).toMonoidHom x
    apply Units.ext
    change Algebra.norm ((AdeleRing (𝓞 K) K)) (algebraMap ((AdeleRing (𝓞 K) K)) ((AdeleRing (𝓞 K) K)⊗[K]L) x.val)=x.val
    rw [Algebra.norm_algebraMap,Module.finrank_baseChange,h,pow_one]
  simp [MonoidHom.range_eq_top.mpr hs]

theorem cyclotomicField_finrank_le_totient
    (F : Type*) [Field F] [CharZero F]
    (m : ℕ) (hm : 0 < m) :
    Module.finrank F (CyclotomicField m F) ≤
      Nat.totient m := by
  let : NeZero m := ⟨hm.ne'⟩
  let C := CyclotomicField m F
  let : IsCyclotomicExtension {m} F C :=
    CyclotomicField.isCyclotomicExtension m F
  let : FiniteDimensional F C :=
    IsCyclotomicExtension.finiteDimensional {m} F C
  obtain ⟨ζ, hζ⟩ :=
    (CyclotomicField.isCyclotomicExtension m F).exists_isPrimitiveRoot
      (Set.mem_singleton m) hm.ne'
  have hgen : Algebra.adjoin F ({ζ} : Set C) = ⊤ :=
    IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ
  have htop :
      IntermediateField.adjoin F ({ζ} : Set C) = ⊤ :=
    IntermediateField.adjoin_eq_top_of_algebra
      F ({ζ} : Set C) hgen
  have hroot :
      Polynomial.aeval ζ
          (Polynomial.cyclotomic m F) = 0 := by
    rw [Polynomial.aeval_def,
      Polynomial.eval₂_eq_eval_map,
      Polynomial.map_cyclotomic,
      ← Polynomial.IsRoot.def]
    exact hζ.isRoot_cyclotomic hm
  have hdegree :
      (minpoly F ζ).natDegree ≤
        (Polynomial.cyclotomic m F).natDegree :=
    Polynomial.natDegree_le_natDegree
      (minpoly.min F ζ
        (Polynomial.cyclotomic.monic m F) hroot)
  calc
    Module.finrank F (CyclotomicField m F) =
        Module.finrank F C := rfl
    _ = Module.finrank F
          (IntermediateField.adjoin F ({ζ} : Set C)) := by
      rw [htop]
      simp
    _ = (minpoly F ζ).natDegree :=
      IntermediateField.adjoin.finrank
        (IsIntegral.of_finite F ζ)
    _ ≤ (Polynomial.cyclotomic m F).natDegree :=
      hdegree
    _ = Nat.totient m :=
      Polynomial.natDegree_cyclotomic m F

 

section Disjoint
variable
    (K M L : Type)
    [Field K] [Field M] [Field L]
    [Algebra K M] [Algebra K L]
    [hKM : FiniteDimensional K M]
    [hKL : FiniteDimensional K L]

 

theorem tensorProduct_isField_of_finrank_coprime
    (hcoprime :
      (Module.finrank K M).Coprime
        (Module.finrank K L)) :
    IsField (M ⊗[K] L) := by
  let Ω := AlgebraicClosure K
  let iM : M →ₐ[K] Ω := IsAlgClosed.lift
  let iL : L →ₐ[K] Ω := IsAlgClosed.lift
  let eM : M ≃ₐ[K] iM.fieldRange :=
    AlgEquiv.ofInjectiveField iM
  let eL : L ≃ₐ[K] iL.fieldRange :=
    AlgEquiv.ofInjectiveField iL
  have hdegrees :
      (Module.finrank K iM.fieldRange).Coprime
        (Module.finrank K iL.fieldRange) := by
    rw [← eM.toLinearEquiv.finrank_eq,
      ← eL.toLinearEquiv.finrank_eq]
    exact hcoprime
  have hdisjoint :
      iM.fieldRange.LinearDisjoint iL.fieldRange :=
    IntermediateField.LinearDisjoint.of_finrank_coprime
      hdegrees
  exact
    IntermediateField.LinearDisjoint.isField_of_isAlgebraic'
      hdisjoint
      (Or.inl (Algebra.IsAlgebraic.of_finite K M))


end Disjoint
theorem prime_degree (base : (
∀ (D M:Type) [Field D] [NumberField D] [Field M] [NumberField M] [Algebra D M] [FiniteDimensional D M],
  let T:=AdeleRing (𝓞 D) D ⊗[D] M
  letI : Algebra M T:=Algebra.TensorProduct.rightAlgebra
  Nonempty (T≃ₐ[M]AdeleRing (𝓞 M) M)
)) (kummer : ∀(D N:Type)[Field D][NumberField D][Field N][NumberField N][Algebra D N]
   [FiniteDimensional D N][IsGalois D N],(Module.finrank D N).Prime →
   (primitiveRoots (Module.finrank D N) D).Nonempty →
   let A:=AdeleRing (𝓞 D) D
   let T:=A⊗[D]N
   ((Units.map (algebraMap D A).toMonoidHom).range ⊔ (Units.map (Algebra.norm A (S:=T))).range).index ∣ Module.finrank D N) (K L : Type)
    [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (p : ℕ) (hp : p.Prime) (hdegree : Module.finrank K L = p) : ((Units.map (algebraMap K (AdeleRing (𝓞 K) K)).toMonoidHom).range ⊔ (Units.map (Algebra.norm (AdeleRing (𝓞 K) K) (S:=(AdeleRing (𝓞 K) K) ⊗[K] L))).range).index ∣ p := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  let M := CyclotomicField p K
  letI : IsCyclotomicExtension {p} K M := CyclotomicField.isCyclotomicExtension p K
  letI : FiniteDimensional K M := IsCyclotomicExtension.finiteDimensional {p} K M
  letI : NumberField M := NumberField.of_module_finite K M
  have hlt : Module.finrank K M < p := by
    have hle := cyclotomicField_finrank_le_totient K p hp.pos
    rw [Nat.totient_prime hp] at hle
    exact hle.trans_lt (Nat.sub_one_lt hp.ne_zero)
  have hc : (Module.finrank K M).Coprime (Module.finrank K L) := by
    rw [hdegree]
    exact (Nat.coprime_of_lt_prime Module.finrank_pos.ne' hlt hp).symm
  let N := M ⊗[K] L
  letI : Field N := (tensorProduct_isField_of_finrank_coprime K M L hc).toField
  letI : Algebra L N := Algebra.TensorProduct.rightAlgebra
  letI : Algebra M N := Algebra.TensorProduct.leftAlgebra
  letI : FiniteDimensional M N := Module.Finite.of_restrictScalars_finite K M N
  letI : FiniteDimensional L N := Module.Finite.of_restrictScalars_finite K L N
  letI : NumberField N := NumberField.of_module_finite M N
  have hd : Module.finrank M N = Module.finrank K L := Module.finrank_baseChange
  let au (g : Gal(L/K)) : Gal(N/M) := { (Algebra.TensorProduct.congr (AlgEquiv.refl : M ≃ₐ[K] M) g).toRingEquiv with
    commutes' := by
      intro m
      change (Algebra.TensorProduct.congr (AlgEquiv.refl : M ≃ₐ[K] M) g) (m⊗ₜ[K](1:L)) = m⊗ₜ[K](1:L)
      simp }
  have hi : Function.Injective au := by
    intro g h eq
    apply AlgEquiv.ext
    intro x
    apply (Algebra.TensorProduct.includeRight (R:=K) (A:=M) (B:=L)).injective
    exact DFunLike.congr_fun eq ((1:M)⊗ₜ[K]x)
  letI : IsGalois M N := IsGalois.of_card_aut_eq_finrank M N (by
    apply Nat.le_antisymm
    · rw [Nat.card_eq_fintype_card];exact AlgEquiv.card_le
    · rw [hd,←IsGalois.card_aut_eq_finrank K L]; exact Nat.card_le_card_of_injective au hi)
  obtain ⟨ζ,hζ⟩ := (CyclotomicField.isCyclotomicExtension p K).exists_isPrimitiveRoot (Set.mem_singleton p) hp.ne_zero
  have hm : (primitiveRoots (Module.finrank M N) M).Nonempty := by
    rw [hd,hdegree]
    exact ⟨ζ,(mem_primitiveRoots hp.pos).2 hζ⟩
  have hp' : (Module.finrank M N).Prime := by rw [hd,hdegree];exact hp
  have hy : ((Units.map (algebraMap M (AdeleRing (𝓞 M) M)).toMonoidHom).range ⊔ (Units.map (Algebra.norm (AdeleRing (𝓞 M) M) (S:=(AdeleRing (𝓞 M) M) ⊗[M] N))).range).index ∣ Module.finrank M N := kummer M N hp' hm
  rw [hd,hdegree] at hy
  exact (coprime_index base K M L N hc).trans hy

theorem degree_dvd (base : (
∀ (D M:Type) [Field D] [NumberField D] [Field M] [NumberField M] [Algebra D M] [FiniteDimensional D M],
  let T:=AdeleRing (𝓞 D) D ⊗[D] M
  letI : Algebra M T:=Algebra.TensorProduct.rightAlgebra
  Nonempty (T≃ₐ[M]AdeleRing (𝓞 M) M)
)) (kummer : ∀(D N:Type)[Field D][NumberField D][Field N][NumberField N][Algebra D N]
   [FiniteDimensional D N][IsGalois D N],(Module.finrank D N).Prime →
   (primitiveRoots (Module.finrank D N) D).Nonempty →
   let A:=AdeleRing (𝓞 D) D
   let T:=A⊗[D]N
   ((Units.map (algebraMap D A).toMonoidHom).range ⊔ (Units.map (Algebra.norm A (S:=T))).range).index ∣ Module.finrank D N) (K L : Type)
    [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L] [IsCyclic Gal(L/K)] : ((Units.map (algebraMap K (AdeleRing (𝓞 K) K)).toMonoidHom).range ⊔ (Units.map (Algebra.norm (AdeleRing (𝓞 K) K) (S:=(AdeleRing (𝓞 K) K) ⊗[K] L))).range).index ∣ Module.finrank K L := by
  induction he : Module.finrank K L using Nat.strong_induction_on generalizing K L with
  | h n ih =>
    by_cases h1 : Module.finrank K L = 1
    · rw [degree_one K L h1];exact one_dvd _
    obtain ⟨p,hp,hpdiv⟩ := Nat.exists_prime_and_dvd h1
    obtain ⟨g,hgen⟩ := IsCyclic.exists_generator (α:=Gal(L/K))
    let H := Subgroup.zpowers (g^p)
    let M := IntermediateField.fixedField H
    letI : H.Normal := inferInstance
    letI : NumberField M := NumberField.of_module_finite K M
    letI : IsGalois K M := by dsimp [M];infer_instance
    letI : IsGalois M L := IsGalois.of_fixed_field L H
    letI : IsCyclic Gal(L/M) := (IntermediateField.subgroupEquivAlgEquiv H).isCyclic.mp (inferInstance : IsCyclic H)
    have hg : orderOf g = Module.finrank K L :=
      (orderOf_eq_card_of_forall_mem_zpowers hgen).trans (IsGalois.card_aut_eq_finrank K L)
    have ht : Module.finrank M L = Module.finrank K L / p := by
      change Module.finrank (IntermediateField.fixedField H) L=_
      rw [IntermediateField.finrank_fixedField_eq_card,Nat.card_zpowers,orderOf_pow_of_dvd hp.ne_zero (hg ▸ hpdiv),hg]
    have hm : Module.finrank K M=p := by
      have long := Module.finrank_mul_finrank K M L
      apply Nat.mul_right_cancel (Module.finrank_pos (R:=M) (M:=L))
      rw [long,ht,Nat.mul_div_cancel' hpdiv]
    have htop := ih (Module.finrank M L) (by rw [ht,←he];exact Nat.div_lt_self Module.finrank_pos hp.one_lt) M L rfl
    have hbase := prime_degree base kummer K M p hp hm
    apply (norm_tower K M L base).trans
    rw [←he,←Module.finrank_mul_finrank K M L,Nat.mul_comm (Module.finrank K M)]
    exact Nat.mul_dvd_mul htop (hm ▸ hbase)

theorem degree_bound (base : (
∀ (D M:Type) [Field D] [NumberField D] [Field M] [NumberField M] [Algebra D M] [FiniteDimensional D M],
  let T:=AdeleRing (𝓞 D) D ⊗[D] M
  letI : Algebra M T:=Algebra.TensorProduct.rightAlgebra
  Nonempty (T≃ₐ[M]AdeleRing (𝓞 M) M)
)) (kummer : ∀(D N:Type)[Field D][NumberField D][Field N][NumberField N][Algebra D N]
   [FiniteDimensional D N][IsGalois D N],(Module.finrank D N).Prime →
   (primitiveRoots (Module.finrank D N) D).Nonempty →
   let A:=AdeleRing (𝓞 D) D
   let T:=A⊗[D]N
   ((Units.map (algebraMap D A).toMonoidHom).range ⊔ (Units.map (Algebra.norm A (S:=T))).range).index ∣ Module.finrank D N) :
  ∀(D N:Type)[Field D][NumberField D][Field N][NumberField N][Algebra D N]
   [FiniteDimensional D N][IsGalois D N](g:Gal(N/D)),(∀ s,s∈Subgroup.zpowers g) →
   ((Units.map (algebraMap D (AdeleRing (𝓞 D) D)).toMonoidHom).range ⊔ (Units.map (Algebra.norm (AdeleRing (𝓞 D) D) (S:=(AdeleRing (𝓞 D) D) ⊗[D] N))).range).index ≤ Module.finrank D N := by
  intro K L _ _ _ _ _ _ _ g gen
  letI : IsCyclic Gal(L/K) := ⟨g,gen⟩
  exact Nat.le_of_dvd Module.finrank_pos (degree_dvd base kummer K L)

theorem deriveCyclicClassFormation : (
∀(D N:Type)[Field D][NumberField D][Field N][NumberField N][Algebra D N]
   [FiniteDimensional D N][IsGalois D N](g:Gal(N/D)),(∀ s,s∈Subgroup.zpowers g) →
   let A:=AdeleRing (𝓞 D) D
   let T:=A⊗[D]N
   let P:=(Units.map (algebraMap D A).toMonoidHom).range ⊔ (Units.map (Algebra.norm A (S:=T))).range
   let q:=QuotientGroup.mk' (Units.map (Algebra.TensorProduct.includeRight (R:=D) (A:=A) (B:=N)).toMonoidHom).range
   let a(s:Gal(N/D)):=Units.mapEquiv (Algebra.TensorProduct.congr (AlgEquiv.refl (R:=A) (A₁:=A)) s).toMulEquiv
   let n:=q.comp (∏ s:Gal(N/D),(a s).toMonoidHom)
   let b:=q.comp ((a g).toMonoidHom / MonoidHom.id Tˣ)
   let k:=b.range.relIndex (n.ker.map q)
   0<k ∧ P.index=Module.finrank D N*k
) → (
∀ (D M:Type) [Field D] [NumberField D] [Field M] [NumberField M] [Algebra D M] [FiniteDimensional D M],
  let T:=AdeleRing (𝓞 D) D ⊗[D] M
  letI : Algebra M T:=Algebra.TensorProduct.rightAlgebra
  Nonempty (T≃ₐ[M]AdeleRing (𝓞 M) M)
) → (
(∀(D N:Type)[Field D][NumberField D][Field N][NumberField N][Algebra D N]
    [FiniteDimensional D N][IsGalois D N][IsCyclic Gal(N/D)],
    let A:=AdeleRing (𝓞 D) D
    (Units.map (algebraMap D A).toMonoidHom).range ⊔ (Units.map (Algebra.norm A (S:=A⊗[D]N))).range=⊤ →
    Module.finrank D N=1) →
  ∀(D N:Type)[Field D][NumberField D][Field N][NumberField N][Algebra D N]
   [FiniteDimensional D N][IsGalois D N],(Module.finrank D N).Prime →
   (primitiveRoots (Module.finrank D N) D).Nonempty →
   let A:=AdeleRing (𝓞 D) D
   let T:=A⊗[D]N
   ((Units.map (algebraMap D A).toMonoidHom).range ⊔ (Units.map (Algebra.norm A (S:=T))).range).index ∣ Module.finrank D N
) → OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H1_R1.H1 := by
  intro first base kummer
  have lower : (∀(D N:Type)[Field D][NumberField D][Field N][NumberField N][Algebra D N]
    [FiniteDimensional D N][IsGalois D N][IsCyclic Gal(N/D)],
    let A:=AdeleRing (𝓞 D) D
    (Units.map (algebraMap D A).toMonoidHom).range ⊔ (Units.map (Algebra.norm A (S:=A⊗[D]N))).range=⊤ →
    Module.finrank D N=1) := by
    intro D N _ _ _ _ _ _ _ _
    dsimp only
    intro top
    obtain ⟨g,hg⟩:=IsCyclic.exists_generator (α:=Gal(N/D))
    obtain ⟨pos,eq⟩:=first D N g hg
    dsimp only at eq
    rw [top,Subgroup.index_top] at eq
    exact le_antisymm ((Nat.le_mul_of_pos_right _ pos).trans_eq eq.symm) Module.finrank_pos
  have second := degree_bound base (kummer lower)
  intro D N _ _ _ _ _ _ _ g gen
  obtain ⟨hk,he⟩ := first D N g gen
  have hle := second D N g gen
  let A:=AdeleRing (𝓞 D) D
  let T:=A⊗[D]N
  let P:=(Units.map (algebraMap D A).toMonoidHom).range ⊔ (Units.map (Algebra.norm A (S:=T))).range
  let q:=QuotientGroup.mk' (Units.map (Algebra.TensorProduct.includeRight (R:=D) (A:=A) (B:=N)).toMonoidHom).range
  let a(s:Gal(N/D)):=Units.mapEquiv (Algebra.TensorProduct.congr (AlgEquiv.refl (R:=A) (A₁:=A)) s).toMulEquiv
  let n:=q.comp (∏ s:Gal(N/D),(a s).toMonoidHom)
  let b:=q.comp ((a g).toMonoidHom / MonoidHom.id Tˣ)
  let k:=b.range.relIndex (n.ker.map q)
  change 0<k at hk
  change P.index=Module.finrank D N*k at he
  change P.index≤Module.finrank D N at hle
  have hpos : 0 < Module.finrank D N := Module.finrank_pos
  have hkle : k ≤ 1 := by
    rw [he] at hle
    exact Nat.le_of_mul_le_mul_left (show Module.finrank D N*k ≤ Module.finrank D N*1 by simpa using hle) hpos
  have hkone : k = 1 := by omega
  refine ⟨by simpa only [hkone,Nat.mul_one] using he,?_⟩
  intro z hz
  have zker : z ∈ n.ker := by
    change q ((∏ s:Gal(N/D), (a s).toMonoidHom) z) = 1
    rw [MonoidHom.finsetProd_apply,map_prod]
    exact hz
  obtain ⟨y,hy⟩ := (Subgroup.relIndex_eq_one.mp hkone) (show q z ∈ n.ker.map q from ⟨z,zker,rfl⟩)
  exact ⟨y,hy⟩

end
end OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H1_R1_H1_R1

end

section
open NumberField IsDedekindDomain
open scoped TensorProduct NumberField Classical
open scoped NumberField TensorProduct Classical

 
namespace OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H1_R1_H1_R1_H3_R1
open NumberField IsDedekindDomain
open scoped NumberField TensorProduct Classical
noncomputable section



theorem deriveKummerPrimeNorm : (
(∀(D N:Type)[Field D][NumberField D][Field N][NumberField N][Algebra D N]
    [FiniteDimensional D N][IsGalois D N][IsCyclic Gal(N/D)],
    let A:=AdeleRing (𝓞 D) D
    (Units.map (algebraMap D A).toMonoidHom).range ⊔ (Units.map (Algebra.norm A (S:=A⊗[D]N))).range=⊤ →
    Module.finrank D N=1) →
  ∀(D:Type)[Field D][NumberField D](E:IntermediateField D (SeparableClosure D))
   [FiniteDimensional D E][IsGalois D E],
   let p:=Module.finrank D E
   p.Prime → (primitiveRoots p D).Nonempty →
   letI:NumberField E:=NumberField.of_module_finite D E
   let V:=HeightOneSpectrum (𝓞 D)
   let A:=AdeleRing (𝓞 D) D
   let U(S T:Finset V):=Subgroup.closure {a:Aˣ |
     (∀ w:InfinitePlace D,∃ y:w.Completion,y^p=a.val.1 w) ∧
     (∀ v∈S,∃ y:v.adicCompletion D,y^p=a.val.2 v) ∧
     ∀ v:V,v∉S∪T → a.val.2 v∈v.adicCompletionIntegers D ∧ (a⁻¹).val.2 v∈v.adicCompletionIntegers D}
   let split(v:V):=∀ t:HeightOneSpectrum (𝓞 E),t.asIdeal.LiesOver v.asIdeal → ∀ g:Gal(E/D),
     HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapAlgEquiv g).toRingEquiv t=t → g=1
   let unram(v:V):=∀ t:HeightOneSpectrum (𝓞 E),t.asIdeal.LiesOver v.asIdeal → Algebra.IsUnramifiedAt (𝓞 D) t.asIdeal
   ∃ S T:Finset V, (∀ v∈T,split v) ∧ (∀ v:V,v∉S∪T → unram v) ∧
     ((Units.map (algebraMap D A).toMonoidHom).range ⊔ U S T).index=p
) → (
∀(D:Type)[Field D][NumberField D](E:IntermediateField D (SeparableClosure D))
   [FiniteDimensional D E][IsGalois D E],
   let p:=Module.finrank D E
   p.Prime → (primitiveRoots p D).Nonempty →
   letI:NumberField E:=NumberField.of_module_finite D E
   let V:=HeightOneSpectrum (𝓞 D)
   let A:=AdeleRing (𝓞 D) D
   let U(S T:Finset V):=Subgroup.closure {a:Aˣ |
     (∀ w:InfinitePlace D,∃ y:w.Completion,y^p=a.val.1 w) ∧
     (∀ v∈S,∃ y:v.adicCompletion D,y^p=a.val.2 v) ∧
     ∀ v:V,v∉S∪T → a.val.2 v∈v.adicCompletionIntegers D ∧ (a⁻¹).val.2 v∈v.adicCompletionIntegers D}
   let split(v:V):=∀ t:HeightOneSpectrum (𝓞 E),t.asIdeal.LiesOver v.asIdeal → ∀ g:Gal(E/D),
     HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapAlgEquiv g).toRingEquiv t=t → g=1
   let unram(v:V):=∀ t:HeightOneSpectrum (𝓞 E),t.asIdeal.LiesOver v.asIdeal → Algebra.IsUnramifiedAt (𝓞 D) t.asIdeal
   ∀ S T:Finset V, (∀ v∈T,split v) → (∀ v:V,v∉S∪T → unram v) →
     U S T ≤ (Units.map (Algebra.norm A (S:=A⊗[D]E))).range
) → (
(∀(D N:Type)[Field D][NumberField D][Field N][NumberField N][Algebra D N]
    [FiniteDimensional D N][IsGalois D N][IsCyclic Gal(N/D)],
    let A:=AdeleRing (𝓞 D) D
    (Units.map (algebraMap D A).toMonoidHom).range ⊔ (Units.map (Algebra.norm A (S:=A⊗[D]N))).range=⊤ →
    Module.finrank D N=1) →
  ∀(D N:Type)[Field D][NumberField D][Field N][NumberField N][Algebra D N]
   [FiniteDimensional D N][IsGalois D N],(Module.finrank D N).Prime →
   (primitiveRoots (Module.finrank D N) D).Nonempty →
   let A:=AdeleRing (𝓞 D) D
   let T:=A⊗[D]N
   ((Units.map (algebraMap D A).toMonoidHom).range ⊔ (Units.map (Algebra.norm A (S:=T))).range).index ∣ Module.finrank D N
) := by
  intro aux norms lower
  have aux := aux lower
  intro D N _ _ _ _ _ _ _ hp hmu
  let i : N →ₐ[D] SeparableClosure D := IsSepClosed.lift
  let E := i.fieldRange
  let e : N ≃ₐ[D] E := AlgHom.equivFieldRange i
  letI : FiniteDimensional D E := e.toLinearEquiv.finiteDimensional
  letI : IsGalois D E := IsGalois.of_algEquiv e
  letI : NumberField E := NumberField.of_module_finite D E
  have hd : Module.finrank D N=Module.finrank D E := e.toLinearEquiv.finrank_eq
  have hpE : (Module.finrank D E).Prime := hd ▸ hp
  have hmuE : (primitiveRoots (Module.finrank D E) D).Nonempty := hd ▸ hmu
  obtain ⟨S,T,hs,hu,hi⟩ := aux D E hpE hmuE
  have hn := norms D E hpE hmuE S T hs hu
  let A:=AdeleRing (𝓞 D) D
  let normN:=Units.map (Algebra.norm A (S:=A⊗[D]N))
  let normE:=Units.map (Algebra.norm A (S:=A⊗[D]E))
  let j := Algebra.TensorProduct.congr (AlgEquiv.refl (R:=A) (A₁:=A)) e
  let u := Units.mapEquiv j.toMulEquiv
  have hr : normE.range ≤ normN.range := by
    rintro _ ⟨y,rfl⟩
    obtain ⟨z,rfl⟩ := u.surjective y
    refine ⟨z,Units.ext ?_⟩
    exact (Algebra.norm_eq_of_algEquiv j z.val).symm
  rw [hd,←hi]
  exact Subgroup.index_dvd_of_le (sup_le_sup_left (hn.trans hr) _)
end
end OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H1_R1_H1_R1_H3_R1

end

section
open NumberField IsDedekindDomain
open scoped NumberField TensorProduct Classical

 
namespace OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H1_R1_H1_R1_H3_R1_H1_R1
open NumberField IsDedekindDomain
open scoped NumberField TensorProduct Classical
noncomputable section




theorem factor {X A:Type} [CommGroup X] [CommGroup A] (j:X→*A) (U J:Subgroup A)
    (hUJ:U≤J) (hj:j.range⊔J=⊤) :
    (U.comap j).relIndex (J.comap j) * (j.range⊔U).index=U.relIndex J := by
  let P:=j.range⊔U
  have h1:U≤P:=le_sup_right
  have h2:P⊔J=⊤:=by
    change j.range⊔U⊔J=⊤
    rwa [sup_assoc,sup_of_le_right hUJ]
  have h3:(j.range ⊓ J)⊔U=P⊓J:=by
    change (j.range ⊓ J)⊔U=(j.range⊔U)⊓J
    rw [sup_comm (j.range⊓J) U,sup_comm j.range U,sup_inf_assoc_of_le _ hUJ]
  rw [Subgroup.relIndex_comap,Subgroup.map_comap_eq,← Subgroup.relIndex_sup_right _ U,h3]
  change U.relIndex (P⊓J)*P.index=U.relIndex J
  rw [←Subgroup.relIndex_top_right P,←h2,Subgroup.relIndex_sup_left,Subgroup.relIndex_inf_mul_relIndex,inf_of_le_left h1]

theorem deriveKummerSUnitPowerIndex : (
∀(D:Type)[Field D][NumberField D](p:ℕ),p.Prime → (primitiveRoots p D).Nonempty →
   let V:=HeightOneSpectrum (𝓞 D)
   let A:=AdeleRing (𝓞 D) D
   let U(S T:Finset V):=Subgroup.closure {a:Aˣ |
     (∀ w:InfinitePlace D,∃ y:w.Completion,y^p=a.val.1 w) ∧
     (∀ v∈S,∃ y:v.adicCompletion D,y^p=a.val.2 v) ∧
     ∀ v:V,v∉S∪T → a.val.2 v∈v.adicCompletionIntegers D ∧ (a⁻¹).val.2 v∈v.adicCompletionIntegers D}
   let J(F:Finset V):=Subgroup.closure {a:Aˣ | ∀ v:V,v∉F → a.val.2 v∈v.adicCompletionIntegers D ∧ (a⁻¹).val.2 v∈v.adicCompletionIntegers D}
   ∀ S T:Finset V,(∀ v:V,v.asIdeal ∣ Ideal.span {(p:𝓞 D)} → v∈S) →
      (U S T).relIndex (J (S∪T))=p^(2*(Nat.card (InfinitePlace D)+S.card))
) → (
∀(D:Type)[Field D][NumberField D](p:ℕ),p.Prime → (primitiveRoots p D).Nonempty →
   ∀ F:Finset (HeightOneSpectrum (𝓞 D)),
     let E:=(F:Set (HeightOneSpectrum (𝓞 D))).unit D
     (powMonoidHom p:E→*E).range.index=p^(Nat.card (InfinitePlace D)+F.card)
) → (
(∀(D N:Type)[Field D][NumberField D][Field N][NumberField N][Algebra D N]
    [FiniteDimensional D N][IsGalois D N][IsCyclic Gal(N/D)],
    let A:=AdeleRing (𝓞 D) D
    (Units.map (algebraMap D A).toMonoidHom).range ⊔ (Units.map (Algebra.norm A (S:=A⊗[D]N))).range=⊤ →
    Module.finrank D N=1) →
  ∀(D:Type)[Field D][NumberField D](E:IntermediateField D (SeparableClosure D))
   [FiniteDimensional D E][IsGalois D E],
   let p:=Module.finrank D E
   p.Prime → (primitiveRoots p D).Nonempty →
   letI:NumberField E:=NumberField.of_module_finite D E
   let V:=HeightOneSpectrum (𝓞 D)
   let A:=AdeleRing (𝓞 D) D
   let U(S T:Finset V):=Subgroup.closure {a:Aˣ |
     (∀ w:InfinitePlace D,∃ y:w.Completion,y^p=a.val.1 w) ∧
     (∀ v∈S,∃ y:v.adicCompletion D,y^p=a.val.2 v) ∧
     ∀ v:V,v∉S∪T → a.val.2 v∈v.adicCompletionIntegers D ∧ (a⁻¹).val.2 v∈v.adicCompletionIntegers D}
   let split(v:V):=∀ t:HeightOneSpectrum (𝓞 E),t.asIdeal.LiesOver v.asIdeal → ∀ g:Gal(E/D),
     HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapAlgEquiv g).toRingEquiv t=t → g=1
   let unram(v:V):=∀ t:HeightOneSpectrum (𝓞 E),t.asIdeal.LiesOver v.asIdeal → Algebra.IsUnramifiedAt (𝓞 D) t.asIdeal
   let J(F:Finset V):=Subgroup.closure {a:Aˣ | ∀ v:V,v∉F → a.val.2 v∈v.adicCompletionIntegers D ∧ (a⁻¹).val.2 v∈v.adicCompletionIntegers D}
   let j:=Units.map (algebraMap D A).toMonoidHom
   ∃ S T:Finset V, (∀ v∈T,split v) ∧ (∀ v:V,v∉S∪T → unram v) ∧ Disjoint S T ∧
     T.card+1=Nat.card (InfinitePlace D)+S.card ∧ (∀ v:V,v.asIdeal ∣ Ideal.span {(p:𝓞 D)} → v∈S) ∧
     j.range⊔J (S∪T)=⊤ ∧ let E:=(↑(S∪T):Set V).unit D
     (J (S∪T)).comap j=E ∧ (U S T).comap j=(powMonoidHom p:E→*E).range.map E.subtype
) → (
(∀(D N:Type)[Field D][NumberField D][Field N][NumberField N][Algebra D N]
    [FiniteDimensional D N][IsGalois D N][IsCyclic Gal(N/D)],
    let A:=AdeleRing (𝓞 D) D
    (Units.map (algebraMap D A).toMonoidHom).range ⊔ (Units.map (Algebra.norm A (S:=A⊗[D]N))).range=⊤ →
    Module.finrank D N=1) →
  ∀(D:Type)[Field D][NumberField D](E:IntermediateField D (SeparableClosure D))
   [FiniteDimensional D E][IsGalois D E],
   let p:=Module.finrank D E
   p.Prime → (primitiveRoots p D).Nonempty →
   letI:NumberField E:=NumberField.of_module_finite D E
   let V:=HeightOneSpectrum (𝓞 D)
   let A:=AdeleRing (𝓞 D) D
   let U(S T:Finset V):=Subgroup.closure {a:Aˣ |
     (∀ w:InfinitePlace D,∃ y:w.Completion,y^p=a.val.1 w) ∧
     (∀ v∈S,∃ y:v.adicCompletion D,y^p=a.val.2 v) ∧
     ∀ v:V,v∉S∪T → a.val.2 v∈v.adicCompletionIntegers D ∧ (a⁻¹).val.2 v∈v.adicCompletionIntegers D}
   let split(v:V):=∀ t:HeightOneSpectrum (𝓞 E),t.asIdeal.LiesOver v.asIdeal → ∀ g:Gal(E/D),
     HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapAlgEquiv g).toRingEquiv t=t → g=1
   let unram(v:V):=∀ t:HeightOneSpectrum (𝓞 E),t.asIdeal.LiesOver v.asIdeal → Algebra.IsUnramifiedAt (𝓞 D) t.asIdeal
   ∃ S T:Finset V, (∀ v∈T,split v) ∧ (∀ v:V,v∉S∪T → unram v) ∧
     ((Units.map (algebraMap D A).toMonoidHom).range ⊔ U S T).index=p
) := by
  intro places units aux lower
  have aux := aux lower
  intro D _ _ N _ _
  dsimp only
  intro hp hmu
  letI : NumberField N:=NumberField.of_module_finite D N
  let p:=Module.finrank D N
  let A:=AdeleRing (𝓞 D) D
  let V:=HeightOneSpectrum (𝓞 D)
  let j:=Units.map (algebraMap D A).toMonoidHom
  obtain ⟨S,T,hS,hU,hd,hc,hpS,hlarge,him,hpow⟩:=aux D N hp hmu
  refine ⟨S,T,hS,hU,?_⟩
  let J:=Subgroup.closure {a:Aˣ | ∀ v:V,v∉S∪T → a.val.2 v∈v.adicCompletionIntegers D ∧ (a⁻¹).val.2 v∈v.adicCompletionIntegers D}
  let U:=Subgroup.closure {a:Aˣ | (∀ w:InfinitePlace D,∃ y:w.Completion,y^p=a.val.1 w) ∧ (∀ v∈S,∃ y:v.adicCompletion D,y^p=a.val.2 v) ∧ ∀ v:V,v∉S∪T → a.val.2 v∈v.adicCompletionIntegers D ∧ (a⁻¹).val.2 v∈v.adicCompletionIntegers D}
  let E:=(↑(S∪T):Set V).unit D
  have hu:U≤J:=Subgroup.closure_mono fun _ hx=>hx.2.2
  have he:=(factor j U J hu hlarge)
  change J.comap j=E at him
  change U.comap j=(powMonoidHom p:E→*E).range.map E.subtype at hpow
  rw [hpow,him] at he
  have hleft(H:Subgroup E):(H.map E.subtype).relIndex E=H.index:=by
    change (H.map E.subtype).relIndex E=H.index
    have hmap := Subgroup.relIndex_map_map_of_injective H ⊤ E.subtype_injective
    rw [← E.subtype.range_eq_map, E.range_subtype,Subgroup.relIndex_top_right] at hmap
    exact hmap
  rw [hleft,units D p hp hmu (S∪T),places D p hp hmu S T hpS] at he
  rw [Finset.card_union_of_disjoint hd] at he
  have hexp:2*(Nat.card (InfinitePlace D)+S.card)=Nat.card (InfinitePlace D)+(S.card+T.card)+1:=by omega
  rw [hexp,pow_succ] at he
  exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos _) he
end
end OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H1_R1_H1_R1_H3_R1_H1_R1

end

namespace OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H1_R1_H1_R1
theorem main : H1 → H2 → H3 → H4 → OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H1_R1.H1 :=
  fun v1 v2 v3 v4 =>
    (OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H1_R1_H1_R1.deriveCyclicClassFormation v1 v2.1 (OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H1_R1_H1_R1_H3_R1.deriveKummerPrimeNorm (OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H1_R1_H1_R1_H3_R1_H1_R1.deriveKummerSUnitPowerIndex v2.2.1 v2.2.2 v3) v4))
end OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H1_R1_H1_R1
