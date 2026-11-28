import OMAReductions.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H1_R1_H2_R1
import Mathlib


/-! Finite rational ray norm images and a continuous procyclic quotient give the rational value. A separate finite cyclotomic calculation detects a single supported prime. -/

namespace OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H1_R1_H2_R1_H1_R1

section

open NumberField IsDedekindDomain
open scoped NumberField TensorProduct Classical
open scoped NumberField Classical TensorProduct IsMulCommutative

def H1 : Prop :=
  (
∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 ℚ)),
    let K := v.adicCompletion ℚ
    Set.range (fun x : (K ⊗[ℚ] F)ˣ => -WithZero.log (Valued.v (Algebra.norm K x.val))) =
      (↑(AddSubgroup.closure {n : ℤ | ∃ w : HeightOneSpectrum (𝓞 F),
        w.asIdeal.LiesOver v.asIdeal ∧ n = (w.asIdeal.inertiaDeg (𝓞 ℚ) : ℤ)}) : Set ℤ)
) ∧
  (
∀ (F : Type) [Field F] [NumberField F] (p : HeightOneSpectrum (𝓞 ℚ)),
  let K := p.adicCompletion ℚ
  let A := AdeleRing (𝓞 ℚ) ℚ
  let N := Units.map (Algebra.norm A (S := A ⊗[ℚ] F))
  (∀ y : (A ⊗[ℚ] F)ˣ, ∃ x : (K ⊗[ℚ] F)ˣ, (N y).val.2 p = Algebra.norm K x.val) ∧
  (∀ x : (K ⊗[ℚ] F)ˣ, ∃ y : (A ⊗[ℚ] F)ˣ, (N y).val.1 = 1 ∧
    (∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ p → (N y).val.2 w = 1) ∧ (N y).val.2 p = Algebra.norm K x.val)
) ∧
  (
  let Z := (Int.castRingHom (∀ n:ℕ+,ZMod (n:ℕ))).range.topologicalClosure
  let ev (m:ℕ+) := Units.map (((Pi.evalRingHom (fun i:ℕ+ => ZMod (i:ℕ)) m).comp Z.subtype).toMonoidHom)
  ∀ (S T:Subgroup Zˣ), (∀ m:ℕ+, S.map (ev m)=T.map (ev m)) → closure (S : Set Zˣ)=closure (T : Set Zˣ)
)

end

section

open NumberField IsDedekindDomain
open scoped NumberField TensorProduct Classical
open scoped NumberField Classical TensorProduct IsMulCommutative

def H2 : Prop :=
  (
  let A := AdeleRing (𝓞 ℚ) ℚ
  let P := HeightOneSpectrum (𝓞 ℚ)
  ∀ (F:Type) [Field F] [NumberField F] (m:ℕ+) (y:(A⊗[ℚ]F)ˣ),
    let N:=Units.map (Algebra.norm A (S:=A⊗[ℚ]F))
    ∃ t:(A⊗[ℚ]F)ˣ, N y / N t ∈ (Units.map (algebraMap ℚ A).toMonoidHom).range ∧
    ((∀ (w:InfinitePlace ℚ) (h:w.IsReal), 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal h ((N t).val.1 w)) ∧
  ∀ p:P, let n:=m.val.factorization (Rat.HeightOneSpectrum.natGenerator p)
    n≠0 → ∃ u:(p.adicCompletionIntegers ℚ)ˣ, (u.val : p.adicCompletion ℚ)=(N t).val.2 p ∧
      (u.val-1)∈(IsLocalRing.maximalIdeal (p.adicCompletionIntegers ℚ))^n)
) ∧
  (
∀ (m : ℕ), (2 < m) → let F:=CyclotomicField m ℚ
  ∀ (p:HeightOneSpectrum (𝓞 F)), p.asIdeal.absNorm.Coprime m → (p.asIdeal.absNorm:ZMod m)=1
)

end

section

open NumberField IsDedekindDomain
open scoped NumberField Classical TensorProduct IsMulCommutative
open scoped NumberField TensorProduct Classical
open Set

def H3 : Prop :=
  (
  let Z := (Int.castRingHom (∀ n:ℕ+,ZMod (n:ℕ))).range.topologicalClosure
  let ev (m:ℕ+) := Units.map (((Pi.evalRingHom (fun i:ℕ+ => ZMod (i:ℕ)) m).comp Z.subtype).toMonoidHom)
  let G:=Gal(SeparableClosure ℚ/ℚ)
  ∃ d:G →* Zˣ, Continuous d ∧ Function.Surjective d ∧
    ∀ H:ClosedSubgroup G, H.toSubgroup.FiniteIndex →
    let F:=IntermediateField.fixedField H.toSubgroup
    ∀ [NumberField F] (m:ℕ+), (H.toSubgroup.map d).map (ev m)=Subgroup.closure {a:(ZMod (m:ℕ))ˣ | ∃ v:HeightOneSpectrum (𝓞 F), (a:ZMod (m:ℕ))=v.asIdeal.absNorm}
) ∧
  (
  let Z := (Int.castRingHom (∀ n:ℕ+,ZMod (n:ℕ))).range.topologicalClosure
  let ev (m:ℕ+) := Units.map (((Pi.evalRingHom (fun i:ℕ+ => ZMod (i:ℕ)) m).comp Z.subtype).toMonoidHom)
  let A:=AdeleRing (𝓞 ℚ) ℚ
  ∃ v:Aˣ →* Zˣ, Function.Surjective v ∧ (∀ x:ℚˣ, v (Units.map (algebraMap ℚ A).toMonoidHom x)=1) ∧
  (∀ (m:ℕ+) (p:HeightOneSpectrum (𝓞 ℚ)) (n:ℕ) (z:Aˣ), z.val.1=1 →
    (∀ w:HeightOneSpectrum (𝓞 ℚ), w≠p → z.val.2 w=1) → p.asIdeal.absNorm.Coprime m.val →
    -WithZero.log (Valued.v (z.val.2 p))=(n:ℤ) → ((ev m (v z)).val:ZMod m.val)=(p.asIdeal.absNorm:ZMod m.val)^n) ∧
  ∀ (m:ℕ+) (z:Aˣ), (let P:=HeightOneSpectrum (𝓞 ℚ)
    (∀ (w:InfinitePlace ℚ) (h:w.IsReal), 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal h (z.val.1 w)) ∧
  ∀ p:P, let n:=m.val.factorization (Rat.HeightOneSpectrum.natGenerator p)
    n≠0 → ∃ u:(p.adicCompletionIntegers ℚ)ˣ, (u.val : p.adicCompletion ℚ)=z.val.2 p ∧
      (u.val-1)∈(IsLocalRing.maximalIdeal (p.adicCompletionIntegers ℚ))^n) →
    ∀ C:Subgroup (ZMod m.val)ˣ, (∀ (p:HeightOneSpectrum (𝓞 ℚ)) (u:(ZMod m.val)ˣ), (u:ZMod m.val)=p.asIdeal.absNorm →
      u ^ (-WithZero.log (Valued.v (z.val.2 p))) ∈ C) → ev m (v z) ∈ C
) ∧
  (
  let R := ∀ n:ℕ+,ZMod (n:ℕ)
  let Z := (Int.castRingHom R).range.topologicalClosure
  (∃ f : Zˣ →* Multiplicative Z, Continuous f ∧ Function.Surjective f) ∧
    ∀ n:ℕ, 0<n → IsOpen ((powMonoidHom n : Multiplicative Z →* Multiplicative Z).range : Set (Multiplicative Z))
)

end

end OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H1_R1_H2_R1_H1_R1

section
open NumberField IsDedekindDomain
open scoped NumberField Classical TensorProduct IsMulCommutative
open Set

 
namespace OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H1_R1_H2_R1_H1_R1_H1_R1
open NumberField IsDedekindDomain
open scoped NumberField Classical TensorProduct IsMulCommutative

open Set

private theorem same_subgroup {Z : Type*} [CommGroup Z] {S T Q : Subgroup Z}
    (hS : Q ≤ S) (hT : Q ≤ T)
    (h : S.map (QuotientGroup.mk' Q) = T.map (QuotientGroup.mk' Q)) : S = T := by
  have eq := congrArg (Subgroup.comap (QuotientGroup.mk' Q)) h
  simpa only [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hS,
    sup_eq_left.mpr hT] using eq

private theorem norm_images {G Z : Type*} [Group G] [CommGroup Z]
    (H : Subgroup G) [H.FiniteIndex] (d : G →* Z) (hd : Function.Surjective d)
    (F : Type) [Field F] [CharZero F] [FiniteDimensional ℚ F]
    (v : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* Z) (hv : Function.Surjective v)
    (levels : ∀ m : ℕ, 0 < m →
      let A := AdeleRing (𝓞 ℚ) ℚ
      let q := QuotientGroup.mk' (powMonoidHom m : Z →* Z).range
      (v.comp (Units.map (Algebra.norm A (S := A ⊗[ℚ] F)))).range.map q = (H.map d).map q) :
    let A := AdeleRing (𝓞 ℚ) ℚ
    (v.comp (Units.map (Algebra.norm A (S := A ⊗[ℚ] F)))).range = H.map d := by
  let A := AdeleRing (𝓞 ℚ) ℚ
  letI : Nontrivial A := (AdeleRing.algebraMap_injective (𝓞 ℚ) ℚ).nontrivial
  let e := Module.finrank ℚ F
  let m := e * H.index
  have he : 0 < e := Module.finrank_pos
  have hm : 0 < m := Nat.mul_pos he (Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero)
  apply same_subgroup (Q := (powMonoidHom m : Z →* Z).range) _ _ (levels m hm)
  · rintro _ ⟨x,rfl⟩
    obtain ⟨a,rfl⟩ := hv x
    refine ⟨Units.map (algebraMap A (A ⊗[ℚ] F)).toMonoidHom (a ^ H.index),?_⟩
    change v _ = (v a) ^ m
    rw [← map_pow]
    apply congrArg v
    apply Units.ext
    change Algebra.norm A (algebraMap A (A ⊗[ℚ] F) (a.val ^ H.index)) = a.val ^ m
    rw [Algebra.norm_algebraMap, Module.finrank_baseChange, ← pow_mul, Nat.mul_comm]
  · rintro _ ⟨x,rfl⟩
    obtain ⟨t,ht⟩ := H.index_map_dvd hd
    have hin := (H.map d).pow_mem ((H.map d).pow_index_mem x) (t * e)
    change x ^ m ∈ H.map d
    rw [← pow_mul] at hin
    convert hin using 2 <;> dsimp only [m] <;> rw [ht] <;> ring

private theorem finite_test {Z : Type*} [CommGroup Z] [TopologicalSpace Z] [IsTopologicalGroup Z] {U : Type*} [CommGroup U] [TopologicalSpace U] (f : U →* Z)
    (cont : Continuous f) {S T : Subgroup U} (h : closure (S : Set U)=closure (T : Set U))
    (n : ℕ) (_hn : 0<n) (ho : IsOpen ((powMonoidHom n : Z →* Z).range : Set Z)) :
    let q := QuotientGroup.mk' (powMonoidHom n : Z →* Z).range
    (S.map f).map q=(T.map f).map q := by
  let N := (powMonoidHom n : Z →* Z).range
  letI : DiscreteTopology (Z ⧸ N) := QuotientGroup.discreteTopology ho
  let g := (QuotientGroup.mk' N).comp f
  have cg : Continuous g := continuous_quot_mk.comp cont
  have eq (B : Set U) : g '' closure B = g '' B := by
    apply le_antisymm _ (image_mono subset_closure)
    exact (image_closure_subset_closure_image cg).trans (closure_minimal (by rfl) (isClosed_discrete _))
  dsimp only
  rw [Subgroup.map_map,Subgroup.map_map]
  apply SetLike.coe_injective
  change g '' (S : Set U)=g '' (T : Set U)
  rw [←eq, h, eq]





theorem deriveRationalRayNormComparison : (
(let R := ∀ n:ℕ+,ZMod (n:ℕ)
  let Z := (Int.castRingHom R).range.topologicalClosure
  let G := Gal(SeparableClosure ℚ/ℚ)
  let A := AdeleRing (𝓞 ℚ) ℚ
  ∃ d:G →* Zˣ, Continuous d ∧ Function.Surjective d ∧
  ∃ v:Aˣ →* Zˣ, Function.Surjective v ∧ (∀ x:ℚˣ, v (Units.map (algebraMap ℚ A).toMonoidHom x)=1) ∧
  ∀ H : ClosedSubgroup G, H.toSubgroup.FiniteIndex →
    let F:=IntermediateField.fixedField H.toSubgroup
    closure ((v.comp (Units.map (Algebra.norm A (S:=A⊗[ℚ]F)))).range : Set Zˣ)=closure (H.toSubgroup.map d : Set Zˣ)) ∧ (∀ (m : ℕ), (2 < m) → ∀ (v:HeightOneSpectrum (𝓞 ℚ)) (n:ℕ),
  let A:=AdeleRing (𝓞 ℚ) ℚ
  ∀ z:Aˣ, z.val.1=1 → (∀ w:HeightOneSpectrum (𝓞 ℚ), w≠v → z.val.2 w=1) →
  v.asIdeal.absNorm.Coprime m → -WithZero.log (Valued.v (z.val.2 v))=(n:ℤ) →
  z∈(Units.map (algebraMap ℚ A).toMonoidHom).range ⊔
    (Units.map (Algebra.norm A (S:=A⊗[ℚ]CyclotomicField m ℚ))).range →
  m ∣ v.asIdeal.absNorm ^ n - 1)
) → (
  let R := ∀ n:ℕ+,ZMod (n:ℕ)
  let Z := (Int.castRingHom R).range.topologicalClosure
  (∃ f : Zˣ →* Multiplicative Z, Continuous f ∧ Function.Surjective f) ∧
    ∀ n:ℕ, 0<n → IsOpen ((powMonoidHom n : Multiplicative Z →* Multiplicative Z).range : Set (Multiplicative Z))
) → OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H1_R1_H2_R1.H1 := by
  rintro ⟨⟨d,cd,sd,v,sv,kill,close⟩,obstruction⟩ ⟨⟨f,cf,sf⟩,powers⟩
  refine ⟨⟨f.comp d,cf.comp cd,sf.comp sd,f.comp v,sf.comp sv,?_,?_⟩,obstruction⟩
  · intro x
    exact (congrArg f (kill x)).trans f.map_one
  · intro H hi F
    letI := hi
    let Ω := SeparableClosure ℚ
    letI : IsGalois ℚ Ω := @IsSepClosure.isGalois ℚ _ Ω _ ((separableClosure ℚ (AlgebraicClosure ℚ)).algebra)
      (separableClosure.isSepClosure ℚ (AlgebraicClosure ℚ))
    letI : FiniteDimensional ℚ F := (InfiniteGalois.isOpen_iff_finite F).mp (by
      change IsOpen (((IntermediateField.fixedField H.toSubgroup).fixingSubgroup : Subgroup (Gal(SeparableClosure ℚ/ℚ))) : Set (Gal(SeparableClosure ℚ/ℚ)))
      rw [InfiniteGalois.fixingSubgroup_fixedField H]
      exact H.toSubgroup.isOpen_of_isClosed_of_finiteIndex H.isClosed')
    apply norm_images H.toSubgroup (f.comp d) (sf.comp sd) F (f.comp v) (sf.comp sv)
    intro n hn
    have eq := finite_test f cf (close H hi) n hn (powers n hn)
    simpa only [←MonoidHom.range_comp,Subgroup.map_map,MonoidHom.comp_assoc] using eq


end OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H1_R1_H2_R1_H1_R1_H1_R1

end

section
open NumberField IsDedekindDomain
open scoped NumberField Classical TensorProduct IsMulCommutative
open Set

 
namespace OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H1_R1_H2_R1_H1_R1_H1_R1_H1_R1
open NumberField IsDedekindDomain
open scoped NumberField Classical TensorProduct IsMulCommutative






theorem deriveRationalPrimeNormImages : (
  let Z := (Int.castRingHom (∀ n:ℕ+,ZMod (n:ℕ))).range.topologicalClosure
  let ev (m:ℕ+) := Units.map (((Pi.evalRingHom (fun i:ℕ+ => ZMod (i:ℕ)) m).comp Z.subtype).toMonoidHom)
  let G:=Gal(SeparableClosure ℚ/ℚ)
  ∃ d:G →* Zˣ, Continuous d ∧ Function.Surjective d ∧
    ∀ H:ClosedSubgroup G, H.toSubgroup.FiniteIndex →
    let F:=IntermediateField.fixedField H.toSubgroup
    ∀ [NumberField F] (m:ℕ+), (H.toSubgroup.map d).map (ev m)=Subgroup.closure {a:(ZMod (m:ℕ))ˣ | ∃ v:HeightOneSpectrum (𝓞 F), (a:ZMod (m:ℕ))=v.asIdeal.absNorm}
) → (
  let Z := (Int.castRingHom (∀ n:ℕ+,ZMod (n:ℕ))).range.topologicalClosure
  let ev (m:ℕ+) := Units.map (((Pi.evalRingHom (fun i:ℕ+ => ZMod (i:ℕ)) m).comp Z.subtype).toMonoidHom)
  let A:=AdeleRing (𝓞 ℚ) ℚ
  ∃ v:Aˣ →* Zˣ, Function.Surjective v ∧ (∀ x:ℚˣ, v (Units.map (algebraMap ℚ A).toMonoidHom x)=1) ∧
  (∀ (m:ℕ+) (p:HeightOneSpectrum (𝓞 ℚ)) (n:ℕ) (z:Aˣ), z.val.1=1 →
    (∀ w:HeightOneSpectrum (𝓞 ℚ), w≠p → z.val.2 w=1) → p.asIdeal.absNorm.Coprime m.val →
    -WithZero.log (Valued.v (z.val.2 p))=(n:ℤ) → ((ev m (v z)).val:ZMod m.val)=(p.asIdeal.absNorm:ZMod m.val)^n) ∧
  ∀ (F:Type) [Field F] [NumberField F] (m:ℕ+),
    (v.comp (Units.map (Algebra.norm A (S:=A⊗[ℚ]F)))).range.map (ev m)=Subgroup.closure {a:(ZMod (m:ℕ))ˣ | ∃ v:HeightOneSpectrum (𝓞 F), (a:ZMod (m:ℕ))=v.asIdeal.absNorm}
) → (
  let Z := (Int.castRingHom (∀ n:ℕ+,ZMod (n:ℕ))).range.topologicalClosure
  let ev (m:ℕ+) := Units.map (((Pi.evalRingHom (fun i:ℕ+ => ZMod (i:ℕ)) m).comp Z.subtype).toMonoidHom)
  ∀ (S T:Subgroup Zˣ), (∀ m:ℕ+, S.map (ev m)=T.map (ev m)) → closure (S : Set Zˣ)=closure (T : Set Zˣ)
) → (
∀ (m : ℕ), (2 < m) → let F:=CyclotomicField m ℚ
  ∀ (p:HeightOneSpectrum (𝓞 F)), p.asIdeal.absNorm.Coprime m → (p.asIdeal.absNorm:ZMod m)=1
) → (
(let R := ∀ n:ℕ+,ZMod (n:ℕ)
  let Z := (Int.castRingHom R).range.topologicalClosure
  let G := Gal(SeparableClosure ℚ/ℚ)
  let A := AdeleRing (𝓞 ℚ) ℚ
  ∃ d:G →* Zˣ, Continuous d ∧ Function.Surjective d ∧
  ∃ v:Aˣ →* Zˣ, Function.Surjective v ∧ (∀ x:ℚˣ, v (Units.map (algebraMap ℚ A).toMonoidHom x)=1) ∧
  ∀ H : ClosedSubgroup G, H.toSubgroup.FiniteIndex →
    let F:=IntermediateField.fixedField H.toSubgroup
    closure ((v.comp (Units.map (Algebra.norm A (S:=A⊗[ℚ]F)))).range : Set Zˣ)=closure (H.toSubgroup.map d : Set Zˣ)) ∧ (∀ (m : ℕ), (2 < m) → ∀ (v:HeightOneSpectrum (𝓞 ℚ)) (n:ℕ),
  let A:=AdeleRing (𝓞 ℚ) ℚ
  ∀ z:Aˣ, z.val.1=1 → (∀ w:HeightOneSpectrum (𝓞 ℚ), w≠v → z.val.2 w=1) →
  v.asIdeal.absNorm.Coprime m → -WithZero.log (Valued.v (z.val.2 v))=(n:ℤ) →
  z∈(Units.map (algebraMap ℚ A).toMonoidHom).range ⊔
    (Units.map (Algebra.norm A (S:=A⊗[ℚ]CyclotomicField m ℚ))).range →
  m ∣ v.asIdeal.absNorm ^ n - 1)
) := by
  rintro ⟨d,cd,sd,gal⟩ ⟨v,sv,kill,point,norms⟩ levels cyclo
  constructor
  ·
    refine ⟨d,cd,sd,v,sv,kill,?_⟩
    intro H hi F
    letI := hi
    let Ω:=SeparableClosure ℚ
    letI : IsGalois ℚ Ω := @IsSepClosure.isGalois ℚ _ Ω _ ((separableClosure ℚ (AlgebraicClosure ℚ)).algebra)
      (separableClosure.isSepClosure ℚ (AlgebraicClosure ℚ))
    letI : FiniteDimensional ℚ F := (InfiniteGalois.isOpen_iff_finite F).mp (by
      change IsOpen (((IntermediateField.fixedField H.toSubgroup).fixingSubgroup : Subgroup (Gal(SeparableClosure ℚ/ℚ))) : Set (Gal(SeparableClosure ℚ/ℚ)))
      rw [InfiniteGalois.fixingSubgroup_fixedField H]
      exact H.toSubgroup.isOpen_of_isClosed_of_finiteIndex H.isClosed')
    letI : NumberField F := NumberField.of_module_finite ℚ F
    apply levels
    intro m
    exact (norms F m).trans (gal H hi m).symm
  · intro m hm p n A z real away cop ord hz
    let M : ℕ+ := ⟨m,by omega⟩
    let F:=CyclotomicField m ℚ
    let Z:=(Int.castRingHom (∀ i:ℕ+,ZMod (i:ℕ))).range.topologicalClosure
    let ev:=Units.map (((Pi.evalRingHom (fun i:ℕ+ => ZMod (i:ℕ)) M).comp Z.subtype).toMonoidHom)
    let s:=ev.comp v
    have zero : Subgroup.closure {a:(ZMod m)ˣ | ∃ w:HeightOneSpectrum (𝓞 F), (a:ZMod m)=w.asIdeal.absNorm} ≤ ⊥ := by
      rw [Subgroup.closure_le]
      rintro a ⟨w,eq⟩
      have hc : w.asIdeal.absNorm.Coprime m := (ZMod.isUnit_iff_coprime _ _).mp (eq ▸ a.isUnit)
      exact Units.ext (eq.trans (cyclo m hm w hc))
    have small : (Units.map (algebraMap ℚ A).toMonoidHom).range ⊔
        (Units.map (Algebra.norm A (S:=A⊗[ℚ]F))).range ≤ s.ker := by
      apply sup_le
      · rintro _ ⟨x,rfl⟩
        exact (congrArg ev (kill x)).trans ev.map_one
      · rintro _ ⟨x,rfl⟩
        apply zero
        exact (norms F M).le ⟨_,⟨x,rfl⟩,rfl⟩
    have one : s z=1 := small hz
    have val := point M p n z real away cop ord
    change (s z).val=(p.asIdeal.absNorm:ZMod m)^n at val
    rw [one,Units.val_one] at val
    have pos : 1 ≤ p.asIdeal.absNorm ^ n := Nat.pos_of_ne_zero (pow_ne_zero n (Ideal.absNorm_eq_zero_iff.not.mpr p.ne_bot))
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    rw [Nat.cast_sub pos,Nat.cast_pow,Nat.cast_one]
    exact sub_eq_zero.mpr val.symm

end OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H1_R1_H2_R1_H1_R1_H1_R1_H1_R1

end

section
open NumberField IsDedekindDomain
open scoped NumberField Classical TensorProduct IsMulCommutative
open scoped NumberField TensorProduct Classical

 
namespace OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H1_R1_H2_R1_H1_R1_H1_R1_H1_R1_H2_R1
open NumberField IsDedekindDomain
open scoped NumberField TensorProduct Classical





theorem upper (F : Type) [Field F] [NumberField F] (m : ℕ+) (p : HeightOneSpectrum (𝓞 ℚ))
    (h : p.asIdeal.absNorm.Coprime m.val)
    (k : ℤ) (hk : k ∈ AddSubgroup.closure {n : ℤ | ∃ w : HeightOneSpectrum (𝓞 F),
      w.asIdeal.LiesOver p.asIdeal ∧ n = (w.asIdeal.inertiaDeg (𝓞 ℚ) : ℤ)}) :
    (ZMod.unitOfCoprime p.asIdeal.absNorm h)^k ∈ Subgroup.closure
      {a : (ZMod m.val)ˣ | ∃ w : HeightOneSpectrum (𝓞 F), (a : ZMod m.val) = w.asIdeal.absNorm} := by
  let u := ZMod.unitOfCoprime p.asIdeal.absNorm h
  let S := Subgroup.closure {a : (ZMod m.val)ˣ | ∃ w : HeightOneSpectrum (𝓞 F), (a : ZMod m.val)=w.asIdeal.absNorm}
  let C : AddSubgroup ℤ := (S.comap (zpowersHom ((ZMod m.val)ˣ) u)).toAddSubgroup'
  change k ∈ C
  apply (AddSubgroup.closure_le C).2 _ hk
  rintro _ ⟨w,hw,rfl⟩
  letI := hw
  change u ^ (w.asIdeal.inertiaDeg (𝓞 ℚ) : ℤ) ∈ S
  rw [zpow_natCast]
  apply Subgroup.subset_closure
  refine ⟨w,?_⟩
  rw [Units.val_pow_eq_pow_val,ZMod.coe_unitOfCoprime,←Nat.cast_pow,Ideal.absNorm_pow_inertiaDeg p.asIdeal w.asIdeal]

theorem lower (F : Type) [Field F] [NumberField F] (m : ℕ+) (w : HeightOneSpectrum (𝓞 F))
    (a : (ZMod m.val)ˣ) (ha : (a : ZMod m.val) = w.asIdeal.absNorm) :
    ∃ p : HeightOneSpectrum (𝓞 ℚ), ∃ h : p.asIdeal.absNorm.Coprime m.val,
      w.asIdeal.LiesOver p.asIdeal ∧ (a : ZMod m.val) =
        (p.asIdeal.absNorm : ZMod m.val)^(w.asIdeal.inertiaDeg (𝓞 ℚ)) := by
  let p := HeightOneSpectrum.under (𝓞 ℚ) w
  letI : w.asIdeal.LiesOver p.asIdeal := ⟨rfl⟩
  have h : w.asIdeal.absNorm.Coprime m.val := (ZMod.isUnit_iff_coprime _ _).mp (ha ▸ a.isUnit)
  have norm := Ideal.absNorm_pow_inertiaDeg p.asIdeal w.asIdeal
  have dvd : p.asIdeal.absNorm ∣ w.asIdeal.absNorm :=
    norm ▸ dvd_pow_self _ (Ideal.inertiaDeg_pos w.asIdeal (𝓞 ℚ)).ne'
  exact ⟨p,h.of_dvd_left dvd,inferInstance,ha.trans (by rw [←Nat.cast_pow,norm])⟩

theorem deriveRationalIdelicPrimeRange : (
  let Z := (Int.castRingHom (∀ n:ℕ+,ZMod (n:ℕ))).range.topologicalClosure
  let ev (m:ℕ+) := Units.map (((Pi.evalRingHom (fun i:ℕ+ => ZMod (i:ℕ)) m).comp Z.subtype).toMonoidHom)
  let A:=AdeleRing (𝓞 ℚ) ℚ
  ∃ v:Aˣ →* Zˣ, Function.Surjective v ∧ (∀ x:ℚˣ, v (Units.map (algebraMap ℚ A).toMonoidHom x)=1) ∧
  (∀ (m:ℕ+) (p:HeightOneSpectrum (𝓞 ℚ)) (n:ℕ) (z:Aˣ), z.val.1=1 →
    (∀ w:HeightOneSpectrum (𝓞 ℚ), w≠p → z.val.2 w=1) → p.asIdeal.absNorm.Coprime m.val →
    -WithZero.log (Valued.v (z.val.2 p))=(n:ℤ) → ((ev m (v z)).val:ZMod m.val)=(p.asIdeal.absNorm:ZMod m.val)^n) ∧
  ∀ (m:ℕ+) (z:Aˣ), (let P:=HeightOneSpectrum (𝓞 ℚ)
    (∀ (w:InfinitePlace ℚ) (h:w.IsReal), 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal h (z.val.1 w)) ∧
  ∀ p:P, let n:=m.val.factorization (Rat.HeightOneSpectrum.natGenerator p)
    n≠0 → ∃ u:(p.adicCompletionIntegers ℚ)ˣ, (u.val : p.adicCompletion ℚ)=z.val.2 p ∧
      (u.val-1)∈(IsLocalRing.maximalIdeal (p.adicCompletionIntegers ℚ))^n) →
    ∀ C:Subgroup (ZMod m.val)ˣ, (∀ (p:HeightOneSpectrum (𝓞 ℚ)) (u:(ZMod m.val)ˣ), (u:ZMod m.val)=p.asIdeal.absNorm →
      u ^ (-WithZero.log (Valued.v (z.val.2 p))) ∈ C) → ev m (v z) ∈ C
) → (
  let A := AdeleRing (𝓞 ℚ) ℚ
  let P := HeightOneSpectrum (𝓞 ℚ)
  ∀ (F:Type) [Field F] [NumberField F] (m:ℕ+) (y:(A⊗[ℚ]F)ˣ),
    let N:=Units.map (Algebra.norm A (S:=A⊗[ℚ]F))
    ∃ t:(A⊗[ℚ]F)ˣ, N y / N t ∈ (Units.map (algebraMap ℚ A).toMonoidHom).range ∧
    ((∀ (w:InfinitePlace ℚ) (h:w.IsReal), 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal h ((N t).val.1 w)) ∧
  ∀ p:P, let n:=m.val.factorization (Rat.HeightOneSpectrum.natGenerator p)
    n≠0 → ∃ u:(p.adicCompletionIntegers ℚ)ˣ, (u.val : p.adicCompletion ℚ)=(N t).val.2 p ∧
      (u.val-1)∈(IsLocalRing.maximalIdeal (p.adicCompletionIntegers ℚ))^n)
) → (
∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 ℚ)),
    let K := v.adicCompletion ℚ
    Set.range (fun x : (K ⊗[ℚ] F)ˣ => -WithZero.log (Valued.v (Algebra.norm K x.val))) =
      (↑(AddSubgroup.closure {n : ℤ | ∃ w : HeightOneSpectrum (𝓞 F),
        w.asIdeal.LiesOver v.asIdeal ∧ n = (w.asIdeal.inertiaDeg (𝓞 ℚ) : ℤ)}) : Set ℤ)
) → (
∀ (F : Type) [Field F] [NumberField F] (p : HeightOneSpectrum (𝓞 ℚ)),
  let K := p.adicCompletion ℚ
  let A := AdeleRing (𝓞 ℚ) ℚ
  let N := Units.map (Algebra.norm A (S := A ⊗[ℚ] F))
  (∀ y : (A ⊗[ℚ] F)ˣ, ∃ x : (K ⊗[ℚ] F)ˣ, (N y).val.2 p = Algebra.norm K x.val) ∧
  (∀ x : (K ⊗[ℚ] F)ˣ, ∃ y : (A ⊗[ℚ] F)ˣ, (N y).val.1 = 1 ∧
    (∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ p → (N y).val.2 w = 1) ∧ (N y).val.2 p = Algebra.norm K x.val)
) → (
  let Z := (Int.castRingHom (∀ n:ℕ+,ZMod (n:ℕ))).range.topologicalClosure
  let ev (m:ℕ+) := Units.map (((Pi.evalRingHom (fun i:ℕ+ => ZMod (i:ℕ)) m).comp Z.subtype).toMonoidHom)
  let A:=AdeleRing (𝓞 ℚ) ℚ
  ∃ v:Aˣ →* Zˣ, Function.Surjective v ∧ (∀ x:ℚˣ, v (Units.map (algebraMap ℚ A).toMonoidHom x)=1) ∧
  (∀ (m:ℕ+) (p:HeightOneSpectrum (𝓞 ℚ)) (n:ℕ) (z:Aˣ), z.val.1=1 →
    (∀ w:HeightOneSpectrum (𝓞 ℚ), w≠p → z.val.2 w=1) → p.asIdeal.absNorm.Coprime m.val →
    -WithZero.log (Valued.v (z.val.2 p))=(n:ℤ) → ((ev m (v z)).val:ZMod m.val)=(p.asIdeal.absNorm:ZMod m.val)^n) ∧
  ∀ (F:Type) [Field F] [NumberField F] (m:ℕ+),
    (v.comp (Units.map (Algebra.norm A (S:=A⊗[ℚ]F)))).range.map (ev m)=Subgroup.closure {a:(ZMod (m:ℕ))ˣ | ∃ v:HeightOneSpectrum (𝓞 F), (a:ZMod (m:ℕ))=v.asIdeal.absNorm}
) := by
  rintro ⟨v,surj,kill,point,evaluate⟩ adjust orders proj
  refine ⟨v,surj,kill,point,?_⟩
  intro F _ _ m
  let Z := (Int.castRingHom (∀ n:ℕ+,ZMod (n:ℕ))).range.topologicalClosure
  let ev := Units.map (((Pi.evalRingHom (fun i:ℕ+ => ZMod (i:ℕ)) m).comp Z.subtype).toMonoidHom)
  let A := AdeleRing (𝓞 ℚ) ℚ
  let N := Units.map (Algebra.norm A (S:=A⊗[ℚ]F))
  let S := Subgroup.closure {a : (ZMod m.val)ˣ | ∃ w : HeightOneSpectrum (𝓞 F), (a : ZMod m.val)=w.asIdeal.absNorm}
  change (v.comp N).range.map ev = S
  apply le_antisymm
  · rintro _ ⟨_,⟨b,rfl⟩,rfl⟩
    obtain ⟨t,⟨r,hr⟩,hg⟩ := adjust F m b
    have eq : v (N b) = v (N t) := by
      apply div_eq_one.mp
      rw [←map_div,show N b / N t = _ from hr.symm,kill]
    change ev (v (N b)) ∈ S
    rw [eq]
    apply evaluate m (N t) hg S
    intro p u hu
    have hc : p.asIdeal.absNorm.Coprime m.val := (ZMod.isUnit_iff_coprime _ _).mp (hu ▸ u.isUnit)
    have hu' : u=ZMod.unitOfCoprime p.asIdeal.absNorm hc := Units.ext (hu.trans (ZMod.coe_unitOfCoprime _ hc).symm)
    rw [hu']
    apply upper F m p hc
    apply (Set.ext_iff.mp (orders F p) _).mp
    obtain ⟨x,hx⟩ := (proj F p).1 t
    exact ⟨x,congrArg (fun b => -WithZero.log (Valued.v b)) hx.symm⟩
  · change Subgroup.closure _ ≤ _
    rw [Subgroup.closure_le]
    rintro a ⟨w,ha⟩
    obtain ⟨p,hp,hw,heq⟩ := lower F m w a ha
    let n := w.asIdeal.inertiaDeg (𝓞 ℚ)
    have hn : (n:ℤ) ∈ AddSubgroup.closure {k:ℤ | ∃ s:HeightOneSpectrum (𝓞 F),
        s.asIdeal.LiesOver p.asIdeal ∧ k = (s.asIdeal.inertiaDeg (𝓞 ℚ):ℤ)} :=
      AddSubgroup.subset_closure ⟨w,hw,rfl⟩
    obtain ⟨x,hx⟩ := (Set.ext_iff.mp (orders F p) (n:ℤ)).mpr hn
    obtain ⟨y,real,away,here⟩ := (proj F p).2 x
    refine ⟨v (N y),⟨y,rfl⟩,Units.ext ?_⟩
    exact (point m p n (N y) real away hp (by rw [here]; exact hx)).trans heq.symm

end OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H1_R1_H2_R1_H1_R1_H1_R1_H1_R1_H2_R1

end

namespace OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H1_R1_H2_R1_H1_R1
theorem main : H1 → H2 → H3 → OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H1_R1_H2_R1.H1 :=
  fun v1 v2 v3 =>
    (OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H1_R1_H2_R1_H1_R1_H1_R1.deriveRationalRayNormComparison (OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H1_R1_H2_R1_H1_R1_H1_R1_H1_R1.deriveRationalPrimeNormImages v3.1 (OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H1_R1_H2_R1_H1_R1_H1_R1_H1_R1_H2_R1.deriveRationalIdelicPrimeRange v3.2.1 v2.1 v1.1 v1.2.1) v1.2.2 v2.2) v3.2.2)
end OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H1_R1_H2_R1_H1_R1
