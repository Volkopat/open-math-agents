import OMAReductions.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H1_R1_H1_R1
import Mathlib


/-! Start with a finite support for ramification and ideal classes. Auxiliary split primes separate the local powers of supported units. The principal ideles convert this separation to a subgroup equality. -/

namespace OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H1_R1_H1_R1_H3_R1

section

open NumberField IsDedekindDomain
open scoped NumberField Classical TensorProduct IsMulCommutative

def H1 : Prop :=
  (
∀(D:Type)[Field D][NumberField D](E:IntermediateField D (SeparableClosure D))
   [FiniteDimensional D E][IsGalois D E],
   let p:=Module.finrank D E
   p.Prime → (primitiveRoots p D).Nonempty →
   letI:NumberField E:=NumberField.of_module_finite D E
   let V:=HeightOneSpectrum (𝓞 D)
   let split(v:V):=∀ t:HeightOneSpectrum (𝓞 E),t.asIdeal.LiesOver v.asIdeal → ∀ g:Gal(E/D),
     HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapAlgEquiv g).toRingEquiv t=t → g=1
   let A:=AdeleRing (𝓞 D) D
   let J(F:Finset V):=Subgroup.closure {a:Aˣ | ∀ v:V,v∉F → a.val.2 v∈v.adicCompletionIntegers D ∧ (a⁻¹).val.2 v∈v.adicCompletionIntegers D}
   let j:=Units.map (algebraMap D A).toMonoidHom
   ∀ B:Finset V,∃ S T:Finset V,B⊆S ∧ (∀ v∈T,split v) ∧ Disjoint S T ∧
     T.card+1=Nat.card (InfinitePlace D)+S.card ∧ (∀ v:V,v.asIdeal ∣ Ideal.span {(p:𝓞 D)} → v∈S) ∧ j.range⊔J S=⊤ ∧ (∀ x:(S:Set V).unit D, (∀ v:T, ∃ y:v.val.adicCompletion D,y^p=(x.val.val:v.val.adicCompletion D)) →
        ∃ z:E,z^p=algebraMap D E x.val.val)
)

end

section

open NumberField IsDedekindDomain
open scoped NumberField Classical TensorProduct IsMulCommutative

def H2 : Prop :=
  (
∀(D:Type)[Field D][NumberField D](E:IntermediateField D (SeparableClosure D))
   [FiniteDimensional D E][IsGalois D E],
   let p:=Module.finrank D E
   p.Prime → (primitiveRoots p D).Nonempty →
   letI:NumberField E:=NumberField.of_module_finite D E
   let V:=HeightOneSpectrum (𝓞 D)
   let A:=AdeleRing (𝓞 D) D
   let unram(v:V):=∀ t:HeightOneSpectrum (𝓞 E),t.asIdeal.LiesOver v.asIdeal → Algebra.IsUnramifiedAt (𝓞 D) t.asIdeal
   let J(F:Finset V):=Subgroup.closure {a:Aˣ | ∀ v:V,v∉F → a.val.2 v∈v.adicCompletionIntegers D ∧ (a⁻¹).val.2 v∈v.adicCompletionIntegers D}
   let j:=Units.map (algebraMap D A).toMonoidHom
   ∃ B:Finset V,(∀ v:V,v∉B → unram v) ∧
     (∀ v:V,v.asIdeal ∣ Ideal.span {(p:𝓞 D)} → v∈B) ∧ j.range⊔J B=⊤
) ∧
  (
∀(D:Type)[Field D][NumberField D](E:IntermediateField D (SeparableClosure D))
   [FiniteDimensional D E][IsGalois D E],
   let p:=Module.finrank D E
   p.Prime → (primitiveRoots p D).Nonempty →
   letI:NumberField E:=NumberField.of_module_finite D E
   let V:=HeightOneSpectrum (𝓞 D)
   ∀ S T:Finset V,Disjoint S T → T.card+1=Nat.card (InfinitePlace D)+S.card →
     (∀ v:V,v.asIdeal ∣ Ideal.span {(p:𝓞 D)} → v∈S) → (∀ x:(S:Set V).unit D, (∀ v:T, ∃ y:v.val.adicCompletion D,y^p=(x.val.val:v.val.adicCompletion D)) →
        ∃ z:E,z^p=algebraMap D E x.val.val) → (∀ u:(∀ v:T,(v.val.adicCompletionIntegers D)ˣ),∃ x:(S:Set V).unit D,∀ v:T,
      ∃ y:(v.val.adicCompletionIntegers D)ˣ, ((y.val.val:v.val.adicCompletion D)^p)*(x.val.val:v.val.adicCompletion D)=(u v).val.val)
)

end

section

open NumberField IsDedekindDomain
open scoped NumberField TensorProduct Classical

def H3 : Prop :=
  (
∀(D M:Type)[Field D][NumberField D][Field M][Algebra D M][FiniteDimensional D M][IsGalois D M][IsCyclic Gal(M/D)]
    (p:ℕ),0<p → let V:=HeightOneSpectrum (𝓞 D)
    let A:=AdeleRing (𝓞 D) D
   let J(F:Finset V):=Subgroup.closure {a:Aˣ | ∀ v:V,v∉F → a.val.2 v∈v.adicCompletionIntegers D ∧ (a⁻¹).val.2 v∈v.adicCompletionIntegers D}
   let j:=Units.map (algebraMap D A).toMonoidHom
    ∀S T:Finset V,Disjoint S T → j.range⊔J S=⊤ → (∀ u:(∀ v:T,(v.val.adicCompletionIntegers D)ˣ),∃ x:(S:Set V).unit D,∀ v:T,
      ∃ y:(v.val.adicCompletionIntegers D)ˣ, ((y.val.val:v.val.adicCompletion D)^p)*(x.val.val:v.val.adicCompletion D)=(u v).val.val) →
    (let norm (F:Type) [Field F] [Algebra D F]:=(Units.map (Algebra.norm F (S:=F⊗[D]M))).range
    (∀w:InfinitePlace D,norm w.Completion=⊤) ∧ (∀v∈S,norm (v.adicCompletion D)=⊤) ∧
    (∀v∈T,(powMonoidHom p:(v.adicCompletion D)ˣ→*(v.adicCompletion D)ˣ).range≤norm (v.adicCompletion D)) ∧
    (∀v:V,v∉S∪T → (Units.map (v.adicCompletionIntegers D).subtype.toMonoidHom).range≤norm (v.adicCompletion D))) → j.range⊔(Units.map (Algebra.norm A (S:=A⊗[D]M))).range=⊤
)

end

section

open NumberField IsDedekindDomain
open scoped NumberField TensorProduct Classical
open scoped NumberField Classical TensorProduct IsMulCommutative

def H4 : Prop :=
  (
∀(D:Type)[Field D][NumberField D](p:ℕ),p.Prime → (primitiveRoots p D).Nonempty →
   let V:=HeightOneSpectrum (𝓞 D)
   ∀ S T:Finset V,(∀v:V,v.asIdeal ∣ Ideal.span {(p:𝓞 D)} → v∈S) →
    ∀x:(↑(S∪T):Set V).unit D,(∀w:InfinitePlace D,∃ y:w.Completion,y^p=(x.val.val:w.Completion)) →
    (∀v∈S,∃y:v.adicCompletion D,y^p=(x.val.val:v.adicCompletion D)) →
    ∃ M:IntermediateField D (SeparableClosure D),FiniteDimensional D M ∧ IsGalois D M ∧ IsCyclic Gal(M/D) ∧
       (∃z:M,z^p=algebraMap D M x.val.val) ∧ let norm (F:Type) [Field F] [Algebra D F]:=(Units.map (Algebra.norm F (S:=F⊗[D]M))).range
    (∀w:InfinitePlace D,norm w.Completion=⊤) ∧ (∀v∈S,norm (v.adicCompletion D)=⊤) ∧
    (∀v∈T,(powMonoidHom p:(v.adicCompletion D)ˣ→*(v.adicCompletion D)ˣ).range≤norm (v.adicCompletion D)) ∧
    (∀v:V,v∉S∪T → (Units.map (v.adicCompletionIntegers D).subtype.toMonoidHom).range≤norm (v.adicCompletion D))
) ∧
  (
∀(D:Type)[Field D][NumberField D](p:ℕ),0<p →
   let V:=HeightOneSpectrum (𝓞 D)
   let A:=AdeleRing (𝓞 D) D
   let U(S T:Finset V):=Subgroup.closure {a:Aˣ |
     (∀ w:InfinitePlace D,∃ y:w.Completion,y^p=a.val.1 w) ∧
     (∀ v∈S,∃ y:v.adicCompletion D,y^p=a.val.2 v) ∧
     ∀ v:V,v∉S∪T → a.val.2 v∈v.adicCompletionIntegers D ∧ (a⁻¹).val.2 v∈v.adicCompletionIntegers D}
   let J(F:Finset V):=Subgroup.closure {a:Aˣ | ∀ v:V,v∉F → a.val.2 v∈v.adicCompletionIntegers D ∧ (a⁻¹).val.2 v∈v.adicCompletionIntegers D}
   let j:=Units.map (algebraMap D A).toMonoidHom
   ∀ S T:Finset V,let W:=(↑(S∪T):Set V).unit D
     (J (S∪T)).comap j=W ∧ ((∀ x:W,(∀ w:InfinitePlace D,∃ y:w.Completion,y^p=(x.val.val:w.Completion)) →
       (∀ v∈S,∃ y:v.adicCompletion D,y^p=(x.val.val:v.adicCompletion D)) → ∃ y:W,y^p=x) → (U S T).comap j=(powMonoidHom p:W→*W).range.map W.subtype)
)

end

end OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H1_R1_H1_R1_H3_R1

section
open NumberField IsDedekindDomain
open scoped NumberField TensorProduct Classical
open scoped NumberField Classical TensorProduct IsMulCommutative

 
namespace OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H1_R1_H1_R1_H3_R1_H1_R1_H3_R1
open NumberField IsDedekindDomain
open scoped NumberField Classical TensorProduct IsMulCommutative




theorem deriveAuxiliarySplitPrimes : (
∀(D:Type)[Field D][NumberField D](E:IntermediateField D (SeparableClosure D))
   [FiniteDimensional D E][IsGalois D E],
   let p:=Module.finrank D E
   p.Prime → (primitiveRoots p D).Nonempty →
   letI:NumberField E:=NumberField.of_module_finite D E
   let V:=HeightOneSpectrum (𝓞 D)
   let A:=AdeleRing (𝓞 D) D
   let unram(v:V):=∀ t:HeightOneSpectrum (𝓞 E),t.asIdeal.LiesOver v.asIdeal → Algebra.IsUnramifiedAt (𝓞 D) t.asIdeal
   let J(F:Finset V):=Subgroup.closure {a:Aˣ | ∀ v:V,v∉F → a.val.2 v∈v.adicCompletionIntegers D ∧ (a⁻¹).val.2 v∈v.adicCompletionIntegers D}
   let j:=Units.map (algebraMap D A).toMonoidHom
   ∃ B:Finset V,(∀ v:V,v∉B → unram v) ∧
     (∀ v:V,v.asIdeal ∣ Ideal.span {(p:𝓞 D)} → v∈B) ∧ j.range⊔J B=⊤
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
   let split(v:V):=∀ t:HeightOneSpectrum (𝓞 E),t.asIdeal.LiesOver v.asIdeal → ∀ g:Gal(E/D),
     HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapAlgEquiv g).toRingEquiv t=t → g=1
   ∀ B:Finset V,∃ S T:Finset V,B⊆S ∧ (∀ v∈T,split v) ∧ Disjoint S T ∧
     T.card+1=Nat.card (InfinitePlace D)+S.card ∧ let W:=(↑(S∪T):Set V).unit D
     (∀ x:W,(∀ w:InfinitePlace D,∃ y:w.Completion,y^p=(x.val.val:w.Completion)) →
       (∀ v∈S,∃ y:v.adicCompletion D,y^p=(x.val.val:v.adicCompletion D)) → ∃ y:W,y^p=x)
) → (
∀(D:Type)[Field D][NumberField D](p:ℕ),0<p →
   let V:=HeightOneSpectrum (𝓞 D)
   let A:=AdeleRing (𝓞 D) D
   let U(S T:Finset V):=Subgroup.closure {a:Aˣ |
     (∀ w:InfinitePlace D,∃ y:w.Completion,y^p=a.val.1 w) ∧
     (∀ v∈S,∃ y:v.adicCompletion D,y^p=a.val.2 v) ∧
     ∀ v:V,v∉S∪T → a.val.2 v∈v.adicCompletionIntegers D ∧ (a⁻¹).val.2 v∈v.adicCompletionIntegers D}
   let J(F:Finset V):=Subgroup.closure {a:Aˣ | ∀ v:V,v∉F → a.val.2 v∈v.adicCompletionIntegers D ∧ (a⁻¹).val.2 v∈v.adicCompletionIntegers D}
   let j:=Units.map (algebraMap D A).toMonoidHom
   ∀ S T:Finset V,let W:=(↑(S∪T):Set V).unit D
     (J (S∪T)).comap j=W ∧ ((∀ x:W,(∀ w:InfinitePlace D,∃ y:w.Completion,y^p=(x.val.val:w.Completion)) →
       (∀ v∈S,∃ y:v.adicCompletion D,y^p=(x.val.val:v.adicCompletion D)) → ∃ y:W,y^p=x) → (U S T).comap j=(powMonoidHom p:W→*W).range.map W.subtype)
) → OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H1_R1_H1_R1.H3 := by
  intro seed separate principal lower
  have separate := separate lower
  intro D _ _ E _ _
  dsimp only
  intro hp hmu
  letI : NumberField E := NumberField.of_module_finite D E
  let p:=Module.finrank D E
  let V:=HeightOneSpectrum (𝓞 D)
  let A:=AdeleRing (𝓞 D) D
  let J(F:Finset V):=Subgroup.closure {a:Aˣ | ∀ v:V,v∉F → a.val.2 v∈v.adicCompletionIntegers D ∧ (a⁻¹).val.2 v∈v.adicCompletionIntegers D}
  let j:=Units.map (algebraMap D A).toMonoidHom
  obtain ⟨B,hun,hpB,hB⟩:=seed D E hp hmu
  obtain ⟨S,T,hBS,hspl,hd,hcard,hpow⟩:=separate D E hp hmu B
  obtain ⟨hs,hu⟩:=principal D p hp.pos S T
  have inclusion:B⊆S∪T:=hBS.trans Finset.subset_union_left
  have mono:J B≤J (S∪T):=Subgroup.closure_mono fun a ha w hw=>ha w (fun h=>hw (inclusion h))
  refine ⟨S,T,hspl,fun v hv=>hun v (fun h=>hv (inclusion h)),hd,hcard,fun v hv=>hBS (hpB v hv),?_,hs,hu hpow⟩
  exact top_unique (hB ▸ (show j.range⊔J B≤j.range⊔J (S∪T) from sup_le_sup_left mono _))

end OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H1_R1_H1_R1_H3_R1_H1_R1_H3_R1

end

section
open NumberField IsDedekindDomain
open scoped NumberField Classical TensorProduct IsMulCommutative

 
namespace OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H1_R1_H1_R1_H3_R1_H1_R1_H3_R1_H2_R1
open NumberField IsDedekindDomain
open scoped NumberField Classical TensorProduct IsMulCommutative



theorem deriveLocalUnitApproximation : (
∀(D:Type)[Field D][NumberField D](E:IntermediateField D (SeparableClosure D))
   [FiniteDimensional D E][IsGalois D E],
   let p:=Module.finrank D E
   p.Prime → (primitiveRoots p D).Nonempty →
   letI:NumberField E:=NumberField.of_module_finite D E
   let V:=HeightOneSpectrum (𝓞 D)
   let split(v:V):=∀ t:HeightOneSpectrum (𝓞 E),t.asIdeal.LiesOver v.asIdeal → ∀ g:Gal(E/D),
     HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapAlgEquiv g).toRingEquiv t=t → g=1
   let A:=AdeleRing (𝓞 D) D
   let J(F:Finset V):=Subgroup.closure {a:Aˣ | ∀ v:V,v∉F → a.val.2 v∈v.adicCompletionIntegers D ∧ (a⁻¹).val.2 v∈v.adicCompletionIntegers D}
   let j:=Units.map (algebraMap D A).toMonoidHom
   ∀ B:Finset V,∃ S T:Finset V,B⊆S ∧ (∀ v∈T,split v) ∧ Disjoint S T ∧
     T.card+1=Nat.card (InfinitePlace D)+S.card ∧ (∀ v:V,v.asIdeal ∣ Ideal.span {(p:𝓞 D)} → v∈S) ∧ j.range⊔J S=⊤ ∧ (∀ u:(∀ v:T,(v.val.adicCompletionIntegers D)ˣ),∃ x:(S:Set V).unit D,∀ v:T,
      ∃ y:(v.val.adicCompletionIntegers D)ˣ, ((y.val.val:v.val.adicCompletion D)^p)*(x.val.val:v.val.adicCompletion D)=(u v).val.val)
) → (
(∀(D N:Type)[Field D][NumberField D][Field N][NumberField N][Algebra D N]
    [FiniteDimensional D N][IsGalois D N][IsCyclic Gal(N/D)],
    let A:=AdeleRing (𝓞 D) D
    (Units.map (algebraMap D A).toMonoidHom).range ⊔ (Units.map (Algebra.norm A (S:=A⊗[D]N))).range=⊤ →
    Module.finrank D N=1) →
  ∀(D:Type)[Field D][NumberField D](p:ℕ),p.Prime → (primitiveRoots p D).Nonempty →
   let V:=HeightOneSpectrum (𝓞 D)
   let A:=AdeleRing (𝓞 D) D
   let J(F:Finset V):=Subgroup.closure {a:Aˣ | ∀ v:V,v∉F → a.val.2 v∈v.adicCompletionIntegers D ∧ (a⁻¹).val.2 v∈v.adicCompletionIntegers D}
   let j:=Units.map (algebraMap D A).toMonoidHom
   ∀ S T:Finset V,Disjoint S T → ((∀ v:V,v.asIdeal ∣ Ideal.span {(p:𝓞 D)} → v∈S) ∧ j.range⊔J S=⊤) → (∀ u:(∀ v:T,(v.val.adicCompletionIntegers D)ˣ),∃ x:(S:Set V).unit D,∀ v:T,
      ∃ y:(v.val.adicCompletionIntegers D)ˣ, ((y.val.val:v.val.adicCompletion D)^p)*(x.val.val:v.val.adicCompletion D)=(u v).val.val) →
     let W:=(↑(S∪T):Set V).unit D
     (∀ x:W,(∀ w:InfinitePlace D,∃ y:w.Completion,y^p=(x.val.val:w.Completion)) →
       (∀ v∈S,∃ y:v.adicCompletion D,y^p=(x.val.val:v.adicCompletion D)) → ∃ y:W,y^p=x)
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
   let split(v:V):=∀ t:HeightOneSpectrum (𝓞 E),t.asIdeal.LiesOver v.asIdeal → ∀ g:Gal(E/D),
     HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapAlgEquiv g).toRingEquiv t=t → g=1
   ∀ B:Finset V,∃ S T:Finset V,B⊆S ∧ (∀ v∈T,split v) ∧ Disjoint S T ∧
     T.card+1=Nat.card (InfinitePlace D)+S.card ∧ let W:=(↑(S∪T):Set V).unit D
     (∀ x:W,(∀ w:InfinitePlace D,∃ y:w.Completion,y^p=(x.val.val:w.Completion)) →
       (∀ v∈S,∃ y:v.adicCompletion D,y^p=(x.val.val:v.adicCompletion D)) → ∃ y:W,y^p=x)
) := by
  intro choose detect lower
  have detect := detect lower
  intro D _ _ E _ _
  dsimp only
  intro hp hmu B
  obtain ⟨S,T,hBS,split,hd,hc,hs,hJ,sur⟩:=choose D E hp hmu B
  exact ⟨S,T,hBS,split,hd,hc,detect D (Module.finrank D E) hp hmu S T hd ⟨hs,hJ⟩ sur⟩

end OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H1_R1_H1_R1_H3_R1_H1_R1_H3_R1_H2_R1

end

section
open NumberField IsDedekindDomain
open scoped NumberField Classical TensorProduct IsMulCommutative

 
namespace OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H1_R1_H1_R1_H3_R1_H1_R1_H3_R1_H2_R1_H1_R1
open NumberField IsDedekindDomain
open scoped NumberField Classical TensorProduct IsMulCommutative



theorem deriveCyclicRadicalLocalization : (
∀(D:Type)[Field D][NumberField D](E:IntermediateField D (SeparableClosure D))
   [FiniteDimensional D E][IsGalois D E],
   let p:=Module.finrank D E
   p.Prime → (primitiveRoots p D).Nonempty →
   letI:NumberField E:=NumberField.of_module_finite D E
   let V:=HeightOneSpectrum (𝓞 D)
   let split(v:V):=∀ t:HeightOneSpectrum (𝓞 E),t.asIdeal.LiesOver v.asIdeal → ∀ g:Gal(E/D),
     HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapAlgEquiv g).toRingEquiv t=t → g=1
   let A:=AdeleRing (𝓞 D) D
   let J(F:Finset V):=Subgroup.closure {a:Aˣ | ∀ v:V,v∉F → a.val.2 v∈v.adicCompletionIntegers D ∧ (a⁻¹).val.2 v∈v.adicCompletionIntegers D}
   let j:=Units.map (algebraMap D A).toMonoidHom
   ∀ B:Finset V,∃ S T:Finset V,B⊆S ∧ (∀ v∈T,split v) ∧ Disjoint S T ∧
     T.card+1=Nat.card (InfinitePlace D)+S.card ∧ (∀ v:V,v.asIdeal ∣ Ideal.span {(p:𝓞 D)} → v∈S) ∧ j.range⊔J S=⊤ ∧ (∀ x:(S:Set V).unit D, (∀ v:T, ∃ y:v.val.adicCompletion D,y^p=(x.val.val:v.val.adicCompletion D)) →
        ∃ z:E,z^p=algebraMap D E x.val.val)
) → (
∀(D:Type)[Field D][NumberField D](E:IntermediateField D (SeparableClosure D))
   [FiniteDimensional D E][IsGalois D E],
   let p:=Module.finrank D E
   p.Prime → (primitiveRoots p D).Nonempty →
   letI:NumberField E:=NumberField.of_module_finite D E
   let V:=HeightOneSpectrum (𝓞 D)
   ∀ S T:Finset V,Disjoint S T → T.card+1=Nat.card (InfinitePlace D)+S.card →
     (∀ v:V,v.asIdeal ∣ Ideal.span {(p:𝓞 D)} → v∈S) → (∀ x:(S:Set V).unit D, (∀ v:T, ∃ y:v.val.adicCompletion D,y^p=(x.val.val:v.val.adicCompletion D)) →
        ∃ z:E,z^p=algebraMap D E x.val.val) → (∀ u:(∀ v:T,(v.val.adicCompletionIntegers D)ˣ),∃ x:(S:Set V).unit D,∀ v:T,
      ∃ y:(v.val.adicCompletionIntegers D)ˣ, ((y.val.val:v.val.adicCompletion D)^p)*(x.val.val:v.val.adicCompletion D)=(u v).val.val)
) → (
∀(D:Type)[Field D][NumberField D](E:IntermediateField D (SeparableClosure D))
   [FiniteDimensional D E][IsGalois D E],
   let p:=Module.finrank D E
   p.Prime → (primitiveRoots p D).Nonempty →
   letI:NumberField E:=NumberField.of_module_finite D E
   let V:=HeightOneSpectrum (𝓞 D)
   let split(v:V):=∀ t:HeightOneSpectrum (𝓞 E),t.asIdeal.LiesOver v.asIdeal → ∀ g:Gal(E/D),
     HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapAlgEquiv g).toRingEquiv t=t → g=1
   let A:=AdeleRing (𝓞 D) D
   let J(F:Finset V):=Subgroup.closure {a:Aˣ | ∀ v:V,v∉F → a.val.2 v∈v.adicCompletionIntegers D ∧ (a⁻¹).val.2 v∈v.adicCompletionIntegers D}
   let j:=Units.map (algebraMap D A).toMonoidHom
   ∀ B:Finset V,∃ S T:Finset V,B⊆S ∧ (∀ v∈T,split v) ∧ Disjoint S T ∧
     T.card+1=Nat.card (InfinitePlace D)+S.card ∧ (∀ v:V,v.asIdeal ∣ Ideal.span {(p:𝓞 D)} → v∈S) ∧ j.range⊔J S=⊤ ∧ (∀ u:(∀ v:T,(v.val.adicCompletionIntegers D)ˣ),∃ x:(S:Set V).unit D,∀ v:T,
      ∃ y:(v.val.adicCompletionIntegers D)ˣ, ((y.val.val:v.val.adicCompletion D)^p)*(x.val.val:v.val.adicCompletion D)=(u v).val.val)
) := by
  intro select count D _ _ E _ _
  dsimp only
  intro hp hmu B
  obtain ⟨S,T,bs,split,disj,card,prime,classes,roots⟩:=select D E hp hmu B
  exact ⟨S,T,bs,split,disj,card,prime,classes,count D E hp hmu S T disj card prime roots⟩

end OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H1_R1_H1_R1_H3_R1_H1_R1_H3_R1_H2_R1_H1_R1

end

section
open NumberField IsDedekindDomain
open scoped NumberField Classical TensorProduct IsMulCommutative
open scoped NumberField TensorProduct Classical

 
namespace OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H1_R1_H1_R1_H3_R1_H1_R1_H3_R1_H2_R1_H2_R1
open NumberField IsDedekindDomain
open scoped NumberField TensorProduct Classical



theorem deriveKummerLocalRootDetection : (
∀(D:Type)[Field D][NumberField D](p:ℕ),p.Prime → (primitiveRoots p D).Nonempty →
   let V:=HeightOneSpectrum (𝓞 D)
   ∀ S T:Finset V,(∀v:V,v.asIdeal ∣ Ideal.span {(p:𝓞 D)} → v∈S) →
    ∀x:(↑(S∪T):Set V).unit D,(∀w:InfinitePlace D,∃ y:w.Completion,y^p=(x.val.val:w.Completion)) →
    (∀v∈S,∃y:v.adicCompletion D,y^p=(x.val.val:v.adicCompletion D)) →
    ∃ M:IntermediateField D (SeparableClosure D),FiniteDimensional D M ∧ IsGalois D M ∧ IsCyclic Gal(M/D) ∧
       (∃z:M,z^p=algebraMap D M x.val.val) ∧ let norm (F:Type) [Field F] [Algebra D F]:=(Units.map (Algebra.norm F (S:=F⊗[D]M))).range
    (∀w:InfinitePlace D,norm w.Completion=⊤) ∧ (∀v∈S,norm (v.adicCompletion D)=⊤) ∧
    (∀v∈T,(powMonoidHom p:(v.adicCompletion D)ˣ→*(v.adicCompletion D)ˣ).range≤norm (v.adicCompletion D)) ∧
    (∀v:V,v∉S∪T → (Units.map (v.adicCompletionIntegers D).subtype.toMonoidHom).range≤norm (v.adicCompletion D))
) → (
∀(D M:Type)[Field D][NumberField D][Field M][Algebra D M][FiniteDimensional D M][IsGalois D M][IsCyclic Gal(M/D)]
    (p:ℕ),0<p → let V:=HeightOneSpectrum (𝓞 D)
    let A:=AdeleRing (𝓞 D) D
   let J(F:Finset V):=Subgroup.closure {a:Aˣ | ∀ v:V,v∉F → a.val.2 v∈v.adicCompletionIntegers D ∧ (a⁻¹).val.2 v∈v.adicCompletionIntegers D}
   let j:=Units.map (algebraMap D A).toMonoidHom
    ∀S T:Finset V,Disjoint S T → j.range⊔J S=⊤ → (∀ u:(∀ v:T,(v.val.adicCompletionIntegers D)ˣ),∃ x:(S:Set V).unit D,∀ v:T,
      ∃ y:(v.val.adicCompletionIntegers D)ˣ, ((y.val.val:v.val.adicCompletion D)^p)*(x.val.val:v.val.adicCompletion D)=(u v).val.val) →
    (let norm (F:Type) [Field F] [Algebra D F]:=(Units.map (Algebra.norm F (S:=F⊗[D]M))).range
    (∀w:InfinitePlace D,norm w.Completion=⊤) ∧ (∀v∈S,norm (v.adicCompletion D)=⊤) ∧
    (∀v∈T,(powMonoidHom p:(v.adicCompletion D)ˣ→*(v.adicCompletion D)ˣ).range≤norm (v.adicCompletion D)) ∧
    (∀v:V,v∉S∪T → (Units.map (v.adicCompletionIntegers D).subtype.toMonoidHom).range≤norm (v.adicCompletion D))) → j.range⊔(Units.map (Algebra.norm A (S:=A⊗[D]M))).range=⊤
) → (
(∀(D N:Type)[Field D][NumberField D][Field N][NumberField N][Algebra D N]
    [FiniteDimensional D N][IsGalois D N][IsCyclic Gal(N/D)],
    let A:=AdeleRing (𝓞 D) D
    (Units.map (algebraMap D A).toMonoidHom).range ⊔ (Units.map (Algebra.norm A (S:=A⊗[D]N))).range=⊤ →
    Module.finrank D N=1) →
  ∀(D:Type)[Field D][NumberField D](p:ℕ),p.Prime → (primitiveRoots p D).Nonempty →
   let V:=HeightOneSpectrum (𝓞 D)
   let A:=AdeleRing (𝓞 D) D
   let J(F:Finset V):=Subgroup.closure {a:Aˣ | ∀ v:V,v∉F → a.val.2 v∈v.adicCompletionIntegers D ∧ (a⁻¹).val.2 v∈v.adicCompletionIntegers D}
   let j:=Units.map (algebraMap D A).toMonoidHom
   ∀ S T:Finset V,Disjoint S T → ((∀ v:V,v.asIdeal ∣ Ideal.span {(p:𝓞 D)} → v∈S) ∧ j.range⊔J S=⊤) → (∀ u:(∀ v:T,(v.val.adicCompletionIntegers D)ˣ),∃ x:(S:Set V).unit D,∀ v:T,
      ∃ y:(v.val.adicCompletionIntegers D)ˣ, ((y.val.val:v.val.adicCompletion D)^p)*(x.val.val:v.val.adicCompletion D)=(u v).val.val) →
     let W:=(↑(S∪T):Set V).unit D
     (∀ x:W,(∀ w:InfinitePlace D,∃ y:w.Completion,y^p=(x.val.val:w.Completion)) →
       (∀ v∈S,∃ y:v.adicCompletion D,y^p=(x.val.val:v.adicCompletion D)) → ∃ y:W,y^p=x)
) := by
  intro build norms lower D _ _ p hp hmu
  dsimp only
  intro S T disj hS approx x hi hf
  obtain ⟨M,dim,gal,cyc,⟨z,hz⟩,loc⟩:=build D p hp hmu S T hS.1 x hi hf
  letI := dim
  letI := gal
  letI := cyc
  letI : NumberField M:=NumberField.of_module_finite D M
  have one:=lower D M (norms D M p hp.pos S T disj hS.2 approx loc)
  obtain ⟨y,hy⟩ := (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp one).surjective z
  have pow:y^p=x.val.val:=(algebraMap D M).injective (by rw [map_pow,hy,hz])
  have nz:y≠0:=by rintro rfl;rw [zero_pow hp.ne_zero] at pow;exact x.val.ne_zero pow.symm
  let u:=Units.mk0 y nz
  have hu:u^p=x.val:=Units.ext pow
  have mem:u∈((S∪T:Finset (HeightOneSpectrum (𝓞 D))):Set (HeightOneSpectrum (𝓞 D))).unit D:=by
    have powmem:u^p∈((S∪T:Finset (HeightOneSpectrum (𝓞 D))):Set (HeightOneSpectrum (𝓞 D))).unit D:=hu ▸ x.property
    intro v hv
    have h:=powmem v hv
    change v.valuation D ((u.val:D)^p)=1 at h
    rw [map_pow] at h
    exact (pow_eq_one_iff_left hp.ne_zero).mp h
  exact ⟨⟨u,mem⟩,Subtype.ext hu⟩
end OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H1_R1_H1_R1_H3_R1_H1_R1_H3_R1_H2_R1_H2_R1

end

namespace OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H1_R1_H1_R1_H3_R1
theorem main : H1 → H2 → H3 → H4 → OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H1_R1_H1_R1.H3 :=
  fun v1 v2 v3 v4 =>
    (OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H1_R1_H1_R1_H3_R1_H1_R1_H3_R1.deriveAuxiliarySplitPrimes v2.1 (OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H1_R1_H1_R1_H3_R1_H1_R1_H3_R1_H2_R1.deriveLocalUnitApproximation (OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H1_R1_H1_R1_H3_R1_H1_R1_H3_R1_H2_R1_H1_R1.deriveCyclicRadicalLocalization v1 v2.2) (OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H1_R1_H1_R1_H3_R1_H1_R1_H3_R1_H2_R1_H2_R1.deriveKummerLocalRootDetection v4.1 v3)) v4.2)
end OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H1_R1_H1_R1_H3_R1
