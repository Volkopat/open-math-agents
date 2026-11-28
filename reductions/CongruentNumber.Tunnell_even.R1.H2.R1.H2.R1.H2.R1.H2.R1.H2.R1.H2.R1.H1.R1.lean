import OMAReductions.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1
import Mathlib

/-! For a cyclic extension the adelic norm index and the norm-one classes give the class formation. Its finite-place reciprocity maps satisfy the product formula on principal elements. Restrict these maps to global integral units. -/
namespace OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H1_R1
open NumberField IsDedekindDomain
open scoped NumberField Classical TensorProduct IsMulCommutative

def H1 : Prop :=
  ∀(D N:Type)[Field D][NumberField D][Field N][NumberField N][Algebra D N]
   [FiniteDimensional D N][IsGalois D N](g:Gal(N/D)),(∀ s,s∈Subgroup.zpowers g) →
   let A:=AdeleRing (𝓞 D) D
   let T:=A⊗[D]N
   let P:=(Units.map (algebraMap D A).toMonoidHom).range ⊔ (Units.map (Algebra.norm A (S:=T))).range
   let q:=QuotientGroup.mk' (Units.map (Algebra.TensorProduct.includeRight (R:=D) (A:=A) (B:=N)).toMonoidHom).range
   let a(s:Gal(N/D)):=Units.mapEquiv (Algebra.TensorProduct.congr (AlgEquiv.refl (R:=A) (A₁:=A)) s).toMulEquiv
   P.index=Module.finrank D N ∧ ∀ z:Tˣ,(∏ s:Gal(N/D),q (a s z))=1 → ∃ y:Tˣ,q (a g y / y)=q z

def H2 : Prop :=
  (∀(D N:Type)[Field D][NumberField D][Field N][NumberField N][Algebra D N]
   [FiniteDimensional D N][IsGalois D N](g:Gal(N/D)),(∀ s,s∈Subgroup.zpowers g) →
   let A:=AdeleRing (𝓞 D) D
   let T:=A⊗[D]N
   let P:=(Units.map (algebraMap D A).toMonoidHom).range ⊔ (Units.map (Algebra.norm A (S:=T))).range
   let q:=QuotientGroup.mk' (Units.map (Algebra.TensorProduct.includeRight (R:=D) (A:=A) (B:=N)).toMonoidHom).range
   let a(s:Gal(N/D)):=Units.mapEquiv (Algebra.TensorProduct.congr (AlgEquiv.refl (R:=A) (A₁:=A)) s).toMulEquiv
   P.index=Module.finrank D N ∧ ∀ z:Tˣ,(∏ s:Gal(N/D),q (a s z))=1 → ∃ y:Tˣ,q (a g y / y)=q z) →
  (∀ (D M:Type) [Field D] [NumberField D] [Field M] [NumberField M] [Algebra D M]
  [FiniteDimensional D M] [IsAbelianGalois D M], let A:=AdeleRing (𝓞 D) D
  let P (B:Type) [Field B] [Algebra D B] := (Units.map (algebraMap D A).toMonoidHom).range ⊔
    (Units.map (Algebra.norm A (S:=A⊗[D]B))).range
  Nonempty ((Aˣ ⧸ P M) ≃* Gal(M/D)) ∧ (P M).index=Module.finrank D M ∧ ∀ E F:IntermediateField D M, E⊔F=⊤ → P M=P E ⊓ P F) ∧ (∀ (m : ℕ), (2 < m) → ∀ (v:HeightOneSpectrum (𝓞 ℚ)) (n:ℕ),
  let A:=AdeleRing (𝓞 ℚ) ℚ
  ∀ z:Aˣ, z.val.1=1 → (∀ w:HeightOneSpectrum (𝓞 ℚ), w≠v → z.val.2 w=1) →
  v.asIdeal.absNorm.Coprime m → -WithZero.log (Valued.v (z.val.2 v))=(n:ℤ) →
  z∈(Units.map (algebraMap ℚ A).toMonoidHom).range ⊔
    (Units.map (Algebra.norm A (S:=A⊗[ℚ]CyclotomicField m ℚ))).range →
  m ∣ v.asIdeal.absNorm ^ n - 1)

def H3 : Prop :=
  (∀ (D M:Type) [Field D] [NumberField D] [Field M] [NumberField M] [Algebra D M]
  [FiniteDimensional D M] [IsAbelianGalois D M], let A:=AdeleRing (𝓞 D) D
  let P (B:Type) [Field B] [Algebra D B] := (Units.map (algebraMap D A).toMonoidHom).range ⊔
    (Units.map (Algebra.norm A (S:=A⊗[D]B))).range
  (P M).index=Module.finrank D M ∧ ∀ E F:IntermediateField D M, E⊔F=⊤ → P M=P E ⊓ P F) → (∀ (m : ℕ), (2 < m) → ∀ (v:HeightOneSpectrum (𝓞 ℚ)) (n:ℕ),
  let A:=AdeleRing (𝓞 ℚ) ℚ
  ∀ z:Aˣ, z.val.1=1 → (∀ w:HeightOneSpectrum (𝓞 ℚ), w≠v → z.val.2 w=1) →
  v.asIdeal.absNorm.Coprime m → -WithZero.log (Valued.v (z.val.2 v))=(n:ℤ) →
  z∈(Units.map (algebraMap ℚ A).toMonoidHom).range ⊔
    (Units.map (Algebra.norm A (S:=A⊗[ℚ]CyclotomicField m ℚ))).range →
  m ∣ v.asIdeal.absNorm ^ n - 1) →
  ∀ (D N:Type) [Field D] [NumberField D] [Field N] [NumberField N] [Algebra D N]
    [FiniteDimensional D N] [IsAbelianGalois D N] (v : HeightOneSpectrum (𝓞 D)),
  let A := AdeleRing (𝓞 D) D
  let P := (Units.map (algebraMap D A).toMonoidHom).range ⊔ (Units.map (Algebra.norm A (S:=A ⊗[D] N))).range
  let V := v.adicCompletion D
  ∃ t:HeightOneSpectrum (𝓞 N), t.asIdeal.LiesOver v.asIdeal ∧ ∃ f:V→+*t.adicCompletion N,
    Continuous f ∧ (∀ c:D,f (c:V)=((algebraMap D N c:N):t.adicCompletion N)) ∧
    letI : Algebra V (t.adicCompletion N):=f.toAlgebra
    ∀ (x:Vˣ) (z:Aˣ),z.val.1=1 → z.val.2 v=x.val →
      (∀ w:HeightOneSpectrum (𝓞 D),w≠v → z.val.2 w=1) →
      (z∈P ↔ ∃ y:(t.adicCompletion N)ˣ,Algebra.norm V (y:t.adicCompletion N)=x.val)

def H4 : Prop :=
  ∀ (D N:Type) [Field D] [NumberField D] [Field N] [NumberField N] [Algebra D N]
    [FiniteDimensional D N] [IsAbelianGalois D N],(∀ i:InfinitePlace D,i.IsComplex) →
  let A := AdeleRing (𝓞 D) D
  let P := (Units.map (algebraMap D A).toMonoidHom).range ⊔ (Units.map (Algebra.norm A (S:=A ⊗[D] N))).range
  ∀ j : ∀ v:HeightOneSpectrum (𝓞 D),(v.adicCompletion D)ˣ →* Aˣ,
    (∀ v x,(j v x).val.1=1 ∧ (j v x).val.2 v=x.val ∧
      ∀ w:HeightOneSpectrum (𝓞 D), w≠v → (j v x).val.2 w=1) →
    ∀ x:Dˣ, ∏ᶠ v, QuotientGroup.mk' P (j v (Units.map (algebraMap D (v.adicCompletion D)).toMonoidHom x))=1

end OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H1_R1

namespace OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H1_R1
open NumberField IsDedekindDomain
open scoped NumberField Classical TensorProduct IsMulCommutative

private theorem fromProduct : H1 → ((∀(D N:Type)[Field D][NumberField D][Field N][NumberField N][Algebra D N]
   [FiniteDimensional D N][IsGalois D N](g:Gal(N/D)),(∀ s,s∈Subgroup.zpowers g) →
   let A:=AdeleRing (𝓞 D) D
   let T:=A⊗[D]N
   let P:=(Units.map (algebraMap D A).toMonoidHom).range ⊔ (Units.map (Algebra.norm A (S:=T))).range
   let q:=QuotientGroup.mk' (Units.map (Algebra.TensorProduct.includeRight (R:=D) (A:=A) (B:=N)).toMonoidHom).range
   let a(s:Gal(N/D)):=Units.mapEquiv (Algebra.TensorProduct.congr (AlgEquiv.refl (R:=A) (A₁:=A)) s).toMulEquiv
   P.index=Module.finrank D N ∧ ∀ z:Tˣ,(∏ s:Gal(N/D),q (a s z))=1 → ∃ y:Tˣ,q (a g y / y)=q z) →
  ∀(D N:Type)[Field D][NumberField D][Field N][NumberField N][Algebra D N]
   [FiniteDimensional D N][IsAbelianGalois D N],(∀ i:InfinitePlace D,i.IsComplex) →
   ∃ σ : ∀ v:HeightOneSpectrum (𝓞 D),(v.adicCompletion D)ˣ →* Gal(N/D),
    (∀ x:Dˣ, ∏ᶠ v,σ v (Units.map (algebraMap D (v.adicCompletion D)).toMonoidHom x)=1) ∧
    ∀ v:HeightOneSpectrum (𝓞 D),let V:=v.adicCompletion D
     ∃ t:HeightOneSpectrum (𝓞 N),t.asIdeal.LiesOver v.asIdeal ∧ ∃ f:V→+*t.adicCompletion N,
      Continuous f ∧ (∀ c:D,f (c:V)=((algebraMap D N c:N):t.adicCompletion N)) ∧
      letI : Algebra V (t.adicCompletion N):=f.toAlgebra
      ∀ x:Vˣ, σ v x=1 ↔ ∃ y:(t.adicCompletion N)ˣ,Algebra.norm V (y:t.adicCompletion N)=x.val) → OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1.H1 := by
  intro classes build
  obtain product := build classes
  intro D N _ _ _ _ _ _ _ complex
  obtain ⟨σ,hprod,hnorm⟩ := product D N complex
  let x (u:(𝓞 D)ˣ) := Units.map (algebraMap (𝓞 D) D).toMonoidHom u
  let loc (v:HeightOneSpectrum (𝓞 D)) (u:(𝓞 D)ˣ) :=
    Units.map (algebraMap D (v.adicCompletion D)).toMonoidHom (x u)
  refine ⟨fun v u => σ v (loc v u),fun u => hprod (x u),?_⟩
  intro v
  obtain ⟨t,ht,f,hf,hc,hk⟩ := hnorm v
  exact ⟨t,ht,f,hf,hc,fun u=>hk (loc v u)⟩

private theorem product : H2 → H3 → H4 → ((∀(D N:Type)[Field D][NumberField D][Field N][NumberField N][Algebra D N]
   [FiniteDimensional D N][IsGalois D N](g:Gal(N/D)),(∀ s,s∈Subgroup.zpowers g) →
   let A:=AdeleRing (𝓞 D) D
   let T:=A⊗[D]N
   let P:=(Units.map (algebraMap D A).toMonoidHom).range ⊔ (Units.map (Algebra.norm A (S:=T))).range
   let q:=QuotientGroup.mk' (Units.map (Algebra.TensorProduct.includeRight (R:=D) (A:=A) (B:=N)).toMonoidHom).range
   let a(s:Gal(N/D)):=Units.mapEquiv (Algebra.TensorProduct.congr (AlgEquiv.refl (R:=A) (A₁:=A)) s).toMulEquiv
   P.index=Module.finrank D N ∧ ∀ z:Tˣ,(∏ s:Gal(N/D),q (a s z))=1 → ∃ y:Tˣ,q (a g y / y)=q z) →
  ∀(D N:Type)[Field D][NumberField D][Field N][NumberField N][Algebra D N]
   [FiniteDimensional D N][IsAbelianGalois D N],(∀ i:InfinitePlace D,i.IsComplex) →
   ∃ σ : ∀ v:HeightOneSpectrum (𝓞 D),(v.adicCompletion D)ˣ →* Gal(N/D),
    (∀ x:Dˣ, ∏ᶠ v,σ v (Units.map (algebraMap D (v.adicCompletion D)).toMonoidHom x)=1) ∧
    ∀ v:HeightOneSpectrum (𝓞 D),let V:=v.adicCompletion D
     ∃ t:HeightOneSpectrum (𝓞 N),t.asIdeal.LiesOver v.asIdeal ∧ ∃ f:V→+*t.adicCompletion N,
      Continuous f ∧ (∀ c:D,f (c:V)=((algebraMap D N c:N):t.adicCompletion N)) ∧
      letI : Algebra V (t.adicCompletion N):=f.toAlgebra
      ∀ x:Vˣ, σ v x=1 ↔ ∃ y:(t.adicCompletion N)ˣ,Algebra.norm V (y:t.adicCompletion N)=x.val) := by
  intro makeGroup makeKernel product classes
  have group:=makeGroup classes
  have localKer := makeKernel (fun D N _ _ _ _ _ _ _ => (group.1 D N).2) group.2
  classical
  intro D N _ _ _ _ _ _ _ hc
  obtain ⟨e⟩ := (group.1 D N).1
  let A := AdeleRing (𝓞 D) D
  let P := (Units.map (algebraMap D A).toMonoidHom).range ⊔ (Units.map (Algebra.norm A (S:=A ⊗[D] N))).range
  let q := QuotientGroup.mk' P
  let place (v:HeightOneSpectrum (𝓞 D)) : v.adicCompletion D →* A :=
    { toFun := fun x => (1,RestrictedProduct.mulSingle (fun w:HeightOneSpectrum (𝓞 D)=>w.adicCompletionIntegers D) v x)
      map_one' := Prod.ext rfl (RestrictedProduct.mulSingle_one _ _)
      map_mul' := fun x y=>Prod.ext (one_mul _).symm (RestrictedProduct.mulSingle_mul _ _ _ _) }
  let j (v:HeightOneSpectrum (𝓞 D)) := Units.map (place v)
  have supp (v:HeightOneSpectrum (𝓞 D)) (x:(v.adicCompletion D)ˣ) :
      (j v x).val.1=1 ∧ (j v x).val.2 v=x.val ∧ ∀ w:HeightOneSpectrum (𝓞 D),w≠v → (j v x).val.2 w=1 :=
    ⟨rfl,RestrictedProduct.mulSingle_eq_same _ v x.val,fun _ h=>RestrictedProduct.mulSingle_eq_of_ne _ x.val h⟩
  let σ (v:HeightOneSpectrum (𝓞 D)) := e.toMonoidHom.comp (q.comp (j v))
  refine ⟨σ,?_,?_⟩
  · intro x
    have h:=product D N hc j supp x
    let a (v:HeightOneSpectrum (𝓞 D)) : Aˣ ⧸ P := q (j v (Units.map (algebraMap D (v.adicCompletion D)).toMonoidHom x))
    let E : (Aˣ ⧸ P) ≃* Gal(N/D) := e
    change (∏ᶠ v,E (a v))=1
    rw [← MulEquiv.map_finprod E a,show (∏ᶠ v,a v)=1 from h,map_one]
  · intro v
    obtain ⟨t,ht,f,hf,hc',hk⟩:=localKer D N v
    refine ⟨t,ht,f,hf,hc',?_⟩
    intro x
    obtain ⟨h1,h2,h3⟩:=supp v x
    change e (q (j v x))=1 ↔ _
    exact (map_eq_one_iff e e.injective).trans ((QuotientGroup.eq_one_iff _).trans (hk x (j v x) h1 h2 h3))

theorem main : H1 → H2 → H3 → H4 → OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1.H1 := fun a b c d => fromProduct a (product b c d)
end OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H1_R1
