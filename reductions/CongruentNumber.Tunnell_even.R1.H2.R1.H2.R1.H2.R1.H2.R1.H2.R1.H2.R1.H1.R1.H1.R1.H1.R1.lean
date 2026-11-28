import OMAReductions.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H1_R1_H1_R1
import Mathlib


/-! The S-unit logarithmic lattice gives the quotient of its fixed-unit index by its norm-one index. The supported-idèle exact sequence and the finite and infinite local factors then compute the norm index for the cyclic idèle classes. -/

namespace OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H1_R1_H1_R1_H1_R1

section

open NumberField IsDedekindDomain
open scoped NumberField TensorProduct Classical

def H1 : Prop :=
  (
∀ (G U J C:Type)[Group G][Fintype G][CommGroup U][CommGroup J][CommGroup C]
    [MulDistribMulAction G U][MulDistribMulAction G J][MulDistribMulAction G C]
    (g:G), (∀ s,s∈Subgroup.zpowers g) → ∀ (i:U→*J)(j:J→*C),
    (∀ s:G,∀ x:U,i (s•x)=s•i x) → (∀ s:G,∀ x:J,j (s•x)=s•j x) →
    Function.Injective i → Function.Surjective j → i.range=j.ker →
    let idx(M:Type)[CommGroup M][MulDistribMulAction G M]:=
    let a(s:G):M→*M:=MulDistribMulAction.toMonoidEnd G M s
    let n:M→*M:=∏ s:G,a s
    let b:=a g / MonoidHom.id M
    (n.range.relIndex b.ker,b.range.relIndex n.ker)
    let u:=idx U
    let v:=idx J
    let w:=idx C
    0<u.1 → 0<u.2 → 0<v.1 → 0<v.2 → 0<w.1 ∧ 0<w.2 ∧ v.1*u.2*w.2=v.2*u.1*w.1
)

end

section

open NumberField IsDedekindDomain
open scoped NumberField TensorProduct Classical

def H2 : Prop :=
  (
∀ (K L:Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L],
  let G:=Gal(L/K)
  ∀ (S:Finset (HeightOneSpectrum (𝓞 L))) (σ:G), (∀ g:G,g∈Subgroup.zpowers σ) →
  let p (g:G):=HeightOneSpectrum.equivOfRingEquiv (NumberField.RingOfIntegers.mapAlgEquiv g).toRingEquiv
  (∀ g w,w∈S ↔ p g w∈S) →
  let U:=(S:Set (HeightOneSpectrum (𝓞 L))).unit L
  let P:=InfinitePlace L ⊕ ↥S
  ∃ (j:MulAction G P),letI:=j; letI:Fintype (MulAction.orbitRel.Quotient G P):=Fintype.ofFinite _
    (∀ g:G,∀ i:InfinitePlace L,g • (Sum.inl i:P)=Sum.inl (g • i)) ∧
    (∀ g:G,∀ s:↥S,Sum.map id Subtype.val (g • (Sum.inr s:P))=Sum.inr (p g s.val)) ∧
    ∃ n b:U→*U,(∀ x:U,((n x).val:L)=∏ g:G,g (x.val:L)) ∧ (∀ x:U,((b x).val:L)=σ (x.val:L)/(x.val:L)) ∧
    let h:=n.range.relIndex b.ker
    let k:=b.range.relIndex n.ker
    0<h ∧ 0<k ∧ h*Nat.card G=k*∏ i:MulAction.orbitRel.Quotient G P,Nat.card (MulAction.stabilizer G i.out)
) ∧
  (
∀(D N:Type)[Field D][NumberField D][Field N][NumberField N][Algebra D N]
   [FiniteDimensional D N][IsGalois D N](g:Gal(N/D)),(∀ s,s∈Subgroup.zpowers g) →
   let G:=Gal(N/D)
   let A:=AdeleRing (𝓞 D) D
   let T:=A⊗[D]N
   let I:=(Units.map (Algebra.TensorProduct.includeRight (R:=D) (A:=A) (B:=N)).toMonoidHom).range
   let C:=Tˣ⧸I
   let q:=QuotientGroup.mk' I
   let a(s:G):=Units.mapEquiv (Algebra.TensorProduct.congr (AlgEquiv.refl (R:=A) (A₁:=A)) s).toMulEquiv
   let P:=(Units.map (algebraMap D A).toMonoidHom).range ⊔ (Units.map (Algebra.norm A (S:=T))).range
   ∃ c:MulDistribMulAction G C,letI:=c; (∀ s:G,∀ z:Tˣ,s•q z=q (a s z)) ∧
   let idx(M:Type)[CommGroup M][MulDistribMulAction G M]:=
    let a(s:G):M→*M:=MulDistribMulAction.toMonoidEnd G M s
    let n:M→*M:=∏ s:G,a s
    let b:=a g / MonoidHom.id M
    (n.range.relIndex b.ker,b.range.relIndex n.ker)
   (idx C).1=P.index
)

end

section

open NumberField IsDedekindDomain
open scoped NumberField TensorProduct Classical

def H3 : Prop :=
  (
∀(D N:Type)[Field D][NumberField D][Field N][NumberField N][Algebra D N]
   [FiniteDimensional D N][IsGalois D N](g:Gal(N/D)),(∀s,s∈Subgroup.zpowers g) →
   let G:=Gal(N/D)
   let V:=HeightOneSpectrum (𝓞 D)
   let W:=HeightOneSpectrum (𝓞 N)
   let A:=AdeleRing (𝓞 D) D
   let T:=A⊗[D]N
   let o(v:V)(x:T):=∀(w:W),w.asIdeal.LiesOver v.asIdeal →
    ∀(m:v.adicCompletion D→+*w.adicCompletion N)(f:T→+*w.adicCompletion N),Continuous m →
    (∀d:D,m (algebraMap D _ d)=algebraMap N _ (algebraMap D N d)) →
    (∀a:A,∀b:N,f (a ⊗ₜ[D] b)=m (a.2 v)*algebraMap N _ b) → f x∈w.adicCompletionIntegers N
   let p(s:G):=HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapAlgEquiv s).toRingEquiv
   let l:=Units.map (Algebra.TensorProduct.includeRight (R:=D) (A:=A) (B:=N)).toMonoidHom
   ∃(R:Finset V)(S:Finset W)(J:Subgroup Tˣ),(∀w:W,w∈S ↔ ∃v∈R,w.asIdeal.LiesOver v.asIdeal) ∧
   (∀v:V,v∉R → ∀w:W,w.asIdeal.LiesOver v.asIdeal → w.asIdeal.ramificationIdx (𝓞 D)=1) ∧
   (∀x:Tˣ,x∈J ↔ ∀v:V,v∉R → o v x.val ∧ o v x.inv) ∧
   J⊔l.range=⊤ ∧ Function.Injective l ∧ J.comap l=(S:Set W).unit N ∧ (∀s w,w∈S ↔ p s w∈S) ∧
   let U:=(S:Set W).unit N
   ∃ u:MulDistribMulAction G U,letI:=u; ∀s:G,∀x:U,((s•x).val:N)=s (x.val:N)
)

end

section

open NumberField IsDedekindDomain
open scoped NumberField TensorProduct Classical

def H4 : Prop :=
  (
∀(D N:Type)[Field D][NumberField D][Field N][NumberField N][Algebra D N]
   [FiniteDimensional D N][IsGalois D N](g:Gal(N/D)),(∀s,s∈Subgroup.zpowers g) →
   let G:=Gal(N/D)
   let V:=HeightOneSpectrum (𝓞 D)
   let W:=HeightOneSpectrum (𝓞 N)
   let A:=AdeleRing (𝓞 D) D
   let T:=A⊗[D]N
   let o(v:V)(x:T):=∀(w:W),w.asIdeal.LiesOver v.asIdeal →
    ∀(m:v.adicCompletion D→+*w.adicCompletion N)(f:T→+*w.adicCompletion N),Continuous m →
    (∀d:D,m (algebraMap D _ d)=algebraMap N _ (algebraMap D N d)) →
    (∀a:A,∀b:N,f (a ⊗ₜ[D] b)=m (a.2 v)*algebraMap N _ b) → f x∈w.adicCompletionIntegers N
   let p(s:G):=HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapAlgEquiv s).toRingEquiv
   let a(s:G):=Units.mapEquiv (Algebra.TensorProduct.congr (AlgEquiv.refl (R:=A) (A₁:=A)) s).toMulEquiv
   ∀(R:Finset V)(S:Finset W)(J:Subgroup Tˣ),(∀w:W,w∈S ↔ ∃v∈R,w.asIdeal.LiesOver v.asIdeal) →
   (∀v:V,v∉R → ∀w:W,w.asIdeal.LiesOver v.asIdeal → w.asIdeal.ramificationIdx (𝓞 D)=1) →
   (∀x:Tˣ,x∈J ↔ ∀v:V,v∉R → o v x.val ∧ o v x.inv) →
   let X:=InfinitePlace N ⊕ ↥S
   ∃ z:MulAction G X, letI:=z; letI:Fintype (MulAction.orbitRel.Quotient G X):=Fintype.ofFinite _
   (∀s:G,∀w:InfinitePlace N,s•(Sum.inl w:X)=Sum.inl (s•w)) ∧
   (∀s:G,∀w:↥S,Sum.map id Subtype.val (s•(Sum.inr w:X))=Sum.inr (p s w.val)) ∧
   ∃ β:MulDistribMulAction G J,letI:=β; (∀s:G,∀x:J,(s•x).val=a s x.val) ∧
   let b(s:G):J→*J:=MulDistribMulAction.toMonoidEnd G J s
   let n:J→*J:=∏s:G,b s
   let d:=b g / MonoidHom.id J
   let h:=n.range.relIndex d.ker
   let k:=d.range.relIndex n.ker
   0<h ∧ 0<k ∧ h=k*∏t:MulAction.orbitRel.Quotient G X,Nat.card (MulAction.stabilizer G t.out)
)

end

end OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H1_R1_H1_R1_H1_R1

section
open NumberField IsDedekindDomain
open scoped TensorProduct NumberField Classical
open scoped NumberField TensorProduct Classical

 
namespace OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H1_R1_H1_R1_H1_R1
open NumberField IsDedekindDomain
open scoped NumberField TensorProduct Classical
noncomputable section



theorem deriveSupportedIdeleClasses : (
∀ (K L:Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L],
  let G:=Gal(L/K)
  ∀ (S:Finset (HeightOneSpectrum (𝓞 L))) (σ:G), (∀ g:G,g∈Subgroup.zpowers σ) →
  let p (g:G):=HeightOneSpectrum.equivOfRingEquiv (NumberField.RingOfIntegers.mapAlgEquiv g).toRingEquiv
  (∀ g w,w∈S ↔ p g w∈S) →
  let U:=(S:Set (HeightOneSpectrum (𝓞 L))).unit L
  let P:=InfinitePlace L ⊕ ↥S
  ∃ (j:MulAction G P),letI:=j; letI:Fintype (MulAction.orbitRel.Quotient G P):=Fintype.ofFinite _
    (∀ g:G,∀ i:InfinitePlace L,g • (Sum.inl i:P)=Sum.inl (g • i)) ∧
    (∀ g:G,∀ s:↥S,Sum.map id Subtype.val (g • (Sum.inr s:P))=Sum.inr (p g s.val)) ∧
    ∃ n b:U→*U,(∀ x:U,((n x).val:L)=∏ g:G,g (x.val:L)) ∧ (∀ x:U,((b x).val:L)=σ (x.val:L)/(x.val:L)) ∧
    let h:=n.range.relIndex b.ker
    let k:=b.range.relIndex n.ker
    0<h ∧ 0<k ∧ h*Nat.card G=k*∏ i:MulAction.orbitRel.Quotient G P,Nat.card (MulAction.stabilizer G i.out)
) → (
∀(D N:Type)[Field D][NumberField D][Field N][NumberField N][Algebra D N]
   [FiniteDimensional D N][IsGalois D N](g:Gal(N/D)),(∀ s,s∈Subgroup.zpowers g) →
  (let G:=Gal(N/D)
  ∀ (S:Finset (HeightOneSpectrum (𝓞 N))) (σ:G), (∀ g:G,g∈Subgroup.zpowers σ) →
  let p (g:G):=HeightOneSpectrum.equivOfRingEquiv (NumberField.RingOfIntegers.mapAlgEquiv g).toRingEquiv
  (∀ g w,w∈S ↔ p g w∈S) →
  let U:=(S:Set (HeightOneSpectrum (𝓞 N))).unit N
  let P:=InfinitePlace N ⊕ ↥S
  ∃ (j:MulAction G P),letI:=j; letI:Fintype (MulAction.orbitRel.Quotient G P):=Fintype.ofFinite _
    (∀ g:G,∀ i:InfinitePlace N,g • (Sum.inl i:P)=Sum.inl (g • i)) ∧
    (∀ g:G,∀ s:↥S,Sum.map id Subtype.val (g • (Sum.inr s:P))=Sum.inr (p g s.val)) ∧
    ∃ n b:U→*U,(∀ x:U,((n x).val:N)=∏ g:G,g (x.val:N)) ∧ (∀ x:U,((b x).val:N)=σ (x.val:N)/(x.val:N)) ∧
    let h:=n.range.relIndex b.ker
    let k:=b.range.relIndex n.ker
    0<h ∧ 0<k ∧ h*Nat.card G=k*∏ i:MulAction.orbitRel.Quotient G P,Nat.card (MulAction.stabilizer G i.out)) →
   let A:=AdeleRing (𝓞 D) D
   let T:=A⊗[D]N
   let P:=(Units.map (algebraMap D A).toMonoidHom).range ⊔ (Units.map (Algebra.norm A (S:=T))).range
   let q:=QuotientGroup.mk' (Units.map (Algebra.TensorProduct.includeRight (R:=D) (A:=A) (B:=N)).toMonoidHom).range
   let a(s:Gal(N/D)):=Units.mapEquiv (Algebra.TensorProduct.congr (AlgEquiv.refl (R:=A) (A₁:=A)) s).toMulEquiv
   let n:=q.comp (∏ s:Gal(N/D),(a s).toMonoidHom)
   let b:=q.comp ((a g).toMonoidHom / MonoidHom.id Tˣ)
   let k:=b.range.relIndex (n.ker.map q)
   0<k ∧ P.index=Module.finrank D N*k
) → OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H1_R1_H1_R1.H1 := by
  intro units supported D N _ _ _ _ _ _ _ g gen
  exact supported D N g gen (units D N)

end
end OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H1_R1_H1_R1_H1_R1

end

section
open NumberField IsDedekindDomain
open scoped NumberField TensorProduct Classical

 
namespace OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H1_R1_H1_R1_H1_R1_H2_R1
open NumberField IsDedekindDomain
open scoped NumberField TensorProduct Classical
noncomputable section




set_option maxHeartbeats 2400000 in
theorem deriveSupportedIdeleHerbrand : (
∀ (G U J C:Type)[Group G][Fintype G][CommGroup U][CommGroup J][CommGroup C]
    [MulDistribMulAction G U][MulDistribMulAction G J][MulDistribMulAction G C]
    (g:G), (∀ s,s∈Subgroup.zpowers g) → ∀ (i:U→*J)(j:J→*C),
    (∀ s:G,∀ x:U,i (s•x)=s•i x) → (∀ s:G,∀ x:J,j (s•x)=s•j x) →
    Function.Injective i → Function.Surjective j → i.range=j.ker →
    let idx(M:Type)[CommGroup M][MulDistribMulAction G M]:=
    let a(s:G):M→*M:=MulDistribMulAction.toMonoidEnd G M s
    let n:M→*M:=∏ s:G,a s
    let b:=a g / MonoidHom.id M
    (n.range.relIndex b.ker,b.range.relIndex n.ker)
    let u:=idx U
    let v:=idx J
    let w:=idx C
    0<u.1 → 0<u.2 → 0<v.1 → 0<v.2 → 0<w.1 ∧ 0<w.2 ∧ v.1*u.2*w.2=v.2*u.1*w.1
) → (
∀(D N:Type)[Field D][NumberField D][Field N][NumberField N][Algebra D N]
   [FiniteDimensional D N][IsGalois D N](g:Gal(N/D)),(∀ s,s∈Subgroup.zpowers g) →
   let G:=Gal(N/D)
   let A:=AdeleRing (𝓞 D) D
   let T:=A⊗[D]N
   let I:=(Units.map (Algebra.TensorProduct.includeRight (R:=D) (A:=A) (B:=N)).toMonoidHom).range
   let C:=Tˣ⧸I
   let q:=QuotientGroup.mk' I
   let a(s:G):=Units.mapEquiv (Algebra.TensorProduct.congr (AlgEquiv.refl (R:=A) (A₁:=A)) s).toMulEquiv
   let P:=(Units.map (algebraMap D A).toMonoidHom).range ⊔ (Units.map (Algebra.norm A (S:=T))).range
   ∃ c:MulDistribMulAction G C,letI:=c; (∀ s:G,∀ z:Tˣ,s•q z=q (a s z)) ∧
   let idx(M:Type)[CommGroup M][MulDistribMulAction G M]:=
    let a(s:G):M→*M:=MulDistribMulAction.toMonoidEnd G M s
    let n:M→*M:=∏ s:G,a s
    let b:=a g / MonoidHom.id M
    (n.range.relIndex b.ker,b.range.relIndex n.ker)
   (idx C).1=P.index
) → (
∀(D N:Type)[Field D][NumberField D][Field N][NumberField N][Algebra D N]
   [FiniteDimensional D N][IsGalois D N](g:Gal(N/D)),(∀ s,s∈Subgroup.zpowers g) →
   let G:=Gal(N/D)
   let A:=AdeleRing (𝓞 D) D
   let T:=A⊗[D]N
   let I:=(Units.map (Algebra.TensorProduct.includeRight (R:=D) (A:=A) (B:=N)).toMonoidHom).range
   let C:=Tˣ⧸I
   let q:=QuotientGroup.mk' I
   let a(s:G):=Units.mapEquiv (Algebra.TensorProduct.congr (AlgEquiv.refl (R:=A) (A₁:=A)) s).toMulEquiv
   ∀ c:MulDistribMulAction G C,letI:=c; (∀ s:G,∀ z:Tˣ,s•q z=q (a s z)) →
   let p(s:G):=HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapAlgEquiv s).toRingEquiv
   ∃ S:Finset (HeightOneSpectrum (𝓞 N)), (∀ s w,w∈S ↔ p s w∈S) ∧
   let U:=(S:Set (HeightOneSpectrum (𝓞 N))).unit N
   let X:=InfinitePlace N ⊕ ↥S
   ∃ u:MulDistribMulAction G U, letI:=u; (∀ s:G,∀ x:U,((s•x).val:N)=s (x.val:N)) ∧
   ∃ z:MulAction G X, letI:=z; letI:Fintype (MulAction.orbitRel.Quotient G X):=Fintype.ofFinite _
   (∀ s:G,∀ w:InfinitePlace N,s•(Sum.inl w:X)=Sum.inl (s•w)) ∧
   (∀ s:G,∀ w:↥S,Sum.map id Subtype.val (s•(Sum.inr w:X))=Sum.inr (p s w.val)) ∧
   ∃ (J:Type)(j₀:CommGroup J), letI:=j₀; ∃ β:MulDistribMulAction G J, letI:=β
   ∃ (i:U→*J)(j:J→*C),(∀ s:G,∀ x:U,i (s•x)=s•i x) ∧ (∀ s:G,∀ x:J,j (s•x)=s•j x) ∧
   Function.Injective i ∧ Function.Surjective j ∧ i.range=j.ker ∧
   let idx(M:Type)[CommGroup M][MulDistribMulAction G M]:=
    let a(s:G):M→*M:=MulDistribMulAction.toMonoidEnd G M s
    let n:M→*M:=∏ s:G,a s
    let b:=a g / MonoidHom.id M
    (n.range.relIndex b.ker,b.range.relIndex n.ker)
   let v:=idx J
   0<v.1 ∧ 0<v.2 ∧ v.1=v.2*∏ t:MulAction.orbitRel.Quotient G X,Nat.card (MulAction.stabilizer G t.out)
) → (
∀(D N:Type)[Field D][NumberField D][Field N][NumberField N][Algebra D N]
   [FiniteDimensional D N][IsGalois D N](g:Gal(N/D)),(∀ s,s∈Subgroup.zpowers g) →
  (let G:=Gal(N/D)
  ∀ (S:Finset (HeightOneSpectrum (𝓞 N))) (σ:G), (∀ g:G,g∈Subgroup.zpowers σ) →
  let p (g:G):=HeightOneSpectrum.equivOfRingEquiv (NumberField.RingOfIntegers.mapAlgEquiv g).toRingEquiv
  (∀ g w,w∈S ↔ p g w∈S) →
  let U:=(S:Set (HeightOneSpectrum (𝓞 N))).unit N
  let P:=InfinitePlace N ⊕ ↥S
  ∃ (j:MulAction G P),letI:=j; letI:Fintype (MulAction.orbitRel.Quotient G P):=Fintype.ofFinite _
    (∀ g:G,∀ i:InfinitePlace N,g • (Sum.inl i:P)=Sum.inl (g • i)) ∧
    (∀ g:G,∀ s:↥S,Sum.map id Subtype.val (g • (Sum.inr s:P))=Sum.inr (p g s.val)) ∧
    ∃ n b:U→*U,(∀ x:U,((n x).val:N)=∏ g:G,g (x.val:N)) ∧ (∀ x:U,((b x).val:N)=σ (x.val:N)/(x.val:N)) ∧
    let h:=n.range.relIndex b.ker
    let k:=b.range.relIndex n.ker
    0<h ∧ 0<k ∧ h*Nat.card G=k*∏ i:MulAction.orbitRel.Quotient G P,Nat.card (MulAction.stabilizer G i.out)) →
   let A:=AdeleRing (𝓞 D) D
   let T:=A⊗[D]N
   let P:=(Units.map (algebraMap D A).toMonoidHom).range ⊔ (Units.map (Algebra.norm A (S:=T))).range
   let q:=QuotientGroup.mk' (Units.map (Algebra.TensorProduct.includeRight (R:=D) (A:=A) (B:=N)).toMonoidHom).range
   let a(s:Gal(N/D)):=Units.mapEquiv (Algebra.TensorProduct.congr (AlgEquiv.refl (R:=A) (A₁:=A)) s).toMulEquiv
   let n:=q.comp (∏ s:Gal(N/D),(a s).toMonoidHom)
   let b:=q.comp ((a g).toMonoidHom / MonoidHom.id Tˣ)
   let k:=b.range.relIndex (n.ker.map q)
   0<k ∧ P.index=Module.finrank D N*k
) := by
  intro exactSeq classes geo D N _ _ _ _ _ _ _ g gen cut
  let G := Gal(N/D)
  let A := AdeleRing (𝓞 D) D
  let T := A ⊗[D] N
  let I := (Units.map (Algebra.TensorProduct.includeRight (R:=D) (A:=A) (B:=N)).toMonoidHom).range
  let C := Tˣ ⧸ I
  let q := QuotientGroup.mk' I
  let a (s:G) := Units.mapEquiv (Algebra.TensorProduct.congr (AlgEquiv.refl (R:=A) (A₁:=A)) s).toMulEquiv
  obtain ⟨c,compat,idx⟩ := classes D N g gen
  letI : MulDistribMulAction G C := c
  obtain ⟨S,stable,u,ua,z,pinf,pfin,J,group,action,i,j,hi,hj,hinj,hsur,hker,j0,j1,jprod⟩ :=
    geo D N g gen c compat
  letI : CommGroup J := group
  letI : MulDistribMulAction G J := action
  let U := (S:Set (HeightOneSpectrum (𝓞 N))).unit N
  letI : MulDistribMulAction G U := u
  let X := InfinitePlace N ⊕ ↥S
  letI : MulAction G X := z
  letI : Fintype (MulAction.orbitRel.Quotient G X) := Fintype.ofFinite _
  obtain ⟨z',pinf',pfin',nu,bu,hnu,hbu,hu,ku,units⟩ := cut S g gen stable
  have ez : z'=z := by
    apply MulAction.ext
    funext s x
    cases x with
    | inl w => exact (pinf' s w).trans (pinf s w).symm
    | inr w => exact (Function.injective_id.sumMap Subtype.val_injective) ((pfin' s w).trans (pfin s w).symm)
  subst z'
  let aut (M : Type) [CommGroup M] [MulDistribMulAction G M] (s:G) : M →* M := MulDistribMulAction.toMonoidEnd G M s
  let norm (M : Type) [CommGroup M] [MulDistribMulAction G M] : M →* M := ∏ s:G, aut M s
  have norm_apply (M:Type) [CommGroup M] [MulDistribMulAction G M] (x:M) : norm M x=∏ s:G,s • x :=
    MonoidHom.finsetProd_apply (aut M) Finset.univ x
  let cob (M : Type) [CommGroup M] [MulDistribMulAction G M] := aut M g / MonoidHom.id M
  let h (M : Type) [CommGroup M] [MulDistribMulAction G M] := (norm M).range.relIndex (cob M).ker
  let k (M : Type) [CommGroup M] [MulDistribMulAction G M] := (cob M).range.relIndex (norm M).ker
  have n_eq : nu=norm U := by
    ext x
    rw [hnu x]
    change _ = ((Units.coeHom N).comp U.subtype) ((∏ s:G,aut U s) x)
    rw [MonoidHom.finsetProd_apply,map_prod]
    exact Finset.prod_congr rfl (fun s _ => (ua s x).symm)
  have b_eq : bu=cob U := by
    apply MonoidHom.ext
    intro x
    apply Subtype.ext
    apply Units.ext
    rw [hbu x,←ua g x]
    exact (map_div ((Units.coeHom N).comp U.subtype) (g • x) x).symm
  subst nu
  subst bu
  let m := ∏ t:MulAction.orbitRel.Quotient G X,Nat.card (MulAction.stabilizer G t.out)
  change 0<h U at hu
  change 0<k U at ku
  change h U*Nat.card G=k U*m at units
  change h J=k J*m at jprod
  change 0<k J at j1
  obtain ⟨c0,c1,bal⟩ := exactSeq G U J C g gen i j hi hj hinj hsur hker hu ku j0 j1
  change h J*k U*k C=k J*h U*h C at bal
  have hc : h C=Nat.card G*k C := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.mul_pos j1 hu)
    calc k J*h U*h C = h J*k U*k C := bal.symm
         _ = k J*(k U*m)*k C := by rw [jprod]; ac_rfl
         _ = k J*h U*(Nat.card G*k C) := by rw [←units]; ac_rfl
  let nn := q.comp (∏ s:G,(a s).toMonoidHom)
  let bb := q.comp ((a g).toMonoidHom / MonoidHom.id Tˣ)
  have nn_eq (w:Tˣ) : nn w=norm C (q w) := by
    calc nn w = ∏ s:G,q (a s w) := by simp only [nn,MonoidHom.comp_apply,MonoidHom.finsetProd_apply,map_prod,MulEquiv.toMonoidHom_eq_coe,MulEquiv.coe_toMonoidHom]; rfl
         _ = ∏ s:G,s • (q w:C) := Finset.prod_congr rfl (fun s _ => (compat s w).symm)
         _ = norm C (q w) := (norm_apply C (q w)).symm
  have bb_eq (w:Tˣ) : bb w=cob C (q w) := by
    change q (a g w / w) = (g • q w) / q w
    rw [map_div,compat]
  have kn : nn.ker.map q=(norm C).ker := by
    ext w
    constructor
    · rintro ⟨z,hz,rfl⟩
      exact (nn_eq z).symm.trans hz
    · intro hw
      obtain ⟨z,rfl⟩ := QuotientGroup.mk'_surjective I w
      exact ⟨z,(nn_eq z).trans hw,rfl⟩
  have rb : bb.range=(cob C).range := by
    ext w
    constructor
    · rintro ⟨z,rfl⟩
      exact ⟨q z,(bb_eq z).symm⟩
    · rintro ⟨w,rfl⟩
      obtain ⟨z,rfl⟩ := QuotientGroup.mk'_surjective I w
      exact ⟨z,bb_eq z⟩
  change 0<bb.range.relIndex (nn.ker.map q) ∧ _=Module.finrank D N*bb.range.relIndex (nn.ker.map q)
  rw [rb,kn,←idx,←IsGalois.card_aut_eq_finrank]
  exact ⟨c1,hc⟩

end
end OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H1_R1_H1_R1_H1_R1_H2_R1

end

section
open NumberField IsDedekindDomain
open scoped NumberField TensorProduct Classical

 
namespace OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H1_R1_H1_R1_H1_R1_H2_R1_H3_R1
open NumberField IsDedekindDomain
open scoped NumberField TensorProduct Classical
noncomputable section



set_option maxHeartbeats 2400000 in
theorem deriveSupportedClassLocalFactors : (
∀(D N:Type)[Field D][NumberField D][Field N][NumberField N][Algebra D N]
   [FiniteDimensional D N][IsGalois D N](g:Gal(N/D)),(∀s,s∈Subgroup.zpowers g) →
   let G:=Gal(N/D)
   let V:=HeightOneSpectrum (𝓞 D)
   let W:=HeightOneSpectrum (𝓞 N)
   let A:=AdeleRing (𝓞 D) D
   let T:=A⊗[D]N
   let o(v:V)(x:T):=∀(w:W),w.asIdeal.LiesOver v.asIdeal →
    ∀(m:v.adicCompletion D→+*w.adicCompletion N)(f:T→+*w.adicCompletion N),Continuous m →
    (∀d:D,m (algebraMap D _ d)=algebraMap N _ (algebraMap D N d)) →
    (∀a:A,∀b:N,f (a ⊗ₜ[D] b)=m (a.2 v)*algebraMap N _ b) → f x∈w.adicCompletionIntegers N
   let p(s:G):=HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapAlgEquiv s).toRingEquiv
   let l:=Units.map (Algebra.TensorProduct.includeRight (R:=D) (A:=A) (B:=N)).toMonoidHom
   ∃(R:Finset V)(S:Finset W)(J:Subgroup Tˣ),(∀w:W,w∈S ↔ ∃v∈R,w.asIdeal.LiesOver v.asIdeal) ∧
   (∀v:V,v∉R → ∀w:W,w.asIdeal.LiesOver v.asIdeal → w.asIdeal.ramificationIdx (𝓞 D)=1) ∧
   (∀x:Tˣ,x∈J ↔ ∀v:V,v∉R → o v x.val ∧ o v x.inv) ∧
   J⊔l.range=⊤ ∧ Function.Injective l ∧ J.comap l=(S:Set W).unit N ∧ (∀s w,w∈S ↔ p s w∈S) ∧
   let U:=(S:Set W).unit N
   ∃ u:MulDistribMulAction G U,letI:=u; ∀s:G,∀x:U,((s•x).val:N)=s (x.val:N)
) → (
∀(D N:Type)[Field D][NumberField D][Field N][NumberField N][Algebra D N]
   [FiniteDimensional D N][IsGalois D N](g:Gal(N/D)),(∀s,s∈Subgroup.zpowers g) →
   let G:=Gal(N/D)
   let V:=HeightOneSpectrum (𝓞 D)
   let W:=HeightOneSpectrum (𝓞 N)
   let A:=AdeleRing (𝓞 D) D
   let T:=A⊗[D]N
   let o(v:V)(x:T):=∀(w:W),w.asIdeal.LiesOver v.asIdeal →
    ∀(m:v.adicCompletion D→+*w.adicCompletion N)(f:T→+*w.adicCompletion N),Continuous m →
    (∀d:D,m (algebraMap D _ d)=algebraMap N _ (algebraMap D N d)) →
    (∀a:A,∀b:N,f (a ⊗ₜ[D] b)=m (a.2 v)*algebraMap N _ b) → f x∈w.adicCompletionIntegers N
   let p(s:G):=HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapAlgEquiv s).toRingEquiv
   let a(s:G):=Units.mapEquiv (Algebra.TensorProduct.congr (AlgEquiv.refl (R:=A) (A₁:=A)) s).toMulEquiv
   ∀(R:Finset V)(S:Finset W)(J:Subgroup Tˣ),(∀w:W,w∈S ↔ ∃v∈R,w.asIdeal.LiesOver v.asIdeal) →
   (∀v:V,v∉R → ∀w:W,w.asIdeal.LiesOver v.asIdeal → w.asIdeal.ramificationIdx (𝓞 D)=1) →
   (∀x:Tˣ,x∈J ↔ ∀v:V,v∉R → o v x.val ∧ o v x.inv) →
   let X:=InfinitePlace N ⊕ ↥S
   ∃ z:MulAction G X, letI:=z; letI:Fintype (MulAction.orbitRel.Quotient G X):=Fintype.ofFinite _
   (∀s:G,∀w:InfinitePlace N,s•(Sum.inl w:X)=Sum.inl (s•w)) ∧
   (∀s:G,∀w:↥S,Sum.map id Subtype.val (s•(Sum.inr w:X))=Sum.inr (p s w.val)) ∧
   ∃ β:MulDistribMulAction G J,letI:=β; (∀s:G,∀x:J,(s•x).val=a s x.val) ∧
   let b(s:G):J→*J:=MulDistribMulAction.toMonoidEnd G J s
   let n:J→*J:=∏s:G,b s
   let d:=b g / MonoidHom.id J
   let h:=n.range.relIndex d.ker
   let k:=d.range.relIndex n.ker
   0<h ∧ 0<k ∧ h=k*∏t:MulAction.orbitRel.Quotient G X,Nat.card (MulAction.stabilizer G t.out)
) → (
∀(D N:Type)[Field D][NumberField D][Field N][NumberField N][Algebra D N]
   [FiniteDimensional D N][IsGalois D N](g:Gal(N/D)),(∀ s,s∈Subgroup.zpowers g) →
   let G:=Gal(N/D)
   let A:=AdeleRing (𝓞 D) D
   let T:=A⊗[D]N
   let I:=(Units.map (Algebra.TensorProduct.includeRight (R:=D) (A:=A) (B:=N)).toMonoidHom).range
   let C:=Tˣ⧸I
   let q:=QuotientGroup.mk' I
   let a(s:G):=Units.mapEquiv (Algebra.TensorProduct.congr (AlgEquiv.refl (R:=A) (A₁:=A)) s).toMulEquiv
   ∀ c:MulDistribMulAction G C,letI:=c; (∀ s:G,∀ z:Tˣ,s•q z=q (a s z)) →
   let p(s:G):=HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapAlgEquiv s).toRingEquiv
   ∃ S:Finset (HeightOneSpectrum (𝓞 N)), (∀ s w,w∈S ↔ p s w∈S) ∧
   let U:=(S:Set (HeightOneSpectrum (𝓞 N))).unit N
   let X:=InfinitePlace N ⊕ ↥S
   ∃ u:MulDistribMulAction G U, letI:=u; (∀ s:G,∀ x:U,((s•x).val:N)=s (x.val:N)) ∧
   ∃ z:MulAction G X, letI:=z; letI:Fintype (MulAction.orbitRel.Quotient G X):=Fintype.ofFinite _
   (∀ s:G,∀ w:InfinitePlace N,s•(Sum.inl w:X)=Sum.inl (s•w)) ∧
   (∀ s:G,∀ w:↥S,Sum.map id Subtype.val (s•(Sum.inr w:X))=Sum.inr (p s w.val)) ∧
   ∃ (J:Type)(j₀:CommGroup J), letI:=j₀; ∃ β:MulDistribMulAction G J, letI:=β
   ∃ (i:U→*J)(j:J→*C),(∀ s:G,∀ x:U,i (s•x)=s•i x) ∧ (∀ s:G,∀ x:J,j (s•x)=s•j x) ∧
   Function.Injective i ∧ Function.Surjective j ∧ i.range=j.ker ∧
   let idx(M:Type)[CommGroup M][MulDistribMulAction G M]:=
    let a(s:G):M→*M:=MulDistribMulAction.toMonoidEnd G M s
    let n:M→*M:=∏ s:G,a s
    let b:=a g / MonoidHom.id M
    (n.range.relIndex b.ker,b.range.relIndex n.ker)
   let v:=idx J
   0<v.1 ∧ 0<v.2 ∧ v.1=v.2*∏ t:MulAction.orbitRel.Quotient G X,Nat.card (MulAction.stabilizer G t.out)
) := by
  intro support factors D N _ _ _ _ _ _ _ g gen
  dsimp only
  intro c compat
  let G:=Gal(N/D)
  let A:=AdeleRing (𝓞 D) D
  let T:=A⊗[D]N
  let l:=Units.map (Algebra.TensorProduct.includeRight (R:=D) (A:=A) (B:=N)).toMonoidHom
  let C:=Tˣ⧸l.range
  let q:=QuotientGroup.mk' l.range
  let a(s:G):=Units.mapEquiv (Algebra.TensorProduct.congr (AlgEquiv.refl (R:=A) (A₁:=A)) s).toMulEquiv
  letI : MulDistribMulAction G C:=c
  obtain ⟨R,S,J,above,ram,integral,hJ,hl,principal,stable,u,ua⟩ := support D N g gen
  obtain ⟨z,zinf,zfin,β,βa,h,k,e⟩:= factors D N g gen R S J above ram integral
  let U:=(S:Set (HeightOneSpectrum (𝓞 N))).unit N
  letI : MulDistribMulAction G U:=u
  letI : MulDistribMulAction G J:=β
  let i:U→*J := (l.comp U.subtype).codRestrict J (fun x => by
    change x.val ∈ J.comap l
    rw [principal]
    exact x.property)
  let j:J→*C:=q.comp J.subtype
  refine ⟨S,stable,u,ua,z,zinf,zfin,J,inferInstance,β,i,j,?_,?_,?_,?_,?_,h,k,e⟩
  · intro s x
    apply Subtype.ext
    change l (s • x).val = (s • i x).val
    rw [βa]
    apply Units.ext
    change (1:A) ⊗ₜ[D] ((s•x).val:N) = (Algebra.TensorProduct.congr (AlgEquiv.refl (R:=A) (A₁:=A)) s) ((1:A) ⊗ₜ[D] (x.val:N))
    rw [ua]
    rfl
  · intro s y
    change q (s•y).val=s • q y.val
    rw [βa,compat]
  · intro x y e
    exact Subtype.ext (hl (congrArg Subtype.val e))
  · intro x
    obtain ⟨y,rfl⟩:=QuotientGroup.mk'_surjective l.range x
    have hy : y∈J⊔l.range:=by rw [hJ]; trivial
    obtain ⟨t,ht,b,hb,rfl⟩:=Subgroup.mem_sup.mp hy
    refine ⟨⟨t,ht⟩,?_⟩
    change q t=q (t*b)
    have hq:q b=1:= (QuotientGroup.eq_one_iff b).2 hb
    rw [map_mul,hq]
    exact (mul_one (q t)).symm
  · ext x
    constructor
    · rintro ⟨y,rfl⟩
      exact (QuotientGroup.eq_one_iff _).mpr ⟨y.val,rfl⟩
    · intro hx
      change q x.val=1 at hx
      have hx' : x.val∈l.range := (QuotientGroup.eq_one_iff x.val).mp hx
      obtain ⟨y,hy⟩:=hx'
      have hyU:y∈U:=by
        change y∈(S:Set (HeightOneSpectrum (𝓞 N))).unit N
        rw [←principal]
        exact (show l y∈J from hy.symm ▸ x.property)
      exact ⟨⟨y,hyU⟩,Subtype.ext hy⟩

end
end OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H1_R1_H1_R1_H1_R1_H2_R1_H3_R1

end

namespace OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H1_R1_H1_R1_H1_R1
theorem main : H1 → H2 → H3 → H4 → OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H1_R1_H1_R1.H1 :=
  fun v1 v2 v3 v4 =>
    (OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H1_R1_H1_R1_H1_R1.deriveSupportedIdeleClasses v2.1 (OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H1_R1_H1_R1_H1_R1_H2_R1.deriveSupportedIdeleHerbrand v1 v2.2 (OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H1_R1_H1_R1_H1_R1_H2_R1_H3_R1.deriveSupportedClassLocalFactors v3 v4)))
end OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H1_R1_H1_R1_H1_R1
