import OMAReductions.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1
import Mathlib

/-!
# The one-prime norm obstruction
A point of infinite order gives a depth in the Gaussian division tower at which a local norm from a Kummer extension has vanishing linear coefficient. Global reciprocity supplies those local norms for every global unit when the extension can ramify at only one finite prime.
-/
namespace OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1
open Set MeasureTheory Complex NumberField IsDedekindDomain IntermediateField IsLocalRing
open scoped Classical NumberField

set_option maxHeartbeats 1200000 in
def H1 : Prop :=
  ∀ (n : ℕ) (hn : 0<n), let ω : ℝ := ∫ x in Ioi (n:ℝ), (Real.sqrt (x^3-(n:ℝ)^2*x))⁻¹;
  ∀ M : PeriodPair, M.ω₁=(ω:ℂ) → M.ω₂=I*(ω:ℂ) →
  ∀ P : (⟨0,0,0,-(n:ℚ)^2,0⟩ : WeierstrassCurve ℚ).toAffine.Point, ¬IsOfFinAddOrder P →
  ∃ B : ℕ, ∀ p : ℕ, p.Prime → B<p → p%4=1 → ¬p∣2*n → ∀ q : GaussianInt, q.norm.natAbs=p →
  let K:=ℚ⟮I⟯;
  let Ω:=algebraicClosure K ℂ;
  let A (r : ℕ) := (let t:=M.ω₁/(q:ℂ)^r;
                    (adjoin K {M.weierstrassP t,M.derivWeierstrassP t/2}).comap (algebraicClosure K ℂ).val);
  let T:=A 1;
  ∀ hT:NumberField T, letI:=hT;
  ∀ (w:HeightOneSpectrum (𝓞 T)) (z:𝓞 T), z∈w.asIdeal → (((z:T):Ω):ℂ)=(q:ℂ) →
  let O:=w.adicCompletionIntegers T; let L:=w.adicCompletion T; let e (x:T):L:=x;
  ∃ (r:ℕ) (h:T≤A (r+1)), let D:=A (r+1);
    letI : Algebra T D:=(IntermediateField.inclusion h).toAlgebra;
    ∃ hd:NumberField D, letI:=hd;
    ∃ (v:HeightOneSpectrum (𝓞 D)) (N:Type) (hn:Field N), letI:=hn;
    ∃ hN:NumberField N, letI:=hN;
    ∃ g:Algebra D N, letI:=g;
    FiniteDimensional D N ∧ IsAbelianGalois D N ∧ (∀ i:InfinitePlace D,i.IsComplex) ∧
    (∀ s:HeightOneSpectrum (𝓞 D),s≠v → ∀ t:HeightOneSpectrum (𝓞 N),t.asIdeal.LiesOver s.asIdeal →
      t.asIdeal.ramificationIdx (𝓞 D)=1) ∧
    ∀ (x:(𝓞 D)ˣ) (b:K),
    ∀ u u₀:Oˣ, ((u:O):L)=e (Algebra.norm T x.val.val) →
      ((u₀:O):L)=e (algebraMap K T b) → maximalIdeal O=Ideal.span {(u:O)-(u₀:O)} →
    let V:=v.adicCompletion D;
    ¬∃ t:HeightOneSpectrum (𝓞 N),t.asIdeal.LiesOver v.asIdeal ∧ ∃ f:V→+*t.adicCompletion N,
      Continuous f ∧ (∀ c:D,f (c:V)=((algebraMap D N c:N):t.adicCompletion N)) ∧
      letI:Algebra V (t.adicCompletion N):=f.toAlgebra;
      ∃ y:(t.adicCompletion N)ˣ,Algebra.norm V (y:t.adicCompletion N)=(x.val.val:V)

def H2 : Prop :=
  ∀ (D N:Type) [Field D] [NumberField D] [Field N] [NumberField N] [Algebra D N]
    [FiniteDimensional D N] [IsAbelianGalois D N] (v:HeightOneSpectrum (𝓞 D)),
  (∀ i:InfinitePlace D,i.IsComplex) →
  (∀ s:HeightOneSpectrum (𝓞 D),s≠v → ∀ t:HeightOneSpectrum (𝓞 N),t.asIdeal.LiesOver s.asIdeal →
    t.asIdeal.ramificationIdx (𝓞 D)=1) →
  ∀ x:(𝓞 D)ˣ,let V:=v.adicCompletion D
  ∃ t:HeightOneSpectrum (𝓞 N),t.asIdeal.LiesOver v.asIdeal ∧ ∃ f:V→+*t.adicCompletion N,
    Continuous f ∧ (∀ c:D,f (algebraMap D V c)=algebraMap N (t.adicCompletion N) (algebraMap D N c)) ∧
    letI:Algebra V (t.adicCompletion N):=f.toAlgebra
    ∃ y:(t.adicCompletion N)ˣ,Algebra.norm V (y:t.adicCompletion N)=algebraMap D V x.val.val

theorem main : H1 → H2 → OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1.H2 := by
  intro geometric reciprocity
  refine fun n hn M h₁ h₂ P hP => ?_
  obtain ⟨B,hB⟩:=geometric n hn M h₁ h₂ P hP
  refine ⟨B,?_⟩
  intro p hp hb hm hg q hq witness
  obtain ⟨hT,w,z,hz,he,a,b,⟨u,u₀,hu,h₀,hspan⟩,upper⟩:=witness
  obtain ⟨r,h,hd,v,N,hfield,hN,g,fd,ab,complex,unramified,obstruct⟩:=
    hB p hp hb hm hg q hq hT w z hz he
  obtain ⟨h',x,hx⟩:=upper r
  exact obstruct x b u u₀ (hx ▸ hu) h₀ hspan (@reciprocity _ N _ hd hfield hN g fd ab v complex unramified x)

end OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1
