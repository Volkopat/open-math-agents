import OMAReductions.R_CongruentNumber_Tunnell_even_R1_H3_R1_H2_R1_H1_R1
import Mathlib
/-! The quaternionic ideal families determine the odd Fourier coefficients. Their ramified local trace computes the Petersson moment at level 32. Half-translation and two finite calibrations eliminate the common divisor terms. -/
namespace OMA.R_CongruentNumber_Tunnell_even_R1_H3_R1_H2_R1_H1_R1_H2_R1
open Finset Polynomial MeasureTheory MatrixGroups ModularGroup CongruenceSubgroup
open scoped UpperHalfPlane Classical ComplexConjugate

def H1 : Prop :=
  let s (d:ℕ) :=
    let b := Icc (-((2*d:ℕ):ℤ)-1) (((2*d:ℕ):ℤ)+1)
    (b ×ˢ (b ×ˢ b)).filter (fun v => v.1^2+v.2.1^2+v.2.2^2=((2*d:ℕ):ℤ))
  let h (d:ℕ) := ((s d).filter (fun v => Odd v.1 ∧ Odd v.2.1 ∧ Even v.2.2 ∧ 0<v.1 ∧ 0<v.2.1)).card
  let P (d:ℕ) := (((s d).filter (fun v => v.1%4=v.2.1%4 ∧ v.2.2%8=0)).card:ℤ)-
    ((s d).filter (fun v => v.1%4=v.2.1%4 ∧ v.2.2%4=0 ∧ (v.1+v.2.1+2*(v.2.2/4))%4=0)).card
  let θ (d : ℕ) (z : ℂ) := (h d:ℂ) + 2*∑' m : ℕ,
    (∑ e ∈ m.divisors, ((if Odd e then jacobiSym (-((2*d:ℕ):ℤ)) e else 0 : ℤ):ℂ))*Function.Periodic.qParam 1 z^m
  let Q (d:ℕ) (z:ℍ) := θ d z*θ d (4*(z:ℂ))
  let R (d a k:ℕ) (b u:ℤ) (z:ℂ) := ∑' x:ℤ×ℤ,
    Complex.exp (2*Real.pi*Complex.I*z*k*((a*x.1+b*x.2:ℤ)^2+(2*(d:ℂ))*((x.2:ℂ)+(a:ℂ)*u/d)^2)/a)
  let K (d:ℕ) (i:ℕ×ℤ×ℕ×ℤ) (u v:ℤ) (z:ℂ) := R d i.1 1 i.2.1 u z*R d i.2.2.1 4 i.2.2.2 v z
  let T (d:ℕ) (i:ℕ×ℤ×ℕ×ℤ) (z:ℂ) := ∑' w:ZMod d×ZMod d,
    (∏ p:↥d.primeFactors, (Nat.card {t:ZMod p.val // (i.1:ZMod p.val)*t^2= -4*i.2.2.1 ∧
      (w.1.val:ZMod p.val)=t*w.2.val}:ℂ))*K d i w.1.val w.2.val z
  let G (d:ℕ) (i:ℕ×ℤ×ℕ×ℤ) := 0 < i.1 ∧ 0 < i.2.2.1 ∧ i.1.Coprime d ∧ i.2.2.1.Coprime d
  let E (F:ℍ→ℂ) (a:ℕ→ℂ) := ∀ z:ℍ,HasSum (fun m:ℕ => a m*Function.Periodic.qParam 1 z^m) (F z)
  ∃ U V:ℕ→ℂ, ∀ d:ℕ, Squarefree d → d%4=1 → ∃ (n:ℕ) (D:Fin n→ℕ×ℤ×ℕ×ℤ) (a:ℕ→ℂ),
    (∀ i,G d (D i)) ∧ (∀ z:ℍ, Q d z=∑ i,K d (D i) 0 0 z) ∧ E (fun z => ∑ i,T d (D i) z) a ∧
    ∀ m,Odd m → a m=(h d:ℂ)^2*U m+(P d:ℂ)^2*V m

def H2 : Prop :=
  let s (d:ℕ) :=
    let b := Icc (-((2*d:ℕ):ℤ)-1) (((2*d:ℕ):ℤ)+1)
    (b ×ˢ (b ×ˢ b)).filter (fun v => v.1^2+v.2.1^2+v.2.2^2=((2*d:ℕ):ℤ))
  let h (d:ℕ) := ((s d).filter (fun v => Odd v.1 ∧ Odd v.2.1 ∧ Even v.2.2 ∧ 0<v.1 ∧ 0<v.2.1)).card
  let θ (d : ℕ) (z : ℂ) := (h d:ℂ) + 2*∑' m : ℕ,
    (∑ e ∈ m.divisors, ((if Odd e then jacobiSym (-((2*d:ℕ):ℤ)) e else 0 : ℤ):ℂ))*Function.Periodic.qParam 1 z^m
  let Q (d:ℕ) (z:ℍ) := θ d z*θ d (4*(z:ℂ))
  let R (d a k:ℕ) (b u:ℤ) (z:ℂ) := ∑' x:ℤ×ℤ,
    Complex.exp (2*Real.pi*Complex.I*z*k*((a*x.1+b*x.2:ℤ)^2+(2*(d:ℂ))*((x.2:ℂ)+(a:ℂ)*u/d)^2)/a)
  let K (d:ℕ) (i:ℕ×ℤ×ℕ×ℤ) (u v:ℤ) (z:ℂ) := R d i.1 1 i.2.1 u z*R d i.2.2.1 4 i.2.2.2 v z
  let T (d:ℕ) (i:ℕ×ℤ×ℕ×ℤ) (z:ℂ) := ∑' w:ZMod d×ZMod d,
    (∏ p:↥d.primeFactors, (Nat.card {t:ZMod p.val // (i.1:ZMod p.val)*t^2= -4*i.2.2.1 ∧
      (w.1.val:ZMod p.val)=t*w.2.val}:ℂ))*K d i w.1.val w.2.val z
  let G (d:ℕ) (i:ℕ×ℤ×ℕ×ℤ) := 0 < i.1 ∧ 0 < i.2.2.1 ∧ i.1.Coprime d ∧ i.2.2.1.Coprime d
  let A (F:ℍ→ℂ) (z:ℍ) := (z.im:ℂ)^2*(ModularForm.eta (4*(z:ℂ))^2*ModularForm.eta (8*(z:ℂ))^2)*conj (F z)
  let L (n:ℕ) (F:ℍ→ℂ) := ∑' q:SL(2,ℤ) ⧸ Gamma0 n, ∫ z in fdo, A F (q.out⁻¹ • z)
  let reg (F:ℍ→ℂ) := Measurable (A F) ∧ (∀ (g:Gamma0 32) z,A F (g.val • z)=A F z) ∧
    ∀ q:SL(2,ℤ) ⧸ Gamma0 32, IntegrableOn (fun z => A F (q.out⁻¹ • z)) fdo
  ∀ d:ℕ, Squarefree d → d%4=1 → ∀ n (D:Fin n→ℕ×ℤ×ℕ×ℤ),
    (∀ i,G d (D i)) → (∀ z:ℍ,Q d z=∑ i,K d (D i) 0 0 z) →
    let F (z:ℍ) := ∑ i,T d (D i) z
    reg F ∧ L 32 F=L (32*d) (Q d)

def H3 : Prop :=
  let A (F:ℍ→ℂ) (z:ℍ) := (z.im:ℂ)^2*(ModularForm.eta (4*(z:ℂ))^2*ModularForm.eta (8*(z:ℂ))^2)*conj (F z)
  let L (n:ℕ) (F:ℍ→ℂ) := ∑' q:SL(2,ℤ) ⧸ Gamma0 n, ∫ z in fdo, A F (q.out⁻¹ • z)
  let reg (F:ℍ→ℂ) := Measurable (A F) ∧ (∀ (g:Gamma0 32) z,A F (g.val • z)=A F z) ∧
    ∀ q:SL(2,ℤ) ⧸ Gamma0 32, IntegrableOn (fun z => A F (q.out⁻¹ • z)) fdo
  let E (F:ℍ→ℂ) (a:ℕ→ℂ) := ∀ z:ℍ,HasSum (fun m:ℕ => a m*Function.Periodic.qParam 1 z^m) (F z)
  ∀ (F Y Z:ℍ→ℂ) (a b c u v:ℕ→ℂ) (x y w:ℕ) (t:ℤ),
    reg F → reg Y → reg Z → E F a → E Y b → E Z c →
    (∀ m,Odd m → a m=(x:ℂ)^2*u m+(t:ℂ)^2*v m) →
    (∀ m,Odd m → b m=(y:ℂ)^2*u m+4*v m) →
    (∀ m,Odd m → c m=(w:ℂ)^2*u m) →
    (w:ℂ)^2*(4*L 32 F-(t:ℂ)^2*L 32 Y)=(4*(x:ℂ)^2-(t:ℂ)^2*(y:ℂ)^2)*L 32 Z

def H4 : Prop :=
  let s (d:ℕ) :=
    let b := Icc (-((2*d:ℕ):ℤ)-1) (((2*d:ℕ):ℤ)+1)
    (b ×ˢ (b ×ˢ b)).filter (fun v => v.1^2+v.2.1^2+v.2.2^2=((2*d:ℕ):ℤ))
  let P (d:ℕ) := (((s d).filter (fun v => v.1%4=v.2.1%4 ∧ v.2.2%8=0)).card:ℤ)-
    ((s d).filter (fun v => v.1%4=v.2.1%4 ∧ v.2.2%4=0 ∧ (v.1+v.2.1+2*(v.2.2/4))%4=0)).card
  ∀ d:ℕ, d%4=1 → (d=1 → P d=2) ∧ (d=17 → P d=0)

theorem main : H1 → H2 → H3 → H4 → OMA.R_CongruentNumber_Tunnell_even_R1_H3_R1_H2_R1_H1_R1.H2 := by
  intro geometry modularity orthogonal calibrate
  let s (d:ℕ) :=
    let b := Icc (-((2*d:ℕ):ℤ)-1) (((2*d:ℕ):ℤ)+1)
    (b ×ˢ (b ×ˢ b)).filter (fun v => v.1^2+v.2.1^2+v.2.2^2=((2*d:ℕ):ℤ))
  let h (d:ℕ) := ((s d).filter (fun v => Odd v.1 ∧ Odd v.2.1 ∧ Even v.2.2 ∧ 0<v.1 ∧ 0<v.2.1)).card
  let P (d:ℕ) := (((s d).filter (fun v => v.1%4=v.2.1%4 ∧ v.2.2%8=0)).card:ℤ)-
    ((s d).filter (fun v => v.1%4=v.2.1%4 ∧ v.2.2%4=0 ∧ (v.1+v.2.1+2*(v.2.2/4))%4=0)).card
  let θ (d : ℕ) (z : ℂ) := (h d:ℂ) + 2*∑' m : ℕ,
    (∑ e ∈ m.divisors, ((if Odd e then jacobiSym (-((2*d:ℕ):ℤ)) e else 0 : ℤ):ℂ))*Function.Periodic.qParam 1 z^m
  let Q (d:ℕ) (z:ℍ) := θ d z*θ d (4*(z:ℂ))
  let R (d a k:ℕ) (b u:ℤ) (z:ℂ) := ∑' x:ℤ×ℤ,
    Complex.exp (2*Real.pi*Complex.I*z*k*((a*x.1+b*x.2:ℤ)^2+(2*(d:ℂ))*((x.2:ℂ)+(a:ℂ)*u/d)^2)/a)
  let K (d:ℕ) (i:ℕ×ℤ×ℕ×ℤ) (u v:ℤ) (z:ℂ) := R d i.1 1 i.2.1 u z*R d i.2.2.1 4 i.2.2.2 v z
  let T (d:ℕ) (i:ℕ×ℤ×ℕ×ℤ) (z:ℂ) := ∑' w:ZMod d×ZMod d,
    (∏ p:↥d.primeFactors, (Nat.card {t:ZMod p.val // (i.1:ZMod p.val)*t^2= -4*i.2.2.1 ∧
      (w.1.val:ZMod p.val)=t*w.2.val}:ℂ))*K d i w.1.val w.2.val z
  let G (d:ℕ) (i:ℕ×ℤ×ℕ×ℤ) := 0 < i.1 ∧ 0 < i.2.2.1 ∧ i.1.Coprime d ∧ i.2.2.1.Coprime d
  let A (F:ℍ→ℂ) (z:ℍ) := (z.im:ℂ)^2*(ModularForm.eta (4*(z:ℂ))^2*ModularForm.eta (8*(z:ℂ))^2)*conj (F z)
  let L (n:ℕ) (F:ℍ→ℂ) := ∑' q:SL(2,ℤ) ⧸ Gamma0 n, ∫ z in fdo, A F (q.out⁻¹ • z)
  let reg (F:ℍ→ℂ) := Measurable (A F) ∧ (∀ (g:Gamma0 32) z,A F (g.val • z)=A F z) ∧
    ∀ q:SL(2,ℤ) ⧸ Gamma0 32, IntegrableOn (fun z => A F (q.out⁻¹ • z)) fdo
  let E (F:ℍ→ℂ) (a:ℕ→ℂ) := ∀ z:ℍ,HasSum (fun m:ℕ => a m*Function.Periodic.qParam 1 z^m) (F z)
  obtain ⟨u,v,hD⟩ : ∃ U V:ℕ→ℂ, ∀ d:ℕ, Squarefree d → d%4=1 → ∃ (n:ℕ) (D:Fin n→ℕ×ℤ×ℕ×ℤ) (a:ℕ→ℂ),
    (∀ i,G d (D i)) ∧ (∀ z:ℍ, Q d z=∑ i,K d (D i) 0 0 z) ∧ E (fun z => ∑ i,T d (D i) z) a ∧
    ∀ m,Odd m → a m=(h d:ℂ)^2*U m+(P d:ℂ)^2*V m := geometry
  intro d hs hd
  have h₁ : Squarefree 1 := squarefree_one
  have h₁₇ : Squarefree 17 := (by decide : Nat.Prime 17).squarefree
  obtain ⟨n,D,a,hg,hq,ha,hodd⟩ := hD d hs hd
  obtain ⟨n₁,D₁,b,hg₁,hq₁,hb,hodd₁⟩ := hD 1 h₁ (by decide)
  obtain ⟨n₁₇,D₁₇,c,hg₁₇,hq₁₇,hc,hodd₁₇⟩ := hD 17 h₁₇ (by decide)
  obtain ⟨r,p⟩ := modularity d hs hd n D hg hq
  obtain ⟨r₁,p₁⟩ := modularity 1 h₁ (by decide) n₁ D₁ hg₁ hq₁
  obtain ⟨r₁₇,p₁₇⟩ := modularity 17 h₁₇ (by decide) n₁₇ D₁₇ hg₁₇ hq₁₇
  have e₁ : P 1=2 := (calibrate 1 (by decide)).1 rfl
  have e₁₇ : P 17=0 := (calibrate 17 (by decide)).2 rfl
  have e := orthogonal _ _ _ a b c u v (h d) (h 1) (h 17) (P d) r r₁ r₁₇ ha hb hc hodd
    (fun m hm => by rw [hodd₁ m hm,e₁]; norm_num)
    (fun m hm => by rw [hodd₁₇ m hm,e₁₇]; simp only [Int.cast_zero,zero_pow (by decide : (2:ℕ)≠0),zero_mul,add_zero])
  rw [p,p₁,p₁₇] at e
  exact e

end OMA.R_CongruentNumber_Tunnell_even_R1_H3_R1_H2_R1_H1_R1_H2_R1
