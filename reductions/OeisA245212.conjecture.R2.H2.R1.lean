import OMAReductions.R_OeisA245212_conjecture_R2

/-! A finite exhaustion at each fixed number of distinct odd primes. The cutoff data are independent of the solutions. -/
namespace OMA.R_OeisA245212_conjecture_R2_H2_R1
open Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- Large rank or large dyadic order bounds the number of divisors of the odd part. -/
def H1 : Prop :=
  let cost := Nat.rec (motive:=fun _=>ℕ→ℕ) (fun _=>1)
    (fun _ f u=>2*(u+1)*f (2*(u+1)^2))
  let fixed := Nat.rec (motive:=fun _=>ℕ→ℕ) (fun _=>1) (fun i f x=>
    let u:=f x; let b:=2*u*x*2^i+2
    2*u+(x^(i+1)*(b^2)^(i+1))*cost (i+1) (x*(b*(x*b)+1)^(i+1)))
  let envelope (j x : ℕ) := ∑i∈range (j+1),fixed i x
  let poly (j x : ℕ) := let u:=2*envelope j x; 2*u+2*u*(2*envelope j (x+2*u))
  let cut (j D : ℕ) := let a:=poly j 1+1; let d:=poly j 2
                         a*(16*(d*D+1)^2+2*(a*D)+6)^d
  let length (r : ℕ) :=
    let j:=(3*r+4)^(2*r+1)
    let e:=(r+2)*j+r
    let h:=12*e+4
    let s:=128+2*r*2^r+(2^(16*(e+2)^2+8)+(16*128^e)^2)+2+16*(h*j+2)^2
    s+cut (r+1) (2*e+1+h*j*r)+(s+2^270+16*140^2)+cut (r+1) (1+h*j*r)
  ∀ a m : ℕ, Odd m → 1 < m → (5 ≤ m.primeFactors.card ∨ 256≤a) →
    OeisA245212.a (2^a*m)=(σ 1 (2^a*m):ℤ) →
    m.divisors.card≤(length m.primeFactors.card)^m.primeFactors.card

/-- Uniform bounds on all odd prime powers in the remaining small ranks and dyadic orders give this second divisor-count cutoff. -/
def H2 : Prop :=
  let w : ArithmeticFunction ℕ := (ArithmeticFunction.id.pmul (σ 0))*ArithmeticFunction.zeta
  let budget (A r : ℕ) := Nat.rec 1 (fun i z=>max (2*z) ((2+2*A*2^i*z)^(i+1))) r
  let threshold (A S r : ℕ) := budget A r*(2*A*r*2^r+2*S)
  let step (h r : ℕ) :=
    let A:=w h; let H:=2*(h*σ 0 h); let e:=threshold A (σ 1 h) r
    h*(max (e+1) (r*H*(σ 1 h+1)/(H-A))+1)^e
  let two (B : ℕ) :=
    let C:=2*B^3+1; let P:=2*C*(C+4)
    let scalar:=16*(C+C+1)
    let Z:=P^4+scalar+C+2*C*P+2
    let expo:=4*C*Z+2*(C+C*Z^2)
    let scale:=max scalar ((2*(4*C+C))^2)
    let multiplier:=2*P*(C+C)*(C*P+1)
    let loose:=2*C+4*C*P+max 784 (64*(scale*multiplier^6))
    4*(B*max 1 (max (Z^expo) (P^loose)))^7
  let next (B r : ℕ) :=
    let C:=2*B^3+1
    let e:=threshold C C r
    B*(max (e+1) (r*C*(C+1))+1)^e
  let small := ∑k∈range 256,
    (two (2^k) + 4*((range (step (2^k) 3+1)).sup (fun h=>step h 2))^7 +
      two (next (next (2^k) 4) 3))
  ∀ a m : ℕ, a<256 → Odd m → m.primeFactors.card≤4 →
    OeisA245212.a (2^a*m)=(σ 1 (2^a*m):ℤ) → m.divisors.card ≤ small

/-- Finite arithmetic for each rank, with all indices including the divisor count bounded. -/
def H3 : Prop :=
  let cost := Nat.rec (motive:=fun _=>ℕ→ℕ) (fun _=>1)
    (fun _ f u=>2*(u+1)*f (2*(u+1)^2))
  let fixed := Nat.rec (motive:=fun _=>ℕ→ℕ) (fun _=>1) (fun i f x=>
    let u:=f x; let b:=2*u*x*2^i+2
    2*u+(x^(i+1)*(b^2)^(i+1))*cost (i+1) (x*(b*(x*b)+1)^(i+1)))
  let envelope (j x : ℕ) := ∑i∈range (j+1),fixed i x
  let poly (j x : ℕ) := let u:=2*envelope j x; 2*u+2*u*(2*envelope j (x+2*u))
  let cut (j D : ℕ) := let a:=poly j 1+1; let d:=poly j 2
                         a*(16*(d*D+1)^2+2*(a*D)+6)^d
  let length (r : ℕ) :=
    let j:=(3*r+4)^(2*r+1)
    let e:=(r+2)*j+r
    let h:=12*e+4
    let s:=128+2*r*2^r+(2^(16*(e+2)^2+8)+(16*128^e)^2)+2+16*(h*j+2)^2
    s+cut (r+1) (2*e+1+h*j*r)+(s+2^270+16*140^2)+cut (r+1) (1+h*j*r)
  let w : ArithmeticFunction ℕ := (ArithmeticFunction.id.pmul (σ 0))*ArithmeticFunction.zeta
  let budget (A r : ℕ) := Nat.rec 1 (fun i z=>max (2*z) ((2+2*A*2^i*z)^(i+1))) r
  let threshold (A S r : ℕ) := budget A r*(2*A*r*2^r+2*S)
  let step (h r : ℕ) :=
    let A:=w h; let H:=2*(h*σ 0 h); let e:=threshold A (σ 1 h) r
    h*(max (e+1) (r*H*(σ 1 h+1)/(H-A))+1)^e
  let two (B : ℕ) :=
    let C:=2*B^3+1; let P:=2*C*(C+4)
    let scalar:=16*(C+C+1)
    let Z:=P^4+scalar+C+2*C*P+2
    let expo:=4*C*Z+2*(C+C*Z^2)
    let scale:=max scalar ((2*(4*C+C))^2)
    let multiplier:=2*P*(C+C)*(C*P+1)
    let loose:=2*C+4*C*P+max 784 (64*(scale*multiplier^6))
    4*(B*max 1 (max (Z^expo) (P^loose)))^7
  let next (B r : ℕ) :=
    let C:=2*B^3+1
    let e:=threshold C C r
    B*(max (e+1) (r*C*(C+1))+1)^e
  let small := ∑k∈range 256,
    (two (2^k) + 4*((range (step (2^k) 3+1)).sup (fun h=>step h 2))^7 +
      two (next (next (2^k) 4) 3))
  ∀ r : ℕ, ∀ t ≤ (length r)^r+small, ∀ a < t*(2*Nat.log 2 (8*t^3)+2),
    ∀ m ≤ ((2^(a+1)-1)*(a+2)*t^2)^(t-1), Odd m → 1 < m → m.primeFactors.card=r →
    m.divisors.card=t → OeisA245212.a (2^a*m)≠(σ 1 (2^a*m):ℤ)

theorem main : H1 → H2 → H3 → OMA.R_OeisA245212_conjecture_R2.H2 := by
  intro big little finite t a ha m hm odd large count eqn
  apply finite m.primeFactors.card t _ a ha m hm odd large rfl count eqn
  by_cases regime : 5 ≤ m.primeFactors.card ∨ 256≤a
  · exact count ▸ (big a m odd large regime eqn).trans (Nat.le_add_right _ _)
  · exact count ▸ (little a m (by omega) odd (by omega) eqn).trans (Nat.le_add_left _ _)

end OMA.R_OeisA245212_conjecture_R2_H2_R1
