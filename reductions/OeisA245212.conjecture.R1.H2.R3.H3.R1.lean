import OMAReductions.R_OeisA245212_conjecture_R1_H2_R3

namespace OMA.R_OeisA245212_conjecture_R1_H2_R3_H3_R1
open Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma

def H1 : Prop :=
  let w : ArithmeticFunction ℕ := (ArithmeticFunction.id.pmul (σ 0))*ArithmeticFunction.zeta
  let step (h r : ℕ) :=
    let A:=w h
    let H:=2*(h*σ 0 h)
    let b:=Nat.rec 1 (fun i t=>max (2*t) ((2+2*A*2^i*t)^(i+1))) r
    let e:=b*(2*A*r*2^r+2*σ 1 h)
    h*(max (e+1) (r*H*(σ 1 h+1)/(H-A))+1)^e
  let fixed (k : ℕ) := 4*((range (step (2^k) 3+1)).sup (fun h=>step h 2))^7
  let dy (t : ℕ) := t*(2*Nat.log 2 (8*t^3)+2)
  let core (t : ℕ) := ((2^(dy t+1)-1)*(dy t+2)*t^2)^(t-1)
  let f:=16^5
  let v (c : ℕ) := (∑ j∈range (4*c+1),fixed j)+
    ∑ t∈range ((c*(64*((f+4)*f+1)^2))^3+1),2^(dy t)*core t
  let D:=16^7
  let C:=2^(16*(D+2)^2+8)+(16*128^D)^2
  let s (z : ℕ) := 2*(512*(C+1)^2)^z+16*((2*(2*D)+1)*z+1)^2+64
  let j:=82*((2*D+1)+(2*(2*D+1)+3)*D)
  let N:=(C+512+s (20*D))+(8*(16*(j+1)^2+68+6*j))^81+1
  let K:=(∑ i∈range 256,fixed i)+((∑ i∈range 67,fixed i)+v (s D))+v 20+v N+v 16
  ∀ k m : ℕ, Odd m → m.primeFactors.card=3 →
    OeisA245212.a (2^k*m)=(σ 1 (2^k*m):ℤ) → 2^k*m≤K

def H2 : Prop :=
  let w : ArithmeticFunction ℕ := (ArithmeticFunction.id.pmul (σ 0))*ArithmeticFunction.zeta
  let step (h r : ℕ) :=
    let A:=w h
    let H:=2*(h*σ 0 h)
    let b:=Nat.rec 1 (fun i t=>max (2*t) ((2+2*A*2^i*t)^(i+1))) r
    let e:=b*(2*A*r*2^r+2*σ 1 h)
    h*(max (e+1) (r*H*(σ 1 h+1)/(H-A))+1)^e
  let fixed (k : ℕ) := 4*((range (step (2^k) 3+1)).sup (fun h=>step h 2))^7
  let dy (t : ℕ) := t*(2*Nat.log 2 (8*t^3)+2)
  let core (t : ℕ) := ((2^(dy t+1)-1)*(dy t+2)*t^2)^(t-1)
  let f:=16^5
  let v (c : ℕ) := (∑ j∈range (4*c+1),fixed j)+
    ∑ t∈range ((c*(64*((f+4)*f+1)^2))^3+1),2^(dy t)*core t
  let D:=16^7
  let C:=2^(16*(D+2)^2+8)+(16*128^D)^2
  let s (z : ℕ) := 2*(512*(C+1)^2)^z+16*((2*(2*D)+1)*z+1)^2+64
  let j:=82*((2*D+1)+(2*(2*D+1)+3)*D)
  let N:=(C+512+s (20*D))+(8*(16*(j+1)^2+68+6*j))^81+1
  let K:=(∑ i∈range 256,fixed i)+((∑ i∈range 67,fixed i)+v (s D))+v 20+v N+v 16
  ∀ k m : ℕ, 1 ≤ k → Odd m → 1 < m → m.primeFactors.card=3 → 2^k*m≤K →
    OeisA245212.a (2^k*m)≠(σ 1 (2^k*m):ℤ)

def H3 : Prop :=
  ∀ k m : ℕ, 1 ≤ k → Odd m → 1 < m → 4 ≤ m.primeFactors.card →
    OeisA245212.a (2^k*m)≠(σ 1 (2^k*m):ℤ)

theorem main : H1 → H2 → H3 → OMA.R_OeisA245212_conjecture_R1_H2_R3.H3 := by
  intro height finite many k m kp odd big rank eqn
  by_cases three : m.primeFactors.card=3
  · exact finite k m kp odd big three (height k m odd three eqn) eqn
  · exact many k m kp odd big (by omega) eqn

end OMA.R_OeisA245212_conjecture_R1_H2_R3_H3_R1
