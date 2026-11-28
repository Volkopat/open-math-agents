import OMAReductions.R_OeisA245212_conjecture_R1_H2_R2_H2_R1

/-! Invert the reduced denominator of the dyadic identity.  The remaining
odd-cofactor statement no longer uses the dyadic exponent, a Mersenne
division, or the two-adic compatibility test as input. -/
namespace OMA.R_OeisA245212_conjecture_R1_H2_R2_H2_R1_H2_R1
open Nat Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma
open private OMA.R_OeisA245212_conjecture_R1_H2_R2.weighted_gt
  from OMAReductions.R_OeisA245212_conjecture_R1_H2_R2

/-- The reduced denominator alone determines both the index and the
reduced numerator, using only distinct primes of the denominator. -/
def H1 : Prop := ∀ t : ℕ, 2≤t →
  let D:=2^t-1
  let G:=D.gcd t
  let z:=D/G
  let i:=z.primeFactors.lcm (fun p=>orderOf (2 : ZMod p))
  i=t ∧ (i.divisors.filter (fun d=>d.Coprime z)).sup id=t/G

/-- Factor the reduced denominator of the divisor ratio. The resulting
index and numerator prescribe a single candidate value of x, and only
when the reconstructed integer is a power of two of the correct size. -/
def H2 : Prop := ∀ m : ℕ, Odd m → 1 < m → ¬ IsSquare m →
  let A:=m*m.divisors.card
  let x:=A-σ 1 m
  let y:=(∑ d ∈ m.divisors, d*d.divisors.card)-A
  let h:=x.gcd y
  let z:=y/h
  let t:=z.primeFactors.lcm (fun p=>orderOf (2 : ZMod p))
  let b:=(t.divisors.filter (fun d=>d.Coprime z)).sup id
  let N:=z*(t/b)+1
  2≤t → Nat.log 2 N=t → N=2^(Nat.log 2 N) →
    x≠(t-1)*y+h*b

theorem linear {x y k : ℕ} (hy : 0<y) (hk : 1≤k)
    (quot : k=x/y) (inv : H1)
    (div : ((2^(k+1)-1)/((2^(k+1)-1).gcd (k+1)))∣y)
    (eqn : x%y=((k+1)/((2^(k+1)-1).gcd (k+1)))*
      (y/((2^(k+1)-1)/((2^(k+1)-1).gcd (k+1))))) :
    let h:=x.gcd y
    let z:=y/h
    let t:=z.primeFactors.lcm (fun p=>orderOf (2 : ZMod p))
    let b:=(t.divisors.filter (fun d=>d.Coprime z)).sup id
    let N:=z*(t/b)+1
    2≤t ∧ Nat.log 2 N=t ∧ N=2^(Nat.log 2 N) ∧ x=(t-1)*y+h*b := by
  let T:=k+1
  let D:=2^T-1
  let G:=D.gcd T
  let Q:=D/G
  let P:=T/G
  let h:=y/Q
  have tp : 0<T:=by dsimp [T];omega
  have Dp : 0<D:=Nat.sub_pos_of_lt (Nat.one_lt_two_pow tp.ne')
  have gp : 0<G:=Nat.gcd_pos_of_pos_left _ Dp
  have qp : 0<Q:=Nat.div_pos (Nat.le_of_dvd Dp (Nat.gcd_dvd_left _ _)) gp
  have pp : 0<P:=Nat.div_pos (Nat.le_of_dvd tp (Nat.gcd_dvd_right _ _)) gp
  have yq : Q*h=y:=Nat.mul_div_cancel' div
  have rem : x%y=P*h:=eqn
  have qr : x%y+k*y=x:=by simpa only [quot,mul_comm] using Nat.mod_add_div x y
  have cp : Q.Coprime P:=Nat.coprime_div_gcd_div_gcd gp
  have gh : x.gcd y=h:=by
    calc
      x.gcd y=(x%y).gcd y:=by nth_rewrite 1 [←qr];rw [Nat.gcd_add_mul_right_left]
      _=(P*h).gcd (Q*h):=congrArg₂ Nat.gcd rem yq.symm
      _=h:=by rw [Nat.gcd_mul_right,cp.symm.gcd_eq_one];simp
  have hp : 0<h:=Nat.div_pos (Nat.le_of_dvd hy div) qp
  have den : y/(x.gcd y)=Q:=by rw [gh,←yq,Nat.mul_div_cancel _ hp]
  obtain ⟨ix,nu⟩:=inv T (by dsimp [T];omega)
  change Q.primeFactors.lcm (fun p=>orderOf (2 : ZMod p))=T at ix
  change ((Q.primeFactors.lcm (fun p=>orderOf (2 : ZMod p))).divisors.filter
    (fun d=>d.Coprime Q)).sup id=P at nu
  have mul : P*G=T:=Nat.div_mul_cancel (Nat.gcd_dvd_right _ _)
  have tg : T/P=G:=by rw [←mul,Nat.mul_div_cancel_left _ pp]
  have qg : Q*G=D:=Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)
  have nn : Q*(T/P)+1=2^T:=by rw [tg,qg];dsimp [D];have:=Nat.two_pow_pos T;omega
  dsimp only
  rw [den,nu,ix,nn,Nat.log_pow (by decide : 1<2)]
  refine ⟨by dsimp [T];omega,rfl,rfl,?_⟩
  change x=k*y+x.gcd y*P
  rw [gh,←qr,rem]
  ring

theorem main : H1 → H2 → OMA.R_OeisA245212_conjecture_R1_H2_R2_H2_R1.H2 := by
  intro inv rem m odd big nonsq
  let A:=m*m.divisors.card
  let x:=A-σ 1 m
  let y:=(∑ d ∈ m.divisors, d*d.divisors.card)-A
  let k:=x/y
  dsimp only
  intro low _ dv eqn
  have hy : 0<y:=Nat.sub_pos_of_lt (OMA.R_OeisA245212_conjecture_R1_H2_R2.weighted_gt m big)
  obtain ⟨t,logN,power,candidate⟩:=linear (x:=x) (k:=k) hy low rfl inv dv eqn
  exact rem m odd big nonsq t logN power candidate

end OMA.R_OeisA245212_conjecture_R1_H2_R2_H2_R1_H2_R1
