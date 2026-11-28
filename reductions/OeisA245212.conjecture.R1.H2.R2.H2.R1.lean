import OMAReductions.R_OeisA245212_conjecture_R1_H2_R2

/-! An exact two-adic exponent test and reduced Mersenne denominator
for the nonsquare odd cofactor in A245212. The earlier reduction by
anmolspace isolates k = x / y; this reduction checks its unique reduced
fraction only on compatible prime supports. -/
namespace OMA.R_OeisA245212_conjecture_R1_H2_R2_H2_R1
open Nat Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma
open private OMA.R_OeisA245212_conjecture_R1_H2_R2.at_power_product
  OMA.R_OeisA245212_conjecture_R1_H2_R2.geom2
  OMA.R_OeisA245212_conjecture_R1_H2_R2.weighted2
  OMA.R_OeisA245212_conjecture_R1_H2_R2.weighted_gt from OMAReductions.R_OeisA245212_conjecture_R1_H2_R2

private theorem numerator {a b u y : ℕ} (ha : 0<a) (eq : a*u=b*y) :
    let g := a.gcd b
    let Q := a/g
    Q∣y ∧ u=(b/g)*(y/Q) := by
  let g := a.gcd b
  let Q := a/g
  let P := b/g
  have gp : 0<g := Nat.gcd_pos_of_pos_left _ ha
  have aeq : Q*g=a := Nat.div_mul_cancel (Nat.gcd_dvd_left a b)
  have beq : P*g=b := Nat.div_mul_cancel (Nat.gcd_dvd_right a b)
  have qp : 0 < Q := Nat.div_pos (Nat.le_of_dvd ha (Nat.gcd_dvd_left a b)) gp
  have ab : Q*u=P*y := by
    apply Nat.eq_of_mul_eq_mul_right gp
    calc
      Q*u*g = Q*g*u := by ring
      _ = a*u := by rw [aeq]
      _ = b*y := eq
      _ = P*y*g := by rw [←beq]; ring
  have cp : Q.Coprime P := Nat.coprime_div_gcd_div_gcd gp
  have div : Q∣y := cp.dvd_of_dvd_mul_left (ab ▸ dvd_mul_right Q u)
  refine ⟨div,?_⟩
  apply Nat.eq_of_mul_eq_mul_left qp
  change Q*u = Q*(P*(y/Q))
  rw [ab,←Nat.mul_assoc,mul_comm Q P,Nat.mul_assoc,Nat.mul_div_cancel' div]

/-- Exact prime-exponent obstruction for a divisor equality, at any power of two. -/
def H1 : Prop :=
  ∀ k m : ℕ, Odd m → OeisA245212.a (2^k*m) = (σ 1 (2^k*m) : ℤ) →
    (let E := ∑ p : m.primeFactors, (m.factorization p+2).factorization 2
      let U := ∑ p : m.primeFactors, if Odd (m.factorization p) then ((p:ℕ)+1).factorization 2-1 else 0
      let H := 1+k+(k+1).factorization 2
      if U < H then E=m.primeFactors.card+U
      else if H < U then E=m.primeFactors.card+H else m.primeFactors.card+H<E)

/-- Only the numerator of one reduced fraction survives both the two-adic
test and the Mersenne denominator divisibility test. -/
def H2 : Prop :=
  ∀ m : ℕ, Odd m → 1 < m → ¬ IsSquare m →
    let A := m*m.divisors.card
    let F := ∑ d ∈ m.divisors, d*d.divisors.card
    let x := A-σ 1 m
    let y := F-A
    let k := x/y
    let D := 2^(k+1)-1
    let g := D.gcd (k+1)
    let Q := D/g
    1 ≤ k →
    (let E := ∑ p : m.primeFactors, (m.factorization p+2).factorization 2
      let U := ∑ p : m.primeFactors, if Odd (m.factorization p) then ((p:ℕ)+1).factorization 2-1 else 0
      let H := 1+k+(k+1).factorization 2
      if U < H then E=m.primeFactors.card+U
      else if H < U then E=m.primeFactors.card+H else m.primeFactors.card+H<E) → Q∣y → x%y ≠ ((k+1)/g)*(y/Q)

theorem main : H1 → H2 → OMA.R_OeisA245212_conjecture_R1_H2_R2.H2 := by
  intro test remain m om hm ns
  let A := m*m.divisors.card
  let F := ∑ d ∈ m.divisors, d*d.divisors.card
  let S := σ 1 m
  let x := A-S
  let y := F-A
  let k := x/y
  change 1 ≤ k → 2^(k+1)*(x-k*y) ≠ x+y
  intro hk eq
  have sumdiv : S ≤ A := by
    change σ 1 m ≤ m*m.divisors.card
    rw [sigma_one_apply]
    calc
      _ ≤ ∑ _ ∈ m.divisors, m := Finset.sum_le_sum fun _ hd => Nat.divisor_le hd
      _ = _ := by simp [mul_comm]
  have wy : A < F := OMA.R_OeisA245212_conjecture_R1_H2_R2.weighted_gt m hm
  have ax : x+S=A := Nat.sub_add_cancel sumdiv
  have fy : y+A=F := Nat.sub_add_cancel wy.le
  have qr : x%y+k*y=x := by simpa only [k,mul_comm] using Nat.mod_add_div x y
  have rem : x-k*y=x%y := by omega
  rw [rem] at eq
  have powpos : 0 < 2^(k+1) := by positivity
  have succD : (2^(k+1)-1)+1=2^(k+1) := by omega
  have ratio : (2^(k+1)-1)*(x%y)=(k+1)*y := by
    nlinarith only [congrArg (fun z : ℕ => z*(x%y)) succD,eq,qr]
  have dp : 0 < 2^(k+1)-1 := by have := Nat.one_lt_two_pow (by omega : k+1≠0); omega
  obtain ⟨d,n⟩ := numerator dp ratio
  apply remain m om hm ns hk _ d n
  apply test k m om
  apply (OMA.R_OeisA245212_conjecture_R1_H2_R2.at_power_product 2 k m Nat.prime_two
    (by omega) (Nat.coprime_two_left.mpr om)).mpr
  change (∑ j ∈ range (k+1), ((j+1)*F+S)*2^j) = (2*m*(k+1)*m.divisors.card)*2^k
  have split : (∑ j ∈ range (k+1), ((j+1)*F+S)*2^j) =
      (∑ j ∈ range (k+1), 2^j*(j+1))*F + (∑ j ∈ range (k+1),2^j)*S := by
    rw [sum_mul,sum_mul,←sum_add_distrib]
    exact sum_congr rfl (fun _ _ => by ring)
  have rhs : (2*m*(k+1)*m.divisors.card)*2^k=(k+1)*2^(k+1)*A := by
    dsimp only [A]; rw [pow_succ]; ring
  rw [split,OMA.R_OeisA245212_conjecture_R1_H2_R2.weighted2,rhs,←fy,←ax]
  have geo := OMA.R_OeisA245212_conjecture_R1_H2_R2.geom2 k
  nlinarith only [congrArg (fun z : ℕ => z*S) geo,eq,
    congrArg (fun z : ℕ => 2^(k+1)*z) qr]

end OMA.R_OeisA245212_conjecture_R1_H2_R2_H2_R1
