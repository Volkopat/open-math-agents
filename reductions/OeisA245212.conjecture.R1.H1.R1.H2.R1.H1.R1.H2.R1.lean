import OMAReductions.R_OeisA245212_conjecture_R1_H1_R1_H2_R1_H1_R1
import Mathlib

/-! Recover the exponent in @steveDOTdigital's odd cofactor test (#6417)
from the odd prime divisors of the reduced cofactor ratio alone. The first
step is a general order identity. The second tests just one index per (m,p),
even if the nonzero cofactor difference has many prime-power divisors. -/
open Finset
open scoped ArithmeticFunction.sigma
namespace OMA.R_OeisA245212_conjecture_R1_H1_R1_H2_R1_H1_R1_H2_R1

/-- The denominator drops some factors shared with the index, but the
orders of its distinct odd prime divisors still recover the whole index. -/
def H1 : Prop :=
  ∀ p t : ℕ, p.Prime → 3≤t →
    let x : ℚ := t+(t:ℚ)/((p:ℚ)^t-1)
    (x.den.primeFactors.filter (·≠2)).lcm (fun q => orderOf (p : ZMod q))=t

/-- One exact fractional-part test per coprime cofactor and prime. All the
parent's exclusions are retained, evaluated only at the recovered index. -/
def H2 : Prop :=
  ∀ m p : ℕ, 0 < m → p.Prime → m.Coprime p →
    let W := ∑ d∈m.divisors,d*d.divisors.card
    let S := σ 1 m
    let R : ℤ := W-((p:ℤ)-1)*S
    let D : ℤ := ((p:ℤ)-1)*(2*((m*m.divisors.card:ℕ):ℤ)*((p:ℤ)-1)-(p:ℤ)*W)
    let x : ℚ := (-(p:ℤ)*R:ℤ)/ (D:ℚ)
    let t := (x.den.primeFactors.filter (·≠2)).lcm (fun q => orderOf (p : ZMod q))
    let n := m*p^(t-1)
    3≤t → D≠0 → R≠0 → p∈(W+S).divisors → p^(t-1)∈R.natAbs.divisors →
    1 < n → Odd n → ¬IsPrimePow n → 2*n.totient < n →
    (¬∃ a b u v : ℕ, a.Prime ∧ b.Prime ∧ a < b ∧ 3≤a ∧ 5≤b ∧ 0 < u ∧ 0 < v ∧ n=a^u*b^v) →
    (¬∃ k a b c u v w : ℕ, 0 < k ∧ a.Prime ∧ b.Prime ∧ c.Prime ∧
      5≤a ∧ a < b ∧ b < c ∧ 0 < u ∧ 0 < v ∧ 0 < w ∧ n=3^k*a^u*b^v*c^w) →
    x-(t:ℚ) ≠ (t:ℚ)/((p:ℚ)^t-1)

theorem main : H1 → H2 → OMA.R_OeisA245212_conjecture_R1_H1_R1_H2_R1_H1_R1.H2 := by
  intro recover rule m p e hm hp cop he W S R inp nz div n big odd nonpow tot no2 no4 equal
  let D : ℤ := ((p:ℤ)-1)*(2*((m*m.divisors.card:ℕ):ℤ)*((p:ℤ)-1)-(p:ℤ)*W)
  let C : ℤ := -(p:ℤ)*R
  have hC : C≠0 := mul_ne_zero (neg_ne_zero.mpr (by exact_mod_cast hp.ne_zero)) nz
  have br : R=(p:ℤ)^e * (((e:ℤ)+1)*D+p*R) := by
    change (W:ℤ)-((p:ℤ)-1)*S = _ at equal ⊢
    dsimp only [D,R]
    convert equal using 1 <;> ring
  have identity : C*((p:ℤ)^(e+1)-1)=D*((e:ℤ)+1)*(p:ℤ)^(e+1) := by
    dsimp only [C]; rw [pow_succ]
    linear_combination (p:ℤ)*br
  have pow_gt : 1<(p:ℤ)^(e+1) := by
    exact_mod_cast Nat.one_lt_pow (by omega : e+1≠0) hp.one_lt
  have hD : D≠0 := by
    intro zero
    rw [zero,zero_mul,zero_mul] at identity
    exact (mul_ne_zero hC (sub_ne_zero.mpr pow_gt.ne')) identity
  let x : ℚ := (C:ℚ)/(D:ℚ)
  have rat : x = (e+1:ℕ)+(e+1:ℕ)/((p:ℚ)^(e+1)-1) := by
    have z : (C:ℚ)*((p:ℚ)^(e+1)-1)=(D:ℚ)*((e:ℚ)+1)*(p:ℚ)^(e+1) := by exact_mod_cast identity
    have dd : (D:ℚ)≠0 := by exact_mod_cast hD
    have pp : (p:ℚ)^(e+1)-1≠0 := by
      have : (1:ℚ)<(p:ℚ)^(e+1) := by exact_mod_cast pow_gt
      linarith
    dsimp only [x]; push_cast
    field_simp [dd,pp]; linarith only [z]
  have index : (x.den.primeFactors.filter (·≠2)).lcm (fun q => orderOf (p : ZMod q))=e+1 := by
    rw [rat]; exact recover p (e+1) hp (by omega)
  let t := (x.den.primeFactors.filter (·≠2)).lcm (fun q => orderOf (p : ZMod q))
  have tt : t=e+1 := index
  have ee : t-1=e := by omega
  have val : m*p^(t-1)=n := by rw [ee]
  have out := rule m p hm hp cop (show 3≤t by omega) hD nz inp
    (show p^(t-1)∈R.natAbs.divisors by rwa [ee]) (val ▸ big) (val ▸ odd)
    (val ▸ nonpow) (val ▸ tot) (val ▸ no2) (val ▸ no4)
  change x-(t:ℚ) ≠ (t:ℚ)/((p:ℚ)^t-1) at out
  rw [tt] at out
  apply out
  linarith only [rat]

end OMA.R_OeisA245212_conjecture_R1_H1_R1_H2_R1_H1_R1_H2_R1
