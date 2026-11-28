import OMAReductions.R_OeisA245212_conjecture_R1_H1_R1_H2_R1

/-! Restricting the four-odd-prime A245212 case to bounded prime supports. -/

namespace OMA.R_OeisA245212_conjecture_R1_H1_R1_H2_R1_H2_R1

open Finset
open scoped ArithmeticFunction.sigma

/-- The prime support of any four-prime solution beginning with three lies
in this explicit range, independently of its exponents. -/
def H1 : Prop :=
  ∀ k p q r e f g : ℕ, 2 ≤ k → p.Prime → q.Prime → r.Prime →
    5 ≤ p → p < q → q < r → 0 < e → 0 < f → 0 < g →
    let n := 3^k*p^e*q^f*r^g
    OeisA245212.a n = (σ 1 n : ℤ) →
      p ∈ ({5,7} : Finset ℕ) ∧ q ≤ 31 ∧ r < 1000000000000000000

/-- Exclude the surviving bounded prime supports, with arbitrary positive exponents. -/
def H2 : Prop :=
  ∀ p ∈ ({5,7} : Finset ℕ), ∀ q ∈ Icc (p+1) 31,
    ∀ r ∈ Icc (q+1) 999999999999999999, q.Prime → r.Prime →
    ∀ k e f g : ℕ, 2 ≤ k → 0 < e → 0 < f → 0 < g →
    let n := 3^k*p^e*q^f*r^g
    2*n.totient < n → OeisA245212.a n ≠ (σ 1 n : ℤ)

theorem main : H1 → H2 → OMA.R_OeisA245212_conjecture_R1_H1_R1_H2_R1.H2 := by
  intro bound remaining k p q r e f g hk hp hq hr hp5 pq qr he hf hg n ht eq
  obtain ⟨p57, qs, rs⟩ := bound k p q r e f g hk hp hq hr hp5 pq qr he hf hg eq
  exact remaining p p57 q (mem_Icc.mpr ⟨pq, qs⟩) r (mem_Icc.mpr ⟨qr, by omega⟩)
    hq hr k e f g hk he hf hg ht eq
end OMA.R_OeisA245212_conjecture_R1_H1_R1_H2_R1_H2_R1
