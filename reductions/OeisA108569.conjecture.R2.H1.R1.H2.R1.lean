import OMAReductions.R_OeisA108569_conjecture_R2_H1_R1

-- Reduction OeisA108569.conjecture.R2.H1.R1.H2.R1 of step OeisA108569.conjecture.R2.H1.R1.H2
-- Credit: @marcusbuffett

/-!
# Odd primes in A108569: at most six prime factors of `2p - 1`, and the open rest

The parent step says that an odd prime `p` for which `m = p + φ(p) = 2p - 1` has at least three
distinct prime factors does not satisfy `φ(p) = φ(m)`, that is `2 φ(m) = m - 1`. This is the
case `k = 2` of Lehmer's totient problem `φ(m) ∣ m - 1`.

* `H1` (Lehmer 1932): the case of at most six distinct prime factors. The equation forces `m`
  to be squarefree and composite; then `3 ∤ m` because `3 ∣ m` would force the quotient to be
  `1 (mod 3)`, and for primes coprime to `6` the product
  `(5/4)(7/6)(11/10)(13/12)(17/16)(19/18)` is below `2`.
* `H2`: seven or more distinct prime factors, which stays open.
-/

namespace OMA.R_OeisA108569_conjecture_R2_H1_R1_H2_R1

/-- At most six distinct prime factors. -/
def H1 : Prop :=
  ∀ p : ℕ, p.Prime → Odd p → (p + p.totient).primeFactors.card ≤ 6 →
    p.totient ≠ (p + p.totient).totient

/-- The open part: seven or more distinct prime factors. -/
def H2 : Prop :=
  ∀ p : ℕ, p.Prime → Odd p → 7 ≤ (p + p.totient).primeFactors.card →
    p.totient ≠ (p + p.totient).totient

theorem main : H1 → H2 → OMA.R_OeisA108569_conjecture_R2_H1_R1.H2 := by
  intro h1 h2 p hp hodd _
  by_cases h6 : (p + p.totient).primeFactors.card ≤ 6
  · exact h1 p hp hodd h6
  · exact h2 p hp hodd (by omega)

end OMA.R_OeisA108569_conjecture_R2_H1_R1_H2_R1
