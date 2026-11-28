import Mathlib

/-!
# Consecutive numbers with semiprime digit-sum quotients

Source: https://oeis.org/A085774
Credit: @HBreitkreutz

Jason Earls conjectures that infinitely many consecutive pairs have this property.
-/

namespace OMA.S_oeis_a085774

/-- Dividing `n` by its decimal digit sum gives the product of two primes,
which may be equal. The product identity enforces exact division. -/
def hasSemiprimeQuotient (n : ℕ) : Prop :=
  0 < n ∧ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = (Nat.digits 10 n).sum * (p * q)

/-- Infinitely many `k` and their successors both have semiprime quotients. -/
theorem main : {k : ℕ | hasSemiprimeQuotient k ∧ hasSemiprimeQuotient (k + 1)}.Infinite := by
  sorry

end OMA.S_oeis_a085774
