import Mathlib

/-!
# OEIS A039986: Primes Whose Every Distinct Digit Permutation Is Composite

Source: https://oeis.org/A039986
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Consider primes $p$ such that every distinct permutation of the base-10 digits of $p$
(including permutations with leading zeros, evaluated as a base-10 integer) is composite
(i.e. not prime and not $0$ or $1$, or equivalently for $q \ne p$ formed by permuting
the digits of $p$, $q$ is composite: `2 ≤ q ∧ ¬ Nat.Prime q`).

Conjecture: The only terms of this sequence having at least $4$ distinct base-10 digits are
the 19 numbers:
`2861, 4027, 4801, 5209, 5623, 5849, 24889, 26561, 40609, 40883, 66541, 66853, 85087, 85843, 86441, 288689, 442469, 558541, 55555429`,
and there are no terms with $5$ or more distinct digits.
-/

namespace OMA.S_oeis_a039986

/-- A prime `p` is in A039986 if every distinct permutation of its base-10 digits
evaluates to a composite number (`2 ≤ q ∧ ¬ Nat.Prime q`). -/
def InA039986 (p : ℕ) : Prop :=
  Nat.Prime p ∧
    ∀ l : List ℕ, l.Perm (Nat.digits 10 p) →
      let q := Nat.ofDigits 10 l
      q ≠ p → 2 ≤ q ∧ ¬ Nat.Prime q

/-- The 19 known terms of A039986 with 4 distinct base-10 digits. -/
def knownFourDistinct : Finset ℕ :=
  {2861, 4027, 4801, 5209, 5623, 5849, 24889, 26561, 40609, 40883,
   66541, 66853, 85087, 85843, 86441, 288689, 442469, 558541, 55555429}

theorem main :
    ∀ p : ℕ, InA039986 p → 4 ≤ (Nat.digits 10 p).toFinset.card →
      p ∈ knownFourDistinct := by
  sorry

end OMA.S_oeis_a039986
