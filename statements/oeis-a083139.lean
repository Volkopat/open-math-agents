import Mathlib

/-!
# A083139: Primes in A083137.

Source: https://oeis.org/A083139
Credit: @gblacher2

Conjecture (comment in A083139): "sequence is infinite."

A083137 (https://oeis.org/A083137): "Smallest palindromic number relatively prime to all the
previous terms", with a(1) = 1; its data and program show the greedy increasing reading, so each
next term is the least decimal palindrome larger than every previous term and coprime to every
previous term. The definitions below are the ones of `statements/oeis-a083137.lean`.

Conventions:
* A083137 is encoded as `a : ℕ → ℕ` with `a n = a(n+1)`, so `a 0 = 1`; the recursion pins `a`
  down uniquely whenever every next term exists;
* "A083139 is infinite" says that A083137 goes on forever and infinitely many of its terms are
  prime; it is stated as the existence of the sequence A083137 whose set of prime values is
  infinite.
-/

namespace OMA.S_oeis_a083139

/-- `x` is a palindrome in base 10. -/
def palindrome (x : ℕ) : Prop := (Nat.digits 10 x).reverse = Nat.digits 10 x

/-- `p` may follow `a 0, ..., a n` in A083137: it is a palindrome, larger than and coprime to
each of them. -/
def eligible (a : ℕ → ℕ) (n p : ℕ) : Prop :=
  palindrome p ∧ ∀ i ≤ n, a i < p ∧ p.Coprime (a i)

/-- `a` is A083137, shifted to offset 0. -/
def IsA083137 (a : ℕ → ℕ) : Prop :=
  a 0 = 1 ∧ ∀ n, IsLeast {p | eligible a n p} (a (n + 1))

/-- The conjecture: A083139, the primes in A083137, is infinite. -/
theorem main : ∃ a : ℕ → ℕ, IsA083137 a ∧ {p : ℕ | p.Prime ∧ p ∈ Set.range a}.Infinite := by
  sorry

end OMA.S_oeis_a083139
