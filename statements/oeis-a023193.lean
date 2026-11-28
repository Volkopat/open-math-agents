import Mathlib

/-!
# A023193: a(n) gives the largest number k for which there is at least one admissible k-tuple taken from [0, 1, ..., n-1] if the tuple starts with 0.

Source: https://oeis.org/A023193
Credit: @azmiozgen

Conjecture (formula section, David W. Wilson, May 23 2005; the comments attribute it to Dickson):
a(n) = lim sup pi(x+n) - pi(x), where pi = A000720. Equivalently, a(n) is the largest number of
primes that occurs on an infinite number of intervals of n consecutive integers.

Formalization notes:
* Admissibility (Wolfdieter Lang's comment, after Hensley and Richards): a tuple B of distinct
  nonnegative integers is admissible if, for each prime p, some congruence class modulo p contains
  no member of B.
* a(n), offset 1: the largest size of an admissible set B ⊆ {0, ..., n-1} with 0 ∈ B.
* pi(x+n) - pi(x) is the number of primes in the n consecutive integers x+1, ..., x+n. For an
  integer sequence, lim sup equal to k means: infinitely many x give a value at least k, and
  only finitely many give a value at least k+1. This is stated as `IsGreatest` of
  {k | pi(x+n) - pi(x) ≥ k for infinitely many x}.
* Controls: with primes p ≤ n checked (enough, since a set of at most n elements cannot cover
  all classes modulo a prime p > n), a(1..12) = 1, 1, 2, 2, 2, 2, 3, 3, 4, 4, 4, 4, as in the entry.
-/

namespace OMA.S_oeis_a023193

/-- A set of integers is admissible if it misses some residue class modulo every prime. -/
def Admissible (B : Finset ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ r : ℕ, ∀ b ∈ B, ¬ b ≡ r [MOD p]

/-- A023193(n): the largest size of an admissible set inside `{0, ..., n-1}` containing `0`. -/
noncomputable def a (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ B : Finset ℕ, B ⊆ Finset.range n ∧ 0 ∈ B ∧ B.card = k ∧ Admissible B}

/-- Dickson's conjecture: `a(n) = lim sup (π(x+n) - π(x))` for every `n ≥ 1`. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n →
      IsGreatest {k : ℕ | {x : ℕ | k ≤ Nat.primeCounting (x + n) - Nat.primeCounting x}.Infinite}
        (a n) := by
  sorry

end OMA.S_oeis_a023193
