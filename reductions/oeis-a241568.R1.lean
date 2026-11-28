import OMAStatements.S_oeis_a241568
import Mathlib

/-! The Fibonacci numbers 2, 3, 5, and 13 supply a nonresidue outside
24 reduced residue classes modulo 1560. The supplementary law at two
and quadratic reciprocity at the three odd primes determine the sieve.
The size restrictions on a Fibonacci witness are included, even for
the small primes. Existence on the surviving classes remains open. -/

namespace OMA.R_oeis_a241568_R1

def H1 : Prop := ∀ p : ℕ, p.Prime → 3 < p →
    ¬ ((p % 24 = 1 ∨ p % 24 = 23) ∧ (p % 5 = 1 ∨ p % 5 = 4) ∧
      p % 13 ∈ ([1, 3, 4, 9, 10, 12] : List ℕ)) →
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ (p - 1) / 2 ∧ (∃ m : ℕ, Nat.fib m = k) ∧ ¬ IsSquare (k : ZMod p)

def H2 : Prop := ∀ p : ℕ, p.Prime → 3 < p →
    (p % 24 = 1 ∨ p % 24 = 23) → (p % 5 = 1 ∨ p % 5 = 4) →
    p % 13 ∈ ([1, 3, 4, 9, 10, 12] : List ℕ) →
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ (p - 1) / 2 ∧ (∃ m : ℕ, Nat.fib m = k) ∧ ¬ IsSquare (k : ZMod p)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a241568.main := by
  intro h1 h2 p hp hgt
  by_cases h : (p % 24 = 1 ∨ p % 24 = 23) ∧ (p % 5 = 1 ∨ p % 5 = 4) ∧
      p % 13 ∈ ([1, 3, 4, 9, 10, 12] : List ℕ)
  · exact h2 p hp hgt h.1 h.2.1 h.2.2
  · exact h1 p hp hgt h

end OMA.R_oeis_a241568_R1
