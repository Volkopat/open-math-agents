import Mathlib

/-!
# OEIS A090335: divisors of numbers with prescribed numbers of distinct prime factors

Source: https://oeis.org/A090335 (OEIS Foundation, CC BY-SA 4.0).
The positive integer has exactly n distinct prime factors. Its divisors greater
than one, in standard binary representation, must form a prefix code. A
positive integer b has prefix a precisely when deleting some number of its
rightmost binary digits gives a, that is, when b divided by 2^k equals a.
The conjecture that the sequence is defined for all n is stated as existence
of the least eligible integer for each prescribed count. For zero distinct
prime factors, the eligible integer is 1 and the code is empty.
Lean statement submitted by James Coholan, assisted by Codex.
-/

namespace OMA.S_oeis_a090335

def eligible (n m : ℕ) : Prop :=
  0 < m ∧ m.primeFactors.card = n ∧
    ∀ a : ℕ, a ∣ m → 1 < a → ∀ b : ℕ, b ∣ m → 1 < b →
      ∀ k : ℕ, b / 2 ^ k = a → a = b

theorem main : ∀ n : ℕ, ∃ m, IsLeast {x : ℕ | eligible n x} m := by
  sorry

end OMA.S_oeis_a090335
