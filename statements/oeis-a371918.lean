import Mathlib

/-!
# Greedy exponents of powers of two containing prescribed decimal substrings

Source: https://oeis.org/A371918, Scott R. Shannon (2024). The input starts at
zero, the admissible exponents start at one, and zero is a one-digit word.
-/
namespace OMA.S_oeis_a371918

/-- The canonical decimal expansion of `x` contains that of `n` at some
position counted from the units. The first inequality excludes padding
with fictitious zeros to the left (and the host 0 is written "0"). -/
def contains (x n : ℕ) : Prop :=
  (x = 0 ∧ n = 0) ∨ ∃ j : ℕ, 10^j ≤ x ∧ x / 10^j % 10^(Nat.log 10 n + 1) = n

def eligible (a : ℕ → ℕ) (n k : ℕ) : Prop :=
  0 < k ∧ contains (2^k) n ∧ ∀ i < n, a i ≠ k

def greedy (a : ℕ → ℕ) : Prop :=
  ∀ n, eligible a n (a n) ∧ ∀ k, eligible a n k → a n ≤ k

theorem main : (∃ a, greedy a) ∧
    ∀ a, greedy a → Function.Injective a ∧ Set.range a = {k : ℕ | 0 < k} := by
  sorry

end OMA.S_oeis_a371918
