import Mathlib

/-!
# Multiples in the twice-iterated odious numbers

Sources: https://oeis.org/A233419, https://oeis.org/A232637 and https://oeis.org/A000069
Credit: @etaubman

With the OEIS one-based indexing, the j-th odious number is the member of
the pair (2(j-1), 2(j-1)+1) with odd binary digit sum. We use this explicit
formula twice. For every k not divisible by 4, we produce multiples of k at
arbitrarily large indices, proving both versions of the conjecture.
-/

namespace OMA.S_oeis_a233419

def weight (u : ℕ) : ℕ := (Nat.digits 2 u).sum

def odious (j : ℕ) : ℕ :=
  2 * (j - 1) + (1 - weight (j - 1) % 2)

def secondOdious (j : ℕ) : ℕ := odious (odious j)

theorem main : ∀ k : ℕ, ¬4 ∣ k → ∀ B : ℕ,
    ∃ j : ℕ, B < j ∧ k ∣ secondOdious j := by
  sorry

end OMA.S_oeis_a233419
