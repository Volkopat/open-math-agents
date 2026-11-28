import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.Lattice.Nat

/-!
# Conditional existence of the minimum in A178984

The original sequence starts at one-based prime index 3. Its nth value
is the least prime p for which prime(n)+1−p is also prime. Existence
under binary Goldbach is the claim in the source entry.

Source: https://oeis.org/A178984 (OEIS Foundation, CC BY-SA 4.0).
Credit: @Solitude1312
-/

namespace OMA.S_oeis_a178984

def binaryGoldbach : Prop :=
  ∀ t : ℕ, 2 < t → Even t → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = t

noncomputable def primeAt (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

def candidates (n : ℕ) : Set ℕ := {p | p.Prime ∧ (primeAt n + 1 - p).Prime}

noncomputable def a (n : ℕ) : ℕ := sInf (candidates n)

theorem main : binaryGoldbach → ∀ n : ℕ, 3 ≤ n → IsLeast (candidates n) (a n) := by
  sorry

end OMA.S_oeis_a178984
