import Mathlib

/-!
# A068890: Smallest nontrivial n-th power whose digits alternate in parity

Source: https://oeis.org/A068890

Conjecture (OEIS A068890):
Only finitely many exponents `n ≥ 1` admit a nontrivial `n`-th power `m ^ n`
(`m ≥ 2`) whose base-10 digits alternate in parity.

Conventions:
- Offset: `1`; `a(1) = 1`, `a(2) = 4`, `a(3) = 8`, `a(4) = 16`, `a(5) = 32`,
  `a(6) = 729`, ...
- Adjacent digits in `Nat.digits 10 x` alternate in parity iff no two consecutive
  entries have the same remainder modulo `2`.
-/

namespace OMA.S_oeis_a068890

/-- Predicate stating that consecutive base-10 digits of `x` alternate in parity. -/
def DigitsAlternateParity (x : ℕ) : Prop :=
  ∀ l₁ l₂ : List ℕ, ∀ a b : ℕ,
    Nat.digits 10 x = l₁ ++ [a, b] ++ l₂ → a % 2 ≠ b % 2

/-- The set of exponents `n ≥ 1` for which there exists a nontrivial `n`-th power
(`m ≥ 2`) whose base-10 digits alternate in parity. -/
def S : Set ℕ :=
  {n : ℕ | 1 ≤ n ∧ ∃ m : ℕ, 2 ≤ m ∧ DigitsAlternateParity (m ^ n)}

/-- Conjecture: the sequence A068890 is finite (only finitely many `n` have such a power). -/
theorem main : Set.Finite S := by
  sorry

end OMA.S_oeis_a068890
