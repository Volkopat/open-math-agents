import Mathlib

/-!
# A356078: Highly composite numbers that are multiples of their number of divisors.

Source: https://oeis.org/A356078
Credit: @luciusacarr

Data: 1, 2, 12, 24, 36, 60, 180, 240, 360, 720, 1260, 1680, 5040, ...

Conjecture (from the entry): this sequence is finite. `main` states it.

Reading of the source:
* A highly composite number (A002182) is a positive integer `n` with more divisors than every
  positive integer `m < n`: `d(m) < d(n)` for all `0 < m < n`, where `d(m)` is the number of
  divisors `(Nat.divisors m).card`.
* "Multiple of its number of divisors" means `d(n) ∣ n`.
* With this reading the terms below 2 * 10^6 are exactly the listed ones up to 1441440 (checked
  numerically).
-/

namespace OMA.S_oeis_a356078

/-- `n` is highly composite (A002182). -/
def IsHighlyComposite (n : ℕ) : Prop :=
  0 < n ∧ ∀ m : ℕ, 0 < m → m < n → (Nat.divisors m).card < (Nat.divisors n).card

/-- The terms of A356078. -/
def S : Set ℕ := {n | IsHighlyComposite n ∧ (Nat.divisors n).card ∣ n}

theorem main :
    -- The sequence is finite.
    S.Finite := by
  sorry

end OMA.S_oeis_a356078
