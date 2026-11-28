import Mathlib

/-!
# OEIS A111489: Primes of the form prime(k) + composite(k) for some k.

Source: https://oeis.org/A111489
Credit: @unserus

OEIS: "Conjecture: This sequence is infinite."
`prime(k)` and `composite(k)` are both 1-indexed in OEIS (`prime(1) = 2`, `composite(1) = 4`);
here both use the same 0-based index of `Nat.nth`, which pairs them identically
(index 2: `5 + 8 = 13`, the first term).
-/

namespace OMA.S_oeis_a111489

/-- `n` is composite: greater than `1` and not prime. -/
def IsComposite (n : ℕ) : Prop := 1 < n ∧ ¬ n.Prime

/-- The terms of A111489: primes of the form `prime(k) + composite(k)`. -/
def a111489Set : Set ℕ :=
  {q : ℕ | q.Prime ∧ ∃ k : ℕ, q = Nat.nth Nat.Prime k + Nat.nth IsComposite k}

/-- A111489 is infinite. -/
theorem main : a111489Set.Infinite := by
  sorry

end OMA.S_oeis_a111489
