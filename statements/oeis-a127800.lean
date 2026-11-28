import Mathlib.Data.Nat.Basic

/-!
# Inverse row sums of Barry's triangle (OEIS A127800)

Sources: https://oeis.org/A127800 and https://oeis.org/A069517.
Formalization by @DomTheDeveloper.

Let r be the zero-based row sums of the inverse, so A r is the all-ones
vector. In row n, the nonzero columns run from (n+1)/2 through n. The
common entry is 1 in row zero and 1/2 thereafter. Clearing the denominator
gives exactly the interval sum below. The system determines r uniquely,
row by row, because its last term always has coefficient one.
A069517 is indexed from one and equals 2 at positive powers of 2, 1 at 1,
and 0 elsewhere.
-/

namespace OMA.S_oeis_a127800

/-- Sum of r(0), ..., r(t-1). -/
def prefixSum (r : ℕ → Rat) : ℕ → Rat
  | 0 => 0
  | t + 1 => prefixSum r t + r t

/-- The inverse row sums satisfy the row equations A r = 1. -/
def rowEquations (r : ℕ → Rat) : Prop :=
  ∀ n : ℕ, prefixSum r (n + 1) - prefixSum r ((n + 1) / 2) =
    if n = 0 then 1 else 2

theorem main : ∀ r : ℕ → Rat, rowEquations r →
    r 0 = 1 ∧ ∀ n : ℕ, 0 < n →
      ((∃ k : ℕ, n + 1 = 2 ^ k) → r n = 2) ∧
      ((¬ ∃ k : ℕ, n + 1 = 2 ^ k) → r n = 0) := by
  sorry

end OMA.S_oeis_a127800
