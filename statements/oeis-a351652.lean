import Mathlib

/-!
# OEIS A351652: greedy sequence with disjoint square-root continued-fraction periods

Source: https://oeis.org/A351652.
The offset-1 sequence starts with 1 and each subsequent term is the least positive
unused integer whose periodic coefficients are disjoint from those of the previous term.
Giorgos Kalogeropoulos conjectured that it permutes the positive integers. Rémy Sigrist
proved the conjecture in the comments of the OEIS entry.

A coefficient occurs in the period exactly when it occurs arbitrarily far in the
continued fraction, since nonsquare positive square roots have eventually periodic
regular continued fractions. For squares the stream ends after the integer part.
-/

namespace OMA.S_oeis_a351652

/-- The values in the periodic part of the continued fraction of `sqrt m`.
For a nonsquare these are precisely the partial quotients that occur arbitrarily far
in its eventually periodic regular continued fraction. A square has no tail entries. -/
def periodicCoeffs (m : ℕ) : Set ℤ :=
  {b | ∀ i : ℕ, ∃ j ≥ i, ∃ p, (GenContFract.of (Real.sqrt (m : ℝ))).s.get? j = some p ∧ p.b = b}

/-- The next term must be positive, unused, and compatible with the current term. -/
def eligible (last : ℕ) (seen : Finset ℕ) (m : ℕ) : Prop :=
  0 < m ∧ m ∉ seen ∧ Disjoint (periodicCoeffs last) (periodicCoeffs m)

open Classical in
/-- Zero-based iteration of the greedy choice, storing the last term and all used terms. -/
noncomputable def state : ℕ → ℕ × Finset ℕ
  | 0 => (1, {1})
  | n + 1 =>
    let old := state n
    if h : ∃ m, eligible old.1 old.2 m then
      let m := Nat.find h
      (m, insert m old.2)
    else old

/-- `a n` is the term of index `n + 1` in A351652. -/
noncomputable def a (n : ℕ) : ℕ := (state n).1

/-- Every positive integer appears exactly once. -/
theorem main : Function.Injective a ∧ ∀ m : ℕ, 0 < m ↔ ∃ n, a n = m := by
  sorry

end OMA.S_oeis_a351652
