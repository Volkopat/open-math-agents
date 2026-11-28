import Mathlib

/-!
# A081515: Sum of terms in n-th row of A081517.

Source: https://oeis.org/A081515
Credit: @gblacher2

Conjecture (comment in A081515): "a(n) is > the n-th triangular number. Conjecture: There are no
composite members."

A081517 (https://oeis.org/A081517): "Consider the smallest number m which can be expressed as the
sum of n distinct numbers coprime to m. Sequence gives triangle (read by rows) of the set of
coprime numbers pertaining to m." Row `n` (offset 1) consists of `n` distinct positive integers,
each coprime to `m`, whose sum is `m`; so the sum of row `n`, A081515(n), is that smallest `m`.
The numbers are positive, as in the data (row 1 is `1`, row 2 is `1, 2`, row 3 is `1, 2, 4`).

The set below is nonempty for every `n ≥ 1`: `m = 1` works for `n = 1`, and for `n ≥ 2` every
prime `p ≥ n * (n + 1) / 2` is `1 + 2 + ... + (n - 1) + (p - n * (n - 1) / 2)`, a sum of `n`
distinct positive integers below `p`. So `sInf` is the least such `m`.

A natural number is composite when it is greater than `1` and not prime. The conjecture says
that no term a(n), `n ≥ 1`, is composite.
-/

namespace OMA.S_oeis_a081515

/-- `m` is the sum of `n` distinct positive integers, each coprime to `m`. -/
def IsCoprimeSum (n m : ℕ) : Prop :=
  ∃ S : Finset ℕ, S.card = n ∧ (∀ x ∈ S, 0 < x ∧ Nat.Coprime x m) ∧ ∑ x ∈ S, x = m

/-- A081515(n): the smallest `m` that is the sum of `n` distinct positive integers coprime
to `m`, which is the sum of the `n`-th row of A081517. -/
noncomputable def a (n : ℕ) : ℕ := sInf {m : ℕ | IsCoprimeSum n m}

/-- The conjecture: A081515 has no composite members. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ¬ (1 < a n ∧ ¬ (a n).Prime) := by
  sorry

end OMA.S_oeis_a081515
