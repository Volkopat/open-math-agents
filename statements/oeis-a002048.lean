import Mathlib

/-!
# OEIS A002048: Andrews' conjecture on segmented numbers

Source: https://oeis.org/A002048
Segmented numbers (prime numbers of measurement): `1, 2, 4, 5, 8, 10, 14, …`, the positive
integers that are not a sum of two or more consecutive smaller segmented numbers.
Andrews conjectures `lim n log n / (a(n) log log n) = 1`.

Conventions. The set `S` of segmented numbers is characterised by: `m ∈ S` iff `m ≥ 1` and
there are no `x < y < m` in `S` with `m` equal to the sum of the elements of `S` in `[x, y]`
(a run of at least two consecutive elements). This determines `S` by strong induction, so
`main` quantifies over every `S` with the property. `a n` is the `n`-th element (`a 1 = 1`).

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a002048

open Filter Topology Real Classical

theorem main :
    ∀ S : Set ℕ,
      (∀ m : ℕ, m ∈ S ↔ 1 ≤ m ∧ ¬ ∃ x ∈ S, ∃ y ∈ S, x < y ∧ y < m ∧
          ∑ z ∈ (Finset.Icc x y).filter (· ∈ S), z = m) →
      Tendsto (fun n : ℕ => n * log n / ((Nat.nth (· ∈ S) (n - 1) : ℝ) * log (log n)))
        atTop (𝓝 1) := by
  sorry

end OMA.S_oeis_a002048
