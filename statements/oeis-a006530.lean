import Mathlib

/-!
# A006530: iterating the greatest prime factor of `a n + b`

Source: https://oeis.org/A006530
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (listed in A006530): let `a, b` be nonzero integers and let `f(n)` be the greatest
prime factor of `a n + b` if `a n + b ≠ 0`, and `f(n) = 0` if `a n + b = 0`, for every integer
`n`. Then the set `{n, f(n), f(f(n)), …}` is finite, of bounded size.

Conventions:
* The greatest prime factor of an integer `m ≠ 0` is that of `|m|`, with the sequence's
  convention `gpf(1) = 1`.
* "Of bounded size": for fixed `a, b`, one bound works for every starting `n`.
-/

namespace OMA.S_oeis_a006530

/-- Greatest prime factor of `|m|`, with `gpf(±1) = 1` and `0 ↦ 0`. -/
def gpf (m : ℤ) : ℤ :=
  if m = 0 then 0 else if m.natAbs = 1 then 1 else ((m.natAbs.primeFactors.sup id : ℕ) : ℤ)

/-- The map `f` for given `a, b`. -/
def f (a b : ℤ) (n : ℤ) : ℤ := gpf (a * n + b)

theorem main :
    ∀ a b : ℤ, a ≠ 0 → b ≠ 0 → ∃ B : ℕ, ∀ n : ℤ,
      (Set.range (fun k : ℕ => (f a b)^[k] n)).Finite ∧
        (Set.range (fun k : ℕ => (f a b)^[k] n)).ncard ≤ B := by
  sorry

end OMA.S_oeis_a006530
