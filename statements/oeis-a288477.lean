import Mathlib

/-!
# A288477: the least even m with every m + 2^k ± 1 composite

Source: https://oeis.org/A288477 (OEIS Foundation, CC BY-SA 4.0)
Credit: @trador01 (agent: Claude Code, model claude-opus-5-5)

A288477 (offset 0): a(n) = (2^49 - 2)*n/3 + 247371098957; for all n, a(n) and a(n) + 2 form a
pair of consecutive Sierpiński numbers.

The entry records:

  Conjecture: a(0) + 1 = 247371098958 is the smallest nonnegative even number m such that for
  all k >= 1 the numbers m + 2^k + 1 and m + 2^k - 1 are composite.

Reading of the source:
* "composite" means greater than 1 and not prime.
* m ranges over the nonnegative even integers (naturals), k over the integers k ≥ 1; for such k,
  `m + 2^k - 1 ≥ 1`, so natural subtraction is exact.
* "the smallest ... such that" is `IsLeast`: 247371098958 has the property, and no smaller
  nonnegative even number does.
-/

namespace OMA.S_oeis_a288477

/-- `x` is composite: greater than 1 and not prime. -/
def Composite (x : ℕ) : Prop := 1 < x ∧ ¬ x.Prime

/-- `m` is even and `m + 2^k + 1`, `m + 2^k - 1` are composite for every `k ≥ 1`. -/
def Good (m : ℕ) : Prop :=
  Even m ∧ ∀ k : ℕ, 1 ≤ k → Composite (m + 2 ^ k + 1) ∧ Composite (m + 2 ^ k - 1)

/-- 247371098958 is the smallest nonnegative even number with the property. -/
theorem main : IsLeast {m : ℕ | Good m} 247371098958 := by
  sorry

end OMA.S_oeis_a288477
