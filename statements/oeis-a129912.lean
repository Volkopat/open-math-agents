import Mathlib

/-!
# OEIS A129912: products of distinct primorials and odd primes

Source: https://oeis.org/A129912
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

A129912 lists the products of distinct primorial numbers `1, 2, 6, 30, 210, …` (A002110).
Conjecture (McEachen, 2010): every odd prime `p` is either adjacent to a term of A129912 or at a
prime distance `q < p` from some term of A129912.

Conventions:
* The `i`-th primorial is `∏_{j < i} prime(j+1)` (`Nat.nth Nat.Prime j`), so primorial `0` is
  `1`. A term is `∏_{i ∈ s} primorial(i)` for a finite set `s`.
* 'Adjacent' means `|p - t| = 1`; 'prime distance `q < p`' means `|p - t| = q` with `q` prime.
-/

namespace OMA.S_oeis_a129912

/-- The `i`-th primorial. -/
noncomputable def primorial (i : ℕ) : ℕ := ∏ j ∈ Finset.range i, Nat.nth Nat.Prime j

/-- `t` is a product of distinct primorials. -/
def InA129912 (t : ℕ) : Prop := ∃ s : Finset ℕ, t = ∏ i ∈ s, primorial i

/-- McEachen's conjecture. -/
theorem main : ∀ p : ℕ, p.Prime → p ≠ 2 → ∃ t : ℕ, InA129912 t ∧
    (Int.natAbs ((p : ℤ) - t) = 1 ∨
      ∃ q : ℕ, q.Prime ∧ q < p ∧ Int.natAbs ((p : ℤ) - t) = q) := by
  sorry

end OMA.S_oeis_a129912
