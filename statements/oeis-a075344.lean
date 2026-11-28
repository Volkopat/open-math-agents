import Mathlib

/-!
# A075344: Number of primes strictly between consecutive terms of A075343

Source: https://oeis.org/A075344
Author: Amarnath Murthy (2002)

Conjecture (OEIS A075344):
Let `b` be the sequence OEIS A075343 defined by `b(1) = 1` and `b(n + 1)` equal to
the smallest integer greater than `b(n)` such that there are exactly `n` composite
numbers strictly between `b(n)` and `b(n + 1)`. Then for every `n ≥ 1`, there is at
least one prime number strictly between `b(n)` and `b(n + 1)`.

Conventions:
- OEIS offset is `1`; here we index `b` from `0` (`b 0 = 1`, `b 1 = 5`, `b 2 = 9`,
  `b 3 = 15`, `b 4 = 22`, `b 5 = 29`, `b 6 = 37`, ...), so `b (n + 1)` is the smallest
  integer `> b n` with `n + 1` composite integers strictly between `b n` and `b (n + 1)`.
- First terms of A075344: `2, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 5, 2, 3, ...`.
-/

namespace OMA.S_oeis_a075344

/-- Predicate stating that `m` is a composite integer (`m > 1` and not prime). -/
def IsComposite (m : ℕ) : Prop :=
  1 < m ∧ ¬ Nat.Prime m

/-- Number of composite integers strictly between `u` and `v`. -/
noncomputable def compositeCountBetween (u v : ℕ) : ℕ :=
  Set.ncard {m : ℕ | u < m ∧ m < v ∧ IsComposite m}

/-- Conjecture: there is always at least one prime strictly between consecutive terms
of OEIS A075343. -/
theorem main :
    ∀ b : ℕ → ℕ,
      b 0 = 1 →
      (∀ n : ℕ, IsLeast {v : ℕ | b n < v ∧ compositeCountBetween (b n) v = n + 1} (b (n + 1))) →
      ∀ n : ℕ, ∃ p : ℕ, b n < p ∧ p < b (n + 1) ∧ Nat.Prime p := by
  sorry

end OMA.S_oeis_a075344
