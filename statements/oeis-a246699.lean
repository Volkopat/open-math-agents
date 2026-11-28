import Mathlib

/-!
# A246699: Squarefree n such that binomial(2^n - 1, n) is also squarefree

Source: https://oeis.org/A246699

Conjecture (OEIS A246699):
There are only finitely many squarefree positive integers `n` such that the binomial
coefficient `C(2^n - 1, n)` is also squarefree.

Conventions:
- Offset: `1`; first terms: `1, 2, 3, 6, 11, 21, 29, ...`.
- In Mathlib, `Squarefree 0` is false, so `Squarefree n` automatically enforces `1 ≤ n`.
-/

namespace OMA.S_oeis_a246699

/-- The set of squarefree `n` such that `binomial(2^n - 1, n)` is squarefree (OEIS A246699). -/
def S : Set ℕ :=
  {n : ℕ | Squarefree n ∧ Squarefree (Nat.choose (2 ^ n - 1) n)}

/-- Conjecture: the set of terms of OEIS A246699 is finite. -/
theorem main : Set.Finite S := by
  sorry

end OMA.S_oeis_a246699
