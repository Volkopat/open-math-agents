import Mathlib

/-!
# A217835: Fermat pseudoprimes to base 2 that can be written as p^2*n - p*n + p, where p is also a Fermat pseudoprime to base 2 and n is a positive integer

Source: https://oeis.org/A217835
Credit: @jrflga (agent: Claude Code, model claude-fable-5-2)

OEIS comments (two conjectures):

* Conjecture: For any Fermat pseudoprime p to base 2 there are infinitely many Fermat
  pseudoprimes to base 2 equal to p^2*n - p*n + p, where n is a positive integer.
* Conjecture: For any Fermat pseudoprime p to base 2 and any positive integer k, there are
  infinitely many Fermat pseudoprimes to base 2 equal to p^2*n - p*n + p^k, where n is a
  positive integer.

The entry begins `348161, 831405, 1246785, ...`; for instance `348161 = 341^2*3 - 341*3 + 341`.
Fermat pseudoprimes to base 2 are A001567: `341, 561, 645, 1105, ...`.

## Encoding

* `Nat.FermatPsp m 2` is Mathlib's Fermat pseudoprime to base 2: `m` divides `2^(m-1) - 1`,
  `m` is not prime and `1 < m`.
* `IsOfForm p k m` says that `m = p^2*n - p*n + p^k` for some positive integer `n`. It is
  written without subtraction, as `m + p * n = p ^ 2 * n + p ^ k`; the two forms agree because
  `p * n ≤ p ^ 2 * n`.
* `main` is the conjunction of the two conjectures. The first one is the case `k = 1` of the
  second one, and is kept as the entry states it.
-/

namespace OMA.S_oeis_a217835

/-- `m = p^2*n - p*n + p^k` for some positive integer `n`. -/
def IsOfForm (p k m : ℕ) : Prop :=
  ∃ n : ℕ, 0 < n ∧ m + p * n = p ^ 2 * n + p ^ k

theorem main :
    (∀ p : ℕ, Nat.FermatPsp p 2 →
      {m : ℕ | Nat.FermatPsp m 2 ∧ IsOfForm p 1 m}.Infinite) ∧
    (∀ p : ℕ, Nat.FermatPsp p 2 → ∀ k : ℕ, 0 < k →
      {m : ℕ | Nat.FermatPsp m 2 ∧ IsOfForm p k m}.Infinite) := by
  sorry

end OMA.S_oeis_a217835
