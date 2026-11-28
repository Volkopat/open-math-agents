import Mathlib

/-!
# A002981 — for n > 2, n! + 1 and (n + 1)! + 1 are not both prime

Source: https://oeis.org/A002981
Credit: @Andyi955

The conjecture recorded in the OEIS entry A002981 (Mohammed Bouayoun, Mar 03 2004) is: for
`n > 2`, if `n! + 1` is prime then `(n + 1)! + 1` is not prime. Equivalently, no two consecutive
factorial-plus-one numbers with index `n > 2` are both prime.

## Encoding

* Factorality is Mathlib's `Nat.factorial`; the factorial notation is not usable here, so the
  statement writes `Nat.factorial n` explicitly.
* `Nat.Prime` is Mathlib's prime predicate, and the claim is the implication stating that
  `(n + 1)! + 1` fails to be prime whenever `n! + 1` is prime, for every `n > 2`.
-/

namespace OMA.S_oeis_a002981

/-- **Bouayoun's conjecture (OEIS A002981)**: for `n > 2`, `n! + 1` prime forces `(n + 1)! + 1`
composite. -/
theorem main :
    ∀ n : ℕ, 2 < n → (Nat.factorial n + 1).Prime →
      ¬ (Nat.factorial (n + 1) + 1).Prime := by
  sorry

end OMA.S_oeis_a002981
