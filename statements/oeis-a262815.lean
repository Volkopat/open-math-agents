import Mathlib

/-!
# A262815: n = x^3 + y(y+1)/2 + z(3z+1)/2

Source: https://oeis.org/A262815

A262815 (offset 0): `a(n)` is the number of ordered ways to write `n` as
`x^3 + y*(y+1)/2 + z*(3*z+1)/2`, where `x`, `y` and `z` are nonnegative integers:
1, 2, 2, 3, 2, 1, 2, 2, 4, 3, 3, 4, 1, …  For example `a(5) = 1` since
`5 = 0^3 + 2*3/2 + 1*(3*1+1)/2`.

Conjecture (Zhi-Wei Sun, Oct 03 2015): `a(n) > 0` for all `n ≥ 0`, and `a(n) = 1` only for
`n = 0, 5, 12, 19, 20, 75, 83, 97, 117`. The entry notes that the conjecture has been verified
up to `10^11` (Mauro Fiorentini, Jul 20 2023).

Both clauses are stated, as a conjunction. The second clause is given as an equivalence:
`a(n) = 1` if and only if `n` is one of the nine listed values. (That `a(n) = 1` at the nine
listed values is a finite computation, shown in the entry's examples; the open content is that
there are no others.)

Conventions:
- `a n` is the cardinality (`Set.ncard`) of the finite set of triples `(x, y, z)` of natural
  numbers with `x^3 + y*(y+1)/2 + z*(3*z+1)/2 = n`. Indexing is the OEIS one (offset 0).
- The divisions by 2 are natural-number divisions and are exact, because `y*(y+1)` and
  `z*(3*z+1)` are even.
-/

namespace OMA.S_oeis_a262815

/-- A262815: the number of triples `(x, y, z)` of nonnegative integers with
`x^3 + y(y+1)/2 + z(3z+1)/2 = n`. -/
noncomputable def a (n : ℕ) : ℕ :=
  {t : ℕ × ℕ × ℕ |
    t.1 ^ 3 + t.2.1 * (t.2.1 + 1) / 2 + t.2.2 * (3 * t.2.2 + 1) / 2 = n}.ncard

theorem main :
    (∀ n : ℕ, 0 < a n) ∧
    (∀ n : ℕ, a n = 1 ↔ n ∈ ({0, 5, 12, 19, 20, 75, 83, 97, 117} : Finset ℕ)) := by
  sorry

end OMA.S_oeis_a262815
