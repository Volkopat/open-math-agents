import Mathlib

/-!
# A270488: n = x^2 + y(y+1) + z(z^2+1)

Source: https://oeis.org/A270488

A270488 (offset 0): `a(n)` is the number of ordered ways to write `n = x^2 + y*(y+1) + z*(z^2+1)`,
where `x`, `y` and `z` are nonnegative integers: 1, 1, 2, 2, 2, 1, 3, 1, 2, 2, 2, 3, …  For
example `a(35) = 1` since `35 = 5^2 + 0*1 + 2*(2^2+1)`.

Conjecture (Zhi-Wei Sun, Mar 17 2016): `a(n) > 0` for all `n = 0, 1, 2, …`, and `a(n) = 1` only
for `n = 0, 1, 5, 7, 19, 35, 54, 62, 63, 197, 285, 339, 479, 505, 917`. Moreover, any integer
`n > 2` can be written as `x^2 + y*(y+1) + z*(z^2+1)`, where `x` is a positive integer, and `y`
and `z` are nonnegative integers.

All three clauses are stated, as a conjunction. The second clause is given as an equivalence:
`a(n) = 1` if and only if `n` is one of the fifteen listed values. (That `a(n) = 1` at the listed
values is a finite computation; the open content is that there are no others.) The further
guesses listed afterwards in the entry (representations `x*(x+1)/2 + P(y,z)` for six other
polynomials `P`) are separate claims and are not part of this statement.

Conventions: `a n` is the cardinality (`Set.ncard`) of the finite set of triples `(x, y, z)` of
natural numbers with `x^2 + y*(y+1) + z*(z^2+1) = n`. Indexing is the OEIS one (offset 0).
Everything is in `ℕ`.
-/

namespace OMA.S_oeis_a270488

/-- A270488: the number of triples `(x, y, z)` of nonnegative integers with
`x^2 + y(y+1) + z(z^2+1) = n`. -/
noncomputable def a (n : ℕ) : ℕ :=
  {t : ℕ × ℕ × ℕ | t.1 ^ 2 + t.2.1 * (t.2.1 + 1) + t.2.2 * (t.2.2 ^ 2 + 1) = n}.ncard

theorem main :
    (∀ n : ℕ, 0 < a n) ∧
    (∀ n : ℕ, a n = 1 ↔
      n ∈ ({0, 1, 5, 7, 19, 35, 54, 62, 63, 197, 285, 339, 479, 505, 917} : Finset ℕ)) ∧
    (∀ n : ℕ, 2 < n →
      ∃ x y z : ℕ, 0 < x ∧ x ^ 2 + y * (y + 1) + z * (z ^ 2 + 1) = n) := by
  sorry

end OMA.S_oeis_a270488
