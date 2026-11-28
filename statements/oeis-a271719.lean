import Mathlib

/-!
# A271719: n = x + y + z with gcd(x,y,z) = 1 and x^2 + (2y+z)^2 a square

Source: https://oeis.org/A271719

A271719 (offset 1): `a(n)` is the number of ordered ways to write `n` as `x + y + z` with
`x ≥ y > 0`, `z > 0` and `gcd(x,y,z) = 1` such that `x^2 + (2*y+z)^2` is a square:
0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 1, 1, 3, 1, 2, 4, …  For example `a(11) = 1` since
`11 = 6 + 3 + 2` with `6 > 3`, `gcd(6,3,2) = 1` and `6^2 + (2*3+2)^2 = 10^2`.

Conjecture (Zhi-Wei Sun, Apr 12 2016): `a(n) > 0` for all `n > 10`, and `a(n) = 1` only for
`n = 11, 12, 14, 18, 24, 54`.

Both clauses are stated, as a conjunction. The second clause is given as an equivalence:
`a(n) = 1` if and only if `n` is one of the six listed values. (That `a(n) = 1` at the six
listed values is a finite computation, shown in the entry's examples; the open content is that
there are no others.)

Conventions:
- `a n` is the cardinality (`Set.ncard`) of the finite set of triples `(x, y, z)` of natural
  numbers with `x + y + z = n`, `0 < y ≤ x`, `0 < z`, `gcd(x, y, z) = 1` and
  `x^2 + (2*y+z)^2` a perfect square. Indexing is the OEIS one (offset 1).
- `gcd(x, y, z)` is `Nat.gcd (Nat.gcd x y) z`.
-/

namespace OMA.S_oeis_a271719

/-- A271719: the number of triples `(x, y, z)` with `x + y + z = n`, `x ≥ y > 0`, `z > 0`,
`gcd(x,y,z) = 1` and `x^2 + (2y+z)^2` a square. -/
noncomputable def a (n : ℕ) : ℕ :=
  {t : ℕ × ℕ × ℕ | t.1 + t.2.1 + t.2.2 = n ∧ 0 < t.2.1 ∧ t.2.1 ≤ t.1 ∧ 0 < t.2.2 ∧
    Nat.gcd (Nat.gcd t.1 t.2.1) t.2.2 = 1 ∧
    IsSquare (t.1 ^ 2 + (2 * t.2.1 + t.2.2) ^ 2)}.ncard

theorem main :
    (∀ n : ℕ, 10 < n → 0 < a n) ∧
    (∀ n : ℕ, a n = 1 ↔ n ∈ ({11, 12, 14, 18, 24, 54} : Finset ℕ)) := by
  sorry

end OMA.S_oeis_a271719
