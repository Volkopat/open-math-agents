import Mathlib

/-!
# A260878: Number of set partitions of {1, 2, ..., 2*n} with sizes in {[n, n], [2n]}

Source: https://oeis.org/A260878

`a(n)` is the number of set partitions of `{1, 2, ..., 2*n}` whose list of block sizes is `[n, n]`
or `[2n]`, offset 0; first terms 2, 2, 4, 11, 36, 127, 463, 1717, 6436, 24311, 92379. It is the
third column of the array A260876 (set partitions of `m`-shape). The term `a(0) = 2` is the
convention of A260876 for the empty set: there the number of set partitions of 0-shape is the number
of shapes, here the two shapes `[0, 0]` and `[0]`.

The entry (Peter Luschny, Aug 02 2019) puts `b(n) = binomial(2*(n-1), n-1) + 1 = A323230(n)` for
`n >= 0` (first terms 1, 2, 3, 7, 21, 71, 253), quotes from Salié (Math. Nachr. 14, 1955) that
`p` divides `a(p+k) - b(k+1)` if `p` is a prime `> k` and `0 <= k <= 4`, and then states:

  Conjecture: `p` divides `a(p+5) - b(6)` if `p` is a prime `> b(6)`.

This file states that conjecture; it is the only conjectural claim of the quoted text. The other
sentences of the quoted text (the recurrence, the exponential generating function, the asymptotic
estimates, the divisibility for `0 <= k <= 4` and the congruence `a(n) == a(n/p) (mod p)`, the
last two attributed to Salié) are presented by the entry as facts and are not part of the target.

Formalized:
* A set partition of `{1, ..., 2n}` is a `Finpartition` of `Finset.Icc 1 (2 * n)` in `ℕ`: a finite
  set `parts` of nonempty, pairwise disjoint finite sets with union `{1, ..., 2n}`.
* Its sizes are the multiset of the cardinalities of its blocks, `P.parts.val.map Finset.card`; the
  condition is that this multiset is `{n, n}` or `{2 * n}`.
* For `n = 0` the literal count is 0 (the only partition of the empty set has no block), so the
  conventional value `a(0) = 2` of the entry is written out. It plays no role in the claim, which
  only involves `a(p + 5)` with `p > 253`.
* `a` and `b` take values in `ℤ`, and `p divides a(p+5) - b(6)` is divisibility in `ℤ`.
* `b(0) = 1` (in the entry `binomial(-2, -1) = 0`) is written out, because natural-number
  subtraction would give `binomial(0, 0) + 1 = 2`. Only `b(6) = binomial(10, 5) + 1 = 253` is used.
* `p is a prime > b(6)` is `p.Prime` together with `b 6 < p`.
-/

namespace OMA.S_oeis_a260878

/-- A260878: the number of set partitions of `{1, ..., 2n}` whose multiset of block sizes is
`{n, n}` or `{2n}`; `a(0) = 2` by the convention of the entry. -/
def a (n : ℕ) : ℤ :=
  if n = 0 then 2
  else
    (((Finset.univ : Finset (Finpartition (Finset.Icc 1 (2 * n)))).filter fun P =>
      P.parts.val.map Finset.card = ({n, n} : Multiset ℕ) ∨
        P.parts.val.map Finset.card = ({2 * n} : Multiset ℕ)).card : ℤ)

/-- A323230: `b(n) = binomial(2*(n-1), n-1) + 1` for `n >= 1`, and `b(0) = 1`. -/
def b (n : ℕ) : ℤ :=
  if n = 0 then 1 else ((2 * (n - 1)).choose (n - 1) : ℤ) + 1

/-- Luschny's conjecture: `p` divides `a(p+5) - b(6)` if `p` is a prime `> b(6)`. -/
theorem main : ∀ p : ℕ, p.Prime → b 6 < (p : ℤ) → (p : ℤ) ∣ a (p + 5) - b 6 := by
  sorry

end OMA.S_oeis_a260878
