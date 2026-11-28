import Mathlib

/-!
# A216442: Numbers of the form 2^i + 3^j + 5^k, where i, j, k >= 0.

Source: https://oeis.org/A216442
Credit: @agchua

Comment of A216442 (unsigned; the entry is by Robert G. Wilson v, Sep 20 2012), verbatim:
  Conjecture: Unlike A004050, which has a limited set of integers expressible in more than one
  way, this set has no such limit.
A004050 lists the numbers of the form 2^j + 3^k; only finitely many of them have more than one
such representation (for example 5 = 2^2 + 3^0 = 2^1 + 3^1 and 11 = 2^3 + 3^1 = 2^1 + 3^2).

Formalisation. An integer n is expressible in more than one way when there are two different
triples (i, j, k) and (i', j', k') of exponents >= 0 with 2^i + 3^j + 5^k = n and
2^i' + 3^j' + 5^k' = n. That this set has no limit means that it is infinite. The comparison
with A004050 is a remark that motivates the conjecture; the conjectured claim is about A216442.
-/

namespace OMA.S_oeis_a216442

/-- Infinitely many integers are expressible in more than one way as 2^i + 3^j + 5^k. -/
theorem main :
    Set.Infinite {n : ℕ | ∃ i j k i' j' k' : ℕ, (i, j, k) ≠ (i', j', k') ∧
      2 ^ i + 3 ^ j + 5 ^ k = n ∧ 2 ^ i' + 3 ^ j' + 5 ^ k' = n} := by
  sorry

end OMA.S_oeis_a216442
