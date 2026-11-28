import Mathlib

/-!
# A270361: Odd primes p for which there exists an odd prime q < p such that p*q - 1 is a square

Source: https://oeis.org/A270361
Credit: @xor2k

Formalizes the OEIS A270361 conjecture: For any odd prime p there is at most one odd prime q,
with q < p, for which p*q-1 is square.

Conventions:
* At most one is expressed as `Set.Subsingleton` of the set of such `q`.
* Is square means `IsSquare` on `ℕ` (a perfect square, `0` included). Since `p * q ≥ 1`, the
  natural subtraction `p * q - 1` is the true integer value.
* The other comments of the entry are descriptive (density remarks, membership in A002144) and are
  not formalized; this is the only comment labelled as a conjecture.
-/

namespace OMA.S_oeis_a270361

/-- For every odd prime `p`, at most one odd prime `q < p` makes `p * q - 1` a square. -/
theorem main :
    ∀ p : ℕ, p.Prime → Odd p →
      {q : ℕ | q.Prime ∧ Odd q ∧ q < p ∧ IsSquare (p * q - 1)}.Subsingleton := by
  sorry

end OMA.S_oeis_a270361
