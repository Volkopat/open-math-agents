import Mathlib

/-!
# A131194: Coalescence of greedy prime sequences with shared decimal digits

Source: https://oeis.org/A131194

An admissible seed is a prime with at least three decimal digits. The listed
sequence starts at 101. The conjecture says that every admissible seed's
sequence meets the sequence from 101, possibly at a different index.
-/

namespace OMA.S_oeis_a131194

/-- Count the intersection of the two decimal digit multisets. -/
def commonDigitCount (p q : ℕ) : ℕ :=
  ∑ d ∈ Finset.range 10, min ((Nat.digits 10 p).count d) ((Nat.digits 10 q).count d)

/-- The least larger prime that shares at least three decimal digits with `p`. -/
noncomputable def nextPrime (p : ℕ) : ℕ :=
  sInf {q : ℕ | p < q ∧ q.Prime ∧ 3 ≤ commonDigitCount p q}

noncomputable def term (seed : ℕ) : ℕ → ℕ
  | 0 => seed
  | n + 1 => nextPrime (term seed n)

theorem main :
    ∀ seed : ℕ, seed.Prime → 100 ≤ seed →
      ∃ i j : ℕ, (term seed i).Prime ∧ term seed i = term 101 j := by
  sorry

end OMA.S_oeis_a131194
