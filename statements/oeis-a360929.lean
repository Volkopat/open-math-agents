import Mathlib

/-!
# A360929: odd numbers not of the form `p + q * (q + 1)`

Source: https://oeis.org/A360929
Source data: https://raw.githubusercontent.com/oeis/oeisdata/main/seq/A360/A360929.seq
Credit: @Bondyboy2001

Here `p` and `q` are prime numbers. The source notes that the parity of `q * (q + 1)` forces
`p` to be odd in every representation of an odd number; this is a consequence, not an extra
hypothesis.
-/

namespace OMA.S_oeis_a360929

/-- `n` has the prime representation excluded in the definition of A360929. -/
def Representable (n : ℕ) : Prop :=
  ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p + q * (q + 1)

/-- The conjecture that `1446377` is the largest odd number with no such representation. -/
theorem main : IsGreatest {n : ℕ | Odd n ∧ ¬ Representable n} 1446377 := by
  sorry

end OMA.S_oeis_a360929
