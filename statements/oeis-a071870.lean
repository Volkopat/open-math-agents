import Mathlib

/-!
# A071870: strictly decreasing greatest prime factors twice in a row

Source: https://oeis.org/A071870
Source data: https://raw.githubusercontent.com/oeis/oeisdata/main/seq/A071/A071870.seq
Credit: @Bondyboy2001

The sequence consists of positive integers `k` such that
`gpf(k) > gpf(k+1) > gpf(k+2)`, where `gpf` is the greatest prime factor. Erdős conjectured
that this sequence is infinite.
-/

namespace OMA.S_oeis_a071870

/-- The greatest prime factor of `m`, with value `0` when `m` has no prime factor. -/
def gpf (m : ℕ) : ℕ := m.primeFactors.sup id

/-- Membership in A071870. -/
def IsTerm (k : ℕ) : Prop :=
  0 < k ∧ gpf k > gpf (k + 1) ∧ gpf (k + 1) > gpf (k + 2)

theorem main : {k : ℕ | IsTerm k}.Infinite := by
  sorry

end OMA.S_oeis_a071870
