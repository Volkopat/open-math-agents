import Mathlib.Data.Nat.Digits.Lemmas

/-!
# OEIS A110735

The term is the least multiple of `n` obtained by inserting one decimal
digit in every gap and at both ends, or zero if no such multiple exists.
The conjecture that no term is zero is stated as the existence of a
corresponding multiple for every positive `n`.

Source: https://oeis.org/A110735
-/

namespace OMA.S_oeis_a110735

/-- Interleave the given digits and the inserted digits, least significant first. -/
def insertDigits : List ℕ → List ℕ → List ℕ
  | a :: digits, b :: gaps => b :: a :: insertDigits digits gaps
  | [], gaps => gaps
  | _ :: _, [] => []

theorem main : ∀ n : ℕ, 0 < n → ∃ gaps : List ℕ,
    gaps.length = (Nat.digits 10 n).length + 1 ∧
    (∀ d ∈ gaps, d < 10) ∧ 0 < gaps.getLastD 0 ∧
    n ∣ Nat.ofDigits 10 (insertDigits (Nat.digits 10 n) gaps) := by
  sorry

end OMA.S_oeis_a110735

