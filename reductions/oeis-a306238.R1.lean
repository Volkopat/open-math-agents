import OMAStatements.S_oeis_a306238
import Mathlib

/-! In the range k ≤ 2n, proper factors of a composite k are small
enough to force an even quotient, apart from small indices where
minimality eliminates the exceptions. The large-candidate case remains open. -/
namespace OMA.R_oeis_a306238_R1
open OMA.S_oeis_a306238

def H1 : Prop := ∀ n k : ℕ, 1 < n → IsLeastOddQuotient n k → k ≤ 2 * n → k.Prime

def H2 : Prop := ∀ n k : ℕ, 1 < n → IsLeastOddQuotient n k → 2 * n < k → k.Prime

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a306238.main := by
  intro near far n k hn hk
  obtain h | h := le_or_gt k (2 * n)
  · exact near n k hn hk h
  · exact far n k hn hk h

end OMA.R_oeis_a306238_R1
