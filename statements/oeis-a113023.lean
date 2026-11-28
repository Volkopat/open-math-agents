import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Finset.Nat

/-!
# Counting decimal suffixes of powers of two

An n-digit integer belongs to A095810 precisely when it occurs as the last
n digits of some power of two. Taking a longer suffix and suppressing its
leading zeros gives the same n-digit residue. Count each integer once.

Mohammed Yaseen proposed the formula in 2022.
Sources: https://oeis.org/A113023 and https://oeis.org/A095810
Credit: @KoaOkano
-/

namespace OMA.S_oeis_a113023

def occurs (n m : ℕ) : Prop := ∃ j : ℕ, 2 ^ j % 10 ^ n = m

noncomputable def terms (n : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ico (10 ^ (n - 1)) (10 ^ n)).filter (occurs n)

theorem main : ∀ n : ℕ, 1 < n → (terms n).card = 18 * 5 ^ (n - 2) := by
  sorry

end OMA.S_oeis_a113023
