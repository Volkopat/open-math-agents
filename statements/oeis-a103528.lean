import Mathlib.Data.Nat.Log
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Int.Cast.Basic

/-!
# A binary congruence sum as a difference of rounded sums

The index j in term stands for the source index k=j+1. The upper limit
in b is the integer part of log base two, A000523. Clearing the
denominator in the final equality expresses the source formula exactly.

Source: https://oeis.org/A103528
Credit: @KoaOkano
-/

namespace OMA.S_oeis_a103528

open Finset

def term (n : ℕ) : ℕ := ∑ j ∈ range (n-1),
  if n % (2^(j+1)) = (j+1) % (2^(j+1)) then 2^j else 0

def c (t k : ℕ) : ℕ := t - t % (2^k)

def b (n : ℕ) : ℕ := ∑ k ∈ range (Nat.log 2 n + 1), c (n-k) k

theorem main : term 1 = 0 ∧ ∀ n : ℕ, 1 < n →
    2*(term n : ℤ) = (b n : ℤ) - (b (n-1) : ℤ) - 1 := by
  sorry

end OMA.S_oeis_a103528
