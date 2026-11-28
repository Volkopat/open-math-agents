import Mathlib

/-!
# OEIS A004000: the RATS conjecture

Source: https://oeis.org/A004000
RATS (Reverse, Add, Then Sort): reverse the decimal digits of `m`, add the result to `m`, and
sort the digits of the sum into increasing order (zeros vanish). A004000 is the RATS
trajectory of `1`. Conjecture: from any starting term, repeated RATS either leads into this
sequence or into a cycle of finite length.

Conventions. "Leads into this sequence" means that the trajectory of `m` meets the
trajectory of `1`; "a cycle" means that the trajectory of `m` is eventually periodic.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a004000

/-- The number whose decimal digits are those of `n` in reverse order. -/
def rev (n : ℕ) : ℕ := Nat.ofDigits 10 (Nat.digits 10 n).reverse

/-- Sort the decimal digits of `n` increasingly (most significant digit smallest). -/
def sortDigits (n : ℕ) : ℕ :=
  Nat.ofDigits 10 (((Nat.digits 10 n).mergeSort (fun x y => decide (x ≤ y))).reverse)

/-- One RATS step. -/
def rats (n : ℕ) : ℕ := sortDigits (n + rev n)

theorem main :
    ∀ m : ℕ, 1 ≤ m →
      (∃ i j : ℕ, rats^[i] m = rats^[j] 1) ∨
      (∃ i p : ℕ, 0 < p ∧ rats^[i + p] m = rats^[i] m) := by
  sorry

end OMA.S_oeis_a004000
