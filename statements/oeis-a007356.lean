import Mathlib

/-!
# OEIS A007356: apocalyptic powers, 2^a(n) contains 666

Source: https://oeis.org/A007356 (OEIS Foundation, CC BY-SA 4.0)
Credit: @sntntHb

A007356 lists, in increasing order and with offset 1, the exponents `k` such that the decimal
expansion of `2^k` contains the block 666: 157, 192, 218, 220, 222, ... The entry states:

  Conjecture: for n > 26069, a(n) = n + 3715. [Charles R Greathouse IV, Sep 28 2011]

`Nat.digits 10` lists digits from least significant to most significant; the block 666 is a
palindrome, so it occurs in the decimal expansion iff `[6, 6, 6]` is an infix of that list.
With `Nat.nth` (0-indexed), `a n = Nat.nth P (n - 1)`. A direct computation confirms
`a(1) = 157` and `a(n) = n + 3715` for `26070 ≤ n ≤ 36284`, and that `26069` is the last failure.
-/

namespace OMA.S_oeis_a007356

/-- `2^k` contains the block 666 in base 10. -/
def P (k : ℕ) : Prop := [6, 6, 6] <:+: Nat.digits 10 (2 ^ k)

/-- The `n`-th apocalyptic exponent (offset 1). -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth P (n - 1)

/-- Conjecture of A007356 (Greathouse): `a(n) = n + 3715` for every `n > 26069`. -/
theorem main : ∀ n : ℕ, 26069 < n → a n = n + 3715 := by
  sorry

end OMA.S_oeis_a007356
