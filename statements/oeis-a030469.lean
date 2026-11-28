import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Finite.Defs

/-!
# Prime concatenations of three consecutive primes

Source: https://oeis.org/A030469
Credit: @inakiabt
-/

namespace OMA.S_oeis_a030469

/-- Write the primes at indices `k`, `k + 1`, and `k + 2` side by side in decimal.
`Nat.digits` lists the units first, so the rightmost prime supplies the first block. -/
noncomputable def concatenation (k : ℕ) : ℕ :=
  let p := Nat.nth Nat.Prime
  Nat.ofDigits 10 (Nat.digits 10 (p (k + 2)) ++ Nat.digits 10 (p (k + 1)) ++ Nat.digits 10 (p k))

/-- Infinitely many distinct concatenations of three consecutive primes are prime. -/
theorem main : {n : ℕ | n.Prime ∧ ∃ k : ℕ, n = concatenation k}.Infinite := by
  sorry

end OMA.S_oeis_a030469
