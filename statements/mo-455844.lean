import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Log

namespace OMA.S_mo_455844

/-- The blue code of a natural number, defined by the two binary recurrences. -/
def blue : ℕ → ℕ :=
  Nat.binaryRec (motive := fun _ => ℕ) 0 (fun bit _ x => x ^^^ (2 * x + bit.toNat))

/-- The largest power of two at most n, for positive n. -/
def leadingPower (n : ℕ) : ℕ := 2 ^ n.log2

/-- The auxiliary function in the proposed recurrences. -/
def g (n : ℕ) : ℕ :=
  let f := leadingPower n
  2 * (blue (f - 1) ^^^ (n / 2)) + 1 - n % 2 + f

/-- Both proposed recurrences for the blue code.
Source: https://mathoverflow.net/questions/455844 -/
theorem main : ∀ n : ℕ, 1 < n →
    (blue n = blue (g n - leadingPower n) + leadingPower n ∧
      blue n = g (blue (n - leadingPower n) + leadingPower n)) := by
  sorry

end OMA.S_mo_455844
