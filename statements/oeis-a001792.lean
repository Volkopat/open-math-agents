import Mathlib

/-!
# OEIS A001792 and the binomial transform A098156

Creighton Dement's conjecture (March 14, 2005) in https://oeis.org/A001792.
The comparison sequence is defined by Paul Barry in https://oeis.org/A098156.
Source entries © OEIS Foundation Inc., CC BY-SA 4.0.
Credit: @connoranderson
-/

namespace OMA.S_oeis_a001792

/-- A001792 starts at index zero. Its positive terms are (n+2) times 2^(n-1). -/
def a : ℕ → ℕ
  | 0 => 1
  | k + 1 => (k + 3) * 2 ^ k

/-- At zero the preceding term is the stipulated extension a(-1) = 0. -/
def preceding : ℕ → ℕ
  | 0 => 0
  | k + 1 => a k

/-- Interleave 1,2,3,... and 1,3,5,..., starting with the former. -/
def interleaved (k : ℕ) : ℕ :=
  if k % 2 = 0 then k / 2 + 1 else k

/-- A098156 is the binomial transform of this interleaving. -/
def a098156 (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), n.choose k * interleaved k

theorem main : ∀ n : ℕ, preceding n + a098156 (n + 1) = 2 * a n := by
  sorry

end OMA.S_oeis_a001792
