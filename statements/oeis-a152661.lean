import Mathlib.Data.Nat.Factorial.Basic

/-!
# Two formulas for permutations with first entries of the same parity

R. J. Mathar conjectured a recurrence for A152661 and an identity with
A077613. There are `e = floor(n/2)` even and `o = ceil(n/2)` odd labels in
`{1,...,n}`. The first two entries can be filled in `e(e-1) + o(o-1)`
ordered ways, and the other labels in `(n-2)!` ways. For A077613, treating
a distinguished adjacent even-odd pair as a single block gives `e*o` choices
of labels and `(n-1)!` arrangements. These counts define both sequences
independently. The recurrence uses `n=t+4` and the second identity `n=t+2`,
so every term is in its source domain.

Sources: https://oeis.org/A152661 and https://oeis.org/A077613
Credit: @KoaOkano
-/

namespace OMA.S_oeis_a152661

def sameParity (n : ℕ) : ℤ :=
  let e : ℤ := (n / 2 : ℕ)
  let o : ℤ := ((n + 1) / 2 : ℕ)
  (e * (e - 1) + o * (o - 1)) * (n - 2).factorial

def evenOddPairs (n : ℕ) : ℤ :=
  ((n / 2 : ℕ) : ℤ) * (((n + 1) / 2 : ℕ) : ℤ) * (n - 1).factorial

theorem main :
    (∀ t : ℕ, (-((t : ℤ) + 1)) * sameParity (t + 4) +
      2 * ((t : ℤ) + 2) * sameParity (t + 3) +
      ((t : ℤ) + 3) * ((t : ℤ) + 2) * ((t : ℤ) + 1) * sameParity (t + 2) = 0) ∧
    (∀ t : ℕ, sameParity (t + 2) = 2 * evenOddPairs (t + 1)) := by
  sorry

end OMA.S_oeis_a152661
