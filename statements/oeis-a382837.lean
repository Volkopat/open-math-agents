import Mathlib

/-!
# Even gaps between terms of OEIS A382837

Source: https://oeis.org/A382837 (OEIS Foundation, CC BY-SA 4.0).

The entry asks whether, for every even natural number `n`, infinitely many
pairs `(k, k+n)` have both entries in A382837. A positive integer `m`
belongs to the sequence when `m - χ(m) > φ(m)`, where `χ` is Atanassov's
alternating sum of the positive divisors in descending order (A071324).
The subtraction is in the integers. The pair is identified by its first entry.
-/

namespace OMA.S_oeis_a382837

/-- Alternating sum of a list, with a positive first term. -/
def alternatingSum : List ℕ → ℤ
  | [] => 0
  | d :: rest => (d : ℤ) - alternatingSum rest

/-- Atanassov's alternating sum of divisors. -/
def chi (m : ℕ) : ℤ :=
  alternatingSum (m.divisors.sort (· ≥ ·))

/-- Membership in OEIS A382837. -/
def IsTerm (m : ℕ) : Prop :=
  0 < m ∧ (m.totient : ℤ) < (m : ℤ) - chi m

theorem main : ∀ n : ℕ, Even n → Set.Infinite {k : ℕ | IsTerm k ∧ IsTerm (k + n)} := by
  sorry

end OMA.S_oeis_a382837
