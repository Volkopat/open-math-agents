import Mathlib

/-!
# Seven-letter words with no adjacent opposite endpoints (OEIS A212840)

For the OEIS parameter n = m + 1, low encodes 0, high encodes n, and inside i
encodes i+1 for 0 ≤ i < m. Words are enumerated by choosing only allowed next
letters. The constant coefficient of the generating series is zero, matching
the offset one. The numerator is specified by its coefficients.

Source: https://oeis.org/A212840 (R. H. Hardin, 2012; Colin Barker, 2018).
-/

namespace OMA.S_oeis_a212840
open PowerSeries

inductive Letter where
  | low
  | high
  | inside (i : ℕ)
  deriving DecidableEq

def choices (m : ℕ) (previous : Option Letter) : List Letter :=
  let interior := (List.range m).map Letter.inside
  match previous with
  | some .low => .low :: interior
  | some .high => .high :: interior
  | _ => .low :: .high :: interior

def words (m : ℕ) : ℕ → Option Letter → List (List Letter)
  | 0, _ => [[]]
  | k+1, p => (choices m p).flatMap fun q => (words m k (some q)).map (q :: ·)

def a : ℕ → ℕ
  | 0 => 0
  | m+1 => (words m 7 none).length

/-- Coefficients of Barker's numerator, indexed from the constant term. -/
def numerator : ℕ → ℤ
  | 0 => 0
  | 1 => 2
  | 2 => 561
  | 3 => 3482
  | 4 => 1543
  | 5 => -682
  | 6 => 151
  | 7 => -18
  | 8 => 1
  | _+9 => 0

theorem main :
    (∀ m : ℕ, let n : ℤ := (m : ℤ) + 1
      (a (m+1) : ℤ) = n^7 + 7*n^6 + 9*n^5 - 15*n^4 - 13*n^3 + 15*n^2 - n - 1) ∧
    (∀ m : ℕ, (a (m+9) : ℤ) = 8*a (m+8) - 28*a (m+7) + 56*a (m+6) - 70*a (m+5)
      + 56*a (m+4) - 28*a (m+3) + 8*a (m+2) - a (m+1)) ∧
    (1-X)^8 * PowerSeries.mk (fun n => (a n : ℤ)) = PowerSeries.mk numerator := by
  sorry

end OMA.S_oeis_a212840
