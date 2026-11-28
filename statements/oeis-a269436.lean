import Mathlib

/-!
# A269436: decreasing consecutive repeats in four-letter words

Source: https://oeis.org/A269436
Credit: @etaubman

R. H. Hardin introduced the sequence. Colin Barker proposed the generating
function and the recurrence in January 2019. A repeat is recorded while
scanning each adjacent pair of equal letters. The accepted words have a
weakly decreasing sequence of recorded values. Both formulas are stated
with the OEIS offset of one.
-/

namespace OMA.S_oeis_a269436

abbrev Word (n : ℕ) := Fin (n+1) × Fin (n+1) × Fin (n+1) × Fin (n+1)

def repeats {n : ℕ} (w : Word n) : List (Fin (n+1)) :=
  (if w.1 = w.2.1 then [w.1] else []) ++
    (if w.2.1 = w.2.2.1 then [w.2.1] else []) ++
    (if w.2.2.1 = w.2.2.2 then [w.2.2.1] else [])

def count (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Word n)).filter (fun w => (repeats w).Pairwise (· ≥ ·))).card

def terms : ℕ → ℚ
  | 0 => 0
  | n+1 => (count (n+1) : ℚ)

open PowerSeries

theorem main :
    (∀ n : ℕ, terms (n+1) = ((n:ℚ)+2)^4 - ((n:ℚ)+2)*(n+1)/2) ∧
    (∀ n : ℕ, terms (n+6) = 5*terms (n+5) - 10*terms (n+4) +
      10*terms (n+3) - 5*terms (n+2) + terms (n+1)) ∧
    (1-X)^5 * mk terms = (X * (15 + 3*X + 10*X^2 - 5*X^3 + X^4) : PowerSeries ℚ) := by
  sorry

end OMA.S_oeis_a269436
