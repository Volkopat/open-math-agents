import Mathlib

/-!
# Four-letter words with restrictions on repetitions (OEIS A269495)
Source: https://oeis.org/A269495 and https://oeis.org/A269494
Credit: @etaubman

In a length-four word, two distinct repeated runs can only have lengths
two and two. The excluded words are therefore (j,j,j+1,j+1) and
(j+1,j+1,j,j). We count the complement of this family inside all four-tuples.
The sequence starts at index one; its ordinary generating series has zero
constant coefficient. The rational series equality is stated after clearing
the denominator, whose constant coefficient is one.
-/

namespace OMA.S_oeis_a269495

abbrev Word (n : ℕ) := Fin (n+1) × Fin (n+1) × Fin (n+1) × Fin (n+1)

def prohibited (n : ℕ) (p : Bool × Fin n) : Word n :=
  if p.1 then (p.2.succ, p.2.succ, p.2.castSucc, p.2.castSucc)
  else (p.2.castSucc, p.2.castSucc, p.2.succ, p.2.succ)

def count (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Word n)) \ Finset.univ.image (prohibited n)).card

def terms : ℕ → ℤ
  | 0 => 0
  | n+1 => (count (n+1) : ℤ)

open PowerSeries

theorem main :
    (∀ n : ℕ, terms (n+1) = ((n:ℤ)+2)^4 - 2*(n+1)) ∧
    (∀ n : ℕ, terms (n+6) = 5*terms (n+5) - 10*terms (n+4) +
      10*terms (n+3) - 5*terms (n+2) + terms (n+1)) ∧
    (1-X)^5 * mk terms = (X * (14 + 7*X + 5*X^2 - 3*X^3 + X^4) : PowerSeries ℤ) := by
  sorry

end OMA.S_oeis_a269495
