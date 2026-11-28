import Mathlib

/-!
# Five-letter words with unequal successive repeated values (OEIS A269469)
Source: https://oeis.org/A269469 and https://oeis.org/A269467
Credit: @etaubman

A repetition is a letter equal to its immediate predecessor. In five positions,
successive repetitions of the same letter require either a constant triple or
two constant pairs with that same letter at both ends of the word. We count
all five-tuples satisfying neither condition. The generating function starts
at index one and its denominator has constant coefficient one.
-/

namespace OMA.S_oeis_a269469

abbrev Alphabet (n : ℕ) := Fin (n+1)
abbrev Word (n : ℕ) := Alphabet n × Alphabet n × Alphabet n × Alphabet n × Alphabet n

def bad {n : ℕ} (w : Word n) : Prop :=
  let (a,b,c,d,e) := w
  (a = b ∧ b = c) ∨ (b = c ∧ c = d) ∨ (c = d ∧ d = e) ∨ (a = b ∧ a = d ∧ d = e)

noncomputable def count (n : ℕ) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Word n)).filter (fun w => ¬bad w)).card

noncomputable def terms : ℕ → ℤ
  | 0 => 0
  | n+1 => (count (n+1) : ℤ)

open PowerSeries

theorem main :
    (∀ n : ℕ, terms (n+1) = ((n:ℤ)+1)^5 + 5*(n+1)^4 + 7*(n+1)^3 +
       2*(n+1)^2 - (n+1)) ∧
    (∀ n : ℕ, terms (n+7) = 6*terms (n+6) - 15*terms (n+5) +
      20*terms (n+4) - 15*terms (n+3) + 6*terms (n+2) - terms (n+1)) ∧
    (1-X)^6 * mk terms = (2*X * (7 + 45*X + 9*X^2 - X^3) : PowerSeries ℤ) := by
  sorry

end OMA.S_oeis_a269469
