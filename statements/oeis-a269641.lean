import Mathlib

/-!
# Four-letter words with prescribed successive repetitions (OEIS A269641)
Source: https://oeis.org/A269641
Credit: @etaubman

A repetition occurs when a letter equals its immediate predecessor. Among
four positions there are two or more repetitions precisely for a constant
triple or two constant pairs. A constant triple gives a forbidden step of
zero. For two separate pairs their second value must rise by two or fall by
one. We count words with at most one repetition and add the permitted pairs.
-/

namespace OMA.S_oeis_a269641

abbrev Alphabet (n : ℕ) := Fin (n+1)
abbrev Word (n : ℕ) := Alphabet n × Alphabet n × Alphabet n × Alphabet n

def two {n : ℕ} (w : Word n) : Prop :=
  let (a,b,c,d) := w
  (a=b ∧ b=c) ∨ (b=c ∧ c=d) ∨ (a=b ∧ c=d)

def allowedPair {n : ℕ} (w : Word n) : Prop :=
  let (a,b,c,d) := w
  a=b ∧ c=d ∧ (c.val = a.val + 2 ∨ a.val = c.val + 1)

noncomputable def count (n : ℕ) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Word n)).filter (fun w => ¬two w ∨ allowedPair w)).card

noncomputable def terms : ℕ → ℤ
  | 0 => 0
  | n+1 => (count (n+1) : ℤ)

open PowerSeries

theorem main :
    (∀ n : ℕ, terms (n+1) = ((n:ℤ)+1)^4 + 4*(n+1)^3 + 3*(n+1)^2 + 2*(n+1) - 1) ∧
    (∀ n : ℕ, terms (n+6) = 5*terms (n+5) - 10*terms (n+4) +
      10*terms (n+3) - 5*terms (n+2) + terms (n+1)) ∧
    (1-X)^5 * mk terms = (X * (3 - X) * (3 + 7*X + X^2 + X^3) : PowerSeries ℤ) := by
  sorry

end OMA.S_oeis_a269641
