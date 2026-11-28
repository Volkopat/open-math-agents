import Mathlib

/-!
# OEIS A269621
Source: https://oeis.org/A269621
Credit: @etaubman

R. H. Hardin counts five-letter words on 0 through n. Scan the word and
record the value of every adjacent equal pair. Two successive recorded
values may stay equal, rise by two, or fall by one. We prove the empirical polynomial and
Colin Barker's conjectured generating function and recurrence.
-/

namespace OMA.S_oeis_a269621

def repeats {q : ℕ} (a b c d e : Fin q) : List ℕ :=
  (if b=a then [a.val] else []) ++ (if c=b then [b.val] else []) ++
  (if d=c then [c.val] else []) ++ (if e=d then [d.val] else [])

def allowed : List ℕ → Bool
  | x::y::t => decide (y=x ∨ y=x+2 ∨ x=y+1) && allowed (y::t)
  | _ => true

def count (n : ℕ) : ℚ :=
  ∑ a : Fin (n+1), ∑ b : Fin (n+1), ∑ c : Fin (n+1),
    ∑ d : Fin (n+1), ∑ e : Fin (n+1),
      if allowed (repeats a b c d e) then 1 else 0

def terms : ℕ → ℚ
  | 0 => 0
  | n+1 => count (n+1)

open PowerSeries

theorem main :
    (∀ n : ℕ, count (n+1) = ((n:ℚ)+1)^5 + 5*((n:ℚ)+1)^4 + 7*((n:ℚ)+1)^3 +
      12*((n:ℚ)+1)^2 + 3*((n:ℚ)+1)) ∧
    (∀ n : ℕ, terms (n+7) = 6*terms (n+6) - 15*terms (n+5) +
      20*terms (n+4) - 15*terms (n+3) + 6*terms (n+2) - terms (n+1)) ∧
    (1-X)^6 * mk terms = (2*X * (14 + 27*X + 21*X^2 + X^3 - 3*X^4) :
      PowerSeries ℚ) := by
  sorry

end OMA.S_oeis_a269621
