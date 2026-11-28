import Mathlib

/-!
# OEIS A269585
Source: https://oeis.org/A269585
Credit: @etaubman

R. H. Hardin counts five-letter words on 0 through n. Scan the word and
record the value of every adjacent equal pair. Two successive recorded
values must differ by at most one. We prove the empirical polynomial and
Colin Barker's conjectured generating function and recurrence.
-/

namespace OMA.S_oeis_a269585

def repeats {q : ℕ} (a b c d e : Fin q) : List ℕ :=
  (if b=a then [a.val] else []) ++ (if c=b then [b.val] else []) ++
  (if d=c then [c.val] else []) ++ (if e=d then [d.val] else [])

def allowed : List ℕ → Bool
  | x::y::t => decide (x ≤ y+1 ∧ y ≤ x+1) && allowed (y::t)
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
    (∀ n : ℕ, count n = (n:ℚ)^5 + 5*n^4 + 7*n^3 + 12*n^2 + 6*n + 1) ∧
    (∀ n : ℕ, terms (n+7) = 6*terms (n+6) - 15*terms (n+5) +
      20*terms (n+4) - 15*terms (n+3) + 6*terms (n+2) - terms (n+1)) ∧
    (1-X)^6 * mk terms = (X * (32 + 37*X + 70*X^2 - 20*X^3 + 2*X^4 - X^5) :
      PowerSeries ℚ) := by
  sorry

end OMA.S_oeis_a269585
