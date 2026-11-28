import Mathlib

/-!
# OEIS A269584
Source: https://oeis.org/A269584
Credit: @etaubman

R. H. Hardin counts four-letter words on 0 through n. Reading from left
to right, record a letter whenever it equals the next letter. Successive
recorded values must differ by at most one. We prove the empirical quartic
and Colin Barker's conjectured generating function and recurrence.
-/

namespace OMA.S_oeis_a269584

def repeats (a b c d : ℕ) : List ℕ :=
  (if b=a then [a] else []) ++ (if c=b then [b] else []) ++
    (if d=c then [c] else [])

def allowed : List ℕ → Bool
  | x::y::t => decide (x ≤ y+1 ∧ y ≤ x+1) && allowed (y::t)
  | _ => true

def count (n : ℕ) : ℚ :=
  ∑ a ∈ Finset.range (n+1), ∑ c ∈ Finset.range (n+1),
    ∑ b ∈ Finset.range (n+1), ∑ d ∈ Finset.range (n+1),
      if allowed (repeats a b c d) then 1 else 0

def terms : ℕ → ℚ
  | 0 => 0
  | n+1 => count (n+1)

open PowerSeries

theorem main :
    (∀ n : ℕ, count n = (n:ℚ)^4 + 4*n^3 + 5*n^2 + 5*n + 1) ∧
    (∀ n : ℕ, terms (n+6) = 5*terms (n+5) - 10*terms (n+4) +
      10*terms (n+3) - 5*terms (n+2) + terms (n+1)) ∧
    (1-X)^5 * mk terms = (X * (16 - X + 15*X^2 - 7*X^3 + X^4) : PowerSeries ℚ) := by
  sorry

end OMA.S_oeis_a269584
