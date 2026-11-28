import Mathlib

/-!
# A268262 — words whose new repeated values appear in order

R. H. Hardin's A268262 counts length-four arrays over 0,…,n. Scan the
adjacent equal pairs from left to right. Each previously unseen repeated
value must be the next member of 0,1,2,… . Colin Barker conjectured the
generating function and recurrence in the OEIS entry.

Source: https://oeis.org/A268262
Credit: @etaubman
-/

namespace OMA.S_oeis_a268262

def repeats (a b c d : ℕ) : List ℕ :=
  (if a=b then [a] else []) ++ (if b=c then [b] else []) ++ (if c=d then [c] else [])

def sequential : ℕ → List ℕ → Bool
  | _, [] => true
  | k, x :: xs =>
    if x < k then sequential k xs else if x=k then sequential (k+1) xs else false

def count (n : ℕ) : ℚ :=
  ∑ b ∈ Finset.range (n+1), ∑ a ∈ Finset.range (n+1),
    ∑ c ∈ Finset.range (n+1), ∑ d ∈ Finset.range (n+1),
      if sequential 0 (repeats a b c d) then 1 else 0

def terms : ℕ → ℚ
  | 0 => 0
  | n+1 => count (n+1)

open PowerSeries

theorem main :
    (∀ n : ℕ, 0<n → count n = (n:ℚ)^4+n^3+3*n^2+2*n+2) ∧
    (∀ n : ℕ, terms (n+6) = 5*terms (n+5) - 10*terms (n+4) +
      10*terms (n+3) - 5*terms (n+2) + terms (n+1)) ∧
    (1-X)^5 * mk terms = (X * (9 - 3*X + 23*X^2 - 7*X^3 + 2*X^4) : PowerSeries ℚ) := by
  sorry

end OMA.S_oeis_a268262
