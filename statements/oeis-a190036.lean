import Mathlib

/-!
# A190036, nondecreasing sums of recent entries

Generate the arrangements one entry at a time. The reversed prefix stores
the latest values first. Each new value lies in 0..4 and is at least the
last, and from the third entry onward it is one of the sums allowed by
the original rule. Distinct ways of writing a value give one choice.

The generating function is stated after multiplying by its denominator.
Index zero has coefficient zero because the OEIS sequence starts at one.

Source: https://oeis.org/A190036
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a190036

def fits (x : ℕ) : List ℕ → Bool
  | [] | [_] => true
  | [a,b] => decide (x=a ∨ x=b ∨ x=a+b)
  | a::b::c::_ => decide (x=a ∨ x=b ∨ x=c ∨ x=a+b ∨ x=a+c ∨ x=b+c)

def extend : ℕ → List ℕ → ℤ
  | 0, row => if row.head? = some 4 then 1 else 0
  | m+1, row => (Finset.range 5).sum fun x =>
    if row.headD 0 ≤ x ∧ fits x row = true then extend m (x :: row) else 0

def sequence (n : ℕ) : ℤ := if n = 0 then 0 else extend (n+2) []

def lag (d n : ℕ) : ℤ := if d ≤ n then sequence (n-d) else 0
def numerator (n : ℕ) : ℤ := if n = 1 then 7 else if n = 2 then -9 else if n = 3 then 3 else if n = 4 then 2 else if n = 6 then -1 else 0

theorem main :
    (∀ n : ℕ, lag 0 n - 3*lag 1 n + 3*lag 2 n - lag 3 n = numerator n) ∧
    (∀ k : ℕ, sequence (k+5) = 3*sequence (k+4) - 3*sequence (k+3) + sequence (k+2)) := by
  sorry

end OMA.S_oeis_a190036
