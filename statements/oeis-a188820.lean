import Mathlib

/-!
# A188820, 5-column binary arrays without diagonal 01

For adjacent rows u above v, every 1 in v forces a 1 in each existing
diagonally adjacent position of u. The left and right shifts form exactly
this set of required bits. Intersecting with the width mask discards bits
outside the array. An initial all-one boundary permits every first row.

The first two conclusions give Colin Barker's even and odd height formulas.
The last compares all coefficients after multiplying the stated generating
function by (1-z)^3 (1+z). The sequence begins at height one.

Source: https://oeis.org/A188820
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a188820

open Finset

def required (v : ℕ) := ((v <<< 1) &&& 31) ||| (v >>> 1)
def allowed (u : ℕ) : Finset ℕ :=
  (range 32).filter fun v => (u &&& required v) = required v

def continuations : ℕ → ℕ → ℤ
  | 0, _ => 1
  | n+1, u => ∑ v ∈ allowed u, continuations n v

def arrays (n : ℕ) : ℤ := if n=0 then 0 else continuations n 31
def delayed (j n : ℕ) : ℤ := if j ≤ n then arrays (n-j) else 0
def numerator (n : ℕ) : ℤ := if n=1 then 32 else if n=2 then 105 else if n=3 then 94 else if n=4 then 41 else if n=5 then -16 else 0

theorem main :
    (∀ n : ℕ, 0<n → Even n → arrays n = 9 + (-48*(n:ℤ)+64*(n:ℤ)^2)) ∧
    (∀ n : ℕ, 1<n → Odd n → arrays n = -48*(n:ℤ)+64*(n:ℤ)^2) ∧
    (∀ n : ℕ, arrays n-2*delayed 1 n+2*delayed 3 n-delayed 4 n = numerator n) := by
  sorry

end OMA.S_oeis_a188820
