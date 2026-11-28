import Mathlib

/-!
# A207118, binary three-column arrays

A row is encoded by its three bits, with the leftmost bit most significant.
The two prohibited horizontal rows are 001 and 010. A forbidden vertical
triple has first bit 0 and last bit 1, irrespective of its middle bit.
Consequently a row must be a bitwise subset of the row two places earlier.
This independently counts the odd-position and even-position rows as two
chains of admissible rows. Their initial upper bound 111 allows any first row.

The conclusions are Colin Barker's even and odd polynomials and his rational
generating function. The latter is written coefficient by coefficient after
multiplication by (1-z)^7 (1+z)^5. Height zero has generating coefficient zero.

Source: https://oeis.org/A207118
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a207118

def legal : List ℕ := (List.range 8).filter fun c => c != 1 && c != 2
def options (c : ℕ) : List ℕ := legal.filter fun b => (b &&& c) == b

def chains : ℕ → ℕ → ℤ
  | 0, _ => 1
  | n+1, c => ((options c).map fun b => chains n b).sum

def arrays (n : ℕ) : ℤ :=
  if n=0 then 0 else chains ((n+1)/2) 7 * chains (n/2) 7

def evenPoly (x : ℤ) : ℤ := x^6+24*x^5+208*x^4+816*x^3+1600*x^2+1536*x+576
def oddPoly (x : ℤ) : ℤ := x^6+24*x^5+205*x^4+768*x^3+1315*x^2+936*x+207
def delayed (d n : ℕ) : ℤ := if d ≤ n then arrays (n-d) else 0
def numerator (n : ℕ) : ℤ := if n=1 then 6 else if n=2 then 24 else if n=3 then 6 else if n=4 then 1 else if n=5 then 16 else if n=6 then -4 else if n=7 then -20 else if n=8 then 6 else if n=9 then 10 else if n=10 then -4 else if n=11 then -2 else if n=12 then 1 else 0

def denTimesSeries (n : ℕ) : ℤ := delayed 0 n - 2*delayed 1 n - 4*delayed 2 n + 10*delayed 3 n + 5*delayed 4 n - 20*delayed 5 n + 20*delayed 7 n - 5*delayed 8 n - 10*delayed 9 n + 4*delayed 10 n + 2*delayed 11 n - delayed 12 n

theorem main : (∀ k : ℕ, 0 < k → 576*arrays (2*k) = evenPoly (2*k)) ∧
    (∀ k : ℕ, 576*arrays (2*k+1) = oddPoly (2*k+1)) ∧
    (∀ n : ℕ, denTimesSeries n = numerator n) := by
  sorry

end OMA.S_oeis_a207118
