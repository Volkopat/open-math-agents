import Mathlib

/-!
# A160845, distinct straight lines through a five-row grid

Use all pairs of different grid points, ordered lexicographically to fix the
direction sign. Divide the coordinate differences by their gcd. For the
resulting primitive direction (u,v), the integer u*y−v*x is constant on
the line. Thus the two primitive components and this intercept identify an
entire straight line. Repeated descriptions of the same line are counted once.

The generating function is stated after multiplying by its denominator.
The empty grid at index zero contributes no lines.

Source: https://oeis.org/A160845
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a160845

abbrev Point := ℕ × ℕ
abbrev Line := ℤ × ℤ × ℤ

def grid (n : ℕ) : Finset Point := (Finset.range n).product (Finset.range 5)

def line (p q : Point) : Line :=
  let dx := (q.1 : ℤ) - p.1
  let dy := (q.2 : ℤ) - p.2
  let g : ℤ := Nat.gcd dx.natAbs dy.natAbs
  let u := dx / g
  let v := dy / g
  (u,v,u*(p.2 : ℤ)-v*(p.1 : ℤ))

def lines (n : ℕ) : Finset Line :=
  (((grid n).product (grid n)).filter fun pq =>
    pq.1.1 < pq.2.1 ∨ (pq.1.1 = pq.2.1 ∧ pq.1.2 < pq.2.2)).image fun pq => line pq.1 pq.2

def sequence (n : ℕ) : ℤ := ((lines n).card : ℤ)

def lag (d n : ℕ) : ℤ := if d ≤ n then sequence (n-d) else 0
def numerator (n : ℕ) : ℤ := if n = 1 then 1 else if n = 2 then 26 else if n = 3 then 25 else if n = 4 then 40 else if n = 5 then 20 else if n = 6 then 16 else if n = 7 then 1 else if n = 9 then 5 else 0

theorem main :
    (∀ n : ℕ, lag 0 n - lag 1 n - lag 3 n + lag 5 n + lag 7 n - lag 8 n = numerator n) ∧
    (∀ k : ℕ, sequence (k+8) = sequence (k+7) + sequence (k+5) - sequence (k+3) - sequence (k+1) + sequence (k+0)) := by
  sorry

end OMA.S_oeis_a160845
