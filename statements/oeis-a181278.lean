import Mathlib

/-!
# A181278: two binary rows with an ordered Gram matrix

Read each matrix from left to right. While the two rows are equal their three
Gram entries modulo two are the same bit. The column (1,0) as the first
unequal pair makes increasing row order impossible. The first column (0,1)
settles the row order, after which all four columns are allowed. A column
(u,v) toggles the two diagonal entries by u and v, and their cross entry by uv.
Compare the resulting two Gram rows lexicographically in decreasing order.

Colin Barker's generating function is expressed coefficient by coefficient
after multiplication by (1−2x)(1+2x)(1−4x). The second conjunct has the
published range n > 3.

Source: https://oeis.org/A181278
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a181278

def afterFirst : ℕ → Bool → Bool → Bool → ℤ
  | 0, a, b, c => if 2*a.toNat + b.toNat > 2*b.toNat + c.toNat then 1 else 0
  | n+1, a, b, c =>
    afterFirst n a b c + afterFirst n a b (!c) + afterFirst n (!a) b c +
      afterFirst n (!a) (!b) (!c)

def beforeFirst : ℕ → Bool → ℤ
  | 0, _ => 0
  | n+1, p => beforeFirst n p + afterFirst n p p (!p) + beforeFirst n (!p)

def sequence (n : ℕ) : ℤ := beforeFirst n false

def lag (d n : ℕ) : ℤ := if d ≤ n then sequence (n-d) else 0

def numerator (n : ℕ) : ℤ := if n = 2 then 3 else if n = 3 then -1 else if n = 4 then -8 else 0

theorem main :
    (∀ n : ℕ, lag 0 n - 4*lag 1 n - 4*lag 2 n + 16*lag 3 n = numerator n) ∧
    (∀ k : ℕ, sequence (k+4) = 4*sequence (k+3) +
      4*sequence (k+2) - 16*sequence (k+1)) := by
  sorry

end OMA.S_oeis_a181278
