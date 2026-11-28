import Mathlib

/-!
# A090634: denominators of the iterated averages of 1, 1/2, ..., 1/n

Source: https://oeis.org/A090634
Credit: @jagong-cmu

Definition in the entry: start with the sequence [1, 1/2, 1/3, ..., 1/n]; form a new sequence
of n-1 terms by taking averages of successive terms; repeat until reach a single number F(n);
a(n) = denominator of F(n).

The entry gives (Michel Marcus, Sep 12 2019):
a(n) = denominator(2*(1-1/2^n)/n) (conjectured).

Known result: the 2003 Putnam problem B2 asks for this averaging process, and its published
solution proves the stronger identity F(n) = (2^n - 1)/(n * 2^(n-1)) = 2*(1-1/2^n)/n for the
rational value itself, before the denominator is taken. OEIS A090633 (the numerators) records
the same identity. So the conjecture follows from a known result; this file states it for
catalogue review as a known result.
References: K. Kedlaya, The Putnam Archive, 2003 solutions, B2,
https://kskedlaya.org/putnam-archive/2003s.pdf (page 5); https://oeis.org/A090633.

Conventions:
* Offset 1, as in the entry (data: 1, 4, 12, 32, 80, 64, 448, ...).
* `start n` is the list [1, 1/2, ..., 1/n] in `ℚ`. One averaging step `avg` maps
  [x_1, ..., x_m] to [(x_1+x_2)/2, ..., (x_(m-1)+x_m)/2], as in the Haskell program of the entry.
* After `n - 1` steps the list has exactly one element; `F n` is that element (`List.headD` with
  default `0` only matters for the empty list, which does not occur for `n >= 1`).
* `a n` is `Rat.den` of `F n`, the denominator in lowest terms, which is the OEIS convention.
* The conjecture is stated for every `n >= 1`, as in the entry.
-/

namespace OMA.S_oeis_a090634

/-- The list `[1, 1/2, 1/3, ..., 1/n]`. -/
def start (n : ℕ) : List ℚ := (List.range n).map (fun k : ℕ => 1 / ((k : ℚ) + 1))

/-- One step: the averages of successive terms. -/
def avg (l : List ℚ) : List ℚ := List.zipWith (fun x y => (x + y) / 2) l l.tail

/-- `F(n)`: the single number that remains after `n - 1` averaging steps. -/
def F (n : ℕ) : ℚ := ((avg^[n - 1]) (start n)).headD 0

/-- A090634: `a(n)` is the denominator of `F(n)`. -/
def a (n : ℕ) : ℕ := (F n).den

/-- For `n >= 1`: `a(n) = denominator(2*(1-1/2^n)/n)`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → a n = (2 * (1 - 1 / 2 ^ n) / (n : ℚ)).den := by
  sorry

end OMA.S_oeis_a090634
