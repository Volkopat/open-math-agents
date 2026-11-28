import Mathlib

/-!
# A125792: Column 2 of table A125790; also equals row sums of matrix power A078121^2.

Source: https://oeis.org/A125792
Credit: @agchua

Benedict W. J. Irwin, Nov 16 2016, in the formula section of A125792:
  Conjecture: a(n+1) = Sum_{i_1=1..3} Sum_{i_2=1..2*i_1-1} ... Sum_{i_n=1..2*i_(n-1)-1} (2*i_n - 1).
  For example: a(2) = Sum_{i=1..3} 2*i-1. a(3) = Sum_{i=1..3} Sum_{j=1..2*i-1} 2*j-1.
Offset of A125792: 0 (data 1, 3, 9, 35, 201, 1827, 27337, ...).

The table. A125790 (offset 0) is a rectangular table T(n,k), n, k >= 0; its formula line reads:
T(n,k) = T(n,k-1) + T(n-1,2*k) for n>0, k>0, with T(0,n)=T(n,0)=1 for n>=0. The definition below
is this recurrence (the listed terms of A125790 and of A125792 agree with it), and
a(n) = A125792(n) = T(n,2), column 2 of the table.

The nested sum. N(0,x) = x and N(m+1,x) = Sum_{i=1..x} N(m,2*i-1), so that N(n,3) is the n-fold
nested sum Sum_{i_1=1..3} Sum_{i_2=1..2*i_1-1} ... Sum_{i_n=1..2*i_(n-1)-1} (2*i_n - 1)
(for n = 1 it is Sum_{i=1..3} (2*i-1), as in the example). The conjecture has n >= 1 sums, so it
is stated for n >= 1.
-/

namespace OMA.S_oeis_a125792

/-- The table A125790: T(n,k) = T(n,k-1) + T(n-1,2k) for n, k > 0, T(0,k) = T(n,0) = 1. -/
def T : ℕ → ℕ → ℕ
  | 0, _ => 1
  | _ + 1, 0 => 1
  | n + 1, k + 1 => T (n + 1) k + T n (2 * (k + 1))

/-- A125792(n) = T(n,2), column 2 of A125790. -/
def a (n : ℕ) : ℕ := T n 2

/-- The nested sums: N(0,x) = x, N(m+1,x) = Sum_{i=1..x} N(m,2i-1). -/
def N : ℕ → ℕ → ℕ
  | 0, x => x
  | m + 1, x => ∑ i ∈ Finset.Icc 1 x, N m (2 * i - 1)

/-- Irwin's conjecture: a(n+1) is the n-fold nested sum, for every n >= 1. -/
theorem main : ∀ n : ℕ, 1 ≤ n → a (n + 1) = N n 3 := by
  sorry

end OMA.S_oeis_a125792
