import Mathlib

/-!
# The proposed binomial transform for A161869

Sources: https://oeis.org/A161869 and https://oeis.org/A024493.
In the k-th aerated Pascal matrix, row n is zero unless k divides n.
Otherwise its entries are the binomial coefficients of row n/k.
The first-column product can be evaluated recursively after the
first Pascal factor. From the second factor on, a nonzero entry in a
positive row uses a strictly smaller column index, and row zero
always stays row zero. Hence the recursion gives the converged entry.

The conjecture identifies the resulting sequence with the binomial
transform of A024493 with zeros inserted at odd indices.
-/

namespace OMA.S_oeis_a161869

def columnTail (k n : ℕ) : ℕ :=
  if _hn : n = 0 then 1
  else if _hk : 2 ≤ k then
    if n % k = 0 then
      ∑ j : Fin (n/k+1), (n/k).choose j.val * columnTail (k+1) j.val
    else 0
  else 0
termination_by n
decreasing_by
  have hdiv : n / k < n := Nat.div_lt_self (Nat.pos_of_ne_zero _hn) (by omega)
  exact lt_of_le_of_lt (Nat.le_of_lt_succ j.isLt) hdiv

def a (n : ℕ) : ℕ := ∑ j ∈ Finset.range (n+1), n.choose j * columnTail 2 j

def b (m : ℕ) : ℕ := ∑ i ∈ Finset.range (m/3+1), m.choose (3*i)

def transform (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (n/2+1), n.choose (2*i) * b i

theorem main : ∀ n : ℕ, a n = transform n := by
  sorry

end OMA.S_oeis_a161869
