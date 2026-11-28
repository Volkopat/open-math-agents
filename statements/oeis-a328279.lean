import Mathlib

/-!
# Least members of decimal digit-sum cycles

Read the decimal digits from left to right. Each pair of adjacent digits
contributes its sum to a concatenation. Sums between 10 and 18 contribute
two digits, and a zero sum contributes one zero. With no pair the
concatenation is zero. A329623 takes the absolute difference from the input.

A328279 lists the least positive member of each cycle in increasing order,
including the one-element cycles. Its offset is one. Barker's generating
function is stated coefficientwise after multiplication by its denominator
(1-x)(1+x^4)(1-10x^4).

Sources: https://oeis.org/A328279 and https://oeis.org/A329623
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a328279

def step (n : ℕ) : ℕ :=
  let ds := (Nat.digits 10 n).reverse
  let sums := List.zipWith (· + ·) ds ds.tail
  let combined := sums.foldl (fun acc v => acc * (if v < 10 then 10 else 100) + v) 0
  Nat.dist n combined

def cycleMinimum (v : ℕ) : Prop :=
  0 < v ∧ ∃ r : ℕ, 0 < r ∧ step^[r] v = v ∧ ∀ i < r, v ≤ step^[i] v

noncomputable def a (n : ℕ) : ℤ := Int.ofNat (Nat.nth cycleMinimum (n-1))

noncomputable def lag (n d : ℕ) : ℤ := if d < n then a (n-d) else 0

def numerator (n : ℕ) : ℤ :=
  ([0, 1, 1, 1, 1, -8, -8, -8, -8, -18, 154, 72, 72, 72, -294, 80, 80, 80, -460] :
    List ℤ).getD n 0

theorem main :
    (∀ n : ℕ, lag n 0 - lag n 1 - 9*lag n 4 + 9*lag n 5 - 10*lag n 8 +
      10*lag n 9 = numerator n) ∧
    (∀ n : ℕ, 17 < n → a n = a (n-1) + 9*a (n-4) - 9*a (n-5) +
      10*a (n-8) - 10*a (n-9)) := by
  sorry

end OMA.S_oeis_a328279
