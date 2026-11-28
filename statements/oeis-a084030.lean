import Mathlib

/-!
# OEIS A084030: main diagonal of triangle A084029

Row n of triangle A084029 lists the first n positive n-digit multiples
of n with decimal digit sum n, padded with zeros when fewer than n
exist (row 2 is [20, 0]). The main diagonal is A084030:
1, 0, 120, 2020, 10400, 100140, 1001203, ...
The OEIS comment conjectures: Only one term is zero.
The diagonal term a(n) is a genuine nonzero entry iff row n needs no
zero-padding at position n, i.e. iff at least n eligible numbers
exist; hence a(n) = 0 iff the eligible set has fewer than n elements.

Source: https://oeis.org/A084030
-/

namespace OMA.S_oeis_a084030

/-- Eligible entries of row n of A084029: the n-digit multiples of n
    with decimal digit sum n. Every n-digit number is below 10^n, so
    this Finset captures the whole row content. -/
def witnesses (n : ℕ) : Finset ℕ :=
  (Finset.range (10 ^ n)).filter fun N =>
    n ∣ N ∧ (Nat.digits 10 N).length = n ∧ (Nat.digits 10 N).sum = n

/-- OEIS conjecture: only one term of the diagonal A084030 is zero.
    Under the zero-padding semantics of A084029, a(n) = 0 iff
    (witnesses n).card < n; the unique zero sits at index 2. -/
theorem main : ∀ n : ℕ, 0 < n → ((witnesses n).card < n ↔ n = 2) := by
  sorry

end OMA.S_oeis_a084030
