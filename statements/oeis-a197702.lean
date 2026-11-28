import Mathlib

/-!
# A197702: Smallest positive integer k such that n = +-1 +-3 +-... +-(2k-1) for some choice of +'s and -'s.

Source: https://oeis.org/A197702
Credit: @agchua

Comment of A197702 (the entry is by John W. Layman, Oct 18 2011):
  Conjecture. Let SO(k) be the sum of the first k odd positive integers.  Then a(n)=k if
  n=SO(k).  Otherwise, choose k so that SO(k-1)<n<SO(k).  Then if SO(k)-n=4, a(n)=k+2, else if
  SO(k)-n is odd then a(n)=k+1 else a(n)=k.  (This has been verified for n up to 200.)
The offset is 1, so n >= 1: the first part is stated for k >= 1 (then SO(k) >= 1), and in the
second part SO(k-1) < n already forces n >= 1 and k >= 1. A choice of signs is a function e from
the naturals to the integers with values 1 or -1 (only e(0), ..., e(k-1) matter), and the signed
sum is Sum_{i<k} e(i)*(2i+1). In the second part SO(k)-n is a difference of naturals with
n < SO(k).
-/

namespace OMA.S_oeis_a197702

/-- SO(k) = 1 + 3 + ... + (2k-1), the sum of the first k odd positive integers. -/
def SO (k : ℕ) : ℕ := ∑ i ∈ Finset.range k, (2 * i + 1)

/-- Rep n k: n = +-1 +-3 +- ... +-(2k-1) for some choice of signs. -/
def Rep (n : ℤ) (k : ℕ) : Prop :=
  ∃ e : ℕ → ℤ, (∀ i, e i = 1 ∨ e i = -1) ∧ n = ∑ i ∈ Finset.range k, e i * (2 * (i : ℤ) + 1)

/-- A197702(n): the smallest positive integer k such that Rep n k. -/
noncomputable def a (n : ℕ) : ℕ := sInf {k : ℕ | 0 < k ∧ Rep (n : ℤ) k}

/-- The conjecture of the comment. -/
theorem main :
    (∀ k : ℕ, 1 ≤ k → a (SO k) = k) ∧
    (∀ n k : ℕ, SO (k - 1) < n → n < SO k →
      (SO k - n = 4 → a n = k + 2) ∧
      (SO k - n ≠ 4 → Odd (SO k - n) → a n = k + 1) ∧
      (SO k - n ≠ 4 → ¬ Odd (SO k - n) → a n = k)) := by
  sorry

end OMA.S_oeis_a197702
