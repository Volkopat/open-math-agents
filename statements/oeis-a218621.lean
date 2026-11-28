import Mathlib

/-!
# A218621: a(n) = unique divisor d of n such that d + (n/d - 1)/2 is minimal and integral.

Source: https://oeis.org/A218621
Credit: @agchua

Comment of A218621 (unsigned; the entry is by L. Edson Jeffery, Feb 18 2013):
  Conjecture. For n, p, v, j natural numbers, the conditions on a(n) seem to be the following:
  1. If n is an odd prime, then a(n) = 1.
  2. If n is odd and composite, then
       a(n) = max(p : p | n, p <= sqrt(n), p is a prime).
  3. If n is equal to a power of 2, then a(n) = n.
  4. If n = 2^j*v, with v odd, v>1 and j>1, then a(n) = 2^j.
  5. If n = 2*v, with v odd and composite, then
       a(n) = 2*p, where p is the least prime such that p | v.
  6. If n = 2*p, for p an odd prime, then a(n) = 2.
Offset of A218621: 1 (data 1, 2, 1, 4, 1, 2, 1, 8, 3, 2, ...).

Formalisation. For a divisor d of n the value d + (n/d - 1)/2 is computed in the rationals
(val n d). Adm n d says that d divides n and that this value is an integer; IsA n d says that
in addition the value is minimal among the values of all such divisors. For every n >= 1 exactly
one d has IsA n d (the admissible divisors form a finite set that contains the largest power of 2
dividing n, and two admissible divisors d1 < d2 with equal value would force n = 2*d1*d2, so that
n/d1 = 2*d2 would be even and d1 not admissible), and a(n) is that d. So the conjecture says: for
every n >= 1 and every d with IsA n d, the six conditions hold with a(n) = d.
Composite means greater than 1 and not prime. For natural p, p <= sqrt(n) is p * p <= n. The max of
condition 2 is expressed with IsGreatest (the set is finite and, for odd composite n, nonempty);
the least prime dividing v in condition 5 is Nat.minFac v.
-/

namespace OMA.S_oeis_a218621

/-- The value d + (n/d - 1)/2, computed in the rationals. -/
def val (n d : ℕ) : ℚ := (d : ℚ) + ((n : ℚ) / (d : ℚ) - 1) / 2

/-- d is a divisor of n and d + (n/d - 1)/2 is an integer. -/
def Adm (n d : ℕ) : Prop := d ∣ n ∧ ∃ z : ℤ, val n d = (z : ℚ)

/-- d = a(n): d is admissible and its value is minimal among the values of all admissible
divisors of n. -/
def IsA (n d : ℕ) : Prop := Adm n d ∧ ∀ e : ℕ, Adm n e → val n d ≤ val n e

/-- The comment's conjecture, conditions 1 to 6, for every n >= 1 with a(n) = d. -/
theorem main : ∀ n d : ℕ, 1 ≤ n → IsA n d →
    ((Nat.Prime n ∧ Odd n) → d = 1) ∧
    ((Odd n ∧ 1 < n ∧ ¬ Nat.Prime n) →
      IsGreatest {p : ℕ | p ∣ n ∧ p * p ≤ n ∧ Nat.Prime p} d) ∧
    (∀ j : ℕ, n = 2 ^ j → d = n) ∧
    (∀ j v : ℕ, n = 2 ^ j * v → Odd v → 1 < v → 1 < j → d = 2 ^ j) ∧
    (∀ v : ℕ, n = 2 * v → Odd v → 1 < v → ¬ Nat.Prime v → d = 2 * Nat.minFac v) ∧
    (∀ p : ℕ, n = 2 * p → Nat.Prime p → Odd p → d = 2) := by
  sorry

end OMA.S_oeis_a218621
