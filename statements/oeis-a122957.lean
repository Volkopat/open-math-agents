import Mathlib

/-!
# A122957: Numbers n such that if m > n, phi(m) >= phi(n).

Source: https://oeis.org/A122957
Credit: @agchua

Comment line of A122957 (the entry is by Franklin T. Adams-Watters, Oct 25 2006), verbatim:
  Conjecture: except for 1,2,3,4, this is the nonzero values of A066362.
Offset of A122957: 1 (data 1, 2, 3, 4, 6, 8, 10, 12, 14, 18, 20, 24, 30, 36, ...).
A066362 (offset 1, by Joseph L. Pe): a(n) = least k > n such that phi(k) < phi(n), if such a k
exists; otherwise a(n) = 0 (data 0, 0, 0, 0, 6, 0, 8, 0, 10, 0, 12, 0, 14, 0, 18, 18, 18, 0,
20, 0, 22, 24, 24, ...).

Formalisation. phi is Nat.totient. A positive integer m is a term of A122957 if phi(k) >= phi(m)
for every k > m (InA122957 m). The terms other than 1, 2, 3, 4 are the terms m > 4. The nonzero
values of A066362 are the numbers m != 0 such that A066362(n) = m for some n >= 1. The
conjecture says that these two sets of numbers are equal.
-/

namespace OMA.S_oeis_a122957

/-- m is a term of A122957: m >= 1 and phi(k) >= phi(m) for every k > m. -/
def InA122957 (m : ℕ) : Prop := 1 ≤ m ∧ ∀ k : ℕ, m < k → Nat.totient m ≤ Nat.totient k

open Classical in
/-- A066362: the least k > n with phi(k) < phi(n), or 0 if there is no such k. -/
noncomputable def A066362 (n : ℕ) : ℕ :=
  if h : ∃ k : ℕ, n < k ∧ Nat.totient k < Nat.totient n then Nat.find h else 0

/-- The terms of A122957 other than 1, 2, 3, 4 are exactly the nonzero values of A066362. -/
theorem main : ∀ m : ℕ, (InA122957 m ∧ 4 < m) ↔ (m ≠ 0 ∧ ∃ n : ℕ, 1 ≤ n ∧ A066362 n = m) := by
  sorry

end OMA.S_oeis_a122957
