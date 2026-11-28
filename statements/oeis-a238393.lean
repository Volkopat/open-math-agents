import Mathlib

/-!
# A238393: a(n) = |{0 < k <= n: 2*p(k)*p(n) + 1 is prime}|, where p(.) is the partition function (A000041).

Source: https://oeis.org/A238393
Credit: @azmiozgen

Conjecture (Zhi-Wei Sun, from the entry):
(i) a(n) > 0 for all n > 0, and a(n) = 1 only for n = 1, 2, 13.
(ii) If n > 1, then 2*p(k)*p(n) - 1 is prime for some 0 < k < n.
(iii) For any integer n > 0, p(k)*(p(n)+1) + 1 is prime for some k = 1, ..., n.

Formalization notes:
* p(n) = `Fintype.card (Nat.Partition n)` (the partition function A000041); q(n), the number of
  partitions of n into distinct parts (A000009), is the number of `Nat.Partition n` whose parts
  have no repetition.
* Parts (i) and (ii) are stated; "a(n) = 1 only for n in S" is stated as: for n ≥ 1, a(n) = 1
  iff n ∈ S.
* Part (iii) is not stated: a direct computation finds that it fails for n = 11 (p(11) = 56 and
  57 p(k) + 1 for k = 1..11 is 58, 115, 172, 286, 400, 628, 856, 1255, 1711 = 29*59, 2395,
  3193 = 31*103, none prime) and for n = 26.
* Controls (computed): a(1..25) = 1, 1, 3, 2, 3, 2, 5, 2, 6, 3, 3, 5, 1, 9, 3, 4, 5, 5, 6, 2, 7, 3, 5,
  8, 3, as in the entry; parts (i) and (ii) hold for n < 130.
-/

namespace OMA.S_oeis_a238393

/-- The partition function `p(n)`. -/
noncomputable def p (n : ℕ) : ℕ := Fintype.card (Nat.Partition n)

/-- A238393(n). -/
noncomputable def a (n : ℕ) : ℕ := ((Finset.Icc 1 n).filter fun k => (2 * p k * p n + 1).Prime).card

/-- The conjecture of the entry (the parts listed above). -/
theorem main :
    (∀ n : ℕ, 0 < n → 0 < a n) ∧
      (∀ n : ℕ, 0 < n → (a n = 1 ↔ n = 1 ∨ n = 2 ∨ n = 13)) ∧
      ∀ n : ℕ, 1 < n → ∃ k, 0 < k ∧ k < n ∧ (2 * p k * p n - 1).Prime := by
  sorry

end OMA.S_oeis_a238393
