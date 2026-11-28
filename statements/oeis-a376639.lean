import Mathlib

/-!
# A376639: terms of A151999 that are not terms of A293928

Source: https://oeis.org/A376639
Credit: @avivorly

A376639 lists the terms of A151999 which are not a term of A293928, where
- A151999: numbers `k` such that every prime that divides `phi(k)` also divides `k`;
- A293928: totients `phi(m)` having one or more solutions `m` to `phi(m)^2 = phi(phi(m)*m)`.

Conjectures (Torlach Rush, in the entry):
1. For each `a(n)` there is no `a(n) = A000010(a(k))`, `k > n`.
2. Every term of A293928 exists in A151999.

`A000010` is Euler's totient function `phi`, here `Nat.totient`.

Conventions:
- A151999 has offset `1` and first term `1`; its terms are the positive integers `k` with every prime factor of
  `Nat.totient k` dividing `k` (`k = 0` is excluded: it would pass vacuously, as `Nat.totient 0 = 0`).
- A293928 has first term `1`; `t` is a term when `t = Nat.totient m` for some `m ≥ 1` with
  `Nat.totient m ^ 2 = Nat.totient (Nat.totient m * m)` (`m = 0` is excluded: it would add `t = 0`).
- A376639 has offset `1`: `a n = Nat.nth InA376639 (n - 1)` is its `n`-th term (in increasing order) for `n ≥ 1`.
  The set is infinite (`2 * 5 ^ j` is a term for every `j ≥ 1`), so `a n` is a genuine term for every `n ≥ 1`.
- Conjecture 1 is stated literally, with the index condition `k > n`. (Since `a` is increasing and
  `Nat.totient s < s` for `s ≥ 2`, a pair with `k ≤ n` could never give `a n = Nat.totient (a k)` anyway.)
- The two conjectures are stated together, as a conjunction.
-/

namespace OMA.S_oeis_a376639

/-- `k` is a term of A151999: `k ≥ 1` and every prime that divides `Nat.totient k` also divides `k`. -/
def InA151999 (k : ℕ) : Prop :=
  0 < k ∧ ∀ p ∈ (Nat.totient k).primeFactors, p ∣ k

/-- `t` is a term of A293928: `t = Nat.totient m` for some `m ≥ 1` solving
`Nat.totient m ^ 2 = Nat.totient (Nat.totient m * m)`. -/
def InA293928 (t : ℕ) : Prop :=
  ∃ m : ℕ, 0 < m ∧ Nat.totient m = t ∧ Nat.totient m ^ 2 = Nat.totient (Nat.totient m * m)

/-- `s` is a term of A376639: a term of A151999 which is not a term of A293928. -/
def InA376639 (s : ℕ) : Prop :=
  InA151999 s ∧ ¬ InA293928 s

/-- `a n`: the `n`-th term of A376639 (offset `1`). -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth InA376639 (n - 1)

theorem main :
    (∀ n : ℕ, 1 ≤ n → ¬ ∃ k : ℕ, n < k ∧ a n = Nat.totient (a k)) ∧
      (∀ t : ℕ, InA293928 t → InA151999 t) := by
  sorry

end OMA.S_oeis_a376639
