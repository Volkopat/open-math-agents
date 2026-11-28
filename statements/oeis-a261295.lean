import Mathlib

/-!
# A261295: Least positive integer k such that both k and k*n belong to the set {m>0: prime(m) = prime(p)+2 for some prime p}.

Source: https://oeis.org/A261295
Credit: @divmxnd0x

Conjecture (Zhi-Wei Sun, stated in A261295):
(i) Any positive rational number `r` can be written as `m/n` with `m` and `n` in the set
`S = {k > 0 : prime(k) = prime(p) + 2 for some prime p}`.
(ii) Any positive rational number `r` can be written as `m/n` with `m` and `n` in the set
`T = {k > 0 : prime(k) = prime(p) - 2 for some prime p}`.

Formalization notes:
* `prime(k)` is the `k`-th prime with `prime(1) = 2`, i.e. `Nat.nth Nat.Prime (k - 1)`.
* `prime(p) - 2` is never truncated in `T`, since it equals `prime(k) ≥ 2`; we write the condition
  as `prime(k) + 2 = prime(p)`.
* With this definition the least `k` with `k, k n ∈ S` is 3, 3, 6, 3 for `n = 1, 2, 3, 6`, matching
  the data of A261295.
-/

namespace OMA.S_oeis_a261295

/-- The `k`-th prime, `prime 1 = 2`. -/
noncomputable def prime (k : ℕ) : ℕ :=
  Nat.nth Nat.Prime (k - 1)

/-- `S = {k > 0 : prime(k) = prime(p) + 2 for some prime p}`. -/
def S : Set ℕ :=
  {k | 0 < k ∧ ∃ p : ℕ, p.Prime ∧ prime k = prime p + 2}

/-- `T = {k > 0 : prime(k) = prime(p) - 2 for some prime p}`. -/
def T : Set ℕ :=
  {k | 0 < k ∧ ∃ p : ℕ, p.Prime ∧ prime k + 2 = prime p}

/-- Sun's conjecture, parts (i) and (ii). -/
theorem main :
    (∀ r : ℚ, 0 < r → ∃ m ∈ S, ∃ n ∈ S, r = (m : ℚ) / n) ∧
      ∀ r : ℚ, 0 < r → ∃ m ∈ T, ∃ n ∈ T, r = (m : ℚ) / n := by
  sorry

end OMA.S_oeis_a261295
