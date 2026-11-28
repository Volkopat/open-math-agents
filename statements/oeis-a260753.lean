import Mathlib

/-!
# A260753: Least positive integer k such that both k and k*n belong to the set {m>0: prime(prime(m))-prime(m)+1 = prime(p) for some prime p}.

Source: https://oeis.org/A260753
Credit: @divmxnd0x

Conjecture (Zhi-Wei Sun, stated in A260753): For any `s` and `t` in the set `{1, -1}`, every positive
rational number `r` can be written as `m/n` with `m` and `n` in the set
`{k > 0 : prime(prime(k)) + s prime(k) + t = prime(p) for some prime p}`.
(The existence of `a(n)` is the case `s = -1`, `t = 1`, `r = n`.)

Formalization notes:
* `prime(k)` is the `k`-th prime with `prime(1) = 2`, i.e. `Nat.nth Nat.Prime (k - 1)`; the
  defining equation is taken in `ℤ`.
* With this definition (`s = -1`, `t = 1`) the least `k` with `k, k n` in the set is 2, 2, 4, 2 for
  `n = 1, 2, 5, 10`, matching the data of A260753.
-/

namespace OMA.S_oeis_a260753

/-- The `k`-th prime, `prime 1 = 2`. -/
noncomputable def prime (k : ℕ) : ℕ :=
  Nat.nth Nat.Prime (k - 1)

/-- `{k > 0 : prime(prime(k)) + s prime(k) + t = prime(p) for some prime p}`. -/
def S (s t : ℤ) : Set ℕ :=
  {k | 0 < k ∧ ∃ p : ℕ, p.Prime ∧ (prime (prime k) : ℤ) + s * prime k + t = prime p}

/-- Sun's conjecture of A260753. -/
theorem main : ∀ s t : ℤ, (s = 1 ∨ s = -1) → (t = 1 ∨ t = -1) →
    ∀ r : ℚ, 0 < r → ∃ m ∈ S s t, ∃ n ∈ S s t, r = (m : ℚ) / n := by
  sorry

end OMA.S_oeis_a260753
