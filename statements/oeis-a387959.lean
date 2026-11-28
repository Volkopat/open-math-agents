import Mathlib

/-!
# A387959: Least positive integer m such that the n numbers (prime(1)-1)^2,...,(prime(n)-1)^2 are pairwise incongruent modulo m.

Source: https://oeis.org/A387959
Credit: @eltociear

`a(n)` (offset 1) is the least `m > 0` such that `(prime(1) - 1)^2, …, (prime(n) - 1)^2` are pairwise
incongruent modulo `m` (`1, 2, 7, 9, 13, 17, ...`). The entry conjectures (Zhi-Wei Sun; verified
for `n ≤ 10^7`):

  a(n) = prime(n+1) except for n = 1, 2, 4, 9.

`main` states that `a(n) = prime(n+1)` for every `n ≥ 1` outside `{1, 2, 4, 9}`. Pairwise
incongruent means that `i ↦ (prime(i) - 1)^2 mod m` is injective on `[1, n]`. `a n` is the `sInf`
of the admissible `m` (such `m` exist, e.g. any `m` larger than all the squares). `prime(k)` is
`Nat.nth Nat.Prime (k - 1)`.
-/

namespace OMA.S_oeis_a387959

/-- `prime n` is the `n`-th prime, 1-indexed (`prime 1 = 2`). -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- OEIS A387959: the least `m > 0` making `(prime i - 1)^2`, `1 ≤ i ≤ n`, pairwise incongruent. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {m : ℕ | 0 < m ∧ Set.InjOn (fun i => (prime i - 1) ^ 2 % m) (Set.Icc 1 n)}

/-- The conjecture in OEIS A387959. -/
theorem main : ∀ n : ℕ, 1 ≤ n → n ∉ ({1, 2, 4, 9} : Finset ℕ) → a n = prime (n + 1) := by
  sorry

end OMA.S_oeis_a387959
