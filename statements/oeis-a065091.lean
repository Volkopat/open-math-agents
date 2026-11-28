import Mathlib

/-!
# OEIS A065091: odd primes via an Agoh–Giuga type congruence

Source: https://oeis.org/A065091
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

A065091 lists the odd primes: `a(n) = prime(n+1)`. Conjecture (OEIS entry, an extension of the
Agoh–Giuga conjecture): `a(n)` is the smallest odd number `m > prime(n)` such that
`∑_{k=1}^{prime(n)-1} k^(m-1) ≡ prime(n) - 1 (mod m)`.

Conventions:
* `prime(n) = Nat.nth Nat.Prime (n - 1)` (`prime(1) = 2`), `n ≥ 1`. "Smallest" is stated as: the
  next prime `m = prime(n+1)` satisfies the congruence, and no odd `m` with
  `prime(n) < m < prime(n+1)` does.
-/

namespace OMA.S_oeis_a065091

/-- The congruence condition for `p` and `m`. -/
def Cond (p m : ℕ) : Prop := (∑ k ∈ Finset.Icc 1 (p - 1), k ^ (m - 1)) % m = (p - 1) % m

/-- `prime(n+1)` is the least odd `m > prime(n)` satisfying the congruence. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    let p := Nat.nth Nat.Prime (n - 1)
    let q := Nat.nth Nat.Prime n
    Cond p q ∧ ∀ m : ℕ, Odd m → p < m → m < q → ¬ Cond p m := by
  sorry

end OMA.S_oeis_a065091
