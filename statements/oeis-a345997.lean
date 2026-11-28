import Mathlib

/-!
# A345997: Let m = A344005(n) be the smallest number such that n|m*(m+1); let X = A345992(n) = gcd(n,m); Y = A345993(n) = gcd(n,m+1). Sequenc

Source: https://oeis.org/A345997
Credit: @max-otc

Let `m = A344005(n)` be the smallest positive `m` such that `n ∣ m * (m + 1)`, let
`X = A345992(n) = gcd(n, m)` and `Y = A345993(n) = gcd(n, m + 1)`. A345997 lists the `n` such that
neither `X` nor `Y` is equal to `A051119(n) = n / p ^ k`, where `p` is the largest prime divisor of
`n` and `k` is its exponent in `n`. The entry states: "Numbers n such that neither A345992(n) nor
A345993(n) is equal to A051119(n). This disproves an obvious conjecture about A344005."

`main` is that obvious conjecture: for every `n ≥ 1`, `A345992(n) = A051119(n)` or
`A345993(n) = A051119(n)`. The entry reports it false (its first term is `n = 60`).

`gpf n` is the largest prime factor of `n`, and `0` for `n = 1` (empty supremum); then
`a051119 1 = 1 / 0 ^ 0 = 1`, matching `A051119(1) = 1`.
-/

namespace OMA.S_oeis_a345997

/-- A344005: the smallest positive `m` such that `n` divides `m * (m + 1)`. -/
noncomputable def a344005 (n : ℕ) : ℕ := sInf {m : ℕ | 0 < m ∧ n ∣ m * (m + 1)}

/-- The largest prime factor of `n` (`0` when `n` has no prime factor). -/
def gpf (n : ℕ) : ℕ := n.primeFactors.sup id

/-- A051119: `n / p ^ k`, where `p` is the largest prime dividing `n` and `p ^ k` is the highest
power of `p` dividing `n`. -/
def a051119 (n : ℕ) : ℕ := n / gpf n ^ n.factorization (gpf n)

/-- The obvious conjecture about A344005 that A345997 disproves: one of
`A345992(n) = gcd(n, A344005(n))` and `A345993(n) = gcd(n, A344005(n) + 1)` equals `A051119(n)`. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    Nat.gcd n (a344005 n) = a051119 n ∨ Nat.gcd n (a344005 n + 1) = a051119 n := by
  sorry

end OMA.S_oeis_a345997
