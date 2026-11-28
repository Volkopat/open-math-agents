import Mathlib

/-!
# A182132: Carmichael numbers of the form C = (30n-7)*(90n-23)*(300n-79)

Source: https://oeis.org/A182132
Credit: @xor2k

Formalizes the OEIS A182132 conjecture (offset 1): The number
C = (30n-7)*(90n-23)*(300n-79) is a Carmichael number if (but not only if) 30n-7, 90n-23
and 300n-79 are all three prime numbers.

Both halves are stated: (i) for every `n ≥ 1`, if `30n-7`, `90n-23` and `300n-79` are all
prime then `C` is a Carmichael number; (ii) the condition is not necessary: for some `n ≥ 1`
the number `C` is a Carmichael number although not all three factors are prime (the entry
itself lists `n = 1, 6, 13, 70` as giving Carmichael numbers with more than three prime
divisors).

Conventions: Carmichael numbers are taken with the defining property of OEIS A002997:
composite numbers `m` (that is, `1 < m` and `m` not prime) such that `b^(m-1) ≡ 1 (mod m)`
for every `b` coprime to `m`. The bases `b` range over `ℕ` (every residue class has a
natural representative), and `m - 1` is ordinary subtraction since `m > 1`. Korselt's
criterion is not built into the definition. The index `n` ranges over the natural numbers
`n ≥ 1` (the OEIS offset; the entry checks `0 < n < 130`); for `n ≥ 1` the natural
subtractions `30n-7`, `90n-23`, `300n-79` do not truncate.
-/

namespace OMA.S_oeis_a182132

/-- Carmichael numbers: composite `m` with `b^(m-1) ≡ 1 (mod m)` for all `b` coprime to `m`. -/
def IsCarmichael (m : ℕ) : Prop :=
  1 < m ∧ ¬ m.Prime ∧ ∀ b : ℕ, b.Coprime m → b ^ (m - 1) ≡ 1 [MOD m]

/-- The number `C(n) = (30n-7)*(90n-23)*(300n-79)`. -/
def C (n : ℕ) : ℕ :=
  (30 * n - 7) * (90 * n - 23) * (300 * n - 79)

/-- (i) For every `n ≥ 1` with `30n-7`, `90n-23`, `300n-79` all prime, `C n` is a Carmichael
number. (ii) For some `n ≥ 1`, `C n` is a Carmichael number although not all three factors
are prime. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → (30 * n - 7).Prime → (90 * n - 23).Prime → (300 * n - 79).Prime →
      IsCarmichael (C n)) ∧
    (∃ n : ℕ, 1 ≤ n ∧ IsCarmichael (C n) ∧
      ¬ ((30 * n - 7).Prime ∧ (90 * n - 23).Prime ∧ (300 * n - 79).Prime)) := by
  sorry

end OMA.S_oeis_a182132
