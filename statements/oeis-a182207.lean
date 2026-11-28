import Mathlib

/-!
# A182207: Carmichael numbers of the form C = p*(2p-1)*(n*(2p-2)+p), where p and 2p-1 are prime numbers

Source: https://oeis.org/A182207
Credit: @xor2k

Formalizes the OEIS A182207 conjecture: Any Carmichael number C divisible by p and 2p-1
(where p and 2p-1 are prime numbers) can be written as C = p*(2p-1)*(n*(2p-2)+p).

Conventions: Carmichael numbers are taken with the defining property of OEIS A002997:
composite numbers `m` (that is, `1 < m` and `m` not prime) such that `b^(m-1) ≡ 1 (mod m)`
for every `b` coprime to `m`. The bases `b` range over `ℕ` (every residue class has a
natural representative), and `m - 1` is ordinary subtraction since `m > 1`. Korselt's
criterion is not built into the definition. The primes `p` and `2p-1` range over natural
numbers, and the integer `n` in `n*(2p-2)+p` is a natural number `n ≥ 0`, which is the
strongest reading.

Remark: this statement is of the same kind as statements/oeis-a182206.lean and
statements/oeis-a182515.lean (same definition of Carmichael number, conclusion of the shape
`C = p * q * (a * n + b)`), but it is a family statement rather than an instance of those: the fixed
primes are replaced by a universally quantified prime `p` and `q = 2p - 1`, with `a = 2p - 2` and
`b = p`, exactly as in the title of A182207.
-/

namespace OMA.S_oeis_a182207

/-- Carmichael numbers: composite `m` with `b^(m-1) ≡ 1 (mod m)` for all `b` coprime to `m`. -/
def IsCarmichael (m : ℕ) : Prop :=
  1 < m ∧ ¬ m.Prime ∧ ∀ b : ℕ, b.Coprime m → b ^ (m - 1) ≡ 1 [MOD m]

/-- Every Carmichael number `C` divisible by primes `p` and `2p-1` equals
`p * (2p-1) * (n * (2p-2) + p)` for some natural number `n`. -/
theorem main :
    ∀ C p : ℕ, IsCarmichael C → p.Prime → (2 * p - 1).Prime → p ∣ C → 2 * p - 1 ∣ C →
      ∃ n : ℕ, C = p * (2 * p - 1) * (n * (2 * p - 2) + p) := by
  sorry

end OMA.S_oeis_a182207
