import Mathlib

/-!
# A109132: Numbers n such that n! + 1 is a Chen prime

Source: https://oeis.org/A109132
Credit: @jrflga (agent: Claude Code, model claude-fable-5-2)

OEIS name: Numbers n such that n! + 1 is a Chen prime. n! + 1 is then called a factorial Chen
prime. OEIS comment: Conjecture: 77! + 1 is the largest factorial Chen prime.

The entry has offset 1 and its known terms are `0, 1, 2, 3, 11, 77`. Chen primes are A109611:
primes p such that p + 2 is either a prime or a semiprime (a product of two primes).

## Encoding

* `IsSemiprime m` says that `m` is a product of two primes, not necessarily distinct.
* `IsChenPrime p` is the definition of A109611.
* `IsFactorialChenPrime p` says that `p` is a Chen prime of the form `n! + 1` for a natural
  number `n` (`n = 0` is allowed: it is the first term of the entry).
* `main` reads *is the largest* literally, with `IsGreatest`: `77! + 1` is a factorial Chen
  prime, and every factorial Chen prime is at most `77! + 1`.
-/

namespace OMA.S_oeis_a109132

/-- `m` is a semiprime: a product of two primes, not necessarily distinct. -/
def IsSemiprime (m : ℕ) : Prop :=
  ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ m = p * q

/-- A Chen prime (A109611): a prime `p` such that `p + 2` is either a prime or a semiprime. -/
def IsChenPrime (p : ℕ) : Prop :=
  p.Prime ∧ ((p + 2).Prime ∨ IsSemiprime (p + 2))

/-- A factorial Chen prime: a Chen prime of the form `n! + 1`. -/
def IsFactorialChenPrime (p : ℕ) : Prop :=
  IsChenPrime p ∧ ∃ n : ℕ, p = n.factorial + 1

theorem main : IsGreatest {p : ℕ | IsFactorialChenPrime p} (Nat.factorial 77 + 1) := by
  sorry

end OMA.S_oeis_a109132
