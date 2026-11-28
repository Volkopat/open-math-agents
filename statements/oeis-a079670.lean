import Mathlib

/-!
# A079670: (gcd(2^p - 1, F(p)) - 1)/(8p) for the primes p of A080050

Source: https://oeis.org/A079670
Credit: @avivorly

A079670 is defined by `a(n) = (gcd(2^p-1, Fibonacci(p))-1)/(8*p) > 0` where `p = A080050(n)`.
A080050 lists the primes `p` such that `2^p-1` and the `p`-th Fibonacci number have a common factor
(11, 8501, 10867, 13109, 14633, 15401, ...); the common factors `gcd(2^p-1, F(p))` form A080051.

Conjecture (the entry's unsigned comment; the entry is by Ralf Stephan, Jan 25 2003):
The members of the sequence seem to be all integers.
Conjecture: a(n) > 1 if A080050(n) !== 1 (mod 10). The reverse is not true.

Both claims are formalized in `main`: the integrality claim as `8 * p ∣ gcdMF p - 1`, and the
conjecture `a(n) > 1` for `A080050(n)` not congruent to `1` mod `10`. The last sentence (the reverse is
not true) is a remark, not part of `main`: `p = 8501 ≡ 1 (mod 10)` is `A080050(2)`, with `a(2) = 10 > 1`.

Conventions:
- `Nat.fib` is the Fibonacci sequence with `F(0) = 0`, `F(1) = 1`, as in A000045.
- `gcdMF p = gcd(2^p - 1, F(p))`; `2^p - 1` is never truncated since `2^p ≥ 1`.
- `InA080050 p` says `p` is a term of A080050: `p` is prime and `gcd(2^p - 1, F(p)) > 1`
  (a common factor means a common divisor `> 1`).
- Offsets (%O): A080050 and A079670 both start at `n = 1`, and A079670(n) is the value at
  `p = A080050(n)`; A080050 lists its members in increasing order without repetition. So a claim for every
  index `n ≥ 1` is the same as the claim for every member `p` of A080050, and `main` quantifies over the
  members `p` directly. (This also avoids a junk value of `Nat.nth` past the end of A080050 if that set
  were finite.)
- `a079670At p = (gcdMF p - 1) / (8 * p)` uses truncating division in `ℕ`; the first conjunct of `main`
  (the integrality claim) makes it exact, and then `a(n) > 1` is `1 < a079670At p`.
-/

namespace OMA.S_oeis_a079670

/-- `gcd(2^p - 1, F(p))`; for `p` in A080050 this is A080051. -/
def gcdMF (p : ℕ) : ℕ := Nat.gcd (2 ^ p - 1) (Nat.fib p)

/-- `p` is a term of A080050: a prime such that `2^p - 1` and `F(p)` have a common factor. -/
def InA080050 (p : ℕ) : Prop := p.Prime ∧ 1 < gcdMF p

/-- The term `a(n)` of A079670 at the index `n` with `p = A080050(n)`:
`(gcd(2^p - 1, F(p)) - 1)/(8 p)`. -/
def a079670At (p : ℕ) : ℕ := (gcdMF p - 1) / (8 * p)

theorem main :
    ∀ p : ℕ, InA080050 p →
      8 * p ∣ gcdMF p - 1 ∧ (p % 10 ≠ 1 → 1 < a079670At p) := by
  sorry

end OMA.S_oeis_a079670
