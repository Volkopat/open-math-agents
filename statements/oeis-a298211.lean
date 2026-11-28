import Mathlib

/-!
# A298211: rank of apparition of `n` in A001353

Source: https://oeis.org/A298211
Credit: @avivorly

A298211 (name, verbatim): Smallest n such that A001353(a(n)) == 0 (mod n), i.e., x=A001075(a(n)) and
y=A001353(a(n)) is the fundamental solution of the Pell equation x^2 - 3*(n*y)^2 = 1.
The entry adds: the fundamental solution of the Pell equation x^2 - 3*(n*y)^2 = 1 is the smallest solution of
x^2 - 3*y^2 = 1 satisfying y == 0 (mod n).

A001353: `U(0) = 0`, `U(1) = 1`, `U(i) = 4*U(i-1) - U(i-2)` (0, 1, 4, 15, 56, 209, ...).
A005385: the safe primes `p`, with `p` and `(p-1)/2` both prime (5, 7, 11, 23, 47, ...; offset 1).
A005384: the Sophie Germain primes `q`, with `q` and `2*q+1` both prime (2, 3, 5, 11, 23, ...; offset 1).

Conjecture (in the entry's formula section, verbatim):
a(k*A005385(n)) = a(k)*A005384(n) for n>2 and k > 0 (conjectured).

Conventions:
- `U : ℕ → ℤ` is A001353, defined by its recurrence and read in `ℤ`, so the subtraction is the literal one. The values
  stay nonnegative (`U(i) ≥ U(i-1) ≥ 0` gives `4*U(i-1) - U(i-2) ≥ 3*U(i-1) ≥ 0`), so a `ℕ`-valued copy would agree.
- `a n` is the least index `i ≥ 1` with `n ∣ U i`, as `sInf` of that set. The name's leading `Smallest n` means the
  smallest index `a(n)`. The index `0` is excluded, since `U(0) = 0` is divisible by every `n`: the data starts with
  `a(1) = 1`, and both programs in the entry (Mathematica `FirstPosition` over `U(1), U(2), ...`; Python, a loop that
  starts at index `1` with `U(1) = 1`) search the indices `i ≥ 1` only. For every `n ≥ 1` the set is nonempty (the map
  `(x, y) ↦ (y, 4*y - x)` is invertible mod `n`, so the pairs `(U(i), U(i+1))` mod `n` return to `(0, 1)`); the
  statement does not rely on this. For `n = 0` the set is empty and `sInf` gives `0`, a value the conjecture never
  reaches, since `k ≥ 1` and every safe prime is `≥ 5`.
- `safe n` is A005385(n) and `sophie n` is A005384(n), both with the OEIS offset `1`: `Nat.nth` counts from `0`, so
  `safe n := Nat.nth _ (n - 1)` and likewise `sophie`. Thus `safe 1 = 5`, `safe 2 = 7`, `safe 3 = 11` and
  `sophie 1 = 2`, `sophie 2 = 3`, `sophie 3 = 5`; the conjecture's `n > 2` is `n ≥ 3` (it leaves out `p = 5` and
  `p = 7`). With these offsets `A005385(n) = 2*A005384(n) + 1` for every `n ≥ 1`, since `q ↦ 2*q + 1` is an increasing
  bijection from the Sophie Germain primes onto the safe primes. The junk value at `n = 0` is never used.
- The safe-prime test `p.Prime ∧ ((p - 1) / 2).Prime` uses `ℕ` division: exact for odd `p`, and for `p = 2` it gives
  `0`, not prime, so the predicate holds exactly for the safe primes.
- `k` is a natural number with `0 < k`.
-/

namespace OMA.S_oeis_a298211

/-- A001353: `U 0 = 0`, `U 1 = 1`, `U (i + 2) = 4 * U (i + 1) - U i`. -/
def U : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | i + 2 => 4 * U (i + 1) - U i

/-- A298211: the least index `i ≥ 1` with `n ∣ U i` (the rank of apparition of `n` in A001353). -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {i : ℕ | 1 ≤ i ∧ (n : ℤ) ∣ U i}

/-- A005385 with offset 1: `safe n` is the `n`-th safe prime (`safe 1 = 5`). -/
noncomputable def safe (n : ℕ) : ℕ :=
  Nat.nth (fun p : ℕ => p.Prime ∧ ((p - 1) / 2).Prime) (n - 1)

/-- A005384 with offset 1: `sophie n` is the `n`-th Sophie Germain prime (`sophie 1 = 2`). -/
noncomputable def sophie (n : ℕ) : ℕ :=
  Nat.nth (fun p : ℕ => p.Prime ∧ (2 * p + 1).Prime) (n - 1)

theorem main :
    ∀ n : ℕ, 2 < n → ∀ k : ℕ, 0 < k → a (k * safe n) = a k * sophie n := by
  sorry

end OMA.S_oeis_a298211
