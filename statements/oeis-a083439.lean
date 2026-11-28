import Mathlib

/-!
# A083439: a(1) = 3; then a(n+1) = smallest prime not already in the sequence such that the concatenations a(n)a(n+1) and a(n+1)a(n) are both primes.

Source: https://oeis.org/A083439
Credit: @gblacher2

Conjecture (Robert Israel, May 24 2026, comment in A083439): "every prime == 1 (mod 6) occurs
in the sequence."

Conventions:
* the offset of A083439 is 1; the sequence is encoded as `a : ℕ → ℕ` with `a n = a(n+1)`, so
  `a 0 = 3`;
* concatenation is in base 10: `concat x y` is the number whose decimal digits are those of `x`
  followed by those of `y`, i.e. `x * 10 ^ (number of digits of y) + y`;
* "smallest prime not already in the sequence" means the least prime `q` different from
  `a 0, ..., a n`; the greedy recursion is encoded by the predicate `IsA083439`, which pins down
  the sequence uniquely when it exists; the conjecture is stated for every sequence satisfying it;
* "every prime == 1 (mod 6) occurs in the sequence" means that every prime `p` with
  `p % 6 = 1` is a value of `a`.
-/

namespace OMA.S_oeis_a083439

/-- Decimal concatenation: the digits of `x` followed by the digits of `y`. -/
def concat (x y : ℕ) : ℕ :=
  x * 10 ^ (Nat.digits 10 y).length + y

/-- `a` is the sequence A083439, shifted to offset 0: `a 0 = 3` and, for `n ≥ 0`, `a (n + 1)`
is the least prime `q` not among `a 0, ..., a n` such that the concatenations `a n ‖ q` and
`q ‖ a n` are both prime. -/
def IsA083439 (a : ℕ → ℕ) : Prop :=
  a 0 = 3 ∧ ∀ n : ℕ,
    IsLeast {q : ℕ | q.Prime ∧ (∀ i ≤ n, a i ≠ q) ∧
      (concat (a n) q).Prime ∧ (concat q (a n)).Prime} (a (n + 1))

/-- The conjecture: every prime congruent to 1 modulo 6 occurs in A083439. -/
theorem main : ∀ a : ℕ → ℕ, IsA083439 a →
    ∀ p : ℕ, p.Prime → p % 6 = 1 → p ∈ Set.range a := by
  sorry

end OMA.S_oeis_a083439
