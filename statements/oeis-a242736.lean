import Mathlib

/-!
# A242736: the number of solutions of a^2 + b^2 == -1 modulo the n-th prime is nondecreasing

Source: https://oeis.org/A242736 (OEIS Foundation, CC BY-SA 4.0).
Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)

Entry A242736, offset 1:
Number of solutions of a^2 + b^2 congruent to -1 modulo the n-th prime. Data
0, 1, 1, 1, 2, 2, 3, 3, 3, 4, 4, 5, 6, 6, 6, 7, 8, 8, 9, 9, 10, 10, 11, 12, 13, 13, 13, 14, 14, ...

Comments: a(n) is the number of solutions of a^2 + b^2 congruent to -1 modulo the n-th prime,
where 0 <= a <= b <= floor((p-1)/2).
Is this sequence nondecreasing? The data for the first thousand terms supports this conjecture.
Formula section: See the answer given in the link above.
For n>1, a(n) = ceiling(p(n)/8), where p(n) is the n-th prime.

Formalization notes.
* `cnt p` is the number of pairs (a, b) of natural numbers with a <= b <= floor((p-1)/2) and
  p | a^2 + b^2 + 1. The values of `cnt` at the primes 2, 3, ..., 41 agree with the data.
* The n-th prime (n >= 1, prime(1) = 2) is `Nat.nth Nat.Prime (n - 1)`.
* `main` states the conjecture: a(n) <= a(n+1) for all n >= 1. The formula section of the entry
  gives the closed form ceiling(p/8) without a proof in the entry; the proof here contains a
  proof of this closed form for odd primes.
-/

namespace OMA.S_oeis_a242736

/-- The number of pairs (a, b) with 0 ≤ a ≤ b ≤ floor((p-1)/2) and a^2 + b^2 ≡ -1 (mod p). -/
def cnt (p : ℕ) : ℕ :=
  ((Finset.range ((p - 1) / 2 + 1) ×ˢ Finset.range ((p - 1) / 2 + 1)).filter
    (fun z => z.1 ≤ z.2 ∧ p ∣ z.1 ^ 2 + z.2 ^ 2 + 1)).card

/-- A242736(n), n ≥ 1: the count for the n-th prime (prime(1) = 2). -/
noncomputable def a (n : ℕ) : ℕ := cnt (Nat.nth Nat.Prime (n - 1))

/-- The sequence is nondecreasing. -/
theorem main : ∀ n : ℕ, 1 ≤ n → a n ≤ a (n + 1) := by
  sorry

end OMA.S_oeis_a242736
