import Mathlib

/-!
# Are there an infinite number of lucky primes?

Source: https://www.openproblemgarden.org/op/are_there_an_infinite_number_of_lucky_primes
Credit: @lzvxck

The source (Gardiner, Lazarus, Metropolis, Ulam) asks whether infinitely many lucky numbers
are prime. The lucky numbers (OEIS A000959: 1, 3, 7, 9, 13, 15, 21, 25, …) are produced by the
lucky sieve: from the positive integers remove every second one, leaving `1, 3, 5, 7, …`; the
second remaining number is 3, so remove every third remaining number; the next remaining
number is 7, so remove every seventh remaining number; and so on, at stage `k` removing every
`m`-th remaining number where `m` is the `(k+1)`-th remaining number. A lucky number is one
that is never removed. (The source's prose description of the sieve is garbled; this is the
standard lucky sieve the problem is about.)

Stage `k` of the sieve is encoded as the increasing enumeration `luckyStage k : ℕ → ℕ` of the
numbers still present (0-indexed). Removing every `m`-th element sends new index `i` to old
index `i + i / (m - 1)`.
-/

namespace OMA.S_opg_are_there_an_infinite_number_of_lucky_primes

/-- The numbers remaining after stage `k` of the lucky sieve, enumerated increasingly
(index 0 is `1`). Stage 0 is the odd numbers; stage `k + 1` removes every `m`-th remaining
number, where `m = luckyStage k (k + 1)` is the `(k + 2)`-th remaining number (`3, 7, 9, …`). -/
def luckyStage : ℕ → ℕ → ℕ
  | 0 => fun i => 2 * i + 1
  | k + 1 => fun i => luckyStage k (i + i / (luckyStage k (k + 1) - 1))

/-- `n` is a lucky number: it survives every stage of the lucky sieve. -/
def IsLucky (n : ℕ) : Prop :=
  ∀ k, n ∈ Set.range (luckyStage k)

/-- **Lucky primes.** There are infinitely many lucky numbers that are prime. -/
theorem main : Set.Infinite {p : ℕ | p.Prime ∧ IsLucky p} := by
  sorry

end OMA.S_opg_are_there_an_infinite_number_of_lucky_primes
