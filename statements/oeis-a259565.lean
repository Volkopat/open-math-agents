import Mathlib

/-!
# A259565: the greedy sequence whose neighbors have squarefree means

Source: https://oeis.org/A259565
Credit: @avivorly

Definition (A259565): a(1) = 1, for n > 1 a(n) = smallest number not already in the sequence such that the
arithmetic mean of two neighboring terms is a squarefree number.

Conjecture (Reinhard Zumkeller, in the entry): conjecture: sequence is a permutation of the odd numbers;

Conventions:
- The sequence has offset 1. It is given through its prefixes: `pre n` is the list `[a(1), ..., a(n)]` of its
  first `n` terms, and `a n` is the last entry of `pre n`. (The value `a 0 = 0` is a placeholder outside the
  offset; it plays no role.)
- The mean of the previous term `x` and a candidate `k` is a squarefree number:
  `2 ∣ x + k ∧ Squarefree ((x + k) / 2)`. The mean must be an integer, and a squarefree number is a positive
  integer; Mathlib's `Squarefree 0` is false, so positivity is automatic.
- Not already in the sequence: `k ∉ pre n`. Smallest number: `sInf` of the set of eligible `k`, read over
  positive `k` (`0` is never eligible anyway, as the previous term is odd). The set is non-empty (`k = 2 * y - x`
  for a large prime `y`, where `x` is the previous term), so `sInf` is its least element.
- Permutation of the odd numbers: every term `a n` (`n ≥ 1`) is odd, the terms are pairwise distinct, and every
  odd number is a term.
-/

namespace OMA.S_oeis_a259565

/-- `pre n` is the list `[a(1), ..., a(n)]` of the first `n` terms: `pre 0 = []`, `pre 1 = [1]`, and for
`n ≥ 1`, `pre (n + 1)` appends the least positive `k` not in `pre n` whose mean with the last term of `pre n`
is a squarefree integer. -/
noncomputable def pre : ℕ → List ℕ
  | 0 => []
  | 1 => [1]
  | n + 2 => pre (n + 1) ++
      [sInf {k : ℕ | 1 ≤ k ∧ k ∉ pre (n + 1) ∧ 2 ∣ (pre (n + 1)).getLastD 0 + k ∧
        Squarefree (((pre (n + 1)).getLastD 0 + k) / 2)}]

/-- The term `a(n)` (offset 1): the last entry of `pre n`. -/
noncomputable def a (n : ℕ) : ℕ := (pre n).getLastD 0

/-- A259565 is a permutation of the odd numbers: its terms are odd, pairwise distinct, and every odd number
occurs. -/
theorem main :
    (∀ n, 1 ≤ n → Odd (a n)) ∧ (∀ i j, 1 ≤ i → 1 ≤ j → a i = a j → i = j) ∧
      (∀ m, Odd m → ∃ n, 1 ≤ n ∧ a n = m) := by
  sorry

end OMA.S_oeis_a259565
