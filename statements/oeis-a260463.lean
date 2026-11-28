import Mathlib

/-!
# A260463: the greedy sequence whose squares begin with the index

Source: https://oeis.org/A260463
Credit: @avivorly

Definition (the entry's name, offset 1): a(n) is the smallest number not already in the sequence such that a(n)^2
begins with n.
The data starts 1, 5, 6, 2, 23, 8, 27, 9, 3, 10, ...; the entry notes a(25) = 16.

Conjecture (Derek Orr, in the entry): Conjectured to be a permutation of the natural numbers.

Conventions:
- `Begins n x` says `n * 10 ^ j ≤ x < (n + 1) * 10 ^ j` for some `j`. For `n ≥ 1` this is exactly: the decimal
  expansion of `x` starts with the decimal expansion of `n` (`x` is `n` followed by `j` more digits).
- `pre n` is the list of the first `n` terms. The term number `n + 1` is the least `k` that is not in `pre n` (not
  already in the sequence) such that `Begins (n + 1) (k ^ 2)`; smallest is `sInf`. The number `0` never qualifies
  (`0` begins with no `n ≥ 1`). The set is non-empty for every `n` (this is shown in the proof), so `sInf` is its
  least element; the definition itself assumes nothing.
- `a n = (pre n).getLastD 0` is the `n`-th term for `n ≥ 1`.
- A permutation of the natural numbers (offset 1, terms `≥ 1`): every term is `≥ 1`, no two indices `≥ 1` carry the
  same term, and every `m ≥ 1` is a term.
-/

namespace OMA.S_oeis_a260463

/-- `x` begins with `n` in decimal: `x` is `n` followed by `j` more digits, for some `j`. -/
def Begins (n x : ℕ) : Prop := ∃ j : ℕ, n * 10 ^ j ≤ x ∧ x < (n + 1) * 10 ^ j

/-- The first `n` terms of the greedy sequence: the next term is the least number not yet used whose square
begins with its index. -/
noncomputable def pre : ℕ → List ℕ
  | 0 => []
  | n + 1 => pre n ++ [sInf {k : ℕ | k ∉ pre n ∧ Begins (n + 1) (k ^ 2)}]

/-- The `n`-th term (offset 1): the last entry of the first `n` terms. -/
noncomputable def a (n : ℕ) : ℕ := (pre n).getLastD 0

theorem main :
    (∀ n, 1 ≤ n → 1 ≤ a n) ∧ (∀ i j, 1 ≤ i → 1 ≤ j → a i = a j → i = j) ∧
      (∀ m, 1 ≤ m → ∃ n, 1 ≤ n ∧ a n = m) := by
  sorry

end OMA.S_oeis_a260463
