import Mathlib

/-!
# Perpetually Fair Assignments Via Balanced Sequences of Permutations

Source: https://arxiv.org/abs/2602.21687v3 (Adams and Segal-Halevi), Section 7, Open Question 1:
"Is there, for every n ≥ 1, a 2-balanced permutation sequence?"
Credit: @tatashbar

Model (Section 2). There are `n` items `1, …, n` (item `1` is the best) and `n` players. On each of
the days `1, …, n` an assignment, a bijection from items to players, is used. A permutation sequence
is this list of `n` assignments. The source does not require it to be a latin square.

`Z_i^t` is the multiset of items that player `i` holds after day `t`, and `Z_i^t[j]` is its `j`-th
smallest label. For an integer `c ≥ 1`, the sequence is `c`-balanced (Section 7, condition (3)) if
`Z_i^t[j] ≤ ⌊(j + c - 1) n / t + 1⌋` for all players `i`, all days `t ∈ [n]` and all `j ∈ [t]`.

Here `Z_i^t[j] ≤ B` is written as: at least `j` of the first `t` items of player `i` have label at
most `B`. This is the same condition, because `Z_i^t` has exactly `t` elements.

Known from the source: the stronger conditions with bound `⌈j n / t⌉` (fully balanced) and
`⌊j n / t + 1⌋` (weakly fully balanced, the case `c = 1`) hold for some sequence when `n ≤ 11` and
`n ≤ 12`, and for no sequence when `n > 61` and `n > 108`. The case `c = 2` is open in the source.

Note from the contributor, not from the source and not formalised: an argument through Halász's
L1 lower bound for the discrepancy of point sets in the square gives `c ≥ κ √(log n) - O(1)` for
every `c`-balanced sequence, so `main` would be false for all sufficiently large `n`. The argument
gives no explicit `n`. The statement below is the question exactly as the source asks it.
-/

namespace OMA.S_arxiv_2602_21687

/-- The label (from `1` to `n`) of the item that player `i` receives on day `d`, where `s d` maps
each item to the player who receives it on day `d`. -/
def item {n : ℕ} (s : Fin n → Equiv.Perm (Fin n)) (i d : Fin n) : ℕ :=
  ((s d).symm i).val + 1

/-- The number of the first `t` days on which player `i` receives an item with label at most `B`. -/
def countUpTo {n : ℕ} (s : Fin n → Equiv.Perm (Fin n)) (i : Fin n) (t B : ℕ) : ℕ :=
  (Finset.univ.filter fun d : Fin n => d.val < t ∧ item s i d ≤ B).card

/-- Condition (3) of the source: `Z_i^t[j] ≤ ⌊(j + c - 1) n / t + 1⌋` for all `i`, all `t ∈ [n]`
and all `j ∈ [t]`. -/
def IsBalanced {n : ℕ} (c : ℕ) (s : Fin n → Equiv.Perm (Fin n)) : Prop :=
  ∀ i : Fin n, ∀ t j : ℕ, 1 ≤ j → j ≤ t → t ≤ n →
    j ≤ countUpTo s i t ((j + c - 1) * n / t + 1)

theorem main : ∀ n : ℕ, 1 ≤ n → ∃ s : Fin n → Equiv.Perm (Fin n), IsBalanced 2 s := by
  sorry

end OMA.S_arxiv_2602_21687
