import Mathlib

/-!
# MathOverflow 427621: maximum elements of a numerical semigroup of order between n and 2n

Source: https://mathoverflow.net/questions/427621
Credit: @OrangeHeadz (agent: Claude Code, model claude-fable-5-2)

Question (Dylan C. Beck): Let `S` be a numerical semigroup, i.e. a submonoid of the non-negative
integers with finite complement, and let `S^*` be the set of nonzero elements of `S`. For a
non-negative integer `n`, the `n`-fold sum of `S^*` is
`n S^* = {s₁ + ⋯ + s_n | s₁, …, s_n ∈ S^*}`. For each positive integer `n`, does
`max (n S^* \ 2n S^*) ≤ max ((2n - 1) S^* \ 2n S^*)` hold?

We state the affirmative answer; a disproof of `main` answers the question negatively.

Conventions:
* `sStar S` is `S^*` and `nsum T k` is the `k`-fold sum of the set `T`, with the empty sum
  `nsum T 0 = {0}` (the question only uses `k ≥ 1`).
* As the question notes, for `n ≥ 1` the sets `n S^* \ 2n S^*` and `(2n - 1) S^* \ 2n S^*` are
  finite and nonempty, so their maximum is their supremum in `ℕ`; we write it as `sSup`.
-/

namespace OMA.S_mo_427621

/-- `S^*`: the nonzero elements of `S`. -/
def sStar (S : AddSubmonoid ℕ) : Set ℕ := {s | s ∈ S ∧ s ≠ 0}

/-- The `k`-fold sum `{t₁ + ⋯ + t_k | t₁, …, t_k ∈ T}` of a set `T` of natural numbers. -/
def nsum (T : Set ℕ) : ℕ → Set ℕ
  | 0 => {0}
  | k + 1 => {x | ∃ s ∈ nsum T k, ∃ t ∈ T, x = s + t}

/-- For every numerical semigroup `S` and every `n ≥ 1`,
`max (n S^* \ 2n S^*) ≤ max ((2n - 1) S^* \ 2n S^*)`. -/
theorem main : ∀ S : AddSubmonoid ℕ, ((S : Set ℕ)ᶜ).Finite → ∀ n : ℕ, 1 ≤ n →
    sSup (nsum (sStar S) n \ nsum (sStar S) (2 * n)) ≤
      sSup (nsum (sStar S) (2 * n - 1) \ nsum (sStar S) (2 * n)) := by
  sorry

end OMA.S_mo_427621
