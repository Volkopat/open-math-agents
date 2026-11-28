import FormalConjectures.OEIS.«243512»

-- Reduction OeisA243512.conjecture.R1 of the OEIS A243512 conjecture
-- Credit: @marcusbuffett

/-!
# A243512: two infinite families of attained differences, and the open rest

`abundancyDiff i` is numerator minus denominator of `σ(i) / i` in lowest terms, and `a n` is the
least `i > 0` with `abundancyDiff i = n` (or `0`). The conjecture is that every `n` is attained.

* `H1` (provable): for every prime `p`, `n = p + 1` is attained (by `i = p ^ 2`, where
  `σ(p^2) / p^2 = (p^2 + p + 1) / p^2` is already reduced), and for every prime `p ≥ 5`,
  `n = (p + 3) / 2` is attained (by `i = 2 p`, where `σ(2p) / 2p = 3 (p + 1) / 2p` reduces to
  `(3 (p + 1) / 2) / p`).
* `H2` (open): every `n` outside these two families is attained.

These are elementary infinite families, not progress on the conjecture.
-/

namespace OMA.R_OeisA243512_conjecture_R1

/-- Provable: the families `p + 1` and `(p + 3) / 2` are attained. -/
def H1 : Prop :=
  ∀ p : ℕ, p.Prime → OeisA243512.a (p + 1) ≠ 0 ∧ (5 ≤ p → OeisA243512.a ((p + 3) / 2) ≠ 0)

/-- Open: every other difference is attained. -/
def H2 : Prop :=
  ∀ n : ℕ, (∀ p : ℕ, p.Prime → n ≠ p + 1) → (∀ p : ℕ, p.Prime → 5 ≤ p → n ≠ (p + 3) / 2) →
    OeisA243512.a n ≠ 0

theorem main : H1 → H2 → type_of% @OeisA243512.conjecture := by
  intro h1 h2 n
  by_cases hA : ∃ p : ℕ, p.Prime ∧ n = p + 1
  · obtain ⟨p, hp, rfl⟩ := hA
    exact (h1 p hp).1
  by_cases hB : ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ n = (p + 3) / 2
  · obtain ⟨p, hp, h5, rfl⟩ := hB
    exact (h1 p hp).2 h5
  exact h2 n (fun p hp h => hA ⟨p, hp, h⟩) (fun p hp h5 h => hB ⟨p, hp, h5, h⟩)

end OMA.R_OeisA243512_conjecture_R1
