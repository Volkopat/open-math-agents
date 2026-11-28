import OMAStatements.S_arxiv_2609_05358

/-!
# Reduction R1 of arxiv-2609.05358: split off the slab `a < b < 2a`, `a + b < c < 2b`

Conjecture 52 (open direction) of arXiv 2609.05358 is split along the parameter region

  `a < b < 2a` and `a + b < c < 2b`,

that is `b = a + d`, `c = 2a + d + r` with `0 < r < d < a`: winding number 1 and angle
`0 < ρ < δ`. For `b ≤ 2a` the paper lists `0 < ρ < δ` as exactly the angles that no test
covers (Section 6), so on this slab the conjecture says that no game is purely periodic.

* `H1`: the conjecture on the slab. It holds there because no game in the slab is purely periodic
  (from a period, the block of `a` consecutive P-positions at the start repeats at a multiple
  of the period, and independence and domination, read backwards from it, force a contradiction).
  Inside the slab the paper records as proved only the lines `{a, a+2, 2a+3}` and
  `{a, 2a-1, 4a-3}`, `a` odd (from Zhang, Theorem 6.3); Moriwaki excludes there only the three
  candidate periods. The line `b = 2a` (Zhang, Proposition 3.1) lies outside the slab.
* `H2`: the conjecture on every remaining parameter. This is the open part.
-/

namespace OMA.R_arxiv_2609_05358_R1

open OMA.S_arxiv_2609_05358

/-- The open direction of Conjecture 52 on the slab `a < b < 2a`, `a + b < c < 2b`. -/
def H1 : Prop :=
  ∀ a b c : ℕ, 2 ≤ a → a < b → b < c → Nat.gcd (Nat.gcd a b) c = 1 → c ≠ a + b →
    b < 2 * a → a + b < c → c < 2 * b →
    (∃ p ≥ 1, ∀ x, grundy {a, b, c} (x + p) = grundy {a, b, c} x) →
    T0 a b c ∨ T1 a b c ∨ T2 a b c

/-- The open direction of Conjecture 52 outside the slab. -/
def H2 : Prop :=
  ∀ a b c : ℕ, 2 ≤ a → a < b → b < c → Nat.gcd (Nat.gcd a b) c = 1 → c ≠ a + b →
    ¬ (b < 2 * a ∧ a + b < c ∧ c < 2 * b) →
    (∃ p ≥ 1, ∀ x, grundy {a, b, c} (x + p) = grundy {a, b, c} x) →
    T0 a b c ∨ T1 a b c ∨ T2 a b c

theorem main : H1 → H2 → type_of% @OMA.S_arxiv_2609_05358.main := by
  intro h1 h2 a b c ha hab hbc hg hne hper
  by_cases hs : b < 2 * a ∧ a + b < c ∧ c < 2 * b
  · exact h1 a b c ha hab hbc hg hne hs.1 hs.2.1 hs.2.2 hper
  · exact h2 a b c ha hab hbc hg hne hs hper

end OMA.R_arxiv_2609_05358_R1
