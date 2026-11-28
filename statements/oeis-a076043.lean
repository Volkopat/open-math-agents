import Mathlib

/-!
# A076043: a(1)=2; for n>1, a(n) is the smallest squarefree number (greater than 1)
not occurring earlier such that a(n) + a(n-1) is a square.

Source: https://oeis.org/A076043
Credit: @cjchaffin

Conjecture (stated on the OEIS page): every squarefree number except 1 is a member.

Conventions:
- The name starts the sequence at `a(1) = 2`, and the listed data (and the greedy rule)
  match that indexing. The `%O` field on the page says `0,1`, which would put the first
  term at index 0; we follow the name and the clause `a(1)=2`.
- "Squarefree number (greater than 1)" is Mathlib's `Squarefree` with the lower bound
  `1 < m` (Mathlib treats `1` as squarefree). Each later term is the least such `m` not
  already used whose sum with the previous term is a square. The conjecture is that this
  listing is a permutation of the squarefree integers greater than 1.
-/

namespace OMA.S_oeis_a076043

/-- A squarefree integer `m > 1` is eligible to follow `prev` given the terms already used. -/
def eligible (used : Finset ℕ) (prev m : ℕ) : Prop :=
  1 < m ∧ Squarefree m ∧ m ∉ used ∧ IsSquare (prev + m)

/-- `a` is the greedy listing defined in the sequence name, starting at `a 1 = 2`. -/
def IsGreedy (a : ℕ → ℕ) : Prop :=
  a 1 = 2 ∧
    ∀ n : ℕ, 1 ≤ n →
      eligible ((Finset.Icc 1 n).image a) (a n) (a (n + 1)) ∧
        ∀ m : ℕ, eligible ((Finset.Icc 1 n).image a) (a n) m → a (n + 1) ≤ m

theorem main :
    ∃ a : ℕ → ℕ, IsGreedy a ∧ ∀ m : ℕ, 1 < m → Squarefree m → ∃ n : ℕ, 1 ≤ n ∧ a n = m := by
  sorry

end OMA.S_oeis_a076043
