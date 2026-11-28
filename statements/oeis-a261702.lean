import Mathlib

/-!
# The greedy Collatz preimage sequence A261702

Source: https://oeis.org/A261702
Credit: @etaubman

The index in `term` counts from zero, so `term n` is OEIS a(n+1).
One is initially eligible. Thereafter the new entries are exactly the
unseen positive integers whose Collatz successors have appeared.
-/

namespace OMA.S_oeis_a261702

def step (k : ℕ) : ℕ := if k % 2 = 0 then k / 2 else 3 * k + 1

inductive ReachesOne : ℕ → Prop
  | one : ReachesOne 1
  | back {k : ℕ} : ReachesOne (step k) → ReachesOne k

def Collatz : Prop := ∀ k : ℕ, 0 < k → ReachesOne k

def eligible (s : Finset ℕ) (k : ℕ) : Prop :=
  0 < k ∧ k ∉ s ∧ (k = 1 ∨ step k ∈ s)

noncomputable def pick (s : Finset ℕ) : ℕ := by
  classical
  exact if h : ∃ k, eligible s k then Nat.find h else 0

noncomputable def seen : ℕ → Finset ℕ
  | 0 => ∅
  | n + 1 => insert (pick (seen n)) (seen n)

noncomputable def term (n : ℕ) : ℕ := pick (seen n)

theorem main : Collatz → Function.Injective term ∧
    (∀ n, 0 < term n) ∧ (∀ k : ℕ, 0 < k → ∃ n, term n = k) := by
  sorry

end OMA.S_oeis_a261702
