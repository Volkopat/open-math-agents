import Mathlib

/-!
# The greedy reduced-Collatz preimage sequence A386314

Source: https://oeis.org/A386314
Credit: @etaubman

The natural index `n` below represents OEIS index `n+1`. An accelerated
odd-to-odd step from `k` to odd `y` means precisely that 3k+1 equals a
power of two times y. The inputs and outputs enumerated here are positive
integers congruent to 1 or 5 modulo 6. The hypothesis uses ordinary,
unaccelerated Collatz trajectories.
-/

namespace OMA.S_oeis_a386314

def step (k : ℕ) : ℕ := if k % 2 = 0 then k / 2 else 3 * k + 1

inductive ReachesOne : ℕ → Prop
  | one : ReachesOne 1
  | back {k : ℕ} : ReachesOne (step k) → ReachesOne k

def Collatz : Prop := ∀ k : ℕ, 0 < k → ReachesOne k

def good (k : ℕ) : Prop := 0 < k ∧ k % 2 = 1 ∧ k % 3 ≠ 0

def reduced (k y : ℕ) : Prop := y % 2 = 1 ∧ ∃ e : ℕ, 3 * k + 1 = 2 ^ e * y

def eligible (s : Finset ℕ) (k : ℕ) : Prop :=
  good k ∧ k ∉ s ∧ (k = 1 ∨ ∃ y ∈ s, reduced k y)

noncomputable def pick (s : Finset ℕ) : ℕ := by
  classical
  exact if h : ∃ k, eligible s k then Nat.find h else 0

noncomputable def seen : ℕ → Finset ℕ
  | 0 => ∅
  | n + 1 => insert (pick (seen n)) (seen n)

noncomputable def term (n : ℕ) : ℕ := pick (seen n)

theorem main : Collatz → Function.Injective term ∧
    (∀ n, good (term n)) ∧ (∀ k, good k → ∃ n, term n = k) := by
  sorry

end OMA.S_oeis_a386314
