import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Find
import Mathlib.Data.Finset.Basic

/-!
# The parity-alternating shared-digit greedy permutation

Sources: OEIS A318698 and its offset-parity companion A318699, OEIS
Foundation, CC BY-SA 4.0. https://oeis.org/A318698 and https://oeis.org/A318699

The first starts at zero and follows the index parity. The second starts at
one and follows the opposite parity. Zero has the one decimal digit 0.
-/

namespace OMA.S_oeis_a318698

def digits (n : ℕ) : List ℕ := if n = 0 then [0] else Nat.digits 10 n

def shares (u v : ℕ) : Prop := ∃ d ∈ digits u, d ∈ digits v

def eligible (seen : Finset ℕ) (prev parity x : ℕ) : Prop :=
  x ∉ seen ∧ x%2 = parity%2 ∧ shares prev x

noncomputable def next (seen : Finset ℕ) (prev parity : ℕ) : ℕ := by
  classical
  exact if h : ∃ x, eligible seen prev parity x then Nat.find h else 0

noncomputable def state (seed : ℕ) : ℕ → ℕ × Finset ℕ
  | 0 => (seed, {seed})
  | n+1 =>
    let (v, seen) := state seed n
    let w := next seen v (n+1+seed)
    (w, insert w seen)

noncomputable def a (seed n : ℕ) : ℕ := (state seed n).1

theorem main : Function.Bijective (a 0) ∧ Function.Bijective (a 1) := by
  sorry

end OMA.S_oeis_a318698
