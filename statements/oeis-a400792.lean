import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Order.Lattice.Nat

/-!
# The greedy coprimality permutation conjecture for A400792

Conjecture by Paolo Xausa and Michael De Vlieger, https://oeis.org/A400792.
OEIS text, CC BY-SA 4.0. Formalization by @pmaster with Codex.
The first term is indexed by zero here. Each subsequent term is the least
unused positive integer whose number of smaller coprime predecessors exceeds
its number of larger noncoprime predecessors by exactly one. The range is
expressed as the strictly positive natural numbers.
-/

namespace OMA.S_oeis_a400792

def good (s : Finset ℕ) (k : ℕ) : ℕ :=
  (s.filter fun x => x < k ∧ Nat.Coprime x k).card

def bad (s : Finset ℕ) (k : ℕ) : ℕ :=
  (s.filter fun x => k < x ∧ ¬ Nat.Coprime x k).card

def eligible (s : Finset ℕ) (k : ℕ) : Prop :=
  0 < k ∧ k ∉ s ∧ good s k = bad s k + 1

noncomputable def pick (s : Finset ℕ) : ℕ := sInf {k | eligible s k}

noncomputable def seen : ℕ → Finset ℕ
  | 0 => {1}
  | t + 1 => insert (pick (seen t)) (seen t)

noncomputable def a : ℕ → ℕ
  | 0 => 1
  | t + 1 => pick (seen t)

theorem main : Function.Injective a ∧ Set.range a = Set.Ioi 0 := by
  sorry

end OMA.S_oeis_a400792
