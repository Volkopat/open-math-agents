import Mathlib

/-!
# Number of cells hit by a random permutation

Source: https://mathoverflow.net/questions/374584
Credit: @Mapika

The numerator counts permutations of Fin n meeting at least r marked cells.
We maximize over boards with exactly floor(α n) cells and also evaluate the
partial diagonal proposed in the question.
-/

open Filter
open scoped Topology BigOperators
namespace OMA.S_mo_374584

abbrev Board (n : ℕ) := Finset (Fin n × Fin n)

def goodCount (n r : ℕ) (A : Board n) : ℕ :=
  (Finset.univ.filter fun π : Equiv.Perm (Fin n) =>
    r ≤ (A.filter fun x => π x.1 = x.2).card).card

noncomputable def maximumTail (n a r : ℕ) : ℝ :=
  ((Finset.univ : Finset (Board n)).sup
    (fun A => if A.card = a then goodCount n r A else 0) : ℕ) / (n.factorial : ℝ)

def partialDiagonal (n a : ℕ) : Board n :=
  Finset.univ.filter fun x => x.1 = x.2 ∧ x.1.val < a

noncomputable def poissonTail (α : ℝ) (r : ℕ) : ℝ :=
  1 - Real.exp (-α) * ∑ j ∈ Finset.range r, α ^ j / (j.factorial : ℝ)

theorem main : ∀ α : ℝ, α ∈ Set.Icc 0 1 → ∀ r : ℕ, 2 ≤ r →
    Tendsto (fun n : ℕ => maximumTail n ⌊α * n⌋₊ r) atTop (𝓝 (poissonTail α r)) ∧
    Tendsto (fun n : ℕ => (goodCount n r (partialDiagonal n ⌊α * n⌋₊) : ℝ) /
      (n.factorial : ℝ)) atTop (𝓝 (poissonTail α r)) := by
  sorry

end OMA.S_mo_374584
