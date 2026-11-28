import Mathlib

/-!
# A395616: Number of cyclic permutations sigma of Z/2^n such that sigma(i+1) is in {2*sigma(i), 2*sigma(i)+1} for all i in Z/2^n.

Source: https://oeis.org/A395616
Credit: @esracummings31-blip

a(n) (offset 1) is the number of permutations `σ` of `ZMod (2^n)` that are cyclic (a single cycle of
length `2^n`, i.e. `σ.IsCycle` and `σ.support = univ`) and satisfy
`σ (i + 1) = 2 * σ i ∨ σ (i + 1) = 2 * σ i + 1` for every `i : ZMod (2^n)`.
Data: 1, 1, 2, 16, 1936, 66615032.

Conjectures (Noah Weninger, Timothy Christopher Miller, Bailey Parrish, Jun 28 2026):
1. a(n) > 0 for all n ≥ 1 (verified computationally for n ≤ 24).
2. a(n) / A016031(n) → 1 as n → ∞, where A016031(n) = 2^(2^(n-1) - n) is the number of binary
   de Bruijn sequences of order n.
-/

namespace OMA.S_oeis_a395616

/-- The defining property: `σ` is a cyclic permutation of `ZMod (2^n)` (one cycle through all
`2^n` residues) and `σ (i + 1) ∈ {2 σ(i), 2 σ(i) + 1}` for all `i`. -/
def Good (n : ℕ) (σ : Equiv.Perm (ZMod (2 ^ n))) : Prop :=
  σ.IsCycle ∧ σ.support = Finset.univ ∧ ∀ i : ZMod (2 ^ n), σ (i + 1) = 2 * σ i ∨ σ (i + 1) = 2 * σ i + 1

/-- A395616. -/
noncomputable def a (n : ℕ) : ℕ := Nat.card {σ : Equiv.Perm (ZMod (2 ^ n)) // Good n σ}

/-- A016031: 2^(2^(n-1) - n), the number of binary de Bruijn sequences of order n. -/
def A016031 (n : ℕ) : ℕ := 2 ^ (2 ^ (n - 1) - n)

theorem main :
    (∀ n : ℕ, 1 ≤ n → 0 < a n) ∧
    Filter.Tendsto (fun n : ℕ => (a n : ℝ) / (A016031 n : ℝ)) Filter.atTop (nhds 1) := by
  sorry

end OMA.S_oeis_a395616
