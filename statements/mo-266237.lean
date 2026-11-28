import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.Field.Rat

/-!
# Random Balanced Assignment

Source: https://mathoverflow.net/questions/266237 (Steve, 2017).
Credit: @LDJAI

For a fixed balanced assignment to K labeled classes, choose a second balanced
assignment uniformly. The point probability for their minimum Hamming distance
after relabeling is given by the following finite contingency-table formula.
The parameter m is the common class size, so N = K * m.
-/

namespace OMA.S_mo_266237

open Finset

/-- Number of objects carrying each label. -/
def counts {A : Type*} [Fintype A] {K : ℕ} (f : A → Fin K) (j : Fin K) : ℕ :=
  (univ.filter fun x => f x = j).card

/-- All labeled balanced assignments. -/
def balanced (N K m : ℕ) : Finset (Fin N → Fin K) :=
  univ.filter fun f => counts f = fun _ => m

/-- Minimum number of mismatches over all permutations of the reference labels. -/
noncomputable def distance {N K : ℕ} (f τ : Fin N → Fin K) : ℕ :=
  univ.inf' univ_nonempty fun p : Equiv.Perm (Fin K) =>
    (univ.filter fun x => f x ≠ p (τ x)).card

/-- Nonnegative integer tables with all row and column sums equal to m. -/
noncomputable def tables (K m : ℕ) : Finset (Fin K → Fin K → ℕ) :=
  (Fintype.piFinset fun _ : Fin K => (univ : Finset (Fin K)).piAntidiag m).filter
    fun t => ∀ j, ∑ i, t i j = m

/-- The minimum off-diagonal mass after relabeling the columns. -/
noncomputable def tableDistance {K : ℕ} (t : Fin K → Fin K → ℕ) : ℕ :=
  univ.inf' univ_nonempty fun p : Equiv.Perm (Fin K) =>
    ∑ i, ∑ j, if j = p i then 0 else t i j

/-- The product of the row multinomial coefficients. -/
def weight {K : ℕ} (t : Fin K → Fin K → ℕ) : ℕ :=
  ∏ i, Nat.multinomial univ (t i)

/-- Exact point probabilities for every sample size, class count, reference and distance. -/
theorem main : ∀ (N K m : ℕ), 0 < K → N = K * m →
    ∀ τ ∈ balanced N K m, ∀ d : ℕ,
      (((balanced N K m).filter fun f => distance f τ = d).card : ℚ) /
          ((balanced N K m).card : ℚ) =
        ((∑ t ∈ (tables K m).filter (fun t => tableDistance t = d), weight t : ℕ) : ℚ) /
          (Nat.multinomial univ (fun _ : Fin K => m) : ℚ) := by
  sorry

end OMA.S_mo_266237
