import Mathlib

/-!
# The reciprocal inversion count of a uniform permutation

Source: user50460, https://mathoverflow.net/questions/165529 (CC BY-SA 3.0).
Credit: @connoranderson. Richard Stanley identified the integrated Mahonian
generating polynomial in the source comments. PeterR pointed out the classical
independent uniform inversion digits. We use the digit recurrence and eight
centered moments to obtain an explicit second-order expansion.

The unregularized reciprocal has infinite mean because the identity permutation
has no inversions. Adding one gives 4/n² + 52/(9n³) with absolute error at most
100/n⁴ for every n at least two.
-/
namespace OMA.S_mo_165529
open Finset Filter
open scoped Topology
abbrev Perm (n : ℕ) := Equiv.Perm (Fin n)
def inversions {n : ℕ} (σ : Perm n) : ℕ :=
  ∑ i, ∑ j, if i<j ∧ σ j<σ i then 1 else 0
noncomputable def average (n : ℕ) (f : Perm n → ℝ) : ℝ := (∑ σ, f σ)/(n.factorial:ℝ)
noncomputable def reciprocal (n : ℕ) : ℝ := average n (fun σ => ((inversions σ : ℝ)+1)⁻¹)
open scoped ENNReal
noncomputable def unshifted (n : ℕ) : ℝ≥0∞ :=
  (∑ σ : Perm n, ((inversions σ:ℝ≥0∞))⁻¹)/(n.factorial:ℝ≥0∞)

theorem main :
    (∀ n : ℕ, unshifted n = ⊤) ∧
    (∀ n : ℕ, 2≤n → |reciprocal n - (4/(n:ℝ)^2+52/(9*(n:ℝ)^3))| ≤ 100/(n:ℝ)^4) ∧
    Tendsto (fun n : ℕ => (n:ℝ)^3*(reciprocal n-4/(n:ℝ)^2)) atTop (𝓝 (52/9:ℝ)) := by
  sorry

end OMA.S_mo_165529
