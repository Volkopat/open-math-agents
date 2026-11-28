import Mathlib

/-!
# The permanent after adding a constant to every entry

Source: Turbo, https://mathoverflow.net/questions/262336 (CC BY-SA 3.0).
Zach Teitler's answer gives the formula by grouping products in the expansion.
Credit: @connoranderson.

For fixed rows S, summing over injections from S into the columns sums the
permanents of all minors on those rows. The empty minor has permanent one.
Every nonzero integer shift also distinguishes two 2-by-2 integer matrices
with the same original permanent.
-/

namespace OMA.S_mo_262336

noncomputable def perm {n : ℕ} {R : Type*} [CommRing R] (M : Matrix (Fin n) (Fin n) R) : R :=
  ∑ σ : Equiv.Perm (Fin n), ∏ i, M i (σ i)

noncomputable def minors {n : ℕ} {R : Type*} [CommRing R] (M : Matrix (Fin n) (Fin n) R)
    (S : Finset (Fin n)) : R := ∑ e : S ↪ Fin n, ∏ i : S, M i (e i)

theorem main : (∀ (R : Type) [CommRing R] (n : ℕ) (M : Matrix (Fin n) (Fin n) R) (a : ℤ),
    perm (fun i j => M i j + (a:R)) = ∑ S : Finset (Fin n),
      ((n-S.card).factorial : R) * (a:R)^(n-S.card) * minors M S) ∧
    (∀ a : ℤ, a ≠ 0 → ∃ M N : Matrix (Fin 2) (Fin 2) ℤ,
      perm M = perm N ∧ perm (fun i j => M i j+a) ≠ perm (fun i j => N i j+a)) := by
  sorry

end OMA.S_mo_262336
