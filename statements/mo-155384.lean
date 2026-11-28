import Mathlib

/-!
# The Gram determinant of a rectangular Vandermonde matrix

Source: dima, https://mathoverflow.net/questions/155384 (CC BY-SA).
Credit: @connoranderson.

The permutation sum below gives a formula for any row count N. Each fixed
point contributes N, and each moved point contributes one geometric quotient.
For roots of unity with common period L, the determinant is a monic polynomial
of degree k in N on every residue class modulo L.
-/

namespace OMA.S_mo_155384
open Equiv Matrix

noncomputable def vand {k : ℕ} (z : Fin k → ℂ) (N : ℕ) : Matrix (Fin N) (Fin k) ℂ :=
  fun r j => z j ^ r.val

noncomputable def gram {k : ℕ} (z : Fin k → ℂ) (N : ℕ) :=
  (vand z N).conjTranspose * vand z N

noncomputable def quotient {k : ℕ} (z : Fin k → ℂ) (N : ℕ) (i j : Fin k) : ℂ :=
  ((z j / z i)^N - 1)/(z j / z i - 1)

theorem main :
    ∀ (k : ℕ) (z : Fin k → ℂ), Function.Injective z → (∀ j, ‖z j‖=1) →
    (∀ N : ℕ, (gram z N).det =
      ∑ σ : Perm (Fin k), Perm.sign σ •
        ((N:ℂ)^σ.supportᶜ.card * ∏ i ∈ σ.support, quotient z N (σ i) i)) ∧
    ∀ L : ℕ, 0<L → (∀ i, z i^L=1) → ∀ r : ℕ, r<L →
      ∃ P : Polynomial ℂ, P.Monic ∧ P.natDegree=k ∧
        ∀ m : ℕ, (gram z (m*L+r)).det = P.eval ((m*L+r : ℕ) : ℂ) := by
  sorry

end OMA.S_mo_155384
