import Mathlib

/-!
# Monomial symmetric polynomials evaluated at every root of unity

Source: wkmath, https://mathoverflow.net/questions/475626 (CC BY-SA 4.0).
Credit: @connoranderson

The orbit contains each rearrangement of the exponent list once, even when
parts repeat. The integer formula uses the sign of the permutation induced
by adding the assigned exponents to their positions modulo the number of
variables. A nonpermutation contributes zero.
-/

namespace OMA.S_mo_475626

noncomputable def arrangements {n : ℕ} (a : Fin n → ℕ) : Finset (Fin n → ℕ) :=
  Finset.univ.image (fun σ : Equiv.Perm (Fin n) => a ∘ σ)

noncomputable def monomialSymmetric {n : ℕ} (a : Fin n → ℕ) (x : Fin n → ℂ) : ℂ :=
  ∑ b ∈ arrangements a, ∏ j, x j ^ b j

def shift {n : ℕ} (b : Fin (n+1) → ℕ) (j : Fin (n+1)) : Fin (n+1) :=
  ⟨(j.val + b j) % (n+1), Nat.mod_lt _ (Nat.succ_pos _)⟩

noncomputable def contribution {n : ℕ} (b : Fin (n+1) → ℕ) : ℤ := by
  classical
  exact if h : Function.Bijective (shift b) then
    (Equiv.Perm.sign (Equiv.ofBijective (shift b) h) : ℤˣ) else 0

theorem main : ∀ (n : ℕ) (a : Fin (n+1) → ℕ) (ζ : ℂ), Antitone a → (∀ i, 0<a i) →
    IsPrimitiveRoot ζ (n+1) →
    monomialSymmetric a (fun i => ζ^i.val) = ((∑ b ∈ arrangements a, contribution b : ℤ) : ℂ) := by
  sorry

end OMA.S_mo_475626
