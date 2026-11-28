import Mathlib

/-!
# Irreducibility over the fraction field of a curve

Source: Nils Amend, https://mathoverflow.net/questions/257393 (CC BY-SA 3.0).
Credit: @connoranderson

We write ℓ = m+1. The variable indexed by i : Fin (m+1) represents
x_(i+1), while the constants z are indexed from 0 through ℓ.
The source explicitly permits assuming that the relation ideal is prime.
-/

namespace OMA.S_mo_257393
open MvPolynomial

abbrev Raw (m : ℕ) := MvPolynomial (Fin (m+1)) ℂ

noncomputable def relation (m r : ℕ) (z : Fin (m+2) → ℂ) (i : Fin m) : Raw m :=
  C (z (Fin.last (m+1))) * X i.castSucc ^ r -
    C (z i.castSucc.succ) * X (Fin.last m) ^ r -
    C (z (Fin.last (m+1)) - z i.castSucc.succ)

noncomputable def relations (m r : ℕ) (z : Fin (m+2) → ℂ) : Ideal (Raw m) :=
  Ideal.span (Set.range (relation m r z))

abbrev Curve (m r : ℕ) (z : Fin (m+2) → ℂ) := Raw m ⧸ relations m r z
abbrev F (m r : ℕ) (z : Fin (m+2) → ℂ) := FractionRing (Curve m r z)

noncomputable def coordinate (m r : ℕ) (z : Fin (m+2) → ℂ) (i : Fin (m+1)) : Curve m r z :=
  Ideal.Quotient.mk _ (X i)

noncomputable def x (m r : ℕ) (z : Fin (m+2) → ℂ) (i : Fin (m+1)) : F m r z :=
  algebraMap (Curve m r z) (F m r z) (coordinate m r z i)

noncomputable def p (m r k : ℕ) (z : Fin (m+2) → ℂ) : Polynomial (F m r z) :=
  Polynomial.C (algebraMap ℂ (F m r z) (z (Fin.last (m+1)))) * Polynomial.X ^ (r+k) -
    Polynomial.C ((∏ i : Fin (m+1) with i.val < k, x m r z i) * (1-x m r z (Fin.last m)^r))

noncomputable def q₀ (m r : ℕ) (z : Fin (m+2) → ℂ) : Polynomial (F m r z) :=
  Polynomial.C (algebraMap ℂ (F m r z) (z (Fin.last (m+1)))) * Polynomial.X ^ r -
    Polynomial.C (algebraMap ℂ (F m r z) (z 0) * x m r z (Fin.last m)^r +
      algebraMap ℂ (F m r z) (z (Fin.last (m+1)) - z 0))

theorem main : ∀ (m r k : ℕ) (z : Fin (m+2) → ℂ), 2 ≤ m → 2 ≤ r → 1 ≤ k → k ≤ m →
    (∀ i, z i ≠ 0) → Function.Injective z → (relations m r z).IsPrime →
    Irreducible (p m r k z) ∧ Irreducible (q₀ m r z) := by
  sorry

end OMA.S_mo_257393
