import Mathlib

/-!
# Finite p-groups as points of unipotent groups

Source https://mathoverflow.net/questions/262745/is-every-p-group-the-mathbbf-p-points-of-a-unipotent-group

Does every finite group of order p^n occur as the prime-field points
of an n-dimensional unipotent algebraic group? Over a finite field
one can pass to the smooth identity component and use affine-space
coordinates for the resulting split unipotent group.
-/

namespace OMA.S_mo_262745

abbrev MulPolynomial (p n : ℕ) :=
  Fin n → MvPolynomial (Fin n ⊕ Fin n) (ZMod p)

abbrev InvPolynomial (p n : ℕ) :=
  Fin n → MvPolynomial (Fin n) (ZMod p)

def evalMul {p n : ℕ} {K : Type} [CommRing K] (coeff : ZMod p →+* K)
    (m : MulPolynomial p n) (x y : Fin n → K) : Fin n → K :=
  fun i => MvPolynomial.eval₂ coeff (Sum.elim x y) (m i)

def evalInv {p n : ℕ} {K : Type} [CommRing K] (coeff : ZMod p →+* K)
    (inv : InvPolynomial p n) (x : Fin n → K) : Fin n → K :=
  fun i => MvPolynomial.eval₂ coeff x (inv i)

def productPower {A : Type} (identity : A) (mul : A → A → A) (x : A) : ℕ → A
  | 0 => identity
  | k + 1 => mul (productPower identity mul x k) x

/-- The group laws are polynomial identities, tested over the algebraic
closure. In characteristic p, a common p-power exponent expresses
unipotence for the resulting affine algebraic group. -/
def IsUnipotentGroupLaw {p n : ℕ} [Fact p.Prime]
    (m : MulPolynomial p n) (inv : InvPolynomial p n) : Prop :=
  let coeff := algebraMap (ZMod p) (AlgebraicClosure (ZMod p))
  let mul := evalMul coeff m
  let inverse := evalInv coeff inv
  (∀ x y z, mul (mul x y) z = mul x (mul y z)) ∧
  (∀ x, mul 0 x = x ∧ mul x 0 = x ∧
    mul (inverse x) x = 0 ∧ mul x (inverse x) = 0) ∧
  ∃ k : ℕ, ∀ x, productPower 0 mul x (p ^ k) = 0

theorem main :
    ∀ (p n : ℕ) [Fact p.Prime] (Γ : Type) [Group Γ] [Finite Γ],
      Nat.card Γ = p ^ n →
      ∃ (m : MulPolynomial p n) (inv : InvPolynomial p n),
        IsUnipotentGroupLaw m inv ∧
        ∃ e : Γ ≃ (Fin n → ZMod p), ∀ x y,
          e (x * y) = evalMul (RingHom.id (ZMod p)) m (e x) (e y) := by
  sorry

end OMA.S_mo_262745
