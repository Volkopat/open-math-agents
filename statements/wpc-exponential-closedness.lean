import Mathlib

/-!
# Zilber's Exponential-Algebraic Closedness Conjecture

Source: https://en.wikipedia.org/wiki/Existential_closedness_conjecture
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Every irreducible algebraic subvariety $V \subseteq \mathbb{C}^n \times (\mathbb{C}^\times)^n$
that is free and rotund contains a point of the form $(z, \exp(z)) = (z_1, \ldots, z_n,
e^{z_1}, \ldots, e^{z_n})$ for some $z \in \mathbb{C}^n$.

Conventions:
- We represent an algebraic subvariety of $\mathbb{C}^n \times (\mathbb{C}^\times)^n$ by
  a prime ideal `I` in `MvPolynomial (Fin n ⊕ Fin n) ℂ`, where `Sum.inl i` represents the
  additive coordinate `x_i` and `Sum.inr i` represents the multiplicative coordinate `y_i`,
  such that `∏ i, X (Sum.inr i) ∉ I` (so $V(I)$ is not contained in any hyperplane $y_i = 0$).
- `IsAdditivelyFree I`: no nontrivial $\mathbb{Z}$-linear relation $\sum_i m_i x_i = c$
  holds identically on $V(I)$.
- `IsMultiplicativelyFree I`: no nontrivial multiplicative relation
  $\prod_{m_i > 0} y_i^{m_i} = c \prod_{m_i < 0} y_i^{-m_i}$ ($c \ne 0$) holds on $V(I)$.
- For a $k \times n$ integer matrix $M$, the monomial map $(x, y) \mapsto (Mx, y^M)$ induces
  a ring homomorphism from the Laurent polynomial ring $\mathbb{C}[u_1,\dots,u_k, v_1^{\pm 1},\dots,v_k^{\pm 1}]$
  into the localization of $\mathbb{C}[x, y] / I$ at the multiplicative coordinates $y_1 \cdots y_n$.
  `IsRotund I` requires that for every $1 \le k \le n$ and every $M \in M_{k \times n}(\mathbb{Z})$
  of rank $k$, the Zariski closure of the image of $V(I)$ under $(x, y) \mapsto (Mx, y^M)$
  has Krull dimension at least $k$.
-/

namespace OMA.S_wpc_exponential_closedness

/-- Polynomial ring `ℂ[x₁, ..., xₙ, y₁, ..., yₙ]`. -/
abbrev PolyRing (n : ℕ) := MvPolynomial (Fin n ⊕ Fin n) ℂ

/-- A prime ideal `I` in `ℂ[x, y]` is additively free if no nonzero `ℤ`-linear combination
of the `x_i` is constant modulo `I`. -/
def IsAdditivelyFree {n : ℕ} (I : Ideal (PolyRing n)) : Prop :=
  ∀ (m : Fin n → ℤ) (c : ℂ),
    (∑ i : Fin n, MvPolynomial.C (m i : ℂ) * MvPolynomial.X (Sum.inl i)) - MvPolynomial.C c ∈ I →
    m = 0

/-- A prime ideal `I` in `ℂ[x, y]` is multiplicatively free if no nontrivial Laurent
monomial relation `∏_{m_i ≥ 0} y_i^{m_i} = c * ∏_{m_i < 0} y_i^{-m_i}` (`c ≠ 0`) lies in `I`. -/
def IsMultiplicativelyFree {n : ℕ} (I : Ideal (PolyRing n)) : Prop :=
  ∀ (m : Fin n → ℤ) (c : ℂ),
    c ≠ 0 →
    (∏ i : Fin n, MvPolynomial.X (Sum.inr i) ^ (m i).toNat) -
      MvPolynomial.C c * (∏ i : Fin n, MvPolynomial.X (Sum.inr i) ^ (-m i).toNat) ∈ I →
    m = 0

/-- The ring homomorphism `ℂ[u₁, ..., u_k, v₁, ..., v_k] → Localization.Away (∏ y_i)` (modulo `I`)
corresponding to the map `(x, y) ↦ (M x, y^M)`. -/
noncomputable def matrixPullback {n k : ℕ} (I : Ideal (PolyRing n))
    (M : Matrix (Fin k) (Fin n) ℤ) :
    PolyRing k →+* Localization.Away (Ideal.Quotient.mk I (∏ i : Fin n, MvPolynomial.X (Sum.inr i))) :=
  let yProd : PolyRing n ⧸ I := Ideal.Quotient.mk I (∏ i : Fin n, MvPolynomial.X (Sum.inr i))
  let toLoc : PolyRing n →+* Localization.Away yProd :=
    (algebraMap (PolyRing n ⧸ I) (Localization.Away yProd)).comp (Ideal.Quotient.mk I)
  MvPolynomial.eval₂Hom (toLoc.comp MvPolynomial.C) (fun idx =>
    match idx with
    | Sum.inl r =>
        ∑ j : Fin n, toLoc (MvPolynomial.C (M r j : ℂ) * MvPolynomial.X (Sum.inl j))
    | Sum.inr r =>
        (∏ j : Fin n, toLoc (MvPolynomial.X (Sum.inr j)) ^ (M r j).toNat) *
          (IsLocalization.Away.invSelf yProd) ^ (∑ j : Fin n, (-M r j).toNat) *
          (∏ j : Fin n, toLoc (∏ l : Fin n, if l = j then 1 else MvPolynomial.X (Sum.inr l)) ^ (-M r j).toNat))

/-- `I` is rotund if for every `1 ≤ k ≤ n` and every `k × n` integer matrix `M` of rank `k`,
the image of `V(I)` under `(x, y) ↦ (M x, y^M)` has Zariski dimension at least `k`. -/
def IsRotund {n : ℕ} (I : Ideal (PolyRing n)) : Prop :=
  ∀ (k : ℕ) (M : Matrix (Fin k) (Fin n) ℤ),
    1 ≤ k →
    (M.map (Int.castRingHom ℚ)).rank = k →
    (k : WithBot ℕ∞) ≤ ringKrullDim (PolyRing k ⧸ RingHom.ker (matrixPullback I M))

theorem main :
    ∀ (n : ℕ) (I : Ideal (PolyRing n)),
      I.IsPrime →
      (∏ i : Fin n, MvPolynomial.X (Sum.inr i)) ∉ I →
      IsAdditivelyFree I →
      IsMultiplicativelyFree I →
      IsRotund I →
      ∃ z : Fin n → ℂ,
        ∀ p ∈ I, MvPolynomial.eval (Sum.elim z (fun i => Complex.exp (z i))) p = 0 := by
  sorry

end OMA.S_wpc_exponential_closedness
