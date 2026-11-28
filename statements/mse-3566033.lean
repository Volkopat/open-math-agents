import Mathlib

/-!
# Baer ring $R$ with $R / J(R)$ not Baer

Source: https://math.stackexchange.com/questions/3566033/is-there-an-example-of-a-baer-ring-r-for-which-r-jr-is-not-baer
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Is there a (unital) Baer ring $R$ such that the quotient $R / J(R)$ of $R$ by its Jacobson
radical $J(R)$ is not Baer?

Conventions:
- A ring $R$ is Baer if for every nonempty subset $X \subseteq R$, its right annihilator
  $\{a \in R \mid \forall x \in X, x a = 0\}$ equals $e R$ for some idempotent $e = e^2 \in R$.
- The quotient $R / J(R)$ is characterized as the codomain of a surjective ring homomorphism
  $\varphi : R \to S$ whose kernel is the Jacobson radical $\{x \in R \mid \forall r \in R,
  \mathrm{IsUnit}(1 - r x)\}$.
-/

namespace OMA.S_mse_3566033

/-- A unital ring is Baer if the right annihilator of every nonempty subset is generated
as a right ideal by an idempotent. -/
def IsBaer (R : Type*) [Ring R] : Prop :=
  ∀ X : Set R, X.Nonempty →
    ∃ e : R, e * e = e ∧
      {a : R | ∀ x ∈ X, x * a = 0} = {a : R | ∃ r : R, a = e * r}

/-- `φ : R →+* S` realizes `S` as the quotient of `R` by its Jacobson radical `J(R)`. -/
def IsJacobsonQuotient {R S : Type*} [Ring R] [Ring S] (φ : R →+* S) : Prop :=
  Function.Surjective φ ∧ ∀ x : R, φ x = 0 ↔ ∀ r : R, IsUnit (1 - r * x)

theorem main :
    ∃ (R S : Type) (_ : Ring R) (_ : Ring S) (φ : R →+* S),
      IsBaer R ∧ IsJacobsonQuotient φ ∧ ¬ IsBaer S := by
  sorry

end OMA.S_mse_3566033
