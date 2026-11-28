import Mathlib

/-!
# Which equations `φ(x) = φ(a x + b)` have solutions

Source: https://mathoverflow.net/questions/488704
Credit: @koolkao

Question (Pooya Farshim, MathOverflow 488704, 2025; CC BY-SA 4.0). For integers `a, b ≥ 0`
consider the equation `φ(x) = φ(a x + b)`, where `φ` is Euler's totient function. Based on
experiments, the source suggests the following pattern:
* `a = 1`: there are solutions for every `b`;
* `a = 2`: there are solutions if and only if `b ≡ 0, 1, 2, 4, 5 (mod 6)`;
* `a = 3`: there are solutions if and only if `b ≡ 1 (mod 2)`;
* `a = 4`: there are solutions if and only if `b ≡ 2, 4 (mod 6)`;
* `a = 5`: there are solutions if and only if `b ≡ 5, 25 (mod 30)`;
* `a ≥ 6`: there are no solutions.
Is this pattern correct?

`main` states that the whole pattern holds. A disproof shows that one of the six claims fails.

Translation choices:
* `a`, `b` and the unknown `x` are natural numbers, and a solution is a positive `x` (for `x = 0`
  the equation reads `0 = φ(b)`, which holds only for `b = 0`);
* `φ` is `Nat.totient`;
* "`b ≡ r₁, …, r_k (mod m)`" is `b % m ∈ {r₁, …, r_k}`;
* the six claims of the source are joined by `∧`.
-/

namespace OMA.S_mo_488704

/-- The equation `φ(x) = φ(a x + b)` has a solution in positive integers `x`. -/
def HasSol (a b : ℕ) : Prop :=
  ∃ x : ℕ, 0 < x ∧ Nat.totient x = Nat.totient (a * x + b)

/-- The pattern of the source for `a = 1, …, 5` and `a ≥ 6`. -/
theorem main :
    (∀ b : ℕ, HasSol 1 b) ∧
      (∀ b : ℕ, HasSol 2 b ↔ b % 6 ∈ ({0, 1, 2, 4, 5} : Finset ℕ)) ∧
      (∀ b : ℕ, HasSol 3 b ↔ b % 2 = 1) ∧
      (∀ b : ℕ, HasSol 4 b ↔ b % 6 ∈ ({2, 4} : Finset ℕ)) ∧
      (∀ b : ℕ, HasSol 5 b ↔ b % 30 ∈ ({5, 25} : Finset ℕ)) ∧
      (∀ a b : ℕ, 6 ≤ a → ¬ HasSol a b) := by
  sorry

end OMA.S_mo_488704
