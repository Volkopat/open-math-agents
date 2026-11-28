import Mathlib

/-!
# On sums of three squares

Source: https://mathoverflow.net/questions/322271 (Zhi-Wei Sun, CC BY-SA 4.0).

By the Gauss–Legendre theorem every `n ∈ ℕ` with `n ≡ 1, 2 (mod 4)` is `x² + y² + z²` with
`x, y, z ∈ ℕ`, and one of `x, y, z` has the parity of `n`.
Conjecture (Sun, 2009). Let `N_1 = 14617`, `N_2 = 15618`, `N_3 = 25582`. Then for each
`i ∈ {1, 2, 3}`, every integer `n > N_i` with `n ≡ 1, 2 (mod 4)` can be written as
`x_1² + x_2² + x_3²` with `x_1, x_2, x_3 ∈ ℕ`, `x_1 ≤ x_2 ≤ x_3`, and `x_i ≡ n (mod 2)`.

Formalization notes:
* The three cases `i = 1, 2, 3` are stated as three conjuncts, with the ordered triple written
  `x₁ ≤ x₂ ≤ x₃`.
* Checked numerically: each case holds for `N_i < n ≤ 40000`, and each `N_i` itself is an
  exception (so the thresholds are sharp, confirming the reading of the index `i`).
-/

namespace OMA.S_mo_322271

/-- `n` is `x₁² + x₂² + x₃²` with `x₁ ≤ x₂ ≤ x₃` and the `i`-th of them of the parity of `n`. -/
def Rep (n : ℕ) (parity : ℕ → ℕ → ℕ → Prop) : Prop :=
  ∃ x₁ x₂ x₃ : ℕ, x₁ ≤ x₂ ∧ x₂ ≤ x₃ ∧ x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2 = n ∧ parity x₁ x₂ x₃

/-- Sun's conjecture, for `i = 1, 2, 3`. -/
theorem main :
    (∀ n : ℕ, 14617 < n → (n % 4 = 1 ∨ n % 4 = 2) →
      Rep n (fun x₁ _ _ => x₁ % 2 = n % 2)) ∧
    (∀ n : ℕ, 15618 < n → (n % 4 = 1 ∨ n % 4 = 2) →
      Rep n (fun _ x₂ _ => x₂ % 2 = n % 2)) ∧
    (∀ n : ℕ, 25582 < n → (n % 4 = 1 ∨ n % 4 = 2) →
      Rep n (fun _ _ x₃ => x₃ % 2 = n % 2)) := by
  sorry

end OMA.S_mo_322271
