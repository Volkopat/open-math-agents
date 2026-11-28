import Mathlib

/-!
# Interlacing sequences by polynomials?

Source: https://mathoverflow.net/questions/334885 (Turbo, CC BY-SA 4.0).
Credit: @connoranderson

For weakly ordered lists, repeated nodes preclude strict interlacing. For distinct
nodes the two integer interpolants can have degree at most t-1 with the displayed
coefficient bound. For every power of two t ≥ 4 the explicit lower-bound family needs
degree at least t/2-1, independently of coefficient heights. This disproves the
proposed uniform fixed polylogarithmic degree, even for M linear in t.
-/

namespace OMA.S_mo_334885
open Polynomial
def interlaces {t : ℕ} (a b : Fin t → ℤ) (f g : ℤ[X]) : Prop :=
  (∀ i, f.eval (a i) < g.eval (b i)) ∧ ∀ i j, i < j → g.eval (b i) < f.eval (a j)
def heightBound (t : ℕ) (M : ℤ) : ℤ :=
  (t:ℤ)*(2*(t:ℤ)+1)*(M+1)^(4*t*t+t)

theorem main :
    (∀ (t : ℕ) (M : ℤ), 1 ≤ M → ∀ a b : Fin t → ℤ,
      Monotone a → Monotone b → (∀ i, 0 < a i ∧ a i < M) → (∀ i, 0 < b i ∧ b i < M) →
      ((∃ f g : ℤ[X], interlaces a b f g) ↔ StrictMono a ∧ StrictMono b) ∧
      (StrictMono a → StrictMono b → ∃ f g : ℤ[X], interlaces a b f g ∧
        max f.natDegree g.natDegree ≤ t-1 ∧
        ∀ k, max |f.coeff k| |g.coeff k| ≤ heightBound t M)) ∧
    ∀ ℓ : ℕ, let s := 2^ℓ
      ∃ a b : Fin (4*s) → ℤ, StrictMono a ∧ StrictMono b ∧
        (∀ i, 0 < a i ∧ a i < 6*(s:ℤ)+1) ∧ (∀ i, 0 < b i ∧ b i < 6*(s:ℤ)+1) ∧
        ∀ f g : ℤ[X], interlaces a b f g → 2*s-1 ≤ max f.natDegree g.natDegree := by
  sorry
end OMA.S_mo_334885
