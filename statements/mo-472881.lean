import Mathlib

/-!
# Polynomial interpolation on subgroup orbits

Source: Shaoyun Bai, https://mathoverflow.net/questions/472881 (CC BY-SA 4.0).
Credit: @connoranderson.

In coordinates the symmetric algebra in the author's clarification is the
multivariate polynomial ring. Vít Tuček observed that finite Lagrange
interpolation gives the first two conditions at a fixed vector. For the
last condition we require each individual coefficient to agree with an
ambient polynomial on the admissible locus, with no uniform degree bound.
-/

namespace OMA.S_mo_472881

abbrev V (d : ℕ) := Fin d → ℂ
abbrev P (d : ℕ) := MvPolynomial (Fin d) ℂ

variable {G : Type} [Group G] {d : ℕ}

def Admissible (ρ : Representation ℂ G (V d)) (H : Subgroup G) (v : V d) : Prop :=
  ∀ g : G, ρ g v = v → g ∈ H

def Selects (ρ : Representation ℂ G (V d)) (H : Subgroup G) (v : V d) (p : P d) : Prop :=
  (∀ g ∈ H, MvPolynomial.eval (ρ g v) p = 1) ∧
  (∀ g ∉ H, MvPolynomial.eval (ρ g v) p = 0)

theorem main : ∀ (G : Type) [Group G] [Fintype G] (d : ℕ)
    (ρ : Representation ℂ G (V d)) (H : Subgroup G) (v : V d),
    Function.Injective ρ → H ≠ ⊤ → Admissible ρ H v →
    (∃ p : P d, Selects ρ H v p) ∧
    ¬ ∃ p : V d → P d, (∀ x, Admissible ρ H x → Selects ρ H x (p x)) ∧
      ∀ m : Fin d →₀ ℕ, ∃ c : P d, ∀ x, Admissible ρ H x →
        MvPolynomial.coeff m (p x) = MvPolynomial.eval x c := by
  sorry

end OMA.S_mo_472881
