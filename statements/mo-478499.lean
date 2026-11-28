import Mathlib

/-!
# Character positivity for Robinson's centralizer count

For a finite group and a prime p, the class function vanishing on p-singular
elements and counting p-elements of the centralizer at p-regular elements is
conjectured to be an ordinary complex character.

[MathOverflow question](https://mathoverflow.net/questions/478499/is-this-generalized-character-always-a-character)
[Robinson's paper](https://arxiv.org/abs/2505.03976)
-/

namespace OMA.S_mo_478499

noncomputable def centralizerCount {G : Type*} [Group G] (p : ℕ) (y : G) : ℂ :=
  if p ∣ orderOf y then 0
  else Nat.card {x : G // Commute x y ∧ ∃ k : ℕ, orderOf x = p ^ k}

theorem main :
    ∀ (G : Type) [Group G] [Fintype G], ∀ p : ℕ, Nat.Prime p →
      ∃ (n : ℕ) (ρ : Representation ℂ G (Fin n → ℂ)),
        ∀ y : G, ρ.character y = centralizerCount p y := by
  sorry

end OMA.S_mo_478499
