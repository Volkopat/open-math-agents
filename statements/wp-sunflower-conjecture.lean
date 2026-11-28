import Mathlib

/-!
# Sunflower conjecture

Source: https://en.wikipedia.org/wiki/sunflower_(mathematics)
Credit: @ihateSAS

The sunflower conjecture: for every fixed `r > 2` the number of `k`-element sets
needed to force a sunflower (a family of `r` sets whose pairwise intersections
are all equal to one common core) is bounded by an exponential function of `k`,
i.e. there is a constant `C`, depending on `r` only, such that every family of
more than `C ^ k` sets of size `k` contains a sunflower with `r` petals.
-/

namespace OMA.S_wp_sunflower_conjecture

theorem main :
    ∀ r : ℕ, 2 < r → ∃ C : ℕ, ∀ k n : ℕ, ∀ F : Finset (Finset (Fin n)),
      (∀ A ∈ F, A.card = k) → C ^ k < F.card →
        ∃ G : Finset (Finset (Fin n)), G ⊆ F ∧ G.card = r ∧
          ∃ Y : Finset (Fin n), ∀ A ∈ G, ∀ B ∈ G, A ≠ B → A ∩ B = Y := by
  sorry

end OMA.S_wp_sunflower_conjecture
