import Mathlib

/-!
# Subgroups of SO(2n, ℂ) all of whose elements have an eigenvalue ±1

Source: https://mathoverflow.net/questions/199635
Asked by MathOverflow user curious.

The question first asks whether some subgroup of `GL(n, ℂ)` has the property that every
element has the eigenvalue `1` while there is no common eigenvector with eigenvalue `1`;
after `SO(n, ℂ)` was pointed out, the asker states the actual problem: if `G ⊂ SO(2n, ℂ)`
has the property that every element of `G` has an eigenvalue `±1`, is there a common
eigenvector with eigenvalue `±1` for the elements of `G`?

This file formalizes that actual problem.

Translation choices.
* `ℂ^{2n}` is `ι → ℂ` for a finite type `ι` with an even number of elements, and `G` is a
  subgroup of `GL ι ℂ`; `G ⊂ SO(2n, ℂ)` means that every element `g` satisfies
  `gᵀ * g = 1` (complex orthogonal, with the plain transpose) and `det g = 1`.
* An element `g` has an eigenvalue `±1` when `g v = v` or `g v = -v` for some nonzero `v`.
* A common eigenvector with eigenvalue `±1` is a nonzero `v` such that every `g ∈ G`
  satisfies `g v = v` or `g v = -v` (the sign may depend on `g`).
* `main` is the affirmative answer. The further question at the end of the post (about
  irreducible subgroups for small `n`) is not formalized here.
-/

namespace OMA.S_mo_199635

open Matrix

theorem main :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι], Even (Fintype.card ι) →
      ∀ G : Subgroup (GL ι ℂ),
        (∀ g ∈ G, (g : Matrix ι ι ℂ)ᵀ * (g : Matrix ι ι ℂ) = 1 ∧
          (g : Matrix ι ι ℂ).det = 1) →
        (∀ g ∈ G, ∃ v : ι → ℂ, v ≠ 0 ∧
          ((g : Matrix ι ι ℂ) *ᵥ v = v ∨ (g : Matrix ι ι ℂ) *ᵥ v = -v)) →
        ∃ v : ι → ℂ, v ≠ 0 ∧ ∀ g ∈ G,
          (g : Matrix ι ι ℂ) *ᵥ v = v ∨ (g : Matrix ι ι ℂ) *ᵥ v = -v := by
  sorry

end OMA.S_mo_199635
