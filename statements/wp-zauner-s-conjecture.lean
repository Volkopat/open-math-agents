import Mathlib

-- Zauner's conjecture: Weyl–Heisenberg covariant SIC-POVMs exist in every dimension.
-- Source: https://en.wikipedia.org/wiki/SIC-POVM#Zauner's_conjecture (redirect target of
-- Zauner's_conjecture)
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

/-!
The source gives the conjecture in the group-covariant form (citing Renes et al. 2004): with
`ω = exp(2πi/d)` and `D_{j,k} = ω^{jk/2} ∑_m ω^{jm} |k + m mod d⟩⟨m|`, there is `|φ⟩ ∈ ℂ^d` such
that `{D_{j,k} |φ⟩}` (all `j, k` mod `d`) is a SIC-POVM, i.e. the `d^2` rank-one projectors onto
these vectors satisfy `Tr(Π_a Π_b) = (d δ_ab + 1)/(d + 1)`.

Conventions:
* Vectors of `ℂ^d` are functions `ZMod d → ℂ` (coordinates in the basis `|0⟩, ..., |d-1⟩`), with
  the standard inner product `⟪u, v⟫ = ∑ n, conj (u n) * v n`, written out explicitly.
* `D_{j,k}` acts by `(D_{j,k} φ) n = ω^{j (n - k)} φ (n - k)`, which is the source's operator
  without the scalar `ω^{jk/2}`. That scalar has modulus one, so it changes neither the
  rank-one projector onto `D_{j,k} φ` nor any quantity below.
* For unit vectors `u, v` the projectors `|u⟩⟨u|, |v⟩⟨v|` satisfy `Tr(Π_u Π_v) = |⟪u, v⟫|^2`, so
  the SIC condition is: `φ` is a unit vector and `|⟪D_a φ, D_b φ⟫|^2 = 1/(d+1)` for `a ≠ b`
  (each `D_a` is unitary, so every `D_a φ` is then a unit vector).
* Dimensions `d ≥ 2`, as in the source's first formulation (`d = 1` is trivial).
* The source's first formulation also asserts that the fiducial projector commutes with an
  order-three element of the Jacobi group; the source presents the covariant form stated here as
  its restatement, and only that form is formalised.
-/

namespace OMA.S_wp_zauner_s_conjecture

open Complex

/-- The Weyl–Heisenberg displacement `D_{j,k}` on `ℂ^d`, up to the unimodular scalar `ω^{jk/2}`:
`(D_{j,k} φ) n = ω^{j (n - k)} φ (n - k)` with `ω = exp(2πi/d)`. -/
noncomputable def displace (d : ℕ) (j k : ZMod d) (φ : ZMod d → ℂ) : ZMod d → ℂ :=
  fun n => exp (2 * Real.pi * I * ((j * (n - k)).val : ℂ) / d) * φ (n - k)

/-- The standard Hermitian inner product on `ℂ^d`, conjugate-linear in the first argument. -/
noncomputable def herm (d : ℕ) [NeZero d] (u v : ZMod d → ℂ) : ℂ :=
  ∑ n, starRingEnd ℂ (u n) * v n

/-- Zauner's conjecture (covariant form). -/
theorem main : ∀ d : ℕ, 2 ≤ d → ∀ [NeZero d], ∃ φ : ZMod d → ℂ, herm d φ φ = 1 ∧
    ∀ a b : ZMod d × ZMod d, a ≠ b →
      ‖herm d (displace d a.1 a.2 φ) (displace d b.1 b.2 φ)‖ ^ 2 = 1 / ((d : ℝ) + 1) := by
  sorry

end OMA.S_wp_zauner_s_conjecture
