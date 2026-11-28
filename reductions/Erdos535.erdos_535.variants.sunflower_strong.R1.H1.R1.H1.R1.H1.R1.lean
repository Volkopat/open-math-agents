import OMAReductions.R_Erdos535_erdos_535_variants_sunflower_strong_R1_H1_R1_H1_R1

-- Reduction Erdos535.erdos_535.variants.sunflower_strong.R1.H1.R1.H1.R1.H1.R1 of step Erdos535.erdos_535.variants.sunflower_strong.R1.H1.R1.H1.R1.H1
-- Credit: @my-other-github-account
-- Split and hypothesis texts reused verbatim from Erdos20.erdos_20.R1.H2.R1.H1.R1 by @JamesSlash (PR 6976).

/-!
# The planar spectral point: non-tree wire metric, diagonal price laws, flat law

Source: OpenAI, *Euclidean geometry in the asymptotic spectrum of tensors* and *An exponential bound for
sunflowers* (OpenAI Math Release, Nov 2026), formalized in Lean 4 in github.com/openai/math (Apache-2.0).
There the target is `OAI.Combinatorics.Sunflower.exists_planar_point`. It is proved from
`matrix_spectral_plane = exists_jointly_convex_spectral_plane (nonTreeWireMetric_every_field F)` (the
spectral tree-or-plane alternative) and from `SpectralPlacementPrices.flatDiagonalLaw_isometry`, which
rests on the purely geometric `OAI.LinearAlgebra.SpectralBooks.flatDiagonalLaw`. The split below
follows that proof.

Tensors on a finite site type are encoded as in the parent step: `⟨d, T⟩` with local dimensions `d j`
and coefficients `T : (∀ j, Fin (d j)) → ℂ`. A spectral point is nonnegative, sends the unit to 1 and
zero tensors to 0, is monotone under restriction (one matrix per site), multiplicative under the
Kronecker product and additive under the direct sum. The wire distance `w s t` of a spectral point is the
binary log-price of one shared bit (the 2-dimensional diagonal) between the sites `s` and `t`
(`SiteTensor.rawWireDistance φ 1`).

- `H1` (algebraic side, `HasNonTreeWireMetric ℂ`): some spectral point on finitely many sites has a wire
  distance that violates the four-point condition of tree metrics. In OpenAI's proof this comes from a
  border-complexity lower bound (`OAI.Computability.BorderVNP`).
- `H2` (spectral geometry, `exists_jointly_convex_spectral_plane`, `jointlyConvexDiagonal_of_raw`,
  `exists_point_diagonal_map`): one four-point defect gives a Euclidean spectral plane, through the CAT(0)
  geodesic realization of the spectrum. The binary diagonal price `δ` of finite planar sets satisfies the
  diagonal price laws (`DiagonalPriceLawsOn univ δ`: monotone, intersecting submodular, jointly convex,
  `δ {p, q} = dist p q`, triangle bound by the half perimeter). Every finite planar placement carries one
  spectral point whose one-bit prices are the ratios of `δ`.
- `H3` (Euclidean geometry, `flatDiagonalLaw` with `C = univ`): in the plane, the diagonal price laws
  force `δ` to be the normalized Gaussian mean width `√(2π) 𝔼 max_{p ∈ S} ⟨u, p⟩`.
-/

namespace OMA.R_Erdos535_erdos_535_variants_sunflower_strong_R1_H1_R1_H1_R1_H1_R1

def H1 : Prop :=
  ∃ (J : Type) (_ : Fintype J) (_ : DecidableEq J) (Φ : (Σ d : J → ℕ, (∀ j, Fin (d j)) → ℂ) → ℝ),
    ((∀ X, 0 ≤ Φ X) ∧ Φ ⟨fun _ => 1, fun _ => 1⟩ = 1 ∧
      (∀ X : Σ d : J → ℕ, (∀ j, Fin (d j)) → ℂ, (∀ z, X.2 z = 0) → Φ X = 0) ∧
      (∀ X Y : Σ d : J → ℕ, (∀ j, Fin (d j)) → ℂ,
        (∃ A : ∀ j, Matrix (Fin (Y.1 j)) (Fin (X.1 j)) ℂ,
          ∀ y, Y.2 y = ∑ z, (∏ j, A j (y j) (z j)) * X.2 z) → Φ Y ≤ Φ X) ∧
      (∀ X Y : Σ d : J → ℕ, (∀ j, Fin (d j)) → ℂ,
        Φ ⟨fun j => X.1 j * Y.1 j, fun z => X.2 (fun j => (finProdFinEquiv.symm (z j)).1) *
          Y.2 (fun j => (finProdFinEquiv.symm (z j)).2)⟩ = Φ X * Φ Y) ∧
      (∀ X Y : Σ d : J → ℕ, (∀ j, Fin (d j)) → ℂ,
        Φ ⟨fun j => X.1 j + Y.1 j, fun z =>
          if h : ∀ j, (z j : ℕ) < X.1 j then X.2 (fun j => ⟨z j, h j⟩)
          else if h' : ∀ j, X.1 j ≤ z j then
            Y.2 (fun j => ⟨z j - X.1 j, by have h2 : (z j : ℕ) < X.1 j + Y.1 j := (z j).2; have := h' j; omega⟩)
          else 0⟩ = Φ X + Φ Y)) ∧
    ∃ a b c e : J,
      let w := fun s t : J => Real.logb 2 (Φ ⟨fun j => if j = s ∨ j = t then 2 else 1,
        fun y => if (y s : ℕ) = y t then 1 else 0⟩);
      max (w a c + w b e) (w a e + w b c) < w a b + w c e

def H2 : Prop :=
 let P : ∀ (J : Type) [Fintype J] [DecidableEq J], ((Σ d : J → ℕ, (∀ j, Fin (d j)) → ℂ) → ℝ) → Prop :=
  fun J _ _ Φ => (∀ X, 0 ≤ Φ X) ∧ Φ ⟨fun _ => 1, fun _ => 1⟩ = 1 ∧ (∀ X : Σ d : J → ℕ, (∀ j, Fin (d j)) → ℂ, (∀ z, X.2 z = 0) → Φ X = 0) ∧
   (∀ X Y : Σ d : J → ℕ, (∀ j, Fin (d j)) → ℂ, (∃ A : ∀ j, Matrix (Fin (Y.1 j)) (Fin (X.1 j)) ℂ,
     ∀ y, Y.2 y = ∑ z, (∏ j, A j (y j) (z j)) * X.2 z) → Φ Y ≤ Φ X) ∧
   (∀ X Y : Σ d : J → ℕ, (∀ j, Fin (d j)) → ℂ, Φ ⟨fun j => X.1 j * Y.1 j, fun z => X.2 (fun j => (finProdFinEquiv.symm (z j)).1) *
     Y.2 (fun j => (finProdFinEquiv.symm (z j)).2)⟩ = Φ X * Φ Y) ∧
   (∀ X Y : Σ d : J → ℕ, (∀ j, Fin (d j)) → ℂ, Φ ⟨fun j => X.1 j + Y.1 j, fun z =>
     if h : ∀ j, (z j : ℕ) < X.1 j then X.2 (fun j => ⟨z j, h j⟩)
     else if h' : ∀ j, X.1 j ≤ z j then
      Y.2 (fun j => ⟨z j - X.1 j, by have h2 : (z j : ℕ) < X.1 j + Y.1 j := (z j).2; have := h' j; omega⟩)
     else 0⟩ = Φ X + Φ Y)
 ∀ (J : Type) [Fintype J] [DecidableEq J] (Φ : (Σ d : J → ℕ, (∀ j, Fin (d j)) → ℂ) → ℝ) (a b c e : J),
  P J Φ → (let w := fun s t : J => Real.logb 2 (Φ ⟨fun j => if j = s ∨ j = t then 2 else 1,
   fun y => if (y s : ℕ) = y t then 1 else 0⟩); max (w a c + w b e) (w a e + w b c) < w a b + w c e) →
  ∃ δ : Finset (EuclideanSpace ℝ (Fin 2)) → ℝ, Monotone δ ∧ (∀ A B : Finset (EuclideanSpace ℝ (Fin 2)), (A ∩ B).Nonempty → δ (A ∪ B) + δ (A ∩ B) ≤ δ A + δ B) ∧
   (∀ Q : Finset (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)), ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → s + t = 1 → δ (Q.image fun q => s • q.1 + t • q.2) ≤ s * δ (Q.image Prod.fst) + t * δ (Q.image Prod.snd)) ∧
   (∀ p q, δ {p, q} = dist p q) ∧ (∀ p q r, δ {p, q, r} ≤ (dist p q + dist q r + dist r p) / 2) ∧
   ∀ (I : Type) [Fintype I] [DecidableEq I] [Nontrivial I] (x : I ↪ EuclideanSpace ℝ (Fin 2)),
    ∃ Ψ, P I Ψ ∧ ∀ (S : Finset I) (hS : S.Nonempty), Real.logb 2 (Ψ ⟨fun i => if i ∈ S then 2 else 1, fun z => if ∀ i ∈ S, ∀ j ∈ S, (z i : ℕ) = z j then 1 else 0⟩) = δ (S.image x) / δ (Finset.univ.image x)

def H3 : Prop :=
  ∀ δ : Finset (EuclideanSpace ℝ (Fin 2)) → ℝ, Monotone δ →
    (∀ A B : Finset (EuclideanSpace ℝ (Fin 2)), (A ∩ B).Nonempty → δ (A ∪ B) + δ (A ∩ B) ≤ δ A + δ B) →
    (∀ Q : Finset (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)),
      ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → s + t = 1 →
        δ (Q.image fun q => s • q.1 + t • q.2) ≤ s * δ (Q.image Prod.fst) + t * δ (Q.image Prod.snd)) →
    (∀ p q, δ {p, q} = dist p q) →
    (∀ p q r, δ {p, q, r} ≤ (dist p q + dist q r + dist r p) / 2) →
    ∀ (S : Finset (EuclideanSpace ℝ (Fin 2))) (hS : S.Nonempty),
      δ S = Real.sqrt (2 * Real.pi) *
        ∫ u, S.sup' hS (fun p => inner ℝ u p) ∂ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin 2))

theorem main : H1 → H2 → H3 → OMA.R_Erdos535_erdos_535_variants_sunflower_strong_R1_H1_R1_H1_R1.H1 := by
  intro hA hB hC I _ _ _ x
  obtain ⟨J, _, _, Φ, hΦ, a, b, c, e, hv⟩ := hA
  obtain ⟨δ, h1, h2, h3, h4, h5, h6⟩ := hB J Φ a b c e hΦ hv
  obtain ⟨Ψ, ⟨g1, g2, g3, g4, g5, g6⟩, g7⟩ := h6 I x
  refine ⟨Ψ, g1, g2, g3, g4, g5, g6, fun S hS => ?_⟩
  rw [g7 S hS, hC δ h1 h2 h3 h4 h5 _ (hS.image x),
    hC δ h1 h2 h3 h4 h5 _ (Finset.univ_nonempty.image x),
    mul_div_mul_left _ _ (Real.sqrt_ne_zero'.mpr (by positivity))]
  simp_rw [Finset.sup'_image]
  rfl

end OMA.R_Erdos535_erdos_535_variants_sunflower_strong_R1_H1_R1_H1_R1_H1_R1
