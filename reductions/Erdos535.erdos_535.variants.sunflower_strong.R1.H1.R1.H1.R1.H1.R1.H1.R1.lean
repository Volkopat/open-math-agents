import OMAReductions.R_Erdos535_erdos_535_variants_sunflower_strong_R1_H1_R1_H1_R1_H1_R1

-- Reduction Erdos20.erdos_20.R1.H2.R1.H1.R1.H1.R1 of step Erdos20.erdos_20.R1.H2.R1.H1.R1.H1
-- Credit: @LordMike
-- Port of reductions/Erdos20.erdos_20.R1.H2.R1.H1.R1.H1.R1.lean by its author onto the identical hypothesis statement Erdos535.erdos_535.variants.sunflower_strong.R1.H1.R1.H1.R1.H1.R1.H1.

/-!
# The non-tree wire metric: tree compression against the border lower bound

Source: OpenAI, *Euclidean geometry in the asymptotic spectrum of tensors* (OpenAI Math Release, Nov 2026),
formalized in Lean 4 in github.com/openai/math (Apache-2.0), `OAI.LinearAlgebra.SpectralBooks.EveryField`.
There `nonTreeWireMetric_every_field` is proved by contradiction: if every spectral point has a tree wire
metric, then (a) Sharp's tree compression (`grid_compress_of_tree`, `uniform_rounds_of_tree`) gives small
arithmetic circuits for the independent-set polynomial of every bipartite graph, while (b) the missing
spectral plane gives a profile shortening (`hasProfileShortening_of_tree`), the companion border-stretch
theorem (`companion_signed_border_stretch`, `OAI.Computability.BorderVNP`) makes the companion's signed
polynomial stretched-exponentially hard in the degree-component border model, and the Hamiltonian-cycle
projection (`hardSubcubicGrids_of_companionPstar`) transfers this to subcubic grids
(`HardSubcubicGrids`). The two sides contradict each other (`hasNonTreeWireMetric_of_hardSubcubicGrids`).

Both hypotheses assume the tree property for every spectral point (encoding of the parent step) and talk
about the same statement `Q`: for every `δ > 0` and every large `N`, the bipartite independent-set polynomial
of every graph on `m + k = N` vertices (two variables per vertex) is the degree-`N` component of the output
of an arithmetic circuit with at most `2 ^ N ^ δ` gates (each gate adds or multiplies two earlier gates or
polynomials of degree at most one).

- `H1` (lower bound, (b)): the tree property refutes `Q`. Exact circuits are a special case of the border
  model, so the companion border lower bound refutes `Q` on the projected subcubic grids.
- `H2` (tree compression, (a)): the tree property implies `Q`.
-/

namespace OMA.R_Erdos535_erdos_535_variants_sunflower_strong_R1_H1_R1_H1_R1_H1_R1_H1_R1

def H1 : Prop :=
 (∀ (J : Type) [Fintype J] [DecidableEq J], let S := Σ d : J → ℕ, (∀ j, Fin (d j)) → ℂ; ∀ Φ : S → ℝ,
 (∀ X, 0 ≤ Φ X) → Φ ⟨fun _ => 1, fun _ => 1⟩ = 1 → (∀ X : S, (∀ z, X.2 z = 0) → Φ X = 0) →
 (∀ X Y : S, ((∃ A : ∀ j, Matrix (Fin (Y.1 j)) (Fin (X.1 j)) ℂ, ∀ y, Y.2 y = ∑ z, (∏ j, A j (y j) (z j)) * X.2 z) → Φ Y ≤ Φ X) ∧
 Φ ⟨fun j => X.1 j * Y.1 j, fun z => X.2 (fun j => (finProdFinEquiv.symm (z j)).1) * Y.2 (fun j => (finProdFinEquiv.symm (z j)).2)⟩ = Φ X * Φ Y ∧
 Φ ⟨fun j => X.1 j + Y.1 j, fun z => if h : ∀ j, (z j : ℕ) < X.1 j then X.2 (fun j => ⟨z j, h j⟩) else if h' : ∀ j, X.1 j ≤ z j then
 Y.2 (fun j => ⟨z j - X.1 j, by have h2 : (z j : ℕ) < X.1 j + Y.1 j := (z j).2; have := h' j; omega⟩) else 0⟩ = Φ X + Φ Y) →
 ∀ a b c e : J, let w := fun s t : J => Real.logb 2 (Φ ⟨fun j => if j = s ∨ j = t then 2 else 1, fun y => if (y s : ℕ) = y t then 1 else 0⟩);
 w a b + w c e ≤ max (w a c + w b e) (w a e + w b c)) →
 ¬ ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℕ in Filter.atTop, ∀ (m k : ℕ) (E : Fin m → Fin k → Bool), m + k = N →
 let R := MvPolynomial ((Fin m ⊕ Fin k) × Bool) ℂ; ∃ (s : ℕ) (g : Fin s → R), (s : ℝ) ≤ 2 ^ (N : ℝ) ^ δ ∧
 (∀ i, ∃ p q : R, (p.totalDegree ≤ 1 ∨ ∃ a < i, p = g a) ∧ (q.totalDegree ≤ 1 ∨ ∃ a < i, q = g a) ∧ (g i = p + q ∨ g i = p * q)) ∧
 ∃ i, MvPolynomial.homogeneousComponent N (g i) = ∑ b : (Fin m → Bool) × (Fin k → Bool), if ∀ x y, E x y = true → b.1 x = true → b.2 y ≠ true
 then (∏ x, (MvPolynomial.X (Sum.inl x, b.1 x) : R)) * ∏ y, MvPolynomial.X (Sum.inr y, b.2 y) else 0

def H2 : Prop :=
 (∀ (J : Type) [Fintype J] [DecidableEq J], let S := Σ d : J → ℕ, (∀ j, Fin (d j)) → ℂ; ∀ Φ : S → ℝ,
 (∀ X, 0 ≤ Φ X) → Φ ⟨fun _ => 1, fun _ => 1⟩ = 1 → (∀ X : S, (∀ z, X.2 z = 0) → Φ X = 0) →
 (∀ X Y : S, ((∃ A : ∀ j, Matrix (Fin (Y.1 j)) (Fin (X.1 j)) ℂ, ∀ y, Y.2 y = ∑ z, (∏ j, A j (y j) (z j)) * X.2 z) → Φ Y ≤ Φ X) ∧
 Φ ⟨fun j => X.1 j * Y.1 j, fun z => X.2 (fun j => (finProdFinEquiv.symm (z j)).1) * Y.2 (fun j => (finProdFinEquiv.symm (z j)).2)⟩ = Φ X * Φ Y ∧
 Φ ⟨fun j => X.1 j + Y.1 j, fun z => if h : ∀ j, (z j : ℕ) < X.1 j then X.2 (fun j => ⟨z j, h j⟩) else if h' : ∀ j, X.1 j ≤ z j then
 Y.2 (fun j => ⟨z j - X.1 j, by have h2 : (z j : ℕ) < X.1 j + Y.1 j := (z j).2; have := h' j; omega⟩) else 0⟩ = Φ X + Φ Y) →
 ∀ a b c e : J, let w := fun s t : J => Real.logb 2 (Φ ⟨fun j => if j = s ∨ j = t then 2 else 1, fun y => if (y s : ℕ) = y t then 1 else 0⟩);
 w a b + w c e ≤ max (w a c + w b e) (w a e + w b c)) →
 ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℕ in Filter.atTop, ∀ (m k : ℕ) (E : Fin m → Fin k → Bool), m + k = N →
 let R := MvPolynomial ((Fin m ⊕ Fin k) × Bool) ℂ; ∃ (s : ℕ) (g : Fin s → R), (s : ℝ) ≤ 2 ^ (N : ℝ) ^ δ ∧
 (∀ i, ∃ p q : R, (p.totalDegree ≤ 1 ∨ ∃ a < i, p = g a) ∧ (q.totalDegree ≤ 1 ∨ ∃ a < i, q = g a) ∧ (g i = p + q ∨ g i = p * q)) ∧
 ∃ i, MvPolynomial.homogeneousComponent N (g i) = ∑ b : (Fin m → Bool) × (Fin k → Bool), if ∀ x y, E x y = true → b.1 x = true → b.2 y ≠ true
 then (∏ x, (MvPolynomial.X (Sum.inl x, b.1 x) : R)) * ∏ y, MvPolynomial.X (Sum.inr y, b.2 y) else 0

theorem main : H1 → H2 → OMA.R_Erdos535_erdos_535_variants_sunflower_strong_R1_H1_R1_H1_R1_H1_R1.H1 := by
 intro h1 h2
 unfold H1 at h1
 unfold H2 at h2
 by_contra hne
 refine (fun t => h1 t (h2 t)) ?_
 intro J _ _ S Φ h0 hu hz h3 a b c e w
 by_contra hlt
 refine hne ?_
 unfold OMA.R_Erdos535_erdos_535_variants_sunflower_strong_R1_H1_R1_H1_R1_H1_R1.H1
 exact ⟨J, inferInstance, inferInstance, Φ, ⟨h0, hu, hz, fun X Y => (h3 X Y).1, fun X Y => (h3 X Y).2.1,
 fun X Y => (h3 X Y).2.2⟩, a, b, c, e, not_le.mp hlt⟩

end OMA.R_Erdos535_erdos_535_variants_sunflower_strong_R1_H1_R1_H1_R1_H1_R1_H1_R1
