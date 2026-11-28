import OMAReductions.R_Erdos20_erdos_20_R1_H2_R1_H1_R1_H1_R1
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.Data.Nat.Log

-- Reduction Erdos20.erdos_20.R1.H2.R1.H1.R1.H1.R1.H1.R1 of step Erdos20.erdos_20.R1.H2.R1.H1.R1.H1.R1.H1

/-!
# Splitting the tree-case lower bound into crossing shortening, border stretch, and Hamiltonian projection

Splits the lower-bound step `Erdos20.erdos_20.R1.H2.R1.H1.R1.H1.R1.H1` along the three independent
stages of OpenAI (Nov 24, 2026), *Euclidean geometry in the asymptotic spectrum of tensors* and its
companion *BorderVNP* (`hasProfileShortening_of_tree`, `paidIdentity_of_profile`,
`companion_signed_border_stretch`, and `IndependentSetGraph.hardSubcubicGrids_of_companionPstar`):

- `H1` (spectral geometry to 2D paid crossing identity): if every finite-site complex spectral point
  has a tree wire metric, then for some positive bit width `m` the 2D antipodal equality tensor is
  realized by a finite sum of `L` Euclidean unit-disk bit-cable networks whose individual wire-length
  cost plus selector cost `4 * clog 2 L` is strictly less than `4 * m`.
- `H2` (border-VNP diagonalization and Hamiltonian transfer): any such 2D paid crossing identity
  over `ℂ` implies the existence of a polynomial-order sequence of homogeneous degree-`n` polynomials
  `f n` projecting from the directed Hamiltonian-cycle polynomial of order `j n ≥ 2` whose degree-`n`
  arithmetic circuit complexity grows at least as `2 ^ (n ^ ε)` for some `ε > 0`.
- `H3` (Hamiltonian-to-independent-set projection): any such stretched-exponentially hard family of
  projected Hamiltonian-cycle polynomials refutes the universal stretched-subexponential circuit
  upper bound `Q` for bipartite independent-set polynomials.
-/

namespace OMA.R_Erdos20_erdos_20_R1_H2_R1_H1_R1_H1_R1_H1_R1

open scoped Classical

def H1 : Prop :=
 (∀ (J : Type) [Fintype J] [DecidableEq J], let S := Σ d : J → ℕ, (∀ j, Fin (d j)) → ℂ; ∀ Φ : S → ℝ,
 (∀ X, 0 ≤ Φ X) → Φ ⟨fun _ => 1, fun _ => 1⟩ = 1 → (∀ X : S, (∀ z, X.2 z = 0) → Φ X = 0) →
 (∀ X Y : S, ((∃ A : ∀ j, Matrix (Fin (Y.1 j)) (Fin (X.1 j)) ℂ, ∀ y, Y.2 y = ∑ z, (∏ j, A j (y j) (z j)) * X.2 z) → Φ Y ≤ Φ X) ∧
 Φ ⟨fun j => X.1 j * Y.1 j, fun z => X.2 (fun j => (finProdFinEquiv.symm (z j)).1) * Y.2 (fun j => (finProdFinEquiv.symm (z j)).2)⟩ = Φ X * Φ Y ∧
 Φ ⟨fun j => X.1 j + Y.1 j, fun z => if h : ∀ j, (z j : ℕ) < X.1 j then X.2 (fun j => ⟨z j, h j⟩) else if h' : ∀ j, X.1 j ≤ z j then
 Y.2 (fun j => ⟨z j - X.1 j, by have h2 : (z j : ℕ) < X.1 j + Y.1 j := (z j).2; have := h' j; omega⟩) else 0⟩ = Φ X + Φ Y) →
 ∀ a b c e : J, let w := fun s t : J => Real.logb 2 (Φ ⟨fun j => if j = s ∨ j = t then 2 else 1, fun y => if (y s : ℕ) = y t then 1 else 0⟩);
 w a b + w c e ≤ max (w a c + w b e) (w a e + w b c)) →
 ∃ (m L : ℕ) (cap : ℝ) (nv ne : Fin L → ℕ) (src dst : ∀ a, Fin (ne a) → Fin (nv a))
 (width : ∀ a, Fin (ne a) → ℕ) (attach : ∀ a, Fin 2 × Bool → Fin (nv a))
 (pos : ∀ a, Fin (nv a) → EuclideanSpace ℝ (Fin 2))
 (tbl : ∀ a (v : Fin (nv a)), (∀ e : {e : Fin (ne a) // src a e = v ∨ dst a e = v}, Fin (width a e.1) → Bool) →
 (∀ p : {p : Fin 2 × Bool // attach a p = v}, Fin m → Bool) → ℂ),
 0 < m ∧ (∀ a v, ‖pos a v‖ ≤ 1) ∧
 (∀ a p, pos a (attach a p) = if p.2 then -EuclideanSpace.single p.1 1 else EuclideanSpace.single p.1 1) ∧
 (∀ a, ∑ e : Fin (ne a), (width a e : ℝ) * dist (pos a (src a e)) (pos a (dst a e)) ≤ cap) ∧
 cap + 4 * (Nat.clog 2 L : ℝ) < 4 * (m : ℝ) ∧
 ∀ x : Fin 2 × Bool → Fin m → Bool, (if ∀ i : Fin 2, x (i, false) = x (i, true) then (1 : ℂ) else 0) =
 ∑ a : Fin L, ∑ z : ∀ e : Fin (ne a), Fin (width a e) → Bool, ∏ v : Fin (nv a), tbl a v (fun e => z e.1) (fun p => x p.1)

def H2 : Prop :=
 (∃ (m L : ℕ) (cap : ℝ) (nv ne : Fin L → ℕ) (src dst : ∀ a, Fin (ne a) → Fin (nv a))
 (width : ∀ a, Fin (ne a) → ℕ) (attach : ∀ a, Fin 2 × Bool → Fin (nv a))
 (pos : ∀ a, Fin (nv a) → EuclideanSpace ℝ (Fin 2))
 (tbl : ∀ a (v : Fin (nv a)), (∀ e : {e : Fin (ne a) // src a e = v ∨ dst a e = v}, Fin (width a e.1) → Bool) →
 (∀ p : {p : Fin 2 × Bool // attach a p = v}, Fin m → Bool) → ℂ),
 0 < m ∧ (∀ a v, ‖pos a v‖ ≤ 1) ∧
 (∀ a p, pos a (attach a p) = if p.2 then -EuclideanSpace.single p.1 1 else EuclideanSpace.single p.1 1) ∧
 (∀ a, ∑ e : Fin (ne a), (width a e : ℝ) * dist (pos a (src a e)) (pos a (dst a e)) ≤ cap) ∧
 cap + 4 * (Nat.clog 2 L : ℝ) < 4 * (m : ℝ) ∧
 ∀ x : Fin 2 × Bool → Fin m → Bool, (if ∀ i : Fin 2, x (i, false) = x (i, true) then (1 : ℂ) else 0) =
 ∑ a : Fin L, ∑ z : ∀ e : Fin (ne a), Fin (width a e) → Bool, ∏ v : Fin (nv a), tbl a v (fun e => z e.1) (fun p => x p.1)) →
 ∃ (ε : ℝ) (A b : ℕ) (j : ℕ → ℕ) (f : ∀ n, MvPolynomial (Fin n × Bool) ℂ),
 0 < ε ∧ 0 < A ∧ 0 < b ∧ (∀ n, 2 ≤ j n) ∧ (∀ n, (f n).IsHomogeneous n) ∧
 (∀ᶠ n : ℕ in Filter.atTop, j n ≤ A * n ^ b) ∧
 (∀ n, ∃ p : Fin (j n) × Fin (j n) → (Fin n × Bool) ⊕ ℂ,
 f n = MvPolynomial.aeval (fun e => Sum.elim MvPolynomial.X MvPolynomial.C (p e))
 (∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin (j n)) => σ.IsCycleOn Set.univ),
 ∏ i : Fin (j n), (MvPolynomial.X (i, σ i) : MvPolynomial (Fin (j n) × Fin (j n)) ℂ))) ∧
 ∀ᶠ n : ℕ in Filter.atTop, ∀ (s : ℕ) (g : Fin s → MvPolynomial (Fin n × Bool) ℂ),
 (∀ i, ∃ p q : MvPolynomial (Fin n × Bool) ℂ, (p.totalDegree ≤ 1 ∨ ∃ a < i, p = g a) ∧
 (q.totalDegree ≤ 1 ∨ ∃ a < i, q = g a) ∧ (g i = p + q ∨ g i = p * q)) →
 (∃ i, MvPolynomial.homogeneousComponent n (g i) = f n) → (2 : ℝ) ^ (n : ℝ) ^ ε ≤ (s : ℝ)

def H3 : Prop :=
 (∃ (ε : ℝ) (A b : ℕ) (j : ℕ → ℕ) (f : ∀ n, MvPolynomial (Fin n × Bool) ℂ),
 0 < ε ∧ 0 < A ∧ 0 < b ∧ (∀ n, 2 ≤ j n) ∧ (∀ n, (f n).IsHomogeneous n) ∧
 (∀ᶠ n : ℕ in Filter.atTop, j n ≤ A * n ^ b) ∧
 (∀ n, ∃ p : Fin (j n) × Fin (j n) → (Fin n × Bool) ⊕ ℂ,
 f n = MvPolynomial.aeval (fun e => Sum.elim MvPolynomial.X MvPolynomial.C (p e))
 (∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin (j n)) => σ.IsCycleOn Set.univ),
 ∏ i : Fin (j n), (MvPolynomial.X (i, σ i) : MvPolynomial (Fin (j n) × Fin (j n)) ℂ))) ∧
 ∀ᶠ n : ℕ in Filter.atTop, ∀ (s : ℕ) (g : Fin s → MvPolynomial (Fin n × Bool) ℂ),
 (∀ i, ∃ p q : MvPolynomial (Fin n × Bool) ℂ, (p.totalDegree ≤ 1 ∨ ∃ a < i, p = g a) ∧
 (q.totalDegree ≤ 1 ∨ ∃ a < i, q = g a) ∧ (g i = p + q ∨ g i = p * q)) →
 (∃ i, MvPolynomial.homogeneousComponent n (g i) = f n) → (2 : ℝ) ^ (n : ℝ) ^ ε ≤ (s : ℝ)) →
 ¬ ∀ δ : ℝ, 0 < δ → ∀ᶠ N : ℕ in Filter.atTop, ∀ (m k : ℕ) (E : Fin m → Fin k → Bool), m + k = N →
 let R := MvPolynomial ((Fin m ⊕ Fin k) × Bool) ℂ; ∃ (s : ℕ) (g : Fin s → R), (s : ℝ) ≤ 2 ^ (N : ℝ) ^ δ ∧
 (∀ i, ∃ p q : R, (p.totalDegree ≤ 1 ∨ ∃ a < i, p = g a) ∧ (q.totalDegree ≤ 1 ∨ ∃ a < i, q = g a) ∧ (g i = p + q ∨ g i = p * q)) ∧
 ∃ i, MvPolynomial.homogeneousComponent N (g i) = ∑ b : (Fin m → Bool) × (Fin k → Bool), if ∀ x y, E x y = true → b.1 x = true → b.2 y ≠ true
 then (∏ x, (MvPolynomial.X (Sum.inl x, b.1 x) : R)) * ∏ y, MvPolynomial.X (Sum.inr y, b.2 y) else 0

theorem main : H1 → H2 → H3 → OMA.R_Erdos20_erdos_20_R1_H2_R1_H1_R1_H1_R1.H1 := by
  intro h1 h2 h3 htree
  exact h3 (h2 (h1 htree))

end OMA.R_Erdos20_erdos_20_R1_H2_R1_H1_R1_H1_R1_H1_R1
