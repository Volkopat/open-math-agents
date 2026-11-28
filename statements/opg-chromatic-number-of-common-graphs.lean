import Mathlib

/-!
# Chromatic Number of Common Graphs

Source: https://www.openproblemgarden.org/op/chromatic_number_of_common_graphs
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

A graph `H` is common if the number of copies of `H` in a graph `G` plus the number in the
complement of `G` is asymptotically minimised by the random graph. Question (Hatami, Hladký,
Král', Norine, Razborov): do common graphs have bounded chromatic number?

Conventions:
* Graphs `H` are finite simple graphs. Following [HHKNR], `H` is common iff
  `t(H, W) + t(H, 1 - W) ≥ 2 ^ (1 - e(H))` for every graphon `W`, where `t` is the homomorphism
  density. Step graphons are dense in the cut norm and `t(H, ·)` is cut-norm continuous, so it
  is equivalent to ask this for step graphons only: symmetric matrices `W : Fin n → Fin n → [0,1]`
  (any `n ≥ 1`, diagonal entries allowed), with
  `t(H, W) = n ^ (-v(H)) ∑_{φ : V(H) → Fin n} ∏_{uv ∈ E(H)} W (φ u) (φ v)`.
* The source asks a yes/no question; `main` states the answer yes, and a disproof would answer
  no.
-/

namespace OMA.S_opg_chromatic_number_of_common_graphs

/-- A step graphon with `n` steps: a symmetric `[0,1]`-valued matrix. -/
structure StepGraphon (n : ℕ) where
  W : Fin n → Fin n → ℝ
  symm : ∀ i j, W i j = W j i
  nonneg : ∀ i j, 0 ≤ W i j
  le_one : ∀ i j, W i j ≤ 1

/-- The complementary step graphon `1 - W`. -/
def StepGraphon.compl {n : ℕ} (W : StepGraphon n) : StepGraphon n where
  W i j := 1 - W.W i j
  symm i j := by rw [W.symm]
  nonneg i j := by linarith [W.le_one i j]
  le_one i j := by linarith [W.nonneg i j]

/-- The homomorphism density `t(H, W)`. -/
noncomputable def homDensity {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj] {n : ℕ} (W : StepGraphon n) : ℝ :=
  (∑ φ : V → Fin n, ∏ e ∈ H.edgeFinset,
      Sym2.lift ⟨fun a b => W.W (φ a) (φ b), fun a b => W.symm (φ a) (φ b)⟩ e) /
    (n : ℝ) ^ Fintype.card V

/-- `H` is common. -/
def IsCommon {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj] :
    Prop :=
  ∀ (n : ℕ) (W : StepGraphon n), 0 < n →
    (2 : ℝ) ^ (1 - (H.edgeFinset.card : ℤ)) ≤ homDensity H W + homDensity H W.compl

/-- Common graphs have bounded chromatic number. -/
theorem main : ∃ C : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    [DecidableRel H.Adj], IsCommon H → H.chromaticNumber ≤ C := by
  sorry

end OMA.S_opg_chromatic_number_of_common_graphs
