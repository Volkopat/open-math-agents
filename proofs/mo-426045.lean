import OMAStatements.S_mo_426045

-- Problem: Conditions ensuring that a compact set can be approximated by approximating its distance function
-- Upstream: formal-conjectures statements/mo-426045.lean:0 (declaration OMA.S_mo_426045.main)
-- Credit: @amtamaddon (the owner of the agent is credited as the solver)


open Metric Set

namespace OMA.Aux426045

variable {X : Type} [MetricSpace X]

noncomputable def F (K : Set X) (δ : ℝ) : X → ℝ := fun y => max (infDist y K - δ) 0

lemma F_lip (K : Set X) (δ : ℝ) : LipschitzWith 1 (F K δ) := by
  apply LipschitzWith.of_le_add
  intro x y
  have h := infDist_le_infDist_add_dist (s := K) (x := x) (y := y)
  have h1 : infDist y K - δ ≤ max (infDist y K - δ) 0 := le_max_left _ _
  have h2 : (0 : ℝ) ≤ max (infDist y K - δ) 0 := le_max_right _ _
  have h3 : (0 : ℝ) ≤ dist x y := dist_nonneg
  unfold F
  exact max_le (by linarith) (by linarith)

lemma F_nonneg (K : Set X) (δ : ℝ) (y : X) : 0 ≤ F K δ y := le_max_right _ _

lemma F_err (K : Set X) {δ : ℝ} (hδ : 0 ≤ δ) (x : X) : |F K δ x - infDist x K| ≤ δ := by
  have h0 : 0 ≤ infDist x K := infDist_nonneg
  unfold F
  rw [abs_le]
  rcases max_cases (infDist x K - δ) 0 with ⟨h, _⟩ | ⟨h, h'⟩ <;> rw [h] <;> constructor <;> linarith

lemma F_zero (K : Set X) {δ : ℝ} (hδ : 0 ≤ δ) {y : X} (hy : y ∈ K) : F K δ y = 0 := by
  unfold F
  rw [infDist_zero_of_mem hy]
  exact max_eq_right (by linarith)

lemma coreA (K : Set X) {s ε : ℝ} (hs : 0 ≤ s) (hε : 0 < ε) {x : X} (hx : infDist x K < s + ε) :
    ∃ δ : ℝ, 0 ≤ δ ∧ δ < ε ∧ F K δ x ≤ s := by
  refine ⟨max (infDist x K - s) 0, le_max_right _ _, max_lt (by linarith) hε, ?_⟩
  have h1 : infDist x K - s ≤ max (infDist x K - s) 0 := le_max_left _ _
  unfold F
  exact max_le (by linarith) hs

lemma coreB (K : Set X) {s ε : ℝ} {f : X → ℝ} (hU : OMA.S_mo_426045.UniformError K ε f) {x : X}
    (hx : f x ≤ s) : infDist x K < s + ε := by
  obtain ⟨δ, hδ, h⟩ := hU
  have := abs_le.mp (h x)
  linarith [this.1, this.2]

lemma safe_iff (K Y : Set X) {s ε : ℝ} (hs : 0 ≤ s) (hε : 0 < ε) :
    OMA.S_mo_426045.Safe K Y s ε ↔ {x | infDist x K < s + ε} ⊆ Y := by
  constructor
  · intro hS x hx
    obtain ⟨δ, h0, hδ, hF⟩ := coreA K hs hε hx
    exact hS (F K δ) (F_lip K δ).continuous.lowerSemicontinuous (F_nonneg K δ)
      ⟨δ, hδ, F_err K h0⟩ ⟨x, hF⟩ hF
  · intro h f _ _ hU _ y hy
    exact h (coreB K hU hy)

end OMA.Aux426045

open OMA.Aux426045 in
theorem OMA.solution : type_of% @OMA.S_mo_426045.main := by
  intro X _ K s ε hs hε
  refine ⟨?_, ?_, ?_⟩
  · intro x
    constructor
    · intro hx
      obtain ⟨δ, h0, hδ, hF⟩ := coreA K hs hε hx
      exact ⟨F K δ, F_lip K δ, F_nonneg K δ, fun y hy => F_zero K h0 hy, ⟨δ, hδ, F_err K h0⟩, hF⟩
    · rintro ⟨f, _, _, _, hU, hx⟩
      exact coreB K hU hx
  · intro Y
    exact safe_iff K Y hs hε
  · intro Y r hr
    have h := safe_iff K Y (s := r / 2) (ε := r / 2) (by linarith) (by linarith)
    rw [add_halves] at h
    exact h
