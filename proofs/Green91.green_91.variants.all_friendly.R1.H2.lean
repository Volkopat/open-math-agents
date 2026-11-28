import OMAReductions.R_Green91_green_91_variants_all_friendly_R1
import Mathlib

/-! Deleting the last vertex of `G(n + 1, 1/2)` gives `G(n, 1/2)`. Every graph on `Fin n` has
probability `2 ^ (-(n choose 2))`, and a graph on `Fin (n + 1)` is the same thing as a graph on
`Fin n` together with the neighbourhood of the last vertex, a map `Fin n → Bool`. So the event
`P (G.comap Fin.castSucc)` has `2 ^ n` times as many graphs, each `2 ^ n` times less likely. -/

namespace OMA.Step_Green91_green_91_variants_all_friendly_R1_H2

open Green91 MeasureTheory SimpleGraph
open scoped Classical

instance (V : Type*) [Countable V] : MeasurableSingletonClass (SimpleGraph V) := by
  constructor
  intro G
  have h : ({G} : Set (SimpleGraph V)) = SimpleGraph.Adj ⁻¹' {G.Adj} := by
    ext H
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    exact ⟨fun h => h ▸ rfl, fun h => SimpleGraph.ext h⟩
  rw [h]
  exact measurable_adj (measurableSet_singleton _)

/-- Every graph on `Fin n` has probability `(1/2) ^ (n choose 2)`. -/
theorem prob_eq (n : ℕ) (P : SimpleGraph (Fin n) → Prop) :
    prob n P = ((Finset.univ.filter P).card : ENNReal) * (2⁻¹ : ENNReal) ^ (n.choose 2) := by
  have hset : {G | P G} = ((Finset.univ.filter P : Finset (SimpleGraph (Fin n))) :
      Set (SimpleGraph (Fin n))) := by
    ext G; simp
  unfold prob
  rw [hset, ← sum_measure_singleton]
  have hone : ∀ G : SimpleGraph (Fin n),
      binomialRandom (Fin n) ⟨1 / 2, by norm_num⟩ {G} = (2⁻¹ : ENNReal) ^ (n.choose 2) := by
    intro G
    rw [binomialRandom_singleton]
    have hp' : unitInterval.toNNReal ⟨1 / 2, by norm_num⟩ = (2⁻¹ : NNReal) :=
      NNReal.eq (by show (1 / 2 : ℝ) = ((2⁻¹ : NNReal) : ℝ); push_cast; norm_num)
    have hq' : unitInterval.toNNReal (unitInterval.symm ⟨1 / 2, by norm_num⟩) = (2⁻¹ : NNReal) :=
      NNReal.eq (by show (1 - 1 / 2 : ℝ) = ((2⁻¹ : NNReal) : ℝ); push_cast; norm_num)
    have hp : ((unitInterval.toNNReal ⟨1 / 2, by norm_num⟩ : NNReal) : ENNReal) = 2⁻¹ := by
      rw [hp', ENNReal.coe_inv two_ne_zero]; rfl
    have hq : ((unitInterval.toNNReal (unitInterval.symm ⟨1 / 2, by norm_num⟩) : NNReal) :
        ENNReal) = 2⁻¹ := by
      rw [hq', ENNReal.coe_inv two_ne_zero]; rfl
    rw [hp, hq, ← pow_add, Nat.card_eq_fintype_card, Fintype.card_fin]
    congr 1
    have hle : G.edgeSet.ncard ≤ n.choose 2 := by
      rw [Set.ncard_eq_toFinset_card', Set.toFinset_card]
      have := G.card_edgeFinset_le_card_choose_two
      rw [Fintype.card_fin] at this
      simpa [SimpleGraph.edgeFinset, Set.toFinset_card] using this
    omega
  simp only [hone, Finset.sum_const, nsmul_eq_mul]

/-- The graph on `Fin (n + 1)` with `G` on `Fin n` and last-vertex neighbourhood `f`. -/
def extG {n : ℕ} (G : SimpleGraph (Fin n)) (f : Fin n → Bool) : SimpleGraph (Fin (n + 1)) where
  Adj x y := Fin.lastCases (Fin.lastCases False (fun j => f j = true) y)
    (fun i => Fin.lastCases (f i = true) (fun j => G.Adj i j) y) x
  symm := ⟨by
    intro x y h
    induction x using Fin.lastCases with
    | last =>
      induction y using Fin.lastCases with
      | last => simp at h
      | cast j => simpa using h
    | cast i =>
      induction y using Fin.lastCases with
      | last => simpa using h
      | cast j => simpa using (show G.Adj i j by simpa using h).symm⟩
  loopless := ⟨by
    intro x h
    induction x using Fin.lastCases with
    | last => simp at h
    | cast i => simp at h⟩

/-- Graphs on `Fin (n + 1)` are graphs on `Fin n` plus the neighbourhood of the last vertex. -/
noncomputable def splitEquiv (n : ℕ) : SimpleGraph (Fin (n + 1)) ≃ SimpleGraph (Fin n) × (Fin n → Bool) where
  toFun G := (G.comap Fin.castSucc, fun i => decide (G.Adj i.castSucc (Fin.last n)))
  invFun x := extG x.1 x.2
  left_inv G := by
    ext x y
    induction x using Fin.lastCases with
    | last =>
      induction y using Fin.lastCases with
      | last => simp [extG]
      | cast j => simp [extG, G.adj_comm]
    | cast i =>
      induction y using Fin.lastCases with
      | last => simp [extG]
      | cast j => simp [extG]
  right_inv x := by
    obtain ⟨G, f⟩ := x
    refine Prod.ext ?_ ?_
    · ext i j; simp [extG]
    · funext i; simp [extG]

theorem card_comap (n : ℕ) (P : SimpleGraph (Fin n) → Prop) :
    (Finset.univ.filter (fun G : SimpleGraph (Fin (n + 1)) => P (G.comap Fin.castSucc))).card =
      (Finset.univ.filter P).card * 2 ^ n := by
  have hmap : (Finset.univ.filter (fun G : SimpleGraph (Fin (n + 1)) =>
      P (G.comap Fin.castSucc))).map (splitEquiv n).toEmbedding =
      (Finset.univ.filter P) ×ˢ (Finset.univ : Finset (Fin n → Bool)) := by
    ext ⟨G, f⟩
    simp only [Finset.mem_map_equiv, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_product, and_true]
    rw [show ((splitEquiv n).symm (G, f)) = extG G f from rfl]
    rw [show (extG G f).comap Fin.castSucc = G by ext i j; simp [extG]]
  rw [← Finset.card_map (splitEquiv n).toEmbedding, hmap, Finset.card_product,
    Finset.card_univ]
  simp

end OMA.Step_Green91_green_91_variants_all_friendly_R1_H2

open OMA.Step_Green91_green_91_variants_all_friendly_R1_H2 in
theorem OMA.solution : OMA.R_Green91_green_91_variants_all_friendly_R1.H2 := by
  classical
  intro n P
  rw [prob_eq, prob_eq, card_comap, Nat.choose_succ_succ, Nat.choose_one_right, pow_add]
  push_cast
  have h2 : (2 : ENNReal) ^ n * (2⁻¹ : ENNReal) ^ n = 1 := by
    rw [← mul_pow, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow]
  calc ((Finset.univ.filter P).card : ENNReal) * 2 ^ n * ((2⁻¹ : ENNReal) ^ n *
        (2⁻¹ : ENNReal) ^ n.choose 2)
      = ((Finset.univ.filter P).card : ENNReal) * (2 ^ n * (2⁻¹ : ENNReal) ^ n) *
        (2⁻¹ : ENNReal) ^ n.choose 2 := by ring
    _ = _ := by rw [h2, mul_one]
