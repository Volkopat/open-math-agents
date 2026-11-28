import FormalConjectures.ErdosProblems.«22»

open Filter SimpleGraph
open scoped Classical

namespace OMA.R_Erdos22_erdos_22_variants_fox_loh_zhao_R1

/-- The geometric input, with a quantitative edge deficit and two triangle-free parts. -/
def H1 : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ (n : ℕ) in atTop,
    ∃ (G : SimpleGraph (Fin n)) (side : Fin n → Bool),
      let budget := C * (Real.log (Real.log n)) ^ (3 / 2 : ℝ) /
        (Real.log n) ^ (1 / 2 : ℝ) * n
      G.CliqueFree 4 ∧ (∀ b, G.CliqueFreeOn {v | side v = b} 3) ∧
      (∀ b, n ≤ 3 * (Finset.univ.filter fun v => side v = b).card) ∧
      (G.indepNum : ℝ) ≤ budget ∧
      (n : ℝ) ^ 2 / 8 - budget * n ≤ G.edgeFinset.card

/-- A single improvement replaces the neighbors of a minimum-degree vertex by the other part. -/
def H2 : Prop :=
  ∀ (n : ℕ) (_ : 0 < n) (G : SimpleGraph (Fin n)) (side : Fin n → Bool),
    G.CliqueFree 4 → (∀ b, G.CliqueFreeOn {v | side v = b} 3) →
    (∀ b, n ≤ 3 * (Finset.univ.filter fun v => side v = b).card) →
    (G.edgeFinset.card : ℝ) < (n : ℝ) ^ 2 / 8 →
    ∃ H : SimpleGraph (Fin n),
      H.CliqueFree 4 ∧ (∀ b, H.CliqueFreeOn {v | side v = b} 3) ∧
      H.indepNum ≤ G.indepNum + 1 ∧
      (G.edgeFinset.card : ℝ) + (n : ℝ) / 12 ≤ H.edgeFinset.card

/-- Stop at the target density, or gain at least `n / 12` edges at each iteration. -/
lemma iterateImprovement (step : H2) {n : ℕ} (hn : 0 < n)
    (G : SimpleGraph (Fin n)) (side : Fin n → Bool)
    (hfree : G.CliqueFree 4) (htri : ∀ b, G.CliqueFreeOn {v | side v = b} 3)
    (hparts : ∀ b, n ≤ 3 * (Finset.univ.filter fun v => side v = b).card) (k : ℕ) :
    ∃ H : SimpleGraph (Fin n), H.CliqueFree 4 ∧
      (∀ b, H.CliqueFreeOn {v | side v = b} 3) ∧ H.indepNum ≤ G.indepNum + k ∧
      min ((n : ℝ) ^ 2 / 8) ((G.edgeFinset.card : ℝ) + (k : ℝ) * n / 12) ≤
        H.edgeFinset.card := by
  induction k with
  | zero =>
    refine ⟨G, hfree, htri, by simp, ?_⟩
    simpa using min_le_right ((n : ℝ) ^ 2 / 8) (G.edgeFinset.card : ℝ)
  | succ k ih =>
    obtain ⟨J, hjfree, hjtri, hjindep, hjedges⟩ := ih
    by_cases hdone : (n : ℝ) ^ 2 / 8 ≤ J.edgeFinset.card
    · exact ⟨J, hjfree, hjtri, by omega, (min_le_left _ _).trans hdone⟩
    · have hprevious : (G.edgeFinset.card : ℝ) + (k : ℝ) * n / 12 ≤
          J.edgeFinset.card := (min_le_iff.mp hjedges).resolve_left hdone
      obtain ⟨H, hhfree, hhtri, hhindep, hhedges⟩ :=
        step n hn J side hjfree hjtri hparts (lt_of_not_ge hdone)
      refine ⟨H, hhfree, hhtri, by omega, (min_le_right _ _).trans ?_⟩
      push_cast
      linarith only [hprevious, hhedges]

theorem main : H1 → H2 → type_of% @Erdos22.erdos_22.variants.fox_loh_zhao := by
  intro seed step
  obtain ⟨C, hC, hseed⟩ := seed
  refine ⟨14 * C, by positivity, ?_⟩
  filter_upwards [hseed, eventually_ge_atTop (1 : ℕ)] with n hgraph hn
  obtain ⟨G, side, hfree, htri, hparts, hindep, hedges⟩ := hgraph
  let budget := C * (Real.log (Real.log n)) ^ (3 / 2 : ℝ) /
    (Real.log n) ^ (1 / 2 : ℝ) * n
  change (G.indepNum : ℝ) ≤ budget at hindep
  change (n : ℝ) ^ 2 / 8 - budget * n ≤ G.edgeFinset.card at hedges
  have hnpos : 0 < n := hn
  have hnreal : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  let v : Fin n := ⟨0, hnpos⟩
  have hsingleton : G.IsIndepSet (↑({v} : Finset (Fin n)) : Set (Fin n)) := by simp
  have hone : 1 ≤ G.indepNum := by simpa using hsingleton.card_le_indepNum
  have hbudget : 1 ≤ budget := (by exact_mod_cast hone : (1 : ℝ) ≤ G.indepNum).trans hindep
  let k := ⌈12 * budget⌉₊
  have hk : 12 * budget ≤ (k : ℝ) := Nat.le_ceil _
  have hk' : (k : ℝ) < 12 * budget + 1 := Nat.ceil_lt_add_one (by linarith)
  have hgain := mul_le_mul_of_nonneg_right hk hnreal
  obtain ⟨H, hhfree, _, hhindep, hhedges⟩ :=
    iterateImprovement step hnpos G side hfree htri hparts k
  have htarget : (n : ℝ) ^ 2 / 8 ≤ (G.edgeFinset.card : ℝ) + (k : ℝ) * n / 12 := by
    linarith only [hedges, hgain]
  rw [min_eq_left htarget] at hhedges
  refine ⟨H, hhfree, ?_, hhedges⟩
  have hhindep' : (H.indepNum : ℝ) ≤ G.indepNum + (k : ℝ) := by exact_mod_cast hhindep
  calc
    (H.indepNum : ℝ) ≤ 14 * budget := by linarith only [hhindep', hindep, hk', hbudget]
    _ = _ := by dsimp only [budget]; ring

end OMA.R_Erdos22_erdos_22_variants_fox_loh_zhao_R1
