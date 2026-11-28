import OMAReductions.R_Erdos23_erdos_23_variants_n5_R2_H2_R1
import Mathlib

/-!
Reduction of the order-22 bound to the order-21 bound and an enumeration
of edge-maximal triangle-free graphs of minimum degree at least four.
The numbers 16 and 17 are the order-21 and order-22 entries in McKay's
extremal bipartization table (OEIS A389646). No catalogue is assumed checked.
We reuse the vertex extension lemma in the ancestor reduction by @steveDOTdigital;
the order-23 reduction by @marcusbuffett uses the same maximal-extension idea.
-/

namespace OMA.R_Erdos23_erdos_23_variants_n5_R2_H2_R1_H1_R1

open Finset SimpleGraph
open scoped Classical

def H1 : Prop :=
  ∀ (G : SimpleGraph (Fin 25)), G.CliqueFree 3 → ∀ W : Finset (Fin 25),
    W.card = 21 → ∃ c : Fin 25 → Bool,
      (∑ i ∈ W, ∑ j ∈ W, if G.Adj i j ∧ c i = c j then 1 else 0) ≤ (32 : ℕ)

def H2 : Prop :=
  ∀ (W : Finset (Fin 25)), W.card = 22 → ∀ K : SimpleGraph (Fin 25),
    K.CliqueFree 3 → (∀ i j, K.Adj i j → i ∈ W ∧ j ∈ W) →
    (∀ H : SimpleGraph (Fin 25), K ≤ H → H.CliqueFree 3 →
      (∀ i j, H.Adj i j → i ∈ W ∧ j ∈ W) → H = K) →
    (∀ i ∈ W, 4 ≤ (W.filter (K.Adj i)).card) →
    ∃ c : Fin 25 → Bool,
      (∑ i ∈ W, ∑ j ∈ W, if K.Adj i j ∧ c i = c j then 1 else 0) ≤ (34 : ℕ)

theorem main : H1 → H2 → OMA.R_Erdos23_erdos_23_variants_n5_R2_H2_R1.H1 := by
  classical
  intro smaller core G triangle W size
  by_cases low : ∃ v ∈ W, (W.filter (G.Adj v)).card ≤ 3
  · obtain ⟨v, member, bound⟩ := low
    obtain ⟨color, oldCost⟩ := smaller G triangle (W.erase v)
      (by rw [card_erase_of_mem member, size])
    let weight (i j : Fin 25) : ℕ := if G.Adj i j then 1 else 0
    have costEq (U : Finset (Fin 25)) (f : Fin 25 → Bool) :
        (∑ i ∈ U, ∑ j ∈ U, if f i = f j then weight i j else 0) =
        ∑ i ∈ U, ∑ j ∈ U, if G.Adj i j ∧ f i = f j then 1 else 0 := by
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro j _
      by_cases h : f i = f j <;> simp [weight, h]
    obtain ⟨f, estimate⟩ := OMA.R_Erdos23_erdos_23_variants_n5_R2.extend_color
      W member weight (fun i j => by simp only [weight, G.adj_comm i j])
      (fun i => by simp [weight]) color
    rw [costEq, costEq] at estimate
    have degree : (∑ j ∈ W.erase v, weight v j) ≤ 3 := by
      change (∑ j ∈ W.erase v, if G.Adj v j then 1 else 0) ≤ 3
      rw [← card_filter]
      exact (card_le_card (filter_subset_filter _ (erase_subset v W))).trans bound
    exact ⟨f, by omega⟩
  · let restricted : SimpleGraph (Fin 25) := {
      Adj := fun i j => G.Adj i j ∧ i ∈ W ∧ j ∈ W
      symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
      loopless := ⟨fun i h => (G.loopless.irrefl i) h.1⟩ }
    let admissible (K : SimpleGraph (Fin 25)) :=
      K.CliqueFree 3 ∧ ∀ i j, K.Adj i j → i ∈ W ∧ j ∈ W
    have start : admissible restricted :=
      ⟨triangle.anti (show restricted ≤ G from fun _ _ h => h.1), fun _ _ h => h.2⟩
    obtain ⟨K, hsub, maximal⟩ := Finite.exists_le_maximal (p := admissible) start
    have keep {i j} (hi : i ∈ W) (hj : j ∈ W) (edge : G.Adj i j) : K.Adj i j :=
      hsub ⟨edge, hi, hj⟩
    have minDegree (i) (hi : i ∈ W) : 4 ≤ (W.filter (K.Adj i)).card := by
      have original : 4 ≤ (W.filter (G.Adj i)).card := by
        by_contra! small
        exact low ⟨i, hi, by omega⟩
      apply original.trans
      apply card_le_card
      intro j h
      obtain ⟨hj, edge⟩ := mem_filter.mp h
      exact mem_filter.mpr ⟨hj, keep hi hj edge⟩
    obtain ⟨c, hc⟩ := core W size K maximal.1.1 maximal.1.2
      (fun H sub cf supported => le_antisymm (maximal.2 ⟨cf, supported⟩ sub) sub)
      minDegree
    refine ⟨c, le_trans ?_ hc⟩
    apply sum_le_sum
    intro i hi
    apply sum_le_sum
    intro j hj
    by_cases h : G.Adj i j ∧ c i = c j
    · simp [h.1, keep hi hj h.1, h.2]
    · simp [h]

end OMA.R_Erdos23_erdos_23_variants_n5_R2_H2_R1_H1_R1
