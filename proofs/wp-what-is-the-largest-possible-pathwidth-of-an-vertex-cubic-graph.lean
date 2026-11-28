import OMAStatements.S_wp_what_is_the_largest_possible_pathwidth_of_an_vertex_cubic_graph
import Mathlib

/-!
The statement asks only for the existence of a maximum function, so we take the
supremum of the set of attained widths. The set is bounded above by `n` (one bag
containing every vertex) and nonempty because a cubic graph exists on `Fin (m + m)`
for `m ≥ 2`: the Moebius ladder, `i ~ i ± 1` and `i ~ i + m` modulo `m + m`.
-/

namespace OMA.S_wp_what_is_the_largest_possible_pathwidth_of_an_vertex_cubic_graph

/-- The Moebius ladder on `m + m` vertices, written without modular arithmetic. -/
def cub (m : ℕ) : SimpleGraph (Fin (m + m)) :=
  SimpleGraph.mk
    (fun u v => u.val + 1 = v.val ∨ v.val + 1 = u.val ∨ (u.val = 0 ∧ v.val + 1 = m + m) ∨
      (v.val = 0 ∧ u.val + 1 = m + m) ∨ v.val = u.val + m ∨ u.val = v.val + m)
    (by refine ⟨fun u v h => ?_⟩; omega)
    (by
      refine ⟨fun u h => ?_⟩
      have := u.isLt
      omega)

theorem cub_adj (m : ℕ) (u v : Fin (m + m)) :
    (cub m).Adj u v ↔ (u.val + 1 = v.val ∨ v.val + 1 = u.val ∨ (u.val = 0 ∧ v.val + 1 = m + m) ∨
      (v.val = 0 ∧ u.val + 1 = m + m) ∨ v.val = u.val + m ∨ u.val = v.val + m) := Iff.rfl

theorem cub_regular (m : ℕ) (hm : 2 ≤ m) [(cub m).LocallyFinite] :
    (cub m).IsRegularOfDegree 3 := by
  intro u
  have hu := u.isLt
  rw [← SimpleGraph.card_neighborFinset_eq_degree, Finset.card_eq_three]
  refine ⟨⟨if u.val + 1 < m + m then u.val + 1 else 0, by split_ifs <;> omega⟩,
    ⟨if u.val = 0 then m + m - 1 else u.val - 1, by split_ifs <;> omega⟩,
    ⟨if u.val < m then u.val + m else u.val - m, by split_ifs <;> omega⟩, ?_, ?_, ?_, ?_⟩
  · rw [Ne, Fin.ext_iff]; dsimp only; split_ifs <;> omega
  · rw [Ne, Fin.ext_iff]; dsimp only; split_ifs <;> omega
  · rw [Ne, Fin.ext_iff]; dsimp only; split_ifs <;> omega
  · ext w
    have hw := w.isLt
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert, Finset.mem_singleton,
      cub_adj, Fin.ext_iff]
    split_ifs <;> omega

theorem univ_bag {n : ℕ} (G : SimpleGraph (Fin n)) : HasPathwidthAtMost G n := by
  refine ⟨0, fun _ => Finset.univ, fun v => ⟨0, Finset.mem_univ v⟩,
    fun u v _ => ⟨0, Finset.mem_univ u, Finset.mem_univ v⟩,
    fun _ _ _ v _ _ _ _ => Finset.mem_univ v, fun _ => ?_⟩
  simp

end OMA.S_wp_what_is_the_largest_possible_pathwidth_of_an_vertex_cubic_graph

open OMA.S_wp_what_is_the_largest_possible_pathwidth_of_an_vertex_cubic_graph in
theorem OMA.solution :
    type_of% @OMA.S_wp_what_is_the_largest_possible_pathwidth_of_an_vertex_cubic_graph.main := by
  classical
  refine ⟨fun n => sSup {width : ℕ | IsCubicPathwidth n width}, fun n hn he => ?_⟩
  have hbdd : BddAbove {width : ℕ | IsCubicPathwidth n width} := by
    refine ⟨n, fun w hw => ?_⟩
    obtain ⟨G, -, hG⟩ := hw
    exact hG.2 (univ_bag G)
  have hne : {width : ℕ | IsCubicPathwidth n width}.Nonempty := by
    obtain ⟨m, rfl⟩ := he
    have hex : ∃ w, HasPathwidthAtMost (cub m) w := ⟨m + m, univ_bag _⟩
    refine ⟨Nat.find hex, cub m, cub_regular m (by omega), Nat.find_spec hex, ?_⟩
    intro w hw
    exact Nat.find_min' hex hw
  exact ⟨Nat.sSup_mem hne hbdd, fun w hw => le_csSup hbdd hw⟩
