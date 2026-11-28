import OMAReductions.R_RamseyNumbers_ramsey_number_four_five_R1_H1_R1_H3_R1
import Mathlib

/-!
Both eight-vertex graphs (8, 31956160) (dropping vertex 5) and (8, 59227328)
(dropping vertex 7) contain the same UNSAT seven-vertex induced subgraph
(7, 507072). This splits H4 into three independent crossing-clique targets:
H1 for (7, 507072), H2 for (8, 59186376), and H3 for (8, 31960512).
-/

-- Reduction RamseyNumbers.ramsey_number_four_five.R1.H1.R1.H3.R1.H4.R1 of step RamseyNumbers.ramsey_number_four_five.R1.H1.R1.H3.R1.H4
-- Credit: @tkaiman

namespace OMA.R_RamseyNumbers_ramsey_number_four_five_R1_H1_R1_H3_R1_H4_R1

def H1 : Prop :=
  ∀ rows : Fin 7 → Fin 16 → Bool,
    ∃ (c : Bool) (s : Finset (Fin 7)) (t : Finset (Fin 16)),
    s.card + t.card = (if c then 4 else 5) ∧
    (∀ i ∈ s, ∀ j ∈ s, i < j → (507072 : ℕ).testBit (j.val*(j.val-1)/2+i.val) = c) ∧
    (∀ i ∈ t, ∀ j ∈ t, i < j →
      (0xacb96354eb266b51b2b6553699403b : ℕ).testBit (j.val*(j.val-1)/2+i.val) = c) ∧
    ∀ i ∈ s, ∀ j ∈ t, rows i j = c

def H2 : Prop :=
  ∀ rows : Fin 8 → Fin 16 → Bool,
    ∃ (c : Bool) (s : Finset (Fin 8)) (t : Finset (Fin 16)),
    s.card + t.card = (if c then 4 else 5) ∧
    (∀ i ∈ s, ∀ j ∈ s, i < j → (59186376 : ℕ).testBit (j.val*(j.val-1)/2+i.val) = c) ∧
    (∀ i ∈ t, ∀ j ∈ t, i < j →
      (0xacb96354eb266b51b2b6553699403b : ℕ).testBit (j.val*(j.val-1)/2+i.val) = c) ∧
    ∀ i ∈ s, ∀ j ∈ t, rows i j = c

def H3 : Prop :=
  ∀ rows : Fin 8 → Fin 16 → Bool,
    ∃ (c : Bool) (s : Finset (Fin 8)) (t : Finset (Fin 16)),
    s.card + t.card = (if c then 4 else 5) ∧
    (∀ i ∈ s, ∀ j ∈ s, i < j → (31960512 : ℕ).testBit (j.val*(j.val-1)/2+i.val) = c) ∧
    (∀ i ∈ t, ∀ j ∈ t, i < j →
      (0xacb96354eb266b51b2b6553699403b : ℕ).testBit (j.val*(j.val-1)/2+i.val) = c) ∧
    ∀ i ∈ s, ∀ j ∈ t, rows i j = c

lemma lift7to8 (m : ℕ) (e : Fin 7 ↪o Fin 8)
    (hm : ∀ i j : Fin 7, i < j →
      m.testBit ((e j).val * ((e j).val - 1) / 2 + (e i).val) =
      (507072 : ℕ).testBit (j.val * (j.val - 1) / 2 + i.val))
    (h7 : H1)
    (rows : Fin 8 → Fin 16 → Bool) :
    ∃ (c : Bool) (s : Finset (Fin 8)) (t : Finset (Fin 16)),
    s.card + t.card = (if c then 4 else 5) ∧
    (∀ i ∈ s, ∀ j ∈ s, i < j → m.testBit (j.val*(j.val-1)/2+i.val) = c) ∧
    (∀ i ∈ t, ∀ j ∈ t, i < j →
      (0xacb96354eb266b51b2b6553699403b : ℕ).testBit (j.val*(j.val-1)/2+i.val) = c) ∧
    ∀ i ∈ s, ∀ j ∈ t, rows i j = c := by
  obtain ⟨c, s, t, hcard, hs, ht, hcross⟩ := h7 (fun i j => rows (e i) j)
  refine ⟨c, s.map e.toEmbedding, t, ?_, ?_, ht, ?_⟩
  · simpa [Finset.card_map] using hcard
  · intro i hi j hj hij
    rcases Finset.mem_map.mp hi with ⟨i', hi', rfl⟩
    rcases Finset.mem_map.mp hj with ⟨j', hj', rfl⟩
    have hlt : i' < j' := e.lt_iff_lt.mp hij
    exact (hm i' j' hlt).trans (hs i' hi' j' hj' hlt)
  · intro i hi j hj
    rcases Finset.mem_map.mp hi with ⟨i', hi', rfl⟩
    exact hcross i' hi' j hj

theorem main : H1 → H2 → H3 → OMA.R_RamseyNumbers_ramsey_number_four_five_R1_H1_R1_H3_R1.H4 := by
  intro h1 h2 h3 p hp rows
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact lift7to8 31956160 (Fin.succAboveOrderEmb 5) (by decide) h1 rows
  · exact h3 rows
  · exact h2 rows
  · exact lift7to8 59227328 (Fin.succAboveOrderEmb 7) (by decide) h1 rows

end OMA.R_RamseyNumbers_ramsey_number_four_five_R1_H1_R1_H3_R1_H4_R1
