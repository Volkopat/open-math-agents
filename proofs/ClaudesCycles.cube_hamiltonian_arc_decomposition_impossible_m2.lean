import FormalConjectures.Paper.ClaudesCycles
import Mathlib

/-! Generate direction tables, retain walks of period eight, and check the twelve
retained tables for a shared arc among any three.
The previous proof in project PR 224 is credited to @TheWaler. -/

namespace CubeArcCheck
open ClaudesCycles

abbrev Directions := Fin 8 → Fin 3

def vertices (x : Fin 8) (b : Fin 3) : ZMod 2 :=
  (x.val / 2 ^ b.val : ℕ)

def neighbor (x : Fin 8) (b : Fin 3) : Fin 8 :=
  Fin.ofNat 8 (x.val ^^^ (2 ^ b.val))

lemma neighbor_correct : ∀ (x : Fin 8) (b : Fin 3),
    vertices (neighbor x b) = bumpAt b (vertices x) := by decide

lemma origin_unique : ∀ x : Fin 8, vertices x = vertices 0 → x = 0 := by decide

def walk (t : Directions) : ℕ → Fin 8
  | 0 => 0
  | k + 1 => neighbor (walk t k) (t (walk t k))

def words : (n : ℕ) → List (Fin n → Fin 3)
  | 0 => [Fin.elim0]
  | n + 1 => (List.finRange 3).flatMap fun b => (words n).map (Fin.cons b)

lemma mem_words (t : Fin n → Fin 3) : t ∈ words n := by
  induction n with
  | zero => simp [words, Subsingleton.elim t Fin.elim0]
  | succ n ih =>
    simp [words]
    exact ⟨t 0, fun i => t i.succ, ih _, Fin.cons_self_tail t⟩

def cycles : List Directions :=
  (words 8).filter fun t => decide (walk t 8 = 0 ∧ walk t 4 ≠ 0)

def encodedCycles : List Directions :=
  [3792, 2370, 4470, 5532, 1270, 5392, 1168, 4588, 1730, 4268, 2768, 2012].map fun n x =>
    Fin.ofNat 3 (n / 3 ^ x.val)

set_option maxRecDepth 4096 in
lemma cycles_eq : cycles = encodedCycles := by decide +kernel

def overlaps (a b c : Directions) : Bool :=
  decide (∃ x, a x = b x ∨ a x = c x ∨ b x = c x)

set_option maxRecDepth 4096 in
lemma conflict {a b c : Directions} (ha : a ∈ cycles) (hb : b ∈ cycles) (hc : c ∈ cycles) :
    ∃ x, a x = b x ∨ a x = c x ∨ b x = c x := by
  have h : cycles.all (fun i => cycles.all (fun j => cycles.all (overlaps i j))) = true := by
    rw [cycles_eq]
    decide
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp h a ha) b hb) c hc)

lemma in_table {σ : Equiv.Perm (Vertex 2)} {t : Directions}
    (h : ∀ x, σ (vertices x) = vertices (neighbor x (t x)))
    (hcyc : IsDirectedHamiltonianCycle (cubeAdj (m := 2)) σ) : t ∈ cycles := by
  have lift (k : ℕ) : vertices (walk t k) = (σ ^ k) (vertices 0) := by
    induction k with
    | zero => simp [walk]
    | succ k ih => rw [walk, ← h, ih, pow_succ', Equiv.Perm.mul_apply]
  have hord : orderOf σ = 8 := by
    rw [hcyc.2.1.orderOf, hcyc.2.2, Finset.card_univ]
    decide
  have h8 : σ ^ 8 = 1 := hord ▸ pow_orderOf_eq_one σ
  have h4 : vertices 0 ∈ (σ ^ 4).support := by
    rw [hcyc.2.1.support_pow_of_pos_of_lt_orderOf (by decide) (by omega), hcyc.2.2]
    exact Finset.mem_univ _
  refine List.mem_filter.mpr ⟨mem_words t, decide_eq_true ?_⟩
  constructor
  · exact origin_unique _ ((lift 8).trans (by simp [h8]))
  · intro ret
    exact Equiv.Perm.mem_support.mp h4 ((lift 4).symm.trans (congrArg vertices ret))

end CubeArcCheck

open ClaudesCycles CubeArcCheck

theorem OMA.solution : type_of% @ClaudesCycles.cube_hamiltonian_arc_decomposition_impossible_m2 := by
  rintro ⟨σ, hcyc, hcover⟩
  let t (i : Fin 3) (x : Fin 8) := ((hcyc i).1 (vertices x)).choose
  have hstep (i : Fin 3) (x : Fin 8) : σ i (vertices x) = bumpAt (t i x) (vertices x) :=
    ((hcyc i).1 (vertices x)).choose_spec.symm
  have htab (i : Fin 3) : t i ∈ cycles := by
    apply in_table (σ := σ i) _ (hcyc i)
    intro x
    rw [neighbor_correct, hstep]
  have unique {i j : Fin 3} (x : Fin 8) (h : t i x = t j x) : i = j := by
    obtain ⟨c, _, huniq⟩ := hcover (vertices x) (t i x)
    exact (huniq i (hstep i x)).trans (huniq j (h ▸ hstep j x)).symm
  obtain ⟨x, h | h | h⟩ := conflict (htab 0) (htab 1) (htab 2) <;>
    have := unique x h <;> omega
