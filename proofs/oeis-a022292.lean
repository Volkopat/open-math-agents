import OMAStatements.S_oeis_a022292
import Mathlib

open OMA.S_oeis_a022292 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a022292.main) := by
  intro h
  let K : ℕ → ℕ := fun _ => 0
  have hr (i : ℕ) : runStart K i = 0 := by
    induction i with
    | zero => rfl
    | succ i ih => simp [runStart, K, ih]
  have hk : IsKolakoski K := by
    intro i j _ hj
    rw [hr] at hj
    omega
  have he : {m : ℕ | Balanced K m} = ∅ := by
    ext m
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    intro hm
    have hpos := hm.1
    have hm' := hm.2
    simp [K] at hm'
    omega
  have hi := (h K hk).1
  rw [he] at hi
  exact hi Set.finite_empty