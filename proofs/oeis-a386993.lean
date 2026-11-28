import OMAStatements.S_oeis_a386993
import Mathlib.Data.List.SplitBy

/-!
# The squarefree specialization of the divisor-block identity

The proof counts the actual runs of List.splitBy. Their first elements
are precisely the divisors d with 2j<d for every smaller divisor j.
An even divisor d has its half among those earlier divisors. For an odd
divisor the strict inequality is equivalent to the weak one in Hoft's
characterization. This proves the equality for all positive integers.

Hartmut F. W. Hoft, proof in https://oeis.org/A379288 (2025).
Google DeepMind, AlphaProof Nexus, A237271 Conjecture 2 (2026).
Source: https://oeis.org/A386993. Credit: @Solitude1312
-/

open OMA.S_oeis_a386993

namespace OMA.A386993

private abbrev starts (D : Finset ℕ) (d : ℕ) : Prop :=
  ∀ j ∈ D, j < d → 2 * j < d

/-- The run currently being built accounts for one part. A later entry
adds a new part precisely when its predecessor is less than half of it. -/
private lemma remaining_count (D : Finset ℕ) (xs : List ℕ) (b : ℕ)
    (run : List ℕ) (acc : List (List ℕ)) (hb : b ∈ D)
    (inside : ∀ j ∈ xs, j ∈ D) (cover : ∀ j ∈ D, j ≤ b ∨ j ∈ xs)
    (order : (b :: xs).Pairwise (· < ·)) :
    (List.splitBy.loop (fun d e : ℕ => decide (e ≤ 2 * d)) xs b run acc).length =
      acc.length + 1 + xs.countP (fun d => decide (starts D d)) := by
  induction xs generalizing b run acc with
  | nil => simp [List.splitBy.loop]
  | cons d tail ih =>
    obtain ⟨before, htail⟩ := List.pairwise_cons.mp order
    have hbd : b < d := before d (by simp)
    have hd : d ∈ D := inside d (by simp)
    have hinside : ∀ j ∈ tail, j ∈ D := fun j hj => inside j (by simp [hj])
    have hcover : ∀ j ∈ D, j ≤ d ∨ j ∈ tail := by
      intro j hj
      rcases cover j hj with h | h
      · exact Or.inl (by omega)
      · rcases List.mem_cons.mp h with rfl | h
        · exact Or.inl (by omega)
        · exact Or.inr h
    have criterion : starts D d ↔ 2 * b < d := by
      constructor
      · intro hs
        exact hs b hb hbd
      · intro h j hj hjd
        rcases cover j hj with hle | hmem
        · omega
        · rcases List.mem_cons.mp hmem with rfl | ht
          · omega
          · have := (List.pairwise_cons.mp htail).1 j ht
            omega
    have next_count (r : List ℕ) (completed : List (List ℕ)) :=
      ih d r completed hd hinside hcover htail
    rw [List.splitBy.loop, List.countP_cons]
    by_cases small : d ≤ 2 * b
    · have hs : ¬ starts D d := fun h => (not_lt_of_ge small) (criterion.mp h)
      simp [small, hs, next_count]
    · have hs : starts D d := criterion.mpr (by omega)
      simp [small, next_count]
      rw [if_pos hs]
      omega

private lemma count_starts (D : Finset ℕ) :
    (D.sort.splitBy (fun d e => decide (e ≤ 2 * d))).length =
      D.sort.countP (fun d => decide (starts D d)) := by
  let L := D.sort
  have hsort : L.Pairwise (· < ·) := D.sortedLT_sort.pairwise
  have mem (j : ℕ) : j ∈ L ↔ j ∈ D := by simp [L]
  change (L.splitBy _).length = L.countP _
  cases hL : L with
  | nil => simp
  | cons d tail =>
    rw [hL] at hsort mem
    have hd : d ∈ D := (mem d).mp (by simp)
    have hi : ∀ j ∈ tail, j ∈ D := fun j hj => (mem j).mp (by simp [hj])
    have hc : ∀ j ∈ D, j ≤ d ∨ j ∈ tail := by
      intro j hj
      rcases List.mem_cons.mp ((mem j).mpr hj) with rfl | h
      · exact Or.inl le_rfl
      · exact Or.inr h
    have hs : starts D d := by
      intro j hj hjd
      rcases List.mem_cons.mp ((mem j).mpr hj) with rfl | h
      · omega
      · have := (List.pairwise_cons.mp hsort).1 j h
        omega
    rw [List.splitBy, remaining_count D tail d [] [] hd hi hc hsort, List.countP_cons]
    simp
    rw [if_pos hs, Nat.add_comm]

private lemma start_iff (n d : ℕ) (hd : d ∈ n.divisors) :
    starts n.divisors d ↔ Odd d ∧ ∀ j ∈ n.divisors, j < d → 2 * j ≤ d := by
  have hpos := Nat.pos_of_mem_divisors hd
  constructor
  · intro hs
    refine ⟨Nat.not_even_iff_odd.mp ?_, fun j hj hlt => (hs j hj hlt).le⟩
    rintro ⟨u, hu⟩
    have hud : u ∣ d := ⟨2, by omega⟩
    obtain ⟨hdn, hn⟩ := Nat.mem_divisors.mp hd
    have hum : u ∈ n.divisors := Nat.mem_divisors.mpr ⟨hud.trans hdn, hn⟩
    have := hs u hum (by omega)
    omega
  · rintro ⟨⟨t, ht⟩, hw⟩ j hj hlt
    have := hw j hj hlt
    omega

lemma all_n (n : ℕ) : blockCount n = sigmaParts n := by
  unfold blockCount sigmaParts
  rw [count_starts]
  apply List.countP_congr
  intro d hd
  have hm : d ∈ n.divisors := (Finset.mem_sort _).mp hd
  simpa only [decide_eq_true_eq] using start_iff n d hm

end OMA.A386993

theorem OMA.solution : type_of% @OMA.S_oeis_a386993.main := by
  intro k
  exact OMA.A386993.all_n _
