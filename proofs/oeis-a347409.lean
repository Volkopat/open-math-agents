import OMAStatements.S_oeis_a347409
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic

/-!
# Infinitely many occurrences of each longest Collatz halving run k ≥ 4

For every odd u ≥ 5 not divisible by 3, there is an odd predecessor v ≥ 5,
also not divisible by 3, such that 3v+1 = 2^r u with r ≤ 4. Choose r by u
modulo 9. Starting at 5, this produces arbitrarily long traces ending at 1
whose halving runs have length at most 4. Prefix exactly k halvings to any
of them. A finite set of starting values could not give unbounded trace
lengths, since the trajectory up to the first visit to 1 is unique.
-/

namespace CollatzHalvingRuns

open OMA.S_oeis_a347409

private theorem unique_trace {n : ℕ} {s t : List Bool} (hs : Trace n s) (ht : Trace n t) :
    s = t := by
  induction hs generalizing t <;> cases ht <;> simp_all <;> solve_by_elim

private theorem prepend_halves {u : ℕ} {s : List Bool} (hu : 0 < u) (hs : Trace u s) (r : ℕ) :
    Trace (2 ^ r * u) (List.replicate r true ++ s) := by
  induction r with
  | zero => simpa using hs
  | succ r ih =>
    rw [List.replicate_succ, List.cons_append, pow_succ', Nat.mul_assoc]
    have hpos : 0 < 2 ^ r * u := Nat.mul_pos (by positivity) hu
    exact Trace.half (by omega) (by omega) (by simpa using ih)

private theorem leading_halves {s : List Bool} (h : (runStats s).1 = 0) (r : ℕ) :
    runStats (List.replicate r true ++ s) = (r, max r (runStats s).2) := by
  induction r with
  | zero =>
    simp only [List.replicate_zero, List.nil_append, Nat.zero_max]
    exact Prod.ext h rfl
  | succ r ih =>
    simp [List.replicate_succ, runStats, ih, ← Nat.max_assoc]

private theorem predecessor {u : ℕ} (hu : 5 ≤ u) (hc : u % 3 ≠ 0) :
    ∃ v r : ℕ, 5 ≤ v ∧ v % 2 = 1 ∧ v % 3 ≠ 0 ∧ r ≤ 4 ∧ 3 * v + 1 = 2 ^ r * u := by
  have hres : u % 9 = 1 ∨ u % 9 = 2 ∨ u % 9 = 4 ∨ u % 9 = 5 ∨ u % 9 = 7 ∨ u % 9 = 8 := by
    omega
  rcases hres with h | h | h | h | h | h
  · refine ⟨(16 * u - 1) / 3, 4, ?_⟩
    norm_num
    omega
  · refine ⟨(8 * u - 1) / 3, 3, ?_⟩
    norm_num
    omega
  · refine ⟨(4 * u - 1) / 3, 2, ?_⟩
    norm_num
    omega
  · refine ⟨(8 * u - 1) / 3, 3, ?_⟩
    norm_num
    omega
  · refine ⟨(16 * u - 1) / 3, 4, ?_⟩
    norm_num
    omega
  · refine ⟨(2 * u - 1) / 3, 1, ?_⟩
    norm_num
    omega

private structure BoundedTrace (u : ℕ) (s : List Bool) : Prop where
  large : 5 ≤ u
  nonmultiple : u % 3 ≠ 0
  valid : Trace u s
  leading : (runStats s).1 = 0
  longest : (runStats s).2 ≤ 4

private theorem long_traces (b : ℕ) :
    ∃ u : ℕ, ∃ s : List Bool, BoundedTrace u s ∧ b ≤ s.length := by
  induction b with
  | zero =>
    have tailTrace := prepend_halves (by decide : 0 < 1) Trace.stop 4
    exact ⟨5, false :: (List.replicate 4 true ++ []),
      ⟨by decide, by decide, Trace.triple (by decide) (by decide) tailTrace, rfl, by decide⟩,
      Nat.zero_le _⟩
  | succ b ih =>
    obtain ⟨u, s, g, hlen⟩ := ih
    obtain ⟨v, r, hv, hodd, hc, hr, he⟩ := predecessor g.large g.nonmultiple
    have tailTrace := prepend_halves (by have := g.large; omega : 0 < u) g.valid r
    rw [← he] at tailTrace
    refine ⟨v, false :: (List.replicate r true ++ s),
      ⟨hv, hc, Trace.triple (by omega) hodd tailTrace, rfl, ?_⟩, ?_⟩
    · change (runStats (List.replicate r true ++ s)).2 ≤ 4
      rw [leading_halves g.leading]
      exact max_le hr g.longest
    · simp only [List.length_cons, List.length_append, List.length_replicate]
      omega

private noncomputable def stepCount (n : ℕ) : ℕ := by
  classical
  exact if h : ∃ s, Trace n s then (Classical.choose h).length else 0

private theorem stepCount_eq {n : ℕ} {s : List Bool} (hs : Trace n s) :
    stepCount n = s.length := by
  rw [stepCount, dif_pos (show ∃ t, Trace n t from ⟨s, hs⟩)]
  exact congrArg List.length (unique_trace (Classical.choose_spec _) hs)

theorem infinite_starts (k : ℕ) (hk : 4 ≤ k) :
    Set.Infinite {n : ℕ | ∃ s : List Bool, Trace n s ∧ (runStats s).2 = k} := by
  classical
  intro hfin
  let bound := hfin.toFinset.sup stepCount
  obtain ⟨u, s, g, hlen⟩ := long_traces (bound + 1)
  have htrace := prepend_halves (by have := g.large; omega : 0 < u) g.valid k
  have hmem : 2 ^ k * u ∈ hfin.toFinset := by
    apply hfin.mem_toFinset.mpr
    refine ⟨_, htrace, ?_⟩
    rw [leading_halves g.leading]
    exact max_eq_left (g.longest.trans hk)
  have hbound : stepCount (2 ^ k * u) ≤ bound := Finset.le_sup (f := stepCount) hmem
  rw [stepCount_eq htrace, List.length_append, List.length_replicate] at hbound
  omega

end CollatzHalvingRuns

theorem OMA.solution : type_of% @OMA.S_oeis_a347409.main := CollatzHalvingRuns.infinite_starts
