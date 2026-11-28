import OMAStatements.S_oeis_a214972

namespace OMA.Sieve214972
open OMA.S_oeis_a214972

def survivor (i : ℕ) := i + i / 2 + 1

lemma kept_iff (j : ℕ) : kept j ↔ j % 3 ≠ 0 := by
  unfold kept A016777
  constructor
  · intro h hj
    exact h ⟨j / 3 + 1, by omega, by omega⟩
  · rintro h ⟨m, hm, he⟩
    omega

lemma nth_kept (i : ℕ) : Nat.nth kept i = survivor i := by
  have hm : StrictMono survivor := by
    intro x y h
    unfold survivor
    omega
  have hr : Set.range survivor = setOf kept := by
    ext j
    change (∃ x, survivor x = j) ↔ kept j
    rw [kept_iff]
    constructor
    · rintro ⟨x, rfl⟩
      unfold survivor
      omega
    · intro h
      by_cases h1 : j % 3 = 1
      · exact ⟨2 * (j / 3), by unfold survivor; omega⟩
      · exact ⟨2 * (j / 3) + 1, by unfold survivor; omega⟩
  have hi : (setOf kept).Infinite := hr ▸ Set.infinite_range_of_injective hm.injective
  symm
  apply Nat.eq_nth_of_strictMonoOn_of_mapsTo_of_surjOn survivor
  · intro j hj
    change j ∈ setOf kept at hj
    rw [← hr] at hj
    obtain ⟨x, hx⟩ := hj
    exact ⟨x, fun hf => (hi hf).elim, hx⟩
  · intro x _
    change survivor x ∈ setOf kept
    rw [← hr]
    exact ⟨x, rfl⟩
  · exact hm.strictMonoOn _
  · exact fun hf => (hi hf).elim

lemma stage_step (k i : ℕ) :
    stage (k+1) i = stage k i + (stage k i - 1) / 2 + 2 := by
  induction k generalizing i with
  | zero => simp [stage, nth_kept, survivor]; omega
  | succ k ih => exact ih (Nat.nth kept i + 1)

lemma threshold_pos (k : ℕ) : 0 < stage k 0 := by
  cases k with
  | zero => decide
  | succ k => rw [stage_step]; omega

lemma threshold (k n : ℕ) : stage k 0 ≤ n ↔ k + 1 ≤ a n := by
  induction k generalizing n with
  | zero =>
    cases n with
    | zero => simp [stage, a]
    | succ n => rw [a]; change 1 ≤ n+1 ↔ 1 ≤ _; omega
  | succ k ih =>
    have hp := threshold_pos k
    rw [stage_step]
    cases n with
    | zero => rw [a]; omega
    | succ n =>
      rw [a]
      have h := ih (2*n/3)
      omega

end OMA.Sieve214972

open OMA.S_oeis_a214972 OMA.Sieve214972 in
theorem OMA.solution : type_of% @OMA.S_oeis_a214972.main := by
  intro n hn
  have mono : a (n-1) ≤ a n := by
    by_contra! h
    have t := (threshold (a n) (n-1)).2 (by omega)
    have := (threshold (a n) n).1 (by omega)
    omega
  constructor
  · rintro ⟨m, hm, h⟩
    let k := m-1
    have he : stage k 0 = n := h
    have h1 := (threshold k n).1 he.le
    have h2 := threshold k (n-1)
    have h3 := threshold (k+1) n
    rw [stage_step, he] at h3
    have h4 : k ≤ a (n-1) := by
      cases hk : k with
      | zero => omega
      | succ j =>
        rw [hk, stage_step] at he
        exact (threshold j (n-1)).1 (by omega)
    omega
  · intro h
    by_contra! ne
    let k := a (n-1)
    have t := (threshold k n).2 (by dsimp [k]; omega)
    have u := threshold k (n-1)
    have e : stage k 0 = n := by dsimp [k] at *; omega
    exact h ⟨k+1, by omega, by simpa [A152009] using e⟩
