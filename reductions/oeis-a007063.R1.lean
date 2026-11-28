import OMAStatements.S_oeis_a007063
import Mathlib.Data.Set.Function

/-!
Kimberling's expulsion conjecture reduces to positive column trajectories.
The unchanged tail reaches any prescribed label at one of three consecutive
columns `2 * i - 3`, `2 * i - 2`, `2 * i - 1` in a suitable row `i`.
After that entry, both branches of the column update stay in the shuffled
part of the array. The column update and injectivity of the diagonal are
proved below. Iliya Bluskov used the column update in his solution to part (a)
of Kimberling's problem 1615 in Crux Mathematicorum, 18(3).
-/

namespace OMA.R_oeis_a007063_R1

open OMA.S_oeis_a007063

private theorem row_succ (i : ℕ) (hi : 1 ≤ i) :
    row (i + 1) = nextRow i (row i) := by
  cases i with
  | zero => omega
  | succ i => rfl

private theorem nextRow_apply (i c : ℕ) (a : ℕ → ℕ) :
    nextRow i a c = a (nextRow i id c) := by
  by_cases h : c + 1 ≤ 2 * i - 2 <;>
    by_cases ho : (c + 1) % 2 = 1 <;> simp [nextRow, h, ho]

private theorem next_column_injective (i : ℕ) (hi : 1 ≤ i) :
    Function.Injective (nextRow i id) := by
  intro a b h
  simp only [nextRow, id_eq] at h
  split at h
  · split at h <;> split at h
    all_goals (try split at h)
    all_goals omega
  · split at h
    · split at h <;> omega
    · omega

private theorem next_column_avoids_diagonal (i : ℕ) (hi : 1 ≤ i) (c : ℕ) :
    nextRow i id c ≠ i - 1 := by
  simp only [nextRow, id_eq]
  split
  · split <;> omega
  · omega

private theorem row_injective : ∀ i : ℕ, Function.Injective (row i)
  | 0 => by intro a b h; simpa [row] using h
  | 1 => by intro a b h; simpa [row] using h
  | i + 2 => by
    intro a b h
    rw [row_succ (i + 1) (by omega)] at h
    simp only [nextRow_apply (i + 1) a (row (i + 1)),
      nextRow_apply (i + 1) b (row (i + 1))] at h
    exact next_column_injective (i + 1) (by omega) (row_injective (i + 1) h)

private theorem row_positive : ∀ i c : ℕ, 1 ≤ row i c
  | 0, c => by simp [row]
  | 1, c => by simp [row]
  | i + 2, c => by
    rw [row_succ (i + 1) (by omega), nextRow_apply]
    exact row_positive (i + 1) _

private theorem later_row_avoids (i : ℕ) (hi : 1 ≤ i) :
    ∀ j, i < j → ∀ c, row j c ≠ diag i := by
  intro j
  induction j with
  | zero => omega
  | succ j ih =>
    intro hij c hc
    rw [row_succ j (by omega), nextRow_apply] at hc
    by_cases he : j = i
    · subst j
      exact next_column_avoids_diagonal i hi c (row_injective i hc)
    · exact ih (by omega) _ hc

private theorem row_tail : ∀ i c : ℕ, 1 ≤ i → 2 * i ≤ c + 4 → row i c = c + i
  | 0, c, hi, _ => by omega
  | 1, c, _, _ => rfl
  | i + 2, c, _, hc => by
    have htail : ¬(c + 1 ≤ 2 * (i + 1) - 2) := by omega
    rw [row_succ (i + 1) (by omega)]
    simp only [nextRow, htail, if_false, Nat.add_sub_cancel]
    rw [row_tail (i + 1) (c + 1) (by omega) (by omega)]
    omega

/-- The diagonal is injective because each row removes its diagonal entry. -/
theorem diag_injOn : Set.InjOn diag {i : ℕ | 1 ≤ i} := by
  intro i hi j hj he
  rcases lt_trichotomy i j with hij | hij | hji
  · exact (later_row_avoids i hi j hij (j - 1) he.symm).elim
  · exact hij
  · exact (later_row_avoids j hj i hji (i - 1) he).elim

/-- Every trajectory starting at the right edge of the shuffle hits the diagonal. -/
def H1 : Prop :=
  ∀ i p : ℕ, 1 ≤ i → 1 ≤ p → p < 2 * i → 2 * i ≤ p + 3 →
    ∀ f : ℕ → ℕ, f 0 = p →
      (∀ t, f (t + 1) =
        if f t = 0 ∨ f t = i + t then 0
        else if f t < i + t then 2 * (i + t - f t) else 2 * (f t - (i + t)) - 1) →
      ∃ t, f t = i + t

/-- A surviving column moves to the column given by the affine update. -/
def H2 : Prop :=
  ∀ i p : ℕ, 1 ≤ i → 1 ≤ p → p < 2 * i → p ≠ i →
    let q := if p < i then 2 * (i - p) else 2 * (p - i) - 1
    1 ≤ q ∧ q < 2 * (i + 1) ∧ row (i + 1) (q - 1) = row i (p - 1)

/-- The two branches of the affine update invert the corresponding shuffles. -/
theorem column_transport : H2 := by
  intro i p hi hp hlt hne
  by_cases h : p < i
  · simp only [if_pos h]
    have hshuffle : (2 * (i - p) - 1) + 1 ≤ 2 * i - 2 := by omega
    have hparity : ((2 * (i - p) - 1) + 1) % 2 ≠ 1 := by omega
    refine ⟨by omega, by omega, ?_⟩
    rw [row_succ i hi]
    simp only [nextRow, hshuffle, hparity, if_true, if_false]
    congr 1
    omega
  · simp only [if_neg h]
    have hshuffle : (2 * (p - i) - 1 - 1) + 1 ≤ 2 * i - 2 := by omega
    have hparity : ((2 * (p - i) - 1 - 1) + 1) % 2 = 1 := by omega
    refine ⟨by omega, by omega, ?_⟩
    rw [row_succ i hi]
    simp only [nextRow, hshuffle, hparity, if_true]
    congr 1
    omega

private theorem trajectory_consistent (transport : H2) {i p : ℕ}
    (hi : 1 ≤ i) (hp : 1 ≤ p) (hbound : p < 2 * i) {f : ℕ → ℕ} (hf : f 0 = p)
    (step : ∀ t, f (t + 1) =
      if f t = 0 ∨ f t = i + t then 0
      else if f t < i + t then 2 * (i + t - f t) else 2 * (f t - (i + t)) - 1) :
    ∀ t, f t = 0 ∨ (1 ≤ f t ∧ f t < 2 * (i + t) ∧
      row (i + t) (f t - 1) = row i (p - 1)) := by
  intro t
  induction t with
  | zero =>
    right
    simp only [hf, Nat.add_zero]
    exact ⟨hp, hbound, trivial⟩
  | succ t ih =>
    rcases ih with hz | ⟨hpositive, hupper, hr⟩
    · left
      simpa only [hz, true_or, if_true] using step t
    · by_cases hd : f t = i + t
      · left
        simpa [hd] using step t
      · have hnz : f t ≠ 0 := by omega
        have hnext : f (t + 1) =
          if f t < i + t then 2 * (i + t - f t) else 2 * (f t - (i + t)) - 1 := by
          simpa only [hnz, hd, false_or, if_false] using step t
        obtain ⟨hq, hqu, hrow⟩ := transport (i + t) (f t) (by omega) hpositive hupper hd
        right
        rw [hnext, Nat.add_succ]
        exact ⟨hq, hqu, hrow.trans hr⟩

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a007063.main := by
  intro hits transport
  refine ⟨?_, diag_injOn, ?_⟩
  · intro i hi
    exact row_positive i (i - 1)
  · intro n hn
    change 1 ≤ n at hn
    let i : ℕ := (n + 1) / 3 + 1
    let p : ℕ := n + 1 - i
    have hi : 1 ≤ i := by dsimp [i]; omega
    have hp : 1 ≤ p := by dsimp [p, i]; omega
    have hupper : p < 2 * i := by dsimp [p, i]; omega
    have hentry : 2 * i ≤ p + 3 := by dsimp [p, i]; omega
    have hlabel : row i (p - 1) = n := by
      rw [row_tail i (p - 1) hi (by omega)]
      dsimp [p, i]
      omega
    let advance (u q : ℕ) : ℕ :=
      if q = 0 ∨ q = i + u then 0
      else if q < i + u then 2 * (i + u - q) else 2 * (q - (i + u)) - 1
    let f : ℕ → ℕ := fun t => Nat.rec p advance t
    have hf : f 0 = p := rfl
    have step (t : ℕ) : f (t + 1) = advance t (f t) := rfl
    obtain ⟨t, ht⟩ := hits i p hi hp hupper hentry f hf step
    rcases trajectory_consistent transport hi hp hupper hf step t with hz | ⟨_, _, hr⟩
    · omega
    · exact ⟨i + t, by change 1 ≤ i + t; omega, by simpa only [diag, ht, hlabel] using hr⟩

/-- Surjectivity also implies that every one of the boundary trajectories hits. -/
theorem trajectories_hit_of_bijOn : (type_of% @OMA.S_oeis_a007063.main) → H1 := by
  intro hbij i p hi hp hupper _ f hf step
  by_contra! noHit
  have hnz : ∀ t, f t ≠ 0 := by
    intro t
    induction t with
    | zero => rw [hf]; omega
    | succ t ih =>
      have hd := noHit t
      have hnext := step t
      rw [if_neg (fun h => h.elim ih hd)] at hnext
      split at hnext <;> omega
  obtain ⟨j, hj, hjlabel⟩ := hbij.2.2 (row_positive i (p - 1))
  have hji : i ≤ j := by
    by_contra! hjlt
    exact later_row_avoids j hj i hjlt (p - 1) hjlabel.symm
  let t := j - i
  have ht : i + t = j := by dsimp [t]; omega
  rcases trajectory_consistent column_transport hi hp hupper hf step t with hz | ⟨hpos, _, hr⟩
  · exact hnz t hz
  · apply noHit t
    have hc : row j (f t - 1) = row j (j - 1) := by
      rw [ht] at hr
      exact hr.trans hjlabel.symm
    have hcol := row_injective j hc
    omega

end OMA.R_oeis_a007063_R1
