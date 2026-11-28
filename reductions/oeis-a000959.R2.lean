import OMAStatements.S_oeis_a000959

-- Credit: @synthrosai
namespace OMA.R_oeis_a000959_R2

open OMA.S_oeis_a000959

/-- On a right edge, an entry in a column at least two is bounded by two plus
the sum of the entries below it down to column one. -/
def H1 : Prop :=
  ∀ t i : ℕ, 1 ≤ t → 1 ≤ i →
    gilbreath (b 2) t (i + 1) ≤
      2 + ∑ j ∈ Finset.range i, gilbreath (b 2) (t + 1 + j) (i - j)

/-- The next input gap is bounded by two plus the preceding right edge.
The sum starts at the preceding gap and ends in column one. -/
def H2 : Prop :=
  ∀ i : ℕ, gilbreath (b 2) 1 (i + 1) ≤
    2 + ∑ j ∈ Finset.range i, gilbreath (b 2) (1 + j) (i - j)

lemma row_nonnegative (t i : ℕ) (ht : 1 ≤ t) : 0 ≤ gilbreath (b 2) t i := by
  cases t with
  | zero => omega
  | succ t => exact abs_nonneg _

lemma split_sum (t i : ℕ) :
    (∑ j ∈ Finset.range (i + 1), gilbreath (b 2) (t + j) (i + 1 - j)) =
    gilbreath (b 2) t (i + 1) +
      ∑ j ∈ Finset.range i, gilbreath (b 2) (t + 1 + j) (i - j) := by
  rw [Finset.sum_range_succ']
  simp only [Nat.add_zero, Nat.sub_zero]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [show t + (j + 1) = t + 1 + j by omega, show i + 1 - (j + 1) = i - j by omega]

lemma descend_edge (inside : H1) (t i : ℕ) (ht : 1 ≤ t)
    (previous : ∀ s : ℕ, 1 ≤ s → s < t + i → gilbreath (b 2) s 1 ≤ 2)
    (budget : gilbreath (b 2) t (i + 1) ≤
      2 + ∑ j ∈ Finset.range i, gilbreath (b 2) (t + j) (i - j)) :
    gilbreath (b 2) (t + i) 1 ≤ 2 := by
  induction i generalizing t with
  | zero => simpa using budget
  | succ i ih =>
    rw [split_sum] at budget
    let rest : ℤ := ∑ j ∈ Finset.range i, gilbreath (b 2) (t + 1 + j) (i - j)
    have available : gilbreath (b 2) t (i + 1) ≤ 2 + rest := by
      cases i with
      | zero =>
        have prior := previous t ht (by omega)
        simpa [rest] using prior
      | succ i => exact inside t (i + 1) ht (by omega)
    have positive := row_nonnegative t (i + 1 + 1) ht
    change gilbreath (b 2) t (i + 1 + 1) ≤ 2 + (gilbreath (b 2) t (i + 1) + rest) at budget
    have next : gilbreath (b 2) (t + 1) (i + 1) ≤ 2 + rest := by
      change |gilbreath (b 2) t (i + 1 + 1) - gilbreath (b 2) t (i + 1)| ≤ 2 + rest
      exact abs_le.mpr ⟨by omega, by omega⟩
    rw [show t + (i + 1) = t + 1 + i by omega]
    exact ih (t + 1) (by omega) (fun s hs hy => previous s hs (by omega)) next

lemma first_tail_bound (inside : H1) (gaps : H2) (t : ℕ) (ht : 1 ≤ t) :
    gilbreath (b 2) t 1 ≤ 2 := by
  induction t using Nat.strong_induction_on with
  | h t ih =>
    obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show t ≠ 0 by omega)
    change gilbreath (b 2) (i + 1) 1 ≤ 2
    rw [show i + 1 = 1 + i by omega]
    exact descend_edge inside 1 i (by decide)
      (fun s hs hsi => ih s (by omega) hs) (gaps i)

lemma odd_stage (k i : ℕ) : s k i % 2 = 1 := by
  induction k generalizing i with
  | zero => simp [s]
  | succ k ih => exact ih _

lemma tail_residue (t i : ℕ) (hi : 0 < i) :
    gilbreath (b 2) t i % 2 = if t = 0 then 1 else 0 := by
  induction t generalizing i with
  | zero =>
    simp only [gilbreath, b, if_neg (Nat.ne_of_gt hi), if_true]
    split
    · decide
    · have h := odd_stage i i
      unfold lucky
      omega
  | succ t ih =>
    simp only [gilbreath, Nat.succ_ne_zero, if_false]
    have hl := ih i hi
    have hr := ih (i + 1) (by omega)
    by_cases h : 0 ≤ gilbreath (b 2) t (i + 1) - gilbreath (b 2) t i
    · rw [abs_of_nonneg h]
      omega
    · rw [abs_of_neg (by omega : gilbreath (b 2) t (i + 1) - gilbreath (b 2) t i < 0)]
      omega

lemma same_rows (n i : ℕ) : gilbreath (b 4) (n + 1) i = gilbreath (b 2) (n + 1) i := by
  induction n generalizing i with
  | zero =>
    cases i with
    | zero => decide
    | succ i => simp [gilbreath, b]
  | succ n ih =>
    change |gilbreath (b 4) (n + 1) (i + 1) - gilbreath (b 4) (n + 1) i| =
      |gilbreath (b 2) (n + 1) (i + 1) - gilbreath (b 2) (n + 1) i|
    rw [ih, ih]

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a000959.main := by
  intro inside gaps
  have heads (n : ℕ) : gilbreath (b 2) (n + 1) 0 = 1 := by
    induction n with
    | zero => decide
    | succ n ih =>
      change |gilbreath (b 2) (n + 1) 1 - gilbreath (b 2) (n + 1) 0| = 1
      rw [ih]
      have hn := row_nonnegative (n + 1) 1 (by omega)
      have hb := first_tail_bound inside gaps (n + 1) (by omega)
      have he := tail_residue (n + 1) 1 (by omega)
      simp only [Nat.succ_ne_zero, if_false] at he
      rcases (show gilbreath (b 2) (n + 1) 1 = 0 ∨ gilbreath (b 2) (n + 1) 1 = 2 by omega)
        with h | h <;> rw [h] <;> decide
  intro c hc t ht
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show t ≠ 0 by omega)
  rcases (show c = 2 ∨ c = 4 from hc) with rfl | rfl
  · exact heads n
  · exact (same_rows n 0).trans (heads n)

end OMA.R_oeis_a000959_R2
