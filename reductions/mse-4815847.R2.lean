import OMAStatements.S_mse_4815847
import Mathlib

/- Lines parallel to a side of the triangle never split it into equal sums.
Rows (b = 0): the row just above a horizontal cut already outweighs every row below it,
since each row sum is 2^r - 2. Columns (a = 0): by the hockey stick identity, column k sums
to C(N+1,k+1) - 1. Equal halves would force a partial row sum of row N+1 to equal
2^N plus the cut index, and the reflection symmetry of binomial rows rules this out.
Anti-diagonals (a + b = 0) reduce to columns via (r,k) to (r,r-k). If a = b = 0, one side
is empty. What remains are the lines of generic slope, split by the sign of a b. -/
namespace OMA.R_mse_4815847_R2

open OMA.S_mse_4815847 Finset

def H1 : Prop :=
  ∀ N : ℕ, 2 ≤ N → ∀ a b c : ℝ, 0 < a * b →
    (∀ p ∈ OMA.S_mse_4815847.entries N, OMA.S_mse_4815847.side a b c p ≠ 0) →
    ∑ p ∈ (OMA.S_mse_4815847.entries N).filter
        (fun p => 0 < OMA.S_mse_4815847.side a b c p), Nat.choose p.1 p.2 ≠
      ∑ p ∈ (OMA.S_mse_4815847.entries N).filter
        (fun p => OMA.S_mse_4815847.side a b c p < 0), Nat.choose p.1 p.2

def H2 : Prop :=
  ∀ N : ℕ, 2 ≤ N → ∀ a b c : ℝ, a * b < 0 → a + b ≠ 0 →
    (∀ p ∈ OMA.S_mse_4815847.entries N, OMA.S_mse_4815847.side a b c p ≠ 0) →
    ∑ p ∈ (OMA.S_mse_4815847.entries N).filter
        (fun p => 0 < OMA.S_mse_4815847.side a b c p), Nat.choose p.1 p.2 ≠
      ∑ p ∈ (OMA.S_mse_4815847.entries N).filter
        (fun p => OMA.S_mse_4815847.side a b c p < 0), Nat.choose p.1 p.2

theorem floor_cut (t : ℝ) (n : ℕ) (hn : 1 ≤ n) : t < n ↔ ⌊t⌋₊ < n := by
  by_cases h0 : 0 ≤ t
  · exact (Nat.floor_lt h0).symm
  · push Not at h0
    rw [Nat.floor_of_nonpos h0.le]
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    constructor
    · intro; omega
    · intro; linarith

/-- A line `α g + c = 0` through a natural-valued coordinate `g` cuts at a natural threshold. -/
theorem cut (N : ℕ) (g : ℕ × ℕ → ℕ) (hg : ∀ p ∈ entries N, 1 ≤ g p) (α c : ℝ) (hα : α ≠ 0)
    (hv : ∀ p ∈ entries N, α * (g p : ℝ) + c ≠ 0)
    (key : ∀ R : ℕ, ∑ p ∈ (entries N).filter (fun p => R < g p), Nat.choose p.1 p.2 ≠
      ∑ p ∈ (entries N).filter (fun p => ¬ R < g p), Nat.choose p.1 p.2) :
    ∑ p ∈ (entries N).filter (fun p => 0 < α * (g p : ℝ) + c), Nat.choose p.1 p.2 ≠
      ∑ p ∈ (entries N).filter (fun p => α * (g p : ℝ) + c < 0), Nat.choose p.1 p.2 := by
  set R := ⌊-c / α⌋₊ with hR
  rcases hα.lt_or_gt with h | h
  · have hneg : ∀ p ∈ entries N, (α * (g p : ℝ) + c < 0 ↔ R < g p) := by
      intro p hp
      rw [← floor_cut _ _ (hg p hp), div_lt_iff_of_neg h]
      constructor <;> intro <;> linarith
    have hpos : ∀ p ∈ entries N, (0 < α * (g p : ℝ) + c ↔ ¬ R < g p) := by
      intro p hp
      rw [← hneg p hp]
      have := hv p hp
      constructor
      · intro h1 h2; linarith
      · intro h1; push Not at h1; exact lt_of_le_of_ne h1 (Ne.symm this)
    rw [Finset.filter_congr hpos, Finset.filter_congr hneg]
    exact (key R).symm
  · have hpos : ∀ p ∈ entries N, (0 < α * (g p : ℝ) + c ↔ R < g p) := by
      intro p hp
      rw [← floor_cut _ _ (hg p hp), div_lt_iff₀ h]
      constructor <;> intro <;> linarith
    have hneg : ∀ p ∈ entries N, (α * (g p : ℝ) + c < 0 ↔ ¬ R < g p) := by
      intro p hp
      rw [← hpos p hp]
      have := hv p hp
      constructor
      · intro h1 h2; linarith
      · intro h1; push Not at h1; exact lt_of_le_of_ne h1 this
    rw [Finset.filter_congr hpos, Finset.filter_congr hneg]
    exact key R

theorem mem_entries {N : ℕ} {p : ℕ × ℕ} :
    p ∈ entries N ↔ p.1 ≤ N ∧ 1 ≤ p.2 ∧ p.2 + 1 ≤ p.1 := by
  simp only [entries, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  omega

lemma sum_entries_rows {M : Type*} [AddCommMonoid M] (N : ℕ) (g : ℕ × ℕ → M) :
    ∑ p ∈ entries N, g p = ∑ r ∈ range (N + 1), ∑ k ∈ Ioo 0 r, g (r, k) := by
  rw [entries, sum_filter, sum_product]
  refine sum_congr rfl fun r hr => ?_
  rw [← sum_filter]
  refine sum_congr ?_ fun _ _ => rfl
  ext k
  simp only [mem_filter, mem_range, mem_Ioo] at hr ⊢
  omega

lemma sum_entries_cols {M : Type*} [AddCommMonoid M] (N : ℕ) (g : ℕ × ℕ → M) :
    ∑ p ∈ entries N, g p = ∑ k ∈ Ioo 0 N, ∑ r ∈ Ioc k N, g (r, k) := by
  rw [entries, sum_filter, sum_product_right]
  have h1 : ∀ k ∈ range (N + 1), (∑ r ∈ range (N + 1),
      if 1 ≤ (r, k).2 ∧ (r, k).2 + 1 ≤ (r, k).1 then g (r, k) else 0) =
      if k ∈ Ioo 0 N then ∑ r ∈ Ioc k N, g (r, k) else 0 := by
    intro k hk
    rw [← sum_filter]
    split_ifs with hkk
    · refine sum_congr ?_ fun _ _ => rfl
      ext r
      simp only [mem_filter, mem_range, mem_Ioc, mem_Ioo] at hk hkk ⊢
      omega
    · refine sum_eq_zero fun r hr => ?_
      simp only [mem_filter, mem_range, mem_Ioo] at hr hkk hk
      omega
  rw [sum_congr rfl h1, ← sum_filter]
  refine sum_congr ?_ fun _ _ => rfl
  ext k
  simp only [mem_filter, mem_range, mem_Ioo]
  omega

lemma row_sum (r : ℕ) : ∑ k ∈ Ioo 0 r, r.choose k = 2 ^ r - 2 := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp
  have hset : range (r + 1) = insert 0 (insert r (Ioo 0 r)) := by
    ext k; simp only [mem_range, mem_insert, mem_Ioo]; omega
  have h := Nat.sum_range_choose r
  rw [hset, sum_insert (by simp; omega), sum_insert (by simp)] at h
  simp only [Nat.choose_zero_right, Nat.choose_self] at h
  omega

lemma rows_total_add (R : ℕ) :
    (∑ r ∈ range (R + 1), (2 ^ r - 2)) + 2 * R + 2 = 2 ^ (R + 1) := by
  induction R with
  | zero => simp
  | succ R ih =>
    rw [sum_range_succ]
    have : 2 ≤ 2 ^ (R + 1) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (R + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [pow_succ 2 (R + 1)]
    omega

lemma total_add (N : ℕ) :
    (∑ p ∈ entries N, p.1.choose p.2) + 2 * N + 2 = 2 ^ (N + 1) := by
  rw [sum_entries_rows, sum_congr rfl fun r _ => row_sum r]; exact rows_total_add N

lemma total_pos {N : ℕ} (hN : 2 ≤ N) : 0 < ∑ p ∈ entries N, p.1.choose p.2 := by
  refine sum_pos' (fun p _ => Nat.zero_le _) ⟨(2, 1), ?_, ?_⟩
  · rw [mem_entries]; simp; omega
  · decide

lemma col_sum_add {N k : ℕ} (hk : k ≤ N) :
    (∑ r ∈ Ioc k N, r.choose k) + 1 = (N + 1).choose (k + 1) := by
  rw [← Nat.sum_Icc_choose N k]
  have hset : Icc k N = insert k (Ioc k N) := by
    ext r; simp only [mem_Icc, mem_insert, mem_Ioc]; omega
  rw [hset, sum_insert (by simp), Nat.choose_self, add_comm]

lemma partial_reflect {n m : ℕ} (hm : m < n) :
    (∑ j ∈ range (m + 1), n.choose j) + ∑ j ∈ range (n - m), n.choose j = 2 ^ n := by
  rw [← Nat.sum_range_choose n]
  have h2 : ∑ j ∈ range (n - m), n.choose j = ∑ j ∈ Ico (m + 1) (n + 1), n.choose j := by
    rw [← sum_range_reflect]
    rw [sum_Ico_eq_sum_range]
    have : n + 1 - (m + 1) = n - m := by omega
    rw [this]
    refine sum_congr rfl fun j hj => ?_
    rw [mem_range] at hj
    rw [← Nat.choose_symm (by omega)]
    congr 1
    omega
  rw [h2, sum_range_add_sum_Ico _ (by omega)]

theorem self_le_choose : ∀ n k : ℕ, 1 ≤ k → k + 1 ≤ n → n ≤ n.choose k
  | 0, k, h1, h2 => by omega
  | n + 1, k, h1, h2 => by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [Nat.choose_succ_succ']
    rcases Nat.eq_zero_or_pos k' with rfl | hk
    · simp
    · have := self_le_choose n k' hk (by omega)
      have := Nat.choose_pos (show k' + 1 ≤ n by omega)
      omega

theorem choose_big {n m : ℕ} (hm : 2 ≤ m) (hn : m + 2 ≤ n) : 2 * (n - 1) ≤ n.choose m := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  rw [Nat.choose_succ_succ', Nat.add_sub_cancel]
  have := self_le_choose n' m' (by omega) (by omega)
  have := self_le_choose n' (m' + 1) (by omega) (by omega)
  omega

/-- The partial row sum `P(m)` of row `n` never equals `2^(n-1) + m` for `2 ≤ m ≤ n-2`. -/
theorem key_P {n m : ℕ} (hm : 2 ≤ m) (hn : m + 2 ≤ n) :
    2 * ∑ j ∈ range (m + 1), n.choose j ≠ 2 ^ n + 2 * m := by
  have hr := partial_reflect (n := n) (m := m) (by omega)
  rcases le_or_gt (m + 1) (n - m) with h | h
  · have := sum_le_sum_of_subset (f := fun j => n.choose j) (range_subset_range.2 h)
    omega
  · have hs := sum_range_add_sum_Ico (fun j => n.choose j) (show n - m ≤ m + 1 by omega)
    have hb : n.choose m ≤ ∑ j ∈ Ico (n - m) (m + 1), n.choose j :=
      single_le_sum (f := fun j => n.choose j) (fun _ _ => Nat.zero_le _)
        (mem_Ico.2 ⟨by omega, by omega⟩)
    have := choose_big hm hn
    omega

lemma cols_split (N : ℕ) (Q : ℕ → Prop) [DecidablePred Q] :
    ∑ p ∈ (entries N).filter (fun p => Q p.2), Nat.choose p.1 p.2 =
      ∑ k ∈ (Ioo 0 N).filter Q, ((N + 1).choose (k + 1) - 1) := by
  rw [sum_filter, sum_entries_cols, sum_filter]
  refine sum_congr rfl fun k hk => ?_
  by_cases h : Q k
  · simp only [h, if_true]
    have := col_sum_add (N := N) (k := k) (by rw [mem_Ioo] at hk; omega)
    omega
  · simp [h]

lemma colsL (N : ℕ) : ∀ R : ℕ, R + 1 ≤ N →
    (∑ k ∈ Ioc 0 R, ((N + 1).choose (k + 1) - 1)) + R + 1 + (N + 1) =
      ∑ j ∈ range (R + 2), (N + 1).choose j := by
  intro R
  induction R with
  | zero => intro _; simp [sum_range_succ]
  | succ R ih =>
    intro hR
    rw [sum_Ioc_succ_top (by omega), sum_range_succ (n := R + 2)]
    have := ih (by omega)
    have := Nat.choose_pos (show R + 1 + 1 ≤ N + 1 by omega)
    have e2 : (N + 1).choose (R + 1 + 1) = (N + 1).choose (R + 2) := rfl
    omega

/-- Vertical cuts (columns). -/
theorem cols_key (N : ℕ) (hN : 2 ≤ N) (R : ℕ) :
    ∑ p ∈ (entries N).filter (fun p => R < p.2), Nat.choose p.1 p.2 ≠
      ∑ p ∈ (entries N).filter (fun p => ¬ R < p.2), Nat.choose p.1 p.2 := by
  intro heq
  have hsplit := sum_filter_add_sum_filter_not (entries N) (fun p => R < p.2)
    (fun p => Nat.choose p.1 p.2)
  have hT := total_add N
  have hTp := total_pos hN
  by_cases hR0 : R = 0
  · have e : (entries N).filter (fun p => ¬ R < p.2) = ∅ :=
      filter_false_of_mem (fun p hp => by rw [mem_entries] at hp; omega)
    rw [e, sum_empty] at heq hsplit
    omega
  by_cases hRN : N ≤ R + 1
  · have e : (entries N).filter (fun p => R < p.2) = ∅ :=
      filter_false_of_mem (fun p hp => by rw [mem_entries] at hp; omega)
    rw [e, sum_empty] at heq hsplit
    omega
  have hL : ∑ p ∈ (entries N).filter (fun p => ¬ R < p.2), Nat.choose p.1 p.2 =
      ∑ k ∈ Ioc 0 R, ((N + 1).choose (k + 1) - 1) := by
    rw [cols_split N (fun k => ¬ R < k)]
    congr 1
    ext k; simp only [mem_filter, mem_Ioo, mem_Ioc]; omega
  have hP := colsL N R (by omega)
  have hk := key_P (n := N + 1) (m := R + 1) (by omega) (by omega)
  rw [show R + 1 + 1 = R + 2 by omega] at hk
  omega

lemma rows_split (N : ℕ) (Q : ℕ → Prop) [DecidablePred Q] :
    ∑ p ∈ (entries N).filter (fun p => Q p.1), Nat.choose p.1 p.2 =
      ∑ r ∈ (range (N + 1)).filter Q, (2 ^ r - 2) := by
  rw [sum_filter, sum_entries_rows, sum_filter]
  refine sum_congr rfl fun r _ => ?_
  by_cases h : Q r <;> simp [h, row_sum]

theorem rows_key (N : ℕ) (hN : 2 ≤ N) (R : ℕ) :
    ∑ p ∈ (entries N).filter (fun p => R < p.1), Nat.choose p.1 p.2 ≠
      ∑ p ∈ (entries N).filter (fun p => ¬ R < p.1), Nat.choose p.1 p.2 := by
  rw [rows_split N (fun r => R < r), rows_split N (fun r => ¬ R < r)]
  rcases le_or_gt N R with h | h
  · have e : (range (N + 1)).filter (fun r => R < r) = ∅ :=
      filter_false_of_mem (fun r hr => by rw [mem_range] at hr; omega)
    rw [e, sum_empty]
    have : 2 ^ 2 - 2 ≤ ∑ r ∈ (range (N + 1)).filter (fun r => ¬ R < r), (2 ^ r - 2) :=
      single_le_sum (f := fun r : ℕ => 2 ^ r - 2) (fun _ _ => Nat.zero_le _)
        (mem_filter.2 ⟨mem_range.2 (by omega), by omega⟩)
    have h4 : (2 : ℕ) ^ 2 - 2 = 2 := by norm_num
    omega
  · have e : (range (N + 1)).filter (fun r => ¬ R < r) = range (R + 1) := by
      ext r; simp only [mem_filter, mem_range]; omega
    rw [e]
    have hL := rows_total_add R
    have hU1 : 2 ^ (R + 1) - 2 ≤ ∑ r ∈ (range (N + 1)).filter (fun r => R < r), (2 ^ r - 2) :=
      single_le_sum (f := fun r : ℕ => 2 ^ r - 2) (fun _ _ => Nat.zero_le _)
        (mem_filter.2 ⟨mem_range.2 (by omega), by omega⟩)
    have hU2 : 2 ^ 2 - 2 ≤ ∑ r ∈ (range (N + 1)).filter (fun r => R < r), (2 ^ r - 2) := by
      by_cases hR : R = 0
      · exact single_le_sum (f := fun r : ℕ => 2 ^ r - 2) (fun _ _ => Nat.zero_le _)
          (mem_filter.2 ⟨mem_range.2 (by omega), by omega⟩)
      · exact le_trans (Nat.sub_le_sub_right (Nat.pow_le_pow_right (by norm_num) (by omega)) 2) hU1
    have h4 : (2 : ℕ) ^ 2 - 2 = 2 := by norm_num
    by_cases hR : R = 0
    · have h0 : ∑ r ∈ range (R + 1), (2 ^ r - 2) = 0 := by subst hR; simp
      omega
    · omega

/-- The reflection `(r, k) ↦ (r, r - k)` turns anti-diagonals into columns. -/
theorem anti_eq (N : ℕ) (Q : ℕ → Prop) [DecidablePred Q] :
    ∑ p ∈ (entries N).filter (fun p => Q (p.1 - p.2)), Nat.choose p.1 p.2 =
      ∑ p ∈ (entries N).filter (fun p => Q p.2), Nat.choose p.1 p.2 := by
  apply Finset.sum_nbij' (fun p => (p.1, p.1 - p.2)) (fun p => (p.1, p.1 - p.2))
  · intro p hp
    simp only [Finset.mem_filter, mem_entries] at hp ⊢
    refine ⟨⟨hp.1.1, by omega, by omega⟩, hp.2⟩
  · intro p hp
    simp only [Finset.mem_filter, mem_entries] at hp ⊢
    refine ⟨⟨hp.1.1, by omega, by omega⟩, ?_⟩
    rw [show p.1 - (p.1 - p.2) = p.2 by omega]; exact hp.2
  · intro p hp
    simp only [Finset.mem_filter, mem_entries] at hp
    ext <;> simp; omega
  · intro p hp
    simp only [Finset.mem_filter, mem_entries] at hp
    ext <;> simp; omega
  · intro p hp
    simp only [Finset.mem_filter, mem_entries] at hp
    exact (Nat.choose_symm (by omega)).symm

theorem anti_key (N : ℕ) (hN : 2 ≤ N) (R : ℕ) :
    ∑ p ∈ (entries N).filter (fun p => R < p.1 - p.2), Nat.choose p.1 p.2 ≠
      ∑ p ∈ (entries N).filter (fun p => ¬ R < p.1 - p.2), Nat.choose p.1 p.2 := by
  rw [anti_eq N (fun x => R < x), anti_eq N (fun x => ¬ R < x)]
  exact cols_key N hN R

theorem deg_case (N : ℕ) (hN : 2 ≤ N) (c : ℝ) (hv : ∀ p ∈ entries N, side 0 0 c p ≠ 0) :
    ∑ p ∈ (entries N).filter (fun p => 0 < side 0 0 c p), Nat.choose p.1 p.2 ≠
      ∑ p ∈ (entries N).filter (fun p => side 0 0 c p < 0), Nat.choose p.1 p.2 := by
  have h21 : ((2 : ℕ), (1 : ℕ)) ∈ entries N := mem_entries.2 ⟨hN, le_refl _, le_refl _⟩
  have hc : c ≠ 0 := by simpa [side] using hv _ h21
  simp only [side, zero_mul, zero_add]
  rcases hc.lt_or_gt with h | h
  · have e1 : (entries N).filter (fun _ => 0 < c) = ∅ := Finset.filter_false_of_mem (fun _ _ => by linarith)
    rw [e1, Finset.sum_empty]
    have : 2 ≤ ∑ p ∈ (entries N).filter (fun _ => c < 0), Nat.choose p.1 p.2 :=
      Finset.single_le_sum (f := fun p : ℕ × ℕ => Nat.choose p.1 p.2) (fun _ _ => Nat.zero_le _)
        (Finset.mem_filter.2 ⟨h21, h⟩)
    omega
  · have e1 : (entries N).filter (fun _ => c < 0) = ∅ := Finset.filter_false_of_mem (fun _ _ => by linarith)
    rw [e1, Finset.sum_empty]
    have : 2 ≤ ∑ p ∈ (entries N).filter (fun _ => 0 < c), Nat.choose p.1 p.2 :=
      Finset.single_le_sum (f := fun p : ℕ × ℕ => Nat.choose p.1 p.2) (fun _ _ => Nat.zero_le _)
        (Finset.mem_filter.2 ⟨h21, h⟩)
    omega

theorem main : H1 → H2 → type_of% @OMA.S_mse_4815847.main := by
  intro h1 h2 N hN a b c hv
  rcases eq_or_ne b 0 with hb | hb
  · subst hb
    rcases eq_or_ne a 0 with ha | ha
    · subst ha; exact deg_case N hN c hv
    · have e : ∀ p : ℕ × ℕ, side a 0 c p = a * ((p.1 : ℕ) : ℝ) + c := by
        intro p; simp [side]
      simp only [e] at hv ⊢
      exact cut N Prod.fst (fun p hp => by have := mem_entries.1 hp; omega) a c ha hv
        (rows_key N hN)
  rcases eq_or_ne a 0 with ha | ha
  · subst ha
    have e : ∀ p : ℕ × ℕ, side 0 b c p = b * ((p.2 : ℕ) : ℝ) + c := by
      intro p; simp [side]
    simp only [e] at hv ⊢
    exact cut N Prod.snd (fun p hp => (mem_entries.1 hp).2.1) b c hb hv (cols_key N hN)
  by_cases hab : a + b = 0
  · have hb' : b = -a := by linarith
    subst hb'
    have e : ∀ p ∈ entries N, side a (-a) c p = a * (((p.1 - p.2 : ℕ) : ℕ) : ℝ) + c := by
      intro p hp
      have := mem_entries.1 hp
      simp only [side]
      rw [Nat.cast_sub (by omega)]
      ring
    have hv' : ∀ p ∈ entries N, a * (((p.1 - p.2 : ℕ) : ℕ) : ℝ) + c ≠ 0 := by
      intro p hp; rw [← e p hp]; exact hv p hp
    have f1 : (entries N).filter (fun p => 0 < side a (-a) c p) =
        (entries N).filter (fun p => 0 < a * (((p.1 - p.2 : ℕ) : ℕ) : ℝ) + c) :=
      Finset.filter_congr (fun p hp => by rw [e p hp])
    have f2 : (entries N).filter (fun p => side a (-a) c p < 0) =
        (entries N).filter (fun p => a * (((p.1 - p.2 : ℕ) : ℕ) : ℝ) + c < 0) :=
      Finset.filter_congr (fun p hp => by rw [e p hp])
    rw [f1, f2]
    exact cut N (fun p => p.1 - p.2) (fun p hp => by have := mem_entries.1 hp; omega)
      a c ha hv' (anti_key N hN)
  rcases lt_trichotomy (a * b) 0 with h | h | h
  · exact h2 N hN a b c h hab hv
  · exact absurd h (mul_ne_zero ha hb)
  · exact h1 N hN a b c h hv

end OMA.R_mse_4815847_R2
