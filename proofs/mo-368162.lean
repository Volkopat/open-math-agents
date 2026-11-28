import OMAStatements.S_mo_368162
import Mathlib.Data.Nat.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

-- Problem: A sequence reminiscent of Fibonacci's recursion.
-- Source: https://mathoverflow.net/questions/368162
-- Paseman's answer gives the displacement recurrence and conjectures the growth error.
-- Credit: @mmexicann

open OMA.S_mo_368162

private theorem a_zero : a 0 = 0 := rfl
private theorem a_one : a 1 = 1 := rfl

-- The settled prefix is fixed, and each moved future entry carries an earlier gap.
private structure Stage (k : ℕ) : Prop where
  settled : ∀ i, i ≤ k + 1 → row k i = a i
  largest : ∀ i, i ≤ k + 1 → a i ≤ a (k + 1)
  lower : k + 1 ≤ a (k + 1)
  gap : ∀ i, 2 ≤ i → i ≤ k + 1 → a (i - 1) + 2 ≤ a i
  untouched : ∀ i, k + 1 < i → (∀ j, j ≤ k + 1 → a j ≠ i) → row k i = i
  carried : ∀ j, j ≤ k + 1 → k + 1 < a j → row k (a j) = a j - a (j - 1)

private theorem stage_zero : Stage 0 := by
  constructor
  · intro i hi
    have h : i - 1 = 0 := by omega
    simp [a, h]
  · intro i hi
    by_cases h : i = 0
    · simp [h, a_zero, a_one]
    · have hi' : i = 1 := by omega
      simp [hi']
  · decide
  · omega
  · intros
    rfl
  · intro j hj h
    by_cases h0 : j = 0
    · simp [h0, a_zero] at h
    · have h1 : j = 1 := by omega
      simp [h1, a_one] at h

private theorem extend {k : ℕ} (s : Stage k) :
    Stage (k + 1) ∧ a (k + 2) = a (k + 1) + row k (k + 2) := by
  let p := k + 2
  let x := row k p
  let q := a (k + 1) + x
  have hx : 2 ≤ x := by
    by_cases h : ∃ j, j ≤ k + 1 ∧ a j = p
    · obtain ⟨j, hj, he⟩ := h
      have hpos : 2 ≤ j := by
        by_contra hn
        by_cases h0 : j = 0
        · simp [h0, a_zero, p] at he
        · have h1 : j = 1 := by omega
          simp [h1, a_one, p] at he
      have hi : k + 1 < a j := by rw [he]; omega
      have hcarry := s.carried j hj hi
      have hgap := s.gap j hpos hj
      rw [he] at hcarry
      change 2 ≤ row k p
      omega
    · have hnot : ∀ j, j ≤ k + 1 → a j ≠ p := fun j hj he => h ⟨j, hj, he⟩
      change 2 ≤ row k p
      rw [s.untouched p (by omega) hnot]
      omega
  have hpq : p < q := by
    dsimp [p, q]
    exact calc
      k + 2 < (k + 1) + x := by omega
      _ ≤ a (k + 1) + x := Nat.add_le_add_right s.lower x
  have hqMax : a (k + 1) < q := by dsimp [q]; omega
  have hfresh : ∀ j, j ≤ k + 1 → a j ≠ q :=
    fun j hj => ne_of_lt (lt_of_le_of_lt (s.largest j hj) hqMax)
  have hq : row k q = q := s.untouched q (by omega) hfresh
  have hrow (i : ℕ) : row (k + 1) i =
      if i = p then q else if i = q then x else row k i := by
    rw [row]
    change (if i = p then row k (row k (k + 1) + x) else
      if i = row k (k + 1) + x then x else row k i) = _
    rw [s.settled (k + 1) le_rfl]
    change (if i = p then row k q else if i = q then x else row k i) = _
    rw [hq]
  have ha : a p = q := by
    have he : p - 1 = k + 1 := by omega
    unfold a
    rw [he, hrow]
    simp
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ha⟩
  · intro i hi
    by_cases he : i = p
    · subst i
      exact (hrow p).trans (by simp [ha])
    · rw [hrow]
      simp [he, show i ≠ q by omega, s.settled i (by omega)]
  · intro i hi
    change a i ≤ a p
    rw [ha]
    by_cases he : i = p
    · simp [he, ha]
    · exact (s.largest i (by omega)).trans hqMax.le
  · change p ≤ a p
    exact ha ▸ hpq.le
  · intro i hi₂ hi
    by_cases he : i = p
    · subst i
      have hpred : p - 1 = k + 1 := by omega
      rw [hpred, ha]
      dsimp [q]
      omega
    · exact s.gap i hi₂ (by omega)
  · intro i hi hf
    have hp : i ≠ p := by omega
    have hne : i ≠ q := by
      intro he
      exact hf p (by omega) (ha.trans he.symm)
    rw [hrow]
    simp [hp, hne, s.untouched i (by omega) fun j hj => hf j (by omega)]
  · intro j hj h
    by_cases he : j = p
    · subst j
      have hpred : p - 1 = k + 1 := by omega
      rw [hpred, ha, hrow]
      simp [show q ≠ p by omega, q]
    · have hj' : j ≤ k + 1 := by omega
      have hp : a j ≠ p := by omega
      rw [hrow]
      simp [hp, hfresh j hj', s.carried j hj' (by omega)]

private theorem phase (k : ℕ) : Stage k := by
  induction k with
  | zero => exact stage_zero
  | succ k ih => exact (extend ih).1

private theorem step_a (k : ℕ) : a (k + 2) = a (k + 1) + row k (k + 2) :=
  (extend (phase k)).2

private theorem gap_a {n : ℕ} (hn : 2 ≤ n) : a (n - 1) + 2 ≤ a n :=
  (phase (n - 1)).gap n hn (by omega)

private theorem strict_a : StrictMono a := by
  apply strictMono_nat_of_lt_succ
  intro n
  cases n with
  | zero => decide
  | succ n =>
    have h := gap_a (n := n + 2) (by omega)
    have he : n + 2 - 1 = n + 1 := by omega
    rw [he] at h
    exact lt_of_lt_of_le (by omega) h

private theorem omits_two {n : ℕ} (hn : 0 < n) : a n ≠ 2 := by
  by_cases he : n = 1
  · simp [he, a_one]
  · have h2 : a 2 = 3 := by decide
    have h := strict_a.monotone (show 2 ≤ n by omega)
    omega

private theorem default_increment {n : ℕ} (hn : 2 ≤ n) (h : ∀ j, a j ≠ n) :
    a n = a (n - 1) + n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  rw [step_a, (phase k).untouched (k + 2) (by omega) (fun j _ => h j)]
  rfl

private theorem upper_increment (n : ℕ) : a n ≤ a (n - 1) + n := by
  by_cases hn : 2 ≤ n
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    rw [step_a, show k + 2 - 1 = k + 1 by omega]
    apply Nat.add_le_add_left
    by_cases h : ∃ j, j ≤ k + 1 ∧ a j = k + 2
    · obtain ⟨j, hj, he⟩ := h
      have hc := (phase k).carried j hj (by omega)
      rw [he] at hc
      rw [hc]
      exact Nat.sub_le _ _
    · rw [(phase k).untouched (k + 2) (by omega) (fun j hj he => h ⟨j, hj, he⟩)]
  · interval_cases n <;> decide

private theorem consecutive_missing (n : ℕ) :
    (∀ j, a j ≠ n + 1) ∨ (∀ j, a j ≠ n + 2) := by
  by_cases hit : ∃ j, a j = n + 1
  · obtain ⟨i, hi⟩ := hit
    right
    intro j hj
    have hij : i < j := by
      apply strict_a.lt_iff_lt.mp
      omega
    have hj₂ : 2 ≤ j := by
      by_contra hc
      interval_cases j
      · simp [a_zero] at hj
      · simp [a_one] at hj
    have hgap := gap_a hj₂
    have hmono := strict_a.monotone (show i ≤ j - 1 by omega)
    omega
  · exact Or.inl (fun j hj => hit ⟨j, hj⟩)

private theorem pair_step {n : ℕ} (hn : 1 ≤ n) : a n + (n + 1) ≤ a (n + 2) := by
  obtain h | h := consecutive_missing n
  · have he := default_increment (n := n + 1) (by omega) h
    have hle := strict_a.monotone (show n + 1 ≤ n + 2 by omega)
    rw [Nat.add_sub_cancel] at he
    omega
  · have he := default_increment (n := n + 2) (by omega) h
    have hle := strict_a.monotone (show n ≤ n + 2 - 1 by omega)
    omega

private theorem odd_lower (m : ℕ) : m ^ 2 ≤ a (2 * m + 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h := pair_step (n := 2 * m + 1) (by omega)
    rw [show 2 * (m + 1) + 1 = 2 * m + 1 + 2 by omega]
    nlinarith

private theorem square_bound (n : ℕ) : n ^ 2 ≤ 16 * a n := by
  by_cases hn : n ≤ 2
  · interval_cases n <;> decide
  let m := (n - 1) / 2
  have hn' : 2 * m + 1 ≤ n := by dsimp [m]; omega
  have hnm : n ≤ 4 * m := by dsimp [m]; omega
  have hlow : m ^ 2 ≤ a n := (odd_lower m).trans (strict_a.monotone hn')
  calc
    n ^ 2 ≤ (4 * m) ^ 2 := Nat.pow_le_pow_left hnm 2
    _ = 16 * m ^ 2 := by ring
    _ ≤ 16 * a n := Nat.mul_le_mul_left 16 hlow

-- A default increment contributes its index. Only earlier sequence values can lose mass.
private def loss (n : ℕ) : ℕ := n - (a n - a (n - 1))

private theorem loss_le (n : ℕ) : loss n ≤ n := Nat.sub_le _ _

private theorem loss_hit {n : ℕ} (h : 0 < loss n) : ∃ j, a j = n := by
  have hn : 2 ≤ n := by
    by_contra hc
    interval_cases n <;> exact (by decide : ¬ (0 < loss _)) h
  by_contra hc
  have he := default_increment hn (fun j hj => hc ⟨j, hj⟩)
  unfold loss at h
  omega

private theorem loss_step (n : ℕ) : a (n + 1) + loss (n + 1) = a n + (n + 1) := by
  have hm := strict_a.monotone (show n ≤ n + 1 by omega)
  have hle := upper_increment (n + 1)
  simp only [loss, Nat.add_sub_cancel] at hle ⊢
  omega

private def lossSum (n : ℕ) : ℕ := ∑ i ∈ Finset.range n, loss (i + 1)

private theorem total_formula (n : ℕ) :
    (a n : ℝ) + (lossSum n : ℝ) = (n : ℝ) * ((n : ℝ) + 1) / 2 := by
  induction n with
  | zero => simp [a_zero, lossSum]
  | succ n ih =>
    have hstep : (a (n + 1) : ℝ) + (loss (n + 1) : ℝ) = a n + ((n : ℝ) + 1) := by
      exact_mod_cast loss_step n
    simp only [lossSum, Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
    change (a (n + 1) : ℝ) + ((lossSum n : ℝ) + (loss (n + 1) : ℝ)) =
      ((n : ℝ) + 1) * ((n : ℝ) + 1 + 1) / 2
    nlinarith only [ih, hstep]

private theorem lossSum_bound (n : ℕ) : lossSum n ≤ ((16 * n).sqrt + 1) * n := by
  let hits := (Finset.range n).filter (fun k => 0 < loss (k + 1))
  have hsub : hits ⊆ (Finset.range ((16 * n).sqrt + 1)).image (fun j => a j - 1) := by
    intro i hi
    have hh := Finset.mem_filter.mp hi
    have hi' : i < n := Finset.mem_range.mp hh.1
    obtain ⟨j, hj⟩ := loss_hit hh.2
    have hjbound : j ≤ (16 * n).sqrt := by
      apply Nat.le_sqrt'.mpr
      apply (square_bound j).trans
      rw [hj]
      exact Nat.mul_le_mul_left 16 (by omega)
    apply Finset.mem_image.mpr
    exact ⟨j, Finset.mem_range.mpr (by omega), by omega⟩
  have hcard : hits.card ≤ (16 * n).sqrt + 1 :=
    (Finset.card_le_card hsub).trans (Finset.card_image_le.trans_eq (Finset.card_range _))
  have he : lossSum n = ∑ i ∈ hits, loss (i + 1) := by
    dsimp [lossSum, hits]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs <;> omega
  rw [he]
  calc
    _ ≤ ∑ _i ∈ hits, n := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
      exact (loss_le (i + 1)).trans (by omega)
    _ = hits.card * n := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ hcard

open Filter
open scoped Topology

private theorem loss_normalized (n : ℕ) (hn : 0 < n) :
    (lossSum n : ℝ) / (n : ℝ) ^ 2 ≤ 4 * (n : ℝ) ^ (-(1 / 2) : ℝ) + 1 / (n : ℝ) := by
  let q := (16 * n).sqrt
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hSq : ((q : ℝ) ^ 2) ≤ 16 * (n : ℝ) := by
    exact_mod_cast Nat.sqrt_le' (16 * n)
  have hRoot : Real.sqrt 16 = 4 := by
    rw [Real.sqrt_eq_iff_mul_self_eq (by norm_num) (by norm_num)]
    norm_num
  have hq : (q : ℝ) ≤ 4 * (n : ℝ) ^ (1 / 2 : ℝ) := calc
    _ ≤ Real.sqrt (16 * (n : ℝ)) := Real.le_sqrt_of_sq_le hSq
    _ = _ := by rw [Real.sqrt_mul (by norm_num), hRoot, Real.sqrt_eq_rpow]
  have hl : (lossSum n : ℝ) ≤ ((q : ℝ) + 1) * (n : ℝ) := by
    exact_mod_cast lossSum_bound n
  have hRp : (n : ℝ) ^ (1 / 2 : ℝ) / (n : ℝ) = (n : ℝ) ^ (-(1 / 2) : ℝ) := by
    rw [show (-(1 / 2) : ℝ) = 1 / 2 - 1 by norm_num, Real.rpow_sub hn', Real.rpow_one]
  calc
    _ ≤ ((q : ℝ) + 1) * (n : ℝ) / (n : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right hl (by positivity)
    _ = ((q : ℝ) + 1) / (n : ℝ) := by field_simp [hn'.ne']
    _ ≤ (4 * (n : ℝ) ^ (1 / 2 : ℝ) + 1) / (n : ℝ) :=
      div_le_div_of_nonneg_right (add_le_add hq le_rfl) hn'.le
    _ = _ := by rw [add_div, mul_div_assoc, hRp]

private theorem growth :
    Tendsto (fun n : ℕ => (a n : ℝ) / (n : ℝ) ^ 2) atTop (𝓝 (1 / 2)) := by
  have hinv : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hroot : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 / 2) : ℝ)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp tendsto_natCast_atTop_atTop
  have hbound : Tendsto (fun n : ℕ => 4 * (n : ℝ) ^ (-(1 / 2) : ℝ) + 1 / (n : ℝ)) atTop (𝓝 0) := by
    simpa using (hroot.const_mul 4).add hinv
  have hloss : Tendsto (fun n : ℕ => (lossSum n : ℝ) / (n : ℝ) ^ 2) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbound
    · exact Eventually.of_forall fun n => by positivity
    · exact (eventually_gt_atTop (0 : ℕ)).mono fun n hn => loss_normalized n hn
  have hconst : Tendsto (fun _ : ℕ => (1 / 2 : ℝ)) atTop (𝓝 (1 / 2)) :=
    tendsto_const_nhds
  have hhalf : Tendsto (fun n : ℕ => (1 / 2 : ℝ) * (1 / (n : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using hinv.const_mul (1 / 2 : ℝ)
  have h : Tendsto
      (fun n : ℕ => 1 / 2 + (1 / 2) * (1 / (n : ℝ)) - (lossSum n : ℝ) / (n : ℝ) ^ 2)
      atTop (𝓝 (1 / 2)) := by
    simpa only [add_zero, sub_zero] using (hconst.add hhalf).sub hloss
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have he : (a n : ℝ) = (n : ℝ) * ((n : ℝ) + 1) / 2 - (lossSum n : ℝ) := by
    linarith only [total_formula n]
  rw [he]
  field_simp [hn'.ne']

theorem OMA.solution : type_of% @OMA.S_mo_368162.main := by
  exact ⟨fun n hn k hk => (phase k).settled n (by omega), strict_a,
    fun _ hn => omits_two hn, growth⟩
