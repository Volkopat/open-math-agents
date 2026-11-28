import OMAStatements.S_oeis_a268255

namespace OMA.A268255Proof
open OMA.S_oeis_a268255 PowerSeries

abbrev Letter := Fin 3
def Good {n : ℕ} (seen : Letter → Prop) (x : Fin (n+1) → Letter) : Prop :=
  ∀ i : Fin n, x i.castSucc = x i.succ → ∀ w < x i.castSucc, seen w ∨
    ∃ j : Fin n, j < i ∧ x j.castSucc = x j.succ ∧ x j.castSucc = w

theorem good_step {n : ℕ} (seen : Letter → Prop) (x : Fin (n+2) → Letter) :
    Good seen x ↔ (x 0 = x (Fin.succ 0) → ∀ w < x 0, seen w) ∧
      Good (fun w => seen w ∨ x 0 = x (Fin.succ 0) ∧ x 0 = w) (Fin.tail x) := by
  unfold Good
  rw [Fin.forall_fin_succ]
  apply and_congr
  · simp
  · apply forall_congr'; intro i
    simp only [Fin.exists_fin_succ, Fin.castSucc_zero, Fin.succ_pos, true_and,
      Fin.succ_lt_succ_iff, Fin.tail, Fin.castSucc_succ, or_assoc]

private theorem cons_step {n : ℕ} (t : ℕ) (c b : Letter) (z : Fin n → Letter) :
    Good (fun w => w.val < t) (Fin.cons c (Fin.cons b z)) ↔
      (c = b → c.val ≤ t) ∧
      Good (fun w => w.val < if c = b then max t (c.val+1) else t) (Fin.cons b z) := by
  rw [good_step]
  simp only [Fin.cons_zero, Fin.cons_succ, Fin.tail_cons]
  by_cases eq : c = b
  · subst b
    simp only [true_implies, if_true, true_and]
    have guard : (∀ w : Letter, w < c → w.val < t) ↔ c.val ≤ t := by
      constructor
      · intro h
        by_contra! hn
        have ht := h ⟨t, by omega⟩ hn
        exact (Nat.lt_irrefl t) ht
      · intro h w hw
        exact lt_of_lt_of_le hw h
    rw [guard]
    apply and_congr_right
    intro hc
    have hp : (fun w : Letter => w.val < t ∨ c = w) =
        (fun w : Letter => w.val < max t (c.val+1)) := by
      funext w
      apply propext
      rw [Fin.ext_iff]
      omega
    rw [hp]
  · simp [eq]

-- Count suffixes after fixing the first symbol and marking all values below t as seen.
private noncomputable def count (n t : ℕ) (c : Letter) : ℤ := by
  classical
  exact ∑ z : Fin n → Letter, if Good (fun w => w.val < t) (Fin.cons c z) then 1 else 0

private theorem split_sum {n : ℕ} (f : (Fin (n+1) → Letter) → ℤ) :
    (∑ x, f x) = ∑ b : Letter, ∑ z : Fin n → Letter, f (Fin.cons b z) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) => Letter)).sum_comp f, Fintype.sum_prod_type]
  rfl

private theorem count_step (n t : ℕ) (c : Letter) :
    count (n+1) t c = ∑ b : Letter, if c = b → c.val ≤ t then
      count n (if c = b then max t (c.val+1) else t) b else 0 := by
  classical
  unfold count
  rw [split_sum]
  apply Finset.sum_congr rfl
  intro b _
  by_cases e : c = b
  · subst b
    by_cases h : c.val ≤ t <;>
      simp only [cons_step, eq_self, true_implies, h, true_and, false_and,
        if_true, if_false, Finset.sum_const_zero]
  · simp only [cons_step, e, false_implies, true_and, if_true, if_false]

private theorem count_full (n : ℕ) (c : Letter) : count n 2 c = 3^n := by
  classical
  have h (z : Fin n → Letter) : Good (fun w => w.val < 2) (Fin.cons c z) := by
    intro i _ w hw
    left
    let x : Fin (n+1) → Letter := Fin.cons c z
    have := (x i.castSucc).isLt
    change w.val < (x i.castSucc).val at hw
    omega
  simp only [count, h, if_true]
  simp [Letter]

private theorem count_zero (t : ℕ) (c : Letter) : count 0 t c = 1 := by
  classical
  simp [count, Good]

-- The first three states have no repeated symbol. The next three have
-- seen a repeated zero. Once one also repeats, every continuation is legal.
private def step (v : Fin 7 → ℤ) : Fin 7 → ℤ :=
  ![v 3 + v 1 + v 2, v 0 + v 2, v 0 + v 1, v 3 + v 4 + v 5,
    v 3 + v 6 + v 5, v 3 + v 4, 3 * v 6]

private noncomputable def counts (n : ℕ) : Fin 7 → ℤ :=
  ![count n 0 0, count n 0 1, count n 0 2, count n 1 0,
    count n 1 1, count n 1 2, 3^n]

private def total (v : Fin 7 → ℤ) : ℤ := v 0 + v 1 + v 2

private theorem counts_step (n : ℕ) : counts (n+1) = step (counts n) := by
  funext i
  fin_cases i
  · change count (n+1) 0 0 = count n 1 0 + count n 0 1 + count n 0 2
    rw [count_step, Fin.sum_univ_three]; rfl
  · change count (n+1) 0 1 = count n 0 0 + count n 0 2
    rw [count_step, Fin.sum_univ_three]
    change count n 0 0 + 0 + count n 0 2 = _
    rw [add_zero]
  · change count (n+1) 0 2 = count n 0 0 + count n 0 1
    rw [count_step, Fin.sum_univ_three]
    change count n 0 0 + count n 0 1 + 0 = _
    rw [add_zero]
  · change count (n+1) 1 0 = count n 1 0 + count n 1 1 + count n 1 2
    rw [count_step, Fin.sum_univ_three]; rfl
  · change count (n+1) 1 1 = count n 1 0 + 3^n + count n 1 2
    rw [count_step, Fin.sum_univ_three, ← count_full n 1]; rfl
  · change count (n+1) 1 2 = count n 1 0 + count n 1 1
    rw [count_step, Fin.sum_univ_three]
    change count n 1 0 + count n 1 1 + 0 = _
    rw [add_zero]
  · change (3:ℤ)^(n+1) = 3*3^n
    exact pow_succ' _ _

private theorem atotal (n : ℕ) : (a n : ℤ) = total (counts n) := by
  classical
  have eq (x : Fin (n+1) → Letter) : RepeatsInOrder x ↔ Good (fun w => w.val < 0) x := by
    simp [Good, RepeatsInOrder, RepeatAt]
  unfold a
  rw [Finset.card_filter]
  push_cast
  simp only [eq]
  rw [split_sum]
  simp only [Fin.sum_univ_three]
  rfl

private theorem step_identity (v : Fin 7 → ℤ) :
    total (step (step (step (step v)))) = 7*total (step (step (step v))) -
    15*total (step (step v)) + 7*total (step v) + 6*total v := by
  simp [total, step]
  ring

private theorem rec_count (n : ℕ) : (a (n+4) : ℤ) =
    7 * a (n+3) - 15 * a (n+2) + 7 * a (n+1) + 6 * a n := by
  simp only [atotal, counts_step]
  exact step_identity _

private theorem initial :
    (a 0 : ℤ) = 3 ∧ (a 1 : ℤ) = 7 ∧ (a 2 : ℤ) = 17 ∧ (a 3 : ℤ) = 42 := by
  rw [atotal, atotal, atotal, atotal]
  change total (counts 0) = 3 ∧ total (counts (0+1)) = 7 ∧
    total (counts ((0+1)+1)) = 17 ∧ total (counts (((0+1)+1)+1)) = 42
  simp only [counts_step]
  simp only [counts, count_zero, pow_zero]
  decide

private theorem rec_scalar (K : Type*) [Field K] [CharZero K] (n : ℕ) :
    (a (n+4) : K) = 7*a (n+3) - 15*a (n+2) + 7*a (n+1) + 6*a n := by
  exact_mod_cast rec_count n

private theorem starts : a 0 = 3 ∧ a 1 = 7 ∧ a 2 = 17 ∧ a 3 = 42 ∧ a 4 = 106 := by
  obtain ⟨h0,h1,h2,h3⟩ := initial
  have h4 := rec_count 0
  norm_num at h4
  omega

private noncomputable def closed (n : ℕ) : ℝ :=
  2^n + 3^n/2 + (3/4-1/Real.sqrt 2)*(1-Real.sqrt 2)^n +
    (3/4+1/Real.sqrt 2)*(1+Real.sqrt 2)^n

private theorem geometric_rec (r : ℝ) (n : ℕ)
    (h : (r-2)*(r-3)*((r-1)^2-2) = 0) :
    r^(n+4) = 7*r^(n+3) - 15*r^(n+2) + 7*r^(n+1) + 6*r^n := by
  simp only [pow_add]
  linear_combination r^n * h

private theorem closed_rec (n : ℕ) : closed (n+4) =
    7*closed (n+3) - 15*closed (n+2) + 7*closed (n+1) + 6*closed n := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hm := geometric_rec (1-Real.sqrt 2) n (by
    have e : (1-Real.sqrt 2-1)^2-2=0 := by
      rw [show 1-Real.sqrt 2-1 = -Real.sqrt 2 by ring, neg_sq, hs]; norm_num
    rw [e, mul_zero])
  have hp := geometric_rec (1+Real.sqrt 2) n (by
    have e : (1+Real.sqrt 2-1)^2-2=0 := by
      rw [show 1+Real.sqrt 2-1 = Real.sqrt 2 by ring, hs]; norm_num
    rw [e, mul_zero])
  unfold closed
  linear_combination geometric_rec 2 n (by norm_num) + (1/2) * geometric_rec 3 n (by norm_num) +
    (3/4-1/Real.sqrt 2)*hm + (3/4+1/Real.sqrt 2)*hp

private theorem formula (n : ℕ) : (a n : ℝ) = closed n := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hp : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hi : 1 / Real.sqrt 2 = Real.sqrt 2 / 2 := by
    field_simp
    nlinarith
  have h3 : Real.sqrt 2 ^ 3 = 2 * Real.sqrt 2 := by rw [pow_succ,hs]
  have h4 : Real.sqrt 2 ^ 4 = 4 := by rw [show (4:ℕ)=2*2 by decide,pow_mul,hs]; norm_num
  obtain ⟨a0,a1,a2,a3,_⟩ := starts
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _|_|_|_|n
    all_goals first
      | solve | norm_num [a0,a1,a2,a3,closed,hi] <;> ring_nf <;> norm_num [h4,h3,hs] <;> ring
      | skip
    rw [rec_scalar ℝ n, closed_rec n]
    rw [ih (n+3) (by omega), ih (n+2) (by omega), ih (n+1) (by omega), ih n (by omega)]

private theorem series_formula :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((1-2*X)*(1-3*X)*(1-2*X-X^2)) = X*(7-32*X+28*X^2+18*X^3) := by
  let F := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ))
  change F * _ = _
  have e : F*((1-2*X)*(1-3*X)*(1-2*X-X^2)) =
      F + (C (-7:ℚ) * F + (C (15:ℚ) * F + (C (-7:ℚ) * F + (C (-6:ℚ) * F)*X)*X)*X)*X := by
    simp only [map_neg, map_ofNat]; ring
  rw [e]
  have g : X*(7-32*X+28*X^2+18*X^3) =
      (C (7:ℚ) + (C (-32:ℚ) + (C (28:ℚ) + C (18:ℚ)*X)*X)*X)*X := by
    simp only [map_neg, map_ofNat]
    ring
  rw [g]
  ext n
  obtain ⟨a0,a1,a2,a3,a4⟩ := starts
  rcases n with _|_|_|_|_|n
  all_goals simp only [map_add, coeff_C_mul, coeff_succ_mul_X, coeff_zero_mul_X, coeff_C,
    F, coeff_mk, Nat.succ_ne_zero, if_false, if_true]
  all_goals norm_num [a0,a1,a2,a3,a4]
  have hr := rec_scalar ℚ (n+1)
  linarith

end OMA.A268255Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a268255.main := by
  exact ⟨OMA.A268255Proof.series_formula, fun n _ => OMA.A268255Proof.formula n⟩
