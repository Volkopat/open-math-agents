import OMAStatements.S_oeis_a251269
import Mathlib

-- Credit: @sntntHb (the owner of the agent is credited as the solver)
-- Sketch: transfer matrix over columns; the characteristic polynomial kills the state vector
-- (checked at j = 0 by decide +kernel, then by induction), giving the recurrence; closed form by
-- strong induction and the g.f. by comparing coefficients.

namespace OMA.P_oeis_a251269

open OMA.S_oeis_a251269 PowerSeries

abbrev R := Fin 2 × Fin 2 × Fin 2

/-- Compatibility of consecutive columns c, d (column sums of vertical windows do not drop). -/
def T (c d : R) : Prop :=
  c.2.1.val + c.1.val ≤ d.2.1.val + d.1.val ∧ c.2.2.val + c.2.1.val ≤ d.2.2.val + d.2.1.val

instance (c d : R) : Decidable (T c d) := by unfold T; infer_instance

def Good (n : ℕ) (B : Fin n → R) : Prop :=
  ∀ j (h : j + 1 < n), T (B ⟨j, by omega⟩) (B ⟨j + 1, h⟩)

noncomputable instance (n : ℕ) : DecidablePred (Good n) := Classical.decPred _

def U : ℕ → R → ℕ
  | 0, _ => 1
  | j + 1, s => ∑ t, if T s t then U j t else 0

lemma Ustep (j : ℕ) (s : R) : U (j + 1) s = ∑ t, if T s t then U j t else 0 := rfl

noncomputable def cnt (m : ℕ) (s : R) : ℕ :=
  (Finset.univ.filter (fun B : Fin (m + 1) → R => Good (m + 1) B ∧ B 0 = s)).card

lemma cons0 {k : ℕ} (s : R) (C : Fin k → R) (h : 0 < k + 1) :
    (Fin.cons s C : Fin (k + 1) → R) ⟨0, h⟩ = s := Fin.cons_zero ..

lemma consS {k : ℕ} (s : R) (C : Fin k → R) (j : ℕ) (h : j + 1 < k + 1) :
    (Fin.cons s C : Fin (k + 1) → R) ⟨j + 1, h⟩ = C ⟨j, by omega⟩ := by
  show (Fin.cons s C : Fin (k + 1) → R) (Fin.succ ⟨j, by omega⟩) = _
  exact Fin.cons_succ ..

lemma good_cons (m : ℕ) (s : R) (C : Fin (m + 1) → R) :
    Good (m + 2) (Fin.cons s C : Fin (m + 2) → R) ↔ T s (C 0) ∧ Good (m + 1) C := by
  constructor
  · intro h
    refine ⟨?_, fun j hj => ?_⟩
    · have := h 0 (by omega)
      rw [cons0, consS] at this
      exact this
    · have := h (j + 1) (by omega)
      rw [consS, consS] at this
      exact this
  · rintro ⟨h0, hg⟩ j hj
    cases j with
    | zero => rw [cons0, consS]; exact h0
    | succ j => rw [consS, consS]; exact hg j (by omega)

lemma cnt_zero (s : R) : cnt 0 s = 1 := by
  unfold cnt
  rw [Finset.card_eq_one]
  refine ⟨fun _ => s, ?_⟩
  ext B
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · rintro ⟨-, h0⟩
    funext i
    obtain rfl : i = 0 := Fin.fin_one_eq_zero i
    exact h0
  · rintro rfl
    exact ⟨fun j hj => by omega, rfl⟩

lemma cnt_succ (m : ℕ) (s : R) : cnt (m + 1) s = ∑ t, if T s t then cnt m t else 0 := by
  classical
  have e : cnt (m + 1) s = (Finset.univ.filter (fun C : Fin (m + 1) → R =>
      Good (m + 1) C ∧ T s (C 0))).card := by
    unfold cnt
    apply Finset.card_nbij' (fun B => Fin.tail B) (fun C => (Fin.cons s C : Fin (m + 2) → R))
    · intro B hB
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hB ⊢
      obtain ⟨hg, h0⟩ := hB
      have hc := Fin.cons_self_tail B
      rw [← hc, good_cons] at hg
      rw [h0] at hg
      exact ⟨hg.2, hg.1⟩
    · intro C hC
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hC ⊢
      exact ⟨(good_cons m s C).2 ⟨hC.2, hC.1⟩, Fin.cons_zero ..⟩
    · intro B hB
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hB
      rw [← hB.2]
      exact Fin.cons_self_tail B
    · intro C _
      exact Fin.tail_cons ..
  rw [e, Finset.card_eq_sum_card_fiberwise (f := fun C : Fin (m + 1) → R => C 0)
    (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.filter_filter]
  split_ifs with h
  · unfold cnt
    congr 1
    apply Finset.filter_congr
    intro C _
    constructor
    · rintro ⟨⟨hg, -⟩, h0⟩; exact ⟨hg, h0⟩
    · rintro ⟨hg, h0⟩; exact ⟨⟨hg, h0 ▸ h⟩, h0⟩
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro C - ⟨⟨-, hq⟩, h0⟩
    exact h (h0 ▸ hq)

lemma cnt_eq_U (m : ℕ) (s : R) : cnt m s = U m s := by
  induction m generalizing s with
  | zero => rw [cnt_zero]; rfl
  | succ m ih => rw [cnt_succ, Ustep]; simp only [ih]

def S (m : ℕ) : ℕ := ∑ s, U m s

lemma card_good (m : ℕ) : (Finset.univ.filter (Good (m + 1))).card = S m := by
  classical
  unfold S
  simp only [← cnt_eq_U]
  unfold cnt
  rw [Finset.card_eq_sum_card_fiberwise (f := fun B : Fin (m + 1) → R => B 0)
    (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.filter_filter]

def tr {n : ℕ} (x : Fin 3 → Fin n → Fin 2) : Fin n → R := fun j => (x 0 j, x 1 j, x 2 j)

lemma cond_iff (n : ℕ) (x : Fin 3 → Fin (n + 1) → Fin 2) :
    (∀ i i' : Fin 3, i'.val = i.val + 1 → ∀ j j' : Fin (n + 1), j'.val = j.val + 1 →
      ¬ (((x i' j').val : ℤ) - (x i j).val < ((x i' j).val : ℤ) - (x i j').val)) ↔
    Good (n + 1) (tr x) := by
  constructor
  · intro h j hj
    have h1 := h 0 1 rfl ⟨j, by omega⟩ ⟨j + 1, hj⟩ rfl
    have h2 := h 1 2 rfl ⟨j, by omega⟩ ⟨j + 1, hj⟩ rfl
    refine ⟨?_, ?_⟩
    · show (x 1 ⟨j, _⟩).val + (x 0 ⟨j, _⟩).val ≤ (x 1 ⟨j + 1, hj⟩).val + (x 0 ⟨j + 1, hj⟩).val
      omega
    · show (x 2 ⟨j, _⟩).val + (x 1 ⟨j, _⟩).val ≤ (x 2 ⟨j + 1, hj⟩).val + (x 1 ⟨j + 1, hj⟩).val
      omega
  · intro h i i' hi j j' hj
    have hlt : j.val + 1 < n + 1 := by have := j'.isLt; omega
    obtain rfl : j' = ⟨j.val + 1, hlt⟩ := Fin.ext hj
    obtain ⟨h1, h2⟩ := h j.val hlt
    have h1' : (x 1 j).val + (x 0 j).val ≤ (x 1 ⟨j.val + 1, hlt⟩).val + (x 0 ⟨j.val + 1, hlt⟩).val :=
      h1
    have h2' : (x 2 j).val + (x 1 j).val ≤ (x 2 ⟨j.val + 1, hlt⟩).val + (x 1 ⟨j.val + 1, hlt⟩).val :=
      h2
    have hi3 := i'.isLt
    rcases (show i.val = 0 ∨ i.val = 1 by omega) with h0 | h0
    · obtain rfl : i = 0 := Fin.ext (by rw [h0]; rfl)
      obtain rfl : i' = 1 := Fin.ext (by rw [hi]; rfl)
      omega
    · obtain rfl : i = 1 := Fin.ext (by rw [h0]; rfl)
      obtain rfl : i' = 2 := Fin.ext (by rw [hi, h0]; rfl)
      omega

lemma a_eq (n : ℕ) : a n = S n := by
  classical
  rw [← card_good]
  unfold a
  apply Finset.card_nbij' (fun x => tr x) (fun B => fun i j => ![(B j).1, (B j).2.1, (B j).2.2] i)
  · intro x hx
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hx ⊢
    exact (cond_iff n x).1 hx
  · intro B hB
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hB ⊢
    rw [cond_iff]
    exact hB
  · intro x _
    funext i j
    fin_cases i <;> rfl
  · intro B _
    funext j
    rfl

set_option maxRecDepth 100000 in
lemma rel0 : ∀ s : R, U 5 s + 14 * U 3 s + 9 * U 1 s = 6 * U 4 s + 16 * U 2 s + 2 * U 0 s := by
  decide +kernel

lemma rel (j : ℕ) : ∀ s : R, U (j + 5) s + 14 * U (j + 3) s + 9 * U (j + 1) s =
    6 * U (j + 4) s + 16 * U (j + 2) s + 2 * U j s := by
  induction j with
  | zero => exact rel0
  | succ j ih =>
    intro s
    rw [show j + 1 + 5 = (j + 5) + 1 by omega, show j + 1 + 3 = (j + 3) + 1 by omega,
      show j + 1 + 1 = (j + 1) + 1 by omega, show j + 1 + 4 = (j + 4) + 1 by omega,
      show j + 1 + 2 = (j + 2) + 1 by omega]
    simp only [Ustep (j + 5), Ustep (j + 3), Ustep (j + 1), Ustep (j + 4), Ustep (j + 2), Ustep j,
      Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t _
    split_ifs
    · exact ih t
    · simp

lemma Srec (m : ℕ) : S (m + 5) + 14 * S (m + 3) + 9 * S (m + 1) =
    6 * S (m + 4) + 16 * S (m + 2) + 2 * S m := by
  simp only [S, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun s _ => rel m s)

set_option maxRecDepth 100000 in
lemma S0 : S 0 = 8 := by decide +kernel
set_option maxRecDepth 100000 in
lemma S1 : S 1 = 35 := by decide +kernel
set_option maxRecDepth 100000 in
lemma S2 : S 2 = 114 := by decide +kernel
set_option maxRecDepth 100000 in
lemma S3 : S 3 = 313 := by decide +kernel
set_option maxRecDepth 100000 in
lemma S4 : S 4 = 772 := by decide +kernel

lemma closed (m : ℕ) : (S m : ℚ) =
    8 * (9 * 2 ^ m - 8) - (109 * m) / 3 - 8 * m ^ 2 - (2 * m ^ 3) / 3 := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases (show m < 5 ∨ 5 ≤ m by omega) with h | h
    · interval_cases m <;> simp [S0, S1, S2, S3, S4] <;> norm_num
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + 5 := ⟨m - 5, by omega⟩
      have r' : (S (k + 5) : ℚ) + 14 * S (k + 3) + 9 * S (k + 1) =
          6 * S (k + 4) + 16 * S (k + 2) + 2 * S k := by exact_mod_cast Srec k
      rw [ih k (by omega), ih (k + 1) (by omega), ih (k + 2) (by omega), ih (k + 3) (by omega),
        ih (k + 4) (by omega)] at r'
      push_cast at r' ⊢
      linear_combination r'

lemma ps (f : ℕ → ℚ) (n k : ℕ) :
    PowerSeries.coeff n (PowerSeries.mk f * PowerSeries.X ^ k) = if k ≤ n then f (n-k) else 0 := by
  rw [PowerSeries.coeff_mul_X_pow']; simp

lemma ps1 (f : ℕ → ℚ) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.mk f * PowerSeries.X) = if 1 ≤ n then f (n-1) else 0 := by
  rw [← ps, pow_one]

end OMA.P_oeis_a251269

open OMA.S_oeis_a251269 OMA.P_oeis_a251269 PowerSeries

set_option maxRecDepth 100000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a251269.main := by
  have hcl : ∀ n : ℕ, (a n : ℚ) =
      8 * (9 * 2 ^ n - 8) - (109 * n) / 3 - 8 * n ^ 2 - (2 * n ^ 3) / 3 := fun n => by
    rw [a_eq]; exact closed n
  have hrec : ∀ n : ℕ, 6 ≤ n → (a n : ℚ) = 6 * a (n - 1) - 14 * a (n - 2) + 16 * a (n - 3) -
      9 * a (n - 4) + 2 * a (n - 5) := by
    intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 6 := ⟨n - 6, by omega⟩
    simp only [show k + 6 - 1 = (k + 5) by omega, show k + 6 - 2 = (k + 4) by omega,
      show k + 6 - 3 = (k + 3) by omega, show k + 6 - 4 = k + 2 by omega,
      show k + 6 - 5 = k + 1 by omega, show k + 6 = (k + 1) + 5 by omega, a_eq]
    have := Srec (k + 1)
    have h' : (S (k + 1 + 5) : ℚ) + 14 * S (k + 1 + 3) + 9 * S (k + 1 + 1) =
        6 * S (k + 1 + 4) + 16 * S (k + 1 + 2) + 2 * S (k + 1) := by exact_mod_cast this
    simp only [show k + 1 + 4 = k + 5 by omega, show k + 1 + 3 = k + 4 by omega,
      show k + 1 + 2 = k + 3 by omega, show k + 1 + 1 = k + 2 by omega] at h'
    linear_combination h'
  refine ⟨?_, fun n _ => hcl n⟩
  rw [show ((1 - X) ^ 4 * (1 - 2 * X) : PowerSeries ℚ) = 1 - C (6:ℚ) * X + C (14:ℚ) * X ^ 2 -
      C (16:ℚ) * X ^ 3 + C (9:ℚ) * X ^ 4 - C (2:ℚ) * X ^ 5 by
      simp only [map_ofNat]; ring,
    show (X * (35 - 96 * X + 119 * X ^ 2 - 70 * X ^ 3 + 16 * X ^ 4) : PowerSeries ℚ) =
      C (35:ℚ) * X - C (96:ℚ) * X ^ 2 + C (119:ℚ) * X ^ 3 - C (70:ℚ) * X ^ 4 + C (16:ℚ) * X ^ 5 by
      simp only [map_ofNat]; ring]
  ext n
  simp only [mul_add, mul_sub, mul_one, map_add, map_sub, mul_left_comm _ (PowerSeries.C _),
    PowerSeries.coeff_C_mul, ps, ps1, PowerSeries.coeff_X, PowerSeries.coeff_mk,
    PowerSeries.coeff_X_pow]
  have v1 : (a 1 : ℚ) = 35 := by rw [hcl]; norm_num
  have v2 : (a 2 : ℚ) = 114 := by rw [hcl]; norm_num
  have v3 : (a 3 : ℚ) = 313 := by rw [hcl]; norm_num
  have v4 : (a 4 : ℚ) = 772 := by rw [hcl]; norm_num
  have v5 : (a 5 : ℚ) = 1775 := by rw [hcl]; norm_num
  rcases (show n ≤ 5 ∨ 6 ≤ n by omega) with h | h
  · interval_cases n <;> simp only [v1, v2, v3, v4, v5] <;> norm_num [v1, v2, v3, v4, v5]
  · have hq := hrec n h
    simp [show n ≠ 0 by omega, show n ≠ 1 by omega, show n ≠ 2 by omega, show n ≠ 3 by omega,
      show n ≠ 4 by omega, show n ≠ 5 by omega,
      show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega, show 4 ≤ n by omega,
      show 5 ≤ n by omega,
      show n - 1 ≠ 0 by omega, show n - 2 ≠ 0 by omega, show n - 3 ≠ 0 by omega,
      show n - 4 ≠ 0 by omega, show n - 5 ≠ 0 by omega]
    rw [hq]; ring


