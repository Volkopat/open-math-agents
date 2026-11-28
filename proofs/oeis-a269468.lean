import OMAStatements.S_oeis_a269468
import Mathlib

open OMA.S_oeis_a269468
open PowerSeries

namespace P269468

open Finset

def cnt (N : ℕ) : ℕ → (List ℕ → Bool) → ℕ
  | 0, P => if P [] then 1 else 0
  | L + 1, P => ∑ a ∈ range N, cnt N L (fun t => P (a :: t))

lemma card_cnt (N : ℕ) : ∀ (L : ℕ) (P : List ℕ → Bool),
    ((Fintype.piFinset fun _ : Fin L => range N).filter (fun v => P (List.ofFn v) = true)).card = cnt N L P
  | 0, P => by
    rw [cnt]
    by_cases h : P [] = true
    · rw [if_pos h]
      rw [Finset.filter_true_of_mem (fun v _ => by simpa [List.ofFn_zero] using h)]
      simp
    · rw [if_neg h, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro v _; simpa [List.ofFn_zero] using h
  | L + 1, P => by
    rw [cnt, Finset.card_filter]
    have e := Finset.filter_piFinset_eq_map_consEquiv (fun _ : Fin (L + 1) => range N) (fun _ => True)
    rw [Finset.filter_true_of_mem (fun _ _ => trivial), Finset.filter_true_of_mem (fun _ _ => trivial)] at e
    rw [e, Finset.sum_map, Finset.sum_product]
    apply Finset.sum_congr rfl
    intro a _
    rw [← card_cnt N L (fun t => P (a :: t)), Finset.card_filter]
    apply Finset.sum_congr rfl
    intro t _
    simp [List.ofFn_succ, Fin.consEquiv]

lemma cnt_congr (N L : ℕ) (P Q : List ℕ → Bool) (h : ∀ l, P l = Q l) : cnt N L P = cnt N L Q := by
  have : P = Q := funext h
  rw [this]

lemma cnt_false (N : ℕ) : ∀ L, cnt N L (fun _ => false) = 0
  | 0 => by simp [cnt]
  | L + 1 => by simp [cnt, cnt_false N L]

lemma cnt_split (N : ℕ) : ∀ (L : ℕ) (P Q : List ℕ → Bool),
    (cnt N L (fun l => P l && Q l) : ℤ) + cnt N L (fun l => P l && !Q l) = cnt N L P
  | 0, P, Q => by
    simp only [cnt]
    by_cases hP : P [] = true <;> by_cases hQ : Q [] = true <;> simp [hP, hQ]
  | L + 1, P, Q => by
    simp only [cnt]
    push_cast
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    exact cnt_split N L (fun t => P (a :: t)) (fun t => Q (a :: t))

def good (l : List ℕ) : Prop := (repVals l).IsChain (· ≠ ·)
instance instGood (l : List ℕ) : Decidable (good l) := by unfold good; infer_instance

def fr (l : List ℕ) : Option ℕ := (repVals l).head?

lemma good1 (b : ℕ) : good [b] := by simp [good, repVals]
lemma fr1 (b : ℕ) : fr [b] = none := by simp [fr, repVals]

lemma good2 (h b : ℕ) (t : List ℕ) : good (h :: b :: t) ↔ good (b :: t) ∧ ¬ (b = h ∧ fr (b :: t) = some h) := by
  simp only [good, fr, repVals]
  split_ifs with hb
  · subst hb
    rw [List.singleton_append, List.isChain_cons]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h2, fun ⟨_, h3⟩ => h1 b ?_ rfl⟩
      simp [h3]
    · rintro ⟨h2, h3⟩
      refine ⟨fun y hy => ?_, h2⟩
      intro hby; subst hby
      exact h3 ⟨rfl, by simpa using hy⟩
  · simp [hb]

lemma fr2 (h b : ℕ) (t : List ℕ) : fr (h :: b :: t) = if b = h then some b else fr (b :: t) := by
  simp only [fr, repVals]
  split_ifs <;> simp

def T (N L b : ℕ) : ℕ := cnt N L (fun t => decide (good (b :: t)))
def C (N L b c : ℕ) : ℕ := cnt N L (fun t => decide (good (b :: t) ∧ fr (b :: t) = some c))

def V (N : ℤ) : ℕ → ℤ × ℤ × ℤ
  | 0 => (1, 0, 0)
  | L + 1 => ((N * (V N L).1 - (V N L).2.1), (V N L).1 - (V N L).2.1 + (N - 1) * (V N L).2.2,
      (V N L).2.1 + (N - 2) * (V N L).2.2)

lemma sum2 (N h : ℕ) (hh : h < N) (X Z : ℤ) :
    ∑ b ∈ range N, (if b = h then X else Z) = X + ((N : ℤ) - 1) * Z := by
  rw [Finset.sum_congr rfl (fun b _ => show (if b = h then X else Z) = Z + (if b = h then X - Z else 0) by
    split_ifs <;> ring), Finset.sum_add_distrib, Finset.sum_const, Finset.sum_ite_eq']
  simp [hh]; ring

lemma sum3 (N h c : ℕ) (hh : h < N) (hc : c < N) (hne : h ≠ c) (X Y Z : ℤ) :
    ∑ b ∈ range N, (if b = h then X else if b = c then Y else Z) = X + Y + ((N : ℤ) - 2) * Z := by
  rw [Finset.sum_congr rfl (fun b _ => show (if b = h then X else if b = c then Y else Z) =
    Z + (if b = h then X - Z else 0) + (if b = c then Y - Z else 0) by
    split_ifs <;> first | (exfalso; omega) | ring), Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_const, Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp [hh, hc]; ring

lemma E_eq (N L h : ℕ) : (cnt N L (fun t => decide (good (h :: t)) && !decide (fr (h :: t) = some h)) : ℤ) =
    T N L h - C N L h h := by
  have := cnt_split N L (fun t => decide (good (h :: t))) (fun t => decide (fr (h :: t) = some h))
  have e : cnt N L (fun t => decide (good (h :: t)) && decide (fr (h :: t) = some h)) = C N L h h := by
    unfold C; apply cnt_congr; intro l; simp [Bool.decide_and]
  unfold T; rw [e] at this; linarith

lemma closed (N : ℕ) : ∀ L, ∀ b < N, (T N L b : ℤ) = (V N L).1 ∧
    ∀ c < N, (C N L b c : ℤ) = if c = b then (V N L).2.1 else (V N L).2.2
  | 0, b, _ => by
    refine ⟨by simp [T, cnt, good1, V], fun c _ => ?_⟩
    simp [C, cnt, fr1, V]
  | L + 1, h, hh => by
    have IH := closed N L
    refine ⟨?_, fun c hc => ?_⟩
    · unfold T; rw [cnt]; push_cast
      rw [Finset.sum_congr rfl (fun b hb => show (cnt N L (fun t => decide (good (h :: b :: t))) : ℤ) =
          if b = h then (V N L).1 - (V N L).2.1 else (V N L).1 by
        simp only [Finset.mem_range] at hb
        split_ifs with hbh
        · subst hbh
          rw [cnt_congr N L _ (fun t => decide (good (b :: t)) && !decide (fr (b :: t) = some b)) (fun t => by
            simp [good2]), E_eq, (IH b hb).1, (IH b hb).2 b hb, if_pos rfl]
        · rw [cnt_congr N L _ (fun t => decide (good (b :: t))) (fun t => by simp [good2, hbh])]
          exact (IH b hb).1)]
      rw [sum2 N h hh]; simp only [V]; ring
    · unfold C; rw [cnt]; push_cast
      rw [Finset.sum_congr rfl (fun b hb => show (cnt N L (fun t => decide (good (h :: b :: t) ∧ fr (h :: b :: t) = some c)) : ℤ) =
          if b = h then (if c = h then (V N L).1 - (V N L).2.1 else 0) else
            (if c = b then (V N L).2.1 else (V N L).2.2) by
        simp only [Finset.mem_range] at hb
        split_ifs with hbh hch hcb
        · rw [hbh, hch]
          rw [cnt_congr N L _ (fun t => decide (good (h :: t)) && !decide (fr (h :: t) = some h)) (fun t => by
            simp [good2, fr2]), E_eq, (IH h hh).1, (IH h hh).2 h hh, if_pos rfl]
        · rw [hbh]
          rw [cnt_congr N L _ (fun _ => false) (fun t => by simp [good2, fr2]; intro _ _ h1; exact hch h1.symm), cnt_false]
          simp
        · rw [cnt_congr N L _ (fun t => decide (good (b :: t) ∧ fr (b :: t) = some c)) (fun t => by simp [good2, fr2, hbh])]
          exact ((IH b hb).2 c hc).trans (if_pos hcb)
        · rw [cnt_congr N L _ (fun t => decide (good (b :: t) ∧ fr (b :: t) = some c)) (fun t => by simp [good2, fr2, hbh])]
          exact ((IH b hb).2 c hc).trans (if_neg hcb))]
      split_ifs with hch
      · subst hch
        have e : ∀ x ∈ range N, (if x = c then (V N L).1 - (V N L).2.1 else
            if c = x then (V N L).2.1 else (V N L).2.2) = (if x = c then (V N L).1 - (V N L).2.1 else (V N L).2.2) := by
          intro x _; split_ifs <;> first | (exfalso; omega) | rfl
        rw [Finset.sum_congr rfl e, sum2 N c hh]; simp only [V]; try ring
      · have e : ∀ x ∈ range N, (if x = h then 0 else if c = x then (V N L).2.1 else (V N L).2.2) =
            (if x = h then 0 else if x = c then (V N L).2.1 else (V N L).2.2) := by
          intro x _; split_ifs <;> first | (exfalso; omega) | rfl
        rw [Finset.sum_congr rfl e, sum3 N h c hh hc (Ne.symm hch)]; simp only [V]; try ring

lemma total (N L : ℕ) : (cnt N (L + 1) (fun l => decide (good l)) : ℤ) = N * (V N L).1 := by
  rw [cnt]; push_cast
  rw [Finset.sum_congr rfl (fun b hb => show (cnt N L (fun t => decide (good (b :: t))) : ℤ) = (V N L).1 from
    (closed N L b (Finset.mem_range.mp hb)).1)]
  simp

lemma a_eq (n : ℕ) : (a n : ℚ) = (1) * ((n : ℚ) + 1) ^ 1 + (-2) * ((n : ℚ) + 1) ^ 2 + (1) * ((n : ℚ) + 1) ^ 4 := by
  have h1 : a n = cnt (n + 1) 4 (fun l => decide (good l)) := by
    unfold a
    rw [← card_cnt]
    congr 1
    apply Finset.filter_congr
    intro v _
    simp [good]
  have h2 := total (n + 1) 3
  rw [← h1] at h2
  simp only [V] at h2
  have h3 : (a n : ℚ) = ((a n : ℤ) : ℚ) := by norm_cast
  rw [h3, h2]
  push_cast
  ring

end P269468

theorem OMA.solution : type_of% @OMA.S_oeis_a269468.main := by
  have hq : ∀ F : PowerSeries ℚ, F * (1 - X) ^ 5 = F - C (5 : ℚ) * (F * X ^ 1) + C (10 : ℚ) * (F * X ^ 2) - C (10 : ℚ) * (F * X ^ 3) + C (5 : ℚ) * (F * X ^ 4) - (F * X ^ 5) := by
    intro F; simp only [map_ofNat]; ring
  have hr : (2 * X * (5 + 8 * X - X ^ 2) : PowerSeries ℚ) = C (10 : ℚ) * X ^ 1 + C (16 : ℚ) * X ^ 2 - C (2 : ℚ) * X ^ 3 := by
    simp only [map_ofNat, map_one, pow_one]; ring
  rw [hq, hr]
  ext n
  simp only [map_add, map_sub, map_neg, coeff_mul_X_pow', coeff_C_mul, coeff_mk, coeff_C_mul_X_pow, coeff_X_pow, coeff_one, coeff_C]
  by_cases hn : n < 5
  · interval_cases n <;> norm_num [P269468.a_eq]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    simp only [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega, show m + 5 - 3 = m + 2 by omega, show m + 5 - 4 = m + 1 by omega, show m + 5 - 5 = m + 0 by omega, show 1 ≤ m + 5 by omega, show 2 ≤ m + 5 by omega, show 3 ≤ m + 5 by omega, show 4 ≤ m + 5 by omega, show 5 ≤ m + 5 by omega, show m + 5 ≠ 0 by omega, show m + 5 ≠ 1 by omega, show m + 5 ≠ 2 by omega, show m + 5 ≠ 3 by omega, if_true, if_false]
    simp only [P269468.a_eq]; push_cast; ring
