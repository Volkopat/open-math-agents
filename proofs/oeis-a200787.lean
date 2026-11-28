import OMAStatements.S_oeis_a200787
import Mathlib


namespace A200787
open Finset

/-- number of surjective arrays onto `Fin k` with the property `Q` -/
def cnt (m : ℕ) (Q : (Fin m → ℕ) → Prop) [DecidablePred Q] (k : ℕ) : ℕ :=
  (univ.filter fun y : Fin m → Fin k => Function.Surjective y ∧ Q (fun i => (y i).val)).card

theorem fib (m N : ℕ) (Q : (Fin m → ℕ) → Prop) [DecidablePred Q]
    (hQ : ∀ x y : Fin m → ℕ, (∀ i j, x i < x j ↔ y i < y j) → (Q x ↔ Q y))
    (S : Finset (Fin N)) :
    cnt m Q S.card =
    ((univ.filter fun x : Fin m → Fin N => Q (fun i => (x i).val)).filter
      fun x => univ.image x = S).card := by
  have hlt : ∀ a b : Fin S.card,
      ((S.orderEmbOfFin rfl a : Fin N).val < (S.orderEmbOfFin rfl b : Fin N).val) ↔
        a.val < b.val := by
    intro a b
    show (S.orderEmbOfFin rfl a) < (S.orderEmbOfFin rfl b) ↔ a < b
    exact OrderEmbedding.lt_iff_lt _
  unfold cnt
  refine Finset.card_bij (fun y _ i => S.orderEmbOfFin rfl (y i)) ?_ ?_ ?_
  · intro y hy
    obtain ⟨-, hsurj, hq⟩ := Finset.mem_filter.1 hy
    refine Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩, ?_⟩
    · exact (hQ (fun i => ((S.orderEmbOfFin rfl (y i) : Fin N)).val) (fun i => (y i).val)
        (fun i j => hlt (y i) (y j))).2 hq
    · ext s
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, rfl⟩
        exact Finset.orderEmbOfFin_mem S rfl (y i)
      · intro hs
        have h2 : s ∈ Set.range (S.orderEmbOfFin rfl) := by
          rw [Finset.range_orderEmbOfFin]; exact hs
        obtain ⟨j, rfl⟩ := h2
        obtain ⟨i, rfl⟩ := hsurj j
        exact ⟨i, rfl⟩
  · intro y1 _ y2 _ h
    funext i
    exact (S.orderEmbOfFin rfl).injective (congrFun h i)
  · intro x hx
    obtain ⟨hx1, himg⟩ := Finset.mem_filter.1 hx
    obtain ⟨-, hq⟩ := Finset.mem_filter.1 hx1
    have hmem : ∀ i, ∃ j, S.orderEmbOfFin rfl j = x i := by
      intro i
      have h1 : x i ∈ S := by
        rw [← himg]; exact Finset.mem_image_of_mem x (Finset.mem_univ i)
      have h2 : x i ∈ Set.range (S.orderEmbOfFin rfl) := by
        rw [Finset.range_orderEmbOfFin]; exact h1
      exact h2
    choose y hy using hmem
    refine ⟨y, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_, ?_⟩, funext hy⟩
    · intro j
      have h1 : S.orderEmbOfFin rfl j ∈ univ.image x := by
        rw [himg]; exact Finset.orderEmbOfFin_mem S rfl j
      obtain ⟨i, -, hi⟩ := Finset.mem_image.1 h1
      exact ⟨i, (S.orderEmbOfFin rfl).injective ((hy i).trans hi)⟩
    · refine (hQ (fun i => (x i).val) (fun i => (y i).val) (fun i j => ?_)).1 hq
      have h3 := hlt (y i) (y j)
      rw [hy i, hy j] at h3
      exact h3

/-- an order-pattern property is counted by a sum of binomials -/
theorem pattern_count (m N : ℕ) (Q : (Fin m → ℕ) → Prop) [DecidablePred Q]
    (hQ : ∀ x y : Fin m → ℕ, (∀ i j, x i < x j ↔ y i < y j) → (Q x ↔ Q y)) :
    (univ.filter fun x : Fin m → Fin N => Q (fun i => (x i).val)).card =
      ∑ k ∈ range (N + 1), N.choose k * cnt m Q k := by
  have h1 := Finset.card_eq_sum_card_fiberwise (f := fun x : Fin m → Fin N => univ.image x)
    (s := univ.filter fun x : Fin m → Fin N => Q (fun i => (x i).val))
    (t := (univ : Finset (Fin N)).powerset)
    (fun x _ => Finset.mem_coe.2 (Finset.mem_powerset.2 (Finset.subset_univ _)))
  rw [h1]
  have h2 : ∀ S ∈ (univ : Finset (Fin N)).powerset,
      ((univ.filter fun x : Fin m → Fin N => Q (fun i => (x i).val)).filter
        fun x => univ.image x = S).card = cnt m Q S.card :=
    fun S _ => (fib m N Q hQ S).symm
  rw [Finset.sum_congr rfl h2, Finset.sum_powerset_apply_card]
  simp only [Finset.card_univ, Fintype.card_fin, smul_eq_mul]

theorem cnt_zero (m : ℕ) (Q : (Fin m → ℕ) → Prop) [DecidablePred Q] (k : ℕ) (hk : m < k) :
    cnt m Q k = 0 := by
  unfold cnt
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro y - ⟨hs, -⟩
  have h := Fintype.card_le_of_surjective y hs
  simp only [Fintype.card_fin] at h
  omega

/-- no two consecutive increases -/
def Q5 (x : Fin 5 → ℕ) : Prop :=
  ¬(x 0 < x 1 ∧ x 1 < x 2) ∧ ¬(x 1 < x 2 ∧ x 2 < x 3) ∧ ¬(x 2 < x 3 ∧ x 3 < x 4)

instance : DecidablePred Q5 := fun x => by unfold Q5; infer_instance

theorem hQ5 (x y : Fin 5 → ℕ) (h : ∀ i j, x i < x j ↔ y i < y j) : Q5 x ↔ Q5 y := by
  unfold Q5
  rw [h 0 1, h 1 2, h 2 3, h 3 4]

theorem tri (x : Fin 5 → ℕ) (a b c : Fin 5) (hab : a.val + 1 = b.val)
    (hbc : b.val + 1 = c.val) (i j k : Fin 5) (hi : i.val = a.val) (hij : i.val + 1 = j.val)
    (hjk : j.val + 1 = k.val) (h : ¬(x a < x b ∧ x b < x c)) : ¬(x i < x j ∧ x j < x k) := by
  have ei : i = a := Fin.ext hi
  have ej : j = b := Fin.ext (by omega)
  have ek : k = c := Fin.ext (by omega)
  rw [ei, ej, ek]; exact h

theorem char (n : ℕ) (x : Fin 5 → Fin (n + 1)) :
    (∀ i j k : Fin 5, i.val + 1 = j.val → j.val + 1 = k.val → ¬(x i < x j ∧ x j < x k)) ↔
      Q5 (fun i => (x i).val) := by
  constructor
  · intro h
    exact ⟨h 0 1 2 rfl rfl, h 1 2 3 rfl rfl, h 2 3 4 rfl rfl⟩
  · rintro ⟨h1, h2, h3⟩ i j k hij hjk
    have hk := k.isLt
    have hi3 : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by omega
    rcases hi3 with h | h | h
    · exact tri (fun i => (x i).val) 0 1 2 rfl rfl i j k h hij hjk h1
    · exact tri (fun i => (x i).val) 1 2 3 rfl rfl i j k h hij hjk h2
    · exact tri (fun i => (x i).val) 2 3 4 rfl rfl i j k h hij hjk h3

theorem c0 : cnt 5 Q5 0 = 0 := by decide +kernel
theorem c1 : cnt 5 Q5 1 = 1 := by decide +kernel
theorem c2 : cnt 5 Q5 2 = 30 := by decide +kernel
theorem c3 : cnt 5 Q5 3 = 123 := by decide +kernel
theorem c4 : cnt 5 Q5 4 = 164 := by decide +kernel
theorem c5 : cnt 5 Q5 5 = 70 := by decide +kernel

theorem a_sum (n : ℕ) : OMA.S_oeis_a200787.a n =
    (n + 1).choose 1 + (n + 1).choose 2 * 30 + (n + 1).choose 3 * 123
      + (n + 1).choose 4 * 164 + (n + 1).choose 5 * 70 := by
  have h : OMA.S_oeis_a200787.a n =
      (univ.filter fun x : Fin 5 → Fin (n + 1) => Q5 (fun i => (x i).val)).card := by
    unfold OMA.S_oeis_a200787.a
    exact congrArg Finset.card (Finset.filter_congr (fun x _ => char n x))
  rw [h, pattern_count 5 (n + 1) Q5 hQ5]
  have e1 : ∑ k ∈ range (n + 1 + 1), (n + 1).choose k * cnt 5 Q5 k =
      ∑ k ∈ range (n + 8), (n + 1).choose k * cnt 5 Q5 k := by
    refine Finset.sum_subset (Finset.range_mono (by omega)) (fun k _ hk => ?_)
    have hk' : n + 1 < k := by
      have := mt Finset.mem_range.2 hk
      omega
    rw [Nat.choose_eq_zero_of_lt hk', Nat.zero_mul]
  have e2 : ∑ k ∈ range 6, (n + 1).choose k * cnt 5 Q5 k =
      ∑ k ∈ range (n + 8), (n + 1).choose k * cnt 5 Q5 k := by
    refine Finset.sum_subset (Finset.range_mono (by omega)) (fun k _ hk => ?_)
    have hk' : 5 < k := by
      have := mt Finset.mem_range.2 hk
      omega
    rw [cnt_zero 5 Q5 k hk', Nat.mul_zero]
  rw [e1, ← e2]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, c0, c1, c2, c3, c4, c5]
  ring

theorem ch1 (N : ℕ) : (N.choose 1 : ℤ) = N := by
  rw [Nat.choose_one_right]

theorem ch2 (N : ℕ) : 2 * (N.choose 2 : ℤ) = (N : ℤ) * (N - 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have e : (N + 1).choose 2 = N.choose 1 + N.choose 2 := Nat.choose_succ_succ' N 1
    have h1 := ch1 N
    rw [e]
    push_cast
    linarith

theorem ch3 (N : ℕ) : 6 * (N.choose 3 : ℤ) = (N : ℤ) * (N - 1) * (N - 2) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have e : (N + 1).choose 3 = N.choose 2 + N.choose 3 := Nat.choose_succ_succ' N 2
    have h1 := ch2 N
    rw [e]
    push_cast
    linarith

theorem ch4 (N : ℕ) : 24 * (N.choose 4 : ℤ) = (N : ℤ) * (N - 1) * (N - 2) * (N - 3) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have e : (N + 1).choose 4 = N.choose 3 + N.choose 4 := Nat.choose_succ_succ' N 3
    have h1 := ch3 N
    rw [e]
    push_cast
    linarith

theorem ch5 (N : ℕ) :
    120 * (N.choose 5 : ℤ) = (N : ℤ) * (N - 1) * (N - 2) * (N - 3) * (N - 4) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have e : (N + 1).choose 5 = N.choose 4 + N.choose 5 := Nat.choose_succ_succ' N 4
    have h1 := ch4 N
    rw [e]
    push_cast
    linarith

theorem h12 (n : ℕ) : 12 * (OMA.S_oeis_a200787.a n : ℤ) =
    (1 + (n : ℤ)) ^ 2 * (12 + 44 * (n : ℤ) + 33 * (n : ℤ) ^ 2 + 7 * (n : ℤ) ^ 3) := by
  have ha : (OMA.S_oeis_a200787.a n : ℤ) =
      ((n + 1).choose 1 : ℤ) + ((n + 1).choose 2 : ℤ) * 30 + ((n + 1).choose 3 : ℤ) * 123
        + ((n + 1).choose 4 : ℤ) * 164 + ((n + 1).choose 5 : ℤ) * 70 := by
    rw [a_sum]
    push_cast
    ring
  have h1 : ((n + 1).choose 1 : ℤ) = (n : ℤ) + 1 := by
    have := ch1 (n + 1)
    push_cast at this
    exact this
  have h2 : 2 * ((n + 1).choose 2 : ℤ) = ((n : ℤ) + 1) * ((n : ℤ) + 1 - 1) := by
    have := ch2 (n + 1)
    push_cast at this
    exact this
  have h3 : 6 * ((n + 1).choose 3 : ℤ) = ((n : ℤ) + 1) * ((n : ℤ) + 1 - 1) * ((n : ℤ) + 1 - 2) := by
    have := ch3 (n + 1)
    push_cast at this
    exact this
  have h4 : 24 * ((n + 1).choose 4 : ℤ) =
      ((n : ℤ) + 1) * ((n : ℤ) + 1 - 1) * ((n : ℤ) + 1 - 2) * ((n : ℤ) + 1 - 3) := by
    have := ch4 (n + 1)
    push_cast at this
    exact this
  have h5 : 120 * ((n + 1).choose 5 : ℤ) =
      ((n : ℤ) + 1) * ((n : ℤ) + 1 - 1) * ((n : ℤ) + 1 - 2) * ((n : ℤ) + 1 - 3)
        * ((n : ℤ) + 1 - 4) := by
    have := ch5 (n + 1)
    push_cast at this
    exact this
  linear_combination 12 * ha + 12 * h1 + 180 * h2 + 246 * h3 + 82 * h4 + 7 * h5

theorem a_val (n : ℕ) (v : ℤ)
    (h : (1 + (n : ℤ)) ^ 2 * (12 + 44 * (n : ℤ) + 33 * (n : ℤ) ^ 2 + 7 * (n : ℤ) ^ 3) = 12 * v) :
    (OMA.S_oeis_a200787.a n : ℤ) = v := by
  have := h12 n
  linarith

/-- the coefficients of the entry's generating function (offset 1) -/
def b (n : ℕ) : ℤ := if n = 0 then (0 : ℤ) else (OMA.S_oeis_a200787.a n : ℤ)

end A200787

theorem OMA.solution : type_of% @OMA.S_oeis_a200787.main := by
  have hrec : ∀ n : ℕ, 6 < n →
      (OMA.S_oeis_a200787.a n : ℤ) = 6 * OMA.S_oeis_a200787.a (n - 1)
        - 15 * OMA.S_oeis_a200787.a (n - 2) + 20 * OMA.S_oeis_a200787.a (n - 3)
        - 15 * OMA.S_oeis_a200787.a (n - 4) + 6 * OMA.S_oeis_a200787.a (n - 5)
        - OMA.S_oeis_a200787.a (n - 6) := by
    intro n hn
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 7 := ⟨n - 7, by omega⟩
    have e1 : j + 7 - 1 = j + 6 := by omega
    have e2 : j + 7 - 2 = j + 5 := by omega
    have e3 : j + 7 - 3 = j + 4 := by omega
    have e4 : j + 7 - 4 = j + 3 := by omega
    have e5 : j + 7 - 5 = j + 2 := by omega
    have e6 : j + 7 - 6 = j + 1 := by omega
    rw [e1, e2, e3, e4, e5, e6]
    have g7 := A200787.h12 (j + 7)
    have g6 := A200787.h12 (j + 6)
    have g5 := A200787.h12 (j + 5)
    have g4 := A200787.h12 (j + 4)
    have g3 := A200787.h12 (j + 3)
    have g2 := A200787.h12 (j + 2)
    have g1 := A200787.h12 (j + 1)
    push_cast at g7 g6 g5 g4 g3 g2 g1
    have key12 : 12 * (OMA.S_oeis_a200787.a (j + 7) : ℤ) =
        12 * (6 * (OMA.S_oeis_a200787.a (j + 6) : ℤ)
        - 15 * OMA.S_oeis_a200787.a (j + 5) + 20 * OMA.S_oeis_a200787.a (j + 4)
        - 15 * OMA.S_oeis_a200787.a (j + 3) + 6 * OMA.S_oeis_a200787.a (j + 2)
        - OMA.S_oeis_a200787.a (j + 1)) := by
      linear_combination g7 - 6 * g6 + 15 * g5 - 20 * g4 + 15 * g3 - 6 * g2 + g1
    linarith
  refine ⟨A200787.h12, hrec, ?_⟩
  have v1 : (OMA.S_oeis_a200787.a 1 : ℤ) = 32 := A200787.a_val 1 32 (by norm_num)
  have v2 : (OMA.S_oeis_a200787.a 2 : ℤ) = 216 := A200787.a_val 2 216 (by norm_num)
  have v3 : (OMA.S_oeis_a200787.a 3 : ℤ) = 840 := A200787.a_val 3 840 (by norm_num)
  have v4 : (OMA.S_oeis_a200787.a 4 : ℤ) = 2425 := A200787.a_val 4 2425 (by norm_num)
  have v5 : (OMA.S_oeis_a200787.a 5 : ℤ) = 5796 := A200787.a_val 5 5796 (by norm_num)
  have v6 : (OMA.S_oeis_a200787.a 6 : ℤ) = 12152 := A200787.a_val 6 12152 (by norm_num)
  have hb : ∀ m : ℕ, 0 < m → A200787.b m = (OMA.S_oeis_a200787.a m : ℤ) :=
    fun m hm => if_neg (by omega)
  have key : ∀ n : ℕ, A200787.b n
      - 6 * (if 1 ≤ n then A200787.b (n - 1) else 0)
      + 15 * (if 2 ≤ n then A200787.b (n - 2) else 0)
      - 20 * (if 3 ≤ n then A200787.b (n - 3) else 0)
      + 15 * (if 4 ≤ n then A200787.b (n - 4) else 0)
      - 6 * (if 5 ≤ n then A200787.b (n - 5) else 0)
      + (if 6 ≤ n then A200787.b (n - 6) else 0)
      = 32 * (if n = 1 then 1 else 0) + 24 * (if n = 2 then 1 else 0)
        + 24 * (if n = 3 then 1 else 0) - 15 * (if n = 4 then 1 else 0)
        + 6 * (if n = 5 then 1 else 0) - (if n = 6 then 1 else 0) := by
    intro n
    by_cases hn : n < 7
    · interval_cases n <;> simp [A200787.b, v1, v2, v3, v4, v5, v6]
    · have h := hrec n (by omega)
      rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega),
        if_pos (by omega), if_pos (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        hb n (by omega), hb (n - 1) (by omega), hb (n - 2) (by omega), hb (n - 3) (by omega),
        hb (n - 4) (by omega), hb (n - 5) (by omega), hb (n - 6) (by omega), h]
      ring
  have h6 : (PowerSeries.C (6 : ℤ)) = 6 := map_ofNat _ 6
  have h15 : (PowerSeries.C (15 : ℤ)) = 15 := map_ofNat _ 15
  have h20 : (PowerSeries.C (20 : ℤ)) = 20 := map_ofNat _ 20
  have h32 : (PowerSeries.C (32 : ℤ)) = 32 := map_ofNat _ 32
  have h24 : (PowerSeries.C (24 : ℤ)) = 24 := map_ofNat _ 24
  show (1 - PowerSeries.X) ^ 6 * PowerSeries.mk A200787.b =
      PowerSeries.X * (32 + 24 * PowerSeries.X + 24 * PowerSeries.X ^ 2 - 15 * PowerSeries.X ^ 3
        + 6 * PowerSeries.X ^ 4 - PowerSeries.X ^ 5)
  have el : (1 - PowerSeries.X) ^ 6 * PowerSeries.mk A200787.b
      = PowerSeries.mk A200787.b
        - PowerSeries.C (6 : ℤ) * (PowerSeries.mk A200787.b * PowerSeries.X ^ 1)
        + PowerSeries.C (15 : ℤ) * (PowerSeries.mk A200787.b * PowerSeries.X ^ 2)
        - PowerSeries.C (20 : ℤ) * (PowerSeries.mk A200787.b * PowerSeries.X ^ 3)
        + PowerSeries.C (15 : ℤ) * (PowerSeries.mk A200787.b * PowerSeries.X ^ 4)
        - PowerSeries.C (6 : ℤ) * (PowerSeries.mk A200787.b * PowerSeries.X ^ 5)
        + PowerSeries.mk A200787.b * PowerSeries.X ^ 6 := by
    rw [h6, h15, h20]
    ring
  have er : (PowerSeries.X : PowerSeries ℤ) * (32 + 24 * PowerSeries.X + 24 * PowerSeries.X ^ 2
        - 15 * PowerSeries.X ^ 3 + 6 * PowerSeries.X ^ 4 - PowerSeries.X ^ 5)
      = PowerSeries.C (32 : ℤ) * PowerSeries.X ^ 1 + PowerSeries.C (24 : ℤ) * PowerSeries.X ^ 2
        + PowerSeries.C (24 : ℤ) * PowerSeries.X ^ 3 - PowerSeries.C (15 : ℤ) * PowerSeries.X ^ 4
        + PowerSeries.C (6 : ℤ) * PowerSeries.X ^ 5 - PowerSeries.X ^ 6 := by
    rw [h6, h15, h32, h24]
    ring
  rw [el, er]
  ext n
  have hC : ∀ (k : ℕ) (c : ℤ) (m : ℕ),
      (if k ≤ m then (if m - k = 0 then c else 0) else 0) = c * (if m = k then 1 else 0) := by
    intro k c m
    split_ifs <;> omega
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
    PowerSeries.coeff_mk, PowerSeries.coeff_X_pow, PowerSeries.coeff_C, hC]
  exact key n
