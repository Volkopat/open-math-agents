import OMAStatements.S_oeis_a028884
import Mathlib

open OMA.S_oeis_a028884

private def live (t : ℕ) (i : ℤ) : Prop :=
  (t = 0 ∧ i = 0) ∨ (1 ≤ t ∧ -(t : ℤ) ≤ i ∧ i ≤ t ∧ ((t : ℤ) - 1 ≤ i ∨ i ≤ 1 - (t : ℤ) ∨ i % 2 = 1))

private instance liveDec (t : ℕ) (i : ℤ) : Decidable (live t i) := by
  unfold live; infer_instance

private instance discDec : DecidablePred IsDisc := fun k => by
  unfold IsDisc; infer_instance

private lemma table (l c r : Bool) :
    rule94 l c r = true ↔ ((l = true ∧ r = false) ∨ (l = false ∧ r = true) ∨
      (l = false ∧ c = true ∧ r = false)) := by
  cases l <;> cases c <;> cases r <;> decide

set_option maxHeartbeats 4000000 in
private lemma state_iff (t : ℕ) (i : ℤ) : state t i = true ↔ live t i := by
  induction t generalizing i with
  | zero => simp [state, live]
  | succ t ih =>
    rw [state, table]
    simp only [Bool.eq_false_iff, ne_eq, ih, live]
    push_cast
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · simp; omega
    · have h1 : t ≠ 0 := by omega
      simp only [h1, false_and, false_or]
      have e1 : (i - 1) % 2 = 1 - i % 2 := by omega
      have e2 : (i + 1) % 2 = 1 - i % 2 := by omega
      rw [e1, e2]
      rcases Int.emod_two_eq_zero_or_one i with hi | hi <;> rw [hi] <;> norm_num <;> omega

private lemma alt (m s c : ℕ) (f : ℕ → ℕ)
    (h : ∀ j < 2 * m, f (s + j) = if (j + c) % 2 = 1 then 1 else 0) :
    ∑ j ∈ Finset.range (2 * m), f (s + j) = m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      ih (fun j hj => h j (by omega)), h (2 * m) (by omega), h (2 * m + 1) (by omega)]
    split_ifs <;> omega

private lemma st (t j : ℕ) : state t ((j : ℤ) - t) = decide (live t ((j : ℤ) - t)) := by
  rw [Bool.eq_iff_iff, state_iff, decide_eq_true_iff]

private lemma on_eq (t : ℕ) (ht : 2 ≤ t) : onCells t = t + 2 + (if t % 2 = 1 then 1 else 0) := by
  unfold onCells
  rw [Finset.card_filter]
  have v1 : ∀ j : ℕ, live t ((j : ℤ) - t) →
      (if state t ((j : ℤ) - (t : ℤ)) = true then 1 else 0) = 1 := by
    intro j hj; simp only [st, decide_eq_true_eq]; exact if_pos hj
  have v0 : ∀ j : ℕ, ¬ live t ((j : ℤ) - t) →
      (if state t ((j : ℤ) - (t : ℤ)) = true then 1 else 0) = 0 := by
    intro j hj; simp only [st, decide_eq_true_eq]; exact if_neg hj
  rw [show 2 * t + 1 = 2 + (2 * (t - 2) + 3) by omega, Finset.sum_range_add,
    Finset.sum_range_add]
  have hmid := alt (t - 2) 2 t (fun j => if state t ((j : ℤ) - (t : ℤ)) = true then 1 else 0) (fun j hj => by
    beta_reduce
    by_cases hj2 : (j + t) % 2 = 1
    · rw [if_pos hj2, v1]; unfold live; right; push_cast; omega
    · rw [if_neg hj2, v0]; unfold live; push_cast; omega)
  beta_reduce at hmid
  rw [hmid]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [v1 0 (by unfold live; right; push_cast; omega), v1 1 (by unfold live; right; push_cast; omega),
    v1 (2 + (2 * (t - 2) + 1)) (by unfold live; right; push_cast; omega),
    v1 (2 + (2 * (t - 2) + 2)) (by unfold live; right; push_cast; omega)]
  by_cases hp : t % 2 = 1
  · rw [v1 (2 + (2 * (t - 2) + 0)) (by unfold live; right; push_cast; omega), if_pos hp]; omega
  · rw [v0 (2 + (2 * (t - 2) + 0)) (by unfold live; push_cast; omega), if_neg hp]; omega

private lemma on0 : onCells 0 = 1 := by decide
private lemma on1 : onCells 1 = 3 := by decide

private lemma A_even (k : ℕ) (hk : 1 ≤ k) : A265284 (2 * k) = 2 * k ^ 2 + 6 * k := by
  induction k, hk using Nat.le_induction with
  | base =>
    simp [A265284, Finset.sum_range_succ, on0, on1, on_eq]
  | succ k hk ih =>
    unfold A265284 at *
    rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, on_eq _ (by omega), on_eq _ (by omega)]
    rw [if_pos (by omega), if_neg (by omega)]
    ring

private lemma A_odd (k : ℕ) : A265284 (2 * k + 1) = 2 * k ^ 2 + 8 * k + 4 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [A265284, Finset.sum_range_succ, on0, on1]
  · have h := A_even k hk
    unfold A265284 at *
    rw [Finset.sum_range_succ, h, on_eq _ (by omega), if_pos (by omega)]
    ring

private lemma c4 (M : ℕ) : ((Finset.range M).filter fun k => k % 4 = 0 ∨ k % 4 = 1).card =
    (M + 3) / 4 + (M + 2) / 4 := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.range_add_one, Finset.filter_insert]
    split_ifs with h
    · rw [Finset.card_insert_of_notMem (by simp), ih]; omega
    · rw [ih]; omega

private lemma sq_mod (r : ℕ) : (r * r) % 4 = 0 ∨ (r * r) % 4 = 1 := by
  rw [Nat.mul_mod]
  have : r % 4 < 4 := Nat.mod_lt _ (by norm_num)
  interval_cases (r % 4) <;> simp

private lemma cnt (M R : ℕ) (h1 : (R - 1) * (R - 1) < M) (h2 : M ≤ R * R) (hR : 1 ≤ R) :
    Nat.count IsDisc M = (M + 3) / 4 + (M + 2) / 4 - R := by
  classical
  rw [Nat.count_eq_card_filter_range]
  have hsq : (Finset.range M).filter (fun k => IsSquare k) = (Finset.range R).image (fun j => j * j) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hk, r, rfl⟩
      refine ⟨r, ?_, rfl⟩
      by_contra hc
      push Not at hc
      have : R * R ≤ r * r := Nat.mul_le_mul hc hc
      omega
    · rintro ⟨j, hj, rfl⟩
      refine ⟨?_, j, rfl⟩
      have : j ≤ R - 1 := by omega
      have := Nat.mul_le_mul this this
      omega
  have hcard : ((Finset.range R).image (fun j => j * j)).card = R := by
    rw [Finset.card_image_of_injective _ (fun x y hxy => Nat.mul_self_inj.mp hxy), Finset.card_range]
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.range M).filter fun k => k % 4 = 0 ∨ k % 4 = 1) (fun k => IsSquare k)
  rw [Finset.filter_filter, Finset.filter_filter] at hsplit
  have e1 : (Finset.range M).filter (fun k => (k % 4 = 0 ∨ k % 4 = 1) ∧ IsSquare k) =
      (Finset.range M).filter (fun k => IsSquare k) := by
    apply Finset.filter_congr
    intro k _
    constructor
    · exact fun h => h.2
    · rintro ⟨r, rfl⟩; exact ⟨sq_mod r, r, rfl⟩
  rw [e1, hsq, hcard, c4] at hsplit
  have e2 : (Finset.range M).filter IsDisc =
      (Finset.range M).filter (fun k => (k % 4 = 0 ∨ k % 4 = 1) ∧ ¬ IsSquare k) :=
    Finset.filter_congr (fun _ _ => Iff.rfl)
  rw [e2]
  omega

private lemma nsq (M R : ℕ) (h1 : R * R < M) (h2 : M < (R + 1) * (R + 1)) : ¬ IsSquare M := by
  rintro ⟨r, rfl⟩
  rcases Nat.lt_or_ge r (R + 1) with h | h
  · have : r ≤ R := by omega
    have := Nat.mul_le_mul this this; omega
  · have := Nat.mul_le_mul h h; omega

theorem OMA.solution : type_of% @OMA.S_oeis_a028884.main := by
  intro n hn
  unfold a A079896
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · -- n = 2k, k ≥ 1; M = 4k^2 + 12k + 1, R = 2k + 3
    have hk : 1 ≤ k := by omega
    have hM : (2 * k + 3) ^ 2 - 8 = 4 * k ^ 2 + 12 * k + 1 := by
      have : (2 * k + 3) ^ 2 = 4 * k ^ 2 + 12 * k + 9 := by ring
      omega
    rw [hM]
    have hA : A265284 (2 * k - 1) = 2 * k ^ 2 + 4 * k - 2 := by
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      rw [show 2 * (j + 1) - 1 = 2 * j + 1 by omega, A_odd]
      have : (j + 1) ^ 2 = j ^ 2 + 2 * j + 1 := by ring
      omega
    rw [hA]
    have hc := cnt (4 * k ^ 2 + 12 * k + 1) (2 * k + 3) (by
        rw [show 2 * k + 3 - 1 = 2 * k + 2 by omega]; nlinarith) (by nlinarith) (by omega)
    have hd : IsDisc (4 * k ^ 2 + 12 * k + 1) := by
      refine ⟨Or.inr (by omega), nsq _ (2 * k + 2) (by nlinarith) (by nlinarith)⟩
    have e : (4 * k ^ 2 + 12 * k + 1 + 3) / 4 + (4 * k ^ 2 + 12 * k + 1 + 2) / 4 - (2 * k + 3) =
        2 * k ^ 2 + 4 * k - 2 := by omega
    rw [← e, ← hc, Nat.nth_count hd]
  · -- n = 2k+1; M = 4k^2 + 16k + 8
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · -- n = 1: M = 8
      have hc := cnt 8 3 (by norm_num) (by norm_num) (by norm_num)
      have hd : IsDisc 8 := ⟨Or.inl (by norm_num), nsq 8 2 (by norm_num) (by norm_num)⟩
      have hA : A265284 0 = 1 := by simp [A265284, on0]
      norm_num at hc
      rw [show 2 * 0 + 1 - 1 = 0 by rfl, hA, show (2 * 0 + 1 + 3) ^ 2 - 8 = 8 by rfl, ← hc,
        Nat.nth_count hd]
    · have hM : (2 * k + 1 + 3) ^ 2 - 8 = 4 * k ^ 2 + 16 * k + 8 := by
        have : (2 * k + 1 + 3) ^ 2 = 4 * k ^ 2 + 16 * k + 16 := by ring
        omega
      rw [hM, show 2 * k + 1 - 1 = 2 * k by omega, A_even k hk]
      have hc := cnt (4 * k ^ 2 + 16 * k + 8) (2 * k + 4) (by
          rw [show 2 * k + 4 - 1 = 2 * k + 3 by omega]; nlinarith) (by nlinarith) (by omega)
      have hd : IsDisc (4 * k ^ 2 + 16 * k + 8) := by
        refine ⟨Or.inl (by omega), nsq _ (2 * k + 3) (by nlinarith) (by nlinarith)⟩
      have e : (4 * k ^ 2 + 16 * k + 8 + 3) / 4 + (4 * k ^ 2 + 16 * k + 8 + 2) / 4 - (2 * k + 4) =
          2 * k ^ 2 + 6 * k := by omega
      rw [← e, ← hc, Nat.nth_count hd]
