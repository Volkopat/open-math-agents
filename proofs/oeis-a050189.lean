import OMAStatements.S_oeis_a050189

namespace OMA.P_oeis_a050189
open OMA.S_oeis_a050189

lemma count_ofFn {n : ℕ} (f : Fin n → Bool) :
    (List.ofFn f).count true = (Finset.univ.filter (fun i => f i = true)).card := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.count_cons, ih (fun i => f i.succ)]
    rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ]
    cases f 0 <;> simp [add_comm]

lemma card_weight (n k : ℕ) :
    Nat.card {w : List.Vector Bool n // w.toList.count true = k} = n.choose k := by
  classical
  have hc : ∀ w : List.Vector Bool n,
      w.toList.count true = (Finset.univ.filter (fun i => w.get i = true)).card := by
    intro w
    rw [← count_ofFn, ← List.Vector.toList_ofFn, List.Vector.ofFn_get]
  let e : {w : List.Vector Bool n // w.toList.count true = k} ≃
      {s : Finset (Fin n) // s.card = k} :=
    { toFun := fun w => ⟨Finset.univ.filter (fun i => w.1.get i = true), by rw [← hc]; exact w.2⟩
      invFun := fun s => ⟨List.Vector.ofFn (fun i => decide (i ∈ s.1)), by
        rw [hc]; simpa using s.2⟩
      left_inv := fun w => by
        apply Subtype.ext
        apply List.Vector.ext
        intro i
        simp
      right_inv := fun s => by
        apply Subtype.ext
        ext i
        simp }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_finset_len, Fintype.card_fin]

lemma periodic_iff {l : List Bool} (h : l.count true = 4) :
    (∃ (u : List Bool) (j : ℕ), 2 ≤ j ∧ l = (List.replicate j u).flatten) ↔ ∃ v, l = v ++ v := by
  constructor
  · rintro ⟨u, j, hj, rfl⟩
    have hc : (List.replicate j u).flatten.count true = j * u.count true := by
      simp [List.count_flatten, List.sum_replicate]
    rw [hc] at h
    have hj4 : j ∣ 4 := ⟨_, h.symm⟩
    have hle := Nat.le_of_dvd (by norm_num) hj4
    interval_cases j
    · exact ⟨u, by simp [List.replicate_succ]⟩
    · norm_num at hj4
    · exact ⟨u ++ u, by simp [List.replicate_succ, List.append_assoc]⟩
  · rintro ⟨v, rfl⟩
    exact ⟨v, 2, le_rfl, by simp [List.replicate_succ]⟩

lemma card_split {α : Type} [Fintype α] (c P : α → Prop) :
    Nat.card {x // c x ∧ ¬ P x} + Nat.card {x // c x ∧ P x} = Nat.card {x // c x} := by
  classical
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hc : c x <;> by_cases hp : P x <;> simp [hc, hp]

lemma card_periodic (n : ℕ) :
    Nat.card {w : List.Vector Bool n // w.toList.count true = 4 ∧ ∃ v, w.toList = v ++ v} =
      if 2 ∣ n then (n / 2).choose 2 else 0 := by
  split_ifs with h2
  · obtain ⟨m, rfl⟩ := h2
    rw [show 2 * m / 2 = m by omega, ← card_weight m 2]
    symm
    apply Nat.card_congr
    exact
      { toFun := fun v => ⟨⟨v.1.1 ++ v.1.1, by rw [List.length_append, v.1.2]; omega⟩, by
          refine ⟨?_, v.1.1, rfl⟩
          show (v.1.1 ++ v.1.1).count true = 4
          rw [List.count_append]
          have := v.2
          simp only [List.Vector.toList] at this
          omega⟩
        invFun := fun w => ⟨⟨w.1.1.take m, by rw [List.length_take, w.1.2]; omega⟩, by
          obtain ⟨hw, v, hv⟩ := w.2
          have hl : v.length = m := by
            have := congrArg List.length hv
            simp only [List.Vector.toList_length, List.length_append] at this
            omega
          show (w.1.1.take m).count true = 2
          have hv' : w.1.1 = v ++ v := hv
          rw [hv', List.take_left' hl]
          have hw' : (w.1.1).count true = 4 := hw
          rw [hv', List.count_append] at hw'
          omega⟩
        left_inv := fun v => by
          apply Subtype.ext; apply Subtype.ext
          exact List.take_left' v.1.2
        right_inv := fun w => by
          apply Subtype.ext; apply Subtype.ext
          obtain ⟨hw, v, hv⟩ := w.2
          have hl : v.length = m := by
            have := congrArg List.length hv
            simp only [List.Vector.toList_length, List.length_append] at this
            omega
          have hv' : w.1.1 = v ++ v := hv
          show w.1.1.take m ++ w.1.1.take m = w.1.1
          rw [hv', List.take_left' hl] }
  · rw [Nat.card_eq_zero]
    left
    constructor
    rintro ⟨w, _, v, hv⟩
    have := congrArg List.length hv
    simp only [List.Vector.toList_length, List.length_append] at this
    omega

lemma main_count (n : ℕ) : a n + (if 2 ∣ n then (n / 2).choose 2 else 0) = n.choose 4 := by
  have h1 : a n = Nat.card {w : List.Vector Bool n //
      w.toList.count true = 4 ∧ ¬ ∃ v, w.toList = v ++ v} :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun w =>
      and_congr_right (fun h => not_congr (periodic_iff h))))
  rw [h1, ← card_periodic, card_split, card_weight]

lemma choose_poly (m : ℕ) : (m.choose 2 : ℚ) = m * (m - 1) / 2 ∧
    (m.choose 3 : ℚ) = m * (m - 1) * (m - 2) / 6 ∧
    (m.choose 4 : ℚ) = m * (m - 1) * (m - 2) * (m - 3) / 24 := by
  induction m with
  | zero => simp
  | succ m ih =>
    obtain ⟨h2, h3, h4⟩ := ih
    have e2 : (m + 1).choose 2 = m.choose 1 + m.choose 2 := Nat.choose_succ_succ' m 1
    have e3 : (m + 1).choose 3 = m.choose 2 + m.choose 3 := Nat.choose_succ_succ' m 2
    have e4 : (m + 1).choose 4 = m.choose 3 + m.choose 4 := Nat.choose_succ_succ' m 3
    refine ⟨?_, ?_, ?_⟩
    · rw [e2]; push_cast [h2, Nat.choose_one_right]; ring
    · rw [e3]; push_cast [h2, h3]; ring
    · rw [e4]; push_cast [h3, h4]; ring

lemma haE (k : ℕ) : (a (2 * k) : ℚ) =
    (2 * k : ℚ) * (2 * k - 1) * (2 * k - 2) * (2 * k - 3) / 24 - k * (k - 1) / 2 := by
  have h := main_count (2 * k)
  rw [if_pos (dvd_mul_right 2 k), show 2 * k / 2 = k by omega] at h
  have h' : (a (2 * k) : ℚ) + (k.choose 2 : ℚ) = ((2 * k).choose 4 : ℚ) := by exact_mod_cast h
  rw [(choose_poly k).1, (choose_poly (2 * k)).2.2] at h'
  push_cast at h'
  linarith

lemma haO (k : ℕ) : (a (2 * k + 1) : ℚ) =
    (2 * k + 1 : ℚ) * (2 * k) * (2 * k - 1) * (2 * k - 2) / 24 := by
  have h := main_count (2 * k + 1)
  rw [if_neg (by omega)] at h
  have h' : (a (2 * k + 1) : ℚ) = ((2 * k + 1).choose 4 : ℚ) := by exact_mod_cast h
  rw [(choose_poly (2 * k + 1)).2.2] at h'
  push_cast at h'
  linarith

lemma recQ (m : ℕ) : (a (m + 12) : ℚ) = 2 * a (m + 11) + 2 * a (m + 10) - 6 * a (m + 9) +
    6 * a (m + 7) - 2 * a (m + 6) - 2 * a (m + 5) + a (m + 4) := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' m
  · rw [show 2 * k + 12 = 2 * (k + 6) by ring, show 2 * k + 11 = 2 * (k + 5) + 1 by ring,
      show 2 * k + 10 = 2 * (k + 5) by ring, show 2 * k + 9 = 2 * (k + 4) + 1 by ring,
      show 2 * k + 7 = 2 * (k + 3) + 1 by ring, show 2 * k + 6 = 2 * (k + 3) by ring,
      show 2 * k + 5 = 2 * (k + 2) + 1 by ring, show 2 * k + 4 = 2 * (k + 2) by ring,
      haE, haE, haE, haE, haO, haO, haO, haO]
    push_cast; ring
  · rw [show 2 * k + 1 + 12 = 2 * (k + 6) + 1 by ring, show 2 * k + 1 + 11 = 2 * (k + 6) by ring,
      show 2 * k + 1 + 10 = 2 * (k + 5) + 1 by ring, show 2 * k + 1 + 9 = 2 * (k + 5) by ring,
      show 2 * k + 1 + 7 = 2 * (k + 4) by ring, show 2 * k + 1 + 6 = 2 * (k + 3) + 1 by ring,
      show 2 * k + 1 + 5 = 2 * (k + 3) by ring, show 2 * k + 1 + 4 = 2 * (k + 2) + 1 by ring,
      haE, haE, haE, haE, haO, haO, haO, haO]
    push_cast; ring

lemma a_eq (n : ℕ) : a n = n.choose 4 - if 2 ∣ n then (n / 2).choose 2 else 0 := by
  have := main_count n; omega

lemma a_small : a 0 = 0 ∧ a 1 = 0 ∧ a 2 = 0 ∧ a 3 = 0 ∧ a 4 = 0 ∧ a 5 = 5 ∧ a 6 = 12 ∧
    a 7 = 35 ∧ a 8 = 64 ∧ a 9 = 126 ∧ a 10 = 200 ∧ a 11 = 330 := by
  simp only [a_eq]; decide

theorem prove_main : (∀ n : ℕ, 12 ≤ n → (a n : ℤ) = 2 * a (n - 1) + 2 * a (n - 2) - 6 * a (n - 3) +
      6 * a (n - 5) - 2 * a (n - 6) - 2 * a (n - 7) + a (n - 8)) ∧
    PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - PowerSeries.X) ^ 5 * (1 + PowerSeries.X) ^ 3) =
      PowerSeries.X ^ 5 * (5 + 2 * PowerSeries.X + PowerSeries.X ^ 2) := by
  refine ⟨fun n hn => ?_, ?_⟩
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
    rw [show m + 12 - 1 = m + 11 by omega, show m + 12 - 2 = m + 10 by omega,
      show m + 12 - 3 = m + 9 by omega, show m + 12 - 5 = m + 7 by omega,
      show m + 12 - 6 = m + 6 by omega, show m + 12 - 7 = m + 5 by omega,
      show m + 12 - 8 = m + 4 by omega]
    have := recQ m
    exact_mod_cast this
  · set s := PowerSeries.mk (fun n => (a n : ℚ)) with hs
    have hL : s * ((1 - PowerSeries.X) ^ 5 * (1 + PowerSeries.X) ^ 3) =
        s - 2 • (s * PowerSeries.X ^ 1) - 2 • (s * PowerSeries.X ^ 2) +
          6 • (s * PowerSeries.X ^ 3) - 6 • (s * PowerSeries.X ^ 5) +
          2 • (s * PowerSeries.X ^ 6) + 2 • (s * PowerSeries.X ^ 7) - s * PowerSeries.X ^ 8 := by
      ring
    have hR : (PowerSeries.X : PowerSeries ℚ) ^ 5 * (5 + 2 * PowerSeries.X + PowerSeries.X ^ 2) =
        5 • PowerSeries.X ^ 5 + 2 • PowerSeries.X ^ 6 + PowerSeries.X ^ 7 := by
      ring
    rw [hL, hR]
    ext n
    simp only [map_sub, map_add, map_nsmul, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow,
      hs, PowerSeries.coeff_mk]
    simp only [nsmul_eq_mul]
    rcases lt_or_ge n 12 with h | h
    · obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := a_small
      interval_cases n <;> simp [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11] <;> norm_num
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' h
      have := recQ m
      have e : ∀ d, d ≤ 8 → d ≤ m + 12 := fun d hd => by omega
      simp only [e 1 (by norm_num), e 2 (by norm_num), e 3 (by norm_num), e 5 (by norm_num),
        e 6 (by norm_num), e 7 (by norm_num), e 8 (by norm_num), ↓reduceIte,
        show m + 12 ≠ 5 by omega, show m + 12 ≠ 6 by omega, show m + 12 ≠ 7 by omega,
        show m + 12 - 1 = m + 11 by omega, show m + 12 - 2 = m + 10 by omega,
        show m + 12 - 3 = m + 9 by omega, show m + 12 - 5 = m + 7 by omega,
        show m + 12 - 6 = m + 6 by omega, show m + 12 - 7 = m + 5 by omega,
        show m + 12 - 8 = m + 4 by omega]
      push_cast
      linarith

end OMA.P_oeis_a050189

theorem OMA.solution : type_of% @OMA.S_oeis_a050189.main :=
  OMA.P_oeis_a050189.prove_main
