import OMAStatements.S_oeis_a004484

section
open OMA.S_oeis_a004484

private def wyTable : List (List ℕ) := [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13], [1, 2, 0, 4, 5, 3, 7, 8, 6, 10, 11, 9, 13, 14], [2, 0, 1, 5, 3, 4, 8, 6, 7, 11, 9, 10, 14, 12], [3, 4, 5, 6, 2, 0, 1, 9, 10, 12, 8, 7, 15, 11]]
private def wy (a n : ℕ) : ℕ :=
  let row := wyTable.getD a []
  if n < 8 then row.getD n 0 else row.getD (8 + (n-8)%6) 0 + 6*((n-8)/6)

private def wyMex (a n : ℕ) : Prop :=
  (∀ c d : ℕ, Move a n c d → wy c d ≠ wy a n) ∧
    (∀ m : ℕ, m < wy a n → ∃ c d : ℕ, Move a n c d ∧ wy c d = m)

private theorem wy_shift (a n : ℕ) (hn : 8 ≤ n) : wy a (n+6) = wy a n + 6 := by
  have h : n+6-8 = (n-8)+6 := by omega
  simp only [wy, if_neg (show ¬ n+6 < 8 by omega), if_neg (show ¬ n < 8 by omega), h,
    Nat.add_mod_right, Nat.add_div_right _ (by decide : 0 < 6)]
  omega

private theorem wy_upper (a n : ℕ) (ha : a ≤ 3) : wy a n ≤ n+6 := by
  by_cases hn : n < 8
  · interval_cases a <;> interval_cases n <;> decide
  · have splitn : n = 8 + (n-8)%6 + 6*((n-8)/6) := by omega
    have hm := Nat.mod_lt (n-8) (by decide : 0 < 6)
    simp only [wy, if_neg hn]
    generalize heq : (n-8)%6 = r at *
    interval_cases a <;> interval_cases r <;> norm_num [wyTable, List.getD] <;> omega

private theorem wy_lower (a n : ℕ) (ha : a ≤ 3) : n ≤ wy a n + 6 := by
  by_cases hn : n < 8
  · interval_cases a <;> interval_cases n <;> decide
  · have splitn : n = 8 + (n-8)%6 + 6*((n-8)/6) := by omega
    have hm := Nat.mod_lt (n-8) (by decide : 0 < 6)
    simp only [wy, if_neg hn]
    generalize heq : (n-8)%6 = r at *
    interval_cases a <;> interval_cases r <;> norm_num [wyTable, List.getD] <;> omega
end

section
open OMA.S_oeis_a004484

private def wyOptions (a n : ℕ) : List (ℕ × ℕ) :=
  (List.range a).map (fun c => (c, n)) ++
    (List.range n).map (fun d => (a, d)) ++
    (List.range (min a n)).map (fun t => (a - (t+1), n - (t+1)))

private lemma wy_mem_options (a n c d : ℕ) :
    (c, d) ∈ wyOptions a n ↔ Move a n c d := by
  simp only [wyOptions, List.mem_append, List.mem_map, List.mem_range, Prod.mk.injEq, Move]
  constructor
  · rintro ((⟨i, hi, rfl, rfl⟩ | ⟨i, hi, rfl, rfl⟩) | ⟨t, ht, rfl, rfl⟩)
    · exact Or.inl ⟨hi, rfl⟩
    · exact Or.inr (Or.inl ⟨rfl, hi⟩)
    · exact Or.inr (Or.inr ⟨t+1, by omega, by omega, by omega⟩)
  · rintro (⟨hc, rfl⟩ | ⟨rfl, hd⟩ | ⟨t, ht, ha, hn⟩)
    · exact Or.inl (Or.inl ⟨c, hc, rfl, rfl⟩)
    · exact Or.inl (Or.inr ⟨d, hd, rfl, rfl⟩)
    · exact Or.inr ⟨t-1, by omega, by omega, by omega⟩

private def wyCheck (a n : ℕ) : Bool :=
  let vals := (wyOptions a n).map (fun p => wy p.1 p.2)
  decide (wy a n ∉ vals) && (List.range (wy a n)).all vals.contains

private lemma wyCheck_sound (a n : ℕ) (h : wyCheck a n = true) : wyMex a n := by
  simp only [wyCheck, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, List.mem_range, List.contains_iff_mem] at h
  constructor
  · intro c d hmove heq
    apply h.1
    exact List.mem_map.mpr ⟨(c,d), (wy_mem_options a n c d).mpr hmove, heq⟩
  · intro m hm
    obtain ⟨⟨c,d⟩, hcd, heq⟩ := List.mem_map.mp (h.2 m hm)
    exact ⟨c, d, (wy_mem_options a n c d).mp hcd, heq⟩

private theorem wy_base (a n : ℕ) (ha : a ≤ 3) (hn : n < 40) : wyMex a n := by
  have cert : ∀ r : Fin 4, ∀ i : Fin 40, wyCheck r i = true := by decide +kernel
  exact wyCheck_sound a n (cert ⟨a, by omega⟩ ⟨n, hn⟩)

private theorem wy_small_witness (a m : ℕ) (ha : a ≤ 3) (hm : m < 20) :
    ∃ d < 32, wy a d = m := by
  have cert : ∀ r : Fin 4, ∀ v : Fin 20, ∃ d : Fin 32, wy r d = v := by decide +kernel
  obtain ⟨d, hd⟩ := cert ⟨a, by omega⟩ ⟨m, hm⟩
  exact ⟨d, d.isLt, hd⟩
end

section
open OMA.S_oeis_a004484

private lemma wy_move_row {a n c d : ℕ} (h : Move a n c d) : c ≤ a := by
  rcases h with ⟨_,_⟩ | ⟨_,_⟩ | ⟨t,_,_,_⟩ <;> omega

private lemma wy_move_translate {a n c d : ℕ} (h : Move a n c d) :
    Move a (n+6) c (d+6) := by
  rcases h with ⟨hc,hd⟩ | ⟨hc,hd⟩ | ⟨t,ht,hc,hd⟩
  · exact Or.inl ⟨hc, by omega⟩
  · exact Or.inr (Or.inl ⟨hc, by omega⟩)
  · exact Or.inr (Or.inr ⟨t, ht, hc, by omega⟩)

private lemma wy_move_retreat {a n c d : ℕ} (h : Move a n c d) (hd' : 6 ≤ d) :
    Move a (n-6) c (d-6) := by
  rcases h with ⟨hc,hd⟩ | ⟨hc,hd⟩ | ⟨t,ht,hc,hd⟩
  · exact Or.inl ⟨hc, by omega⟩
  · exact Or.inr (Or.inl ⟨hc, by omega⟩)
  · exact Or.inr (Or.inr ⟨t, ht, hc, by omega⟩)

private theorem wy_lift (small : ∀ a m : ℕ, a ≤ 3 → m < 20 → ∃ d < 32, wy a d = m)
    (a n : ℕ) (ha : a ≤ 3) (hn : 40 ≤ n) (ih : wyMex a (n-6)) : wyMex a n := by
  have step_n : wy a n = wy a (n-6) + 6 := by
    simpa [Nat.sub_add_cancel (show 6 ≤ n by omega)] using wy_shift a (n-6) (by omega)
  constructor
  · intro c d move equal
    have hc := (wy_move_row move).trans ha
    have hlow := wy_lower a n ha
    have hhigh := wy_upper c d hc
    have hd : 8 ≤ d-6 := by omega
    have step_d := wy_shift c (d-6) hd
    rw [Nat.sub_add_cancel (by omega : 6 ≤ d)] at step_d
    exact ih.1 c (d-6) (wy_move_retreat move (by omega)) (by omega)
  · intro m hm
    by_cases low : m < 20
    · obtain ⟨d, hd, hv⟩ := small a m ha low
      exact ⟨a, d, Or.inr (Or.inl ⟨rfl, by omega⟩), hv⟩
    · obtain ⟨c, d, move, hv⟩ := ih.2 (m-6) (by omega)
      have hc := (wy_move_row move).trans ha
      have bound := wy_upper c d hc
      have shift_d := wy_shift c d (by omega)
      have trans := wy_move_translate move
      rw [Nat.sub_add_cancel (by omega : 6 ≤ n)] at trans
      exact ⟨c, d+6, trans, by omega⟩
end

section
open OMA.S_oeis_a004484

private theorem wy_unique (mex : ∀ a n : ℕ, a ≤ 3 → wyMex a n)
    (g : ℕ → ℕ → ℕ) (hg : IsGrundy g) (a n : ℕ) (ha : a ≤ 3) :
    g a n = wy a n := by
  suffices H : ∀ k a n : ℕ, a+n = k → a ≤ 3 → g a n = wy a n from H _ a n rfl ha
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro a n hsum ha
    have prev (c d : ℕ) (hm : Move a n c d) : g c d = wy c d := by
      apply ih (c+d) _ c d rfl
      all_goals rcases hm with ⟨_,rfl⟩ | ⟨rfl,_⟩ | ⟨t,ht,_,_⟩ <;> omega
    obtain ⟨skipG, hitG⟩ := hg a n
    obtain ⟨skipW, hitW⟩ := mex a n ha
    rcases lt_trichotomy (g a n) (wy a n) with lt|eq|gt
    · obtain ⟨c,d,move,value⟩ := hitW _ lt
      exact False.elim (skipG c d move ((prev c d move).trans value))
    · exact eq
    · obtain ⟨c,d,move,value⟩ := hitG _ gt
      exact False.elim (skipW c d move ((prev c d move).symm.trans value))
end

section
open OMA.S_oeis_a004484 PowerSeries

private lemma wy_conclusion (g : ℕ → ℕ → ℕ) (hrow : ∀ n, g 3 n = wy 3 n) :
    (∀ n : ℕ, 14 < n →
      (g 3 n : ℤ) = (g 3 (n - 1) : ℤ) + (g 3 (n - 6) : ℤ) - (g 3 (n - 7) : ℤ)) ∧
    (let x : PowerSeries ℚ := PowerSeries.X
     let a : PowerSeries ℚ := PowerSeries.mk (fun n => (g 3 n : ℚ))
     a * (x^7 - x^6 - x + 1) =
       4*x^14 - 12*x^13 + 7*x^12 + x^11 + x^9 + 7*x^7 -
         2*x^6 - 2*x^5 - 4*x^4 + x^3 + x^2 + x + 3) := by
  have hrec (n : ℕ) (hn : 14 < n) :
      (g 3 n : ℤ) = (g 3 (n-1) : ℤ) + (g 3 (n-6) : ℤ) - (g 3 (n-7) : ℤ) := by
    have h₁ := wy_shift 3 (n-6) (by omega)
    have h₂ := wy_shift 3 (n-7) (by omega)
    rw [show n-6+6 = n by omega] at h₁
    rw [show n-7+6 = n-1 by omega] at h₂
    simp only [hrow]
    omega
  refine ⟨hrec, ?_⟩
  let A := mk (fun n => (g 3 n : ℚ))
  have lhs : A * (X^7-X^6-X+1) = A*X^7 - A*X^6 - A*X^1 + A := by ring
  change A * (X^7-X^6-X+1) = _
  rw [lhs]
  have rhs : 4*X^14 - 12*X^13 + 7*X^12 + X^11 + X^9 + 7*X^7 -
      2*X^6 - 2*X^5 - 4*X^4 + X^3 + X^2 + X + 3 =
      C (4 : ℚ)*X^14 - C 12*X^13 + C 7*X^12 + X^11 + X^9 + C 7*X^7 -
      C 2*X^6 - C 2*X^5 - C 4*X^4 + X^3 + X^2 + X + C 3 := by
    norm_num [map_ofNat]
  rw [rhs]
  ext n
  simp only [map_add, map_sub, coeff_mul_X_pow',
    coeff_X_pow, coeff_X, coeff_C, A, coeff_mk]
  by_cases big : 14 < n
  · simp (disch := omega) only [if_neg, if_pos]
    have hr : (g 3 n : ℚ) = (g 3 (n-1) : ℚ) + (g 3 (n-6) : ℚ) - (g 3 (n-7) : ℚ) := by
      exact_mod_cast hrec n big
    linarith
  · have early (k : ℕ) (hk : k ≤ 14) :
        wy 3 k = ([3,4,5,6,2,0,1,9,10,12,8,7,15,11,16] : List ℕ).getD k 0 := by
      interval_cases k <;> decide
    interval_cases n <;> simp only [hrow] <;> simp (disch := omega) only [early] <;> norm_num [List.getD]
end

theorem OMA.solution : type_of% @OMA.S_oeis_a004484.main := by
  have mex (a n : ℕ) (ha : a ≤ 3) : wyMex a n := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases small : n < 40
      · exact wy_base a n ha small
      · exact wy_lift wy_small_witness a n ha (by omega) (ih (n-6) (by omega))
  intro g hg
  exact wy_conclusion g (fun n => wy_unique mex g hg 3 n (by decide))
