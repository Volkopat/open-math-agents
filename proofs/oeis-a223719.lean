import OMAStatements.S_oeis_a223719

/-!
Proof of Barker's g.f. and recurrence for A223719 (n X 2 arrays over 0..2 with rows,
antidiagonals and columns unimodal).

* A list of length at most two is unimodal. Rows have length 2 and, with only two columns, every
  antidiagonal has at most two entries, so only the two columns are constrained, and they are
  independent: `a n = u n ^ 2`, where `u n` counts the unimodal words of length `n` over 0..2.
* Count unimodal words by their first letter. With `up n x` the number of words `g` of length `n`
  such that `x :: g` is unimodal and `down n x` the number such that `x :: g` is nonincreasing,
  a unimodal word `x :: y :: l` either starts with an ascent `x ≤ y` (and `y :: l` is unimodal)
  or with a strict descent `y < x` (and `y :: l` is nonincreasing), so
  `up (n + 1) x = Sum_{y ≥ x} up n y + Sum_{y < x} down n y` and
  `down (n + 1) x = Sum_{y ≤ x} down n y`, with `up 0 x = down 0 x = 1`.
* A leading 0 does not change unimodality, so `u n = up n 0`. By induction,
  `down n 0 = 1`, `down n 1 = n + 1`, `down n 2 = up n 2 = (n + 1)(n + 2)/2`,
  `up n 1 = 1 + n + n(n + 1)(n + 2)/6` and
  `up n 0 = (n^4 + 6n^3 + 23n^2 + 18n + 24)/24 = C(n + 3, 4) + C(n + 1, 2) + 1`.
* Hence `a n` is a polynomial of degree 8 in `n` (for every `n`), which gives the recurrence by
  substitution and the g.f. by comparing coefficients (the ninth difference of a polynomial of
  degree 8 vanishes).
-/

namespace OMA.Helpers

open OMA.S_oeis_a223719 Finset

/-- Lists of length at most two are unimodal. -/
theorem shortUniA223719 : ∀ l : List (Fin 3), l.length ≤ 2 → Unimodal l
  | [], _ => ⟨[], [], rfl, List.Pairwise.nil, List.Pairwise.nil⟩
  | [x], _ => ⟨[x], [], rfl, List.pairwise_singleton _ _, List.Pairwise.nil⟩
  | [x, y], _ => by
    by_cases hxy : x ≤ y
    · exact ⟨[x, y], [], rfl, by simp [hxy], List.Pairwise.nil⟩
    · exact ⟨[x], [y], rfl, List.pairwise_singleton _ _, List.pairwise_singleton _ _⟩
  | _ :: _ :: _ :: _, h => by simp at h

/-- An antidiagonal of an array with two columns has at most two entries. -/
theorem antidiagLenA223719 {n : ℕ} (A : Fin n → Fin 2 → Fin 3) (d : ℕ) :
    (antidiag A d).length ≤ 2 := by
  unfold antidiag
  rw [List.length_filterMap_eq_countP, List.countP_eq_length_filter]
  refine le_trans ?_ (Finset.card_le_two (a := d - 1) (b := d))
  have hnd := ((List.nodup_finRange n).filter
    (fun i : Fin n => (if h : (i : ℕ) ≤ d ∧ d - i < 2 then some (A i ⟨d - i, h.2⟩)
      else none).isSome)).map Fin.val_injective
  rw [← List.length_map (f := Fin.val), ← List.toFinset_card_of_nodup hnd]
  refine Finset.card_le_card fun x hx => ?_
  simp only [List.mem_toFinset, List.mem_map, List.mem_filter] at hx
  obtain ⟨i, ⟨-, hi⟩, rfl⟩ := hx
  simp at hi
  simp only [Finset.mem_insert, Finset.mem_singleton]
  omega

/-- Only the two columns matter: rows and antidiagonals have at most two entries. -/
theorem goodIffA223719 {n : ℕ} (A : Fin n → Fin 2 → Fin 3) :
    Good A ↔ Unimodal (List.ofFn fun i => A i 0) ∧ Unimodal (List.ofFn fun i => A i 1) := by
  unfold Good
  rw [Fin.forall_fin_two]
  constructor
  · exact fun h => h.2.2
  · exact fun h => ⟨fun i => shortUniA223719 _ (by simp),
      fun d => shortUniA223719 _ (antidiagLenA223719 A d), h⟩

/-- The number of unimodal words of length `n` over 0..2. -/
noncomputable def uA223719 (n : ℕ) : ℕ :=
  Nat.card {c : Fin n → Fin 3 // Unimodal (List.ofFn c)}

/-- A good array is a pair of unimodal columns. -/
def colsEquivA223719 (n : ℕ) :
    {A : Fin n → Fin 2 → Fin 3 // Good A} ≃
      {c : Fin n → Fin 3 // Unimodal (List.ofFn c)} ×
        {c : Fin n → Fin 3 // Unimodal (List.ofFn c)} where
  toFun A := (⟨fun i => A.1 i 0, ((goodIffA223719 A.1).1 A.2).1⟩,
    ⟨fun i => A.1 i 1, ((goodIffA223719 A.1).1 A.2).2⟩)
  invFun p := ⟨fun i => ![p.1.1 i, p.2.1 i],
    (goodIffA223719 _).2 ⟨by simpa using p.1.2, by simpa using p.2.2⟩⟩
  left_inv A := Subtype.ext (funext fun i => funext fun j => by fin_cases j <;> rfl)
  right_inv p := rfl

theorem aEqA223719 (n : ℕ) : a n = uA223719 n ^ 2 := by
  unfold a uA223719
  rw [Nat.card_congr (colsEquivA223719 n), Nat.card_prod, sq]

/-- Dropping the first entry keeps a list unimodal. -/
theorem tailUniA223719 {x : Fin 3} {l : List (Fin 3)} (h : Unimodal (x :: l)) : Unimodal l := by
  obtain ⟨l₁, l₂, he, h₁, h₂⟩ := h
  cases l₁ with
  | nil =>
    simp only [List.nil_append] at he
    subst he
    exact ⟨[], l, rfl, List.Pairwise.nil, h₂.of_cons⟩
  | cons z l₁ =>
    simp only [List.cons_append, List.cons.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨l₁, l₂, rfl, h₁.of_cons, h₂⟩

theorem consGeA223719 (x y : Fin 3) (l : List (Fin 3)) :
    (x :: y :: l).Pairwise (· ≥ ·) ↔ y ≤ x ∧ (y :: l).Pairwise (· ≥ ·) := by
  constructor
  · intro h
    exact ⟨List.rel_of_pairwise_cons h (List.mem_cons_self ..), h.of_cons⟩
  · rintro ⟨hyx, h⟩
    refine List.Pairwise.cons (fun z hz => ?_) h
    rcases List.mem_cons.1 hz with rfl | hz
    · exact hyx
    · exact le_trans (List.rel_of_pairwise_cons h hz) hyx

/-- The first step of a unimodal list: an ascent (then the rest is unimodal) or a strict descent
(then the rest is nonincreasing). -/
theorem consUniA223719 (x y : Fin 3) (l : List (Fin 3)) :
    Unimodal (x :: y :: l) ↔
      (x ≤ y ∧ Unimodal (y :: l)) ∨ (y < x ∧ (y :: l).Pairwise (· ≥ ·)) := by
  constructor
  · intro h
    by_cases hxy : x ≤ y
    · exact Or.inl ⟨hxy, tailUniA223719 h⟩
    · refine Or.inr ⟨lt_of_not_ge hxy, ?_⟩
      obtain ⟨l₁, l₂, he, h₁, h₂⟩ := h
      match l₁, he, h₁ with
      | [], he, _ =>
        simp only [List.nil_append] at he
        subst he
        exact h₂.of_cons
      | [z], he, _ =>
        simp only [List.singleton_append, List.cons.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        exact h₂
      | z :: w :: l₁, he, h₁ =>
        simp only [List.cons_append, List.cons.injEq] at he
        obtain ⟨rfl, rfl, -⟩ := he
        exact absurd (List.rel_of_pairwise_cons h₁ (List.mem_cons_self ..)) hxy
  · rintro (⟨hxy, l₁, l₂, he, h₁, h₂⟩ | ⟨-, h⟩)
    · cases l₁ with
      | nil =>
        simp only [List.nil_append] at he
        subst he
        exact ⟨[x], y :: l, rfl, List.pairwise_singleton _ _, h₂⟩
      | cons z l₁ =>
        simp only [List.cons_append, List.cons.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        refine ⟨x :: y :: l₁, l₂, rfl, List.Pairwise.cons (fun w hw => ?_) h₁, h₂⟩
        rcases List.mem_cons.1 hw with rfl | hw
        · exact hxy
        · exact le_trans hxy (List.rel_of_pairwise_cons h₁ hw)
    · exact ⟨[x], y :: l, rfl, List.pairwise_singleton _ _, h⟩

/-- A leading 0 does not change unimodality. -/
theorem zeroUniA223719 (l : List (Fin 3)) : Unimodal (0 :: l) ↔ Unimodal l := by
  refine ⟨tailUniA223719, fun ⟨l₁, l₂, he, h₁, h₂⟩ => ?_⟩
  exact ⟨0 :: l₁, l₂, by rw [he]; rfl, List.Pairwise.cons (fun w _ => Fin.zero_le w) h₁, h₂⟩

open Classical in
/-- `upA223719 n x` counts the words `g` of length `n` such that `x :: g` is unimodal. -/
noncomputable def upA223719 (n : ℕ) (x : Fin 3) : ℕ :=
  ∑ g : Fin n → Fin 3, if Unimodal (x :: List.ofFn g) then 1 else 0

open Classical in
/-- `downA223719 n x` counts the words `g` of length `n` such that `x :: g` is nonincreasing. -/
noncomputable def downA223719 (n : ℕ) (x : Fin 3) : ℕ :=
  ∑ g : Fin n → Fin 3, if (x :: List.ofFn g).Pairwise (· ≥ ·) then 1 else 0

theorem upZeroA223719 (x : Fin 3) : upA223719 0 x = 1 := by
  have h : Unimodal [x] := shortUniA223719 _ (by simp)
  unfold upA223719
  simp [h]

theorem downZeroA223719 (x : Fin 3) : downA223719 0 x = 1 := by
  unfold downA223719
  simp

theorem upSuccA223719 (n : ℕ) (x : Fin 3) :
    upA223719 (n + 1) x = ∑ y : Fin 3, if x ≤ y then upA223719 n y else downA223719 n y := by
  classical
  unfold upA223719 downA223719
  rw [Fintype.sum_equiv (Fin.consEquiv fun _ => Fin 3).symm _
    (fun p => if Unimodal (x :: List.ofFn (Fin.cons p.1 p.2 : Fin (n + 1) → Fin 3)) then 1 else 0)
    (fun g => by simp), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases hxy : x ≤ y
  · rw [if_pos hxy]
    refine Finset.sum_congr rfl fun g _ => if_congr ?_ rfl rfl
    rw [List.ofFn_cons, consUniA223719]
    constructor
    · rintro (⟨-, h⟩ | ⟨h, -⟩)
      · exact h
      · exact absurd hxy (not_le.2 h)
    · exact fun h => Or.inl ⟨hxy, h⟩
  · rw [if_neg hxy]
    refine Finset.sum_congr rfl fun g _ => if_congr ?_ rfl rfl
    rw [List.ofFn_cons, consUniA223719]
    constructor
    · rintro (⟨h, -⟩ | ⟨-, h⟩)
      · exact absurd h hxy
      · exact h
    · exact fun h => Or.inr ⟨lt_of_not_ge hxy, h⟩

theorem downSuccA223719 (n : ℕ) (x : Fin 3) :
    downA223719 (n + 1) x = ∑ y : Fin 3, if y ≤ x then downA223719 n y else 0 := by
  classical
  unfold downA223719
  rw [Fintype.sum_equiv (Fin.consEquiv fun _ => Fin 3).symm _
    (fun p => if (x :: List.ofFn (Fin.cons p.1 p.2 : Fin (n + 1) → Fin 3)).Pairwise (· ≥ ·)
      then 1 else 0)
    (fun g => by simp), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases hyx : y ≤ x
  · rw [if_pos hyx]
    refine Finset.sum_congr rfl fun g _ => if_congr ?_ rfl rfl
    rw [List.ofFn_cons, consGeA223719]
    exact ⟨fun h => h.2, fun h => ⟨hyx, h⟩⟩
  · rw [if_neg hyx]
    refine Finset.sum_eq_zero fun g _ => if_neg ?_
    rw [List.ofFn_cons, consGeA223719]
    exact fun h => hyx h.1

theorem uEqUpA223719 (n : ℕ) : uA223719 n = upA223719 n 0 := by
  classical
  unfold uA223719 upA223719
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]
  refine Finset.sum_congr rfl fun g _ => if_congr ?_ rfl rfl
  exact (zeroUniA223719 _).symm

theorem downClosedA223719 (n : ℕ) :
    (downA223719 n 0 : ℚ) = 1 ∧ (downA223719 n 1 : ℚ) = n + 1 ∧
      (downA223719 n 2 : ℚ) = (n + 1) * (n + 2) / 2 := by
  induction n with
  | zero => simp only [downZeroA223719]; norm_num
  | succ n ih =>
    obtain ⟨h0, h1, h2⟩ := ih
    simp only [downSuccA223719, Fin.sum_univ_three]
    refine ⟨?_, ?_, ?_⟩
    · simp [h0]
    · simp [h0, h1]
      ring
    · simp [h0, h1, h2]
      ring

theorem upClosedA223719 (n : ℕ) :
    (upA223719 n 2 : ℚ) = (n + 1) * (n + 2) / 2 ∧
      (upA223719 n 1 : ℚ) = 1 + n + n * (n + 1) * (n + 2) / 6 ∧
      (upA223719 n 0 : ℚ) = (n ^ 4 + 6 * n ^ 3 + 23 * n ^ 2 + 18 * n + 24) / 24 := by
  induction n with
  | zero => simp only [upZeroA223719]; norm_num
  | succ n ih =>
    obtain ⟨h2, h1, h0⟩ := ih
    obtain ⟨d0, d1, d2⟩ := downClosedA223719 n
    simp only [upSuccA223719, Fin.sum_univ_three]
    refine ⟨?_, ?_, ?_⟩
    · simp [h2, d0, d1]
      ring
    · simp [h1, h2, d0]
      ring
    · simp [h0, h1, h2]
      ring

/-- The closed form: `a n = u(n)^2` with `u(n) = C(n+3,4) + C(n+1,2) + 1`. -/
theorem closedA223719 (n : ℕ) :
    (a n : ℚ) = ((n ^ 4 + 6 * n ^ 3 + 23 * n ^ 2 + 18 * n + 24) / 24) ^ 2 := by
  rw [aEqA223719, uEqUpA223719]
  push_cast
  rw [(upClosedA223719 n).2.2]

/-- Barker's recurrence, from the closed form. -/
theorem recA223719 (n : ℕ) (hn : 9 < n) :
    (a n : ℤ) = 9 * a (n - 1) - 36 * a (n - 2) + 84 * a (n - 3) -
      126 * a (n - 4) + 126 * a (n - 5) - 84 * a (n - 6) + 36 * a (n - 7) - 9 * a (n - 8) +
      a (n - 9) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 10 := ⟨n - 10, by omega⟩
  rw [show m + 10 - 1 = m + 9 by omega, show m + 10 - 2 = m + 8 by omega,
    show m + 10 - 3 = m + 7 by omega, show m + 10 - 4 = m + 6 by omega,
    show m + 10 - 5 = m + 5 by omega, show m + 10 - 6 = m + 4 by omega,
    show m + 10 - 7 = m + 3 by omega, show m + 10 - 8 = m + 2 by omega,
    show m + 10 - 9 = m + 1 by omega]
  have h : ((a (m + 10) : ℤ) : ℚ) = ((9 * a (m + 9) - 36 * a (m + 8) + 84 * a (m + 7) -
      126 * a (m + 6) + 126 * a (m + 5) - 84 * a (m + 4) + 36 * a (m + 3) - 9 * a (m + 2) +
      a (m + 1) : ℤ) : ℚ) := by
    push_cast
    simp only [closedA223719]
    push_cast
    ring
  exact_mod_cast h

open PowerSeries in
/-- Barker's generating function, from the closed form (a polynomial of degree 8 has vanishing
ninth difference). -/
theorem genFunA223719 :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 9 =
        X * (9 + 79 * X ^ 2 - 80 * X ^ 3 + 106 * X ^ 4 - 68 * X ^ 5 + 31 * X ^ 6 - 8 * X ^ 7 +
          X ^ 8) := by
  set P : ℕ → ℚ := fun n => if n = 0 then (0 : ℚ) else (a n : ℚ) with hP
  have key : PowerSeries.mk P * (1 - X) ^ 9 =
      C 1 * (PowerSeries.mk P * X ^ 0) - C 9 * (PowerSeries.mk P * X ^ 1) +
        C 36 * (PowerSeries.mk P * X ^ 2) - C 84 * (PowerSeries.mk P * X ^ 3) +
        C 126 * (PowerSeries.mk P * X ^ 4) - C 126 * (PowerSeries.mk P * X ^ 5) +
        C 84 * (PowerSeries.mk P * X ^ 6) - C 36 * (PowerSeries.mk P * X ^ 7) +
        C 9 * (PowerSeries.mk P * X ^ 8) - C 1 * (PowerSeries.mk P * X ^ 9) := by
    simp only [map_one, map_ofNat]
    ring
  have hrhs : (X : ℚ⟦X⟧) * (9 + 79 * X ^ 2 - 80 * X ^ 3 + 106 * X ^ 4 - 68 * X ^ 5 +
      31 * X ^ 6 - 8 * X ^ 7 + X ^ 8) =
      C 9 * X ^ 1 + C 79 * X ^ 3 - C 80 * X ^ 4 + C 106 * X ^ 5 - C 68 * X ^ 6 +
        C 31 * X ^ 7 - C 8 * X ^ 8 + C 1 * X ^ 9 := by
    simp only [map_one, map_ofNat]
    ring
  rw [key, hrhs]
  ext k
  simp only [map_sub, map_add, coeff_C_mul_X_pow]
  simp only [coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  by_cases hk : k < 10
  · interval_cases k <;> norm_num [hP, closedA223719]
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 10 := ⟨k - 10, by omega⟩
    simp only [show 0 ≤ j + 10 by omega, show 1 ≤ j + 10 by omega, show 2 ≤ j + 10 by omega,
      show 3 ≤ j + 10 by omega, show 4 ≤ j + 10 by omega, show 5 ≤ j + 10 by omega,
      show 6 ≤ j + 10 by omega, show 7 ≤ j + 10 by omega, show 8 ≤ j + 10 by omega,
      show 9 ≤ j + 10 by omega, show j + 10 - 0 = j + 10 by omega,
      show j + 10 - 1 = j + 9 by omega, show j + 10 - 2 = j + 8 by omega,
      show j + 10 - 3 = j + 7 by omega, show j + 10 - 4 = j + 6 by omega,
      show j + 10 - 5 = j + 5 by omega, show j + 10 - 6 = j + 4 by omega,
      show j + 10 - 7 = j + 3 by omega, show j + 10 - 8 = j + 2 by omega,
      show j + 10 - 9 = j + 1 by omega, show ¬ (j + 10 = 1) by omega,
      show ¬ (j + 10 = 3) by omega, show ¬ (j + 10 = 4) by omega, show ¬ (j + 10 = 5) by omega,
      show ¬ (j + 10 = 6) by omega, show ¬ (j + 10 = 7) by omega, show ¬ (j + 10 = 8) by omega,
      show ¬ (j + 10 = 9) by omega, show ¬ (j + 10 = 0) by omega, show ¬ (j + 9 = 0) by omega,
      show ¬ (j + 8 = 0) by omega, show ¬ (j + 7 = 0) by omega, show ¬ (j + 6 = 0) by omega,
      show ¬ (j + 5 = 0) by omega, show ¬ (j + 4 = 0) by omega, show ¬ (j + 3 = 0) by omega,
      show ¬ (j + 2 = 0) by omega, show ¬ (j + 1 = 0) by omega, if_true, if_false, hP,
      closedA223719]
    push_cast
    ring

end OMA.Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a223719.main :=
  ⟨OMA.Helpers.genFunA223719, OMA.Helpers.recA223719⟩
