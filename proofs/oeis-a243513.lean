import OMAStatements.S_oeis_a243513
import Mathlib

/-!
Once two successive letters differ, every later letter differs from the two before it. A valid
word is read letter by letter; its state is the last two letters together with which of the
symbols 0, 1, 2, 3 occur. Valid states fall into four classes: all zeros, largest symbol 1,
largest symbol 2, largest symbol at least 3, and the number of continuations from one class to
another depends only on the classes. The class counts are 1, 1, n and (3^n - 2n - 1)/4 for words
of length n + 2, which gives 4 * count n = 7 + 3^n + 2n and then the generating function.
-/

namespace R243513
open OMA.S_oeis_a243513

instance decValid (L : ℕ) : DecidablePred (@validWord L) := fun w => by
  unfold validWord; infer_instance

abbrev St := Fin 5 × Fin 5 × Bool × Bool × Bool × Bool

def info {L : ℕ} (w : Fin (L + 1) → Fin 5) : St :=
  (w ⟨L - 1, by omega⟩, w (Fin.last L), decide (∃ j, (w j).val = 0), decide (∃ j, (w j).val = 1),
    decide (∃ j, (w j).val = 2), decide (∃ j, (w j).val = 3))

def ok : St → Fin 5 → Bool
  | (a, b, r0, r1, r2, r3), x => decide ((0 < x.val → (x.val = 1 ∧ r0 = true) ∨
      (x.val = 2 ∧ r1 = true) ∨ (x.val = 3 ∧ r2 = true) ∨ (x.val = 4 ∧ r3 = true)) ∧
      (a ≠ b → x ≠ a ∧ x ≠ b))

def step : St → Fin 5 → St
  | (_, b, r0, r1, r2, r3), x => (b, x, r0 || decide (x.val = 0), r1 || decide (x.val = 1),
      r2 || decide (x.val = 2), r3 || decide (x.val = 3))

def cls : St → ℕ
  | (a, b, _, _, r2, r3) => if a = b then 0 else if r3 then 3 else if r2 then 2 else 1

def good : St → Bool
  | (a, b, r0, r1, r2, r3) => decide (r0 = true ∧
      ((a = 0 ∧ b = 0 ∧ r1 = false ∧ r2 = false ∧ r3 = false) ∨
       (a = 0 ∧ b = 1 ∧ r1 = true ∧ r2 = false ∧ r3 = false) ∨
       (a ≠ b ∧ a.val ≤ 2 ∧ b.val ≤ 2 ∧ r1 = true ∧ r2 = true ∧ r3 = false) ∨
       (a ≠ b ∧ r1 = true ∧ r2 = true ∧ r3 = true)))

def tm (k k' : ℕ) : ℕ :=
  if k = 0 then (if k' = 0 ∨ k' = 1 then 1 else 0)
  else if k = 1 then (if k' = 2 then 1 else 0)
  else if k = 2 then (if k' = 2 ∨ k' = 3 then 1 else 0)
  else if k' = 3 then 3 else 0

theorem good_step : ∀ t : St, good t = true → ∀ x : Fin 5, ok t x = true →
    good (step t x) = true := by
  rintro ⟨a, b, r0, r1, r2, r3⟩
  revert a b r0 r1 r2 r3
  decide +kernel

theorem trans_count : ∀ t : St, good t = true → ∀ k' < 4,
    (∑ x : Fin 5, if ok t x = true ∧ cls (step t x) = k' then 1 else 0) = tm (cls t) k' := by
  rintro ⟨a, b, r0, r1, r2, r3⟩
  simp only [Fin.sum_univ_five]
  revert a b r0 r1 r2 r3
  decide +kernel

theorem cls_lt : ∀ t : St, cls t < 4 := by
  rintro ⟨a, b, r0, r1, r2, r3⟩
  simp only [cls]
  split_ifs <;> omega

theorem snoc_val {L : ℕ} (w : Fin (L + 1) → Fin 5) (x : Fin 5) (i : Fin (L + 2)) (j : Fin (L + 1))
    (h : i.val = j.val) : (Fin.snoc w x : Fin (L + 2) → Fin 5) i = w j := by
  obtain rfl : i = Fin.castSucc j := Fin.ext h
  exact Fin.snoc_castSucc ..

theorem snoc_val' {L : ℕ} (w : Fin (L + 1) → Fin 5) (x : Fin 5) (i : Fin (L + 2))
    (h : i.val = L + 1) : (Fin.snoc w x : Fin (L + 2) → Fin 5) i = x := by
  obtain rfl : i = Fin.last (L + 1) := Fin.ext h
  exact Fin.snoc_last ..

theorem info_snoc {L : ℕ} (w : Fin (L + 1) → Fin 5) (x : Fin 5) :
    info (Fin.snoc w x : Fin (L + 2) → Fin 5) = step (info w) x := by
  have e2 : ∀ v, (∃ j, ((Fin.snoc w x : Fin (L + 2) → Fin 5) j).val = v) ↔
      (∃ j, (w j).val = v) ∨ x.val = v := fun v =>
    Fin.exists_fin_succ'.trans (by simp only [Fin.snoc_castSucc, Fin.snoc_last])
  simp only [info, step, Prod.mk.injEq, e2, Bool.decide_or, Fin.snoc_last, and_true]
  exact snoc_val w x _ _ (by simp)

theorem rg_iff {ι : Type} (g : ι → ℕ) (m : ℕ) (hm : m < 5) :
    (0 < m → (m = 1 ∧ ∃ j, g j = 0) ∨ (m = 2 ∧ ∃ j, g j = 1) ∨ (m = 3 ∧ ∃ j, g j = 2) ∨
      (m = 4 ∧ ∃ j, g j = 3)) ↔ (0 < m → ∃ j, g j + 1 = m) := by
  constructor
  · intro h hm0
    rcases h hm0 with ⟨h1, j, hj⟩ | ⟨h1, j, hj⟩ | ⟨h1, j, hj⟩ | ⟨h1, j, hj⟩ <;> exact ⟨j, by omega⟩
  · intro h hm0
    obtain ⟨j, hj⟩ := h hm0
    have : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 := by omega
    rcases this with h1 | h1 | h1 | h1
    · exact Or.inl ⟨h1, j, by omega⟩
    · exact Or.inr (Or.inl ⟨h1, j, by omega⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨h1, j, by omega⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h1, j, by omega⟩))

theorem valid_snoc {L : ℕ} (w : Fin (L + 1) → Fin 5) (x : Fin 5) :
    validWord (Fin.snoc w x : Fin (L + 2) → Fin 5) ↔ validWord w ∧ ok (info w) x = true := by
  have key1 : (∀ i : Fin (L + 2), 0 < ((Fin.snoc w x : Fin (L + 2) → Fin 5) i).val →
      ∃ j, j < i ∧ ((Fin.snoc w x : Fin (L + 2) → Fin 5) j).val + 1 =
        ((Fin.snoc w x : Fin (L + 2) → Fin 5) i).val) ↔
      (∀ i : Fin (L + 1), 0 < (w i).val → ∃ j, j < i ∧ (w j).val + 1 = (w i).val) ∧
      (0 < x.val → ∃ j, (w j).val + 1 = x.val) := by
    constructor
    · intro h
      refine ⟨fun i hi => ?_, fun hx => ?_⟩
      · have hi' : 0 < ((Fin.snoc w x : Fin (L + 2) → Fin 5) (Fin.castSucc i)).val := by
          rwa [Fin.snoc_castSucc]
        obtain ⟨j, hj1, hj2⟩ := h _ hi'
        have hj3 := Fin.lt_def.mp hj1
        have hj : j.val < L + 1 := by
          have := i.isLt; simp only [Fin.val_castSucc] at hj3; omega
        refine ⟨⟨j.val, hj⟩, Fin.lt_def.mpr ?_, ?_⟩
        · simpa using hj3
        · rwa [snoc_val w x j ⟨j.val, hj⟩ rfl, Fin.snoc_castSucc] at hj2
      · have hx' : 0 < ((Fin.snoc w x : Fin (L + 2) → Fin 5) (Fin.last _)).val := by
          rwa [Fin.snoc_last]
        obtain ⟨j, hj1, hj2⟩ := h _ hx'
        have hj : j.val < L + 1 := by
          have := Fin.lt_def.mp hj1; simpa using this
        refine ⟨⟨j.val, hj⟩, ?_⟩
        rwa [snoc_val w x j ⟨j.val, hj⟩ rfl, Fin.snoc_last] at hj2
    · rintro ⟨h1, h2⟩ i hi
      by_cases hiL : i.val = L + 1
      · rw [snoc_val' w x i hiL] at hi ⊢
        obtain ⟨j, hj⟩ := h2 hi
        refine ⟨Fin.castSucc j, Fin.lt_def.mpr ?_, ?_⟩
        · have := j.isLt; simp only [Fin.val_castSucc]; omega
        · rwa [Fin.snoc_castSucc]
      · have hi' : i.val < L + 1 := by have := i.isLt; omega
        rw [snoc_val w x i ⟨i.val, hi'⟩ rfl] at hi ⊢
        obtain ⟨j, hj1, hj2⟩ := h1 _ hi
        refine ⟨Fin.castSucc j, Fin.lt_def.mpr ?_, ?_⟩
        · have := Fin.lt_def.mp hj1; simpa using this
        · rwa [Fin.snoc_castSucc]
  have key2 : (∀ i j k : Fin (L + 2), j.val = i.val + 1 → k.val = j.val + 1 →
      (Fin.snoc w x : Fin (L + 2) → Fin 5) i ≠ (Fin.snoc w x : Fin (L + 2) → Fin 5) j →
      (Fin.snoc w x : Fin (L + 2) → Fin 5) k ≠ (Fin.snoc w x : Fin (L + 2) → Fin 5) i ∧
      (Fin.snoc w x : Fin (L + 2) → Fin 5) k ≠ (Fin.snoc w x : Fin (L + 2) → Fin 5) j) ↔
      (∀ i j k : Fin (L + 1), j.val = i.val + 1 → k.val = j.val + 1 → w i ≠ w j →
        w k ≠ w i ∧ w k ≠ w j) ∧
      (w ⟨L - 1, by omega⟩ ≠ w (Fin.last L) →
        x ≠ w ⟨L - 1, by omega⟩ ∧ x ≠ w (Fin.last L)) := by
    constructor
    · intro h
      refine ⟨fun i j k hij hjk hne => ?_, fun hne => ?_⟩
      · have := h (Fin.castSucc i) (Fin.castSucc j) (Fin.castSucc k) (by simpa using hij)
          (by simpa using hjk)
        simp only [Fin.snoc_castSucc] at this
        exact this hne
      · have hL : 1 ≤ L := by
          by_contra h0
          obtain rfl : L = 0 := by omega
          exact hne rfl
        have := h ⟨L - 1, by omega⟩ ⟨L, by omega⟩ (Fin.last _) (by show L = L - 1 + 1; omega) rfl
        rw [snoc_val w x ⟨L - 1, by omega⟩ ⟨L - 1, by omega⟩ rfl,
          snoc_val w x ⟨L, by omega⟩ (Fin.last L) rfl, Fin.snoc_last] at this
        exact this hne
    · rintro ⟨h1, h2⟩ i j k hij hjk
      by_cases hk : k.val = L + 1
      · rw [snoc_val' w x k hk, snoc_val w x i ⟨L - 1, by omega⟩ (by show i.val = L - 1; omega),
          snoc_val w x j (Fin.last L) (by show j.val = L; omega)]
        exact h2
      · have := k.isLt
        rw [snoc_val w x i ⟨i.val, by omega⟩ rfl, snoc_val w x j ⟨j.val, by omega⟩ rfl,
          snoc_val w x k ⟨k.val, by omega⟩ rfl]
        exact h1 _ _ _ hij hjk
  have hC : ok (info w) x = true ↔ (0 < x.val → ∃ j, (w j).val + 1 = x.val) ∧
      (w ⟨L - 1, by omega⟩ ≠ w (Fin.last L) →
        x ≠ w ⟨L - 1, by omega⟩ ∧ x ≠ w (Fin.last L)) := by
    simp only [ok, info, decide_eq_true_eq]
    exact and_congr_left' (rg_iff (fun j => (w j).val) x.val x.isLt)
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨a1, a2⟩ := key1.1 h1
    obtain ⟨b1, b2⟩ := key2.1 h2
    exact ⟨⟨a1, b1⟩, hC.2 ⟨a2, b2⟩⟩
  · rintro ⟨⟨a1, b1⟩, hc⟩
    obtain ⟨a2, b2⟩ := hC.1 hc
    exact ⟨key1.2 ⟨a1, a2⟩, key2.2 ⟨b1, b2⟩⟩

theorem valid0 (w : Fin 1 → Fin 5) : validWord w ↔ w = fun _ => 0 := by
  constructor
  · intro hw
    funext i
    obtain rfl : i = 0 := Subsingleton.elim i 0
    have : (w 0).val = 0 := by
      by_contra hne
      obtain ⟨j, hj, -⟩ := hw.1 0 (Nat.pos_of_ne_zero hne)
      exact Fin.not_lt_zero j hj
    exact Fin.ext this
  · rintro rfl
    exact ⟨fun i hi => absurd hi (lt_irrefl 0), fun i j k hij _ => absurd hij (by
      have := j.isLt; omega)⟩

theorem good_info : ∀ {L : ℕ} {w : Fin (L + 1) → Fin 5}, validWord w → good (info w) = true
  | 0, w, hw => by
      obtain rfl := (valid0 w).1 hw
      decide
  | L + 1, w, hw => by
      obtain ⟨v, y, rfl⟩ : ∃ v y, w = (Fin.snoc v y : Fin (L + 2) → Fin 5) :=
        ⟨Fin.init w, w (Fin.last _), (Fin.snoc_init_self w).symm⟩
      rw [valid_snoc] at hw
      rw [info_snoc]
      exact good_step _ (good_info hw.1) _ hw.2

def N (L k : ℕ) : ℕ :=
  ∑ w : Fin (L + 1) → Fin 5, if validWord w ∧ cls (info w) = k then 1 else 0

theorem sum_cls (L : ℕ) (f : ℕ → ℕ) :
    (∑ w : Fin (L + 1) → Fin 5, if validWord w then f (cls (info w)) else 0) =
      ∑ k ∈ Finset.range 4, f k * N L k := by
  simp only [N, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  by_cases hw : validWord w
  · simp only [hw, true_and, ↓reduceIte, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    simp [cls_lt]
  · simp [hw]

theorem N_succ (L k' : ℕ) (hk : k' < 4) : N (L + 1) k' = ∑ k ∈ Finset.range 4, tm k k' * N L k := by
  rw [← sum_cls L (fun k => tm k k')]
  have e : N (L + 1) k' = ∑ p : Fin 5 × (Fin (L + 1) → Fin 5),
      if validWord (Fin.snoc p.2 p.1 : Fin (L + 2) → Fin 5) ∧
        cls (info (Fin.snoc p.2 p.1 : Fin (L + 2) → Fin 5)) = k' then 1 else 0 :=
    (Equiv.sum_comp (Fin.snocEquiv fun _ => Fin 5) _).symm
  rw [e, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  simp only [valid_snoc, info_snoc]
  by_cases hw : validWord w
  · simp only [hw, true_and, ↓reduceIte]
    exact trans_count (info w) (good_info hw) k' hk
  · simp only [hw, false_and, ↓reduceIte, Finset.sum_const_zero]

theorem N_zero (k : ℕ) : N 0 k = if k = 0 then 1 else 0 := by
  have hc : cls (info (fun _ => 0 : Fin 1 → Fin 5)) = 0 := by decide
  have h : ∀ w : Fin 1 → Fin 5, (validWord w ∧ cls (info w) = k) ↔ (w = fun _ => 0) ∧ 0 = k := by
    intro w
    rw [valid0]
    constructor
    · rintro ⟨rfl, hk⟩
      exact ⟨rfl, hc ▸ hk⟩
    · rintro ⟨rfl, rfl⟩
      exact ⟨rfl, hc⟩
  simp only [N, h]
  by_cases hk : k = 0
  · subst hk; simp
  · simp [hk, Ne.symm hk]

theorem closed (n : ℕ) :
    N (n + 1) 0 = 1 ∧ N (n + 1) 1 = 1 ∧ N (n + 1) 2 = n ∧ 4 * N (n + 1) 3 + 2 * n + 1 = 3 ^ n := by
  have r : ∀ L, N (L + 1) 0 = N L 0 ∧ N (L + 1) 1 = N L 0 ∧ N (L + 1) 2 = N L 1 + N L 2 ∧
      N (L + 1) 3 = N L 2 + 3 * N L 3 := by
    intro L
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [N_succ _ _ (by norm_num)] <;>
      simp [Finset.sum_range_succ, tm]
  induction n with
  | zero =>
    obtain ⟨a, b, c, d⟩ := r 0
    simp only [N_zero] at a b c d
    simp at a b c d ⊢
    omega
  | succ n ih =>
    obtain ⟨a, b, c, d⟩ := r (n + 1)
    rw [a, b, c, d, pow_succ]
    omega

theorem count_eq (n : ℕ) : count n = ∑ k ∈ Finset.range 4, N (n + 1) k := by
  have h := sum_cls (n + 1) (fun _ => 1)
  simp only [one_mul] at h
  rw [← h]
  show Nat.card {w : Fin (n + 1 + 1) → Fin 5 // validWord w} = _
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]

theorem count_formula (n : ℕ) : 4 * count n = 7 + 3 ^ n + 2 * n := by
  obtain ⟨a, b, c, d⟩ := closed n
  rw [count_eq]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  omega

end R243513

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a243513.main := by
  open OMA.S_oeis_a243513 R243513 in
  refine ⟨fun n _ => count_formula n, ?_⟩
  have hq : ∀ m, (count m : ℚ) = (7 + 3 ^ m + 2 * m) / 4 := by
    intro m
    have h' : (4 * count m : ℚ) = 7 + 3 ^ m + 2 * m := by exact_mod_cast count_formula m
    linarith
  rw [show ((1 - X) ^ 2 * (1 - 3 * X) : PowerSeries ℚ)
        = 1 - C 5 * X ^ 1 + C 7 * X ^ 2 - C 3 * X ^ 3 by simp only [map_ofNat]; ring,
      show (X * (3 - 10 * X + 6 * X ^ 2) : PowerSeries ℚ)
        = C 3 * X ^ 1 - C 10 * X ^ 2 + C 6 * X ^ 3 by simp only [map_ofNat]; ring,
      show ∀ p : PowerSeries ℚ, p * (1 - C 5 * X ^ 1 + C 7 * X ^ 2 - C 3 * X ^ 3)
        = p - C 5 * (p * X ^ 1) + C 7 * (p * X ^ 2) - C 3 * (p * X ^ 3) from fun p => by ring]
  ext n
  simp only [series, map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', coeff_mk]
  rcases n with _ | _ | _ | _ | n
  · simp
  · simp [hq]; norm_num
  · simp [hq]; norm_num
  · simp [hq]; norm_num
  · simp [hq]
    ring
