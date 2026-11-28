import OMAStatements.S_oeis_a190040
import Mathlib

/-!
Credit: @ivillar
Proof: a transfer-matrix argument on the last three terms. Appending a term y to a valid
nondecreasing word with last three terms (t, a, b) keeps it valid exactly when b <= y and y is one
of t, a, b or a sum of two of them, so the numbers N(m, s) of valid words of length m + 3 with last
three terms s satisfy N(m+1, (a,b,c)) = sum over t of N(m, (t,a,b)). Starting from the words of
length 3, the values up to m = 8 are computed from this recursion, and from m = 8 on every N(m, s)
is a polynomial of degree at most 3 in m (proved by induction). Hence a(n) is a cubic polynomial
for n >= 9, which gives the recurrence for n >= 13; the cases n = 11, 12 are checked from the values.
-/

namespace OMAA190040Helpers

open OMA.S_oeis_a190040 Finset

/-- A valid prefix: nondecreasing and following the rule. -/
def V {L : ℕ} (w : Fin L → Fin 9) : Prop := Monotone w ∧ Rule w

instance decV {L : ℕ} : DecidablePred (V (L := L)) := fun w => by
  unfold V Monotone Rule
  infer_instance

/-- The values as a function on `ℕ` (zero outside). -/
def xv {L : ℕ} (w : Fin L → Fin 9) (i : ℕ) : ℕ := if h : i < L then (w ⟨i, h⟩ : ℕ) else 0

/-- The rule at position `i`, for a function on `ℕ`. -/
def C (f : ℕ → ℕ) (i : ℕ) : Prop :=
  (∃ j, j < i ∧ i ≤ j + 3 ∧ f j = f i) ∨ (∃ j k, j < k ∧ k < i ∧ i ≤ j + 3 ∧ f j + f k = f i)

theorem rule_nat {L : ℕ} (w : Fin L → Fin 9) : Rule w ↔ ∀ i, i < L → 2 ≤ i → C (xv w) i := by
  unfold Rule C
  constructor
  · intro h i hi h2
    rcases h ⟨i, hi⟩ h2 with ⟨j, hj, h3, he⟩ | ⟨j, k, hjk, hk, h3, he⟩
    · refine Or.inl ⟨j, hj, h3, ?_⟩
      simp only [xv, dif_pos j.isLt, dif_pos hi]
      rw [he]
    · refine Or.inr ⟨j, k, hjk, hk, h3, ?_⟩
      simp only [xv, dif_pos j.isLt, dif_pos k.isLt, dif_pos hi]
      exact he
  · intro h i h2
    rcases h i i.isLt h2 with ⟨j, hj, h3, he⟩ | ⟨j, k, hjk, hk, h3, he⟩
    · have hjL : j < L := by omega
      refine Or.inl ⟨⟨j, hjL⟩, hj, h3, ?_⟩
      simp only [xv, dif_pos hjL, dif_pos i.isLt] at he
      exact Fin.ext he
    · have hjL : j < L := by omega
      have hkL : k < L := by omega
      refine Or.inr ⟨⟨j, hjL⟩, ⟨k, hkL⟩, hjk, hk, h3, ?_⟩
      simp only [xv, dif_pos hjL, dif_pos hkL, dif_pos i.isLt] at he
      exact he

theorem C_congr (f g : ℕ → ℕ) (i : ℕ) (h : ∀ j, j ≤ i → f j = g j) : C f i ↔ C g i := by
  unfold C
  constructor
  · rintro (⟨j, hj, h3, he⟩ | ⟨j, k, hjk, hk, h3, he⟩)
    · exact Or.inl ⟨j, hj, h3, by rw [← h j (by omega), ← h i le_rfl]; exact he⟩
    · exact Or.inr ⟨j, k, hjk, hk, h3, by
        rw [← h j (by omega), ← h k (by omega), ← h i le_rfl]; exact he⟩
  · rintro (⟨j, hj, h3, he⟩ | ⟨j, k, hjk, hk, h3, he⟩)
    · exact Or.inl ⟨j, hj, h3, by rw [h j (by omega), h i le_rfl]; exact he⟩
    · exact Or.inr ⟨j, k, hjk, hk, h3, by
        rw [h j (by omega), h k (by omega), h i le_rfl]; exact he⟩

theorem xv_snoc {L : ℕ} (w : Fin L → Fin 9) (y : Fin 9) (i : ℕ) :
    xv (Fin.snoc w y : Fin (L + 1) → Fin 9) i =
      if i < L then xv w i else if i = L then (y : ℕ) else 0 := by
  unfold xv
  by_cases h1 : i < L
  · rw [dif_pos (by omega), if_pos h1, dif_pos h1]
    simp [Fin.snoc, h1]
  · rw [if_neg h1]
    by_cases h2 : i = L
    · subst h2
      rw [dif_pos (by omega), if_pos rfl]
      simp [Fin.snoc]
    · rw [dif_neg (by omega), if_neg h2]

/-- The last three terms of a word of length `m + 3`. -/
def st {m : ℕ} (w : Fin (m + 3) → Fin 9) : ℕ × ℕ × ℕ := (xv w m, xv w (m + 1), xv w (m + 2))

/-- The rule for a new last term `c` after a window `t`. -/
def okw (t : ℕ × ℕ × ℕ) (c : ℕ) : Prop :=
  c = t.1 ∨ c = t.2.1 ∨ c = t.2.2 ∨ c = t.1 + t.2.1 ∨ c = t.1 + t.2.2 ∨ c = t.2.1 + t.2.2

instance : ∀ t c, Decidable (okw t c) := fun t c => by unfold okw; infer_instance

theorem rule_snoc {m : ℕ} (w : Fin (m + 3) → Fin 9) (y : Fin 9) :
    Rule (Fin.snoc w y : Fin (m + 3 + 1) → Fin 9) ↔ Rule w ∧ okw (st w) y := by
  rw [rule_nat, rule_nat]
  have hx := xv_snoc w y
  have e3 : xv (Fin.snoc w y : Fin (m + 3 + 1) → Fin 9) (m + 3) = y := by
    rw [hx]
    simp
  have elt : ∀ j, j < m + 3 → xv (Fin.snoc w y : Fin (m + 3 + 1) → Fin 9) j = xv w j :=
    fun j hj => by rw [hx, if_pos hj]
  constructor
  · intro h
    refine ⟨fun i hi h2 => ?_, ?_⟩
    · have := h i (by omega) h2
      rwa [C_congr _ (xv w) i (fun j hj => elt j (by omega))] at this
    · have h3 := h (m + 3) (by omega) (by omega)
      unfold C at h3
      unfold okw st
      simp only
      rcases h3 with ⟨j, hj, h4, he⟩ | ⟨j, k, hjk, hk, h4, he⟩
      · rw [e3, elt j hj] at he
        have : j = m ∨ j = m + 1 ∨ j = m + 2 := by omega
        rcases this with rfl | rfl | rfl <;> omega
      · rw [e3, elt j (by omega), elt k hk] at he
        have : (j = m ∧ k = m + 1) ∨ (j = m ∧ k = m + 2) ∨ (j = m + 1 ∧ k = m + 2) := by omega
        rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega
  · rintro ⟨h, hok⟩ i hi h2
    by_cases hi3 : i < m + 3
    · rw [C_congr _ (xv w) i (fun j hj => elt j (by omega))]
      exact h i hi3 h2
    · have hi' : i = m + 3 := by omega
      subst hi'
      unfold C
      rw [e3]
      unfold okw st at hok
      simp only at hok
      rcases hok with he | he | he | he | he | he
      · exact Or.inl ⟨m, by omega, by omega, by rw [elt m (by omega)]; omega⟩
      · exact Or.inl ⟨m + 1, by omega, by omega, by rw [elt (m + 1) (by omega)]; omega⟩
      · exact Or.inl ⟨m + 2, by omega, by omega, by rw [elt (m + 2) (by omega)]; omega⟩
      · exact Or.inr ⟨m, m + 1, by omega, by omega, by omega, by
          rw [elt m (by omega), elt (m + 1) (by omega)]; omega⟩
      · exact Or.inr ⟨m, m + 2, by omega, by omega, by omega, by
          rw [elt m (by omega), elt (m + 2) (by omega)]; omega⟩
      · exact Or.inr ⟨m + 1, m + 2, by omega, by omega, by omega, by
          rw [elt (m + 1) (by omega), elt (m + 2) (by omega)]; omega⟩

theorem mono_snoc {k : ℕ} (w : Fin (k + 1) → Fin 9) (y : Fin 9) :
    Monotone (Fin.snoc w y : Fin (k + 1 + 1) → Fin 9) ↔ Monotone w ∧ w (Fin.last k) ≤ y := by
  rw [Fin.monotone_iff_le_succ, Fin.monotone_iff_le_succ, Fin.forall_fin_succ']
  simp only [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last]

theorem st_snoc {m : ℕ} (w : Fin (m + 3) → Fin 9) (y : Fin 9) :
    st (m := m + 1) (Fin.snoc w y : Fin (m + 3 + 1) → Fin 9) = ((st w).2.1, (st w).2.2, (y : ℕ)) := by
  unfold st
  rw [xv_snoc, xv_snoc, xv_snoc, if_pos (by omega), if_pos (by omega)]
  simp

theorem last_eq {m : ℕ} (w : Fin (m + 3) → Fin 9) : (w (Fin.last (m + 2)) : ℕ) = (st w).2.2 := by
  show (w (Fin.last (m + 2)) : ℕ) = xv w (m + 2)
  unfold xv
  rw [dif_pos (by omega)]
  rfl

open Classical in
/-- Number of valid words of length `m + 3` whose last three terms are `s`. -/
noncomputable def N (m : ℕ) (s : ℕ × ℕ × ℕ) : ℕ :=
  #(univ.filter fun w : Fin (m + 3) → Fin 9 => V w ∧ st w = s)

theorem st_lt {m : ℕ} (w : Fin (m + 3) → Fin 9) :
    (st w).1 < 9 ∧ (st w).2.1 < 9 ∧ (st w).2.2 < 9 := by
  unfold st xv
  simp only [dif_pos (show m < m + 3 by omega), dif_pos (show m + 1 < m + 3 by omega),
    dif_pos (show m + 2 < m + 3 by omega)]
  exact ⟨(w _).isLt, (w _).isLt, (w _).isLt⟩

theorem st_mono {m : ℕ} (w : Fin (m + 3) → Fin 9) (hw : Monotone w) :
    (st w).1 ≤ (st w).2.1 ∧ (st w).2.1 ≤ (st w).2.2 := by
  unfold st xv
  simp only [dif_pos (show m < m + 3 by omega), dif_pos (show m + 1 < m + 3 by omega),
    dif_pos (show m + 2 < m + 3 by omega)]
  exact ⟨hw (show (⟨m, by omega⟩ : Fin (m + 3)) ≤ ⟨m + 1, by omega⟩ from by
      rw [Fin.le_iff_val_le_val]; simp),
    hw (show (⟨m + 1, by omega⟩ : Fin (m + 3)) ≤ ⟨m + 2, by omega⟩ from by
      rw [Fin.le_iff_val_le_val]; simp)⟩

theorem N_nonmono (m : ℕ) (s : ℕ × ℕ × ℕ) (h : ¬ (s.1 ≤ s.2.1 ∧ s.2.1 ≤ s.2.2)) : N m s = 0 := by
  classical
  unfold N
  rw [card_eq_zero, filter_eq_empty_iff]
  rintro w - ⟨hV, rfl⟩
  exact h (st_mono w hV.1)

theorem N_big (m : ℕ) (s : ℕ × ℕ × ℕ) (h : 9 ≤ s.2.2) : N m s = 0 := by
  classical
  unfold N
  rw [card_eq_zero, filter_eq_empty_iff]
  rintro w - ⟨-, rfl⟩
  have := (st_lt w).2.2
  omega

theorem mono_snoc3 {m : ℕ} (w : Fin (m + 3) → Fin 9) (y : Fin 9) :
    Monotone (Fin.snoc w y : Fin (m + 3 + 1) → Fin 9) ↔ Monotone w ∧ w (Fin.last (m + 2)) ≤ y :=
  mono_snoc (k := m + 2) w y

theorem V_snoc {m : ℕ} (w : Fin (m + 3) → Fin 9) (y : Fin 9) :
    V (Fin.snoc w y : Fin (m + 3 + 1) → Fin 9) ↔ V w ∧ (st w).2.2 ≤ (y : ℕ) ∧ okw (st w) y := by
  unfold V
  rw [mono_snoc3, rule_snoc, Fin.le_iff_val_le_val, last_eq]
  tauto

theorem cond_iff (V0 : Prop) (s1 s2 s3 a b c : ℕ) (hc : c < 9) :
    ((V0 ∧ s3 ≤ c ∧ okw (s1, s2, s3) c) ∧ (s2, s3, c) = (a, b, c)) ↔
      ((c < 9 ∧ b ≤ c ∧ okw (s1, a, b) c) ∧ V0 ∧ (s1, s2, s3) = (s1, a, b)) := by
  constructor
  · rintro ⟨⟨h0, h1, h2⟩, h3⟩
    simp only [Prod.mk.injEq] at h3
    obtain ⟨rfl, rfl, -⟩ := h3
    exact ⟨⟨hc, h1, h2⟩, h0, rfl⟩
  · rintro ⟨⟨-, h1, h2⟩, h0, h3⟩
    simp only [Prod.mk.injEq] at h3
    obtain ⟨-, rfl, rfl⟩ := h3
    exact ⟨⟨h0, h1, h2⟩, rfl⟩

theorem trans (m a b c : ℕ) :
    N (m + 1) (a, b, c) =
      ∑ t ∈ range 9, if c < 9 ∧ b ≤ c ∧ okw (t, a, b) c then N m (t, a, b) else 0 := by
  classical
  let e : Fin 9 × (Fin (m + 3) → Fin 9) ≃ (Fin (m + 3 + 1) → Fin 9) :=
    { toFun := fun p => Fin.snoc p.2 p.1
      invFun := fun w => (w (Fin.last (m + 3)), Fin.init w)
      left_inv := fun p => by simp [Fin.init_snoc, Fin.snoc_last]
      right_inv := fun w => Fin.snoc_init_self w }
  have hL : N (m + 1) (a, b, c) = ∑ w : Fin (m + 3 + 1) → Fin 9,
      if V w ∧ st (m := m + 1) w = (a, b, c) then 1 else 0 := by
    unfold N
    rw [card_filter]
  rw [hL, ← e.sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  have hR : ∀ t, (if c < 9 ∧ b ≤ c ∧ okw (t, a, b) c then N m (t, a, b) else 0) =
      ∑ v : Fin (m + 3) → Fin 9,
        if (c < 9 ∧ b ≤ c ∧ okw (t, a, b) c) ∧ (V v ∧ st v = (t, a, b)) then 1 else 0 := by
    intro t
    split_ifs with h
    · unfold N
      rw [card_filter]
      exact Finset.sum_congr rfl fun v _ => by simp [h]
    · simp [h]
  rw [Finset.sum_congr rfl fun t _ => hR t]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  have hl : ∀ y, e (y, v) = (Fin.snoc v y : Fin (m + 3 + 1) → Fin 9) := fun y => rfl
  simp only [hl, V_snoc, st_snoc]
  have hs := st_lt v
  rw [Finset.sum_eq_single (st v).1]
  · by_cases hc : c < 9
    · rw [Finset.sum_eq_single ⟨c, hc⟩]
      · generalize st v = s at hs ⊢
        obtain ⟨s1, s2, s3⟩ := s
        exact if_congr (cond_iff (V v) s1 s2 s3 a b c hc) rfl rfl
      · intro y _ hy
        rw [if_neg]
        rintro ⟨-, h⟩
        apply hy
        apply Fin.ext
        simp only [Prod.mk.injEq] at h
        exact h.2.2
      · intro h
        exact absurd (mem_univ _) h
    · rw [Finset.sum_eq_zero, if_neg]
      · rintro ⟨⟨h, -⟩, -⟩
        exact hc h
      · intro y _
        rw [if_neg]
        rintro ⟨-, h⟩
        simp only [Prod.mk.injEq] at h
        have := y.isLt
        omega
  · intro t _ ht
    rw [if_neg]
    rintro ⟨-, -, h⟩
    exact ht (by rw [h])
  · intro h
    exact absurd (mem_range.mpr hs.1) h

theorem st0 (w : Fin 3 → Fin 9) (a b c : ℕ) (ha : a < 9) (hb : b < 9) (hc : c < 9) :
    st (m := 0) w = (a, b, c) ↔ w = ![⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩] := by
  unfold st xv
  simp only [dif_pos (show (0 : ℕ) < 0 + 3 by norm_num), dif_pos (show 0 + 1 < 0 + 3 by norm_num),
    dif_pos (show 0 + 2 < 0 + 3 by norm_num), Prod.mk.injEq]
  constructor
  · rintro ⟨h0, h1, h2⟩
    funext i
    fin_cases i
    · exact Fin.ext h0
    · exact Fin.ext h1
    · exact Fin.ext h2
  · rintro rfl
    exact ⟨rfl, rfl, rfl⟩

theorem N0_one (a b c : ℕ) (ha : a < 9) (hb : b < 9) (hc : c < 9)
    (h : V (![⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩] : Fin 3 → Fin 9)) : N 0 (a, b, c) = 1 := by
  classical
  unfold N
  rw [card_eq_one]
  refine ⟨![⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩], ?_⟩
  ext w
  rw [mem_filter, mem_singleton]
  constructor
  · rintro ⟨-, -, hs⟩
    exact (st0 w a b c ha hb hc).mp hs
  · rintro rfl
    exact ⟨mem_univ _, h, (st0 _ a b c ha hb hc).mpr rfl⟩

theorem N0_zero (a b c : ℕ) (ha : a < 9) (hb : b < 9) (hc : c < 9)
    (h : ¬ V (![⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩] : Fin 3 → Fin 9)) : N 0 (a, b, c) = 0 := by
  classical
  unfold N
  rw [card_eq_zero, filter_eq_empty_iff]
  rintro w - ⟨hV, hs⟩
  rw [(st0 w a b c ha hb hc).mp hs] at hV
  exact h hV

theorem a_eq (m : ℕ) : a (m + 1) = ∑ t ∈ range 9 ×ˢ range 9, N m (t.1, t.2, 8) := by
  classical
  unfold a
  rw [Fintype.card_subtype]
  have e : (univ.filter fun x : Fin (m + 1 + 2) → Fin 9 =>
      Monotone x ∧ x (Fin.last (m + 1 + 1)) = 8 ∧ Rule x) =
      univ.filter fun x : Fin (m + 3) → Fin 9 => V x ∧ (st x).2.2 = 8 := by
    apply filter_congr
    intro x _
    have hl := last_eq (m := m) x
    have h8 : x (Fin.last (m + 2)) = 8 ↔ (x (Fin.last (m + 2)) : ℕ) = 8 := by
      rw [Fin.ext_iff]
      rfl
    unfold V
    change Monotone x ∧ x (Fin.last (m + 2)) = 8 ∧ Rule x ↔ (Monotone x ∧ Rule x) ∧ (st x).2.2 = 8
    rw [h8, hl]
    tauto
  rw [e, card_eq_sum_card_fiberwise (f := fun x : Fin (m + 3) → Fin 9 => ((st x).1, (st x).2.1))
    (t := range 9 ×ˢ range 9) (fun x _ => by
      have := st_lt x
      simp only [coe_product, coe_range, Set.mem_prod, Set.mem_Iio]
      exact ⟨this.1, this.2.1⟩)]
  refine Finset.sum_congr rfl fun t _ => ?_
  unfold N
  rw [filter_filter]
  congr 1
  apply filter_congr
  intro x _
  constructor
  · rintro ⟨⟨hV, h8⟩, ht⟩
    refine ⟨hV, ?_⟩
    rw [← ht, ← h8]
  · rintro ⟨hV, hs⟩
    rw [hs]
    exact ⟨⟨hV, rfl⟩, rfl⟩

theorem tr_s000 (m : ℕ) : N (m + 1) (0, 0, 0) = N m (0, 0, 0) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (1, 0, 0) (by norm_num), N_nonmono m (2, 0, 0) (by norm_num), N_nonmono m (3, 0, 0) (by norm_num), N_nonmono m (4, 0, 0) (by norm_num), N_nonmono m (5, 0, 0) (by norm_num), N_nonmono m (6, 0, 0) (by norm_num), N_nonmono m (7, 0, 0) (by norm_num), N_nonmono m (8, 0, 0) (by norm_num)]
  norm_num [okw]

theorem tr_s001 (m : ℕ) : N (m + 1) (0, 0, 1) = 0 := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (1, 0, 0) (by norm_num), N_nonmono m (2, 0, 0) (by norm_num), N_nonmono m (3, 0, 0) (by norm_num), N_nonmono m (4, 0, 0) (by norm_num), N_nonmono m (5, 0, 0) (by norm_num), N_nonmono m (6, 0, 0) (by norm_num), N_nonmono m (7, 0, 0) (by norm_num), N_nonmono m (8, 0, 0) (by norm_num)]
  norm_num [okw]

theorem tr_s002 (m : ℕ) : N (m + 1) (0, 0, 2) = 0 := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (1, 0, 0) (by norm_num), N_nonmono m (2, 0, 0) (by norm_num), N_nonmono m (3, 0, 0) (by norm_num), N_nonmono m (4, 0, 0) (by norm_num), N_nonmono m (5, 0, 0) (by norm_num), N_nonmono m (6, 0, 0) (by norm_num), N_nonmono m (7, 0, 0) (by norm_num), N_nonmono m (8, 0, 0) (by norm_num)]
  norm_num [okw]

theorem tr_s003 (m : ℕ) : N (m + 1) (0, 0, 3) = 0 := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (1, 0, 0) (by norm_num), N_nonmono m (2, 0, 0) (by norm_num), N_nonmono m (3, 0, 0) (by norm_num), N_nonmono m (4, 0, 0) (by norm_num), N_nonmono m (5, 0, 0) (by norm_num), N_nonmono m (6, 0, 0) (by norm_num), N_nonmono m (7, 0, 0) (by norm_num), N_nonmono m (8, 0, 0) (by norm_num)]
  norm_num [okw]

theorem tr_s004 (m : ℕ) : N (m + 1) (0, 0, 4) = 0 := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (1, 0, 0) (by norm_num), N_nonmono m (2, 0, 0) (by norm_num), N_nonmono m (3, 0, 0) (by norm_num), N_nonmono m (4, 0, 0) (by norm_num), N_nonmono m (5, 0, 0) (by norm_num), N_nonmono m (6, 0, 0) (by norm_num), N_nonmono m (7, 0, 0) (by norm_num), N_nonmono m (8, 0, 0) (by norm_num)]
  norm_num [okw]

theorem tr_s005 (m : ℕ) : N (m + 1) (0, 0, 5) = 0 := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (1, 0, 0) (by norm_num), N_nonmono m (2, 0, 0) (by norm_num), N_nonmono m (3, 0, 0) (by norm_num), N_nonmono m (4, 0, 0) (by norm_num), N_nonmono m (5, 0, 0) (by norm_num), N_nonmono m (6, 0, 0) (by norm_num), N_nonmono m (7, 0, 0) (by norm_num), N_nonmono m (8, 0, 0) (by norm_num)]
  norm_num [okw]

theorem tr_s006 (m : ℕ) : N (m + 1) (0, 0, 6) = 0 := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (1, 0, 0) (by norm_num), N_nonmono m (2, 0, 0) (by norm_num), N_nonmono m (3, 0, 0) (by norm_num), N_nonmono m (4, 0, 0) (by norm_num), N_nonmono m (5, 0, 0) (by norm_num), N_nonmono m (6, 0, 0) (by norm_num), N_nonmono m (7, 0, 0) (by norm_num), N_nonmono m (8, 0, 0) (by norm_num)]
  norm_num [okw]

theorem tr_s007 (m : ℕ) : N (m + 1) (0, 0, 7) = 0 := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (1, 0, 0) (by norm_num), N_nonmono m (2, 0, 0) (by norm_num), N_nonmono m (3, 0, 0) (by norm_num), N_nonmono m (4, 0, 0) (by norm_num), N_nonmono m (5, 0, 0) (by norm_num), N_nonmono m (6, 0, 0) (by norm_num), N_nonmono m (7, 0, 0) (by norm_num), N_nonmono m (8, 0, 0) (by norm_num)]
  norm_num [okw]

theorem tr_s008 (m : ℕ) : N (m + 1) (0, 0, 8) = 0 := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (1, 0, 0) (by norm_num), N_nonmono m (2, 0, 0) (by norm_num), N_nonmono m (3, 0, 0) (by norm_num), N_nonmono m (4, 0, 0) (by norm_num), N_nonmono m (5, 0, 0) (by norm_num), N_nonmono m (6, 0, 0) (by norm_num), N_nonmono m (7, 0, 0) (by norm_num), N_nonmono m (8, 0, 0) (by norm_num)]
  norm_num [okw]

theorem tr_s011 (m : ℕ) : N (m + 1) (0, 1, 1) = N m (0, 0, 1) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (1, 0, 1) (by norm_num), N_nonmono m (2, 0, 1) (by norm_num), N_nonmono m (3, 0, 1) (by norm_num), N_nonmono m (4, 0, 1) (by norm_num), N_nonmono m (5, 0, 1) (by norm_num), N_nonmono m (6, 0, 1) (by norm_num), N_nonmono m (7, 0, 1) (by norm_num), N_nonmono m (8, 0, 1) (by norm_num)]
  norm_num [okw]

theorem tr_s012 (m : ℕ) : N (m + 1) (0, 1, 2) = 0 := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (1, 0, 1) (by norm_num), N_nonmono m (2, 0, 1) (by norm_num), N_nonmono m (3, 0, 1) (by norm_num), N_nonmono m (4, 0, 1) (by norm_num), N_nonmono m (5, 0, 1) (by norm_num), N_nonmono m (6, 0, 1) (by norm_num), N_nonmono m (7, 0, 1) (by norm_num), N_nonmono m (8, 0, 1) (by norm_num)]
  norm_num [okw]

theorem tr_s013 (m : ℕ) : N (m + 1) (0, 1, 3) = 0 := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (1, 0, 1) (by norm_num), N_nonmono m (2, 0, 1) (by norm_num), N_nonmono m (3, 0, 1) (by norm_num), N_nonmono m (4, 0, 1) (by norm_num), N_nonmono m (5, 0, 1) (by norm_num), N_nonmono m (6, 0, 1) (by norm_num), N_nonmono m (7, 0, 1) (by norm_num), N_nonmono m (8, 0, 1) (by norm_num)]
  norm_num [okw]

theorem tr_s014 (m : ℕ) : N (m + 1) (0, 1, 4) = 0 := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (1, 0, 1) (by norm_num), N_nonmono m (2, 0, 1) (by norm_num), N_nonmono m (3, 0, 1) (by norm_num), N_nonmono m (4, 0, 1) (by norm_num), N_nonmono m (5, 0, 1) (by norm_num), N_nonmono m (6, 0, 1) (by norm_num), N_nonmono m (7, 0, 1) (by norm_num), N_nonmono m (8, 0, 1) (by norm_num)]
  norm_num [okw]

theorem tr_s015 (m : ℕ) : N (m + 1) (0, 1, 5) = 0 := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (1, 0, 1) (by norm_num), N_nonmono m (2, 0, 1) (by norm_num), N_nonmono m (3, 0, 1) (by norm_num), N_nonmono m (4, 0, 1) (by norm_num), N_nonmono m (5, 0, 1) (by norm_num), N_nonmono m (6, 0, 1) (by norm_num), N_nonmono m (7, 0, 1) (by norm_num), N_nonmono m (8, 0, 1) (by norm_num)]
  norm_num [okw]

theorem tr_s016 (m : ℕ) : N (m + 1) (0, 1, 6) = 0 := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (1, 0, 1) (by norm_num), N_nonmono m (2, 0, 1) (by norm_num), N_nonmono m (3, 0, 1) (by norm_num), N_nonmono m (4, 0, 1) (by norm_num), N_nonmono m (5, 0, 1) (by norm_num), N_nonmono m (6, 0, 1) (by norm_num), N_nonmono m (7, 0, 1) (by norm_num), N_nonmono m (8, 0, 1) (by norm_num)]
  norm_num [okw]

theorem tr_s017 (m : ℕ) : N (m + 1) (0, 1, 7) = 0 := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (1, 0, 1) (by norm_num), N_nonmono m (2, 0, 1) (by norm_num), N_nonmono m (3, 0, 1) (by norm_num), N_nonmono m (4, 0, 1) (by norm_num), N_nonmono m (5, 0, 1) (by norm_num), N_nonmono m (6, 0, 1) (by norm_num), N_nonmono m (7, 0, 1) (by norm_num), N_nonmono m (8, 0, 1) (by norm_num)]
  norm_num [okw]

theorem tr_s018 (m : ℕ) : N (m + 1) (0, 1, 8) = 0 := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (1, 0, 1) (by norm_num), N_nonmono m (2, 0, 1) (by norm_num), N_nonmono m (3, 0, 1) (by norm_num), N_nonmono m (4, 0, 1) (by norm_num), N_nonmono m (5, 0, 1) (by norm_num), N_nonmono m (6, 0, 1) (by norm_num), N_nonmono m (7, 0, 1) (by norm_num), N_nonmono m (8, 0, 1) (by norm_num)]
  norm_num [okw]

theorem tr_s022 (m : ℕ) : N (m + 1) (0, 2, 2) = N m (0, 0, 2) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (1, 0, 2) (by norm_num), N_nonmono m (2, 0, 2) (by norm_num), N_nonmono m (3, 0, 2) (by norm_num), N_nonmono m (4, 0, 2) (by norm_num), N_nonmono m (5, 0, 2) (by norm_num), N_nonmono m (6, 0, 2) (by norm_num), N_nonmono m (7, 0, 2) (by norm_num), N_nonmono m (8, 0, 2) (by norm_num)]
  norm_num [okw]

theorem tr_s023 (m : ℕ) : N (m + 1) (0, 2, 3) = 0 := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (1, 0, 2) (by norm_num), N_nonmono m (2, 0, 2) (by norm_num), N_nonmono m (3, 0, 2) (by norm_num), N_nonmono m (4, 0, 2) (by norm_num), N_nonmono m (5, 0, 2) (by norm_num), N_nonmono m (6, 0, 2) (by norm_num), N_nonmono m (7, 0, 2) (by norm_num), N_nonmono m (8, 0, 2) (by norm_num)]
  norm_num [okw]

theorem tr_s024 (m : ℕ) : N (m + 1) (0, 2, 4) = 0 := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (1, 0, 2) (by norm_num), N_nonmono m (2, 0, 2) (by norm_num), N_nonmono m (3, 0, 2) (by norm_num), N_nonmono m (4, 0, 2) (by norm_num), N_nonmono m (5, 0, 2) (by norm_num), N_nonmono m (6, 0, 2) (by norm_num), N_nonmono m (7, 0, 2) (by norm_num), N_nonmono m (8, 0, 2) (by norm_num)]
  norm_num [okw]

theorem tr_s025 (m : ℕ) : N (m + 1) (0, 2, 5) = 0 := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (1, 0, 2) (by norm_num), N_nonmono m (2, 0, 2) (by norm_num), N_nonmono m (3, 0, 2) (by norm_num), N_nonmono m (4, 0, 2) (by norm_num), N_nonmono m (5, 0, 2) (by norm_num), N_nonmono m (6, 0, 2) (by norm_num), N_nonmono m (7, 0, 2) (by norm_num), N_nonmono m (8, 0, 2) (by norm_num)]
  norm_num [okw]

theorem tr_s026 (m : ℕ) : N (m + 1) (0, 2, 6) = 0 := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (1, 0, 2) (by norm_num), N_nonmono m (2, 0, 2) (by norm_num), N_nonmono m (3, 0, 2) (by norm_num), N_nonmono m (4, 0, 2) (by norm_num), N_nonmono m (5, 0, 2) (by norm_num), N_nonmono m (6, 0, 2) (by norm_num), N_nonmono m (7, 0, 2) (by norm_num), N_nonmono m (8, 0, 2) (by norm_num)]
  norm_num [okw]

theorem tr_s027 (m : ℕ) : N (m + 1) (0, 2, 7) = 0 := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (1, 0, 2) (by norm_num), N_nonmono m (2, 0, 2) (by norm_num), N_nonmono m (3, 0, 2) (by norm_num), N_nonmono m (4, 0, 2) (by norm_num), N_nonmono m (5, 0, 2) (by norm_num), N_nonmono m (6, 0, 2) (by norm_num), N_nonmono m (7, 0, 2) (by norm_num), N_nonmono m (8, 0, 2) (by norm_num)]
  norm_num [okw]

theorem tr_s028 (m : ℕ) : N (m + 1) (0, 2, 8) = 0 := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (1, 0, 2) (by norm_num), N_nonmono m (2, 0, 2) (by norm_num), N_nonmono m (3, 0, 2) (by norm_num), N_nonmono m (4, 0, 2) (by norm_num), N_nonmono m (5, 0, 2) (by norm_num), N_nonmono m (6, 0, 2) (by norm_num), N_nonmono m (7, 0, 2) (by norm_num), N_nonmono m (8, 0, 2) (by norm_num)]
  norm_num [okw]

theorem tr_s033 (m : ℕ) : N (m + 1) (0, 3, 3) = N m (0, 0, 3) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (1, 0, 3) (by norm_num), N_nonmono m (2, 0, 3) (by norm_num), N_nonmono m (3, 0, 3) (by norm_num), N_nonmono m (4, 0, 3) (by norm_num), N_nonmono m (5, 0, 3) (by norm_num), N_nonmono m (6, 0, 3) (by norm_num), N_nonmono m (7, 0, 3) (by norm_num), N_nonmono m (8, 0, 3) (by norm_num)]
  norm_num [okw]

theorem tr_s034 (m : ℕ) : N (m + 1) (0, 3, 4) = 0 := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (1, 0, 3) (by norm_num), N_nonmono m (2, 0, 3) (by norm_num), N_nonmono m (3, 0, 3) (by norm_num), N_nonmono m (4, 0, 3) (by norm_num), N_nonmono m (5, 0, 3) (by norm_num), N_nonmono m (6, 0, 3) (by norm_num), N_nonmono m (7, 0, 3) (by norm_num), N_nonmono m (8, 0, 3) (by norm_num)]
  norm_num [okw]

theorem tr_s035 (m : ℕ) : N (m + 1) (0, 3, 5) = 0 := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (1, 0, 3) (by norm_num), N_nonmono m (2, 0, 3) (by norm_num), N_nonmono m (3, 0, 3) (by norm_num), N_nonmono m (4, 0, 3) (by norm_num), N_nonmono m (5, 0, 3) (by norm_num), N_nonmono m (6, 0, 3) (by norm_num), N_nonmono m (7, 0, 3) (by norm_num), N_nonmono m (8, 0, 3) (by norm_num)]
  norm_num [okw]

theorem tr_s036 (m : ℕ) : N (m + 1) (0, 3, 6) = 0 := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (1, 0, 3) (by norm_num), N_nonmono m (2, 0, 3) (by norm_num), N_nonmono m (3, 0, 3) (by norm_num), N_nonmono m (4, 0, 3) (by norm_num), N_nonmono m (5, 0, 3) (by norm_num), N_nonmono m (6, 0, 3) (by norm_num), N_nonmono m (7, 0, 3) (by norm_num), N_nonmono m (8, 0, 3) (by norm_num)]
  norm_num [okw]

theorem tr_s037 (m : ℕ) : N (m + 1) (0, 3, 7) = 0 := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (1, 0, 3) (by norm_num), N_nonmono m (2, 0, 3) (by norm_num), N_nonmono m (3, 0, 3) (by norm_num), N_nonmono m (4, 0, 3) (by norm_num), N_nonmono m (5, 0, 3) (by norm_num), N_nonmono m (6, 0, 3) (by norm_num), N_nonmono m (7, 0, 3) (by norm_num), N_nonmono m (8, 0, 3) (by norm_num)]
  norm_num [okw]

theorem tr_s038 (m : ℕ) : N (m + 1) (0, 3, 8) = 0 := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (1, 0, 3) (by norm_num), N_nonmono m (2, 0, 3) (by norm_num), N_nonmono m (3, 0, 3) (by norm_num), N_nonmono m (4, 0, 3) (by norm_num), N_nonmono m (5, 0, 3) (by norm_num), N_nonmono m (6, 0, 3) (by norm_num), N_nonmono m (7, 0, 3) (by norm_num), N_nonmono m (8, 0, 3) (by norm_num)]
  norm_num [okw]

theorem tr_s044 (m : ℕ) : N (m + 1) (0, 4, 4) = N m (0, 0, 4) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (1, 0, 4) (by norm_num), N_nonmono m (2, 0, 4) (by norm_num), N_nonmono m (3, 0, 4) (by norm_num), N_nonmono m (4, 0, 4) (by norm_num), N_nonmono m (5, 0, 4) (by norm_num), N_nonmono m (6, 0, 4) (by norm_num), N_nonmono m (7, 0, 4) (by norm_num), N_nonmono m (8, 0, 4) (by norm_num)]
  norm_num [okw]

theorem tr_s045 (m : ℕ) : N (m + 1) (0, 4, 5) = 0 := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (1, 0, 4) (by norm_num), N_nonmono m (2, 0, 4) (by norm_num), N_nonmono m (3, 0, 4) (by norm_num), N_nonmono m (4, 0, 4) (by norm_num), N_nonmono m (5, 0, 4) (by norm_num), N_nonmono m (6, 0, 4) (by norm_num), N_nonmono m (7, 0, 4) (by norm_num), N_nonmono m (8, 0, 4) (by norm_num)]
  norm_num [okw]

theorem tr_s046 (m : ℕ) : N (m + 1) (0, 4, 6) = 0 := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (1, 0, 4) (by norm_num), N_nonmono m (2, 0, 4) (by norm_num), N_nonmono m (3, 0, 4) (by norm_num), N_nonmono m (4, 0, 4) (by norm_num), N_nonmono m (5, 0, 4) (by norm_num), N_nonmono m (6, 0, 4) (by norm_num), N_nonmono m (7, 0, 4) (by norm_num), N_nonmono m (8, 0, 4) (by norm_num)]
  norm_num [okw]

theorem tr_s047 (m : ℕ) : N (m + 1) (0, 4, 7) = 0 := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (1, 0, 4) (by norm_num), N_nonmono m (2, 0, 4) (by norm_num), N_nonmono m (3, 0, 4) (by norm_num), N_nonmono m (4, 0, 4) (by norm_num), N_nonmono m (5, 0, 4) (by norm_num), N_nonmono m (6, 0, 4) (by norm_num), N_nonmono m (7, 0, 4) (by norm_num), N_nonmono m (8, 0, 4) (by norm_num)]
  norm_num [okw]

theorem tr_s048 (m : ℕ) : N (m + 1) (0, 4, 8) = 0 := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (1, 0, 4) (by norm_num), N_nonmono m (2, 0, 4) (by norm_num), N_nonmono m (3, 0, 4) (by norm_num), N_nonmono m (4, 0, 4) (by norm_num), N_nonmono m (5, 0, 4) (by norm_num), N_nonmono m (6, 0, 4) (by norm_num), N_nonmono m (7, 0, 4) (by norm_num), N_nonmono m (8, 0, 4) (by norm_num)]
  norm_num [okw]

theorem tr_s055 (m : ℕ) : N (m + 1) (0, 5, 5) = N m (0, 0, 5) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (1, 0, 5) (by norm_num), N_nonmono m (2, 0, 5) (by norm_num), N_nonmono m (3, 0, 5) (by norm_num), N_nonmono m (4, 0, 5) (by norm_num), N_nonmono m (5, 0, 5) (by norm_num), N_nonmono m (6, 0, 5) (by norm_num), N_nonmono m (7, 0, 5) (by norm_num), N_nonmono m (8, 0, 5) (by norm_num)]
  norm_num [okw]

theorem tr_s056 (m : ℕ) : N (m + 1) (0, 5, 6) = 0 := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (1, 0, 5) (by norm_num), N_nonmono m (2, 0, 5) (by norm_num), N_nonmono m (3, 0, 5) (by norm_num), N_nonmono m (4, 0, 5) (by norm_num), N_nonmono m (5, 0, 5) (by norm_num), N_nonmono m (6, 0, 5) (by norm_num), N_nonmono m (7, 0, 5) (by norm_num), N_nonmono m (8, 0, 5) (by norm_num)]
  norm_num [okw]

theorem tr_s057 (m : ℕ) : N (m + 1) (0, 5, 7) = 0 := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (1, 0, 5) (by norm_num), N_nonmono m (2, 0, 5) (by norm_num), N_nonmono m (3, 0, 5) (by norm_num), N_nonmono m (4, 0, 5) (by norm_num), N_nonmono m (5, 0, 5) (by norm_num), N_nonmono m (6, 0, 5) (by norm_num), N_nonmono m (7, 0, 5) (by norm_num), N_nonmono m (8, 0, 5) (by norm_num)]
  norm_num [okw]

theorem tr_s058 (m : ℕ) : N (m + 1) (0, 5, 8) = 0 := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (1, 0, 5) (by norm_num), N_nonmono m (2, 0, 5) (by norm_num), N_nonmono m (3, 0, 5) (by norm_num), N_nonmono m (4, 0, 5) (by norm_num), N_nonmono m (5, 0, 5) (by norm_num), N_nonmono m (6, 0, 5) (by norm_num), N_nonmono m (7, 0, 5) (by norm_num), N_nonmono m (8, 0, 5) (by norm_num)]
  norm_num [okw]

theorem tr_s066 (m : ℕ) : N (m + 1) (0, 6, 6) = N m (0, 0, 6) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (1, 0, 6) (by norm_num), N_nonmono m (2, 0, 6) (by norm_num), N_nonmono m (3, 0, 6) (by norm_num), N_nonmono m (4, 0, 6) (by norm_num), N_nonmono m (5, 0, 6) (by norm_num), N_nonmono m (6, 0, 6) (by norm_num), N_nonmono m (7, 0, 6) (by norm_num), N_nonmono m (8, 0, 6) (by norm_num)]
  norm_num [okw]

theorem tr_s067 (m : ℕ) : N (m + 1) (0, 6, 7) = 0 := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (1, 0, 6) (by norm_num), N_nonmono m (2, 0, 6) (by norm_num), N_nonmono m (3, 0, 6) (by norm_num), N_nonmono m (4, 0, 6) (by norm_num), N_nonmono m (5, 0, 6) (by norm_num), N_nonmono m (6, 0, 6) (by norm_num), N_nonmono m (7, 0, 6) (by norm_num), N_nonmono m (8, 0, 6) (by norm_num)]
  norm_num [okw]

theorem tr_s068 (m : ℕ) : N (m + 1) (0, 6, 8) = 0 := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (1, 0, 6) (by norm_num), N_nonmono m (2, 0, 6) (by norm_num), N_nonmono m (3, 0, 6) (by norm_num), N_nonmono m (4, 0, 6) (by norm_num), N_nonmono m (5, 0, 6) (by norm_num), N_nonmono m (6, 0, 6) (by norm_num), N_nonmono m (7, 0, 6) (by norm_num), N_nonmono m (8, 0, 6) (by norm_num)]
  norm_num [okw]

theorem tr_s077 (m : ℕ) : N (m + 1) (0, 7, 7) = N m (0, 0, 7) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (1, 0, 7) (by norm_num), N_nonmono m (2, 0, 7) (by norm_num), N_nonmono m (3, 0, 7) (by norm_num), N_nonmono m (4, 0, 7) (by norm_num), N_nonmono m (5, 0, 7) (by norm_num), N_nonmono m (6, 0, 7) (by norm_num), N_nonmono m (7, 0, 7) (by norm_num), N_nonmono m (8, 0, 7) (by norm_num)]
  norm_num [okw]

theorem tr_s078 (m : ℕ) : N (m + 1) (0, 7, 8) = 0 := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (1, 0, 7) (by norm_num), N_nonmono m (2, 0, 7) (by norm_num), N_nonmono m (3, 0, 7) (by norm_num), N_nonmono m (4, 0, 7) (by norm_num), N_nonmono m (5, 0, 7) (by norm_num), N_nonmono m (6, 0, 7) (by norm_num), N_nonmono m (7, 0, 7) (by norm_num), N_nonmono m (8, 0, 7) (by norm_num)]
  norm_num [okw]

theorem tr_s088 (m : ℕ) : N (m + 1) (0, 8, 8) = N m (0, 0, 8) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (1, 0, 8) (by norm_num), N_nonmono m (2, 0, 8) (by norm_num), N_nonmono m (3, 0, 8) (by norm_num), N_nonmono m (4, 0, 8) (by norm_num), N_nonmono m (5, 0, 8) (by norm_num), N_nonmono m (6, 0, 8) (by norm_num), N_nonmono m (7, 0, 8) (by norm_num), N_nonmono m (8, 0, 8) (by norm_num)]
  norm_num [okw]

theorem tr_s111 (m : ℕ) : N (m + 1) (1, 1, 1) = N m (0, 1, 1) + N m (1, 1, 1) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (2, 1, 1) (by norm_num), N_nonmono m (3, 1, 1) (by norm_num), N_nonmono m (4, 1, 1) (by norm_num), N_nonmono m (5, 1, 1) (by norm_num), N_nonmono m (6, 1, 1) (by norm_num), N_nonmono m (7, 1, 1) (by norm_num), N_nonmono m (8, 1, 1) (by norm_num)]
  norm_num [okw]

theorem tr_s112 (m : ℕ) : N (m + 1) (1, 1, 2) = N m (0, 1, 1) + N m (1, 1, 1) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (2, 1, 1) (by norm_num), N_nonmono m (3, 1, 1) (by norm_num), N_nonmono m (4, 1, 1) (by norm_num), N_nonmono m (5, 1, 1) (by norm_num), N_nonmono m (6, 1, 1) (by norm_num), N_nonmono m (7, 1, 1) (by norm_num), N_nonmono m (8, 1, 1) (by norm_num)]
  norm_num [okw]

theorem tr_s113 (m : ℕ) : N (m + 1) (1, 1, 3) = 0 := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (2, 1, 1) (by norm_num), N_nonmono m (3, 1, 1) (by norm_num), N_nonmono m (4, 1, 1) (by norm_num), N_nonmono m (5, 1, 1) (by norm_num), N_nonmono m (6, 1, 1) (by norm_num), N_nonmono m (7, 1, 1) (by norm_num), N_nonmono m (8, 1, 1) (by norm_num)]
  norm_num [okw]

theorem tr_s114 (m : ℕ) : N (m + 1) (1, 1, 4) = 0 := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (2, 1, 1) (by norm_num), N_nonmono m (3, 1, 1) (by norm_num), N_nonmono m (4, 1, 1) (by norm_num), N_nonmono m (5, 1, 1) (by norm_num), N_nonmono m (6, 1, 1) (by norm_num), N_nonmono m (7, 1, 1) (by norm_num), N_nonmono m (8, 1, 1) (by norm_num)]
  norm_num [okw]

theorem tr_s115 (m : ℕ) : N (m + 1) (1, 1, 5) = 0 := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (2, 1, 1) (by norm_num), N_nonmono m (3, 1, 1) (by norm_num), N_nonmono m (4, 1, 1) (by norm_num), N_nonmono m (5, 1, 1) (by norm_num), N_nonmono m (6, 1, 1) (by norm_num), N_nonmono m (7, 1, 1) (by norm_num), N_nonmono m (8, 1, 1) (by norm_num)]
  norm_num [okw]

theorem tr_s116 (m : ℕ) : N (m + 1) (1, 1, 6) = 0 := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (2, 1, 1) (by norm_num), N_nonmono m (3, 1, 1) (by norm_num), N_nonmono m (4, 1, 1) (by norm_num), N_nonmono m (5, 1, 1) (by norm_num), N_nonmono m (6, 1, 1) (by norm_num), N_nonmono m (7, 1, 1) (by norm_num), N_nonmono m (8, 1, 1) (by norm_num)]
  norm_num [okw]

theorem tr_s117 (m : ℕ) : N (m + 1) (1, 1, 7) = 0 := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (2, 1, 1) (by norm_num), N_nonmono m (3, 1, 1) (by norm_num), N_nonmono m (4, 1, 1) (by norm_num), N_nonmono m (5, 1, 1) (by norm_num), N_nonmono m (6, 1, 1) (by norm_num), N_nonmono m (7, 1, 1) (by norm_num), N_nonmono m (8, 1, 1) (by norm_num)]
  norm_num [okw]

theorem tr_s118 (m : ℕ) : N (m + 1) (1, 1, 8) = 0 := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (2, 1, 1) (by norm_num), N_nonmono m (3, 1, 1) (by norm_num), N_nonmono m (4, 1, 1) (by norm_num), N_nonmono m (5, 1, 1) (by norm_num), N_nonmono m (6, 1, 1) (by norm_num), N_nonmono m (7, 1, 1) (by norm_num), N_nonmono m (8, 1, 1) (by norm_num)]
  norm_num [okw]

theorem tr_s122 (m : ℕ) : N (m + 1) (1, 2, 2) = N m (0, 1, 2) + N m (1, 1, 2) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (2, 1, 2) (by norm_num), N_nonmono m (3, 1, 2) (by norm_num), N_nonmono m (4, 1, 2) (by norm_num), N_nonmono m (5, 1, 2) (by norm_num), N_nonmono m (6, 1, 2) (by norm_num), N_nonmono m (7, 1, 2) (by norm_num), N_nonmono m (8, 1, 2) (by norm_num)]
  norm_num [okw]

theorem tr_s123 (m : ℕ) : N (m + 1) (1, 2, 3) = N m (0, 1, 2) + N m (1, 1, 2) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (2, 1, 2) (by norm_num), N_nonmono m (3, 1, 2) (by norm_num), N_nonmono m (4, 1, 2) (by norm_num), N_nonmono m (5, 1, 2) (by norm_num), N_nonmono m (6, 1, 2) (by norm_num), N_nonmono m (7, 1, 2) (by norm_num), N_nonmono m (8, 1, 2) (by norm_num)]
  norm_num [okw]

theorem tr_s124 (m : ℕ) : N (m + 1) (1, 2, 4) = 0 := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (2, 1, 2) (by norm_num), N_nonmono m (3, 1, 2) (by norm_num), N_nonmono m (4, 1, 2) (by norm_num), N_nonmono m (5, 1, 2) (by norm_num), N_nonmono m (6, 1, 2) (by norm_num), N_nonmono m (7, 1, 2) (by norm_num), N_nonmono m (8, 1, 2) (by norm_num)]
  norm_num [okw]

theorem tr_s125 (m : ℕ) : N (m + 1) (1, 2, 5) = 0 := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (2, 1, 2) (by norm_num), N_nonmono m (3, 1, 2) (by norm_num), N_nonmono m (4, 1, 2) (by norm_num), N_nonmono m (5, 1, 2) (by norm_num), N_nonmono m (6, 1, 2) (by norm_num), N_nonmono m (7, 1, 2) (by norm_num), N_nonmono m (8, 1, 2) (by norm_num)]
  norm_num [okw]

theorem tr_s126 (m : ℕ) : N (m + 1) (1, 2, 6) = 0 := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (2, 1, 2) (by norm_num), N_nonmono m (3, 1, 2) (by norm_num), N_nonmono m (4, 1, 2) (by norm_num), N_nonmono m (5, 1, 2) (by norm_num), N_nonmono m (6, 1, 2) (by norm_num), N_nonmono m (7, 1, 2) (by norm_num), N_nonmono m (8, 1, 2) (by norm_num)]
  norm_num [okw]

theorem tr_s127 (m : ℕ) : N (m + 1) (1, 2, 7) = 0 := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (2, 1, 2) (by norm_num), N_nonmono m (3, 1, 2) (by norm_num), N_nonmono m (4, 1, 2) (by norm_num), N_nonmono m (5, 1, 2) (by norm_num), N_nonmono m (6, 1, 2) (by norm_num), N_nonmono m (7, 1, 2) (by norm_num), N_nonmono m (8, 1, 2) (by norm_num)]
  norm_num [okw]

theorem tr_s128 (m : ℕ) : N (m + 1) (1, 2, 8) = 0 := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (2, 1, 2) (by norm_num), N_nonmono m (3, 1, 2) (by norm_num), N_nonmono m (4, 1, 2) (by norm_num), N_nonmono m (5, 1, 2) (by norm_num), N_nonmono m (6, 1, 2) (by norm_num), N_nonmono m (7, 1, 2) (by norm_num), N_nonmono m (8, 1, 2) (by norm_num)]
  norm_num [okw]

theorem tr_s133 (m : ℕ) : N (m + 1) (1, 3, 3) = N m (0, 1, 3) + N m (1, 1, 3) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (2, 1, 3) (by norm_num), N_nonmono m (3, 1, 3) (by norm_num), N_nonmono m (4, 1, 3) (by norm_num), N_nonmono m (5, 1, 3) (by norm_num), N_nonmono m (6, 1, 3) (by norm_num), N_nonmono m (7, 1, 3) (by norm_num), N_nonmono m (8, 1, 3) (by norm_num)]
  norm_num [okw]

theorem tr_s134 (m : ℕ) : N (m + 1) (1, 3, 4) = N m (0, 1, 3) + N m (1, 1, 3) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (2, 1, 3) (by norm_num), N_nonmono m (3, 1, 3) (by norm_num), N_nonmono m (4, 1, 3) (by norm_num), N_nonmono m (5, 1, 3) (by norm_num), N_nonmono m (6, 1, 3) (by norm_num), N_nonmono m (7, 1, 3) (by norm_num), N_nonmono m (8, 1, 3) (by norm_num)]
  norm_num [okw]

theorem tr_s135 (m : ℕ) : N (m + 1) (1, 3, 5) = 0 := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (2, 1, 3) (by norm_num), N_nonmono m (3, 1, 3) (by norm_num), N_nonmono m (4, 1, 3) (by norm_num), N_nonmono m (5, 1, 3) (by norm_num), N_nonmono m (6, 1, 3) (by norm_num), N_nonmono m (7, 1, 3) (by norm_num), N_nonmono m (8, 1, 3) (by norm_num)]
  norm_num [okw]

theorem tr_s136 (m : ℕ) : N (m + 1) (1, 3, 6) = 0 := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (2, 1, 3) (by norm_num), N_nonmono m (3, 1, 3) (by norm_num), N_nonmono m (4, 1, 3) (by norm_num), N_nonmono m (5, 1, 3) (by norm_num), N_nonmono m (6, 1, 3) (by norm_num), N_nonmono m (7, 1, 3) (by norm_num), N_nonmono m (8, 1, 3) (by norm_num)]
  norm_num [okw]

theorem tr_s137 (m : ℕ) : N (m + 1) (1, 3, 7) = 0 := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (2, 1, 3) (by norm_num), N_nonmono m (3, 1, 3) (by norm_num), N_nonmono m (4, 1, 3) (by norm_num), N_nonmono m (5, 1, 3) (by norm_num), N_nonmono m (6, 1, 3) (by norm_num), N_nonmono m (7, 1, 3) (by norm_num), N_nonmono m (8, 1, 3) (by norm_num)]
  norm_num [okw]

theorem tr_s138 (m : ℕ) : N (m + 1) (1, 3, 8) = 0 := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (2, 1, 3) (by norm_num), N_nonmono m (3, 1, 3) (by norm_num), N_nonmono m (4, 1, 3) (by norm_num), N_nonmono m (5, 1, 3) (by norm_num), N_nonmono m (6, 1, 3) (by norm_num), N_nonmono m (7, 1, 3) (by norm_num), N_nonmono m (8, 1, 3) (by norm_num)]
  norm_num [okw]

theorem tr_s144 (m : ℕ) : N (m + 1) (1, 4, 4) = N m (0, 1, 4) + N m (1, 1, 4) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (2, 1, 4) (by norm_num), N_nonmono m (3, 1, 4) (by norm_num), N_nonmono m (4, 1, 4) (by norm_num), N_nonmono m (5, 1, 4) (by norm_num), N_nonmono m (6, 1, 4) (by norm_num), N_nonmono m (7, 1, 4) (by norm_num), N_nonmono m (8, 1, 4) (by norm_num)]
  norm_num [okw]

theorem tr_s145 (m : ℕ) : N (m + 1) (1, 4, 5) = N m (0, 1, 4) + N m (1, 1, 4) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (2, 1, 4) (by norm_num), N_nonmono m (3, 1, 4) (by norm_num), N_nonmono m (4, 1, 4) (by norm_num), N_nonmono m (5, 1, 4) (by norm_num), N_nonmono m (6, 1, 4) (by norm_num), N_nonmono m (7, 1, 4) (by norm_num), N_nonmono m (8, 1, 4) (by norm_num)]
  norm_num [okw]

theorem tr_s146 (m : ℕ) : N (m + 1) (1, 4, 6) = 0 := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (2, 1, 4) (by norm_num), N_nonmono m (3, 1, 4) (by norm_num), N_nonmono m (4, 1, 4) (by norm_num), N_nonmono m (5, 1, 4) (by norm_num), N_nonmono m (6, 1, 4) (by norm_num), N_nonmono m (7, 1, 4) (by norm_num), N_nonmono m (8, 1, 4) (by norm_num)]
  norm_num [okw]

theorem tr_s147 (m : ℕ) : N (m + 1) (1, 4, 7) = 0 := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (2, 1, 4) (by norm_num), N_nonmono m (3, 1, 4) (by norm_num), N_nonmono m (4, 1, 4) (by norm_num), N_nonmono m (5, 1, 4) (by norm_num), N_nonmono m (6, 1, 4) (by norm_num), N_nonmono m (7, 1, 4) (by norm_num), N_nonmono m (8, 1, 4) (by norm_num)]
  norm_num [okw]

theorem tr_s148 (m : ℕ) : N (m + 1) (1, 4, 8) = 0 := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (2, 1, 4) (by norm_num), N_nonmono m (3, 1, 4) (by norm_num), N_nonmono m (4, 1, 4) (by norm_num), N_nonmono m (5, 1, 4) (by norm_num), N_nonmono m (6, 1, 4) (by norm_num), N_nonmono m (7, 1, 4) (by norm_num), N_nonmono m (8, 1, 4) (by norm_num)]
  norm_num [okw]

theorem tr_s155 (m : ℕ) : N (m + 1) (1, 5, 5) = N m (0, 1, 5) + N m (1, 1, 5) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (2, 1, 5) (by norm_num), N_nonmono m (3, 1, 5) (by norm_num), N_nonmono m (4, 1, 5) (by norm_num), N_nonmono m (5, 1, 5) (by norm_num), N_nonmono m (6, 1, 5) (by norm_num), N_nonmono m (7, 1, 5) (by norm_num), N_nonmono m (8, 1, 5) (by norm_num)]
  norm_num [okw]

theorem tr_s156 (m : ℕ) : N (m + 1) (1, 5, 6) = N m (0, 1, 5) + N m (1, 1, 5) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (2, 1, 5) (by norm_num), N_nonmono m (3, 1, 5) (by norm_num), N_nonmono m (4, 1, 5) (by norm_num), N_nonmono m (5, 1, 5) (by norm_num), N_nonmono m (6, 1, 5) (by norm_num), N_nonmono m (7, 1, 5) (by norm_num), N_nonmono m (8, 1, 5) (by norm_num)]
  norm_num [okw]

theorem tr_s157 (m : ℕ) : N (m + 1) (1, 5, 7) = 0 := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (2, 1, 5) (by norm_num), N_nonmono m (3, 1, 5) (by norm_num), N_nonmono m (4, 1, 5) (by norm_num), N_nonmono m (5, 1, 5) (by norm_num), N_nonmono m (6, 1, 5) (by norm_num), N_nonmono m (7, 1, 5) (by norm_num), N_nonmono m (8, 1, 5) (by norm_num)]
  norm_num [okw]

theorem tr_s158 (m : ℕ) : N (m + 1) (1, 5, 8) = 0 := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (2, 1, 5) (by norm_num), N_nonmono m (3, 1, 5) (by norm_num), N_nonmono m (4, 1, 5) (by norm_num), N_nonmono m (5, 1, 5) (by norm_num), N_nonmono m (6, 1, 5) (by norm_num), N_nonmono m (7, 1, 5) (by norm_num), N_nonmono m (8, 1, 5) (by norm_num)]
  norm_num [okw]

theorem tr_s166 (m : ℕ) : N (m + 1) (1, 6, 6) = N m (0, 1, 6) + N m (1, 1, 6) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (2, 1, 6) (by norm_num), N_nonmono m (3, 1, 6) (by norm_num), N_nonmono m (4, 1, 6) (by norm_num), N_nonmono m (5, 1, 6) (by norm_num), N_nonmono m (6, 1, 6) (by norm_num), N_nonmono m (7, 1, 6) (by norm_num), N_nonmono m (8, 1, 6) (by norm_num)]
  norm_num [okw]

theorem tr_s167 (m : ℕ) : N (m + 1) (1, 6, 7) = N m (0, 1, 6) + N m (1, 1, 6) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (2, 1, 6) (by norm_num), N_nonmono m (3, 1, 6) (by norm_num), N_nonmono m (4, 1, 6) (by norm_num), N_nonmono m (5, 1, 6) (by norm_num), N_nonmono m (6, 1, 6) (by norm_num), N_nonmono m (7, 1, 6) (by norm_num), N_nonmono m (8, 1, 6) (by norm_num)]
  norm_num [okw]

theorem tr_s168 (m : ℕ) : N (m + 1) (1, 6, 8) = 0 := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (2, 1, 6) (by norm_num), N_nonmono m (3, 1, 6) (by norm_num), N_nonmono m (4, 1, 6) (by norm_num), N_nonmono m (5, 1, 6) (by norm_num), N_nonmono m (6, 1, 6) (by norm_num), N_nonmono m (7, 1, 6) (by norm_num), N_nonmono m (8, 1, 6) (by norm_num)]
  norm_num [okw]

theorem tr_s177 (m : ℕ) : N (m + 1) (1, 7, 7) = N m (0, 1, 7) + N m (1, 1, 7) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (2, 1, 7) (by norm_num), N_nonmono m (3, 1, 7) (by norm_num), N_nonmono m (4, 1, 7) (by norm_num), N_nonmono m (5, 1, 7) (by norm_num), N_nonmono m (6, 1, 7) (by norm_num), N_nonmono m (7, 1, 7) (by norm_num), N_nonmono m (8, 1, 7) (by norm_num)]
  norm_num [okw]

theorem tr_s178 (m : ℕ) : N (m + 1) (1, 7, 8) = N m (0, 1, 7) + N m (1, 1, 7) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (2, 1, 7) (by norm_num), N_nonmono m (3, 1, 7) (by norm_num), N_nonmono m (4, 1, 7) (by norm_num), N_nonmono m (5, 1, 7) (by norm_num), N_nonmono m (6, 1, 7) (by norm_num), N_nonmono m (7, 1, 7) (by norm_num), N_nonmono m (8, 1, 7) (by norm_num)]
  norm_num [okw]

theorem tr_s188 (m : ℕ) : N (m + 1) (1, 8, 8) = N m (0, 1, 8) + N m (1, 1, 8) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (2, 1, 8) (by norm_num), N_nonmono m (3, 1, 8) (by norm_num), N_nonmono m (4, 1, 8) (by norm_num), N_nonmono m (5, 1, 8) (by norm_num), N_nonmono m (6, 1, 8) (by norm_num), N_nonmono m (7, 1, 8) (by norm_num), N_nonmono m (8, 1, 8) (by norm_num)]
  norm_num [okw]

theorem tr_s222 (m : ℕ) : N (m + 1) (2, 2, 2) = N m (0, 2, 2) + N m (1, 2, 2) + N m (2, 2, 2) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (3, 2, 2) (by norm_num), N_nonmono m (4, 2, 2) (by norm_num), N_nonmono m (5, 2, 2) (by norm_num), N_nonmono m (6, 2, 2) (by norm_num), N_nonmono m (7, 2, 2) (by norm_num), N_nonmono m (8, 2, 2) (by norm_num)]
  norm_num [okw]

theorem tr_s223 (m : ℕ) : N (m + 1) (2, 2, 3) = N m (1, 2, 2) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (3, 2, 2) (by norm_num), N_nonmono m (4, 2, 2) (by norm_num), N_nonmono m (5, 2, 2) (by norm_num), N_nonmono m (6, 2, 2) (by norm_num), N_nonmono m (7, 2, 2) (by norm_num), N_nonmono m (8, 2, 2) (by norm_num)]
  norm_num [okw]

theorem tr_s224 (m : ℕ) : N (m + 1) (2, 2, 4) = N m (0, 2, 2) + N m (1, 2, 2) + N m (2, 2, 2) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (3, 2, 2) (by norm_num), N_nonmono m (4, 2, 2) (by norm_num), N_nonmono m (5, 2, 2) (by norm_num), N_nonmono m (6, 2, 2) (by norm_num), N_nonmono m (7, 2, 2) (by norm_num), N_nonmono m (8, 2, 2) (by norm_num)]
  norm_num [okw]

theorem tr_s225 (m : ℕ) : N (m + 1) (2, 2, 5) = 0 := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (3, 2, 2) (by norm_num), N_nonmono m (4, 2, 2) (by norm_num), N_nonmono m (5, 2, 2) (by norm_num), N_nonmono m (6, 2, 2) (by norm_num), N_nonmono m (7, 2, 2) (by norm_num), N_nonmono m (8, 2, 2) (by norm_num)]
  norm_num [okw]

theorem tr_s226 (m : ℕ) : N (m + 1) (2, 2, 6) = 0 := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (3, 2, 2) (by norm_num), N_nonmono m (4, 2, 2) (by norm_num), N_nonmono m (5, 2, 2) (by norm_num), N_nonmono m (6, 2, 2) (by norm_num), N_nonmono m (7, 2, 2) (by norm_num), N_nonmono m (8, 2, 2) (by norm_num)]
  norm_num [okw]

theorem tr_s227 (m : ℕ) : N (m + 1) (2, 2, 7) = 0 := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (3, 2, 2) (by norm_num), N_nonmono m (4, 2, 2) (by norm_num), N_nonmono m (5, 2, 2) (by norm_num), N_nonmono m (6, 2, 2) (by norm_num), N_nonmono m (7, 2, 2) (by norm_num), N_nonmono m (8, 2, 2) (by norm_num)]
  norm_num [okw]

theorem tr_s228 (m : ℕ) : N (m + 1) (2, 2, 8) = 0 := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (3, 2, 2) (by norm_num), N_nonmono m (4, 2, 2) (by norm_num), N_nonmono m (5, 2, 2) (by norm_num), N_nonmono m (6, 2, 2) (by norm_num), N_nonmono m (7, 2, 2) (by norm_num), N_nonmono m (8, 2, 2) (by norm_num)]
  norm_num [okw]

theorem tr_s233 (m : ℕ) : N (m + 1) (2, 3, 3) = N m (0, 2, 3) + N m (1, 2, 3) + N m (2, 2, 3) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (3, 2, 3) (by norm_num), N_nonmono m (4, 2, 3) (by norm_num), N_nonmono m (5, 2, 3) (by norm_num), N_nonmono m (6, 2, 3) (by norm_num), N_nonmono m (7, 2, 3) (by norm_num), N_nonmono m (8, 2, 3) (by norm_num)]
  norm_num [okw]

theorem tr_s234 (m : ℕ) : N (m + 1) (2, 3, 4) = N m (1, 2, 3) + N m (2, 2, 3) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (3, 2, 3) (by norm_num), N_nonmono m (4, 2, 3) (by norm_num), N_nonmono m (5, 2, 3) (by norm_num), N_nonmono m (6, 2, 3) (by norm_num), N_nonmono m (7, 2, 3) (by norm_num), N_nonmono m (8, 2, 3) (by norm_num)]
  norm_num [okw]

theorem tr_s235 (m : ℕ) : N (m + 1) (2, 3, 5) = N m (0, 2, 3) + N m (1, 2, 3) + N m (2, 2, 3) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (3, 2, 3) (by norm_num), N_nonmono m (4, 2, 3) (by norm_num), N_nonmono m (5, 2, 3) (by norm_num), N_nonmono m (6, 2, 3) (by norm_num), N_nonmono m (7, 2, 3) (by norm_num), N_nonmono m (8, 2, 3) (by norm_num)]
  norm_num [okw]

theorem tr_s236 (m : ℕ) : N (m + 1) (2, 3, 6) = 0 := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (3, 2, 3) (by norm_num), N_nonmono m (4, 2, 3) (by norm_num), N_nonmono m (5, 2, 3) (by norm_num), N_nonmono m (6, 2, 3) (by norm_num), N_nonmono m (7, 2, 3) (by norm_num), N_nonmono m (8, 2, 3) (by norm_num)]
  norm_num [okw]

theorem tr_s237 (m : ℕ) : N (m + 1) (2, 3, 7) = 0 := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (3, 2, 3) (by norm_num), N_nonmono m (4, 2, 3) (by norm_num), N_nonmono m (5, 2, 3) (by norm_num), N_nonmono m (6, 2, 3) (by norm_num), N_nonmono m (7, 2, 3) (by norm_num), N_nonmono m (8, 2, 3) (by norm_num)]
  norm_num [okw]

theorem tr_s238 (m : ℕ) : N (m + 1) (2, 3, 8) = 0 := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (3, 2, 3) (by norm_num), N_nonmono m (4, 2, 3) (by norm_num), N_nonmono m (5, 2, 3) (by norm_num), N_nonmono m (6, 2, 3) (by norm_num), N_nonmono m (7, 2, 3) (by norm_num), N_nonmono m (8, 2, 3) (by norm_num)]
  norm_num [okw]

theorem tr_s244 (m : ℕ) : N (m + 1) (2, 4, 4) = N m (0, 2, 4) + N m (1, 2, 4) + N m (2, 2, 4) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (3, 2, 4) (by norm_num), N_nonmono m (4, 2, 4) (by norm_num), N_nonmono m (5, 2, 4) (by norm_num), N_nonmono m (6, 2, 4) (by norm_num), N_nonmono m (7, 2, 4) (by norm_num), N_nonmono m (8, 2, 4) (by norm_num)]
  norm_num [okw]

theorem tr_s245 (m : ℕ) : N (m + 1) (2, 4, 5) = N m (1, 2, 4) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (3, 2, 4) (by norm_num), N_nonmono m (4, 2, 4) (by norm_num), N_nonmono m (5, 2, 4) (by norm_num), N_nonmono m (6, 2, 4) (by norm_num), N_nonmono m (7, 2, 4) (by norm_num), N_nonmono m (8, 2, 4) (by norm_num)]
  norm_num [okw]

theorem tr_s246 (m : ℕ) : N (m + 1) (2, 4, 6) = N m (0, 2, 4) + N m (1, 2, 4) + N m (2, 2, 4) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (3, 2, 4) (by norm_num), N_nonmono m (4, 2, 4) (by norm_num), N_nonmono m (5, 2, 4) (by norm_num), N_nonmono m (6, 2, 4) (by norm_num), N_nonmono m (7, 2, 4) (by norm_num), N_nonmono m (8, 2, 4) (by norm_num)]
  norm_num [okw]

theorem tr_s247 (m : ℕ) : N (m + 1) (2, 4, 7) = 0 := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (3, 2, 4) (by norm_num), N_nonmono m (4, 2, 4) (by norm_num), N_nonmono m (5, 2, 4) (by norm_num), N_nonmono m (6, 2, 4) (by norm_num), N_nonmono m (7, 2, 4) (by norm_num), N_nonmono m (8, 2, 4) (by norm_num)]
  norm_num [okw]

theorem tr_s248 (m : ℕ) : N (m + 1) (2, 4, 8) = 0 := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (3, 2, 4) (by norm_num), N_nonmono m (4, 2, 4) (by norm_num), N_nonmono m (5, 2, 4) (by norm_num), N_nonmono m (6, 2, 4) (by norm_num), N_nonmono m (7, 2, 4) (by norm_num), N_nonmono m (8, 2, 4) (by norm_num)]
  norm_num [okw]

theorem tr_s255 (m : ℕ) : N (m + 1) (2, 5, 5) = N m (0, 2, 5) + N m (1, 2, 5) + N m (2, 2, 5) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (3, 2, 5) (by norm_num), N_nonmono m (4, 2, 5) (by norm_num), N_nonmono m (5, 2, 5) (by norm_num), N_nonmono m (6, 2, 5) (by norm_num), N_nonmono m (7, 2, 5) (by norm_num), N_nonmono m (8, 2, 5) (by norm_num)]
  norm_num [okw]

theorem tr_s256 (m : ℕ) : N (m + 1) (2, 5, 6) = N m (1, 2, 5) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (3, 2, 5) (by norm_num), N_nonmono m (4, 2, 5) (by norm_num), N_nonmono m (5, 2, 5) (by norm_num), N_nonmono m (6, 2, 5) (by norm_num), N_nonmono m (7, 2, 5) (by norm_num), N_nonmono m (8, 2, 5) (by norm_num)]
  norm_num [okw]

theorem tr_s257 (m : ℕ) : N (m + 1) (2, 5, 7) = N m (0, 2, 5) + N m (1, 2, 5) + N m (2, 2, 5) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (3, 2, 5) (by norm_num), N_nonmono m (4, 2, 5) (by norm_num), N_nonmono m (5, 2, 5) (by norm_num), N_nonmono m (6, 2, 5) (by norm_num), N_nonmono m (7, 2, 5) (by norm_num), N_nonmono m (8, 2, 5) (by norm_num)]
  norm_num [okw]

theorem tr_s258 (m : ℕ) : N (m + 1) (2, 5, 8) = 0 := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (3, 2, 5) (by norm_num), N_nonmono m (4, 2, 5) (by norm_num), N_nonmono m (5, 2, 5) (by norm_num), N_nonmono m (6, 2, 5) (by norm_num), N_nonmono m (7, 2, 5) (by norm_num), N_nonmono m (8, 2, 5) (by norm_num)]
  norm_num [okw]

theorem tr_s266 (m : ℕ) : N (m + 1) (2, 6, 6) = N m (0, 2, 6) + N m (1, 2, 6) + N m (2, 2, 6) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (3, 2, 6) (by norm_num), N_nonmono m (4, 2, 6) (by norm_num), N_nonmono m (5, 2, 6) (by norm_num), N_nonmono m (6, 2, 6) (by norm_num), N_nonmono m (7, 2, 6) (by norm_num), N_nonmono m (8, 2, 6) (by norm_num)]
  norm_num [okw]

theorem tr_s267 (m : ℕ) : N (m + 1) (2, 6, 7) = N m (1, 2, 6) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (3, 2, 6) (by norm_num), N_nonmono m (4, 2, 6) (by norm_num), N_nonmono m (5, 2, 6) (by norm_num), N_nonmono m (6, 2, 6) (by norm_num), N_nonmono m (7, 2, 6) (by norm_num), N_nonmono m (8, 2, 6) (by norm_num)]
  norm_num [okw]

theorem tr_s268 (m : ℕ) : N (m + 1) (2, 6, 8) = N m (0, 2, 6) + N m (1, 2, 6) + N m (2, 2, 6) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (3, 2, 6) (by norm_num), N_nonmono m (4, 2, 6) (by norm_num), N_nonmono m (5, 2, 6) (by norm_num), N_nonmono m (6, 2, 6) (by norm_num), N_nonmono m (7, 2, 6) (by norm_num), N_nonmono m (8, 2, 6) (by norm_num)]
  norm_num [okw]

theorem tr_s277 (m : ℕ) : N (m + 1) (2, 7, 7) = N m (0, 2, 7) + N m (1, 2, 7) + N m (2, 2, 7) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (3, 2, 7) (by norm_num), N_nonmono m (4, 2, 7) (by norm_num), N_nonmono m (5, 2, 7) (by norm_num), N_nonmono m (6, 2, 7) (by norm_num), N_nonmono m (7, 2, 7) (by norm_num), N_nonmono m (8, 2, 7) (by norm_num)]
  norm_num [okw]

theorem tr_s278 (m : ℕ) : N (m + 1) (2, 7, 8) = N m (1, 2, 7) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (3, 2, 7) (by norm_num), N_nonmono m (4, 2, 7) (by norm_num), N_nonmono m (5, 2, 7) (by norm_num), N_nonmono m (6, 2, 7) (by norm_num), N_nonmono m (7, 2, 7) (by norm_num), N_nonmono m (8, 2, 7) (by norm_num)]
  norm_num [okw]

theorem tr_s288 (m : ℕ) : N (m + 1) (2, 8, 8) = N m (0, 2, 8) + N m (1, 2, 8) + N m (2, 2, 8) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (3, 2, 8) (by norm_num), N_nonmono m (4, 2, 8) (by norm_num), N_nonmono m (5, 2, 8) (by norm_num), N_nonmono m (6, 2, 8) (by norm_num), N_nonmono m (7, 2, 8) (by norm_num), N_nonmono m (8, 2, 8) (by norm_num)]
  norm_num [okw]

theorem tr_s333 (m : ℕ) : N (m + 1) (3, 3, 3) = N m (0, 3, 3) + N m (1, 3, 3) + N m (2, 3, 3) + N m (3, 3, 3) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (4, 3, 3) (by norm_num), N_nonmono m (5, 3, 3) (by norm_num), N_nonmono m (6, 3, 3) (by norm_num), N_nonmono m (7, 3, 3) (by norm_num), N_nonmono m (8, 3, 3) (by norm_num)]
  norm_num [okw]

theorem tr_s334 (m : ℕ) : N (m + 1) (3, 3, 4) = N m (1, 3, 3) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (4, 3, 3) (by norm_num), N_nonmono m (5, 3, 3) (by norm_num), N_nonmono m (6, 3, 3) (by norm_num), N_nonmono m (7, 3, 3) (by norm_num), N_nonmono m (8, 3, 3) (by norm_num)]
  norm_num [okw]

theorem tr_s335 (m : ℕ) : N (m + 1) (3, 3, 5) = N m (2, 3, 3) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (4, 3, 3) (by norm_num), N_nonmono m (5, 3, 3) (by norm_num), N_nonmono m (6, 3, 3) (by norm_num), N_nonmono m (7, 3, 3) (by norm_num), N_nonmono m (8, 3, 3) (by norm_num)]
  norm_num [okw]

theorem tr_s336 (m : ℕ) : N (m + 1) (3, 3, 6) = N m (0, 3, 3) + N m (1, 3, 3) + N m (2, 3, 3) + N m (3, 3, 3) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (4, 3, 3) (by norm_num), N_nonmono m (5, 3, 3) (by norm_num), N_nonmono m (6, 3, 3) (by norm_num), N_nonmono m (7, 3, 3) (by norm_num), N_nonmono m (8, 3, 3) (by norm_num)]
  norm_num [okw]

theorem tr_s337 (m : ℕ) : N (m + 1) (3, 3, 7) = 0 := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (4, 3, 3) (by norm_num), N_nonmono m (5, 3, 3) (by norm_num), N_nonmono m (6, 3, 3) (by norm_num), N_nonmono m (7, 3, 3) (by norm_num), N_nonmono m (8, 3, 3) (by norm_num)]
  norm_num [okw]

theorem tr_s338 (m : ℕ) : N (m + 1) (3, 3, 8) = 0 := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (4, 3, 3) (by norm_num), N_nonmono m (5, 3, 3) (by norm_num), N_nonmono m (6, 3, 3) (by norm_num), N_nonmono m (7, 3, 3) (by norm_num), N_nonmono m (8, 3, 3) (by norm_num)]
  norm_num [okw]

theorem tr_s344 (m : ℕ) : N (m + 1) (3, 4, 4) = N m (0, 3, 4) + N m (1, 3, 4) + N m (2, 3, 4) + N m (3, 3, 4) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (4, 3, 4) (by norm_num), N_nonmono m (5, 3, 4) (by norm_num), N_nonmono m (6, 3, 4) (by norm_num), N_nonmono m (7, 3, 4) (by norm_num), N_nonmono m (8, 3, 4) (by norm_num)]
  norm_num [okw]

theorem tr_s345 (m : ℕ) : N (m + 1) (3, 4, 5) = N m (1, 3, 4) + N m (2, 3, 4) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (4, 3, 4) (by norm_num), N_nonmono m (5, 3, 4) (by norm_num), N_nonmono m (6, 3, 4) (by norm_num), N_nonmono m (7, 3, 4) (by norm_num), N_nonmono m (8, 3, 4) (by norm_num)]
  norm_num [okw]

theorem tr_s346 (m : ℕ) : N (m + 1) (3, 4, 6) = N m (2, 3, 4) + N m (3, 3, 4) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (4, 3, 4) (by norm_num), N_nonmono m (5, 3, 4) (by norm_num), N_nonmono m (6, 3, 4) (by norm_num), N_nonmono m (7, 3, 4) (by norm_num), N_nonmono m (8, 3, 4) (by norm_num)]
  norm_num [okw]

theorem tr_s347 (m : ℕ) : N (m + 1) (3, 4, 7) = N m (0, 3, 4) + N m (1, 3, 4) + N m (2, 3, 4) + N m (3, 3, 4) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (4, 3, 4) (by norm_num), N_nonmono m (5, 3, 4) (by norm_num), N_nonmono m (6, 3, 4) (by norm_num), N_nonmono m (7, 3, 4) (by norm_num), N_nonmono m (8, 3, 4) (by norm_num)]
  norm_num [okw]

theorem tr_s348 (m : ℕ) : N (m + 1) (3, 4, 8) = 0 := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (4, 3, 4) (by norm_num), N_nonmono m (5, 3, 4) (by norm_num), N_nonmono m (6, 3, 4) (by norm_num), N_nonmono m (7, 3, 4) (by norm_num), N_nonmono m (8, 3, 4) (by norm_num)]
  norm_num [okw]

theorem tr_s355 (m : ℕ) : N (m + 1) (3, 5, 5) = N m (0, 3, 5) + N m (1, 3, 5) + N m (2, 3, 5) + N m (3, 3, 5) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (4, 3, 5) (by norm_num), N_nonmono m (5, 3, 5) (by norm_num), N_nonmono m (6, 3, 5) (by norm_num), N_nonmono m (7, 3, 5) (by norm_num), N_nonmono m (8, 3, 5) (by norm_num)]
  norm_num [okw]

theorem tr_s356 (m : ℕ) : N (m + 1) (3, 5, 6) = N m (1, 3, 5) + N m (3, 3, 5) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (4, 3, 5) (by norm_num), N_nonmono m (5, 3, 5) (by norm_num), N_nonmono m (6, 3, 5) (by norm_num), N_nonmono m (7, 3, 5) (by norm_num), N_nonmono m (8, 3, 5) (by norm_num)]
  norm_num [okw]

theorem tr_s357 (m : ℕ) : N (m + 1) (3, 5, 7) = N m (2, 3, 5) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (4, 3, 5) (by norm_num), N_nonmono m (5, 3, 5) (by norm_num), N_nonmono m (6, 3, 5) (by norm_num), N_nonmono m (7, 3, 5) (by norm_num), N_nonmono m (8, 3, 5) (by norm_num)]
  norm_num [okw]

theorem tr_s358 (m : ℕ) : N (m + 1) (3, 5, 8) = N m (0, 3, 5) + N m (1, 3, 5) + N m (2, 3, 5) + N m (3, 3, 5) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (4, 3, 5) (by norm_num), N_nonmono m (5, 3, 5) (by norm_num), N_nonmono m (6, 3, 5) (by norm_num), N_nonmono m (7, 3, 5) (by norm_num), N_nonmono m (8, 3, 5) (by norm_num)]
  norm_num [okw]

theorem tr_s366 (m : ℕ) : N (m + 1) (3, 6, 6) = N m (0, 3, 6) + N m (1, 3, 6) + N m (2, 3, 6) + N m (3, 3, 6) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (4, 3, 6) (by norm_num), N_nonmono m (5, 3, 6) (by norm_num), N_nonmono m (6, 3, 6) (by norm_num), N_nonmono m (7, 3, 6) (by norm_num), N_nonmono m (8, 3, 6) (by norm_num)]
  norm_num [okw]

theorem tr_s367 (m : ℕ) : N (m + 1) (3, 6, 7) = N m (1, 3, 6) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (4, 3, 6) (by norm_num), N_nonmono m (5, 3, 6) (by norm_num), N_nonmono m (6, 3, 6) (by norm_num), N_nonmono m (7, 3, 6) (by norm_num), N_nonmono m (8, 3, 6) (by norm_num)]
  norm_num [okw]

theorem tr_s368 (m : ℕ) : N (m + 1) (3, 6, 8) = N m (2, 3, 6) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (4, 3, 6) (by norm_num), N_nonmono m (5, 3, 6) (by norm_num), N_nonmono m (6, 3, 6) (by norm_num), N_nonmono m (7, 3, 6) (by norm_num), N_nonmono m (8, 3, 6) (by norm_num)]
  norm_num [okw]

theorem tr_s377 (m : ℕ) : N (m + 1) (3, 7, 7) = N m (0, 3, 7) + N m (1, 3, 7) + N m (2, 3, 7) + N m (3, 3, 7) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (4, 3, 7) (by norm_num), N_nonmono m (5, 3, 7) (by norm_num), N_nonmono m (6, 3, 7) (by norm_num), N_nonmono m (7, 3, 7) (by norm_num), N_nonmono m (8, 3, 7) (by norm_num)]
  norm_num [okw]

theorem tr_s378 (m : ℕ) : N (m + 1) (3, 7, 8) = N m (1, 3, 7) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (4, 3, 7) (by norm_num), N_nonmono m (5, 3, 7) (by norm_num), N_nonmono m (6, 3, 7) (by norm_num), N_nonmono m (7, 3, 7) (by norm_num), N_nonmono m (8, 3, 7) (by norm_num)]
  norm_num [okw]

theorem tr_s388 (m : ℕ) : N (m + 1) (3, 8, 8) = N m (0, 3, 8) + N m (1, 3, 8) + N m (2, 3, 8) + N m (3, 3, 8) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (4, 3, 8) (by norm_num), N_nonmono m (5, 3, 8) (by norm_num), N_nonmono m (6, 3, 8) (by norm_num), N_nonmono m (7, 3, 8) (by norm_num), N_nonmono m (8, 3, 8) (by norm_num)]
  norm_num [okw]

theorem tr_s444 (m : ℕ) : N (m + 1) (4, 4, 4) = N m (0, 4, 4) + N m (1, 4, 4) + N m (2, 4, 4) + N m (3, 4, 4) + N m (4, 4, 4) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (5, 4, 4) (by norm_num), N_nonmono m (6, 4, 4) (by norm_num), N_nonmono m (7, 4, 4) (by norm_num), N_nonmono m (8, 4, 4) (by norm_num)]
  norm_num [okw]

theorem tr_s445 (m : ℕ) : N (m + 1) (4, 4, 5) = N m (1, 4, 4) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (5, 4, 4) (by norm_num), N_nonmono m (6, 4, 4) (by norm_num), N_nonmono m (7, 4, 4) (by norm_num), N_nonmono m (8, 4, 4) (by norm_num)]
  norm_num [okw]

theorem tr_s446 (m : ℕ) : N (m + 1) (4, 4, 6) = N m (2, 4, 4) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (5, 4, 4) (by norm_num), N_nonmono m (6, 4, 4) (by norm_num), N_nonmono m (7, 4, 4) (by norm_num), N_nonmono m (8, 4, 4) (by norm_num)]
  norm_num [okw]

theorem tr_s447 (m : ℕ) : N (m + 1) (4, 4, 7) = N m (3, 4, 4) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (5, 4, 4) (by norm_num), N_nonmono m (6, 4, 4) (by norm_num), N_nonmono m (7, 4, 4) (by norm_num), N_nonmono m (8, 4, 4) (by norm_num)]
  norm_num [okw]

theorem tr_s448 (m : ℕ) : N (m + 1) (4, 4, 8) = N m (0, 4, 4) + N m (1, 4, 4) + N m (2, 4, 4) + N m (3, 4, 4) + N m (4, 4, 4) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (5, 4, 4) (by norm_num), N_nonmono m (6, 4, 4) (by norm_num), N_nonmono m (7, 4, 4) (by norm_num), N_nonmono m (8, 4, 4) (by norm_num)]
  norm_num [okw]

theorem tr_s455 (m : ℕ) : N (m + 1) (4, 5, 5) = N m (0, 4, 5) + N m (1, 4, 5) + N m (2, 4, 5) + N m (3, 4, 5) + N m (4, 4, 5) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (5, 4, 5) (by norm_num), N_nonmono m (6, 4, 5) (by norm_num), N_nonmono m (7, 4, 5) (by norm_num), N_nonmono m (8, 4, 5) (by norm_num)]
  norm_num [okw]

theorem tr_s456 (m : ℕ) : N (m + 1) (4, 5, 6) = N m (1, 4, 5) + N m (2, 4, 5) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (5, 4, 5) (by norm_num), N_nonmono m (6, 4, 5) (by norm_num), N_nonmono m (7, 4, 5) (by norm_num), N_nonmono m (8, 4, 5) (by norm_num)]
  norm_num [okw]

theorem tr_s457 (m : ℕ) : N (m + 1) (4, 5, 7) = N m (2, 4, 5) + N m (3, 4, 5) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (5, 4, 5) (by norm_num), N_nonmono m (6, 4, 5) (by norm_num), N_nonmono m (7, 4, 5) (by norm_num), N_nonmono m (8, 4, 5) (by norm_num)]
  norm_num [okw]

theorem tr_s458 (m : ℕ) : N (m + 1) (4, 5, 8) = N m (3, 4, 5) + N m (4, 4, 5) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (5, 4, 5) (by norm_num), N_nonmono m (6, 4, 5) (by norm_num), N_nonmono m (7, 4, 5) (by norm_num), N_nonmono m (8, 4, 5) (by norm_num)]
  norm_num [okw]

theorem tr_s466 (m : ℕ) : N (m + 1) (4, 6, 6) = N m (0, 4, 6) + N m (1, 4, 6) + N m (2, 4, 6) + N m (3, 4, 6) + N m (4, 4, 6) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (5, 4, 6) (by norm_num), N_nonmono m (6, 4, 6) (by norm_num), N_nonmono m (7, 4, 6) (by norm_num), N_nonmono m (8, 4, 6) (by norm_num)]
  norm_num [okw]

theorem tr_s467 (m : ℕ) : N (m + 1) (4, 6, 7) = N m (1, 4, 6) + N m (3, 4, 6) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (5, 4, 6) (by norm_num), N_nonmono m (6, 4, 6) (by norm_num), N_nonmono m (7, 4, 6) (by norm_num), N_nonmono m (8, 4, 6) (by norm_num)]
  norm_num [okw]

theorem tr_s468 (m : ℕ) : N (m + 1) (4, 6, 8) = N m (2, 4, 6) + N m (4, 4, 6) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (5, 4, 6) (by norm_num), N_nonmono m (6, 4, 6) (by norm_num), N_nonmono m (7, 4, 6) (by norm_num), N_nonmono m (8, 4, 6) (by norm_num)]
  norm_num [okw]

theorem tr_s477 (m : ℕ) : N (m + 1) (4, 7, 7) = N m (0, 4, 7) + N m (1, 4, 7) + N m (2, 4, 7) + N m (3, 4, 7) + N m (4, 4, 7) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (5, 4, 7) (by norm_num), N_nonmono m (6, 4, 7) (by norm_num), N_nonmono m (7, 4, 7) (by norm_num), N_nonmono m (8, 4, 7) (by norm_num)]
  norm_num [okw]

theorem tr_s478 (m : ℕ) : N (m + 1) (4, 7, 8) = N m (1, 4, 7) + N m (4, 4, 7) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (5, 4, 7) (by norm_num), N_nonmono m (6, 4, 7) (by norm_num), N_nonmono m (7, 4, 7) (by norm_num), N_nonmono m (8, 4, 7) (by norm_num)]
  norm_num [okw]

theorem tr_s488 (m : ℕ) : N (m + 1) (4, 8, 8) = N m (0, 4, 8) + N m (1, 4, 8) + N m (2, 4, 8) + N m (3, 4, 8) + N m (4, 4, 8) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (5, 4, 8) (by norm_num), N_nonmono m (6, 4, 8) (by norm_num), N_nonmono m (7, 4, 8) (by norm_num), N_nonmono m (8, 4, 8) (by norm_num)]
  norm_num [okw]

theorem tr_s555 (m : ℕ) : N (m + 1) (5, 5, 5) = N m (0, 5, 5) + N m (1, 5, 5) + N m (2, 5, 5) + N m (3, 5, 5) + N m (4, 5, 5) + N m (5, 5, 5) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (6, 5, 5) (by norm_num), N_nonmono m (7, 5, 5) (by norm_num), N_nonmono m (8, 5, 5) (by norm_num)]
  norm_num [okw]

theorem tr_s556 (m : ℕ) : N (m + 1) (5, 5, 6) = N m (1, 5, 5) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (6, 5, 5) (by norm_num), N_nonmono m (7, 5, 5) (by norm_num), N_nonmono m (8, 5, 5) (by norm_num)]
  norm_num [okw]

theorem tr_s557 (m : ℕ) : N (m + 1) (5, 5, 7) = N m (2, 5, 5) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (6, 5, 5) (by norm_num), N_nonmono m (7, 5, 5) (by norm_num), N_nonmono m (8, 5, 5) (by norm_num)]
  norm_num [okw]

theorem tr_s558 (m : ℕ) : N (m + 1) (5, 5, 8) = N m (3, 5, 5) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (6, 5, 5) (by norm_num), N_nonmono m (7, 5, 5) (by norm_num), N_nonmono m (8, 5, 5) (by norm_num)]
  norm_num [okw]

theorem tr_s566 (m : ℕ) : N (m + 1) (5, 6, 6) = N m (0, 5, 6) + N m (1, 5, 6) + N m (2, 5, 6) + N m (3, 5, 6) + N m (4, 5, 6) + N m (5, 5, 6) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (6, 5, 6) (by norm_num), N_nonmono m (7, 5, 6) (by norm_num), N_nonmono m (8, 5, 6) (by norm_num)]
  norm_num [okw]

theorem tr_s567 (m : ℕ) : N (m + 1) (5, 6, 7) = N m (1, 5, 6) + N m (2, 5, 6) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (6, 5, 6) (by norm_num), N_nonmono m (7, 5, 6) (by norm_num), N_nonmono m (8, 5, 6) (by norm_num)]
  norm_num [okw]

theorem tr_s568 (m : ℕ) : N (m + 1) (5, 6, 8) = N m (2, 5, 6) + N m (3, 5, 6) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (6, 5, 6) (by norm_num), N_nonmono m (7, 5, 6) (by norm_num), N_nonmono m (8, 5, 6) (by norm_num)]
  norm_num [okw]

theorem tr_s577 (m : ℕ) : N (m + 1) (5, 7, 7) = N m (0, 5, 7) + N m (1, 5, 7) + N m (2, 5, 7) + N m (3, 5, 7) + N m (4, 5, 7) + N m (5, 5, 7) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (6, 5, 7) (by norm_num), N_nonmono m (7, 5, 7) (by norm_num), N_nonmono m (8, 5, 7) (by norm_num)]
  norm_num [okw]

theorem tr_s578 (m : ℕ) : N (m + 1) (5, 7, 8) = N m (1, 5, 7) + N m (3, 5, 7) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (6, 5, 7) (by norm_num), N_nonmono m (7, 5, 7) (by norm_num), N_nonmono m (8, 5, 7) (by norm_num)]
  norm_num [okw]

theorem tr_s588 (m : ℕ) : N (m + 1) (5, 8, 8) = N m (0, 5, 8) + N m (1, 5, 8) + N m (2, 5, 8) + N m (3, 5, 8) + N m (4, 5, 8) + N m (5, 5, 8) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (6, 5, 8) (by norm_num), N_nonmono m (7, 5, 8) (by norm_num), N_nonmono m (8, 5, 8) (by norm_num)]
  norm_num [okw]

theorem tr_s666 (m : ℕ) : N (m + 1) (6, 6, 6) = N m (0, 6, 6) + N m (1, 6, 6) + N m (2, 6, 6) + N m (3, 6, 6) + N m (4, 6, 6) + N m (5, 6, 6) + N m (6, 6, 6) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (7, 6, 6) (by norm_num), N_nonmono m (8, 6, 6) (by norm_num)]
  norm_num [okw]

theorem tr_s667 (m : ℕ) : N (m + 1) (6, 6, 7) = N m (1, 6, 6) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (7, 6, 6) (by norm_num), N_nonmono m (8, 6, 6) (by norm_num)]
  norm_num [okw]

theorem tr_s668 (m : ℕ) : N (m + 1) (6, 6, 8) = N m (2, 6, 6) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (7, 6, 6) (by norm_num), N_nonmono m (8, 6, 6) (by norm_num)]
  norm_num [okw]

theorem tr_s677 (m : ℕ) : N (m + 1) (6, 7, 7) = N m (0, 6, 7) + N m (1, 6, 7) + N m (2, 6, 7) + N m (3, 6, 7) + N m (4, 6, 7) + N m (5, 6, 7) + N m (6, 6, 7) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (7, 6, 7) (by norm_num), N_nonmono m (8, 6, 7) (by norm_num)]
  norm_num [okw]

theorem tr_s678 (m : ℕ) : N (m + 1) (6, 7, 8) = N m (1, 6, 7) + N m (2, 6, 7) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (7, 6, 7) (by norm_num), N_nonmono m (8, 6, 7) (by norm_num)]
  norm_num [okw]

theorem tr_s688 (m : ℕ) : N (m + 1) (6, 8, 8) = N m (0, 6, 8) + N m (1, 6, 8) + N m (2, 6, 8) + N m (3, 6, 8) + N m (4, 6, 8) + N m (5, 6, 8) + N m (6, 6, 8) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (7, 6, 8) (by norm_num), N_nonmono m (8, 6, 8) (by norm_num)]
  norm_num [okw]

theorem tr_s777 (m : ℕ) : N (m + 1) (7, 7, 7) = N m (0, 7, 7) + N m (1, 7, 7) + N m (2, 7, 7) + N m (3, 7, 7) + N m (4, 7, 7) + N m (5, 7, 7) + N m (6, 7, 7) + N m (7, 7, 7) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (8, 7, 7) (by norm_num)]
  norm_num [okw]

theorem tr_s778 (m : ℕ) : N (m + 1) (7, 7, 8) = N m (1, 7, 7) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (8, 7, 7) (by norm_num)]
  norm_num [okw]

theorem tr_s788 (m : ℕ) : N (m + 1) (7, 8, 8) = N m (0, 7, 8) + N m (1, 7, 8) + N m (2, 7, 8) + N m (3, 7, 8) + N m (4, 7, 8) + N m (5, 7, 8) + N m (6, 7, 8) + N m (7, 7, 8) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero, N_nonmono m (8, 7, 8) (by norm_num)]
  norm_num [okw]

theorem tr_s888 (m : ℕ) : N (m + 1) (8, 8, 8) = N m (0, 8, 8) + N m (1, 8, 8) + N m (2, 8, 8) + N m (3, 8, 8) + N m (4, 8, 8) + N m (5, 8, 8) + N m (6, 8, 8) + N m (7, 8, 8) + N m (8, 8, 8) := by
  rw [trans]
  simp only [sum_range_succ, sum_range_zero]
  norm_num [okw]

theorem v0_s000 : N 0 (0, 0, 0) = 1 := N0_one 0 0 0 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s001 : N 0 (0, 0, 1) = 0 := N0_zero 0 0 1 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s002 : N 0 (0, 0, 2) = 0 := N0_zero 0 0 2 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s003 : N 0 (0, 0, 3) = 0 := N0_zero 0 0 3 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s004 : N 0 (0, 0, 4) = 0 := N0_zero 0 0 4 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s005 : N 0 (0, 0, 5) = 0 := N0_zero 0 0 5 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s006 : N 0 (0, 0, 6) = 0 := N0_zero 0 0 6 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s007 : N 0 (0, 0, 7) = 0 := N0_zero 0 0 7 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s008 : N 0 (0, 0, 8) = 0 := N0_zero 0 0 8 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s011 : N 0 (0, 1, 1) = 1 := N0_one 0 1 1 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s012 : N 0 (0, 1, 2) = 0 := N0_zero 0 1 2 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s013 : N 0 (0, 1, 3) = 0 := N0_zero 0 1 3 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s014 : N 0 (0, 1, 4) = 0 := N0_zero 0 1 4 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s015 : N 0 (0, 1, 5) = 0 := N0_zero 0 1 5 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s016 : N 0 (0, 1, 6) = 0 := N0_zero 0 1 6 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s017 : N 0 (0, 1, 7) = 0 := N0_zero 0 1 7 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s018 : N 0 (0, 1, 8) = 0 := N0_zero 0 1 8 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s022 : N 0 (0, 2, 2) = 1 := N0_one 0 2 2 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s023 : N 0 (0, 2, 3) = 0 := N0_zero 0 2 3 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s024 : N 0 (0, 2, 4) = 0 := N0_zero 0 2 4 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s025 : N 0 (0, 2, 5) = 0 := N0_zero 0 2 5 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s026 : N 0 (0, 2, 6) = 0 := N0_zero 0 2 6 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s027 : N 0 (0, 2, 7) = 0 := N0_zero 0 2 7 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s028 : N 0 (0, 2, 8) = 0 := N0_zero 0 2 8 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s033 : N 0 (0, 3, 3) = 1 := N0_one 0 3 3 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s034 : N 0 (0, 3, 4) = 0 := N0_zero 0 3 4 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s035 : N 0 (0, 3, 5) = 0 := N0_zero 0 3 5 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s036 : N 0 (0, 3, 6) = 0 := N0_zero 0 3 6 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s037 : N 0 (0, 3, 7) = 0 := N0_zero 0 3 7 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s038 : N 0 (0, 3, 8) = 0 := N0_zero 0 3 8 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s044 : N 0 (0, 4, 4) = 1 := N0_one 0 4 4 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s045 : N 0 (0, 4, 5) = 0 := N0_zero 0 4 5 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s046 : N 0 (0, 4, 6) = 0 := N0_zero 0 4 6 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s047 : N 0 (0, 4, 7) = 0 := N0_zero 0 4 7 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s048 : N 0 (0, 4, 8) = 0 := N0_zero 0 4 8 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s055 : N 0 (0, 5, 5) = 1 := N0_one 0 5 5 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s056 : N 0 (0, 5, 6) = 0 := N0_zero 0 5 6 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s057 : N 0 (0, 5, 7) = 0 := N0_zero 0 5 7 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s058 : N 0 (0, 5, 8) = 0 := N0_zero 0 5 8 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s066 : N 0 (0, 6, 6) = 1 := N0_one 0 6 6 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s067 : N 0 (0, 6, 7) = 0 := N0_zero 0 6 7 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s068 : N 0 (0, 6, 8) = 0 := N0_zero 0 6 8 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s077 : N 0 (0, 7, 7) = 1 := N0_one 0 7 7 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s078 : N 0 (0, 7, 8) = 0 := N0_zero 0 7 8 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s088 : N 0 (0, 8, 8) = 1 := N0_one 0 8 8 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s111 : N 0 (1, 1, 1) = 1 := N0_one 1 1 1 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s112 : N 0 (1, 1, 2) = 1 := N0_one 1 1 2 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s113 : N 0 (1, 1, 3) = 0 := N0_zero 1 1 3 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s114 : N 0 (1, 1, 4) = 0 := N0_zero 1 1 4 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s115 : N 0 (1, 1, 5) = 0 := N0_zero 1 1 5 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s116 : N 0 (1, 1, 6) = 0 := N0_zero 1 1 6 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s117 : N 0 (1, 1, 7) = 0 := N0_zero 1 1 7 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s118 : N 0 (1, 1, 8) = 0 := N0_zero 1 1 8 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s122 : N 0 (1, 2, 2) = 1 := N0_one 1 2 2 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s123 : N 0 (1, 2, 3) = 1 := N0_one 1 2 3 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s124 : N 0 (1, 2, 4) = 0 := N0_zero 1 2 4 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s125 : N 0 (1, 2, 5) = 0 := N0_zero 1 2 5 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s126 : N 0 (1, 2, 6) = 0 := N0_zero 1 2 6 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s127 : N 0 (1, 2, 7) = 0 := N0_zero 1 2 7 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s128 : N 0 (1, 2, 8) = 0 := N0_zero 1 2 8 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s133 : N 0 (1, 3, 3) = 1 := N0_one 1 3 3 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s134 : N 0 (1, 3, 4) = 1 := N0_one 1 3 4 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s135 : N 0 (1, 3, 5) = 0 := N0_zero 1 3 5 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s136 : N 0 (1, 3, 6) = 0 := N0_zero 1 3 6 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s137 : N 0 (1, 3, 7) = 0 := N0_zero 1 3 7 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s138 : N 0 (1, 3, 8) = 0 := N0_zero 1 3 8 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s144 : N 0 (1, 4, 4) = 1 := N0_one 1 4 4 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s145 : N 0 (1, 4, 5) = 1 := N0_one 1 4 5 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s146 : N 0 (1, 4, 6) = 0 := N0_zero 1 4 6 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s147 : N 0 (1, 4, 7) = 0 := N0_zero 1 4 7 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s148 : N 0 (1, 4, 8) = 0 := N0_zero 1 4 8 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s155 : N 0 (1, 5, 5) = 1 := N0_one 1 5 5 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s156 : N 0 (1, 5, 6) = 1 := N0_one 1 5 6 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s157 : N 0 (1, 5, 7) = 0 := N0_zero 1 5 7 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s158 : N 0 (1, 5, 8) = 0 := N0_zero 1 5 8 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s166 : N 0 (1, 6, 6) = 1 := N0_one 1 6 6 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s167 : N 0 (1, 6, 7) = 1 := N0_one 1 6 7 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s168 : N 0 (1, 6, 8) = 0 := N0_zero 1 6 8 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s177 : N 0 (1, 7, 7) = 1 := N0_one 1 7 7 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s178 : N 0 (1, 7, 8) = 1 := N0_one 1 7 8 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s188 : N 0 (1, 8, 8) = 1 := N0_one 1 8 8 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s222 : N 0 (2, 2, 2) = 1 := N0_one 2 2 2 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s223 : N 0 (2, 2, 3) = 0 := N0_zero 2 2 3 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s224 : N 0 (2, 2, 4) = 1 := N0_one 2 2 4 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s225 : N 0 (2, 2, 5) = 0 := N0_zero 2 2 5 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s226 : N 0 (2, 2, 6) = 0 := N0_zero 2 2 6 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s227 : N 0 (2, 2, 7) = 0 := N0_zero 2 2 7 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s228 : N 0 (2, 2, 8) = 0 := N0_zero 2 2 8 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s233 : N 0 (2, 3, 3) = 1 := N0_one 2 3 3 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s234 : N 0 (2, 3, 4) = 0 := N0_zero 2 3 4 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s235 : N 0 (2, 3, 5) = 1 := N0_one 2 3 5 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s236 : N 0 (2, 3, 6) = 0 := N0_zero 2 3 6 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s237 : N 0 (2, 3, 7) = 0 := N0_zero 2 3 7 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s238 : N 0 (2, 3, 8) = 0 := N0_zero 2 3 8 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s244 : N 0 (2, 4, 4) = 1 := N0_one 2 4 4 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s245 : N 0 (2, 4, 5) = 0 := N0_zero 2 4 5 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s246 : N 0 (2, 4, 6) = 1 := N0_one 2 4 6 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s247 : N 0 (2, 4, 7) = 0 := N0_zero 2 4 7 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s248 : N 0 (2, 4, 8) = 0 := N0_zero 2 4 8 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s255 : N 0 (2, 5, 5) = 1 := N0_one 2 5 5 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s256 : N 0 (2, 5, 6) = 0 := N0_zero 2 5 6 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s257 : N 0 (2, 5, 7) = 1 := N0_one 2 5 7 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s258 : N 0 (2, 5, 8) = 0 := N0_zero 2 5 8 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s266 : N 0 (2, 6, 6) = 1 := N0_one 2 6 6 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s267 : N 0 (2, 6, 7) = 0 := N0_zero 2 6 7 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s268 : N 0 (2, 6, 8) = 1 := N0_one 2 6 8 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s277 : N 0 (2, 7, 7) = 1 := N0_one 2 7 7 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s278 : N 0 (2, 7, 8) = 0 := N0_zero 2 7 8 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s288 : N 0 (2, 8, 8) = 1 := N0_one 2 8 8 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s333 : N 0 (3, 3, 3) = 1 := N0_one 3 3 3 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s334 : N 0 (3, 3, 4) = 0 := N0_zero 3 3 4 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s335 : N 0 (3, 3, 5) = 0 := N0_zero 3 3 5 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s336 : N 0 (3, 3, 6) = 1 := N0_one 3 3 6 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s337 : N 0 (3, 3, 7) = 0 := N0_zero 3 3 7 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s338 : N 0 (3, 3, 8) = 0 := N0_zero 3 3 8 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s344 : N 0 (3, 4, 4) = 1 := N0_one 3 4 4 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s345 : N 0 (3, 4, 5) = 0 := N0_zero 3 4 5 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s346 : N 0 (3, 4, 6) = 0 := N0_zero 3 4 6 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s347 : N 0 (3, 4, 7) = 1 := N0_one 3 4 7 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s348 : N 0 (3, 4, 8) = 0 := N0_zero 3 4 8 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s355 : N 0 (3, 5, 5) = 1 := N0_one 3 5 5 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s356 : N 0 (3, 5, 6) = 0 := N0_zero 3 5 6 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s357 : N 0 (3, 5, 7) = 0 := N0_zero 3 5 7 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s358 : N 0 (3, 5, 8) = 1 := N0_one 3 5 8 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s366 : N 0 (3, 6, 6) = 1 := N0_one 3 6 6 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s367 : N 0 (3, 6, 7) = 0 := N0_zero 3 6 7 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s368 : N 0 (3, 6, 8) = 0 := N0_zero 3 6 8 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s377 : N 0 (3, 7, 7) = 1 := N0_one 3 7 7 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s378 : N 0 (3, 7, 8) = 0 := N0_zero 3 7 8 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s388 : N 0 (3, 8, 8) = 1 := N0_one 3 8 8 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s444 : N 0 (4, 4, 4) = 1 := N0_one 4 4 4 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s445 : N 0 (4, 4, 5) = 0 := N0_zero 4 4 5 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s446 : N 0 (4, 4, 6) = 0 := N0_zero 4 4 6 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s447 : N 0 (4, 4, 7) = 0 := N0_zero 4 4 7 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s448 : N 0 (4, 4, 8) = 1 := N0_one 4 4 8 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s455 : N 0 (4, 5, 5) = 1 := N0_one 4 5 5 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s456 : N 0 (4, 5, 6) = 0 := N0_zero 4 5 6 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s457 : N 0 (4, 5, 7) = 0 := N0_zero 4 5 7 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s458 : N 0 (4, 5, 8) = 0 := N0_zero 4 5 8 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s466 : N 0 (4, 6, 6) = 1 := N0_one 4 6 6 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s467 : N 0 (4, 6, 7) = 0 := N0_zero 4 6 7 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s468 : N 0 (4, 6, 8) = 0 := N0_zero 4 6 8 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s477 : N 0 (4, 7, 7) = 1 := N0_one 4 7 7 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s478 : N 0 (4, 7, 8) = 0 := N0_zero 4 7 8 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s488 : N 0 (4, 8, 8) = 1 := N0_one 4 8 8 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s555 : N 0 (5, 5, 5) = 1 := N0_one 5 5 5 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s556 : N 0 (5, 5, 6) = 0 := N0_zero 5 5 6 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s557 : N 0 (5, 5, 7) = 0 := N0_zero 5 5 7 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s558 : N 0 (5, 5, 8) = 0 := N0_zero 5 5 8 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s566 : N 0 (5, 6, 6) = 1 := N0_one 5 6 6 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s567 : N 0 (5, 6, 7) = 0 := N0_zero 5 6 7 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s568 : N 0 (5, 6, 8) = 0 := N0_zero 5 6 8 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s577 : N 0 (5, 7, 7) = 1 := N0_one 5 7 7 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s578 : N 0 (5, 7, 8) = 0 := N0_zero 5 7 8 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s588 : N 0 (5, 8, 8) = 1 := N0_one 5 8 8 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s666 : N 0 (6, 6, 6) = 1 := N0_one 6 6 6 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s667 : N 0 (6, 6, 7) = 0 := N0_zero 6 6 7 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s668 : N 0 (6, 6, 8) = 0 := N0_zero 6 6 8 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s677 : N 0 (6, 7, 7) = 1 := N0_one 6 7 7 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s678 : N 0 (6, 7, 8) = 0 := N0_zero 6 7 8 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s688 : N 0 (6, 8, 8) = 1 := N0_one 6 8 8 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s777 : N 0 (7, 7, 7) = 1 := N0_one 7 7 7 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s778 : N 0 (7, 7, 8) = 0 := N0_zero 7 7 8 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s788 : N 0 (7, 8, 8) = 1 := N0_one 7 8 8 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v0_s888 : N 0 (8, 8, 8) = 1 := N0_one 8 8 8 (by norm_num) (by norm_num) (by norm_num) (by decide)

theorem v1_s000 : N 1 (0, 0, 0) = 1 := by
  rw [tr_s000, v0_s000]

theorem v1_s001 : N 1 (0, 0, 1) = 0 := by
  rw [tr_s001]

theorem v1_s002 : N 1 (0, 0, 2) = 0 := by
  rw [tr_s002]

theorem v1_s003 : N 1 (0, 0, 3) = 0 := by
  rw [tr_s003]

theorem v1_s004 : N 1 (0, 0, 4) = 0 := by
  rw [tr_s004]

theorem v1_s005 : N 1 (0, 0, 5) = 0 := by
  rw [tr_s005]

theorem v1_s006 : N 1 (0, 0, 6) = 0 := by
  rw [tr_s006]

theorem v1_s007 : N 1 (0, 0, 7) = 0 := by
  rw [tr_s007]

theorem v1_s008 : N 1 (0, 0, 8) = 0 := by
  rw [tr_s008]

theorem v1_s011 : N 1 (0, 1, 1) = 0 := by
  rw [tr_s011, v0_s001]

theorem v1_s012 : N 1 (0, 1, 2) = 0 := by
  rw [tr_s012]

theorem v1_s013 : N 1 (0, 1, 3) = 0 := by
  rw [tr_s013]

theorem v1_s014 : N 1 (0, 1, 4) = 0 := by
  rw [tr_s014]

theorem v1_s015 : N 1 (0, 1, 5) = 0 := by
  rw [tr_s015]

theorem v1_s016 : N 1 (0, 1, 6) = 0 := by
  rw [tr_s016]

theorem v1_s017 : N 1 (0, 1, 7) = 0 := by
  rw [tr_s017]

theorem v1_s018 : N 1 (0, 1, 8) = 0 := by
  rw [tr_s018]

theorem v1_s022 : N 1 (0, 2, 2) = 0 := by
  rw [tr_s022, v0_s002]

theorem v1_s023 : N 1 (0, 2, 3) = 0 := by
  rw [tr_s023]

theorem v1_s024 : N 1 (0, 2, 4) = 0 := by
  rw [tr_s024]

theorem v1_s025 : N 1 (0, 2, 5) = 0 := by
  rw [tr_s025]

theorem v1_s026 : N 1 (0, 2, 6) = 0 := by
  rw [tr_s026]

theorem v1_s027 : N 1 (0, 2, 7) = 0 := by
  rw [tr_s027]

theorem v1_s028 : N 1 (0, 2, 8) = 0 := by
  rw [tr_s028]

theorem v1_s033 : N 1 (0, 3, 3) = 0 := by
  rw [tr_s033, v0_s003]

theorem v1_s034 : N 1 (0, 3, 4) = 0 := by
  rw [tr_s034]

theorem v1_s035 : N 1 (0, 3, 5) = 0 := by
  rw [tr_s035]

theorem v1_s036 : N 1 (0, 3, 6) = 0 := by
  rw [tr_s036]

theorem v1_s037 : N 1 (0, 3, 7) = 0 := by
  rw [tr_s037]

theorem v1_s038 : N 1 (0, 3, 8) = 0 := by
  rw [tr_s038]

theorem v1_s044 : N 1 (0, 4, 4) = 0 := by
  rw [tr_s044, v0_s004]

theorem v1_s045 : N 1 (0, 4, 5) = 0 := by
  rw [tr_s045]

theorem v1_s046 : N 1 (0, 4, 6) = 0 := by
  rw [tr_s046]

theorem v1_s047 : N 1 (0, 4, 7) = 0 := by
  rw [tr_s047]

theorem v1_s048 : N 1 (0, 4, 8) = 0 := by
  rw [tr_s048]

theorem v1_s055 : N 1 (0, 5, 5) = 0 := by
  rw [tr_s055, v0_s005]

theorem v1_s056 : N 1 (0, 5, 6) = 0 := by
  rw [tr_s056]

theorem v1_s057 : N 1 (0, 5, 7) = 0 := by
  rw [tr_s057]

theorem v1_s058 : N 1 (0, 5, 8) = 0 := by
  rw [tr_s058]

theorem v1_s066 : N 1 (0, 6, 6) = 0 := by
  rw [tr_s066, v0_s006]

theorem v1_s067 : N 1 (0, 6, 7) = 0 := by
  rw [tr_s067]

theorem v1_s068 : N 1 (0, 6, 8) = 0 := by
  rw [tr_s068]

theorem v1_s077 : N 1 (0, 7, 7) = 0 := by
  rw [tr_s077, v0_s007]

theorem v1_s078 : N 1 (0, 7, 8) = 0 := by
  rw [tr_s078]

theorem v1_s088 : N 1 (0, 8, 8) = 0 := by
  rw [tr_s088, v0_s008]

theorem v1_s111 : N 1 (1, 1, 1) = 2 := by
  rw [tr_s111, v0_s011, v0_s111]

theorem v1_s112 : N 1 (1, 1, 2) = 2 := by
  rw [tr_s112, v0_s011, v0_s111]

theorem v1_s113 : N 1 (1, 1, 3) = 0 := by
  rw [tr_s113]

theorem v1_s114 : N 1 (1, 1, 4) = 0 := by
  rw [tr_s114]

theorem v1_s115 : N 1 (1, 1, 5) = 0 := by
  rw [tr_s115]

theorem v1_s116 : N 1 (1, 1, 6) = 0 := by
  rw [tr_s116]

theorem v1_s117 : N 1 (1, 1, 7) = 0 := by
  rw [tr_s117]

theorem v1_s118 : N 1 (1, 1, 8) = 0 := by
  rw [tr_s118]

theorem v1_s122 : N 1 (1, 2, 2) = 1 := by
  rw [tr_s122, v0_s012, v0_s112]

theorem v1_s123 : N 1 (1, 2, 3) = 1 := by
  rw [tr_s123, v0_s012, v0_s112]

theorem v1_s124 : N 1 (1, 2, 4) = 0 := by
  rw [tr_s124]

theorem v1_s125 : N 1 (1, 2, 5) = 0 := by
  rw [tr_s125]

theorem v1_s126 : N 1 (1, 2, 6) = 0 := by
  rw [tr_s126]

theorem v1_s127 : N 1 (1, 2, 7) = 0 := by
  rw [tr_s127]

theorem v1_s128 : N 1 (1, 2, 8) = 0 := by
  rw [tr_s128]

theorem v1_s133 : N 1 (1, 3, 3) = 0 := by
  rw [tr_s133, v0_s013, v0_s113]

theorem v1_s134 : N 1 (1, 3, 4) = 0 := by
  rw [tr_s134, v0_s013, v0_s113]

theorem v1_s135 : N 1 (1, 3, 5) = 0 := by
  rw [tr_s135]

theorem v1_s136 : N 1 (1, 3, 6) = 0 := by
  rw [tr_s136]

theorem v1_s137 : N 1 (1, 3, 7) = 0 := by
  rw [tr_s137]

theorem v1_s138 : N 1 (1, 3, 8) = 0 := by
  rw [tr_s138]

theorem v1_s144 : N 1 (1, 4, 4) = 0 := by
  rw [tr_s144, v0_s014, v0_s114]

theorem v1_s145 : N 1 (1, 4, 5) = 0 := by
  rw [tr_s145, v0_s014, v0_s114]

theorem v1_s146 : N 1 (1, 4, 6) = 0 := by
  rw [tr_s146]

theorem v1_s147 : N 1 (1, 4, 7) = 0 := by
  rw [tr_s147]

theorem v1_s148 : N 1 (1, 4, 8) = 0 := by
  rw [tr_s148]

theorem v1_s155 : N 1 (1, 5, 5) = 0 := by
  rw [tr_s155, v0_s015, v0_s115]

theorem v1_s156 : N 1 (1, 5, 6) = 0 := by
  rw [tr_s156, v0_s015, v0_s115]

theorem v1_s157 : N 1 (1, 5, 7) = 0 := by
  rw [tr_s157]

theorem v1_s158 : N 1 (1, 5, 8) = 0 := by
  rw [tr_s158]

theorem v1_s166 : N 1 (1, 6, 6) = 0 := by
  rw [tr_s166, v0_s016, v0_s116]

theorem v1_s167 : N 1 (1, 6, 7) = 0 := by
  rw [tr_s167, v0_s016, v0_s116]

theorem v1_s168 : N 1 (1, 6, 8) = 0 := by
  rw [tr_s168]

theorem v1_s177 : N 1 (1, 7, 7) = 0 := by
  rw [tr_s177, v0_s017, v0_s117]

theorem v1_s178 : N 1 (1, 7, 8) = 0 := by
  rw [tr_s178, v0_s017, v0_s117]

theorem v1_s188 : N 1 (1, 8, 8) = 0 := by
  rw [tr_s188, v0_s018, v0_s118]

theorem v1_s222 : N 1 (2, 2, 2) = 3 := by
  rw [tr_s222, v0_s022, v0_s122, v0_s222]

theorem v1_s223 : N 1 (2, 2, 3) = 1 := by
  rw [tr_s223, v0_s122]

theorem v1_s224 : N 1 (2, 2, 4) = 3 := by
  rw [tr_s224, v0_s022, v0_s122, v0_s222]

theorem v1_s225 : N 1 (2, 2, 5) = 0 := by
  rw [tr_s225]

theorem v1_s226 : N 1 (2, 2, 6) = 0 := by
  rw [tr_s226]

theorem v1_s227 : N 1 (2, 2, 7) = 0 := by
  rw [tr_s227]

theorem v1_s228 : N 1 (2, 2, 8) = 0 := by
  rw [tr_s228]

theorem v1_s233 : N 1 (2, 3, 3) = 1 := by
  rw [tr_s233, v0_s023, v0_s123, v0_s223]

theorem v1_s234 : N 1 (2, 3, 4) = 1 := by
  rw [tr_s234, v0_s123, v0_s223]

theorem v1_s235 : N 1 (2, 3, 5) = 1 := by
  rw [tr_s235, v0_s023, v0_s123, v0_s223]

theorem v1_s236 : N 1 (2, 3, 6) = 0 := by
  rw [tr_s236]

theorem v1_s237 : N 1 (2, 3, 7) = 0 := by
  rw [tr_s237]

theorem v1_s238 : N 1 (2, 3, 8) = 0 := by
  rw [tr_s238]

theorem v1_s244 : N 1 (2, 4, 4) = 1 := by
  rw [tr_s244, v0_s024, v0_s124, v0_s224]

theorem v1_s245 : N 1 (2, 4, 5) = 0 := by
  rw [tr_s245, v0_s124]

theorem v1_s246 : N 1 (2, 4, 6) = 1 := by
  rw [tr_s246, v0_s024, v0_s124, v0_s224]

theorem v1_s247 : N 1 (2, 4, 7) = 0 := by
  rw [tr_s247]

theorem v1_s248 : N 1 (2, 4, 8) = 0 := by
  rw [tr_s248]

theorem v1_s255 : N 1 (2, 5, 5) = 0 := by
  rw [tr_s255, v0_s025, v0_s125, v0_s225]

theorem v1_s256 : N 1 (2, 5, 6) = 0 := by
  rw [tr_s256, v0_s125]

theorem v1_s257 : N 1 (2, 5, 7) = 0 := by
  rw [tr_s257, v0_s025, v0_s125, v0_s225]

theorem v1_s258 : N 1 (2, 5, 8) = 0 := by
  rw [tr_s258]

theorem v1_s266 : N 1 (2, 6, 6) = 0 := by
  rw [tr_s266, v0_s026, v0_s126, v0_s226]

theorem v1_s267 : N 1 (2, 6, 7) = 0 := by
  rw [tr_s267, v0_s126]

theorem v1_s268 : N 1 (2, 6, 8) = 0 := by
  rw [tr_s268, v0_s026, v0_s126, v0_s226]

theorem v1_s277 : N 1 (2, 7, 7) = 0 := by
  rw [tr_s277, v0_s027, v0_s127, v0_s227]

theorem v1_s278 : N 1 (2, 7, 8) = 0 := by
  rw [tr_s278, v0_s127]

theorem v1_s288 : N 1 (2, 8, 8) = 0 := by
  rw [tr_s288, v0_s028, v0_s128, v0_s228]

theorem v1_s333 : N 1 (3, 3, 3) = 4 := by
  rw [tr_s333, v0_s033, v0_s133, v0_s233, v0_s333]

theorem v1_s334 : N 1 (3, 3, 4) = 1 := by
  rw [tr_s334, v0_s133]

theorem v1_s335 : N 1 (3, 3, 5) = 1 := by
  rw [tr_s335, v0_s233]

theorem v1_s336 : N 1 (3, 3, 6) = 4 := by
  rw [tr_s336, v0_s033, v0_s133, v0_s233, v0_s333]

theorem v1_s337 : N 1 (3, 3, 7) = 0 := by
  rw [tr_s337]

theorem v1_s338 : N 1 (3, 3, 8) = 0 := by
  rw [tr_s338]

theorem v1_s344 : N 1 (3, 4, 4) = 1 := by
  rw [tr_s344, v0_s034, v0_s134, v0_s234, v0_s334]

theorem v1_s345 : N 1 (3, 4, 5) = 1 := by
  rw [tr_s345, v0_s134, v0_s234]

theorem v1_s346 : N 1 (3, 4, 6) = 0 := by
  rw [tr_s346, v0_s234, v0_s334]

theorem v1_s347 : N 1 (3, 4, 7) = 1 := by
  rw [tr_s347, v0_s034, v0_s134, v0_s234, v0_s334]

theorem v1_s348 : N 1 (3, 4, 8) = 0 := by
  rw [tr_s348]

theorem v1_s355 : N 1 (3, 5, 5) = 1 := by
  rw [tr_s355, v0_s035, v0_s135, v0_s235, v0_s335]

theorem v1_s356 : N 1 (3, 5, 6) = 0 := by
  rw [tr_s356, v0_s135, v0_s335]

theorem v1_s357 : N 1 (3, 5, 7) = 1 := by
  rw [tr_s357, v0_s235]

theorem v1_s358 : N 1 (3, 5, 8) = 1 := by
  rw [tr_s358, v0_s035, v0_s135, v0_s235, v0_s335]

theorem v1_s366 : N 1 (3, 6, 6) = 1 := by
  rw [tr_s366, v0_s036, v0_s136, v0_s236, v0_s336]

theorem v1_s367 : N 1 (3, 6, 7) = 0 := by
  rw [tr_s367, v0_s136]

theorem v1_s368 : N 1 (3, 6, 8) = 0 := by
  rw [tr_s368, v0_s236]

theorem v1_s377 : N 1 (3, 7, 7) = 0 := by
  rw [tr_s377, v0_s037, v0_s137, v0_s237, v0_s337]

theorem v1_s378 : N 1 (3, 7, 8) = 0 := by
  rw [tr_s378, v0_s137]

theorem v1_s388 : N 1 (3, 8, 8) = 0 := by
  rw [tr_s388, v0_s038, v0_s138, v0_s238, v0_s338]

theorem v1_s444 : N 1 (4, 4, 4) = 5 := by
  rw [tr_s444, v0_s044, v0_s144, v0_s244, v0_s344, v0_s444]

theorem v1_s445 : N 1 (4, 4, 5) = 1 := by
  rw [tr_s445, v0_s144]

theorem v1_s446 : N 1 (4, 4, 6) = 1 := by
  rw [tr_s446, v0_s244]

theorem v1_s447 : N 1 (4, 4, 7) = 1 := by
  rw [tr_s447, v0_s344]

theorem v1_s448 : N 1 (4, 4, 8) = 5 := by
  rw [tr_s448, v0_s044, v0_s144, v0_s244, v0_s344, v0_s444]

theorem v1_s455 : N 1 (4, 5, 5) = 1 := by
  rw [tr_s455, v0_s045, v0_s145, v0_s245, v0_s345, v0_s445]

theorem v1_s456 : N 1 (4, 5, 6) = 1 := by
  rw [tr_s456, v0_s145, v0_s245]

theorem v1_s457 : N 1 (4, 5, 7) = 0 := by
  rw [tr_s457, v0_s245, v0_s345]

theorem v1_s458 : N 1 (4, 5, 8) = 0 := by
  rw [tr_s458, v0_s345, v0_s445]

theorem v1_s466 : N 1 (4, 6, 6) = 1 := by
  rw [tr_s466, v0_s046, v0_s146, v0_s246, v0_s346, v0_s446]

theorem v1_s467 : N 1 (4, 6, 7) = 0 := by
  rw [tr_s467, v0_s146, v0_s346]

theorem v1_s468 : N 1 (4, 6, 8) = 1 := by
  rw [tr_s468, v0_s246, v0_s446]

theorem v1_s477 : N 1 (4, 7, 7) = 1 := by
  rw [tr_s477, v0_s047, v0_s147, v0_s247, v0_s347, v0_s447]

theorem v1_s478 : N 1 (4, 7, 8) = 0 := by
  rw [tr_s478, v0_s147, v0_s447]

theorem v1_s488 : N 1 (4, 8, 8) = 1 := by
  rw [tr_s488, v0_s048, v0_s148, v0_s248, v0_s348, v0_s448]

theorem v1_s555 : N 1 (5, 5, 5) = 6 := by
  rw [tr_s555, v0_s055, v0_s155, v0_s255, v0_s355, v0_s455, v0_s555]

theorem v1_s556 : N 1 (5, 5, 6) = 1 := by
  rw [tr_s556, v0_s155]

theorem v1_s557 : N 1 (5, 5, 7) = 1 := by
  rw [tr_s557, v0_s255]

theorem v1_s558 : N 1 (5, 5, 8) = 1 := by
  rw [tr_s558, v0_s355]

theorem v1_s566 : N 1 (5, 6, 6) = 1 := by
  rw [tr_s566, v0_s056, v0_s156, v0_s256, v0_s356, v0_s456, v0_s556]

theorem v1_s567 : N 1 (5, 6, 7) = 1 := by
  rw [tr_s567, v0_s156, v0_s256]

theorem v1_s568 : N 1 (5, 6, 8) = 0 := by
  rw [tr_s568, v0_s256, v0_s356]

theorem v1_s577 : N 1 (5, 7, 7) = 1 := by
  rw [tr_s577, v0_s057, v0_s157, v0_s257, v0_s357, v0_s457, v0_s557]

theorem v1_s578 : N 1 (5, 7, 8) = 0 := by
  rw [tr_s578, v0_s157, v0_s357]

theorem v1_s588 : N 1 (5, 8, 8) = 1 := by
  rw [tr_s588, v0_s058, v0_s158, v0_s258, v0_s358, v0_s458, v0_s558]

theorem v1_s666 : N 1 (6, 6, 6) = 7 := by
  rw [tr_s666, v0_s066, v0_s166, v0_s266, v0_s366, v0_s466, v0_s566, v0_s666]

theorem v1_s667 : N 1 (6, 6, 7) = 1 := by
  rw [tr_s667, v0_s166]

theorem v1_s668 : N 1 (6, 6, 8) = 1 := by
  rw [tr_s668, v0_s266]

theorem v1_s677 : N 1 (6, 7, 7) = 1 := by
  rw [tr_s677, v0_s067, v0_s167, v0_s267, v0_s367, v0_s467, v0_s567, v0_s667]

theorem v1_s678 : N 1 (6, 7, 8) = 1 := by
  rw [tr_s678, v0_s167, v0_s267]

theorem v1_s688 : N 1 (6, 8, 8) = 1 := by
  rw [tr_s688, v0_s068, v0_s168, v0_s268, v0_s368, v0_s468, v0_s568, v0_s668]

theorem v1_s777 : N 1 (7, 7, 7) = 8 := by
  rw [tr_s777, v0_s077, v0_s177, v0_s277, v0_s377, v0_s477, v0_s577, v0_s677, v0_s777]

theorem v1_s778 : N 1 (7, 7, 8) = 1 := by
  rw [tr_s778, v0_s177]

theorem v1_s788 : N 1 (7, 8, 8) = 1 := by
  rw [tr_s788, v0_s078, v0_s178, v0_s278, v0_s378, v0_s478, v0_s578, v0_s678, v0_s778]

theorem v1_s888 : N 1 (8, 8, 8) = 9 := by
  rw [tr_s888, v0_s088, v0_s188, v0_s288, v0_s388, v0_s488, v0_s588, v0_s688, v0_s788, v0_s888]

theorem v2_s000 : N 2 (0, 0, 0) = 1 := by
  rw [tr_s000, v1_s000]

theorem v2_s001 : N 2 (0, 0, 1) = 0 := by
  rw [tr_s001]

theorem v2_s002 : N 2 (0, 0, 2) = 0 := by
  rw [tr_s002]

theorem v2_s003 : N 2 (0, 0, 3) = 0 := by
  rw [tr_s003]

theorem v2_s004 : N 2 (0, 0, 4) = 0 := by
  rw [tr_s004]

theorem v2_s005 : N 2 (0, 0, 5) = 0 := by
  rw [tr_s005]

theorem v2_s006 : N 2 (0, 0, 6) = 0 := by
  rw [tr_s006]

theorem v2_s007 : N 2 (0, 0, 7) = 0 := by
  rw [tr_s007]

theorem v2_s008 : N 2 (0, 0, 8) = 0 := by
  rw [tr_s008]

theorem v2_s011 : N 2 (0, 1, 1) = 0 := by
  rw [tr_s011, v1_s001]

theorem v2_s012 : N 2 (0, 1, 2) = 0 := by
  rw [tr_s012]

theorem v2_s013 : N 2 (0, 1, 3) = 0 := by
  rw [tr_s013]

theorem v2_s014 : N 2 (0, 1, 4) = 0 := by
  rw [tr_s014]

theorem v2_s015 : N 2 (0, 1, 5) = 0 := by
  rw [tr_s015]

theorem v2_s016 : N 2 (0, 1, 6) = 0 := by
  rw [tr_s016]

theorem v2_s017 : N 2 (0, 1, 7) = 0 := by
  rw [tr_s017]

theorem v2_s018 : N 2 (0, 1, 8) = 0 := by
  rw [tr_s018]

theorem v2_s022 : N 2 (0, 2, 2) = 0 := by
  rw [tr_s022, v1_s002]

theorem v2_s023 : N 2 (0, 2, 3) = 0 := by
  rw [tr_s023]

theorem v2_s024 : N 2 (0, 2, 4) = 0 := by
  rw [tr_s024]

theorem v2_s025 : N 2 (0, 2, 5) = 0 := by
  rw [tr_s025]

theorem v2_s026 : N 2 (0, 2, 6) = 0 := by
  rw [tr_s026]

theorem v2_s027 : N 2 (0, 2, 7) = 0 := by
  rw [tr_s027]

theorem v2_s028 : N 2 (0, 2, 8) = 0 := by
  rw [tr_s028]

theorem v2_s033 : N 2 (0, 3, 3) = 0 := by
  rw [tr_s033, v1_s003]

theorem v2_s034 : N 2 (0, 3, 4) = 0 := by
  rw [tr_s034]

theorem v2_s035 : N 2 (0, 3, 5) = 0 := by
  rw [tr_s035]

theorem v2_s036 : N 2 (0, 3, 6) = 0 := by
  rw [tr_s036]

theorem v2_s037 : N 2 (0, 3, 7) = 0 := by
  rw [tr_s037]

theorem v2_s038 : N 2 (0, 3, 8) = 0 := by
  rw [tr_s038]

theorem v2_s044 : N 2 (0, 4, 4) = 0 := by
  rw [tr_s044, v1_s004]

theorem v2_s045 : N 2 (0, 4, 5) = 0 := by
  rw [tr_s045]

theorem v2_s046 : N 2 (0, 4, 6) = 0 := by
  rw [tr_s046]

theorem v2_s047 : N 2 (0, 4, 7) = 0 := by
  rw [tr_s047]

theorem v2_s048 : N 2 (0, 4, 8) = 0 := by
  rw [tr_s048]

theorem v2_s055 : N 2 (0, 5, 5) = 0 := by
  rw [tr_s055, v1_s005]

theorem v2_s056 : N 2 (0, 5, 6) = 0 := by
  rw [tr_s056]

theorem v2_s057 : N 2 (0, 5, 7) = 0 := by
  rw [tr_s057]

theorem v2_s058 : N 2 (0, 5, 8) = 0 := by
  rw [tr_s058]

theorem v2_s066 : N 2 (0, 6, 6) = 0 := by
  rw [tr_s066, v1_s006]

theorem v2_s067 : N 2 (0, 6, 7) = 0 := by
  rw [tr_s067]

theorem v2_s068 : N 2 (0, 6, 8) = 0 := by
  rw [tr_s068]

theorem v2_s077 : N 2 (0, 7, 7) = 0 := by
  rw [tr_s077, v1_s007]

theorem v2_s078 : N 2 (0, 7, 8) = 0 := by
  rw [tr_s078]

theorem v2_s088 : N 2 (0, 8, 8) = 0 := by
  rw [tr_s088, v1_s008]

theorem v2_s111 : N 2 (1, 1, 1) = 2 := by
  rw [tr_s111, v1_s011, v1_s111]

theorem v2_s112 : N 2 (1, 1, 2) = 2 := by
  rw [tr_s112, v1_s011, v1_s111]

theorem v2_s113 : N 2 (1, 1, 3) = 0 := by
  rw [tr_s113]

theorem v2_s114 : N 2 (1, 1, 4) = 0 := by
  rw [tr_s114]

theorem v2_s115 : N 2 (1, 1, 5) = 0 := by
  rw [tr_s115]

theorem v2_s116 : N 2 (1, 1, 6) = 0 := by
  rw [tr_s116]

theorem v2_s117 : N 2 (1, 1, 7) = 0 := by
  rw [tr_s117]

theorem v2_s118 : N 2 (1, 1, 8) = 0 := by
  rw [tr_s118]

theorem v2_s122 : N 2 (1, 2, 2) = 2 := by
  rw [tr_s122, v1_s012, v1_s112]

theorem v2_s123 : N 2 (1, 2, 3) = 2 := by
  rw [tr_s123, v1_s012, v1_s112]

theorem v2_s124 : N 2 (1, 2, 4) = 0 := by
  rw [tr_s124]

theorem v2_s125 : N 2 (1, 2, 5) = 0 := by
  rw [tr_s125]

theorem v2_s126 : N 2 (1, 2, 6) = 0 := by
  rw [tr_s126]

theorem v2_s127 : N 2 (1, 2, 7) = 0 := by
  rw [tr_s127]

theorem v2_s128 : N 2 (1, 2, 8) = 0 := by
  rw [tr_s128]

theorem v2_s133 : N 2 (1, 3, 3) = 0 := by
  rw [tr_s133, v1_s013, v1_s113]

theorem v2_s134 : N 2 (1, 3, 4) = 0 := by
  rw [tr_s134, v1_s013, v1_s113]

theorem v2_s135 : N 2 (1, 3, 5) = 0 := by
  rw [tr_s135]

theorem v2_s136 : N 2 (1, 3, 6) = 0 := by
  rw [tr_s136]

theorem v2_s137 : N 2 (1, 3, 7) = 0 := by
  rw [tr_s137]

theorem v2_s138 : N 2 (1, 3, 8) = 0 := by
  rw [tr_s138]

theorem v2_s144 : N 2 (1, 4, 4) = 0 := by
  rw [tr_s144, v1_s014, v1_s114]

theorem v2_s145 : N 2 (1, 4, 5) = 0 := by
  rw [tr_s145, v1_s014, v1_s114]

theorem v2_s146 : N 2 (1, 4, 6) = 0 := by
  rw [tr_s146]

theorem v2_s147 : N 2 (1, 4, 7) = 0 := by
  rw [tr_s147]

theorem v2_s148 : N 2 (1, 4, 8) = 0 := by
  rw [tr_s148]

theorem v2_s155 : N 2 (1, 5, 5) = 0 := by
  rw [tr_s155, v1_s015, v1_s115]

theorem v2_s156 : N 2 (1, 5, 6) = 0 := by
  rw [tr_s156, v1_s015, v1_s115]

theorem v2_s157 : N 2 (1, 5, 7) = 0 := by
  rw [tr_s157]

theorem v2_s158 : N 2 (1, 5, 8) = 0 := by
  rw [tr_s158]

theorem v2_s166 : N 2 (1, 6, 6) = 0 := by
  rw [tr_s166, v1_s016, v1_s116]

theorem v2_s167 : N 2 (1, 6, 7) = 0 := by
  rw [tr_s167, v1_s016, v1_s116]

theorem v2_s168 : N 2 (1, 6, 8) = 0 := by
  rw [tr_s168]

theorem v2_s177 : N 2 (1, 7, 7) = 0 := by
  rw [tr_s177, v1_s017, v1_s117]

theorem v2_s178 : N 2 (1, 7, 8) = 0 := by
  rw [tr_s178, v1_s017, v1_s117]

theorem v2_s188 : N 2 (1, 8, 8) = 0 := by
  rw [tr_s188, v1_s018, v1_s118]

theorem v2_s222 : N 2 (2, 2, 2) = 4 := by
  rw [tr_s222, v1_s022, v1_s122, v1_s222]

theorem v2_s223 : N 2 (2, 2, 3) = 1 := by
  rw [tr_s223, v1_s122]

theorem v2_s224 : N 2 (2, 2, 4) = 4 := by
  rw [tr_s224, v1_s022, v1_s122, v1_s222]

theorem v2_s225 : N 2 (2, 2, 5) = 0 := by
  rw [tr_s225]

theorem v2_s226 : N 2 (2, 2, 6) = 0 := by
  rw [tr_s226]

theorem v2_s227 : N 2 (2, 2, 7) = 0 := by
  rw [tr_s227]

theorem v2_s228 : N 2 (2, 2, 8) = 0 := by
  rw [tr_s228]

theorem v2_s233 : N 2 (2, 3, 3) = 2 := by
  rw [tr_s233, v1_s023, v1_s123, v1_s223]

theorem v2_s234 : N 2 (2, 3, 4) = 2 := by
  rw [tr_s234, v1_s123, v1_s223]

theorem v2_s235 : N 2 (2, 3, 5) = 2 := by
  rw [tr_s235, v1_s023, v1_s123, v1_s223]

theorem v2_s236 : N 2 (2, 3, 6) = 0 := by
  rw [tr_s236]

theorem v2_s237 : N 2 (2, 3, 7) = 0 := by
  rw [tr_s237]

theorem v2_s238 : N 2 (2, 3, 8) = 0 := by
  rw [tr_s238]

theorem v2_s244 : N 2 (2, 4, 4) = 3 := by
  rw [tr_s244, v1_s024, v1_s124, v1_s224]

theorem v2_s245 : N 2 (2, 4, 5) = 0 := by
  rw [tr_s245, v1_s124]

theorem v2_s246 : N 2 (2, 4, 6) = 3 := by
  rw [tr_s246, v1_s024, v1_s124, v1_s224]

theorem v2_s247 : N 2 (2, 4, 7) = 0 := by
  rw [tr_s247]

theorem v2_s248 : N 2 (2, 4, 8) = 0 := by
  rw [tr_s248]

theorem v2_s255 : N 2 (2, 5, 5) = 0 := by
  rw [tr_s255, v1_s025, v1_s125, v1_s225]

theorem v2_s256 : N 2 (2, 5, 6) = 0 := by
  rw [tr_s256, v1_s125]

theorem v2_s257 : N 2 (2, 5, 7) = 0 := by
  rw [tr_s257, v1_s025, v1_s125, v1_s225]

theorem v2_s258 : N 2 (2, 5, 8) = 0 := by
  rw [tr_s258]

theorem v2_s266 : N 2 (2, 6, 6) = 0 := by
  rw [tr_s266, v1_s026, v1_s126, v1_s226]

theorem v2_s267 : N 2 (2, 6, 7) = 0 := by
  rw [tr_s267, v1_s126]

theorem v2_s268 : N 2 (2, 6, 8) = 0 := by
  rw [tr_s268, v1_s026, v1_s126, v1_s226]

theorem v2_s277 : N 2 (2, 7, 7) = 0 := by
  rw [tr_s277, v1_s027, v1_s127, v1_s227]

theorem v2_s278 : N 2 (2, 7, 8) = 0 := by
  rw [tr_s278, v1_s127]

theorem v2_s288 : N 2 (2, 8, 8) = 0 := by
  rw [tr_s288, v1_s028, v1_s128, v1_s228]

theorem v2_s333 : N 2 (3, 3, 3) = 5 := by
  rw [tr_s333, v1_s033, v1_s133, v1_s233, v1_s333]

theorem v2_s334 : N 2 (3, 3, 4) = 0 := by
  rw [tr_s334, v1_s133]

theorem v2_s335 : N 2 (3, 3, 5) = 1 := by
  rw [tr_s335, v1_s233]

theorem v2_s336 : N 2 (3, 3, 6) = 5 := by
  rw [tr_s336, v1_s033, v1_s133, v1_s233, v1_s333]

theorem v2_s337 : N 2 (3, 3, 7) = 0 := by
  rw [tr_s337]

theorem v2_s338 : N 2 (3, 3, 8) = 0 := by
  rw [tr_s338]

theorem v2_s344 : N 2 (3, 4, 4) = 2 := by
  rw [tr_s344, v1_s034, v1_s134, v1_s234, v1_s334]

theorem v2_s345 : N 2 (3, 4, 5) = 1 := by
  rw [tr_s345, v1_s134, v1_s234]

theorem v2_s346 : N 2 (3, 4, 6) = 2 := by
  rw [tr_s346, v1_s234, v1_s334]

theorem v2_s347 : N 2 (3, 4, 7) = 2 := by
  rw [tr_s347, v1_s034, v1_s134, v1_s234, v1_s334]

theorem v2_s348 : N 2 (3, 4, 8) = 0 := by
  rw [tr_s348]

theorem v2_s355 : N 2 (3, 5, 5) = 2 := by
  rw [tr_s355, v1_s035, v1_s135, v1_s235, v1_s335]

theorem v2_s356 : N 2 (3, 5, 6) = 1 := by
  rw [tr_s356, v1_s135, v1_s335]

theorem v2_s357 : N 2 (3, 5, 7) = 1 := by
  rw [tr_s357, v1_s235]

theorem v2_s358 : N 2 (3, 5, 8) = 2 := by
  rw [tr_s358, v1_s035, v1_s135, v1_s235, v1_s335]

theorem v2_s366 : N 2 (3, 6, 6) = 4 := by
  rw [tr_s366, v1_s036, v1_s136, v1_s236, v1_s336]

theorem v2_s367 : N 2 (3, 6, 7) = 0 := by
  rw [tr_s367, v1_s136]

theorem v2_s368 : N 2 (3, 6, 8) = 0 := by
  rw [tr_s368, v1_s236]

theorem v2_s377 : N 2 (3, 7, 7) = 0 := by
  rw [tr_s377, v1_s037, v1_s137, v1_s237, v1_s337]

theorem v2_s378 : N 2 (3, 7, 8) = 0 := by
  rw [tr_s378, v1_s137]

theorem v2_s388 : N 2 (3, 8, 8) = 0 := by
  rw [tr_s388, v1_s038, v1_s138, v1_s238, v1_s338]

theorem v2_s444 : N 2 (4, 4, 4) = 7 := by
  rw [tr_s444, v1_s044, v1_s144, v1_s244, v1_s344, v1_s444]

theorem v2_s445 : N 2 (4, 4, 5) = 0 := by
  rw [tr_s445, v1_s144]

theorem v2_s446 : N 2 (4, 4, 6) = 1 := by
  rw [tr_s446, v1_s244]

theorem v2_s447 : N 2 (4, 4, 7) = 1 := by
  rw [tr_s447, v1_s344]

theorem v2_s448 : N 2 (4, 4, 8) = 7 := by
  rw [tr_s448, v1_s044, v1_s144, v1_s244, v1_s344, v1_s444]

theorem v2_s455 : N 2 (4, 5, 5) = 2 := by
  rw [tr_s455, v1_s045, v1_s145, v1_s245, v1_s345, v1_s445]

theorem v2_s456 : N 2 (4, 5, 6) = 0 := by
  rw [tr_s456, v1_s145, v1_s245]

theorem v2_s457 : N 2 (4, 5, 7) = 1 := by
  rw [tr_s457, v1_s245, v1_s345]

theorem v2_s458 : N 2 (4, 5, 8) = 2 := by
  rw [tr_s458, v1_s345, v1_s445]

theorem v2_s466 : N 2 (4, 6, 6) = 2 := by
  rw [tr_s466, v1_s046, v1_s146, v1_s246, v1_s346, v1_s446]

theorem v2_s467 : N 2 (4, 6, 7) = 0 := by
  rw [tr_s467, v1_s146, v1_s346]

theorem v2_s468 : N 2 (4, 6, 8) = 2 := by
  rw [tr_s468, v1_s246, v1_s446]

theorem v2_s477 : N 2 (4, 7, 7) = 2 := by
  rw [tr_s477, v1_s047, v1_s147, v1_s247, v1_s347, v1_s447]

theorem v2_s478 : N 2 (4, 7, 8) = 1 := by
  rw [tr_s478, v1_s147, v1_s447]

theorem v2_s488 : N 2 (4, 8, 8) = 5 := by
  rw [tr_s488, v1_s048, v1_s148, v1_s248, v1_s348, v1_s448]

theorem v2_s555 : N 2 (5, 5, 5) = 8 := by
  rw [tr_s555, v1_s055, v1_s155, v1_s255, v1_s355, v1_s455, v1_s555]

theorem v2_s556 : N 2 (5, 5, 6) = 0 := by
  rw [tr_s556, v1_s155]

theorem v2_s557 : N 2 (5, 5, 7) = 0 := by
  rw [tr_s557, v1_s255]

theorem v2_s558 : N 2 (5, 5, 8) = 1 := by
  rw [tr_s558, v1_s355]

theorem v2_s566 : N 2 (5, 6, 6) = 2 := by
  rw [tr_s566, v1_s056, v1_s156, v1_s256, v1_s356, v1_s456, v1_s556]

theorem v2_s567 : N 2 (5, 6, 7) = 0 := by
  rw [tr_s567, v1_s156, v1_s256]

theorem v2_s568 : N 2 (5, 6, 8) = 0 := by
  rw [tr_s568, v1_s256, v1_s356]

theorem v2_s577 : N 2 (5, 7, 7) = 2 := by
  rw [tr_s577, v1_s057, v1_s157, v1_s257, v1_s357, v1_s457, v1_s557]

theorem v2_s578 : N 2 (5, 7, 8) = 1 := by
  rw [tr_s578, v1_s157, v1_s357]

theorem v2_s588 : N 2 (5, 8, 8) = 2 := by
  rw [tr_s588, v1_s058, v1_s158, v1_s258, v1_s358, v1_s458, v1_s558]

theorem v2_s666 : N 2 (6, 6, 6) = 10 := by
  rw [tr_s666, v1_s066, v1_s166, v1_s266, v1_s366, v1_s466, v1_s566, v1_s666]

theorem v2_s667 : N 2 (6, 6, 7) = 0 := by
  rw [tr_s667, v1_s166]

theorem v2_s668 : N 2 (6, 6, 8) = 0 := by
  rw [tr_s668, v1_s266]

theorem v2_s677 : N 2 (6, 7, 7) = 2 := by
  rw [tr_s677, v1_s067, v1_s167, v1_s267, v1_s367, v1_s467, v1_s567, v1_s667]

theorem v2_s678 : N 2 (6, 7, 8) = 0 := by
  rw [tr_s678, v1_s167, v1_s267]

theorem v2_s688 : N 2 (6, 8, 8) = 2 := by
  rw [tr_s688, v1_s068, v1_s168, v1_s268, v1_s368, v1_s468, v1_s568, v1_s668]

theorem v2_s777 : N 2 (7, 7, 7) = 11 := by
  rw [tr_s777, v1_s077, v1_s177, v1_s277, v1_s377, v1_s477, v1_s577, v1_s677, v1_s777]

theorem v2_s778 : N 2 (7, 7, 8) = 0 := by
  rw [tr_s778, v1_s177]

theorem v2_s788 : N 2 (7, 8, 8) = 2 := by
  rw [tr_s788, v1_s078, v1_s178, v1_s278, v1_s378, v1_s478, v1_s578, v1_s678, v1_s778]

theorem v2_s888 : N 2 (8, 8, 8) = 13 := by
  rw [tr_s888, v1_s088, v1_s188, v1_s288, v1_s388, v1_s488, v1_s588, v1_s688, v1_s788, v1_s888]

theorem v3_s000 : N 3 (0, 0, 0) = 1 := by
  rw [tr_s000, v2_s000]

theorem v3_s001 : N 3 (0, 0, 1) = 0 := by
  rw [tr_s001]

theorem v3_s002 : N 3 (0, 0, 2) = 0 := by
  rw [tr_s002]

theorem v3_s003 : N 3 (0, 0, 3) = 0 := by
  rw [tr_s003]

theorem v3_s004 : N 3 (0, 0, 4) = 0 := by
  rw [tr_s004]

theorem v3_s005 : N 3 (0, 0, 5) = 0 := by
  rw [tr_s005]

theorem v3_s006 : N 3 (0, 0, 6) = 0 := by
  rw [tr_s006]

theorem v3_s007 : N 3 (0, 0, 7) = 0 := by
  rw [tr_s007]

theorem v3_s008 : N 3 (0, 0, 8) = 0 := by
  rw [tr_s008]

theorem v3_s011 : N 3 (0, 1, 1) = 0 := by
  rw [tr_s011, v2_s001]

theorem v3_s012 : N 3 (0, 1, 2) = 0 := by
  rw [tr_s012]

theorem v3_s013 : N 3 (0, 1, 3) = 0 := by
  rw [tr_s013]

theorem v3_s014 : N 3 (0, 1, 4) = 0 := by
  rw [tr_s014]

theorem v3_s015 : N 3 (0, 1, 5) = 0 := by
  rw [tr_s015]

theorem v3_s016 : N 3 (0, 1, 6) = 0 := by
  rw [tr_s016]

theorem v3_s017 : N 3 (0, 1, 7) = 0 := by
  rw [tr_s017]

theorem v3_s018 : N 3 (0, 1, 8) = 0 := by
  rw [tr_s018]

theorem v3_s022 : N 3 (0, 2, 2) = 0 := by
  rw [tr_s022, v2_s002]

theorem v3_s023 : N 3 (0, 2, 3) = 0 := by
  rw [tr_s023]

theorem v3_s024 : N 3 (0, 2, 4) = 0 := by
  rw [tr_s024]

theorem v3_s025 : N 3 (0, 2, 5) = 0 := by
  rw [tr_s025]

theorem v3_s026 : N 3 (0, 2, 6) = 0 := by
  rw [tr_s026]

theorem v3_s027 : N 3 (0, 2, 7) = 0 := by
  rw [tr_s027]

theorem v3_s028 : N 3 (0, 2, 8) = 0 := by
  rw [tr_s028]

theorem v3_s033 : N 3 (0, 3, 3) = 0 := by
  rw [tr_s033, v2_s003]

theorem v3_s034 : N 3 (0, 3, 4) = 0 := by
  rw [tr_s034]

theorem v3_s035 : N 3 (0, 3, 5) = 0 := by
  rw [tr_s035]

theorem v3_s036 : N 3 (0, 3, 6) = 0 := by
  rw [tr_s036]

theorem v3_s037 : N 3 (0, 3, 7) = 0 := by
  rw [tr_s037]

theorem v3_s038 : N 3 (0, 3, 8) = 0 := by
  rw [tr_s038]

theorem v3_s044 : N 3 (0, 4, 4) = 0 := by
  rw [tr_s044, v2_s004]

theorem v3_s045 : N 3 (0, 4, 5) = 0 := by
  rw [tr_s045]

theorem v3_s046 : N 3 (0, 4, 6) = 0 := by
  rw [tr_s046]

theorem v3_s047 : N 3 (0, 4, 7) = 0 := by
  rw [tr_s047]

theorem v3_s048 : N 3 (0, 4, 8) = 0 := by
  rw [tr_s048]

theorem v3_s055 : N 3 (0, 5, 5) = 0 := by
  rw [tr_s055, v2_s005]

theorem v3_s056 : N 3 (0, 5, 6) = 0 := by
  rw [tr_s056]

theorem v3_s057 : N 3 (0, 5, 7) = 0 := by
  rw [tr_s057]

theorem v3_s058 : N 3 (0, 5, 8) = 0 := by
  rw [tr_s058]

theorem v3_s066 : N 3 (0, 6, 6) = 0 := by
  rw [tr_s066, v2_s006]

theorem v3_s067 : N 3 (0, 6, 7) = 0 := by
  rw [tr_s067]

theorem v3_s068 : N 3 (0, 6, 8) = 0 := by
  rw [tr_s068]

theorem v3_s077 : N 3 (0, 7, 7) = 0 := by
  rw [tr_s077, v2_s007]

theorem v3_s078 : N 3 (0, 7, 8) = 0 := by
  rw [tr_s078]

theorem v3_s088 : N 3 (0, 8, 8) = 0 := by
  rw [tr_s088, v2_s008]

theorem v3_s111 : N 3 (1, 1, 1) = 2 := by
  rw [tr_s111, v2_s011, v2_s111]

theorem v3_s112 : N 3 (1, 1, 2) = 2 := by
  rw [tr_s112, v2_s011, v2_s111]

theorem v3_s113 : N 3 (1, 1, 3) = 0 := by
  rw [tr_s113]

theorem v3_s114 : N 3 (1, 1, 4) = 0 := by
  rw [tr_s114]

theorem v3_s115 : N 3 (1, 1, 5) = 0 := by
  rw [tr_s115]

theorem v3_s116 : N 3 (1, 1, 6) = 0 := by
  rw [tr_s116]

theorem v3_s117 : N 3 (1, 1, 7) = 0 := by
  rw [tr_s117]

theorem v3_s118 : N 3 (1, 1, 8) = 0 := by
  rw [tr_s118]

theorem v3_s122 : N 3 (1, 2, 2) = 2 := by
  rw [tr_s122, v2_s012, v2_s112]

theorem v3_s123 : N 3 (1, 2, 3) = 2 := by
  rw [tr_s123, v2_s012, v2_s112]

theorem v3_s124 : N 3 (1, 2, 4) = 0 := by
  rw [tr_s124]

theorem v3_s125 : N 3 (1, 2, 5) = 0 := by
  rw [tr_s125]

theorem v3_s126 : N 3 (1, 2, 6) = 0 := by
  rw [tr_s126]

theorem v3_s127 : N 3 (1, 2, 7) = 0 := by
  rw [tr_s127]

theorem v3_s128 : N 3 (1, 2, 8) = 0 := by
  rw [tr_s128]

theorem v3_s133 : N 3 (1, 3, 3) = 0 := by
  rw [tr_s133, v2_s013, v2_s113]

theorem v3_s134 : N 3 (1, 3, 4) = 0 := by
  rw [tr_s134, v2_s013, v2_s113]

theorem v3_s135 : N 3 (1, 3, 5) = 0 := by
  rw [tr_s135]

theorem v3_s136 : N 3 (1, 3, 6) = 0 := by
  rw [tr_s136]

theorem v3_s137 : N 3 (1, 3, 7) = 0 := by
  rw [tr_s137]

theorem v3_s138 : N 3 (1, 3, 8) = 0 := by
  rw [tr_s138]

theorem v3_s144 : N 3 (1, 4, 4) = 0 := by
  rw [tr_s144, v2_s014, v2_s114]

theorem v3_s145 : N 3 (1, 4, 5) = 0 := by
  rw [tr_s145, v2_s014, v2_s114]

theorem v3_s146 : N 3 (1, 4, 6) = 0 := by
  rw [tr_s146]

theorem v3_s147 : N 3 (1, 4, 7) = 0 := by
  rw [tr_s147]

theorem v3_s148 : N 3 (1, 4, 8) = 0 := by
  rw [tr_s148]

theorem v3_s155 : N 3 (1, 5, 5) = 0 := by
  rw [tr_s155, v2_s015, v2_s115]

theorem v3_s156 : N 3 (1, 5, 6) = 0 := by
  rw [tr_s156, v2_s015, v2_s115]

theorem v3_s157 : N 3 (1, 5, 7) = 0 := by
  rw [tr_s157]

theorem v3_s158 : N 3 (1, 5, 8) = 0 := by
  rw [tr_s158]

theorem v3_s166 : N 3 (1, 6, 6) = 0 := by
  rw [tr_s166, v2_s016, v2_s116]

theorem v3_s167 : N 3 (1, 6, 7) = 0 := by
  rw [tr_s167, v2_s016, v2_s116]

theorem v3_s168 : N 3 (1, 6, 8) = 0 := by
  rw [tr_s168]

theorem v3_s177 : N 3 (1, 7, 7) = 0 := by
  rw [tr_s177, v2_s017, v2_s117]

theorem v3_s178 : N 3 (1, 7, 8) = 0 := by
  rw [tr_s178, v2_s017, v2_s117]

theorem v3_s188 : N 3 (1, 8, 8) = 0 := by
  rw [tr_s188, v2_s018, v2_s118]

theorem v3_s222 : N 3 (2, 2, 2) = 6 := by
  rw [tr_s222, v2_s022, v2_s122, v2_s222]

theorem v3_s223 : N 3 (2, 2, 3) = 2 := by
  rw [tr_s223, v2_s122]

theorem v3_s224 : N 3 (2, 2, 4) = 6 := by
  rw [tr_s224, v2_s022, v2_s122, v2_s222]

theorem v3_s225 : N 3 (2, 2, 5) = 0 := by
  rw [tr_s225]

theorem v3_s226 : N 3 (2, 2, 6) = 0 := by
  rw [tr_s226]

theorem v3_s227 : N 3 (2, 2, 7) = 0 := by
  rw [tr_s227]

theorem v3_s228 : N 3 (2, 2, 8) = 0 := by
  rw [tr_s228]

theorem v3_s233 : N 3 (2, 3, 3) = 3 := by
  rw [tr_s233, v2_s023, v2_s123, v2_s223]

theorem v3_s234 : N 3 (2, 3, 4) = 3 := by
  rw [tr_s234, v2_s123, v2_s223]

theorem v3_s235 : N 3 (2, 3, 5) = 3 := by
  rw [tr_s235, v2_s023, v2_s123, v2_s223]

theorem v3_s236 : N 3 (2, 3, 6) = 0 := by
  rw [tr_s236]

theorem v3_s237 : N 3 (2, 3, 7) = 0 := by
  rw [tr_s237]

theorem v3_s238 : N 3 (2, 3, 8) = 0 := by
  rw [tr_s238]

theorem v3_s244 : N 3 (2, 4, 4) = 4 := by
  rw [tr_s244, v2_s024, v2_s124, v2_s224]

theorem v3_s245 : N 3 (2, 4, 5) = 0 := by
  rw [tr_s245, v2_s124]

theorem v3_s246 : N 3 (2, 4, 6) = 4 := by
  rw [tr_s246, v2_s024, v2_s124, v2_s224]

theorem v3_s247 : N 3 (2, 4, 7) = 0 := by
  rw [tr_s247]

theorem v3_s248 : N 3 (2, 4, 8) = 0 := by
  rw [tr_s248]

theorem v3_s255 : N 3 (2, 5, 5) = 0 := by
  rw [tr_s255, v2_s025, v2_s125, v2_s225]

theorem v3_s256 : N 3 (2, 5, 6) = 0 := by
  rw [tr_s256, v2_s125]

theorem v3_s257 : N 3 (2, 5, 7) = 0 := by
  rw [tr_s257, v2_s025, v2_s125, v2_s225]

theorem v3_s258 : N 3 (2, 5, 8) = 0 := by
  rw [tr_s258]

theorem v3_s266 : N 3 (2, 6, 6) = 0 := by
  rw [tr_s266, v2_s026, v2_s126, v2_s226]

theorem v3_s267 : N 3 (2, 6, 7) = 0 := by
  rw [tr_s267, v2_s126]

theorem v3_s268 : N 3 (2, 6, 8) = 0 := by
  rw [tr_s268, v2_s026, v2_s126, v2_s226]

theorem v3_s277 : N 3 (2, 7, 7) = 0 := by
  rw [tr_s277, v2_s027, v2_s127, v2_s227]

theorem v3_s278 : N 3 (2, 7, 8) = 0 := by
  rw [tr_s278, v2_s127]

theorem v3_s288 : N 3 (2, 8, 8) = 0 := by
  rw [tr_s288, v2_s028, v2_s128, v2_s228]

theorem v3_s333 : N 3 (3, 3, 3) = 7 := by
  rw [tr_s333, v2_s033, v2_s133, v2_s233, v2_s333]

theorem v3_s334 : N 3 (3, 3, 4) = 0 := by
  rw [tr_s334, v2_s133]

theorem v3_s335 : N 3 (3, 3, 5) = 2 := by
  rw [tr_s335, v2_s233]

theorem v3_s336 : N 3 (3, 3, 6) = 7 := by
  rw [tr_s336, v2_s033, v2_s133, v2_s233, v2_s333]

theorem v3_s337 : N 3 (3, 3, 7) = 0 := by
  rw [tr_s337]

theorem v3_s338 : N 3 (3, 3, 8) = 0 := by
  rw [tr_s338]

theorem v3_s344 : N 3 (3, 4, 4) = 2 := by
  rw [tr_s344, v2_s034, v2_s134, v2_s234, v2_s334]

theorem v3_s345 : N 3 (3, 4, 5) = 2 := by
  rw [tr_s345, v2_s134, v2_s234]

theorem v3_s346 : N 3 (3, 4, 6) = 2 := by
  rw [tr_s346, v2_s234, v2_s334]

theorem v3_s347 : N 3 (3, 4, 7) = 2 := by
  rw [tr_s347, v2_s034, v2_s134, v2_s234, v2_s334]

theorem v3_s348 : N 3 (3, 4, 8) = 0 := by
  rw [tr_s348]

theorem v3_s355 : N 3 (3, 5, 5) = 3 := by
  rw [tr_s355, v2_s035, v2_s135, v2_s235, v2_s335]

theorem v3_s356 : N 3 (3, 5, 6) = 1 := by
  rw [tr_s356, v2_s135, v2_s335]

theorem v3_s357 : N 3 (3, 5, 7) = 2 := by
  rw [tr_s357, v2_s235]

theorem v3_s358 : N 3 (3, 5, 8) = 3 := by
  rw [tr_s358, v2_s035, v2_s135, v2_s235, v2_s335]

theorem v3_s366 : N 3 (3, 6, 6) = 5 := by
  rw [tr_s366, v2_s036, v2_s136, v2_s236, v2_s336]

theorem v3_s367 : N 3 (3, 6, 7) = 0 := by
  rw [tr_s367, v2_s136]

theorem v3_s368 : N 3 (3, 6, 8) = 0 := by
  rw [tr_s368, v2_s236]

theorem v3_s377 : N 3 (3, 7, 7) = 0 := by
  rw [tr_s377, v2_s037, v2_s137, v2_s237, v2_s337]

theorem v3_s378 : N 3 (3, 7, 8) = 0 := by
  rw [tr_s378, v2_s137]

theorem v3_s388 : N 3 (3, 8, 8) = 0 := by
  rw [tr_s388, v2_s038, v2_s138, v2_s238, v2_s338]

theorem v3_s444 : N 3 (4, 4, 4) = 12 := by
  rw [tr_s444, v2_s044, v2_s144, v2_s244, v2_s344, v2_s444]

theorem v3_s445 : N 3 (4, 4, 5) = 0 := by
  rw [tr_s445, v2_s144]

theorem v3_s446 : N 3 (4, 4, 6) = 3 := by
  rw [tr_s446, v2_s244]

theorem v3_s447 : N 3 (4, 4, 7) = 2 := by
  rw [tr_s447, v2_s344]

theorem v3_s448 : N 3 (4, 4, 8) = 12 := by
  rw [tr_s448, v2_s044, v2_s144, v2_s244, v2_s344, v2_s444]

theorem v3_s455 : N 3 (4, 5, 5) = 1 := by
  rw [tr_s455, v2_s045, v2_s145, v2_s245, v2_s345, v2_s445]

theorem v3_s456 : N 3 (4, 5, 6) = 0 := by
  rw [tr_s456, v2_s145, v2_s245]

theorem v3_s457 : N 3 (4, 5, 7) = 1 := by
  rw [tr_s457, v2_s245, v2_s345]

theorem v3_s458 : N 3 (4, 5, 8) = 1 := by
  rw [tr_s458, v2_s345, v2_s445]

theorem v3_s466 : N 3 (4, 6, 6) = 6 := by
  rw [tr_s466, v2_s046, v2_s146, v2_s246, v2_s346, v2_s446]

theorem v3_s467 : N 3 (4, 6, 7) = 2 := by
  rw [tr_s467, v2_s146, v2_s346]

theorem v3_s468 : N 3 (4, 6, 8) = 4 := by
  rw [tr_s468, v2_s246, v2_s446]

theorem v3_s477 : N 3 (4, 7, 7) = 3 := by
  rw [tr_s477, v2_s047, v2_s147, v2_s247, v2_s347, v2_s447]

theorem v3_s478 : N 3 (4, 7, 8) = 1 := by
  rw [tr_s478, v2_s147, v2_s447]

theorem v3_s488 : N 3 (4, 8, 8) = 7 := by
  rw [tr_s488, v2_s048, v2_s148, v2_s248, v2_s348, v2_s448]

theorem v3_s555 : N 3 (5, 5, 5) = 12 := by
  rw [tr_s555, v2_s055, v2_s155, v2_s255, v2_s355, v2_s455, v2_s555]

theorem v3_s556 : N 3 (5, 5, 6) = 0 := by
  rw [tr_s556, v2_s155]

theorem v3_s557 : N 3 (5, 5, 7) = 0 := by
  rw [tr_s557, v2_s255]

theorem v3_s558 : N 3 (5, 5, 8) = 2 := by
  rw [tr_s558, v2_s355]

theorem v3_s566 : N 3 (5, 6, 6) = 1 := by
  rw [tr_s566, v2_s056, v2_s156, v2_s256, v2_s356, v2_s456, v2_s556]

theorem v3_s567 : N 3 (5, 6, 7) = 0 := by
  rw [tr_s567, v2_s156, v2_s256]

theorem v3_s568 : N 3 (5, 6, 8) = 1 := by
  rw [tr_s568, v2_s256, v2_s356]

theorem v3_s577 : N 3 (5, 7, 7) = 2 := by
  rw [tr_s577, v2_s057, v2_s157, v2_s257, v2_s357, v2_s457, v2_s557]

theorem v3_s578 : N 3 (5, 7, 8) = 1 := by
  rw [tr_s578, v2_s157, v2_s357]

theorem v3_s588 : N 3 (5, 8, 8) = 5 := by
  rw [tr_s588, v2_s058, v2_s158, v2_s258, v2_s358, v2_s458, v2_s558]

theorem v3_s666 : N 3 (6, 6, 6) = 18 := by
  rw [tr_s666, v2_s066, v2_s166, v2_s266, v2_s366, v2_s466, v2_s566, v2_s666]

theorem v3_s667 : N 3 (6, 6, 7) = 0 := by
  rw [tr_s667, v2_s166]

theorem v3_s668 : N 3 (6, 6, 8) = 0 := by
  rw [tr_s668, v2_s266]

theorem v3_s677 : N 3 (6, 7, 7) = 0 := by
  rw [tr_s677, v2_s067, v2_s167, v2_s267, v2_s367, v2_s467, v2_s567, v2_s667]

theorem v3_s678 : N 3 (6, 7, 8) = 0 := by
  rw [tr_s678, v2_s167, v2_s267]

theorem v3_s688 : N 3 (6, 8, 8) = 2 := by
  rw [tr_s688, v2_s068, v2_s168, v2_s268, v2_s368, v2_s468, v2_s568, v2_s668]

theorem v3_s777 : N 3 (7, 7, 7) = 17 := by
  rw [tr_s777, v2_s077, v2_s177, v2_s277, v2_s377, v2_s477, v2_s577, v2_s677, v2_s777]

theorem v3_s778 : N 3 (7, 7, 8) = 0 := by
  rw [tr_s778, v2_s177]

theorem v3_s788 : N 3 (7, 8, 8) = 2 := by
  rw [tr_s788, v2_s078, v2_s178, v2_s278, v2_s378, v2_s478, v2_s578, v2_s678, v2_s778]

theorem v3_s888 : N 3 (8, 8, 8) = 24 := by
  rw [tr_s888, v2_s088, v2_s188, v2_s288, v2_s388, v2_s488, v2_s588, v2_s688, v2_s788, v2_s888]

theorem v4_s000 : N 4 (0, 0, 0) = 1 := by
  rw [tr_s000, v3_s000]

theorem v4_s001 : N 4 (0, 0, 1) = 0 := by
  rw [tr_s001]

theorem v4_s002 : N 4 (0, 0, 2) = 0 := by
  rw [tr_s002]

theorem v4_s003 : N 4 (0, 0, 3) = 0 := by
  rw [tr_s003]

theorem v4_s004 : N 4 (0, 0, 4) = 0 := by
  rw [tr_s004]

theorem v4_s005 : N 4 (0, 0, 5) = 0 := by
  rw [tr_s005]

theorem v4_s006 : N 4 (0, 0, 6) = 0 := by
  rw [tr_s006]

theorem v4_s007 : N 4 (0, 0, 7) = 0 := by
  rw [tr_s007]

theorem v4_s008 : N 4 (0, 0, 8) = 0 := by
  rw [tr_s008]

theorem v4_s011 : N 4 (0, 1, 1) = 0 := by
  rw [tr_s011, v3_s001]

theorem v4_s012 : N 4 (0, 1, 2) = 0 := by
  rw [tr_s012]

theorem v4_s013 : N 4 (0, 1, 3) = 0 := by
  rw [tr_s013]

theorem v4_s014 : N 4 (0, 1, 4) = 0 := by
  rw [tr_s014]

theorem v4_s015 : N 4 (0, 1, 5) = 0 := by
  rw [tr_s015]

theorem v4_s016 : N 4 (0, 1, 6) = 0 := by
  rw [tr_s016]

theorem v4_s017 : N 4 (0, 1, 7) = 0 := by
  rw [tr_s017]

theorem v4_s018 : N 4 (0, 1, 8) = 0 := by
  rw [tr_s018]

theorem v4_s022 : N 4 (0, 2, 2) = 0 := by
  rw [tr_s022, v3_s002]

theorem v4_s023 : N 4 (0, 2, 3) = 0 := by
  rw [tr_s023]

theorem v4_s024 : N 4 (0, 2, 4) = 0 := by
  rw [tr_s024]

theorem v4_s025 : N 4 (0, 2, 5) = 0 := by
  rw [tr_s025]

theorem v4_s026 : N 4 (0, 2, 6) = 0 := by
  rw [tr_s026]

theorem v4_s027 : N 4 (0, 2, 7) = 0 := by
  rw [tr_s027]

theorem v4_s028 : N 4 (0, 2, 8) = 0 := by
  rw [tr_s028]

theorem v4_s033 : N 4 (0, 3, 3) = 0 := by
  rw [tr_s033, v3_s003]

theorem v4_s034 : N 4 (0, 3, 4) = 0 := by
  rw [tr_s034]

theorem v4_s035 : N 4 (0, 3, 5) = 0 := by
  rw [tr_s035]

theorem v4_s036 : N 4 (0, 3, 6) = 0 := by
  rw [tr_s036]

theorem v4_s037 : N 4 (0, 3, 7) = 0 := by
  rw [tr_s037]

theorem v4_s038 : N 4 (0, 3, 8) = 0 := by
  rw [tr_s038]

theorem v4_s044 : N 4 (0, 4, 4) = 0 := by
  rw [tr_s044, v3_s004]

theorem v4_s045 : N 4 (0, 4, 5) = 0 := by
  rw [tr_s045]

theorem v4_s046 : N 4 (0, 4, 6) = 0 := by
  rw [tr_s046]

theorem v4_s047 : N 4 (0, 4, 7) = 0 := by
  rw [tr_s047]

theorem v4_s048 : N 4 (0, 4, 8) = 0 := by
  rw [tr_s048]

theorem v4_s055 : N 4 (0, 5, 5) = 0 := by
  rw [tr_s055, v3_s005]

theorem v4_s056 : N 4 (0, 5, 6) = 0 := by
  rw [tr_s056]

theorem v4_s057 : N 4 (0, 5, 7) = 0 := by
  rw [tr_s057]

theorem v4_s058 : N 4 (0, 5, 8) = 0 := by
  rw [tr_s058]

theorem v4_s066 : N 4 (0, 6, 6) = 0 := by
  rw [tr_s066, v3_s006]

theorem v4_s067 : N 4 (0, 6, 7) = 0 := by
  rw [tr_s067]

theorem v4_s068 : N 4 (0, 6, 8) = 0 := by
  rw [tr_s068]

theorem v4_s077 : N 4 (0, 7, 7) = 0 := by
  rw [tr_s077, v3_s007]

theorem v4_s078 : N 4 (0, 7, 8) = 0 := by
  rw [tr_s078]

theorem v4_s088 : N 4 (0, 8, 8) = 0 := by
  rw [tr_s088, v3_s008]

theorem v4_s111 : N 4 (1, 1, 1) = 2 := by
  rw [tr_s111, v3_s011, v3_s111]

theorem v4_s112 : N 4 (1, 1, 2) = 2 := by
  rw [tr_s112, v3_s011, v3_s111]

theorem v4_s113 : N 4 (1, 1, 3) = 0 := by
  rw [tr_s113]

theorem v4_s114 : N 4 (1, 1, 4) = 0 := by
  rw [tr_s114]

theorem v4_s115 : N 4 (1, 1, 5) = 0 := by
  rw [tr_s115]

theorem v4_s116 : N 4 (1, 1, 6) = 0 := by
  rw [tr_s116]

theorem v4_s117 : N 4 (1, 1, 7) = 0 := by
  rw [tr_s117]

theorem v4_s118 : N 4 (1, 1, 8) = 0 := by
  rw [tr_s118]

theorem v4_s122 : N 4 (1, 2, 2) = 2 := by
  rw [tr_s122, v3_s012, v3_s112]

theorem v4_s123 : N 4 (1, 2, 3) = 2 := by
  rw [tr_s123, v3_s012, v3_s112]

theorem v4_s124 : N 4 (1, 2, 4) = 0 := by
  rw [tr_s124]

theorem v4_s125 : N 4 (1, 2, 5) = 0 := by
  rw [tr_s125]

theorem v4_s126 : N 4 (1, 2, 6) = 0 := by
  rw [tr_s126]

theorem v4_s127 : N 4 (1, 2, 7) = 0 := by
  rw [tr_s127]

theorem v4_s128 : N 4 (1, 2, 8) = 0 := by
  rw [tr_s128]

theorem v4_s133 : N 4 (1, 3, 3) = 0 := by
  rw [tr_s133, v3_s013, v3_s113]

theorem v4_s134 : N 4 (1, 3, 4) = 0 := by
  rw [tr_s134, v3_s013, v3_s113]

theorem v4_s135 : N 4 (1, 3, 5) = 0 := by
  rw [tr_s135]

theorem v4_s136 : N 4 (1, 3, 6) = 0 := by
  rw [tr_s136]

theorem v4_s137 : N 4 (1, 3, 7) = 0 := by
  rw [tr_s137]

theorem v4_s138 : N 4 (1, 3, 8) = 0 := by
  rw [tr_s138]

theorem v4_s144 : N 4 (1, 4, 4) = 0 := by
  rw [tr_s144, v3_s014, v3_s114]

theorem v4_s145 : N 4 (1, 4, 5) = 0 := by
  rw [tr_s145, v3_s014, v3_s114]

theorem v4_s146 : N 4 (1, 4, 6) = 0 := by
  rw [tr_s146]

theorem v4_s147 : N 4 (1, 4, 7) = 0 := by
  rw [tr_s147]

theorem v4_s148 : N 4 (1, 4, 8) = 0 := by
  rw [tr_s148]

theorem v4_s155 : N 4 (1, 5, 5) = 0 := by
  rw [tr_s155, v3_s015, v3_s115]

theorem v4_s156 : N 4 (1, 5, 6) = 0 := by
  rw [tr_s156, v3_s015, v3_s115]

theorem v4_s157 : N 4 (1, 5, 7) = 0 := by
  rw [tr_s157]

theorem v4_s158 : N 4 (1, 5, 8) = 0 := by
  rw [tr_s158]

theorem v4_s166 : N 4 (1, 6, 6) = 0 := by
  rw [tr_s166, v3_s016, v3_s116]

theorem v4_s167 : N 4 (1, 6, 7) = 0 := by
  rw [tr_s167, v3_s016, v3_s116]

theorem v4_s168 : N 4 (1, 6, 8) = 0 := by
  rw [tr_s168]

theorem v4_s177 : N 4 (1, 7, 7) = 0 := by
  rw [tr_s177, v3_s017, v3_s117]

theorem v4_s178 : N 4 (1, 7, 8) = 0 := by
  rw [tr_s178, v3_s017, v3_s117]

theorem v4_s188 : N 4 (1, 8, 8) = 0 := by
  rw [tr_s188, v3_s018, v3_s118]

theorem v4_s222 : N 4 (2, 2, 2) = 8 := by
  rw [tr_s222, v3_s022, v3_s122, v3_s222]

theorem v4_s223 : N 4 (2, 2, 3) = 2 := by
  rw [tr_s223, v3_s122]

theorem v4_s224 : N 4 (2, 2, 4) = 8 := by
  rw [tr_s224, v3_s022, v3_s122, v3_s222]

theorem v4_s225 : N 4 (2, 2, 5) = 0 := by
  rw [tr_s225]

theorem v4_s226 : N 4 (2, 2, 6) = 0 := by
  rw [tr_s226]

theorem v4_s227 : N 4 (2, 2, 7) = 0 := by
  rw [tr_s227]

theorem v4_s228 : N 4 (2, 2, 8) = 0 := by
  rw [tr_s228]

theorem v4_s233 : N 4 (2, 3, 3) = 4 := by
  rw [tr_s233, v3_s023, v3_s123, v3_s223]

theorem v4_s234 : N 4 (2, 3, 4) = 4 := by
  rw [tr_s234, v3_s123, v3_s223]

theorem v4_s235 : N 4 (2, 3, 5) = 4 := by
  rw [tr_s235, v3_s023, v3_s123, v3_s223]

theorem v4_s236 : N 4 (2, 3, 6) = 0 := by
  rw [tr_s236]

theorem v4_s237 : N 4 (2, 3, 7) = 0 := by
  rw [tr_s237]

theorem v4_s238 : N 4 (2, 3, 8) = 0 := by
  rw [tr_s238]

theorem v4_s244 : N 4 (2, 4, 4) = 6 := by
  rw [tr_s244, v3_s024, v3_s124, v3_s224]

theorem v4_s245 : N 4 (2, 4, 5) = 0 := by
  rw [tr_s245, v3_s124]

theorem v4_s246 : N 4 (2, 4, 6) = 6 := by
  rw [tr_s246, v3_s024, v3_s124, v3_s224]

theorem v4_s247 : N 4 (2, 4, 7) = 0 := by
  rw [tr_s247]

theorem v4_s248 : N 4 (2, 4, 8) = 0 := by
  rw [tr_s248]

theorem v4_s255 : N 4 (2, 5, 5) = 0 := by
  rw [tr_s255, v3_s025, v3_s125, v3_s225]

theorem v4_s256 : N 4 (2, 5, 6) = 0 := by
  rw [tr_s256, v3_s125]

theorem v4_s257 : N 4 (2, 5, 7) = 0 := by
  rw [tr_s257, v3_s025, v3_s125, v3_s225]

theorem v4_s258 : N 4 (2, 5, 8) = 0 := by
  rw [tr_s258]

theorem v4_s266 : N 4 (2, 6, 6) = 0 := by
  rw [tr_s266, v3_s026, v3_s126, v3_s226]

theorem v4_s267 : N 4 (2, 6, 7) = 0 := by
  rw [tr_s267, v3_s126]

theorem v4_s268 : N 4 (2, 6, 8) = 0 := by
  rw [tr_s268, v3_s026, v3_s126, v3_s226]

theorem v4_s277 : N 4 (2, 7, 7) = 0 := by
  rw [tr_s277, v3_s027, v3_s127, v3_s227]

theorem v4_s278 : N 4 (2, 7, 8) = 0 := by
  rw [tr_s278, v3_s127]

theorem v4_s288 : N 4 (2, 8, 8) = 0 := by
  rw [tr_s288, v3_s028, v3_s128, v3_s228]

theorem v4_s333 : N 4 (3, 3, 3) = 10 := by
  rw [tr_s333, v3_s033, v3_s133, v3_s233, v3_s333]

theorem v4_s334 : N 4 (3, 3, 4) = 0 := by
  rw [tr_s334, v3_s133]

theorem v4_s335 : N 4 (3, 3, 5) = 3 := by
  rw [tr_s335, v3_s233]

theorem v4_s336 : N 4 (3, 3, 6) = 10 := by
  rw [tr_s336, v3_s033, v3_s133, v3_s233, v3_s333]

theorem v4_s337 : N 4 (3, 3, 7) = 0 := by
  rw [tr_s337]

theorem v4_s338 : N 4 (3, 3, 8) = 0 := by
  rw [tr_s338]

theorem v4_s344 : N 4 (3, 4, 4) = 3 := by
  rw [tr_s344, v3_s034, v3_s134, v3_s234, v3_s334]

theorem v4_s345 : N 4 (3, 4, 5) = 3 := by
  rw [tr_s345, v3_s134, v3_s234]

theorem v4_s346 : N 4 (3, 4, 6) = 3 := by
  rw [tr_s346, v3_s234, v3_s334]

theorem v4_s347 : N 4 (3, 4, 7) = 3 := by
  rw [tr_s347, v3_s034, v3_s134, v3_s234, v3_s334]

theorem v4_s348 : N 4 (3, 4, 8) = 0 := by
  rw [tr_s348]

theorem v4_s355 : N 4 (3, 5, 5) = 5 := by
  rw [tr_s355, v3_s035, v3_s135, v3_s235, v3_s335]

theorem v4_s356 : N 4 (3, 5, 6) = 2 := by
  rw [tr_s356, v3_s135, v3_s335]

theorem v4_s357 : N 4 (3, 5, 7) = 3 := by
  rw [tr_s357, v3_s235]

theorem v4_s358 : N 4 (3, 5, 8) = 5 := by
  rw [tr_s358, v3_s035, v3_s135, v3_s235, v3_s335]

theorem v4_s366 : N 4 (3, 6, 6) = 7 := by
  rw [tr_s366, v3_s036, v3_s136, v3_s236, v3_s336]

theorem v4_s367 : N 4 (3, 6, 7) = 0 := by
  rw [tr_s367, v3_s136]

theorem v4_s368 : N 4 (3, 6, 8) = 0 := by
  rw [tr_s368, v3_s236]

theorem v4_s377 : N 4 (3, 7, 7) = 0 := by
  rw [tr_s377, v3_s037, v3_s137, v3_s237, v3_s337]

theorem v4_s378 : N 4 (3, 7, 8) = 0 := by
  rw [tr_s378, v3_s137]

theorem v4_s388 : N 4 (3, 8, 8) = 0 := by
  rw [tr_s388, v3_s038, v3_s138, v3_s238, v3_s338]

theorem v4_s444 : N 4 (4, 4, 4) = 18 := by
  rw [tr_s444, v3_s044, v3_s144, v3_s244, v3_s344, v3_s444]

theorem v4_s445 : N 4 (4, 4, 5) = 0 := by
  rw [tr_s445, v3_s144]

theorem v4_s446 : N 4 (4, 4, 6) = 4 := by
  rw [tr_s446, v3_s244]

theorem v4_s447 : N 4 (4, 4, 7) = 2 := by
  rw [tr_s447, v3_s344]

theorem v4_s448 : N 4 (4, 4, 8) = 18 := by
  rw [tr_s448, v3_s044, v3_s144, v3_s244, v3_s344, v3_s444]

theorem v4_s455 : N 4 (4, 5, 5) = 2 := by
  rw [tr_s455, v3_s045, v3_s145, v3_s245, v3_s345, v3_s445]

theorem v4_s456 : N 4 (4, 5, 6) = 0 := by
  rw [tr_s456, v3_s145, v3_s245]

theorem v4_s457 : N 4 (4, 5, 7) = 2 := by
  rw [tr_s457, v3_s245, v3_s345]

theorem v4_s458 : N 4 (4, 5, 8) = 2 := by
  rw [tr_s458, v3_s345, v3_s445]

theorem v4_s466 : N 4 (4, 6, 6) = 9 := by
  rw [tr_s466, v3_s046, v3_s146, v3_s246, v3_s346, v3_s446]

theorem v4_s467 : N 4 (4, 6, 7) = 2 := by
  rw [tr_s467, v3_s146, v3_s346]

theorem v4_s468 : N 4 (4, 6, 8) = 7 := by
  rw [tr_s468, v3_s246, v3_s446]

theorem v4_s477 : N 4 (4, 7, 7) = 4 := by
  rw [tr_s477, v3_s047, v3_s147, v3_s247, v3_s347, v3_s447]

theorem v4_s478 : N 4 (4, 7, 8) = 2 := by
  rw [tr_s478, v3_s147, v3_s447]

theorem v4_s488 : N 4 (4, 8, 8) = 12 := by
  rw [tr_s488, v3_s048, v3_s148, v3_s248, v3_s348, v3_s448]

theorem v4_s555 : N 4 (5, 5, 5) = 16 := by
  rw [tr_s555, v3_s055, v3_s155, v3_s255, v3_s355, v3_s455, v3_s555]

theorem v4_s556 : N 4 (5, 5, 6) = 0 := by
  rw [tr_s556, v3_s155]

theorem v4_s557 : N 4 (5, 5, 7) = 0 := by
  rw [tr_s557, v3_s255]

theorem v4_s558 : N 4 (5, 5, 8) = 3 := by
  rw [tr_s558, v3_s355]

theorem v4_s566 : N 4 (5, 6, 6) = 1 := by
  rw [tr_s566, v3_s056, v3_s156, v3_s256, v3_s356, v3_s456, v3_s556]

theorem v4_s567 : N 4 (5, 6, 7) = 0 := by
  rw [tr_s567, v3_s156, v3_s256]

theorem v4_s568 : N 4 (5, 6, 8) = 1 := by
  rw [tr_s568, v3_s256, v3_s356]

theorem v4_s577 : N 4 (5, 7, 7) = 3 := by
  rw [tr_s577, v3_s057, v3_s157, v3_s257, v3_s357, v3_s457, v3_s557]

theorem v4_s578 : N 4 (5, 7, 8) = 2 := by
  rw [tr_s578, v3_s157, v3_s357]

theorem v4_s588 : N 4 (5, 8, 8) = 6 := by
  rw [tr_s588, v3_s058, v3_s158, v3_s258, v3_s358, v3_s458, v3_s558]

theorem v4_s666 : N 4 (6, 6, 6) = 30 := by
  rw [tr_s666, v3_s066, v3_s166, v3_s266, v3_s366, v3_s466, v3_s566, v3_s666]

theorem v4_s667 : N 4 (6, 6, 7) = 0 := by
  rw [tr_s667, v3_s166]

theorem v4_s668 : N 4 (6, 6, 8) = 0 := by
  rw [tr_s668, v3_s266]

theorem v4_s677 : N 4 (6, 7, 7) = 2 := by
  rw [tr_s677, v3_s067, v3_s167, v3_s267, v3_s367, v3_s467, v3_s567, v3_s667]

theorem v4_s678 : N 4 (6, 7, 8) = 0 := by
  rw [tr_s678, v3_s167, v3_s267]

theorem v4_s688 : N 4 (6, 8, 8) = 5 := by
  rw [tr_s688, v3_s068, v3_s168, v3_s268, v3_s368, v3_s468, v3_s568, v3_s668]

theorem v4_s777 : N 4 (7, 7, 7) = 22 := by
  rw [tr_s777, v3_s077, v3_s177, v3_s277, v3_s377, v3_s477, v3_s577, v3_s677, v3_s777]

theorem v4_s778 : N 4 (7, 7, 8) = 0 := by
  rw [tr_s778, v3_s177]

theorem v4_s788 : N 4 (7, 8, 8) = 2 := by
  rw [tr_s788, v3_s078, v3_s178, v3_s278, v3_s378, v3_s478, v3_s578, v3_s678, v3_s778]

theorem v4_s888 : N 4 (8, 8, 8) = 40 := by
  rw [tr_s888, v3_s088, v3_s188, v3_s288, v3_s388, v3_s488, v3_s588, v3_s688, v3_s788, v3_s888]

theorem v5_s000 : N 5 (0, 0, 0) = 1 := by
  rw [tr_s000, v4_s000]

theorem v5_s001 : N 5 (0, 0, 1) = 0 := by
  rw [tr_s001]

theorem v5_s002 : N 5 (0, 0, 2) = 0 := by
  rw [tr_s002]

theorem v5_s003 : N 5 (0, 0, 3) = 0 := by
  rw [tr_s003]

theorem v5_s004 : N 5 (0, 0, 4) = 0 := by
  rw [tr_s004]

theorem v5_s005 : N 5 (0, 0, 5) = 0 := by
  rw [tr_s005]

theorem v5_s006 : N 5 (0, 0, 6) = 0 := by
  rw [tr_s006]

theorem v5_s007 : N 5 (0, 0, 7) = 0 := by
  rw [tr_s007]

theorem v5_s008 : N 5 (0, 0, 8) = 0 := by
  rw [tr_s008]

theorem v5_s011 : N 5 (0, 1, 1) = 0 := by
  rw [tr_s011, v4_s001]

theorem v5_s012 : N 5 (0, 1, 2) = 0 := by
  rw [tr_s012]

theorem v5_s013 : N 5 (0, 1, 3) = 0 := by
  rw [tr_s013]

theorem v5_s014 : N 5 (0, 1, 4) = 0 := by
  rw [tr_s014]

theorem v5_s015 : N 5 (0, 1, 5) = 0 := by
  rw [tr_s015]

theorem v5_s016 : N 5 (0, 1, 6) = 0 := by
  rw [tr_s016]

theorem v5_s017 : N 5 (0, 1, 7) = 0 := by
  rw [tr_s017]

theorem v5_s018 : N 5 (0, 1, 8) = 0 := by
  rw [tr_s018]

theorem v5_s022 : N 5 (0, 2, 2) = 0 := by
  rw [tr_s022, v4_s002]

theorem v5_s023 : N 5 (0, 2, 3) = 0 := by
  rw [tr_s023]

theorem v5_s024 : N 5 (0, 2, 4) = 0 := by
  rw [tr_s024]

theorem v5_s025 : N 5 (0, 2, 5) = 0 := by
  rw [tr_s025]

theorem v5_s026 : N 5 (0, 2, 6) = 0 := by
  rw [tr_s026]

theorem v5_s027 : N 5 (0, 2, 7) = 0 := by
  rw [tr_s027]

theorem v5_s028 : N 5 (0, 2, 8) = 0 := by
  rw [tr_s028]

theorem v5_s033 : N 5 (0, 3, 3) = 0 := by
  rw [tr_s033, v4_s003]

theorem v5_s034 : N 5 (0, 3, 4) = 0 := by
  rw [tr_s034]

theorem v5_s035 : N 5 (0, 3, 5) = 0 := by
  rw [tr_s035]

theorem v5_s036 : N 5 (0, 3, 6) = 0 := by
  rw [tr_s036]

theorem v5_s037 : N 5 (0, 3, 7) = 0 := by
  rw [tr_s037]

theorem v5_s038 : N 5 (0, 3, 8) = 0 := by
  rw [tr_s038]

theorem v5_s044 : N 5 (0, 4, 4) = 0 := by
  rw [tr_s044, v4_s004]

theorem v5_s045 : N 5 (0, 4, 5) = 0 := by
  rw [tr_s045]

theorem v5_s046 : N 5 (0, 4, 6) = 0 := by
  rw [tr_s046]

theorem v5_s047 : N 5 (0, 4, 7) = 0 := by
  rw [tr_s047]

theorem v5_s048 : N 5 (0, 4, 8) = 0 := by
  rw [tr_s048]

theorem v5_s055 : N 5 (0, 5, 5) = 0 := by
  rw [tr_s055, v4_s005]

theorem v5_s056 : N 5 (0, 5, 6) = 0 := by
  rw [tr_s056]

theorem v5_s057 : N 5 (0, 5, 7) = 0 := by
  rw [tr_s057]

theorem v5_s058 : N 5 (0, 5, 8) = 0 := by
  rw [tr_s058]

theorem v5_s066 : N 5 (0, 6, 6) = 0 := by
  rw [tr_s066, v4_s006]

theorem v5_s067 : N 5 (0, 6, 7) = 0 := by
  rw [tr_s067]

theorem v5_s068 : N 5 (0, 6, 8) = 0 := by
  rw [tr_s068]

theorem v5_s077 : N 5 (0, 7, 7) = 0 := by
  rw [tr_s077, v4_s007]

theorem v5_s078 : N 5 (0, 7, 8) = 0 := by
  rw [tr_s078]

theorem v5_s088 : N 5 (0, 8, 8) = 0 := by
  rw [tr_s088, v4_s008]

theorem v5_s111 : N 5 (1, 1, 1) = 2 := by
  rw [tr_s111, v4_s011, v4_s111]

theorem v5_s112 : N 5 (1, 1, 2) = 2 := by
  rw [tr_s112, v4_s011, v4_s111]

theorem v5_s113 : N 5 (1, 1, 3) = 0 := by
  rw [tr_s113]

theorem v5_s114 : N 5 (1, 1, 4) = 0 := by
  rw [tr_s114]

theorem v5_s115 : N 5 (1, 1, 5) = 0 := by
  rw [tr_s115]

theorem v5_s116 : N 5 (1, 1, 6) = 0 := by
  rw [tr_s116]

theorem v5_s117 : N 5 (1, 1, 7) = 0 := by
  rw [tr_s117]

theorem v5_s118 : N 5 (1, 1, 8) = 0 := by
  rw [tr_s118]

theorem v5_s122 : N 5 (1, 2, 2) = 2 := by
  rw [tr_s122, v4_s012, v4_s112]

theorem v5_s123 : N 5 (1, 2, 3) = 2 := by
  rw [tr_s123, v4_s012, v4_s112]

theorem v5_s124 : N 5 (1, 2, 4) = 0 := by
  rw [tr_s124]

theorem v5_s125 : N 5 (1, 2, 5) = 0 := by
  rw [tr_s125]

theorem v5_s126 : N 5 (1, 2, 6) = 0 := by
  rw [tr_s126]

theorem v5_s127 : N 5 (1, 2, 7) = 0 := by
  rw [tr_s127]

theorem v5_s128 : N 5 (1, 2, 8) = 0 := by
  rw [tr_s128]

theorem v5_s133 : N 5 (1, 3, 3) = 0 := by
  rw [tr_s133, v4_s013, v4_s113]

theorem v5_s134 : N 5 (1, 3, 4) = 0 := by
  rw [tr_s134, v4_s013, v4_s113]

theorem v5_s135 : N 5 (1, 3, 5) = 0 := by
  rw [tr_s135]

theorem v5_s136 : N 5 (1, 3, 6) = 0 := by
  rw [tr_s136]

theorem v5_s137 : N 5 (1, 3, 7) = 0 := by
  rw [tr_s137]

theorem v5_s138 : N 5 (1, 3, 8) = 0 := by
  rw [tr_s138]

theorem v5_s144 : N 5 (1, 4, 4) = 0 := by
  rw [tr_s144, v4_s014, v4_s114]

theorem v5_s145 : N 5 (1, 4, 5) = 0 := by
  rw [tr_s145, v4_s014, v4_s114]

theorem v5_s146 : N 5 (1, 4, 6) = 0 := by
  rw [tr_s146]

theorem v5_s147 : N 5 (1, 4, 7) = 0 := by
  rw [tr_s147]

theorem v5_s148 : N 5 (1, 4, 8) = 0 := by
  rw [tr_s148]

theorem v5_s155 : N 5 (1, 5, 5) = 0 := by
  rw [tr_s155, v4_s015, v4_s115]

theorem v5_s156 : N 5 (1, 5, 6) = 0 := by
  rw [tr_s156, v4_s015, v4_s115]

theorem v5_s157 : N 5 (1, 5, 7) = 0 := by
  rw [tr_s157]

theorem v5_s158 : N 5 (1, 5, 8) = 0 := by
  rw [tr_s158]

theorem v5_s166 : N 5 (1, 6, 6) = 0 := by
  rw [tr_s166, v4_s016, v4_s116]

theorem v5_s167 : N 5 (1, 6, 7) = 0 := by
  rw [tr_s167, v4_s016, v4_s116]

theorem v5_s168 : N 5 (1, 6, 8) = 0 := by
  rw [tr_s168]

theorem v5_s177 : N 5 (1, 7, 7) = 0 := by
  rw [tr_s177, v4_s017, v4_s117]

theorem v5_s178 : N 5 (1, 7, 8) = 0 := by
  rw [tr_s178, v4_s017, v4_s117]

theorem v5_s188 : N 5 (1, 8, 8) = 0 := by
  rw [tr_s188, v4_s018, v4_s118]

theorem v5_s222 : N 5 (2, 2, 2) = 10 := by
  rw [tr_s222, v4_s022, v4_s122, v4_s222]

theorem v5_s223 : N 5 (2, 2, 3) = 2 := by
  rw [tr_s223, v4_s122]

theorem v5_s224 : N 5 (2, 2, 4) = 10 := by
  rw [tr_s224, v4_s022, v4_s122, v4_s222]

theorem v5_s225 : N 5 (2, 2, 5) = 0 := by
  rw [tr_s225]

theorem v5_s226 : N 5 (2, 2, 6) = 0 := by
  rw [tr_s226]

theorem v5_s227 : N 5 (2, 2, 7) = 0 := by
  rw [tr_s227]

theorem v5_s228 : N 5 (2, 2, 8) = 0 := by
  rw [tr_s228]

theorem v5_s233 : N 5 (2, 3, 3) = 4 := by
  rw [tr_s233, v4_s023, v4_s123, v4_s223]

theorem v5_s234 : N 5 (2, 3, 4) = 4 := by
  rw [tr_s234, v4_s123, v4_s223]

theorem v5_s235 : N 5 (2, 3, 5) = 4 := by
  rw [tr_s235, v4_s023, v4_s123, v4_s223]

theorem v5_s236 : N 5 (2, 3, 6) = 0 := by
  rw [tr_s236]

theorem v5_s237 : N 5 (2, 3, 7) = 0 := by
  rw [tr_s237]

theorem v5_s238 : N 5 (2, 3, 8) = 0 := by
  rw [tr_s238]

theorem v5_s244 : N 5 (2, 4, 4) = 8 := by
  rw [tr_s244, v4_s024, v4_s124, v4_s224]

theorem v5_s245 : N 5 (2, 4, 5) = 0 := by
  rw [tr_s245, v4_s124]

theorem v5_s246 : N 5 (2, 4, 6) = 8 := by
  rw [tr_s246, v4_s024, v4_s124, v4_s224]

theorem v5_s247 : N 5 (2, 4, 7) = 0 := by
  rw [tr_s247]

theorem v5_s248 : N 5 (2, 4, 8) = 0 := by
  rw [tr_s248]

theorem v5_s255 : N 5 (2, 5, 5) = 0 := by
  rw [tr_s255, v4_s025, v4_s125, v4_s225]

theorem v5_s256 : N 5 (2, 5, 6) = 0 := by
  rw [tr_s256, v4_s125]

theorem v5_s257 : N 5 (2, 5, 7) = 0 := by
  rw [tr_s257, v4_s025, v4_s125, v4_s225]

theorem v5_s258 : N 5 (2, 5, 8) = 0 := by
  rw [tr_s258]

theorem v5_s266 : N 5 (2, 6, 6) = 0 := by
  rw [tr_s266, v4_s026, v4_s126, v4_s226]

theorem v5_s267 : N 5 (2, 6, 7) = 0 := by
  rw [tr_s267, v4_s126]

theorem v5_s268 : N 5 (2, 6, 8) = 0 := by
  rw [tr_s268, v4_s026, v4_s126, v4_s226]

theorem v5_s277 : N 5 (2, 7, 7) = 0 := by
  rw [tr_s277, v4_s027, v4_s127, v4_s227]

theorem v5_s278 : N 5 (2, 7, 8) = 0 := by
  rw [tr_s278, v4_s127]

theorem v5_s288 : N 5 (2, 8, 8) = 0 := by
  rw [tr_s288, v4_s028, v4_s128, v4_s228]

theorem v5_s333 : N 5 (3, 3, 3) = 14 := by
  rw [tr_s333, v4_s033, v4_s133, v4_s233, v4_s333]

theorem v5_s334 : N 5 (3, 3, 4) = 0 := by
  rw [tr_s334, v4_s133]

theorem v5_s335 : N 5 (3, 3, 5) = 4 := by
  rw [tr_s335, v4_s233]

theorem v5_s336 : N 5 (3, 3, 6) = 14 := by
  rw [tr_s336, v4_s033, v4_s133, v4_s233, v4_s333]

theorem v5_s337 : N 5 (3, 3, 7) = 0 := by
  rw [tr_s337]

theorem v5_s338 : N 5 (3, 3, 8) = 0 := by
  rw [tr_s338]

theorem v5_s344 : N 5 (3, 4, 4) = 4 := by
  rw [tr_s344, v4_s034, v4_s134, v4_s234, v4_s334]

theorem v5_s345 : N 5 (3, 4, 5) = 4 := by
  rw [tr_s345, v4_s134, v4_s234]

theorem v5_s346 : N 5 (3, 4, 6) = 4 := by
  rw [tr_s346, v4_s234, v4_s334]

theorem v5_s347 : N 5 (3, 4, 7) = 4 := by
  rw [tr_s347, v4_s034, v4_s134, v4_s234, v4_s334]

theorem v5_s348 : N 5 (3, 4, 8) = 0 := by
  rw [tr_s348]

theorem v5_s355 : N 5 (3, 5, 5) = 7 := by
  rw [tr_s355, v4_s035, v4_s135, v4_s235, v4_s335]

theorem v5_s356 : N 5 (3, 5, 6) = 3 := by
  rw [tr_s356, v4_s135, v4_s335]

theorem v5_s357 : N 5 (3, 5, 7) = 4 := by
  rw [tr_s357, v4_s235]

theorem v5_s358 : N 5 (3, 5, 8) = 7 := by
  rw [tr_s358, v4_s035, v4_s135, v4_s235, v4_s335]

theorem v5_s366 : N 5 (3, 6, 6) = 10 := by
  rw [tr_s366, v4_s036, v4_s136, v4_s236, v4_s336]

theorem v5_s367 : N 5 (3, 6, 7) = 0 := by
  rw [tr_s367, v4_s136]

theorem v5_s368 : N 5 (3, 6, 8) = 0 := by
  rw [tr_s368, v4_s236]

theorem v5_s377 : N 5 (3, 7, 7) = 0 := by
  rw [tr_s377, v4_s037, v4_s137, v4_s237, v4_s337]

theorem v5_s378 : N 5 (3, 7, 8) = 0 := by
  rw [tr_s378, v4_s137]

theorem v5_s388 : N 5 (3, 8, 8) = 0 := by
  rw [tr_s388, v4_s038, v4_s138, v4_s238, v4_s338]

theorem v5_s444 : N 5 (4, 4, 4) = 27 := by
  rw [tr_s444, v4_s044, v4_s144, v4_s244, v4_s344, v4_s444]

theorem v5_s445 : N 5 (4, 4, 5) = 0 := by
  rw [tr_s445, v4_s144]

theorem v5_s446 : N 5 (4, 4, 6) = 6 := by
  rw [tr_s446, v4_s244]

theorem v5_s447 : N 5 (4, 4, 7) = 3 := by
  rw [tr_s447, v4_s344]

theorem v5_s448 : N 5 (4, 4, 8) = 27 := by
  rw [tr_s448, v4_s044, v4_s144, v4_s244, v4_s344, v4_s444]

theorem v5_s455 : N 5 (4, 5, 5) = 3 := by
  rw [tr_s455, v4_s045, v4_s145, v4_s245, v4_s345, v4_s445]

theorem v5_s456 : N 5 (4, 5, 6) = 0 := by
  rw [tr_s456, v4_s145, v4_s245]

theorem v5_s457 : N 5 (4, 5, 7) = 3 := by
  rw [tr_s457, v4_s245, v4_s345]

theorem v5_s458 : N 5 (4, 5, 8) = 3 := by
  rw [tr_s458, v4_s345, v4_s445]

theorem v5_s466 : N 5 (4, 6, 6) = 13 := by
  rw [tr_s466, v4_s046, v4_s146, v4_s246, v4_s346, v4_s446]

theorem v5_s467 : N 5 (4, 6, 7) = 3 := by
  rw [tr_s467, v4_s146, v4_s346]

theorem v5_s468 : N 5 (4, 6, 8) = 10 := by
  rw [tr_s468, v4_s246, v4_s446]

theorem v5_s477 : N 5 (4, 7, 7) = 5 := by
  rw [tr_s477, v4_s047, v4_s147, v4_s247, v4_s347, v4_s447]

theorem v5_s478 : N 5 (4, 7, 8) = 2 := by
  rw [tr_s478, v4_s147, v4_s447]

theorem v5_s488 : N 5 (4, 8, 8) = 18 := by
  rw [tr_s488, v4_s048, v4_s148, v4_s248, v4_s348, v4_s448]

theorem v5_s555 : N 5 (5, 5, 5) = 23 := by
  rw [tr_s555, v4_s055, v4_s155, v4_s255, v4_s355, v4_s455, v4_s555]

theorem v5_s556 : N 5 (5, 5, 6) = 0 := by
  rw [tr_s556, v4_s155]

theorem v5_s557 : N 5 (5, 5, 7) = 0 := by
  rw [tr_s557, v4_s255]

theorem v5_s558 : N 5 (5, 5, 8) = 5 := by
  rw [tr_s558, v4_s355]

theorem v5_s566 : N 5 (5, 6, 6) = 2 := by
  rw [tr_s566, v4_s056, v4_s156, v4_s256, v4_s356, v4_s456, v4_s556]

theorem v5_s567 : N 5 (5, 6, 7) = 0 := by
  rw [tr_s567, v4_s156, v4_s256]

theorem v5_s568 : N 5 (5, 6, 8) = 2 := by
  rw [tr_s568, v4_s256, v4_s356]

theorem v5_s577 : N 5 (5, 7, 7) = 5 := by
  rw [tr_s577, v4_s057, v4_s157, v4_s257, v4_s357, v4_s457, v4_s557]

theorem v5_s578 : N 5 (5, 7, 8) = 3 := by
  rw [tr_s578, v4_s157, v4_s357]

theorem v5_s588 : N 5 (5, 8, 8) = 10 := by
  rw [tr_s588, v4_s058, v4_s158, v4_s258, v4_s358, v4_s458, v4_s558]

theorem v5_s666 : N 5 (6, 6, 6) = 47 := by
  rw [tr_s666, v4_s066, v4_s166, v4_s266, v4_s366, v4_s466, v4_s566, v4_s666]

theorem v5_s667 : N 5 (6, 6, 7) = 0 := by
  rw [tr_s667, v4_s166]

theorem v5_s668 : N 5 (6, 6, 8) = 0 := by
  rw [tr_s668, v4_s266]

theorem v5_s677 : N 5 (6, 7, 7) = 2 := by
  rw [tr_s677, v4_s067, v4_s167, v4_s267, v4_s367, v4_s467, v4_s567, v4_s667]

theorem v5_s678 : N 5 (6, 7, 8) = 0 := by
  rw [tr_s678, v4_s167, v4_s267]

theorem v5_s688 : N 5 (6, 8, 8) = 8 := by
  rw [tr_s688, v4_s068, v4_s168, v4_s268, v4_s368, v4_s468, v4_s568, v4_s668]

theorem v5_s777 : N 5 (7, 7, 7) = 31 := by
  rw [tr_s777, v4_s077, v4_s177, v4_s277, v4_s377, v4_s477, v4_s577, v4_s677, v4_s777]

theorem v5_s778 : N 5 (7, 7, 8) = 0 := by
  rw [tr_s778, v4_s177]

theorem v5_s788 : N 5 (7, 8, 8) = 4 := by
  rw [tr_s788, v4_s078, v4_s178, v4_s278, v4_s378, v4_s478, v4_s578, v4_s678, v4_s778]

theorem v5_s888 : N 5 (8, 8, 8) = 65 := by
  rw [tr_s888, v4_s088, v4_s188, v4_s288, v4_s388, v4_s488, v4_s588, v4_s688, v4_s788, v4_s888]

theorem v6_s000 : N 6 (0, 0, 0) = 1 := by
  rw [tr_s000, v5_s000]

theorem v6_s001 : N 6 (0, 0, 1) = 0 := by
  rw [tr_s001]

theorem v6_s002 : N 6 (0, 0, 2) = 0 := by
  rw [tr_s002]

theorem v6_s003 : N 6 (0, 0, 3) = 0 := by
  rw [tr_s003]

theorem v6_s004 : N 6 (0, 0, 4) = 0 := by
  rw [tr_s004]

theorem v6_s005 : N 6 (0, 0, 5) = 0 := by
  rw [tr_s005]

theorem v6_s006 : N 6 (0, 0, 6) = 0 := by
  rw [tr_s006]

theorem v6_s007 : N 6 (0, 0, 7) = 0 := by
  rw [tr_s007]

theorem v6_s008 : N 6 (0, 0, 8) = 0 := by
  rw [tr_s008]

theorem v6_s011 : N 6 (0, 1, 1) = 0 := by
  rw [tr_s011, v5_s001]

theorem v6_s012 : N 6 (0, 1, 2) = 0 := by
  rw [tr_s012]

theorem v6_s013 : N 6 (0, 1, 3) = 0 := by
  rw [tr_s013]

theorem v6_s014 : N 6 (0, 1, 4) = 0 := by
  rw [tr_s014]

theorem v6_s015 : N 6 (0, 1, 5) = 0 := by
  rw [tr_s015]

theorem v6_s016 : N 6 (0, 1, 6) = 0 := by
  rw [tr_s016]

theorem v6_s017 : N 6 (0, 1, 7) = 0 := by
  rw [tr_s017]

theorem v6_s018 : N 6 (0, 1, 8) = 0 := by
  rw [tr_s018]

theorem v6_s022 : N 6 (0, 2, 2) = 0 := by
  rw [tr_s022, v5_s002]

theorem v6_s023 : N 6 (0, 2, 3) = 0 := by
  rw [tr_s023]

theorem v6_s024 : N 6 (0, 2, 4) = 0 := by
  rw [tr_s024]

theorem v6_s025 : N 6 (0, 2, 5) = 0 := by
  rw [tr_s025]

theorem v6_s026 : N 6 (0, 2, 6) = 0 := by
  rw [tr_s026]

theorem v6_s027 : N 6 (0, 2, 7) = 0 := by
  rw [tr_s027]

theorem v6_s028 : N 6 (0, 2, 8) = 0 := by
  rw [tr_s028]

theorem v6_s033 : N 6 (0, 3, 3) = 0 := by
  rw [tr_s033, v5_s003]

theorem v6_s034 : N 6 (0, 3, 4) = 0 := by
  rw [tr_s034]

theorem v6_s035 : N 6 (0, 3, 5) = 0 := by
  rw [tr_s035]

theorem v6_s036 : N 6 (0, 3, 6) = 0 := by
  rw [tr_s036]

theorem v6_s037 : N 6 (0, 3, 7) = 0 := by
  rw [tr_s037]

theorem v6_s038 : N 6 (0, 3, 8) = 0 := by
  rw [tr_s038]

theorem v6_s044 : N 6 (0, 4, 4) = 0 := by
  rw [tr_s044, v5_s004]

theorem v6_s045 : N 6 (0, 4, 5) = 0 := by
  rw [tr_s045]

theorem v6_s046 : N 6 (0, 4, 6) = 0 := by
  rw [tr_s046]

theorem v6_s047 : N 6 (0, 4, 7) = 0 := by
  rw [tr_s047]

theorem v6_s048 : N 6 (0, 4, 8) = 0 := by
  rw [tr_s048]

theorem v6_s055 : N 6 (0, 5, 5) = 0 := by
  rw [tr_s055, v5_s005]

theorem v6_s056 : N 6 (0, 5, 6) = 0 := by
  rw [tr_s056]

theorem v6_s057 : N 6 (0, 5, 7) = 0 := by
  rw [tr_s057]

theorem v6_s058 : N 6 (0, 5, 8) = 0 := by
  rw [tr_s058]

theorem v6_s066 : N 6 (0, 6, 6) = 0 := by
  rw [tr_s066, v5_s006]

theorem v6_s067 : N 6 (0, 6, 7) = 0 := by
  rw [tr_s067]

theorem v6_s068 : N 6 (0, 6, 8) = 0 := by
  rw [tr_s068]

theorem v6_s077 : N 6 (0, 7, 7) = 0 := by
  rw [tr_s077, v5_s007]

theorem v6_s078 : N 6 (0, 7, 8) = 0 := by
  rw [tr_s078]

theorem v6_s088 : N 6 (0, 8, 8) = 0 := by
  rw [tr_s088, v5_s008]

theorem v6_s111 : N 6 (1, 1, 1) = 2 := by
  rw [tr_s111, v5_s011, v5_s111]

theorem v6_s112 : N 6 (1, 1, 2) = 2 := by
  rw [tr_s112, v5_s011, v5_s111]

theorem v6_s113 : N 6 (1, 1, 3) = 0 := by
  rw [tr_s113]

theorem v6_s114 : N 6 (1, 1, 4) = 0 := by
  rw [tr_s114]

theorem v6_s115 : N 6 (1, 1, 5) = 0 := by
  rw [tr_s115]

theorem v6_s116 : N 6 (1, 1, 6) = 0 := by
  rw [tr_s116]

theorem v6_s117 : N 6 (1, 1, 7) = 0 := by
  rw [tr_s117]

theorem v6_s118 : N 6 (1, 1, 8) = 0 := by
  rw [tr_s118]

theorem v6_s122 : N 6 (1, 2, 2) = 2 := by
  rw [tr_s122, v5_s012, v5_s112]

theorem v6_s123 : N 6 (1, 2, 3) = 2 := by
  rw [tr_s123, v5_s012, v5_s112]

theorem v6_s124 : N 6 (1, 2, 4) = 0 := by
  rw [tr_s124]

theorem v6_s125 : N 6 (1, 2, 5) = 0 := by
  rw [tr_s125]

theorem v6_s126 : N 6 (1, 2, 6) = 0 := by
  rw [tr_s126]

theorem v6_s127 : N 6 (1, 2, 7) = 0 := by
  rw [tr_s127]

theorem v6_s128 : N 6 (1, 2, 8) = 0 := by
  rw [tr_s128]

theorem v6_s133 : N 6 (1, 3, 3) = 0 := by
  rw [tr_s133, v5_s013, v5_s113]

theorem v6_s134 : N 6 (1, 3, 4) = 0 := by
  rw [tr_s134, v5_s013, v5_s113]

theorem v6_s135 : N 6 (1, 3, 5) = 0 := by
  rw [tr_s135]

theorem v6_s136 : N 6 (1, 3, 6) = 0 := by
  rw [tr_s136]

theorem v6_s137 : N 6 (1, 3, 7) = 0 := by
  rw [tr_s137]

theorem v6_s138 : N 6 (1, 3, 8) = 0 := by
  rw [tr_s138]

theorem v6_s144 : N 6 (1, 4, 4) = 0 := by
  rw [tr_s144, v5_s014, v5_s114]

theorem v6_s145 : N 6 (1, 4, 5) = 0 := by
  rw [tr_s145, v5_s014, v5_s114]

theorem v6_s146 : N 6 (1, 4, 6) = 0 := by
  rw [tr_s146]

theorem v6_s147 : N 6 (1, 4, 7) = 0 := by
  rw [tr_s147]

theorem v6_s148 : N 6 (1, 4, 8) = 0 := by
  rw [tr_s148]

theorem v6_s155 : N 6 (1, 5, 5) = 0 := by
  rw [tr_s155, v5_s015, v5_s115]

theorem v6_s156 : N 6 (1, 5, 6) = 0 := by
  rw [tr_s156, v5_s015, v5_s115]

theorem v6_s157 : N 6 (1, 5, 7) = 0 := by
  rw [tr_s157]

theorem v6_s158 : N 6 (1, 5, 8) = 0 := by
  rw [tr_s158]

theorem v6_s166 : N 6 (1, 6, 6) = 0 := by
  rw [tr_s166, v5_s016, v5_s116]

theorem v6_s167 : N 6 (1, 6, 7) = 0 := by
  rw [tr_s167, v5_s016, v5_s116]

theorem v6_s168 : N 6 (1, 6, 8) = 0 := by
  rw [tr_s168]

theorem v6_s177 : N 6 (1, 7, 7) = 0 := by
  rw [tr_s177, v5_s017, v5_s117]

theorem v6_s178 : N 6 (1, 7, 8) = 0 := by
  rw [tr_s178, v5_s017, v5_s117]

theorem v6_s188 : N 6 (1, 8, 8) = 0 := by
  rw [tr_s188, v5_s018, v5_s118]

theorem v6_s222 : N 6 (2, 2, 2) = 12 := by
  rw [tr_s222, v5_s022, v5_s122, v5_s222]

theorem v6_s223 : N 6 (2, 2, 3) = 2 := by
  rw [tr_s223, v5_s122]

theorem v6_s224 : N 6 (2, 2, 4) = 12 := by
  rw [tr_s224, v5_s022, v5_s122, v5_s222]

theorem v6_s225 : N 6 (2, 2, 5) = 0 := by
  rw [tr_s225]

theorem v6_s226 : N 6 (2, 2, 6) = 0 := by
  rw [tr_s226]

theorem v6_s227 : N 6 (2, 2, 7) = 0 := by
  rw [tr_s227]

theorem v6_s228 : N 6 (2, 2, 8) = 0 := by
  rw [tr_s228]

theorem v6_s233 : N 6 (2, 3, 3) = 4 := by
  rw [tr_s233, v5_s023, v5_s123, v5_s223]

theorem v6_s234 : N 6 (2, 3, 4) = 4 := by
  rw [tr_s234, v5_s123, v5_s223]

theorem v6_s235 : N 6 (2, 3, 5) = 4 := by
  rw [tr_s235, v5_s023, v5_s123, v5_s223]

theorem v6_s236 : N 6 (2, 3, 6) = 0 := by
  rw [tr_s236]

theorem v6_s237 : N 6 (2, 3, 7) = 0 := by
  rw [tr_s237]

theorem v6_s238 : N 6 (2, 3, 8) = 0 := by
  rw [tr_s238]

theorem v6_s244 : N 6 (2, 4, 4) = 10 := by
  rw [tr_s244, v5_s024, v5_s124, v5_s224]

theorem v6_s245 : N 6 (2, 4, 5) = 0 := by
  rw [tr_s245, v5_s124]

theorem v6_s246 : N 6 (2, 4, 6) = 10 := by
  rw [tr_s246, v5_s024, v5_s124, v5_s224]

theorem v6_s247 : N 6 (2, 4, 7) = 0 := by
  rw [tr_s247]

theorem v6_s248 : N 6 (2, 4, 8) = 0 := by
  rw [tr_s248]

theorem v6_s255 : N 6 (2, 5, 5) = 0 := by
  rw [tr_s255, v5_s025, v5_s125, v5_s225]

theorem v6_s256 : N 6 (2, 5, 6) = 0 := by
  rw [tr_s256, v5_s125]

theorem v6_s257 : N 6 (2, 5, 7) = 0 := by
  rw [tr_s257, v5_s025, v5_s125, v5_s225]

theorem v6_s258 : N 6 (2, 5, 8) = 0 := by
  rw [tr_s258]

theorem v6_s266 : N 6 (2, 6, 6) = 0 := by
  rw [tr_s266, v5_s026, v5_s126, v5_s226]

theorem v6_s267 : N 6 (2, 6, 7) = 0 := by
  rw [tr_s267, v5_s126]

theorem v6_s268 : N 6 (2, 6, 8) = 0 := by
  rw [tr_s268, v5_s026, v5_s126, v5_s226]

theorem v6_s277 : N 6 (2, 7, 7) = 0 := by
  rw [tr_s277, v5_s027, v5_s127, v5_s227]

theorem v6_s278 : N 6 (2, 7, 8) = 0 := by
  rw [tr_s278, v5_s127]

theorem v6_s288 : N 6 (2, 8, 8) = 0 := by
  rw [tr_s288, v5_s028, v5_s128, v5_s228]

theorem v6_s333 : N 6 (3, 3, 3) = 18 := by
  rw [tr_s333, v5_s033, v5_s133, v5_s233, v5_s333]

theorem v6_s334 : N 6 (3, 3, 4) = 0 := by
  rw [tr_s334, v5_s133]

theorem v6_s335 : N 6 (3, 3, 5) = 4 := by
  rw [tr_s335, v5_s233]

theorem v6_s336 : N 6 (3, 3, 6) = 18 := by
  rw [tr_s336, v5_s033, v5_s133, v5_s233, v5_s333]

theorem v6_s337 : N 6 (3, 3, 7) = 0 := by
  rw [tr_s337]

theorem v6_s338 : N 6 (3, 3, 8) = 0 := by
  rw [tr_s338]

theorem v6_s344 : N 6 (3, 4, 4) = 4 := by
  rw [tr_s344, v5_s034, v5_s134, v5_s234, v5_s334]

theorem v6_s345 : N 6 (3, 4, 5) = 4 := by
  rw [tr_s345, v5_s134, v5_s234]

theorem v6_s346 : N 6 (3, 4, 6) = 4 := by
  rw [tr_s346, v5_s234, v5_s334]

theorem v6_s347 : N 6 (3, 4, 7) = 4 := by
  rw [tr_s347, v5_s034, v5_s134, v5_s234, v5_s334]

theorem v6_s348 : N 6 (3, 4, 8) = 0 := by
  rw [tr_s348]

theorem v6_s355 : N 6 (3, 5, 5) = 8 := by
  rw [tr_s355, v5_s035, v5_s135, v5_s235, v5_s335]

theorem v6_s356 : N 6 (3, 5, 6) = 4 := by
  rw [tr_s356, v5_s135, v5_s335]

theorem v6_s357 : N 6 (3, 5, 7) = 4 := by
  rw [tr_s357, v5_s235]

theorem v6_s358 : N 6 (3, 5, 8) = 8 := by
  rw [tr_s358, v5_s035, v5_s135, v5_s235, v5_s335]

theorem v6_s366 : N 6 (3, 6, 6) = 14 := by
  rw [tr_s366, v5_s036, v5_s136, v5_s236, v5_s336]

theorem v6_s367 : N 6 (3, 6, 7) = 0 := by
  rw [tr_s367, v5_s136]

theorem v6_s368 : N 6 (3, 6, 8) = 0 := by
  rw [tr_s368, v5_s236]

theorem v6_s377 : N 6 (3, 7, 7) = 0 := by
  rw [tr_s377, v5_s037, v5_s137, v5_s237, v5_s337]

theorem v6_s378 : N 6 (3, 7, 8) = 0 := by
  rw [tr_s378, v5_s137]

theorem v6_s388 : N 6 (3, 8, 8) = 0 := by
  rw [tr_s388, v5_s038, v5_s138, v5_s238, v5_s338]

theorem v6_s444 : N 6 (4, 4, 4) = 39 := by
  rw [tr_s444, v5_s044, v5_s144, v5_s244, v5_s344, v5_s444]

theorem v6_s445 : N 6 (4, 4, 5) = 0 := by
  rw [tr_s445, v5_s144]

theorem v6_s446 : N 6 (4, 4, 6) = 8 := by
  rw [tr_s446, v5_s244]

theorem v6_s447 : N 6 (4, 4, 7) = 4 := by
  rw [tr_s447, v5_s344]

theorem v6_s448 : N 6 (4, 4, 8) = 39 := by
  rw [tr_s448, v5_s044, v5_s144, v5_s244, v5_s344, v5_s444]

theorem v6_s455 : N 6 (4, 5, 5) = 4 := by
  rw [tr_s455, v5_s045, v5_s145, v5_s245, v5_s345, v5_s445]

theorem v6_s456 : N 6 (4, 5, 6) = 0 := by
  rw [tr_s456, v5_s145, v5_s245]

theorem v6_s457 : N 6 (4, 5, 7) = 4 := by
  rw [tr_s457, v5_s245, v5_s345]

theorem v6_s458 : N 6 (4, 5, 8) = 4 := by
  rw [tr_s458, v5_s345, v5_s445]

theorem v6_s466 : N 6 (4, 6, 6) = 18 := by
  rw [tr_s466, v5_s046, v5_s146, v5_s246, v5_s346, v5_s446]

theorem v6_s467 : N 6 (4, 6, 7) = 4 := by
  rw [tr_s467, v5_s146, v5_s346]

theorem v6_s468 : N 6 (4, 6, 8) = 14 := by
  rw [tr_s468, v5_s246, v5_s446]

theorem v6_s477 : N 6 (4, 7, 7) = 7 := by
  rw [tr_s477, v5_s047, v5_s147, v5_s247, v5_s347, v5_s447]

theorem v6_s478 : N 6 (4, 7, 8) = 3 := by
  rw [tr_s478, v5_s147, v5_s447]

theorem v6_s488 : N 6 (4, 8, 8) = 27 := by
  rw [tr_s488, v5_s048, v5_s148, v5_s248, v5_s348, v5_s448]

theorem v6_s555 : N 6 (5, 5, 5) = 33 := by
  rw [tr_s555, v5_s055, v5_s155, v5_s255, v5_s355, v5_s455, v5_s555]

theorem v6_s556 : N 6 (5, 5, 6) = 0 := by
  rw [tr_s556, v5_s155]

theorem v6_s557 : N 6 (5, 5, 7) = 0 := by
  rw [tr_s557, v5_s255]

theorem v6_s558 : N 6 (5, 5, 8) = 7 := by
  rw [tr_s558, v5_s355]

theorem v6_s566 : N 6 (5, 6, 6) = 3 := by
  rw [tr_s566, v5_s056, v5_s156, v5_s256, v5_s356, v5_s456, v5_s556]

theorem v6_s567 : N 6 (5, 6, 7) = 0 := by
  rw [tr_s567, v5_s156, v5_s256]

theorem v6_s568 : N 6 (5, 6, 8) = 3 := by
  rw [tr_s568, v5_s256, v5_s356]

theorem v6_s577 : N 6 (5, 7, 7) = 7 := by
  rw [tr_s577, v5_s057, v5_s157, v5_s257, v5_s357, v5_s457, v5_s557]

theorem v6_s578 : N 6 (5, 7, 8) = 4 := by
  rw [tr_s578, v5_s157, v5_s357]

theorem v6_s588 : N 6 (5, 8, 8) = 15 := by
  rw [tr_s588, v5_s058, v5_s158, v5_s258, v5_s358, v5_s458, v5_s558]

theorem v6_s666 : N 6 (6, 6, 6) = 72 := by
  rw [tr_s666, v5_s066, v5_s166, v5_s266, v5_s366, v5_s466, v5_s566, v5_s666]

theorem v6_s667 : N 6 (6, 6, 7) = 0 := by
  rw [tr_s667, v5_s166]

theorem v6_s668 : N 6 (6, 6, 8) = 0 := by
  rw [tr_s668, v5_s266]

theorem v6_s677 : N 6 (6, 7, 7) = 3 := by
  rw [tr_s677, v5_s067, v5_s167, v5_s267, v5_s367, v5_s467, v5_s567, v5_s667]

theorem v6_s678 : N 6 (6, 7, 8) = 0 := by
  rw [tr_s678, v5_s167, v5_s267]

theorem v6_s688 : N 6 (6, 8, 8) = 12 := by
  rw [tr_s688, v5_s068, v5_s168, v5_s268, v5_s368, v5_s468, v5_s568, v5_s668]

theorem v6_s777 : N 6 (7, 7, 7) = 43 := by
  rw [tr_s777, v5_s077, v5_s177, v5_s277, v5_s377, v5_s477, v5_s577, v5_s677, v5_s777]

theorem v6_s778 : N 6 (7, 7, 8) = 0 := by
  rw [tr_s778, v5_s177]

theorem v6_s788 : N 6 (7, 8, 8) = 5 := by
  rw [tr_s788, v5_s078, v5_s178, v5_s278, v5_s378, v5_s478, v5_s578, v5_s678, v5_s778]

theorem v6_s888 : N 6 (8, 8, 8) = 105 := by
  rw [tr_s888, v5_s088, v5_s188, v5_s288, v5_s388, v5_s488, v5_s588, v5_s688, v5_s788, v5_s888]

theorem v7_s000 : N 7 (0, 0, 0) = 1 := by
  rw [tr_s000, v6_s000]

theorem v7_s001 : N 7 (0, 0, 1) = 0 := by
  rw [tr_s001]

theorem v7_s002 : N 7 (0, 0, 2) = 0 := by
  rw [tr_s002]

theorem v7_s003 : N 7 (0, 0, 3) = 0 := by
  rw [tr_s003]

theorem v7_s004 : N 7 (0, 0, 4) = 0 := by
  rw [tr_s004]

theorem v7_s005 : N 7 (0, 0, 5) = 0 := by
  rw [tr_s005]

theorem v7_s006 : N 7 (0, 0, 6) = 0 := by
  rw [tr_s006]

theorem v7_s007 : N 7 (0, 0, 7) = 0 := by
  rw [tr_s007]

theorem v7_s008 : N 7 (0, 0, 8) = 0 := by
  rw [tr_s008]

theorem v7_s011 : N 7 (0, 1, 1) = 0 := by
  rw [tr_s011, v6_s001]

theorem v7_s012 : N 7 (0, 1, 2) = 0 := by
  rw [tr_s012]

theorem v7_s013 : N 7 (0, 1, 3) = 0 := by
  rw [tr_s013]

theorem v7_s014 : N 7 (0, 1, 4) = 0 := by
  rw [tr_s014]

theorem v7_s015 : N 7 (0, 1, 5) = 0 := by
  rw [tr_s015]

theorem v7_s016 : N 7 (0, 1, 6) = 0 := by
  rw [tr_s016]

theorem v7_s017 : N 7 (0, 1, 7) = 0 := by
  rw [tr_s017]

theorem v7_s018 : N 7 (0, 1, 8) = 0 := by
  rw [tr_s018]

theorem v7_s022 : N 7 (0, 2, 2) = 0 := by
  rw [tr_s022, v6_s002]

theorem v7_s023 : N 7 (0, 2, 3) = 0 := by
  rw [tr_s023]

theorem v7_s024 : N 7 (0, 2, 4) = 0 := by
  rw [tr_s024]

theorem v7_s025 : N 7 (0, 2, 5) = 0 := by
  rw [tr_s025]

theorem v7_s026 : N 7 (0, 2, 6) = 0 := by
  rw [tr_s026]

theorem v7_s027 : N 7 (0, 2, 7) = 0 := by
  rw [tr_s027]

theorem v7_s028 : N 7 (0, 2, 8) = 0 := by
  rw [tr_s028]

theorem v7_s033 : N 7 (0, 3, 3) = 0 := by
  rw [tr_s033, v6_s003]

theorem v7_s034 : N 7 (0, 3, 4) = 0 := by
  rw [tr_s034]

theorem v7_s035 : N 7 (0, 3, 5) = 0 := by
  rw [tr_s035]

theorem v7_s036 : N 7 (0, 3, 6) = 0 := by
  rw [tr_s036]

theorem v7_s037 : N 7 (0, 3, 7) = 0 := by
  rw [tr_s037]

theorem v7_s038 : N 7 (0, 3, 8) = 0 := by
  rw [tr_s038]

theorem v7_s044 : N 7 (0, 4, 4) = 0 := by
  rw [tr_s044, v6_s004]

theorem v7_s045 : N 7 (0, 4, 5) = 0 := by
  rw [tr_s045]

theorem v7_s046 : N 7 (0, 4, 6) = 0 := by
  rw [tr_s046]

theorem v7_s047 : N 7 (0, 4, 7) = 0 := by
  rw [tr_s047]

theorem v7_s048 : N 7 (0, 4, 8) = 0 := by
  rw [tr_s048]

theorem v7_s055 : N 7 (0, 5, 5) = 0 := by
  rw [tr_s055, v6_s005]

theorem v7_s056 : N 7 (0, 5, 6) = 0 := by
  rw [tr_s056]

theorem v7_s057 : N 7 (0, 5, 7) = 0 := by
  rw [tr_s057]

theorem v7_s058 : N 7 (0, 5, 8) = 0 := by
  rw [tr_s058]

theorem v7_s066 : N 7 (0, 6, 6) = 0 := by
  rw [tr_s066, v6_s006]

theorem v7_s067 : N 7 (0, 6, 7) = 0 := by
  rw [tr_s067]

theorem v7_s068 : N 7 (0, 6, 8) = 0 := by
  rw [tr_s068]

theorem v7_s077 : N 7 (0, 7, 7) = 0 := by
  rw [tr_s077, v6_s007]

theorem v7_s078 : N 7 (0, 7, 8) = 0 := by
  rw [tr_s078]

theorem v7_s088 : N 7 (0, 8, 8) = 0 := by
  rw [tr_s088, v6_s008]

theorem v7_s111 : N 7 (1, 1, 1) = 2 := by
  rw [tr_s111, v6_s011, v6_s111]

theorem v7_s112 : N 7 (1, 1, 2) = 2 := by
  rw [tr_s112, v6_s011, v6_s111]

theorem v7_s113 : N 7 (1, 1, 3) = 0 := by
  rw [tr_s113]

theorem v7_s114 : N 7 (1, 1, 4) = 0 := by
  rw [tr_s114]

theorem v7_s115 : N 7 (1, 1, 5) = 0 := by
  rw [tr_s115]

theorem v7_s116 : N 7 (1, 1, 6) = 0 := by
  rw [tr_s116]

theorem v7_s117 : N 7 (1, 1, 7) = 0 := by
  rw [tr_s117]

theorem v7_s118 : N 7 (1, 1, 8) = 0 := by
  rw [tr_s118]

theorem v7_s122 : N 7 (1, 2, 2) = 2 := by
  rw [tr_s122, v6_s012, v6_s112]

theorem v7_s123 : N 7 (1, 2, 3) = 2 := by
  rw [tr_s123, v6_s012, v6_s112]

theorem v7_s124 : N 7 (1, 2, 4) = 0 := by
  rw [tr_s124]

theorem v7_s125 : N 7 (1, 2, 5) = 0 := by
  rw [tr_s125]

theorem v7_s126 : N 7 (1, 2, 6) = 0 := by
  rw [tr_s126]

theorem v7_s127 : N 7 (1, 2, 7) = 0 := by
  rw [tr_s127]

theorem v7_s128 : N 7 (1, 2, 8) = 0 := by
  rw [tr_s128]

theorem v7_s133 : N 7 (1, 3, 3) = 0 := by
  rw [tr_s133, v6_s013, v6_s113]

theorem v7_s134 : N 7 (1, 3, 4) = 0 := by
  rw [tr_s134, v6_s013, v6_s113]

theorem v7_s135 : N 7 (1, 3, 5) = 0 := by
  rw [tr_s135]

theorem v7_s136 : N 7 (1, 3, 6) = 0 := by
  rw [tr_s136]

theorem v7_s137 : N 7 (1, 3, 7) = 0 := by
  rw [tr_s137]

theorem v7_s138 : N 7 (1, 3, 8) = 0 := by
  rw [tr_s138]

theorem v7_s144 : N 7 (1, 4, 4) = 0 := by
  rw [tr_s144, v6_s014, v6_s114]

theorem v7_s145 : N 7 (1, 4, 5) = 0 := by
  rw [tr_s145, v6_s014, v6_s114]

theorem v7_s146 : N 7 (1, 4, 6) = 0 := by
  rw [tr_s146]

theorem v7_s147 : N 7 (1, 4, 7) = 0 := by
  rw [tr_s147]

theorem v7_s148 : N 7 (1, 4, 8) = 0 := by
  rw [tr_s148]

theorem v7_s155 : N 7 (1, 5, 5) = 0 := by
  rw [tr_s155, v6_s015, v6_s115]

theorem v7_s156 : N 7 (1, 5, 6) = 0 := by
  rw [tr_s156, v6_s015, v6_s115]

theorem v7_s157 : N 7 (1, 5, 7) = 0 := by
  rw [tr_s157]

theorem v7_s158 : N 7 (1, 5, 8) = 0 := by
  rw [tr_s158]

theorem v7_s166 : N 7 (1, 6, 6) = 0 := by
  rw [tr_s166, v6_s016, v6_s116]

theorem v7_s167 : N 7 (1, 6, 7) = 0 := by
  rw [tr_s167, v6_s016, v6_s116]

theorem v7_s168 : N 7 (1, 6, 8) = 0 := by
  rw [tr_s168]

theorem v7_s177 : N 7 (1, 7, 7) = 0 := by
  rw [tr_s177, v6_s017, v6_s117]

theorem v7_s178 : N 7 (1, 7, 8) = 0 := by
  rw [tr_s178, v6_s017, v6_s117]

theorem v7_s188 : N 7 (1, 8, 8) = 0 := by
  rw [tr_s188, v6_s018, v6_s118]

theorem v7_s222 : N 7 (2, 2, 2) = 14 := by
  rw [tr_s222, v6_s022, v6_s122, v6_s222]

theorem v7_s223 : N 7 (2, 2, 3) = 2 := by
  rw [tr_s223, v6_s122]

theorem v7_s224 : N 7 (2, 2, 4) = 14 := by
  rw [tr_s224, v6_s022, v6_s122, v6_s222]

theorem v7_s225 : N 7 (2, 2, 5) = 0 := by
  rw [tr_s225]

theorem v7_s226 : N 7 (2, 2, 6) = 0 := by
  rw [tr_s226]

theorem v7_s227 : N 7 (2, 2, 7) = 0 := by
  rw [tr_s227]

theorem v7_s228 : N 7 (2, 2, 8) = 0 := by
  rw [tr_s228]

theorem v7_s233 : N 7 (2, 3, 3) = 4 := by
  rw [tr_s233, v6_s023, v6_s123, v6_s223]

theorem v7_s234 : N 7 (2, 3, 4) = 4 := by
  rw [tr_s234, v6_s123, v6_s223]

theorem v7_s235 : N 7 (2, 3, 5) = 4 := by
  rw [tr_s235, v6_s023, v6_s123, v6_s223]

theorem v7_s236 : N 7 (2, 3, 6) = 0 := by
  rw [tr_s236]

theorem v7_s237 : N 7 (2, 3, 7) = 0 := by
  rw [tr_s237]

theorem v7_s238 : N 7 (2, 3, 8) = 0 := by
  rw [tr_s238]

theorem v7_s244 : N 7 (2, 4, 4) = 12 := by
  rw [tr_s244, v6_s024, v6_s124, v6_s224]

theorem v7_s245 : N 7 (2, 4, 5) = 0 := by
  rw [tr_s245, v6_s124]

theorem v7_s246 : N 7 (2, 4, 6) = 12 := by
  rw [tr_s246, v6_s024, v6_s124, v6_s224]

theorem v7_s247 : N 7 (2, 4, 7) = 0 := by
  rw [tr_s247]

theorem v7_s248 : N 7 (2, 4, 8) = 0 := by
  rw [tr_s248]

theorem v7_s255 : N 7 (2, 5, 5) = 0 := by
  rw [tr_s255, v6_s025, v6_s125, v6_s225]

theorem v7_s256 : N 7 (2, 5, 6) = 0 := by
  rw [tr_s256, v6_s125]

theorem v7_s257 : N 7 (2, 5, 7) = 0 := by
  rw [tr_s257, v6_s025, v6_s125, v6_s225]

theorem v7_s258 : N 7 (2, 5, 8) = 0 := by
  rw [tr_s258]

theorem v7_s266 : N 7 (2, 6, 6) = 0 := by
  rw [tr_s266, v6_s026, v6_s126, v6_s226]

theorem v7_s267 : N 7 (2, 6, 7) = 0 := by
  rw [tr_s267, v6_s126]

theorem v7_s268 : N 7 (2, 6, 8) = 0 := by
  rw [tr_s268, v6_s026, v6_s126, v6_s226]

theorem v7_s277 : N 7 (2, 7, 7) = 0 := by
  rw [tr_s277, v6_s027, v6_s127, v6_s227]

theorem v7_s278 : N 7 (2, 7, 8) = 0 := by
  rw [tr_s278, v6_s127]

theorem v7_s288 : N 7 (2, 8, 8) = 0 := by
  rw [tr_s288, v6_s028, v6_s128, v6_s228]

theorem v7_s333 : N 7 (3, 3, 3) = 22 := by
  rw [tr_s333, v6_s033, v6_s133, v6_s233, v6_s333]

theorem v7_s334 : N 7 (3, 3, 4) = 0 := by
  rw [tr_s334, v6_s133]

theorem v7_s335 : N 7 (3, 3, 5) = 4 := by
  rw [tr_s335, v6_s233]

theorem v7_s336 : N 7 (3, 3, 6) = 22 := by
  rw [tr_s336, v6_s033, v6_s133, v6_s233, v6_s333]

theorem v7_s337 : N 7 (3, 3, 7) = 0 := by
  rw [tr_s337]

theorem v7_s338 : N 7 (3, 3, 8) = 0 := by
  rw [tr_s338]

theorem v7_s344 : N 7 (3, 4, 4) = 4 := by
  rw [tr_s344, v6_s034, v6_s134, v6_s234, v6_s334]

theorem v7_s345 : N 7 (3, 4, 5) = 4 := by
  rw [tr_s345, v6_s134, v6_s234]

theorem v7_s346 : N 7 (3, 4, 6) = 4 := by
  rw [tr_s346, v6_s234, v6_s334]

theorem v7_s347 : N 7 (3, 4, 7) = 4 := by
  rw [tr_s347, v6_s034, v6_s134, v6_s234, v6_s334]

theorem v7_s348 : N 7 (3, 4, 8) = 0 := by
  rw [tr_s348]

theorem v7_s355 : N 7 (3, 5, 5) = 8 := by
  rw [tr_s355, v6_s035, v6_s135, v6_s235, v6_s335]

theorem v7_s356 : N 7 (3, 5, 6) = 4 := by
  rw [tr_s356, v6_s135, v6_s335]

theorem v7_s357 : N 7 (3, 5, 7) = 4 := by
  rw [tr_s357, v6_s235]

theorem v7_s358 : N 7 (3, 5, 8) = 8 := by
  rw [tr_s358, v6_s035, v6_s135, v6_s235, v6_s335]

theorem v7_s366 : N 7 (3, 6, 6) = 18 := by
  rw [tr_s366, v6_s036, v6_s136, v6_s236, v6_s336]

theorem v7_s367 : N 7 (3, 6, 7) = 0 := by
  rw [tr_s367, v6_s136]

theorem v7_s368 : N 7 (3, 6, 8) = 0 := by
  rw [tr_s368, v6_s236]

theorem v7_s377 : N 7 (3, 7, 7) = 0 := by
  rw [tr_s377, v6_s037, v6_s137, v6_s237, v6_s337]

theorem v7_s378 : N 7 (3, 7, 8) = 0 := by
  rw [tr_s378, v6_s137]

theorem v7_s388 : N 7 (3, 8, 8) = 0 := by
  rw [tr_s388, v6_s038, v6_s138, v6_s238, v6_s338]

theorem v7_s444 : N 7 (4, 4, 4) = 53 := by
  rw [tr_s444, v6_s044, v6_s144, v6_s244, v6_s344, v6_s444]

theorem v7_s445 : N 7 (4, 4, 5) = 0 := by
  rw [tr_s445, v6_s144]

theorem v7_s446 : N 7 (4, 4, 6) = 10 := by
  rw [tr_s446, v6_s244]

theorem v7_s447 : N 7 (4, 4, 7) = 4 := by
  rw [tr_s447, v6_s344]

theorem v7_s448 : N 7 (4, 4, 8) = 53 := by
  rw [tr_s448, v6_s044, v6_s144, v6_s244, v6_s344, v6_s444]

theorem v7_s455 : N 7 (4, 5, 5) = 4 := by
  rw [tr_s455, v6_s045, v6_s145, v6_s245, v6_s345, v6_s445]

theorem v7_s456 : N 7 (4, 5, 6) = 0 := by
  rw [tr_s456, v6_s145, v6_s245]

theorem v7_s457 : N 7 (4, 5, 7) = 4 := by
  rw [tr_s457, v6_s245, v6_s345]

theorem v7_s458 : N 7 (4, 5, 8) = 4 := by
  rw [tr_s458, v6_s345, v6_s445]

theorem v7_s466 : N 7 (4, 6, 6) = 22 := by
  rw [tr_s466, v6_s046, v6_s146, v6_s246, v6_s346, v6_s446]

theorem v7_s467 : N 7 (4, 6, 7) = 4 := by
  rw [tr_s467, v6_s146, v6_s346]

theorem v7_s468 : N 7 (4, 6, 8) = 18 := by
  rw [tr_s468, v6_s246, v6_s446]

theorem v7_s477 : N 7 (4, 7, 7) = 8 := by
  rw [tr_s477, v6_s047, v6_s147, v6_s247, v6_s347, v6_s447]

theorem v7_s478 : N 7 (4, 7, 8) = 4 := by
  rw [tr_s478, v6_s147, v6_s447]

theorem v7_s488 : N 7 (4, 8, 8) = 39 := by
  rw [tr_s488, v6_s048, v6_s148, v6_s248, v6_s348, v6_s448]

theorem v7_s555 : N 7 (5, 5, 5) = 45 := by
  rw [tr_s555, v6_s055, v6_s155, v6_s255, v6_s355, v6_s455, v6_s555]

theorem v7_s556 : N 7 (5, 5, 6) = 0 := by
  rw [tr_s556, v6_s155]

theorem v7_s557 : N 7 (5, 5, 7) = 0 := by
  rw [tr_s557, v6_s255]

theorem v7_s558 : N 7 (5, 5, 8) = 8 := by
  rw [tr_s558, v6_s355]

theorem v7_s566 : N 7 (5, 6, 6) = 4 := by
  rw [tr_s566, v6_s056, v6_s156, v6_s256, v6_s356, v6_s456, v6_s556]

theorem v7_s567 : N 7 (5, 6, 7) = 0 := by
  rw [tr_s567, v6_s156, v6_s256]

theorem v7_s568 : N 7 (5, 6, 8) = 4 := by
  rw [tr_s568, v6_s256, v6_s356]

theorem v7_s577 : N 7 (5, 7, 7) = 8 := by
  rw [tr_s577, v6_s057, v6_s157, v6_s257, v6_s357, v6_s457, v6_s557]

theorem v7_s578 : N 7 (5, 7, 8) = 4 := by
  rw [tr_s578, v6_s157, v6_s357]

theorem v7_s588 : N 7 (5, 8, 8) = 19 := by
  rw [tr_s588, v6_s058, v6_s158, v6_s258, v6_s358, v6_s458, v6_s558]

theorem v7_s666 : N 7 (6, 6, 6) = 107 := by
  rw [tr_s666, v6_s066, v6_s166, v6_s266, v6_s366, v6_s466, v6_s566, v6_s666]

theorem v7_s667 : N 7 (6, 6, 7) = 0 := by
  rw [tr_s667, v6_s166]

theorem v7_s668 : N 7 (6, 6, 8) = 0 := by
  rw [tr_s668, v6_s266]

theorem v7_s677 : N 7 (6, 7, 7) = 4 := by
  rw [tr_s677, v6_s067, v6_s167, v6_s267, v6_s367, v6_s467, v6_s567, v6_s667]

theorem v7_s678 : N 7 (6, 7, 8) = 0 := by
  rw [tr_s678, v6_s167, v6_s267]

theorem v7_s688 : N 7 (6, 8, 8) = 17 := by
  rw [tr_s688, v6_s068, v6_s168, v6_s268, v6_s368, v6_s468, v6_s568, v6_s668]

theorem v7_s777 : N 7 (7, 7, 7) = 60 := by
  rw [tr_s777, v6_s077, v6_s177, v6_s277, v6_s377, v6_s477, v6_s577, v6_s677, v6_s777]

theorem v7_s778 : N 7 (7, 7, 8) = 0 := by
  rw [tr_s778, v6_s177]

theorem v7_s788 : N 7 (7, 8, 8) = 7 := by
  rw [tr_s788, v6_s078, v6_s178, v6_s278, v6_s378, v6_s478, v6_s578, v6_s678, v6_s778]

theorem v7_s888 : N 7 (8, 8, 8) = 164 := by
  rw [tr_s888, v6_s088, v6_s188, v6_s288, v6_s388, v6_s488, v6_s588, v6_s688, v6_s788, v6_s888]

theorem v8_s000 : N 8 (0, 0, 0) = 1 := by
  rw [tr_s000, v7_s000]

theorem v8_s001 : N 8 (0, 0, 1) = 0 := by
  rw [tr_s001]

theorem v8_s002 : N 8 (0, 0, 2) = 0 := by
  rw [tr_s002]

theorem v8_s003 : N 8 (0, 0, 3) = 0 := by
  rw [tr_s003]

theorem v8_s004 : N 8 (0, 0, 4) = 0 := by
  rw [tr_s004]

theorem v8_s005 : N 8 (0, 0, 5) = 0 := by
  rw [tr_s005]

theorem v8_s006 : N 8 (0, 0, 6) = 0 := by
  rw [tr_s006]

theorem v8_s007 : N 8 (0, 0, 7) = 0 := by
  rw [tr_s007]

theorem v8_s008 : N 8 (0, 0, 8) = 0 := by
  rw [tr_s008]

theorem v8_s011 : N 8 (0, 1, 1) = 0 := by
  rw [tr_s011, v7_s001]

theorem v8_s012 : N 8 (0, 1, 2) = 0 := by
  rw [tr_s012]

theorem v8_s013 : N 8 (0, 1, 3) = 0 := by
  rw [tr_s013]

theorem v8_s014 : N 8 (0, 1, 4) = 0 := by
  rw [tr_s014]

theorem v8_s015 : N 8 (0, 1, 5) = 0 := by
  rw [tr_s015]

theorem v8_s016 : N 8 (0, 1, 6) = 0 := by
  rw [tr_s016]

theorem v8_s017 : N 8 (0, 1, 7) = 0 := by
  rw [tr_s017]

theorem v8_s018 : N 8 (0, 1, 8) = 0 := by
  rw [tr_s018]

theorem v8_s022 : N 8 (0, 2, 2) = 0 := by
  rw [tr_s022, v7_s002]

theorem v8_s023 : N 8 (0, 2, 3) = 0 := by
  rw [tr_s023]

theorem v8_s024 : N 8 (0, 2, 4) = 0 := by
  rw [tr_s024]

theorem v8_s025 : N 8 (0, 2, 5) = 0 := by
  rw [tr_s025]

theorem v8_s026 : N 8 (0, 2, 6) = 0 := by
  rw [tr_s026]

theorem v8_s027 : N 8 (0, 2, 7) = 0 := by
  rw [tr_s027]

theorem v8_s028 : N 8 (0, 2, 8) = 0 := by
  rw [tr_s028]

theorem v8_s033 : N 8 (0, 3, 3) = 0 := by
  rw [tr_s033, v7_s003]

theorem v8_s034 : N 8 (0, 3, 4) = 0 := by
  rw [tr_s034]

theorem v8_s035 : N 8 (0, 3, 5) = 0 := by
  rw [tr_s035]

theorem v8_s036 : N 8 (0, 3, 6) = 0 := by
  rw [tr_s036]

theorem v8_s037 : N 8 (0, 3, 7) = 0 := by
  rw [tr_s037]

theorem v8_s038 : N 8 (0, 3, 8) = 0 := by
  rw [tr_s038]

theorem v8_s044 : N 8 (0, 4, 4) = 0 := by
  rw [tr_s044, v7_s004]

theorem v8_s045 : N 8 (0, 4, 5) = 0 := by
  rw [tr_s045]

theorem v8_s046 : N 8 (0, 4, 6) = 0 := by
  rw [tr_s046]

theorem v8_s047 : N 8 (0, 4, 7) = 0 := by
  rw [tr_s047]

theorem v8_s048 : N 8 (0, 4, 8) = 0 := by
  rw [tr_s048]

theorem v8_s055 : N 8 (0, 5, 5) = 0 := by
  rw [tr_s055, v7_s005]

theorem v8_s056 : N 8 (0, 5, 6) = 0 := by
  rw [tr_s056]

theorem v8_s057 : N 8 (0, 5, 7) = 0 := by
  rw [tr_s057]

theorem v8_s058 : N 8 (0, 5, 8) = 0 := by
  rw [tr_s058]

theorem v8_s066 : N 8 (0, 6, 6) = 0 := by
  rw [tr_s066, v7_s006]

theorem v8_s067 : N 8 (0, 6, 7) = 0 := by
  rw [tr_s067]

theorem v8_s068 : N 8 (0, 6, 8) = 0 := by
  rw [tr_s068]

theorem v8_s077 : N 8 (0, 7, 7) = 0 := by
  rw [tr_s077, v7_s007]

theorem v8_s078 : N 8 (0, 7, 8) = 0 := by
  rw [tr_s078]

theorem v8_s088 : N 8 (0, 8, 8) = 0 := by
  rw [tr_s088, v7_s008]

theorem v8_s111 : N 8 (1, 1, 1) = 2 := by
  rw [tr_s111, v7_s011, v7_s111]

theorem v8_s112 : N 8 (1, 1, 2) = 2 := by
  rw [tr_s112, v7_s011, v7_s111]

theorem v8_s113 : N 8 (1, 1, 3) = 0 := by
  rw [tr_s113]

theorem v8_s114 : N 8 (1, 1, 4) = 0 := by
  rw [tr_s114]

theorem v8_s115 : N 8 (1, 1, 5) = 0 := by
  rw [tr_s115]

theorem v8_s116 : N 8 (1, 1, 6) = 0 := by
  rw [tr_s116]

theorem v8_s117 : N 8 (1, 1, 7) = 0 := by
  rw [tr_s117]

theorem v8_s118 : N 8 (1, 1, 8) = 0 := by
  rw [tr_s118]

theorem v8_s122 : N 8 (1, 2, 2) = 2 := by
  rw [tr_s122, v7_s012, v7_s112]

theorem v8_s123 : N 8 (1, 2, 3) = 2 := by
  rw [tr_s123, v7_s012, v7_s112]

theorem v8_s124 : N 8 (1, 2, 4) = 0 := by
  rw [tr_s124]

theorem v8_s125 : N 8 (1, 2, 5) = 0 := by
  rw [tr_s125]

theorem v8_s126 : N 8 (1, 2, 6) = 0 := by
  rw [tr_s126]

theorem v8_s127 : N 8 (1, 2, 7) = 0 := by
  rw [tr_s127]

theorem v8_s128 : N 8 (1, 2, 8) = 0 := by
  rw [tr_s128]

theorem v8_s133 : N 8 (1, 3, 3) = 0 := by
  rw [tr_s133, v7_s013, v7_s113]

theorem v8_s134 : N 8 (1, 3, 4) = 0 := by
  rw [tr_s134, v7_s013, v7_s113]

theorem v8_s135 : N 8 (1, 3, 5) = 0 := by
  rw [tr_s135]

theorem v8_s136 : N 8 (1, 3, 6) = 0 := by
  rw [tr_s136]

theorem v8_s137 : N 8 (1, 3, 7) = 0 := by
  rw [tr_s137]

theorem v8_s138 : N 8 (1, 3, 8) = 0 := by
  rw [tr_s138]

theorem v8_s144 : N 8 (1, 4, 4) = 0 := by
  rw [tr_s144, v7_s014, v7_s114]

theorem v8_s145 : N 8 (1, 4, 5) = 0 := by
  rw [tr_s145, v7_s014, v7_s114]

theorem v8_s146 : N 8 (1, 4, 6) = 0 := by
  rw [tr_s146]

theorem v8_s147 : N 8 (1, 4, 7) = 0 := by
  rw [tr_s147]

theorem v8_s148 : N 8 (1, 4, 8) = 0 := by
  rw [tr_s148]

theorem v8_s155 : N 8 (1, 5, 5) = 0 := by
  rw [tr_s155, v7_s015, v7_s115]

theorem v8_s156 : N 8 (1, 5, 6) = 0 := by
  rw [tr_s156, v7_s015, v7_s115]

theorem v8_s157 : N 8 (1, 5, 7) = 0 := by
  rw [tr_s157]

theorem v8_s158 : N 8 (1, 5, 8) = 0 := by
  rw [tr_s158]

theorem v8_s166 : N 8 (1, 6, 6) = 0 := by
  rw [tr_s166, v7_s016, v7_s116]

theorem v8_s167 : N 8 (1, 6, 7) = 0 := by
  rw [tr_s167, v7_s016, v7_s116]

theorem v8_s168 : N 8 (1, 6, 8) = 0 := by
  rw [tr_s168]

theorem v8_s177 : N 8 (1, 7, 7) = 0 := by
  rw [tr_s177, v7_s017, v7_s117]

theorem v8_s178 : N 8 (1, 7, 8) = 0 := by
  rw [tr_s178, v7_s017, v7_s117]

theorem v8_s188 : N 8 (1, 8, 8) = 0 := by
  rw [tr_s188, v7_s018, v7_s118]

theorem v8_s222 : N 8 (2, 2, 2) = 16 := by
  rw [tr_s222, v7_s022, v7_s122, v7_s222]

theorem v8_s223 : N 8 (2, 2, 3) = 2 := by
  rw [tr_s223, v7_s122]

theorem v8_s224 : N 8 (2, 2, 4) = 16 := by
  rw [tr_s224, v7_s022, v7_s122, v7_s222]

theorem v8_s225 : N 8 (2, 2, 5) = 0 := by
  rw [tr_s225]

theorem v8_s226 : N 8 (2, 2, 6) = 0 := by
  rw [tr_s226]

theorem v8_s227 : N 8 (2, 2, 7) = 0 := by
  rw [tr_s227]

theorem v8_s228 : N 8 (2, 2, 8) = 0 := by
  rw [tr_s228]

theorem v8_s233 : N 8 (2, 3, 3) = 4 := by
  rw [tr_s233, v7_s023, v7_s123, v7_s223]

theorem v8_s234 : N 8 (2, 3, 4) = 4 := by
  rw [tr_s234, v7_s123, v7_s223]

theorem v8_s235 : N 8 (2, 3, 5) = 4 := by
  rw [tr_s235, v7_s023, v7_s123, v7_s223]

theorem v8_s236 : N 8 (2, 3, 6) = 0 := by
  rw [tr_s236]

theorem v8_s237 : N 8 (2, 3, 7) = 0 := by
  rw [tr_s237]

theorem v8_s238 : N 8 (2, 3, 8) = 0 := by
  rw [tr_s238]

theorem v8_s244 : N 8 (2, 4, 4) = 14 := by
  rw [tr_s244, v7_s024, v7_s124, v7_s224]

theorem v8_s245 : N 8 (2, 4, 5) = 0 := by
  rw [tr_s245, v7_s124]

theorem v8_s246 : N 8 (2, 4, 6) = 14 := by
  rw [tr_s246, v7_s024, v7_s124, v7_s224]

theorem v8_s247 : N 8 (2, 4, 7) = 0 := by
  rw [tr_s247]

theorem v8_s248 : N 8 (2, 4, 8) = 0 := by
  rw [tr_s248]

theorem v8_s255 : N 8 (2, 5, 5) = 0 := by
  rw [tr_s255, v7_s025, v7_s125, v7_s225]

theorem v8_s256 : N 8 (2, 5, 6) = 0 := by
  rw [tr_s256, v7_s125]

theorem v8_s257 : N 8 (2, 5, 7) = 0 := by
  rw [tr_s257, v7_s025, v7_s125, v7_s225]

theorem v8_s258 : N 8 (2, 5, 8) = 0 := by
  rw [tr_s258]

theorem v8_s266 : N 8 (2, 6, 6) = 0 := by
  rw [tr_s266, v7_s026, v7_s126, v7_s226]

theorem v8_s267 : N 8 (2, 6, 7) = 0 := by
  rw [tr_s267, v7_s126]

theorem v8_s268 : N 8 (2, 6, 8) = 0 := by
  rw [tr_s268, v7_s026, v7_s126, v7_s226]

theorem v8_s277 : N 8 (2, 7, 7) = 0 := by
  rw [tr_s277, v7_s027, v7_s127, v7_s227]

theorem v8_s278 : N 8 (2, 7, 8) = 0 := by
  rw [tr_s278, v7_s127]

theorem v8_s288 : N 8 (2, 8, 8) = 0 := by
  rw [tr_s288, v7_s028, v7_s128, v7_s228]

theorem v8_s333 : N 8 (3, 3, 3) = 26 := by
  rw [tr_s333, v7_s033, v7_s133, v7_s233, v7_s333]

theorem v8_s334 : N 8 (3, 3, 4) = 0 := by
  rw [tr_s334, v7_s133]

theorem v8_s335 : N 8 (3, 3, 5) = 4 := by
  rw [tr_s335, v7_s233]

theorem v8_s336 : N 8 (3, 3, 6) = 26 := by
  rw [tr_s336, v7_s033, v7_s133, v7_s233, v7_s333]

theorem v8_s337 : N 8 (3, 3, 7) = 0 := by
  rw [tr_s337]

theorem v8_s338 : N 8 (3, 3, 8) = 0 := by
  rw [tr_s338]

theorem v8_s344 : N 8 (3, 4, 4) = 4 := by
  rw [tr_s344, v7_s034, v7_s134, v7_s234, v7_s334]

theorem v8_s345 : N 8 (3, 4, 5) = 4 := by
  rw [tr_s345, v7_s134, v7_s234]

theorem v8_s346 : N 8 (3, 4, 6) = 4 := by
  rw [tr_s346, v7_s234, v7_s334]

theorem v8_s347 : N 8 (3, 4, 7) = 4 := by
  rw [tr_s347, v7_s034, v7_s134, v7_s234, v7_s334]

theorem v8_s348 : N 8 (3, 4, 8) = 0 := by
  rw [tr_s348]

theorem v8_s355 : N 8 (3, 5, 5) = 8 := by
  rw [tr_s355, v7_s035, v7_s135, v7_s235, v7_s335]

theorem v8_s356 : N 8 (3, 5, 6) = 4 := by
  rw [tr_s356, v7_s135, v7_s335]

theorem v8_s357 : N 8 (3, 5, 7) = 4 := by
  rw [tr_s357, v7_s235]

theorem v8_s358 : N 8 (3, 5, 8) = 8 := by
  rw [tr_s358, v7_s035, v7_s135, v7_s235, v7_s335]

theorem v8_s366 : N 8 (3, 6, 6) = 22 := by
  rw [tr_s366, v7_s036, v7_s136, v7_s236, v7_s336]

theorem v8_s367 : N 8 (3, 6, 7) = 0 := by
  rw [tr_s367, v7_s136]

theorem v8_s368 : N 8 (3, 6, 8) = 0 := by
  rw [tr_s368, v7_s236]

theorem v8_s377 : N 8 (3, 7, 7) = 0 := by
  rw [tr_s377, v7_s037, v7_s137, v7_s237, v7_s337]

theorem v8_s378 : N 8 (3, 7, 8) = 0 := by
  rw [tr_s378, v7_s137]

theorem v8_s388 : N 8 (3, 8, 8) = 0 := by
  rw [tr_s388, v7_s038, v7_s138, v7_s238, v7_s338]

theorem v8_s444 : N 8 (4, 4, 4) = 69 := by
  rw [tr_s444, v7_s044, v7_s144, v7_s244, v7_s344, v7_s444]

theorem v8_s445 : N 8 (4, 4, 5) = 0 := by
  rw [tr_s445, v7_s144]

theorem v8_s446 : N 8 (4, 4, 6) = 12 := by
  rw [tr_s446, v7_s244]

theorem v8_s447 : N 8 (4, 4, 7) = 4 := by
  rw [tr_s447, v7_s344]

theorem v8_s448 : N 8 (4, 4, 8) = 69 := by
  rw [tr_s448, v7_s044, v7_s144, v7_s244, v7_s344, v7_s444]

theorem v8_s455 : N 8 (4, 5, 5) = 4 := by
  rw [tr_s455, v7_s045, v7_s145, v7_s245, v7_s345, v7_s445]

theorem v8_s456 : N 8 (4, 5, 6) = 0 := by
  rw [tr_s456, v7_s145, v7_s245]

theorem v8_s457 : N 8 (4, 5, 7) = 4 := by
  rw [tr_s457, v7_s245, v7_s345]

theorem v8_s458 : N 8 (4, 5, 8) = 4 := by
  rw [tr_s458, v7_s345, v7_s445]

theorem v8_s466 : N 8 (4, 6, 6) = 26 := by
  rw [tr_s466, v7_s046, v7_s146, v7_s246, v7_s346, v7_s446]

theorem v8_s467 : N 8 (4, 6, 7) = 4 := by
  rw [tr_s467, v7_s146, v7_s346]

theorem v8_s468 : N 8 (4, 6, 8) = 22 := by
  rw [tr_s468, v7_s246, v7_s446]

theorem v8_s477 : N 8 (4, 7, 7) = 8 := by
  rw [tr_s477, v7_s047, v7_s147, v7_s247, v7_s347, v7_s447]

theorem v8_s478 : N 8 (4, 7, 8) = 4 := by
  rw [tr_s478, v7_s147, v7_s447]

theorem v8_s488 : N 8 (4, 8, 8) = 53 := by
  rw [tr_s488, v7_s048, v7_s148, v7_s248, v7_s348, v7_s448]

theorem v8_s555 : N 8 (5, 5, 5) = 57 := by
  rw [tr_s555, v7_s055, v7_s155, v7_s255, v7_s355, v7_s455, v7_s555]

theorem v8_s556 : N 8 (5, 5, 6) = 0 := by
  rw [tr_s556, v7_s155]

theorem v8_s557 : N 8 (5, 5, 7) = 0 := by
  rw [tr_s557, v7_s255]

theorem v8_s558 : N 8 (5, 5, 8) = 8 := by
  rw [tr_s558, v7_s355]

theorem v8_s566 : N 8 (5, 6, 6) = 4 := by
  rw [tr_s566, v7_s056, v7_s156, v7_s256, v7_s356, v7_s456, v7_s556]

theorem v8_s567 : N 8 (5, 6, 7) = 0 := by
  rw [tr_s567, v7_s156, v7_s256]

theorem v8_s568 : N 8 (5, 6, 8) = 4 := by
  rw [tr_s568, v7_s256, v7_s356]

theorem v8_s577 : N 8 (5, 7, 7) = 8 := by
  rw [tr_s577, v7_s057, v7_s157, v7_s257, v7_s357, v7_s457, v7_s557]

theorem v8_s578 : N 8 (5, 7, 8) = 4 := by
  rw [tr_s578, v7_s157, v7_s357]

theorem v8_s588 : N 8 (5, 8, 8) = 20 := by
  rw [tr_s588, v7_s058, v7_s158, v7_s258, v7_s358, v7_s458, v7_s558]

theorem v8_s666 : N 8 (6, 6, 6) = 151 := by
  rw [tr_s666, v7_s066, v7_s166, v7_s266, v7_s366, v7_s466, v7_s566, v7_s666]

theorem v8_s667 : N 8 (6, 6, 7) = 0 := by
  rw [tr_s667, v7_s166]

theorem v8_s668 : N 8 (6, 6, 8) = 0 := by
  rw [tr_s668, v7_s266]

theorem v8_s677 : N 8 (6, 7, 7) = 4 := by
  rw [tr_s677, v7_s067, v7_s167, v7_s267, v7_s367, v7_s467, v7_s567, v7_s667]

theorem v8_s678 : N 8 (6, 7, 8) = 0 := by
  rw [tr_s678, v7_s167, v7_s267]

theorem v8_s688 : N 8 (6, 8, 8) = 22 := by
  rw [tr_s688, v7_s068, v7_s168, v7_s268, v7_s368, v7_s468, v7_s568, v7_s668]

theorem v8_s777 : N 8 (7, 7, 7) = 80 := by
  rw [tr_s777, v7_s077, v7_s177, v7_s277, v7_s377, v7_s477, v7_s577, v7_s677, v7_s777]

theorem v8_s778 : N 8 (7, 7, 8) = 0 := by
  rw [tr_s778, v7_s177]

theorem v8_s788 : N 8 (7, 8, 8) = 8 := by
  rw [tr_s788, v7_s078, v7_s178, v7_s278, v7_s378, v7_s478, v7_s578, v7_s678, v7_s778]

theorem v8_s888 : N 8 (8, 8, 8) = 246 := by
  rw [tr_s888, v7_s088, v7_s188, v7_s288, v7_s388, v7_s488, v7_s588, v7_s688, v7_s788, v7_s888]

theorem closed_all (m : ℕ) (hm : 8 ≤ m) :
    (N m (0, 0, 0) : ℚ) = (1 : ℚ) * 1 ∧
    (N m (0, 0, 1) : ℚ) = 0 ∧
    (N m (0, 0, 2) : ℚ) = 0 ∧
    (N m (0, 0, 3) : ℚ) = 0 ∧
    (N m (0, 0, 4) : ℚ) = 0 ∧
    (N m (0, 0, 5) : ℚ) = 0 ∧
    (N m (0, 0, 6) : ℚ) = 0 ∧
    (N m (0, 0, 7) : ℚ) = 0 ∧
    (N m (0, 0, 8) : ℚ) = 0 ∧
    (N m (0, 1, 1) : ℚ) = 0 ∧
    (N m (0, 1, 2) : ℚ) = 0 ∧
    (N m (0, 1, 3) : ℚ) = 0 ∧
    (N m (0, 1, 4) : ℚ) = 0 ∧
    (N m (0, 1, 5) : ℚ) = 0 ∧
    (N m (0, 1, 6) : ℚ) = 0 ∧
    (N m (0, 1, 7) : ℚ) = 0 ∧
    (N m (0, 1, 8) : ℚ) = 0 ∧
    (N m (0, 2, 2) : ℚ) = 0 ∧
    (N m (0, 2, 3) : ℚ) = 0 ∧
    (N m (0, 2, 4) : ℚ) = 0 ∧
    (N m (0, 2, 5) : ℚ) = 0 ∧
    (N m (0, 2, 6) : ℚ) = 0 ∧
    (N m (0, 2, 7) : ℚ) = 0 ∧
    (N m (0, 2, 8) : ℚ) = 0 ∧
    (N m (0, 3, 3) : ℚ) = 0 ∧
    (N m (0, 3, 4) : ℚ) = 0 ∧
    (N m (0, 3, 5) : ℚ) = 0 ∧
    (N m (0, 3, 6) : ℚ) = 0 ∧
    (N m (0, 3, 7) : ℚ) = 0 ∧
    (N m (0, 3, 8) : ℚ) = 0 ∧
    (N m (0, 4, 4) : ℚ) = 0 ∧
    (N m (0, 4, 5) : ℚ) = 0 ∧
    (N m (0, 4, 6) : ℚ) = 0 ∧
    (N m (0, 4, 7) : ℚ) = 0 ∧
    (N m (0, 4, 8) : ℚ) = 0 ∧
    (N m (0, 5, 5) : ℚ) = 0 ∧
    (N m (0, 5, 6) : ℚ) = 0 ∧
    (N m (0, 5, 7) : ℚ) = 0 ∧
    (N m (0, 5, 8) : ℚ) = 0 ∧
    (N m (0, 6, 6) : ℚ) = 0 ∧
    (N m (0, 6, 7) : ℚ) = 0 ∧
    (N m (0, 6, 8) : ℚ) = 0 ∧
    (N m (0, 7, 7) : ℚ) = 0 ∧
    (N m (0, 7, 8) : ℚ) = 0 ∧
    (N m (0, 8, 8) : ℚ) = 0 ∧
    (N m (1, 1, 1) : ℚ) = (2 : ℚ) * 1 ∧
    (N m (1, 1, 2) : ℚ) = (2 : ℚ) * 1 ∧
    (N m (1, 1, 3) : ℚ) = 0 ∧
    (N m (1, 1, 4) : ℚ) = 0 ∧
    (N m (1, 1, 5) : ℚ) = 0 ∧
    (N m (1, 1, 6) : ℚ) = 0 ∧
    (N m (1, 1, 7) : ℚ) = 0 ∧
    (N m (1, 1, 8) : ℚ) = 0 ∧
    (N m (1, 2, 2) : ℚ) = (2 : ℚ) * 1 ∧
    (N m (1, 2, 3) : ℚ) = (2 : ℚ) * 1 ∧
    (N m (1, 2, 4) : ℚ) = 0 ∧
    (N m (1, 2, 5) : ℚ) = 0 ∧
    (N m (1, 2, 6) : ℚ) = 0 ∧
    (N m (1, 2, 7) : ℚ) = 0 ∧
    (N m (1, 2, 8) : ℚ) = 0 ∧
    (N m (1, 3, 3) : ℚ) = 0 ∧
    (N m (1, 3, 4) : ℚ) = 0 ∧
    (N m (1, 3, 5) : ℚ) = 0 ∧
    (N m (1, 3, 6) : ℚ) = 0 ∧
    (N m (1, 3, 7) : ℚ) = 0 ∧
    (N m (1, 3, 8) : ℚ) = 0 ∧
    (N m (1, 4, 4) : ℚ) = 0 ∧
    (N m (1, 4, 5) : ℚ) = 0 ∧
    (N m (1, 4, 6) : ℚ) = 0 ∧
    (N m (1, 4, 7) : ℚ) = 0 ∧
    (N m (1, 4, 8) : ℚ) = 0 ∧
    (N m (1, 5, 5) : ℚ) = 0 ∧
    (N m (1, 5, 6) : ℚ) = 0 ∧
    (N m (1, 5, 7) : ℚ) = 0 ∧
    (N m (1, 5, 8) : ℚ) = 0 ∧
    (N m (1, 6, 6) : ℚ) = 0 ∧
    (N m (1, 6, 7) : ℚ) = 0 ∧
    (N m (1, 6, 8) : ℚ) = 0 ∧
    (N m (1, 7, 7) : ℚ) = 0 ∧
    (N m (1, 7, 8) : ℚ) = 0 ∧
    (N m (1, 8, 8) : ℚ) = 0 ∧
    (N m (2, 2, 2) : ℚ) = (2 : ℚ) * (m : ℚ) ∧
    (N m (2, 2, 3) : ℚ) = (2 : ℚ) * 1 ∧
    (N m (2, 2, 4) : ℚ) = (2 : ℚ) * (m : ℚ) ∧
    (N m (2, 2, 5) : ℚ) = 0 ∧
    (N m (2, 2, 6) : ℚ) = 0 ∧
    (N m (2, 2, 7) : ℚ) = 0 ∧
    (N m (2, 2, 8) : ℚ) = 0 ∧
    (N m (2, 3, 3) : ℚ) = (4 : ℚ) * 1 ∧
    (N m (2, 3, 4) : ℚ) = (4 : ℚ) * 1 ∧
    (N m (2, 3, 5) : ℚ) = (4 : ℚ) * 1 ∧
    (N m (2, 3, 6) : ℚ) = 0 ∧
    (N m (2, 3, 7) : ℚ) = 0 ∧
    (N m (2, 3, 8) : ℚ) = 0 ∧
    (N m (2, 4, 4) : ℚ) = (-2 : ℚ) * 1 + (2 : ℚ) * (m : ℚ) ∧
    (N m (2, 4, 5) : ℚ) = 0 ∧
    (N m (2, 4, 6) : ℚ) = (-2 : ℚ) * 1 + (2 : ℚ) * (m : ℚ) ∧
    (N m (2, 4, 7) : ℚ) = 0 ∧
    (N m (2, 4, 8) : ℚ) = 0 ∧
    (N m (2, 5, 5) : ℚ) = 0 ∧
    (N m (2, 5, 6) : ℚ) = 0 ∧
    (N m (2, 5, 7) : ℚ) = 0 ∧
    (N m (2, 5, 8) : ℚ) = 0 ∧
    (N m (2, 6, 6) : ℚ) = 0 ∧
    (N m (2, 6, 7) : ℚ) = 0 ∧
    (N m (2, 6, 8) : ℚ) = 0 ∧
    (N m (2, 7, 7) : ℚ) = 0 ∧
    (N m (2, 7, 8) : ℚ) = 0 ∧
    (N m (2, 8, 8) : ℚ) = 0 ∧
    (N m (3, 3, 3) : ℚ) = (-6 : ℚ) * 1 + (4 : ℚ) * (m : ℚ) ∧
    (N m (3, 3, 4) : ℚ) = 0 ∧
    (N m (3, 3, 5) : ℚ) = (4 : ℚ) * 1 ∧
    (N m (3, 3, 6) : ℚ) = (-6 : ℚ) * 1 + (4 : ℚ) * (m : ℚ) ∧
    (N m (3, 3, 7) : ℚ) = 0 ∧
    (N m (3, 3, 8) : ℚ) = 0 ∧
    (N m (3, 4, 4) : ℚ) = (4 : ℚ) * 1 ∧
    (N m (3, 4, 5) : ℚ) = (4 : ℚ) * 1 ∧
    (N m (3, 4, 6) : ℚ) = (4 : ℚ) * 1 ∧
    (N m (3, 4, 7) : ℚ) = (4 : ℚ) * 1 ∧
    (N m (3, 4, 8) : ℚ) = 0 ∧
    (N m (3, 5, 5) : ℚ) = (8 : ℚ) * 1 ∧
    (N m (3, 5, 6) : ℚ) = (4 : ℚ) * 1 ∧
    (N m (3, 5, 7) : ℚ) = (4 : ℚ) * 1 ∧
    (N m (3, 5, 8) : ℚ) = (8 : ℚ) * 1 ∧
    (N m (3, 6, 6) : ℚ) = (-10 : ℚ) * 1 + (4 : ℚ) * (m : ℚ) ∧
    (N m (3, 6, 7) : ℚ) = 0 ∧
    (N m (3, 6, 8) : ℚ) = 0 ∧
    (N m (3, 7, 7) : ℚ) = 0 ∧
    (N m (3, 7, 8) : ℚ) = 0 ∧
    (N m (3, 8, 8) : ℚ) = 0 ∧
    (N m (4, 4, 4) : ℚ) = (-3 : ℚ) * 1 + (1 : ℚ) * (m : ℚ) + (1 : ℚ) * (m : ℚ) ^ 2 ∧
    (N m (4, 4, 5) : ℚ) = 0 ∧
    (N m (4, 4, 6) : ℚ) = (-4 : ℚ) * 1 + (2 : ℚ) * (m : ℚ) ∧
    (N m (4, 4, 7) : ℚ) = (4 : ℚ) * 1 ∧
    (N m (4, 4, 8) : ℚ) = (-3 : ℚ) * 1 + (1 : ℚ) * (m : ℚ) + (1 : ℚ) * (m : ℚ) ^ 2 ∧
    (N m (4, 5, 5) : ℚ) = (4 : ℚ) * 1 ∧
    (N m (4, 5, 6) : ℚ) = 0 ∧
    (N m (4, 5, 7) : ℚ) = (4 : ℚ) * 1 ∧
    (N m (4, 5, 8) : ℚ) = (4 : ℚ) * 1 ∧
    (N m (4, 6, 6) : ℚ) = (-6 : ℚ) * 1 + (4 : ℚ) * (m : ℚ) ∧
    (N m (4, 6, 7) : ℚ) = (4 : ℚ) * 1 ∧
    (N m (4, 6, 8) : ℚ) = (-10 : ℚ) * 1 + (4 : ℚ) * (m : ℚ) ∧
    (N m (4, 7, 7) : ℚ) = (8 : ℚ) * 1 ∧
    (N m (4, 7, 8) : ℚ) = (4 : ℚ) * 1 ∧
    (N m (4, 8, 8) : ℚ) = (-3 : ℚ) * 1 + (-1 : ℚ) * (m : ℚ) + (1 : ℚ) * (m : ℚ) ^ 2 ∧
    (N m (5, 5, 5) : ℚ) = (-39 : ℚ) * 1 + (12 : ℚ) * (m : ℚ) ∧
    (N m (5, 5, 6) : ℚ) = 0 ∧
    (N m (5, 5, 7) : ℚ) = 0 ∧
    (N m (5, 5, 8) : ℚ) = (8 : ℚ) * 1 ∧
    (N m (5, 6, 6) : ℚ) = (4 : ℚ) * 1 ∧
    (N m (5, 6, 7) : ℚ) = 0 ∧
    (N m (5, 6, 8) : ℚ) = (4 : ℚ) * 1 ∧
    (N m (5, 7, 7) : ℚ) = (8 : ℚ) * 1 ∧
    (N m (5, 7, 8) : ℚ) = (4 : ℚ) * 1 ∧
    (N m (5, 8, 8) : ℚ) = (20 : ℚ) * 1 ∧
    (N m (6, 6, 6) : ℚ) = (23 : ℚ) * 1 + (-16 : ℚ) * (m : ℚ) + (4 : ℚ) * (m : ℚ) ^ 2 ∧
    (N m (6, 6, 7) : ℚ) = 0 ∧
    (N m (6, 6, 8) : ℚ) = 0 ∧
    (N m (6, 7, 7) : ℚ) = (4 : ℚ) * 1 ∧
    (N m (6, 7, 8) : ℚ) = 0 ∧
    (N m (6, 8, 8) : ℚ) = (-10 : ℚ) * 1 + (4 : ℚ) * (m : ℚ) ∧
    (N m (7, 7, 7) : ℚ) = (-80 : ℚ) * 1 + (20 : ℚ) * (m : ℚ) ∧
    (N m (7, 7, 8) : ℚ) = 0 ∧
    (N m (7, 8, 8) : ℚ) = (8 : ℚ) * 1 ∧
    (N m (8, 8, 8) : ℚ) = (-98 : ℚ) * 1 + ((41 : ℚ) / 3) * (m : ℚ) + (1 : ℚ) * (m : ℚ) ^ 2 + ((1 : ℚ) / 3) * (m : ℚ) ^ 3 := by
  induction m, hm using Nat.le_induction with
  | base =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [v8_s000, v8_s001, v8_s002, v8_s003, v8_s004, v8_s005, v8_s006, v8_s007, v8_s008, v8_s011, v8_s012, v8_s013, v8_s014, v8_s015, v8_s016, v8_s017, v8_s018, v8_s022, v8_s023, v8_s024, v8_s025, v8_s026, v8_s027, v8_s028, v8_s033, v8_s034, v8_s035, v8_s036, v8_s037, v8_s038, v8_s044, v8_s045, v8_s046, v8_s047, v8_s048, v8_s055, v8_s056, v8_s057, v8_s058, v8_s066, v8_s067, v8_s068, v8_s077, v8_s078, v8_s088, v8_s111, v8_s112, v8_s113, v8_s114, v8_s115, v8_s116, v8_s117, v8_s118, v8_s122, v8_s123, v8_s124, v8_s125, v8_s126, v8_s127, v8_s128, v8_s133, v8_s134, v8_s135, v8_s136, v8_s137, v8_s138, v8_s144, v8_s145, v8_s146, v8_s147, v8_s148, v8_s155, v8_s156, v8_s157, v8_s158, v8_s166, v8_s167, v8_s168, v8_s177, v8_s178, v8_s188, v8_s222, v8_s223, v8_s224, v8_s225, v8_s226, v8_s227, v8_s228, v8_s233, v8_s234, v8_s235, v8_s236, v8_s237, v8_s238, v8_s244, v8_s245, v8_s246, v8_s247, v8_s248, v8_s255, v8_s256, v8_s257, v8_s258, v8_s266, v8_s267, v8_s268, v8_s277, v8_s278, v8_s288, v8_s333, v8_s334, v8_s335, v8_s336, v8_s337, v8_s338, v8_s344, v8_s345, v8_s346, v8_s347, v8_s348, v8_s355, v8_s356, v8_s357, v8_s358, v8_s366, v8_s367, v8_s368, v8_s377, v8_s378, v8_s388, v8_s444, v8_s445, v8_s446, v8_s447, v8_s448, v8_s455, v8_s456, v8_s457, v8_s458, v8_s466, v8_s467, v8_s468, v8_s477, v8_s478, v8_s488, v8_s555, v8_s556, v8_s557, v8_s558, v8_s566, v8_s567, v8_s568, v8_s577, v8_s578, v8_s588, v8_s666, v8_s667, v8_s668, v8_s677, v8_s678, v8_s688, v8_s777, v8_s778, v8_s788, v8_s888] <;> norm_num
  | succ m hm ih =>
    obtain ⟨hs000, hs001, hs002, hs003, hs004, hs005, hs006, hs007, hs008, hs011, hs012, hs013, hs014, hs015, hs016, hs017, hs018, hs022, hs023, hs024, hs025, hs026, hs027, hs028, hs033, hs034, hs035, hs036, hs037, hs038, hs044, hs045, hs046, hs047, hs048, hs055, hs056, hs057, hs058, hs066, hs067, hs068, hs077, hs078, hs088, hs111, hs112, hs113, hs114, hs115, hs116, hs117, hs118, hs122, hs123, hs124, hs125, hs126, hs127, hs128, hs133, hs134, hs135, hs136, hs137, hs138, hs144, hs145, hs146, hs147, hs148, hs155, hs156, hs157, hs158, hs166, hs167, hs168, hs177, hs178, hs188, hs222, hs223, hs224, hs225, hs226, hs227, hs228, hs233, hs234, hs235, hs236, hs237, hs238, hs244, hs245, hs246, hs247, hs248, hs255, hs256, hs257, hs258, hs266, hs267, hs268, hs277, hs278, hs288, hs333, hs334, hs335, hs336, hs337, hs338, hs344, hs345, hs346, hs347, hs348, hs355, hs356, hs357, hs358, hs366, hs367, hs368, hs377, hs378, hs388, hs444, hs445, hs446, hs447, hs448, hs455, hs456, hs457, hs458, hs466, hs467, hs468, hs477, hs478, hs488, hs555, hs556, hs557, hs558, hs566, hs567, hs568, hs577, hs578, hs588, hs666, hs667, hs668, hs677, hs678, hs688, hs777, hs778, hs788, hs888⟩ := ih
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [tr_s000]
      all_goals (rw [hs000])
    · rw [tr_s001]
      push_cast
      all_goals simp
    · rw [tr_s002]
      push_cast
      all_goals simp
    · rw [tr_s003]
      push_cast
      all_goals simp
    · rw [tr_s004]
      push_cast
      all_goals simp
    · rw [tr_s005]
      push_cast
      all_goals simp
    · rw [tr_s006]
      push_cast
      all_goals simp
    · rw [tr_s007]
      push_cast
      all_goals simp
    · rw [tr_s008]
      push_cast
      all_goals simp
    · rw [tr_s011]
      all_goals (rw [hs001])
    · rw [tr_s012]
      push_cast
      all_goals simp
    · rw [tr_s013]
      push_cast
      all_goals simp
    · rw [tr_s014]
      push_cast
      all_goals simp
    · rw [tr_s015]
      push_cast
      all_goals simp
    · rw [tr_s016]
      push_cast
      all_goals simp
    · rw [tr_s017]
      push_cast
      all_goals simp
    · rw [tr_s018]
      push_cast
      all_goals simp
    · rw [tr_s022]
      all_goals (rw [hs002])
    · rw [tr_s023]
      push_cast
      all_goals simp
    · rw [tr_s024]
      push_cast
      all_goals simp
    · rw [tr_s025]
      push_cast
      all_goals simp
    · rw [tr_s026]
      push_cast
      all_goals simp
    · rw [tr_s027]
      push_cast
      all_goals simp
    · rw [tr_s028]
      push_cast
      all_goals simp
    · rw [tr_s033]
      all_goals (rw [hs003])
    · rw [tr_s034]
      push_cast
      all_goals simp
    · rw [tr_s035]
      push_cast
      all_goals simp
    · rw [tr_s036]
      push_cast
      all_goals simp
    · rw [tr_s037]
      push_cast
      all_goals simp
    · rw [tr_s038]
      push_cast
      all_goals simp
    · rw [tr_s044]
      all_goals (rw [hs004])
    · rw [tr_s045]
      push_cast
      all_goals simp
    · rw [tr_s046]
      push_cast
      all_goals simp
    · rw [tr_s047]
      push_cast
      all_goals simp
    · rw [tr_s048]
      push_cast
      all_goals simp
    · rw [tr_s055]
      all_goals (rw [hs005])
    · rw [tr_s056]
      push_cast
      all_goals simp
    · rw [tr_s057]
      push_cast
      all_goals simp
    · rw [tr_s058]
      push_cast
      all_goals simp
    · rw [tr_s066]
      all_goals (rw [hs006])
    · rw [tr_s067]
      push_cast
      all_goals simp
    · rw [tr_s068]
      push_cast
      all_goals simp
    · rw [tr_s077]
      all_goals (rw [hs007])
    · rw [tr_s078]
      push_cast
      all_goals simp
    · rw [tr_s088]
      all_goals (rw [hs008])
    · rw [tr_s111]
      push_cast
      all_goals (rw [hs011, hs111]; ring)
    · rw [tr_s112]
      push_cast
      all_goals (rw [hs011, hs111]; ring)
    · rw [tr_s113]
      push_cast
      all_goals simp
    · rw [tr_s114]
      push_cast
      all_goals simp
    · rw [tr_s115]
      push_cast
      all_goals simp
    · rw [tr_s116]
      push_cast
      all_goals simp
    · rw [tr_s117]
      push_cast
      all_goals simp
    · rw [tr_s118]
      push_cast
      all_goals simp
    · rw [tr_s122]
      push_cast
      all_goals (rw [hs012, hs112]; ring)
    · rw [tr_s123]
      push_cast
      all_goals (rw [hs012, hs112]; ring)
    · rw [tr_s124]
      push_cast
      all_goals simp
    · rw [tr_s125]
      push_cast
      all_goals simp
    · rw [tr_s126]
      push_cast
      all_goals simp
    · rw [tr_s127]
      push_cast
      all_goals simp
    · rw [tr_s128]
      push_cast
      all_goals simp
    · rw [tr_s133]
      push_cast
      all_goals (rw [hs013, hs113]; ring)
    · rw [tr_s134]
      push_cast
      all_goals (rw [hs013, hs113]; ring)
    · rw [tr_s135]
      push_cast
      all_goals simp
    · rw [tr_s136]
      push_cast
      all_goals simp
    · rw [tr_s137]
      push_cast
      all_goals simp
    · rw [tr_s138]
      push_cast
      all_goals simp
    · rw [tr_s144]
      push_cast
      all_goals (rw [hs014, hs114]; ring)
    · rw [tr_s145]
      push_cast
      all_goals (rw [hs014, hs114]; ring)
    · rw [tr_s146]
      push_cast
      all_goals simp
    · rw [tr_s147]
      push_cast
      all_goals simp
    · rw [tr_s148]
      push_cast
      all_goals simp
    · rw [tr_s155]
      push_cast
      all_goals (rw [hs015, hs115]; ring)
    · rw [tr_s156]
      push_cast
      all_goals (rw [hs015, hs115]; ring)
    · rw [tr_s157]
      push_cast
      all_goals simp
    · rw [tr_s158]
      push_cast
      all_goals simp
    · rw [tr_s166]
      push_cast
      all_goals (rw [hs016, hs116]; ring)
    · rw [tr_s167]
      push_cast
      all_goals (rw [hs016, hs116]; ring)
    · rw [tr_s168]
      push_cast
      all_goals simp
    · rw [tr_s177]
      push_cast
      all_goals (rw [hs017, hs117]; ring)
    · rw [tr_s178]
      push_cast
      all_goals (rw [hs017, hs117]; ring)
    · rw [tr_s188]
      push_cast
      all_goals (rw [hs018, hs118]; ring)
    · rw [tr_s222]
      push_cast
      all_goals (rw [hs022, hs122, hs222]; ring)
    · rw [tr_s223]
      all_goals (rw [hs122])
    · rw [tr_s224]
      push_cast
      all_goals (rw [hs022, hs122, hs222]; ring)
    · rw [tr_s225]
      push_cast
      all_goals simp
    · rw [tr_s226]
      push_cast
      all_goals simp
    · rw [tr_s227]
      push_cast
      all_goals simp
    · rw [tr_s228]
      push_cast
      all_goals simp
    · rw [tr_s233]
      push_cast
      all_goals (rw [hs023, hs123, hs223]; ring)
    · rw [tr_s234]
      push_cast
      all_goals (rw [hs123, hs223]; ring)
    · rw [tr_s235]
      push_cast
      all_goals (rw [hs023, hs123, hs223]; ring)
    · rw [tr_s236]
      push_cast
      all_goals simp
    · rw [tr_s237]
      push_cast
      all_goals simp
    · rw [tr_s238]
      push_cast
      all_goals simp
    · rw [tr_s244]
      push_cast
      all_goals (rw [hs024, hs124, hs224]; ring)
    · rw [tr_s245]
      all_goals (rw [hs124])
    · rw [tr_s246]
      push_cast
      all_goals (rw [hs024, hs124, hs224]; ring)
    · rw [tr_s247]
      push_cast
      all_goals simp
    · rw [tr_s248]
      push_cast
      all_goals simp
    · rw [tr_s255]
      push_cast
      all_goals (rw [hs025, hs125, hs225]; ring)
    · rw [tr_s256]
      all_goals (rw [hs125])
    · rw [tr_s257]
      push_cast
      all_goals (rw [hs025, hs125, hs225]; ring)
    · rw [tr_s258]
      push_cast
      all_goals simp
    · rw [tr_s266]
      push_cast
      all_goals (rw [hs026, hs126, hs226]; ring)
    · rw [tr_s267]
      all_goals (rw [hs126])
    · rw [tr_s268]
      push_cast
      all_goals (rw [hs026, hs126, hs226]; ring)
    · rw [tr_s277]
      push_cast
      all_goals (rw [hs027, hs127, hs227]; ring)
    · rw [tr_s278]
      all_goals (rw [hs127])
    · rw [tr_s288]
      push_cast
      all_goals (rw [hs028, hs128, hs228]; ring)
    · rw [tr_s333]
      push_cast
      all_goals (rw [hs033, hs133, hs233, hs333]; ring)
    · rw [tr_s334]
      all_goals (rw [hs133])
    · rw [tr_s335]
      all_goals (rw [hs233])
    · rw [tr_s336]
      push_cast
      all_goals (rw [hs033, hs133, hs233, hs333]; ring)
    · rw [tr_s337]
      push_cast
      all_goals simp
    · rw [tr_s338]
      push_cast
      all_goals simp
    · rw [tr_s344]
      push_cast
      all_goals (rw [hs034, hs134, hs234, hs334]; ring)
    · rw [tr_s345]
      push_cast
      all_goals (rw [hs134, hs234]; ring)
    · rw [tr_s346]
      push_cast
      all_goals (rw [hs234, hs334]; ring)
    · rw [tr_s347]
      push_cast
      all_goals (rw [hs034, hs134, hs234, hs334]; ring)
    · rw [tr_s348]
      push_cast
      all_goals simp
    · rw [tr_s355]
      push_cast
      all_goals (rw [hs035, hs135, hs235, hs335]; ring)
    · rw [tr_s356]
      push_cast
      all_goals (rw [hs135, hs335]; ring)
    · rw [tr_s357]
      all_goals (rw [hs235])
    · rw [tr_s358]
      push_cast
      all_goals (rw [hs035, hs135, hs235, hs335]; ring)
    · rw [tr_s366]
      push_cast
      all_goals (rw [hs036, hs136, hs236, hs336]; ring)
    · rw [tr_s367]
      all_goals (rw [hs136])
    · rw [tr_s368]
      all_goals (rw [hs236])
    · rw [tr_s377]
      push_cast
      all_goals (rw [hs037, hs137, hs237, hs337]; ring)
    · rw [tr_s378]
      all_goals (rw [hs137])
    · rw [tr_s388]
      push_cast
      all_goals (rw [hs038, hs138, hs238, hs338]; ring)
    · rw [tr_s444]
      push_cast
      all_goals (rw [hs044, hs144, hs244, hs344, hs444]; ring)
    · rw [tr_s445]
      all_goals (rw [hs144])
    · rw [tr_s446]
      push_cast
      all_goals (rw [hs244]; ring)
    · rw [tr_s447]
      all_goals (rw [hs344])
    · rw [tr_s448]
      push_cast
      all_goals (rw [hs044, hs144, hs244, hs344, hs444]; ring)
    · rw [tr_s455]
      push_cast
      all_goals (rw [hs045, hs145, hs245, hs345, hs445]; ring)
    · rw [tr_s456]
      push_cast
      all_goals (rw [hs145, hs245]; ring)
    · rw [tr_s457]
      push_cast
      all_goals (rw [hs245, hs345]; ring)
    · rw [tr_s458]
      push_cast
      all_goals (rw [hs345, hs445]; ring)
    · rw [tr_s466]
      push_cast
      all_goals (rw [hs046, hs146, hs246, hs346, hs446]; ring)
    · rw [tr_s467]
      push_cast
      all_goals (rw [hs146, hs346]; ring)
    · rw [tr_s468]
      push_cast
      all_goals (rw [hs246, hs446]; ring)
    · rw [tr_s477]
      push_cast
      all_goals (rw [hs047, hs147, hs247, hs347, hs447]; ring)
    · rw [tr_s478]
      push_cast
      all_goals (rw [hs147, hs447]; ring)
    · rw [tr_s488]
      push_cast
      all_goals (rw [hs048, hs148, hs248, hs348, hs448]; ring)
    · rw [tr_s555]
      push_cast
      all_goals (rw [hs055, hs155, hs255, hs355, hs455, hs555]; ring)
    · rw [tr_s556]
      all_goals (rw [hs155])
    · rw [tr_s557]
      all_goals (rw [hs255])
    · rw [tr_s558]
      all_goals (rw [hs355])
    · rw [tr_s566]
      push_cast
      all_goals (rw [hs056, hs156, hs256, hs356, hs456, hs556]; ring)
    · rw [tr_s567]
      push_cast
      all_goals (rw [hs156, hs256]; ring)
    · rw [tr_s568]
      push_cast
      all_goals (rw [hs256, hs356]; ring)
    · rw [tr_s577]
      push_cast
      all_goals (rw [hs057, hs157, hs257, hs357, hs457, hs557]; ring)
    · rw [tr_s578]
      push_cast
      all_goals (rw [hs157, hs357]; ring)
    · rw [tr_s588]
      push_cast
      all_goals (rw [hs058, hs158, hs258, hs358, hs458, hs558]; ring)
    · rw [tr_s666]
      push_cast
      all_goals (rw [hs066, hs166, hs266, hs366, hs466, hs566, hs666]; ring)
    · rw [tr_s667]
      all_goals (rw [hs166])
    · rw [tr_s668]
      all_goals (rw [hs266])
    · rw [tr_s677]
      push_cast
      all_goals (rw [hs067, hs167, hs267, hs367, hs467, hs567, hs667]; ring)
    · rw [tr_s678]
      push_cast
      all_goals (rw [hs167, hs267]; ring)
    · rw [tr_s688]
      push_cast
      all_goals (rw [hs068, hs168, hs268, hs368, hs468, hs568, hs668]; ring)
    · rw [tr_s777]
      push_cast
      all_goals (rw [hs077, hs177, hs277, hs377, hs477, hs577, hs677, hs777]; ring)
    · rw [tr_s778]
      all_goals (rw [hs177])
    · rw [tr_s788]
      push_cast
      all_goals (rw [hs078, hs178, hs278, hs378, hs478, hs578, hs678, hs778]; ring)
    · rw [tr_s888]
      push_cast
      all_goals (rw [hs088, hs188, hs288, hs388, hs488, hs588, hs688, hs788, hs888]; ring)

theorem a_explicit (m : ℕ) : a (m + 1) = N m (0, 0, 8) + N m (0, 1, 8) + N m (0, 2, 8) + N m (0, 3, 8) + N m (0, 4, 8) + N m (0, 5, 8) + N m (0, 6, 8) + N m (0, 7, 8) + N m (0, 8, 8) + N m (1, 1, 8) + N m (1, 2, 8) + N m (1, 3, 8) + N m (1, 4, 8) + N m (1, 5, 8) + N m (1, 6, 8) + N m (1, 7, 8) + N m (1, 8, 8) + N m (2, 2, 8) + N m (2, 3, 8) + N m (2, 4, 8) + N m (2, 5, 8) + N m (2, 6, 8) + N m (2, 7, 8) + N m (2, 8, 8) + N m (3, 3, 8) + N m (3, 4, 8) + N m (3, 5, 8) + N m (3, 6, 8) + N m (3, 7, 8) + N m (3, 8, 8) + N m (4, 4, 8) + N m (4, 5, 8) + N m (4, 6, 8) + N m (4, 7, 8) + N m (4, 8, 8) + N m (5, 5, 8) + N m (5, 6, 8) + N m (5, 7, 8) + N m (5, 8, 8) + N m (6, 6, 8) + N m (6, 7, 8) + N m (6, 8, 8) + N m (7, 7, 8) + N m (7, 8, 8) + N m (8, 8, 8) := by
  rw [a_eq]
  simp only [sum_product, sum_range_succ, sum_range_zero, N_nonmono m (1, 0, 8) (by norm_num), N_nonmono m (2, 0, 8) (by norm_num), N_nonmono m (2, 1, 8) (by norm_num), N_nonmono m (3, 0, 8) (by norm_num), N_nonmono m (3, 1, 8) (by norm_num), N_nonmono m (3, 2, 8) (by norm_num), N_nonmono m (4, 0, 8) (by norm_num), N_nonmono m (4, 1, 8) (by norm_num), N_nonmono m (4, 2, 8) (by norm_num), N_nonmono m (4, 3, 8) (by norm_num), N_nonmono m (5, 0, 8) (by norm_num), N_nonmono m (5, 1, 8) (by norm_num), N_nonmono m (5, 2, 8) (by norm_num), N_nonmono m (5, 3, 8) (by norm_num), N_nonmono m (5, 4, 8) (by norm_num), N_nonmono m (6, 0, 8) (by norm_num), N_nonmono m (6, 1, 8) (by norm_num), N_nonmono m (6, 2, 8) (by norm_num), N_nonmono m (6, 3, 8) (by norm_num), N_nonmono m (6, 4, 8) (by norm_num), N_nonmono m (6, 5, 8) (by norm_num), N_nonmono m (7, 0, 8) (by norm_num), N_nonmono m (7, 1, 8) (by norm_num), N_nonmono m (7, 2, 8) (by norm_num), N_nonmono m (7, 3, 8) (by norm_num), N_nonmono m (7, 4, 8) (by norm_num), N_nonmono m (7, 5, 8) (by norm_num), N_nonmono m (7, 6, 8) (by norm_num), N_nonmono m (8, 0, 8) (by norm_num), N_nonmono m (8, 1, 8) (by norm_num), N_nonmono m (8, 2, 8) (by norm_num), N_nonmono m (8, 3, 8) (by norm_num), N_nonmono m (8, 4, 8) (by norm_num), N_nonmono m (8, 5, 8) (by norm_num), N_nonmono m (8, 6, 8) (by norm_num), N_nonmono m (8, 7, 8) (by norm_num)]
  ring

theorem a_poly (m : ℕ) (hm : 8 ≤ m) : (a (m + 1) : ℚ) = (-64 : ℚ) * 1 + ((65 : ℚ) / 3) * (m : ℚ) + (3 : ℚ) * (m : ℚ) ^ 2 + ((1 : ℚ) / 3) * (m : ℚ) ^ 3 := by
  rw [a_explicit]
  push_cast
  obtain ⟨-, -, -, -, -, -, -, -, hs008, -, -, -, -, -, -, -, hs018, -, -, -, -, -, -, hs028, -, -, -, -, -, hs038, -, -, -, -, hs048, -, -, -, hs058, -, -, hs068, -, hs078, hs088, -, -, -, -, -, -, -, hs118, -, -, -, -, -, -, hs128, -, -, -, -, -, hs138, -, -, -, -, hs148, -, -, -, hs158, -, -, hs168, -, hs178, hs188, -, -, -, -, -, -, hs228, -, -, -, -, -, hs238, -, -, -, -, hs248, -, -, -, hs258, -, -, hs268, -, hs278, hs288, -, -, -, -, -, hs338, -, -, -, -, hs348, -, -, -, hs358, -, -, hs368, -, hs378, hs388, -, -, -, -, hs448, -, -, -, hs458, -, -, hs468, -, hs478, hs488, -, -, -, hs558, -, -, hs568, -, hs578, hs588, -, -, hs668, -, hs678, hs688, -, hs778, hs788, hs888⟩ := closed_all m hm
  rw [hs008, hs018, hs028, hs038, hs048, hs058, hs068, hs078, hs088, hs118, hs128, hs138, hs148, hs158, hs168, hs178, hs188, hs228, hs238, hs248, hs258, hs268, hs278, hs288, hs338, hs348, hs358, hs368, hs378, hs388, hs448, hs458, hs468, hs478, hs488, hs558, hs568, hs578, hs588, hs668, hs678, hs688, hs778, hs788, hs888]
  ring

theorem aval3 : a 3 = 40 := by
  rw [a_explicit, v2_s008, v2_s018, v2_s028, v2_s038, v2_s048, v2_s058, v2_s068, v2_s078, v2_s088, v2_s118, v2_s128, v2_s138, v2_s148, v2_s158, v2_s168, v2_s178, v2_s188, v2_s228, v2_s238, v2_s248, v2_s258, v2_s268, v2_s278, v2_s288, v2_s338, v2_s348, v2_s358, v2_s368, v2_s378, v2_s388, v2_s448, v2_s458, v2_s468, v2_s478, v2_s488, v2_s558, v2_s568, v2_s578, v2_s588, v2_s668, v2_s678, v2_s688, v2_s778, v2_s788, v2_s888]

theorem aval4 : a 4 = 65 := by
  rw [a_explicit, v3_s008, v3_s018, v3_s028, v3_s038, v3_s048, v3_s058, v3_s068, v3_s078, v3_s088, v3_s118, v3_s128, v3_s138, v3_s148, v3_s158, v3_s168, v3_s178, v3_s188, v3_s228, v3_s238, v3_s248, v3_s258, v3_s268, v3_s278, v3_s288, v3_s338, v3_s348, v3_s358, v3_s368, v3_s378, v3_s388, v3_s448, v3_s458, v3_s468, v3_s478, v3_s488, v3_s558, v3_s568, v3_s578, v3_s588, v3_s668, v3_s678, v3_s688, v3_s778, v3_s788, v3_s888]

theorem aval5 : a 5 = 105 := by
  rw [a_explicit, v4_s008, v4_s018, v4_s028, v4_s038, v4_s048, v4_s058, v4_s068, v4_s078, v4_s088, v4_s118, v4_s128, v4_s138, v4_s148, v4_s158, v4_s168, v4_s178, v4_s188, v4_s228, v4_s238, v4_s248, v4_s258, v4_s268, v4_s278, v4_s288, v4_s338, v4_s348, v4_s358, v4_s368, v4_s378, v4_s388, v4_s448, v4_s458, v4_s468, v4_s478, v4_s488, v4_s558, v4_s568, v4_s578, v4_s588, v4_s668, v4_s678, v4_s688, v4_s778, v4_s788, v4_s888]

theorem aval6 : a 6 = 164 := by
  rw [a_explicit, v5_s008, v5_s018, v5_s028, v5_s038, v5_s048, v5_s058, v5_s068, v5_s078, v5_s088, v5_s118, v5_s128, v5_s138, v5_s148, v5_s158, v5_s168, v5_s178, v5_s188, v5_s228, v5_s238, v5_s248, v5_s258, v5_s268, v5_s278, v5_s288, v5_s338, v5_s348, v5_s358, v5_s368, v5_s378, v5_s388, v5_s448, v5_s458, v5_s468, v5_s478, v5_s488, v5_s558, v5_s568, v5_s578, v5_s588, v5_s668, v5_s678, v5_s688, v5_s778, v5_s788, v5_s888]

theorem aval7 : a 7 = 246 := by
  rw [a_explicit, v6_s008, v6_s018, v6_s028, v6_s038, v6_s048, v6_s058, v6_s068, v6_s078, v6_s088, v6_s118, v6_s128, v6_s138, v6_s148, v6_s158, v6_s168, v6_s178, v6_s188, v6_s228, v6_s238, v6_s248, v6_s258, v6_s268, v6_s278, v6_s288, v6_s338, v6_s348, v6_s358, v6_s368, v6_s378, v6_s388, v6_s448, v6_s458, v6_s468, v6_s478, v6_s488, v6_s558, v6_s568, v6_s578, v6_s588, v6_s668, v6_s678, v6_s688, v6_s778, v6_s788, v6_s888]

theorem aval8 : a 8 = 349 := by
  rw [a_explicit, v7_s008, v7_s018, v7_s028, v7_s038, v7_s048, v7_s058, v7_s068, v7_s078, v7_s088, v7_s118, v7_s128, v7_s138, v7_s148, v7_s158, v7_s168, v7_s178, v7_s188, v7_s228, v7_s238, v7_s248, v7_s258, v7_s268, v7_s278, v7_s288, v7_s338, v7_s348, v7_s358, v7_s368, v7_s378, v7_s388, v7_s448, v7_s458, v7_s468, v7_s478, v7_s488, v7_s558, v7_s568, v7_s578, v7_s588, v7_s668, v7_s678, v7_s688, v7_s778, v7_s788, v7_s888]

theorem aval9 : a 9 = 472 := by
  rw [a_explicit, v8_s008, v8_s018, v8_s028, v8_s038, v8_s048, v8_s058, v8_s068, v8_s078, v8_s088, v8_s118, v8_s128, v8_s138, v8_s148, v8_s158, v8_s168, v8_s178, v8_s188, v8_s228, v8_s238, v8_s248, v8_s258, v8_s268, v8_s278, v8_s288, v8_s338, v8_s348, v8_s358, v8_s368, v8_s378, v8_s388, v8_s448, v8_s458, v8_s468, v8_s478, v8_s488, v8_s558, v8_s568, v8_s578, v8_s588, v8_s668, v8_s678, v8_s688, v8_s778, v8_s788, v8_s888]


theorem aval10 : a 10 = 617 := by
  have h := a_poly 9 (by norm_num)
  norm_num at h
  exact_mod_cast h

theorem aval11 : a 11 = 786 := by
  have h := a_poly 10 (by norm_num)
  norm_num at h
  exact_mod_cast h

theorem aval12 : a 12 = 981 := by
  have h := a_poly 11 (by norm_num)
  norm_num at h
  exact_mod_cast h

end OMAA190040Helpers

open OMAA190040Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a190040.main := by
  intro n hn
  by_cases h13 : 13 ≤ n
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 13 := ⟨n - 13, by omega⟩
    rw [show m + 13 - 1 = m + 11 + 1 by omega, show m + 13 - 2 = m + 10 + 1 by omega,
      show m + 13 - 3 = m + 9 + 1 by omega, show m + 13 - 4 = m + 8 + 1 by omega,
      show m + 13 = m + 12 + 1 by omega]
    have h0 := a_poly (m + 12) (by omega)
    have h1 := a_poly (m + 11) (by omega)
    have h2 := a_poly (m + 10) (by omega)
    have h3 := a_poly (m + 9) (by omega)
    have h4 := a_poly (m + 8) (by omega)
    have hq : (OMA.S_oeis_a190040.a (m + 12 + 1) : ℚ) = 4 * OMA.S_oeis_a190040.a (m + 11 + 1) -
        6 * OMA.S_oeis_a190040.a (m + 10 + 1) + 4 * OMA.S_oeis_a190040.a (m + 9 + 1) -
        OMA.S_oeis_a190040.a (m + 8 + 1) := by
      rw [h0, h1, h2, h3, h4]
      push_cast
      ring
    exact_mod_cast hq
  · interval_cases n <;> norm_num [aval7, aval8, aval9, aval10, aval11, aval12]
