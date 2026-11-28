import OMAStatements.S_oeis_a325618
import Mathlib

namespace A325618P

open OMA.S_oeis_a325618

private def sv (y : ℕ) : ℕ := y * y + y + 1

/-! ## Part 1: 137 is not a term -/

private def ex : ℕ → ℕ → ℕ → ℕ → Bool
  | 0, _, _, rem => rem == 0
  | k + 1, y, prev, rem =>
      (List.range ((y + 1) * prev + 1)).any
        (fun b => decide (sv (y + 1) * b ≤ rem) && ex k (y + 1) b (rem - sv (y + 1) * b))

private lemma ex_sound (a : ℕ → ℕ) (ha : ∀ i, a (i + 1) ≤ (i + 1) * a i) :
    ∀ k y rem, (∑ i ∈ Finset.Ico (y + 1) (y + 1 + k), sv i * a i) = rem →
      ex k y (a y) rem = true := by
  intro k
  induction k with
  | zero =>
    intro y rem h
    simp at h
    simp [ex, ← h]
  | succ k ih =>
    intro y rem h
    rw [Finset.sum_eq_sum_Ico_succ_bot (by omega)] at h
    simp only [ex, List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨a (y + 1), ?_, ?_, ?_⟩
    · have := ha y; omega
    · omega
    · apply ih
      have : y + 1 + (k + 1) = y + 1 + 1 + k := by omega
      rw [this] at h
      omega

set_option maxRecDepth 100000 in
private lemma ex_false : ex 136 0 1 136 = false := by decide

private lemma fact_div_cast {x y : ℕ} (h : x ≤ y) :
    (((y.factorial / x.factorial : ℕ)) : ℚ) = (y.factorial : ℚ) / x.factorial := by
  rw [Nat.cast_div (Nat.factorial_dvd_factorial h) (by positivity)]

private lemma tel (x : ℕ) : (∑ y ∈ Finset.range x, sv y * y.factorial) = x * x.factorial := by
  induction x with
  | zero => simp
  | succ x ih =>
    rw [Finset.sum_range_succ, ih, Nat.factorial_succ]
    simp only [sv]; ring

private lemma trunc (x : ℕ) (g : ℕ → ℚ) : ∀ n, x ≤ n →
    (∑ y ∈ Finset.range n, (if y < x then g y else 0)) = ∑ y ∈ Finset.range x, g y := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    apply Finset.sum_congr rfl
    intro y hy; simp at hy; simp [hy]
  | succ n hn ih =>
    rw [Finset.sum_range_succ, ih]
    have : ¬ n < x := by omega
    simp [this]

private lemma swap (P : Multiset ℕ) (s : Finset ℕ) (g : ℕ → ℕ → ℚ) :
    (∑ y ∈ s, (P.map (g y)).sum) = (P.map fun x => ∑ y ∈ s, g y x).sum := by
  induction P using Multiset.induction_on with
  | empty => simp
  | cons a P ih => simp [Finset.sum_add_distrib, ih]

private lemma not137 : ¬ IsTerm 137 := by
  rintro ⟨p, hp⟩
  unfold recipFactorialSum at hp
  set P := p.parts with hP
  have hpos : ∀ x ∈ P, 0 < x := fun x hx => p.parts_pos hx
  have hsum : P.sum = 137 := p.parts_sum
  have hle : ∀ x ∈ P, x ≤ 137 := fun x hx => hsum ▸ Multiset.le_sum_of_mem hx
  let A : ℕ → ℚ := fun y =>
    (P.map fun x => if y < x then (y.factorial : ℚ) / x.factorial else 0).sum
  let Bn : ℕ → ℕ := fun y => (P.map fun x => if y < x then 0 else y.factorial / x.factorial).sum
  have hAB : ∀ y, A y + Bn y = y.factorial := by
    intro y
    have e1 : ((Bn y : ℕ) : ℚ) =
        (P.map fun x => if y < x then (0 : ℚ) else (y.factorial : ℚ) / x.factorial).sum := by
      simp only [Bn, Nat.cast_multiset_sum, Multiset.map_map, Function.comp_def]
      congr 1
      apply Multiset.map_congr rfl
      intro x _
      split_ifs with h
      · simp
      · exact fact_div_cast (by omega)
    rw [e1, ← Multiset.sum_map_add]
    have : (P.map fun x => (if y < x then (y.factorial : ℚ) / x.factorial else 0) +
        (if y < x then (0 : ℚ) else (y.factorial : ℚ) / x.factorial)) =
        P.map fun x => (y.factorial : ℚ) * (1 / x.factorial) := by
      apply Multiset.map_congr rfl
      intro x _
      split_ifs <;> ring
    rw [this, Multiset.sum_map_mul_left, hp, mul_one]
  have hAnn : ∀ y, 0 ≤ A y := by
    intro y
    apply Multiset.sum_nonneg
    intro z hz
    simp only [Multiset.mem_map] at hz
    obtain ⟨x, _, rfl⟩ := hz
    split_ifs <;> positivity
  let a : ℕ → ℕ := fun y => y.factorial - Bn y
  have ha : ∀ y, (a y : ℚ) = A y := by
    intro y
    have h1 := hAB y
    have h2 := hAnn y
    have hb : Bn y ≤ y.factorial := by
      have : (Bn y : ℚ) ≤ y.factorial := by linarith
      exact_mod_cast this
    simp only [a]
    rw [Nat.cast_sub hb]
    linarith
  have ha0 : a 0 = 1 := by
    have : (a 0 : ℚ) = 1 := by
      rw [ha]
      simp only [A]
      rw [← hp]
      congr 1
      apply Multiset.map_congr rfl
      intro x hx
      simp [hpos x hx]
    exact_mod_cast this
  have hrec : ∀ i, a (i + 1) ≤ (i + 1) * a i := by
    intro i
    have : (a (i + 1) : ℚ) ≤ (i + 1) * a i := by
      rw [ha, ha]
      simp only [A]
      rw [← Multiset.sum_map_mul_left]
      apply Multiset.sum_map_le_sum_map
      intro x _
      by_cases h1 : i + 1 < x
      · have h2 : i < x := by omega
        simp only [h1, h2, if_true, Nat.factorial_succ]
        push_cast; ring_nf; exact le_refl _
      · simp only [h1, if_false]
        split_ifs <;> positivity
    exact_mod_cast this
  have hident : (∑ y ∈ Finset.range 137, (sv y : ℚ) * A y) = 137 := by
    simp only [A]
    simp_rw [← Multiset.sum_map_mul_left]
    rw [swap]
    have : (P.map fun x => ∑ y ∈ Finset.range 137,
        (sv y : ℚ) * (if y < x then (y.factorial : ℚ) / x.factorial else 0)) =
        P.map (Nat.cast : ℕ → ℚ) := by
      apply Multiset.map_congr rfl
      intro x hx
      have := trunc x (fun y => (sv y : ℚ) * ((y.factorial : ℚ) / x.factorial)) 137 (hle x hx)
      simp only [mul_ite, mul_zero] at this ⊢
      rw [this]
      have ht := tel x
      have : (∑ y ∈ Finset.range x, (sv y : ℚ) * (y.factorial : ℚ)) = x * x.factorial := by
        exact_mod_cast ht
      simp_rw [← mul_div_assoc, ← Finset.sum_div]
      rw [this]
      field_simp
    rw [this, ← Nat.cast_multiset_sum, hsum]
    norm_num
  have hnat : (∑ y ∈ Finset.range 137, sv y * a y) = 137 := by
    have : ((∑ y ∈ Finset.range 137, sv y * a y : ℕ) : ℚ) = 137 := by
      push_cast
      simp_rw [ha]
      exact hident
    exact_mod_cast this
  have key : sv 0 * a 0 + (∑ i ∈ Finset.Ico 1 137, sv i * a i) = 137 := by
    rw [Finset.range_eq_Ico] at hnat
    rwa [Finset.sum_eq_sum_Ico_succ_bot (by norm_num)] at hnat
  rw [ha0, show sv 0 = 1 from rfl] at key
  have h136 : (∑ i ∈ Finset.Ico 1 137, sv i * a i) = 136 := by omega
  have := ex_sound a hrec 136 0 136 h136
  rw [ha0, ex_false] at this
  exact absurd this (by decide)

/-! ## Part 2: every m > 137 is a term -/

private def f (y : ℕ) : ℚ := 1 / (y.factorial : ℚ)

private def Inv (L m : ℕ) : Prop :=
  ∃ Q : Multiset ℕ, (∀ x ∈ Q, 0 < x) ∧ L + Q.sum = m ∧ f L + (Q.map f).sum = 1

private lemma term_of_inv {L m : ℕ} (hL : 0 < L) (h : Inv L m) : IsTerm m := by
  obtain ⟨Q, hQ, hs, hr⟩ := h
  refine ⟨⟨L ::ₘ Q, ?_, ?_⟩, ?_⟩
  · intro i hi
    rw [Multiset.mem_cons] at hi
    rcases hi with rfl | hi
    · exact hL
    · exact hQ i hi
  · simp [hs]
  · unfold recipFactorialSum
    rw [Multiset.map_cons, Multiset.sum_cons]
    exact hr

private lemma inv_step {L m : ℕ} (b c : ℕ) (hbc : b + c = L) (h : Inv L m) :
    Inv (L + 1) (m + (L * L + L + 1) + b * (L * L + 3 * L + 3)) := by
  obtain ⟨Q, hQ, hs, hr⟩ := h
  refine ⟨Multiset.replicate c (L + 1) + Multiset.replicate (b * (L + 2)) (L + 2) + Q, ?_, ?_, ?_⟩
  · intro x hx
    simp only [Multiset.mem_add, Multiset.mem_replicate] at hx
    rcases hx with (⟨_, rfl⟩ | ⟨_, rfl⟩) | hx
    · omega
    · omega
    · exact hQ x hx
  · simp only [Multiset.sum_add, Multiset.sum_replicate, smul_eq_mul]
    subst hbc; rw [← hs]; ring
  · rw [← hr]
    simp only [Multiset.map_add, Multiset.sum_add, Multiset.map_replicate,
      Multiset.sum_replicate, nsmul_eq_mul, f]
    have e1 : ((L + 1).factorial : ℚ) = (L + 1) * L.factorial := by
      rw [Nat.factorial_succ]; push_cast; ring
    have e2 : ((L + 2).factorial : ℚ) = (L + 2) * ((L + 1) * L.factorial) := by
      rw [Nat.factorial_succ (L + 1), Nat.factorial_succ L]; push_cast; ring
    rw [e1, e2]
    have hLf : (L.factorial : ℚ) ≠ 0 := by positivity
    have hbc' : (b : ℚ) + c = L := by exact_mod_cast hbc
    push_cast
    field_simp
    rw [← hbc']; ring

private def orS (x base step : ℕ) : ℕ → ℕ
  | 0 => x <<< base
  | n + 1 => orS x base step n ||| (x <<< (base + (n + 1) * step))

private def mk : ℕ → ℕ
  | 0 => 0
  | L + 1 => if L = 0 then 2 else orS (mk L) (L * L + L + 1) (L * L + 3 * L + 3) L

private lemma orS_sound (x base step : ℕ) : ∀ n m, (orS x base step n).testBit m = true →
    ∃ b ≤ n, base + b * step ≤ m ∧ x.testBit (m - (base + b * step)) = true := by
  intro n
  induction n with
  | zero =>
    intro m h
    simp only [orS, Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨0, le_refl _, by simpa using h.1, by simpa using h.2⟩
  | succ n ih =>
    intro m h
    simp only [orS, Nat.testBit_lor, Bool.or_eq_true] at h
    rcases h with h | h
    · obtain ⟨b, hb, h1, h2⟩ := ih m h
      exact ⟨b, by omega, h1, h2⟩
    · simp only [Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨n + 1, le_refl _, h.1, h.2⟩

private lemma mk_sound : ∀ L m, (mk (L + 1)).testBit m = true → Inv (L + 1) m := by
  intro L
  induction L with
  | zero =>
    intro m h
    simp only [mk, if_true] at h
    have : m = 1 := by
      rw [show (2 : ℕ) = 2 ^ 1 by rfl, Nat.testBit_two_pow] at h
      simpa [eq_comm] using h
    subst this
    exact ⟨0, by simp, by simp, by simp [f]⟩
  | succ L ih =>
    intro m h
    simp only [mk, Nat.succ_ne_zero, if_false] at h
    obtain ⟨b, hb, h1, h2⟩ := orS_sound _ _ _ _ m h
    have := inv_step b (L + 1 - b) (by omega) (ih _ h2)
    convert this using 1
    omega

set_option maxRecDepth 100000 in
private lemma bits7 : ∀ i, i < 556 → (mk 7).testBit (230 + i) = true := by decide

private lemma inv7 (m : ℕ) (h1 : 230 ≤ m) (h2 : m ≤ 785) : Inv 7 m := by
  apply mk_sound 6
  have := bits7 (m - 230) (by omega)
  rw [show 230 + (m - 230) = m by omega] at this
  exact this

private def lo : ℕ → ℕ
  | 0 => 230
  | n + 1 => lo n + ((n + 7) * (n + 7) + (n + 7) + 1)

private def w : ℕ → ℕ
  | 0 => 555
  | n + 1 => w n + (n + 7) * ((n + 7) * (n + 7) + 3 * (n + 7) + 3)

private lemma w_ge : ∀ n, (n + 7) ^ 3 ≤ w n := by
  intro n
  induction n with
  | zero => simp [w]
  | succ n ih =>
    simp only [w]
    nlinarith [ih]

private lemma lo_ge : ∀ n, 230 ≤ lo n := by
  intro n
  induction n with
  | zero => simp [lo]
  | succ n ih => simp only [lo]; omega

private lemma Qn : ∀ n m, lo n ≤ m → m ≤ lo n + w n → Inv (n + 7) m := by
  intro n
  induction n with
  | zero => intro m h1 h2; simp only [lo, w] at h1 h2; exact inv7 m h1 (by omega)
  | succ n ih =>
    intro m h1 h2
    simp only [lo, w] at h1 h2
    have hw := w_ge n
    have ht3 : (n + 7) * (n + 7) + 3 * (n + 7) + 3 ≤ (n + 7) ^ 3 := by nlinarith
    obtain ⟨t, ht⟩ : ∃ t, t = (n + 7) * (n + 7) + 3 * (n + 7) + 3 := ⟨_, rfl⟩
    obtain ⟨e, he⟩ : ∃ e, e = m - lo n - ((n + 7) * (n + 7) + (n + 7) + 1) := ⟨_, rfl⟩
    rw [← ht] at h2 ht3
    have hwt : t ≤ w n + 1 := by omega
    by_cases hc : n + 7 ≤ e / t
    · have hLt : (n + 7) * t ≤ e :=
        le_trans (Nat.mul_le_mul_right t hc) (Nat.div_mul_le_self e t)
      have := inv_step (n + 7) 0 (by omega) (ih (lo n + (e - (n + 7) * t)) (by omega) (by omega))
      rw [← ht] at this
      convert this using 1
      omega
    · have htpos : 0 < t := by omega
      have hmod := Nat.mod_lt e htpos
      have hdm := Nat.div_add_mod e t
      have := inv_step (e / t) (n + 7 - e / t) (by omega) (ih (lo n + e % t) (by omega) (by omega))
      rw [← ht] at this
      convert this using 1
      have : t * (e / t) = e / t * t := Nat.mul_comm _ _
      omega

private lemma big : ∀ n m, 230 ≤ m → m ≤ lo n + w n → IsTerm m := by
  intro n
  induction n with
  | zero => intro m h1 h2; exact term_of_inv (by norm_num) (Qn 0 m (by simpa [lo] using h1) h2)
  | succ n ih =>
    intro m h1 h2
    by_cases h : m ≤ lo n + w n
    · exact ih m h1 h
    · have hc : (n + 7) * (n + 7) + (n + 7) + 1 ≤ w n + 1 := by
        have := w_ge n
        have : (n + 7) * (n + 7) + (n + 7) + 1 ≤ (n + 7) ^ 3 := by nlinarith
        omega
      exact term_of_inv (by omega) (Qn (n + 1) m (by simp only [lo]; omega) h2)

private def U : ℕ := mk 1 ||| mk 2 ||| mk 3 ||| mk 4 ||| mk 5 ||| mk 6 ||| mk 7

set_option maxRecDepth 100000 in
private lemma U_cover : ∀ m, 138 ≤ m → m < 230 →
    (U.testBit m = true ∨ m = 142 ∨ m = 143 ∨ m = 155 ∨ m = 167 ∨ m = 186 ∨ m = 198 ∨
      m = 229) := by decide

private lemma U_sound (m : ℕ) (h : U.testBit m = true) : IsTerm m := by
  simp only [U, Nat.testBit_lor, Bool.or_eq_true] at h
  rcases h with ((((((h | h) | h) | h) | h) | h) | h)
  · exact term_of_inv (by norm_num) (mk_sound 0 m h)
  · exact term_of_inv (by norm_num) (mk_sound 1 m h)
  · exact term_of_inv (by norm_num) (mk_sound 2 m h)
  · exact term_of_inv (by norm_num) (mk_sound 3 m h)
  · exact term_of_inv (by norm_num) (mk_sound 4 m h)
  · exact term_of_inv (by norm_num) (mk_sound 5 m h)
  · exact term_of_inv (by norm_num) (mk_sound 6 m h)

private lemma of_ms (m : ℕ) (P : Multiset ℕ) (hp : ∀ x ∈ P, 0 < x) (hs : P.sum = m)
    (hr : (P.map f).sum = 1) : IsTerm m :=
  ⟨⟨P, fun h => hp _ h, hs⟩, by unfold recipFactorialSum; exact hr⟩

private lemma of5 (m c1 y1 c2 y2 c3 y3 c4 y4 c5 y5 : ℕ)
    (hp : 0 < y1 ∧ 0 < y2 ∧ 0 < y3 ∧ 0 < y4 ∧ 0 < y5)
    (hs : c1 * y1 + c2 * y2 + c3 * y3 + c4 * y4 + c5 * y5 = m)
    (hr : (c1 : ℚ) / y1.factorial + c2 / y2.factorial + c3 / y3.factorial + c4 / y4.factorial
      + c5 / y5.factorial = 1) : IsTerm m := by
  apply of_ms m (Multiset.replicate c1 y1 + Multiset.replicate c2 y2 + Multiset.replicate c3 y3
    + Multiset.replicate c4 y4 + Multiset.replicate c5 y5)
  · intro x hx
    simp only [Multiset.mem_add, Multiset.mem_replicate] at hx
    rcases hx with (((⟨_, rfl⟩ | ⟨_, rfl⟩) | ⟨_, rfl⟩) | ⟨_, rfl⟩) | ⟨_, rfl⟩ <;> omega
  · simp only [Multiset.sum_add, Multiset.sum_replicate, smul_eq_mul]; omega
  · rw [← hr]
    simp only [Multiset.map_add, Multiset.sum_add, Multiset.map_replicate,
      Multiset.sum_replicate, nsmul_eq_mul, f]
    ring

private theorem main' : ¬ IsTerm 137 ∧ ∀ m : ℕ, 137 < m → IsTerm m := by
  refine ⟨not137, ?_⟩
  intro m hm
  by_cases h230 : m < 230
  · rcases U_cover m (by omega) h230 with h | h | h | h | h | h | h | h
    · exact U_sound m h
    · subst h; exact of5 142 1 2 1 3 3 4 25 5 0 1 (by norm_num) (by norm_num) (by norm_num [Nat.factorial])
    · subst h; exact of5 143 2 3 14 4 9 5 6 6 0 1 (by norm_num) (by norm_num) (by norm_num [Nat.factorial])
    · subst h; exact of5 155 1 2 7 4 25 5 0 1 0 1 (by norm_num) (by norm_num) (by norm_num [Nat.factorial])
    · subst h; exact of5 167 1 3 16 4 20 5 0 1 0 1 (by norm_num) (by norm_num) (by norm_num [Nat.factorial])
    · subst h; exact of5 186 1 2 7 4 24 5 6 6 0 1 (by norm_num) (by norm_num) (by norm_num [Nat.factorial])
    · subst h; exact of5 198 1 3 16 4 19 5 6 6 0 1 (by norm_num) (by norm_num) (by norm_num [Nat.factorial])
    · subst h; exact of5 229 1 2 7 4 24 5 5 6 7 7 (by norm_num) (by norm_num) (by norm_num [Nat.factorial])
  · exact big m m (by omega) (by
      have := w_ge m
      have : m + 7 ≤ (m + 7) ^ 3 := Nat.le_self_pow (by norm_num) _
      omega)

end A325618P

theorem OMA.solution : type_of% @OMA.S_oeis_a325618.main := A325618P.main'

