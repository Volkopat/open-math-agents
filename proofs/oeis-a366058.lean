import OMAStatements.S_oeis_a366058
import Mathlib

open OMA.S_oeis_a366058

namespace OMA.P_oeis_a366058

def V {n : ℕ} (q : ℤ × ℤ × ℤ) (s : Fin n → Fin 6) : Prop :=
  ∀ k : ℕ, k < n → sqDist (q + pos s k) ≤ sqDist (q + pos s (k + 1))

lemma pos_zero {n : ℕ} (s : Fin n → Fin 6) : pos s 0 = 0 := by simp [pos]

lemma pos_cons_succ {n : ℕ} (d : Fin 6) (t : Fin n → Fin 6) (k : ℕ) :
    pos (Fin.cons d t : Fin (n + 1) → Fin 6) (k + 1) = dir d + pos t k := by
  simp [pos, List.ofFn_succ]

lemma V_cons {n : ℕ} (q : ℤ × ℤ × ℤ) (d : Fin 6) (t : Fin n → Fin 6) :
    V q (Fin.cons d t : Fin (n + 1) → Fin 6) ↔ sqDist q ≤ sqDist (q + dir d) ∧ V (q + dir d) t := by
  constructor
  · intro h
    refine ⟨?_, fun k hk => ?_⟩
    · have := h 0 (by omega)
      simpa [pos_zero, pos_cons_succ] using this
    · have := h (k + 1) (by omega)
      rw [pos_cons_succ, pos_cons_succ, ← add_assoc, ← add_assoc] at this
      exact this
  · rintro ⟨h0, h⟩ k hk
    rcases k with _ | k
    · simpa [pos_zero, pos_cons_succ] using h0
    · rw [pos_cons_succ, pos_cons_succ, ← add_assoc, ← add_assoc]
      exact h k (by omega)

lemma card_cons (n : ℕ) (P : (Fin (n + 1) → Fin 6) → Prop) :
    Nat.card {s // P s} = ∑ d : Fin 6, Nat.card {t : Fin n → Fin 6 // P (Fin.cons d t)} := by
  rw [← Nat.card_sigma]
  apply Nat.card_congr
  exact { toFun := fun s => ⟨s.1 0, Fin.tail s.1, by simpa [Fin.cons_self_tail] using s.2⟩,
          invFun := fun p => ⟨Fin.cons p.1 p.2.1, p.2.2⟩,
          left_inv := fun s => by ext1; simp [Fin.cons_self_tail],
          right_inv := fun p => rfl }

lemma card_and {α : Type} [Finite α] (A : Prop) [Decidable A] (R : α → Prop) :
    Nat.card {t // A ∧ R t} = if A then Nat.card {t // R t} else 0 := by
  by_cases hA : A
  · simp only [hA, true_and, if_true]
  · simp only [hA, false_and, if_false]
    exact Nat.card_of_isEmpty

def zc (t : ℤ) : ℕ := if t = 0 then 1 else 0

def z (q : ℤ × ℤ × ℤ) : ℕ := zc q.1 + zc q.2.1 + zc q.2.2

def f : ℕ → ℕ → ℕ
  | 0, _ => 1
  | (n + 1), w => (3 - w) * f n w + 2 * w * f n (w - 1)

lemma pairX (n : ℕ) (t : ℤ) (b c : ℕ) :
    ((if 0 ≤ t then f n (zc (t + 1) + b + c) else 0) +
      (if t ≤ 0 then f n (zc (t - 1) + b + c) else 0)) =
      if t = 0 then 2 * f n (b + c) else f n (b + c) := by
  rcases lt_trichotomy t 0 with h | rfl | h
  · simp [zc, not_le.mpr h, h.le, h.ne, show t - 1 ≠ 0 by omega]
  · simp [zc]; ring
  · simp [zc, not_le.mpr h, h.le, h.ne', show t + 1 ≠ 0 by omega]

lemma pairY (n : ℕ) (t : ℤ) (a c : ℕ) :
    ((if 0 ≤ t then f n (a + zc (t + 1) + c) else 0) +
      (if t ≤ 0 then f n (a + zc (t - 1) + c) else 0)) =
      if t = 0 then 2 * f n (a + c) else f n (a + c) := by
  rcases lt_trichotomy t 0 with h | rfl | h
  · simp [zc, not_le.mpr h, h.le, h.ne, show t - 1 ≠ 0 by omega]
  · simp [zc]; ring
  · simp [zc, not_le.mpr h, h.le, h.ne', show t + 1 ≠ 0 by omega]

lemma pairZ (n : ℕ) (t : ℤ) (a b : ℕ) :
    ((if 0 ≤ t then f n (a + b + zc (t + 1)) else 0) +
      (if t ≤ 0 then f n (a + b + zc (t - 1)) else 0)) =
      if t = 0 then 2 * f n (a + b) else f n (a + b) := by
  rcases lt_trichotomy t 0 with h | rfl | h
  · simp [zc, not_le.mpr h, h.le, h.ne, show t - 1 ≠ 0 by omega]
  · simp [zc]; ring
  · simp [zc, not_le.mpr h, h.le, h.ne', show t + 1 ≠ 0 by omega]

lemma count (n : ℕ) : ∀ q : ℤ × ℤ × ℤ, Nat.card {s : Fin n → Fin 6 // V q s} = f n (z q) := by
  induction n with
  | zero =>
    intro q
    have : ∀ s : Fin 0 → Fin 6, V q s := fun s k hk => absurd hk (Nat.not_lt_zero _)
    simp only [this]
    simp [f]
  | succ n ih =>
    rintro ⟨x, y, w⟩
    rw [card_cons]
    simp only [V_cons, card_and, ih]
    simp only [Fin.sum_univ_six, dir, sqDist, z, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, Prod.mk_add_mk, add_zero]
    have c0 : (x ^ 2 + y ^ 2 + w ^ 2 ≤ (x + 1) ^ 2 + y ^ 2 + w ^ 2) ↔ 0 ≤ x := by
      constructor <;> intro h <;> nlinarith
    have c1 : (x ^ 2 + y ^ 2 + w ^ 2 ≤ (x - 1) ^ 2 + y ^ 2 + w ^ 2) ↔ x ≤ 0 := by
      constructor <;> intro h <;> nlinarith
    have c2 : (x ^ 2 + y ^ 2 + w ^ 2 ≤ x ^ 2 + (y + 1) ^ 2 + w ^ 2) ↔ 0 ≤ y := by
      constructor <;> intro h <;> nlinarith
    have c3 : (x ^ 2 + y ^ 2 + w ^ 2 ≤ x ^ 2 + (y - 1) ^ 2 + w ^ 2) ↔ y ≤ 0 := by
      constructor <;> intro h <;> nlinarith
    have c4 : (x ^ 2 + y ^ 2 + w ^ 2 ≤ x ^ 2 + y ^ 2 + (w + 1) ^ 2) ↔ 0 ≤ w := by
      constructor <;> intro h <;> nlinarith
    have c5 : (x ^ 2 + y ^ 2 + w ^ 2 ≤ x ^ 2 + y ^ 2 + (w - 1) ^ 2) ↔ w ≤ 0 := by
      constructor <;> intro h <;> nlinarith
    simp only [← sub_eq_add_neg]
    simp only [c0, c1, c2, c3, c4, c5]
    rw [show ∀ a b c d e g : ℕ, a + b + c + d + e + g = (a + b) + (c + d) + (e + g) from by
      intros; ring]
    rw [pairX, pairY, pairZ]
    rcases eq_or_ne x 0 with hx | hx <;> rcases eq_or_ne y 0 with hy | hy <;>
      rcases eq_or_ne w 0 with hw | hw <;> simp [hx, hy, hw, zc, f] <;> ring


lemma f0 (m : ℕ) : (f m 0 : ℤ) = 3 ^ m := by
  induction m with
  | zero => simp [f]
  | succ m ih => simp only [f]; push_cast; rw [ih]; ring

lemma f1 (m : ℕ) : (f m 1 : ℤ) = 2 * 3 ^ m - 2 ^ m := by
  induction m with
  | zero => simp [f]
  | succ m ih => simp only [f]; push_cast; rw [ih, f0]; ring

lemma f2 (m : ℕ) : (f m 2 : ℤ) = 4 * 3 ^ m - 4 * 2 ^ m + 1 := by
  induction m with
  | zero => simp [f]
  | succ m ih => simp only [f]; push_cast; rw [ih, f1]; ring

lemma pos_succ {n : ℕ} (s : Fin n → Fin 6) (k : ℕ) (hk : k < n) :
    pos s (k + 1) = pos s k + dir (s ⟨k, hk⟩) := by
  unfold pos
  rw [List.take_add_one, List.map_append, List.sum_append]
  simp [hk]

def L1 (p : ℤ × ℤ × ℤ) : ℤ := |p.1| + |p.2.1| + |p.2.2|

lemma absP (x : ℤ) (h : 0 ≤ x) : |x + 1| = |x| + 1 := by
  rw [abs_of_nonneg h, abs_of_nonneg (by omega)]

lemma absN (x : ℤ) (h : x ≤ 0) : |x + -1| = |x| + 1 := by
  rw [abs_of_nonpos h, abs_of_nonpos (by omega)]; ring

lemma step (p : ℤ × ℤ × ℤ) (d : Fin 6) (h : sqDist p ≤ sqDist (p + dir d)) :
    L1 (p + dir d) = L1 p + 1 := by
  obtain ⟨x, y, w⟩ := p
  fin_cases d <;> simp [dir, sqDist, L1] at h ⊢
  · rw [absP x (by nlinarith)]; ring
  · rw [absN x (by nlinarith)]; ring
  · rw [absP y (by nlinarith)]; ring
  · rw [absN y (by nlinarith)]; ring
  · rw [absP w (by nlinarith)]; ring
  · rw [absN w (by nlinarith)]; ring

lemma L1_pos {n : ℕ} (s : Fin n → Fin 6) (h : V 0 s) : ∀ k, k ≤ n → L1 (pos s k) = k := by
  intro k
  induction k with
  | zero => intro _; simp [pos_zero, L1]
  | succ k ih =>
    intro hk
    have hk' : k < n := by omega
    have hv := h k hk'
    rw [zero_add, zero_add, pos_succ s k hk'] at hv
    rw [pos_succ s k hk', step _ _ hv, ih (by omega)]
    push_cast; ring

lemma isWalk_iff {n : ℕ} (s : Fin n → Fin 6) : IsWalk s ↔ V 0 s := by
  constructor
  · intro h k hk
    rw [zero_add, zero_add]
    exact h.2 k hk
  · intro h
    refine ⟨fun i j hi hj hij => ?_, fun k hk => by simpa using h k hk⟩
    have h1 := L1_pos s h i hi
    have h2 := L1_pos s h j hj
    rw [hij] at h1
    omega

end OMA.P_oeis_a366058

open OMA.P_oeis_a366058 in
theorem OMA.solution : type_of% @OMA.S_oeis_a366058.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h1 : a (m + 1) = Nat.card {s : Fin (m + 1) → Fin 6 // V 0 s} :=
    Nat.card_congr (Equiv.subtypeEquivRight isWalk_iff)
  have hz : z 0 = 3 := by simp [z, zc]
  rw [h1, count, hz]
  simp only [f]
  push_cast
  rw [f2]
  simp

