import OMAStatements.S_oeis_a245954
import Mathlib

namespace OMA.Helpers_a245954
open OMA.S_oeis_a245954

def ch (n : ℕ) : (m : ℕ) → ℕ → ℕ → ℕ → (Fin m → Fin (n + 1)) → Bool
  | 0, _, _, _, _ => true
  | m + 1, a, b, c, y => decide (a + b = n ∨ a + c = n ∨ b + c = n ∨ a + (y 0 : ℕ) = n ∨
      b + (y 0 : ℕ) = n ∨ c + (y 0 : ℕ) = n) && ch n m b c (y 0) (Fin.tail y)

def T (n : ℕ) : ℕ → ℕ → ℕ → ℕ → ℤ
  | 0, _, _, _ => 1
  | m + 1, a, b, c => ∑ v ∈ Finset.range (n + 1),
      if a + b = n ∨ a + c = n ∨ b + c = n ∨ a + v = n ∨ b + v = n ∨ c + v = n then T n m b c v else 0

theorem sum_cons {n m : ℕ} (f : (Fin (m + 1) → Fin (n + 1)) → ℤ) :
    ∑ y, f y = ∑ v : Fin (n + 1), ∑ z : Fin m → Fin (n + 1), f (Fin.cons v z) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.consEquiv fun _ => Fin (n + 1)) _ _ (fun p => rfl)).symm

theorem cnt (n : ℕ) : ∀ m a b c, (((Finset.univ : Finset (Fin m → Fin (n + 1))).filter
    (fun y => ch n m a b c y = true)).card : ℤ) = T n m a b c := by
  intro m
  induction m with
  | zero => intro a b c; simp [ch, T]
  | succ m ih =>
    intro a b c
    rw [Finset.card_filter, Nat.cast_sum, sum_cons, T,
      ← Fin.sum_univ_eq_sum_range (fun v => if a + b = n ∨ a + c = n ∨ b + c = n ∨ a + v = n ∨
        b + v = n ∨ c + v = n then T n m b c v else 0)]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    simp only [ch, Fin.cons_zero, Fin.tail_cons, Bool.and_eq_true, decide_eq_true_eq]
    split_ifs with h
    · rw [← ih b c v, Finset.card_filter, Nat.cast_sum]
      refine Finset.sum_congr rfl (fun z _ => ?_)
      simp [h]
    · simp [h]

theorem win {n : ℕ} (x : Fin 7 → Fin (n + 1)) (i : ℕ) :
    (∃ s < (4 : ℕ), ∃ t < (4 : ℕ), s < t ∧ get x (i + s) + get x (i + t) = n) ↔
      (get x i + get x (i + 1) = n ∨ get x i + get x (i + 2) = n ∨ get x (i + 1) + get x (i + 2) = n ∨
       get x i + get x (i + 3) = n ∨ get x (i + 1) + get x (i + 3) = n ∨
       get x (i + 2) + get x (i + 3) = n) := by
  constructor
  · rintro ⟨s, hs, t, ht, hst, e⟩
    interval_cases s <;> interval_cases t <;> simp_all
  · rintro (h | h | h | h | h | h)
    · exact ⟨0, by norm_num, 1, by norm_num, by norm_num, by simpa using h⟩
    · exact ⟨0, by norm_num, 2, by norm_num, by norm_num, by simpa using h⟩
    · exact ⟨1, by norm_num, 2, by norm_num, by norm_num, h⟩
    · exact ⟨0, by norm_num, 3, by norm_num, by norm_num, by simpa using h⟩
    · exact ⟨1, by norm_num, 3, by norm_num, by norm_num, h⟩
    · exact ⟨2, by norm_num, 3, by norm_num, by norm_num, h⟩

theorem good_iff {n : ℕ} (x : Fin 7 → Fin (n + 1)) :
    good x = ch n 4 (x 0) (x 1) (x 2) (fun i => x ⟨i + 3, by omega⟩) := by
  apply Bool.eq_iff_iff.mpr
  simp only [good, decide_eq_true_eq, win]
  simp only [ch, Bool.and_eq_true, decide_eq_true_eq, and_true]
  simp only [Fin.tail, Fin.val_succ, Fin.val_zero, S_oeis_a245954.get]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · have := h 0 (by norm_num); simpa using this
    · have := h 1 (by norm_num); simpa using this
    · have := h 2 (by norm_num); simpa using this
    · have := h 3 (by norm_num); simpa using this
  · rintro ⟨h0, h1, h2, h3⟩ i hi
    interval_cases i <;> simp_all

theorem a_eq (n : ℕ) : a n = ∑ p ∈ Finset.range (n + 1), ∑ q ∈ Finset.range (n + 1),
    ∑ r ∈ Finset.range (n + 1), T n 4 p q r := by
  unfold a
  rw [Finset.card_filter, Nat.cast_sum, sum_cons]
  rw [← Fin.sum_univ_eq_sum_range (fun p => ∑ q ∈ Finset.range (n + 1), ∑ r ∈ Finset.range (n + 1), T n 4 p q r)]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [sum_cons, ← Fin.sum_univ_eq_sum_range (fun q => ∑ r ∈ Finset.range (n + 1), T n 4 p q r)]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [sum_cons, ← Fin.sum_univ_eq_sum_range (fun r => T n 4 p q r)]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [← cnt, Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  rw [good_iff]
  rfl


def SS4 (N : ℤ) (e : Bool) (G : Bool → Bool → Bool → Bool → Bool → ℤ) (E P Ha Hb : Bool) : ℤ :=
  if E then
    (if Ha then G true true true true true + N * G false false false false false
     else G true true false false false + G false false true true false +
       (if e then G false false false false true else 0) +
       (N - 1 - (if e then 1 else 0)) * G false false false false false)
  else if P then
    G true false false true false + G false true true false false +
      (if e then G false false false false true else 0) +
      (N - 1 - (if e then 1 else 0)) * G false false false false false
  else if Ha then
    G true false true false true + G false true false false false + G false false false true false +
      (N - 2) * G false false false false false
  else if Hb then
    G false true false true true + G true false false false false + G false false true false false +
      (N - 2) * G false false false false false
  else
    G true false false false false + G false true false false false + G false false true false false +
      G false false false true false + (if e then G false false false false true else 0) +
      (N - 3 - (if e then 1 else 0)) * G false false false false false

def SS (N : ℤ) (e : Bool) (G : Bool → Bool → Bool → Bool → ℤ) (Hb : Bool) : ℤ :=
  if Hb then G true true true true + N * G false false true false
  else G true false false false + G false true false false +
    (if e then G false false false true else 0) +
    (N - 1 - (if e then 1 else 0)) * G false false false false

def Φ (n : ℤ) (e : Bool) : ℕ → Bool → Bool → Bool → Bool → Bool → Bool → Bool → Bool → Bool → ℤ
  | 0, _, _, _, _, _, _, _, _, _ => 1
  | m + 1, Eab, Eac, Ebc, Pab, Pac, Pbc, Ha, Hb, Hc =>
    if Pab = true ∨ Pac = true ∨ Pbc = true then
      SS4 n e (fun x1 x2 x3 x4 x5 => Φ n e m Ebc x1 x2 Pbc x3 x4 Hb Hc x5) Ebc Pbc Hb Hc
    else Φ n e m Ebc Pab Pac Pbc Eab Eac Hb Hc Ha +
      (if Eab then 0 else Φ n e m Ebc Hb Pbc Pbc true Ebc Hb Hc Hb) +
      (if Eac = true ∨ Ebc = true then 0 else Φ n e m Ebc Pbc Hc Pbc Ebc true Hb Hc Hc)

theorem Φ0 (n : ℤ) (e E1 E2 E3 P1 P2 P3 H1 H2 H3 : Bool) : Φ n e 0 E1 E2 E3 P1 P2 P3 H1 H2 H3 = 1 := rfl

theorem sum_half (n : ℕ) (c : ℤ) :
    ∑ v ∈ Finset.range (n + 1), (if 2 * v = n then c else 0) = if decide (Even n) = true then c else 0 := by
  simp only [decide_eq_true_eq]
  split_ifs with h
  · obtain ⟨k, rfl⟩ := h
    rw [Finset.sum_congr rfl (g := fun v => if v = k then c else 0) (fun v _ => by
      congr 1; apply propext; omega)]
    rw [Finset.sum_ite_eq']
    simp
  · apply Finset.sum_eq_zero
    intro v _
    rw [if_neg]
    intro h2; exact h ⟨v, by omega⟩

theorem sum_pt (n x : ℕ) (hx : x ≤ n) (c : ℤ) :
    ∑ v ∈ Finset.range (n + 1), (if v = x then c else 0) = c := by
  rw [Finset.sum_ite_eq']; simp; omega

theorem sum_const' (n : ℕ) (c : ℤ) : ∑ _v ∈ Finset.range (n + 1), c = ((n : ℤ) + 1) * c := by
  simp

theorem L3 (n b : ℕ) (hb : b ≤ n) (G : Bool → Bool → Bool → Bool → ℤ) :
    ∑ v ∈ Finset.range (n + 1), G (decide (b = v)) (decide (b + v = n)) (decide (2 * b = n))
      (decide (2 * v = n)) = SS n (decide (Even n)) G (decide (2 * b = n)) := by
  by_cases h : 2 * b = n
  · have : ∀ v ∈ Finset.range (n + 1), G (decide (b = v)) (decide (b + v = n)) (decide (2 * b = n))
        (decide (2 * v = n)) = G false false true false +
          (if v = b then G true true true true - G false false true false else 0) := by
      intro v _
      split_ifs <;>
        (try rw [decide_eq_true (show b = v by omega)]) <;>
        (try rw [decide_eq_false (show ¬ b = v by omega)]) <;>
        (try rw [decide_eq_true (show b + v = n by omega)]) <;>
        (try rw [decide_eq_false (show ¬ b + v = n by omega)]) <;>
        (try rw [decide_eq_true (show 2 * b = n by omega)]) <;>
        (try rw [decide_eq_true (show 2 * v = n by omega)]) <;>
        (try rw [decide_eq_false (show ¬ 2 * v = n by omega)]) <;>
        first | (exfalso; omega) | ring
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, sum_pt n b hb, sum_const']
    simp only [SS, decide_eq_true h, if_true]
    ring
  · have : ∀ v ∈ Finset.range (n + 1), G (decide (b = v)) (decide (b + v = n)) (decide (2 * b = n))
        (decide (2 * v = n)) = G false false false false +
          (if v = b then G true false false false - G false false false false else 0) +
          (if v = n - b then G false true false false - G false false false false else 0) +
          (if 2 * v = n then G false false false true - G false false false false else 0) := by
      intro v _
      rw [decide_eq_false h]
      split_ifs <;>
        (try rw [decide_eq_true (show b = v by omega)]) <;>
        (try rw [decide_eq_false (show ¬ b = v by omega)]) <;>
        (try rw [decide_eq_true (show b + v = n by omega)]) <;>
        (try rw [decide_eq_false (show ¬ b + v = n by omega)]) <;>
        (try rw [decide_eq_true (show 2 * v = n by omega)]) <;>
        (try rw [decide_eq_false (show ¬ 2 * v = n by omega)]) <;>
        first | (exfalso; omega) | ring
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib, sum_pt n b hb, sum_pt n (n - b) (by omega), sum_half, sum_const']
    simp only [SS, decide_eq_false h, Bool.false_eq_true, if_false]
    split_ifs <;> ring

theorem L3' (n b c : ℕ) (hb : b ≤ n) (hc : c ≤ n) (G : Bool → Bool → Bool → Bool → Bool → ℤ) :
    ∑ v ∈ Finset.range (n + 1), G (decide (b = v)) (decide (c = v)) (decide (b + v = n))
      (decide (c + v = n)) (decide (2 * v = n)) =
      SS4 n (decide (Even n)) G (decide (b = c)) (decide (b + c = n)) (decide (2 * b = n))
        (decide (2 * c = n)) := by
  by_cases E : b = c
  · subst E
    by_cases H : 2 * b = n
    · have : ∀ v ∈ Finset.range (n + 1), G (decide (b = v)) (decide (b = v)) (decide (b + v = n))
          (decide (b + v = n)) (decide (2 * v = n)) = G false false false false false +
            (if v = b then G true true true true true - G false false false false false else 0) := by
        intro v _
        split_ifs <;>
          (try rw [decide_eq_true (show b = v by omega)]) <;>
          (try rw [decide_eq_false (show ¬ b = v by omega)]) <;>
          (try rw [decide_eq_true (show b + v = n by omega)]) <;>
          (try rw [decide_eq_false (show ¬ b + v = n by omega)]) <;>
          (try rw [decide_eq_true (show 2 * v = n by omega)]) <;>
          (try rw [decide_eq_false (show ¬ 2 * v = n by omega)]) <;>
          first | (exfalso; omega) | ring
      rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, sum_pt n b hb, sum_const']
      rw [show decide (b = b) = true from decide_eq_true rfl,
        show decide (b + b = n) = true from decide_eq_true (by omega), decide_eq_true H]
      simp only [SS4, if_true]
      ring
    · have : ∀ v ∈ Finset.range (n + 1), G (decide (b = v)) (decide (b = v)) (decide (b + v = n))
          (decide (b + v = n)) (decide (2 * v = n)) = G false false false false false +
            (if v = b then G true true false false false - G false false false false false else 0) +
            (if v = n - b then G false false true true false - G false false false false false else 0) +
            (if 2 * v = n then G false false false false true - G false false false false false else 0) := by
        intro v _
        split_ifs <;>
          (try rw [decide_eq_true (show b = v by omega)]) <;>
          (try rw [decide_eq_false (show ¬ b = v by omega)]) <;>
          (try rw [decide_eq_true (show b + v = n by omega)]) <;>
          (try rw [decide_eq_false (show ¬ b + v = n by omega)]) <;>
          (try rw [decide_eq_true (show 2 * v = n by omega)]) <;>
          (try rw [decide_eq_false (show ¬ 2 * v = n by omega)]) <;>
          first | (exfalso; omega) | ring
      rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.sum_add_distrib, sum_pt n b hb, sum_pt n (n - b) (by omega), sum_half, sum_const']
      rw [show decide (b = b) = true from decide_eq_true rfl,
        show decide (b + b = n) = false from decide_eq_false (by omega), decide_eq_false H]
      simp only [SS4, if_true, Bool.false_eq_true, if_false]
      split_ifs <;> ring
  by_cases P : b + c = n
  · have : ∀ v ∈ Finset.range (n + 1), G (decide (b = v)) (decide (c = v)) (decide (b + v = n))
        (decide (c + v = n)) (decide (2 * v = n)) = G false false false false false +
          (if v = b then G true false false true false - G false false false false false else 0) +
          (if v = c then G false true true false false - G false false false false false else 0) +
          (if 2 * v = n then G false false false false true - G false false false false false else 0) := by
      intro v _
      split_ifs <;>
        (try rw [decide_eq_true (show b = v by omega)]) <;>
        (try rw [decide_eq_false (show ¬ b = v by omega)]) <;>
        (try rw [decide_eq_true (show c = v by omega)]) <;>
        (try rw [decide_eq_false (show ¬ c = v by omega)]) <;>
        (try rw [decide_eq_true (show b + v = n by omega)]) <;>
        (try rw [decide_eq_false (show ¬ b + v = n by omega)]) <;>
        (try rw [decide_eq_true (show c + v = n by omega)]) <;>
        (try rw [decide_eq_false (show ¬ c + v = n by omega)]) <;>
        (try rw [decide_eq_true (show 2 * v = n by omega)]) <;>
        (try rw [decide_eq_false (show ¬ 2 * v = n by omega)]) <;>
        first | (exfalso; omega) | ring
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib, sum_pt n b hb, sum_pt n c hc, sum_half, sum_const']
    simp only [SS4, decide_eq_false E, decide_eq_true P, if_true, Bool.false_eq_true, if_false]
    split_ifs <;> ring
  by_cases Hb : 2 * b = n
  · have : ∀ v ∈ Finset.range (n + 1), G (decide (b = v)) (decide (c = v)) (decide (b + v = n))
        (decide (c + v = n)) (decide (2 * v = n)) = G false false false false false +
          (if v = b then G true false true false true - G false false false false false else 0) +
          (if v = c then G false true false false false - G false false false false false else 0) +
          (if v = n - c then G false false false true false - G false false false false false else 0) := by
      intro v _
      split_ifs <;>
        (try rw [decide_eq_true (show b = v by omega)]) <;>
        (try rw [decide_eq_false (show ¬ b = v by omega)]) <;>
        (try rw [decide_eq_true (show c = v by omega)]) <;>
        (try rw [decide_eq_false (show ¬ c = v by omega)]) <;>
        (try rw [decide_eq_true (show b + v = n by omega)]) <;>
        (try rw [decide_eq_false (show ¬ b + v = n by omega)]) <;>
        (try rw [decide_eq_true (show c + v = n by omega)]) <;>
        (try rw [decide_eq_false (show ¬ c + v = n by omega)]) <;>
        (try rw [decide_eq_true (show 2 * v = n by omega)]) <;>
        (try rw [decide_eq_false (show ¬ 2 * v = n by omega)]) <;>
        first | (exfalso; omega) | ring
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib, sum_pt n b hb, sum_pt n c hc, sum_pt n (n - c) (by omega), sum_const']
    simp only [SS4, decide_eq_false E, decide_eq_false P, decide_eq_true Hb, if_true, Bool.false_eq_true,
      if_false]
    ring
  by_cases Hc : 2 * c = n
  · have : ∀ v ∈ Finset.range (n + 1), G (decide (b = v)) (decide (c = v)) (decide (b + v = n))
        (decide (c + v = n)) (decide (2 * v = n)) = G false false false false false +
          (if v = c then G false true false true true - G false false false false false else 0) +
          (if v = b then G true false false false false - G false false false false false else 0) +
          (if v = n - b then G false false true false false - G false false false false false else 0) := by
      intro v _
      split_ifs <;>
        (try rw [decide_eq_true (show b = v by omega)]) <;>
        (try rw [decide_eq_false (show ¬ b = v by omega)]) <;>
        (try rw [decide_eq_true (show c = v by omega)]) <;>
        (try rw [decide_eq_false (show ¬ c = v by omega)]) <;>
        (try rw [decide_eq_true (show b + v = n by omega)]) <;>
        (try rw [decide_eq_false (show ¬ b + v = n by omega)]) <;>
        (try rw [decide_eq_true (show c + v = n by omega)]) <;>
        (try rw [decide_eq_false (show ¬ c + v = n by omega)]) <;>
        (try rw [decide_eq_true (show 2 * v = n by omega)]) <;>
        (try rw [decide_eq_false (show ¬ 2 * v = n by omega)]) <;>
        first | (exfalso; omega) | ring
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib, sum_pt n c hc, sum_pt n b hb, sum_pt n (n - b) (by omega), sum_const']
    simp only [SS4, decide_eq_false E, decide_eq_false P, decide_eq_false Hb, decide_eq_true Hc,
      if_true, Bool.false_eq_true, if_false]
    ring
  · have : ∀ v ∈ Finset.range (n + 1), G (decide (b = v)) (decide (c = v)) (decide (b + v = n))
        (decide (c + v = n)) (decide (2 * v = n)) = G false false false false false +
          (if v = b then G true false false false false - G false false false false false else 0) +
          (if v = c then G false true false false false - G false false false false false else 0) +
          (if v = n - b then G false false true false false - G false false false false false else 0) +
          (if v = n - c then G false false false true false - G false false false false false else 0) +
          (if 2 * v = n then G false false false false true - G false false false false false else 0) := by
      intro v _
      split_ifs <;>
        (try rw [decide_eq_true (show b = v by omega)]) <;>
        (try rw [decide_eq_false (show ¬ b = v by omega)]) <;>
        (try rw [decide_eq_true (show c = v by omega)]) <;>
        (try rw [decide_eq_false (show ¬ c = v by omega)]) <;>
        (try rw [decide_eq_true (show b + v = n by omega)]) <;>
        (try rw [decide_eq_false (show ¬ b + v = n by omega)]) <;>
        (try rw [decide_eq_true (show c + v = n by omega)]) <;>
        (try rw [decide_eq_false (show ¬ c + v = n by omega)]) <;>
        (try rw [decide_eq_true (show 2 * v = n by omega)]) <;>
        (try rw [decide_eq_false (show ¬ 2 * v = n by omega)]) <;>
        first | (exfalso; omega) | ring
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, sum_pt n b hb,
      sum_pt n c hc, sum_pt n (n - b) (by omega), sum_pt n (n - c) (by omega), sum_half, sum_const']
    simp only [SS4, decide_eq_false E, decide_eq_false P, decide_eq_false Hb, decide_eq_false Hc,
      Bool.false_eq_true, if_false]
    split_ifs <;> ring

theorem Pe1_000000000 (n : ℤ) : Φ n true 1 false false false false false false false false false = 3 := by
  rw [Φ]
  simp only [↓reduceIte, Bool.false_eq_true, or_self, Φ0]
  ring

theorem Pe1_000000001 (n : ℤ) : Φ n true 1 false false false false false false false false true = 3 := by
  rw [Φ]
  simp only [↓reduceIte, Bool.false_eq_true, or_self, Φ0]
  ring

theorem Pe1_000000010 (n : ℤ) : Φ n true 1 false false false false false false false true false = 3 := by
  rw [Φ]
  simp only [↓reduceIte, Bool.false_eq_true, or_self, Φ0]
  ring

theorem Pe1_000000100 (n : ℤ) : Φ n true 1 false false false false false false true false false = 3 := by
  rw [Φ]
  simp only [↓reduceIte, Bool.false_eq_true, or_self, Φ0]
  ring

theorem Pe1_000001000 (n : ℤ) : Φ n true 1 false false false false false true false false false = n + 1 := by
  rw [Φ]
  simp only [SS4, ↓reduceIte, Bool.false_eq_true, or_true, Φ0]
  ring

theorem Pe1_000001100 (n : ℤ) : Φ n true 1 false false false false false true true false false = n + 1 := by
  rw [Φ]
  simp only [SS4, ↓reduceIte, Bool.false_eq_true, or_true, Φ0]
  ring

theorem Pe1_000010000 (n : ℤ) : Φ n true 1 false false false false true false false false false = n + 1 := by
  rw [Φ]
  simp only [SS4, ↓reduceIte, Bool.false_eq_true, true_or, or_true, Φ0]
  ring

theorem Pe1_000010010 (n : ℤ) : Φ n true 1 false false false false true false false true false = n + 1 := by
  rw [Φ]
  simp only [SS4, ↓reduceIte, Bool.false_eq_true, true_or, or_true, Φ0]
  ring

theorem Pe1_000100000 (n : ℤ) : Φ n true 1 false false false true false false false false false = n + 1 := by
  rw [Φ]
  simp only [SS4, ↓reduceIte, Bool.false_eq_true, true_or, or_self, Φ0]
  ring

theorem Pe1_000100001 (n : ℤ) : Φ n true 1 false false false true false false false false true = n + 1 := by
  rw [Φ]
  simp only [SS4, ↓reduceIte, Bool.false_eq_true, true_or, or_self, Φ0]
  ring

theorem Pe1_001000000 (n : ℤ) : Φ n true 1 false false true false false false false false false = 2 := by
  rw [Φ]
  simp only [↓reduceIte, Bool.false_eq_true, or_true, or_self, Φ0]
  ring

theorem Pe1_001000100 (n : ℤ) : Φ n true 1 false false true false false false true false false = 2 := by
  rw [Φ]
  simp only [↓reduceIte, Bool.false_eq_true, or_true, or_self, Φ0]
  ring

theorem Pe1_001001011 (n : ℤ) : Φ n true 1 false false true false false true false true true = n + 1 := by
  rw [Φ]
  simp only [SS4, ↓reduceIte, Bool.false_eq_true, or_true, Φ0]
  ring

theorem Pe1_001110000 (n : ℤ) : Φ n true 1 false false true true true false false false false = n + 1 := by
  rw [Φ]
  simp only [SS4, ↓reduceIte, Bool.false_eq_true, true_or, or_self, Φ0]
  ring

theorem Pe1_010000000 (n : ℤ) : Φ n true 1 false true false false false false false false false = 2 := by
  rw [Φ]
  simp only [↓reduceIte, Bool.false_eq_true, true_or, or_self, Φ0]
  ring

theorem Pe1_010000010 (n : ℤ) : Φ n true 1 false true false false false false false true false = 2 := by
  rw [Φ]
  simp only [↓reduceIte, Bool.false_eq_true, true_or, or_self, Φ0]
  ring

theorem Pe1_010010101 (n : ℤ) : Φ n true 1 false true false false true false true false true = n + 1 := by
  rw [Φ]
  simp only [SS4, ↓reduceIte, Bool.false_eq_true, true_or, or_true, Φ0]
  ring

theorem Pe1_010101000 (n : ℤ) : Φ n true 1 false true false true false true false false false = n + 1 := by
  rw [Φ]
  simp only [SS4, ↓reduceIte, Bool.false_eq_true, or_true, or_self, Φ0]
  ring

theorem Pe1_100000000 (n : ℤ) : Φ n true 1 true false false false false false false false false = 2 := by
  rw [Φ]
  simp only [↓reduceIte, Bool.false_eq_true, or_self, Φ0]
  ring

theorem Pe1_100000001 (n : ℤ) : Φ n true 1 true false false false false false false false true = 2 := by
  rw [Φ]
  simp only [↓reduceIte, Bool.false_eq_true, or_self, Φ0]
  ring

theorem Pe1_100011000 (n : ℤ) : Φ n true 1 true false false false true true false false false = n + 1 := by
  rw [Φ]
  simp only [SS4, ↓reduceIte, Bool.false_eq_true, or_true, or_self, Φ0]
  ring

theorem Pe1_100100110 (n : ℤ) : Φ n true 1 true false false true false false true true false = n + 1 := by
  rw [Φ]
  simp only [SS4, ↓reduceIte, Bool.false_eq_true, true_or, or_self, Φ0]
  ring

theorem Pe1_111000000 (n : ℤ) : Φ n true 1 true true true false false false false false false = 1 := by
  rw [Φ]
  simp only [↓reduceIte, Bool.false_eq_true, or_self, Φ0]
  ring

theorem Pe1_111111111 (n : ℤ) : Φ n true 1 true true true true true true true true true = n + 1 := by
  rw [Φ]
  simp only [SS4, ↓reduceIte, or_self, Φ0]
  ring

theorem Pe2_000000000 (n : ℤ) : Φ n true 2 false false false false false false false false false = 2*n + 5 := by
  rw [Φ]
  simp only [↓reduceIte, Bool.false_eq_true, or_self, Pe1_000000000, Pe1_000001000, Pe1_000010000]
  ring

theorem Pe2_000000001 (n : ℤ) : Φ n true 2 false false false false false false false false true = 2*n + 5 := by
  rw [Φ]
  simp only [↓reduceIte, Bool.false_eq_true, or_self, Pe1_000000010, Pe1_000010010, Pe1_001001011]
  ring

theorem Pe2_000000010 (n : ℤ) : Φ n true 2 false false false false false false false true false = 2*n + 5 := by
  rw [Φ]
  simp only [↓reduceIte, Bool.false_eq_true, or_self, Pe1_000000100, Pe1_000001100, Pe1_010010101]
  ring

theorem Pe2_000000100 (n : ℤ) : Φ n true 2 false false false false false false true false false = 2*n + 5 := by
  rw [Φ]
  simp only [↓reduceIte, Bool.false_eq_true, or_self, Pe1_000000001, Pe1_000001000, Pe1_000010000]
  ring

theorem Pe2_000001000 (n : ℤ) : Φ n true 2 false false false false false true false false false = n^2 + 2*n + 1 := by
  rw [Φ]
  simp only [SS4, ↓reduceIte, Bool.false_eq_true, or_true, Pe1_000100000, Pe1_000100001, Pe1_001110000, Pe1_010101000]
  ring

theorem Pe2_000001100 (n : ℤ) : Φ n true 2 false false false false false true true false false = n^2 + 2*n + 1 := by
  rw [Φ]
  simp only [SS4, ↓reduceIte, Bool.false_eq_true, or_true, Pe1_000100000, Pe1_000100001, Pe1_001110000, Pe1_010101000]
  ring

theorem Pe2_000010000 (n : ℤ) : Φ n true 2 false false false false true false false false false = 5*n - 3 := by
  rw [Φ]
  simp only [SS4, ↓reduceIte, Bool.false_eq_true, true_or, or_true, Pe1_000000000, Pe1_000000001, Pe1_000001000, Pe1_000010000, Pe1_001000000, Pe1_010000000]
  ring

theorem Pe2_000010010 (n : ℤ) : Φ n true 2 false false false false true false false true false = 5*n - 2 := by
  rw [Φ]
  simp only [SS4, ↓reduceIte, Bool.false_eq_true, true_or, or_true, Pe1_000000100, Pe1_000001100, Pe1_001000100, Pe1_010010101]
  ring

theorem Pe2_000100000 (n : ℤ) : Φ n true 2 false false false true false false false false false = 5*n - 3 := by
  rw [Φ]
  simp only [SS4, ↓reduceIte, Bool.false_eq_true, true_or, or_self, Pe1_000000000, Pe1_000000001, Pe1_000001000, Pe1_000010000, Pe1_001000000, Pe1_010000000]
  ring

theorem Pe2_000100001 (n : ℤ) : Φ n true 2 false false false true false false false false true = 5*n - 2 := by
  rw [Φ]
  simp only [SS4, ↓reduceIte, Bool.false_eq_true, true_or, or_self, Pe1_000000010, Pe1_000010010, Pe1_001001011, Pe1_010000010]
  ring

theorem Pe2_001000000 (n : ℤ) : Φ n true 2 false false true false false false false false false = n + 3 := by
  rw [Φ]
  simp only [↓reduceIte, Bool.false_eq_true, or_true, or_self, Pe1_100000000, Pe1_100011000]
  ring

theorem Pe2_001000100 (n : ℤ) : Φ n true 2 false false true false false false true false false = n + 3 := by
  rw [Φ]
  simp only [↓reduceIte, Bool.false_eq_true, or_true, or_self, Pe1_100000001, Pe1_100011000]
  ring

theorem Pe2_001001011 (n : ℤ) : Φ n true 2 false false true false false true false true true = n^2 + 2*n + 1 := by
  rw [Φ]
  simp only [SS4, ↓reduceIte, Bool.false_eq_true, or_true, Pe1_100100110, Pe1_111111111]
  ring

theorem Pe2_001110000 (n : ℤ) : Φ n true 2 false false true true true false false false false = 3*n := by
  rw [Φ]
  simp only [SS4, ↓reduceIte, Bool.false_eq_true, true_or, or_self, Pe1_100000000, Pe1_100000001, Pe1_100011000, Pe1_111000000]
  ring

theorem Pe2_010000000 (n : ℤ) : Φ n true 2 false true false false false false false false false = 2*n + 2 := by
  rw [Φ]
  simp only [↓reduceIte, Bool.false_eq_true, true_or, or_self, Pe1_000001000, Pe1_000010000]
  ring

theorem Pe2_010000010 (n : ℤ) : Φ n true 2 false true false false false false false true false = 2*n + 2 := by
  rw [Φ]
  simp only [↓reduceIte, Bool.false_eq_true, true_or, or_self, Pe1_000001100, Pe1_010010101]
  ring

theorem Pe2_010010101 (n : ℤ) : Φ n true 2 false true false false true false true false true = 5*n - 2 := by
  rw [Φ]
  simp only [SS4, ↓reduceIte, Bool.false_eq_true, true_or, or_true, Pe1_000000010, Pe1_000010010, Pe1_001001011, Pe1_010000010]
  ring

theorem Pe2_010101000 (n : ℤ) : Φ n true 2 false true false true false true false false false = n^2 + 2*n + 1 := by
  rw [Φ]
  simp only [SS4, ↓reduceIte, Bool.false_eq_true, or_true, or_self, Pe1_000100000, Pe1_000100001, Pe1_001110000, Pe1_010101000]
  ring

theorem Pe2_100000000 (n : ℤ) : Φ n true 2 true false false false false false false false false = 2*n + 2 := by
  rw [Φ]
  simp only [↓reduceIte, Bool.false_eq_true, or_self, Pe1_000001000, Pe1_000010000]
  ring

theorem Pe2_100000001 (n : ℤ) : Φ n true 2 true false false false false false false false true = 2*n + 2 := by
  rw [Φ]
  simp only [↓reduceIte, Bool.false_eq_true, or_self, Pe1_000010010, Pe1_001001011]
  ring

theorem Pe2_100011000 (n : ℤ) : Φ n true 2 true false false false true true false false false = n^2 + 2*n + 1 := by
  rw [Φ]
  simp only [SS4, ↓reduceIte, Bool.false_eq_true, or_true, or_self, Pe1_000100000, Pe1_000100001, Pe1_001110000, Pe1_010101000]
  ring

theorem Pe2_100100110 (n : ℤ) : Φ n true 2 true false false true false false true true false = 5*n - 2 := by
  rw [Φ]
  simp only [SS4, ↓reduceIte, Bool.false_eq_true, true_or, or_self, Pe1_000000100, Pe1_000001100, Pe1_001000100, Pe1_010010101]
  ring

theorem Pe2_111000000 (n : ℤ) : Φ n true 2 true true true false false false false false false = n + 1 := by
  rw [Φ]
  simp only [↓reduceIte, Bool.false_eq_true, or_self, Pe1_100011000]
  ring

theorem Pe2_111111111 (n : ℤ) : Φ n true 2 true true true true true true true true true = n^2 + 2*n + 1 := by
  rw [Φ]
  simp only [SS4, ↓reduceIte, or_self, Pe1_100100110, Pe1_111111111]
  ring

theorem Pe3_000000000 (n : ℤ) : Φ n true 3 false false false false false false false false false = n^2 + 9*n + 3 := by
  rw [Φ]
  simp only [↓reduceIte, Bool.false_eq_true, or_self, Pe2_000000000, Pe2_000001000, Pe2_000010000]
  ring

theorem Pe3_000000001 (n : ℤ) : Φ n true 3 false false false false false false false false true = n^2 + 9*n + 4 := by
  rw [Φ]
  simp only [↓reduceIte, Bool.false_eq_true, or_self, Pe2_000000010, Pe2_000010010, Pe2_001001011]
  ring

theorem Pe3_000000010 (n : ℤ) : Φ n true 3 false false false false false false false true false = n^2 + 9*n + 4 := by
  rw [Φ]
  simp only [↓reduceIte, Bool.false_eq_true, or_self, Pe2_000000100, Pe2_000001100, Pe2_010010101]
  ring

theorem Pe3_000000100 (n : ℤ) : Φ n true 3 false false false false false false true false false = n^2 + 9*n + 3 := by
  rw [Φ]
  simp only [↓reduceIte, Bool.false_eq_true, or_self, Pe2_000000001, Pe2_000001000, Pe2_000010000]
  ring

theorem Pe3_000001000 (n : ℤ) : Φ n true 3 false false false false false true false false false = 6*n^2 - 3*n + 5 := by
  rw [Φ]
  simp only [SS4, ↓reduceIte, Bool.false_eq_true, or_true, Pe2_000100000, Pe2_000100001, Pe2_001110000, Pe2_010101000]
  ring

theorem Pe3_000001100 (n : ℤ) : Φ n true 3 false false false false false true true false false = 6*n^2 - 3*n + 5 := by
  rw [Φ]
  simp only [SS4, ↓reduceIte, Bool.false_eq_true, or_true, Pe2_000100000, Pe2_000100001, Pe2_001110000, Pe2_010101000]
  ring

theorem Pe3_000010000 (n : ℤ) : Φ n true 3 false false false false true false false false false = 3*n^2 + 9*n - 12 := by
  rw [Φ]
  simp only [SS4, ↓reduceIte, Bool.false_eq_true, true_or, or_true, Pe2_000000000, Pe2_000000001, Pe2_000001000, Pe2_000010000, Pe2_001000000, Pe2_010000000]
  ring

theorem Pe3_000010010 (n : ℤ) : Φ n true 3 false false false false true false false true false = 3*n^2 + 9*n - 8 := by
  rw [Φ]
  simp only [SS4, ↓reduceIte, Bool.false_eq_true, true_or, or_true, Pe2_000000100, Pe2_000001100, Pe2_001000100, Pe2_010010101]
  ring

theorem Pe3_000100000 (n : ℤ) : Φ n true 3 false false false true false false false false false = 3*n^2 + 9*n - 12 := by
  rw [Φ]
  simp only [SS4, ↓reduceIte, Bool.false_eq_true, true_or, or_self, Pe2_000000000, Pe2_000000001, Pe2_000001000, Pe2_000010000, Pe2_001000000, Pe2_010000000]
  ring

theorem Pe3_000100001 (n : ℤ) : Φ n true 3 false false false true false false false false true = 3*n^2 + 10*n - 9 := by
  rw [Φ]
  simp only [SS4, ↓reduceIte, Bool.false_eq_true, true_or, or_self, Pe2_000000010, Pe2_000010010, Pe2_001001011, Pe2_010000010]
  ring

theorem Pe3_001000000 (n : ℤ) : Φ n true 3 false false true false false false false false false = n^2 + 4*n + 3 := by
  rw [Φ]
  simp only [↓reduceIte, Bool.false_eq_true, or_true, or_self, Pe2_100000000, Pe2_100011000]
  ring

theorem Pe3_001000100 (n : ℤ) : Φ n true 3 false false true false false false true false false = n^2 + 4*n + 3 := by
  rw [Φ]
  simp only [↓reduceIte, Bool.false_eq_true, or_true, or_self, Pe2_100000001, Pe2_100011000]
  ring

theorem Pe3_001001011 (n : ℤ) : Φ n true 3 false false true false false true false true true = 6*n^2 + 1 := by
  rw [Φ]
  simp only [SS4, ↓reduceIte, Bool.false_eq_true, or_true, Pe2_100100110, Pe2_111111111]
  ring

theorem Pe3_001110000 (n : ℤ) : Φ n true 3 false false true true true false false false false = 3*n^2 + 3*n := by
  rw [Φ]
  simp only [SS4, ↓reduceIte, Bool.false_eq_true, true_or, or_self, Pe2_100000000, Pe2_100000001, Pe2_100011000, Pe2_111000000]
  ring

theorem Pe3_010000000 (n : ℤ) : Φ n true 3 false true false false false false false false false = n^2 + 7*n - 2 := by
  rw [Φ]
  simp only [↓reduceIte, Bool.false_eq_true, true_or, or_self, Pe2_000001000, Pe2_000010000]
  ring

theorem Pe3_010000010 (n : ℤ) : Φ n true 3 false true false false false false false true false = n^2 + 7*n - 1 := by
  rw [Φ]
  simp only [↓reduceIte, Bool.false_eq_true, true_or, or_self, Pe2_000001100, Pe2_010010101]
  ring

theorem Pe3_010010101 (n : ℤ) : Φ n true 3 false true false false true false true false true = 3*n^2 + 10*n - 9 := by
  rw [Φ]
  simp only [SS4, ↓reduceIte, Bool.false_eq_true, true_or, or_true, Pe2_000000010, Pe2_000010010, Pe2_001001011, Pe2_010000010]
  ring

theorem Pe3_010101000 (n : ℤ) : Φ n true 3 false true false true false true false false false = 6*n^2 - 3*n + 5 := by
  rw [Φ]
  simp only [SS4, ↓reduceIte, Bool.false_eq_true, or_true, or_self, Pe2_000100000, Pe2_000100001, Pe2_001110000, Pe2_010101000]
  ring

theorem Pe3_100000000 (n : ℤ) : Φ n true 3 true false false false false false false false false = n^2 + 7*n - 2 := by
  rw [Φ]
  simp only [↓reduceIte, Bool.false_eq_true, or_self, Pe2_000001000, Pe2_000010000]
  ring

theorem Pe3_100000001 (n : ℤ) : Φ n true 3 true false false false false false false false true = n^2 + 7*n - 1 := by
  rw [Φ]
  simp only [↓reduceIte, Bool.false_eq_true, or_self, Pe2_000010010, Pe2_001001011]
  ring

theorem Pe3_100011000 (n : ℤ) : Φ n true 3 true false false false true true false false false = 6*n^2 - 3*n + 5 := by
  rw [Φ]
  simp only [SS4, ↓reduceIte, Bool.false_eq_true, or_true, or_self, Pe2_000100000, Pe2_000100001, Pe2_001110000, Pe2_010101000]
  ring

theorem Pe3_100100110 (n : ℤ) : Φ n true 3 true false false true false false true true false = 3*n^2 + 9*n - 8 := by
  rw [Φ]
  simp only [SS4, ↓reduceIte, Bool.false_eq_true, true_or, or_self, Pe2_000000100, Pe2_000001100, Pe2_001000100, Pe2_010010101]
  ring

theorem Pe3_111000000 (n : ℤ) : Φ n true 3 true true true false false false false false false = n^2 + 2*n + 1 := by
  rw [Φ]
  simp only [↓reduceIte, Bool.false_eq_true, or_self, Pe2_100011000]
  ring

theorem Pe3_111111111 (n : ℤ) : Φ n true 3 true true true true true true true true true = 6*n^2 + 1 := by
  rw [Φ]
  simp only [SS4, ↓reduceIte, or_self, Pe2_100100110, Pe2_111111111]
  ring

theorem Pe4_000000000 (n : ℤ) : Φ n true 4 false false false false false false false false false = 10*n^2 + 15*n - 4 := by
  rw [Φ]
  simp only [↓reduceIte, Bool.false_eq_true, or_self, Pe3_000000000, Pe3_000001000, Pe3_000010000]
  ring

theorem Pe4_000000001 (n : ℤ) : Φ n true 4 false false false false false false false false true = 10*n^2 + 18*n - 3 := by
  rw [Φ]
  simp only [↓reduceIte, Bool.false_eq_true, or_self, Pe3_000000010, Pe3_000010010, Pe3_001001011]
  ring

theorem Pe4_000000010 (n : ℤ) : Φ n true 4 false false false false false false false true false = 10*n^2 + 16*n - 1 := by
  rw [Φ]
  simp only [↓reduceIte, Bool.false_eq_true, or_self, Pe3_000000100, Pe3_000001100, Pe3_010010101]
  ring

theorem Pe4_000000100 (n : ℤ) : Φ n true 4 false false false false false false true false false = 10*n^2 + 15*n - 3 := by
  rw [Φ]
  simp only [↓reduceIte, Bool.false_eq_true, or_self, Pe3_000000001, Pe3_000001000, Pe3_000010000]
  ring

theorem Pe4_000001000 (n : ℤ) : Φ n true 4 false false false false false true false false false = 3*n^3 + 15*n^2 - 20*n + 20 := by
  rw [Φ]
  simp only [SS4, ↓reduceIte, Bool.false_eq_true, or_true, Pe3_000100000, Pe3_000100001, Pe3_001110000, Pe3_010101000]
  ring

theorem Pe4_000001100 (n : ℤ) : Φ n true 4 false false false false false true true false false = 3*n^3 + 15*n^2 - 20*n + 20 := by
  rw [Φ]
  simp only [SS4, ↓reduceIte, Bool.false_eq_true, or_true, Pe3_000100000, Pe3_000100001, Pe3_001110000, Pe3_010101000]
  ring

theorem Pe4_000010000 (n : ℤ) : Φ n true 4 false false false false true false false false false = n^3 + 17*n^2 - 7*n - 14 := by
  rw [Φ]
  simp only [SS4, ↓reduceIte, Bool.false_eq_true, true_or, or_true, Pe3_000000000, Pe3_000000001, Pe3_000001000, Pe3_000010000, Pe3_001000000, Pe3_010000000]
  ring

theorem Pe4_000010010 (n : ℤ) : Φ n true 4 false false false false true false false true false = n^3 + 17*n^2 - 4*n - 7 := by
  rw [Φ]
  simp only [SS4, ↓reduceIte, Bool.false_eq_true, true_or, or_true, Pe3_000000100, Pe3_000001100, Pe3_001000100, Pe3_010010101]
  ring

theorem Pe4_000100000 (n : ℤ) : Φ n true 4 false false false true false false false false false = n^3 + 17*n^2 - 7*n - 14 := by
  rw [Φ]
  simp only [SS4, ↓reduceIte, Bool.false_eq_true, true_or, or_self, Pe3_000000000, Pe3_000000001, Pe3_000001000, Pe3_000010000, Pe3_001000000, Pe3_010000000]
  ring

theorem Pe4_000100001 (n : ℤ) : Φ n true 4 false false false true false false false false true = n^3 + 17*n^2 + 2*n - 16 := by
  rw [Φ]
  simp only [SS4, ↓reduceIte, Bool.false_eq_true, true_or, or_self, Pe3_000000010, Pe3_000010010, Pe3_001001011, Pe3_010000010]
  ring

theorem Pe4_001000000 (n : ℤ) : Φ n true 4 false false true false false false false false false = 7*n^2 + 4*n + 3 := by
  rw [Φ]
  simp only [↓reduceIte, Bool.false_eq_true, or_true, or_self, Pe3_100000000, Pe3_100011000]
  ring

theorem Pe4_001000100 (n : ℤ) : Φ n true 4 false false true false false false true false false = 7*n^2 + 4*n + 4 := by
  rw [Φ]
  simp only [↓reduceIte, Bool.false_eq_true, or_true, or_self, Pe3_100000001, Pe3_100011000]
  ring

theorem Pe4_001001011 (n : ℤ) : Φ n true 4 false false true false false true false true true = 3*n^3 + 15*n^2 - 8*n + 1 := by
  rw [Φ]
  simp only [SS4, ↓reduceIte, Bool.false_eq_true, or_true, Pe3_100100110, Pe3_111111111]
  ring

theorem Pe4_001110000 (n : ℤ) : Φ n true 4 false false true true true false false false false = n^3 + 13*n^2 - 10*n + 9 := by
  rw [Φ]
  simp only [SS4, ↓reduceIte, Bool.false_eq_true, true_or, or_self, Pe3_100000000, Pe3_100000001, Pe3_100011000, Pe3_111000000]
  ring

theorem Pe4_010000000 (n : ℤ) : Φ n true 4 false true false false false false false false false = 9*n^2 + 6*n - 7 := by
  rw [Φ]
  simp only [↓reduceIte, Bool.false_eq_true, true_or, or_self, Pe3_000001000, Pe3_000010000]
  ring

theorem Pe4_010000010 (n : ℤ) : Φ n true 4 false true false false false false false true false = 9*n^2 + 7*n - 4 := by
  rw [Φ]
  simp only [↓reduceIte, Bool.false_eq_true, true_or, or_self, Pe3_000001100, Pe3_010010101]
  ring

theorem Pe4_010010101 (n : ℤ) : Φ n true 4 false true false false true false true false true = n^3 + 17*n^2 + 2*n - 16 := by
  rw [Φ]
  simp only [SS4, ↓reduceIte, Bool.false_eq_true, true_or, or_true, Pe3_000000010, Pe3_000010010, Pe3_001001011, Pe3_010000010]
  ring

theorem Pe4_010101000 (n : ℤ) : Φ n true 4 false true false true false true false false false = 3*n^3 + 15*n^2 - 20*n + 20 := by
  rw [Φ]
  simp only [SS4, ↓reduceIte, Bool.false_eq_true, or_true, or_self, Pe3_000100000, Pe3_000100001, Pe3_001110000, Pe3_010101000]
  ring

theorem Pe4_100000000 (n : ℤ) : Φ n true 4 true false false false false false false false false = 9*n^2 + 6*n - 7 := by
  rw [Φ]
  simp only [↓reduceIte, Bool.false_eq_true, or_self, Pe3_000001000, Pe3_000010000]
  ring

theorem Pe4_100000001 (n : ℤ) : Φ n true 4 true false false false false false false false true = 9*n^2 + 9*n - 7 := by
  rw [Φ]
  simp only [↓reduceIte, Bool.false_eq_true, or_self, Pe3_000010010, Pe3_001001011]
  ring

theorem Pe4_100011000 (n : ℤ) : Φ n true 4 true false false false true true false false false = 3*n^3 + 15*n^2 - 20*n + 20 := by
  rw [Φ]
  simp only [SS4, ↓reduceIte, Bool.false_eq_true, or_true, or_self, Pe3_000100000, Pe3_000100001, Pe3_001110000, Pe3_010101000]
  ring

theorem Pe4_100100110 (n : ℤ) : Φ n true 4 true false false true false false true true false = n^3 + 17*n^2 - 4*n - 7 := by
  rw [Φ]
  simp only [SS4, ↓reduceIte, Bool.false_eq_true, true_or, or_self, Pe3_000000100, Pe3_000001100, Pe3_001000100, Pe3_010010101]
  ring

theorem Pe4_111000000 (n : ℤ) : Φ n true 4 true true true false false false false false false = 6*n^2 - 3*n + 5 := by
  rw [Φ]
  simp only [↓reduceIte, Bool.false_eq_true, or_self, Pe3_100011000]
  ring

theorem Pe4_111111111 (n : ℤ) : Φ n true 4 true true true true true true true true true = 3*n^3 + 15*n^2 - 8*n + 1 := by
  rw [Φ]
  simp only [SS4, ↓reduceIte, or_self, Pe3_100100110, Pe3_111111111]
  ring

theorem Po1_000000000 (n : ℤ) : Φ n false 1 false false false false false false false false false = 3 := by
  rw [Φ]
  simp only [↓reduceIte, Bool.false_eq_true, or_self, Φ0]
  ring

theorem Po1_000001000 (n : ℤ) : Φ n false 1 false false false false false true false false false = n + 1 := by
  rw [Φ]
  simp only [SS4, ↓reduceIte, Bool.false_eq_true, or_true, Φ0]
  ring

theorem Po1_000010000 (n : ℤ) : Φ n false 1 false false false false true false false false false = n + 1 := by
  rw [Φ]
  simp only [SS4, ↓reduceIte, Bool.false_eq_true, true_or, or_true, Φ0]
  ring

theorem Po1_000100000 (n : ℤ) : Φ n false 1 false false false true false false false false false = n + 1 := by
  rw [Φ]
  simp only [SS4, ↓reduceIte, Bool.false_eq_true, true_or, or_self, Φ0]
  ring

theorem Po1_001000000 (n : ℤ) : Φ n false 1 false false true false false false false false false = 2 := by
  rw [Φ]
  simp only [↓reduceIte, Bool.false_eq_true, or_true, or_self, Φ0]
  ring

theorem Po1_001110000 (n : ℤ) : Φ n false 1 false false true true true false false false false = n + 1 := by
  rw [Φ]
  simp only [SS4, ↓reduceIte, Bool.false_eq_true, true_or, or_self, Φ0]
  ring

theorem Po1_010000000 (n : ℤ) : Φ n false 1 false true false false false false false false false = 2 := by
  rw [Φ]
  simp only [↓reduceIte, Bool.false_eq_true, true_or, or_self, Φ0]
  ring

theorem Po1_010101000 (n : ℤ) : Φ n false 1 false true false true false true false false false = n + 1 := by
  rw [Φ]
  simp only [SS4, ↓reduceIte, Bool.false_eq_true, or_true, or_self, Φ0]
  ring

theorem Po1_100000000 (n : ℤ) : Φ n false 1 true false false false false false false false false = 2 := by
  rw [Φ]
  simp only [↓reduceIte, Bool.false_eq_true, or_self, Φ0]
  ring

theorem Po1_100011000 (n : ℤ) : Φ n false 1 true false false false true true false false false = n + 1 := by
  rw [Φ]
  simp only [SS4, ↓reduceIte, Bool.false_eq_true, or_true, or_self, Φ0]
  ring

theorem Po1_111000000 (n : ℤ) : Φ n false 1 true true true false false false false false false = 1 := by
  rw [Φ]
  simp only [↓reduceIte, Bool.false_eq_true, or_self, Φ0]
  ring

theorem Po2_000000000 (n : ℤ) : Φ n false 2 false false false false false false false false false = 2*n + 5 := by
  rw [Φ]
  simp only [↓reduceIte, Bool.false_eq_true, or_self, Po1_000000000, Po1_000001000, Po1_000010000]
  ring

theorem Po2_000001000 (n : ℤ) : Φ n false 2 false false false false false true false false false = n^2 + 2*n + 1 := by
  rw [Φ]
  simp only [SS4, ↓reduceIte, Bool.false_eq_true, or_true, Po1_000100000, Po1_001110000, Po1_010101000]
  ring

theorem Po2_000010000 (n : ℤ) : Φ n false 2 false false false false true false false false false = 5*n - 3 := by
  rw [Φ]
  simp only [SS4, ↓reduceIte, Bool.false_eq_true, true_or, or_true, Po1_000000000, Po1_000001000, Po1_000010000, Po1_001000000, Po1_010000000]
  ring

theorem Po2_000100000 (n : ℤ) : Φ n false 2 false false false true false false false false false = 5*n - 3 := by
  rw [Φ]
  simp only [SS4, ↓reduceIte, Bool.false_eq_true, true_or, or_self, Po1_000000000, Po1_000001000, Po1_000010000, Po1_001000000, Po1_010000000]
  ring

theorem Po2_001000000 (n : ℤ) : Φ n false 2 false false true false false false false false false = n + 3 := by
  rw [Φ]
  simp only [↓reduceIte, Bool.false_eq_true, or_true, or_self, Po1_100000000, Po1_100011000]
  ring

theorem Po2_001110000 (n : ℤ) : Φ n false 2 false false true true true false false false false = 3*n := by
  rw [Φ]
  simp only [SS4, ↓reduceIte, Bool.false_eq_true, true_or, or_self, Po1_100000000, Po1_100011000, Po1_111000000]
  ring

theorem Po2_010000000 (n : ℤ) : Φ n false 2 false true false false false false false false false = 2*n + 2 := by
  rw [Φ]
  simp only [↓reduceIte, Bool.false_eq_true, true_or, or_self, Po1_000001000, Po1_000010000]
  ring

theorem Po2_010101000 (n : ℤ) : Φ n false 2 false true false true false true false false false = n^2 + 2*n + 1 := by
  rw [Φ]
  simp only [SS4, ↓reduceIte, Bool.false_eq_true, or_true, or_self, Po1_000100000, Po1_001110000, Po1_010101000]
  ring

theorem Po2_100000000 (n : ℤ) : Φ n false 2 true false false false false false false false false = 2*n + 2 := by
  rw [Φ]
  simp only [↓reduceIte, Bool.false_eq_true, or_self, Po1_000001000, Po1_000010000]
  ring

theorem Po2_100011000 (n : ℤ) : Φ n false 2 true false false false true true false false false = n^2 + 2*n + 1 := by
  rw [Φ]
  simp only [SS4, ↓reduceIte, Bool.false_eq_true, or_true, or_self, Po1_000100000, Po1_001110000, Po1_010101000]
  ring

theorem Po2_111000000 (n : ℤ) : Φ n false 2 true true true false false false false false false = n + 1 := by
  rw [Φ]
  simp only [↓reduceIte, Bool.false_eq_true, or_self, Po1_100011000]
  ring

theorem Po3_000000000 (n : ℤ) : Φ n false 3 false false false false false false false false false = n^2 + 9*n + 3 := by
  rw [Φ]
  simp only [↓reduceIte, Bool.false_eq_true, or_self, Po2_000000000, Po2_000001000, Po2_000010000]
  ring

theorem Po3_000001000 (n : ℤ) : Φ n false 3 false false false false false true false false false = 6*n^2 - 3*n + 4 := by
  rw [Φ]
  simp only [SS4, ↓reduceIte, Bool.false_eq_true, or_true, Po2_000100000, Po2_001110000, Po2_010101000]
  ring

theorem Po3_000010000 (n : ℤ) : Φ n false 3 false false false false true false false false false = 3*n^2 + 9*n - 12 := by
  rw [Φ]
  simp only [SS4, ↓reduceIte, Bool.false_eq_true, true_or, or_true, Po2_000000000, Po2_000001000, Po2_000010000, Po2_001000000, Po2_010000000]
  ring

theorem Po3_000100000 (n : ℤ) : Φ n false 3 false false false true false false false false false = 3*n^2 + 9*n - 12 := by
  rw [Φ]
  simp only [SS4, ↓reduceIte, Bool.false_eq_true, true_or, or_self, Po2_000000000, Po2_000001000, Po2_000010000, Po2_001000000, Po2_010000000]
  ring

theorem Po3_001000000 (n : ℤ) : Φ n false 3 false false true false false false false false false = n^2 + 4*n + 3 := by
  rw [Φ]
  simp only [↓reduceIte, Bool.false_eq_true, or_true, or_self, Po2_100000000, Po2_100011000]
  ring

theorem Po3_001110000 (n : ℤ) : Φ n false 3 false false true true true false false false false = 3*n^2 + 3*n := by
  rw [Φ]
  simp only [SS4, ↓reduceIte, Bool.false_eq_true, true_or, or_self, Po2_100000000, Po2_100011000, Po2_111000000]
  ring

theorem Po3_010000000 (n : ℤ) : Φ n false 3 false true false false false false false false false = n^2 + 7*n - 2 := by
  rw [Φ]
  simp only [↓reduceIte, Bool.false_eq_true, true_or, or_self, Po2_000001000, Po2_000010000]
  ring

theorem Po3_010101000 (n : ℤ) : Φ n false 3 false true false true false true false false false = 6*n^2 - 3*n + 4 := by
  rw [Φ]
  simp only [SS4, ↓reduceIte, Bool.false_eq_true, or_true, or_self, Po2_000100000, Po2_001110000, Po2_010101000]
  ring

theorem Po3_100000000 (n : ℤ) : Φ n false 3 true false false false false false false false false = n^2 + 7*n - 2 := by
  rw [Φ]
  simp only [↓reduceIte, Bool.false_eq_true, or_self, Po2_000001000, Po2_000010000]
  ring

theorem Po3_100011000 (n : ℤ) : Φ n false 3 true false false false true true false false false = 6*n^2 - 3*n + 4 := by
  rw [Φ]
  simp only [SS4, ↓reduceIte, Bool.false_eq_true, or_true, or_self, Po2_000100000, Po2_001110000, Po2_010101000]
  ring

theorem Po3_111000000 (n : ℤ) : Φ n false 3 true true true false false false false false false = n^2 + 2*n + 1 := by
  rw [Φ]
  simp only [↓reduceIte, Bool.false_eq_true, or_self, Po2_100011000]
  ring

theorem Po4_000000000 (n : ℤ) : Φ n false 4 false false false false false false false false false = 10*n^2 + 15*n - 5 := by
  rw [Φ]
  simp only [↓reduceIte, Bool.false_eq_true, or_self, Po3_000000000, Po3_000001000, Po3_000010000]
  ring

theorem Po4_000001000 (n : ℤ) : Φ n false 4 false false false false false true false false false = 3*n^3 + 15*n^2 - 21*n + 16 := by
  rw [Φ]
  simp only [SS4, ↓reduceIte, Bool.false_eq_true, or_true, Po3_000100000, Po3_001110000, Po3_010101000]
  ring

theorem Po4_000010000 (n : ℤ) : Φ n false 4 false false false false true false false false false = n^3 + 17*n^2 - 7*n - 16 := by
  rw [Φ]
  simp only [SS4, ↓reduceIte, Bool.false_eq_true, true_or, or_true, Po3_000000000, Po3_000001000, Po3_000010000, Po3_001000000, Po3_010000000]
  ring

theorem Po4_000100000 (n : ℤ) : Φ n false 4 false false false true false false false false false = n^3 + 17*n^2 - 7*n - 16 := by
  rw [Φ]
  simp only [SS4, ↓reduceIte, Bool.false_eq_true, true_or, or_self, Po3_000000000, Po3_000001000, Po3_000010000, Po3_001000000, Po3_010000000]
  ring

theorem Po4_001000000 (n : ℤ) : Φ n false 4 false false true false false false false false false = 7*n^2 + 4*n + 2 := by
  rw [Φ]
  simp only [↓reduceIte, Bool.false_eq_true, or_true, or_self, Po3_100000000, Po3_100011000]
  ring

theorem Po4_001110000 (n : ℤ) : Φ n false 4 false false true true true false false false false = n^3 + 13*n^2 - 10*n + 7 := by
  rw [Φ]
  simp only [SS4, ↓reduceIte, Bool.false_eq_true, true_or, or_self, Po3_100000000, Po3_100011000, Po3_111000000]
  ring

theorem Po4_010000000 (n : ℤ) : Φ n false 4 false true false false false false false false false = 9*n^2 + 6*n - 8 := by
  rw [Φ]
  simp only [↓reduceIte, Bool.false_eq_true, true_or, or_self, Po3_000001000, Po3_000010000]
  ring

theorem Po4_010101000 (n : ℤ) : Φ n false 4 false true false true false true false false false = 3*n^3 + 15*n^2 - 21*n + 16 := by
  rw [Φ]
  simp only [SS4, ↓reduceIte, Bool.false_eq_true, or_true, or_self, Po3_000100000, Po3_001110000, Po3_010101000]
  ring

theorem Po4_100000000 (n : ℤ) : Φ n false 4 true false false false false false false false false = 9*n^2 + 6*n - 8 := by
  rw [Φ]
  simp only [↓reduceIte, Bool.false_eq_true, or_self, Po3_000001000, Po3_000010000]
  ring

theorem Po4_100011000 (n : ℤ) : Φ n false 4 true false false false true true false false false = 3*n^3 + 15*n^2 - 21*n + 16 := by
  rw [Φ]
  simp only [SS4, ↓reduceIte, Bool.false_eq_true, or_true, or_self, Po3_000100000, Po3_001110000, Po3_010101000]
  ring

theorem Po4_111000000 (n : ℤ) : Φ n false 4 true true true false false false false false false = 6*n^2 - 3*n + 4 := by
  rw [Φ]
  simp only [↓reduceIte, Bool.false_eq_true, or_self, Po3_100011000]
  ring


theorem L43 (n x y z : ℕ) (hx : x ≤ n) (hy : y ≤ n) (hz : z ≤ n) (f : ℕ → ℤ) :
    ∑ v ∈ Finset.range (n + 1), (if v = x ∨ v = y ∨ v = z then f v else 0) =
      f x + (if x = y then 0 else f y) + (if z = x ∨ z = y then 0 else f z) := by
  rw [Finset.sum_congr rfl (g := fun v => (if v = x then f x else 0) +
      (if v = y then (if x = y then 0 else f y) else 0) +
      (if v = z then (if z = x ∨ z = y then 0 else f z) else 0)) (fun v _ => by
        by_cases h1 : v = x <;> by_cases h2 : v = y <;> by_cases h3 : v = z <;> by_cases h4 : x = y <;>
          by_cases h5 : z = x <;> by_cases h6 : z = y <;> simp_all)]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, sum_pt n x hx, sum_pt n y hy, sum_pt n z hz]

theorem L2 (n : ℕ) : ∀ m a b c, a ≤ n → b ≤ n → c ≤ n →
    T n m a b c = Φ n (decide (Even n)) m (decide (a = b)) (decide (a = c)) (decide (b = c))
      (decide (a + b = n)) (decide (a + c = n)) (decide (b + c = n)) (decide (2 * a = n))
      (decide (2 * b = n)) (decide (2 * c = n)) := by
  intro m
  induction m with
  | zero => intro a b c _ _ _; rfl
  | succ m ih =>
    intro a b c ha hb hc
    rw [T]
    by_cases P : a + b = n ∨ a + c = n ∨ b + c = n
    · rw [Finset.sum_congr rfl (g := fun v => T n m b c v) (fun v _ => if_pos (by tauto))]
      rw [Finset.sum_congr rfl (fun v hv => ih b c v hb hc (by simp at hv; omega))]
      rw [Φ, if_pos (show (decide (a + b = n) = true ∨ decide (a + c = n) = true ∨ decide (b + c = n) = true) by simp only [decide_eq_true_eq]; exact P)]
      exact L3' n b c hb hc (fun x1 x2 x3 x4 x5 => Φ n (decide (Even n)) m (decide (b = c)) x1 x2
        (decide (b + c = n)) x3 x4 (decide (2 * b = n)) (decide (2 * c = n)) x5)
    · rw [Finset.sum_congr rfl (g := fun v => if v = n - a ∨ v = n - b ∨ v = n - c then T n m b c v else 0)
        (fun v hv => by congr 1; apply propext; omega)]
      rw [L43 n (n - a) (n - b) (n - c) (by omega) (by omega) (by omega), ih b c (n - a) hb hc (by omega),
        ih b c (n - b) hb hc (by omega), ih b c (n - c) hb hc (by omega)]
      rw [Φ, if_neg (show ¬ (decide (a + b = n) = true ∨ decide (a + c = n) = true ∨ decide (b + c = n) = true) by simp only [decide_eq_true_eq]; exact P)]
      rw [show decide (b = n - a) = decide (a + b = n) from decide_eq_decide.mpr (by omega),
        show decide (c = n - a) = decide (a + c = n) from decide_eq_decide.mpr (by omega),
        show decide (b + (n - a) = n) = decide (a = b) from decide_eq_decide.mpr (by omega),
        show decide (c + (n - a) = n) = decide (a = c) from decide_eq_decide.mpr (by omega),
        show decide (2 * (n - a) = n) = decide (2 * a = n) from decide_eq_decide.mpr (by omega),
        show decide (b = n - b) = decide (2 * b = n) from decide_eq_decide.mpr (by omega),
        show decide (c = n - b) = decide (b + c = n) from decide_eq_decide.mpr (by omega),
        show decide (b + (n - b) = n) = true from decide_eq_true (by omega),
        show decide (c + (n - b) = n) = decide (b = c) from decide_eq_decide.mpr (by omega),
        show decide (2 * (n - b) = n) = decide (2 * b = n) from decide_eq_decide.mpr (by omega),
        show decide (b = n - c) = decide (b + c = n) from decide_eq_decide.mpr (by omega),
        show decide (c = n - c) = decide (2 * c = n) from decide_eq_decide.mpr (by omega),
        show decide (b + (n - c) = n) = decide (b = c) from decide_eq_decide.mpr (by omega),
        show decide (c + (n - c) = n) = true from decide_eq_true (by omega),
        show decide (2 * (n - c) = n) = decide (2 * c = n) from decide_eq_decide.mpr (by omega)]
      have i1 : (n - a = n - b) ↔ (decide (a = b) = true) := by rw [decide_eq_true_eq]; omega
      have i2 : (n - c = n - a ∨ n - c = n - b) ↔ (decide (a = c) = true ∨ decide (b = c) = true) := by
        simp only [decide_eq_true_eq]; omega
      simp only [i1, i2]

def Gp (N : ℤ) (e : Bool) (E P Ha Hb : Bool) : ℤ :=
  SS4 N e (fun x1 x2 x3 x4 x5 => Φ N e 4 E x1 x2 P x3 x4 Ha Hb x5) E P Ha Hb

theorem a_SS (n : ℕ) : a n = ((n : ℤ) + 1) * SS n (decide (Even n)) (Gp n (decide (Even n))) false +
    (if decide (Even n) = true then SS n (decide (Even n)) (Gp n (decide (Even n))) true -
      SS n (decide (Even n)) (Gp n (decide (Even n))) false else 0) := by
  rw [a_eq]
  rw [Finset.sum_congr rfl (g := fun p => SS n (decide (Even n)) (Gp n (decide (Even n))) false +
      (if 2 * p = n then SS n (decide (Even n)) (Gp n (decide (Even n))) true -
        SS n (decide (Even n)) (Gp n (decide (Even n))) false else 0))
    (fun p hp => by
      have hp' : p ≤ n := by simp at hp; omega
      rw [Finset.sum_congr rfl (g := fun q => Gp n (decide (Even n)) (decide (p = q)) (decide (p + q = n))
        (decide (2 * p = n)) (decide (2 * q = n))) (fun q hq => by
          have hq' : q ≤ n := by simp at hq; omega
          rw [Finset.sum_congr rfl (fun r hr => L2 n 4 p q r hp' hq' (by simp at hr; omega))]
          exact L3' n p q hp' hq' (fun x1 x2 x3 x4 x5 => Φ n (decide (Even n)) 4 (decide (p = q)) x1 x2
            (decide (p + q = n)) x3 x4 (decide (2 * p = n)) (decide (2 * q = n)) x5))]
      rw [L3 n p hp' (Gp n (decide (Even n)))]
      by_cases h : 2 * p = n <;> simp [h])]
  rw [Finset.sum_add_distrib, sum_half, sum_const']


theorem a_even (n : ℕ) (h : Even n) :
    (a n : ℚ) = 1 + 34 * (n : ℚ) + 6 * (n : ℚ) ^ 2 - 16 * (n : ℚ) ^ 3 + 66 * (n : ℚ) ^ 4 + 15 * (n : ℚ) ^ 5 := by
  have hz : a n = 1 + 34 * (n : ℤ) + 6 * (n : ℤ) ^ 2 - 16 * (n : ℤ) ^ 3 + 66 * (n : ℤ) ^ 4 + 15 * (n : ℤ) ^ 5 := by
    rw [a_SS, decide_eq_true h]
    simp only [SS, Gp, SS4, ↓reduceIte, Bool.false_eq_true, Pe4_000000000, Pe4_000000001, Pe4_000000010, Pe4_000000100, Pe4_000001000, Pe4_000001100, Pe4_000010000, Pe4_000010010, Pe4_000100000, Pe4_000100001, Pe4_001000000, Pe4_001000100, Pe4_001001011, Pe4_001110000, Pe4_010000000, Pe4_010000010, Pe4_010010101, Pe4_010101000, Pe4_100000000, Pe4_100000001, Pe4_100011000, Pe4_100100110, Pe4_111000000, Pe4_111111111]
    ring
  rw [hz]; push_cast; ring

theorem a_odd (n : ℕ) (h : ¬ Even n) :
    (a n : ℚ) = 58 + 57 * (n : ℚ) - 80 * (n : ℚ) ^ 2 - 28 * (n : ℚ) ^ 3 + 66 * (n : ℚ) ^ 4 + 15 * (n : ℚ) ^ 5 := by
  have hz : a n = 58 + 57 * (n : ℤ) - 80 * (n : ℤ) ^ 2 - 28 * (n : ℤ) ^ 3 + 66 * (n : ℤ) ^ 4 + 15 * (n : ℤ) ^ 5 := by
    rw [a_SS, decide_eq_false h]
    simp only [SS, Gp, SS4, ↓reduceIte, Bool.false_eq_true, Po4_000000000, Po4_000001000, Po4_000010000, Po4_000100000, Po4_001000000, Po4_001110000, Po4_010000000, Po4_010101000, Po4_100000000, Po4_100011000, Po4_111000000]
    ring
  rw [hz]; push_cast; ring


def Q (m : ℕ) : ℚ := if Even m then 1 + 34 * (m : ℚ) + 6 * (m : ℚ) ^ 2 - 16 * (m : ℚ) ^ 3 + 66 * (m : ℚ) ^ 4 + 15 * (m : ℚ) ^ 5 else 58 + 57 * (m : ℚ) - 80 * (m : ℚ) ^ 2 - 28 * (m : ℚ) ^ 3 + 66 * (m : ℚ) ^ 4 + 15 * (m : ℚ) ^ 5

theorem aQ (m : ℕ) : (a m : ℚ) = Q m := by
  unfold Q; split_ifs with h
  · exact a_even m h
  · exact a_odd m h


theorem rec11 (k : ℕ) (hk : 11 ≤ k) : (1) * Q k + (-2) * Q (k - 1) + (-3) * Q (k - 2) + (8) * Q (k - 3) + (2) * Q (k - 4) + (-12) * Q (k - 5) + (2) * Q (k - 6) + (8) * Q (k - 7) + (-3) * Q (k - 8) + (-2) * Q (k - 9) + (1) * Q (k - 10) = 0 := by
  obtain ⟨t, rfl | rfl⟩ : ∃ t, k = 2 * t + 11 ∨ k = 2 * t + 12 := ⟨(k - 11) / 2, by omega⟩
  · rw [show 2 * t + 11 - 1 = 2 * t + 10 by omega, show 2 * t + 11 - 2 = 2 * t + 9 by omega, show 2 * t + 11 - 3 = 2 * t + 8 by omega, show 2 * t + 11 - 4 = 2 * t + 7 by omega, show 2 * t + 11 - 5 = 2 * t + 6 by omega, show 2 * t + 11 - 6 = 2 * t + 5 by omega, show 2 * t + 11 - 7 = 2 * t + 4 by omega, show 2 * t + 11 - 8 = 2 * t + 3 by omega, show 2 * t + 11 - 9 = 2 * t + 2 by omega, show 2 * t + 11 - 10 = 2 * t + 1 by omega]
    simp only [Q, (show ¬ Even (2 * t + 11) from Nat.not_even_iff_odd.mpr ⟨t + 5, by ring⟩), (show Even (2 * t + 10) from ⟨t + 5, by ring⟩), (show ¬ Even (2 * t + 9) from Nat.not_even_iff_odd.mpr ⟨t + 4, by ring⟩), (show Even (2 * t + 8) from ⟨t + 4, by ring⟩), (show ¬ Even (2 * t + 7) from Nat.not_even_iff_odd.mpr ⟨t + 3, by ring⟩), (show Even (2 * t + 6) from ⟨t + 3, by ring⟩), (show ¬ Even (2 * t + 5) from Nat.not_even_iff_odd.mpr ⟨t + 2, by ring⟩), (show Even (2 * t + 4) from ⟨t + 2, by ring⟩), (show ¬ Even (2 * t + 3) from Nat.not_even_iff_odd.mpr ⟨t + 1, by ring⟩), (show Even (2 * t + 2) from ⟨t + 1, by ring⟩), (show ¬ Even (2 * t + 1) from Nat.not_even_iff_odd.mpr ⟨t + 0, by ring⟩), if_true, if_false]
    push_cast; ring
  · rw [show 2 * t + 12 - 1 = 2 * t + 11 by omega, show 2 * t + 12 - 2 = 2 * t + 10 by omega, show 2 * t + 12 - 3 = 2 * t + 9 by omega, show 2 * t + 12 - 4 = 2 * t + 8 by omega, show 2 * t + 12 - 5 = 2 * t + 7 by omega, show 2 * t + 12 - 6 = 2 * t + 6 by omega, show 2 * t + 12 - 7 = 2 * t + 5 by omega, show 2 * t + 12 - 8 = 2 * t + 4 by omega, show 2 * t + 12 - 9 = 2 * t + 3 by omega, show 2 * t + 12 - 10 = 2 * t + 2 by omega]
    simp only [Q, (show Even (2 * t + 12) from ⟨t + 6, by ring⟩), (show ¬ Even (2 * t + 11) from Nat.not_even_iff_odd.mpr ⟨t + 5, by ring⟩), (show Even (2 * t + 10) from ⟨t + 5, by ring⟩), (show ¬ Even (2 * t + 9) from Nat.not_even_iff_odd.mpr ⟨t + 4, by ring⟩), (show Even (2 * t + 8) from ⟨t + 4, by ring⟩), (show ¬ Even (2 * t + 7) from Nat.not_even_iff_odd.mpr ⟨t + 3, by ring⟩), (show Even (2 * t + 6) from ⟨t + 3, by ring⟩), (show ¬ Even (2 * t + 5) from Nat.not_even_iff_odd.mpr ⟨t + 2, by ring⟩), (show Even (2 * t + 4) from ⟨t + 2, by ring⟩), (show ¬ Even (2 * t + 3) from Nat.not_even_iff_odd.mpr ⟨t + 1, by ring⟩), (show Even (2 * t + 2) from ⟨t + 1, by ring⟩), if_true, if_false]
    push_cast; ring


open PowerSeries in
theorem gf : PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) * ((1 - X) ^ 6 * (1 + X) ^ 4 : PowerSeries ℚ) = X * (88 + 1325 * X + 4478 * X ^ 2 + 12178 * X ^ 3 + 8990 * X ^ 4 + 2708 * X ^ 5 - 310 * X ^ 6 - 658 * X ^ 7 + 2 * X ^ 8 - X ^ 9) := by
  set f : ℕ → ℚ := fun n => if n < 1 then 0 else (a n : ℚ) with hf
  set A : PowerSeries ℚ := PowerSeries.mk f with hA
  have hD : A * ((1 - X) ^ 6 * (1 + X) ^ 4 : PowerSeries ℚ) = A - C (2 : ℚ) * (A * X ^ 1) - C (3 : ℚ) * (A * X ^ 2) + C (8 : ℚ) * (A * X ^ 3) + C (2 : ℚ) * (A * X ^ 4) - C (12 : ℚ) * (A * X ^ 5) + C (2 : ℚ) * (A * X ^ 6) + C (8 : ℚ) * (A * X ^ 7) - C (3 : ℚ) * (A * X ^ 8) - C (2 : ℚ) * (A * X ^ 9) + (A * X ^ 10) := by
    simp only [map_ofNat]; ring
  have hN : X * (88 + 1325 * X + 4478 * X ^ 2 + 12178 * X ^ 3 + 8990 * X ^ 4 + 2708 * X ^ 5 - 310 * X ^ 6 - 658 * X ^ 7 + 2 * X ^ 8 - X ^ 9 : PowerSeries ℚ) = C (88 : ℚ) * X ^ 1 + C (1325 : ℚ) * X ^ 2 + C (4478 : ℚ) * X ^ 3 + C (12178 : ℚ) * X ^ 4 + C (8990 : ℚ) * X ^ 5 + C (2708 : ℚ) * X ^ 6 - C (310 : ℚ) * X ^ 7 - C (658 : ℚ) * X ^ 8 + C (2 : ℚ) * X ^ 9 - X ^ 10 := by
    simp only [map_ofNat]; ring
  rw [hD, hN]
  ext k
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', hA, coeff_mk, coeff_X_pow]
  have hfk : ∀ m, 1 ≤ m → f m = Q m := fun m hm => by
    simp only [hf, show ¬ m < 1 by omega, if_false, aQ]
  rcases Nat.lt_or_ge k 11 with h | h
  · have f0 : f 0 = 0 := by simp [hf]
    interval_cases k <;> simp [f0, hfk, Q] <;> norm_num
  · simp only [show 1 ≤ k by omega, show 2 ≤ k by omega, show 3 ≤ k by omega, show 4 ≤ k by omega, show 5 ≤ k by omega, show 6 ≤ k by omega, show 7 ≤ k by omega, show 8 ≤ k by omega, show 9 ≤ k by omega, show 10 ≤ k by omega, if_true, coeff_C, show k ≠ 10 by omega, show k - 1 ≠ 0 by omega, show k - 2 ≠ 0 by omega, show k - 3 ≠ 0 by omega, show k - 4 ≠ 0 by omega, show k - 5 ≠ 0 by omega, show k - 6 ≠ 0 by omega, show k - 7 ≠ 0 by omega, show k - 8 ≠ 0 by omega, show k - 9 ≠ 0 by omega, if_false, hfk k (by omega), hfk (k - 1) (by omega), hfk (k - 2) (by omega), hfk (k - 3) (by omega), hfk (k - 4) (by omega), hfk (k - 5) (by omega), hfk (k - 6) (by omega), hfk (k - 7) (by omega), hfk (k - 8) (by omega), hfk (k - 9) (by omega), hfk (k - 10) (by omega)]
    linear_combination rec11 k h

end OMA.Helpers_a245954

open OMA.Helpers_a245954 in
theorem OMA.solution : type_of% @OMA.S_oeis_a245954.main :=
  ⟨gf, fun n _ h => a_even n h, fun n _ h => a_odd n (Nat.not_even_iff_odd.mpr h)⟩
