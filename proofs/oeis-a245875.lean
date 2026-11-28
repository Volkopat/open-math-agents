import OMAStatements.S_oeis_a245875
import Mathlib

namespace OMA.Helpers_a245875
open OMA.S_oeis_a245875

def ch (n : ℕ) : (m : ℕ) → ℕ → ℕ → (Fin m → Fin (n + 1)) → Bool
  | 0, _, _, _ => true
  | m + 1, a, b, y => decide (a + b = n ∨ a + (y 0 : ℕ) = n ∨ b + (y 0 : ℕ) = n) && ch n m b (y 0) (Fin.tail y)

def T (n : ℕ) : ℕ → ℕ → ℕ → ℤ
  | 0, _, _ => 1
  | m + 1, a, b => ∑ v ∈ Finset.range (n + 1),
      if a + b = n ∨ a + v = n ∨ b + v = n then T n m b v else 0

theorem sum_cons {n m : ℕ} (f : (Fin (m + 1) → Fin (n + 1)) → ℤ) :
    ∑ y, f y = ∑ v : Fin (n + 1), ∑ z : Fin m → Fin (n + 1), f (Fin.cons v z) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.consEquiv fun _ => Fin (n + 1)) _ _ (fun p => rfl)).symm

theorem cnt (n : ℕ) : ∀ m a b, (((Finset.univ : Finset (Fin m → Fin (n + 1))).filter
    (fun y => ch n m a b y = true)).card : ℤ) = T n m a b := by
  intro m
  induction m with
  | zero => intro a b; simp [ch, T]
  | succ m ih =>
    intro a b
    rw [Finset.card_filter, Nat.cast_sum, sum_cons, T,
      ← Fin.sum_univ_eq_sum_range (fun v => if a + b = n ∨ a + v = n ∨ b + v = n then T n m b v else 0)]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    simp only [ch, Fin.cons_zero, Fin.tail_cons, Bool.and_eq_true, decide_eq_true_eq]
    split_ifs with h
    · rw [← ih b v, Finset.card_filter, Nat.cast_sum]
      refine Finset.sum_congr rfl (fun z _ => ?_)
      simp [h]
    · simp [h]

theorem win {n : ℕ} (x : Fin 8 → Fin (n + 1)) (i : ℕ) :
    (∃ s < (3 : ℕ), ∃ t < (3 : ℕ), s < t ∧ get x (i + s) + get x (i + t) = n) ↔
      (get x i + get x (i + 1) = n ∨ get x i + get x (i + 2) = n ∨ get x (i + 1) + get x (i + 2) = n) := by
  constructor
  · rintro ⟨s, hs, t, ht, hst, e⟩
    interval_cases s <;> interval_cases t <;> simp_all
  · rintro (h | h | h)
    · exact ⟨0, by norm_num, 1, by norm_num, by norm_num, by simpa using h⟩
    · exact ⟨0, by norm_num, 2, by norm_num, by norm_num, by simpa using h⟩
    · exact ⟨1, by norm_num, 2, by norm_num, by norm_num, h⟩

theorem good_iff {n : ℕ} (x : Fin 8 → Fin (n + 1)) :
    good x = ch n 6 (x 0) (x 1) (fun i => x ⟨i + 2, by omega⟩) := by
  apply Bool.eq_iff_iff.mpr
  simp only [good, decide_eq_true_eq, win]
  simp only [ch, Bool.and_eq_true, decide_eq_true_eq, and_true]
  simp only [Fin.tail, Fin.val_succ, Fin.val_zero, S_oeis_a245875.get]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · have := h 0 (by norm_num); simpa using this
    · have := h 1 (by norm_num); simpa using this
    · have := h 2 (by norm_num); simpa using this
    · have := h 3 (by norm_num); simpa using this
    · have := h 4 (by norm_num); simpa using this
    · have := h 5 (by norm_num); simpa using this
  · rintro ⟨h0, h1, h2, h3, h4, h5⟩ i hi
    interval_cases i <;> simp_all

theorem a_eq (n : ℕ) : a n = ∑ p ∈ Finset.range (n + 1), ∑ q ∈ Finset.range (n + 1), T n 6 p q := by
  unfold a
  rw [Finset.card_filter, Nat.cast_sum, sum_cons]
  rw [← Fin.sum_univ_eq_sum_range (fun p => ∑ q ∈ Finset.range (n + 1), T n 6 p q)]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [sum_cons, ← Fin.sum_univ_eq_sum_range (fun q => T n 6 p q)]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [← cnt, Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  rw [good_iff]
  rfl


def Φ (n : ℤ) (e : Bool) : ℕ → Bool → Bool → Bool → Bool → ℤ
  | 0, _, _, _, _ => 1
  | m + 1, E, P, Ha, Hb =>
    if P then
      (if Hb then Φ n e m true true true true + n * Φ n e m false false true false
       else Φ n e m true false false false + Φ n e m false true false false +
         (if e then Φ n e m false false false true else 0) +
         (n - 1 - (if e then 1 else 0)) * Φ n e m false false false false)
    else Φ n e m false E Hb Ha + (if E then 0 else Φ n e m Hb true Hb Hb)

theorem Φ0 (n : ℤ) (e E P Ha Hb : Bool) : Φ n e 0 E P Ha Hb = 1 := rfl

/-- The column sum, as a function of the four flags. -/
def SS (n : ℕ) (G : Bool → Bool → Bool → Bool → ℤ) (Hb : Bool) : ℤ :=
  if Hb then G true true true true + n * G false false true false
  else G true false false false + G false true false false +
    (if Even n then G false false false true else 0) +
    ((n : ℤ) - 1 - (if Even n then 1 else 0)) * G false false false false

theorem sum_half (n : ℕ) (c : ℤ) :
    ∑ v ∈ Finset.range (n + 1), (if 2 * v = n then c else 0) = if Even n then c else 0 := by
  split_ifs with h
  · obtain ⟨k, rfl⟩ := h
    rw [Finset.sum_congr rfl (g := fun v => if v = k then c else 0) (fun v _ => by
      congr 1; apply propext; omega)]
    rw [Finset.sum_ite_eq']
    simp <;> omega
  · apply Finset.sum_eq_zero
    intro v _
    rw [if_neg]
    intro h2; exact h ⟨v, by omega⟩

theorem sum_pt (n x : ℕ) (hx : x ≤ n) (c : ℤ) :
    ∑ v ∈ Finset.range (n + 1), (if v = x then c else 0) = c := by
  rw [Finset.sum_ite_eq']; simp; omega

theorem L3 (n b : ℕ) (hb : b ≤ n) (G : Bool → Bool → Bool → Bool → ℤ) :
    ∑ v ∈ Finset.range (n + 1), G (decide (b = v)) (decide (b + v = n)) (decide (2 * b = n))
      (decide (2 * v = n)) = SS n G (decide (2 * b = n)) := by
  by_cases h : 2 * b = n
  · have : ∀ v ∈ Finset.range (n + 1), G (decide (b = v)) (decide (b + v = n)) (decide (2 * b = n))
        (decide (2 * v = n)) = G false false true false +
          (if v = b then G true true true true - G false false true false else 0) := by
      intro v _
      by_cases hv : v = b
      · subst hv
        rw [if_pos rfl, decide_eq_true rfl, decide_eq_true (show v + v = n by omega), decide_eq_true h]
        ring
      · rw [if_neg hv]
        rw [decide_eq_false (show ¬ b = v by omega), decide_eq_false (show ¬ b + v = n by omega),
          decide_eq_true h, decide_eq_false (show ¬ 2 * v = n by omega)]
        ring
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, sum_pt n b hb]
    simp [SS, h]
    ring
  · have : ∀ v ∈ Finset.range (n + 1), G (decide (b = v)) (decide (b + v = n)) (decide (2 * b = n))
        (decide (2 * v = n)) = G false false false false +
          (if v = b then G true false false false - G false false false false else 0) +
          (if v = n - b then G false true false false - G false false false false else 0) +
          (if 2 * v = n then G false false false true - G false false false false else 0) := by
      intro v _
      rw [decide_eq_false h]
      by_cases h1 : v = b
      · subst h1
        rw [if_pos rfl, if_neg (by omega), if_neg h, decide_eq_true rfl,
          decide_eq_false (show ¬ v + v = n by omega), decide_eq_false h]
        ring
      by_cases h2 : v = n - b
      · rw [if_neg h1, if_pos h2, if_neg (by omega), decide_eq_false (show ¬ b = v by omega),
          decide_eq_true (show b + v = n by omega), decide_eq_false (show ¬ 2 * v = n by omega)]
        ring
      by_cases h3 : 2 * v = n
      · rw [if_neg h1, if_neg h2, if_pos h3, decide_eq_false (show ¬ b = v by omega),
          decide_eq_false (show ¬ b + v = n by omega), decide_eq_true h3]
        ring
      · rw [if_neg h1, if_neg h2, if_neg h3, decide_eq_false (show ¬ b = v by omega),
          decide_eq_false (show ¬ b + v = n by omega), decide_eq_false h3]
        ring
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib, sum_pt n b hb, sum_pt n (n - b) (by omega), sum_half]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, SS, decide_eq_false h,
      Bool.false_eq_true, if_false]
    push_cast
    split_ifs <;> ring

theorem L4 (n x y : ℕ) (hx : x ≤ n) (hy : y ≤ n) (f : ℕ → ℤ) :
    ∑ v ∈ Finset.range (n + 1), (if v = x ∨ v = y then f v else 0) =
      f x + (if x = y then 0 else f y) := by
  by_cases h : x = y
  · subst h
    simp only [or_self, if_true, add_zero]
    rw [Finset.sum_ite_eq']; simp; omega
  · rw [if_neg h]
    rw [Finset.sum_congr rfl (g := fun v => (if v = x then f v else 0) + (if v = y then f v else 0))
      (fun v _ => by split_ifs <;> first | omega | ring)]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
    simp; omega

theorem L2 (n : ℕ) : ∀ m a b, a ≤ n → b ≤ n →
    T n m a b = Φ n (decide (Even n)) m (decide (a = b)) (decide (a + b = n)) (decide (2 * a = n))
      (decide (2 * b = n)) := by
  intro m
  induction m with
  | zero => intro a b _ _; rfl
  | succ m ih =>
    intro a b ha hb
    rw [T]
    by_cases h : a + b = n
    · rw [Finset.sum_congr rfl (g := fun v => T n m b v) (fun v _ => if_pos (Or.inl h))]
      rw [Finset.sum_congr rfl (fun v hv => ih b v hb (by simp at hv; omega)), L3 n b hb]
      rw [Φ, if_pos (decide_eq_true h)]
      simp only [SS, decide_eq_true_eq]
    · rw [Finset.sum_congr rfl (g := fun v => if v = n - a ∨ v = n - b then T n m b v else 0)
        (fun v hv => by simp only [h, false_or]; congr 1; apply propext; omega)]
      rw [L4 n (n - a) (n - b) (by omega) (by omega), ih b (n - a) hb (by omega),
        ih b (n - b) hb (by omega)]
      rw [Φ, decide_eq_false h]
      simp only [Bool.false_eq_true, if_false]
      have e1 : decide (b = n - a) = false := decide_eq_false (by omega)
      have e2 : decide (b + (n - a) = n) = decide (a = b) := decide_eq_decide.mpr (by omega)
      have e3 : decide (2 * (n - a) = n) = decide (2 * a = n) := decide_eq_decide.mpr (by omega)
      have e4 : decide (b = n - b) = decide (2 * b = n) := decide_eq_decide.mpr (by omega)
      have e5 : decide (b + (n - b) = n) = true := decide_eq_true (by omega)
      have e6 : decide (2 * (n - b) = n) = decide (2 * b = n) := decide_eq_decide.mpr (by omega)
      rw [e1, e2, e3, e4, e5, e6]
      congr 1
      by_cases hab : a = b
      · simp [hab]
      · rw [if_neg (by omega), decide_eq_false hab]
        rfl

theorem a_SS (n : ℕ) : a n = (n + 1 : ℤ) * SS n (Φ n (decide (Even n)) 6) false +
    (if Even n then SS n (Φ n (decide (Even n)) 6) true - SS n (Φ n (decide (Even n)) 6) false else 0) := by
  rw [a_eq]
  rw [Finset.sum_congr rfl (g := fun p => SS n (Φ n (decide (Even n)) 6) false +
      (if 2 * p = n then SS n (Φ n (decide (Even n)) 6) true - SS n (Φ n (decide (Even n)) 6) false else 0))
    (fun p hp => by
      rw [Finset.sum_congr rfl (fun q hq => L2 n 6 p q (by simp at hp; omega) (by simp at hq; omega))]
      rw [L3 n p (by simp at hp; omega)]
      by_cases h : 2 * p = n <;> simp [h])]
  rw [Finset.sum_add_distrib, sum_half]
  simp

theorem Pe1_1111 (n : ℤ) : Φ n true 1 true true true true = n + 1 := by
  rw [Φ]
  simp only [↓reduceIte, Φ0, Bool.false_eq_true]
  ring

theorem Pe1_0010 (n : ℤ) : Φ n true 1 false false true false = 2 := by
  rw [Φ]
  simp only [↓reduceIte, Φ0, Bool.false_eq_true]
  ring

theorem Pe1_0001 (n : ℤ) : Φ n true 1 false false false true = 2 := by
  rw [Φ]
  simp only [↓reduceIte, Φ0, Bool.false_eq_true]
  ring

theorem Pe1_0100 (n : ℤ) : Φ n true 1 false true false false = n + 1 := by
  rw [Φ]
  simp only [↓reduceIte, Φ0, Bool.false_eq_true]
  ring

theorem Pe1_1000 (n : ℤ) : Φ n true 1 true false false false = 1 := by
  rw [Φ]
  simp only [↓reduceIte, Φ0, Bool.false_eq_true]
  ring

theorem Pe1_0000 (n : ℤ) : Φ n true 1 false false false false = 2 := by
  rw [Φ]
  simp only [↓reduceIte, Φ0, Bool.false_eq_true]
  ring

theorem Pe2_1111 (n : ℤ) : Φ n true 2 true true true true = 3*n + 1 := by
  rw [Φ]
  simp only [↓reduceIte, Φ0, Pe1_1111, Pe1_0010, Bool.false_eq_true]
  ring

theorem Pe2_0010 (n : ℤ) : Φ n true 2 false false true false = n + 3 := by
  rw [Φ]
  simp only [↓reduceIte, Φ0, Pe1_0001, Pe1_0100, Bool.false_eq_true]
  ring

theorem Pe2_0001 (n : ℤ) : Φ n true 2 false false false true = n + 3 := by
  rw [Φ]
  simp only [↓reduceIte, Φ0, Pe1_0010, Pe1_1111, Bool.false_eq_true]
  ring

theorem Pe2_0100 (n : ℤ) : Φ n true 2 false true false false = 3*n := by
  rw [Φ]
  simp only [↓reduceIte, Φ0, Pe1_1000, Pe1_0100, Pe1_0001, Pe1_0000, Bool.false_eq_true]
  ring

theorem Pe2_1000 (n : ℤ) : Φ n true 2 true false false false = n + 1 := by
  rw [Φ]
  simp only [↓reduceIte, Φ0, Pe1_0100, Bool.false_eq_true]
  ring

theorem Pe2_0000 (n : ℤ) : Φ n true 2 false false false false = n + 3 := by
  rw [Φ]
  simp only [↓reduceIte, Φ0, Pe1_0000, Pe1_0100, Bool.false_eq_true]
  ring

theorem Pe3_1111 (n : ℤ) : Φ n true 3 true true true true = n^2 + 6*n + 1 := by
  rw [Φ]
  simp only [↓reduceIte, Φ0, Pe2_1111, Pe2_0010, Bool.false_eq_true]
  ring

theorem Pe3_0010 (n : ℤ) : Φ n true 3 false false true false = 4*n + 3 := by
  rw [Φ]
  simp only [↓reduceIte, Φ0, Pe2_0001, Pe2_0100, Bool.false_eq_true]
  ring

theorem Pe3_0001 (n : ℤ) : Φ n true 3 false false false true = 4*n + 4 := by
  rw [Φ]
  simp only [↓reduceIte, Φ0, Pe2_0010, Pe2_1111, Bool.false_eq_true]
  ring

theorem Pe3_0100 (n : ℤ) : Φ n true 3 false true false false = n^2 + 6*n - 2 := by
  rw [Φ]
  simp only [↓reduceIte, Φ0, Pe2_1000, Pe2_0100, Pe2_0001, Pe2_0000, Bool.false_eq_true]
  ring

theorem Pe3_1000 (n : ℤ) : Φ n true 3 true false false false = 3*n := by
  rw [Φ]
  simp only [↓reduceIte, Φ0, Pe2_0100, Bool.false_eq_true]
  ring

theorem Pe3_0000 (n : ℤ) : Φ n true 3 false false false false = 4*n + 3 := by
  rw [Φ]
  simp only [↓reduceIte, Φ0, Pe2_0000, Pe2_0100, Bool.false_eq_true]
  ring

theorem Pe4_1111 (n : ℤ) : Φ n true 4 true true true true = 5*n^2 + 9*n + 1 := by
  rw [Φ]
  simp only [↓reduceIte, Φ0, Pe3_1111, Pe3_0010, Bool.false_eq_true]
  ring

theorem Pe4_0010 (n : ℤ) : Φ n true 4 false false true false = n^2 + 10*n + 2 := by
  rw [Φ]
  simp only [↓reduceIte, Φ0, Pe3_0001, Pe3_0100, Bool.false_eq_true]
  ring

theorem Pe4_0001 (n : ℤ) : Φ n true 4 false false false true = n^2 + 10*n + 4 := by
  rw [Φ]
  simp only [↓reduceIte, Φ0, Pe3_0010, Pe3_1111, Bool.false_eq_true]
  ring

theorem Pe4_0100 (n : ℤ) : Φ n true 4 false true false false = 5*n^2 + 8*n - 4 := by
  rw [Φ]
  simp only [↓reduceIte, Φ0, Pe3_1000, Pe3_0100, Pe3_0001, Pe3_0000, Bool.false_eq_true]
  ring

theorem Pe4_1000 (n : ℤ) : Φ n true 4 true false false false = n^2 + 6*n - 2 := by
  rw [Φ]
  simp only [↓reduceIte, Φ0, Pe3_0100, Bool.false_eq_true]
  ring

theorem Pe4_0000 (n : ℤ) : Φ n true 4 false false false false = n^2 + 10*n + 1 := by
  rw [Φ]
  simp only [↓reduceIte, Φ0, Pe3_0000, Pe3_0100, Bool.false_eq_true]
  ring

theorem Pe5_1111 (n : ℤ) : Φ n true 5 true true true true = n^3 + 15*n^2 + 11*n + 1 := by
  rw [Φ]
  simp only [↓reduceIte, Φ0, Pe4_1111, Pe4_0010, Bool.false_eq_true]
  ring

theorem Pe5_0010 (n : ℤ) : Φ n true 5 false false true false = 6*n^2 + 18*n := by
  rw [Φ]
  simp only [↓reduceIte, Φ0, Pe4_0001, Pe4_0100, Bool.false_eq_true]
  ring

theorem Pe5_0001 (n : ℤ) : Φ n true 5 false false false true = 6*n^2 + 19*n + 3 := by
  rw [Φ]
  simp only [↓reduceIte, Φ0, Pe4_0010, Pe4_1111, Bool.false_eq_true]
  ring

theorem Pe5_0100 (n : ℤ) : Φ n true 5 false true false false = n^3 + 15*n^2 + 5*n - 4 := by
  rw [Φ]
  simp only [↓reduceIte, Φ0, Pe4_1000, Pe4_0100, Pe4_0001, Pe4_0000, Bool.false_eq_true]
  ring

theorem Pe5_1000 (n : ℤ) : Φ n true 5 true false false false = 5*n^2 + 8*n - 4 := by
  rw [Φ]
  simp only [↓reduceIte, Φ0, Pe4_0100, Bool.false_eq_true]
  ring

theorem Pe5_0000 (n : ℤ) : Φ n true 5 false false false false = 6*n^2 + 18*n - 3 := by
  rw [Φ]
  simp only [↓reduceIte, Φ0, Pe4_0000, Pe4_0100, Bool.false_eq_true]
  ring

theorem Pe6_1111 (n : ℤ) : Φ n true 6 true true true true = 7*n^3 + 33*n^2 + 11*n + 1 := by
  rw [Φ]
  simp only [↓reduceIte, Φ0, Pe5_1111, Pe5_0010, Bool.false_eq_true]
  ring

theorem Pe6_0010 (n : ℤ) : Φ n true 6 false false true false = n^3 + 21*n^2 + 24*n - 1 := by
  rw [Φ]
  simp only [↓reduceIte, Φ0, Pe5_0001, Pe5_0100, Bool.false_eq_true]
  ring

theorem Pe6_1000 (n : ℤ) : Φ n true 6 true false false false = n^3 + 15*n^2 + 5*n - 4 := by
  rw [Φ]
  simp only [↓reduceIte, Φ0, Pe5_0100, Bool.false_eq_true]
  ring

theorem Pe6_0100 (n : ℤ) : Φ n true 6 false true false false = 7*n^3 + 32*n^2 - 7*n + 1 := by
  rw [Φ]
  simp only [↓reduceIte, Φ0, Pe5_1000, Pe5_0100, Pe5_0001, Pe5_0000, Bool.false_eq_true]
  ring

theorem Pe6_0001 (n : ℤ) : Φ n true 6 false false false true = n^3 + 21*n^2 + 29*n + 1 := by
  rw [Φ]
  simp only [↓reduceIte, Φ0, Pe5_0010, Pe5_1111, Bool.false_eq_true]
  ring

theorem Pe6_0000 (n : ℤ) : Φ n true 6 false false false false = n^3 + 21*n^2 + 23*n - 7 := by
  rw [Φ]
  simp only [↓reduceIte, Φ0, Pe5_0000, Pe5_0100, Bool.false_eq_true]
  ring

theorem Po1_1111 (n : ℤ) : Φ n false 1 true true true true = n + 1 := by
  rw [Φ]
  simp only [↓reduceIte, Φ0, Bool.false_eq_true]
  ring

theorem Po1_0010 (n : ℤ) : Φ n false 1 false false true false = 2 := by
  rw [Φ]
  simp only [↓reduceIte, Φ0, Bool.false_eq_true]
  ring

theorem Po1_0001 (n : ℤ) : Φ n false 1 false false false true = 2 := by
  rw [Φ]
  simp only [↓reduceIte, Φ0, Bool.false_eq_true]
  ring

theorem Po1_0100 (n : ℤ) : Φ n false 1 false true false false = n + 1 := by
  rw [Φ]
  simp only [↓reduceIte, Φ0, Bool.false_eq_true]
  ring

theorem Po1_1000 (n : ℤ) : Φ n false 1 true false false false = 1 := by
  rw [Φ]
  simp only [↓reduceIte, Φ0, Bool.false_eq_true]
  ring

theorem Po1_0000 (n : ℤ) : Φ n false 1 false false false false = 2 := by
  rw [Φ]
  simp only [↓reduceIte, Φ0, Bool.false_eq_true]
  ring

theorem Po2_1111 (n : ℤ) : Φ n false 2 true true true true = 3*n + 1 := by
  rw [Φ]
  simp only [↓reduceIte, Φ0, Po1_1111, Po1_0010, Bool.false_eq_true]
  ring

theorem Po2_0010 (n : ℤ) : Φ n false 2 false false true false = n + 3 := by
  rw [Φ]
  simp only [↓reduceIte, Φ0, Po1_0001, Po1_0100, Bool.false_eq_true]
  ring

theorem Po2_0001 (n : ℤ) : Φ n false 2 false false false true = n + 3 := by
  rw [Φ]
  simp only [↓reduceIte, Φ0, Po1_0010, Po1_1111, Bool.false_eq_true]
  ring

theorem Po2_0100 (n : ℤ) : Φ n false 2 false true false false = 3*n := by
  rw [Φ]
  simp only [↓reduceIte, Φ0, Po1_1000, Po1_0100, Po1_0000, Bool.false_eq_true]
  ring

theorem Po2_1000 (n : ℤ) : Φ n false 2 true false false false = n + 1 := by
  rw [Φ]
  simp only [↓reduceIte, Φ0, Po1_0100, Bool.false_eq_true]
  ring

theorem Po2_0000 (n : ℤ) : Φ n false 2 false false false false = n + 3 := by
  rw [Φ]
  simp only [↓reduceIte, Φ0, Po1_0000, Po1_0100, Bool.false_eq_true]
  ring

theorem Po3_1111 (n : ℤ) : Φ n false 3 true true true true = n^2 + 6*n + 1 := by
  rw [Φ]
  simp only [↓reduceIte, Φ0, Po2_1111, Po2_0010, Bool.false_eq_true]
  ring

theorem Po3_0010 (n : ℤ) : Φ n false 3 false false true false = 4*n + 3 := by
  rw [Φ]
  simp only [↓reduceIte, Φ0, Po2_0001, Po2_0100, Bool.false_eq_true]
  ring

theorem Po3_0001 (n : ℤ) : Φ n false 3 false false false true = 4*n + 4 := by
  rw [Φ]
  simp only [↓reduceIte, Φ0, Po2_0010, Po2_1111, Bool.false_eq_true]
  ring

theorem Po3_0100 (n : ℤ) : Φ n false 3 false true false false = n^2 + 6*n - 2 := by
  rw [Φ]
  simp only [↓reduceIte, Φ0, Po2_1000, Po2_0100, Po2_0000, Bool.false_eq_true]
  ring

theorem Po3_1000 (n : ℤ) : Φ n false 3 true false false false = 3*n := by
  rw [Φ]
  simp only [↓reduceIte, Φ0, Po2_0100, Bool.false_eq_true]
  ring

theorem Po3_0000 (n : ℤ) : Φ n false 3 false false false false = 4*n + 3 := by
  rw [Φ]
  simp only [↓reduceIte, Φ0, Po2_0000, Po2_0100, Bool.false_eq_true]
  ring

theorem Po4_1111 (n : ℤ) : Φ n false 4 true true true true = 5*n^2 + 9*n + 1 := by
  rw [Φ]
  simp only [↓reduceIte, Φ0, Po3_1111, Po3_0010, Bool.false_eq_true]
  ring

theorem Po4_0010 (n : ℤ) : Φ n false 4 false false true false = n^2 + 10*n + 2 := by
  rw [Φ]
  simp only [↓reduceIte, Φ0, Po3_0001, Po3_0100, Bool.false_eq_true]
  ring

theorem Po4_0001 (n : ℤ) : Φ n false 4 false false false true = n^2 + 10*n + 4 := by
  rw [Φ]
  simp only [↓reduceIte, Φ0, Po3_0010, Po3_1111, Bool.false_eq_true]
  ring

theorem Po4_0100 (n : ℤ) : Φ n false 4 false true false false = 5*n^2 + 8*n - 5 := by
  rw [Φ]
  simp only [↓reduceIte, Φ0, Po3_1000, Po3_0100, Po3_0000, Bool.false_eq_true]
  ring

theorem Po4_1000 (n : ℤ) : Φ n false 4 true false false false = n^2 + 6*n - 2 := by
  rw [Φ]
  simp only [↓reduceIte, Φ0, Po3_0100, Bool.false_eq_true]
  ring

theorem Po4_0000 (n : ℤ) : Φ n false 4 false false false false = n^2 + 10*n + 1 := by
  rw [Φ]
  simp only [↓reduceIte, Φ0, Po3_0000, Po3_0100, Bool.false_eq_true]
  ring

theorem Po5_1111 (n : ℤ) : Φ n false 5 true true true true = n^3 + 15*n^2 + 11*n + 1 := by
  rw [Φ]
  simp only [↓reduceIte, Φ0, Po4_1111, Po4_0010, Bool.false_eq_true]
  ring

theorem Po5_0010 (n : ℤ) : Φ n false 5 false false true false = 6*n^2 + 18*n - 1 := by
  rw [Φ]
  simp only [↓reduceIte, Φ0, Po4_0001, Po4_0100, Bool.false_eq_true]
  ring

theorem Po5_0001 (n : ℤ) : Φ n false 5 false false false true = 6*n^2 + 19*n + 3 := by
  rw [Φ]
  simp only [↓reduceIte, Φ0, Po4_0010, Po4_1111, Bool.false_eq_true]
  ring

theorem Po5_0100 (n : ℤ) : Φ n false 5 false true false false = n^3 + 15*n^2 + 5*n - 8 := by
  rw [Φ]
  simp only [↓reduceIte, Φ0, Po4_1000, Po4_0100, Po4_0000, Bool.false_eq_true]
  ring

theorem Po5_1000 (n : ℤ) : Φ n false 5 true false false false = 5*n^2 + 8*n - 5 := by
  rw [Φ]
  simp only [↓reduceIte, Φ0, Po4_0100, Bool.false_eq_true]
  ring

theorem Po5_0000 (n : ℤ) : Φ n false 5 false false false false = 6*n^2 + 18*n - 4 := by
  rw [Φ]
  simp only [↓reduceIte, Φ0, Po4_0000, Po4_0100, Bool.false_eq_true]
  ring

theorem Po6_1111 (n : ℤ) : Φ n false 6 true true true true = 7*n^3 + 33*n^2 + 10*n + 1 := by
  rw [Φ]
  simp only [↓reduceIte, Φ0, Po5_1111, Po5_0010, Bool.false_eq_true]
  ring

theorem Po6_0010 (n : ℤ) : Φ n false 6 false false true false = n^3 + 21*n^2 + 24*n - 5 := by
  rw [Φ]
  simp only [↓reduceIte, Φ0, Po5_0001, Po5_0100, Bool.false_eq_true]
  ring

theorem Po6_1000 (n : ℤ) : Φ n false 6 true false false false = n^3 + 15*n^2 + 5*n - 8 := by
  rw [Φ]
  simp only [↓reduceIte, Φ0, Po5_0100, Bool.false_eq_true]
  ring

theorem Po6_0100 (n : ℤ) : Φ n false 6 false true false false = 7*n^3 + 32*n^2 - 9*n - 9 := by
  rw [Φ]
  simp only [↓reduceIte, Φ0, Po5_1000, Po5_0100, Po5_0000, Bool.false_eq_true]
  ring

theorem Po6_0001 (n : ℤ) : Φ n false 6 false false false true = n^3 + 21*n^2 + 29*n := by
  rw [Φ]
  simp only [↓reduceIte, Φ0, Po5_0010, Po5_1111, Bool.false_eq_true]
  ring

theorem Po6_0000 (n : ℤ) : Φ n false 6 false false false false = n^3 + 21*n^2 + 23*n - 12 := by
  rw [Φ]
  simp only [↓reduceIte, Φ0, Po5_0000, Po5_0100, Bool.false_eq_true]
  ring



theorem a_even (n : ℕ) (h : Even n) :
    (a n : ℚ) = 1 + 22 * (n : ℚ) + 31 * (n : ℚ) ^ 2 + 77 * (n : ℚ) ^ 3 + 29 * (n : ℚ) ^ 4 + (n : ℚ) ^ 5 := by
  have hz : a n = 1 + 22 * (n : ℤ) + 31 * (n : ℤ) ^ 2 + 77 * (n : ℤ) ^ 3 + 29 * (n : ℤ) ^ 4 + (n : ℤ) ^ 5 := by
    rw [a_SS, decide_eq_true h]
    simp only [SS, h, if_true, ↓reduceIte, Bool.false_eq_true, Pe6_1111, Pe6_0010, Pe6_1000, Pe6_0100,
      Pe6_0001, Pe6_0000]
    ring
  rw [hz]; push_cast; ring

theorem a_odd (n : ℕ) (h : ¬ Even n) :
    (a n : ℚ) = -5 - 44 * (n : ℚ) + 10 * (n : ℚ) ^ 2 + 77 * (n : ℚ) ^ 3 + 29 * (n : ℚ) ^ 4 + (n : ℚ) ^ 5 := by
  have hz : a n = -5 - 44 * (n : ℤ) + 10 * (n : ℤ) ^ 2 + 77 * (n : ℤ) ^ 3 + 29 * (n : ℤ) ^ 4 + (n : ℤ) ^ 5 := by
    rw [a_SS, decide_eq_false h]
    simp only [SS, h, if_false, ↓reduceIte, Bool.false_eq_true, Po6_1111, Po6_0010, Po6_1000, Po6_0100,
      Po6_0001, Po6_0000]
    ring
  rw [hz]; push_cast; ring

def Q (m : ℕ) : ℚ := if Even m then 1 + 22 * (m : ℚ) + 31 * (m : ℚ) ^ 2 + 77 * (m : ℚ) ^ 3 + 29 * (m : ℚ) ^ 4 + (m : ℚ) ^ 5
  else -5 - 44 * (m : ℚ) + 10 * (m : ℚ) ^ 2 + 77 * (m : ℚ) ^ 3 + 29 * (m : ℚ) ^ 4 + (m : ℚ) ^ 5

theorem aQ (m : ℕ) : (a m : ℚ) = Q m := by
  unfold Q; split_ifs with h
  · exact a_even m h
  · exact a_odd m h

theorem rec10 (k : ℕ) (hk : 10 ≤ k) :
    Q k - 3 * Q (k - 1) + 8 * Q (k - 3) - 6 * Q (k - 4) - 6 * Q (k - 5) + 8 * Q (k - 6) - 3 * Q (k - 8)
      + Q (k - 9) = 0 := by
  obtain ⟨t, rfl | rfl⟩ : ∃ t, k = 2 * t + 10 ∨ k = 2 * t + 11 := ⟨(k - 10) / 2, by omega⟩
  · rw [show 2 * t + 10 - 1 = 2 * t + 9 by omega, show 2 * t + 10 - 3 = 2 * t + 7 by omega,
      show 2 * t + 10 - 4 = 2 * t + 6 by omega, show 2 * t + 10 - 5 = 2 * t + 5 by omega,
      show 2 * t + 10 - 6 = 2 * t + 4 by omega, show 2 * t + 10 - 8 = 2 * t + 2 by omega,
      show 2 * t + 10 - 9 = 2 * t + 1 by omega]
    simp only [Q, (show Even (2 * t + 10) from ⟨t + 5, by ring⟩), (show ¬ Even (2 * t + 9) from Nat.not_even_iff_odd.mpr ⟨t + 4, by ring⟩), (show ¬ Even (2 * t + 7) from Nat.not_even_iff_odd.mpr ⟨t + 3, by ring⟩), (show Even (2 * t + 6) from ⟨t + 3, by ring⟩), (show ¬ Even (2 * t + 5) from Nat.not_even_iff_odd.mpr ⟨t + 2, by ring⟩), (show Even (2 * t + 4) from ⟨t + 2, by ring⟩), (show Even (2 * t + 2) from ⟨t + 1, by ring⟩), (show ¬ Even (2 * t + 1) from Nat.not_even_iff_odd.mpr ⟨t + 0, by ring⟩), if_true, if_false]
    push_cast; ring
  · rw [show 2 * t + 11 - 1 = 2 * t + 10 by omega, show 2 * t + 11 - 3 = 2 * t + 8 by omega,
      show 2 * t + 11 - 4 = 2 * t + 7 by omega, show 2 * t + 11 - 5 = 2 * t + 6 by omega,
      show 2 * t + 11 - 6 = 2 * t + 5 by omega, show 2 * t + 11 - 8 = 2 * t + 3 by omega,
      show 2 * t + 11 - 9 = 2 * t + 2 by omega]
    simp only [Q, (show ¬ Even (2 * t + 11) from Nat.not_even_iff_odd.mpr ⟨t + 5, by ring⟩), (show Even (2 * t + 10) from ⟨t + 5, by ring⟩), (show Even (2 * t + 8) from ⟨t + 4, by ring⟩), (show ¬ Even (2 * t + 7) from Nat.not_even_iff_odd.mpr ⟨t + 3, by ring⟩), (show Even (2 * t + 6) from ⟨t + 3, by ring⟩), (show ¬ Even (2 * t + 5) from Nat.not_even_iff_odd.mpr ⟨t + 2, by ring⟩), (show ¬ Even (2 * t + 3) from Nat.not_even_iff_odd.mpr ⟨t + 1, by ring⟩), (show Even (2 * t + 2) from ⟨t + 1, by ring⟩), if_true, if_false]
    push_cast; ring

open PowerSeries in
theorem gf : PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) * ((1 - X) ^ 6 * (1 + X) ^ 3 : PowerSeries ℚ) = X * (68 + 1077 * X + 781 * X ^ 2 + 633 * X ^ 3 - 1143 * X ^ 4 - 561 * X ^ 5 + 103 * X ^ 6 + 3 * X ^ 7 - X ^ 8) := by
  set f : ℕ → ℚ := fun n => if n < 1 then 0 else (a n : ℚ) with hf
  set A : PowerSeries ℚ := PowerSeries.mk f with hA
  have hD : A * ((1 - X) ^ 6 * (1 + X) ^ 3 : PowerSeries ℚ) =
      A - C (3 : ℚ) * (A * X ^ 1) + C (8 : ℚ) * (A * X ^ 3) - C (6 : ℚ) * (A * X ^ 4)
        - C (6 : ℚ) * (A * X ^ 5) + C (8 : ℚ) * (A * X ^ 6) - C (3 : ℚ) * (A * X ^ 8) + A * X ^ 9 := by
    simp only [map_ofNat]; ring
  have hN : X * (68 + 1077 * X + 781 * X ^ 2 + 633 * X ^ 3 - 1143 * X ^ 4 - 561 * X ^ 5 + 103 * X ^ 6
      + 3 * X ^ 7 - X ^ 8 : PowerSeries ℚ) =
      C (68 : ℚ) * X ^ 1 + C (1077 : ℚ) * X ^ 2 + C (781 : ℚ) * X ^ 3 + C (633 : ℚ) * X ^ 4
        - C (1143 : ℚ) * X ^ 5 - C (561 : ℚ) * X ^ 6 + C (103 : ℚ) * X ^ 7 + C (3 : ℚ) * X ^ 8 - X ^ 9 := by
    simp only [map_ofNat]; ring
  rw [hD, hN]
  ext k
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', hA, coeff_mk, coeff_X_pow]
  have hfk : ∀ m, 1 ≤ m → f m = Q m := fun m hm => by
    simp only [hf, show ¬ m < 1 by omega, if_false, aQ]
  rcases Nat.lt_or_ge k 10 with h | h
  · have f0 : f 0 = 0 := by simp [hf]
    interval_cases k <;> simp [f0, hfk, Q] <;> norm_num
  · simp only [show 1 ≤ k by omega, show 3 ≤ k by omega, show 4 ≤ k by omega, show 5 ≤ k by omega,
      show 6 ≤ k by omega, show 8 ≤ k by omega, show 9 ≤ k by omega, if_true,
      show k ≠ 1 by omega, show k ≠ 2 by omega, show k ≠ 3 by omega, show k ≠ 4 by omega,
      show k ≠ 5 by omega, show k ≠ 6 by omega, show k ≠ 7 by omega, show k ≠ 8 by omega,
      show k ≠ 9 by omega, show 2 ≤ k by omega, show 7 ≤ k by omega, coeff_C,
      show k - 1 ≠ 0 by omega, show k - 2 ≠ 0 by omega, show k - 3 ≠ 0 by omega, show k - 4 ≠ 0 by omega,
      show k - 5 ≠ 0 by omega, show k - 6 ≠ 0 by omega, show k - 7 ≠ 0 by omega, show k - 8 ≠ 0 by omega,
      if_false, hfk k (by omega), hfk (k - 1) (by omega), hfk (k - 3) (by omega),
      hfk (k - 4) (by omega), hfk (k - 5) (by omega), hfk (k - 6) (by omega), hfk (k - 8) (by omega),
      hfk (k - 9) (by omega)]
    linear_combination rec10 k h

end OMA.Helpers_a245875

open OMA.Helpers_a245875 in
theorem OMA.solution : type_of% @OMA.S_oeis_a245875.main :=
  ⟨gf, fun n _ h => a_even n h, fun n _ h => a_odd n (Nat.not_even_iff_odd.mpr h)⟩
