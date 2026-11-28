import OMAStatements.S_oeis_a245876

/-!
# Counting the nine-entry arrays of A245876

The count keeps four facts about the last two symbols: whether they are equal,
whether they are complementary, and whether either is its own complement.
The transfer recurrence and its justification for arbitrary continuation lengths
are adapted from ppleskov's proof of A245875 (project PR 29989).
Seven transitions give the parity polynomials for nine entries.
-/

namespace OMA.Helpers_a245876
open OMA.S_oeis_a245876

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

theorem win {n : ℕ} (x : Fin 9 → Fin (n + 1)) (i : ℕ) :
    (∃ s < (3 : ℕ), ∃ t < (3 : ℕ), s < t ∧ get x (i + s) + get x (i + t) = n) ↔
      (get x i + get x (i + 1) = n ∨ get x i + get x (i + 2) = n ∨ get x (i + 1) + get x (i + 2) = n) := by
  constructor
  · rintro ⟨s, hs, t, ht, hst, e⟩
    interval_cases s <;> interval_cases t <;> simp_all
  · rintro (h | h | h)
    · exact ⟨0, by norm_num, 1, by norm_num, by norm_num, by simpa using h⟩
    · exact ⟨0, by norm_num, 2, by norm_num, by norm_num, by simpa using h⟩
    · exact ⟨1, by norm_num, 2, by norm_num, by norm_num, h⟩

theorem good_iff {n : ℕ} (x : Fin 9 → Fin (n + 1)) :
    good x = ch n 7 (x 0) (x 1) (fun i => x ⟨i + 2, by omega⟩) := by
  apply Bool.eq_iff_iff.mpr
  simp only [good, decide_eq_true_eq, win]
  simp only [ch, Bool.and_eq_true, decide_eq_true_eq, and_true]
  simp only [Fin.tail, Fin.val_succ, Fin.val_zero, S_oeis_a245876.get]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have := h 0 (by norm_num); simpa using this
    · have := h 1 (by norm_num); simpa using this
    · have := h 2 (by norm_num); simpa using this
    · have := h 3 (by norm_num); simpa using this
    · have := h 4 (by norm_num); simpa using this
    · have := h 5 (by norm_num); simpa using this
    · have := h 6 (by norm_num); simpa using this
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6⟩ i hi
    interval_cases i <;> simp_all

theorem a_eq (n : ℕ) : a n = ∑ p ∈ Finset.range (n + 1), ∑ q ∈ Finset.range (n + 1), T n 7 p q := by
  unfold a
  rw [Finset.card_filter, Nat.cast_sum, sum_cons]
  rw [← Fin.sum_univ_eq_sum_range (fun p => ∑ q ∈ Finset.range (n + 1), T n 7 p q)]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [sum_cons, ← Fin.sum_univ_eq_sum_range (fun q => T n 7 p q)]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [← cnt, Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  rw [good_iff]
  rfl

end OMA.Helpers_a245876

namespace OMA.Helpers_a245876
open OMA.S_oeis_a245876

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
    simp
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
      (fun v _ => by split_ifs <;> omega)]
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

theorem a_SS (n : ℕ) : a n = (n + 1 : ℤ) * SS n (Φ n (decide (Even n)) 7) false +
    (if Even n then SS n (Φ n (decide (Even n)) 7) true - SS n (Φ n (decide (Even n)) 7) false else 0) := by
  rw [a_eq]
  rw [Finset.sum_congr rfl (g := fun p => SS n (Φ n (decide (Even n)) 7) false +
      (if 2 * p = n then SS n (Φ n (decide (Even n)) 7) true - SS n (Φ n (decide (Even n)) 7) false else 0))
    (fun p hp => by
      rw [Finset.sum_congr rfl (fun q hq => L2 n 7 p q (by simp at hp; omega) (by simp at hq; omega))]
      rw [L3 n p (by simp at hp; omega)]
      by_cases h : 2 * p = n <;> simp [h])]
  rw [Finset.sum_add_distrib, sum_half]
  simp

end OMA.Helpers_a245876

namespace OMA.Helpers_a245876

set_option maxHeartbeats 1500000 in
theorem eval_even (n : ℕ) (h : Even n) :
    (n + 1 : ℤ) * SS n (Φ n (decide (Even n)) 7) false +
      (if Even n then SS n (Φ n (decide (Even n)) 7) true -
        SS n (Φ n (decide (Even n)) 7) false else 0) =
      1 + 37 * (n : ℤ) + 43 * (n : ℤ) ^ 2 + 126 * (n : ℤ) ^ 3 + 89 * (n : ℤ) ^ 4 + 9 * (n : ℤ) ^ 5 := by
  simp only [SS, h, decide_true, Φ, Bool.false_eq_true, ↓reduceIte]
  ring

set_option maxHeartbeats 1500000 in
theorem eval_odd (n : ℕ) (h : ¬ Even n) :
    (n + 1 : ℤ) * SS n (Φ n (decide (Even n)) 7) false +
      (if Even n then SS n (Φ n (decide (Even n)) 7) true -
        SS n (Φ n (decide (Even n)) 7) false else 0) =
      7 - 76 * (n : ℤ) - 41 * (n : ℤ) ^ 2 + 122 * (n : ℤ) ^ 3 + 89 * (n : ℤ) ^ 4 + 9 * (n : ℤ) ^ 5 := by
  simp only [SS, h, decide_false, Φ, Bool.false_eq_true, ↓reduceIte]
  ring

end OMA.Helpers_a245876

/-! The offset-one generating function of the two parity polynomials. -/

namespace OMA.Helpers_a245876

open S_oeis_a245876 PowerSeries

set_option maxHeartbeats 3000000 in
theorem gf_of_forms
    (a_even : ∀ n : ℕ, Even n → a n =
      1 + 37*(n:ℤ) + 43*(n:ℤ)^2 + 126*(n:ℤ)^3 + 89*(n:ℤ)^4 + 9*(n:ℤ)^5)
    (a_odd : ∀ n : ℕ, ¬ Even n → a n =
      7 - 76*(n:ℤ) - 41*(n:ℤ)^2 + 122*(n:ℤ)^3 + 89*(n:ℤ)^4 + 9*(n:ℤ)^5) :
    PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) *
      ((1-X)^6 * (1+X)^4 : PowerSeries ℚ) =
    X * (110 + 2747*X + 5836*X^2 + 8680*X^3 + 3456*X^4 - 2178*X^5 -
      1148*X^6 - 224*X^7 + 2*X^8 - X^9) := by
  let P (x : ℚ) := 1 + 37*x + 43*x^2 + 126*x^3 + 89*x^4 + 9*x^5
  let Q (x : ℚ) := 7 - 76*x - 41*x^2 + 122*x^3 + 89*x^4 + 9*x^5
  let b (n : ℕ) : ℚ := if n < 1 then 0 else a n
  have hb (n : ℕ) : b n = if n < 1 then 0 else if n%2=0 then P n else Q n := by
    dsimp only [b]
    split_ifs with h he
    · rfl
    · dsimp only [P]
      exact_mod_cast a_even n (Nat.even_iff.mpr he)
    · dsimp only [Q]
      exact_mod_cast a_odd n (fun h => he (Nat.even_iff.mp h))
  let A := PowerSeries.mk b
  have hd : A*((1-X)^6 * (1+X)^4) =
      A - C 2*(A*X^1) - C 3*(A*X^2) + C 8*(A*X^3) + C 2*(A*X^4) -
      C 12*(A*X^5) + C 2*(A*X^6) + C 8*(A*X^7) - C 3*(A*X^8) -
      C 2*(A*X^9) + A*X^10 := by
    simp only [map_ofNat]
    ring
  have hn : X*(110 + 2747*X + 5836*X^2 + 8680*X^3 + 3456*X^4 - 2178*X^5 -
        1148*X^6 - 224*X^7 + 2*X^8 - X^9 : PowerSeries ℚ) =
      C 110*X^1 + C 2747*X^2 + C 5836*X^3 + C 8680*X^4 + C 3456*X^5 -
      C 2178*X^6 - C 1148*X^7 - C 224*X^8 + C 2*X^9 - X^10 := by
    simp only [map_ofNat]
    ring
  change A*_ = _
  rw [hd, hn]
  ext n
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', coeff_C, coeff_X_pow, A, coeff_mk]
  by_cases hlarge : 10 < n
  · simp (disch := omega) only [if_pos, if_neg]
    simp only [hb]
    by_cases h : n%2=0 <;> simp (disch := omega) only [if_pos, if_neg] <;>
      dsimp only [P, Q] <;>
      try simp (disch := omega) only [Nat.cast_sub, Nat.cast_ofNat]
    all_goals ring
  · interval_cases n <;> norm_num [hb, P, Q]

end OMA.Helpers_a245876

namespace OMA.Helpers_a245876

open OMA.S_oeis_a245876

private theorem even_count (n : ℕ) (h : Even n) : a n =
    1 + 37*(n:ℤ) + 43*(n:ℤ)^2 + 126*(n:ℤ)^3 + 89*(n:ℤ)^4 + 9*(n:ℤ)^5 :=
  (a_SS n).trans (eval_even n h)

private theorem odd_count (n : ℕ) (h : ¬ Even n) : a n =
    7 - 76*(n:ℤ) - 41*(n:ℤ)^2 + 122*(n:ℤ)^3 + 89*(n:ℤ)^4 + 9*(n:ℤ)^5 :=
  (a_SS n).trans (eval_odd n h)

end OMA.Helpers_a245876

open OMA.Helpers_a245876 in
theorem OMA.solution : type_of% @OMA.S_oeis_a245876.main := by
  refine ⟨gf_of_forms even_count odd_count, ?_, ?_⟩
  · intro n _ h
    exact_mod_cast even_count n h
  · intro n _ h
    exact_mod_cast odd_count n (Nat.not_even_iff_odd.mpr h)
