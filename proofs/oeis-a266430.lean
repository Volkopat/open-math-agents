import OMAStatements.S_oeis_a266430

namespace A266430Proof

open OMA.S_oeis_a266430

abbrev Col := Fin 4 → Fin 2
abbrev Mask := Fin 3 → Bool

def full : Mask := fun _ => true

def colLE (c d : Col) : Prop :=
  toLex c ≤ toLex d ∧ (∑ i, (c i : ℕ)) ≤ ∑ i, (d i : ℕ)

instance (c d : Col) : Decidable (colLE c d) := by
  have h : toLex c ≤ toLex d ↔ c = d ∨ ∃ i, (∀ j < i, c j = d j) ∧ c i < d i := by
    rw [le_iff_eq_or_lt]
    rfl
  letI : Decidable (toLex c ≤ toLex d) := decidable_of_iff _ h.symm
  unfold colLE
  infer_instance

def ok (m : Mask) (c : Col) : Prop := ∀ j, m j = true → c j.castSucc ≤ c j.succ

instance (m : Mask) (c : Col) : Decidable (ok m c) := by unfold ok; infer_instance

def upd (m : Mask) (c : Col) : Mask :=
  fun j => m j && decide (c j.castSucc = c j.succ)

def F : ℕ → Col → Mask → ℤ
  | 0, _, _ => 1
  | n+1, c, m => ∑ d : Col, if colLE c d ∧ ok m d then F n d (upd m d) else 0

def total (k : ℕ) : ℤ := ∑ c : Col, if ok full c then F k c (upd full c) else 0

private def rowsOrdered (m : Mask) (l : List Col) : Prop :=
  ∀ j, m j = true → l.map (fun c => c j.castSucc) ≤ l.map (fun c => c j.succ)

private theorem rowlex {a b : Fin 2} {s t : List (Fin 2)} :
    a :: s ≤ b :: t ↔ a < b ∨ a = b ∧ s ≤ t := by
  change (a :: s = b :: t ∨ List.Lex (· < ·) (a :: s) (b :: t)) ↔
    a < b ∨ a = b ∧ (s = t ∨ List.Lex (· < ·) s t)
  rw [List.cons_lex_cons_iff, List.cons.injEq]
  tauto

private theorem rows_cons (m : Mask) (c : Col) (l : List Col) :
    rowsOrdered m (c :: l) ↔ ok m c ∧ rowsOrdered (upd m c) l := by
  simp only [rowsOrdered, List.map_cons, ok, upd,
    Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · intro h
    constructor
    · intro j hj
      rcases rowlex.mp (h j hj) with hlt | ⟨he,_⟩
      · exact hlt.le
      · exact he.le
    · rintro j ⟨hj,he⟩
      rcases rowlex.mp (h j hj) with hlt | ⟨_,hl⟩
      · exact False.elim (hlt.ne he)
      · exact hl
  · rintro ⟨h,h'⟩ j hj
    apply rowlex.mpr
    rcases lt_or_eq_of_le (h j hj) with hlt | he
    · exact Or.inl hlt
    · exact Or.inr ⟨he,h' j ⟨hj,he⟩⟩

private def Tail (c : Col) (m : Mask) (l : List Col) : Prop :=
  (c :: l).IsChain colLE ∧ rowsOrdered m l

private theorem tail_cons (c d : Col) (m : Mask) (l : List Col) :
    Tail c m (d :: l) ↔ (colLE c d ∧ ok m d) ∧ Tail d (upd m d) l := by
  simp only [Tail, List.isChain_cons_cons, rows_cons]
  tauto

private theorem solution_cons (c : Col) (l : List Col) :
    IsSolution (c :: l) ↔ ok full c ∧ Tail c (upd full c) l := by
  have h : (∀ j : Fin 3,
      (c :: l).map (fun r => r j.castSucc) ≤ (c :: l).map (fun r => r j.succ)) ↔
      rowsOrdered full (c :: l) := by simp [rowsOrdered,full]
  unfold IsSolution
  rw [h, rows_cons]
  change _ ∧ _ ∧ _ ↔ _ ∧ _ ∧ _
  tauto

private def toCols {n : ℕ} (l : List Col) (h : l.length = n) : Fin n → Col :=
  fun i => l.get (i.cast h.symm)

private theorem recover {n : ℕ} (l : List Col) (h : l.length = n) :
    List.ofFn (toCols l h) = l := by
  subst n
  exact List.ofFn_get l

private def arraysEquiv (n : ℕ) :
    {l : List Col // l.length = n ∧ IsSolution l} ≃ {x : Fin n → Col // IsSolution (List.ofFn x)} where
  toFun l := ⟨toCols l.val l.prop.1, by rw [recover]; exact l.prop.2⟩
  invFun x := ⟨List.ofFn x.val,List.length_ofFn,x.prop⟩
  left_inv l := Subtype.ext (recover l.val l.prop.1)
  right_inv x := Subtype.ext (List.ofFn_injective (recover (List.ofFn x.val) List.length_ofFn))

private theorem sum_cols {n : ℕ} (f : (Fin (n+1) → Col) → ℤ) :
    (∑ x, f x) = ∑ c : Col, ∑ x : Fin n → Col, f (Fin.cons c x) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) => Col)).sum_comp f, Fintype.sum_prod_type]
  rfl

private noncomputable def tails (n : ℕ) (c : Col) (m : Mask) : ℤ := by
  classical
  exact ∑ x : Fin n → Col, if Tail c m (List.ofFn x) then 1 else 0

private theorem tails_eq (n : ℕ) (c : Col) (m : Mask) : tails n c m = F n c m := by
  classical
  induction n generalizing c m with
  | zero => simp [tails, Tail, rowsOrdered, F]
  | succ n ih =>
    unfold tails
    rw [sum_cols]
    simp only [List.ofFn_cons, tail_cons, ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero]
    change (∑ d : Col, if colLE c d then if ok m d then tails n d (upd m d) else 0 else 0) = _
    simp only [ih,F,ite_and]

theorem count_arrays (k : ℕ) : (a (k+1) : ℤ) = total k := by
  classical
  rw [a, Nat.card_congr (arraysEquiv (k+1)), Nat.card_eq_fintype_card, Fintype.card_subtype,
    ← Finset.sum_boole, sum_cols]
  simp only [List.ofFn_cons, solution_cons, ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero]
  change (∑ c : Col, if ok full c then tails k c (upd full c) else 0) = _
  simp only [tails_eq,total]

/-- Coefficients counting chains with exactly i strict changes of column.
The mask records adjacent rows that still agree on the prefix. -/
private def coefficients (c : Col) (m : Mask) : Array ℤ :=
  let ci := 8*(c 0 : ℕ) + 4*(c 1 : ℕ) + 2*(c 2 : ℕ) + (c 3 : ℕ)
  let p := upd m c
  let mi := 4*(p 0).toNat + 2*(p 1).toNat + (p 2).toNat
  match 8*ci + mi with
  | 0 => #[1, 15, 96, 352, 830, 1330, 1484, 1156, 617, 215, 44, 4]
  | 1 => #[1, 11, 58, 202, 492, 834, 990, 825, 474, 179, 40, 4]
  | 2 => #[1, 11, 60, 214, 526, 900, 1078, 902, 517, 193, 42, 4]
  | 3 => #[1, 7, 28, 93, 245, 465, 623, 585, 376, 157, 38, 4]
  | 4 => #[1, 11, 64, 240, 606, 1050, 1260, 1044, 585, 211, 44, 4]
  | 5 => #[1, 8, 39, 138, 356, 650, 830, 737, 446, 175, 40, 4]
  | 6 => #[1, 7, 32, 118, 327, 639, 861, 791, 485, 189, 42, 4]
  | 7 => #[1, 4, 13, 44, 133, 300, 470, 498, 348, 153, 38, 4]
  | 8 => #[1, 14, 82, 270, 560, 770, 714, 442, 175, 40, 4]
  | 10 => #[1, 10, 50, 164, 362, 538, 540, 362, 155, 38, 4]
  | 12 => #[1, 10, 54, 186, 420, 630, 630, 414, 171, 40, 4]
  | 14 => #[1, 6, 26, 92, 235, 404, 457, 334, 151, 38, 4]
  | 16 => #[1, 13, 69, 201, 359, 411, 303, 139, 36, 4]
  | 20 => #[1, 9, 45, 141, 279, 351, 279, 135, 36, 4]
  | 24 => #[1, 10, 41, 92, 125, 106, 55, 16, 2]
  | 25 => #[1, 7, 24, 55, 81, 75, 43, 14, 2]
  | 28 => #[1, 7, 27, 66, 101, 95, 53, 16, 2]
  | 29 => #[1, 5, 16, 39, 64, 66, 41, 14, 2]
  | 32 => #[1, 11, 48, 112, 155, 131, 66, 18, 2]
  | 33 => #[1, 8, 29, 67, 100, 93, 52, 16, 2]
  | 40 => #[1, 9, 32, 60, 65, 41, 14, 2]
  | 48 => #[1, 8, 24, 36, 29, 12, 2]
  | 50 => #[1, 6, 16, 25, 23, 11, 2]
  | 56 => #[1, 4, 6, 4, 1]
  | 57 | 58 => #[1, 3, 4, 3, 1]
  | 59 => #[1, 2, 2, 2, 1]
  | 64 => #[1, 7, 20, 30, 25, 11, 2]
  | 65 => #[1, 5, 12, 19, 18, 9, 2]
  | 66 => #[1, 5, 13, 21, 20, 10, 2]
  | 67 => #[1, 3, 6, 11, 13, 8, 2]
  | 72 => #[1, 6, 14, 16, 9, 2]
  | 74 => #[1, 4, 9, 12, 8, 2]
  | 80 => #[1, 5, 9, 7, 2]
  | 88 | 96 | 100 => #[1, 3, 3, 1]
  | 89 | 97 | 101 => #[1, 2, 2, 1]
  | 104 | 108 => #[1, 2, 1]
  | 112 | 114 | 116 | 118 => #[1, 1]
  | 120 | 121 | 122 | 123 | 124 | 125 | 126 | 127 => #[1]
  | _ => #[]

private def q (i : ℕ) (c : Col) (m : Mask) : ℤ :=
  ((coefficients c m)[i]?).getD 0
private abbrev Counts := Col → Mask → ℤ

/-- Extend the current prefix by one column. -/
private def step : Counts →ₗ[ℤ] Counts where
  toFun f c m := ∑ d : Col, if colLE c d ∧ ok (upd m c) d then f d (upd m c) else 0
  map_add' f g := by
    funext c m
    simp only [Pi.add_apply, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d _
    split <;> simp
  map_smul' r f := by
    funext c m
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    split <;> simp

/-- Sum over all admissible first columns. -/
private def initial : Counts →ₗ[ℤ] ℤ where
  toFun f := ∑ c : Col, if ok full c then f c full else 0
  map_add' f g := by
    simp only [Pi.add_apply, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d _
    split <;> simp
  map_smul' r f := by
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    split <;> simp
private theorem q_zero : ∀ (c : Col) (m : Mask), q 0 c m = 1 := by decide +kernel

private theorem q_twelve : ∀ (c : Col) (m : Mask), q 12 c m = 0 := by decide +kernel

set_option maxHeartbeats 6000000 in
private theorem step_q (i : ℕ) (hi : i < 12) : step (q i) = q i + q (i+1) := by
  have h : ∀ (j : Fin 12) (c : Col) (m : Mask),
      step (q j.val) c m = q j.val c m + q (j.val+1) c m := by decide +kernel
  funext c m
  exact h ⟨i, hi⟩ c m

private def firstCoefficients : Array ℤ := #[5, 17, 57, 177, 433, 770, 968, 846, 501, 191, 42, 4]

private theorem initial_q (i : ℕ) (hi : i < 12) :
    initial (q i) = (firstCoefficients[i]?).getD 0 := by
  have h : ∀ j : Fin 12, initial (q j.val) = (firstCoefficients[j.val]?).getD 0 := by
    decide +kernel
  exact h ⟨i, hi⟩
private theorem pascal_sum (n k : ℕ) (x : ℕ → ℤ) :
    (∑ i ∈ Finset.range (n+1), (k.choose i : ℤ) * (x i + x (i+1))) =
      (∑ i ∈ Finset.range (n+1), ((k+1).choose i : ℤ) * x i) +
        (k.choose n : ℤ) * x (n+1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ _ (n+1), Finset.sum_range_succ _ (n+1), ih,
      Nat.choose_succ_succ, Nat.cast_add]
    ring

private def poly (k : ℕ) : Counts := ∑ i ∈ Finset.range 12, (k.choose i : ℤ) • q i

private theorem counts_poly (k : ℕ) : (fun c m => F k c (upd m c)) = poly k := by
  induction k with
  | zero =>
    funext c m
    norm_num [F, poly, Finset.sum_range_succ, q_zero]
  | succ k ih =>
    change step (fun c m => F k c (upd m c)) = poly (k+1)
    rw [ih, poly, map_sum]
    simp only [map_smul]
    calc
      _ = ∑ i ∈ Finset.range 12, (k.choose i : ℤ) • (q i + q (i+1)) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [step_q i (Finset.mem_range.mp hi)]
      _ = poly (k+1) := by
        funext c m
        simp only [poly, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.add_apply]
        simpa only [Nat.reduceAdd, q_twelve, mul_zero, add_zero] using pascal_sum 11 k (fun i => q i c m)

theorem total_formula (k : ℕ) : total k =
    5*(k.choose 0 : ℤ) + 17*(k.choose 1 : ℤ) + 57*(k.choose 2 : ℤ) +
    177*(k.choose 3 : ℤ) + 433*(k.choose 4 : ℤ) + 770*(k.choose 5 : ℤ) +
    968*(k.choose 6 : ℤ) + 846*(k.choose 7 : ℤ) + 501*(k.choose 8 : ℤ) +
    191*(k.choose 9 : ℤ) + 42*(k.choose 10 : ℤ) + 4*(k.choose 11 : ℤ) := by
  change initial (fun c m => F k c (upd m c)) = _
  rw [counts_poly, poly, map_sum]
  simp only [map_smul, smul_eq_mul]
  calc
    _ = ∑ i ∈ Finset.range 12, (k.choose i : ℤ) * (firstCoefficients[i]?).getD 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [initial_q i (Finset.mem_range.mp hi)]
    _ = _ := by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero]
      change 0 + _ * 5 + _ * 17 + _ * 57 + _ * 177 + _ * 433 + _ * 770 + _ * 968 +
        _ * 846 + _ * 501 + _ * 191 + _ * 42 + _ * 4 = _
      ring

open OMA.S_oeis_a266430 PowerSeries

private def polynomial (n : ℚ) : ℚ :=
  (1 / 9979200) * n ^ 11 + (1 / 201600) * n ^ 10 + (1 / 12096) * n ^ 9 + (1 / 1344) * n ^ 8
      + (1271 / 302400) * n ^ 7 + (479 / 28800) * n ^ 6 + (12797 / 181440) * n ^ 5
      + (97 / 504) * n ^ 4 + (1779 / 2800) * n ^ 3 + (2032 / 1575) * n ^ 2 + (8269 / 4620) * n + 1

-- A polynomial of degree eleven has vanishing twelfth difference.
set_option maxHeartbeats 3000000 in
private theorem difference (n : ℚ) : polynomial (n + 12) =
    12 * polynomial (n + 11) - 66 * polynomial (n + 10) + 220 * polynomial (n + 9)
      - 495 * polynomial (n + 8) + 792 * polynomial (n + 7) - 924 * polynomial (n + 6)
      + 792 * polynomial (n + 5) - 495 * polynomial (n + 4) + 220 * polynomial (n + 3)
      - 66 * polynomial (n + 2) + 12 * polynomial (n + 1) - polynomial n := by
  unfold polynomial
  ring

set_option maxHeartbeats 3000000 in
private theorem series : mk (fun n : ℕ => polynomial (n+1)) * (1-X)^12 =
    5 - 38 * X + 162 * X ^ 2 - 396 * X ^ 3 + 679 * X ^ 4 - 833 * X ^ 5 + 737 * X ^ 6 - 471 * X ^ 7
      + 213 * X ^ 8 - 65 * X ^ 9 + 12 * X ^ 10 - 1 * X ^ 11 := by
  let A := mk (fun n : ℕ => polynomial (n+1))
  change A * _ = _
  rw [show A * (1-X)^12 = A
      - C 12 * (A * X^1)
      + C 66 * (A * X^2)
      - C 220 * (A * X^3)
      + C 495 * (A * X^4)
      - C 792 * (A * X^5)
      + C 924 * (A * X^6)
      - C 792 * (A * X^7)
      + C 495 * (A * X^8)
      - C 220 * (A * X^9)
      + C 66 * (A * X^10)
      - C 12 * (A * X^11)
      + (A * X^12) by
        simp only [map_ofNat]; ring,
      show (5 - 38 * X + 162 * X ^ 2 - 396 * X ^ 3 + 679 * X ^ 4 - 833 * X ^ 5 + 737 * X ^ 6
      - 471 * X ^ 7 + 213 * X ^ 8 - 65 * X ^ 9 + 12 * X ^ 10 - 1 * X ^ 11 : PowerSeries ℚ) =
        C 5 * (1 : PowerSeries ℚ)
      - C 38 * X^1
      + C 162 * X^2
      - C 396 * X^3
      + C 679 * X^4
      - C 833 * X^5
      + C 737 * X^6
      - C 471 * X^7
      + C 213 * X^8
      - C 65 * X^9
      + C 12 * X^10
      - X^11 by simp only [map_ofNat]; ring]
  ext n
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', coeff_X_pow, coeff_C, coeff_one,
    A, coeff_mk]
  by_cases hn : n ≤ 11
  · interval_cases n <;> norm_num [polynomial]
  · simp (disch := omega) only [if_pos, if_neg, Nat.cast_sub, Nat.cast_ofNat, mul_zero,
      sub_zero, add_zero]
    linear_combination (norm := ring_nf) difference ((n : ℚ) - 11)

theorem solutionOfPolynomial (h : ∀ n : ℕ, 1 ≤ n → (a n : ℚ) = polynomial n) :
    type_of% @OMA.S_oeis_a266430.main := by
  refine ⟨h, ?_, ?_⟩
  · have hseq (n : ℕ) : (a (n+1) : ℚ) = polynomial ((n : ℚ)+1) := by
      simpa using h (n+1) (by omega)
    simpa only [hseq] using series
  · intro n hn
    apply_fun ((↑) : ℤ → ℚ) using Int.cast_injective
    push_cast
    simp (disch := omega) only [h, Nat.cast_sub, Nat.cast_ofNat]
    convert difference ((n : ℚ) - 12) using 1 <;> ring_nf

private def binomialPolynomial (x : ℚ) : ℕ → ℚ
  | 0 => 1
  | k+1 => binomialPolynomial x k * (x-k)/(k+1)

private theorem choose_as_polynomial (n k : ℕ) :
    (n.choose k : ℚ) = binomialPolynomial n k := by
  induction k with
  | zero => simp [binomialPolynomial]
  | succ k ih =>
    rw [binomialPolynomial, ← ih]
    apply (eq_div_iff (by positivity)).mpr
    by_cases h : k ≤ n
    · have eq := congrArg (fun z : ℕ => (z : ℚ)) (Nat.choose_succ_right_eq n k)
      simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_sub h] using eq
    · simp [Nat.choose_eq_zero_of_lt (show n < k by omega),
        Nat.choose_eq_zero_of_lt (show n < k+1 by omega)]

private theorem binomial_to_polynomial (k : ℕ) :
    5*(k.choose 0:ℚ)+17*(k.choose 1:ℚ)+57*(k.choose 2:ℚ)+177*(k.choose 3:ℚ)+
    433*(k.choose 4:ℚ)+770*(k.choose 5:ℚ)+968*(k.choose 6:ℚ)+846*(k.choose 7:ℚ)+
    501*(k.choose 8:ℚ)+191*(k.choose 9:ℚ)+42*(k.choose 10:ℚ)+4*(k.choose 11:ℚ)
      = polynomial (k+1) := by
  simp only [choose_as_polynomial, polynomial]
  norm_num [binomialPolynomial]
  ring

end A266430Proof

open A266430Proof OMA.S_oeis_a266430 in
theorem OMA.solution : type_of% @OMA.S_oeis_a266430.main := by
  apply solutionOfPolynomial
  intro n hn
  obtain ⟨k,rfl⟩ : ∃ k, n=k+1 := ⟨n-1, by omega⟩
  have h := congrArg (fun z : ℤ => (z : ℚ)) ((count_arrays k).trans (total_formula k))
  push_cast at h ⊢
  exact h.trans (binomial_to_polynomial k)
