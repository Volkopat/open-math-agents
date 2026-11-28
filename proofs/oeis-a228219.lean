import OMAStatements.S_oeis_a228219

/-!
OEIS A228219 (R. H. Hardin, Aug 16 2013): Number of second differences of arrays of length 4 of
numbers in 0..n.
Conjectures from Colin Barker, Mar 16 2018: G.f.: x*(15 + 4*x + x^2) / (1 - x)^3.
a(n) = 3*a(n-1) - 3*a(n-2) + a(n-3) for n>3.

Proof. The second differences of x in 0..n are d1 = x0 - 2 x1 + x2 and d2 = x1 - 2 x2 + x3. Every
such pair lies in the octagon |d1| <= 2n, |d2| <= 2n, |d1 + 2 d2| <= 3n, |2 d1 + d2| <= 3n, and
every lattice point of the octagon is reached: x1 is the largest of the lower bounds that
eliminating x2 gives, x2 the largest lower bound given x1, and x0, x3 follow (`img_eq`). The
octagon has 10 n^2 + 4 n + 1 lattice points: its slice at d1 has 3n points plus one when d1 + n is
even for |d1| <= n, and 5n + 1 - 2|d1| points for n < |d1| <= 2n (`card_oct`). The g.f. and the
recurrence follow from the polynomial.
-/

namespace OMA.S_oeis_a228219

open PowerSeries Finset


/-- The octagon that holds the second differences. -/
noncomputable def oct (n : ℕ) : Finset (ℤ × ℤ) :=
  ((Icc (-2 * (n : ℤ)) (2 * n)) ×ˢ (Icc (-2 * (n : ℤ)) (2 * n))).filter
    (fun p => -3 * (n : ℤ) ≤ p.1 + 2 * p.2 ∧ p.1 + 2 * p.2 ≤ 3 * n ∧
      -3 * (n : ℤ) ≤ 2 * p.1 + p.2 ∧ 2 * p.1 + p.2 ≤ 3 * n)

/-- The two second differences as a pair. -/
def pr (v : Fin 2 → ℤ) : ℤ × ℤ := (v 0, v 1)

lemma pr_inj : Function.Injective pr := by
  intro v w h
  simp only [pr, Prod.mk.injEq] at h
  funext i
  fin_cases i
  · exact h.1
  · exact h.2

lemma a_eq (n : ℕ) :
    a n = ((univ : Finset (Fin 4 → Fin (n + 1))).image (fun x => pr (secondDiff x))).card := by
  unfold a
  rw [show (fun x : Fin 4 → Fin (n + 1) => pr (secondDiff x)) = pr ∘ secondDiff from rfl,
    ← Finset.image_image, card_image_of_injective _ pr_inj]

lemma sd {n : ℕ} (x : Fin 4 → Fin (n + 1)) :
    pr (secondDiff x) = ((x 0 : ℤ) - 2 * (x 1 : ℤ) + (x 2 : ℤ), (x 1 : ℤ) - 2 * (x 2 : ℤ) + (x 3 : ℤ)) :=
  rfl

lemma img_eq (n : ℕ) :
    (univ : Finset (Fin 4 → Fin (n + 1))).image (fun x => pr (secondDiff x)) = oct n := by
  ext ⟨d1, d2⟩
  simp only [mem_image, mem_univ, true_and, oct, mem_filter, mem_product, mem_Icc]
  constructor
  · rintro ⟨x, hx⟩
    rw [sd, Prod.mk.injEq] at hx
    have b0 := (x 0).isLt
    have b1 := (x 1).isLt
    have b2 := (x 2).isLt
    have b3 := (x 3).isLt
    omega
  · rintro ⟨⟨⟨h1, h2⟩, h3, h4⟩, h5, h6, h7, h8⟩
    set u : ℤ := max (max (max 0 (-((2 * d1 + d2) / 3))) (-(d1 / 2))) (d2 - n) with hu
    set v : ℤ := max (max 0 (2 * u + d1 - n)) (-((d2 - u) / 2)) with hv
    have hu0 : 0 ≤ u := by omega
    have hun : u ≤ n := by omega
    have hv0 : 0 ≤ v := by omega
    have hvn : v ≤ n := by omega
    have hx00 : 0 ≤ d1 + 2 * u - v := by omega
    have hx0n : d1 + 2 * u - v ≤ n := by omega
    have hx30 : 0 ≤ d2 - u + 2 * v := by omega
    have hx3n : d2 - u + 2 * v ≤ n := by omega
    refine ⟨![⟨(d1 + 2 * u - v).toNat, by omega⟩, ⟨u.toNat, by omega⟩, ⟨v.toNat, by omega⟩,
      ⟨(d2 - u + 2 * v).toNat, by omega⟩], ?_⟩
    rw [sd, Prod.mk.injEq]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Fin.val_mk]
    rw [Int.toNat_of_nonneg hx00, Int.toNat_of_nonneg hu0, Int.toNat_of_nonneg hv0,
      Int.toNat_of_nonneg hx30]
    constructor <;> ring

/-- The size of the slice of the octagon at d1. -/
def W (n : ℕ) (d1 : ℤ) : ℤ :=
  min (min (2 * (n : ℤ)) (3 * n - 2 * d1)) ((3 * n - d1) / 2) + 1 -
    max (max (-2 * (n : ℤ)) (-3 * n - 2 * d1)) (-((3 * n + d1) / 2))

lemma fiber (n : ℕ) (d1 : ℤ) (hd : d1 ∈ Icc (-2 * (n : ℤ)) (2 * n)) :
    (oct n).filter (fun p => p.1 = d1) =
      (Icc (max (max (-2 * (n : ℤ)) (-3 * n - 2 * d1)) (-((3 * n + d1) / 2)))
        (min (min (2 * (n : ℤ)) (3 * n - 2 * d1)) ((3 * n - d1) / 2))).image (fun e => (d1, e)) := by
  rw [mem_Icc] at hd
  ext ⟨p1, p2⟩
  simp only [oct, mem_filter, mem_product, mem_Icc, mem_image, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨⟨⟨h1, h2⟩, h3, h4⟩, h5, h6, h7, h8⟩, rfl⟩
    exact ⟨p2, by omega, rfl, rfl⟩
  · rintro ⟨e, he, rfl, rfl⟩
    omega

lemma card_fiber (n : ℕ) (d1 : ℤ) (hd : d1 ∈ Icc (-2 * (n : ℤ)) (2 * n)) :
    (((oct n).filter (fun p => p.1 = d1)).card : ℤ) = W n d1 := by
  rw [fiber n d1 hd, card_image_of_injective _ (fun e e' h => (Prod.mk.inj h).2), Int.card_Icc]
  rw [mem_Icc] at hd
  unfold W
  rw [Int.toNat_of_nonneg (by omega)]

lemma W_left (n k : ℕ) (hk : k < n) : W n (-2 * n + k) = n + 1 + 2 * k := by
  unfold W
  omega

lemma W_mid (n k : ℕ) (hk1 : n ≤ k) (hk2 : k ≤ 3 * n) :
    W n (-2 * n + k) = 3 * n + if (k - n) % 2 = 0 then 1 else 0 := by
  unfold W
  split_ifs with h <;> omega

lemma W_right (n k : ℕ) (hk1 : 3 * n < k) (hk2 : k ≤ 4 * n) : W n (-2 * n + k) = 9 * n + 1 - 2 * k := by
  unfold W
  omega

lemma parity_count (n : ℕ) :
    ∑ j ∈ range (2 * n + 1), (if j % 2 = 0 then (1 : ℤ) else 0) = n + 1 := by
  induction n with
  | zero => rw [show 2 * 0 + 1 = 1 by rfl, sum_range_one]; simp
  | succ m ih =>
    rw [show 2 * (m + 1) + 1 = 2 * m + 1 + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih]
    rw [if_neg (by omega), if_pos (by omega)]
    push_cast
    ring

lemma card_oct (n : ℕ) : ((oct n).card : ℤ) = 10 * n ^ 2 + 4 * n + 1 := by
  rw [card_eq_sum_card_fiberwise (f := Prod.fst) (t := Icc (-2 * (n : ℤ)) (2 * n))
    (by
      intro p hp
      simp only [oct, coe_filter, mem_product, mem_Icc, Set.mem_setOf_eq] at hp
      simp only [coe_Icc, Set.mem_Icc]
      omega)]
  push_cast
  rw [sum_congr rfl (fun d1 hd => card_fiber n d1 hd)]
  rw [Int.Icc_eq_finset_map, sum_map]
  rw [show (2 * (n : ℤ) + 1 - -2 * n).toNat = 4 * n + 1 by omega]
  simp only [Function.Embedding.trans_apply, Nat.castEmbedding_apply, addLeftEmbedding_apply]
  rw [range_eq_Ico, ← sum_Ico_consecutive _ (Nat.zero_le (3 * n + 1))
      (show 3 * n + 1 ≤ 4 * n + 1 by omega),
    ← sum_Ico_consecutive _ (Nat.zero_le n) (show n ≤ 3 * n + 1 by omega)]
  rw [sum_congr rfl (fun k hk => W_left n k (mem_Ico.mp hk).2),
    sum_congr rfl (fun k hk => W_mid n k (mem_Ico.mp hk).1 (by have := (mem_Ico.mp hk).2; omega)),
    sum_congr rfl (fun k hk => W_right n k (by have := (mem_Ico.mp hk).1; omega)
      (by have := (mem_Ico.mp hk).2; omega))]
  rw [sum_Ico_eq_sum_range, sum_Ico_eq_sum_range, sum_Ico_eq_sum_range]
  simp only [Nat.sub_zero, zero_add, show 3 * n + 1 - n = 2 * n + 1 by omega,
    show 4 * n + 1 - (3 * n + 1) = n by omega]
  have hmid : ∑ j ∈ range (2 * n + 1), ((3 : ℤ) * n + if (n + j - n) % 2 = 0 then 1 else 0) =
      3 * n * (2 * n + 1) + (n + 1) := by
    rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul]
    simp only [Nat.add_sub_cancel_left]
    rw [parity_count]
    push_cast
    ring
  push_cast
  rw [hmid]
  simp only [sum_add_distrib, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, ← mul_sum]
  ring

/-- a(n) as a polynomial in n. -/
lemma a_poly (n : ℕ) : (a n : ℚ) = 10 * (n : ℚ) ^ 2 + 4 * n + 1 := by
  have h : (a n : ℤ) = 10 * n ^ 2 + 4 * n + 1 := by rw [a_eq, img_eq, card_oct]
  exact_mod_cast h

/-- Barker's g.f. -/
theorem gf :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 3 =
      X * (15 + 4 * X + X ^ 2) := by
  set A := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have e1 : A * (1 - X) ^ 3 = A - C (3 : ℚ) * (A * X ^ 1) + C (3 : ℚ) * (A * X ^ 2) - A * X ^ 3 := by
    simp only [map_ofNat]
    ring
  have e2 : (X * (15 + 4 * X + X ^ 2) : ℚ⟦X⟧) = X ^ 1 * C (15 : ℚ) + X ^ 2 * C (4 : ℚ) + X ^ 3 := by
    simp only [map_ofNat]
    ring
  rw [e1, e2]
  ext n
  simp only [map_sub, map_add, coeff_mul_C, coeff_mul_X_pow', coeff_X_pow, hA, coeff_mk,
    coeff_C_mul]
  rcases n with _ | _ | _ | _ | m
  · simp
  · simp only [Nat.reduceAdd, Nat.reduceSub, Nat.reduceLeDiff, Nat.reduceEqDiff, le_refl, if_true,
      if_false, a_poly]
    all_goals norm_num
  · simp only [Nat.reduceAdd, Nat.reduceSub, Nat.reduceLeDiff, Nat.reduceEqDiff, le_refl, if_true,
      if_false, a_poly]
    all_goals norm_num
  · simp only [Nat.reduceAdd, Nat.reduceSub, Nat.reduceLeDiff, Nat.reduceEqDiff, le_refl, if_true,
      if_false, a_poly]
    all_goals norm_num
  · simp only [show ¬ (m + 4 = 0) by omega, show 1 ≤ m + 4 by omega, show m + 4 - 1 = m + 3 by omega,
      show ¬ (m + 3 = 0) by omega, show 2 ≤ m + 4 by omega, show m + 4 - 2 = m + 2 by omega,
      show ¬ (m + 2 = 0) by omega, show 3 ≤ m + 4 by omega, show m + 4 - 3 = m + 1 by omega,
      show ¬ (m + 1 = 0) by omega, show ¬ (m + 4 = 1) by omega, show ¬ (m + 4 = 2) by omega,
      show ¬ (m + 4 = 3) by omega, if_true, if_false]
    rw [a_poly (m + 4), a_poly (m + 3), a_poly (m + 2), a_poly (m + 1)]
    push_cast
    ring

/-- Barker's recurrence. -/
theorem recur : ∀ n : ℕ, 3 < n → (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3) := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  rw [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega,
    show m + 4 - 3 = m + 1 by omega]
  have h : (a (m + 4) : ℚ) = 3 * a (m + 3) - 3 * a (m + 2) + a (m + 1) := by
    rw [a_poly (m + 4), a_poly (m + 3), a_poly (m + 2), a_poly (m + 1)]
    push_cast
    ring
  exact_mod_cast h

/-- Barker's conjectures. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 3 =
      X * (15 + 4 * X + X ^ 2) ∧
    ∀ n : ℕ, 3 < n → (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3) :=
  ⟨gf, recur⟩

end OMA.S_oeis_a228219

theorem OMA.solution : type_of% @OMA.S_oeis_a228219.main :=
  OMA.S_oeis_a228219.conjecture
