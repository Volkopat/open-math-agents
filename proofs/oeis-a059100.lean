import OMAStatements.S_oeis_a059100

namespace OMA.S_oeis_a059100_proof

open OMA.S_oeis_a059100

private structure Mat2 where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ

private def Mat2.one : Mat2 := ⟨1, 0, 0, 1⟩

private def Mat2.step (x : ℕ) : Mat2 := ⟨(x : ℤ), 1, 1, 0⟩

private def Mat2.mul (M N : Mat2) : Mat2 :=
  ⟨M.a * N.a + M.b * N.c, M.a * N.b + M.b * N.d,
   M.c * N.a + M.d * N.c, M.c * N.b + M.d * N.d⟩

private def Mat2.transpose (M : Mat2) : Mat2 := ⟨M.a, M.c, M.b, M.d⟩

private def Mat2.det (M : Mat2) : ℤ := M.a * M.d - M.b * M.c

private lemma Mat2.one_mul (M : Mat2) : Mat2.mul Mat2.one M = M := by
  cases M; simp [Mat2.mul, Mat2.one]

private lemma Mat2.mul_one (M : Mat2) : Mat2.mul M Mat2.one = M := by
  cases M; simp [Mat2.mul, Mat2.one]

private lemma Mat2.mul_assoc (A B C : Mat2) :
    Mat2.mul (Mat2.mul A B) C = Mat2.mul A (Mat2.mul B C) := by
  cases A; cases B; cases C
  simp only [Mat2.mul, Mat2.mk.injEq]
  exact ⟨by ring, by ring, by ring, by ring⟩

private lemma Mat2.transpose_mul (A B : Mat2) :
    (Mat2.mul A B).transpose = Mat2.mul B.transpose A.transpose := by
  cases A; cases B
  simp only [Mat2.mul, Mat2.transpose, Mat2.mk.injEq]
  exact ⟨by ring, by ring, by ring, by ring⟩

private lemma Mat2.transpose_one : Mat2.one.transpose = Mat2.one := rfl

private lemma Mat2.transpose_step (x : ℕ) : (Mat2.step x).transpose = Mat2.step x := rfl

private lemma Mat2.det_mul (A B : Mat2) : (Mat2.mul A B).det = A.det * B.det := by
  cases A; cases B; simp only [Mat2.mul, Mat2.det]; ring

private lemma Mat2.det_one : Mat2.one.det = 1 := by simp [Mat2.one, Mat2.det]

private lemma Mat2.det_step (x : ℕ) : (Mat2.step x).det = -1 := by
  simp [Mat2.step, Mat2.det]

private def matProd : List ℕ → Mat2
  | [] => Mat2.one
  | x :: xs => Mat2.mul (Mat2.step x) (matProd xs)

private lemma matProd_append (xs ys : List ℕ) :
    matProd (xs ++ ys) = Mat2.mul (matProd xs) (matProd ys) := by
  induction xs with
  | nil => simp [matProd, Mat2.one_mul]
  | cons x xs ih => simp [matProd, ih, Mat2.mul_assoc]

private lemma matProd_reverse (xs : List ℕ) :
    matProd xs.reverse = (matProd xs).transpose := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp [List.reverse_cons, matProd_append, matProd, ih, Mat2.mul_one,
      Mat2.transpose_mul, Mat2.transpose_step]

private lemma det_matProd (xs : List ℕ) : (matProd xs).det = (-1 : ℤ) ^ xs.length := by
  induction xs with
  | nil => simp [matProd, Mat2.det_one]
  | cons x xs ih =>
    simp [matProd, Mat2.det_mul, Mat2.det_step, ih, pow_succ']

private lemma matProd_nonneg (xs : List ℕ) :
    0 ≤ (matProd xs).a ∧ 0 ≤ (matProd xs).b ∧ 0 ≤ (matProd xs).c ∧ 0 ≤ (matProd xs).d := by
  induction xs with
  | nil => simp [matProd, Mat2.one]
  | cons x xs ih =>
    rcases ih with ⟨ha, hb, hc, hd⟩
    simp only [matProd, Mat2.mul, Mat2.step, one_mul, zero_mul, add_zero]
    exact ⟨by positivity, by positivity, ha, hb⟩

private lemma matProd_pos_a (xs : List ℕ) (h : ∀ d ∈ xs, 1 ≤ d) : 0 < (matProd xs).a := by
  induction xs with
  | nil => simp [matProd, Mat2.one]
  | cons x xs ih =>
    have hx : (1 : ℤ) ≤ (x : ℤ) := by exact_mod_cast h x (by simp)
    have ha : 0 < (matProd xs).a := ih fun d hd => h d (by simp [hd])
    have hc : 0 ≤ (matProd xs).c := (matProd_nonneg xs).2.2.1
    simp only [matProd, Mat2.mul, Mat2.step, one_mul]
    nlinarith

private lemma folding_identity (U : Mat2) (a : ℕ) (ha : 1 ≤ a) (hdet : U.det = -1) :
    let M := Mat2.mul U (Mat2.step a)
    let M' := Mat2.mul (Mat2.mul (Mat2.mul U (Mat2.step (a + 1))) (Mat2.step (a - 1))) U.transpose
    M'.a = M.a ^ 2 ∧ M'.c = M.c * M.a + 1 := by
  cases U with
  | mk r s t u =>
    have hsub : ((a - 1 : ℕ) : ℤ) = (a : ℤ) - 1 := by omega
    have hadd : ((a + 1 : ℕ) : ℤ) = (a : ℤ) + 1 := by push_cast; ring
    simp only [Mat2.det] at hdet
    simp only [Mat2.mul, Mat2.step, Mat2.transpose, hsub, hadd]
    constructor
    · ring
    · linear_combination -hdet

private def shallitList (m : ℕ) : ℕ → List ℕ
  | 0 => [m - 1, m + 1]
  | k + 1 =>
    let l := shallitList m k
    let u := l.dropLast
    let a := l.getLastD 0
    u ++ [a + 1, a - 1] ++ u.reverse

private lemma getLastD_cons_of_ne_nil (x : ℕ) (xs : List ℕ) (h : xs ≠ []) (d : ℕ) :
    (x :: xs).getLastD d = xs.getLastD d := by
  cases xs with
  | nil => exact absurd rfl h
  | cons y ys => simp

private lemma dropLast_append_getLastD (l : List ℕ) (hne : l ≠ []) :
    l.dropLast ++ [l.getLastD 0] = l := by
  induction l with
  | nil => exact absurd rfl hne
  | cons x xs ih =>
    cases xs with
    | nil => rfl
    | cons y ys =>
      have hsub := ih (List.cons_ne_nil y ys)
      rw [List.dropLast_cons_of_ne_nil (List.cons_ne_nil y ys),
        getLastD_cons_of_ne_nil x (y :: ys) (List.cons_ne_nil y ys) 0, List.cons_append]
      exact congrArg (x :: ·) hsub

private lemma shallitList_length (m k : ℕ) : (shallitList m k).length = 2 ^ (k + 1) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [shallitList, List.length_append, List.length_reverse, List.length_dropLast,
      List.length_cons, List.length_nil, ih]
    have hpos : 1 ≤ 2 ^ (k + 1) := Nat.one_le_pow _ _ (by omega)
    rw [pow_succ']
    omega

private lemma shallitList_ne_nil (m k : ℕ) : shallitList m k ≠ [] := by
  intro h
  have hlen := shallitList_length m k
  rw [h, List.length_nil] at hlen
  have hpos : 0 < 2 ^ (k + 1) := pow_pos (by omega) _
  omega

private lemma shallitList_headD (m k : ℕ) : (shallitList m k).headD 0 = m - 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hlen : 2 ≤ (shallitList m k).length := by
      rw [shallitList_length]
      have h1 : 1 ≤ 2 ^ k := Nat.one_le_pow _ _ (by omega)
      rw [pow_succ']
      omega
    have hu_ne : (shallitList m k).dropLast ≠ [] := by
      intro h
      have := congrArg List.length h
      rw [List.length_dropLast, List.length_nil] at this
      omega
    have hhead_drop : (shallitList m k).dropLast.headD 0 = (shallitList m k).headD 0 := by
      cases hl : shallitList m k with
      | nil => exact absurd hl (shallitList_ne_nil m k)
      | cons x xs =>
        cases xs with
        | nil => rw [hl] at hlen; simp at hlen
        | cons y ys =>
          simp [List.dropLast_cons_of_ne_nil (List.cons_ne_nil y ys)]
    simp only [shallitList, List.append_assoc]
    cases hu : (shallitList m k).dropLast with
    | nil => exact absurd hu hu_ne
    | cons x xs =>
      rw [List.cons_append, List.headD_cons]
      have hx : x = (shallitList m k).dropLast.headD 0 := by rw [hu]; rfl
      rw [hx, hhead_drop, ih]

private lemma getLastD_append_of_ne_nil (xs ys : List ℕ) (hy : ys ≠ []) :
    (xs ++ ys).getLastD 0 = ys.getLastD 0 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [List.cons_append, getLastD_cons_of_ne_nil _ _ (by simp [hy]), ih]

private lemma getLastD_reverse (l : List ℕ) : l.reverse.getLastD 0 = l.headD 0 := by
  cases l with
  | nil => rfl
  | cons x xs =>
    rw [List.reverse_cons, getLastD_append_of_ne_nil _ _ (List.cons_ne_nil x [])]
    rfl

private lemma shallitList_getLastD_succ (m k : ℕ) :
    (shallitList m (k + 1)).getLastD 0 = m - 1 := by
  have hlen : 2 ≤ (shallitList m k).length := by
    rw [shallitList_length]
    have h1 : 1 ≤ 2 ^ k := Nat.one_le_pow _ _ (by omega)
    rw [pow_succ']
    omega
  have hu_ne : (shallitList m k).dropLast ≠ [] := by
    intro h
    have := congrArg List.length h
    rw [List.length_dropLast, List.length_nil] at this
    omega
  have hrev_ne : (shallitList m k).dropLast.reverse ≠ [] := by
    simpa using hu_ne
  simp only [shallitList]
  rw [getLastD_append_of_ne_nil _ _ hrev_ne, getLastD_reverse]
  have hhead_drop : (shallitList m k).dropLast.headD 0 = (shallitList m k).headD 0 := by
    cases hl : shallitList m k with
    | nil => exact absurd hl (shallitList_ne_nil m k)
    | cons x xs =>
      cases xs with
      | nil => rw [hl] at hlen; simp at hlen
      | cons y ys =>
        simp [List.dropLast_cons_of_ne_nil (List.cons_ne_nil y ys)]
  rw [hhead_drop, shallitList_headD]

private lemma shallitList_getLastD_ge (m k : ℕ) : m - 1 ≤ (shallitList m k).getLastD 0 := by
  cases k with
  | zero => simp [shallitList]; omega
  | succ k => rw [shallitList_getLastD_succ]

private lemma shallitList_mem_bounds (m : ℕ) (hm : 4 ≤ m) (k : ℕ) :
    ∀ d ∈ shallitList m k, m - 2 ≤ d ∧ d ≤ m + 2 := by
  induction k with
  | zero =>
    intro d hd
    simp only [shallitList, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl <;> omega
  | succ k ih =>
    intro d hd
    simp only [shallitList, List.mem_append, List.mem_reverse, List.mem_cons,
      List.not_mem_nil, or_false] at hd
    have hdrop : ∀ x ∈ (shallitList m k).dropLast, x ∈ shallitList m k :=
      fun x hx => List.dropLast_subset _ hx
    have ha_cases :
        (shallitList m k).getLastD 0 = m + 1 ∨ (shallitList m k).getLastD 0 = m - 1 := by
      cases k with
      | zero => left; rfl
      | succ k' => right; exact shallitList_getLastD_succ m k'
    rcases hd with (hx | (rfl | rfl)) | hx
    · exact ih d (hdrop d hx)
    · rcases ha_cases with h | h <;> rw [h] <;> omega
    · rcases ha_cases with h | h <;> rw [h] <;> omega
    · exact ih d (hdrop d hx)

private lemma shallitList_one_eq (m : ℕ) :
    shallitList m 1 = [m - 1, m + 2, m, m - 1] := by
  have hlast : (shallitList m 0).getLastD 0 = m + 1 := rfl
  have hdrop : (shallitList m 0).dropLast = [m - 1] := rfl
  change (shallitList m 0).dropLast ++
      [(shallitList m 0).getLastD 0 + 1, (shallitList m 0).getLastD 0 - 1] ++
      (shallitList m 0).dropLast.reverse = _
  rw [hdrop, hlast]
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
  rw [show m + 1 - 1 = m by omega]

private lemma matProd_shallitList (m : ℕ) (hm : 4 ≤ m) (k : ℕ) :
    (matProd (shallitList m k)).a = (m : ℤ) ^ (2 ^ (k + 1)) ∧
      ((matProd (shallitList m k)).c : ℝ) / ((matProd (shallitList m k)).a : ℝ) =
        ∑ r ∈ Finset.range (k + 2), (1 : ℝ) / (m : ℝ) ^ (2 ^ r) := by
  induction k with
  | zero =>
    have hm1 : ((m - 1 : ℕ) : ℤ) = (m : ℤ) - 1 := by omega
    have hm2 : ((m + 1 : ℕ) : ℤ) = (m : ℤ) + 1 := by push_cast; ring
    have ha : (matProd (shallitList m 0)).a = (m : ℤ) ^ 2 := by
      simp only [shallitList, matProd, Mat2.mul, Mat2.step, Mat2.one, hm1, hm2]
      ring
    have hc : (matProd (shallitList m 0)).c = (m : ℤ) + 1 := by
      simp only [shallitList, matProd, Mat2.mul, Mat2.step, Mat2.one, hm1, hm2]
      ring
    refine ⟨ha, ?_⟩
    rw [ha, hc]
    have hm_ne : (m : ℝ) ≠ 0 := by positivity
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one]
    push_cast
    field_simp [hm_ne]
  | succ k ih =>
    rcases ih with ⟨ha_k, hsum_k⟩
    set l := shallitList m k
    set u := l.dropLast
    set a := l.getLastD 0
    have hl_eq : u ++ [a] = l := dropLast_append_getLastD l (shallitList_ne_nil m k)
    have hu_len : u.length = 2 ^ (k + 1) - 1 := by
      simp only [u, l, List.length_dropLast, shallitList_length]
    have hdet_u : (matProd u).det = -1 := by
      rw [det_matProd, hu_len]
      have heven : Even (2 ^ (k + 1)) := by
        rw [pow_succ']
        exact even_two_mul _
      have hpos : 1 ≤ 2 ^ (k + 1) := Nat.one_le_pow _ _ (by omega)
      rcases heven with ⟨t, ht⟩
      have hodd : Odd (2 ^ (k + 1) - 1) := ⟨t - 1, by omega⟩
      exact hodd.neg_one_pow
    have ha_ge1 : 1 ≤ a := by
      have : m - 1 ≤ a := shallitList_getLastD_ge m k
      omega
    have hM_eq : matProd l = Mat2.mul (matProd u) (Mat2.step a) := by
      rw [← hl_eq, matProd_append]
      simp [matProd, Mat2.mul_one]
    have hM'_eq :
        matProd (shallitList m (k + 1)) =
          Mat2.mul (Mat2.mul (Mat2.mul (matProd u) (Mat2.step (a + 1))) (Mat2.step (a - 1)))
            (matProd u).transpose := by
      change matProd (u ++ [a + 1, a - 1] ++ u.reverse) = _
      rw [matProd_append, matProd_append, matProd_reverse]
      simp only [matProd, Mat2.mul_one, Mat2.mul_assoc]
    have hfold := folding_identity (matProd u) a ha_ge1 hdet_u
    rw [← hM_eq, ← hM'_eq] at hfold
    rcases hfold with ⟨ha_next, hc_next⟩
    have ha_final : (matProd (shallitList m (k + 1))).a = (m : ℤ) ^ (2 ^ (k + 2)) := by
      rw [ha_next, ha_k, ← pow_mul, ← pow_succ]
    refine ⟨ha_final, ?_⟩
    rw [hc_next, ha_next, Finset.sum_range_succ, ← hsum_k]
    have hqk_ne : ((matProd l).a : ℝ) ≠ 0 := by
      rw [ha_k]
      exact_mod_cast (pow_ne_zero _ (by omega : (m : ℤ) ≠ 0))
    have hqk_sq : (((matProd l).a : ℝ) ^ 2) = (m : ℝ) ^ (2 ^ (k + 2)) := by
      have h1 : ((matProd l).a : ℝ) = (m : ℝ) ^ (2 ^ (k + 1)) := by exact_mod_cast ha_k
      rw [h1, ← pow_mul, ← pow_succ]
    push_cast
    rw [sq, add_div, mul_div_mul_right _ _ hqk_ne, ← sq, hqk_sq]

private noncomputable def cfEval : List ℕ → ℝ → ℝ
  | [], t => t
  | a :: ds, t => 1 / ((a : ℝ) + cfEval ds t)

private lemma cfEval_bounds (ds : List ℕ) (t : ℝ)
    (hds : ∀ d ∈ ds, 1 ≤ d) (ht0 : 0 < t) (ht1 : t < 1) :
    0 < cfEval ds t ∧ cfEval ds t < 1 := by
  induction ds with
  | nil => exact ⟨ht0, ht1⟩
  | cons a ds ih =>
    have ha : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast hds a (by simp)
    rcases ih (fun d hd => hds d (by simp [hd])) with ⟨h0, _⟩
    have hden : (1 : ℝ) < (a : ℝ) + cfEval ds t := by linarith
    simp only [cfEval]
    refine ⟨by positivity, ?_⟩
    exact (div_lt_one (by linarith)).mpr hden

private lemma cfEval_eq_matProd (ds : List ℕ) (t : ℝ)
    (hds : ∀ d ∈ ds, 1 ≤ d) (ht0 : 0 < t) :
    cfEval ds t =
      (((matProd ds).c : ℝ) + ((matProd ds).d : ℝ) * t) /
        (((matProd ds).a : ℝ) + ((matProd ds).b : ℝ) * t) := by
  induction ds with
  | nil => simp [cfEval, matProd, Mat2.one]
  | cons a ds ih =>
    have hds' : ∀ d ∈ ds, 1 ≤ d := fun d hd => hds d (by simp [hd])
    have ih' := ih hds'
    have hNa : (0 : ℝ) < ((matProd ds).a : ℝ) := by exact_mod_cast matProd_pos_a ds hds'
    have hNb : (0 : ℝ) ≤ ((matProd ds).b : ℝ) := by exact_mod_cast (matProd_nonneg ds).2.1
    have hNc : (0 : ℝ) ≤ ((matProd ds).c : ℝ) := by exact_mod_cast (matProd_nonneg ds).2.2.1
    have hNd : (0 : ℝ) ≤ ((matProd ds).d : ℝ) := by exact_mod_cast (matProd_nonneg ds).2.2.2
    have hden_pos : (0 : ℝ) < ((matProd ds).a : ℝ) + ((matProd ds).b : ℝ) * t := by nlinarith
    have ha_pos : (0 : ℝ) < (a : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (by have := hds a (by simp); omega)
    have hden2_pos :
        (0 : ℝ) <
          ((a : ℝ) * ((matProd ds).a : ℝ) + ((matProd ds).c : ℝ)) +
            ((a : ℝ) * ((matProd ds).b : ℝ) + ((matProd ds).d : ℝ)) * t := by nlinarith
    simp only [cfEval, matProd, Mat2.mul, Mat2.step, one_mul, zero_mul, add_zero, ih']
    push_cast
    field_simp [ne_of_gt hden_pos, ne_of_gt hden2_pos]
    ring

private lemma of_s_get?_int_add (a : ℤ) (y : ℝ) (hy0 : 0 < y) (hy1 : y < 1) (k : ℕ) :
    (GenContFract.of ((a : ℝ) + y)).s.get? k = (GenContFract.of y).s.get? k := by
  have hf1 : Int.fract ((a : ℝ) + y) = y := by
    rw [Int.fract_intCast_add, Int.fract_eq_self.mpr ⟨le_of_lt hy0, hy1⟩]
  have hf2 : Int.fract y = y := Int.fract_eq_self.mpr ⟨le_of_lt hy0, hy1⟩
  have hy_ne : y ≠ 0 := ne_of_gt hy0
  cases k with
  | zero =>
    change (GenContFract.of ((a : ℝ) + y)).s.head = (GenContFract.of y).s.head
    rw [GenContFract.of_s_head (by rw [hf1]; exact hy_ne),
      GenContFract.of_s_head (by rw [hf2]; exact hy_ne), hf1, hf2]
  | succ k =>
    rw [GenContFract.of_s_succ, GenContFract.of_s_succ, hf1, hf2]

private lemma of_s_get?_cfEval (ds : List ℕ) (t : ℝ)
    (hds : ∀ d ∈ ds, 1 ≤ d) (ht0 : 0 < t) (ht1 : t < 1) :
    ∀ i (hi : i < ds.length),
      (GenContFract.of (cfEval ds t)).s.get? i = some ⟨1, (ds[i] : ℝ)⟩ := by
  induction ds with
  | nil => intro i hi; simp at hi
  | cons a ds ih =>
    intro i hi
    have hds' : ∀ d ∈ ds, 1 ≤ d := fun d hd => hds d (by simp [hd])
    rcases cfEval_bounds ds t hds' ht0 ht1 with ⟨hy0, hy1⟩
    rcases cfEval_bounds (a :: ds) t hds ht0 ht1 with ⟨hv0, hv1⟩
    have hfv : Int.fract (cfEval (a :: ds) t) = cfEval (a :: ds) t :=
      Int.fract_eq_self.mpr ⟨le_of_lt hv0, hv1⟩
    have hfv_ne : Int.fract (cfEval (a :: ds) t) ≠ 0 := by rw [hfv]; exact ne_of_gt hv0
    have hinv : (Int.fract (cfEval (a :: ds) t))⁻¹ = ((a : ℤ) : ℝ) + cfEval ds t := by
      rw [hfv]
      simp only [cfEval, one_div, inv_inv, Int.cast_natCast]
    cases i with
    | zero =>
      change (GenContFract.of (cfEval (a :: ds) t)).s.head = some ⟨1, (a : ℝ)⟩
      rw [GenContFract.of_s_head hfv_ne, hinv]
      have hfl : ⌊((a : ℤ) : ℝ) + cfEval ds t⌋ = (a : ℤ) :=
        Int.floor_eq_iff.mpr ⟨by linarith, by linarith⟩
      rw [hfl]
      simp
    | succ k =>
      rw [GenContFract.of_s_succ, hinv, of_s_get?_int_add (a : ℤ) (cfEval ds t) hy0 hy1 k]
      have hk : k < ds.length := by simpa using hi
      simpa using ih hds' k hk

private lemma pow_two_add_le (j r : ℕ) : 2 ^ j + r ≤ 2 ^ (r + j) := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hpos : 1 ≤ 2 ^ j := Nat.one_le_pow _ _ (by omega)
    rw [show r + 1 + j = (r + j) + 1 by omega, pow_succ']
    omega

private lemma s_eq_tsum_m (n : ℕ) :
    s n = ∑' k : ℕ, (1 : ℝ) / ((n ^ 2 : ℕ) : ℝ) ^ (2 ^ k) := by
  unfold s
  congr 1
  ext k
  push_cast
  rw [pow_succ', pow_mul]

private lemma summable_shallit (m : ℕ) (hm : 4 ≤ m) :
    Summable fun k : ℕ => (1 : ℝ) / (m : ℝ) ^ (2 ^ k) := by
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : 1 ≤ m)
  have hgeom : Summable fun k : ℕ => ((m : ℝ)⁻¹) ^ k :=
    summable_geometric_of_lt_one (by positivity)
      (inv_lt_one_of_one_lt₀ (by exact_mod_cast (by omega : 1 < m)))
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) hgeom
  rw [one_div, inv_pow]
  have hk_le : k ≤ 2 ^ k := Nat.le_of_lt (Nat.lt_two_pow_self)
  have hpow : (m : ℝ) ^ k ≤ (m : ℝ) ^ (2 ^ k) := pow_le_pow_right₀ hm1 hk_le
  exact inv_anti₀ (by positivity) hpow

private lemma shallit_tail_bounds (m : ℕ) (hm : 4 ≤ m) (j : ℕ) :
    let eps := (∑' k : ℕ, (1 : ℝ) / (m : ℝ) ^ (2 ^ k)) -
      ∑ k ∈ Finset.range j, (1 : ℝ) / (m : ℝ) ^ (2 ^ k)
    0 < eps ∧ eps < 2 / (m : ℝ) ^ (2 ^ j) := by
  intro eps
  have hsum := summable_shallit m hm
  have hsplit := hsum.sum_add_tsum_nat_add j
  have heps : eps = ∑' r : ℕ, (1 : ℝ) / (m : ℝ) ^ (2 ^ (r + j)) := by
    dsimp only [eps]
    linarith [hsplit]
  have hsum_shift : Summable fun r : ℕ => (1 : ℝ) / (m : ℝ) ^ (2 ^ (r + j)) :=
    (summable_nat_add_iff j).mpr hsum
  have hm_pos : (0 : ℝ) < (m : ℝ) := by positivity
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : 1 ≤ m)
  have hpos : 0 < eps := by
    rw [heps]
    have h0 : (0 : ℝ) < (1 : ℝ) / (m : ℝ) ^ (2 ^ (0 + j)) := by positivity
    have hle := hsum_shift.le_tsum 0 (fun r _ => by positivity)
    linarith
  have hlt : eps < 2 / (m : ℝ) ^ (2 ^ j) := by
    rw [heps]
    have hgeom : Summable fun r : ℕ => ((m : ℝ)⁻¹) ^ r :=
      summable_geometric_of_lt_one (by positivity)
        (inv_lt_one_of_one_lt₀ (by exact_mod_cast (by omega : 1 < m)))
    have hdom : Summable fun r : ℕ => ((1 : ℝ) / (m : ℝ) ^ (2 ^ j)) * ((m : ℝ)⁻¹) ^ r :=
      hgeom.mul_left _
    have hle :
        (∑' r : ℕ, (1 : ℝ) / (m : ℝ) ^ (2 ^ (r + j))) ≤
          ∑' r : ℕ, ((1 : ℝ) / (m : ℝ) ^ (2 ^ j)) * ((m : ℝ)⁻¹) ^ r := by
      refine hsum_shift.tsum_le_tsum (fun r => ?_) hdom
      have hexp : (m : ℝ) ^ (2 ^ j + r) ≤ (m : ℝ) ^ (2 ^ (r + j)) :=
        pow_le_pow_right₀ hm1 (pow_two_add_le j r)
      have hinv : (1 : ℝ) / (m : ℝ) ^ (2 ^ (r + j)) ≤ (1 : ℝ) / (m : ℝ) ^ (2 ^ j + r) := by
        rw [one_div, one_div]
        exact inv_anti₀ (by positivity) hexp
      refine le_trans hinv (le_of_eq ?_)
      rw [pow_add, one_div, mul_inv, one_div, inv_pow]
    rw [tsum_mul_left, tsum_geometric_of_lt_one (by positivity)
      (inv_lt_one_of_one_lt₀ (by exact_mod_cast (by omega : 1 < m)))] at hle
    have hgeo_lt : (1 - (m : ℝ)⁻¹)⁻¹ < 2 := by
      have hm4 : (4 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      have h1 : (1 / 2 : ℝ) < 1 - (m : ℝ)⁻¹ := by
        have hinv4 : (m : ℝ)⁻¹ ≤ 1 / 4 := by
          rw [one_div]
          exact inv_anti₀ (by positivity) hm4
        linarith
      have h2 := inv_strictAnti₀ (by positivity) h1
      simpa using h2
    have hq_pos : (0 : ℝ) < 1 / (m : ℝ) ^ (2 ^ j) := by positivity
    have hmul : (1 / (m : ℝ) ^ (2 ^ j)) * (1 - (m : ℝ)⁻¹)⁻¹ < (1 / (m : ℝ) ^ (2 ^ j)) * 2 :=
      mul_lt_mul_of_pos_left hgeo_lt hq_pos
    linarith [hle, hmul, show (1 / (m : ℝ) ^ (2 ^ j)) * 2 = 2 / (m : ℝ) ^ (2 ^ j) by ring]
  exact ⟨hpos, hlt⟩

private lemma partDens_of_s_eq (n : ℕ) (hn : 2 ≤ n) (k i : ℕ)
    (hi : i < (shallitList (n ^ 2) k).dropLast.length) :
    (GenContFract.of (s n)).partDens.get? i =
      some (((shallitList (n ^ 2) k).dropLast[i] : ℕ) : ℝ) := by
  set m := n ^ 2
  have hm : 4 ≤ m := by dsimp only [m]; nlinarith
  set l := shallitList m k
  set u := l.dropLast
  set a := l.getLastD 0
  have hl_eq : u ++ [a] = l := dropLast_append_getLastD l (shallitList_ne_nil m k)
  set M := matProd u
  have hM_l : matProd l = Mat2.mul M (Mat2.step a) := by
    rw [← hl_eq, matProd_append]
    simp [matProd, Mat2.mul_one, M]
  have hdet_u : M.det = -1 := by
    rw [det_matProd, show u.length = 2 ^ (k + 1) - 1 by simp [u, l, shallitList_length]]
    have heven : Even (2 ^ (k + 1)) := by rw [pow_succ']; exact even_two_mul _
    have hpos : 1 ≤ 2 ^ (k + 1) := Nat.one_le_pow _ _ (by omega)
    rcases heven with ⟨r, hr⟩
    exact (show Odd (2 ^ (k + 1) - 1) from ⟨r - 1, by omega⟩).neg_one_pow
  rcases matProd_shallitList m hm k with ⟨hq_eq, hsum_eq⟩
  set q : ℝ := ((matProd l).a : ℝ)
  set p : ℝ := ((matProd l).c : ℝ)
  have hq_val : q = (m : ℝ) ^ (2 ^ (k + 1)) := by dsimp only [q, l]; exact_mod_cast hq_eq
  have hq_pos : 0 < q := by rw [hq_val]; positivity
  have hq_def : q = (M.a : ℝ) * (a : ℝ) + (M.b : ℝ) := by
    have : (matProd l).a = M.a * (a : ℤ) + M.b := by
      simp [hM_l, Mat2.mul, Mat2.step]
    dsimp only [q]
    exact_mod_cast this
  have hp_def : p = (M.c : ℝ) * (a : ℝ) + (M.d : ℝ) := by
    have : (matProd l).c = M.c * (a : ℤ) + M.d := by
      simp [hM_l, Mat2.mul, Mat2.step]
    dsimp only [p]
    exact_mod_cast this
  have hdet_r : (M.a : ℝ) * (M.d : ℝ) - (M.b : ℝ) * (M.c : ℝ) = -1 := by
    exact_mod_cast hdet_u
  have hu_ge1 : ∀ d ∈ u, 1 ≤ d := fun d hd => by
    have hbd := shallitList_mem_bounds m hm k d (List.dropLast_subset _ hd)
    omega
  have hMa_pos : (0 : ℝ) < (M.a : ℝ) := by exact_mod_cast matProd_pos_a u hu_ge1
  have hMb_nonneg : (0 : ℝ) ≤ (M.b : ℝ) := by exact_mod_cast (matProd_nonneg u).2.1
  have ha_ge3 : (3 : ℝ) ≤ (a : ℝ) := by
    have : m - 1 ≤ a := shallitList_getLastD_ge m k
    exact_mod_cast (by omega : 3 ≤ a)
  set eps := s n - p / q
  have heps_bounds : 0 < eps ∧ eps < 2 / q ^ 2 := by
    have htb := shallit_tail_bounds m hm (k + 2)
    have hsn : s n = ∑' r : ℕ, (1 : ℝ) / (m : ℝ) ^ (2 ^ r) := s_eq_tsum_m n
    have hq2 : q ^ 2 = (m : ℝ) ^ (2 ^ (k + 2)) := by
      rw [hq_val, ← pow_mul, ← pow_succ]
    have heq : eps = (∑' r : ℕ, (1 : ℝ) / (m : ℝ) ^ (2 ^ r)) -
        ∑ r ∈ Finset.range (k + 2), (1 : ℝ) / (m : ℝ) ^ (2 ^ r) := by
      dsimp only [eps]
      rw [hsn, hsum_eq]
    rw [heq, hq2]
    exact htb
  rcases heps_bounds with ⟨heps_pos, heps_lt⟩
  set N : ℝ := (M.c : ℝ) - (M.a : ℝ) * s n
  set D : ℝ := (M.b : ℝ) * s n - (M.d : ℝ)
  have hN_eq : N = 1 / q - (M.a : ℝ) * eps := by
    have h1 : (M.c : ℝ) * q - (M.a : ℝ) * p = 1 := by
      rw [hq_def, hp_def]
      linear_combination -hdet_r
    have h2 : s n = p / q + eps := by dsimp only [eps]; ring
    dsimp only [N]
    rw [h2]
    field_simp [ne_of_gt hq_pos]
    linear_combination h1
  have hD_eq : D = (a : ℝ) / q + (M.b : ℝ) * eps := by
    have h1 : (M.b : ℝ) * p - (M.d : ℝ) * q = (a : ℝ) := by
      rw [hq_def, hp_def]
      linear_combination -(a : ℝ) * hdet_r
    have h2 : s n = p / q + eps := by dsimp only [eps]; ring
    dsimp only [D]
    rw [h2]
    field_simp [ne_of_gt hq_pos]
    linear_combination h1
  have hMa_le : 3 * (M.a : ℝ) ≤ q := by nlinarith
  have hN_pos : 0 < N := by
    rw [hN_eq]
    have h1 : (M.a : ℝ) * eps < (q / 3) * (2 / q ^ 2) := by
      have hmul1 : (M.a : ℝ) * eps < (M.a : ℝ) * (2 / q ^ 2) :=
        mul_lt_mul_of_pos_left heps_lt hMa_pos
      have hmul2 : (M.a : ℝ) * (2 / q ^ 2) ≤ (q / 3) * (2 / q ^ 2) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      linarith
    have h2 : (q / 3) * (2 / q ^ 2) = 2 / (3 * q) := by
      field_simp [ne_of_gt hq_pos]
    have h3 : 2 / (3 * q) < 1 / q := by
      rw [div_lt_div_iff₀ (by positivity) hq_pos]
      linarith
    linarith
  have hN_lt_D : N < D := by
    rw [hN_eq, hD_eq]
    have h1 : 1 / q < (a : ℝ) / q := by
      rw [div_lt_div_iff₀ hq_pos hq_pos]
      nlinarith
    have h2 : 0 < (M.a : ℝ) * eps := mul_pos hMa_pos heps_pos
    have h3 : 0 ≤ (M.b : ℝ) * eps := mul_nonneg hMb_nonneg (le_of_lt heps_pos)
    linarith
  have hD_pos : 0 < D := lt_trans hN_pos hN_lt_D
  set t : ℝ := N / D
  have ht0 : 0 < t := div_pos hN_pos hD_pos
  have ht1 : t < 1 := (div_lt_one hD_pos).mpr hN_lt_D
  have hsn_cf : cfEval u t = s n := by
    rw [cfEval_eq_matProd u t hu_ge1 ht0]
    change (((M.c : ℝ) + (M.d : ℝ) * t) / ((M.a : ℝ) + (M.b : ℝ) * t)) = s n
    have hden_pos : (0 : ℝ) < (M.a : ℝ) + (M.b : ℝ) * t := by nlinarith
    rw [div_eq_iff (ne_of_gt hden_pos)]
    have htD : t * D = N := div_mul_cancel₀ N (ne_of_gt hD_pos)
    apply mul_right_cancel₀ (ne_of_gt hD_pos)
    calc
      ((M.c : ℝ) + (M.d : ℝ) * t) * D = (M.c : ℝ) * D + (M.d : ℝ) * (t * D) := by ring
      _ = (M.c : ℝ) * D + (M.d : ℝ) * N := by rw [htD]
      _ = s n * ((M.a : ℝ) * D + (M.b : ℝ) * N) := by dsimp only [N, D]; ring
      _ = s n * ((M.a : ℝ) * D + (M.b : ℝ) * (t * D)) := by rw [htD]
      _ = s n * ((M.a : ℝ) + (M.b : ℝ) * t) * D := by ring
  have hs_get := of_s_get?_cfEval u t hu_ge1 ht0 ht1 i hi
  rw [hsn_cf] at hs_get
  exact GenContFract.partDen_eq_s_b hs_get

end OMA.S_oeis_a059100_proof

theorem OMA.solution : type_of% @OMA.S_oeis_a059100.main := by
  intro n hn
  have hm : 4 ≤ n ^ 2 := by nlinarith
  constructor
  · refine ⟨1, ?_⟩
    have hlen : 1 < (OMA.S_oeis_a059100_proof.shallitList (n ^ 2) 1).dropLast.length := by
      rw [OMA.S_oeis_a059100_proof.shallitList_one_eq]
      simp
    have hget := OMA.S_oeis_a059100_proof.partDens_of_s_eq n hn 1 1 hlen
    rw [hget]
    congr 1
    simp [OMA.S_oeis_a059100_proof.shallitList_one_eq]
  · rintro b ⟨i, hi⟩
    have hlen : i < (OMA.S_oeis_a059100_proof.shallitList (n ^ 2) (i + 1)).dropLast.length := by
      rw [List.length_dropLast, OMA.S_oeis_a059100_proof.shallitList_length]
      have h1 : i + 1 < 2 ^ (i + 1) := Nat.lt_two_pow_self
      have h2 : 2 ^ (i + 2) = 2 * 2 ^ (i + 1) := pow_succ' 2 (i + 1)
      omega
    have hget := OMA.S_oeis_a059100_proof.partDens_of_s_eq n hn (i + 1) i hlen
    rw [hget, Option.some.injEq] at hi
    rw [← hi]
    have hmem :
        (OMA.S_oeis_a059100_proof.shallitList (n ^ 2) (i + 1)).dropLast[i] ∈
          OMA.S_oeis_a059100_proof.shallitList (n ^ 2) (i + 1) :=
      List.dropLast_subset _ (List.getElem_mem hlen)
    have hbd := (OMA.S_oeis_a059100_proof.shallitList_mem_bounds (n ^ 2) hm (i + 1) _ hmem).2
    have hbd_r :
        (((OMA.S_oeis_a059100_proof.shallitList (n ^ 2) (i + 1)).dropLast[i] : ℕ) : ℝ) ≤
          ((n ^ 2 + 2 : ℕ) : ℝ) := by exact_mod_cast hbd
    simpa using hbd_r
