import OMAStatements.S_oeis_a235892

namespace OMA.S_oeis_a235892

open PowerSeries Finset



/-! ## Blocks: two equal pairs -/

/-- `medEq` holds exactly when the four values form two equal pairs. -/
theorem medEq_iff (p q r s : ℕ) :
    medEq p q r s = true ↔ (p = q ∧ r = s) ∨ (p = r ∧ q = s) ∨ (p = s ∧ q = r) := by
  unfold medEq
  simp only [List.insertionSort, List.foldr_cons, List.foldr_nil]
  repeat' (first | split_ifs | simp only [List.orderedInsert_cons, List.orderedInsert_nil])
  all_goals simp only [List.getD_cons_zero, List.getD_cons_succ, beq_iff_eq]
  all_goals omega

/-- The block with top row (p, q) and bottom row (r, s) consists of two equal pairs. -/
def twoPairs {K : ℕ} (p q r s : Fin K) : Prop :=
  (p = q ∧ r = s) ∨ (p = r ∧ q = s) ∨ (p = s ∧ q = r)

instance {K : ℕ} (p q r s : Fin K) : Decidable (twoPairs p q r s) := by
  unfold twoPairs; infer_instance

lemma twoPairs_refl {K : ℕ} (p q : Fin K) : twoPairs p q p q := Or.inr (Or.inl ⟨rfl, rfl⟩)

lemma twoPairs_symm {K : ℕ} {p q r s : Fin K} (h : twoPairs p q r s) : twoPairs r s p q := by
  simp only [twoPairs, Fin.ext_iff] at h ⊢
  omega

lemma twoPairs_trans {K : ℕ} {p q r s u v : Fin K} (h1 : twoPairs p q r s)
    (h2 : twoPairs r s u v) : twoPairs p q u v := by
  simp only [twoPairs, Fin.ext_iff] at h1 h2 ⊢
  omega

lemma twoPairs_transpose {K : ℕ} {p q r s : Fin K} : twoPairs p q r s ↔ twoPairs p r q s := by
  simp only [twoPairs, Fin.ext_iff]
  omega

/-! ## Rows -/

/-- Rows r (above) and s (below) satisfy the block condition on every pair of columns j, j'. -/
def rel {K k : ℕ} (r s : Fin (k + 1) → Fin K) : Prop :=
  ∀ j j' : Fin (k + 1), twoPairs (r j) (r j') (s j) (s j')

instance {K k : ℕ} (r s : Fin (k + 1) → Fin K) : Decidable (rel r s) := by
  unfold rel; infer_instance

lemma rel_refl {K k : ℕ} (r : Fin (k + 1) → Fin K) : rel r r := fun _ _ => twoPairs_refl _ _

lemma rel_symm {K k : ℕ} {r s : Fin (k + 1) → Fin K} (h : rel r s) : rel s r :=
  fun j j' => twoPairs_symm (h j j')

lemma rel_trans {K k : ℕ} {r s t : Fin (k + 1) → Fin K} (h1 : rel r s) (h2 : rel s t) :
    rel r t :=
  fun j j' => twoPairs_trans (h1 j j') (h2 j j')

/-- The blocks on adjacent columns give the block condition on every pair of columns. -/
lemma rel_of_adj {K k : ℕ} {r s : Fin (k + 1) → Fin K}
    (h : ∀ j : Fin k, twoPairs (r j.castSucc) (r j.succ) (s j.castSucc) (s j.succ)) :
    rel r s := by
  have key : ∀ j : Fin (k + 1), twoPairs (r 0) (s 0) (r j) (s j) := by
    intro j
    induction j using Fin.induction with
    | zero => exact twoPairs_refl _ _
    | succ i ih => exact twoPairs_trans ih (twoPairs_transpose.mp (h i))
  intro j j'
  exact twoPairs_transpose.mpr (twoPairs_trans (twoPairs_symm (key j)) (key j'))

/-! ## The count as a sum over classes -/

/-- The number of (n+1) X (k+1) arrays with entries in Fin K all of whose 2 X 2 blocks on
adjacent rows and columns consist of two equal pairs. -/
def count (K n k : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin (n + 1) → Fin (k + 1) → Fin K)).filter (fun x =>
    ∀ (i : Fin n) (j : Fin k), twoPairs (x i.castSucc j.castSucc) (x i.castSucc j.succ)
      (x i.succ j.castSucc) (x i.succ j.succ))).card

lemma valid_iff {K n k : ℕ} (x : Fin (n + 1) → Fin (k + 1) → Fin K) :
    (∀ (i : Fin n) (j : Fin k), twoPairs (x i.castSucc j.castSucc) (x i.castSucc j.succ)
      (x i.succ j.castSucc) (x i.succ j.succ)) ↔ ∀ i, rel (x 0) (x i) := by
  constructor
  · intro h i
    induction i using Fin.induction with
    | zero => exact rel_refl _
    | succ i ih => exact rel_trans ih (rel_of_adj (h i))
  · intro h i j
    exact rel_trans (rel_symm (h i.castSucc)) (h i.succ) _ _

/-- The size of the class of the row r. -/
def classSize {K k : ℕ} (r : Fin (k + 1) → Fin K) : ℕ :=
  ((Finset.univ : Finset (Fin (k + 1) → Fin K)).filter (fun s => rel r s)).card

lemma count_eq_sum (K n k : ℕ) :
    count K n k = ∑ r : Fin (k + 1) → Fin K, classSize r ^ n := by
  unfold count
  simp_rw [valid_iff]
  rw [Finset.card_eq_sum_card_fiberwise (f := fun x => x 0) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [Finset.filter_filter]
  have hc : classSize r ^ n = (Fintype.piFinset (fun _ : Fin n =>
      (Finset.univ : Finset (Fin (k + 1) → Fin K)).filter (fun s => rel r s))).card := by
    rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rfl
  rw [hc]
  refine Finset.card_bij' (fun x _ => Fin.tail x)
    (fun y _ => (Fin.cons r y : Fin (n + 1) → Fin (k + 1) → Fin K)) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    simp only [Fintype.mem_piFinset, Finset.mem_filter, Finset.mem_univ, true_and]
    intro i
    rw [← hx.2]
    exact hx.1 i.succ
  · intro y hy
    simp only [Fintype.mem_piFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.cons_zero, and_true]
    intro i
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
    · simp only [Fin.cons_zero]
      exact rel_refl r
    · simp only [Fin.cons_succ]
      exact hy i
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    rw [← hx.2]
    exact Fin.cons_self_tail x
  · intro y _
    funext i
    simp [Fin.tail]

/-! ## Class sizes -/

/-- A constant row. -/
def Const {K k : ℕ} (r : Fin (k + 1) → Fin K) : Prop := ∀ j, r j = r 0

instance {K k : ℕ} (r : Fin (k + 1) → Fin K) : Decidable (Const r) := by
  unfold Const; infer_instance

lemma rel_const_iff {K k : ℕ} {r s : Fin (k + 1) → Fin K} (hr : Const r) :
    rel r s ↔ Const s := by
  constructor
  · intro h j
    have h1 := h 0 j
    have h2 := hr j
    simp only [twoPairs, Fin.ext_iff] at h1 h2 ⊢
    omega
  · intro hs j j'
    rw [hr j, hr j', hs j, hs j']
    exact Or.inl ⟨rfl, rfl⟩

lemma card_const (K k : ℕ) :
    ((Finset.univ : Finset (Fin (k + 1) → Fin K)).filter (fun r => Const r)).card = K := by
  have h : (Finset.univ : Finset (Fin (k + 1) → Fin K)).filter (fun r => Const r) =
      Finset.univ.image (fun c : Fin K => fun _ : Fin (k + 1) => c) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hs
      exact ⟨s 0, funext fun j => (hs j).symm⟩
    · rintro ⟨c, rfl⟩ j
      rfl
  rw [h, Finset.card_image_of_injective _ (fun c d hcd => congrFun hcd 0), Finset.card_univ,
    Fintype.card_fin]

lemma classSize_const {K k : ℕ} {r : Fin (k + 1) → Fin K} (hr : Const r) : classSize r = K := by
  have h : (Finset.univ : Finset (Fin (k + 1) → Fin K)).filter (fun s => rel r s) =
      (Finset.univ : Finset (Fin (k + 1) → Fin K)).filter (fun s => Const s) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact rel_const_iff hr
  unfold classSize
  rw [h]
  exact card_const K k

lemma eq_of_rel_of_agree {K k : ℕ} {r s : Fin (k + 1) → Fin K} (h : rel r s) {j0 : Fin (k + 1)}
    (h0 : s j0 = r j0) : s = r := by
  funext j
  have h1 := h j0 j
  simp only [twoPairs, Fin.ext_iff] at h1 h0 ⊢
  omega

/-- The rows related to r other than r itself. -/
def partners {K k : ℕ} (r : Fin (k + 1) → Fin K) : Finset (Fin (k + 1) → Fin K) :=
  (Finset.univ : Finset (Fin (k + 1) → Fin K)).filter (fun s => rel r s ∧ s ≠ r)

lemma classSize_eq {K k : ℕ} (r : Fin (k + 1) → Fin K) :
    classSize r = (partners r).card + 1 := by
  have h : (Finset.univ : Finset (Fin (k + 1) → Fin K)).filter (fun s => rel r s) =
      insert r (partners r) := by
    ext s
    simp only [partners, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hs
      by_cases e : s = r
      · exact Or.inl e
      · exact Or.inr ⟨hs, e⟩
    · rintro (rfl | ⟨hs, _⟩)
      · exact rel_refl _
      · exact hs
  unfold classSize
  rw [h, Finset.card_insert_of_notMem]
  simp [partners]

lemma partners_card_le {K k : ℕ} {r : Fin (k + 1) → Fin K} (hr : ¬ Const r) :
    (partners r).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro s hs s' hs'
  simp only [partners, Finset.mem_filter, Finset.mem_univ, true_and] at hs hs'
  have hd : ∀ j, s j ≠ r j := fun j hj => hs.2 (eq_of_rel_of_agree hs.1 hj)
  have hd' : ∀ j, s' j ≠ r j := fun j hj => hs'.2 (eq_of_rel_of_agree hs'.1 hj)
  obtain ⟨j1, hj1⟩ : ∃ j1, r j1 ≠ r 0 := by
    by_contra hcon
    exact hr fun j => not_not.mp fun hj => hcon ⟨j, hj⟩
  funext j
  by_cases hj : r j = r 0
  · have a1 := hs.1 j j1
    have a2 := hs'.1 j j1
    have b1 := hd j
    have b2 := hd' j
    simp only [twoPairs, Fin.ext_iff, ne_eq] at a1 a2 b1 b2 hj hj1 ⊢
    omega
  · have a1 := hs.1 j 0
    have a2 := hs'.1 j 0
    have b1 := hd j
    have b2 := hd' j
    simp only [twoPairs, Fin.ext_iff, ne_eq] at a1 a2 b1 b2 hj ⊢
    omega

/-- Every nonconstant row of length 2 has a partner (the swapped row). -/
lemma partners_card_two {K : ℕ} {r : Fin (1 + 1) → Fin K} (hr : ¬ Const r) :
    (partners r).card = 1 := by
  have h10 : r 1 ≠ r 0 := by
    intro h
    apply hr
    intro j
    fin_cases j
    · rfl
    · exact h
  rw [Finset.card_eq_one]
  refine ⟨fun j => if j = 0 then r 1 else r 0, ?_⟩
  ext s
  simp only [partners, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · rintro ⟨hs, hne⟩
    have hd : ∀ j, s j ≠ r j := fun j hj => hne (eq_of_rel_of_agree hs hj)
    have a1 := hs 0 1
    have b0 := hd 0
    have b1 := hd 1
    have e0 : s 0 = r 1 := by
      simp only [twoPairs, Fin.ext_iff, ne_eq] at a1 b0 b1 h10 ⊢
      omega
    have e1 : s 1 = r 0 := by
      simp only [twoPairs, Fin.ext_iff, ne_eq] at a1 b0 b1 h10 ⊢
      omega
    funext j
    fin_cases j
    · simp [e0]
    · simp [e1]
  · rintro rfl
    refine ⟨?_, ?_⟩
    · intro j j'
      fin_cases j <;> fin_cases j' <;> simp [twoPairs]
    · intro h
      have := congrFun h 0
      simp only at this
      exact h10 this

/-! ## The formula -/

/-- The number of nonconstant rows of length k + 1. -/
def nonconst (K k : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin (k + 1) → Fin K)).filter (fun r => ¬ Const r)).card

/-- The number of nonconstant rows of length k + 1 with a partner. -/
def partnered (K k : ℕ) : ℕ :=
  ∑ r ∈ (Finset.univ : Finset (Fin (k + 1) → Fin K)).filter (fun r => ¬ Const r),
    (partners r).card

lemma nonconst_add (K k : ℕ) : nonconst K k + K = K ^ (k + 1) := by
  have h := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin (k + 1) → Fin K))) (fun r => Const r)
  rw [card_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin] at h
  unfold nonconst
  omega

lemma count_form (K n k : ℕ) :
    count K n k = K ^ (n + 1) + nonconst K k + (2 ^ n - 1) * partnered K k := by
  rw [count_eq_sum, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun r => Const r)]
  have h1 : ∑ r ∈ Finset.univ.filter (fun r : Fin (k + 1) → Fin K => Const r),
      classSize r ^ n = K ^ (n + 1) := by
    have e : ∀ r ∈ Finset.univ.filter (fun r : Fin (k + 1) → Fin K => Const r),
        classSize r ^ n = K ^ n := fun r hr => by
      rw [classSize_const (Finset.mem_filter.mp hr).2]
    rw [Finset.sum_congr rfl e, Finset.sum_const, card_const, smul_eq_mul, pow_succ]
    ring
  have h2 : ∑ r ∈ Finset.univ.filter (fun r : Fin (k + 1) → Fin K => ¬ Const r),
      classSize r ^ n = nonconst K k + (2 ^ n - 1) * partnered K k := by
    unfold nonconst partnered
    rw [Finset.card_eq_sum_ones, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun r hr => ?_)
    rw [classSize_eq]
    have hle := partners_card_le (Finset.mem_filter.mp hr).2
    have h2n := Nat.two_pow_pos n
    rcases (show (partners r).card = 0 ∨ (partners r).card = 1 by omega) with h | h
    · rw [h]
      simp
    · rw [h, show (1 + 1 : ℕ) = 2 from rfl, mul_one]
      omega
  rw [h1, h2]
  ring

lemma count_symm (K n k : ℕ) : count K n k = count K k n := by
  unfold count
  refine Finset.card_bij' (fun x _ => fun j i => x i j) (fun y _ => fun i j => y j i)
    ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    intro j i
    exact twoPairs_transpose.mp (hx i j)
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    intro i j
    exact twoPairs_transpose.mp (hy j i)
  · intro x _
    rfl
  · intro y _
    rfl

lemma partnered_one (K : ℕ) : partnered K 1 = nonconst K 1 := by
  unfold partnered nonconst
  rw [Finset.card_eq_sum_ones]
  exact Finset.sum_congr rfl (fun r hr => partners_card_two (Finset.mem_filter.mp hr).2)

/-- The count for every K, n, k. -/
theorem count_formula (K n k : ℕ) :
    count K n k + K = K ^ (n + 1) + K ^ (k + 1) + K * (K - 1) * (2 ^ n - 1) * (2 ^ k - 1) := by
  have h2n : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have h2k : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hM : (partnered K k : ℤ) = (K : ℤ) * ((K : ℤ) - 1) * (2 ^ k - 1) := by
    have E1 := count_form K 1 k
    have E2 := count_form K k 1
    have E3 := count_symm K 1 k
    have E4 := nonconst_add K k
    have E5 := nonconst_add K 1
    rw [partnered_one] at E2
    norm_num at E1
    zify [h2k] at E1 E2 E3 E4 E5
    linear_combination (-1 : ℤ) * E1 + E3 + E2 - E4 + (2 ^ k : ℤ) * E5
  have hT := count_form K n k
  have hC := nonconst_add K k
  have hKK : (K : ℤ) * ((K - 1 : ℕ) : ℤ) = (K : ℤ) * ((K : ℤ) - 1) := by
    rcases Nat.eq_zero_or_pos K with h | h
    · subst h
      simp
    · rw [Nat.cast_sub h]
      push_cast
      ring
  zify [h2n, h2k] at hT hC ⊢
  rw [hKK]
  linear_combination hT + hC + ((2 : ℤ) ^ n - 1) * hM

/-- The statements' form of the condition, `medEq` on the blocks of rows i, i' = i + 1 and
columns j, j' = j + 1, is the block form used in `count`. -/
lemma site_iff {K n k : ℕ} (x : Fin (n + 1) → Fin (k + 1) → Fin K) :
    (∀ i i' : Fin (n + 1), i'.val = i.val + 1 → ∀ j j' : Fin (k + 1), j'.val = j.val + 1 →
      medEq (x i j).val (x i j').val (x i' j).val (x i' j').val = true) ↔
    ∀ (i : Fin n) (j : Fin k), twoPairs (x i.castSucc j.castSucc) (x i.castSucc j.succ)
      (x i.succ j.castSucc) (x i.succ j.succ) := by
  constructor
  · intro h i j
    have h1 := h i.castSucc i.succ (by simp) j.castSucc j.succ (by simp)
    rw [medEq_iff] at h1
    simp only [twoPairs, Fin.ext_iff]
    exact h1
  · intro h i i' hi j j' hj
    have hi' : i.val < n := by have := i'.isLt; omega
    have hj' : j.val < k := by have := j'.isLt; omega
    have e1 : i = (⟨i.val, hi'⟩ : Fin n).castSucc := Fin.ext rfl
    have e2 : i' = (⟨i.val, hi'⟩ : Fin n).succ := Fin.ext (by simp [hi])
    have e3 : j = (⟨j.val, hj'⟩ : Fin k).castSucc := Fin.ext rfl
    have e4 : j' = (⟨j.val, hj'⟩ : Fin k).succ := Fin.ext (by simp [hj])
    have h1 := h ⟨i.val, hi'⟩ ⟨j.val, hj'⟩
    rw [← e1, ← e2, ← e3, ← e4] at h1
    rw [medEq_iff]
    simp only [twoPairs, Fin.ext_iff] at h1
    exact h1

/-! ## The entry -/

lemma a_eq_count (n : ℕ) : a n = count 4 n 7 := by
  unfold a count
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact site_iff x

/-- The closed form for every n >= 0, from `count_formula`. -/
lemma a_closed (n : ℕ) : (a n : ℚ) = 4 * (16002 + 381 * 2 ^ n + 4 ^ n) := by
  have h := count_formula 4 n 7
  rw [← a_eq_count] at h
  have h2 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have h' : ((a n + 4 : ℕ) : ℚ) = ((4 ^ (n + 1) + 4 ^ (7 + 1) + 4 * (4 - 1) * (2 ^ n - 1) * (2 ^ 7 - 1) : ℕ) : ℚ) := by
    rw [h]
  push_cast [Nat.cast_sub h2] at h'
  linear_combination h'

theorem closed : ∀ n : ℕ, 1 ≤ n → (a n : ℚ) = 4 * (16002 + 381 * 2 ^ n + 4 ^ n) := fun n _ => a_closed n

lemma a_rec (k : ℕ) : (a (k + 3) : ℚ) + 14 * (a (k + 1) : ℚ) = 7 * (a (k + 2) : ℚ) + 8 * (a (k + 0) : ℚ) := by
  simp only [a_closed]
  ring

lemma a1 : (a 1 : ℚ) = 67072 := by
  rw [a_closed]
  norm_num

lemma a2 : (a 2 : ℚ) = 70168 := by
  rw [a_closed]
  norm_num

lemma a3 : (a 3 : ℚ) = 76456 := by
  rw [a_closed]
  norm_num

/-- The g.f. as stated. -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
    ((1 - X) * (1 - 2 * X) * (1 - 4 * X)) =
      8 * X * (8384 - 49917 * X + 65536 * X ^ 2) := by
  set A := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have e1 : A * ((1 - X) * (1 - 2 * X) * (1 - 4 * X)) = A - C (7 : ℚ) * (A * X ^ 1) + C (14 : ℚ) * (A * X ^ 2) - C (8 : ℚ) * (A * X ^ 3) := by
    rw [show (C (7 : ℚ) : ℚ⟦X⟧) = 7 from map_ofNat C 7, show (C (8 : ℚ) : ℚ⟦X⟧) = 8 from map_ofNat C 8, show (C (14 : ℚ) : ℚ⟦X⟧) = 14 from map_ofNat C 14]
    ring
  have e2 : (8 * X * (8384 - 49917 * X + 65536 * X ^ 2) : ℚ⟦X⟧) = C (67072 : ℚ) * X ^ 1 - C (399336 : ℚ) * X ^ 2 + C (524288 : ℚ) * X ^ 3 := by
    rw [show (C (67072 : ℚ) : ℚ⟦X⟧) = 67072 from map_ofNat C 67072, show (C (399336 : ℚ) : ℚ⟦X⟧) = 399336 from map_ofNat C 399336, show (C (524288 : ℚ) : ℚ⟦X⟧) = 524288 from map_ofNat C 524288]
    ring
  rw [e1, e2]
  ext n
  simp only [map_sub, map_add, coeff_C_mul, coeff_mul_X_pow', coeff_X_pow, coeff_C, hA,
    coeff_mk]
  rcases Nat.lt_or_ge n 4 with hn | hn
  · interval_cases n <;> norm_num only [a1, a2, a3, if_true, if_false]
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
    have h' := a_rec (k + 1)
    simp only [show k + 1 + 3 = k + 4 from rfl, show k + 1 + 2 = k + 3 from rfl,
      show k + 1 + 1 = k + 2 from rfl, show k + 1 + 0 = k + 1 from rfl] at h'
    simp only [show k + 4 - 1 = k + 3 by omega, show k + 4 - 2 = k + 2 by omega,
      show k + 4 - 3 = k + 1 by omega, show ¬ (k + 4 = 0) by omega, show ¬ (k + 3 = 0) by omega,
      show ¬ (k + 2 = 0) by omega, show ¬ (k + 1 = 0) by omega, show 1 ≤ k + 4 by omega,
      show 2 ≤ k + 4 by omega, show 3 ≤ k + 4 by omega, show ¬ (k + 4 = 1) by omega,
      show ¬ (k + 4 = 2) by omega, show ¬ (k + 4 = 3) by omega, if_true, if_false]
    linear_combination h'

/-- Controls: the entry's data. -/
theorem controls : a 1 = 67072 ∧ a 2 = 70168 ∧ a 3 = 76456 ∧ a 4 = 89416 ∧ a 5 = 116872 ∧ a 6 = 177928 ∧ a 7 = 324616 ∧ a 8 = 716296 ∧ a 9 = 1892872 ∧ a 10 = 5818888 ∧ a 11 = 19962376 ∧ a 12 = 73415176 ∧ a 13 = 280984072 ∧ a 14 = 1098775048 ∧ a 15 = 4344969736 ∧ a 16 = 17279810056 ∧ a 17 = 68919294472 ∧ a 18 = 275277478408 ∧ a 19 = 1100310706696 ∧ a 20 = 4399644604936 ∧ a 21 = 17595382168072 := by
  have v1 : (a 1 : ℚ) = 67072 := by rw [a_closed]; norm_num
  have v2 : (a 2 : ℚ) = 70168 := by rw [a_closed]; norm_num
  have v3 : (a 3 : ℚ) = 76456 := by rw [a_closed]; norm_num
  have v4 : (a 4 : ℚ) = 89416 := by rw [a_closed]; norm_num
  have v5 : (a 5 : ℚ) = 116872 := by rw [a_closed]; norm_num
  have v6 : (a 6 : ℚ) = 177928 := by rw [a_closed]; norm_num
  have v7 : (a 7 : ℚ) = 324616 := by rw [a_closed]; norm_num
  have v8 : (a 8 : ℚ) = 716296 := by rw [a_closed]; norm_num
  have v9 : (a 9 : ℚ) = 1892872 := by rw [a_closed]; norm_num
  have v10 : (a 10 : ℚ) = 5818888 := by rw [a_closed]; norm_num
  have v11 : (a 11 : ℚ) = 19962376 := by rw [a_closed]; norm_num
  have v12 : (a 12 : ℚ) = 73415176 := by rw [a_closed]; norm_num
  have v13 : (a 13 : ℚ) = 280984072 := by rw [a_closed]; norm_num
  have v14 : (a 14 : ℚ) = 1098775048 := by rw [a_closed]; norm_num
  have v15 : (a 15 : ℚ) = 4344969736 := by rw [a_closed]; norm_num
  have v16 : (a 16 : ℚ) = 17279810056 := by rw [a_closed]; norm_num
  have v17 : (a 17 : ℚ) = 68919294472 := by rw [a_closed]; norm_num
  have v18 : (a 18 : ℚ) = 275277478408 := by rw [a_closed]; norm_num
  have v19 : (a 19 : ℚ) = 1100310706696 := by rw [a_closed]; norm_num
  have v20 : (a 20 : ℚ) = 4399644604936 := by rw [a_closed]; norm_num
  have v21 : (a 21 : ℚ) = 17595382168072 := by rw [a_closed]; norm_num
  exact ⟨by exact_mod_cast v1, by exact_mod_cast v2, by exact_mod_cast v3, by exact_mod_cast v4, by exact_mod_cast v5, by exact_mod_cast v6, by exact_mod_cast v7, by exact_mod_cast v8, by exact_mod_cast v9, by exact_mod_cast v10, by exact_mod_cast v11, by exact_mod_cast v12, by exact_mod_cast v13, by exact_mod_cast v14, by exact_mod_cast v15, by exact_mod_cast v16, by exact_mod_cast v17, by exact_mod_cast v18, by exact_mod_cast v19, by exact_mod_cast v20, by exact_mod_cast v21⟩

/-- The conjunction stated as `main`. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) *
      ((1 - X) * (1 - 2 * X) * (1 - 4 * X)) =
        8 * X * (8384 - 49917 * X + 65536 * X ^ 2) ∧
      ∀ n : ℕ, 1 ≤ n → (a n : ℚ) = 4 * (16002 + 381 * 2 ^ n + 4 ^ n) :=
  ⟨gf, closed⟩

end OMA.S_oeis_a235892

theorem OMA.solution : type_of% @OMA.S_oeis_a235892.main :=
  OMA.S_oeis_a235892.conjecture
