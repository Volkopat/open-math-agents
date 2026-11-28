import OMAStatements.S_oeis_a187235

open Equiv Equiv.Perm Finset Polynomial Nat MulAction Subgroup

namespace A187235

noncomputable def cycles {α : Type*} [Fintype α] [DecidableEq α] (σ : Perm α) : ℕ :=
  OMA.S_oeis_a187235.cycleCount σ

abbrev orb {α : Type*} [DecidableEq α] (σ : Perm α) : Setoid α :=
  orbitRel (zpowers σ) α

abbrev Place (n : ℕ) : Type := OMA.S_oeis_a187235.Placement n

abbrev keeps (n : ℕ) (σ : Perm (Fin (2 * n + 1))) : Prop :=
  OMA.S_oeis_a187235.ParityPreserving n σ

/-! ### Diagonal lengths -/

def diagLen (n d : ℕ) : ℕ := min (d + 1) (2 * n - 1 - d)

def rowLo (n d : ℕ) : ℕ := d - min d (n - 1)

lemma diagLen_low {n d : ℕ} (hn : 1 ≤ n) (hd : d < n) : diagLen n d = d + 1 := by
  have hle : d + 1 ≤ 2 * n - 1 - d := by omega
  simp [diagLen, min_eq_left hle]

lemma diagLen_high {n d : ℕ} (hn : 1 ≤ n) (hdn : n ≤ d) (hd : d < 2 * n - 1) :
    diagLen n d = 2 * n - 1 - d := by
  have hle : 2 * n - 1 - d ≤ d + 1 := by omega
  simp [diagLen, min_eq_right hle]

lemma diagLen_eq_span (n d : ℕ) (hn : 1 ≤ n) (hd : d < 2 * n - 1) :
    diagLen n d = min d (n - 1) - rowLo n d + 1 := by
  unfold diagLen rowLo
  by_cases h : d ≤ n - 1
  · rw [min_eq_left h, min_eq_left (show d + 1 ≤ 2 * n - 1 - d by omega)]
    omega
  · rw [min_eq_right (show n - 1 ≤ d by omega),
      min_eq_right (show 2 * n - 1 - d ≤ d + 1 by omega)]
    omega

lemma diagLen_pos {n d : ℕ} (hn : 1 ≤ n) (hd : d < 2 * n - 1) : 0 < diagLen n d := by
  rw [diagLen_eq_span n d hn hd]
  omega

lemma row_bound (n d i : ℕ) (hn : 1 ≤ n) (hd : d < 2 * n - 1) (hi : i < diagLen n d) :
    rowLo n d + i < n := by
  unfold rowLo
  by_cases h : d ≤ n - 1
  · rw [diagLen_low hn (by omega)] at hi
    rw [min_eq_left h]
    omega
  · rw [diagLen_high hn (by omega) hd] at hi
    rw [min_eq_right (show n - 1 ≤ d by omega)]
    omega

lemma col_bound (n d i : ℕ) (hn : 1 ≤ n) (hd : d < 2 * n - 1) (hi : i < diagLen n d) :
    d - (rowLo n d + i) < n := by
  unfold rowLo
  by_cases h : d ≤ n - 1
  · rw [diagLen_low hn (by omega)] at hi
    rw [min_eq_left h]
    omega
  · rw [diagLen_high hn (by omega) hd] at hi
    rw [min_eq_right (show n - 1 ≤ d by omega)]
    omega

lemma sum_bound (n d i : ℕ) (hn : 1 ≤ n) (hd : d < 2 * n - 1) (hi : i < diagLen n d) :
    rowLo n d + i + (d - (rowLo n d + i)) = d := by
  unfold rowLo
  by_cases h : d ≤ n - 1
  · rw [diagLen_low hn (by omega)] at hi
    rw [min_eq_left h]
    omega
  · rw [diagLen_high hn (by omega) hd] at hi
    rw [min_eq_right (show n - 1 ≤ d by omega)]
    omega

def squareOf {n : ℕ} (d : Fin (2 * n - 1)) (i : Fin (diagLen n d.val)) : Fin n × Fin n :=
  have hn : 1 ≤ n := by have := d.isLt; omega
  (⟨rowLo n d.val + i.val, row_bound n d.val i.val hn d.isLt i.isLt⟩,
    ⟨d.val - (rowLo n d.val + i.val), col_bound n d.val i.val hn d.isLt i.isLt⟩)

lemma squareOf_sum {n : ℕ} (d : Fin (2 * n - 1)) (i : Fin (diagLen n d.val)) :
    (squareOf d i).1.val + (squareOf d i).2.val = d.val := by
  have hn : 1 ≤ n := by have := d.isLt; omega
  simp only [squareOf, Fin.val_mk]
  exact sum_bound n d.val i.val hn d.isLt i.isLt

lemma squareOf_diag {n : ℕ} (d : Fin (2 * n - 1)) (i : Fin (diagLen n d.val)) :
    (squareOf d i).1.val + (squareOf d i).2.val = d.val :=
  squareOf_sum d i

lemma index_bound (n r c : ℕ) (hr : r < n) (hc : c < n) :
    r - rowLo n (r + c) < diagLen n (r + c) := by
  have hd : r + c < 2 * n - 1 := by omega
  have hn : 1 ≤ n := by omega
  unfold rowLo
  by_cases h : r + c ≤ n - 1
  · rw [diagLen_low hn (by omega), min_eq_left h]
    omega
  · rw [diagLen_high hn (by omega) hd, min_eq_right (show n - 1 ≤ r + c by omega)]
    omega

lemma index_cancel (n d i : ℕ) (hn : 1 ≤ n) (hd : d < 2 * n - 1) (hi : i < diagLen n d) :
    rowLo n d + i - rowLo n (rowLo n d + i + (d - (rowLo n d + i))) = i := by
  have hsum := sum_bound n d i hn hd hi
  unfold rowLo at hsum ⊢
  by_cases h : d ≤ n - 1
  · rw [diagLen_low hn (by omega)] at hi
    rw [min_eq_left h] at hsum ⊢
    omega
  · rw [diagLen_high hn (by omega) hd] at hi
    rw [min_eq_right (show n - 1 ≤ d by omega)] at hsum ⊢
    omega

lemma row_back (n r c : ℕ) (hr : r < n) (hc : c < n) :
    rowLo n (r + c) + (r - rowLo n (r + c)) = r := by
  have hd : r + c < 2 * n - 1 := by omega
  unfold rowLo
  by_cases h : r + c ≤ n - 1
  · rw [min_eq_left h]
    omega
  · rw [min_eq_right (show n - 1 ≤ r + c by omega)]
    omega

lemma col_back (n r c : ℕ) (hr : r < n) (hc : c < n) :
    r + c - (rowLo n (r + c) + (r - rowLo n (r + c))) = c := by
  have hd : r + c < 2 * n - 1 := by omega
  unfold rowLo
  by_cases h : r + c ≤ n - 1
  · rw [min_eq_left h]
    omega
  · rw [min_eq_right (show n - 1 ≤ r + c by omega)]
    omega

def indexOf {n : ℕ} (s : Fin n × Fin n) :
    Fin (diagLen n (s.1.val + s.2.val)) :=
  ⟨s.1.val - rowLo n (s.1.val + s.2.val), index_bound n s.1.val s.2.val s.1.isLt s.2.isLt⟩

lemma indexOf_squareOf_val {n : ℕ} (d : Fin (2 * n - 1)) (i : Fin (diagLen n d.val)) :
    (indexOf (squareOf d i)).val = i.val := by
  have hn : 1 ≤ n := by have := d.isLt; omega
  simp only [indexOf, squareOf, Fin.val_mk]
  exact index_cancel n d.val i.val hn d.isLt i.isLt

lemma squareOf_indexOf {n : ℕ} (s : Fin n × Fin n) :
    squareOf ⟨s.1.val + s.2.val, by
      have := s.1.isLt
      have := s.2.isLt
      omega⟩ (indexOf s) = s := by
  apply Prod.ext
  · apply Fin.ext
    simp only [squareOf, indexOf, Fin.val_mk]
    exact row_back n s.1.val s.2.val s.1.isLt s.2.isLt
  · apply Fin.ext
    simp only [squareOf, indexOf, Fin.val_mk]
    exact col_back n s.1.val s.2.val s.1.isLt s.2.isLt

/-! ### Generating functions -/

lemma natDegree_one_add_C_X_le (c : ℕ) : (1 + C c * X : ℕ[X]).natDegree ≤ 1 := by
  calc
    (1 + C c * X).natDegree ≤ max (1 : ℕ[X]).natDegree (C c * X).natDegree := natDegree_add_le _ _
    _ ≤ 1 := by
      apply max_le
      · simp
      · exact (natDegree_C_mul_le c X).trans (by simp)

lemma reflect_one_add_C_X (c : ℕ) : reflect 1 (1 + C c * X : ℕ[X]) = X + C c := by
  ext i
  rw [coeff_reflect, coeff_add, coeff_add, coeff_one, coeff_C_mul, coeff_X, coeff_X, coeff_C]
  by_cases h1 : i = 1
  · subst h1
    simp [revAt_le (Nat.le_refl 1)]
  · by_cases h0 : i = 0
    · subst h0
      simp [revAt_zero]
    · have hgt : 1 < i := by omega
      have hne : 1 ≠ i := by omega
      simp [revAt_eq_self_of_lt hgt, h0, hne]

lemma natDegree_prod_one_add_le {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℕ) :
    (∏ i ∈ s, (1 + C (f i) * X : ℕ[X])).natDegree ≤ s.card := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha, card_insert_of_notMem ha]
    refine natDegree_mul_le.trans ?_
    calc
      (1 + C (f a) * X).natDegree + (∏ i ∈ s, (1 + C (f i) * X : ℕ[X])).natDegree
        ≤ 1 + s.card := Nat.add_le_add (natDegree_one_add_C_X_le (f a)) ih
      _ = s.card + 1 := by omega

lemma reflect_prod_one_add {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℕ) :
    reflect s.card (∏ i ∈ s, (1 + C (f i) * X : ℕ[X])) =
      ∏ i ∈ s, (X + C (f i)) := by
  induction s using Finset.induction with
  | empty => simp [reflect_one]
  | insert a s ha ih =>
    rw [card_insert_of_notMem ha, add_comm, prod_insert ha, prod_insert ha,
      reflect_mul _ _ (natDegree_one_add_C_X_le (f a)) (natDegree_prod_one_add_le s f),
      reflect_one_add_C_X, ih]

lemma coeff_mul_one_add_C_X (p : ℕ[X]) (a k : ℕ) :
    ((1 + C a * X) * p).coeff k =
      p.coeff k + a * (if k = 0 then 0 else p.coeff (k - 1)) := by
  have hmul : (1 + C a * X) * p = p + C a * (X * p) := by
    rw [add_mul, one_mul, mul_assoc]
  rw [hmul, coeff_add, coeff_C_mul]
  cases k with
  | zero => simp [coeff_X_mul_zero]
  | succ k => simp [coeff_X_mul, Nat.add_sub_cancel]

lemma coeff_prod_one_add {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℕ) (k : ℕ) :
    (∏ i ∈ s, (1 + C (f i) * X : ℕ[X])).coeff k =
      ∑ t ∈ s.powersetCard k, ∏ i ∈ t, f i := by
  induction s using Finset.induction generalizing k with
  | empty =>
    cases k with
    | zero => simp [powersetCard_zero]
    | succ k =>
      have hempty : (∅ : Finset ι).card < k + 1 := by simp
      simp [powersetCard_eq_empty.mpr hempty, coeff_one]
  | insert a s ha ih =>
    rw [prod_insert ha]
    cases k with
    | zero =>
      rw [coeff_mul_one_add_C_X, if_pos rfl, mul_zero, add_zero, ih, powersetCard_zero]
      simp
    | succ k =>
      rw [coeff_mul_one_add_C_X, if_neg (Nat.succ_ne_zero k), Nat.succ_sub_one, ih, ih,
        powersetCard_succ_insert ha]
      have hdis : Disjoint (s.powersetCard (k + 1)) ((s.powersetCard k).image (insert a)) := by
        rw [disjoint_left]
        intro t ht him
        obtain ⟨u, hu, rfl⟩ := mem_image.mp him
        exact ha ((mem_powersetCard.mp ht).1 (mem_insert_self a u))
      rw [sum_union hdis]
      have hinj : Set.InjOn (insert a) (s.powersetCard k : Set (Finset ι)) := by
        intro u hu v hv heq
        have hau : a ∉ u := notMem_mono (mem_powersetCard.mp hu).1 ha
        have hav : a ∉ v := notMem_mono (mem_powersetCard.mp hv).1 ha
        apply congrArg (erase · a) at heq
        simpa [erase_insert hau, erase_insert hav] using heq
      rw [sum_image hinj]
      have hprod : ∀ u ∈ s.powersetCard k, ∏ i ∈ insert a u, f i = f a * ∏ i ∈ u, f i := by
        intro u hu
        exact prod_insert (notMem_mono (mem_powersetCard.mp hu).1 ha)
      rw [sum_congr rfl hprod, mul_sum, add_comm]

noncomputable def rising (m : ℕ) : ℕ[X] := ∏ j ∈ range m, (X + C j)

lemma coeff_X_add_C_mul (p : ℕ[X]) (a k : ℕ) :
    ((X + C a) * p).coeff k =
      (if k = 0 then 0 else p.coeff (k - 1)) + a * p.coeff k := by
  rw [add_mul, coeff_add, coeff_C_mul]
  cases k with
  | zero => simp [coeff_X_mul_zero]
  | succ k => simp [coeff_X_mul]

lemma coeff_rising (m k : ℕ) : (rising m).coeff k = stirlingFirst m k := by
  induction m generalizing k with
  | zero =>
    cases k with
    | zero => simp [rising, stirlingFirst]
    | succ k => simp [rising, stirlingFirst, coeff_one]
  | succ m ih =>
    have hr : rising (m + 1) = (X + C m) * rising m := by
      rw [rising, rising, prod_range_succ, mul_comm]
    rw [hr, coeff_X_add_C_mul]
    cases k with
    | zero =>
      rw [if_pos rfl, zero_add, ih, stirlingFirst_succ_zero]
      cases m with
      | zero => simp [stirlingFirst]
      | succ m => simp [stirlingFirst_succ_zero]
    | succ k =>
      rw [if_neg (Nat.succ_ne_zero k), Nat.succ_sub_one, ih, ih, stirlingFirst_succ_succ]
      ac_rfl

lemma rising_eq_X_mul (m : ℕ) (hm : 1 ≤ m) :
    rising m = X * ∏ k ∈ range (m - 1), (X + C (k + 1)) := by
  rw [show m = (m - 1) + 1 by omega, rising, prod_range_succ', mul_comm]
  simp

noncomputable def oneAdd (m : ℕ) : ℕ[X] := ∏ k ∈ range m, (1 + C (k + 1) * X)

lemma reflect_oneAdd (m : ℕ) :
    reflect m (oneAdd m) = ∏ k ∈ range m, (X + C (k + 1)) := by
  simpa [oneAdd] using reflect_prod_one_add (range m) (fun k => k + 1)

lemma range_split (n : ℕ) (hn : 1 ≤ n) :
    range (2 * n - 1) = range n ∪ (range (n - 1)).image (fun i => i + n) := by
  ext d
  simp only [mem_union, mem_range, mem_image]
  constructor
  · intro hd
    by_cases h : d < n
    · exact Or.inl h
    · exact Or.inr ⟨d - n, by omega, by omega⟩
  · rintro (hd | ⟨i, hi, rfl⟩) <;> omega

lemma range_split_disj (n : ℕ) :
    Disjoint (range n) ((range (n - 1)).image (fun i => i + n)) := by
  rw [disjoint_left]
  intro d hd him
  simp only [mem_range, mem_image] at hd him
  obtain ⟨i, hi, rfl⟩ := him
  omega

lemma bishopPoly_eq (n : ℕ) (hn : 1 ≤ n) :
    (∏ d ∈ range (2 * n - 1), (1 + C (diagLen n d) * X : ℕ[X])) =
      oneAdd n * oneAdd (n - 1) := by
  rw [range_split n hn, prod_union (range_split_disj n)]
  have hlow : ∏ d ∈ range n, (1 + C (diagLen n d) * X : ℕ[X]) = oneAdd n := by
    unfold oneAdd
    refine prod_congr rfl fun d hd => ?_
    rw [diagLen_low hn (mem_range.mp hd)]
  have hhigh : ∏ d ∈ (range (n - 1)).image (fun i => i + n),
      (1 + C (diagLen n d) * X : ℕ[X]) = oneAdd (n - 1) := by
    rw [prod_image (fun i hi j hj heq => by
      have hi' : i < n - 1 := mem_range.mp hi
      have hj' : j < n - 1 := mem_range.mp hj
      omega)]
    unfold oneAdd
    refine prod_nbij' (fun i => n - 2 - i) (fun i => n - 2 - i)
      (fun i hi => by
        have hi' : i < n - 1 := mem_range.mp hi
        simp only [mem_range]
        omega)
      (fun i hi => by
        have hi' : i < n - 1 := mem_range.mp hi
        simp only [mem_range]
        omega)
      (fun i hi => by
        have hi' : i < n - 1 := mem_range.mp hi
        omega)
      (fun i hi => by
        have hi' : i < n - 1 := mem_range.mp hi
        omega)
      (fun i hi => by
        have hi' : i < n - 1 := mem_range.mp hi
        have hlen : diagLen n (i + n) = n - 1 - i := by
          have hlt : i + n < 2 * n - 1 := by omega
          rw [diagLen_high hn (by omega) hlt]
          omega
        have hnat : n - 1 - i = n - 2 - i + 1 := by omega
        rw [hlen, hnat])
  rw [hlow, hhigh]

lemma bishop_coeff_eq_rising (n : ℕ) (hn : 1 ≤ n) :
    (∏ d ∈ range (2 * n - 1), (1 + C (diagLen n d) * X : ℕ[X])).coeff n =
      (rising (n + 1) * rising n).coeff (n + 1) := by
  rw [bishopPoly_eq n hn]
  have hp : reflect n (oneAdd n) = ∏ k ∈ range n, (X + C (k + 1)) := reflect_oneAdd n
  have hq : reflect (n - 1) (oneAdd (n - 1)) =
      ∏ k ∈ range (n - 1), (X + C (k + 1)) := reflect_oneAdd (n - 1)
  have hdeg1 : (oneAdd n).natDegree ≤ n := by
    simpa [oneAdd] using natDegree_prod_one_add_le (range n) (fun k => k + 1)
  have hdeg2 : (oneAdd (n - 1)).natDegree ≤ n - 1 := by
    simpa [oneAdd] using natDegree_prod_one_add_le (range (n - 1)) (fun k => k + 1)
  have href : reflect (n + (n - 1)) (oneAdd n * oneAdd (n - 1)) =
      reflect n (oneAdd n) * reflect (n - 1) (oneAdd (n - 1)) :=
    reflect_mul _ _ hdeg1 hdeg2
  have hsum : n + (n - 1) = 2 * n - 1 := by omega
  rw [rising_eq_X_mul (n + 1) (by omega), rising_eq_X_mul n hn, Nat.add_sub_cancel]
  have hmul : (X * ∏ k ∈ range n, (X + C (k + 1))) *
      (X * ∏ k ∈ range (n - 1), (X + C (k + 1))) =
      X ^ 2 * (reflect n (oneAdd n) * reflect (n - 1) (oneAdd (n - 1))) := by
    rw [hp, hq]
    ring
  rw [hmul, ← href, hsum]
  have hidx : n + 1 = (n - 1) + 2 := by omega
  rw [hidx, coeff_X_pow_mul]
  have hle : n - 1 ≤ 2 * n - 1 := by omega
  rw [coeff_reflect, revAt_le hle]
  congr 1
  omega

/-! ### Placements -/

def diagOf (n : ℕ) (s : Fin n × Fin n) : Fin (2 * n - 1) :=
  ⟨s.1.val + s.2.val, by
    have := s.1.isLt
    have := s.2.isLt
    omega⟩

lemma diagOf_val (n : ℕ) (s : Fin n × Fin n) :
    (diagOf n s).val = s.1.val + s.2.val := rfl

def BishopPick (n : ℕ) : Type :=
  Σ s : {s : Finset (Fin (2 * n - 1)) // s.card = n},
    ∀ d : s.1, Fin (diagLen n d.1.val)

def squaresOf {n : ℕ} (p : BishopPick n) : Finset (Fin n × Fin n) :=
  p.1.1.attach.image (fun d => squareOf d.1 (p.2 d))

lemma squaresOf_card {n : ℕ} (p : BishopPick n) : (squaresOf p).card = n := by
  have hinj : Set.InjOn (fun d : p.1.1 => squareOf d.1 (p.2 d)) (p.1.1.attach : Set _) := by
    intro d _ e _ heq
    have hs := congrArg (fun s : Fin n × Fin n => s.1.val + s.2.val) heq
    simp only [squareOf_sum] at hs
    ext
    exact hs
  rw [squaresOf, Finset.card_image_of_injOn hinj, card_attach]
  exact p.1.2

lemma squaresOf_nonattack {n : ℕ} (p : BishopPick n) :
    OMA.S_oeis_a187235.Nonattacking n (squaresOf p) := by
  intro s hs t ht hne hsum
  rw [squaresOf, mem_image] at hs ht
  obtain ⟨d, hd, rfl⟩ := hs
  obtain ⟨e, he, rfl⟩ := ht
  have hde : d.1.val = e.1.val := by
    simpa [squareOf_sum] using hsum
  have : d = e := Subtype.ext (Fin.ext hde)
  cases this
  exact hne rfl

lemma mem_squaresOf_diag {n : ℕ} (p : BishopPick n)
    {d : p.1.1} :
    squareOf d.1 (p.2 d) ∈ squaresOf p ∧
      diagOf n (squareOf d.1 (p.2 d)) = d.1 := by
  refine ⟨mem_image.mpr ⟨d, mem_attach _ d, rfl⟩, ?_⟩
  apply Fin.ext
  simp [diagOf, squareOf_sum]

def diagsOf {n : ℕ} (S : Place n) : Finset (Fin (2 * n - 1)) :=
  S.1.image (diagOf n)

lemma diagsOf_card {n : ℕ} (S : Place n) : (diagsOf S).card = n := by
  have hinj : Set.InjOn (diagOf n) (S.1 : Set _) := by
    intro a ha b hb hab
    have hsum : a.1.val + a.2.val = b.1.val + b.2.val := by
      simpa [diagOf, Fin.ext_iff] using hab
    by_cases hne : a = b
    · exact hne
    · exact absurd hsum (S.2.2 a ha b hb hne)
  rw [diagsOf, Finset.card_image_of_injOn hinj]
  exact S.2.1

lemma unique_on_diag {n : ℕ} (S : Place n) (d : Fin (2 * n - 1)) (hd : d ∈ diagsOf S) :
    ∃! s, s ∈ S.1 ∧ diagOf n s = d := by
  rw [diagsOf, mem_image] at hd
  obtain ⟨s, hs, hsdi⟩ := hd
  refine ⟨s, ⟨hs, hsdi⟩, ?_⟩
  intro t ht
  have hsum : t.1.val + t.2.val = s.1.val + s.2.val := by
    have h1 := congrArg Fin.val ht.2
    have h2 := congrArg Fin.val hsdi
    simp only [diagOf_val] at h1 h2
    omega
  by_cases hne : t = s
  · exact hne
  · exact absurd hsum (S.2.2 t ht.1 s hs hne)

def chosenSquare {n : ℕ} (S : Place n) (d : {d : Fin (2 * n - 1) // d ∈ diagsOf S}) :
    Fin n × Fin n :=
  S.1.choose (fun s => diagOf n s = d.1) (unique_on_diag S d.1 d.2)

lemma chosenSquare_mem {n : ℕ} (S : Place n)
    (d : {d : Fin (2 * n - 1) // d ∈ diagsOf S}) :
    chosenSquare S d ∈ S.1 ∧ diagOf n (chosenSquare S d) = d.1 :=
  S.1.choose_spec (fun s => diagOf n s = d.1) (unique_on_diag S d.1 d.2)

lemma chosenSquare_unique {n : ℕ} (S : Place n)
    (d : {d : Fin (2 * n - 1) // d ∈ diagsOf S})
    {s : Fin n × Fin n} (hs : s ∈ S.1) (hd : diagOf n s = d.1) :
    s = chosenSquare S d := by
  have huniq := unique_on_diag S d.1 d.2
  have hmem := chosenSquare_mem S d
  exact huniq.unique ⟨hs, hd⟩ hmem

def pickIndex {n : ℕ} (S : Place n) (d : {d : Fin (2 * n - 1) // d ∈ diagsOf S}) :
    Fin (diagLen n d.1.val) :=
  let s := chosenSquare S d
  have hsum : s.1.val + s.2.val = d.1.val := by
    simpa [diagOf] using congrArg Fin.val (chosenSquare_mem S d).2
  Fin.cast (congrArg (diagLen n) hsum) (indexOf s)

def pickOf {n : ℕ} (S : Place n) : BishopPick n :=
  ⟨⟨diagsOf S, diagsOf_card S⟩, fun d => pickIndex S d⟩

def placeOf {n : ℕ} (p : BishopPick n) : Place n :=
  ⟨squaresOf p, squaresOf_card p, squaresOf_nonattack p⟩

lemma pickIndex_val {n : ℕ} (S : Place n)
    (d : {d : Fin (2 * n - 1) // d ∈ diagsOf S}) :
    (pickIndex S d).val = (indexOf (chosenSquare S d)).val := by
  simp only [pickIndex, indexOf, Fin.val_cast, Fin.val_mk]

lemma squareOf_pickIndex {n : ℕ} (S : Place n)
    (d : {d : Fin (2 * n - 1) // d ∈ diagsOf S}) :
    squareOf d.1 (pickIndex S d) = chosenSquare S d := by
  have hsum : (chosenSquare S d).1.val + (chosenSquare S d).2.val = d.1.val := by
    simpa [diagOf_val] using congrArg Fin.val (chosenSquare_mem S d).2
  apply Prod.ext
  · apply Fin.ext
    simp only [squareOf, Fin.val_mk]
    rw [pickIndex_val]
    simp only [indexOf, Fin.val_mk]
    rw [hsum]
    have hr := row_back n (chosenSquare S d).1.val (chosenSquare S d).2.val
      (chosenSquare S d).1.isLt (chosenSquare S d).2.isLt
    rw [hsum] at hr
    exact hr
  · apply Fin.ext
    simp only [squareOf, Fin.val_mk]
    rw [pickIndex_val]
    simp only [indexOf, Fin.val_mk]
    rw [hsum]
    have hc := col_back n (chosenSquare S d).1.val (chosenSquare S d).2.val
      (chosenSquare S d).1.isLt (chosenSquare S d).2.isLt
    rw [hsum] at hc
    exact hc

lemma squares_pick {n : ℕ} (S : Place n) : squaresOf (pickOf S) = S.1 := by
  ext x
  constructor
  · intro hx
    rw [squaresOf, pickOf, mem_image] at hx
    obtain ⟨d, _, rfl⟩ := hx
    rw [squareOf_pickIndex]
    exact (chosenSquare_mem S d).1
  · intro hx
    let d : {d : Fin (2 * n - 1) // d ∈ diagsOf S} :=
      ⟨diagOf n x, by rw [diagsOf]; exact mem_image.mpr ⟨x, hx, rfl⟩⟩
    have hxeq : x = chosenSquare S d := chosenSquare_unique S d hx rfl
    rw [squaresOf, pickOf]
    refine mem_image.mpr ⟨d, mem_attach _ d, ?_⟩
    rw [squareOf_pickIndex]
    exact hxeq.symm

lemma diags_squares {n : ℕ} (p : BishopPick n) : diagsOf (placeOf p) = p.1.1 := by
  ext d
  constructor
  · intro hd
    unfold diagsOf at hd
    change d ∈ (squaresOf p).image (diagOf n) at hd
    rw [mem_image] at hd
    obtain ⟨s, hs, rfl⟩ := hd
    unfold squaresOf at hs
    rw [mem_image] at hs
    obtain ⟨e, _, rfl⟩ := hs
    have hval : (diagOf n (squareOf e.1 (p.2 e))).val = e.1.val := by
      simp [diagOf_val, squareOf_sum]
    have : diagOf n (squareOf e.1 (p.2 e)) = e.1 := Fin.ext hval
    simpa [this] using (show e.1 ∈ p.1.1 from e.2)
  · intro hd
    unfold diagsOf
    change d ∈ (squaresOf p).image (diagOf n)
    rw [mem_image]
    refine ⟨squareOf d (p.2 ⟨d, hd⟩), ?_, ?_⟩
    · unfold squaresOf
      rw [mem_image]
      exact ⟨⟨d, hd⟩, mem_attach _ _, rfl⟩
    · apply Fin.ext
      simp [diagOf_val, squareOf_sum]

lemma placeEquiv_left {n : ℕ} (S : Place n) : placeOf (pickOf S) = S := by
  apply Subtype.ext
  simpa [placeOf] using squares_pick S

lemma pickIndex_square {n : ℕ} (p : BishopPick n) (d : p.1.1)
    (e : {x : Fin (2 * n - 1) // x ∈ diagsOf (placeOf p)}) (hde : e.1 = d.1) :
    (pickIndex (placeOf p) e).val = (p.2 d).val := by
  rw [pickIndex_val]
  have hchosen : chosenSquare (placeOf p) e = squareOf d.1 (p.2 d) :=
    (chosenSquare_unique (placeOf p) e (by
      change squareOf d.1 (p.2 d) ∈ squaresOf p
      unfold squaresOf
      exact mem_image.mpr ⟨d, mem_attach _ d, rfl⟩) (by
      apply Fin.ext
      simp [diagOf_val, squareOf_sum, hde])).symm
  rw [hchosen]
  exact indexOf_squareOf_val d.1 (p.2 d)

lemma rec_pick_val {n : ℕ}
    {s t : {u : Finset (Fin (2 * n - 1)) // u.card = n}} (h : s = t)
    (f : ∀ d : s.1, Fin (diagLen n d.1.val))
    (d : {d : Fin (2 * n - 1) // d ∈ t.1}) :
    (Eq.rec (motive := fun x _ => ∀ e : x.1, Fin (diagLen n e.1.val)) f h d).val =
      (f ⟨d.1, (congrArg Subtype.val h).symm ▸ d.2⟩).val := by
  subst h
  rfl

lemma placeEquiv_right {n : ℕ} (p : BishopPick n) : pickOf (placeOf p) = p := by
  have hsub : (pickOf (placeOf p)).1 = p.1 := Subtype.ext (diags_squares p)
  apply Sigma.eq hsub
  funext d
  apply Fin.ext
  rw [rec_pick_val hsub (pickOf (placeOf p)).2]
  apply pickIndex_square
  rfl

def placeEquiv (n : ℕ) : Place n ≃ BishopPick n where
  toFun := pickOf
  invFun := placeOf
  left_inv := placeEquiv_left
  right_inv := placeEquiv_right

lemma sum_powerset_diag (n : ℕ) :
    ∑ s : {s : Finset (Fin (2 * n - 1)) // s.card = n}, ∏ d ∈ s.1, diagLen n d.val =
      (∏ d ∈ range (2 * n - 1), (1 + C (diagLen n d) * X : ℕ[X])).coeff n := by
  have hfin : (∏ i : Fin (2 * n - 1), (1 + C (diagLen n i.val) * X : ℕ[X])).coeff n =
      ∑ t ∈ (univ : Finset (Fin (2 * n - 1))).powersetCard n, ∏ i ∈ t, diagLen n i.val := by
    simpa using coeff_prod_one_add (univ : Finset (Fin (2 * n - 1)))
      (fun i => diagLen n i.val) n
  have hrange : ∏ i : Fin (2 * n - 1), (1 + C (diagLen n i.val) * X : ℕ[X]) =
      ∏ d ∈ range (2 * n - 1), (1 + C (diagLen n d) * X : ℕ[X]) := by
    simpa using Fin.prod_univ_eq_prod_range (fun i => (1 + C (diagLen n i) * X : ℕ[X])) (2 * n - 1)
  rw [← hrange, hfin]
  classical
  let e : {s : Finset (Fin (2 * n - 1)) // s.card = n} ≃
      {s : Finset (Fin (2 * n - 1)) // s ∈ univ.powersetCard n} :=
    Equiv.subtypeEquivRight fun s => by
      simpa [Finset.mem_powersetCard_univ] using (Iff.rfl (s.card = n))
  rw [Fintype.sum_equiv e
    (fun s : {s : Finset (Fin (2 * n - 1)) // s.card = n} => ∏ d ∈ s.1, diagLen n d.val)
    (fun s : {s : Finset (Fin (2 * n - 1)) // s ∈ univ.powersetCard n} =>
      ∏ d ∈ s.1, diagLen n d.val)
    (fun s => by rfl)]
  exact Finset.sum_coe_sort ((univ : Finset (Fin (2 * n - 1))).powersetCard n)
    (fun t => ∏ d ∈ t, diagLen n d.val)

lemma bishopPick_card (n : ℕ) :
    Nat.card (BishopPick n) =
      (∏ d ∈ range (2 * n - 1), (1 + C (diagLen n d) * X : ℕ[X])).coeff n := by
  unfold BishopPick
  rw [Nat.card_sigma]
  refine Eq.trans ?_ (sum_powerset_diag n)
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Nat.card_pi]
  simp only [Nat.card_fin]
  exact Finset.prod_coe_sort s.1 (fun i => diagLen n i.val)

lemma place_card (n : ℕ) :
    Nat.card (Place n) =
      (∏ d ∈ range (2 * n - 1), (1 + C (diagLen n d) * X : ℕ[X])).coeff n := by
  rw [Nat.card_congr (placeEquiv n), bishopPick_card]

/-! ### Cycles -/

lemma sameCycle_orbit {α : Type*} [Fintype α] [DecidableEq α] (σ : Perm α) (a b : α) :
    orbitRel (zpowers σ) α a b ↔ σ.SameCycle a b := by
  rw [orbitRel_apply, mem_orbit_iff]
  constructor
  · rintro ⟨g, hg⟩
    rw [subgroup_smul_def, Perm.smul_def] at hg
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp g.2
    exact SameCycle.symm ⟨k, by rw [hk]; exact hg⟩
  · intro h
    obtain ⟨k, hk⟩ := h.symm
    refine ⟨⟨σ ^ k, zpow_mem_zpowers σ k⟩, ?_⟩
    rw [subgroup_smul_def, Perm.smul_def]
    exact hk

lemma cycles_eq_quot {α : Type*} [Fintype α] [DecidableEq α] (σ : Perm α) :
    cycles σ = Nat.card (Quotient (orb σ)) := rfl

lemma cycles_pos {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] (σ : Perm α) :
    0 < cycles σ := by
  rw [cycles_eq_quot]
  refine Nat.card_pos_iff.mpr ⟨?_, inferInstance⟩
  obtain ⟨a⟩ := ‹Nonempty α›
  exact ⟨Quotient.mk (orb σ) a⟩

lemma cycles_le {m : ℕ} (σ : Perm (Fin m)) : cycles σ ≤ m := by
  rw [cycles_eq_quot]
  simpa [Nat.card_fin] using
    Nat.card_le_card_of_surjective (Quotient.mk (orb σ)) Quotient.mk_surjective

abbrev up {m : ℕ} (i : Fin m) : Fin (m + 1) := i.castSucc

abbrev down {m : ℕ} (x : Fin (m + 1)) (hx : x ≠ Fin.last m) : Fin m := x.castPred hx

def extendFix {m : ℕ} (τ : Perm (Fin m)) : Perm (Fin (m + 1)) where
  toFun x := if hx : x = Fin.last m then Fin.last m else up (τ (down x hx))
  invFun x := if hx : x = Fin.last m then Fin.last m else up (τ.symm (down x hx))
  left_inv x := by
    by_cases hx : x = Fin.last m
    · simp [hx]
    · have hy : up (τ (down x hx)) ≠ Fin.last m := Fin.castSucc_ne_last _
      simp [hx, hy, up, down, Fin.castPred_castSucc, Fin.castSucc_castPred,
        Equiv.symm_apply_apply]
  right_inv x := by
    by_cases hx : x = Fin.last m
    · simp [hx]
    · have hy : up (τ.symm (down x hx)) ≠ Fin.last m := Fin.castSucc_ne_last _
      simp [hx, hy, up, down, Fin.castPred_castSucc, Fin.castSucc_castPred,
        Equiv.apply_symm_apply]

lemma extendFix_top {m : ℕ} (τ : Perm (Fin m)) :
    extendFix τ (Fin.last m) = Fin.last m := by
  simp [extendFix]

lemma extendFix_up {m : ℕ} (τ : Perm (Fin m)) (i : Fin m) :
    extendFix τ (up i) = up (τ i) := by
  have hne : up i ≠ Fin.last m := Fin.castSucc_ne_last i
  simp [extendFix, hne, up, down, Fin.castPred_castSucc]

lemma extend_pow_up {m : ℕ} (τ : Perm (Fin m)) (k : ℕ) (a : Fin m) :
    ((extendFix τ) ^ k) (up a) = up ((τ ^ k) a) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [_root_.pow_succ', Perm.mul_apply, ih, extendFix_up, _root_.pow_succ', Perm.mul_apply]

lemma extend_symm {m : ℕ} (τ : Perm (Fin m)) :
    (extendFix τ).symm = extendFix τ.symm := by
  ext x
  by_cases hx : x = Fin.last m
  · simp [hx, extendFix]
  · simp [hx, extendFix, Fin.castSucc_ne_last]

lemma extend_zpow_up {m : ℕ} (τ : Perm (Fin m)) (k : ℤ) (a : Fin m) :
    ((extendFix τ) ^ k) (up a) = up ((τ ^ k) a) := by
  cases k with
  | ofNat k =>
    simpa [zpow_ofNat] using extend_pow_up τ k a
  | negSucc k =>
    simp only [zpow_negSucc, ← inv_pow, extend_symm]
    exact extend_pow_up τ.symm (k + 1) a

lemma extend_same_up {m : ℕ} (τ : Perm (Fin m)) (a b : Fin m) :
    (extendFix τ).SameCycle (up a) (up b) ↔ τ.SameCycle a b := by
  constructor
  · rintro ⟨k, hk⟩
    rw [extend_zpow_up] at hk
    exact ⟨k, Fin.castSucc_injective m (by simpa [up] using hk)⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, by rw [extend_zpow_up, hk]⟩

lemma extend_not_top {m : ℕ} (τ : Perm (Fin m)) (a : Fin m) :
    ¬ (extendFix τ).SameCycle (up a) (Fin.last m) := by
  rintro ⟨k, hk⟩
  rw [extend_zpow_up] at hk
  exact Fin.castSucc_ne_last ((τ ^ k) a) (by simpa [up] using hk)

lemma extend_top_class {m : ℕ} (τ : Perm (Fin m)) {a b : Fin (m + 1)}
    (h : (extendFix τ).SameCycle a b) :
    a = Fin.last m ↔ b = Fin.last m := by
  constructor
  · intro ha
    by_contra hb
    have hb' : b = up (down b hb) := (Fin.castSucc_castPred b hb).symm
    rw [ha, hb'] at h
    exact extend_not_top τ (down b hb) h.symm
  · intro hb
    by_contra ha
    have ha' : a = up (down a ha) := (Fin.castSucc_castPred a ha).symm
    rw [hb, ha'] at h
    exact extend_not_top τ (down a ha) h

lemma extend_down_same {m : ℕ} (τ : Perm (Fin m)) {a b : Fin (m + 1)}
    (ha : a ≠ Fin.last m) (hb : b ≠ Fin.last m)
    (h : (extendFix τ).SameCycle a b) :
    τ.SameCycle (down a ha) (down b hb) := by
  have ha' : a = up (down a ha) := (Fin.castSucc_castPred a ha).symm
  have hb' : b = up (down b hb) := (Fin.castSucc_castPred b hb).symm
  rw [ha', hb'] at h
  exact (extend_same_up τ _ _).mp h

def extendTo {m : ℕ} (τ : Perm (Fin m)) :
    Quotient (orb (extendFix τ)) → Quotient (orb τ) ⊕ Unit :=
  Quotient.lift
    (fun x => if hx : x = Fin.last m then Sum.inr ()
      else Sum.inl (Quotient.mk (orb τ) (down x hx)))
    (fun a b h => by
      have hsc : (extendFix τ).SameCycle a b := (sameCycle_orbit _ a b).mp h
      by_cases ha : a = Fin.last m
      · have hb : b = Fin.last m := (extend_top_class τ hsc).mp ha
        simp [ha, hb]
      · have hb : b ≠ Fin.last m := fun hb => ha ((extend_top_class τ hsc).mpr hb)
        simp [ha, hb]
        apply Quotient.sound
        exact (sameCycle_orbit τ _ _).mpr (extend_down_same τ ha hb hsc))

def extendInv {m : ℕ} (τ : Perm (Fin m)) :
    Quotient (orb τ) ⊕ Unit → Quotient (orb (extendFix τ))
  | Sum.inl q =>
      Quotient.lift (fun i => Quotient.mk (orb (extendFix τ)) (up i))
        (fun a b h => by
          apply Quotient.sound
          exact (sameCycle_orbit _ _ _).mpr
            ((extend_same_up τ a b).mpr ((sameCycle_orbit τ a b).mp h))) q
  | Sum.inr _ => Quotient.mk (orb (extendFix τ)) (Fin.last m)

lemma extendTo_top {m : ℕ} (τ : Perm (Fin m)) :
    extendTo τ (Quotient.mk _ (Fin.last m)) = Sum.inr () := by
  simp [extendTo]

lemma extendTo_up {m : ℕ} (τ : Perm (Fin m)) (i : Fin m) :
    extendTo τ (Quotient.mk _ (up i)) = Sum.inl (Quotient.mk _ i) := by
  have hne : up i ≠ Fin.last m := Fin.castSucc_ne_last i
  simp [extendTo, hne, up, down, Fin.castPred_castSucc]

lemma extendInv_up {m : ℕ} (τ : Perm (Fin m)) (i : Fin m) :
    extendInv τ (Sum.inl (Quotient.mk _ i)) = Quotient.mk _ (up i) := by
  simp [extendInv]

def extendQuot {m : ℕ} (τ : Perm (Fin m)) :
    Quotient (orb (extendFix τ)) ≃ Quotient (orb τ) ⊕ Unit where
  toFun := extendTo τ
  invFun := extendInv τ
  left_inv q := by
    refine Quotient.inductionOn q ?_
    intro x
    by_cases hx : x = Fin.last m
    · subst hx
      simp [extendTo_top, extendInv]
    · rw [show x = up (down x hx) from (Fin.castSucc_castPred x hx).symm,
        extendTo_up, extendInv_up]
  right_inv s := by
    cases s with
    | inl q =>
      refine Quotient.inductionOn q ?_
      intro i
      simp [extendInv_up, extendTo_up]
    | inr u =>
      cases u
      simp [extendInv, extendTo_top]

lemma cycles_extendFix {m : ℕ} (τ : Perm (Fin m)) :
    cycles (extendFix τ) = cycles τ + 1 := by
  rw [cycles_eq_quot, cycles_eq_quot, Nat.card_congr (extendQuot τ), Nat.card_sum]
  rw [Nat.card_unique (α := Unit)]

def insertTo {m : ℕ} (τ : Perm (Fin m)) (i : Fin m) (x : Fin (m + 1)) : Fin (m + 1) :=
  if hx : x = Fin.last m then up (τ i)
  else if down x hx = i then Fin.last m
  else up (τ (down x hx))

lemma insertTo_top {m : ℕ} (τ : Perm (Fin m)) (i : Fin m) :
    insertTo τ i (Fin.last m) = up (τ i) := by
  simp [insertTo]

lemma insertTo_up_self {m : ℕ} (τ : Perm (Fin m)) (i : Fin m) :
    insertTo τ i (up i) = Fin.last m := by
  have hne : up i ≠ Fin.last m := Fin.castSucc_ne_last i
  simp [insertTo, hne, up, down, Fin.castPred_castSucc]

lemma insertTo_up_other {m : ℕ} (τ : Perm (Fin m)) (i j : Fin m) (hj : j ≠ i) :
    insertTo τ i (up j) = up (τ j) := by
  have hne : up j ≠ Fin.last m := Fin.castSucc_ne_last j
  simp [insertTo, hne, up, down, Fin.castPred_castSucc, hj]

lemma insertTo_left {m : ℕ} (τ : Perm (Fin m)) (i : Fin m) (x : Fin (m + 1)) :
    insertTo τ.symm (τ i) (insertTo τ i x) = x := by
  by_cases hx : x = Fin.last m
  · simp [hx, insertTo_top, insertTo_up_self, Equiv.symm_apply_apply]
  · by_cases hxi : down x hx = i
    · have hxeq : x = up i := by
        simpa [up] using (Fin.castPred_eq_iff_eq_castSucc x hx i).mp hxi
      simp [hxeq, insertTo_up_self, insertTo_top, Equiv.symm_apply_apply]
    · have hxeq : x = up (down x hx) := (Fin.castSucc_castPred x hx).symm
      have hne : down x hx ≠ i := hxi
      rw [hxeq, insertTo_up_other τ i _ hne]
      have hτ : τ (down x hx) ≠ τ i := fun h => hne ((Equiv.injective τ) h)
      rw [insertTo_up_other τ.symm (τ i) _ hτ, Equiv.symm_apply_apply]

def insert {m : ℕ} (τ : Perm (Fin m)) (i : Fin m) : Perm (Fin (m + 1)) where
  toFun := insertTo τ i
  invFun := insertTo τ.symm (τ i)
  left_inv := insertTo_left τ i
  right_inv x := by simpa [Equiv.symm_apply_apply] using insertTo_left τ.symm (τ i) x

lemma insert_apply {m : ℕ} (τ : Perm (Fin m)) (i : Fin m) (x : Fin (m + 1)) :
    insert τ i x = insertTo τ i x := rfl

def erase {m : ℕ} (i : Fin m) (x : Fin (m + 1)) : Fin m :=
  if hx : x = Fin.last m then i else down x hx

lemma erase_one_step {m : ℕ} (τ : Perm (Fin m)) (i : Fin m) (x : Fin (m + 1)) :
    τ.SameCycle (erase i x) (erase i (insert τ i x)) := by
  rw [insert_apply]
  by_cases hx : x = Fin.last m
  · subst hx
    have hne : up (τ i) ≠ Fin.last m := Fin.castSucc_ne_last _
    have h1 : erase i (Fin.last m) = i := by simp [erase]
    have h2 : erase i (insertTo τ i (Fin.last m)) = τ i := by
      rw [insertTo_top]
      simp [erase, hne, down, up, Fin.castPred_castSucc]
    rw [h1, h2]
    exact ⟨1, by rw [_root_.zpow_one]⟩
  · by_cases hxi : down x hx = i
    · have h1 : erase i x = i := by simp [erase, hx, hxi]
      have h2 : erase i (insertTo τ i x) = i := by simp [erase, hx, insertTo, hxi]
      rw [h1, h2]
    · have hne : up (τ (down x hx)) ≠ Fin.last m := Fin.castSucc_ne_last _
      have h1 : erase i x = down x hx := by simp [erase, hx]
      have h2 : erase i (insertTo τ i x) = τ (down x hx) := by
        simp [erase, hx, insertTo, hxi, hne, down, up, Fin.castPred_castSucc]
      rw [h1, h2]
      exact ⟨1, by rw [_root_.zpow_one]⟩

lemma erase_pow {m : ℕ} (τ : Perm (Fin m)) (i : Fin m) (k : ℕ) (x : Fin (m + 1)) :
    τ.SameCycle (erase i x) (erase i (((insert τ i) ^ k) x)) := by
  induction k with
  | zero => exact SameCycle.refl _ _
  | succ k ih =>
    rw [_root_.pow_succ', Perm.mul_apply]
    exact ih.trans (erase_one_step τ i _)

lemma insert_same_erase {m : ℕ} (τ : Perm (Fin m)) (i : Fin m) {x y : Fin (m + 1)}
    (h : (insert τ i).SameCycle x y) :
    τ.SameCycle (erase i x) (erase i y) := by
  obtain ⟨k, hk⟩ := h.exists_nat_pow_eq
  rw [← hk]
  exact erase_pow τ i k x

lemma insert_link {m : ℕ} (τ : Perm (Fin m)) (i j : Fin m) :
    (insert τ i).SameCycle (up j) (up (τ j)) := by
  by_cases hj : j = i
  · subst hj
    refine ⟨(2 : ℤ), ?_⟩
    simp [zpow_ofNat, pow_two, Perm.mul_apply, insert_apply, insertTo_up_self, insertTo_top]
  · refine ⟨(1 : ℤ), ?_⟩
    simp [zpow_one, insert_apply, insertTo_up_other τ i j hj]

lemma insert_pow_link {m : ℕ} (τ : Perm (Fin m)) (i : Fin m) (k : ℕ) (j : Fin m) :
    (insert τ i).SameCycle (up j) (up ((τ ^ k) j)) := by
  induction k with
  | zero => exact SameCycle.refl _ _
  | succ k ih =>
    apply ih.trans
    simpa [_root_.pow_succ', Perm.mul_apply] using insert_link τ i ((τ ^ k) j)

lemma insert_same_up {m : ℕ} (τ : Perm (Fin m)) (i a b : Fin m)
    (h : τ.SameCycle a b) : (insert τ i).SameCycle (up a) (up b) := by
  obtain ⟨k, hk⟩ := h.exists_nat_pow_eq
  rw [← hk]
  exact insert_pow_link τ i k a

lemma insert_erase_same {m : ℕ} (τ : Perm (Fin m)) (i : Fin m) (x : Fin (m + 1)) :
    (insert τ i).SameCycle x (up (erase i x)) := by
  by_cases hx : x = Fin.last m
  · rw [hx]
    simp [erase]
    exact (show (insert τ i).SameCycle (up i) (Fin.last m) from
      ⟨1, by simp [zpow_one, insert_apply, insertTo_up_self]⟩).symm
  · simp [erase, hx, down, Fin.castSucc_castPred]
    exact SameCycle.refl _ _

def eraseTo {m : ℕ} (τ : Perm (Fin m)) (i : Fin m) :
    Quotient (orb (insert τ i)) → Quotient (orb τ) :=
  Quotient.lift (fun x => Quotient.mk (orb τ) (erase i x))
    (fun a b h => by
      apply Quotient.sound
      exact (sameCycle_orbit τ _ _).mpr
        (insert_same_erase τ i ((sameCycle_orbit _ a b).mp h)))

def eraseInv {m : ℕ} (τ : Perm (Fin m)) (i : Fin m) :
    Quotient (orb τ) → Quotient (orb (insert τ i)) :=
  Quotient.lift (fun j => Quotient.mk (orb (insert τ i)) (up j))
    (fun a b h => by
      apply Quotient.sound
      exact (sameCycle_orbit _ _ _).mpr
        (insert_same_up τ i a b ((sameCycle_orbit τ a b).mp h)))

def insertQuot {m : ℕ} (τ : Perm (Fin m)) (i : Fin m) :
    Quotient (orb (insert τ i)) ≃ Quotient (orb τ) where
  toFun := eraseTo τ i
  invFun := eraseInv τ i
  left_inv q := by
    refine Quotient.inductionOn q ?_
    intro x
    have hsame := insert_erase_same τ i x
    simp [eraseTo, eraseInv]
    apply Quotient.sound
    exact (sameCycle_orbit _ _ _).mpr hsame.symm
  right_inv q := by
    refine Quotient.inductionOn q ?_
    intro j
    simp [eraseTo, eraseInv, erase, Fin.castSucc_ne_last, down, up, Fin.castPred_castSucc]

lemma cycles_insert {m : ℕ} (τ : Perm (Fin m)) (i : Fin m) :
    cycles (insert τ i) = cycles τ := by
  rw [cycles_eq_quot, cycles_eq_quot, Nat.card_congr (insertQuot τ i)]

def restrictTo {m : ℕ} (σ : Perm (Fin (m + 1))) (hσ : σ (Fin.last m) = Fin.last m)
    (j : Fin m) : Fin m :=
  down (σ (up j)) (by
    intro h
    exact Fin.castSucc_ne_last j (σ.injective (h.trans hσ.symm)))

lemma symm_fixes {m : ℕ} (σ : Perm (Fin (m + 1))) (hσ : σ (Fin.last m) = Fin.last m) :
    σ.symm (Fin.last m) = Fin.last m := by
  simpa using (congrArg σ.symm hσ).symm

def restrict {m : ℕ} (σ : Perm (Fin (m + 1))) (hσ : σ (Fin.last m) = Fin.last m) :
    Perm (Fin m) where
  toFun := restrictTo σ hσ
  invFun := restrictTo σ.symm (symm_fixes σ hσ)
  left_inv j := by
    simp [restrictTo, up, down, Fin.castPred_castSucc, Fin.castSucc_castPred,
      Equiv.symm_apply_apply]
  right_inv j := by
    simp [restrictTo, up, down, Fin.castPred_castSucc, Fin.castSucc_castPred,
      Equiv.apply_symm_apply]

lemma restrict_extend {m : ℕ} (τ : Perm (Fin m)) :
    restrict (extendFix τ) (extendFix_top τ) = τ := by
  ext j
  simp [restrict, restrictTo, extendFix_up, up, down, Fin.castPred_castSucc]

lemma extend_restrict {m : ℕ} (σ : Perm (Fin (m + 1)))
    (hσ : σ (Fin.last m) = Fin.last m) :
    extendFix (restrict σ hσ) = σ := by
  ext x
  by_cases hx : x = Fin.last m
  · simp [hx, extendFix_top, hσ]
  · simp [extendFix, hx, restrict, restrictTo, Fin.castSucc_castPred]

lemma symm_moved {m : ℕ} (σ : Perm (Fin (m + 1))) (hσ : σ (Fin.last m) ≠ Fin.last m) :
    σ.symm (Fin.last m) ≠ Fin.last m := by
  intro h
  exact hσ (by simpa using (congrArg σ h).symm)

def movedPred {m : ℕ} (σ : Perm (Fin (m + 1))) (hσ : σ (Fin.last m) ≠ Fin.last m) : Fin m :=
  down (σ.symm (Fin.last m)) (symm_moved σ hσ)

def deletedTo {m : ℕ} (σ : Perm (Fin (m + 1))) (hσ : σ (Fin.last m) ≠ Fin.last m)
    (j : Fin m) : Fin m :=
  if hj : σ (up j) = Fin.last m then down (σ (Fin.last m)) hσ
  else down (σ (up j)) hj

lemma deletedTo_left {m : ℕ} (σ : Perm (Fin (m + 1))) (hσ : σ (Fin.last m) ≠ Fin.last m)
    (j : Fin m) :
    deletedTo σ.symm (symm_moved σ hσ) (deletedTo σ hσ j) = j := by
  by_cases hj : σ (up j) = Fin.last m
  · have hpred : σ.symm (Fin.last m) = up j := by
      simpa using (congrArg σ.symm hj).symm
    have hp : σ.symm (up (down (σ (Fin.last m)) hσ)) = Fin.last m := by
      simp [up, down, Fin.castSucc_castPred, Equiv.symm_apply_apply]
    simp [deletedTo, hj, hp, hpred, up, down, Fin.castPred_castSucc]
  · have hp : σ.symm (up (down (σ (up j)) hj)) = up j := by
      simp [up, down, Fin.castSucc_castPred, Equiv.symm_apply_apply]
    have hne : up j ≠ Fin.last m := Fin.castSucc_ne_last j
    simp [deletedTo, hj, hp, hne, up, down, Fin.castPred_castSucc]

lemma deletedTo_right {m : ℕ} (σ : Perm (Fin (m + 1))) (hσ : σ (Fin.last m) ≠ Fin.last m)
    (j : Fin m) :
    deletedTo σ hσ (deletedTo σ.symm (symm_moved σ hσ) j) = j := by
  have hσ' : σ.symm.symm (Fin.last m) ≠ Fin.last m := by simpa using hσ
  have h := deletedTo_left σ.symm (symm_moved σ hσ) j
  simpa [Equiv.symm_symm, hσ'] using h

def deleted {m : ℕ} (σ : Perm (Fin (m + 1))) (hσ : σ (Fin.last m) ≠ Fin.last m) :
    Perm (Fin m) where
  toFun := deletedTo σ hσ
  invFun := deletedTo σ.symm (symm_moved σ hσ)
  left_inv := deletedTo_left σ hσ
  right_inv := deletedTo_right σ hσ

lemma deleted_apply {m : ℕ} (σ : Perm (Fin (m + 1))) (hσ : σ (Fin.last m) ≠ Fin.last m)
    (j : Fin m) : deleted σ hσ j = deletedTo σ hσ j := rfl

lemma deletedTo_ne {m : ℕ} (σ : Perm (Fin (m + 1))) (hσ : σ (Fin.last m) ≠ Fin.last m)
    (j : Fin m) (hj : σ (up j) ≠ Fin.last m) :
    deletedTo σ hσ j = down (σ (up j)) hj := by
  unfold deletedTo
  rw [dif_neg hj]

lemma pred_insert {m : ℕ} (τ : Perm (Fin m)) (i : Fin m) :
    movedPred (insert τ i) (by
      rw [insert_apply, insertTo_top]
      exact Fin.castSucc_ne_last _) = i := by
  have happ : insert τ i (up i) = Fin.last m := by
    rw [insert_apply]
    exact insertTo_up_self τ i
  have h : (insert τ i).symm (Fin.last m) = up i := by
    simpa using (congrArg (insert τ i).symm happ).symm
  simp [movedPred, h, up, down, Fin.castPred_castSucc]

lemma deleted_insert {m : ℕ} (τ : Perm (Fin m)) (i : Fin m) :
    deleted (insert τ i) (by
      rw [insert_apply, insertTo_top]
      exact Fin.castSucc_ne_last _) = τ := by
  ext j
  by_cases hj : j = i
  · subst hj
    simp [deleted, deletedTo, insert_apply, insertTo_up_self, insertTo_top, up, down,
      Fin.castPred_castSucc]
  · have hne : insert τ i (up j) ≠ Fin.last m := by
      rw [insert_apply, insertTo_up_other τ i j hj]
      exact Fin.castSucc_ne_last _
    simp [deleted, deletedTo, hne, insert_apply, insertTo_up_other τ i j hj, up, down,
      Fin.castPred_castSucc]

lemma insert_deleted {m : ℕ} (σ : Perm (Fin (m + 1))) (hσ : σ (Fin.last m) ≠ Fin.last m) :
    insert (deleted σ hσ) (movedPred σ hσ) = σ := by
  apply Equiv.ext
  intro x
  by_cases hx : x = Fin.last m
  · subst hx
    rw [insert_apply, insertTo_top]
    have hpred : up (movedPred σ hσ) = σ.symm (Fin.last m) := by
      simp [movedPred, up, down, Fin.castSucc_castPred]
    have hback : σ (up (movedPred σ hσ)) = Fin.last m := by
      simpa using congrArg σ hpred
    have hdel : deleted σ hσ (movedPred σ hσ) = down (σ (Fin.last m)) hσ := by
      simp [deleted, deletedTo, hback]
    rw [hdel]
    exact Fin.castSucc_castPred (σ (Fin.last m)) hσ
  · by_cases hxi : down x hx = movedPred σ hσ
    · have hxeq : x = up (movedPred σ hσ) := by
        simpa [up] using (Fin.castPred_eq_iff_eq_castSucc x hx _).mp hxi
      rw [hxeq, insert_apply, insertTo_up_self]
      have hpred : σ.symm (Fin.last m) = up (movedPred σ hσ) := by
        simp [movedPred, up, down, Fin.castSucc_castPred]
      have h := congrArg σ hpred
      rw [Equiv.apply_symm_apply] at h
      exact h
    · have hxeq : x = up (down x hx) := (Fin.castSucc_castPred x hx).symm
      have hne : down x hx ≠ movedPred σ hσ := hxi
      rw [hxeq, insert_apply, insertTo_up_other _ _ _ hne]
      have hσj : σ (up (down x hx)) ≠ Fin.last m := by
        intro h
        have hsym : σ.symm (Fin.last m) = up (down x hx) := by
          simpa using (congrArg σ.symm h).symm
        have heq : down x hx = movedPred σ hσ := by
          apply Fin.ext
          simp [movedPred, down, up, Fin.coe_castPred, hsym]
        exact hne heq
      rw [deleted_apply, deletedTo_ne σ hσ (down x hx) hσj]
      exact Fin.castSucc_castPred (σ (up (down x hx))) hσj

def Cyc (m k : ℕ) : Type := {σ : Perm (Fin m) // cycles σ = k}

lemma perm_fin_zero_cycles (σ : Perm (Fin 0)) : cycles σ = 0 := by
  rw [cycles_eq_quot]
  refine Nat.card_eq_zero.mpr (Or.inl ⟨fun q => ?_⟩)
  exact Quotient.recOnSubsingleton q (fun x => Fin.elim0 x)

lemma cyc_zero_zero : Nat.card (Cyc 0 0) = 1 := by
  have hcard : Nat.card (Perm (Fin 0)) = 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    simp
  let e : Cyc 0 0 ≃ Perm (Fin 0) :=
    { toFun := fun σ => σ.1
      invFun := fun σ => ⟨σ, perm_fin_zero_cycles σ⟩
      left_inv := fun σ => Subtype.ext rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, hcard]

lemma cyc_zero_succ (k : ℕ) : Nat.card (Cyc 0 (k + 1)) = 0 := by
  rw [Nat.card_eq_zero]
  refine Or.inl ⟨fun σ => ?_⟩
  have h0 := perm_fin_zero_cycles σ.1
  have h1 := σ.2
  omega

lemma cyc_succ_zero (m : ℕ) : Nat.card (Cyc (m + 1) 0) = 0 := by
  rw [Nat.card_eq_zero]
  refine Or.inl ⟨fun σ => ?_⟩
  have hpos := cycles_pos σ.1
  have h0 := σ.2
  omega

def cycTo {m k : ℕ} (σ : Cyc (m + 1) (k + 1)) :
    Cyc m k ⊕ (Fin m × Cyc m (k + 1)) :=
  if h : σ.1 (Fin.last m) = Fin.last m then
    Sum.inl ⟨restrict σ.1 h, by
      have he := cycles_extendFix (restrict σ.1 h)
      rw [extend_restrict σ.1 h] at he
      have hk := σ.2
      omega⟩
  else
    Sum.inr ⟨movedPred σ.1 h, ⟨deleted σ.1 h, by
      have he := cycles_insert (deleted σ.1 h) (movedPred σ.1 h)
      rw [insert_deleted σ.1 h] at he
      have hk := σ.2
      omega⟩⟩

def cycInv {m k : ℕ} :
    Cyc m k ⊕ (Fin m × Cyc m (k + 1)) → Cyc (m + 1) (k + 1)
  | Sum.inl τ => ⟨extendFix τ.1, by
      have he := cycles_extendFix τ.1
      have hk := τ.2
      omega⟩
  | Sum.inr p => ⟨insert p.2.1 p.1, by
      have he := cycles_insert p.2.1 p.1
      have hk := p.2.2
      omega⟩

def cycSplit {m k : ℕ} : Cyc (m + 1) (k + 1) ≃ Cyc m k ⊕ (Fin m × Cyc m (k + 1)) where
  toFun := cycTo
  invFun := cycInv
  left_inv σ := by
    apply Subtype.ext
    by_cases h : σ.1 (Fin.last m) = Fin.last m
    · simp only [cycTo, cycInv, h, dif_pos h]
      exact extend_restrict σ.1 h
    · simp only [cycTo, cycInv, h, dif_neg h]
      exact insert_deleted σ.1 h
  right_inv s := by
    cases s with
    | inl τ =>
      unfold cycInv cycTo
      rw [dif_pos (extendFix_top τ.1)]
      exact congrArg Sum.inl (Subtype.ext (restrict_extend τ.1))
    | inr p =>
      unfold cycInv cycTo
      have hne : insert p.2.1 p.1 (Fin.last m) ≠ Fin.last m := by
        rw [insert_apply, insertTo_top]
        exact Fin.castSucc_ne_last _
      rw [dif_neg hne]
      refine congrArg Sum.inr (Prod.ext (pred_insert p.2.1 p.1) (Subtype.ext ?_))
      exact deleted_insert p.2.1 p.1

lemma cyc_finite (m k : ℕ) : Finite (Cyc m k) :=
  Finite.of_injective (fun σ : Cyc m k => σ.1) fun a b h => Subtype.ext h

lemma cyc_rec (m k : ℕ) :
    Nat.card (Cyc (m + 1) (k + 1)) =
      Nat.card (Cyc m k) + m * Nat.card (Cyc m (k + 1)) := by
  letI := cyc_finite m k
  letI := cyc_finite m (k + 1)
  rw [Nat.card_congr (cycSplit (m := m) (k := k)), Nat.card_sum, Nat.card_prod, Nat.card_fin]

lemma cycCard_eq (m k : ℕ) : Nat.card (Cyc m k) = stirlingFirst m k := by
  induction m generalizing k with
  | zero =>
    cases k with
    | zero =>
      simpa using cyc_zero_zero
    | succ k =>
      rw [cyc_zero_succ, stirlingFirst_zero_succ]
  | succ m ih =>
    cases k with
    | zero =>
      rw [cyc_succ_zero, stirlingFirst_succ_zero]
    | succ k =>
      rw [cyc_rec m k, ih k, ih (k + 1), stirlingFirst_succ_succ]
      ac_rfl

/-! ### Parity -/

def evenEmb {n : ℕ} (i : Fin (n + 1)) : Fin (2 * n + 1) :=
  ⟨2 * i.val, by have := i.isLt; omega⟩

def oddEmb {n : ℕ} (j : Fin n) : Fin (2 * n + 1) :=
  ⟨2 * j.val + 1, by have := j.isLt; omega⟩

lemma evenEmb_mod {n : ℕ} (i : Fin (n + 1)) : (evenEmb i).val % 2 = 0 := by
  simp [evenEmb, Nat.mul_mod_right]

lemma oddEmb_mod {n : ℕ} (j : Fin n) : (oddEmb j).val % 2 = 1 := by
  simp [oddEmb, Nat.add_mod, Nat.mul_mod_right]

def evenIdx {n : ℕ} (x : Fin (2 * n + 1)) (hx : x.val % 2 = 0) : Fin (n + 1) :=
  ⟨x.val / 2, by
    have hxlt := x.isLt
    have hmod : x.val % 2 + 2 * (x.val / 2) = x.val := Nat.mod_add_div x.val 2
    omega⟩

def oddIdx {n : ℕ} (x : Fin (2 * n + 1)) (hx : x.val % 2 = 1) : Fin n :=
  ⟨x.val / 2, by
    have hxlt := x.isLt
    have hmod : x.val % 2 + 2 * (x.val / 2) = x.val := Nat.mod_add_div x.val 2
    omega⟩

lemma mod_one_of_ne {n : ℕ} {x : Fin (2 * n + 1)} (hx : x.val % 2 ≠ 0) : x.val % 2 = 1 := by
  cases Nat.mod_two_eq_zero_or_one x.val with
  | inl h => exact (hx h).elim
  | inr h => exact h

lemma evenIdx_evenEmb {n : ℕ} (i : Fin (n + 1)) (hx : (evenEmb i).val % 2 = 0) :
    evenIdx (evenEmb i) hx = i := by
  apply Fin.ext
  simp [evenIdx, evenEmb]

lemma oddIdx_oddEmb {n : ℕ} (j : Fin n) (hx : (oddEmb j).val % 2 = 1) :
    oddIdx (oddEmb j) hx = j := by
  apply Fin.ext
  simp [oddIdx, oddEmb]
  omega

lemma evenEmb_evenIdx {n : ℕ} (x : Fin (2 * n + 1)) (hx : x.val % 2 = 0) :
    evenEmb (evenIdx x hx) = x := by
  apply Fin.ext
  simp [evenEmb, evenIdx]
  exact Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hx)

lemma oddEmb_oddIdx {n : ℕ} (x : Fin (2 * n + 1)) (hx : x.val % 2 = 1) :
    oddEmb (oddIdx x hx) = x := by
  apply Fin.ext
  simp [oddEmb, oddIdx]
  have hmod : x.val % 2 + 2 * (x.val / 2) = x.val := Nat.mod_add_div x.val 2
  omega

def combineTo {n : ℕ} (σe : Perm (Fin (n + 1))) (σo : Perm (Fin n))
    (x : Fin (2 * n + 1)) : Fin (2 * n + 1) :=
  if hx : x.val % 2 = 0 then evenEmb (σe (evenIdx x hx))
  else oddEmb (σo (oddIdx x (mod_one_of_ne hx)))

lemma combineTo_even {n : ℕ} (σe : Perm (Fin (n + 1))) (σo : Perm (Fin n)) (i : Fin (n + 1)) :
    combineTo σe σo (evenEmb i) = evenEmb (σe i) := by
  have hx : (evenEmb i).val % 2 = 0 := evenEmb_mod i
  simp [combineTo, hx, evenIdx_evenEmb]

lemma combineTo_odd {n : ℕ} (σe : Perm (Fin (n + 1))) (σo : Perm (Fin n)) (j : Fin n) :
    combineTo σe σo (oddEmb j) = oddEmb (σo j) := by
  have hx : (oddEmb j).val % 2 ≠ 0 := by simp [oddEmb_mod]
  simp [combineTo, hx, oddIdx_oddEmb]

def combine {n : ℕ} (σe : Perm (Fin (n + 1))) (σo : Perm (Fin n)) :
    Perm (Fin (2 * n + 1)) where
  toFun := combineTo σe σo
  invFun := combineTo σe.symm σo.symm
  left_inv x := by
    by_cases hx : x.val % 2 = 0
    · rw [show combineTo σe σo x = evenEmb (σe (evenIdx x hx)) by simp [combineTo, hx]]
      rw [combineTo_even, Equiv.symm_apply_apply, evenEmb_evenIdx]
    · have ho : x.val % 2 = 1 := mod_one_of_ne hx
      rw [show combineTo σe σo x = oddEmb (σo (oddIdx x ho)) by simp [combineTo, hx]]
      rw [combineTo_odd, Equiv.symm_apply_apply, oddEmb_oddIdx]
  right_inv x := by
    by_cases hx : x.val % 2 = 0
    · rw [show combineTo σe.symm σo.symm x = evenEmb (σe.symm (evenIdx x hx)) by simp [combineTo, hx]]
      rw [combineTo_even, Equiv.apply_symm_apply, evenEmb_evenIdx]
    · have ho : x.val % 2 = 1 := mod_one_of_ne hx
      rw [show combineTo σe.symm σo.symm x = oddEmb (σo.symm (oddIdx x ho)) by simp [combineTo, hx]]
      rw [combineTo_odd, Equiv.apply_symm_apply, oddEmb_oddIdx]

lemma combine_apply {n : ℕ} (σe : Perm (Fin (n + 1))) (σo : Perm (Fin n))
    (x : Fin (2 * n + 1)) : combine σe σo x = combineTo σe σo x := rfl

lemma combine_keeps {n : ℕ} (σe : Perm (Fin (n + 1))) (σo : Perm (Fin n)) :
    keeps n (combine σe σo) := by
  intro x
  by_cases hx : x.val % 2 = 0
  · rw [combine_apply, show combineTo σe σo x = evenEmb (σe (evenIdx x hx)) by simp [combineTo, hx]]
    simp [evenEmb_mod, hx]
  · have ho : x.val % 2 = 1 := mod_one_of_ne hx
    rw [combine_apply, show combineTo σe σo x = oddEmb (σo (oddIdx x ho)) by simp [combineTo, hx]]
    simp [oddEmb_mod, ho]

lemma keeps_symm {n : ℕ} {σ : Perm (Fin (2 * n + 1))} (hσ : keeps n σ) : keeps n σ.symm := by
  intro i
  have h := hσ (σ.symm i)
  simpa using h.symm

lemma keeps_pow {n : ℕ} {σ : Perm (Fin (2 * n + 1))} (hσ : keeps n σ) (k : ℕ)
    (x : Fin (2 * n + 1)) : ((σ ^ k) x).val % 2 = x.val % 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [_root_.pow_succ', Perm.mul_apply, hσ, ih]

lemma keeps_zpow {n : ℕ} {σ : Perm (Fin (2 * n + 1))} (hσ : keeps n σ) (k : ℤ)
    (x : Fin (2 * n + 1)) : ((σ ^ k) x).val % 2 = x.val % 2 := by
  cases k with
  | ofNat k =>
    simpa [zpow_ofNat] using keeps_pow hσ k x
  | negSucc k =>
    simp only [zpow_negSucc, ← inv_pow]
    exact keeps_pow (keeps_symm hσ) (k + 1) x

lemma combine_symm {n : ℕ} (σe : Perm (Fin (n + 1))) (σo : Perm (Fin n)) :
    (combine σe σo).symm = combine σe.symm σo.symm := by
  ext x
  rfl

lemma combine_pow_even {n : ℕ} (σe : Perm (Fin (n + 1))) (σo : Perm (Fin n)) (k : ℕ)
    (i : Fin (n + 1)) :
    ((combine σe σo) ^ k) (evenEmb i) = evenEmb ((σe ^ k) i) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [_root_.pow_succ', Perm.mul_apply, ih, combine_apply, combineTo_even, _root_.pow_succ',
      Perm.mul_apply]

lemma combine_pow_odd {n : ℕ} (σe : Perm (Fin (n + 1))) (σo : Perm (Fin n)) (k : ℕ)
    (j : Fin n) :
    ((combine σe σo) ^ k) (oddEmb j) = oddEmb ((σo ^ k) j) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [_root_.pow_succ', Perm.mul_apply, ih, combine_apply, combineTo_odd, _root_.pow_succ',
      Perm.mul_apply]

lemma combine_zpow_even {n : ℕ} (σe : Perm (Fin (n + 1))) (σo : Perm (Fin n)) (k : ℤ)
    (i : Fin (n + 1)) :
    ((combine σe σo) ^ k) (evenEmb i) = evenEmb ((σe ^ k) i) := by
  cases k with
  | ofNat k =>
    simpa [zpow_ofNat] using combine_pow_even σe σo k i
  | negSucc k =>
    simp only [zpow_negSucc, ← inv_pow]
    exact combine_pow_even σe.symm σo.symm (k + 1) i

lemma combine_zpow_odd {n : ℕ} (σe : Perm (Fin (n + 1))) (σo : Perm (Fin n)) (k : ℤ)
    (j : Fin n) :
    ((combine σe σo) ^ k) (oddEmb j) = oddEmb ((σo ^ k) j) := by
  cases k with
  | ofNat k =>
    simpa [zpow_ofNat] using combine_pow_odd σe σo k j
  | negSucc k =>
    simp only [zpow_negSucc, ← inv_pow]
    exact combine_pow_odd σe.symm σo.symm (k + 1) j

lemma combine_same_even {n : ℕ} (σe : Perm (Fin (n + 1))) (σo : Perm (Fin n))
    (a b : Fin (n + 1)) :
    (combine σe σo).SameCycle (evenEmb a) (evenEmb b) ↔ σe.SameCycle a b := by
  constructor
  · rintro ⟨k, hk⟩
    rw [combine_zpow_even] at hk
    refine ⟨k, ?_⟩
    apply Fin.ext
    have hval := congrArg Fin.val hk
    simpa [evenEmb] using hval
  · rintro ⟨k, hk⟩
    exact ⟨k, by rw [combine_zpow_even, hk]⟩

lemma combine_same_odd {n : ℕ} (σe : Perm (Fin (n + 1))) (σo : Perm (Fin n)) (a b : Fin n) :
    (combine σe σo).SameCycle (oddEmb a) (oddEmb b) ↔ σo.SameCycle a b := by
  constructor
  · rintro ⟨k, hk⟩
    rw [combine_zpow_odd] at hk
    refine ⟨k, ?_⟩
    apply Fin.ext
    have hval := congrArg Fin.val hk
    simp [oddEmb] at hval
    omega
  · rintro ⟨k, hk⟩
    exact ⟨k, by rw [combine_zpow_odd, hk]⟩

lemma combine_cross {n : ℕ} (σe : Perm (Fin (n + 1))) (σo : Perm (Fin n))
    (i : Fin (n + 1)) (j : Fin n) :
    ¬ (combine σe σo).SameCycle (evenEmb i) (oddEmb j) := by
  intro h
  obtain ⟨k, hk⟩ := h
  have hp := keeps_zpow (combine_keeps σe σo) k (evenEmb i)
  rw [hk] at hp
  simp [evenEmb_mod, oddEmb_mod] at hp

def evenTo {n : ℕ} (σ : Perm (Fin (2 * n + 1))) (hσ : keeps n σ) (i : Fin (n + 1)) :
    Fin (n + 1) :=
  evenIdx (σ (evenEmb i)) (by
    have h := hσ (evenEmb i)
    simpa [evenEmb_mod] using h)

def oddTo {n : ℕ} (σ : Perm (Fin (2 * n + 1))) (hσ : keeps n σ) (j : Fin n) : Fin n :=
  oddIdx (σ (oddEmb j)) (by
    have h := hσ (oddEmb j)
    simpa [oddEmb_mod] using h)

lemma evenTo_val {n : ℕ} (σ : Perm (Fin (2 * n + 1))) (hσ : keeps n σ) (i : Fin (n + 1)) :
    (evenTo σ hσ i).val = (σ (evenEmb i)).val / 2 := by
  simp [evenTo, evenIdx]

def evenPart {n : ℕ} (σ : Perm (Fin (2 * n + 1))) (hσ : keeps n σ) : Perm (Fin (n + 1)) where
  toFun := evenTo σ hσ
  invFun := evenTo σ.symm (keeps_symm hσ)
  left_inv i := by
    apply Fin.ext
    have hx : (σ (evenEmb i)).val % 2 = 0 := by
      simpa [evenEmb_mod] using hσ (evenEmb i)
    have he : evenTo σ hσ i = evenIdx (σ (evenEmb i)) hx := by
      apply Fin.ext
      simp [evenTo, evenIdx]
    rw [evenTo_val, he, evenEmb_evenIdx, Equiv.symm_apply_apply]
    simp [evenEmb]
  right_inv i := by
    apply Fin.ext
    have hx : (σ.symm (evenEmb i)).val % 2 = 0 := by
      simpa [evenEmb_mod] using keeps_symm hσ (evenEmb i)
    have he : evenTo σ.symm (keeps_symm hσ) i = evenIdx (σ.symm (evenEmb i)) hx := by
      apply Fin.ext
      simp [evenTo, evenIdx]
    rw [evenTo_val, he, evenEmb_evenIdx, Equiv.apply_symm_apply]
    simp [evenEmb]

lemma oddTo_val {n : ℕ} (σ : Perm (Fin (2 * n + 1))) (hσ : keeps n σ) (j : Fin n) :
    (oddTo σ hσ j).val = (σ (oddEmb j)).val / 2 := by
  simp [oddTo, oddIdx]

def oddPart {n : ℕ} (σ : Perm (Fin (2 * n + 1))) (hσ : keeps n σ) : Perm (Fin n) where
  toFun := oddTo σ hσ
  invFun := oddTo σ.symm (keeps_symm hσ)
  left_inv j := by
    apply Fin.ext
    have hx : (σ (oddEmb j)).val % 2 = 1 := by
      simpa [oddEmb_mod] using hσ (oddEmb j)
    have he : oddTo σ hσ j = oddIdx (σ (oddEmb j)) hx := by
      apply Fin.ext
      simp [oddTo, oddIdx]
    rw [oddTo_val, he, oddEmb_oddIdx, Equiv.symm_apply_apply]
    simp [oddEmb]
    omega
  right_inv j := by
    apply Fin.ext
    have hx : (σ.symm (oddEmb j)).val % 2 = 1 := by
      simpa [oddEmb_mod] using keeps_symm hσ (oddEmb j)
    have he : oddTo σ.symm (keeps_symm hσ) j = oddIdx (σ.symm (oddEmb j)) hx := by
      apply Fin.ext
      simp [oddTo, oddIdx]
    rw [oddTo_val, he, oddEmb_oddIdx, Equiv.apply_symm_apply]
    simp [oddEmb]
    omega

lemma evenPart_combine {n : ℕ} (σe : Perm (Fin (n + 1))) (σo : Perm (Fin n)) :
    evenPart (combine σe σo) (combine_keeps σe σo) = σe := by
  apply Equiv.ext
  intro i
  change evenTo (combine σe σo) (combine_keeps σe σo) i = σe i
  have he : evenTo (combine σe σo) (combine_keeps σe σo) i =
      evenIdx (evenEmb (σe i)) (evenEmb_mod (σe i)) := by
    apply Fin.ext
    simp [evenTo, evenIdx, combine_apply, combineTo_even]
  rw [he]
  exact evenIdx_evenEmb (σe i) (evenEmb_mod (σe i))

lemma oddPart_combine {n : ℕ} (σe : Perm (Fin (n + 1))) (σo : Perm (Fin n)) :
    oddPart (combine σe σo) (combine_keeps σe σo) = σo := by
  apply Equiv.ext
  intro j
  change oddTo (combine σe σo) (combine_keeps σe σo) j = σo j
  have he : oddTo (combine σe σo) (combine_keeps σe σo) j =
      oddIdx (oddEmb (σo j)) (oddEmb_mod (σo j)) := by
    apply Fin.ext
    simp [oddTo, oddIdx, combine_apply, combineTo_odd]
  rw [he]
  exact oddIdx_oddEmb (σo j) (oddEmb_mod (σo j))

lemma recombine {n : ℕ} (σ : Perm (Fin (2 * n + 1))) (hσ : keeps n σ) :
    combine (evenPart σ hσ) (oddPart σ hσ) = σ := by
  apply Equiv.ext
  intro x
  rw [combine_apply]
  by_cases hx : x.val % 2 = 0
  · have hto : combineTo (evenPart σ hσ) (oddPart σ hσ) x =
        evenEmb ((evenPart σ hσ) (evenIdx x hx)) := by
      simp [combineTo, hx]
    rw [hto]
    change evenEmb (evenTo σ hσ (evenIdx x hx)) = σ x
    have hσx : (σ (evenEmb (evenIdx x hx))).val % 2 = 0 := by
      rw [evenEmb_evenIdx]
      exact (hσ x).trans hx
    have he : evenTo σ hσ (evenIdx x hx) =
        evenIdx (σ (evenEmb (evenIdx x hx))) hσx := by
      apply Fin.ext
      simp [evenTo, evenIdx]
    rw [he, evenEmb_evenIdx, evenEmb_evenIdx]
  · have ho : x.val % 2 = 1 := mod_one_of_ne hx
    have hto : combineTo (evenPart σ hσ) (oddPart σ hσ) x =
        oddEmb ((oddPart σ hσ) (oddIdx x ho)) := by
      simp [combineTo, hx]
    rw [hto]
    change oddEmb (oddTo σ hσ (oddIdx x ho)) = σ x
    have hσx : (σ (oddEmb (oddIdx x ho))).val % 2 = 1 := by
      rw [oddEmb_oddIdx]
      exact (hσ x).trans ho
    have he : oddTo σ hσ (oddIdx x ho) =
        oddIdx (σ (oddEmb (oddIdx x ho))) hσx := by
      apply Fin.ext
      simp [oddTo, oddIdx]
    rw [he, oddEmb_oddIdx, oddEmb_oddIdx]

def parityTo {n : ℕ} (σe : Perm (Fin (n + 1))) (σo : Perm (Fin n)) :
    Quotient (orb (combine σe σo)) → Quotient (orb σe) ⊕ Quotient (orb σo) :=
  Quotient.lift
    (fun x => if hx : x.val % 2 = 0 then Sum.inl (Quotient.mk (orb σe) (evenIdx x hx))
      else Sum.inr (Quotient.mk (orb σo) (oddIdx x (mod_one_of_ne hx))))
    (fun a b h => by
      have hsc : (combine σe σo).SameCycle a b := (sameCycle_orbit _ a b).mp h
      by_cases ha : a.val % 2 = 0
      · have hb : b.val % 2 = 0 := by
          obtain ⟨k, hk⟩ := hsc
          have hp := keeps_zpow (combine_keeps σe σo) k a
          have hp' := congrArg (fun y : Fin (2 * n + 1) => y.val % 2) hk
          exact (hp'.symm.trans hp).trans ha
        have hdown : σe.SameCycle (evenIdx a ha) (evenIdx b hb) := by
          have ha' := (evenEmb_evenIdx a ha).symm
          have hb' := (evenEmb_evenIdx b hb).symm
          rw [ha', hb'] at hsc
          exact (combine_same_even σe σo _ _).mp hsc
        simp [ha, hb]
        apply Quotient.sound
        exact (sameCycle_orbit σe _ _).mpr hdown
      · have hoa : a.val % 2 = 1 := mod_one_of_ne ha
        have hb : b.val % 2 ≠ 0 := by
          intro hb0
          obtain ⟨k, hk⟩ := hsc
          have hp := keeps_zpow (combine_keeps σe σo) k a
          have hp' := congrArg (fun y : Fin (2 * n + 1) => y.val % 2) hk
          exact ha ((hp'.symm.trans hp).symm.trans hb0)
        have hob : b.val % 2 = 1 := mod_one_of_ne hb
        have hdown : σo.SameCycle (oddIdx a hoa) (oddIdx b hob) := by
          have ha' := (oddEmb_oddIdx a hoa).symm
          have hb' := (oddEmb_oddIdx b hob).symm
          rw [ha', hb'] at hsc
          exact (combine_same_odd σe σo _ _).mp hsc
        simp [ha, hb]
        apply Quotient.sound
        exact (sameCycle_orbit σo _ _).mpr hdown)

def parityInv {n : ℕ} (σe : Perm (Fin (n + 1))) (σo : Perm (Fin n)) :
    Quotient (orb σe) ⊕ Quotient (orb σo) → Quotient (orb (combine σe σo))
  | Sum.inl q =>
      Quotient.lift (fun i => Quotient.mk (orb (combine σe σo)) (evenEmb i))
        (fun a b h => by
          apply Quotient.sound
          exact (sameCycle_orbit _ _ _).mpr
            ((combine_same_even σe σo a b).mpr ((sameCycle_orbit σe a b).mp h))) q
  | Sum.inr q =>
      Quotient.lift (fun j => Quotient.mk (orb (combine σe σo)) (oddEmb j))
        (fun a b h => by
          apply Quotient.sound
          exact (sameCycle_orbit _ _ _).mpr
            ((combine_same_odd σe σo a b).mpr ((sameCycle_orbit σo a b).mp h))) q

lemma parityTo_even {n : ℕ} (σe : Perm (Fin (n + 1))) (σo : Perm (Fin n)) (i : Fin (n + 1)) :
    parityTo σe σo (Quotient.mk _ (evenEmb i)) = Sum.inl (Quotient.mk _ i) := by
  have hx : (evenEmb i).val % 2 = 0 := evenEmb_mod i
  simp [parityTo, hx, evenIdx_evenEmb]

lemma parityTo_odd {n : ℕ} (σe : Perm (Fin (n + 1))) (σo : Perm (Fin n)) (j : Fin n) :
    parityTo σe σo (Quotient.mk _ (oddEmb j)) = Sum.inr (Quotient.mk _ j) := by
  have hx : (oddEmb j).val % 2 ≠ 0 := by simp [oddEmb_mod]
  simp [parityTo, hx, oddIdx_oddEmb]

lemma parityInv_even {n : ℕ} (σe : Perm (Fin (n + 1))) (σo : Perm (Fin n)) (i : Fin (n + 1)) :
    parityInv σe σo (Sum.inl (Quotient.mk _ i)) = Quotient.mk _ (evenEmb i) := by
  simp [parityInv]

lemma parityInv_odd {n : ℕ} (σe : Perm (Fin (n + 1))) (σo : Perm (Fin n)) (j : Fin n) :
    parityInv σe σo (Sum.inr (Quotient.mk _ j)) = Quotient.mk _ (oddEmb j) := by
  simp [parityInv]

def parityQuot {n : ℕ} (σe : Perm (Fin (n + 1))) (σo : Perm (Fin n)) :
    Quotient (orb (combine σe σo)) ≃ Quotient (orb σe) ⊕ Quotient (orb σo) where
  toFun := parityTo σe σo
  invFun := parityInv σe σo
  left_inv q := by
    refine Quotient.inductionOn q ?_
    intro x
    by_cases hx : x.val % 2 = 0
    · rw [show x = evenEmb (evenIdx x hx) from (evenEmb_evenIdx x hx).symm]
      rw [parityTo_even, parityInv_even]
    · have ho : x.val % 2 = 1 := mod_one_of_ne hx
      rw [show x = oddEmb (oddIdx x ho) from (oddEmb_oddIdx x ho).symm]
      rw [parityTo_odd, parityInv_odd]
  right_inv s := by
    cases s with
    | inl q =>
      refine Quotient.inductionOn q ?_
      intro i
      rw [parityInv_even, parityTo_even]
    | inr q =>
      refine Quotient.inductionOn q ?_
      intro j
      rw [parityInv_odd, parityTo_odd]

lemma cycles_combine {n : ℕ} (σe : Perm (Fin (n + 1))) (σo : Perm (Fin n)) :
    cycles (combine σe σo) = cycles σe + cycles σo := by
  rw [cycles_eq_quot, cycles_eq_quot, cycles_eq_quot, Nat.card_congr (parityQuot σe σo),
    Nat.card_sum]

abbrev Good (n : ℕ) :=
  {σ : Perm (Fin (2 * n + 1)) // keeps n σ ∧ cycles σ = n + 1}

def parityEquiv (n : ℕ) :
    {p : Perm (Fin (n + 1)) × Perm (Fin n) // cycles p.1 + cycles p.2 = n + 1} ≃ Good n where
  toFun p := ⟨combine p.1.1 p.1.2, combine_keeps p.1.1 p.1.2, by
    rw [cycles_combine]
    exact p.2⟩
  invFun σ := ⟨(evenPart σ.1 σ.2.1, oddPart σ.1 σ.2.1), by
    have h := cycles_combine (evenPart σ.1 σ.2.1) (oddPart σ.1 σ.2.1)
    rw [recombine σ.1 σ.2.1] at h
    rw [← h]
    exact σ.2.2⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · exact evenPart_combine p.1.1 p.1.2
    · exact oddPart_combine p.1.1 p.1.2
  right_inv σ := by
    apply Subtype.ext
    exact recombine σ.1 σ.2.1

lemma sigma_pair_eq {n : ℕ} {k₁ k₂ : Fin (n + 2)}
    {σe₁ : Cyc (n + 1) k₁.val} {σo₁ : Cyc n (n + 1 - k₁.val)}
    {σe₂ : Cyc (n + 1) k₂.val} {σo₂ : Cyc n (n + 1 - k₂.val)}
    (hk : k₁ = k₂) (he : σe₁.1 = σe₂.1) (ho : σo₁.1 = σo₂.1) :
    (⟨k₁, σe₁, σo₁⟩ :
        Σ k : Fin (n + 2), Cyc (n + 1) k.val × Cyc n (n + 1 - k.val)) =
      ⟨k₂, σe₂, σo₂⟩ := by
  subst hk
  exact congrArg (Sigma.mk k₁) (Prod.ext (Subtype.ext he) (Subtype.ext ho))

noncomputable def cyclePack (n : ℕ) :
    (Σ k : Fin (n + 2), Cyc (n + 1) k.val × Cyc n (n + 1 - k.val)) ≃
      {p : Perm (Fin (n + 1)) × Perm (Fin n) // cycles p.1 + cycles p.2 = n + 1} where
  toFun := fun ⟨k, σe, σo⟩ => ⟨(σe.1, σo.1), by
    rw [σe.2, σo.2]
    omega⟩
  invFun p :=
    ⟨⟨cycles p.1.1, by
        have hle := cycles_le p.1.1
        omega⟩,
      ⟨p.1.1, rfl⟩,
      ⟨p.1.2, show cycles p.1.2 = n + 1 - cycles p.1.1 from by
        have hsum := p.2
        omega⟩⟩
  left_inv := fun ⟨k, σe, σo⟩ => by
    apply sigma_pair_eq
    · apply Fin.ext
      exact σe.2
    · rfl
    · rfl
  right_inv p := by
    apply Subtype.ext
    rfl

lemma rising_mul_coeff (n : ℕ) :
    (rising (n + 1) * rising n).coeff (n + 1) =
      ∑ k ∈ range (n + 2), stirlingFirst (n + 1) k * stirlingFirst n (n + 1 - k) := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk
      (fun ij => (rising (n + 1)).coeff ij.1 * (rising n).coeff ij.2) (n + 1)]
  refine sum_congr rfl fun k _ => ?_
  simp [coeff_rising]

lemma good_card (n : ℕ) :
    Nat.card (Good n) =
      ∑ k ∈ range (n + 2), stirlingFirst (n + 1) k * stirlingFirst n (n + 1 - k) := by
  rw [← Nat.card_congr (parityEquiv n), ← Nat.card_congr (cyclePack n)]
  haveI : ∀ k : Fin (n + 2), Finite (Cyc (n + 1) k.val × Cyc n (n + 1 - k.val)) := by
    intro k
    haveI := cyc_finite (n + 1) k.val
    haveI := cyc_finite n (n + 1 - k.val)
    infer_instance
  rw [Nat.card_sigma]
  simp_rw [Nat.card_prod, cycCard_eq]
  simpa using Fin.sum_univ_eq_sum_range
    (fun k => stirlingFirst (n + 1) k * stirlingFirst n (n + 1 - k)) (n + 2)

lemma main_card (n : ℕ) (hn : 1 ≤ n) :
    Nat.card (Place n) =
      Nat.card {σ : Perm (Fin (2 * n + 1)) // keeps n σ ∧ cycles σ = n + 1} := by
  rw [place_card, bishop_coeff_eq_rising n hn, rising_mul_coeff]
  exact (good_card n).symm

end A187235

theorem OMA.solution : type_of% @OMA.S_oeis_a187235.main := by
  intro n hn
  exact A187235.main_card n hn

