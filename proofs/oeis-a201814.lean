import OMAStatements.S_oeis_a201814

namespace OMA.S_oeis_a201814

open PowerSeries



section ZeroSum

open PowerSeries

/-! ### Weighted chains -/

/-- Continuations of v of length L with R between consecutive entries, each entry u weighted by
f u. -/
def wch {α M : Type*} [CommSemiring M] (s : Finset α) (R : α → α → Prop) [DecidableRel R]
    (f : α → M) : ℕ → α → M
  | 0, _ => 1
  | L + 1, v => ∑ u ∈ s.filter (R v ·), f u * wch s R f L u

lemma sum_piFinset_cons {α M : Type*} [DecidableEq α] [AddCommMonoid M] (s : Finset α) {L : ℕ}
    (P : (Fin (L + 1) → α) → Prop) [DecidablePred P] (F : (Fin (L + 1) → α) → M) :
    ∑ x ∈ (Fintype.piFinset fun _ : Fin (L + 1) => s).filter P, F x =
      ∑ v ∈ s, ∑ y ∈ (Fintype.piFinset fun _ : Fin L => s).filter (fun y => P (Fin.cons v y)),
        F (Fin.cons v y) := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun x : Fin (L + 1) → α => x 0) (t := s)
    (fun x hx => by
      simp only [Finset.mem_filter, Fintype.mem_piFinset] at hx
      exact hx.1 0)]
  refine Finset.sum_congr rfl (fun v hv => ?_)
  symm
  apply Finset.sum_nbij' (fun y => (Fin.cons v y : Fin (L + 1) → α)) (fun x => Fin.tail x)
  · intro y hy
    simp only [Finset.mem_filter, Fintype.mem_piFinset] at hy ⊢
    refine ⟨⟨fun i => ?_, hy.2⟩, by simp⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using hv
    · simpa using hy.1 j
  · intro x hx
    simp only [Finset.mem_filter, Fintype.mem_piFinset] at hx ⊢
    obtain ⟨⟨hmem, hp⟩, h0⟩ := hx
    refine ⟨fun i => hmem i.succ, ?_⟩
    rw [← h0, Fin.cons_self_tail]
    exact hp
  · intro y _
    simp
  · intro x hx
    simp only [Finset.mem_filter] at hx
    show Fin.cons v (Fin.tail x) = x
    rw [← hx.2, Fin.cons_self_tail]
  · intro y _
    rfl

lemma chain_cons' {α : Type*} (R : α → α → Prop) {L : ℕ} (v : α) (y : Fin (L + 1) → α) :
    (∀ i : Fin (L + 1), R ((Fin.cons v y : Fin (L + 2) → α) i.castSucc)
      ((Fin.cons v y : Fin (L + 2) → α) i.succ)) ↔
      R v (y 0) ∧ ∀ i : Fin L, R (y i.castSucc) (y i.succ) := by
  rw [Fin.forall_fin_succ]
  simp only [Fin.castSucc_zero, Fin.cons_zero, Fin.succ_zero_eq_one, Fin.cons_one,
    Fin.castSucc_succ, Fin.cons_succ]

lemma prod_cons {α M : Type*} [CommMonoid M] (f : α → M) {L : ℕ} (v : α) (y : Fin L → α) :
    ∏ i, f ((Fin.cons v y : Fin (L + 1) → α) i) = f v * ∏ i, f (y i) := by
  rw [Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]

lemma wsum_from {α M : Type*} [DecidableEq α] [CommSemiring M] (s : Finset α)
    (R : α → α → Prop) [DecidableRel R] (f : α → M) :
    ∀ (L : ℕ) (v : α), ∑ y ∈ (Fintype.piFinset fun _ : Fin L => s).filter
      (fun y => ∀ i : Fin L, R ((Fin.cons v y : Fin (L + 1) → α) i.castSucc)
        ((Fin.cons v y : Fin (L + 1) → α) i.succ)), ∏ i, f (y i) = wch s R f L v
  | 0, v => by
    rw [wch]
    have hu : (Fintype.piFinset fun _ : Fin 0 => s) = {Fin.elim0} := by
      ext g
      simp only [Fintype.mem_piFinset, Finset.mem_singleton]
      exact ⟨fun _ => funext fun i => i.elim0, fun _ i => i.elim0⟩
    rw [hu, Finset.filter_singleton]
    simp
  | L + 1, v => by
    conv_rhs => rw [wch, Finset.sum_filter]
    rw [sum_piFinset_cons]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    rw [Finset.filter_congr (fun z _ => chain_cons' R v (Fin.cons w z))]
    simp only [Fin.cons_zero]
    rw [Finset.sum_congr rfl (fun z _ => prod_cons f w z)]
    by_cases hw : R v w
    · rw [if_pos hw, ← wsum_from s R f L w, Finset.mul_sum]
      refine Finset.sum_congr ?_ (fun z _ => rfl)
      ext z
      simp only [Finset.mem_filter, hw, true_and]
    · rw [if_neg hw]
      exact Finset.sum_eq_zero (fun z hz => by
        simp only [Finset.mem_filter] at hz
        exact absurd hz.2.1 hw)

/-- Weighted arrays with R between consecutive entries, through wch. -/
theorem wsum_chain {α M : Type*} [DecidableEq α] [CommSemiring M] (s : Finset α)
    (R : α → α → Prop) [DecidableRel R] (f : α → M) (L : ℕ) :
    ∑ x ∈ (Fintype.piFinset fun _ : Fin (L + 1) => s).filter
      (fun x => ∀ i : Fin L, R (x i.castSucc) (x i.succ)), ∏ i, f (x i) =
        ∑ v ∈ s, f v * wch s R f L v := by
  rw [sum_piFinset_cons]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [Finset.sum_congr rfl (fun y _ => prod_cons f v y), ← Finset.mul_sum, wsum_from]

/-! ### Classes: zero, positive, negative -/

/-- The class of an integer: 0 for zero, 1 for positive, 2 for negative. -/
def cls (v : ℤ) : Fin 3 := if v = 0 then 0 else if 0 < v then 1 else 2

lemma cls_eq_zero (v : ℤ) : cls v = 0 ↔ v = 0 := by
  unfold cls
  split_ifs <;> simp_all

lemma cls_eq_one (v : ℤ) : cls v = 1 ↔ 0 < v := by
  unfold cls
  split_ifs with h1 h2 <;> simp_all

lemma cls_eq_two (v : ℤ) : cls v = 2 ↔ v < 0 := by
  unfold cls
  split_ifs with h1 h2 <;> simp_all <;> omega

/-- The weighted chain sums by class. -/
def Om {M : Type*} [CommSemiring M] (Rc : Fin 3 → Fin 3 → Prop) [DecidableRel Rc]
    (G : Fin 3 → M) : ℕ → Fin 3 → M
  | 0, _ => 1
  | L + 1, c => ∑ c' : Fin 3, if Rc c c' then G c' * Om Rc G L c' else 0

lemma wch_cls {M : Type*} [CommSemiring M] (s : Finset ℤ) (Rc : Fin 3 → Fin 3 → Prop)
    [DecidableRel Rc] (f : ℤ → M) (G : Fin 3 → M)
    (hG : ∀ c, G c = ∑ u ∈ s.filter (fun u => cls u = c), f u) :
    ∀ (L : ℕ) (v : ℤ), wch s (fun v u => Rc (cls v) (cls u)) f L v = Om Rc G L (cls v)
  | 0, _ => rfl
  | L + 1, v => by
    rw [wch, Om, Finset.sum_filter, ← Finset.sum_fiberwise s cls]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    have hu : ∀ u ∈ s.filter (fun u => cls u = c),
        (if Rc (cls v) (cls u) then f u * wch s (fun v u => Rc (cls v) (cls u)) f L u else 0) =
          if Rc (cls v) c then f u * Om Rc G L c else 0 := by
      intro u hu
      rw [Finset.mem_filter] at hu
      rw [wch_cls s Rc f G hG L u, hu.2]
    rw [Finset.sum_congr rfl hu]
    split_ifs with h
    · rw [hG c, Finset.sum_mul]
    · simp

/-! ### Counts as coefficients -/

lemma card_coeff {ι : Type*} [Fintype ι] (S : Finset (ι → ℤ)) (w : ℤ → ℕ) (m : ℕ) :
    ((S.filter (fun x => ∑ i, w (x i) = m)).card : ℤ) =
      coeff m (∑ x ∈ S, ∏ i, (X : ℤ⟦X⟧) ^ w (x i)) := by
  rw [Finset.card_filter, map_sum]
  push_cast
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.prod_pow_eq_pow_sum, coeff_X_pow]
  exact if_congr eq_comm rfl rfl

lemma zsum_iff {K n : ℕ} (x : Fin K → ℤ) (hx : ∀ i, -(n : ℤ) ≤ x i ∧ x i ≤ n) :
    ∑ i, x i = 0 ↔ ∑ i, (x i + n).toNat = K * n := by
  have h : ((∑ i, (x i + n).toNat : ℕ) : ℤ) = ∑ i, x i + K * n := by
    push_cast
    rw [Finset.sum_congr rfl (fun i _ => Int.toNat_of_nonneg (by linarith [(hx i).1])),
      Finset.sum_add_distrib]
    simp
  omega

/-- The generating polynomial of 0..n-1. -/
noncomputable def Pn (n : ℕ) : ℤ⟦X⟧ := ∑ j ∈ Finset.range n, X ^ j

/-- The generating functions of the entries of each class in -n..n, shifted by n. -/
noncomputable def Gn (n : ℕ) : Fin 3 → ℤ⟦X⟧ := ![X ^ n, X ^ (n + 1) * Pn n, Pn n]

lemma Gn_zero (n : ℕ) :
    Gn n 0 = ∑ u ∈ (Finset.Icc (-(n : ℤ)) n).filter (fun u => cls u = 0), X ^ (u + n).toNat := by
  have hs : (Finset.Icc (-(n : ℤ)) n).filter (fun u => cls u = 0) = {0} := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton, cls_eq_zero]
    omega
  rw [hs, Finset.sum_singleton]
  simp [Gn]

lemma Gn_one (n : ℕ) :
    Gn n 1 = ∑ u ∈ (Finset.Icc (-(n : ℤ)) n).filter (fun u => cls u = 1), X ^ (u + n).toNat := by
  have hs : (Finset.Icc (-(n : ℤ)) n).filter (fun u => cls u = 1) = Finset.Icc 1 (n : ℤ) := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_Icc, cls_eq_one]
    omega
  rw [hs]
  show X ^ (n + 1) * Pn n = _
  rw [Pn, Finset.mul_sum]
  apply Finset.sum_nbij' (fun j : ℕ => (j : ℤ) + 1) (fun u : ℤ => (u - 1).toNat)
  · intro j hj
    simp only [Finset.mem_range] at hj
    simp only [Finset.mem_Icc]
    omega
  · intro u hu
    simp only [Finset.mem_Icc] at hu
    simp only [Finset.mem_range]
    omega
  · intro j _
    simp
  · intro u hu
    simp only [Finset.mem_Icc] at hu
    omega
  · intro j _
    rw [← pow_add]
    congr 1
    omega

lemma Gn_two (n : ℕ) :
    Gn n 2 = ∑ u ∈ (Finset.Icc (-(n : ℤ)) n).filter (fun u => cls u = 2), X ^ (u + n).toNat := by
  have hs : (Finset.Icc (-(n : ℤ)) n).filter (fun u => cls u = 2) =
      Finset.Icc (-(n : ℤ)) (-1) := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_Icc, cls_eq_two]
    omega
  rw [hs]
  show Pn n = _
  rw [Pn]
  apply Finset.sum_nbij' (fun j : ℕ => (j : ℤ) - n) (fun u : ℤ => (u + n).toNat)
  · intro j hj
    simp only [Finset.mem_range] at hj
    simp only [Finset.mem_Icc]
    omega
  · intro u hu
    simp only [Finset.mem_Icc] at hu
    simp only [Finset.mem_range]
    omega
  · intro j _
    simp
  · intro u hu
    simp only [Finset.mem_Icc] at hu
    omega
  · intro j _
    congr 1
    omega

lemma Gn_eq (n : ℕ) (c : Fin 3) :
    Gn n c = ∑ u ∈ (Finset.Icc (-(n : ℤ)) n).filter (fun u => cls u = c), X ^ (u + n).toNat := by
  fin_cases c
  exacts [Gn_zero n, Gn_one n, Gn_two n]

/-- The zero-sum arrays in -n..n with a chain condition on the classes, as a coefficient. -/
theorem count_chain (K n : ℕ) (Rc : Fin 3 → Fin 3 → Prop) [DecidableRel Rc] :
    ((((Fintype.piFinset fun _ : Fin (K + 1) => Finset.Icc (-(n : ℤ)) n).filter
      (fun x => ∀ i : Fin K, Rc (cls (x i.castSucc)) (cls (x i.succ)))).filter
        (fun x => ∑ i, (x i + (n : ℤ)).toNat = (K + 1) * n)).card : ℤ) =
      coeff ((K + 1) * n) (∑ c : Fin 3, Gn n c * Om Rc (Gn n) K c) := by
  rw [card_coeff _ (fun u : ℤ => (u + n).toNat),
    wsum_chain (Finset.Icc (-(n : ℤ)) n) (fun v u => Rc (cls v) (cls u))
      (fun u => (X : ℤ⟦X⟧) ^ (u + n).toNat) K]
  rw [Finset.sum_congr rfl (fun v _ => by
    rw [wch_cls _ Rc _ (Gn n) (fun c => Gn_eq n c) K v])]
  rw [← Finset.sum_fiberwise (Finset.Icc (-(n : ℤ)) n) cls]
  congr 1
  refine Finset.sum_congr rfl (fun c _ => ?_)
  have hu : ∀ u ∈ (Finset.Icc (-(n : ℤ)) n).filter (fun u => cls u = c),
      (X : ℤ⟦X⟧) ^ (u + n).toNat * Om Rc (Gn n) K (cls u) =
        X ^ (u + n).toNat * Om Rc (Gn n) K c := by
    intro u hu
    rw [Finset.mem_filter] at hu
    rw [hu.2]
  rw [Finset.sum_congr rfl hu, ← Finset.sum_mul, ← Gn_eq]

/-! ### The coefficients -/

/-- The coefficient for p positive and q negative entries (and any number of zeros). -/
noncomputable def Mc (p q n : ℕ) : ℤ :=
  if p ≤ q * n then coeff (q * n - p) (Pn n ^ (p + q)) else 0

lemma coeff_mono (p q z K n : ℕ) (hK : p + q + z = K) :
    coeff (K * n) (Gn n 1 ^ p * Gn n 2 ^ q * Gn n 0 ^ z) = Mc p q n := by
  have e : Gn n 1 ^ p * Gn n 2 ^ q * Gn n 0 ^ z =
      X ^ ((n * p + n * z) + p) * Pn n ^ (p + q) := by
    show (X ^ (n + 1) * Pn n) ^ p * Pn n ^ q * (X ^ n) ^ z = _
    ring
  rw [e, coeff_X_pow_mul', Mc, ← hK, show (p + q + z) * n = (n * p + n * z) + q * n by ring]
  obtain ⟨A, hA⟩ : ∃ A, n * p + n * z = A := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, q * n = B := ⟨_, rfl⟩
  rw [hA, hB]
  by_cases h : p ≤ B
  · rw [if_pos (by omega), if_pos h, show A + B - (A + p) = B - p by omega]
  · rw [if_neg (by omega), if_neg h]

lemma coeff_Pn_pow (d n S : ℕ) :
    coeff S (Pn n ^ (d + 1)) = ∑ t ∈ Finset.range (d + 1 + 1), (-1) ^ t * ((d + 1).choose t : ℤ) *
      (if t * n ≤ S then ((d + (S - t * n)).choose d : ℤ) else 0) := by
  have hP : (1 - X) * Pn n = 1 - X ^ n := by
    unfold Pn
    exact mul_neg_geom_sum X n
  have hG := mk_add_choose_mul_one_sub_pow_eq_one ℤ d
  have key : Pn n ^ (d + 1) =
      (mk fun k => ((d + k).choose d : ℤ)) * (1 - X ^ n) ^ (d + 1) := by
    rw [← hP, mul_pow, ← mul_assoc, hG, one_mul]
  have hb : (1 - X ^ n : ℤ⟦X⟧) ^ (d + 1) =
      ∑ t ∈ Finset.range (d + 1 + 1), C ((-1) ^ t * ((d + 1).choose t : ℤ)) * X ^ (t * n) := by
    rw [sub_eq_neg_add, add_pow]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [one_pow, mul_one, neg_pow, ← pow_mul, mul_comm n t, map_mul, map_pow, map_neg, map_one,
      map_natCast]
    ring
  rw [key, hb, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [show (mk fun k => ((d + k).choose d : ℤ)) * (C ((-1) ^ t * ((d + 1).choose t : ℤ)) *
      X ^ (t * n)) = C ((-1) ^ t * ((d + 1).choose t : ℤ)) *
        (X ^ (t * n) * mk fun k => ((d + k).choose d : ℤ)) by ring,
    coeff_C_mul, coeff_X_pow_mul', coeff_mk]

lemma choose_mul_factorial (N : ℕ) : ∀ k : ℕ,
    (N.choose k : ℚ) * k.factorial = ∏ i ∈ Finset.range k, ((N : ℚ) - i)
  | 0 => by simp
  | k + 1 => by
    rw [Finset.prod_range_succ, ← choose_mul_factorial N k, Nat.factorial_succ]
    rcases Nat.lt_or_ge N k with hk | hk
    · rw [Nat.choose_eq_zero_of_lt hk, Nat.choose_eq_zero_of_lt (by omega)]
      simp
    · have h := Nat.choose_succ_right_eq N k
      have h' : (N.choose (k + 1) : ℚ) * (k + 1) = (N.choose k : ℚ) * ((N : ℚ) - k) := by
        rw [← Nat.cast_sub hk]
        exact_mod_cast h
      push_cast
      linear_combination (k.factorial : ℚ) * h'

lemma choose_div (N k : ℕ) :
    (N.choose k : ℚ) = (∏ i ∈ Finset.range k, ((N : ℚ) - i)) / k.factorial := by
  rw [eq_div_iff (by positivity), choose_mul_factorial]

lemma Mc_closed (p q n : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hn : 1 ≤ n) :
    (Mc p q n : ℚ) = ∑ t ∈ Finset.range q,
      (-1) ^ t * ((p + q).choose t : ℚ) * (((q - t) * n + (q - 1)).choose (p + q - 1) : ℚ) := by
  obtain ⟨d, hd⟩ : ∃ d, p + q = d + 1 := ⟨p + q - 1, by omega⟩
  have hd' : p + q - 1 = d := by omega
  rw [hd', hd]
  have hsplit : Finset.range (d + 1 + 1) = Finset.range q ∪ Finset.Ico q (d + 1 + 1) := by
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
      Finset.Ico_union_Ico_eq_Ico (Nat.zero_le q) (by omega)]
  have hdisj : Disjoint (Finset.range q) (Finset.Ico q (d + 1 + 1)) := by
    rw [Finset.range_eq_Ico]
    exact Finset.Ico_disjoint_Ico_consecutive 0 q (d + 1 + 1)
  have hz : ∀ t, q ≤ t → ¬ (t * n ≤ q * n - p) := by
    intro t ht
    have : q * n ≤ t * n := Nat.mul_le_mul_right n ht
    have : 1 ≤ t * n := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
    omega
  have hzero : ∀ t, (q - t) * n < p → ((q - t) * n + (q - 1)).choose d = 0 := by
    intro t h
    apply Nat.choose_eq_zero_of_lt
    omega
  unfold Mc
  rw [hd]
  by_cases h : p ≤ q * n
  · rw [if_pos h, coeff_Pn_pow d n _, hsplit, Finset.sum_union hdisj]
    rw [Finset.sum_eq_zero (s := Finset.Ico q (d + 1 + 1)) (fun t ht => by
      rw [Finset.mem_Ico] at ht
      rw [if_neg (hz t ht.1), mul_zero])]
    push_cast
    rw [add_zero]
    refine Finset.sum_congr rfl (fun t ht => ?_)
    rw [Finset.mem_range] at ht
    have e1 : (q - t) * n = q * n - t * n := Nat.sub_mul q t n
    have e2 : t * n ≤ q * n := Nat.mul_le_mul_right n ht.le
    by_cases ht' : t * n ≤ q * n - p
    · rw [if_pos ht', show d + (q * n - p - t * n) = (q - t) * n + (q - 1) by omega]
    · rw [if_neg ht', hzero t (by omega)]
      push_cast
      ring
  · rw [if_neg h]
    push_cast
    symm
    refine Finset.sum_eq_zero (fun t _ => ?_)
    have : (q - t) * n ≤ q * n := Nat.mul_le_mul_right n (Nat.sub_le q t)
    rw [hzero t (by omega)]
    push_cast
    ring

lemma Mc_zero_right (p n : ℕ) (hp : 1 ≤ p) : Mc p 0 n = 0 := by
  unfold Mc
  rw [if_neg (by omega)]

lemma coeff_Pn (n j : ℕ) : coeff j (Pn n) = if j < n then 1 else 0 := by
  rw [Pn, map_sum]
  simp only [coeff_X_pow]
  rw [Finset.sum_ite_eq]
  simp [Finset.mem_range]

/-- Pn n ^ q has degree q (n - 1). -/
lemma coeff_Pn_pow_high (n : ℕ) : ∀ (q m : ℕ), q * (n - 1) < m → coeff m (Pn n ^ q) = 0
  | 0, m, h => by
    rw [pow_zero, coeff_one, if_neg (by omega)]
  | q + 1, m, h => by
    rw [pow_succ, coeff_mul]
    refine Finset.sum_eq_zero (fun ij hij => ?_)
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
    by_cases hj : ij.2 < n
    · have hm : (q + 1) * (n - 1) = q * (n - 1) + (n - 1) := by ring
      rw [hm] at h
      rw [coeff_Pn_pow_high n q ij.1 (by omega), zero_mul]
    · rw [coeff_Pn, if_neg hj, mul_zero]

lemma Mc_zero_left (q n : ℕ) (hq : 1 ≤ q) (hn : 1 ≤ n) : Mc 0 q n = 0 := by
  unfold Mc
  rw [if_pos (Nat.zero_le _), Nat.sub_zero, zero_add]
  apply coeff_Pn_pow_high
  have h : q * (n - 1) + q = q * n := by
    rw [← Nat.mul_succ]
    congr 1
    omega
  omega

lemma Mc_zero_zero (n : ℕ) : Mc 0 0 n = 1 := by
  unfold Mc
  simp

lemma coeff_natCast_mul (m c : ℕ) (F : ℤ⟦X⟧) :
    coeff m ((c : ℤ⟦X⟧) * F) = (c : ℤ) * coeff m F := by
  rw [← map_natCast (C (R := ℤ)) c, coeff_C_mul]

lemma om_zero {M : Type*} [CommSemiring M] (Rc : Fin 3 → Fin 3 → Prop) [DecidableRel Rc]
    (G : Fin 3 → M) (c : Fin 3) : Om Rc G 0 c = 1 := rfl

/-! ### Conditions on the whole class pattern -/

/-- The number of entries of class c in a class pattern. -/
def ncls {K : ℕ} (σ : Fin K → Fin 3) (c : Fin 3) : ℕ := (Finset.univ.filter (fun i => σ i = c)).card

lemma ncls_sum {K : ℕ} (σ : Fin K → Fin 3) : ncls σ 1 + ncls σ 2 + ncls σ 0 = K := by
  have h := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin K)))
    (t := (Finset.univ : Finset (Fin 3))) (f := σ) (fun _ _ => Finset.mem_univ _)
  rw [Fin.sum_univ_three, Finset.card_univ, Fintype.card_fin] at h
  unfold ncls
  omega

lemma prod_cls {K : ℕ} {M : Type*} [CommMonoid M] (G : Fin 3 → M) (σ : Fin K → Fin 3) :
    ∏ i, G (σ i) = G 1 ^ ncls σ 1 * G 2 ^ ncls σ 2 * G 0 ^ ncls σ 0 := by
  rw [← Finset.prod_fiberwise Finset.univ σ (fun i => G (σ i)), Fin.prod_univ_three]
  have h : ∀ c : Fin 3, ∏ i ∈ Finset.univ.filter (fun i => σ i = c), G (σ i) = G c ^ ncls σ c := by
    intro c
    rw [Finset.prod_congr rfl (fun i hi => by rw [(Finset.mem_filter.1 hi).2]), Finset.prod_const]
    rfl
  rw [h 0, h 1, h 2]
  ac_rfl

/-- The number of class patterns of length K with p entries of class 1 and q of class 2. -/
def trin : ℕ → ℕ → ℕ → ℕ
  | 0, p, q => if p = 0 ∧ q = 0 then 1 else 0
  | K + 1, p, q => trin K p q + (if p = 0 then 0 else trin K (p - 1) q) +
      (if q = 0 then 0 else trin K p (q - 1))

lemma ncls_cons {K : ℕ} (c : Fin 3) (τ : Fin K → Fin 3) (d : Fin 3) :
    ncls (Fin.cons c τ : Fin (K + 1) → Fin 3) d = (if c = d then 1 else 0) + ncls τ d := by
  unfold ncls
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]

lemma card_head3 {K : ℕ} (Q : (Fin (K + 1) → Fin 3) → Prop) [DecidablePred Q] :
    (Finset.univ.filter Q).card =
      ∑ v : Fin 3, (Finset.univ.filter (fun h : Fin K → Fin 3 => Q (Fin.cons v h))).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun g : Fin (K + 1) → Fin 3 => g 0)
    (t := Finset.univ) (by intro x _; simp)]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  symm
  apply Finset.card_bij (fun h _ => (Fin.cons v h : Fin (K + 1) → Fin 3))
  · intro h hh
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hh ⊢
    exact ⟨hh, by simp⟩
  · intro h₁ _ h₂ _ e
    simpa using congrArg Fin.tail e
  · intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
    obtain ⟨hq, h0⟩ := hg
    refine ⟨Fin.tail g, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← h0, Fin.cons_self_tail]
      exact hq
    · show Fin.cons v (Fin.tail g) = g
      rw [← h0, Fin.cons_self_tail]

lemma card_ncls : ∀ (K p q : ℕ),
    (Finset.univ.filter (fun σ : Fin K → Fin 3 => ncls σ 1 = p ∧ ncls σ 2 = q)).card = trin K p q
  | 0, p, q => by
    have h1 : ∀ σ : Fin 0 → Fin 3, ncls σ 1 = 0 := fun σ => by simp [ncls]
    have h2 : ∀ σ : Fin 0 → Fin 3, ncls σ 2 = 0 := fun σ => by simp [ncls]
    rw [trin]
    split_ifs with h
    · rw [Finset.filter_true_of_mem (fun σ _ => by rw [h1, h2]; exact ⟨h.1.symm, h.2.symm⟩)]
      simp
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro σ _ hσ
      rw [h1, h2] at hσ
      exact h ⟨hσ.1.symm, hσ.2.symm⟩
  | K + 1, p, q => by
    rw [card_head3, Fin.sum_univ_three, trin]
    have e0 : (Finset.univ.filter (fun τ : Fin K → Fin 3 =>
        ncls (Fin.cons 0 τ : Fin (K + 1) → Fin 3) 1 = p ∧
          ncls (Fin.cons 0 τ : Fin (K + 1) → Fin 3) 2 = q)).card = trin K p q := by
      rw [← card_ncls K p q]
      congr 1
      ext τ
      rw [Finset.mem_filter, Finset.mem_filter, ncls_cons, ncls_cons]
      simp
    have e1 : (Finset.univ.filter (fun τ : Fin K → Fin 3 =>
        ncls (Fin.cons 1 τ : Fin (K + 1) → Fin 3) 1 = p ∧
          ncls (Fin.cons 1 τ : Fin (K + 1) → Fin 3) 2 = q)).card =
        if p = 0 then 0 else trin K (p - 1) q := by
      split_ifs with hp
      · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro τ _ hτ
        rw [ncls_cons, ncls_cons] at hτ
        simp at hτ
        omega
      · rw [← card_ncls K (p - 1) q]
        congr 1
        ext τ
        rw [Finset.mem_filter, Finset.mem_filter, ncls_cons, ncls_cons]
        simp
        omega
    have e2 : (Finset.univ.filter (fun τ : Fin K → Fin 3 =>
        ncls (Fin.cons 2 τ : Fin (K + 1) → Fin 3) 1 = p ∧
          ncls (Fin.cons 2 τ : Fin (K + 1) → Fin 3) 2 = q)).card =
        if q = 0 then 0 else trin K p (q - 1) := by
      split_ifs with hq
      · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro τ _ hτ
        rw [ncls_cons, ncls_cons] at hτ
        simp at hτ
        omega
      · rw [← card_ncls K p (q - 1)]
        congr 1
        ext τ
        rw [Finset.mem_filter, Finset.mem_filter, ncls_cons, ncls_cons]
        simp
        omega
    rw [e0, e1, e2]

/-- The zero-sum arrays in -n..n whose class pattern satisfies P, through the class patterns. -/
theorem count_pattern (K n : ℕ) (P : (Fin K → Fin 3) → Prop) [DecidablePred P] :
    ((((Fintype.piFinset fun _ : Fin K => Finset.Icc (-(n : ℤ)) n).filter
      (fun x => P (fun i => cls (x i)))).filter
        (fun x => ∑ i, (x i + (n : ℤ)).toNat = K * n)).card : ℤ) =
      ∑ σ ∈ Finset.univ.filter P, Mc (ncls σ 1) (ncls σ 2) n := by
  rw [card_coeff _ (fun u : ℤ => (u + n).toNat)]
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun x : Fin K → ℤ => fun i => cls (x i))
    (t := Finset.univ.filter P) (fun x hx => by
      simp only [Finset.mem_filter] at hx ⊢
      exact ⟨Finset.mem_univ _, hx.2⟩)]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  have hset : ((Fintype.piFinset fun _ : Fin K => Finset.Icc (-(n : ℤ)) n).filter
      (fun x => P (fun i => cls (x i)))).filter (fun x => (fun i => cls (x i)) = σ) =
      Fintype.piFinset fun i => (Finset.Icc (-(n : ℤ)) n).filter (fun u => cls u = σ i) := by
    ext x
    simp only [Finset.mem_filter, Fintype.mem_piFinset, funext_iff]
    constructor
    · rintro ⟨⟨hx, _⟩, hσ⟩ i
      exact ⟨hx i, hσ i⟩
    · intro h
      have hσ : (fun i => cls (x i)) = σ := funext fun i => (h i).2
      refine ⟨⟨fun i => (h i).1, ?_⟩, fun i => (h i).2⟩
      rw [hσ]
      simp_all
  rw [hset, ← Finset.prod_univ_sum
    (fun i => (Finset.Icc (-(n : ℤ)) n).filter (fun u => cls u = σ i))
    (fun _ v => (X : ℤ⟦X⟧) ^ (v + n).toNat)]
  simp only [← Gn_eq]
  rw [prod_cls, coeff_mono _ _ _ K n (ncls_sum σ)]

end ZeroSum

/-- Balanced class patterns: as many positive entries (class 1) as negative ones (class 2). -/
def bal (σ : Fin 6 → Fin 3) : Prop := ncls σ 1 = ncls σ 2

instance : DecidablePred bal := fun σ => by unfold bal; infer_instance

/-- The count through the balanced class patterns. -/
theorem a_pattern (n : ℕ) :
    (a n : ℤ) = ∑ σ ∈ Finset.univ.filter bal, Mc (ncls σ 1) (ncls σ 2) n := by
  rw [← count_pattern 6 n bal]
  unfold a arrays
  congr 2
  ext x
  simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc]
  have hb : (Finset.univ.filter (fun i => 0 < x i)).card =
      (Finset.univ.filter (fun i => x i < 0)).card ↔ bal (fun i => cls (x i)) := by
    unfold bal ncls
    simp only [cls_eq_one, cls_eq_two]
  constructor
  · rintro ⟨hx, hs, hc⟩
    exact ⟨⟨hx, hb.1 hc⟩, (zsum_iff x hx).1 hs⟩
  · rintro ⟨⟨hx, hc⟩, hs⟩
    exact ⟨hx, (zsum_iff x hx).2 hs, hb.2 hc⟩

/-- Grouped by the number p of positive entries (at most half of them). -/
theorem a_group (n : ℕ) :
    (a n : ℤ) = ∑ p ∈ Finset.range 4,
      (((Finset.univ.filter bal).filter (fun σ => ncls σ 1 = p)).card : ℤ) * Mc p p n := by
  rw [a_pattern, ← Finset.sum_fiberwise_of_maps_to (g := fun σ => ncls σ 1)
    (t := Finset.range 4) (fun σ hσ => by
      simp only [Finset.mem_filter, bal] at hσ
      have := ncls_sum σ
      rw [Finset.mem_range]
      omega)]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [Finset.sum_congr rfl (fun σ hσ => by
    simp only [Finset.mem_filter, bal] at hσ
    rw [← hσ.1.2, hσ.2]), Finset.sum_const, nsmul_eq_mul]

lemma cnt0 : ((Finset.univ.filter bal).filter (fun σ => ncls σ 1 = 0)).card = 1 := by
  rw [Finset.filter_filter, Finset.filter_congr (fun σ _ =>
    show bal σ ∧ ncls σ 1 = 0 ↔ ncls σ 1 = 0 ∧ ncls σ 2 = 0 by unfold bal; omega), card_ncls]
  decide

lemma cnt1 : ((Finset.univ.filter bal).filter (fun σ => ncls σ 1 = 1)).card = 30 := by
  rw [Finset.filter_filter, Finset.filter_congr (fun σ _ =>
    show bal σ ∧ ncls σ 1 = 1 ↔ ncls σ 1 = 1 ∧ ncls σ 2 = 1 by unfold bal; omega), card_ncls]
  decide

lemma cnt2 : ((Finset.univ.filter bal).filter (fun σ => ncls σ 1 = 2)).card = 90 := by
  rw [Finset.filter_filter, Finset.filter_congr (fun σ _ =>
    show bal σ ∧ ncls σ 1 = 2 ↔ ncls σ 1 = 2 ∧ ncls σ 2 = 2 by unfold bal; omega), card_ncls]
  decide

lemma cnt3 : ((Finset.univ.filter bal).filter (fun σ => ncls σ 1 = 3)).card = 20 := by
  rw [Finset.filter_filter, Finset.filter_congr (fun σ _ =>
    show bal σ ∧ ncls σ 1 = 3 ↔ ncls σ 1 = 3 ∧ ncls σ 2 = 3 by unfold bal; omega), card_ncls]
  decide

lemma M_1_1 (n : ℕ) (hn : 1 ≤ n) :
    (Mc 1 1 n : ℚ) = (n : ℚ) := by
  rw [Mc_closed 1 1 n (by norm_num) (by norm_num) hn]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, choose_div,
    Finset.prod_range_succ, Finset.prod_range_zero, Nat.factorial]
  push_cast
  ring

lemma M_2_2 (n : ℕ) (hn : 1 ≤ n) :
    (Mc 2 2 n : ℚ) = 2 / 3 * (n : ℚ) ^ 3 + 1 / 3 * (n : ℚ) := by
  rw [Mc_closed 2 2 n (by norm_num) (by norm_num) hn]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, choose_div,
    Finset.prod_range_succ, Finset.prod_range_zero, Nat.factorial]
  push_cast
  ring

lemma M_3_3 (n : ℕ) (hn : 1 ≤ n) :
    (Mc 3 3 n : ℚ) = 11 / 20 * (n : ℚ) ^ 5 + 1 / 4 * (n : ℚ) ^ 3 + 1 / 5 * (n : ℚ) := by
  rw [Mc_closed 3 3 n (by norm_num) (by norm_num) hn]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, choose_div,
    Finset.prod_range_succ, Finset.prod_range_zero, Nat.factorial]
  push_cast
  ring

/-- Hardin's polynomial, for n ≥ 1. -/
theorem poly (n : ℕ) (hn : 1 ≤ n) : (a n : ℚ) = 11 * (n : ℚ) ^ 5 + 65 * (n : ℚ) ^ 3 + 64 * (n : ℚ)
    + 1 := by
  have h := a_group n
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, cnt0, cnt1, cnt2, cnt3] at h
  rw [Mc_zero_zero] at h
  have hq : (a n : ℚ) = ((a n : ℤ) : ℚ) := by norm_cast
  rw [hq, h]
  push_cast
  rw [M_1_1 n hn, M_2_2 n hn, M_3_3 n hn]
  ring

lemma val (n v : ℕ) (hn : 1 ≤ n) (h : 11 * (n : ℚ) ^ 5 + 65 * (n : ℚ) ^ 3 + 64 * (n : ℚ)
    + 1 = v) : a n = v := by
  have e := poly n hn
  rw [h] at e
  exact_mod_cast e

/-- The values a(1..6). -/
theorem small : a 1 = 141 ∧ a 2 = 1001 ∧ a 3 = 4621 ∧ a 4 = 15681 ∧ a 5 = 42821 ∧ a 6 = 99961 :=
  ⟨val 1 141 (by norm_num) (by norm_num), val 2 1001 (by norm_num) (by norm_num),
    val 3 4621 (by norm_num) (by norm_num), val 4 15681 (by norm_num) (by norm_num),
    val 5 42821 (by norm_num) (by norm_num), val 6 99961 (by norm_num) (by norm_num)⟩

/-- Barker's recurrence, for n > 6. -/
theorem recurrence (n : ℕ) (hn : 6 < n) :
    (a n : ℤ) = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) - 15 * a (n - 4) + 6 * a (n - 5) - a (n - 6) := by
  obtain ⟨q, rfl⟩ : ∃ q, n = q + 7 := ⟨n - 7, by omega⟩
  simp only [show q + 7 - 1 = q + 6 by omega, show q + 7 - 2 = q + 5 by omega, show q + 7 - 3 = q
    + 4 by omega, show q + 7 - 4 = q + 3 by omega, show q + 7 - 5 = q + 2 by omega, show q + 7
    - 6 = q + 1 by omega]
  apply Int.cast_injective (α := ℚ)
  push_cast
  rw [poly (q + 7) (by omega), poly (q + 6) (by omega), poly (q + 5) (by omega),
    poly (q + 4) (by omega), poly (q + 3) (by omega), poly (q + 2) (by omega),
    poly (q + 1) (by omega)]
  push_cast
  ring

/-- Barker's g.f., as A(x) (1 - x)^6 = N(x) in Z[[x]]. -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 6 =
    X * (141 + 155 * X + 730 * X ^ 2 + 150 * X ^ 3 + 145 * X ^ 4 - X ^ 5) := by
  set A : ℤ⟦X⟧ := PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) with hA
  have e1 : A * (1 - X) ^ 6 =
      A - C 6 * (A * X ^ 1) + C 15 * (A * X ^ 2) - C 20 * (A * X ^ 3) + C 15 * (A * X ^ 4)
        - C 6 * (A * X ^ 5) + A * X ^ 6 := by
    simp only [map_ofNat]; ring
  have e2 : (X * (141 + 155 * X + 730 * X ^ 2 + 150 * X ^ 3 + 145 * X ^ 4 - X ^ 5) : ℤ⟦X⟧) =
      X ^ 1 * C 141 + X ^ 2 * C 155 + X ^ 3 * C 730 + X ^ 4 * C 150 + X ^ 5 * C 145 - X ^ 6 := by
    simp only [map_ofNat]; ring
  rw [e1, e2]
  ext n
  have hc : ∀ k, coeff k A = if k = 0 then (0 : ℤ) else a k := fun k => by rw [hA, coeff_mk]
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_C, coeff_X_pow, coeff_mul_X_pow', hc]
  have v := small
  rcases Nat.lt_or_ge n 7 with hn | hn
  · interval_cases n <;> simp_all
  · obtain ⟨q, rfl⟩ : ∃ q, n = q + 7 := ⟨n - 7, by omega⟩
    have h := recurrence (q + 7) (by omega)
    simp only [show q + 7 - 1 = q + 6 by omega, show q + 7 - 2 = q + 5 by omega, show q + 7
      - 3 = q + 4 by omega, show q + 7 - 4 = q + 3 by omega, show q + 7 - 5 = q + 2 by omega,
      show q + 7 - 6 = q + 1 by omega] at h ⊢
    simp only [show ¬ q + 7 = 0 by omega, show ¬ q + 6 = 0 by omega, show ¬ q + 5 = 0 by omega,
      show ¬ q + 4 = 0 by omega, show ¬ q + 3 = 0 by omega, show ¬ q + 2 = 0 by omega, show ¬ q
      + 1 = 0 by omega, show 1 ≤ q + 7 by omega, show 2 ≤ q + 7 by omega, show 3 ≤ q
      + 7 by omega, show 4 ≤ q + 7 by omega, show 5 ≤ q + 7 by omega, show 6 ≤ q + 7 by omega,
      show ¬ q + 7 = 1 by omega, show ¬ q + 7 = 2 by omega, show ¬ q + 7 = 3 by omega, show ¬ q
      + 7 = 4 by omega, show ¬ q + 7 = 5 by omega, show ¬ q + 7 = 6 by omega, if_true, if_false]
    rw [h]
    ring

/-- Controls: the entry's terms a(1..26). -/
theorem controls : a 1 = 141 ∧ a 2 = 1001 ∧ a 3 = 4621 ∧ a 4 = 15681 ∧ a 5 = 42821 ∧ a 6 = 99961 ∧
    a 7 = 207621 ∧ a 8 = 394241 ∧ a 9 = 697501 ∧ a 10 = 1165641 ∧ a 11 = 1858781 ∧
    a 12 = 2850241 ∧ a 13 = 4227861 ∧ a 14 = 6095321 ∧ a 15 = 8573461 ∧ a 16 = 11801601 ∧
    a 17 = 15938861 ∧ a 18 = 21165481 ∧ a 19 = 27684141 ∧ a 20 = 35721281 ∧ a 21 = 45528421 ∧
    a 22 = 57383481 ∧ a 23 = 71592101 ∧ a 24 = 88488961 ∧ a 25 = 108439101 ∧ a 26 = 131839241 :=
  ⟨val 1 141 (by norm_num) (by norm_num), val 2 1001 (by norm_num) (by norm_num),
    val 3 4621 (by norm_num) (by norm_num), val 4 15681 (by norm_num) (by norm_num),
    val 5 42821 (by norm_num) (by norm_num), val 6 99961 (by norm_num) (by norm_num),
    val 7 207621 (by norm_num) (by norm_num), val 8 394241 (by norm_num) (by norm_num),
    val 9 697501 (by norm_num) (by norm_num), val 10 1165641 (by norm_num) (by norm_num),
    val 11 1858781 (by norm_num) (by norm_num), val 12 2850241 (by norm_num) (by norm_num),
    val 13 4227861 (by norm_num) (by norm_num), val 14 6095321 (by norm_num) (by norm_num),
    val 15 8573461 (by norm_num) (by norm_num), val 16 11801601 (by norm_num) (by norm_num),
    val 17 15938861 (by norm_num) (by norm_num), val 18 21165481 (by norm_num) (by norm_num),
    val 19 27684141 (by norm_num) (by norm_num), val 20 35721281 (by norm_num) (by norm_num),
    val 21 45528421 (by norm_num) (by norm_num), val 22 57383481 (by norm_num) (by norm_num),
    val 23 71592101 (by norm_num) (by norm_num), val 24 88488961 (by norm_num) (by norm_num),
    val 25 108439101 (by norm_num) (by norm_num), val 26 131839241 (by norm_num) (by norm_num)⟩

/-- Both of Barker's conjectures. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 6 =
      X * (141 + 155 * X + 730 * X ^ 2 + 150 * X ^ 3 + 145 * X ^ 4 - X ^ 5) ∧
    (∀ n : ℕ, 6 < n →
      (a n : ℤ) = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) - 15 * a (n - 4) + 6 * a (n - 5) - a (n - 6)) :=
  ⟨gf, recurrence⟩

end OMA.S_oeis_a201814

theorem OMA.solution : type_of% @OMA.S_oeis_a201814.main :=
  OMA.S_oeis_a201814.conjecture
