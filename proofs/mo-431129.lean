import OMAStatements.S_mo_431129

open OMA.S_mo_431129 Matrix Polynomial

namespace PowerSumLowerBound

/-- Polynomial evaluation of a `Part k`-indexed coefficient vector on a moment vector `m`. -/
def evalForm {k : ℕ} (a : Part k → ℝ) (m : Fin k → ℝ) : ℝ :=
  ∑ e : Part k, a e * ∏ j : Fin k, (m j) ^ (e.val j).val

lemma form_eq_evalForm {k n : ℕ} (a : Part k → ℝ) (x : Fin n → ℝ) :
    form a x = evalForm a (fun j ↦ moment x (j.val + 1)) := rfl

/-- A 1-variable polynomial of degree `≤ k` vanishing on `k + 1` distinct points is zero. -/
lemma coeff_eq_zero_of_eval_grid_zero {k : ℕ} (b : Fin (k + 1) → ℝ) (pts : Fin (k + 1) → ℝ)
    (hpts : Function.Injective pts)
    (hzero : ∀ s : Fin (k + 1), ∑ r : Fin (k + 1), b r * (pts s) ^ r.val = 0) :
    ∀ r : Fin (k + 1), b r = 0 := by
  let p : ℝ[X] := ∑ r : Fin (k + 1), C (b r) * X ^ r.val
  have hp_coeff : ∀ r : Fin (k + 1), p.coeff r.val = b r := fun r ↦ by
    dsimp [p]
    rw [Polynomial.finsetSum_coeff]
    rw [Finset.sum_eq_single r]
    · simp
    · intro j _ hjr
      have hne : r.val ≠ j.val := fun h ↦ hjr (Fin.ext h.symm)
      simp [hne]
    · intro h; exact absurd (Finset.mem_univ r) h
  have hp_eval : ∀ s : Fin (k + 1), p.eval (pts s) = 0 := fun s ↦ by
    dsimp [p]
    rw [Polynomial.eval_finsetSum]
    simpa [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X] using hzero s
  have hp_deg : p.natDegree ≤ k := by
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun r _ ↦ ?_
    calc
      (C (b r) * X ^ r.val).natDegree ≤ (C (b r)).natDegree + (X ^ r.val).natDegree :=
        Polynomial.natDegree_mul_le
      _ = r.val := by simp
      _ ≤ k := Nat.le_of_lt_succ r.isLt
  have hp0 : p = 0 := by
    by_contra hne
    have hsub : (Finset.univ.image pts) ⊆ p.roots.toFinset := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨s, _, rfl⟩
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hne]
      exact hp_eval s
    have hcard1 : (Finset.univ.image pts).card = k + 1 := by
      rw [Finset.card_image_of_injective _ hpts, Finset.card_univ, Fintype.card_fin]
    have hcard2 : p.roots.toFinset.card ≤ p.roots.card := Multiset.toFinset_card_le _
    have hcard3 : p.roots.card ≤ p.natDegree := Polynomial.card_roots' p
    have hle := Finset.card_le_card hsub
    omega
  intro r
  rw [← hp_coeff r, hp0, Polynomial.coeff_zero]

/-- Multivariate vanishing on a `(k + 1)`-point Cartesian grid forces all coefficients to be zero. -/
lemma multivar_coeff_eq_zero_of_grid_zero {k : ℕ} :
    ∀ (d : ℕ) (pts : Fin d → Fin (k + 1) → ℝ), (∀ j, Function.Injective (pts j)) →
    ∀ (c : (Fin d → Fin (k + 1)) → ℝ),
    (∀ idx : Fin d → Fin (k + 1),
      ∑ α : Fin d → Fin (k + 1), c α * ∏ j : Fin d, (pts j (idx j)) ^ (α j).val = 0) →
    ∀ α : Fin d → Fin (k + 1), c α = 0 := by
  intro d
  induction d with
  | zero =>
    intro _ _ c hzero α
    have h0 := hzero Fin.elim0
    have huniq : ∀ β : Fin 0 → Fin (k + 1), β = α := fun β ↦ Subsingleton.elim β α
    rw [Finset.sum_eq_single α] at h0
    · simpa using h0
    · intro β _ hne; exact absurd (huniq β) hne
    · intro h; exact absurd (Finset.mem_univ α) h
  | succ d ih =>
    intro pts hpts c hzero α
    let eEquiv : (Fin (k + 1) × (Fin d → Fin (k + 1))) ≃ (Fin (d + 1) → Fin (k + 1)) :=
      { toFun := fun p ↦ Fin.cons p.1 p.2
        invFun := fun f ↦ (f 0, fun j ↦ f j.succ)
        left_inv := fun ⟨r, β⟩ ↦ by ext <;> simp
        right_inv := fun f ↦ by
          ext j
          refine Fin.cases ?_ ?_ j <;> simp }
    have hslice : ∀ (r : Fin (k + 1)) (idx' : Fin d → Fin (k + 1)),
        ∑ β : Fin d → Fin (k + 1),
          c (Fin.cons r β) * ∏ j : Fin d, (pts j.succ (idx' j)) ^ (β j).val = 0 := by
      intro r idx'
      let b : Fin (k + 1) → ℝ := fun r' ↦
        ∑ β : Fin d → Fin (k + 1),
          c (Fin.cons r' β) * ∏ j : Fin d, (pts j.succ (idx' j)) ^ (β j).val
      refine coeff_eq_zero_of_eval_grid_zero b (pts 0) (hpts 0) (fun s ↦ ?_) r
      let idxAll : Fin (d + 1) → Fin (k + 1) := Fin.cons s idx'
      have h0 : ∑ p : Fin (k + 1) × (Fin d → Fin (k + 1)),
          c (eEquiv p) * ∏ j : Fin (d + 1), (pts j (idxAll j)) ^ (eEquiv p j).val = 0 := by
        rw [Fintype.sum_equiv eEquiv _
          (fun f ↦ c f * ∏ j : Fin (d + 1), (pts j (idxAll j)) ^ (f j).val)
          (fun _ ↦ rfl)]
        exact hzero idxAll
      rw [Fintype.sum_prod_type] at h0
      rw [← h0]
      refine Finset.sum_congr rfl fun r' _ ↦ ?_
      dsimp [b, eEquiv, idxAll]
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun β _ ↦ ?_
      rw [Fin.prod_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      ring
    have hcons : α = Fin.cons (α 0) (fun j ↦ α j.succ) := by
      ext j; refine Fin.cases ?_ ?_ j <;> simp
    rw [hcons]
    exact ih (fun j ↦ pts j.succ) (fun j ↦ hpts j.succ)
      (fun β ↦ c (Fin.cons (α 0) β)) (hslice (α 0)) (fun j ↦ α j.succ)

/-- Moment matrix `V j r = ((r + 1) / k) ^ (j + 1)` on `Fin k`. -/
noncomputable def momentMat (k : ℕ) : Matrix (Fin k) (Fin k) ℝ :=
  fun j r ↦ (((r.val + 1 : ℕ) : ℝ) / (k : ℝ)) ^ (j.val + 1)

lemma momentMat_det_ne_zero {k : ℕ} (hk : 0 < k) : (momentMat k).det ≠ 0 := by
  let u : Fin k → ℝ := fun r ↦ ((r.val + 1 : ℕ) : ℝ) / (k : ℝ)
  have hu_pos : ∀ r : Fin k, 0 < u r := fun r ↦ by
    dsimp [u]
    exact div_pos (by positivity) (by exact_mod_cast hk)
  have hu_strict : StrictMono u := by
    intro a b hab
    dsimp [u]
    apply div_lt_div_of_pos_right _ (by exact_mod_cast hk)
    exact_mod_cast Nat.succ_lt_succ hab
  have hfac : momentMat k = (Matrix.vandermonde u)ᵀ * Matrix.diagonal u := by
    ext j r
    simp only [momentMat, Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.vandermonde_apply,
      pow_succ, u]
  rw [hfac, Matrix.det_mul, Matrix.det_transpose, Matrix.det_vandermonde, Matrix.det_diagonal]
  refine mul_ne_zero ?_ ?_
  · refine Finset.prod_ne_zero_iff.mpr fun i _ ↦ Finset.prod_ne_zero_iff.mpr fun j hj ↦ ?_
    have hij : i < j := (Finset.mem_Ioi.mp hj)
    exact sub_ne_zero.mpr (hu_strict hij).ne'
  · exact Finset.prod_ne_zero_iff.mpr fun r _ ↦ (hu_pos r).ne'

/-- Difference of products of `k` numbers in `[-1, 1]` is Lipschitz with constant `k`. -/
lemma abs_prod_pow_sub_le {k : ℕ} (e : Part k) {m m' : Fin k → ℝ}
    (hm : ∀ j, |m j| ≤ 1) (hm' : ∀ j, |m' j| ≤ 1) {δ : ℝ} (hδ : 0 ≤ δ)
    (hdiff : ∀ j, |m j - m' j| ≤ δ) :
    |(∏ j : Fin k, (m j) ^ (e.val j).val) - ∏ j : Fin k, (m' j) ^ (e.val j).val| ≤ (k : ℝ) * δ := by
  have hpow_le : ∀ (a b : ℝ) (p : ℕ), |a| ≤ 1 → |b| ≤ 1 → |a - b| ≤ δ →
      |a ^ p - b ^ p| ≤ (p : ℝ) * δ := by
    intro a b p ha hb hab
    induction p with
    | zero => simp
    | succ p ih =>
      have hsplit : a ^ (p + 1) - b ^ (p + 1) = a * (a ^ p - b ^ p) + (a - b) * b ^ p := by ring
      rw [hsplit]
      have hbp : |b ^ p| ≤ 1 := by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg b) hb
      calc
        |a * (a ^ p - b ^ p) + (a - b) * b ^ p|
            ≤ |a * (a ^ p - b ^ p)| + |(a - b) * b ^ p| := abs_add_le _ _
        _ = |a| * |a ^ p - b ^ p| + |a - b| * |b ^ p| := by rw [abs_mul, abs_mul]
        _ ≤ 1 * ((p : ℝ) * δ) + δ * 1 := by gcongr
        _ = ((p + 1 : ℕ) : ℝ) * δ := by push_cast; ring
  have hprod_aux : ∀ (s : Finset (Fin k)),
      |(∏ j ∈ s, (m j) ^ (e.val j).val) - ∏ j ∈ s, (m' j) ^ (e.val j).val| ≤
        (∑ j ∈ s, ((e.val j).val : ℝ)) * δ := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
      have hsplit : (m a) ^ (e.val a).val * (∏ j ∈ s, (m j) ^ (e.val j).val) -
          (m' a) ^ (e.val a).val * (∏ j ∈ s, (m' j) ^ (e.val j).val) =
          (m a) ^ (e.val a).val * ((∏ j ∈ s, (m j) ^ (e.val j).val) - ∏ j ∈ s, (m' j) ^ (e.val j).val) +
          ((m a) ^ (e.val a).val - (m' a) ^ (e.val a).val) * (∏ j ∈ s, (m' j) ^ (e.val j).val) := by
        ring
      rw [hsplit]
      have hma : |(m a) ^ (e.val a).val| ≤ 1 := by
        rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) (hm a)
      have hpm' : |∏ j ∈ s, (m' j) ^ (e.val j).val| ≤ 1 := by
        rw [Finset.abs_prod]
        refine Finset.prod_le_one (fun j _ ↦ abs_nonneg _) fun j _ ↦ ?_
        rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) (hm' j)
      have hda : |(m a) ^ (e.val a).val - (m' a) ^ (e.val a).val| ≤ ((e.val a).val : ℝ) * δ :=
        hpow_le (m a) (m' a) (e.val a).val (hm a) (hm' a) (hdiff a)
      calc
        |(m a) ^ (e.val a).val * ((∏ j ∈ s, (m j) ^ (e.val j).val) - ∏ j ∈ s, (m' j) ^ (e.val j).val) +
            ((m a) ^ (e.val a).val - (m' a) ^ (e.val a).val) * (∏ j ∈ s, (m' j) ^ (e.val j).val)|
            ≤ |(m a) ^ (e.val a).val * ((∏ j ∈ s, (m j) ^ (e.val j).val) - ∏ j ∈ s, (m' j) ^ (e.val j).val)| +
              |((m a) ^ (e.val a).val - (m' a) ^ (e.val a).val) * (∏ j ∈ s, (m' j) ^ (e.val j).val)| :=
              abs_add_le _ _
        _ = |(m a) ^ (e.val a).val| * |(∏ j ∈ s, (m j) ^ (e.val j).val) - ∏ j ∈ s, (m' j) ^ (e.val j).val| +
            |(m a) ^ (e.val a).val - (m' a) ^ (e.val a).val| * |∏ j ∈ s, (m' j) ^ (e.val j).val| := by
              rw [abs_mul, abs_mul]
        _ ≤ 1 * ((∑ j ∈ s, ((e.val j).val : ℝ)) * δ) + (((e.val a).val : ℝ) * δ) * 1 := by gcongr
        _ = (((e.val a).val : ℝ) + ∑ j ∈ s, ((e.val j).val : ℝ)) * δ := by ring
  have hsum_le : (∑ j : Fin k, ((e.val j).val : ℝ)) ≤ (k : ℝ) := by
    have hnat : ∑ j : Fin k, (e.val j).val ≤ k := by
      have h1 : ∑ j : Fin k, (e.val j).val ≤ ∑ j : Fin k, (j.val + 1) * (e.val j).val := by
        refine Finset.sum_le_sum fun j _ ↦ ?_
        exact Nat.le_mul_of_pos_left _ (Nat.succ_pos j.val)
      exact h1.trans (le_of_eq e.property)
    exact_mod_cast hnat
  calc
    |(∏ j : Fin k, (m j) ^ (e.val j).val) - ∏ j : Fin k, (m' j) ^ (e.val j).val|
        ≤ (∑ j : Fin k, ((e.val j).val : ℝ)) * δ := hprod_aux Finset.univ
    _ ≤ (k : ℝ) * δ := mul_le_mul_of_nonneg_right hsum_le hδ

/-- Rounding any weight vector `w ∈ [0, 1/k]^k` to an `n`-point empirical distribution in `[0, 1]^n`. -/
lemma exists_sample_approx {k n : ℕ} (hk : 0 < k) (hn : 0 < n) (w : Fin k → ℝ)
    (hw : ∀ r : Fin k, w r ∈ Set.Icc (0 : ℝ) (1 / (k : ℝ))) :
    ∃ x : Fin n → ℝ, (∀ i, x i ∈ Set.Icc (-1 : ℝ) 1) ∧
      ∀ j : Fin k, |moment x (j.val + 1) - (momentMat k *ᵥ w) j| ≤ (k : ℝ) / (n : ℝ) := by
  let c : Fin k → ℕ := fun r ↦ Nat.floor ((n : ℝ) * w r)
  have hc_le_real : ∀ r : Fin k, (c r : ℝ) ≤ (n : ℝ) * w r := fun r ↦
    Nat.floor_le (mul_nonneg (Nat.cast_nonneg n) (hw r).1)
  have hc_gt_real : ∀ r : Fin k, (n : ℝ) * w r - 1 < (c r : ℝ) := fun r ↦ by
    have h := Nat.lt_floor_add_one ((n : ℝ) * w r)
    linarith
  have hsum_c : ∑ r : Fin k, c r ≤ n := by
    have hreal : ((∑ r : Fin k, c r : ℕ) : ℝ) ≤ (n : ℝ) := by
      push_cast
      calc
        ∑ r : Fin k, (c r : ℝ) ≤ ∑ r : Fin k, (n : ℝ) * w r :=
          Finset.sum_le_sum fun r _ ↦ hc_le_real r
        _ ≤ ∑ _r : Fin k, (n : ℝ) * (1 / (k : ℝ)) := by
              refine Finset.sum_le_sum fun r _ ↦ mul_le_mul_of_nonneg_left (hw r).2 (Nat.cast_nonneg n)
        _ = (k : ℝ) * ((n : ℝ) * (1 / (k : ℝ))) := by simp
        _ = (n : ℝ) := by
              have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
              field_simp [hk0]
    exact_mod_cast hreal
  -- Prefix sums `pref r = ∑_{s < r} c s`
  let pref : Fin (k + 1) → ℕ := fun r ↦ ∑ s : Fin k, if s.val < r.val then c s else 0
  have hpref_mono : ∀ r : Fin k, pref r.castSucc + c r = pref r.succ := fun r ↦ by
    dsimp [pref]
    have hsplit : ∀ s : Fin k, (if s.val < r.val + 1 then c s else 0) =
        (if s.val < r.val then c s else 0) + (if s = r then c s else 0) := fun s ↦ by
      by_cases hlt : s.val < r.val
      · have hne : s ≠ r := fun h ↦ by subst h; omega
        simp [hlt, hne, show s.val < r.val + 1 by omega]
      · by_cases heq : s = r
        · subst heq; simp
        · have hgt : ¬ s.val < r.val + 1 := by
            intro h; apply heq; exact Fin.ext (by omega)
          rw [if_neg hgt, if_neg hlt, if_neg heq, add_zero]
    simp_rw [hsplit]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
    simp
  have hpref_le : ∀ r : Fin (k + 1), pref r ≤ n := fun r ↦ by
    calc
      pref r ≤ ∑ s : Fin k, c s := Finset.sum_le_sum fun s _ ↦ by split_ifs <;> omega
      _ ≤ n := hsum_c
  have hpref_strict_mono : ∀ a b : Fin (k + 1), a ≤ b → pref a ≤ pref b := fun a b hab ↦ by
    refine Finset.sum_le_sum fun s _ ↦ ?_
    by_cases ha : s.val < a.val
    · have hb : s.val < b.val := lt_of_lt_of_le ha hab
      simp [ha, hb]
    · simp [ha]
  let u : Fin k → ℝ := fun r ↦ ((r.val + 1 : ℕ) : ℝ) / (k : ℝ)
  let x : Fin n → ℝ := fun i ↦
    if h : ∃ r : Fin k, pref r.castSucc ≤ i.val ∧ i.val < pref r.succ then u h.choose else 0
  have hx_mem : ∀ i : Fin n, x i ∈ Set.Icc (-1 : ℝ) 1 := fun i ↦ by
    dsimp [x]
    split_ifs with h
    · dsimp [u]
      have h1 : (0 : ℝ) ≤ ((h.choose.val + 1 : ℕ) : ℝ) / (k : ℝ) := by positivity
      have h2 : ((h.choose.val + 1 : ℕ) : ℝ) / (k : ℝ) ≤ 1 := by
        rw [div_le_one (by exact_mod_cast hk)]
        exact_mod_cast Nat.succ_le_of_lt h.choose.isLt
      exact ⟨by linarith, h2⟩
    · exact ⟨by norm_num, by norm_num⟩
  have hdisj : ∀ (r₁ r₂ : Fin k) (i : Fin n),
      pref r₁.castSucc ≤ i.val → i.val < pref r₁.succ →
      pref r₂.castSucc ≤ i.val → i.val < pref r₂.succ → r₁ = r₂ := by
    intro r₁ r₂ i h1a h1b h2a h2b
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hle : pref r₁.succ ≤ pref r₂.castSucc :=
        hpref_strict_mono r₁.succ r₂.castSucc (by show r₁.val + 1 ≤ r₂.val; omega)
      omega
    · have hle : pref r₂.succ ≤ pref r₁.castSucc :=
        hpref_strict_mono r₂.succ r₁.castSucc (by show r₂.val + 1 ≤ r₁.val; omega)
      omega
  have hx_on_block : ∀ (r : Fin k) (i : Fin n),
      pref r.castSucc ≤ i.val → i.val < pref r.succ → x i = u r := fun r i hlo hhi ↦ by
    dsimp [x]
    have hex : ∃ r' : Fin k, pref r'.castSucc ≤ i.val ∧ i.val < pref r'.succ := ⟨r, hlo, hhi⟩
    rw [dif_pos hex]
    have heq : hex.choose = r := hdisj hex.choose r i hex.choose_spec.1 hex.choose_spec.2 hlo hhi
    rw [heq]
  have hblock_card : ∀ r : Fin k,
      (Finset.univ.filter fun i : Fin n ↦ pref r.castSucc ≤ i.val ∧ i.val < pref r.succ).card = c r := by
    intro r
    have hbij : (Finset.univ.filter fun i : Fin n ↦ pref r.castSucc ≤ i.val ∧ i.val < pref r.succ).card =
        (Finset.Ico (pref r.castSucc) (pref r.succ)).card := by
      refine Finset.card_bij (fun i _ ↦ i.val) ?_ ?_ ?_
      · intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        exact Finset.mem_Ico.mpr hi
      · intro a _ b _ hab; exact Fin.ext hab
      · intro m hm
        rcases Finset.mem_Ico.mp hm with ⟨hlo, hhi⟩
        have hlt : m < n := lt_of_lt_of_le hhi (hpref_le r.succ)
        exact ⟨⟨m, hlt⟩, by simp [hlo, hhi], rfl⟩
    rw [hbij, Nat.card_Ico]
    have h := hpref_mono r
    omega
  refine ⟨x, hx_mem, fun j ↦ ?_⟩
  have hsum_x : ∑ i : Fin n, (x i) ^ (j.val + 1) = ∑ r : Fin k, (c r : ℝ) * (u r) ^ (j.val + 1) := by
    let B : Fin k → Finset (Fin n) := fun r ↦
      Finset.univ.filter fun i : Fin n ↦ pref r.castSucc ≤ i.val ∧ i.val < pref r.succ
    have hB_disj : Set.PairwiseDisjoint (Set.univ : Set (Fin k)) B := by
      intro r₁ _ r₂ _ hne
      change Disjoint (B r₁) (B r₂)
      rw [Finset.disjoint_left]
      intro i h1 h2
      simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
      exact hne (hdisj r₁ r₂ i h1.1 h1.2 h2.1 h2.2)
    have hzero_out : ∀ i : Fin n, i ∉ Finset.univ.biUnion B → (x i) ^ (j.val + 1) = 0 := by
      intro i hi
      have hno : ¬ ∃ r : Fin k, pref r.castSucc ≤ i.val ∧ i.val < pref r.succ := by
        rintro ⟨r, hlo, hhi⟩
        apply hi
        exact Finset.mem_biUnion.mpr ⟨r, Finset.mem_univ r, by simp [B, hlo, hhi]⟩
      have hx0 : x i = 0 := by dsimp [x]; rw [dif_neg hno]
      rw [hx0, zero_pow (Nat.succ_ne_zero j.val)]
    calc
      ∑ i : Fin n, (x i) ^ (j.val + 1)
          = ∑ i ∈ Finset.univ.biUnion B, (x i) ^ (j.val + 1) := by
            refine (Finset.sum_subset (Finset.subset_univ _) fun i _ hi ↦ hzero_out i hi).symm
      _ = ∑ r : Fin k, ∑ i ∈ B r, (x i) ^ (j.val + 1) := Finset.sum_biUnion (by
            intro r₁ _ r₂ _ hne; exact hB_disj (Set.mem_univ r₁) (Set.mem_univ r₂) hne)
      _ = ∑ r : Fin k, (c r : ℝ) * (u r) ^ (j.val + 1) := by
            refine Finset.sum_congr rfl fun r _ ↦ ?_
            have hconst : ∀ i ∈ B r, (x i) ^ (j.val + 1) = (u r) ^ (j.val + 1) := fun i hi ↦ by
              simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at hi
              rw [hx_on_block r i hi.1 hi.2]
            rw [Finset.sum_congr rfl hconst, Finset.sum_const, hblock_card r, nsmul_eq_mul]
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  unfold moment
  rw [hsum_x, Finset.sum_div]
  simp only [Matrix.mulVec, dotProduct, momentMat]
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ r : Fin k, ((c r : ℝ) * (u r) ^ (j.val + 1) / (n : ℝ) -
        (((r.val + 1 : ℕ) : ℝ) / (k : ℝ)) ^ (j.val + 1) * w r)|
        ≤ ∑ r : Fin k, |(c r : ℝ) * (u r) ^ (j.val + 1) / (n : ℝ) -
            (u r) ^ (j.val + 1) * w r| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _r : Fin k, (1 : ℝ) / (n : ℝ) := by
          refine Finset.sum_le_sum fun r _ ↦ ?_
          have hfac : (c r : ℝ) * (u r) ^ (j.val + 1) / (n : ℝ) - (u r) ^ (j.val + 1) * w r =
              (u r) ^ (j.val + 1) * ((c r : ℝ) / (n : ℝ) - w r) := by ring
          rw [hfac, abs_mul]
          have hu_le : |(u r) ^ (j.val + 1)| ≤ 1 := by
            have hu0 : 0 ≤ u r := by dsimp [u]; positivity
            have hu1 : u r ≤ 1 := by
              dsimp [u]
              rw [div_le_one (by exact_mod_cast hk)]
              exact_mod_cast Nat.succ_le_of_lt r.isLt
            rw [abs_of_nonneg (pow_nonneg hu0 _)]
            exact pow_le_one₀ hu0 hu1
          have hdiff : |(c r : ℝ) / (n : ℝ) - w r| ≤ 1 / (n : ℝ) := by
            rw [abs_le]
            have h1 := hc_le_real r
            have h2 := hc_gt_real r
            constructor
            · rw [le_sub_iff_add_le, le_div_iff₀ hn_pos]
              have h3 : (-(1 / (n : ℝ)) + w r) * (n : ℝ) = (n : ℝ) * w r - 1 := by
                field_simp [hn_pos.ne']; ring
              linarith
            · rw [sub_le_iff_le_add, div_le_iff₀ hn_pos]
              have h3 : (1 / (n : ℝ) + w r) * (n : ℝ) = 1 + (n : ℝ) * w r := by
                field_simp [hn_pos.ne']
              linarith
          calc
            |(u r) ^ (j.val + 1)| * |(c r : ℝ) / (n : ℝ) - w r|
                ≤ 1 * (1 / (n : ℝ)) := by gcongr
            _ = 1 / (n : ℝ) := one_mul _
    _ = (k : ℝ) / (n : ℝ) := by simp [div_eq_mul_inv]

lemma main_proof (k : ℕ) (hk : 0 < k) :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n ≥ N,
      ∀ a : Part k → ℝ, (∀ e, |a e| ≤ 1) → (∃ e, |a e| = 1) →
        ∃ x : Fin n → ℝ, (∀ i, x i ∈ Set.Icc (-1) 1) ∧ c ≤ |form a x| := by
  -- 1. Invertibility of momentMat k and existence of an open box in its image of [0, 1/k]^k
  let V : Matrix (Fin k) (Fin k) ℝ := momentMat k
  have hV_unit : IsUnit V.det := isUnit_iff_ne_zero.mpr (momentMat_det_ne_zero hk)
  let Vinv : Matrix (Fin k) (Fin k) ℝ := V⁻¹
  have hVVinv : V * Vinv = 1 := Matrix.mul_nonsing_inv V hV_unit
  let w0 : Fin k → ℝ := fun _ ↦ 1 / (2 * (k : ℝ))
  let m0 : Fin k → ℝ := V *ᵥ w0
  have hVinv_bound : ∃ L : ℝ, 0 < L ∧ ∀ v : Fin k → ℝ, ∀ r : Fin k,
      |(Vinv *ᵥ v) r| ≤ L * ∑ j : Fin k, |v j| := by
    let L : ℝ := 1 + ∑ r : Fin k, ∑ j : Fin k, |Vinv r j|
    refine ⟨L, by
      have hnn : 0 ≤ ∑ r : Fin k, ∑ j : Fin k, |Vinv r j| :=
        Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
      linarith, fun v r ↦ ?_⟩
    simp only [Matrix.mulVec, dotProduct]
    calc
      |∑ j : Fin k, Vinv r j * v j| ≤ ∑ j : Fin k, |Vinv r j * v j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j : Fin k, |Vinv r j| * |v j| := by simp_rw [abs_mul]
      _ ≤ ∑ j : Fin k, L * |v j| := by
            refine Finset.sum_le_sum fun j _ ↦ mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
            have h1 : |Vinv r j| ≤ ∑ j' : Fin k, |Vinv r j'| :=
              Finset.single_le_sum (fun j' _ ↦ abs_nonneg (Vinv r j')) (Finset.mem_univ j)
            have h2 : ∑ j' : Fin k, |Vinv r j'| ≤ ∑ r' : Fin k, ∑ j' : Fin k, |Vinv r' j'| :=
              Finset.single_le_sum (f := fun r' : Fin k ↦ ∑ j' : Fin k, |Vinv r' j'|)
                (fun r' _ ↦ Finset.sum_nonneg fun j' _ ↦ abs_nonneg _) (Finset.mem_univ r)
            dsimp [L]; linarith
      _ = L * ∑ j : Fin k, |v j| := (Finset.mul_sum _ _ _).symm
  rcases hVinv_bound with ⟨L, hL_pos, hL_bound⟩
  let δ : ℝ := 1 / (4 * (k : ℝ) * (k : ℝ) * L)
  have hδ_pos : 0 < δ := by
    have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    dsimp [δ]; positivity
  -- Grid points `pts j s = m0 j + (s / (k + 1)) * δ`
  let pts : Fin k → Fin (k + 1) → ℝ := fun j s ↦ m0 j + ((s.val : ℝ) / ((k + 1 : ℕ) : ℝ)) * δ
  have hpts_inj : ∀ j : Fin k, Function.Injective (pts j) := fun j a b hab ↦ by
    dsimp [pts] at hab
    have h1 : ((a.val : ℝ) / ((k + 1 : ℕ) : ℝ)) * δ = ((b.val : ℝ) / ((k + 1 : ℕ) : ℝ)) * δ := by
      linarith
    have h2 : (a.val : ℝ) / ((k + 1 : ℕ) : ℝ) = (b.val : ℝ) / ((k + 1 : ℕ) : ℝ) :=
      mul_right_cancel₀ hδ_pos.ne' h1
    have hk1_ne : (((k + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
    have h3 : (a.val : ℝ) = (b.val : ℝ) := (div_left_inj' hk1_ne).mp h2
    exact Fin.ext (by exact_mod_cast h3)
  let gridPt : (Fin k → Fin (k + 1)) → (Fin k → ℝ) := fun idx j ↦ pts j (idx j)
  -- Every grid point `gridPt idx` is `V *ᵥ w` for some `w ∈ [0, 1/k]^k`
  have hgrid_preimg : ∀ idx : Fin k → Fin (k + 1),
      ∃ w : Fin k → ℝ, (∀ r, w r ∈ Set.Icc (0 : ℝ) (1 / (k : ℝ))) ∧ V *ᵥ w = gridPt idx := by
    intro idx
    let diff : Fin k → ℝ := fun j ↦ gridPt idx j - m0 j
    let w : Fin k → ℝ := w0 + Vinv *ᵥ diff
    refine ⟨w, fun r ↦ ?_, ?_⟩
    · have hdiff_le : ∀ j : Fin k, |diff j| ≤ δ := fun j ↦ by
        dsimp [diff, gridPt, pts]
        have h0 : 0 ≤ ((idx j).val : ℝ) / ((k + 1 : ℕ) : ℝ) * δ := by positivity
        have h1 : ((idx j).val : ℝ) / ((k + 1 : ℕ) : ℝ) ≤ 1 := by
          rw [div_le_one (by positivity)]
          exact_mod_cast le_of_lt (idx j).isLt
        rw [add_sub_cancel_left, abs_of_nonneg h0]
        nlinarith
      have hpert : |(Vinv *ᵥ diff) r| ≤ 1 / (4 * (k : ℝ)) := by
        calc
          |(Vinv *ᵥ diff) r| ≤ L * ∑ j : Fin k, |diff j| := hL_bound diff r
          _ ≤ L * ∑ _j : Fin k, δ :=
                mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ ↦ hdiff_le j) hL_pos.le
          _ = L * ((k : ℝ) * δ) := by simp
          _ = 1 / (4 * (k : ℝ)) := by
                have hk_ne : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
                dsimp [δ]; field_simp [hk_ne, hL_pos.ne']
      have habs := abs_le.mp hpert
      have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
      have h14 : 1 / (4 * (k : ℝ)) ≤ 1 / (2 * (k : ℝ)) := by
        rw [one_div_le_one_div (by positivity) (by positivity)]; linarith
      have h34 : 1 / (2 * (k : ℝ)) + 1 / (4 * (k : ℝ)) ≤ 1 / (k : ℝ) := by
        have : 1 / (2 * (k : ℝ)) + 1 / (4 * (k : ℝ)) = 3 / (4 * (k : ℝ)) := by ring
        rw [this, div_le_div_iff₀ (by positivity) hk_pos]; linarith
      dsimp [w, w0]
      exact ⟨by linarith, by linarith⟩
    · dsimp [w]
      rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, hVVinv, Matrix.one_mulVec]
      ext j
      simp [diff, m0]
  -- 2. Compactness of the unit L∞ sphere `S` on `Part k → ℝ`
  let F : (Part k → ℝ) → ℝ := fun a ↦ ∑ idx : Fin k → Fin (k + 1), (evalForm a (gridPt idx)) ^ 2
  have hF_cont : Continuous F := by
    refine continuous_finsetSum _ fun idx _ ↦ ?_
    refine (continuous_finsetSum _ fun e _ ↦ ?_).pow 2
    exact (continuous_apply e).mul continuous_const
  let S : Set (Part k → ℝ) := {a | (∀ e, |a e| ≤ 1) ∧ ∃ e, |a e| = 1}
  have hPart_ne : Nonempty (Part k) := by
    let e0 : Fin k → Fin (k + 1) := fun j ↦
      if j.val = k - 1 then ⟨1, by omega⟩ else ⟨0, by omega⟩
    refine ⟨⟨e0, ?_⟩⟩
    rw [Finset.sum_eq_single ⟨k - 1, by omega⟩]
    · dsimp [e0]; simp; omega
    · intro j _ hj
      have hne : j.val ≠ k - 1 := fun h ↦ hj (Fin.ext h)
      dsimp [e0]; simp [hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hS_ne : S.Nonempty := by
    refine ⟨fun _ ↦ 1, fun _ ↦ by norm_num, ?_⟩
    rcases hPart_ne with ⟨e₀⟩
    exact ⟨e₀, by norm_num⟩
  have hS_closed : IsClosed S := by
    have h1 : IsClosed {a : Part k → ℝ | ∀ e, |a e| ≤ 1} := by
      have heq : {a : Part k → ℝ | ∀ e, |a e| ≤ 1} = ⋂ e : Part k, {a | |a e| ≤ 1} := by
        ext a; simp
      rw [heq]
      exact isClosed_iInter fun e ↦ isClosed_le (continuous_abs.comp (continuous_apply e)) continuous_const
    have h2 : IsClosed {a : Part k → ℝ | ∃ e, |a e| = 1} := by
      have heq : {a : Part k → ℝ | ∃ e, |a e| = 1} = ⋃ e : Part k, {a | |a e| = 1} := by
        ext a; simp
      rw [heq]
      exact isClosed_iUnion_of_finite fun e ↦
        isClosed_eq (continuous_abs.comp (continuous_apply e)) continuous_const
    exact h1.inter h2
  have hS_compact : IsCompact S := by
    let cube : Set (Part k → ℝ) := Set.pi Set.univ fun _ ↦ Set.Icc (-1 : ℝ) 1
    have hcube : IsCompact cube := isCompact_univ_pi fun _ ↦ isCompact_Icc
    exact hcube.of_isClosed_subset hS_closed fun a ha e _ ↦ abs_le.mp (ha.1 e)
  obtain ⟨a₀, ha₀_mem, ha₀_min⟩ := hS_compact.exists_isMinOn hS_ne hF_cont.continuousOn
  have hF_pos : 0 < F a₀ := by
    have hnn : 0 ≤ F a₀ := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
    refine lt_of_le_of_ne hnn fun h0 ↦ ?_
    have hall0 : ∀ idx : Fin k → Fin (k + 1), evalForm a₀ (gridPt idx) = 0 := fun idx ↦ by
      have hsq : (evalForm a₀ (gridPt idx)) ^ 2 = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg fun _ _ ↦ sq_nonneg _).mp h0.symm idx (Finset.mem_univ _)
      exact sq_eq_zero_iff.mp hsq
    let cExt : (Fin k → Fin (k + 1)) → ℝ := fun α ↦
      if h : ∑ j : Fin k, (j.val + 1) * (α j).val = k then a₀ ⟨α, h⟩ else 0
    have hcExt_zero : ∀ idx : Fin k → Fin (k + 1),
        ∑ α : Fin k → Fin (k + 1), cExt α * ∏ j : Fin k, (pts j (idx j)) ^ (α j).val = 0 := by
      intro idx
      rw [← hall0 idx]
      unfold evalForm
      have hsum_eq : ∑ α : Fin k → Fin (k + 1), cExt α * ∏ j : Fin k, (pts j (idx j)) ^ (α j).val =
          ∑ α ∈ Finset.univ.filter (fun α : Fin k → Fin (k + 1) ↦
            ∑ j : Fin k, (j.val + 1) * (α j).val = k),
            cExt α * ∏ j : Fin k, (pts j (idx j)) ^ (α j).val := by
        refine (Finset.sum_subset (Finset.filter_subset _ _) fun α _ hα ↦ ?_).symm
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hα
        dsimp [cExt]
        rw [dif_neg hα, zero_mul]
      rw [hsum_eq]
      refine Finset.sum_bij (fun α hα ↦ ⟨α, (Finset.mem_filter.mp hα).2⟩) ?_ ?_ ?_ ?_
      · intro _ _; exact Finset.mem_univ _
      · intro α₁ _ α₂ _ h; exact congr_arg Subtype.val h
      · intro e _
        exact ⟨e.val, Finset.mem_filter.mpr ⟨Finset.mem_univ _, e.property⟩, Subtype.eta e e.property⟩
      · intro α hα
        have hprop : ∑ j : Fin k, (j.val + 1) * (α j).val = k := (Finset.mem_filter.mp hα).2
        dsimp [cExt, gridPt]
        rw [dif_pos hprop]
    have hall_c0 := multivar_coeff_eq_zero_of_grid_zero k pts hpts_inj cExt hcExt_zero
    rcases ha₀_mem.2 with ⟨e₁, he₁⟩
    have hzero_e1 : a₀ e₁ = 0 := by
      have h := hall_c0 e₁.val
      dsimp [cExt] at h
      rw [dif_pos e₁.property] at h
      exact h
    rw [hzero_e1] at he₁
    norm_num at he₁
  -- 3. Extract `c > 0` and `N : ℕ`
  let Gcard : ℕ := Fintype.card (Fin k → Fin (k + 1))
  have hGcard_pos : (0 : ℝ) < (Gcard : ℝ) := by
    dsimp [Gcard]; rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]; positivity
  let c : ℝ := Real.sqrt (F a₀ / (Gcard : ℝ)) / 2
  have hc_pos : 0 < c := by
    dsimp [c]; exact div_pos (Real.sqrt_pos.mpr (div_pos hF_pos hGcard_pos)) (by norm_num)
  let Kconst : ℝ := (Fintype.card (Part k) : ℝ) * (k : ℝ) * (k : ℝ)
  let N : ℕ := max 1 (Nat.ceil (Kconst / c) + 1)
  refine ⟨c, hc_pos, N, fun n hn a ha_le ha_eq ↦ ?_⟩
  have hn_pos : 0 < n := by omega
  have ha_mem : a ∈ S := ⟨ha_le, ha_eq⟩
  have hFa_ge : F a₀ ≤ F a := isMinOn_iff.mp ha₀_min a ha_mem
  have hex_idx : ∃ idx : Fin k → Fin (k + 1), F a₀ / (Gcard : ℝ) ≤ (evalForm a (gridPt idx)) ^ 2 := by
    by_contra hlt
    push Not at hlt
    have hsum_lt : F a < ∑ _idx : Fin k → Fin (k + 1), F a₀ / (Gcard : ℝ) :=
      Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun idx _ ↦ hlt idx
    have hrhs : (∑ _idx : Fin k → Fin (k + 1), F a₀ / (Gcard : ℝ)) = F a₀ := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      change (Gcard : ℝ) * (F a₀ / (Gcard : ℝ)) = F a₀
      field_simp [hGcard_pos.ne']
    linarith
  rcases hex_idx with ⟨idx, hidx⟩
  have hval_ge : 2 * c ≤ |evalForm a (gridPt idx)| := by
    have hsq : (2 * c) ^ 2 = F a₀ / (Gcard : ℝ) := by
      dsimp [c]
      have h1 : 2 * (Real.sqrt (F a₀ / (Gcard : ℝ)) / 2) = Real.sqrt (F a₀ / (Gcard : ℝ)) := by ring
      rw [h1, Real.sq_sqrt (div_nonneg hF_pos.le hGcard_pos.le)]
    nlinarith [abs_nonneg (evalForm a (gridPt idx)), sq_abs (evalForm a (gridPt idx))]
  obtain ⟨w, hw_mem, hw_eq⟩ := hgrid_preimg idx
  obtain ⟨x, hx_mem, hx_approx⟩ := exists_sample_approx hk hn_pos w hw_mem
  refine ⟨x, hx_mem, ?_⟩
  have hm_le : ∀ j : Fin k, |moment x (j.val + 1)| ≤ 1 := fun j ↦ by
    unfold moment
    have hn_r : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
    rw [abs_div, abs_of_pos hn_r, div_le_one hn_r]
    calc
      |∑ i : Fin n, (x i) ^ (j.val + 1)| ≤ ∑ i : Fin n, |(x i) ^ (j.val + 1)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin n, (1 : ℝ) := by
            refine Finset.sum_le_sum fun i _ ↦ ?_
            rw [abs_pow]
            exact pow_le_one₀ (abs_nonneg _) (abs_le.mpr (hx_mem i))
      _ = (n : ℝ) := by simp
  have hg_le : ∀ j : Fin k, |gridPt idx j| ≤ 1 := fun j ↦ by
    rw [← hw_eq]
    simp only [Matrix.mulVec, dotProduct, V, momentMat]
    calc
      |∑ r : Fin k, (((r.val + 1 : ℕ) : ℝ) / (k : ℝ)) ^ (j.val + 1) * w r|
          ≤ ∑ r : Fin k, |(((r.val + 1 : ℕ) : ℝ) / (k : ℝ)) ^ (j.val + 1) * w r| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ r : Fin k, 1 / (k : ℝ) := by
            refine Finset.sum_le_sum fun r _ ↦ ?_
            rw [abs_mul]
            have hu0 : (0 : ℝ) ≤ ((r.val + 1 : ℕ) : ℝ) / (k : ℝ) := by positivity
            have hu1 : ((r.val + 1 : ℕ) : ℝ) / (k : ℝ) ≤ 1 := by
              rw [div_le_one (by exact_mod_cast hk)]
              exact_mod_cast Nat.succ_le_of_lt r.isLt
            have hpow1 : |(((r.val + 1 : ℕ) : ℝ) / (k : ℝ)) ^ (j.val + 1)| ≤ 1 := by
              rw [abs_of_nonneg (pow_nonneg hu0 _)]
              exact pow_le_one₀ hu0 hu1
            have hw1 : |w r| ≤ 1 / (k : ℝ) := by
              rw [abs_of_nonneg (hw_mem r).1]; exact (hw_mem r).2
            calc
              |(((r.val + 1 : ℕ) : ℝ) / (k : ℝ)) ^ (j.val + 1)| * |w r|
                  ≤ 1 * (1 / (k : ℝ)) := by gcongr
              _ = 1 / (k : ℝ) := one_mul _
      _ = 1 := by
            have hk_ne : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
            simp [hk_ne]
  have hform_diff : |form a x - evalForm a (gridPt idx)| ≤ Kconst / (n : ℝ) := by
    rw [form_eq_evalForm]
    unfold evalForm
    rw [← Finset.sum_sub_distrib]
    calc
      |∑ e : Part k, (a e * ∏ j : Fin k, (moment x (j.val + 1)) ^ (e.val j).val -
          a e * ∏ j : Fin k, (gridPt idx j) ^ (e.val j).val)|
          ≤ ∑ e : Part k, |a e * ((∏ j : Fin k, (moment x (j.val + 1)) ^ (e.val j).val) -
              ∏ j : Fin k, (gridPt idx j) ^ (e.val j).val)| := by
                have h := Finset.abs_sum_le_sum_abs (fun e : Part k ↦
                  a e * ∏ j : Fin k, (moment x (j.val + 1)) ^ (e.val j).val -
                  a e * ∏ j : Fin k, (gridPt idx j) ^ (e.val j).val) Finset.univ
                simpa [← mul_sub] using h
      _ ≤ ∑ _e : Part k, (k : ℝ) * ((k : ℝ) / (n : ℝ)) := by
            refine Finset.sum_le_sum fun e _ ↦ ?_
            rw [abs_mul]
            have hlip := abs_prod_pow_sub_le e hm_le hg_le (δ := (k : ℝ) / (n : ℝ))
              (by positivity) (fun j ↦ by rw [← hw_eq]; exact hx_approx j)
            calc
              |a e| * |(∏ j : Fin k, (moment x (j.val + 1)) ^ (e.val j).val) -
                  ∏ j : Fin k, (gridPt idx j) ^ (e.val j).val|
                  ≤ 1 * ((k : ℝ) * ((k : ℝ) / (n : ℝ))) :=
                    mul_le_mul (ha_le e) hlip (abs_nonneg _) zero_le_one
              _ = (k : ℝ) * ((k : ℝ) / (n : ℝ)) := one_mul _
      _ = Kconst / (n : ℝ) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
            dsimp [Kconst]; ring
  have herr_le : Kconst / (n : ℝ) ≤ c := by
    have hn_r : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
    have hn_ge : Kconst / c ≤ (n : ℝ) := by
      have h1 : Nat.ceil (Kconst / c) ≤ n := by omega
      exact (Nat.le_ceil _).trans (by exact_mod_cast h1)
    rw [div_le_iff₀ hn_r]
    have hmul := (div_le_iff₀ hc_pos).mp hn_ge
    linarith
  have htri := abs_sub_abs_le_abs_sub (evalForm a (gridPt idx)) (form a x)
  rw [abs_sub_comm] at htri
  linarith

end PowerSumLowerBound

theorem OMA.solution : type_of% @OMA.S_mo_431129.main :=
  PowerSumLowerBound.main_proof
