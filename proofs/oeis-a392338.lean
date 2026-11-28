import OMAStatements.S_oeis_a392338

namespace OMA.P_oeis_a392338

open Matrix BigOperators Finset
open OMA.S_oeis_a392338

private lemma fin_one_val {n : ℕ} [NeZero n] (hn : 2 ≤ n) : (1 : Fin n).val = 1 := by
  change 1 % n = 1
  exact Nat.mod_eq_of_lt (by omega)

private lemma fin_two_val {n : ℕ} [NeZero n] (hn : 3 ≤ n) : (2 : Fin n).val = 2 := by
  change 2 % n = 2
  exact Nat.mod_eq_of_lt (by omega)

private lemma sub_fin_val {n : ℕ} [NeZero n] (i j : Fin n) :
    (⟨(j.val + n - i.val) % n, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩ : Fin n) = j - i := by
  ext
  rw [Fin.val_sub]
  dsimp only
  have hi : i.val < n := i.isLt
  have hj : j.val < n := j.isLt
  by_cases h0 : i.val = 0
  · simp [h0]
  · have h1 : (n - i.val) % n = n - i.val := Nat.mod_eq_of_lt (by omega)
    have h2 : n - i.val + j.val = j.val + n - i.val := by omega
    rw [h2]

private lemma circulantMatrix_eq {n : ℕ} [NeZero n] (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    circulantMatrix n σ i j = ((σ (j - i)).val : ℤ) := by
  unfold circulantMatrix
  rw [sub_fin_val]

private lemma sum_fin_val_odd (m : ℕ) :
    ∑ x : Fin (2 * m + 1), (x.val : ℤ) = (m : ℤ) * (2 * m + 1 : ℤ) := by
  have hnat : ∑ x : Fin (2 * m + 1), x.val = m * (2 * m + 1) := by
    rw [Fin.sum_univ_eq_sum_range (fun k => k)]
    have h2 := Finset.sum_range_id_mul_two (2 * m + 1)
    have h3 : (2 * m + 1) * (2 * m + 1 - 1) = (m * (2 * m + 1)) * 2 := by
      rw [show 2 * m + 1 - 1 = 2 * m by omega]; ring
    linarith
  exact_mod_cast hnat

private lemma circulant_row_sum (m : ℕ) (σ : Equiv.Perm (Fin (2 * m + 1)))
    (i : Fin (2 * m + 1)) :
    ∑ j : Fin (2 * m + 1), circulantMatrix (2 * m + 1) σ i j =
      (m : ℤ) * (2 * m + 1 : ℤ) := by
  simp_rw [circulantMatrix_eq]
  let e : Fin (2 * m + 1) ≃ Fin (2 * m + 1) := (Equiv.subRight i).trans σ
  have h : ∑ j : Fin (2 * m + 1), ((σ (j - i)).val : ℤ) =
      ∑ x : Fin (2 * m + 1), (x.val : ℤ) :=
    Equiv.sum_comp e (fun x : Fin (2 * m + 1) => (x.val : ℤ))
  rw [h, sum_fin_val_odd]

private lemma circulant_col_sum (m : ℕ) (σ : Equiv.Perm (Fin (2 * m + 1)))
    (j : Fin (2 * m + 1)) :
    ∑ i : Fin (2 * m + 1), circulantMatrix (2 * m + 1) σ i j =
      (m : ℤ) * (2 * m + 1 : ℤ) := by
  simp_rw [circulantMatrix_eq]
  let e : Fin (2 * m + 1) ≃ Fin (2 * m + 1) := (Equiv.subLeft j).trans σ
  have h : ∑ i : Fin (2 * m + 1), ((σ (j - i)).val : ℤ) =
      ∑ x : Fin (2 * m + 1), (x.val : ℤ) :=
    Equiv.sum_comp e (fun x : Fin (2 * m + 1) => (x.val : ℤ))
  rw [h, sum_fin_val_odd]

private lemma det_updateRow_univ_sum {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (i₀ : Fin n) :
    (M.updateRow i₀ (fun j => ∑ i : Fin n, M i j)).det = M.det := by
  have hrow : (fun j => ∑ i : Fin n, M i j) = ∑ i : Fin n, (1 : ℤ) • M i := by
    ext j; rw [Finset.sum_apply]; simp
  rw [hrow, Matrix.det_updateRow_sum, one_smul]

private lemma det_updateCol_univ_sum {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (j₀ : Fin n) :
    (M.updateCol j₀ (fun i => ∑ j : Fin n, M i j)).det = M.det := by
  have h1 : (M.updateCol j₀ (fun i => ∑ j : Fin n, M i j))ᵀ =
      Mᵀ.updateRow j₀ (fun i => ∑ j : Fin n, Mᵀ j i) := by
    ext a b
    by_cases h : a = j₀
    · subst h; simp
    · simp [h]
  rw [← Matrix.det_transpose, h1, det_updateRow_univ_sum, Matrix.det_transpose]

private lemma circulant_det_dvd_odd (m : ℕ) (σ : Equiv.Perm (Fin (2 * m + 1))) :
    ((m : ℤ) * ((2 * m + 1 : ℤ) ^ 2)) ∣ (circulantMatrix (2 * m + 1) σ).det := by
  let C := circulantMatrix (2 * m + 1) σ
  let B : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) ℤ := C.updateRow 0 (fun _ => 1)
  have h1 : C.det = ((m : ℤ) * (2 * m + 1 : ℤ)) * B.det := by
    have hsum : C.updateRow 0 (fun j => ∑ i : Fin (2 * m + 1), C i j) =
        B.updateRow 0 (((m : ℤ) * (2 * m + 1 : ℤ)) • (fun _ : Fin (2 * m + 1) => (1 : ℤ))) := by
      ext i j
      by_cases hi : i = 0
      · subst hi
        simp only [Matrix.updateRow_self, Pi.smul_apply, smul_eq_mul, mul_one]
        exact circulant_col_sum m σ j
      · simp [B, hi]
    calc C.det = (C.updateRow 0 (fun j => ∑ i : Fin (2 * m + 1), C i j)).det :=
          (det_updateRow_univ_sum C 0).symm
      _ = (B.updateRow 0 (((m : ℤ) * (2 * m + 1 : ℤ)) • (fun _ : Fin (2 * m + 1) => (1 : ℤ)))).det := by
          rw [hsum]
      _ = ((m : ℤ) * (2 * m + 1 : ℤ)) * (B.updateRow 0 (fun _ => 1)).det :=
          Matrix.det_updateRow_smul _ _ _ _
      _ = ((m : ℤ) * (2 * m + 1 : ℤ)) * B.det := by
        have hB : B.updateRow 0 (fun _ => 1) = B := by ext i j; by_cases hi : i = 0 <;> simp [B, hi]
        rw [hB]
  let B' : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) ℤ :=
    B.updateCol 0 (fun i => if i = 0 then 1 else (m : ℤ))
  have h2 : B.det = (2 * m + 1 : ℤ) * B'.det := by
    have hcol : B.updateCol 0 (fun i => ∑ j : Fin (2 * m + 1), B i j) =
        B'.updateCol 0 ((2 * m + 1 : ℤ) • (fun i : Fin (2 * m + 1) => if i = 0 then (1 : ℤ) else (m : ℤ))) := by
      ext i j
      by_cases hj : j = 0
      · subst hj
        simp only [Matrix.updateCol_self, Pi.smul_apply, smul_eq_mul]
        by_cases hi : i = 0
        · subst hi
          simp [B]
        · simp only [hi, ↓reduceIte]
          have hBi : ∀ x : Fin (2 * m + 1), B i x = circulantMatrix (2 * m + 1) σ i x := by
            intro x; simp [B, C, hi]
          simp_rw [hBi]
          rw [circulant_row_sum m σ i]
          ring
      · simp [B', hj]
    calc B.det = (B.updateCol 0 (fun i => ∑ j : Fin (2 * m + 1), B i j)).det :=
          (det_updateCol_univ_sum B 0).symm
      _ = (B'.updateCol 0 ((2 * m + 1 : ℤ) •
            (fun i : Fin (2 * m + 1) => if i = 0 then (1 : ℤ) else (m : ℤ)))).det := by rw [hcol]
      _ = (2 * m + 1 : ℤ) * (B'.updateCol 0 (fun i => if i = 0 then (1 : ℤ) else (m : ℤ))).det :=
          Matrix.det_updateCol_smul _ _ _ _
      _ = (2 * m + 1 : ℤ) * B'.det := by
        have hB' : B'.updateCol 0 (fun i => if i = 0 then (1 : ℤ) else (m : ℤ)) = B' := by
          ext i j; by_cases hj : j = 0 <;> simp [B', hj]
        rw [hB']
  refine ⟨B'.det, ?_⟩
  rw [h1, h2]
  ring

private lemma circulant_det_lower_bound (m : ℕ) (σ : Equiv.Perm (Fin (2 * m + 1)))
    (hdet : (circulantMatrix (2 * m + 1) σ).det ≠ 0) :
    a084367 m ≤ (circulantMatrix (2 * m + 1) σ).det.natAbs := by
  obtain ⟨q, hq⟩ := circulant_det_dvd_odd m σ
  have hq0 : q ≠ 0 := by
    intro h0; apply hdet; rw [hq, h0, mul_zero]
  have habs : (circulantMatrix (2 * m + 1) σ).det.natAbs = a084367 m * q.natAbs := by
    rw [hq, Int.natAbs_mul]
    unfold a084367
    have hpos : (((m : ℤ) * ((2 * m + 1 : ℤ) ^ 2))).natAbs = m * (2 * m + 1) ^ 2 := by
      have : (m : ℤ) * ((2 * m + 1 : ℤ) ^ 2) = ((m * (2 * m + 1) ^ 2 : ℕ) : ℤ) := by push_cast; ring
      rw [this, Int.natAbs_natCast]
    rw [hpos]
  rw [habs]
  have hq1 : 1 ≤ q.natAbs := Int.natAbs_pos.mpr hq0
  exact Nat.le_mul_of_pos_right _ hq1

-- Part 2: Explicit permutation σ₀ achieving det = m * (2 * m + 1)^2

private def sigma0Fun (m : ℕ) (k : Fin (2 * m + 1)) : Fin (2 * m + 1) :=
  if h0 : k.val = 0 then ⟨0, by omega⟩
  else if hodd : k.val % 2 = 1 then ⟨2 * m + 1 - k.val, by omega⟩
  else ⟨k.val - 1, by omega⟩

private def sigma0InvFun (m : ℕ) (y : Fin (2 * m + 1)) : Fin (2 * m + 1) :=
  if h0 : y.val = 0 then ⟨0, by omega⟩
  else if heven : y.val % 2 = 0 then ⟨2 * m + 1 - y.val, by omega⟩
  else ⟨y.val + 1, by omega⟩

private def sigma0 (m : ℕ) : Equiv.Perm (Fin (2 * m + 1)) where
  toFun := sigma0Fun m
  invFun := sigma0InvFun m
  left_inv k := by
    ext
    unfold sigma0Fun sigma0InvFun
    by_cases h0 : k.val = 0
    · simp [h0]
    · by_cases hodd : k.val % 2 = 1
      · simp only [h0, hodd, ↓reduceDIte]
        have h1 : 2 * m + 1 - k.val ≠ 0 := by omega
        have h2 : (2 * m + 1 - k.val) % 2 = 0 := by omega
        simp only [h1, h2, ↓reduceDIte]
        omega
      · simp only [h0, hodd, ↓reduceDIte]
        have h1 : k.val - 1 ≠ 0 := by omega
        have h2 : ¬ ((k.val - 1) % 2 = 0) := by omega
        simp only [h1, h2, ↓reduceDIte]
        omega
  right_inv y := by
    ext
    unfold sigma0Fun sigma0InvFun
    by_cases h0 : y.val = 0
    · simp [h0]
    · by_cases heven : y.val % 2 = 0
      · simp only [h0, heven, ↓reduceDIte]
        have h1 : 2 * m + 1 - y.val ≠ 0 := by omega
        have h2 : (2 * m + 1 - y.val) % 2 = 1 := by omega
        simp only [h1, h2, ↓reduceDIte]
        omega
      · simp only [h0, heven, ↓reduceDIte]
        have h1 : y.val + 1 ≠ 0 := by omega
        have h2 : ¬ ((y.val + 1) % 2 = 1) := by omega
        simp only [h1, h2, ↓reduceDIte]
        omega

private def shiftMat (n : ℕ) [NeZero n] : Matrix (Fin n) (Fin n) ℤ :=
  fun i j => if j = i + 1 then 1 else 0

private lemma shiftMat_mul (n : ℕ) [NeZero n] (M : Matrix (Fin n) (Fin n) ℤ) (i j : Fin n) :
    (shiftMat n * M) i j = M (i + 1) j := by
  simp only [Matrix.mul_apply, shiftMat]
  rw [Finset.sum_eq_single (i + 1)]
  · simp
  · intro k _ hk; simp [hk]
  · intro h; exact absurd (Finset.mem_univ _) h

private lemma one_add_shiftMat_mul (n : ℕ) [NeZero n] (M : Matrix (Fin n) (Fin n) ℤ) (i j : Fin n) :
    ((1 + shiftMat n) * M) i j = M i j + M (i + 1) j := by
  rw [add_mul, one_mul, Matrix.add_apply, shiftMat_mul]

private lemma sigma0_second_diff (m : ℕ) (hm : 1 ≤ m) (d : Fin (2 * m + 1)) :
    ((sigma0 m d).val : ℤ) + 2 * ((sigma0 m (d - 1)).val : ℤ) + ((sigma0 m (d - 2)).val : ℤ) =
      4 * (m : ℤ) + (if d = (2 : Fin (2 * m + 1)) then 1 else 0) -
        (if d = (1 : Fin (2 * m + 1)) then 1 else 0) := by
  have h1val : (1 : Fin (2 * m + 1)).val = 1 := fin_one_val (by omega)
  have h2val : (2 : Fin (2 * m + 1)).val = 2 := fin_two_val (by omega)
  have hdlt : d.val < 2 * m + 1 := d.isLt
  have hd_sub1 : (d - 1).val = if d.val = 0 then 2 * m else d.val - 1 := by
    have hv := congrArg Fin.val (sub_fin_val (1 : Fin (2 * m + 1)) d)
    dsimp only at hv
    rw [h1val] at hv
    rw [← hv]
    split_ifs with h0
    · rw [h0, show 0 + (2 * m + 1) - 1 = 2 * m by omega]; exact Nat.mod_eq_of_lt (by omega)
    · have : d.val + (2 * m + 1) - 1 = (d.val - 1) + (2 * m + 1) := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  have hd_sub2 : (d - 2).val = if d.val = 0 then 2 * m - 1 else if d.val = 1 then 2 * m else d.val - 2 := by
    have hv := congrArg Fin.val (sub_fin_val (2 : Fin (2 * m + 1)) d)
    dsimp only at hv
    rw [h2val] at hv
    rw [← hv]
    split_ifs with h0 h1
    · rw [h0, show 0 + (2 * m + 1) - 2 = 2 * m - 1 by omega]; exact Nat.mod_eq_of_lt (by omega)
    · rw [h1, show 1 + (2 * m + 1) - 2 = 2 * m by omega]; exact Nat.mod_eq_of_lt (by omega)
    · have : d.val + (2 * m + 1) - 2 = (d.val - 2) + (2 * m + 1) := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  have hval : ∀ x : Fin (2 * m + 1),
      (sigma0 m x).val =
        if x.val = 0 then 0 else if x.val % 2 = 1 then 2 * m + 1 - x.val else x.val - 1 := by
    intro x
    change (sigma0Fun m x).val = _
    unfold sigma0Fun
    split_ifs <;> rfl
  have hd1_iff : d = (1 : Fin (2 * m + 1)) ↔ d.val = 1 := by
    constructor
    · intro h; rw [h, h1val]
    · intro h; ext; rw [h, h1val]
  have hd2_iff : d = (2 : Fin (2 * m + 1)) ↔ d.val = 2 := by
    constructor
    · intro h; rw [h, h2val]
    · intro h; ext; rw [h, h2val]
  rw [hval d, hval (d - 1), hval (d - 2), hd_sub1, hd_sub2]
  simp only [hd1_iff, hd2_iff]
  by_cases h0 : d.val = 0
  · simp only [h0, ↓reduceIte]
    have h2m0 : 2 * m ≠ 0 := by omega
    have h2mp : ¬ ((2 * m) % 2 = 1) := by omega
    have h2m10 : 2 * m - 1 ≠ 0 := by omega
    have h2m1p : (2 * m - 1) % 2 = 1 := by omega
    simp only [h2m0, h2mp, h2m10, h2m1p,
      show ¬ ((0 : ℕ) = 2) by omega, show ¬ ((0 : ℕ) = 1) by omega, ↓reduceIte]
    omega
  · by_cases h1 : d.val = 1
    · simp only [h1, ↓reduceIte]
      have h10 : (1 : ℕ) ≠ 0 := by omega
      have h2m0 : 2 * m ≠ 0 := by omega
      have h2mp : ¬ ((2 * m) % 2 = 1) := by omega
      simp only [h10, h2m0, h2mp, show (1 : ℕ) - 1 = 0 by omega,
        show ¬ ((1 : ℕ) = 2) by omega, ↓reduceIte]
      omega
    · by_cases h2 : d.val = 2
      · simp only [h2, ↓reduceIte]
        have h20 : (2 : ℕ) ≠ 0 := by omega
        have h2p : ¬ ((2 : ℕ) % 2 = 1) := by omega
        have h10 : (2 - 1 : ℕ) ≠ 0 := by omega
        have h1p : (2 - 1 : ℕ) % 2 = 1 := by omega
        simp only [h20, h2p, h10, h1p, show (2 : ℕ) - 2 = 0 by omega,
          show ¬ ((2 : ℕ) = 1) by omega, ↓reduceIte]
        omega
      · simp only [h0, h1, h2, ↓reduceIte]
        have hdm1 : d.val - 1 ≠ 0 := by omega
        have hdm2 : d.val - 2 ≠ 0 := by omega
        by_cases hodd : d.val % 2 = 1
        · have hdm1p : ¬ ((d.val - 1) % 2 = 1) := by omega
          have hdm2p : (d.val - 2) % 2 = 1 := by omega
          simp only [hdm1, hdm2, hodd, hdm1p, hdm2p, ↓reduceIte]
          omega
        · have hdm1p : (d.val - 1) % 2 = 1 := by omega
          have hdm2p : ¬ ((d.val - 2) % 2 = 1) := by omega
          simp only [hdm1, hdm2, hodd, hdm1p, hdm2p, ↓reduceIte]
          omega

private def Jmat (n : ℕ) : Matrix (Fin n) (Fin n) ℤ := fun _ _ => 1

private lemma two_step_identity (m : ℕ) (hm : 1 ≤ m) :
    (1 + shiftMat (2 * m + 1)) * (1 + shiftMat (2 * m + 1)) *
      circulantMatrix (2 * m + 1) (sigma0 m) =
    shiftMat (2 * m + 1) * ((4 * (m : ℤ)) • Jmat (2 * m + 1) + shiftMat (2 * m + 1) - 1) := by
  ext i j
  rw [Matrix.mul_assoc, one_add_shiftMat_mul, one_add_shiftMat_mul, one_add_shiftMat_mul]
  rw [shiftMat_mul]
  simp only [circulantMatrix_eq, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
    Jmat, smul_eq_mul, mul_one, shiftMat, Matrix.one_apply]
  have h2eq : (2 : Fin (2 * m + 1)) = 1 + 1 := by
    ext
    rw [fin_two_val (by omega)]
    change 2 = ((1 : Fin (2 * m + 1)).val + (1 : Fin (2 * m + 1)).val) % (2 * m + 1)
    rw [fin_one_val (by omega), Nat.mod_eq_of_lt (by omega)]
  have hsub1 : j - (i + 1) = (j - i) - 1 := by abel
  have hsub2 : j - (i + 1 + 1) = (j - i) - 2 := by rw [h2eq]; abel
  rw [hsub1, hsub2]
  have hlin : ((sigma0 m (j - i)).val : ℤ) + ((sigma0 m (j - i - 1)).val : ℤ) +
      (((sigma0 m (j - i - 1)).val : ℤ) + ((sigma0 m (j - i - 2)).val : ℤ)) =
      ((sigma0 m (j - i)).val : ℤ) + 2 * ((sigma0 m (j - i - 1)).val : ℤ) +
      ((sigma0 m (j - i - 2)).val : ℤ) := by ring
  rw [hlin, sigma0_second_diff m hm (j - i)]
  have heq1 : (j - i = 1) ↔ (i + 1 = j) := by
    constructor
    · intro h; calc i + 1 = i + (j - i) := by rw [h]
        _ = j := by abel
    · intro h; rw [← h]; abel
  have heq2 : (j - i = 2) ↔ (j = i + 1 + 1) := by
    constructor
    · intro h; rw [h2eq] at h
      calc j = (j - i) + i := by abel
        _ = (1 + 1) + i := by rw [h]
        _ = i + 1 + 1 := by abel
    · intro h; rw [h, h2eq]; abel
  simp only [heq1, heq2]

-- Family of permutations τ_k on Fin n (for k : Fin n)
private def tauFun {n : ℕ} [NeZero n] (k : Fin n) (i : Fin n) : Fin n :=
  if k.val = 0 then i
  else if i.val = 0 then k
  else if i.val < k.val then i
  else i + 1

private def tauInvFun {n : ℕ} [NeZero n] (k : Fin n) (j : Fin n) : Fin n :=
  if k.val = 0 then j
  else if j = k then 0
  else if 1 ≤ j.val ∧ j.val < k.val then j
  else j - 1

private lemma fin_add_one_val {n : ℕ} [NeZero n] (i : Fin n) :
    (i + 1).val = if i.val + 1 = n then 0 else i.val + 1 := by
  have hn : 0 < n := NeZero.pos n
  by_cases h1 : n = 1
  · subst h1; simp
  · have h1v : (1 : Fin n).val = 1 := fin_one_val (by omega)
    change (i.val + (1 : Fin n).val) % n = _
    rw [h1v]
    split_ifs with h
    · rw [h, Nat.mod_self]
    · exact Nat.mod_eq_of_lt (by omega)

private lemma fin_sub_one_val {n : ℕ} [NeZero n] (j : Fin n) :
    (j - 1).val = if j.val = 0 then n - 1 else j.val - 1 := by
  have hn : 0 < n := NeZero.pos n
  by_cases h1 : n = 1
  · subst h1; simp
  · have hv := congrArg Fin.val (sub_fin_val (1 : Fin n) j)
    dsimp only at hv
    have h1v : (1 : Fin n).val = 1 := fin_one_val (by omega)
    rw [h1v] at hv
    rw [← hv]
    split_ifs with h0
    · rw [h0, show 0 + n - 1 = n - 1 by omega]; exact Nat.mod_eq_of_lt (by omega)
    · have : j.val + n - 1 = (j.val - 1) + n := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

private def tauPerm {n : ℕ} [NeZero n] (k : Fin n) : Equiv.Perm (Fin n) where
  toFun := tauFun k
  invFun := tauInvFun k
  left_inv i := by
    have hn : 0 < n := NeZero.pos n
    ext
    unfold tauFun tauInvFun
    by_cases hk : k.val = 0
    · simp [hk]
    · simp only [hk, ↓reduceIte]
      by_cases hi0 : i.val = 0
      · simp [hi0]
      · by_cases hik : i.val < k.val
        · have hne : i ≠ k := fun h => by subst h; exact Nat.lt_irrefl _ hik
          simp only [hi0, hik, hne, ↓reduceIte, show 1 ≤ i.val by omega, and_self]
        · simp only [hi0, hik, ↓reduceIte]
          have hadd := fin_add_one_val i
          have hne : i + 1 ≠ k := by
            intro h
            have hv := congrArg Fin.val h
            rw [hadd] at hv
            split_ifs at hv <;> omega
          have hnot : ¬ (1 ≤ (i + 1).val ∧ (i + 1).val < k.val) := by
            rw [hadd]; split_ifs <;> omega
          simp only [hne, hnot, ↓reduceIte]
          exact congrArg Fin.val (add_sub_cancel_right i 1)
  right_inv j := by
    have hn : 0 < n := NeZero.pos n
    ext
    unfold tauFun tauInvFun
    by_cases hk : k.val = 0
    · simp [hk]
    · simp only [hk, ↓reduceIte]
      by_cases hjk : j = k
      · subst hjk; simp
      · by_cases hjmid : 1 ≤ j.val ∧ j.val < k.val
        · have hj0 : j.val ≠ 0 := by omega
          simp only [hjk, hjmid.1, hjmid.2, and_self, hj0, ↓reduceIte]
        · simp only [hjk, hjmid, ↓reduceIte]
          have hsub := fin_sub_one_val j
          have hjne : j.val ≠ k.val := fun h => hjk (Fin.ext h)
          have hsub0 : (j - 1).val ≠ 0 := by rw [hsub]; split_ifs <;> omega
          have hsublt : ¬ ((j - 1).val < k.val) := by rw [hsub]; split_ifs <;> omega
          simp only [hsub0, hsublt, ↓reduceIte]
          exact congrArg Fin.val (sub_add_cancel j 1)

private lemma tauPerm_zero {n : ℕ} [NeZero n] : tauPerm (0 : Fin n) = 1 := by
  ext i; change (tauFun (0 : Fin n) i).val = i.val
  simp [tauFun]

private lemma tauPerm_one {n : ℕ} (hn : 2 ≤ n) [NeZero n] :
    tauPerm (1 : Fin n) = Equiv.addRight (1 : Fin n) := by
  have h1v : (1 : Fin n).val = 1 := fin_one_val hn
  ext i
  change (tauFun (1 : Fin n) i).val = (i + 1).val
  unfold tauFun
  simp only [h1v, show (1 : ℕ) ≠ 0 by omega, ↓reduceIte]
  by_cases hi0 : i.val = 0
  · have hi : i = 0 := Fin.ext hi0
    simp [hi]
  · have hlt : ¬ (i.val < 1) := by omega
    simp [hi0, hlt]

private lemma tauPerm_last {n : ℕ} (hn : 2 ≤ n) [NeZero n] :
    tauPerm (⟨n - 1, by omega⟩ : Fin n) = Equiv.swap (0 : Fin n) ⟨n - 1, by omega⟩ := by
  ext i
  change (tauFun (⟨n - 1, by omega⟩ : Fin n) i).val = (Equiv.swap (0 : Fin n) ⟨n - 1, by omega⟩ i).val
  unfold tauFun
  dsimp only
  simp only [show n - 1 ≠ 0 by omega, ↓reduceIte]
  by_cases hi0 : i.val = 0
  · have hi : i = 0 := Fin.ext hi0
    simp [hi]
  · by_cases hil : i.val < n - 1
    · have hne0 : i ≠ 0 := fun h => hi0 (by simp [h])
      have hnel : i ≠ ⟨n - 1, by omega⟩ := fun h => by
        have hv := congrArg Fin.val h; dsimp only at hv; omega
      simp [hi0, hil, Equiv.swap_apply_of_ne_of_ne hne0 hnel]
    · have hi : i = ⟨n - 1, by omega⟩ := Fin.ext (by dsimp only; omega)
      rw [hi]
      simp only [Equiv.swap_apply_right, Fin.val_zero]
      have h1 : (⟨n - 1, by omega⟩ : Fin n).val ≠ 0 := by dsimp only; omega
      have h2 : ¬ ((⟨n - 1, by omega⟩ : Fin n).val < n - 1) := by dsimp only; omega
      simp only [h1, h2, ↓reduceIte]
      rw [fin_add_one_val]
      dsimp only
      simp [show n - 1 + 1 = n by omega]

private lemma tauPerm_step {n : ℕ} [NeZero n] (k : Fin n) (hk1 : 1 ≤ k.val) (hk2 : k.val + 1 < n) :
    tauPerm k = tauPerm ⟨k.val + 1, hk2⟩ * Equiv.swap (0 : Fin n) k := by
  ext i
  change (tauFun k i).val = (tauFun ⟨k.val + 1, hk2⟩ (Equiv.swap (0 : Fin n) k i)).val
  unfold tauFun
  dsimp only
  simp only [show k.val ≠ 0 by omega, show k.val + 1 ≠ 0 by omega, ↓reduceIte]
  by_cases hi0 : i = 0
  · subst hi0
    simp only [Fin.val_zero, ↓reduceIte, Equiv.swap_apply_left,
      show k.val ≠ 0 by omega, show k.val < k.val + 1 by omega]
  · by_cases hik : i = k
    · subst hik
      have hi0v : i.val ≠ 0 := by omega
      simp only [hi0v, Nat.lt_irrefl, ↓reduceIte, Equiv.swap_apply_right, Fin.val_zero]
      rw [fin_add_one_val]
      simp [show i.val + 1 ≠ n by omega]
    · rw [Equiv.swap_apply_of_ne_of_ne hi0 hik]
      have hi0v : i.val ≠ 0 := fun h => hi0 (Fin.ext h)
      have hikv : i.val ≠ k.val := fun h => hik (Fin.ext h)
      have hiff : (i.val < k.val) ↔ (i.val < k.val + 1) := by omega
      simp only [hi0v, hiff, ↓reduceIte]

private lemma tauPerm_sign {n : ℕ} (hn : 2 ≤ n) [NeZero n] (k : Fin n) (hk : 1 ≤ k.val) :
    Equiv.Perm.sign (tauPerm k) = (-1 : ℤˣ) ^ (n - k.val) := by
  suffices h : ∀ d : ℕ, ∀ (j : Fin n), 1 ≤ j.val → n - 1 - j.val = d →
      Equiv.Perm.sign (tauPerm j) = (-1 : ℤˣ) ^ (n - j.val) from
    h (n - 1 - k.val) k hk rfl
  intro d
  induction d with
  | zero =>
    intro j hj hd
    have hj_eq : j = ⟨n - 1, by omega⟩ := Fin.ext (by dsimp only; omega)
    rw [hj_eq, tauPerm_last hn]
    have hne : (0 : Fin n) ≠ ⟨n - 1, by omega⟩ := by
      intro h; have hv := congrArg Fin.val h; dsimp only at hv; simp at hv; omega
    rw [Equiv.Perm.sign_swap hne]
    dsimp only
    simp [show n - (n - 1) = 1 by omega]
  | succ d ih =>
    intro j hj hd
    have hj2 : j.val + 1 < n := by omega
    rw [tauPerm_step j hj hj2, map_mul]
    have hne : (0 : Fin n) ≠ j := fun h => by
      have hv := congrArg Fin.val h; simp at hv; omega
    rw [Equiv.Perm.sign_swap hne]
    have hnext := ih ⟨j.val + 1, hj2⟩ (by dsimp only; omega) (by dsimp only; omega)
    dsimp only at hnext
    rw [hnext]
    have hexp : n - j.val = (n - (j.val + 1)) + 1 := by omega
    rw [hexp, pow_succ]

private lemma addRight_one_sign_odd (m : ℕ) (hm : 1 ≤ m) :
    Equiv.Perm.sign (Equiv.addRight (1 : Fin (2 * m + 1))) = 1 := by
  have hn : 2 ≤ 2 * m + 1 := by omega
  have h1v : (1 : Fin (2 * m + 1)).val = 1 := fin_one_val hn
  rw [← tauPerm_one hn, tauPerm_sign hn (1 : Fin (2 * m + 1)) (by omega)]
  rw [h1v, show 2 * m + 1 - 1 = 2 * m by omega, pow_mul]
  simp

private lemma fin_ne_add_one {n : ℕ} [NeZero n] (hn : 2 ≤ n) (i : Fin n) : i ≠ i + 1 := by
  intro h
  have h0 : (0 : Fin n) = 1 := by
    have := congrArg (fun x => x - i) h; simpa using this
  have hv := congrArg Fin.val h0
  rw [Fin.val_zero, fin_one_val hn] at hv
  omega

private lemma det_one_add_shiftMat_odd (m : ℕ) (hm : 1 ≤ m) :
    (1 + shiftMat (2 * m + 1)).det = 2 := by
  have hn : 2 ≤ 2 * m + 1 := by omega
  rw [← Matrix.det_transpose, Matrix.det_apply]
  have hterm : ∀ τ : Equiv.Perm (Fin (2 * m + 1)),
      (∏ i : Fin (2 * m + 1), (1 + shiftMat (2 * m + 1))ᵀ (τ i) i) ≠ 0 →
      τ = 1 ∨ τ = Equiv.addRight (1 : Fin (2 * m + 1)) := by
    intro τ hne
    have hall : ∀ i : Fin (2 * m + 1), τ i = i ∨ τ i = i + 1 := by
      intro i
      have hi : (1 + shiftMat (2 * m + 1))ᵀ (τ i) i ≠ 0 := by
        intro h0; apply hne
        exact Finset.prod_eq_zero (Finset.mem_univ i) h0
      simp only [Matrix.transpose_apply, Matrix.add_apply, Matrix.one_apply, shiftMat] at hi
      by_cases h1 : i = τ i
      · exact Or.inl h1.symm
      · by_cases h2 : τ i = i + 1
        · exact Or.inr h2
        · exfalso; apply hi; simp [h1, h2]
    by_cases hfix : ∃ i : Fin (2 * m + 1), τ i = i
    · left
      obtain ⟨i₀, hi₀⟩ := hfix
      have hstep : ∀ i : Fin (2 * m + 1), τ i = i → τ (i - 1) = i - 1 := by
        intro i hi
        rcases hall (i - 1) with h | h
        · exact h
        · exfalso
          rw [sub_add_cancel] at h
          have hinj : i - 1 = i := τ.injective (h.trans hi.symm)
          have h10 : (i - 1) + 1 = i + 1 := congrArg (· + 1) hinj
          rw [sub_add_cancel] at h10
          exact fin_ne_add_one hn i h10
      have hiter : ∀ k : ℕ, τ (i₀ - k • (1 : Fin (2 * m + 1))) =
          i₀ - k • (1 : Fin (2 * m + 1)) := by
        intro k
        induction k with
        | zero => simpa using hi₀
        | succ k ih =>
          have heq : i₀ - (k + 1) • (1 : Fin (2 * m + 1)) =
              (i₀ - k • (1 : Fin (2 * m + 1))) - 1 := by
            rw [add_nsmul, one_nsmul]; abel
          rw [heq]; exact hstep _ ih
      have hnsmul : ∀ k : ℕ, (k • (1 : Fin (2 * m + 1))).val = k % (2 * m + 1) := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
          rw [add_nsmul, one_nsmul, fin_add_one_val, ih]
          have hmod : (k + 1) % (2 * m + 1) = (k % (2 * m + 1) + 1) % (2 * m + 1) := by
            rw [Nat.add_mod, Nat.mod_eq_of_lt (show 1 < 2 * m + 1 by omega)]
          rw [hmod]
          have hklt : k % (2 * m + 1) < 2 * m + 1 := Nat.mod_lt _ (by omega)
          split_ifs with h
          · rw [h, Nat.mod_self]
          · exact (Nat.mod_eq_of_lt (by omega)).symm
      ext i
      have hk := hiter (i₀ - i).val
      have hcast : (i₀ - i).val • (1 : Fin (2 * m + 1)) = i₀ - i := by
        ext
        rw [hnsmul, Nat.mod_eq_of_lt (i₀ - i).isLt]
      rw [hcast, sub_sub_cancel] at hk
      exact congrArg Fin.val hk
    · right
      push Not at hfix
      ext i
      rcases hall i with h | h
      · exact absurd h (hfix i)
      · exact congrArg Fin.val h
  have h1ne : (1 : Equiv.Perm (Fin (2 * m + 1))) ≠ Equiv.addRight (1 : Fin (2 * m + 1)) := by
    intro h
    have h0 := congrArg (fun f => f 0) h
    exact fin_ne_add_one hn 0 h0
  rw [Finset.sum_eq_add (1 : Equiv.Perm (Fin (2 * m + 1))) (Equiv.addRight (1 : Fin (2 * m + 1)))]
  · have hp1 : ∏ i : Fin (2 * m + 1),
        (1 + shiftMat (2 * m + 1))ᵀ ((1 : Equiv.Perm (Fin (2 * m + 1))) i) i = 1 := by
      apply Finset.prod_eq_one
      intro i _
      simp [shiftMat, fin_ne_add_one hn i]
    have hp2 : ∏ i : Fin (2 * m + 1),
        (1 + shiftMat (2 * m + 1))ᵀ (Equiv.addRight (1 : Fin (2 * m + 1)) i) i = 1 := by
      apply Finset.prod_eq_one
      intro i _
      simp [shiftMat, fin_ne_add_one hn i]
    rw [map_one, addRight_one_sign_odd m hm, hp1, hp2]
    norm_num
  · exact h1ne
  · intro τ _ hne
    have hz : ∏ i : Fin (2 * m + 1), (1 + shiftMat (2 * m + 1))ᵀ (τ i) i = 0 := by
      by_contra h
      rcases hterm τ h with rfl | rfl
      · exact hne.1 rfl
      · exact hne.2 rfl
    rw [hz, smul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h
  · intro h; exact absurd (Finset.mem_univ _) h

private lemma det_shiftMat_odd (m : ℕ) (hm : 1 ≤ m) :
    (shiftMat (2 * m + 1)).det = 1 := by
  rw [← Matrix.det_transpose, Matrix.det_apply]
  rw [Finset.sum_eq_single (Equiv.addRight (1 : Fin (2 * m + 1)))]
  · rw [addRight_one_sign_odd m hm]
    simp [shiftMat]
  · intro τ _ hne
    have hex : ∃ i : Fin (2 * m + 1), τ i ≠ i + 1 := by
      by_contra hall; push Not at hall
      apply hne; ext i; exact congrArg Fin.val (hall i)
    obtain ⟨i, hi⟩ := hex
    have hz : ∏ j : Fin (2 * m + 1), (shiftMat (2 * m + 1))ᵀ (τ j) j = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [shiftMat, hi]
    rw [hz, smul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

-- Helper: subtract `c • row 0` from every row in `s` (with `0 ∉ s`) without changing det
private lemma det_sub_row_zero_finset {n : ℕ} [NeZero n] (M : Matrix (Fin n) (Fin n) ℤ)
    (c : ℤ) (s : Finset (Fin n)) (h0 : (0 : Fin n) ∉ s) :
    (Matrix.of (fun i j => if i ∈ s then M i j - c * M 0 j else M i j)).det = M.det := by
  induction s using Finset.induction_on with
  | empty =>
    have heq : Matrix.of (fun i j => if i ∈ (∅ : Finset (Fin n)) then M i j - c * M 0 j else M i j) = M := by
      ext i j; simp
    rw [heq]
  | @insert a s ha ih =>
    have ha0 : a ≠ 0 := fun h => h0 (h ▸ Finset.mem_insert_self a s)
    have h0s : (0 : Fin n) ∉ s := fun h => h0 (Finset.mem_insert_of_mem h)
    let M' : Matrix (Fin n) (Fin n) ℤ :=
      Matrix.of (fun i j => if i ∈ s then M i j - c * M 0 j else M i j)
    have heq : Matrix.of (fun i j => if i ∈ insert a s then M i j - c * M 0 j else M i j) =
        M'.updateRow a (M' a + (-c) • M' 0) := by
      ext i j
      by_cases hia : i = a
      · subst hia
        simp only [Matrix.of_apply, Finset.mem_insert_self, ↓reduceIte, Matrix.updateRow_self,
          Pi.add_apply, Pi.smul_apply, smul_eq_mul, M', ha, h0s]
        ring
      · simp only [Matrix.of_apply, Finset.mem_insert, hia, false_or,
          Matrix.updateRow_ne hia, M']
    rw [heq, Matrix.det_updateRow_add, Matrix.det_updateRow_smul]
    have hzero : (M'.updateRow a (M' 0)).det = 0 :=
      Matrix.det_zero_of_row_eq ha0 (by simp [ha0.symm])
    rw [hzero, mul_zero, add_zero, Matrix.updateRow_eq_self]
    exact ih h0s

-- Compute det(D) where row 0 is 1 and rows i ≠ 0 are (shiftMat n - 1) i
private lemma det_D_odd (m : ℕ) (hm : 1 ≤ m) :
    (Matrix.of (fun i j : Fin (2 * m + 1) =>
      if i = 0 then (1 : ℤ) else (shiftMat (2 * m + 1) - 1) i j)).det = (2 * m + 1 : ℤ) := by
  have hn : 2 ≤ 2 * m + 1 := by omega
  let D : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) ℤ :=
    Matrix.of (fun i j => if i = 0 then 1 else (shiftMat (2 * m + 1) - 1) i j)
  rw [← Matrix.det_transpose, Matrix.det_apply]
  have hchar : ∀ τ : Equiv.Perm (Fin (2 * m + 1)),
      (∏ i : Fin (2 * m + 1), Dᵀ (τ i) i) ≠ 0 → τ = tauPerm (τ 0) := by
    intro τ hne
    have hall : ∀ i : Fin (2 * m + 1), i ≠ 0 → τ i = i ∨ τ i = i + 1 := by
      intro i hi0
      have hi : D i (τ i) ≠ 0 := by
        intro h0; apply hne
        exact Finset.prod_eq_zero (Finset.mem_univ i) h0
      simp only [D, Matrix.of_apply, hi0, ↓reduceIte, Matrix.sub_apply, shiftMat,
        Matrix.one_apply] at hi
      by_cases h1 : τ i = i + 1
      · exact Or.inr h1
      · by_cases h2 : i = τ i
        · exact Or.inl h2.symm
        · exfalso; apply hi; simp [h1, h2]
    let k := τ 0
    by_cases hk0 : k.val = 0
    · have h0 : τ 0 = 0 := Fin.ext hk0
      have hfix : ∀ r : ℕ, (hr : r < 2 * m + 1) → τ ⟨r, hr⟩ = ⟨r, hr⟩ := by
        intro r
        induction r with
        | zero => intro _; exact h0
        | succ r ih =>
          intro hr
          let y : Fin (2 * m + 1) := ⟨r + 1, hr⟩
          let x := τ.symm y
          have hxy : τ x = y := τ.apply_symm_apply y
          have hx0 : x ≠ 0 := by
            intro hx; rw [hx, h0] at hxy
            have hv := congrArg Fin.val hxy; simp [y] at hv
          rcases hall x hx0 with h | h
          · change τ y = y; rw [← hxy, h]; exact h
          · have hx_eq : x = ⟨r, by omega⟩ := by
              ext
              have hv := congrArg Fin.val (h.symm.trans hxy)
              rw [fin_add_one_val] at hv
              dsimp only [y] at hv ⊢
              split_ifs at hv; all_goals omega
            have hprev := ih (by omega)
            rw [← hx_eq] at hprev
            exact absurd (hprev.symm.trans h) (fin_ne_add_one hn x)
      ext i
      rw [hfix i.val i.isLt]
      change i.val = (tauFun k i).val
      simp [tauFun, hk0]
    · have hlow : ∀ d : ℕ, ∀ (i : Fin (2 * m + 1)),
          1 ≤ i.val → i.val < k.val → k.val - 1 - i.val = d → τ i = i := by
        intro d
        induction d with
        | zero =>
          intro i hi1 hik hd
          have hi0 : i ≠ 0 := fun h => by simp [h] at hi1
          rcases hall i hi0 with h | h
          · exact h
          · exfalso
            have hi1k : i + 1 = k := by
              ext; rw [fin_add_one_val]; split_ifs <;> omega
            rw [hi1k] at h
            have : i = 0 := τ.injective h
            exact hi0 this
        | succ d ih =>
          intro i hi1 hik hd
          have hi0 : i ≠ 0 := fun h => by simp [h] at hi1
          rcases hall i hi0 with h | h
          · exact h
          · exfalso
            have hnext : τ (i + 1) = i + 1 := by
              have hval : (i + 1).val = i.val + 1 := by rw [fin_add_one_val]; split_ifs <;> omega
              exact ih (i + 1) (by omega) (by omega) (by omega)
            have : i = i + 1 := τ.injective (h.trans hnext.symm)
            exact fin_ne_add_one hn i this
      have hhigh : ∀ d : ℕ, ∀ (i : Fin (2 * m + 1)),
          k.val ≤ i.val → (2 * m + 1) - 1 - i.val = d → τ i = i + 1 := by
        intro d
        induction d with
        | zero =>
          intro i hik hd
          let x := τ.symm 0
          have hxy : τ x = 0 := τ.apply_symm_apply 0
          have hx0 : x ≠ 0 := by
            intro hx; rw [hx] at hxy
            have hv := congrArg Fin.val hxy; exact hk0 hv
          rcases hall x hx0 with h | h
          · exfalso; exact hx0 (h.symm.trans hxy)
          · have hxi : x = i := by
              ext
              have hv := congrArg Fin.val (h.symm.trans hxy)
              rw [fin_add_one_val] at hv
              simp only [Fin.val_zero] at hv
              split_ifs at hv; all_goals omega
            rw [← hxi, h]
        | succ d ih =>
          intro i hik hd
          have hnext_val : (i + 1).val = i.val + 1 := by rw [fin_add_one_val]; split_ifs <;> omega
          have hnext : τ (i + 1) = (i + 1) + 1 := ih (i + 1) (by omega) (by omega)
          let x := τ.symm (i + 1)
          have hxy : τ x = i + 1 := τ.apply_symm_apply (i + 1)
          have hx0 : x ≠ 0 := by
            intro hx; rw [hx] at hxy
            have hv := congrArg Fin.val hxy; omega
          rcases hall x hx0 with h | h
          · exfalso
            have hxeq : x = i + 1 := h.symm.trans hxy
            rw [hxeq, hnext] at hxy
            exact fin_ne_add_one hn (i + 1) hxy.symm
          · have hxi : x = i := add_right_cancel (h.symm.trans hxy)
            rw [← hxi, h]
      ext i
      change (τ i).val = (tauFun k i).val
      unfold tauFun
      simp only [hk0, ↓reduceIte]
      by_cases hi0 : i.val = 0
      · have hi : i = 0 := Fin.ext hi0
        simp [hi, k]
      · by_cases hik : i.val < k.val
        · simp only [hi0, hik, ↓reduceIte]
          exact congrArg Fin.val (hlow (k.val - 1 - i.val) i (by omega) hik rfl)
        · simp only [hi0, hik, ↓reduceIte]
          exact congrArg Fin.val (hhigh ((2 * m + 1) - 1 - i.val) i (by omega) rfl)
  have hterm_val : ∀ k : Fin (2 * m + 1),
      (Equiv.Perm.sign (tauPerm k) : ℤ) * ∏ i : Fin (2 * m + 1), Dᵀ (tauPerm k i) i = 1 := by
    intro k
    by_cases hk0 : k.val = 0
    · have hk : k = 0 := Fin.ext hk0
      subst hk
      rw [tauPerm_zero, map_one]
      simp only [Units.val_one, one_mul]
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (0 : Fin (2 * m + 1)))]
      have h0 : Dᵀ ((1 : Equiv.Perm (Fin (2 * m + 1))) 0) 0 = 1 := by simp [D]
      rw [h0, one_mul]
      have hrest : ∏ i ∈ Finset.univ.erase (0 : Fin (2 * m + 1)),
          Dᵀ ((1 : Equiv.Perm (Fin (2 * m + 1))) i) i = (-1 : ℤ) ^ (2 * m) := by
        have hconst : ∀ i ∈ Finset.univ.erase (0 : Fin (2 * m + 1)),
            Dᵀ ((1 : Equiv.Perm (Fin (2 * m + 1))) i) i = -1 := by
          intro i hi
          have hi0 : i ≠ 0 := (Finset.mem_erase.mp hi).1
          simp [D, hi0, shiftMat, fin_ne_add_one hn i]
        rw [Finset.prod_congr rfl hconst, Finset.prod_const]
        simp
      rw [hrest, pow_mul]
      norm_num
    · rw [tauPerm_sign hn k (by omega)]
      have hprod : ∏ i : Fin (2 * m + 1), Dᵀ (tauPerm k i) i = (-1 : ℤ) ^ (k.val - 1) := by
        have hval : ∀ i : Fin (2 * m + 1), Dᵀ (tauPerm k i) i =
            if 1 ≤ i.val ∧ i.val < k.val then (-1 : ℤ) else 1 := by
          intro i
          change D i (tauFun k i) = _
          unfold D tauFun
          simp only [Matrix.of_apply, hk0, ↓reduceIte]
          by_cases hi0 : i.val = 0
          · have hi : i = 0 := Fin.ext hi0
            simp [hi]
          · have hi : i ≠ 0 := fun h => hi0 (by simp [h])
            by_cases hik : i.val < k.val
            · simp only [hi, hi0, hik, show 1 ≤ i.val by omega, and_self, ↓reduceIte,
                Matrix.sub_apply, shiftMat, Matrix.one_apply, fin_ne_add_one hn i]
              norm_num
            · simp only [hi, hi0, hik, and_false, ↓reduceIte, Matrix.sub_apply, shiftMat,
                Matrix.one_apply, fin_ne_add_one hn i]
              norm_num
        simp_rw [hval]
        rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
        congr 1
        have hbij : (Finset.univ.filter (fun i : Fin (2 * m + 1) => 1 ≤ i.val ∧ i.val < k.val)).card =
            (Finset.Ico 1 k.val).card := by
          apply Finset.card_bij (fun i _ => i.val)
          · intro i hi; simp at hi ⊢; exact hi
          · intro a _ b _ h; exact Fin.ext h
          · intro r hr; simp only [Finset.mem_Ico] at hr
            exact ⟨⟨r, by omega⟩, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hr, rfl⟩
        rw [hbij, Nat.card_Ico]
      rw [hprod]
      have hsign : (((-1 : ℤˣ) ^ ((2 * m + 1) - k.val) : ℤˣ) : ℤ) = (-1 : ℤ) ^ ((2 * m + 1) - k.val) := by
        simp
      rw [hsign, ← pow_add]
      have hexp : (2 * m + 1) - k.val + (k.val - 1) = 2 * m := by omega
      rw [hexp, pow_mul]
      norm_num
  have hinj : Function.Injective (tauPerm (n := 2 * m + 1)) := by
    intro k₁ k₂ h
    have h0 := congrArg (fun f => f 0) h
    change tauFun k₁ 0 = tauFun k₂ 0 at h0
    unfold tauFun at h0
    by_cases hk1 : k₁.val = 0 <;> by_cases hk2 : k₂.val = 0
    · exact Fin.ext (hk1.trans hk2.symm)
    · simp only [hk1, hk2, ↓reduceIte, Fin.val_zero] at h0
      exfalso; exact hk2 (congrArg Fin.val h0.symm)
    · simp only [hk1, hk2, ↓reduceIte, Fin.val_zero] at h0
      exfalso; exact hk1 (congrArg Fin.val h0)
    · simp only [hk1, hk2, ↓reduceIte, Fin.val_zero] at h0
      exact h0
  have hsum : ∑ τ : Equiv.Perm (Fin (2 * m + 1)),
        Equiv.Perm.sign τ • ∏ i : Fin (2 * m + 1), Dᵀ (τ i) i =
      ∑ τ ∈ Finset.univ.image (tauPerm (n := 2 * m + 1)),
        Equiv.Perm.sign τ • ∏ i : Fin (2 * m + 1), Dᵀ (τ i) i := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro τ _ hnot
    have hz : ∏ i : Fin (2 * m + 1), Dᵀ (τ i) i = 0 := by
      by_contra h
      apply hnot
      rw [Finset.mem_image]
      exact ⟨τ 0, Finset.mem_univ _, (hchar τ h).symm⟩
    rw [hz, smul_zero]
  rw [hsum, Finset.sum_image (fun a _ b _ hab => hinj hab)]
  have hsum1 : ∑ k : Fin (2 * m + 1),
      Equiv.Perm.sign (tauPerm k) • ∏ i : Fin (2 * m + 1), Dᵀ (tauPerm k i) i =
      ∑ _k : Fin (2 * m + 1), (1 : ℤ) := by
    apply Finset.sum_congr rfl
    intro k _
    rw [Units.smul_def, smul_eq_mul]
    exact hterm_val k
  rw [hsum1]
  simp

private lemma det_rhs_odd (m : ℕ) (hm : 1 ≤ m) :
    ((4 * (m : ℤ)) • Jmat (2 * m + 1) + shiftMat (2 * m + 1) - 1).det =
      4 * (m : ℤ) * ((2 * m + 1 : ℤ) ^ 2) := by
  let A : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) ℤ :=
    (4 * (m : ℤ)) • Jmat (2 * m + 1) + shiftMat (2 * m + 1) - 1
  let B : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) ℤ := A.updateRow 0 (fun _ => 1)
  have hcol : ∀ j : Fin (2 * m + 1), ∑ i : Fin (2 * m + 1), A i j = 4 * (m : ℤ) * (2 * m + 1 : ℤ) := by
    intro j
    have hshift : ∑ i : Fin (2 * m + 1),
        (shiftMat (2 * m + 1) i j - (1 : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) ℤ) i j) = 0 := by
      rw [Finset.sum_sub_distrib]
      have hs1 : ∑ i : Fin (2 * m + 1), shiftMat (2 * m + 1) i j = 1 := by
        rw [Finset.sum_eq_single (j - 1)]
        · simp [shiftMat]
        · intro i _ hi
          have hne : j ≠ i + 1 := fun h => hi (eq_sub_of_add_eq h.symm)
          simp [shiftMat, hne]
        · intro h; exact absurd (Finset.mem_univ _) h
      have hs2 : ∑ i : Fin (2 * m + 1),
          (1 : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) ℤ) i j = 1 := by
        rw [Finset.sum_eq_single j]
        · simp
        · intro i _ hi; simp [hi]
        · intro h; exact absurd (Finset.mem_univ _) h
      rw [hs1, hs2, sub_self]
    have hA : ∑ i : Fin (2 * m + 1), A i j =
        ∑ _i : Fin (2 * m + 1), (4 * (m : ℤ)) +
        ∑ i : Fin (2 * m + 1),
          (shiftMat (2 * m + 1) i j - (1 : Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) ℤ) i j) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      simp only [A, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Jmat, smul_eq_mul, mul_one]
      ring
    rw [hA, hshift, add_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    simp; ring
  have hAB : A.det = (4 * (m : ℤ) * (2 * m + 1 : ℤ)) * B.det := by
    have hu : A.updateRow 0 (fun j => ∑ i : Fin (2 * m + 1), A i j) =
        B.updateRow 0 ((4 * (m : ℤ) * (2 * m + 1 : ℤ)) • (fun _ : Fin (2 * m + 1) => (1 : ℤ))) := by
      ext i j
      by_cases hi : i = 0
      · subst hi
        simp only [Matrix.updateRow_self, Pi.smul_apply, smul_eq_mul, mul_one]
        exact hcol j
      · simp [B, hi]
    calc A.det = (A.updateRow 0 (fun j => ∑ i : Fin (2 * m + 1), A i j)).det :=
          (det_updateRow_univ_sum A 0).symm
      _ = (B.updateRow 0 ((4 * (m : ℤ) * (2 * m + 1 : ℤ)) •
            (fun _ : Fin (2 * m + 1) => (1 : ℤ)))).det := by rw [hu]
      _ = (4 * (m : ℤ) * (2 * m + 1 : ℤ)) * (B.updateRow 0 (fun _ => 1)).det :=
          Matrix.det_updateRow_smul _ _ _ _
      _ = (4 * (m : ℤ) * (2 * m + 1 : ℤ)) * B.det := by
        have hB : B.updateRow 0 (fun _ => 1) = B := by ext i j; by_cases hi : i = 0 <;> simp [B, hi]
        rw [hB]
  have hBD : B.det =
      (Matrix.of (fun i j : Fin (2 * m + 1) =>
        if i = 0 then (1 : ℤ) else (shiftMat (2 * m + 1) - 1) i j)).det := by
    have hs := det_sub_row_zero_finset B (4 * (m : ℤ))
      (Finset.univ.erase 0) (Finset.notMem_erase 0 _)
    rw [← hs]
    congr 1
    ext i j
    by_cases hi : i = 0
    · subst hi; simp [B]
    · simp only [Matrix.of_apply, Finset.mem_erase, hi, ne_eq, not_false_eq_true, Finset.mem_univ,
        and_self, ↓reduceIte, B, Matrix.updateRow_self, Matrix.updateRow_ne hi, A, Matrix.sub_apply,
        Matrix.add_apply, Matrix.smul_apply, Jmat, smul_eq_mul, mul_one]
      ring
  rw [hAB, hBD, det_D_odd m hm]
  ring

private lemma circulant_sigma0_det (m : ℕ) (hm : 1 ≤ m) :
    (circulantMatrix (2 * m + 1) (sigma0 m)).det = (m : ℤ) * ((2 * m + 1 : ℤ) ^ 2) := by
  have hmul := congrArg Matrix.det (two_step_identity m hm)
  simp only [Matrix.det_mul] at hmul
  rw [det_one_add_shiftMat_odd m hm, det_shiftMat_odd m hm, det_rhs_odd m hm] at hmul
  linarith

private theorem main_proof : type_of% @OMA.S_oeis_a392338.main := by
  intro m hm
  unfold a392338
  let S : Set ℕ := { d : ℕ | ∃ σ : Equiv.Perm (Fin (2 * m + 1)),
    (circulantMatrix (2 * m + 1) σ).det ≠ 0 ∧ (circulantMatrix (2 * m + 1) σ).det.natAbs = d }
  have hmem : a084367 m ∈ S := by
    refine ⟨sigma0 m, ?_, ?_⟩
    · rw [circulant_sigma0_det m hm]
      have hm0 : (m : ℤ) ≠ 0 := by omega
      have hn0 : (2 * (m : ℤ) + 1) ≠ 0 := by omega
      exact mul_ne_zero hm0 (pow_ne_zero 2 hn0)
    · rw [circulant_sigma0_det m hm]
      unfold a084367
      have : (m : ℤ) * ((2 * m + 1 : ℤ) ^ 2) = ((m * (2 * m + 1) ^ 2 : ℕ) : ℤ) := by
        push_cast; ring
      rw [this, Int.natAbs_natCast]
  have hle : ∀ d ∈ S, a084367 m ≤ d := by
    intro d ⟨σ, hne, hd⟩
    rw [← hd]
    exact circulant_det_lower_bound m σ hne
  exact le_antisymm (Nat.sInf_le hmem) (le_csInf ⟨a084367 m, hmem⟩ hle)

end OMA.P_oeis_a392338

theorem OMA.solution : type_of% @OMA.S_oeis_a392338.main :=
  OMA.P_oeis_a392338.main_proof

