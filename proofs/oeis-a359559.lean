import OMAStatements.S_oeis_a359559

-- Credit: @mjsechrest2

namespace OMA.P_oeis_a359559

open OMA.S_oeis_a359559
open scoped BigOperators Matrix

private noncomputable def seqX (j : ℕ) : ℂ := (Complex.I - Complex.I ^ j) / (Complex.I - 1)
private noncomputable def seqY (j : ℕ) : ℂ := (Complex.I ^ j - 1) / (Complex.I - 1)

private lemma I_sub_one_ne : (Complex.I - 1 : ℂ) ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this

private lemma seqX_zero : seqX 0 = 1 := by
  unfold seqX
  simp [div_self I_sub_one_ne]

private lemma seqX_one : seqX 1 = 0 := by
  unfold seqX
  simp

private lemma seqY_zero : seqY 0 = 0 := by
  unfold seqY
  simp

private lemma seqY_one : seqY 1 = 1 := by
  unfold seqY
  simp [div_self I_sub_one_ne]

private lemma seqX_rec (k : ℕ) :
    (1 + Complex.I) * seqX k - 2 * seqX (k + 1) + (1 - Complex.I) * seqX (k + 2) = 0 := by
  unfold seqX
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  have h1 : Complex.I ^ (k + 1) = Complex.I ^ k * Complex.I := pow_succ Complex.I k
  have h2 : Complex.I ^ (k + 2) = Complex.I ^ k * Complex.I ^ 2 := by rw [pow_add]
  rw [h1, h2, hI]
  field_simp [I_sub_one_ne]
  ring

private lemma seqY_rec (k : ℕ) :
    (1 + Complex.I) * seqY k - 2 * seqY (k + 1) + (1 - Complex.I) * seqY (k + 2) = 0 := by
  unfold seqY
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  have h1 : Complex.I ^ (k + 1) = Complex.I ^ k * Complex.I := pow_succ Complex.I k
  have h2 : Complex.I ^ (k + 2) = Complex.I ^ k * Complex.I ^ 2 := by rw [pow_add]
  rw [h1, h2, hI]
  field_simp [I_sub_one_ne]
  ring

private lemma sum_I_pow (n : ℕ) :
    ∑ j ∈ Finset.range n, Complex.I ^ j = (Complex.I ^ n - 1) / (Complex.I - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    field_simp [I_sub_one_ne]
    ring

private lemma sum_succ_mul_I_pow (n : ℕ) :
    ∑ j ∈ Finset.range n, ((j : ℂ) + 1) * Complex.I ^ j =
      ((n : ℂ) * Complex.I ^ (n + 1) - ((n : ℂ) + 1) * Complex.I ^ n + 1) / (Complex.I - 1) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have h1 : Complex.I ^ (n + 1) = Complex.I ^ n * Complex.I := pow_succ Complex.I n
    have h2 : Complex.I ^ (n + 2) = Complex.I ^ n * Complex.I ^ 2 := by rw [pow_add]
    push_cast
    rw [h2, h1]
    field_simp [I_sub_one_ne]
    ring

private lemma sum_succ_range (n : ℕ) :
    ∑ j ∈ Finset.range n, ((j : ℂ) + 1) = (n : ℂ) * ((n : ℂ) + 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

private lemma entry_row1_sub (j : ℕ) :
    entry 1 j - entry 0 j =
      -Complex.I + (if j = 0 then -1 - Complex.I else 0) + (if j = 1 then 1 - Complex.I else 0) := by
  rcases j with _ | _ | j
  · simp [entry]; ring
  · simp [entry]; ring
  · simp [entry]; ring

private lemma entry_row_diff2 (k j : ℕ) (hk : 2 ≤ k) :
    entry k j - 2 * entry (k - 1) j + entry (k - 2) j =
      if j = k - 2 then 1 + Complex.I
      else if j = k - 1 then -2
      else if j = k then 1 - Complex.I
      else 0 := by
  have hk1 : k - 1 < k := by omega
  have hk2 : k - 2 < k - 1 := by omega
  by_cases hj0 : j = k - 2
  · subst hj0
    simp only [↓reduceIte, entry]
    split_ifs <;> try omega
    push_cast [Nat.cast_sub (show 1 ≤ k by omega), Nat.cast_sub (show 2 ≤ k by omega)]
    ring
  · by_cases hj1 : j = k - 1
    · subst hj1
      simp only [hj0, ↓reduceIte, entry]
      split_ifs <;> try omega
      push_cast [Nat.cast_sub (show 1 ≤ k by omega), Nat.cast_sub (show 2 ≤ k by omega)]
      ring
    · by_cases hj2 : j = k
      · subst hj2
        simp only [hj0, hj1, ↓reduceIte, entry]
        split_ifs <;> try omega
        push_cast [Nat.cast_sub (show 1 ≤ j by omega), Nat.cast_sub (show 2 ≤ j by omega)]
        ring
      · simp only [hj0, hj1, hj2, ↓reduceIte, entry]
        by_cases hlt : j < k - 2
        · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
            if_neg (by omega), if_neg (by omega)]
          push_cast [Nat.cast_sub (show 1 ≤ k by omega), Nat.cast_sub (show 2 ≤ k by omega)]
          ring
        · have hgt : k < j := by omega
          rw [if_neg (by omega), if_pos (by omega), if_neg (by omega), if_pos (by omega),
            if_neg (by omega), if_pos (by omega)]
          push_cast [Nat.cast_sub (show 1 ≤ k by omega), Nat.cast_sub (show 2 ≤ k by omega)]
          ring

private lemma a_closed (n : ℕ) :
    a n = (((n:ℂ)^2+(4+Complex.I)*(n:ℂ)+4+4*Complex.I)/8)*(1+Complex.I)^n +
      (((n:ℂ)^2+(4-Complex.I)*(n:ℂ)+4-4*Complex.I)/8)*(1-Complex.I)^n := by
  rcases n with _ | _ | _ | m
  · simp [a]; ring
  · simp [a, toeplitz, entry]; ring_nf; rw [Complex.I_sq]; norm_num
  · simp [a, toeplitz, Matrix.det_fin_two, entry]
    ring_nf; rw [Complex.I_sq]; norm_num
  · set n := m + 3 with hn_def
    have hn2 : 2 ≤ n := by omega
    -- Unit lower-triangular row operation matrix E
    let E : Matrix (Fin n) (Fin n) ℂ := fun i j =>
      if i = j then 1
      else if i.val = 1 ∧ j.val = 0 then -1
      else if 2 ≤ i.val ∧ j.val + 1 = i.val then -2
      else if 2 ≤ i.val ∧ j.val + 2 = i.val then 1
      else 0
    have hE_lt : E.BlockTriangular OrderDual.toDual := by
      intro i j hij
      change i < j at hij
      have hlt : i.val < j.val := hij
      dsimp [E]
      rw [if_neg (by intro h; subst h; omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    have hE_det : E.det = 1 := by
      rw [Matrix.det_of_isLowerTriangular E hE_lt]
      apply Finset.prod_eq_one
      intro i _
      simp [E]
    -- M = E * toeplitz n
    let M : Matrix (Fin n) (Fin n) ℂ := E * toeplitz n
    have hM0 : ∀ j : Fin n, M ⟨0, by omega⟩ j = entry 0 j.val := by
      intro j
      simp only [M, Matrix.mul_apply, toeplitz]
      rw [Finset.sum_eq_single (⟨0, by omega⟩ : Fin n)]
      · dsimp [E]; rw [one_mul]
      · intro k _ hk
        dsimp [E]
        rw [if_neg (fun h => hk h.symm), zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h
    have hM1 : ∀ j : Fin n, M ⟨1, by omega⟩ j = entry 1 j.val - entry 0 j.val := by
      intro j
      simp only [M, Matrix.mul_apply, toeplitz]
      let f0 : Fin n := ⟨0, by omega⟩
      let f1 : Fin n := ⟨1, by omega⟩
      have hf0v : f0.val = 0 := rfl
      have hf1v : f1.val = 1 := rfl
      have hf01 : f0 ≠ f1 := by intro h; have := congrArg Fin.val h; omega
      have hzero : ∀ k ∈ Finset.univ, k ∉ ({f0, f1} : Finset (Fin n)) → E f1 k * entry k.val j.val = 0 := by
        intro k _ hk
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or, Fin.ext_iff, hf0v, hf1v] at hk
        dsimp only [E]
        rw [if_neg (by intro h; exact hk.2 (by rw [← hf1v]; exact (congrArg Fin.val h).symm)),
          if_neg (by omega), if_neg (by omega), if_neg (by omega), zero_mul]
      rw [← Finset.sum_subset (Finset.subset_univ {f0, f1}) hzero, Finset.sum_pair hf01]
      have he10 : E f1 f0 = -1 := by
        dsimp only [E]; rw [if_neg hf01.symm, if_pos ⟨hf1v, hf0v⟩]
      have he11 : E f1 f1 = 1 := by simp [E]
      rw [he10, he11, hf0v, hf1v]
      ring
    have hMk : ∀ (i j : Fin n), 2 ≤ i.val →
        M i j = entry i.val j.val - 2 * entry (i.val - 1) j.val + entry (i.val - 2) j.val := by
      intro i j hi
      simp only [M, Matrix.mul_apply, toeplitz]
      let k0 : Fin n := i
      let k1 : Fin n := ⟨i.val - 1, by omega⟩
      let k2 : Fin n := ⟨i.val - 2, by omega⟩
      have hsub : (Finset.univ.filter fun k : Fin n => k = k0 ∨ k = k1 ∨ k = k2) = {k0, k1, k2} := by
        ext k; simp
      have hzero : ∀ k ∈ Finset.univ, k ∉ ({k0, k1, k2} : Finset (Fin n)) →
          E i k * entry k.val j.val = 0 := by
        intro k _ hk
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or, Fin.ext_iff, k0, k1, k2] at hk
        have hE0 : E i k = 0 := by
          dsimp [E]
          rw [if_neg (by intro h; exact hk.1 (congrArg Fin.val h).symm),
            if_neg (by omega), if_neg (by omega), if_neg (by omega)]
        rw [hE0, zero_mul]
      rw [← Finset.sum_subset (Finset.subset_univ {k0, k1, k2}) hzero]
      have h01 : k0 ≠ k1 := by intro h; have := congrArg Fin.val h; dsimp [k0, k1] at this; omega
      have h02 : k0 ≠ k2 := by intro h; have := congrArg Fin.val h; dsimp [k0, k2] at this; omega
      have h12 : k1 ≠ k2 := by intro h; have := congrArg Fin.val h; dsimp [k1, k2] at this; omega
      rw [Finset.sum_insert (by simp [h01, h02]), Finset.sum_insert (by simp [h12]),
        Finset.sum_singleton]
      have he0 : E i k0 = 1 := by simp [E, k0]
      have he1 : E i k1 = -2 := by
        dsimp [E, k1]
        rw [if_neg (by intro h; have := congrArg Fin.val h; dsimp at this; omega),
          if_neg (by omega), if_pos (by omega)]
      have he2 : E i k2 = 1 := by
        dsimp [E, k2]
        rw [if_neg (by intro h; have := congrArg Fin.val h; dsimp at this; omega),
          if_neg (by omega), if_neg (by omega), if_pos (by omega)]
      rw [he0, he1, he2]
      dsimp [k0, k1, k2]
      ring
    -- Unit lower-triangular column operation matrix V
    let V : Matrix (Fin n) (Fin n) ℂ := fun i j =>
      if j.val = 0 then seqX i.val
      else if j.val = 1 then seqY i.val
      else if i = j then 1
      else 0
    have hV_low : V.BlockTriangular OrderDual.toDual := by
      intro i j hij
      change i < j at hij
      have hlt : i.val < j.val := hij
      dsimp [V]
      by_cases hj0 : j.val = 0
      · omega
      · by_cases hj1 : j.val = 1
        · have hi0 : i.val = 0 := by omega
          rw [if_neg hj0, if_pos hj1, hi0, seqY_zero]
        · rw [if_neg hj0, if_neg hj1, if_neg (by intro h; subst h; omega)]
    have hV_det : V.det = 1 := by
      rw [Matrix.det_of_isLowerTriangular V hV_low]
      apply Finset.prod_eq_one
      intro i _
      dsimp [V]
      by_cases hi0 : i.val = 0
      · rw [if_pos hi0, hi0, seqX_zero]
      · by_cases hi1 : i.val = 1
        · rw [if_neg hi0, if_pos hi1, hi1, seqY_one]
        · rw [if_neg hi0, if_neg hi1, if_pos rfl]
    -- W = M * V
    let W : Matrix (Fin n) (Fin n) ℂ := M * V
    have hW_det : W.det = a n := by
      simp only [W, M, Matrix.det_mul, hE_det, hV_det, one_mul, mul_one, a]
    -- Show W is block upper-triangular wrt b : Fin n → Fin 2
    let b : Fin n → Fin 2 := fun i => if i.val < 2 then 0 else 1
    have hW_col0 : ∀ i : Fin n, W i ⟨0, by omega⟩ = ∑ j : Fin n, M i j * seqX j.val := by
      intro i
      change (M * V) i ⟨0, by omega⟩ = _
      rw [Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro j _
      dsimp [V]
    have hW_col1 : ∀ i : Fin n, W i ⟨1, by omega⟩ = ∑ j : Fin n, M i j * seqY j.val := by
      intro i
      change (M * V) i ⟨1, by omega⟩ = _
      rw [Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro j _
      change M i j * (if (1 : ℕ) = 0 then seqX j.val else if (1 : ℕ) = 1 then seqY j.val else if j = ⟨1, by omega⟩ then 1 else 0) = M i j * seqY j.val
      simp
    have hW_colge : ∀ (i j : Fin n), 2 ≤ j.val → W i j = M i j := by
      intro i j hj
      simp only [W, Matrix.mul_apply]
      rw [Finset.sum_eq_single j]
      · dsimp [V]; rw [if_neg (by omega), if_neg (by omega), if_pos rfl, mul_one]
      · intro k _ hkj
        dsimp [V]; rw [if_neg (by omega), if_neg (by omega), if_neg hkj, mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    have hW_bt : W.BlockTriangular b := by
      -- We want W i j = 0 whenever b j < b i, i.e. j.val < 2 and 2 ≤ i.val
      intro i j hij
      have hj2 : j.val < 2 := by
        dsimp [b] at hij; split_ifs at hij <;> simp at hij <;> omega
      have hi2 : 2 ≤ i.val := by
        dsimp [b] at hij; split_ifs at hij <;> simp at hij <;> omega
      have hMk_simp : ∀ k : Fin n,
          M i k = if k.val = i.val - 2 then 1 + Complex.I
            else if k.val = i.val - 1 then -2
            else if k.val = i.val then 1 - Complex.I else 0 := by
        intro k; rw [hMk i k hi2, entry_row_diff2 i.val k.val hi2]
      have hsum_seq (g : ℕ → ℂ)
          (hrec : (1 + Complex.I) * g (i.val - 2) - 2 * g (i.val - 1) + (1 - Complex.I) * g i.val = 0) :
          ∑ k : Fin n, M i k * g k.val = 0 := by
        let k0 : Fin n := i
        let k1 : Fin n := ⟨i.val - 1, by omega⟩
        let k2 : Fin n := ⟨i.val - 2, by omega⟩
        have hzero : ∀ k ∈ Finset.univ, k ∉ ({k0, k1, k2} : Finset (Fin n)) →
            M i k * g k.val = 0 := by
          intro k _ hk
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or, Fin.ext_iff, k0, k1, k2] at hk
          rw [hMk_simp k, if_neg hk.2.2, if_neg hk.2.1, if_neg hk.1, zero_mul]
        rw [← Finset.sum_subset (Finset.subset_univ {k0, k1, k2}) hzero]
        have h01 : k0 ≠ k1 := by intro h; have := congrArg Fin.val h; dsimp [k0, k1] at this; omega
        have h02 : k0 ≠ k2 := by intro h; have := congrArg Fin.val h; dsimp [k0, k2] at this; omega
        have h12 : k1 ≠ k2 := by intro h; have := congrArg Fin.val h; dsimp [k1, k2] at this; omega
        rw [Finset.sum_insert (by simp [h01, h02]), Finset.sum_insert (by simp [h12]),
          Finset.sum_singleton]
        rw [hMk_simp k0, hMk_simp k1, hMk_simp k2]
        dsimp [k0, k1, k2]
        rw [if_neg (by omega), if_neg (by omega), if_pos rfl,
          if_neg (by omega), if_pos rfl, if_pos rfl]
        linear_combination hrec
      have hj_cases : j = ⟨0, by omega⟩ ∨ j = ⟨1, by omega⟩ := by
        rcases j with ⟨jv, hjv⟩; interval_cases jv <;> simp
      rcases hj_cases with hj0 | hj1
      · rw [hj0, hW_col0]
        apply hsum_seq seqX
        have h := seqX_rec (i.val - 2)
        have hs1 : i.val - 2 + 1 = i.val - 1 := by omega
        have hs2 : i.val - 2 + 2 = i.val := by omega
        rwa [hs1, hs2] at h
      · rw [hj1, hW_col1]
        apply hsum_seq seqY
        have h := seqY_rec (i.val - 2)
        have hs1 : i.val - 2 + 1 = i.val - 1 := by omega
        have hs2 : i.val - 2 + 2 = i.val := by omega
        rwa [hs1, hs2] at h
    -- Compute W.det via BlockTriangular.det
    have hdet_prod := hW_bt.det
    have himg : Finset.image b Finset.univ = ({0, 1} : Finset (Fin 2)) := by
      ext x
      simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
      fin_cases x
      · exact ⟨fun _ => Or.inl rfl, fun _ => ⟨⟨0, by omega⟩, by simp [b]⟩⟩
      · exact ⟨fun _ => Or.inr rfl, fun _ => ⟨⟨2, by omega⟩, by simp [b]⟩⟩
    rw [himg, Finset.prod_pair (by decide)] at hdet_prod
    -- Block 1 (i.val >= 2) is lower triangular with diagonal 1 - I
    have hblock1 : (W.toSquareBlock b (1 : Fin 2)).det =
        (1 - Complex.I) ^ (m + 1) := by
      let e1 : Fin (m + 1) ≃ {i : Fin n // b i = (1 : Fin 2)} :=
        { toFun := fun k => ⟨⟨k.val + 2, by omega⟩, by simp [b]⟩
          invFun := fun x => ⟨x.1.val - 2, by
            have hx := x.2; by_contra h; simp [b] at hx; omega⟩
          left_inv := fun k => Fin.ext (by dsimp; omega)
          right_inv := fun x => by
            have hx := x.2; simp [b] at hx
            exact Subtype.ext (Fin.ext (by dsimp; omega)) }
      rw [← Matrix.det_reindex_self e1.symm]
      let B1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ :=
        Matrix.reindex e1.symm e1.symm (W.toSquareBlock b (1 : Fin 2))
      have hB1_low : B1.BlockTriangular OrderDual.toDual := by
        intro x y hxy
        change x < y at hxy
        have hlt : x.val < y.val := hxy
        change W ⟨x.val + 2, by omega⟩ ⟨y.val + 2, by omega⟩ = 0
        rw [hW_colge _ _ (by dsimp; omega), hMk _ _ (by dsimp; omega),
          entry_row_diff2 _ _ (by dsimp; omega)]
        dsimp
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      rw [Matrix.det_of_isLowerTriangular B1 hB1_low]
      have hdiag : ∀ x : Fin (m + 1), B1 x x = 1 - Complex.I := by
        intro x
        change W ⟨x.val + 2, by omega⟩ ⟨x.val + 2, by omega⟩ = 1 - Complex.I
        rw [hW_colge _ _ (by dsimp; omega), hMk _ _ (by dsimp; omega),
          entry_row_diff2 _ _ (by dsimp; omega)]
        dsimp
        rw [if_neg (by omega), if_neg (by omega), if_pos rfl]
      rw [Finset.prod_congr rfl (fun x _ => hdiag x), Finset.prod_const, Finset.card_univ,
        Fintype.card_fin]
    -- Block 0 (i.val < 2) is a 2x2 matrix
    have hblock0 : (W.toSquareBlock b (0 : Fin 2)).det =
        W ⟨0, by omega⟩ ⟨0, by omega⟩ * W ⟨1, by omega⟩ ⟨1, by omega⟩ -
        W ⟨0, by omega⟩ ⟨1, by omega⟩ * W ⟨1, by omega⟩ ⟨0, by omega⟩ := by
      let e : Fin 2 ≃ {i : Fin n // b i = (0 : Fin 2)} :=
        { toFun := fun k => ⟨⟨k.val, by omega⟩, by simp [b]; omega⟩
          invFun := fun x => ⟨x.1.val, by
            have hx := x.2; by_contra h; simp [b, h] at hx; omega⟩
          left_inv := fun k => Fin.ext rfl
          right_inv := fun x => Subtype.ext (Fin.ext rfl) }
      rw [← Matrix.det_reindex_self e.symm]
      rw [Matrix.det_fin_two]
      rfl
    -- Compute the 4 entries of Q = block 0
    have hq00 : W ⟨0, by omega⟩ ⟨0, by omega⟩ =
        (1 - Complex.I) * seqX 0 +
          Complex.I * (Complex.I * ((n : ℂ) * ((n : ℂ) + 1) / 2) -
            ((n : ℂ) * Complex.I ^ (n + 1) - ((n : ℂ) + 1) * Complex.I ^ n + 1) / (Complex.I - 1) ^ 2) /
          (Complex.I - 1) := by
      rw [hW_col0]
      have hsum : ∑ j : Fin n, M ⟨0, by omega⟩ j * seqX j.val =
          ∑ j ∈ Finset.range n, entry 0 j * seqX j := by
        rw [← Fin.sum_univ_eq_sum_range (fun j => entry 0 j * seqX j)]
        apply Finset.sum_congr rfl; intro j _; rw [hM0]
      rw [hsum]
      have hsplit : ∀ j ∈ Finset.range n,
          entry 0 j * seqX j =
            (if j = 0 then (1 - Complex.I) * seqX 0 else 0) +
            Complex.I * ((j : ℂ) + 1) * seqX j := by
        intro j _
        rcases j with _ | j
        · simp [entry]; ring
        · simp [entry]
      rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
      have h0 : ∑ j ∈ Finset.range n, (if j = 0 then (1 - Complex.I) * seqX 0 else 0) =
          (1 - Complex.I) * seqX 0 := by
        rw [Finset.sum_ite_eq', if_pos (Finset.mem_range.mpr (by omega))]
      rw [h0]
      congr 1
      have htail : ∑ j ∈ Finset.range n, Complex.I * ((j : ℂ) + 1) * seqX j =
          Complex.I * (Complex.I * (∑ j ∈ Finset.range n, ((j : ℂ) + 1)) -
            ∑ j ∈ Finset.range n, ((j : ℂ) + 1) * Complex.I ^ j) / (Complex.I - 1) := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_div]
        apply Finset.sum_congr rfl
        intro j _
        unfold seqX
        ring
      rw [htail, sum_succ_range, sum_succ_mul_I_pow]
    have hq01 : W ⟨0, by omega⟩ ⟨1, by omega⟩ =
        Complex.I * (((n : ℂ) * Complex.I ^ (n + 1) - ((n : ℂ) + 1) * Complex.I ^ n + 1) / (Complex.I - 1) ^ 2 -
          (n : ℂ) * ((n : ℂ) + 1) / 2) / (Complex.I - 1) := by
      rw [hW_col1]
      have hsum : ∑ j : Fin n, M ⟨0, by omega⟩ j * seqY j.val =
          ∑ j ∈ Finset.range n, entry 0 j * seqY j := by
        rw [← Fin.sum_univ_eq_sum_range (fun j => entry 0 j * seqY j)]
        apply Finset.sum_congr rfl; intro j _; rw [hM0]
      rw [hsum]
      have hsplit : ∀ j ∈ Finset.range n,
          entry 0 j * seqY j = Complex.I * ((j : ℂ) + 1) * seqY j := by
        intro j _
        rcases j with _ | j
        · simp [seqY_zero]
        · simp [entry]
      rw [Finset.sum_congr rfl hsplit]
      have htail : ∑ j ∈ Finset.range n, Complex.I * ((j : ℂ) + 1) * seqY j =
          Complex.I * ((∑ j ∈ Finset.range n, ((j : ℂ) + 1) * Complex.I ^ j) -
            ∑ j ∈ Finset.range n, ((j : ℂ) + 1)) / (Complex.I - 1) := by
        rw [← Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_div]
        apply Finset.sum_congr rfl
        intro j _
        unfold seqY
        ring
      rw [htail, sum_succ_range, sum_succ_mul_I_pow]
    have hq10 : W ⟨1, by omega⟩ ⟨0, by omega⟩ =
        (-1 - Complex.I) -
          Complex.I * (Complex.I * (n : ℂ) - (Complex.I ^ n - 1) / (Complex.I - 1)) / (Complex.I - 1) := by
      rw [hW_col0]
      have hsum : ∑ j : Fin n, M ⟨1, by omega⟩ j * seqX j.val =
          ∑ j ∈ Finset.range n, (entry 1 j - entry 0 j) * seqX j := by
        rw [← Fin.sum_univ_eq_sum_range (fun j => (entry 1 j - entry 0 j) * seqX j)]
        apply Finset.sum_congr rfl; intro j _; rw [hM1]
      rw [hsum]
      have hsplit : ∀ j ∈ Finset.range n,
          (entry 1 j - entry 0 j) * seqX j =
            (if j = 0 then (-1 - Complex.I) else 0) + (-Complex.I * seqX j) := by
        intro j _
        rw [entry_row1_sub]
        rcases j with _ | _ | j
        · simp [seqX_zero]; ring
        · simp [seqX_one]
        · simp
      rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
      have h0 : ∑ j ∈ Finset.range n, (if j = 0 then (-1 - Complex.I : ℂ) else 0) =
          -1 - Complex.I := by
        rw [Finset.sum_ite_eq', if_pos (Finset.mem_range.mpr (by omega))]
      rw [h0]
      have htail : ∑ j ∈ Finset.range n, (-Complex.I * seqX j) =
          -(Complex.I * (Complex.I * (n : ℂ) - ∑ j ∈ Finset.range n, Complex.I ^ j) / (Complex.I - 1)) := by
        have hn_sum : (n : ℂ) = ∑ _j ∈ Finset.range n, (1 : ℂ) := by simp
        rw [hn_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_div,
          ← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro j _
        unfold seqX
        ring
      rw [htail, sum_I_pow]
      ring
    have hq11 : W ⟨1, by omega⟩ ⟨1, by omega⟩ =
        (1 - Complex.I) -
          Complex.I * ((Complex.I ^ n - 1) / (Complex.I - 1) - (n : ℂ)) / (Complex.I - 1) := by
      rw [hW_col1]
      have hsum : ∑ j : Fin n, M ⟨1, by omega⟩ j * seqY j.val =
          ∑ j ∈ Finset.range n, (entry 1 j - entry 0 j) * seqY j := by
        rw [← Fin.sum_univ_eq_sum_range (fun j => (entry 1 j - entry 0 j) * seqY j)]
        apply Finset.sum_congr rfl; intro j _; rw [hM1]
      rw [hsum]
      have hsplit : ∀ j ∈ Finset.range n,
          (entry 1 j - entry 0 j) * seqY j =
            (if j = 1 then (1 - Complex.I) else 0) + (-Complex.I * seqY j) := by
        intro j _
        rw [entry_row1_sub]
        rcases j with _ | _ | j
        · simp [seqY_zero]
        · simp [seqY_one]; ring
        · simp
      rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
      have h1 : ∑ j ∈ Finset.range n, (if j = 1 then (1 - Complex.I : ℂ) else 0) =
          1 - Complex.I := by
        rw [Finset.sum_ite_eq', if_pos (Finset.mem_range.mpr (by omega))]
      rw [h1]
      have htail : ∑ j ∈ Finset.range n, (-Complex.I * seqY j) =
          -(Complex.I * ((∑ j ∈ Finset.range n, Complex.I ^ j) - (n : ℂ)) / (Complex.I - 1)) := by
        have hn_sum : (n : ℂ) = ∑ _j ∈ Finset.range n, (1 : ℂ) := by simp
        rw [hn_sum, ← Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_div,
          ← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro j _
        unfold seqY
        ring
      rw [htail, sum_I_pow]
      ring
    rw [← hW_det, hdet_prod, hblock0, hblock1, hq00, hq01, hq10, hq11, seqX_zero]
    -- Final algebraic identity in ℂ using I^2 = -1 and (1+I)^n = I^n * (1-I)^n
    have hpow_rel : (1 + Complex.I) ^ n = Complex.I ^ n * (1 - Complex.I) ^ n := by
      rw [← mul_pow]
      congr 1
      have hI : Complex.I ^ 2 = -1 := Complex.I_sq
      linear_combination hI
    have hpow_m : (1 - Complex.I) ^ n = (1 - Complex.I) ^ 2 * (1 - Complex.I) ^ (m + 1) := by
      rw [hn_def, show m + 3 = 2 + (m + 1) by omega, pow_add]
    have hIpow : Complex.I ^ (n + 1) = Complex.I ^ n * Complex.I := pow_succ Complex.I n
    rw [hpow_rel, hpow_m, hIpow]
    have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
    field_simp [I_sub_one_ne]
    ring_nf
    have hI3 : Complex.I ^ 3 = -Complex.I := by linear_combination Complex.I * hI2
    have hI4 : Complex.I ^ 4 = 1 := by rw [show (4 : ℕ) = 2 + 2 by rfl, pow_add, hI2]; norm_num
    have hI5 : Complex.I ^ 5 = Complex.I := by linear_combination Complex.I * hI4
    have hI6 : Complex.I ^ 6 = -1 := by rw [show (6 : ℕ) = 2 + 4 by rfl, pow_add, hI2, hI4]; ring
    have hI7 : Complex.I ^ 7 = -Complex.I := by linear_combination Complex.I * hI6
    have hI8 : Complex.I ^ 8 = 1 := by rw [show (8 : ℕ) = 4 + 4 by rfl, pow_add, hI4]; norm_num
    have hI9 : Complex.I ^ 9 = Complex.I := by linear_combination Complex.I * hI8
    have hI10 : Complex.I ^ 10 = -1 := by rw [show (10 : ℕ) = 2 + 8 by rfl, pow_add, hI2, hI8]; ring
    simp only [hI10, hI9, hI8, hI7, hI6, hI5, hI4, hI3, hI2]
    ring

private lemma a_rec (n : ℕ) (hn : 5 < n) :
    a n = 6 * a (n - 1) - 18 * a (n - 2) + 32 * a (n - 3) -
      36 * a (n - 4) + 24 * a (n - 5) - 8 * a (n - 6) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 6 := ⟨n - 6, by omega⟩
  have hs1 : k + 6 - 1 = k + 5 := by omega
  have hs2 : k + 6 - 2 = k + 4 := by omega
  have hs3 : k + 6 - 3 = k + 3 := by omega
  have hs4 : k + 6 - 4 = k + 2 := by omega
  have hs5 : k + 6 - 5 = k + 1 := by omega
  have hs6 : k + 6 - 6 = k := by omega
  rw [hs1, hs2, hs3, hs4, hs5, hs6]
  simp only [a_closed]
  push_cast
  simp only [pow_add]
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  ring_nf
  have hI3 : Complex.I ^ 3 = -Complex.I := by linear_combination Complex.I * hI
  have hI4 : Complex.I ^ 4 = 1 := by rw [show (4 : ℕ) = 2 + 2 by rfl, pow_add, hI]; norm_num
  have hI5 : Complex.I ^ 5 = Complex.I := by linear_combination Complex.I * hI4
  have hI6 : Complex.I ^ 6 = -1 := by rw [show (6 : ℕ) = 2 + 4 by rfl, pow_add, hI, hI4]; ring
  have hI7 : Complex.I ^ 7 = -Complex.I := by linear_combination Complex.I * hI6
  rw [hI7, hI6, hI5, hI4, hI3, hI]
  ring

private lemma coeff_exp_cos (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.exp ℂ * PowerSeries.cos ℂ) =
      ((1 + Complex.I) ^ n + (1 - Complex.I) ^ n) / (2 * (n.factorial : ℂ)) := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have hterm : ∀ k ∈ Finset.range (n + 1),
      PowerSeries.coeff k (PowerSeries.exp ℂ) * PowerSeries.coeff (n - k) (PowerSeries.cos ℂ) =
      (n.choose k : ℂ) * ((Complex.I ^ (n - k) + (-Complex.I) ^ (n - k)) / 2) / (n.factorial : ℂ) := by
    intro k hk
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [PowerSeries.coeff_exp, PowerSeries.cos, PowerSeries.coeff_mk]
    simp only [map_div₀, map_one, map_natCast, map_pow, map_neg]
    have hcos_id :
        (if Even (n - k) then (-1 : ℂ) ^ ((n - k) / 2) / ((n - k).factorial : ℂ) else 0) =
        ((Complex.I ^ (n - k) + (-Complex.I) ^ (n - k)) / 2) / ((n - k).factorial : ℂ) := by
      rcases Nat.even_or_odd (n - k) with ⟨r, hr⟩ | ⟨r, hr⟩
      · rw [if_pos ⟨r, hr⟩, show n - k = 2 * r by omega, show 2 * r / 2 = r by omega]
        rw [pow_mul, pow_mul]
        have h1 : Complex.I ^ 2 = -1 := Complex.I_sq
        have h2 : (-Complex.I) ^ 2 = -1 := by rw [neg_sq]; exact Complex.I_sq
        rw [h1, h2]
        ring
      · rw [if_neg (by rintro ⟨t, ht⟩; omega), hr, pow_add, pow_add, pow_mul, pow_mul]
        have h1 : Complex.I ^ 2 = -1 := Complex.I_sq
        have h2 : (-Complex.I) ^ 2 = -1 := by rw [neg_sq]; exact Complex.I_sq
        rw [h1, h2]
        ring
    rw [hcos_id]
    have hch := Nat.choose_mul_factorial_mul_factorial hkn
    have hch_c : (n.choose k : ℂ) * (k.factorial : ℂ) * ((n - k).factorial : ℂ) = (n.factorial : ℂ) := by
      exact_mod_cast hch
    have hfk : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    have hfnk : ((n - k).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (n - k)
    have hfn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    field_simp [hfk, hfnk, hfn]
    linear_combination -((Complex.I ^ (n - k) + (-Complex.I) ^ (n - k)) * hch_c)
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_div]
  have hsum :
      ∑ k ∈ Finset.range (n + 1), (n.choose k : ℂ) * ((Complex.I ^ (n - k) + (-Complex.I) ^ (n - k)) / 2) =
      ((1 + Complex.I) ^ n + (1 - Complex.I) ^ n) / 2 := by
    have h1 := add_pow (1 : ℂ) Complex.I n
    have h2 := add_pow (1 : ℂ) (-Complex.I) n
    simp only [one_pow, one_mul] at h1 h2
    rw [show (1 - Complex.I : ℂ) = 1 + (-Complex.I) by ring, h1, h2, ← Finset.sum_add_distrib,
      Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hsum]
  ring

private lemma coeff_exp_sin (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.exp ℂ * PowerSeries.sin ℂ) =
      ((1 + Complex.I) ^ n - (1 - Complex.I) ^ n) / (2 * Complex.I * (n.factorial : ℂ)) := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have hterm : ∀ k ∈ Finset.range (n + 1),
      PowerSeries.coeff k (PowerSeries.exp ℂ) * PowerSeries.coeff (n - k) (PowerSeries.sin ℂ) =
      (n.choose k : ℂ) * ((Complex.I ^ (n - k) - (-Complex.I) ^ (n - k)) / (2 * Complex.I)) / (n.factorial : ℂ) := by
    intro k hk
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [PowerSeries.coeff_exp, PowerSeries.sin, PowerSeries.coeff_mk]
    simp only [map_div₀, map_one, map_natCast, map_pow, map_neg]
    have hsin_id :
        (if Even (n - k) then 0 else (-1 : ℂ) ^ ((n - k) / 2) / ((n - k).factorial : ℂ)) =
        ((Complex.I ^ (n - k) - (-Complex.I) ^ (n - k)) / (2 * Complex.I)) / ((n - k).factorial : ℂ) := by
      rcases Nat.even_or_odd (n - k) with ⟨r, hr⟩ | ⟨r, hr⟩
      · rw [if_pos ⟨r, hr⟩, show n - k = 2 * r by omega, pow_mul, pow_mul]
        have h1 : Complex.I ^ 2 = -1 := Complex.I_sq
        have h2 : (-Complex.I) ^ 2 = -1 := by rw [neg_sq]; exact Complex.I_sq
        rw [h1, h2]
        ring
      · rw [if_neg (by rintro ⟨t, ht⟩; omega), hr, show (2 * r + 1) / 2 = r by omega,
          pow_add, pow_add, pow_mul, pow_mul]
        have h1 : Complex.I ^ 2 = -1 := Complex.I_sq
        have h2 : (-Complex.I) ^ 2 = -1 := by rw [neg_sq]; exact Complex.I_sq
        rw [h1, h2]
        field_simp [Complex.I_ne_zero]
        ring
    rw [hsin_id]
    have hch := Nat.choose_mul_factorial_mul_factorial hkn
    have hch_c : (n.choose k : ℂ) * (k.factorial : ℂ) * ((n - k).factorial : ℂ) = (n.factorial : ℂ) := by
      exact_mod_cast hch
    have hfk : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
    have hfnk : ((n - k).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (n - k)
    have hfn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    field_simp [hfk, hfnk, hfn, Complex.I_ne_zero]
    linear_combination -((Complex.I ^ (n - k) - (-Complex.I) ^ (n - k)) * hch_c)
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_div]
  have hsum :
      ∑ k ∈ Finset.range (n + 1),
        (n.choose k : ℂ) * ((Complex.I ^ (n - k) - (-Complex.I) ^ (n - k)) / (2 * Complex.I)) =
      ((1 + Complex.I) ^ n - (1 - Complex.I) ^ n) / (2 * Complex.I) := by
    have h1 := add_pow (1 : ℂ) Complex.I n
    have h2 := add_pow (1 : ℂ) (-Complex.I) n
    simp only [one_pow, one_mul] at h1 h2
    rw [show (1 - Complex.I : ℂ) = 1 + (-Complex.I) by ring, h1, h2, ← Finset.sum_sub_distrib,
      Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hsum]
  ring

end OMA.P_oeis_a359559

theorem OMA.solution : type_of% @OMA.S_oeis_a359559.main := by
  open OMA.S_oeis_a359559 OMA.P_oeis_a359559 PowerSeries in
  refine ⟨a_closed, a_rec, ?_, ?_⟩
  · -- OGF
    dsimp only
    let D : PowerSeries ℂ := (1 - 2 * X + 2 * X ^ 2) ^ 3
    have hD0 : constantCoeff D = 1 := by
      simp [D]
    have hmul : ogf * D = 1 - 5 * X + 9 * X ^ 2 - 12 * X ^ 3 + 10 * X ^ 4 - 4 * X ^ 5 := by
      have hDexp : D = 1 - C 6 * X ^ 1 + C 18 * X ^ 2 - C 32 * X ^ 3 + C 36 * X ^ 4 -
          C 24 * X ^ 5 + C 8 * X ^ 6 := by
        dsimp [D]; simp only [map_ofNat]; ring
      have hrhs : (1 - 5 * X + 9 * X ^ 2 - 12 * X ^ 3 + 10 * X ^ 4 - 4 * X ^ 5 : PowerSeries ℂ) =
          1 - C 5 * X ^ 1 + C 9 * X ^ 2 - C 12 * X ^ 3 + C 10 * X ^ 4 - C 4 * X ^ 5 := by
        simp only [map_ofNat]; ring
      ext n
      rw [hDexp, hrhs]
      have hc (c : ℂ) (k : ℕ) :
          coeff n (ogf * (C c * X ^ k)) = if k ≤ n then c * a (n - k) else 0 := by
        rw [mul_left_comm, coeff_C_mul, ogf, coeff_mul_X_pow']
        split_ifs <;> simp
      simp only [mul_add, mul_sub, mul_one, map_add, map_sub, hc, coeff_C_mul, coeff_X_pow]
      rw [ogf, coeff_mk]
      by_cases hn : 6 ≤ n
      · rw [if_pos (by omega), if_pos (by omega), if_pos (by omega), if_pos (by omega),
          if_pos (by omega), if_pos (by omega)]
        have h0 : n ≠ 0 := by omega
        have h1 : n ≠ 1 := by omega
        have h2 : n ≠ 2 := by omega
        have h3 : n ≠ 3 := by omega
        have h4 : n ≠ 4 := by omega
        have h5 : n ≠ 5 := by omega
        simp only [coeff_one, h0, h1, h2, h3, h4, h5, ↓reduceIte, mul_zero, add_zero, sub_zero]
        have hr := a_rec n (by omega)
        linear_combination hr
      · have ha0 : a 0 = 1 := by rw [a_closed]; ring
        have ha1 : a 1 = 1 := by rw [a_closed]; ring_nf; rw [Complex.I_sq]; norm_num
        have ha2 : a 2 = -3 := by rw [a_closed]; ring_nf; rw [Complex.I_sq]; norm_num
        have ha3 : a 3 = -16 := by
          rw [a_closed]; ring_nf
          have hI : Complex.I ^ 2 = -1 := Complex.I_sq
          have hI3 : Complex.I ^ 3 = -Complex.I := by linear_combination Complex.I * hI
          have hI4 : Complex.I ^ 4 = 1 := by rw [show (4 : ℕ) = 2 + 2 by rfl, pow_add, hI]; norm_num
          simp only [hI4, hI3, hI]; norm_num
        have ha4 : a 4 = -36 := by
          rw [a_closed]; ring_nf
          have hI : Complex.I ^ 2 = -1 := Complex.I_sq
          have hI3 : Complex.I ^ 3 = -Complex.I := by linear_combination Complex.I * hI
          have hI4 : Complex.I ^ 4 = 1 := by rw [show (4 : ℕ) = 2 + 2 by rfl, pow_add, hI]; norm_num
          have hI5 : Complex.I ^ 5 = Complex.I := by linear_combination Complex.I * hI4
          simp only [hI5, hI4, hI3, hI]; norm_num
        have ha5 : a 5 = -40 := by
          rw [a_closed]; ring_nf
          have hI : Complex.I ^ 2 = -1 := Complex.I_sq
          have hI3 : Complex.I ^ 3 = -Complex.I := by linear_combination Complex.I * hI
          have hI4 : Complex.I ^ 4 = 1 := by rw [show (4 : ℕ) = 2 + 2 by rfl, pow_add, hI]; norm_num
          have hI5 : Complex.I ^ 5 = Complex.I := by linear_combination Complex.I * hI4
          have hI6 : Complex.I ^ 6 = -1 := by rw [show (6 : ℕ) = 2 + 4 by rfl, pow_add, hI, hI4]; ring
          simp only [hI6, hI5, hI4, hI3, hI]; norm_num
        interval_cases n <;> simp [coeff_one, ha0, ha1, ha2, ha3, ha4, ha5] <;> norm_num
    rw [← hmul, mul_assoc, PowerSeries.mul_inv_cancel D (by rw [hD0]; exact one_ne_zero), mul_one]
  · -- EGF
    dsimp only
    have hrhs :
        C (1 / 2 : ℂ) * exp ℂ * (X + 1) * (2 * cos ℂ - (X + 2) * sin ℂ) =
        (exp ℂ * cos ℂ) + (exp ℂ * cos ℂ) * X ^ 1 -
        (exp ℂ * sin ℂ) - C (3 / 2 : ℂ) * ((exp ℂ * sin ℂ) * X ^ 1) -
        C (1 / 2 : ℂ) * ((exp ℂ * sin ℂ) * X ^ 2) := by
      have h2 : C (2 : ℂ) = (2 : PowerSeries ℂ) := map_ofNat C 2
      have h3 : C (3 : ℂ) = (3 : PowerSeries ℂ) := map_ofNat C 3
      have hhalf : C (1 / 2 : ℂ) * 2 = 1 := by rw [← h2, ← map_mul]; norm_num
      have h32 : C (3 / 2 : ℂ) = 3 * C (1 / 2 : ℂ) := by rw [← h3, ← map_mul]; norm_num
      rw [h32]
      linear_combination (exp ℂ * cos ℂ * (X + 1) - exp ℂ * sin ℂ) * hhalf
    ext n
    rw [hrhs, egf, coeff_mk]
    simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow']
    rcases n with _ | _ | m
    · simp [a_closed, coeff_exp_cos, coeff_exp_sin]; ring
    · simp only [Nat.reduceLeDiff, ↓reduceIte, Nat.sub_self, Nat.cast_one,
        coeff_exp_cos, coeff_exp_sin, a_closed, Nat.factorial_zero, pow_zero, mul_one]
      have hI : Complex.I ^ 2 = -1 := Complex.I_sq
      have hI3 : Complex.I ^ 3 = -Complex.I := by linear_combination Complex.I * hI
      field_simp [Complex.I_ne_zero]
      ring_nf
      simp only [hI3, hI]
      ring
    · set n := m + 2 with hn_def
      have h1 : 1 ≤ n := by omega
      have h2 : 2 ≤ n := by omega
      rw [if_pos h1, if_pos h1, if_pos h2, coeff_exp_cos n, coeff_exp_cos (n - 1),
        coeff_exp_sin n, coeff_exp_sin (n - 1), coeff_exp_sin (n - 2), a_closed n]
      have hs1 : n - 1 = m + 1 := by omega
      have hs2 : n - 2 = m := by omega
      rw [hs1, hs2]
      have hfn : (n.factorial : ℂ) = ((m + 2 : ℕ) : ℂ) * ((m + 1 : ℕ) : ℂ) * (m.factorial : ℂ) := by
        have : n.factorial = (m + 2) * (m + 1) * m.factorial := by
          change (m + 2).factorial = _
          rw [Nat.factorial_succ, Nat.factorial_succ]; ring
        exact_mod_cast this
      have hfn1 : ((m + 1).factorial : ℂ) = ((m + 1 : ℕ) : ℂ) * (m.factorial : ℂ) := by
        exact_mod_cast Nat.factorial_succ m
      have hfm : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
      have hm1 : ((m + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
      have hm2 : ((m + 2 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (m + 1)
      have hp1 : (1 + Complex.I) ^ n = (1 + Complex.I) ^ 2 * (1 + Complex.I) ^ m := by
        change (1 + Complex.I) ^ (m + 2) = _; rw [pow_add]; ring
      have hp2 : (1 - Complex.I) ^ n = (1 - Complex.I) ^ 2 * (1 - Complex.I) ^ m := by
        change (1 - Complex.I) ^ (m + 2) = _; rw [pow_add]; ring
      have hp1' : (1 + Complex.I) ^ (m + 1) = (1 + Complex.I) * (1 + Complex.I) ^ m := by
        rw [pow_succ]; ring
      have hp2' : (1 - Complex.I) ^ (m + 1) = (1 - Complex.I) * (1 - Complex.I) ^ m := by
        rw [pow_succ]; ring
      rw [hfn, hfn1, hp1, hp2, hp1', hp2']
      have hI : Complex.I ^ 2 = -1 := Complex.I_sq
      field_simp [hfm, hm1, hm2, Complex.I_ne_zero]
      push_cast [hn_def]
      ring_nf
      have hI3 : Complex.I ^ 3 = -Complex.I := by linear_combination Complex.I * hI
      have hI4 : Complex.I ^ 4 = 1 := by rw [show (4 : ℕ) = 2 + 2 by rfl, pow_add, hI]; norm_num
      simp only [hI4, hI3, hI]
      ring
