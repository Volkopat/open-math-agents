import OMAStatements.S_oeis_a000247

/-!
Four-diagonal dynamic programming proof of L. Edson Jeffery's matrix identity
(OEIS A000247): computing the top-right diagonals of unitPrimitiveMatrix^k *ᵥ 1
yields 2^k, 2^k - 1, and 2^(k+3) - (k + 5), giving 2^n - n - 2 at k = n - 3.
-/

theorem OMA.solution : type_of% @OMA.S_oeis_a000247.main := by
  refine ⟨rfl, ?_⟩
  intro n hn
  let M : Matrix (Fin n) (Fin n) ℕ := OMA.S_oeis_a000247.unitPrimitiveMatrix n
  let onesVec : Fin n → ℕ := fun _ => 1
  let f : ℕ → Fin n → ℕ := fun k i => Matrix.mulVec (M ^ k) onesVec i
  have hf0 : ∀ i : Fin n, f 0 i = 1 := by
    intro i
    simp [f, onesVec]
  have hf_succ : ∀ (k : ℕ) (i : Fin n), f (k + 1) i = Matrix.mulVec M (f k) i := by
    intro k i
    change Matrix.mulVec (M ^ (k + 1)) onesVec i = Matrix.mulVec M (Matrix.mulVec (M ^ k) onesVec) i
    rw [pow_succ', Matrix.mulVec_mulVec]
  have hsum2 : ∀ (g : Fin n → ℕ) (a b : Fin n), a ≠ b →
      (∀ j : Fin n, j ≠ a → j ≠ b → g j = 0) →
      ∑ j : Fin n, g j = g a + g b := by
    intro g a b hab hg
    rw [← Finset.add_sum_erase Finset.univ g (Finset.mem_univ a)]
    rw [← Finset.add_sum_erase (Finset.univ.erase a) g
      (Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ b⟩)]
    have hzero : ∑ j ∈ (Finset.univ.erase a).erase b, g j = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      rw [Finset.mem_erase, Finset.mem_erase] at hj
      exact hg j hj.2.1 hj.1
    omega
  have hstep0 : ∀ (u : Fin n → ℕ) (i : Fin n), i.val = 0 →
      Matrix.mulVec M u i = u ⟨1, by omega⟩ := by
    intro u i hi
    rw [Matrix.mulVec, dotProduct]
    have hsum : ∑ j : Fin n, M i j * u j = M i ⟨1, by omega⟩ * u ⟨1, by omega⟩ := by
      refine Finset.sum_eq_single (⟨1, by omega⟩ : Fin n) ?_ (fun h => absurd (Finset.mem_univ _) h)
      intro j _ hj
      have hjne : j.val ≠ 1 := fun h => hj (Fin.ext h)
      have hM0 : M i j = 0 := by
        dsimp [M, OMA.S_oeis_a000247.unitPrimitiveMatrix]
        split_ifs with hcond
        · rcases hcond with h | h | ⟨rfl, h⟩ <;> omega
        · rfl
      simp [hM0]
    have hM1 : M i ⟨1, by omega⟩ = 1 := by
      dsimp [M, OMA.S_oeis_a000247.unitPrimitiveMatrix]
      split_ifs with hcond
      · rfl
      · exfalso; apply hcond; left; omega
    rw [hsum, hM1, one_mul]
  have hstep_mid : ∀ (u : Fin n → ℕ) (i : Fin n) (_ : 0 < i.val) (hin : i.val + 1 < n),
      Matrix.mulVec M u i = u ⟨i.val - 1, by omega⟩ + u ⟨i.val + 1, by omega⟩ := by
    intro u i hi0 hin
    rw [Matrix.mulVec, dotProduct]
    let a : Fin n := ⟨i.val - 1, by omega⟩
    let b : Fin n := ⟨i.val + 1, by omega⟩
    have hab : a ≠ b := by
      intro h
      have := congrArg Fin.val h
      dsimp [a, b] at this
      omega
    have hsum := hsum2 (fun j => M i j * u j) a b hab (by
      intro j hja hjb
      have hj1 : j.val ≠ i.val - 1 := fun h => hja (Fin.ext h)
      have hj2 : j.val ≠ i.val + 1 := fun h => hjb (Fin.ext h)
      have hM0 : M i j = 0 := by
        dsimp [M, OMA.S_oeis_a000247.unitPrimitiveMatrix]
        split_ifs with hcond
        · rcases hcond with h | h | ⟨rfl, h⟩ <;> omega
        · rfl
      simp [hM0])
    have hMa : M i a = 1 := by
      dsimp [M, OMA.S_oeis_a000247.unitPrimitiveMatrix, a]
      split_ifs with hcond
      · rfl
      · exfalso; apply hcond; right; left; omega
    have hMb : M i b = 1 := by
      dsimp [M, OMA.S_oeis_a000247.unitPrimitiveMatrix, b]
      split_ifs with hcond
      · rfl
      · exfalso; apply hcond; left; rfl
    rw [hsum, hMa, hMb, one_mul, one_mul]
  have hstep_last : ∀ (u : Fin n → ℕ) (i : Fin n) (hin : i.val + 1 = n),
      Matrix.mulVec M u i = u ⟨n - 2, by omega⟩ + u ⟨n - 1, by omega⟩ := by
    intro u i hin
    rw [Matrix.mulVec, dotProduct]
    let a : Fin n := ⟨n - 2, by omega⟩
    let b : Fin n := ⟨n - 1, by omega⟩
    have hab : a ≠ b := by
      intro h
      have := congrArg Fin.val h
      dsimp [a, b] at this
      omega
    have hsum := hsum2 (fun j => M i j * u j) a b hab (by
      intro j hja hjb
      have hj1 : j.val ≠ n - 2 := fun h => hja (Fin.ext h)
      have hj2 : j.val ≠ n - 1 := fun h => hjb (Fin.ext h)
      have hM0 : M i j = 0 := by
        dsimp [M, OMA.S_oeis_a000247.unitPrimitiveMatrix]
        split_ifs with hcond
        · rcases hcond with h | h | ⟨h1, _⟩
          · omega
          · omega
          · exact absurd (by rw [← h1]; omega : j.val = n - 1) hj2
        · rfl
      simp [hM0])
    have hMa : M i a = 1 := by
      dsimp [M, OMA.S_oeis_a000247.unitPrimitiveMatrix, a]
      split_ifs with hcond
      · rfl
      · exfalso; apply hcond; right; left; omega
    have hMb : M i b = 1 := by
      dsimp [M, OMA.S_oeis_a000247.unitPrimitiveMatrix, b]
      split_ifs with hcond
      · rfl
      · exfalso; apply hcond; right; right; exact ⟨Fin.ext (by dsimp; omega), hin⟩
    rw [hsum, hMa, hMb, one_mul, one_mul]
  have hd0 : ∀ (k : ℕ) (i : Fin n), k ≤ i.val → f k i = 2 ^ k := by
    intro k
    induction k with
    | zero =>
      intro i _
      exact hf0 i
    | succ k ih =>
      intro i hki
      rw [hf_succ]
      by_cases hlast : i.val + 1 = n
      · rw [hstep_last (f k) i hlast]
        rw [ih ⟨n - 2, by omega⟩ (by dsimp; omega), ih ⟨n - 1, by omega⟩ (by dsimp; omega)]
        rw [pow_succ']
        omega
      · rw [hstep_mid (f k) i (by omega) (by omega)]
        rw [ih ⟨i.val - 1, by omega⟩ (by dsimp; omega), ih ⟨i.val + 1, by omega⟩ (by dsimp; omega)]
        rw [pow_succ']
        omega
  have hd1 : ∀ (k : ℕ) (hk : k ≤ n - 2), f (k + 1) ⟨k, by omega⟩ = 2 ^ (k + 1) - 1 := by
    intro k
    induction k with
    | zero =>
      intro _
      rw [hf_succ, hstep0 (f 0) ⟨0, by omega⟩ rfl, hf0 ⟨1, by omega⟩]
      decide
    | succ k ih =>
      intro hk
      rw [hf_succ, hstep_mid (f (k + 1)) ⟨k + 1, by omega⟩ (by dsimp; omega) (by dsimp; omega)]
      dsimp
      have h1 : f (k + 1) ⟨k, by omega⟩ = 2 ^ (k + 1) - 1 := ih (by omega)
      have h2 : f (k + 1) ⟨k + 2, by omega⟩ = 2 ^ (k + 1) := hd0 (k + 1) ⟨k + 2, by omega⟩ (by dsimp; omega)
      have hpow : 1 ≤ 2 ^ (k + 1) := Nat.one_le_pow _ _ (by omega)
      rw [h1, h2, pow_succ]
      omega
  have hbound : ∀ k : ℕ, k + 5 ≤ 2 ^ (k + 3) := by
    intro k
    induction k with
    | zero => decide
    | succ k ih =>
      rw [pow_succ]
      omega
  have hd3 : ∀ (k : ℕ) (hk : k ≤ n - 3), f (k + 3) ⟨k, by omega⟩ = 2 ^ (k + 3) - (k + 5) := by
    intro k
    induction k with
    | zero =>
      intro _
      rw [hf_succ, hstep0 (f 2) ⟨0, by omega⟩ rfl]
      have h1 := hd1 1 (by omega)
      rw [h1]
      rfl
    | succ k ih =>
      intro hk
      rw [hf_succ, hstep_mid (f (k + 3)) ⟨k + 1, by omega⟩ (by dsimp; omega) (by dsimp; omega)]
      dsimp
      have h1 : f (k + 3) ⟨k, by omega⟩ = 2 ^ (k + 3) - (k + 5) := ih (by omega)
      have h2 : f (k + 3) ⟨k + 2, by omega⟩ = 2 ^ (k + 3) - 1 := by
        simpa [Nat.add_assoc] using hd1 (k + 2) (by omega)
      have hb1 := hbound k
      have hb2 : 1 ≤ 2 ^ (k + 3) := Nat.one_le_pow _ _ (by omega)
      have hpow2 : 2 ^ (k + 1 + 3) = 2 * 2 ^ (k + 3) := by
        rw [show k + 1 + 3 = (k + 3) + 1 by omega, pow_succ']
      rw [h1, h2, hpow2]
      omega
  have hres := hd3 (n - 3) le_rfl
  have heq1 : (n - 3) + 3 = n := by omega
  have heq2 : (n - 3) + 5 = n + 2 := by omega
  change f n ⟨n - 3, by omega⟩ = OMA.S_oeis_a000247.a n
  unfold OMA.S_oeis_a000247.a
  rw [congrArg (fun k => f k ⟨n - 3, by omega⟩) heq1.symm, hres, heq1, heq2]
  omega
