import OMAStatements.S_oeis_a064796

open OMA.S_oeis_a064796 (f)

private theorem closedForm (n : ℕ) :
    f n = ((n + 1) / 2) * (n + 2 - (n + 1) / 2) := by
  let k := n / 2
  by_cases hp : n % 2 = 1
  · have hn : n = 2 * k + 1 := by omega
    have h : (n + 1) * (n + 3) = ((k + 1) * (k + 2)) * 4 := by
      rw [hn]
      ring
    rw [f, if_pos hp, h, show (n + 1) / 2 = k + 1 by omega,
      show n + 2 - (k + 1) = k + 2 by omega]
    omega
  · have hn : n = 2 * k := by omega
    have h : n * (n + 4) = (k * (k + 2)) * 4 := by
      rw [hn]
      ring
    rw [f, if_neg hp, h, show (n + 1) / 2 = k by omega,
      show n + 2 - k = k + 2 by omega]
    omega

private theorem rotateVal {n : ℕ} (i : Fin n) :
    (finRotate n i).val = if i.val + 1 < n then i.val + 1 else 0 := by
  obtain ⟨k, hk⟩ := i
  cases n with
  | zero => omega
  | succ n =>
    by_cases h : k < n
    · rw [finRotate_of_lt h]
      simp [show k + 1 < n + 1 by omega]
    · have he : k = n := by omega
      subst k
      rw [finRotate_last']
      simp

private theorem rotateTwiceNe {n : ℕ} (hn : 3 ≤ n) (i : Fin n) :
    finRotate n (finRotate n i) ≠ i := by
  intro h
  have h₁ := rotateVal i
  have h₂ := rotateVal (finRotate n i)
  have he := congrArg Fin.val h
  have hi := i.isLt
  split at h₁ <;> split at h₂ <;> omega

private def zigzag {n : ℕ} (i : Fin n) : Fin n :=
  ⟨if i.val % 2 = 0 then i.val / 2 else n - 1 - i.val / 2, by
    have hi := i.isLt
    split <;> omega⟩

private theorem zigzagInjective (n : ℕ) : Function.Injective (@zigzag n) := by
  intro i j h
  apply Fin.ext
  have hi := i.isLt
  have hj := j.isLt
  have he := congrArg Fin.val h
  change (if i.val % 2 = 0 then i.val / 2 else n - 1 - i.val / 2) =
    (if j.val % 2 = 0 then j.val / 2 else n - 1 - j.val / 2) at he
  split at he <;> split at he <;> omega

private noncomputable def zigzagPerm (n : ℕ) : Equiv.Perm (Fin n) :=
  Equiv.ofBijective zigzag ⟨zigzagInjective n,
    Finite.surjective_of_injective (zigzagInjective n)⟩

private theorem zigzagVal {n : ℕ} (i : Fin n) :
    (zigzag i).val + 1 =
      if i.val % 2 = 0 then i.val / 2 + 1 else n - i.val / 2 := by
  have hi := i.isLt
  by_cases h : i.val % 2 = 0
  · simp [zigzag, h]
  · simp [zigzag, h]
    omega

private theorem productBound (n u v : ℕ) (hu : u ≤ (n + 1) / 2)
    (hv : u + v ≤ n + 2) : u * v ≤ f n := by
  let m := (n + 1) / 2
  let w := n + 2 - m
  change u ≤ m at hu
  rw [closedForm]
  change u * v ≤ m * w
  calc
    u * v ≤ u * (n + 2 - u) := Nat.mul_le_mul_left _ (by omega)
    _ = u * w + u * (m - u) := by
      rw [show n + 2 - u = w + (m - u) by omega, Nat.mul_add]
    _ ≤ u * w + w * (m - u) :=
      Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega : u ≤ w)) _
    _ = m * w := by rw [Nat.mul_comm w (m - u), ← Nat.add_mul, Nat.add_sub_of_le hu]

-- Alternate the smallest and largest remaining values around the circle.
private theorem zigzagBound (n : ℕ) (hn : 3 ≤ n) (i : Fin n) :
    ((zigzagPerm n i : ℕ) + 1) * ((zigzagPerm n (finRotate n i) : ℕ) + 1) ≤ f n := by
  let j := finRotate n i
  change ((zigzag i).val + 1) * ((zigzag j).val + 1) ≤ f n
  have hi := i.isLt
  have hj := j.isLt
  have hr := rotateVal i
  change j.val = _ at hr
  by_cases h : i.val + 1 < n
  · rw [if_pos h] at hr
    by_cases hp : i.val % 2 = 0
    · have hq : j.val % 2 ≠ 0 := by omega
      rw [zigzagVal i, zigzagVal j, if_pos hp, if_neg hq]
      exact productBound n _ _ (by omega) (by omega)
    · have hq : j.val % 2 = 0 := by omega
      rw [zigzagVal i, zigzagVal j, if_neg hp, if_pos hq, Nat.mul_comm]
      exact productBound n _ _ (by omega) (by omega)
  · rw [if_neg h] at hr
    have hq : j.val % 2 = 0 := by omega
    rw [zigzagVal j, if_pos hq, hr, Nat.mul_comm]
    exact productBound n _ _ (by omega) (by omega)

private theorem arrangementLowerBound (n : ℕ) (hn : 3 ≤ n) (σ : Equiv.Perm (Fin n)) :
    ∃ i : Fin n, f n ≤ ((σ i : ℕ) + 1) * ((σ (finRotate n i) : ℕ) + 1) := by
  let m := n / 2
  let t (a : Fin n) := σ (finRotate n (σ.symm a))
  have htinj : Function.Injective t :=
    σ.injective.comp ((finRotate n).injective.comp σ.symm.injective)
  have ht₂ (a : Fin n) : t (t a) ≠ a := by
    intro h
    change σ (finRotate n (σ.symm (σ (finRotate n (σ.symm a))))) = a at h
    rw [σ.symm_apply_apply] at h
    exact rotateTwiceNe hn (σ.symm a) (σ.injective (h.trans (σ.apply_symm_apply a).symm))
  suffices ∃ a : Fin n, f n ≤ (a.val + 1) * ((t a).val + 1) by
    obtain ⟨a, ha⟩ := this
    exact ⟨σ.symm a, by simpa only [t, σ.apply_symm_apply] using ha⟩
  by_cases hhigh : ∃ a : Fin n, m ≤ a.val ∧ m ≤ (t a).val
  · obtain ⟨a, ha, hb⟩ := hhigh
    have hne : (t a).val ≠ a.val := by
      intro h
      have e : t a = a := Fin.ext h
      exact ht₂ a (by rw [e, e])
    have hf : f n ≤ (m + 1) * (m + 2) := by
      rw [closedForm]
      exact Nat.mul_le_mul (by omega) (by omega)
    refine ⟨a, hf.trans ?_⟩
    by_cases h : m + 1 ≤ (t a).val
    · exact Nat.mul_le_mul (by omega) (by omega)
    · rw [Nat.mul_comm (a.val + 1)]
      exact Nat.mul_le_mul (by omega) (by omega)
  · -- If no two large values are adjacent, their successors inject into the small values.
    have hsep (a : Fin n) (ha : m ≤ a.val) : (t a).val < m := by
      by_contra! hb
      exact hhigh ⟨a, ha, hb⟩
    let high (j : Fin (n - m)) : Fin n := ⟨m + j.val, by have := j.isLt; omega⟩
    let down (j : Fin (n - m)) : Fin m :=
      ⟨(t (high j)).val, hsep _ (Nat.le_add_right _ _)⟩
    have hdown : Function.Injective down := by
      intro i j h
      have e : t (high i) = t (high j) := Fin.ext (congrArg (fun z : Fin m => z.val) h)
      have he := congrArg Fin.val (htinj e)
      apply Fin.ext
      change m + i.val = m + j.val at he
      omega
    have hc : n - m ≤ m := by simpa using Fintype.card_le_of_injective down hdown
    have heven : n = 2 * m := by omega
    have hsize : n - m = m := by omega
    have hsurj : Function.Surjective down := by
      let fromLow : Fin m → Fin (n - m) := fun i => ⟨i.val, by rw [hsize]; exact i.isLt⟩
      have hi : Function.Injective (down ∘ fromLow) := by
        intro i j h
        exact Fin.ext (congrArg (fun z : Fin (n - m) => z.val) (hdown h))
      intro x
      obtain ⟨j, hj⟩ := Finite.surjective_of_injective hi x
      exact ⟨fromLow j, hj⟩
    -- Equality of the two counts makes the largest small value sit between two large values.
    let x : Fin n := ⟨m - 1, by omega⟩
    have hx : x.val + 1 = m := by change m - 1 + 1 = m; omega
    have hpred (y : Fin n) (hy : y.val < m) : ∃ j, t (high j) = y := by
      obtain ⟨j, hj⟩ := hsurj ⟨y.val, hy⟩
      exact ⟨j, Fin.ext (congrArg (fun z : Fin m => z.val) hj)⟩
    obtain ⟨j, hj⟩ := hpred x (by omega)
    have htx : m ≤ (t x).val := by
      by_contra! hlow
      obtain ⟨k, hk⟩ := hpred (t x) hlow
      have he := congrArg Fin.val (htinj hk)
      change m + k.val = x.val at he
      omega
    have hne : (t x).val ≠ (high j).val := by
      intro he
      exact ht₂ (high j) (hj ▸ Fin.ext he)
    have hval : (high j).val = m + j.val := rfl
    have hf : f n = m * (m + 2) := by
      rw [closedForm, show (n + 1) / 2 = m by omega, show n + 2 - m = m + 2 by omega]
    by_cases h : m + 1 ≤ (t x).val
    · refine ⟨x, ?_⟩
      rw [hf, hx]
      exact Nat.mul_le_mul_left _ (by omega)
    · refine ⟨high j, ?_⟩
      rw [hj, hf, hx, Nat.mul_comm m (m + 2)]
      exact Nat.mul_le_mul_right _ (by omega)

theorem OMA.solution : type_of% @OMA.S_oeis_a064796.main := by
  intro n hn
  refine ⟨arrangementLowerBound n hn, ?_⟩
  intro b hb
  obtain ⟨i, hi⟩ := hb (zigzagPerm n)
  exact hi.trans (zigzagBound n hn i)
