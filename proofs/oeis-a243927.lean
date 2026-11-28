import OMAStatements.S_oeis_a243927

-- Problem: A243927: Number of numbers in row n of the array at A243925.
-- Upstream: formal-conjectures statements/oeis-a243927.lean:0 (declaration OMA.S_oeis_a243927.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: a row drops every number of the earlier rows, so no number is in two rows. The
-- numbers in some row contain 1 and are closed under f(x) = x+1 and g(x) = -2/x (x nonzero).
-- Descent: for 1 <= p < q, p/q = f(g(2q/(q-p))) and q-p < q (strong induction on q); for p > q,
-- p/q = f((p-q)/q) (strong induction on p); p = q gives 1. So every positive rational occurs,
-- 0 = f(g(2)), and r < 0 is g(2/(-r)) with 2/(-r) > 0.

open OMA.S_oeis_a243927 in
theorem OMA.solution : type_of% @OMA.S_oeis_a243927.main := by
  have R1 : ∀ k, (R (k + 1)).1 = cand (R k).1 \ (R k).2 := fun k => rfl
  have R2 : ∀ k, (R (k + 1)).2 = (R k).2 ∪ cand (R k).1 := fun k => rfl
  have Lsub : ∀ k, (R k).1 ⊆ (R k).2 := by
    intro k
    cases k with
    | zero => exact Finset.Subset.refl _
    | succ k =>
      rw [R1 k, R2 k]
      intro x hx
      exact Finset.mem_union_right _ (Finset.mem_sdiff.mp hx).1
  have Lmono : ∀ i j, i ≤ j → (R i).2 ⊆ (R j).2 := by
    intro i j hij
    induction j, hij using Nat.le_induction with
    | base => exact Finset.Subset.refl _
    | succ k _ ih =>
      rw [R2 k]
      exact Finset.Subset.trans ih Finset.subset_union_left
  have Lback : ∀ k x, x ∈ (R k).2 → ∃ j, x ∈ (R j).1 := by
    intro k
    induction k with
    | zero =>
      intro x hx
      exact ⟨0, hx⟩
    | succ k ih =>
      intro x hx
      rw [R2 k] at hx
      by_cases hk : x ∈ (R k).2
      · exact ih x hk
      · refine ⟨k + 1, ?_⟩
        rw [R1 k]
        rcases Finset.mem_union.mp hx with h | h
        · exact absurd h hk
        · exact Finset.mem_sdiff.mpr ⟨h, hk⟩
  have NotPrev : ∀ i j x, i < j → x ∈ (R i).1 → x ∉ (R j).1 := by
    intro i j x hij hi hj
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    rw [R1 k] at hj
    exact (Finset.mem_sdiff.mp hj).2 (Lmono i k (by omega) (Lsub i hi))
  have Ap1 : ∃ k, (1 : ℚ) ∈ (R k).2 := ⟨0, Finset.mem_singleton_self 1⟩
  have Apf : ∀ x : ℚ, (∃ k, x ∈ (R k).2) → ∃ k, x + 1 ∈ (R k).2 := by
    rintro x ⟨k, hk⟩
    obtain ⟨j, hj⟩ := Lback k x hk
    refine ⟨j + 1, ?_⟩
    rw [R2 j]
    apply Finset.mem_union_right
    unfold cand
    exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hj)
  have Apg : ∀ x : ℚ, (∃ k, x ∈ (R k).2) → x ≠ 0 → ∃ k, -2 / x ∈ (R k).2 := by
    rintro x ⟨k, hk⟩ hx0
    obtain ⟨j, hj⟩ := Lback k x hk
    refine ⟨j + 1, ?_⟩
    rw [R2 j]
    apply Finset.mem_union_right
    unfold cand
    exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hj, hx0⟩))
  have Pos : ∀ q : ℕ, 1 ≤ q → ∀ p : ℕ, 1 ≤ p → ∃ k, (p : ℚ) / (q : ℚ) ∈ (R k).2 := by
    intro q
    induction q using Nat.strong_induction_on with
    | _ q ihq =>
      intro hq p
      have hq0 : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      induction p using Nat.strong_induction_on with
      | _ p ihp =>
        intro hp
        rcases lt_trichotomy p q with hlt | heq | hgt
        · have hy := ihq (q - p) (by omega) (by omega) (2 * q) (by omega)
          have h1 : ((2 * q : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
          have h2 : ((q - p : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
          have h3 := Apf _ (Apg _ hy (div_ne_zero h1 h2))
          have h2q : (2 : ℚ) * (q : ℚ) ≠ 0 := mul_ne_zero two_ne_zero hq0
          have e : -2 / (((2 * q : ℕ) : ℚ) / ((q - p : ℕ) : ℚ)) + 1 = (p : ℚ) / (q : ℚ) := by
            have c2 : ((2 * q : ℕ) : ℚ) = 2 * (q : ℚ) := by norm_num
            rw [Nat.cast_sub hlt.le, c2, div_div_eq_mul_div, div_add_one h2q,
              div_eq_div_iff h2q hq0]
            ring
          rw [e] at h3
          exact h3
        · rw [heq, div_self hq0]
          exact Ap1
        · have hx := ihp (p - q) (by omega) (by omega)
          have h3 := Apf _ hx
          have e : ((p - q : ℕ) : ℚ) / (q : ℚ) + 1 = (p : ℚ) / (q : ℚ) := by
            rw [div_add_one hq0, Nat.cast_sub hgt.le, sub_add_cancel]
          rw [e] at h3
          exact h3
  have PosQ : ∀ r : ℚ, 0 < r → ∃ k, r ∈ (R k).2 := by
    intro r hr
    have hn : 0 < r.num := Rat.num_pos.mpr hr
    have h1 : ((r.num.toNat : ℕ) : ℤ) = r.num := Int.toNat_of_nonneg hn.le
    have h2 : ((r.num.toNat : ℕ) : ℚ) = (r.num : ℚ) := by exact_mod_cast h1
    have hd : 1 ≤ r.den := by
      have h := r.den_pos
      omega
    have key := Pos r.den hd r.num.toNat (by omega)
    rw [h2, Rat.num_div_den] at key
    exact key
  have AllQ : ∀ r : ℚ, ∃ k, r ∈ (R k).2 := by
    intro r
    rcases lt_trichotomy r 0 with hneg | hzero | hpos
    · have hy : (0 : ℚ) < 2 / (-r) := div_pos (by norm_num) (by linarith)
      have h := Apg _ (PosQ _ hy) hy.ne'
      have e : -2 / (2 / (-r)) = r := by
        rw [div_div_eq_mul_div]
        ring
      rw [e] at h
      exact h
    · rw [hzero]
      have h2 : (0 : ℚ) < 2 := by norm_num
      have h := Apf _ (Apg _ (PosQ 2 h2) (by norm_num))
      have e : -2 / (2 : ℚ) + 1 = 0 := by norm_num
      rw [e] at h
      exact h
    · exact PosQ r hpos
  intro r
  obtain ⟨k, hk⟩ := AllQ r
  obtain ⟨j, hj⟩ := Lback k r hk
  refine ⟨j + 1, ⟨by omega, ?_⟩, ?_⟩
  · show r ∈ (R (j + 1 - 1)).1
    rw [Nat.add_sub_cancel]
    exact hj
  · rintro m ⟨hm1, hm⟩
    have hm' : r ∈ (R (m - 1)).1 := hm
    rcases lt_trichotomy (m - 1) j with h | h | h
    · exact absurd hj (NotPrev (m - 1) j r h hm')
    · omega
    · exact absurd hm' (NotPrev j (m - 1) r h hj)
