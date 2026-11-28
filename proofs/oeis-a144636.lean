import OMAStatements.S_oeis_a144636
import Mathlib

/-! Parity: B = (1/6) A(6X) satisfies B + 3B^2 + 6B^3 = X, has integer coefficients, and mod 2 equals sum of X^(2^k). -/

open PowerSeries

private lemma a144636_mem_mul (S : Subring ℚ) (P Q : ℚ⟦X⟧) (hP : constantCoeff P = 0)
    (hQ : constantCoeff Q = 0) (n : ℕ) (hp : ∀ m < n, coeff m P ∈ S)
    (hq : ∀ m < n, coeff m Q ∈ S) : coeff n (P * Q) ∈ S := by
  rw [coeff_mul]
  refine Subring.sum_mem S (fun x hx => ?_)
  have hx' := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
  rcases Nat.eq_zero_or_pos x.1 with h1 | h1
  · rw [h1, coeff_zero_eq_constantCoeff_apply, hP, zero_mul]; exact S.zero_mem
  rcases Nat.eq_zero_or_pos x.2 with h2 | h2
  · rw [h2, coeff_zero_eq_constantCoeff_apply, hQ, mul_zero]; exact S.zero_mem
  exact S.mul_mem (hp _ (by omega)) (hq _ (by omega))

private lemma a144636_integral (B : ℚ⟦X⟧) (h0 : constantCoeff B = 0)
    (hB : B + 3 * B ^ 2 + 6 * B ^ 3 = X) : ∀ n, ∃ z : ℤ, coeff n B = z := by
  let S := (Int.castRingHom ℚ).range
  have hB' : B = X - 3 * (B * B) - 6 * (B * (B * B)) := by
    rw [← hB]; ring
  have h2 : constantCoeff (B * B) = 0 := by rw [map_mul, h0, zero_mul]
  have key : ∀ n, ∀ m < n, coeff m B ∈ S := by
    intro n
    induction n with
    | zero => intro m hm; omega
    | succ n ih =>
      intro m hm
      have hlt : ∀ k < m, coeff k B ∈ S := fun k hk => ih k (by omega)
      have hsq : ∀ k < m, coeff k (B * B) ∈ S := fun k hk =>
        a144636_mem_mul S B B h0 h0 k (fun j hj => hlt j (by omega))
          (fun j hj => hlt j (by omega))
      rw [hB', map_sub, map_sub]
      refine S.sub_mem (S.sub_mem ?_ ?_) ?_
      · rw [coeff_X]
        split_ifs
        · exact ⟨1, by simp⟩
        · exact ⟨0, by simp⟩
      · rw [show (3 : ℚ⟦X⟧) = C (3 : ℚ) from (map_ofNat C 3).symm, coeff_C_mul]
        exact S.mul_mem ⟨3, by simp⟩ (a144636_mem_mul S B B h0 h0 m hlt hlt)
      · rw [show (6 : ℚ⟦X⟧) = C (6 : ℚ) from (map_ofNat C 6).symm, coeff_C_mul]
        exact S.mul_mem ⟨6, by simp⟩ (a144636_mem_mul S B (B * B) h0 h2 m hlt hsq)
  intro n
  obtain ⟨z, hz⟩ := key (n + 1) n (by omega)
  exact ⟨z, by rw [← hz]; simp⟩

private lemma a144636_lt2 (n : ℕ) : n < 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ]; omega

private lemma a144636_T (N : ℕ) (h2 : (2 : (ZMod 2)⟦X⟧) = 0) :
    (∑ k ∈ Finset.range N, (X : (ZMod 2)⟦X⟧) ^ (2 ^ k)) +
      (∑ k ∈ Finset.range N, (X : (ZMod 2)⟦X⟧) ^ (2 ^ k)) ^ 2 =
      X + X ^ (2 ^ N) := by
  induction N with
  | zero => simp; linear_combination (-(X : (ZMod 2)⟦X⟧)) * h2
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have hx : (X : (ZMod 2)⟦X⟧) ^ (2 ^ (N + 1)) = ((X : (ZMod 2)⟦X⟧) ^ (2 ^ N)) ^ 2 := by
      rw [← pow_mul, ← pow_succ]
    rw [hx]
    linear_combination ih + ((X : (ZMod 2)⟦X⟧) ^ (2 ^ N) +
      (∑ k ∈ Finset.range N, (X : (ZMod 2)⟦X⟧) ^ (2 ^ k)) * (X : (ZMod 2)⟦X⟧) ^ (2 ^ N)) * h2

private lemma a144636_coeffT (N n : ℕ) (hn : n < N) :
    (coeff n (∑ k ∈ Finset.range N, (X : (ZMod 2)⟦X⟧) ^ (2 ^ k)) = 1 ↔ ∃ k : ℕ, n = 2 ^ k) := by
  rw [map_sum]
  simp only [coeff_X_pow]
  by_cases h : ∃ k : ℕ, n = 2 ^ k
  · obtain ⟨k, hk⟩ := h
    have hkN : k < N := by have := a144636_lt2 k; omega
    rw [Finset.sum_eq_single k]
    · simp [hk]
    · intro j _ hj
      rw [if_neg]
      intro hj'
      exact hj (Nat.pow_right_injective le_rfl (hj'.symm.trans hk))
    · intro hk'; exact absurd (Finset.mem_range.mpr hkN) hk'
  · rw [Finset.sum_eq_zero]
    · simp only [zero_ne_one, false_iff]; exact h
    · intro j _
      rw [if_neg]
      intro hj; exact h ⟨j, hj⟩

private lemma a144636_core : ∀ A : PowerSeries ℚ, constantCoeff A = 0 →
    A ^ 3 + 3 * A ^ 2 + 6 * A = 6 * X →
    ∀ n : ℕ, 1 ≤ n →
      ((∃ m : ℤ, Odd m ∧
          (6 : ℚ) ^ (n - 1) * ((n.factorial : ℚ) * coeff n A) / (n.factorial : ℚ) = m) ↔
        ∃ k : ℕ, n = 2 ^ k) := by
  intro A hA0 hA n hn
  set B : ℚ⟦X⟧ := C (1 / 6 : ℚ) * rescale (6 : ℚ) A with hBdef
  have hR : (rescale (6 : ℚ) A) ^ 3 + 3 * (rescale (6 : ℚ) A) ^ 2 + 6 * rescale (6 : ℚ) A
      = 36 * X := by
    have := congrArg (rescale (6 : ℚ)) hA
    simp only [map_add, map_mul, map_pow, map_ofNat, rescale_X] at this
    rw [this]
    ring
  have hc : C (1 / 6 : ℚ) * (6 : ℚ⟦X⟧) = 1 := by
    rw [show (6 : ℚ⟦X⟧) = C (6 : ℚ) from (map_ofNat C 6).symm, ← map_mul]
    norm_num
  have hB : B + 3 * B ^ 2 + 6 * B ^ 3 = X := by
    rw [hBdef]
    linear_combination (6 * C (1 / 6 : ℚ) ^ 3) * hR -
      (3 * C (1 / 6 : ℚ) ^ 2 * (rescale (6 : ℚ) A) ^ 2 +
        C (1 / 6 : ℚ) * rescale (6 : ℚ) A * (1 + 6 * C (1 / 6 : ℚ)) -
        X * (1 + 6 * C (1 / 6 : ℚ) + 36 * C (1 / 6 : ℚ) ^ 2)) * hc
  have hB0 : constantCoeff B = 0 := by
    rw [hBdef, map_mul, ← coeff_zero_eq_constantCoeff_apply (φ := rescale _ A), coeff_rescale,
      coeff_zero_eq_constantCoeff_apply, hA0]
    simp
  have hcoef : (6 : ℚ) ^ (n - 1) * ((n.factorial : ℚ) * coeff n A) / (n.factorial : ℚ)
      = coeff n B := by
    rw [hBdef, coeff_C_mul, coeff_rescale]
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have hf : ((k + 1).factorial : ℚ) ≠ 0 := by positivity
    rw [Nat.add_sub_cancel]
    field_simp
    ring
  have hint := a144636_integral B hB0 hB
  let Z : ℤ⟦X⟧ := PowerSeries.mk (fun n => Classical.choose (hint n))
  have hmap : PowerSeries.map (Int.castRingHom ℚ) Z = B := by
    ext j
    simp only [coeff_map, Z, coeff_mk, eq_intCast]
    exact (Classical.choose_spec (hint j)).symm
  have hZ : Z + 3 * Z ^ 2 + 6 * Z ^ 3 = X := by
    apply PowerSeries.map_injective (Int.castRingHom ℚ) Int.cast_injective
    simp only [map_add, map_mul, map_pow, map_ofNat, map_X, hmap]
    exact hB
  have hZ0 : coeff 0 Z = 0 := by
    have h := congrArg (coeff 0) hmap
    rw [coeff_map, coeff_zero_eq_constantCoeff_apply (φ := B), hB0] at h
    simpa using h
  set W : (ZMod 2)⟦X⟧ := PowerSeries.map (Int.castRingHom (ZMod 2)) Z with hWdef
  have h3 : (3 : (ZMod 2)⟦X⟧) = 1 := by
    rw [show (3 : (ZMod 2)⟦X⟧) = C (3 : ZMod 2) from (map_ofNat C 3).symm,
      show (3 : ZMod 2) = 1 by decide, map_one]
  have h6 : (6 : (ZMod 2)⟦X⟧) = 0 := by
    rw [show (6 : (ZMod 2)⟦X⟧) = C (6 : ZMod 2) from (map_ofNat C 6).symm,
      show (6 : ZMod 2) = 0 by decide, map_zero]
  have h2 : (2 : (ZMod 2)⟦X⟧) = 0 := by
    rw [show (2 : (ZMod 2)⟦X⟧) = C (2 : ZMod 2) from (map_ofNat C 2).symm,
      show (2 : ZMod 2) = 0 by decide, map_zero]
  have hW : W + W ^ 2 = X := by
    have := congrArg (PowerSeries.map (Int.castRingHom (ZMod 2))) hZ
    simp only [map_add, map_mul, map_pow, map_ofNat, map_X] at this
    rw [← hWdef, h3, h6] at this
    simpa using this
  have hW0 : constantCoeff W = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, hWdef, coeff_map, hZ0, map_zero]
  set T : (ZMod 2)⟦X⟧ := ∑ k ∈ Finset.range (n + 1), (X : (ZMod 2)⟦X⟧) ^ (2 ^ k) with hTdef
  have hT := a144636_T (n + 1) h2
  rw [← hTdef] at hT
  have hT0 : constantCoeff T = 0 := by
    rw [hTdef, map_sum]
    apply Finset.sum_eq_zero
    intro k _
    rw [map_pow, constantCoeff_X, zero_pow (by positivity)]
  have hprod : (W - T) * (1 + W + T) = -(X ^ (2 ^ (n + 1))) := by
    linear_combination hW - hT
  have hu : IsUnit (1 + W + T) := by
    rw [isUnit_iff_constantCoeff, map_add, map_add, hW0, hT0]
    simp
  have hdvd : (X : (ZMod 2)⟦X⟧) ^ (2 ^ (n + 1)) ∣ W - T := by
    rw [← hu.dvd_mul_right, hprod]
    exact (dvd_neg).mpr dvd_rfl
  have hWT : coeff n W = coeff n T := by
    have := X_pow_dvd_iff.mp hdvd n (by have := a144636_lt2 (n + 1); omega)
    rw [map_sub] at this
    exact sub_eq_zero.mp this
  have hodd : Odd (coeff n Z) ↔ ∃ k : ℕ, n = 2 ^ k := by
    rw [← ZMod.intCast_eq_one_iff_odd, ← a144636_coeffT (n + 1) n (by omega), ← hTdef,
      ← hWT, hWdef, coeff_map]
    simp
  rw [hcoef, ← hodd, ← hmap, coeff_map]
  simp only [eq_intCast, Int.cast_inj]
  constructor
  · rintro ⟨m, hm, hm'⟩; rw [hm']; exact hm
  · intro h; exact ⟨_, h, rfl⟩

theorem OMA.solution : type_of% @OMA.S_oeis_a144636.main := a144636_core
