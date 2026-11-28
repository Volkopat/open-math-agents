import OMAStatements.S_oeis_a025248

-- Problem: A025248: a(n) = a(1)*a(n-1) + a(2)*a(n-2) + ... + a(n-3)*a(3) for n >= 4, with initial terms 1, 0, 2, 2.
-- Upstream: formal-conjectures statements/oeis-a025248.lean:0 (declaration OMA.S_oeis_a025248.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Write the generating function as D G = A + B S with polynomials D, A, B and S^2 = P.
Differentiating S^2 = P and D G = A + B S and eliminating S and its derivative gives a first
order linear differential equation c1 G' + c0 G = r with polynomial c1, c0, r.
The recurrence is the coefficient of a power of x in this equation, beyond the degree of r. -/

namespace A025248Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxHeartbeats 4000000 in
theorem key (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 2 * X + X ^ 2 - 8 * X ^ 3)
    (hG : G * (2 + (0) * S) = 1 + X + (-1) * S) :
    (-4 + 8 * X - 4 * X ^ 2 + 32 * X ^ 3) * derivative ℚ G + (-4 + 4 * X - 48 * X ^ 2) * G = -4 + 4 * X - 24 * X ^ 2 - 8 * X ^ 3 := by
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d8 : derivative ℚ (8 : ℚ⟦X⟧) = 0 := dnum 8
  have hS2 : S * S = (1 - 2 * X + 1 * (X * X) - 8 * (X * X * X) : ℚ⟦X⟧) := by linear_combination hS
  have hk : (2) * G = (1 + X : ℚ⟦X⟧) + (-1) * S := by
    linear_combination hG
  have hPd : derivative ℚ (1 - 2 * X + 1 * (X * X) - 8 * (X * X * X) : ℚ⟦X⟧) = -2 + 2 * X - 24 * X ^ 2 := by
    simp [Derivation.leibniz, d2, d8]
    ring
  have hSSd : derivative ℚ (S * S) = 2 * S * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have hdS : 2 * S * derivative ℚ S = -2 + 2 * X - 24 * X ^ 2 := by rw [← hSSd, hS2, hPd]
  have hL : derivative ℚ ((2 : ℚ⟦X⟧) * G) = (0) * G + (2) * derivative ℚ G := by
    simp [Derivation.leibniz, d2]
  have hR : derivative ℚ ((1 + 1 * X : ℚ⟦X⟧) + (-1 : ℚ⟦X⟧) * S) =
      1 + (0) * S + (-1) * derivative ℚ S := by
    simp
  have hk2 : (2 : ℚ⟦X⟧) * G = (1 + 1 * X : ℚ⟦X⟧) + (-1 : ℚ⟦X⟧) * S := by linear_combination hk
  have hdk : (0) * G + (2) * derivative ℚ G =
      1 + (0) * S + (-1) * derivative ℚ S := by
    rw [← hL, ← hR, hk2]
  linear_combination (-1) ^ 2 * S * hdS - 2 * (-1) ^ 2 * derivative ℚ S * hS -
      (2 * (0) * (1 - 2 * X + X ^ 2 - 8 * X ^ 3) + (-1) * (-2 + 2 * X - 24 * X ^ 2)) * hk + 2 * (-1) * (1 - 2 * X + X ^ 2 - 8 * X ^ 3) * hdk

set_option maxHeartbeats 4000000 in
theorem keyC (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 2 * X + X ^ 2 - 8 * X ^ 3)
    (hG : G * (2 + (0) * S) = 1 + X + (-1) * S) :
    derivative ℚ G * C (-4) + derivative ℚ G * X * C 8 +
      derivative ℚ G * X * X * C (-4) + derivative ℚ G * X * X * X * C 32 +
      G * C (-4) + G * X * C 4 +
      G * X * X * C (-48) =
      C (-4) + C 4 * X +
      C (-24) * X * X + C (-8) * X * X * X := by
  have h := key S G hS hG
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem rel (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 2 * X + X ^ 2 - 8 * X ^ 3)
    (hG : G * (2 + (0) * S) = 1 + X + (-1) * S) (m : ℕ) :
    (-4) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G + 8 * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G +
      (-4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G + 32 * ((m : ℚ) + 2) * coeff (m + 1 + 1) G +
      (-4) * coeff (m + 1 + 1 + 1 + 1) G + 4 * coeff (m + 1 + 1 + 1) G +
      (-48) * coeff (m + 1 + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

/-- The sequence extended by 0 at index 0. -/
def gs (a : ℕ → ℚ) : ℕ → ℚ := fun n => if n = 0 then 0 else a n

set_option maxHeartbeats 4000000 in
theorem gs_zero (a : ℕ → ℚ) : gs a 0 = 0 := if_pos rfl

set_option maxHeartbeats 4000000 in
theorem gs_pos (a : ℕ → ℚ) (k : ℕ) (hk : k ≠ 0) : gs a k = a k := if_neg hk

set_option maxHeartbeats 4000000 in
theorem convR (g : ℕ → ℚ) (n : ℕ) :
    coeff n (PowerSeries.mk g * PowerSeries.mk g) = ∑ k ∈ Finset.range (n + 1), g k * g (n - k) := by
  rw [PowerSeries.coeff_mul]
  simp only [PowerSeries.coeff_mk]
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => g i * g j) n

set_option maxHeartbeats 4000000 in
theorem conv (g : ℕ → ℚ) (hg0 : g 0 = 0) (n : ℕ) :
    coeff n (PowerSeries.mk g * PowerSeries.mk g) = ∑ k ∈ Finset.Icc 1 (n - 1), g k * g (n - k) := by
  rw [convR]
  symm
  apply Finset.sum_subset
  · intro k hk
    rw [Finset.mem_Icc] at hk
    rw [Finset.mem_range]
    omega
  · intro k hk hk'
    rw [Finset.mem_range] at hk
    rw [Finset.mem_Icc] at hk'
    have hc : k = 0 ∨ k = n := by omega
    rcases hc with rfl | rfl
    · rw [hg0, zero_mul]
    · rw [Nat.sub_self, hg0, mul_zero]

set_option maxHeartbeats 4000000 in
theorem quadC (a : ℕ → ℚ) (h1 : a 1 = 1) (h2 : a 2 = 0) (h3 : a 3 = 2)
    (hrec : ∀ n : ℕ, 4 ≤ n → a n = ∑ k ∈ Finset.Icc 1 (n - 3), a k * a (n - k)) :
    PowerSeries.mk (gs a) * PowerSeries.mk (gs a) =
      PowerSeries.mk (gs a) + PowerSeries.mk (gs a) * X * C 1 - (C 1 * X ^ 1 + C 2 * X ^ 3) := by
  ext n
  rcases n with _ | _ | _ | _ | m
  · rw [convR]
    simp [gs]
  · rw [convR]
    simp [Finset.sum_range_succ, gs, PowerSeries.coeff_X, h1]
  · rw [convR]
    simp [Finset.sum_range_succ, gs, PowerSeries.coeff_X, h1, h2]
  · rw [convR]
    simp [Finset.sum_range_succ, gs, PowerSeries.coeff_X, h1, h2, h3]
  · have hL := conv (gs a) (gs_zero a) (m + 1 + 1 + 1 + 1)
    have e1 : m + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 := rfl
    have e3 : m + 1 + 1 + 1 + 1 - 3 = m + 1 := rfl
    have f2 : m + 1 + 1 + 1 + 1 - (m + 1 + 1) = 2 := by omega
    have f1 : m + 1 + 1 + 1 + 1 - (m + 1 + 1 + 1) = 1 := by omega
    have hsum : ∑ k ∈ Finset.Icc 1 (m + 1), gs a k * gs a (m + 1 + 1 + 1 + 1 - k) =
        ∑ k ∈ Finset.Icc 1 (m + 1), a k * a (m + 1 + 1 + 1 + 1 - k) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_Icc] at hk
      rw [gs_pos a k (by omega), gs_pos a _ (by omega)]
    have hq : coeff (m + 1 + 1 + 1 + 1) (C 1 * X ^ 1 + C 2 * X ^ 3 : ℚ⟦X⟧) = 0 := by
      simp [PowerSeries.coeff_X]
    have hr := hrec (m + 1 + 1 + 1 + 1) (by omega)
    rw [e3] at hr
    rw [e1, Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega), hsum, f2, f1,
      gs_pos a (m + 1 + 1) (by omega), gs_pos a (m + 1 + 1 + 1) (by omega), gs_pos a 2 (by omega),
      gs_pos a 1 (by omega), h1, h2, ← hr] at hL
    rw [map_sub, hq, sub_zero, hL]
    simp [gs]

set_option maxHeartbeats 4000000 in
theorem quad (a : ℕ → ℚ) (h1 : a 1 = 1) (h2 : a 2 = 0) (h3 : a 3 = 2)
    (hrec : ∀ n : ℕ, 4 ≤ n → a n = ∑ k ∈ Finset.Icc 1 (n - 3), a k * a (n - k)) :
    PowerSeries.mk (gs a) * PowerSeries.mk (gs a) = (1 + X) * PowerSeries.mk (gs a) - (X + 2 * X ^ 3) := by
  rw [quadC a h1 h2 h3 hrec]
  simp only [map_ofNat, map_one]
  ring

end A025248Aux

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a025248.main := by
  intro a h1 h2 h3 hrec n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 + 1 := ⟨n - 5, by omega⟩
  have e1 : m + 1 + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 + 1 := rfl
  have e3 : m + 1 + 1 + 1 + 1 + 1 - 3 = m + 1 + 1 := rfl
  rw [e1, e2, e3]
  have hQ := A025248Aux.quad a h1 h2 h3 hrec
  have r := A025248Aux.rel ((1 + PowerSeries.X : PowerSeries ℚ) - 2 * PowerSeries.mk (A025248Aux.gs a))
      (PowerSeries.mk (A025248Aux.gs a)) (by linear_combination 4 * hQ) (by ring) m
  simp only [PowerSeries.coeff_mk, A025248Aux.gs, Nat.add_one_ne_zero, ↓reduceIte] at r
  push_cast
  linear_combination ((-1 : ℚ) / 4) * r
