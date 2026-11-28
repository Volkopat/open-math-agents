import OMAStatements.S_oeis_a164012

-- Problem: A164012: Zero together with row 12 of the array in A163280.
-- Upstream: formal-conjectures statements/oeis-a164012.lean:0 (declaration OMA.S_oeis_a164012.main)
-- Credit: @marcelopierry (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.P_oeis_a164012

open OMA.S_oeis_a164012

lemma of_lowerDiv (j : ℕ) (hj : 0 < j) : lowerDiv j ∣ j ∧ lowerDiv j * lowerDiv j ≤ j := by
  obtain ⟨d, hd, h⟩ := Finset.exists_mem_eq_sup ((Nat.divisors j).filter fun d => d * d ≤ j)
    ⟨1, by simp; omega⟩ id
  rw [lowerDiv, h]
  simp at hd
  exact ⟨hd.1.1, hd.2⟩

lemma lowerDiv_eq (k r : ℕ) (hk : 0 < k)
    (H : ∀ s, 1 ≤ s → 2 * k * s + s * s ≤ k * r → s * (r - s) < k + s) :
    lowerDiv (k * (k + r)) = k := by
  unfold lowerDiv
  apply le_antisymm
  · apply Finset.sup_le
    intro d hd
    simp only [Finset.mem_filter, Nat.mem_divisors] at hd
    obtain ⟨⟨hdvd, -⟩, hsq⟩ := hd
    by_contra hlt
    obtain ⟨s, rfl⟩ : ∃ s, d = k + s := ⟨d - k, by simp only [id] at hlt; omega⟩
    have hs : 1 ≤ s := by simp only [id] at hlt; omega
    have hineq : 2 * k * s + s * s ≤ k * r := by nlinarith
    have hsr : 2 * s < r := by by_contra! hc; nlinarith [Nat.mul_le_mul_left k hc]
    have key : (k + s) ∣ s * (r - s) := by
      obtain ⟨t, rfl⟩ : ∃ t, r = s + t := ⟨r - s, by omega⟩
      have e : (k + s) * (k + t) = k * (k + (s + t)) + s * t := by ring
      have h1 : (k + s) ∣ k * (k + (s + t)) + s * t := e ▸ dvd_mul_right _ _
      rw [show s + t - s = t by omega]
      exact (Nat.dvd_add_right hdvd).mp h1
    have := H s hs hineq
    have := Nat.le_of_dvd (Nat.mul_pos (by omega) (by omega)) key
    omega
  · apply Finset.le_sup (f := id)
    simp only [Finset.mem_filter, Nat.mem_divisors]
    refine ⟨⟨dvd_mul_right _ _, ?_⟩, ?_⟩
    · positivity
    · nlinarith

lemma count_eq (k R : ℕ) (hk : 0 < k)
    (H : ∀ r < R + 1, ∀ s, 1 ≤ s → 2 * k * s + s * s ≤ k * r → s * (r - s) < k + s) :
    Nat.count (fun j => lowerDiv j = k) (k * (k + R)) = R := by
  rw [Nat.count_eq_card_filter_range]
  have hset : (Finset.range (k * (k + R))).filter (fun j => lowerDiv j = k) =
      (Finset.range R).image (fun r => k * (k + r)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hj, hl⟩
      obtain ⟨hd, hkk⟩ := hl ▸ of_lowerDiv j (Nat.pos_of_ne_zero (by rintro rfl; simp [lowerDiv] at hl; omega))
      obtain ⟨m, rfl⟩ := hd
      have hm1 : k ≤ m := Nat.le_of_mul_le_mul_left hkk hk
      have hm2 : m < k + R := Nat.lt_of_mul_lt_mul_left hj
      exact ⟨m - k, by omega, by rw [show k + (m - k) = m by omega]⟩
    · rintro ⟨r, hr, rfl⟩
      exact ⟨Nat.mul_lt_mul_of_pos_left (by omega) hk, lowerDiv_eq k r hk (H r (by omega))⟩
  rw [hset, Finset.card_image_of_injective]
  · simp
  · intro x y hxy
    have := Nat.eq_of_mul_eq_mul_left hk hxy
    omega

lemma T_eq (k R : ℕ) (hk : 0 < k)
    (H : ∀ r < R + 1, ∀ s, 1 ≤ s → 2 * k * s + s * s ≤ k * r → s * (r - s) < k + s) :
    T (R + 1) k = k * (k + R) := by
  simpa [T, count_eq k R hk H] using Nat.nth_count (p := (lowerDiv · = k)) (lowerDiv_eq k R hk (H R (by omega)))

lemma solve : ∀ n : ℕ, 36 < n → a n = n * (n + 11) := by
  intro n hn
  rw [a, if_neg (by omega)]
  apply T_eq n 11 (by omega)
  intro r hr s hs h
  have h2 : 2 * s < r := by by_contra! hc; nlinarith [Nat.mul_le_mul_left n hc]
  have hs' : s < 7 := by omega
  interval_cases r <;> interval_cases s <;> omega

end OMA.P_oeis_a164012

theorem OMA.solution : type_of% @OMA.S_oeis_a164012.main := OMA.P_oeis_a164012.solve
