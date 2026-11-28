import OMAStatements.S_oeis_a393866
import Mathlib

namespace A393866X
open PowerSeries OMA.S_oeis_a393866


private lemma frob (P : Polynomial ℤ) (p : ℕ) (hp : p.Prime) (j : ℕ) (hj0 : 0 < j)
    (hjp : j < p) : (p : ℤ) ∣ (P ^ p).coeff j := by
  have := Fact.mk hp
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have h1 : (((P ^ p).coeff j : ℤ) : ZMod p) =
      ((P.map (Int.castRingHom (ZMod p))) ^ p).coeff j := by
    rw [← Polynomial.map_pow, Polynomial.coeff_map]; rfl
  rw [h1, ← ZMod.expand_card, Polynomial.coeff_expand hp.pos]
  have : ¬ p ∣ j := fun h => absurd (Nat.le_of_dvd hj0 h) (by omega)
  simp [this]

private lemma nth_ge (k : ℕ) : k + 2 ≤ Nat.nth Nat.Prime k := by
  induction k with
  | zero => simp [Nat.nth_prime_zero_eq_two]
  | succ k ih =>
    have : Nat.nth Nat.Prime k < Nat.nth Nat.Prime (k + 1) :=
      Nat.nth_strictMono Nat.infinite_setOfPred_prime (Nat.lt_succ_self k)
    omega

private lemma pr_ge (n : ℕ) (hn : 1 ≤ n) : n + 1 ≤ pr n := by
  have := nth_ge (n - 1); unfold pr; omega

private lemma pr_prime (n : ℕ) : (pr n).Prime := Nat.prime_nth_prime _

private lemma expand_lem (A g : PowerSeries ℚ) (n p : ℕ) (hn : 1 ≤ n) (hp : 1 ≤ p)
    (hag : ∀ i < n, coeff i A = coeff i g) (hg0 : constantCoeff g = 1) :
    (∀ j < n, coeff j (A ^ p) = coeff j (g ^ p)) ∧
      coeff n (A ^ p) = coeff n (g ^ p) + (p : ℚ) * (coeff n A - coeff n g) := by
  have hdvd : (X : PowerSeries ℚ) ^ n ∣ A - g := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro m hm
    rw [map_sub, hag m hm, sub_self]
  obtain ⟨h, hh⟩ := hdvd
  have hA : A = g + X ^ n * h := by rw [← hh]; ring
  obtain ⟨k, hk⟩ := Polynomial.binomExpansion (Polynomial.X ^ p : Polynomial (PowerSeries ℚ)) g (X ^ n * h)
  simp only [Polynomial.eval_pow, Polynomial.eval_X, Polynomial.derivative_X_pow,
    Polynomial.eval_mul, Polynomial.eval_C] at hk
  have e : A ^ p = g ^ p + X ^ n * (C (p : ℚ) * g ^ (p - 1) * h) + X ^ n * (X ^ n * (k * h ^ 2)) := by
    rw [hA, hk, ← map_natCast (C (R := ℚ)) p]; ring
  have hc : coeff n (A - g) = coeff 0 h := by
    rw [hh, PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self]
  refine ⟨fun j hj => ?_, ?_⟩
  · rw [e, map_add, map_add, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul',
      if_neg (by omega), if_neg (by omega)]
    ring
  · rw [e, map_add, map_add, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul',
      if_pos le_rfl, if_pos le_rfl, Nat.sub_self, PowerSeries.coeff_X_pow_mul', if_neg (by omega),
      ← map_sub, hc]
    simp [PowerSeries.coeff_zero_eq_constantCoeff_apply, hg0]


private lemma newton (A : PowerSeries ℚ) (hA : constantCoeff A = 1) (p m : ℕ) (hp : 1 ≤ p) :
    coeff (m + 1) (A ^ p) * ((m : ℚ) + 1) =
      (p : ℚ) * ∑ k ∈ Finset.range (m + 1),
        coeff k (derivative ℚ A * A⁻¹) * coeff (m - k) (A ^ p) := by
  have hinv : A⁻¹ * A = 1 := PowerSeries.inv_mul_cancel _ (by rw [hA]; exact one_ne_zero)
  have hd : derivative ℚ (A ^ p) = C (p : ℚ) * ((derivative ℚ A * A⁻¹) * A ^ p) := by
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    rw [Derivation.leibniz_pow, Nat.add_sub_cancel, smul_eq_mul, nsmul_eq_mul,
      show derivative ℚ A * A⁻¹ * A ^ (q + 1) = derivative ℚ A * A ^ q * (A⁻¹ * A) by ring, hinv,
      ← map_natCast (C (R := ℚ)) (q + 1)]
    ring
  have := congrArg (coeff m) hd
  rw [PowerSeries.coeff_derivative, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at this
  push_cast at this
  exact this

private lemma step (A : PowerSeries ℚ) (hA0 : coeff 0 A = 1)
    (hrel : ∀ n : ℕ, 1 ≤ n → coeff n (A ^ pr n * (1 - C ((pr n : ℕ) : ℚ) * X)) = 0)
    (m : ℕ) (hA : ∀ i < m + 1, ∃ z : ℤ, coeff i A = z)
    (hL : ∀ k < m, ∃ z : ℤ, coeff k (derivative ℚ A * A⁻¹) = z) :
    (∃ z : ℤ, coeff (m + 1) A = z) ∧ (∃ z : ℤ, coeff m (derivative ℚ A * A⁻¹) = z) ∧
      (1 ≤ m → ∃ w : ℤ, coeff m (derivative ℚ A * A⁻¹) = ((pr (m + 1) : ℕ) : ℚ) * w) := by
  have hrel1 := hrel (m + 1) (by omega)
  set p := pr (m + 1) with hpdef
  have hpp : p.Prime := pr_prime _
  have hpge : m + 2 ≤ p := pr_ge (m + 1) (by omega)
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hpp.ne_zero
  have hAc : constantCoeff A = 1 := by rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hA0]
  let P : Polynomial ℤ := ∑ i ∈ Finset.range (m + 1), Polynomial.monomial i ⌊coeff i A⌋
  let g : PowerSeries ℚ := ((P.map (Int.castRingHom ℚ) : Polynomial ℚ) : PowerSeries ℚ)
  have hgc : ∀ i, coeff i g = if i < m + 1 then coeff i A else 0 := by
    intro i
    rw [Polynomial.coeff_coe, Polynomial.coeff_map, Polynomial.finset_sum_coeff]
    simp only [Polynomial.coeff_monomial, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_range]
    split_ifs with hi
    · obtain ⟨z, hz⟩ := hA i hi
      rw [hz]; simp
    · simp
  have hgt : ∀ j, coeff j (g ^ p) = (((P ^ p).coeff j : ℤ) : ℚ) := by
    intro j
    rw [← Polynomial.coe_pow, Polynomial.coeff_coe, ← Polynomial.map_pow, Polynomial.coeff_map]
    rfl
  have hg0 : constantCoeff g = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hgc, if_pos (by omega), hA0]
  obtain ⟨hlow, hn⟩ := expand_lem A g (m + 1) p (by omega) hpp.one_lt.le
    (fun i hi => by rw [hgc, if_pos hi]) hg0
  rw [hgc, if_neg (lt_irrefl _), sub_zero, hgt] at hn
  have hrel' : coeff (m + 1) (A ^ p) = (p : ℚ) * coeff m (A ^ p) := by
    rw [mul_sub, mul_one, map_sub,
      show A ^ p * (C (p : ℚ) * X) = C (p : ℚ) * A ^ p * X by ring,
      PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_C_mul, sub_eq_zero] at hrel1
    exact hrel1
  have hdiv : ∀ j, 1 ≤ j → j ≤ m + 1 → ∃ c : ℤ, (((P ^ p).coeff j : ℤ) : ℚ) = (p : ℚ) * c := by
    intro j hj1 hj2
    obtain ⟨c, hc⟩ := frob P p hpp j (by omega) (by omega)
    exact ⟨c, by rw [hc]; push_cast; ring⟩
  have hBt : ∀ j, j ≤ m → coeff j (A ^ p) = (((P ^ p).coeff j : ℤ) : ℚ) := by
    intro j hj; rw [hlow j (by omega), hgt]
  obtain ⟨c, hc⟩ := hdiv (m + 1) (by omega) le_rfl
  have hlowm := hBt m le_rfl
  have hnewt := newton A hAc p m hpp.one_lt.le
  have hB0 : coeff 0 (A ^ p) = 1 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, hAc, one_pow]
  rw [Finset.sum_range_succ, Nat.sub_self, hB0, mul_one] at hnewt
  set S := ∑ k ∈ Finset.range m, coeff k (derivative ℚ A * A⁻¹) * coeff (m - k) (A ^ p) with hSdef
  have hS : ∃ z : ℤ, S = (p : ℚ) * z := by
    have key : ∀ k ∈ Finset.range m,
        (fun x : ℚ => ∃ z : ℤ, x = (p : ℚ) * z)
          (coeff k (derivative ℚ A * A⁻¹) * coeff (m - k) (A ^ p)) := by
      intro k hk
      rw [Finset.mem_range] at hk
      obtain ⟨z1, hz1⟩ := hL k hk
      obtain ⟨c1, hc1⟩ := hdiv (m - k) (by omega) (by omega)
      refine ⟨z1 * c1, ?_⟩
      rw [hz1, hBt (m - k) (by omega), hc1]; push_cast; ring
    exact Finset.sum_induction _ (fun x : ℚ => ∃ z : ℤ, x = (p : ℚ) * z)
      (fun x y ⟨u, hu⟩ ⟨v, hv⟩ => ⟨u + v, by rw [hu, hv]; push_cast; ring⟩) ⟨0, by simp⟩ key
  obtain ⟨zS, hzS⟩ := hS
  have hLm : coeff m (derivative ℚ A * A⁻¹) = coeff m (A ^ p) * ((m : ℚ) + 1) - S := by
    apply mul_left_cancel₀ hp0
    linear_combination -hnewt + ((m : ℚ) + 1) * hrel'
  refine ⟨⟨(P ^ p).coeff m - c, ?_⟩, ⟨(P ^ p).coeff m * ((m : ℤ) + 1) - p * zS, ?_⟩, fun hm => ?_⟩
  · apply mul_left_cancel₀ hp0
    push_cast
    linear_combination -hn + hrel' + (p : ℚ) * hlowm - hc
  · rw [hLm, hlowm, hzS]; push_cast; ring
  · obtain ⟨c2, hc2⟩ := hdiv m hm (by omega)
    refine ⟨c2 * ((m : ℤ) + 1) - zS, ?_⟩
    rw [hLm, hlowm, hzS, hc2]; push_cast; ring

private theorem main' (a : ℕ → ℚ) (ha : a 0 = 1)
    (hrel : ∀ n : ℕ, 1 ≤ n → coeff n (ser a ^ pr n * (1 - C ((pr n : ℕ) : ℚ) * X)) = 0)
    (n : ℕ) (hn : 2 ≤ n) :
    ∃ m : ℤ, coeff n (X * derivative ℚ (ser a) * (ser a)⁻¹) = ((pr n : ℕ) : ℚ) * (m : ℚ) := by
  have hA0 : coeff 0 (ser a) = 1 := by rw [ser, coeff_mk, ha]
  have Q : ∀ m, (∀ i < m + 1, ∃ z : ℤ, coeff i (ser a) = z) ∧
      (∀ k < m, ∃ z : ℤ, coeff k (derivative ℚ (ser a) * (ser a)⁻¹) = z) := by
    intro m
    induction m with
    | zero =>
      exact ⟨fun i hi => ⟨1, by rw [show i = 0 by omega, hA0]; simp⟩,
        fun k hk => absurd hk (Nat.not_lt_zero _)⟩
    | succ m ih =>
      obtain ⟨h1, h2, -⟩ := step (ser a) hA0 hrel m ih.1 ih.2
      refine ⟨fun i hi => ?_, fun k hk => ?_⟩
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | h
        · exact ih.1 i h
        · rw [h]; exact h1
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hk with h | h
        · exact ih.2 k h
        · rw [h]; exact h2
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨-, -, h3⟩ := step (ser a) hA0 hrel m (Q m).1 (Q m).2
  obtain ⟨w, hw⟩ := h3 (by omega)
  exact ⟨w, by rw [mul_assoc, PowerSeries.coeff_succ_X_mul, hw]⟩

end A393866X


theorem OMA.solution : type_of% @OMA.S_oeis_a393866.main := by
  intro a ha hrel n hn
  exact A393866X.main' a ha hrel n hn
