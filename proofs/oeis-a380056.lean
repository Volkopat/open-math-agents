import OMAStatements.S_oeis_a380056

/-!
OEIS A380056: https://oeis.org/A380056
Formal statement credited to @sntntHb. Solution by @grp06.

The factorial-scaled cosine coefficients give a triangular binomial
convolution. Modulo five, the cosine factor retains just the even
indices, so two binomial expansions give its action on a geometric
sequence.
-/

namespace A380056Proof

open Finset PowerSeries
open OMA.S_oeis_a380056

private def C (j : ℕ) : ℤ :=
  if Even j then (-4) ^ (j / 2) else 0

private def rhs {R : Type*} [Zero R] [One R] (n : ℕ) : R :=
  if n = 0 then 0 else 1

private def convolution {R : Type*} [Ring R] (c u : ℕ → R) (n : ℕ) : R :=
  ∑ j ∈ range (n + 1), (n.choose j : R) * c j * u (n - j)

private def tail {R : Type*} [Ring R] (c u : ℕ → R) (n : ℕ) : R :=
  ∑ j ∈ range n, (n.choose (j + 1) : R) * c (j + 1) * u (n - (j + 1))

private theorem convolution_split {R : Type*} [Ring R] (c u : ℕ → R)
    (hc : c 0 = 1) (n : ℕ) :
    convolution c u n = tail c u n + u n := by
  unfold convolution tail
  rw [Finset.sum_range_succ']
  simp [hc]

private theorem tail_congr {R : Type*} [Ring R] (c u v : ℕ → R) (n : ℕ)
    (h : ∀ k < n, u k = v k) : tail c u n = tail c v n := by
  unfold tail
  apply Finset.sum_congr rfl
  intro j hj
  have hk : n - (j + 1) < n := by
    have hjn := Finset.mem_range.mp hj
    omega
  rw [h (n - (j + 1)) hk]

private theorem C_zero : C 0 = 1 := by simp [C]

private theorem scaled_cos (j : ℕ) :
    (j.factorial : ℚ) * coeff j (rescale (2 : ℚ) (cos ℚ)) = (C j : ℚ) := by
  rw [coeff_rescale, cos, coeff_mk]
  by_cases hj : Even j
  · obtain ⟨k, hk⟩ := even_iff_two_dvd.mp hj
    have he : 2 * (j / 2) = j := by omega
    have hp : (2 : ℚ) ^ j = (4 : ℚ) ^ (j / 2) := calc
      (2 : ℚ) ^ j = 2 ^ (2 * (j / 2)) := congrArg (fun e : ℕ => (2 : ℚ) ^ e) he.symm
      _ = 4 ^ (j / 2) := by rw [pow_mul]; norm_num
    have hf : (j.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
    simp only [if_pos hj, Algebra.algebraMap_self_apply, C, Int.cast_pow, Int.cast_neg,
      Int.cast_ofNat]
    rw [hp]
    calc
      (j.factorial : ℚ) * (4 ^ (j / 2) * ((-1) ^ (j / 2) / j.factorial)) =
          4 ^ (j / 2) * ((j.factorial : ℚ) * ((-1) ^ (j / 2) / j.factorial)) := by ring
      _ = (-4) ^ (j / 2) := by
        rw [mul_div_cancel₀ _ hf, ← mul_pow]; norm_num
  · simp [C, hj]

private theorem egf_cancel :
    rescale (2 : ℚ) (cos ℚ) * egf = exp ℚ - 1 := by
  have hc : constantCoeff (rescale (2 : ℚ) (cos ℚ)) = 1 := by
    simpa only [Nat.factorial_zero, Nat.cast_one, one_mul, C_zero, Int.cast_one,
      coeff_zero_eq_constantCoeff_apply] using scaled_cos 0
  unfold egf
  calc
    _ = (exp ℚ - 1) * ((rescale (2 : ℚ) (cos ℚ))⁻¹ * rescale (2 : ℚ) (cos ℚ)) := by
      ac_rfl
    _ = _ := by rw [PowerSeries.inv_mul_cancel _ (by rw [hc]; exact one_ne_zero), mul_one]

private theorem scaled_exp_sub (n : ℕ) :
    (n.factorial : ℚ) * coeff n (exp ℚ - 1) = (rhs n : ℚ) := by
  by_cases hn : n = 0
  · subst n
    norm_num [rhs, coeff_exp]
  · have hf : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    simp only [map_sub, coeff_exp, Algebra.algebraMap_self_apply, coeff_one,
      if_neg hn, sub_zero, rhs]
    exact mul_div_cancel₀ _ hf

private theorem rational_recurrence (n : ℕ) :
    convolution (fun j => (C j : ℚ)) a n = rhs n := by
  have h := congrArg (fun f : PowerSeries ℚ => (n.factorial : ℚ) * coeff n f) egf_cancel
  change (n.factorial : ℚ) * coeff n (rescale (2 : ℚ) (cos ℚ) * egf) =
    (n.factorial : ℚ) * coeff n (exp ℚ - 1) at h
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun j k => coeff j (rescale (2 : ℚ) (cos ℚ)) * coeff k egf) n,
    Finset.mul_sum, scaled_exp_sub] at h
  rw [← h]
  unfold convolution
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j ≤ n := by have := Finset.mem_range.mp hj; omega
  have hf : (n.choose j : ℚ) * (j.factorial : ℚ) * ((n - j).factorial : ℚ) =
      (n.factorial : ℚ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hjn
  change (n.choose j : ℚ) * (C j : ℚ) * a (n - j) =
    (n.factorial : ℚ) * (coeff j (rescale (2 : ℚ) (cos ℚ)) * coeff (n - j) egf)
  rw [← scaled_cos j, a, ← hf]
  ring

private theorem a_zero : a 0 = 0 := by
  have h := rational_recurrence 0
  have hc : (C 0 : ℚ) = 1 := by simp [C_zero]
  rw [convolution_split (fun j => (C j : ℚ)) a hc 0] at h
  simpa [tail, rhs] using h

private theorem tail_cast_rat (u : ℕ → ℤ) (n : ℕ) :
    (↑(tail (R := ℤ) C u n) : ℚ) = tail (fun j => (C j : ℚ)) (fun j => (u j : ℚ)) n := by
  change (Int.castRingHom ℚ) (tail C u n) = _
  simp only [tail, map_sum, map_mul, map_natCast]
  simp only [Int.coe_castRingHom]

private theorem integral (n : ℕ) : ∃ z : ℤ, a n = (z : ℚ) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    classical
    let u (k : ℕ) : ℤ := if hk : k < n then Classical.choose (ih k hk) else 0
    have hu (k : ℕ) (hk : k < n) : a k = (u k : ℚ) := by
      simpa only [u, dif_pos hk] using Classical.choose_spec (ih k hk)
    have h := rational_recurrence n
    have hc : (C 0 : ℚ) = 1 := by simp [C_zero]
    rw [convolution_split (fun j => (C j : ℚ)) a hc n,
      tail_congr (fun j => (C j : ℚ)) a (fun k => (u k : ℚ)) n hu,
      ← tail_cast_rat u n] at h
    refine ⟨(rhs n : ℤ) - tail C u n, ?_⟩
    have hr : ((rhs n : ℤ) : ℚ) = rhs n := by by_cases hn : n = 0 <;> simp [rhs, hn]
    rw [Int.cast_sub, hr, ← h]
    ring

private noncomputable def A (n : ℕ) : ℤ := Classical.choose (integral n)

private theorem a_eq (n : ℕ) : a n = (A n : ℚ) :=
  Classical.choose_spec (integral n)

private theorem convolution_cast {R : Type*} [Ring R] (u : ℕ → ℤ) (n : ℕ) :
    (↑(convolution (R := ℤ) C u n) : R) =
      convolution (fun j => (C j : R)) (fun j => (u j : R)) n := by
  change (Int.castRingHom R) (convolution C u n) = _
  simp only [convolution, map_sum, map_mul, map_natCast]
  simp only [Int.coe_castRingHom]

private theorem rhs_cast {R : Type*} [Ring R] (n : ℕ) :
    ((rhs n : ℤ) : R) = rhs n := by
  by_cases hn : n = 0 <;> simp [rhs, hn]

private theorem integral_recurrence (n : ℕ) : convolution C A n = rhs n := by
  apply (Int.cast_injective (α := ℚ))
  change (↑(convolution (R := ℤ) C A n) : ℚ) = ((rhs n : ℤ) : ℚ)
  have ha : a = (fun j => (A j : ℚ)) := funext a_eq
  rw [convolution_cast A n, rhs_cast n, ← ha]
  exact rational_recurrence n

private theorem cast_recurrence {R : Type*} [Ring R] (n : ℕ) :
    convolution (fun j => (C j : R)) (fun j => (A j : R)) n = rhs n := by
  rw [← convolution_cast A n, integral_recurrence n, rhs_cast n]

private theorem C_mod_four (j : ℕ) (hj : j ≠ 0) : (C j : ZMod 4) = 0 := by
  by_cases he : Even j
  · obtain ⟨k, hk⟩ := even_iff_two_dvd.mp he
    have hp : j / 2 ≠ 0 := by omega
    have hz : (-4 : ZMod 4) = 0 := by decide
    simp [C, he, hz, zero_pow hp]
  · simp [C, he]

private theorem A_mod_four (n : ℕ) (hn : n ≠ 0) : (A n : ZMod 4) = 1 := by
  have h := cast_recurrence (R := ZMod 4) n
  have hc : (C 0 : ZMod 4) = 1 := by simp [C_zero]
  rw [convolution_split (fun j => (C j : ZMod 4)) (fun j => (A j : ZMod 4)) hc n] at h
  have ht : tail (fun j => (C j : ZMod 4)) (fun j => (A j : ZMod 4)) n = 0 := by
    unfold tail
    apply Finset.sum_eq_zero
    intro j _
    change (n.choose (j + 1) : ZMod 4) * (C (j + 1) : ZMod 4) *
      (A (n - (j + 1)) : ZMod 4) = 0
    rw [C_mod_four (j + 1) (Nat.succ_ne_zero j), mul_zero, zero_mul]
  simpa [ht, rhs, hn] using h

private theorem C_mod_five (j : ℕ) :
    2 * (C j : ZMod 5) = 1 + (-1 : ZMod 5) ^ j := by
  have h : (-4 : ZMod 5) = 1 := by decide
  by_cases hj : Even j
  · simp [C, hj, h, one_add_one_eq_two]
  · simp [C, hj, neg_one_pow_eq_ite]

private def B (n : ℕ) : ZMod 5 := 2 * 2 ^ n - 2 * 4 ^ n

private theorem binomial_pair (x : ZMod 5) (n : ℕ) :
    (∑ j ∈ range (n + 1), (n.choose j : ZMod 5) * (1 + (-1) ^ j) * x ^ (n - j)) =
      (1 + x) ^ n + (-1 + x) ^ n := by
  rw [add_pow (1 : ZMod 5) x n, add_pow (-1 : ZMod 5) x n, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [one_pow]
  ring

private theorem B_recurrence (n : ℕ) :
    convolution (fun j => (C j : ZMod 5)) B n = rhs n := by
  calc
    convolution (fun j => (C j : ZMod 5)) B n =
        (∑ j ∈ range (n + 1), (n.choose j : ZMod 5) * (1 + (-1) ^ j) * 2 ^ (n - j)) -
        (∑ j ∈ range (n + 1), (n.choose j : ZMod 5) * (1 + (-1) ^ j) * 4 ^ (n - j)) := by
      rw [← Finset.sum_sub_distrib]
      unfold convolution B
      apply Finset.sum_congr rfl
      intro j _
      rw [← C_mod_five j]
      ring
    _ = _ := by
      rw [binomial_pair, binomial_pair]
      have h12 : (1 + 2 : ZMod 5) = 3 := by decide
      have h14 : (1 + 4 : ZMod 5) = 0 := by decide
      have hm2 : (-1 + 2 : ZMod 5) = 1 := by decide
      have hm4 : (-1 + 4 : ZMod 5) = 3 := by decide
      simp only [h12, h14, hm2, hm4, one_pow]
      by_cases hn : n = 0
      · subst n
        simp [rhs]
      · rw [zero_pow hn, rhs, if_neg hn]
        ring

private theorem A_mod_five (n : ℕ) : (A n : ZMod 5) = B n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have ha := cast_recurrence (R := ZMod 5) n
    have hb := B_recurrence n
    have hc : (C 0 : ZMod 5) = 1 := by simp [C_zero]
    rw [convolution_split (fun j => (C j : ZMod 5)) (fun j => (A j : ZMod 5)) hc n,
      tail_congr (fun j => (C j : ZMod 5)) (fun j => (A j : ZMod 5)) B n ih] at ha
    rw [convolution_split (fun j => (C j : ZMod 5)) B hc n] at hb
    exact add_left_cancel (ha.trans hb.symm)

private theorem B_four_mul (n : ℕ) : B (4 * n) = 0 := by
  have h2 : (2 : ZMod 5) ^ (4 : ℕ) = 1 := by decide
  have h4 : (4 : ZMod 5) ^ (4 : ℕ) = 1 := by decide
  simp only [B, pow_mul, h2, h4, one_pow, mul_one, sub_self]

theorem congruences :
    (∀ n : ℕ, 1 ≤ n → ∃ m : ℤ, a n = 4 * (m : ℚ) + 1) ∧
      (∀ n : ℕ, 1 ≤ n → ∃ m : ℤ, a (4 * n) = 5 * (m : ℚ)) := by
  constructor
  · intro n hn
    have hc : ((A n - 1 : ℤ) : ZMod 4) = 0 := by
      rw [Int.cast_sub, Int.cast_one, A_mod_four n (by omega), sub_self]
    obtain ⟨m, hm⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (A n - 1) 4).mp hc
    refine ⟨m, ?_⟩
    have hz : A n = 4 * m + 1 := by
      change A n - 1 = 4 * m at hm
      omega
    rw [a_eq, hz]
    push_cast
    rfl
  · intro n _
    have hc : (A (4 * n) : ZMod 5) = 0 :=
      (A_mod_five (4 * n)).trans (B_four_mul n)
    obtain ⟨m, hm⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (A (4 * n)) 5).mp hc
    refine ⟨m, ?_⟩
    change A (4 * n) = 5 * m at hm
    rw [a_eq, hm]
    push_cast
    rfl

end A380056Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a380056.main :=
  A380056Proof.congruences
