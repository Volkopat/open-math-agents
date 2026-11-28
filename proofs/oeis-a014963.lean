import OMAStatements.S_oeis_a014963
import Mathlib

/-! The array A191898 is `T(n, k) = ∑_{d ∣ gcd(n, k)} μ(d) d`: this closed form satisfies the
defining recurrence because its sum over any `k` consecutive values of `n` is
`k ∑_{d ∣ k} μ(d) = 0` for `k ≥ 2`. Then `∑_{k ≤ K} T(n, k)/k = ∑_{d ∣ n} μ(d) H(⌊K/d⌋)`, and
`H(⌊K/d⌋) - log K → γ - log d`; with `∑_{d ∣ n} μ(d) = 0` (`n > 1`) the limit is
`-∑_{d ∣ n} μ(d) log d = Λ(n)`. -/

namespace OMA.A014963Proof

open OMA.S_oeis_a014963 Filter Topology Finset Real

/-- The closed form of `T`. -/
def G (n k : ℕ) : ℤ :=
  ∑ d ∈ k.divisors.filter (fun d => d ∣ n), (ArithmeticFunction.moebius d : ℤ) * d

lemma G_comm {n k : ℕ} (hn : n ≠ 0) (hk : k ≠ 0) : G n k = G k n := by
  unfold G
  congr 1
  ext d
  simp only [mem_filter, Nat.mem_divisors]
  tauto

lemma G_add_self (n k : ℕ) : G (n + k) k = G n k := by
  unfold G
  congr 1
  ext d
  simp only [mem_filter, Nat.mem_divisors]
  constructor <;> rintro ⟨⟨h1, h2⟩, h3⟩ <;> refine ⟨⟨h1, h2⟩, ?_⟩
  · exact (Nat.dvd_add_left h1).mp h3
  · exact (Nat.dvd_add_left h1).mpr h3

lemma sum_moebius_zero {k : ℕ} (hk : 2 ≤ k) :
    ∑ d ∈ k.divisors, (ArithmeticFunction.moebius d : ℤ) = 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f k)
    ArithmeticFunction.moebius_mul_coe_zeta
  simp only [ArithmeticFunction.coe_mul_zeta_apply] at h
  rw [h, ArithmeticFunction.one_apply_ne (by omega)]

lemma window_zero {k : ℕ} (hk : 2 ≤ k) (m : ℕ) : ∑ i ∈ range k, G (m + 1 + i) k = 0 := by
  induction m with
  | zero =>
    have h1 : ∀ i, G (0 + 1 + i) k = ∑ d ∈ k.divisors,
        if d ∣ i + 1 then (ArithmeticFunction.moebius d : ℤ) * d else 0 := by
      intro i
      rw [G, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro d _
      rw [show 0 + 1 + i = i + 1 by ring]
    simp_rw [h1]
    rw [Finset.sum_comm]
    have h2 : ∀ d ∈ k.divisors, (∑ i ∈ range k,
        if d ∣ i + 1 then (ArithmeticFunction.moebius d : ℤ) * d else 0) =
        (ArithmeticFunction.moebius d : ℤ) * k := by
      intro d hd
      rw [← Finset.sum_filter, Finset.sum_const, Nat.card_multiples, nsmul_eq_mul]
      obtain ⟨e, he⟩ := Nat.dvd_of_mem_divisors hd
      have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
      rw [he, Nat.mul_div_cancel_left _ hd0]
      push_cast
      ring
    rw [Finset.sum_congr rfl h2, ← Finset.sum_mul, sum_moebius_zero hk, zero_mul]
  | succ m ih =>
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [Finset.sum_range_succ'] at ih
    rw [Finset.sum_range_succ]
    have e1 : m + 1 + 1 + k' = (m + 1) + (k' + 1) := by ring
    rw [e1, G_add_self]
    have e2 : ∀ i ∈ range k', G (m + 1 + (i + 1)) (k' + 1) = G (m + 1 + 1 + i) (k' + 1) := by
      intro i _
      congr 1
      ring
    rw [Finset.sum_congr rfl e2, add_zero] at ih
    exact ih

lemma rec_helper (a b : ℕ) (hb : 2 ≤ b) (hab : b ≤ a) (F : ℕ → ℤ)
    (hF : ∀ i, 1 ≤ i → i < b → F i = G (a - i) b) :
    -(∑ i : Fin b, if h : (i : ℕ) = 0 then (0 : ℤ) else F (i : ℕ)) = G a b := by
  rw [Fin.sum_univ_eq_sum_range (fun i => if h : i = 0 then (0 : ℤ) else F i) b]
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  rw [Finset.sum_range_succ']
  have h1 : ∀ i ∈ range b', (if h : i + 1 = 0 then (0 : ℤ) else F (i + 1)) =
      G (a - (i + 1)) (b' + 1) := by
    intro i hi
    rw [dif_neg (by omega)]
    exact hF _ (by omega) (by simp at hi; omega)
  rw [Finset.sum_congr rfl h1, dif_pos rfl, add_zero]
  have hw := window_zero hb (a - (b' + 1))
  rw [← Finset.sum_range_reflect, Finset.sum_range_succ'] at hw
  have h2 : ∀ j ∈ range b', G (a - (b' + 1) + 1 + (b' + 1 - 1 - (j + 1))) (b' + 1) =
      G (a - (j + 1)) (b' + 1) := by
    intro j hj
    simp at hj
    congr 1
    omega
  rw [Finset.sum_congr rfl h2] at hw
  have h3 : a - (b' + 1) + 1 + (b' + 1 - 1 - 0) = a := by omega
  rw [h3] at hw
  linarith

theorem T_eq : ∀ s n k, n + k = s → 1 ≤ n → 1 ≤ k → T n k = G n k := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
  intro n k hs hn hk
  rw [T, dif_neg (by omega)]
  by_cases h1 : k = 1 ∨ n = 1
  · rw [dif_pos h1]
    rcases h1 with rfl | rfl
    · simp [G, Finset.filter_singleton]
    · simp [G, Finset.filter_eq', show k ≠ 0 by omega]
  · rw [dif_neg h1]
    by_cases hkn : k ≤ n
    · rw [dif_pos hkn]
      exact rec_helper n k (by omega) hkn (fun i => T (n - i) k)
        (fun i hi1 hi2 => ih _ (by omega) _ _ rfl (by omega) (by omega))
    · rw [dif_neg hkn, G_comm (by omega) (by omega)]
      exact rec_helper k n (by omega) (by omega) (fun i => T (k - i) n)
        (fun i hi1 hi2 => ih _ (by omega) _ _ rfl (by omega) (by omega))

lemma inner (d K : ℕ) (hd : 0 < d) :
    ∑ k ∈ Icc 1 K, (if d ∣ k then (d : ℝ) / k else 0) = (harmonic (K / d) : ℝ) := by
  rw [harmonic_eq_sum_Icc, ← Finset.sum_filter]
  have : (Icc 1 K).filter (fun k => d ∣ k) =
      (Icc 1 (K / d)).map ⟨(d * ·), mul_right_injective₀ hd.ne'⟩ := by
    ext k
    simp only [mem_filter, mem_Icc, Finset.mem_map, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨⟨h1, h2⟩, j, rfl⟩
      refine ⟨j, ⟨?_, ?_⟩, rfl⟩
      · rcases Nat.eq_zero_or_pos j with rfl | hj
        · simp at h1
        · exact hj
      · exact (Nat.le_div_iff_mul_le hd).mpr (by rw [mul_comm]; exact h2)
    · rintro ⟨j, ⟨h1, h2⟩, rfl⟩
      refine ⟨⟨by nlinarith, ?_⟩, dvd_mul_right d j⟩
      have := (Nat.le_div_iff_mul_le hd).mp h2
      rw [mul_comm]; exact this
  rw [this, Finset.sum_map]
  push_cast
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Function.Embedding.coeFn_mk]
  have hj0 : (j : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by simp at hj; omega)
  have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  push_cast
  field_simp

lemma partial_sum {n : ℕ} (hn : 1 < n) (K : ℕ) :
    ∑ k ∈ Icc 1 K, (T n k : ℝ) / k =
      ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ) * (harmonic (K / d) : ℝ) := by
  have h1 : ∀ k ∈ Icc 1 K, (T n k : ℝ) / k = ∑ d ∈ n.divisors,
      (ArithmeticFunction.moebius d : ℝ) * (if d ∣ k then (d : ℝ) / k else 0) := by
    intro k hk
    simp only [mem_Icc] at hk
    rw [T_eq _ n k rfl (by omega) hk.1, G_comm (by omega) (by omega), G, Finset.sum_filter]
    push_cast
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro d _
    split_ifs <;> ring
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [← Finset.mul_sum, inner d K (Nat.pos_of_mem_divisors hd)]

lemma ratio_tendsto {d : ℕ} (hd : 0 < d) :
    Tendsto (fun K : ℕ => ((K / d : ℕ) : ℝ) / K) atTop (𝓝 (1 / d)) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hlow : Tendsto (fun K : ℕ => (1 : ℝ) / d - 1 / K) atTop (𝓝 (1 / d)) := by
    have := (tendsto_one_div_atTop_nhds_zero_nat).const_sub ((1 : ℝ) / d)
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with K hK
    have hK' : (0 : ℝ) < K := by exact_mod_cast hK
    have hdm := Nat.div_add_mod K d
    have hmod := Nat.mod_lt K hd
    have hc : (K : ℝ) = d * ((K / d : ℕ) : ℝ) + ((K % d : ℕ) : ℝ) := by exact_mod_cast hdm.symm
    have hm : ((K % d : ℕ) : ℝ) < d := by exact_mod_cast hmod
    rw [div_sub_div _ _ hd'.ne' hK'.ne', div_le_div_iff₀ (by positivity) hK']
    nlinarith
  · filter_upwards [eventually_gt_atTop 0] with K hK
    have hK' : (0 : ℝ) < K := by exact_mod_cast hK
    rw [div_le_div_iff₀ hK' hd']
    have := (Nat.cast_div_le (α := ℝ) (m := K) (n := d))
    rw [le_div_iff₀ hd'] at this
    linarith

lemma log_part {d : ℕ} (hd : 0 < d) :
    Tendsto (fun K : ℕ => Real.log ((K / d : ℕ) : ℝ) - Real.log K) atTop (𝓝 (-Real.log d)) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have h := (ratio_tendsto hd).log (by positivity)
  rw [one_div, Real.log_inv] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop d] with K hK
  have h1 : 0 < K / d := Nat.div_pos hK hd
  rw [Real.log_div (by exact_mod_cast h1.ne') (by exact_mod_cast (by omega : K ≠ 0))]

lemma harm_part {d : ℕ} (hd : 0 < d) :
    Tendsto (fun K : ℕ => (harmonic (K / d) : ℝ) - Real.log K) atTop
      (𝓝 (eulerMascheroniConstant - Real.log d)) := by
  have h1 := tendsto_harmonic_sub_log.comp (Nat.tendsto_div_const_atTop hd.ne')
  have h2 := h1.add (log_part hd)
  rw [← sub_eq_add_neg] at h2
  refine h2.congr (fun K => ?_)
  simp only [Function.comp]
  ring

theorem solution : ∀ n : ℕ, 1 < n →
    Tendsto (fun K : ℕ => ∑ k ∈ Finset.Icc 1 K, (T n k : ℝ) / k) atTop
      (𝓝 (ArithmeticFunction.vonMangoldt n)) := by
  intro n hn
  have hμ : ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ) = 0 := by
    exact_mod_cast sum_moebius_zero (k := n) (by omega)
  have hlim : Tendsto (fun K : ℕ => ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ) *
      ((harmonic (K / d) : ℝ) - Real.log K)) atTop
      (𝓝 (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ) *
        (eulerMascheroniConstant - Real.log d))) := by
    apply tendsto_finsetSum
    intro d hd
    exact (harm_part (Nat.pos_of_mem_divisors hd)).const_mul _
  have hval : ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ) *
      (eulerMascheroniConstant - Real.log d) = ArithmeticFunction.vonMangoldt n := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    have hl := ArithmeticFunction.sum_moebius_mul_log_eq (n := n)
    simp only [ArithmeticFunction.log_apply] at hl
    rw [← Finset.sum_mul, hμ, zero_mul, hl]
    ring
  rw [hval] at hlim
  refine hlim.congr ?_
  intro K
  rw [partial_sum hn K]
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [← Finset.sum_mul, hμ, zero_mul, sub_zero]

end OMA.A014963Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a014963.main := OMA.A014963Proof.solution
