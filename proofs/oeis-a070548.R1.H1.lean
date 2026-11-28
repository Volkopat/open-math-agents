import OMAReductions.R_oeis_a070548_R1
import Mathlib

/-! The density of the squarefree numbers is 6 / pi^2.

For k >= 1 write k = b^2 a with a squarefree. Then d^2 | k exactly when d | b, so the sum of
mu(d) over d^2 | k is the sum of mu over the divisors of b, which is 1 if b = 1 (that is, if k is
squarefree) and 0 otherwise. Summing over k <= n and exchanging the sums, the number of squarefree
k <= n is the sum over d of mu(d) floor(n / d^2). Dividing by n, each term tends to mu(d) / d^2
and is at most 1 / d^2 in absolute value, so by dominated convergence for series (Tannery) the
proportion tends to the sum of mu(d) / d^2, which is 1 / zeta(2) = 6 / pi^2. The two sign classes
of the Möbius function together are exactly the squarefree numbers. -/

open Finset

namespace SqfreeDensity

/-- The Dirichlet series of the Möbius function at 2. -/
lemma tsum_moebius_div_sq :
    ∑' d : ℕ, ((ArithmeticFunction.moebius d : ℤ) : ℝ) / (d : ℝ) ^ 2 = 6 / Real.pi ^ 2 := by
  have hs : (1 : ℝ) < (2 : ℂ).re := by norm_num
  have h1 := ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius hs
  rw [ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs, riemannZeta_two] at h1
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h2 : LSeries (fun n : ℕ => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) 2 =
      6 / (Real.pi : ℂ) ^ 2 := by
    field_simp
    field_simp at h1
    linear_combination h1
  have h3 : LSeries (fun n : ℕ => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) 2 =
      ((∑' d : ℕ, ((ArithmeticFunction.moebius d : ℤ) : ℝ) / (d : ℝ) ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    unfold LSeries
    congr 1
    funext n
    rw [LSeries.term_def]
    split_ifs with hn
    · simp [hn]
    · rw [Complex.cpow_ofNat]
      push_cast
      rfl
  rw [h3] at h2
  exact_mod_cast h2

/-- For squarefree `a`, `d ^ 2 ∣ b ^ 2 * a` exactly when `d ∣ b`. -/
lemma sq_dvd_iff {a b d : ℕ} (ha : Squarefree a) (hd : 0 < d) :
    d * d ∣ b * b * a ↔ d ∣ b := by
  constructor
  · intro h
    obtain ⟨d', b', hcop, hd', hb'⟩ := Nat.exists_coprime d b
    have hg : 0 < Nat.gcd d b := Nat.gcd_pos_of_pos_left _ hd
    have h1 : d' * d' * (Nat.gcd d b * Nat.gcd d b) ∣ b' * b' * a * (Nat.gcd d b * Nat.gcd d b) := by
      have e1 : d' * d' * (Nat.gcd d b * Nat.gcd d b) = d * d := by
        conv_rhs => rw [hd']
        ring
      have e2 : b' * b' * a * (Nat.gcd d b * Nat.gcd d b) = b * b * a := by
        conv_rhs => rw [hb']
        ring
      rw [e1, e2]
      exact h
    have h2 : d' * d' ∣ b' * b' * a := Nat.dvd_of_mul_dvd_mul_right (Nat.mul_pos hg hg) h1
    have hcop2 : Nat.Coprime (d' * d') (b' * b') := Nat.Coprime.mul_left (Nat.Coprime.mul_right hcop hcop) (Nat.Coprime.mul_right hcop hcop)
    have h3 : d' * d' ∣ a := hcop2.dvd_of_dvd_mul_left h2
    have h4 : d' = 1 := Nat.isUnit_iff.mp (ha d' h3)
    rw [hd', h4, one_mul]
    exact Nat.gcd_dvd_right d b
  · intro h
    exact Dvd.dvd.mul_right (Nat.mul_dvd_mul h h) a


/-- The indicator of the squarefree numbers as a Möbius sum over square divisors. -/
lemma sum_moebius_sq_dvd {k N : ℕ} (hk : 1 ≤ k) (hkN : k ≤ N) :
    ∑ d ∈ (Finset.Icc 1 N).filter (fun d => d * d ∣ k), ArithmeticFunction.moebius d =
      if Squarefree k then 1 else 0 := by
  obtain ⟨a, b, hab, ha⟩ := Nat.sq_mul_squarefree k
  have hk' : k = b * b * a := by
    rw [← hab]
    ring
  have hb : 0 < b := by
    rcases Nat.eq_zero_or_pos b with h | h
    · rw [h] at hk'
      simp at hk'
      omega
    · exact h
  have hapos : 0 < a := by
    rcases Nat.eq_zero_or_pos a with h | h
    · rw [h] at hk'
      simp at hk'
      omega
    · exact h
  have hbk : b ≤ k := by
    calc b ≤ b * b := Nat.le_mul_self b
      _ ≤ b * b * a := Nat.le_mul_of_pos_right _ hapos
      _ = k := hk'.symm
  have hset : (Finset.Icc 1 N).filter (fun d => d * d ∣ k) = b.divisors := by
    ext d
    rw [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hd1, -⟩, hdk⟩
      rw [hk'] at hdk
      exact ⟨(sq_dvd_iff ha (by omega)).mp hdk, hb.ne'⟩
    · rintro ⟨hdb, -⟩
      have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos hdb hb
      have hdle : d ≤ b := Nat.le_of_dvd hb hdb
      refine ⟨⟨hd1, by omega⟩, ?_⟩
      rw [hk']
      exact (sq_dvd_iff ha (by omega)).mpr hdb
  rw [hset]
  have hsum : ∑ d ∈ b.divisors, ArithmeticFunction.moebius d = if b = 1 then 1 else 0 := by
    have h := congrArg (fun f : ArithmeticFunction ℤ => f b)
      ArithmeticFunction.moebius_mul_coe_zeta
    simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
    exact h
  rw [hsum]
  have hiff : b = 1 ↔ Squarefree k := by
    constructor
    · intro h1
      rw [hk', h1]
      simpa using ha
    · intro hsq
      exact Nat.isUnit_iff.mp (hsq b ⟨a, hk'⟩)
  simp only [hiff]

/-- The number of squarefree integers up to `n` as a Möbius sum. -/
lemma card_squarefree (n : ℕ) :
    (((Finset.Icc 1 n).filter (fun k => Squarefree k)).card : ℤ) =
      ∑ d ∈ Finset.Icc 1 n, ArithmeticFunction.moebius d * ((n / (d * d) : ℕ) : ℤ) := by
  classical
  rw [Finset.card_filter]
  push_cast
  have h1 : ∀ k ∈ Finset.Icc 1 n, (if Squarefree k then (1 : ℤ) else 0) =
      ∑ d ∈ Finset.Icc 1 n, if d * d ∣ k then ArithmeticFunction.moebius d else 0 := by
    intro k hk
    obtain ⟨hk1, hkn⟩ := Finset.mem_Icc.mp hk
    rw [← sum_moebius_sq_dvd hk1 hkn, Finset.sum_filter]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  congr 1
  have hIcc : Finset.Icc 1 n = Finset.Ioc 0 n := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have h := Nat.Ioc_filter_dvd_card_eq_div n (d * d)
  rw [hIcc]
  exact_mod_cast h

/-- The two sign classes of the Möbius function together are the squarefree numbers. -/
lemma card_sign_add (n : ℕ) :
    ((Finset.Icc 1 n).filter (fun k => ArithmeticFunction.moebius k = 1)).card +
      ((Finset.Icc 1 n).filter (fun k => ArithmeticFunction.moebius k = -1)).card =
      ((Finset.Icc 1 n).filter (fun k => Squarefree k)).card := by
  classical
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext k
    simp only [Finset.mem_union, Finset.mem_filter]
    rw [← ArithmeticFunction.moebius_ne_zero_iff_squarefree,
      ArithmeticFunction.moebius_ne_zero_iff_eq_or]
    tauto
  · rw [Finset.disjoint_filter]
    intro k _ h1 h2
    rw [h1] at h2
    norm_num at h2


/-- Each summand of the Möbius formula converges. -/
lemma term_tendsto (d : ℕ) :
    Filter.Tendsto (fun n : ℕ =>
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) * ((n / (d * d) : ℕ) : ℝ) / (n : ℝ))
      Filter.atTop (nhds (((ArithmeticFunction.moebius d : ℤ) : ℝ) / (d : ℝ) ^ 2)) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  · have hm : 0 < d * d := Nat.mul_pos hd hd
    have hmR : (0 : ℝ) < ((d * d : ℕ) : ℝ) := by exact_mod_cast hm
    have hratio : Filter.Tendsto (fun n : ℕ => ((n / (d * d) : ℕ) : ℝ) / (n : ℝ)) Filter.atTop
        (nhds (1 / ((d * d : ℕ) : ℝ))) := by
      have hlow : Filter.Tendsto (fun n : ℕ => 1 / ((d * d : ℕ) : ℝ) - 1 / (n : ℝ)) Filter.atTop
          (nhds (1 / ((d * d : ℕ) : ℝ))) := by
        have h := (tendsto_const_nhds (x := 1 / ((d * d : ℕ) : ℝ))
          (f := (Filter.atTop : Filter ℕ))).sub tendsto_one_div_atTop_nhds_zero_nat
        simpa using h
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
      · filter_upwards [Filter.eventually_ge_atTop 1] with n hn
        have hnR : (0 : ℝ) < n := by exact_mod_cast hn
        have hdm : (d * d) * (n / (d * d)) + n % (d * d) = n := Nat.div_add_mod n (d * d)
        have hmod : n % (d * d) < d * d := Nat.mod_lt n hm
        have hreal : (n : ℝ) < ((d * d : ℕ) : ℝ) * ((n / (d * d) : ℕ) : ℝ) + ((d * d : ℕ) : ℝ) := by
          have h' : n < (d * d) * (n / (d * d)) + d * d := by omega
          exact_mod_cast h'
        rw [div_sub_div _ _ hmR.ne' hnR.ne', div_le_div_iff₀ (mul_pos hmR hnR) hnR]
        have h1 : (n : ℝ) - ((d * d : ℕ) : ℝ) ≤ ((d * d : ℕ) : ℝ) * ((n / (d * d) : ℕ) : ℝ) := by
          linarith
        nlinarith [mul_le_mul_of_nonneg_right h1 hnR.le]
      · filter_upwards [Filter.eventually_ge_atTop 1] with n hn
        have hnR : (0 : ℝ) < n := by exact_mod_cast hn
        have hle : ((n / (d * d) : ℕ) : ℝ) ≤ (n : ℝ) / ((d * d : ℕ) : ℝ) := Nat.cast_div_le
        rw [div_le_div_iff₀ hnR hmR]
        have h1 := (le_div_iff₀ hmR).mp hle
        linarith
    have h := hratio.const_mul ((ArithmeticFunction.moebius d : ℤ) : ℝ)
    have hval : ((ArithmeticFunction.moebius d : ℤ) : ℝ) * (1 / ((d * d : ℕ) : ℝ)) =
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) / (d : ℝ) ^ 2 := by
      push_cast
      ring
    rw [← hval]
    exact h.congr (fun n => by ring)

/-- The summands are dominated by `1 / d ^ 2`. -/
lemma term_bound {n : ℕ} (hn : 1 ≤ n) (d : ℕ) :
    ‖((ArithmeticFunction.moebius d : ℤ) : ℝ) * ((n / (d * d) : ℕ) : ℝ) / (n : ℝ)‖ ≤
      1 / (d : ℝ) ^ 2 := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  · have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd
    have hmu : |((ArithmeticFunction.moebius d : ℤ) : ℝ)| ≤ 1 := by
      have h := ArithmeticFunction.abs_moebius_le_one (n := d)
      exact_mod_cast h
    have hle : ((n / (d * d) : ℕ) : ℝ) ≤ (n : ℝ) / ((d * d : ℕ) : ℝ) := Nat.cast_div_le
    have hfl0 : (0 : ℝ) ≤ ((n / (d * d) : ℕ) : ℝ) := Nat.cast_nonneg _
    have hd2 : (0 : ℝ) < (d : ℝ) ^ 2 := by positivity
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_nonneg hfl0, abs_of_pos hnR,
      div_le_div_iff₀ hnR hd2]
    push_cast at hle
    have h1 : ((n / (d * d) : ℕ) : ℝ) * (d : ℝ) ^ 2 ≤ n := by
      have h2 := (le_div_iff₀ (by positivity)).mp hle
      nlinarith
    have h3 : (0 : ℝ) ≤ ((n / (d * d) : ℕ) : ℝ) * (d : ℝ) ^ 2 := mul_nonneg hfl0 hd2.le
    nlinarith [mul_le_mul_of_nonneg_right hmu h3]

/-- The density of the squarefree numbers is `6 / π ^ 2`. -/
theorem squarefree_density :
    Filter.Tendsto (fun n : ℕ =>
        ((((Finset.Icc 1 n).filter (fun k => ArithmeticFunction.moebius k = 1)).card : ℝ) +
          (((Finset.Icc 1 n).filter (fun k => ArithmeticFunction.moebius k = -1)).card : ℝ)) / n)
      Filter.atTop (nhds (6 / Real.pi ^ 2)) := by
  have hT := tendsto_tsum_of_dominated_convergence
    (f := fun (n : ℕ) (d : ℕ) =>
      ((ArithmeticFunction.moebius d : ℤ) : ℝ) * ((n / (d * d) : ℕ) : ℝ) / (n : ℝ))
    (g := fun d : ℕ => ((ArithmeticFunction.moebius d : ℤ) : ℝ) / (d : ℝ) ^ 2)
    (bound := fun d : ℕ => 1 / (d : ℝ) ^ 2) (𝓕 := Filter.atTop)
    (Real.summable_one_div_nat_pow.mpr (by norm_num)) term_tendsto
    (by
      filter_upwards [Filter.eventually_ge_atTop 1] with n hn
      exact term_bound hn)
  rw [tsum_moebius_div_sq] at hT
  refine hT.congr (fun n => ?_)
  have hfin : ∑' d : ℕ,
      ((ArithmeticFunction.moebius d : ℤ) : ℝ) * ((n / (d * d) : ℕ) : ℝ) / (n : ℝ) =
      ∑ d ∈ Finset.Icc 1 n,
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) * ((n / (d * d) : ℕ) : ℝ) / (n : ℝ) := by
    apply tsum_eq_sum
    intro d hd
    rw [Finset.mem_Icc] at hd
    rcases Nat.eq_zero_or_pos d with rfl | hdpos
    · simp
    · have hlt : n < d * d := by
        have h1 : n < d := by omega
        exact lt_of_lt_of_le h1 (Nat.le_mul_self d)
      rw [Nat.div_eq_of_lt hlt]
      simp
  rw [hfin, ← Finset.sum_div]
  congr 1
  have h1 := card_squarefree n
  have h2 := card_sign_add n
  have h3 : ((((Finset.Icc 1 n).filter (fun k => ArithmeticFunction.moebius k = 1)).card : ℝ) +
      (((Finset.Icc 1 n).filter (fun k => ArithmeticFunction.moebius k = -1)).card : ℝ)) =
      ((((Finset.Icc 1 n).filter (fun k => Squarefree k)).card : ℕ) : ℝ) := by
    exact_mod_cast h2
  rw [h3]
  have h4 : ((((Finset.Icc 1 n).filter (fun k => Squarefree k)).card : ℤ) : ℝ) =
      ((∑ d ∈ Finset.Icc 1 n, ArithmeticFunction.moebius d * ((n / (d * d) : ℕ) : ℤ) : ℤ) : ℝ) := by
    rw [h1]
  push_cast at h4
  exact h4.symm

end SqfreeDensity

theorem OMA.solution : OMA.R_oeis_a070548_R1.H1 := by
  unfold OMA.R_oeis_a070548_R1.H1 OMA.S_oeis_a070548.countSign
  exact SqfreeDensity.squarefree_density
