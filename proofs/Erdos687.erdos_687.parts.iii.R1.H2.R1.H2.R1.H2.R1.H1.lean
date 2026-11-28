import OMAReductions.R_Erdos687_erdos_687_parts_iii_R1_H2_R1_H2_R1_H2_R1

-- Step Erdos687.erdos_687.parts.iii.R1.H2.R1.H2.R1.H2.R1.H1: hypothesis H1 of reduction Erdos687.erdos_687.parts.iii.R1.H2.R1.H2.R1.H2.R1
-- Credit: @DevinWatson
-- Unconditional L^2 minor-arc Parseval bound over a full primorial period Q = prod_{p <= x} p:
--   sum_{M < Q} S_min(M)^2 <= (exp 5 / log 2) * Q * L * log x
-- Proof in 4 elementary steps:
--   1. Spectral orthogonality on Z/QZ via Re(Z(M))^2 <= Re(Z(M) * conj(Z(M))) and
--      spectral_orthogonality_on_primorial from the parent reduction.
--   2. Exact discrete Parseval bound on Z/dZ: sum_{1 <= r < d} |S_L(r/d)|^2 = (L % d)*(d - L % d) <= d * L,
--      yielding sum_{(r,d)=1} F_L(r/d)^2 <= d * L for all d >= 2, L >= 1.
--   3. Multiplicativity on squarefree Q = prod_{p <= x} p:
--      sum_{d | Q} d / phi(d)^2 = prod_{p <= x} (1 + p / (p - 1)^2).
--   4. Mertens first/second upper bound via Legendre factorization of n! and Chebyshev.theta_le_log4_mul_x,
--      giving sum_{p <= x} 1/p <= 3 - log(log 2) + log(log x) and
--      prod_{p <= x} (1 + p / (p - 1)^2) <= (exp 5 / log 2) * log x.

namespace Erdos687MinorL2

open Finset Real

private lemma succ_le_two_pow (k : ℕ) : k + 1 ≤ 2 ^ k := by
  induction k with
  | zero => decide
  | succ m ih =>
    rw [pow_succ]
    omega

private lemma one_le_D {L : ℕ} (hL : 1 ≤ L) : 1 ≤ L / (Nat.log 2 L + 1) := by
  have hlog : Nat.log 2 L + 1 ≤ L :=
    (succ_le_two_pow (Nat.log 2 L)).trans (Nat.pow_log_le_self 2 (by omega))
  exact Nat.div_pos hlog (Nat.succ_pos _)

private lemma moebius_sq_le_one (d : ℕ) : ((ArithmeticFunction.moebius d : ℝ) ^ 2) ≤ 1 := by
  by_cases hsq : Squarefree d
  · rw [ArithmeticFunction.moebius_apply_of_squarefree hsq]
    push_cast
    rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]
    norm_num

private lemma norm_fejer_sum_le (d L r : ℕ) :
    ‖∑ u ∈ range L,
      Complex.exp (((2 * Real.pi * (r : ℝ) * (u : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I)‖ ≤ (L : ℝ) := by
  calc
    ‖∑ u ∈ range L,
      Complex.exp (((2 * Real.pi * (r : ℝ) * (u : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I)‖
        ≤ ∑ u ∈ range L,
            ‖Complex.exp (((2 * Real.pi * (r : ℝ) * (u : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I)‖ :=
      norm_sum_le _ _
    _ = ∑ _u ∈ range L, (1 : ℝ) := by
      refine Finset.sum_congr rfl fun u _ => Complex.norm_exp_ofReal_mul_I _
    _ = (L : ℝ) := by simp

private lemma fejer_sum_parseval_le_mul {d L : ℕ} (hd : 1 ≤ d) :
    ∑ r ∈ (range d).filter (fun r => r ≠ 0),
      ‖∑ u ∈ range L,
        Complex.exp (((2 * Real.pi * (r : ℝ) * (u : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I)‖ ^ 2 ≤
      (d : ℝ) * (L : ℝ) := by
  have hfull_c :
      (∑ r ∈ range d,
        ((‖∑ u ∈ range L,
          Complex.exp (((2 * Real.pi * (r : ℝ) * (u : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I)‖ ^ 2 : ℝ) : ℂ)) =
      (d : ℂ) * ∑ u ∈ range L, ∑ v ∈ range L, (if (d : ℤ) ∣ ((u : ℤ) - (v : ℤ)) then (1 : ℂ) else 0) := by
    have hnorm : ∀ r ∈ range d,
        ((‖∑ u ∈ range L,
          Complex.exp (((2 * Real.pi * (r : ℝ) * (u : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I)‖ ^ 2 : ℝ) : ℂ) =
        ∑ u ∈ range L, ∑ v ∈ range L,
          Complex.exp (((2 * Real.pi * (r : ℝ) * (((u : ℤ) - (v : ℤ) : ℤ) : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I) := by
      intro r _
      rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, map_sum, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
      rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [Finset.sum_congr rfl hnorm]
    trans (∑ u ∈ range L, ∑ v ∈ range L, ∑ r ∈ range d,
      Complex.exp (((2 * Real.pi * (r : ℝ) * (((u : ℤ) - (v : ℤ) : ℤ) : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I))
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun u _ => Finset.sum_comm
    · simp_rw [OMA.R_Erdos687_erdos_687_parts_iii_R1_H2_R1_H2_R1.sum_exp_int_div hd]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      split_ifs <;> simp
  have hpair_count :
      (∑ u ∈ range L, ∑ v ∈ range L, (if (d : ℤ) ∣ ((u : ℤ) - (v : ℤ)) then (1 : ℝ) else 0)) =
      ((L % d : ℕ) : ℝ) * (((L / d + 1 : ℕ) : ℝ) ^ 2) +
        ((d - L % d : ℕ) : ℝ) * (((L / d : ℕ) : ℝ) ^ 2) := by
    have hdiv_iff : ∀ u v : ℕ, ((d : ℤ) ∣ ((u : ℤ) - (v : ℤ))) ↔ u % d = v % d := by
      intro u v
      rw [← Int.modEq_iff_dvd, Int.natCast_modEq_iff, Nat.ModEq, eq_comm]
    simp_rw [hdiv_iff]
    let cnt : ℕ → ℕ := fun m => ((range L).filter fun u => u % d = m).card
    have hsum_sq :
        (∑ u ∈ range L, ∑ v ∈ range L, (if u % d = v % d then (1 : ℝ) else 0)) =
        ∑ m ∈ range d, ((cnt m : ℝ) ^ 2) := by
      have h1 : ∀ u ∈ range L,
          (∑ v ∈ range L, (if u % d = v % d then (1 : ℝ) else 0)) = (cnt (u % d) : ℝ) := by
        intro u _
        dsimp [cnt]
        rw [Finset.sum_boole]
        congr 2
        ext v
        simp only [mem_filter]
        exact and_congr_right fun _ => eq_comm
      rw [Finset.sum_congr rfl h1]
      have hpart : range L = (range d).biUnion (fun m => (range L).filter fun u => u % d = m) := by
        ext u
        simp only [mem_biUnion, mem_range, mem_filter]
        constructor
        · intro hu; exact ⟨u % d, Nat.mod_lt u (by omega), hu, rfl⟩
        · rintro ⟨_, _, hu, _⟩; exact hu
      have hpw : (range d : Set ℕ).PairwiseDisjoint (fun m => (range L).filter fun u => u % d = m) := by
        intro m₁ _ m₂ _ hne
        rw [Function.onFun, Finset.disjoint_left]
        intro u hu₁ hu₂
        exact hne ((mem_filter.mp hu₁).2.symm.trans (mem_filter.mp hu₂).2)
      conv_lhs => rw [hpart]
      rw [Finset.sum_biUnion hpw]
      refine Finset.sum_congr rfl fun m _ => ?_
      have hconst : ∑ u ∈ (range L).filter (fun u => u % d = m), (cnt (u % d) : ℝ) =
          ∑ _u ∈ (range L).filter (fun u => u % d = m), (cnt m : ℝ) :=
        Finset.sum_congr rfl fun u hu => by rw [(mem_filter.mp hu).2]
      rw [hconst, Finset.sum_const, nsmul_eq_mul, sq]
    have hcnt_lt : ∀ m < L % d, cnt m = L / d + 1 := by
      intro m hm
      have hm_d : m < d := hm.trans (Nat.mod_lt L (by omega))
      dsimp [cnt]
      have himg : (range L).filter (fun u => u % d = m) =
          (range (L / d + 1)).image (fun j => j * d + m) := by
        ext u
        simp only [mem_filter, mem_range, mem_image]
        constructor
        · rintro ⟨huL, hum⟩
          refine ⟨u / d, ?_, by rw [Nat.mul_comm, ← hum]; exact Nat.div_add_mod u d⟩
          have hdm1 : d * (u / d) + m = u := by rw [← hum]; exact Nat.div_add_mod u d
          have hdm2 : d * (L / d) + L % d = L := Nat.div_add_mod L d
          have hml := Nat.mod_lt L (by omega : 0 < d)
          by_contra hge
          push Not at hge
          have : d * (L / d + 1) ≤ d * (u / d) := Nat.mul_le_mul_left d hge
          rw [Nat.mul_add, Nat.mul_one] at this
          omega
        · rintro ⟨j, hj, rfl⟩
          have hdm2 : d * (L / d) + L % d = L := Nat.div_add_mod L d
          have hmul : j * d ≤ d * (L / d) := by
            rw [Nat.mul_comm]
            exact Nat.mul_le_mul_left d (by omega)
          refine ⟨by omega, ?_⟩
          rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hm_d]
      rw [himg, Finset.card_image_of_injective _ (fun j₁ j₂ h =>
        Nat.eq_of_mul_eq_mul_right (by omega) (Nat.add_right_cancel h)), Finset.card_range]
    have hcnt_ge : ∀ m, L % d ≤ m → m < d → cnt m = L / d := by
      intro m hm1 hm2
      dsimp [cnt]
      have himg : (range L).filter (fun u => u % d = m) =
          (range (L / d)).image (fun j => j * d + m) := by
        ext u
        simp only [mem_filter, mem_range, mem_image]
        constructor
        · rintro ⟨huL, hum⟩
          refine ⟨u / d, ?_, by rw [Nat.mul_comm, ← hum]; exact Nat.div_add_mod u d⟩
          have hdm1 : d * (u / d) + m = u := by rw [← hum]; exact Nat.div_add_mod u d
          have hdm2 : d * (L / d) + L % d = L := Nat.div_add_mod L d
          by_contra hge
          push Not at hge
          have : d * (L / d) ≤ d * (u / d) := Nat.mul_le_mul_left d hge
          omega
        · rintro ⟨j, hj, rfl⟩
          have hdm2 : d * (L / d) + L % d = L := Nat.div_add_mod L d
          have hmul : (j + 1) * d ≤ d * (L / d) := by
            rw [Nat.mul_comm]
            exact Nat.mul_le_mul_left d (by omega)
          rw [Nat.add_mul, Nat.one_mul] at hmul
          refine ⟨by omega, ?_⟩
          rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hm2]
      rw [himg, Finset.card_image_of_injective _ (fun j₁ j₂ h =>
        Nat.eq_of_mul_eq_mul_right (by omega) (Nat.add_right_cancel h)), Finset.card_range]
    rw [hsum_sq]
    have hsplit : range d = range (L % d) ∪ Ico (L % d) d := by
      ext m
      simp only [mem_range, mem_union, mem_Ico]
      have := Nat.mod_lt L (by omega : 0 < d)
      omega
    have hdisj : Disjoint (range (L % d)) (Ico (L % d) d) := by
      rw [Finset.disjoint_left]
      intro m h1 h2
      have := mem_range.mp h1
      have := (mem_Ico.mp h2).1
      omega
    rw [hsplit, Finset.sum_union hdisj]
    have hs1 : ∑ m ∈ range (L % d), ((cnt m : ℝ) ^ 2) =
        ((L % d : ℕ) : ℝ) * (((L / d + 1 : ℕ) : ℝ) ^ 2) := by
      have hc : ∑ m ∈ range (L % d), ((cnt m : ℝ) ^ 2) =
          ∑ _m ∈ range (L % d), (((L / d + 1 : ℕ) : ℝ) ^ 2) :=
        Finset.sum_congr rfl fun m hm => by rw [hcnt_lt m (mem_range.mp hm)]
      rw [hc, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hs2 : ∑ m ∈ Ico (L % d) d, ((cnt m : ℝ) ^ 2) =
        ((d - L % d : ℕ) : ℝ) * (((L / d : ℕ) : ℝ) ^ 2) := by
      have hc : ∑ m ∈ Ico (L % d) d, ((cnt m : ℝ) ^ 2) =
          ∑ _m ∈ Ico (L % d) d, (((L / d : ℕ) : ℝ) ^ 2) :=
        Finset.sum_congr rfl fun m hm => by
          have hm' := mem_Ico.mp hm
          rw [hcnt_ge m hm'.1 hm'.2]
      rw [hc, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
    rw [hs1, hs2]
  have hfull_r :
      (∑ r ∈ range d,
        ‖∑ u ∈ range L,
          Complex.exp (((2 * Real.pi * (r : ℝ) * (u : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I)‖ ^ 2) =
      (d : ℝ) * (((L % d : ℕ) : ℝ) * (((L / d + 1 : ℕ) : ℝ) ^ 2) +
        ((d - L % d : ℕ) : ℝ) * (((L / d : ℕ) : ℝ) ^ 2)) := by
    have hre := congrArg Complex.re hfull_c
    rw [Complex.re_sum, ← Complex.ofReal_natCast, Complex.re_ofReal_mul] at hre
    simp only [Complex.ofReal_re, Complex.re_sum, apply_ite Complex.re,
      Complex.one_re, Complex.zero_re] at hre
    rw [hre, hpair_count]
  have hfilt_eq : (range d).filter (fun r => r ≠ 0) = (range d).erase 0 := by
    ext r
    simp only [mem_filter, mem_erase, mem_range]
    tauto
  have h0_term :
      ‖∑ u ∈ range L,
        Complex.exp (((2 * Real.pi * ((0 : ℕ) : ℝ) * (u : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I)‖ ^ 2 =
      (L : ℝ) ^ 2 := by
    simp only [Nat.cast_zero, mul_zero, zero_mul, zero_div, Complex.ofReal_zero, Complex.exp_zero,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, Complex.norm_natCast]
  have hsplit0 := Finset.add_sum_erase (range d)
    (fun r => ‖∑ u ∈ range L,
      Complex.exp (((2 * Real.pi * (r : ℝ) * (u : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I)‖ ^ 2)
    (show 0 ∈ range d from mem_range.mpr (by omega))
  rw [h0_term, hfull_r] at hsplit0
  have hrem_eq :
      ∑ r ∈ (range d).filter (fun r => r ≠ 0),
        ‖∑ u ∈ range L,
          Complex.exp (((2 * Real.pi * (r : ℝ) * (u : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I)‖ ^ 2 =
      ((L % d : ℕ) : ℝ) * ((d : ℝ) - ((L % d : ℕ) : ℝ)) := by
    rw [hfilt_eq]
    have hdm_r : (L : ℝ) = (d : ℝ) * ((L / d : ℕ) : ℝ) + ((L % d : ℕ) : ℝ) := by
      exact_mod_cast (Nat.div_add_mod L d).symm
    have hsub_r : ((d - L % d : ℕ) : ℝ) = (d : ℝ) - ((L % d : ℕ) : ℝ) := by
      rw [Nat.cast_sub (Nat.mod_lt L (by omega)).le]
    rw [hsub_r, Nat.cast_add, Nat.cast_one] at hsplit0
    nlinarith
  rw [hrem_eq]
  have hs_le_L : ((L % d : ℕ) : ℝ) ≤ (L : ℝ) := by exact_mod_cast Nat.mod_le L d
  have hs_nn : (0 : ℝ) ≤ ((L % d : ℕ) : ℝ) := by positivity
  have hsub_nn : (0 : ℝ) ≤ (d : ℝ) - ((L % d : ℕ) : ℝ) := by
    have : ((L % d : ℕ) : ℝ) ≤ (d : ℝ) := by exact_mod_cast (Nat.mod_lt L (by omega)).le
    linarith
  nlinarith

private lemma fejer_sq_sum_le {d L : ℕ} (hd : 2 ≤ d) (hL : 1 ≤ L) :
    ∑ r ∈ (range d).filter (fun r => Nat.Coprime r d),
      (‖∑ u ∈ range L,
        Complex.exp (((2 * Real.pi * (r : ℝ) * (u : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I)‖ ^ 2 /
        (L : ℝ)) ^ 2 ≤
      (d : ℝ) * (L : ℝ) := by
  have hL_pos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (show 0 < L by omega)
  have hsub : (range d).filter (fun r => Nat.Coprime r d) ⊆ (range d).filter (fun r => r ≠ 0) := by
    intro r hr
    obtain ⟨hrd, hcop⟩ := mem_filter.mp hr
    refine mem_filter.mpr ⟨hrd, ?_⟩
    rintro rfl
    rw [Nat.coprime_zero_left] at hcop
    omega
  have hterm : ∀ r ∈ (range d).filter (fun r => Nat.Coprime r d),
      (‖∑ u ∈ range L,
        Complex.exp (((2 * Real.pi * (r : ℝ) * (u : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I)‖ ^ 2 /
        (L : ℝ)) ^ 2 ≤
      ‖∑ u ∈ range L,
        Complex.exp (((2 * Real.pi * (r : ℝ) * (u : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I)‖ ^ 2 := by
    intro r _
    set S := ‖∑ u ∈ range L,
      Complex.exp (((2 * Real.pi * (r : ℝ) * (u : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I)‖
    have hS_nn : 0 ≤ S := norm_nonneg _
    have hS_le : S ≤ (L : ℝ) := norm_fejer_sum_le d L r
    have hS2_le : S ^ 2 ≤ (L : ℝ) ^ 2 := by nlinarith
    rw [div_pow, div_le_iff₀ (sq_pos_of_pos hL_pos)]
    have hS2_nn : 0 ≤ S ^ 2 := sq_nonneg S
    calc
      (S ^ 2) ^ 2 = S ^ 2 * S ^ 2 := sq _
      _ ≤ S ^ 2 * (L : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hS2_le hS2_nn
  calc
    ∑ r ∈ (range d).filter (fun r => Nat.Coprime r d),
      (‖∑ u ∈ range L,
        Complex.exp (((2 * Real.pi * (r : ℝ) * (u : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I)‖ ^ 2 /
        (L : ℝ)) ^ 2
        ≤ ∑ r ∈ (range d).filter (fun r => Nat.Coprime r d),
            ‖∑ u ∈ range L,
              Complex.exp (((2 * Real.pi * (r : ℝ) * (u : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I)‖ ^ 2 :=
      Finset.sum_le_sum hterm
    _ ≤ ∑ r ∈ (range d).filter (fun r => r ≠ 0),
          ‖∑ u ∈ range L,
            Complex.exp (((2 * Real.pi * (r : ℝ) * (u : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I)‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)
    _ ≤ (d : ℝ) * (L : ℝ) := fejer_sum_parseval_le_mul (by omega)

private lemma parseval_minor_arc_sum_sq (Q D L : ℕ) (hQ : 1 ≤ Q) (hL : 1 ≤ L) (hD : 1 ≤ D) :
    (∑ M ∈ range Q,
      (∑ d ∈ Q.divisors.filter (fun d => D < d),
        ((ArithmeticFunction.moebius d : ℝ) / (Nat.totient d : ℝ)) *
          ∑ r ∈ (range d).filter (fun r => Nat.Coprime r d),
            Real.cos (2 * Real.pi * (r : ℝ) * ((M + L : ℕ) : ℝ) / (d : ℝ)) *
              (‖∑ u ∈ range L,
                Complex.exp (((2 * Real.pi * (r : ℝ) * (u : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I)‖ ^ 2 /
                (L : ℝ))) ^ 2) ≤
      (Q : ℝ) * (L : ℝ) * ∑ d ∈ Q.divisors, (d : ℝ) / ((Nat.totient d : ℝ) ^ 2) := by
  let Dset := Q.divisors.filter (fun d => D < d)
  let Rset : ℕ → Finset ℕ := fun d => (range d).filter (fun r => Nat.Coprime r d)
  let F : ℕ → ℕ → ℝ := fun d r =>
    ‖∑ u ∈ range L,
      Complex.exp (((2 * Real.pi * (r : ℝ) * (u : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I)‖ ^ 2 / (L : ℝ)
  let coeff : ℕ → ℕ → ℝ := fun d r =>
    ((ArithmeticFunction.moebius d : ℝ) / (Nat.totient d : ℝ)) * F d r
  let Z : ℕ → ℂ := fun M =>
    ∑ d ∈ Dset, ∑ r ∈ Rset d,
      ((coeff d r : ℝ) : ℂ) *
        Complex.exp (((2 * Real.pi * (r : ℝ) * ((M + L : ℕ) : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I)
  have hre_eq : ∀ M : ℕ,
      (∑ d ∈ Dset,
        ((ArithmeticFunction.moebius d : ℝ) / (Nat.totient d : ℝ)) *
          ∑ r ∈ Rset d,
            Real.cos (2 * Real.pi * (r : ℝ) * ((M + L : ℕ) : ℝ) / (d : ℝ)) * F d r) =
      (Z M).re := by
    intro M
    dsimp [Z, coeff]
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Complex.re_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
    ring
  have hle_normSq : ∀ M : ℕ, ((Z M).re) ^ 2 ≤ (Z M * starRingEnd ℂ (Z M)).re := by
    intro M
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_apply]
    nlinarith [sq_nonneg (Z M).im]
  have hstep1 :
      (∑ M ∈ range Q,
        (∑ d ∈ Dset,
          ((ArithmeticFunction.moebius d : ℝ) / (Nat.totient d : ℝ)) *
            ∑ r ∈ Rset d,
              Real.cos (2 * Real.pi * (r : ℝ) * ((M + L : ℕ) : ℝ) / (d : ℝ)) * F d r) ^ 2) ≤
      (∑ M ∈ range Q, Z M * starRingEnd ℂ (Z M)).re := by
    rw [Complex.re_sum]
    refine Finset.sum_le_sum fun M _ => ?_
    rw [hre_eq M]
    exact hle_normSq M
  have horth :
      (∑ M ∈ range Q, Z M * starRingEnd ℂ (Z M)) =
      (Q : ℂ) * ∑ d ∈ Dset, ∑ r ∈ Rset d, (((coeff d r : ℝ) ^ 2 : ℝ) : ℂ) := by
    have hexp : ∀ M : ℕ, Z M * starRingEnd ℂ (Z M) =
        ∑ d₁ ∈ Dset, ∑ r₁ ∈ Rset d₁, ∑ d₂ ∈ Dset, ∑ r₂ ∈ Rset d₂,
          (((coeff d₁ r₁ : ℝ) : ℂ) * ((coeff d₂ r₂ : ℝ) : ℂ)) *
            (Complex.exp (((2 * Real.pi * (r₁ : ℝ) * ((M + L : ℕ) : ℝ) / (d₁ : ℝ) : ℝ) : ℂ) * Complex.I) *
              starRingEnd ℂ (Complex.exp (((2 * Real.pi * (r₂ : ℝ) * ((M + L : ℕ) : ℝ) / (d₂ : ℝ) : ℝ) : ℂ) * Complex.I))) := by
      intro M
      dsimp [Z]
      rw [map_sum, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun d₁ _ => ?_
      simp_rw [map_sum, Finset.sum_mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun r₁ _ => ?_
      refine Finset.sum_congr rfl fun d₂ _ => ?_
      refine Finset.sum_congr rfl fun r₂ _ => ?_
      rw [map_mul, Complex.conj_ofReal]
      ring
    simp_rw [hexp]
    rw [Finset.sum_comm]
    trans (∑ d₁ ∈ Dset, ∑ r₁ ∈ Rset d₁, ∑ d₂ ∈ Dset, ∑ r₂ ∈ Rset d₂,
      (((coeff d₁ r₁ : ℝ) : ℂ) * ((coeff d₂ r₂ : ℝ) : ℂ)) *
        ∑ M ∈ range Q,
          Complex.exp (((2 * Real.pi * (r₁ : ℝ) * ((M + L : ℕ) : ℝ) / (d₁ : ℝ) : ℝ) : ℂ) * Complex.I) *
            starRingEnd ℂ (Complex.exp (((2 * Real.pi * (r₂ : ℝ) * ((M + L : ℕ) : ℝ) / (d₂ : ℝ) : ℝ) : ℂ) * Complex.I)))
    · refine Finset.sum_congr rfl fun d₁ _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun r₁ _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun d₂ _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun r₂ _ => ?_
      rw [← Finset.mul_sum]
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun d₁ hd₁ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun r₁ hr₁ => ?_
      have hd₁_div : d₁ ∈ Q.divisors := (mem_filter.mp hd₁).1
      have hr₁_lt : r₁ < d₁ := mem_range.mp (mem_filter.mp hr₁).1
      have hr₁_cop : Nat.Coprime r₁ d₁ := (mem_filter.mp hr₁).2
      have hinner : ∀ d₂ ∈ Dset, ∀ r₂ ∈ Rset d₂,
          (((coeff d₁ r₁ : ℝ) : ℂ) * ((coeff d₂ r₂ : ℝ) : ℂ)) *
            (∑ M ∈ range Q,
              Complex.exp (((2 * Real.pi * (r₁ : ℝ) * ((M + L : ℕ) : ℝ) / (d₁ : ℝ) : ℝ) : ℂ) * Complex.I) *
                starRingEnd ℂ (Complex.exp (((2 * Real.pi * (r₂ : ℝ) * ((M + L : ℕ) : ℝ) / (d₂ : ℝ) : ℝ) : ℂ) * Complex.I))) =
          if d₁ = d₂ ∧ r₁ = r₂ then (Q : ℂ) * (((coeff d₁ r₁ : ℝ) ^ 2 : ℝ) : ℂ) else 0 := by
        intro d₂ hd₂ r₂ hr₂
        have hd₂_div : d₂ ∈ Q.divisors := (mem_filter.mp hd₂).1
        have hr₂_lt : r₂ < d₂ := mem_range.mp (mem_filter.mp hr₂).1
        have hr₂_cop : Nat.Coprime r₂ d₂ := (mem_filter.mp hr₂).2
        rw [OMA.R_Erdos687_erdos_687_parts_iii_R1_H2_R1_H2_R1_H2_R1.spectral_orthogonality_on_primorial
          hQ L hd₁_div hd₂_div hr₁_lt hr₁_cop hr₂_lt hr₂_cop]
        split_ifs with h
        · rcases h with ⟨rfl, rfl⟩
          push_cast
          ring
        · ring
      have hsum2 :
          (∑ d₂ ∈ Dset, ∑ r₂ ∈ Rset d₂,
            (((coeff d₁ r₁ : ℝ) : ℂ) * ((coeff d₂ r₂ : ℝ) : ℂ)) *
              (∑ M ∈ range Q,
                Complex.exp (((2 * Real.pi * (r₁ : ℝ) * ((M + L : ℕ) : ℝ) / (d₁ : ℝ) : ℝ) : ℂ) * Complex.I) *
                  starRingEnd ℂ (Complex.exp (((2 * Real.pi * (r₂ : ℝ) * ((M + L : ℕ) : ℝ) / (d₂ : ℝ) : ℝ) : ℂ) * Complex.I)))) =
          (Q : ℂ) * (((coeff d₁ r₁ : ℝ) ^ 2 : ℝ) : ℂ) := by
        have h1 : ∀ d₂ ∈ Dset,
            (∑ r₂ ∈ Rset d₂,
              (((coeff d₁ r₁ : ℝ) : ℂ) * ((coeff d₂ r₂ : ℝ) : ℂ)) *
                (∑ M ∈ range Q,
                  Complex.exp (((2 * Real.pi * (r₁ : ℝ) * ((M + L : ℕ) : ℝ) / (d₁ : ℝ) : ℝ) : ℂ) * Complex.I) *
                    starRingEnd ℂ (Complex.exp (((2 * Real.pi * (r₂ : ℝ) * ((M + L : ℕ) : ℝ) / (d₂ : ℝ) : ℝ) : ℂ) * Complex.I)))) =
            if d₁ = d₂ then (Q : ℂ) * (((coeff d₁ r₁ : ℝ) ^ 2 : ℝ) : ℂ) else 0 := by
          intro d₂ hd₂
          rw [Finset.sum_congr rfl fun r₂ hr₂ => hinner d₂ hd₂ r₂ hr₂]
          by_cases hdeq : d₁ = d₂
          · subst hdeq
            simp only [true_and, ↓reduceIte]
            simp [hr₁]
          · simp [hdeq]
        rw [Finset.sum_congr rfl h1]
        simp [hd₁]
      exact hsum2
  have hdiag :
      (∑ M ∈ range Q, Z M * starRingEnd ℂ (Z M)).re =
      (Q : ℝ) * ∑ d ∈ Dset, ∑ r ∈ Rset d, (coeff d r) ^ 2 := by
    rw [horth, ← Complex.ofReal_natCast, Complex.re_ofReal_mul]
    simp only [Complex.re_sum, Complex.ofReal_re]
  have hDset_bound :
      (∑ d ∈ Dset, ∑ r ∈ Rset d, (coeff d r) ^ 2) ≤
      (L : ℝ) * ∑ d ∈ Q.divisors, (d : ℝ) / ((Nat.totient d : ℝ) ^ 2) := by
    have hterm : ∀ d ∈ Dset,
        (∑ r ∈ Rset d, (coeff d r) ^ 2) ≤ (L : ℝ) * ((d : ℝ) / ((Nat.totient d : ℝ) ^ 2)) := by
      intro d hd
      have hd_gt : D < d := (mem_filter.mp hd).2
      have hd2 : 2 ≤ d := by omega
      have hsum_coeff :
          (∑ r ∈ Rset d, (coeff d r) ^ 2) =
          (((ArithmeticFunction.moebius d : ℝ) ^ 2) / ((Nat.totient d : ℝ) ^ 2)) *
            ∑ r ∈ Rset d, (F d r) ^ 2 := by
        dsimp [coeff]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun r _ => ?_
        ring
      rw [hsum_coeff]
      have hF_le : ∑ r ∈ Rset d, (F d r) ^ 2 ≤ (d : ℝ) * (L : ℝ) := fejer_sq_sum_le hd2 hL
      have hF_nn : 0 ≤ ∑ r ∈ Rset d, (F d r) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
      have hphi_nn : 0 ≤ ((Nat.totient d : ℝ) ^ 2)⁻¹ := by positivity
      have hmu : ((ArithmeticFunction.moebius d : ℝ) ^ 2) / ((Nat.totient d : ℝ) ^ 2) ≤
          1 / ((Nat.totient d : ℝ) ^ 2) := by
        exact div_le_div_of_nonneg_right (moebius_sq_le_one d) (sq_nonneg _)
      calc
        (((ArithmeticFunction.moebius d : ℝ) ^ 2) / ((Nat.totient d : ℝ) ^ 2)) *
            ∑ r ∈ Rset d, (F d r) ^ 2
            ≤ (1 / ((Nat.totient d : ℝ) ^ 2)) * ((d : ℝ) * (L : ℝ)) :=
          mul_le_mul hmu hF_le hF_nn (by positivity)
        _ = (L : ℝ) * ((d : ℝ) / ((Nat.totient d : ℝ) ^ 2)) := by ring
    calc
      ∑ d ∈ Dset, ∑ r ∈ Rset d, (coeff d r) ^ 2
          ≤ ∑ d ∈ Dset, (L : ℝ) * ((d : ℝ) / ((Nat.totient d : ℝ) ^ 2)) :=
        Finset.sum_le_sum hterm
      _ = (L : ℝ) * ∑ d ∈ Dset, (d : ℝ) / ((Nat.totient d : ℝ) ^ 2) := (Finset.mul_sum _ _ _).symm
      _ ≤ (L : ℝ) * ∑ d ∈ Q.divisors, (d : ℝ) / ((Nat.totient d : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun _ _ _ => by positivity))
          (by positivity)
  calc
    (∑ M ∈ range Q,
      (∑ d ∈ Dset,
        ((ArithmeticFunction.moebius d : ℝ) / (Nat.totient d : ℝ)) *
          ∑ r ∈ Rset d,
            Real.cos (2 * Real.pi * (r : ℝ) * ((M + L : ℕ) : ℝ) / (d : ℝ)) * F d r) ^ 2)
        ≤ (∑ M ∈ range Q, Z M * starRingEnd ℂ (Z M)).re := hstep1
    _ = (Q : ℝ) * ∑ d ∈ Dset, ∑ r ∈ Rset d, (coeff d r) ^ 2 := hdiag
    _ ≤ (Q : ℝ) * ((L : ℝ) * ∑ d ∈ Q.divisors, (d : ℝ) / ((Nat.totient d : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_left hDset_bound (by positivity)
    _ = (Q : ℝ) * (L : ℝ) * ∑ d ∈ Q.divisors, (d : ℝ) / ((Nat.totient d : ℝ) ^ 2) := by ring

private lemma sum_div_totient_sq_eq_prod (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    ∑ d ∈ (∏ p ∈ P, p).divisors, (d : ℝ) / ((Nat.totient d : ℝ) ^ 2) =
      ∏ p ∈ P, (1 + (p : ℝ) / (((p : ℝ) - 1) ^ 2)) := by
  classical
  induction P using Finset.induction_on with
  | empty => simp
  | @insert p s hp ih =>
    have hpp : p.Prime := hP p (mem_insert_self p s)
    have hs : ∀ q ∈ s, q.Prime := fun q hq => hP q (mem_insert_of_mem hq)
    set Q := ∏ q ∈ s, q
    have hQ_pos : 0 < Q := Finset.prod_pos fun q hq => (hs q hq).pos
    have hcop : Nat.Coprime p Q := by
      refine Nat.coprime_prod_right_iff.mpr fun q hq => ?_
      have hne : p ≠ q := fun h => hp (h ▸ hq)
      exact (Nat.coprime_primes hpp (hs q hq)).mpr hne
    have hdiv_union : (p * Q).divisors = Q.divisors ∪ Q.divisors.image (fun d => p * d) := by
      ext m
      simp only [Nat.mem_divisors, mem_union, mem_image]
      constructor
      · rintro ⟨hm, hne⟩
        by_cases hpm : p ∣ m
        · obtain ⟨d, rfl⟩ := hpm
          right
          refine ⟨d, ⟨(Nat.mul_dvd_mul_iff_left hpp.pos).mp hm, hQ_pos.ne'⟩, rfl⟩
        · left
          have hcop_pm : Nat.Coprime m p := (hpp.coprime_iff_not_dvd.mpr hpm).symm
          exact ⟨hcop_pm.dvd_of_dvd_mul_left hm, hQ_pos.ne'⟩
      · rintro (⟨hm, _⟩ | ⟨d, ⟨hd, _⟩, rfl⟩)
        · exact ⟨hm.trans (dvd_mul_left Q p), mul_ne_zero hpp.ne_zero hQ_pos.ne'⟩
        · exact ⟨Nat.mul_dvd_mul_left p hd, mul_ne_zero hpp.ne_zero hQ_pos.ne'⟩
    have hdisj : Disjoint Q.divisors (Q.divisors.image (fun d => p * d)) := by
      rw [Finset.disjoint_left]
      intro m hm1 hm2
      obtain ⟨d, _, rfl⟩ := mem_image.mp hm2
      have hpQ : p ∣ Q := (dvd_mul_right p d).trans (Nat.mem_divisors.mp hm1).1
      exact hpp.not_dvd_one (hcop.gcd_eq_one ▸ Nat.dvd_gcd dvd_rfl hpQ)
    rw [Finset.prod_insert hp, Finset.prod_insert hp, hdiv_union, Finset.sum_union hdisj,
      Finset.sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hpp.pos h)]
    have himg_eq :
        ∑ d ∈ Q.divisors, ((p * d : ℕ) : ℝ) / ((Nat.totient (p * d) : ℝ) ^ 2) =
        ((p : ℝ) / (((p : ℝ) - 1) ^ 2)) * ∑ d ∈ Q.divisors, (d : ℝ) / ((Nat.totient d : ℝ) ^ 2) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun d hd => ?_
      have hdQ : d ∣ Q := (Nat.mem_divisors.mp hd).1
      have hcop_pd : Nat.Coprime p d := hcop.coprime_dvd_right hdQ
      rw [Nat.totient_mul hcop_pd, Nat.totient_prime hpp]
      have hp1 : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
        rw [Nat.cast_sub hpp.one_le, Nat.cast_one]
      push_cast
      rw [hp1, mul_pow, ← div_mul_div_comm]
    rw [himg_eq, ← ih hs]
    ring

private lemma factorial_le_pow_self (n : ℕ) : n.factorial ≤ n ^ n := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Nat.factorial_succ, pow_succ']
    exact Nat.mul_le_mul_left (m + 1) (ih.trans (Nat.pow_le_pow_left (Nat.le_succ m) m))

private lemma prod_prime_pow_dvd {P : Finset ℕ} {f : ℕ → ℕ} {m : ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hdvd : ∀ p ∈ P, p ^ f p ∣ m) :
    (∏ p ∈ P, p ^ f p) ∣ m := by
  classical
  induction P using Finset.induction_on with
  | empty => simp
  | @insert p s hp ih =>
    rw [Finset.prod_insert hp]
    have hpp : p.Prime := hP p (mem_insert_self p s)
    have hs : ∀ q ∈ s, q.Prime := fun q hq => hP q (mem_insert_of_mem hq)
    have hcop : Nat.Coprime (p ^ f p) (∏ q ∈ s, q ^ f q) := by
      refine Nat.coprime_prod_right_iff.mpr fun q hq => ?_
      have hne : p ≠ q := fun h => hp (h ▸ hq)
      exact ((Nat.coprime_primes hpp (hs q hq)).mpr hne).pow _ _
    exact hcop.mul_dvd_of_dvd_of_dvd (hdvd p (mem_insert_self p s))
      (ih hs fun q hq => hdvd q (mem_insert_of_mem hq))

private lemma mertens_first_upper (n : ℕ) (hn : 1 ≤ n) :
    ∑ p ∈ (range (n + 1)).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ) ≤
      Real.log (n : ℝ) + Real.log 4 := by
  let P := (range (n + 1)).filter Nat.Prime
  have hfac_dvd : (∏ p ∈ P, p ^ (n / p)) ∣ n.factorial := by
    refine prod_prime_pow_dvd (fun p hp => (mem_filter.mp hp).2) ?_
    intro p hp
    have hpp : p.Prime := (mem_filter.mp hp).2
    have hpn : p ≤ n := Nat.lt_succ_iff.mp (mem_range.mp (mem_filter.mp hp).1)
    rw [hpp.pow_dvd_iff_le_factorization (Nat.factorial_ne_zero n),
      Nat.factorization_def _ hpp]
    haveI : Fact p.Prime := ⟨hpp⟩
    rw [padicValNat_factorial (Nat.lt_succ_self (Nat.log p n))]
    have h1 : 1 ∈ Ico 1 (Nat.log p n + 1) :=
      mem_Ico.mpr ⟨le_rfl, Nat.succ_le_succ (Nat.log_pos hpp.one_lt hpn)⟩
    calc
      n / p = n / p ^ 1 := by simp
      _ ≤ ∑ i ∈ Ico 1 (Nat.log p n + 1), n / p ^ i :=
        Finset.single_le_sum (f := fun i => n / p ^ i) (fun _ _ => Nat.zero_le _) h1
  have hprod_le : (∏ p ∈ P, p ^ (n / p)) ≤ n ^ n :=
    (Nat.le_of_dvd (Nat.factorial_pos n) hfac_dvd).trans (factorial_le_pow_self n)
  have hprod_pos : (0 : ℝ) < ((∏ p ∈ P, p ^ (n / p) : ℕ) : ℝ) := by
    exact_mod_cast Finset.prod_pos fun p hp => pow_pos (Nat.Prime.pos (mem_filter.mp hp).2) _
  have hlog_le : Real.log ((∏ p ∈ P, p ^ (n / p) : ℕ) : ℝ) ≤ Real.log ((n ^ n : ℕ) : ℝ) :=
    Real.log_le_log hprod_pos (by exact_mod_cast hprod_le)
  have hlog_lhs :
      Real.log ((∏ p ∈ P, p ^ (n / p) : ℕ) : ℝ) =
      ∑ p ∈ P, ((n / p : ℕ) : ℝ) * Real.log (p : ℝ) := by
    rw [Nat.cast_prod, Real.log_prod (fun p hp => by
      exact_mod_cast (pow_pos (Nat.Prime.pos (mem_filter.mp hp).2) _).ne')]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Nat.cast_pow, Real.log_pow]
  have hlog_rhs : Real.log ((n ^ n : ℕ) : ℝ) = (n : ℝ) * Real.log (n : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow]
  rw [hlog_lhs, hlog_rhs] at hlog_le
  have hfloor : ∀ p ∈ P,
      ((n : ℝ) / (p : ℝ) - 1) * Real.log (p : ℝ) ≤ ((n / p : ℕ) : ℝ) * Real.log (p : ℝ) := by
    intro p hp
    have hpp : p.Prime := (mem_filter.mp hp).2
    have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
    have hlogp_nn : 0 ≤ Real.log (p : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hpp.one_le)
    have hlt : n < p * (n / p + 1) := Nat.lt_mul_div_succ n hpp.pos
    have hlt_r : (n : ℝ) < (p : ℝ) * (((n / p : ℕ) : ℝ) + 1) := by exact_mod_cast hlt
    have hdiv_le : (n : ℝ) / (p : ℝ) - 1 ≤ ((n / p : ℕ) : ℝ) := by
      rw [sub_le_iff_le_add, div_le_iff₀ hp_pos]
      linarith
    exact mul_le_mul_of_nonneg_right hdiv_le hlogp_nn
  have hsum_floor :
      (n : ℝ) * (∑ p ∈ P, Real.log (p : ℝ) / (p : ℝ)) - ∑ p ∈ P, Real.log (p : ℝ) ≤
      (n : ℝ) * Real.log (n : ℝ) := by
    have h1 : (n : ℝ) * (∑ p ∈ P, Real.log (p : ℝ) / (p : ℝ)) - ∑ p ∈ P, Real.log (p : ℝ) =
        ∑ p ∈ P, ((n : ℝ) / (p : ℝ) - 1) * Real.log (p : ℝ) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun p _ => by ring
    rw [h1]
    exact (Finset.sum_le_sum hfloor).trans hlog_le
  have htheta_eq : ∑ p ∈ P, Real.log (p : ℝ) = Chebyshev.theta (n : ℝ) := by
    have hP_eq : P = (Ioc 0 n).filter Nat.Prime := by
      ext p
      simp only [P, mem_filter, mem_range, mem_Ioc]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨⟨h2.pos, by omega⟩, h2⟩
      · rintro ⟨⟨_, h1⟩, h2⟩; exact ⟨by omega, h2⟩
    rw [hP_eq]
    simp [Chebyshev.theta]
  have htheta_le : ∑ p ∈ P, Real.log (p : ℝ) ≤ Real.log 4 * (n : ℝ) := by
    rw [htheta_eq]
    exact Chebyshev.theta_le_log4_mul_x (by positivity)
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hmul_le :
      (n : ℝ) * (∑ p ∈ P, Real.log (p : ℝ) / (p : ℝ)) ≤
      (n : ℝ) * (Real.log (n : ℝ) + Real.log 4) := by
    linarith
  exact le_of_mul_le_mul_left hmul_le hn_pos

private lemma mertens_second_upper {x : ℕ} (hx : 2 ≤ x) :
    ∑ p ∈ (range (x + 1)).filter Nat.Prime, (p : ℝ)⁻¹ ≤
      3 - Real.log (Real.log 2) + Real.log (Real.log (x : ℝ)) := by
  let S : ℕ → ℝ := fun k => ∑ p ∈ (range (k + 1)).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ)
  have hS_step : ∀ k : ℕ, 2 ≤ k →
      (S k - S (k - 1)) / Real.log (k : ℝ) = if k.Prime then (k : ℝ)⁻¹ else 0 := by
    intro k hk
    have hlogk_pos : 0 < Real.log (k : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < k by omega))
    have hdiff : S k - S (k - 1) = if k.Prime then Real.log (k : ℝ) / (k : ℝ) else 0 := by
      dsimp [S]
      have hr : range (k + 1) = insert k (range k) := Finset.range_add_one
      have hkm1 : k - 1 + 1 = k := by omega
      rw [hkm1, hr, Finset.filter_insert]
      split_ifs with hkp
      · rw [Finset.sum_insert (fun h => Nat.lt_irrefl k (mem_range.mp (mem_filter.mp h).1))]
        ring
      · ring
    rw [hdiff]
    split_ifs with hkp
    · field_simp [hlogk_pos.ne']
    · simp
  have hsum_eq :
      ∑ p ∈ (range (x + 1)).filter Nat.Prime, (p : ℝ)⁻¹ =
      ∑ k ∈ Icc 2 x, (S k - S (k - 1)) / Real.log (k : ℝ) := by
    rw [Finset.sum_congr rfl fun k hk => hS_step k (mem_Icc.mp hk).1, ← Finset.sum_filter]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext p
    simp only [mem_filter, mem_range, mem_Icc]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨⟨h2.two_le, by omega⟩, h2⟩
    · rintro ⟨⟨_, h1⟩, h2⟩; exact ⟨by omega, h2⟩
  have hab : ∀ m : ℕ, 2 ≤ m →
      ∑ k ∈ Icc 2 m, (S k - S (k - 1)) / Real.log (k : ℝ) =
      S m / Real.log (m : ℝ) +
        ∑ k ∈ Ico 2 m, S k * (1 / Real.log (k : ℝ) - 1 / Real.log ((k + 1 : ℕ) : ℝ)) := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base =>
      have hS1 : S 1 = 0 := by
        dsimp [S]
        have : (range 2).filter Nat.Prime = ∅ := by decide
        rw [this, Finset.sum_empty]
      rw [Icc_self, Finset.sum_singleton, Ico_self, Finset.sum_empty, add_zero]
      simp [hS1]
    | succ m hm ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ m + 1), ih,
        Finset.sum_Ico_succ_top hm]
      simp only [Nat.add_sub_cancel]
      ring
  rw [hsum_eq, hab x hx]
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogx_pos : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have htop : S x / Real.log (x : ℝ) ≤ 1 + Real.log 4 / Real.log (x : ℝ) := by
    have h1 := mertens_first_upper x (by omega)
    calc
      S x / Real.log (x : ℝ) ≤ (Real.log (x : ℝ) + Real.log 4) / Real.log (x : ℝ) :=
        div_le_div_of_nonneg_right h1 hlogx_pos.le
      _ = 1 + Real.log 4 / Real.log (x : ℝ) := by
        rw [add_div, div_self hlogx_pos.ne']
  have hterm : ∀ k ∈ Ico 2 x,
      S k * (1 / Real.log (k : ℝ) - 1 / Real.log ((k + 1 : ℕ) : ℝ)) ≤
      (Real.log (Real.log ((k + 1 : ℕ) : ℝ)) - Real.log (Real.log (k : ℝ))) +
        Real.log 4 * (1 / Real.log (k : ℝ) - 1 / Real.log ((k + 1 : ℕ) : ℝ)) := by
    intro k hk
    have hk2 : 2 ≤ k := (mem_Ico.mp hk).1
    have hlogk_pos : 0 < Real.log (k : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < k by omega))
    have hlogk1_pos : 0 < Real.log ((k + 1 : ℕ) : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < k + 1 by omega))
    have hlog_lt : Real.log (k : ℝ) ≤ Real.log ((k + 1 : ℕ) : ℝ) :=
      Real.log_le_log (by exact_mod_cast (show 0 < k by omega)) (by exact_mod_cast Nat.le_succ k)
    have hdiff_nn : 0 ≤ 1 / Real.log (k : ℝ) - 1 / Real.log ((k + 1 : ℕ) : ℝ) := by
      have : 1 / Real.log ((k + 1 : ℕ) : ℝ) ≤ 1 / Real.log (k : ℝ) :=
        one_div_le_one_div_of_le hlogk_pos hlog_lt
      linarith
    have hSk : S k ≤ Real.log (k : ℝ) + Real.log 4 := mertens_first_upper k (by omega)
    have hmain_term :
        Real.log (k : ℝ) * (1 / Real.log (k : ℝ) - 1 / Real.log ((k + 1 : ℕ) : ℝ)) ≤
        Real.log (Real.log ((k + 1 : ℕ) : ℝ)) - Real.log (Real.log (k : ℝ)) := by
      have h1 : Real.log (k : ℝ) * (1 / Real.log (k : ℝ) - 1 / Real.log ((k + 1 : ℕ) : ℝ)) =
          1 - (Real.log ((k + 1 : ℕ) : ℝ) / Real.log (k : ℝ))⁻¹ := by
        field_simp [hlogk_pos.ne', hlogk1_pos.ne']
      rw [h1, ← Real.log_div hlogk1_pos.ne' hlogk_pos.ne']
      exact Real.one_sub_inv_le_log_of_pos (div_pos hlogk1_pos hlogk_pos)
    calc
      S k * (1 / Real.log (k : ℝ) - 1 / Real.log ((k + 1 : ℕ) : ℝ))
          ≤ (Real.log (k : ℝ) + Real.log 4) *
              (1 / Real.log (k : ℝ) - 1 / Real.log ((k + 1 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_right hSk hdiff_nn
      _ = Real.log (k : ℝ) * (1 / Real.log (k : ℝ) - 1 / Real.log ((k + 1 : ℕ) : ℝ)) +
            Real.log 4 * (1 / Real.log (k : ℝ) - 1 / Real.log ((k + 1 : ℕ) : ℝ)) := by ring
      _ ≤ (Real.log (Real.log ((k + 1 : ℕ) : ℝ)) - Real.log (Real.log (k : ℝ))) +
            Real.log 4 * (1 / Real.log (k : ℝ) - 1 / Real.log ((k + 1 : ℕ) : ℝ)) := by linarith
  have htele1 : ∀ m : ℕ, 2 ≤ m →
      ∑ k ∈ Ico 2 m, (Real.log (Real.log ((k + 1 : ℕ) : ℝ)) - Real.log (Real.log (k : ℝ))) =
      Real.log (Real.log (m : ℝ)) - Real.log (Real.log 2) := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => simp
    | succ m hm ih =>
      rw [Finset.sum_Ico_succ_top hm, ih]
      ring
  have htele2 : ∀ m : ℕ, 2 ≤ m →
      ∑ k ∈ Ico 2 m, (1 / Real.log (k : ℝ) - 1 / Real.log ((k + 1 : ℕ) : ℝ)) =
      1 / Real.log 2 - 1 / Real.log (m : ℝ) := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => simp
    | succ m hm ih =>
      rw [Finset.sum_Ico_succ_top hm, ih]
      ring
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have hsum_le :
      ∑ k ∈ Ico 2 x, S k * (1 / Real.log (k : ℝ) - 1 / Real.log ((k + 1 : ℕ) : ℝ)) ≤
      (Real.log (Real.log (x : ℝ)) - Real.log (Real.log 2)) +
        Real.log 4 * (1 / Real.log 2 - 1 / Real.log (x : ℝ)) := by
    calc
      ∑ k ∈ Ico 2 x, S k * (1 / Real.log (k : ℝ) - 1 / Real.log ((k + 1 : ℕ) : ℝ))
          ≤ ∑ k ∈ Ico 2 x,
              ((Real.log (Real.log ((k + 1 : ℕ) : ℝ)) - Real.log (Real.log (k : ℝ))) +
                Real.log 4 * (1 / Real.log (k : ℝ) - 1 / Real.log ((k + 1 : ℕ) : ℝ))) :=
        Finset.sum_le_sum hterm
      _ = (∑ k ∈ Ico 2 x, (Real.log (Real.log ((k + 1 : ℕ) : ℝ)) - Real.log (Real.log (k : ℝ)))) +
            Real.log 4 * ∑ k ∈ Ico 2 x, (1 / Real.log (k : ℝ) - 1 / Real.log ((k + 1 : ℕ) : ℝ)) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      _ = (Real.log (Real.log (x : ℝ)) - Real.log (Real.log 2)) +
            Real.log 4 * (1 / Real.log 2 - 1 / Real.log (x : ℝ)) := by
        rw [htele1 x hx, htele2 x hx]
  have hcancel :
      Real.log 4 * (1 / Real.log 2 - 1 / Real.log (x : ℝ)) = 2 - Real.log 4 / Real.log (x : ℝ) := by
    rw [mul_sub, mul_one_div, mul_one_div, hlog4, mul_div_cancel_right₀ _ hlog2_pos.ne']
  linarith

private lemma sum_inv_mul_pred_le_one {x : ℕ} (hx : 2 ≤ x) :
    ∑ p ∈ (range (x + 1)).filter Nat.Prime, (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) ≤ 1 := by
  have hsub : (range (x + 1)).filter Nat.Prime ⊆ Icc 2 x := by
    intro p hp
    obtain ⟨h1, h2⟩ := mem_filter.mp hp
    exact mem_Icc.mpr ⟨h2.two_le, Nat.lt_succ_iff.mp (mem_range.mp h1)⟩
  have htele : ∀ m : ℕ, 2 ≤ m →
      ∑ k ∈ Icc 2 m, (1 : ℝ) / ((k : ℝ) * ((k : ℝ) - 1)) = 1 - 1 / (m : ℝ) := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base =>
      rw [Icc_self, Finset.sum_singleton]
      norm_num
    | succ m hm ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ m + 1), ih]
      have hm_ne : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
      have hm1_ne : ((m + 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show m + 1 ≠ 0 by omega)
      push_cast
      field_simp [hm_ne, hm1_ne]
      ring
  calc
    ∑ p ∈ (range (x + 1)).filter Nat.Prime, (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))
        ≤ ∑ k ∈ Icc 2 x, (1 : ℝ) / ((k : ℝ) * ((k : ℝ) - 1)) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun k hk _ => ?_
      have hk2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (mem_Icc.mp hk).1
      have : 0 ≤ (k : ℝ) * ((k : ℝ) - 1) := by nlinarith
      positivity
    _ = 1 - 1 / (x : ℝ) := htele x hx
    _ ≤ 1 := by
      have : 0 ≤ 1 / (x : ℝ) := by positivity
      linarith

private lemma euler_prod_bound {x : ℕ} (hx : 2 ≤ x) :
    ∏ p ∈ (range (x + 1)).filter Nat.Prime, (1 + (p : ℝ) / (((p : ℝ) - 1) ^ 2)) ≤
      (Real.exp 5 / Real.log 2) * Real.log (x : ℝ) := by
  let P := (range (x + 1)).filter Nat.Prime
  have hterm : ∀ p ∈ P,
      1 + (p : ℝ) / (((p : ℝ) - 1) ^ 2) ≤
      Real.exp ((p : ℝ)⁻¹ + 2 * (1 / ((p : ℝ) * ((p : ℝ) - 1)))) := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (mem_filter.mp hp).2.two_le
    have hp_pos : 0 < (p : ℝ) := by linarith
    have hp1_pos : 0 < (p : ℝ) - 1 := by linarith
    have hfac : 1 + (p : ℝ) / (((p : ℝ) - 1) ^ 2) =
        (1 + ((p : ℝ)⁻¹ + 1 / ((p : ℝ) * ((p : ℝ) - 1)))) *
          (1 + 1 / ((p : ℝ) * ((p : ℝ) - 1))) := by
      field_simp [hp_pos.ne', hp1_pos.ne']
      ring
    rw [hfac]
    have h1 : 1 + ((p : ℝ)⁻¹ + 1 / ((p : ℝ) * ((p : ℝ) - 1))) ≤
        Real.exp ((p : ℝ)⁻¹ + 1 / ((p : ℝ) * ((p : ℝ) - 1))) := by
      linarith [Real.add_one_le_exp ((p : ℝ)⁻¹ + 1 / ((p : ℝ) * ((p : ℝ) - 1)))]
    have h2 : 1 + 1 / ((p : ℝ) * ((p : ℝ) - 1)) ≤
        Real.exp (1 / ((p : ℝ) * ((p : ℝ) - 1))) := by
      linarith [Real.add_one_le_exp (1 / ((p : ℝ) * ((p : ℝ) - 1)))]
    have hnn1 : 0 ≤ 1 + ((p : ℝ)⁻¹ + 1 / ((p : ℝ) * ((p : ℝ) - 1))) := by positivity
    have hnn2 : 0 ≤ 1 + 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by positivity
    calc
      (1 + ((p : ℝ)⁻¹ + 1 / ((p : ℝ) * ((p : ℝ) - 1)))) * (1 + 1 / ((p : ℝ) * ((p : ℝ) - 1)))
          ≤ Real.exp ((p : ℝ)⁻¹ + 1 / ((p : ℝ) * ((p : ℝ) - 1))) *
              Real.exp (1 / ((p : ℝ) * ((p : ℝ) - 1))) :=
        mul_le_mul h1 h2 hnn2 (Real.exp_pos _).le
      _ = Real.exp ((p : ℝ)⁻¹ + 2 * (1 / ((p : ℝ) * ((p : ℝ) - 1)))) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hprod_le :
      ∏ p ∈ P, (1 + (p : ℝ) / (((p : ℝ) - 1) ^ 2)) ≤
      Real.exp (∑ p ∈ P, ((p : ℝ)⁻¹ + 2 * (1 / ((p : ℝ) * ((p : ℝ) - 1))))) := by
    rw [Real.exp_sum]
    refine Finset.prod_le_prod (fun p hp => ?_) hterm
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (mem_filter.mp hp).2.two_le
    positivity
  have hsum_le :
      ∑ p ∈ P, ((p : ℝ)⁻¹ + 2 * (1 / ((p : ℝ) * ((p : ℝ) - 1)))) ≤
      5 - Real.log (Real.log 2) + Real.log (Real.log (x : ℝ)) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    have h1 := mertens_second_upper hx
    have h2 := sum_inv_mul_pred_le_one hx
    linarith
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogx_pos : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  calc
    ∏ p ∈ P, (1 + (p : ℝ) / (((p : ℝ) - 1) ^ 2))
        ≤ Real.exp (∑ p ∈ P, ((p : ℝ)⁻¹ + 2 * (1 / ((p : ℝ) * ((p : ℝ) - 1))))) := hprod_le
    _ ≤ Real.exp (5 - Real.log (Real.log 2) + Real.log (Real.log (x : ℝ))) :=
      Real.exp_le_exp.mpr hsum_le
    _ = (Real.exp 5 / Real.log 2) * Real.log (x : ℝ) := by
      rw [Real.exp_add, Real.exp_sub, Real.exp_log hlog2_pos, Real.exp_log hlogx_pos]

end Erdos687MinorL2

theorem OMA.solution : OMA.R_Erdos687_erdos_687_parts_iii_R1_H2_R1_H2_R1_H2_R1.H1 := by
  refine ⟨Real.exp 5 / Real.log 2, div_pos (Real.exp_pos 5) (Real.log_pos (by norm_num)), ?_⟩
  intro x hx L hL
  dsimp only
  set D := L / (Nat.log 2 L + 1)
  set P := (Finset.range (x + 1)).filter Nat.Prime
  set Q := ∏ p ∈ P, p
  have hP : ∀ p ∈ P, p.Prime := fun p hp => (Finset.mem_filter.mp hp).2
  have hQ_pos : 1 ≤ Q := Finset.prod_pos fun p hp => (hP p hp).pos
  have hD_pos : 1 ≤ D := Erdos687MinorL2.one_le_D hL
  have h1 := Erdos687MinorL2.parseval_minor_arc_sum_sq Q D L hQ_pos hL hD_pos
  have h2 := Erdos687MinorL2.sum_div_totient_sq_eq_prod P hP
  have h3 := Erdos687MinorL2.euler_prod_bound hx
  calc
    (∑ M ∈ Finset.range Q,
      (∑ d ∈ Q.divisors.filter (fun d => D < d),
        ((ArithmeticFunction.moebius d : ℝ) / (Nat.totient d : ℝ)) *
          ∑ r ∈ (Finset.range d).filter (fun r => Nat.Coprime r d),
            Real.cos (2 * Real.pi * (r : ℝ) * ((M + L : ℕ) : ℝ) / (d : ℝ)) *
              (‖∑ u ∈ Finset.range L,
                Complex.exp (((2 * Real.pi * (r : ℝ) * (u : ℝ) / (d : ℝ) : ℝ) : ℂ) * Complex.I)‖ ^ 2 /
                (L : ℝ))) ^ 2)
        ≤ (Q : ℝ) * (L : ℝ) * ∑ d ∈ Q.divisors, (d : ℝ) / ((Nat.totient d : ℝ) ^ 2) := h1
    _ = (Q : ℝ) * (L : ℝ) * ∏ p ∈ P, (1 + (p : ℝ) / (((p : ℝ) - 1) ^ 2)) := by rw [h2]
    _ ≤ (Q : ℝ) * (L : ℝ) * ((Real.exp 5 / Real.log 2) * Real.log (x : ℝ)) :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = (Real.exp 5 / Real.log 2) * (Q : ℝ) * (L : ℝ) * Real.log (x : ℝ) := by ring
