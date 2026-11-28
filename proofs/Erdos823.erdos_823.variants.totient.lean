import FormalConjectures.ErdosProblems.«823»

/-! Equal totients with dense ratios via tail products of p/(p-1) and Dirichlet primes q ≡ 1 (mod φ(P)). -/

open Filter Finset Topology

theorem OMA.solution : type_of% @Erdos823.erdos_823.variants.totient := by
  classical
  intro α hα
  let A : Set ℝ := {x | ∃ n m : ℕ, 0 < n ∧ 0 < m ∧ n.totient = m.totient ∧ (n : ℝ) / m = x}
  have hc : α ∈ closure A := Metric.mem_closure_iff.2 fun ε hε => by
    have ⟨P, hP, hclose⟩ : ∃ P : ℕ, 0 < P ∧ |(P : ℝ) / P.totient - α| < ε / 2 := by
      by_cases hunit : α = 1
      · exact ⟨1, by decide, by simpa [hunit] using half_pos hε⟩
      have hpos : 0 < α := by linarith
      obtain ⟨K, hK⟩ := exists_nat_gt (1 + α / (ε / 2))
      let u (p : ℕ) : ℝ := if K ≤ p ∧ p.Prime then 1 / p else 0
      let F (p : ℕ) : ℝ := if K ≤ p ∧ p.Prime then 1 + 1 / ((p : ℝ) - 1) else 1
      let R (n : ℕ) : ℝ := ∏ p ∈ range n, F p
      have hu (p : ℕ) : 0 ≤ u p := by dsimp [u]; split <;> positivity
      have hdiv : ¬ Summable u := fun h => not_summable_one_div_on_primes (h.congr_cofinite <| by
        rw [Nat.cofinite_eq_atTop]; filter_upwards [eventually_ge_atTop K] with p hp; simp [u, hp, Set.indicator_apply])
      have hstep (p : ℕ) : 1 + u p ≤ F p ∧ F p < 1 + (ε / 2) / α := by
        by_cases h : K ≤ p ∧ p.Prime
        · have hp1 : (1 : ℝ) < p := by exact_mod_cast h.2.one_lt
          have hkp : (K : ℝ) ≤ p := by exact_mod_cast h.1
          have hlg : α < ((p : ℝ) - 1) * (ε / 2) := (div_lt_iff₀ (half_pos hε)).1 (by linarith)
          have hlo : (1 : ℝ) / p ≤ 1 / ((p : ℝ) - 1) := one_div_le_one_div_of_le (by linarith) (by linarith)
          have hup : (1 : ℝ) / ((p : ℝ) - 1) < (ε / 2) / α :=
            (div_lt_div_iff₀ (by linarith : 0 < (p : ℝ) - 1) hpos).2 (by nlinarith)
          simp only [u, F, if_pos h]; constructor <;> linarith
        · simp [u, F, h, div_pos (half_pos hε) hpos]
      have hF (p : ℕ) : 1 ≤ F p := by linarith [(hstep p).1, hu p]
      have hR (n : ℕ) : 1 ≤ R n := one_le_prod fun p _ => hF p
      have hsum (n : ℕ) : 1 + ∑ p ∈ range n, u p ≤ R n := by
        induction n with
        | zero => simp [R]
        | succ n ih =>
          rw [sum_range_succ, show R (n + 1) = R n * F n by simp [R, prod_range_succ]]
          calc _ ≤ R n + u n := by linarith
            _ ≤ R n * (1 + u n) := by nlinarith [mul_nonneg (sub_nonneg.2 (hR n)) (hu n)]
            _ ≤ R n * F n := mul_le_mul_of_nonneg_left (hstep n).1 (by linarith [hR n])
      have hex : ∃ n, α ≤ R n := by
        obtain ⟨n, hn⟩ := ((tendsto_atTop.1 ((not_summable_iff_tendsto_nat_atTop_of_nonneg hu).1 hdiv)) α).exists
        exact ⟨n, by linarith [hsum n]⟩
      let n := Nat.find hex
      have hn : α ≤ R n := Nat.find_spec hex
      have hnu : R n < α + ε / 2 := by
        cases hn' : n with
        | zero => simpa [hn', R] using (show 1 < α + ε / 2 by linarith)
        | succ m =>
          have hmR : R m < α := lt_of_not_ge (Nat.find_min hex (show m < n by omega))
          rw [show R (m + 1) = R m * F m by simp [R, prod_range_succ]]
          calc _ ≤ α * F m := mul_le_mul_of_nonneg_right hmR.le (by linarith [hF m])
            _ < α * (1 + (ε / 2) / α) := mul_lt_mul_of_pos_left (hstep m).2 hpos
            _ = _ := by field_simp
      let s := (range n).filter fun p => K ≤ p ∧ p.Prime
      have hs : ∀ p ∈ s, p.Prime := fun _ hp => (mem_filter.1 hp).2.2
      let a : ℕ := ∏ p ∈ s, p
      have ha : 0 < a := prod_pos fun p hp => (hs p hp).pos
      have heq : (a : ℝ) / a.totient = R n := by
        have htot := congrArg (fun q : ℚ => (q : ℝ)) (Nat.totient_eq_mul_prod_factors a)
        push_cast at htot
        rw [htot, Nat.primeFactors_prod hs, div_mul_cancel_left₀ (by exact_mod_cast ha.ne'), ← prod_inv_distrib]
        trans ∏ p ∈ s, (1 + 1 / ((p : ℝ) - 1))
        · refine prod_congr rfl fun p hp => ?_
          have h1 : (1 : ℝ) < p := by exact_mod_cast (hs p hp).one_lt
          have hp0 : (p : ℝ) ≠ 0 := by linarith
          have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
          have hsub : 1 - (p : ℝ)⁻¹ = ((p : ℝ) - 1) / p := by field_simp
          rw [hsub, inv_div]; field_simp; ring
        · exact prod_filter _ _
      exact ⟨a, ha, by rw [heq, abs_of_nonneg (sub_nonneg.2 hn)]; linarith⟩
    let r : ℝ := (P : ℝ) / P.totient
    have hr : 0 < r := div_pos (by exact_mod_cast hP) (by exact_mod_cast Nat.totient_pos.2 hP)
    obtain ⟨N, hN⟩ := exists_nat_gt (r / (ε / 2))
    obtain ⟨q, hq, hqN, hcong⟩ := Nat.exists_prime_gt_modEq_one N (Nat.totient_pos.2 hP).ne'
    obtain ⟨t, htq⟩ := (Nat.modEq_iff_dvd' hq.one_lt.le).1 hcong.symm
    have ht : 0 < t := by_contra fun hz => by
      have : t = 0 := by omega
      simp [this] at htq; have := hq.one_lt; omega
    have htlt : t < q := by have := Nat.le_mul_of_pos_left t (Nat.totient_pos.2 hP); omega
    let S := t.primeFactors \ P.primeFactors
    let k := ∏ p ∈ S, p
    have hs (p) (h : p ∈ S) : p.Prime := Nat.prime_of_mem_primeFactors (mem_sdiff.1 h).1
    have hk : 0 < k := prod_pos fun p hp => (hs p hp).pos
    have hkf : k.primeFactors = S := Nat.primeFactors_prod hs
    have hPk : P.Coprime k := Nat.coprime_prod_right_iff.2 fun p hp =>
      ((hs p hp).coprime_iff_not_dvd.2 fun hd => (mem_sdiff.1 hp).2 (Nat.mem_primeFactors.2 ⟨hs p hp, hd, hP.ne'⟩)).symm
    have hqk : q.Coprime k := hq.coprime_iff_not_dvd.2 fun hd => by
      have hm := Nat.mem_primeFactors.2 ⟨hq, hd, hk.ne'⟩; rw [hkf] at hm
      exact (Nat.le_of_dvd ht (Nat.dvd_of_mem_primeFactors (mem_sdiff.1 hm).1)).not_gt htlt
    have hsub : t.primeFactors ⊆ (P * k).primeFactors := by
      rw [Nat.primeFactors_mul hP.ne' hk.ne', hkf]
      exact fun p hp => if h : p ∈ P.primeFactors then mem_union_left _ h else mem_union_right _ (mem_sdiff.2 ⟨hp, h⟩)
    have htot : (P * k * t).totient = (q * k).totient := by
      have hsc : (P * k * t).totient = t * (P * k).totient := by
        have hpf : (P * k * t).primeFactors = (P * k).primeFactors := by
          rw [Nat.primeFactors_mul (Nat.mul_pos hP hk).ne' ht.ne', union_eq_left.2 hsub]
        have hq' : ((P * k * t).totient : ℚ) = t * (P * k).totient := by
          rw [Nat.totient_eq_mul_prod_factors, Nat.totient_eq_mul_prod_factors, hpf, Nat.cast_mul]; ring
        exact_mod_cast hq'
      rw [hsc, Nat.totient_mul hPk, Nat.totient_mul hqk, Nat.totient_prime hq, htq]; ring
    have hratio : ((P * k * t : ℕ) : ℝ) / (q * k : ℕ) = r * (1 - 1 / (q : ℝ)) := by
      have hcast : (q : ℝ) - 1 = (P.totient : ℝ) * t := by
        simpa [Nat.cast_sub hq.one_lt.le] using congrArg (fun a : ℕ => (a : ℝ)) htq
      have hφ : (P.totient : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.2 hP).ne'
      have hqr : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne_zero
      have hkr : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
      dsimp [r]; push_cast; field_simp; nlinarith [congrArg (fun z : ℝ => z * P * k) hcast]
    have hqr : (0 : ℝ) < q := by exact_mod_cast hq.pos
    have hbd : r / q < ε / 2 := (div_lt_iff₀ hqr).2 (by
      have hlg : r / (ε / 2) < q := hN.trans (by exact_mod_cast hqN)
      have := (div_lt_iff₀ (half_pos hε)).1 hlg; linarith)
    refine ⟨((P * k * t : ℕ) : ℝ) / (q * k : ℕ), ⟨_, _, by positivity, Nat.mul_pos hq.pos hk, htot, rfl⟩, ?_⟩
    calc dist α _ ≤ dist α r + dist r _ := dist_triangle _ _ _
      _ < ε := by
        rw [dist_comm α r, Real.dist_eq, Real.dist_eq, hratio,
          show r - r * (1 - 1 / (q : ℝ)) = r / q by ring, abs_of_pos (div_pos hr hqr)]
        linarith
  obtain ⟨s, hs, hlim⟩ := mem_closure_iff_seq_limit.1 hc
  choose n m hn hm heq hr using hs
  exact ⟨n, m, hn, hm, heq, (funext hr : (fun i => (n i : ℝ) / m i) = s) ▸ hlim⟩
