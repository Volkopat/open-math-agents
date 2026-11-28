import OMAStatements.S_erdos_415
import Mathlib

/- Erdős Problem 415, first question. Pollack, Pomerance and Treviño,
   Theorem 1.5 and §8 (https://www.pollack-math.net/MonotonePhi.pdf),
   give a sharper asymptotic for monotone runs of consecutive totients.
   Here the reverse permutation suffices. We bound the sum of logarithmic
   totient losses on its interval by counting multiples of each prime. -/

namespace TotientOrdering
open Finset Real Filter Topology OMA.S_erdos_415

noncomputable def loss (n : ℕ) : ℝ := -Real.log ((n.totient : ℝ) / n)
noncomputable def weight (p : ℕ) : ℝ := -Real.log (1 - (p : ℝ)⁻¹)

theorem weight_bounds {p : ℕ} (hp : p.Prime) :
    1 / (p : ℝ) ≤ weight p ∧ weight p ≤ 2 / (p : ℝ) := by
  have hp2 : 2 ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hp0 : 0 < (p : ℝ) := by linarith
  have h : 0 < 1 - (p : ℝ)⁻¹ := by rw [← one_div]; apply sub_pos.mpr; apply (div_lt_one hp0).2; linarith
  constructor
  · have := Real.log_le_sub_one_of_pos h
    unfold weight
    rw [one_div]
    linarith
  · have hb := Real.one_sub_inv_le_log_of_pos h
    have hh : (1 - (p : ℝ)⁻¹)⁻¹ ≤ 1 + 2 / (p : ℝ) := by
      rw [← one_div, div_le_iff₀ h]
      field_simp
      nlinarith
    unfold weight
    linarith

theorem loss_eq {n : ℕ} (hn : 0 < n) : loss n = ∑ p ∈ n.primeFactors, weight p := by
  have he : (n.totient : ℝ) = n * ∏ p ∈ n.primeFactors, (1 - (p : ℝ)⁻¹) := by
    have hq := congrArg (fun x : ℚ => (x : ℝ)) (Nat.totient_eq_mul_prod_factors n)
    push_cast at hq
    exact hq
  have hp : ∀ p ∈ n.primeFactors, 1 - (p : ℝ)⁻¹ ≠ 0 := by
    intro p hp
    have hh : 1 < (p : ℝ) := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
    exact ne_of_gt (sub_pos.mpr (inv_lt_one_of_one_lt₀ hh))
  unfold loss weight
  rw [he, mul_div_cancel_left₀ _ (by exact_mod_cast hn.ne'), Real.log_prod hp, sum_neg_distrib]

theorem forcing_multiple (L : ℝ) : ∃ M : ℕ, 0 < M ∧ ∀ n : ℕ, 0 < n → M ∣ n → L < loss n := by
  classical
  obtain ⟨s, hs⟩ : ∃ s : Finset Nat.Primes, L < ∑ p ∈ s, 1 / (p.val : ℝ) := by
    by_contra! h
    exact Nat.Primes.not_summable_one_div (summable_of_sum_le (fun p => by positivity) h)
  let M := ∏ p ∈ s, p.val
  refine ⟨M, prod_pos (fun p _ => p.property.pos), ?_⟩
  intro n hn hd
  rw [loss_eq hn]
  let e : Nat.Primes ↪ ℕ := Function.Embedding.subtype _
  have hsub : s.map e ⊆ n.primeFactors := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := mem_map.mp hp
    exact Nat.mem_primeFactors.mpr ⟨q.property, (dvd_prod_of_mem (fun r : Nat.Primes => r.val) hq).trans hd, hn.ne'⟩
  calc L < ∑ p ∈ s, 1 / (p.val : ℝ) := hs
       _ ≤ ∑ p ∈ s, weight p.val := sum_le_sum fun p _ => (weight_bounds p.property).1
       _ = ∑ p ∈ s.map e, weight p := by rw [sum_map]; rfl
       _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub <| fun p hp _ =>
         (by positivity : 0 ≤ 1 / (p : ℝ)).trans (weight_bounds (Nat.prime_of_mem_primeFactors hp)).1

theorem propagate {m d i : ℕ} (hd : 0 < m+d) (hdi : d ≤ i)
    (hφ : (m+i).totient ≤ (m+d).totient) : loss (m+d) ≤ loss (m+i) := by
  have hi : 0 < m+i := by omega
  have hda : 0 < ((m+d : ℕ) : ℝ) := by positivity
  have hia : 0 < ((m+i : ℕ) : ℝ) := by positivity
  have hφi := Nat.totient_pos.mpr hi
  unfold loss
  apply neg_le_neg
  apply Real.log_le_log (div_pos (Nat.cast_pos.mpr hφi) hia)
  apply div_le_div₀ (Nat.cast_nonneg _) (Nat.cast_le.mpr hφ) hda
  exact_mod_cast (show m+d ≤ m+i by omega)

theorem occupancy (m k p : ℕ) (hp : 0 < p) :
    ((Ioc m (m+k)).filter (p ∣ ·)).card ≤ k / p + 1 := by
  apply le_trans (b := (Ioc (m/p) ((m+k)/p)).card)
  · apply card_le_card_of_injOn (· / p)
    · intro x hx
      obtain ⟨⟨hx1,hx2⟩, hpx⟩ := (show (m < x ∧ x ≤ m+k) ∧ p ∣ x by simpa using hx)
      have hcancel := Nat.div_mul_cancel hpx
      exact mem_Ioc.mpr ⟨(Nat.div_lt_iff_lt_mul hp).mpr (hcancel.symm ▸ hx1), Nat.div_le_div_right hx2⟩
    · intro x hx y hy h
      have h1 := Nat.div_mul_cancel (mem_filter.mp hx).2
      have h2 := Nat.div_mul_cancel (mem_filter.mp hy).2
      dsimp at h
      exact h1.symm.trans ((congrArg (· * p) h).trans h2)
  · change ((Ioc (m/p) ((m+k)/p)).card : ℕ) ≤ k/p+1
    rw [Nat.card_Ioc, Nat.add_div hp]
    simp only [Nat.add_assoc, Nat.add_sub_cancel_left]
    split <;> simp

theorem first_multiple (m M : ℕ) (hM : 0 < M) :
    ∃ d, 1 ≤ d ∧ d ≤ M ∧ M ∣ m+d := by
  refine ⟨M-m%M, ?_, Nat.sub_le _ _, ?_⟩
  · have := Nat.mod_lt m hM
    omega
  · use m/M+1
    rw [Nat.mul_add_one]
    have := Nat.div_add_mod m M
    have := Nat.mod_lt m hM
    omega

theorem factor_count (n : ℕ) (hn : 0 < n) :
    (n.primeFactors.card : ℝ) * Real.log 2 ≤ Real.log n := by
  have hN : 2 ^ n.primeFactors.card ≤ n := by
    calc 2 ^ n.primeFactors.card = ∏ _p ∈ n.primeFactors, 2 := by simp
         _ ≤ ∏ p ∈ n.primeFactors, p := by
           apply prod_le_prod'; exact fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
         _ ≤ n := Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd _)
  have hc : (2 : ℝ) ^ n.primeFactors.card ≤ n := by exact_mod_cast hN
  simpa using Real.log_le_log (by positivity) hc

theorem dyadic_cost {j : ℕ} (hj : 0 < j) (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime ∧ 2 ^ j < p ∧ p ≤ 2 ^ (j + 1)) :
    ∑ p ∈ s, (1 : ℝ) / p ≤ 4 / j := by
  let x := 2 ^ (j+1)
  have hsub : s ⊆ Nat.primesLE x := fun p hp => Nat.mem_primesLE.mpr ⟨(hs p hp).2.2, (hs p hp).1⟩
  have htheta : ∑ p ∈ s, Real.log p ≤ Real.log 4 * (x : ℝ) := by
    apply le_trans (sum_le_sum_of_subset_of_nonneg hsub (fun p hp _ => ?_))
    · rw [← Chebyshev.theta_eq_sum_primesLE_log]
      exact Chebyshev.theta_le_log4_mul_x (by positivity)
    · exact Real.log_nonneg (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_le)
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hj' : 0 < (j : ℝ) := by positivity
  have hpow : (0 : ℝ) < 2 ^ j := by positivity
  have hcard : s.card * ((j : ℝ) * Real.log 2) ≤ Real.log 4 * (x : ℝ) := by
    apply le_trans _ htheta
    rw [← nsmul_eq_mul, ← sum_const]
    apply sum_le_sum
    intro p hp
    have hpp : (2 : ℝ)^j ≤ (p : ℝ) := by exact_mod_cast (hs p hp).2.1.le
    simpa using Real.log_le_log hpow hpp
  have hx : (x : ℝ) = (2:ℝ)^j * 2 := by simp [x, pow_succ]
  have hfour : Real.log 4 = 2 * Real.log 2 := by
    convert Real.log_pow (2 : ℝ) 2 using 1 <;> norm_num
  rw [hx, hfour] at hcard
  have hcard' : (s.card : ℝ) * j ≤ 4 * 2^j := by
    apply (mul_le_mul_iff_of_pos_right hlog).mp
    linarith only [hcard]
  calc ∑ p ∈ s, (1 : ℝ)/p ≤ ∑ _p ∈ s, (1:ℝ)/2^j := by
         apply sum_le_sum
         intro p hp
         exact one_div_le_one_div_of_le hpow (by exact_mod_cast (hs p hp).2.1.le)
       _ = (s.card : ℝ) / 2 ^ j := by simp [div_eq_mul_inv]
       _ ≤ 4 / j := (div_le_div_iff₀ hpow hj').mpr hcard'

theorem reciprocal_prefix (j : ℕ) :
   ∑ p ∈ Nat.primesLE (2^(j+1)), (1 : ℝ)/p ≤ 1/2 + 4 * (harmonic j : ℝ) := by
  induction j with
  | zero => norm_num [Nat.primesLE, Nat.primesBelow, Finset.sum_filter, Finset.sum_range_succ]
  | succ j ih =>
    let A := Nat.primesLE (2^(j+1))
    let B := Nat.primesLE (2^(j+1+1))
    have hsub : A ⊆ B := by
      intro p hp
      obtain ⟨h₁,h₂⟩ := Nat.mem_primesLE.mp hp
      exact Nat.mem_primesLE.mpr ⟨h₁.trans (by simp [pow_succ]), h₂⟩
    have hs : ∀ p ∈ B \ A, p.Prime ∧ 2^(j+1) < p ∧ p ≤ 2^(j+1+1) := by
      intro p hp
      obtain ⟨hb,ha⟩ := mem_sdiff.mp hp
      obtain ⟨hx,hy⟩ := Nat.mem_primesLE.mp hb
      exact ⟨hy, lt_of_not_ge (fun h => ha (Nat.mem_primesLE.mpr ⟨h,hy⟩)), hx⟩
    have hsum := sum_sdiff hsub (f := fun p : ℕ => (1 : ℝ)/p)
    have h := dyadic_cost (Nat.succ_pos j) _ hs
    change ∑ p ∈ B, (1 : ℝ)/p ≤ _
    change ∑ p ∈ A, (1 : ℝ)/p ≤ _ at ih
    rw [harmonic_succ]
    push_cast
    rw [← hsum]
    rw [div_eq_mul_inv] at h
    push_cast at h
    linarith

theorem decreasing_run (n : ℕ) :
    ∃ m : ℕ, m + F n ≤ n ∧
      ∀ i j : Fin (F n), i < j →
        Nat.totient (m + 1 + j) < Nat.totient (m + 1 + i) := by
  let admissible : Set ℕ :=
    {k | ∀ σ : Equiv.Perm (Fin k), ∃ m : ℕ, m+k≤n ∧ Appears k m σ}
  have hne : admissible.Nonempty := ⟨0, fun _ => ⟨0, by omega, fun i => i.elim0⟩⟩
  have hbd : BddAbove admissible := by
    refine ⟨n, ?_⟩
    intro k hk
    obtain ⟨m, hm, -⟩ := hk 1
    omega
  have h : F n ∈ admissible := Nat.sSup_mem hne hbd
  obtain ⟨m, hm, hdec⟩ := h Fin.revPerm
  exact ⟨m, hm, fun i j hij => (hdec j i).2 (Fin.rev_lt_rev.mpr hij)⟩

noncomputable abbrev ell (n : ℕ) := Real.log (Real.log (Real.log n))
theorem finish (block : ∀ L : ℝ, 0 < L → ∃ M : ℕ, ∀ᶠ n : ℕ in atTop,
    L * ((F n : ℝ) - M) ≤ 5 * F n + 30 + 8 * ell n) :
    ¬ ∃ c : ℝ, 0 < c ∧ Tendsto (fun n : ℕ => (F n : ℝ) / ell n) atTop (𝓝 c) := by
  rintro ⟨c, hc, hlim⟩
  let L := 6 + 9/c
  have hL : 0 < L := by dsimp [L]; positivity
  obtain ⟨M, hM⟩ := block L hL
  have hInf : Tendsto ell atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))
  have hineq : L * (c - 0) ≤ 5 * c + 0 + 8 := by
    apply le_of_tendsto_of_tendsto ((hlim.sub (hInf.const_div_atTop (M : ℝ))).const_mul L)
      (((hlim.const_mul (5 : ℝ)).add (hInf.const_div_atTop 30)).add_const 8)
    filter_upwards [hM, hInf.eventually_gt_atTop 0] with n hn hpos
    field_simp [ne_of_gt hpos]
    nlinarith [hn]
  dsimp [L] at hineq
  have hdiv := div_mul_cancel₀ (9:ℝ) hc.ne'
  nlinarith

theorem loss_nonneg (x : ℕ) (hx : 0 < x) : 0 ≤ loss x := by
  rw [loss_eq hx]
  exact sum_nonneg fun p hp =>
    (by positivity : 0 ≤ 1 / (p : ℝ)).trans (weight_bounds (Nat.prime_of_mem_primeFactors hp)).1

theorem block_lower {L : ℝ} (hL : 0 < L) {M : ℕ} (hM : 0 < M)
    (hforce : ∀ x : ℕ, 0 < x → M ∣ x → L < loss x)
    (m k : ℕ) (hdec : ∀ i j : Fin k, i < j →
      (m + 1 + j).totient < (m + 1 + i).totient) :
    L * ((k : ℝ) - M) ≤ ∑ x ∈ Ioc m (m+k), loss x := by
  have hnon : ∀ x ∈ Ioc m (m+k), 0 ≤ loss x :=
    fun x hx => loss_nonneg x (lt_of_le_of_lt (Nat.zero_le m) (mem_Ioc.mp hx).1)
  by_cases hk : M ≤ k
  · obtain ⟨d, hd, hdM, hdvd⟩ := first_multiple m M hM
    have ht : Ioc (m+M) (m+k) ⊆ Ioc m (m+k) := by
      intro x hx
      obtain ⟨h₁,h₂⟩ := mem_Ioc.mp hx
      exact mem_Ioc.mpr ⟨by omega,h₂⟩
    have htail : ∀ x ∈ Ioc (m+M) (m+k), L ≤ loss x := by
      intro x hx
      obtain ⟨h₁,h₂⟩ := mem_Ioc.mp hx
      let i : Fin k := ⟨d-1, by omega⟩
      let j : Fin k := ⟨x-m-1, by omega⟩
      have hd' : m+1+i.val = m+d := by dsimp [i]; omega
      have hx' : m+1+j.val = x := by dsimp [j]; omega
      have h := hdec i j (by change d-1 < x-m-1; omega)
      rw [hd', hx'] at h
      have hprop := propagate (m := m) (d := d) (i := x-m) (by omega) (by omega)
        (by simpa [Nat.add_sub_of_le (show m ≤ x by omega)] using h.le)
      simpa [Nat.add_sub_of_le (show m ≤ x by omega)] using
        (hforce (m+d) (by omega) hdvd).le.trans hprop
    calc L * ((k : ℝ) - M) = ∑ _x ∈ Ioc (m+M) (m+k), L := by
           simp [Nat.card_Ioc, show m+k-(m+M) = k-M by omega, Nat.cast_sub hk, mul_comm]
         _ ≤ _ := (sum_le_sum htail).trans
           (sum_le_sum_of_subset_of_nonneg ht (fun x hx _ => hnon x hx))
  · exact (mul_nonpos_of_nonneg_of_nonpos hL.le (sub_nonpos.mpr
      (by exact_mod_cast (Nat.le_of_not_ge hk)))).trans (sum_nonneg hnon)

theorem prime_square_sum (b : ℕ) :
    ∑ p ∈ b.primesLE, (1 : ℝ) / (p : ℝ)^2 ≤ 1 := by
  have h : ∀ a : ℕ, (∑ i ∈ range a, (1 : ℝ) / ((i : ℝ)+2)^2) ≤ 1 - 1/((a : ℝ)+1) := by
    intro a
    induction a with
    | zero => norm_num
    | succ a ih =>
      rw [sum_range_succ]
      push_cast
      have htel : (1:ℝ)/((a:ℝ)+2)^2 ≤ 1/((a:ℝ)+1) - 1/((a:ℝ)+2) := by
        field_simp
        nlinarith
      rw [show (a:ℝ)+1+1 = a+2 by ring]
      linarith
  have hsub : b.primesLE ⊆ (range b).image (fun i : ℕ => (i + 2 : ℕ)) := by
    intro p hp
    obtain ⟨hpb, hprime⟩ := Nat.mem_primesLE.mp hp
    exact mem_image.mpr ⟨p-2, mem_range.mpr (by have := hprime.two_le; omega),
      by have := hprime.two_le; omega⟩
  calc ∑ p ∈ b.primesLE, (1 : ℝ)/(p : ℝ)^2 ≤
         ∑ p ∈ (range b).image (fun i : ℕ => (i + 2 : ℕ)), (1 : ℝ)/(p : ℝ)^2 :=
           sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)
       _ = ∑ i ∈ range b, (1 : ℝ)/((i : ℝ)+2)^2 := by
         rw [sum_image (by intro i _ j _ h; exact Nat.add_right_cancel h)]
         simp
       _ ≤ _ := (h b).trans (sub_le_self _ (by positivity))

theorem term_upper (x n b : ℕ) (hx : 0 < x) (hxn : x ≤ n)
    (hB : 0 < log (n : ℝ)) (hb : log (n : ℝ) ≤ b) :
    loss x ≤ (∑ p ∈ b.primesLE, if p ∣ x then 2 / (p : ℝ) else 0) + 3 := by
  classical
  let S := x.primeFactors.filter (· ≤ b)
  let T := x.primeFactors.filter (fun p => ¬ p ≤ b)
  have hS : S = b.primesLE.filter (· ∣ x) := by
    ext p
    simp [S, Nat.mem_primeFactors, Nat.mem_primesLE, hx.ne', and_comm, and_left_comm]
  have hs : ∑ p ∈ S, weight p ≤ ∑ p ∈ b.primesLE, if p ∣ x then 2 / (p : ℝ) else 0 := by
    rw [← sum_filter, ← hS]
    exact sum_le_sum fun p hp => (weight_bounds (Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1)).2
  have ht : ∑ p ∈ T, weight p ≤ ∑ _p ∈ T, 2 / log (n : ℝ) := by
    apply sum_le_sum
    intro p hp
    obtain ⟨hpx, hpb⟩ := mem_filter.mp hp
    exact (weight_bounds (Nat.prime_of_mem_primeFactors hpx)).2.trans
      (div_le_div_of_nonneg_left (by norm_num) hB (hb.trans (by exact_mod_cast (lt_of_not_ge hpb).le)))
  have hcnt : (T.card : ℝ) * log 2 ≤ log n := by
    calc (T.card : ℝ) * log 2 ≤ (x.primeFactors.card : ℝ) * log 2 := by
           gcongr
           exact filter_subset _ _
         _ ≤ _ := (factor_count x hx).trans (Real.log_le_log (by positivity) (by exact_mod_cast hxn))
  have ht' : (T.card : ℝ) * (2 / log n) ≤ 3 := by
    rw [← mul_div_assoc, div_le_iff₀ hB]
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) T.card)
      (show 0 ≤ 3*log 2 - 2 by linarith [Real.log_two_gt_d9])]
  rw [loss_eq hx, ← sum_filter_add_sum_filter_not x.primeFactors (· ≤ b)]
  exact add_le_add hs (ht.trans (by simpa using ht'))

theorem interval_upper (m k n b : ℕ) (hend : m+k ≤ n)
    (hB : 0 < log (n : ℝ)) (hb : log (n : ℝ) ≤ b) :
    ∑ x ∈ Ioc m (m+k), loss x ≤ 5*k + 2 * ∑ p ∈ b.primesLE, (1:ℝ)/p := by
  classical
  let I := Ioc m (m+k)
  have hocc (p : ℕ) (hp : p ∈ b.primesLE) :
      (∑ x ∈ I, if p ∣ x then 2 / (p:ℝ) else 0) ≤
        (2*(k:ℝ)) * (1/(p:ℝ)^2) + 2*(1/(p:ℝ)) := by
    rw [← sum_filter, sum_const, nsmul_eq_mul]
    have h₁ : ((I.filter (p ∣ ·)).card : ℝ) ≤ ((k / p : ℕ) : ℝ) + 1 := by
      exact_mod_cast occupancy m k p (Nat.mem_primesLE.mp hp).2.pos
    have h₂ : ((k / p : ℕ) : ℝ) ≤ (k:ℝ)/p := by
      apply (le_div_iff₀ (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.pos)).2
      exact_mod_cast Nat.div_mul_le_self k p
    calc _ ≤ ((k:ℝ)/p + 1) * (2/(p:ℝ)) := by gcongr; linarith
         _ = _ := by ring
  have ht := sum_le_sum (s := I) (fun x hx => term_upper x n b
    (lt_of_le_of_lt (Nat.zero_le m) (mem_Ioc.mp hx).1) ((mem_Ioc.mp hx).2.trans hend) hB hb)
  rw [sum_add_distrib, sum_comm] at ht
  have hs := sum_le_sum hocc
  rw [sum_add_distrib, ← mul_sum, ← mul_sum] at hs
  have hsq := mul_le_mul_of_nonneg_left (prime_square_sum b) (by positivity : 0 ≤ 2*(k:ℝ))
  have hI : I.card = k := by simp [I, Nat.card_Ioc]
  simp only [sum_const, nsmul_eq_mul, hI] at ht
  change ∑ x ∈ I, loss x ≤ _
  linarith


theorem cutoff_bound (n : ℕ) (hB : 2 ≤ log (n : ℝ)) :
    ∃ b : ℕ, log (n : ℝ) ≤ b ∧
      2 * (∑ p ∈ b.primesLE, (1:ℝ)/p) ≤ 30 + 8 * ell n := by
  let B := log (n : ℝ)
  have hB0 : 0 < B := by dsimp [B]; linarith
  have h2 : 0 < log 2 := Real.log_pos (by norm_num)
  have hlog : log 2 ≤ log B := Real.log_le_log (by norm_num) hB
  let J := ⌈log B / log 2⌉₊
  have hq : 1 ≤ log B / log 2 := (one_le_div h2).2 hlog
  have hlow : log B / log 2 ≤ (J : ℝ) := Nat.le_ceil _
  have hhigh : (J : ℝ) < log B / log 2 + 1 :=
    Nat.ceil_lt_add_one (by linarith)
  refine ⟨2^(J+1), ?_, ?_⟩
  · have hl : log B ≤ (J : ℝ)*log 2 := (div_le_iff₀ h2).mp hlow
    have hb : B ≤ (2:ℝ)^J := by
      apply (Real.log_le_log_iff hB0 (by positivity)).mp
      simpa using hl
    push_cast
    rw [pow_succ]
    change B ≤ _
    linarith
  · have hJ : 0 < (J : ℝ) := by linarith
    have hjlog : log (J : ℝ) ≤ log (log B) + 2 := by
      have hu : (J : ℝ) ≤ log B * (2 / log 2) := by
        calc (J : ℝ) ≤ log B / log 2 + 1 := hhigh.le
             _ ≤ log B / log 2 + log B / log 2 := by linarith
             _ = _ := by ring
      have hlogB : 0 < log B := h2.trans_le hlog
      have hc : 2 / log 2 ≤ 3 := (div_le_iff₀ h2).mpr (by linarith [Real.log_two_gt_d9])
      calc log (J : ℝ) ≤ log (log B * (2 / log 2)) := Real.log_le_log hJ hu
           _ = _ + log (2 / log 2) := Real.log_mul hlogB.ne' (by positivity)
           _ ≤ _ := by linarith [Real.log_le_sub_one_of_pos (show 0 < 2/log 2 by positivity)]
    have hs := reciprocal_prefix J
    have hh := harmonic_le_one_add_log J
    change 2 * _ ≤ 30 + 8 * log (log B)
    linarith

end TotientOrdering

open TotientOrdering OMA.S_erdos_415 Filter in
theorem OMA.solution : type_of% @OMA.S_erdos_415.main := by
  apply finish
  intro L hL
  obtain ⟨M, hM, hf⟩ := forcing_multiple L
  refine ⟨M, ?_⟩
  have hlarge : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlarge.eventually_ge_atTop 2] with n hn
  obtain ⟨m, hm, hdec⟩ := decreasing_run n
  obtain ⟨b, hb, hrec⟩ := cutoff_bound n hn
  have hlo := block_lower hL hM hf m (F n) hdec
  have hup := interval_upper m (F n) n b hm (by linarith) hb
  linarith

