import FormalConjectures.ErdosProblems.«856»
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.Harmonic.Bounds

/-! Count representations as a product of a member of the set and a prime. -/

open Finset Nat Filter Real

theorem OMA.solution : type_of% @Erdos856.erdos_856.variants.erdos_upper := by
  classical
  intro k hk
  have hlog : Tendsto (fun N : ℕ => log (N : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine ⟨6 * (k : ℝ), by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (2 : ℕ),
    hlog.eventually (eventually_ge_atTop (1 : ℝ)),
    (tendsto_log_atTop.comp hlog).eventually (eventually_gt_atTop (0 : ℝ))] with N hN hlogN hloglogN
  unfold Erdos856.f
  refine csSup_le ⟨0, ∅, empty_subset _, fun ⟨S, hS, hcard, _, _⟩ => by
    have := card_le_card hS; rw [card_empty] at this; omega, by simp⟩ ?_
  rintro _ ⟨A, hA, hfree, rfl⟩
  let P := (N + 1).primesBelow
  have hp_bd {p : ℕ} (hp : p.Prime) : (p : ℝ)⁻¹ ≤ 1 / 2 := by
    rw [one_div]; exact inv_anti₀ (by norm_num) (by exact_mod_cast hp.two_le)
  have hlogsum : log (log (N : ℝ)) ≤ 2 * ∑ p ∈ P, (p : ℝ)⁻¹ := by
    have heul : (harmonic N : ℝ) ≤ ∏ p ∈ P, (1 - (p : ℝ)⁻¹)⁻¹ := by
      let f (n : ℕ) : ℝ := (n : ℝ)⁻¹
      have hs {p : ℕ} (hp : p.Prime) : Summable fun n : ℕ => ‖f (p ^ n)‖ := by
        simpa [f, mul_inv, inv_pow, Real.norm_eq_abs, abs_of_nonneg] using
          summable_geometric_of_lt_one (by positivity) ((hp_bd hp).trans_lt (by norm_num))
      obtain ⟨-, heuler⟩ := EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
        (by simp [f]) (fun _ => by simp [f, mul_comm]) (fun hp => hs hp) (N + 1)
      have hprod : ∏ p ∈ P, (1 - (p : ℝ)⁻¹)⁻¹ = ∏ p ∈ P, ∑' n : ℕ, f (p ^ n) :=
        prod_congr rfl fun p hp => by
          simp only [f, Nat.cast_pow, ← inv_pow]
          exact (tsum_geometric_of_lt_one (by positivity) ((hp_bd (prime_of_mem_primesBelow hp)).trans_lt (by norm_num))).symm
      rw [← hprod] at heuler
      let s := Icc 1 N
      let emb : s ↪ (N + 1).smoothNumbers := ⟨fun m => ⟨m.1, Nat.mem_smoothNumbers_of_lt
        (by have := (mem_Icc.1 m.2).1; omega) (by have := (mem_Icc.1 m.2).2; omega)⟩,
        fun _ _ h => Subtype.ext (congrArg (fun t : (N + 1).smoothNumbers => t.1) h)⟩
      rw [show (harmonic N : ℝ) = ∑ m ∈ s, f m by simp [harmonic_eq_sum_Icc, s, f], ← sum_attach s]
      change (∑ m ∈ s.attach, f (emb m).1) ≤ _
      rw [← sum_map s.attach emb (fun m => f m.1), ← heuler.tsum_eq]
      exact heuler.summable.sum_le_tsum _ fun _ _ => by dsimp [f]; positivity
    have hple : log (N : ℝ) ≤ ∏ p ∈ P, (1 - (p : ℝ)⁻¹)⁻¹ :=
      (log_le_harmonic_floor (N : ℝ) (by positivity)).trans (by simpa using heul)
    have hpp p (hp : p ∈ P) : 0 < (1 - (p : ℝ)⁻¹)⁻¹ := inv_pos.2 (by linarith [hp_bd (prime_of_mem_primesBelow hp)])
    calc log (log (N : ℝ)) ≤ log (∏ p ∈ P, (1 - (p : ℝ)⁻¹)⁻¹) :=
          (log_le_log_iff (log_pos (by exact_mod_cast (by omega : 1 < N))) (prod_pos hpp)).2 hple
      _ = ∑ p ∈ P, log ((1 - (p : ℝ)⁻¹)⁻¹) := log_prod fun p hp => (hpp p hp).ne'
      _ ≤ ∑ p ∈ P, 2 * (p : ℝ)⁻¹ := sum_le_sum fun p hp => by
          let u := (p : ℝ)⁻¹
          have hu : u ≤ 1 / 2 := hp_bd (prime_of_mem_primesBelow hp)
          have hu1 : 0 < 1 - u := by linarith
          calc log (1 - u)⁻¹ ≤ (1 - u)⁻¹ - 1 := log_le_sub_one_of_pos (inv_pos.2 hu1)
            _ = u / (1 - u) := by field_simp; ring
            _ ≤ 2 * u := (div_le_iff₀ hu1).2 (by dsimp [u]; nlinarith [show 0 ≤ (p : ℝ)⁻¹ by positivity])
      _ = _ := (mul_sum ..).symm
  have hrec : (∑ a ∈ A, (a : ℝ)⁻¹) * (∑ p ∈ P, (p : ℝ)⁻¹) ≤ (k : ℝ) * harmonic (N ^ 2) := by
    let S := A ×ˢ P
    let prod (v : ℕ × ℕ) := v.1 * v.2
    let fib (t : ℕ) := S.filter fun v => prod v = t
    have hmaps : (S : Set (ℕ × ℕ)).MapsTo prod (Icc 1 (N ^ 2) : Finset ℕ) := fun v hv => by
      obtain ⟨ha, hp⟩ := mem_product.1 (mem_coe.1 hv)
      have := mem_Icc.1 (hA ha); have hps := mem_primesBelow.1 hp
      exact mem_coe.2 (mem_Icc.2 ⟨Nat.mul_pos (by omega) hps.2.pos, by rw [pow_two]; exact Nat.mul_le_mul (by omega) (by omega)⟩)
    have hfib t : (fib t).card ≤ k := by
      by_contra! hbad
      obtain ⟨h, hsub, hcard⟩ := exists_subset_card_eq hbad.le
      have hpr v (hv : v ∈ h) : v.1 ∈ A ∧ v.2.Prime ∧ v.1 * v.2 = t := by
        have hm := mem_filter.1 (hsub hv); have hv' := mem_product.1 hm.1
        exact ⟨hv'.1, prime_of_mem_primesBelow hv'.2, hm.2⟩
      have hinj : (h : Set (ℕ × ℕ)).InjOn Prod.fst := fun v hv w hw he => by
        have hpd := (hpr v (mem_coe.1 hv)).2.2.trans (hpr w (mem_coe.1 hw)).2.2.symm
        have := (mem_Icc.1 (hA (hpr v (mem_coe.1 hv)).1)).1
        exact Prod.ext he (Nat.eq_of_mul_eq_mul_left (show 0 < v.1 by omega) (by simpa only [← he] using hpd))
      refine hfree ⟨h.image Prod.fst, fun a ha => by obtain ⟨v, hv, rfl⟩ := mem_image.1 ha; exact (hpr v hv).1,
        (Finset.card_image_of_injOn hinj).trans hcard, t, fun a ha b hb hne => ?_⟩
      obtain ⟨v, hv, rfl⟩ := mem_image.1 ha; obtain ⟨w, hw, rfl⟩ := mem_image.1 hb
      have hv' := hpr v hv; have hw' := hpr w hw
      have hpd := hv'.2.2.trans hw'.2.2.symm
      have hpq : v.2 ≠ w.2 := fun he => hne (Nat.eq_of_mul_eq_mul_right hv'.2.1.pos (he ▸ hpd))
      have hco := (Nat.coprime_primes hv'.2.1 hw'.2.1).2 hpq
      obtain ⟨c, hc⟩ := hco.symm.dvd_of_dvd_mul_right (hpd.symm ▸ dvd_mul_left w.2 w.1)
      have hb' : w.1 = c * v.2 := Nat.eq_of_mul_eq_mul_right hw'.2.1.pos (by rw [← hpd, hc]; ac_rfl)
      have hlcm : Nat.lcm v.1 w.1 = v.1 * v.2 := by
        rw [hc, hb', mul_comm w.2 c, ← lcm_eq_nat_lcm, _root_.lcm_mul_left, normalize_eq,
          lcm_eq_nat_lcm, hco.symm.lcm_eq_mul]; ac_rfl
      exact hlcm.trans hv'.2.2
    have hsum : (∑ v ∈ S, (prod v : ℝ)⁻¹) = (∑ a ∈ A, (a : ℝ)⁻¹) * (∑ p ∈ P, (p : ℝ)⁻¹) := by
      simp only [S, prod, sum_product, Nat.cast_mul, mul_inv, sum_mul, mul_sum]; exact sum_comm
    rw [← hsum, ← sum_fiberwise_of_maps_to hmaps, show (harmonic (N ^ 2) : ℝ) = ∑ m ∈ Icc 1 (N ^ 2), (m : ℝ)⁻¹ by
      simp [harmonic_eq_sum_Icc], mul_sum]
    refine sum_le_sum fun t _ => ?_
    calc (∑ v ∈ fib t, (prod v : ℝ)⁻¹) = (fib t).card * (t : ℝ)⁻¹ := by
          rw [← nsmul_eq_mul, ← sum_const]; exact sum_congr rfl fun v hv => by rw [(mem_filter.1 hv).2]
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hfib t) (by positivity)
  have hH : (harmonic (N ^ 2) : ℝ) ≤ 3 * log (N : ℝ) := by
    have h := harmonic_le_one_add_log (N ^ 2); rw [Nat.cast_pow, Real.log_pow] at h; norm_num at h; linarith only [hlogN, h]
  have hsum0 : 0 ≤ ∑ a ∈ A, (a : ℝ)⁻¹ := sum_nonneg fun _ _ => by positivity
  rw [← mul_div_assoc, le_div_iff₀ (show 0 < log (log (N : ℝ)) from hloglogN)]
  calc (∑ a ∈ A, (a : ℝ)⁻¹) * log (log (N : ℝ)) ≤ (∑ a ∈ A, (a : ℝ)⁻¹) * (2 * ∑ p ∈ P, (p : ℝ)⁻¹) :=
        mul_le_mul_of_nonneg_left hlogsum hsum0
    _ = 2 * ((∑ a ∈ A, (a : ℝ)⁻¹) * (∑ p ∈ P, (p : ℝ)⁻¹)) := by ring
    _ ≤ 2 * ((k : ℝ) * harmonic (N ^ 2)) := mul_le_mul_of_nonneg_left hrec (by norm_num)
    _ ≤ 2 * ((k : ℝ) * (3 * log (N : ℝ))) := by gcongr
    _ = _ := by ring
