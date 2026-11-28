import FormalConjectures.ErdosProblems.«1004»
import Mathlib.NumberTheory.Bertrand
import Mathlib.Data.Nat.Totient

/-! Shorter proof of `Erdos1004.erdos_1004.variants.le_of_isDistinctTotientRun`. -/

open Filter
open scoped Topology

theorem OMA.solution : type_of% @Erdos1004.erdos_1004.variants.le_of_isDistinctTotientRun := by
  refine ⟨1, by norm_num, ?_⟩
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (1 : ℕ), hlog.eventually_ge_atTop 1000] with n hn hlogn K hrun
  rw [one_mul]
  let z := (n : ℝ) ^ (1 / 3 : ℝ)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hz1 : 1 ≤ z := Real.one_le_rpow hn1 (by norm_num)
  have hz0 : 0 < z := zero_lt_one.trans_le hz1
  have hz3 : z ^ 3 = n := by rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
  let R := ⌈z⌉₊
  have hR : z ≤ R := Nat.le_ceil z
  obtain ⟨p, hp, hRp, hpR⟩ := Nat.exists_prime_lt_and_le_two_mul R fun h0 =>
    hz0.not_ge (by simpa [h0] using hR)
  let d := p - 1
  have hd0 : 0 < d := by have := hp.two_le; omega
  have hd1 : z ≤ d := hR.trans (by exact_mod_cast (show R ≤ d by omega))
  have hd4 : (d : ℝ) ≤ 4 * z := by
    have hp' : (p : ℝ) ≤ 2 * R := by exact_mod_cast hpR
    have hd' : (d : ℝ) ≤ p := by exact_mod_cast (show d ≤ p by omega)
    have : (R : ℝ) < z + 1 := Nat.ceil_lt_add_one hz0.le
    linarith
  let a := d * d
  have ha : 0 < a := Nat.mul_pos hd0 hd0
  let t₀ := n / a + 1
  let t := if p ∣ t₀ then t₀ + 1 else t₀
  have htlo : t₀ ≤ t := by dsimp [t]; split <;> omega
  have hthi : t ≤ t₀ + 1 := by dsimp [t]; split <;> omega
  have htd : ¬ p ∣ t := by
    dsimp [t]; split
    · rename_i h; intro hb
      exact hp.one_lt.not_ge (Nat.le_of_dvd one_pos (by simpa using Nat.dvd_sub hb h))
    · assumption
  let m := t * d; let u := m * d; let v := m * p
  have hu : n < u := by
    rw [show u = t * a by dsimp [u, m, a]; ring]
    exact (Nat.div_lt_iff_lt_mul ha).1 ((Nat.lt_succ_self _).trans_le htlo)
  have huv_eq : v = u + m := by
    dsimp [v, u]; rw [show p = d + 1 by have := hp.two_le; omega, mul_add, mul_one]
  have huv : u < v := by have := Nat.mul_pos ((Nat.succ_pos _).trans_le htlo) hd0; omega
  have htoti : Nat.totient u = Nat.totient v := by
    have hpm : ¬ p ∣ m := fun h => (hp.dvd_mul.1 h).elim htd fun hd => by
      have := Nat.le_of_dvd hd0 hd; omega
    have hm : Nat.totient u = d * Nat.totient m := Nat.eq_of_mul_eq_mul_left (Nat.totient_pos.2 hd0) <| by
      have he := Nat.totient_gcd_mul_totient_mul m d
      rw [Nat.gcd_eq_right ⟨t, mul_comm _ _⟩] at he; linarith
    rw [hm, show v = p * m from mul_comm m p, Nat.totient_mul_of_prime_of_not_dvd hp hpm]
  have hu' : (u : ℝ) ≤ n + 2 * (d : ℝ) ^ 2 := by
    have hb : t * a ≤ n / a * a + 2 * a := by
      have := Nat.mul_le_mul_right a hthi; dsimp only [t₀] at this; linarith
    have hdv := Nat.div_mul_le_self n a
    have h : u ≤ n + 2 * d ^ 2 := by
      have : u = t * a := by dsimp [u, m, a]; ring
      have : a = d ^ 2 := (sq d).symm
      omega
    exact_mod_cast h
  have hm' : (m : ℝ) ≤ z ^ 2 + 2 * d := le_of_mul_le_mul_right (a := (d : ℝ)) (by
    have hdN : (n : ℝ) ≤ z ^ 2 * d := by
      rw [← hz3, pow_succ]; exact mul_le_mul_of_nonneg_left hd1 (sq_nonneg _)
    calc (m : ℝ) * d = u := (Nat.cast_mul m d).symm
      _ ≤ n + 2 * (d : ℝ) ^ 2 := hu'
      _ ≤ (z ^ 2 + 2 * d) * d := by nlinarith only [hdN]) (by exact_mod_cast hd0)
  have hv : (v : ℝ) ≤ n + 41 * z ^ 2 := by
    have hv_eq : (v : ℝ) = u + m := by exact_mod_cast huv_eq
    have hdsq : (d : ℝ) ^ 2 ≤ 16 * z ^ 2 := by nlinarith [mul_le_mul hd4 hd4 (by positivity) (by positivity)]
    have hdlin : (d : ℝ) ≤ 4 * z ^ 2 := by nlinarith [mul_le_mul_of_nonneg_left hz1 hz0.le]
    linarith
  have hbound : (K : ℝ) ≤ 41 * z ^ 2 := by
    by_contra! h
    have hnv : v ≤ n + K := by exact_mod_cast (by linarith only [hv, h] : (v : ℝ) ≤ n + K)
    exact huv.ne (hrun ⟨by omega, by omega⟩ ⟨by omega, hnv⟩ htoti)
  refine hbound.trans ?_
  let L := Real.log (n : ℝ); let y := L ^ (1 / 3 : ℝ)
  have hL0 : 0 < L := by linarith only [hlogn]
  have hy0 : 0 < y := Real.rpow_pos_of_pos hL0 _
  have hy3 : y ^ 3 = L := by rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; norm_num
  have hy10 : 10 ≤ y := by
    by_contra! h
    have := pow_lt_pow_left₀ h hy0.le (by decide : 3 ≠ 0); norm_num at this
    linarith only [this, hy3, hlogn]
  have hy6 : 6 * y ≤ L := by
    nlinarith [sq_nonneg (y - 10), mul_le_mul_of_nonneg_right (show 6 ≤ y ^ 2 by nlinarith) hy0.le]
  have h41 : Real.log 41 ≤ 40 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 41)]
  have hn0 : (0 : ℝ) < n := by positivity
  refine (Real.log_le_log_iff (by positivity) (by positivity)).1 ?_
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_rpow hn0,
    Real.log_div hn0.ne' (Real.exp_pos _).ne', Real.log_exp]
  change Real.log 41 + (2 : ℝ) * ((1 / 3 : ℝ) * L) ≤ L - y
  linarith only [h41, hy6, hlogn]
