import OMAStatements.S_oeis_a101035
import Mathlib

namespace OMA.S_oeis_a101035

open ArithmeticFunction Finset
open scoped ArithmeticFunction.zeta ArithmeticFunction.Moebius

lemma pillai (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, ((Nat.gcd k n : ℕ) : ℤ) = ∑ e ∈ n.divisors, ((Nat.totient e : ℕ) : ℤ) * ((n / e : ℕ) : ℤ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have h1 : ∀ k, ((Nat.gcd k n : ℕ) : ℤ) = ∑ e ∈ n.divisors, if e ∣ k then ((Nat.totient e : ℕ) : ℤ) else 0 := by
    intro k
    have h2 : ((Nat.gcd k n : ℕ) : ℤ) = ∑ e ∈ (Nat.gcd k n).divisors, ((Nat.totient e : ℕ) : ℤ) := by
      exact_mod_cast (Nat.sum_totient (Nat.gcd k n)).symm
    rw [h2, ← Finset.sum_filter]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext e
    simp only [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
    have hg : Nat.gcd k n ≠ 0 := (Nat.gcd_pos_of_pos_right k hn).ne'
    constructor
    · intro h
      exact ⟨⟨h.1.2, hn.ne'⟩, h.1.1⟩
    · intro h
      exact ⟨⟨h.2, h.1.1⟩, hg⟩
  simp_rw [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun e he => ?_)
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  have : (Finset.Icc 1 n).filter (fun k => e ∣ k) = (Finset.Ioc 0 n).filter (fun k => e ∣ k) := by
    ext k; simp; omega
  rw [this, Nat.Ioc_filter_dvd_card_eq_div]
  ring

def J : ArithmeticFunction ℤ := ⟨fun n => (n : ℤ), by simp⟩
def Ph : ArithmeticFunction ℤ := ⟨fun n => ((Nat.totient n : ℕ) : ℤ), by simp⟩
def P : ArithmeticFunction ℤ := ⟨fun n => ∑ k ∈ Finset.Icc 1 n, ((Nat.gcd k n : ℕ) : ℤ), by simp⟩

lemma P_eq : P = Ph * J := by
  ext n
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (fun x y => Ph x * J y)]
  exact pillai n

lemma Ph_zeta : Ph * (ζ : ArithmeticFunction ℤ) = J := by
  ext n
  rw [ArithmeticFunction.coe_mul_zeta_apply]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [J]
  · show ∑ i ∈ n.divisors, ((Nat.totient i : ℕ) : ℤ) = (n : ℤ)
    exact_mod_cast Nat.sum_totient n

lemma Ph_eq : Ph = J * μ := by
  calc Ph = Ph * ((ζ : ArithmeticFunction ℤ) * μ) := by rw [coe_zeta_mul_moebius, mul_one]
    _ = (Ph * (ζ : ArithmeticFunction ℤ)) * μ := by rw [mul_assoc]
    _ = J * μ := by rw [Ph_zeta]

def MJ : ArithmeticFunction ℤ := pmul μ J

lemma MJ_J : MJ * J = 1 := by
  ext n
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (fun x y => MJ x * J y)]
  have key : ∀ d ∈ n.divisors, MJ d * J (n / d) = (n : ℤ) * μ d := by
    intro d hd
    have hdn : d ∣ n := Nat.dvd_of_mem_divisors hd
    obtain ⟨c, rfl⟩ := hdn
    have hd0 : 0 < d := Nat.pos_of_mem_divisors hd |> fun h => Nat.pos_of_ne_zero (by rintro rfl; simp at h)
    have e1 : MJ d = μ d * (d : ℤ) := rfl
    have e2 : J (d * c / d) = (c : ℤ) := by
      show (((d * c / d : ℕ)) : ℤ) = c
      rw [Nat.mul_div_cancel_left _ hd0]
    have e3 : (d * c : ℕ) = d * c := rfl
    rw [e1, e2]; push_cast; ring
  rw [Finset.sum_congr rfl key, ← Finset.mul_sum]
  have h1 := congrArg (fun f => f n) (moebius_mul_coe_zeta : (μ * ζ : ArithmeticFunction ℤ) = 1)
  simp only [ArithmeticFunction.coe_mul_zeta_apply] at h1
  rw [h1]
  by_cases hn : n = 1
  · subst hn; simp
  · simp [hn]

lemma reindex (m : ℕ) (hm : 0 < m) (F : ℕ → ℕ → ℤ) :
    ∑ u ∈ m.divisors, ∑ n ∈ u.divisors, F n (u / n) = ∑ n ∈ m.divisors, ∑ k ∈ (m / n).divisors, F n k := by
  rw [Finset.sum_comm' (t' := m.divisors) (s' := fun n => m.divisors.filter (fun u => n ∣ u))]
  · refine Finset.sum_congr rfl (fun n hn => ?_)
    have hn0 : 0 < n := Nat.pos_of_mem_divisors hn
    have hnm : n ∣ m := Nat.dvd_of_mem_divisors hn
    have hmn : m / n ≠ 0 := (Nat.div_pos (Nat.le_of_dvd hm hnm) hn0).ne'
    refine Finset.sum_nbij' (fun u => u / n) (fun k => n * k) ?_ ?_ ?_ ?_ ?_
    · intro u hu
      rw [Finset.mem_filter, Nat.mem_divisors] at hu
      obtain ⟨c, hc⟩ := hu.2
      have hu1 : u ∣ m := hu.1.1
      rw [Nat.mem_divisors]
      refine ⟨?_, hmn⟩
      rw [hc, Nat.mul_div_cancel_left _ hn0]
      rw [hc] at hu1
      exact Nat.dvd_div_of_mul_dvd hu1
    · intro k hk
      rw [Nat.mem_divisors] at hk
      rw [Finset.mem_filter, Nat.mem_divisors]
      exact ⟨⟨Nat.mul_dvd_of_dvd_div hnm hk.1, hm.ne'⟩, Dvd.intro _ rfl⟩
    · intro u hu
      rw [Finset.mem_filter] at hu
      exact Nat.mul_div_cancel' hu.2
    · intro k hk
      exact Nat.mul_div_cancel_left _ hn0
    · intro u hu; rfl
  · intro u n
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · intro h
      exact ⟨⟨⟨h.1.1, h.1.2⟩, h.2.1⟩, ⟨h.2.1.trans h.1.1, h.1.2⟩⟩
    · intro h
      exact ⟨⟨h.1.1.1, h.1.1.2⟩, h.1.2, (Nat.pos_of_dvd_of_pos h.1.1.1 hm).ne'⟩

lemma a_formula (a : ℕ → ℤ)
    (h : ∀ n : ℕ, 1 ≤ n →
        ∑ d ∈ n.divisors, a d * ∑ k ∈ Finset.Icc 1 (n / d), ((Nat.gcd k (n / d) : ℕ) : ℤ) =
          if n = 1 then 1 else 0) (m : ℕ) (hm : 1 ≤ m) :
    a m = ∑ n ∈ m.divisors, ∑ k ∈ (m / n).divisors, μ n * μ k * ((n : ℤ) * k) := by
  let A : ArithmeticFunction ℤ := ⟨fun n => if n = 0 then 0 else a n, by simp⟩
  have hAP : A * P = 1 := by
    ext n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (fun x y => A x * P y)]
    have e : ∑ d ∈ n.divisors, A d * P (n / d) =
        ∑ d ∈ n.divisors, a d * ∑ k ∈ Finset.Icc 1 (n / d), ((Nat.gcd k (n / d) : ℕ) : ℤ) := by
      refine Finset.sum_congr rfl (fun d hd => ?_)
      have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
      show (if d = 0 then 0 else a d) * _ = _
      rw [if_neg hd0]
      rfl
    rw [e, h n hn]
    simp [ArithmeticFunction.one_apply]
  let B : ArithmeticFunction ℤ := (MJ * MJ) * (ζ : ArithmeticFunction ℤ)
  have hPB : P * B = 1 := by
    calc P * B = (MJ * J) * (MJ * J) * (μ * (ζ : ArithmeticFunction ℤ)) := by
          rw [P_eq, Ph_eq]; ring
      _ = 1 := by rw [MJ_J, moebius_mul_coe_zeta]; simp
  have hAB : A = B := by
    calc A = A * (P * B) := by rw [hPB, mul_one]
      _ = (A * P) * B := by rw [mul_assoc]
      _ = B := by rw [hAP, one_mul]
  have h1 : a m = B m := by
    rw [← hAB]; show a m = (if m = 0 then 0 else a m); rw [if_neg (by omega)]
  rw [h1]
  show ((MJ * MJ) * (ζ : ArithmeticFunction ℤ)) m = _
  rw [ArithmeticFunction.coe_mul_zeta_apply]
  have e2 : ∀ u ∈ m.divisors, (MJ * MJ) u = ∑ n ∈ u.divisors, μ n * μ (u / n) * ((n : ℤ) * ((u / n : ℕ) : ℤ)) := by
    intro u hu
    rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (fun x y => MJ x * MJ y)]
    refine Finset.sum_congr rfl (fun n hn => ?_)
    show μ n * (n : ℤ) * (μ (u / n) * ((u / n : ℕ) : ℤ)) = _
    ring
  rw [Finset.sum_congr rfl e2]
  exact reindex m hm (fun n k => μ n * μ k * ((n : ℤ) * k))

end OMA.S_oeis_a101035

theorem OMA.solution : type_of% @OMA.S_oeis_a101035.main := by
  intro a h m hm
  have hf := OMA.S_oeis_a101035.a_formula a h m hm
  have hq : (a m : ℚ) = ∑ n ∈ m.divisors, ∑ k ∈ (m / n).divisors,
      ((ArithmeticFunction.moebius n * ArithmeticFunction.moebius k : ℤ) : ℚ) * ((n : ℚ) * k) := by
    rw [hf]; push_cast; rfl
  rw [hq, Finset.sum_div]
  refine Finset.sum_congr rfl (fun n hn => ?_)
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  have hnm : n ∣ m := Nat.dvd_of_mem_divisors hn
  have hkm : k ∣ m / n := Nat.dvd_of_mem_divisors hk
  have hnk : n * k ∣ m := Nat.mul_dvd_of_dvd_div hnm hkm
  obtain ⟨j, hj⟩ := hnk
  have hn0 : (n : ℚ) ≠ 0 := by
    have := Nat.pos_of_mem_divisors hn; positivity
  have hk0 : (k : ℚ) ≠ 0 := by
    have := Nat.pos_of_mem_divisors hk; positivity
  have hm0 : (m : ℚ) ≠ 0 := by positivity
  have hj0 : (j : ℚ) ≠ 0 := by
    intro h0
    have : j = 0 := by exact_mod_cast h0
    subst this; simp at hj; omega
  have hd : m / (n * k) = j := by
    rw [hj]; exact Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (by rintro h0; simp [Nat.mul_eq_zero] at h0; rcases h0 with h0 | h0 <;> simp_all))
  rw [hd]
  have hmq : (m : ℚ) = n * k * j := by exact_mod_cast hj
  rw [hmq]
  field_simp
