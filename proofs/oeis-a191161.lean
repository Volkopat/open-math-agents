import OMAStatements.S_oeis_a191161
import Mathlib

open OMA.S_oeis_a191161

namespace OMA.P_oeis_a191161

open ArithmeticFunction

def AF (f : ℕ → ℤ) : ArithmeticFunction ℤ := ⟨fun n => if n = 0 then 0 else f n, by simp⟩

theorem AF_apply (f : ℕ → ℤ) {n : ℕ} (hn : n ≠ 0) : AF f n = f n := by
  simp [AF, hn]

def Z : ArithmeticFunction ℤ := ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℤ)
def K : ArithmeticFunction ℤ := 1 + 1 + -Z
def I : ArithmeticFunction ℤ := ((ArithmeticFunction.id : ArithmeticFunction ℕ) : ArithmeticFunction ℤ)
def Sg : ArithmeticFunction ℤ := ((ArithmeticFunction.sigma 1 : ArithmeticFunction ℕ) : ArithmeticFunction ℤ)
def PhN : ArithmeticFunction ℕ := ⟨fun n => Nat.totient n, by simp⟩
theorem PhN_apply (n : ℕ) : PhN n = Nat.totient n := rfl
def Ph : ArithmeticFunction ℤ := (PhN : ArithmeticFunction ℤ)
def F : ArithmeticFunction ℤ := Ph + Ph + -I

theorem sumdiv (f : ℕ → ℤ) (n : ℕ) (hn : n ≠ 0) :
    ∑ d ∈ n.divisors, f d = ∑ d ∈ n.properDivisors, f d + f n := by
  rw [← Nat.insert_self_properDivisors hn, Finset.sum_insert (by simp), add_comm]

theorem mulZ (G : ArithmeticFunction ℤ) (n : ℕ) (hn : n ≠ 0) :
    (G * Z) n = ∑ d ∈ n.properDivisors, G d + G n := by
  unfold Z
  rw [coe_mul_zeta_apply, sumdiv _ n hn]

theorem mulK (G : ArithmeticFunction ℤ) (n : ℕ) (hn : n ≠ 0) :
    (G * K) n = G n - ∑ d ∈ n.properDivisors, G d := by
  unfold K
  rw [mul_add, mul_add, mul_one, mul_neg, ArithmeticFunction.add_apply, ArithmeticFunction.add_apply,
    ArithmeticFunction.neg_apply, mulZ G n hn]
  ring

theorem mul_apply' (G H : ArithmeticFunction ℤ) (n : ℕ) :
    (G * H) n = ∑ d ∈ n.divisors, G d * H (n / d) := by
  rw [mul_apply, Nat.sum_divisorsAntidiagonal (fun x y => G x * H y)]

theorem pd_AF (f : ℕ → ℤ) (n : ℕ) : ∑ d ∈ n.properDivisors, AF f d = ∑ d ∈ n.properDivisors, f d := by
  apply Finset.sum_congr rfl
  intro d hd
  have : d ≠ 0 := by
    rintro rfl
    rw [Nat.mem_properDivisors] at hd
    obtain ⟨h1, h2⟩ := hd
    rw [zero_dvd_iff] at h1
    omega
  rw [AF_apply f this]

theorem Sg_eq : Sg = I * Z := by
  ext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · unfold Z I Sg
    rw [coe_mul_zeta_apply]
    simp only [natCoe_apply, sigma_one_apply, id_apply]
    push_cast; rfl

theorem PhZ : Ph * Z = I := by
  ext n
  unfold Z I Ph
  rw [coe_mul_zeta_apply]
  simp only [natCoe_apply, PhN_apply, id_apply]
  rw [← Nat.cast_sum, Nat.sum_totient]

theorem II (n : ℕ) : (I * I) n = (n : ℤ) * (n.divisors.card : ℤ) := by
  rw [mul_apply']
  unfold I
  simp only [natCoe_apply, id_apply]
  rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Nat.mem_divisors] at hd
  rw [← Nat.cast_mul, Nat.mul_div_cancel' hd.1]
  simp

end OMA.P_oeis_a191161

open OMA.P_oeis_a191161 ArithmeticFunction in
theorem OMA.solution : type_of% @OMA.S_oeis_a191161.main := by
  intro a B H e ha ⟨hB1, hB⟩ ⟨hH1, hH⟩ ⟨he1, he⟩
  -- the four Dirichlet equations
  have eA : AF a * K = Sg := by
    ext n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [mulK _ n (by omega), pd_AF, AF_apply a (by omega), ha n hn]
      unfold Sg; simp
  have eH : AF H * K = 1 := by
    ext n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [mulK _ n (by omega), pd_AF, AF_apply H (by omega)]
      rcases Nat.lt_or_ge n 2 with h1 | h2
      · obtain rfl : n = 1 := by omega
        simp [hH1]
      · rw [hH n h2, one_apply_ne (by omega)]; ring
  have eB : AF B * K = Z := by
    ext n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [mulK _ n (by omega), pd_AF, AF_apply B (by omega)]
      unfold Z
      simp only [natCoe_apply]
      rw [zeta_apply_ne (by omega)]
      rcases Nat.lt_or_ge n 2 with h1 | h2
      · obtain rfl : n = 1 := by omega
        simp [hB1]
      · rw [hB n h2]; push_cast; ring
  have eE : AF e * F = 1 := by
    ext n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [mul_apply', sumdiv _ n (by omega), Nat.div_self hn,
        AF_apply e (by omega)]
      have hF1 : F 1 = 1 := by
        unfold F Ph I; simp [PhN_apply]
      rw [hF1, mul_one]
      have hsum : ∑ d ∈ n.properDivisors, AF e d * F (n / d) =
          ∑ d ∈ n.properDivisors, (2 * (Nat.totient (n / d) : ℤ) - ((n / d : ℕ) : ℤ)) * e d := by
        apply Finset.sum_congr rfl
        intro d hd
        have hd0 : d ≠ 0 := by
          rintro rfl
          rw [Nat.mem_properDivisors, zero_dvd_iff] at hd
          omega
        rw [AF_apply e hd0]
        unfold F Ph I
        simp only [ArithmeticFunction.add_apply, ArithmeticFunction.neg_apply, natCoe_apply, id_apply, PhN_apply]
        ring
      rw [hsum]
      rcases Nat.lt_or_ge n 2 with h1 | h2
      · obtain rfl : n = 1 := by omega
        simp [he1]
      · rw [he n h2, one_apply_ne (by omega)]; ring
  -- algebra
  have A1 : AF a = Sg * AF H := by
    calc AF a = AF a * (AF H * K) := by rw [eH, mul_one]
      _ = (AF a * K) * AF H := by ring
      _ = Sg * AF H := by rw [eA]
  have B1 : AF B = Z * AF H := by
    calc AF B = AF B * (AF H * K) := by rw [eH, mul_one]
      _ = (AF B * K) * AF H := by ring
      _ = Z * AF H := by rw [eB]
  have G1 : Sg * F = (I * I) * K := by
    rw [Sg_eq]
    unfold F K
    have := PhZ
    calc I * Z * (Ph + Ph + -I) = I * (Ph * Z) + I * (Ph * Z) - I * Z * I := by ring
      _ = I * I * (1 + 1 + -Z) := by rw [this]; ring
  have A2 : AF a * F = I * I := by
    calc AF a * F = (Sg * F) * AF H := by rw [A1]; ring
      _ = (I * I) * (AF H * K) := by rw [G1]; ring
      _ = I * I := by rw [eH, mul_one]
  have A3 : AF a = (I * I) * AF e := by
    calc AF a = AF a * (AF e * F) := by rw [eE, mul_one]
      _ = (AF a * F) * AF e := by ring
      _ = (I * I) * AF e := by rw [A2]
  have A4 : AF a = I * AF B := by
    rw [B1, A1, Sg_eq]; ring
  intro n hn
  have hn0 : n ≠ 0 := by omega
  have conv : ∀ (G : ArithmeticFunction ℤ) (f : ℕ → ℤ),
      (G * AF f) n = ∑ d ∈ n.divisors, G d * f (n / d) := by
    intro G f
    rw [mul_apply']
    apply Finset.sum_congr rfl
    intro d hd
    rw [Nat.mem_divisors] at hd
    have : n / d ≠ 0 := by
      have := Nat.div_pos (Nat.le_of_dvd (by omega) hd.1) (Nat.pos_of_dvd_of_pos hd.1 (by omega))
      omega
    rw [AF_apply f this]
  have ha' : a n = AF a n := (AF_apply a hn0).symm
  refine ⟨?_, ?_, ?_⟩
  · rw [ha', A4, conv]
    apply Finset.sum_congr rfl
    intro d _
    unfold I; simp
  · rw [ha', A1, conv]
    apply Finset.sum_congr rfl
    intro d _
    unfold Sg; simp
  · rw [ha', A3, conv]
    apply Finset.sum_congr rfl
    intro d _
    rw [II]
