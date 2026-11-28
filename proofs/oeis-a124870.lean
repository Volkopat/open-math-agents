import OMAStatements.S_oeis_a124870
import Mathlib

namespace A124870

open OMA.S_oeis_a124870

/-- `(7 - 24 i) ^ m = p m + q m * i`. -/
def pq : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | m + 1 => (7 * (pq m).1 + 24 * (pq m).2, 7 * (pq m).2 - 24 * (pq m).1)

def p (m : ℕ) : ℤ := (pq m).1
def q (m : ℕ) : ℤ := (pq m).2

lemma p_zero : p 0 = 1 := rfl
lemma q_zero : q 0 = 0 := rfl
lemma p_succ (m : ℕ) : p (m + 1) = 7 * p m + 24 * q m := rfl
lemma q_succ (m : ℕ) : q (m + 1) = 7 * q m - 24 * p m := rfl

lemma inv (m : ℕ) : p m % 2 = 1 ∧ q m % 8 = 0 ∧
    ((p m % 5 = 1 ∧ q m % 5 = 0) ∨ (p m % 5 = 2 ∧ q m % 5 = 1) ∨
      (p m % 5 = 3 ∧ q m % 5 = 4)) := by
  induction m with
  | zero => rw [p_zero, q_zero]; omega
  | succ m ih => rw [p_succ, q_succ]; omega

lemma base2 : base ^ 2 = (⟨-2 / 25, 3 / 50⟩ : QI) := by
  rw [pow_two, base, QuadraticAlgebra.mk_mul_mk, QuadraticAlgebra.mk.injEq]
  constructor <;> norm_num

lemma base3 : base ^ 3 = (⟨13 / 500, 9 / 500⟩ : QI) := by
  rw [pow_succ, base2, base, QuadraticAlgebra.mk_mul_mk, QuadraticAlgebra.mk.injEq]
  constructor <;> norm_num

lemma base4 : base ^ 4 = (⟨7 / 2500, -24 / 2500⟩ : QI) := by
  rw [pow_succ, base3, base, QuadraticAlgebra.mk_mul_mk, QuadraticAlgebra.mk.injEq]
  constructor <;> norm_num

lemma pow4 (m : ℕ) :
    base ^ (4 * m) = (⟨(p m : ℚ) / 2500 ^ m, (q m : ℚ) / 2500 ^ m⟩ : QI) := by
  induction m with
  | zero =>
    rw [p_zero, q_zero]
    apply QuadraticAlgebra.ext <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  | succ m ih =>
    have e : 4 * (m + 1) = 4 * m + 4 := by ring
    rw [e, pow_add, ih, base4, QuadraticAlgebra.mk_mul_mk, p_succ, q_succ,
      QuadraticAlgebra.mk.injEq]
    constructor
    · push_cast; field_simp; ring
    · push_cast; field_simp; ring

lemma re0 (m : ℕ) : (base ^ (4 * m)).re = (p m : ℚ) / ((2500 ^ m : ℕ) : ℚ) := by
  rw [pow4]; push_cast; rfl

lemma re1 (m : ℕ) :
    (base ^ (4 * m + 1)).re = ((3 * q m - p m : ℤ) : ℚ) / ((10 * 2500 ^ m : ℕ) : ℚ) := by
  rw [pow_succ, pow4, base, QuadraticAlgebra.mk_mul_mk]
  show ((p m : ℚ) / 2500 ^ m * (-1 / 10) + (-1) * ((q m : ℚ) / 2500 ^ m) * (-3 / 10) : ℚ) = _
  push_cast; field_simp; ring

lemma re2 (m : ℕ) :
    (base ^ (4 * m + 2)).re = ((-4 * p m - 3 * q m : ℤ) : ℚ) / ((50 * 2500 ^ m : ℕ) : ℚ) := by
  rw [pow_add, pow4, base2, QuadraticAlgebra.mk_mul_mk]
  show ((p m : ℚ) / 2500 ^ m * (-2 / 25) + (-1) * ((q m : ℚ) / 2500 ^ m) * (3 / 50) : ℚ) = _
  push_cast; field_simp; ring

lemma re3 (m : ℕ) :
    (base ^ (4 * m + 3)).re = ((13 * p m - 9 * q m : ℤ) : ℚ) / ((500 * 2500 ^ m : ℕ) : ℚ) := by
  rw [pow_add, pow4, base3, QuadraticAlgebra.mk_mul_mk]
  show ((p m : ℚ) / 2500 ^ m * (13 / 500) + (-1) * ((q m : ℚ) / 2500 ^ m) * (9 / 500) : ℚ) = _
  push_cast; field_simp; ring

lemma cop10 (c : ℤ) (h2 : c % 2 = 1) (h5 : c % 5 ≠ 0) : Nat.Coprime c.natAbs 10 := by
  have h2' : Nat.Coprime c.natAbs 2 := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
    intro h
    have h' : ((2 : ℕ) : ℤ) ∣ c := Int.natCast_dvd.mpr h
    omega
  have h5' : Nat.Coprime c.natAbs 5 := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_five]
    intro h
    have h' : ((5 : ℕ) : ℤ) ∣ c := Int.natCast_dvd.mpr h
    omega
  exact Nat.Coprime.mul_right h2' h5'

lemma den_eq (c : ℤ) (D k : ℕ) (hD : 0 < D) (hdvd : D ∣ 10 ^ k) (h2 : c % 2 = 1)
    (h5 : c % 5 ≠ 0) : ((c : ℚ) / (D : ℚ)).den = D := by
  have hc : Nat.Coprime c.natAbs D :=
    Nat.Coprime.coprime_dvd_right hdvd (Nat.Coprime.pow_right k (cop10 c h2 h5))
  have h := Rat.den_div_eq_of_coprime (a := c) (b := (D : ℤ)) (by exact_mod_cast hD)
    (by rw [Int.natAbs_natCast]; exact hc)
  exact_mod_cast h

lemma dvd_aux (A j m : ℕ) (hA : A ∣ 10 ^ j) : A * 2500 ^ m ∣ 10 ^ (j + 4 * m) := by
  rw [pow_add, pow_mul]
  exact Nat.mul_dvd_mul hA (pow_dvd_pow_of_dvd (by norm_num) m)

lemma a0 (m : ℕ) : a (4 * m) = 2500 ^ m := by
  have hi := inv m
  unfold a
  rw [re0]
  have hd := dvd_aux 1 0 m (by norm_num)
  rw [one_mul] at hd
  exact den_eq (p m) (2500 ^ m) (0 + 4 * m) (by positivity) hd hi.1 (by omega)

lemma a1 (m : ℕ) : a (4 * m + 1) = 10 * 2500 ^ m := by
  have hi := inv m
  unfold a
  rw [re1]
  exact den_eq _ (10 * 2500 ^ m) (1 + 4 * m) (by positivity) (dvd_aux 10 1 m (by norm_num))
    (by omega) (by omega)

lemma a3 (m : ℕ) : a (4 * m + 3) = 500 * 2500 ^ m := by
  have hi := inv m
  unfold a
  rw [re3]
  exact den_eq _ (500 * 2500 ^ m) (3 + 4 * m) (by positivity) (dvd_aux 500 3 m (by norm_num))
    (by omega) (by omega)

lemma a2 (k : ℕ) : a (4 * (k + 1) + 2) = 31250 * 2500 ^ k := by
  have hi := inv (k + 1)
  obtain ⟨c, hc, hc2, hc5⟩ : ∃ c : ℤ, -4 * p (k + 1) - 3 * q (k + 1) = 4 * c ∧ c % 2 = 1 ∧
      c % 5 ≠ 0 := by
    refine ⟨(-4 * p (k + 1) - 3 * q (k + 1)) / 4, ?_, ?_, ?_⟩ <;> omega
  have hre : (base ^ (4 * (k + 1) + 2)).re = (c : ℚ) / ((31250 * 2500 ^ k : ℕ) : ℚ) := by
    rw [re2, hc]; push_cast; field_simp; ring
  unfold a
  rw [hre]
  exact den_eq c (31250 * 2500 ^ k) (6 + 4 * k) (by positivity)
    (dvd_aux 31250 6 k (by norm_num)) hc2 hc5

lemma a_two : a 2 = 25 := by
  unfold a
  rw [base2]
  have h := Rat.den_div_eq_of_coprime (a := -2) (b := 25) (by norm_num) (by decide)
  have e : ((⟨-2 / 25, 3 / 50⟩ : QI)).re = (((-2 : ℤ) : ℚ) / ((25 : ℤ) : ℚ)) := by
    show (-2 / 25 : ℚ) = _
    norm_num
  rw [e]
  exact_mod_cast h

lemma rec (k : ℕ) (hk : k ≠ 2) : a (k + 4) = 2500 * a k := by
  obtain ⟨m, r, hr, rfl⟩ : ∃ m r, r < 4 ∧ k = 4 * m + r :=
    ⟨k / 4, k % 4, Nat.mod_lt _ (by norm_num), by omega⟩
  interval_cases r
  · have h0 : a (4 * m + 0) = 2500 ^ m := a0 m
    have h1 := a0 (m + 1)
    have e1 : 4 * (m + 1) = 4 * m + 0 + 4 := by ring
    rw [e1] at h1
    rw [h1, h0]
    ring
  · have h0 := a1 m
    have h1 := a1 (m + 1)
    have e1 : 4 * (m + 1) + 1 = 4 * m + 1 + 4 := by ring
    rw [e1] at h1
    rw [h1, h0]
    ring
  · obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    have h0 := a2 j
    have h1 := a2 (j + 1)
    have e1 : 4 * (j + 1 + 1) + 2 = 4 * (j + 1) + 2 + 4 := by ring
    rw [e1] at h1
    rw [h1, h0]
    ring
  · have h0 := a3 m
    have h1 := a3 (m + 1)
    have e1 : 4 * (m + 1) + 3 = 4 * m + 3 + 4 := by ring
    rw [e1] at h1
    rw [h1, h0]
    ring

lemma vals : a 0 = 1 ∧ a 1 = 10 ∧ a 2 = 25 ∧ a 3 = 500 ∧ a 4 = 2500 ∧ a 5 = 25000 ∧
    a 6 = 31250 := by
  have h0 := a0 0
  have h1 := a1 0
  have h3 := a3 0
  have h4 := a0 1
  have h5 := a1 1
  have h6 := a2 0
  norm_num at h0 h1 h3 h4 h5 h6
  exact ⟨h0, h1, a_two, h3, h4, h5, h6⟩

end A124870

open OMA.S_oeis_a124870 in
theorem OMA.solution : type_of% @OMA.S_oeis_a124870.main := by
  refine ⟨?_, ?_⟩
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
    have e4 : k + 4 - 4 = k := by omega
    rw [e4]
    exact A124870.rec k (by omega)
  · have e50 : PowerSeries.C (50 : ℚ) = (50 : PowerSeries ℚ) := map_ofNat _ 50
    have e2500 : PowerSeries.C (2500 : ℚ) = (2500 : PowerSeries ℚ) := map_ofNat _ 2500
    have hpoly : ((1 - PowerSeries.C 50 * PowerSeries.X ^ 2) *
        (1 + PowerSeries.C 50 * PowerSeries.X ^ 2)) * series
        = series - PowerSeries.C (2500 : ℚ) * (PowerSeries.X ^ 4 * series) := by
      rw [e50, e2500]; ring
    rw [hpoly]
    obtain ⟨v0, v1, v2, v3, v4, v5, v6⟩ := A124870.vals
    ext n
    simp only [map_sub, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul',
      PowerSeries.coeff_one, PowerSeries.coeff_X, PowerSeries.coeff_X_pow, series,
      PowerSeries.coeff_mk]
    by_cases hn : n ≤ 6
    · interval_cases n <;> simp [v0, v1, v2, v3, v4, v5, v6] <;> norm_num
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 7 := ⟨n - 7, by omega⟩
      have h := A124870.rec (k + 3) (by omega)
      have e1 : k + 3 + 4 = k + 7 := by ring
      rw [e1] at h
      simp [h]
