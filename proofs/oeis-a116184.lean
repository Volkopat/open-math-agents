import OMAStatements.S_oeis_a116184
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

namespace OMA.P_oeis_a116184

open OMA.S_oeis_a116184

/-- Fast modular exponentiation in `ℕ`. -/
private def powMod (a : ℕ) : ℕ → ℕ → ℕ
  | 0, m => 1 % m
  | e + 1, m => (a * powMod a e m) % m

private lemma powMod_zmod (a e m : ℕ) : (powMod a e m : ZMod m) = (a : ZMod m) ^ e := by
  induction e with
  | zero => simp [powMod]
  | succ e ih =>
    simp only [powMod, ZMod.natCast_mod, Nat.cast_mul, ih, pow_succ']

/-- Explicit modular inverses `j⁻¹ mod 37^3` for `j ∈ {1, ..., 36}`. -/
private def uArr : List ℕ :=
  [0, 1, 25327, 33769, 37990, 30392, 42211, 43417, 18995, 45025, 15196, 27629,
   46432, 19482, 47035, 27015, 34824, 14898, 47839, 2666, 7598, 48241, 39141, 28630,
   23216, 16209, 9741, 48777, 48844, 5240, 38834, 1634, 17412, 26094, 7449, 18814, 49246]

/-- Explicit values `(u_j ^ 36 - 1) mod 37^3` for `j ∈ {1, ..., 36}`. -/
private def dArr : List ℕ :=
  [0, 0, 31450, 26714, 13616, 11322, 32153, 1628, 47804, 41107, 29082, 21460,
   38961, 4070, 23495, 44881, 32708, 47730, 20535, 20609, 48211, 7807, 18685, 1295,
   47138, 7585, 36889, 43179, 46731, 29489, 36630, 28268, 18981, 39960, 35372, 7474, 1332]

private def uVal (j : ℕ) : ℕ := uArr.getD j 0
private def dVal (j : ℕ) : ℕ := dArr.getD j 0

/-- If `x ^ 3 = 0` in a commutative ring, then `(1 + x) ^ k = 1 + k * x + C(k, 2) * x ^ 2`. -/
private lemma one_add_pow_of_cube_zero {R : Type*} [CommRing R] (x : R) (hx : x ^ 3 = 0) :
    ∀ k : ℕ, (1 + x) ^ k = 1 + (k : R) * x + (Nat.choose k 2 : R) * x ^ 2 := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', ih]
    have hch : Nat.choose (k + 1) 2 = Nat.choose k 2 + k := by
      rw [Nat.choose_succ_succ, Nat.choose_one_right, add_comm]
    rw [hch]
    push_cast
    calc (1 + x) * (1 + (k : R) * x + (Nat.choose k 2 : R) * x ^ 2)
        = 1 + ((k : R) + 1) * x + ((Nat.choose k 2 : R) + (k : R)) * x ^ 2 +
            (Nat.choose k 2 : R) * x ^ 3 := by ring
      _ = 1 + ((k : R) + 1) * x + ((Nat.choose k 2 : R) + (k : R)) * x ^ 2 := by rw [hx]; ring

private lemma uVal_mul_mod :
    ∀ j ∈ Finset.Icc (1 : ℕ) 36, (j * uVal j) % (37 ^ 3) = 1 := by
  decide

private lemma uVal_pow36_mod :
    ∀ j ∈ Finset.Icc (1 : ℕ) 36, powMod (uVal j) 36 (37 ^ 3) = (1 + dVal j) % (37 ^ 3) := by
  decide

private lemma dVal_cube_mod :
    ∀ j ∈ Finset.Icc (1 : ℕ) 36, (dVal j ^ 3) % (37 ^ 3) = 0 := by
  decide

private lemma sum_c0_mod :
    (∑ j ∈ Finset.Icc (1 : ℕ) 36, (uVal j ^ 3) % (37 ^ 3)) % (37 ^ 3) = 0 := by
  decide

private lemma sum_c1_mod :
    (∑ j ∈ Finset.Icc (1 : ℕ) 36, ((uVal j ^ 3) % (37 ^ 3) * dVal j) % (37 ^ 3)) % (37 ^ 3) = 0 := by
  decide

private lemma sum_c2_mod :
    (∑ j ∈ Finset.Icc (1 : ℕ) 36,
      (((uVal j ^ 3) % (37 ^ 3) * dVal j) % (37 ^ 3) * dVal j) % (37 ^ 3)) % (37 ^ 3) = 0 := by
  decide

private lemma sum_c0 :
    ∑ j ∈ Finset.Icc (1 : ℕ) 36, (uVal j : ZMod (37 ^ 3)) ^ 3 = 0 := by
  have h : ((∑ j ∈ Finset.Icc (1 : ℕ) 36, (uVal j ^ 3) % (37 ^ 3) : ℕ) : ZMod (37 ^ 3)) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]
    exact Nat.dvd_of_mod_eq_zero sum_c0_mod
  simpa [Nat.cast_sum, ZMod.natCast_mod, Nat.cast_pow] using h

private lemma sum_c1 :
    ∑ j ∈ Finset.Icc (1 : ℕ) 36, (uVal j : ZMod (37 ^ 3)) ^ 3 * (dVal j : ZMod (37 ^ 3)) = 0 := by
  have h : ((∑ j ∈ Finset.Icc (1 : ℕ) 36,
      ((uVal j ^ 3) % (37 ^ 3) * dVal j) % (37 ^ 3) : ℕ) : ZMod (37 ^ 3)) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]
    exact Nat.dvd_of_mod_eq_zero sum_c1_mod
  simpa [Nat.cast_sum, ZMod.natCast_mod, Nat.cast_mul, Nat.cast_pow] using h

private lemma sum_c2 :
    ∑ j ∈ Finset.Icc (1 : ℕ) 36, (uVal j : ZMod (37 ^ 3)) ^ 3 * (dVal j : ZMod (37 ^ 3)) ^ 2 = 0 := by
  have h : ((∑ j ∈ Finset.Icc (1 : ℕ) 36,
      (((uVal j ^ 3) % (37 ^ 3) * dVal j) % (37 ^ 3) * dVal j) % (37 ^ 3) : ℕ) : ZMod (37 ^ 3)) = 0 := by
    rw [ZMod.natCast_eq_zero_iff]
    exact Nat.dvd_of_mod_eq_zero sum_c2_mod
  have h' : ∑ j ∈ Finset.Icc (1 : ℕ) 36,
      (uVal j : ZMod (37 ^ 3)) ^ 3 * (dVal j : ZMod (37 ^ 3)) * (dVal j : ZMod (37 ^ 3)) = 0 := by
    simpa [Nat.cast_sum, ZMod.natCast_mod, Nat.cast_mul, Nat.cast_pow] using h
  convert h' using 2 with j
  ring

private lemma sum_u_pow_zero (k : ℕ) :
    ∑ j ∈ Finset.Icc (1 : ℕ) 36, (uVal j : ZMod (37 ^ 3)) ^ (3 + 36 * k) = 0 := by
  have hterm : ∀ j ∈ Finset.Icc (1 : ℕ) 36,
      (uVal j : ZMod (37 ^ 3)) ^ (3 + 36 * k) =
        (uVal j : ZMod (37 ^ 3)) ^ 3 +
        (k : ZMod (37 ^ 3)) * ((uVal j : ZMod (37 ^ 3)) ^ 3 * (dVal j : ZMod (37 ^ 3))) +
        (Nat.choose k 2 : ZMod (37 ^ 3)) * ((uVal j : ZMod (37 ^ 3)) ^ 3 * (dVal j : ZMod (37 ^ 3)) ^ 2) := by
    intro j hj
    have hd3 : (dVal j : ZMod (37 ^ 3)) ^ 3 = 0 := by
      have h0 : ((dVal j ^ 3 : ℕ) : ZMod (37 ^ 3)) = 0 := by
        rw [ZMod.natCast_eq_zero_iff]
        exact Nat.dvd_of_mod_eq_zero (dVal_cube_mod j hj)
      simpa [Nat.cast_pow] using h0
    have hu36 : (uVal j : ZMod (37 ^ 3)) ^ 36 = 1 + (dVal j : ZMod (37 ^ 3)) := by
      rw [← powMod_zmod (uVal j) 36 (37 ^ 3), uVal_pow36_mod j hj, ZMod.natCast_mod, Nat.cast_add, Nat.cast_one]
    rw [pow_add, pow_mul, hu36, one_add_pow_of_cube_zero (dVal j : ZMod (37 ^ 3)) hd3 k]
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, sum_c0, sum_c1, sum_c2]
  ring

private lemma coprime_factorial_36 : Nat.Coprime (37 ^ 3) (Nat.factorial 36) := by
  have h37 : Nat.Prime 37 := by decide
  have hgen : ∀ m : ℕ, m ≤ 36 → Nat.Coprime 37 m.factorial := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      rw [Nat.factorial_succ]
      have hm1 : Nat.Coprime 37 (m + 1) :=
        h37.coprime_iff_not_dvd.mpr (fun hd => by
          have hle := Nat.le_of_dvd (by omega) hd
          omega)
      exact hm1.mul_right (ih (by omega))
  exact (hgen 36 le_rfl).pow_left 3

private lemma H36_eq_div (n : ℕ) :
    H36 n =
      ((∑ j ∈ Finset.Icc (1 : ℕ) 36, (Nat.factorial 36 / j) ^ n : ℕ) : ℚ) /
        (((Nat.factorial 36) ^ n : ℕ) : ℚ) := by
  unfold H36
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_Icc] at hj
  have hjdvd : j ∣ Nat.factorial 36 := Nat.dvd_factorial hj.1 hj.2
  have hj0 : (j : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hf0 : ((Nat.factorial 36 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero 36)
  have hq : ((Nat.factorial 36 / j : ℕ) : ℚ) = ((Nat.factorial 36 : ℕ) : ℚ) / (j : ℚ) := by
    rw [eq_div_iff hj0]
    exact_mod_cast Nat.div_mul_cancel hjdvd
  rw [hq, div_pow, div_div, mul_comm ((j : ℚ) ^ n), ← div_div, div_self (pow_ne_zero n hf0), one_div]

private lemma prove_main :
    ∀ k : ℕ, ((37 ^ 3 : ℕ) : ℤ) ∣ (H36 (3 + 36 * k)).num := by
  intro k
  set n : ℕ := 3 + 36 * k
  set S : ℕ := ∑ j ∈ Finset.Icc (1 : ℕ) 36, (Nat.factorial 36 / j) ^ n
  set D : ℕ := (Nat.factorial 36) ^ n
  have hD0 : (D : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (pow_ne_zero n (Nat.factorial_ne_zero 36))
  have hS_zmod : (S : ZMod (37 ^ 3)) = 0 := by
    simp only [S, Nat.cast_sum, Nat.cast_pow]
    have hterm : ∀ j ∈ Finset.Icc (1 : ℕ) 36,
        ((Nat.factorial 36 / j : ℕ) : ZMod (37 ^ 3)) ^ n =
          ((Nat.factorial 36 : ℕ) : ZMod (37 ^ 3)) ^ n * (uVal j : ZMod (37 ^ 3)) ^ n := by
      intro j hj
      rw [← mul_pow]
      congr 1
      have hjdvd : j ∣ Nat.factorial 36 :=
        Nat.dvd_factorial (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2
      have hmul : ((Nat.factorial 36 / j : ℕ) : ZMod (37 ^ 3)) * (j : ZMod (37 ^ 3)) =
          ((Nat.factorial 36 : ℕ) : ZMod (37 ^ 3)) := by
        rw [← Nat.cast_mul, Nat.div_mul_cancel hjdvd]
      have hinv : (j : ZMod (37 ^ 3)) * (uVal j : ZMod (37 ^ 3)) = 1 := by
        rw [← Nat.cast_mul, ← ZMod.natCast_mod, uVal_mul_mod j hj, Nat.cast_one]
      calc ((Nat.factorial 36 / j : ℕ) : ZMod (37 ^ 3))
          = ((Nat.factorial 36 / j : ℕ) : ZMod (37 ^ 3)) *
              ((j : ZMod (37 ^ 3)) * (uVal j : ZMod (37 ^ 3))) := by
              rw [hinv, mul_one]
        _ = (((Nat.factorial 36 / j : ℕ) : ZMod (37 ^ 3)) * (j : ZMod (37 ^ 3))) *
              (uVal j : ZMod (37 ^ 3)) := by ring
        _ = ((Nat.factorial 36 : ℕ) : ZMod (37 ^ 3)) * (uVal j : ZMod (37 ^ 3)) := by rw [hmul]
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, sum_u_pow_zero k, mul_zero]
  have hS_dvd : 37 ^ 3 ∣ S := (ZMod.natCast_eq_zero_iff S (37 ^ 3)).mp hS_zmod
  have hq : H36 n = (S : ℚ) / (D : ℚ) := H36_eq_div n
  have hnum_div : ((H36 n).num : ℚ) / ((H36 n).den : ℚ) = (S : ℚ) / (D : ℚ) := by
    rw [Rat.num_div_den, hq]
  have hden0 : ((H36 n).den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (H36 n).den_nz
  have hcross_q : ((H36 n).num : ℚ) * (D : ℚ) = (S : ℚ) * ((H36 n).den : ℚ) := by
    field_simp at hnum_div
    linarith
  have hcross_z : (H36 n).num * (D : ℤ) = (S : ℤ) * ((H36 n).den : ℤ) := by
    exact_mod_cast hcross_q
  have hdvd_prod : ((37 ^ 3 : ℕ) : ℤ) ∣ (H36 n).num * (D : ℤ) := by
    rw [hcross_z]
    exact dvd_mul_of_dvd_left (Int.ofNat_dvd.mpr hS_dvd) _
  have hcop_D : Nat.Coprime (37 ^ 3) D := coprime_factorial_36.pow_right n
  have hcop_z : IsCoprime ((37 ^ 3 : ℕ) : ℤ) (D : ℤ) := hcop_D.isCoprime
  exact hcop_z.dvd_of_dvd_mul_right hdvd_prod

end OMA.P_oeis_a116184

theorem OMA.solution : type_of% @OMA.S_oeis_a116184.main :=
  OMA.P_oeis_a116184.prove_main
