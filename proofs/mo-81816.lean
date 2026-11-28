import OMAStatements.S_mo_81816
import Mathlib

namespace PrimePowerDivisibility

open Finset OMA.S_mo_81816

/-!
The nonnegative-exponent question allows all exponents to vanish. The
additional lemmas explain the difference for positive exponents.
-/

theorem nonnegative_exponents (m : ℕ) :
    ∃ p a : Fin m → ℕ, valid p a := by
  refine ⟨fun _ => 3, fun _ => 0, ?_, ?_, ?_⟩
  · exact monotone_const
  · intro _
    change Nat.Prime 3 ∧ Odd (3 : ℕ)
    decide
  · simp

theorem positive_exponents :
    ∃ p a : Fin 7 → ℕ, valid p a ∧ ∀ i, 0 < a i := by
  let p : Fin 7 → ℕ := ![3, 3, 3, 3, 5, 5, 89]
  let a : Fin 7 → ℕ := fun _ => 1
  refine ⟨p, a, ?_, fun _ => by decide⟩
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [p]
  · intro i
    fin_cases i <;> decide
  · decide


private def positiveOddPower (x : ℤ) : Prop :=
  ∃ p k : ℕ, Nat.Prime p ∧ Odd p ∧ 0 < k ∧ x = (p : ℤ)^k

private theorem positiveOddPower_basic {x : ℤ} (h : positiveOddPower x) :
    3 ≤ x ∧ Odd x ∧ x ≠ 15 := by
  obtain ⟨p,k,hp,hop,hk,rfl⟩ := h
  have hp3 : 3 ≤ p := by
    obtain ⟨u,hu⟩ := hop
    have hp2 := hp.two_le
    omega
  have hP : (p : ℤ) ≤ (p : ℤ)^k := by
    obtain ⟨i,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
    rw [pow_succ]
    have hPow : (1 : ℤ) ≤ (p : ℤ)^i := one_le_pow₀ (by exact_mod_cast (show 1 ≤ p by omega))
    nlinarith [mul_le_mul_of_nonneg_right hPow (show 0 ≤ (p : ℤ) by positivity)]
  refine ⟨le_trans (by exact_mod_cast hp3) hP, (by exact_mod_cast hop : Odd (p : ℤ)).pow, ?_⟩
  intro h15
  have he : p^k = 15 := by exact_mod_cast h15
  have h3 : (3 : ℕ) ∣ p^k := by rw [he]; decide
  have h5 : (5 : ℕ) ∣ p^k := by rw [he]; decide
  have h3p := (show Nat.Prime 3 by decide).dvd_of_dvd_pow h3
  have h5p := (show Nat.Prime 5 by decide).dvd_of_dvd_pow h5
  have hp3' : p = 3 := ((Nat.dvd_prime hp).mp h3p).resolve_left (by decide) |>.symm
  have hp5' : p = 5 := ((Nat.dvd_prime hp).mp h5p).resolve_left (by decide) |>.symm
  omega

private theorem no_three_sorted {a b c : ℤ} (ha : 3 ≤ a) (hab : a ≤ b) (hbc : b ≤ c)
    (haOdd : Odd a) (hbOdd : Odd b) (hcOdd : Odd c) (hc15 : c ≠ 15) :
    ¬ ((a-1)*(b-1)*(c-1) ∣ a*b*c-1) := by
  intro h
  let P := (a-1)*(b-1)*(c-1)
  let N := a*b*c-1
  obtain ⟨q,hq⟩ := h
  change N = P*q at hq
  have hA : 0 < a-1 := by omega
  have hB : 0 < b-1 := by omega
  have hC : 0 < c-1 := by omega
  have hP : 0 < P := by dsimp [P]; positivity
  have hLower (z : ℤ) (hz : z*P < N) : z < q := by
    rw [hq, mul_comm P q] at hz
    by_contra hn
    exact (not_le_of_gt hz) (mul_le_mul_of_nonneg_right (le_of_not_gt hn) hP.le)
  have hUpper (z : ℤ) (hz : N < z*P) : q < z := by
    rw [hq, mul_comm P q] at hz
    by_contra hn
    exact (not_le_of_gt hz) (mul_le_mul_of_nonneg_right (le_of_not_gt hn) hP.le)
  have hq2 : 1 < q := by
    apply hLower
    have hh : 0 < (a-1)*(b-1)+(a-1)*(c-1)+(b-1)*(c-1)+(a-1)+(b-1)+(c-1) := by
      positivity
    dsimp [N,P]
    nlinarith only [hh]
  have ha3 : a = 3 := by
    by_contra hne
    have ha5 : 5 ≤ a := by obtain ⟨x,hx⟩ := haOdd; omega
    let x := a-5
    let y := b-5
    let z := c-5
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hz : 0 ≤ z := by dsimp [z]; omega
    have ht : 0 < 4 + 7*(x+y+z) + 3*(x*y+x*z+y*z) + x*y*z := by positivity
    have hu : N < 2*P := by
      dsimp [x,y,z] at ht
      dsimp [N,P]
      nlinarith only [ht]
    have := hUpper 2 hu
    omega
  have hb8 : b < 9 := by
    by_contra! hb9
    let x := b-9
    let y := c-9
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have ht : 0 < 14 + 5*x + 5*y + x*y := by positivity
    have hu : N < 2*P := by
      dsimp [x,y] at ht
      simp only [N,P,ha3]
      nlinarith only [ht]
    have := hUpper 2 hu
    omega
  have hbCases : b = 3 ∨ b = 5 ∨ b = 7 := by obtain ⟨x,hx⟩ := hbOdd; omega
  rcases hbCases with hb | hb | hb
  · have hQ : 2 < q := hLower 2 (by simp [N,P,ha3,hb]; omega)
    by_cases hc3 : c = 3
    · norm_num [N,P,ha3,hb,hc3] at hq
      omega
    · have hc5 : 5 ≤ c := by obtain ⟨x,hx⟩ := hcOdd; omega
      have := hUpper 3 (by simp [N,P,ha3,hb]; omega)
      omega
  · have hQ := hUpper 3 (by simp [N,P,ha3,hb]; omega)
    have hq' : q = 2 := by omega
    have he : c = 15 := by
      simp [N,P,ha3,hb,hq'] at hq
      omega
    exact hc15 he
  · have hQ := hUpper 3 (by simp [N,P,ha3,hb]; omega)
    have hq' : q = 2 := by omega
    simp [N,P,ha3,hb,hq'] at hq
    omega

theorem no_three_positive (a b c : ℤ) (hA : positiveOddPower a)
    (hB : positiveOddPower b) (hC : positiveOddPower c) :
    ¬ ((a-1)*(b-1)*(c-1) ∣ a*b*c-1) := by
  have apply_sorted (x y z : ℤ) (hx : positiveOddPower x) (hy : positiveOddPower y)
      (hz : positiveOddPower z) (hxy : x ≤ y) (hyz : y ≤ z) :
      ¬ ((x-1)*(y-1)*(z-1) ∣ x*y*z-1) :=
    no_three_sorted (positiveOddPower_basic hx).1 hxy hyz (positiveOddPower_basic hx).2.1
      (positiveOddPower_basic hy).2.1 (positiveOddPower_basic hz).2.1 (positiveOddPower_basic hz).2.2
  intro hev
  by_cases hab : a ≤ b
  · by_cases hbc : b ≤ c
    · exact apply_sorted a b c hA hB hC hab hbc hev
    · by_cases hac : a ≤ c
      · apply apply_sorted a c b hA hC hB hac (by omega)
        simpa only [mul_comm,mul_left_comm,mul_assoc] using hev
      · apply apply_sorted c a b hC hA hB (by omega) hab
        simpa only [mul_comm,mul_left_comm,mul_assoc] using hev
  · by_cases hac : a ≤ c
    · apply apply_sorted b a c hB hA hC (by omega) hac
      simpa only [mul_comm,mul_left_comm,mul_assoc] using hev
    · by_cases hbc : b ≤ c
      · apply apply_sorted b c a hB hC hA hbc (by omega)
        simpa only [mul_comm,mul_left_comm,mul_assoc] using hev
      · apply apply_sorted c b a hC hB hA (by omega) (by omega)
        simpa only [mul_comm,mul_left_comm,mul_assoc] using hev

end PrimePowerDivisibility

theorem OMA.solution : type_of% @OMA.S_mo_81816.main := by
  intro m _
  exact PrimePowerDivisibility.nonnegative_exponents m
