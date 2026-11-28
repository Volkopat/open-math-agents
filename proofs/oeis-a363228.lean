import OMAStatements.S_oeis_a363228
import Mathlib

namespace R363228
open OMA.S_oeis_a363228

theorem lt2 (j : ℕ) : j < 2 ^ j := Nat.lt_two_pow_self

theorem four_pow (k : ℕ) : (4 : ℕ) ^ k = 2 ^ (2 * k) := by
  rw [pow_mul] <;> norm_num

theorem exp4_pow (j u : ℕ) (hu : Odd u) : exp4 (2 ^ j * u) = j / 2 := by
  have hu' : u % 2 = 1 := Nat.odd_iff.mp hu
  unfold OMA.S_oeis_a363228.exp4
  refine Nat.findGreatest_eq_iff.mpr ⟨?_, ?_, ?_⟩
  · have h1 := lt2 j
    have h2 : 2 ^ j * 1 ≤ 2 ^ j * u := Nat.mul_le_mul (le_refl _) (by omega)
    omega
  · intro _
    show 4 ^ (j / 2) ∣ 2 ^ j * u
    rw [four_pow]
    exact dvd_mul_of_dvd_left (pow_dvd_pow 2 (by omega)) u
  · intro k hk _ hd
    have hd' : 4 ^ k ∣ 2 ^ j * u := hd
    rw [four_pow] at hd'
    have h3 : 2 ^ (j + 1) ∣ 2 ^ j * u := dvd_trans (pow_dvd_pow 2 (by omega)) hd'
    obtain ⟨t, ht⟩ := h3
    have h4 : 2 ^ j * u = 2 ^ j * (2 * t) := by rw [ht]; ring
    have h5 := Nat.eq_of_mul_eq_mul_left (by positivity) h4
    omega

theorem exp4_zero (x : ℕ) (hx : ¬ 4 ∣ x) : exp4 x = 0 := by
  unfold OMA.S_oeis_a363228.exp4
  refine Nat.findGreatest_eq_iff.mpr ⟨Nat.zero_le _, fun h => (h rfl).elim, ?_⟩
  intro k hk _ hd
  exact hx (dvd_trans (dvd_pow_self (4 : ℕ) (by omega)) hd)

theorem fib24 (m : ℕ) : Nat.fib (m + 24) % 16 = Nat.fib m % 16 := by
  have h : Nat.fib (m + 24) = Nat.fib m * Nat.fib 23 + Nat.fib (m + 1) * Nat.fib 24 :=
    Nat.fib_add m 23
  have e23 : Nat.fib 23 = 28657 := by decide
  have e24 : Nat.fib 24 = 46368 := by decide
  rw [e23, e24] at h
  omega

theorem fibmod (r q : ℕ) : Nat.fib (r + 24 * q) % 16 = Nat.fib r % 16 := by
  induction q with
  | zero => simp
  | succ q ih => rw [show r + 24 * (q + 1) = r + 24 * q + 24 by ring, fib24, ih]

theorem fibmod' (m : ℕ) : Nat.fib m % 16 = Nat.fib (m % 24) % 16 := by
  have h := fibmod (m % 24) (m / 24)
  rw [Nat.mod_add_div] at h
  exact h

theorem tab : ∀ r, r < 24 → (r % 6 = 0 → Nat.fib r % 8 = 0) ∧ (r % 6 = 1 → Nat.fib r % 2 = 1) ∧
    (r % 12 = 6 → Nat.fib r % 16 = 8) ∧ (r % 6 ≠ 0 → Nat.fib r % 4 ≠ 0) := by
  decide +kernel

theorem fprop (m : ℕ) : (m % 6 = 0 → Nat.fib m % 8 = 0) ∧ (m % 6 = 1 → Nat.fib m % 2 = 1) ∧
    (m % 12 = 6 → Nat.fib m % 16 = 8) ∧ (m % 6 ≠ 0 → Nat.fib m % 4 ≠ 0) := by
  have h1 := fibmod' m
  obtain ⟨t1, t2, t3, t4⟩ := tab (m % 24) (Nat.mod_lt _ (by norm_num))
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have := t1 (by omega); omega
  · have := t2 (by omega); omega
  · have := t3 (by omega); omega
  · have := t4 (by omega); omega

theorem pow9 (k : ℕ) : 9 ^ (2 * k + 1) % 16 = 9 := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 2 by ring, pow_add, show (9 : ℕ) ^ 2 = 81 by norm_num]
    omega

theorem oddpart (X : ℕ) (h : X % 16 = 9) :
    Odd ((X - 1) / 8) ∧ X - 1 = 2 ^ (0 + 3) * ((X - 1) / 8) := by
  refine ⟨Nat.odd_iff.mpr (by omega), ?_⟩
  rw [show (2 : ℕ) ^ (0 + 3) = 8 by norm_num]
  omega

theorem key : ∀ n : ℕ, 1 ≤ n → ∃ i u w : ℕ, Odd u ∧ Odd w ∧ 9 ^ n - 1 = 2 ^ (i + 3) * u ∧
    Nat.fib (6 * n) = 2 ^ (i + 3) * w := by
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih hn
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨k, hk⟩
  · subst hm
    obtain ⟨i, u, w, hu, hw, h9, hf⟩ := ih m (by omega) (by omega)
    have hpos : 0 < 9 ^ m := by positivity
    have hX : 9 ^ m = 2 ^ (i + 3) * u + 1 := by omega
    have p8 : Nat.fib (6 * m) % 8 = 0 := (fprop (6 * m)).1 (by omega)
    have p1 : Nat.fib (6 * m + 1) % 2 = 1 := (fprop (6 * m + 1)).2.1 (by omega)
    have mono : Nat.fib (6 * m) ≤ Nat.fib (6 * m + 1) := Nat.fib_le_fib_succ
    obtain ⟨q, hq, hqo⟩ : ∃ q, 2 * Nat.fib (6 * m + 1) - Nat.fib (6 * m) = 2 * q ∧ q % 2 = 1 :=
      ⟨(2 * Nat.fib (6 * m + 1) - Nat.fib (6 * m)) / 2, by omega, by omega⟩
    have hodd2 : Odd (2 ^ (i + 2) * u + 1) := ⟨2 ^ (i + 1) * u, by ring⟩
    refine ⟨i + 1, u * (2 ^ (i + 2) * u + 1), w * q, hu.mul hodd2,
      hw.mul (Nat.odd_iff.mpr hqo), ?_, ?_⟩
    · rw [pow_add, hX]
      apply Nat.sub_eq_of_eq_add
      ring
    · rw [show 6 * (m + m) = 2 * (6 * m) by ring, Nat.fib_two_mul, hq, hf]
      ring
  · subst hk
    obtain ⟨o1, o2⟩ := oddpart (9 ^ (2 * k + 1)) (pow9 k)
    have hf : Nat.fib (6 * (2 * k + 1)) % 16 = 8 := (fprop (6 * (2 * k + 1))).2.2.1 (by omega)
    refine ⟨0, (9 ^ (2 * k + 1) - 1) / 8, Nat.fib (6 * (2 * k + 1)) / 8, o1, ?_, o2, ?_⟩
    · rw [Nat.odd_iff]; omega
    · rw [show (2 : ℕ) ^ (0 + 3) = 8 by norm_num]; omega

end R363228

theorem OMA.solution : type_of% @OMA.S_oeis_a363228.main := by
  refine ⟨?_, ?_⟩
  · intro n hn
    obtain ⟨i, u, w, hu, hw, h9, hf⟩ := R363228.key n hn
    show OMA.S_oeis_a363228.exp4 (9 ^ n - 1) = OMA.S_oeis_a363228.exp4 (Nat.fib (6 * n))
    rw [h9, hf, R363228.exp4_pow _ _ hu, R363228.exp4_pow _ _ hw]
  · intro m hm h6
    have h4 : Nat.fib m % 4 ≠ 0 := (R363228.fprop m).2.2.2 (by omega)
    exact R363228.exp4_zero _ (by omega)
