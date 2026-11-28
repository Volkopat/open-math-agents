import OMAStatements.S_oeis_a074724
import Mathlib

/-!
Proof sketch. Write `n = 3 ^ e * m` with `3` not dividing `m`.
Fibonacci part: `F(3t) + 3 a^2 b = 2 a^3 + 3 a b^2` with `a = F t`, `b = F (t+1)`, so if `3 ∣ a`
then `F(3t) = a * (3 * d)` with `d ≡ b^2` mod 3, nonzero mod 3 since `F t` and `F (t+1)` are coprime.
Base: `F(4m) = 3 u` (since `F 4 = 3`) and `9 ∣ F(4m) ↔ 3 ∣ m` using `F(4m+12) = 89 F(4m) + 144 F(4m+1)`.
Induction on `e` gives `F(4 n) = 3 ^ (e+1) * u` with `3` not dividing `u`.
Sigma part: `σ(3^(e+1)) = 3 σ(3^e) + 1` and `2 σ(3^e) + 1 = 3^(e+1)`, plus multiplicativity.
-/

namespace R074724
open OMA.S_oeis_a074724 ArithmeticFunction

theorem alg {a b c X Y Z P Q R : ℕ} (h1 : Y = a * a + b * b) (h2 : Z = a * b + b * c)
    (h3 : Q = X * a + Y * b) (h4 : R = Y * a + Z * b) (h5 : R = P + Q) (h6 : Z = X + Y)
    (h7 : c = a + b) : P + 3 * a ^ 2 * b = 2 * a ^ 3 + 3 * a * b ^ 2 := by
  zify at *
  linear_combination -h5 + h4 - h3 + (a : ℤ) * h6 + ((b : ℤ) - a) * h2 + (2 * (a : ℤ) - b) * h1
    + ((b : ℤ) - a) * b * h7

theorem fib_three_mul (t : ℕ) :
    Nat.fib (3 * t) + 3 * Nat.fib t ^ 2 * Nat.fib (t + 1) =
      2 * Nat.fib t ^ 3 + 3 * Nat.fib t * Nat.fib (t + 1) ^ 2 := by
  have h1 : Nat.fib (2 * t + 1) = Nat.fib t * Nat.fib t + Nat.fib (t + 1) * Nat.fib (t + 1) := by
    rw [two_mul]; exact Nat.fib_add t t
  have h2 : Nat.fib (2 * t + 2) = Nat.fib t * Nat.fib (t + 1) + Nat.fib (t + 1) * Nat.fib (t + 2) := by
    rw [show 2 * t + 2 = t + (t + 1) + 1 by ring]; exact Nat.fib_add t (t + 1)
  have h3 : Nat.fib (3 * t + 1) = Nat.fib (2 * t) * Nat.fib t + Nat.fib (2 * t + 1) * Nat.fib (t + 1) := by
    rw [show 3 * t + 1 = 2 * t + t + 1 by ring]; exact Nat.fib_add (2 * t) t
  have h4 : Nat.fib (3 * t + 2) =
      Nat.fib (2 * t + 1) * Nat.fib t + Nat.fib (2 * t + 2) * Nat.fib (t + 1) := by
    rw [show 3 * t + 2 = (2 * t + 1) + t + 1 by ring]; exact Nat.fib_add (2 * t + 1) t
  exact alg h1 h2 h3 h4 Nat.fib_add_two Nat.fib_add_two Nat.fib_add_two

theorem step (t : ℕ) (h : 3 ∣ Nat.fib t) : ∃ d, ¬ 3 ∣ d ∧ Nat.fib (3 * t) = Nat.fib t * (3 * d) := by
  have hb : ¬ 3 ∣ Nat.fib (t + 1) := fun h' => by
    have := Nat.dvd_gcd h h'
    rw [(Nat.fib_coprime_fib_succ t).gcd_eq_one] at this
    omega
  obtain ⟨k, hk⟩ := h
  have hid := fib_three_mul t
  rw [hk] at hid ⊢
  generalize Nat.fib (t + 1) = b at hb hid
  generalize Nat.fib (3 * t) = P at hid ⊢
  have hle : 3 * (k * b) ≤ 6 * k ^ 2 + b ^ 2 := by
    have : (3 * (k * b) : ℤ) ≤ 6 * k ^ 2 + b ^ 2 := by
      nlinarith [sq_nonneg ((b : ℤ) - 3 * k), sq_nonneg (k : ℤ), sq_nonneg (b : ℤ)]
    exact_mod_cast this
  refine ⟨6 * k ^ 2 + b ^ 2 - 3 * (k * b), ?_, ?_⟩
  · intro hd
    have hb2 : ¬ 3 ∣ b ^ 2 := fun h2 => hb (Nat.prime_three.dvd_of_dvd_pow h2)
    omega
  · zify [hle] at hid ⊢
    linear_combination hid

theorem nine (m : ℕ) : 9 ∣ Nat.fib (4 * m) ↔ 3 ∣ m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.lt_or_ge m 3 with h | h
    · interval_cases m <;> norm_num
    · obtain ⟨j, rfl⟩ : ∃ j, m = j + 3 := ⟨m - 3, by omega⟩
      have h12 : Nat.fib (4 * (j + 3)) = Nat.fib (4 * j) * 89 + Nat.fib (4 * j + 1) * 144 := by
        rw [show 4 * (j + 3) = 4 * j + 11 + 1 by ring, Nat.fib_add (4 * j) 11]; norm_num
      have := ih j (by omega)
      rw [h12]; omega

theorem fib_val {m : ℕ} (hm : ¬ 3 ∣ m) (e : ℕ) :
    ∃ u, ¬ 3 ∣ u ∧ Nat.fib (4 * (3 ^ e * m)) = 3 ^ (e + 1) * u := by
  induction e with
  | zero =>
    have h4 : Nat.fib 4 = 3 := by norm_num
    obtain ⟨u, hu⟩ : 3 ∣ Nat.fib (4 * m) := h4 ▸ Nat.fib_dvd 4 (4 * m) (dvd_mul_right 4 m)
    exact ⟨u, fun h => hm ((nine m).1 (by omega)), by simpa using hu⟩
  | succ e ih =>
    obtain ⟨u, hu, hf⟩ := ih
    obtain ⟨d, hd, hf3⟩ := step _ ⟨3 ^ e * u, by rw [hf]; ring⟩
    refine ⟨u * d, fun h => ?_, ?_⟩
    · rcases (Nat.prime_three.dvd_mul).1 h with h | h <;> contradiction
    · rw [show 4 * (3 ^ (e + 1) * m) = 3 * (4 * (3 ^ e * m)) by ring, hf3, hf]; ring

theorem v3 (e u : ℕ) (hu : ¬ 3 ∣ u) : padicValNat 3 (3 ^ e * u) = e := by
  rw [padicValNat.mul (by positivity) (by rintro rfl; exact hu (dvd_zero 3)),
    padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hu, add_zero]

theorem sig (e : ℕ) :
    2 * sigma 1 (3 ^ e) + 1 = 3 ^ (e + 1) ∧ sigma 1 (3 ^ (e + 1)) = 3 * sigma 1 (3 ^ e) + 1 := by
  rw [sigma_one_apply_prime_pow Nat.prime_three, sigma_one_apply_prime_pow Nat.prime_three,
    Finset.sum_range_succ _ (e + 1)]
  have : 2 * (∑ k ∈ Finset.range (e + 1), 3 ^ k) + 1 = 3 ^ (e + 1) := by
    induction e with
    | zero => simp
    | succ e ih => rw [Finset.sum_range_succ, pow_succ 3 (e + 1)]; omega
  omega

end R074724

theorem OMA.solution : type_of% @OMA.S_oeis_a074724.main := by
  intro n hn
  obtain ⟨e, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : n ≠ 0) 3 (by norm_num)
  obtain ⟨u, hu, hf⟩ := R074724.fib_val hm e
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero 3)
  have hc : ∀ i, Nat.Coprime (3 ^ i) m := fun i =>
    Nat.Coprime.pow_left i ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hm)
  have h1 := (ArithmeticFunction.isMultiplicative_sigma (k := 1)).map_mul_of_coprime (hc e)
  have h2 := (ArithmeticFunction.isMultiplicative_sigma (k := 1)).map_mul_of_coprime (hc (e + 1))
  obtain ⟨hs1, hs2⟩ := R074724.sig e
  have hpos := ArithmeticFunction.sigma_pos 1 m hm0
  rw [show 3 * (3 ^ e * m) = 3 ^ (e + 1) * m by ring, h2, h1, hs2, OMA.S_oeis_a074724.a074724, hf,
    R074724.v3 _ _ hu, R074724.v3 _ _ hm]
  have e1 : (3 * ArithmeticFunction.sigma 1 (3 ^ e) + 1) * ArithmeticFunction.sigma 1 m =
      3 * (ArithmeticFunction.sigma 1 (3 ^ e) * ArithmeticFunction.sigma 1 m) + ArithmeticFunction.sigma 1 m := by ring
  have e2 : 3 ^ (e + 1) * ArithmeticFunction.sigma 1 m = 2 * (ArithmeticFunction.sigma 1 (3 ^ e) * ArithmeticFunction.sigma 1 m) + ArithmeticFunction.sigma 1 m := by
    rw [← hs1]; ring
  refine ⟨rfl, ?_, ?_⟩
  · omega
  · rw [e1, Nat.add_sub_cancel_left, e2]; omega
