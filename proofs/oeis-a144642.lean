import OMAStatements.S_oeis_a144642

-- Problem: A144642: Positive numbers that are not the sum of a triangular number, a square and a Fibonacci number.
-- Upstream: formal-conjectures statements/oeis-a144642.lean:0 (declaration OMA.S_oeis_a144642.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Idea: n = 3970902 = a(1) is a counterexample. If n = x^2 + y(y+1)/2 + F then
-- 8x^2 + (2y+1)^2 = 8(n - F) + 1 =: M. For each of the 34 indices m with F = fib m <= n, M has a
-- prime factor p with p = 5 or 7 mod 8 that divides M exactly once. Since -2 is not a square
-- mod p (ZMod.exists_sq_eq_neg_two_iff), p | 8x^2 + z^2 forces p | x and p | z, so p^2 | M,
-- which is impossible.

namespace H01A144642

theorem key (p x z : ℕ) (hp : p.Prime) (h8 : p % 8 = 5 ∨ p % 8 = 7)
    (h : p ∣ 8 * x ^ 2 + z ^ 2) : p ∣ x := by
  have hp2 : p ≠ 2 := by
    rintro rfl
    omega
  have hfact : Fact p.Prime := ⟨hp⟩
  by_contra hx
  have hx0 : (x : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact hx
  have h20 : (2 : ZMod p) ≠ 0 := by
    intro h2
    have h2' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h2
    rw [ZMod.natCast_eq_zero_iff] at h2'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2')
  have hs : 8 * (x : ZMod p) ^ 2 + (z : ZMod p) ^ 2 = 0 := by
    have h' := (ZMod.natCast_eq_zero_iff (8 * x ^ 2 + z ^ 2) p).mpr h
    push_cast at h'
    exact h'
  have hsq : IsSquare (-2 : ZMod p) := by
    refine ⟨(z : ZMod p) / (2 * x), ?_⟩
    rw [div_mul_div_comm, eq_div_iff (mul_ne_zero (mul_ne_zero h20 hx0) (mul_ne_zero h20 hx0))]
    linear_combination (-1 : ZMod p) * hs
  rw [ZMod.exists_sq_eq_neg_two_iff hp2] at hsq
  omega

theorem obstruct (p m x z : ℕ) (hp : p.Prime) (h8 : p % 8 = 5 ∨ p % 8 = 7) (hm : ¬ p ∣ m)
    (h : 8 * x ^ 2 + z ^ 2 = p * m) : False := by
  have hd : p ∣ 8 * x ^ 2 + z ^ 2 := ⟨m, h⟩
  have hx := key p x z hp h8 hd
  have hz : p ∣ z := by
    have h1 : p ∣ 8 * x ^ 2 := Dvd.dvd.mul_left (dvd_pow hx (by norm_num : (2 : ℕ) ≠ 0)) 8
    have h2 : p ∣ z ^ 2 := (Nat.dvd_add_right h1).mp hd
    exact hp.dvd_of_dvd_pow h2
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hz
  have e : p * (p * (8 * a ^ 2 + b ^ 2)) = p * m := by
    rw [← h]
    ring
  have e2 := Nat.eq_of_mul_eq_mul_left hp.pos e
  exact hm ⟨8 * a ^ 2 + b ^ 2, e2.symm⟩

theorem rep (n x y m : ℕ) (h : n = x ^ 2 + y * (y + 1) / 2 + Nat.fib m) :
    8 * x ^ 2 + (2 * y + 1) ^ 2 + 8 * Nat.fib m = 8 * n + 1 := by
  have ht : 2 * (y * (y + 1) / 2) = y * (y + 1) :=
    Nat.two_mul_div_two_of_even (Nat.even_mul_succ_self y)
  have e1 : (2 * y + 1) ^ 2 = 4 * (y * (y + 1)) + 1 := by ring
  omega

theorem fib_le (m : ℕ) (hm : Nat.fib m ≤ 3970902) : m ≤ 33 := by
  by_contra h
  have h1 : Nat.fib 34 ≤ Nat.fib m := Nat.fib_mono (by omega)
  have h2 : Nat.fib 34 = 5702887 := by norm_num
  omega

end H01A144642

open H01A144642 in
theorem OMA.solution : type_of% @OMA.S_oeis_a144642.main := by
  intro H
  obtain ⟨x, y, m, h⟩ := H 3970902 (by norm_num)
  have hr := rep 3970902 x y m h
  have hfm : Nat.fib m ≤ 3970902 := by omega
  have hm := fib_le m hfm
  clear h hfm H
  interval_cases m
  · rw [show Nat.fib 0 = 0 by norm_num] at hr
    exact obstruct 701 45317 x (2 * y + 1) (by norm_num) (by decide) (by decide) (by omega)
  · rw [show Nat.fib 1 = 1 by norm_num] at hr
    exact obstruct 23 1381183 x (2 * y + 1) (by norm_num) (by decide) (by decide) (by omega)
  · rw [show Nat.fib 2 = 1 by norm_num] at hr
    exact obstruct 23 1381183 x (2 * y + 1) (by norm_num) (by decide) (by decide) (by omega)
  · rw [show Nat.fib 3 = 2 by norm_num] at hr
    exact obstruct 37 858573 x (2 * y + 1) (by norm_num) (by decide) (by decide) (by omega)
  · rw [show Nat.fib 4 = 3 by norm_num] at hr
    exact obstruct 53 599381 x (2 * y + 1) (by norm_num) (by decide) (by decide) (by omega)
  · rw [show Nat.fib 5 = 5 by norm_num] at hr
    exact obstruct 13 2443629 x (2 * y + 1) (by norm_num) (by decide) (by decide) (by omega)
  · rw [show Nat.fib 6 = 8 by norm_num] at hr
    exact obstruct 61 520773 x (2 * y + 1) (by norm_num) (by decide) (by decide) (by omega)
  · rw [show Nat.fib 7 = 13 by norm_num] at hr
    exact obstruct 7 4538159 x (2 * y + 1) (by norm_num) (by decide) (by decide) (by omega)
  · rw [show Nat.fib 8 = 21 by norm_num] at hr
    exact obstruct 461 68909 x (2 * y + 1) (by norm_num) (by decide) (by decide) (by omega)
  · rw [show Nat.fib 9 = 34 by norm_num] at hr
    exact obstruct 5 6353389 x (2 * y + 1) (by norm_num) (by decide) (by decide) (by omega)
  · rw [show Nat.fib 10 = 55 by norm_num] at hr
    exact obstruct 7 4538111 x (2 * y + 1) (by norm_num) (by decide) (by decide) (by omega)
  · rw [show Nat.fib 11 = 89 by norm_num] at hr
    exact obstruct 5 6353301 x (2 * y + 1) (by norm_num) (by decide) (by decide) (by omega)
  · rw [show Nat.fib 12 = 144 by norm_num] at hr
    exact obstruct 5 6353213 x (2 * y + 1) (by norm_num) (by decide) (by decide) (by omega)
  · rw [show Nat.fib 13 = 233 by norm_num] at hr
    exact obstruct 29 1095357 x (2 * y + 1) (by norm_num) (by decide) (by decide) (by omega)
  · rw [show Nat.fib 14 = 377 by norm_num] at hr
    exact obstruct 30869 1029 x (2 * y + 1) (by norm_num) (by decide) (by decide) (by omega)
  · rw [show Nat.fib 15 = 610 by norm_num] at hr
    exact obstruct 29 1095253 x (2 * y + 1) (by norm_num) (by decide) (by decide) (by omega)
  · rw [show Nat.fib 16 = 987 by norm_num] at hr
    exact obstruct 29 1095149 x (2 * y + 1) (by norm_num) (by decide) (by decide) (by omega)
  · rw [show Nat.fib 17 = 1597 by norm_num] at hr
    exact obstruct 2543 12487 x (2 * y + 1) (by norm_num) (by decide) (by decide) (by omega)
  · rw [show Nat.fib 18 = 2584 by norm_num] at hr
    exact obstruct 5 6349309 x (2 * y + 1) (by norm_num) (by decide) (by decide) (by omega)
  · rw [show Nat.fib 19 = 4181 by norm_num] at hr
    exact obstruct 733 43293 x (2 * y + 1) (by norm_num) (by decide) (by decide) (by omega)
  · rw [show Nat.fib 20 = 6765 by norm_num] at hr
    exact obstruct 13 2439469 x (2 * y + 1) (by norm_num) (by decide) (by decide) (by omega)
  · rw [show Nat.fib 21 = 10946 by norm_num] at hr
    exact obstruct 151 209799 x (2 * y + 1) (by norm_num) (by decide) (by decide) (by omega)
  · rw [show Nat.fib 22 = 17711 by norm_num] at hr
    exact obstruct 13 2432733 x (2 * y + 1) (by norm_num) (by decide) (by decide) (by omega)
  · rw [show Nat.fib 23 = 28657 by norm_num] at hr
    exact obstruct 7 4505423 x (2 * y + 1) (by norm_num) (by decide) (by decide) (by omega)
  · rw [show Nat.fib 24 = 46368 by norm_num] at hr
    exact obstruct 31 1012783 x (2 * y + 1) (by norm_num) (by decide) (by decide) (by omega)
  · rw [show Nat.fib 25 = 75025 by norm_num] at hr
    exact obstruct 7 4452431 x (2 * y + 1) (by norm_num) (by decide) (by decide) (by omega)
  · rw [show Nat.fib 26 = 121393 by norm_num] at hr
    exact obstruct 7 4399439 x (2 * y + 1) (by norm_num) (by decide) (by decide) (by omega)
  · rw [show Nat.fib 27 = 196418 by norm_num] at hr
    exact obstruct 29 1041237 x (2 * y + 1) (by norm_num) (by decide) (by decide) (by omega)
  · rw [show Nat.fib 28 = 317811 by norm_num] at hr
    exact obstruct 2879 10151 x (2 * y + 1) (by norm_num) (by decide) (by decide) (by omega)
  · rw [show Nat.fib 29 = 514229 by norm_num] at hr
    exact obstruct 5 5530677 x (2 * y + 1) (by norm_num) (by decide) (by decide) (by omega)
  · rw [show Nat.fib 30 = 832040 by norm_num] at hr
    exact obstruct 7 3587271 x (2 * y + 1) (by norm_num) (by decide) (by decide) (by omega)
  · rw [show Nat.fib 31 = 1346269 by norm_num] at hr
    exact obstruct 5 4199413 x (2 * y + 1) (by norm_num) (by decide) (by decide) (by omega)
  · rw [show Nat.fib 32 = 2178309 by norm_num] at hr
    exact obstruct 5 2868149 x (2 * y + 1) (by norm_num) (by decide) (by decide) (by omega)
  · rw [show Nat.fib 33 = 3524578 by norm_num] at hr
    exact obstruct 13 274661 x (2 * y + 1) (by norm_num) (by decide) (by decide) (by omega)
