import OMAReductions.R_Goormaghtigh_goormaghtigh_conjecture_R1
import Mathlib

-- Reduction Goormaghtigh.goormaghtigh_conjecture.R1.H2.R1 of step Goormaghtigh.goormaghtigh_conjecture.R1.H2
-- Credit: @rickmanelius
-- The step asks that x^2 + x + 1 = 1 + y + ... + y^(n-1) has no solution with n even (both known
-- solutions, 31 and 8191, have n odd). Write n = 2t and N = x^2 + x + 1. main proves, for a solution:
--   y is even (for odd y the right side is a sum of 2t odd terms, but N is odd);
--   N = (y + 1) * repunit (y^2) t = repunit y t * (y^t + 1);
--   every prime p dividing N is 3 or 1 mod 3 (x^3 = 1 mod p and Fermat), and 9 does not divide N,
--   so every divisor of N prime to 3 is 1 mod 3; hence y is not 1 mod 3 (y + 1 would be 2 mod 3);
--   y < x, x (x + 1) = y + y^2 mod y^3 (N = 1 + y + y^2 mod y^3), and N = n mod y - 1;
--   (x - y)(x + y + 1) = y^3 repunit y (n - 3) and the gcd of the two factors divides 2y + 1, so
--   y = a b with a, b coprime, a^3 dividing x - y and b^3 dividing x + y + 1;
--   n = 4 is impossible: then (x - y)(x + y + 1) = y^3, so x - y = a^3, x + y + 1 = b^3 and
--   b^3 = a^3 + 2 a b + 1, which has no solution with a at least 1 (this is the 3-descent on the
--   elliptic curve x^2 + x = y^3 + y^2 + y of conductor 19);
--   Jacobi symbol obstructions in the style of Lebesgue: modulo a cyclotomic value Phi_k(y) the
--   right side is 1 + y (or 2y - 1), so 4y + 1 (or 8y - 7) is a square there, and reciprocity
--   (4y + 1 = 1 mod 4) moves the symbol to a fixed modulus, because 4^deg Phi_k(y) is constant
--   modulo 4y + 1: t odd (k = 4): J(4y + 1 | 17) is not -1, so y mod 17 is in
--   {0, 2, 3, 4, 5, 6, 8, 12, 13}; t = 1 mod 3 (k = 3): y mod 13 is in {0, 2, 3, 4, 6, 7, 12};
--   t = 1 mod 3 (k = 6): y mod 7 is in {0, 2, 5, 6} (for y = 18q + 2 after taking the factor 3
--   out of Phi_6(y) and the factor 9 out of 4y + 1 = 9(8q + 1)); t = 2 mod 3 (k = 6, 8y - 7, 57)
--   with 3 | y: y mod 19 is in {0, 5, 6, 8, 9, 12, 13, 14, 15, 17}; t = 1 mod 6 (k = 12):
--   J(4y + 1 | 241) is not -1; and for even t, y^2 + 1 divides N;
--   if y = 2 mod 3: 3 divides y + 1 and 9 does not, so (y + 1)/3 = 1 mod 3 and y = 2 mod 9;
--     for even t, y^t + 1 = 2 mod 3 would divide N, so t is odd; for every d dividing t,
--     repunit (y^2) d = d mod 3 divides repunit (y^2) t, which is prime to 3, so d = 1 mod 3:
--     every divisor of t is 1 mod 6 (n = 2 mod 12, n at least 14);
--     y - 1 is not a square: (2 y^t)^2 - (y - 1)(2x + 1)^2 = 3y + 1, and for y - 1 = s^2 the left
--     side factors with 2 y^t + s (2x + 1) at most 3y + 1, which is below 2 y^2 (this covers y = 2,
--     where the equation is x^2 + x + 2 = 2^n of Ramanujan and Nagell), so y is at least 20.
-- What remains is split by y mod 3, each case keeping the equation and the proved constraints:
-- H1: y = 0 mod 6 and n at least 6 (every prime factor of N is then 1 mod 3);
-- H2: y = 2 mod 18, every divisor of t is 1 mod 6, n at least 14 (3 exactly divides N).
-- Yuan (J. Number Theory 112, 2005) settled n odd; for n even no solution is known.

namespace OMA.R_Goormaghtigh_goormaghtigh_conjecture_R1_H2_R1

/-- Case `y ≡ 0 (mod 3)`: no solution of `x^2 + x + 1 = repunit y (2 t)` with `t ≥ 3` (that is
`n ≥ 6`), `y ≡ 0 (mod 6)`, `y < x`, `x ≢ 1 (mod 3)`, every prime factor of `x^2 + x + 1` congruent
to `1 (mod 3)`, `x (x + 1) ≡ y + y^2 (mod y^3)`, `y = a b` with `a, b` coprime, `a^3 ∣ x - y` and
`b^3 ∣ x + y + 1`, `x^2 + x + 1 ≡ 2 t (mod y - 1)`, `y^2 + 1 ∣ x^2 + x + 1` when `t` is even,
`4 y + 1` a square modulo `17` (`y mod 17` in `{0, 2, 3, 4, 5, 6, 8, 12, 13}`) when `t` is odd,
`y mod 7` in `{0, 2, 5, 6}` and `y mod 13` in `{0, 2, 3, 4, 6, 7, 12}` when `t ≡ 1 (mod 3)`,
`y mod 19` in `{0, 5, 6, 8, 9, 12, 13, 14, 15, 17}` when `t ≡ 2 (mod 3)`, and `J(4 y + 1 | 241) ≠ -1`
when `t ≡ 1 (mod 6)`. -/
def H1 : Prop := ∀ x y t : ℕ, 2 ≤ x → 3 ≤ t → 6 ≤ y → y % 6 = 0 → y < x → x % 3 ≠ 1 →
  (∀ p : ℕ, p.Prime → p ∣ x ^ 2 + x + 1 → p % 3 = 1) →
  x * (x + 1) % y ^ 3 = y + y ^ 2 →
  (∃ a b : ℕ, a * b = y ∧ Nat.Coprime a b ∧ a ^ 3 ∣ x - y ∧ b ^ 3 ∣ x + y + 1) →
  (x ^ 2 + x + 1) % (y - 1) = 2 * t % (y - 1) →
  (t % 2 = 0 → y ^ 2 + 1 ∣ x ^ 2 + x + 1) →
  (t % 2 = 1 → y % 17 ∈ ({0, 2, 3, 4, 5, 6, 8, 12, 13} : Finset ℕ)) →
  (t % 3 = 1 → y % 7 ∈ ({0, 2, 5, 6} : Finset ℕ) ∧
    y % 13 ∈ ({0, 2, 3, 4, 6, 7, 12} : Finset ℕ)) →
  (t % 3 = 2 → y % 19 ∈ ({0, 5, 6, 8, 9, 12, 13, 14, 15, 17} : Finset ℕ)) →
  (t % 6 = 1 → jacobiSym (4 * y + 1) 241 ≠ -1) →
  Goormaghtigh.repunit x 3 ≠ Goormaghtigh.repunit y (2 * t)

/-- Case `y ≡ 2 (mod 3)`: no solution of `x^2 + x + 1 = repunit y (2 t)` with `t ≡ 1 (mod 6)`,
`t ≥ 7` (so `n ≡ 2 (mod 12)`, `n ≥ 14`), every divisor of `t` congruent to `1 (mod 6)`,
`y ≡ 2 (mod 18)`, `y ≥ 20`, `y - 1` not a square, `y < x`,
`x ≡ 1 (mod 3)`, every prime factor of `x^2 + x + 1` equal to `3` or congruent to `1 (mod 3)`,
`9 ∤ x^2 + x + 1`, `x (x + 1) ≡ y + y^2 (mod y^3)`, `y = a b` with `a, b` coprime, `a^3 ∣ x - y`
and `b^3 ∣ x + y + 1`, `x^2 + x + 1 ≡ 2 t (mod y - 1)`, `y mod 17` in
`{0, 2, 3, 4, 5, 6, 8, 12, 13}`, `y mod 13` in `{0, 2, 3, 4, 6, 7, 12}`, `y mod 7` in
`{0, 2, 5, 6}`, and `J(4 y + 1 | 241) ≠ -1`. -/
def H2 : Prop := ∀ x y t : ℕ, 2 ≤ x → 7 ≤ t → 20 ≤ y → y % 18 = 2 → t % 6 = 1 →
  (∀ d : ℕ, d ∣ t → d % 6 = 1) → y < x →
  x % 3 = 1 → ¬ IsSquare (y - 1) →
  (∀ p : ℕ, p.Prime → p ∣ x ^ 2 + x + 1 → p = 3 ∨ p % 3 = 1) → ¬ 9 ∣ x ^ 2 + x + 1 →
  x * (x + 1) % y ^ 3 = y + y ^ 2 →
  (∃ a b : ℕ, a * b = y ∧ Nat.Coprime a b ∧ a ^ 3 ∣ x - y ∧ b ^ 3 ∣ x + y + 1) →
  (x ^ 2 + x + 1) % (y - 1) = 2 * t % (y - 1) →
  y % 17 ∈ ({0, 2, 3, 4, 5, 6, 8, 12, 13} : Finset ℕ) →
  y % 13 ∈ ({0, 2, 3, 4, 6, 7, 12} : Finset ℕ) →
  y % 7 ∈ ({0, 2, 5, 6} : Finset ℕ) →
  jacobiSym (4 * y + 1) 241 ≠ -1 →
  Goormaghtigh.repunit x 3 ≠ Goormaghtigh.repunit y (2 * t)

open Goormaghtigh

lemma repunit_succ (b n : ℕ) : repunit b (n + 1) = repunit b n + b ^ n := by
  unfold repunit
  rw [Finset.sum_range_succ]

lemma repunit_add (b m n : ℕ) : repunit b (m + n) = repunit b m + b ^ m * repunit b n := by
  unfold repunit
  rw [Finset.sum_range_add, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [pow_add]

lemma repunit_three (x : ℕ) : repunit x 3 = x ^ 2 + x + 1 := by
  unfold repunit
  simp [Finset.sum_range_succ]
  ring

lemma repunit_succ' (b n : ℕ) : repunit b (n + 1) = 1 + b * repunit b n := by
  have h := repunit_add b 1 n
  rw [add_comm 1 n] at h
  rw [h]
  simp [repunit]

/-- `repunit y (2 t) = (y + 1) * repunit (y ^ 2) t`. -/
lemma repunit_two_mul (y t : ℕ) : repunit y (t + t) = (y + 1) * repunit (y ^ 2) t := by
  induction t with
  | zero => simp [repunit]
  | succ t ih =>
    rw [show t + 1 + (t + 1) = (t + t) + 1 + 1 by ring, repunit_succ, repunit_succ, ih, repunit_succ]
    ring

/-- `repunit b (d k) = repunit b d * repunit (b ^ d) k`. -/
lemma repunit_mul (b d k : ℕ) : repunit b (d * k) = repunit b d * repunit (b ^ d) k := by
  induction k with
  | zero => simp [repunit]
  | succ k ih =>
    rw [Nat.mul_succ, repunit_add, ih, repunit_succ, ← pow_mul]
    ring

/-- `repunit y (2 t) = repunit y t * (y ^ t + 1)`. -/
lemma repunit_double (y t : ℕ) : repunit y (t + t) = repunit y t * (y ^ t + 1) := by
  rw [repunit_add]
  ring

/-- `repunit b n ≡ n (mod m)` when `b ≡ 1 (mod m)`. -/
lemma repunit_mod_of_one (b n m : ℕ) (hb : b % m = 1 % m) : repunit b n % m = n % m := by
  induction n with
  | zero => simp [repunit]
  | succ n ih =>
    rw [repunit_succ, Nat.add_mod, ih, Nat.pow_mod, hb, ← Nat.pow_mod, one_pow, ← Nat.add_mod]

/-- `(y - 1) * repunit y n + 1 = y ^ n`, written with `y = c + 1`. -/
lemma geom_identity (c n : ℕ) : c * repunit (c + 1) n + 1 = (c + 1) ^ n := by
  induction n with
  | zero => simp [repunit]
  | succ n ih =>
    rw [repunit_succ, pow_succ, ← ih]
    ring

lemma three_dvd_iff (x : ℕ) : 3 ∣ x ^ 2 + x + 1 ↔ x % 3 = 1 := by
  rw [← ZMod.natCast_eq_zero_iff, ← ZMod.val_natCast 3 x]
  push_cast
  generalize (x : ZMod 3) = r
  revert r
  decide

lemma not_nine_dvd (x : ℕ) : ¬ 9 ∣ x ^ 2 + x + 1 := by
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  generalize (x : ZMod 9) = r
  revert r
  decide

lemma odd_x2x1 (x : ℕ) : (x ^ 2 + x + 1) % 2 = 1 := by
  rw [← ZMod.val_natCast]
  push_cast
  generalize (x : ZMod 2) = r
  revert r
  decide

/-- A prime factor of `x ^ 2 + x + 1` is `3` or `1 (mod 3)`: `x ^ 3 = 1` and Fermat. -/
lemma prime_dvd_x2x1 (x p : ℕ) (hp : p.Prime) (h : p ∣ x ^ 2 + x + 1) :
    p = 3 ∨ p % 3 = 1 := by
  have := Fact.mk hp
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨h3, h1⟩ := hcon
  have h2 : p % 3 = 2 := by
    have hlt := Nat.mod_lt p (show 3 > 0 by norm_num)
    interval_cases hr : p % 3
    · exfalso
      have h3p : 3 ∣ p := Nat.dvd_of_mod_eq_zero hr
      exact h3 ((Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp h3p).symm
    · exact absurd rfl h1
    · rfl
  have hx : (x : ZMod p) ^ 2 + x + 1 = 0 := by
    have := (ZMod.natCast_eq_zero_iff (x ^ 2 + x + 1) p).mpr h
    push_cast at this
    exact this
  have hx3 : (x : ZMod p) ^ 3 = 1 := by
    have e : (x : ZMod p) ^ 3 - 1 = ((x : ZMod p) - 1) * ((x : ZMod p) ^ 2 + x + 1) := by ring
    rw [hx, mul_zero] at e
    exact sub_eq_zero.mp e
  have hx0 : (x : ZMod p) ≠ 0 := by
    intro h0
    rw [h0] at hx
    simp at hx
  have hferm := ZMod.pow_card_sub_one_eq_one hx0
  obtain ⟨k, hk⟩ : ∃ k, p - 1 = 3 * k + 1 := ⟨p / 3, by omega⟩
  rw [hk, pow_succ, pow_mul, hx3, one_pow, one_mul] at hferm
  rw [hferm] at hx
  have h3z : ((3 : ℕ) : ZMod p) = 0 := by
    rw [← hx]
    norm_num
  rw [ZMod.natCast_eq_zero_iff] at h3z
  exact h3 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h3z)

/-- A divisor of `x ^ 2 + x + 1` prime to `3` is `1 (mod 3)`. -/
lemma dvd_x2x1_mod_three (x d : ℕ) (hd : d ∣ x ^ 2 + x + 1) (h3 : ¬ 3 ∣ d) : d % 3 = 1 := by
  induction d using Nat.recOnMul with
  | zero =>
    exfalso
    rw [zero_dvd_iff] at hd
    omega
  | one => rfl
  | prime p hp =>
    rcases prime_dvd_x2x1 x p hp hd with h | h
    · subst h
      exact absurd (dvd_refl 3) h3
    · exact h
  | mul a b iha ihb =>
    have ha : a ∣ x ^ 2 + x + 1 := Dvd.dvd.trans (dvd_mul_right a b) hd
    have hb : b ∣ x ^ 2 + x + 1 := Dvd.dvd.trans (dvd_mul_left b a) hd
    have h3a : ¬ 3 ∣ a := fun h => h3 (Dvd.dvd.mul_right h b)
    have h3b : ¬ 3 ∣ b := fun h => h3 (Dvd.dvd.mul_left h a)
    rw [Nat.mul_mod, iha ha h3a, ihb hb h3b]

/-- `b ^ 3 = a ^ 3 + 2 a b + 1` has no solution with `a ≥ 1`. -/
lemma cube_contra (a b : ℕ) (ha : 1 ≤ a) (h : b ^ 3 = 2 * (a * b) + a ^ 3 + 1) : False := by
  have hab : a < b := by
    by_contra hc
    rw [not_lt] at hc
    have := Nat.pow_le_pow_left hc 3
    nlinarith
  obtain ⟨e, rfl⟩ : ∃ e, b = a + 1 + e := ⟨b - a - 1, by omega⟩
  have expand : (a + 1 + e) ^ 3 = a ^ 3 + 2 * (a * (a + 1 + e)) + 1 +
      (a ^ 2 * (1 + 3 * e) + a * (1 + e) * (1 + 3 * e) + e * (3 + 3 * e + e ^ 2)) := by ring
  have hpos : 0 < a ^ 2 * (1 + 3 * e) := by positivity
  omega

/-- `n = 4` is impossible: `(x - y) (x + y + 1) = y ^ 3` with coprime factors. -/
lemma no_four (x y : ℕ) (hyx : y < x) (h : x ^ 2 + x + 1 = repunit y (2 + 2)) : False := by
  have e : repunit y (2 + 2) = 1 + y + y ^ 2 + y ^ 3 := by
    simp only [repunit, Finset.sum_range_succ, Finset.sum_range_zero]
    ring
  rw [e] at h
  obtain ⟨d, rfl⟩ : ∃ d, x = y + d := ⟨x - y, by omega⟩
  have hd : 1 ≤ d := by omega
  have key : d * (2 * y + d + 1) = y ^ 3 := by nlinarith [h]
  have hcop : Nat.gcd d (2 * y + d + 1) = 1 := by
    by_contra hg
    obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hg
    have hpd : p ∣ d := hpg.trans (Nat.gcd_dvd_left _ _)
    have hpe : p ∣ 2 * y + d + 1 := hpg.trans (Nat.gcd_dvd_right _ _)
    have hpy3 : p ∣ y ^ 3 := key ▸ (Dvd.dvd.mul_right hpd _)
    have hpy : p ∣ y := hp.dvd_of_dvd_pow hpy3
    have h2 : p ∣ 2 * y + d := Dvd.dvd.add (Dvd.dvd.mul_left hpy 2) hpd
    have h1 : p ∣ 1 := (Nat.dvd_add_right h2).mp hpe
    exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
  have hu : IsUnit (gcd d (2 * y + d + 1)) := Nat.isUnit_iff.mpr hcop
  obtain ⟨a, ha⟩ := exists_eq_pow_of_mul_eq_pow hu key
  have hcop' : Nat.gcd (2 * y + d + 1) d = 1 := by rw [Nat.gcd_comm]; exact hcop
  have hu' : IsUnit (gcd (2 * y + d + 1) d) := Nat.isUnit_iff.mpr hcop'
  obtain ⟨b, hb⟩ := exists_eq_pow_of_mul_eq_pow hu' (by rw [mul_comm]; exact key)
  have hab : a * b = y := by
    have h3 : (a * b) ^ 3 = y ^ 3 := by rw [mul_pow, ← ha, ← hb, key]
    exact Nat.pow_left_injective (by norm_num) h3
  have ha1 : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with h0 | h0
    · rw [h0] at ha
      simp at ha
      omega
    · exact h0
  have hb3 : b ^ 3 = 2 * (a * b) + a ^ 3 + 1 := by rw [← hb, ← ha, hab]
  exact cube_contra a b ha1 hb3

/-- `y - 1` is not a square: `(2 y ^ t) ^ 2 - (y - 1) (2 x + 1) ^ 2 = 3 y + 1` would factor. -/
lemma not_square (x y t : ℕ) (hy : 2 ≤ y) (ht : 2 ≤ t) (h : x ^ 2 + x + 1 = repunit y (t + t)) :
    ¬ IsSquare (y - 1) := by
  rintro ⟨s, hs⟩
  obtain ⟨c, rfl⟩ : ∃ c, y = c + 1 := ⟨y - 1, by omega⟩
  rw [Nat.add_sub_cancel] at hs
  have hg := geom_identity c (t + t)
  rw [← h] at hg
  subst hs
  have key : (2 * (s * s + 1) ^ t) ^ 2 = (s * (2 * x + 1)) ^ 2 + 3 * (s * s + 1) + 1 := by
    have e : (2 * (s * s + 1) ^ t) ^ 2 = 4 * (s * s + 1) ^ (t + t) := by ring
    rw [e, ← hg]
    ring
  have hY : 2 ≤ s * s + 1 := hy
  have hA : 2 * (s * s + 1) ^ 2 ≤ 2 * (s * s + 1) ^ t := by
    have := Nat.pow_le_pow_right (by omega : 0 < s * s + 1) ht
    omega
  generalize 2 * (s * s + 1) ^ t = A at key hA
  generalize s * (2 * x + 1) = B at key
  generalize s * s + 1 = Y at key hA hY
  have hAB : B < A := by
    by_contra hc
    rw [not_lt] at hc
    have := Nat.pow_le_pow_left hc 2
    omega
  nlinarith

/-- From `(x - y) (x + y + 1) = y ^ 3 M`: the gcd of the two factors divides `2 y + 1`, so it is
prime to `y`, and `y ^ 3` splits as `a ^ 3 * b ^ 3` with `a ^ 3 ∣ x - y`, `b ^ 3 ∣ x + y + 1`. -/
lemma cube_split (x y M : ℕ) (hyx : y < x) (h : (x - y) * (x + y + 1) = y ^ 3 * M) :
    ∃ a b : ℕ, a * b = y ∧ Nat.Coprime a b ∧ a ^ 3 ∣ x - y ∧ b ^ 3 ∣ x + y + 1 := by
  have hg : Nat.Coprime (Nat.gcd (x - y) (x + y + 1)) y := by
    apply Nat.coprime_of_dvd
    intro p hp hpg hpy
    have h1 : p ∣ x - y := hpg.trans (Nat.gcd_dvd_left _ _)
    have h2 : p ∣ x + y + 1 := hpg.trans (Nat.gcd_dvd_right _ _)
    have h3 : p ∣ (x + y + 1) - (x - y) := Nat.dvd_sub h2 h1
    rw [show x + y + 1 - (x - y) = 2 * y + 1 by omega] at h3
    have h4 : p ∣ 1 := (Nat.dvd_add_right (Dvd.dvd.mul_left hpy 2)).mp h3
    exact hp.one_lt.ne' (Nat.dvd_one.mp h4)
  have hg3 : Nat.Coprime (Nat.gcd (x - y) (x + y + 1)) (y ^ 3) := Nat.Coprime.pow_right 3 hg
  have huv : Nat.Coprime (Nat.gcd (y ^ 3) (x - y)) (Nat.gcd (y ^ 3) (x + y + 1)) := by
    have h1 : Nat.gcd (Nat.gcd (y ^ 3) (x - y)) (Nat.gcd (y ^ 3) (x + y + 1)) ∣ x - y :=
      (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _)
    have h2 : Nat.gcd (Nat.gcd (y ^ 3) (x - y)) (Nat.gcd (y ^ 3) (x + y + 1)) ∣ x + y + 1 :=
      (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right _ _)
    have h3 : Nat.gcd (Nat.gcd (y ^ 3) (x - y)) (Nat.gcd (y ^ 3) (x + y + 1)) ∣ y ^ 3 :=
      (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _)
    have h4 := Nat.dvd_gcd (Nat.dvd_gcd h1 h2) h3
    rw [Nat.Coprime.gcd_eq_one hg3] at h4
    exact Nat.eq_one_of_dvd_one h4
  have hprod : Nat.gcd (y ^ 3) (x - y) * Nat.gcd (y ^ 3) (x + y + 1) = y ^ 3 := by
    apply Nat.dvd_antisymm
    · exact Nat.Coprime.mul_dvd_of_dvd_of_dvd huv (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_left _ _)
    · have h1 : y ^ 3 ∣ (x - y) * (x + y + 1) := ⟨M, h⟩
      have h2 : Nat.gcd (y ^ 3) ((x - y) * (x + y + 1)) = y ^ 3 := Nat.gcd_eq_left h1
      exact (dvd_of_eq h2.symm).trans (gcd_mul_dvd_mul_gcd (y ^ 3 : ℕ) (x - y) (x + y + 1))
  obtain ⟨a, ha⟩ := exists_eq_pow_of_mul_eq_pow (Nat.isUnit_iff.mpr huv) hprod
  obtain ⟨b, hb⟩ := exists_eq_pow_of_mul_eq_pow (Nat.isUnit_iff.mpr huv.symm)
    (by rw [mul_comm]; exact hprod)
  refine ⟨a, b, ?_, ?_, ?_, ?_⟩
  · have h3 : (a * b) ^ 3 = y ^ 3 := by rw [mul_pow, ← ha, ← hb, hprod]
    exact Nat.pow_left_injective (by norm_num) h3
  · rw [ha, hb] at huv
    exact (Nat.coprime_pow_left_iff (by norm_num) _ _).mp
      ((Nat.coprime_pow_right_iff (by norm_num) _ _).mp huv)
  · rw [← ha]
    exact Nat.gcd_dvd_right _ _
  · rw [← hb]
    exact Nat.gcd_dvd_right _ _

/-- Modulo `y ^ 2 + 1` (where `y ^ 2 = -1`), `repunit y (4 s) = 0`. -/
lemma repunit_four_mul_mod (y s : ℕ) : ((repunit y (4 * s) : ℕ) : ZMod (y ^ 2 + 1)) = 0 := by
  have hy2 : (y : ZMod (y ^ 2 + 1)) ^ 2 + 1 = 0 := by
    have : ((y ^ 2 + 1 : ℕ) : ZMod (y ^ 2 + 1)) = 0 := ZMod.natCast_self _
    push_cast at this
    exact this
  induction s with
  | zero => simp [repunit]
  | succ s ih =>
    rw [show 4 * (s + 1) = 4 * s + 1 + 1 + 1 + 1 by ring]
    rw [repunit_succ, repunit_succ, repunit_succ, repunit_succ]
    push_cast
    rw [ih]
    linear_combination (y : ZMod (y ^ 2 + 1)) ^ (4 * s) * (1 + (y : ZMod (y ^ 2 + 1))) * hy2

/-- Modulo `y ^ 2 + 1`, `repunit y (4 s + 2) = y + 1`. -/
lemma repunit_mod_sq_add_one (y s : ℕ) :
    ((repunit y (4 * s + 2) : ℕ) : ZMod (y ^ 2 + 1)) = (y : ZMod (y ^ 2 + 1)) + 1 := by
  have hy2 : (y : ZMod (y ^ 2 + 1)) ^ 2 + 1 = 0 := by
    have : ((y ^ 2 + 1 : ℕ) : ZMod (y ^ 2 + 1)) = 0 := ZMod.natCast_self _
    push_cast at this
    exact this
  induction s with
  | zero =>
    simp only [repunit, Finset.sum_range_succ, Finset.sum_range_zero]
    push_cast
    ring
  | succ s ih =>
    rw [show 4 * (s + 1) + 2 = 4 * s + 2 + 1 + 1 + 1 + 1 by ring]
    rw [repunit_succ, repunit_succ, repunit_succ, repunit_succ]
    push_cast
    rw [ih]
    linear_combination (y : ZMod (y ^ 2 + 1)) ^ (4 * s) * (y : ZMod (y ^ 2 + 1)) ^ 2 *
      (1 + (y : ZMod (y ^ 2 + 1))) * hy2

/-- For odd `t` and even `y`: `(2 x + 1) ^ 2 ≡ 4 y + 1 (mod y ^ 2 + 1)`, and by reciprocity
`J(4 y + 1 | y ^ 2 + 1) = J(y ^ 2 + 1 | 4 y + 1) = J(17 | 4 y + 1) = J(4 y + 1 | 17)`
(as `16 (y ^ 2 + 1) ≡ 17 (mod 4 y + 1)`), so `J(4 y + 1 | 17) ≠ -1`. -/
lemma jacobi_seventeen (x y t : ℕ) (hy : y % 2 = 0) (ht : t % 2 = 1)
    (h : x ^ 2 + x + 1 = repunit y (t + t)) : jacobiSym (4 * y + 1) 17 ≠ -1 := by
  intro hJ
  obtain ⟨s, hs⟩ : ∃ s, t + t = 4 * s + 2 := ⟨t / 2, by omega⟩
  have hN := repunit_mod_sq_add_one y s
  rw [← hs, ← h] at hN
  have hsq : ((2 * x + 1 : ℕ) : ZMod (y ^ 2 + 1)) ^ 2 = ((4 * y + 1 : ℤ) : ZMod (y ^ 2 + 1)) := by
    push_cast at hN ⊢
    linear_combination 4 * hN
  have hodd : Odd (y ^ 2 + 1) := by
    obtain ⟨k, hk⟩ : ∃ k, y = 2 * k := ⟨y / 2, by omega⟩
    exact ⟨2 * k * k, by rw [hk]; ring⟩
  have hodd2 : Odd (4 * y + 1) := ⟨2 * y, by ring⟩
  have h16 : jacobiSym 16 (4 * y + 1) = 1 := by
    rw [show (16 : ℤ) = 4 ^ 2 by norm_num]
    apply jacobiSym.sq_one'
    have : Int.gcd 4 ((4 * y + 1 : ℕ) : ℤ) = Nat.gcd 4 (4 * y + 1) := rfl
    rw [this]
    rw [Nat.gcd_comm, Nat.gcd_rec]
    norm_num [Nat.mul_add_mod]
  have e1 : jacobiSym ((y ^ 2 + 1 : ℕ) : ℤ) (4 * y + 1) = jacobiSym 17 (4 * y + 1) := by
    calc jacobiSym ((y ^ 2 + 1 : ℕ) : ℤ) (4 * y + 1)
        = jacobiSym 16 (4 * y + 1) * jacobiSym ((y ^ 2 + 1 : ℕ) : ℤ) (4 * y + 1) := by
          rw [h16, one_mul]
      _ = jacobiSym (16 * ((y ^ 2 + 1 : ℕ) : ℤ)) (4 * y + 1) := by rw [jacobiSym.mul_left]
      _ = jacobiSym 17 (4 * y + 1) := by
          apply jacobiSym.mod_left'
          rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
          apply Int.emod_eq_zero_of_dvd
          exact ⟨4 * y - 1, by push_cast; ring⟩
  have hJ' : jacobiSym (4 * y + 1) (y ^ 2 + 1) = -1 := by
    have e0 : ((4 * y + 1 : ℤ)) = ((4 * y + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [e0, jacobiSym.quadratic_reciprocity_one_mod_four (by omega) hodd, e1]
    have e2 : (17 : ℤ) = ((17 : ℕ) : ℤ) := by norm_num
    rw [e2, jacobiSym.quadratic_reciprocity_one_mod_four (by norm_num) hodd2]
    push_cast
    exact hJ
  exact ZMod.nonsquare_of_jacobiSym_eq_neg_one hJ' ⟨_, by rw [← hsq]; ring⟩

/-- `J(4 y + 1 | 17) ≠ -1` means `y mod 17` is one of `0, 2, 3, 4, 5, 6, 8, 12, 13`. -/
lemma jacobi_residues (y : ℕ) (h : jacobiSym (4 * y + 1) 17 ≠ -1) :
    y % 17 ∈ ({0, 2, 3, 4, 5, 6, 8, 12, 13} : Finset ℕ) := by
  rw [jacobiSym.mod_left] at h
  have e : ((4 * y + 1 : ℤ)) % ((17 : ℕ) : ℤ) = (((4 * (y % 17) + 1) % 17 : ℕ) : ℤ) := by
    push_cast
    omega
  rw [e] at h
  have hlt := Nat.mod_lt y (show 17 > 0 by norm_num)
  interval_cases hr : y % 17 <;> simp_all <;> norm_num at h

/-- If `4 y + 1` is a square modulo an odd `m` and `16 m ≡ c (mod 4 y + 1)` with `c` odd, then
`J(4 y + 1 | c) ≠ -1` (two applications of reciprocity, `4 y + 1 ≡ 1 (mod 4)`). -/
lemma jacobi_transfer (y m c : ℕ) (hm : Odd m) (hc : Odd c)
    (hmc : (16 * (m : ℤ)) % ((4 * y + 1 : ℕ) : ℤ) = (c : ℤ) % ((4 * y + 1 : ℕ) : ℤ))
    (hsq : IsSquare (((4 * y + 1 : ℕ) : ℤ) : ZMod m)) : jacobiSym (4 * y + 1) c ≠ -1 := by
  intro hJ
  have hodd2 : Odd (4 * y + 1) := ⟨2 * y, by ring⟩
  have h16 : jacobiSym 16 (4 * y + 1) = 1 := by
    rw [show (16 : ℤ) = 4 ^ 2 by norm_num]
    apply jacobiSym.sq_one'
    have : Int.gcd 4 ((4 * y + 1 : ℕ) : ℤ) = Nat.gcd 4 (4 * y + 1) := rfl
    rw [this]
    rw [Nat.gcd_comm, Nat.gcd_rec]
    norm_num [Nat.mul_add_mod]
  have e1 : jacobiSym (m : ℤ) (4 * y + 1) = jacobiSym (c : ℤ) (4 * y + 1) := by
    calc jacobiSym (m : ℤ) (4 * y + 1)
        = jacobiSym 16 (4 * y + 1) * jacobiSym (m : ℤ) (4 * y + 1) := by rw [h16, one_mul]
      _ = jacobiSym (16 * (m : ℤ)) (4 * y + 1) := by rw [jacobiSym.mul_left]
      _ = jacobiSym (c : ℤ) (4 * y + 1) := jacobiSym.mod_left' hmc
  have hJ' : jacobiSym (((4 * y + 1 : ℕ) : ℤ)) m = -1 := by
    rw [jacobiSym.quadratic_reciprocity_one_mod_four (by omega) hm, e1,
      ← jacobiSym.quadratic_reciprocity_one_mod_four (by omega) hc]
    push_cast
    exact hJ
  exact ZMod.nonsquare_of_jacobiSym_eq_neg_one hJ' hsq

/-- Modulo `y ^ 2 + y + 1` (where `y ^ 3 = 1`), `repunit y (3 j + 2) = y + 1`. -/
lemma repunit_mod_phi3 (y j : ℕ) :
    ((repunit y (3 * j + 2) : ℕ) : ZMod (y ^ 2 + y + 1)) = (y : ZMod (y ^ 2 + y + 1)) + 1 := by
  have hm : (y : ZMod (y ^ 2 + y + 1)) ^ 2 + y + 1 = 0 := by
    have : ((y ^ 2 + y + 1 : ℕ) : ZMod (y ^ 2 + y + 1)) = 0 := ZMod.natCast_self _
    push_cast at this
    exact this
  induction j with
  | zero =>
    simp only [repunit, Finset.sum_range_succ, Finset.sum_range_zero]
    push_cast
    ring
  | succ j ih =>
    rw [show 3 * (j + 1) + 2 = 3 * j + 2 + 1 + 1 + 1 by ring]
    rw [repunit_succ, repunit_succ, repunit_succ]
    push_cast
    rw [ih]
    linear_combination (y : ZMod (y ^ 2 + y + 1)) ^ (3 * j + 2) * hm

/-- Modulo `z ^ 2 + z + 1 = y ^ 2 - y + 1` with `y = z + 1` (where `y ^ 3 = -1`),
`repunit y (6 k + 2) = y + 1`. -/
lemma repunit_mod_phi6 (z k : ℕ) :
    ((repunit (z + 1) (6 * k + 2) : ℕ) : ZMod (z ^ 2 + z + 1)) =
      ((z + 1 : ℕ) : ZMod (z ^ 2 + z + 1)) + 1 := by
  have hm : (z : ZMod (z ^ 2 + z + 1)) ^ 2 + z + 1 = 0 := by
    have : ((z ^ 2 + z + 1 : ℕ) : ZMod (z ^ 2 + z + 1)) = 0 := ZMod.natCast_self _
    push_cast at this
    exact this
  induction k with
  | zero =>
    simp only [repunit, Finset.sum_range_succ, Finset.sum_range_zero]
    push_cast
    ring
  | succ k ih =>
    rw [show 6 * (k + 1) + 2 = 6 * k + 2 + 1 + 1 + 1 + 1 + 1 + 1 by ring]
    rw [repunit_succ, repunit_succ, repunit_succ, repunit_succ, repunit_succ, repunit_succ]
    push_cast at ih ⊢
    rw [ih]
    linear_combination ((z : ZMod (z ^ 2 + z + 1)) + 1) ^ (6 * k + 2) *
      (1 + ((z : ZMod (z ^ 2 + z + 1)) + 1) + ((z : ZMod (z ^ 2 + z + 1)) + 1) ^ 2) *
      (2 + (z : ZMod (z ^ 2 + z + 1))) * hm

lemma jacobi_thirteen (x y t : ℕ) (hy : y % 2 = 0) (ht : t % 3 = 1)
    (h : x ^ 2 + x + 1 = repunit y (t + t)) : jacobiSym (4 * y + 1) 13 ≠ -1 := by
  obtain ⟨j, hj⟩ : ∃ j, t + t = 3 * j + 2 := ⟨2 * (t / 3), by omega⟩
  have hN := repunit_mod_phi3 y j
  rw [← hj, ← h] at hN
  apply jacobi_transfer y (y ^ 2 + y + 1) 13
  · obtain ⟨k, hk⟩ : ∃ k, y = 2 * k := ⟨y / 2, by omega⟩
    exact ⟨2 * k * k + k, by rw [hk]; ring⟩
  · exact ⟨6, by norm_num⟩
  · rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
    apply Int.emod_eq_zero_of_dvd
    exact ⟨4 * y + 3, by push_cast; ring⟩
  · refine ⟨((2 * x + 1 : ℕ) : ZMod (y ^ 2 + y + 1)), ?_⟩
    push_cast at hN ⊢
    linear_combination -4 * hN

lemma jacobi_twentyone (x y t : ℕ) (hy : y % 2 = 0) (hy1 : 1 ≤ y) (ht : t % 3 = 1)
    (h : x ^ 2 + x + 1 = repunit y (t + t)) : jacobiSym (4 * y + 1) 21 ≠ -1 := by
  obtain ⟨z, rfl⟩ : ∃ z, y = z + 1 := ⟨y - 1, by omega⟩
  obtain ⟨k, hk⟩ : ∃ k, t + t = 6 * k + 2 := ⟨t / 3, by omega⟩
  have hN := repunit_mod_phi6 z k
  rw [← hk, ← h] at hN
  apply jacobi_transfer (z + 1) (z ^ 2 + z + 1) 21
  · obtain ⟨k, hk⟩ : ∃ k, z = 2 * k + 1 := ⟨z / 2, by omega⟩
    exact ⟨2 * k * k + 3 * k + 1, by rw [hk]; ring⟩
  · exact ⟨10, by norm_num⟩
  · rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
    apply Int.emod_eq_zero_of_dvd
    exact ⟨4 * z - 1, by push_cast; ring⟩
  · refine ⟨((2 * x + 1 : ℕ) : ZMod (z ^ 2 + z + 1)), ?_⟩
    push_cast at hN ⊢
    linear_combination -4 * hN

lemma residues_thirteen (y : ℕ) (h : jacobiSym (4 * y + 1) 13 ≠ -1) :
    y % 13 ∈ ({0, 2, 3, 4, 6, 7, 12} : Finset ℕ) := by
  rw [jacobiSym.mod_left] at h
  have e : ((4 * y + 1 : ℤ)) % ((13 : ℕ) : ℤ) = (((4 * (y % 13) + 1) % 13 : ℕ) : ℤ) := by
    push_cast
    omega
  rw [e] at h
  have hlt := Nat.mod_lt y (show 13 > 0 by norm_num)
  interval_cases hr : y % 13 <;> simp_all <;> norm_num at h

lemma residues_seven (y : ℕ) (h3 : y % 3 = 0) (h : jacobiSym (4 * y + 1) 21 ≠ -1) :
    y % 7 ∈ ({0, 2, 5, 6} : Finset ℕ) := by
  rw [jacobiSym.mod_left] at h
  have e : ((4 * y + 1 : ℤ)) % ((21 : ℕ) : ℤ) = (((4 * (y % 21) + 1) % 21 : ℕ) : ℤ) := by
    push_cast
    omega
  rw [e] at h
  have h7 : y % 7 = y % 21 % 7 := by omega
  have h3' : y % 21 % 3 = 0 := by omega
  rw [h7]
  have hlt := Nat.mod_lt y (show 21 > 0 by norm_num)
  interval_cases hr : y % 21 <;> simp_all <;> norm_num at h

/-- If `L ≡ 1 (mod 4)` is a square modulo an odd `m` and `k ^ 2 m ≡ c (mod L)` with `c` odd and
`k` prime to `L`, then `J(L | c) ≠ -1`. -/
lemma jacobi_transfer' (L m c k : ℕ) (hL : L % 4 = 1) (hm : Odd m) (hc : Odd c)
    (hk : Nat.Coprime k L)
    (hmc : ((k : ℤ) ^ 2 * (m : ℤ)) % (L : ℤ) = (c : ℤ) % (L : ℤ))
    (hsq : IsSquare ((L : ℤ) : ZMod m)) : jacobiSym L c ≠ -1 := by
  intro hJ
  have hk2 : jacobiSym ((k : ℤ) ^ 2) L = 1 := by
    apply jacobiSym.sq_one'
    rw [Int.gcd_natCast_natCast]
    exact hk
  have e1 : jacobiSym (m : ℤ) L = jacobiSym (c : ℤ) L := by
    calc jacobiSym (m : ℤ) L = jacobiSym ((k : ℤ) ^ 2) L * jacobiSym (m : ℤ) L := by
          rw [hk2, one_mul]
      _ = jacobiSym ((k : ℤ) ^ 2 * (m : ℤ)) L := by rw [jacobiSym.mul_left]
      _ = jacobiSym (c : ℤ) L := jacobiSym.mod_left' hmc
  have hJ' : jacobiSym (L : ℤ) m = -1 := by
    rw [jacobiSym.quadratic_reciprocity_one_mod_four hL hm, e1,
      ← jacobiSym.quadratic_reciprocity_one_mod_four hL hc]
    exact hJ
  exact ZMod.nonsquare_of_jacobiSym_eq_neg_one hJ' hsq

/-- Modulo `z ^ 2 + z + 1 = y ^ 2 - y + 1` with `y = z + 1`, `repunit y (6 k + 4) = 2 y - 1`. -/
lemma repunit_mod_phi6' (z k : ℕ) :
    ((repunit (z + 1) (6 * k + 4) : ℕ) : ZMod (z ^ 2 + z + 1)) =
      2 * (z : ZMod (z ^ 2 + z + 1)) + 1 := by
  have hm : (z : ZMod (z ^ 2 + z + 1)) ^ 2 + z + 1 = 0 := by
    have : ((z ^ 2 + z + 1 : ℕ) : ZMod (z ^ 2 + z + 1)) = 0 := ZMod.natCast_self _
    push_cast at this
    exact this
  induction k with
  | zero =>
    simp only [repunit, Finset.sum_range_succ, Finset.sum_range_zero]
    push_cast
    linear_combination ((z : ZMod (z ^ 2 + z + 1)) + 3) * hm
  | succ k ih =>
    rw [show 6 * (k + 1) + 4 = 6 * k + 4 + 1 + 1 + 1 + 1 + 1 + 1 by ring]
    rw [repunit_succ, repunit_succ, repunit_succ, repunit_succ, repunit_succ, repunit_succ]
    push_cast at ih ⊢
    rw [ih]
    linear_combination ((z : ZMod (z ^ 2 + z + 1)) + 1) ^ (6 * k + 4) *
      (1 + ((z : ZMod (z ^ 2 + z + 1)) + 1) + ((z : ZMod (z ^ 2 + z + 1)) + 1) ^ 2) *
      (2 + (z : ZMod (z ^ 2 + z + 1))) * hm

/-- Modulo `u ^ 2 + u + 1 = y ^ 4 - y ^ 2 + 1` with `y ^ 2 = u + 1` (where `y ^ 6 = -1`),
`repunit y (12 k + 2) = y + 1`. -/
lemma repunit_mod_phi12 (y u k : ℕ) (hu : y ^ 2 = u + 1) :
    ((repunit y (12 * k + 2) : ℕ) : ZMod (u ^ 2 + u + 1)) = (y : ZMod (u ^ 2 + u + 1)) + 1 := by
  have hm : (u : ZMod (u ^ 2 + u + 1)) ^ 2 + u + 1 = 0 := by
    have : ((u ^ 2 + u + 1 : ℕ) : ZMod (u ^ 2 + u + 1)) = 0 := ZMod.natCast_self _
    push_cast at this
    exact this
  have hy : (y : ZMod (u ^ 2 + u + 1)) ^ 2 = u + 1 := by
    have := congrArg (fun n : ℕ => (n : ZMod (u ^ 2 + u + 1))) hu
    push_cast at this
    exact this
  induction k with
  | zero =>
    simp only [repunit, Finset.sum_range_succ, Finset.sum_range_zero]
    push_cast
    ring
  | succ k ih =>
    rw [show 12 * (k + 1) + 2 = 12 * k + 2 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 by ring]
    rw [repunit_succ, repunit_succ, repunit_succ, repunit_succ, repunit_succ, repunit_succ,
      repunit_succ, repunit_succ, repunit_succ, repunit_succ, repunit_succ, repunit_succ]
    push_cast
    rw [ih]
    linear_combination (y : ZMod (u ^ 2 + u + 1)) ^ (12 * k + 2) *
      (1 + (y : ZMod (u ^ 2 + u + 1)) ^ 2 + (y : ZMod (u ^ 2 + u + 1)) ^ 4) *
      (1 + (y : ZMod (u ^ 2 + u + 1)) + (y : ZMod (u ^ 2 + u + 1)) ^ 2 +
        (y : ZMod (u ^ 2 + u + 1)) ^ 3) *
      (hm + ((y : ZMod (u ^ 2 + u + 1)) ^ 2 + u) * hy)

/-- For `t ≡ 2 (mod 3)`: `(2 x + 1) ^ 2 ≡ 8 y - 7 (mod y ^ 2 - y + 1)` and
`64 (y ^ 2 - y + 1) ≡ 57 (mod 8 y - 7)`, so `J(8 y - 7 | 57) ≠ -1`. -/
lemma jacobi_fiftyseven (x y t : ℕ) (hy : y % 2 = 0) (hy1 : 1 ≤ y) (ht : t % 3 = 2)
    (h : x ^ 2 + x + 1 = repunit y (t + t)) : jacobiSym (8 * (y - 1) + 1 : ℕ) 57 ≠ -1 := by
  obtain ⟨z, rfl⟩ : ∃ z, y = z + 1 := ⟨y - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  obtain ⟨k, hk⟩ : ∃ k, t + t = 6 * k + 4 := ⟨t / 3, by omega⟩
  have hN := repunit_mod_phi6' z k
  rw [← hk, ← h] at hN
  apply jacobi_transfer' (8 * z + 1) (z ^ 2 + z + 1) 57 8 (by omega)
  · obtain ⟨j, hj⟩ : ∃ j, z = 2 * j + 1 := ⟨z / 2, by omega⟩
    exact ⟨2 * j * j + 3 * j + 1, by rw [hj]; ring⟩
  · exact ⟨28, by norm_num⟩
  · rw [Nat.coprime_comm, Nat.Coprime, Nat.gcd_rec]
    norm_num [Nat.mul_add_mod]
  · rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
    apply Int.emod_eq_zero_of_dvd
    exact ⟨8 * z + 7, by push_cast; ring⟩
  · refine ⟨((2 * x + 1 : ℕ) : ZMod (z ^ 2 + z + 1)), ?_⟩
    push_cast at hN ⊢
    linear_combination -4 * hN

/-- For `t ≡ 1 (mod 6)`: `(2 x + 1) ^ 2 ≡ 4 y + 1 (mod y ^ 4 - y ^ 2 + 1)` and
`256 (y ^ 4 - y ^ 2 + 1) ≡ 241 (mod 4 y + 1)`, so `J(4 y + 1 | 241) ≠ -1`. -/
lemma jacobi_241 (x y t : ℕ) (hy1 : 1 ≤ y) (ht : t % 6 = 1)
    (h : x ^ 2 + x + 1 = repunit y (t + t)) : jacobiSym (4 * y + 1) 241 ≠ -1 := by
  obtain ⟨u, hu⟩ : ∃ u, y ^ 2 = u + 1 := ⟨y ^ 2 - 1, by
    have := Nat.one_le_pow 2 y hy1
    omega⟩
  obtain ⟨k, hk⟩ : ∃ k, t + t = 12 * k + 2 := ⟨t / 6, by omega⟩
  have hN := repunit_mod_phi12 y u k hu
  rw [← hk, ← h] at hN
  have e0 : ((4 * y + 1 : ℤ)) = ((4 * y + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [e0]
  apply jacobi_transfer' (4 * y + 1) (u ^ 2 + u + 1) 241 16 (by omega)
  · obtain ⟨j, hj⟩ := Nat.even_mul_succ_self u
    exact ⟨j, by rw [show u ^ 2 + u = u * (u + 1) by ring, hj]; ring⟩
  · exact ⟨120, by norm_num⟩
  · rw [show (16 : ℕ) = 2 ^ 4 by norm_num, Nat.coprime_pow_left_iff (by norm_num),
      Nat.coprime_two_left]
    exact ⟨2 * y, by ring⟩
  · rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
    apply Int.emod_eq_zero_of_dvd
    have hu' : (u : ℤ) = (y : ℤ) ^ 2 - 1 := by
      have := congrArg (fun n : ℕ => (n : ℤ)) hu
      push_cast at this
      linarith
    refine ⟨64 * (y : ℤ) ^ 3 - 16 * (y : ℤ) ^ 2 - 60 * y + 15, ?_⟩
    push_cast
    rw [hu']
    ring
  · refine ⟨((2 * x + 1 : ℕ) : ZMod (u ^ 2 + u + 1)), ?_⟩
    push_cast at hN ⊢
    linear_combination -4 * hN

lemma residues_nineteen (y : ℕ) (hy1 : 1 ≤ y) (h3 : y % 3 = 0)
    (h : jacobiSym (8 * (y - 1) + 1 : ℕ) 57 ≠ -1) :
    y % 19 ∈ ({0, 5, 6, 8, 9, 12, 13, 14, 15, 17} : Finset ℕ) := by
  obtain ⟨z, rfl⟩ : ∃ z, y = z + 1 := ⟨y - 1, by omega⟩
  rw [Nat.add_sub_cancel] at h
  rw [jacobiSym.mod_left] at h
  have e : (((8 * z + 1 : ℕ) : ℤ)) % ((57 : ℕ) : ℤ) = (((8 * (z % 57) + 1) % 57 : ℕ) : ℤ) := by
    push_cast
    omega
  rw [e] at h
  have h19 : (z + 1) % 19 = (z % 57 + 1) % 19 := by omega
  have h3' : (z % 57 + 1) % 3 = 0 := by omega
  rw [h19]
  have hlt := Nat.mod_lt z (show 57 > 0 by norm_num)
  interval_cases hr : z % 57 <;> simp_all <;> norm_num at h

/-- For `y = 18 q + 2` and `t ≡ 1 (mod 6)`: `y ^ 2 - y + 1 = 3 m` with `m = 108 q ^ 2 + 18 q + 1`,
`(2 x + 1) ^ 2 ≡ 4 y + 1 = 9 (8 q + 1) (mod m)`, so `8 q + 1` is a square modulo `m`; and
`16 m ≡ 7 (mod 8 q + 1)`, so `J(8 q + 1 | 7) ≠ -1`, which puts `y mod 7` in `{0, 2, 5, 6}`. -/
lemma seven_of_two_mod_three (x q t : ℕ) (ht : t % 6 = 1)
    (h : x ^ 2 + x + 1 = repunit (18 * q + 2) (t + t)) :
    (18 * q + 2) % 7 ∈ ({0, 2, 5, 6} : Finset ℕ) := by
  obtain ⟨k, hk⟩ : ∃ k, t + t = 6 * k + 2 := ⟨t / 3, by omega⟩
  have hN := repunit_mod_phi6 (18 * q + 1) k
  rw [show 18 * q + 1 + 1 = 18 * q + 2 by ring, ← hk, ← h] at hN
  have hM : (18 * q + 1) ^ 2 + (18 * q + 1) + 1 = 3 * (108 * q ^ 2 + 18 * q + 1) := by ring
  rw [hM] at hN
  have hN' : ((x ^ 2 + x + 1 : ℕ) : ZMod (108 * q ^ 2 + 18 * q + 1)) =
      ((18 * q + 3 : ℕ) : ZMod (108 * q ^ 2 + 18 * q + 1)) := by
    have h1 : ((x ^ 2 + x + 1 : ℕ) : ZMod (3 * (108 * q ^ 2 + 18 * q + 1))) =
        ((18 * q + 3 : ℕ) : ZMod (3 * (108 * q ^ 2 + 18 * q + 1))) := by
      rw [hN]
      push_cast
      ring
    rw [ZMod.natCast_eq_natCast_iff] at h1 ⊢
    exact Nat.ModEq.of_dvd (Dvd.intro_left 3 rfl) h1
  have hm : ((108 * q ^ 2 + 18 * q + 1 : ℕ) : ZMod (108 * q ^ 2 + 18 * q + 1)) = 0 :=
    ZMod.natCast_self _
  push_cast at hN' hm
  have hJ := jacobi_transfer' (8 * q + 1) (108 * q ^ 2 + 18 * q + 1) 7 4 (by omega)
    ⟨54 * q ^ 2 + 9 * q, by ring⟩ ⟨3, by norm_num⟩
    (by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, Nat.coprime_pow_left_iff (by norm_num),
        Nat.coprime_two_left]
      exact ⟨4 * q, by ring⟩)
    (by
      rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
      apply Int.emod_eq_zero_of_dvd
      exact ⟨9 * (24 * q + 1), by push_cast; ring⟩)
    ⟨((2 * x + 1 : ℕ) : ZMod (108 * q ^ 2 + 18 * q + 1)) *
      (-(36 * (q : ZMod (108 * q ^ 2 + 18 * q + 1)) ^ 2 +
        6 * (q : ZMod (108 * q ^ 2 + 18 * q + 1)))), by
      push_cast
      linear_combination (-4 * (36 * (q : ZMod (108 * q ^ 2 + 18 * q + 1)) ^ 2 + 6 * q) ^ 2) * hN' +
        (-(8 * (q : ZMod (108 * q ^ 2 + 18 * q + 1)) + 1) *
          (108 * (q : ZMod (108 * q ^ 2 + 18 * q + 1)) ^ 2 + 18 * q + 1 - 2)) * hm⟩
  rw [jacobiSym.mod_left] at hJ
  have e : (((8 * q + 1 : ℕ) : ℤ)) % ((7 : ℕ) : ℤ) = (((8 * (q % 7) + 1) % 7 : ℕ) : ℤ) := by
    push_cast
    omega
  rw [e] at hJ
  have h7 : (18 * q + 2) % 7 = (18 * (q % 7) + 2) % 7 := by omega
  rw [h7]
  have hlt := Nat.mod_lt q (show 7 > 0 by norm_num)
  interval_cases hr : q % 7 <;> simp_all <;> norm_num at hJ

theorem main : H1 → H2 → OMA.R_Goormaghtigh_goormaghtigh_conjecture_R1.H2 := by
  intro hH1 hH2 x y n hx hy hxy hn hev heq0
  exfalso
  obtain ⟨t, rfl⟩ := hev
  have ht : 2 ≤ t := by omega
  have heq : x ^ 2 + x + 1 = repunit y (t + t) := by rw [← repunit_three]; exact heq0
  have hgoal : repunit x 3 = repunit y (2 * t) := by rw [two_mul]; exact heq0
  -- y is even
  have hy2 : y % 2 = 0 := by
    by_contra hodd
    have h1 : y % 2 = 1 % 2 := by omega
    have h2 := repunit_mod_of_one y (t + t) 2 h1
    rw [← heq, odd_x2x1] at h2
    omega
  -- the two factorizations
  have hfac1 : x ^ 2 + x + 1 = (y + 1) * repunit (y ^ 2) t := by rw [heq, repunit_two_mul]
  have hfac2 : x ^ 2 + x + 1 = repunit y t * (y ^ t + 1) := by rw [heq, repunit_double]
  have hdy1 : y + 1 ∣ x ^ 2 + x + 1 := Dvd.intro _ hfac1.symm
  -- y is not 1 mod 3
  have hy3 : y % 3 ≠ 1 := by
    intro h
    have := dvd_x2x1_mod_three x (y + 1) hdy1 (by omega)
    omega
  -- N = (1 + y + y ^ 2) + y ^ 3 * M with M ≥ 1
  have hsplit : repunit y (t + t) = (y ^ 2 + y + 1) + y ^ 3 * repunit y (t + t - 3) := by
    have e := repunit_add y 3 (t + t - 3)
    rw [show 3 + (t + t - 3) = t + t by omega, repunit_three] at e
    exact e
  have hM : 1 ≤ repunit y (t + t - 3) := by
    obtain ⟨k, hk⟩ : ∃ k, t + t - 3 = k + 1 := ⟨t + t - 4, by omega⟩
    rw [hk, repunit_succ']
    omega
  have hy3pos : 1 ≤ y ^ 3 := Nat.one_le_pow _ _ (by omega)
  have hyx : y < x := by
    by_contra hc
    rw [not_lt] at hc
    have h1 : x ^ 2 ≤ y ^ 2 := Nat.pow_le_pow_left hc 2
    have h2 : 1 ≤ y ^ 3 * repunit y (t + t - 3) := Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (by omega) (by omega))
    rw [hsplit] at heq
    omega
  -- n = 4 is impossible
  have ht3 : 3 ≤ t := by
    by_contra hc
    have t2 : t = 2 := by omega
    subst t2
    exact no_four x y hyx heq
  -- x (x + 1) ≡ y + y ^ 2 (mod y ^ 3)
  have hmod : x * (x + 1) % y ^ 3 = y + y ^ 2 := by
    have e : x * (x + 1) = (y + y ^ 2) + y ^ 3 * repunit y (t + t - 3) := by
      have := heq
      rw [hsplit] at this
      nlinarith [this]
    rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt]
    nlinarith
  -- y = a b with a ^ 3 ∣ x - y and b ^ 3 ∣ x + y + 1
  have hprodeq : (x - y) * (x + y + 1) = y ^ 3 * repunit y (t + t - 3) := by
    have h1 := heq
    rw [hsplit] at h1
    obtain ⟨d, rfl⟩ : ∃ d, x = y + d := ⟨x - y, by omega⟩
    rw [Nat.add_sub_cancel_left]
    nlinarith [h1]
  have hcube := cube_split x y _ hyx hprodeq
  -- N ≡ n (mod y - 1)
  have hm1 : (x ^ 2 + x + 1) % (y - 1) = 2 * t % (y - 1) := by
    rw [heq, two_mul]
    apply repunit_mod_of_one
    rw [Nat.mod_eq_sub_mod (by omega : y - 1 ≤ y), show y - (y - 1) = 1 by omega]
  -- modulo y ^ 2 + 1
  have hsq1 : t % 2 = 0 → y ^ 2 + 1 ∣ x ^ 2 + x + 1 := by
    intro ht2
    obtain ⟨s, hs⟩ : ∃ s, t + t = 4 * s := ⟨t / 2, by omega⟩
    have h1 := repunit_four_mul_mod y s
    rw [← hs, ← heq, ZMod.natCast_eq_zero_iff] at h1
    exact h1
  have h17 : t % 2 = 1 → y % 17 ∈ ({0, 2, 3, 4, 5, 6, 8, 12, 13} : Finset ℕ) :=
    fun ht2 => jacobi_residues y (jacobi_seventeen x y t hy2 ht2 heq)
  have h13 : t % 3 = 1 → y % 13 ∈ ({0, 2, 3, 4, 6, 7, 12} : Finset ℕ) :=
    fun ht1 => residues_thirteen y (jacobi_thirteen x y t hy2 ht1 heq)
  have h241 : t % 6 = 1 → jacobiSym (4 * y + 1) 241 ≠ -1 :=
    fun ht1 => jacobi_241 x y t (by omega) ht1 heq
  rcases (by omega : y % 3 = 0 ∨ y % 3 = 2) with h0 | h2
  · -- y ≡ 0 (mod 3): N ≡ 1 (mod 3)
    have hN3 : (x ^ 2 + x + 1) % 3 = 1 := by
      have e := repunit_succ' y (t + t - 1)
      rw [show t + t - 1 + 1 = t + t by omega] at e
      rw [heq, e, Nat.add_mod, Nat.mul_mod, h0]
      simp
    have hx3 : x % 3 ≠ 1 := fun h => by
      have := (three_dvd_iff x).mpr h
      omega
    have hp : ∀ p : ℕ, p.Prime → p ∣ x ^ 2 + x + 1 → p % 3 = 1 := by
      intro p hp hpd
      rcases prime_dvd_x2x1 x p hp hpd with h | h
      · subst h
        omega
      · exact h
    have h7 : t % 3 = 1 → y % 7 ∈ ({0, 2, 5, 6} : Finset ℕ) ∧
        y % 13 ∈ ({0, 2, 3, 4, 6, 7, 12} : Finset ℕ) :=
      fun ht1 => ⟨residues_seven y h0 (jacobi_twentyone x y t hy2 (by omega) ht1 heq), h13 ht1⟩
    have h19 : t % 3 = 2 → y % 19 ∈ ({0, 5, 6, 8, 9, 12, 13, 14, 15, 17} : Finset ℕ) :=
      fun ht2 => residues_nineteen y (by omega) h0 (jacobi_fiftyseven x y t hy2 (by omega) ht2 heq)
    exact hH1 x y t hx ht3 (by omega) (by omega) hyx hx3 hp hmod hcube hm1 hsq1 h17 h7 h19 h241
      hgoal
  · -- y ≡ 2 (mod 3)
    have h3y : 3 ∣ y + 1 := by omega
    have hN3 : 3 ∣ x ^ 2 + x + 1 := h3y.trans hdy1
    have hx3 : x % 3 = 1 := (three_dvd_iff x).mp hN3
    -- y ≡ 2 (mod 9)
    have hy9 : y % 9 = 2 := by
      obtain ⟨m, hm⟩ := h3y
      have hmd : m ∣ x ^ 2 + x + 1 := (Dvd.intro_left 3 hm.symm).trans hdy1
      have hm3 : ¬ 3 ∣ m := by
        rintro ⟨k, hk⟩
        apply not_nine_dvd x
        exact (Dvd.intro k (by rw [hm, hk]; ring)).trans hdy1
      have := dvd_x2x1_mod_three x m hmd hm3
      omega
    -- t ≡ 1 (mod 3)
    have hy2' : y ^ 2 % 3 = 1 := by rw [Nat.pow_mod, h2]
    have hR : repunit (y ^ 2) t % 3 = t % 3 := by
      apply repunit_mod_of_one
      rw [hy2']
    have hRd : repunit (y ^ 2) t ∣ x ^ 2 + x + 1 := Dvd.intro_left _ hfac1.symm
    have hR3 : ¬ 3 ∣ repunit (y ^ 2) t := by
      intro h
      apply not_nine_dvd x
      rw [hfac1]
      obtain ⟨a, ha⟩ := h3y
      obtain ⟨b, hb⟩ := h
      exact ⟨a * b, by rw [ha, hb]; ring⟩
    have ht3' : t % 3 = 1 := by
      have := dvd_x2x1_mod_three x _ hRd hR3
      omega
    -- t is odd
    have ht2 : t % 2 = 1 := by
      by_contra hc
      obtain ⟨s, hs⟩ : ∃ s, t = 2 * s := ⟨t / 2, by omega⟩
      have hB : (y ^ t + 1) % 3 = 2 := by
        rw [hs, pow_mul, Nat.add_mod, Nat.pow_mod, hy2', one_pow]
        norm_num
      have hBd : y ^ t + 1 ∣ x ^ 2 + x + 1 := Dvd.intro_left _ hfac2.symm
      have := dvd_x2x1_mod_three x _ hBd (by omega)
      omega
    -- every divisor of t is 1 mod 6
    have hdivt : ∀ d : ℕ, d ∣ t → d % 6 = 1 := by
      intro d hd
      obtain ⟨k, hk⟩ := hd
      have hRdR : repunit (y ^ 2) d ∣ repunit (y ^ 2) t := by
        rw [hk, repunit_mul]
        exact dvd_mul_right _ _
      have h3d : ¬ 3 ∣ repunit (y ^ 2) d := fun h3 => hR3 (h3.trans hRdR)
      have hmodd : repunit (y ^ 2) d % 3 = d % 3 := by
        apply repunit_mod_of_one
        rw [hy2']
      have h1d := dvd_x2x1_mod_three x _ (hRdR.trans hRd) h3d
      have hd2 : d % 2 = 1 := by
        rcases Nat.even_or_odd d with he | ho
        · exfalso
          have h2t : 2 ∣ t := (even_iff_two_dvd.mp he).trans ⟨k, hk⟩
          omega
        · exact Nat.odd_iff.mp ho
      omega
    have hy7 : y % 7 ∈ ({0, 2, 5, 6} : Finset ℕ) := by
      obtain ⟨q, hq⟩ : ∃ q, y = 18 * q + 2 := ⟨y / 18, by omega⟩
      have h7 := seven_of_two_mod_three x q t (by omega) (by rw [← hq]; exact heq)
      rw [hq]
      exact h7
    have hsq := not_square x y t hy ht heq
    have hy20 : 20 ≤ y := by
      by_contra hc
      have hy2e : y = 2 := by omega
      apply hsq
      rw [hy2e]
      exact ⟨1, rfl⟩
    exact hH2 x y t hx (by omega) hy20 (by omega) (by omega) hdivt hyx hx3 hsq
      (fun p hp hpd => prime_dvd_x2x1 x p hp hpd) (not_nine_dvd x) hmod hcube hm1 (h17 ht2)
      (h13 ht3') hy7 (h241 (by omega)) hgoal

end OMA.R_Goormaghtigh_goormaghtigh_conjecture_R1_H2_R1
