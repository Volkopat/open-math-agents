import OMAStatements.S_oeis_a363196
import Mathlib

/-!
Proof of the A363196 conjecture: `a n = -1` iff `n = 1`.
- `n = 1`: `3^k mod 100` has period 20 (`3^20 ≡ 1 mod 100`), and none of the 20 residues has tens digit 7 together
  with a units digit other than 7. Digits 0 and 1 of `x` depend only on `x mod 100` (`digit_mod`).
- `n = 0, 2, 3`: `k = 3, 6, 37`.
- `n = k + 4`: `81^125 ≡ 1 + 10^4 (mod 10^5)` lifts, by `(1 + z)^s = 1 + s*z + z^2*Q` with `s = 10`, to
  `81^(125*10^k) ≡ 1 + 10^(k+4) (mod 10^(k+5))`; then `3^(3500*10^k) = (81^(125*10^k))^7 ≡ 1 + 7*10^(k+4)
  (mod 10^(k+5))` (the same identity with `s = 7`), and the rightmost 7 of `1 + 7*10^n` is at the `10^n` position.
-/

namespace OMA.A363196Proof

open OMA.S_oeis_a363196

/-- The definition in terms of `x / 10^i % 10`. -/
theorem R_iff (x n : ℕ) :
    RightmostSevenAt x n ↔ x / 10 ^ n % 10 = 7 ∧ ∀ i < n, x / 10 ^ i % 10 ≠ 7 := by
  have key : ∀ i, (Nat.digits 10 x).getD i 0 = x / 10 ^ i % 10 :=
    fun i => Nat.getD_digits x i (by norm_num)
  unfold RightmostSevenAt
  simp only [key]

/-- The digit at index `i ≤ n` depends only on `x mod 10^(n+1)`. -/
theorem digit_mod (x n i : ℕ) (hi : i ≤ n) : x / 10 ^ i % 10 = x % 10 ^ (n + 1) / 10 ^ i % 10 := by
  have h : 10 ^ (n + 1) = 10 ^ i * 10 ^ (n + 1 - i) := by
    rw [← pow_add]; congr 1; omega
  have hd : (10 : ℕ) ∣ 10 ^ (n + 1 - i) := dvd_pow_self 10 (by omega)
  rw [h, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ hd]

theorem R_congr {x y n : ℕ} (h : x % 10 ^ (n + 1) = y % 10 ^ (n + 1)) :
    RightmostSevenAt x n ↔ RightmostSevenAt y n := by
  have key : ∀ i ≤ n, x / 10 ^ i % 10 = y / 10 ^ i % 10 := fun i hi => by
    rw [digit_mod x n i hi, digit_mod y n i hi, h]
  rw [R_iff, R_iff, key n le_rfl]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun i hi => by rw [← key i hi.le]; exact h2 i hi⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun i hi => by rw [key i hi.le]; exact h2 i hi⟩

theorem pow3_mod100 (k : ℕ) : 3 ^ k % 100 = 3 ^ (k % 20) % 100 := by
  conv_lhs => rw [← Nat.div_add_mod k 20, pow_add, pow_mul]
  rw [Nat.mul_mod, Nat.pow_mod (3 ^ 20)]
  norm_num

/-- `n = 1`: no `k` works. -/
theorem not_one (k : ℕ) : ¬ RightmostSevenAt (3 ^ k) 1 := by
  have hp : 3 ^ k % 10 ^ (1 + 1) = 3 ^ (k % 20) % 10 ^ (1 + 1) := by
    rw [show (10 : ℕ) ^ (1 + 1) = 100 by norm_num]
    exact pow3_mod100 k
  rw [R_congr hp, R_iff]
  have key : ∀ r < 20, ¬ (3 ^ r / 10 ^ 1 % 10 = 7 ∧ ∀ i < 1, 3 ^ r / 10 ^ i % 10 ≠ 7) := by decide
  exact key _ (Nat.mod_lt _ (by norm_num))

theorem w0 : RightmostSevenAt (3 ^ 3) 0 := (R_iff _ _).2 (by decide)

theorem w2 : RightmostSevenAt (3 ^ 6) 2 := (R_iff _ _).2 (by decide)

theorem w3 : RightmostSevenAt (3 ^ 37) 3 := (R_iff _ _).2 (by decide)

/-- `(1 + z)^s ≡ 1 + s*z (mod z^2)`. -/
theorem binom (z : ℤ) (s : ℕ) : ∃ Q : ℤ, (1 + z) ^ s = 1 + (s : ℤ) * z + z ^ 2 * Q := by
  induction s with
  | zero => exact ⟨0, by simp⟩
  | succ s ih =>
    obtain ⟨Q, hQ⟩ := ih
    refine ⟨s + Q + z * Q, ?_⟩
    rw [pow_succ, hQ]
    push_cast
    ring

/-- `81^(125*10^k) ≡ 1 + 10^(k+4) (mod 10^(k+5))`. -/
theorem lift (k : ℕ) : ∃ e : ℤ, (81 : ℤ) ^ (125 * 10 ^ k) = 1 + 10 ^ (k + 4) + e * 10 ^ (k + 5) := by
  induction k with
  | zero => exact ⟨((81 : ℤ) ^ 125 - 10001) / 10 ^ 5, by norm_num⟩
  | succ k ih =>
    obtain ⟨e, he⟩ := ih
    obtain ⟨Q, hQ⟩ := binom ((1 + 10 * e) * 10 ^ (k + 4)) 10
    refine ⟨e + (1 + 10 * e) ^ 2 * 10 ^ (k + 2) * Q, ?_⟩
    have h1 : (81 : ℤ) ^ (125 * 10 ^ (k + 1)) = ((81 : ℤ) ^ (125 * 10 ^ k)) ^ 10 := by
      rw [← pow_mul]; congr 1; ring
    have h2 : (81 : ℤ) ^ (125 * 10 ^ k) = 1 + (1 + 10 * e) * 10 ^ (k + 4) := by
      rw [he]; ring
    rw [h1, h2, hQ]
    push_cast
    ring

/-- The rightmost 7 of `1 + 7*10^n` (`n ≥ 1`) is at the `10^n` position. -/
theorem target (n : ℕ) (hn : 1 ≤ n) : RightmostSevenAt (1 + 7 * 10 ^ n) n := by
  rw [R_iff]
  have h10 : 10 ≤ 10 ^ n := by
    calc 10 = 10 ^ 1 := by norm_num
      _ ≤ 10 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  constructor
  · rw [Nat.add_mul_div_right _ _ (by omega : 0 < 10 ^ n)]
    have h0 : 1 / 10 ^ n = 0 := Nat.div_eq_of_lt (by omega)
    omega
  · intro i hi
    have hsplit : 1 + 7 * 10 ^ n = 1 + 10 * (7 * 10 ^ (n - i - 1)) * 10 ^ i := by
      have hp : 10 ^ n = 10 ^ i * 10 * 10 ^ (n - i - 1) := by
        rw [← pow_succ, ← pow_add]; congr 1; omega
      rw [hp]; ring
    rw [hsplit, Nat.add_mul_div_right _ _ (by positivity : 0 < 10 ^ i), Nat.add_mul_mod_self_left]
    have h1 : 1 / 10 ^ i % 10 ≤ 1 := (Nat.mod_le _ _).trans (Nat.div_le_self 1 _)
    exact ne_of_lt (lt_of_le_of_lt h1 (by norm_num))

/-- `n = k + 4`: `k = 3500 * 10^k` works. -/
theorem large (k : ℕ) : RightmostSevenAt (3 ^ (3500 * 10 ^ k)) (k + 4) := by
  obtain ⟨e, he⟩ := lift k
  obtain ⟨Q, hQ⟩ := binom ((1 + 10 * e) * 10 ^ (k + 4)) 7
  have h3 : (3 : ℤ) ^ (3500 * 10 ^ k) = ((81 : ℤ) ^ (125 * 10 ^ k)) ^ 7 := by
    rw [← pow_mul, show (81 : ℤ) = 3 ^ 4 by norm_num, ← pow_mul]
    congr 1
    ring
  have h2 : (81 : ℤ) ^ (125 * 10 ^ k) = 1 + (1 + 10 * e) * 10 ^ (k + 4) := by
    rw [he]; ring
  have hfin : (3 : ℤ) ^ (3500 * 10 ^ k) =
      1 + 7 * 10 ^ (k + 4) + 10 ^ (k + 5) * (7 * e + (1 + 10 * e) ^ 2 * 10 ^ (k + 3) * Q) := by
    rw [h3, h2, hQ]
    push_cast
    ring
  have hmod : 3 ^ (3500 * 10 ^ k) % 10 ^ (k + 4 + 1) = (1 + 7 * 10 ^ (k + 4)) % 10 ^ (k + 4 + 1) := by
    have hm : 1 + 7 * 10 ^ (k + 4) ≡ 3 ^ (3500 * 10 ^ k) [MOD 10 ^ (k + 4 + 1)] := by
      rw [Nat.modEq_iff_dvd]
      push_cast
      exact ⟨7 * e + (1 + 10 * e) ^ 2 * 10 ^ (k + 3) * Q, by linear_combination hfin⟩
    exact hm.symm
  rw [R_congr hmod]
  exact target (k + 4) (by omega)

theorem cast_ne_neg_one (m : ℕ) : (m : ℤ) ≠ -1 := by omega

theorem a_eq_neg_one_iff (n : ℕ) : a n = -1 ↔ ¬ ∃ k, RightmostSevenAt (3 ^ k) n := by
  by_cases h : ∃ k, RightmostSevenAt (3 ^ k) n
  · unfold a
    rw [dif_pos h]
    exact ⟨fun h' => absurd h' (cast_ne_neg_one _), fun h' => absurd h h'⟩
  · unfold a
    rw [dif_neg h]
    exact ⟨fun _ => h, fun _ => rfl⟩

theorem exists_k (n : ℕ) (hn : n ≠ 1) : ∃ k, RightmostSevenAt (3 ^ k) n := by
  rcases (by omega : n = 0 ∨ n = 2 ∨ n = 3 ∨ 4 ≤ n) with h | h | h | h
  · subst h; exact ⟨3, w0⟩
  · subst h; exact ⟨6, w2⟩
  · subst h; exact ⟨37, w3⟩
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
    exact ⟨_, large k⟩

end OMA.A363196Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a363196.main := by
  intro n
  rw [OMA.A363196Proof.a_eq_neg_one_iff]
  constructor
  · intro h
    by_contra hn
    exact h (OMA.A363196Proof.exists_k n hn)
  · rintro rfl ⟨k, hk⟩
    exact OMA.A363196Proof.not_one k hk
