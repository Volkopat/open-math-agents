import OMAStatements.S_oeis_a037096

-- Problem: A037096: Periodic vertical binary vectors computed for powers of 3: a(n) = Sum_{k=0 .. (2^n)-1} (floor((3^k)/(2^n)) mod 2) * 2^k.
-- Upstream: formal-conjectures statements/oeis-a037096.lean:0 (declaration OMA.S_oeis_a037096.main)
-- Credit: @DevinWatson (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.E037096

open Polynomial OMA.S_oeis_a037096

private lemma pow3_pow2_mod : ∀ m : ℕ, 1 ≤ m →
    3 ^ (2 ^ m) % 2 ^ (m + 3) = 1 + 2 ^ (m + 2) := by
  intro m hm
  induction m with
  | zero => omega
  | succ m ih =>
    by_cases hm0 : m = 0
    · subst hm0; decide
    · have hm1 : 1 ≤ m := by omega
      have hprev := ih hm1
      set a := 3 ^ (2 ^ m)
      set q := a / 2 ^ (m + 3)
      have ha : a = 2 ^ (m + 3) * q + (1 + 2 ^ (m + 2)) := by
        have hdm := Nat.div_add_mod a (2 ^ (m + 3))
        rw [hprev] at hdm
        exact hdm.symm
      have hsq : 3 ^ (2 ^ (m + 1)) =
          (1 + 2 ^ (m + 3)) + 2 ^ (m + 4) * (q + 2 ^ m * (1 + 2 * q) ^ 2) := by
        have hpow : 3 ^ (2 ^ (m + 1)) = a ^ 2 := by
          rw [pow_succ, pow_mul]
        rw [hpow, ha]
        have h1 : 2 ^ (m + 3) = 2 * 2 ^ (m + 2) := by rw [pow_succ']
        have h2 : 2 ^ (m + 4) = 4 * 2 ^ (m + 2) := by
          rw [show m + 4 = (m + 2) + 2 by omega, pow_add]; ring
        have h3 : 2 ^ (m + 2) * 2 ^ (m + 2) = 4 * 2 ^ (m + 2) * 2 ^ m := by
          rw [← pow_add, show 4 * 2 ^ (m + 2) = 2 ^ (m + 4) by rw [h2], ← pow_add]
          congr 1; omega
        rw [h1, h2]
        nlinarith [h3]
      rw [hsq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt]
      have hlt : 1 < 2 ^ (m + 3) := by
        have : 2 ^ 1 ≤ 2 ^ (m + 3) := Nat.pow_le_pow_right (by omega) (by omega)
        omega
      have h2 : 2 ^ (m + 4) = 2 ^ (m + 3) + 2 ^ (m + 3) := by rw [pow_succ']; omega
      omega

private lemma pow3_odd (k : ℕ) : 3 ^ k % 2 = 1 := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [pow_succ, Nat.mul_mod, ih]

private lemma digit_add_half (n k : ℕ) (hn : 3 ≤ n) :
    digit n (k + 2 ^ (n - 2)) = digit n k + 1 := by
  have hmod : 3 ^ (2 ^ (n - 2)) % 2 ^ (n + 1) = 1 + 2 ^ n := by
    have h := pow3_pow2_mod (n - 2) (by omega)
    rwa [show n - 2 + 3 = n + 1 by omega, show n - 2 + 2 = n by omega] at h
  set q := 3 ^ (2 ^ (n - 2)) / 2 ^ (n + 1)
  have h3p : 3 ^ (2 ^ (n - 2)) = 2 ^ (n + 1) * q + (1 + 2 ^ n) := by
    have hdm := Nat.div_add_mod (3 ^ (2 ^ (n - 2))) (2 ^ (n + 1))
    rw [hmod] at hdm
    exact hdm.symm
  set r := 3 ^ k / 2
  have h3k : 3 ^ k = 2 * r + 1 := by
    have hdm := Nat.div_add_mod (3 ^ k) 2
    rw [pow3_odd k] at hdm
    exact hdm.symm
  have hprod : 3 ^ (k + 2 ^ (n - 2)) =
      3 ^ k + 2 ^ n * (1 + 2 * (r + 3 ^ k * q)) := by
    rw [pow_add, h3p]
    have h2 : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ']
    rw [h2, h3k]
    ring
  have hdiv : 3 ^ (k + 2 ^ (n - 2)) / 2 ^ n =
      3 ^ k / 2 ^ n + (1 + 2 * (r + 3 ^ k * q)) := by
    rw [hprod, Nat.add_mul_div_left _ _ (Nat.pos_of_ne_zero (by positivity))]
  unfold digit
  rw [ZMod.natCast_mod, ZMod.natCast_mod, hdiv]
  push_cast
  have h2z : (2 : ZMod 2) = 0 := by decide
  rw [h2z]
  ring

private lemma digit_add_period (n k : ℕ) (hn : 3 ≤ n) :
    digit n (k + 2 ^ (n - 1)) = digit n k := by
  have hhalf : 2 ^ (n - 1) = 2 ^ (n - 2) + 2 ^ (n - 2) := by
    rw [show n - 1 = (n - 2) + 1 by omega, pow_succ']; omega
  rw [hhalf, ← add_assoc, digit_add_half n (k + 2 ^ (n - 2)) hn, digit_add_half n k hn]
  have h11 : (1 : ZMod 2) + 1 = 0 := by decide
  rw [add_assoc, h11, add_zero]

private lemma one_add_one_R : (1 : R) + 1 = 0 := by
  rw [← map_one C, ← map_add, show (1 : ZMod 2) + 1 = 0 by decide, map_zero]

private lemma two_R : (2 : R) = 0 := by
  rw [show (2 : R) = 1 + 1 by ring, one_add_one_R]

private lemma add_pow_two_pow (a b : R) : ∀ m : ℕ,
    (a + b) ^ (2 ^ m) = a ^ (2 ^ m) + b ^ (2 ^ m)
  | 0 => by simp
  | m + 1 => by
    rw [pow_succ, pow_mul, add_pow_two_pow a b m, add_sq, ← pow_mul, ← pow_mul, ← pow_succ]
    rw [two_R]
    ring

private lemma x_add_one_mul_geom (L : ℕ) :
    (X + 1 : R) * (∑ k ∈ Finset.range L, X ^ k) = X ^ L + 1 := by
  induction L with
  | zero =>
    simp [one_add_one_R]
  | succ L ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    have hself : (X : R) ^ L + X ^ L = 0 := by
      rw [show (X : R) ^ L + X ^ L = 2 * X ^ L by ring, two_R, zero_mul]
    calc
      (X ^ L + 1) + (X + 1) * X ^ L
          = X ^ (L + 1) + 1 + (X ^ L + X ^ L) := by ring
      _ = X ^ (L + 1) + 1 := by rw [hself, add_zero]

private lemma x_add_one_ne_zero : (X + 1 : R) ≠ 0 := by
  intro h
  have hev := congrArg (Polynomial.eval 0) h
  simp at hev

private lemma geom_eq_pow (m : ℕ) :
    (∑ k ∈ Finset.range (2 ^ m), (X : R) ^ k) = (X + 1) ^ (2 ^ m - 1) := by
  apply mul_left_cancel₀ x_add_one_ne_zero
  rw [x_add_one_mul_geom]
  have hpos : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  rw [← pow_succ', show 2 ^ m - 1 + 1 = 2 ^ m by omega, add_pow_two_pow, one_pow]

private lemma column_full_eq (n : ℕ) (hn : 3 ≤ n) :
    column n (2 ^ n) = (X + 1) ^ (2 ^ (n - 1)) * column n (2 ^ (n - 1)) := by
  set L := 2 ^ (n - 1)
  have h2L : 2 ^ n = L + L := by
    rw [show n = (n - 1) + 1 by omega, pow_succ']; omega
  unfold column
  rw [h2L, Finset.sum_range_add]
  have hshift :
      ∑ k ∈ Finset.range L, C (digit n (L + k)) * X ^ (L + k) =
        X ^ L * ∑ k ∈ Finset.range L, C (digit n k) * X ^ k := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [add_comm L k, digit_add_period n k hn, pow_add]
    ring
  rw [hshift]
  have hpow : (X + 1 : R) ^ L = X ^ L + 1 := by
    simpa [L] using add_pow_two_pow X 1 (n - 1)
  rw [hpow]
  ring

private lemma dvd_column_half (n : ℕ) (hn : 3 ≤ n) :
    (X + 1 : R) ^ (2 ^ (n - 2) - 1) ∣ column n (2 ^ (n - 1)) := by
  set L := 2 ^ (n - 2)
  have h2L : 2 ^ (n - 1) = L + L := by
    rw [show n - 1 = (n - 2) + 1 by omega, pow_succ']; omega
  unfold column
  rw [h2L, Finset.sum_range_add]
  have hshift :
      ∑ k ∈ Finset.range L, C (digit n (L + k)) * X ^ (L + k) =
        X ^ L * (∑ k ∈ Finset.range L, C (digit n k) * X ^ k) +
          X ^ L * (∑ k ∈ Finset.range L, X ^ k) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [add_comm L k, digit_add_half n k hn, map_add, map_one, pow_add]
    ring
  rw [hshift, geom_eq_pow (n - 2)]
  have hpow : (X + 1 : R) ^ L = X ^ L + 1 := by
    simpa [L] using add_pow_two_pow X 1 (n - 2)
  have hpos : 1 ≤ L := Nat.one_le_two_pow
  have hsplit : (X + 1 : R) ^ L = (X + 1) ^ (L - 1) * (X + 1) := by
    rw [← pow_succ, show L - 1 + 1 = L by omega]
  refine ⟨(X + 1) * (∑ k ∈ Finset.range L, C (digit n k) * X ^ k) + X ^ L, ?_⟩
  calc
    (∑ k ∈ Finset.range L, C (digit n k) * X ^ k) +
        (X ^ L * (∑ k ∈ Finset.range L, C (digit n k) * X ^ k) +
          X ^ L * (X + 1) ^ (L - 1))
        = (X ^ L + 1) * (∑ k ∈ Finset.range L, C (digit n k) * X ^ k) +
            X ^ L * (X + 1) ^ (L - 1) := by ring
    _ = (X + 1) ^ L * (∑ k ∈ Finset.range L, C (digit n k) * X ^ k) +
            X ^ L * (X + 1) ^ (L - 1) := by rw [← hpow]
    _ = (X + 1) ^ (L - 1) * ((X + 1) * (∑ k ∈ Finset.range L, C (digit n k) * X ^ k) + X ^ L) := by
        rw [hsplit]; ring

private lemma solution_aux : ∀ n : ℕ, 3 ≤ n →
    (X + 1) ^ (3 * 2 ^ (n - 2) - 1) ∣ column n (2 ^ n) ∧
    column n (2 ^ n) = (X + 1) ^ (3 * 2 ^ (n - 2) - 1) * quotient n := by
  intro n hn
  have hdvd : (X + 1 : R) ^ (2 ^ (n - 2) - 1) ∣ column n (2 ^ (n - 1)) :=
    dvd_column_half n hn
  have hne : (X + 1 : R) ^ (2 ^ (n - 2) - 1) ≠ 0 :=
    pow_ne_zero _ x_add_one_ne_zero
  have hhalf : column n (2 ^ (n - 1)) =
      (X + 1 : R) ^ (2 ^ (n - 2) - 1) * quotient n := by
    unfold quotient
    exact (EuclideanDomain.mul_div_cancel' hne hdvd).symm
  have hexp : 2 ^ (n - 1) + (2 ^ (n - 2) - 1) = 3 * 2 ^ (n - 2) - 1 := by
    have h1 : 2 ^ (n - 1) = 2 * 2 ^ (n - 2) := by
      rw [show n - 1 = (n - 2) + 1 by omega, pow_succ']
    have hpos : 1 ≤ 2 ^ (n - 2) := Nat.one_le_two_pow
    omega
  have heq : column n (2 ^ n) = (X + 1 : R) ^ (3 * 2 ^ (n - 2) - 1) * quotient n := by
    rw [column_full_eq n hn, hhalf, ← mul_assoc, ← pow_add, hexp]
  exact ⟨⟨quotient n, heq⟩, heq⟩

end OMA.E037096

theorem OMA.solution : type_of% @OMA.S_oeis_a037096.main :=
  OMA.E037096.solution_aux
