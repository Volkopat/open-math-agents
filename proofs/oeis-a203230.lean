import OMAStatements.S_oeis_a203230

-- Problem: OEIS A203230 (the statement with `products`). Writing products n = (P n, a n), we have
-- P (2m) = 3^m, and a(n+1) = digit(n) a(n) + P(n). By induction 3 a(2m) = 4m 3^m,
-- 3 a(2m+1) = (4m+3) 3^m and a(2m+2) = 4(m+1) 3^m; the recurrence follows, and with the first
-- values 0, 1, 4, 7, 24 it gives the generating function.

namespace OMA.A203230

open OMA.S_oeis_a203230

lemma prod_succ (n : ℕ) : products (n + 1) = ((products n).1 * digit n, a n * digit n + (products n).1) := by
  simp only [products, a]

lemma digit_even (m : ℕ) : digit (2 * m) = 1 := by simp [digit]
lemma digit_odd (m : ℕ) : digit (2 * m + 1) = 3 := by
  simp only [digit, show (2 * m + 1) % 2 = 1 by omega]

lemma closed (m : ℕ) : (products (2 * m)).1 = 3 ^ m ∧ 3 * a (2 * m + 1) = (4 * m + 3) * 3 ^ m ∧
    a (2 * m + 2) = 4 * (m + 1) * 3 ^ m := by
  induction m with
  | zero =>
    refine ⟨rfl, by decide, by decide⟩
  | succ m ih =>
    obtain ⟨hP, h1, h2⟩ := ih
    have hP1 : (products (2 * m + 1)).1 = 3 ^ m := by
      rw [prod_succ, digit_even, hP, mul_one]
    have hP' : (products (2 * (m + 1))).1 = 3 ^ (m + 1) := by
      rw [show 2 * (m + 1) = (2 * m + 1) + 1 by ring, prod_succ, digit_odd, hP1]; ring
    have e1 : a (2 * (m + 1) + 1) = a (2 * m + 2) + 3 ^ (m + 1) := by
      have := (congrArg Prod.snd (prod_succ (2 * (m + 1)))).trans rfl
      rw [show a (2 * (m + 1) + 1) = (products (2 * (m + 1) + 1)).2 from rfl, this]
      simp only [digit_even, hP', mul_one]
      rfl
    have h1' : 3 * a (2 * (m + 1) + 1) = (4 * ((m + 1 : ℕ) : ℤ) + 3) * 3 ^ (m + 1) := by
      rw [e1, h2]; push_cast; ring
    have e2 : a (2 * (m + 1) + 2) = 3 * a (2 * (m + 1) + 1) + 3 ^ (m + 1) := by
      have := prod_succ (2 * (m + 1) + 1)
      rw [show a (2 * (m + 1) + 2) = (products (2 * (m + 1) + 1 + 1)).2 from rfl, this]
      simp only [show 2 * (m + 1) + 1 = 2 * (m + 1) + 1 from rfl, digit_odd]
      rw [show (products (2 * (m + 1) + 1)).1 = 3 ^ (m + 1) by
        rw [prod_succ, digit_even, hP', mul_one]]
      ring
    have h2' : a (2 * (m + 1) + 2) = 4 * (((m + 1 : ℕ) : ℤ) + 1) * 3 ^ (m + 1) := by
      rw [e2, h1']; push_cast; ring
    exact ⟨hP', h1', h2'⟩

lemma a_one : a 1 = 1 := rfl

lemma odd_val (m : ℕ) : 3 * a (2 * m + 1) = (4 * m + 3) * 3 ^ m := (closed m).2.1
lemma even_val (m : ℕ) : a (2 * m + 2) = 4 * (m + 1) * 3 ^ m := (closed m).2.2

lemma recur (n : ℕ) (hn : 5 ≤ n) : a n = 6 * a (n - 2) - 9 * a (n - 4) := by
  obtain ⟨m, rfl | rfl⟩ : ∃ m, n = 2 * (m + 2) + 1 ∨ n = 2 * (m + 2) + 2 := by
    obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' n
    · exact ⟨k - 3, Or.inr (by omega)⟩
    · exact ⟨k - 2, Or.inl (by omega)⟩
  · rw [show 2 * (m + 2) + 1 - 2 = 2 * (m + 1) + 1 by omega,
      show 2 * (m + 2) + 1 - 4 = 2 * m + 1 by omega]
    have h0 := odd_val (m + 2); have h1 := odd_val (m + 1); have h2 := odd_val m
    push_cast at h0 h1 h2
    have e : (3 : ℤ) ^ (m + 2) = 9 * 3 ^ m := by ring
    have e' : (3 : ℤ) ^ (m + 1) = 3 * 3 ^ m := by ring
    rw [e] at h0; rw [e'] at h1
    nlinarith
  · rw [show 2 * (m + 2) + 2 - 2 = 2 * (m + 1) + 2 by omega,
      show 2 * (m + 2) + 2 - 4 = 2 * m + 2 by omega, even_val, even_val, even_val]
    push_cast; ring

end OMA.A203230

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a203230.main := by
  refine ⟨fun n hn => OMA.A203230.recur n (by omega), ?_⟩
  have hco : ∀ (f : PowerSeries ℤ) (c : ℤ) (k n : ℕ),
      coeff n ((C c * X ^ k) * f) = if k ≤ n then c * coeff (n - k) f else 0 := by
    intro f c k n
    rw [show (C c * X ^ k) * f = f * X ^ k * C c by ring, coeff_mul_C, coeff_mul_X_pow']
    split_ifs <;> simp [mul_comm]
  have hpoly : ((1 : PowerSeries ℤ) - C 3 * X ^ 2) ^ 2 = C 1 * X ^ 0 - C 6 * X ^ 2 + C 9 * X ^ 4 := by
    simp only [map_ofNat, map_one]; ring
  have hrhs : (X : PowerSeries ℤ) ^ 1 + C 4 * X ^ 2 + X ^ 3 = C 1 * X ^ 1 + C 4 * X ^ 2 + C 1 * X ^ 3 := by
    simp only [map_ofNat, map_one]; ring
  have v0 : OMA.S_oeis_a203230.a 0 = 0 := rfl
  have v1 : OMA.S_oeis_a203230.a 1 = 1 := rfl
  have v2 : OMA.S_oeis_a203230.a 2 = 4 := by decide
  have v3 : OMA.S_oeis_a203230.a 3 = 7 := by decide
  have v4 : OMA.S_oeis_a203230.a 4 = 24 := by decide
  rw [hpoly, hrhs]
  ext n
  simp only [sub_mul, add_mul, map_sub, map_add, coeff_mk, coeff_C_mul_X_pow, hco]
  rcases n with _ | _ | _ | _ | _ | m
  · simp [v0]
  · simp [v1]
  · simp [v2, v0]
  · simp [v1, v3]
  · simp [v2, v4, v0]
  · have h := OMA.A203230.recur (m + 5) (by omega)
    simp only [show 2 ≤ m + 5 by omega, show 4 ≤ m + 5 by omega, show 0 ≤ m + 5 by omega, if_true,
      show m + 5 ≠ 1 by omega, show m + 5 ≠ 2 by omega, show m + 5 ≠ 3 by omega, if_false,
      Nat.sub_zero]
    rw [h]; ring
