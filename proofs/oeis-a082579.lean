import OMAStatements.S_oeis_a082579

/-!
# Proof of Bala's congruence for OEIS A082579

`a(n) = n! [x^n] exp(x/(1-x)^2) = Sum_{k=0..n} n!/k! * C(n+k-1, n-k)`. The statement: for
every `k ≥ 2` and every `n`, `k` divides `a(n+k) - a(n)`.

Reindexing by `i = n - k`, the `i`-th term is `T(i, n) = n^(i) * C(2n-i-1, i)`, where `n^(i)` is
the falling factorial, and `T(i, n) = 0` for `i > n`. Since `i! * C(N, i) = N^(i)`, the term can
also be written `C(n, i) * (2n-i-1)^(i)`. Falling factorials are periodic modulo `k`
(`(x+k)^(i) ≡ x^(i)`), so moving the factor `i!` back and forth gives `T(i, n+k) ≡ T(i, n)`
modulo `k` for every `i`, and summing over `i ≤ n + k` gives the claim.
-/

namespace OMA.S_oeis_a082579

/-- Falling factorials are periodic modulo `k`. -/
theorem descFactorial_add_mod (k x i : ℕ) :
    (((x + k).descFactorial i : ℕ) : ZMod k) = ((x.descFactorial i : ℕ) : ZMod k) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Nat.descFactorial_succ, Nat.descFactorial_succ, Nat.cast_mul, Nat.cast_mul, ih]
    rcases Nat.lt_or_ge x i with h | h
    · rw [Nat.descFactorial_of_lt h]
      simp
    · have h1 : x + k - i = (x - i) + k := by omega
      rw [h1]
      simp

/-- The `i`-th term of `a(m)`, in the order of decreasing `k = m - i`. -/
def T (i m : ℕ) : ℕ := m.descFactorial i * (m + (m - i) - 1).choose i

theorem T_eq (i m : ℕ) : T i m = m.choose i * (m + (m - i) - 1).descFactorial i := by
  rw [T, Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose]
  ring

theorem a_eq (n : ℕ) : a n = ∑ i ∈ Finset.range (n + 1), T i n := by
  rw [a, ← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  have h1 : n + 1 - 1 - i = n - i := by omega
  have h2 : n - (n - i) = i := by omega
  rw [h1, h2, T, Nat.descFactorial_eq_div (by omega : i ≤ n)]

theorem T_mod (k i n : ℕ) : ((T i (n + k) : ℕ) : ZMod k) = ((T i n : ℕ) : ZMod k) := by
  rcases Nat.lt_or_ge n i with h | h
  · -- both sides vanish modulo `k`
    rw [T, T, Nat.cast_mul, Nat.cast_mul, descFactorial_add_mod, Nat.descFactorial_of_lt h]
    simp
  · rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp [T]
    · have hN : n + k + (n + k - i) - 1 = (n + (n - i) - 1 + k) + k := by omega
      calc ((T i (n + k) : ℕ) : ZMod k)
          = (((n + k).choose i : ℕ) : ZMod k)
              * (((n + (n - i) - 1 + k + k).descFactorial i : ℕ) : ZMod k) := by
            rw [T_eq, hN, Nat.cast_mul]
        _ = (((n + k).choose i : ℕ) : ZMod k)
              * (((n + (n - i) - 1).descFactorial i : ℕ) : ZMod k) := by
            rw [descFactorial_add_mod, descFactorial_add_mod]
        _ = (((n + k).descFactorial i : ℕ) : ZMod k)
              * (((n + (n - i) - 1).choose i : ℕ) : ZMod k) := by
            rw [Nat.descFactorial_eq_factorial_mul_choose (n + (n - i) - 1),
              Nat.descFactorial_eq_factorial_mul_choose (n + k)]
            push_cast
            ring
        _ = ((n.descFactorial i : ℕ) : ZMod k)
              * (((n + (n - i) - 1).choose i : ℕ) : ZMod k) := by
            rw [descFactorial_add_mod]
        _ = ((T i n : ℕ) : ZMod k) := by
            rw [T, Nat.cast_mul]

theorem a_mod (k n : ℕ) : ((a (n + k) : ℕ) : ZMod k) = ((a n : ℕ) : ZMod k) := by
  have h1 : a n = ∑ i ∈ Finset.range (n + k + 1), T i n := by
    rw [a_eq]
    apply Finset.sum_subset
    · intro i hi
      rw [Finset.mem_range] at hi ⊢
      omega
    · intro i _ hi
      rw [Finset.mem_range] at hi
      rw [T, Nat.descFactorial_of_lt (by omega), zero_mul]
  rw [h1, a_eq, Nat.cast_sum, Nat.cast_sum]
  exact Finset.sum_congr rfl fun i _ => T_mod k i n

end OMA.S_oeis_a082579

theorem OMA.solution : type_of% @OMA.S_oeis_a082579.main := by
  intro k _ n
  have h := OMA.S_oeis_a082579.a_mod k n
  have h2 : (((OMA.S_oeis_a082579.a n : ℕ) : ℤ) : ZMod k)
      = (((OMA.S_oeis_a082579.a (n + k) : ℕ) : ℤ) : ZMod k) := by
    rw [Int.cast_natCast, Int.cast_natCast, h]
  exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ k).mp h2
