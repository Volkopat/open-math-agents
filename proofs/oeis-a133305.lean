import OMAStatements.S_oeis_a133305
import Mathlib

-- Credit: @hermitokatt (Lean proof with Claude Code)

/-!
Proof of R. J. Mathar's recurrence for A133305.

With `F(n, i) = C(n, i) C(n, i+1) 4^i 5^(n-i)`, `n a(n) = Σ_i F(n, i)` for every `n` (both sides vanish
at `n = 0`). Zeilberger's algorithm gives, for all `n, i`,
`(n+1)(n+2) F(n, i) - 9(n+2)(2n+3) F(n+1, i) + (n+1)(n+3) F(n+2, i) = G(n, i+1) - G(n, i)`,
`G(n, i) = -5 i (16n^2 - 12in + 43n + i^2 - 13i + 27) C(n+1, i) C(n+2, i) 4^i 5^(n-i) / (n+1)`.
This is checked as a rational identity after writing every binomial through `C(n+2, i)` (Pascal-type
ratio identities, valid over `ℚ` for all `i`). Summing over `i < n+3`, where `G` vanishes at both ends,
gives the recurrence for `n a(n)`; dividing by `(n+1)(n+2)` gives the conjecture.
-/

namespace OMA.A133305Proof

open OMA.S_oeis_a133305

/-- `C(m, k+1) (k+1) = C(m, k) (m - k)` over `ℚ`, for all `m, k`. -/
theorem succ_right_q (m k : ℕ) : (m.choose (k + 1) : ℚ) * ((k : ℚ) + 1) = (m.choose k : ℚ) * ((m : ℚ) - k) := by
  rcases Nat.lt_or_ge m k with h | h
  · rw [Nat.choose_eq_zero_of_lt h, Nat.choose_eq_zero_of_lt (by omega : m < k + 1)]
    simp
  · have e := Nat.choose_succ_right_eq m k
    have e' : ((m.choose (k + 1) * (k + 1) : ℕ) : ℚ) = ((m.choose k * (m - k) : ℕ) : ℚ) := by rw [e]
    push_cast [Nat.cast_sub h] at e'
    linear_combination e'

/-- `C(m, k) (m+1) = C(m+1, k) (m+1-k)` over `ℚ`, for all `m, k`. -/
theorem mul_succ_q (m k : ℕ) :
    (m.choose k : ℚ) * ((m : ℚ) + 1) = ((m + 1).choose k : ℚ) * ((m : ℚ) + 1 - k) := by
  rcases Nat.lt_or_ge (m + 1) k with h | h
  · rw [Nat.choose_eq_zero_of_lt h, Nat.choose_eq_zero_of_lt (by omega : m < k)]
    simp
  · have e := Nat.choose_mul_succ_eq m k
    have e' : ((m.choose k * (m + 1) : ℕ) : ℚ) = (((m + 1).choose k * (m + 1 - k) : ℕ) : ℚ) := by rw [e]
    push_cast [Nat.cast_sub h] at e'
    linear_combination e'

/-- The summand of `n a(n)`: `C(n, i) C(n, i+1) 4^i 5^(n-i)`. -/
def F (n i : ℕ) : ℚ := (n.choose i : ℚ) * (n.choose (i + 1) : ℚ) * 4 ^ i * 5 ^ n / 5 ^ i

/-- Zeilberger's certificate. -/
def G (n i : ℕ) : ℚ :=
  -5 * (i : ℚ) * (16 * (n : ℚ) ^ 2 - 12 * (i : ℚ) * n + 43 * n + (i : ℚ) ^ 2 - 13 * i + 27)
    * ((n + 1).choose i : ℚ) * ((n + 2).choose i : ℚ) * 4 ^ i * 5 ^ n / (5 ^ i * ((n : ℚ) + 1))

theorem tele (n i : ℕ) :
    ((n : ℚ) + 1) * ((n : ℚ) + 2) * F n i - 9 * ((n : ℚ) + 2) * (2 * (n : ℚ) + 3) * F (n + 1) i
      + ((n : ℚ) + 1) * ((n : ℚ) + 3) * F (n + 2) i = G n (i + 1) - G n i := by
  have hi1 : ((i : ℚ) + 1) ≠ 0 := by positivity
  have hn1 : ((n : ℚ) + 1) ≠ 0 := by positivity
  have hn2 : (((n + 1 : ℕ) : ℚ) + 1) ≠ 0 := by positivity
  have hn2' : ((n : ℚ) + 1 + 1) ≠ 0 := by positivity
  have hn2'' : ((n : ℚ) + 2) ≠ 0 := by positivity
  have e5 := (eq_div_iff hi1).mpr (succ_right_q n i)
  have e4 := (eq_div_iff hi1).mpr (succ_right_q (n + 1) i)
  have e3 := (eq_div_iff hi1).mpr (succ_right_q (n + 2) i)
  have e2 := (eq_div_iff hn1).mpr (mul_succ_q n i)
  have e1 := (eq_div_iff hn2).mpr (mul_succ_q (n + 1) i)
  rw [show n + 1 + 1 = n + 2 by ring] at e1
  unfold F G
  rw [e5, e4, e3, e2, e1]
  push_cast
  field_simp
  ring

theorem F_zero (n i : ℕ) (h : n ≤ i) : F n i = 0 := by
  unfold F
  rw [Nat.choose_eq_zero_of_lt (by omega : n < i + 1)]
  simp

theorem sum_ext (n d : ℕ) : ∑ i ∈ Finset.range (n + d), F n i = ∑ i ∈ Finset.range n, F n i := by
  induction d with
  | zero => rfl
  | succ d ih => rw [← add_assoc, Finset.sum_range_succ, ih, F_zero n (n + d) (by omega), add_zero]

theorem b_eq (n : ℕ) : (n : ℚ) * a n = ∑ i ∈ Finset.range n, F n i := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn' : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    unfold a
    rw [if_neg (by omega), mul_comm, div_mul_cancel₀ _ hn']
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Finset.mem_range] at hi
    unfold F
    rw [pow_sub₀ _ (by norm_num : (5 : ℚ) ≠ 0) hi.le]
    ring

/-- Zeilberger's recurrence for `b(n) = n a(n)`, summed. -/
theorem sumZ (n : ℕ) :
    ((n : ℚ) + 1) * ((n : ℚ) + 2) * ((n : ℚ) * a n)
      - 9 * ((n : ℚ) + 2) * (2 * (n : ℚ) + 3) * (((n + 1 : ℕ) : ℚ) * a (n + 1))
      + ((n : ℚ) + 1) * ((n : ℚ) + 3) * (((n + 2 : ℕ) : ℚ) * a (n + 2)) = 0 := by
  have key : ∑ i ∈ Finset.range (n + 3), (((n : ℚ) + 1) * ((n : ℚ) + 2) * F n i
      - 9 * ((n : ℚ) + 2) * (2 * (n : ℚ) + 3) * F (n + 1) i
      + ((n : ℚ) + 1) * ((n : ℚ) + 3) * F (n + 2) i) = 0 := by
    rw [Finset.sum_congr rfl (fun i _ => tele n i), Finset.sum_range_sub]
    unfold G
    rw [Nat.choose_eq_zero_of_lt (show n + 1 < n + 3 by omega)]
    simp
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at key
  have h0 := b_eq n
  have h1 := b_eq (n + 1)
  have h2 := b_eq (n + 2)
  rw [← sum_ext n 3] at h0
  rw [← sum_ext (n + 1) 2, show n + 1 + 2 = n + 3 by ring] at h1
  rw [← sum_ext (n + 2) 1, show n + 2 + 1 = n + 3 by ring] at h2
  linear_combination ((n : ℚ) + 1) * ((n : ℚ) + 2) * h0
    - 9 * ((n : ℚ) + 2) * (2 * (n : ℚ) + 3) * h1 + ((n : ℚ) + 1) * ((n : ℚ) + 3) * h2 + key

end OMA.A133305Proof

open OMA.S_oeis_a133305 OMA.A133305Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a133305.main := by
  intro N hN
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 2 := ⟨N - 2, by omega⟩
  rw [show n + 2 - 1 = n + 1 by omega, show n + 2 - 2 = n by omega]
  have key := sumZ n
  push_cast at key ⊢
  have hD : ((n : ℚ) + 1) * ((n : ℚ) + 2) ≠ 0 := by positivity
  refine (mul_eq_zero.mp ?_).resolve_left hD
  linear_combination key
