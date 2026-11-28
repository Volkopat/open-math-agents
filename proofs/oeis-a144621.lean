import OMAStatements.S_oeis_a144621
import Mathlib

/-
A144621: a(n+1) = det M(n) for n > 2, where M(n) is the 2^n x 2^n matrix with entries
1 + v_2(i+j+1) (0-based i, j).

Method. Work with the two-parameter family K n x y = x * M n + y * J n, where J n is the
anti-diagonal permutation matrix; its (i, j) entry is c n x y (i+j+1) with
c n x y m = x (1 + v_2 m) + y [m = 2^n].

Splitting the index set as 2^(n+1) = 2^n + 2^n gives the block form
  K (n+1) x y = [[P, Q], [Q, P]],   P = K n x 0,   Q = K n x (x+y),
because v_2(m + 2^n) = v_2(m) + [m = 2^n] and v_2(m + 2^(n+1)) = v_2(m) for 0 < m < 2^(n+1).
Hence (blk_det)
  det K (n+1) x y = det (P+Q) * det (P-Q) = det K n (2x) (x+y) * det K n 0 (-(x+y)).

From this recursion alone: det K (n+1) 0 z is even in z (ev), and by induction (R)
  det K (n+2) x y * ((2^(n+2)-1) x + y) = ((2^(n+3)-1) x + y) * (det K (n+1) x y)^2.
The sequence satisfies the same relation (A): a(n+2) (2^(n+1)-1) = (2^(n+2)-1) a(n+1)^2,
and a(3) = 21 = det K 2 1 0, so a(n+3) = det K (n+2) 1 0 = det M (n+2) for every n (key).
-/

namespace OMA.P144621
open OMA.S_oeis_a144621 Matrix

/-- Entry function: `x * (1 + v₂ m) + y * [m = 2 ^ n]`. -/
def c (n : ℕ) (x y : ℤ) (m : ℕ) : ℤ :=
  x * (1 + padicValNat 2 m) + if m = 2 ^ n then y else 0

/-- `x • M n + y • J n`, where `J n` is the anti-diagonal permutation matrix. -/
def K (n : ℕ) (x y : ℤ) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℤ :=
  of fun i j => c n x y (i.val + j.val + 1)

lemma v_add {k m : ℕ} (h0 : m ≠ 0) (h : ¬ 2 ^ k ∣ m) :
    padicValNat 2 (m + 2 ^ k) = padicValNat 2 m := by
  obtain ⟨a, b, hb, rfl⟩ := Nat.exists_eq_two_pow_mul_odd h0
  have hak : a < k := by
    by_contra hc
    exact h (Dvd.dvd.mul_right (pow_dvd_pow 2 (not_lt.1 hc)) b)
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hak
  have e : 2 ^ a * b + 2 ^ (a + d + 1) = 2 ^ a * (b + 2 * 2 ^ d) := by ring
  have h2 : ¬ 2 ∣ b := hb.not_two_dvd_nat
  rw [e, padicValNat.mul (by positivity) (by positivity), padicValNat.mul (by positivity) hb.pos.ne',
    padicValNat.eq_zero_of_not_dvd h2, padicValNat.eq_zero_of_not_dvd (n := b + 2 * 2 ^ d)]
  omega

lemma c1 {n m : ℕ} (x y : ℤ) (h : m < 2 ^ (n + 1)) : c (n + 1) x y m = c n x 0 m := by
  simp [c, h.ne]

lemma c2 {n m : ℕ} (x y : ℤ) (h0 : m ≠ 0) (h : m < 2 ^ (n + 1)) :
    c (n + 1) x y (m + 2 ^ n) = c n x (x + y) m := by
  unfold c
  by_cases hm : m = 2 ^ n
  · subst hm
    rw [← two_mul, ← pow_succ', padicValNat.prime_pow, padicValNat.prime_pow]
    simp; ring
  · have hd : ¬ 2 ^ n ∣ m := fun hd => hm (Nat.eq_of_dvd_of_lt_two_mul h0 hd (by rwa [← pow_succ']))
    have : m + 2 ^ n ≠ 2 ^ (n + 1) := by rw [pow_succ']; omega
    rw [v_add h0 hd]; simp [hm, this]

lemma c3 {n m : ℕ} (x y : ℤ) (h0 : m ≠ 0) (h : m < 2 ^ (n + 1)) :
    c (n + 1) x y (m + 2 ^ (n + 1)) = c n x 0 m := by
  unfold c
  rw [v_add h0 (Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero h0) h)]; simp [h0]

/-- The index split `2 ^ (n + 1) = 2 ^ n + 2 ^ n`. -/
def e (n : ℕ) : Fin (2 ^ n) ⊕ Fin (2 ^ n) ≃ Fin (2 ^ (n + 1)) :=
  finSumFinEquiv.trans (finCongr (by ring))

lemma blk (n : ℕ) (x y : ℤ) : (K (n + 1) x y).submatrix (e n) (e n) =
    fromBlocks (K n x 0) (K n x (x + y)) (K n x (x + y)) (K n x 0) := by
  have h2 : 2 ^ (n + 1) = 2 * 2 ^ n := pow_succ' 2 n
  ext (i | i) (j | j) <;> simp [K, e]
  · exact c1 x y (by omega)
  · rw [← c2 x y (m := i + j + 1) (by omega) (by omega)]; congr 1; ring
  · rw [← c2 x y (m := i + j + 1) (by omega) (by omega)]; congr 1; ring
  · rw [← c3 x y (m := i + j + 1) (by omega) (by omega)]; congr 1; ring

lemma det_bb {m : Type*} [Fintype m] [DecidableEq m] (A B : Matrix m m ℤ) :
    (fromBlocks A B B A).det = (A + B).det * (A - B).det := by
  have h : fromBlocks 1 0 1 1 * fromBlocks A B B A * fromBlocks 1 0 (-1) 1 =
      fromBlocks (A - B) B 0 (A + B) := by
    simp [fromBlocks_multiply, sub_eq_add_neg, add_comm]
    abel
  have := congrArg det h
  rw [det_mul, det_mul, det_fromBlocks_zero₁₂, det_fromBlocks_zero₁₂, det_fromBlocks_zero₂₁] at this
  simpa [mul_comm] using this

lemma blk_det (n : ℕ) (x y : ℤ) :
    (K (n + 1) x y).det = (K n (2 * x) (x + y)).det * (K n 0 (-(x + y))).det := by
  rw [← det_submatrix_equiv_self (e n), blk, det_bb]
  congr 2 <;> ext i j <;> simp [K, c] <;> split_ifs <;> ring

lemma D0 (x y : ℤ) : (K 0 x y).det = x + y := by
  show (K 0 x y : Matrix (Fin 1) (Fin 1) ℤ).det = x + y
  rw [det_fin_one]; simp [K, c]

lemma ev (n : ℕ) (z : ℤ) : (K (n + 1) 0 (-z)).det = (K (n + 1) 0 z).det := by
  rw [blk_det, blk_det]; simp [mul_comm]

lemma R (n : ℕ) : ∀ x y : ℤ, (K (n + 2) x y).det * ((2 ^ (n + 2) - 1) * x + y) =
    ((2 ^ (n + 3) - 1) * x + y) * (K (n + 1) x y).det ^ 2 := by
  induction n with
  | zero => intro x y; simp only [blk_det, D0]; ring
  | succ n ih =>
    intro x y
    have h := ih (2 * x) (x + y)
    rw [blk_det (n + 2), blk_det (n + 1) x y, blk_det (n + 1) 0, ev n]
    simp only [mul_zero, zero_add] at *
    rw [ev n (x + y)]
    linear_combination (K (n + 1) 0 (x + y)).det ^ 2 * h

lemma A (n : ℕ) : a (n + 2) * (2 ^ (n + 1) - 1) = (2 ^ (n + 2) - 1) * a (n + 1) ^ 2 := by
  induction n with
  | zero => simp [a]
  | succ n ih =>
    rw [show a (n + 1 + 2) = a (n + 2) * (3 * a (n + 2) - 2 * a (n + 1) ^ 2) from rfl]
    linear_combination (2 * a (n + 2)) * ih

lemma key (n : ℕ) : a (n + 3) = (K (n + 2) 1 0).det := by
  induction n with
  | zero => simp only [blk_det, D0]; simp [a]
  | succ n ih =>
    have h1 := A (n + 2)
    have h2 := R (n + 1) 1 0
    rw [← ih] at h2
    have h3 : (1 : ℤ) < 2 ^ (n + 3) := one_lt_pow₀ (by norm_num) (by omega)
    refine mul_right_cancel₀ (b := (2 : ℤ) ^ (n + 3) - 1) (by omega) ?_
    linear_combination h1 - h2

end OMA.P144621

theorem OMA.solution : type_of% @OMA.S_oeis_a144621.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  rw [OMA.P144621.key (k + 1)]
  congr 1
  ext i j
  simp [OMA.S_oeis_a144621.M, OMA.P144621.K, OMA.P144621.c]
