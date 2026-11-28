import OMAStatements.S_oeis_a144743
import Mathlib

/-!
# OEIS A144743 and A130282: reduction to a tree of triples

Write `A = a n`. A pair `(k, s)` with `1 < k < A - 1` and `s² = (A² - 1)(k² - 1) + 1` gives, with
`c = A k - |s|`, a triple `(x, y, A)`, `2 ≤ x ≤ y ≤ A`, solving the symmetric equation
`x² + y² + z² = 2 x y z + 2`.

Vieta descent: replacing the largest entry `z` of such a triple by `2 x y - z` gives a smaller
triple, and the descent stops exactly at a root `(j, j + 1, 2 j² + 2 j - 1)` with `j ≥ 2`. So every
triple is obtained from a root by a word of the two upward moves
`(x, y, z) ↦ (y, z, 2 y z - x)` (`false`) and `(x, y, z) ↦ (x, z, 2 x z - y)` (`true`);
this is `complete` below, and `main` deduces that the conjecture says: no `a n` is the largest
entry of such a triple.

For a fixed word the largest entry is a polynomial in `j`, so each word is one family.

* `H1`: all words for `n < 8`, and the words of length at most `9` for every `n`.
* `H2`: the words of length at least `10` for `n ≥ 8`.
-/

namespace OMA.R_oeis_a144743_R2
open OMA.S_oeis_a144743

private theorem a_ge (n : ℕ) : 3 ≤ a n := by
  induction n with
  | zero => simp [a]
  | succ n ih =>
    simp only [a]
    nlinarith [mul_nonneg (sub_nonneg.mpr ih) (by linarith : (0 : ℤ) ≤ a n + 2)]

/-- A solution `k` gives a sorted triple with largest entry `A`. -/
private theorem triple_of_sol (A k s : ℤ) (hA : 3 ≤ A) (hk1 : 1 < k) (hk2 : k < A - 1)
    (hs : s ^ 2 = (A ^ 2 - 1) * (k ^ 2 - 1) + 1) :
    ∃ x y : ℤ, 2 ≤ x ∧ x ≤ y ∧ y ≤ A ∧ x ^ 2 + y ^ 2 + A ^ 2 = 2 * x * y * A + 2 := by
  obtain ⟨s0, hs0, hs0'⟩ : ∃ s0 : ℤ, 0 ≤ s0 ∧ s0 ^ 2 = (A ^ 2 - 1) * (k ^ 2 - 1) + 1 :=
    ⟨|s|, abs_nonneg s, by rw [sq_abs]; exact hs⟩
  have hkA : k ≤ A := by linarith
  have hAk : 0 ≤ A * k := mul_nonneg (by linarith) (by linarith)
  have hlt : s0 < A * k := by
    by_contra h
    rw [not_lt] at h
    nlinarith [mul_self_le_mul_self hAk h, mul_self_nonneg A, mul_self_nonneg k]
  obtain ⟨c, hc⟩ : ∃ c : ℤ, s0 = A * k - c := ⟨A * k - s0, by ring⟩
  have rel : c ^ 2 - 2 * A * k * c + A ^ 2 + k ^ 2 - 2 = 0 := by
    rw [hc] at hs0'
    linear_combination hs0'
  have hc1 : 1 ≤ c := by linarith
  have hcne : c ≠ 1 := by
    intro h1
    rw [h1] at rel
    have h2 : 2 ≤ A - k := by linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr h2) (by linarith : (0 : ℤ) ≤ A - k + 2)]
  have hc2 : 2 ≤ c := by omega
  have hcA : c < A := by
    by_contra h
    rw [not_lt] at h
    have h3 : s0 ≤ A * (k - 1) := by rw [hc]; nlinarith
    have h4 := mul_self_le_mul_self hs0 h3
    nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ k - 2) (mul_self_nonneg A),
      mul_self_le_mul_self (by linarith : (0 : ℤ) ≤ k) hkA]
  rcases le_total k c with h | h
  · exact ⟨k, c, by linarith, h, le_of_lt hcA, by linear_combination rel⟩
  · exact ⟨c, k, hc2, h, hkA, by linear_combination rel⟩

/-- Vieta descent: every sorted triple with entries at least `2` comes from a root by a word of
upward moves. -/
private theorem complete : ∀ (m : ℕ) (x y z : ℤ), z.toNat = m → 2 ≤ x → x ≤ y → y ≤ z →
    x ^ 2 + y ^ 2 + z ^ 2 = 2 * x * y * z + 2 →
    ∃ (w : List Bool) (j : ℤ), 2 ≤ j ∧
      w.foldr (fun b t => if b then (t.1, t.2.2, 2 * t.1 * t.2.2 - t.2.1)
        else (t.2.1, t.2.2, 2 * t.2.1 * t.2.2 - t.1))
        ((j, j + 1, 2 * j * j + 2 * j - 1) : ℤ × ℤ × ℤ) = (x, y, z) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro x y z hm hx hxy hyz h
    have hprod : z * (2 * x * y - z) = x ^ 2 + y ^ 2 - 2 := by linear_combination (-1 : ℤ) * h
    have hpos : 1 ≤ 2 * x * y - z := by
      by_contra hneg
      rw [not_le] at hneg
      have h0 : 2 * x * y - z ≤ 0 := by linarith
      nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ z) (by linarith : (0 : ℤ) ≤ -(2 * x * y - z)),
        mul_self_nonneg x, mul_self_nonneg y, mul_nonneg (by linarith : (0 : ℤ) ≤ x - 2)
          (by linarith : (0 : ℤ) ≤ x + 2)]
    have hxx : x * x ≤ y * y := mul_self_le_mul_self (by linarith) hxy
    have hlt : 2 * x * y - z < y := by
      by_contra hge
      rw [not_lt] at hge
      have h1 := mul_nonneg (sub_nonneg.mpr hyz) (sub_nonneg.mpr hge)
      nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ x - 2) (mul_self_nonneg y)]
    have hyz' : y < z := by
      rcases lt_or_eq_of_le hyz with h1 | h1
      · exact h1
      · exfalso
        rw [← h1] at hlt
        nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ x - 2) (by linarith : (0 : ℤ) ≤ y)]
    have hmeas : y.toNat < m := by
      rw [← hm]
      exact (Int.toNat_lt_toNat (by linarith)).mpr hyz'
    have heq' : x ^ 2 + y ^ 2 + (2 * x * y - z) ^ 2 = 2 * x * y * (2 * x * y - z) + 2 := by
      linear_combination h
    rcases eq_or_lt_of_le hpos with h1 | h1
    · rw [← h1] at heq'
      have hd : (y - x - 1) * (y - x + 1) = 0 := by linear_combination heq'
      have hyx : y = x + 1 := by
        rcases mul_eq_zero.mp hd with h2 | h2
        · linarith
        · linarith
      refine ⟨[], x, hx, ?_⟩
      simp only [List.foldr_nil]
      refine Prod.ext rfl (Prod.ext (by simpa using hyx.symm) ?_)
      simp only
      rw [hyx] at h1
      linarith
    · rcases le_or_gt (2 * x * y - z) x with h2 | h2
      · obtain ⟨w, j, hj, hT⟩ := ih y.toNat hmeas (2 * x * y - z) x y rfl (by linarith) h2 hxy
          (by linear_combination heq')
        refine ⟨false :: w, j, hj, ?_⟩
        simp only [List.foldr_cons, hT, Bool.false_eq_true, if_false]
        refine Prod.ext rfl (Prod.ext rfl ?_)
        simp only
        ring
      · obtain ⟨w, j, hj, hT⟩ := ih y.toNat hmeas x (2 * x * y - z) y rfl hx (by linarith)
          (by linarith) (by linear_combination heq')
        refine ⟨true :: w, j, hj, ?_⟩
        simp only [List.foldr_cons, hT, if_true]
        refine Prod.ext rfl (Prod.ext rfl ?_)
        simp only
        ring

/-- The provable part: every word for `n < 8`, and the words of length at most `9` for all `n`. -/
def H1 : Prop := ∀ (n : ℕ) (w : List Bool) (j : ℤ), (n < 8 ∨ w.length ≤ 9) → 2 ≤ j →
    (w.foldr (fun b t => if b then (t.1, t.2.2, 2 * t.1 * t.2.2 - t.2.1)
        else (t.2.1, t.2.2, 2 * t.2.1 * t.2.2 - t.1))
      ((j, j + 1, 2 * j * j + 2 * j - 1) : ℤ × ℤ × ℤ)).2.2 ≠ a n

/-- The open part: the words of length at least `10` for `n ≥ 8`. -/
def H2 : Prop := ∀ (n : ℕ) (w : List Bool) (j : ℤ), 8 ≤ n → 9 < w.length → 2 ≤ j →
    (w.foldr (fun b t => if b then (t.1, t.2.2, 2 * t.1 * t.2.2 - t.2.1)
        else (t.2.1, t.2.2, 2 * t.2.1 * t.2.2 - t.1))
      ((j, j + 1, 2 * j * j + 2 * j - 1) : ℤ × ℤ × ℤ)).2.2 ≠ a n

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a144743.main := by
  intro h1 h2 n ⟨k, hk1, hk2, s, hs⟩
  obtain ⟨x, y, hx, hxy, hyA, h⟩ := triple_of_sol (a n) k s (a_ge n) hk1 hk2 hs
  obtain ⟨w, j, hj, hT⟩ := complete _ x y (a n) rfl hx hxy hyA h
  have hz : (w.foldr (fun b t => if b then (t.1, t.2.2, 2 * t.1 * t.2.2 - t.2.1)
        else (t.2.1, t.2.2, 2 * t.2.1 * t.2.2 - t.1))
      ((j, j + 1, 2 * j * j + 2 * j - 1) : ℤ × ℤ × ℤ)).2.2 = a n := by rw [hT]
  rcases Nat.lt_or_ge n 8 with hn | hn
  · exact h1 n w j (Or.inl hn) hj hz
  · rcases Nat.lt_or_ge 9 w.length with hw | hw
    · exact h2 n w j hn hw hj hz
    · exact h1 n w j (Or.inr hw) hj hz

end OMA.R_oeis_a144743_R2
