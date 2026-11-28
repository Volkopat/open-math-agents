import OMAStatements.S_oeis_a144743
import Mathlib

/-!
# OEIS A144743 and A130282: reduction to the short range `2 k² ≤ a(n)`

Write `A = a n`. A pair `(k, s)` with `s² = (A² - 1)(k² - 1) + 1` and `s ≥ 0` gives the
integer `c = A k - s`, and `(A, k, c)` solves the symmetric equation
`A² + k² + c² = 2 A k c + 2`. Hence `c` is again a solution, with square root `A c - k`,
and for `1 < k < A - 1` one has `c ≥ 2`. Writing `m ≤ K` for the two numbers `k, c`,
the inequality `(K - m)(2 A m - K - m) ≥ 0` turns the equation into
`(2 A - 2) m² ≤ A² - 2`, that is `2 m² ≤ A`.

So the conjecture for `a n` only has to be checked for `k` with `2 k² ≤ a n`.
`main` proves this, and settles `n ≤ 5` by a kernel-checked sieve with quadratic
non-residues (for `a 5 = 13441735781` the range is `2 ≤ k ≤ 81980`).

* `H1`: the short range for `a 6 = 180680260792773944179`, a finite statement
  (`2 ≤ c ≤ 9504742521`).
* `H2`: the short range for every `n ≥ 7`.
-/

namespace OMA.R_oeis_a144743_R1
open OMA.S_oeis_a144743

private theorem a_ge (n : ℕ) : 3 ≤ a n := by
  induction n with
  | zero => simp [a]
  | succ n ih =>
    simp only [a]
    nlinarith [mul_nonneg (sub_nonneg.mpr ih) (by linarith : (0 : ℤ) ≤ a n + 2)]

/-- The partner descent: a solution `k` strictly between `1` and `A - 1` yields a
solution `c ≥ 2` with `2 c² ≤ A`. -/
private theorem partner (A k s : ℤ) (hA : 3 ≤ A) (hk1 : 1 < k) (hk2 : k < A - 1)
    (hs : s ^ 2 = (A ^ 2 - 1) * (k ^ 2 - 1) + 1) :
    ∃ c t : ℤ, 2 ≤ c ∧ 2 * c ^ 2 ≤ A ∧ t ^ 2 = (A ^ 2 - 1) * (c ^ 2 - 1) + 1 := by
  obtain ⟨s0, hs0, hs0'⟩ : ∃ s0 : ℤ, 0 ≤ s0 ∧ s0 ^ 2 = (A ^ 2 - 1) * (k ^ 2 - 1) + 1 :=
    ⟨|s|, abs_nonneg s, by rw [sq_abs]; exact hs⟩
  have hAk : 0 ≤ A * k := mul_nonneg (by linarith) (by linarith)
  have hlt : s0 < A * k := by
    by_contra h
    rw [not_lt] at h
    nlinarith [mul_self_le_mul_self hAk h, mul_self_nonneg A, mul_self_nonneg k]
  obtain ⟨c1, hc1⟩ : ∃ c1 : ℤ, s0 = A * k - c1 := ⟨A * k - s0, by ring⟩
  have rel : c1 ^ 2 - 2 * A * k * c1 + A ^ 2 + k ^ 2 - 2 = 0 := by
    rw [hc1] at hs0'
    linear_combination hs0'
  have hc1pos : 1 ≤ c1 := by linarith
  have hc1ne : c1 ≠ 1 := by
    intro h1
    rw [h1] at rel
    have h2 : 2 ≤ A - k := by linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr h2) (by linarith : (0 : ℤ) ≤ A - k + 2)]
  have hc1two : 2 ≤ c1 := by omega
  have hA1 : 0 ≤ A - 1 := by linarith
  rcases le_total c1 k with h | h
  · refine ⟨c1, A * c1 - k, hc1two, ?_, by linear_combination rel⟩
    have h3 : 0 ≤ 2 * A * c1 - k - c1 := by nlinarith
    have g := mul_nonneg (sub_nonneg.mpr h) h3
    by_contra hcon
    rw [not_le] at hcon
    have h4 : A + 1 ≤ 2 * c1 ^ 2 := by linarith
    nlinarith [mul_le_mul_of_nonneg_left h4 hA1]
  · refine ⟨k, s0, by linarith, ?_, hs0'⟩
    have h3 : 0 ≤ 2 * A * k - c1 - k := by nlinarith
    have g := mul_nonneg (sub_nonneg.mpr h) h3
    by_contra hcon
    rw [not_le] at hcon
    have h4 : A + 1 ≤ 2 * k ^ 2 := by linarith
    nlinarith [mul_le_mul_of_nonneg_left h4 hA1]

/-- Soundness of the sieve: a bit mask of the squares modulo `p.1` certifies non-squares. -/
private theorem not_sq (pairs : List (ℕ × ℕ))
    (hp : ∀ p ∈ pairs, 0 < p.1 ∧ ∀ r < p.1, Nat.testBit p.2 (r * r % p.1) = true)
    (v : ℕ) (h : pairs.any (fun p => !Nat.testBit p.2 (v % p.1)) = true) (t : ℕ) :
    t * t ≠ v := by
  obtain ⟨p, hpm, hb⟩ := List.any_eq_true.mp h
  intro hv
  have h1 := (hp p hpm).2 (t % p.1) (Nat.mod_lt _ (hp p hpm).1)
  rw [← Nat.mul_mod, hv] at h1
  simp [h1] at hb

private theorem bridge (pairs : List (ℕ × ℕ))
    (hp : ∀ p ∈ pairs, 0 < p.1 ∧ ∀ r < p.1, Nat.testBit p.2 (r * r % p.1) = true)
    (A m : ℕ) (hA : 1 ≤ A) (hm : 1 ≤ m)
    (h : pairs.any (fun p => !Nat.testBit p.2 (((A * A - 1) * (m * m - 1) + 1) % p.1)) = true)
    (t : ℤ) : t ^ 2 ≠ ((A : ℤ) ^ 2 - 1) * ((m : ℤ) ^ 2 - 1) + 1 := by
  intro ht
  apply not_sq pairs hp _ h t.natAbs
  have h1 : 1 ≤ A * A := Nat.mul_pos hA hA
  have h2 : 1 ≤ m * m := Nat.mul_pos hm hm
  have key : ((t.natAbs * t.natAbs : ℕ) : ℤ) = (((A * A - 1) * (m * m - 1) + 1 : ℕ) : ℤ) := by
    rw [Nat.cast_mul, Int.natAbs_mul_self', Nat.cast_add, Nat.cast_mul, Nat.cast_sub h1,
      Nat.cast_sub h2]
    push_cast
    linear_combination ht
  exact_mod_cast key

/-- The sieve data: the masks are correct, and they certify the short ranges for
`a 2 = 19`, `a 3 = 341`, `a 4 = 115939` and `a 5 = 13441735781`. -/
private theorem sieve : ∃ pairs : List (ℕ × ℕ),
    (∀ p ∈ pairs, 0 < p.1 ∧ ∀ r < p.1, Nat.testBit p.2 (r * r % p.1) = true) ∧
    ((([(19, 2), (341, 12), (115939, 239)] : List (ℕ × ℕ)).all fun AN =>
      (List.range AN.2).all fun i => pairs.any fun p =>
        !Nat.testBit p.2 (((AN.1 * AN.1 - 1) * ((2 + i) * (2 + i) - 1) + 1) % p.1)) = true) ∧
    (((List.range 205).all fun b => (List.range 400).all fun i => pairs.any fun p =>
        !Nat.testBit p.2 (((13441735781 * 13441735781 - 1) *
          ((2 + 400 * b + i) * (2 + 400 * b + i) - 1) + 1) % p.1)) = true) :=
  ⟨[(13, 5659), (29, 332473075), (47, 4626135339999), (53, 5310023542746835), (109, 473022961816146413042658758988475), (103, 1760368345969468176824550810519), (127, 30790515292689894969866990722818747159), (233, 11407298157331152343070632129032946256988158338589093115578919345316759), (139, 264983527547230301571683161851591864167155), (179, 213639904063009026037015904849907732195616726489756219), (71, 20052041432995567487), (37, 96068509339), (131, 736595995152387833549853625256200223419), (59, 156326468341437115)],
    by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- The short range for `a 6`: no `c ≥ 2` with `2 c² ≤ a 6` makes
`(a 6 ² - 1)(c² - 1) + 1` a square. -/
def H1 : Prop := ∀ c : ℤ, 2 ≤ c → 2 * c ^ 2 ≤ a 6 →
    ¬ ∃ s : ℤ, s ^ 2 = (a 6 ^ 2 - 1) * (c ^ 2 - 1) + 1

/-- The short range for all later terms. -/
def H2 : Prop := ∀ n : ℕ, 7 ≤ n → ∀ c : ℤ, 2 ≤ c → 2 * c ^ 2 ≤ a n →
    ¬ ∃ s : ℤ, s ^ 2 = (a n ^ 2 - 1) * (c ^ 2 - 1) + 1

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a144743.main := by
  intro h1 h2 n ⟨k, hk1, hk2, s, hs⟩
  obtain ⟨c, t, hc2, hcA, ht⟩ := partner (a n) k s (a_ge n) hk1 hk2 hs
  rcases Nat.lt_or_ge n 7 with hn | hn
  · obtain ⟨pairs, hp, hsmall, hbig⟩ := sieve
    obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le (by linarith : (0 : ℤ) ≤ c)
    have hm2 : 2 ≤ m := by exact_mod_cast hc2
    have small : ∀ A N : ℕ, (A, N) ∈ ([(19, 2), (341, 12), (115939, 239)] : List (ℕ × ℕ)) →
        1 ≤ A → m < 2 + N → t ^ 2 ≠ ((A : ℤ) ^ 2 - 1) * ((m : ℤ) ^ 2 - 1) + 1 := by
      intro A N hAN hA1 hmN
      have h3 := List.all_eq_true.mp (List.all_eq_true.mp hsmall (A, N) hAN) (m - 2)
        (List.mem_range.mpr (by omega))
      have e : 2 + (m - 2) = m := by omega
      simp only [e] at h3
      exact bridge pairs hp A m hA1 (by omega) h3 t
    have hmz : (2 : ℤ) ≤ m := hc2
    interval_cases n
    · have ha : a 0 = 3 := by simp [a]
      rw [ha] at hcA
      nlinarith
    · have ha : a 1 = 5 := by simp [a]
      rw [ha] at hcA
      nlinarith
    · have ha : a 2 = 19 := by simp [a]
      rw [ha] at hcA ht
      have hm : m < 2 + 2 := by
        by_contra hh
        have h4 : (4 : ℤ) ≤ m := by exact_mod_cast not_lt.mp hh
        nlinarith
      exact small 19 2 (by simp) (by norm_num) hm (by exact_mod_cast ht)
    · have ha : a 3 = 341 := by simp [a]
      rw [ha] at hcA ht
      have hm : m < 2 + 12 := by
        by_contra hh
        have h4 : (14 : ℤ) ≤ m := by exact_mod_cast not_lt.mp hh
        nlinarith
      exact small 341 12 (by simp) (by norm_num) hm (by exact_mod_cast ht)
    · have ha : a 4 = 115939 := by simp [a]
      rw [ha] at hcA ht
      have hm : m < 2 + 239 := by
        by_contra hh
        have h4 : (241 : ℤ) ≤ m := by exact_mod_cast not_lt.mp hh
        nlinarith
      exact small 115939 239 (by simp) (by norm_num) hm (by exact_mod_cast ht)
    · have ha : a 5 = 13441735781 := by simp [a]
      rw [ha] at hcA ht
      have hm : m < 81981 := by
        by_contra hh
        have h4 : (81981 : ℤ) ≤ m := by exact_mod_cast not_lt.mp hh
        nlinarith
      have h3 := List.all_eq_true.mp (List.all_eq_true.mp hbig ((m - 2) / 400)
        (List.mem_range.mpr (by omega))) ((m - 2) % 400) (List.mem_range.mpr (by omega))
      have e : 2 + 400 * ((m - 2) / 400) + (m - 2) % 400 = m := by omega
      simp only [e] at h3
      exact bridge pairs hp 13441735781 m (by norm_num) (by omega) h3 t (by exact_mod_cast ht)
    · exact h1 m hc2 hcA ⟨t, ht⟩
  · exact h2 n hn c hc2 hcA ⟨t, ht⟩

end OMA.R_oeis_a144743_R1
