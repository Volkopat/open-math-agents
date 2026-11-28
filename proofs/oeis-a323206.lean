import OMAStatements.S_oeis_a323206
import Mathlib

/-!
# A323206: parity of `hypergeometric([-k, k+1], [-k-1], n)`

* The `j`-th hypergeometric term is `c(k, j) n^j` with the ballot number
  `c(k, j) = binomial(k+j, k) - binomial(k+j, k+1)` (`term_eq`), so `A(n, k) = Z` is an integer.
* `n` even: `Z = 1 + n W` is odd.
* `n` odd: `Z ≡ S = ∑_j c(k, j) = binomial(2k+1, k+1) - binomial(2k+1, k+2) (mod 2)`, and
  `S (2k+3) = binomial(2k+3, k+1)`. By Lucas' theorem modulo `2` (the binary form
  `odd_choose_add_iff`, reused from the merged proof `proofs/oeis-a000139.lean` by @Heart-galaxy),
  this binomial is odd iff `k+1` and `k+2` share no binary digit, i.e. iff `k + 2` is a power of `2`.
-/

namespace OMA.A323206Proof

open Polynomial OMA.S_oeis_a323206 Finset

/-- The ballot numbers. -/
def c (k j : ℕ) : ℤ := ((k + j).choose k : ℤ) - ((k + j).choose (k + 1) : ℤ)

lemma poch_neg (k j : ℕ) : (ascPochhammer ℚ j).eval (-(k : ℚ)) * ((k : ℚ) + 1) =
    ((k : ℚ) + 1 - j) * (ascPochhammer ℚ j).eval (-(k : ℚ) - 1) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [ascPochhammer_succ_eval, ascPochhammer_succ_eval]
    have e : (ascPochhammer ℚ j).eval (-(k : ℚ)) * (-(k : ℚ) + j) * ((k : ℚ) + 1) =
        ((ascPochhammer ℚ j).eval (-(k : ℚ)) * ((k : ℚ) + 1)) * (-(k : ℚ) + j) := by ring
    rw [e, ih]; push_cast; ring

lemma poch_pos (k j : ℕ) :
    (ascPochhammer ℚ j).eval ((k : ℚ) + 1) = ((k + j).choose j : ℚ) * (j.factorial : ℚ) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [ascPochhammer_succ_eval, ih, show k + (j + 1) = k + j + 1 by ring, Nat.factorial_succ]
    have h := Nat.add_one_mul_choose_eq (k + j) j
    have hq : ((k : ℚ) + j + 1) * ((k + j).choose j : ℚ) =
        ((k + j + 1).choose (j + 1) : ℚ) * ((j : ℚ) + 1) := by exact_mod_cast h
    push_cast
    linear_combination (j.factorial : ℚ) * hq

lemma poch_ne (k j : ℕ) (hj : j ≤ k) : (ascPochhammer ℚ j).eval (-(k : ℚ) - 1) ≠ 0 := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [ascPochhammer_succ_eval]
    refine mul_ne_zero (ih (by omega)) ?_
    have hlt : (j : ℚ) < k + 1 := by exact_mod_cast (show j < k + 1 by omega)
    intro h; linarith

lemma ballot (k j : ℕ) :
    ((k : ℚ) + 1 - j) / ((k : ℚ) + 1) * ((k + j).choose j : ℚ) = (c k j : ℚ) := by
  have h1 : ((k + j).choose (k + 1) : ℚ) * ((k : ℚ) + 1) = ((k + j).choose k : ℚ) * j := by
    have := Nat.choose_succ_right_eq (k + j) k
    rw [show k + j - k = j by omega] at this
    exact_mod_cast this
  have hs : (k + j).choose j = (k + j).choose k := (Nat.choose_symm_add).symm
  have hk1 : ((k : ℚ) + 1) ≠ 0 := by positivity
  rw [div_mul_eq_mul_div, div_eq_iff hk1, hs]
  unfold c; push_cast
  linear_combination h1

lemma term_eq (n k j : ℕ) (hj : j ≤ k) : term n k j = (c k j : ℚ) * (n : ℚ) ^ j := by
  have hq := poch_ne k j hj
  have hk1 : ((k : ℚ) + 1) ≠ 0 := by positivity
  have hf : (j.factorial : ℚ) ≠ 0 := by positivity
  have hP : (ascPochhammer ℚ j).eval (-(k : ℚ)) =
      ((k : ℚ) + 1 - j) * (ascPochhammer ℚ j).eval (-(k : ℚ) - 1) / ((k : ℚ) + 1) := by
    rw [eq_div_iff hk1]; exact poch_neg k j
  unfold term
  rw [hP, poch_pos, ← ballot k j]
  field_simp

lemma A_eq (n k : ℕ) :
    A n k = ((∑ j ∈ range (k + 1), c k j * (n : ℤ) ^ j : ℤ) : ℚ) := by
  unfold A; push_cast
  refine Finset.sum_congr rfl (fun j hj => ?_)
  rw [term_eq n k j (by simp at hj; omega)]

lemma hs0 (k N : ℕ) : ∑ j ∈ range N, (k + j).choose k = (k + N).choose (k + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, ih, show k + (N + 1) = k + N + 1 by ring, Nat.choose_succ_succ]; ring

lemma hs1 (k N : ℕ) : ∑ j ∈ range N, (k + j).choose (k + 1) = (k + N).choose (k + 2) := by
  induction N with
  | zero => simp [Nat.choose_eq_zero_of_lt]
  | succ N ih =>
    rw [sum_range_succ, ih, show k + (N + 1) = k + N + 1 by ring, Nat.choose_succ_succ]; ring

lemma sum_c (k : ℕ) : ∑ j ∈ range (k + 1), c k j =
    ((2 * k + 1).choose (k + 1) : ℤ) - ((2 * k + 1).choose (k + 2) : ℤ) := by
  have e0 : ∑ j ∈ range (k + 1), (((k + j).choose k : ℕ) : ℤ) = ((2 * k + 1).choose (k + 1) : ℤ) := by
    rw [← Nat.cast_sum, hs0, show k + (k + 1) = 2 * k + 1 by ring]
  have e1 : ∑ j ∈ range (k + 1), (((k + j).choose (k + 1) : ℕ) : ℤ) =
      ((2 * k + 1).choose (k + 2) : ℤ) := by
    rw [← Nat.cast_sum, hs1, show k + (k + 1) = 2 * k + 1 by ring]
  simp only [c, sum_sub_distrib, e0, e1]

lemma sum_c_mul (k : ℕ) : (∑ j ∈ range (k + 1), c k j) * (2 * k + 3) =
    ((2 * k + 3).choose (k + 1) : ℤ) := by
  rw [sum_c]
  have h1 := Nat.choose_succ_right_eq (2 * k + 1) (k + 1)
  rw [show 2 * k + 1 - (k + 1) = k by omega] at h1
  have h2 := Nat.choose_succ_succ (2 * k + 1) k
  have h2' : (2 * k + 1).choose k = (2 * k + 1).choose (k + 1) := (Nat.choose_symm_half k).symm
  have h3 := Nat.choose_mul_succ_eq (2 * k + 2) (k + 1)
  rw [show 2 * k + 2 + 1 - (k + 1) = k + 2 by omega] at h3
  have q1 : ((2 * k + 1).choose (k + 2) : ℤ) * ((k : ℤ) + 2) = ((2 * k + 1).choose (k + 1) : ℤ) * k := by
    exact_mod_cast h1
  have q2 : ((2 * k + 2).choose (k + 1) : ℤ) = 2 * ((2 * k + 1).choose (k + 1) : ℤ) := by
    rw [show 2 * k + 2 = 2 * k + 1 + 1 by ring]
    have := congrArg (fun x : ℕ => (x : ℤ)) h2; push_cast at this; rw [this, h2']; ring
  have q3 : ((2 * k + 2).choose (k + 1) : ℤ) * (2 * k + 3) = ((2 * k + 3).choose (k + 1) : ℤ) * (k + 2) := by
    have := congrArg (fun x : ℕ => (x : ℤ)) h3; push_cast at this
    rw [show (2 : ℤ) * k + 2 + 1 = 2 * k + 3 by ring] at this
    rw [show 2 * k + 3 = 2 * k + 2 + 1 by ring]; linear_combination this
  have hk2 : ((k : ℤ) + 2) ≠ 0 := by positivity
  apply mul_right_cancel₀ hk2
  linear_combination -(2 * (k : ℤ) + 3) * q1 - (2 * (k : ℤ) + 3) * q2 + q3

lemma choose_low_bits (x y : ℕ) : ((x + y) % 2).choose (x % 2) =
    if x % 2 = 1 ∧ y % 2 = 1 then 0 else 1 := by
  rw [Nat.add_mod]
  have hx := Nat.mod_lt x (by decide : 0 < 2)
  have hy := Nat.mod_lt y (by decide : 0 < 2)
  generalize x % 2 = u at hx ⊢
  generalize y % 2 = v at hy ⊢
  interval_cases u <;> interval_cases v <;> decide

/-- A binary form of Lucas's theorem in terms of disjoint bit positions. -/
theorem odd_choose_add_iff (x y : ℕ) :
    Odd ((x + y).choose x) ↔ ∀ i : ℕ, ¬ (x.testBit i ∧ y.testBit i) := by
  induction x using Nat.strong_induction_on generalizing y with
  | h x ih =>
    by_cases hx : x = 0
    · subst x
      simp
    have hlt : x / 2 < x := Nat.div_lt_self (Nat.pos_of_ne_zero hx) (by decide)
    have hlucas := @Choose.choose_modEq_choose_mod_mul_choose_div_nat
      (x + y) x 2 ⟨Nat.prime_two⟩
    simp only [Nat.ModEq] at hlucas
    rw [Nat.odd_iff, hlucas, choose_low_bits]
    by_cases hcollision : x % 2 = 1 ∧ y % 2 = 1
    · have hbits : ¬ ∀ i : ℕ, ¬ (x.testBit i ∧ y.testBit i) := by
        intro h
        exact h 0 ⟨Nat.mod_two_eq_one_iff_testBit_zero.mp hcollision.1,
          Nat.mod_two_eq_one_iff_testBit_zero.mp hcollision.2⟩
      rw [if_pos hcollision, zero_mul]
      exact iff_of_false (by decide) hbits
    · have hadd : (x + y) / 2 = x / 2 + y / 2 := by omega
      rw [if_neg hcollision, one_mul, hadd, ← Nat.odd_iff, ih (x / 2) hlt (y / 2)]
      constructor
      · intro h i
        cases i with
        | zero => simpa only [← Nat.mod_two_eq_one_iff_testBit_zero] using hcollision
        | succ i => simpa only [Nat.testBit_succ] using h i
      · intro h i
        simpa only [Nat.testBit_div_two] using h (i + 1)

lemma bits_succ (x : ℕ) : (∀ i : ℕ, ¬ (x.testBit i ∧ (x + 1).testBit i)) ↔ ∃ j, x + 1 = 2 ^ j := by
  induction x using Nat.strong_induction_on with
  | h x ih =>
    rcases Nat.even_or_odd x with ⟨y, hy⟩ | ⟨y, hy⟩
    · by_cases hy0 : y = 0
      · subst hy0; simp at hy; subst hy; exact ⟨fun _ => ⟨0, by simp⟩, fun _ i => by simp⟩
      · have hne : ∃ i, y.testBit i = true := by
          by_contra hno
          push Not at hno
          exact hy0 (Nat.eq_of_testBit_eq (fun i => by simpa using hno i))
        obtain ⟨i, hi⟩ := hne
        refine iff_of_false (fun h => h (i + 1) ⟨?_, ?_⟩) ?_
        · rw [← Nat.testBit_div_two, show x / 2 = y by omega]; exact hi
        · rw [← Nat.testBit_div_two, show (x + 1) / 2 = y by omega]; exact hi
        · rintro ⟨j, hj⟩
          rcases j with _ | j
          · simp at hj; omega
          · rw [pow_succ] at hj; omega
    · have hx2 : x / 2 = y := by omega
      have hx3 : (x + 1) / 2 = y + 1 := by omega
      have hlt : y < x := by omega
      have h0 : ¬ (x.testBit 0 ∧ (x + 1).testBit 0) := by
        rintro ⟨-, h⟩
        have := Nat.mod_two_eq_one_iff_testBit_zero.mpr h; omega
      constructor
      · intro h
        obtain ⟨j, hj⟩ := (ih y hlt).1 (fun i hi => h (i + 1) ⟨by
          rw [← Nat.testBit_div_two, hx2]; exact hi.1, by rw [← Nat.testBit_div_two, hx3]; exact hi.2⟩)
        exact ⟨j + 1, by rw [pow_succ]; omega⟩
      · rintro ⟨j, hj⟩ i hi
        rcases j with _ | j
        · simp at hj; omega
        · have hy1 : y + 1 = 2 ^ j := by rw [pow_succ] at hj; omega
          rcases i with _ | i
          · exact h0 hi
          · exact (ih y hlt).2 ⟨j, hy1⟩ i ⟨by rw [← hx2, Nat.testBit_div_two]; exact hi.1,
              by rw [← hx3, Nat.testBit_div_two]; exact hi.2⟩

theorem solution : ∀ n k : ℕ, (∃ m : ℤ, A n k = m ∧ Odd m) ↔
    (Even n ∨ (Odd n ∧ ∃ j : ℕ, 0 < j ∧ k + 2 = 2 ^ j)) := by
  intro n k
  have hA := A_eq n k
  have hex : (∃ m : ℤ, A n k = m ∧ Odd m) ↔
      Odd (∑ j ∈ range (k + 1), c k j * (n : ℤ) ^ j) := by
    constructor
    · rintro ⟨m, hm, ho⟩
      have : (∑ j ∈ range (k + 1), c k j * (n : ℤ) ^ j) = m := by exact_mod_cast hA.symm.trans hm
      rw [this]; exact ho
    · exact fun h => ⟨_, hA, h⟩
  rw [hex]
  rcases Nat.even_or_odd n with hn | hn
  · have hc0 : c k 0 = 1 := by simp [c, Nat.choose_succ_self]
    have hsplit : ∑ j ∈ range (k + 1), c k j * (n : ℤ) ^ j =
        1 + (n : ℤ) * ∑ j ∈ range k, c k (j + 1) * (n : ℤ) ^ j := by
      rw [sum_range_succ', hc0, pow_zero, mul_one, mul_sum, add_comm]
      congr 1
      exact sum_congr rfl (fun j _ => by ring)
    have hodd : Odd (∑ j ∈ range (k + 1), c k j * (n : ℤ) ^ j) := by
      rw [hsplit]; exact ((Int.even_coe_nat n).2 hn).mul_right _ |>.one_add
    exact ⟨fun _ => Or.inl hn, fun _ => hodd⟩
  · have hdvd : (2 : ℤ) ∣ (∑ j ∈ range (k + 1), c k j * (n : ℤ) ^ j) - ∑ j ∈ range (k + 1), c k j := by
      rw [← sum_sub_distrib]
      refine dvd_sum (fun j _ => ?_)
      have he : Even ((n : ℤ) ^ j - 1) := (((Int.odd_coe_nat n).2 hn).pow).sub_odd odd_one
      rw [show c k j * (n : ℤ) ^ j - c k j = c k j * ((n : ℤ) ^ j - 1) by ring]
      exact dvd_mul_of_dvd_right (even_iff_two_dvd.1 he) _
    have hpar : Odd (∑ j ∈ range (k + 1), c k j * (n : ℤ) ^ j) ↔ Odd (∑ j ∈ range (k + 1), c k j) := by
      obtain ⟨w, hw⟩ := hdvd
      rw [Int.odd_iff, Int.odd_iff]; omega
    have hW : Odd (∑ j ∈ range (k + 1), c k j) ↔ Odd ((2 * k + 3).choose (k + 1)) := by
      rw [← Int.odd_coe_nat, ← sum_c_mul, Int.odd_mul]
      have : Odd (2 * (k : ℤ) + 3) := ⟨k + 1, by ring⟩
      exact ⟨fun h => ⟨h, this⟩, fun h => h.1⟩
    have hL := odd_choose_add_iff (k + 1) (k + 2)
    rw [show k + 1 + (k + 2) = 2 * k + 3 by ring] at hL
    have hB := bits_succ (k + 1)
    rw [hpar, hW, hL, hB]
    constructor
    · rintro ⟨j, hj⟩
      refine Or.inr ⟨hn, j, ?_, by omega⟩
      rcases j with _ | j
      · simp at hj
      · omega
    · rintro (h | ⟨-, j, -, hj⟩)
      · exact absurd h (Nat.not_even_iff_odd.2 hn)
      · exact ⟨j, by omega⟩

end OMA.A323206Proof

/-- The submitted solution. -/
theorem OMA.solution : type_of% @OMA.S_oeis_a323206.main := OMA.A323206Proof.solution
