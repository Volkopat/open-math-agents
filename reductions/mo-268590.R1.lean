import OMAStatements.S_mo_268590

/-!
Every even-length palindrome is divisible by one more than its base, so the first three lengths
must be odd. For adjacent three-digit palindromes, the digit bounds limit the drop in the leading
digit to at most two. Reducing the expansions modulo the larger base then leaves two possible
transitions. Three such transitions cannot occur in succession, and the first two force the
fourth representation to have at least three digits. The remaining subgoals start at five digits.
-/

namespace OMA.R_mo_268590_R1

open OMA.S_mo_268590

private lemma even_palindrome_dvd_succ {b N : ℕ} (h : NontrivPalindrome b N)
    (he : Even (Nat.digits b N).length) : b + 1 ∣ N := by
  let dig := (Nat.digits b N).map (fun d : ℕ => (d : ℤ))
  have hp : dig.Palindrome := (List.Palindrome.of_reverse_eq h.2).map _
  have he' : Even dig.length := by simpa [dig] using he
  have hdiv : ((b + 1 : ℕ) : ℤ) ∣ (b : ℤ) - (-1) := ⟨1, by push_cast; ring⟩
  rw [Nat.dvd_iff_dvd_ofDigits (b + 1) b (-1) hdiv, Nat.ofDigits_neg_one]
  refine ⟨0, (show dig.alternatingSum = 0 from ?_)⟩
  have hrev := dig.alternatingSum_reverse
  rw [hp.reverse_eq, pow_succ', he'.neg_one_pow, mul_one, neg_one_zsmul] at hrev
  exact eq_zero_of_neg_eq hrev.symm

private lemma palindrome_ne_zero {b N : ℕ} (h : NontrivPalindrome b N) : N ≠ 0 := by
  intro hN
  simpa [hN] using h.1

private lemma odd_length_of_next_palindrome {b N : ℕ} (hb : 2 ≤ b)
    (h : NontrivPalindrome b N) (hnext : NontrivPalindrome (b + 1) N) :
    Odd (Nat.digits b N).length := by
  rcases Nat.even_or_odd (Nat.digits b N).length with he | ho
  · exfalso
    have hdiv := even_palindrome_dvd_succ h he
    have hn := palindrome_ne_zero hnext
    have hhead : (Nat.digits (b + 1) N).head! = 0 := by
      rw [Nat.head!_digits (by omega : b + 1 ≠ 1), Nat.mod_eq_zero_of_dvd hdiv]
    have hlast := congrArg List.head? hnext.2
    rw [List.head?_reverse, List.getLast?_eq_getLast (Nat.digits_ne_nil_iff_ne_zero.mpr hn)] at hlast
    exact Nat.getLast_digit_ne_zero (b + 1) hn ((List.head!_of_head? hlast.symm).symm.trans hhead)
  · exact ho

private lemma digit_length_antitone {b c N : ℕ} (hb : 1 < b) (hbc : b ≤ c) :
    (Nat.digits c N).length ≤ (Nat.digits b N).length := by
  apply (Nat.digits_length_le_iff (hb.trans_le hbc) N).mpr
  exact (Nat.lt_base_pow_length_digits hb).trans_le (Nat.pow_le_pow_left hbc _)

private lemma three_digit_description {b N : ℕ} (hb : 2 ≤ b) (hp : NontrivPalindrome b N)
    (hl : (Nat.digits b N).length = 3) :
    ∃ a c : ℤ, 0 < a ∧ a < b ∧ 0 ≤ c ∧ c < b ∧ (N : ℤ) = a * (b : ℤ)^2 + c * b + a := by
  obtain ⟨a, c, a', hd⟩ := List.length_eq_three.mp hl
  have he : a' = a := by simpa [hd] using congrArg List.head! hp.2
  subst a'
  have hn := palindrome_ne_zero hp
  have hlast : (Nat.digits b N).getLast! ≠ 0 := by
    rw [List.getLast!_of_getLast? (List.getLast?_eq_getLast (Nat.digits_ne_nil_iff_ne_zero.mpr hn))]
    exact Nat.getLast_digit_ne_zero b hn
  have ha0 := Nat.pos_of_ne_zero (show a ≠ 0 by simpa [hd] using hlast)
  have hab : a < b := Nat.digits_lt_base (m := N) (by omega) (by rw [hd]; simp)
  have hcb : c < b := Nat.digits_lt_base (m := N) (by omega) (by rw [hd]; simp)
  have hN : N = a * b^2 + c * b + a := by
    rw [← Nat.ofDigits_digits b N, hd]
    simp only [Nat.ofDigits_cons, Nat.ofDigits_nil]
    ring
  exact ⟨a, c, by exact_mod_cast ha0, by exact_mod_cast hab, by positivity,
    by exact_mod_cast hcb, by exact_mod_cast hN⟩

private lemma three_digit_bounds {b a c : ℤ} (hb : 1 < b) (ha0 : 0 < a) (ha : a < b)
    (hc0 : 0 ≤ c) (hc : c < b) :
    a * b^2 ≤ a * b^2 + c * b + a ∧ a * b^2 + c * b + a < (a + 1) * b^2 := by
  constructor
  · nlinarith only [ha0, mul_nonneg hc0 (by omega : 0 ≤ b)]
  · have hcb := mul_le_mul_of_nonneg_right (show c ≤ b - 1 by omega) (by omega : 0 ≤ b)
    nlinarith only [hcb, show a ≤ b - 1 by omega]

/-- The leading digit either drops by one or is the largest digit followed by a zero. -/
private lemma adjacent_three_digit {b a c A C : ℤ} (hb : 1 < b)
    (ha0 : 0 < a) (ha : a < b) (hc0 : 0 ≤ c) (hc : c < b)
    (hA0 : 0 < A) (hA : A < b + 1) (hC0 : 0 ≤ C) (hC : C < b + 1)
    (h : a * b^2 + c * b + a = A * (b + 1)^2 + C * (b + 1) + A) :
    (A + 1 = a ∧ c = a + 1 ∧ C = b + 2 - a) ∨
      (a = b - 1 ∧ c = 0 ∧ A = b - 3 ∧ C = 5) := by
  obtain ⟨hla, hua⟩ := three_digit_bounds hb ha0 ha hc0 hc
  obtain ⟨hlA, huA⟩ := three_digit_bounds (by omega : 1 < b + 1) hA0 hA hC0 hC
  have hle : A ≤ a := by
    by_contra! hlt
    have hmul := mul_le_mul_of_nonneg_right (show a + 1 ≤ A by omega) (sq_nonneg b)
    have hbase : b^2 ≤ (b + 1)^2 := by nlinarith only [hb]
    have hmul' := mul_le_mul_of_nonneg_left hbase hA0.le
    linarith only [hmul, hmul', hua, hlA, h]
  have hle' : a ≤ A + 2 := by
    by_contra! hlt
    have hmul := mul_le_mul_of_nonneg_right (show A + 1 ≤ b - 1 by omega) (by omega : 0 ≤ 2*b+1)
    have hmid : (A + 1) * (b + 1)^2 ≤ (A + 3) * b^2 := by nlinarith only [hmul, hb]
    have hlast := mul_le_mul_of_nonneg_right (show A + 3 ≤ a by omega) (sq_nonneg b)
    linarith only [hmid, hlast, hla, huA, h]
  let q := (A - a) * (b + 1) + C - c + 2*a
  have hq : 2*a - c - A = (b + 1) * q := by
    dsimp [q]
    linear_combination h
  have hq0 : 0 ≤ q := by
    by_contra! hneg
    have hm := mul_le_mul_of_nonneg_left (show q ≤ -1 by omega) (by omega : 0 ≤ b + 1)
    have hlow : -(b+1) < 2*a - c - A := by omega
    nlinarith only [hq, hm, hlow]
  have hq1 : q ≤ 1 := by
    by_contra! hbig
    have hm := mul_le_mul_of_nonneg_left (show 2 ≤ q by omega) (by omega : 0 ≤ b + 1)
    have hhigh : 2*a - c - A ≤ b+1 := by omega
    nlinarith only [hq, hm, hhigh, hb]
  obtain hz | hz : q = 0 ∨ q = 1 := by omega
  · have hfirst : 2*a - c - A = 0 := by simpa [hz] using hq
    change (A - a) * (b + 1) + C - c + 2*a = 0 at hz
    obtain h₀ | h₁ | h₂ : A - a = 0 ∨ A - a = -1 ∨ A - a = -2 := by omega
    · rw [h₀, zero_mul] at hz
      omega
    · rw [h₁, neg_one_mul] at hz
      left
      omega
    · rw [h₂] at hz
      omega
  · have hfirst : 2*a - c - A = b + 1 := by simpa [hz] using hq
    have hdiff : A - a = -2 := by omega
    change (A - a) * (b + 1) + C - c + 2*a = 1 at hz
    rw [hdiff] at hz
    right
    omega

/-- A candidate cannot start with a three-digit palindrome. -/
private lemma excludes_three_digit_base {b N : ℕ} (hb : 2 ≤ b)
    (h : ∀ i < 4, NontrivPalindrome (b + i) N)
    (hfirst : (Nat.digits b N).length = 3)
    (hodd : ∀ i < 3, Odd (Nat.digits (b + i) N).length) : False := by
  have hbZ : (1 : ℤ) < b := by exact_mod_cast (show 1 < b by omega)
  have short (i : ℕ) (hi : i < 3) : (Nat.digits (b + i) N).length = 3 := by
    have hlo := (h i (by omega)).1
    have hhi := digit_length_antitone (N := N) (by omega : 1 < b) (by omega : b ≤ b + i)
    obtain ⟨k, hk⟩ := hodd i hi
    omega
  obtain ⟨a, c, ha0, ha, hc0, hc, e0⟩ :=
    three_digit_description hb (by simpa using h 0 (by decide)) hfirst
  obtain ⟨A, C, hA0, hA, hC0, hC, e1⟩ :=
    three_digit_description (by omega) (h 1 (by decide)) (short 1 (by decide))
  obtain ⟨D, E, hD0, hD, hE0, hE, e2⟩ :=
    three_digit_description (by omega) (h 2 (by decide)) (short 2 (by decide))
  push_cast at hA hC e1 hD hE e2
  have first := adjacent_three_digit hbZ ha0 ha hc0 hc hA0 hA hC0 hC (e0.symm.trans e1)
  have second := adjacent_three_digit (b := (b : ℤ) + 1) (by omega) hA0 hA hC0 hC hD0
    (by omega) hE0 (by omega) (by simpa [add_assoc] using e1.symm.trans e2)
  have hA_lt : A < b := by rcases first <;> omega
  obtain ⟨hDA, hCeq, hEeq⟩ : D + 1 = A ∧ C = A + 1 ∧ E = (b : ℤ) + 3 - A := by
    rcases second <;> omega
  have ⟨hD2, hAne⟩ : 2 ≤ D ∧ 2*A ≠ (b : ℤ) + 3 := by
    rcases first <;> omega
  have hNlow : (b + 3)^2 ≤ N := by
    have hmul := mul_le_mul_of_nonneg_right hD2 (sq_nonneg ((b : ℤ) + 2))
    have hsmall : ((b : ℤ) + 3)^2 ≤ 2 * ((b : ℤ) + 2)^2 := by
      nlinarith only [hbZ, sq_nonneg (b : ℤ)]
    have hlarge := (three_digit_bounds (by omega : (1 : ℤ) < b + 2) hD0 hD hE0 hE).1
    have hZ : ((b : ℤ) + 3)^2 ≤ (N : ℤ) := by linarith only [hsmall, hmul, hlarge, e2]
    exact_mod_cast hZ
  have hlast : (Nat.digits (b + 3) N).length = 3 := by
    have hlo := (Nat.lt_digits_length_iff (k := 2) (by omega : 1 < b + 3) N).mpr hNlow
    have hhi := digit_length_antitone (N := N) (by omega : 1 < b) (by omega : b ≤ b + 3)
    omega
  obtain ⟨F, H, hF0, hF, hH0, hH, e3⟩ := three_digit_description (by omega) (h 3 (by decide)) hlast
  push_cast at hF hH e3
  have third := adjacent_three_digit (b := (b : ℤ) + 2) (by omega) hD0 hD hE0 hE hF0
    (by omega) hH0 (by omega) (by simpa [add_assoc] using e2.symm.trans e3)
  rcases third <;> omega

/-- No constant-length example with an odd number of digits at least five. -/
def H1 : Prop :=
  ∀ N b : ℕ, 2 ≤ b →
    5 ≤ (Nat.digits b N).length → Odd (Nat.digits b N).length →
    (∀ i < 4, (Nat.digits (b + i) N).length = (Nat.digits b N).length) →
    ¬ (∀ i < 4, NontrivPalindrome (b + i) N)

/-- No example with differing lengths and odd lengths in the first three bases. -/
def H2 : Prop :=
  ∀ N b : ℕ, 2 ≤ b → 5 ≤ (Nat.digits b N).length →
    (∀ i < 3, Odd (Nat.digits (b + i) N).length) →
    (Nat.digits (b + 3) N).length < (Nat.digits b N).length →
    ¬ (∀ i < 4, NontrivPalindrome (b + i) N)

theorem main : H1 → H2 → type_of% @OMA.S_mo_268590.main := by
  intro h1 h2
  rintro ⟨N, b, hb, hpal⟩
  have hodd (i : ℕ) (hi : i < 3) : Odd (Nat.digits (b + i) N).length :=
    odd_length_of_next_palindrome (by omega) (hpal i (by omega))
      (by simpa [add_assoc] using hpal (i + 1) (by omega))
  have h5 : 5 ≤ (Nat.digits b N).length := by
    by_contra! hlt
    have htwo := (hpal 0 (by decide)).1
    obtain ⟨k, hk⟩ := hodd 0 (by decide)
    simp only [Nat.add_zero] at htwo hk
    exact excludes_three_digit_base hb hpal (by omega) hodd
  by_cases hlt : (Nat.digits (b + 3) N).length < (Nat.digits b N).length
  · exact h2 N b hb h5 hodd hlt hpal
  · have hs (i : ℕ) (hi : i < 4) : (Nat.digits (b + i) N).length = (Nat.digits b N).length := by
      have hlo := digit_length_antitone (N := N) (by omega : 1 < b + i) (by omega : b + i ≤ b + 3)
      have hhi := digit_length_antitone (N := N) (by omega : 1 < b) (by omega : b ≤ b + i)
      omega
    exact h1 N b hb h5 (by simpa using hodd 0 (by decide)) hs hpal

end OMA.R_mo_268590_R1
