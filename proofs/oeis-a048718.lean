import OMAStatements.S_oeis_a048718

namespace OMA.P_oeis_a048718

open OMA.S_oeis_a048718

/-- closure condition on a finite set of carry states -/
def Good (c1 c2 c3 : ℕ) (R : List (ℕ × ℕ × ℕ)) : Prop :=
  ∀ r ∈ R, r.1 ^^^ r.2.1 = r.2.2 ∧ (r.1 / 2, r.2.1 / 2, r.2.2 / 2) ∈ R ∧
    r.1 % 2 ^^^ r.2.1 % 2 = r.2.2 % 2 ∧
    (c1 + r.1) % 16 ^^^ (c2 + r.2.1) % 16 = (c3 + r.2.2) % 16 ∧
    ((c1 + r.1) / 16, (c2 + r.2.1) / 16, (c3 + r.2.2) / 16) ∈ R

lemma xor_split (w a b c d : ℕ) (hb : b < 2 ^ w) (hd : d < 2 ^ w) :
    (2 ^ w * a + b) ^^^ (2 ^ w * c + d) = 2 ^ w * (a ^^^ c) + (b ^^^ d) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, Nat.testBit_two_pow_mul_add _ hb, Nat.testBit_two_pow_mul_add _ hd,
    Nat.testBit_two_pow_mul_add _ (Nat.xor_lt_two_pow hb hd)]
  split_ifs <;> simp [Nat.testBit_xor]

lemma xor2 (a b c d : ℕ) (hb : b < 2) (hd : d < 2) :
    (2 * a + b) ^^^ (2 * c + d) = 2 * (a ^^^ c) + (b ^^^ d) := by
  simpa using xor_split 1 a b c d (by simpa using hb) (by simpa using hd)

lemma xor16 (a b c d : ℕ) (hb : b < 16) (hd : d < 16) :
    (16 * a + b) ^^^ (16 * c + d) = 16 * (a ^^^ c) + (b ^^^ d) := by
  have := xor_split 4 a b c d (by norm_num; omega) (by norm_num; omega)
  norm_num at this
  exact this

lemma sparse_div2 {x : ℕ} (hx : Sparse x) : Sparse (x / 2) := by
  intro i j hij hi hj
  rw [Nat.testBit_div_two] at hi hj
  have := hx (i + 1) (j + 1) (by omega) hi hj
  omega

lemma sparse_div16 {x : ℕ} (hx : Sparse x) : Sparse (x / 16) := by
  intro i j hij hi hj
  rw [show (16 : ℕ) = 2 ^ 4 by norm_num, Nat.testBit_div_two_pow] at hi hj
  have := hx (i + 4) (j + 4) (by omega) hi hj
  omega

lemma odd_mod16 {x : ℕ} (hx : Sparse x) (h : x % 2 = 1) : x % 16 = 1 := by
  have h0 : x.testBit 0 = true := by simp [Nat.testBit_zero, h]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [show (16 : ℕ) = 2 ^ 4 by norm_num, Nat.testBit_mod_two_pow]
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp [h0]
  · have h1 : (1 : ℕ).testBit i = false := by
      obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
      rw [← Nat.testBit_div_two]; simp
    rw [h1]
    by_cases h4 : i < 4
    · have : x.testBit i = false := by
        by_contra hc
        have := hx 0 i hi h0 (by simpa using hc)
        omega
      simp [this]
    · simp [h4]

lemma key (c1 c2 c3 : ℕ) (R : List (ℕ × ℕ × ℕ)) (hR : Good c1 c2 c3 R) :
    ∀ y, Sparse y → ∀ r ∈ R, (c1 * y + r.1) ^^^ (c2 * y + r.2.1) = c3 * y + r.2.2 := by
  intro y
  induction y using Nat.strong_induction_on with
  | _ y ih =>
  intro hy r hr
  obtain ⟨h0, hrh, h1, h16, hrs⟩ := hR r hr
  rcases Nat.eq_zero_or_pos y with rfl | hpos
  · simpa using h0
  rcases Nat.mod_two_eq_zero_or_one y with he | ho
  · have hlt : y / 2 < y := Nat.div_lt_self hpos (by norm_num)
    have IH := ih (y / 2) hlt (sparse_div2 hy) _ hrh
    have hq : y / 2 * 2 = y := by omega
    have e : ∀ c s : ℕ, c * y + s = 2 * (c * (y / 2) + s / 2) + s % 2 := by
      intro c s
      have := Nat.div_add_mod' s 2
      conv_lhs => rw [← hq, ← this]
      ring
    rw [e c1, e c2, e c3, xor2 _ _ _ _ (Nat.mod_lt _ (by norm_num))
      (Nat.mod_lt _ (by norm_num)), IH, h1]
  · have hlt : y / 16 < y := Nat.div_lt_self hpos (by norm_num)
    have IH := ih (y / 16) hlt (sparse_div16 hy) _ hrs
    have hm := odd_mod16 hy ho
    have hq : y / 16 * 16 + 1 = y := by omega
    have e : ∀ c s : ℕ, c * y + s = 16 * (c * (y / 16) + (c + s) / 16) + (c + s) % 16 := by
      intro c s
      have := Nat.div_add_mod' (c + s) 16
      rw [show 16 * (c * (y / 16) + (c + s) / 16) + (c + s) % 16 =
        16 * (c * (y / 16)) + ((c + s) / 16 * 16 + (c + s) % 16) by ring, this]
      conv_lhs => rw [← hq]
      ring
    rw [e c1, e c2, e c3, xor16 _ _ _ _ (Nat.mod_lt _ (by norm_num))
      (Nat.mod_lt _ (by norm_num)), IH, h16]

lemma ident (c1 c2 c3 : ℕ) (R : List (ℕ × ℕ × ℕ)) (hR : Good c1 c2 c3 R) (h0 : (0, 0, 0) ∈ R)
    (y : ℕ) (hy : Sparse y) : (c1 * y) ^^^ (c2 * y) = c3 * y := by
  simpa using key c1 c2 c3 R hR y hy _ h0

lemma sparse_a (n : ℕ) : Sparse (a n) := by
  apply Nat.nth_mem_of_infinite
  apply Set.infinite_of_forall_exists_gt
  intro m
  refine ⟨2 ^ m, ?_, Nat.lt_two_pow_self⟩
  intro i j hij hi hj
  rw [Nat.testBit_two_pow] at hi hj
  simp at hi hj
  omega

end OMA.P_oeis_a048718

open OMA.S_oeis_a048718 OMA.P_oeis_a048718 in
theorem OMA.solution : type_of% @OMA.S_oeis_a048718.main := by
  intro n
  have hs := sparse_a n
  have g0 : Good 1 14 15 [(0, 0, 0)] := by unfold Good; decide
  refine ⟨by simpa using ident 1 14 15 _ g0 (by simp) _ hs, ?_⟩
  refine ⟨ident 3 9 10 [(0, 0, 0)] (by unfold Good; decide) (by simp) _ hs, ?_⟩
  refine ⟨ident 3 13 14 [(0, 0, 0)] (by unfold Good; decide) (by simp) _ hs, ?_⟩
  refine ⟨ident 5 9 12 [(0, 0, 0)] (by unfold Good; decide) (by simp) _ hs, ?_⟩
  refine ⟨ident 5 11 14 [(0, 0, 0)] (by unfold Good; decide) (by simp) _ hs, ?_⟩
  refine ⟨ident 6 11 13 [(0, 0, 0)] (by unfold Good; decide) (by simp) _ hs, ?_⟩
  refine ⟨ident 7 9 14 [(0, 0, 0)] (by unfold Good; decide) (by simp) _ hs, ?_⟩
  refine ⟨ident 7 10 13 [(0, 0, 0)] (by unfold Good; decide) (by simp) _ hs, ?_⟩
  refine ⟨ident 7 11 12 [(0, 0, 0)] (by unfold Good; decide) (by simp) _ hs, ?_⟩
  refine ⟨ident 12 21 25 [(0, 0, 0), (0, 1, 1)] (by unfold Good; decide) (by simp) _ hs, ?_⟩
  exact ident 12 37 41 [(0, 0, 0), (0, 1, 1), (0, 2, 2)] (by unfold Good; decide) (by simp) _ hs
