import OMAStatements.S_oeis_a326781

namespace OMA.S_oeis_a326781


noncomputable instance : DecidablePred Good := Classical.decPred _


/-- Barker's recurrence. -/
def Conjecture : Prop :=
  ∀ n : ℕ, 17 < n → (a n : ℤ) = a (n - 1) + a (n - 16) - a (n - 17)

/-- Below `2^17` the forbidden bits are `0, 1, 3, 7, 15`, and `0b1000000010001011 = 32907`. -/
theorem good_iff (m : ℕ) (hm : m < 2 ^ 17) : Good m ↔ m &&& 32907 = 0 := by
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_land, Nat.zero_testBit]
    by_cases hb : (32907 : ℕ).testBit i = true
    · have hi : i < 16 := by
        by_contra hi
        have : (32907 : ℕ).testBit i = false :=
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right
            (by norm_num) (Nat.le_of_not_lt hi)))
        rw [this] at hb
        exact absurd hb (by decide)
      have hpow : ∃ k, i + 1 = 2 ^ k := by
        interval_cases i <;> first
          | exact absurd hb (by decide)
          | exact ⟨0, rfl⟩ | exact ⟨1, rfl⟩ | exact ⟨2, rfl⟩ | exact ⟨3, rfl⟩ | exact ⟨4, rfl⟩
      by_cases hmi : m.testBit i = true
      · exact absurd hpow (h i hmi)
      · simp [Bool.eq_false_iff.mpr hmi]
    · simp [Bool.eq_false_iff.mpr hb]
  · intro h i hi ⟨k, hk⟩
    have hland := Nat.testBit_land m 32907 i
    rw [h, Nat.zero_testBit, hi, Bool.true_and] at hland
    have hi17 : i < 17 := by
      by_contra hc
      have : m.testBit i = false :=
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hm (Nat.pow_le_pow_right (by norm_num)
          (Nat.le_of_not_lt hc)))
      rw [this] at hi
      exact absurd hi (by decide)
    have hk5 : k < 5 := by
      by_contra hc
      have : 2 ^ 5 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (Nat.le_of_not_lt hc)
      omega
    rcases (show i = 0 ∨ i = 1 ∨ i = 3 ∨ i = 7 ∨ i = 15 by
        interval_cases k <;> norm_num at hk <;> omega) with h0 | h0 | h0 | h0 | h0 <;>
      subst h0 <;> exact absurd hland (by decide)

theorem count_congr_lt {p q : ℕ → Prop} [DecidablePred p] [DecidablePred q] :
    ∀ n, (∀ i, i < n → (p i ↔ q i)) → Nat.count p n = Nat.count q n := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro h
    rw [Nat.count_succ, Nat.count_succ, ih (fun i hi => h i (by omega))]
    have hn := h n (by omega)
    by_cases hp : p n
    · rw [if_pos hp, if_pos (hn.mp hp)]
    · rw [if_neg hp, if_neg (fun hq => hp (hn.mpr hq))]

/-- The computable test that agrees with `Good` below `2^17`. -/
def GoodB (m : ℕ) : Prop := m &&& 32907 = 0

instance : DecidablePred GoodB := fun m => inferInstanceAs (Decidable (m &&& 32907 = 0))

/-- Reading off a term: if `v` has the property and exactly `n - 1` smaller numbers do, `a n = v`. -/
theorem a_eq (n v : ℕ) (hv : v < 2 ^ 17) (hg : GoodB v)
    (hc : Nat.count GoodB v = n - 1) : a n = v := by
  have hcount : Nat.count Good v = n - 1 := by
    rw [← hc]
    exact count_congr_lt v (fun i hi => good_iff i (by omega))
  have hgood : Good v := (good_iff v hv).mpr hg
  rw [a, ← hcount, Nat.nth_count hgood]

theorem a_2049 : a 2049 = 65536 := a_eq _ _ (by norm_num) (by decide) (by decide +kernel)
theorem a_2048 : a 2048 = 32628 := a_eq _ _ (by norm_num) (by decide) (by decide +kernel)
theorem a_2033 : a 2033 = 32512 := a_eq _ _ (by norm_num) (by decide) (by decide +kernel)
theorem a_2032 : a 2032 = 32372 := a_eq _ _ (by norm_num) (by decide) (by decide +kernel)

theorem disproof : ¬ Conjecture := by
  intro h
  have := h 2049 (by norm_num)
  norm_num [a_2049, a_2048, a_2033, a_2032] at this

end OMA.S_oeis_a326781

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a326781.main) :=
  fun h => OMA.S_oeis_a326781.disproof h.2
