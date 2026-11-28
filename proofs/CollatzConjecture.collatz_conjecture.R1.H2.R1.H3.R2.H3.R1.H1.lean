import OMAReductions.R_CollatzConjecture_collatz_conjecture_R1_H2_R1_H3_R2_H3_R1

-- Proof of OMA.R_CollatzConjecture_collatz_conjecture_R1_H2_R1_H3_R2_H3_R1.H1
-- Credit: @Twalways

open CollatzConjecture

private def cstep (x : ℕ) : ℕ :=
  if Nat.beq (x % 2) 0 then x / 2 else 3 * x + 1

private lemma cstep_eq (x : ℕ) : cstep x = CollatzConjecture.collatzStep x := by
  unfold cstep CollatzConjecture.collatzStep
  cases h : Nat.beq (x % 2) 0
  · have hne : x % 2 ≠ 0 := by intro he; rw [he] at h; simp at h
    have ho : ¬ Even x := by rw [Nat.even_iff]; omega
    simp [ho]
  · have he : Even x := Nat.even_iff.mpr (Nat.beq_eq.mp h)
    simp [he]


private def memNat (x : ℕ) : List ℕ → Bool
  | [] => false
  | y :: ys => if Nat.beq x y then true else memNat x ys

private lemma memNat_iff (x : ℕ) : ∀ l : List ℕ, memNat x l = true ↔ x ∈ l
  | [] => by simp [memNat]
  | y :: ys => by
    simp only [memNat, List.mem_cons]
    cases h : Nat.beq x y
    · simp [Nat.beq_eq.mp, memNat_iff x ys, show x ≠ y by
        intro heq; subst heq; simp at h]
    · simp [Nat.beq_eq.mp h]


private lemma affine_even {a b q : ℕ} (ha : a % 2 = 0) (hb : b % 2 = 0) :
    collatzStep (a * q + b) = (a / 2) * q + b / 2 := by
  have hev : (a * q + b) % 2 = 0 := by
    have ha' : a = 2 * (a / 2) := by omega
    rw [ha', show 2 * (a / 2) * q + b = 2 * ((a / 2) * q) + b by ring]
    omega
  rw [← cstep_eq, cstep]
  have hbeq : Nat.beq ((a * q + b) % 2) 0 = true := Nat.beq_eq.mpr hev
  rw [hbeq]
  simp only [↓reduceIte]
  have ha' : a = 2 * (a / 2) := by omega
  have hb' : b = 2 * (b / 2) := by omega
  have hmul : a * q + b = 2 * ((a / 2) * q + b / 2) := by
    conv_lhs => rw [ha', hb']
    ring
  rw [hmul, Nat.mul_div_cancel_left _ (by omega : 0 < 2)]

private lemma affine_odd {a b q : ℕ} (ha : a % 2 = 0) (hb : b % 2 = 1) :
    collatzStep (a * q + b) = (3 * a) * q + (3 * b + 1) := by
  have hodd : (a * q + b) % 2 ≠ 0 := by
    have ha' : a = 2 * (a / 2) := by omega
    rw [ha', show 2 * (a / 2) * q + b = 2 * ((a / 2) * q) + b by ring]
    omega
  rw [← cstep_eq, cstep]
  have hbeq : Nat.beq ((a * q + b) % 2) 0 = false := by
    cases hc : Nat.beq ((a * q + b) % 2) 0
    · rfl
    · exact absurd (Nat.beq_eq.mp hc) hodd
  rw [hbeq]
  simp only [Bool.false_eq_true, ↓reduceIte]
  ring

private def checkAffine (r : ℕ) : ℕ → ℕ → ℕ → Bool
  | 0, a, b => Nat.blt a 1024 && Nat.blt b r
  | fuel + 1, a, b =>
    if Nat.blt a 1024 && Nat.blt b r then true
    else if Nat.beq (a % 2) 0 then
      if Nat.beq (b % 2) 0 then checkAffine r fuel (a / 2) (b / 2)
      else checkAffine r fuel (3 * a) (3 * b + 1)
    else false

private lemma checkAffine_sound (r q : ℕ) : ∀ fuel a b s : ℕ,
    collatzStep^[s] (1024 * q + r) = a * q + b →
    checkAffine r fuel a b = true →
    ∃ t : ℕ, t ≤ s + fuel ∧ collatzStep^[t] (1024 * q + r) < 1024 * q + r
  | 0, a, b, s, hval, h => by
    simp only [checkAffine, Bool.and_eq_true, Nat.blt_eq] at h
    refine ⟨s, by omega, ?_⟩
    rw [hval]
    nlinarith
  | fuel + 1, a, b, s, hval, h => by
    simp only [checkAffine] at h
    cases hok : (Nat.blt a 1024 && Nat.blt b r)
    · simp only [hok, Bool.false_eq_true, ↓reduceIte] at h
      cases ha : Nat.beq (a % 2) 0
      · simp [ha] at h
      · simp only [ha, ↓reduceIte] at h
        have ha0 : a % 2 = 0 := Nat.beq_eq.mp ha
        cases hb : Nat.beq (b % 2) 0
        · simp only [hb, Bool.false_eq_true, ↓reduceIte] at h
          have hb1 : b % 2 = 1 := by
            have hne : b % 2 ≠ 0 := by intro he; rw [he] at hb; simp at hb
            omega
          have hnext : collatzStep^[s + 1] (1024 * q + r) = (3 * a) * q + (3 * b + 1) := by
            rw [Function.iterate_succ_apply', hval, affine_odd ha0 hb1]
          obtain ⟨t, ht, hlt⟩ := checkAffine_sound r q fuel (3 * a) (3 * b + 1) (s + 1) hnext h
          exact ⟨t, by omega, hlt⟩
        · simp only [hb, ↓reduceIte] at h
          have hb0 : b % 2 = 0 := Nat.beq_eq.mp hb
          have hnext : collatzStep^[s + 1] (1024 * q + r) = (a / 2) * q + b / 2 := by
            rw [Function.iterate_succ_apply', hval, affine_even ha0 hb0]
          obtain ⟨t, ht, hlt⟩ := checkAffine_sound r q fuel (a / 2) (b / 2) (s + 1) hnext h
          exact ⟨t, by omega, hlt⟩
    · simp only [Bool.and_eq_true, Nat.blt_eq] at hok
      refine ⟨s, by omega, ?_⟩
      rw [hval]
      nlinarith

private def checkBlock (f : ℕ → Bool) : ℕ → ℕ → Bool
  | lo, 0 => f lo
  | lo, d + 1 => checkBlock f lo d && checkBlock f (lo + 2 ^ d) d

private lemma checkBlock_sound {f : ℕ → Bool} : ∀ d lo q : ℕ,
    checkBlock f lo d = true → lo ≤ q → q < lo + 2 ^ d → f q = true
  | 0, lo, q, h, h1, h2 => by
    have hq : q = lo := by omega
    simpa [checkBlock, hq] using h
  | d + 1, lo, q, h, h1, h2 => by
    simp only [checkBlock, Bool.and_eq_true] at h
    by_cases hlt : q < lo + 2 ^ d
    · exact checkBlock_sound d lo q h.1 h1 hlt
    · exact checkBlock_sound d (lo + 2 ^ d) q h.2 (by omega) (by rw [pow_succ'] at h2; omega)


private def checkRes (r : ℕ) : Bool :=
  if !(memNat (r % 128) [27, 31, 39, 47, 63, 71, 79, 91, 95, 103, 111, 123, 127]) || memNat r [27, 31, 47, 63, 71, 91, 103, 111, 127, 155, 159, 167, 191, 207, 223, 231, 239, 251, 255, 283, 303, 319, 327, 359, 383, 411, 415, 447, 463, 479, 487, 495, 511, 539, 543, 559, 603, 615, 623, 639, 667, 671, 679, 703, 719, 743, 751, 763, 767, 795, 799, 831, 839, 859, 871, 879, 895, 927, 935, 959, 991, 1007, 1019, 1023] then true
  else checkAffine r 16 1024 r

private lemma checkAll_ok : checkBlock checkRes 0 10 = true := by decide +kernel

theorem OMA.solution : OMA.R_CollatzConjecture_collatz_conjecture_R1_H2_R1_H3_R2_H3_R1.H1 := by
  intro n _ h128 hnot
  have hok : checkRes (n % 1024) = true :=
    checkBlock_sound 10 0 (n % 1024) checkAll_ok (by omega) (Nat.mod_lt n (by omega))
  have hm128 : memNat ((n % 1024) % 128) [27, 31, 39, 47, 63, 71, 79, 91, 95, 103, 111, 123, 127] = true := by
    have hm : (n % 1024) % 128 = n % 128 := by omega
    rw [hm, memNat_iff]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  have hmnot : memNat (n % 1024) [27, 31, 47, 63, 71, 91, 103, 111, 127, 155, 159, 167, 191, 207, 223, 231, 239, 251, 255, 283, 303, 319, 327, 359, 383, 411, 415, 447, 463, 479, 487, 495, 511, 539, 543, 559, 603, 615, 623, 639, 667, 671, 679, 703, 719, 743, 751, 763, 767, 795, 799, 831, 839, 859, 871, 879, 895, 927, 935, 959, 991, 1007, 1019, 1023] = false := by
    cases hc : memNat (n % 1024) [27, 31, 47, 63, 71, 91, 103, 111, 127, 155, 159, 167, 191, 207, 223, 231, 239, 251, 255, 283, 303, 319, 327, 359, 383, 411, 415, 447, 463, 479, 487, 495, 511, 539, 543, 559, 603, 615, 623, 639, 667, 671, 679, 703, 719, 743, 751, 763, 767, 795, 799, 831, 839, 859, 871, 879, 895, 927, 935, 959, 991, 1007, 1019, 1023]
    · rfl
    · exact absurd ((memNat_iff (n % 1024) _).mp hc) hnot
  simp only [checkRes, hm128, hmnot, Bool.not_true, Bool.false_or,
    Bool.false_eq_true, ↓reduceIte] at hok
  obtain ⟨s, _, hlt⟩ := checkAffine_sound (n % 1024) (n / 1024) 16 1024 (n % 1024) 0
    (by simp) hok
  have hdiv : 1024 * (n / 1024) + n % 1024 = n := Nat.div_add_mod n 1024
  rw [hdiv] at hlt
  exact ⟨s, hlt⟩
