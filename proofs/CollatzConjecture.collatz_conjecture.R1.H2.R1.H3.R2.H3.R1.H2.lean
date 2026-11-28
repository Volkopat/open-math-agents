import OMAReductions.R_CollatzConjecture_collatz_conjecture_R1_H2_R1_H3_R2_H3_R1

-- Proof of OMA.R_CollatzConjecture_collatz_conjecture_R1_H2_R1_H3_R2_H3_R1.H2
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


private def dropsBelow (target : ℕ) : ℕ → ℕ → Bool
  | 0, x => Nat.blt x target
  | fuel + 1, x => if Nat.blt x target then true else dropsBelow target fuel (cstep x)

private lemma dropsBelow_sound (target : ℕ) : ∀ fuel x : ℕ,
    dropsBelow target fuel x = true → ∃ i : ℕ, collatzStep^[i] x < target
  | 0, x, h => by
    simp only [dropsBelow, Nat.blt_eq] at h
    exact ⟨0, h⟩
  | fuel + 1, x, h => by
    simp only [dropsBelow] at h
    cases hx : Nat.blt x target
    · simp only [hx, Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨i, hi⟩ := dropsBelow_sound target fuel (cstep x) h
      refine ⟨i + 1, ?_⟩
      rw [Function.iterate_succ_apply, ← cstep_eq]
      exact hi
    · exact ⟨0, Nat.blt_eq.mp hx⟩

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


private def checkQ (q : ℕ) : Bool :=
  ([27, 31, 47, 63, 71, 91, 103, 111, 127, 155, 159, 167, 191, 207, 223, 231, 239, 251, 255, 283, 303, 319, 327, 359, 383, 411, 415, 447, 463, 479, 487, 495, 511, 539, 543, 559, 603, 615, 623, 639, 667, 671, 679, 703, 719, 743, 751, 763, 767, 795, 799, 831, 839, 859, 871, 879, 895, 927, 935, 959, 991, 1007, 1019, 1023] : List ℕ).all fun r =>
    let n := 1024 * q + r
    if Nat.blt n 10000 || Nat.ble 100000 n then true
    else dropsBelow n 225 n

private lemma checkAll_ok : checkBlock checkQ 9 7 = true := by decide +kernel

theorem OMA.solution : OMA.R_CollatzConjecture_collatz_conjecture_R1_H2_R1_H3_R2_H3_R1.H2 := by
  intro n hlo hhi h1024
  have hq : checkQ (n / 1024) = true :=
    checkBlock_sound 7 9 (n / 1024) checkAll_ok (by omega) (by omega)
  have hr := List.all_eq_true.mp hq (n % 1024) h1024
  have hdiv : 1024 * (n / 1024) + n % 1024 = n := Nat.div_add_mod n 1024
  dsimp only at hr
  rw [hdiv] at hr
  have h1 : Nat.blt n 10000 = false := by
    cases hc : Nat.blt n 10000
    · rfl
    · have := Nat.blt_eq.mp hc; omega
  have h2 : Nat.ble 100000 n = false := by
    cases hc : Nat.ble 100000 n
    · rfl
    · have := Nat.ble_eq.mp hc; omega
  rw [h1, h2] at hr
  simp only [Bool.false_or, Bool.false_eq_true, ↓reduceIte] at hr
  exact dropsBelow_sound n 225 n hr
