import OMAStatements.S_oeis_a007857

-- Problem: A007857: Number of independent sets in rooted plane trees on n nodes.
-- Upstream: formal-conjectures statements/oeis-a007857.lean:0 (declaration OMA.S_oeis_a007857.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Both C(3n, n) and C(2n, n) satisfy first-order recurrences with polynomial coefficients
(hB1, hC1). After clearing the denominators n, n-1, n-2, n-3 of the closed form, Mathar's recurrence
is a polynomial combination of shifted copies of these two relations (lemma `pure`), which is
checked by `linear_combination`. -/

namespace A007857Aux

open OMA.S_oeis_a007857

theorem hB1 (m : ℕ) :
    2 * ((m : ℚ) + 1) * (2 * (m : ℚ) + 1) * ((3 * (m + 1)).choose (m + 1) : ℚ) =
      3 * (3 * (m : ℚ) + 1) * (3 * (m : ℚ) + 2) * ((3 * m).choose m : ℚ) := by
  have h1 : ((3 * m).choose m : ℚ) * (m.factorial : ℚ) * ((2 * m).factorial : ℚ) =
      ((3 * m).factorial : ℚ) := by
    have h := Nat.choose_mul_factorial_mul_factorial (show m ≤ 3 * m by omega)
    have e : 3 * m - m = 2 * m := by omega
    rw [e] at h
    exact_mod_cast h
  have h2 : ((3 * (m + 1)).choose (m + 1) : ℚ) * ((m + 1).factorial : ℚ) *
      ((2 * (m + 1)).factorial : ℚ) = ((3 * (m + 1)).factorial : ℚ) := by
    have h := Nat.choose_mul_factorial_mul_factorial (show m + 1 ≤ 3 * (m + 1) by omega)
    have e : 3 * (m + 1) - (m + 1) = 2 * (m + 1) := by omega
    rw [e] at h
    exact_mod_cast h
  have f1 : ((m + 1).factorial : ℚ) = ((m : ℚ) + 1) * (m.factorial : ℚ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have f2 : ((2 * (m + 1)).factorial : ℚ) =
      (2 * (m : ℚ) + 2) * (2 * (m : ℚ) + 1) * ((2 * m).factorial : ℚ) := by
    have e : 2 * (m + 1) = 2 * m + 1 + 1 := by ring
    rw [e, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    ring
  have f3 : ((3 * (m + 1)).factorial : ℚ) =
      (3 * (m : ℚ) + 3) * (3 * (m : ℚ) + 2) * (3 * (m : ℚ) + 1) * ((3 * m).factorial : ℚ) := by
    have e : 3 * (m + 1) = 3 * m + 2 + 1 := by ring
    rw [e, Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    ring
  rw [f1, f2, f3] at h2
  have p1 : (m.factorial : ℚ) ≠ 0 := by positivity
  have p2 : ((2 * m).factorial : ℚ) ≠ 0 := by positivity
  have p3 : (m : ℚ) + 1 ≠ 0 := by positivity
  have p : ((m : ℚ) + 1) * (m.factorial : ℚ) * ((2 * m).factorial : ℚ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero p3 p1) p2
  apply mul_left_cancel₀ p
  linear_combination h2 - (3 * (m : ℚ) + 3) * (3 * (m : ℚ) + 2) * (3 * (m : ℚ) + 1) * h1

theorem hC1 (m : ℕ) :
    ((m : ℚ) + 1) * ((2 * (m + 1)).choose (m + 1) : ℚ) =
      2 * (2 * (m : ℚ) + 1) * ((2 * m).choose m : ℚ) := by
  have h := Nat.succ_mul_centralBinom_succ m
  rw [Nat.centralBinom_eq_two_mul_choose, Nat.centralBinom_eq_two_mul_choose] at h
  exact_mod_cast h

theorem hB2 (m : ℕ) :
    2 * (((m : ℚ) + 1) + 1) * (2 * ((m : ℚ) + 1) + 1) * ((3 * (m + 2)).choose (m + 2) : ℚ) =
      3 * (3 * ((m : ℚ) + 1) + 1) * (3 * ((m : ℚ) + 1) + 2) * ((3 * (m + 1)).choose (m + 1) : ℚ) := by
  have h := hB1 (m + 1)
  have e : ((m + 1 : ℕ) : ℚ) = (m : ℚ) + 1 := by push_cast; ring
  rw [e] at h
  exact h

theorem hC2 (m : ℕ) :
    (((m : ℚ) + 1) + 1) * ((2 * (m + 2)).choose (m + 2) : ℚ) =
      2 * (2 * ((m : ℚ) + 1) + 1) * ((2 * (m + 1)).choose (m + 1) : ℚ) := by
  have h := hC1 (m + 1)
  have e : ((m + 1 : ℕ) : ℚ) = (m : ℚ) + 1 := by push_cast; ring
  rw [e] at h
  exact h

theorem hB3 (m : ℕ) :
    2 * (((m : ℚ) + 2) + 1) * (2 * ((m : ℚ) + 2) + 1) * ((3 * (m + 3)).choose (m + 3) : ℚ) =
      3 * (3 * ((m : ℚ) + 2) + 1) * (3 * ((m : ℚ) + 2) + 2) * ((3 * (m + 2)).choose (m + 2) : ℚ) := by
  have h := hB1 (m + 2)
  have e : ((m + 2 : ℕ) : ℚ) = (m : ℚ) + 2 := by push_cast; ring
  rw [e] at h
  exact h

theorem hC3 (m : ℕ) :
    (((m : ℚ) + 2) + 1) * ((2 * (m + 3)).choose (m + 3) : ℚ) =
      2 * (2 * ((m : ℚ) + 2) + 1) * ((2 * (m + 2)).choose (m + 2) : ℚ) := by
  have h := hC1 (m + 2)
  have e : ((m + 2 : ℕ) : ℚ) = (m : ℚ) + 2 := by push_cast; ring
  rw [e] at h
  exact h

theorem pure (m : ℕ) :
    2 * ((m : ℚ) + 4) * (((m : ℚ) + 4) - 1) * (2 * ((m : ℚ) + 4) - 3) * (44 * ((m : ℚ) + 4) - 69) * (((m : ℚ) + 3) * ((m : ℚ) + 2) * ((m : ℚ) + 1)) *
        (2 * ((3 * (m + 3)).choose (m + 3) : ℚ) - ((2 * (m + 3)).choose (m + 3) : ℚ)) +
      (((m : ℚ) + 4) - 1) * (176 * ((m : ℚ) + 4) ^ 3 - 9591 * ((m : ℚ) + 4) ^ 2 + 38703 * ((m : ℚ) + 4) - 40640) * (((m : ℚ) + 4) * ((m : ℚ) + 2) * ((m : ℚ) + 1)) *
        (2 * ((3 * (m + 2)).choose (m + 2) : ℚ) - ((2 * (m + 2)).choose (m + 2) : ℚ)) +
      (-17479 * ((m : ℚ) + 4) ^ 4 + 218005 * ((m : ℚ) + 4) ^ 3 - 959616 * ((m : ℚ) + 4) ^ 2 + 1797890 * ((m : ℚ) + 4) - 1221920) * (((m : ℚ) + 4) * ((m : ℚ) + 3) * ((m : ℚ) + 1)) *
        (2 * ((3 * (m + 1)).choose (m + 1) : ℚ) - ((2 * (m + 1)).choose (m + 1) : ℚ)) +
      6 * (3 * ((m : ℚ) + 4) - 10) * (2 * ((m : ℚ) + 4) - 7) * (3 * ((m : ℚ) + 4) - 11) * (517 * ((m : ℚ) + 4) - 1198) * (((m : ℚ) + 4) * ((m : ℚ) + 3) * ((m : ℚ) + 2)) *
        (2 * ((3 * m).choose m : ℚ) - ((2 * m).choose m : ℚ)) = 0 := by
  have hne : (2 * ((m : ℚ) + 1) * (2 * (m : ℚ) + 1)) * (2 * (((m : ℚ) + 1) + 1) * (2 * ((m : ℚ) + 1) + 1)) * (2 * (((m : ℚ) + 2) + 1) * (2 * ((m : ℚ) + 2) + 1)) * ((m : ℚ) + 1) * (((m : ℚ) + 1) + 1) * (((m : ℚ) + 2) + 1) ≠ 0 := by positivity
  apply mul_left_cancel₀ hne
  linear_combination (22187520 + 204743808 * (m : ℚ) + 845726400 * (m : ℚ) ^ 2 + 2080936032 * (m : ℚ) ^ 3 + 3417494512 * (m : ℚ) ^ 4 + 3972066368 * (m : ℚ) ^ 5 + 3375892272 * (m : ℚ) ^ 6 + 2134912576 * (m : ℚ) ^ 7 + 1010947856 * (m : ℚ) ^ 8 + 357161280 * (m : ℚ) ^ 9 + 92774096 * (m : ℚ) ^ 10 + 17197792 * (m : ℚ) ^ 11 + 2152512 * (m : ℚ) ^ 12 + 162944 * (m : ℚ) ^ 13 + 5632 * (m : ℚ) ^ 14) * hB3 m +
    (-173560320 - 1461483648 * (m : ℚ) - 5379343488 * (m : ℚ) ^ 2 - 11437142112 * (m : ℚ) ^ 3 - 15549729696 * (m : ℚ) ^ 4 - 14013329040 * (m : ℚ) ^ 5 - 8225375296 * (m : ℚ) ^ 6 - 2739437456 * (m : ℚ) ^ 7 - 77174848 * (m : ℚ) ^ 8 + 419610384 * (m : ℚ) ^ 9 + 228294336 * (m : ℚ) ^ 10 + 64859568 * (m : ℚ) ^ 11 + 10970464 * (m : ℚ) ^ 12 + 1047104 * (m : ℚ) ^ 13 + 43648 * (m : ℚ) ^ 14) * hB2 m +
    (-360806400 - 3756326400 * (m : ℚ) - 17369911296 * (m : ℚ) ^ 2 - 47417877504 * (m : ℚ) ^ 3 - 85648339200 * (m : ℚ) ^ 4 - 108617341984 * (m : ℚ) ^ 5 - 100014889952 * (m : ℚ) ^ 6 - 68096704832 * (m : ℚ) ^ 7 - 34524600640 * (m : ℚ) ^ 8 - 12994474272 * (m : ℚ) ^ 9 - 3579860448 * (m : ℚ) ^ 10 - 700936064 * (m : ℚ) ^ 11 - 92316160 * (m : ℚ) ^ 12 - 7327744 * (m : ℚ) ^ 13 - 264704 * (m : ℚ) ^ 14) * hB1 m +
    (-110937600 - 1068094080 * (m : ℚ) - 4638119616 * (m : ℚ) ^ 2 - 12096132960 * (m : ℚ) ^ 3 - 21249344624 * (m : ℚ) ^ 4 - 26695320864 * (m : ℚ) ^ 5 - 24823594096 * (m : ℚ) ^ 6 - 17426347424 * (m : ℚ) ^ 7 - 9324564432 * (m : ℚ) ^ 8 - 3807702112 * (m : ℚ) ^ 9 - 1178193040 * (m : ℚ) ^ 10 - 271537152 * (m : ℚ) ^ 11 - 45158144 * (m : ℚ) ^ 12 - 5119744 * (m : ℚ) ^ 13 - 354048 * (m : ℚ) ^ 14 - 11264 * (m : ℚ) ^ 15) * hC3 m +
    (897868800 + 8328700800 * (m : ℚ) + 34516024992 * (m : ℚ) ^ 2 + 84910295712 * (m : ℚ) ^ 3 + 138639406856 * (m : ℚ) ^ 4 + 158819731624 * (m : ℚ) ^ 5 + 131266832504 * (m : ℚ) ^ 6 + 79022253736 * (m : ℚ) ^ 7 + 34358669288 * (m : ℚ) ^ 8 + 10414667992 * (m : ℚ) ^ 9 + 1984555336 * (m : ℚ) ^ 10 + 144702872 * (m : ℚ) ^ 11 - 32374544 * (m : ℚ) ^ 12 - 10549216 * (m : ℚ) ^ 13 - 1236032 * (m : ℚ) ^ 14 - 56320 * (m : ℚ) ^ 15) * hC2 m +
    (541209600 + 6987513600 * (m : ℚ) + 39870486144 * (m : ℚ) ^ 2 + 133987948416 * (m : ℚ) ^ 3 + 297814186368 * (m : ℚ) ^ 4 + 465494602992 * (m : ℚ) ^ 5 + 530326476936 * (m : ℚ) ^ 6 + 449759668944 * (m : ℚ) ^ 7 + 287020827864 * (m : ℚ) ^ 8 + 138143867616 * (m : ℚ) ^ 9 + 49835811096 * (m : ℚ) ^ 10 + 13256541264 * (m : ℚ) ^ 11 + 2520768168 * (m : ℚ) ^ 12 + 323907792 * (m : ℚ) ^ 13 + 25177824 * (m : ℚ) ^ 14 + 893376 * (m : ℚ) ^ 15) * hC1 m

end A007857Aux

open A007857Aux OMA.S_oeis_a007857 in
theorem OMA.solution : type_of% @OMA.S_oeis_a007857.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  have e1 : m + 4 - 1 = m + 3 := rfl
  have e2 : m + 4 - 2 = m + 2 := rfl
  have e3 : m + 4 - 3 = m + 1 := rfl
  rw [e1, e2, e3]
  have h0 : ((m : ℚ) + 4) * a (m + 4) = 2 * ((3 * (m + 3)).choose (m + 3) : ℚ) - ((2 * (m + 3)).choose (m + 3) : ℚ) := by
    have hk : ((m : ℚ) + 4) ≠ 0 := by positivity
    have e : m + 4 - 1 = m + 3 := rfl
    unfold a
    rw [e]
    push_cast
    field_simp
  have h1 : ((m : ℚ) + 3) * a (m + 3) = 2 * ((3 * (m + 2)).choose (m + 2) : ℚ) - ((2 * (m + 2)).choose (m + 2) : ℚ) := by
    have hk : ((m : ℚ) + 3) ≠ 0 := by positivity
    have e : m + 3 - 1 = m + 2 := rfl
    unfold a
    rw [e]
    push_cast
    field_simp
  have h2 : ((m : ℚ) + 2) * a (m + 2) = 2 * ((3 * (m + 1)).choose (m + 1) : ℚ) - ((2 * (m + 1)).choose (m + 1) : ℚ) := by
    have hk : ((m : ℚ) + 2) ≠ 0 := by positivity
    have e : m + 2 - 1 = m + 1 := rfl
    unfold a
    rw [e]
    push_cast
    field_simp
  have h3 : ((m : ℚ) + 1) * a (m + 1) = 2 * ((3 * m).choose m : ℚ) - ((2 * m).choose m : ℚ) := by
    have hk : ((m : ℚ) + 1) ≠ 0 := by positivity
    have e : m + 1 - 1 = m := rfl
    unfold a
    rw [e]
    push_cast
    field_simp
  have hD : ((m : ℚ) + 4) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * ((m : ℚ) + 1) ≠ 0 := by positivity
  apply mul_left_cancel₀ hD
  push_cast
  linear_combination (2 * ((m : ℚ) + 4) * (((m : ℚ) + 4) - 1) * (2 * ((m : ℚ) + 4) - 3) * (44 * ((m : ℚ) + 4) - 69) * (((m : ℚ) + 3) * ((m : ℚ) + 2) * ((m : ℚ) + 1))) * h0 + ((((m : ℚ) + 4) - 1) * (176 * ((m : ℚ) + 4) ^ 3 - 9591 * ((m : ℚ) + 4) ^ 2 + 38703 * ((m : ℚ) + 4) - 40640) * (((m : ℚ) + 4) * ((m : ℚ) + 2) * ((m : ℚ) + 1))) * h1 + ((-17479 * ((m : ℚ) + 4) ^ 4 + 218005 * ((m : ℚ) + 4) ^ 3 - 959616 * ((m : ℚ) + 4) ^ 2 + 1797890 * ((m : ℚ) + 4) - 1221920) * (((m : ℚ) + 4) * ((m : ℚ) + 3) * ((m : ℚ) + 1))) * h2 + (6 * (3 * ((m : ℚ) + 4) - 10) * (2 * ((m : ℚ) + 4) - 7) * (3 * ((m : ℚ) + 4) - 11) * (517 * ((m : ℚ) + 4) - 1198) * (((m : ℚ) + 4) * ((m : ℚ) + 3) * ((m : ℚ) + 2))) * h3 + A007857Aux.pure m
