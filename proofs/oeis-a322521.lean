import OMAStatements.S_oeis_a322521
import Mathlib

open OMA.S_oeis_a322521

private def per (v : ℕ) : Prop := ∃ m, 0 < m ∧ collatz^[m] v = v

private lemma itc (m x : ℕ) : collatz^[m] (collatz x) = collatz (collatz^[m] x) := by
  rw [← Function.iterate_succ_apply, Function.iterate_succ_apply']

private lemma T2 (v : ℕ) : collatz (2 * v) = v := by
  unfold collatz; rw [if_pos (by omega)]; omega

private lemma T3 (v : ℕ) (h : (v + 2) % 6 = 0) : collatz ((v - 1) / 3) = v := by
  unfold collatz; rw [if_neg (by omega)]; omega

private lemma enc_succ (v r : ℕ) : enc v (r + 1) =
    if 4 < v ∧ (v + 2) % 6 = 0 then
      (if r % 2 = 0 then enc (2 * v) (r / 2) else enc ((v - 1) / 3) (r / 2))
    else enc (2 * v) r := by
  rw [enc]

private lemma desc (r : ℕ) : ∀ v, ∃ d, collatz^[d] (enc v r) = v ∧ (0 < r → 0 < d) := by
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro v
    rcases r with _ | s
    · exact ⟨0, by simp [enc], by omega⟩
    · have step : ∀ c t, t < s + 1 → collatz c = v → enc v (s + 1) = enc c t →
          ∃ d, collatz^[d] (enc v (s + 1)) = v ∧ (0 < s + 1 → 0 < d) := by
        intro c t ht hc he
        obtain ⟨d, hd, -⟩ := ih t ht c
        refine ⟨d + 1, ?_, fun _ => by omega⟩
        rw [he, Function.iterate_succ_apply', hd, hc]
      by_cases hb : 4 < v ∧ (v + 2) % 6 = 0
      · by_cases hp : s % 2 = 0
        · exact step (2 * v) (s / 2) (by omega) (T2 v) (by rw [enc_succ, if_pos hb, if_pos hp])
        · exact step ((v - 1) / 3) (s / 2) (by omega) (T3 v hb.2) (by rw [enc_succ, if_pos hb, if_neg hp])
      · exact step (2 * v) s (by omega) (T2 v) (by rw [enc_succ, if_neg hb])

private lemma nper_child (v c : ℕ) (hv : ¬ per v) (hc : collatz c = v) : ¬ per c := by
  rintro ⟨m, hm, h⟩
  exact hv ⟨m, hm, by rw [← hc, itc, h]⟩

private lemma cross (N x y v d1 d2 : ℕ) (h1 : collatz^[d1] N = x) (h2 : collatz^[d2] N = y)
    (hx : collatz x = v) (hy : collatz y = v) (hxy : x ≠ y) (hv : ¬ per v) (hle : d1 ≤ d2) : False := by
  obtain ⟨k, rfl⟩ : ∃ k, d2 = k + d1 := ⟨d2 - d1, by omega⟩
  rw [Function.iterate_add_apply, h1] at h2
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact hxy (by simpa using h2)
  · exact hv ⟨k, hk, by rw [← hx, itc, h2, hy, hx]⟩

private lemma inj (n : ℕ) : ∀ r1 r2 v, r1 + r2 = n → ¬ per v → enc v r1 = enc v r2 → r1 = r2 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro r1 r2 v hn hv he
    rcases r1 with _ | s1 <;> rcases r2 with _ | s2
    · rfl
    · exfalso
      obtain ⟨d, hd, hpos⟩ := desc (s2 + 1) v
      rw [← he] at hd
      exact hv ⟨d, hpos (by omega), by simpa [enc] using hd⟩
    · exfalso
      obtain ⟨d, hd, hpos⟩ := desc (s1 + 1) v
      rw [he] at hd
      exact hv ⟨d, hpos (by omega), by simpa [enc] using hd⟩
    · rw [enc_succ, enc_succ] at he
      by_cases hb : 4 < v ∧ (v + 2) % 6 = 0
      · rw [if_pos hb, if_pos hb] at he
        have n2 := nper_child v (2 * v) hv (T2 v)
        have n3 := nper_child v ((v - 1) / 3) hv (T3 v hb.2)
        have hne : 2 * v ≠ (v - 1) / 3 := by omega
        by_cases p1 : s1 % 2 = 0 <;> by_cases p2 : s2 % 2 = 0 <;> simp only [p1, p2, if_true, if_false] at he
        · have := ih (s1 / 2 + s2 / 2) (by omega) _ _ _ rfl n2 he; omega
        · exfalso
          obtain ⟨d1, h1, -⟩ := desc (s1 / 2) (2 * v)
          obtain ⟨d2, h2, -⟩ := desc (s2 / 2) ((v - 1) / 3)
          rw [he] at h1
          rcases Nat.le_total d1 d2 with h | h
          · exact cross _ _ _ v d1 d2 h1 h2 (T2 v) (T3 v hb.2) hne hv h
          · exact cross _ _ _ v d2 d1 h2 h1 (T3 v hb.2) (T2 v) hne.symm hv h
        · exfalso
          obtain ⟨d1, h1, -⟩ := desc (s1 / 2) ((v - 1) / 3)
          obtain ⟨d2, h2, -⟩ := desc (s2 / 2) (2 * v)
          rw [he] at h1
          rcases Nat.le_total d1 d2 with h | h
          · exact cross _ _ _ v d1 d2 h1 h2 (T3 v hb.2) (T2 v) hne.symm hv h
          · exact cross _ _ _ v d2 d1 h2 h1 (T2 v) (T3 v hb.2) hne hv h
        · have := ih (s1 / 2 + s2 / 2) (by omega) _ _ _ rfl n3 he; omega
      · rw [if_neg hb, if_neg hb] at he
        have := ih (s1 + s2) (by omega) _ _ _ rfl (nper_child v (2 * v) hv (T2 v)) he
        omega

private lemma orb (m x : ℕ) (hx : x = 1 ∨ x = 2 ∨ x = 4) : collatz^[m] x = 1 ∨ collatz^[m] x = 2 ∨ collatz^[m] x = 4 := by
  induction m with
  | zero => simpa using hx
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    rcases ih with h | h | h <;> rw [h] <;> simp [collatz]

private lemma nper8 : ¬ per 8 := by
  rintro ⟨m, hm, h⟩
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [Function.iterate_succ_apply, show collatz 8 = 4 by rfl] at h
  rcases orb k 4 (by simp) with h' | h' | h' <;> omega

private lemma enc1 (s : ℕ) : enc 1 (s + 3) = enc 8 s := by
  rw [enc_succ, if_neg (by omega), enc_succ, if_neg (by omega), enc_succ, if_neg (by omega)]

private lemma inj1 (r1 r2 : ℕ) (he : enc 1 r1 = enc 1 r2) : r1 = r2 := by
  have e0 : enc 1 0 = 1 := by rw [enc]
  have e1 : enc 1 1 = 2 := by rw [enc_succ, if_neg (by omega), enc]
  have e2 : enc 1 2 = 4 := by rw [enc_succ, if_neg (by omega), enc_succ, if_neg (by omega), enc]
  have small : ∀ r, r < 3 → enc 1 r = 1 ∨ enc 1 r = 2 ∨ enc 1 r = 4 := by
    intro r hr; interval_cases r <;> simp [e0, e1, e2]
  have big : ∀ s, ¬ (enc 8 s = 1 ∨ enc 8 s = 2 ∨ enc 8 s = 4) := by
    intro s hs
    obtain ⟨d, hd, -⟩ := desc s 8
    rcases orb d _ hs with h | h | h <;> omega
  rcases Nat.lt_or_ge r1 3 with h1 | h1 <;> rcases Nat.lt_or_ge r2 3 with h2 | h2
  · interval_cases r1 <;> interval_cases r2 <;> simp_all
  · obtain ⟨s, rfl⟩ : ∃ s, r2 = s + 3 := ⟨r2 - 3, by omega⟩
    rw [enc1] at he; exact absurd (he ▸ small r1 h1) (big s)
  · obtain ⟨s, rfl⟩ : ∃ s, r1 = s + 3 := ⟨r1 - 3, by omega⟩
    rw [enc1] at he; exact absurd (he.symm ▸ small r2 h2) (big s)
  · obtain ⟨s, rfl⟩ : ∃ s, r1 = s + 3 := ⟨r1 - 3, by omega⟩
    obtain ⟨t, rfl⟩ : ∃ t, r2 = t + 3 := ⟨r2 - 3, by omega⟩
    rw [enc1, enc1] at he
    have := inj (s + t) s t 8 rfl nper8 he
    omega

private lemma pos (r : ℕ) : ∀ v, 1 ≤ v → 1 ≤ enc v r := by
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro v hv
    rcases r with _ | s
    · simpa [enc] using hv
    · rw [enc_succ]
      split_ifs with hb hp
      · exact ih _ (by omega) _ (by omega)
      · exact ih _ (by omega) _ (by omega)
      · exact ih _ (by omega) _ (by omega)

theorem OMA.solution : type_of% @OMA.S_oeis_a322521.main := by
  intro _ k
  refine ⟨A319303 k, pos k 1 le_rfl, ?_⟩
  have h : ∃ j, A319303 j = A319303 k := ⟨k, rfl⟩
  unfold a
  rw [dif_pos h]
  congr 1
  exact inj1 _ _ (Nat.find_spec h)
