import OMAReductions.R_OeisA153330_conjecture3_R1

/-!
# Proof of `OeisA153330.conjecture3.R1.H1`

From the four inequalities for `n ≥ 8`, cross-multiplication yields:
- `2 * (2 ^ d * 3 ^ a) < 3 * (3 ^ c * 2 ^ b)` (using `8 * (n + 1) ≤ 9 * n`), and
- `3 * (2 ^ b * 3 ^ c) < 4 * (3 ^ a * 2 ^ d)` (using `n < n + 1`).

Splitting on the relative order of `(a, c)` and `(b, d)`:
- Opposite-sign cases force `a = c` and `b = d`, giving difference `0 = 5 * 0 + 8 * 0`.
- Same-sign cases reduce to `(u, v) : ℕ × ℕ` with either `2 * 2 ^ v < 3 * 3 ^ u < 4 * 2 ^ v`
  (positive difference `u + v`) or `2 * 3 ^ u < 3 * 2 ^ v < 4 * 3 ^ u` (negative difference
  `-(u + v)`). Every natural number `≥ 28` has the form `5 * x + 8 * y`, and the finite set
  of pairs with `u + v < 28` is verified by `decide`.
-/

namespace OMA.P_OeisA153330_H1

private lemma rep_5_8_of_ge_28 : ∀ m : ℕ, 28 ≤ m → ∃ x y : ℕ, m = 5 * x + 8 * y := by
  intro m hm
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases h33 : m < 33
    · have hcases : m = 28 ∨ m = 29 ∨ m = 30 ∨ m = 31 ∨ m = 32 := by omega
      rcases hcases with rfl | rfl | rfl | rfl | rfl
      · exact ⟨4, 1, by omega⟩
      · exact ⟨1, 3, by omega⟩
      · exact ⟨6, 0, by omega⟩
      · exact ⟨3, 2, by omega⟩
      · exact ⟨0, 4, by omega⟩
    · obtain ⟨x, y, hxy⟩ := ih (m - 5) (by omega) (by omega)
      exact ⟨x + 1, y, by omega⟩

private def posCheck (u v : ℕ) : Bool :=
  !(2 * 2 ^ v < 3 * 3 ^ u && 3 * 3 ^ u < 4 * 2 ^ v) ||
    (u + v == 1 || u + v == 3 || u + v == 6 ||
      (List.range 7).any fun x => (List.range 5).any fun y => u + v == 5 * x + 8 * y)

private def negCheck (u v : ℕ) : Bool :=
  !(2 * 3 ^ u < 3 * 2 ^ v && 3 * 2 ^ v < 4 * 3 ^ u) ||
    (List.range 7).any fun x => (List.range 5).any fun y => u + v == 5 * x + 8 * y

private lemma posCheck_all :
    ∀ u : Fin 28, ∀ v : Fin 28, posCheck u.1 v.1 = true := by
  decide

private lemma negCheck_all :
    ∀ u : Fin 28, ∀ v : Fin 28, negCheck u.1 v.1 = true := by
  decide

private lemma pos_small {u v : ℕ} (hu : u < 28) (hv : v < 28)
    (h1 : 2 * 2 ^ v < 3 * 3 ^ u) (h2 : 3 * 3 ^ u < 4 * 2 ^ v) :
    u + v = 1 ∨ u + v = 3 ∨ u + v = 6 ∨ ∃ x y : ℕ, u + v = 5 * x + 8 * y := by
  have hc := posCheck_all ⟨u, hu⟩ ⟨v, hv⟩
  simp only [posCheck, Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff,
    decide_eq_false_iff_not, beq_iff_eq, List.any_eq_true, List.mem_range] at hc
  rcases hc with (h | h) | (((h | h) | h) | ⟨x, _, y, _, hxy⟩)
  · exact False.elim (h h1)
  · exact False.elim (h h2)
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr ⟨x, y, hxy⟩))

private lemma neg_small {u v : ℕ} (hu : u < 28) (hv : v < 28)
    (h1 : 2 * 3 ^ u < 3 * 2 ^ v) (h2 : 3 * 2 ^ v < 4 * 3 ^ u) :
    ∃ x y : ℕ, u + v = 5 * x + 8 * y := by
  have hc := negCheck_all ⟨u, hu⟩ ⟨v, hv⟩
  simp only [negCheck, Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff,
    decide_eq_false_iff_not, beq_iff_eq, List.any_eq_true, List.mem_range] at hc
  rcases hc with (h | h) | ⟨x, _, y, _, hxy⟩
  · exact False.elim (h h1)
  · exact False.elim (h h2)
  · exact ⟨x, y, hxy⟩

theorem h1_proof : OMA.R_OeisA153330_conjecture3_R1.H1 := by
  intro a b c d n hn h1 h2 h3 h4
  have hn_pos : 0 < n := by omega
  have hA : 2 * (2 ^ d * 3 ^ a) < 3 * (3 ^ c * 2 ^ b) := by
    have hmul : 3 * n * (2 * (2 ^ d * 3 ^ a)) < 3 * n * (3 * (3 ^ c * 2 ^ b)) := by
      have h4' : 3 * 2 ^ d * (2 * (3 ^ a * n)) < 4 * (3 ^ c * (n + 1)) * (2 * (3 ^ a * n)) :=
        Nat.mul_lt_mul_of_pos_right h4 (by positivity)
      have h89 : 8 * (n + 1) ≤ 9 * n := by omega
      have hstep1 : 4 * (3 ^ c * (n + 1)) * (2 * (3 ^ a * n)) =
          8 * (n + 1) * (3 ^ c * (3 ^ a * n)) := by ring
      have hstep2 : 8 * (n + 1) * (3 ^ c * (3 ^ a * n)) ≤ 9 * n * (3 ^ c * 2 ^ b) :=
        Nat.mul_le_mul h89 (Nat.mul_le_mul_left _ h1)
      have hlhs : 3 * n * (2 * (2 ^ d * 3 ^ a)) = 3 * 2 ^ d * (2 * (3 ^ a * n)) := by ring
      have hrhs : 3 * n * (3 * (3 ^ c * 2 ^ b)) = 9 * n * (3 ^ c * 2 ^ b) := by ring
      rw [hlhs, hrhs]
      exact lt_of_lt_of_le (by rwa [hstep1] at h4') hstep2
    exact Nat.lt_of_mul_lt_mul_left hmul
  have hB : 3 * (2 ^ b * 3 ^ c) < 4 * (3 ^ a * 2 ^ d) := by
    have hmul : (n + 1) * (3 * (2 ^ b * 3 ^ c)) < (n + 1) * (4 * (3 ^ a * 2 ^ d)) := by
      have h2' : 3 * 2 ^ b * (3 ^ c * (n + 1)) < 4 * (3 ^ a * n) * (3 ^ c * (n + 1)) :=
        Nat.mul_lt_mul_of_pos_right h2 (by positivity)
      have hstep1 : 4 * (3 ^ a * n) * (3 ^ c * (n + 1)) ≤ 4 * (3 ^ a * n) * 2 ^ d :=
        Nat.mul_le_mul_left _ h3
      have hstep2 : 4 * (3 ^ a * n) * 2 ^ d ≤ (n + 1) * (4 * (3 ^ a * 2 ^ d)) := by
        have : n ≤ n + 1 := Nat.le_succ n
        calc 4 * (3 ^ a * n) * 2 ^ d = n * (4 * (3 ^ a * 2 ^ d)) := by ring
          _ ≤ (n + 1) * (4 * (3 ^ a * 2 ^ d)) := Nat.mul_le_mul_right _ this
      have hlhs : (n + 1) * (3 * (2 ^ b * 3 ^ c)) = 3 * 2 ^ b * (3 ^ c * (n + 1)) := by ring
      rw [hlhs]
      exact lt_of_lt_of_le h2' (le_trans hstep1 hstep2)
    exact Nat.lt_of_mul_lt_mul_left hmul
  by_cases hac : a ≤ c
  · obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le hac
    by_cases hbd : b ≤ d
    · obtain ⟨v, rfl⟩ := Nat.exists_eq_add_of_le hbd
      have hA' : 2 * 2 ^ v < 3 * 3 ^ u := by
        have hmul : 2 ^ b * 3 ^ a * (2 * 2 ^ v) < 2 ^ b * 3 ^ a * (3 * 3 ^ u) := by
          have hl : 2 ^ b * 3 ^ a * (2 * 2 ^ v) = 2 * (2 ^ (b + v) * 3 ^ a) := by
            rw [pow_add]; ring
          have hr : 2 ^ b * 3 ^ a * (3 * 3 ^ u) = 3 * (3 ^ (a + u) * 2 ^ b) := by
            rw [pow_add]; ring
          rw [hl, hr]; exact hA
        exact Nat.lt_of_mul_lt_mul_left hmul
      have hB' : 3 * 3 ^ u < 4 * 2 ^ v := by
        have hmul : 2 ^ b * 3 ^ a * (3 * 3 ^ u) < 2 ^ b * 3 ^ a * (4 * 2 ^ v) := by
          have hl : 2 ^ b * 3 ^ a * (3 * 3 ^ u) = 3 * (2 ^ b * 3 ^ (a + u)) := by
            rw [pow_add]; ring
          have hr : 2 ^ b * 3 ^ a * (4 * 2 ^ v) = 4 * (3 ^ a * 2 ^ (b + v)) := by
            rw [pow_add]; ring
          rw [hl, hr]; exact hB
        exact Nat.lt_of_mul_lt_mul_left hmul
      rw [show ((a + u : ℕ) + (b + v : ℕ) : ℤ) - (a + b : ℤ) = ((u + v : ℕ) : ℤ) by push_cast; ring]
      have hna : (((u + v : ℕ) : ℤ)).natAbs = u + v := Int.natAbs_natCast (u + v)
      by_cases huv : 28 ≤ u + v
      · exact Or.inr (Or.inr (Or.inr (by rw [hna]; exact rep_5_8_of_ge_28 (u + v) huv)))
      · have hres := pos_small (by omega) (by omega) hA' hB'
        rcases hres with h | h | h | h
        · exact Or.inl (by exact_mod_cast h)
        · exact Or.inr (Or.inl (by exact_mod_cast h))
        · exact Or.inr (Or.inr (Or.inl (by exact_mod_cast h)))
        · exact Or.inr (Or.inr (Or.inr (by rw [hna]; exact h)))
    · obtain ⟨v, rfl⟩ := Nat.exists_eq_add_of_le (le_of_not_ge hbd)
      have hB' : 3 * (2 ^ v * 3 ^ u) < 4 := by
        have hmul : 2 ^ d * 3 ^ a * (3 * (2 ^ v * 3 ^ u)) < 2 ^ d * 3 ^ a * 4 := by
          have hl : 2 ^ d * 3 ^ a * (3 * (2 ^ v * 3 ^ u)) = 3 * (2 ^ (d + v) * 3 ^ (a + u)) := by
            rw [pow_add, pow_add]; ring
          have hr : 2 ^ d * 3 ^ a * 4 = 4 * (3 ^ a * 2 ^ d) := by ring
          rw [hl, hr]; exact hB
        exact Nat.lt_of_mul_lt_mul_left hmul
      have h1_le : 1 ≤ 2 ^ v * 3 ^ u := Nat.mul_pos (by positivity) (by positivity)
      have heq1 : 2 ^ v * 3 ^ u = 1 := by omega
      have hv0 : v = 0 := by
        by_contra hvne
        have : 2 ≤ 2 ^ v := le_trans (by norm_num : 2 ≤ 2 ^ 1) (Nat.pow_le_pow_right (by norm_num) (by omega))
        have : 1 ≤ 3 ^ u := Nat.one_le_pow _ _ (by norm_num)
        nlinarith
      have hu0 : u = 0 := by
        by_contra hune
        have : 3 ≤ 3 ^ u := le_trans (by norm_num : 3 ≤ 3 ^ 1) (Nat.pow_le_pow_right (by norm_num) (by omega))
        have : 1 ≤ 2 ^ v := Nat.one_le_pow _ _ (by norm_num)
        nlinarith
      subst hv0 hu0
      exact Or.inr (Or.inr (Or.inr ⟨0, 0, by simp⟩))
  · obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le (le_of_not_ge hac)
    by_cases hbd : b ≤ d
    · obtain ⟨v, rfl⟩ := Nat.exists_eq_add_of_le hbd
      have hA' : 2 * (2 ^ v * 3 ^ u) < 3 := by
        have hmul : 2 ^ b * 3 ^ c * (2 * (2 ^ v * 3 ^ u)) < 2 ^ b * 3 ^ c * 3 := by
          have hl : 2 ^ b * 3 ^ c * (2 * (2 ^ v * 3 ^ u)) = 2 * (2 ^ (b + v) * 3 ^ (c + u)) := by
            rw [pow_add, pow_add]; ring
          have hr : 2 ^ b * 3 ^ c * 3 = 3 * (3 ^ c * 2 ^ b) := by ring
          rw [hl, hr]; exact hA
        exact Nat.lt_of_mul_lt_mul_left hmul
      have h1_le : 1 ≤ 2 ^ v * 3 ^ u := Nat.mul_pos (by positivity) (by positivity)
      have heq1 : 2 ^ v * 3 ^ u = 1 := by omega
      have hv0 : v = 0 := by
        by_contra hvne
        have : 2 ≤ 2 ^ v := le_trans (by norm_num : 2 ≤ 2 ^ 1) (Nat.pow_le_pow_right (by norm_num) (by omega))
        have : 1 ≤ 3 ^ u := Nat.one_le_pow _ _ (by norm_num)
        nlinarith
      have hu0 : u = 0 := by
        by_contra hune
        have : 3 ≤ 3 ^ u := le_trans (by norm_num : 3 ≤ 3 ^ 1) (Nat.pow_le_pow_right (by norm_num) (by omega))
        have : 1 ≤ 2 ^ v := Nat.one_le_pow _ _ (by norm_num)
        nlinarith
      subst hv0 hu0
      exact Or.inr (Or.inr (Or.inr ⟨0, 0, by simp⟩))
    · obtain ⟨v, rfl⟩ := Nat.exists_eq_add_of_le (le_of_not_ge hbd)
      have hA' : 2 * 3 ^ u < 3 * 2 ^ v := by
        have hmul : 2 ^ d * 3 ^ c * (2 * 3 ^ u) < 2 ^ d * 3 ^ c * (3 * 2 ^ v) := by
          have hl : 2 ^ d * 3 ^ c * (2 * 3 ^ u) = 2 * (2 ^ d * 3 ^ (c + u)) := by
            rw [pow_add]; ring
          have hr : 2 ^ d * 3 ^ c * (3 * 2 ^ v) = 3 * (3 ^ c * 2 ^ (d + v)) := by
            rw [pow_add]; ring
          rw [hl, hr]; exact hA
        exact Nat.lt_of_mul_lt_mul_left hmul
      have hB' : 3 * 2 ^ v < 4 * 3 ^ u := by
        have hmul : 2 ^ d * 3 ^ c * (3 * 2 ^ v) < 2 ^ d * 3 ^ c * (4 * 3 ^ u) := by
          have hl : 2 ^ d * 3 ^ c * (3 * 2 ^ v) = 3 * (2 ^ (d + v) * 3 ^ c) := by
            rw [pow_add]; ring
          have hr : 2 ^ d * 3 ^ c * (4 * 3 ^ u) = 4 * (3 ^ (c + u) * 2 ^ d) := by
            rw [pow_add]; ring
          rw [hl, hr]; exact hB
        exact Nat.lt_of_mul_lt_mul_left hmul
      have hnatAbs : ((c + d : ℤ) - ((c + u : ℕ) + (d + v : ℕ) : ℤ)).natAbs = u + v := by
        have h1 : (c + d : ℤ) - ((c + u : ℕ) + (d + v : ℕ) : ℤ) = -((u + v : ℕ) : ℤ) := by
          push_cast; ring
        rw [h1, Int.natAbs_neg, Int.natAbs_natCast]
      refine Or.inr (Or.inr (Or.inr ?_))
      rw [hnatAbs]
      by_cases huv : 28 ≤ u + v
      · exact rep_5_8_of_ge_28 (u + v) huv
      · exact neg_small (by omega) (by omega) hA' hB'

end OMA.P_OeisA153330_H1

theorem OMA.solution : OMA.R_OeisA153330_conjecture3_R1.H1 :=
  OMA.P_OeisA153330_H1.h1_proof
