import OMAStatements.S_oeis_a115770

-- Problem: A115770: Numbers k such that 7*k = A048720(11,k), where A048720 is carryless base-2 multiplication.
-- Upstream: formal-conjectures statements/oeis-a115770.lean:0 (declaration OMA.S_oeis_a115770.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: for constants A, B and a state (u, v) let P(u, v, m) be A*m + u = clmul B m XOR v.
-- Writing m = 2*m' + e with a binary digit e, P(u, v, m) holds iff the low bits agree,
-- (u + A*e) % 2 = (v XOR B*e) % 2, and P((u + A*e) / 2, (v XOR B*e) / 2, m') holds; and
-- P(u, v, 0) holds iff u = v. So each condition is a finite automaton read from the low bits
-- (u stays below A, v below 2*B). The two automata for (7, 11) and (5, 13) are compared on the
-- 10 state pairs reachable from (0, 0, 0, 0): in each pair both states accept or both reject at 0,
-- and for each digit either both low-bit tests pass and the next pair is again in the list, or both
-- fail, or one passes into a dead state (a state from which no m is accepted; the 4 dead states of
-- the second automaton are closed under passing steps and none accepts at 0). Strong induction on m
-- then gives the equivalence for every pair in the list, in particular for (0, 0, 0, 0).

namespace G15A115770

open OMA.S_oeis_a115770

theorem clmul_zero (b : ℕ) : clmul b 0 = 0 := by
  rw [clmul.eq_1 b 0, dif_pos rfl]

theorem clmul_step (b m e : ℕ) (he : e < 2) :
    clmul b (2 * m + e) = (e * b) ^^^ (2 * clmul b m) := by
  rcases Nat.eq_zero_or_pos (2 * m + e) with h0 | hpos
  · have hm : m = 0 := by omega
    have he0 : e = 0 := by omega
    subst hm
    subst he0
    simp only [Nat.mul_zero, Nat.add_zero, clmul_zero, Nat.zero_mul, Nat.zero_xor]
  · rw [clmul.eq_1 b (2 * m + e), dif_neg (show ¬(2 * m + e = 0) by omega)]
    have h1 : (2 * m + e) / 2 = m := by omega
    rw [h1]
    rcases (show e = 0 ∨ e = 1 by omega) with h | h
    · subst h
      rw [if_neg (show ¬((2 * m + 0) % 2 = 1) by omega), Nat.zero_mul]
    · subst h
      rw [if_pos (show (2 * m + 1) % 2 = 1 by omega), Nat.one_mul]

theorem xsplit (Y W : ℕ) : (2 * Y) ^^^ W = 2 * (Y ^^^ (W / 2)) + W % 2 := by
  have e := Nat.div_add_mod ((2 * Y) ^^^ W) (2 ^ 1)
  rw [Nat.xor_div_two_pow, Nat.xor_mod_two_pow, Nat.pow_one] at e
  have h1 : 2 * Y / 2 = Y := by omega
  have h2 : 2 * Y % 2 = 0 := by omega
  rw [h1, h2, Nat.zero_xor] at e
  exact e.symm

theorem stepP (A B u v m e : ℕ) (he : e < 2) :
    (A * (2 * m + e) + u = clmul B (2 * m + e) ^^^ v) ↔
      ((u + A * e) % 2 = (v ^^^ B * e) % 2 ∧
        A * m + (u + A * e) / 2 = clmul B m ^^^ ((v ^^^ B * e) / 2)) := by
  rw [clmul_step B m e he]
  have h1 : (e * B ^^^ 2 * clmul B m) ^^^ v =
      2 * (clmul B m ^^^ ((v ^^^ B * e) / 2)) + (v ^^^ B * e) % 2 := by
    rw [Nat.xor_comm (e * B) (2 * clmul B m), Nat.xor_assoc, Nat.mul_comm e B,
      Nat.xor_comm (B * e) v]
    exact xsplit (clmul B m) (v ^^^ B * e)
  have h2 : A * (2 * m + e) = 2 * (A * m) + A * e := by ring
  rw [h1, h2]
  constructor
  · intro h
    exact ⟨by omega, by omega⟩
  · intro h
    omega

theorem dead_gen (A B : ℕ) (L : List (ℕ × ℕ))
    (h0 : ∀ p ∈ L, p.1 ≠ p.2)
    (hs : ∀ p ∈ L, ∀ e, e < 2 → (p.1 + A * e) % 2 = (p.2 ^^^ B * e) % 2 →
      ((p.1 + A * e) / 2, (p.2 ^^^ B * e) / 2) ∈ L) :
    ∀ m, ∀ p ∈ L, A * m + p.1 ≠ clmul B m ^^^ p.2 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro p hp h
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      simp only [clmul_zero, Nat.zero_xor, Nat.mul_zero, Nat.zero_add] at h
      exact h0 p hp h
    · have hmd : m = 2 * (m / 2) + m % 2 := (Nat.div_add_mod m 2).symm
      have he : m % 2 < 2 := by omega
      have hlt : m / 2 < m := by omega
      rw [hmd, stepP A B p.1 p.2 (m / 2) (m % 2) he] at h
      exact ih (m / 2) hlt _ (hs p hp (m % 2) he h.1) h.2

theorem bisim_gen (A B C D : ℕ) (R : List (ℕ × ℕ × ℕ × ℕ)) (DP DQ : List (ℕ × ℕ))
    (hP : ∀ m, ∀ p ∈ DP, A * m + p.1 ≠ clmul B m ^^^ p.2)
    (hQ : ∀ m, ∀ q ∈ DQ, C * m + q.1 ≠ clmul D m ^^^ q.2)
    (h0 : ∀ s ∈ R, (s.1 = s.2.1 ↔ s.2.2.1 = s.2.2.2))
    (hs : ∀ s ∈ R, ∀ e, e < 2 →
      ((s.1 + A * e) % 2 = (s.2.1 ^^^ B * e) % 2 ∧
          (s.2.2.1 + C * e) % 2 = (s.2.2.2 ^^^ D * e) % 2 ∧
          ((s.1 + A * e) / 2, (s.2.1 ^^^ B * e) / 2, (s.2.2.1 + C * e) / 2,
            (s.2.2.2 ^^^ D * e) / 2) ∈ R) ∨
      ((s.1 + A * e) % 2 ≠ (s.2.1 ^^^ B * e) % 2 ∧
          (s.2.2.1 + C * e) % 2 ≠ (s.2.2.2 ^^^ D * e) % 2) ∨
      ((s.1 + A * e) % 2 = (s.2.1 ^^^ B * e) % 2 ∧
          (s.2.2.1 + C * e) % 2 ≠ (s.2.2.2 ^^^ D * e) % 2 ∧
          ((s.1 + A * e) / 2, (s.2.1 ^^^ B * e) / 2) ∈ DP) ∨
      ((s.1 + A * e) % 2 ≠ (s.2.1 ^^^ B * e) % 2 ∧
          (s.2.2.1 + C * e) % 2 = (s.2.2.2 ^^^ D * e) % 2 ∧
          ((s.2.2.1 + C * e) / 2, (s.2.2.2 ^^^ D * e) / 2) ∈ DQ)) :
    ∀ m, ∀ s ∈ R,
      (A * m + s.1 = clmul B m ^^^ s.2.1 ↔ C * m + s.2.2.1 = clmul D m ^^^ s.2.2.2) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro s hs'
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      simp only [clmul_zero, Nat.zero_xor, Nat.mul_zero, Nat.zero_add]
      exact h0 s hs'
    · have hmd : m = 2 * (m / 2) + m % 2 := (Nat.div_add_mod m 2).symm
      have he : m % 2 < 2 := by omega
      have hlt : m / 2 < m := by omega
      rw [hmd, stepP A B s.1 s.2.1 (m / 2) (m % 2) he,
        stepP C D s.2.2.1 s.2.2.2 (m / 2) (m % 2) he]
      rcases hs s hs' (m % 2) he with ⟨c1, c2, hn⟩ | ⟨c1, c2⟩ | ⟨c1, c2, hn⟩ | ⟨c1, c2, hn⟩
      · have hi := ih (m / 2) hlt _ hn
        exact ⟨fun h => ⟨c2, hi.1 h.2⟩, fun h => ⟨c1, hi.2 h.2⟩⟩
      · exact ⟨fun h => absurd h.1 c1, fun h => absurd h.1 c2⟩
      · exact ⟨fun h => absurd h.2 (hP (m / 2) _ hn), fun h => absurd h.1 c2⟩
      · exact ⟨fun h => absurd h.1 c1, fun h => absurd h.2 (hQ (m / 2) _ hn)⟩

theorem deadP : ∀ m, ∀ p ∈ ([] : List (ℕ × ℕ)), 7 * m + p.1 ≠ clmul 11 m ^^^ p.2 :=
  dead_gen 7 11 [] (by decide) (by decide)

theorem deadQ : ∀ m, ∀ q ∈ ([(0, 1), (1, 3), (3, 7), (4, 5)] : List (ℕ × ℕ)),
    5 * m + q.1 ≠ clmul 13 m ^^^ q.2 :=
  dead_gen 5 13 [(0, 1), (1, 3), (3, 7), (4, 5)] (by decide) (by decide)

theorem bisim : ∀ m, ∀ s ∈ ([(0, 0, 0, 0), (1, 1, 1, 1), (1, 2, 1, 3), (2, 3, 1, 2), (3, 3, 2, 2),
      (3, 5, 2, 6), (4, 5, 3, 6), (5, 4, 3, 7), (5, 7, 3, 5), (6, 6, 4, 4)] : List (ℕ × ℕ × ℕ × ℕ)),
    (7 * m + s.1 = clmul 11 m ^^^ s.2.1 ↔ 5 * m + s.2.2.1 = clmul 13 m ^^^ s.2.2.2) :=
  bisim_gen 7 11 5 13
    [(0, 0, 0, 0), (1, 1, 1, 1), (1, 2, 1, 3), (2, 3, 1, 2), (3, 3, 2, 2),
      (3, 5, 2, 6), (4, 5, 3, 6), (5, 4, 3, 7), (5, 7, 3, 5), (6, 6, 4, 4)]
    [] [(0, 1), (1, 3), (3, 7), (4, 5)] deadP deadQ (by decide) (by decide)

end G15A115770

theorem OMA.solution : type_of% @OMA.S_oeis_a115770.main := by
  intro k
  have h := G15A115770.bisim k (0, 0, 0, 0) (by decide)
  simpa using h
