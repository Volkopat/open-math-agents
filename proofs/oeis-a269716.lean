import OMAStatements.S_oeis_a269716

-- Problem: A269716: Number of active (ON, black) cells at stage 2^n-1 of the two-dimensional cellular automaton defined by Rule 22, based on the 5-celled von Neumann neighborhood
-- Upstream: formal-conjectures statements/oeis-a269716.lean:0 (declaration OMA.S_oeis_a269716.main)
-- Credit: @therealtomgriffin-hash (the owner of the agent is credited as the solver)
--
-- Proof outline. Rule 22: a cell becomes ON iff (it is ON and has no ON neighbour) or (it is OFF and has
-- exactly one or two ON neighbours). With d = |x| + |y|, k = t - d, s = t / 2, the cell (x, y) is ON at
-- time t iff d <= t, choose s (k / 4) is odd, and
--   t even: k % 4 = 0;   t odd: k % 4 in {0, 1}, or k % 4 = 2 and the cell is off both axes.
-- This is checked by induction on t through three one-dimensional local lemmas (origin, axis,
-- off-axis), using Pascal mod 2 and the evenness of central binomial coefficients.
-- At t = 2^n - 1 every band is ON (choose (2^m - 1) q is odd, by Lucas), and the count over the
-- square reduces to elementary sums: a(n) = 2^(n-1) (3 2^n - 2) for n >= 2, a(0) = 1, a(1) = 5.

namespace A269716P
open OMA.S_oeis_a269716

def B (s m : ℕ) : Bool := Nat.bodd (s.choose m)

def C (e r : ℕ) (a : Bool) : Bool :=
  if e = 0 then r == 0 else (r == 0 || r == 1 || (r == 2 && !a))

def H (t k : ℕ) (a : Bool) : Bool := B (t / 2) (k / 4) && C (t % 2) (k % 4) a

def G (t d : ℕ) (a : Bool) : Bool := if d ≤ t then H t (t - d) a else false

def R (c : Bool) (n : ℕ) : Bool := (c && n == 0) || (!c && (n == 1 || n == 2))

lemma B_succ (s m : ℕ) : B (s + 1) (m + 1) = (B s m ^^ B s (m + 1)) := by
  simp [B, Nat.choose_succ_succ, Nat.bodd_add]

lemma B_zero (s : ℕ) : B s 0 = true := by simp [B]

lemma B_c (s q : ℕ) (h : s = 2 * q + 1) : B (s + 1) (q + 1) = false := by
  subst h
  have h2 : 2 ∣ (2 * (q + 1)).choose (q + 1) := by
    rw [← Nat.centralBinom_eq_two_mul_choose]
    exact Nat.two_dvd_centralBinom_of_one_le (by omega)
  have h3 : 2 * q + 1 + 1 = 2 * (q + 1) := by ring
  rw [B, h3]
  obtain ⟨c, hc⟩ := h2
  rw [hc, Nat.bodd_mul]
  simp

lemma C3 (e : ℕ) (a : Bool) : C e 3 a = false := by
  unfold C; split_ifs <;> rfl

lemma L1 (t d : ℕ) (hd : 1 ≤ d) (a1 a2 : Bool) :
    R (G t d false) (2 * (G t (d + 1) false).toNat + (G t (d - 1) a1).toNat + (G t (d - 1) a2).toNat)
      = G (t + 1) d false := by
  unfold G
  by_cases h0 : d ≤ t
  · have h1 : d - 1 ≤ t := by omega
    have h2 : d ≤ t + 1 := by omega
    simp only [h0, h1, h2, if_true]
    unfold H
    generalize hq0 : (t - d) / 4 = q0
    generalize hr0 : (t - d) % 4 = r0
    generalize hq2 : (t - (d - 1)) / 4 = q2
    generalize hr2 : (t - (d - 1)) % 4 = r2
    generalize hq3 : (t + 1 - d) / 4 = q3
    generalize hr3 : (t + 1 - d) % 4 = r3
    generalize hs : t / 2 = s
    generalize he : t % 2 = e
    generalize hs1 : (t + 1) / 2 = s1
    generalize he1 : (t + 1) % 2 = e1
    by_cases h3 : d + 1 ≤ t
    · simp only [h3, if_true]
      generalize hq1 : (t - (d + 1)) / 4 = q1
      generalize hr1 : (t - (d + 1)) % 4 = r1
      have he2 : e = 0 ∨ e = 1 := by omega
      have hr4 : r0 = 0 ∨ r0 = 1 ∨ r0 = 2 ∨ r0 = 3 := by omega
      rcases he2 with rfl | rfl <;> rcases hr4 with rfl | rfl | rfl | rfl
      all_goals try (exfalso; omega)
      all_goals
        try (have hh : s = s1 := (by omega); subst hh)
        try (have hh : s + 1 = s1 := (by omega); subst hh)
        try (have hh : (0:ℕ) = e1 := (by omega); subst hh)
        try (have hh : (1:ℕ) = e1 := (by omega); subst hh)
        try (have hh : q0 = q1 := (by omega); subst hh)
        try (have hh : q0 = q2 := (by omega); subst hh)
        try (have hh : q0 + 1 = q2 := (by omega); subst hh)
        try (have hh : q0 = q3 := (by omega); subst hh)
        try (have hh : q0 + 1 = q3 := (by omega); subst hh)
        try (have hh : (0:ℕ) = r1 := (by omega); subst hh)
        try (have hh : (1:ℕ) = r1 := (by omega); subst hh)
        try (have hh : (2:ℕ) = r1 := (by omega); subst hh)
        try (have hh : (3:ℕ) = r1 := (by omega); subst hh)
        try (have hh : (0:ℕ) = r2 := (by omega); subst hh)
        try (have hh : (1:ℕ) = r2 := (by omega); subst hh)
        try (have hh : (2:ℕ) = r2 := (by omega); subst hh)
        try (have hh : (3:ℕ) = r2 := (by omega); subst hh)
        try (have hh : (0:ℕ) = r3 := (by omega); subst hh)
        try (have hh : (1:ℕ) = r3 := (by omega); subst hh)
        try (have hh : (2:ℕ) = r3 := (by omega); subst hh)
        try (have hh : (3:ℕ) = r3 := (by omega); subst hh)
        try (have hh : (0:ℕ) = q0 := (by omega); subst hh)
      all_goals simp only [C, B_succ, B_zero, R]
      all_goals
        try generalize B s q0 = b0
        try generalize B s (q0 + 1) = b1
        try generalize B (s + 1) q0 = b2
        try generalize B s q1 = b3
        try generalize B s 1 = b4
        try generalize B (s + 1) 1 = b5
        try revert b0
        try revert b1
        try revert b2
        try revert b3
        try revert b4
        try revert b5
        try revert a1
        try revert a2
        decide

    · simp only [h3, if_false]
      have he2 : e = 0 ∨ e = 1 := by omega
      have hr4 : r0 = 0 ∨ r0 = 1 ∨ r0 = 2 ∨ r0 = 3 := by omega
      rcases he2 with rfl | rfl <;> rcases hr4 with rfl | rfl | rfl | rfl
      all_goals try (exfalso; omega)
      all_goals
        try (have hh : s = s1 := (by omega); subst hh)
        try (have hh : s + 1 = s1 := (by omega); subst hh)
        try (have hh : (0:ℕ) = e1 := (by omega); subst hh)
        try (have hh : (1:ℕ) = e1 := (by omega); subst hh)
        try (have hh : q0 = q1 := (by omega); subst hh)
        try (have hh : q0 = q2 := (by omega); subst hh)
        try (have hh : q0 + 1 = q2 := (by omega); subst hh)
        try (have hh : q0 = q3 := (by omega); subst hh)
        try (have hh : q0 + 1 = q3 := (by omega); subst hh)
        try (have hh : (0:ℕ) = r1 := (by omega); subst hh)
        try (have hh : (1:ℕ) = r1 := (by omega); subst hh)
        try (have hh : (2:ℕ) = r1 := (by omega); subst hh)
        try (have hh : (3:ℕ) = r1 := (by omega); subst hh)
        try (have hh : (0:ℕ) = r2 := (by omega); subst hh)
        try (have hh : (1:ℕ) = r2 := (by omega); subst hh)
        try (have hh : (2:ℕ) = r2 := (by omega); subst hh)
        try (have hh : (3:ℕ) = r2 := (by omega); subst hh)
        try (have hh : (0:ℕ) = r3 := (by omega); subst hh)
        try (have hh : (1:ℕ) = r3 := (by omega); subst hh)
        try (have hh : (2:ℕ) = r3 := (by omega); subst hh)
        try (have hh : (3:ℕ) = r3 := (by omega); subst hh)
        try (have hh : (0:ℕ) = q0 := (by omega); subst hh)
      all_goals simp only [C, B_succ, B_zero, R]
      all_goals
        try generalize B s q0 = b0
        try generalize B s (q0 + 1) = b1
        try generalize B (s + 1) q0 = b2
        try generalize B s q1 = b3
        try generalize B s 1 = b4
        try generalize B (s + 1) 1 = b5
        try revert b0
        try revert b1
        try revert b2
        try revert b3
        try revert b4
        try revert b5
        try revert a1
        try revert a2
        decide
  · have h1 : ¬ d + 1 ≤ t := by omega
    simp only [h0, h1, if_false]
    by_cases h4 : d = t + 1
    · subst h4
      have h5 : t + 1 - 1 = t := by omega
      simp only [h5, le_refl, if_true, Nat.sub_self, H, C, B_zero, R]
      split_ifs <;> simp_all [B_zero]
    · have h5 : ¬ d - 1 ≤ t := by omega
      have h6 : ¬ d ≤ t + 1 := by omega
      simp [h5, h6, R]

lemma L2 (t d : ℕ) (hd : 1 ≤ d) :
    R (G t d true) ((G t (d + 1) true).toNat + 2 * (G t (d + 1) false).toNat + (G t (d - 1) true).toNat)
      = G (t + 1) d true := by
  unfold G
  by_cases h0 : d ≤ t
  · have h1 : d - 1 ≤ t := by omega
    have h2 : d ≤ t + 1 := by omega
    simp only [h0, h1, h2, if_true]
    unfold H
    generalize hq0 : (t - d) / 4 = q0
    generalize hr0 : (t - d) % 4 = r0
    generalize hq2 : (t - (d - 1)) / 4 = q2
    generalize hr2 : (t - (d - 1)) % 4 = r2
    generalize hq3 : (t + 1 - d) / 4 = q3
    generalize hr3 : (t + 1 - d) % 4 = r3
    generalize hs : t / 2 = s
    generalize he : t % 2 = e
    generalize hs1 : (t + 1) / 2 = s1
    generalize he1 : (t + 1) % 2 = e1
    by_cases h3 : d + 1 ≤ t
    · simp only [h3, if_true]
      generalize hq1 : (t - (d + 1)) / 4 = q1
      generalize hr1 : (t - (d + 1)) % 4 = r1
      have he2 : e = 0 ∨ e = 1 := by omega
      have hr4 : r0 = 0 ∨ r0 = 1 ∨ r0 = 2 ∨ r0 = 3 := by omega
      rcases he2 with rfl | rfl <;> rcases hr4 with rfl | rfl | rfl | rfl
      all_goals try (exfalso; omega)
      all_goals
        try (have hh : s = s1 := (by omega); subst hh)
        try (have hh : s + 1 = s1 := (by omega); subst hh)
        try (have hh : (0:ℕ) = e1 := (by omega); subst hh)
        try (have hh : (1:ℕ) = e1 := (by omega); subst hh)
        try (have hh : q0 = q1 := (by omega); subst hh)
        try (have hh : q0 = q2 := (by omega); subst hh)
        try (have hh : q0 + 1 = q2 := (by omega); subst hh)
        try (have hh : q0 = q3 := (by omega); subst hh)
        try (have hh : q0 + 1 = q3 := (by omega); subst hh)
        try (have hh : (0:ℕ) = r1 := (by omega); subst hh)
        try (have hh : (1:ℕ) = r1 := (by omega); subst hh)
        try (have hh : (2:ℕ) = r1 := (by omega); subst hh)
        try (have hh : (3:ℕ) = r1 := (by omega); subst hh)
        try (have hh : (0:ℕ) = r2 := (by omega); subst hh)
        try (have hh : (1:ℕ) = r2 := (by omega); subst hh)
        try (have hh : (2:ℕ) = r2 := (by omega); subst hh)
        try (have hh : (3:ℕ) = r2 := (by omega); subst hh)
        try (have hh : (0:ℕ) = r3 := (by omega); subst hh)
        try (have hh : (1:ℕ) = r3 := (by omega); subst hh)
        try (have hh : (2:ℕ) = r3 := (by omega); subst hh)
        try (have hh : (3:ℕ) = r3 := (by omega); subst hh)
        try (have hh : (0:ℕ) = q0 := (by omega); subst hh)
      all_goals simp only [C, B_succ, B_zero, R]
      all_goals
        try generalize B s q0 = b0
        try generalize B s (q0 + 1) = b1
        try generalize B (s + 1) q0 = b2
        try generalize B s q1 = b3
        try generalize B s 1 = b4
        try generalize B (s + 1) 1 = b5
        try revert b0
        try revert b1
        try revert b2
        try revert b3
        try revert b4
        try revert b5
        try revert a1
        try revert a2
        decide

    · simp only [h3, if_false]
      have he2 : e = 0 ∨ e = 1 := by omega
      have hr4 : r0 = 0 ∨ r0 = 1 ∨ r0 = 2 ∨ r0 = 3 := by omega
      rcases he2 with rfl | rfl <;> rcases hr4 with rfl | rfl | rfl | rfl
      all_goals try (exfalso; omega)
      all_goals
        try (have hh : s = s1 := (by omega); subst hh)
        try (have hh : s + 1 = s1 := (by omega); subst hh)
        try (have hh : (0:ℕ) = e1 := (by omega); subst hh)
        try (have hh : (1:ℕ) = e1 := (by omega); subst hh)
        try (have hh : q0 = q1 := (by omega); subst hh)
        try (have hh : q0 = q2 := (by omega); subst hh)
        try (have hh : q0 + 1 = q2 := (by omega); subst hh)
        try (have hh : q0 = q3 := (by omega); subst hh)
        try (have hh : q0 + 1 = q3 := (by omega); subst hh)
        try (have hh : (0:ℕ) = r1 := (by omega); subst hh)
        try (have hh : (1:ℕ) = r1 := (by omega); subst hh)
        try (have hh : (2:ℕ) = r1 := (by omega); subst hh)
        try (have hh : (3:ℕ) = r1 := (by omega); subst hh)
        try (have hh : (0:ℕ) = r2 := (by omega); subst hh)
        try (have hh : (1:ℕ) = r2 := (by omega); subst hh)
        try (have hh : (2:ℕ) = r2 := (by omega); subst hh)
        try (have hh : (3:ℕ) = r2 := (by omega); subst hh)
        try (have hh : (0:ℕ) = r3 := (by omega); subst hh)
        try (have hh : (1:ℕ) = r3 := (by omega); subst hh)
        try (have hh : (2:ℕ) = r3 := (by omega); subst hh)
        try (have hh : (3:ℕ) = r3 := (by omega); subst hh)
        try (have hh : (0:ℕ) = q0 := (by omega); subst hh)
      all_goals simp only [C, B_succ, B_zero, R]
      all_goals
        try generalize B s q0 = b0
        try generalize B s (q0 + 1) = b1
        try generalize B (s + 1) q0 = b2
        try generalize B s q1 = b3
        try generalize B s 1 = b4
        try generalize B (s + 1) 1 = b5
        try revert b0
        try revert b1
        try revert b2
        try revert b3
        try revert b4
        try revert b5
        try revert a1
        try revert a2
        decide
  · have h1 : ¬ d + 1 ≤ t := by omega
    simp only [h0, h1, if_false]
    by_cases h4 : d = t + 1
    · subst h4
      have h5 : t + 1 - 1 = t := by omega
      simp only [h5, le_refl, if_true, Nat.sub_self, H, C, B_zero, R]
      split_ifs <;> simp_all [B_zero]
    · have h5 : ¬ d - 1 ≤ t := by omega
      have h6 : ¬ d ≤ t + 1 := by omega
      simp [h5, h6, R]


lemma L0 (t : ℕ) :
    R (G t 0 true) (4 * (G t 1 true).toNat) = G (t + 1) 0 true := by
  unfold G
  simp only [Nat.zero_le, if_true, Nat.sub_zero]
  unfold H
  generalize hq0 : t / 4 = q0
  generalize hr0 : t % 4 = r0
  generalize hq3 : (t + 1) / 4 = q3
  generalize hr3 : (t + 1) % 4 = r3
  generalize hs : t / 2 = s
  generalize he : t % 2 = e
  generalize hs1 : (t + 1) / 2 = s1
  generalize he1 : (t + 1) % 2 = e1
  by_cases h3 : 1 ≤ t
  · simp only [h3, if_true]
    generalize hq1 : (t - 1) / 4 = q1
    generalize hr1 : (t - 1) % 4 = r1
    have he2 : e = 0 ∨ e = 1 := by omega
    have hr4 : r0 = 0 ∨ r0 = 1 ∨ r0 = 2 ∨ r0 = 3 := by omega
    rcases he2 with rfl | rfl <;> rcases hr4 with rfl | rfl | rfl | rfl
    all_goals try (exfalso; omega)
    all_goals
      try (have hh : s = s1 := (by omega); subst hh)
      try (have hh : s + 1 = s1 := (by omega); subst hh)
      try (have hh : (0:ℕ) = e1 := (by omega); subst hh)
      try (have hh : (1:ℕ) = e1 := (by omega); subst hh)
      try (have hh : q0 = q1 := (by omega); subst hh)
      try (have hh : q0 = q2 := (by omega); subst hh)
      try (have hh : q0 + 1 = q2 := (by omega); subst hh)
      try (have hh : q0 = q3 := (by omega); subst hh)
      try (have hh : q0 + 1 = q3 := (by omega); subst hh)
      try (have hh : (0:ℕ) = r1 := (by omega); subst hh)
      try (have hh : (1:ℕ) = r1 := (by omega); subst hh)
      try (have hh : (2:ℕ) = r1 := (by omega); subst hh)
      try (have hh : (3:ℕ) = r1 := (by omega); subst hh)
      try (have hh : (0:ℕ) = r2 := (by omega); subst hh)
      try (have hh : (1:ℕ) = r2 := (by omega); subst hh)
      try (have hh : (2:ℕ) = r2 := (by omega); subst hh)
      try (have hh : (3:ℕ) = r2 := (by omega); subst hh)
      try (have hh : (0:ℕ) = r3 := (by omega); subst hh)
      try (have hh : (1:ℕ) = r3 := (by omega); subst hh)
      try (have hh : (2:ℕ) = r3 := (by omega); subst hh)
      try (have hh : (3:ℕ) = r3 := (by omega); subst hh)
      try (have hh : (0:ℕ) = q0 := (by omega); subst hh)
    all_goals try (have hc := B_c s q0 (by omega); rw [hc])
    all_goals simp only [C, B_succ, B_zero, R]
    all_goals
      try generalize B s q0 = b0
      try generalize B s (q0 + 1) = b1
      try generalize B (s + 1) q0 = b2
      try generalize B s q1 = b3
      try generalize B s 1 = b4
      try generalize B (s + 1) 1 = b5
      try revert b0
      try revert b1
      try revert b2
      try revert b3
      try revert b4
      try revert b5
      try revert a1
      try revert a2
      decide
  · simp only [h3, if_false]
    have he2 : e = 0 ∨ e = 1 := by omega
    have hr4 : r0 = 0 ∨ r0 = 1 ∨ r0 = 2 ∨ r0 = 3 := by omega
    rcases he2 with rfl | rfl <;> rcases hr4 with rfl | rfl | rfl | rfl
    all_goals try (exfalso; omega)
    all_goals
      try (have hh : s = s1 := (by omega); subst hh)
      try (have hh : s + 1 = s1 := (by omega); subst hh)
      try (have hh : (0:ℕ) = e1 := (by omega); subst hh)
      try (have hh : (1:ℕ) = e1 := (by omega); subst hh)
      try (have hh : q0 = q1 := (by omega); subst hh)
      try (have hh : q0 = q2 := (by omega); subst hh)
      try (have hh : q0 + 1 = q2 := (by omega); subst hh)
      try (have hh : q0 = q3 := (by omega); subst hh)
      try (have hh : q0 + 1 = q3 := (by omega); subst hh)
      try (have hh : (0:ℕ) = r1 := (by omega); subst hh)
      try (have hh : (1:ℕ) = r1 := (by omega); subst hh)
      try (have hh : (2:ℕ) = r1 := (by omega); subst hh)
      try (have hh : (3:ℕ) = r1 := (by omega); subst hh)
      try (have hh : (0:ℕ) = r2 := (by omega); subst hh)
      try (have hh : (1:ℕ) = r2 := (by omega); subst hh)
      try (have hh : (2:ℕ) = r2 := (by omega); subst hh)
      try (have hh : (3:ℕ) = r2 := (by omega); subst hh)
      try (have hh : (0:ℕ) = r3 := (by omega); subst hh)
      try (have hh : (1:ℕ) = r3 := (by omega); subst hh)
      try (have hh : (2:ℕ) = r3 := (by omega); subst hh)
      try (have hh : (3:ℕ) = r3 := (by omega); subst hh)
      try (have hh : (0:ℕ) = q0 := (by omega); subst hh)
    all_goals try (have hc := B_c s q0 (by omega); rw [hc])
    all_goals simp only [C, B_succ, B_zero, R]
    all_goals
      try generalize B s q0 = b0
      try generalize B s (q0 + 1) = b1
      try generalize B (s + 1) q0 = b2
      try generalize B s q1 = b3
      try generalize B s 1 = b4
      try generalize B (s + 1) 1 = b5
      try revert b0
      try revert b1
      try revert b2
      try revert b3
      try revert b4
      try revert b5
      try revert a1
      try revert a2
      decide


lemma rule22 (c : Bool) (n : ℕ) (h : n ≤ 4) : Nat.testBit 22 (c.toNat + 2 * n) = R c n := by
  interval_cases n <;> cases c <;> decide

lemma toNat_le (b : Bool) : b.toNat ≤ 1 := by cases b <;> decide

theorem char (t : ℕ) : ∀ x y : ℤ, cell 22 t x y = G t (x.natAbs + y.natAbs) (x == 0 || y == 0) := by
  induction t with
  | zero =>
    intro x y
    simp only [cell, G, H, C]
    by_cases h : x = 0 ∧ y = 0
    · obtain ⟨rfl, rfl⟩ := h
      decide
    · have h' : ¬ (x.natAbs + y.natAbs ≤ 0) := by omega
      simp [h, h']
  | succ t ih =>
    intro x y
    rw [cell]
    simp only [ih]
    rw [rule22 _ _ (by
      have := toNat_le (G t ((x + 1).natAbs + y.natAbs) (x + 1 == 0 || y == 0))
      have := toNat_le (G t ((x - 1).natAbs + y.natAbs) (x - 1 == 0 || y == 0))
      have := toNat_le (G t (x.natAbs + (y + 1).natAbs) (x == 0 || y + 1 == 0))
      have := toNat_le (G t (x.natAbs + (y - 1).natAbs) (x == 0 || y - 1 == 0))
      omega)]
    rcases lt_trichotomy x 0 with hx | hx | hx <;> rcases lt_trichotomy y 0 with hy | hy | hy
    · -- x < 0, y < 0
      have e1 : (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs - 1 := by omega
      have e2 : (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 := by omega
      have e3 : x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs - 1 := by omega
      have e4 : x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs + 1 := by omega
      have f2 : (x - 1 == 0 || y == 0) = false := by simp; omega
      have f4 : (x == 0 || y - 1 == 0) = false := by simp; omega
      have fA : (x == 0 || y == 0) = false := by simp; omega
      rw [e1, e2, e3, e4, f2, f4, fA]
      rw [← L1 t _ (by omega) (x + 1 == 0 || y == 0) (x == 0 || y + 1 == 0)]
      congr 1; omega
    · -- x < 0, y = 0
      subst hy
      have e1 : (x + 1).natAbs + (0:ℤ).natAbs = x.natAbs + (0:ℤ).natAbs - 1 := by omega
      have e2 : (x - 1).natAbs + (0:ℤ).natAbs = x.natAbs + (0:ℤ).natAbs + 1 := by omega
      have e3 : x.natAbs + ((0:ℤ) + 1).natAbs = x.natAbs + (0:ℤ).natAbs + 1 := by omega
      have e4 : x.natAbs + ((0:ℤ) - 1).natAbs = x.natAbs + (0:ℤ).natAbs + 1 := by omega
      have f1 : (x + 1 == 0 || (0:ℤ) == 0) = true := by simp
      have f2 : (x - 1 == 0 || (0:ℤ) == 0) = true := by simp
      have f3 : (x == 0 || (0:ℤ) + 1 == 0) = false := by simp; omega
      have f4 : (x == 0 || (0:ℤ) - 1 == 0) = false := by simp; omega
      have fA : (x == 0 || (0:ℤ) == 0) = true := by simp
      rw [e1, e2, e3, e4, f1, f2, f3, f4, fA]
      rw [← L2 t _ (by omega)]
      congr 1; omega
    · -- x < 0, y > 0
      have e1 : (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs - 1 := by omega
      have e2 : (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 := by omega
      have e3 : x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs + 1 := by omega
      have e4 : x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs - 1 := by omega
      have f2 : (x - 1 == 0 || y == 0) = false := by simp; omega
      have f3 : (x == 0 || y + 1 == 0) = false := by simp; omega
      have fA : (x == 0 || y == 0) = false := by simp; omega
      rw [e1, e2, e3, e4, f2, f3, fA]
      rw [← L1 t _ (by omega) (x + 1 == 0 || y == 0) (x == 0 || y - 1 == 0)]
      congr 1; omega
    · -- x = 0, y < 0
      subst hx
      have e1 : ((0:ℤ) + 1).natAbs + y.natAbs = (0:ℤ).natAbs + y.natAbs + 1 := by omega
      have e2 : ((0:ℤ) - 1).natAbs + y.natAbs = (0:ℤ).natAbs + y.natAbs + 1 := by omega
      have e3 : (0:ℤ).natAbs + (y + 1).natAbs = (0:ℤ).natAbs + y.natAbs - 1 := by omega
      have e4 : (0:ℤ).natAbs + (y - 1).natAbs = (0:ℤ).natAbs + y.natAbs + 1 := by omega
      have f1 : ((0:ℤ) + 1 == 0 || y == 0) = false := by simp; omega
      have f2 : ((0:ℤ) - 1 == 0 || y == 0) = false := by simp; omega
      have f3 : ((0:ℤ) == 0 || y + 1 == 0) = true := by simp
      have f4 : ((0:ℤ) == 0 || y - 1 == 0) = true := by simp
      have fA : ((0:ℤ) == 0 || y == 0) = true := by simp
      rw [e1, e2, e3, e4, f1, f2, f3, f4, fA]
      rw [← L2 t _ (by omega)]
      congr 1; omega
    · -- x = 0, y = 0
      subst hx; subst hy
      have a1 : Int.natAbs 0 + Int.natAbs 0 = 0 := by decide
      have a2 : ((0:ℤ) + 1).natAbs + Int.natAbs 0 = 1 := by decide
      have a3 : ((0:ℤ) - 1).natAbs + Int.natAbs 0 = 1 := by decide
      have a4 : Int.natAbs 0 + ((0:ℤ) + 1).natAbs = 1 := by decide
      have a5 : Int.natAbs 0 + ((0:ℤ) - 1).natAbs = 1 := by decide
      have b1 : ((0:ℤ) == 0 || (0:ℤ) == 0) = true := by decide
      have b2 : ((0:ℤ) + 1 == 0 || (0:ℤ) == 0) = true := by decide
      have b3 : ((0:ℤ) - 1 == 0 || (0:ℤ) == 0) = true := by decide
      have b4 : ((0:ℤ) == 0 || (0:ℤ) + 1 == 0) = true := by decide
      have b5 : ((0:ℤ) == 0 || (0:ℤ) - 1 == 0) = true := by decide
      rw [a1, a2, a3, a4, a5, b1, b2, b3, b4, b5, ← L0 t]
      congr 1; omega
    · -- x = 0, y > 0
      subst hx
      have e1 : ((0:ℤ) + 1).natAbs + y.natAbs = (0:ℤ).natAbs + y.natAbs + 1 := by omega
      have e2 : ((0:ℤ) - 1).natAbs + y.natAbs = (0:ℤ).natAbs + y.natAbs + 1 := by omega
      have e3 : (0:ℤ).natAbs + (y + 1).natAbs = (0:ℤ).natAbs + y.natAbs + 1 := by omega
      have e4 : (0:ℤ).natAbs + (y - 1).natAbs = (0:ℤ).natAbs + y.natAbs - 1 := by omega
      have f1 : ((0:ℤ) + 1 == 0 || y == 0) = false := by simp; omega
      have f2 : ((0:ℤ) - 1 == 0 || y == 0) = false := by simp; omega
      have f3 : ((0:ℤ) == 0 || y + 1 == 0) = true := by simp
      have f4 : ((0:ℤ) == 0 || y - 1 == 0) = true := by simp
      have fA : ((0:ℤ) == 0 || y == 0) = true := by simp
      rw [e1, e2, e3, e4, f1, f2, f3, f4, fA]
      rw [← L2 t _ (by omega)]
      congr 1; omega
    · -- x > 0, y < 0
      have e1 : (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 := by omega
      have e2 : (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs - 1 := by omega
      have e3 : x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs - 1 := by omega
      have e4 : x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs + 1 := by omega
      have f1 : (x + 1 == 0 || y == 0) = false := by simp; omega
      have f4 : (x == 0 || y - 1 == 0) = false := by simp; omega
      have fA : (x == 0 || y == 0) = false := by simp; omega
      rw [e1, e2, e3, e4, f1, f4, fA]
      rw [← L1 t _ (by omega) (x - 1 == 0 || y == 0) (x == 0 || y + 1 == 0)]
      congr 1; omega
    · -- x > 0, y = 0
      subst hy
      have e1 : (x + 1).natAbs + (0:ℤ).natAbs = x.natAbs + (0:ℤ).natAbs + 1 := by omega
      have e2 : (x - 1).natAbs + (0:ℤ).natAbs = x.natAbs + (0:ℤ).natAbs - 1 := by omega
      have e3 : x.natAbs + ((0:ℤ) + 1).natAbs = x.natAbs + (0:ℤ).natAbs + 1 := by omega
      have e4 : x.natAbs + ((0:ℤ) - 1).natAbs = x.natAbs + (0:ℤ).natAbs + 1 := by omega
      have f1 : (x + 1 == 0 || (0:ℤ) == 0) = true := by simp
      have f2 : (x - 1 == 0 || (0:ℤ) == 0) = true := by simp
      have f3 : (x == 0 || (0:ℤ) + 1 == 0) = false := by simp; omega
      have f4 : (x == 0 || (0:ℤ) - 1 == 0) = false := by simp; omega
      have fA : (x == 0 || (0:ℤ) == 0) = true := by simp
      rw [e1, e2, e3, e4, f1, f2, f3, f4, fA]
      rw [← L2 t _ (by omega)]
      congr 1; omega
    · -- x > 0, y > 0
      have e1 : (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 := by omega
      have e2 : (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs - 1 := by omega
      have e3 : x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs + 1 := by omega
      have e4 : x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs - 1 := by omega
      have f1 : (x + 1 == 0 || y == 0) = false := by simp; omega
      have f3 : (x == 0 || y + 1 == 0) = false := by simp; omega
      have fA : (x == 0 || y == 0) = false := by simp; omega
      rw [e1, e2, e3, e4, f1, f3, fA]
      rw [← L1 t _ (by omega) (x - 1 == 0 || y == 0) (x == 0 || y - 1 == 0)]
      congr 1; omega

lemma bodd_of_mod (n : ℕ) (h : n % 2 = 1) : Nat.bodd n = true := by
  have := Nat.mod_two_of_bodd n
  cases hb : Nat.bodd n <;> simp_all

lemma Bfull (m : ℕ) : ∀ q, q ≤ 2 ^ m - 1 → B (2 ^ m - 1) q = true := by
  induction m with
  | zero => intro q hq; simp at hq; subst hq; simp [B]
  | succ m ih =>
    intro q hq
    have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have key := @Choose.choose_modEq_choose_mod_mul_choose_div_nat (2 ^ (m+1) - 1) q 2 hp
    have h1 : (2 ^ (m+1) - 1) % 2 = 1 := by
      have : 2 ^ (m+1) = 2 * 2 ^ m := by ring
      have : 0 < 2 ^ m := by positivity
      omega
    have h2 : (2 ^ (m+1) - 1) / 2 = 2 ^ m - 1 := by
      have : 2 ^ (m+1) = 2 * 2 ^ m := by ring
      have : 0 < 2 ^ m := by positivity
      omega
    have h3 : q / 2 ≤ 2 ^ m - 1 := by
      have : 2 ^ (m+1) = 2 * 2 ^ m := by ring
      omega
    have h4 : (1 : ℕ).choose (q % 2) = 1 := by
      have : q % 2 = 0 ∨ q % 2 = 1 := by omega
      rcases this with h | h <;> rw [h] <;> rfl
    rw [h1, h2, h4, one_mul] at key
    have ih' := ih (q / 2) h3
    unfold B at ih' ⊢
    apply bodd_of_mod
    unfold Nat.ModEq at key
    rw [key]
    have := Nat.mod_two_of_bodd ((2 ^ m - 1).choose (q / 2))
    rw [ih'] at this
    simpa using this

lemma fold (h : ℕ → ℕ) (T : ℕ) :
    ∑ i ∈ Finset.range (2 * T + 1), h (((i : ℤ) - T).natAbs) = h 0 + 2 * ∑ u ∈ Finset.range T, h (u + 1) := by
  rw [show 2 * T + 1 = T + (T + 1) by ring, Finset.sum_range_add]
  have e1 : ∑ i ∈ Finset.range T, h (((i : ℤ) - T).natAbs) = ∑ i ∈ Finset.range T, (fun u => h (u + 1)) (T - 1 - i) := by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Finset.mem_range] at hi
    congr 1; omega
  have e2 : ∑ x ∈ Finset.range (T + 1), h ((((T + x : ℕ) : ℤ) - T).natAbs) = ∑ x ∈ Finset.range (T + 1), h x := by
    apply Finset.sum_congr rfl
    intro i hi
    congr 1; omega
  rw [e1, Finset.sum_range_reflect (fun u => h (u + 1)) T, e2, Finset.sum_range_succ']
  ring

lemma cntA (N : ℕ) : ∑ w ∈ Finset.range N, (if w % 4 < 2 then 1 else 0) = 2 * (N / 4) + min (N % 4) 2 := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih]; split_ifs <;> omega

lemma cntI (L N : ℕ) : ∑ v ∈ Finset.range N, (if v < L ∧ (L - 1 - v) % 4 ≠ 3 then 1 else 0)
    = min N L - (L / 4 - (L - min N L) / 4) := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih]; split_ifs <;> omega

lemma cntJ (M : ℕ) : ∑ w ∈ Finset.range (4 * M + 3), (w - w / 4) = (M + 1) * (6 * M + 3) := by
  induction M with
  | zero => decide
  | succ M ih =>
    rw [show 4 * (M + 1) + 3 = 4 * M + 3 + 1 + 1 + 1 + 1 by ring]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, ih]
    have a1 : 4 * M + 3 - (4 * M + 3) / 4 = 3 * M + 3 := by omega
    have a2 : 4 * M + 3 + 1 - (4 * M + 3 + 1) / 4 = 3 * M + 3 := by omega
    have a3 : 4 * M + 3 + 1 + 1 - (4 * M + 3 + 1 + 1) / 4 = 3 * M + 4 := by omega
    have a4 : 4 * M + 3 + 1 + 1 + 1 - (4 * M + 3 + 1 + 1 + 1) / 4 = 3 * M + 5 := by omega
    rw [a1, a2, a3, a4]
    ring


lemma flag (z : ℤ) : (z == 0) = (z.natAbs == 0) := by
  by_cases h : z = 0
  · subst h; rfl
  · have h' : z.natAbs ≠ 0 := by omega
    simp [h, h']

def g (T u v : ℕ) : ℕ := if G T (u + v) (u == 0 || v == 0) then 1 else 0

lemma onCount_eq (T : ℕ) : onCount 22 T =
    (g T 0 0 + 2 * ∑ v ∈ Finset.range T, g T 0 (v + 1)) +
      2 * ∑ u ∈ Finset.range T, (g T (u + 1) 0 + 2 * ∑ v ∈ Finset.range T, g T (u + 1) (v + 1)) := by
  unfold onCount
  have h1 : ∀ i j : ℕ, (if cell 22 T ((i : ℤ) - T) ((j : ℤ) - T) then 1 else 0)
      = g T (((i : ℤ) - T).natAbs) (((j : ℤ) - T).natAbs) := by
    intro i j
    rw [char, flag, flag]
    rfl
  simp only [h1]
  have h2 : ∀ i : ℕ, ∑ j ∈ Finset.range (2 * T + 1), g T (((i : ℤ) - T).natAbs) (((j : ℤ) - T).natAbs)
      = g T (((i : ℤ) - T).natAbs) 0 + 2 * ∑ v ∈ Finset.range T, g T (((i : ℤ) - T).natAbs) (v + 1) :=
    fun i => fold (fun v => g T (((i : ℤ) - T).natAbs) v) T
  simp only [h2]
  exact fold (fun u => g T u 0 + 2 * ∑ v ∈ Finset.range T, g T u (v + 1)) T

lemma G_T (M d : ℕ) (a : Bool) (hf : ∀ q, q ≤ 2 * M + 1 → B (2 * M + 1) q = true) :
    G (4 * M + 3) d a = (decide (d ≤ 4 * M + 3) && C 1 ((4 * M + 3 - d) % 4) a) := by
  unfold G H
  by_cases hd : d ≤ 4 * M + 3
  · have e1 : (4 * M + 3) / 2 = 2 * M + 1 := by omega
    have e2 : (4 * M + 3) % 2 = 1 := by omega
    rw [if_pos hd, e1, e2, hf _ (by omega)]
    simp [hd]
  · rw [if_neg hd]
    simp [hd]

lemma count (M : ℕ) (hf : ∀ q, q ≤ 2 * M + 1 → B (2 * M + 1) q = true) :
    onCount 22 (4 * M + 3) = (M + 1) * (24 * M + 20) := by
  rw [onCount_eq]
  have g00 : g (4 * M + 3) 0 0 = 0 := by
    unfold g; rw [G_T M _ _ hf]
    have : (4 * M + 3 - (0 + 0)) % 4 = 3 := by omega
    rw [this]; simp [C]
  have gA : ∀ v ∈ Finset.range (4 * M + 3), g (4 * M + 3) 0 (v + 1)
      = (fun w => if w % 4 < 2 then 1 else 0) (4 * M + 3 - 1 - v) := by
    intro v hv
    simp only [Finset.mem_range] at hv
    unfold g; rw [G_T M _ _ hf]
    have e : 4 * M + 3 - (0 + (v + 1)) = 4 * M + 3 - 1 - v := by omega
    rw [e]
    have hle : 0 + (v + 1) ≤ 4 * M + 3 := by omega
    simp only [hle, decide_true, Bool.true_and, C, beq_self_eq_true, Bool.true_or, Bool.not_true,
      Bool.and_false, Bool.or_false]
    split_ifs <;> simp_all <;> omega
  have gA' : ∀ u ∈ Finset.range (4 * M + 3), g (4 * M + 3) (u + 1) 0 = g (4 * M + 3) 0 (u + 1) := by
    intro u _
    unfold g
    rw [Nat.add_zero, Nat.zero_add, Bool.or_comm]
  have gI : ∀ u ∈ Finset.range (4 * M + 3), ∀ v ∈ Finset.range (4 * M + 3), g (4 * M + 3) (u + 1) (v + 1)
      = if v < (4 * M + 3 - 1 - u) ∧ ((4 * M + 3 - 1 - u) - 1 - v) % 4 ≠ 3 then 1 else 0 := by
    intro u _ v _
    unfold g; rw [G_T M _ _ hf]
    have f : ((u + 1 == 0) || (v + 1 == 0)) = false := by simp
    rw [f]
    simp only [C, Bool.not_false, Bool.and_true]
    by_cases h : u + 1 + (v + 1) ≤ 4 * M + 3
    · have e : 4 * M + 3 - (u + 1 + (v + 1)) = (4 * M + 3 - 1 - u) - 1 - v := by omega
      rw [e]
      simp only [h, decide_true, Bool.true_and]
      split_ifs <;> simp_all <;> omega
    · simp [h]
      omega
  have sA : ∑ v ∈ Finset.range (4 * M + 3), g (4 * M + 3) 0 (v + 1) = 2 * M + 2 := by
    rw [Finset.sum_congr rfl gA, Finset.sum_range_reflect (fun w => if w % 4 < 2 then 1 else 0) (4 * M + 3), cntA]
    omega
  have sI : ∀ u ∈ Finset.range (4 * M + 3), ∑ v ∈ Finset.range (4 * M + 3), g (4 * M + 3) (u + 1) (v + 1)
      = (fun w => w - w / 4) (4 * M + 3 - 1 - u) := by
    intro u hu
    rw [Finset.sum_congr rfl (gI u hu), cntI]
    simp only
    have : min (4 * M + 3) (4 * M + 3 - 1 - u) = 4 * M + 3 - 1 - u := by omega
    rw [this, Nat.sub_self]
    simp
  rw [g00, sA]
  have hsplit : ∑ u ∈ Finset.range (4 * M + 3), (g (4 * M + 3) (u + 1) 0 + 2 * ∑ v ∈ Finset.range (4 * M + 3), g (4 * M + 3) (u + 1) (v + 1))
      = ∑ u ∈ Finset.range (4 * M + 3), g (4 * M + 3) 0 (u + 1) + 2 * ∑ u ∈ Finset.range (4 * M + 3), (fun w => w - w / 4) (4 * M + 3 - 1 - u) := by
    rw [Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl gA'
    · exact Finset.sum_congr rfl (fun u hu => by rw [sI u hu])
  rw [hsplit, sA, Finset.sum_range_reflect (fun w => w - w / 4) (4 * M + 3), cntJ]
  ring


lemma a_closed (n : ℕ) (hn : 2 ≤ n) : (a n : ℚ) = (2 : ℚ) ^ (n - 1) * (3 * (2 : ℚ) ^ n - 2) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  have hP : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have h4 : 2 ^ (k + 2) = 4 * 2 ^ k := by ring
  have hT : 2 ^ (k + 2) - 1 = 4 * (2 ^ k - 1) + 3 := by omega
  have hf : ∀ q, q ≤ 2 * (2 ^ k - 1) + 1 → B (2 * (2 ^ k - 1) + 1) q = true := by
    intro q hq
    have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    have : 2 * (2 ^ k - 1) + 1 = 2 ^ (k + 1) - 1 := by omega
    rw [this] at hq ⊢
    exact Bfull (k + 1) q hq
  unfold a
  rw [hT, count (2 ^ k - 1) hf]
  have hk1 : k + 2 - 1 = k + 1 := by omega
  rw [hk1]
  have hMc : ((2 ^ k - 1 : ℕ) : ℚ) = (2 : ℚ) ^ k - 1 := by
    rw [Nat.cast_sub hP]
    push_cast
    ring
  push_cast
  rw [hMc]
  ring

lemma part1 : ∀ n : ℕ, 2 ≤ n → (a n : ℚ) = (2 : ℚ) ^ (n - 1) * (3 * (2 : ℚ) ^ n - 2) := a_closed

lemma part2 : ∀ n : ℕ, 4 ≤ n → (a n : ℚ) = 6 * a (n - 1) - 8 * a (n - 2) := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  rw [a_closed _ (by omega), a_closed _ (by omega), a_closed _ (by omega)]
  have e1 : k + 4 - 1 = k + 3 := by omega
  have e2 : k + 3 - 1 = k + 2 := by omega
  have e3 : k + 4 - 2 - 1 = k + 1 := by omega
  have e4 : k + 4 - 2 = k + 2 := by omega
  have e5 : k + 2 - 1 = k + 1 := by omega
  simp only [e1, e2, e3, e4, e5]
  ring

lemma a0 : a 0 = 1 := by
  unfold a
  have : onCount 22 (2 ^ 0 - 1) = 1 := by decide
  rw [this]; rfl

lemma a1 : a 1 = 5 := by
  unfold a
  have : onCount 22 (2 ^ 1 - 1) = 5 := by decide
  rw [this]; rfl

open PowerSeries in
lemma part3 : (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - 2 * X) * (1 - 4 * X) : PowerSeries ℚ)
    = (1 + 2 * X) * (1 - 3 * X + 4 * X ^ 2)) := by
  have hL : (PowerSeries.mk (fun n => (a n : ℚ)) * ((1 - 2 * X) * (1 - 4 * X) : PowerSeries ℚ))
      = PowerSeries.mk (fun n => (a n : ℚ)) - (6 : ℚ) • (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 1)
        + (8 : ℚ) • (PowerSeries.mk (fun n => (a n : ℚ)) * X ^ 2) := by
    rw [smul_eq_C_mul, smul_eq_C_mul]
    simp only [map_ofNat]
    ring
  have hR : ((1 + 2 * X) * (1 - 3 * X + 4 * X ^ 2) : PowerSeries ℚ)
      = 1 - X ^ 1 - (2 : ℚ) • X ^ 2 + (8 : ℚ) • X ^ 3 := by
    rw [smul_eq_C_mul, smul_eq_C_mul]
    simp only [map_ofNat]
    ring
  rw [hL, hR]
  ext n
  simp only [map_add, map_sub, map_smul, coeff_mul_X_pow', coeff_mk, coeff_X_pow, coeff_one, smul_eq_mul]
  have v0 : (a 0 : ℚ) = 1 := by rw [a0]; norm_num
  have v1 : (a 1 : ℚ) = 5 := by rw [a1]; norm_num
  have v2 : (a 2 : ℚ) = 20 := by rw [a_closed 2 (by norm_num)]; norm_num
  have v3 : (a 3 : ℚ) = 88 := by rw [a_closed 3 (by norm_num)]; norm_num
  rcases n with _ | _ | _ | _ | n
  · simp [v0]
  · simp [v0, v1]; norm_num
  · simp [v0, v1, v2]; norm_num
  · simp [v1, v2, v3]; norm_num
  · have h := part2 (n + 4) (by omega)
    have e1 : n + 4 - 1 = n + 1 + 1 + 1 := by omega
    have e2 : n + 4 - 2 = n + 1 + 1 := by omega
    rw [e1, e2] at h
    simp
    have e3 : n + 1 + 1 + 1 + 1 - 1 = n + 1 + 1 + 1 := by omega
    have e4 : n + 1 + 1 + 1 + 1 - 2 = n + 1 + 1 := by omega
    simp only [e3, e4] at *
    linarith

end A269716P

theorem OMA.solution : type_of% @OMA.S_oeis_a269716.main := by
  exact ⟨A269716P.part1, A269716P.part2, A269716P.part3⟩
