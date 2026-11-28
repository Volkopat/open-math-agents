import OMAStatements.S_oeis_a006451

-- Problem: A006451: Numbers k such that k*(k+1)/2 + 1 is a square.
-- Upstream: formal-conjectures statements/oeis-a006451.lean:0 (declaration OMA.S_oeis_a006451.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: k(k+1)/2 + 1 = m^2 iff k(k+1) + 2 = 2m^2. The map (k, m) -> (3k+4m+1, 2k+3m+1)
-- preserves the solutions; Q lists the two orbits of (0, 1) and (2, 2) interleaved, Q(n+2) being
-- the image of Q(n), and both coordinates of Q increase. Conversely, for a solution with k >= 6
-- the inverse image (3k+1-4m, 3m-2k-1) is a solution with a smaller k, and the solutions with
-- k <= 5 are (0, 1), (2, 2), (5, 4); so by strong induction every solution is some Q(n). Hence
-- the first coordinates of Q enumerate the set in increasing order (Nat.nth_comp_of_strictMono),
-- so a(n) = Q(n).1, which satisfies a(n+4) + a(n) = 6a(n+2) + 2 with a(0..4) = 0, 2, 5, 15, 32;
-- the g.f. identity follows by comparing coefficients.

namespace R05A006451

open OMA.S_oeis_a006451

/-- The predicate of A006451. -/
abbrev P (k : ℕ) : Prop := IsSquare (k * (k + 1) / 2 + 1)

/-- The solutions (k, m) of k(k+1) + 2 = 2m^2, in increasing order. -/
def Q : ℕ → ℕ × ℕ
  | 0 => (0, 1)
  | 1 => (2, 2)
  | n + 2 => (3 * (Q n).1 + 4 * (Q n).2 + 1, 2 * (Q n).1 + 3 * (Q n).2 + 1)

theorem Qk2 (n : ℕ) : (Q (n + 2)).1 = 3 * (Q n).1 + 4 * (Q n).2 + 1 := rfl

theorem Qm2 (n : ℕ) : (Q (n + 2)).2 = 2 * (Q n).1 + 3 * (Q n).2 + 1 := rfl

theorem Q_sol_pair (n : ℕ) :
    (Q n).1 * ((Q n).1 + 1) + 2 = 2 * ((Q n).2 * (Q n).2) ∧
    (Q (n + 1)).1 * ((Q (n + 1)).1 + 1) + 2 = 2 * ((Q (n + 1)).2 * (Q (n + 1)).2) := by
  induction n with
  | zero => exact ⟨by decide, by decide⟩
  | succ n ih =>
    obtain ⟨h0, h1⟩ := ih
    refine ⟨h1, ?_⟩
    have e1 := Qk2 n
    have e2 := Qm2 n
    rw [show n + 1 + 1 = n + 2 by omega, e1, e2]
    nlinarith [h0]

theorem Q_sol (n : ℕ) : (Q n).1 * ((Q n).1 + 1) + 2 = 2 * ((Q n).2 * (Q n).2) :=
  (Q_sol_pair n).1

theorem Q_lt_pair (n : ℕ) :
    ((Q n).1 < (Q (n + 1)).1 ∧ (Q n).2 < (Q (n + 1)).2) ∧
    ((Q (n + 1)).1 < (Q (n + 2)).1 ∧ (Q (n + 1)).2 < (Q (n + 2)).2) := by
  induction n with
  | zero => exact ⟨⟨by decide, by decide⟩, by decide, by decide⟩
  | succ n ih =>
    obtain ⟨⟨h1, h2⟩, h3⟩ := ih
    refine ⟨h3, ?_⟩
    have e1 := Qk2 n
    have e2 := Qm2 n
    have e3 := Qk2 (n + 1)
    have e4 := Qm2 (n + 1)
    rw [show n + 1 + 1 = n + 2 by omega]
    constructor <;> omega

theorem Q_mono : StrictMono (fun n => (Q n).1) :=
  strictMono_nat_of_lt_succ (fun n => (Q_lt_pair n).1.1)

theorem descent (k : ℕ) : ∀ m : ℕ, k * (k + 1) + 2 = 2 * (m * m) → ∃ n, Q n = (k, m) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro m h
    rcases Nat.lt_or_ge k 6 with hk | hk
    · interval_cases k
      · have hb : m ≤ 1 := by nlinarith
        interval_cases m
        · omega
        · exact ⟨0, rfl⟩
      · have hb : m ≤ 1 := by nlinarith
        interval_cases m <;> omega
      · have hb : m ≤ 2 := by nlinarith
        interval_cases m
        · omega
        · omega
        · exact ⟨1, rfl⟩
      · have hb : m ≤ 2 := by nlinarith
        interval_cases m <;> omega
      · have hb : m ≤ 3 := by nlinarith
        interval_cases m <;> omega
      · have hb : m ≤ 4 := by nlinarith
        interval_cases m
        · omega
        · omega
        · omega
        · omega
        · exact ⟨2, rfl⟩
    · have h1 : 4 * m < 3 * k + 1 := by
        by_contra hc
        have hle : 3 * k + 1 ≤ 4 * m := by omega
        have hsq := Nat.mul_le_mul hle hle
        nlinarith [hsq, h, Nat.mul_le_mul hk (le_refl k)]
      have h2 : 2 * k + 1 ≤ 3 * m := by
        by_contra hc
        have hle : 3 * m ≤ 2 * k := by omega
        have hsq := Nat.mul_le_mul hle hle
        nlinarith [hsq, h]
      have h3 : 2 * k + 1 < 4 * m := by
        by_contra hc
        have hle : 4 * m ≤ 2 * k + 1 := by omega
        have hsq := Nat.mul_le_mul hle hle
        nlinarith [hsq, h]
      obtain ⟨k', hk'⟩ : ∃ k', 3 * k + 1 = k' + 4 * m := ⟨3 * k + 1 - 4 * m, by omega⟩
      obtain ⟨m', hm'⟩ : ∃ m', 3 * m = m' + 2 * k + 1 := ⟨3 * m - (2 * k + 1), by omega⟩
      have hlt : k' < k := by omega
      have hz : (k : ℤ) * (k + 1) + 2 = 2 * (m * m) := by exact_mod_cast h
      have z1 : (k' : ℤ) = 3 * (k : ℤ) + 1 - 4 * (m : ℤ) := by omega
      have z2 : (m' : ℤ) = 3 * (m : ℤ) - 2 * (k : ℤ) - 1 := by omega
      have hsolz : (k' : ℤ) * (k' + 1) + 2 = 2 * (m' * m') := by
        rw [z1, z2]
        linear_combination hz
      have hsol : k' * (k' + 1) + 2 = 2 * (m' * m') := by exact_mod_cast hsolz
      obtain ⟨n, hn⟩ := ih k' hlt m' hsol
      have e5 : (Q n).1 = k' := congrArg Prod.fst hn
      have e6 : (Q n).2 = m' := congrArg Prod.snd hn
      refine ⟨n + 2, Prod.ext ?_ ?_⟩
      · show (Q (n + 2)).1 = k
        rw [Qk2, e5, e6]
        omega
      · show (Q (n + 2)).2 = m
        rw [Qm2, e5, e6]
        omega

theorem hP (k : ℕ) : P k ↔ ∃ m, k * (k + 1) + 2 = 2 * (m * m) := by
  have he : k * (k + 1) % 2 = 0 := Nat.even_iff.mp (Nat.even_mul_succ_self k)
  constructor
  · rintro ⟨r, hr⟩
    exact ⟨r, by omega⟩
  · rintro ⟨r, hr⟩
    exact ⟨r, by omega⟩

theorem P_Q (n : ℕ) : P (Q n).1 := (hP _).mpr ⟨(Q n).2, Q_sol n⟩

theorem Q_range (k : ℕ) (hk : P k) : k ∈ Set.range (fun n => (Q n).1) := by
  obtain ⟨m, hm⟩ := (hP k).mp hk
  obtain ⟨n, hn⟩ := descent k m hm
  exact Set.mem_range.mpr ⟨n, congrArg Prod.fst hn⟩

theorem P_inf : (Set.ofPred P).Infinite :=
  Set.infinite_of_injective_forall_mem Q_mono.injective
    (fun n => show (Q n).1 ∈ Set.ofPred P from P_Q n)

theorem a_eq (n : ℕ) : a n = (Q n).1 := by
  have h := Nat.nth_comp_of_strictMono (p := P) (n := n) Q_mono Q_range
    (fun hfi => (P_inf hfi).elim)
  have h2 : Nat.nth (fun i => P (Q i).1) n = n := Nat.nth_of_forall (fun i _ => P_Q i)
  rw [h2] at h
  unfold a
  exact h.symm

theorem Q_rec (n : ℕ) : (Q (n + 4)).1 + (Q n).1 = 6 * (Q (n + 2)).1 + 2 := by
  have e1 := Qk2 (n + 2)
  have e2 := Qm2 n
  have e3 := Qk2 n
  rw [show n + 2 + 2 = n + 4 by omega] at e1
  omega

end R05A006451

open OMA.S_oeis_a006451 R05A006451 in
theorem OMA.solution : type_of% @OMA.S_oeis_a006451.main := by
  have rq : ∀ j : ℕ, ((Q (j + 4)).1 : ℚ) + ((Q j).1 : ℚ) = 6 * ((Q (j + 2)).1 : ℚ) + 2 := by
    intro j
    exact_mod_cast Q_rec j
  have q0 : ((Q 0).1 : ℚ) = 0 := by exact_mod_cast (show (Q 0).1 = 0 from rfl)
  have q1 : ((Q 1).1 : ℚ) = 2 := by exact_mod_cast (show (Q 1).1 = 2 from rfl)
  have q2 : ((Q 2).1 : ℚ) = 5 := by exact_mod_cast (show (Q 2).1 = 5 from rfl)
  have q3 : ((Q 3).1 : ℚ) = 15 := by exact_mod_cast (show (Q 3).1 = 15 from rfl)
  have q4 : ((Q 4).1 : ℚ) = 32 := by exact_mod_cast (show (Q 4).1 = 32 from rfl)
  obtain ⟨A, hA⟩ : ∃ A : PowerSeries ℚ, A = PowerSeries.mk (fun n => (a n : ℚ)) := ⟨_, rfl⟩
  rw [← hA]
  have cA : ∀ m, PowerSeries.coeff m A = ((Q m).1 : ℚ) := by
    intro m
    rw [hA, PowerSeries.coeff_mk, a_eq m]
  have c2 : (PowerSeries.C (2 : ℚ) : PowerSeries ℚ) = 2 := map_ofNat _ 2
  have c3 : (PowerSeries.C (3 : ℚ) : PowerSeries ℚ) = 3 := map_ofNat _ 3
  have c6 : (PowerSeries.C (6 : ℚ) : PowerSeries ℚ) = 6 := map_ofNat _ 6
  have e : A * ((PowerSeries.X - 1) * (PowerSeries.X ^ 2 + 2 * PowerSeries.X - 1) *
      (PowerSeries.X ^ 2 - 2 * PowerSeries.X - 1)) =
      A * PowerSeries.X ^ 5 - A * PowerSeries.X ^ 4 -
        PowerSeries.C (6 : ℚ) * (A * PowerSeries.X ^ 3) +
        PowerSeries.C (6 : ℚ) * (A * PowerSeries.X ^ 2) + A * PowerSeries.X ^ 1 - A := by
    rw [c6]
    ring
  have e2 : (PowerSeries.X * (-2 - 3 * PowerSeries.X + 2 * PowerSeries.X ^ 2 +
      PowerSeries.X ^ 3) : PowerSeries ℚ) =
      PowerSeries.X ^ 4 + PowerSeries.C (2 : ℚ) * PowerSeries.X ^ 3 -
        PowerSeries.C (3 : ℚ) * PowerSeries.X ^ 2 -
        PowerSeries.C (2 : ℚ) * PowerSeries.X ^ 1 := by
    rw [c2, c3]
    ring
  refine e.trans (Eq.trans ?_ e2.symm)
  ext m
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul]
  rcases Nat.lt_or_ge m 5 with hm | hm
  · interval_cases m <;> simp only [PowerSeries.coeff_mul_X_pow', cA, PowerSeries.coeff_X_pow] <;>
      norm_num [q0, q1, q2, q3, q4]
  · obtain ⟨j, rfl⟩ : ∃ j, m = j + 5 := ⟨m - 5, by omega⟩
    have t0 : PowerSeries.coeff (j + 5) A = ((Q (j + 5)).1 : ℚ) := cA (j + 5)
    have t1 : PowerSeries.coeff (j + 5) (A * PowerSeries.X ^ 1) = ((Q (j + 4)).1 : ℚ) := by
      rw [show j + 5 = j + 4 + 1 by omega, PowerSeries.coeff_mul_X_pow, cA]
    have t2 : PowerSeries.coeff (j + 5) (A * PowerSeries.X ^ 2) = ((Q (j + 3)).1 : ℚ) := by
      rw [show j + 5 = j + 3 + 2 by omega, PowerSeries.coeff_mul_X_pow, cA]
    have t3 : PowerSeries.coeff (j + 5) (A * PowerSeries.X ^ 3) = ((Q (j + 2)).1 : ℚ) := by
      rw [show j + 5 = j + 2 + 3 by omega, PowerSeries.coeff_mul_X_pow, cA]
    have t4 : PowerSeries.coeff (j + 5) (A * PowerSeries.X ^ 4) = ((Q (j + 1)).1 : ℚ) := by
      rw [show j + 5 = j + 1 + 4 by omega, PowerSeries.coeff_mul_X_pow, cA]
    have t5 : PowerSeries.coeff (j + 5) (A * PowerSeries.X ^ 5) = ((Q j).1 : ℚ) := by
      rw [PowerSeries.coeff_mul_X_pow, cA]
    have u1 : PowerSeries.coeff (j + 5) (PowerSeries.X ^ 1 : PowerSeries ℚ) = 0 := by
      rw [PowerSeries.coeff_X_pow, if_neg (show ¬(j + 5 = 1) by omega)]
    have u2 : PowerSeries.coeff (j + 5) (PowerSeries.X ^ 2 : PowerSeries ℚ) = 0 := by
      rw [PowerSeries.coeff_X_pow, if_neg (show ¬(j + 5 = 2) by omega)]
    have u3 : PowerSeries.coeff (j + 5) (PowerSeries.X ^ 3 : PowerSeries ℚ) = 0 := by
      rw [PowerSeries.coeff_X_pow, if_neg (show ¬(j + 5 = 3) by omega)]
    have u4 : PowerSeries.coeff (j + 5) (PowerSeries.X ^ 4 : PowerSeries ℚ) = 0 := by
      rw [PowerSeries.coeff_X_pow, if_neg (show ¬(j + 5 = 4) by omega)]
    rw [t0, t1, t2, t3, t4, t5, u1, u2, u3, u4]
    have r1 := rq j
    have r2 := rq (j + 1)
    rw [show j + 1 + 4 = j + 5 by omega, show j + 1 + 2 = j + 3 by omega] at r2
    linear_combination r1 - r2
