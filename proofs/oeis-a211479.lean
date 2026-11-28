import OMAStatements.S_oeis_a211479

-- Problem: A211479: Number of -1..1 arrays x(i) of n+1 elements i=1..n+1 with x(i)+x(j), x(i+1)+x(j+1), -(x(i)+x(j+1)), and -(x(i+1)+x(j)) having two, three or four distinct values for every i<=n and j<=n.
-- Upstream: formal-conjectures statements/oeis-a211479.lean:0 (declaration OMA.S_oeis_a211479.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: write the entries as Fin 3 values (0, 1, 2 stand for -1, 0, 1). The four numbers of two
-- windows (p, q), (r, s) sum to 0, so they are all equal only for the windows 0,0 and 0,0 or -1,-1 and
-- 1,1 (a check of the 81 cases). Hence an array qualifies iff all its windows avoid {0 0, -1 -1} (R1)
-- or all its windows avoid {0 0, 1 1} (R2). Inclusion-exclusion gives a(n) + T3(n) = T1(n) + T2(n),
-- where Tk(n) counts the arrays whose windows satisfy Rk, and R3 = R1 and R2 (no equal neighbours).
-- Splitting off the first entry (Fin.consEquiv) gives 3-state transfer recurrences: T1 and T2 satisfy
-- T(m+2) = 2T(m+1) + T(m) with T(0) = 3, T(1) = 7, and T3(m) = 3*2^m. The closed form follows by
-- induction (1 +- sqrt 2 are the roots of x^2 - 2x - 1), and the g.f. by comparing coefficients.

namespace P1A211479

open OMA.S_oeis_a211479

/-- The test of the statement for two windows, in Fin 3 coordinates (the value of p is p - 1). -/
def G (p q r s : Fin 3) : Bool :=
  decide (nd (((p : ℕ) : ℤ) - 1) (((q : ℕ) : ℤ) - 1) (((r : ℕ) : ℤ) - 1) (((s : ℕ) : ℤ) - 1) ∈
    ({2, 3, 4} : Finset ℕ))

/-- Adjacent entries are neither both 0 nor both -1. -/
def R1 (u w : Fin 3) : Bool := decide (¬(u = 1 ∧ w = 1) ∧ ¬(u = 0 ∧ w = 0))

/-- Adjacent entries are neither both 0 nor both 1. -/
def R2 (u w : Fin 3) : Bool := decide (¬(u = 1 ∧ w = 1) ∧ ¬(u = 2 ∧ w = 2))

/-- Both conditions: adjacent entries are different. -/
def R3 (u w : Fin 3) : Bool := R1 u w && R2 u w

theorem fin1 : ∀ p q r s : Fin 3, G p q p q = true → G r s r s = true → G p q r s = true →
    R1 p q = true ∨ R2 r s = true := by
  decide +kernel

theorem fin2 : ∀ p q r s : Fin 3, R1 p q = true → R1 r s = true → G p q r s = true := by
  decide +kernel

theorem fin3 : ∀ p q r s : Fin 3, R2 p q = true → R2 r s = true → G p q r s = true := by
  decide +kernel

theorem r3pt : ∀ u w : Fin 3, R3 u w = true ↔ R1 u w = true ∧ R2 u w = true := by
  decide

theorem charac (n : ℕ) (x : Fin (n + 1) → Fin 3) :
    (∀ i j : Fin n, nd (v x i.castSucc) (v x i.succ) (v x j.castSucc) (v x j.succ) ∈
      ({2, 3, 4} : Finset ℕ)) ↔
    (∀ i : Fin n, R1 (x i.castSucc) (x i.succ) = true) ∨
      (∀ i : Fin n, R2 (x i.castSucc) (x i.succ) = true) := by
  have hG : ∀ i j : Fin n,
      (nd (v x i.castSucc) (v x i.succ) (v x j.castSucc) (v x j.succ) ∈
        ({2, 3, 4} : Finset ℕ)) ↔
        G (x i.castSucc) (x i.succ) (x j.castSucc) (x j.succ) = true :=
    fun _ _ => decide_eq_true_iff.symm
  constructor
  · intro h
    by_cases h1 : ∀ i : Fin n, R1 (x i.castSucc) (x i.succ) = true
    · exact Or.inl h1
    · right
      intro j
      obtain ⟨i, hi⟩ := not_forall.mp h1
      rcases fin1 _ _ _ _ ((hG i i).mp (h i i)) ((hG j j).mp (h j j)) ((hG i j).mp (h i j))
        with h2 | h2
      · exact absurd h2 hi
      · exact h2
  · rintro (h | h) i j
    · exact (hG i j).mpr (fin2 _ _ _ _ (h i) (h j))
    · exact (hG i j).mpr (fin3 _ _ _ _ (h i) (h j))

/-- The number of arrays of length m + 1 that start with u and whose adjacent pairs satisfy P. -/
def N (P : Fin 3 → Fin 3 → Bool) (m : ℕ) (u : Fin 3) : ℕ :=
  ∑ t : Fin m → Fin 3, if (∀ i : Fin m, P ((Fin.cons u t : Fin (m + 1) → Fin 3) i.castSucc)
    ((Fin.cons u t : Fin (m + 1) → Fin 3) i.succ) = true) then 1 else 0

theorem consSum (m : ℕ) (f : (Fin (m + 1) → Fin 3) → ℕ) :
    ∑ x : Fin (m + 1) → Fin 3, f x = ∑ u : Fin 3, ∑ t : Fin m → Fin 3, f (Fin.cons u t) := by
  have h1 := Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (m + 1) => Fin 3)).symm
    (fun x : Fin (m + 1) → Fin 3 => f x)
    (fun p : Fin 3 × (Fin m → Fin 3) => f (Fin.cons p.1 p.2))
    (fun x => congrArg f (Fin.cons_self_tail x).symm)
  exact h1.trans (Fintype.sum_prod_type _)

theorem total (P : Fin 3 → Fin 3 → Bool) (m : ℕ) :
    (∑ x : Fin (m + 1) → Fin 3,
      if (∀ i : Fin m, P (x i.castSucc) (x i.succ) = true) then (1 : ℕ) else 0) =
      ∑ u : Fin 3, N P m u :=
  consSum m (fun x => if (∀ i : Fin m, P (x i.castSucc) (x i.succ) = true) then (1 : ℕ) else 0)

theorem N0 (P : Fin 3 → Fin 3 → Bool) (u : Fin 3) : N P 0 u = 1 := by
  unfold N
  rw [Fintype.sum_unique]
  exact if_pos (fun i => Fin.elim0 i)

theorem cons0 (m : ℕ) (u : Fin 3) (t : Fin m → Fin 3) :
    (Fin.cons u t : Fin (m + 1) → Fin 3) 0 = u :=
  Fin.cons_zero (α := fun _ => Fin 3) u t

theorem consS (m : ℕ) (u : Fin 3) (t : Fin m → Fin 3) (i : Fin m) :
    (Fin.cons u t : Fin (m + 1) → Fin 3) i.succ = t i :=
  Fin.cons_succ (α := fun _ => Fin 3) u t i

theorem consWin (P : Fin 3 → Fin 3 → Bool) (m : ℕ) (u : Fin 3) (t : Fin (m + 1) → Fin 3) :
    (∀ i : Fin (m + 1), P ((Fin.cons u t : Fin (m + 1 + 1) → Fin 3) i.castSucc)
        ((Fin.cons u t : Fin (m + 1 + 1) → Fin 3) i.succ) = true) ↔
      P u (t 0) = true ∧ ∀ i : Fin m, P (t i.castSucc) (t i.succ) = true := by
  have e : ∀ i : Fin m,
      (Fin.cons u t : Fin (m + 1 + 1) → Fin 3) i.succ.castSucc = t i.castSucc :=
    fun i => (congrArg (Fin.cons u t : Fin (m + 1 + 1) → Fin 3) (Fin.succ_castSucc i).symm).trans
      (consS (m + 1) u t i.castSucc)
  rw [Fin.forall_fin_succ]
  simp only [Fin.castSucc_zero, cons0, consS, e]

theorem Nsucc (P : Fin 3 → Fin 3 → Bool) (m : ℕ) (u : Fin 3) :
    N P (m + 1) u = ∑ w : Fin 3, (if P u w = true then N P m w else 0) := by
  unfold N
  rw [consSum m]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  by_cases hw : P u w = true
  · rw [if_pos hw]
    refine Finset.sum_congr rfl (fun s _ => if_congr ?_ rfl rfl)
    rw [consWin P m u (Fin.cons w s), cons0 m w s]
    exact ⟨fun h => h.2, fun h => ⟨hw, h⟩⟩
  · rw [if_neg hw]
    refine Finset.sum_eq_zero (fun s _ => if_neg ?_)
    intro h
    rw [consWin P m u (Fin.cons w s), cons0 m w s] at h
    exact hw h.1

theorem ite3 (P : Fin 3 → Fin 3 → Bool) (m : ℕ) (u : Fin 3) :
    N P (m + 1) u = (if P u 0 = true then N P m 0 else 0) +
      (if P u 1 = true then N P m 1 else 0) + (if P u 2 = true then N P m 2 else 0) := by
  rw [Nsucc, Fin.sum_univ_three]

theorem cardP (P : Fin 3 → Fin 3 → Bool) (m : ℕ) :
    ((Finset.univ : Finset (Fin (m + 1) → Fin 3)).filter
      (fun x => ∀ i : Fin m, P (x i.castSucc) (x i.succ) = true)).card =
      N P m 0 + N P m 1 + N P m 2 := by
  rw [Finset.card_filter, total P m, Fin.sum_univ_three]

theorem rec1 (m : ℕ) :
    N R1 (m + 1) 0 + N R1 (m + 1) 1 + N R1 (m + 1) 2 =
      2 * (N R1 m 0 + N R1 m 1 + N R1 m 2) + N R1 m 2 ∧
    N R1 (m + 1) 2 = N R1 m 0 + N R1 m 1 + N R1 m 2 := by
  have h0 := ite3 R1 m 0
  have h1 := ite3 R1 m 1
  have h2 := ite3 R1 m 2
  rw [if_neg (by decide : ¬ (R1 0 0 = true)), if_pos (by decide : R1 0 1 = true),
    if_pos (by decide : R1 0 2 = true)] at h0
  rw [if_pos (by decide : R1 1 0 = true), if_neg (by decide : ¬ (R1 1 1 = true)),
    if_pos (by decide : R1 1 2 = true)] at h1
  rw [if_pos (by decide : R1 2 0 = true), if_pos (by decide : R1 2 1 = true),
    if_pos (by decide : R1 2 2 = true)] at h2
  constructor
  · omega
  · omega

theorem rec2 (m : ℕ) :
    N R2 (m + 1) 0 + N R2 (m + 1) 1 + N R2 (m + 1) 2 =
      2 * (N R2 m 0 + N R2 m 1 + N R2 m 2) + N R2 m 0 ∧
    N R2 (m + 1) 0 = N R2 m 0 + N R2 m 1 + N R2 m 2 := by
  have h0 := ite3 R2 m 0
  have h1 := ite3 R2 m 1
  have h2 := ite3 R2 m 2
  rw [if_pos (by decide : R2 0 0 = true), if_pos (by decide : R2 0 1 = true),
    if_pos (by decide : R2 0 2 = true)] at h0
  rw [if_pos (by decide : R2 1 0 = true), if_neg (by decide : ¬ (R2 1 1 = true)),
    if_pos (by decide : R2 1 2 = true)] at h1
  rw [if_pos (by decide : R2 2 0 = true), if_pos (by decide : R2 2 1 = true),
    if_neg (by decide : ¬ (R2 2 2 = true))] at h2
  constructor
  · omega
  · omega

theorem rec3 (m : ℕ) :
    N R3 (m + 1) 0 + N R3 (m + 1) 1 + N R3 (m + 1) 2 =
      2 * (N R3 m 0 + N R3 m 1 + N R3 m 2) := by
  have h0 := ite3 R3 m 0
  have h1 := ite3 R3 m 1
  have h2 := ite3 R3 m 2
  rw [if_neg (by decide : ¬ (R3 0 0 = true)), if_pos (by decide : R3 0 1 = true),
    if_pos (by decide : R3 0 2 = true)] at h0
  rw [if_pos (by decide : R3 1 0 = true), if_neg (by decide : ¬ (R3 1 1 = true)),
    if_pos (by decide : R3 1 2 = true)] at h1
  rw [if_pos (by decide : R3 2 0 = true), if_pos (by decide : R3 2 1 = true),
    if_neg (by decide : ¬ (R3 2 2 = true))] at h2
  omega

theorem ie (n : ℕ) : a n + (N R3 n 0 + N R3 n 1 + N R3 n 2) =
    (N R1 n 0 + N R1 n 1 + N R1 n 2) + (N R2 n 0 + N R2 n 1 + N R2 n 2) := by
  rw [← cardP R1 n, ← cardP R2 n, ← cardP R3 n]
  have hU : (Finset.univ : Finset (Fin (n + 1) → Fin 3)).filter (fun x => ∀ i j : Fin n,
      nd (v x i.castSucc) (v x i.succ) (v x j.castSucc) (v x j.succ) ∈
        ({2, 3, 4} : Finset ℕ)) =
      (Finset.univ : Finset (Fin (n + 1) → Fin 3)).filter
        (fun x => ∀ i : Fin n, R1 (x i.castSucc) (x i.succ) = true) ∪
      (Finset.univ : Finset (Fin (n + 1) → Fin 3)).filter
        (fun x => ∀ i : Fin n, R2 (x i.castSucc) (x i.succ) = true) := by
    ext x
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    exact charac n x
  have hI : (Finset.univ : Finset (Fin (n + 1) → Fin 3)).filter
        (fun x => ∀ i : Fin n, R1 (x i.castSucc) (x i.succ) = true) ∩
      (Finset.univ : Finset (Fin (n + 1) → Fin 3)).filter
        (fun x => ∀ i : Fin n, R2 (x i.castSucc) (x i.succ) = true) =
      (Finset.univ : Finset (Fin (n + 1) → Fin 3)).filter
        (fun x => ∀ i : Fin n, R3 (x i.castSucc) (x i.succ) = true) := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h i => (r3pt _ _).mpr ⟨h.1 i, h.2 i⟩,
      fun h => ⟨fun i => ((r3pt _ _).mp (h i)).1, fun i => ((r3pt _ _).mp (h i)).2⟩⟩
  unfold a
  rw [hU, ← hI]
  exact Finset.card_union_add_card_inter _ _

end P1A211479

open OMA.S_oeis_a211479 P1A211479 in
theorem OMA.solution : type_of% @OMA.S_oeis_a211479.main := by
  obtain ⟨A, hAd⟩ : ∃ A : ℕ → ℕ, ∀ m, a m = A m := ⟨a, fun _ => rfl⟩
  obtain ⟨T1, hT1⟩ : ∃ T : ℕ → ℕ, ∀ m, T m = N R1 m 0 + N R1 m 1 + N R1 m 2 :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨T2, hT2⟩ : ∃ T : ℕ → ℕ, ∀ m, T m = N R2 m 0 + N R2 m 1 + N R2 m 2 :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨T3, hT3⟩ : ∃ T : ℕ → ℕ, ∀ m, T m = N R3 m 0 + N R3 m 1 + N R3 m 2 :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨c1, hc1⟩ : ∃ c : ℕ → ℕ, ∀ m, c m = N R1 m 2 := ⟨_, fun _ => rfl⟩
  obtain ⟨c2, hc2⟩ : ∃ c : ℕ → ℕ, ∀ m, c m = N R2 m 0 := ⟨_, fun _ => rfl⟩
  have e1 : ∀ m, T1 (m + 1) = 2 * T1 m + c1 m ∧ c1 (m + 1) = T1 m := by
    intro m
    rw [hT1, hT1, hc1, hc1]
    exact rec1 m
  have e2 : ∀ m, T2 (m + 1) = 2 * T2 m + c2 m ∧ c2 (m + 1) = T2 m := by
    intro m
    rw [hT2, hT2, hc2, hc2]
    exact rec2 m
  have e3 : ∀ m, T3 (m + 1) = 2 * T3 m := by
    intro m
    rw [hT3, hT3]
    exact rec3 m
  have ha : ∀ m, A m + T3 m = T1 m + T2 m := by
    intro m
    rw [← hAd, hT1, hT2, hT3]
    exact ie m
  have i1 : T1 0 = 3 := by
    have h := hT1 0
    rw [N0, N0, N0] at h
    omega
  have i2 : T2 0 = 3 := by
    have h := hT2 0
    rw [N0, N0, N0] at h
    omega
  have i3 : T3 0 = 3 := by
    have h := hT3 0
    rw [N0, N0, N0] at h
    omega
  have j1 : c1 0 = 1 := by
    have h := hc1 0
    rw [N0] at h
    exact h
  have j2 : c2 0 = 1 := by
    have h := hc2 0
    rw [N0] at h
    exact h
  have p1 : ∀ m, T1 (m + 2) = 2 * T1 (m + 1) + T1 m := by
    intro m
    have h1 := (e1 (m + 1)).1
    have h2 := (e1 m).2
    rw [show m + 1 + 1 = m + 2 by omega] at h1
    omega
  have p2 : ∀ m, T2 (m + 2) = 2 * T2 (m + 1) + T2 m := by
    intro m
    have h1 := (e2 (m + 1)).1
    have h2 := (e2 m).2
    rw [show m + 1 + 1 = m + 2 by omega] at h1
    omega
  have q3 : ∀ m, T3 m = 3 * 2 ^ m := by
    intro m
    induction m with
    | zero => simp [i3]
    | succ k ih =>
      rw [e3 k, ih]
      ring
  have t10 : T1 1 = 7 := by
    have h := (e1 0).1
    rw [show (0 : ℕ) + 1 = 1 from rfl, i1, j1] at h
    omega
  have t20 : T2 1 = 7 := by
    have h := (e2 0).1
    rw [show (0 : ℕ) + 1 = 1 from rfl, i2, j2] at h
    omega
  have t12 : T1 2 = 17 := by
    have h := p1 0
    rw [show (0 : ℕ) + 2 = 2 from rfl, show (0 : ℕ) + 1 = 1 from rfl, t10, i1] at h
    omega
  have t22 : T2 2 = 17 := by
    have h := p2 0
    rw [show (0 : ℕ) + 2 = 2 from rfl, show (0 : ℕ) + 1 = 1 from rfl, t20, i2] at h
    omega
  have t13 : T1 3 = 41 := by
    have h := p1 1
    rw [show (1 : ℕ) + 2 = 3 from rfl, show (1 : ℕ) + 1 = 2 from rfl, t12, t10] at h
    omega
  have t23 : T2 3 = 41 := by
    have h := p2 1
    rw [show (1 : ℕ) + 2 = 3 from rfl, show (1 : ℕ) + 1 = 2 from rfl, t22, t20] at h
    omega
  have s1 : T3 1 = 6 := by
    have h := e3 0
    rw [show (0 : ℕ) + 1 = 1 from rfl, i3] at h
    omega
  have s2 : T3 2 = 12 := by
    have h := e3 1
    rw [show (1 : ℕ) + 1 = 2 from rfl, s1] at h
    omega
  have s3 : T3 3 = 24 := by
    have h := e3 2
    rw [show (2 : ℕ) + 1 = 3 from rfl, s2] at h
    omega
  have A1 : A 1 = 8 := by
    have h := ha 1
    rw [s1, t10, t20] at h
    omega
  have A2 : A 2 = 22 := by
    have h := ha 2
    rw [s2, t12, t22] at h
    omega
  have A3 : A 3 = 58 := by
    have h := ha 3
    rw [s3, t13, t23] at h
    omega
  refine ⟨?_, ?_⟩
  · obtain ⟨b, hb⟩ : ∃ b : ℕ → ℚ, ∀ n, b n = (A (n + 1) : ℚ) := ⟨_, fun _ => rfl⟩
    have hmk : PowerSeries.mk (fun n => (a (n + 1) : ℚ)) = PowerSeries.mk b := by
      congr 1
      funext n
      rw [hb, hAd]
    have hq : ∀ m, (A m : ℚ) = (T1 m : ℚ) + (T2 m : ℚ) - 3 * 2 ^ m := by
      intro m
      have h2 : (A m : ℚ) + (T3 m : ℚ) = (T1 m : ℚ) + (T2 m : ℚ) := by exact_mod_cast ha m
      have h3 : (T3 m : ℚ) = 3 * 2 ^ m := by exact_mod_cast q3 m
      linear_combination h2 - h3
    have pQ : ∀ m, (T1 (m + 2) : ℚ) + (T2 (m + 2) : ℚ) =
        2 * ((T1 (m + 1) : ℚ) + (T2 (m + 1) : ℚ)) + ((T1 m : ℚ) + (T2 m : ℚ)) := by
      intro m
      have h : T1 (m + 2) + T2 (m + 2) = 2 * (T1 (m + 1) + T2 (m + 1)) + (T1 m + T2 m) := by
        have h1 := p1 m
        have h2 := p2 m
        omega
      exact_mod_cast h
    have hb0 : b 0 = 8 := by
      rw [hb 0, show (0 : ℕ) + 1 = 1 from rfl]
      exact_mod_cast A1
    have hb1 : b 1 = 22 := by
      rw [hb 1, show (1 : ℕ) + 1 = 2 from rfl]
      exact_mod_cast A2
    have hb2 : b 2 = 58 := by
      rw [hb 2, show (2 : ℕ) + 1 = 3 from rfl]
      exact_mod_cast A3
    have hr3 : ∀ m, 3 ≤ m → b m - 4 * b (m - 1) + 3 * b (m - 2) + 2 * b (m - 3) = 0 := by
      intro m hm
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by omega⟩
      rw [show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega,
        show k + 3 - 3 = k by omega, hb (k + 3), hb (k + 2), hb (k + 1), hb k,
        show k + 3 + 1 = k + 4 by omega, show k + 2 + 1 = k + 3 by omega,
        show k + 1 + 1 = k + 2 by omega, hq (k + 4), hq (k + 3), hq (k + 2), hq (k + 1)]
      have q1 := pQ (k + 2)
      have q2 := pQ (k + 1)
      rw [show k + 2 + 2 = k + 4 by omega, show k + 2 + 1 = k + 3 by omega] at q1
      rw [show k + 1 + 2 = k + 3 by omega, show k + 1 + 1 = k + 2 by omega] at q2
      linear_combination q1 - 2 * q2
    have gfb : PowerSeries.mk b *
        ((1 - 2 * PowerSeries.X) * (1 - 2 * PowerSeries.X - PowerSeries.X ^ 2)) =
        2 * (4 - 5 * PowerSeries.X - 3 * PowerSeries.X ^ 2) := by
      have e : PowerSeries.mk b *
          ((1 - 2 * PowerSeries.X) * (1 - 2 * PowerSeries.X - PowerSeries.X ^ 2)) =
          PowerSeries.mk b
            - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 4 * (PowerSeries.mk b * PowerSeries.X ^ 1)
            + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 3 * (PowerSeries.mk b * PowerSeries.X ^ 2)
            + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2 *
              (PowerSeries.mk b * PowerSeries.X ^ 3) := by
        rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 4,
          map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 3,
          map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2]
        ring
      have e2 : (2 * (4 - 5 * PowerSeries.X - 3 * PowerSeries.X ^ 2) : PowerSeries ℚ) =
          (PowerSeries.C : ℚ →+* PowerSeries ℚ) 8 * PowerSeries.X ^ 0
            - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 10 * PowerSeries.X ^ 1
            - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 6 * PowerSeries.X ^ 2 := by
        rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 8,
          map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 10,
          map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 6]
        ring
      rw [e, e2]
      ext m
      simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
        PowerSeries.coeff_mk, PowerSeries.coeff_C]
      rcases Nat.lt_or_ge m 3 with hm | hm
      · interval_cases m
        · norm_num [hb0]
        · norm_num [hb0, hb1]
        · norm_num [hb0, hb1, hb2]
      · simp (disch := omega) only [if_pos, if_neg]
        linarith [hr3 m hm]
    rw [hmk]
    calc PowerSeries.X * PowerSeries.mk b *
          ((1 - 2 * PowerSeries.X) * (1 - 2 * PowerSeries.X - PowerSeries.X ^ 2))
        = PowerSeries.X * (PowerSeries.mk b *
          ((1 - 2 * PowerSeries.X) * (1 - 2 * PowerSeries.X - PowerSeries.X ^ 2))) := by
          ring
      _ = PowerSeries.X * (2 * (4 - 5 * PowerSeries.X - 3 * PowerSeries.X ^ 2)) := by
          rw [gfb]
      _ = 2 * PowerSeries.X * (4 - 5 * PowerSeries.X - 3 * PowerSeries.X ^ 2) := by
          ring
  · have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    obtain ⟨f, hf⟩ : ∃ f : ℕ → ℝ, ∀ m, f m = (3 - 2 * Real.sqrt 2) * (1 - Real.sqrt 2) ^ m +
        (3 + 2 * Real.sqrt 2) * (1 + Real.sqrt 2) ^ m := ⟨_, fun _ => rfl⟩
    have pR : ∀ m, (T1 (m + 2) : ℝ) + (T2 (m + 2) : ℝ) =
        2 * ((T1 (m + 1) : ℝ) + (T2 (m + 1) : ℝ)) + ((T1 m : ℝ) + (T2 m : ℝ)) := by
      intro m
      have h : T1 (m + 2) + T2 (m + 2) = 2 * (T1 (m + 1) + T2 (m + 1)) + (T1 m + T2 m) := by
        have h1 := p1 m
        have h2 := p2 m
        omega
      exact_mod_cast h
    have pair : ∀ m, (T1 m : ℝ) + (T2 m : ℝ) = f m ∧
        (T1 (m + 1) : ℝ) + (T2 (m + 1) : ℝ) = f (m + 1) := by
      intro m
      induction m with
      | zero =>
        show (T1 0 : ℝ) + (T2 0 : ℝ) = f 0 ∧ (T1 1 : ℝ) + (T2 1 : ℝ) = f 1
        refine ⟨?_, ?_⟩
        · rw [hf 0, i1, i2]
          push_cast
          ring
        · rw [hf 1, t10, t20]
          push_cast
          linear_combination (-4) * hsq
      | succ k ih =>
        obtain ⟨h0, h1⟩ := ih
        refine ⟨h1, ?_⟩
        have hR := pR k
        rw [show k + 1 + 1 = k + 2 by omega, hf (k + 2)]
        rw [hf k] at h0
        rw [hf (k + 1)] at h1
        linear_combination hR + 2 * h1 + h0 -
          ((3 - 2 * Real.sqrt 2) * (1 - Real.sqrt 2) ^ k +
            (3 + 2 * Real.sqrt 2) * (1 + Real.sqrt 2) ^ k) * hsq
    intro n _
    have h1 := (pair n).1
    have hc : (A n : ℝ) + (T3 n : ℝ) = (T1 n : ℝ) + (T2 n : ℝ) := by exact_mod_cast ha n
    have hc3 : (T3 n : ℝ) = 3 * 2 ^ n := by exact_mod_cast q3 n
    rw [hAd n]
    rw [hf n] at h1
    linear_combination hc - hc3 + h1
