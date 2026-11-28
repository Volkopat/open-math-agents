import OMAStatements.S_oeis_a211476

-- Problem: A211476: Number of -1..1 arrays x(i) of n+1 elements i=1..n+1 with x(i)+x(j), x(i+1)+x(j+1), -(x(i)+x(j+1)), and -(x(i+1)+x(j)) having one or three distinct values for every i<=n and j<=n.
-- Upstream: formal-conjectures statements/oeis-a211476.lean:0 (declaration OMA.S_oeis_a211476.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: write the entries as Fin 3 values (0, 1, 2 stand for -1, 0, 1). A check of the 81
-- pairs of windows shows that an array qualifies iff all its windows have different entries (Q1)
-- or all its windows avoid -1 -1, 1 1, -1 1 and 1 -1 (Q2). Inclusion-exclusion gives
-- a(n) + T3(n) = T1(n) + T2(n), where Tk(n) counts the arrays whose windows satisfy Qk and
-- Q3 = Q1 and Q2. Splitting off the first entry (Fin.consEquiv) gives 3-state transfer recurrences:
-- T1(m) = 3*2^m, T2(m+2) = T2(m+1) + 2T2(m) with T2(0) = 3, T2(1) = 5, so 3T2(m) = 8*2^m + (-1)^m,
-- and T3(m+2) = 2T3(m) with T3(0) = 3, T3(1) = 4. The closed forms follow for even and odd n, and
-- the g.f. by comparing coefficients ((x - 2)(x + 1)(x^2 - 2) annihilates all three counts).

namespace P1A211476

open OMA.S_oeis_a211476

/-- The test of the statement for two windows, in Fin 3 coordinates (the value of p is p - 1). -/
def G (p q r s : Fin 3) : Bool :=
  decide (nd (((p : ℕ) : ℤ) - 1) (((q : ℕ) : ℤ) - 1) (((r : ℕ) : ℤ) - 1) (((s : ℕ) : ℤ) - 1) ∈
    ({1, 3} : Finset ℕ))

/-- Adjacent entries are different. -/
def Q1 (u w : Fin 3) : Bool := decide (¬(u = 0 ∧ w = 0) ∧ ¬(u = 1 ∧ w = 1) ∧ ¬(u = 2 ∧ w = 2))

/-- Adjacent entries are not both nonzero (in values). -/
def Q2 (u w : Fin 3) : Bool :=
  decide (¬(u = 0 ∧ w = 0) ∧ ¬(u = 2 ∧ w = 2) ∧ ¬(u = 0 ∧ w = 2) ∧ ¬(u = 2 ∧ w = 0))

/-- Both conditions. -/
def Q3 (u w : Fin 3) : Bool := Q1 u w && Q2 u w

theorem fin1 : ∀ p q r s : Fin 3, G p q p q = true → G r s r s = true → G p q r s = true →
    Q1 p q = true ∨ Q2 r s = true := by
  decide +kernel

theorem fin2 : ∀ p q r s : Fin 3, Q1 p q = true → Q1 r s = true → G p q r s = true := by
  decide +kernel

theorem fin3 : ∀ p q r s : Fin 3, Q2 p q = true → Q2 r s = true → G p q r s = true := by
  decide +kernel

theorem q3pt : ∀ u w : Fin 3, Q3 u w = true ↔ Q1 u w = true ∧ Q2 u w = true := by
  decide

theorem charac (n : ℕ) (x : Fin (n + 1) → Fin 3) :
    (∀ i j : Fin n, nd (v x i.castSucc) (v x i.succ) (v x j.castSucc) (v x j.succ) ∈
      ({1, 3} : Finset ℕ)) ↔
    (∀ i : Fin n, Q1 (x i.castSucc) (x i.succ) = true) ∨
      (∀ i : Fin n, Q2 (x i.castSucc) (x i.succ) = true) := by
  have hG : ∀ i j : Fin n,
      (nd (v x i.castSucc) (v x i.succ) (v x j.castSucc) (v x j.succ) ∈
        ({1, 3} : Finset ℕ)) ↔
        G (x i.castSucc) (x i.succ) (x j.castSucc) (x j.succ) = true :=
    fun _ _ => decide_eq_true_iff.symm
  constructor
  · intro h
    by_cases h1 : ∀ i : Fin n, Q1 (x i.castSucc) (x i.succ) = true
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
    N Q1 (m + 1) 0 + N Q1 (m + 1) 1 + N Q1 (m + 1) 2 =
      2 * (N Q1 m 0 + N Q1 m 1 + N Q1 m 2) := by
  have h0 := ite3 Q1 m 0
  have h1 := ite3 Q1 m 1
  have h2 := ite3 Q1 m 2
  rw [if_neg (by decide : ¬ (Q1 0 0 = true)), if_pos (by decide : Q1 0 1 = true),
    if_pos (by decide : Q1 0 2 = true)] at h0
  rw [if_pos (by decide : Q1 1 0 = true), if_neg (by decide : ¬ (Q1 1 1 = true)),
    if_pos (by decide : Q1 1 2 = true)] at h1
  rw [if_pos (by decide : Q1 2 0 = true), if_pos (by decide : Q1 2 1 = true),
    if_neg (by decide : ¬ (Q1 2 2 = true))] at h2
  omega

theorem rec2 (m : ℕ) :
    N Q2 (m + 1) 0 + N Q2 (m + 1) 1 + N Q2 (m + 1) 2 =
      (N Q2 m 0 + N Q2 m 1 + N Q2 m 2) + 2 * N Q2 m 1 ∧
    N Q2 (m + 1) 1 = N Q2 m 0 + N Q2 m 1 + N Q2 m 2 := by
  have h0 := ite3 Q2 m 0
  have h1 := ite3 Q2 m 1
  have h2 := ite3 Q2 m 2
  rw [if_neg (by decide : ¬ (Q2 0 0 = true)), if_pos (by decide : Q2 0 1 = true),
    if_neg (by decide : ¬ (Q2 0 2 = true))] at h0
  rw [if_pos (by decide : Q2 1 0 = true), if_pos (by decide : Q2 1 1 = true),
    if_pos (by decide : Q2 1 2 = true)] at h1
  rw [if_neg (by decide : ¬ (Q2 2 0 = true)), if_pos (by decide : Q2 2 1 = true),
    if_neg (by decide : ¬ (Q2 2 2 = true))] at h2
  constructor
  · omega
  · omega

theorem rec3 (m : ℕ) :
    N Q3 (m + 1) 0 + N Q3 (m + 1) 1 + N Q3 (m + 1) 2 =
      (N Q3 m 0 + N Q3 m 1 + N Q3 m 2) + N Q3 m 1 ∧
    N Q3 (m + 1) 1 + N Q3 m 1 = N Q3 m 0 + N Q3 m 1 + N Q3 m 2 := by
  have h0 := ite3 Q3 m 0
  have h1 := ite3 Q3 m 1
  have h2 := ite3 Q3 m 2
  rw [if_neg (by decide : ¬ (Q3 0 0 = true)), if_pos (by decide : Q3 0 1 = true),
    if_neg (by decide : ¬ (Q3 0 2 = true))] at h0
  rw [if_pos (by decide : Q3 1 0 = true), if_neg (by decide : ¬ (Q3 1 1 = true)),
    if_pos (by decide : Q3 1 2 = true)] at h1
  rw [if_neg (by decide : ¬ (Q3 2 0 = true)), if_pos (by decide : Q3 2 1 = true),
    if_neg (by decide : ¬ (Q3 2 2 = true))] at h2
  constructor
  · omega
  · omega

theorem ie (n : ℕ) : a n + (N Q3 n 0 + N Q3 n 1 + N Q3 n 2) =
    (N Q1 n 0 + N Q1 n 1 + N Q1 n 2) + (N Q2 n 0 + N Q2 n 1 + N Q2 n 2) := by
  rw [← cardP Q1 n, ← cardP Q2 n, ← cardP Q3 n]
  have hU : (Finset.univ : Finset (Fin (n + 1) → Fin 3)).filter (fun x => ∀ i j : Fin n,
      nd (v x i.castSucc) (v x i.succ) (v x j.castSucc) (v x j.succ) ∈
        ({1, 3} : Finset ℕ)) =
      (Finset.univ : Finset (Fin (n + 1) → Fin 3)).filter
        (fun x => ∀ i : Fin n, Q1 (x i.castSucc) (x i.succ) = true) ∪
      (Finset.univ : Finset (Fin (n + 1) → Fin 3)).filter
        (fun x => ∀ i : Fin n, Q2 (x i.castSucc) (x i.succ) = true) := by
    ext x
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    exact charac n x
  have hI : (Finset.univ : Finset (Fin (n + 1) → Fin 3)).filter
        (fun x => ∀ i : Fin n, Q1 (x i.castSucc) (x i.succ) = true) ∩
      (Finset.univ : Finset (Fin (n + 1) → Fin 3)).filter
        (fun x => ∀ i : Fin n, Q2 (x i.castSucc) (x i.succ) = true) =
      (Finset.univ : Finset (Fin (n + 1) → Fin 3)).filter
        (fun x => ∀ i : Fin n, Q3 (x i.castSucc) (x i.succ) = true) := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h i => (q3pt _ _).mpr ⟨h.1 i, h.2 i⟩,
      fun h => ⟨fun i => ((q3pt _ _).mp (h i)).1, fun i => ((q3pt _ _).mp (h i)).2⟩⟩
  unfold a
  rw [hU, ← hI]
  exact Finset.card_union_add_card_inter _ _

end P1A211476

open OMA.S_oeis_a211476 P1A211476 in
theorem OMA.solution : type_of% @OMA.S_oeis_a211476.main := by
  obtain ⟨A, hAd⟩ : ∃ A : ℕ → ℕ, ∀ m, a m = A m := ⟨a, fun _ => rfl⟩
  obtain ⟨T1, hT1⟩ : ∃ T : ℕ → ℕ, ∀ m, T m = N Q1 m 0 + N Q1 m 1 + N Q1 m 2 :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨T2, hT2⟩ : ∃ T : ℕ → ℕ, ∀ m, T m = N Q2 m 0 + N Q2 m 1 + N Q2 m 2 :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨T3, hT3⟩ : ∃ T : ℕ → ℕ, ∀ m, T m = N Q3 m 0 + N Q3 m 1 + N Q3 m 2 :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨d2, hd2⟩ : ∃ c : ℕ → ℕ, ∀ m, c m = N Q2 m 1 := ⟨_, fun _ => rfl⟩
  obtain ⟨d3, hd3⟩ : ∃ c : ℕ → ℕ, ∀ m, c m = N Q3 m 1 := ⟨_, fun _ => rfl⟩
  have e1 : ∀ m, T1 (m + 1) = 2 * T1 m := by
    intro m
    rw [hT1, hT1]
    exact rec1 m
  have e2 : ∀ m, T2 (m + 1) = T2 m + 2 * d2 m ∧ d2 (m + 1) = T2 m := by
    intro m
    rw [hT2, hT2, hd2, hd2]
    exact rec2 m
  have e3 : ∀ m, T3 (m + 1) = T3 m + d3 m ∧ d3 (m + 1) + d3 m = T3 m := by
    intro m
    rw [hT3, hT3, hd3, hd3]
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
  have j2 : d2 0 = 1 := by
    have h := hd2 0
    rw [N0] at h
    exact h
  have j3 : d3 0 = 1 := by
    have h := hd3 0
    rw [N0] at h
    exact h
  have p2 : ∀ m, T2 (m + 2) = T2 (m + 1) + 2 * T2 m := by
    intro m
    have h1 := (e2 (m + 1)).1
    have h2 := (e2 m).2
    rw [show m + 1 + 1 = m + 2 by omega] at h1
    omega
  have p3 : ∀ m, T3 (m + 2) = 2 * T3 m := by
    intro m
    have h1 := (e3 (m + 1)).1
    have h2 := (e3 m).1
    have h3 := (e3 m).2
    rw [show m + 1 + 1 = m + 2 by omega] at h1
    omega
  have q1 : ∀ m, T1 m = 3 * 2 ^ m := by
    intro m
    induction m with
    | zero => simp [i1]
    | succ k ih =>
      rw [e1 k, ih]
      ring
  have t21 : T2 1 = 5 := by
    have h := (e2 0).1
    rw [show (0 : ℕ) + 1 = 1 from rfl, i2, j2] at h
    omega
  have t31 : T3 1 = 4 := by
    have h := (e3 0).1
    rw [show (0 : ℕ) + 1 = 1 from rfl, i3, j3] at h
    omega
  have q2 : ∀ m, (3 : ℚ) * (T2 m : ℚ) = 8 * 2 ^ m + (-1) ^ m ∧
      (3 : ℚ) * (T2 (m + 1) : ℚ) = 8 * 2 ^ (m + 1) + (-1) ^ (m + 1) := by
    intro m
    induction m with
    | zero =>
      show (3 : ℚ) * (T2 0 : ℚ) = 8 * 2 ^ 0 + (-1) ^ 0 ∧
        (3 : ℚ) * (T2 1 : ℚ) = 8 * 2 ^ 1 + (-1) ^ 1
      rw [i2, t21]
      norm_num
    | succ k ih =>
      obtain ⟨h0, h1⟩ := ih
      refine ⟨h1, ?_⟩
      have hR : (T2 (k + 2) : ℚ) = (T2 (k + 1) : ℚ) + 2 * (T2 k : ℚ) := by
        exact_mod_cast p2 k
      rw [show k + 1 + 1 = k + 2 by omega]
      linear_combination 3 * hR + h1 + 2 * h0
  have q3e : ∀ k, T3 (2 * k) = 3 * 2 ^ k := by
    intro k
    induction k with
    | zero => simp [i3]
    | succ k ih =>
      rw [show 2 * (k + 1) = 2 * k + 2 by ring, p3 (2 * k), ih]
      ring
  have q3o : ∀ k, T3 (2 * k + 1) = 4 * 2 ^ k := by
    intro k
    induction k with
    | zero => simp [t31]
    | succ k ih =>
      rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 2 by ring, p3 (2 * k + 1), ih]
      ring
  have hq : ∀ m, (A m : ℚ) = (T1 m : ℚ) + (T2 m : ℚ) - (T3 m : ℚ) := by
    intro m
    have h2 : (A m : ℚ) + (T3 m : ℚ) = (T1 m : ℚ) + (T2 m : ℚ) := by exact_mod_cast ha m
    linear_combination h2
  have hq1 : ∀ m, (T1 m : ℚ) = 3 * 2 ^ m := by
    intro m
    exact_mod_cast q1 m
  refine ⟨?_, ?_, ?_⟩
  · have t22 : T2 2 = 11 := by
      have h := p2 0
      rw [show (0 : ℕ) + 2 = 2 from rfl, show (0 : ℕ) + 1 = 1 from rfl, t21, i2] at h
      omega
    have t23 : T2 3 = 21 := by
      have h := p2 1
      rw [show (1 : ℕ) + 2 = 3 from rfl, show (1 : ℕ) + 1 = 2 from rfl, t22, t21] at h
      omega
    have t24 : T2 4 = 43 := by
      have h := p2 2
      rw [show (2 : ℕ) + 2 = 4 from rfl, show (2 : ℕ) + 1 = 3 from rfl, t23, t22] at h
      omega
    have t32 : T3 2 = 6 := by
      have h := p3 0
      rw [show (0 : ℕ) + 2 = 2 from rfl, i3] at h
      omega
    have t33 : T3 3 = 8 := by
      have h := p3 1
      rw [show (1 : ℕ) + 2 = 3 from rfl, t31] at h
      omega
    have t34 : T3 4 = 12 := by
      have h := p3 2
      rw [show (2 : ℕ) + 2 = 4 from rfl, t32] at h
      omega
    have t11 : T1 1 = 6 := (q1 1).trans (by norm_num)
    have t12 : T1 2 = 12 := (q1 2).trans (by norm_num)
    have t13 : T1 3 = 24 := (q1 3).trans (by norm_num)
    have t14 : T1 4 = 48 := (q1 4).trans (by norm_num)
    have A1 : A 1 = 7 := by
      have h := ha 1
      rw [t31, t11, t21] at h
      omega
    have A2 : A 2 = 17 := by
      have h := ha 2
      rw [t32, t12, t22] at h
      omega
    have A3 : A 3 = 37 := by
      have h := ha 3
      rw [t33, t13, t23] at h
      omega
    have A4 : A 4 = 79 := by
      have h := ha 4
      rw [t34, t14, t24] at h
      omega
    obtain ⟨b, hb⟩ : ∃ b : ℕ → ℚ, ∀ n, b n = (A (n + 1) : ℚ) := ⟨_, fun _ => rfl⟩
    have hmk : PowerSeries.mk (fun n => (a (n + 1) : ℚ)) = PowerSeries.mk b := by
      congr 1
      funext n
      rw [hb, hAd]
    have hb0 : b 0 = 7 := by
      rw [hb 0, show (0 : ℕ) + 1 = 1 from rfl]
      exact_mod_cast A1
    have hb1 : b 1 = 17 := by
      rw [hb 1, show (1 : ℕ) + 1 = 2 from rfl]
      exact_mod_cast A2
    have hb2 : b 2 = 37 := by
      rw [hb 2, show (2 : ℕ) + 1 = 3 from rfl]
      exact_mod_cast A3
    have hb3 : b 3 = 79 := by
      rw [hb 3, show (3 : ℕ) + 1 = 4 from rfl]
      exact_mod_cast A4
    have pQ3 : ∀ m, (T3 (m + 2) : ℚ) = 2 * (T3 m : ℚ) := by
      intro m
      exact_mod_cast p3 m
    have hr4 : ∀ m, 4 ≤ m →
        b m - b (m - 1) - 4 * b (m - 2) + 2 * b (m - 3) + 4 * b (m - 4) = 0 := by
      intro m hm
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 4 := ⟨m - 4, by omega⟩
      rw [show k + 4 - 1 = k + 3 by omega, show k + 4 - 2 = k + 2 by omega,
        show k + 4 - 3 = k + 1 by omega, show k + 4 - 4 = k by omega,
        hb (k + 4), hb (k + 3), hb (k + 2), hb (k + 1), hb k,
        show k + 4 + 1 = k + 5 by omega, show k + 3 + 1 = k + 4 by omega,
        show k + 2 + 1 = k + 3 by omega, show k + 1 + 1 = k + 2 by omega,
        hq (k + 5), hq (k + 4), hq (k + 3), hq (k + 2), hq (k + 1),
        hq1 (k + 5), hq1 (k + 4), hq1 (k + 3), hq1 (k + 2), hq1 (k + 1)]
      have u5 := (q2 (k + 5)).1
      have u4 := (q2 (k + 4)).1
      have u3 := (q2 (k + 3)).1
      have u2 := (q2 (k + 2)).1
      have u1 := (q2 (k + 1)).1
      have r1 := pQ3 (k + 3)
      have r2 := pQ3 (k + 2)
      have r3 := pQ3 (k + 1)
      rw [show k + 3 + 2 = k + 5 by omega] at r1
      rw [show k + 2 + 2 = k + 4 by omega] at r2
      rw [show k + 1 + 2 = k + 3 by omega] at r3
      linear_combination (1 / 3 : ℚ) * u5 - (1 / 3 : ℚ) * u4 - (4 / 3 : ℚ) * u3 +
        (2 / 3 : ℚ) * u2 + (4 / 3 : ℚ) * u1 - r1 + r2 + 2 * r3
    have gfb : PowerSeries.mk b *
        ((1 + PowerSeries.X) * (1 - 2 * PowerSeries.X) * (1 - 2 * PowerSeries.X ^ 2)) =
        7 + 10 * PowerSeries.X - 8 * PowerSeries.X ^ 2 - 12 * PowerSeries.X ^ 3 := by
      have e : PowerSeries.mk b *
          ((1 + PowerSeries.X) * (1 - 2 * PowerSeries.X) * (1 - 2 * PowerSeries.X ^ 2)) =
          PowerSeries.mk b
            - PowerSeries.mk b * PowerSeries.X ^ 1
            - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 4 * (PowerSeries.mk b * PowerSeries.X ^ 2)
            + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2 * (PowerSeries.mk b * PowerSeries.X ^ 3)
            + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 4 *
              (PowerSeries.mk b * PowerSeries.X ^ 4) := by
        rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 4,
          map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 2]
        ring
      have e2 : (7 + 10 * PowerSeries.X - 8 * PowerSeries.X ^ 2 - 12 * PowerSeries.X ^ 3 :
          PowerSeries ℚ) =
          (PowerSeries.C : ℚ →+* PowerSeries ℚ) 7 * PowerSeries.X ^ 0
            + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 10 * PowerSeries.X ^ 1
            - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 8 * PowerSeries.X ^ 2
            - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 12 * PowerSeries.X ^ 3 := by
        rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 7,
          map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 10,
          map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 8,
          map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 12]
        ring
      rw [e, e2]
      ext m
      simp only [map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
        PowerSeries.coeff_mk, PowerSeries.coeff_C]
      rcases Nat.lt_or_ge m 4 with hm | hm
      · interval_cases m
        · norm_num [hb0]
        · norm_num [hb0, hb1]
        · norm_num [hb0, hb1, hb2]
        · norm_num [hb0, hb1, hb2, hb3]
      · simp (disch := omega) only [if_pos, if_neg]
        linarith [hr4 m hm]
    rw [hmk]
    calc PowerSeries.X * PowerSeries.mk b *
          ((1 + PowerSeries.X) * (1 - 2 * PowerSeries.X) * (1 - 2 * PowerSeries.X ^ 2))
        = PowerSeries.X * (PowerSeries.mk b *
          ((1 + PowerSeries.X) * (1 - 2 * PowerSeries.X) * (1 - 2 * PowerSeries.X ^ 2))) := by
          ring
      _ = PowerSeries.X * (7 + 10 * PowerSeries.X - 8 * PowerSeries.X ^ 2 -
          12 * PowerSeries.X ^ 3) := by
          rw [gfb]
  · intro n _ hev
    obtain ⟨k, rfl⟩ := hev
    rw [show (k + k) / 2 = k by omega, show k + k = 2 * k by ring, hAd (2 * k)]
    have h1 := hq (2 * k)
    have h2 := hq1 (2 * k)
    have h3 := (q2 (2 * k)).1
    have h4 : (T3 (2 * k) : ℚ) = 3 * 2 ^ k := by exact_mod_cast q3e k
    have h5 : ((-1 : ℚ)) ^ (2 * k) = 1 := by
      rw [pow_mul]
      norm_num
    linear_combination h1 + h2 + (1 / 3 : ℚ) * h3 - h4 + (1 / 3 : ℚ) * h5
  · intro n _ hod
    obtain ⟨k, rfl⟩ := hod
    rw [show (2 * k + 1 + 3) / 2 = k + 2 by omega, hAd (2 * k + 1)]
    have h1 := hq (2 * k + 1)
    have h2 := hq1 (2 * k + 1)
    have h3 := (q2 (2 * k + 1)).1
    have h4 : (T3 (2 * k + 1) : ℚ) = 4 * 2 ^ k := by exact_mod_cast q3o k
    have h5 : ((-1 : ℚ)) ^ (2 * k + 1) = -1 := by
      rw [pow_succ, pow_mul]
      norm_num
    linear_combination h1 + h2 + (1 / 3 : ℚ) * h3 - h4 + (1 / 3 : ℚ) * h5
