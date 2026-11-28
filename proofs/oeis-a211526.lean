import OMAStatements.S_oeis_a211526

-- Problem: A211526: Number of -1..1 arrays x(i) of n+1 elements i=1..n+1 with set{t,u,v in 0,1}((x[i+t]+x[j+u]+x[k+v])*(-1)^(t+u+v)) having two, four or five distinct values for every i,j,k<=n.
-- Upstream: formal-conjectures statements/oeis-a211526.lean:0 (declaration OMA.S_oeis_a211526.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: write the entries as Fin 3 values (0, 1, 2 stand for -1, 0, 1). Finite checks on
-- window triples show: a window 0,0 (in values) is never allowed; a window -1,-1 or 1,1 together
-- with a window containing a 0 is never allowed; three windows from the edge classes {-1,0},
-- {0,1}, {-1,1} are never allowed together; and arrays all of whose windows lie in one of the
-- classes R0 (entries +-1), R1, R2, R3 (adjacent entries different, edge class {-1,0}, {0,1} or
-- {-1,1} missing) always qualify. Hence the admissible arrays form L0 u (L1 u L2 u L3), Lk being
-- the arrays whose windows satisfy Rk, and inclusion-exclusion reduces a(n) to eight 3-state
-- transfer counts (Fin.consEquiv): a(n) + 8 = 2^(n+1) + W1(n) + W2(n) + W3(n) for n >= 1, where
-- each Wk satisfies W(m+2) = 2W(m), W(0) = 3, W(1) = 4. The closed forms follow, and the g.f. by
-- comparing coefficients ((x - 1)(x - 2)(x^2 - 2) annihilates the counts).

namespace P1A211526

open OMA.S_oeis_a211526

/-- The test of the statement for three windows, in Fin 3 coordinates (the value of p is p - 1). -/
def G (p q r s t u : Fin 3) : Bool :=
  decide (nd (((p : ℕ) : ℤ) - 1) (((q : ℕ) : ℤ) - 1) (((r : ℕ) : ℤ) - 1) (((s : ℕ) : ℤ) - 1)
    (((t : ℕ) : ℤ) - 1) (((u : ℕ) : ℤ) - 1) ∈ ({2, 4, 5} : Finset ℕ))

/-- Both entries are -1 or 1. -/
def R0 (u w : Fin 3) : Bool := decide (u ≠ 1 ∧ w ≠ 1)

/-- Different entries, not -1 next to 0. -/
def R1 (u w : Fin 3) : Bool := decide (u ≠ w ∧ ¬(u = 0 ∧ w = 1) ∧ ¬(u = 1 ∧ w = 0))

/-- Different entries, not 0 next to 1. -/
def R2 (u w : Fin 3) : Bool := decide (u ≠ w ∧ ¬(u = 1 ∧ w = 2) ∧ ¬(u = 2 ∧ w = 1))

/-- Different entries, not -1 next to 1. -/
def R3 (u w : Fin 3) : Bool := decide (u ≠ w ∧ ¬(u = 0 ∧ w = 2) ∧ ¬(u = 2 ∧ w = 0))

/-- The window is -1,1 or 1,-1. -/
def R12 (u w : Fin 3) : Bool := decide ((u = 0 ∧ w = 2) ∨ (u = 2 ∧ w = 0))

/-- The window is 0,1 or 1,0. -/
def R13 (u w : Fin 3) : Bool := decide ((u = 1 ∧ w = 2) ∨ (u = 2 ∧ w = 1))

/-- The window is -1,0 or 0,-1. -/
def R23 (u w : Fin 3) : Bool := decide ((u = 0 ∧ w = 1) ∨ (u = 1 ∧ w = 0))

/-- No window at all. -/
def R123 (u w : Fin 3) : Bool := R13 u w && R23 u w

theorem b0 : ∀ p q r s t u : Fin 3, R0 p q = true → R0 r s = true → R0 t u = true →
    G p q r s t u = true := by
  decide +kernel

theorem b1 : ∀ p q r s t u : Fin 3, R1 p q = true → R1 r s = true → R1 t u = true →
    G p q r s t u = true := by
  decide +kernel

theorem b2 : ∀ p q r s t u : Fin 3, R2 p q = true → R2 r s = true → R2 t u = true →
    G p q r s t u = true := by
  decide +kernel

theorem b3 : ∀ p q r s t u : Fin 3, R3 p q = true → R3 r s = true → R3 t u = true →
    G p q r s t u = true := by
  decide +kernel

theorem f12 : ∀ p q r s : Fin 3, (r = 1 ∨ s = 1) → p = q → G p q p q p q = true →
    G p q r s r s = true → G r s r s r s = true → False := by
  decide +kernel

theorem f3 : ∀ p q r s t u : Fin 3, R23 p q = true → R13 r s = true → R12 t u = true →
    G p q r s t u = true → False := by
  decide +kernel

theorem r0f : ∀ u w : Fin 3, ¬ (R0 u w = true) → u = 1 ∨ w = 1 := by
  decide

theorem r1of : ∀ u w : Fin 3, u ≠ w → ¬ (R23 u w = true) → R1 u w = true := by
  decide

theorem r2of : ∀ u w : Fin 3, u ≠ w → ¬ (R13 u w = true) → R2 u w = true := by
  decide

theorem r3of : ∀ u w : Fin 3, u ≠ w → ¬ (R12 u w = true) → R3 u w = true := by
  decide

theorem p12 : ∀ u w : Fin 3, R12 u w = true ↔ R1 u w = true ∧ R2 u w = true := by
  decide

theorem p13 : ∀ u w : Fin 3, R13 u w = true ↔ R1 u w = true ∧ R3 u w = true := by
  decide

theorem p23 : ∀ u w : Fin 3, R23 u w = true ↔ R2 u w = true ∧ R3 u w = true := by
  decide

theorem p123 : ∀ u w : Fin 3, R123 u w = true ↔ R13 u w = true ∧ R23 u w = true := by
  decide

theorem q01 : ∀ u w : Fin 3, R0 u w = true → R1 u w = true → R12 u w = true := by
  decide

theorem q02 : ∀ u w : Fin 3, R0 u w = true → R2 u w = true → R12 u w = true := by
  decide

theorem q03 : ∀ u w : Fin 3, R0 u w = true → R3 u w = true → R12 u w = true := by
  decide

theorem q12a : ∀ u w : Fin 3, R12 u w = true → R0 u w = true := by
  decide

theorem q12b : ∀ u w : Fin 3, R12 u w = true → R1 u w = true := by
  decide

theorem charac (n : ℕ) (x : Fin (n + 1) → Fin 3) :
    (∀ i j k : Fin n, nd (v x i.castSucc) (v x i.succ) (v x j.castSucc) (v x j.succ)
      (v x k.castSucc) (v x k.succ) ∈ ({2, 4, 5} : Finset ℕ)) ↔
    (∀ i : Fin n, R0 (x i.castSucc) (x i.succ) = true) ∨
      (((∀ i : Fin n, R1 (x i.castSucc) (x i.succ) = true) ∨
        (∀ i : Fin n, R2 (x i.castSucc) (x i.succ) = true)) ∨
        (∀ i : Fin n, R3 (x i.castSucc) (x i.succ) = true)) := by
  have hG : ∀ i j k : Fin n,
      (nd (v x i.castSucc) (v x i.succ) (v x j.castSucc) (v x j.succ) (v x k.castSucc)
        (v x k.succ) ∈ ({2, 4, 5} : Finset ℕ)) ↔
        G (x i.castSucc) (x i.succ) (x j.castSucc) (x j.succ) (x k.castSucc) (x k.succ) =
          true :=
    fun _ _ _ => decide_eq_true_iff.symm
  constructor
  · intro h
    have h' : ∀ i j k : Fin n,
        G (x i.castSucc) (x i.succ) (x j.castSucc) (x j.succ) (x k.castSucc) (x k.succ) =
          true :=
      fun i j k => (hG i j k).mp (h i j k)
    by_cases h0 : ∀ i : Fin n, R0 (x i.castSucc) (x i.succ) = true
    · exact Or.inl h0
    · right
      obtain ⟨i0, hi0⟩ := not_forall.mp h0
      have hz := r0f _ _ hi0
      have hd : ∀ j : Fin n, x j.castSucc ≠ x j.succ := fun j heq =>
        f12 _ _ _ _ hz heq (h' j j j) (h' j i0 i0) (h' i0 i0 i0)
      by_cases hA : ∃ i : Fin n, R23 (x i.castSucc) (x i.succ) = true
      · by_cases hC : ∃ i : Fin n, R13 (x i.castSucc) (x i.succ) = true
        · by_cases hE : ∃ i : Fin n, R12 (x i.castSucc) (x i.succ) = true
          · exfalso
            obtain ⟨iA, hiA⟩ := hA
            obtain ⟨iC, hiC⟩ := hC
            obtain ⟨iE, hiE⟩ := hE
            exact f3 _ _ _ _ _ _ hiA hiC hiE (h' iA iC iE)
          · exact Or.inr (fun i => r3of _ _ (hd i) (fun hh => hE ⟨i, hh⟩))
        · exact Or.inl (Or.inr (fun i => r2of _ _ (hd i) (fun hh => hC ⟨i, hh⟩)))
      · exact Or.inl (Or.inl (fun i => r1of _ _ (hd i) (fun hh => hA ⟨i, hh⟩)))
  · rintro (h | (h | h) | h) i j k
    · exact (hG i j k).mpr (b0 _ _ _ _ _ _ (h i) (h j) (h k))
    · exact (hG i j k).mpr (b1 _ _ _ _ _ _ (h i) (h j) (h k))
    · exact (hG i j k).mpr (b2 _ _ _ _ _ _ (h i) (h j) (h k))
    · exact (hG i j k).mpr (b3 _ _ _ _ _ _ (h i) (h j) (h k))

/-- The number of arrays of length m + 1 that start with u and whose adjacent pairs satisfy P. -/
def N (P : Fin 3 → Fin 3 → Bool) (m : ℕ) (u : Fin 3) : ℕ :=
  ∑ t : Fin m → Fin 3, if (∀ i : Fin m, P ((Fin.cons u t : Fin (m + 1) → Fin 3) i.castSucc)
    ((Fin.cons u t : Fin (m + 1) → Fin 3) i.succ) = true) then 1 else 0

/-- The arrays of length m + 1 whose adjacent pairs satisfy P. -/
def L (P : Fin 3 → Fin 3 → Bool) (m : ℕ) : Finset (Fin (m + 1) → Fin 3) :=
  (Finset.univ : Finset (Fin (m + 1) → Fin 3)).filter
    (fun x => ∀ i : Fin m, P (x i.castSucc) (x i.succ) = true)

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
    (L P m).card = N P m 0 + N P m 1 + N P m 2 := by
  unfold L
  rw [Finset.card_filter, total P m, Fin.sum_univ_three]

theorem interL (P Q R : Fin 3 → Fin 3 → Bool) (m : ℕ)
    (h : ∀ u w : Fin 3, R u w = true ↔ P u w = true ∧ Q u w = true) :
    L P m ∩ L Q m = L R m := by
  ext x
  simp only [L, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun hh i => (h _ _).mpr ⟨hh.1 i, hh.2 i⟩,
    fun hh => ⟨fun i => ((h _ _).mp (hh i)).1, fun i => ((h _ _).mp (hh i)).2⟩⟩

theorem rec0 (m : ℕ) :
    N R0 (m + 1) 0 + N R0 (m + 1) 2 = 2 * (N R0 m 0 + N R0 m 2) ∧
    N R0 (m + 1) 0 + N R0 (m + 1) 1 + N R0 (m + 1) 2 = 2 * (N R0 m 0 + N R0 m 2) := by
  have h0 := ite3 R0 m 0
  have h1 := ite3 R0 m 1
  have h2 := ite3 R0 m 2
  rw [if_pos (by decide : R0 0 0 = true), if_neg (by decide : ¬ (R0 0 1 = true)),
    if_pos (by decide : R0 0 2 = true)] at h0
  rw [if_neg (by decide : ¬ (R0 1 0 = true)), if_neg (by decide : ¬ (R0 1 1 = true)),
    if_neg (by decide : ¬ (R0 1 2 = true))] at h1
  rw [if_pos (by decide : R0 2 0 = true), if_neg (by decide : ¬ (R0 2 1 = true)),
    if_pos (by decide : R0 2 2 = true)] at h2
  constructor
  · omega
  · omega

theorem rec1 (m : ℕ) :
    N R1 (m + 1) 0 + N R1 (m + 1) 1 + N R1 (m + 1) 2 =
      (N R1 m 0 + N R1 m 1 + N R1 m 2) + N R1 m 2 ∧
    N R1 (m + 1) 2 + N R1 m 2 = N R1 m 0 + N R1 m 1 + N R1 m 2 := by
  have h0 := ite3 R1 m 0
  have h1 := ite3 R1 m 1
  have h2 := ite3 R1 m 2
  rw [if_neg (by decide : ¬ (R1 0 0 = true)), if_neg (by decide : ¬ (R1 0 1 = true)),
    if_pos (by decide : R1 0 2 = true)] at h0
  rw [if_neg (by decide : ¬ (R1 1 0 = true)), if_neg (by decide : ¬ (R1 1 1 = true)),
    if_pos (by decide : R1 1 2 = true)] at h1
  rw [if_pos (by decide : R1 2 0 = true), if_pos (by decide : R1 2 1 = true),
    if_neg (by decide : ¬ (R1 2 2 = true))] at h2
  constructor
  · omega
  · omega

theorem rec2 (m : ℕ) :
    N R2 (m + 1) 0 + N R2 (m + 1) 1 + N R2 (m + 1) 2 =
      (N R2 m 0 + N R2 m 1 + N R2 m 2) + N R2 m 0 ∧
    N R2 (m + 1) 0 + N R2 m 0 = N R2 m 0 + N R2 m 1 + N R2 m 2 := by
  have h0 := ite3 R2 m 0
  have h1 := ite3 R2 m 1
  have h2 := ite3 R2 m 2
  rw [if_neg (by decide : ¬ (R2 0 0 = true)), if_pos (by decide : R2 0 1 = true),
    if_pos (by decide : R2 0 2 = true)] at h0
  rw [if_pos (by decide : R2 1 0 = true), if_neg (by decide : ¬ (R2 1 1 = true)),
    if_neg (by decide : ¬ (R2 1 2 = true))] at h1
  rw [if_pos (by decide : R2 2 0 = true), if_neg (by decide : ¬ (R2 2 1 = true)),
    if_neg (by decide : ¬ (R2 2 2 = true))] at h2
  constructor
  · omega
  · omega

theorem rec3 (m : ℕ) :
    N R3 (m + 1) 0 + N R3 (m + 1) 1 + N R3 (m + 1) 2 =
      (N R3 m 0 + N R3 m 1 + N R3 m 2) + N R3 m 1 ∧
    N R3 (m + 1) 1 + N R3 m 1 = N R3 m 0 + N R3 m 1 + N R3 m 2 := by
  have h0 := ite3 R3 m 0
  have h1 := ite3 R3 m 1
  have h2 := ite3 R3 m 2
  rw [if_neg (by decide : ¬ (R3 0 0 = true)), if_pos (by decide : R3 0 1 = true),
    if_neg (by decide : ¬ (R3 0 2 = true))] at h0
  rw [if_pos (by decide : R3 1 0 = true), if_neg (by decide : ¬ (R3 1 1 = true)),
    if_pos (by decide : R3 1 2 = true)] at h1
  rw [if_neg (by decide : ¬ (R3 2 0 = true)), if_pos (by decide : R3 2 1 = true),
    if_neg (by decide : ¬ (R3 2 2 = true))] at h2
  constructor
  · omega
  · omega

theorem rec12 (m : ℕ) :
    N R12 (m + 1) 0 + N R12 (m + 1) 1 + N R12 (m + 1) 2 = N R12 m 0 + N R12 m 2 ∧
    N R12 (m + 1) 0 + N R12 (m + 1) 2 = N R12 m 0 + N R12 m 2 := by
  have h0 := ite3 R12 m 0
  have h1 := ite3 R12 m 1
  have h2 := ite3 R12 m 2
  rw [if_neg (by decide : ¬ (R12 0 0 = true)), if_neg (by decide : ¬ (R12 0 1 = true)),
    if_pos (by decide : R12 0 2 = true)] at h0
  rw [if_neg (by decide : ¬ (R12 1 0 = true)), if_neg (by decide : ¬ (R12 1 1 = true)),
    if_neg (by decide : ¬ (R12 1 2 = true))] at h1
  rw [if_pos (by decide : R12 2 0 = true), if_neg (by decide : ¬ (R12 2 1 = true)),
    if_neg (by decide : ¬ (R12 2 2 = true))] at h2
  constructor
  · omega
  · omega

theorem rec13 (m : ℕ) :
    N R13 (m + 1) 0 + N R13 (m + 1) 1 + N R13 (m + 1) 2 = N R13 m 1 + N R13 m 2 ∧
    N R13 (m + 1) 1 + N R13 (m + 1) 2 = N R13 m 1 + N R13 m 2 := by
  have h0 := ite3 R13 m 0
  have h1 := ite3 R13 m 1
  have h2 := ite3 R13 m 2
  rw [if_neg (by decide : ¬ (R13 0 0 = true)), if_neg (by decide : ¬ (R13 0 1 = true)),
    if_neg (by decide : ¬ (R13 0 2 = true))] at h0
  rw [if_neg (by decide : ¬ (R13 1 0 = true)), if_neg (by decide : ¬ (R13 1 1 = true)),
    if_pos (by decide : R13 1 2 = true)] at h1
  rw [if_neg (by decide : ¬ (R13 2 0 = true)), if_pos (by decide : R13 2 1 = true),
    if_neg (by decide : ¬ (R13 2 2 = true))] at h2
  constructor
  · omega
  · omega

theorem rec23 (m : ℕ) :
    N R23 (m + 1) 0 + N R23 (m + 1) 1 + N R23 (m + 1) 2 = N R23 m 0 + N R23 m 1 ∧
    N R23 (m + 1) 0 + N R23 (m + 1) 1 = N R23 m 0 + N R23 m 1 := by
  have h0 := ite3 R23 m 0
  have h1 := ite3 R23 m 1
  have h2 := ite3 R23 m 2
  rw [if_neg (by decide : ¬ (R23 0 0 = true)), if_pos (by decide : R23 0 1 = true),
    if_neg (by decide : ¬ (R23 0 2 = true))] at h0
  rw [if_pos (by decide : R23 1 0 = true), if_neg (by decide : ¬ (R23 1 1 = true)),
    if_neg (by decide : ¬ (R23 1 2 = true))] at h1
  rw [if_neg (by decide : ¬ (R23 2 0 = true)), if_neg (by decide : ¬ (R23 2 1 = true)),
    if_neg (by decide : ¬ (R23 2 2 = true))] at h2
  constructor
  · omega
  · omega

theorem rec123 (m : ℕ) :
    N R123 (m + 1) 0 + N R123 (m + 1) 1 + N R123 (m + 1) 2 = 0 := by
  have h0 := ite3 R123 m 0
  have h1 := ite3 R123 m 1
  have h2 := ite3 R123 m 2
  rw [if_neg (by decide : ¬ (R123 0 0 = true)), if_neg (by decide : ¬ (R123 0 1 = true)),
    if_neg (by decide : ¬ (R123 0 2 = true))] at h0
  rw [if_neg (by decide : ¬ (R123 1 0 = true)), if_neg (by decide : ¬ (R123 1 1 = true)),
    if_neg (by decide : ¬ (R123 1 2 = true))] at h1
  rw [if_neg (by decide : ¬ (R123 2 0 = true)), if_neg (by decide : ¬ (R123 2 1 = true)),
    if_neg (by decide : ¬ (R123 2 2 = true))] at h2
  omega

theorem ie (n : ℕ) : ∃ U V W : ℕ,
    a n + (N R12 n 0 + N R12 n 1 + N R12 n 2) = (N R0 n 0 + N R0 n 1 + N R0 n 2) + U ∧
    U + W = V + (N R3 n 0 + N R3 n 1 + N R3 n 2) ∧
    V + (N R12 n 0 + N R12 n 1 + N R12 n 2) =
      (N R1 n 0 + N R1 n 1 + N R1 n 2) + (N R2 n 0 + N R2 n 1 + N R2 n 2) ∧
    W + (N R123 n 0 + N R123 n 1 + N R123 n 2) =
      (N R13 n 0 + N R13 n 1 + N R13 n 2) + (N R23 n 0 + N R23 n 1 + N R23 n 2) := by
  rw [← cardP R0 n, ← cardP R1 n, ← cardP R2 n, ← cardP R3 n, ← cardP R12 n,
    ← cardP R13 n, ← cardP R23 n, ← cardP R123 n]
  have hU : (Finset.univ : Finset (Fin (n + 1) → Fin 3)).filter (fun x => ∀ i j k : Fin n,
      nd (v x i.castSucc) (v x i.succ) (v x j.castSucc) (v x j.succ) (v x k.castSucc)
        (v x k.succ) ∈ ({2, 4, 5} : Finset ℕ)) =
      L R0 n ∪ (L R1 n ∪ L R2 n ∪ L R3 n) := by
    ext x
    simp only [L, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    exact charac n x
  have hI0 : L R0 n ∩ (L R1 n ∪ L R2 n ∪ L R3 n) = L R12 n := by
    ext x
    simp only [L, Finset.mem_inter, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
      true_and]
    constructor
    · rintro ⟨h0, (h1 | h2) | h3⟩ i
      · exact q01 _ _ (h0 i) (h1 i)
      · exact q02 _ _ (h0 i) (h2 i)
      · exact q03 _ _ (h0 i) (h3 i)
    · intro h
      exact ⟨fun i => q12a _ _ (h i), Or.inl (Or.inl (fun i => q12b _ _ (h i)))⟩
  have hD : (L R1 n ∪ L R2 n) ∩ L R3 n = L R13 n ∪ L R23 n := by
    ext x
    simp only [L, Finset.mem_inter, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
      true_and]
    constructor
    · rintro ⟨h1 | h2, h3⟩
      · exact Or.inl (fun i => (p13 _ _).mpr ⟨h1 i, h3 i⟩)
      · exact Or.inr (fun i => (p23 _ _).mpr ⟨h2 i, h3 i⟩)
    · rintro (h | h)
      · exact ⟨Or.inl (fun i => ((p13 _ _).mp (h i)).1), fun i => ((p13 _ _).mp (h i)).2⟩
      · exact ⟨Or.inr (fun i => ((p23 _ _).mp (h i)).1), fun i => ((p23 _ _).mp (h i)).2⟩
  refine ⟨(L R1 n ∪ L R2 n ∪ L R3 n).card, (L R1 n ∪ L R2 n).card,
    (L R13 n ∪ L R23 n).card, ?_, ?_, ?_, ?_⟩
  · unfold a
    rw [hU, ← hI0]
    exact Finset.card_union_add_card_inter _ _
  · rw [← hD]
    exact Finset.card_union_add_card_inter _ _
  · rw [← interL R1 R2 R12 n p12]
    exact Finset.card_union_add_card_inter _ _
  · rw [← interL R13 R23 R123 n p123]
    exact Finset.card_union_add_card_inter _ _

theorem wform (P : ℕ → ℕ) (h0 : P 0 = 3) (h1 : P 1 = 4) (hr : ∀ m, P (m + 2) = 2 * P m) :
    (∀ k, P (2 * k) = 3 * 2 ^ k) ∧ (∀ k, P (2 * k + 1) = 4 * 2 ^ k) := by
  refine ⟨fun k => ?_, fun k => ?_⟩
  · induction k with
    | zero => simp [h0]
    | succ k ih =>
      rw [show 2 * (k + 1) = 2 * k + 2 by ring, hr (2 * k), ih]
      ring
  · induction k with
    | zero => simp [h1]
    | succ k ih =>
      rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 2 by ring, hr (2 * k + 1), ih]
      ring

theorem wvals (P : ℕ → ℕ) (h0 : P 0 = 3) (h1 : P 1 = 4) (hr : ∀ m, P (m + 2) = 2 * P m) :
    P 2 = 6 ∧ P 3 = 8 ∧ P 4 = 12 := by
  have h2 := hr 0
  have h3 := hr 1
  have h4 := hr 2
  rw [show (0 : ℕ) + 2 = 2 from rfl] at h2
  rw [show (1 : ℕ) + 2 = 3 from rfl] at h3
  rw [show (2 : ℕ) + 2 = 4 from rfl] at h4
  exact ⟨by omega, by omega, by omega⟩

theorem prec (P c : ℕ → ℕ) (h : ∀ m, P (m + 1) = P m + c m ∧ c (m + 1) + c m = P m) :
    ∀ m, P (m + 2) = 2 * P m := by
  intro m
  have h1 := (h (m + 1)).1
  have h2 := (h m).1
  have h3 := (h m).2
  rw [show m + 1 + 1 = m + 2 by omega] at h1
  omega

theorem pone (P c : ℕ → ℕ) (hP : P 0 = 3) (hc : c 0 = 1)
    (h : ∀ m, P (m + 1) = P m + c m ∧ c (m + 1) + c m = P m) : P 1 = 4 := by
  have h1 := (h 0).1
  rw [show (0 : ℕ) + 1 = 1 from rfl, hP, hc] at h1
  omega

theorem eform (E s : ℕ → ℕ) (hs0 : s 0 = 2) (h : ∀ m, E (m + 1) = s m ∧ s (m + 1) = s m) :
    ∀ m, E (m + 1) = 2 := by
  have hs : ∀ m, s m = 2 := by
    intro m
    induction m with
    | zero => exact hs0
    | succ k ih => rw [(h k).2, ih]
  intro m
  rw [(h m).1, hs m]

end P1A211526

open OMA.S_oeis_a211526 P1A211526 in
theorem OMA.solution : type_of% @OMA.S_oeis_a211526.main := by
  obtain ⟨A, hAd⟩ : ∃ A : ℕ → ℕ, ∀ m, a m = A m := ⟨a, fun _ => rfl⟩
  obtain ⟨T0, hT0⟩ : ∃ T : ℕ → ℕ, ∀ m, T m = N R0 m 0 + N R0 m 1 + N R0 m 2 :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨S0, hS0⟩ : ∃ T : ℕ → ℕ, ∀ m, T m = N R0 m 0 + N R0 m 2 := ⟨_, fun _ => rfl⟩
  obtain ⟨P1, hP1⟩ : ∃ T : ℕ → ℕ, ∀ m, T m = N R1 m 0 + N R1 m 1 + N R1 m 2 :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨c1, hc1⟩ : ∃ c : ℕ → ℕ, ∀ m, c m = N R1 m 2 := ⟨_, fun _ => rfl⟩
  obtain ⟨P2, hP2⟩ : ∃ T : ℕ → ℕ, ∀ m, T m = N R2 m 0 + N R2 m 1 + N R2 m 2 :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨c2, hc2⟩ : ∃ c : ℕ → ℕ, ∀ m, c m = N R2 m 0 := ⟨_, fun _ => rfl⟩
  obtain ⟨P3, hP3⟩ : ∃ T : ℕ → ℕ, ∀ m, T m = N R3 m 0 + N R3 m 1 + N R3 m 2 :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨c3, hc3⟩ : ∃ c : ℕ → ℕ, ∀ m, c m = N R3 m 1 := ⟨_, fun _ => rfl⟩
  obtain ⟨E12, hE12⟩ : ∃ T : ℕ → ℕ, ∀ m, T m = N R12 m 0 + N R12 m 1 + N R12 m 2 :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨s12, hs12⟩ : ∃ c : ℕ → ℕ, ∀ m, c m = N R12 m 0 + N R12 m 2 := ⟨_, fun _ => rfl⟩
  obtain ⟨E13, hE13⟩ : ∃ T : ℕ → ℕ, ∀ m, T m = N R13 m 0 + N R13 m 1 + N R13 m 2 :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨s13, hs13⟩ : ∃ c : ℕ → ℕ, ∀ m, c m = N R13 m 1 + N R13 m 2 := ⟨_, fun _ => rfl⟩
  obtain ⟨E23, hE23⟩ : ∃ T : ℕ → ℕ, ∀ m, T m = N R23 m 0 + N R23 m 1 + N R23 m 2 :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨s23, hs23⟩ : ∃ c : ℕ → ℕ, ∀ m, c m = N R23 m 0 + N R23 m 1 := ⟨_, fun _ => rfl⟩
  obtain ⟨Z, hZ⟩ : ∃ T : ℕ → ℕ, ∀ m, T m = N R123 m 0 + N R123 m 1 + N R123 m 2 :=
    ⟨_, fun _ => rfl⟩
  have e0 : ∀ m, S0 (m + 1) = 2 * S0 m ∧ T0 (m + 1) = 2 * S0 m := by
    intro m
    rw [hS0, hS0, hT0]
    exact rec0 m
  have e1 : ∀ m, P1 (m + 1) = P1 m + c1 m ∧ c1 (m + 1) + c1 m = P1 m := by
    intro m
    rw [hP1, hP1, hc1, hc1]
    exact rec1 m
  have e2 : ∀ m, P2 (m + 1) = P2 m + c2 m ∧ c2 (m + 1) + c2 m = P2 m := by
    intro m
    rw [hP2, hP2, hc2, hc2]
    exact rec2 m
  have e3 : ∀ m, P3 (m + 1) = P3 m + c3 m ∧ c3 (m + 1) + c3 m = P3 m := by
    intro m
    rw [hP3, hP3, hc3, hc3]
    exact rec3 m
  have e12 : ∀ m, E12 (m + 1) = s12 m ∧ s12 (m + 1) = s12 m := by
    intro m
    rw [hE12, hs12, hs12]
    exact rec12 m
  have e13 : ∀ m, E13 (m + 1) = s13 m ∧ s13 (m + 1) = s13 m := by
    intro m
    rw [hE13, hs13, hs13]
    exact rec13 m
  have e23 : ∀ m, E23 (m + 1) = s23 m ∧ s23 (m + 1) = s23 m := by
    intro m
    rw [hE23, hs23, hs23]
    exact rec23 m
  have ez : ∀ m, Z (m + 1) = 0 := by
    intro m
    rw [hZ]
    exact rec123 m
  have ha : ∀ m, ∃ U V W : ℕ, A m + E12 m = T0 m + U ∧ U + W = V + P3 m ∧
      V + E12 m = P1 m + P2 m ∧ W + Z m = E13 m + E23 m := by
    intro m
    rw [← hAd, hT0, hP1, hP2, hP3, hE12, hE13, hE23, hZ]
    exact ie m
  have iS0 : S0 0 = 2 := by
    have h := hS0 0
    rw [N0, N0] at h
    omega
  have iP1 : P1 0 = 3 := by
    have h := hP1 0
    rw [N0, N0, N0] at h
    omega
  have iP2 : P2 0 = 3 := by
    have h := hP2 0
    rw [N0, N0, N0] at h
    omega
  have iP3 : P3 0 = 3 := by
    have h := hP3 0
    rw [N0, N0, N0] at h
    omega
  have ic1 : c1 0 = 1 := by
    have h := hc1 0
    rw [N0] at h
    exact h
  have ic2 : c2 0 = 1 := by
    have h := hc2 0
    rw [N0] at h
    exact h
  have ic3 : c3 0 = 1 := by
    have h := hc3 0
    rw [N0] at h
    exact h
  have is12 : s12 0 = 2 := by
    have h := hs12 0
    rw [N0, N0] at h
    omega
  have is13 : s13 0 = 2 := by
    have h := hs13 0
    rw [N0, N0] at h
    omega
  have is23 : s23 0 = 2 := by
    have h := hs23 0
    rw [N0, N0] at h
    omega
  have vS0 : ∀ m, S0 m = 2 ^ (m + 1) := by
    intro m
    induction m with
    | zero => simp [iS0]
    | succ k ih =>
      rw [(e0 k).1, ih]
      ring
  have vT0 : ∀ m, 1 ≤ m → T0 m = 2 ^ (m + 1) := by
    intro m hm
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    rw [(e0 k).2, vS0 k]
    ring
  have pP1 := prec P1 c1 e1
  have pP2 := prec P2 c2 e2
  have pP3 := prec P3 c3 e3
  have tP1 := pone P1 c1 iP1 ic1 e1
  have tP2 := pone P2 c2 iP2 ic2 e2
  have tP3 := pone P3 c3 iP3 ic3 e3
  have hA : ∀ m, 1 ≤ m → A m + 8 = T0 m + P1 m + P2 m + P3 m := by
    intro m hm
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    obtain ⟨U, V, W, h1, h2, h3, h4⟩ := ha (k + 1)
    have g1 := eform E12 s12 is12 e12 k
    have g2 := eform E13 s13 is13 e13 k
    have g3 := eform E23 s23 is23 e23 k
    have g4 := ez k
    omega
  have hAq : ∀ m, 1 ≤ m → (A m : ℚ) = 2 ^ (m + 1) + (P1 m : ℚ) + (P2 m : ℚ) + (P3 m : ℚ) - 8 := by
    intro m hm
    have hq : (A m : ℚ) + 8 = (T0 m : ℚ) + (P1 m : ℚ) + (P2 m : ℚ) + (P3 m : ℚ) := by
      exact_mod_cast hA m hm
    have hq2 : (T0 m : ℚ) = 2 ^ (m + 1) := by exact_mod_cast vT0 m hm
    linear_combination hq + hq2
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨v12, v13, v14⟩ := wvals P1 iP1 tP1 pP1
    obtain ⟨v22, v23, v24⟩ := wvals P2 iP2 tP2 pP2
    obtain ⟨v32, v33, v34⟩ := wvals P3 iP3 tP3 pP3
    have t01 : T0 1 = 4 := (vT0 1 (by norm_num)).trans (by norm_num)
    have t02 : T0 2 = 8 := (vT0 2 (by norm_num)).trans (by norm_num)
    have t03 : T0 3 = 16 := (vT0 3 (by norm_num)).trans (by norm_num)
    have t04 : T0 4 = 32 := (vT0 4 (by norm_num)).trans (by norm_num)
    have A1 : A 1 = 8 := by
      have h := hA 1 (by norm_num)
      omega
    have A2 : A 2 = 18 := by
      have h := hA 2 (by norm_num)
      omega
    have A3 : A 3 = 32 := by
      have h := hA 3 (by norm_num)
      omega
    have A4 : A 4 = 60 := by
      have h := hA 4 (by norm_num)
      omega
    obtain ⟨b, hb⟩ : ∃ b : ℕ → ℚ, ∀ n, b n = (A (n + 1) : ℚ) := ⟨_, fun _ => rfl⟩
    have hmk : PowerSeries.mk (fun n => (a (n + 1) : ℚ)) = PowerSeries.mk b := by
      congr 1
      funext n
      rw [hb, hAd]
    have hb0 : b 0 = 8 := by
      rw [hb 0, show (0 : ℕ) + 1 = 1 from rfl]
      exact_mod_cast A1
    have hb1 : b 1 = 18 := by
      rw [hb 1, show (1 : ℕ) + 1 = 2 from rfl]
      exact_mod_cast A2
    have hb2 : b 2 = 32 := by
      rw [hb 2, show (2 : ℕ) + 1 = 3 from rfl]
      exact_mod_cast A3
    have hb3 : b 3 = 60 := by
      rw [hb 3, show (3 : ℕ) + 1 = 4 from rfl]
      exact_mod_cast A4
    have pq1 : ∀ m, (P1 (m + 2) : ℚ) = 2 * (P1 m : ℚ) := fun m => by exact_mod_cast pP1 m
    have pq2 : ∀ m, (P2 (m + 2) : ℚ) = 2 * (P2 m : ℚ) := fun m => by exact_mod_cast pP2 m
    have pq3 : ∀ m, (P3 (m + 2) : ℚ) = 2 * (P3 m : ℚ) := fun m => by exact_mod_cast pP3 m
    have hr4 : ∀ m, 4 ≤ m → b m - 3 * b (m - 1) + 6 * b (m - 3) - 4 * b (m - 4) = 0 := by
      intro m hm
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 4 := ⟨m - 4, by omega⟩
      rw [show k + 4 - 1 = k + 3 by omega, show k + 4 - 3 = k + 1 by omega,
        show k + 4 - 4 = k by omega, hb (k + 4), hb (k + 3), hb (k + 1), hb k,
        show k + 4 + 1 = k + 5 by omega, show k + 3 + 1 = k + 4 by omega,
        show k + 1 + 1 = k + 2 by omega, hAq (k + 5) (by omega), hAq (k + 4) (by omega),
        hAq (k + 2) (by omega), hAq (k + 1) (by omega)]
      have r1a := pq1 (k + 3)
      have r1b := pq1 (k + 2)
      have r1c := pq1 (k + 1)
      have r2a := pq2 (k + 3)
      have r2b := pq2 (k + 2)
      have r2c := pq2 (k + 1)
      have r3a := pq3 (k + 3)
      have r3b := pq3 (k + 2)
      have r3c := pq3 (k + 1)
      rw [show k + 3 + 2 = k + 5 by omega] at r1a r2a r3a
      rw [show k + 2 + 2 = k + 4 by omega] at r1b r2b r3b
      rw [show k + 1 + 2 = k + 3 by omega] at r1c r2c r3c
      linear_combination r1a - 3 * r1b + 2 * r1c + r2a - 3 * r2b + 2 * r2c +
        r3a - 3 * r3b + 2 * r3c
    have gfb : PowerSeries.mk b *
        ((1 - PowerSeries.X) * (1 - 2 * PowerSeries.X) * (1 - 2 * PowerSeries.X ^ 2)) =
        2 * (4 - 3 * PowerSeries.X - 11 * PowerSeries.X ^ 2 + 6 * PowerSeries.X ^ 3) := by
      have e : PowerSeries.mk b *
          ((1 - PowerSeries.X) * (1 - 2 * PowerSeries.X) * (1 - 2 * PowerSeries.X ^ 2)) =
          PowerSeries.mk b
            - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 3 * (PowerSeries.mk b * PowerSeries.X ^ 1)
            + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 6 * (PowerSeries.mk b * PowerSeries.X ^ 3)
            - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 4 *
              (PowerSeries.mk b * PowerSeries.X ^ 4) := by
        rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 3,
          map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 6,
          map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 4]
        ring
      have e2 : (2 * (4 - 3 * PowerSeries.X - 11 * PowerSeries.X ^ 2 + 6 * PowerSeries.X ^ 3) :
          PowerSeries ℚ) =
          (PowerSeries.C : ℚ →+* PowerSeries ℚ) 8 * PowerSeries.X ^ 0
            - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 6 * PowerSeries.X ^ 1
            - (PowerSeries.C : ℚ →+* PowerSeries ℚ) 22 * PowerSeries.X ^ 2
            + (PowerSeries.C : ℚ →+* PowerSeries ℚ) 12 * PowerSeries.X ^ 3 := by
        rw [map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 8,
          map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 6,
          map_ofNat (PowerSeries.C : ℚ →+* PowerSeries ℚ) 22,
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
          ((1 - PowerSeries.X) * (1 - 2 * PowerSeries.X) * (1 - 2 * PowerSeries.X ^ 2))
        = PowerSeries.X * (PowerSeries.mk b *
          ((1 - PowerSeries.X) * (1 - 2 * PowerSeries.X) * (1 - 2 * PowerSeries.X ^ 2))) := by
          ring
      _ = PowerSeries.X * (2 * (4 - 3 * PowerSeries.X - 11 * PowerSeries.X ^ 2 +
          6 * PowerSeries.X ^ 3)) := by
          rw [gfb]
      _ = 2 * PowerSeries.X * (4 - 3 * PowerSeries.X - 11 * PowerSeries.X ^ 2 +
          6 * PowerSeries.X ^ 3) := by
          ring
  · intro n hn hev
    obtain ⟨k, rfl⟩ := hev
    have hk : 1 ≤ 2 * k := by omega
    rw [show (k + k) / 2 = k by omega, show k + k = 2 * k by ring, hAd (2 * k), hAq (2 * k) hk]
    have w1 : (P1 (2 * k) : ℚ) = 3 * 2 ^ k := by exact_mod_cast (wform P1 iP1 tP1 pP1).1 k
    have w2 : (P2 (2 * k) : ℚ) = 3 * 2 ^ k := by exact_mod_cast (wform P2 iP2 tP2 pP2).1 k
    have w3 : (P3 (2 * k) : ℚ) = 3 * 2 ^ k := by exact_mod_cast (wform P3 iP3 tP3 pP3).1 k
    rw [w1, w2, w3]
    ring
  · intro n _ hod
    obtain ⟨k, rfl⟩ := hod
    rw [show (2 * k + 1 + 1) / 2 = k + 1 by omega, hAd (2 * k + 1),
      hAq (2 * k + 1) (by omega)]
    have w1 : (P1 (2 * k + 1) : ℚ) = 4 * 2 ^ k := by
      exact_mod_cast (wform P1 iP1 tP1 pP1).2 k
    have w2 : (P2 (2 * k + 1) : ℚ) = 4 * 2 ^ k := by
      exact_mod_cast (wform P2 iP2 tP2 pP2).2 k
    have w3 : (P3 (2 * k + 1) : ℚ) = 4 * 2 ^ k := by
      exact_mod_cast (wform P3 iP3 tP3 pP3).2 k
    rw [w1, w2, w3]
    ring
