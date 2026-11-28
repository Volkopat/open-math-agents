import OMAStatements.S_oeis_a202194

-- Problem: A202194: Number of (n+2)X(n+2) binary arrays avoiding patterns 001 and 101 in rows and columns.
-- Upstream: formal-conjectures statements/oeis-a202194.lean:0 (declaration OMA.S_oeis_a202194.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: a word w of length k+1 avoids 001 and 101 iff its tail w(1), ..., w(k) is
-- non-increasing (AntiW). So an array M of size k+1 is counted iff its corner M 0 0 is free, the
-- tail of row 0 and the tail of column 0 are non-increasing, and the k X k block
-- (M (i+1) (j+1)) is non-increasing in both indices (FerM, a Ferrers matrix). This is a
-- bijection with Fin 2 x ferS 1 k x ferS 1 k x ferS k k. Ferrers r X s matrices number
-- C(r+s, r): either the first row is all ones (remove it) or the last column is all zeros
-- (remove it), so the count satisfies the Pascal recurrence. Hence the count is
-- 2 (k+1)^2 C(2k, k), and with k = n+1 this is 4 (n+2)^2 (2n+1)!/(n! (n+1)!).

namespace P1A202194

open OMA.S_oeis_a202194

theorem f2le1 : ∀ x : Fin 2, x ≤ 1 := by decide

theorem f2ge0 : ∀ x : Fin 2, 0 ≤ x := by decide

theorem f2ge1 : ∀ x : Fin 2, 1 ≤ x → x = 1 := by decide

theorem f2le0 : ∀ x : Fin 2, x ≤ 0 → x = 0 := by decide

theorem f2ne1 : ∀ x : Fin 2, x ≠ 1 → x = 0 := by decide

theorem f2key : ∀ x y z : Fin 2, ¬ (x = 0 ∧ y = 0 ∧ z = 1) → ¬ (x = 1 ∧ y = 0 ∧ z = 1) →
    z ≤ y := by
  decide

theorem f2key' : ∀ x y z : Fin 2, z ≤ y →
    ¬ (x = 0 ∧ y = 0 ∧ z = 1) ∧ ¬ (x = 1 ∧ y = 0 ∧ z = 1) := by
  decide

/-- The word t is non-increasing, tested on consecutive positions. -/
def AntiW {k : ℕ} (t : Fin k → Fin 2) : Prop :=
  ∀ p q : Fin k, (q : ℕ) = (p : ℕ) + 1 → t q ≤ t p

/-- A Ferrers 0/1 matrix: non-increasing in both indices. -/
def FerM {r s : ℕ} (N : Fin r → Fin s → Fin 2) : Prop :=
  ∀ i i' : Fin r, ∀ j j' : Fin s, i ≤ i' → j ≤ j' → N i' j' ≤ N i j

instance {r s : ℕ} (N : Fin r → Fin s → Fin 2) : Decidable (FerM N) := by
  unfold FerM
  infer_instance

/-- The Ferrers r X s matrices. -/
def ferS (r s : ℕ) : Finset (Fin r → Fin s → Fin 2) :=
  Finset.univ.filter (fun N => FerM N)

theorem memFer {r s : ℕ} (N : Fin r → Fin s → Fin 2) : N ∈ ferS r s ↔ FerM N :=
  ⟨fun h => (Finset.mem_filter.mp h).2, fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ N, h⟩⟩

theorem avoids_iff {k : ℕ} (w : Fin (k + 1) → Fin 2) : Avoids w ↔ AntiW (Fin.tail w) := by
  constructor
  · intro h p q hpq
    have h3 := h p.castSucc p.succ q.succ rfl (by rw [Fin.val_succ, Fin.val_castSucc]; omega)
    exact f2key (w p.castSucc) (w p.succ) (w q.succ) h3.1 h3.2
  · intro h i j l hj hl
    cases j using Fin.cases with
    | zero =>
      rw [Fin.val_zero] at hj
      exact absurd hj (by omega)
    | succ j' =>
      cases l using Fin.cases with
      | zero =>
        rw [Fin.val_zero] at hl
        exact absurd hl (by omega)
      | succ l' =>
        have hjl : (l' : ℕ) = (j' : ℕ) + 1 := by
          rw [Fin.val_succ] at hj hl
          omega
        exact f2key' (w i) (w j'.succ) (w l'.succ) (h j' l' hjl)

theorem mono_le {k : ℕ} {t : Fin k → Fin 2} (h : AntiW t) :
    ∀ d : ℕ, ∀ p q : Fin k, (q : ℕ) = (p : ℕ) + d → t q ≤ t p
  | 0, p, q, hpq => le_of_eq (congrArg t (Fin.ext hpq))
  | d + 1, p, q, hpq => by
    have hq := q.isLt
    exact le_trans (h ⟨(q : ℕ) - 1, by omega⟩ q (by show (q : ℕ) = (q : ℕ) - 1 + 1; omega))
      (mono_le h d p ⟨(q : ℕ) - 1, by omega⟩ (by show (q : ℕ) - 1 = (p : ℕ) + d; omega))

theorem mono_le' {k : ℕ} {t : Fin k → Fin 2} (h : AntiW t) (p q : Fin k) (hpq : p ≤ q) :
    t q ≤ t p := by
  have h' := Fin.le_iff_val_le_val.mp hpq
  exact mono_le h ((q : ℕ) - (p : ℕ)) p q (by omega)

theorem mono_fin1 (u : Fin 1 → Fin 2) : AntiW u := by
  intro p q hpq
  have hp := p.isLt
  have hq := q.isLt
  exact absurd hpq (by omega)

theorem fer_iff {r s : ℕ} (N : Fin r → Fin s → Fin 2) :
    FerM N ↔ (∀ i, AntiW (N i)) ∧ ∀ j, AntiW (fun i => N i j) := by
  constructor
  · intro h
    refine ⟨fun i p q hpq => h i i p q le_rfl (Fin.le_iff_val_le_val.mpr (by omega)),
      fun j p q hpq => h p q j j (Fin.le_iff_val_le_val.mpr (by omega)) le_rfl⟩
  · rintro ⟨h1, h2⟩ i i' j j' hi hj
    exact le_trans (mono_le' (h1 i') j j' hj) (mono_le' (h2 j) i i' hi)

theorem fer1 {k : ℕ} {t : Fin k → Fin 2} (h : AntiW t) : FerM (fun _ : Fin 1 => t) :=
  (fer_iff (fun _ : Fin 1 => t)).mpr ⟨fun _ => h, fun j => mono_fin1 (fun _ => t j)⟩

theorem fer0 (s : ℕ) : (ferS 0 s).card = 1 := by
  rw [Finset.card_eq_one]
  refine ⟨fun i => Fin.elim0 i, ?_⟩
  ext N
  rw [Finset.mem_singleton, memFer]
  constructor
  · intro _
    funext i
    exact Fin.elim0 i
  · intro _
    unfold FerM
    intro i
    exact Fin.elim0 i

theorem ferB0 (r : ℕ) : (ferS r 0).card = 1 := by
  rw [Finset.card_eq_one]
  refine ⟨fun _ j => Fin.elim0 j, ?_⟩
  ext N
  rw [Finset.mem_singleton, memFer]
  constructor
  · intro _
    funext i j
    exact Fin.elim0 j
  · intro _
    unfold FerM
    intro i i' j
    exact Fin.elim0 j

theorem ferSplit1 (r s : ℕ) :
    ((ferS (r + 1) (s + 1)).filter (fun N => N 0 (Fin.last s) = 1)).card =
      (ferS r (s + 1)).card := by
  refine Finset.card_bij' (fun (N : Fin (r + 1) → Fin (s + 1) → Fin 2) _ => Fin.tail N)
    (fun (N' : Fin r → Fin (s + 1) → Fin 2) _ =>
      (Fin.cons (fun _ => (1 : Fin 2)) N' : Fin (r + 1) → Fin (s + 1) → Fin 2)) ?_ ?_ ?_ ?_
  · intro N hN
    have hF := (memFer N).mp (Finset.mem_filter.mp hN).1
    exact (memFer _).mpr (fun i i' j j' hi hj =>
      hF i.succ i'.succ j j' (Fin.succ_le_succ_iff.mpr hi) hj)
  · intro N' hN'
    have hF := (memFer N').mp hN'
    refine Finset.mem_filter.mpr ⟨(memFer _).mpr ?_, ?_⟩
    · intro i i' j j' hi hj
      cases i using Fin.cases with
      | zero =>
        simp only [Fin.cons_zero]
        exact f2le1 _
      | succ i =>
        cases i' using Fin.cases with
        | zero => exact absurd (Fin.le_zero_iff.mp hi) (Fin.succ_ne_zero i)
        | succ i' =>
          simp only [Fin.cons_succ]
          exact hF i i' j j' (Fin.succ_le_succ_iff.mp hi) hj
    · simp only [Fin.cons_zero]
  · intro N hN
    obtain ⟨hs, h1⟩ := Finset.mem_filter.mp hN
    have hF := (memFer N).mp hs
    have h0 : N 0 = fun _ => (1 : Fin 2) := by
      funext j
      have hle := hF 0 0 j (Fin.last s) le_rfl (Fin.le_last j)
      rw [h1] at hle
      exact f2ge1 _ hle
    show (Fin.cons (fun _ => (1 : Fin 2)) (Fin.tail N) : Fin (r + 1) → Fin (s + 1) → Fin 2) = N
    rw [← h0]
    exact Fin.cons_self_tail N
  · intro N' _
    exact Fin.tail_cons _ _

theorem ferSplit2 (r s : ℕ) :
    ((ferS (r + 1) (s + 1)).filter (fun N => ¬ N 0 (Fin.last s) = 1)).card =
      (ferS (r + 1) s).card := by
  refine Finset.card_bij'
    (fun (N : Fin (r + 1) → Fin (s + 1) → Fin 2) _ =>
      fun (i : Fin (r + 1)) (j : Fin s) => N i (Fin.castSucc j))
    (fun (N'' : Fin (r + 1) → Fin s → Fin 2) _ =>
      fun (i : Fin (r + 1)) (j : Fin (s + 1)) =>
        if h : (j : ℕ) < s then N'' i ⟨(j : ℕ), h⟩ else (0 : Fin 2)) ?_ ?_ ?_ ?_
  · intro N hN
    have hF := (memFer N).mp (Finset.mem_filter.mp hN).1
    exact (memFer _).mpr (fun i i' j j' hi hj =>
      hF i i' j.castSucc j'.castSucc hi (Fin.castSucc_le_castSucc_iff.mpr hj))
  · intro N'' hN''
    have hF := (memFer N'').mp hN''
    refine Finset.mem_filter.mpr ⟨(memFer _).mpr ?_, ?_⟩
    · intro i i' j j' hi hj
      show (if h : (j' : ℕ) < s then N'' i' ⟨(j' : ℕ), h⟩ else (0 : Fin 2)) ≤
        (if h : (j : ℕ) < s then N'' i ⟨(j : ℕ), h⟩ else (0 : Fin 2))
      by_cases hj' : (j' : ℕ) < s
      · have hjb : (j : ℕ) < s := lt_of_le_of_lt (Fin.le_iff_val_le_val.mp hj) hj'
        rw [dif_pos hj', dif_pos hjb]
        exact hF i i' ⟨(j : ℕ), hjb⟩ ⟨(j' : ℕ), hj'⟩ hi
          (Fin.mk_le_mk.mpr (Fin.le_iff_val_le_val.mp hj))
      · rw [dif_neg hj']
        exact f2ge0 _
    · have hl : ¬ ((Fin.last s : Fin (s + 1)) : ℕ) < s := lt_irrefl s
      show ¬ ((if h : ((Fin.last s : Fin (s + 1)) : ℕ) < s then N'' 0 ⟨_, h⟩
        else (0 : Fin 2)) = 1)
      rw [dif_neg hl]
      decide
  · intro N hN
    obtain ⟨hs, h1⟩ := Finset.mem_filter.mp hN
    have hF := (memFer N).mp hs
    funext i j
    show (if h : (j : ℕ) < s then N i (Fin.castSucc ⟨(j : ℕ), h⟩) else (0 : Fin 2)) = N i j
    by_cases hj : (j : ℕ) < s
    · exact (dif_pos hj).trans (congrArg (N i) (Fin.ext rfl))
    · rw [dif_neg hj]
      have hjl : j = Fin.last s := Fin.ext (by
        rw [Fin.val_last]
        have := j.isLt
        omega)
      subst hjl
      have h00 : N 0 (Fin.last s) = 0 := f2ne1 _ h1
      have hle := hF 0 i (Fin.last s) (Fin.last s) (Fin.zero_le i) le_rfl
      rw [h00] at hle
      exact (f2le0 _ hle).symm
  · intro N'' _
    funext i j
    exact (dif_pos (show ((Fin.castSucc j : Fin (s + 1)) : ℕ) < s from j.isLt)).trans rfl

theorem ferSplit (r s : ℕ) :
    (ferS (r + 1) (s + 1)).card = (ferS r (s + 1)).card + (ferS (r + 1) s).card := by
  rw [← Finset.card_filter_add_card_filter_not (s := ferS (r + 1) (s + 1))
    (fun N => N 0 (Fin.last s) = 1), ferSplit1, ferSplit2]

theorem ferCard (r : ℕ) : ∀ s : ℕ, (ferS r s).card = (r + s).choose r := by
  induction r with
  | zero =>
    intro s
    rw [fer0 s, Nat.zero_add, Nat.choose_zero_right]
  | succ r ihr =>
    intro s
    induction s with
    | zero => rw [ferB0 (r + 1), Nat.add_zero, Nat.choose_self]
    | succ s ihs =>
      rw [ferSplit r s, ihr (s + 1), ihs, show r + (s + 1) = r + s + 1 by omega,
        show r + 1 + s = r + s + 1 by omega, show r + 1 + (s + 1) = r + s + 1 + 1 by omega]
      exact (Nat.choose_succ_succ' (r + s + 1) r).symm

theorem good_iff {k : ℕ} (M : Fin (k + 1) → Fin (k + 1) → Fin 2) :
    Good M ↔ AntiW (Fin.tail (M 0)) ∧ AntiW (Fin.tail (fun r => M r 0)) ∧
      FerM (fun i j : Fin k => M i.succ j.succ) := by
  unfold Good
  constructor
  · rintro ⟨hr, hc⟩
    exact ⟨(avoids_iff (M 0)).mp (hr 0), (avoids_iff (fun r => M r 0)).mp (hc 0),
      (fer_iff (fun i j : Fin k => M i.succ j.succ)).mpr
        ⟨fun i => (avoids_iff (M i.succ)).mp (hr i.succ),
          fun j => (avoids_iff (fun r => M r j.succ)).mp (hc j.succ)⟩⟩
  · rintro ⟨h1, h2, h3⟩
    obtain ⟨h4, h5⟩ := (fer_iff (fun i j : Fin k => M i.succ j.succ)).mp h3
    refine ⟨fun r => ?_, fun c => ?_⟩
    · cases r using Fin.cases with
      | zero => exact (avoids_iff (M 0)).mpr h1
      | succ r => exact (avoids_iff (M r.succ)).mpr (h4 r)
    · cases c using Fin.cases with
      | zero => exact (avoids_iff (fun r => M r 0)).mpr h2
      | succ c => exact (avoids_iff (fun r => M r c.succ)).mpr (h5 c)

/-- The array with corner c, row 0 tail T 0, column 0 tail L 0 and inner block N. -/
def build {k : ℕ} (c : Fin 2) (T L : Fin 1 → Fin k → Fin 2) (N : Fin k → Fin k → Fin 2) :
    Fin (k + 1) → Fin (k + 1) → Fin 2 :=
  Fin.cons (Fin.cons c (T 0) : Fin (k + 1) → Fin 2)
    (fun i => (Fin.cons (L 0 i) (N i) : Fin (k + 1) → Fin 2))

theorem b00 {k : ℕ} (c : Fin 2) (T L : Fin 1 → Fin k → Fin 2) (N : Fin k → Fin k → Fin 2) :
    build c T L N 0 0 = c := by
  simp only [build, Fin.cons_zero]

theorem b0s {k : ℕ} (c : Fin 2) (T L : Fin 1 → Fin k → Fin 2) (N : Fin k → Fin k → Fin 2)
    (j : Fin k) : build c T L N 0 j.succ = T 0 j := by
  simp only [build, Fin.cons_zero, Fin.cons_succ]

theorem bs0 {k : ℕ} (c : Fin 2) (T L : Fin 1 → Fin k → Fin 2) (N : Fin k → Fin k → Fin 2)
    (i : Fin k) : build c T L N i.succ 0 = L 0 i := by
  simp only [build, Fin.cons_zero, Fin.cons_succ]

theorem bss {k : ℕ} (c : Fin 2) (T L : Fin 1 → Fin k → Fin 2) (N : Fin k → Fin k → Fin 2)
    (i j : Fin k) : build c T L N i.succ j.succ = N i j := by
  simp only [build, Fin.cons_succ]

theorem good_card (k : ℕ) :
    (Finset.univ.filter (fun M : Fin (k + 1) → Fin (k + 1) → Fin 2 => Good M)).card =
      2 * (k + 1) * (k + 1) * (k + k).choose k := by
  have e : (Finset.univ.filter (fun M : Fin (k + 1) → Fin (k + 1) → Fin 2 => Good M)).card =
      ((Finset.univ : Finset (Fin 2)) ×ˢ (ferS 1 k ×ˢ (ferS 1 k ×ˢ ferS k k))).card := by
    refine Finset.card_bij'
      (fun (M : Fin (k + 1) → Fin (k + 1) → Fin 2) _ =>
        (M 0 0, ((fun _ => Fin.tail (M 0)) : Fin 1 → Fin k → Fin 2),
          ((fun _ => Fin.tail (fun r => M r 0)) : Fin 1 → Fin k → Fin 2),
          ((fun i j => M i.succ j.succ) : Fin k → Fin k → Fin 2)))
      (fun (x : Fin 2 × (Fin 1 → Fin k → Fin 2) × (Fin 1 → Fin k → Fin 2) ×
          (Fin k → Fin k → Fin 2)) _ => build x.1 x.2.1 x.2.2.1 x.2.2.2) ?_ ?_ ?_ ?_
    · intro M hM
      obtain ⟨h1, h2, h3⟩ := (good_iff M).mp (Finset.mem_filter.mp hM).2
      exact Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_product.mpr
        ⟨(memFer _).mpr (fer1 h1), Finset.mem_product.mpr
          ⟨(memFer _).mpr (fer1 h2), (memFer _).mpr h3⟩⟩⟩
    · rintro ⟨c, T, L, N⟩ hx
      obtain ⟨-, hx1⟩ := Finset.mem_product.mp hx
      obtain ⟨hT, hx2⟩ := Finset.mem_product.mp hx1
      obtain ⟨hL, hN⟩ := Finset.mem_product.mp hx2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, (good_iff _).mpr ⟨?_, ?_, ?_⟩⟩
      · have e1 : Fin.tail (build c T L N 0) = T 0 := funext (fun j => b0s c T L N j)
        exact (congrArg AntiW e1).mpr (((fer_iff T).mp ((memFer T).mp hT)).1 0)
      · have e2 : Fin.tail (fun r => build c T L N r 0) = L 0 :=
          funext (fun i => bs0 c T L N i)
        exact (congrArg AntiW e2).mpr (((fer_iff L).mp ((memFer L).mp hL)).1 0)
      · have e3 : (fun i j : Fin k => build c T L N i.succ j.succ) = N :=
          funext (fun i => funext (fun j => bss c T L N i j))
        exact (congrArg FerM e3).mpr ((memFer N).mp hN)
    · intro M _
      funext i j
      cases i using Fin.cases with
      | zero =>
        cases j using Fin.cases with
        | zero => exact b00 _ _ _ _
        | succ j => exact b0s _ _ _ _ j
      | succ i =>
        cases j using Fin.cases with
        | zero => exact bs0 _ _ _ _ i
        | succ j => exact bss _ _ _ _ i j
    · rintro ⟨c, T, L, N⟩ _
      refine Prod.ext (b00 c T L N) (Prod.ext ?_ (Prod.ext ?_ ?_))
      · funext u j
        have hu : u = 0 := Subsingleton.elim u 0
        subst hu
        exact b0s c T L N j
      · funext u i
        have hu : u = 0 := Subsingleton.elim u 0
        subst hu
        exact bs0 c T L N i
      · funext i j
        exact bss c T L N i j
  rw [e, Finset.card_product, Finset.card_product, Finset.card_product, Finset.card_univ,
    Fintype.card_fin, ferCard 1 k, ferCard k k, Nat.choose_one_right]
  ring

end P1A202194

open OMA.S_oeis_a202194 P1A202194 in
theorem OMA.solution : type_of% @OMA.S_oeis_a202194.main := by
  intro n _
  have hcard : a n = 2 * (n + 1 + 1) * (n + 1 + 1) * (n + 1 + (n + 1)).choose (n + 1) :=
    good_card (n + 1)
  obtain ⟨C, hCdef⟩ : ∃ C : ℕ, C = (n + 1 + (n + 1)).choose (n + 1) := ⟨_, rfl⟩
  rw [← hCdef] at hcard
  have hC := Nat.add_choose_mul_factorial_mul_factorial (n + 1) (n + 1)
  rw [← hCdef, show n + 1 + (n + 1) = 2 * n + 1 + 1 by omega,
    Nat.factorial_succ (2 * n + 1)] at hC
  have hF1 := Nat.factorial_succ n
  have hCq : (C : ℚ) * ((n + 1).factorial : ℚ) * ((n + 1).factorial : ℚ) =
      (2 * (n : ℚ) + 1 + 1) * ((2 * n + 1).factorial : ℚ) := by
    exact_mod_cast hC
  have hF1q : ((n + 1).factorial : ℚ) = ((n : ℚ) + 1) * (n.factorial : ℚ) := by
    exact_mod_cast hF1
  have haq : (a n : ℚ) = 2 * ((n : ℚ) + 1 + 1) * ((n : ℚ) + 1 + 1) * (C : ℚ) := by
    exact_mod_cast hcard
  have hkey : ((n : ℚ) + 1) * ((C : ℚ) * (n.factorial : ℚ) * ((n + 1).factorial : ℚ)) =
      ((n : ℚ) + 1) * (2 * ((2 * n + 1).factorial : ℚ)) := by
    linear_combination hCq - (C : ℚ) * ((n + 1).factorial : ℚ) * hF1q
  have hkey2 := mul_left_cancel₀ (by positivity : ((n : ℚ) + 1) ≠ 0) hkey
  rw [eq_div_iff (by positivity)]
  linear_combination ((n.factorial : ℚ) * ((n + 1).factorial : ℚ)) * haq +
    2 * ((n : ℚ) + 2) ^ 2 * hkey2
