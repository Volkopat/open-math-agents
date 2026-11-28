import OMAStatements.S_oeis_a208285

-- Problem: oeis-a208285
-- Transfer-matrix proof: rows are states, triples of consecutive rows are transitions;
-- the kernel checks the vector recurrence on the table of extension counts.

namespace OMA.Arr

section Gen
variable {α : Type} [Fintype α] [DecidableEq α]

def Valid (H : α → Prop) (V : α → α → α → Prop) (n : ℕ) (s : Fin n → α) : Prop :=
  (∀ i : Fin n, H (s i)) ∧
    ∀ (i : ℕ) (h : i + 1 + 1 < n),
      V (s ⟨i, by omega⟩) (s ⟨i + 1, by omega⟩) (s ⟨i + 1 + 1, h⟩)

theorem cons_mk_zero {n : ℕ} (a : α) (f : Fin n → α) (h : 0 < n + 1) :
    (Fin.cons a f : Fin (n + 1) → α) ⟨0, h⟩ = a := rfl

theorem cons_mk_succ {n : ℕ} (a : α) (f : Fin n → α) (i : ℕ) (h : i + 1 < n + 1) :
    (Fin.cons a f : Fin (n + 1) → α) ⟨i + 1, h⟩ = f ⟨i, by omega⟩ := rfl

theorem valid_two (H : α → Prop) (V : α → α → α → Prop) (u v : α) (t : Fin 0 → α) :
    Valid H V 2 (Fin.cons u (Fin.cons v t)) ↔ H u ∧ H v := by
  constructor
  · intro h
    exact ⟨h.1 0, h.1 1⟩
  · intro h
    refine ⟨fun i => ?_, fun i hi => absurd hi (by omega)⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · exact h.1
    · have : j = 0 := Subsingleton.elim _ _
      subst this
      exact h.2

theorem valid_succ (H : α → Prop) (V : α → α → α → Prop) (m : ℕ) (u v w : α)
    (t : Fin m → α) :
    Valid H V (m + 3) (Fin.cons u (Fin.cons v (Fin.cons w t))) ↔
      H u ∧ V u v w ∧ Valid H V (m + 2) (Fin.cons v (Fin.cons w t)) := by
  constructor
  · intro h
    refine ⟨h.1 0, ?_, fun i => h.1 i.succ, fun i hi => ?_⟩
    · have h0 := h.2 0 (by omega)
      rw [cons_mk_zero, cons_mk_succ, cons_mk_succ, cons_mk_zero, cons_mk_succ, cons_mk_zero] at h0
      exact h0
    · have h1 := h.2 (i + 1) (by omega)
      rw [cons_mk_succ, cons_mk_succ, cons_mk_succ] at h1
      exact h1
  · intro h
    refine ⟨fun i => ?_, fun i hi => ?_⟩
    · refine Fin.cases ?_ (fun j => ?_) i
      · exact h.1
      · exact h.2.2.1 j
    · cases i with
      | zero =>
        rw [cons_mk_zero, cons_mk_succ, cons_mk_succ, cons_mk_zero, cons_mk_succ, cons_mk_zero]
        exact h.2.1
      | succ i =>
        rw [cons_mk_succ, cons_mk_succ, cons_mk_succ]
        exact h.2.2.2 i (by omega)

variable (H : α → Prop) (V : α → α → α → Prop) [DecidablePred H]
  [∀ u v w, Decidable (V u v w)] [∀ (n : ℕ) (s : Fin n → α), Decidable (Valid H V n s)]

def F : ℕ → α → α → ℤ
  | 0, u, v => if H u ∧ H v then 1 else 0
  | m + 1, u, v => if H u then ∑ w, (if V u v w then F m v w else 0) else 0

theorem sum_valid : ∀ (m : ℕ) (u v : α),
    (∑ t : Fin m → α, if Valid H V (m + 2) (Fin.cons u (Fin.cons v t)) then (1 : ℤ) else 0)
      = F H V m u v := by
  intro m
  induction m with
  | zero =>
    intro u v
    simp only [F]
    rw [Fintype.sum_unique]
    exact if_congr (valid_two H V u v _) rfl rfl
  | succ m ih =>
    intro u v
    rw [← (Fin.consEquiv (fun _ : Fin (m + 1) => α)).sum_comp, Fintype.sum_prod_type]
    simp only [F]
    have key : ∀ (w : α) (t : Fin m → α),
        Valid H V (m + 1 + 2) (Fin.cons u (Fin.cons v
          ((Fin.consEquiv (fun _ : Fin (m + 1) => α)) (w, t)))) ↔
        H u ∧ V u v w ∧ Valid H V (m + 2) (Fin.cons v (Fin.cons w t)) :=
      fun w t => valid_succ H V m u v w t
    simp only [key]
    by_cases hu : H u
    · rw [if_pos hu]
      refine Finset.sum_congr rfl fun w _ => ?_
      by_cases hv : V u v w
      · rw [if_pos hv, ← ih v w]
        refine Finset.sum_congr rfl fun t _ => ?_
        simp [hu, hv]
      · rw [if_neg hv]
        refine Finset.sum_eq_zero fun t _ => ?_
        simp [hv]
    · rw [if_neg hu]
      refine Finset.sum_eq_zero fun w _ => Finset.sum_eq_zero fun t _ => ?_
      simp [hu]

theorem card_valid (m : ℕ) :
    (((Finset.univ : Finset (Fin (m + 2) → α)).filter (fun s => Valid H V (m + 2) s)).card : ℤ)
      = ∑ u, ∑ v, F H V m u v := by
  rw [Finset.card_filter]
  push_cast
  rw [← (Fin.consEquiv (fun _ : Fin (m + 2) => α)).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← (Fin.consEquiv (fun _ : Fin (m + 1) => α)).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [← sum_valid H V m u v]
  rfl

def G (rows : List α) : ℕ → α → α → ℤ
  | 0, _, _ => 1
  | m + 1, u, v => (rows.map (fun w => if V u v w then G rows m v w else 0)).sum

theorem sum_rows (rows : List α) (hN : rows.Nodup) (hH : ∀ u, H u ↔ u ∈ rows) (f : α → ℤ) :
    (∑ w, if H w then f w else 0) = (rows.map f).sum := by
  rw [← List.sum_toFinset f hN, ← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext w
  simp [hH]

theorem F_eq (rows : List α) (hN : rows.Nodup) (hH : ∀ u, H u ↔ u ∈ rows) :
    ∀ (m : ℕ) (u v : α), F H V m u v = if H u ∧ H v then G V rows m u v else 0 := by
  intro m
  induction m with
  | zero => intro u v; simp [F, G]
  | succ m ih =>
    intro u v
    simp only [F, G]
    by_cases hu : H u
    · by_cases hv : H v
      · rw [if_pos hu, if_pos ⟨hu, hv⟩, ← sum_rows H rows hN hH]
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [ih v w]
        by_cases hw : H w <;> simp [hv, hw]
      · rw [if_pos hu, if_neg (fun h => hv h.2)]
        refine Finset.sum_eq_zero fun w _ => ?_
        rw [ih v w]
        simp [hv]
    · rw [if_neg hu, if_neg (fun h => hu h.1)]

def C (rows : List α) (m : ℕ) : ℤ :=
  (rows.map (fun u => (rows.map (fun v => G V rows m u v)).sum)).sum

theorem card_eq_C (rows : List α) (hN : rows.Nodup) (hH : ∀ u, H u ↔ u ∈ rows) (m : ℕ) :
    (((Finset.univ : Finset (Fin (m + 2) → α)).filter (fun s => Valid H V (m + 2) s)).card : ℤ)
      = C V rows m := by
  rw [card_valid, C, ← sum_rows H rows hN hH]
  refine Finset.sum_congr rfl fun u _ => ?_
  by_cases hu : H u
  · rw [if_pos hu, ← sum_rows H rows hN hH]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [F_eq H V rows hN hH]
    by_cases hv : H v <;> simp [hu, hv]
  · rw [if_neg hu]
    refine Finset.sum_eq_zero fun v _ => ?_
    rw [F_eq H V rows hN hH]
    simp [hu]

theorem card_one (rows : List α) (hN : rows.Nodup) (hH : ∀ u, H u ↔ u ∈ rows) :
    (((Finset.univ : Finset (Fin 1 → α)).filter (fun s => Valid H V 1 s)).card : ℤ)
      = rows.length := by
  rw [Finset.card_filter]
  push_cast
  rw [← (Equiv.funUnique (Fin 1) α).symm.sum_comp]
  have : ∀ u : α, Valid H V 1 ((Equiv.funUnique (Fin 1) α).symm u) ↔ H u := by
    intro u
    constructor
    · intro h; exact h.1 0
    · intro h; exact ⟨fun _ => h, fun i hi => absurd hi (by omega)⟩
  simp only [this]
  rw [sum_rows H rows hN hH]
  simp

end Gen
end OMA.Arr

namespace OMA.Arr

section Tab
variable {α : Type} (V : α → α → α → Prop) [∀ u v w, Decidable (V u v w)] (rows : List α)

theorem zipWith_map_self {β γ : Type} (f : α → β → γ) (g : α → β) (l : List α) :
    List.zipWith f l (l.map g) = l.map (fun a => f a (g a)) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem zipWith_map_map {β γ δ : Type} (f : β → γ → δ) (g : α → β) (h : α → γ) (l : List α) :
    List.zipWith f (l.map g) (l.map h) = l.map (fun a => f (g a) (h a)) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem sum_lin (P : α → Prop) [DecidablePred P] (a : ℤ) (f g : α → ℤ) (l : List α) :
    (l.map (fun w => if P w then a * f w + g w else 0)).sum
      = a * (l.map (fun w => if P w then f w else 0)).sum
        + (l.map (fun w => if P w then g w else 0)).sum := by
  induction l with
  | nil => simp
  | cons b l ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    split_ifs <;> ring

theorem sum_lin2 (a : ℤ) (f g : α → ℤ) (l : List α) :
    (l.map (fun w => a * f w + g w)).sum = a * (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => simp
  | cons b l ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    ring

def step (T : List (List ℤ)) : List (List ℤ) :=
  rows.map (fun u => List.zipWith
    (fun v gv => (List.zipWith (fun w x => if V u v w then x else 0) rows gv).sum) rows T)

def tab : ℕ → List (List ℤ)
  | 0 => rows.map (fun _ => rows.map (fun _ => 1))
  | m + 1 => step V rows (tab m)

theorem tab_eq : ∀ m : ℕ,
    tab V rows m = rows.map (fun u => rows.map (fun v => G V rows m u v)) := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [tab, ih, step]
    refine List.map_congr_left fun u _ => ?_
    rw [zipWith_map_self]
    refine List.map_congr_left fun v _ => ?_
    rw [zipWith_map_self]
    rfl

theorem C_eq_tab (m : ℕ) : C V rows m = ((tab V rows m).map List.sum).sum := by
  rw [tab_eq, C, List.map_map]
  rfl

def comb : List ℤ → ℕ → α → α → ℤ
  | [], _, _, _ => 0
  | a :: q, m, u, v => a * G V rows m u v + comb q (m + 1) u v

theorem comb_succ : ∀ (q : List ℤ) (m : ℕ) (u v : α),
    comb V rows q (m + 1) u v
      = (rows.map (fun w => if V u v w then comb V rows q m v w else 0)).sum := by
  intro q
  induction q with
  | nil => intro m u v; simp [comb]
  | cons a q ih =>
    intro m u v
    simp only [comb]
    rw [sum_lin, ← ih (m + 1) u v]
    rfl

theorem comb_zero (q : List ℤ)
    (h0 : ∀ u ∈ rows, ∀ v ∈ rows, comb V rows q 0 u v = 0) :
    ∀ (m : ℕ), ∀ u ∈ rows, ∀ v ∈ rows, comb V rows q m u v = 0 := by
  intro m
  induction m with
  | zero => exact h0
  | succ m ih =>
    intro u _ v hv
    rw [comb_succ]
    refine List.sum_eq_zero ?_
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨w, hw, rfl⟩ := hx
    rw [ih v hv w hw]
    simp

def combC : List ℤ → ℕ → ℤ
  | [], _ => 0
  | a :: q, m => a * C V rows m + combC q (m + 1)

theorem combC_eq : ∀ (q : List ℤ) (m : ℕ),
    combC V rows q m
      = (rows.map (fun u => (rows.map (fun v => comb V rows q m u v)).sum)).sum := by
  intro q
  induction q with
  | nil => intro m; simp [combC, comb]
  | cons a q ih =>
    intro m
    simp only [combC, comb, ih, C]
    rw [← sum_lin2]
    refine congrArg List.sum (List.map_congr_left fun u _ => ?_)
    rw [sum_lin2]

def combT : List ℤ → List (List ℤ) → List (List ℤ)
  | [], _ => rows.map (fun _ => rows.map (fun _ => 0))
  | a :: q, T => List.zipWith (List.zipWith (fun x y => a * x + y)) T (combT q (step V rows T))

theorem combT_eq : ∀ (q : List ℤ) (m : ℕ),
    combT V rows q (tab V rows m)
      = rows.map (fun u => rows.map (fun v => comb V rows q m u v)) := by
  intro q
  induction q with
  | nil => intro m; rfl
  | cons a q ih =>
    intro m
    rw [combT, show step V rows (tab V rows m) = tab V rows (m + 1) from rfl, ih, tab_eq,
      zipWith_map_map]
    refine List.map_congr_left fun u _ => ?_
    rw [zipWith_map_map]
    rfl

theorem rec_C (q : List ℤ)
    (hchk : combT V rows q (tab V rows 0) = rows.map (fun _ => rows.map (fun _ => 0))) :
    ∀ m : ℕ, combC V rows q m = 0 := by
  have h0 : ∀ u ∈ rows, ∀ v ∈ rows, comb V rows q 0 u v = 0 := by
    rw [combT_eq] at hchk
    intro u hu v hv
    have h1 := List.map_inj_left.mp hchk u hu
    exact List.map_inj_left.mp h1 v hv
  intro m
  rw [combC_eq]
  refine List.sum_eq_zero ?_
  intro x hx
  rw [List.mem_map] at hx
  obtain ⟨u, hu, rfl⟩ := hx
  refine List.sum_eq_zero ?_
  intro y hy
  rw [List.mem_map] at hy
  obtain ⟨v, hv, rfl⟩ := hy
  exact comb_zero V rows q h0 m u hu v hv

end Tab

section Bridge

def getG {r c : ℕ} (x : Fin r → Fin c → Fin 2) (i j : ℕ) : ℕ :=
  if h : i < r ∧ j < c then (x ⟨i, h.1⟩ ⟨j, h.2⟩ : ℕ) else 0

theorem getG_eq {r c : ℕ} (x : Fin r → Fin c → Fin 2) (i j : ℕ) (hi : i < r) (hj : j < c) :
    getG x i j = (x ⟨i, hi⟩ ⟨j, hj⟩ : ℕ) := dif_pos ⟨hi, hj⟩

def Hrow (p1 p2 : ℕ × ℕ × ℕ) {c : ℕ} (u : Fin c → Fin 2) : Prop :=
  ∀ (j : ℕ) (h : j < c - 2),
    (((u ⟨j, by omega⟩ : Fin 2) : ℕ), ((u ⟨j + 1, by omega⟩ : Fin 2) : ℕ),
      ((u ⟨j + 2, by omega⟩ : Fin 2) : ℕ)) ≠ p1 ∧
    (((u ⟨j, by omega⟩ : Fin 2) : ℕ), ((u ⟨j + 1, by omega⟩ : Fin 2) : ℕ),
      ((u ⟨j + 2, by omega⟩ : Fin 2) : ℕ)) ≠ p2

def Vt (q1 q2 : ℕ × ℕ × ℕ) {c : ℕ} (u v w : Fin c → Fin 2) : Prop :=
  ∀ (j : ℕ) (h : j < c),
    (((u ⟨j, h⟩ : Fin 2) : ℕ), ((v ⟨j, h⟩ : Fin 2) : ℕ), ((w ⟨j, h⟩ : Fin 2) : ℕ)) ≠ q1 ∧
    (((u ⟨j, h⟩ : Fin 2) : ℕ), ((v ⟨j, h⟩ : Fin 2) : ℕ), ((w ⟨j, h⟩ : Fin 2) : ℕ)) ≠ q2

instance (p1 p2 : ℕ × ℕ × ℕ) {c : ℕ} (u : Fin c → Fin 2) : Decidable (Hrow p1 p2 u) :=
  Nat.decidableBallLT _ _

instance (q1 q2 : ℕ × ℕ × ℕ) {c : ℕ} (u v w : Fin c → Fin 2) : Decidable (Vt q1 q2 u v w) :=
  Nat.decidableBallLT _ _

theorem avoid_iff (p1 p2 q1 q2 : ℕ × ℕ × ℕ) {r c : ℕ} (x : Fin r → Fin c → Fin 2) :
    ((∀ i < r, ∀ j < c - 2,
        (getG x i j, getG x i (j + 1), getG x i (j + 2)) ≠ p1 ∧
        (getG x i j, getG x i (j + 1), getG x i (j + 2)) ≠ p2) ∧
      (∀ i < r - 2, ∀ j < c,
        (getG x i j, getG x (i + 1) j, getG x (i + 2) j) ≠ q1 ∧
        (getG x i j, getG x (i + 1) j, getG x (i + 2) j) ≠ q2))
      ↔ Valid (Hrow p1 p2) (Vt q1 q2) r x := by
  constructor
  · intro h
    refine ⟨fun i j hj => ?_, fun i hi j hj => ?_⟩
    · have h1 := h.1 i.val i.isLt j hj
      rw [getG_eq x i.val j i.isLt (by omega), getG_eq x i.val (j + 1) i.isLt (by omega),
        getG_eq x i.val (j + 2) i.isLt (by omega)] at h1
      exact h1
    · have h1 := h.2 i (by omega) j hj
      rw [getG_eq x i j (by omega) hj, getG_eq x (i + 1) j (by omega) hj,
        getG_eq x (i + 2) j (by omega) hj] at h1
      exact h1
  · intro h
    refine ⟨fun i hi j hj => ?_, fun i hi j hj => ?_⟩
    · rw [getG_eq x i j hi (by omega), getG_eq x i (j + 1) hi (by omega),
        getG_eq x i (j + 2) hi (by omega)]
      exact h.1 ⟨i, hi⟩ j hj
    · rw [getG_eq x i j (by omega) hj, getG_eq x (i + 1) j (by omega) hj,
        getG_eq x (i + 2) j (by omega) hj]
      exact h.2 i (by omega) j hj

theorem avoid_iff_swap (p1 p2 q1 q2 : ℕ × ℕ × ℕ) {r c : ℕ} (x : Fin r → Fin c → Fin 2) :
    ((∀ i < r, ∀ j < c - 2,
        (getG x i j, getG x i (j + 1), getG x i (j + 2)) ≠ p1 ∧
        (getG x i j, getG x i (j + 1), getG x i (j + 2)) ≠ p2) ∧
      (∀ i < r - 2, ∀ j < c,
        (getG x i j, getG x (i + 1) j, getG x (i + 2) j) ≠ q1 ∧
        (getG x i j, getG x (i + 1) j, getG x (i + 2) j) ≠ q2))
      ↔ Valid (Hrow q1 q2) (Vt p1 p2) c (fun j i => x i j) := by
  constructor
  · intro h
    refine ⟨fun j i hi => ?_, fun j hj i hi => ?_⟩
    · have h1 := h.2 i hi j.val j.isLt
      rw [getG_eq x i j.val (by omega) j.isLt, getG_eq x (i + 1) j.val (by omega) j.isLt,
        getG_eq x (i + 2) j.val (by omega) j.isLt] at h1
      exact h1
    · have h1 := h.1 i hi j (by omega)
      rw [getG_eq x i j hi (by omega), getG_eq x i (j + 1) hi (by omega),
        getG_eq x i (j + 2) hi (by omega)] at h1
      exact h1
  · intro h
    refine ⟨fun i hi j hj => ?_, fun i hi j hj => ?_⟩
    · rw [getG_eq x i j hi (by omega), getG_eq x i (j + 1) hi (by omega),
        getG_eq x i (j + 2) hi (by omega)]
      exact h.2 j (by omega) i hi
    · rw [getG_eq x i j (by omega) hj, getG_eq x (i + 1) j (by omega) hj,
        getG_eq x (i + 2) j (by omega) hj]
      exact h.1 ⟨j, hj⟩ i hi

end Bridge

end OMA.Arr

namespace OMA.Arr

section Fast
variable {α : Type} (V : α → α → α → Prop) [∀ u v w, Decidable (V u v w)] (rows : List α)

def rowTbl (u : α) : List (List Bool) :=
  rows.map (fun v => rows.map (fun w => decide (V u v w)))

def tblOf : List (List (List Bool)) := rows.map (rowTbl V rows)

def decRow (N : ℕ) (ru : List ℕ) : List (List Bool) :=
  ru.map (fun mask => (List.range N).map (fun i => mask.testBit i))

def dec (N : ℕ) (masks : List (List ℕ)) : List (List (List Bool)) := masks.map (decRow N)

def stepB (tbl : List (List (List Bool))) (T : List (List ℤ)) : List (List ℤ) :=
  tbl.map (fun tu => List.zipWith
    (fun tv gv => (List.zipWith (fun (b : Bool) x => if b then x else 0) tv gv).sum) tu T)

theorem step_eq (tbl : List (List (List Bool))) (htbl : tblOf V rows = tbl)
    (T : List (List ℤ)) : step V rows T = stepB tbl T := by
  subst htbl
  simp only [step, stepB, tblOf, rowTbl, List.map_map, List.zipWith_map_left]
  refine List.map_congr_left fun u _ => ?_
  simp only [Function.comp, rowTbl, List.zipWith_map_left, decide_eq_true_eq]

def iterB (tbl : List (List (List Bool))) : ℕ → List (List ℤ) → List (List ℤ)
  | 0, T => T
  | m + 1, T => stepB tbl (iterB tbl m T)

theorem tab_eqB (tbl : List (List (List Bool))) (htbl : tblOf V rows = tbl) :
    ∀ m : ℕ, tab V rows m = iterB tbl m (rows.map (fun _ => rows.map (fun _ => 1))) := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih => rw [tab, ih, step_eq V rows tbl htbl]; rfl

def combTB (tbl : List (List (List Bool))) (Z : List (List ℤ)) :
    List ℤ → List (List ℤ) → List (List ℤ)
  | [], _ => Z
  | a :: q, T =>
    List.zipWith (List.zipWith (fun x y => a * x + y)) T (combTB tbl Z q (stepB tbl T))

theorem combT_eqB (tbl : List (List (List Bool))) (htbl : tblOf V rows = tbl) :
    ∀ (q : List ℤ) (T : List (List ℤ)),
      combT V rows q T = combTB tbl (rows.map (fun _ => rows.map (fun _ => 0))) q T := by
  intro q
  induction q with
  | nil => intro T; rfl
  | cons a q ih => intro T; rw [combT, combTB, step_eq V rows tbl htbl, ih]

theorem rec_CB (tbl : List (List (List Bool))) (htbl : tblOf V rows = tbl) (q : List ℤ)
    (hchk : combTB tbl (rows.map (fun _ => rows.map (fun _ => 0))) q
      (rows.map (fun _ => rows.map (fun _ => 1))) = rows.map (fun _ => rows.map (fun _ => 0))) :
    ∀ m : ℕ, combC V rows q m = 0 := by
  refine rec_C V rows q ?_
  rw [combT_eqB V rows tbl htbl]
  exact hchk

theorem C_eqB (tbl : List (List (List Bool))) (htbl : tblOf V rows = tbl) (m : ℕ) :
    C V rows m
      = ((iterB tbl m (rows.map (fun _ => rows.map (fun _ => 1)))).map List.sum).sum := by
  rw [C_eq_tab, tab_eqB V rows tbl htbl]

end Fast

end OMA.Arr

namespace OMA.P208285
open OMA.Arr OMA.S_oeis_a208285

def rows : List (Fin 6 → Fin 2) :=
  [![0, 1, 0, 1, 0, 0], ![0, 1, 0, 1, 0, 1], ![0, 1, 0, 1, 1, 0], ![0, 1, 0, 1, 1, 1], ![0, 1, 1, 0, 1, 0], ![0, 1, 1, 0, 1, 1], ![0, 1, 1, 1, 0, 0], ![0, 1, 1, 1, 0, 1], ![0, 1, 1, 1, 1, 0], ![0, 1, 1, 1, 1, 1], ![1, 0, 1, 0, 1, 0], ![1, 0, 1, 0, 1, 1], ![1, 0, 1, 1, 0, 0], ![1, 0, 1, 1, 0, 1], ![1, 0, 1, 1, 1, 0], ![1, 0, 1, 1, 1, 1], ![1, 1, 0, 1, 0, 0], ![1, 1, 0, 1, 0, 1], ![1, 1, 0, 1, 1, 0], ![1, 1, 0, 1, 1, 1], ![1, 1, 1, 0, 1, 0], ![1, 1, 1, 0, 1, 1], ![1, 1, 1, 1, 0, 0], ![1, 1, 1, 1, 0, 1], ![1, 1, 1, 1, 1, 0], ![1, 1, 1, 1, 1, 1]]

theorem hN : rows.Nodup := by decide +kernel

theorem hH : ∀ u : Fin 6 → Fin 2, Hrow (0, 0, 0) (0, 0, 1) u ↔ u ∈ rows := by
  simp only [Fin.forall_fin_succ_pi, Fin.forall_fin_zero_pi]
  decide +kernel

def masks : List (List ℕ) :=
  [[1, 3, 5, 15, 341, 1023, 65, 195, 325, 975, 22369621, 67108863, 4264001, 12792003, 21320005, 63960015, 65537, 196611, 327685, 983055, 22348117, 67044351, 4259905, 12779715, 21299525, 63898575],
   [3, 2, 15, 10, 1023, 682, 195, 130, 975, 650, 67108863, 44739242, 12792003, 8528002, 63960015, 42640010, 196611, 131074, 983055, 655370, 67044351, 44696234, 12779715, 8519810, 63898575, 42599050],
   [5, 15, 4, 12, 276, 828, 325, 975, 260, 780, 18105620, 54316860, 21320005, 63960015, 17056004, 51168012, 327685, 983055, 262148, 786444, 18088212, 54264636, 21299525, 63898575, 17039620, 51118860],
   [15, 10, 12, 8, 828, 552, 975, 650, 780, 520, 54316860, 36211240, 63960015, 42640010, 51168012, 34112008, 983055, 655370, 786444, 524296, 54264636, 36176424, 63898575, 42599050, 51118860, 34079240],
   [341, 1023, 276, 828, 16, 48, 336, 1008, 272, 816, 1049616, 3148848, 22041936, 66125808, 17843472, 53530416, 22348117, 67044351, 18088212, 54264636, 1048592, 3145776, 22020432, 66061296, 17826064, 53478192],
   [1023, 682, 828, 552, 48, 32, 1008, 672, 816, 544, 3148848, 2099232, 66125808, 44083872, 53530416, 35686944, 67044351, 44696234, 54264636, 36176424, 3145776, 2097184, 66061296, 44040864, 53478192, 35652128],
   [65, 195, 325, 975, 336, 1008, 64, 192, 320, 960, 22041936, 66125808, 4198464, 12595392, 20992320, 62976960, 4259905, 12779715, 21299525, 63898575, 22020432, 66061296, 4194368, 12583104, 20971840, 62915520],
   [195, 130, 975, 650, 1008, 672, 192, 128, 960, 640, 66125808, 44083872, 12595392, 8396928, 62976960, 41984640, 12779715, 8519810, 63898575, 42599050, 66061296, 44040864, 12583104, 8388736, 62915520, 41943680],
   [325, 975, 260, 780, 272, 816, 320, 960, 256, 768, 17843472, 53530416, 20992320, 62976960, 16793856, 50381568, 21299525, 63898575, 17039620, 51118860, 17826064, 53478192, 20971840, 62915520, 16777472, 50332416],
   [975, 650, 780, 520, 816, 544, 960, 640, 768, 512, 53530416, 35686944, 62976960, 41984640, 50381568, 33587712, 63898575, 42599050, 51118860, 34079240, 53478192, 35652128, 62915520, 41943680, 50332416, 33554944],
   [22369621, 67108863, 18105620, 54316860, 1049616, 3148848, 22041936, 66125808, 17843472, 53530416, 1024, 3072, 21504, 64512, 17408, 52224, 22369280, 67107840, 18105344, 54316032, 1049600, 3148800, 22041600, 66124800, 17843200, 53529600],
   [67108863, 44739242, 54316860, 36211240, 3148848, 2099232, 66125808, 44083872, 53530416, 35686944, 3072, 2048, 64512, 43008, 52224, 34816, 67107840, 44738560, 54316032, 36210688, 3148800, 2099200, 66124800, 44083200, 53529600, 35686400],
   [4264001, 12792003, 21320005, 63960015, 22041936, 66125808, 4198464, 12595392, 20992320, 62976960, 21504, 64512, 4096, 12288, 20480, 61440, 4263936, 12791808, 21319680, 63959040, 22041600, 66124800, 4198400, 12595200, 20992000, 62976000],
   [12792003, 8528002, 63960015, 42640010, 66125808, 44083872, 12595392, 8396928, 62976960, 41984640, 64512, 43008, 12288, 8192, 61440, 40960, 12791808, 8527872, 63959040, 42639360, 66124800, 44083200, 12595200, 8396800, 62976000, 41984000],
   [21320005, 63960015, 17056004, 51168012, 17843472, 53530416, 20992320, 62976960, 16793856, 50381568, 17408, 52224, 20480, 61440, 16384, 49152, 21319680, 63959040, 17055744, 51167232, 17843200, 53529600, 20992000, 62976000, 16793600, 50380800],
   [63960015, 42640010, 51168012, 34112008, 53530416, 35686944, 62976960, 41984640, 50381568, 33587712, 52224, 34816, 61440, 40960, 49152, 32768, 63959040, 42639360, 51167232, 34111488, 53529600, 35686400, 62976000, 41984000, 50380800, 33587200],
   [65537, 196611, 327685, 983055, 22348117, 67044351, 4259905, 12779715, 21299525, 63898575, 22369280, 67107840, 4263936, 12791808, 21319680, 63959040, 65536, 196608, 327680, 983040, 22347776, 67043328, 4259840, 12779520, 21299200, 63897600],
   [196611, 131074, 983055, 655370, 67044351, 44696234, 12779715, 8519810, 63898575, 42599050, 67107840, 44738560, 12791808, 8527872, 63959040, 42639360, 196608, 131072, 983040, 655360, 67043328, 44695552, 12779520, 8519680, 63897600, 42598400],
   [327685, 983055, 262148, 786444, 18088212, 54264636, 21299525, 63898575, 17039620, 51118860, 18105344, 54316032, 21319680, 63959040, 17055744, 51167232, 327680, 983040, 262144, 786432, 18087936, 54263808, 21299200, 63897600, 17039360, 51118080],
   [983055, 655370, 786444, 524296, 54264636, 36176424, 63898575, 42599050, 51118860, 34079240, 54316032, 36210688, 63959040, 42639360, 51167232, 34111488, 983040, 655360, 786432, 524288, 54263808, 36175872, 63897600, 42598400, 51118080, 34078720],
   [22348117, 67044351, 18088212, 54264636, 1048592, 3145776, 22020432, 66061296, 17826064, 53478192, 1049600, 3148800, 22041600, 66124800, 17843200, 53529600, 22347776, 67043328, 18087936, 54263808, 1048576, 3145728, 22020096, 66060288, 17825792, 53477376],
   [67044351, 44696234, 54264636, 36176424, 3145776, 2097184, 66061296, 44040864, 53478192, 35652128, 3148800, 2099200, 66124800, 44083200, 53529600, 35686400, 67043328, 44695552, 54263808, 36175872, 3145728, 2097152, 66060288, 44040192, 53477376, 35651584],
   [4259905, 12779715, 21299525, 63898575, 22020432, 66061296, 4194368, 12583104, 20971840, 62915520, 22041600, 66124800, 4198400, 12595200, 20992000, 62976000, 4259840, 12779520, 21299200, 63897600, 22020096, 66060288, 4194304, 12582912, 20971520, 62914560],
   [12779715, 8519810, 63898575, 42599050, 66061296, 44040864, 12583104, 8388736, 62915520, 41943680, 66124800, 44083200, 12595200, 8396800, 62976000, 41984000, 12779520, 8519680, 63897600, 42598400, 66060288, 44040192, 12582912, 8388608, 62914560, 41943040],
   [21299525, 63898575, 17039620, 51118860, 17826064, 53478192, 20971840, 62915520, 16777472, 50332416, 17843200, 53529600, 20992000, 62976000, 16793600, 50380800, 21299200, 63897600, 17039360, 51118080, 17825792, 53477376, 20971520, 62914560, 16777216, 50331648],
   [63898575, 42599050, 51118860, 34079240, 53478192, 35652128, 62915520, 41943680, 50332416, 33554944, 53529600, 35686400, 62976000, 41984000, 50380800, 33587200, 63897600, 42598400, 51118080, 34078720, 53477376, 35651584, 62914560, 41943040, 50331648, 33554432]]

theorem ht0 : rowTbl (Vt (0, 0, 1) (1, 1, 0)) rows ![0, 1, 0, 1, 0, 0] = decRow 26 [1, 3, 5, 15, 341, 1023, 65, 195, 325, 975, 22369621, 67108863, 4264001, 12792003, 21320005, 63960015, 65537, 196611, 327685, 983055, 22348117, 67044351, 4259905, 12779715, 21299525, 63898575] := by
  decide +kernel

theorem ht1 : rowTbl (Vt (0, 0, 1) (1, 1, 0)) rows ![0, 1, 0, 1, 0, 1] = decRow 26 [3, 2, 15, 10, 1023, 682, 195, 130, 975, 650, 67108863, 44739242, 12792003, 8528002, 63960015, 42640010, 196611, 131074, 983055, 655370, 67044351, 44696234, 12779715, 8519810, 63898575, 42599050] := by
  decide +kernel

theorem ht2 : rowTbl (Vt (0, 0, 1) (1, 1, 0)) rows ![0, 1, 0, 1, 1, 0] = decRow 26 [5, 15, 4, 12, 276, 828, 325, 975, 260, 780, 18105620, 54316860, 21320005, 63960015, 17056004, 51168012, 327685, 983055, 262148, 786444, 18088212, 54264636, 21299525, 63898575, 17039620, 51118860] := by
  decide +kernel

theorem ht3 : rowTbl (Vt (0, 0, 1) (1, 1, 0)) rows ![0, 1, 0, 1, 1, 1] = decRow 26 [15, 10, 12, 8, 828, 552, 975, 650, 780, 520, 54316860, 36211240, 63960015, 42640010, 51168012, 34112008, 983055, 655370, 786444, 524296, 54264636, 36176424, 63898575, 42599050, 51118860, 34079240] := by
  decide +kernel

theorem ht4 : rowTbl (Vt (0, 0, 1) (1, 1, 0)) rows ![0, 1, 1, 0, 1, 0] = decRow 26 [341, 1023, 276, 828, 16, 48, 336, 1008, 272, 816, 1049616, 3148848, 22041936, 66125808, 17843472, 53530416, 22348117, 67044351, 18088212, 54264636, 1048592, 3145776, 22020432, 66061296, 17826064, 53478192] := by
  decide +kernel

theorem ht5 : rowTbl (Vt (0, 0, 1) (1, 1, 0)) rows ![0, 1, 1, 0, 1, 1] = decRow 26 [1023, 682, 828, 552, 48, 32, 1008, 672, 816, 544, 3148848, 2099232, 66125808, 44083872, 53530416, 35686944, 67044351, 44696234, 54264636, 36176424, 3145776, 2097184, 66061296, 44040864, 53478192, 35652128] := by
  decide +kernel

theorem ht6 : rowTbl (Vt (0, 0, 1) (1, 1, 0)) rows ![0, 1, 1, 1, 0, 0] = decRow 26 [65, 195, 325, 975, 336, 1008, 64, 192, 320, 960, 22041936, 66125808, 4198464, 12595392, 20992320, 62976960, 4259905, 12779715, 21299525, 63898575, 22020432, 66061296, 4194368, 12583104, 20971840, 62915520] := by
  decide +kernel

theorem ht7 : rowTbl (Vt (0, 0, 1) (1, 1, 0)) rows ![0, 1, 1, 1, 0, 1] = decRow 26 [195, 130, 975, 650, 1008, 672, 192, 128, 960, 640, 66125808, 44083872, 12595392, 8396928, 62976960, 41984640, 12779715, 8519810, 63898575, 42599050, 66061296, 44040864, 12583104, 8388736, 62915520, 41943680] := by
  decide +kernel

theorem ht8 : rowTbl (Vt (0, 0, 1) (1, 1, 0)) rows ![0, 1, 1, 1, 1, 0] = decRow 26 [325, 975, 260, 780, 272, 816, 320, 960, 256, 768, 17843472, 53530416, 20992320, 62976960, 16793856, 50381568, 21299525, 63898575, 17039620, 51118860, 17826064, 53478192, 20971840, 62915520, 16777472, 50332416] := by
  decide +kernel

theorem ht9 : rowTbl (Vt (0, 0, 1) (1, 1, 0)) rows ![0, 1, 1, 1, 1, 1] = decRow 26 [975, 650, 780, 520, 816, 544, 960, 640, 768, 512, 53530416, 35686944, 62976960, 41984640, 50381568, 33587712, 63898575, 42599050, 51118860, 34079240, 53478192, 35652128, 62915520, 41943680, 50332416, 33554944] := by
  decide +kernel

theorem ht10 : rowTbl (Vt (0, 0, 1) (1, 1, 0)) rows ![1, 0, 1, 0, 1, 0] = decRow 26 [22369621, 67108863, 18105620, 54316860, 1049616, 3148848, 22041936, 66125808, 17843472, 53530416, 1024, 3072, 21504, 64512, 17408, 52224, 22369280, 67107840, 18105344, 54316032, 1049600, 3148800, 22041600, 66124800, 17843200, 53529600] := by
  decide +kernel

theorem ht11 : rowTbl (Vt (0, 0, 1) (1, 1, 0)) rows ![1, 0, 1, 0, 1, 1] = decRow 26 [67108863, 44739242, 54316860, 36211240, 3148848, 2099232, 66125808, 44083872, 53530416, 35686944, 3072, 2048, 64512, 43008, 52224, 34816, 67107840, 44738560, 54316032, 36210688, 3148800, 2099200, 66124800, 44083200, 53529600, 35686400] := by
  decide +kernel

theorem ht12 : rowTbl (Vt (0, 0, 1) (1, 1, 0)) rows ![1, 0, 1, 1, 0, 0] = decRow 26 [4264001, 12792003, 21320005, 63960015, 22041936, 66125808, 4198464, 12595392, 20992320, 62976960, 21504, 64512, 4096, 12288, 20480, 61440, 4263936, 12791808, 21319680, 63959040, 22041600, 66124800, 4198400, 12595200, 20992000, 62976000] := by
  decide +kernel

theorem ht13 : rowTbl (Vt (0, 0, 1) (1, 1, 0)) rows ![1, 0, 1, 1, 0, 1] = decRow 26 [12792003, 8528002, 63960015, 42640010, 66125808, 44083872, 12595392, 8396928, 62976960, 41984640, 64512, 43008, 12288, 8192, 61440, 40960, 12791808, 8527872, 63959040, 42639360, 66124800, 44083200, 12595200, 8396800, 62976000, 41984000] := by
  decide +kernel

theorem ht14 : rowTbl (Vt (0, 0, 1) (1, 1, 0)) rows ![1, 0, 1, 1, 1, 0] = decRow 26 [21320005, 63960015, 17056004, 51168012, 17843472, 53530416, 20992320, 62976960, 16793856, 50381568, 17408, 52224, 20480, 61440, 16384, 49152, 21319680, 63959040, 17055744, 51167232, 17843200, 53529600, 20992000, 62976000, 16793600, 50380800] := by
  decide +kernel

theorem ht15 : rowTbl (Vt (0, 0, 1) (1, 1, 0)) rows ![1, 0, 1, 1, 1, 1] = decRow 26 [63960015, 42640010, 51168012, 34112008, 53530416, 35686944, 62976960, 41984640, 50381568, 33587712, 52224, 34816, 61440, 40960, 49152, 32768, 63959040, 42639360, 51167232, 34111488, 53529600, 35686400, 62976000, 41984000, 50380800, 33587200] := by
  decide +kernel

theorem ht16 : rowTbl (Vt (0, 0, 1) (1, 1, 0)) rows ![1, 1, 0, 1, 0, 0] = decRow 26 [65537, 196611, 327685, 983055, 22348117, 67044351, 4259905, 12779715, 21299525, 63898575, 22369280, 67107840, 4263936, 12791808, 21319680, 63959040, 65536, 196608, 327680, 983040, 22347776, 67043328, 4259840, 12779520, 21299200, 63897600] := by
  decide +kernel

theorem ht17 : rowTbl (Vt (0, 0, 1) (1, 1, 0)) rows ![1, 1, 0, 1, 0, 1] = decRow 26 [196611, 131074, 983055, 655370, 67044351, 44696234, 12779715, 8519810, 63898575, 42599050, 67107840, 44738560, 12791808, 8527872, 63959040, 42639360, 196608, 131072, 983040, 655360, 67043328, 44695552, 12779520, 8519680, 63897600, 42598400] := by
  decide +kernel

theorem ht18 : rowTbl (Vt (0, 0, 1) (1, 1, 0)) rows ![1, 1, 0, 1, 1, 0] = decRow 26 [327685, 983055, 262148, 786444, 18088212, 54264636, 21299525, 63898575, 17039620, 51118860, 18105344, 54316032, 21319680, 63959040, 17055744, 51167232, 327680, 983040, 262144, 786432, 18087936, 54263808, 21299200, 63897600, 17039360, 51118080] := by
  decide +kernel

theorem ht19 : rowTbl (Vt (0, 0, 1) (1, 1, 0)) rows ![1, 1, 0, 1, 1, 1] = decRow 26 [983055, 655370, 786444, 524296, 54264636, 36176424, 63898575, 42599050, 51118860, 34079240, 54316032, 36210688, 63959040, 42639360, 51167232, 34111488, 983040, 655360, 786432, 524288, 54263808, 36175872, 63897600, 42598400, 51118080, 34078720] := by
  decide +kernel

theorem ht20 : rowTbl (Vt (0, 0, 1) (1, 1, 0)) rows ![1, 1, 1, 0, 1, 0] = decRow 26 [22348117, 67044351, 18088212, 54264636, 1048592, 3145776, 22020432, 66061296, 17826064, 53478192, 1049600, 3148800, 22041600, 66124800, 17843200, 53529600, 22347776, 67043328, 18087936, 54263808, 1048576, 3145728, 22020096, 66060288, 17825792, 53477376] := by
  decide +kernel

theorem ht21 : rowTbl (Vt (0, 0, 1) (1, 1, 0)) rows ![1, 1, 1, 0, 1, 1] = decRow 26 [67044351, 44696234, 54264636, 36176424, 3145776, 2097184, 66061296, 44040864, 53478192, 35652128, 3148800, 2099200, 66124800, 44083200, 53529600, 35686400, 67043328, 44695552, 54263808, 36175872, 3145728, 2097152, 66060288, 44040192, 53477376, 35651584] := by
  decide +kernel

theorem ht22 : rowTbl (Vt (0, 0, 1) (1, 1, 0)) rows ![1, 1, 1, 1, 0, 0] = decRow 26 [4259905, 12779715, 21299525, 63898575, 22020432, 66061296, 4194368, 12583104, 20971840, 62915520, 22041600, 66124800, 4198400, 12595200, 20992000, 62976000, 4259840, 12779520, 21299200, 63897600, 22020096, 66060288, 4194304, 12582912, 20971520, 62914560] := by
  decide +kernel

theorem ht23 : rowTbl (Vt (0, 0, 1) (1, 1, 0)) rows ![1, 1, 1, 1, 0, 1] = decRow 26 [12779715, 8519810, 63898575, 42599050, 66061296, 44040864, 12583104, 8388736, 62915520, 41943680, 66124800, 44083200, 12595200, 8396800, 62976000, 41984000, 12779520, 8519680, 63897600, 42598400, 66060288, 44040192, 12582912, 8388608, 62914560, 41943040] := by
  decide +kernel

theorem ht24 : rowTbl (Vt (0, 0, 1) (1, 1, 0)) rows ![1, 1, 1, 1, 1, 0] = decRow 26 [21299525, 63898575, 17039620, 51118860, 17826064, 53478192, 20971840, 62915520, 16777472, 50332416, 17843200, 53529600, 20992000, 62976000, 16793600, 50380800, 21299200, 63897600, 17039360, 51118080, 17825792, 53477376, 20971520, 62914560, 16777216, 50331648] := by
  decide +kernel

theorem ht25 : rowTbl (Vt (0, 0, 1) (1, 1, 0)) rows ![1, 1, 1, 1, 1, 1] = decRow 26 [63898575, 42599050, 51118860, 34079240, 53478192, 35652128, 62915520, 41943680, 50332416, 33554944, 53529600, 35686400, 62976000, 41984000, 50380800, 33587200, 63897600, 42598400, 51118080, 34078720, 53477376, 35651584, 62914560, 41943040, 50331648, 33554432] := by
  decide +kernel

theorem htbl : tblOf (Vt (0, 0, 1) (1, 1, 0)) rows = dec 26 masks := by
  unfold tblOf dec
  conv_lhs =>
    arg 2
    unfold rows
  conv_rhs =>
    arg 2
    unfold masks
  simp only [List.map_cons, List.map_nil, ht0, ht1, ht2, ht3, ht4, ht5, ht6, ht7, ht8,
    ht9, ht10, ht11, ht12, ht13, ht14, ht15, ht16, ht17, ht18, ht19, ht20, ht21, ht22, ht23, ht24, ht25]

theorem hchk : combTB (dec 26 masks) (rows.map (fun _ => rows.map (fun _ => 0))) [-1, 7, -21, 35, -35, 21, -7, 1]
    (rows.map (fun _ => rows.map (fun _ => 1))) = rows.map (fun _ => rows.map (fun _ => 0)) := by
  decide +kernel

theorem vals : C (Vt (0, 0, 1) (1, 1, 0)) rows 0 = 676 ∧ C (Vt (0, 0, 1) (1, 1, 0)) rows 1 = 4374 ∧ C (Vt (0, 0, 1) (1, 1, 0)) rows 2 = 16872 ∧ C (Vt (0, 0, 1) (1, 1, 0)) rows 3 = 49130 ∧ C (Vt (0, 0, 1) (1, 1, 0)) rows 4 = 119580 ∧ C (Vt (0, 0, 1) (1, 1, 0)) rows 5 = 256774 ∧ C (Vt (0, 0, 1) (1, 1, 0)) rows 6 = 502416 := by
  simp only [C_eqB (Vt (0, 0, 1) (1, 1, 0)) rows (dec 26 masks) htbl]
  decide +kernel

theorem a_C (m : ℕ) : a (m + 2) = C (Vt (0, 0, 1) (1, 1, 0)) rows m := by
  classical
  rw [← card_eq_C (Hrow (0, 0, 0) (0, 0, 1)) (Vt (0, 0, 1) (1, 1, 0)) rows hN hH m]
  unfold a
  refine congrArg Nat.cast (congrArg Finset.card (Finset.filter_congr fun x _ => ?_))
  simp only [avoids, decide_eq_true_eq]
  exact avoid_iff _ _ _ _ x

theorem a_1 : a 1 = 26 := by
  classical
  have h := card_one (Hrow (0, 0, 0) (0, 0, 1)) (Vt (0, 0, 1) (1, 1, 0)) rows hN hH
  rw [show ((rows.length : ℕ) : ℤ) = 26 from rfl] at h
  rw [← h]
  unfold a
  refine congrArg Nat.cast (congrArg Finset.card (Finset.filter_congr fun x _ => ?_))
  simp only [avoids, decide_eq_true_eq]
  exact avoid_iff _ _ _ _ x

theorem recZ (m : ℕ) : -a (m + 2) + 7 * a (m + 3) - 21 * a (m + 4) + 35 * a (m + 5) - 35 * a (m + 6) + 21 * a (m + 7) - 7 * a (m + 8) + a (m + 9) = 0 := by
  have h := rec_CB (Vt (0, 0, 1) (1, 1, 0)) rows (dec 26 masks) htbl [-1, 7, -21, 35, -35, 21, -7, 1] hchk m
  simp only [combC] at h
  rw [a_C, a_C, a_C, a_C, a_C, a_C, a_C, a_C]
  linarith

end OMA.P208285

theorem OMA.solution : type_of% @OMA.S_oeis_a208285.main := by
  have A1 : (OMA.S_oeis_a208285.a 1 : ℚ) = 26 := by exact_mod_cast OMA.P208285.a_1
  obtain ⟨v0, v1, v2, v3, v4, v5, v6⟩ := OMA.P208285.vals
  have A2 : (OMA.S_oeis_a208285.a 2 : ℚ) = 676 := by
    have h := OMA.P208285.a_C 0
    rw [v0] at h
    exact_mod_cast h
  have A3 : (OMA.S_oeis_a208285.a 3 : ℚ) = 4374 := by
    have h := OMA.P208285.a_C 1
    rw [v1] at h
    exact_mod_cast h
  have A4 : (OMA.S_oeis_a208285.a 4 : ℚ) = 16872 := by
    have h := OMA.P208285.a_C 2
    rw [v2] at h
    exact_mod_cast h
  have A5 : (OMA.S_oeis_a208285.a 5 : ℚ) = 49130 := by
    have h := OMA.P208285.a_C 3
    rw [v3] at h
    exact_mod_cast h
  have A6 : (OMA.S_oeis_a208285.a 6 : ℚ) = 119580 := by
    have h := OMA.P208285.a_C 4
    rw [v4] at h
    exact_mod_cast h
  have A7 : (OMA.S_oeis_a208285.a 7 : ℚ) = 256774 := by
    have h := OMA.P208285.a_C 5
    rw [v5] at h
    exact_mod_cast h
  have A8 : (OMA.S_oeis_a208285.a 8 : ℚ) = 502416 := by
    have h := OMA.P208285.a_C 6
    rw [v6] at h
    exact_mod_cast h
  have hrec : ∀ m : ℕ, (OMA.S_oeis_a208285.a (m + 9) : ℚ) = OMA.S_oeis_a208285.a (m + 2) - 7 * OMA.S_oeis_a208285.a (m + 3) + 21 * OMA.S_oeis_a208285.a (m + 4) - 35 * OMA.S_oeis_a208285.a (m + 5) + 35 * OMA.S_oeis_a208285.a (m + 6) - 21 * OMA.S_oeis_a208285.a (m + 7) + 7 * OMA.S_oeis_a208285.a (m + 8) := by
    intro m
    have h := OMA.P208285.recZ m
    have h' : (-(OMA.S_oeis_a208285.a (m + 2) : ℚ) + 7 * (OMA.S_oeis_a208285.a (m + 3) : ℚ) - 21 * (OMA.S_oeis_a208285.a (m + 4) : ℚ) + 35 * (OMA.S_oeis_a208285.a (m + 5) : ℚ) - 35 * (OMA.S_oeis_a208285.a (m + 6) : ℚ) + 21 * (OMA.S_oeis_a208285.a (m + 7) : ℚ) - 7 * (OMA.S_oeis_a208285.a (m + 8) : ℚ) + (OMA.S_oeis_a208285.a (m + 9) : ℚ) : ℚ) = 0 := by exact_mod_cast h
    linarith
  refine ⟨?_, ?_⟩
  · have hD : (((1 - PowerSeries.X) ^ 7) : PowerSeries ℚ)
        = PowerSeries.C (1 : ℚ) * PowerSeries.X ^ 0 + PowerSeries.C (-7 : ℚ) * PowerSeries.X ^ 1 + PowerSeries.C (21 : ℚ) * PowerSeries.X ^ 2 + PowerSeries.C (-35 : ℚ) * PowerSeries.X ^ 3 + PowerSeries.C (35 : ℚ) * PowerSeries.X ^ 4 + PowerSeries.C (-21 : ℚ) * PowerSeries.X ^ 5 + PowerSeries.C (7 : ℚ) * PowerSeries.X ^ 6 + PowerSeries.C (-1 : ℚ) * PowerSeries.X ^ 7 := by
      simp only [map_ofNat, map_neg, map_one, map_zero]; ring
    have hNum : ((2 * PowerSeries.X * (13 + 247 * PowerSeries.X + 94 * PowerSeries.X ^ 2 - 230 * PowerSeries.X ^ 3 + 65 * PowerSeries.X ^ 4 + 3 * PowerSeries.X ^ 5)) : PowerSeries ℚ)
        = PowerSeries.C (0 : ℚ) * PowerSeries.X ^ 0 + PowerSeries.C (26 : ℚ) * PowerSeries.X ^ 1 + PowerSeries.C (494 : ℚ) * PowerSeries.X ^ 2 + PowerSeries.C (188 : ℚ) * PowerSeries.X ^ 3 + PowerSeries.C (-460 : ℚ) * PowerSeries.X ^ 4 + PowerSeries.C (130 : ℚ) * PowerSeries.X ^ 5 + PowerSeries.C (6 : ℚ) * PowerSeries.X ^ 6 := by
      simp only [map_ofNat, map_neg, map_one, map_zero]; ring
    have key : ∀ F : PowerSeries ℚ, F * (PowerSeries.C (1 : ℚ) * PowerSeries.X ^ 0 + PowerSeries.C (-7 : ℚ) * PowerSeries.X ^ 1 + PowerSeries.C (21 : ℚ) * PowerSeries.X ^ 2 + PowerSeries.C (-35 : ℚ) * PowerSeries.X ^ 3 + PowerSeries.C (35 : ℚ) * PowerSeries.X ^ 4 + PowerSeries.C (-21 : ℚ) * PowerSeries.X ^ 5 + PowerSeries.C (7 : ℚ) * PowerSeries.X ^ 6 + PowerSeries.C (-1 : ℚ) * PowerSeries.X ^ 7)
        = PowerSeries.C (1 : ℚ) * (F * PowerSeries.X ^ 0) + PowerSeries.C (-7 : ℚ) * (F * PowerSeries.X ^ 1) + PowerSeries.C (21 : ℚ) * (F * PowerSeries.X ^ 2) + PowerSeries.C (-35 : ℚ) * (F * PowerSeries.X ^ 3) + PowerSeries.C (35 : ℚ) * (F * PowerSeries.X ^ 4) + PowerSeries.C (-21 : ℚ) * (F * PowerSeries.X ^ 5) + PowerSeries.C (7 : ℚ) * (F * PowerSeries.X ^ 6) + PowerSeries.C (-1 : ℚ) * (F * PowerSeries.X ^ 7) := by
      intro F; ring
    rw [hD, hNum, key]
    ext n
    simp only [map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_X_pow,
      PowerSeries.coeff_mk, PowerSeries.coeff_C]
    rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | m
    · norm_num
    · norm_num [A1]
    · norm_num [A1, A2]
    · norm_num [A1, A2, A3]
    · norm_num [A1, A2, A3, A4]
    · norm_num [A1, A2, A3, A4, A5]
    · norm_num [A1, A2, A3, A4, A5, A6]
    · norm_num [A1, A2, A3, A4, A5, A6, A7]
    · norm_num [A1, A2, A3, A4, A5, A6, A7, A8]
    · rw [show m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = m + 9 from rfl]
      have h := hrec m
      simp only [show 0 ≤ m + 9 from by omega,
        show m + 9 - 0 = m + 9 from rfl,
        show ¬ (m + 9 < 1) from by omega,
        show 1 ≤ m + 9 from by omega,
        show m + 9 - 1 = m + 8 from rfl,
        show ¬ (m + 8 < 1) from by omega,
        show 2 ≤ m + 9 from by omega,
        show m + 9 - 2 = m + 7 from rfl,
        show ¬ (m + 7 < 1) from by omega,
        show 3 ≤ m + 9 from by omega,
        show m + 9 - 3 = m + 6 from rfl,
        show ¬ (m + 6 < 1) from by omega,
        show 4 ≤ m + 9 from by omega,
        show m + 9 - 4 = m + 5 from rfl,
        show ¬ (m + 5 < 1) from by omega,
        show 5 ≤ m + 9 from by omega,
        show m + 9 - 5 = m + 4 from rfl,
        show ¬ (m + 4 < 1) from by omega,
        show 6 ≤ m + 9 from by omega,
        show m + 9 - 6 = m + 3 from rfl,
        show ¬ (m + 3 < 1) from by omega,
        show 7 ≤ m + 9 from by omega,
        show m + 9 - 7 = m + 2 from rfl,
        show ¬ (m + 2 < 1) from by omega,
        show ¬ (m + 9 = 0) from by omega,
        show ¬ (m + 8 = 0) from by omega,
        show ¬ (m + 7 = 0) from by omega,
        show ¬ (m + 6 = 0) from by omega,
        show ¬ (m + 5 = 0) from by omega,
        show ¬ (m + 4 = 0) from by omega,
        show ¬ (m + 3 = 0) from by omega,
        if_true, if_false]
      rw [h]
      ring
  · intro n hn
    rcases Nat.lt_or_ge n 9 with h | h
    · interval_cases n <;> norm_num [A1, A2, A3, A4, A5, A6, A7, A8]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 9 := ⟨n - 9, by omega⟩
      have h := hrec m
      simp only [show m + 9 - 1 = m + 8 from rfl, show m + 9 - 2 = m + 7 from rfl, show m + 9 - 3 = m + 6 from rfl, show m + 9 - 4 = m + 5 from rfl, show m + 9 - 5 = m + 4 from rfl, show m + 9 - 6 = m + 3 from rfl, show m + 9 - 7 = m + 2 from rfl]
      rw [h]
      ring
