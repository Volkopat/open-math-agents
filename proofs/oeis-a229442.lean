import OMAStatements.S_oeis_a229442

namespace OMA.S_oeis_a229442

open PowerSeries Finset


instance {m q : ℕ} : DecidableRel (@lexLE m q) := fun u v => by unfold lexLE; infer_instance


instance {n : ℕ} : DecidablePred (@good n) := fun x => by unfold good; infer_instance


/-! ## Lexicographic order on `Fin.cons` -/

/-- Strict lexicographic order. -/
def lexLT {m q : ℕ} (u v : Fin m → Fin q) : Prop :=
  ∃ i : Fin m, (∀ j : Fin m, j < i → u j = v j) ∧ u i < v i

lemma lexLT_cons {m q : ℕ} (a b : Fin q) (u v : Fin m → Fin q) :
    lexLT (Fin.cons a u : Fin (m + 1) → Fin q) (Fin.cons b v) ↔ a < b ∨ (a = b ∧ lexLT u v) := by
  constructor
  · rintro ⟨i, hi, hlt⟩
    induction i using Fin.cases with
    | zero => left; simpa using hlt
    | succ i =>
      right
      have h0 := hi 0 (Fin.succ_pos i)
      simp only [Fin.cons_zero] at h0
      refine ⟨h0, i, fun j hj => ?_, by simpa using hlt⟩
      have := hi j.succ (Fin.succ_lt_succ_iff.2 hj)
      simpa using this
  · rintro (h | ⟨rfl, i, hi, hlt⟩)
    · exact ⟨0, fun j hj => absurd hj (Fin.not_lt_zero j), by simpa using h⟩
    · refine ⟨i.succ, fun j hj => ?_, by simpa using hlt⟩
      induction j using Fin.cases with
      | zero => rfl
      | succ j => simpa using hi j (Fin.succ_lt_succ_iff.1 hj)

lemma lexLE_cons {m q : ℕ} (a b : Fin q) (u v : Fin m → Fin q) :
    lexLE (Fin.cons a u : Fin (m + 1) → Fin q) (Fin.cons b v) ↔ a < b ∨ (a = b ∧ lexLE u v) := by
  have e : lexLE (Fin.cons a u : Fin (m + 1) → Fin q) (Fin.cons b v) ↔
      (Fin.cons a u : Fin (m + 1) → Fin q) = Fin.cons b v ∨
        lexLT (Fin.cons a u : Fin (m + 1) → Fin q) (Fin.cons b v) := Iff.rfl
  rw [e, lexLT_cons, Fin.cons_inj]
  unfold lexLE
  change _ ↔ a < b ∨ (a = b ∧ (u = v ∨ lexLT u v))
  tauto

/-! ## The status of a pair of columns -/

/-- z: the two columns have not differed yet; d: they have, in the right order. -/
inductive T2
  | z
  | d
  deriving DecidableEq

instance : Fintype T2 := ⟨{.z, .d}, fun t => by cases t <;> simp⟩

/-- The condition that the rest (u, v) of a pair of columns must satisfy after the status t. -/
def PT {m : ℕ} : T2 → (Fin m → Fin 3) → (Fin m → Fin 3) → Prop
  | .z, u, v => lexLE u v
  | .d, _, _ => True

instance {m : ℕ} (t : T2) (u v : Fin m → Fin 3) : Decidable (PT t u v) := by
  cases t <;> unfold PT <;> infer_instance

/-- The entries (x, y) of the next row in the two columns are allowed after the status t. -/
def okT (t : T2) (x y : Fin 3) : Prop := t = .z → x ≤ y

instance (t : T2) (x y : Fin 3) : Decidable (okT t x y) := by
  unfold okT; infer_instance

/-- The status after the entries (x, y). -/
def stpT (t : T2) (x y : Fin 3) : T2 := if x = y then t else .d

lemma PT_cons {m : ℕ} (t : T2) (x y : Fin 3) (u v : Fin m → Fin 3) :
    PT t (Fin.cons x u : Fin (m + 1) → Fin 3) (Fin.cons y v) ↔ okT t x y ∧ PT (stpT t x y) u v := by
  by_cases hxy : x = y
  · subst hxy
    rw [show stpT t x x = t from if_pos rfl]
    cases t <;> simp [PT, okT, lexLE_cons]
  · rw [show stpT t x y = .d from if_neg hxy]
    cases t
    · simp only [PT, okT, lexLE_cons, hxy, false_and, or_false, true_implies, and_true]
      exact ⟨le_of_lt, fun h => lt_of_le_of_ne h hxy⟩
    · simp [PT, okT]

lemma PT_nil (t : T2) (u v : Fin 0 → Fin 3) : PT t u v := by
  cases t
  · exact Or.inl (funext fun i => i.elim0)
  · trivial

/-! ## The arrays the proof counts -/

/-- The condition inside a row. -/
def hrow (r : Fin 5 → Fin 3) : Prop :=
  ∀ j : Fin 4, ¬ ((r j.succ : ℤ) - r j.castSucc ≡ 1 [ZMOD 3])

/-- The conditions between a row r and the row s below it. -/
def vcond (r s : Fin 5 → Fin 3) : Prop :=
  (∀ j : Fin 5, ¬ ((s j : ℤ) - r j ≡ -1 [ZMOD 3])) ∧ lexLE r s

instance (r : Fin 5 → Fin 3) : Decidable (hrow r) := by unfold hrow; infer_instance

instance (r s : Fin 5 → Fin 3) : Decidable (vcond r s) := by unfold vcond; infer_instance

/-- Column j of the array f. -/
def col {m : ℕ} (f : Fin m → Fin 5 → Fin 3) (j : Fin 5) : Fin m → Fin 3 := fun i => f i j

/-- Consecutive rows satisfy the conditions between rows. -/
def chain {m : ℕ} (y : Fin m → Fin 5 → Fin 3) : Prop :=
  ∀ i i' : Fin m, i.val + 1 = i'.val → vcond (y i) (y i')

instance {m : ℕ} : DecidablePred (@chain m) := fun y => by unfold chain; infer_instance

/-- The arrays counted by the proof. -/
def core {m : ℕ} (y : Fin m → Fin 5 → Fin 3) : Prop :=
  (∀ i, hrow (y i)) ∧ chain y ∧ ∀ j : Fin 4, PT .z (col y j.castSucc) (col y j.succ)

instance {m : ℕ} : DecidablePred (@core m) := fun y => by unfold core; infer_instance

/-- The rows f continue the row r validly, when the column pairs have statuses τ after r. -/
def Cont {m : ℕ} (τ : Fin 4 → T2) (r : Fin 5 → Fin 3) (f : Fin m → Fin 5 → Fin 3) : Prop :=
  chain (Fin.cons r f : Fin (m + 1) → Fin 5 → Fin 3) ∧
    (∀ i, hrow (f i)) ∧ ∀ j : Fin 4, PT (τ j) (col f j.castSucc) (col f j.succ)

instance {m : ℕ} (τ : Fin 4 → T2) (r : Fin 5 → Fin 3) : DecidablePred (@Cont m τ r) :=
  fun f => by unfold Cont; infer_instance

/-- The next row s is allowed by the statuses τ. -/
def okR (τ : Fin 4 → T2) (s : Fin 5 → Fin 3) : Prop :=
  ∀ j : Fin 4, okT (τ j) (s j.castSucc) (s j.succ)

instance (τ : Fin 4 → T2) : DecidablePred (okR τ) := fun s => by unfold okR; infer_instance

/-- The statuses after the row s. -/
def stpR (τ : Fin 4 → T2) (s : Fin 5 → Fin 3) : Fin 4 → T2 :=
  fun j => stpT (τ j) (s j.castSucc) (s j.succ)

lemma col_cons {m : ℕ} (s : Fin 5 → Fin 3) (g : Fin m → Fin 5 → Fin 3) (j : Fin 5) :
    col (Fin.cons s g : Fin (m + 1) → Fin 5 → Fin 3) j = Fin.cons (s j) (col g j) := by
  funext i
  induction i using Fin.cases <;> rfl

lemma chain_cons2 {m : ℕ} (r s : Fin 5 → Fin 3) (g : Fin m → Fin 5 → Fin 3) :
    chain (Fin.cons r (Fin.cons s g) : Fin (m + 2) → Fin 5 → Fin 3) ↔
      vcond r s ∧ chain (Fin.cons s g : Fin (m + 1) → Fin 5 → Fin 3) := by
  unfold chain
  constructor
  · intro h
    refine ⟨by simpa using h 0 1 (by simp), fun i j hij => ?_⟩
    have := h i.succ j.succ (by simp [hij])
    simpa using this
  · rintro ⟨h0, h⟩ i j hij
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => simp at hij
      | succ j =>
        have hj : j = 0 := by ext; simp at hij; omega
        subst hj
        simpa using h0
    | succ i =>
      induction j using Fin.cases with
      | zero => simp at hij
      | succ j =>
        simp only [Fin.cons_succ]
        exact h i j (by simp at hij; omega)

lemma all_hrow_cons {m : ℕ} (s : Fin 5 → Fin 3) (g : Fin m → Fin 5 → Fin 3) :
    (∀ i, hrow ((Fin.cons s g : Fin (m + 1) → Fin 5 → Fin 3) i)) ↔ hrow s ∧ ∀ i, hrow (g i) := by
  rw [Fin.forall_fin_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]

lemma Cont_cons {m : ℕ} (τ : Fin 4 → T2) (r s : Fin 5 → Fin 3) (g : Fin m → Fin 5 → Fin 3) :
    Cont τ r (Fin.cons s g) ↔ (hrow s ∧ vcond r s) ∧ okR τ s ∧ Cont (stpR τ s) s g := by
  unfold Cont okR stpR
  rw [chain_cons2, all_hrow_cons]
  simp only [col_cons, PT_cons]
  constructor
  · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5⟩
    exact ⟨⟨h3, h1⟩, fun j => (h5 j).1, h2, h4, fun j => (h5 j).2⟩
  · rintro ⟨⟨h3, h1⟩, h5, h2, h4, h6⟩
    exact ⟨⟨h1, h2⟩, ⟨h3, h4⟩, fun j => ⟨h5 j, h6 j⟩⟩

lemma Cont_nil (τ : Fin 4 → T2) (r : Fin 5 → Fin 3) (f : Fin 0 → Fin 5 → Fin 3) :
    Cont τ r f := by
  refine ⟨fun i i' h => ?_, fun i => i.elim0, fun j => PT_nil _ _ _⟩
  have := i'.isLt
  have := i.isLt
  omega

lemma core_cons {m : ℕ} (s : Fin 5 → Fin 3) (g : Fin m → Fin 5 → Fin 3) :
    core (Fin.cons s g : Fin (m + 1) → Fin 5 → Fin 3) ↔
      (hrow s ∧ okR (fun _ => .z) s) ∧ Cont (stpR (fun _ => .z) s) s g := by
  unfold core Cont okR stpR
  rw [all_hrow_cons]
  simp only [col_cons, PT_cons]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨⟨h1, fun j => (h4 j).1⟩, h3, h2, fun j => (h4 j).2⟩
  · rintro ⟨⟨h1, h4⟩, h3, h2, h5⟩
    exact ⟨⟨h1, h2⟩, h3, fun j => ⟨h4 j, h5 j⟩⟩

/-! ## Counting by the first row -/

lemma card_by_head {α : Type*} [Fintype α] [DecidableEq α] {m : ℕ}
    (Q : (Fin (m + 1) → α) → Prop) [DecidablePred Q] :
    (univ.filter Q).card = ∑ v : α, (univ.filter (fun h : Fin m → α => Q (Fin.cons v h))).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun g : Fin (m + 1) → α => g 0) (t := univ)
    (by intro x _; simp)]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  symm
  apply Finset.card_bij (fun h _ => (Fin.cons v h : Fin (m + 1) → α))
  · intro h hh
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hh ⊢
    exact ⟨hh, by simp⟩
  · intro h₁ _ h₂ _ e
    simpa using congrArg Fin.tail e
  · intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
    obtain ⟨hq, h0⟩ := hg
    refine ⟨Fin.tail g, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← h0, Fin.cons_self_tail]
      exact hq
    · show Fin.cons v (Fin.tail g) = g
      rw [← h0, Fin.cons_self_tail]

/-- F(m, τ, r): the number of ways to continue the row r by m more rows, statuses τ after r. -/
def F (m : ℕ) (τ : Fin 4 → T2) (r : Fin 5 → Fin 3) : ℕ :=
  (univ.filter (fun f : Fin m → Fin 5 → Fin 3 => Cont τ r f)).card

lemma F_succ (m : ℕ) (τ : Fin 4 → T2) (r : Fin 5 → Fin 3) :
    F (m + 1) τ r = ∑ s : Fin 5 → Fin 3,
      if (hrow s ∧ vcond r s) ∧ okR τ s then F m (stpR τ s) s else 0 := by
  unfold F
  rw [card_by_head]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  simp only [Cont_cons]
  split_ifs with h
  · congr 1
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun hg => hg.2.2, fun hg => ⟨h.1, h.2, hg⟩⟩
  · rw [Finset.card_eq_zero]
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
    exact fun hg => h ⟨hg.1, hg.2.1⟩

lemma F_zero (τ : Fin 4 → T2) (r : Fin 5 → Fin 3) : F 0 τ r = 1 := by
  unfold F
  have hu : (univ : Finset (Fin 0 → Fin 5 → Fin 3)) = {Fin.elim0} := by
    ext g
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    funext i
    exact i.elim0
  rw [hu, Finset.filter_singleton, if_pos (Cont_nil _ _ _)]
  rfl

lemma good_iff_core {n : ℕ} (x : Fin n → Fin 5 → Fin 3) : good x ↔ core x := by
  unfold good core chain hrow vcond col
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨fun i j => h1 i j.castSucc j.succ (by simp), fun i i' hi => ⟨fun j => h2 i i' j hi, h3 i i' hi⟩,
      fun j => h4 j.castSucc j.succ (by simp)⟩
  · rintro ⟨h1, h2, h4⟩
    refine ⟨fun i j j' hj => ?_, fun i i' j hi => (h2 i i' hi).1 j, fun i i' hi => (h2 i i' hi).2,
      fun j j' hj => ?_⟩
    · have hj3 : j.val < 4 := by have := j'.isLt; omega
      have e1 : j = (⟨j.val, hj3⟩ : Fin 4).castSucc := Fin.ext rfl
      have e2 : j' = (⟨j.val, hj3⟩ : Fin 4).succ := Fin.ext (by simp; omega)
      rw [e1, e2]
      exact h1 i _
    · have hj3 : j.val < 4 := by have := j'.isLt; omega
      have e1 : j = (⟨j.val, hj3⟩ : Fin 4).castSucc := Fin.ext rfl
      have e2 : j' = (⟨j.val, hj3⟩ : Fin 4).succ := Fin.ext (by simp; omega)
      rw [e1, e2]
      exact h4 _

lemma a_eq (n : ℕ) : a n = (univ.filter (fun y : Fin n → Fin 5 → Fin 3 => core y)).card := by
  unfold a
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, good_iff_core]

lemma a_succ (m : ℕ) : a (m + 1) = ∑ s : Fin 5 → Fin 3,
    if hrow s ∧ okR (fun _ => .z) s then F m (stpR (fun _ => .z) s) s else 0 := by
  rw [a_eq, card_by_head]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  simp only [core_cons]
  split_ifs with h
  · unfold F
    congr 1
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun hg => hg.2, fun hg => ⟨h, hg⟩⟩
  · rw [Finset.card_eq_zero]
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
    exact fun hg => h hg.1

/-! ## The count the kernel evaluates -/

/-- Pass the status through a match, so that the kernel sees a constructor. -/
def mk2 (t : T2) (f : T2 → ℕ) : ℕ :=
  match t with
  | .z => f .z
  | .d => f .d

lemma mk2_eq (t : T2) (f : T2 → ℕ) : mk2 t f = f t := by cases t <;> rfl

/-- Digit j of the code c of a row: the entry in column j. -/
def dg (c j : ℕ) : ℕ := c / 3 ^ j % 3

def okB (t : T2) (x y : ℕ) : Bool :=
  match t with
  | .z => decide (x ≤ y)
  | .d => true

def stpB (t : T2) (x y : ℕ) : T2 := if x = y then t else .d

/-- (b - a) mod 3 = k, for digits a, b. -/
def mdB (b a k : ℕ) : Bool := (b + 3 - a) % 3 == k

lemma md_one : ∀ a b : Fin 3, mdB b a 1 = true ↔ ((b : ℤ) - a ≡ 1 [ZMOD 3]) := by decide

lemma md_two : ∀ a b : Fin 3, mdB b a 2 = true ↔ ((b : ℤ) - a ≡ -1 [ZMOD 3]) := by decide

/-- The row with code c satisfies the condition inside a row. -/
def hrowB (c : ℕ) : Bool := !mdB (dg c 1) (dg c 0) 1 && !mdB (dg c 2) (dg c 1) 1 && !mdB (dg c 3) (dg c 2) 1 && !mdB (dg c 4) (dg c 3) 1

/-- Lexicographic order on digit lists. -/
def lexB : List ℕ → List ℕ → Bool
  | x :: xs, y :: ys => decide (x < y) || (decide (x = y) && lexB xs ys)
  | _, _ => true

/-- The rows with codes r (above) and s (below) satisfy the conditions between rows. -/
def vB (r s : ℕ) : Bool :=
  (!mdB (dg s 0) (dg r 0) 2 && !mdB (dg s 1) (dg r 1) 2 && !mdB (dg s 2) (dg r 2) 2 && !mdB (dg s 3) (dg r 3) 2 && !mdB (dg s 4) (dg r 4) 2) && lexB (List.ofFn (fun i : Fin 5 => dg r i)) (List.ofFn (fun i : Fin 5 => dg s i))

/-- A sum over a list, by plain recursion (cheap for the kernel). -/
def sumL {α : Type} : List α → (α → ℕ) → ℕ
  | [], _ => 0
  | x :: l, f => f x + sumL l f

lemma sumL_eq {α : Type} (l : List α) (f : α → ℕ) : sumL l f = (l.map f).sum := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [sumL, ih]

lemma sumL_filter {α : Type} (l : List α) (p : α → Bool) (f : α → ℕ) :
    sumL (l.filter p) f = sumL l (fun x => if p x = true then f x else 0) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    by_cases h : p x = true
    · simp [List.filter_cons, h, sumL, ih]
    · simp [List.filter_cons, h, sumL, ih]

/-- All row codes, and the rows satisfying the condition inside a row. -/
def allRows : List (Fin (3 ^ 5)) := List.finRange (3 ^ 5)

def validRows : List (Fin (3 ^ 5)) := allRows.filter (fun c => hrowB c)

lemma sumL_allRows (g : Fin (3 ^ 5) → ℕ) : sumL allRows g = ∑ s, g s := by
  rw [sumL_eq, allRows, Fin.sum_univ_def]

/-- The rows that may follow the row r. -/
def succL (r : Fin (3 ^ 5)) : List (Fin (3 ^ 5)) := validRows.filter (fun s => vB r s)

/-- W(m, t, r) through the status machine; the kernel evaluates each state once. -/
def cnt : ℕ → T2 → T2 → T2 → T2 → Fin (3 ^ 5) → ℕ
  | 0, t0, t1, t2, t3, _ => 1
  | m + 1, t0, t1, t2, t3, r =>
      sumL (succL r) (fun s : Fin (3 ^ 5) =>
        if okB t0 (dg s 0) (dg s 1) && okB t1 (dg s 1) (dg s 2) && okB t2 (dg s 2) (dg s 3) && okB t3 (dg s 3) (dg s 4) then
          mk2 (stpB t0 (dg s 0) (dg s 1)) (fun u0 => mk2 (stpB t1 (dg s 1) (dg s 2)) (fun u1 => mk2 (stpB t2 (dg s 2) (dg s 3)) (fun u2 => mk2 (stpB t3 (dg s 3) (dg s 4)) (fun u3 => cnt m u0 u1 u2 u3 s))))
        else 0)

lemma ite_band (b c : Bool) (x : ℕ) :
    (if b = true then (if c = true then x else 0) else 0) = if (b && c) = true then x else 0 := by
  cases b <;> cases c <;> rfl

/-- The row with code c. -/
def dec : Fin (3 ^ 5) ≃ (Fin 5 → Fin 3) := finFunctionFinEquiv.symm

lemma dec_val (c : Fin (3 ^ 5)) (j : Fin 5) : (dec c j : ℕ) = dg c j :=
  finFunctionFinEquiv_symm_apply_val c j

lemma okB_iff (t : T2) (x y : Fin 3) : okB t x y = true ↔ okT t x y := by
  cases t
  · show decide ((x : ℕ) ≤ (y : ℕ)) = true ↔ (T2.z = T2.z → x ≤ y)
    rw [decide_eq_true_eq]
    exact ⟨fun h _ => h, fun h => h rfl⟩
  · exact ⟨fun _ h => absurd h (by decide), fun _ => rfl⟩

lemma stpB_eq (t : T2) (x y : Fin 3) : stpB t x y = stpT t x y := by
  unfold stpB stpT
  simp only [Fin.ext_iff]

lemma lexB_iff : ∀ (m : ℕ) (u v : Fin m → Fin 3),
    lexB (List.ofFn (fun i => (u i : ℕ))) (List.ofFn (fun i => (v i : ℕ))) = true ↔ lexLE u v
  | 0, u, v => by
    simp only [List.ofFn_zero, lexB, true_iff]
    exact Or.inl (funext fun i => i.elim0)
  | m + 1, u, v => by
    rw [List.ofFn_succ, List.ofFn_succ]
    simp only [lexB, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    rw [lexB_iff m (fun i => u i.succ) (fun i => v i.succ)]
    conv_rhs => rw [← Fin.cons_self_tail u, ← Fin.cons_self_tail v]
    rw [lexLE_cons]
    simp only [Fin.lt_def, Fin.ext_iff]
    rfl

lemma hrow_iff (r : Fin 5 → Fin 3) : hrow r ↔ ¬ ((r 1 : ℤ) - r 0 ≡ 1 [ZMOD 3]) ∧ ¬ ((r 2 : ℤ) - r 1 ≡ 1 [ZMOD 3]) ∧ ¬ ((r 3 : ℤ) - r 2 ≡ 1 [ZMOD 3]) ∧ ¬ ((r 4 : ℤ) - r 3 ≡ 1 [ZMOD 3]) := by
  unfold hrow
  constructor
  · intro h
    exact ⟨h 0, h 1, h 2, h 3⟩
  · rintro ⟨h0, h1, h2, h3⟩ j
    fin_cases j
    · exact h0
    · exact h1
    · exact h2
    · exact h3

lemma vert_iff (r s : Fin 5 → Fin 3) :
    (∀ j : Fin 5, ¬ ((s j : ℤ) - r j ≡ -1 [ZMOD 3])) ↔ ¬ ((s 0 : ℤ) - r 0 ≡ -1 [ZMOD 3]) ∧ ¬ ((s 1 : ℤ) - r 1 ≡ -1 [ZMOD 3]) ∧ ¬ ((s 2 : ℤ) - r 2 ≡ -1 [ZMOD 3]) ∧ ¬ ((s 3 : ℤ) - r 3 ≡ -1 [ZMOD 3]) ∧ ¬ ((s 4 : ℤ) - r 4 ≡ -1 [ZMOD 3]) := by
  constructor
  · intro h
    exact ⟨h 0, h 1, h 2, h 3, h 4⟩
  · rintro ⟨h0, h1, h2, h3, h4⟩ j
    fin_cases j
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4

lemma hrowB_iff (c : Fin (3 ^ 5)) : hrowB c = true ↔ hrow (dec c) := by
  rw [hrow_iff]
  have c0 : dg c 0 = (dec c 0 : ℕ) := (dec_val c 0).symm
  have c1 : dg c 1 = (dec c 1 : ℕ) := (dec_val c 1).symm
  have c2 : dg c 2 = (dec c 2 : ℕ) := (dec_val c 2).symm
  have c3 : dg c 3 = (dec c 3 : ℕ) := (dec_val c 3).symm
  have c4 : dg c 4 = (dec c 4 : ℕ) := (dec_val c 4).symm
  simp only [hrowB, c0, c1, c2, c3, c4, Bool.and_eq_true, Bool.not_eq_true', Bool.eq_false_iff, ne_eq,
    md_one, and_assoc]

lemma vB_iff (r s : Fin (3 ^ 5)) : vB r s = true ↔ vcond (dec r) (dec s) := by
  have e : ∀ c : Fin (3 ^ 5), List.ofFn (fun i : Fin 5 => dg c i) =
      List.ofFn (fun i => (dec c i : ℕ)) := fun c =>
    congrArg List.ofFn (funext fun i => (dec_val c i).symm)
  unfold vB vcond
  rw [e, e, Bool.and_eq_true, lexB_iff, vert_iff]
  have r0 : dg r 0 = (dec r 0 : ℕ) := (dec_val r 0).symm
  have s0 : dg s 0 = (dec s 0 : ℕ) := (dec_val s 0).symm
  have r1 : dg r 1 = (dec r 1 : ℕ) := (dec_val r 1).symm
  have s1 : dg s 1 = (dec s 1 : ℕ) := (dec_val s 1).symm
  have r2 : dg r 2 = (dec r 2 : ℕ) := (dec_val r 2).symm
  have s2 : dg s 2 = (dec s 2 : ℕ) := (dec_val s 2).symm
  have r3 : dg r 3 = (dec r 3 : ℕ) := (dec_val r 3).symm
  have s3 : dg s 3 = (dec s 3 : ℕ) := (dec_val s 3).symm
  have r4 : dg r 4 = (dec r 4 : ℕ) := (dec_val r 4).symm
  have s4 : dg s 4 = (dec s 4 : ℕ) := (dec_val s 4).symm
  simp only [r0, s0, r1, s1, r2, s2, r3, s3, r4, s4, Bool.and_eq_true, Bool.not_eq_true', Bool.eq_false_iff, ne_eq, md_two,
    and_assoc]

lemma okR_iff (τ : Fin 4 → T2) (s : Fin 5 → Fin 3) :
    okR τ s ↔ okT (τ 0) (s 0) (s 1) ∧ okT (τ 1) (s 1) (s 2) ∧ okT (τ 2) (s 2) (s 3) ∧ okT (τ 3) (s 3) (s 4) := by
  unfold okR
  constructor
  · intro h
    exact ⟨h 0, h 1, h 2, h 3⟩
  · rintro ⟨h0, h1, h2, h3⟩ j
    fin_cases j
    · exact h0
    · exact h1
    · exact h2
    · exact h3

lemma cnt_eq : ∀ (m : ℕ) (t0 t1 t2 t3 : T2) (r : Fin (3 ^ 5)),
    cnt m t0 t1 t2 t3 r = F m ![t0, t1, t2, t3] (dec r)
  | 0, t0, t1, t2, t3, r => by
    rw [cnt, F_zero]
  | m + 1, t0, t1, t2, t3, r => by
    rw [cnt, succL, validRows]
    simp only [sumL_filter]
    rw [sumL_allRows, F_succ, ← Equiv.sum_comp dec]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    simp only [ite_band]
    simp only [mk2_eq, cnt_eq m]
    have d0 : dg s 0 = (dec s 0 : ℕ) := (dec_val s 0).symm
    have d1 : dg s 1 = (dec s 1 : ℕ) := (dec_val s 1).symm
    have d2 : dg s 2 = (dec s 2 : ℕ) := (dec_val s 2).symm
    have d3 : dg s 3 = (dec s 3 : ℕ) := (dec_val s 3).symm
    have d4 : dg s 4 = (dec s 4 : ℕ) := (dec_val s 4).symm
    rw [d0, d1, d2, d3, d4]
    simp only [stpB_eq]
    have hst : stpR ![t0, t1, t2, t3] (dec s) =
        ![stpT t0 (dec s 0) (dec s 1), stpT t1 (dec s 1) (dec s 2), stpT t2 (dec s 2) (dec s 3), stpT t3 (dec s 3) (dec s 4)] := by
      funext j
      fin_cases j <;> rfl
    have hc : (hrowB s && (vB r s && (okB t0 (dec s 0) (dec s 1) && okB t1 (dec s 1) (dec s 2) && okB t2 (dec s 2) (dec s 3) && okB t3 (dec s 3) (dec s 4)))) = true ↔
          (hrow (dec s) ∧ vcond (dec r) (dec s)) ∧ okR ![t0, t1, t2, t3] (dec s) := by
      rw [okR_iff]
      simp only [Bool.and_eq_true, vB_iff, hrowB_iff, okB_iff, and_assoc]
      try exact Iff.rfl
    rw [hst]
    by_cases h : (hrowB s && (vB r s && (okB t0 (dec s 0) (dec s 1) && okB t1 (dec s 1) (dec s 2) && okB t2 (dec s 2) (dec s 3) && okB t3 (dec s 3) (dec s 4)))) = true
    · rw [if_pos h, if_pos (hc.1 h)]
    · rw [if_neg h, if_neg (fun h' => h (hc.2 h'))]

lemma cnt_succ (m : ℕ) (t0 t1 t2 t3 : T2) (r : Fin (3 ^ 5)) :
    cnt (m + 1) t0 t1 t2 t3 r = ∑ s : Fin (3 ^ 5),
      if (hrowB s && (vB r s && (okB t0 (dg s 0) (dg s 1) && okB t1 (dg s 1) (dg s 2) && okB t2 (dg s 2) (dg s 3) && okB t3 (dg s 3) (dg s 4)))) = true then
        cnt m (stpB t0 (dg s 0) (dg s 1)) (stpB t1 (dg s 1) (dg s 2)) (stpB t2 (dg s 2) (dg s 3)) (stpB t3 (dg s 3) (dg s 4)) s
      else 0 := by
  rw [cnt, succL, validRows]
  simp only [sumL_filter]
  rw [sumL_allRows]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  simp only [ite_band, mk2_eq]

def Sa (m : ℕ) : ℕ := sumL validRows (fun s : Fin (3 ^ 5) =>
    if okB .z (dg s 0) (dg s 1) && okB .z (dg s 1) (dg s 2) && okB .z (dg s 2) (dg s 3) && okB .z (dg s 3) (dg s 4) then
      cnt m (stpB .z (dg s 0) (dg s 1)) (stpB .z (dg s 1) (dg s 2)) (stpB .z (dg s 2) (dg s 3)) (stpB .z (dg s 3) (dg s 4)) s
    else 0)

lemma a_succ' (m : ℕ) : a (m + 1) = Sa m := by
  unfold Sa
  rw [validRows, sumL_filter, sumL_allRows, a_succ, ← Equiv.sum_comp dec]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [ite_band, cnt_eq]
  have d0 : dg s 0 = (dec s 0 : ℕ) := (dec_val s 0).symm
  have d1 : dg s 1 = (dec s 1 : ℕ) := (dec_val s 1).symm
  have d2 : dg s 2 = (dec s 2 : ℕ) := (dec_val s 2).symm
  have d3 : dg s 3 = (dec s 3 : ℕ) := (dec_val s 3).symm
  have d4 : dg s 4 = (dec s 4 : ℕ) := (dec_val s 4).symm
  rw [d0, d1, d2, d3, d4]
  simp only [stpB_eq]
  have hst : stpR (fun _ => .z) (dec s) =
      ![stpT .z (dec s 0) (dec s 1), stpT .z (dec s 1) (dec s 2), stpT .z (dec s 2) (dec s 3), stpT .z (dec s 3) (dec s 4)] := by
    funext j
    fin_cases j <;> rfl
  have hc : (hrowB s && (okB .z (dec s 0) (dec s 1) && okB .z (dec s 1) (dec s 2) && okB .z (dec s 2) (dec s 3) && okB .z (dec s 3) (dec s 4))) = true ↔ hrow (dec s) ∧ okR (fun _ => .z) (dec s) := by
    rw [okR_iff]
    simp only [Bool.and_eq_true, hrowB_iff, okB_iff, and_assoc]
    try exact Iff.rfl
  rw [hst]
  by_cases h : (hrowB s && (okB .z (dec s 0) (dec s 1) && okB .z (dec s 1) (dec s 2) && okB .z (dec s 2) (dec s 3) && okB .z (dec s 3) (dec s 4))) = true
  · rw [if_pos h, if_pos (hc.1 h)]
  · rw [if_neg h, if_neg (fun h' => h (hc.2 h'))]

/-! ## The relation for every reachable state -/

/-- The status as a digit. -/
def t2v : T2 → ℕ
  | .z => 0
  | .d => 1

/-- The states reachable from the first row, as a bit mask indexed by
(Sum_j t2v t_j 2^j) * 243 + r (computed by a search outside Lean; `chk` checks that it holds the
starting states and is closed under the transitions). -/
def reachB (t0 t1 t2 t3 : T2) (r : Fin (3 ^ 5)) : Bool :=
  Nat.testBit 0x800000000000000130104000000804c00000000000000004026000004800100000000000000022000800000100880000000000000000804400000800020000000000000000c00100000020030000000000000000100180000020004000000000000000080020000004002000000000000000020010000000000800000000000000000184000000004c00000000000000000026000000004100000000000000000010800000000880000000000000000004400000000020000000000000000000500000000030000000000000000000180000000004000000000000000000060000000002000000000000000000010000000000800006000000000000000000000804c00000000000000000000000004c04100000400000000000000000000100880000000000000000000000000880020000010000000000000000000020030000000000000000000000000030004000001000000000000000000004002000000000000000000000000002000810000000000000000000000000004c00000000000000000000000000006101000000000000000000000000000880000000000000000000000000000428000000000000000000000000000030000000000000000000000000000014000000000000000000000000000002000000000000000000000000000001 ((t2v t0 + 2 * (t2v t1 + 2 * (t2v t2 + 2 * (t2v t3)))) * 243 + r)

/-- The relation Sum_i (-1)^i C(11, i) W(m + 11 - i) = 0, negative terms on the right. -/
def RL (m : ℕ) (t0 t1 t2 t3 : T2) (r : Fin (3 ^ 5)) : ℕ :=
  cnt (m + 11) t0 t1 t2 t3 r + 55 * cnt (m + 9) t0 t1 t2 t3 r + 330 * cnt (m + 7) t0 t1 t2 t3 r + 462 * cnt (m + 5) t0 t1 t2 t3 r + 165 * cnt (m + 3) t0 t1 t2 t3 r + 11 * cnt (m + 1) t0 t1 t2 t3 r

def RR (m : ℕ) (t0 t1 t2 t3 : T2) (r : Fin (3 ^ 5)) : ℕ :=
  11 * cnt (m + 10) t0 t1 t2 t3 r + 165 * cnt (m + 8) t0 t1 t2 t3 r + 462 * cnt (m + 6) t0 t1 t2 t3 r + 330 * cnt (m + 4) t0 t1 t2 t3 r + 55 * cnt (m + 2) t0 t1 t2 t3 r + cnt m t0 t1 t2 t3 r

/-- The starting state of the first row s is in the mask. -/
def fA (s : Fin (3 ^ 5)) : Bool := !(hrowB s && (okB .z (dg s 0) (dg s 1) && okB .z (dg s 1) (dg s 2) && okB .z (dg s 2) (dg s 3) && okB .z (dg s 3) (dg s 4))) || reachB (stpB .z (dg s 0) (dg s 1)) (stpB .z (dg s 1) (dg s 2)) (stpB .z (dg s 2) (dg s 3)) (stpB .z (dg s 3) (dg s 4)) s

/-- The successor of the state (t0 t1 t2 t3, r) by the row s is in the mask. -/
def fN (t0 t1 t2 t3 : T2) (s : Fin (3 ^ 5)) : Bool :=
  !(okB t0 (dg s 0) (dg s 1) && okB t1 (dg s 1) (dg s 2) && okB t2 (dg s 2) (dg s 3) && okB t3 (dg s 3) (dg s 4)) || reachB (stpB t0 (dg s 0) (dg s 1)) (stpB t1 (dg s 1) (dg s 2)) (stpB t2 (dg s 2) (dg s 3)) (stpB t3 (dg s 3) (dg s 4)) s

/-- For a state in the mask: all successors are in the mask and the relation holds at m = 0. -/
def fB (t0 t1 t2 t3 : T2) (r : Fin (3 ^ 5)) : Bool :=
  !reachB t0 t1 t2 t3 r || ((succL r).all (fun s => fN t0 t1 t2 t3 s) && RL 0 t0 t1 t2 t3 r == RR 0 t0 t1 t2 t3 r)

/-- The first values a(1..11). -/
def fS : Bool := Sa 0 == 7 && Sa 1 == 19 && Sa 2 == 60 && Sa 3 == 212 && Sa 4 == 753 && Sa 5 == 2546 && Sa 6 == 8024 &&
  Sa 7 == 23428 && Sa 8 == 63430 && Sa 9 == 159945 && Sa 10 == 377840

def T2s : List T2 := [.z, .d]

/-- Everything the kernel computes, in one Boolean so that the evaluated counts are shared. -/
def chk : Bool :=
  allRows.all fA && T2s.all (fun t0 => T2s.all (fun t1 => T2s.all (fun t2 => T2s.all (fun t3 => allRows.all (fun r => fB t0 t1 t2 t3 r))))) && fS

lemma chk_true : chk = true := by decide +kernel

lemma allRows_all {p : Fin (3 ^ 5) → Bool} (h : allRows.all p = true) (s : Fin (3 ^ 5)) :
    p s = true := List.all_eq_true.1 h s (List.mem_finRange s)

lemma T2s_all {p : T2 → Bool} (h : T2s.all p = true) (t : T2) : p t = true :=
  List.all_eq_true.1 h t (by cases t <;> simp [T2s])

lemma imp_of_bool {b c : Bool} (h : (!b || c) = true) (hb : b = true) : c = true := by
  cases b <;> cases c <;> simp_all

lemma chk_parts : (∀ s, fA s = true) ∧ (∀ (t0 t1 t2 t3 : T2) r, fB t0 t1 t2 t3 r = true) ∧ fS = true := by
  have h := chk_true
  simp only [chk, Bool.and_eq_true] at h
  exact ⟨fun s => allRows_all h.1.1 s, fun t0 t1 t2 t3 r => allRows_all (T2s_all (T2s_all (T2s_all (T2s_all (h.1.2) t0) t1) t2) t3) r, h.2⟩

lemma reach_init : ∀ s : Fin (3 ^ 5), (hrowB s && (okB .z (dg s 0) (dg s 1) && okB .z (dg s 1) (dg s 2) && okB .z (dg s 2) (dg s 3) && okB .z (dg s 3) (dg s 4))) = true →
    reachB (stpB .z (dg s 0) (dg s 1)) (stpB .z (dg s 1) (dg s 2)) (stpB .z (dg s 2) (dg s 3)) (stpB .z (dg s 3) (dg s 4)) s = true := fun s hs => imp_of_bool (chk_parts.1 s) hs

lemma fB_parts (t0 t1 t2 t3 : T2) (r : Fin (3 ^ 5)) (hr : reachB t0 t1 t2 t3 r = true) :
    (∀ s ∈ succL r, fN t0 t1 t2 t3 s = true) ∧ RL 0 t0 t1 t2 t3 r = RR 0 t0 t1 t2 t3 r := by
  have h := chk_parts.2.1 t0 t1 t2 t3 r
  unfold fB at h
  rw [hr] at h
  simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨List.all_eq_true.1 h.1, h.2⟩

lemma reach_next : ∀ (t0 t1 t2 t3 : T2) (r : Fin (3 ^ 5)), reachB t0 t1 t2 t3 r = true →
    ∀ s : Fin (3 ^ 5), (hrowB s && (vB r s && (okB t0 (dg s 0) (dg s 1) && okB t1 (dg s 1) (dg s 2) && okB t2 (dg s 2) (dg s 3) && okB t3 (dg s 3) (dg s 4)))) = true →
      reachB (stpB t0 (dg s 0) (dg s 1)) (stpB t1 (dg s 1) (dg s 2)) (stpB t2 (dg s 2) (dg s 3)) (stpB t3 (dg s 3) (dg s 4)) s = true := by
  intro t0 t1 t2 t3 r hr s hs
  rw [Bool.and_eq_true, Bool.and_eq_true] at hs
  have hm : s ∈ succL r :=
    List.mem_filter.2 ⟨List.mem_filter.2 ⟨List.mem_finRange s, hs.1⟩, hs.2.1⟩
  exact imp_of_bool ((fB_parts t0 t1 t2 t3 r hr).1 s hm) hs.2.2

lemma R_base : ∀ (t0 t1 t2 t3 : T2) (r : Fin (3 ^ 5)), reachB t0 t1 t2 t3 r = true →
    RL 0 t0 t1 t2 t3 r = RR 0 t0 t1 t2 t3 r := fun t0 t1 t2 t3 r hr => (fB_parts t0 t1 t2 t3 r hr).2

lemma kernel_facts : Sa 0 = 7 ∧ Sa 1 = 19 ∧ Sa 2 = 60 ∧ Sa 3 = 212 ∧ Sa 4 = 753 ∧ Sa 5 = 2546 ∧ Sa 6 = 8024 ∧
    Sa 7 = 23428 ∧ Sa 8 = 63430 ∧ Sa 9 = 159945 ∧ Sa 10 = 377840 := by
  have h := chk_parts.2.2
  simp only [fS, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1.1.1.1.1.1.1.1, h.1.1.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.2, h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

lemma R_all (m : ℕ) : ∀ (t0 t1 t2 t3 : T2) (r : Fin (3 ^ 5)), reachB t0 t1 t2 t3 r = true →
    RL m t0 t1 t2 t3 r = RR m t0 t1 t2 t3 r := by
  induction m with
  | zero => exact R_base
  | succ m ih =>
    intro t0 t1 t2 t3 r h
    unfold RL RR
    rw [show m + 1 + 11 = (m + 11) + 1 from rfl, show m + 1 + 10 = (m + 10) + 1 from rfl, show m + 1 + 9 = (m + 9) + 1 from rfl, show m + 1 + 8 = (m + 8) + 1 from rfl, show m + 1 + 7 = (m + 7) + 1 from rfl, show m + 1 + 6 = (m + 6) + 1 from rfl, show m + 1 + 5 = (m + 5) + 1 from rfl, show m + 1 + 4 = (m + 4) + 1 from rfl, show m + 1 + 3 = (m + 3) + 1 from rfl, show m + 1 + 2 = (m + 2) + 1 from rfl, show m + 1 + 1 = (m + 1) + 1 from rfl,
      cnt_succ (m + 11), cnt_succ (m + 10), cnt_succ (m + 9), cnt_succ (m + 8), cnt_succ (m + 7), cnt_succ (m + 6), cnt_succ (m + 5), cnt_succ (m + 4), cnt_succ (m + 3), cnt_succ (m + 2), cnt_succ (m + 1), cnt_succ m]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    split_ifs with hc
    · exact ih _ _ _ _ s (reach_next t0 t1 t2 t3 r h s hc)
    · simp

/-! ## Barker's recurrence and g.f. -/

lemma a_rel (n : ℕ) : a (n + 12) + 55 * a (n + 10) + 330 * a (n + 8) + 462 * a (n + 6) + 165 * a (n + 4) + 11 * a (n + 2) =
    11 * a (n + 11) + 165 * a (n + 9) + 462 * a (n + 7) + 330 * a (n + 5) + 55 * a (n + 3) + a (n + 1) := by
  rw [show n + 12 = (n + 11) + 1 from rfl, show n + 11 = (n + 10) + 1 from rfl, show n + 10 = (n + 9) + 1 from rfl, show n + 9 = (n + 8) + 1 from rfl, show n + 8 = (n + 7) + 1 from rfl, show n + 7 = (n + 6) + 1 from rfl, show n + 6 = (n + 5) + 1 from rfl, show n + 5 = (n + 4) + 1 from rfl, show n + 4 = (n + 3) + 1 from rfl, show n + 3 = (n + 2) + 1 from rfl, show n + 2 = (n + 1) + 1 from rfl,
    a_succ' (n + 11), a_succ' (n + 10), a_succ' (n + 9), a_succ' (n + 8), a_succ' (n + 7), a_succ' (n + 6), a_succ' (n + 5), a_succ' (n + 4), a_succ' (n + 3), a_succ' (n + 2), a_succ' (n + 1), a_succ' n]
  simp only [Sa, validRows, sumL_filter, sumL_allRows]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  simp only [ite_band]
  split_ifs with hc
  · exact R_all n _ _ _ _ s (reach_init s hc)
  · simp

lemma a_v1 : a 1 = 7 := (a_succ' 0).trans kernel_facts.1
lemma a_v2 : a 2 = 19 := (a_succ' 1).trans kernel_facts.2.1
lemma a_v3 : a 3 = 60 := (a_succ' 2).trans kernel_facts.2.2.1
lemma a_v4 : a 4 = 212 := (a_succ' 3).trans kernel_facts.2.2.2.1
lemma a_v5 : a 5 = 753 := (a_succ' 4).trans kernel_facts.2.2.2.2.1
lemma a_v6 : a 6 = 2546 := (a_succ' 5).trans kernel_facts.2.2.2.2.2.1
lemma a_v7 : a 7 = 8024 := (a_succ' 6).trans kernel_facts.2.2.2.2.2.2.1
lemma a_v8 : a 8 = 23428 := (a_succ' 7).trans kernel_facts.2.2.2.2.2.2.2.1
lemma a_v9 : a 9 = 63430 := (a_succ' 8).trans kernel_facts.2.2.2.2.2.2.2.2.1
lemma a_v10 : a 10 = 159945 := (a_succ' 9).trans kernel_facts.2.2.2.2.2.2.2.2.2.1
lemma a_v11 : a 11 = 377840 := (a_succ' 10).trans kernel_facts.2.2.2.2.2.2.2.2.2.2

/-- Barker's recurrence, for n > 11. -/
theorem recurrence (n : ℕ) (hn : 11 < n) :
    (a n : ℤ) = 11 * a (n - 1) - 55 * a (n - 2) + 165 * a (n - 3) - 330 * a (n - 4) + 462 * a (n - 5) - 462 * a (n - 6) + 330 * a (n - 7) - 165 * a (n - 8) + 55 * a (n - 9) - 11 * a (n - 10) + a (n - 11) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 12 := ⟨n - 12, by omega⟩
  have h := a_rel k
  simp only [show k + 12 - 1 = k + 11 by omega, show k + 12 - 2 = k + 10 by omega, show k + 12 - 3 = k + 9 by omega, show k + 12 - 4 = k + 8 by omega, show k + 12 - 5 = k + 7 by omega, show k + 12 - 6 = k + 6 by omega, show k + 12 - 7 = k + 5 by omega, show k + 12 - 8 = k + 4 by omega, show k + 12 - 9 = k + 3 by omega, show k + 12 - 10 = k + 2 by omega, show k + 12 - 11 = k + 1 by omega]
  have h' : (a (k + 12) : ℤ) + 55 * a (k + 10) + 330 * a (k + 8) + 462 * a (k + 6) + 165 * a (k + 4) + 11 * a (k + 2) =
      11 * (a (k + 11) : ℤ) + 165 * a (k + 9) + 462 * a (k + 7) + 330 * a (k + 5) + 55 * a (k + 3) + a (k + 1) := by exact_mod_cast h
  linarith

/-- Barker's g.f.: (Sum_{n >= 1} a(n) x^n) (1 - x)^11 = numerator. -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 11 =
      X * (7 - 58 * X + 236 * X ^ 2 - 558 * X ^ 3 + 896 * X ^ 4 - 941 * X ^ 5 + 709 * X ^ 6 - 343 * X ^ 7 + 103 * X ^ 8 - 17 * X ^ 9 + X ^ 10) := by
  set A : ℚ⟦X⟧ := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have e1 : A * (1 - X) ^ 11 =
      A - C 11 * (A * X ^ 1) + C 55 * (A * X ^ 2) - C 165 * (A * X ^ 3) + C 330 * (A * X ^ 4) - C 462 * (A * X ^ 5) + C 462 * (A * X ^ 6) - C 330 * (A * X ^ 7) + C 165 * (A * X ^ 8) - C 55 * (A * X ^ 9) + C 11 * (A * X ^ 10) - A * X ^ 11 := by
    simp only [map_ofNat]; ring
  have e2 : (X * (7 - 58 * X + 236 * X ^ 2 - 558 * X ^ 3 + 896 * X ^ 4 - 941 * X ^ 5 + 709 * X ^ 6 - 343 * X ^ 7 + 103 * X ^ 8 - 17 * X ^ 9 + X ^ 10) : ℚ⟦X⟧) =
      X ^ 1 * C 7 - X ^ 2 * C 58 + X ^ 3 * C 236 - X ^ 4 * C 558 + X ^ 5 * C 896 - X ^ 6 * C 941 + X ^ 7 * C 709 - X ^ 8 * C 343 + X ^ 9 * C 103 - X ^ 10 * C 17 + X ^ 11 := by
    simp only [map_ofNat]; ring
  rw [e1, e2]
  ext n
  have hc : ∀ k, coeff k A = if k = 0 then (0 : ℚ) else a k := fun k => by rw [hA, coeff_mk]
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_C, coeff_X_pow, coeff_mul_X_pow',
    hc]
  have v1 := a_v1
  have v2 := a_v2
  have v3 := a_v3
  have v4 := a_v4
  have v5 := a_v5
  have v6 := a_v6
  have v7 := a_v7
  have v8 := a_v8
  have v9 := a_v9
  have v10 := a_v10
  have v11 := a_v11
  rcases Nat.lt_or_ge n 12 with hn | hn
  · interval_cases n <;> simp_all <;> norm_num
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 12 := ⟨n - 12, by omega⟩
    have h := a_rel k
    have hq : (a (k + 12) : ℚ) + 55 * a (k + 10) + 330 * a (k + 8) + 462 * a (k + 6) + 165 * a (k + 4) + 11 * a (k + 2) =
        11 * (a (k + 11) : ℚ) + 165 * a (k + 9) + 462 * a (k + 7) + 330 * a (k + 5) + 55 * a (k + 3) + a (k + 1) := by exact_mod_cast h
    simp only [show k + 12 - 1 = k + 11 by omega,
      show k + 12 - 2 = k + 10 by omega,
      show k + 12 - 3 = k + 9 by omega,
      show k + 12 - 4 = k + 8 by omega,
      show k + 12 - 5 = k + 7 by omega,
      show k + 12 - 6 = k + 6 by omega,
      show k + 12 - 7 = k + 5 by omega,
      show k + 12 - 8 = k + 4 by omega,
      show k + 12 - 9 = k + 3 by omega,
      show k + 12 - 10 = k + 2 by omega,
      show k + 12 - 11 = k + 1 by omega,
      show ¬ k + 12 = 0 by omega,
      show ¬ k + 11 = 0 by omega,
      show ¬ k + 10 = 0 by omega,
      show ¬ k + 9 = 0 by omega,
      show ¬ k + 8 = 0 by omega,
      show ¬ k + 7 = 0 by omega,
      show ¬ k + 6 = 0 by omega,
      show ¬ k + 5 = 0 by omega,
      show ¬ k + 4 = 0 by omega,
      show ¬ k + 3 = 0 by omega,
      show ¬ k + 2 = 0 by omega,
      show ¬ k + 1 = 0 by omega,
      show 1 ≤ k + 12 by omega,
      show 2 ≤ k + 12 by omega,
      show 3 ≤ k + 12 by omega,
      show 4 ≤ k + 12 by omega,
      show 5 ≤ k + 12 by omega,
      show 6 ≤ k + 12 by omega,
      show 7 ≤ k + 12 by omega,
      show 8 ≤ k + 12 by omega,
      show 9 ≤ k + 12 by omega,
      show 10 ≤ k + 12 by omega,
      show 11 ≤ k + 12 by omega,
      show ¬ k + 12 = 1 by omega,
      show ¬ k + 12 = 2 by omega,
      show ¬ k + 12 = 3 by omega,
      show ¬ k + 12 = 4 by omega,
      show ¬ k + 12 = 5 by omega,
      show ¬ k + 12 = 6 by omega,
      show ¬ k + 12 = 7 by omega,
      show ¬ k + 12 = 8 by omega,
      show ¬ k + 12 = 9 by omega,
      show ¬ k + 12 = 10 by omega,
      show ¬ k + 12 = 11 by omega, if_true, if_false]
    linear_combination hq

/-- Both of Barker's conjectures. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 11 =
      X * (7 - 58 * X + 236 * X ^ 2 - 558 * X ^ 3 + 896 * X ^ 4 - 941 * X ^ 5 + 709 * X ^ 6 - 343 * X ^ 7 + 103 * X ^ 8 - 17 * X ^ 9 + X ^ 10) ∧
    ∀ n : ℕ, 11 < n →
      (a n : ℤ) = 11 * a (n - 1) - 55 * a (n - 2) + 165 * a (n - 3) - 330 * a (n - 4) + 462 * a (n - 5) - 462 * a (n - 6) + 330 * a (n - 7) - 165 * a (n - 8) + 55 * a (n - 9) - 11 * a (n - 10) + a (n - 11) :=
  ⟨gf, recurrence⟩

/-- Controls: the entry's data a(1..27), from a(1..11) and the relation (proved for an
abstract sequence f, so that no tactic unfolds `a`). -/
theorem controls :
    a 1 = 7 ∧ a 2 = 19 ∧ a 3 = 60 ∧ a 4 = 212 ∧ a 5 = 753 ∧ a 6 = 2546 ∧ a 7 = 8024 ∧ a 8 = 23428 ∧
    a 9 = 63430 ∧ a 10 = 159945 ∧ a 11 = 377840 ∧ a 12 = 841419 ∧ a 13 = 1777036 ∧ a 14 = 3578998 ∧
    a 15 = 6908102 ∧ a 16 = 12834739 ∧ a 17 = 23041529 ∧ a 18 = 40103959 ∧ a 19 = 67871516 ∧
    a 20 = 111976374 ∧ a 21 = 180501843 ∧ a 22 = 284848554 ∧ a 23 = 440842772 ∧ a 24 = 670138334 ∧
    a 25 = 1001971536 ∧ a 26 = 1475336877 ∧ a 27 = 2141660944 := by
  have key : ∀ f : ℕ → ℕ, f 1 = 7 → f 2 = 19 → f 3 = 60 → f 4 = 212 → f 5 = 753 → f 6 = 2546 → f 7 = 8024 → f 8 = 23428 → f 9 = 63430 → f 10 = 159945 → f 11 = 377840 →
      (∀ n, f (n + 12) + 55 * f (n + 10) + 330 * f (n + 8) + 462 * f (n + 6) + 165 * f (n + 4) + 11 * f (n + 2) = 11 * f (n + 11) + 165 * f (n + 9) + 462 * f (n + 7) + 330 * f (n + 5) + 55 * f (n + 3) + f (n + 1)) →
        f 1 = 7 ∧ f 2 = 19 ∧ f 3 = 60 ∧ f 4 = 212 ∧ f 5 = 753 ∧ f 6 = 2546 ∧ f 7 = 8024 ∧
        f 8 = 23428 ∧ f 9 = 63430 ∧ f 10 = 159945 ∧ f 11 = 377840 ∧ f 12 = 841419 ∧ f 13 = 1777036 ∧
        f 14 = 3578998 ∧ f 15 = 6908102 ∧ f 16 = 12834739 ∧ f 17 = 23041529 ∧ f 18 = 40103959 ∧
        f 19 = 67871516 ∧ f 20 = 111976374 ∧ f 21 = 180501843 ∧ f 22 = 284848554 ∧ f 23 = 440842772 ∧
        f 24 = 670138334 ∧ f 25 = 1001971536 ∧ f 26 = 1475336877 ∧ f 27 = 2141660944 := by
    intro f h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 hr
    have h12 : f 12 = 841419 := by
      have r := hr 0
      simp only [Nat.reduceAdd, Nat.reduceMul, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11] at r
      omega
    have h13 : f 13 = 1777036 := by
      have r := hr 1
      simp only [Nat.reduceAdd, Nat.reduceMul, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12] at r
      omega
    have h14 : f 14 = 3578998 := by
      have r := hr 2
      simp only [Nat.reduceAdd, Nat.reduceMul, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13] at r
      omega
    have h15 : f 15 = 6908102 := by
      have r := hr 3
      simp only [Nat.reduceAdd, Nat.reduceMul, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14] at r
      omega
    have h16 : f 16 = 12834739 := by
      have r := hr 4
      simp only [Nat.reduceAdd, Nat.reduceMul, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15] at r
      omega
    have h17 : f 17 = 23041529 := by
      have r := hr 5
      simp only [Nat.reduceAdd, Nat.reduceMul, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16] at r
      omega
    have h18 : f 18 = 40103959 := by
      have r := hr 6
      simp only [Nat.reduceAdd, Nat.reduceMul, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17] at r
      omega
    have h19 : f 19 = 67871516 := by
      have r := hr 7
      simp only [Nat.reduceAdd, Nat.reduceMul, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18] at r
      omega
    have h20 : f 20 = 111976374 := by
      have r := hr 8
      simp only [Nat.reduceAdd, Nat.reduceMul, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19] at r
      omega
    have h21 : f 21 = 180501843 := by
      have r := hr 9
      simp only [Nat.reduceAdd, Nat.reduceMul, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20] at r
      omega
    have h22 : f 22 = 284848554 := by
      have r := hr 10
      simp only [Nat.reduceAdd, Nat.reduceMul, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21] at r
      omega
    have h23 : f 23 = 440842772 := by
      have r := hr 11
      simp only [Nat.reduceAdd, Nat.reduceMul, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22] at r
      omega
    have h24 : f 24 = 670138334 := by
      have r := hr 12
      simp only [Nat.reduceAdd, Nat.reduceMul, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23] at r
      omega
    have h25 : f 25 = 1001971536 := by
      have r := hr 13
      simp only [Nat.reduceAdd, Nat.reduceMul, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24] at r
      omega
    have h26 : f 26 = 1475336877 := by
      have r := hr 14
      simp only [Nat.reduceAdd, Nat.reduceMul, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25] at r
      omega
    have h27 : f 27 = 2141660944 := by
      have r := hr 15
      simp only [Nat.reduceAdd, Nat.reduceMul, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26] at r
      omega
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27⟩
  exact key a a_v1 a_v2 a_v3 a_v4 a_v5 a_v6 a_v7 a_v8 a_v9 a_v10 a_v11 a_rel

/-- Control by direct enumeration of all arrays with 1 row(s): a(1) = 7. -/
theorem control_direct :
    ((univ : Finset (Fin 1 → Fin 5 → Fin 3)).filter good).card = 7 := by
  decide +kernel

end OMA.S_oeis_a229442

theorem OMA.solution : type_of% @OMA.S_oeis_a229442.main :=
  OMA.S_oeis_a229442.conjecture
