import OMAStatements.S_oeis_a201372

namespace OMA.S_oeis_a201372

open PowerSeries Finset


instance {m q : ℕ} : DecidableRel (@lexLE m q) := fun u v => by unfold lexLE; infer_instance



instance {n : ℕ} : DecidablePred (@good n) := fun x => by unfold good; infer_instance


/-! ## Lexicographic orders on `Fin.cons` -/

/-- Strict lexicographic order. -/
def lexLT {m q : ℕ} (u v : Fin m → Fin q) : Prop :=
  ∃ i : Fin m, (∀ j : Fin m, j < i → u j = v j) ∧ u i < v i

/-- Strict lexicographic order comparing from the last entry. -/
def revLT {m q : ℕ} (u v : Fin m → Fin q) : Prop :=
  ∃ i : Fin m, (∀ j : Fin m, i < j → u j = v j) ∧ u i < v i

instance {m q : ℕ} : DecidableRel (@revLT m q) := fun u v => by unfold revLT; infer_instance

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

lemma revLT_cons {m q : ℕ} (a b : Fin q) (u v : Fin m → Fin q) :
    revLT (Fin.cons a u : Fin (m + 1) → Fin q) (Fin.cons b v) ↔ revLT u v ∨ (u = v ∧ a < b) := by
  constructor
  · rintro ⟨i, hi, hlt⟩
    induction i using Fin.cases with
    | zero =>
      right
      refine ⟨funext fun j => ?_, by simpa using hlt⟩
      simpa using hi j.succ (Fin.succ_pos j)
    | succ i =>
      left
      refine ⟨i, fun j hj => ?_, by simpa using hlt⟩
      simpa using hi j.succ (Fin.succ_lt_succ_iff.2 hj)
  · rintro (⟨i, hi, hlt⟩ | ⟨rfl, h⟩)
    · refine ⟨i.succ, fun j hj => ?_, by simpa using hlt⟩
      induction j using Fin.cases with
      | zero => exact absurd hj (Fin.not_lt_zero _)
      | succ j => simpa using hi j (Fin.succ_lt_succ_iff.1 hj)
    · refine ⟨0, fun j hj => ?_, by simpa using h⟩
      induction j using Fin.cases with
      | zero => exact absurd hj (lt_irrefl _)
      | succ j => rfl

lemma bwd_inj {m q : ℕ} (u v : Fin m → Fin q) : bwd u = bwd v ↔ u = v := by
  constructor
  · intro h
    funext i
    have := congrFun h (Fin.rev i)
    simpa [bwd] using this
  · rintro rfl
    rfl

lemma lexLT_bwd {m q : ℕ} (u v : Fin m → Fin q) : lexLT (bwd u) (bwd v) ↔ revLT u v := by
  constructor
  · rintro ⟨i, hi, hlt⟩
    refine ⟨Fin.rev i, fun j hj => ?_, by simpa [bwd] using hlt⟩
    have hj' : Fin.rev j < i := by
      have := (Fin.rev_lt_rev (i := j) (j := Fin.rev i)).2 hj
      simpa using this
    have := hi (Fin.rev j) hj'
    simpa [bwd] using this
  · rintro ⟨i, hi, hlt⟩
    refine ⟨Fin.rev i, fun j hj => ?_, by simpa [bwd] using hlt⟩
    have hj' : i < Fin.rev j := by
      have := (Fin.rev_lt_rev (i := Fin.rev i) (j := j)).2 hj
      simpa using this
    have := hi (Fin.rev j) hj'
    simpa [bwd] using this

lemma lexLE_bwd {m q : ℕ} (u v : Fin m → Fin q) : lexLE (bwd u) (bwd v) ↔ u = v ∨ revLT u v := by
  unfold lexLE
  rw [bwd_inj]
  exact or_congr Iff.rfl (lexLT_bwd u v)

/-! ## The status of a pair of columns -/

/-- z: no difference yet; l: the last difference had the left column smaller; g: the last
difference had the left column larger (the first one had it smaller). -/
inductive T3
  | z
  | l
  | g
  deriving DecidableEq

instance : Fintype T3 := ⟨{.z, .l, .g}, fun t => by cases t <;> simp⟩

/-- The condition that the rest (u, v) of a pair of columns must satisfy after the status t. -/
def PT {m q : ℕ} : T3 → (Fin m → Fin q) → (Fin m → Fin q) → Prop
  | .z, u, v => lexLE u v ∧ lexLE (bwd v) (bwd u)
  | .l, u, v => revLT v u
  | .g, u, v => v = u ∨ revLT v u

instance {m q : ℕ} (t : T3) (u v : Fin m → Fin q) : Decidable (PT t u v) := by
  cases t <;> unfold PT <;> infer_instance

/-- The entries (x, y) of the next row in the two columns are allowed after the status t. -/
def okT {q : ℕ} (t : T3) (x y : Fin q) : Prop := t = .z → x ≤ y

/-- The status after the entries (x, y). -/
def stpT {q : ℕ} (t : T3) (x y : Fin q) : T3 := if x = y then t else if x < y then .l else .g

/-- The status t is acceptable at the end of the array. -/
def accT (t : T3) : Prop := t ≠ .l

lemma stpT_lt {q : ℕ} (t : T3) {x y : Fin q} (h : x < y) : stpT t x y = .l := by
  simp [stpT, ne_of_lt h, h]

lemma stpT_self {q : ℕ} (t : T3) (x : Fin q) : stpT t x x = t := by
  simp [stpT]

lemma stpT_gt {q : ℕ} (t : T3) {x y : Fin q} (h : y < x) : stpT t x y = .g := by
  simp [stpT, ne_of_gt h, lt_asymm h]

lemma PT_cons {m q : ℕ} (t : T3) (x y : Fin q) (u v : Fin m → Fin q) :
    PT t (Fin.cons x u : Fin (m + 1) → Fin q) (Fin.cons y v) ↔ okT t x y ∧ PT (stpT t x y) u v := by
  rcases lt_trichotomy x y with h | rfl | h
  · have h1 : x ≠ y := ne_of_lt h
    have h2 : ¬ y < x := lt_asymm h
    have h3 : y ≠ x := fun e => h1 e.symm
    have h4 : x ≤ y := le_of_lt h
    rw [stpT_lt t h]
    cases t <;>
      simp only [PT, okT, lexLE_cons, lexLE_bwd, revLT_cons, Fin.cons_inj, h, h1, h2, h3, h4] <;>
      tauto
  · rw [stpT_self]
    cases t <;>
      simp only [PT, okT, lexLE_cons, lexLE_bwd, revLT_cons, Fin.cons_inj, lt_irrefl, le_refl] <;>
      tauto
  · have h1 : x ≠ y := ne_of_gt h
    have h2 : ¬ x < y := lt_asymm h
    have h3 : ¬ x ≤ y := not_le.2 h
    have h4 : y ≠ x := fun e => h1 e.symm
    rw [stpT_gt t h]
    cases t <;>
      simp only [PT, okT, lexLE_cons, lexLE_bwd, revLT_cons, Fin.cons_inj, h, h1, h2, h3, h4] <;>
      tauto

instance {q : ℕ} (t : T3) (x y : Fin q) : Decidable (okT t x y) := by
  unfold okT; infer_instance

instance (t : T3) : Decidable (accT t) := by
  unfold accT; infer_instance

lemma PT_nil {q : ℕ} (t : T3) (u v : Fin 0 → Fin q) : PT t u v ↔ accT t := by
  have huv : ∀ w w' : Fin 0 → Fin q, w = w' := fun w w' => funext fun i => i.elim0
  have hr : ∀ w w' : Fin 0 → Fin q, ¬ revLT w w' := fun w w' ⟨i, _⟩ => i.elim0
  cases t
  · exact ⟨fun _ => by decide, fun _ => ⟨Or.inl (huv u v), Or.inl (huv _ _)⟩⟩
  · exact ⟨fun h => absurd h (hr v u), fun h => absurd rfl h⟩
  · exact ⟨fun _ => by decide, fun _ => Or.inl (huv v u)⟩

/-! ## Arrays read row by row -/

/-- The row conditions between consecutive rows. -/
def chain {m : ℕ} (f : Fin m → Fin 5 → Fin 2) : Prop :=
  ∀ i i' : Fin m, i.val + 1 = i'.val → PT .z (f i) (f i')

instance {m : ℕ} : DecidablePred (@chain m) := fun f => by unfold chain; infer_instance

lemma chain_cons2 {m : ℕ} (r s : Fin 5 → Fin 2) (g : Fin m → Fin 5 → Fin 2) :
    chain (Fin.cons r (Fin.cons s g) : Fin (m + 2) → Fin 5 → Fin 2) ↔
      PT .z r s ∧ chain (Fin.cons s g : Fin (m + 1) → Fin 5 → Fin 2) := by
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

lemma chain_one (f : Fin 1 → Fin 5 → Fin 2) : chain f := by
  intro i j hij
  have := j.isLt
  have := i.isLt
  omega

/-- Column j of the array f. -/
def col {m : ℕ} (f : Fin m → Fin 5 → Fin 2) (j : Fin 5) : Fin m → Fin 2 := fun i => f i j

/-- The rows f continue the row r validly, when the column pairs have statuses τ after r. -/
def Cont {m : ℕ} (τ : Fin 4 → T3) (r : Fin 5 → Fin 2) (f : Fin m → Fin 5 → Fin 2) : Prop :=
  chain (Fin.cons r f : Fin (m + 1) → Fin 5 → Fin 2) ∧
    ∀ j : Fin 4, PT (τ j) (col f j.castSucc) (col f j.succ)

instance {m : ℕ} (τ : Fin 4 → T3) (r : Fin 5 → Fin 2) : DecidablePred (@Cont m τ r) :=
  fun f => by unfold Cont; infer_instance

/-- The next row s is allowed by the statuses τ. -/
def okR (τ : Fin 4 → T3) (s : Fin 5 → Fin 2) : Prop :=
  ∀ j : Fin 4, okT (τ j) (s j.castSucc) (s j.succ)

instance (τ : Fin 4 → T3) : DecidablePred (okR τ) := fun s => by unfold okR; infer_instance

/-- The statuses after the row s. -/
def stpR (τ : Fin 4 → T3) (s : Fin 5 → Fin 2) : Fin 4 → T3 :=
  fun j => stpT (τ j) (s j.castSucc) (s j.succ)

lemma col_cons {m : ℕ} (s : Fin 5 → Fin 2) (g : Fin m → Fin 5 → Fin 2) (j : Fin 5) :
    col (Fin.cons s g : Fin (m + 1) → Fin 5 → Fin 2) j = Fin.cons (s j) (col g j) := by
  funext i
  induction i using Fin.cases <;> rfl

lemma Cont_cons {m : ℕ} (τ : Fin 4 → T3) (r s : Fin 5 → Fin 2) (g : Fin m → Fin 5 → Fin 2) :
    Cont τ r (Fin.cons s g) ↔ PT .z r s ∧ okR τ s ∧ Cont (stpR τ s) s g := by
  unfold Cont okR stpR
  simp only [chain_cons2, col_cons, PT_cons]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, fun j => (h3 j).1, h2, fun j => (h3 j).2⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨h1, h3⟩, fun j => ⟨h2 j, h4 j⟩⟩

lemma Cont_nil (τ : Fin 4 → T3) (r : Fin 5 → Fin 2) (f : Fin 0 → Fin 5 → Fin 2) :
    Cont τ r f ↔ ∀ j, accT (τ j) := by
  unfold Cont
  simp only [PT_nil]
  exact ⟨fun h => h.2, fun h => ⟨chain_one _, h⟩⟩

lemma good_iff {n : ℕ} (x : Fin n → Fin 5 → Fin 2) :
    good x ↔ chain x ∧ ∀ j : Fin 4, PT .z (col x j.castSucc) (col x j.succ) := by
  unfold good chain
  refine and_congr Iff.rfl ⟨fun h j => h j.castSucc j.succ (by simp), fun h j j' hj => ?_⟩
  have hj3 : j.val < 4 := by have := j'.isLt; omega
  have e1 : j = (⟨j.val, hj3⟩ : Fin 4).castSucc := Fin.ext rfl
  have e2 : j' = (⟨j.val, hj3⟩ : Fin 4).succ := Fin.ext (by simp; omega)
  rw [e1, e2]
  exact h _

lemma good_cons {m : ℕ} (s : Fin 5 → Fin 2) (g : Fin m → Fin 5 → Fin 2) :
    good (Fin.cons s g : Fin (m + 1) → Fin 5 → Fin 2) ↔
      okR (fun _ => .z) s ∧ Cont (stpR (fun _ => .z) s) s g := by
  rw [good_iff]
  unfold Cont okR stpR
  simp only [col_cons, PT_cons]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun j => (h2 j).1, h1, fun j => (h2 j).2⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h2, fun j => ⟨h1 j, h3 j⟩⟩

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
def F (m : ℕ) (τ : Fin 4 → T3) (r : Fin 5 → Fin 2) : ℕ :=
  (univ.filter (fun f : Fin m → Fin 5 → Fin 2 => Cont τ r f)).card

lemma F_succ (m : ℕ) (τ : Fin 4 → T3) (r : Fin 5 → Fin 2) :
    F (m + 1) τ r = ∑ s : Fin 5 → Fin 2,
      if PT .z r s ∧ okR τ s then F m (stpR τ s) s else 0 := by
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

lemma F_zero (τ : Fin 4 → T3) (r : Fin 5 → Fin 2) :
    F 0 τ r = if ∀ j, accT (τ j) then 1 else 0 := by
  unfold F
  have hu : (univ : Finset (Fin 0 → Fin 5 → Fin 2)) = {Fin.elim0} := by
    ext g
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    funext i
    exact i.elim0
  rw [hu, Finset.filter_singleton]
  simp only [Cont_nil]
  split_ifs <;> simp

lemma a_succ (m : ℕ) : a (m + 1) = ∑ s : Fin 5 → Fin 2,
    if okR (fun _ => .z) s then F m (stpR (fun _ => .z) s) s else 0 := by
  unfold a
  rw [card_by_head]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  simp only [good_cons]
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
def mk3 (t : T3) (f : T3 → ℕ) : ℕ :=
  match t with
  | .z => f .z
  | .l => f .l
  | .g => f .g

lemma mk3_eq (t : T3) (f : T3 → ℕ) : mk3 t f = f t := by cases t <;> rfl

/-- Digit j of the code c of a row: the entry in column j. -/
def dg (c j : ℕ) : ℕ := c / 2 ^ j % 2

def okB (t : T3) (x y : ℕ) : Bool :=
  match t with
  | .z => decide (x ≤ y)
  | .l => true
  | .g => true

def stpB (t : T3) (x y : ℕ) : T3 := if x = y then t else if x < y then .l else .g

def accB (t : T3) : Bool :=
  match t with
  | .z => true
  | .l => false
  | .g => true

/-- The status machine run along two rows given by digit lists. -/
def ptB : T3 → List ℕ → List ℕ → Bool
  | t, x :: xs, y :: ys => okB t x y && ptB (stpB t x y) xs ys
  | t, [], _ => accB t
  | t, _ :: _, [] => accB t

/-- PT .z between the rows with codes r and s. -/
def rowB (r s : ℕ) : Bool :=
  ptB .z (List.ofFn (fun i : Fin 5 => dg r i)) (List.ofFn (fun i : Fin 5 => dg s i))

/-- W(m, t, r) through the status machine; the kernel evaluates each state once. -/
def cnt : ℕ → T3 → T3 → T3 → T3 → Fin (2 ^ 5) → ℕ
  | 0, t0, t1, t2, t3, _ => if accB t0 && accB t1 && accB t2 && accB t3 then 1 else 0
  | m + 1, t0, t1, t2, t3, r =>
      ∑ s ∈ univ.filter (fun s : Fin (2 ^ 5) => rowB r s = true),
        if okB t0 (dg s 0) (dg s 1) && okB t1 (dg s 1) (dg s 2) && okB t2 (dg s 2) (dg s 3) && okB t3 (dg s 3) (dg s 4) then
          mk3 (stpB t0 (dg s 0) (dg s 1)) (fun u0 => mk3 (stpB t1 (dg s 1) (dg s 2)) (fun u1 => mk3 (stpB t2 (dg s 2) (dg s 3)) (fun u2 => mk3 (stpB t3 (dg s 3) (dg s 4)) (fun u3 => cnt m u0 u1 u2 u3 s))))
        else 0

lemma ite_band (b c : Bool) (x : ℕ) :
    (if b = true then (if c = true then x else 0) else 0) = if (b && c) = true then x else 0 := by
  cases b <;> cases c <;> rfl

/-- The row with code c. -/
def dec : Fin (2 ^ 5) ≃ (Fin 5 → Fin 2) := finFunctionFinEquiv.symm

lemma dec_val (c : Fin (2 ^ 5)) (j : Fin 5) : (dec c j : ℕ) = dg c j :=
  finFunctionFinEquiv_symm_apply_val c j

lemma okB_iff {q : ℕ} (t : T3) (x y : Fin q) : okB t x y = true ↔ okT t x y := by
  cases t
  · show decide ((x : ℕ) ≤ y) = true ↔ (T3.z = T3.z → x ≤ y)
    rw [decide_eq_true_eq]
    exact ⟨fun h _ => h, fun h => h rfl⟩
  · exact ⟨fun _ h => absurd h (by decide), fun _ => rfl⟩
  · exact ⟨fun _ h => absurd h (by decide), fun _ => rfl⟩

lemma stpB_eq {q : ℕ} (t : T3) (x y : Fin q) : stpB t x y = stpT t x y := by
  unfold stpB stpT
  simp only [Fin.ext_iff, Fin.lt_def]

lemma accB_iff (t : T3) : accB t = true ↔ accT t := by
  cases t <;> simp [accB, accT]

lemma ptB_iff {q : ℕ} : ∀ (m : ℕ) (t : T3) (u v : Fin m → Fin q),
    ptB t (List.ofFn (fun i => (u i : ℕ))) (List.ofFn (fun i => (v i : ℕ))) = true ↔ PT t u v
  | 0, t, u, v => by
    simp only [List.ofFn_zero, ptB, accB_iff]
    exact (PT_nil t u v).symm
  | m + 1, t, u, v => by
    rw [List.ofFn_succ, List.ofFn_succ]
    simp only [ptB, Bool.and_eq_true, okB_iff, stpB_eq]
    rw [ptB_iff m (stpT t (u 0) (v 0)) (fun i => u i.succ) (fun i => v i.succ)]
    conv_rhs => rw [← Fin.cons_self_tail u, ← Fin.cons_self_tail v]
    rw [PT_cons]
    rfl

lemma rowB_iff (r s : Fin (2 ^ 5)) : rowB r s = true ↔ PT .z (dec r) (dec s) := by
  have e : ∀ c : Fin (2 ^ 5), List.ofFn (fun i : Fin 5 => dg c i) =
      List.ofFn (fun i => (dec c i : ℕ)) := fun c =>
    congrArg List.ofFn (funext fun i => (dec_val c i).symm)
  rw [rowB, e, e, ptB_iff]

lemma okR_iff (τ : Fin 4 → T3) (s : Fin 5 → Fin 2) :
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

lemma cnt_eq : ∀ (m : ℕ) (t0 t1 t2 t3 : T3) (r : Fin (2 ^ 5)),
    cnt m t0 t1 t2 t3 r = F m ![t0, t1, t2, t3] (dec r)
  | 0, t0, t1, t2, t3, r => by
    rw [cnt, F_zero]
    have e : (accB t0 && accB t1 && accB t2 && accB t3) = true ↔ ∀ j, accT (![t0, t1, t2, t3] j) := by
      simp only [Bool.and_eq_true, accB_iff]
      constructor
      · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ j
        fin_cases j
        · exact h1
        · exact h2
        · exact h3
        · exact h4
      · intro h
        exact ⟨⟨⟨h 0, h 1⟩, h 2⟩, h 3⟩
    by_cases h : (accB t0 && accB t1 && accB t2 && accB t3) = true
    · rw [if_pos h, if_pos (e.1 h)]
    · rw [if_neg h, if_neg (fun h' => h (e.2 h'))]
  | m + 1, t0, t1, t2, t3, r => by
    rw [cnt, F_succ, ← Equiv.sum_comp dec, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [ite_band]
    simp only [mk3_eq, cnt_eq m]
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
    have hc : (rowB r s && (okB t0 (dec s 0) (dec s 1) && okB t1 (dec s 1) (dec s 2) && okB t2 (dec s 2) (dec s 3) && okB t3 (dec s 3) (dec s 4))) = true ↔
          PT .z (dec r) (dec s) ∧ okR ![t0, t1, t2, t3] (dec s) := by
      rw [okR_iff]
      simp only [Bool.and_eq_true, rowB_iff, okB_iff, and_assoc]
      try exact Iff.rfl
    rw [hst]
    by_cases h : (rowB r s && (okB t0 (dec s 0) (dec s 1) && okB t1 (dec s 1) (dec s 2) && okB t2 (dec s 2) (dec s 3) && okB t3 (dec s 3) (dec s 4))) = true
    · rw [if_pos h, if_pos (hc.1 h)]
    · rw [if_neg h, if_neg (fun h' => h (hc.2 h'))]

lemma cnt_succ (m : ℕ) (t0 t1 t2 t3 : T3) (r : Fin (2 ^ 5)) :
    cnt (m + 1) t0 t1 t2 t3 r = ∑ s ∈ univ.filter (fun s : Fin (2 ^ 5) => rowB r s = true),
      if okB t0 (dg s 0) (dg s 1) && okB t1 (dg s 1) (dg s 2) && okB t2 (dg s 2) (dg s 3) && okB t3 (dg s 3) (dg s 4) then
        cnt m (stpB t0 (dg s 0) (dg s 1)) (stpB t1 (dg s 1) (dg s 2)) (stpB t2 (dg s 2) (dg s 3)) (stpB t3 (dg s 3) (dg s 4)) s
      else 0 := by
  rw [cnt]
  simp only [mk3_eq]

/-- The first row s: allowed, and its statuses. -/
lemma a_succ' (m : ℕ) : a (m + 1) = ∑ s : Fin (2 ^ 5),
    if okB .z (dg s 0) (dg s 1) && okB .z (dg s 1) (dg s 2) && okB .z (dg s 2) (dg s 3) && okB .z (dg s 3) (dg s 4) then
      cnt m (stpB .z (dg s 0) (dg s 1)) (stpB .z (dg s 1) (dg s 2)) (stpB .z (dg s 2) (dg s 3)) (stpB .z (dg s 3) (dg s 4)) s
    else 0 := by
  rw [a_succ, ← Equiv.sum_comp dec]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [cnt_eq]
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
  have hc : (okB .z (dec s 0) (dec s 1) && okB .z (dec s 1) (dec s 2) && okB .z (dec s 2) (dec s 3) && okB .z (dec s 3) (dec s 4)) = true ↔ okR (fun _ => .z) (dec s) := by
    rw [okR_iff]
    simp only [Bool.and_eq_true, okB_iff, and_assoc]
    try exact Iff.rfl
  rw [hst]
  by_cases h : (okB .z (dec s 0) (dec s 1) && okB .z (dec s 1) (dec s 2) && okB .z (dec s 2) (dec s 3) && okB .z (dec s 3) (dec s 4)) = true
  · rw [if_pos h, if_pos (hc.1 h)]
  · rw [if_neg h, if_neg (fun h' => h (hc.2 h'))]

/-! ## The relation for every reachable state -/

/-- The status as a digit. -/
def t3v : T3 → ℕ
  | .z => 0
  | .l => 1
  | .g => 2

/-- The states reachable from the first row, as a bit mask indexed by
(Sum_j t3v t_j 3^j) * 32 + r (computed by a search outside Lean; `reach_init` and `reach_next`
check that it contains the starting states and is closed under the transitions). -/
def reachB (t0 t1 t2 t3 : T3) (r : ℕ) : Bool :=
  Nat.testBit 14258176724286048638089003499156014911303361013425388677065076989482360581876786626114043210361222254409782477923279056836246633640728923332079779240414365436829771451558439207854537245713874633675239843565778811157798998816209024324996612661739950993310967450903600265259176765339548823635118731040902101105886059877270488702395495776036128421591490725133197928441115851872879603893168827980057911691398685237852570189258101742349798604679856787244881526061350576027673700579520505694970467935970087624147994577670568574023076611150867157502925234086181648325026767178300159780842158190421268023230336201259213344256755718618235376381792015315220049284957791081179736034748056113424735082644272224740673305324428982754942391841407869188822762579857137697350051637068726009857 ((t3v t0 + 3 * (t3v t1 + 3 * (t3v t2 + 3 * (t3v t3)))) * 32 + r)

lemma reach_init : ∀ s : Fin (2 ^ 5), (okB .z (dg s 0) (dg s 1) && okB .z (dg s 1) (dg s 2) && okB .z (dg s 2) (dg s 3) && okB .z (dg s 3) (dg s 4)) = true →
    reachB (stpB .z (dg s 0) (dg s 1)) (stpB .z (dg s 1) (dg s 2)) (stpB .z (dg s 2) (dg s 3)) (stpB .z (dg s 3) (dg s 4)) s = true := by
  decide +kernel

lemma reach_next : ∀ (t0 t1 t2 t3 : T3) (r : Fin (2 ^ 5)), reachB t0 t1 t2 t3 r = true →
    ∀ s ∈ univ.filter (fun s : Fin (2 ^ 5) => rowB r s = true), (okB t0 (dg s 0) (dg s 1) && okB t1 (dg s 1) (dg s 2) && okB t2 (dg s 2) (dg s 3) && okB t3 (dg s 3) (dg s 4)) = true →
      reachB (stpB t0 (dg s 0) (dg s 1)) (stpB t1 (dg s 1) (dg s 2)) (stpB t2 (dg s 2) (dg s 3)) (stpB t3 (dg s 3) (dg s 4)) s = true := by
  decide +kernel

/-- The relation Sum_i (-1)^i C(7, i) W(m + 7 - i) = 0, negative terms on the right. -/
def RL (m : ℕ) (t0 t1 t2 t3 : T3) (r : Fin (2 ^ 5)) : ℕ :=
  cnt (m + 7) t0 t1 t2 t3 r + 21 * cnt (m + 5) t0 t1 t2 t3 r + 35 * cnt (m + 3) t0 t1 t2 t3 r + 7 * cnt (m + 1) t0 t1 t2 t3 r

def RR (m : ℕ) (t0 t1 t2 t3 : T3) (r : Fin (2 ^ 5)) : ℕ :=
  7 * cnt (m + 6) t0 t1 t2 t3 r + 35 * cnt (m + 4) t0 t1 t2 t3 r + 21 * cnt (m + 2) t0 t1 t2 t3 r + cnt m t0 t1 t2 t3 r

lemma R_base : ∀ (t0 t1 t2 t3 : T3) (r : Fin (2 ^ 5)), reachB t0 t1 t2 t3 r = true →
    RL 0 t0 t1 t2 t3 r = RR 0 t0 t1 t2 t3 r := by
  decide +kernel

lemma R_all : ∀ (m : ℕ) (t0 t1 t2 t3 : T3) (r : Fin (2 ^ 5)), reachB t0 t1 t2 t3 r = true →
    RL m t0 t1 t2 t3 r = RR m t0 t1 t2 t3 r
  | 0, t0, t1, t2, t3, r, h => R_base t0 t1 t2 t3 r h
  | m + 1, t0, t1, t2, t3, r, h => by
    unfold RL RR
    rw [show m + 1 + 7 = (m + 7) + 1 from rfl, show m + 1 + 6 = (m + 6) + 1 from rfl, show m + 1 + 5 = (m + 5) + 1 from rfl, show m + 1 + 4 = (m + 4) + 1 from rfl, show m + 1 + 3 = (m + 3) + 1 from rfl, show m + 1 + 2 = (m + 2) + 1 from rfl, show m + 1 + 1 = (m + 1) + 1 from rfl,
      cnt_succ (m + 7), cnt_succ (m + 6), cnt_succ (m + 5), cnt_succ (m + 4), cnt_succ (m + 3), cnt_succ (m + 2), cnt_succ (m + 1), cnt_succ m]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun s hs => ?_)
    split_ifs with hc
    · have := R_all m _ _ _ _ s (reach_next t0 t1 t2 t3 r h s hs hc)
      unfold RL RR at this
      linarith
    · simp

/-! ## Barker's recurrence and g.f. -/

lemma a_rel (n : ℕ) : a (n + 8) + 21 * a (n + 6) + 35 * a (n + 4) + 7 * a (n + 2) =
    7 * a (n + 7) + 35 * a (n + 5) + 21 * a (n + 3) + a (n + 1) := by
  rw [show n + 8 = (n + 7) + 1 from rfl, show n + 7 = (n + 6) + 1 from rfl, show n + 6 = (n + 5) + 1 from rfl, show n + 5 = (n + 4) + 1 from rfl, show n + 4 = (n + 3) + 1 from rfl, show n + 3 = (n + 2) + 1 from rfl, show n + 2 = (n + 1) + 1 from rfl,
    a_succ' (n + 7), a_succ' (n + 6), a_succ' (n + 5), a_succ' (n + 4), a_succ' (n + 3), a_succ' (n + 2), a_succ' (n + 1), a_succ' n]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  split_ifs with hc
  · have := R_all n _ _ _ _ s (reach_init s hc)
    unfold RL RR at this
    linarith
  · simp

lemma a_v1 : a 1 = 2 := by rw [a_succ']; decide +kernel
lemma a_v2 : a 2 = 6 := by rw [a_succ']; decide +kernel
lemma a_v3 : a 3 = 22 := by rw [a_succ']; decide +kernel
lemma a_v4 : a 4 = 80 := by rw [a_succ']; decide +kernel
lemma a_v5 : a 5 = 268 := by rw [a_succ']; decide +kernel
lemma a_v6 : a 6 = 786 := by rw [a_succ']; decide +kernel
lemma a_v7 : a 7 = 2016 := by rw [a_succ']; decide +kernel

/-- Barker's recurrence, for n > 7. -/
theorem recurrence (n : ℕ) (hn : 7 < n) :
    (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 8 := ⟨n - 8, by omega⟩
  have h := a_rel k
  simp only [show k + 8 - 1 = k + 7 by omega, show k + 8 - 2 = k + 6 by omega, show k + 8 - 3 = k + 5 by omega, show k + 8 - 4 = k + 4 by omega, show k + 8 - 5 = k + 3 by omega, show k + 8 - 6 = k + 2 by omega, show k + 8 - 7 = k + 1 by omega]
  have h' : (a (k + 8) : ℤ) + 21 * a (k + 6) + 35 * a (k + 4) + 7 * a (k + 2) =
      7 * (a (k + 7) : ℤ) + 35 * a (k + 5) + 21 * a (k + 3) + a (k + 1) := by exact_mod_cast h
  linarith

/-- Barker's g.f.: (Sum_{n >= 1} a(n) x^n) (1 - x)^7 = numerator. -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 7 =
      2 * X * (1 - 4 * X + 11 * X ^ 2 - 9 * X ^ 3 + 15 * X ^ 4 - 6 * X ^ 5) := by
  set A : ℚ⟦X⟧ := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have e1 : A * (1 - X) ^ 7 =
      A - C 7 * (A * X ^ 1) + C 21 * (A * X ^ 2) - C 35 * (A * X ^ 3) + C 35 * (A * X ^ 4) - C 21 * (A * X ^ 5) + C 7 * (A * X ^ 6) - A * X ^ 7 := by
    simp only [map_ofNat]; ring
  have e2 : (2 * X * (1 - 4 * X + 11 * X ^ 2 - 9 * X ^ 3 + 15 * X ^ 4 - 6 * X ^ 5) : ℚ⟦X⟧) =
      X ^ 1 * C 2 - X ^ 2 * C 8 + X ^ 3 * C 22 - X ^ 4 * C 18 + X ^ 5 * C 30 - X ^ 6 * C 12 := by
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
  rcases Nat.lt_or_ge n 8 with hn | hn
  · interval_cases n <;> simp_all <;> norm_num
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 8 := ⟨n - 8, by omega⟩
    have h := a_rel k
    have hq : (a (k + 8) : ℚ) + 21 * a (k + 6) + 35 * a (k + 4) + 7 * a (k + 2) =
        7 * (a (k + 7) : ℚ) + 35 * a (k + 5) + 21 * a (k + 3) + a (k + 1) := by exact_mod_cast h
    simp only [show k + 8 - 1 = k + 7 by omega,
      show k + 8 - 2 = k + 6 by omega,
      show k + 8 - 3 = k + 5 by omega,
      show k + 8 - 4 = k + 4 by omega,
      show k + 8 - 5 = k + 3 by omega,
      show k + 8 - 6 = k + 2 by omega,
      show k + 8 - 7 = k + 1 by omega,
      show ¬ k + 8 = 0 by omega,
      show ¬ k + 7 = 0 by omega,
      show ¬ k + 6 = 0 by omega,
      show ¬ k + 5 = 0 by omega,
      show ¬ k + 4 = 0 by omega,
      show ¬ k + 3 = 0 by omega,
      show ¬ k + 2 = 0 by omega,
      show ¬ k + 1 = 0 by omega,
      show 1 ≤ k + 8 by omega,
      show 2 ≤ k + 8 by omega,
      show 3 ≤ k + 8 by omega,
      show 4 ≤ k + 8 by omega,
      show 5 ≤ k + 8 by omega,
      show 6 ≤ k + 8 by omega,
      show 7 ≤ k + 8 by omega,
      show ¬ k + 8 = 1 by omega,
      show ¬ k + 8 = 2 by omega,
      show ¬ k + 8 = 3 by omega,
      show ¬ k + 8 = 4 by omega,
      show ¬ k + 8 = 5 by omega,
      show ¬ k + 8 = 6 by omega, if_true, if_false]
    linear_combination hq

/-- Both of Barker's conjectures. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 7 =
      2 * X * (1 - 4 * X + 11 * X ^ 2 - 9 * X ^ 3 + 15 * X ^ 4 - 6 * X ^ 5) ∧
    ∀ n : ℕ, 7 < n →
      (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7) :=
  ⟨gf, recurrence⟩

/-- Controls: the entry's data a(1..32), from a(1..7) and the relation (proved for an
abstract sequence f, so that no tactic unfolds `a`). -/
theorem controls :
    a 1 = 2 ∧ a 2 = 6 ∧ a 3 = 22 ∧ a 4 = 80 ∧ a 5 = 268 ∧ a 6 = 786 ∧ a 7 = 2016 ∧ a 8 = 4608 ∧
    a 9 = 9582 ∧ a 10 = 18446 ∧ a 11 = 33330 ∧ a 12 = 57136 ∧ a 13 = 93704 ∧ a 14 = 147994 ∧
    a 15 = 226284 ∧ a 16 = 336384 ∧ a 17 = 487866 ∧ a 18 = 692310 ∧ a 19 = 963566 ∧ a 20 = 1318032 ∧
    a 21 = 1774948 ∧ a 22 = 2356706 ∧ a 23 = 3089176 ∧ a 24 = 4002048 ∧ a 25 = 5129190 ∧
    a 26 = 6509022 ∧ a 27 = 8184906 ∧ a 28 = 10205552 ∧ a 29 = 12625440 ∧ a 30 = 15505258 ∧
    a 31 = 18912356 ∧ a 32 = 22921216 := by
  have key : ∀ f : ℕ → ℕ, f 1 = 2 → f 2 = 6 → f 3 = 22 → f 4 = 80 → f 5 = 268 → f 6 = 786 → f 7 = 2016 →
      (∀ n, f (n + 8) + 21 * f (n + 6) + 35 * f (n + 4) + 7 * f (n + 2) = 7 * f (n + 7) + 35 * f (n + 5) + 21 * f (n + 3) + f (n + 1)) →
        f 1 = 2 ∧ f 2 = 6 ∧ f 3 = 22 ∧ f 4 = 80 ∧ f 5 = 268 ∧ f 6 = 786 ∧ f 7 = 2016 ∧ f 8 = 4608 ∧
        f 9 = 9582 ∧ f 10 = 18446 ∧ f 11 = 33330 ∧ f 12 = 57136 ∧ f 13 = 93704 ∧ f 14 = 147994 ∧
        f 15 = 226284 ∧ f 16 = 336384 ∧ f 17 = 487866 ∧ f 18 = 692310 ∧ f 19 = 963566 ∧
        f 20 = 1318032 ∧ f 21 = 1774948 ∧ f 22 = 2356706 ∧ f 23 = 3089176 ∧ f 24 = 4002048 ∧
        f 25 = 5129190 ∧ f 26 = 6509022 ∧ f 27 = 8184906 ∧ f 28 = 10205552 ∧ f 29 = 12625440 ∧
        f 30 = 15505258 ∧ f 31 = 18912356 ∧ f 32 = 22921216 := by
    intro f h1 h2 h3 h4 h5 h6 h7 hr
    have h8 : f 8 = 4608 := by
      have r := hr 0
      simp only [Nat.reduceAdd, Nat.reduceMul, h1, h2, h3, h4, h5, h6, h7] at r
      omega
    have h9 : f 9 = 9582 := by
      have r := hr 1
      simp only [Nat.reduceAdd, Nat.reduceMul, h2, h3, h4, h5, h6, h7, h8] at r
      omega
    have h10 : f 10 = 18446 := by
      have r := hr 2
      simp only [Nat.reduceAdd, Nat.reduceMul, h3, h4, h5, h6, h7, h8, h9] at r
      omega
    have h11 : f 11 = 33330 := by
      have r := hr 3
      simp only [Nat.reduceAdd, Nat.reduceMul, h4, h5, h6, h7, h8, h9, h10] at r
      omega
    have h12 : f 12 = 57136 := by
      have r := hr 4
      simp only [Nat.reduceAdd, Nat.reduceMul, h5, h6, h7, h8, h9, h10, h11] at r
      omega
    have h13 : f 13 = 93704 := by
      have r := hr 5
      simp only [Nat.reduceAdd, Nat.reduceMul, h6, h7, h8, h9, h10, h11, h12] at r
      omega
    have h14 : f 14 = 147994 := by
      have r := hr 6
      simp only [Nat.reduceAdd, Nat.reduceMul, h7, h8, h9, h10, h11, h12, h13] at r
      omega
    have h15 : f 15 = 226284 := by
      have r := hr 7
      simp only [Nat.reduceAdd, Nat.reduceMul, h8, h9, h10, h11, h12, h13, h14] at r
      omega
    have h16 : f 16 = 336384 := by
      have r := hr 8
      simp only [Nat.reduceAdd, Nat.reduceMul, h9, h10, h11, h12, h13, h14, h15] at r
      omega
    have h17 : f 17 = 487866 := by
      have r := hr 9
      simp only [Nat.reduceAdd, Nat.reduceMul, h10, h11, h12, h13, h14, h15, h16] at r
      omega
    have h18 : f 18 = 692310 := by
      have r := hr 10
      simp only [Nat.reduceAdd, Nat.reduceMul, h11, h12, h13, h14, h15, h16, h17] at r
      omega
    have h19 : f 19 = 963566 := by
      have r := hr 11
      simp only [Nat.reduceAdd, Nat.reduceMul, h12, h13, h14, h15, h16, h17, h18] at r
      omega
    have h20 : f 20 = 1318032 := by
      have r := hr 12
      simp only [Nat.reduceAdd, Nat.reduceMul, h13, h14, h15, h16, h17, h18, h19] at r
      omega
    have h21 : f 21 = 1774948 := by
      have r := hr 13
      simp only [Nat.reduceAdd, Nat.reduceMul, h14, h15, h16, h17, h18, h19, h20] at r
      omega
    have h22 : f 22 = 2356706 := by
      have r := hr 14
      simp only [Nat.reduceAdd, Nat.reduceMul, h15, h16, h17, h18, h19, h20, h21] at r
      omega
    have h23 : f 23 = 3089176 := by
      have r := hr 15
      simp only [Nat.reduceAdd, Nat.reduceMul, h16, h17, h18, h19, h20, h21, h22] at r
      omega
    have h24 : f 24 = 4002048 := by
      have r := hr 16
      simp only [Nat.reduceAdd, Nat.reduceMul, h17, h18, h19, h20, h21, h22, h23] at r
      omega
    have h25 : f 25 = 5129190 := by
      have r := hr 17
      simp only [Nat.reduceAdd, Nat.reduceMul, h18, h19, h20, h21, h22, h23, h24] at r
      omega
    have h26 : f 26 = 6509022 := by
      have r := hr 18
      simp only [Nat.reduceAdd, Nat.reduceMul, h19, h20, h21, h22, h23, h24, h25] at r
      omega
    have h27 : f 27 = 8184906 := by
      have r := hr 19
      simp only [Nat.reduceAdd, Nat.reduceMul, h20, h21, h22, h23, h24, h25, h26] at r
      omega
    have h28 : f 28 = 10205552 := by
      have r := hr 20
      simp only [Nat.reduceAdd, Nat.reduceMul, h21, h22, h23, h24, h25, h26, h27] at r
      omega
    have h29 : f 29 = 12625440 := by
      have r := hr 21
      simp only [Nat.reduceAdd, Nat.reduceMul, h22, h23, h24, h25, h26, h27, h28] at r
      omega
    have h30 : f 30 = 15505258 := by
      have r := hr 22
      simp only [Nat.reduceAdd, Nat.reduceMul, h23, h24, h25, h26, h27, h28, h29] at r
      omega
    have h31 : f 31 = 18912356 := by
      have r := hr 23
      simp only [Nat.reduceAdd, Nat.reduceMul, h24, h25, h26, h27, h28, h29, h30] at r
      omega
    have h32 : f 32 = 22921216 := by
      have r := hr 24
      simp only [Nat.reduceAdd, Nat.reduceMul, h25, h26, h27, h28, h29, h30, h31] at r
      omega
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32⟩
  exact key a a_v1 a_v2 a_v3 a_v4 a_v5 a_v6 a_v7 a_rel

/-- Control by direct enumeration of all arrays with 1 row(s): a(1) = 2. -/
theorem control_direct :
    ((univ : Finset (Fin 1 → Fin 5 → Fin 2)).filter good).card = 2 := by
  decide +kernel

end OMA.S_oeis_a201372

theorem OMA.solution : type_of% @OMA.S_oeis_a201372.main :=
  OMA.S_oeis_a201372.conjecture
