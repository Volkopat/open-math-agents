import OMAStatements.S_oeis_a263869

namespace OMA.S_oeis_a263869

open PowerSeries Finset


instance {m q : ℕ} : DecidableRel (@lexLE m q) := fun u v => by unfold lexLE; infer_instance




instance {m : ℕ} : DecidablePred (@good m) := fun x => by unfold good; infer_instance


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
def PT {m : ℕ} : T2 → (Fin m → Fin 2) → (Fin m → Fin 2) → Prop
  | .z, u, v => lexLE u v
  | .d, _, _ => True

instance {m : ℕ} (t : T2) (u v : Fin m → Fin 2) : Decidable (PT t u v) := by
  cases t <;> unfold PT <;> infer_instance

/-- The entries (x, y) of the next row in the two columns are allowed after the status t. -/
def okT (t : T2) (x y : Fin 2) : Prop := t = .z → x ≤ y

instance (t : T2) (x y : Fin 2) : Decidable (okT t x y) := by
  unfold okT; infer_instance

/-- The status after the entries (x, y). -/
def stpT (t : T2) (x y : Fin 2) : T2 := if x = y then t else .d

lemma PT_cons {m : ℕ} (t : T2) (x y : Fin 2) (u v : Fin m → Fin 2) :
    PT t (Fin.cons x u : Fin (m + 1) → Fin 2) (Fin.cons y v) ↔ okT t x y ∧ PT (stpT t x y) u v := by
  by_cases hxy : x = y
  · subst hxy
    rw [show stpT t x x = t from if_pos rfl]
    cases t <;> simp [PT, okT, lexLE_cons]
  · rw [show stpT t x y = .d from if_neg hxy]
    cases t
    · simp only [PT, okT, lexLE_cons, hxy, false_and, or_false, true_implies, and_true]
      exact ⟨le_of_lt, fun h => lt_of_le_of_ne h hxy⟩
    · simp [PT, okT]

lemma PT_nil (t : T2) (u v : Fin 0 → Fin 2) : PT t u v := by
  cases t
  · exact Or.inl (funext fun i => i.elim0)
  · trivial

/-! ## Column residues -/

/-- A residue mod 3, as a constructor the kernel can match on. -/
inductive R3
  | q0
  | q1
  | q2
  deriving DecidableEq

instance : Fintype R3 := ⟨{.q0, .q1, .q2}, fun t => by cases t <;> simp⟩

def rf : R3 → Fin 3
  | .q0 => 0
  | .q1 => 1
  | .q2 => 2

/-! ## The arrays the proof counts -/

/-- The condition on a single row. -/
def hrow (r : Fin 5 → Fin 2) : Prop := 3 ∣ rowVal r

/-- The condition between a row r and the row s below it. -/
def vcond (r s : Fin 5 → Fin 2) : Prop := lexLE r s

instance (r : Fin 5 → Fin 2) : Decidable (hrow r) := by unfold hrow; infer_instance

instance (r s : Fin 5 → Fin 2) : Decidable (vcond r s) := by unfold vcond; infer_instance

/-- Consecutive rows satisfy the condition between rows. -/
def chain {m : ℕ} (y : Fin m → Fin 5 → Fin 2) : Prop :=
  ∀ i i' : Fin m, i.val + 1 = i'.val → vcond (y i) (y i')

instance {m : ℕ} : DecidablePred (@chain m) := fun y => by unfold chain; infer_instance

/-- Column j of the array f. -/
def col {m : ℕ} (f : Fin m → Fin 5 → Fin 2) (j : Fin 5) : Fin m → Fin 2 := fun i => f i j

lemma colVal_cons {m : ℕ} (s : Fin 5 → Fin 2) (g : Fin m → Fin 5 → Fin 2) (j : Fin 5) :
    colVal (Fin.cons s g : Fin (m + 1) → Fin 5 → Fin 2) j = (s j : ℕ) * 2 ^ m + colVal g j := by
  unfold colVal
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, Fin.val_zero, Fin.val_succ, Nat.sub_zero,
    Nat.add_sub_cancel]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  congr 2
  omega

lemma colVal_nil (g : Fin 0 → Fin 5 → Fin 2) (j : Fin 5) : colVal g j = 0 := by
  simp [colVal]

lemma dvd_res (c b v m : ℕ) :
    3 ∣ c * 2 ^ (m + 1) + (b * 2 ^ m + v) ↔ 3 ∣ ((2 * c + b) % 3) * 2 ^ m + v := by
  have h1 : c * 2 ^ (m + 1) + (b * 2 ^ m + v) = (2 * c + b) * 2 ^ m + v := by ring
  have h2 : (2 * c + b) * 2 ^ m = ((2 * c + b) % 3) * 2 ^ m + 3 * ((2 * c + b) / 3 * 2 ^ m) := by
    conv_lhs => rw [← Nat.mod_add_div (2 * c + b) 3]
    ring
  rw [h1, h2, show ((2 * c + b) % 3) * 2 ^ m + 3 * ((2 * c + b) / 3 * 2 ^ m) + v =
    ((2 * c + b) % 3) * 2 ^ m + v + 3 * ((2 * c + b) / 3 * 2 ^ m) by ring]
  exact Nat.dvd_add_left (dvd_mul_right 3 _)

/-- The arrays counted by the proof. -/
def core {m : ℕ} (y : Fin m → Fin 5 → Fin 2) : Prop :=
  (∀ i, hrow (y i)) ∧ chain y ∧ (∀ j : Fin 4, PT .z (col y j.castSucc) (col y j.succ)) ∧
    ∀ j : Fin 5, 3 ∣ colVal y j

instance {m : ℕ} : DecidablePred (@core m) := fun y => by unfold core; infer_instance

/-- The rows f continue the row r validly, the column pairs having statuses τ and the columns
residues c after r. -/
def Cont {m : ℕ} (τ : Fin 4 → T2) (c : Fin 5 → Fin 3) (r : Fin 5 → Fin 2)
    (f : Fin m → Fin 5 → Fin 2) : Prop :=
  chain (Fin.cons r f : Fin (m + 1) → Fin 5 → Fin 2) ∧ (∀ i, hrow (f i)) ∧
    (∀ j : Fin 4, PT (τ j) (col f j.castSucc) (col f j.succ)) ∧
    ∀ j : Fin 5, 3 ∣ (c j : ℕ) * 2 ^ m + colVal f j

instance {m : ℕ} (τ : Fin 4 → T2) (c : Fin 5 → Fin 3) (r : Fin 5 → Fin 2) :
    DecidablePred (@Cont m τ c r) := fun f => by unfold Cont; infer_instance

/-- The next row s is allowed by the statuses τ. -/
def okR (τ : Fin 4 → T2) (s : Fin 5 → Fin 2) : Prop :=
  ∀ j : Fin 4, okT (τ j) (s j.castSucc) (s j.succ)

instance (τ : Fin 4 → T2) : DecidablePred (okR τ) := fun s => by unfold okR; infer_instance

/-- The statuses after the row s. -/
def stpR (τ : Fin 4 → T2) (s : Fin 5 → Fin 2) : Fin 4 → T2 :=
  fun j => stpT (τ j) (s j.castSucc) (s j.succ)

/-- The column residues after the row s. -/
def resR (c : Fin 5 → Fin 3) (s : Fin 5 → Fin 2) : Fin 5 → Fin 3 :=
  fun j => ⟨(2 * (c j : ℕ) + s j) % 3, Nat.mod_lt _ (by norm_num)⟩

lemma col_cons {m : ℕ} (s : Fin 5 → Fin 2) (g : Fin m → Fin 5 → Fin 2) (j : Fin 5) :
    col (Fin.cons s g : Fin (m + 1) → Fin 5 → Fin 2) j = Fin.cons (s j) (col g j) := by
  funext i
  induction i using Fin.cases <;> rfl

lemma chain_cons2 {m : ℕ} (r s : Fin 5 → Fin 2) (g : Fin m → Fin 5 → Fin 2) :
    chain (Fin.cons r (Fin.cons s g) : Fin (m + 2) → Fin 5 → Fin 2) ↔
      vcond r s ∧ chain (Fin.cons s g : Fin (m + 1) → Fin 5 → Fin 2) := by
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

lemma all_hrow_cons {m : ℕ} (s : Fin 5 → Fin 2) (g : Fin m → Fin 5 → Fin 2) :
    (∀ i, hrow ((Fin.cons s g : Fin (m + 1) → Fin 5 → Fin 2) i)) ↔ hrow s ∧ ∀ i, hrow (g i) := by
  rw [Fin.forall_fin_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]

lemma res_cons {m : ℕ} (c : Fin 5 → Fin 3) (s : Fin 5 → Fin 2) (g : Fin m → Fin 5 → Fin 2) :
    (∀ j : Fin 5, 3 ∣ (c j : ℕ) * 2 ^ (m + 1) + colVal (Fin.cons s g : Fin (m + 1) → Fin 5 → Fin 2) j) ↔
      ∀ j : Fin 5, 3 ∣ (resR c s j : ℕ) * 2 ^ m + colVal g j := by
  refine forall_congr' (fun j => ?_)
  rw [colVal_cons, dvd_res]
  rfl

lemma Cont_cons {m : ℕ} (τ : Fin 4 → T2) (c : Fin 5 → Fin 3) (r s : Fin 5 → Fin 2)
    (g : Fin m → Fin 5 → Fin 2) :
    Cont τ c r (Fin.cons s g) ↔ (hrow s ∧ vcond r s) ∧ okR τ s ∧ Cont (stpR τ s) (resR c s) s g := by
  unfold Cont okR stpR
  rw [chain_cons2, all_hrow_cons, res_cons]
  simp only [col_cons, PT_cons]
  constructor
  · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5, h6⟩
    exact ⟨⟨h3, h1⟩, fun j => (h5 j).1, h2, h4, fun j => (h5 j).2, h6⟩
  · rintro ⟨⟨h3, h1⟩, h5, h2, h4, h7, h6⟩
    exact ⟨⟨h1, h2⟩, ⟨h3, h4⟩, fun j => ⟨h5 j, h7 j⟩, h6⟩

lemma Cont_nil (τ : Fin 4 → T2) (c : Fin 5 → Fin 3) (r : Fin 5 → Fin 2)
    (f : Fin 0 → Fin 5 → Fin 2) : Cont τ c r f ↔ ∀ j, c j = 0 := by
  unfold Cont
  simp only [colVal_nil, pow_zero, mul_one, add_zero]
  constructor
  · rintro ⟨_, _, _, h⟩ j
    have h3 := h j
    have hc := (c j).isLt
    apply Fin.ext
    simp only [Fin.val_zero]
    omega
  · intro h
    refine ⟨fun i i' hi => ?_, fun i => i.elim0, fun j => PT_nil _ _ _, fun j => by simp [h j]⟩
    have := i'.isLt
    have := i.isLt
    omega

lemma core_cons {m : ℕ} (s : Fin 5 → Fin 2) (g : Fin m → Fin 5 → Fin 2) :
    core (Fin.cons s g : Fin (m + 1) → Fin 5 → Fin 2) ↔
      (hrow s ∧ okR (fun _ => .z) s) ∧ Cont (stpR (fun _ => .z) s) (resR (fun _ => 0) s) s g := by
  unfold core Cont okR stpR
  rw [all_hrow_cons]
  have hres : (∀ j : Fin 5, 3 ∣ colVal (Fin.cons s g : Fin (m + 1) → Fin 5 → Fin 2) j) ↔
      ∀ j : Fin 5, 3 ∣ (resR (fun _ => 0) s j : ℕ) * 2 ^ m + colVal g j := by
    rw [← res_cons]
    simp
  rw [hres]
  simp only [col_cons, PT_cons]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4, h6⟩
    exact ⟨⟨h1, fun j => (h4 j).1⟩, h3, h2, fun j => (h4 j).2, h6⟩
  · rintro ⟨⟨h1, h4⟩, h3, h2, h5, h6⟩
    exact ⟨⟨h1, h2⟩, h3, fun j => ⟨h4 j, h5 j⟩, h6⟩

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

/-- F(m, τ, c, r): the number of ways to continue the row r by m more rows. -/
def F (m : ℕ) (τ : Fin 4 → T2) (c : Fin 5 → Fin 3) (r : Fin 5 → Fin 2) : ℕ :=
  (univ.filter (fun f : Fin m → Fin 5 → Fin 2 => Cont τ c r f)).card

lemma F_succ (m : ℕ) (τ : Fin 4 → T2) (c : Fin 5 → Fin 3) (r : Fin 5 → Fin 2) :
    F (m + 1) τ c r = ∑ s : Fin 5 → Fin 2,
      if (hrow s ∧ vcond r s) ∧ okR τ s then F m (stpR τ s) (resR c s) s else 0 := by
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

lemma F_zero (τ : Fin 4 → T2) (c : Fin 5 → Fin 3) (r : Fin 5 → Fin 2) :
    F 0 τ c r = if ∀ j, c j = 0 then 1 else 0 := by
  unfold F
  have hu : (univ : Finset (Fin 0 → Fin 5 → Fin 2)) = {Fin.elim0} := by
    ext g
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    funext i
    exact i.elim0
  rw [hu, Finset.filter_singleton]
  simp only [Cont_nil]
  split_ifs <;> simp

lemma good_iff_core {m : ℕ} (x : Fin m → Fin 5 → Fin 2) : good x ↔ core x := by
  unfold good core chain hrow vcond col
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h3, fun j => h4 j.castSucc j.succ (by simp), h2⟩
  · rintro ⟨h1, h3, h4, h2⟩
    refine ⟨h1, h2, h3, fun j j' hj => ?_⟩
    have hj3 : j.val < 4 := by have := j'.isLt; omega
    have e1 : j = (⟨j.val, hj3⟩ : Fin 4).castSucc := Fin.ext rfl
    have e2 : j' = (⟨j.val, hj3⟩ : Fin 4).succ := Fin.ext (by simp; omega)
    rw [e1, e2]
    exact h4 _

lemma a_succ (m : ℕ) : a m = ∑ s : Fin 5 → Fin 2,
    if hrow s ∧ okR (fun _ => .z) s then F m (stpR (fun _ => .z) s) (resR (fun _ => 0) s) s
    else 0 := by
  unfold a
  rw [card_by_head]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  simp only [good_iff_core, core_cons]
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

/-- Pass a status or residue through a match, so that the kernel sees a constructor. -/
def mk2 (t : T2) (f : T2 → ℕ) : ℕ :=
  match t with
  | .z => f .z
  | .d => f .d

lemma mk2_eq (t : T2) (f : T2 → ℕ) : mk2 t f = f t := by cases t <;> rfl

def mkR (t : R3) (f : R3 → ℕ) : ℕ :=
  match t with
  | .q0 => f .q0
  | .q1 => f .q1
  | .q2 => f .q2

lemma mkR_eq (t : R3) (f : R3 → ℕ) : mkR t f = f t := by cases t <;> rfl

/-- Digit j of the code c of a row: the entry in column j. -/
def dg (c j : ℕ) : ℕ := c / 2 ^ j % 2

def okB (t : T2) (x y : ℕ) : Bool :=
  match t with
  | .z => decide (x ≤ y)
  | .d => true

def stpB (t : T2) (x y : ℕ) : T2 := if x = y then t else .d

def ofN (n : ℕ) : R3 := if n = 0 then .q0 else if n = 1 then .q1 else .q2

/-- The residue after appending the bit b. -/
def resB (e : R3) (b : ℕ) : R3 := ofN ((2 * (rf e : ℕ) + b) % 3)

/-- The row with code c is divisible by 3. -/
def hrowB (c : ℕ) : Bool := (dg c 0 * 16 + dg c 1 * 8 + dg c 2 * 4 + dg c 3 * 2 + dg c 4 * 1) % 3 == 0

/-- Lexicographic order on digit lists. -/
def lexB : List ℕ → List ℕ → Bool
  | x :: xs, y :: ys => decide (x < y) || (decide (x = y) && lexB xs ys)
  | _, _ => true

/-- The rows with codes r (above) and s (below) are in the right order. -/
def vB (r s : ℕ) : Bool := lexB (List.ofFn (fun i : Fin 5 => dg r i)) (List.ofFn (fun i : Fin 5 => dg s i))

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

def allRows : List (Fin (2 ^ 5)) := List.finRange (2 ^ 5)

def validRows : List (Fin (2 ^ 5)) := allRows.filter (fun c => hrowB c)

lemma sumL_allRows (g : Fin (2 ^ 5) → ℕ) : sumL allRows g = ∑ s, g s := by
  rw [sumL_eq, allRows, Fin.sum_univ_def]

/-- The rows that may follow the row r. -/
def succL (r : Fin (2 ^ 5)) : List (Fin (2 ^ 5)) := validRows.filter (fun s => vB r s)

/-- W(m, state) through the transfer; the kernel evaluates each state once. -/
def cnt : ℕ → T2 → T2 → T2 → T2 → R3 → R3 → R3 → R3 → R3 → Fin (2 ^ 5) → ℕ
  | 0, t0, t1, t2, t3, e0, e1, e2, e3, e4, _ => if e0 == .q0 && e1 == .q0 && e2 == .q0 && e3 == .q0 && e4 == .q0 then 1 else 0
  | m + 1, t0, t1, t2, t3, e0, e1, e2, e3, e4, r =>
      sumL (succL r) (fun s : Fin (2 ^ 5) =>
        if okB t0 (dg s 0) (dg s 1) && okB t1 (dg s 1) (dg s 2) && okB t2 (dg s 2) (dg s 3) && okB t3 (dg s 3) (dg s 4) then
          mk2 (stpB t0 (dg s 0) (dg s 1)) (fun u0 => mk2 (stpB t1 (dg s 1) (dg s 2)) (fun u1 => mk2 (stpB t2 (dg s 2) (dg s 3)) (fun u2 => mk2 (stpB t3 (dg s 3) (dg s 4)) (fun u3 => mkR (resB e0 (dg s 0)) (fun f0 => mkR (resB e1 (dg s 1)) (fun f1 => mkR (resB e2 (dg s 2)) (fun f2 => mkR (resB e3 (dg s 3)) (fun f3 => mkR (resB e4 (dg s 4)) (fun f4 => cnt m u0 u1 u2 u3 f0 f1 f2 f3 f4 s)))))))))
        else 0)

lemma ite_band (b c : Bool) (x : ℕ) :
    (if b = true then (if c = true then x else 0) else 0) = if (b && c) = true then x else 0 := by
  cases b <;> cases c <;> rfl

def dec : Fin (2 ^ 5) ≃ (Fin 5 → Fin 2) := finFunctionFinEquiv.symm

lemma dec_val (c : Fin (2 ^ 5)) (j : Fin 5) : (dec c j : ℕ) = dg c j :=
  finFunctionFinEquiv_symm_apply_val c j

lemma okB_iff (t : T2) (x y : Fin 2) : okB t x y = true ↔ okT t x y := by
  cases t
  · show decide ((x : ℕ) ≤ (y : ℕ)) = true ↔ (T2.z = T2.z → x ≤ y)
    rw [decide_eq_true_eq]
    exact ⟨fun h _ => h, fun h => h rfl⟩
  · exact ⟨fun _ h => absurd h (by decide), fun _ => rfl⟩

lemma stpB_eq (t : T2) (x y : Fin 2) : stpB t x y = stpT t x y := by
  unfold stpB stpT
  simp only [Fin.ext_iff]

lemma rf_ofN (n : ℕ) (h : n < 3) : (rf (ofN n) : ℕ) = n := by
  unfold ofN
  split_ifs with h0 h1
  · simp [rf, h0]
  · simp [rf, h1]
  · simp only [rf, Fin.val_two]
    omega

lemma resB_val (e : R3) (b : ℕ) : (rf (resB e b) : ℕ) = (2 * (rf e : ℕ) + b) % 3 :=
  rf_ofN _ (Nat.mod_lt _ (by norm_num))

lemma lexB_iff : ∀ (m : ℕ) (u v : Fin m → Fin 2),
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

lemma hrowB_iff : ∀ c : Fin (2 ^ 5), hrowB c = true ↔ hrow (dec c) := by
  decide +kernel

lemma vB_iff (r s : Fin (2 ^ 5)) : vB r s = true ↔ vcond (dec r) (dec s) := by
  have e : ∀ c : Fin (2 ^ 5), List.ofFn (fun i : Fin 5 => dg c i) =
      List.ofFn (fun i => (dec c i : ℕ)) := fun c =>
    congrArg List.ofFn (funext fun i => (dec_val c i).symm)
  unfold vB vcond
  rw [e, e, lexB_iff]

lemma okR_iff (τ : Fin 4 → T2) (s : Fin 5 → Fin 2) :
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

lemma rf_zero (e : R3) : rf e = 0 ↔ e = .q0 := by cases e <;> decide

lemma acc_iff (e0 e1 e2 e3 e4 : R3) :
    (e0 == .q0 && e1 == .q0 && e2 == .q0 && e3 == .q0 && e4 == .q0) = true ↔ ∀ j, (![rf e0, rf e1, rf e2, rf e3, rf e4] : Fin 5 → Fin 3) j = 0 := by
  simp only [Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩ j
    fin_cases j <;> simp [h0, h1, h2, h3, h4, rf]
  · intro h
    exact ⟨⟨⟨⟨(rf_zero e0).1 (h 0), (rf_zero e1).1 (h 1)⟩, (rf_zero e2).1 (h 2)⟩, (rf_zero e3).1 (h 3)⟩, (rf_zero e4).1 (h 4)⟩

lemma cnt_eq : ∀ (m : ℕ) (t0 t1 t2 t3 : T2) (e0 e1 e2 e3 e4 : R3) (r : Fin (2 ^ 5)),
    cnt m t0 t1 t2 t3 e0 e1 e2 e3 e4 r = F m ![t0, t1, t2, t3] ![rf e0, rf e1, rf e2, rf e3, rf e4] (dec r)
  | 0, t0, t1, t2, t3, e0, e1, e2, e3, e4, r => by
    rw [cnt, F_zero]
    by_cases h : (e0 == .q0 && e1 == .q0 && e2 == .q0 && e3 == .q0 && e4 == .q0) = true
    · rw [if_pos h, if_pos ((acc_iff e0 e1 e2 e3 e4).1 h)]
    · rw [if_neg h, if_neg (fun h' => h ((acc_iff e0 e1 e2 e3 e4).2 h'))]
  | m + 1, t0, t1, t2, t3, e0, e1, e2, e3, e4, r => by
    rw [cnt, succL, validRows]
    simp only [sumL_filter]
    rw [sumL_allRows, F_succ, ← Equiv.sum_comp dec]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    simp only [ite_band]
    simp only [mk2_eq, mkR_eq, cnt_eq m]
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
    have hres : resR ![rf e0, rf e1, rf e2, rf e3, rf e4] (dec s) =
        ![rf (resB e0 (dec s 0)), rf (resB e1 (dec s 1)), rf (resB e2 (dec s 2)), rf (resB e3 (dec s 3)), rf (resB e4 (dec s 4))] := by
      funext j
      fin_cases j
      · exact Fin.ext (resB_val e0 _).symm
      · exact Fin.ext (resB_val e1 _).symm
      · exact Fin.ext (resB_val e2 _).symm
      · exact Fin.ext (resB_val e3 _).symm
      · exact Fin.ext (resB_val e4 _).symm
    have hc : (hrowB s && (vB r s && (okB t0 (dec s 0) (dec s 1) && okB t1 (dec s 1) (dec s 2) && okB t2 (dec s 2) (dec s 3) && okB t3 (dec s 3) (dec s 4)))) = true ↔
          (hrow (dec s) ∧ vcond (dec r) (dec s)) ∧ okR ![t0, t1, t2, t3] (dec s) := by
      rw [okR_iff]
      simp only [Bool.and_eq_true, vB_iff, hrowB_iff, okB_iff, and_assoc]
      try exact Iff.rfl
    rw [hst, hres]
    by_cases h : (hrowB s && (vB r s && (okB t0 (dec s 0) (dec s 1) && okB t1 (dec s 1) (dec s 2) && okB t2 (dec s 2) (dec s 3) && okB t3 (dec s 3) (dec s 4)))) = true
    · rw [if_pos h, if_pos (hc.1 h)]
    · rw [if_neg h, if_neg (fun h' => h (hc.2 h'))]

lemma cnt_succ (m : ℕ) (t0 t1 t2 t3 : T2) (e0 e1 e2 e3 e4 : R3) (r : Fin (2 ^ 5)) :
    cnt (m + 1) t0 t1 t2 t3 e0 e1 e2 e3 e4 r = ∑ s : Fin (2 ^ 5),
      if (hrowB s && (vB r s && (okB t0 (dg s 0) (dg s 1) && okB t1 (dg s 1) (dg s 2) && okB t2 (dg s 2) (dg s 3) && okB t3 (dg s 3) (dg s 4)))) = true then
        cnt m (stpB t0 (dg s 0) (dg s 1)) (stpB t1 (dg s 1) (dg s 2)) (stpB t2 (dg s 2) (dg s 3)) (stpB t3 (dg s 3) (dg s 4)) (resB e0 (dg s 0)) (resB e1 (dg s 1)) (resB e2 (dg s 2)) (resB e3 (dg s 3)) (resB e4 (dg s 4)) s
      else 0 := by
  rw [cnt, succL, validRows]
  simp only [sumL_filter]
  rw [sumL_allRows]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  simp only [ite_band, mk2_eq, mkR_eq]

def Sa (m : ℕ) : ℕ := sumL validRows (fun s : Fin (2 ^ 5) =>
    if okB .z (dg s 0) (dg s 1) && okB .z (dg s 1) (dg s 2) && okB .z (dg s 2) (dg s 3) && okB .z (dg s 3) (dg s 4) then
      cnt m (stpB .z (dg s 0) (dg s 1)) (stpB .z (dg s 1) (dg s 2)) (stpB .z (dg s 2) (dg s 3)) (stpB .z (dg s 3) (dg s 4)) (resB .q0 (dg s 0)) (resB .q0 (dg s 1)) (resB .q0 (dg s 2)) (resB .q0 (dg s 3)) (resB .q0 (dg s 4)) s
    else 0)

lemma a_succ' (m : ℕ) : a m = Sa m := by
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
  have hres : resR (fun _ => 0) (dec s) =
      ![rf (resB .q0 (dec s 0)), rf (resB .q0 (dec s 1)), rf (resB .q0 (dec s 2)), rf (resB .q0 (dec s 3)), rf (resB .q0 (dec s 4))] := by
    funext j
    fin_cases j
    · exact Fin.ext (resB_val .q0 _).symm
    · exact Fin.ext (resB_val .q0 _).symm
    · exact Fin.ext (resB_val .q0 _).symm
    · exact Fin.ext (resB_val .q0 _).symm
    · exact Fin.ext (resB_val .q0 _).symm
  have hc : (hrowB s && (okB .z (dec s 0) (dec s 1) && okB .z (dec s 1) (dec s 2) && okB .z (dec s 2) (dec s 3) && okB .z (dec s 3) (dec s 4))) = true ↔ hrow (dec s) ∧ okR (fun _ => .z) (dec s) := by
    rw [okR_iff]
    simp only [Bool.and_eq_true, hrowB_iff, okB_iff, and_assoc]
    try exact Iff.rfl
  rw [hst, hres]
  by_cases h : (hrowB s && (okB .z (dec s 0) (dec s 1) && okB .z (dec s 1) (dec s 2) && okB .z (dec s 2) (dec s 3) && okB .z (dec s 3) (dec s 4))) = true
  · rw [if_pos h, if_pos (hc.1 h)]
  · rw [if_neg h, if_neg (fun h' => h (hc.2 h'))]

/-! ## The relation for every reachable state -/

/-- For each valid row code, the statuses and residues of the reachable states with that last row
(computed by a search outside Lean; `chk` checks that the table holds the starting states and is
closed under the transitions). -/
def reachT (r : Fin (2 ^ 5)) : List (T2 × T2 × T2 × T2 × R3 × R3 × R3 × R3 × R3) :=
  match r.val with
  | 0 => [(.z, .z, .z, .z, .q0, .q0, .q0, .q0, .q0)]
  | 3 => [(.d, .d, .d, .d, .q0, .q0, .q0, .q0, .q0), (.d, .d, .d, .d, .q0, .q0, .q0, .q1, .q1), (.d, .d, .d, .d, .q0, .q0, .q0, .q2, .q2), (.d, .d, .d, .d, .q0, .q1, .q1, .q0, .q0), (.d, .d, .d, .d, .q0, .q1, .q1, .q1, .q1), (.d, .d, .d, .d, .q0, .q1, .q1, .q2, .q2), (.d, .d, .d, .d, .q0, .q1, .q2, .q0, .q2), (.d, .d, .d, .d, .q0, .q1, .q2, .q1, .q0), (.d, .d, .d, .d, .q0, .q1, .q2, .q2, .q1), (.d, .d, .d, .d, .q0, .q2, .q0, .q0, .q2), (.d, .d, .d, .d, .q0, .q2, .q0, .q1, .q0), (.d, .d, .d, .d, .q0, .q2, .q0, .q2, .q1), (.d, .d, .d, .d, .q1, .q0, .q1, .q0, .q1), (.d, .d, .d, .d, .q1, .q0, .q1, .q1, .q2), (.d, .d, .d, .d, .q1, .q0, .q1, .q2, .q0), (.d, .d, .d, .d, .q1, .q0, .q2, .q0, .q0), (.d, .d, .d, .d, .q1, .q0, .q2, .q1, .q1), (.d, .d, .d, .d, .q1, .q0, .q2, .q2, .q2), (.d, .d, .d, .d, .q1, .q1, .q0, .q0, .q0), (.d, .d, .d, .d, .q1, .q1, .q0, .q1, .q1), (.d, .d, .d, .d, .q1, .q1, .q0, .q2, .q2), (.d, .d, .d, .d, .q1, .q2, .q0, .q0, .q1), (.d, .d, .d, .d, .q1, .q2, .q0, .q1, .q2), (.d, .d, .d, .d, .q1, .q2, .q0, .q2, .q0)]
  | 6 => [(.d, .z, .d, .z, .q0, .q0, .q0, .q0, .q0), (.d, .z, .d, .z, .q0, .q0, .q0, .q1, .q1), (.d, .z, .d, .z, .q0, .q1, .q1, .q0, .q0), (.d, .z, .d, .z, .q0, .q1, .q1, .q2, .q2)]
  | 15 => [(.d, .d, .d, .d, .q0, .q0, .q0, .q0, .q0), (.d, .d, .d, .d, .q0, .q0, .q0, .q1, .q1), (.d, .d, .d, .d, .q0, .q0, .q0, .q2, .q2), (.d, .d, .d, .d, .q0, .q0, .q1, .q0, .q2), (.d, .d, .d, .d, .q0, .q0, .q1, .q1, .q0), (.d, .d, .d, .d, .q0, .q0, .q1, .q2, .q1), (.d, .d, .d, .d, .q0, .q1, .q0, .q0, .q1), (.d, .d, .d, .d, .q0, .q1, .q0, .q1, .q2), (.d, .d, .d, .d, .q0, .q1, .q0, .q2, .q0), (.d, .d, .d, .d, .q0, .q1, .q1, .q0, .q0), (.d, .d, .d, .d, .q0, .q1, .q1, .q1, .q1), (.d, .d, .d, .d, .q0, .q1, .q1, .q2, .q2), (.d, .d, .d, .d, .q0, .q1, .q2, .q0, .q2), (.d, .d, .d, .d, .q0, .q1, .q2, .q1, .q0), (.d, .d, .d, .d, .q0, .q1, .q2, .q2, .q1), (.d, .d, .d, .d, .q0, .q2, .q0, .q0, .q2), (.d, .d, .d, .d, .q0, .q2, .q0, .q1, .q0), (.d, .d, .d, .d, .q0, .q2, .q0, .q2, .q1), (.d, .d, .d, .d, .q0, .q2, .q1, .q0, .q1), (.d, .d, .d, .d, .q0, .q2, .q1, .q1, .q2), (.d, .d, .d, .d, .q0, .q2, .q1, .q2, .q0), (.d, .d, .d, .d, .q1, .q0, .q0, .q0, .q2), (.d, .d, .d, .d, .q1, .q0, .q0, .q1, .q0), (.d, .d, .d, .d, .q1, .q0, .q0, .q2, .q1), (.d, .d, .d, .d, .q1, .q0, .q1, .q0, .q1), (.d, .d, .d, .d, .q1, .q0, .q1, .q1, .q2), (.d, .d, .d, .d, .q1, .q0, .q1, .q2, .q0), (.d, .d, .d, .d, .q1, .q0, .q2, .q0, .q0), (.d, .d, .d, .d, .q1, .q0, .q2, .q1, .q1), (.d, .d, .d, .d, .q1, .q0, .q2, .q2, .q2), (.d, .d, .d, .d, .q1, .q1, .q0, .q0, .q0), (.d, .d, .d, .d, .q1, .q1, .q0, .q1, .q1), (.d, .d, .d, .d, .q1, .q1, .q0, .q2, .q2), (.d, .d, .d, .d, .q1, .q1, .q1, .q0, .q2), (.d, .d, .d, .d, .q1, .q1, .q1, .q1, .q0), (.d, .d, .d, .d, .q1, .q1, .q1, .q2, .q1), (.d, .d, .d, .d, .q1, .q2, .q0, .q0, .q1), (.d, .d, .d, .d, .q1, .q2, .q0, .q1, .q2), (.d, .d, .d, .d, .q1, .q2, .q0, .q2, .q0), (.d, .d, .d, .d, .q1, .q2, .q1, .q0, .q0), (.d, .d, .d, .d, .q1, .q2, .q1, .q1, .q1), (.d, .d, .d, .d, .q1, .q2, .q1, .q2, .q2)]
  | 21 => [(.d, .d, .d, .d, .q0, .q0, .q0, .q0, .q0), (.d, .d, .d, .d, .q0, .q0, .q0, .q1, .q1), (.d, .d, .d, .d, .q0, .q0, .q0, .q2, .q2), (.d, .d, .d, .d, .q0, .q1, .q1, .q0, .q0), (.d, .d, .d, .d, .q0, .q1, .q1, .q1, .q1), (.d, .d, .d, .d, .q0, .q1, .q1, .q2, .q2), (.d, .d, .d, .d, .q1, .q0, .q1, .q0, .q1), (.d, .d, .d, .d, .q1, .q0, .q1, .q1, .q2), (.d, .d, .d, .d, .q1, .q0, .q1, .q2, .q0), (.d, .d, .d, .d, .q1, .q2, .q0, .q0, .q1), (.d, .d, .d, .d, .q1, .q2, .q0, .q1, .q2), (.d, .d, .d, .d, .q1, .q2, .q0, .q2, .q0)]
  | 24 => [(.z, .z, .d, .z, .q0, .q0, .q0, .q0, .q0), (.z, .z, .d, .z, .q0, .q0, .q0, .q1, .q1)]
  | 27 => [(.d, .d, .d, .d, .q0, .q0, .q0, .q0, .q0), (.d, .d, .d, .d, .q0, .q0, .q0, .q1, .q1), (.d, .d, .d, .d, .q0, .q0, .q0, .q2, .q2), (.d, .d, .d, .d, .q0, .q1, .q1, .q0, .q0), (.d, .d, .d, .d, .q0, .q1, .q1, .q1, .q1), (.d, .d, .d, .d, .q0, .q1, .q1, .q2, .q2), (.d, .d, .d, .d, .q0, .q1, .q2, .q0, .q2), (.d, .d, .d, .d, .q0, .q1, .q2, .q1, .q0), (.d, .d, .d, .d, .q0, .q1, .q2, .q2, .q1), (.d, .d, .d, .d, .q0, .q2, .q0, .q0, .q2), (.d, .d, .d, .d, .q0, .q2, .q0, .q1, .q0), (.d, .d, .d, .d, .q0, .q2, .q0, .q2, .q1), (.d, .d, .d, .d, .q1, .q0, .q1, .q0, .q1), (.d, .d, .d, .d, .q1, .q0, .q1, .q1, .q2), (.d, .d, .d, .d, .q1, .q0, .q1, .q2, .q0), (.d, .d, .d, .d, .q1, .q0, .q2, .q0, .q0), (.d, .d, .d, .d, .q1, .q0, .q2, .q1, .q1), (.d, .d, .d, .d, .q1, .q0, .q2, .q2, .q2), (.d, .d, .d, .d, .q1, .q1, .q0, .q0, .q0), (.d, .d, .d, .d, .q1, .q1, .q0, .q1, .q1), (.d, .d, .d, .d, .q1, .q1, .q0, .q2, .q2), (.d, .d, .d, .d, .q1, .q2, .q0, .q0, .q1), (.d, .d, .d, .d, .q1, .q2, .q0, .q1, .q2), (.d, .d, .d, .d, .q1, .q2, .q0, .q2, .q0)]
  | 30 => [(.d, .z, .z, .z, .q0, .q0, .q0, .q0, .q0), (.d, .z, .z, .z, .q0, .q1, .q1, .q1, .q1), (.d, .z, .d, .z, .q0, .q0, .q0, .q0, .q0), (.d, .z, .d, .z, .q0, .q0, .q0, .q1, .q1), (.d, .z, .d, .z, .q0, .q0, .q0, .q2, .q2), (.d, .z, .d, .z, .q0, .q1, .q1, .q0, .q0), (.d, .z, .d, .z, .q0, .q1, .q1, .q1, .q1), (.d, .z, .d, .z, .q0, .q1, .q1, .q2, .q2)]
  | _ => []

/-- The state is in the table. -/
def reachB (t0 t1 t2 t3 : T2) (e0 e1 e2 e3 e4 : R3) (r : Fin (2 ^ 5)) : Bool := List.elem (t0, t1, t2, t3, e0, e1, e2, e3, e4) (reachT r)

/-- The invariant: a valid row whose state is in the table. -/
def reachV (t0 t1 t2 t3 : T2) (e0 e1 e2 e3 e4 : R3) (r : Fin (2 ^ 5)) : Bool := hrowB r && reachB t0 t1 t2 t3 e0 e1 e2 e3 e4 r

/-- The relation Sum_i c_i W(m + 14 - i) = 0, negative terms on the right. -/
def RL (m : ℕ) (t0 t1 t2 t3 : T2) (e0 e1 e2 e3 e4 : R3) (r : Fin (2 ^ 5)) : ℕ :=
  cnt (m + 14) t0 t1 t2 t3 e0 e1 e2 e3 e4 r + 12 * cnt (m + 11) t0 t1 t2 t3 e0 e1 e2 e3 e4 r + 9 * cnt (m + 10) t0 t1 t2 t3 e0 e1 e2 e3 e4 r + 40 * cnt (m + 7) t0 t1 t2 t3 e0 e1 e2 e3 e4 r + 9 * cnt (m + 4) t0 t1 t2 t3 e0 e1 e2 e3 e4 r + 12 * cnt (m + 3) t0 t1 t2 t3 e0 e1 e2 e3 e4 r + cnt m t0 t1 t2 t3 e0 e1 e2 e3 e4 r

def RR (m : ℕ) (t0 t1 t2 t3 : T2) (e0 e1 e2 e3 e4 : R3) (r : Fin (2 ^ 5)) : ℕ :=
  2 * cnt (m + 13) t0 t1 t2 t3 e0 e1 e2 e3 e4 r + 5 * cnt (m + 12) t0 t1 t2 t3 e0 e1 e2 e3 e4 r + 30 * cnt (m + 9) t0 t1 t2 t3 e0 e1 e2 e3 e4 r + 5 * cnt (m + 8) t0 t1 t2 t3 e0 e1 e2 e3 e4 r + 5 * cnt (m + 6) t0 t1 t2 t3 e0 e1 e2 e3 e4 r + 30 * cnt (m + 5) t0 t1 t2 t3 e0 e1 e2 e3 e4 r + 5 * cnt (m + 2) t0 t1 t2 t3 e0 e1 e2 e3 e4 r + 2 * cnt (m + 1) t0 t1 t2 t3 e0 e1 e2 e3 e4 r

/-- The starting state of the (valid) first row s is in the table. -/
def fA (s : Fin (2 ^ 5)) : Bool := !(okB .z (dg s 0) (dg s 1) && okB .z (dg s 1) (dg s 2) && okB .z (dg s 2) (dg s 3) && okB .z (dg s 3) (dg s 4)) || reachB (stpB .z (dg s 0) (dg s 1)) (stpB .z (dg s 1) (dg s 2)) (stpB .z (dg s 2) (dg s 3)) (stpB .z (dg s 3) (dg s 4)) (resB .q0 (dg s 0)) (resB .q0 (dg s 1)) (resB .q0 (dg s 2)) (resB .q0 (dg s 3)) (resB .q0 (dg s 4)) s

/-- The successor of the state by the (valid) row s is in the table. -/
def fN (t0 t1 t2 t3 : T2) (e0 e1 e2 e3 e4 : R3) (s : Fin (2 ^ 5)) : Bool :=
  !(okB t0 (dg s 0) (dg s 1) && okB t1 (dg s 1) (dg s 2) && okB t2 (dg s 2) (dg s 3) && okB t3 (dg s 3) (dg s 4)) || reachB (stpB t0 (dg s 0) (dg s 1)) (stpB t1 (dg s 1) (dg s 2)) (stpB t2 (dg s 2) (dg s 3)) (stpB t3 (dg s 3) (dg s 4)) (resB e0 (dg s 0)) (resB e1 (dg s 1)) (resB e2 (dg s 2)) (resB e3 (dg s 3)) (resB e4 (dg s 4)) s

def fB' (t0 t1 t2 t3 : T2) (e0 e1 e2 e3 e4 : R3) (r : Fin (2 ^ 5)) : Bool :=
  (succL r).all (fun s => fN t0 t1 t2 t3 e0 e1 e2 e3 e4 s) && RL 0 t0 t1 t2 t3 e0 e1 e2 e3 e4 r == RR 0 t0 t1 t2 t3 e0 e1 e2 e3 e4 r

def mk2b (t : T2) (f : T2 → Bool) : Bool :=
  match t with
  | .z => f .z
  | .d => f .d

lemma mk2b_eq (t : T2) (f : T2 → Bool) : mk2b t f = f t := by cases t <;> rfl

def mkRb (t : R3) (f : R3 → Bool) : Bool :=
  match t with
  | .q0 => f .q0
  | .q1 => f .q1
  | .q2 => f .q2

lemma mkRb_eq (t : R3) (f : R3 → Bool) : mkRb t f = f t := by cases t <;> rfl

/-- For a state of the table: all successors are in the table and the relation holds at m = 0. -/
def fB (p : T2 × T2 × T2 × T2 × R3 × R3 × R3 × R3 × R3) (r : Fin (2 ^ 5)) : Bool :=
  mk2b p.1 (fun t0 => mk2b p.2.1 (fun t1 => mk2b p.2.2.1 (fun t2 => mk2b p.2.2.2.1 (fun t3 => mkRb p.2.2.2.2.1 (fun e0 => mkRb p.2.2.2.2.2.1 (fun e1 => mkRb p.2.2.2.2.2.2.1 (fun e2 => mkRb p.2.2.2.2.2.2.2.1 (fun e3 => mkRb p.2.2.2.2.2.2.2.2 (fun e4 => fB' t0 t1 t2 t3 e0 e1 e2 e3 e4 r)))))))))

/-- The first values a(0..14). -/
def fS : Bool := Sa 0 == 1 && Sa 1 == 3 && Sa 2 == 3 && Sa 3 == 7 && Sa 4 == 7 && Sa 5 == 16 && Sa 6 == 17 && Sa 7 == 41 &&
  Sa 8 == 48 && Sa 9 == 113 && Sa 10 == 141 && Sa 11 == 303 && Sa 12 == 387 && Sa 13 == 752 &&
  Sa 14 == 962

/-- Everything the kernel computes, in one Boolean so that the evaluated counts are shared. -/
def chk : Bool :=
  validRows.all fA && validRows.all (fun r => (reachT r).all (fun p => fB p r)) && fS

lemma chk_true : chk = true := by decide +kernel

lemma valid_mem {s : Fin (2 ^ 5)} (h : hrowB s = true) : s ∈ validRows :=
  List.mem_filter.2 ⟨List.mem_finRange s, h⟩

lemma imp_of_bool {b c : Bool} (h : (!b || c) = true) (hb : b = true) : c = true := by
  cases b <;> cases c <;> simp_all

lemma chk_parts : (∀ s ∈ validRows, fA s = true) ∧
    (∀ r ∈ validRows, ∀ p ∈ reachT r, fB p r = true) ∧ fS = true := by
  have h := chk_true
  simp only [chk, Bool.and_eq_true] at h
  exact ⟨List.all_eq_true.1 h.1.1, fun r hr => List.all_eq_true.1 (List.all_eq_true.1 h.1.2 r hr),
    h.2⟩

lemma reach_init : ∀ s : Fin (2 ^ 5), (hrowB s && (okB .z (dg s 0) (dg s 1) && okB .z (dg s 1) (dg s 2) && okB .z (dg s 2) (dg s 3) && okB .z (dg s 3) (dg s 4))) = true →
    reachV (stpB .z (dg s 0) (dg s 1)) (stpB .z (dg s 1) (dg s 2)) (stpB .z (dg s 2) (dg s 3)) (stpB .z (dg s 3) (dg s 4)) (resB .q0 (dg s 0)) (resB .q0 (dg s 1)) (resB .q0 (dg s 2)) (resB .q0 (dg s 3)) (resB .q0 (dg s 4)) s = true := by
  intro s hs
  rw [Bool.and_eq_true] at hs
  simp only [reachV, hs.1, Bool.true_and]
  exact imp_of_bool (chk_parts.1 s (valid_mem hs.1)) hs.2

lemma fB_parts (t0 t1 t2 t3 : T2) (e0 e1 e2 e3 e4 : R3) (r : Fin (2 ^ 5)) (hr : reachV t0 t1 t2 t3 e0 e1 e2 e3 e4 r = true) :
    (∀ s ∈ succL r, fN t0 t1 t2 t3 e0 e1 e2 e3 e4 s = true) ∧ RL 0 t0 t1 t2 t3 e0 e1 e2 e3 e4 r = RR 0 t0 t1 t2 t3 e0 e1 e2 e3 e4 r := by
  unfold reachV at hr
  rw [Bool.and_eq_true] at hr
  have h := chk_parts.2.1 r (valid_mem hr.1) _ (List.elem_iff.1 hr.2)
  simp only [fB, mk2b_eq, mkRb_eq, fB', Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨List.all_eq_true.1 h.1, h.2⟩

lemma reach_next : ∀ (t0 t1 t2 t3 : T2) (e0 e1 e2 e3 e4 : R3) (r : Fin (2 ^ 5)), reachV t0 t1 t2 t3 e0 e1 e2 e3 e4 r = true →
    ∀ s : Fin (2 ^ 5), (hrowB s && (vB r s && (okB t0 (dg s 0) (dg s 1) && okB t1 (dg s 1) (dg s 2) && okB t2 (dg s 2) (dg s 3) && okB t3 (dg s 3) (dg s 4)))) = true →
      reachV (stpB t0 (dg s 0) (dg s 1)) (stpB t1 (dg s 1) (dg s 2)) (stpB t2 (dg s 2) (dg s 3)) (stpB t3 (dg s 3) (dg s 4)) (resB e0 (dg s 0)) (resB e1 (dg s 1)) (resB e2 (dg s 2)) (resB e3 (dg s 3)) (resB e4 (dg s 4)) s = true := by
  intro t0 t1 t2 t3 e0 e1 e2 e3 e4 r hr s hs
  rw [Bool.and_eq_true, Bool.and_eq_true] at hs
  have hm : s ∈ succL r :=
    List.mem_filter.2 ⟨List.mem_filter.2 ⟨List.mem_finRange s, hs.1⟩, hs.2.1⟩
  simp only [reachV, hs.1, Bool.true_and]
  exact imp_of_bool ((fB_parts t0 t1 t2 t3 e0 e1 e2 e3 e4 r hr).1 s hm) hs.2.2

lemma kernel_facts : Sa 0 = 1 ∧ Sa 1 = 3 ∧ Sa 2 = 3 ∧ Sa 3 = 7 ∧ Sa 4 = 7 ∧ Sa 5 = 16 ∧ Sa 6 = 17 ∧ Sa 7 = 41 ∧
    Sa 8 = 48 ∧ Sa 9 = 113 ∧ Sa 10 = 141 ∧ Sa 11 = 303 ∧ Sa 12 = 387 ∧ Sa 13 = 752 ∧ Sa 14 = 962 := by
  have h := chk_parts.2.2
  simp only [fS, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1.1.1.1.1.1.1.1.1.1.1.1, h.1.1.1.1.1.1.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.2, h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

lemma R_all (m : ℕ) : ∀ (t0 t1 t2 t3 : T2) (e0 e1 e2 e3 e4 : R3) (r : Fin (2 ^ 5)), reachV t0 t1 t2 t3 e0 e1 e2 e3 e4 r = true →
    RL m t0 t1 t2 t3 e0 e1 e2 e3 e4 r = RR m t0 t1 t2 t3 e0 e1 e2 e3 e4 r := by
  induction m with
  | zero => exact fun t0 t1 t2 t3 e0 e1 e2 e3 e4 r hr => (fB_parts t0 t1 t2 t3 e0 e1 e2 e3 e4 r hr).2
  | succ m ih =>
    intro t0 t1 t2 t3 e0 e1 e2 e3 e4 r h
    unfold RL RR
    rw [show m + 1 + 14 = (m + 14) + 1 from rfl, show m + 1 + 13 = (m + 13) + 1 from rfl, show m + 1 + 12 = (m + 12) + 1 from rfl, show m + 1 + 11 = (m + 11) + 1 from rfl, show m + 1 + 10 = (m + 10) + 1 from rfl, show m + 1 + 9 = (m + 9) + 1 from rfl, show m + 1 + 8 = (m + 8) + 1 from rfl, show m + 1 + 7 = (m + 7) + 1 from rfl, show m + 1 + 6 = (m + 6) + 1 from rfl, show m + 1 + 5 = (m + 5) + 1 from rfl, show m + 1 + 4 = (m + 4) + 1 from rfl, show m + 1 + 3 = (m + 3) + 1 from rfl, show m + 1 + 2 = (m + 2) + 1 from rfl, show m + 1 + 1 = (m + 1) + 1 from rfl,
      cnt_succ (m + 14), cnt_succ (m + 13), cnt_succ (m + 12), cnt_succ (m + 11), cnt_succ (m + 10), cnt_succ (m + 9), cnt_succ (m + 8), cnt_succ (m + 7), cnt_succ (m + 6), cnt_succ (m + 5), cnt_succ (m + 4), cnt_succ (m + 3), cnt_succ (m + 2), cnt_succ (m + 1), cnt_succ m]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    split_ifs with hc
    · exact ih _ _ _ _ _ _ _ _ _ s (reach_next t0 t1 t2 t3 e0 e1 e2 e3 e4 r h s hc)
    · simp

/-! ## The recurrence for a -/

lemma a_rel (n : ℕ) : a (n + 14) + 12 * a (n + 11) + 9 * a (n + 10) + 40 * a (n + 7) + 9 * a (n + 4) + 12 * a (n + 3) + a n =
    2 * a (n + 13) + 5 * a (n + 12) + 30 * a (n + 9) + 5 * a (n + 8) + 5 * a (n + 6) + 30 * a (n + 5) + 5 * a (n + 2) + 2 * a (n + 1) := by
  rw [a_succ' (n + 14), a_succ' (n + 13), a_succ' (n + 12), a_succ' (n + 11), a_succ' (n + 10), a_succ' (n + 9), a_succ' (n + 8), a_succ' (n + 7), a_succ' (n + 6), a_succ' (n + 5), a_succ' (n + 4), a_succ' (n + 3), a_succ' (n + 2), a_succ' (n + 1), a_succ' n]
  simp only [Sa, validRows, sumL_filter, sumL_allRows]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  simp only [ite_band]
  split_ifs with hc
  · exact R_all n _ _ _ _ _ _ _ _ _ s (reach_init s hc)
  · simp

lemma a_v0 : a 0 = 1 := (a_succ' 0).trans kernel_facts.1
lemma a_v1 : a 1 = 3 := (a_succ' 1).trans kernel_facts.2.1
lemma a_v2 : a 2 = 3 := (a_succ' 2).trans kernel_facts.2.2.1
lemma a_v3 : a 3 = 7 := (a_succ' 3).trans kernel_facts.2.2.2.1
lemma a_v4 : a 4 = 7 := (a_succ' 4).trans kernel_facts.2.2.2.2.1
lemma a_v5 : a 5 = 16 := (a_succ' 5).trans kernel_facts.2.2.2.2.2.1
lemma a_v6 : a 6 = 17 := (a_succ' 6).trans kernel_facts.2.2.2.2.2.2.1
lemma a_v7 : a 7 = 41 := (a_succ' 7).trans kernel_facts.2.2.2.2.2.2.2.1
lemma a_v8 : a 8 = 48 := (a_succ' 8).trans kernel_facts.2.2.2.2.2.2.2.2.1
lemma a_v9 : a 9 = 113 := (a_succ' 9).trans kernel_facts.2.2.2.2.2.2.2.2.2.1
lemma a_v10 : a 10 = 141 := (a_succ' 10).trans kernel_facts.2.2.2.2.2.2.2.2.2.2.1
lemma a_v11 : a 11 = 303 := (a_succ' 11).trans kernel_facts.2.2.2.2.2.2.2.2.2.2.2.1
lemma a_v12 : a 12 = 387 := (a_succ' 12).trans kernel_facts.2.2.2.2.2.2.2.2.2.2.2.2.1
lemma a_v13 : a 13 = 752 := (a_succ' 13).trans kernel_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.1
lemma a_v14 : a 14 = 962 := (a_succ' 14).trans kernel_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2

set_option maxHeartbeats 1000000 in
/-- Barker's g.f. -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (((1 - X) ^ 8 * (1 + X) ^ 6)) =
      X * (3 - 3 * X - 14 * X ^ 2 + 14 * X ^ 3 + 30 * X ^ 4 - 29 * X ^ 5 - 31 * X ^ 6 + 31 * X ^ 7 + 20 * X ^ 8 - 20 * X ^ 9 - 7 * X ^ 10 + 7 * X ^ 11 + X ^ 12 - X ^ 13) := by
  set A : ℚ⟦X⟧ := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have e1 : A * (((1 - X) ^ 8 * (1 + X) ^ 6)) =
      A - C 2 * (A * X ^ 1) - C 5 * (A * X ^ 2) + C 12 * (A * X ^ 3) + C 9 * (A * X ^ 4) - C 30 * (A * X ^ 5) - C 5 * (A * X ^ 6) + C 40 * (A * X ^ 7) - C 5 * (A * X ^ 8) - C 30 * (A * X ^ 9) + C 9 * (A * X ^ 10) + C 12 * (A * X ^ 11) - C 5 * (A * X ^ 12) - C 2 * (A * X ^ 13) + A * X ^ 14 := by
    simp only [map_ofNat]; ring
  have e2 : (X * (3 - 3 * X - 14 * X ^ 2 + 14 * X ^ 3 + 30 * X ^ 4 - 29 * X ^ 5 - 31 * X ^ 6 + 31 * X ^ 7 + 20 * X ^ 8 - 20 * X ^ 9 - 7 * X ^ 10 + 7 * X ^ 11 + X ^ 12 - X ^ 13) : ℚ⟦X⟧) =
      X ^ 1 * C 3 - X ^ 2 * C 3 - X ^ 3 * C 14 + X ^ 4 * C 14 + X ^ 5 * C 30 - X ^ 6 * C 29 - X ^ 7 * C 31 + X ^ 8 * C 31 + X ^ 9 * C 20 - X ^ 10 * C 20 - X ^ 11 * C 7 + X ^ 12 * C 7 + X ^ 13 - X ^ 14 := by
    simp only [map_ofNat]; ring
  rw [e1, e2]
  ext n
  have hc : ∀ k, coeff k A = if k = 0 then (0 : ℚ) else a k := fun k => by rw [hA, coeff_mk]
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_C, coeff_X_pow, coeff_mul_X_pow', hc]
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
  have v12 := a_v12
  have v13 := a_v13
  have v14 := a_v14
  rcases Nat.lt_or_ge n 15 with hn | hn
  · interval_cases n <;> simp_all <;> norm_num
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 15 := ⟨n - 15, by omega⟩
    have h := a_rel (k + 1)
    simp only [show k + 1 + 1 = k + 2 from rfl, show k + 1 + 2 = k + 3 from rfl, show k + 1 + 3 = k + 4 from rfl, show k + 1 + 4 = k + 5 from rfl, show k + 1 + 5 = k + 6 from rfl, show k + 1 + 6 = k + 7 from rfl, show k + 1 + 7 = k + 8 from rfl, show k + 1 + 8 = k + 9 from rfl, show k + 1 + 9 = k + 10 from rfl, show k + 1 + 10 = k + 11 from rfl, show k + 1 + 11 = k + 12 from rfl, show k + 1 + 12 = k + 13 from rfl, show k + 1 + 13 = k + 14 from rfl, show k + 1 + 14 = k + 15 from rfl] at h
    have hq : (a (k + 15) + 12 * a (k + 12) + 9 * a (k + 11) + 40 * a (k + 8) + 9 * a (k + 5) + 12 * a (k + 4) + a (k + 1) : ℚ) = 2 * a (k + 14) + 5 * a (k + 13) + 30 * a (k + 10) + 5 * a (k + 9) + 5 * a (k + 7) + 30 * a (k + 6) + 5 * a (k + 3) + 2 * a (k + 2) := by exact_mod_cast h
    simp only [show k + 15 - 1 = k + 14 by omega,
      show k + 15 - 2 = k + 13 by omega,
      show k + 15 - 3 = k + 12 by omega,
      show k + 15 - 4 = k + 11 by omega,
      show k + 15 - 5 = k + 10 by omega,
      show k + 15 - 6 = k + 9 by omega,
      show k + 15 - 7 = k + 8 by omega,
      show k + 15 - 8 = k + 7 by omega,
      show k + 15 - 9 = k + 6 by omega,
      show k + 15 - 10 = k + 5 by omega,
      show k + 15 - 11 = k + 4 by omega,
      show k + 15 - 12 = k + 3 by omega,
      show k + 15 - 13 = k + 2 by omega,
      show k + 15 - 14 = k + 1 by omega,
      show ¬ k + 15 = 0 by omega,
      show ¬ k + 14 = 0 by omega,
      show ¬ k + 13 = 0 by omega,
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
      show 1 ≤ k + 15 by omega,
      show 2 ≤ k + 15 by omega,
      show 3 ≤ k + 15 by omega,
      show 4 ≤ k + 15 by omega,
      show 5 ≤ k + 15 by omega,
      show 6 ≤ k + 15 by omega,
      show 7 ≤ k + 15 by omega,
      show 8 ≤ k + 15 by omega,
      show 9 ≤ k + 15 by omega,
      show 10 ≤ k + 15 by omega,
      show 11 ≤ k + 15 by omega,
      show 12 ≤ k + 15 by omega,
      show 13 ≤ k + 15 by omega,
      show 14 ≤ k + 15 by omega,
      show ¬ k + 15 = 1 by omega,
      show ¬ k + 15 = 2 by omega,
      show ¬ k + 15 = 3 by omega,
      show ¬ k + 15 = 4 by omega,
      show ¬ k + 15 = 5 by omega,
      show ¬ k + 15 = 6 by omega,
      show ¬ k + 15 = 7 by omega,
      show ¬ k + 15 = 8 by omega,
      show ¬ k + 15 = 9 by omega,
      show ¬ k + 15 = 10 by omega,
      show ¬ k + 15 = 11 by omega,
      show ¬ k + 15 = 12 by omega,
      show ¬ k + 15 = 13 by omega,
      show ¬ k + 15 = 14 by omega, if_true, if_false]
    linear_combination hq

/-! ## The closed form -/

/-- The closed form as a polynomial in x = n and e = (-1)^n. -/
def Fc (x e : ℚ) : ℚ := (315 * (2889 - 841 * e) + (537927 - 96327 * e) * x - 21 * (-4723 + 755 * e) * x ^ 2 - 7 * (-1469 + 45 * e) * x ^ 3 - 105 * (3 + 5 * e) * x ^ 4 - 7 * (-29 + 9 * e) * x ^ 5 + 42 * x ^ 6 + 2 * x ^ 7) / 645120

def Fq (n : ℕ) : ℚ := Fc n ((-1) ^ n)

set_option maxHeartbeats 1000000 in
lemma F_rel (n : ℕ) : Fq (n + 14) + 12 * Fq (n + 11) + 9 * Fq (n + 10) + 40 * Fq (n + 7) + 9 * Fq (n + 4) + 12 * Fq (n + 3) + Fq n = 2 * Fq (n + 13) + 5 * Fq (n + 12) + 30 * Fq (n + 9) + 5 * Fq (n + 8) + 5 * Fq (n + 6) + 30 * Fq (n + 5) + 5 * Fq (n + 2) + 2 * Fq (n + 1) := by
  simp only [Fq, Fc, pow_add]
  push_cast
  ring

set_option maxHeartbeats 1000000 in
lemma a_eq_F : ∀ n : ℕ, 1 ≤ n → (a n : ℚ) = Fq n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases Nat.lt_or_ge n 15 with h | h
    · interval_cases n <;> simp only [a_v1, a_v2, a_v3, a_v4, a_v5, a_v6, a_v7, a_v8, a_v9, a_v10, a_v11, a_v12, a_v13, a_v14, Fq, Fc] <;> norm_num
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 15 := ⟨n - 15, by omega⟩
      have hr := a_rel (k + 1)
      have hF := F_rel (k + 1)
      have i1 := ih (k + 1) (by omega) (by omega)
      have i2 := ih (k + 2) (by omega) (by omega)
      have i3 := ih (k + 3) (by omega) (by omega)
      have i4 := ih (k + 4) (by omega) (by omega)
      have i5 := ih (k + 5) (by omega) (by omega)
      have i6 := ih (k + 6) (by omega) (by omega)
      have i7 := ih (k + 7) (by omega) (by omega)
      have i8 := ih (k + 8) (by omega) (by omega)
      have i9 := ih (k + 9) (by omega) (by omega)
      have i10 := ih (k + 10) (by omega) (by omega)
      have i11 := ih (k + 11) (by omega) (by omega)
      have i12 := ih (k + 12) (by omega) (by omega)
      have i13 := ih (k + 13) (by omega) (by omega)
      have i14 := ih (k + 14) (by omega) (by omega)
      have hq : (a (k + 1 + 14) : ℚ) + 12 * a (k + 1 + 11) + 9 * a (k + 1 + 10) + 40 * a (k + 1 + 7) + 9 * a (k + 1 + 4) + 12 * a (k + 1 + 3) + a (k + 1) = 2 * (a (k + 1 + 13) : ℚ) + 5 * a (k + 1 + 12) + 30 * a (k + 1 + 9) + 5 * a (k + 1 + 8) + 5 * a (k + 1 + 6) + 30 * a (k + 1 + 5) + 5 * a (k + 1 + 2) + 2 * a (k + 1 + 1) := by exact_mod_cast hr
      simp only [show k + 1 + 1 = k + 2 from rfl, show k + 1 + 2 = k + 3 from rfl, show k + 1 + 3 = k + 4 from rfl, show k + 1 + 4 = k + 5 from rfl, show k + 1 + 5 = k + 6 from rfl, show k + 1 + 6 = k + 7 from rfl, show k + 1 + 7 = k + 8 from rfl, show k + 1 + 8 = k + 9 from rfl, show k + 1 + 9 = k + 10 from rfl, show k + 1 + 10 = k + 11 from rfl, show k + 1 + 11 = k + 12 from rfl, show k + 1 + 12 = k + 13 from rfl, show k + 1 + 13 = k + 14 from rfl, show k + 1 + 14 = k + 15 from rfl] at hF hq
      linarith

/-- Barker's closed form. -/
theorem closed_form : ∀ n : ℕ, 1 ≤ n → (a n : ℚ) =
    (315 * (2889 - 841 * (-1) ^ n) + (537927 - 96327 * (-1) ^ n) * n - 21 * (-4723 + 755 * (-1) ^ n) * n ^ 2 - 7 * (-1469 + 45 * (-1) ^ n) * n ^ 3 - 105 * (3 + 5 * (-1) ^ n) * n ^ 4 - 7 * (-29 + 9 * (-1) ^ n) * n ^ 5 + 42 * n ^ 6 + 2 * n ^ 7) / 645120 := by
  intro n hn
  rw [a_eq_F n hn]
  simp only [Fq, Fc]

/-- Both of Barker's conjectures. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * ((1 - X) ^ 8 * (1 + X) ^ 6) =
      X * (3 - 3 * X - 14 * X ^ 2 + 14 * X ^ 3 + 30 * X ^ 4 - 29 * X ^ 5 - 31 * X ^ 6 + 31 * X ^ 7 + 20 * X ^ 8 - 20 * X ^ 9 - 7 * X ^ 10 + 7 * X ^ 11 + X ^ 12 - X ^ 13) ∧
    ∀ n : ℕ, 1 ≤ n → (a n : ℚ) =
      (315 * (2889 - 841 * (-1) ^ n) + (537927 - 96327 * (-1) ^ n) * n - 21 * (-4723 + 755 * (-1) ^ n) * n ^ 2 - 7 * (-1469 + 45 * (-1) ^ n) * n ^ 3 - 105 * (3 + 5 * (-1) ^ n) * n ^ 4 - 7 * (-29 + 9 * (-1) ^ n) * n ^ 5 + 42 * n ^ 6 + 2 * n ^ 7) / 645120 :=
  ⟨gf, closed_form⟩

set_option maxHeartbeats 2000000 in
/-- Controls: the entry's data a(1..40), from the closed form. -/
theorem controls :
    a 1 = 3 ∧ a 2 = 3 ∧ a 3 = 7 ∧ a 4 = 7 ∧ a 5 = 16 ∧ a 6 = 17 ∧ a 7 = 41 ∧ a 8 = 48 ∧ a 9 = 113 ∧
    a 10 = 141 ∧ a 11 = 303 ∧ a 12 = 387 ∧ a 13 = 752 ∧ a 14 = 962 ∧ a 15 = 1713 ∧ a 16 = 2175 ∧
    a 17 = 3607 ∧ a 18 = 4531 ∧ a 19 = 7095 ∧ a 20 = 8811 ∧ a 21 = 13168 ∧ a 22 = 16171 ∧
    a 23 = 23257 ∧ a 24 = 28262 ∧ a 25 = 39365 ∧ a 26 = 47373 ∧ a 27 = 64223 ∧ a 28 = 76599 ∧
    a 29 = 101472 ∧ a 30 = 120036 ∧ a 31 = 155873 ∧ a 32 = 183005 ∧ a 33 = 233547 ∧ a 34 = 272307 ∧
    a 35 = 342247 ∧ a 36 = 396511 ∧ a 37 = 491664 ∧ a 38 = 566277 ∧ a 39 = 693769 ∧ a 40 = 794716 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩ <;>
  · rw [← Nat.cast_inj (R := ℚ), a_eq_F _ (by norm_num)]
    simp only [Fq, Fc]
    norm_num

end OMA.S_oeis_a263869

theorem OMA.solution : type_of% @OMA.S_oeis_a263869.main :=
  OMA.S_oeis_a263869.conjecture
