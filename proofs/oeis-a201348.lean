import OMAStatements.S_oeis_a201348

namespace OMA.S_oeis_a201348

open PowerSeries Finset


instance {m q : ℕ} : DecidableRel (@lexLE m q) := fun u v => by unfold lexLE; infer_instance


instance {m : ℕ} : DecidableRel (@adj m) := fun a b => by unfold adj; infer_instance


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

def PT {m : ℕ} : T2 → (Fin m → Fin 2) → (Fin m → Fin 2) → Prop
  | .z, u, v => lexLE u v
  | .d, _, _ => True

instance {m : ℕ} (t : T2) (u v : Fin m → Fin 2) : Decidable (PT t u v) := by
  cases t <;> unfold PT <;> infer_instance

def okT (t : T2) (x y : Fin 2) : Prop := t = .z → x ≤ y

instance (t : T2) (x y : Fin 2) : Decidable (okT t x y) := by
  unfold okT; infer_instance

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

/-! ## Neighbors -/

/-- The element in column j of the row r has an equal horizontal neighbor. -/
def hnb (r : Fin 3 → Fin 2) (j : Fin 3) : Prop := ∃ j' : Fin 3, adj j j' ∧ r j' = r j

/-- The element in row i, column j of y has an equal vertical neighbor. -/
def vnb {m : ℕ} (y : Fin m → Fin 3 → Fin 2) (i : Fin m) (j : Fin 3) : Prop :=
  ∃ i' : Fin m, adj i i' ∧ y i' j = y i j

instance (r : Fin 3 → Fin 2) (j : Fin 3) : Decidable (hnb r j) := by unfold hnb; infer_instance

instance {m : ℕ} (y : Fin m → Fin 3 → Fin 2) (i : Fin m) (j : Fin 3) : Decidable (vnb y i j) := by
  unfold vnb; infer_instance

lemma vnb_cons_zero {m : ℕ} (s : Fin 3 → Fin 2) (g : Fin m → Fin 3 → Fin 2) (j : Fin 3) :
    vnb (Fin.cons s g : Fin (m + 1) → Fin 3 → Fin 2) 0 j ↔ ∃ h : 0 < m, g ⟨0, h⟩ j = s j := by
  unfold vnb adj
  constructor
  · rintro ⟨i', hi', he⟩
    induction i' using Fin.cases with
    | zero => simp at hi'
    | succ i =>
      have hi0 : i.val = 0 := by simp at hi'; omega
      refine ⟨by have := i.isLt; omega, ?_⟩
      have : i = ⟨0, by have := i.isLt; omega⟩ := Fin.ext hi0
      rw [← this]
      simpa using he
  · rintro ⟨h, he⟩
    refine ⟨Fin.succ ⟨0, h⟩, by simp, ?_⟩
    rw [Fin.cons_succ, Fin.cons_zero]
    exact he

lemma vnb_cons_one {m : ℕ} (r s : Fin 3 → Fin 2) (g : Fin m → Fin 3 → Fin 2) (j : Fin 3) :
    vnb (Fin.cons r (Fin.cons s g) : Fin (m + 2) → Fin 3 → Fin 2) (Fin.succ 0) j ↔
      r j = s j ∨ ∃ h : 0 < m, g ⟨0, h⟩ j = s j := by
  unfold vnb adj
  constructor
  · rintro ⟨i', hi', he⟩
    induction i' using Fin.cases with
    | zero => left; simpa using he
    | succ i =>
      induction i using Fin.cases with
      | zero => simp at hi'
      | succ i =>
        right
        have hi0 : i.val = 0 := by simp at hi'; omega
        refine ⟨by have := i.isLt; omega, ?_⟩
        have : i = ⟨0, by have := i.isLt; omega⟩ := Fin.ext hi0
        rw [← this]
        simpa using he
  · rintro (he | ⟨h, he⟩)
    · refine ⟨0, by simp, ?_⟩
      rw [Fin.cons_zero, Fin.cons_succ, Fin.cons_zero]
      exact he
    · refine ⟨Fin.succ (Fin.succ ⟨0, h⟩), by simp, ?_⟩
      rw [Fin.cons_succ, Fin.cons_succ, Fin.cons_succ, Fin.cons_zero]
      exact he

lemma vnb_cons_ss {m : ℕ} (r : Fin 3 → Fin 2) (y : Fin (m + 1) → Fin 3 → Fin 2) (i : Fin m)
    (j : Fin 3) :
    vnb (Fin.cons r y : Fin (m + 2) → Fin 3 → Fin 2) i.succ.succ j ↔ vnb y i.succ j := by
  unfold vnb adj
  constructor
  · rintro ⟨i', hi', he⟩
    induction i' using Fin.cases with
    | zero => simp at hi'
    | succ k =>
      refine ⟨k, ?_, by simpa using he⟩
      simp only [Fin.val_succ] at hi' ⊢
      omega
  · rintro ⟨k, hk, he⟩
    refine ⟨k.succ, ?_, by simpa using he⟩
    simp only [Fin.val_succ] at hk ⊢
    omega

/-! ## The arrays the proof counts -/

/-- Consecutive rows are lexicographically nondecreasing. -/
def chain {m : ℕ} (y : Fin m → Fin 3 → Fin 2) : Prop :=
  ∀ i i' : Fin m, i.val + 1 = i'.val → lexLE (y i) (y i')

instance {m : ℕ} : DecidablePred (@chain m) := fun y => by unfold chain; infer_instance

def col {m : ℕ} (f : Fin m → Fin 3 → Fin 2) (j : Fin 3) : Fin m → Fin 2 := fun i => f i j

/-- Every element has an equal horizontal or vertical neighbor. -/
def nbr {m : ℕ} (y : Fin m → Fin 3 → Fin 2) : Prop := ∀ i j, hnb (y i) j ∨ vnb y i j

def core {m : ℕ} (y : Fin m → Fin 3 → Fin 2) : Prop :=
  chain y ∧ (∀ j : Fin 2, PT .z (col y j.castSucc) (col y j.succ)) ∧ nbr y

instance {m : ℕ} : DecidablePred (@core m) := fun y => by
  unfold core nbr; infer_instance

/-- The neighbor condition for the rows f below the row r, whose elements have an equal neighbor
in their row or above exactly where the flag fl is true. -/
def NBc {m : ℕ} (fl : Fin 3 → Bool) (r : Fin 3 → Fin 2) (f : Fin m → Fin 3 → Fin 2) : Prop :=
  (∀ j, fl j = false → ∃ h : 0 < m, f ⟨0, h⟩ j = r j) ∧
    ∀ i : Fin m, ∀ j, hnb (f i) j ∨ vnb (Fin.cons r f : Fin (m + 1) → Fin 3 → Fin 2) i.succ j

def Cont {m : ℕ} (τ : Fin 2 → T2) (fl : Fin 3 → Bool) (r : Fin 3 → Fin 2)
    (f : Fin m → Fin 3 → Fin 2) : Prop :=
  chain (Fin.cons r f : Fin (m + 1) → Fin 3 → Fin 2) ∧
    (∀ j : Fin 2, PT (τ j) (col f j.castSucc) (col f j.succ)) ∧ NBc fl r f

instance {m : ℕ} (τ : Fin 2 → T2) (fl : Fin 3 → Bool) (r : Fin 3 → Fin 2) :
    DecidablePred (@Cont m τ fl r) := fun f => by unfold Cont NBc; infer_instance

def okR (τ : Fin 2 → T2) (s : Fin 3 → Fin 2) : Prop :=
  ∀ j : Fin 2, okT (τ j) (s j.castSucc) (s j.succ)

/-- Elements of r without a neighbor yet keep their value in the next row s. -/
def okF (fl : Fin 3 → Bool) (r s : Fin 3 → Fin 2) : Prop := ∀ j, fl j = true ∨ s j = r j

instance (τ : Fin 2 → T2) : DecidablePred (okR τ) := fun s => by unfold okR; infer_instance

instance (fl : Fin 3 → Bool) (r : Fin 3 → Fin 2) : DecidablePred (okF fl r) := fun s => by
  unfold okF; infer_instance

def stpR (τ : Fin 2 → T2) (s : Fin 3 → Fin 2) : Fin 2 → T2 :=
  fun j => stpT (τ j) (s j.castSucc) (s j.succ)

/-- The flags of the next row s below r. -/
def flR (r s : Fin 3 → Fin 2) : Fin 3 → Bool := fun j => decide (hnb s j ∨ r j = s j)

def flH (s : Fin 3 → Fin 2) : Fin 3 → Bool := fun j => decide (hnb s j)

lemma col_cons {m : ℕ} (s : Fin 3 → Fin 2) (g : Fin m → Fin 3 → Fin 2) (j : Fin 3) :
    col (Fin.cons s g : Fin (m + 1) → Fin 3 → Fin 2) j = Fin.cons (s j) (col g j) := by
  funext i
  induction i using Fin.cases <;> rfl

lemma chain_cons2 {m : ℕ} (r s : Fin 3 → Fin 2) (g : Fin m → Fin 3 → Fin 2) :
    chain (Fin.cons r (Fin.cons s g) : Fin (m + 2) → Fin 3 → Fin 2) ↔
      lexLE r s ∧ chain (Fin.cons s g : Fin (m + 1) → Fin 3 → Fin 2) := by
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

lemma chain_one (f : Fin 1 → Fin 3 → Fin 2) : chain f := by
  intro i j hij
  have := j.isLt
  have := i.isLt
  omega

lemma NBc_cons {m : ℕ} (fl : Fin 3 → Bool) (r s : Fin 3 → Fin 2) (g : Fin m → Fin 3 → Fin 2) :
    NBc fl r (Fin.cons s g) ↔ okF fl r s ∧ NBc (flR r s) s g := by
  unfold NBc okF flR
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun j => ?_, fun j hj => ?_, fun i j => ?_⟩
    · by_cases hf : fl j = true
      · exact Or.inl hf
      · obtain ⟨_, he⟩ := h1 j (by simpa using hf)
        right
        simpa using he
    · have h0 := h2 0 j
      simp only [Fin.cons_zero, decide_eq_false_iff_not, not_or] at hj
      rcases h0 with h0 | h0
      · exact absurd h0 hj.1
      · rw [vnb_cons_one] at h0
        rcases h0 with h0 | h0
        · exact absurd h0 hj.2
        · exact h0
    · have h0 := h2 i.succ j
      simp only [Fin.cons_succ] at h0
      rcases h0 with h0 | h0
      · exact Or.inl h0
      · right
        exact (vnb_cons_ss r _ i j).1 h0
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun j hj => ⟨Nat.succ_pos m, ?_⟩, fun i j => ?_⟩
    · rcases h1 j with h | h
      · rw [h] at hj; exact absurd hj (by decide)
      · simpa using h
    · induction i using Fin.cases with
      | zero =>
        simp only [Fin.cons_zero]
        by_cases hh : hnb s j
        · exact Or.inl hh
        · right
          rw [vnb_cons_one]
          by_cases hr : r j = s j
          · exact Or.inl hr
          · right
            exact h2 j (by simp [hh, hr])
      | succ i =>
        simp only [Fin.cons_succ]
        rcases h3 i j with h | h
        · exact Or.inl h
        · right
          exact (vnb_cons_ss r _ i j).2 h

lemma NBc_nil (fl : Fin 3 → Bool) (r : Fin 3 → Fin 2) (f : Fin 0 → Fin 3 → Fin 2) :
    NBc fl r f ↔ ∀ j, fl j = true := by
  unfold NBc
  constructor
  · rintro ⟨h1, _⟩ j
    by_contra hj
    obtain ⟨h, _⟩ := h1 j (by simpa using hj)
    exact absurd h (lt_irrefl 0)
  · intro h
    refine ⟨fun j hj => absurd (h j) (by simp [hj]), fun i => i.elim0⟩

lemma Cont_cons {m : ℕ} (τ : Fin 2 → T2) (fl : Fin 3 → Bool) (r s : Fin 3 → Fin 2)
    (g : Fin m → Fin 3 → Fin 2) :
    Cont τ fl r (Fin.cons s g) ↔ lexLE r s ∧ (okR τ s ∧ okF fl r s) ∧
      Cont (stpR τ s) (flR r s) s g := by
  unfold Cont okR stpR
  rw [chain_cons2, NBc_cons]
  simp only [col_cons, PT_cons]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4, h5⟩
    exact ⟨h1, ⟨fun j => (h3 j).1, h4⟩, h2, fun j => (h3 j).2, h5⟩
  · rintro ⟨h1, ⟨h3, h4⟩, h2, h6, h5⟩
    exact ⟨⟨h1, h2⟩, fun j => ⟨h3 j, h6 j⟩, h4, h5⟩

lemma Cont_nil (τ : Fin 2 → T2) (fl : Fin 3 → Bool) (r : Fin 3 → Fin 2)
    (f : Fin 0 → Fin 3 → Fin 2) : Cont τ fl r f ↔ ∀ j, fl j = true := by
  unfold Cont
  rw [NBc_nil]
  exact ⟨fun h => h.2.2, fun h => ⟨chain_one _, fun j => PT_nil _ _ _, h⟩⟩

lemma nbr_cons {m : ℕ} (s : Fin 3 → Fin 2) (g : Fin m → Fin 3 → Fin 2) :
    nbr (Fin.cons s g : Fin (m + 1) → Fin 3 → Fin 2) ↔ NBc (flH s) s g := by
  unfold nbr NBc flH
  constructor
  · intro h
    refine ⟨fun j hj => ?_, fun i j => ?_⟩
    · simp only [decide_eq_false_iff_not] at hj
      rcases h 0 j with h0 | h0
      · exact absurd (by simpa using h0) hj
      · exact (vnb_cons_zero s g j).1 h0
    · have := h i.succ j
      simpa using this
  · rintro ⟨h1, h2⟩ i j
    induction i using Fin.cases with
    | zero =>
      simp only [Fin.cons_zero]
      by_cases hh : hnb s j
      · exact Or.inl hh
      · exact Or.inr ((vnb_cons_zero s g j).2 (h1 j (by simp [hh])))
    | succ i =>
      have := h2 i j
      simpa using this

lemma core_cons {m : ℕ} (s : Fin 3 → Fin 2) (g : Fin m → Fin 3 → Fin 2) :
    core (Fin.cons s g : Fin (m + 1) → Fin 3 → Fin 2) ↔
      okR (fun _ => .z) s ∧ Cont (stpR (fun _ => .z) s) (flH s) s g := by
  unfold core Cont okR stpR
  rw [nbr_cons]
  simp only [col_cons, PT_cons]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨fun j => (h2 j).1, h1, fun j => (h2 j).2, h3⟩
  · rintro ⟨h2, h1, h4, h3⟩
    exact ⟨h1, fun j => ⟨h2 j, h4 j⟩, h3⟩

lemma good_iff_core {n : ℕ} (x : Fin n → Fin 3 → Fin 2) : good x ↔ core x := by
  unfold good core chain nbr hnb vnb col
  refine and_congr Iff.rfl (and_congr ⟨fun h j => h j.castSucc j.succ (by simp), fun h j j' hj => ?_⟩ ?_)
  · have hj3 : j.val < 2 := by have := j'.isLt; omega
    have e1 : j = (⟨j.val, hj3⟩ : Fin 2).castSucc := Fin.ext rfl
    have e2 : j' = (⟨j.val, hj3⟩ : Fin 2).succ := Fin.ext (by simp; omega)
    rw [e1, e2]
    exact h _
  · refine forall_congr' (fun i => forall_congr' (fun j => ?_))
    constructor
    · rintro ⟨i', j', (⟨rfl, h⟩ | ⟨h, rfl⟩), he⟩
      · exact Or.inl ⟨j', h, he⟩
      · exact Or.inr ⟨i', h, he⟩
    · rintro (⟨j', h, he⟩ | ⟨i', h, he⟩)
      · exact ⟨i, j', Or.inl ⟨rfl, h⟩, he⟩
      · exact ⟨i', j, Or.inr ⟨h, rfl⟩, he⟩

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

def F (m : ℕ) (τ : Fin 2 → T2) (fl : Fin 3 → Bool) (r : Fin 3 → Fin 2) : ℕ :=
  (univ.filter (fun f : Fin m → Fin 3 → Fin 2 => Cont τ fl r f)).card

lemma F_succ (m : ℕ) (τ : Fin 2 → T2) (fl : Fin 3 → Bool) (r : Fin 3 → Fin 2) :
    F (m + 1) τ fl r = ∑ s : Fin 3 → Fin 2,
      if lexLE r s ∧ (okR τ s ∧ okF fl r s) then F m (stpR τ s) (flR r s) s else 0 := by
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

lemma F_zero (τ : Fin 2 → T2) (fl : Fin 3 → Bool) (r : Fin 3 → Fin 2) :
    F 0 τ fl r = if ∀ j, fl j = true then 1 else 0 := by
  unfold F
  have hu : (univ : Finset (Fin 0 → Fin 3 → Fin 2)) = {Fin.elim0} := by
    ext g
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    funext i
    exact i.elim0
  rw [hu, Finset.filter_singleton]
  simp only [Cont_nil]
  split_ifs <;> simp

lemma a_succ (m : ℕ) : a (m + 1) = ∑ s : Fin 3 → Fin 2,
    if okR (fun _ => .z) s then F m (stpR (fun _ => .z) s) (flH s) s else 0 := by
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

def mk2 (t : T2) (f : T2 → ℕ) : ℕ :=
  match t with
  | .z => f .z
  | .d => f .d

lemma mk2_eq (t : T2) (f : T2 → ℕ) : mk2 t f = f t := by cases t <;> rfl

def mkB (b : Bool) (f : Bool → ℕ) : ℕ :=
  match b with
  | true => f true
  | false => f false

lemma mkB_eq (b : Bool) (f : Bool → ℕ) : mkB b f = f b := by cases b <;> rfl

def dg (c j : ℕ) : ℕ := c / 2 ^ j % 2

def okB (t : T2) (x y : ℕ) : Bool :=
  match t with
  | .z => decide (x ≤ y)
  | .d => true

def stpB (t : T2) (x y : ℕ) : T2 := if x = y then t else .d

/-- The element in column j of the row with code c has an equal horizontal neighbor. -/
def hnbB (c : ℕ) (j : ℕ) : Bool :=
  (decide (0 < j) && dg c j == dg c (j - 1)) || (decide (j + 1 < 3) && dg c j == dg c (j + 1))

def lexB : List ℕ → List ℕ → Bool
  | x :: xs, y :: ys => decide (x < y) || (decide (x = y) && lexB xs ys)
  | _, _ => true

def vB (r s : ℕ) : Bool :=
  lexB (List.ofFn (fun i : Fin 3 => dg r i)) (List.ofFn (fun i : Fin 3 => dg s i))

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

def allRows : List (Fin (2 ^ 3)) := List.finRange (2 ^ 3)

lemma sumL_allRows (g : Fin (2 ^ 3) → ℕ) : sumL allRows g = ∑ s, g s := by
  rw [sumL_eq, allRows, Fin.sum_univ_def]

def succL (r : Fin (2 ^ 3)) : List (Fin (2 ^ 3)) := allRows.filter (fun s => vB r s)

def cnt : ℕ → T2 → T2 → Bool → Bool → Bool → Fin (2 ^ 3) → ℕ
  | 0, t0, t1, b0, b1, b2, _ => if b0 && b1 && b2 then 1 else 0
  | m + 1, t0, t1, b0, b1, b2, r =>
      sumL (succL r) (fun s : Fin (2 ^ 3) =>
        if okB t0 (dg s 0) (dg s 1) && okB t1 (dg s 1) (dg s 2) && (b0 || dg s 0 == dg r 0) && (b1 || dg s 1 == dg r 1) && (b2 || dg s 2 == dg r 2) then
          mk2 (stpB t0 (dg s 0) (dg s 1)) (fun u0 => mk2 (stpB t1 (dg s 1) (dg s 2)) (fun u1 => mkB (hnbB s 0 || dg r 0 == dg s 0) (fun c0 => mkB (hnbB s 1 || dg r 1 == dg s 1) (fun c1 => mkB (hnbB s 2 || dg r 2 == dg s 2) (fun c2 => cnt m u0 u1 c0 c1 c2 s)))))
        else 0)

lemma ite_band (b c : Bool) (x : ℕ) :
    (if b = true then (if c = true then x else 0) else 0) = if (b && c) = true then x else 0 := by
  cases b <;> cases c <;> rfl

def dec : Fin (2 ^ 3) ≃ (Fin 3 → Fin 2) := finFunctionFinEquiv.symm

lemma dec_val (c : Fin (2 ^ 3)) (j : Fin 3) : (dec c j : ℕ) = dg c j :=
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

lemma flagB_iff (b : Bool) (x y : Fin 2) : (b || (x : ℕ) == (y : ℕ)) = true ↔ (b = true ∨ x = y) := by
  simp [Fin.ext_iff]

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

lemma vB_iff (r s : Fin (2 ^ 3)) : vB r s = true ↔ lexLE (dec r) (dec s) := by
  have e : ∀ c : Fin (2 ^ 3), List.ofFn (fun i : Fin 3 => dg c i) =
      List.ofFn (fun i => (dec c i : ℕ)) := fun c =>
    congrArg List.ofFn (funext fun i => (dec_val c i).symm)
  unfold vB
  rw [e, e, lexB_iff]

lemma hnbB_iff : ∀ (c : Fin (2 ^ 3)) (j : Fin 3), hnbB c j = true ↔ hnb (dec c) j := by
  decide +kernel

lemma okR_iff (τ : Fin 2 → T2) (fl : Fin 3 → Bool) (r s : Fin 3 → Fin 2) :
    okR τ s ∧ okF fl r s ↔ okT (τ 0) (s 0) (s 1) ∧ okT (τ 1) (s 1) (s 2) ∧ (fl 0 = true ∨ s 0 = r 0) ∧ (fl 1 = true ∨ s 1 = r 1) ∧ (fl 2 = true ∨ s 2 = r 2) := by
  unfold okR okF
  constructor
  · rintro ⟨h, h'⟩
    exact ⟨h 0, h 1, h' 0, h' 1, h' 2⟩
  · rintro ⟨h0, h1, h2, h3, h4⟩
    refine ⟨fun j => ?_, fun j => ?_⟩
    · fin_cases j
      · exact h0
      · exact h1
    · fin_cases j
      · exact h2
      · exact h3
      · exact h4

lemma acc_iff (b0 b1 b2 : Bool) : (b0 && b1 && b2) = true ↔ ∀ j, (![b0, b1, b2] : Fin 3 → Bool) j = true := by
  simp only [Bool.and_eq_true]
  constructor
  · rintro ⟨⟨h0, h1⟩, h2⟩ j
    fin_cases j
    · exact h0
    · exact h1
    · exact h2
  · intro h
    exact ⟨⟨h 0, h 1⟩, h 2⟩

lemma fl_val (r s : Fin (2 ^ 3)) (j : Fin 3) :
    (hnbB s j || (dec r j : ℕ) == (dec s j : ℕ)) = flR (dec r) (dec s) j := by
  unfold flR
  by_cases h : hnb (dec s) j ∨ dec r j = dec s j
  · rw [decide_eq_true h]
    rcases h with h | h
    · rw [(hnbB_iff s j).2 h]; rfl
    · rw [h]; simp
  · rw [decide_eq_false h]
    rw [not_or] at h
    have h1 : hnbB s j = false := by
      by_contra hc
      exact h.1 ((hnbB_iff s j).1 (by simpa using hc))
    rw [h1]
    simpa [Fin.ext_iff] using h.2

lemma fh_val (s : Fin (2 ^ 3)) (j : Fin 3) : hnbB s j = flH (dec s) j := by
  unfold flH
  by_cases h : hnb (dec s) j
  · rw [decide_eq_true h, (hnbB_iff s j).2 h]
  · rw [decide_eq_false h]
    by_contra hc
    exact h ((hnbB_iff s j).1 (by simpa using hc))

lemma cnt_eq : ∀ (m : ℕ) (t0 t1 : T2) (b0 b1 b2 : Bool) (r : Fin (2 ^ 3)),
    cnt m t0 t1 b0 b1 b2 r = F m ![t0, t1] ![b0, b1, b2] (dec r)
  | 0, t0, t1, b0, b1, b2, r => by
    rw [cnt, F_zero]
    by_cases h : (b0 && b1 && b2) = true
    · rw [if_pos h, if_pos ((acc_iff b0 b1 b2).1 h)]
    · rw [if_neg h, if_neg (fun h' => h ((acc_iff b0 b1 b2).2 h'))]
  | m + 1, t0, t1, b0, b1, b2, r => by
    rw [cnt, succL, sumL_filter, sumL_allRows, F_succ, ← Equiv.sum_comp dec]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [ite_band]
    simp only [mk2_eq, mkB_eq, cnt_eq m]
    have d0 : dg s 0 = (dec s 0 : ℕ) := (dec_val s 0).symm
    have d1 : dg s 1 = (dec s 1 : ℕ) := (dec_val s 1).symm
    have d2 : dg s 2 = (dec s 2 : ℕ) := (dec_val s 2).symm
    have e0 : dg r 0 = (dec r 0 : ℕ) := (dec_val r 0).symm
    have e1 : dg r 1 = (dec r 1 : ℕ) := (dec_val r 1).symm
    have e2 : dg r 2 = (dec r 2 : ℕ) := (dec_val r 2).symm
    rw [d0, d1, d2, e0, e1, e2]
    simp only [stpB_eq]
    have hst : stpR ![t0, t1] (dec s) = ![stpT t0 (dec s 0) (dec s 1), stpT t1 (dec s 1) (dec s 2)] := by
      funext j
      fin_cases j <;> rfl
    have hfl : flR (dec r) (dec s) = ![(hnbB s 0 || (dec r 0 : ℕ) == (dec s 0 : ℕ)), (hnbB s 1 || (dec r 1 : ℕ) == (dec s 1 : ℕ)), (hnbB s 2 || (dec r 2 : ℕ) == (dec s 2 : ℕ))] := by
      funext j
      fin_cases j <;> exact (fl_val r s _).symm
    have hc : (vB r s && (okB t0 (dec s 0) (dec s 1) && okB t1 (dec s 1) (dec s 2) && (b0 || (dec s 0 : ℕ) == (dec r 0 : ℕ)) && (b1 || (dec s 1 : ℕ) == (dec r 1 : ℕ)) && (b2 || (dec s 2 : ℕ) == (dec r 2 : ℕ)))) = true ↔
        lexLE (dec r) (dec s) ∧ (okR ![t0, t1] (dec s) ∧ okF ![b0, b1, b2] (dec r) (dec s)) := by
      rw [okR_iff]
      simp only [Bool.and_eq_true, vB_iff, okB_iff, flagB_iff, and_assoc]
      try exact Iff.rfl
    rw [hst, hfl]
    by_cases h : (vB r s && (okB t0 (dec s 0) (dec s 1) && okB t1 (dec s 1) (dec s 2) && (b0 || (dec s 0 : ℕ) == (dec r 0 : ℕ)) && (b1 || (dec s 1 : ℕ) == (dec r 1 : ℕ)) && (b2 || (dec s 2 : ℕ) == (dec r 2 : ℕ)))) = true
    · rw [if_pos h, if_pos (hc.1 h)]
    · rw [if_neg h, if_neg (fun h' => h (hc.2 h'))]

lemma cnt_succ (m : ℕ) (t0 t1 : T2) (b0 b1 b2 : Bool) (r : Fin (2 ^ 3)) :
    cnt (m + 1) t0 t1 b0 b1 b2 r = ∑ s : Fin (2 ^ 3),
      if (vB r s && (okB t0 (dg s 0) (dg s 1) && okB t1 (dg s 1) (dg s 2) && (b0 || dg s 0 == dg r 0) && (b1 || dg s 1 == dg r 1) && (b2 || dg s 2 == dg r 2))) = true then cnt m (stpB t0 (dg s 0) (dg s 1)) (stpB t1 (dg s 1) (dg s 2)) (hnbB s 0 || dg r 0 == dg s 0) (hnbB s 1 || dg r 1 == dg s 1) (hnbB s 2 || dg r 2 == dg s 2) s else 0 := by
  rw [cnt, succL, sumL_filter, sumL_allRows]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  simp only [ite_band, mk2_eq, mkB_eq]

def Sa (m : ℕ) : ℕ := sumL allRows (fun s : Fin (2 ^ 3) =>
    if okB .z (dg s 0) (dg s 1) && okB .z (dg s 1) (dg s 2) then cnt m (stpB .z (dg s 0) (dg s 1)) (stpB .z (dg s 1) (dg s 2)) (hnbB s 0) (hnbB s 1) (hnbB s 2) s else 0)

lemma a_succ' (m : ℕ) : a (m + 1) = Sa m := by
  unfold Sa
  rw [sumL_allRows, a_succ, ← Equiv.sum_comp dec]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [cnt_eq]
  have d0 : dg s 0 = (dec s 0 : ℕ) := (dec_val s 0).symm
  have d1 : dg s 1 = (dec s 1 : ℕ) := (dec_val s 1).symm
  have d2 : dg s 2 = (dec s 2 : ℕ) := (dec_val s 2).symm
  rw [d0, d1, d2]
  simp only [stpB_eq]
  have hst : stpR (fun _ => .z) (dec s) = ![stpT .z (dec s 0) (dec s 1), stpT .z (dec s 1) (dec s 2)] := by
    funext j
    fin_cases j <;> rfl
  have hfl : flH (dec s) = ![hnbB s 0, hnbB s 1, hnbB s 2] := by
    funext j
    fin_cases j <;> exact (fh_val s _).symm
  have hc : (okB .z (dec s 0) (dec s 1) && okB .z (dec s 1) (dec s 2)) = true ↔ okR (fun _ => .z) (dec s) := by
    unfold okR
    simp only [Bool.and_eq_true, okB_iff]
    constructor
    · intro h j
      fin_cases j <;> simp_all
    · intro h
      exact ⟨h 0, h 1⟩
  rw [hst, hfl]
  by_cases h : (okB .z (dec s 0) (dec s 1) && okB .z (dec s 1) (dec s 2)) = true
  · rw [if_pos h, if_pos (hc.1 h)]
  · rw [if_neg h, if_neg (fun h' => h (hc.2 h'))]

/-! ## The relation for every reachable state, from m = 2 on -/

def t2v : T2 → ℕ
  | .z => 0
  | .d => 1

def bv : Bool → ℕ
  | false => 0
  | true => 1

/-- The states reachable from the first row, as a bit mask (computed by a search outside Lean;
`chk` checks that it holds the starting states and is closed under the transitions). -/
def reachB (t0 t1 : T2) (b0 b1 b2 : Bool) (r : Fin (2 ^ 3)) : Bool :=
  Nat.testBit 0xee98c28102004200000000002000000028180000000000000400000020000000 ((2 ^ 0 * t2v t0 + 2 ^ 1 * t2v t1 + 2 ^ 2 * bv b0 + 2 ^ 3 * bv b1 + 2 ^ 4 * bv b2) * 8 + r)

def RL (m : ℕ) (t0 t1 : T2) (b0 b1 b2 : Bool) (r : Fin (2 ^ 3)) : ℕ :=
  cnt (m + 8) t0 t1 b0 b1 b2 r + 28 * cnt (m + 6) t0 t1 b0 b1 b2 r + 70 * cnt (m + 4) t0 t1 b0 b1 b2 r + 28 * cnt (m + 2) t0 t1 b0 b1 b2 r + cnt m t0 t1 b0 b1 b2 r

def RR (m : ℕ) (t0 t1 : T2) (b0 b1 b2 : Bool) (r : Fin (2 ^ 3)) : ℕ :=
  8 * cnt (m + 7) t0 t1 b0 b1 b2 r + 56 * cnt (m + 5) t0 t1 b0 b1 b2 r + 56 * cnt (m + 3) t0 t1 b0 b1 b2 r + 8 * cnt (m + 1) t0 t1 b0 b1 b2 r

def fA (s : Fin (2 ^ 3)) : Bool := !(okB .z (dg s 0) (dg s 1) && okB .z (dg s 1) (dg s 2)) || reachB (stpB .z (dg s 0) (dg s 1)) (stpB .z (dg s 1) (dg s 2)) (hnbB s 0) (hnbB s 1) (hnbB s 2) s

def fN (t0 t1 : T2) (b0 b1 b2 : Bool) (r s : Fin (2 ^ 3)) : Bool :=
  !(okB t0 (dg s 0) (dg s 1) && okB t1 (dg s 1) (dg s 2) && (b0 || dg s 0 == dg r 0) && (b1 || dg s 1 == dg r 1) && (b2 || dg s 2 == dg r 2)) || reachB (stpB t0 (dg s 0) (dg s 1)) (stpB t1 (dg s 1) (dg s 2)) (hnbB s 0 || dg r 0 == dg s 0) (hnbB s 1 || dg r 1 == dg s 1) (hnbB s 2 || dg r 2 == dg s 2) s

def fB (t0 t1 : T2) (b0 b1 b2 : Bool) (r : Fin (2 ^ 3)) : Bool :=
  !reachB t0 t1 b0 b1 b2 r || ((succL r).all (fun s => fN t0 t1 b0 b1 b2 r s) && RL 2 t0 t1 b0 b1 b2 r == RR 2 t0 t1 b0 b1 b2 r)

def fS : Bool := Sa 0 == 2 && Sa 1 == 8 && Sa 2 == 18 && Sa 3 == 47 && Sa 4 == 118 && Sa 5 == 273 && Sa 6 == 585 &&
  Sa 7 == 1174 && Sa 8 == 2228 && Sa 9 == 4030 && Sa 10 == 6992

def T2s : List T2 := [.z, .d]

def Bs : List Bool := [false, true]

def chk : Bool :=
  allRows.all fA && T2s.all (fun t0 => T2s.all (fun t1 => Bs.all (fun b0 => Bs.all (fun b1 => Bs.all (fun b2 => allRows.all (fun r => fB t0 t1 b0 b1 b2 r)))))) && fS

lemma chk_true : chk = true := by decide +kernel

lemma allRows_all {p : Fin (2 ^ 3) → Bool} (h : allRows.all p = true) (s : Fin (2 ^ 3)) :
    p s = true := List.all_eq_true.1 h s (List.mem_finRange s)

lemma T2s_all {p : T2 → Bool} (h : T2s.all p = true) (t : T2) : p t = true :=
  List.all_eq_true.1 h t (by cases t <;> simp [T2s])

lemma Bs_all {p : Bool → Bool} (h : Bs.all p = true) (b : Bool) : p b = true :=
  List.all_eq_true.1 h b (by cases b <;> simp [Bs])

lemma imp_of_bool {b c : Bool} (h : (!b || c) = true) (hb : b = true) : c = true := by
  cases b <;> cases c <;> simp_all

lemma chk_parts : (∀ s, fA s = true) ∧ (∀ (t0 t1 : T2) (b0 b1 b2 : Bool) r, fB t0 t1 b0 b1 b2 r = true) ∧
    fS = true := by
  have h := chk_true
  simp only [chk, Bool.and_eq_true] at h
  exact ⟨fun s => allRows_all h.1.1 s, fun t0 t1 b0 b1 b2 r => allRows_all (Bs_all (Bs_all (Bs_all (T2s_all (T2s_all (h.1.2) t0) t1) b0) b1) b2) r, h.2⟩

lemma reach_init : ∀ s : Fin (2 ^ 3), (okB .z (dg s 0) (dg s 1) && okB .z (dg s 1) (dg s 2)) = true → reachB (stpB .z (dg s 0) (dg s 1)) (stpB .z (dg s 1) (dg s 2)) (hnbB s 0) (hnbB s 1) (hnbB s 2) s = true :=
  fun s hs => imp_of_bool (chk_parts.1 s) hs

lemma fB_parts (t0 t1 : T2) (b0 b1 b2 : Bool) (r : Fin (2 ^ 3)) (hr : reachB t0 t1 b0 b1 b2 r = true) :
    (∀ s ∈ succL r, fN t0 t1 b0 b1 b2 r s = true) ∧ RL 2 t0 t1 b0 b1 b2 r = RR 2 t0 t1 b0 b1 b2 r := by
  have h := chk_parts.2.1 t0 t1 b0 b1 b2 r
  unfold fB at h
  rw [hr] at h
  simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨List.all_eq_true.1 h.1, h.2⟩

lemma reach_next : ∀ (t0 t1 : T2) (b0 b1 b2 : Bool) (r : Fin (2 ^ 3)), reachB t0 t1 b0 b1 b2 r = true →
    ∀ s : Fin (2 ^ 3), (vB r s && (okB t0 (dg s 0) (dg s 1) && okB t1 (dg s 1) (dg s 2) && (b0 || dg s 0 == dg r 0) && (b1 || dg s 1 == dg r 1) && (b2 || dg s 2 == dg r 2))) = true → reachB (stpB t0 (dg s 0) (dg s 1)) (stpB t1 (dg s 1) (dg s 2)) (hnbB s 0 || dg r 0 == dg s 0) (hnbB s 1 || dg r 1 == dg s 1) (hnbB s 2 || dg r 2 == dg s 2) s = true := by
  intro t0 t1 b0 b1 b2 r hr s hs
  rw [Bool.and_eq_true] at hs
  have hm : s ∈ succL r := List.mem_filter.2 ⟨List.mem_finRange s, hs.1⟩
  exact imp_of_bool ((fB_parts t0 t1 b0 b1 b2 r hr).1 s hm) hs.2

lemma kernel_facts : Sa 0 = 2 ∧ Sa 1 = 8 ∧ Sa 2 = 18 ∧ Sa 3 = 47 ∧ Sa 4 = 118 ∧ Sa 5 = 273 ∧ Sa 6 = 585 ∧ Sa 7 = 1174 ∧
    Sa 8 = 2228 ∧ Sa 9 = 4030 ∧ Sa 10 = 6992 := by
  have h := chk_parts.2.2
  simp only [fS, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1.1.1.1.1.1.1.1, h.1.1.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.2, h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

lemma R_all (k : ℕ) : ∀ (t0 t1 : T2) (b0 b1 b2 : Bool) (r : Fin (2 ^ 3)), reachB t0 t1 b0 b1 b2 r = true →
    RL (2 + k) t0 t1 b0 b1 b2 r = RR (2 + k) t0 t1 b0 b1 b2 r := by
  induction k with
  | zero => exact fun t0 t1 b0 b1 b2 r hr => (fB_parts t0 t1 b0 b1 b2 r hr).2
  | succ k ih =>
    intro t0 t1 b0 b1 b2 r h
    rw [show 2 + (k + 1) = (2 + k) + 1 from rfl]
    generalize 2 + k = m at ih ⊢
    unfold RL RR
    rw [show m + 1 + 8 = (m + 8) + 1 from rfl, show m + 1 + 7 = (m + 7) + 1 from rfl, show m + 1 + 6 = (m + 6) + 1 from rfl, show m + 1 + 5 = (m + 5) + 1 from rfl, show m + 1 + 4 = (m + 4) + 1 from rfl, show m + 1 + 3 = (m + 3) + 1 from rfl, show m + 1 + 2 = (m + 2) + 1 from rfl, show m + 1 + 1 = (m + 1) + 1 from rfl,
      cnt_succ (m + 8), cnt_succ (m + 7), cnt_succ (m + 6), cnt_succ (m + 5), cnt_succ (m + 4), cnt_succ (m + 3), cnt_succ (m + 2), cnt_succ (m + 1), cnt_succ m]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    split_ifs with hc
    · exact ih _ _ _ _ _ s (reach_next t0 t1 b0 b1 b2 r h s hc)
    · simp

/-! ## Barker's recurrence and g.f. -/

lemma a_rel (n : ℕ) (hn : 2 ≤ n) : a (n + 9) + 28 * a (n + 7) + 70 * a (n + 5) + 28 * a (n + 3) + a (n + 1) =
    8 * a (n + 8) + 56 * a (n + 6) + 56 * a (n + 4) + 8 * a (n + 2) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 2 + k := ⟨n - 2, by omega⟩
  generalize hm : 2 + k = n
  rw [show n + 9 = (n + 8) + 1 from rfl, show n + 8 = (n + 7) + 1 from rfl, show n + 7 = (n + 6) + 1 from rfl, show n + 6 = (n + 5) + 1 from rfl, show n + 5 = (n + 4) + 1 from rfl, show n + 4 = (n + 3) + 1 from rfl, show n + 3 = (n + 2) + 1 from rfl, show n + 2 = (n + 1) + 1 from rfl,
    a_succ' (n + 8), a_succ' (n + 7), a_succ' (n + 6), a_succ' (n + 5), a_succ' (n + 4), a_succ' (n + 3), a_succ' (n + 2), a_succ' (n + 1), a_succ' n]
  simp only [Sa, sumL_allRows]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  split_ifs with hc
  · have := R_all k _ _ _ _ _ s (reach_init s hc)
    rw [hm] at this
    exact this
  · simp

lemma a_v1 : a 1 = 2 := (a_succ' 0).trans kernel_facts.1
lemma a_v2 : a 2 = 8 := (a_succ' 1).trans kernel_facts.2.1
lemma a_v3 : a 3 = 18 := (a_succ' 2).trans kernel_facts.2.2.1
lemma a_v4 : a 4 = 47 := (a_succ' 3).trans kernel_facts.2.2.2.1
lemma a_v5 : a 5 = 118 := (a_succ' 4).trans kernel_facts.2.2.2.2.1
lemma a_v6 : a 6 = 273 := (a_succ' 5).trans kernel_facts.2.2.2.2.2.1
lemma a_v7 : a 7 = 585 := (a_succ' 6).trans kernel_facts.2.2.2.2.2.2.1
lemma a_v8 : a 8 = 1174 := (a_succ' 7).trans kernel_facts.2.2.2.2.2.2.2.1
lemma a_v9 : a 9 = 2228 := (a_succ' 8).trans kernel_facts.2.2.2.2.2.2.2.2.1
lemma a_v10 : a 10 = 4030 := (a_succ' 9).trans kernel_facts.2.2.2.2.2.2.2.2.2.1
lemma a_v11 : a 11 = 6992 := (a_succ' 10).trans kernel_facts.2.2.2.2.2.2.2.2.2.2

/-- Barker's recurrence, for n > 9. -/
theorem recurrence (n : ℕ) (hn : 9 < n) :
    (a n : ℤ) = 8 * a (n - 1) - 28 * a (n - 2) + 56 * a (n - 3) - 70 * a (n - 4) + 56 * a (n - 5) - 28 * a (n - 6) + 8 * a (n - 7) - a (n - 8) := by
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
  rcases Nat.lt_or_ge n 11 with h | h
  · interval_cases n <;> simp_all <;> norm_num
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 9 := ⟨n - 9, by omega⟩
    have hr := a_rel k (by omega)
    simp only [show k + 9 - 1 = k + 8 by omega, show k + 9 - 2 = k + 7 by omega, show k + 9 - 3 = k + 6 by omega, show k + 9 - 4 = k + 5 by omega, show k + 9 - 5 = k + 4 by omega, show k + 9 - 6 = k + 3 by omega, show k + 9 - 7 = k + 2 by omega, show k + 9 - 8 = k + 1 by omega]
    have h' : (a (k + 9) : ℤ) + 28 * a (k + 7) + 70 * a (k + 5) + 28 * a (k + 3) + a (k + 1) =
        8 * (a (k + 8) : ℤ) + 56 * a (k + 6) + 56 * a (k + 4) + 8 * a (k + 2) := by exact_mod_cast hr
    linarith

set_option maxHeartbeats 1000000 in
/-- Barker's g.f. -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 8 =
      X * (2 - 8 * X + 10 * X ^ 2 + 15 * X ^ 3 - 62 * X ^ 4 + 85 * X ^ 5 - 59 * X ^ 6 + 20 * X ^ 7 - 2 * X ^ 8) := by
  set A : ℚ⟦X⟧ := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) with hA
  have e1 : A * (1 - X) ^ 8 =
      A - C 8 * (A * X ^ 1) + C 28 * (A * X ^ 2) - C 56 * (A * X ^ 3) + C 70 * (A * X ^ 4) - C 56 * (A * X ^ 5) + C 28 * (A * X ^ 6) - C 8 * (A * X ^ 7) + A * X ^ 8 := by
    simp only [map_ofNat]; ring
  have e2 : (X * (2 - 8 * X + 10 * X ^ 2 + 15 * X ^ 3 - 62 * X ^ 4 + 85 * X ^ 5 - 59 * X ^ 6 + 20 * X ^ 7 - 2 * X ^ 8) : ℚ⟦X⟧) =
      X ^ 1 * C 2 - X ^ 2 * C 8 + X ^ 3 * C 10 + X ^ 4 * C 15 - X ^ 5 * C 62 + X ^ 6 * C 85 - X ^ 7 * C 59 + X ^ 8 * C 20 - X ^ 9 * C 2 := by
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
  rcases Nat.lt_or_ge n 10 with hn | hn
  · interval_cases n <;> simp_all <;> norm_num
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 10 := ⟨n - 10, by omega⟩
    have h := recurrence (k + 10) (by omega)
    simp only [show k + 10 - 1 = k + 9 by omega, show k + 10 - 2 = k + 8 by omega, show k + 10 - 3 = k + 7 by omega, show k + 10 - 4 = k + 6 by omega, show k + 10 - 5 = k + 5 by omega, show k + 10 - 6 = k + 4 by omega, show k + 10 - 7 = k + 3 by omega, show k + 10 - 8 = k + 2 by omega] at h
    have hq : (a (k + 10) : ℚ) = 8 * (a (k + 9) : ℚ) - 28 * (a (k + 8) : ℚ) + 56 * (a (k + 7) : ℚ) - 70 * (a (k + 6) : ℚ) + 56 * (a (k + 5) : ℚ) - 28 * (a (k + 4) : ℚ) + 8 * (a (k + 3) : ℚ) - (a (k + 2) : ℚ) := by exact_mod_cast h
    simp only [show k + 10 - 1 = k + 9 by omega,
      show k + 10 - 2 = k + 8 by omega,
      show k + 10 - 3 = k + 7 by omega,
      show k + 10 - 4 = k + 6 by omega,
      show k + 10 - 5 = k + 5 by omega,
      show k + 10 - 6 = k + 4 by omega,
      show k + 10 - 7 = k + 3 by omega,
      show k + 10 - 8 = k + 2 by omega,
      show ¬ k + 10 = 0 by omega,
      show ¬ k + 9 = 0 by omega,
      show ¬ k + 8 = 0 by omega,
      show ¬ k + 7 = 0 by omega,
      show ¬ k + 6 = 0 by omega,
      show ¬ k + 5 = 0 by omega,
      show ¬ k + 4 = 0 by omega,
      show ¬ k + 3 = 0 by omega,
      show ¬ k + 2 = 0 by omega,
      show 1 ≤ k + 10 by omega,
      show 2 ≤ k + 10 by omega,
      show 3 ≤ k + 10 by omega,
      show 4 ≤ k + 10 by omega,
      show 5 ≤ k + 10 by omega,
      show 6 ≤ k + 10 by omega,
      show 7 ≤ k + 10 by omega,
      show 8 ≤ k + 10 by omega,
      show ¬ k + 10 = 1 by omega,
      show ¬ k + 10 = 2 by omega,
      show ¬ k + 10 = 3 by omega,
      show ¬ k + 10 = 4 by omega,
      show ¬ k + 10 = 5 by omega,
      show ¬ k + 10 = 6 by omega,
      show ¬ k + 10 = 7 by omega,
      show ¬ k + 10 = 8 by omega,
      show ¬ k + 10 = 9 by omega, if_true, if_false]
    linear_combination hq

/-- Both of Barker's conjectures. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 8 =
      X * (2 - 8 * X + 10 * X ^ 2 + 15 * X ^ 3 - 62 * X ^ 4 + 85 * X ^ 5 - 59 * X ^ 6 + 20 * X ^ 7 - 2 * X ^ 8) ∧
    ∀ n : ℕ, 9 < n →
      (a n : ℤ) = 8 * a (n - 1) - 28 * a (n - 2) + 56 * a (n - 3) - 70 * a (n - 4) + 56 * a (n - 5) - 28 * a (n - 6) + 8 * a (n - 7) - a (n - 8) :=
  ⟨gf, recurrence⟩

/-- Controls: the entry's data a(1..34). -/
theorem controls :
    a 1 = 2 ∧ a 2 = 8 ∧ a 3 = 18 ∧ a 4 = 47 ∧ a 5 = 118 ∧ a 6 = 273 ∧ a 7 = 585 ∧ a 8 = 1174 ∧
    a 9 = 2228 ∧ a 10 = 4030 ∧ a 11 = 6992 ∧ a 12 = 11697 ∧ a 13 = 18950 ∧ a 14 = 29839 ∧
    a 15 = 45807 ∧ a 16 = 68736 ∧ a 17 = 101044 ∧ a 18 = 145796 ∧ a 19 = 206830 ∧ a 20 = 288899 ∧
    a 21 = 397830 ∧ a 22 = 540701 ∧ a 23 = 726037 ∧ a 24 = 964026 ∧ a 25 = 1266756 ∧ a 26 = 1648474 ∧
    a 27 = 2125868 ∧ a 28 = 2718373 ∧ a 29 = 3448502 ∧ a 30 = 4342203 ∧ a 31 = 5429243 ∧
    a 32 = 6743620 ∧ a 33 = 8324004 ∧ a 34 = 10214208 := by
  have key : ∀ f : ℕ → ℕ, f 1 = 2 → f 2 = 8 → f 3 = 18 → f 4 = 47 → f 5 = 118 → f 6 = 273 → f 7 = 585 → f 8 = 1174 → f 9 = 2228 → f 10 = 4030 → f 11 = 6992 →
      (∀ n, 2 ≤ n → f (n + 9) + 28 * f (n + 7) + 70 * f (n + 5) + 28 * f (n + 3) + f (n + 1) = 8 * f (n + 8) + 56 * f (n + 6) + 56 * f (n + 4) + 8 * f (n + 2)) →
        f 1 = 2 ∧ f 2 = 8 ∧ f 3 = 18 ∧ f 4 = 47 ∧ f 5 = 118 ∧ f 6 = 273 ∧ f 7 = 585 ∧ f 8 = 1174 ∧
        f 9 = 2228 ∧ f 10 = 4030 ∧ f 11 = 6992 ∧ f 12 = 11697 ∧ f 13 = 18950 ∧ f 14 = 29839 ∧
        f 15 = 45807 ∧ f 16 = 68736 ∧ f 17 = 101044 ∧ f 18 = 145796 ∧ f 19 = 206830 ∧ f 20 = 288899 ∧
        f 21 = 397830 ∧ f 22 = 540701 ∧ f 23 = 726037 ∧ f 24 = 964026 ∧ f 25 = 1266756 ∧
        f 26 = 1648474 ∧ f 27 = 2125868 ∧ f 28 = 2718373 ∧ f 29 = 3448502 ∧ f 30 = 4342203 ∧
        f 31 = 5429243 ∧ f 32 = 6743620 ∧ f 33 = 8324004 ∧ f 34 = 10214208 := by
    intro f h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 hr
    have h12 : f 12 = 11697 := by
      have r := hr 3 (by norm_num)
      simp only [Nat.reduceAdd, Nat.reduceMul, h4, h5, h6, h7, h8, h9, h10, h11] at r
      omega
    have h13 : f 13 = 18950 := by
      have r := hr 4 (by norm_num)
      simp only [Nat.reduceAdd, Nat.reduceMul, h5, h6, h7, h8, h9, h10, h11, h12] at r
      omega
    have h14 : f 14 = 29839 := by
      have r := hr 5 (by norm_num)
      simp only [Nat.reduceAdd, Nat.reduceMul, h6, h7, h8, h9, h10, h11, h12, h13] at r
      omega
    have h15 : f 15 = 45807 := by
      have r := hr 6 (by norm_num)
      simp only [Nat.reduceAdd, Nat.reduceMul, h7, h8, h9, h10, h11, h12, h13, h14] at r
      omega
    have h16 : f 16 = 68736 := by
      have r := hr 7 (by norm_num)
      simp only [Nat.reduceAdd, Nat.reduceMul, h8, h9, h10, h11, h12, h13, h14, h15] at r
      omega
    have h17 : f 17 = 101044 := by
      have r := hr 8 (by norm_num)
      simp only [Nat.reduceAdd, Nat.reduceMul, h9, h10, h11, h12, h13, h14, h15, h16] at r
      omega
    have h18 : f 18 = 145796 := by
      have r := hr 9 (by norm_num)
      simp only [Nat.reduceAdd, Nat.reduceMul, h10, h11, h12, h13, h14, h15, h16, h17] at r
      omega
    have h19 : f 19 = 206830 := by
      have r := hr 10 (by norm_num)
      simp only [Nat.reduceAdd, Nat.reduceMul, h11, h12, h13, h14, h15, h16, h17, h18] at r
      omega
    have h20 : f 20 = 288899 := by
      have r := hr 11 (by norm_num)
      simp only [Nat.reduceAdd, Nat.reduceMul, h12, h13, h14, h15, h16, h17, h18, h19] at r
      omega
    have h21 : f 21 = 397830 := by
      have r := hr 12 (by norm_num)
      simp only [Nat.reduceAdd, Nat.reduceMul, h13, h14, h15, h16, h17, h18, h19, h20] at r
      omega
    have h22 : f 22 = 540701 := by
      have r := hr 13 (by norm_num)
      simp only [Nat.reduceAdd, Nat.reduceMul, h14, h15, h16, h17, h18, h19, h20, h21] at r
      omega
    have h23 : f 23 = 726037 := by
      have r := hr 14 (by norm_num)
      simp only [Nat.reduceAdd, Nat.reduceMul, h15, h16, h17, h18, h19, h20, h21, h22] at r
      omega
    have h24 : f 24 = 964026 := by
      have r := hr 15 (by norm_num)
      simp only [Nat.reduceAdd, Nat.reduceMul, h16, h17, h18, h19, h20, h21, h22, h23] at r
      omega
    have h25 : f 25 = 1266756 := by
      have r := hr 16 (by norm_num)
      simp only [Nat.reduceAdd, Nat.reduceMul, h17, h18, h19, h20, h21, h22, h23, h24] at r
      omega
    have h26 : f 26 = 1648474 := by
      have r := hr 17 (by norm_num)
      simp only [Nat.reduceAdd, Nat.reduceMul, h18, h19, h20, h21, h22, h23, h24, h25] at r
      omega
    have h27 : f 27 = 2125868 := by
      have r := hr 18 (by norm_num)
      simp only [Nat.reduceAdd, Nat.reduceMul, h19, h20, h21, h22, h23, h24, h25, h26] at r
      omega
    have h28 : f 28 = 2718373 := by
      have r := hr 19 (by norm_num)
      simp only [Nat.reduceAdd, Nat.reduceMul, h20, h21, h22, h23, h24, h25, h26, h27] at r
      omega
    have h29 : f 29 = 3448502 := by
      have r := hr 20 (by norm_num)
      simp only [Nat.reduceAdd, Nat.reduceMul, h21, h22, h23, h24, h25, h26, h27, h28] at r
      omega
    have h30 : f 30 = 4342203 := by
      have r := hr 21 (by norm_num)
      simp only [Nat.reduceAdd, Nat.reduceMul, h22, h23, h24, h25, h26, h27, h28, h29] at r
      omega
    have h31 : f 31 = 5429243 := by
      have r := hr 22 (by norm_num)
      simp only [Nat.reduceAdd, Nat.reduceMul, h23, h24, h25, h26, h27, h28, h29, h30] at r
      omega
    have h32 : f 32 = 6743620 := by
      have r := hr 23 (by norm_num)
      simp only [Nat.reduceAdd, Nat.reduceMul, h24, h25, h26, h27, h28, h29, h30, h31] at r
      omega
    have h33 : f 33 = 8324004 := by
      have r := hr 24 (by norm_num)
      simp only [Nat.reduceAdd, Nat.reduceMul, h25, h26, h27, h28, h29, h30, h31, h32] at r
      omega
    have h34 : f 34 = 10214208 := by
      have r := hr 25 (by norm_num)
      simp only [Nat.reduceAdd, Nat.reduceMul, h26, h27, h28, h29, h30, h31, h32, h33] at r
      omega
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34⟩
  exact key a a_v1 a_v2 a_v3 a_v4 a_v5 a_v6 a_v7 a_v8 a_v9 a_v10 a_v11 a_rel

end OMA.S_oeis_a201348

theorem OMA.solution : type_of% @OMA.S_oeis_a201348.main :=
  OMA.S_oeis_a201348.conjecture
