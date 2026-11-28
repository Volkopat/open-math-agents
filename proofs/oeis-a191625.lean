import OMAStatements.S_oeis_a191625
import Mathlib

/-!
# The corner-ending prudent walk recurrence

The walk count is split by its last strict increase of either coordinate maximum.
The resulting finite recurrence yields the kernel equation; evaluating at zero
and the small formal root gives a differential equation for the corner series.
The generating-function method follows M. Bousquet-Mélou, *Families of prudent
self-avoiding walks*, arXiv:0804.4843v3, Lemma 1 and Proposition 5.
-/

namespace OMA.S_oeis_a191625

namespace WalkDecomposition

variable {n : ℕ}

/-- Just the first two clauses of `valid`, suitable for an arbitrary prefix. -/
def Admissible (w : Fin n → Fin 4) : Prop :=
  (∀ (i : Fin n) (j : ℕ), j ≤ i.val → ∀ k : ℕ, 0 < k →
    pos w j ≠ pos w i.val + k • dir (w i)) ∧
  (∀ i ≤ n, (∀ j ≤ i, (pos w j).1 ≤ (pos w i).1) ∨
            (∀ j ≤ i, (pos w j).2 ≤ (pos w i).2))

def Right (w : Fin n → Fin 4) (i : ℕ) : Prop :=
  ∀ j ≤ i, (pos w j).1 ≤ (pos w i).1

def Top (w : Fin n → Fin 4) (i : ℕ) : Prop :=
  ∀ j ≤ i, (pos w j).2 ≤ (pos w i).2

def TopGap (w : Fin n → Fin 4) (d : ℤ) : Prop :=
  Admissible w ∧ Top w n ∧
    (∃ a ≤ n, (pos w a).1 - (pos w n).1 = d ∧
      ∀ b ≤ n, (pos w b).1 ≤ (pos w a).1)

theorem valid_iff_topGap_zero (w : Fin n → Fin 4) : valid w ↔ TopGap w 0 := by
  constructor
  · intro h
    exact ⟨⟨h.1, h.2.1⟩, fun j hj => (h.2.2 j hj).2,
      n, le_rfl, sub_self _, fun j hj => (h.2.2 j hj).1⟩
  · rintro ⟨⟨hray, hbox⟩, htop, a, _, ha, hmax⟩
    exact ⟨hray, hbox, fun j hj => ⟨(sub_eq_zero.mp ha) ▸ hmax j hj, htop j hj⟩⟩

noncomputable def C (n : ℕ) (d : ℤ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun w : Fin n → Fin 4 => TopGap w d)).card

theorem count_eq_C_zero (n : ℕ) : count n = (C n 0 : ℤ) := by
  classical
  unfold count C
  congr 2
  ext w
  simp [valid_iff_topGap_zero]

private theorem step (w : Fin n → Fin 4) (q : Fin n) :
    pos w (q.val+1) = pos w q.val + dir (w q) := by
  simp [pos, q.isLt]

private theorem dir_cases (d : Fin 4) : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by
  fin_cases d <;> decide

@[simp] private theorem dir_east : dir 0 = (1,0) := rfl
@[simp] private theorem dir_north : dir 1 = (0,1) := rfl
@[simp] private theorem dir_west : dir 2 = (-1,0) := rfl
@[simp] private theorem dir_south : dir 3 = (0,-1) := rfl

/-- A newly attained right edge stays occupied after the maxima stop increasing.
The old point at maximum height blocks a west ray even at a distance > 1. -/
theorem suffix_on_right {w : Fin n → Fin 4} (h : Admissible w) {m a : ℕ}
    (ha : a ≤ m)
    (hx : ∀ j ≤ n, (pos w j).1 ≤ (pos w (m+1)).1)
    (hy : ∀ j ≤ n, (pos w j).2 ≤ (pos w a).2)
    (hold : (pos w a).1 < (pos w (m+1)).1) :
    (∀ j, m < j → j ≤ n → (pos w j).1 = (pos w (m+1)).1) ∧
    (∀ q : Fin n, m < q.val → w q = 1 ∨ w q = 3) := by
  have single (q : Fin n) (hq : m < q.val)
      (hqX : (pos w q.val).1 = (pos w (m+1)).1) :
      (w q = 1 ∨ w q = 3) ∧ (pos w (q.val+1)).1 = (pos w (m+1)).1 := by
    have hstep := step w q
    have hnext : q.val+1 ≤ n := q.isLt
    rcases dir_cases (w q) with he | hn | hw | hs
    · rw [he, dir_east] at hstep
      have heX := congrArg Prod.fst hstep
      simp only [Prod.fst_add] at heX
      have := hx _ hnext
      omega
    · exact ⟨Or.inl hn, by simpa only [hstep, hn, dir_north, Prod.fst_add, add_zero] using hqX⟩
    · exfalso
      rw [hw, dir_west] at hstep
      have hwX := congrArg Prod.fst hstep
      have hwY := congrArg Prod.snd hstep
      simp only [Prod.fst_add] at hwX
      simp only [Prod.snd_add, add_zero] at hwY
      rcases h.2 _ hnext with hright | htop
      · have := hright (m+1) (by omega)
        omega
      · have htopQ := htop a (by omega)
        have hmaxQ := hy q.val (by omega)
        have hheight : (pos w a).2 = (pos w q.val).2 := by omega
        let k := ((pos w q.val).1 - (pos w a).1).toNat
        have hk : 0 < k := by dsimp [k]; omega
        have hkx : (k : ℤ) = (pos w q.val).1 - (pos w a).1 := by dsimp [k]; omega
        apply h.1 q a (by omega) k hk
        rw [hw, dir_west]
        apply Prod.ext
        · change (pos w a).1 = (pos w q.val).1 + k • (-1 : ℤ)
          rw [nsmul_eq_mul, mul_neg, mul_one]
          omega
        · change (pos w a).2 = (pos w q.val).2 + k • (0 : ℤ)
          simpa only [smul_zero, add_zero] using hheight
    · exact ⟨Or.inr hs, by simpa only [hstep, hs, dir_south, Prod.fst_add, add_zero] using hqX⟩
  have allX : ∀ j, m < j → j ≤ n → (pos w j).1 = (pos w (m+1)).1 := by
    intro j
    induction j with
    | zero => omega
    | succ j ih =>
      intro hm hj
      by_cases he : j = m
      · subst j; rfl
      · have hjn : j < n := by omega
        have hjm : m < j := by omega
        exact (single ⟨j, hjn⟩ hjm (ih hjm (Nat.le_of_lt hjn))).2
  exact ⟨allX, fun q hq => (single q hq (allX q.val hq (Nat.le_of_lt q.isLt))).1⟩

private theorem same_vertical {w : Fin n → Fin 4} (h : Admissible w)
    (a b : Fin n) (hab : b.val = a.val+1)
    (ha : w a = 1 ∨ w a = 3) (hb : w b = 1 ∨ w b = 3) : w a = w b := by
  have hs := step w a
  have his : a.val ≤ b.val := by omega
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exact ha.trans hb.symm
  · exfalso
    apply h.1 b a.val his 1 (by decide)
    rw [one_nsmul, hab, hs, ha, hb, dir_north, dir_south]
    apply Prod.ext <;> simp
  · exfalso
    apply h.1 b a.val his 1 (by decide)
    rw [one_nsmul, hab, hs, ha, hb, dir_south, dir_north]
    apply Prod.ext <;> simp
  · exact ha.trans hb.symm

/-- Empty suffixes satisfy both alternatives. For counting use the first branch
for the empty suffix, and require a nonempty suffix in the second branch. -/
theorem suffix_constant_vertical {w : Fin n → Fin 4} (h : Admissible w) (m : ℕ)
    (hv : ∀ q : Fin n, m < q.val → w q = 1 ∨ w q = 3) :
    (∀ q : Fin n, m < q.val → w q = 1) ∨ (∀ q : Fin n, m < q.val → w q = 3) := by
  by_cases hm : m+1 < n
  · let first : Fin n := ⟨m+1, hm⟩
    have constant : ∀ (j : ℕ) (hj : j < n), m < j → w ⟨j, hj⟩ = w first := by
      intro j
      induction j with
      | zero => omega
      | succ j ih =>
        intro hj hmj
        by_cases h : j = m
        · subst j; rfl
        · have jn : j < n := by omega
          have jm : m < j := by omega
          exact (same_vertical ‹Admissible w› ⟨j, jn⟩ ⟨j+1, hj⟩ rfl
            (hv _ jm) (hv _ hmj)).symm.trans (ih jn jm)
    rcases hv first (show m < m+1 by omega) with hf | hf
    · exact Or.inl fun q hq => (constant q.val q.isLt hq).trans hf
    · exact Or.inr fun q hq => (constant q.val q.isLt hq).trans hf
  · exact Or.inl fun q hq => False.elim (hm (lt_of_le_of_lt hq q.isLt))

/-- Frozen maxima and an old top witness imply the top-ending right-edge
suffix consists exclusively of north steps (or is empty). -/
theorem suffix_north_of_top {w : Fin n → Fin 4} (h : Admissible w) (ht : Top w n)
    {m a : ℕ} (hm : m < n) (ha : a ≤ m)
    (hx : ∀ j ≤ n, (pos w j).1 ≤ (pos w (m+1)).1)
    (hy : ∀ j ≤ n, (pos w j).2 ≤ (pos w a).2)
    (hold : (pos w a).1 < (pos w (m+1)).1) :
    Right w n ∧ (∀ q : Fin n, m < q.val → w q = 1) := by
  obtain ⟨hcol, hvertical⟩ := suffix_on_right h ha hx hy hold
  refine ⟨fun j hj => (hcol n hm le_rfl).symm ▸ hx j hj, ?_⟩
  rcases suffix_constant_vertical h m hvertical with hn | hs
  · exact hn
  · intro q hq
    exfalso
    let last : Fin n := ⟨n-1, by omega⟩
    have hl : m < last.val := by show m < n-1; omega
    have hi : last.val+1 = n := by show (n-1)+1 = n; omega
    have hstep := congrArg Prod.snd (step w last)
    simp only [hi, hs last hl, dir_south, Prod.snd_add] at hstep
    have htlast := ht last.val (Nat.le_of_lt last.isLt)
    omega

/-- A strict record in one coordinate at step `q` (as opposed to an
increase in width or height). The ordered set of past indices is nonempty. -/
def Record (f : ℕ → ℤ) (q : ℕ) : Prop := ∀ j ≤ q, f j < f (q+1)

def LastIncrease (w : Fin n → Fin 4) (p : Fin n) : Prop :=
  ∀ q : Fin n, p.val < q.val →
    ¬ Record (fun i => (pos w i).1) q.val ∧ ¬ Record (fun i => (pos w i).2) q.val

private theorem attained (f : ℕ → ℤ) (m : ℕ) : ∃ a ≤ m, ∀ j ≤ m, f j ≤ f a := by
  induction m with
  | zero => exact ⟨0, le_rfl, fun j hj => Nat.eq_zero_of_le_zero hj ▸ le_rfl⟩
  | succ m ih =>
    obtain ⟨a, ha, hmax⟩ := ih
    rcases le_total (f (m+1)) (f a) with h | h
    · refine ⟨a, by omega, fun j hj => ?_⟩
      by_cases he : j = m+1
      · simpa [he] using h
      · exact hmax j (by omega)
    · refine ⟨m+1, le_rfl, fun j hj => ?_⟩
      by_cases he : j = m+1
      · simp [he]
      · exact (hmax j (by omega)).trans h

private theorem frozen (f : ℕ → ℤ) {m a n : ℕ}
    (hm : ∀ j ≤ m+1, f j ≤ f a)
    (hno : ∀ q : Fin n, m < q.val → ¬Record f q.val) :
    ∀ j ≤ n, f j ≤ f a := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro hj
    by_cases he : j ≤ m+1
    · exact hm j he
    · let q : Fin n := ⟨j-1, by omega⟩
      have hq : m < q.val := by show m < j-1; omega
      have heq : q.val+1 = j := by show j-1+1 = j; omega
      by_contra! hbad
      refine hno q hq (fun i hi => ?_)
      have hij : i < j := by omega
      rw [heq]
      exact (ih i hij (by omega)).trans_lt hbad

private theorem right_data_of_lastX {w : Fin n → Fin 4} (p : Fin n)
    (hp : Record (fun i => (pos w i).1) p.val) (hlast : LastIncrease w p) :
    Right w p.val ∧ w p = 0 ∧
    (∃ a ≤ p.val, (∀ j ≤ n, (pos w j).1 ≤ (pos w (p.val+1)).1) ∧
      (∀ j ≤ n, (pos w j).2 ≤ (pos w a).2) ∧ (pos w a).1 < (pos w (p.val+1)).1) := by
  have hdx := congrArg Prod.fst (step w p)
  simp only [Prod.fst_add] at hdx
  have hstrict : (pos w p.val).1 < (pos w (p.val+1)).1 := hp p.val le_rfl
  have he : w p = 0 := by
    rcases dir_cases (w p) with he | hn | hw | hs
    · exact he
    · rw [hn, dir_north] at hdx; change _ = _ + 0 at hdx; omega
    · rw [hw, dir_west] at hdx; change _ = _ + (-1) at hdx; omega
    · rw [hs, dir_south] at hdx; change _ = _ + 0 at hdx; omega
  rw [he, dir_east] at hdx
  change (pos w (p.val+1)).1 = (pos w p.val).1 + 1 at hdx
  have hr : Right w p.val := by
    intro j hj
    have hbefore : (pos w j).1 < (pos w (p.val+1)).1 := hp j hj
    omega
  obtain ⟨a, ha, hamax⟩ := attained (fun j => (pos w j).2) p.val
  have hdy : (pos w (p.val+1)).2 = (pos w p.val).2 := by
    simp [step w p, he]
  have hx := frozen (fun j => (pos w j).1) (m := p.val) (a := p.val+1)
    (fun j hj => by
      by_cases heq : j = p.val+1
      · simp [heq]
      · exact (hp j (by omega)).le)
    (fun q hq => (hlast q hq).1)
  have hy := frozen (fun j => (pos w j).2) (m := p.val) (a := a)
    (fun j hj => by
      by_cases heq : j = p.val+1
      · rw [heq, hdy]; exact hamax _ le_rfl
      · exact hamax j (by omega))
    (fun q hq => (hlast q hq).2)
  have hold := hp a ha
  exact ⟨hr, he, a, ha, hx, hy, hold⟩

/-- The direction and form of a top-ending suffix whose last increase was
horizontal. In particular the last-east class contributes only at gap zero. -/
theorem lastEast_suffix {w : Fin n → Fin 4} {d : ℤ} (h : TopGap w d) (p : Fin n)
    (hp : Record (fun i => (pos w i).1) p.val) (hlast : LastIncrease w p) :
    Right w p.val ∧ w p = 0 ∧ d = 0 ∧ (∀ q : Fin n, p.val < q.val → w q = 1) := by
  obtain ⟨hr, he, a, ha, hx, hy, hold⟩ := right_data_of_lastX p hp hlast
  obtain ⟨hrn, htail⟩ := suffix_north_of_top h.1 h.2.1 p.isLt ha hx hy hold
  obtain ⟨b, hb, hd, hmax⟩ := h.2.2
  have hzero : d = 0 := by
    have := hmax n le_rfl
    have := hrn b hb
    omega
  exact ⟨hr, he, hzero, htail⟩

/-- Reflection in the diagonal exchanges E/N and W/S. -/
def reflectDir (d : Fin 4) : Fin 4 :=
  if d = 0 then 1 else if d = 1 then 0 else if d = 2 then 3 else 2

def reflect (w : Fin n → Fin 4) : Fin n → Fin 4 := fun q => reflectDir (w q)

@[simp] private theorem reflectDir_involutive (d : Fin 4) : reflectDir (reflectDir d) = d := by
  fin_cases d <;> decide

private theorem reflectDir_eq (a b : Fin 4) : reflectDir a = b ↔ a = reflectDir b := by
  constructor <;> intro h
  · simpa only [reflectDir_involutive] using congrArg reflectDir h
  · simpa only [reflectDir_involutive] using congrArg reflectDir h

private theorem dir_reflect (d : Fin 4) : dir (reflectDir d) = (dir d).swap := by
  fin_cases d <;> rfl

theorem pos_reflect (w : Fin n → Fin 4) (j : ℕ) (hj : j ≤ n) :
    pos (reflect w) j = (pos w j).swap := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have lt : j < n := hj
    rw [step (reflect w) ⟨j,lt⟩, step w ⟨j,lt⟩, ih (Nat.le_of_lt lt)]
    rw [reflect, dir_reflect]
    rfl

theorem admissible_reflect {w : Fin n → Fin 4} (h : Admissible w) : Admissible (reflect w) := by
  constructor
  · intro q j hj k hk hh
    rw [pos_reflect w j (by have := q.isLt; omega), pos_reflect w q.val q.isLt.le,
      reflect, dir_reflect] at hh
    exact h.1 q j hj k hk (congrArg Prod.swap hh)
  · intro j hj
    rcases h.2 j hj with hr | ht
    · exact Or.inr fun i hi => by rw [pos_reflect w i (hi.trans hj), pos_reflect w j hj]; exact hr i hi
    · exact Or.inl fun i hi => by rw [pos_reflect w i (hi.trans hj), pos_reflect w j hj]; exact ht i hi

/-- A last north record leaves the walk on the new top. The suffix is all east
(including empty), or nonempty and all west. -/
theorem lastNorth_suffix {w : Fin n → Fin 4} (h : Admissible w) (p : Fin n)
    (hp : Record (fun i => (pos w i).2) p.val) (hlast : LastIncrease w p) :
    Top w p.val ∧ w p = 1 ∧ (∀ j, p.val < j → j ≤ n → Top w j) ∧
      ((∀ q : Fin n, p.val < q.val → w q = 0) ∨
        (p.val+1 < n ∧ ∀ q : Fin n, p.val < q.val → w q = 2)) := by
  have recX (q : Fin n) : Record (fun i => (pos (reflect w) i).1) q.val ↔
      Record (fun i => (pos w i).2) q.val := by
    unfold Record
    have hj : q.val+1 ≤ n := q.isLt
    simp only [pos_reflect w _ hj]
    exact forall_congr' fun i => forall_congr' fun hi => by
      rw [pos_reflect w i (hi.trans q.isLt.le)]
      rfl
  have recY (q : Fin n) : Record (fun i => (pos (reflect w) i).2) q.val ↔
      Record (fun i => (pos w i).1) q.val := by
    unfold Record
    have hj : q.val+1 ≤ n := q.isLt
    simp only [pos_reflect w _ hj]
    exact forall_congr' fun i => forall_congr' fun hi => by
      rw [pos_reflect w i (hi.trans q.isLt.le)]
      rfl
  have hlast' : LastIncrease (reflect w) p := by
    intro q hq
    rw [recX, recY]
    exact ⟨(hlast q hq).2, (hlast q hq).1⟩
  obtain ⟨hr, he, a, ha, hx, hy, hold⟩ := right_data_of_lastX p ((recX p).2 hp) hlast'
  have h' := admissible_reflect h
  obtain ⟨hcol, hv⟩ := suffix_on_right h' ha hx hy hold
  refine ⟨?_, (reflectDir_eq _ _).mp he, ?_, ?_⟩
  · intro j hj
    have hh := hr j hj
    rw [pos_reflect w j (hj.trans p.isLt.le), pos_reflect w p.val p.isLt.le] at hh
    exact hh
  · intro j hj hjn i hi
    have hi' := hx i (hi.trans hjn)
    rw [← hcol j hj hjn] at hi'
    rw [pos_reflect w i (hi.trans hjn), pos_reflect w j hjn] at hi'
    exact hi'
  · by_cases he : p.val+1 < n
    · rcases suffix_constant_vertical h' p.val hv with hn | hs
      · exact Or.inl fun q hq => (reflectDir_eq _ _).mp (hn q hq)
      · exact Or.inr ⟨he, fun q hq => (reflectDir_eq _ _).mp (hs q hq)⟩
    · exact Or.inl fun q hq => False.elim (he (lt_of_le_of_lt hq q.isLt))

end WalkDecomposition

end OMA.S_oeis_a191625

/-! Prefix restriction and append for the A191625 walk decomposition. -/

namespace OMA.S_oeis_a191625.WalkDecomposition

variable {m n : ℕ}

/-- Restrict the steps to the first `m` indices, without changing their values. -/
def restrictPrefix (w : Fin n → Fin 4) (hmn : m ≤ n) : Fin m → Fin 4 :=
  fun q => w (Fin.castLE hmn q)

/-- The original position recursion, at an index where a step exists. -/
theorem pos_step_at (w : Fin n → Fin 4) (i : ℕ) (hi : i < n) :
    pos w (i+1) = pos w i + dir (w ⟨i,hi⟩) := by
  simp [pos, hi]

theorem pos_restrictPrefix (w : Fin n → Fin 4) (hmn : m ≤ n) {i : ℕ} (hi : i ≤ m) :
    pos (restrictPrefix w hmn) i = pos w i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have him : i < m := hi
    rw [pos_step_at _ _ him, pos_step_at w i (him.trans_le hmn), ih him.le]
    rfl

theorem admissible_restrictPrefix {w : Fin n → Fin 4} (hw : Admissible w) (hmn : m ≤ n) :
    Admissible (restrictPrefix w hmn) := by
  constructor
  · intro q j hj k hk
    rw [pos_restrictPrefix w hmn (hj.trans q.isLt.le), pos_restrictPrefix w hmn q.isLt.le]
    exact hw.1 (Fin.castLE hmn q) j hj k hk
  · intro i hi
    rcases hw.2 i (hi.trans hmn) with hr | ht
    · exact Or.inl fun j hj => by
        rw [pos_restrictPrefix w hmn (hj.trans hi), pos_restrictPrefix w hmn hi]
        exact hr j hj
    · exact Or.inr fun j hj => by
        rw [pos_restrictPrefix w hmn (hj.trans hi), pos_restrictPrefix w hmn hi]
        exact ht j hj

theorem right_restrictPrefix_iff (w : Fin n → Fin 4) (hmn : m ≤ n) {i : ℕ} (hi : i ≤ m) :
    Right (restrictPrefix w hmn) i ↔ Right w i := by
  unfold Right
  exact forall_congr' fun j => forall_congr' fun hj => by
    rw [pos_restrictPrefix w hmn (hj.trans hi), pos_restrictPrefix w hmn hi]

theorem top_restrictPrefix_iff (w : Fin n → Fin 4) (hmn : m ≤ n) {i : ℕ} (hi : i ≤ m) :
    Top (restrictPrefix w hmn) i ↔ Top w i := by
  unfold Top
  exact forall_congr' fun j => forall_congr' fun hj => by
    rw [pos_restrictPrefix w hmn (hj.trans hi), pos_restrictPrefix w hmn hi]

/-- Append one direction after the existing steps. -/
def appendStep (v : Fin m → Fin 4) (d : Fin 4) : Fin (m+1) → Fin 4 :=
  fun q => if h : q.val < m then v ⟨q.val,h⟩ else d

@[simp] theorem appendStep_before (v : Fin m → Fin 4) (d : Fin 4)
    (q : Fin (m+1)) (hq : q.val < m) : appendStep v d q = v ⟨q.val,hq⟩ := by
  simp [appendStep, hq]

@[simp] theorem appendStep_at (v : Fin m → Fin 4) (d : Fin 4) (hm : m < m+1) :
    appendStep v d ⟨m,hm⟩ = d := by
  simp [appendStep]

@[simp] theorem restrictPrefix_appendStep (v : Fin m → Fin 4) (d : Fin 4) (h : m ≤ m+1) :
    restrictPrefix (appendStep v d) h = v := by
  funext q
  exact appendStep_before v d (Fin.castLE h q) q.isLt

theorem pos_appendStep_prefix (v : Fin m → Fin 4) (d : Fin 4) {i : ℕ} (hi : i ≤ m) :
    pos (appendStep v d) i = pos v i := by
  simpa only [restrictPrefix_appendStep] using
    (pos_restrictPrefix (appendStep v d) (Nat.le_succ m) hi).symm

theorem pos_appendStep_end (v : Fin m → Fin 4) (d : Fin 4) :
    pos (appendStep v d) (m+1) = pos v m + dir d := by
  rw [pos_step_at _ _ (Nat.lt_succ_self m), appendStep_at, pos_appendStep_prefix v d le_rfl]

/-- Append `r` copies of `e` after the existing steps. -/
def appendRun (v : Fin m → Fin 4) (e : Fin 4) (r : ℕ) : Fin (m+r) → Fin 4 :=
  fun q => if h : q.val < m then v ⟨q.val,h⟩ else e

variable {r : ℕ}

@[simp] theorem appendRun_before (v : Fin m → Fin 4) (e : Fin 4)
    (q : Fin (m+r)) (hq : q.val < m) : appendRun v e r q = v ⟨q.val,hq⟩ := by
  simp [appendRun, hq]

@[simp] theorem appendRun_after (v : Fin m → Fin 4) (e : Fin 4)
    (q : Fin (m+r)) (hq : m ≤ q.val) : appendRun v e r q = e := by
  simp [appendRun, not_lt_of_ge hq]

@[simp] theorem restrictPrefix_appendRun (v : Fin m → Fin 4) (e : Fin 4) (r : ℕ)
    (h : m ≤ m+r) : restrictPrefix (appendRun v e r) h = v := by
  funext q
  exact appendRun_before v e (Fin.castLE h q) q.isLt

theorem pos_appendRun_prefix (v : Fin m → Fin 4) (e : Fin 4) (r : ℕ) {i : ℕ} (hi : i ≤ m) :
    pos (appendRun v e r) i = pos v i := by
  simpa only [restrictPrefix_appendRun] using
    (pos_restrictPrefix (appendRun v e r) (Nat.le_add_right m r) hi).symm

/-- Displacement within a constant tail of any word, including at its start. -/
theorem pos_constant_tail (w : Fin n → Fin 4) (e : Fin 4) {s : ℕ}
    (he : ∀ q : Fin n, s ≤ q.val → w q = e) {t : ℕ} (ht : s+t ≤ n) :
    pos w (s+t) = pos w s + t • dir e := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hlt : s+t < n := ht
    rw [← Nat.add_assoc, pos_step_at w (s+t) hlt, he ⟨s+t,hlt⟩ (Nat.le_add_right s t), ih hlt.le,
      succ_nsmul, add_assoc]

theorem pos_appendRun_tail (v : Fin m → Fin 4) (e : Fin 4) {t : ℕ} (ht : t ≤ r) :
    pos (appendRun v e r) (m+t) = pos v m + t • dir e := by
  rw [pos_constant_tail (appendRun v e r) e (appendRun_after v e) (Nat.add_le_add_left ht m),
    pos_appendRun_prefix v e r le_rfl]

/-- A distinguished step at index `m`, followed by a constant run. -/
def appendStepRun (v : Fin m → Fin 4) (d e : Fin 4) (r : ℕ) : Fin (m+1+r) → Fin 4 :=
  appendRun (appendStep v d) e r

@[simp] theorem appendStepRun_before (v : Fin m → Fin 4) (d e : Fin 4)
    (q : Fin (m+1+r)) (hq : q.val < m) : appendStepRun v d e r q = v ⟨q.val,hq⟩ := by
  unfold appendStepRun
  rw [appendRun_before _ _ q (hq.trans (Nat.lt_succ_self m)), appendStep_before _ _ _ hq]

@[simp] theorem appendStepRun_at (v : Fin m → Fin 4) (d e : Fin 4) (hm : m < m+1+r) :
    appendStepRun v d e r ⟨m,hm⟩ = d := by
  unfold appendStepRun
  rw [appendRun_before _ _ _ (Nat.lt_succ_self m), appendStep_at]

@[simp] theorem appendStepRun_after (v : Fin m → Fin 4) (d e : Fin 4)
    (q : Fin (m+1+r)) (hq : m < q.val) : appendStepRun v d e r q = e :=
  appendRun_after (appendStep v d) e q hq

@[simp] theorem restrictPrefix_appendStepRun (v : Fin m → Fin 4) (d e : Fin 4) (r : ℕ)
    (h : m ≤ m+1+r) : restrictPrefix (appendStepRun v d e r) h = v := by
  funext q
  exact appendStepRun_before v d e (Fin.castLE h q) q.isLt

theorem pos_appendStepRun_prefix (v : Fin m → Fin 4) (d e : Fin 4) (r : ℕ) {i : ℕ}
    (hi : i ≤ m) : pos (appendStepRun v d e r) i = pos v i := by
  rw [appendStepRun, pos_appendRun_prefix _ _ _ (hi.trans (Nat.le_succ m)),
    pos_appendStep_prefix v d hi]

theorem pos_appendStepRun_tail (v : Fin m → Fin 4) (d e : Fin 4) {t : ℕ} (ht : t ≤ r) :
    pos (appendStepRun v d e r) (m+1+t) = (pos v m + dir d) + t • dir e := by
  rw [appendStepRun, pos_appendRun_tail _ _ ht, pos_appendStep_end]

/-- If the steps strictly after the split are constant, rebuilding from the
restricted prefix, the split step, and the tail direction gives the original word. -/
theorem appendStepRun_restrictPrefix (w : Fin n → Fin 4) (e : Fin 4) (hn : m+1+r = n)
    (hm : m < n) (htail : ∀ q : Fin n, m < q.val → w q = e) :
    (fun q : Fin n => appendStepRun (restrictPrefix w hm.le) (w ⟨m,hm⟩) e r
      (Fin.cast hn.symm q)) = w := by
  subst n
  funext q
  rcases lt_trichotomy q.val m with hq | hq | hq
  · exact appendStepRun_before _ _ _ q hq
  · have heq : q = ⟨m,hm⟩ := Fin.ext hq
    subst q
    exact appendStepRun_at _ _ _ hm
  · exact (appendStepRun_after _ _ _ q hq).trans (htail q hq).symm

end OMA.S_oeis_a191625.WalkDecomposition

namespace OMA.S_oeis_a191625.WalkDecomposition

variable {n : ℕ}

/-- If either coordinate sets a record, exactly one record index has no later record. -/
theorem existsUnique_lastIncrease {w : Fin n → Fin 4}
    (h : ∃ q : Fin n, Record (fun i => (pos w i).1) q.val ∨
      Record (fun i => (pos w i).2) q.val) :
    ∃! p : Fin n, (Record (fun i => (pos w i).1) p.val ∨
      Record (fun i => (pos w i).2) p.val) ∧ LastIncrease w p := by
  classical
  let P (q : Fin n) := Record (fun i => (pos w i).1) q.val ∨
    Record (fun i => (pos w i).2) q.val
  let s := Finset.univ.filter P
  have hs : s.Nonempty := by
    obtain ⟨q, hq⟩ := h
    exact ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq⟩⟩
  let p := s.max' hs
  have hp : P p := (Finset.mem_filter.mp (s.max'_mem hs)).2
  have hlast : LastIncrease w p := by
    intro q hq
    have hn : ¬ P q := fun hr =>
      (not_le_of_gt (show p < q from hq)) (s.le_max' q (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr⟩))
    exact ⟨fun hx => hn (Or.inl hx), fun hy => hn (Or.inr hy)⟩
  refine ⟨p, ⟨hp, hlast⟩, fun q ⟨hq, hqLast⟩ => le_antisymm ?_ ?_⟩
  · exact s.le_max' q (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq⟩)
  · by_contra! hh
    exact hp.elim (hqLast p (show q.val < p.val from hh)).1
      (hqLast p (show q.val < p.val from hh)).2

private theorem record_pos_step (w : Fin n → Fin 4) (q : Fin n) :
    pos w (q.val + 1) = pos w q.val + dir (w q) := by
  simp [pos, q.isLt]

private theorem le_origin_of_noRecord (f : ℕ → ℤ)
    (h : ∀ q : Fin n, ¬ Record f q.val) : ∀ j ≤ n, f j ≤ f 0 := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro hj
    cases j with
    | zero => exact le_rfl
    | succ i =>
      by_contra! hn
      apply h ⟨i, hj⟩
      intro a ha
      change a ≤ i at ha
      exact (ih a (by omega) (by omega)).trans_lt hn

private theorem pos_of_allWest {w : Fin n → Fin 4} (hw : ∀ q, w q = 2) :
    ∀ j ≤ n, pos w j = (-(j : ℤ), 0) := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro hj
    have hj' : j < n := hj
    rw [record_pos_step w ⟨j, hj'⟩, hw, ih (Nat.le_of_lt hj'), show dir 2 = (-1, 0) from rfl]
    apply Prod.ext
    · simp; omega
    · rfl

private theorem allWest_of_noRecord {w : Fin n → Fin 4}
    (h : Admissible w) (ht : Top w n)
    (hno : ∀ q : Fin n, ¬ Record (fun i => (pos w i).1) q.val ∧
      ¬ Record (fun i => (pos w i).2) q.val) : ∀ q : Fin n, w q = 2 := by
  have hx : ∀ j ≤ n, (pos w j).1 ≤ 0 :=
    le_origin_of_noRecord (fun i => (pos w i).1) (fun q => (hno q).1)
  have hy : ∀ j ≤ n, (pos w j).2 ≤ 0 :=
    le_origin_of_noRecord (fun i => (pos w i).2) (fun q => (hno q).2)
  have hbase : (pos w n).2 = 0 := le_antisymm (hy n le_rfl) (ht 0 (Nat.zero_le n))
  -- A step from below height zero back to height zero would land on the origin.
  have prev (q : Fin n) (hn : (pos w (q.val+1)).2 = 0) : (pos w q.val).2 = 0 := by
    by_contra hne
    have hneg := lt_of_le_of_ne (hy q.val q.isLt.le) hne
    have hs := record_pos_step w q
    have hd : w q = 0 ∨ w q = 1 ∨ w q = 2 ∨ w q = 3 := by
      generalize w q = d
      fin_cases d <;> decide
    rcases hd with hd | hd | hd | hd
    · rw [hd, show dir 0 = (1, 0) from rfl] at hs
      rw [hs, Prod.snd_add, add_zero] at hn
      omega
    · have hr : Right w q.val := (h.2 q.val q.isLt.le).resolve_right
        (fun hh => (not_lt_of_ge (hh 0 (Nat.zero_le _))) hneg)
      have hzero : (pos w q.val).1 = 0 := le_antisymm (hx _ q.isLt.le) (hr 0 (Nat.zero_le _))
      apply h.1 q 0 (Nat.zero_le _) 1 Nat.one_pos
      rw [one_nsmul, ← hs]
      apply Prod.ext
      · simpa [hs, hd, pos, show dir 1 = (0, 1) from rfl] using hzero.symm
      · exact hn.symm
    · rw [hd, show dir 2 = (-1, 0) from rfl] at hs
      rw [hs, Prod.snd_add, add_zero] at hn
      omega
    · rw [hd, show dir 3 = (0, -1) from rfl] at hs
      rw [hs, Prod.snd_add] at hn
      omega
  have allY : ∀ j ≤ n, (pos w j).2 = 0 := by
    have back : ∀ k ≤ n, (pos w (n-k)).2 = 0 := by
      intro k
      induction k with
      | zero => simpa using fun _ : 0 ≤ n => hbase
      | succ k ih =>
        intro hk
        exact prev ⟨n-(k+1), by omega⟩ (by simpa [show n-(k+1)+1 = n-k by omega] using ih (by omega))
    intro j hj
    simpa [show n-(n-j) = j by omega] using back (n-j) (by omega)
  intro q
  have hq := allY q.val q.isLt.le
  have hn := allY (q.val+1) q.isLt
  have hs := record_pos_step w q
  have hd : w q = 0 ∨ w q = 1 ∨ w q = 2 ∨ w q = 3 := by
    generalize w q = d
    fin_cases d <;> decide
  rcases hd with hd | hd | hd | hd
  · exfalso
    have hnx := hx (q.val+1) q.isLt
    rw [hs, hd, show dir 0 = (1, 0) from rfl, Prod.fst_add] at hnx
    let k := (-(pos w q.val).1).toNat
    have hk : 0 < k := by dsimp [k]; omega
    have hkx : (k : ℤ) = -(pos w q.val).1 := by dsimp [k]; omega
    apply h.1 q 0 (Nat.zero_le _) k hk
    rw [hd, show dir 0 = (1, 0) from rfl]
    apply Prod.ext
    · change (0 : ℤ) = (pos w q.val).1 + k • (1 : ℤ)
      rw [nsmul_eq_mul, mul_one, hkx, add_neg_cancel]
    · change (0 : ℤ) = (pos w q.val).2 + k • (0 : ℤ)
      simp [hq]
  · rw [hs, hd, show dir 1 = (0, 1) from rfl, Prod.snd_add] at hn
    omega
  · exact hd
  · rw [hs, hd, show dir 3 = (0, -1) from rfl, Prod.snd_add] at hn
    omega

/-- Among top-gap walks, the no-record class is exactly the all-west word at
horizontal gap `n`, including the empty word at gap zero. -/
theorem topGap_noRecord_iff {w : Fin n → Fin 4} {d : ℤ} :
    (TopGap w d ∧ (∀ q : Fin n, ¬ Record (fun i => (pos w i).1) q.val ∧
      ¬ Record (fun i => (pos w i).2) q.val)) ↔
    (∀ q : Fin n, w q = 2) ∧ d = (n : ℤ) := by
  constructor
  · rintro ⟨⟨hadm, ht, a, ha, hgap, hmax⟩, hno⟩
    have hw := allWest_of_noRecord hadm ht hno
    have hp := pos_of_allWest hw
    have h0 := hmax 0 (Nat.zero_le n)
    rw [hp 0 (Nat.zero_le n), hp a ha] at h0
    rw [hp a ha, hp n le_rfl] at hgap
    exact ⟨hw, by simp at h0 hgap; omega⟩
  · rintro ⟨hw, rfl⟩
    have hp := pos_of_allWest hw
    have ht : ∀ j ≤ n, Top w j := by
      intro j hj a ha
      rw [hp a (ha.trans hj), hp j hj]
    have hray : ∀ (q : Fin n) (j : ℕ), j ≤ q.val → ∀ k : ℕ, 0 < k →
        pos w j ≠ pos w q.val + k • dir (w q) := by
      intro q j hj k hk he
      rw [hp j (hj.trans q.isLt.le), hp q.val q.isLt.le, hw q,
        show dir 2 = (-1, 0) from rfl] at he
      have hx := congrArg Prod.fst he
      change -(j : ℤ) = -(q.val : ℤ) + k • (-1 : ℤ) at hx
      rw [nsmul_eq_mul, mul_neg, mul_one] at hx
      omega
    refine ⟨⟨⟨hray, fun j hj => Or.inr (ht j hj)⟩, ht n le_rfl,
      0, Nat.zero_le n, ?_, ?_⟩, ?_⟩
    · rw [hp 0 (Nat.zero_le n), hp n le_rfl]
      simp
    · intro b hb
      rw [hp b hb, hp 0 (Nat.zero_le n)]
      simp
    · intro q
      constructor <;> intro hr <;> have hn := hr q.val le_rfl <;> dsimp only at hn <;>
        rw [hp q.val q.isLt.le, hp (q.val+1) q.isLt] at hn <;> simp at hn

end OMA.S_oeis_a191625.WalkDecomposition

/-! Last-record constructors for the A191625 walk decomposition. -/

namespace OMA.S_oeis_a191625.WalkDecomposition

variable {m r : ℕ}

private theorem north_dir : dir 1 = (0, 1) := rfl
private theorem east_dir : dir 0 = (1, 0) := rfl
private theorem west_dir : dir 2 = (-1, 0) := rfl

private theorem pos_north_run (v : Fin m → Fin 4) (e : Fin 4) {i : ℕ}
    (hi : m < i) (hin : i ≤ m+1+r) :
    pos (appendStepRun v 1 e r) i = (pos v m + dir 1) + (i-(m+1)) • dir e := by
  have heq : m+1 + (i-(m+1)) = i := by omega
  have htail := pos_appendStepRun_tail v 1 e (r := r) (t := i-(m+1)) (by omega)
  rwa [heq] at htail

/-- A north step opens a fresh row. Either horizontal direction on that row
is admissible, even before imposing a bound on the horizontal displacement. -/
private theorem north_run_fresh {v : Fin m → Fin 4} {e : Fin 4}
    (hv : Admissible v) (ht : Top v m) (he : e = 0 ∨ e = 2) :
    let w := appendStepRun v 1 e r
    Admissible w ∧ (∀ i, m < i → i ≤ m+1+r → (pos w i).2 = (pos v m).2 + 1) ∧
      Record (fun i => (pos w i).2) m := by
  let w := appendStepRun v 1 e r
  have old {i : ℕ} (hi : i ≤ m) : pos w i = pos v i :=
    pos_appendStepRun_prefix v 1 e r hi
  have row (i : ℕ) (hi : m < i) (hin : i ≤ m+1+r) : (pos w i).2 = (pos v m).2 + 1 := by
    change (pos (appendStepRun v 1 e r) i).2 = _
    rw [pos_north_run v e hi hin, north_dir]
    change (pos v m).2 + 1 + (i-(m+1)) • (dir e).2 = _
    rcases he with rfl | rfl
    · simp
    · simp
  refine ⟨⟨?_, ?_⟩, row, ?_⟩
  · intro q j hj k hk
    rcases lt_trichotomy q.val m with hq | hq | hq
    · change pos w j ≠ pos w q.val + k • dir (appendStepRun v 1 e r q)
      rw [old (hj.trans hq.le), old hq.le, appendStepRun_before v 1 e q hq]
      exact hv.1 ⟨q.val,hq⟩ j hj k hk
    · change pos w j ≠ pos w q.val + k • dir (appendStepRun v 1 e r q)
      rw [old (hj.trans hq.le), old hq.le]
      have hdir : appendStepRun v 1 e r q = 1 := by
        have hq' : q = ⟨m, by omega⟩ := Fin.ext hq
        rw [hq', appendStepRun_at]
      rw [hdir, north_dir]
      intro hhit
      have hhitY := congrArg Prod.snd hhit
      change (pos v j).2 = (pos v q.val).2 + k • (1 : ℤ) at hhitY
      rw [hq, nsmul_eq_mul, mul_one] at hhitY
      have hjY := ht j (hj.trans hq.le)
      omega
    · change pos w j ≠ pos w q.val + k • dir (appendStepRun v 1 e r q)
      rw [appendStepRun_after v 1 e q hq]
      intro hhit
      by_cases hjm : j ≤ m
      · have h := congrArg Prod.snd hhit
        change (pos w j).2 = (pos w q.val).2 + k • (dir e).2 at h
        rw [old hjm, row _ hq q.isLt.le] at h
        have hjY := ht j hjm
        rcases he with rfl | rfl
        · simp at h; omega
        · simp at h; omega
      · have h := congrArg Prod.fst hhit
        change (pos (appendStepRun v 1 e r) j).1 =
          (pos (appendStepRun v 1 e r) q.val).1 + k • (dir e).1 at h
        rw [pos_north_run v e (by omega) (hj.trans q.isLt.le),
          pos_north_run v e hq q.isLt.le, north_dir] at h
        change (pos v m).1 + 0 + (j-(m+1)) • (dir e).1 =
          (pos v m).1 + 0 + (q.val-(m+1)) • (dir e).1 + k • (dir e).1 at h
        rcases he with rfl | rfl
        · simp at h; omega
        · simp at h; omega
  · intro i hi
    by_cases him : i ≤ m
    · rcases hv.2 i him with hr | ht'
      · exact Or.inl fun j hj => by rw [old him, old (hj.trans him)]; exact hr j hj
      · exact Or.inr fun j hj => by rw [old him, old (hj.trans him)]; exact ht' j hj
    · refine Or.inr fun j hj => ?_
      change (pos w j).2 ≤ (pos w i).2
      rw [row i (by omega) hi]
      by_cases hjm : j ≤ m
      · rw [old hjm]; have h := ht j hjm; omega
      · rw [row j (by omega) (hj.trans hi)]
  · intro j hj
    change (pos w j).2 < (pos w (m+1)).2
    rw [old hj, row (m+1) (by omega) (by omega)]
    have h := ht j hj
    omega

/-- When the horizontal displacement fits under the old maximum, the old
witness still attains the new maximum. Neither coordinate records again. -/
private theorem lastNorth_constructor_horizontal {v : Fin m → Fin 4} {e : Fin 4} {d : ℤ}
    (hv : TopGap v d) (he : e = 0 ∨ e = 2) (hfit : r • (dir e).1 ≤ d) :
    let w := appendStepRun v 1 e r
    TopGap w (d - r • (dir e).1) ∧ Record (fun i => (pos w i).2) m ∧
      LastIncrease w ⟨m, by omega⟩ := by
  obtain ⟨hadm, ht, a, ha, hgap, hmax⟩ := hv
  obtain ⟨hadm', row, hrec⟩ := north_run_fresh (r := r) hadm ht he
  let w := appendStepRun v 1 e r
  change Admissible w at hadm'
  have old {i : ℕ} (hi : i ≤ m) : pos w i = pos v i :=
    pos_appendStepRun_prefix v 1 e r hi
  have column (i : ℕ) (hi : m < i) (hin : i ≤ m+1+r) :
      (pos w i).1 = (pos v m).1 + (i-(m+1)) • (dir e).1 := by
    change (pos (appendStepRun v 1 e r) i).1 = _
    rw [pos_north_run v e hi hin, north_dir]
    change (pos v m).1 + 0 + (i-(m+1)) • (dir e).1 = _
    rw [add_zero]
  have hfinal : (pos w (m+1+r)).1 = (pos v m).1 + r • (dir e).1 := by
    rw [column _ (by omega) le_rfl, Nat.add_sub_cancel_left]
  have hmax' (i : ℕ) (hi : i ≤ m+1+r) : (pos w i).1 ≤ (pos w a).1 := by
    rw [old ha]
    by_cases him : i ≤ m
    · rw [old him]; exact hmax i him
    · rw [column i (by omega) hi]
      rcases he with rfl | rfl
      · simp at hfit ⊢
        omega
      · simp
        have hbound := hmax m le_rfl
        omega
  have htop' : Top w (m+1+r) := by
    intro j hj
    rw [row _ (by omega) le_rfl]
    by_cases hjm : j ≤ m
    · rw [old hjm]; have h := ht j hjm; omega
    · rw [row j (by omega) hj]
  refine ⟨⟨hadm', htop', a, by omega, ?_, hmax'⟩, hrec, ?_⟩
  · rw [old ha, hfinal]
    omega
  · intro q hq
    have hmq : m < q.val := hq
    have hqnext : q.val+1 ≤ m+1+r := q.isLt
    constructor
    · intro hrecord
      exact (not_lt_of_ge (hmax' _ hqnext)) (hrecord a (by omega))
    · intro hrecord
      have hh := hrecord q.val le_rfl
      change (pos w q.val).2 < (pos w (q.val+1)).2 at hh
      rw [row _ hmq q.isLt.le, row _ (by omega) hqnext] at hh
      exact (lt_irrefl _) hh

/-- `v ++ N ++ W^r` increases its horizontal gap by `r`.
For the disjoint west tag take `0 < r`; the geometric conclusion also holds at `r = 0`. -/
theorem lastNorth_constructor_west {v : Fin m → Fin 4} {d : ℤ} (hv : TopGap v d) :
    let w := appendStepRun v 1 2 r
    TopGap w (d + (r : ℤ)) ∧ Record (fun i => (pos w i).2) m ∧
      LastIncrease w ⟨m, by omega⟩ := by
  have hd : 0 ≤ d := by
    obtain ⟨a, _, hgap, hmax⟩ := hv.2.2
    have := hmax m le_rfl
    omega
  have hfit : r • (dir 2).1 ≤ d := by
    simp
    omega
  simpa [west_dir, nsmul_eq_mul, sub_neg_eq_add] using
    (lastNorth_constructor_horizontal hv (Or.inr rfl) hfit)

/-- `v ++ N ++ E^r` decreases its horizontal gap by `r` when it stays within
its old maximum x-coordinate. This includes the empty run. -/
theorem lastNorth_constructor_east {v : Fin m → Fin 4} {d : ℤ}
    (hv : TopGap v d) (hr : (r : ℤ) ≤ d) :
    let w := appendStepRun v 1 0 r
    TopGap w (d - (r : ℤ)) ∧ Record (fun i => (pos w i).2) m ∧
      LastIncrease w ⟨m, by omega⟩ := by
  have hfit : r • (dir 0).1 ≤ d := by simpa [east_dir] using hr
  simpa [east_dir] using (lastNorth_constructor_horizontal hv (Or.inl rfl) hfit)

/-- The right-edge analogue of `TopGap`: the gap is vertical. -/
def RightGap {n : ℕ} (v : Fin n → Fin 4) (d : ℤ) : Prop :=
  Admissible v ∧ Right v n ∧
    (∃ a ≤ n, (pos v a).2 - (pos v n).2 = d ∧
      ∀ j ≤ n, (pos v j).2 ≤ (pos v a).2)

theorem reflect_involutive {n : ℕ} (v : Fin n → Fin 4) : reflect (reflect v) = v := by
  funext q
  change reflectDir (reflectDir (v q)) = v q
  generalize v q = d
  fin_cases d <;> rfl

theorem reflect_appendStepRun (v : Fin m → Fin 4) (d e : Fin 4) :
    reflect (appendStepRun v d e r) = appendStepRun (reflect v) (reflectDir d) (reflectDir e) r := by
  funext q
  change reflectDir (appendStepRun v d e r q) = _
  rcases lt_trichotomy q.val m with hq | hq | hq
  · rw [appendStepRun_before _ _ _ q hq, appendStepRun_before _ _ _ q hq]; rfl
  · have hq' : q = ⟨m, by omega⟩ := Fin.ext hq
    rw [hq', appendStepRun_at, appendStepRun_at]
  · rw [appendStepRun_after _ _ _ q hq, appendStepRun_after _ _ _ q hq]

theorem topGap_reflect_iff_rightGap {n : ℕ} (v : Fin n → Fin 4) (d : ℤ) :
    TopGap (reflect v) d ↔ RightGap v d := by
  constructor
  · rintro ⟨hadm, ht, a, ha, hd, hmax⟩
    refine ⟨reflect_involutive v ▸ admissible_reflect hadm, ?_, a, ha, ?_, ?_⟩
    · intro j hj
      have h := ht j hj
      rwa [pos_reflect v j hj, pos_reflect v n le_rfl] at h
    · rwa [pos_reflect v a ha, pos_reflect v n le_rfl] at hd
    · intro j hj
      have h := hmax j hj
      rwa [pos_reflect v j hj, pos_reflect v a ha] at h
  · rintro ⟨hadm, hr, a, ha, hd, hmax⟩
    refine ⟨admissible_reflect hadm, ?_, a, ha, ?_, ?_⟩
    · intro j hj
      rw [pos_reflect v j hj, pos_reflect v n le_rfl]
      exact hr j hj
    · rw [pos_reflect v a ha, pos_reflect v n le_rfl]
      exact hd
    · intro j hj
      rw [pos_reflect v j hj, pos_reflect v a ha]
      exact hmax j hj

/-- Reflection of a gap-zero top walk is again gap-zero and top-ending:
a zero top gap means the endpoint lies on both edges. -/
private theorem topGap_zero_reflect {n : ℕ} {w : Fin n → Fin 4} (h : TopGap w 0) :
    TopGap (reflect w) 0 := by
  have hc := (valid_iff_topGap_zero w).mpr h
  apply (topGap_reflect_iff_rightGap w 0).mpr
  exact ⟨h.1, fun j hj => (hc.2.2 j hj).1,
    n, le_rfl, sub_self _, fun j hj => (hc.2.2 j hj).2⟩

/-- `v ++ E ++ N^r` with right gap exactly `r` ends at a corner. The east
step is a strict x-record, and neither coordinate records afterward. -/
theorem lastEast_constructor {v : Fin m → Fin 4} (hv : RightGap v (r : ℤ)) :
    let w := appendStepRun v 0 1 r
    TopGap w 0 ∧ Record (fun i => (pos w i).1) m ∧ LastIncrease w ⟨m, by omega⟩ := by
  let w := appendStepRun v 0 1 r
  have h := lastNorth_constructor_east ((topGap_reflect_iff_rightGap _ _).mpr hv) le_rfl
  have hword : reflect (appendStepRun (reflect v) 1 0 r) = w := by
    rw [reflect_appendStepRun, reflect_involutive]
    rfl
  obtain ⟨hgap, hrecord, hlast⟩ := h
  rw [sub_self] at hgap
  have hcorner := topGap_zero_reflect hgap
  rw [hword] at hcorner
  have hy (i : ℕ) (hi : i ≤ m+1+r) :
      (pos (appendStepRun (reflect v) 1 0 r) i).2 = (pos w i).1 := by
    rw [← hword, pos_reflect _ i hi]
    rfl
  have hx (i : ℕ) (hi : i ≤ m+1+r) :
      (pos (appendStepRun (reflect v) 1 0 r) i).1 = (pos w i).2 := by
    rw [← hword, pos_reflect _ i hi]
    rfl
  refine ⟨hcorner, ?_, ?_⟩
  · intro j hj
    have h := hrecord j hj
    simpa only [hy j (by omega), hy (m+1) (by omega)] using h
  · intro q hq
    have h := hlast q hq
    have transferY : Record (fun i => (pos (appendStepRun (reflect v) 1 0 r) i).2) q.val ↔
        Record (fun i => (pos w i).1) q.val := by
      unfold Record
      exact forall_congr' fun j => forall_congr' fun hj => by
        simp only [hy j (hj.trans q.isLt.le), hy _ q.isLt]
    have transferX : Record (fun i => (pos (appendStepRun (reflect v) 1 0 r) i).1) q.val ↔
        Record (fun i => (pos w i).2) q.val := by
      unfold Record
      exact forall_congr' fun j => forall_congr' fun hj => by
        simp only [hx j (hj.trans q.isLt.le), hx _ q.isLt]
    exact ⟨fun hr => h.2 (transferY.mpr hr), fun hr => h.1 (transferX.mpr hr)⟩

end OMA.S_oeis_a191625.WalkDecomposition

namespace OMA.S_oeis_a191625.WalkDecomposition

variable {n m d : ℕ}

abbrev GapWalk (n d : ℕ) := { w : Fin n → Fin 4 // TopGap w (d : ℤ) }

private theorem topGap_nonneg {w : Fin n → Fin 4} {g : ℤ} (h : TopGap w g) : 0 ≤ g := by
  obtain ⟨a, _, hgap, hmax⟩ := h.2.2
  have := hmax n le_rfl
  omega

/-- If no new record occurs from the split onward, the final maximum is attained
in the old prefix. -/
private theorem attained_before {f : ℕ → ℤ} (_hm : m ≤ n)
    (h : ∀ i, m ≤ i → i < n → ¬ Record f i) :
    ∃ a ≤ m, ∀ j ≤ n, f j ≤ f a := by
  have hp : ∀ k, ∃ a ≤ k, ∀ j ≤ k, f j ≤ f a := by
    intro k
    induction k with
    | zero => exact ⟨0, le_rfl, fun j hj => by simp [Nat.eq_zero_of_le_zero hj]⟩
    | succ k ih =>
      obtain ⟨a, ha, hmax⟩ := ih
      by_cases hnew : f (k+1) ≤ f a
      · exact ⟨a, by omega, fun j hj => by
          rcases Nat.eq_or_lt_of_le hj with rfl | hj
          · exact hnew
          · exact hmax _ (by omega)⟩
      · exact ⟨k+1, le_rfl, fun j hj => by
          rcases Nat.eq_or_lt_of_le hj with rfl | hj
          · exact le_rfl
          · exact (hmax _ (by omega)).trans (le_of_lt (lt_of_not_ge hnew))⟩
  obtain ⟨a, ha, hmax⟩ := hp m
  refine ⟨a, ha, ?_⟩
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro hj
    by_cases hjm : j ≤ m
    · exact hmax _ hjm
    · obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
      by_contra! hbad
      apply h i (by omega) (by omega)
      intro b hb
      exact (ih b (by omega) (by omega)).trans_lt hbad

private abbrev Pre (p : Fin n) := (p.rev : ℕ)

private theorem split_length (p : Fin n) : p.val + 1 + Pre p = n := by
  have hp := p.isLt
  simp only [Pre, Fin.val_rev]
  omega

private theorem pos_of_tail {w : Fin n → Fin 4} (p : Fin n) {b e : Fin 4}
    (hb : w p = b) (he : ∀ q : Fin n, p.val < q.val → w q = e) :
    pos w n = (pos w p.val + dir b) + Pre p • dir e := by
  have hn := split_length p
  have h := pos_constant_tail w e (s := p.val+1) (t := Pre p)
    (fun q hq => he q (by omega)) hn.le
  rw [hn, pos_step_at w _ p.isLt, hb] at h
  exact h

private theorem recover_east {w : Fin n → Fin 4} {g : ℤ} (hw : TopGap w g) (p : Fin n)
    (hl : LastIncrease w p) (hr : Right w p.val) (hp : w p = 0)
    (he : ∀ q : Fin n, p.val < q.val → w q = 1) :
    RightGap (restrictPrefix w p.isLt.le) (Pre p : ℤ) := by
  have hc : ∀ i, p.val ≤ i → i < n → ¬ Record (fun j => (pos w j).2) i := by
    intro i hmi hi
    rcases Nat.eq_or_lt_of_le hmi with rfl | hmi
    · intro h
      have hlt : (pos w p.val).2 < (pos w (p.val+1)).2 := h p.val le_rfl
      rw [pos_step_at w _ p.isLt, hp] at hlt
      simp at hlt
    · exact (hl ⟨i,hi⟩ hmi).2
  obtain ⟨a, ha, hmax⟩ := attained_before p.isLt.le hc
  have hfinal := congrArg Prod.snd (pos_of_tail p hp he)
  change (pos w n).2 = (pos w p.val).2 + 0 + Pre p • (1 : ℤ) at hfinal
  simp only [add_zero, nsmul_eq_mul, mul_one] at hfinal
  have h1 := hw.2.1 a (ha.trans p.isLt.le)
  have h2 := hmax n le_rfl
  refine ⟨admissible_restrictPrefix hw.1 _, (right_restrictPrefix_iff w _ le_rfl).mpr hr,
    a, ha, ?_, ?_⟩
  · rw [pos_restrictPrefix w _ ha, pos_restrictPrefix w _ le_rfl]
    omega
  · intro j hj
    rw [pos_restrictPrefix w _ hj, pos_restrictPrefix w _ ha]
    exact hmax j (hj.trans p.isLt.le)

private theorem recover_north {w : Fin n → Fin 4} {g : ℤ} (hw : TopGap w g) (p : Fin n)
    (hl : LastIncrease w p) (ht : Top w p.val) (hp : w p = 1) {e : Fin 4}
    (he : ∀ q : Fin n, p.val < q.val → w q = e) :
    TopGap (restrictPrefix w p.isLt.le) (g + (Pre p : ℤ) * (dir e).1) := by
  have hc : ∀ i, p.val ≤ i → i < n → ¬ Record (fun j => (pos w j).1) i := by
    intro i hmi hi
    rcases Nat.eq_or_lt_of_le hmi with rfl | hmi
    · intro h
      have hlt : (pos w p.val).1 < (pos w (p.val+1)).1 := h p.val le_rfl
      rw [pos_step_at w _ p.isLt, hp] at hlt
      simp at hlt
    · exact (hl ⟨i,hi⟩ hmi).1
  obtain ⟨a, ha, hmax⟩ := attained_before p.isLt.le hc
  obtain ⟨b, hb, hgap, hbmax⟩ := hw.2.2
  have hab := le_antisymm (hbmax a (ha.trans p.isLt.le)) (hmax b hb)
  have hfinal := congrArg Prod.fst (pos_of_tail p hp he)
  change (pos w n).1 = (pos w p.val).1 + 0 + Pre p • (dir e).1 at hfinal
  simp only [add_zero, nsmul_eq_mul] at hfinal
  refine ⟨admissible_restrictPrefix hw.1 _, (top_restrictPrefix_iff w _ le_rfl).mpr ht,
    a, ha, ?_, ?_⟩
  · rw [pos_restrictPrefix w _ ha, pos_restrictPrefix w _ le_rfl]
    omega
  · intro j hj
    rw [pos_restrictPrefix w _ hj, pos_restrictPrefix w _ ha]
    exact hmax j (hj.trans p.isLt.le)

private def castWalk {a b : ℕ} (h : a = b) (w : Fin a → Fin 4) : Fin b → Fin 4 :=
  fun q => w (Fin.cast h.symm q)

private def HasLast (w : Fin n → Fin 4) (p : Fin n) : Prop :=
  (Record (fun i => (pos w i).1) p.val ∨ Record (fun i => (pos w i).2) p.val) ∧
    LastIncrease w p

private theorem cast_run_cert {r : ℕ} (h : m+1+r = n) (v : Fin m → Fin 4)
    (b e : Fin 4) (g : ℤ)
    (hc : TopGap (appendStepRun v b e r) g ∧
      HasLast (appendStepRun v b e r) ⟨m, by omega⟩) :
    TopGap (castWalk h (appendStepRun v b e r)) g ∧
      HasLast (castWalk h (appendStepRun v b e r)) ⟨m, by omega⟩ := by
  subst n
  exact hc

private def place (p : Fin n) (v : Fin p.val → Fin 4) (b e : Fin 4) : Fin n → Fin 4 :=
  castWalk (split_length p) (appendStepRun v b e (Pre p))

private theorem place_restrict (p : Fin n) (v : Fin p.val → Fin 4) (b e : Fin 4) :
    restrictPrefix (place p v b e) p.isLt.le = v := by
  funext q
  exact appendStepRun_before _ _ _ _ q.isLt

private theorem place_at (p : Fin n) (v : Fin p.val → Fin 4) (b e : Fin 4) :
    place p v b e p = b := by
  exact appendStepRun_at _ _ _ _

private theorem place_after (p : Fin n) (v : Fin p.val → Fin 4) (b e : Fin 4) (q : Fin n)
    (hq : p.val < q.val) : place p v b e q = e := by
  exact appendStepRun_after _ _ _ _ hq

private theorem place_recover (w : Fin n → Fin 4) (p : Fin n) {b e : Fin 4}
    (hb : w p = b) (he : ∀ q : Fin n, p.val < q.val → w q = e) :
    place p (restrictPrefix w p.isLt.le) b e = w := by
  rw [← hb]
  exact appendStepRun_restrictPrefix w e (split_length p) p.isLt he

/-- Distinguish the two north-record pieces even though the record step is the same.
The west suffix is nonempty; an empty suffix belongs to `northEast`. -/
inductive RunKind
  | east | northWest | northEast
  deriving DecidableEq

instance : Fintype RunKind :=
  ⟨{.east, .northWest, .northEast}, by intro t; cases t <;> simp⟩

private def RunKind.guard (t : RunKind) (d k : ℕ) : Prop :=
  match t with
  | .east => d = 0
  | .northWest => 1 ≤ k ∧ k ≤ d
  | .northEast => True

private def RunKind.gap (t : RunKind) (d k : ℕ) : ℕ :=
  match t with
  | .east => k
  | .northWest => d - k
  | .northEast => d + k

private def RunKind.start : RunKind → Fin 4
  | .east => 0
  | _ => 1

private def RunKind.tail : RunKind → Fin 4
  | .east => 1
  | .northWest => 2
  | .northEast => 0

private def RunKind.prefixWord (t : RunKind) (w : Fin m → Fin 4) : Fin m → Fin 4 :=
  match t with
  | .east => reflect w
  | _ => w

private theorem prefixWord_inj (t : RunKind) :
    Function.Injective (t.prefixWord : (Fin m → Fin 4) → Fin m → Fin 4) := by
  cases t
  · intro u v h
    change reflect u = reflect v at h
    simpa only [reflect_involutive] using congrArg reflect h
  all_goals exact fun _ _ h => h

abbrev Guarded (P : Prop) (α : Type) := Subtype (fun _ : α => P)

/-- The singleton no-record piece followed by the three last-record pieces.
`k` indexes the length of the tail and `k.rev` is the position of the record. -/
abbrev WalkPieces (n d : ℕ) :=
  Guarded (d = n) Unit ⊕ (Σ t : RunKind, Σ k : Fin n,
    Guarded (t.guard d k.val) (GapWalk (Pre k) (t.gap d k.val)))

private def runWord (t : RunKind) (k : Fin n) (v : Fin (Pre k) → Fin 4) : Fin n → Fin 4 :=
  place k.rev (t.prefixWord v) t.start t.tail

private theorem run_cert (t : RunKind) (k : Fin n) (v : GapWalk (Pre k) (t.gap d k.val))
    (hg : t.guard d k.val) : TopGap (runWord t k v.val) (d : ℤ) ∧
      HasLast (runWord t k v.val) k.rev := by
  unfold runWord place
  apply cast_run_cert
  cases t with
  | east =>
    have hd : d = 0 := hg
    have hv : RightGap (reflect v.val) (Pre k.rev : ℤ) := by
      apply (topGap_reflect_iff_rightGap (reflect v.val) _).mp
      rw [reflect_involutive]
      simpa only [Pre, Fin.rev_rev, RunKind.gap] using v.property
    obtain ⟨hgap, hrecord, hlast⟩ := lastEast_constructor hv
    exact ⟨hd.symm ▸ hgap, Or.inl hrecord, hlast⟩
  | northWest =>
    have hk : k.val ≤ d := hg.2
    obtain ⟨hgap, hrecord, hlast⟩ := lastNorth_constructor_west (r := Pre k.rev) v.property
    have hg' : ((d - k.val : ℕ) : ℤ) + (Pre k.rev : ℤ) = d := by
      simp only [Pre, Fin.rev_rev, Int.ofNat_sub hk]
      omega
    change TopGap _ (((d - k.val : ℕ) : ℤ) + (Pre k.rev : ℤ)) at hgap
    rw [hg'] at hgap
    exact ⟨hgap, Or.inr hrecord, hlast⟩
  | northEast =>
    have hk : (Pre k.rev : ℤ) ≤ ((d + k.val : ℕ) : ℤ) := by
      simp only [Pre, Fin.rev_rev, Nat.cast_add]
      omega
    obtain ⟨hgap, hrecord, hlast⟩ := lastNorth_constructor_east (r := Pre k.rev) v.property hk
    have hg' : ((d + k.val : ℕ) : ℤ) - (Pre k.rev : ℤ) = d := by
      simp [Pre]
    change TopGap _ (((d + k.val : ℕ) : ℤ) - (Pre k.rev : ℤ)) at hgap
    rw [hg'] at hgap
    exact ⟨hgap, Or.inr hrecord, hlast⟩

private abbrev westWord (n : ℕ) : Fin n → Fin 4 := fun _ => 2

private theorem noRec_westWord (h : d = n) :
    TopGap (westWord n) (d : ℤ) ∧ ¬ ∃ p, HasLast (westWord n) p := by
  obtain ⟨hw, hno⟩ := topGap_noRecord_iff.mpr
    (show (∀ q, westWord n q = 2) ∧ (d : ℤ) = n from ⟨fun _ => rfl, by exact_mod_cast h⟩)
  refine ⟨hw, ?_⟩
  rintro ⟨p, hp, _⟩
  exact hp.elim (hno p).1 (hno p).2

/-- Assemble the four pieces using the checked record constructors. -/
def buildWalk : WalkPieces n d → GapWalk n d
  | .inl a => ⟨westWord n, (noRec_westWord a.property).1⟩
  | .inr ⟨t, k, v⟩ => ⟨runWord t k v.val.val, (run_cert t k v.val v.property).1⟩

private theorem same_last {w : Fin n → Fin 4} {p q : Fin n}
    (hp : HasLast w p) (hq : HasLast w q) : p = q := by
  obtain ⟨a, _, ha⟩ := existsUnique_lastIncrease (show ∃ j, _ from ⟨p, hp.1⟩)
  exact (ha p hp).trans (ha q hq).symm

private theorem same_kind (t u : RunKind) (k : Fin n)
    {v w : Fin (Pre k) → Fin 4} (heq : runWord t k v = runWord u k w)
    (ht : t.guard d k.val) (hu : u.guard d k.val) : t = u := by
  have hs : t.start = u.start := by
    have h := congrFun heq k.rev
    unfold runWord at h
    rwa [place_at, place_at] at h
  have htail (hk : 1 ≤ k.val) : t.tail = u.tail := by
    have hp : (k.rev).val + 1 < n := by
      have h := split_length k.rev
      simp only [Pre, Fin.rev_rev] at h
      omega
    let q : Fin n := ⟨(k.rev).val + 1, hp⟩
    have h := congrFun heq q
    unfold runWord at h
    have hq : k.rev.val < q.val := Nat.lt_succ_self _
    rwa [place_after _ _ _ _ _ hq, place_after _ _ _ _ _ hq] at h
  cases t <;> cases u <;> first
  | rfl
  | exact False.elim ((by decide : (0 : Fin 4) ≠ 1) hs)
  | exact False.elim ((by decide : (1 : Fin 4) ≠ 0) hs)
  | exact False.elim ((by decide : (2 : Fin 4) ≠ 0) (htail ht.1))
  | exact False.elim ((by decide : (0 : Fin 4) ≠ 2) (htail hu.1))

theorem buildWalk_injective (n d : ℕ) : Function.Injective (@buildWalk n d) := by
  rintro (a | ⟨t, k, v⟩) (b | ⟨u, j, w⟩) h
  · exact congrArg Sum.inl (Subsingleton.elim a b)
  · have h' : westWord n = runWord u j w.val.val := congrArg Subtype.val h
    exact ((noRec_westWord a.property).2 ⟨j.rev, h'.symm ▸ (run_cert u j w.val w.property).2⟩).elim
  · have h' : runWord t k v.val.val = westWord n := congrArg Subtype.val h
    exact ((noRec_westWord b.property).2 ⟨k.rev, h' ▸ (run_cert t k v.val v.property).2⟩).elim
  · have h' : runWord t k v.val.val = runWord u j w.val.val := congrArg Subtype.val h
    have hj : k.rev = j.rev := same_last ((run_cert t k v.val v.property).2)
      (h'.symm ▸ (run_cert u j w.val w.property).2)
    have hkj : k = j := by simpa only [Fin.rev_rev] using congrArg Fin.rev hj
    subst j
    have htu := same_kind t u k h' v.property w.property
    subst u
    have hvw : t.prefixWord v.val.val = t.prefixWord w.val.val := by
      have h := congrArg (fun x => restrictPrefix x k.rev.isLt.le) h'
      simpa only [runWord, place_restrict] using h
    have heq : v = w := Subtype.ext (Subtype.ext (prefixWord_inj t hvw))
    subst w
    rfl

theorem buildWalk_surjective (n d : ℕ) : Function.Surjective (@buildWalk n d) := by
  classical
  rintro ⟨w, hw⟩
  by_cases h : ∃ q : Fin n, Record (fun i => (pos w i).1) q.val ∨ Record (fun i => (pos w i).2) q.val
  · obtain ⟨p, ⟨hr, hl⟩, _⟩ := existsUnique_lastIncrease h
    obtain ⟨k, rfl⟩ : ∃ k : Fin n, k.rev = p := ⟨p.rev, Fin.rev_rev p⟩
    let v := restrictPrefix w k.rev.isLt.le
    rcases hr with hr | hr
    · obtain ⟨hedge, hb, hd, he⟩ := lastEast_suffix hw k.rev hr hl
      have hd' : d = 0 := by exact_mod_cast hd
      have hv := (topGap_reflect_iff_rightGap v _).mpr (recover_east hw k.rev hl hedge hb he)
      have hv' : TopGap (reflect v) (k.val : ℤ) := by simpa only [Pre, Fin.rev_rev] using hv
      refine ⟨.inr ⟨.east, k, ⟨⟨reflect v, hv'⟩, hd'⟩⟩, Subtype.ext ?_⟩
      change place k.rev (reflect (reflect v)) 0 1 = w
      rw [reflect_involutive]
      exact place_recover w k.rev hb he
    · obtain ⟨hedge, hb, _, he | ⟨hne, he⟩⟩ := lastNorth_suffix hw.1 k.rev hr hl
      · have hv := recover_north hw k.rev hl hedge hb he
        have hv' : TopGap v ((d + k.val : ℕ) : ℤ) := by
          change TopGap v ((d : ℤ) + (Pre k.rev : ℤ) * 1) at hv
          simpa only [Pre, Fin.rev_rev, mul_one, Nat.cast_add] using hv
        exact ⟨.inr ⟨.northEast, k, ⟨⟨v, hv'⟩, trivial⟩⟩,
          Subtype.ext (place_recover w k.rev hb he)⟩
      · have len := split_length k.rev
        simp only [Pre, Fin.rev_rev] at len
        have hk : 1 ≤ k.val := by omega
        have hv := recover_north hw k.rev hl hedge hb he
        change TopGap v ((d : ℤ) + (Pre k.rev : ℤ) * (-1)) at hv
        have hv' : TopGap v ((d : ℤ) - k.val) := by
          simpa only [Pre, Fin.rev_rev, mul_neg_one, ← sub_eq_add_neg] using hv
        have hnonneg := topGap_nonneg hv'
        have hkd : k.val ≤ d := by omega
        rw [← Int.ofNat_sub hkd] at hv'
        exact ⟨.inr ⟨.northWest, k, ⟨⟨v, hv'⟩, hk, hkd⟩⟩,
          Subtype.ext (place_recover w k.rev hb he)⟩
  · have hno : ∀ q : Fin n, ¬ Record (fun i => (pos w i).1) q.val ∧
        ¬ Record (fun i => (pos w i).2) q.val := fun q =>
      ⟨fun hx => h ⟨q, Or.inl hx⟩, fun hy => h ⟨q, Or.inr hy⟩⟩
    obtain ⟨hwest, hd⟩ := topGap_noRecord_iff.mp ⟨hw, hno⟩
    have hd' : d = n := by exact_mod_cast hd
    exact ⟨.inl ⟨(), hd'⟩, Subtype.ext (funext fun q => (hwest q).symm)⟩

/-- The all-length disjoint finite equivalence, in the constructor direction. -/
noncomputable def walkPiecesEquiv (n d : ℕ) : WalkPieces n d ≃ GapWalk n d :=
  Equiv.ofBijective buildWalk ⟨buildWalk_injective n d, buildWalk_surjective n d⟩

private theorem x_drop (w : Fin n → Fin 4) {a b : ℕ} (hab : a ≤ b) (hbn : b ≤ n) :
    (pos w a).1 - (pos w b).1 ≤ ((b : ℤ) - a) := by
  induction b with
  | zero =>
    have ha : a = 0 := by omega
    simp [ha]
  | succ b ih =>
    by_cases ha : a = b + 1
    · simp [ha]
    · have hb : b < n := by omega
      have hprev := ih (by omega) hb.le
      rw [pos_step_at w _ hb]
      generalize w ⟨b, hb⟩ = q
      fin_cases q <;> simp <;> omega

/-- No walks have gaps outside the integer triangle. -/
theorem C_eq_zero_outside (n : ℕ) (g : ℤ) (h : g < 0 ∨ (n : ℤ) < g) : C n g = 0 := by
  classical
  unfold C
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro w hw
  have ht := (Finset.mem_filter.mp hw).2
  have hnonneg := topGap_nonneg ht
  obtain ⟨a, ha, hgap, _⟩ := ht.2.2
  have hle := x_drop w ha le_rfl
  omega

/-- The existing walk count with a natural-valued gap index. -/
noncomputable def CN (n d : ℕ) : ℕ := C n (d : ℤ)

theorem CN_supported (n d : ℕ) (h : n < d) : CN n d = 0 :=
  C_eq_zero_outside n d (Or.inr (by exact_mod_cast h))

theorem count_eq_CN_zero (n : ℕ) : count n = (CN n 0 : ℤ) := count_eq_C_zero n

open Finset

open scoped Classical

private theorem card_gapWalk (n d : ℕ) : Nat.card (GapWalk n d) = CN n d := by
  have h := Fintype.card_subtype (fun w : Fin n → Fin 4 => TopGap w (d : ℤ))
  rwa [← Nat.card_eq_fintype_card] at h

private theorem card_guarded (P : Prop) (α : Type) [Fintype α] :
    Nat.card (Guarded P α) = if P then Nat.card α else 0 := by
  simp only [Nat.card_eq_fintype_card]
  rw [Fintype.card_subtype]
  by_cases h : P <;> simp [h]

private theorem RunKind.sum_nat (f : RunKind → ℕ) :
    ∑ t, f t = f .east + f .northWest + f .northEast := by
  have h : (univ : Finset RunKind) = {.east, .northWest, .northEast} := rfl
  rw [h]
  simp [add_comm, add_left_comm]

/-- The all-length count recurrence for the actual walk count. The west guard
prevents a negative integer prefix gap from being counted as natural gap zero. -/
theorem CN_recurrence (n d : ℕ) :
    CN n d = (if d = n then 1 else 0)
      + (if d = 0 then ∑ k ∈ range n, CN (n - 1 - k) k else 0)
      + (∑ k ∈ range n, if 1 ≤ k ∧ k ≤ d then CN (n - 1 - k) (d - k) else 0)
      + ∑ k ∈ range n, CN (n - 1 - k) (d + k) := by
  rw [← card_gapWalk n d, ← Nat.card_congr (walkPiecesEquiv n d)]
  simp only [WalkPieces, Nat.card_sum, Nat.card_sigma, card_guarded,
    card_gapWalk, Nat.card_unique (α := Unit), RunKind.sum_nat, RunKind.guard, RunKind.gap, if_true,
    Pre, Fin.val_rev]
  rw [Fin.sum_univ_eq_sum_range (fun k => if d = 0 then CN (n - (k + 1)) k else 0),
    Fin.sum_univ_eq_sum_range (fun k => if 1 ≤ k ∧ k ≤ d then CN (n - (k + 1)) (d - k) else 0),
    Fin.sum_univ_eq_sum_range (fun k => CN (n - (k + 1)) (d + k))]
  by_cases hd : d = 0 <;> simp [hd, Nat.sub_sub, Nat.add_comm 1, add_assoc]

end OMA.S_oeis_a191625.WalkDecomposition

namespace A191625FiniteRows

open Finset
open PowerSeries (coeff)

abbrev S := PowerSeries ℚ
noncomputable abbrev t : S := PowerSeries.X

/-- The two explicit inputs about walk counts. No count is defined by the recurrence. -/
def Supported (C : ℕ → ℕ → ℕ) : Prop := ∀ n d, n < d → C n d = 0

def Decomp (C : ℕ → ℕ → ℕ) : Prop := ∀ n d, d ≤ n →
  C n d = (if d = n then 1 else 0)
    + (if d = 0 then ∑ k ∈ range n, C (n - 1 - k) k else 0)
    + (∑ k ∈ range n, if 1 ≤ k ∧ k ≤ d then C (n - 1 - k) (d - k) else 0)
    + ∑ k ∈ range n, C (n - 1 - k) (d + k)

noncomputable def entry (C : ℕ → ℕ → ℕ) (n d : ℕ) : S :=
  PowerSeries.C (C n d : ℚ)

noncomputable def row (C : ℕ → ℕ → ℕ) (s : S) (n : ℕ) : S :=
  ∑ d ∈ range (n + 1), entry C n d * s ^ d

noncomputable def part (C : ℕ → ℕ → ℕ) (s : S) (N : ℕ) : S :=
  ∑ n ∈ range (N + 1), t ^ n * row C s n

noncomputable def T (C : ℕ → ℕ → ℕ) (s : S) : S :=
  PowerSeries.mk fun N => coeff N (part C s N)

/-- Agreement of coefficients through degree `N`, inclusive. -/
def Agree (N : ℕ) (p q : S) : Prop := ∀ j ≤ N, coeff j p = coeff j q

namespace Agree

variable {N : ℕ} {p q r u v : S}

theorem refl (p : S) : Agree N p p := fun _ _ => rfl

theorem symm (h : Agree N p q) : Agree N q p := fun j hj => (h j hj).symm

theorem trans (h₁ : Agree N p q) (h₂ : Agree N q r) : Agree N p r :=
  fun j hj => (h₁ j hj).trans (h₂ j hj)

theorem add (h₁ : Agree N p q) (h₂ : Agree N u v) : Agree N (p + u) (q + v) := by
  intro j hj
  simp only [map_add, h₁ j hj, h₂ j hj]

theorem sub (h₁ : Agree N p q) (h₂ : Agree N u v) : Agree N (p - u) (q - v) := by
  intro j hj
  simp only [map_sub, h₁ j hj, h₂ j hj]

theorem mul (h₁ : Agree N p q) (h₂ : Agree N u v) : Agree N (p * u) (q * v) := by
  intro j hj
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  apply sum_congr rfl
  rintro ⟨a, b⟩ hab
  have hab' := mem_antidiagonal.mp hab
  change coeff a p * coeff b u = coeff a q * coeff b v
  rw [h₁ a (by omega), h₂ b (by omega)]

theorem mul_left (r : S) (h : Agree N p q) : Agree N (r * p) (r * q) :=
  (refl r).mul h

theorem sum {ι : Type*} {I : Finset ι} {f g : ι → S}
    (h : ∀ i ∈ I, Agree N (f i) (g i)) : Agree N (∑ i ∈ I, f i) (∑ i ∈ I, g i) := by
  intro j hj
  simp only [map_sum]
  exact sum_congr rfl fun i hi => h i hi j hj

theorem vanish_pow (a : S) {n : ℕ} (hn : N < n) : Agree N (t ^ n * a) 0 := by
  intro j hj
  rw [PowerSeries.coeff_X_pow_mul', if_neg (by omega), map_zero]

end Agree

/-- Enlarge a finite cutoff when every term in the added tail has degree above `N`. -/
theorem agree_sum_range_mono {N a b : ℕ} (hab : a ≤ b) (f : ℕ → S)
    (h : ∀ i, a ≤ i → i < b → Agree N (f i) 0) :
    Agree N (∑ i ∈ range a, f i) (∑ i ∈ range b, f i) := by
  intro j hj
  simp only [map_sum]
  apply sum_subset (range_mono hab)
  intro i hi hni
  simpa only [map_zero] using h i (by simpa using hni) (mem_range.mp hi) j hj

theorem agree_T_part (C : ℕ → ℕ → ℕ) (s : S) (N : ℕ) : Agree N (T C s) (part C s N) := by
  intro j hj
  rw [T, PowerSeries.coeff_mk]
  exact agree_sum_range_mono (Nat.succ_le_succ hj) _
    (fun n hn _ => Agree.vanish_pow (row C s n) (by omega)) j le_rfl

end A191625FiniteRows

namespace A191625FiniteRows
open Finset

theorem east_gap_reindex {R : Type*} [CommSemiring R]
    (a : ℕ → R) (s : R) (m k n : ℕ)
    (ha : ∀ g, m < g → a g = 0) (hn : m + k + 1 = n) :
    (∑ d ∈ range (n+1), a (d+k) * s^d) =
      ∑ g ∈ range (m+1), if k ≤ g then a g * s^(g-k) else 0 := by
  apply sum_bij_ne_zero (fun d _ _ => d+k)
  · intro d hd hz
    simp only [mem_range]
    by_contra hh
    have hzero := ha (d+k) (by omega)
    simp [hzero] at hz
  · intro d hd hz e he hez h
    omega
  · intro g hg hz
    have hkg : k ≤ g := by
      by_contra hh
      simp [hh] at hz
    refine ⟨g-k, ?_, ?_, by omega⟩
    · simp only [mem_range] at hg ⊢
      omega
    · simpa [Nat.sub_add_cancel hkg, hkg] using hz
  · intro d hd hz
    simp

theorem west_gap_reindex {R : Type*} [CommSemiring R]
    (a : ℕ → R) (s : R) (m k n : ℕ)
    (ha : ∀ g, m < g → a g = 0) (hn : m + k + 1 = n) :
    (∑ d ∈ range (n+1), if k ≤ d then a (d-k) * s^d else 0) =
      s^k * (∑ g ∈ range (m+1), a g * s^g) := by
  rw [mul_sum]
  apply sum_bij_ne_zero (fun d _ _ => d-k)
  · intro d hd hz
    have hkd : k ≤ d := by
      by_contra hh
      simp [hh] at hz
    simp only [mem_range]
    by_contra hh
    have hzero := ha (d-k) (by omega)
    simp [hzero] at hz
  · intro d hd hz e he hez h
    have hkd : k ≤ d := by
      by_contra hh
      simp [hh] at hz
    have hke : k ≤ e := by
      by_contra hh
      simp [hh] at hez
    omega
  · intro g hg hz
    refine ⟨g+k, ?_, ?_, by omega⟩
    · simp only [mem_range] at hg ⊢
      omega
    · simpa [pow_add, mul_comm, mul_left_comm, mul_assoc] using hz
  · intro d hd hz
    have hkd : k ≤ d := by
      by_contra hh
      simp [hh] at hz
    rw [if_pos hkd, ← Nat.sub_add_cancel hkd, pow_add]
    simp [mul_comm, mul_left_comm]

end A191625FiniteRows

open Finset
namespace A191625FiniteRows

theorem length_reindex {R : Type*} [AddCommMonoid R] (N : ℕ) (f : ℕ → ℕ → R) :
    (∑ n ∈ range (N+1), ∑ k ∈ range n, f (n-1-k) k) =
      ∑ m ∈ range (N+1), ∑ k ∈ range (N-m), f m k := by
  have shift : (∑ n ∈ range (N+1), ∑ k ∈ range n, f (n-1-k) k) =
      ∑ n ∈ range N, ∑ k ∈ range (n+1), f (n-k) k := by
    rw [sum_range_succ']
    simp
  rw [shift, sum_range_succ]
  simp only [Nat.sub_self, range_zero, sum_empty, add_zero]
  rw [← sum_range_diag_flip]
  apply sum_congr rfl
  intro n hn
  calc
    (∑ k ∈ range (n+1), f (n-k) k) =
        ∑ k ∈ range (n+1), f (n-k) (n-(n-k)) := by
      apply sum_congr rfl
      intro k hk
      have hk' := mem_range.mp hk
      congr 1; omega
    _ = ∑ k ∈ range (n+1), f k (n-k) := by
      simpa using sum_range_reflect (fun k => f k (n-k)) (n+1)

end A191625FiniteRows

namespace A191625FiniteRows
open Finset

noncomputable def cornerTerm (C : ℕ → ℕ → ℕ) (m k : ℕ) : S := entry C m k
noncomputable def westTerm (C : ℕ → ℕ → ℕ) (s : S) (m k : ℕ) : S :=
  if 1 ≤ k then s ^ k * row C s m else 0
noncomputable def eastTerm (C : ℕ → ℕ → ℕ) (s : S) (m k : ℕ) : S :=
  ∑ g ∈ range (m + 1), if k ≤ g then entry C m g * s ^ (g-k) else 0

theorem entry_decomp (C : ℕ → ℕ → ℕ) (hD : Decomp C) (n d : ℕ) (hd : d ≤ n) :
    entry C n d = (if d = n then 1 else 0)
      + (if d = 0 then ∑ k ∈ range n, entry C (n-1-k) k else 0)
      + (∑ k ∈ range n, if 1 ≤ k ∧ k ≤ d then entry C (n-1-k) (d-k) else 0)
      + ∑ k ∈ range n, entry C (n-1-k) (d+k) := by
  have h := congrArg (fun x : ℕ => (PowerSeries.C (x : ℚ) : S)) (hD n d hd)
  simpa only [entry, Nat.cast_add, Nat.cast_sum, map_add, map_sum,
    apply_ite, Nat.cast_one, Nat.cast_zero, map_one, map_zero] using h

theorem row_decomp_raw (C : ℕ → ℕ → ℕ) (hD : Decomp C) (s : S) (n : ℕ) :
    row C s n = s^n
      + (∑ k ∈ range n, cornerTerm C (n-1-k) k)
      + (∑ k ∈ range n, ∑ d ∈ range (n+1),
          (if 1 ≤ k ∧ k ≤ d then entry C (n-1-k) (d-k) else 0) * s^d)
      + ∑ k ∈ range n, ∑ d ∈ range (n+1), entry C (n-1-k) (d+k) * s^d := by
  unfold row
  have he : ∀ d ∈ range (n+1), entry C n d * s^d =
      ((if d = n then 1 else 0)
      + (if d = 0 then ∑ k ∈ range n, entry C (n-1-k) k else 0)
      + (∑ k ∈ range n, if 1 ≤ k ∧ k ≤ d then entry C (n-1-k) (d-k) else 0)
      + ∑ k ∈ range n, entry C (n-1-k) (d+k)) * s^d := by
    intro d hd
    rw [entry_decomp C hD n d (by have := mem_range.mp hd; omega)]
  rw [sum_congr rfl he]
  simp_rw [add_mul, sum_add_distrib]
  congr 1
  · congr 1
    · congr 1
      · simp
      · simp [cornerTerm]
    · simp_rw [sum_mul]
      exact sum_comm
  · simp_rw [sum_mul]
    exact sum_comm

theorem row_of_decomp (C : ℕ → ℕ → ℕ) (hS : Supported C) (hD : Decomp C)
    (s : S) (n : ℕ) :
    row C s n = s^n + (∑ k ∈ range n, cornerTerm C (n-1-k) k)
      + (∑ k ∈ range n, westTerm C s (n-1-k) k)
      + ∑ k ∈ range n, eastTerm C s (n-1-k) k := by
  rw [row_decomp_raw C hD s n]
  have hs (m g : ℕ) (hg : m < g) : entry C m g = 0 := by
    simp [entry, hS m g hg]
  congr 1
  · congr 1
    apply sum_congr rfl
    intro k hk
    have hkn : k < n := mem_range.mp hk
    by_cases hk1 : 1 ≤ k
    · simp only [westTerm, hk1, true_and]
      simp_rw [ite_mul, zero_mul]
      exact west_gap_reindex (entry C (n-1-k)) s (n-1-k) k n
        (hs (n-1-k)) (by omega)
    · simp [westTerm, hk1]
  · apply sum_congr rfl
    intro k hk
    exact east_gap_reindex (entry C (n-1-k)) s (n-1-k) k n
      (hs (n-1-k)) (by have := mem_range.mp hk; omega)

end A191625FiniteRows

namespace A191625FiniteRows
open Finset

/-- Rectangular sum indexed by prefix length and run length. Terms above the
    desired total length vanish through degree `N`. -/
noncomputable def pairs (N : ℕ) (f : ℕ → ℕ → S) : S :=
  ∑ m ∈ range (N + 1), ∑ k ∈ range (N + 1), t ^ (m + 1 + k) * f m k

theorem geometric_agree (N : ℕ) (s : S) :
    Agree N ((1 - t * s) * ∑ n ∈ range (N + 1), (t * s) ^ n) 1 := by
  rw [mul_neg_geom_sum]
  exact (Agree.refl 1).sub (by simpa only [mul_pow] using
    (Agree.vanish_pow (N := N) (s ^ (N + 1)) (n := N + 1) (by omega))) |>.trans (by simp [Agree.refl])

theorem corner_agree (C : ℕ → ℕ → ℕ) (hS : Supported C) (N : ℕ) :
    Agree N (pairs N (entry C)) (t * part C t N) := by
  unfold pairs part row
  simp only [mul_sum]
  apply Agree.sum
  intro m hm
  have hmr : m + 1 ≤ N + 1 := Nat.succ_le_succ (Nat.le_of_lt_succ (mem_range.mp hm))
  refine (agree_sum_range_mono hmr (fun k => t ^ (m + 1 + k) * entry C m k)
    (fun k hk _ => ?_)).symm.trans ?_
  · simp only [entry, hS m k (by omega), Nat.cast_zero, map_zero, mul_zero]
    exact Agree.refl 0
  · apply Agree.sum
    intro k _
    rw [pow_add, pow_succ t m]
    ring_nf
    exact Agree.refl _

theorem west_agree (C : ℕ → ℕ → ℕ) (s : S) (N : ℕ) :
    Agree N ((1 - t * s) * pairs N (fun m k => if 1 ≤ k then s ^ k * row C s m else 0))
      (t ^ 2 * s * part C s N) := by
  let x := t * s
  have hsum : ∀ m, (∑ k ∈ range (N + 1), t ^ (m + 1 + k) *
      (if 1 ≤ k then s ^ k * row C s m else 0)) =
      (t ^ m * row C s m) * t * ((∑ k ∈ range (N + 1), x ^ k) - 1) := by
    intro m
    have hone : (∑ k ∈ range (N + 1), if k = 0 then (1 : S) else 0) = 1 := by simp
    rw [← hone, ← sum_sub_distrib, mul_sum]
    apply sum_congr rfl
    intro k _
    rcases k with _ | k
    · simp
    · simp [x, pow_add, mul_pow]
      ring
  have hexact :
    (1 - t * s) * pairs N (fun m k => if 1 ≤ k then s ^ k * row C s m else 0) =
      x * (t * part C s N) - x ^ (N + 1) * (t * part C s N) := by
    calc
      _ = ((1 - x) * ((∑ k ∈ range (N + 1), x ^ k) - 1)) * (t * part C s N) := by
        simp only [pairs, hsum, part, ← sum_mul]
        ring
      _ = (x - x ^ (N + 1)) * (t * part C s N) := by
        congr 1
        rw [mul_sub, mul_neg_geom_sum]
        ring
      _ = _ := sub_mul ..
  rw [hexact]
  have htail : Agree N (x ^ (N + 1) * (t * part C s N)) 0 := by
    rw [show x = t * s from rfl, mul_pow, mul_assoc]
    exact Agree.vanish_pow _ (by omega)
  have h := (Agree.refl (x * (t * part C s N))).sub htail
  simpa only [sub_zero, show x * (t * part C s N) = t ^ 2 * s * part C s N by
    dsimp only [x]; ring] using h

/-- The divided difference is used only as a finite polynomial identity. -/
theorem east_agree (C : ℕ → ℕ → ℕ) (s : S) (N : ℕ) :
    Agree N ((s - t) * pairs N (fun m k => ∑ g ∈ range (m + 1),
      if k ≤ g then entry C m g * s ^ (g-k) else 0))
      (t * (s * part C s N - t * part C t N)) := by
  suffices heq : (s - t) * pairs N (fun m k => ∑ g ∈ range (m + 1),
      if k ≤ g then entry C m g * s ^ (g-k) else 0) =
      t * (s * part C s N - t * part C t N) by
    rw [heq]
    exact Agree.refl _
  unfold pairs part row
  simp only [mul_sub, mul_sum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro m hm
  rw [sum_comm]
  apply sum_congr rfl
  intro g hg
  have hgn : g + 1 ≤ N + 1 := by
    simp only [mem_range] at hm hg
    omega
  calc
    _ = ∑ k ∈ range (g + 1), (s - t) *
          (t ^ (m + 1 + k) * (entry C m g * s ^ (g-k))) := by
      symm
      rw [← sum_subset (range_mono hgn) (f := fun k => (s - t) *
        (t ^ (m + 1 + k) * (if k ≤ g then entry C m g * s ^ (g-k) else 0)))]
      · apply sum_congr rfl
        intro k hk
        rw [if_pos (Nat.le_of_lt_succ (mem_range.mp hk))]
      · intro k _ hk
        simp only [mem_range] at hk
        simp [show ¬k ≤ g by omega]
    _ = (t ^ (m + 1) * entry C m g) *
          ((∑ k ∈ range (g + 1), t ^ k * s ^ (g-k)) * (s - t)) := by
      simp only [sum_mul, mul_sum]
      apply sum_congr rfl
      intro k _
      rw [pow_add]
      ring
    _ = _ := by
      rw [show (∑ k ∈ range (g + 1), t ^ k * s ^ (g-k)) * (s - t) =
          s ^ (g + 1) - t ^ (g + 1) from by
        rw [← neg_sub t s, mul_neg]
        rw [show (∑ k ∈ range (g + 1), t ^ k * s ^ (g-k)) * (t - s) =
          t ^ (g + 1) - s ^ (g + 1) from by
            simpa only [Nat.add_sub_cancel] using geom_sum₂_mul t s (g + 1), neg_sub]]
      rw [pow_succ s g, pow_succ t g, pow_succ t m]
      ring

end A191625FiniteRows

namespace A191625FiniteRows
open Finset
open PowerSeries (coeff)

theorem coeff_T_zero (C : ℕ → ℕ → ℕ) (N : ℕ) :
    coeff N (T C 0) = (C N 0 : ℚ) := by
  rw [agree_T_part C 0 N N le_rfl]
  have hr (m : ℕ) : row C 0 m = entry C m 0 := by
    simp [row, zero_pow_eq]
  simp_rw [part, map_sum, hr, PowerSeries.coeff_X_pow_mul']
  simp only [entry, PowerSeries.coeff_C]
  have hh : ∀ x ∈ range (N+1),
      (if x ≤ N then if N-x = 0 then (C x 0 : ℚ) else 0 else 0) =
      if x = N then (C N 0 : ℚ) else 0 := by
    intro x hx
    have := mem_range.mp hx
    split_ifs
    all_goals simp_all
    all_goals omega
  rw [sum_congr rfl hh]
  simp

theorem coeff_T_X (C : ℕ → ℕ → ℕ) (hS : Supported C) (N : ℕ) :
    coeff N (T C t) = ∑ m ∈ range (N+1), (C m (N-m) : ℚ) := by
  rw [agree_T_part C t N N le_rfl]
  simp only [part, map_sum]
  apply sum_congr rfl
  intro m hm
  rw [PowerSeries.coeff_X_pow_mul', if_pos (by have := mem_range.mp hm; omega)]
  simp only [row, map_sum, entry]
  simp_rw [mul_comm (PowerSeries.C _), PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_C]
  have hh : ∀ x ∈ range (m+1),
      (if x ≤ N-m then if N-m-x = 0 then (C m x : ℚ) else 0 else 0) =
      if x = N-m then (C m (N-m) : ℚ) else 0 := by
    intro x hx
    split_ifs
    all_goals simp_all
    all_goals omega
  rw [sum_congr rfl hh]
  by_cases h : N-m < m+1
  · simp [h]
  · have hz := hS m (N-m) (by omega)
    simp [hz]
end A191625FiniteRows

namespace A191625FiniteRows
open Finset
open PowerSeries (coeff)

private noncomputable def byLength (N : ℕ) (f : ℕ → ℕ → S) : S :=
  ∑ n ∈ range (N + 1), t ^ n * ∑ k ∈ range n, f (n - 1 - k) k

private theorem agree_byLength_pairs (N : ℕ) (f : ℕ → ℕ → S) :
    Agree N (byLength N f) (pairs N f) := by
  have he : byLength N f =
      ∑ n ∈ range (N + 1), ∑ k ∈ range n, t ^ ((n - 1 - k) + 1 + k) * f (n - 1 - k) k := by
    simp only [byLength, mul_sum]
    apply sum_congr rfl
    intro n _
    apply sum_congr rfl
    intro k hk
    rw [show (n - 1 - k) + 1 + k = n by have := mem_range.mp hk; omega]
  rw [he, length_reindex N (fun m k => t ^ (m + 1 + k) * f m k)]
  unfold pairs
  apply Agree.sum
  intro m _
  apply agree_sum_range_mono (by omega)
  intro k hk _
  exact Agree.vanish_pow _ (by omega)

private theorem part_decomp (C : ℕ → ℕ → ℕ) (hS : Supported C) (hD : Decomp C)
    (s : S) (N : ℕ) :
    part C s N = (∑ n ∈ range (N + 1), (t * s) ^ n) + byLength N (cornerTerm C)
      + byLength N (westTerm C s) + byLength N (eastTerm C s) := by
  simp only [part, byLength, row_of_decomp C hS hD, mul_add, sum_add_distrib, mul_pow]

noncomputable def K (s : S) : S := (1 - t * s) * (s - t) - t * s * (1 - t^2)

/-- The denominator-cleared kernel identity, valid even at `s = t`. -/
theorem kernel_of_decomp (C : ℕ → ℕ → ℕ) (hS : Supported C) (hD : Decomp C) (s : S) :
    K s * T C s = s - t + t * (1 - t * s) * (s - 2 * t) * T C t := by
  ext N
  have hp := agree_T_part C s N
  have hpt := agree_T_part C t N
  have hH := geometric_agree N s
  have hJ := (agree_byLength_pairs N (cornerTerm C)).trans (corner_agree C hS N)
  have hW := ((agree_byLength_pairs N (westTerm C s)).mul_left (1 - t * s)).trans
    (west_agree C s N)
  have hE := ((agree_byLength_pairs N (eastTerm C s)).mul_left (s - t)).trans
    (east_agree C s N)
  have hL : Agree N (K s * T C s) (K s * part C s N) := hp.mul_left _
  have hR : Agree N (s - t + t * (1 - t * s) * (s - 2 * t) * T C t)
      (s - t + t * (1 - t * s) * (s - 2 * t) * part C t N) :=
    (Agree.refl _).add (hpt.mul_left _)
  have h : Agree N
      ((s - t) * ((1 - t * s) * (∑ n ∈ range (N + 1), (t * s) ^ n)
        + (1 - t * s) * byLength N (cornerTerm C)
        + (1 - t * s) * byLength N (westTerm C s))
        + (1 - t * s) * ((s - t) * byLength N (eastTerm C s))
        - t * s * (1 - t^2) * part C s N)
      ((s - t) * (1 + (1 - t * s) * (t * part C t N) + t^2 * s * part C s N)
        + (1 - t * s) * (t * (s * part C s N - t * part C t N))
        - t * s * (1 - t^2) * part C s N) :=
    (((hH.add (hJ.mul_left _)).add hW).mul_left _ |>.add (hE.mul_left _)).sub (Agree.refl _)
  have hmid : Agree N (K s * part C s N)
      (s - t + t * (1 - t * s) * (s - 2 * t) * part C t N) := by
    convert h using 1
    · unfold K
      rw [part_decomp C hS hD s N]
      ring
    · ring
  exact (hL.trans (hmid.trans hR.symm)) N le_rfl


end A191625FiniteRows

namespace A191625Kernel
open PowerSeries Finset
noncomputable section

private abbrev S := PowerSeries ℚ
private abbrev t : S := X
private def b : S := 1 - t - t^2

-- The successor coefficient of U = t*(1 + U*(U+b)) needs only earlier ones.
private def u : ℕ → ℚ
  | 0 => 0
  | n+1 => coeff n (1 : S) + ∑ p ∈ antidiagonal n,
      if _h : p.1 ≤ n ∧ p.2 ≤ n then u p.1 * (u p.2 + coeff p.2 b) else 0
termination_by n => n
decreasing_by all_goals omega

private def U : S := mk u

private theorem fixed_point : U = t * (1 + U * (U + b)) := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp only [U, coeff_mk, u, coeff_zero_X_mul, t]
  | succ n =>
    rw [coeff_succ_X_mul, map_add, coeff_mul]
    simp only [U, coeff_mk, map_add]
    rw [u]
    congr 1
    apply Finset.sum_congr rfl
    intro p hp
    have h := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    rw [dif_pos (show p.1 ≤ n ∧ p.2 ≤ n by omega)]

theorem exists_small_root : ∃ V : PowerSeries ℚ, constantCoeff V = 0 ∧
    X * V^2 - (1 - X + X^2 + X^3) * V + X = 0 := by
  refine ⟨U, ?_, ?_⟩
  · rw [← coeff_zero_eq_constantCoeff, U, coeff_mk, u]
  · have h := fixed_point
    unfold b at h
    change t * U^2 - (1-t+t^2+t^3)*U+t=0
    linear_combination -h

end
end A191625Kernel

namespace A191625Elim
open PowerSeries
noncomputable section
abbrev S := PowerSeries ℚ
abbrev t : S := X

def K (s : S) := (1-t*s)*(s-t)-t*s*(1-t^2)

def KernelEquation (T : S → S) : Prop :=
  ∀ s, K s * T s = s-t + t*(1-t*s)*(s-2*t)*T t

/-- Select the normalized radical and give the denominator-cleared corner series.
Only the kernel equation is assumed; the zero-constant root is constructed in SmallRoot. -/
theorem radical_of_kernel (T : S → S) (h : KernelEquation T) :
    ∃ z : S, constantCoeff z = 1 ∧ z^2 = (1-t^4)*(1-2*t-t^2) ∧
      t*(1-2*t-2*t^2+2*t^3)*T 0 = t^4-2*t^3+3*t-1+(1-t)*z := by
  obtain ⟨u, hu0, hq⟩ := A191625Kernel.exists_small_root
  change t*u^2-(1-t+t^2+t^3)*u+t = 0 at hq
  have ht : t ≠ 0 := X_ne_zero
  have hF : T 0 = 1 + 2*t*T t := by
    apply mul_left_cancel₀ ht
    have h0 := h 0
    unfold K at h0
    linear_combination -h0
  have hKu : K u = 0 := by unfold K; linear_combination -hq
  have hu := h u
  rw [hKu, zero_mul] at hu
  let L := (1-t*u)*(u-2*t)
  have hL : L*(T 0-1) = 2*(t-u) := by
    rw [hF]; dsimp [L]; linear_combination -2*hu
  have hnL : L ≠ 0 := by
    have hfac : L = t*((1+t-t^2)*u-1) := by dsimp [L]; linear_combination -hq
    rw [hfac]
    apply mul_ne_zero ht
    intro he
    have hc := congrArg (constantCoeff (R := ℚ)) he
    simp [hu0] at hc
  let z := 1-t+t^2+t^3-2*t*u
  refine ⟨z, ?_, ?_, ?_⟩
  · simp [z, t]
  · dsimp [z]; linear_combination 4*t*hq
  · let D := t*(1-2*t-2*t^2+2*t^3)
    let Y := t^4-2*t^3+3*t-1+(1-t)*z
    change D*T 0 = Y
    have cert : L*(Y-D) = 2*D*(t-u) := by
      dsimp [L,Y,D,z]; linear_combination 2*t*(2*t^2-t*u-2*t+u-1)*hq
    apply mul_left_cancel₀ hnL
    linear_combination D*hL - cert

end
end A191625Elim

namespace A191625Downstream

noncomputable section
open PowerSeries

abbrev S := PowerSeries ℚ
abbrev t : S := PowerSeries.X

def A : S := 1 - 4*t + t^2 + 8*t^3 - 3*t^4 + 2*t^5 - t^6 - 8*t^7 + 2*t^8 + 2*t^9
def B : S := 1 - 4*t - 3*t^2 + 18*t^3 - 3*t^4 - 6*t^5 + 7*t^6 + 2*t^8
def R : S := 1 - 7*t^2 + 6*t^3 + 5*t^4 - 14*t^5 - 5*t^6 + 2*t^8

/-- The ten coefficients, in descending sequence-index order. -/
def recurrence {K : Type*} [CommRing K] (a : ℕ → K) (n : ℕ) : Prop :=
  ((n : K) + 1) * a n - 4*(n : K) * a (n-1) + ((n : K)-5) * a (n-2)
    + (8*(n : K)-6) * a (n-3) + (9-3*(n : K)) * a (n-4)
    + (2*(n : K)-16) * a (n-5) + (13-(n : K)) * a (n-6)
    + (56-8*(n : K)) * a (n-7) + (2*(n : K)-14) * a (n-8)
    + (2*(n : K)-18) * a (n-9) = 0

private def theta (F : S) := t * derivative ℚ F

private lemma coeff_theta (n : ℕ) (F : S) : coeff n (theta F) = n * coeff n F := by
  cases n with
  | zero => simp [theta, t]
  | succ m => simp [theta, t, coeff_succ_X_mul, coeff_derivative, mul_comm]

private lemma coeff_nat_mul (n c : ℕ) (G : S) :
    coeff n ((c : S) * G) = c * coeff n G := by
  simp only [← nsmul_eq_mul, map_nsmul]

private lemma coeff_num_mul (n c : ℕ) [c.AtLeastTwo] (G : S) :
    coeff n (ofNat(c) * G) = ofNat(c) * coeff n G := by
  simpa only [Nat.cast_ofNat] using coeff_nat_mul n (ofNat(c) : ℕ) G

private lemma coeff_t_mul (n : ℕ) (G : S) (h : 1 ≤ n) :
    coeff n (t * G) = coeff (n-1) G := by
  simpa [h] using (coeff_X_pow_mul' G 1 n)

/-- Coefficient extraction at every `n ≥ 9`, not just at finitely many test indices. -/
theorem rational_recurrence (F : S) (h : A * (t * derivative ℚ F) + B * F = R)
    (n : ℕ) (hn : 9 ≤ n) : recurrence (fun i => coeff i F) n := by
  change A * theta F + B * F = R at h
  have e := congrArg (coeff n) h
  simp (disch := omega) only [A, B, R, add_mul, sub_mul, one_mul, mul_assoc,
    map_add, map_sub, coeff_num_mul, coeff_X_pow_mul', coeff_t_mul, if_pos,
    coeff_X_pow, coeff_one, if_neg, coeff_theta, Nat.cast_sub] at e
  unfold recurrence
  linear_combination e

/-- Integer transport needs only pointwise equality after casting to `ℚ`. -/
theorem integer_recurrence (F : S) (a : ℕ → ℤ) (ha : ∀ i, coeff i F = (a i : ℚ))
    (h : A * (t * derivative ℚ F) + B * F = R) (n : ℕ) (hn : 9 ≤ n) :
    recurrence a n := by
  have e := rational_recurrence F h n hn
  unfold recurrence at e ⊢
  simp only [ha] at e
  exact_mod_cast e

end
end A191625Downstream

namespace A191625Downstream
noncomputable section
open PowerSeries

/-- The two denominator-cleared radical identities imply the differential equation.
No inverse of the denominator or choice of square-root branch is needed. -/
theorem differential_of_radical (F z : S) (hz : z^2 = (1-t^4)*(1-2*t-t^2))
    (hF : t*(1-2*t-2*t^2+2*t^3)*F = t^4-2*t^3+3*t-1+(1-t)*z) :
    A * (t * derivative ℚ F) + B * F = R := by
  have hz' := congrArg (derivative ℚ) hz
  have hF' := congrArg (derivative ℚ) hF
  have dt : derivative ℚ t = 1 := derivative_X
  have d2 : derivative ℚ (2 : S) = 0 := (derivative ℚ).map_natCast 2
  have d3 : derivative ℚ (3 : S) = 0 := (derivative ℚ).map_natCast 3
  simp only [derivative_pow, Derivation.leibniz, smul_eq_mul, map_sub, map_add,
    derivative_one, d2, d3, dt] at hz' hF'
  let Δ := (1-t^4)*(1-2*t-t^2)
  have hrad : 2*Δ*derivative ℚ z = (-2-2*t-4*t^3+10*t^4+6*t^5)*z := by
    change 2*((1-t^4)*(1-2*t-t^2))*_ = _
    rw [← hz]
    linear_combination z*hz'
  dsimp [Δ] at hrad
  unfold A B R
  have two_ne : (2 : S) ≠ 0 := by
    intro e
    have h := congrArg (constantCoeff (R := ℚ)) e
    rw [show (2:S) = 1+1 by ring, map_add, map_one, map_zero] at h
    norm_num at h
  apply mul_left_cancel₀ two_ne
  linear_combination 2*((1-t^4)*(1-2*t-t^2))*hF' +
    2*(2-2*t^2-8*t^4-4*t^5)*hF + (1-t)*hrad

end
end A191625Downstream

namespace A191625Downstream
open PowerSeries
open A191625Elim (KernelEquation radical_of_kernel)
noncomputable section

/-- All the algebra between the kernel and the differential equation, with no walk premises. -/
theorem differential_of_kernel (T : S → S) (hk : KernelEquation T) :
    A * (t * derivative ℚ (T 0)) + B * T 0 = R := by
  obtain ⟨z, _, hz, hF⟩ := radical_of_kernel T hk
  exact differential_of_radical (T 0) z hz hF

/-- Rational coefficients of the corner specialization; no integrality assumption. -/
theorem recurrence_of_kernel (T : S → S) (hk : KernelEquation T) (n : ℕ) (hn : 9 ≤ n) :
    recurrence (fun i => coeff i (T 0)) n :=
  rational_recurrence (T 0) (differential_of_kernel T hk) n hn

/-- Transfer to any integer sequence identified coefficientwise with the corner specialization. -/
theorem integer_recurrence_of_kernel (T : S → S) (hk : KernelEquation T)
    (a : ℕ → ℤ) (ha : ∀ i, coeff i (T 0) = (a i : ℚ)) (n : ℕ) (hn : 9 ≤ n) :
    recurrence a n :=
  integer_recurrence (T 0) a ha (differential_of_kernel T hk) n hn

end
end A191625Downstream

open OMA.S_oeis_a191625 (count)
open OMA.S_oeis_a191625.WalkDecomposition (CN CN_supported CN_recurrence count_eq_CN_zero)

theorem OMA.solution : type_of% @OMA.S_oeis_a191625.main := by
  intro n hn
  let T := A191625FiniteRows.T CN
  have hS : A191625FiniteRows.Supported CN := CN_supported
  have hD : A191625FiniteRows.Decomp CN := fun m d _ => CN_recurrence m d
  have hk : A191625Elim.KernelEquation T := fun s =>
    A191625FiniteRows.kernel_of_decomp CN hS hD s
  have ha (i : ℕ) : PowerSeries.coeff i (T 0) = (count i : ℚ) := by
    rw [A191625FiniteRows.coeff_T_zero, count_eq_CN_zero]
    simp
  have h := A191625Downstream.integer_recurrence_of_kernel T hk count ha n hn
  unfold A191625Downstream.recurrence at h
  linear_combination h
