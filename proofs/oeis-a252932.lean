import OMAStatements.S_oeis_a252932

namespace OMA.S_oeis_a252932

open PowerSeries




/-- The conditions of the entry on one row v with row index i. -/
def RA (i : ℕ) (v : Fin 2 → ℕ) : Prop :=
  (∀ j : Fin 2, i = 0 → j.val = 0 → v j = 0) ∧
  (∀ j : Fin 2, max i j.val ≤ v j + 3 ∧ v j ≤ max i j.val + 3) ∧
  (∀ j j' : Fin 2, j'.val = j.val + 1 → step01 (v j) (v j'))

/-- The conditions of the entry between a row u and the row v below it. -/
def RB (u v : Fin 2 → ℕ) : Prop :=
  (∀ j : Fin 2, step01 (u j) (v j)) ∧
  (∀ j j' : Fin 2, j'.val = j.val + 1 → step01 (u j) (v j'))

theorem good_iff (n : ℕ) (x : Fin n → Fin 2 → ℕ) :
    good n x ↔ (∀ i : Fin n, RA i.val (x i)) ∧
      ∀ i i' : Fin n, i'.val = i.val + 1 → RB (x i) (x i') := by
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨fun i => ⟨fun j hi hj => h1 i j hi hj, fun j => h2 i j, fun j j' hj => h3 i j j' hj⟩,
      fun i i' hi => ⟨fun j => h4 i i' j hi, fun j j' hj => h5 i i' j j' hi hj⟩⟩
  · rintro ⟨hA, hB⟩
    exact ⟨fun i j hi hj => (hA i).1 j hi hj, fun i j => (hA i).2.1 j,
      fun i j j' hj => (hA i).2.2 j j' hj, fun i i' j hi => (hB i i' hi).1 j,
      fun i i' j j' hi hj => (hB i i' hi).2 j j' hj⟩

/-- The steps from the upper left 0 keep every value at most its king-move distance. -/
theorem le_dist {n : ℕ} {x : Fin n → Fin 2 → ℕ} (h : good n x) :
    ∀ s, ∀ (i : Fin n) (j : Fin 2), i.val + j.val = s → x i j ≤ max i.val j.val := by
  obtain ⟨h1, -, h3, h4, h5⟩ := h
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro i j hs
    have hi0 := i.isLt
    have hj0 := j.isLt
    by_cases hi : i.val = 0 <;> by_cases hj : j.val = 0
    · rw [h1 i j hi hj]
      exact Nat.zero_le _
    · have e := h3 i ⟨j.val - 1, by omega⟩ j (by simp only; omega)
      have p := ih (i.val + (j.val - 1)) (by omega) i ⟨j.val - 1, by omega⟩ rfl
      simp only [step01] at e
      simp only at p
      omega
    · have e := h4 ⟨i.val - 1, by omega⟩ i j (by simp only; omega)
      have p := ih ((i.val - 1) + j.val) (by omega) ⟨i.val - 1, by omega⟩ j rfl
      simp only [step01] at e
      simp only at p
      omega
    · have e := h5 ⟨i.val - 1, by omega⟩ i ⟨j.val - 1, by omega⟩ j (by simp only; omega)
        (by simp only; omega)
      have p := ih ((i.val - 1) + (j.val - 1)) (by omega) ⟨i.val - 1, by omega⟩ ⟨j.val - 1, by omega⟩ rfl
      simp only [step01] at e
      simp only at p
      omega

/-- The conditions on a row r of deficits (its values are max i j - r j) at a row index i, with
c = min i 3: every deficit is at most max i j, and every step right changes the value by 0 or 1. -/
def ZA (c : ℕ) (r : Fin 2 → Fin 4) : Bool :=
  decide ((∀ j : Fin 2, (r j : ℕ) ≤ max c j.val) ∧
    ∀ j j' : Fin 2, j'.val = j.val + 1 →
      ((r j' : ℕ) = r j + (if c ≤ j.val then 1 else 0) ∨
        (r j' : ℕ) + 1 = r j + (if c ≤ j.val then 1 else 0)))

/-- The conditions between a row p of deficits at a row index i, with c = min i 3, and the row
r of deficits below it: every step down or diagonally down-right changes the value by 0 or 1. -/
def ZB (c : ℕ) (p r : Fin 2 → Fin 4) : Bool :=
  decide ((∀ j : Fin 2, (r j : ℕ) = p j + (if j.val ≤ c then 1 else 0) ∨
      (r j : ℕ) + 1 = p j + (if j.val ≤ c then 1 else 0)) ∧
    ∀ j j' : Fin 2, j'.val = j.val + 1 → ((r j' : ℕ) = p j ∨ (r j' : ℕ) = p j + 1))

/-- The values of a row r of deficits at row index i. -/
def vals (i : ℕ) (r : Fin 2 → Fin 4) : Fin 2 → ℕ := fun j => max i j.val - r j

theorem rowA (i : ℕ) (r : Fin 2 → Fin 4) :
    (RA i (vals i r) ∧ ∀ j : Fin 2, (r j : ℕ) ≤ max i j.val) ↔ ZA (min i 3) r = true := by
  simp only [RA, ZA, vals, step01, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨-, -, h3⟩, hb⟩
    refine ⟨fun j => ?_, fun j j' hj => ?_⟩
    · have := hb j
      have := (r j).isLt
      omega
    · have e := h3 j j' hj
      have b1 := hb j
      have b2 := hb j'
      have := (r j).isLt
      have := (r j').isLt
      have := j'.isLt
      split_ifs <;> omega
  · rintro ⟨hb, hs⟩
    refine ⟨⟨fun j hi hj => ?_, fun j => ?_, fun j j' hj => ?_⟩, fun j => ?_⟩
    · have := hb j
      omega
    · have := (r j).isLt
      have := hb j
      omega
    · have e := hs j j' hj
      have b1 := hb j
      have b2 := hb j'
      have := (r j).isLt
      have := (r j').isLt
      have := j'.isLt
      split_ifs at e <;> omega
    · have := (r j).isLt
      have := hb j
      omega

theorem rowB (i : ℕ) (p r : Fin 2 → Fin 4) (hp : ∀ j : Fin 2, (p j : ℕ) ≤ max i j.val)
    (hr : ∀ j : Fin 2, (r j : ℕ) ≤ max (i + 1) j.val) :
    RB (vals i p) (vals (i + 1) r) ↔ ZB (min i 3) p r = true := by
  simp only [RB, ZB, vals, step01, decide_eq_true_eq]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun j => ?_, fun j j' hj => ?_⟩
    · have e := h1 j
      have := hp j
      have := hr j
      have := (p j).isLt
      have := (r j).isLt
      have := j.isLt
      split_ifs <;> omega
    · have e := h2 j j' hj
      have := hp j
      have := hr j'
      have := (p j).isLt
      have := (r j').isLt
      omega
  · rintro ⟨h1, h2⟩
    refine ⟨fun j => ?_, fun j j' hj => ?_⟩
    · have e := h1 j
      have := hp j
      have := hr j
      have := (p j).isLt
      have := (r j).isLt
      have := j.isLt
      split_ifs at e <;> omega
    · have e := h2 j j' hj
      have := hp j
      have := hr j'
      have := (p j).isLt
      have := (r j').isLt
      omega

theorem bound_of_ZA {i : ℕ} {r : Fin 2 → Fin 4} (h : ZA (min i 3) r = true) (j : Fin 2) :
    (r j : ℕ) ≤ max i j.val :=
  ((rowA i r).2 h).2 j

/-- The deficit form of the conditions on an array of deficits. -/
def GZ (n : ℕ) (z : Fin n → Fin 2 → Fin 4) : Prop :=
  (∀ i : Fin n, ZA (min i.val 3) (z i) = true) ∧
    ∀ i i' : Fin n, i'.val = i.val + 1 → ZB (min i.val 3) (z i) (z i') = true

instance (n : ℕ) : DecidablePred (GZ n) := fun z => by unfold GZ; infer_instance

theorem set_eq (n : ℕ) : {x : Fin n → Fin 2 → ℕ | good n x} =
    (fun z : Fin n → Fin 2 → Fin 4 => fun i => vals i.val (z i)) '' {z | GZ n z} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_image]
  constructor
  · intro hx
    have hd : ∀ i j, x i j ≤ max i.val j.val := fun i j => le_dist hx (i.val + j.val) i j rfl
    have hw := hx.2.1
    let z : Fin n → Fin 2 → Fin 4 := fun i j =>
      ⟨max i.val j.val - x i j, by have := hd i j; have := (hw i j).1; omega⟩
    have hv : ∀ i, vals i.val (z i) = x i := fun i => by
      funext j
      simp only [vals, z]
      have := hd i j
      omega
    have hb : ∀ i j, ((z i j : Fin 4) : ℕ) ≤ max i.val j.val := fun i j => by
      simp only [z]
      omega
    rw [good_iff] at hx
    refine ⟨z, ⟨fun i => ?_, fun i i' hi => ?_⟩, funext hv⟩
    · rw [← rowA]
      exact ⟨by rw [hv]; exact hx.1 i, hb i⟩
    · have e : vals i'.val (z i') = vals (i.val + 1) (z i') := by rw [hi]
      rw [← rowB i.val (z i) (z i') (hb i) (fun j => by rw [← hi]; exact hb i' j), ← e, hv, hv]
      exact hx.2 i i' hi
  · rintro ⟨z, hz, rfl⟩
    rw [good_iff]
    refine ⟨fun i => ((rowA _ _).2 (hz.1 i)).1, fun i i' hi => ?_⟩
    have e : vals i'.val (z i') = vals (i.val + 1) (z i') := by rw [hi]
    show RB (vals i.val (z i)) (vals i'.val (z i'))
    rw [e, rowB i.val (z i) (z i') (bound_of_ZA (hz.1 i))
      (fun j => by rw [← hi]; exact bound_of_ZA (hz.1 i') j)]
    exact hz.2 i i' hi

theorem injOn (n : ℕ) :
    Set.InjOn (fun z : Fin n → Fin 2 → Fin 4 => fun i => vals i.val (z i)) {z | GZ n z} := by
  intro z hz z' hz' h
  funext i j
  have e := congrFun (congrFun h i) j
  simp only [vals] at e
  have b := bound_of_ZA (hz.1 i) j
  have b' := bound_of_ZA (hz'.1 i) j
  exact Fin.ext (by omega)

theorem a_eq (n : ℕ) :
    a n = (Finset.univ.filter fun z : Fin n → Fin 2 → Fin 4 => GZ n z).card := by
  unfold a
  rw [set_eq, Set.ncard_image_of_injOn (injOn n), ← Set.ncard_coe_finset]
  congr 1
  ext z
  simp

theorem GZ_snoc (m : ℕ) (y : Fin (m + 1) → Fin 2 → Fin 4) (t : Fin 2 → Fin 4) :
    GZ (m + 1 + 1) (Fin.snoc y t) ↔
      GZ (m + 1) y ∧ ZA (min (m + 1) 3) t = true ∧ ZB (min m 3) (y (Fin.last m)) t = true := by
  constructor
  · rintro ⟨hA, hB⟩
    refine ⟨⟨fun i => ?_, fun i i' h => ?_⟩, ?_, ?_⟩
    · have := hA (Fin.castSucc i)
      simpa only [Fin.snoc_castSucc, Fin.coe_castSucc] using this
    · have := hB (Fin.castSucc i) (Fin.castSucc i') (by simpa only [Fin.coe_castSucc] using h)
      simpa only [Fin.snoc_castSucc, Fin.coe_castSucc] using this
    · have := hA (Fin.last (m + 1))
      simpa only [Fin.snoc_last, Fin.val_last] using this
    · have := hB (Fin.castSucc (Fin.last m)) (Fin.last (m + 1)) (by simp)
      simpa only [Fin.snoc_last, Fin.snoc_castSucc, Fin.coe_castSucc, Fin.val_last] using this
  · rintro ⟨⟨hA, hB⟩, ht, hl⟩
    refine ⟨fun i => ?_, fun i i' h => ?_⟩
    · induction i using Fin.lastCases with
      | last => simpa only [Fin.snoc_last, Fin.val_last] using ht
      | cast i => simpa only [Fin.snoc_castSucc, Fin.coe_castSucc] using hA i
    · induction i' using Fin.lastCases with
      | last =>
        have hi : i = Fin.castSucc (Fin.last m) := by
          apply Fin.ext
          simp only [Fin.val_last] at h
          simp only [Fin.coe_castSucc, Fin.val_last]
          omega
        subst hi
        simpa only [Fin.snoc_last, Fin.snoc_castSucc, Fin.coe_castSucc, Fin.val_last] using hl
      | cast i'' =>
        induction i using Fin.lastCases with
        | last =>
          simp only [Fin.val_last, Fin.coe_castSucc] at h
          have := i''.isLt
          omega
        | cast i =>
          have := hB i i'' (by simpa only [Fin.coe_castSucc] using h)
          simpa only [Fin.snoc_castSucc, Fin.coe_castSucc] using this

theorem GZ_one (z : Fin (0 + 1) → Fin 2 → Fin 4) : GZ (0 + 1) z ↔ ZA 0 (z 0) = true := by
  constructor
  · rintro ⟨hA, -⟩
    simpa using hA 0
  · intro h
    refine ⟨fun i => ?_, fun i i' hi => ?_⟩
    · have hi : i = 0 := by
        ext
        simp only [Fin.val_zero]
        have := i.isLt
        omega
      subst hi
      simpa using h
    · have := i.isLt
      have := i'.isLt
      omega

theorem sum_snoc (m : ℕ) (f : (Fin (m + 1 + 1) → Fin 2 → Fin 4) → ℕ) :
    ∑ z : Fin (m + 1 + 1) → Fin 2 → Fin 4, f z =
      ∑ t : Fin 2 → Fin 4, ∑ y : Fin (m + 1) → Fin 2 → Fin 4, f (Fin.snoc y t) := by
  rw [← (Fin.snocEquiv fun _ => Fin 2 → Fin 4).sum_comp, Fintype.sum_prod_type]
  rfl

/-- The number of deficit arrays with m + 1 rows whose last row is r. -/
def Cnt (m : ℕ) (r : Fin 2 → Fin 4) : ℕ :=
  ∑ z : Fin (m + 1) → Fin 2 → Fin 4, if GZ (m + 1) z ∧ z (Fin.last m) = r then 1 else 0

theorem a_succ (n : ℕ) : a (n + 1) = ∑ r : Fin 2 → Fin 4, Cnt n r := by
  rw [a_eq, Finset.card_filter]
  unfold Cnt
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  rw [Finset.sum_eq_single (z (Fin.last n))]
  · simp
  · intro r _ hr
    simp [Ne.symm hr]
  · simp

theorem Cnt_zero (r : Fin 2 → Fin 4) : Cnt 0 r = if ZA 0 r = true then 1 else 0 := by
  unfold Cnt
  rw [Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin 2 → Fin 4)) _
    (fun t => if ZA 0 t = true ∧ t = r then 1 else 0) (fun z => by
      simp only [Equiv.funUnique_apply, GZ_one]
      rfl)]
  rw [Finset.sum_eq_single r]
  · simp
  · intro t _ ht
    simp [ht]
  · simp

theorem Cnt_succ (m : ℕ) (r : Fin 2 → Fin 4) :
    Cnt (m + 1) r = ∑ p : Fin 2 → Fin 4,
      if (ZA (min (m + 1) 3) r && ZB (min m 3) p r) = true then Cnt m p else 0 := by
  have lhs : Cnt (m + 1) r = ∑ y : Fin (m + 1) → Fin 2 → Fin 4,
      if GZ (m + 1) y ∧ ZA (min (m + 1) 3) r = true ∧ ZB (min m 3) (y (Fin.last m)) r = true
      then 1 else 0 := by
    unfold Cnt
    rw [sum_snoc, Finset.sum_eq_single r]
    · refine Finset.sum_congr rfl (fun y _ => ?_)
      simp only [GZ_snoc, Fin.snoc_last, and_true]
    · intro t _ ht
      refine Finset.sum_eq_zero (fun y _ => ?_)
      simp [Fin.snoc_last, ht]
    · simp
  have rhs : ∀ p : Fin 2 → Fin 4,
      (if (ZA (min (m + 1) 3) r && ZB (min m 3) p r) = true then Cnt m p else 0) =
        ∑ y : Fin (m + 1) → Fin 2 → Fin 4,
          if (ZA (min (m + 1) 3) r && ZB (min m 3) p r) = true ∧ GZ (m + 1) y ∧
            y (Fin.last m) = p then 1 else 0 := by
    intro p
    unfold Cnt
    split_ifs with h
    · refine Finset.sum_congr rfl (fun y _ => ?_)
      simp [h]
    · symm
      refine Finset.sum_eq_zero (fun y _ => ?_)
      simp [h]
  rw [lhs, Finset.sum_congr rfl (fun p _ => rhs p), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [Finset.sum_eq_single (y (Fin.last m))]
  · simp only [and_true, Bool.and_eq_true]
    by_cases h1 : GZ (m + 1) y <;> by_cases h2 : ZA (min (m + 1) 3) r = true <;>
      by_cases h3 : ZB (min m 3) (y (Fin.last m)) r = true <;> simp [h1, h2, h3]
  · intro p _ hp
    simp [Ne.symm hp]
  · simp

/-- From row 3 on the transfer does not depend on the row. -/
theorem Cnt_hom (m : ℕ) (hm : 3 ≤ m) (r : Fin 2 → Fin 4) :
    Cnt (m + 1) r = ∑ p : Fin 2 → Fin 4,
      if (ZA 3 r && ZB 3 p r) = true then Cnt m p else 0 := by
  rw [Cnt_succ, Nat.min_eq_right (by omega : 3 ≤ m + 1), Nat.min_eq_right hm]

theorem sum_pi_succ {m : ℕ} (g : (Fin (m + 1) → Fin 4) → ℕ) :
    ∑ p, g p = ∑ c : Fin 4, ∑ q : Fin m → Fin 4, g (Fin.cons c q) := by
  rw [← (Fin.consEquiv fun _ => Fin 4).sum_comp, Fintype.sum_prod_type]
  rfl

theorem sum_pi_zero (g : (Fin 0 → Fin 4) → ℕ) : ∑ p, g p = g ![] := by
  rw [Fintype.sum_unique]
  exact congrArg g (Subsingleton.elim _ _)

theorem row_eta (r : Fin 2 → Fin 4) : ![r 0, r 1] = r := by
  funext j
  fin_cases j <;> rfl

/-- The position of a row of deficits in the tables. -/
def code (r : Fin 2 → Fin 4) : ℕ := (r 0 : ℕ) * 4 + (r 1 : ℕ)

/-- The table of Cnt 0: the base 2^10 digit at position `code r` is Cnt 0 r. -/
def t0 (r : Fin 2 → Fin 4) : ℕ :=
  1025 / 1024 ^ code r % 1024

/-- The table of Cnt 1: the base 2^10 digit at position `code r` is Cnt 1 r. -/
def t1 (r : Fin 2 → Fin 4) : ℕ :=
  1128098930098178 / 1024 ^ code r % 1024

/-- The table of Cnt 2: the base 2^10 digit at position `code r` is Cnt 2 r. -/
def t2 (r : Fin 2 → Fin 4) : ℕ :=
  1271364420346091174019958046722 / 1024 ^ code r % 1024

/-- The table of Cnt 3: the base 2^10 digit at position `code r` is Cnt 3 r. -/
def t3 (r : Fin 2 → Fin 4) : ℕ :=
  1432822879005603954364652228090067919566798850 / 1024 ^ code r % 1024

/-- The table of Cnt 4: the base 2^10 digit at position `code r` is Cnt 4 r. -/
def t4 (r : Fin 2 → Fin 4) : ℕ :=
  20003768443082000662839885428454439610147143682 / 1024 ^ code r % 1024

/-- The table of Cnt 5: the base 2^10 digit at position `code r` is Cnt 5 r. -/
def t5 (r : Fin 2 → Fin 4) : ℕ :=
  78548799775524549493722695458376211273823027202 / 1024 ^ code r % 1024

/-- The table of Cnt 6: the base 2^10 digit at position `code r` is Cnt 6 r. -/
def t6 (r : Fin 2 → Fin 4) : ℕ :=
  199903879959628608543945657829047305092718395394 / 1024 ^ code r % 1024

/-- The table of Cnt 7: the base 2^10 digit at position `code r` is Cnt 7 r. -/
def t7 (r : Fin 2 → Fin 4) : ℕ :=
  406904972078689535910441348051659643248957194242 / 1024 ^ code r % 1024

lemma Cnt0 (r : Fin 2 → Fin 4) : Cnt 0 r = t0 r := by
  have h : ∀ c0 c1 : Fin 4, Cnt 0 ![c0, c1] = t0 ![c0, c1] := by
    intro c0 c1
    rw [Cnt_zero]
    revert c0 c1
    decide +kernel
  rw [← row_eta r]
  exact h _ _

lemma Cnt1 (r : Fin 2 → Fin 4) : Cnt 1 r = t1 r := by
  have h : ∀ c0 c1 : Fin 4, Cnt 1 ![c0, c1] = t1 ![c0, c1] := by
    intro c0 c1
    rw [Cnt_succ]
    simp only [Cnt0, sum_pi_succ, sum_pi_zero]
    revert c0 c1
    decide +kernel
  rw [← row_eta r]
  exact h _ _

lemma Cnt2 (r : Fin 2 → Fin 4) : Cnt 2 r = t2 r := by
  have h : ∀ c0 c1 : Fin 4, Cnt 2 ![c0, c1] = t2 ![c0, c1] := by
    intro c0 c1
    rw [Cnt_succ]
    simp only [Cnt1, sum_pi_succ, sum_pi_zero]
    revert c0 c1
    decide +kernel
  rw [← row_eta r]
  exact h _ _

lemma Cnt3 (r : Fin 2 → Fin 4) : Cnt 3 r = t3 r := by
  have h : ∀ c0 c1 : Fin 4, Cnt 3 ![c0, c1] = t3 ![c0, c1] := by
    intro c0 c1
    rw [Cnt_succ]
    simp only [Cnt2, sum_pi_succ, sum_pi_zero]
    revert c0 c1
    decide +kernel
  rw [← row_eta r]
  exact h _ _

lemma Cnt4 (r : Fin 2 → Fin 4) : Cnt 4 r = t4 r := by
  have h : ∀ c0 c1 : Fin 4, Cnt 4 ![c0, c1] = t4 ![c0, c1] := by
    intro c0 c1
    rw [Cnt_succ]
    simp only [Cnt3, sum_pi_succ, sum_pi_zero]
    revert c0 c1
    decide +kernel
  rw [← row_eta r]
  exact h _ _

lemma Cnt5 (r : Fin 2 → Fin 4) : Cnt 5 r = t5 r := by
  have h : ∀ c0 c1 : Fin 4, Cnt 5 ![c0, c1] = t5 ![c0, c1] := by
    intro c0 c1
    rw [Cnt_succ]
    simp only [Cnt4, sum_pi_succ, sum_pi_zero]
    revert c0 c1
    decide +kernel
  rw [← row_eta r]
  exact h _ _

lemma Cnt6 (r : Fin 2 → Fin 4) : Cnt 6 r = t6 r := by
  have h : ∀ c0 c1 : Fin 4, Cnt 6 ![c0, c1] = t6 ![c0, c1] := by
    intro c0 c1
    rw [Cnt_succ]
    simp only [Cnt5, sum_pi_succ, sum_pi_zero]
    revert c0 c1
    decide +kernel
  rw [← row_eta r]
  exact h _ _

lemma Cnt7 (r : Fin 2 → Fin 4) : Cnt 7 r = t7 r := by
  have h : ∀ c0 c1 : Fin 4, Cnt 7 ![c0, c1] = t7 ![c0, c1] := by
    intro c0 c1
    rw [Cnt_succ]
    simp only [Cnt6, sum_pi_succ, sum_pi_zero]
    revert c0 c1
    decide +kernel
  rw [← row_eta r]
  exact h _ _

/-- The difference equation of order 4 on every deficit row, from m = 3 on. -/
theorem Cnt_rec (m : ℕ) : ∀ r : Fin 2 → Fin 4, (Cnt (m + 7) r : ℤ) = 4 * Cnt (m + 6) r - 6 * Cnt (m + 5) r + 4 * Cnt (m + 4) r - Cnt (m + 3) r := by
  induction m with
  | zero =>
    intro r
    simp only [Nat.zero_add, Cnt3, Cnt4, Cnt5, Cnt6, Cnt7]
    have h : ∀ c0 c1 : Fin 4, (t7 ![c0, c1] : ℤ) = 4 * t6 ![c0, c1] - 6 * t5 ![c0, c1] + 4 * t4 ![c0, c1] - t3 ![c0, c1] := by
      decide +kernel
    rw [← row_eta r]
    exact h _ _
  | succ m ih =>
    intro r
    rw [show m + 1 + 7 = m + 7 + 1 by omega, show m + 1 + 6 = m + 6 + 1 by omega, show m + 1 + 5 = m + 5 + 1 by omega, show m + 1 + 4 = m + 4 + 1 by omega, show m + 1 + 3 = m + 3 + 1 by omega,
      Cnt_hom (m + 7) (by omega), Cnt_hom (m + 6) (by omega), Cnt_hom (m + 5) (by omega), Cnt_hom (m + 4) (by omega), Cnt_hom (m + 3) (by omega)]
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    split_ifs
    · exact ih p
    · simp

/-- The recurrence of a, for n >= 8. -/
theorem a_rec (m : ℕ) : (a (m + 7 + 1) : ℤ) = 4 * a (m + 6 + 1) - 6 * a (m + 5 + 1) + 4 * a (m + 4 + 1) - a (m + 3 + 1) := by
  rw [a_succ, a_succ, a_succ, a_succ, a_succ]
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun r _ => Cnt_rec m r)

lemma v1 : a 1 = 2 := by
  rw [a_succ]
  simp only [Cnt0, sum_pi_succ, sum_pi_zero]
  decide +kernel

lemma v2 : a 2 = 5 := by
  rw [a_succ]
  simp only [Cnt1, sum_pi_succ, sum_pi_zero]
  decide +kernel

lemma v3 : a 3 = 13 := by
  rw [a_succ]
  simp only [Cnt2, sum_pi_succ, sum_pi_zero]
  decide +kernel

lemma v4 : a 4 = 34 := by
  rw [a_succ]
  simp only [Cnt3, sum_pi_succ, sum_pi_zero]
  decide +kernel

lemma v5 : a 5 = 83 := by
  rw [a_succ]
  simp only [Cnt4, sum_pi_succ, sum_pi_zero]
  decide +kernel

lemma v6 : a 6 = 176 := by
  rw [a_succ]
  simp only [Cnt5, sum_pi_succ, sum_pi_zero]
  decide +kernel

lemma v7 : a 7 = 329 := by
  rw [a_succ]
  simp only [Cnt6, sum_pi_succ, sum_pi_zero]
  decide +kernel

/-- Barker's recurrence, for n > 6. -/
theorem recurrence (n : ℕ) (hn : 6 < n) : (a n : ℤ) = 4 * a (n - 1) - 6 * a (n - 2) + 4 * a (n - 3) - a (n - 4) := by
  rcases Nat.lt_or_ge n 8 with h | h
  · interval_cases n
    · show (a 7 : ℤ) = 4 * a 6 - 6 * a 5 + 4 * a 4 - a 3
      rw [v7, v6, v5, v4, v3]
      norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 + 4 + 1 := ⟨n - 8, by omega⟩
    rw [show m + 3 + 4 + 1 - 1 = m + 6 + 1 by omega, show m + 3 + 4 + 1 - 2 = m + 5 + 1 by omega, show m + 3 + 4 + 1 - 3 = m + 4 + 1 by omega, show m + 3 + 4 + 1 - 4 = m + 3 + 1 by omega]
    rw [show m + 3 + 4 + 1 = m + 7 + 1 by omega]
    exact a_rec m

/-- Barker's g.f., as A(x) (1 - x)^4 = its numerator in Z[[x]]. -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 4 =
    X * (2 - 3 * X + 5 * X ^ 2 + 4 * X ^ 3 + 7 * X ^ 4 + X ^ 5) := by
  set A : ℤ⟦X⟧ := PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) with hA
  have e1 : A * (1 - X) ^ 4 = A - C 4 * (A * X ^ 1) + C 6 * (A * X ^ 2) - C 4 * (A * X ^ 3) + A * X ^ 4 := by
    simp only [map_ofNat]; ring
  have e2 : (X * (2 - 3 * X + 5 * X ^ 2 + 4 * X ^ 3 + 7 * X ^ 4 + X ^ 5) : ℤ⟦X⟧) =
      X ^ 1 * C 2 - X ^ 2 * C 3 + X ^ 3 * C 5 + X ^ 4 * C 4 + X ^ 5 * C 7 + X ^ 6 := by
    simp only [map_ofNat]; ring
  rw [e1, e2]
  ext n
  have hc : ∀ k, coeff k A = if k = 0 then (0 : ℤ) else a k := fun k => by rw [hA, coeff_mk]
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_C, coeff_X_pow, coeff_mul_X_pow', hc]
  rcases Nat.lt_or_ge n 7 with hn | hn
  · interval_cases n <;> simp [v1, v2, v3, v4, v5, v6]
  · obtain ⟨q, rfl⟩ : ∃ q, n = q + 7 := ⟨n - 7, by omega⟩
    have h := recurrence (q + 7) (by omega)
    simp only [show q + 7 - 1 = q + 6 by omega, show q + 7 - 2 = q + 5 by omega, show q + 7 - 3 = q + 4 by omega, show q + 7 - 4 = q + 3 by omega] at h ⊢
    simp only [ show ¬ q + 7 = 0 by omega, show 1 ≤ q + 7 by omega, show ¬ q + 6 = 0 by omega,
      show 2 ≤ q + 7 by omega, show ¬ q + 5 = 0 by omega, show 3 ≤ q + 7 by omega,
      show ¬ q + 4 = 0 by omega, show 4 ≤ q + 7 by omega, show ¬ q + 3 = 0 by omega,
      show ¬ q + 7 = 1 by omega, show ¬ q + 7 = 2 by omega, show ¬ q + 7 = 3 by omega,
      show ¬ q + 7 = 4 by omega, show ¬ q + 7 = 5 by omega, show ¬ q + 7 = 6 by omega, if_true,
      if_false]
    rw [h]
    ring

/-- Controls: the entry's data a(1..40). -/
theorem controls : a 1 = 2 ∧ a 2 = 5 ∧ a 3 = 13 ∧ a 4 = 34 ∧ a 5 = 83 ∧ a 6 = 176 ∧ a 7 = 329 ∧
    a 8 = 558 ∧ a 9 = 879 ∧ a 10 = 1308 ∧ a 11 = 1861 ∧ a 12 = 2554 ∧ a 13 = 3403 ∧ a 14 = 4424 ∧
    a 15 = 5633 ∧ a 16 = 7046 ∧ a 17 = 8679 ∧ a 18 = 10548 ∧ a 19 = 12669 ∧ a 20 = 15058 ∧
    a 21 = 17731 ∧ a 22 = 20704 ∧ a 23 = 23993 ∧ a 24 = 27614 ∧ a 25 = 31583 ∧ a 26 = 35916 ∧
    a 27 = 40629 ∧ a 28 = 45738 ∧ a 29 = 51259 ∧ a 30 = 57208 ∧ a 31 = 63601 ∧ a 32 = 70454 ∧
    a 33 = 77783 ∧ a 34 = 85604 ∧ a 35 = 93933 ∧ a 36 = 102786 ∧ a 37 = 112179 ∧ a 38 = 122128 ∧
    a 39 = 132649 ∧ a 40 = 143758 := by
  have v8 : a 8 = 558 := by
    have h : (a 8 : ℤ) = 4 * a 7 - 6 * a 6 + 4 * a 5 - a 4 := a_rec 0
    rw [v7, v6, v5, v4] at h
    omega
  have v9 : a 9 = 879 := by
    have h : (a 9 : ℤ) = 4 * a 8 - 6 * a 7 + 4 * a 6 - a 5 := a_rec 1
    rw [v8, v7, v6, v5] at h
    omega
  have v10 : a 10 = 1308 := by
    have h : (a 10 : ℤ) = 4 * a 9 - 6 * a 8 + 4 * a 7 - a 6 := a_rec 2
    rw [v9, v8, v7, v6] at h
    omega
  have v11 : a 11 = 1861 := by
    have h : (a 11 : ℤ) = 4 * a 10 - 6 * a 9 + 4 * a 8 - a 7 := a_rec 3
    rw [v10, v9, v8, v7] at h
    omega
  have v12 : a 12 = 2554 := by
    have h : (a 12 : ℤ) = 4 * a 11 - 6 * a 10 + 4 * a 9 - a 8 := a_rec 4
    rw [v11, v10, v9, v8] at h
    omega
  have v13 : a 13 = 3403 := by
    have h : (a 13 : ℤ) = 4 * a 12 - 6 * a 11 + 4 * a 10 - a 9 := a_rec 5
    rw [v12, v11, v10, v9] at h
    omega
  have v14 : a 14 = 4424 := by
    have h : (a 14 : ℤ) = 4 * a 13 - 6 * a 12 + 4 * a 11 - a 10 := a_rec 6
    rw [v13, v12, v11, v10] at h
    omega
  have v15 : a 15 = 5633 := by
    have h : (a 15 : ℤ) = 4 * a 14 - 6 * a 13 + 4 * a 12 - a 11 := a_rec 7
    rw [v14, v13, v12, v11] at h
    omega
  have v16 : a 16 = 7046 := by
    have h : (a 16 : ℤ) = 4 * a 15 - 6 * a 14 + 4 * a 13 - a 12 := a_rec 8
    rw [v15, v14, v13, v12] at h
    omega
  have v17 : a 17 = 8679 := by
    have h : (a 17 : ℤ) = 4 * a 16 - 6 * a 15 + 4 * a 14 - a 13 := a_rec 9
    rw [v16, v15, v14, v13] at h
    omega
  have v18 : a 18 = 10548 := by
    have h : (a 18 : ℤ) = 4 * a 17 - 6 * a 16 + 4 * a 15 - a 14 := a_rec 10
    rw [v17, v16, v15, v14] at h
    omega
  have v19 : a 19 = 12669 := by
    have h : (a 19 : ℤ) = 4 * a 18 - 6 * a 17 + 4 * a 16 - a 15 := a_rec 11
    rw [v18, v17, v16, v15] at h
    omega
  have v20 : a 20 = 15058 := by
    have h : (a 20 : ℤ) = 4 * a 19 - 6 * a 18 + 4 * a 17 - a 16 := a_rec 12
    rw [v19, v18, v17, v16] at h
    omega
  have v21 : a 21 = 17731 := by
    have h : (a 21 : ℤ) = 4 * a 20 - 6 * a 19 + 4 * a 18 - a 17 := a_rec 13
    rw [v20, v19, v18, v17] at h
    omega
  have v22 : a 22 = 20704 := by
    have h : (a 22 : ℤ) = 4 * a 21 - 6 * a 20 + 4 * a 19 - a 18 := a_rec 14
    rw [v21, v20, v19, v18] at h
    omega
  have v23 : a 23 = 23993 := by
    have h : (a 23 : ℤ) = 4 * a 22 - 6 * a 21 + 4 * a 20 - a 19 := a_rec 15
    rw [v22, v21, v20, v19] at h
    omega
  have v24 : a 24 = 27614 := by
    have h : (a 24 : ℤ) = 4 * a 23 - 6 * a 22 + 4 * a 21 - a 20 := a_rec 16
    rw [v23, v22, v21, v20] at h
    omega
  have v25 : a 25 = 31583 := by
    have h : (a 25 : ℤ) = 4 * a 24 - 6 * a 23 + 4 * a 22 - a 21 := a_rec 17
    rw [v24, v23, v22, v21] at h
    omega
  have v26 : a 26 = 35916 := by
    have h : (a 26 : ℤ) = 4 * a 25 - 6 * a 24 + 4 * a 23 - a 22 := a_rec 18
    rw [v25, v24, v23, v22] at h
    omega
  have v27 : a 27 = 40629 := by
    have h : (a 27 : ℤ) = 4 * a 26 - 6 * a 25 + 4 * a 24 - a 23 := a_rec 19
    rw [v26, v25, v24, v23] at h
    omega
  have v28 : a 28 = 45738 := by
    have h : (a 28 : ℤ) = 4 * a 27 - 6 * a 26 + 4 * a 25 - a 24 := a_rec 20
    rw [v27, v26, v25, v24] at h
    omega
  have v29 : a 29 = 51259 := by
    have h : (a 29 : ℤ) = 4 * a 28 - 6 * a 27 + 4 * a 26 - a 25 := a_rec 21
    rw [v28, v27, v26, v25] at h
    omega
  have v30 : a 30 = 57208 := by
    have h : (a 30 : ℤ) = 4 * a 29 - 6 * a 28 + 4 * a 27 - a 26 := a_rec 22
    rw [v29, v28, v27, v26] at h
    omega
  have v31 : a 31 = 63601 := by
    have h : (a 31 : ℤ) = 4 * a 30 - 6 * a 29 + 4 * a 28 - a 27 := a_rec 23
    rw [v30, v29, v28, v27] at h
    omega
  have v32 : a 32 = 70454 := by
    have h : (a 32 : ℤ) = 4 * a 31 - 6 * a 30 + 4 * a 29 - a 28 := a_rec 24
    rw [v31, v30, v29, v28] at h
    omega
  have v33 : a 33 = 77783 := by
    have h : (a 33 : ℤ) = 4 * a 32 - 6 * a 31 + 4 * a 30 - a 29 := a_rec 25
    rw [v32, v31, v30, v29] at h
    omega
  have v34 : a 34 = 85604 := by
    have h : (a 34 : ℤ) = 4 * a 33 - 6 * a 32 + 4 * a 31 - a 30 := a_rec 26
    rw [v33, v32, v31, v30] at h
    omega
  have v35 : a 35 = 93933 := by
    have h : (a 35 : ℤ) = 4 * a 34 - 6 * a 33 + 4 * a 32 - a 31 := a_rec 27
    rw [v34, v33, v32, v31] at h
    omega
  have v36 : a 36 = 102786 := by
    have h : (a 36 : ℤ) = 4 * a 35 - 6 * a 34 + 4 * a 33 - a 32 := a_rec 28
    rw [v35, v34, v33, v32] at h
    omega
  have v37 : a 37 = 112179 := by
    have h : (a 37 : ℤ) = 4 * a 36 - 6 * a 35 + 4 * a 34 - a 33 := a_rec 29
    rw [v36, v35, v34, v33] at h
    omega
  have v38 : a 38 = 122128 := by
    have h : (a 38 : ℤ) = 4 * a 37 - 6 * a 36 + 4 * a 35 - a 34 := a_rec 30
    rw [v37, v36, v35, v34] at h
    omega
  have v39 : a 39 = 132649 := by
    have h : (a 39 : ℤ) = 4 * a 38 - 6 * a 37 + 4 * a 36 - a 35 := a_rec 31
    rw [v38, v37, v36, v35] at h
    omega
  have v40 : a 40 = 143758 := by
    have h : (a 40 : ℤ) = 4 * a 39 - 6 * a 38 + 4 * a 37 - a 36 := a_rec 32
    rw [v39, v38, v37, v36] at h
    omega
  exact ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28, v29, v30, v31, v32, v33, v34, v35, v36, v37, v38, v39, v40⟩

/-- Both of Barker's conjectures. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 4 =
      X * (2 - 3 * X + 5 * X ^ 2 + 4 * X ^ 3 + 7 * X ^ 4 + X ^ 5) ∧
    ∀ n : ℕ, 6 < n → (a n : ℤ) = 4 * a (n - 1) - 6 * a (n - 2) + 4 * a (n - 3) - a (n - 4) :=
  ⟨gf, recurrence⟩

end OMA.S_oeis_a252932

theorem OMA.solution : type_of% @OMA.S_oeis_a252932.main :=
  OMA.S_oeis_a252932.conjecture
