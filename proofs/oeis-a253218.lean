import OMAStatements.S_oeis_a253218

namespace OMA.S_oeis_a253218

open PowerSeries




/-- The conditions of the entry on one row v with row index i. -/
def RA (i : ℕ) (v : Fin 3 → ℕ) : Prop :=
  (∀ j : Fin 3, i = 0 → j.val = 0 → v j = 0) ∧
  (∀ j : Fin 3, max i j.val ≤ v j + 2 ∧ v j ≤ max i j.val + 2) ∧
  (∀ j j' : Fin 3, j'.val = j.val + 1 → step01 (v j) (v j'))

/-- The conditions of the entry between a row u and the row v below it. -/
def RB (u v : Fin 3 → ℕ) : Prop :=
  (∀ j : Fin 3, step01 (u j) (v j)) ∧
  (∀ j j' : Fin 3, j'.val = j.val + 1 → step01 (u j) (v j'))

theorem good_iff (n : ℕ) (x : Fin n → Fin 3 → ℕ) :
    good n x ↔ ((∀ i : Fin n, RA i.val (x i)) ∧
      ∀ i i' : Fin n, i'.val = i.val + 1 → RB (x i) (x i')) ∧
      ∀ i j, i.val + 1 = n → j.val + 1 = 3 → x i j + 2 = max i.val j.val := by
  constructor
  · rintro ⟨h1, h6, h2, h3, h4, h5⟩
    exact ⟨⟨fun i => ⟨fun j hi hj => h1 i j hi hj, fun j => h2 i j, fun j j' hj => h3 i j j' hj⟩,
      fun i i' hi => ⟨fun j => h4 i i' j hi, fun j j' hj => h5 i i' j j' hi hj⟩⟩, h6⟩
  · rintro ⟨⟨hA, hB⟩, h6⟩
    exact ⟨fun i j hi hj => (hA i).1 j hi hj, h6, fun i j => (hA i).2.1 j,
      fun i j j' hj => (hA i).2.2 j j' hj, fun i i' j hi => (hB i i' hi).1 j,
      fun i i' j j' hi hj => (hB i i' hi).2 j j' hj⟩

/-- The steps from the upper left 0 keep every value at most its king-move distance. -/
theorem le_dist {n : ℕ} {x : Fin n → Fin 3 → ℕ} (h : good n x) :
    ∀ s, ∀ (i : Fin n) (j : Fin 3), i.val + j.val = s → x i j ≤ max i.val j.val := by
  obtain ⟨h1, -, -, h3, h4, h5⟩ := h
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
c = min i 2: every deficit is at most max i j, and every step right changes the value by 0 or 1. -/
def ZA (c : ℕ) (r : Fin 3 → Fin 3) : Bool :=
  (List.finRange 3).all (fun j => decide ((r j : ℕ) ≤ max c j.val)) &&
    (List.finRange 3).all (fun j => decide (∀ h : j.val + 1 < 3,
      (r ⟨j.val + 1, h⟩ : ℕ) = r j + (if c ≤ j.val then 1 else 0) ∨
        (r ⟨j.val + 1, h⟩ : ℕ) + 1 = r j + (if c ≤ j.val then 1 else 0)))

/-- The conditions between a row p of deficits at a row index i, with c = min i 2, and the row
r of deficits below it: every step down or diagonally down-right changes the value by 0 or 1. -/
def ZB (c : ℕ) (p r : Fin 3 → Fin 3) : Bool :=
  (List.finRange 3).all (fun j => decide ((r j : ℕ) = p j + (if j.val ≤ c then 1 else 0) ∨
      (r j : ℕ) + 1 = p j + (if j.val ≤ c then 1 else 0))) &&
    (List.finRange 3).all (fun j => decide (∀ h : j.val + 1 < 3,
      (r ⟨j.val + 1, h⟩ : ℕ) = p j ∨ (r ⟨j.val + 1, h⟩ : ℕ) = p j + 1))

theorem ZA_iff (c : ℕ) (r : Fin 3 → Fin 3) : ZA c r = true ↔
    (∀ j : Fin 3, (r j : ℕ) ≤ max c j.val) ∧
      ∀ j : Fin 3, ∀ h : j.val + 1 < 3,
        ((r ⟨j.val + 1, h⟩ : ℕ) = r j + (if c ≤ j.val then 1 else 0) ∨
          (r ⟨j.val + 1, h⟩ : ℕ) + 1 = r j + (if c ≤ j.val then 1 else 0)) := by
  simp only [ZA, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq]

theorem ZB_iff (c : ℕ) (p r : Fin 3 → Fin 3) : ZB c p r = true ↔
    (∀ j : Fin 3, (r j : ℕ) = p j + (if j.val ≤ c then 1 else 0) ∨
      (r j : ℕ) + 1 = p j + (if j.val ≤ c then 1 else 0)) ∧
      ∀ j : Fin 3, ∀ h : j.val + 1 < 3,
        ((r ⟨j.val + 1, h⟩ : ℕ) = p j ∨ (r ⟨j.val + 1, h⟩ : ℕ) = p j + 1) := by
  simp only [ZB, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq]

/-- The values of a row r of deficits at row index i. -/
def vals (i : ℕ) (r : Fin 3 → Fin 3) : Fin 3 → ℕ := fun j => max i j.val - r j

theorem rowA (i : ℕ) (r : Fin 3 → Fin 3) :
    (RA i (vals i r) ∧ ∀ j : Fin 3, (r j : ℕ) ≤ max i j.val) ↔ ZA (min i 2) r = true := by
  rw [ZA_iff]
  simp only [RA, vals, step01]
  constructor
  · rintro ⟨⟨-, -, h3⟩, hb⟩
    refine ⟨fun j => ?_, fun j h => ?_⟩
    · have := hb j
      have := (r j).isLt
      omega
    · have e : max i (j.val + 1) - (r ⟨j.val + 1, h⟩ : ℕ) = max i j.val - r j ∨
          max i (j.val + 1) - (r ⟨j.val + 1, h⟩ : ℕ) = max i j.val - r j + 1 := h3 j ⟨j.val + 1, h⟩ rfl
      have b1 := hb j
      have b2 : (r ⟨j.val + 1, h⟩ : ℕ) ≤ max i (j.val + 1) := hb ⟨j.val + 1, h⟩
      have := (r j).isLt
      have := (r ⟨j.val + 1, h⟩).isLt
      split_ifs <;> omega
  · rintro ⟨hb, hs⟩
    refine ⟨⟨fun j hi hj => ?_, fun j => ?_, fun j j' hj => ?_⟩, fun j => ?_⟩
    · have := hb j
      omega
    · have := (r j).isLt
      have := hb j
      omega
    · have h : j.val + 1 < 3 := by have := j'.isLt; omega
      have hj' : j' = ⟨j.val + 1, h⟩ := Fin.ext hj
      rw [hj']
      show max i (j.val + 1) - (r ⟨j.val + 1, h⟩ : ℕ) = max i j.val - r j ∨
        max i (j.val + 1) - (r ⟨j.val + 1, h⟩ : ℕ) = max i j.val - r j + 1
      have e := hs j h
      have b1 := hb j
      have b2 : (r ⟨j.val + 1, h⟩ : ℕ) ≤ max (min i 2) (j.val + 1) := hb ⟨j.val + 1, h⟩
      have := (r j).isLt
      have := (r ⟨j.val + 1, h⟩).isLt
      split_ifs at e <;> omega
    · have := (r j).isLt
      have := hb j
      omega

theorem rowB (i : ℕ) (p r : Fin 3 → Fin 3) (hp : ∀ j : Fin 3, (p j : ℕ) ≤ max i j.val)
    (hr : ∀ j : Fin 3, (r j : ℕ) ≤ max (i + 1) j.val) :
    RB (vals i p) (vals (i + 1) r) ↔ ZB (min i 2) p r = true := by
  rw [ZB_iff]
  simp only [RB, vals, step01]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun j => ?_, fun j h => ?_⟩
    · have e := h1 j
      have := hp j
      have := hr j
      have := (p j).isLt
      have := (r j).isLt
      have := j.isLt
      split_ifs <;> omega
    · have e : max (i + 1) (j.val + 1) - (r ⟨j.val + 1, h⟩ : ℕ) = max i j.val - p j ∨
          max (i + 1) (j.val + 1) - (r ⟨j.val + 1, h⟩ : ℕ) = max i j.val - p j + 1 :=
        h2 j ⟨j.val + 1, h⟩ rfl
      have := hp j
      have b2 : (r ⟨j.val + 1, h⟩ : ℕ) ≤ max (i + 1) (j.val + 1) := hr ⟨j.val + 1, h⟩
      have := (p j).isLt
      have := (r ⟨j.val + 1, h⟩).isLt
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
    · have h : j.val + 1 < 3 := by have := j'.isLt; omega
      have hj' : j' = ⟨j.val + 1, h⟩ := Fin.ext hj
      rw [hj']
      show max (i + 1) (j.val + 1) - (r ⟨j.val + 1, h⟩ : ℕ) = max i j.val - p j ∨
        max (i + 1) (j.val + 1) - (r ⟨j.val + 1, h⟩ : ℕ) = max i j.val - p j + 1
      have e := h2 j h
      have := hp j
      have b2 : (r ⟨j.val + 1, h⟩ : ℕ) ≤ max (i + 1) (j.val + 1) := hr ⟨j.val + 1, h⟩
      have := (p j).isLt
      have := (r ⟨j.val + 1, h⟩).isLt
      omega

theorem bound_of_ZA {i : ℕ} {r : Fin 3 → Fin 3} (h : ZA (min i 2) r = true) (j : Fin 3) :
    (r j : ℕ) ≤ max i j.val :=
  ((rowA i r).2 h).2 j

/-- The deficit form of the conditions on an array of deficits. -/
def GZ (n : ℕ) (z : Fin n → Fin 3 → Fin 3) : Prop :=
  (∀ i : Fin n, ZA (min i.val 2) (z i) = true) ∧
    ∀ i i' : Fin n, i'.val = i.val + 1 → ZB (min i.val 2) (z i) (z i') = true

instance (n : ℕ) : DecidablePred (GZ n) := fun z => by unfold GZ; infer_instance

/-- The lower right deficit is 2. -/
def LZ (n : ℕ) (z : Fin n → Fin 3 → Fin 3) : Prop :=
  ∀ i j, i.val + 1 = n → j.val + 1 = 3 → (z i j : ℕ) = 2

instance (n : ℕ) : DecidablePred (LZ n) := fun z => by unfold LZ; infer_instance

theorem set_eq (n : ℕ) : {x : Fin n → Fin 3 → ℕ | good n x} =
    (fun z : Fin n → Fin 3 → Fin 3 => fun i => vals i.val (z i)) '' {z | GZ n z ∧ LZ n z} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_image]
  constructor
  · intro hx
    have hd : ∀ i j, x i j ≤ max i.val j.val := fun i j => le_dist hx (i.val + j.val) i j rfl
    have hw := hx.2.2.1
    have hq := hx.2.1
    let z : Fin n → Fin 3 → Fin 3 := fun i j =>
      ⟨max i.val j.val - x i j, by have := hd i j; have := (hw i j).1; omega⟩
    have hv : ∀ i, vals i.val (z i) = x i := fun i => by
      funext j
      simp only [vals, z]
      have := hd i j
      omega
    have hb : ∀ i j, ((z i j : Fin 3) : ℕ) ≤ max i.val j.val := fun i j => by
      simp only [z]
      omega
    rw [good_iff] at hx
    refine ⟨z, ⟨⟨fun i => ?_, fun i i' hi => ?_⟩, fun i j hi hj => ?_⟩, funext hv⟩
    · rw [← rowA]
      exact ⟨by rw [hv]; exact hx.1.1 i, hb i⟩
    · have e : vals i'.val (z i') = vals (i.val + 1) (z i') := by rw [hi]
      rw [← rowB i.val (z i) (z i') (hb i) (fun j => by rw [← hi]; exact hb i' j), ← e, hv, hv]
      exact hx.1.2 i i' hi
    · have := hq i j hi hj
      have := hd i j
      simp only [z]
      omega
  · rintro ⟨z, ⟨hz, hl⟩, rfl⟩
    rw [good_iff]
    refine ⟨⟨fun i => ((rowA _ _).2 (hz.1 i)).1, fun i i' hi => ?_⟩, fun i j hi hj => ?_⟩
    · have e : vals i'.val (z i') = vals (i.val + 1) (z i') := by rw [hi]
      show RB (vals i.val (z i)) (vals i'.val (z i'))
      rw [e, rowB i.val (z i) (z i') (bound_of_ZA (hz.1 i))
        (fun j => by rw [← hi]; exact bound_of_ZA (hz.1 i') j)]
      exact hz.2 i i' hi
    · have := hl i j hi hj
      have := bound_of_ZA (hz.1 i) j
      simp only [vals]
      omega

theorem injOn (n : ℕ) :
    Set.InjOn (fun z : Fin n → Fin 3 → Fin 3 => fun i => vals i.val (z i)) {z | GZ n z ∧ LZ n z} := by
  intro z hz z' hz' h
  funext i j
  have e := congrFun (congrFun h i) j
  simp only [vals] at e
  have b := bound_of_ZA (hz.1.1 i) j
  have b' := bound_of_ZA (hz'.1.1 i) j
  exact Fin.ext (by omega)

theorem a_eq (n : ℕ) :
    a n = (Finset.univ.filter fun z : Fin n → Fin 3 → Fin 3 => GZ n z ∧ LZ n z).card := by
  unfold a
  rw [set_eq, Set.ncard_image_of_injOn (injOn n), ← Set.ncard_coe_finset]
  congr 1
  ext z
  simp

theorem GZ_snoc (m : ℕ) (y : Fin (m + 1) → Fin 3 → Fin 3) (t : Fin 3 → Fin 3) :
    GZ (m + 1 + 1) (Fin.snoc y t) ↔
      GZ (m + 1) y ∧ ZA (min (m + 1) 2) t = true ∧ ZB (min m 2) (y (Fin.last m)) t = true := by
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

theorem GZ_one (z : Fin (0 + 1) → Fin 3 → Fin 3) : GZ (0 + 1) z ↔ ZA 0 (z 0) = true := by
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

theorem sum_snoc (m : ℕ) (f : (Fin (m + 1 + 1) → Fin 3 → Fin 3) → ℕ) :
    ∑ z : Fin (m + 1 + 1) → Fin 3 → Fin 3, f z =
      ∑ t : Fin 3 → Fin 3, ∑ y : Fin (m + 1) → Fin 3 → Fin 3, f (Fin.snoc y t) := by
  rw [← (Fin.snocEquiv fun _ => Fin 3 → Fin 3).sum_comp, Fintype.sum_prod_type]
  rfl

/-- The number of deficit arrays with m + 1 rows whose last row is r. -/
def Cnt (m : ℕ) (r : Fin 3 → Fin 3) : ℕ :=
  ∑ z : Fin (m + 1) → Fin 3 → Fin 3, if GZ (m + 1) z ∧ z (Fin.last m) = r then 1 else 0

theorem LZ_iff (n : ℕ) (z : Fin (n + 1) → Fin 3 → Fin 3) :
    LZ (n + 1) z ↔ (z (Fin.last n) 2 : ℕ) = 2 := by
  constructor
  · intro h
    exact h _ _ (by simp) rfl
  · intro h i j hi hj
    have e1 : i = Fin.last n := Fin.ext (by simp only [Fin.val_last]; omega)
    have e2 : j = 2 := Fin.ext (by have : ((2 : Fin 3) : ℕ) = 2 := rfl; omega)
    rw [e1, e2]
    exact h

theorem a_succ (n : ℕ) : a (n + 1) = ∑ r : Fin 3 → Fin 3,
    if (r 2 : ℕ) = 2 then Cnt n r else 0 := by
  rw [a_eq, Finset.card_filter]
  simp only [LZ_iff]
  have h : ∀ r : Fin 3 → Fin 3, (if (r 2 : ℕ) = 2 then Cnt n r else 0) =
      ∑ z : Fin (n + 1) → Fin 3 → Fin 3,
        if (r 2 : ℕ) = 2 ∧ GZ (n + 1) z ∧ z (Fin.last n) = r then 1 else 0 := by
    intro r
    unfold Cnt
    by_cases hr : (r 2 : ℕ) = 2
    · rw [if_pos hr]
      refine Finset.sum_congr rfl (fun z _ => ?_)
      simp only [hr, true_and]
    · rw [if_neg hr]
      symm
      refine Finset.sum_eq_zero (fun z _ => ?_)
      simp only [hr, false_and, if_false]
  rw [Finset.sum_congr rfl (fun r _ => h r), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  rw [Finset.sum_eq_single (z (Fin.last n))]
  · by_cases h1 : GZ (n + 1) z <;> by_cases h2 : (z (Fin.last n) 2 : ℕ) = 2 <;> simp [h1, h2]
  · intro r _ hr
    simp [Ne.symm hr]
  · simp

theorem Cnt_zero (r : Fin 3 → Fin 3) : Cnt 0 r = if ZA 0 r = true then 1 else 0 := by
  unfold Cnt
  rw [Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin 3 → Fin 3)) _
    (fun t => if ZA 0 t = true ∧ t = r then 1 else 0) (fun z => by
      simp only [Equiv.funUnique_apply, GZ_one]
      rfl)]
  rw [Finset.sum_eq_single r]
  · simp
  · intro t _ ht
    simp [ht]
  · simp

theorem Cnt_succ (m : ℕ) (r : Fin 3 → Fin 3) :
    Cnt (m + 1) r = ∑ p : Fin 3 → Fin 3,
      if (ZA (min (m + 1) 2) r && ZB (min m 2) p r) = true then Cnt m p else 0 := by
  have lhs : Cnt (m + 1) r = ∑ y : Fin (m + 1) → Fin 3 → Fin 3,
      if GZ (m + 1) y ∧ ZA (min (m + 1) 2) r = true ∧ ZB (min m 2) (y (Fin.last m)) r = true
      then 1 else 0 := by
    unfold Cnt
    rw [sum_snoc, Finset.sum_eq_single r]
    · refine Finset.sum_congr rfl (fun y _ => ?_)
      simp only [GZ_snoc, Fin.snoc_last, and_true]
    · intro t _ ht
      refine Finset.sum_eq_zero (fun y _ => ?_)
      simp [Fin.snoc_last, ht]
    · simp
  have rhs : ∀ p : Fin 3 → Fin 3,
      (if (ZA (min (m + 1) 2) r && ZB (min m 2) p r) = true then Cnt m p else 0) =
        ∑ y : Fin (m + 1) → Fin 3 → Fin 3,
          if (ZA (min (m + 1) 2) r && ZB (min m 2) p r) = true ∧ GZ (m + 1) y ∧
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
    by_cases h1 : GZ (m + 1) y <;> by_cases h2 : ZA (min (m + 1) 2) r = true <;>
      by_cases h3 : ZB (min m 2) (y (Fin.last m)) r = true <;> simp [h1, h2, h3]
  · intro p _ hp
    simp [Ne.symm hp]
  · simp

/-- From row 2 on the transfer does not depend on the row. -/
theorem Cnt_hom (m : ℕ) (hm : 2 ≤ m) (r : Fin 3 → Fin 3) :
    Cnt (m + 1) r = ∑ p : Fin 3 → Fin 3,
      if (ZA 2 r && ZB 2 p r) = true then Cnt m p else 0 := by
  rw [Cnt_succ, Nat.min_eq_right (by omega : 2 ≤ m + 1), Nat.min_eq_right hm]

theorem ZB_down {c : ℕ} {p r : Fin 3 → Fin 3} (h : ZB c p r = true) (j : Fin 3) :
    (r j : ℕ) = p j + (if j.val ≤ c then 1 else 0) ∨
      (r j : ℕ) + 1 = p j + (if j.val ≤ c then 1 else 0) := by
  exact ((ZB_iff c p r).1 h).1 j

/-- The candidate row above r for the choice e: the deficit r j + e j - 1 where the step down
raises the king-move distance (j ≤ c) and r j + e j elsewhere. -/
def pred (c : ℕ) (r : Fin 3 → Fin 3) (e : Fin 3 → Fin 2) : Fin 3 → Fin 3 :=
  fun j => ⟨min ((r j : ℕ) + e j - (if j.val ≤ c then 1 else 0)) 2, by omega⟩

/-- The choice e gives a candidate row above r without cutting off any value. -/
def valid (c : ℕ) (r : Fin 3 → Fin 3) (e : Fin 3 → Fin 2) : Bool :=
  (List.finRange 3).all (fun j => decide ((if j.val ≤ c then 1 else 0) ≤ (r j : ℕ) + e j ∧
    (r j : ℕ) + e j - (if j.val ≤ c then 1 else 0) ≤ 2))

theorem valid_iff (c : ℕ) (r : Fin 3 → Fin 3) (e : Fin 3 → Fin 2) : valid c r e = true ↔
    ∀ j : Fin 3, (if j.val ≤ c then 1 else 0) ≤ (r j : ℕ) + e j ∧
      (r j : ℕ) + e j - (if j.val ≤ c then 1 else 0) ≤ 2 := by
  simp only [valid, List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq]

/-- The rows above r that a step down allows are the candidates `pred c r e`. -/
theorem sum_pred (c : ℕ) (r : Fin 3 → Fin 3) (f : (Fin 3 → Fin 3) → ℕ) :
    ∑ e : Fin 3 → Fin 2,
        (if (valid c r e && ZB c (pred c r e) r) = true then f (pred c r e) else 0) =
      ∑ p : Fin 3 → Fin 3, (if ZB c p r = true then f p else 0) := by
  apply Finset.sum_bij_ne_zero (fun e _ _ => pred c r e)
  · intro e _ _
    exact Finset.mem_univ _
  · intro e₁ _ h₁ e₂ _ h₂ he
    have v₁ : valid c r e₁ = true := by
      by_contra hv
      exact h₁ (by simp [hv])
    have v₂ : valid c r e₂ = true := by
      by_contra hv
      exact h₂ (by simp [hv])
    rw [valid_iff] at v₁ v₂
    funext j
    have hj := congrArg Fin.val (congrFun he j)
    simp only [pred] at hj
    have a1 := v₁ j
    have a2 := v₂ j
    have := (e₁ j).isLt
    have := (e₂ j).isLt
    apply Fin.ext
    split_ifs at a1 a2 hj <;> omega
  · intro p _ hp
    have hz : ZB c p r = true := by
      by_contra h
      exact hp (by simp [h])
    let e : Fin 3 → Fin 2 := fun j =>
      ⟨(p j : ℕ) + (if j.val ≤ c then 1 else 0) - r j, by
        have := ZB_down hz j
        split_ifs at this ⊢ <;> omega⟩
    have hv : valid c r e = true := by
      rw [valid_iff]
      intro j
      have hd := ZB_down hz j
      have := (p j).isLt
      simp only [e]
      split_ifs at hd ⊢ <;> omega
    have hpe : pred c r e = p := by
      funext j
      apply Fin.ext
      have hd := ZB_down hz j
      have := (p j).isLt
      simp only [pred, e]
      split_ifs at hd ⊢ <;> omega
    refine ⟨e, Finset.mem_univ _, ?_, hpe⟩
    rw [hpe]
    simpa [hv, hz] using hp
  · intro e _ h
    have v : valid c r e = true := by
      by_contra hv
      exact h (by simp [hv])
    simp [v]

/-- The contribution of the candidate `pred c r e` to the count of r. -/
def spTerm (c : ℕ) (f : (Fin 3 → Fin 3) → ℕ) (r : Fin 3 → Fin 3) (e : Fin 3 → Fin 2) : ℕ :=
  if (valid c r e && ZB c (pred c r e) r) = true then f (pred c r e) else 0

/-- The transfer with the rows above r restricted to the candidates. -/
theorem Cnt_sparse (m : ℕ) (r : Fin 3 → Fin 3) :
    Cnt (m + 1) r = if ZA (min (m + 1) 2) r = true then
      ∑ e : Fin 3 → Fin 2, spTerm (min m 2) (Cnt m) r e else 0 := by
  rw [Cnt_succ]
  split_ifs with h
  · simp only [spTerm]
    rw [sum_pred]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    simp [h]
  · refine Finset.sum_eq_zero (fun p _ => ?_)
    simp [h]

/-- The row with base-b digits of n, column j holding the digit of b ^ j (the kernel evaluates it by
arithmetic on numerals). -/
def dig (b : ℕ) (hb : 0 < b) (n : ℕ) : Fin 3 → Fin b := fun j => ⟨n / b ^ j.val % b, Nat.mod_lt _ hb⟩

theorem sum_dig (b : ℕ) (hb : 0 < b) (g : (Fin 3 → Fin b) → ℕ) :
    ∑ f, g f = ∑ n ∈ Finset.range (b ^ 3), g (dig b hb n) := by
  rw [← (finFunctionFinEquiv (m := b) (n := 3)).symm.sum_comp]
  exact Fin.sum_univ_eq_sum_range (fun n => g (dig b hb n)) _

/-- The position of a row of deficits in the tables. -/
def code (r : Fin 3 → Fin 3) : ℕ := (r 0 : ℕ) + (r 1 : ℕ) * 3 + (r 2 : ℕ) * 9

theorem code_lt (r : Fin 3 → Fin 3) : code r < 3 ^ 3 := by
  simp only [code]
  have := (r 0).isLt
  have := (r 1).isLt
  have := (r 2).isLt
  omega

theorem dig_code (r : Fin 3 → Fin 3) : dig 3 (by norm_num) (code r) = r := by
  funext j
  apply Fin.ext
  simp only [dig, code]
  have := (r 0).isLt
  have := (r 1).isLt
  have := (r 2).isLt
  fin_cases j <;> simp <;> omega

/-- The sum of `Cnt_sparse` over the choices e, by their codes. -/
def spSum (c : ℕ) (f : (Fin 3 → Fin 3) → ℕ) (r : Fin 3 → Fin 3) : ℕ :=
  ∑ n ∈ Finset.range (2 ^ 3), spTerm c f r (dig 2 (by norm_num) n)

theorem Cnt_sp (m : ℕ) (r : Fin 3 → Fin 3) :
    Cnt (m + 1) r = if ZA (min (m + 1) 2) r = true then spSum (min m 2) (Cnt m) r else 0 := by
  rw [Cnt_sparse, sum_dig 2 (by norm_num)]
  rfl

/-- The table of Cnt 0: the 11-bit digit at position `code r` is Cnt 0 r. -/
def t0 (r : Fin 3 → Fin 3) : ℕ :=
  3450873173395281893717377931143957244096923326800721386000918754885633 >>> (11 * code r) % 2048

/-- The table of Cnt 1: the 11-bit digit at position `code r` is Cnt 1 r. -/
def t1 (r : Fin 3 → Fin 3) : ℕ :=
  7067388259113537318333190002993974808512362334763813013824573283978186754 >>> (11 * code r) % 2048

/-- The table of Cnt 2: the 11-bit digit at position `code r` is Cnt 2 r. -/
def t2 (r : Fin 3 → Fin 3) : ℕ :=
  124330809102446660538845562037293688312943655152799700154927445313599028846678322980869 >>> (11 * code r) % 2048

/-- The table of Cnt 3: the 11-bit digit at position `code r` is Cnt 3 r. -/
def t3 (r : Fin 3 → Fin 3) : ℕ :=
  2362285372946486550238065678703283773354640115978302177714823011587787308892238332831749 >>> (11 * code r) % 2048

/-- The table of Cnt 4: the 11-bit digit at position `code r` is Cnt 4 r. -/
def t4 (r : Fin 3 → Fin 3) : ℕ :=
  12681742528449559374962247327757270263750333870699440207012679702857374983919864454850565 >>> (11 * code r) % 2048

/-- The table of Cnt 5: the 11-bit digit at position `code r` is Cnt 5 r. -/
def t5 (r : Fin 3 → Fin 3) : ℕ :=
  32699002793943471721716382815674655454963384233516598463238534422694579247907170401921029 >>> (11 * code r) % 2048

/-- The table of Cnt 6: the 11-bit digit at position `code r` is Cnt 6 r. -/
def t6 (r : Fin 3 → Fin 3) : ℕ :=
  62662727787633116911578163266528457448185557612280711068273668680394973452145143859652613 >>> (11 * code r) % 2048

/-- The table of Cnt 7: the 11-bit digit at position `code r` is Cnt 7 r. -/
def t7 (r : Fin 3 → Fin 3) : ℕ :=
  102572917509518494944547588680318676243416854006991778022118082475958557596633784828045317 >>> (11 * code r) % 2048

lemma Cnt0 (r : Fin 3 → Fin 3) : Cnt 0 r = t0 r := by
  have h : ∀ c0 c1 c2 : Fin 3,
      (if ZA 0 (dig 3 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 3 + (c2 : ℕ) * 9)) = true then 1 else 0) = t0 (dig 3 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 3 + (c2 : ℕ) * 9)) := by
    decide +kernel
  rw [Cnt_zero, ← dig_code r]
  exact h (r 0) (r 1) (r 2)

lemma Cnt1 (r : Fin 3 → Fin 3) : Cnt 1 r = t1 r := by
  have hf : Cnt 0 = t0 := funext Cnt0
  have h : ∀ c0 c1 c2 : Fin 3,
      (if ZA (min 1 2) (dig 3 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 3 + (c2 : ℕ) * 9)) = true then spSum (min 0 2) t0 (dig 3 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 3 + (c2 : ℕ) * 9)) else 0) =
        t1 (dig 3 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 3 + (c2 : ℕ) * 9)) := by
    decide +kernel
  rw [Cnt_sp, hf, ← dig_code r]
  exact h (r 0) (r 1) (r 2)

lemma Cnt2 (r : Fin 3 → Fin 3) : Cnt 2 r = t2 r := by
  have hf : Cnt 1 = t1 := funext Cnt1
  have h : ∀ c0 c1 c2 : Fin 3,
      (if ZA (min 2 2) (dig 3 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 3 + (c2 : ℕ) * 9)) = true then spSum (min 1 2) t1 (dig 3 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 3 + (c2 : ℕ) * 9)) else 0) =
        t2 (dig 3 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 3 + (c2 : ℕ) * 9)) := by
    decide +kernel
  rw [Cnt_sp, hf, ← dig_code r]
  exact h (r 0) (r 1) (r 2)

lemma Cnt3 (r : Fin 3 → Fin 3) : Cnt 3 r = t3 r := by
  have hf : Cnt 2 = t2 := funext Cnt2
  have h : ∀ c0 c1 c2 : Fin 3,
      (if ZA (min 3 2) (dig 3 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 3 + (c2 : ℕ) * 9)) = true then spSum (min 2 2) t2 (dig 3 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 3 + (c2 : ℕ) * 9)) else 0) =
        t3 (dig 3 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 3 + (c2 : ℕ) * 9)) := by
    decide +kernel
  rw [Cnt_sp, hf, ← dig_code r]
  exact h (r 0) (r 1) (r 2)

lemma Cnt4 (r : Fin 3 → Fin 3) : Cnt 4 r = t4 r := by
  have hf : Cnt 3 = t3 := funext Cnt3
  have h : ∀ c0 c1 c2 : Fin 3,
      (if ZA (min 4 2) (dig 3 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 3 + (c2 : ℕ) * 9)) = true then spSum (min 3 2) t3 (dig 3 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 3 + (c2 : ℕ) * 9)) else 0) =
        t4 (dig 3 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 3 + (c2 : ℕ) * 9)) := by
    decide +kernel
  rw [Cnt_sp, hf, ← dig_code r]
  exact h (r 0) (r 1) (r 2)

lemma Cnt5 (r : Fin 3 → Fin 3) : Cnt 5 r = t5 r := by
  have hf : Cnt 4 = t4 := funext Cnt4
  have h : ∀ c0 c1 c2 : Fin 3,
      (if ZA (min 5 2) (dig 3 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 3 + (c2 : ℕ) * 9)) = true then spSum (min 4 2) t4 (dig 3 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 3 + (c2 : ℕ) * 9)) else 0) =
        t5 (dig 3 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 3 + (c2 : ℕ) * 9)) := by
    decide +kernel
  rw [Cnt_sp, hf, ← dig_code r]
  exact h (r 0) (r 1) (r 2)

lemma Cnt6 (r : Fin 3 → Fin 3) : Cnt 6 r = t6 r := by
  have hf : Cnt 5 = t5 := funext Cnt5
  have h : ∀ c0 c1 c2 : Fin 3,
      (if ZA (min 6 2) (dig 3 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 3 + (c2 : ℕ) * 9)) = true then spSum (min 5 2) t5 (dig 3 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 3 + (c2 : ℕ) * 9)) else 0) =
        t6 (dig 3 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 3 + (c2 : ℕ) * 9)) := by
    decide +kernel
  rw [Cnt_sp, hf, ← dig_code r]
  exact h (r 0) (r 1) (r 2)

lemma Cnt7 (r : Fin 3 → Fin 3) : Cnt 7 r = t7 r := by
  have hf : Cnt 6 = t6 := funext Cnt6
  have h : ∀ c0 c1 c2 : Fin 3,
      (if ZA (min 7 2) (dig 3 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 3 + (c2 : ℕ) * 9)) = true then spSum (min 6 2) t6 (dig 3 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 3 + (c2 : ℕ) * 9)) else 0) =
        t7 (dig 3 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 3 + (c2 : ℕ) * 9)) := by
    decide +kernel
  rw [Cnt_sp, hf, ← dig_code r]
  exact h (r 0) (r 1) (r 2)

/-- The difference equation of order 3 on every deficit row, from m = 4 on. -/
theorem Cnt_rec (m : ℕ) : ∀ r : Fin 3 → Fin 3, (Cnt (m + 7) r : ℤ) = 3 * Cnt (m + 6) r - 3 * Cnt (m + 5) r + Cnt (m + 4) r := by
  induction m with
  | zero =>
    intro r
    simp only [Nat.zero_add, Cnt4, Cnt5, Cnt6, Cnt7]
    have h : ∀ c0 c1 c2 : Fin 3,
        (t7 (dig 3 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 3 + (c2 : ℕ) * 9)) : ℤ) = 3 * t6 (dig 3 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 3 + (c2 : ℕ) * 9)) - 3 * t5 (dig 3 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 3 + (c2 : ℕ) * 9)) + t4 (dig 3 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 3 + (c2 : ℕ) * 9)) := by
      decide +kernel
    rw [← dig_code r]
    exact h (r 0) (r 1) (r 2)
  | succ m ih =>
    intro r
    rw [show m + 1 + 7 = m + 7 + 1 by omega, show m + 1 + 6 = m + 6 + 1 by omega, show m + 1 + 5 = m + 5 + 1 by omega, show m + 1 + 4 = m + 4 + 1 by omega,
      Cnt_hom (m + 7) (by omega), Cnt_hom (m + 6) (by omega), Cnt_hom (m + 5) (by omega), Cnt_hom (m + 4) (by omega)]
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    split_ifs
    · exact ih p
    · simp

/-- The recurrence of a, for n >= 8. -/
theorem a_rec (m : ℕ) : (a (m + 7 + 1) : ℤ) = 3 * a (m + 6 + 1) - 3 * a (m + 5 + 1) + a (m + 4 + 1) := by
  rw [a_succ, a_succ, a_succ, a_succ]
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  split_ifs
  · exact Cnt_rec m r
  · simp

lemma v1 : a 1 = 1 := by
  rw [a_succ, sum_dig 3 (by norm_num)]
  simp only [Cnt0]
  decide +kernel

lemma v2 : a 2 = 1 := by
  rw [a_succ, sum_dig 3 (by norm_num)]
  simp only [Cnt1]
  decide +kernel

lemma v3 : a 3 = 1 := by
  rw [a_succ, sum_dig 3 (by norm_num)]
  simp only [Cnt2]
  decide +kernel

lemma v4 : a 4 = 19 := by
  rw [a_succ, sum_dig 3 (by norm_num)]
  simp only [Cnt3]
  decide +kernel

lemma v5 : a 5 = 102 := by
  rw [a_succ, sum_dig 3 (by norm_num)]
  simp only [Cnt4]
  decide +kernel

lemma v6 : a 6 = 263 := by
  rw [a_succ, sum_dig 3 (by norm_num)]
  simp only [Cnt5]
  decide +kernel

lemma v7 : a 7 = 504 := by
  rw [a_succ, sum_dig 3 (by norm_num)]
  simp only [Cnt6]
  decide +kernel

/-- Barker's recurrence, for n > 7. -/
theorem recurrence (n : ℕ) (hn : 7 < n) : (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 + 3 + 1 := ⟨n - 8, by omega⟩
  rw [show m + 4 + 3 + 1 - 1 = m + 6 + 1 by omega, show m + 4 + 3 + 1 - 2 = m + 5 + 1 by omega, show m + 4 + 3 + 1 - 3 = m + 4 + 1 by omega]
  rw [show m + 4 + 3 + 1 = m + 7 + 1 by omega]
  exact a_rec m

/-- Barker's g.f., as A(x) (1 - x)^3 = its numerator in Z[[x]]. -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 3 =
    X * (1 - 2 * X + X ^ 2 + 18 * X ^ 3 + 47 * X ^ 4 + 13 * X ^ 5 + 2 * X ^ 6) := by
  set A : ℤ⟦X⟧ := PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) with hA
  have e1 : A * (1 - X) ^ 3 = A - C 3 * (A * X ^ 1) + C 3 * (A * X ^ 2) - A * X ^ 3 := by
    simp only [map_ofNat]; ring
  have e2 : (X * (1 - 2 * X + X ^ 2 + 18 * X ^ 3 + 47 * X ^ 4 + 13 * X ^ 5 + 2 * X ^ 6) : ℤ⟦X⟧) =
      X ^ 1 - X ^ 2 * C 2 + X ^ 3 + X ^ 4 * C 18 + X ^ 5 * C 47 + X ^ 6 * C 13 + X ^ 7 * C 2 := by
    simp only [map_ofNat]; ring
  rw [e1, e2]
  ext n
  have hc : ∀ k, coeff k A = if k = 0 then (0 : ℤ) else a k := fun k => by rw [hA, coeff_mk]
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_C, coeff_X_pow, coeff_mul_X_pow', hc]
  rcases Nat.lt_or_ge n 8 with hn | hn
  · interval_cases n <;> simp [v1, v2, v3, v4, v5, v6, v7]
  · obtain ⟨q, rfl⟩ : ∃ q, n = q + 8 := ⟨n - 8, by omega⟩
    have h := recurrence (q + 8) (by omega)
    simp only [show q + 8 - 1 = q + 7 by omega, show q + 8 - 2 = q + 6 by omega, show q + 8 - 3 = q + 5 by omega] at h ⊢
    simp only [ show ¬ q + 8 = 0 by omega, show 1 ≤ q + 8 by omega, show ¬ q + 7 = 0 by omega,
      show 2 ≤ q + 8 by omega, show ¬ q + 6 = 0 by omega, show 3 ≤ q + 8 by omega,
      show ¬ q + 5 = 0 by omega, show ¬ q + 8 = 1 by omega, show ¬ q + 8 = 2 by omega,
      show ¬ q + 8 = 3 by omega, show ¬ q + 8 = 4 by omega, show ¬ q + 8 = 5 by omega,
      show ¬ q + 8 = 6 by omega, show ¬ q + 8 = 7 by omega, if_true, if_false]
    rw [h]
    ring

/-- Controls: the entry's data a(1..41). -/
theorem controls : a 1 = 1 ∧ a 2 = 1 ∧ a 3 = 1 ∧ a 4 = 19 ∧ a 5 = 102 ∧ a 6 = 263 ∧ a 7 = 504 ∧
    a 8 = 825 ∧ a 9 = 1226 ∧ a 10 = 1707 ∧ a 11 = 2268 ∧ a 12 = 2909 ∧ a 13 = 3630 ∧ a 14 = 4431 ∧
    a 15 = 5312 ∧ a 16 = 6273 ∧ a 17 = 7314 ∧ a 18 = 8435 ∧ a 19 = 9636 ∧ a 20 = 10917 ∧
    a 21 = 12278 ∧ a 22 = 13719 ∧ a 23 = 15240 ∧ a 24 = 16841 ∧ a 25 = 18522 ∧ a 26 = 20283 ∧
    a 27 = 22124 ∧ a 28 = 24045 ∧ a 29 = 26046 ∧ a 30 = 28127 ∧ a 31 = 30288 ∧ a 32 = 32529 ∧
    a 33 = 34850 ∧ a 34 = 37251 ∧ a 35 = 39732 ∧ a 36 = 42293 ∧ a 37 = 44934 ∧ a 38 = 47655 ∧
    a 39 = 50456 ∧ a 40 = 53337 ∧ a 41 = 56298 := by
  have v8 : a 8 = 825 := by
    have h : (a 8 : ℤ) = 3 * a 7 - 3 * a 6 + a 5 := a_rec 0
    rw [v7, v6, v5] at h
    omega
  have v9 : a 9 = 1226 := by
    have h : (a 9 : ℤ) = 3 * a 8 - 3 * a 7 + a 6 := a_rec 1
    rw [v8, v7, v6] at h
    omega
  have v10 : a 10 = 1707 := by
    have h : (a 10 : ℤ) = 3 * a 9 - 3 * a 8 + a 7 := a_rec 2
    rw [v9, v8, v7] at h
    omega
  have v11 : a 11 = 2268 := by
    have h : (a 11 : ℤ) = 3 * a 10 - 3 * a 9 + a 8 := a_rec 3
    rw [v10, v9, v8] at h
    omega
  have v12 : a 12 = 2909 := by
    have h : (a 12 : ℤ) = 3 * a 11 - 3 * a 10 + a 9 := a_rec 4
    rw [v11, v10, v9] at h
    omega
  have v13 : a 13 = 3630 := by
    have h : (a 13 : ℤ) = 3 * a 12 - 3 * a 11 + a 10 := a_rec 5
    rw [v12, v11, v10] at h
    omega
  have v14 : a 14 = 4431 := by
    have h : (a 14 : ℤ) = 3 * a 13 - 3 * a 12 + a 11 := a_rec 6
    rw [v13, v12, v11] at h
    omega
  have v15 : a 15 = 5312 := by
    have h : (a 15 : ℤ) = 3 * a 14 - 3 * a 13 + a 12 := a_rec 7
    rw [v14, v13, v12] at h
    omega
  have v16 : a 16 = 6273 := by
    have h : (a 16 : ℤ) = 3 * a 15 - 3 * a 14 + a 13 := a_rec 8
    rw [v15, v14, v13] at h
    omega
  have v17 : a 17 = 7314 := by
    have h : (a 17 : ℤ) = 3 * a 16 - 3 * a 15 + a 14 := a_rec 9
    rw [v16, v15, v14] at h
    omega
  have v18 : a 18 = 8435 := by
    have h : (a 18 : ℤ) = 3 * a 17 - 3 * a 16 + a 15 := a_rec 10
    rw [v17, v16, v15] at h
    omega
  have v19 : a 19 = 9636 := by
    have h : (a 19 : ℤ) = 3 * a 18 - 3 * a 17 + a 16 := a_rec 11
    rw [v18, v17, v16] at h
    omega
  have v20 : a 20 = 10917 := by
    have h : (a 20 : ℤ) = 3 * a 19 - 3 * a 18 + a 17 := a_rec 12
    rw [v19, v18, v17] at h
    omega
  have v21 : a 21 = 12278 := by
    have h : (a 21 : ℤ) = 3 * a 20 - 3 * a 19 + a 18 := a_rec 13
    rw [v20, v19, v18] at h
    omega
  have v22 : a 22 = 13719 := by
    have h : (a 22 : ℤ) = 3 * a 21 - 3 * a 20 + a 19 := a_rec 14
    rw [v21, v20, v19] at h
    omega
  have v23 : a 23 = 15240 := by
    have h : (a 23 : ℤ) = 3 * a 22 - 3 * a 21 + a 20 := a_rec 15
    rw [v22, v21, v20] at h
    omega
  have v24 : a 24 = 16841 := by
    have h : (a 24 : ℤ) = 3 * a 23 - 3 * a 22 + a 21 := a_rec 16
    rw [v23, v22, v21] at h
    omega
  have v25 : a 25 = 18522 := by
    have h : (a 25 : ℤ) = 3 * a 24 - 3 * a 23 + a 22 := a_rec 17
    rw [v24, v23, v22] at h
    omega
  have v26 : a 26 = 20283 := by
    have h : (a 26 : ℤ) = 3 * a 25 - 3 * a 24 + a 23 := a_rec 18
    rw [v25, v24, v23] at h
    omega
  have v27 : a 27 = 22124 := by
    have h : (a 27 : ℤ) = 3 * a 26 - 3 * a 25 + a 24 := a_rec 19
    rw [v26, v25, v24] at h
    omega
  have v28 : a 28 = 24045 := by
    have h : (a 28 : ℤ) = 3 * a 27 - 3 * a 26 + a 25 := a_rec 20
    rw [v27, v26, v25] at h
    omega
  have v29 : a 29 = 26046 := by
    have h : (a 29 : ℤ) = 3 * a 28 - 3 * a 27 + a 26 := a_rec 21
    rw [v28, v27, v26] at h
    omega
  have v30 : a 30 = 28127 := by
    have h : (a 30 : ℤ) = 3 * a 29 - 3 * a 28 + a 27 := a_rec 22
    rw [v29, v28, v27] at h
    omega
  have v31 : a 31 = 30288 := by
    have h : (a 31 : ℤ) = 3 * a 30 - 3 * a 29 + a 28 := a_rec 23
    rw [v30, v29, v28] at h
    omega
  have v32 : a 32 = 32529 := by
    have h : (a 32 : ℤ) = 3 * a 31 - 3 * a 30 + a 29 := a_rec 24
    rw [v31, v30, v29] at h
    omega
  have v33 : a 33 = 34850 := by
    have h : (a 33 : ℤ) = 3 * a 32 - 3 * a 31 + a 30 := a_rec 25
    rw [v32, v31, v30] at h
    omega
  have v34 : a 34 = 37251 := by
    have h : (a 34 : ℤ) = 3 * a 33 - 3 * a 32 + a 31 := a_rec 26
    rw [v33, v32, v31] at h
    omega
  have v35 : a 35 = 39732 := by
    have h : (a 35 : ℤ) = 3 * a 34 - 3 * a 33 + a 32 := a_rec 27
    rw [v34, v33, v32] at h
    omega
  have v36 : a 36 = 42293 := by
    have h : (a 36 : ℤ) = 3 * a 35 - 3 * a 34 + a 33 := a_rec 28
    rw [v35, v34, v33] at h
    omega
  have v37 : a 37 = 44934 := by
    have h : (a 37 : ℤ) = 3 * a 36 - 3 * a 35 + a 34 := a_rec 29
    rw [v36, v35, v34] at h
    omega
  have v38 : a 38 = 47655 := by
    have h : (a 38 : ℤ) = 3 * a 37 - 3 * a 36 + a 35 := a_rec 30
    rw [v37, v36, v35] at h
    omega
  have v39 : a 39 = 50456 := by
    have h : (a 39 : ℤ) = 3 * a 38 - 3 * a 37 + a 36 := a_rec 31
    rw [v38, v37, v36] at h
    omega
  have v40 : a 40 = 53337 := by
    have h : (a 40 : ℤ) = 3 * a 39 - 3 * a 38 + a 37 := a_rec 32
    rw [v39, v38, v37] at h
    omega
  have v41 : a 41 = 56298 := by
    have h : (a 41 : ℤ) = 3 * a 40 - 3 * a 39 + a 38 := a_rec 33
    rw [v40, v39, v38] at h
    omega
  exact ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28, v29, v30, v31, v32, v33, v34, v35, v36, v37, v38, v39, v40, v41⟩

/-- Both of Barker's conjectures. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 3 =
      X * (1 - 2 * X + X ^ 2 + 18 * X ^ 3 + 47 * X ^ 4 + 13 * X ^ 5 + 2 * X ^ 6) ∧
    ∀ n : ℕ, 7 < n → (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3) :=
  ⟨gf, recurrence⟩

end OMA.S_oeis_a253218

theorem OMA.solution : type_of% @OMA.S_oeis_a253218.main :=
  OMA.S_oeis_a253218.conjecture
