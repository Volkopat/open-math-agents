import OMAStatements.S_oeis_a253001

namespace OMA.S_oeis_a253001

open PowerSeries




/-- The conditions of the entry on one row v with row index i. -/
def RA (i : ℕ) (v : Fin 5 → ℕ) : Prop :=
  (∀ j : Fin 5, i = 0 → j.val = 0 → v j = 0) ∧
  (∀ j : Fin 5, max i j.val ≤ v j + 3 ∧ v j ≤ max i j.val + 3) ∧
  (∀ j j' : Fin 5, j'.val = j.val + 1 → step01 (v j) (v j'))

/-- The conditions of the entry between a row u and the row v below it. -/
def RB (u v : Fin 5 → ℕ) : Prop :=
  (∀ j : Fin 5, step01 (u j) (v j)) ∧
  (∀ j j' : Fin 5, j'.val = j.val + 1 → step01 (u j) (v j'))

theorem good_iff (n : ℕ) (x : Fin n → Fin 5 → ℕ) :
    good n x ↔ ((∀ i : Fin n, RA i.val (x i)) ∧
      ∀ i i' : Fin n, i'.val = i.val + 1 → RB (x i) (x i')) ∧
      ∀ i j, i.val + 1 = n → j.val + 1 = 5 → x i j + 3 = max i.val j.val := by
  constructor
  · rintro ⟨h1, h6, h2, h3, h4, h5⟩
    exact ⟨⟨fun i => ⟨fun j hi hj => h1 i j hi hj, fun j => h2 i j, fun j j' hj => h3 i j j' hj⟩,
      fun i i' hi => ⟨fun j => h4 i i' j hi, fun j j' hj => h5 i i' j j' hi hj⟩⟩, h6⟩
  · rintro ⟨⟨hA, hB⟩, h6⟩
    exact ⟨fun i j hi hj => (hA i).1 j hi hj, h6, fun i j => (hA i).2.1 j,
      fun i j j' hj => (hA i).2.2 j j' hj, fun i i' j hi => (hB i i' hi).1 j,
      fun i i' j j' hi hj => (hB i i' hi).2 j j' hj⟩

/-- The steps from the upper left 0 keep every value at most its king-move distance. -/
theorem le_dist {n : ℕ} {x : Fin n → Fin 5 → ℕ} (h : good n x) :
    ∀ s, ∀ (i : Fin n) (j : Fin 5), i.val + j.val = s → x i j ≤ max i.val j.val := by
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
c = min i 4: every deficit is at most max i j, and every step right changes the value by 0 or 1. -/
def ZA (c : ℕ) (r : Fin 5 → Fin 4) : Bool :=
  (List.finRange 5).all (fun j => decide ((r j : ℕ) ≤ max c j.val)) &&
    (List.finRange 5).all (fun j => decide (∀ h : j.val + 1 < 5,
      (r ⟨j.val + 1, h⟩ : ℕ) = r j + (if c ≤ j.val then 1 else 0) ∨
        (r ⟨j.val + 1, h⟩ : ℕ) + 1 = r j + (if c ≤ j.val then 1 else 0)))

/-- The conditions between a row p of deficits at a row index i, with c = min i 4, and the row
r of deficits below it: every step down or diagonally down-right changes the value by 0 or 1. -/
def ZB (c : ℕ) (p r : Fin 5 → Fin 4) : Bool :=
  (List.finRange 5).all (fun j => decide ((r j : ℕ) = p j + (if j.val ≤ c then 1 else 0) ∨
      (r j : ℕ) + 1 = p j + (if j.val ≤ c then 1 else 0))) &&
    (List.finRange 5).all (fun j => decide (∀ h : j.val + 1 < 5,
      (r ⟨j.val + 1, h⟩ : ℕ) = p j ∨ (r ⟨j.val + 1, h⟩ : ℕ) = p j + 1))

theorem ZA_iff (c : ℕ) (r : Fin 5 → Fin 4) : ZA c r = true ↔
    (∀ j : Fin 5, (r j : ℕ) ≤ max c j.val) ∧
      ∀ j : Fin 5, ∀ h : j.val + 1 < 5,
        ((r ⟨j.val + 1, h⟩ : ℕ) = r j + (if c ≤ j.val then 1 else 0) ∨
          (r ⟨j.val + 1, h⟩ : ℕ) + 1 = r j + (if c ≤ j.val then 1 else 0)) := by
  simp only [ZA, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq]

theorem ZB_iff (c : ℕ) (p r : Fin 5 → Fin 4) : ZB c p r = true ↔
    (∀ j : Fin 5, (r j : ℕ) = p j + (if j.val ≤ c then 1 else 0) ∨
      (r j : ℕ) + 1 = p j + (if j.val ≤ c then 1 else 0)) ∧
      ∀ j : Fin 5, ∀ h : j.val + 1 < 5,
        ((r ⟨j.val + 1, h⟩ : ℕ) = p j ∨ (r ⟨j.val + 1, h⟩ : ℕ) = p j + 1) := by
  simp only [ZB, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq]

/-- The values of a row r of deficits at row index i. -/
def vals (i : ℕ) (r : Fin 5 → Fin 4) : Fin 5 → ℕ := fun j => max i j.val - r j

theorem rowA (i : ℕ) (r : Fin 5 → Fin 4) :
    (RA i (vals i r) ∧ ∀ j : Fin 5, (r j : ℕ) ≤ max i j.val) ↔ ZA (min i 4) r = true := by
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
    · have h : j.val + 1 < 5 := by have := j'.isLt; omega
      have hj' : j' = ⟨j.val + 1, h⟩ := Fin.ext hj
      rw [hj']
      show max i (j.val + 1) - (r ⟨j.val + 1, h⟩ : ℕ) = max i j.val - r j ∨
        max i (j.val + 1) - (r ⟨j.val + 1, h⟩ : ℕ) = max i j.val - r j + 1
      have e := hs j h
      have b1 := hb j
      have b2 : (r ⟨j.val + 1, h⟩ : ℕ) ≤ max (min i 4) (j.val + 1) := hb ⟨j.val + 1, h⟩
      have := (r j).isLt
      have := (r ⟨j.val + 1, h⟩).isLt
      split_ifs at e <;> omega
    · have := (r j).isLt
      have := hb j
      omega

theorem rowB (i : ℕ) (p r : Fin 5 → Fin 4) (hp : ∀ j : Fin 5, (p j : ℕ) ≤ max i j.val)
    (hr : ∀ j : Fin 5, (r j : ℕ) ≤ max (i + 1) j.val) :
    RB (vals i p) (vals (i + 1) r) ↔ ZB (min i 4) p r = true := by
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
    · have h : j.val + 1 < 5 := by have := j'.isLt; omega
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

theorem bound_of_ZA {i : ℕ} {r : Fin 5 → Fin 4} (h : ZA (min i 4) r = true) (j : Fin 5) :
    (r j : ℕ) ≤ max i j.val :=
  ((rowA i r).2 h).2 j

/-- The deficit form of the conditions on an array of deficits. -/
def GZ (n : ℕ) (z : Fin n → Fin 5 → Fin 4) : Prop :=
  (∀ i : Fin n, ZA (min i.val 4) (z i) = true) ∧
    ∀ i i' : Fin n, i'.val = i.val + 1 → ZB (min i.val 4) (z i) (z i') = true

instance (n : ℕ) : DecidablePred (GZ n) := fun z => by unfold GZ; infer_instance

/-- The lower right deficit is 3. -/
def LZ (n : ℕ) (z : Fin n → Fin 5 → Fin 4) : Prop :=
  ∀ i j, i.val + 1 = n → j.val + 1 = 5 → (z i j : ℕ) = 3

instance (n : ℕ) : DecidablePred (LZ n) := fun z => by unfold LZ; infer_instance

theorem set_eq (n : ℕ) : {x : Fin n → Fin 5 → ℕ | good n x} =
    (fun z : Fin n → Fin 5 → Fin 4 => fun i => vals i.val (z i)) '' {z | GZ n z ∧ LZ n z} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_image]
  constructor
  · intro hx
    have hd : ∀ i j, x i j ≤ max i.val j.val := fun i j => le_dist hx (i.val + j.val) i j rfl
    have hw := hx.2.2.1
    have hq := hx.2.1
    let z : Fin n → Fin 5 → Fin 4 := fun i j =>
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
    Set.InjOn (fun z : Fin n → Fin 5 → Fin 4 => fun i => vals i.val (z i)) {z | GZ n z ∧ LZ n z} := by
  intro z hz z' hz' h
  funext i j
  have e := congrFun (congrFun h i) j
  simp only [vals] at e
  have b := bound_of_ZA (hz.1.1 i) j
  have b' := bound_of_ZA (hz'.1.1 i) j
  exact Fin.ext (by omega)

theorem a_eq (n : ℕ) :
    a n = (Finset.univ.filter fun z : Fin n → Fin 5 → Fin 4 => GZ n z ∧ LZ n z).card := by
  unfold a
  rw [set_eq, Set.ncard_image_of_injOn (injOn n), ← Set.ncard_coe_finset]
  congr 1
  ext z
  simp

theorem GZ_snoc (m : ℕ) (y : Fin (m + 1) → Fin 5 → Fin 4) (t : Fin 5 → Fin 4) :
    GZ (m + 1 + 1) (Fin.snoc y t) ↔
      GZ (m + 1) y ∧ ZA (min (m + 1) 4) t = true ∧ ZB (min m 4) (y (Fin.last m)) t = true := by
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

theorem GZ_one (z : Fin (0 + 1) → Fin 5 → Fin 4) : GZ (0 + 1) z ↔ ZA 0 (z 0) = true := by
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

theorem sum_snoc (m : ℕ) (f : (Fin (m + 1 + 1) → Fin 5 → Fin 4) → ℕ) :
    ∑ z : Fin (m + 1 + 1) → Fin 5 → Fin 4, f z =
      ∑ t : Fin 5 → Fin 4, ∑ y : Fin (m + 1) → Fin 5 → Fin 4, f (Fin.snoc y t) := by
  rw [← (Fin.snocEquiv fun _ => Fin 5 → Fin 4).sum_comp, Fintype.sum_prod_type]
  rfl

/-- The number of deficit arrays with m + 1 rows whose last row is r. -/
def Cnt (m : ℕ) (r : Fin 5 → Fin 4) : ℕ :=
  ∑ z : Fin (m + 1) → Fin 5 → Fin 4, if GZ (m + 1) z ∧ z (Fin.last m) = r then 1 else 0

theorem LZ_iff (n : ℕ) (z : Fin (n + 1) → Fin 5 → Fin 4) :
    LZ (n + 1) z ↔ (z (Fin.last n) 4 : ℕ) = 3 := by
  constructor
  · intro h
    exact h _ _ (by simp) rfl
  · intro h i j hi hj
    have e1 : i = Fin.last n := Fin.ext (by simp only [Fin.val_last]; omega)
    have e2 : j = 4 := Fin.ext (by have : ((4 : Fin 5) : ℕ) = 4 := rfl; omega)
    rw [e1, e2]
    exact h

theorem a_succ (n : ℕ) : a (n + 1) = ∑ r : Fin 5 → Fin 4,
    if (r 4 : ℕ) = 3 then Cnt n r else 0 := by
  rw [a_eq, Finset.card_filter]
  simp only [LZ_iff]
  have h : ∀ r : Fin 5 → Fin 4, (if (r 4 : ℕ) = 3 then Cnt n r else 0) =
      ∑ z : Fin (n + 1) → Fin 5 → Fin 4,
        if (r 4 : ℕ) = 3 ∧ GZ (n + 1) z ∧ z (Fin.last n) = r then 1 else 0 := by
    intro r
    unfold Cnt
    by_cases hr : (r 4 : ℕ) = 3
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
  · by_cases h1 : GZ (n + 1) z <;> by_cases h2 : (z (Fin.last n) 4 : ℕ) = 3 <;> simp [h1, h2]
  · intro r _ hr
    simp [Ne.symm hr]
  · simp

theorem Cnt_zero (r : Fin 5 → Fin 4) : Cnt 0 r = if ZA 0 r = true then 1 else 0 := by
  unfold Cnt
  rw [Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin 5 → Fin 4)) _
    (fun t => if ZA 0 t = true ∧ t = r then 1 else 0) (fun z => by
      simp only [Equiv.funUnique_apply, GZ_one]
      rfl)]
  rw [Finset.sum_eq_single r]
  · simp
  · intro t _ ht
    simp [ht]
  · simp

theorem Cnt_succ (m : ℕ) (r : Fin 5 → Fin 4) :
    Cnt (m + 1) r = ∑ p : Fin 5 → Fin 4,
      if (ZA (min (m + 1) 4) r && ZB (min m 4) p r) = true then Cnt m p else 0 := by
  have lhs : Cnt (m + 1) r = ∑ y : Fin (m + 1) → Fin 5 → Fin 4,
      if GZ (m + 1) y ∧ ZA (min (m + 1) 4) r = true ∧ ZB (min m 4) (y (Fin.last m)) r = true
      then 1 else 0 := by
    unfold Cnt
    rw [sum_snoc, Finset.sum_eq_single r]
    · refine Finset.sum_congr rfl (fun y _ => ?_)
      simp only [GZ_snoc, Fin.snoc_last, and_true]
    · intro t _ ht
      refine Finset.sum_eq_zero (fun y _ => ?_)
      simp [Fin.snoc_last, ht]
    · simp
  have rhs : ∀ p : Fin 5 → Fin 4,
      (if (ZA (min (m + 1) 4) r && ZB (min m 4) p r) = true then Cnt m p else 0) =
        ∑ y : Fin (m + 1) → Fin 5 → Fin 4,
          if (ZA (min (m + 1) 4) r && ZB (min m 4) p r) = true ∧ GZ (m + 1) y ∧
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
    by_cases h1 : GZ (m + 1) y <;> by_cases h2 : ZA (min (m + 1) 4) r = true <;>
      by_cases h3 : ZB (min m 4) (y (Fin.last m)) r = true <;> simp [h1, h2, h3]
  · intro p _ hp
    simp [Ne.symm hp]
  · simp

/-- From row 4 on the transfer does not depend on the row. -/
theorem Cnt_hom (m : ℕ) (hm : 4 ≤ m) (r : Fin 5 → Fin 4) :
    Cnt (m + 1) r = ∑ p : Fin 5 → Fin 4,
      if (ZA 4 r && ZB 4 p r) = true then Cnt m p else 0 := by
  rw [Cnt_succ, Nat.min_eq_right (by omega : 4 ≤ m + 1), Nat.min_eq_right hm]

theorem ZB_down {c : ℕ} {p r : Fin 5 → Fin 4} (h : ZB c p r = true) (j : Fin 5) :
    (r j : ℕ) = p j + (if j.val ≤ c then 1 else 0) ∨
      (r j : ℕ) + 1 = p j + (if j.val ≤ c then 1 else 0) := by
  exact ((ZB_iff c p r).1 h).1 j

/-- The candidate row above r for the choice e: the deficit r j + e j - 1 where the step down
raises the king-move distance (j ≤ c) and r j + e j elsewhere. -/
def pred (c : ℕ) (r : Fin 5 → Fin 4) (e : Fin 5 → Fin 2) : Fin 5 → Fin 4 :=
  fun j => ⟨min ((r j : ℕ) + e j - (if j.val ≤ c then 1 else 0)) 3, by omega⟩

/-- The choice e gives a candidate row above r without cutting off any value. -/
def valid (c : ℕ) (r : Fin 5 → Fin 4) (e : Fin 5 → Fin 2) : Bool :=
  (List.finRange 5).all (fun j => decide ((if j.val ≤ c then 1 else 0) ≤ (r j : ℕ) + e j ∧
    (r j : ℕ) + e j - (if j.val ≤ c then 1 else 0) ≤ 3))

theorem valid_iff (c : ℕ) (r : Fin 5 → Fin 4) (e : Fin 5 → Fin 2) : valid c r e = true ↔
    ∀ j : Fin 5, (if j.val ≤ c then 1 else 0) ≤ (r j : ℕ) + e j ∧
      (r j : ℕ) + e j - (if j.val ≤ c then 1 else 0) ≤ 3 := by
  simp only [valid, List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq]

/-- The rows above r that a step down allows are the candidates `pred c r e`. -/
theorem sum_pred (c : ℕ) (r : Fin 5 → Fin 4) (f : (Fin 5 → Fin 4) → ℕ) :
    ∑ e : Fin 5 → Fin 2,
        (if (valid c r e && ZB c (pred c r e) r) = true then f (pred c r e) else 0) =
      ∑ p : Fin 5 → Fin 4, (if ZB c p r = true then f p else 0) := by
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
    let e : Fin 5 → Fin 2 := fun j =>
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
def spTerm (c : ℕ) (f : (Fin 5 → Fin 4) → ℕ) (r : Fin 5 → Fin 4) (e : Fin 5 → Fin 2) : ℕ :=
  if (valid c r e && ZB c (pred c r e) r) = true then f (pred c r e) else 0

/-- The transfer with the rows above r restricted to the candidates. -/
theorem Cnt_sparse (m : ℕ) (r : Fin 5 → Fin 4) :
    Cnt (m + 1) r = if ZA (min (m + 1) 4) r = true then
      ∑ e : Fin 5 → Fin 2, spTerm (min m 4) (Cnt m) r e else 0 := by
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
def dig (b : ℕ) (hb : 0 < b) (n : ℕ) : Fin 5 → Fin b := fun j => ⟨n / b ^ j.val % b, Nat.mod_lt _ hb⟩

theorem sum_dig (b : ℕ) (hb : 0 < b) (g : (Fin 5 → Fin b) → ℕ) :
    ∑ f, g f = ∑ n ∈ Finset.range (b ^ 5), g (dig b hb n) := by
  rw [← (finFunctionFinEquiv (m := b) (n := 5)).symm.sum_comp]
  exact Fin.sum_univ_eq_sum_range (fun n => g (dig b hb n)) _

/-- The position of a row of deficits in the tables. -/
def code (r : Fin 5 → Fin 4) : ℕ := (r 0 : ℕ) + (r 1 : ℕ) * 4 + (r 2 : ℕ) * 16 + (r 3 : ℕ) * 64 + (r 4 : ℕ) * 256

theorem code_lt (r : Fin 5 → Fin 4) : code r < 4 ^ 5 := by
  simp only [code]
  have := (r 0).isLt
  have := (r 1).isLt
  have := (r 2).isLt
  have := (r 3).isLt
  have := (r 4).isLt
  omega

theorem dig_code (r : Fin 5 → Fin 4) : dig 4 (by norm_num) (code r) = r := by
  funext j
  apply Fin.ext
  simp only [dig, code]
  have := (r 0).isLt
  have := (r 1).isLt
  have := (r 2).isLt
  have := (r 3).isLt
  have := (r 4).isLt
  fin_cases j <;> simp <;> omega

/-- The sum of `Cnt_sparse` over the choices e, by their codes. -/
def spSum (c : ℕ) (f : (Fin 5 → Fin 4) → ℕ) (r : Fin 5 → Fin 4) : ℕ :=
  ∑ n ∈ Finset.range (2 ^ 5), spTerm c f r (dig 2 (by norm_num) n)

theorem Cnt_sp (m : ℕ) (r : Fin 5 → Fin 4) :
    Cnt (m + 1) r = if ZA (min (m + 1) 4) r = true then spSum (min m 4) (Cnt m) r else 0 := by
  rw [Cnt_sparse, sum_dig 2 (by norm_num)]
  rfl

/-- Packs f 0, ..., f (n - 1) as 25-bit digits. -/
def pk (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => pk f n + f n <<< (25 * n)

/-- The packed table of Cnt (m + 1), computed from the packed table t of Cnt m. -/
def step (m t : ℕ) : ℕ :=
  pk (fun c => if ZA (min (m + 1) 4) (dig 4 (by norm_num) c) = true then
    spSum (min m 4) (fun p => t >>> (25 * code p) % 33554432) (dig 4 (by norm_num) c) else 0) 1024

/-- The packed tables, recomputed by the kernel. -/
def T : ℕ → ℕ
  | 0 => pk (fun c => if ZA 0 (dig 4 (by norm_num) c) = true then 1 else 0) 1024
  | m + 1 => step m (T m)

def t0 (r : Fin 5 → Fin 4) : ℕ := T 0 >>> (25 * code r) % 33554432

def t1 (r : Fin 5 → Fin 4) : ℕ := T 1 >>> (25 * code r) % 33554432

def t2 (r : Fin 5 → Fin 4) : ℕ := T 2 >>> (25 * code r) % 33554432

def t3 (r : Fin 5 → Fin 4) : ℕ := T 3 >>> (25 * code r) % 33554432

def t4 (r : Fin 5 → Fin 4) : ℕ := T 4 >>> (25 * code r) % 33554432

def t5 (r : Fin 5 → Fin 4) : ℕ := T 5 >>> (25 * code r) % 33554432

def t6 (r : Fin 5 → Fin 4) : ℕ := T 6 >>> (25 * code r) % 33554432

def t7 (r : Fin 5 → Fin 4) : ℕ := T 7 >>> (25 * code r) % 33554432

def t8 (r : Fin 5 → Fin 4) : ℕ := T 8 >>> (25 * code r) % 33554432

def t9 (r : Fin 5 → Fin 4) : ℕ := T 9 >>> (25 * code r) % 33554432

def t10 (r : Fin 5 → Fin 4) : ℕ := T 10 >>> (25 * code r) % 33554432

def t11 (r : Fin 5 → Fin 4) : ℕ := T 11 >>> (25 * code r) % 33554432

def t12 (r : Fin 5 → Fin 4) : ℕ := T 12 >>> (25 * code r) % 33554432


lemma Cnt0 (r : Fin 5 → Fin 4) : Cnt 0 r = t0 r := by
  have h : ∀ c0 c1 c2 c3 c4 : Fin 4,
      (if ZA 0 (dig 4 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 4 + (c2 : ℕ) * 16 + (c3 : ℕ) * 64 + (c4 : ℕ) * 256)) = true then 1 else 0) = t0 (dig 4 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 4 + (c2 : ℕ) * 16 + (c3 : ℕ) * 64 + (c4 : ℕ) * 256)) := by
    decide +kernel
  rw [Cnt_zero, ← dig_code r]
  exact h (r 0) (r 1) (r 2) (r 3) (r 4)

lemma Cnt1 (r : Fin 5 → Fin 4) : Cnt 1 r = t1 r := by
  have hf : Cnt 0 = t0 := funext Cnt0
  have h : ∀ c0 c1 c2 c3 c4 : Fin 4,
      (if ZA (min 1 4) (dig 4 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 4 + (c2 : ℕ) * 16 + (c3 : ℕ) * 64 + (c4 : ℕ) * 256)) = true then spSum (min 0 4) t0 (dig 4 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 4 + (c2 : ℕ) * 16 + (c3 : ℕ) * 64 + (c4 : ℕ) * 256)) else 0) =
        t1 (dig 4 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 4 + (c2 : ℕ) * 16 + (c3 : ℕ) * 64 + (c4 : ℕ) * 256)) := by
    decide +kernel
  rw [Cnt_sp, hf, ← dig_code r]
  exact h (r 0) (r 1) (r 2) (r 3) (r 4)

lemma Cnt2 (r : Fin 5 → Fin 4) : Cnt 2 r = t2 r := by
  have hf : Cnt 1 = t1 := funext Cnt1
  have h : ∀ c0 c1 c2 c3 c4 : Fin 4,
      (if ZA (min 2 4) (dig 4 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 4 + (c2 : ℕ) * 16 + (c3 : ℕ) * 64 + (c4 : ℕ) * 256)) = true then spSum (min 1 4) t1 (dig 4 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 4 + (c2 : ℕ) * 16 + (c3 : ℕ) * 64 + (c4 : ℕ) * 256)) else 0) =
        t2 (dig 4 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 4 + (c2 : ℕ) * 16 + (c3 : ℕ) * 64 + (c4 : ℕ) * 256)) := by
    decide +kernel
  rw [Cnt_sp, hf, ← dig_code r]
  exact h (r 0) (r 1) (r 2) (r 3) (r 4)

lemma Cnt3 (r : Fin 5 → Fin 4) : Cnt 3 r = t3 r := by
  have hf : Cnt 2 = t2 := funext Cnt2
  have h : ∀ c0 c1 c2 c3 c4 : Fin 4,
      (if ZA (min 3 4) (dig 4 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 4 + (c2 : ℕ) * 16 + (c3 : ℕ) * 64 + (c4 : ℕ) * 256)) = true then spSum (min 2 4) t2 (dig 4 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 4 + (c2 : ℕ) * 16 + (c3 : ℕ) * 64 + (c4 : ℕ) * 256)) else 0) =
        t3 (dig 4 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 4 + (c2 : ℕ) * 16 + (c3 : ℕ) * 64 + (c4 : ℕ) * 256)) := by
    decide +kernel
  rw [Cnt_sp, hf, ← dig_code r]
  exact h (r 0) (r 1) (r 2) (r 3) (r 4)

lemma Cnt4 (r : Fin 5 → Fin 4) : Cnt 4 r = t4 r := by
  have hf : Cnt 3 = t3 := funext Cnt3
  have h : ∀ c0 c1 c2 c3 c4 : Fin 4,
      (if ZA (min 4 4) (dig 4 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 4 + (c2 : ℕ) * 16 + (c3 : ℕ) * 64 + (c4 : ℕ) * 256)) = true then spSum (min 3 4) t3 (dig 4 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 4 + (c2 : ℕ) * 16 + (c3 : ℕ) * 64 + (c4 : ℕ) * 256)) else 0) =
        t4 (dig 4 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 4 + (c2 : ℕ) * 16 + (c3 : ℕ) * 64 + (c4 : ℕ) * 256)) := by
    decide +kernel
  rw [Cnt_sp, hf, ← dig_code r]
  exact h (r 0) (r 1) (r 2) (r 3) (r 4)

lemma Cnt5 (r : Fin 5 → Fin 4) : Cnt 5 r = t5 r := by
  have hf : Cnt 4 = t4 := funext Cnt4
  have h : ∀ c0 c1 c2 c3 c4 : Fin 4,
      (if ZA (min 5 4) (dig 4 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 4 + (c2 : ℕ) * 16 + (c3 : ℕ) * 64 + (c4 : ℕ) * 256)) = true then spSum (min 4 4) t4 (dig 4 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 4 + (c2 : ℕ) * 16 + (c3 : ℕ) * 64 + (c4 : ℕ) * 256)) else 0) =
        t5 (dig 4 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 4 + (c2 : ℕ) * 16 + (c3 : ℕ) * 64 + (c4 : ℕ) * 256)) := by
    decide +kernel
  rw [Cnt_sp, hf, ← dig_code r]
  exact h (r 0) (r 1) (r 2) (r 3) (r 4)

lemma Cnt6 (r : Fin 5 → Fin 4) : Cnt 6 r = t6 r := by
  have hf : Cnt 5 = t5 := funext Cnt5
  have h : ∀ c0 c1 c2 c3 c4 : Fin 4,
      (if ZA (min 6 4) (dig 4 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 4 + (c2 : ℕ) * 16 + (c3 : ℕ) * 64 + (c4 : ℕ) * 256)) = true then spSum (min 5 4) t5 (dig 4 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 4 + (c2 : ℕ) * 16 + (c3 : ℕ) * 64 + (c4 : ℕ) * 256)) else 0) =
        t6 (dig 4 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 4 + (c2 : ℕ) * 16 + (c3 : ℕ) * 64 + (c4 : ℕ) * 256)) := by
    decide +kernel
  rw [Cnt_sp, hf, ← dig_code r]
  exact h (r 0) (r 1) (r 2) (r 3) (r 4)

lemma Cnt7 (r : Fin 5 → Fin 4) : Cnt 7 r = t7 r := by
  have hf : Cnt 6 = t6 := funext Cnt6
  have h : ∀ c0 c1 c2 c3 c4 : Fin 4,
      (if ZA (min 7 4) (dig 4 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 4 + (c2 : ℕ) * 16 + (c3 : ℕ) * 64 + (c4 : ℕ) * 256)) = true then spSum (min 6 4) t6 (dig 4 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 4 + (c2 : ℕ) * 16 + (c3 : ℕ) * 64 + (c4 : ℕ) * 256)) else 0) =
        t7 (dig 4 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 4 + (c2 : ℕ) * 16 + (c3 : ℕ) * 64 + (c4 : ℕ) * 256)) := by
    decide +kernel
  rw [Cnt_sp, hf, ← dig_code r]
  exact h (r 0) (r 1) (r 2) (r 3) (r 4)

lemma Cnt8 (r : Fin 5 → Fin 4) : Cnt 8 r = t8 r := by
  have hf : Cnt 7 = t7 := funext Cnt7
  have h : ∀ c0 c1 c2 c3 c4 : Fin 4,
      (if ZA (min 8 4) (dig 4 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 4 + (c2 : ℕ) * 16 + (c3 : ℕ) * 64 + (c4 : ℕ) * 256)) = true then spSum (min 7 4) t7 (dig 4 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 4 + (c2 : ℕ) * 16 + (c3 : ℕ) * 64 + (c4 : ℕ) * 256)) else 0) =
        t8 (dig 4 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 4 + (c2 : ℕ) * 16 + (c3 : ℕ) * 64 + (c4 : ℕ) * 256)) := by
    decide +kernel
  rw [Cnt_sp, hf, ← dig_code r]
  exact h (r 0) (r 1) (r 2) (r 3) (r 4)

lemma Cnt9 (r : Fin 5 → Fin 4) : Cnt 9 r = t9 r := by
  have hf : Cnt 8 = t8 := funext Cnt8
  have h : ∀ c0 c1 c2 c3 c4 : Fin 4,
      (if ZA (min 9 4) (dig 4 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 4 + (c2 : ℕ) * 16 + (c3 : ℕ) * 64 + (c4 : ℕ) * 256)) = true then spSum (min 8 4) t8 (dig 4 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 4 + (c2 : ℕ) * 16 + (c3 : ℕ) * 64 + (c4 : ℕ) * 256)) else 0) =
        t9 (dig 4 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 4 + (c2 : ℕ) * 16 + (c3 : ℕ) * 64 + (c4 : ℕ) * 256)) := by
    decide +kernel
  rw [Cnt_sp, hf, ← dig_code r]
  exact h (r 0) (r 1) (r 2) (r 3) (r 4)

lemma Cnt10 (r : Fin 5 → Fin 4) : Cnt 10 r = t10 r := by
  have hf : Cnt 9 = t9 := funext Cnt9
  have h : ∀ c0 c1 c2 c3 c4 : Fin 4,
      (if ZA (min 10 4) (dig 4 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 4 + (c2 : ℕ) * 16 + (c3 : ℕ) * 64 + (c4 : ℕ) * 256)) = true then spSum (min 9 4) t9 (dig 4 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 4 + (c2 : ℕ) * 16 + (c3 : ℕ) * 64 + (c4 : ℕ) * 256)) else 0) =
        t10 (dig 4 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 4 + (c2 : ℕ) * 16 + (c3 : ℕ) * 64 + (c4 : ℕ) * 256)) := by
    decide +kernel
  rw [Cnt_sp, hf, ← dig_code r]
  exact h (r 0) (r 1) (r 2) (r 3) (r 4)

lemma Cnt11 (r : Fin 5 → Fin 4) : Cnt 11 r = t11 r := by
  have hf : Cnt 10 = t10 := funext Cnt10
  have h : ∀ c0 c1 c2 c3 c4 : Fin 4,
      (if ZA (min 11 4) (dig 4 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 4 + (c2 : ℕ) * 16 + (c3 : ℕ) * 64 + (c4 : ℕ) * 256)) = true then spSum (min 10 4) t10 (dig 4 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 4 + (c2 : ℕ) * 16 + (c3 : ℕ) * 64 + (c4 : ℕ) * 256)) else 0) =
        t11 (dig 4 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 4 + (c2 : ℕ) * 16 + (c3 : ℕ) * 64 + (c4 : ℕ) * 256)) := by
    decide +kernel
  rw [Cnt_sp, hf, ← dig_code r]
  exact h (r 0) (r 1) (r 2) (r 3) (r 4)

lemma Cnt12 (r : Fin 5 → Fin 4) : Cnt 12 r = t12 r := by
  have hf : Cnt 11 = t11 := funext Cnt11
  have h : ∀ c0 c1 c2 c3 c4 : Fin 4,
      (if ZA (min 12 4) (dig 4 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 4 + (c2 : ℕ) * 16 + (c3 : ℕ) * 64 + (c4 : ℕ) * 256)) = true then spSum (min 11 4) t11 (dig 4 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 4 + (c2 : ℕ) * 16 + (c3 : ℕ) * 64 + (c4 : ℕ) * 256)) else 0) =
        t12 (dig 4 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 4 + (c2 : ℕ) * 16 + (c3 : ℕ) * 64 + (c4 : ℕ) * 256)) := by
    decide +kernel
  rw [Cnt_sp, hf, ← dig_code r]
  exact h (r 0) (r 1) (r 2) (r 3) (r 4)

/-- The difference equation of order 4 on every deficit row, from m = 8 on. -/
theorem Cnt_rec (m : ℕ) : ∀ r : Fin 5 → Fin 4, (Cnt (m + 12) r : ℤ) = 4 * Cnt (m + 11) r - 6 * Cnt (m + 10) r + 4 * Cnt (m + 9) r - Cnt (m + 8) r := by
  induction m with
  | zero =>
    intro r
    simp only [Nat.zero_add, Cnt8, Cnt9, Cnt10, Cnt11, Cnt12]
    have h : ∀ c0 c1 c2 c3 c4 : Fin 4,
        (t12 (dig 4 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 4 + (c2 : ℕ) * 16 + (c3 : ℕ) * 64 + (c4 : ℕ) * 256)) : ℤ) = 4 * t11 (dig 4 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 4 + (c2 : ℕ) * 16 + (c3 : ℕ) * 64 + (c4 : ℕ) * 256)) - 6 * t10 (dig 4 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 4 + (c2 : ℕ) * 16 + (c3 : ℕ) * 64 + (c4 : ℕ) * 256)) + 4 * t9 (dig 4 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 4 + (c2 : ℕ) * 16 + (c3 : ℕ) * 64 + (c4 : ℕ) * 256)) - t8 (dig 4 (by norm_num) ((c0 : ℕ) + (c1 : ℕ) * 4 + (c2 : ℕ) * 16 + (c3 : ℕ) * 64 + (c4 : ℕ) * 256)) := by
      decide +kernel
    rw [← dig_code r]
    exact h (r 0) (r 1) (r 2) (r 3) (r 4)
  | succ m ih =>
    intro r
    rw [show m + 1 + 12 = m + 12 + 1 by omega, show m + 1 + 11 = m + 11 + 1 by omega, show m + 1 + 10 = m + 10 + 1 by omega, show m + 1 + 9 = m + 9 + 1 by omega, show m + 1 + 8 = m + 8 + 1 by omega,
      Cnt_hom (m + 12) (by omega), Cnt_hom (m + 11) (by omega), Cnt_hom (m + 10) (by omega), Cnt_hom (m + 9) (by omega), Cnt_hom (m + 8) (by omega)]
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    split_ifs
    · exact ih p
    · simp

/-- The recurrence of a, for n >= 13. -/
theorem a_rec (m : ℕ) : (a (m + 12 + 1) : ℤ) = 4 * a (m + 11 + 1) - 6 * a (m + 10 + 1) + 4 * a (m + 9 + 1) - a (m + 8 + 1) := by
  rw [a_succ, a_succ, a_succ, a_succ, a_succ]
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  split_ifs
  · exact Cnt_rec m r
  · simp

lemma v1 : a 1 = 4 := by
  rw [a_succ, sum_dig 4 (by norm_num)]
  simp only [Cnt0]
  decide +kernel

lemma v2 : a 2 = 14 := by
  rw [a_succ, sum_dig 4 (by norm_num)]
  simp only [Cnt1]
  decide +kernel

lemma v3 : a 3 = 34 := by
  rw [a_succ, sum_dig 4 (by norm_num)]
  simp only [Cnt2]
  decide +kernel

lemma v4 : a 4 = 69 := by
  rw [a_succ, sum_dig 4 (by norm_num)]
  simp only [Cnt3]
  decide +kernel

lemma v5 : a 5 = 69 := by
  rw [a_succ, sum_dig 4 (by norm_num)]
  simp only [Cnt4]
  decide +kernel

lemma v6 : a 6 = 3072 := by
  rw [a_succ, sum_dig 4 (by norm_num)]
  simp only [Cnt5]
  decide +kernel

lemma v7 : a 7 = 39758 := by
  rw [a_succ, sum_dig 4 (by norm_num)]
  simp only [Cnt6]
  decide +kernel

lemma v8 : a 8 = 228484 := by
  rw [a_succ, sum_dig 4 (by norm_num)]
  simp only [Cnt7]
  decide +kernel

lemma v9 : a 9 = 775433 := by
  rw [a_succ, sum_dig 4 (by norm_num)]
  simp only [Cnt8]
  decide +kernel

lemma v10 : a 10 = 1932763 := by
  rw [a_succ, sum_dig 4 (by norm_num)]
  simp only [Cnt9]
  decide +kernel

lemma v11 : a 11 = 3965261 := by
  rw [a_succ, sum_dig 4 (by norm_num)]
  simp only [Cnt10]
  decide +kernel

lemma v12 : a 12 = 7139167 := by
  rw [a_succ, sum_dig 4 (by norm_num)]
  simp only [Cnt11]
  decide +kernel

/-- Barker's recurrence, for n > 12. -/
theorem recurrence (n : ℕ) (hn : 12 < n) : (a n : ℤ) = 4 * a (n - 1) - 6 * a (n - 2) + 4 * a (n - 3) - a (n - 4) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 + 4 + 1 := ⟨n - 13, by omega⟩
  rw [show m + 8 + 4 + 1 - 1 = m + 11 + 1 by omega, show m + 8 + 4 + 1 - 2 = m + 10 + 1 by omega, show m + 8 + 4 + 1 - 3 = m + 9 + 1 by omega, show m + 8 + 4 + 1 - 4 = m + 8 + 1 by omega]
  rw [show m + 8 + 4 + 1 = m + 12 + 1 by omega]
  exact a_rec m

/-- Barker's g.f., as A(x) (1 - x)^4 = its numerator in Z[[x]]. -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 4 =
    X * (4 - 2 * X + 2 * X ^ 2 + X ^ 3 - 55 * X ^ 4 + 3088 * X ^ 5 + 27642 * X ^ 6 +
        87677 * X ^ 7 + 87826 * X ^ 8 + 45975 * X ^ 9 + 12629 * X ^ 10 + 1453 * X ^ 11) := by
  set A : ℤ⟦X⟧ := PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) with hA
  have e1 : A * (1 - X) ^ 4 = A - C 4 * (A * X ^ 1) + C 6 * (A * X ^ 2) - C 4 * (A * X ^ 3) + A * X ^ 4 := by
    simp only [map_ofNat]; ring
  have e2 : (X * (4 - 2 * X + 2 * X ^ 2 + X ^ 3 - 55 * X ^ 4 + 3088 * X ^ 5 + 27642 * X ^ 6 +
        87677 * X ^ 7 + 87826 * X ^ 8 + 45975 * X ^ 9 + 12629 * X ^ 10 + 1453 * X ^ 11) : ℤ⟦X⟧) =
      X ^ 1 * C 4 - X ^ 2 * C 2 + X ^ 3 * C 2 + X ^ 4 - X ^ 5 * C 55 + X ^ 6 * C 3088 + X ^ 7 * C 27642 + X ^ 8 * C 87677 + X ^ 9 * C 87826 + X ^ 10 * C 45975 + X ^ 11 * C 12629 + X ^ 12 * C 1453 := by
    simp only [map_ofNat]; ring
  rw [e1, e2]
  ext n
  have hc : ∀ k, coeff k A = if k = 0 then (0 : ℤ) else a k := fun k => by rw [hA, coeff_mk]
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_C, coeff_X_pow, coeff_mul_X_pow', hc]
  rcases Nat.lt_or_ge n 13 with hn | hn
  · interval_cases n <;> simp [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12]
  · obtain ⟨q, rfl⟩ : ∃ q, n = q + 13 := ⟨n - 13, by omega⟩
    have h := recurrence (q + 13) (by omega)
    simp only [show q + 13 - 1 = q + 12 by omega, show q + 13 - 2 = q + 11 by omega, show q + 13 - 3 = q + 10 by omega, show q + 13 - 4 = q + 9 by omega] at h ⊢
    simp only [ show ¬ q + 13 = 0 by omega, show 1 ≤ q + 13 by omega, show ¬ q + 12 = 0 by omega,
      show 2 ≤ q + 13 by omega, show ¬ q + 11 = 0 by omega, show 3 ≤ q + 13 by omega,
      show ¬ q + 10 = 0 by omega, show 4 ≤ q + 13 by omega, show ¬ q + 9 = 0 by omega,
      show ¬ q + 13 = 1 by omega, show ¬ q + 13 = 2 by omega, show ¬ q + 13 = 3 by omega,
      show ¬ q + 13 = 4 by omega, show ¬ q + 13 = 5 by omega, show ¬ q + 13 = 6 by omega,
      show ¬ q + 13 = 7 by omega, show ¬ q + 13 = 8 by omega, show ¬ q + 13 = 9 by omega,
      show ¬ q + 13 = 10 by omega, show ¬ q + 13 = 11 by omega, show ¬ q + 13 = 12 by omega,
      if_true, if_false]
    rw [h]
    ring

/-- Controls: the entry's data a(1..27). -/
theorem controls : a 1 = 4 ∧ a 2 = 14 ∧ a 3 = 34 ∧ a 4 = 69 ∧ a 5 = 69 ∧ a 6 = 3072 ∧ a 7 = 39758 ∧
    a 8 = 228484 ∧ a 9 = 775433 ∧ a 10 = 1932763 ∧ a 11 = 3965261 ∧ a 12 = 7139167 ∧
    a 13 = 11720721 ∧ a 14 = 17976163 ∧ a 15 = 26171733 ∧ a 16 = 36573671 ∧ a 17 = 49448217 ∧
    a 18 = 65061611 ∧ a 19 = 83680093 ∧ a 20 = 105569903 ∧ a 21 = 130997281 ∧ a 22 = 160228467 ∧
    a 23 = 193529701 ∧ a 24 = 231167223 ∧ a 25 = 273407273 ∧ a 26 = 320516091 ∧
    a 27 = 372759917 := by
  have v13 : a 13 = 11720721 := by
    have h : (a 13 : ℤ) = 4 * a 12 - 6 * a 11 + 4 * a 10 - a 9 := a_rec 0
    rw [v12, v11, v10, v9] at h
    omega
  have v14 : a 14 = 17976163 := by
    have h : (a 14 : ℤ) = 4 * a 13 - 6 * a 12 + 4 * a 11 - a 10 := a_rec 1
    rw [v13, v12, v11, v10] at h
    omega
  have v15 : a 15 = 26171733 := by
    have h : (a 15 : ℤ) = 4 * a 14 - 6 * a 13 + 4 * a 12 - a 11 := a_rec 2
    rw [v14, v13, v12, v11] at h
    omega
  have v16 : a 16 = 36573671 := by
    have h : (a 16 : ℤ) = 4 * a 15 - 6 * a 14 + 4 * a 13 - a 12 := a_rec 3
    rw [v15, v14, v13, v12] at h
    omega
  have v17 : a 17 = 49448217 := by
    have h : (a 17 : ℤ) = 4 * a 16 - 6 * a 15 + 4 * a 14 - a 13 := a_rec 4
    rw [v16, v15, v14, v13] at h
    omega
  have v18 : a 18 = 65061611 := by
    have h : (a 18 : ℤ) = 4 * a 17 - 6 * a 16 + 4 * a 15 - a 14 := a_rec 5
    rw [v17, v16, v15, v14] at h
    omega
  have v19 : a 19 = 83680093 := by
    have h : (a 19 : ℤ) = 4 * a 18 - 6 * a 17 + 4 * a 16 - a 15 := a_rec 6
    rw [v18, v17, v16, v15] at h
    omega
  have v20 : a 20 = 105569903 := by
    have h : (a 20 : ℤ) = 4 * a 19 - 6 * a 18 + 4 * a 17 - a 16 := a_rec 7
    rw [v19, v18, v17, v16] at h
    omega
  have v21 : a 21 = 130997281 := by
    have h : (a 21 : ℤ) = 4 * a 20 - 6 * a 19 + 4 * a 18 - a 17 := a_rec 8
    rw [v20, v19, v18, v17] at h
    omega
  have v22 : a 22 = 160228467 := by
    have h : (a 22 : ℤ) = 4 * a 21 - 6 * a 20 + 4 * a 19 - a 18 := a_rec 9
    rw [v21, v20, v19, v18] at h
    omega
  have v23 : a 23 = 193529701 := by
    have h : (a 23 : ℤ) = 4 * a 22 - 6 * a 21 + 4 * a 20 - a 19 := a_rec 10
    rw [v22, v21, v20, v19] at h
    omega
  have v24 : a 24 = 231167223 := by
    have h : (a 24 : ℤ) = 4 * a 23 - 6 * a 22 + 4 * a 21 - a 20 := a_rec 11
    rw [v23, v22, v21, v20] at h
    omega
  have v25 : a 25 = 273407273 := by
    have h : (a 25 : ℤ) = 4 * a 24 - 6 * a 23 + 4 * a 22 - a 21 := a_rec 12
    rw [v24, v23, v22, v21] at h
    omega
  have v26 : a 26 = 320516091 := by
    have h : (a 26 : ℤ) = 4 * a 25 - 6 * a 24 + 4 * a 23 - a 22 := a_rec 13
    rw [v25, v24, v23, v22] at h
    omega
  have v27 : a 27 = 372759917 := by
    have h : (a 27 : ℤ) = 4 * a 26 - 6 * a 25 + 4 * a 24 - a 23 := a_rec 14
    rw [v26, v25, v24, v23] at h
    omega
  exact ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27⟩

/-- Both of Barker's conjectures. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 4 =
      X * (4 - 2 * X + 2 * X ^ 2 + X ^ 3 - 55 * X ^ 4 + 3088 * X ^ 5 + 27642 * X ^ 6 +
        87677 * X ^ 7 + 87826 * X ^ 8 + 45975 * X ^ 9 + 12629 * X ^ 10 + 1453 * X ^ 11) ∧
    ∀ n : ℕ, 12 < n → (a n : ℤ) = 4 * a (n - 1) - 6 * a (n - 2) + 4 * a (n - 3) - a (n - 4) :=
  ⟨gf, recurrence⟩

end OMA.S_oeis_a253001

theorem OMA.solution : type_of% @OMA.S_oeis_a253001.main :=
  OMA.S_oeis_a253001.conjecture
