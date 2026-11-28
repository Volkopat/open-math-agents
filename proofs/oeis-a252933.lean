import OMAStatements.S_oeis_a252933

namespace OMA.S_oeis_a252933

open PowerSeries




/-- The conditions of the entry on one row v with row index i. -/
def RA (i : ℕ) (v : Fin 3 → ℕ) : Prop :=
  (∀ j : Fin 3, i = 0 → j.val = 0 → v j = 0) ∧
  (∀ j : Fin 3, max i j.val ≤ v j + 3 ∧ v j ≤ max i j.val + 3) ∧
  (∀ j j' : Fin 3, j'.val = j.val + 1 → step01 (v j) (v j'))

/-- The conditions of the entry between a row u and the row v below it. -/
def RB (u v : Fin 3 → ℕ) : Prop :=
  (∀ j : Fin 3, step01 (u j) (v j)) ∧
  (∀ j j' : Fin 3, j'.val = j.val + 1 → step01 (u j) (v j'))

theorem good_iff (n : ℕ) (x : Fin n → Fin 3 → ℕ) :
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
theorem le_dist {n : ℕ} {x : Fin n → Fin 3 → ℕ} (h : good n x) :
    ∀ s, ∀ (i : Fin n) (j : Fin 3), i.val + j.val = s → x i j ≤ max i.val j.val := by
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
def ZA (c : ℕ) (r : Fin 3 → Fin 4) : Bool :=
  decide ((∀ j : Fin 3, (r j : ℕ) ≤ max c j.val) ∧
    ∀ j j' : Fin 3, j'.val = j.val + 1 →
      ((r j' : ℕ) = r j + (if c ≤ j.val then 1 else 0) ∨
        (r j' : ℕ) + 1 = r j + (if c ≤ j.val then 1 else 0)))

/-- The conditions between a row p of deficits at a row index i, with c = min i 3, and the row
r of deficits below it: every step down or diagonally down-right changes the value by 0 or 1. -/
def ZB (c : ℕ) (p r : Fin 3 → Fin 4) : Bool :=
  decide ((∀ j : Fin 3, (r j : ℕ) = p j + (if j.val ≤ c then 1 else 0) ∨
      (r j : ℕ) + 1 = p j + (if j.val ≤ c then 1 else 0)) ∧
    ∀ j j' : Fin 3, j'.val = j.val + 1 → ((r j' : ℕ) = p j ∨ (r j' : ℕ) = p j + 1))

/-- The values of a row r of deficits at row index i. -/
def vals (i : ℕ) (r : Fin 3 → Fin 4) : Fin 3 → ℕ := fun j => max i j.val - r j

theorem rowA (i : ℕ) (r : Fin 3 → Fin 4) :
    (RA i (vals i r) ∧ ∀ j : Fin 3, (r j : ℕ) ≤ max i j.val) ↔ ZA (min i 3) r = true := by
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

theorem rowB (i : ℕ) (p r : Fin 3 → Fin 4) (hp : ∀ j : Fin 3, (p j : ℕ) ≤ max i j.val)
    (hr : ∀ j : Fin 3, (r j : ℕ) ≤ max (i + 1) j.val) :
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

theorem bound_of_ZA {i : ℕ} {r : Fin 3 → Fin 4} (h : ZA (min i 3) r = true) (j : Fin 3) :
    (r j : ℕ) ≤ max i j.val :=
  ((rowA i r).2 h).2 j

/-- The deficit form of the conditions on an array of deficits. -/
def GZ (n : ℕ) (z : Fin n → Fin 3 → Fin 4) : Prop :=
  (∀ i : Fin n, ZA (min i.val 3) (z i) = true) ∧
    ∀ i i' : Fin n, i'.val = i.val + 1 → ZB (min i.val 3) (z i) (z i') = true

instance (n : ℕ) : DecidablePred (GZ n) := fun z => by unfold GZ; infer_instance

theorem set_eq (n : ℕ) : {x : Fin n → Fin 3 → ℕ | good n x} =
    (fun z : Fin n → Fin 3 → Fin 4 => fun i => vals i.val (z i)) '' {z | GZ n z} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_image]
  constructor
  · intro hx
    have hd : ∀ i j, x i j ≤ max i.val j.val := fun i j => le_dist hx (i.val + j.val) i j rfl
    have hw := hx.2.1
    let z : Fin n → Fin 3 → Fin 4 := fun i j =>
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
    Set.InjOn (fun z : Fin n → Fin 3 → Fin 4 => fun i => vals i.val (z i)) {z | GZ n z} := by
  intro z hz z' hz' h
  funext i j
  have e := congrFun (congrFun h i) j
  simp only [vals] at e
  have b := bound_of_ZA (hz.1 i) j
  have b' := bound_of_ZA (hz'.1 i) j
  exact Fin.ext (by omega)

theorem a_eq (n : ℕ) :
    a n = (Finset.univ.filter fun z : Fin n → Fin 3 → Fin 4 => GZ n z).card := by
  unfold a
  rw [set_eq, Set.ncard_image_of_injOn (injOn n), ← Set.ncard_coe_finset]
  congr 1
  ext z
  simp

theorem GZ_snoc (m : ℕ) (y : Fin (m + 1) → Fin 3 → Fin 4) (t : Fin 3 → Fin 4) :
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

theorem GZ_one (z : Fin (0 + 1) → Fin 3 → Fin 4) : GZ (0 + 1) z ↔ ZA 0 (z 0) = true := by
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

theorem sum_snoc (m : ℕ) (f : (Fin (m + 1 + 1) → Fin 3 → Fin 4) → ℕ) :
    ∑ z : Fin (m + 1 + 1) → Fin 3 → Fin 4, f z =
      ∑ t : Fin 3 → Fin 4, ∑ y : Fin (m + 1) → Fin 3 → Fin 4, f (Fin.snoc y t) := by
  rw [← (Fin.snocEquiv fun _ => Fin 3 → Fin 4).sum_comp, Fintype.sum_prod_type]
  rfl

/-- The number of deficit arrays with m + 1 rows whose last row is r. -/
def Cnt (m : ℕ) (r : Fin 3 → Fin 4) : ℕ :=
  ∑ z : Fin (m + 1) → Fin 3 → Fin 4, if GZ (m + 1) z ∧ z (Fin.last m) = r then 1 else 0

theorem a_succ (n : ℕ) : a (n + 1) = ∑ r : Fin 3 → Fin 4, Cnt n r := by
  rw [a_eq, Finset.card_filter]
  unfold Cnt
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  rw [Finset.sum_eq_single (z (Fin.last n))]
  · simp
  · intro r _ hr
    simp [Ne.symm hr]
  · simp

theorem Cnt_zero (r : Fin 3 → Fin 4) : Cnt 0 r = if ZA 0 r = true then 1 else 0 := by
  unfold Cnt
  rw [Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin 3 → Fin 4)) _
    (fun t => if ZA 0 t = true ∧ t = r then 1 else 0) (fun z => by
      simp only [Equiv.funUnique_apply, GZ_one]
      rfl)]
  rw [Finset.sum_eq_single r]
  · simp
  · intro t _ ht
    simp [ht]
  · simp

theorem Cnt_succ (m : ℕ) (r : Fin 3 → Fin 4) :
    Cnt (m + 1) r = ∑ p : Fin 3 → Fin 4,
      if (ZA (min (m + 1) 3) r && ZB (min m 3) p r) = true then Cnt m p else 0 := by
  have lhs : Cnt (m + 1) r = ∑ y : Fin (m + 1) → Fin 3 → Fin 4,
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
  have rhs : ∀ p : Fin 3 → Fin 4,
      (if (ZA (min (m + 1) 3) r && ZB (min m 3) p r) = true then Cnt m p else 0) =
        ∑ y : Fin (m + 1) → Fin 3 → Fin 4,
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
theorem Cnt_hom (m : ℕ) (hm : 3 ≤ m) (r : Fin 3 → Fin 4) :
    Cnt (m + 1) r = ∑ p : Fin 3 → Fin 4,
      if (ZA 3 r && ZB 3 p r) = true then Cnt m p else 0 := by
  rw [Cnt_succ, Nat.min_eq_right (by omega : 3 ≤ m + 1), Nat.min_eq_right hm]

theorem sum_pi_succ {m : ℕ} (g : (Fin (m + 1) → Fin 4) → ℕ) :
    ∑ p, g p = ∑ c : Fin 4, ∑ q : Fin m → Fin 4, g (Fin.cons c q) := by
  rw [← (Fin.consEquiv fun _ => Fin 4).sum_comp, Fintype.sum_prod_type]
  rfl

theorem sum_pi_zero (g : (Fin 0 → Fin 4) → ℕ) : ∑ p, g p = g ![] := by
  rw [Fintype.sum_unique]
  exact congrArg g (Subsingleton.elim _ _)

theorem row_eta (r : Fin 3 → Fin 4) : ![r 0, r 1, r 2] = r := by
  funext j
  fin_cases j <;> rfl

/-- The position of a row of deficits in the tables. -/
def code (r : Fin 3 → Fin 4) : ℕ := (r 0 : ℕ) * 16 + (r 1 : ℕ) * 4 + (r 2 : ℕ)

/-- The table of Cnt 0: the base 2^14 digit at position `code r` is Cnt 0 r. -/
def t0 (r : Fin 3 → Fin 4) : ℕ :=
  19343993705454784206618625 / 16384 ^ code r % 16384

/-- The table of Cnt 1: the base 2^14 digit at position `code r` is Cnt 1 r. -/
def t1 (r : Fin 3 → Fin 4) : ℕ :=
  521544867315888890776243174379040724845175829625369103596816294620709496454767967913207971842 / 16384 ^ code r % 16384

/-- The table of Cnt 2: the base 2^14 digit at position `code r` is Cnt 2 r. -/
def t2 (r : Fin 3 → Fin 4) : ℕ :=
  1013250822234940999917512563103586214754010381084876396288822078855047869457413433087692607603510259933553743150804380799845534911276526965672861227248528659315418058095169896453 / 16384 ^ code r % 16384

/-- The table of Cnt 3: the base 2^14 digit at position `code r` is Cnt 3 r. -/
def t3 (r : Fin 3 → Fin 4) : ℕ :=
  32252411455852098976431283770333159849785786403077303214118381383302841344497653119466599320855331941218322192149758019890973538586162873461051249382023346902026573474697554891484037682431300300061711899562051692694110999885107210517283238548320157661962525913120773 / 16384 ^ code r % 16384

/-- The table of Cnt 4: the base 2^14 digit at position `code r` is Cnt 4 r. -/
def t4 (r : Fin 3 → Fin 4) : ℕ :=
  1096452098166527733355123072210069854026192088989966453854695100140319437459539708773560454572659045677831399890073135145516340791276594924623164519137665894689830281190786769985832414319984286594503274010887462336640796085179959301838968150219968261262888685572980741 / 16384 ^ code r % 16384

/-- The table of Cnt 5: the base 2^14 digit at position `code r` is Cnt 5 r. -/
def t5 (r : Fin 3 → Fin 4) : ℕ :=
  8996761761567850382993466731624953046553305789129019181428888917520079919175659267732233733266483821195913612236443159380518144433620467905408216132953344086693182211940477171405715915644580700979391999664950055500811993582795297759791318659783032859835627769146900485 / 16384 ^ code r % 16384

/-- The table of Cnt 6: the base 2^14 digit at position `code r` is Cnt 6 r. -/
def t6 (r : Fin 3 → Fin 4) : ℕ :=
  33148634097006276663768068923512647441747052266400680685849098994037288448778789721676258085034370106312284236176013625964446516910440497283753225762291784829716299957654052694642437450645042678177950826841371065138128695805384496307096068483230935565648018335240028165 / 16384 ^ code r % 16384

/-- The table of Cnt 7: the base 2^14 digit at position `code r` is Cnt 7 r. -/
def t7 (r : Fin 3 → Fin 4) : ℕ :=
  83870321665725268418498066072023868010678668357447949446177057927869169685579963482215345538932122352094802548920837829406722308993273509959082782830257276735251110940187081389866534473939074145007059304528650264767107080345751495155440657049607357560136360792011309061 / 16384 ^ code r % 16384

/-- The table of Cnt 8: the base 2^14 digit at position `code r` is Cnt 8 r. -/
def t8 (r : Fin 3 → Fin 4) : ℕ :=
  171480077028968287490002594601309329724419390898913823941474498317192948288890212960959208124015545009611327827682969064216766371453656332830821476759954108414789542581395131307248544440144379028283596981715287427906263324796700234516512523787955980024736955547619688453 / 16384 ^ code r % 16384

lemma Cnt0 (r : Fin 3 → Fin 4) : Cnt 0 r = t0 r := by
  have h : ∀ c0 c1 c2 : Fin 4, Cnt 0 ![c0, c1, c2] = t0 ![c0, c1, c2] := by
    intro c0 c1 c2
    rw [Cnt_zero]
    revert c0 c1 c2
    decide +kernel
  rw [← row_eta r]
  exact h _ _ _

lemma Cnt1 (r : Fin 3 → Fin 4) : Cnt 1 r = t1 r := by
  have h : ∀ c0 c1 c2 : Fin 4, Cnt 1 ![c0, c1, c2] = t1 ![c0, c1, c2] := by
    intro c0 c1 c2
    rw [Cnt_succ]
    simp only [Cnt0, sum_pi_succ, sum_pi_zero]
    revert c0 c1 c2
    decide +kernel
  rw [← row_eta r]
  exact h _ _ _

lemma Cnt2 (r : Fin 3 → Fin 4) : Cnt 2 r = t2 r := by
  have h : ∀ c0 c1 c2 : Fin 4, Cnt 2 ![c0, c1, c2] = t2 ![c0, c1, c2] := by
    intro c0 c1 c2
    rw [Cnt_succ]
    simp only [Cnt1, sum_pi_succ, sum_pi_zero]
    revert c0 c1 c2
    decide +kernel
  rw [← row_eta r]
  exact h _ _ _

lemma Cnt3 (r : Fin 3 → Fin 4) : Cnt 3 r = t3 r := by
  have h : ∀ c0 c1 c2 : Fin 4, Cnt 3 ![c0, c1, c2] = t3 ![c0, c1, c2] := by
    intro c0 c1 c2
    rw [Cnt_succ]
    simp only [Cnt2, sum_pi_succ, sum_pi_zero]
    revert c0 c1 c2
    decide +kernel
  rw [← row_eta r]
  exact h _ _ _

lemma Cnt4 (r : Fin 3 → Fin 4) : Cnt 4 r = t4 r := by
  have h : ∀ c0 c1 c2 : Fin 4, Cnt 4 ![c0, c1, c2] = t4 ![c0, c1, c2] := by
    intro c0 c1 c2
    rw [Cnt_succ]
    simp only [Cnt3, sum_pi_succ, sum_pi_zero]
    revert c0 c1 c2
    decide +kernel
  rw [← row_eta r]
  exact h _ _ _

lemma Cnt5 (r : Fin 3 → Fin 4) : Cnt 5 r = t5 r := by
  have h : ∀ c0 c1 c2 : Fin 4, Cnt 5 ![c0, c1, c2] = t5 ![c0, c1, c2] := by
    intro c0 c1 c2
    rw [Cnt_succ]
    simp only [Cnt4, sum_pi_succ, sum_pi_zero]
    revert c0 c1 c2
    decide +kernel
  rw [← row_eta r]
  exact h _ _ _

lemma Cnt6 (r : Fin 3 → Fin 4) : Cnt 6 r = t6 r := by
  have h : ∀ c0 c1 c2 : Fin 4, Cnt 6 ![c0, c1, c2] = t6 ![c0, c1, c2] := by
    intro c0 c1 c2
    rw [Cnt_succ]
    simp only [Cnt5, sum_pi_succ, sum_pi_zero]
    revert c0 c1 c2
    decide +kernel
  rw [← row_eta r]
  exact h _ _ _

lemma Cnt7 (r : Fin 3 → Fin 4) : Cnt 7 r = t7 r := by
  have h : ∀ c0 c1 c2 : Fin 4, Cnt 7 ![c0, c1, c2] = t7 ![c0, c1, c2] := by
    intro c0 c1 c2
    rw [Cnt_succ]
    simp only [Cnt6, sum_pi_succ, sum_pi_zero]
    revert c0 c1 c2
    decide +kernel
  rw [← row_eta r]
  exact h _ _ _

lemma Cnt8 (r : Fin 3 → Fin 4) : Cnt 8 r = t8 r := by
  have h : ∀ c0 c1 c2 : Fin 4, Cnt 8 ![c0, c1, c2] = t8 ![c0, c1, c2] := by
    intro c0 c1 c2
    rw [Cnt_succ]
    simp only [Cnt7, sum_pi_succ, sum_pi_zero]
    revert c0 c1 c2
    decide +kernel
  rw [← row_eta r]
  exact h _ _ _

/-- The difference equation of order 4 on every deficit row, from m = 4 on. -/
theorem Cnt_rec (m : ℕ) : ∀ r : Fin 3 → Fin 4, (Cnt (m + 8) r : ℤ) = 4 * Cnt (m + 7) r - 6 * Cnt (m + 6) r + 4 * Cnt (m + 5) r - Cnt (m + 4) r := by
  induction m with
  | zero =>
    intro r
    simp only [Nat.zero_add, Cnt4, Cnt5, Cnt6, Cnt7, Cnt8]
    have h : ∀ c0 c1 c2 : Fin 4, (t8 ![c0, c1, c2] : ℤ) = 4 * t7 ![c0, c1, c2] - 6 * t6 ![c0, c1, c2] + 4 * t5 ![c0, c1, c2] - t4 ![c0, c1, c2] := by
      decide +kernel
    rw [← row_eta r]
    exact h _ _ _
  | succ m ih =>
    intro r
    rw [show m + 1 + 8 = m + 8 + 1 by omega, show m + 1 + 7 = m + 7 + 1 by omega, show m + 1 + 6 = m + 6 + 1 by omega, show m + 1 + 5 = m + 5 + 1 by omega, show m + 1 + 4 = m + 4 + 1 by omega,
      Cnt_hom (m + 8) (by omega), Cnt_hom (m + 7) (by omega), Cnt_hom (m + 6) (by omega), Cnt_hom (m + 5) (by omega), Cnt_hom (m + 4) (by omega)]
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    split_ifs
    · exact ih p
    · simp

/-- The recurrence of a, for n >= 9. -/
theorem a_rec (m : ℕ) : (a (m + 8 + 1) : ℤ) = 4 * a (m + 7 + 1) - 6 * a (m + 6 + 1) + 4 * a (m + 5 + 1) - a (m + 4 + 1) := by
  rw [a_succ, a_succ, a_succ, a_succ, a_succ]
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun r _ => Cnt_rec m r)

lemma v1 : a 1 = 4 := by
  rw [a_succ]
  simp only [Cnt0, sum_pi_succ, sum_pi_zero]
  decide +kernel

lemma v2 : a 2 = 13 := by
  rw [a_succ]
  simp only [Cnt1, sum_pi_succ, sum_pi_zero]
  decide +kernel

lemma v3 : a 3 = 44 := by
  rw [a_succ]
  simp only [Cnt2, sum_pi_succ, sum_pi_zero]
  decide +kernel

lemma v4 : a 4 = 153 := by
  rw [a_succ]
  simp only [Cnt3, sum_pi_succ, sum_pi_zero]
  decide +kernel

lemma v5 : a 5 = 494 := by
  rw [a_succ]
  simp only [Cnt4, sum_pi_succ, sum_pi_zero]
  decide +kernel

lemma v6 : a 6 = 1343 := by
  rw [a_succ]
  simp only [Cnt5, sum_pi_succ, sum_pi_zero]
  decide +kernel

lemma v7 : a 7 = 3016 := by
  rw [a_succ]
  simp only [Cnt6, sum_pi_succ, sum_pi_zero]
  decide +kernel

lemma v8 : a 8 = 5833 := by
  rw [a_succ]
  simp only [Cnt7, sum_pi_succ, sum_pi_zero]
  decide +kernel

/-- Barker's recurrence, for n > 8. -/
theorem recurrence (n : ℕ) (hn : 8 < n) : (a n : ℤ) = 4 * a (n - 1) - 6 * a (n - 2) + 4 * a (n - 3) - a (n - 4) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 + 4 + 1 := ⟨n - 9, by omega⟩
  rw [show m + 4 + 4 + 1 - 1 = m + 7 + 1 by omega, show m + 4 + 4 + 1 - 2 = m + 6 + 1 by omega, show m + 4 + 4 + 1 - 3 = m + 5 + 1 by omega, show m + 4 + 4 + 1 - 4 = m + 4 + 1 by omega]
  rw [show m + 4 + 4 + 1 = m + 8 + 1 by omega]
  exact a_rec m

/-- Barker's g.f., as A(x) (1 - x)^4 = its numerator in Z[[x]]. -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 4 =
    X * (4 - 3 * X + 16 * X ^ 2 + 39 * X ^ 3 + 98 * X ^ 4 + 122 * X ^ 5 + 40 * X ^ 6 + 4 * X ^ 7) := by
  set A : ℤ⟦X⟧ := PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) with hA
  have e1 : A * (1 - X) ^ 4 = A - C 4 * (A * X ^ 1) + C 6 * (A * X ^ 2) - C 4 * (A * X ^ 3) + A * X ^ 4 := by
    simp only [map_ofNat]; ring
  have e2 : (X * (4 - 3 * X + 16 * X ^ 2 + 39 * X ^ 3 + 98 * X ^ 4 + 122 * X ^ 5 + 40 * X ^ 6 + 4 * X ^ 7) : ℤ⟦X⟧) =
      X ^ 1 * C 4 - X ^ 2 * C 3 + X ^ 3 * C 16 + X ^ 4 * C 39 + X ^ 5 * C 98 + X ^ 6 * C 122 + X ^ 7 * C 40 + X ^ 8 * C 4 := by
    simp only [map_ofNat]; ring
  rw [e1, e2]
  ext n
  have hc : ∀ k, coeff k A = if k = 0 then (0 : ℤ) else a k := fun k => by rw [hA, coeff_mk]
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_C, coeff_X_pow, coeff_mul_X_pow', hc]
  rcases Nat.lt_or_ge n 9 with hn | hn
  · interval_cases n <;> simp [v1, v2, v3, v4, v5, v6, v7, v8]
  · obtain ⟨q, rfl⟩ : ∃ q, n = q + 9 := ⟨n - 9, by omega⟩
    have h := recurrence (q + 9) (by omega)
    simp only [show q + 9 - 1 = q + 8 by omega, show q + 9 - 2 = q + 7 by omega, show q + 9 - 3 = q + 6 by omega, show q + 9 - 4 = q + 5 by omega] at h ⊢
    simp only [ show ¬ q + 9 = 0 by omega, show 1 ≤ q + 9 by omega, show ¬ q + 8 = 0 by omega,
      show 2 ≤ q + 9 by omega, show ¬ q + 7 = 0 by omega, show 3 ≤ q + 9 by omega,
      show ¬ q + 6 = 0 by omega, show 4 ≤ q + 9 by omega, show ¬ q + 5 = 0 by omega,
      show ¬ q + 9 = 1 by omega, show ¬ q + 9 = 2 by omega, show ¬ q + 9 = 3 by omega,
      show ¬ q + 9 = 4 by omega, show ¬ q + 9 = 5 by omega, show ¬ q + 9 = 6 by omega,
      show ¬ q + 9 = 7 by omega, show ¬ q + 9 = 8 by omega, if_true, if_false]
    rw [h]
    ring

/-- Controls: the entry's data a(1..33). -/
theorem controls : a 1 = 4 ∧ a 2 = 13 ∧ a 3 = 44 ∧ a 4 = 153 ∧ a 5 = 494 ∧ a 6 = 1343 ∧ a 7 = 3016 ∧
    a 8 = 5833 ∧ a 9 = 10114 ∧ a 10 = 16179 ∧ a 11 = 24348 ∧ a 12 = 34941 ∧ a 13 = 48278 ∧
    a 14 = 64679 ∧ a 15 = 84464 ∧ a 16 = 107953 ∧ a 17 = 135466 ∧ a 18 = 167323 ∧ a 19 = 203844 ∧
    a 20 = 245349 ∧ a 21 = 292158 ∧ a 22 = 344591 ∧ a 23 = 402968 ∧ a 24 = 467609 ∧ a 25 = 538834 ∧
    a 26 = 616963 ∧ a 27 = 702316 ∧ a 28 = 795213 ∧ a 29 = 895974 ∧ a 30 = 1004919 ∧
    a 31 = 1122368 ∧ a 32 = 1248641 ∧ a 33 = 1384058 := by
  have v9 : a 9 = 10114 := by
    have h : (a 9 : ℤ) = 4 * a 8 - 6 * a 7 + 4 * a 6 - a 5 := a_rec 0
    rw [v8, v7, v6, v5] at h
    omega
  have v10 : a 10 = 16179 := by
    have h : (a 10 : ℤ) = 4 * a 9 - 6 * a 8 + 4 * a 7 - a 6 := a_rec 1
    rw [v9, v8, v7, v6] at h
    omega
  have v11 : a 11 = 24348 := by
    have h : (a 11 : ℤ) = 4 * a 10 - 6 * a 9 + 4 * a 8 - a 7 := a_rec 2
    rw [v10, v9, v8, v7] at h
    omega
  have v12 : a 12 = 34941 := by
    have h : (a 12 : ℤ) = 4 * a 11 - 6 * a 10 + 4 * a 9 - a 8 := a_rec 3
    rw [v11, v10, v9, v8] at h
    omega
  have v13 : a 13 = 48278 := by
    have h : (a 13 : ℤ) = 4 * a 12 - 6 * a 11 + 4 * a 10 - a 9 := a_rec 4
    rw [v12, v11, v10, v9] at h
    omega
  have v14 : a 14 = 64679 := by
    have h : (a 14 : ℤ) = 4 * a 13 - 6 * a 12 + 4 * a 11 - a 10 := a_rec 5
    rw [v13, v12, v11, v10] at h
    omega
  have v15 : a 15 = 84464 := by
    have h : (a 15 : ℤ) = 4 * a 14 - 6 * a 13 + 4 * a 12 - a 11 := a_rec 6
    rw [v14, v13, v12, v11] at h
    omega
  have v16 : a 16 = 107953 := by
    have h : (a 16 : ℤ) = 4 * a 15 - 6 * a 14 + 4 * a 13 - a 12 := a_rec 7
    rw [v15, v14, v13, v12] at h
    omega
  have v17 : a 17 = 135466 := by
    have h : (a 17 : ℤ) = 4 * a 16 - 6 * a 15 + 4 * a 14 - a 13 := a_rec 8
    rw [v16, v15, v14, v13] at h
    omega
  have v18 : a 18 = 167323 := by
    have h : (a 18 : ℤ) = 4 * a 17 - 6 * a 16 + 4 * a 15 - a 14 := a_rec 9
    rw [v17, v16, v15, v14] at h
    omega
  have v19 : a 19 = 203844 := by
    have h : (a 19 : ℤ) = 4 * a 18 - 6 * a 17 + 4 * a 16 - a 15 := a_rec 10
    rw [v18, v17, v16, v15] at h
    omega
  have v20 : a 20 = 245349 := by
    have h : (a 20 : ℤ) = 4 * a 19 - 6 * a 18 + 4 * a 17 - a 16 := a_rec 11
    rw [v19, v18, v17, v16] at h
    omega
  have v21 : a 21 = 292158 := by
    have h : (a 21 : ℤ) = 4 * a 20 - 6 * a 19 + 4 * a 18 - a 17 := a_rec 12
    rw [v20, v19, v18, v17] at h
    omega
  have v22 : a 22 = 344591 := by
    have h : (a 22 : ℤ) = 4 * a 21 - 6 * a 20 + 4 * a 19 - a 18 := a_rec 13
    rw [v21, v20, v19, v18] at h
    omega
  have v23 : a 23 = 402968 := by
    have h : (a 23 : ℤ) = 4 * a 22 - 6 * a 21 + 4 * a 20 - a 19 := a_rec 14
    rw [v22, v21, v20, v19] at h
    omega
  have v24 : a 24 = 467609 := by
    have h : (a 24 : ℤ) = 4 * a 23 - 6 * a 22 + 4 * a 21 - a 20 := a_rec 15
    rw [v23, v22, v21, v20] at h
    omega
  have v25 : a 25 = 538834 := by
    have h : (a 25 : ℤ) = 4 * a 24 - 6 * a 23 + 4 * a 22 - a 21 := a_rec 16
    rw [v24, v23, v22, v21] at h
    omega
  have v26 : a 26 = 616963 := by
    have h : (a 26 : ℤ) = 4 * a 25 - 6 * a 24 + 4 * a 23 - a 22 := a_rec 17
    rw [v25, v24, v23, v22] at h
    omega
  have v27 : a 27 = 702316 := by
    have h : (a 27 : ℤ) = 4 * a 26 - 6 * a 25 + 4 * a 24 - a 23 := a_rec 18
    rw [v26, v25, v24, v23] at h
    omega
  have v28 : a 28 = 795213 := by
    have h : (a 28 : ℤ) = 4 * a 27 - 6 * a 26 + 4 * a 25 - a 24 := a_rec 19
    rw [v27, v26, v25, v24] at h
    omega
  have v29 : a 29 = 895974 := by
    have h : (a 29 : ℤ) = 4 * a 28 - 6 * a 27 + 4 * a 26 - a 25 := a_rec 20
    rw [v28, v27, v26, v25] at h
    omega
  have v30 : a 30 = 1004919 := by
    have h : (a 30 : ℤ) = 4 * a 29 - 6 * a 28 + 4 * a 27 - a 26 := a_rec 21
    rw [v29, v28, v27, v26] at h
    omega
  have v31 : a 31 = 1122368 := by
    have h : (a 31 : ℤ) = 4 * a 30 - 6 * a 29 + 4 * a 28 - a 27 := a_rec 22
    rw [v30, v29, v28, v27] at h
    omega
  have v32 : a 32 = 1248641 := by
    have h : (a 32 : ℤ) = 4 * a 31 - 6 * a 30 + 4 * a 29 - a 28 := a_rec 23
    rw [v31, v30, v29, v28] at h
    omega
  have v33 : a 33 = 1384058 := by
    have h : (a 33 : ℤ) = 4 * a 32 - 6 * a 31 + 4 * a 30 - a 29 := a_rec 24
    rw [v32, v31, v30, v29] at h
    omega
  exact ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28, v29, v30, v31, v32, v33⟩

/-- Both of Barker's conjectures. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 4 =
      X * (4 - 3 * X + 16 * X ^ 2 + 39 * X ^ 3 + 98 * X ^ 4 + 122 * X ^ 5 + 40 * X ^ 6 + 4 * X ^ 7) ∧
    ∀ n : ℕ, 8 < n → (a n : ℤ) = 4 * a (n - 1) - 6 * a (n - 2) + 4 * a (n - 3) - a (n - 4) :=
  ⟨gf, recurrence⟩

end OMA.S_oeis_a252933

theorem OMA.solution : type_of% @OMA.S_oeis_a252933.main :=
  OMA.S_oeis_a252933.conjecture
