import OMAStatements.S_oeis_a252832

namespace OMA.S_oeis_a252832

open PowerSeries




/-- The conditions of the entry on one row v with row index i. -/
def RA (i : ℕ) (v : Fin 4 → ℕ) : Prop :=
  (∀ j : Fin 4, i = 0 → j.val = 0 → v j = 0) ∧
  (∀ j : Fin 4, max i j.val ≤ v j + 2 ∧ v j ≤ max i j.val + 2) ∧
  (∀ j j' : Fin 4, j'.val = j.val + 1 → step01 (v j) (v j'))

/-- The conditions of the entry between a row u and the row v below it. -/
def RB (u v : Fin 4 → ℕ) : Prop :=
  (∀ j : Fin 4, step01 (u j) (v j)) ∧
  (∀ j j' : Fin 4, j'.val = j.val + 1 → step01 (u j) (v j'))

theorem good_iff (n : ℕ) (x : Fin n → Fin 4 → ℕ) :
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
theorem le_dist {n : ℕ} {x : Fin n → Fin 4 → ℕ} (h : good n x) :
    ∀ s, ∀ (i : Fin n) (j : Fin 4), i.val + j.val = s → x i j ≤ max i.val j.val := by
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
def ZA (c : ℕ) (r : Fin 4 → Fin 3) : Bool :=
  decide ((∀ j : Fin 4, (r j : ℕ) ≤ max c j.val) ∧
    ∀ j j' : Fin 4, j'.val = j.val + 1 →
      ((r j' : ℕ) = r j + (if c ≤ j.val then 1 else 0) ∨
        (r j' : ℕ) + 1 = r j + (if c ≤ j.val then 1 else 0)))

/-- The conditions between a row p of deficits at a row index i, with c = min i 3, and the row
r of deficits below it: every step down or diagonally down-right changes the value by 0 or 1. -/
def ZB (c : ℕ) (p r : Fin 4 → Fin 3) : Bool :=
  decide ((∀ j : Fin 4, (r j : ℕ) = p j + (if j.val ≤ c then 1 else 0) ∨
      (r j : ℕ) + 1 = p j + (if j.val ≤ c then 1 else 0)) ∧
    ∀ j j' : Fin 4, j'.val = j.val + 1 → ((r j' : ℕ) = p j ∨ (r j' : ℕ) = p j + 1))

/-- The values of a row r of deficits at row index i. -/
def vals (i : ℕ) (r : Fin 4 → Fin 3) : Fin 4 → ℕ := fun j => max i j.val - r j

theorem rowA (i : ℕ) (r : Fin 4 → Fin 3) :
    (RA i (vals i r) ∧ ∀ j : Fin 4, (r j : ℕ) ≤ max i j.val) ↔ ZA (min i 3) r = true := by
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

theorem rowB (i : ℕ) (p r : Fin 4 → Fin 3) (hp : ∀ j : Fin 4, (p j : ℕ) ≤ max i j.val)
    (hr : ∀ j : Fin 4, (r j : ℕ) ≤ max (i + 1) j.val) :
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

theorem bound_of_ZA {i : ℕ} {r : Fin 4 → Fin 3} (h : ZA (min i 3) r = true) (j : Fin 4) :
    (r j : ℕ) ≤ max i j.val :=
  ((rowA i r).2 h).2 j

/-- The deficit form of the conditions on an array of deficits. -/
def GZ (n : ℕ) (z : Fin n → Fin 4 → Fin 3) : Prop :=
  (∀ i : Fin n, ZA (min i.val 3) (z i) = true) ∧
    ∀ i i' : Fin n, i'.val = i.val + 1 → ZB (min i.val 3) (z i) (z i') = true

instance (n : ℕ) : DecidablePred (GZ n) := fun z => by unfold GZ; infer_instance

theorem set_eq (n : ℕ) : {x : Fin n → Fin 4 → ℕ | good n x} =
    (fun z : Fin n → Fin 4 → Fin 3 => fun i => vals i.val (z i)) '' {z | GZ n z} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_image]
  constructor
  · intro hx
    have hd : ∀ i j, x i j ≤ max i.val j.val := fun i j => le_dist hx (i.val + j.val) i j rfl
    have hw := hx.2.1
    let z : Fin n → Fin 4 → Fin 3 := fun i j =>
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
    Set.InjOn (fun z : Fin n → Fin 4 → Fin 3 => fun i => vals i.val (z i)) {z | GZ n z} := by
  intro z hz z' hz' h
  funext i j
  have e := congrFun (congrFun h i) j
  simp only [vals] at e
  have b := bound_of_ZA (hz.1 i) j
  have b' := bound_of_ZA (hz'.1 i) j
  exact Fin.ext (by omega)

theorem a_eq (n : ℕ) :
    a n = (Finset.univ.filter fun z : Fin n → Fin 4 → Fin 3 => GZ n z).card := by
  unfold a
  rw [set_eq, Set.ncard_image_of_injOn (injOn n), ← Set.ncard_coe_finset]
  congr 1
  ext z
  simp

theorem GZ_snoc (m : ℕ) (y : Fin (m + 1) → Fin 4 → Fin 3) (t : Fin 4 → Fin 3) :
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

theorem GZ_one (z : Fin (0 + 1) → Fin 4 → Fin 3) : GZ (0 + 1) z ↔ ZA 0 (z 0) = true := by
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

theorem sum_snoc (m : ℕ) (f : (Fin (m + 1 + 1) → Fin 4 → Fin 3) → ℕ) :
    ∑ z : Fin (m + 1 + 1) → Fin 4 → Fin 3, f z =
      ∑ t : Fin 4 → Fin 3, ∑ y : Fin (m + 1) → Fin 4 → Fin 3, f (Fin.snoc y t) := by
  rw [← (Fin.snocEquiv fun _ => Fin 4 → Fin 3).sum_comp, Fintype.sum_prod_type]
  rfl

/-- The number of deficit arrays with m + 1 rows whose last row is r. -/
def Cnt (m : ℕ) (r : Fin 4 → Fin 3) : ℕ :=
  ∑ z : Fin (m + 1) → Fin 4 → Fin 3, if GZ (m + 1) z ∧ z (Fin.last m) = r then 1 else 0

theorem a_succ (n : ℕ) : a (n + 1) = ∑ r : Fin 4 → Fin 3, Cnt n r := by
  rw [a_eq, Finset.card_filter]
  unfold Cnt
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  rw [Finset.sum_eq_single (z (Fin.last n))]
  · simp
  · intro r _ hr
    simp [Ne.symm hr]
  · simp

theorem Cnt_zero (r : Fin 4 → Fin 3) : Cnt 0 r = if ZA 0 r = true then 1 else 0 := by
  unfold Cnt
  rw [Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin 4 → Fin 3)) _
    (fun t => if ZA 0 t = true ∧ t = r then 1 else 0) (fun z => by
      simp only [Equiv.funUnique_apply, GZ_one]
      rfl)]
  rw [Finset.sum_eq_single r]
  · simp
  · intro t _ ht
    simp [ht]
  · simp

theorem Cnt_succ (m : ℕ) (r : Fin 4 → Fin 3) :
    Cnt (m + 1) r = ∑ p : Fin 4 → Fin 3,
      if (ZA (min (m + 1) 3) r && ZB (min m 3) p r) = true then Cnt m p else 0 := by
  have lhs : Cnt (m + 1) r = ∑ y : Fin (m + 1) → Fin 4 → Fin 3,
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
  have rhs : ∀ p : Fin 4 → Fin 3,
      (if (ZA (min (m + 1) 3) r && ZB (min m 3) p r) = true then Cnt m p else 0) =
        ∑ y : Fin (m + 1) → Fin 4 → Fin 3,
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
theorem Cnt_hom (m : ℕ) (hm : 3 ≤ m) (r : Fin 4 → Fin 3) :
    Cnt (m + 1) r = ∑ p : Fin 4 → Fin 3,
      if (ZA 3 r && ZB 3 p r) = true then Cnt m p else 0 := by
  rw [Cnt_succ, Nat.min_eq_right (by omega : 3 ≤ m + 1), Nat.min_eq_right hm]

theorem sum_pi_succ {m : ℕ} (g : (Fin (m + 1) → Fin 3) → ℕ) :
    ∑ p, g p = ∑ c : Fin 3, ∑ q : Fin m → Fin 3, g (Fin.cons c q) := by
  rw [← (Fin.consEquiv fun _ => Fin 3).sum_comp, Fintype.sum_prod_type]
  rfl

theorem sum_pi_zero (g : (Fin 0 → Fin 3) → ℕ) : ∑ p, g p = g ![] := by
  rw [Fintype.sum_unique]
  exact congrArg g (Subsingleton.elim _ _)

theorem row_eta (r : Fin 4 → Fin 3) : ![r 0, r 1, r 2, r 3] = r := by
  funext j
  fin_cases j <;> rfl

/-- The position of a row of deficits in the tables. -/
def code (r : Fin 4 → Fin 3) : ℕ := (r 0 : ℕ) * 27 + (r 1 : ℕ) * 9 + (r 2 : ℕ) * 3 + (r 3 : ℕ)

/-- The table of Cnt 0: the base 2^15 digit at position `code r` is Cnt 0 r. -/
def t0 (r : Fin 4 → Fin 3) : ℕ :=
  57896044618659743266559627593479555006503865068986596122193353923993958121473 / 32768 ^ code r % 32768

/-- The table of Cnt 1: the base 2^15 digit at position `code r` is Cnt 1 r. -/
def t1 (r : Fin 4 → Fin 3) : ℕ :=
  4784065733064082924533238480135303662477812566536181040833802802247362470534524386983639660651997690745187749051964975398797379018011223149927078336594595242786231339593235592797527817992029727719426 / 32768 ^ code r % 32768

/-- The table of Cnt 2: the base 2^15 digit at position `code r` is Cnt 2 r. -/
def t2 (r : Fin 4 → Fin 3) : ℕ :=
  17218479456387218813665807092953430542310820174303951835727036772040993001513200874165445426875756903164603990119253768158743518652536200212923283614738002591278956606059815378516932039079691175949451357108369944341726074085547671653197440407981441351681827861265955536742256070314391633617775028954889267910752368777570266479513071304935393529344172239547072517 / 32768 ^ code r % 32768

/-- The table of Cnt 3: the base 2^15 digit at position `code r` is Cnt 3 r. -/
def t3 (r : Fin 4 → Fin 3) : ℕ :=
  327177908452221464791870611139855121439865008039496682531002631411671520771542705719230905403878763021452694319237059887683613570469896148384329507609218953457891588910260847098430139367157688854012613648505525406848716735235727998168054009210687044707907296541623322338778083058207704935326078560418006955342216281517923924291003838284724577612013700811897962511 / 32768 ^ code r % 32768

/-- The table of Cnt 4: the base 2^15 digit at position `code r` is Cnt 4 r. -/
def t4 (r : Fin 4 → Fin 3) : ℕ :=
  4614735356580998547700940931374534562051170236586718555181413707728061903508920206441708129949274265709494866636737369606332203591138734404006873487822360234959289341151054070785424673478604133575951807372721633497315241980370437894460720530684972746932553146247754383001004826017091510529723802304070854974543055909865535368415625314695840400043074263113032269839 / 32768 ^ code r % 32768

/-- The table of Cnt 5: the base 2^15 digit at position `code r` is Cnt 5 r. -/
def t5 (r : Fin 4 → Fin 3) : ℕ :=
  21506292281132441629993142546534514743899627237658352990633549837164032493586641585204873906137039443776755136919747833419962542117986451439550013651849208962241604028208654309015841161668263413362426338859396832453551331716948006959943969416811603036324909292120211693559225101015941288772485565021199242194054388006292852600157138024703678598707334571351783505935 / 32768 ^ code r % 32768

/-- The table of Cnt 6: the base 2^15 digit at position `code r` is Cnt 6 r. -/
def t6 (r : Fin 4 → Fin 3) : ℕ :=
  54066686529646597933188316061965849175409717092102884092142054451678311389782836144754197749003343449065814298879603356469232060343491978278350025645053866839579689770461587940351493794230451593828875852170636582409387048951222023501860768621742499393113920451430294845498296066371246768087862407065409228518775837802513967374403618290005146734564503826430307598351 / 32768 ^ code r % 32768

/-- The table of Cnt 7: the base 2^15 digit at position `code r` is Cnt 7 r. -/
def t7 (r : Fin 4 → Fin 3) : ℕ :=
  103070731286340606096436208395318627259582672489938454573161464552826247414294324535010495331626320517745910985385544792286285820817659925370727264485384610109546200061590736462784139886398231705964490777612894470655984285897684653915190736560070367650270616945548554008913070026567727711618403746951623227654308738284045197192075474100282083509336635412102871253007 / 32768 ^ code r % 32768

/-- The table of Cnt 8: the base 2^15 digit at position `code r` is Cnt 8 r. -/
def t8 (r : Fin 4 → Fin 3) : ℕ :=
  168604516321164934853028783316881935407992355643404767379044781997718894502397888719888378069995901912780923754162169352380381111491011867047096448813134922030385833685509636230866078679225264737050314084897446624084673380701658230770017575313794683828773089864376669791893839431035601980714296228416379186363588883001996935386285745467665178142585737693170245828623 / 32768 ^ code r % 32768

/-- The table of Cnt 9: the base 2^15 digit at position `code r` is Cnt 9 r. -/
def t9 (r : Fin 4 → Fin 3) : ℕ :=
  250668041634119584202966040826655773620638766552501822509792006786356252654093528699387845964112087634170852605209477036751517932363547803307457578628304802602098590642218287244597310172711550687086345774024293042695454333363142754066341284882915447928621339207914642194440604279774869575375539851459677104646616271956369181957034432392154430634311810669632431325199 / 32768 ^ code r % 32768

lemma Cnt0 (r : Fin 4 → Fin 3) : Cnt 0 r = t0 r := by
  have h : ∀ c0 c1 c2 c3 : Fin 3, Cnt 0 ![c0, c1, c2, c3] = t0 ![c0, c1, c2, c3] := by
    intro c0 c1 c2 c3
    rw [Cnt_zero]
    revert c0 c1 c2 c3
    decide +kernel
  rw [← row_eta r]
  exact h _ _ _ _

lemma Cnt1 (r : Fin 4 → Fin 3) : Cnt 1 r = t1 r := by
  have h : ∀ c0 c1 c2 c3 : Fin 3, Cnt 1 ![c0, c1, c2, c3] = t1 ![c0, c1, c2, c3] := by
    intro c0 c1 c2 c3
    rw [Cnt_succ]
    simp only [Cnt0, sum_pi_succ, sum_pi_zero]
    revert c0 c1 c2 c3
    decide +kernel
  rw [← row_eta r]
  exact h _ _ _ _

lemma Cnt2 (r : Fin 4 → Fin 3) : Cnt 2 r = t2 r := by
  have h : ∀ c0 c1 c2 c3 : Fin 3, Cnt 2 ![c0, c1, c2, c3] = t2 ![c0, c1, c2, c3] := by
    intro c0 c1 c2 c3
    rw [Cnt_succ]
    simp only [Cnt1, sum_pi_succ, sum_pi_zero]
    revert c0 c1 c2 c3
    decide +kernel
  rw [← row_eta r]
  exact h _ _ _ _

lemma Cnt3 (r : Fin 4 → Fin 3) : Cnt 3 r = t3 r := by
  have h : ∀ c0 c1 c2 c3 : Fin 3, Cnt 3 ![c0, c1, c2, c3] = t3 ![c0, c1, c2, c3] := by
    intro c0 c1 c2 c3
    rw [Cnt_succ]
    simp only [Cnt2, sum_pi_succ, sum_pi_zero]
    revert c0 c1 c2 c3
    decide +kernel
  rw [← row_eta r]
  exact h _ _ _ _

lemma Cnt4 (r : Fin 4 → Fin 3) : Cnt 4 r = t4 r := by
  have h : ∀ c0 c1 c2 c3 : Fin 3, Cnt 4 ![c0, c1, c2, c3] = t4 ![c0, c1, c2, c3] := by
    intro c0 c1 c2 c3
    rw [Cnt_succ]
    simp only [Cnt3, sum_pi_succ, sum_pi_zero]
    revert c0 c1 c2 c3
    decide +kernel
  rw [← row_eta r]
  exact h _ _ _ _

lemma Cnt5 (r : Fin 4 → Fin 3) : Cnt 5 r = t5 r := by
  have h : ∀ c0 c1 c2 c3 : Fin 3, Cnt 5 ![c0, c1, c2, c3] = t5 ![c0, c1, c2, c3] := by
    intro c0 c1 c2 c3
    rw [Cnt_succ]
    simp only [Cnt4, sum_pi_succ, sum_pi_zero]
    revert c0 c1 c2 c3
    decide +kernel
  rw [← row_eta r]
  exact h _ _ _ _

lemma Cnt6 (r : Fin 4 → Fin 3) : Cnt 6 r = t6 r := by
  have h : ∀ c0 c1 c2 c3 : Fin 3, Cnt 6 ![c0, c1, c2, c3] = t6 ![c0, c1, c2, c3] := by
    intro c0 c1 c2 c3
    rw [Cnt_succ]
    simp only [Cnt5, sum_pi_succ, sum_pi_zero]
    revert c0 c1 c2 c3
    decide +kernel
  rw [← row_eta r]
  exact h _ _ _ _

lemma Cnt7 (r : Fin 4 → Fin 3) : Cnt 7 r = t7 r := by
  have h : ∀ c0 c1 c2 c3 : Fin 3, Cnt 7 ![c0, c1, c2, c3] = t7 ![c0, c1, c2, c3] := by
    intro c0 c1 c2 c3
    rw [Cnt_succ]
    simp only [Cnt6, sum_pi_succ, sum_pi_zero]
    revert c0 c1 c2 c3
    decide +kernel
  rw [← row_eta r]
  exact h _ _ _ _

lemma Cnt8 (r : Fin 4 → Fin 3) : Cnt 8 r = t8 r := by
  have h : ∀ c0 c1 c2 c3 : Fin 3, Cnt 8 ![c0, c1, c2, c3] = t8 ![c0, c1, c2, c3] := by
    intro c0 c1 c2 c3
    rw [Cnt_succ]
    simp only [Cnt7, sum_pi_succ, sum_pi_zero]
    revert c0 c1 c2 c3
    decide +kernel
  rw [← row_eta r]
  exact h _ _ _ _

lemma Cnt9 (r : Fin 4 → Fin 3) : Cnt 9 r = t9 r := by
  have h : ∀ c0 c1 c2 c3 : Fin 3, Cnt 9 ![c0, c1, c2, c3] = t9 ![c0, c1, c2, c3] := by
    intro c0 c1 c2 c3
    rw [Cnt_succ]
    simp only [Cnt8, sum_pi_succ, sum_pi_zero]
    revert c0 c1 c2 c3
    decide +kernel
  rw [← row_eta r]
  exact h _ _ _ _

/-- The difference equation of order 3 on every deficit row, from m = 6 on. -/
theorem Cnt_rec (m : ℕ) : ∀ r : Fin 4 → Fin 3, (Cnt (m + 9) r : ℤ) = 3 * Cnt (m + 8) r - 3 * Cnt (m + 7) r + Cnt (m + 6) r := by
  induction m with
  | zero =>
    intro r
    simp only [Nat.zero_add, Cnt6, Cnt7, Cnt8, Cnt9]
    have h : ∀ c0 c1 c2 c3 : Fin 3, (t9 ![c0, c1, c2, c3] : ℤ) = 3 * t8 ![c0, c1, c2, c3] - 3 * t7 ![c0, c1, c2, c3] + t6 ![c0, c1, c2, c3] := by
      decide +kernel
    rw [← row_eta r]
    exact h _ _ _ _
  | succ m ih =>
    intro r
    rw [show m + 1 + 9 = m + 9 + 1 by omega, show m + 1 + 8 = m + 8 + 1 by omega, show m + 1 + 7 = m + 7 + 1 by omega, show m + 1 + 6 = m + 6 + 1 by omega,
      Cnt_hom (m + 9) (by omega), Cnt_hom (m + 8) (by omega), Cnt_hom (m + 7) (by omega), Cnt_hom (m + 6) (by omega)]
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    split_ifs
    · exact ih p
    · simp

/-- The recurrence of a, for n >= 10. -/
theorem a_rec (m : ℕ) : (a (m + 9 + 1) : ℤ) = 3 * a (m + 8 + 1) - 3 * a (m + 7 + 1) + a (m + 6 + 1) := by
  rw [a_succ, a_succ, a_succ, a_succ]
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun r _ => Cnt_rec m r)

lemma v1 : a 1 = 7 := by
  rw [a_succ]
  simp only [Cnt0, sum_pi_succ, sum_pi_zero]
  decide +kernel

lemma v2 : a 2 = 29 := by
  rw [a_succ]
  simp only [Cnt1, sum_pi_succ, sum_pi_zero]
  decide +kernel

lemma v3 : a 3 = 127 := by
  rw [a_succ]
  simp only [Cnt2, sum_pi_succ, sum_pi_zero]
  decide +kernel

lemma v4 : a 4 = 493 := by
  rw [a_succ]
  simp only [Cnt3, sum_pi_succ, sum_pi_zero]
  decide +kernel

lemma v5 : a 5 = 1474 := by
  rw [a_succ]
  simp only [Cnt4, sum_pi_succ, sum_pi_zero]
  decide +kernel

lemma v6 : a 6 = 3365 := by
  rw [a_succ]
  simp only [Cnt5, sum_pi_succ, sum_pi_zero]
  decide +kernel

lemma v7 : a 7 = 6211 := by
  rw [a_succ]
  simp only [Cnt6, sum_pi_succ, sum_pi_zero]
  decide +kernel

lemma v8 : a 8 = 10017 := by
  rw [a_succ]
  simp only [Cnt7, sum_pi_succ, sum_pi_zero]
  decide +kernel

lemma v9 : a 9 = 14783 := by
  rw [a_succ]
  simp only [Cnt8, sum_pi_succ, sum_pi_zero]
  decide +kernel

/-- Barker's recurrence, for n > 8. -/
theorem recurrence (n : ℕ) (hn : 8 < n) : (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3) := by
  rcases Nat.lt_or_ge n 10 with h | h
  · interval_cases n
    · show (a 9 : ℤ) = 3 * a 8 - 3 * a 7 + a 6
      rw [v9, v8, v7, v6]
      norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 + 3 + 1 := ⟨n - 10, by omega⟩
    rw [show m + 6 + 3 + 1 - 1 = m + 8 + 1 by omega, show m + 6 + 3 + 1 - 2 = m + 7 + 1 by omega, show m + 6 + 3 + 1 - 3 = m + 6 + 1 by omega]
    rw [show m + 6 + 3 + 1 = m + 9 + 1 by omega]
    exact a_rec m

/-- Barker's g.f., as A(x) (1 - x)^3 = its numerator in Z[[x]]. -/
theorem gf : PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 3 =
    X * (7 + 8 * X + 61 * X ^ 2 + 192 * X ^ 3 + 347 * X ^ 4 + 295 * X ^ 5 + 45 * X ^ 6 +
        5 * X ^ 7) := by
  set A : ℤ⟦X⟧ := PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) with hA
  have e1 : A * (1 - X) ^ 3 = A - C 3 * (A * X ^ 1) + C 3 * (A * X ^ 2) - A * X ^ 3 := by
    simp only [map_ofNat]; ring
  have e2 : (X * (7 + 8 * X + 61 * X ^ 2 + 192 * X ^ 3 + 347 * X ^ 4 + 295 * X ^ 5 + 45 * X ^ 6 +
        5 * X ^ 7) : ℤ⟦X⟧) =
      X ^ 1 * C 7 + X ^ 2 * C 8 + X ^ 3 * C 61 + X ^ 4 * C 192 + X ^ 5 * C 347 + X ^ 6 * C 295 + X ^ 7 * C 45 + X ^ 8 * C 5 := by
    simp only [map_ofNat]; ring
  rw [e1, e2]
  ext n
  have hc : ∀ k, coeff k A = if k = 0 then (0 : ℤ) else a k := fun k => by rw [hA, coeff_mk]
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_C, coeff_X_pow, coeff_mul_X_pow', hc]
  rcases Nat.lt_or_ge n 9 with hn | hn
  · interval_cases n <;> simp [v1, v2, v3, v4, v5, v6, v7, v8]
  · obtain ⟨q, rfl⟩ : ∃ q, n = q + 9 := ⟨n - 9, by omega⟩
    have h := recurrence (q + 9) (by omega)
    simp only [show q + 9 - 1 = q + 8 by omega, show q + 9 - 2 = q + 7 by omega, show q + 9 - 3 = q + 6 by omega] at h ⊢
    simp only [ show ¬ q + 9 = 0 by omega, show 1 ≤ q + 9 by omega, show ¬ q + 8 = 0 by omega,
      show 2 ≤ q + 9 by omega, show ¬ q + 7 = 0 by omega, show 3 ≤ q + 9 by omega,
      show ¬ q + 6 = 0 by omega, show ¬ q + 9 = 1 by omega, show ¬ q + 9 = 2 by omega,
      show ¬ q + 9 = 3 by omega, show ¬ q + 9 = 4 by omega, show ¬ q + 9 = 5 by omega,
      show ¬ q + 9 = 6 by omega, show ¬ q + 9 = 7 by omega, show ¬ q + 9 = 8 by omega, if_true,
      if_false]
    rw [h]
    ring

/-- Controls: the entry's data a(1..34). -/
theorem controls : a 1 = 7 ∧ a 2 = 29 ∧ a 3 = 127 ∧ a 4 = 493 ∧ a 5 = 1474 ∧ a 6 = 3365 ∧
    a 7 = 6211 ∧ a 8 = 10017 ∧ a 9 = 14783 ∧ a 10 = 20509 ∧ a 11 = 27195 ∧ a 12 = 34841 ∧
    a 13 = 43447 ∧ a 14 = 53013 ∧ a 15 = 63539 ∧ a 16 = 75025 ∧ a 17 = 87471 ∧ a 18 = 100877 ∧
    a 19 = 115243 ∧ a 20 = 130569 ∧ a 21 = 146855 ∧ a 22 = 164101 ∧ a 23 = 182307 ∧ a 24 = 201473 ∧
    a 25 = 221599 ∧ a 26 = 242685 ∧ a 27 = 264731 ∧ a 28 = 287737 ∧ a 29 = 311703 ∧ a 30 = 336629 ∧
    a 31 = 362515 ∧ a 32 = 389361 ∧ a 33 = 417167 ∧ a 34 = 445933 := by
  have v10 : a 10 = 20509 := by
    have h : (a 10 : ℤ) = 3 * a 9 - 3 * a 8 + a 7 := a_rec 0
    rw [v9, v8, v7] at h
    omega
  have v11 : a 11 = 27195 := by
    have h : (a 11 : ℤ) = 3 * a 10 - 3 * a 9 + a 8 := a_rec 1
    rw [v10, v9, v8] at h
    omega
  have v12 : a 12 = 34841 := by
    have h : (a 12 : ℤ) = 3 * a 11 - 3 * a 10 + a 9 := a_rec 2
    rw [v11, v10, v9] at h
    omega
  have v13 : a 13 = 43447 := by
    have h : (a 13 : ℤ) = 3 * a 12 - 3 * a 11 + a 10 := a_rec 3
    rw [v12, v11, v10] at h
    omega
  have v14 : a 14 = 53013 := by
    have h : (a 14 : ℤ) = 3 * a 13 - 3 * a 12 + a 11 := a_rec 4
    rw [v13, v12, v11] at h
    omega
  have v15 : a 15 = 63539 := by
    have h : (a 15 : ℤ) = 3 * a 14 - 3 * a 13 + a 12 := a_rec 5
    rw [v14, v13, v12] at h
    omega
  have v16 : a 16 = 75025 := by
    have h : (a 16 : ℤ) = 3 * a 15 - 3 * a 14 + a 13 := a_rec 6
    rw [v15, v14, v13] at h
    omega
  have v17 : a 17 = 87471 := by
    have h : (a 17 : ℤ) = 3 * a 16 - 3 * a 15 + a 14 := a_rec 7
    rw [v16, v15, v14] at h
    omega
  have v18 : a 18 = 100877 := by
    have h : (a 18 : ℤ) = 3 * a 17 - 3 * a 16 + a 15 := a_rec 8
    rw [v17, v16, v15] at h
    omega
  have v19 : a 19 = 115243 := by
    have h : (a 19 : ℤ) = 3 * a 18 - 3 * a 17 + a 16 := a_rec 9
    rw [v18, v17, v16] at h
    omega
  have v20 : a 20 = 130569 := by
    have h : (a 20 : ℤ) = 3 * a 19 - 3 * a 18 + a 17 := a_rec 10
    rw [v19, v18, v17] at h
    omega
  have v21 : a 21 = 146855 := by
    have h : (a 21 : ℤ) = 3 * a 20 - 3 * a 19 + a 18 := a_rec 11
    rw [v20, v19, v18] at h
    omega
  have v22 : a 22 = 164101 := by
    have h : (a 22 : ℤ) = 3 * a 21 - 3 * a 20 + a 19 := a_rec 12
    rw [v21, v20, v19] at h
    omega
  have v23 : a 23 = 182307 := by
    have h : (a 23 : ℤ) = 3 * a 22 - 3 * a 21 + a 20 := a_rec 13
    rw [v22, v21, v20] at h
    omega
  have v24 : a 24 = 201473 := by
    have h : (a 24 : ℤ) = 3 * a 23 - 3 * a 22 + a 21 := a_rec 14
    rw [v23, v22, v21] at h
    omega
  have v25 : a 25 = 221599 := by
    have h : (a 25 : ℤ) = 3 * a 24 - 3 * a 23 + a 22 := a_rec 15
    rw [v24, v23, v22] at h
    omega
  have v26 : a 26 = 242685 := by
    have h : (a 26 : ℤ) = 3 * a 25 - 3 * a 24 + a 23 := a_rec 16
    rw [v25, v24, v23] at h
    omega
  have v27 : a 27 = 264731 := by
    have h : (a 27 : ℤ) = 3 * a 26 - 3 * a 25 + a 24 := a_rec 17
    rw [v26, v25, v24] at h
    omega
  have v28 : a 28 = 287737 := by
    have h : (a 28 : ℤ) = 3 * a 27 - 3 * a 26 + a 25 := a_rec 18
    rw [v27, v26, v25] at h
    omega
  have v29 : a 29 = 311703 := by
    have h : (a 29 : ℤ) = 3 * a 28 - 3 * a 27 + a 26 := a_rec 19
    rw [v28, v27, v26] at h
    omega
  have v30 : a 30 = 336629 := by
    have h : (a 30 : ℤ) = 3 * a 29 - 3 * a 28 + a 27 := a_rec 20
    rw [v29, v28, v27] at h
    omega
  have v31 : a 31 = 362515 := by
    have h : (a 31 : ℤ) = 3 * a 30 - 3 * a 29 + a 28 := a_rec 21
    rw [v30, v29, v28] at h
    omega
  have v32 : a 32 = 389361 := by
    have h : (a 32 : ℤ) = 3 * a 31 - 3 * a 30 + a 29 := a_rec 22
    rw [v31, v30, v29] at h
    omega
  have v33 : a 33 = 417167 := by
    have h : (a 33 : ℤ) = 3 * a 32 - 3 * a 31 + a 30 := a_rec 23
    rw [v32, v31, v30] at h
    omega
  have v34 : a 34 = 445933 := by
    have h : (a 34 : ℤ) = 3 * a 33 - 3 * a 32 + a 31 := a_rec 24
    rw [v33, v32, v31] at h
    omega
  exact ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28, v29, v30, v31, v32, v33, v34⟩

/-- Both of Barker's conjectures. -/
theorem conjecture :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 3 =
      X * (7 + 8 * X + 61 * X ^ 2 + 192 * X ^ 3 + 347 * X ^ 4 + 295 * X ^ 5 + 45 * X ^ 6 +
        5 * X ^ 7) ∧
    ∀ n : ℕ, 8 < n → (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3) :=
  ⟨gf, recurrence⟩

end OMA.S_oeis_a252832

theorem OMA.solution : type_of% @OMA.S_oeis_a252832.main :=
  OMA.S_oeis_a252832.conjecture
