import OMAStatements.S_oeis_a250856

namespace OMA.S_oeis_a250856_Proof

open OMA.S_oeis_a250856 PowerSeries

private def blkB (p q r s : ℕ) : Bool :=
  Nat.ble (q + r) (s + p) && Nat.ble (min r p) (min s q)

private lemma blkB_iff (p q r s : ℕ) : blkB p q r s = true ↔ Blk p q r s := by
  unfold blkB Blk
  simp only [Bool.and_eq_true, Nat.ble_eq]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by omega, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by omega, h2⟩

private instance (p q r s : ℕ) : Decidable (Blk p q r s) :=
  decidable_of_iff (blkB p q r s = true) (blkB_iff p q r s)

private inductive Tree4 (α : Type) : ℕ → Type
  | leaf : α → Tree4 α 0
  | node : Tree4 α k → Tree4 α k → Tree4 α k → Tree4 α k → Tree4 α (k + 1)

private def Tree4.leafVal : Tree4 α 0 → α
  | .leaf a => a

private def Tree4.child : Tree4 α (k + 1) → Fin 4 → Tree4 α k
  | .node t0 t1 t2 t3, q =>
      match q.1 with
      | 0 => t0
      | 1 => t1
      | 2 => t2
      | _ => t3

private lemma Tree4.child_0 (t0 t1 t2 t3 : Tree4 α k) : (Tree4.node t0 t1 t2 t3).child 0 = t0 := rfl
private lemma Tree4.child_1 (t0 t1 t2 t3 : Tree4 α k) : (Tree4.node t0 t1 t2 t3).child 1 = t1 := rfl
private lemma Tree4.child_2 (t0 t1 t2 t3 : Tree4 α k) : (Tree4.node t0 t1 t2 t3).child 2 = t2 := rfl
private lemma Tree4.child_3 (t0 t1 t2 t3 : Tree4 α k) : (Tree4.node t0 t1 t2 t3).child 3 = t3 := rfl

private def mkN (f : ℕ → Tree4 α k) : Tree4 α (k + 1) :=
  .node (f 0) (f 1) (f 2) (f 3)

private lemma mkN_child (f : ℕ → Tree4 α k) (q : Fin 4) : (mkN f).child q = f q.1 := by
  fin_cases q <;> rfl

private def Tree4.const (v : α) : ∀ k, Tree4 α k
  | 0 => .leaf v
  | k + 1 =>
      let t := Tree4.const v k
      .node t t t t

private lemma Tree4.const_child (v : α) (k : ℕ) (q : Fin 4) :
    (Tree4.const v (k + 1)).child q = Tree4.const v k := by
  fin_cases q <;> rfl

private def Tree4.sum : ∀ {k}, Tree4 ℕ k → ℕ
  | 0, .leaf a => a
  | _ + 1, .node t0 t1 t2 t3 => t0.sum + t1.sum + t2.sum + t3.sum

private lemma Tree4.sum_zero (t : Tree4 ℕ 0) : t.sum = t.leafVal := by
  rcases t with ⟨a⟩
  rfl

private lemma Tree4.sum_node (t : Tree4 ℕ (k + 1)) :
    t.sum = ∑ q : Fin 4, (t.child q).sum := by
  rcases t with ⟨t0, t1, t2, t3⟩
  simp [Tree4.sum, Fin.sum_univ_four, Tree4.child_0, Tree4.child_1, Tree4.child_2, Tree4.child_3]

private def getCol (t : Tree4 α 5) (c : Fin 5 → Fin 4) : α :=
  ((((t.child (c 0)).child (c 1)).child (c 2)).child (c 3)).child (c 4) |>.leafVal

private lemma getCol_const (v : α) (c : Fin 5 → Fin 4) :
    getCol (Tree4.const v 5) c = v := by
  unfold getCol
  rw [Tree4.const_child, Tree4.const_child, Tree4.const_child, Tree4.const_child, Tree4.const_child]
  rfl

private def colEquiv : (Fin 5 → Fin 4) ≃ Fin 4 × Fin 4 × Fin 4 × Fin 4 × Fin 4 where
  toFun c := (c 0, c 1, c 2, c 3, c 4)
  invFun p i :=
    match i with
    | ⟨0, _⟩ => p.1
    | ⟨1, _⟩ => p.2.1
    | ⟨2, _⟩ => p.2.2.1
    | ⟨3, _⟩ => p.2.2.2.1
    | ⟨4, _⟩ => p.2.2.2.2
  left_inv c := by
    funext i
    fin_cases i <;> rfl
  right_inv p := by
    rcases p with ⟨a, b, c, d, e⟩
    rfl

private lemma sum_eq_sum_getCol (t : Tree4 ℕ 5) :
    t.sum = ∑ c : Fin 5 → Fin 4, getCol t c := by
  rw [Fintype.sum_equiv colEquiv _ (fun p => getCol t (colEquiv.symm p))
    (fun c => by simp)]
  simp only [Fintype.sum_prod_type]
  rw [Tree4.sum_node]
  refine Finset.sum_congr rfl fun q0 _ => ?_
  rw [Tree4.sum_node]
  refine Finset.sum_congr rfl fun q1 _ => ?_
  rw [Tree4.sum_node]
  refine Finset.sum_congr rfl fun q2 _ => ?_
  rw [Tree4.sum_node]
  refine Finset.sum_congr rfl fun q3 _ => ?_
  rw [Tree4.sum_node]
  refine Finset.sum_congr rfl fun q4 _ => ?_
  rw [Tree4.sum_zero]
  rfl

private def sum4 (p3 q3 p4 : ℕ) : Tree4 ℕ 1 → ℕ
  | .node (.leaf a0) (.leaf a1) (.leaf a2) (.leaf a3) =>
      (if blkB p3 q3 p4 0 then a0 else 0) +
      (if blkB p3 q3 p4 1 then a1 else 0) +
      (if blkB p3 q3 p4 2 then a2 else 0) +
      (if blkB p3 q3 p4 3 then a3 else 0)

private def sum3 (p2 q2 p3 p4 : ℕ) : Tree4 ℕ 2 → ℕ
  | .node t0 t1 t2 t3 =>
      (if blkB p2 q2 p3 0 then sum4 p3 0 p4 t0 else 0) +
      (if blkB p2 q2 p3 1 then sum4 p3 1 p4 t1 else 0) +
      (if blkB p2 q2 p3 2 then sum4 p3 2 p4 t2 else 0) +
      (if blkB p2 q2 p3 3 then sum4 p3 3 p4 t3 else 0)

private def sum2 (p1 q1 p2 p3 p4 : ℕ) : Tree4 ℕ 3 → ℕ
  | .node t0 t1 t2 t3 =>
      (if blkB p1 q1 p2 0 then sum3 p2 0 p3 p4 t0 else 0) +
      (if blkB p1 q1 p2 1 then sum3 p2 1 p3 p4 t1 else 0) +
      (if blkB p1 q1 p2 2 then sum3 p2 2 p3 p4 t2 else 0) +
      (if blkB p1 q1 p2 3 then sum3 p2 3 p3 p4 t3 else 0)

private def sum1 (p0 q0 p1 p2 p3 p4 : ℕ) : Tree4 ℕ 4 → ℕ
  | .node t0 t1 t2 t3 =>
      (if blkB p0 q0 p1 0 then sum2 p1 0 p2 p3 p4 t0 else 0) +
      (if blkB p0 q0 p1 1 then sum2 p1 1 p2 p3 p4 t1 else 0) +
      (if blkB p0 q0 p1 2 then sum2 p1 2 p2 p3 p4 t2 else 0) +
      (if blkB p0 q0 p1 3 then sum2 p1 3 p2 p3 p4 t3 else 0)

private def sum0 (p0 p1 p2 p3 p4 : ℕ) : Tree4 ℕ 5 → ℕ
  | .node t0 t1 t2 t3 =>
      sum1 p0 0 p1 p2 p3 p4 t0 +
      sum1 p0 1 p1 p2 p3 p4 t1 +
      sum1 p0 2 p1 p2 p3 p4 t2 +
      sum1 p0 3 p1 p2 p3 p4 t3

private def stepTree (t : Tree4 ℕ 5) : Tree4 ℕ 5 :=
  mkN fun p0 => mkN fun p1 => mkN fun p2 => mkN fun p3 => mkN fun p4 =>
    .leaf (sum0 p0 p1 p2 p3 p4 t)

private def colAdj (p q : Fin 5 → Fin 4) : Prop :=
  ∀ i : Fin 4, Blk (p i.castSucc) (q i.castSucc) (p i.succ) (q i.succ)

private instance : DecidableRel colAdj := fun p q =>
  inferInstanceAs (Decidable (∀ i : Fin 4, Blk (p i.castSucc) (q i.castSucc) (p i.succ) (q i.succ)))

private lemma colAdj_iff (p q : Fin 5 → Fin 4) :
    colAdj p q ↔
      blkB (p 0) (q 0) (p 1) (q 1) = true ∧
      blkB (p 1) (q 1) (p 2) (q 2) = true ∧
      blkB (p 2) (q 2) (p 3) (q 3) = true ∧
      blkB (p 3) (q 3) (p 4) (q 4) = true := by
  constructor
  · intro h
    exact ⟨(blkB_iff _ _ _ _).2 (h 0), (blkB_iff _ _ _ _).2 (h 1),
      (blkB_iff _ _ _ _).2 (h 2), (blkB_iff _ _ _ _).2 (h 3)⟩
  · rintro ⟨h0, h1, h2, h3⟩ i
    fin_cases i
    · exact (blkB_iff _ _ _ _).1 h0
    · exact (blkB_iff _ _ _ _).1 h1
    · exact (blkB_iff _ _ _ _).1 h2
    · exact (blkB_iff _ _ _ _).1 h3

private lemma ite_sum_zero {α : Type*} (s : Finset α) (P : Prop) [Decidable P] (f : α → ℕ) :
    (if P then ∑ x ∈ s, f x else 0) = ∑ x ∈ s, if P then f x else 0 := by
  split_ifs <;> simp

private lemma ite_and {P Q : Prop} [Decidable P] [Decidable Q] (a : ℕ) :
    (if P then (if Q then a else 0) else 0) = if P ∧ Q then a else 0 := by
  by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]

private lemma sum4_eq (p3 q3 p4 : ℕ) : ∀ t : Tree4 ℕ 1,
    sum4 p3 q3 p4 t = ∑ q4 : Fin 4, if blkB p3 q3 p4 q4.1 then (t.child q4).leafVal else 0
  | .node (.leaf a0) (.leaf a1) (.leaf a2) (.leaf a3) => by
      simp [sum4, Fin.sum_univ_four, Tree4.child_0, Tree4.child_1, Tree4.child_2, Tree4.child_3,
        Tree4.leafVal]

private lemma sum3_eq (p2 q2 p3 p4 : ℕ) (t : Tree4 ℕ 2) :
    sum3 p2 q2 p3 p4 t =
      ∑ q3 : Fin 4, ∑ q4 : Fin 4,
        if blkB p2 q2 p3 q3.1 = true ∧ blkB p3 q3.1 p4 q4.1 = true
        then ((t.child q3).child q4).leafVal else 0 := by
  have h : sum3 p2 q2 p3 p4 t =
      ∑ q3 : Fin 4, if blkB p2 q2 p3 q3.1 then sum4 p3 q3.1 p4 (t.child q3) else 0 := by
    rcases t with ⟨t0, t1, t2, t3⟩
    simp [sum3, Fin.sum_univ_four, Tree4.child_0, Tree4.child_1, Tree4.child_2, Tree4.child_3]
  rw [h]
  refine Finset.sum_congr rfl fun q3 _ => ?_
  rw [sum4_eq, ite_sum_zero]
  refine Finset.sum_congr rfl fun q4 _ => ite_and _

private lemma sum2_eq (p1 q1 p2 p3 p4 : ℕ) (t : Tree4 ℕ 3) :
    sum2 p1 q1 p2 p3 p4 t =
      ∑ q2 : Fin 4, ∑ q3 : Fin 4, ∑ q4 : Fin 4,
        if blkB p1 q1 p2 q2.1 = true ∧ blkB p2 q2.1 p3 q3.1 = true ∧ blkB p3 q3.1 p4 q4.1 = true
        then (((t.child q2).child q3).child q4).leafVal else 0 := by
  have h : sum2 p1 q1 p2 p3 p4 t =
      ∑ q2 : Fin 4, if blkB p1 q1 p2 q2.1 then sum3 p2 q2.1 p3 p4 (t.child q2) else 0 := by
    rcases t with ⟨t0, t1, t2, t3⟩
    simp [sum2, Fin.sum_univ_four, Tree4.child_0, Tree4.child_1, Tree4.child_2, Tree4.child_3]
  rw [h]
  refine Finset.sum_congr rfl fun q2 _ => ?_
  rw [sum3_eq, ite_sum_zero]
  refine Finset.sum_congr rfl fun q3 _ => ?_
  rw [ite_sum_zero]
  refine Finset.sum_congr rfl fun q4 _ => ite_and _

private lemma sum1_eq (p0 q0 p1 p2 p3 p4 : ℕ) (t : Tree4 ℕ 4) :
    sum1 p0 q0 p1 p2 p3 p4 t =
      ∑ q1 : Fin 4, ∑ q2 : Fin 4, ∑ q3 : Fin 4, ∑ q4 : Fin 4,
        if blkB p0 q0 p1 q1.1 = true ∧ blkB p1 q1.1 p2 q2.1 = true ∧
           blkB p2 q2.1 p3 q3.1 = true ∧ blkB p3 q3.1 p4 q4.1 = true
        then ((((t.child q1).child q2).child q3).child q4).leafVal else 0 := by
  have h : sum1 p0 q0 p1 p2 p3 p4 t =
      ∑ q1 : Fin 4, if blkB p0 q0 p1 q1.1 then sum2 p1 q1.1 p2 p3 p4 (t.child q1) else 0 := by
    rcases t with ⟨t0, t1, t2, t3⟩
    simp [sum1, Fin.sum_univ_four, Tree4.child_0, Tree4.child_1, Tree4.child_2, Tree4.child_3]
  rw [h]
  refine Finset.sum_congr rfl fun q1 _ => ?_
  rw [sum2_eq, ite_sum_zero]
  refine Finset.sum_congr rfl fun q2 _ => ?_
  rw [ite_sum_zero]
  refine Finset.sum_congr rfl fun q3 _ => ?_
  rw [ite_sum_zero]
  refine Finset.sum_congr rfl fun q4 _ => ite_and _

private lemma getCol_stepTree (t : Tree4 ℕ 5) (p : Fin 5 → Fin 4) :
    getCol (stepTree t) p = ∑ q : Fin 5 → Fin 4, if colAdj p q then getCol t q else 0 := by
  have hget : getCol (stepTree t) p = sum0 (p 0).1 (p 1).1 (p 2).1 (p 3).1 (p 4).1 t := by
    simp [stepTree, getCol, mkN_child, Tree4.leafVal]
  rw [hget]
  rw [Fintype.sum_equiv colEquiv _
    (fun q => if colAdj p (colEquiv.symm q) then getCol t (colEquiv.symm q) else 0)
    (fun q => by simp)]
  simp only [Fintype.sum_prod_type]
  have h0 : sum0 (p 0).1 (p 1).1 (p 2).1 (p 3).1 (p 4).1 t =
      ∑ q0 : Fin 4, sum1 (p 0).1 q0.1 (p 1).1 (p 2).1 (p 3).1 (p 4).1 (t.child q0) := by
    rcases t with ⟨t0, t1, t2, t3⟩
    simp [sum0, Fin.sum_univ_four, Tree4.child_0, Tree4.child_1, Tree4.child_2, Tree4.child_3]
  rw [h0]
  refine Finset.sum_congr rfl fun q0 _ => ?_
  rw [sum1_eq]
  refine Finset.sum_congr rfl fun q1 _ => ?_
  refine Finset.sum_congr rfl fun q2 _ => ?_
  refine Finset.sum_congr rfl fun q3 _ => ?_
  refine Finset.sum_congr rfl fun q4 _ => ?_
  simp only [colAdj_iff, colEquiv, Equiv.coe_fn_symm_mk, getCol]

private def vecTree : ℕ → Tree4 ℕ 5
  | 0 => Tree4.const 1 5
  | n + 1 => stepTree (vecTree n)

private def ValidArr (n : ℕ) (x : Fin 5 → Fin (n + 1) → Fin 4) : Prop :=
  ∀ i : Fin 4, ∀ j : Fin n,
    Blk (x i.castSucc j.castSucc) (x i.castSucc j.succ) (x i.succ j.castSucc) (x i.succ j.succ)

private instance (n : ℕ) : DecidablePred (ValidArr n) := fun x =>
  inferInstanceAs (Decidable (∀ i : Fin 4, ∀ j : Fin n,
    Blk (x i.castSucc j.castSucc) (x i.castSucc j.succ) (x i.succ j.castSucc) (x i.succ j.succ)))

private def countStart (n : ℕ) (p : Fin 5 → Fin 4) : ℕ :=
  Fintype.card {x : Fin 5 → Fin (n + 1) → Fin 4 // ValidArr n x ∧ (fun i => x i 0) = p}

private lemma countStart_zero (p : Fin 5 → Fin 4) : countStart 0 p = 1 := by
  unfold countStart
  have : Unique {x : Fin 5 → Fin 1 → Fin 4 // ValidArr 0 x ∧ (fun i => x i 0) = p} :=
    { default := ⟨fun i _ => p i, ⟨fun _ j => Fin.elim0 j, rfl⟩⟩
      uniq := fun ⟨x, _, hx⟩ => Subtype.ext (funext fun i => funext fun j => by
        have hj : j = 0 := Subsingleton.elim j 0
        subst hj
        exact congrFun hx i) }
  exact Fintype.card_unique

private lemma sum_subtype_ite {α : Type*} [Fintype α] (P : α → Prop) [DecidablePred P] (f : α → ℕ) :
    (∑ x : {a : α // P a}, f x.1) = ∑ a : α, if P a then f a else 0 := by
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun (x : {a : α // P a}) _ => x.1)
    (fun x _ => Finset.mem_filter.2 ⟨Finset.mem_univ _, x.2⟩)
    (fun x _ y _ h => Subtype.ext h)
    (fun a ha => ⟨⟨a, (Finset.mem_filter.1 ha).2⟩, Finset.mem_univ _, rfl⟩)
    (fun _ _ => rfl)

private lemma countStart_succ (n : ℕ) (p : Fin 5 → Fin 4) :
    countStart (n + 1) p = ∑ q : Fin 5 → Fin 4, if colAdj p q then countStart n q else 0 := by
  unfold countStart
  let e : {x : Fin 5 → Fin (n + 2) → Fin 4 // ValidArr (n + 1) x ∧ (fun i => x i 0) = p} ≃
      Σ q : {q : Fin 5 → Fin 4 // colAdj p q},
        {y : Fin 5 → Fin (n + 1) → Fin 4 // ValidArr n y ∧ (fun i => y i 0) = q.1} :=
    { toFun := fun ⟨x, hx, hp⟩ =>
        ⟨⟨fun i => x i 1, fun i => by
            have h0 := hx i 0
            have h0p : x i.castSucc 0 = p i.castSucc := congrFun hp i.castSucc
            have h1p : x i.succ 0 = p i.succ := congrFun hp i.succ
            simpa [h0p, h1p] using h0⟩,
          ⟨fun i j => x i j.succ, ⟨fun i j => hx i j.succ, rfl⟩⟩⟩
      invFun := fun ⟨⟨q, hq⟩, ⟨y, hy, hqy⟩⟩ =>
        ⟨fun i => Fin.cons (p i) (y i),
          ⟨fun i j => by
              refine Fin.cases ?_ ?_ j
              · have h0y : y i.castSucc 0 = q i.castSucc := congrFun hqy i.castSucc
                have h1y : y i.succ 0 = q i.succ := congrFun hqy i.succ
                simpa [h0y, h1y] using hq i
              · intro k
                simpa using hy i k,
            rfl⟩⟩
      left_inv := fun ⟨x, _, hp⟩ => Subtype.ext (funext fun i => funext fun j => by
        refine Fin.cases ?_ ?_ j
        · exact (congrFun hp i).symm
        · intro k
          rfl)
      right_inv := fun ⟨⟨_, _⟩, ⟨_, _, hqy⟩⟩ => by
        cases hqy
        rfl }
  rw [Fintype.card_congr e, Fintype.card_sigma]
  exact sum_subtype_ite (colAdj p) (fun q =>
    Fintype.card {y : Fin 5 → Fin (n + 1) → Fin 4 // ValidArr n y ∧ (fun i => y i 0) = q})

private lemma countStart_eq_getCol (n : ℕ) (p : Fin 5 → Fin 4) :
    countStart n p = getCol (vecTree n) p := by
  induction n generalizing p with
  | zero =>
      rw [countStart_zero, vecTree, getCol_const]
  | succ n ih =>
      rw [countStart_succ, vecTree, getCol_stepTree]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [ih q]

private lemma a_eq_sum_vecTree (n : ℕ) : a n = (vecTree n).sum := by
  rw [sum_eq_sum_getCol]
  have ha : a n = Fintype.card {x : Fin 5 → Fin (n + 1) → Fin 4 // ValidArr n x} := by
    unfold a ValidArr
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_congr (Equiv.refl _)
  rw [ha]
  let e : {x : Fin 5 → Fin (n + 1) → Fin 4 // ValidArr n x} ≃
      Σ p : Fin 5 → Fin 4,
        {x : Fin 5 → Fin (n + 1) → Fin 4 // ValidArr n x ∧ (fun i => x i 0) = p} :=
    { toFun := fun ⟨x, hx⟩ => ⟨fun i => x i 0, ⟨x, hx, rfl⟩⟩
      invFun := fun ⟨_, ⟨x, hx, _⟩⟩ => ⟨x, hx⟩
      left_inv := fun ⟨_, _⟩ => rfl
      right_inv := fun ⟨_, ⟨_, _, hp⟩⟩ => by
        cases hp
        rfl }
  rw [Fintype.card_congr e, Fintype.card_sigma]
  refine Finset.sum_congr rfl fun p _ => ?_
  exact countStart_eq_getCol n p

private def allEq8 : ∀ {k},
    Tree4 ℕ k → Tree4 ℕ k → Tree4 ℕ k → Tree4 ℕ k →
    Tree4 ℕ k → Tree4 ℕ k → Tree4 ℕ k → Tree4 ℕ k → Bool
  | 0, .leaf a0, .leaf a1, .leaf a2, .leaf a3, .leaf a4, .leaf a5, .leaf a6, .leaf a7 =>
      decide (a7 + 21 * a5 + 35 * a3 + 7 * a1 = 7 * a6 + 35 * a4 + 21 * a2 + a0)
  | _ + 1,
    .node t00 t01 t02 t03, .node t10 t11 t12 t13, .node t20 t21 t22 t23, .node t30 t31 t32 t33,
    .node t40 t41 t42 t43, .node t50 t51 t52 t53, .node t60 t61 t62 t63, .node t70 t71 t72 t73 =>
      allEq8 t00 t10 t20 t30 t40 t50 t60 t70 &&
      allEq8 t01 t11 t21 t31 t41 t51 t61 t71 &&
      allEq8 t02 t12 t22 t32 t42 t52 t62 t72 &&
      allEq8 t03 t13 t23 t33 t43 t53 t63 t73

private lemma allEq8_child {k : ℕ}
    {t0 t1 t2 t3 t4 t5 t6 t7 : Tree4 ℕ (k + 1)}
    (h : allEq8 t0 t1 t2 t3 t4 t5 t6 t7 = true) (q : Fin 4) :
    allEq8 (t0.child q) (t1.child q) (t2.child q) (t3.child q)
      (t4.child q) (t5.child q) (t6.child q) (t7.child q) = true := by
  rcases t0 with ⟨_, _, _, _⟩
  rcases t1 with ⟨_, _, _, _⟩
  rcases t2 with ⟨_, _, _, _⟩
  rcases t3 with ⟨_, _, _, _⟩
  rcases t4 with ⟨_, _, _, _⟩
  rcases t5 with ⟨_, _, _, _⟩
  rcases t6 with ⟨_, _, _, _⟩
  rcases t7 with ⟨_, _, _, _⟩
  simp only [allEq8, Bool.and_eq_true] at h
  fin_cases q
  · exact h.1.1.1
  · exact h.1.1.2
  · exact h.1.2
  · exact h.2

private lemma allEq8_getCol
    {t0 t1 t2 t3 t4 t5 t6 t7 : Tree4 ℕ 5}
    (h : allEq8 t0 t1 t2 t3 t4 t5 t6 t7 = true) (c : Fin 5 → Fin 4) :
    getCol t7 c + 21 * getCol t5 c + 35 * getCol t3 c + 7 * getCol t1 c =
      7 * getCol t6 c + 35 * getCol t4 c + 21 * getCol t2 c + getCol t0 c := by
  have h1 := allEq8_child h (c 0)
  have h2 := allEq8_child h1 (c 1)
  have h3 := allEq8_child h2 (c 2)
  have h4 := allEq8_child h3 (c 3)
  have h5 := allEq8_child h4 (c 4)
  unfold getCol
  generalize (((((t0.child (c 0)).child (c 1)).child (c 2)).child (c 3)).child (c 4)) = l0 at h5 ⊢
  generalize (((((t1.child (c 0)).child (c 1)).child (c 2)).child (c 3)).child (c 4)) = l1 at h5 ⊢
  generalize (((((t2.child (c 0)).child (c 1)).child (c 2)).child (c 3)).child (c 4)) = l2 at h5 ⊢
  generalize (((((t3.child (c 0)).child (c 1)).child (c 2)).child (c 3)).child (c 4)) = l3 at h5 ⊢
  generalize (((((t4.child (c 0)).child (c 1)).child (c 2)).child (c 3)).child (c 4)) = l4 at h5 ⊢
  generalize (((((t5.child (c 0)).child (c 1)).child (c 2)).child (c 3)).child (c 4)) = l5 at h5 ⊢
  generalize (((((t6.child (c 0)).child (c 1)).child (c 2)).child (c 3)).child (c 4)) = l6 at h5 ⊢
  generalize (((((t7.child (c 0)).child (c 1)).child (c 2)).child (c 3)).child (c 4)) = l7 at h5 ⊢
  rcases l0 with ⟨a0⟩; rcases l1 with ⟨a1⟩; rcases l2 with ⟨a2⟩; rcases l3 with ⟨a3⟩
  rcases l4 with ⟨a4⟩; rcases l5 with ⟨a5⟩; rcases l6 with ⟨a6⟩; rcases l7 with ⟨a7⟩
  simpa [allEq8, Tree4.leafVal] using h5

private def checkBase : Bool :=
  let v0 := vecTree 0
  let v1 := stepTree v0
  let v2 := stepTree v1
  let v3 := stepTree v2
  let v4 := stepTree v3
  let v5 := stepTree v4
  let v6 := stepTree v5
  let v7 := stepTree v6
  allEq8 v0 v1 v2 v3 v4 v5 v6 v7 &&
  decide (v0.sum = 1024) &&
  decide (v1.sum = 12311) &&
  decide (v2.sum = 63631) &&
  decide (v3.sum = 223933) &&
  decide (v4.sum = 626416) &&
  decide (v5.sum = 1499679) &&
  decide (v6.sum = 3204951)

private theorem checkBase_true : checkBase = true := by
  decide +kernel

private lemma base_vec_rel (c : Fin 5 → Fin 4) :
    getCol (vecTree 7) c + 21 * getCol (vecTree 5) c + 35 * getCol (vecTree 3) c + 7 * getCol (vecTree 1) c =
      7 * getCol (vecTree 6) c + 35 * getCol (vecTree 4) c + 21 * getCol (vecTree 2) c + getCol (vecTree 0) c := by
  have h := checkBase_true
  unfold checkBase at h
  simp only [Bool.and_eq_true] at h
  exact allEq8_getCol h.1.1.1.1.1.1.1 c

private lemma a_init :
    a 0 = 1024 ∧ a 1 = 12311 ∧ a 2 = 63631 ∧ a 3 = 223933 ∧
    a 4 = 626416 ∧ a 5 = 1499679 ∧ a 6 = 3204951 := by
  have h := checkBase_true
  unfold checkBase at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [a_eq_sum_vecTree, vecTree]
  exact ⟨h.1.1.1.1.1.1.2, h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

private lemma getCol_vecTree_succ (k : ℕ) (c : Fin 5 → Fin 4) :
    getCol (vecTree (k + 1)) c = ∑ q : Fin 5 → Fin 4, if colAdj c q then getCol (vecTree k) q else 0 :=
  getCol_stepTree (vecTree k) c

private lemma vec_rel_all (m : ℕ) (c : Fin 5 → Fin 4) :
    getCol (vecTree (m + 7)) c + 21 * getCol (vecTree (m + 5)) c +
      35 * getCol (vecTree (m + 3)) c + 7 * getCol (vecTree (m + 1)) c =
    7 * getCol (vecTree (m + 6)) c + 35 * getCol (vecTree (m + 4)) c +
      21 * getCol (vecTree (m + 2)) c + getCol (vecTree m) c := by
  induction m generalizing c with
  | zero => exact base_vec_rel c
  | succ m ih =>
      rw [show m + 1 + 7 = (m + 7) + 1 by omega,
          show m + 1 + 6 = (m + 6) + 1 by omega,
          show m + 1 + 5 = (m + 5) + 1 by omega,
          show m + 1 + 4 = (m + 4) + 1 by omega,
          show m + 1 + 3 = (m + 3) + 1 by omega,
          show m + 1 + 2 = (m + 2) + 1 by omega,
          show m + 1 + 1 = (m + 1) + 1 by omega]
      rw [getCol_vecTree_succ (m + 7), getCol_vecTree_succ (m + 6), getCol_vecTree_succ (m + 5),
          getCol_vecTree_succ (m + 4), getCol_vecTree_succ (m + 3), getCol_vecTree_succ (m + 2),
          getCol_vecTree_succ (m + 1), getCol_vecTree_succ m]
      have hlin : ∀ (k : ℕ) (f : (Fin 5 → Fin 4) → ℕ),
          k * (∑ q : Fin 5 → Fin 4, if colAdj c q then f q else 0) =
            ∑ q : Fin 5 → Fin 4, if colAdj c q then k * f q else 0 := by
        intro k f
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        split_ifs <;> simp
      rw [hlin 21, hlin 35, hlin 7, hlin 7, hlin 35, hlin 21]
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
          ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun q _ => ?_
      by_cases hcq : colAdj c q
      · simp only [if_pos hcq]
        exact ih q
      · simp only [if_neg hcq]

private lemma a_rec_nat (m : ℕ) :
    a (m + 7) + 21 * a (m + 5) + 35 * a (m + 3) + 7 * a (m + 1) =
      7 * a (m + 6) + 35 * a (m + 4) + 21 * a (m + 2) + a m := by
  simp only [a_eq_sum_vecTree, sum_eq_sum_getCol]
  simp only [Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => vec_rel_all m c

private lemma a_rec_int (m : ℕ) :
    (a (m + 7) : ℤ) =
      7 * a (m + 6) - 21 * a (m + 5) + 35 * a (m + 4) -
        35 * a (m + 3) + 21 * a (m + 2) - 7 * a (m + 1) + a m := by
  have h := a_rec_nat m
  omega

private def polyQ (n : ℚ) : ℚ :=
  76 / 9 * n ^ 6 + 1595 / 12 * n ^ 5 + 28765 / 36 * n ^ 4 +
    31373 / 12 * n ^ 3 + 155683 / 36 * n ^ 2 + 10223 / 3 * n + 1024

private lemma polyQ_rec (m : ℕ) :
    polyQ ((m + 7 : ℕ) : ℚ) =
      7 * polyQ ((m + 6 : ℕ) : ℚ) - 21 * polyQ ((m + 5 : ℕ) : ℚ) +
        35 * polyQ ((m + 4 : ℕ) : ℚ) - 35 * polyQ ((m + 3 : ℕ) : ℚ) +
        21 * polyQ ((m + 2 : ℕ) : ℚ) - 7 * polyQ ((m + 1 : ℕ) : ℚ) +
        polyQ (m : ℚ) := by
  unfold polyQ
  push_cast
  ring

private lemma a_eq_polyQ (n : ℕ) : (a n : ℚ) = polyQ (n : ℚ) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := a_init
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => norm_num [h0, polyQ]
    | 1 => norm_num [h1, polyQ]
    | 2 => norm_num [h2, polyQ]
    | 3 => norm_num [h3, polyQ]
    | 4 => norm_num [h4, polyQ]
    | 5 => norm_num [h5, polyQ]
    | 6 => norm_num [h6, polyQ]
    | m + 7 =>
      have hr : (a (m + 7) : ℚ) =
          7 * (a (m + 6) : ℚ) - 21 * (a (m + 5) : ℚ) + 35 * (a (m + 4) : ℚ) -
            35 * (a (m + 3) : ℚ) + 21 * (a (m + 2) : ℚ) - 7 * (a (m + 1) : ℚ) +
            (a m : ℚ) := by
        exact_mod_cast a_rec_int m
      rw [hr, ih (m + 6) (by omega), ih (m + 5) (by omega), ih (m + 4) (by omega),
          ih (m + 3) (by omega), ih (m + 2) (by omega), ih (m + 1) (by omega),
          ih m (by omega), ← polyQ_rec m]

private lemma gf_eq :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G := by
  set F : PowerSeries ℚ := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ))
  set N : PowerSeries ℚ :=
    X * (12311 - 22546 * X + 37047 * X ^ 2 - 35749 * X ^ 3 +
      21160 * X ^ 4 - 7167 * X ^ 5 + 1024 * X ^ 6)
  set D : PowerSeries ℚ := (1 - X : PowerSeries ℚ) ^ 7
  have hD_expand :
      D = 1 - 7 * X + 21 * X ^ 2 - 35 * X ^ 3 + 35 * X ^ 4 - 21 * X ^ 5 + 7 * X ^ 6 - X ^ 7 := by
    dsimp only [D]
    ring
  have hmul : F * D = N := by
    ext n
    have hcoeff : PowerSeries.coeff n (F * D) =
        PowerSeries.coeff n F
        - 7 * PowerSeries.coeff n (F * X ^ 1)
        + 21 * PowerSeries.coeff n (F * X ^ 2)
        - 35 * PowerSeries.coeff n (F * X ^ 3)
        + 35 * PowerSeries.coeff n (F * X ^ 4)
        - 21 * PowerSeries.coeff n (F * X ^ 5)
        + 7 * PowerSeries.coeff n (F * X ^ 6)
        - PowerSeries.coeff n (F * X ^ 7) := by
      rw [hD_expand]
      have hring : F * (1 - 7 * X + 21 * X ^ 2 - 35 * X ^ 3 + 35 * X ^ 4 - 21 * X ^ 5 + 7 * X ^ 6 - X ^ 7) =
          F - (7 : ℚ) • (F * X ^ 1) + (21 : ℚ) • (F * X ^ 2) - (35 : ℚ) • (F * X ^ 3) +
            (35 : ℚ) • (F * X ^ 4) - (21 : ℚ) • (F * X ^ 5) + (7 : ℚ) • (F * X ^ 6) -
            (F * X ^ 7) := by
        simp only [Algebra.smul_def, map_ofNat]
        ring
      rw [hring]
      simp only [map_sub, map_add, map_smul, smul_eq_mul]
    have hN : N =
        (12311 : ℚ) • X - (22546 : ℚ) • X ^ 2 + (37047 : ℚ) • X ^ 3 -
          (35749 : ℚ) • X ^ 4 + (21160 : ℚ) • X ^ 5 - (7167 : ℚ) • X ^ 6 +
          (1024 : ℚ) • X ^ 7 := by
      dsimp only [N]
      simp only [Algebra.smul_def, map_ofNat]
      ring
    rw [hcoeff, hN]
    simp only [map_sub, map_add, map_smul, smul_eq_mul,
      PowerSeries.coeff_mul_X_pow',
      PowerSeries.coeff_X, PowerSeries.coeff_X_pow]
    obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := a_init
    have h7 : a 7 = 6279401 := by
      have hr0 := a_rec_nat 0
      simp only [zero_add] at hr0
      omega
    match n with
    | 0 => simp [F]
    | 1 => simp [F, h1]
    | 2 => norm_num [F, h1, h2]
    | 3 => norm_num [F, h1, h2, h3]
    | 4 => norm_num [F, h1, h2, h3, h4]
    | 5 => norm_num [F, h1, h2, h3, h4, h5]
    | 6 => norm_num [F, h1, h2, h3, h4, h5, h6]
    | 7 => norm_num [F, h1, h2, h3, h4, h5, h6, h7]
    | m + 8 =>
      simp only [F, PowerSeries.coeff_mk,
        show 1 ≤ m + 8 by omega, show 2 ≤ m + 8 by omega, show 3 ≤ m + 8 by omega,
        show 4 ≤ m + 8 by omega, show 5 ≤ m + 8 by omega,
        show 6 ≤ m + 8 by omega, show 7 ≤ m + 8 by omega,
        show m + 8 ≠ 1 by omega, show m + 8 ≠ 2 by omega, show m + 8 ≠ 3 by omega,
        show m + 8 ≠ 4 by omega, show m + 8 ≠ 5 by omega, show m + 8 ≠ 6 by omega,
        show m + 8 ≠ 7 by omega,
        show m + 8 ≠ 0 by omega,
        show m + 8 - 1 = m + 7 by omega, show m + 8 - 2 = m + 6 by omega,
        show m + 8 - 3 = m + 5 by omega, show m + 8 - 4 = m + 4 by omega,
        show m + 8 - 5 = m + 3 by omega, show m + 8 - 6 = m + 2 by omega,
        show m + 8 - 7 = m + 1 by omega,
        show m + 7 ≠ 0 by omega, show m + 6 ≠ 0 by omega, show m + 5 ≠ 0 by omega,
        show m + 4 ≠ 0 by omega, show m + 3 ≠ 0 by omega, show m + 2 ≠ 0 by omega,
        show m + 1 ≠ 0 by omega,
        ↓reduceIte, mul_zero, sub_zero, add_zero]
      have hr : (a (m + 1 + 7) : ℚ) =
          7 * (a (m + 1 + 6) : ℚ) - 21 * (a (m + 1 + 5) : ℚ) + 35 * (a (m + 1 + 4) : ℚ) -
            35 * (a (m + 1 + 3) : ℚ) + 21 * (a (m + 1 + 2) : ℚ) - 7 * (a (m + 1 + 1) : ℚ) +
            (a (m + 1) : ℚ) := by
        exact_mod_cast a_rec_int (m + 1)
      have hr' : (a (m + 8) : ℚ) =
          7 * (a (m + 7) : ℚ) - 21 * (a (m + 6) : ℚ) + 35 * (a (m + 5) : ℚ) -
            35 * (a (m + 4) : ℚ) + 21 * (a (m + 3) : ℚ) - 7 * (a (m + 2) : ℚ) +
            (a (m + 1) : ℚ) := hr
      linarith
  have hD_inv : D * D⁻¹ = 1 := PowerSeries.mul_inv_cancel D (by
    have hc : PowerSeries.constantCoeff D = (1 : ℚ) := by dsimp only [D]; simp
    simp [hc])
  calc
    F = F * 1 := (mul_one F).symm
    _ = F * (D * D⁻¹) := by rw [hD_inv]
    _ = (F * D) * D⁻¹ := by rw [mul_assoc]
    _ = N * D⁻¹ := by rw [hmul]
    _ = G := rfl

private theorem main_proved :
    (∀ n : ℕ, 1 ≤ n → (a n : ℚ) = 76 / 9 * (n : ℚ) ^ 6 + 1595 / 12 * (n : ℚ) ^ 5 + 28765 / 36 * (n : ℚ) ^ 4 + 31373 / 12 * (n : ℚ) ^ 3 + 155683 / 36 * (n : ℚ) ^ 2 + 10223 / 3 * (n : ℚ) + 1024) ∧
    (PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G) ∧
    (∀ n : ℕ, 7 < n → (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7)) := by
  refine ⟨fun n _ => a_eq_polyQ n, gf_eq, ?_⟩
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
  simpa [show m + 7 - 1 = m + 6 by omega, show m + 7 - 2 = m + 5 by omega,
    show m + 7 - 3 = m + 4 by omega, show m + 7 - 4 = m + 3 by omega,
    show m + 7 - 5 = m + 2 by omega, show m + 7 - 6 = m + 1 by omega,
    show m + 7 - 7 = m by omega] using a_rec_int m

end OMA.S_oeis_a250856_Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a250856.main :=
  OMA.S_oeis_a250856_Proof.main_proved
