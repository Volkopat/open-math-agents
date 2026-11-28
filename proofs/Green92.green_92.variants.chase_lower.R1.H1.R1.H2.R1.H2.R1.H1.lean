import OMAReductions.R_Green92_green_92_variants_chase_lower_R1_H1_R1_H2_R1_H2_R1

/-!
Proof of the nearby-position second moment bound for Chase's lower bound
(`Green92.green_92.variants.chase_lower.R1.H1.R1.H2.R1.H2.R1.H1`).

Method:
1. Count subsequences of the alternating word `(0,1)^(2k+1)` to show
   `∑ w ∈ U, B w ≤ 2 ^ n`.
2. Express `A w j = P k w j - P (k+1) w j` exactly as
   `((m2 * (a + 1) - m1 * (b + 1)) / ((a + 1) * (b + 1))) * C(a + 1, m1) * C(b + 1, m2)`
   with `a = k + c (w.take j)`, `b = k + c (w.drop (j + 1))`.
3. Bound the hypergeometric peak by `O(1 / √k)` via Bernoulli's inequality on consecutive
   ratios, and the tail `|j - μ(j)| > 20 * √k * log k` by `O(k^(-4))` via exponential decay.
4. Use `c (w.take (j + 2)) ≤ c (w.take j) + 1` to show at most `O(√k * log k)` positions
   lie in the central regime, giving `∑ j, (A w j / B w)^2 ≤ C * (log n)^3 / n^(3/2)`
   pointwise for every `w ∈ U.filter E`.
-/

section Green92ChaseH1

open Finset Filter Real

private def cnt (w : List Bool) : ℕ :=
  (w.zip w.tail).count (false, true)

private def F (a : ℕ) (w : List Bool) : ℕ :=
  (a + cnt w).choose w.length

-- Step 1: Properties of `cnt` under append, take, drop

private lemma zip_tail_append_singleton (v : List Bool) (x : Bool) :
    (v ++ [x]).zip (v ++ [x]).tail =
      match v.getLast? with
      | none => []
      | some y => v.zip v.tail ++ [(y, x)] := by
  induction v with
  | nil => simp
  | cons a t ih =>
    cases t with
    | nil => simp
    | cons b r =>
      simp only [List.cons_append, List.tail_cons, List.zip_cons_cons, List.getLast?_cons_cons]
      have iht : (b :: (r ++ [x])).zip (r ++ [x]) =
          match (b :: r).getLast? with
          | none => []
          | some y => (b :: r).zip r ++ [(y, x)] := by
        simpa only [List.cons_append, List.tail_cons] using ih
      cases hlast : (b :: r).getLast? with
      | none =>
        exfalso
        exact List.cons_ne_nil b r (List.getLast?_eq_none_iff.mp hlast)
      | some y =>
        rw [hlast] at iht
        simp only [iht, List.cons_append]

private lemma cnt_append_false (v : List Bool) : cnt (v ++ [false]) = cnt v := by
  unfold cnt
  rw [zip_tail_append_singleton]
  cases hv : v.getLast? with
  | none =>
    have hnil : v = [] := List.getLast?_eq_none_iff.mp hv
    subst hnil; simp
  | some y => simp [List.count_append]

private lemma cnt_append_true_of_last_true (v : List Bool)
    (h : v.getLast? ≠ some false) : cnt (v ++ [true]) = cnt v := by
  unfold cnt
  rw [zip_tail_append_singleton]
  cases hv : v.getLast? with
  | none =>
    have hnil : v = [] := List.getLast?_eq_none_iff.mp hv
    subst hnil; simp
  | some y =>
    cases y
    · exact (h hv).elim
    · simp [List.count_append]

private lemma cnt_append_false_true (u : List Bool) :
    cnt (u ++ [false, true]) = cnt u + 1 := by
  have h1 : u ++ [false, true] = (u ++ [false]) ++ [true] := by simp
  rw [h1]
  unfold cnt
  rw [zip_tail_append_singleton]
  have hlast : (u ++ [false]).getLast? = some false := by simp
  rw [hlast, List.count_append]
  have h2 : ((u ++ [false]).zip (u ++ [false]).tail).count (false, true) = cnt u :=
    cnt_append_false u
  rw [h2]
  have h3 : [(false, true)].count (false, true) = 1 := by decide
  rw [h3]
  rfl

-- Alternating word trace counting: ∑_{w ∈ U} F a w ≤ 4 ^ a

private def altWord (a : ℕ) (i : Fin (2 * a)) : Bool :=
  decide (i.val % 2 = 1)

private def altTrace (a : ℕ) (S : Finset (Fin (2 * a))) : List Bool :=
  ((List.finRange (2 * a)).filter (fun i => i ∈ S)).map (altWord a)

private lemma list_finRange_two_succ (a : ℕ) :
    List.finRange (2 * (a + 1)) =
      (List.finRange (2 * a)).map (Fin.castAdd 2) ++
        [⟨2 * a, by omega⟩, ⟨2 * a + 1, by omega⟩] := by
  apply List.ext_getElem
  · simp; omega
  · intro i h1 h2
    simp only [List.getElem_finRange]
    by_cases hi : i < 2 * a
    · rw [List.getElem_append_left (by simp; omega), List.getElem_map, List.getElem_finRange]
      rfl
    · rw [List.getElem_append_right (by simp; omega)]
      simp only [List.length_map, List.length_finRange]
      have hsub : i - 2 * a = 0 ∨ i - 2 * a = 1 := by simp at h1; omega
      rcases hsub with h0 | h1'
      · apply Fin.ext; simp [h0]; omega
      · apply Fin.ext; simp [h1']; omega

private lemma altTrace_succ (a : ℕ) (S : Finset (Fin (2 * (a + 1)))) :
    let S' : Finset (Fin (2 * a)) := univ.filter (fun i => Fin.castAdd 2 i ∈ S)
    let b0 : Bool := decide (⟨2 * a, by omega⟩ ∈ S)
    let b1 : Bool := decide (⟨2 * a + 1, by omega⟩ ∈ S)
    altTrace (a + 1) S =
      altTrace a S' ++ (if b0 then [false] else []) ++ (if b1 then [true] else []) := by
  intro S' b0 b1
  unfold altTrace
  rw [list_finRange_two_succ, List.filter_append, List.map_append]
  have hleft :
      (((List.finRange (2 * a)).map (Fin.castAdd 2)).filter (fun i => i ∈ S)).map (altWord (a + 1)) =
        ((List.finRange (2 * a)).filter (fun i => i ∈ S')).map (altWord a) := by
    rw [List.filter_map, List.map_map]
    refine congrArg₂ List.map ?_ ?_
    · funext i; simp [altWord]
    · refine congrArg (fun p => List.filter p (List.finRange (2 * a))) ?_
      funext i; simp [S']
  rw [hleft, List.append_assoc]
  congr 1
  have hw0 : altWord (a + 1) ⟨2 * a, by omega⟩ = false := by
    simp [altWord]
  have hw1 : altWord (a + 1) ⟨2 * a + 1, by omega⟩ = true := by
    simp [altWord]
  dsimp only [b0, b1]
  by_cases h0 : (⟨2 * a, by omega⟩ : Fin (2 * (a + 1))) ∈ S <;>
  by_cases h1 : (⟨2 * a + 1, by omega⟩ : Fin (2 * (a + 1))) ∈ S <;>
  simp [h0, h1, hw0, hw1]

private lemma card_altTrace_eq_F (a : ℕ) :
    ∀ w : List Bool, (univ.filter (fun S : Finset (Fin (2 * a)) => altTrace a S = w)).card = F a w := by
  induction a with
  | zero =>
    intro w
    have huniv : (univ : Finset (Finset (Fin 0))) = {∅} := by
      ext s
      simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
      exact Finset.eq_empty_of_isEmpty s
    cases w with
    | nil =>
      rw [huniv]; simp [altTrace, F, cnt]
    | cons x xs =>
      rw [huniv]
      have hcnt : cnt (x :: xs) < (x :: xs).length := by
        unfold cnt
        have h1 : ((x :: xs).zip (x :: xs).tail).count (false, true) ≤
            ((x :: xs).zip (x :: xs).tail).length := List.count_le_length
        simp only [List.tail_cons, List.length_zip, List.length_cons, min_eq_right (Nat.le_succ _)] at h1 ⊢
        omega
      simp only [altTrace, F, zero_add]
      rw [Nat.choose_eq_zero_of_lt hcnt]
      simp
  | succ a ih =>
    intro w
    -- Bijection Finset (Fin (2*(a+1))) ≃ Finset (Fin (2*a)) × Bool × Bool
    let φ : Finset (Fin (2 * (a + 1))) → Finset (Fin (2 * a)) × Bool × Bool := fun S =>
      (univ.filter (fun i => Fin.castAdd 2 i ∈ S),
       decide (⟨2 * a, by omega⟩ ∈ S),
       decide (⟨2 * a + 1, by omega⟩ ∈ S))
    have hφ_inj : Function.Injective φ := by
      intro S₁ S₂ h
      have h1 : univ.filter (fun i : Fin (2 * a) => Fin.castAdd 2 i ∈ S₁) =
          univ.filter (fun i : Fin (2 * a) => Fin.castAdd 2 i ∈ S₂) := congrArg Prod.fst h
      have h2 : decide ((⟨2 * a, by omega⟩ : Fin (2 * (a + 1))) ∈ S₁) =
          decide ((⟨2 * a, by omega⟩ : Fin (2 * (a + 1))) ∈ S₂) := congrArg (fun p => p.2.1) h
      have h3 : decide ((⟨2 * a + 1, by omega⟩ : Fin (2 * (a + 1))) ∈ S₁) =
          decide ((⟨2 * a + 1, by omega⟩ : Fin (2 * (a + 1))) ∈ S₂) := congrArg (fun p => p.2.2) h
      ext x
      by_cases hx : x.val < 2 * a
      · have hmem := Finset.ext_iff.mp h1 ⟨x.val, hx⟩
        simpa [Fin.castAdd] using hmem
      · have hx' : x = ⟨2 * a, by omega⟩ ∨ x = ⟨2 * a + 1, by omega⟩ := by
          rcases (show x.val = 2 * a ∨ x.val = 2 * a + 1 by omega) with h0 | h0
          · left; exact Fin.ext h0
          · right; exact Fin.ext h0
        rcases hx' with hx0 | hx1
        · rw [hx0]; simpa using h2
        · rw [hx1]; simpa using h3
    have hφ_surj : Function.Surjective φ := by
      rintro ⟨S', b0, b1⟩
      let S : Finset (Fin (2 * (a + 1))) :=
        S'.map ⟨Fin.castAdd 2, Fin.castAdd_injective _ _⟩ ∪
        (if b0 then {⟨2 * a, by omega⟩} else ∅) ∪
        (if b1 then {⟨2 * a + 1, by omega⟩} else ∅)
      refine ⟨S, ?_⟩
      dsimp only [φ]
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · ext i
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_map,
          Function.Embedding.coeFn_mk]
        constructor
        · rintro ((⟨j, hj, hij⟩ | h0) | h1)
          · exact Fin.castAdd_injective _ _ hij ▸ hj
          · exfalso; split_ifs at h0 with hb0
            · have := congrArg Fin.val (Finset.mem_singleton.mp h0); simp at this; omega
            · exact Finset.notMem_empty _ h0
          · exfalso; split_ifs at h1 with hb1
            · have := congrArg Fin.val (Finset.mem_singleton.mp h1); simp at this; omega
            · exact Finset.notMem_empty _ h1
        · intro hi; exact Or.inl (Or.inl ⟨i, hi, rfl⟩)
      · cases b0
        · rw [decide_eq_false_iff_not]
          simp only [S, Bool.false_eq_true, ↓reduceIte, Finset.union_empty,
            Finset.mem_union, Finset.mem_map, Function.Embedding.coeFn_mk, not_or]
          refine ⟨?_, ?_⟩
          · rintro ⟨j, _, hj⟩; have := congrArg Fin.val hj; simp at this; omega
          · intro h1; split_ifs at h1 with hb1
            · have := congrArg Fin.val (Finset.mem_singleton.mp h1); simp at this
            · exact Finset.notMem_empty _ h1
        · rw [decide_eq_true_iff]
          exact Finset.mem_union_left _ (Finset.mem_union_right _ (by simp))
      · cases b1
        · rw [decide_eq_false_iff_not]
          simp only [S, Bool.false_eq_true, ↓reduceIte, Finset.union_empty,
            Finset.mem_union, Finset.mem_map, Function.Embedding.coeFn_mk, not_or]
          refine ⟨?_, ?_⟩
          · rintro ⟨j, _, hj⟩; have := congrArg Fin.val hj; simp at this; omega
          · intro h0; split_ifs at h0 with hb0
            · have := congrArg Fin.val (Finset.mem_singleton.mp h0); simp at this
            · exact Finset.notMem_empty _ h0
        · rw [decide_eq_true_iff]
          exact Finset.mem_union_right _ (by simp)
    let e := Equiv.ofBijective φ ⟨hφ_inj, hφ_surj⟩
    have hcard :
        (univ.filter (fun S : Finset (Fin (2 * (a + 1))) => altTrace (a + 1) S = w)).card =
        (univ.filter (fun p : Finset (Fin (2 * a)) × Bool × Bool =>
          altTrace a p.1 ++ (if p.2.1 then [false] else []) ++
            (if p.2.2 then [true] else []) = w)).card := by
      refine Finset.card_bij (fun S _ => e S) ?_ ?_ ?_
      · intro S hS
        rw [mem_filter] at hS ⊢
        refine ⟨mem_univ _, ?_⟩
        change altTrace a (φ S).1 ++ (if (φ S).2.1 then [false] else []) ++
          (if (φ S).2.2 then [true] else []) = w
        dsimp only [φ]
        rw [← altTrace_succ a S]
        exact hS.2
      · intro S₁ _ S₂ _ h; exact e.injective h
      · intro p hp
        rw [mem_filter] at hp
        refine ⟨e.symm p, mem_filter.mpr ⟨mem_univ _, ?_⟩, e.apply_symm_apply p⟩
        rw [altTrace_succ a (e.symm p)]
        have hpe : φ (e.symm p) = p := e.apply_symm_apply p
        have h1 : univ.filter (fun i : Fin (2 * a) => Fin.castAdd 2 i ∈ e.symm p) = p.1 :=
          congrArg Prod.fst hpe
        have h2 : decide ((⟨2 * a, by omega⟩ : Fin (2 * (a + 1))) ∈ e.symm p) = p.2.1 :=
          congrArg (fun q => q.2.1) hpe
        have h3 : decide ((⟨2 * a + 1, by omega⟩ : Fin (2 * (a + 1))) ∈ e.symm p) = p.2.2 :=
          congrArg (fun q => q.2.2) hpe
        rw [h1, h2, h3]
        exact hp.2
    rw [hcard]
    -- Split the product over (b0, b1) ∈ Bool × Bool
    have hsplit :
        (univ.filter (fun p : Finset (Fin (2 * a)) × Bool × Bool =>
          altTrace a p.1 ++ (if p.2.1 then [false] else []) ++
            (if p.2.2 then [true] else []) = w)).card =
        (univ.filter (fun S' : Finset (Fin (2 * a)) => altTrace a S' = w)).card +
        (univ.filter (fun S' : Finset (Fin (2 * a)) => altTrace a S' ++ [false] = w)).card +
        (univ.filter (fun S' : Finset (Fin (2 * a)) => altTrace a S' ++ [true] = w)).card +
        (univ.filter (fun S' : Finset (Fin (2 * a)) => altTrace a S' ++ [false, true] = w)).card := by
      have hprod : (univ : Finset (Finset (Fin (2 * a)) × Bool × Bool)) =
          univ ×ˢ (univ ×ˢ univ) := by ext; simp
      rw [hprod, card_filter, Finset.sum_product]
      simp only [Finset.sum_product, Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte,
        List.append_nil, card_filter]
      simp only [List.append_assoc, List.cons_append, List.nil_append, Finset.sum_add_distrib]
      ac_rfl
    rw [hsplit]
    -- Case analysis on w from the right
    refine List.reverseRecOn w ?_ ?_
    · simp [ih [], F, cnt]
    · intro v x _
      cases x
      · -- w = v ++ [false]
        have h0 : (univ.filter (fun S' : Finset (Fin (2 * a)) =>
            altTrace a S' ++ [false] = v ++ [false])).card = F a v := by
          simp only [List.append_cancel_right_eq]
          exact ih v
        have h1 : (univ.filter (fun S' : Finset (Fin (2 * a)) =>
            altTrace a S' ++ [true] = v ++ [false])).card = 0 := by
          rw [card_eq_zero, filter_eq_empty_iff]
          intro S' _ h
          have := congrArg List.getLast? h
          simp at this
        have h2 : (univ.filter (fun S' : Finset (Fin (2 * a)) =>
            altTrace a S' ++ [false, true] = v ++ [false])).card = 0 := by
          rw [card_eq_zero, filter_eq_empty_iff]
          intro S' _ h
          have h' : (altTrace a S' ++ [false]) ++ [true] = v ++ [false] := by simpa using h
          have := congrArg List.getLast? h'
          simp at this
        rw [ih (v ++ [false]), h0, h1, h2]
        simp only [add_zero, F, cnt_append_false, List.length_append, List.length_singleton]
        have hch := Nat.choose_succ_succ (a + cnt v) v.length
        simp only [Nat.succ_eq_add_one] at hch
        rw [show a + 1 + cnt v = (a + cnt v) + 1 by omega]
        omega
      · -- w = v ++ [true]
        have h0 : ∀ v' : List Bool, (univ.filter (fun S' : Finset (Fin (2 * a)) =>
            altTrace a S' ++ [false] = v' ++ [true])).card = 0 := by
          intro v'
          rw [card_eq_zero, filter_eq_empty_iff]
          intro S' _ h
          have := congrArg List.getLast? h
          simp at this
        have h1 : ∀ v' : List Bool, (univ.filter (fun S' : Finset (Fin (2 * a)) =>
            altTrace a S' ++ [true] = v' ++ [true])).card = F a v' := by
          intro v'
          simp only [List.append_cancel_right_eq]
          exact ih v'
        refine List.reverseRecOn v ?_ ?_
        · -- v = []
          have h2 : (univ.filter (fun S' : Finset (Fin (2 * a)) =>
              altTrace a S' ++ [false, true] = [] ++ [true])).card = 0 := by
            rw [card_eq_zero, filter_eq_empty_iff]
            intro S' _ h
            have := congrArg List.length h
            simp at this
          rw [ih ([] ++ [true]), h0 [], h1 [], h2]
          simp [F, cnt]
        · intro u y _
          cases y
          · -- v = u ++ [false], w = u ++ [false, true]
            have h2 : (univ.filter (fun S' : Finset (Fin (2 * a)) =>
                altTrace a S' ++ [false, true] = (u ++ [false]) ++ [true])).card = F a u := by
              have heq : (u ++ [false]) ++ [true] = u ++ [false, true] := by simp
              rw [heq]
              simp only [List.append_cancel_right_eq]
              exact ih u
            rw [ih ((u ++ [false]) ++ [true]), h0 (u ++ [false]), h1 (u ++ [false]), h2]
            have hw : (u ++ [false]) ++ [true] = u ++ [false, true] := by simp
            rw [hw]
            simp only [add_zero, F, cnt_append_false_true, cnt_append_false,
              List.length_append, List.length_cons, List.length_nil]
            have hc1 : (a + cnt u).choose (u.length + 1) + (a + cnt u).choose u.length =
                (a + cnt u + 1).choose (u.length + 1) := by
              have hch := Nat.choose_succ_succ (a + cnt u) u.length
              simp only [Nat.succ_eq_add_one] at hch; omega
            have hc2 : (a + (cnt u + 1)).choose (u.length + 2) +
                (a + cnt u + 1).choose (u.length + 1) =
                (a + 1 + (cnt u + 1)).choose (u.length + 2) := by
              have hch := Nat.choose_succ_succ (a + cnt u + 1) (u.length + 1)
              simp only [Nat.succ_eq_add_one] at hch
              have hlen : u.length + 1 + 1 = u.length + 2 := by omega
              have ha : a + 1 + (cnt u + 1) = (a + cnt u + 1) + 1 := by omega
              have ha' : a + (cnt u + 1) = a + cnt u + 1 := by omega
              rw [hlen] at hch
              rw [ha, ha']
              omega
            linarith [hc1, hc2]
          · -- v = u ++ [true], w = u ++ [true, true]
            have h2 : (univ.filter (fun S' : Finset (Fin (2 * a)) =>
                altTrace a S' ++ [false, true] = (u ++ [true]) ++ [true])).card = 0 := by
              rw [card_eq_zero, filter_eq_empty_iff]
              intro S' _ h
              have h' : (altTrace a S' ++ [false]) ++ [true] = (u ++ [true]) ++ [true] := by
                simpa using h
              have h'' := List.append_cancel_right h'
              have := congrArg List.getLast? h''
              simp at this
            rw [ih ((u ++ [true]) ++ [true]), h0 (u ++ [true]), h1 (u ++ [true]), h2]
            have hlt : (u ++ [true]).getLast? ≠ some false := by simp
            simp only [add_zero, F, cnt_append_true_of_last_true _ hlt,
              List.length_append, List.length_singleton]
            have hch := Nat.choose_succ_succ (a + cnt (u ++ [true])) ((u ++ [true]).length)
            simp only [Nat.succ_eq_add_one, List.length_append, List.length_singleton] at hch
            rw [show a + 1 + cnt (u ++ [true]) = (a + cnt (u ++ [true])) + 1 by omega]
            omega

private lemma sum_F_le_pow (a : ℕ) (U : Finset (List Bool)) :
    ∑ w ∈ U, F a w ≤ 2 ^ (2 * a) := by
  have h1 : ∑ w ∈ U, F a w =
      ∑ w ∈ U, (univ.filter (fun S : Finset (Fin (2 * a)) => altTrace a S = w)).card :=
    sum_congr rfl fun w _ => (card_altTrace_eq_F a w).symm
  rw [h1, ← Finset.card_biUnion]
  · calc (U.biUnion (fun w => univ.filter (fun S : Finset (Fin (2 * a)) => altTrace a S = w))).card
        ≤ (univ : Finset (Finset (Fin (2 * a)))).card := card_le_univ _
      _ = 2 ^ (2 * a) := by simp
  · intro w₁ _ w₂ _ hne
    exact Finset.disjoint_left.mpr fun S h1 h2 =>
      hne ((mem_filter.mp h1).2.symm.trans (mem_filter.mp h2).2)

-- Step 2: Properties of `cnt` on `take` and `drop`

private lemma sublist_zip_tail_append (w : List Bool) (j : ℕ) :
    List.Sublist ((w.take j).zip (w.take j).tail ++ (w.drop (j + 1)).zip (w.drop (j + 1)).tail)
      (w.zip w.tail) := by
  induction w generalizing j with
  | nil => simp
  | cons a t ih =>
    cases j with
    | zero =>
      simp only [List.take_zero, List.tail_nil, List.zip_nil_left, List.nil_append,
        List.drop_succ_cons, List.drop_zero]
      cases t with
      | nil => simp
      | cons b r =>
        simp only [List.tail_cons, List.zip_cons_cons]
        exact List.sublist_cons_self _ _
    | succ j' =>
      simp only [List.take_succ_cons, List.drop_succ_cons]
      cases t with
      | nil => simp
      | cons b r =>
        cases j' with
        | zero =>
          simp only [List.take_zero, List.tail_cons, List.zip_nil_right, List.nil_append,
            List.drop_succ_cons, List.drop_zero]
          cases r with
          | nil => simp
          | cons c s =>
            simp only [List.tail_cons, List.zip_cons_cons]
            exact List.sublist_cons_of_sublist _ (List.sublist_cons_self _ _)
        | succ j'' =>
          simp only [List.take_succ_cons, List.tail_cons, List.zip_cons_cons, List.cons_append]
          exact List.Sublist.cons₂ (a, b) (ih (j'' + 1))

private lemma cnt_take_add_drop_le (w : List Bool) (j : ℕ) :
    cnt (w.take j) + cnt (w.drop (j + 1)) ≤ cnt w := by
  unfold cnt
  rw [← List.count_append]
  exact (sublist_zip_tail_append w j).count_le (false, true)

private lemma cnt_take_add_drop_ge (w : List Bool) (j : ℕ) :
    cnt w ≤ cnt (w.take j) + cnt (w.drop (j + 1)) + 2 := by
  -- Actually even simpler: we prove for any list v, x, u: cnt (v ++ [x] ++ u) ≤ cnt v + cnt u + 2
  by_cases hj : j < w.length
  · have hw : w = w.take j ++ [w[j]] ++ w.drop (j + 1) := by
      have h1 := List.take_append_drop j w
      have h2 : w.drop j = w[j] :: w.drop (j + 1) := List.drop_eq_getElem_cons hj
      rw [h2] at h1
      simpa [List.append_assoc] using h1.symm
    suffices hgen : ∀ (v u : List Bool) (x : Bool),
        cnt (v ++ [x] ++ u) ≤ cnt v + cnt u + 2 by
      conv_lhs => rw [hw]
      exact hgen (w.take j) (w.drop (j + 1)) w[j]
    intro v u x
    induction u generalizing v x with
    | nil =>
      simp only [List.append_nil, cnt]
      rw [zip_tail_append_singleton]
      cases v.getLast? with
      | none => simp
      | some y =>
        rw [List.count_append]
        have : [(y, x)].count (false, true) ≤ 1 := by cases y <;> cases x <;> decide
        omega
    | cons y r ihu =>
      have h1 : v ++ [x] ++ (y :: r) = (v ++ [x]) ++ [y] ++ r := by simp [List.append_assoc]
      have hstep : ∀ (a : List Bool) (b : Bool), cnt (a ++ [b]) ≤ cnt a + 1 := by
        intro a b
        unfold cnt
        rw [zip_tail_append_singleton]
        cases a.getLast? with
        | none => simp
        | some z =>
          rw [List.count_append]
          have : [(z, b)].count (false, true) ≤ 1 := by cases z <;> cases b <;> decide
          omega
      have hconcat : ∀ (a b : List Bool), cnt (a ++ b) ≤ cnt a + cnt b + 1 := by
        intro a b
        induction b using List.reverseRecOn with
        | nil => simp [cnt]
        | append_singleton b' c ihb =>
          rw [← List.append_assoc]
          have hlast_eq : ∀ (p q : List Bool), q ≠ [] → (p ++ q).getLast? = q.getLast? := by
            intro p q hq; rw [List.getLast?_append_of_ne_nil p hq]
          by_cases hb' : b' = []
          · subst hb'; simp only [List.nil_append, List.append_nil, cnt] at *
            rw [zip_tail_append_singleton]
            cases ha : a.getLast? with
            | none =>
              have hnil : a = [] := List.getLast?_eq_none_iff.mp ha
              subst hnil; simp
            | some z =>
              simp only [List.count_append]
              have : [(z, c)].count (false, true) ≤ 1 := by cases z <;> cases c <;> decide
              omega
          · unfold cnt at ihb ⊢
            rw [zip_tail_append_singleton (a ++ b') c, zip_tail_append_singleton b' c,
                hlast_eq a b' hb']
            cases hb : b'.getLast? with
            | none => exact (hb' (List.getLast?_eq_none_iff.mp hb)).elim
            | some z =>
              rw [List.count_append, List.count_append]
              omega
      calc cnt (v ++ [x] ++ (y :: r))
          = cnt ((v ++ [x]) ++ (y :: r)) := rfl
        _ ≤ cnt (v ++ [x]) + cnt (y :: r) + 1 := hconcat _ _
        _ ≤ (cnt v + 1) + cnt (y :: r) + 1 := by have := hstep v x; omega
        _ = cnt v + cnt (y :: r) + 2 := by omega
  · have htake : w.take j = w := List.take_of_length_le (by omega)
    rw [htake]; omega

private lemma cnt_append_two_le (v : List Bool) (x y : Bool) :
    cnt (v ++ [x, y]) ≤ cnt v + 1 := by
  have h1 : v ++ [x, y] = (v ++ [x]) ++ [y] := by simp
  rw [h1]
  unfold cnt
  rw [zip_tail_append_singleton (v ++ [x]) y]
  have hlast : (v ++ [x]).getLast? = some x := by simp
  rw [hlast, List.count_append, zip_tail_append_singleton v x]
  cases hv : v.getLast? with
  | none =>
    have hnil : v = [] := List.getLast?_eq_none_iff.mp hv
    subst hnil
    simp only [List.count_nil, zero_add]
    have h1 : [(x, y)].count (false, true) ≤ 1 := by cases x <;> cases y <;> decide
    omega
  | some z =>
    rw [List.count_append]
    have hpair : [(z, x)].count (false, true) + [(x, y)].count (false, true) ≤ 1 := by
      cases z <;> cases x <;> cases y <;> decide
    omega

private lemma cnt_take_step2 (w : List Bool) (j : ℕ) :
    cnt (w.take (j + 2)) ≤ cnt (w.take j) + 1 := by
  by_cases h1 : j + 1 < w.length
  · have heq : w.take (j + 2) = w.take j ++ [w[j], w[j + 1]] := by
      have ha : w.take (j + 1) = w.take j ++ [w[j]] := List.take_succ_eq_append_getElem (by omega)
      have hb : w.take (j + 2) = w.take (j + 1) ++ [w[j + 1]] := List.take_succ_eq_append_getElem h1
      rw [hb, ha, List.append_assoc]; rfl
    rw [heq]
    exact cnt_append_two_le (w.take j) w[j] w[j + 1]
  · by_cases h0 : j < w.length
    · have heq : w.take (j + 2) = w.take j ++ [w[j]] := by
        have hlen : w.length = j + 1 := by omega
        have h2 : w.take (j + 2) = w := List.take_of_length_le (by omega)
        have h3 : w.take (j + 1) = w := by rw [← hlen, List.take_length]
        calc w.take (j + 2) = w := h2
          _ = w.take (j + 1) := h3.symm
          _ = w.take j ++ [w[j]] := List.take_succ_eq_append_getElem h0
      rw [heq]
      unfold cnt
      rw [zip_tail_append_singleton]
      cases hv : (w.take j).getLast? with
      | none => simp
      | some z =>
        rw [List.count_append]
        have : [(z, w[j])].count (false, true) ≤ 1 := by cases z <;> cases w[j] <;> decide
        omega
    · rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
      omega

private lemma cnt_take_mono (w : List Bool) {i j : ℕ} (hij : i ≤ j) :
    cnt (w.take i) ≤ cnt (w.take j) := by
  induction hij with
  | refl => exact le_rfl
  | @step m hm ih =>
    by_cases hml : m < w.length
    · rw [List.take_succ_eq_append_getElem hml]
      unfold cnt
      rw [zip_tail_append_singleton]
      cases hv : (w.take m).getLast? with
      | none =>
        have hnil : w.take m = [] := List.getLast?_eq_none_iff.mp hv
        rw [hnil] at ih
        simp [cnt] at ih ⊢
        exact ih
      | some z =>
        rw [List.count_append]
        exact ih.trans (Nat.le_add_right _ _)
    · have h1 : w.take m = w := List.take_of_length_le (by omega)
      have h2 : w.take (m + 1) = w := List.take_of_length_le (by omega)
      rw [h1] at ih
      rw [h2]
      exact ih

-- Step 3: Exact identity for `A w j`

private lemma choose_succ_mul_real (a r : ℕ) :
    ((a : ℝ) + 1) * (a.choose r : ℝ) = ((a : ℝ) + 1 - r) * ((a + 1).choose r : ℝ) := by
  by_cases hr : r ≤ a + 1
  · have hnat : (a + 1) * a.choose r = (a + 1 - r) * (a + 1).choose r := by
      cases r with
      | zero => simp
      | succ r' =>
        have h2 : (r' + 1) * (a + 1).choose (r' + 1) = (a + 1) * a.choose r' := by
          have := Nat.add_one_mul_choose_eq a r'
          linarith
        have h3 : (a + 1).choose (r' + 1) = a.choose (r' + 1) + a.choose r' := by
          have hch := Nat.choose_succ_succ a r'
          simp only [Nat.succ_eq_add_one] at hch; omega
        have h4 : (a + 1 - (r' + 1)) * (a + 1).choose (r' + 1) +
            (r' + 1) * (a + 1).choose (r' + 1) = (a + 1) * (a + 1).choose (r' + 1) := by
          rw [← Nat.add_mul, Nat.sub_add_cancel hr]
        have h5 : (a + 1) * (a + 1).choose (r' + 1) =
            (a + 1) * a.choose (r' + 1) + (a + 1) * a.choose r' := by
          rw [h3, Nat.mul_add]
        omega
    have hR : (((a + 1) * a.choose r : ℕ) : ℝ) = (((a + 1 - r) * (a + 1).choose r : ℕ) : ℝ) := by
      exact_mod_cast hnat
    push_cast [Nat.cast_sub hr] at hR
    linarith
  · have h1 : a.choose r = 0 := Nat.choose_eq_zero_of_lt (by omega)
    have h2 : (a + 1).choose r = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [h1, h2]

private lemma A_exact_identity (a b m1 m2 : ℕ) :
    ((a.choose m1 * (b + 1).choose m2 : ℕ) : ℝ) - (((a + 1).choose m1 * b.choose m2 : ℕ) : ℝ) =
      (((m2 : ℝ) * ((a : ℝ) + 1) - (m1 : ℝ) * ((b : ℝ) + 1)) /
        (((a : ℝ) + 1) * ((b : ℝ) + 1))) *
        (((a + 1).choose m1 : ℝ) * ((b + 1).choose m2 : ℝ)) := by
  have ha : (0 : ℝ) < (a : ℝ) + 1 := by positivity
  have hb : (0 : ℝ) < (b : ℝ) + 1 := by positivity
  have hab : (0 : ℝ) < ((a : ℝ) + 1) * ((b : ℝ) + 1) := mul_pos ha hb
  rw [div_mul_eq_mul_div, eq_div_iff hab.ne']
  have hca := choose_succ_mul_real a m1
  have hcb := choose_succ_mul_real b m2
  push_cast
  calc ((a.choose m1 : ℝ) * ((b + 1).choose m2 : ℝ) -
          ((a + 1).choose m1 : ℝ) * (b.choose m2 : ℝ)) * (((a : ℝ) + 1) * ((b : ℝ) + 1))
      = (((a : ℝ) + 1) * (a.choose m1 : ℝ)) * ((b : ℝ) + 1) * ((b + 1).choose m2 : ℝ) -
        ((a : ℝ) + 1) * ((a + 1).choose m1 : ℝ) * (((b : ℝ) + 1) * (b.choose m2 : ℝ)) := by ring
    _ = (((a : ℝ) + 1 - m1) * ((a + 1).choose m1 : ℝ)) * ((b : ℝ) + 1) * ((b + 1).choose m2 : ℝ) -
        ((a : ℝ) + 1) * ((a + 1).choose m1 : ℝ) * (((b : ℝ) + 1 - m2) * ((b + 1).choose m2 : ℝ)) := by
          rw [hca, hcb]
    _ = ((m2 : ℝ) * ((a : ℝ) + 1) - (m1 : ℝ) * ((b : ℝ) + 1)) *
          (((a + 1).choose m1 : ℝ) * ((b + 1).choose m2 : ℝ)) := by ring

-- Step 4: Hypergeometric ratio, peak, and tail bounds

private lemma choose_step_real (n r : ℕ) :
    ((r : ℝ) + 1) * (n.choose (r + 1) : ℝ) = ((n : ℝ) - r) * (n.choose r : ℝ) := by
  by_cases hr : r ≤ n
  · have hnat : (r + 1) * n.choose (r + 1) = (n - r) * n.choose r := by
      have h1 := Nat.choose_succ_right_eq n r
      linarith
    have hR : (((r + 1) * n.choose (r + 1) : ℕ) : ℝ) = (((n - r) * n.choose r : ℕ) : ℝ) := by
      exact_mod_cast hnat
    push_cast [Nat.cast_sub hr] at hR
    linarith
  · have h1 : n.choose (r + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    have h2 : n.choose r = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [h1, h2]

private lemma hypergeom_step_eq (A B M r : ℕ) (hr : r < M) :
    ((A.choose (r + 1) : ℝ) * (B.choose (M - (r + 1)) : ℝ)) *
      (((r : ℝ) + 1) * ((B : ℝ) - (M : ℝ) + (r : ℝ) + 1)) =
    ((A.choose r : ℝ) * (B.choose (M - r) : ℝ)) *
      (((A : ℝ) - (r : ℝ)) * ((M : ℝ) - (r : ℝ))) := by
  have hm : M - r = (M - (r + 1)) + 1 := by omega
  have h1 := choose_step_real A r
  have h2 := choose_step_real B (M - (r + 1))
  have hcast1 : ((M - (r + 1) : ℕ) : ℝ) + 1 = (M : ℝ) - (r : ℝ) := by
    have : (M - (r + 1) : ℕ) + 1 = M - r := by omega
    have hR : (((M - (r + 1) : ℕ) + 1 : ℕ) : ℝ) = ((M - r : ℕ) : ℝ) := by exact_mod_cast this
    push_cast [Nat.cast_sub (le_of_lt hr)] at hR
    linarith
  have hcast2 : (B : ℝ) - ((M - (r + 1) : ℕ) : ℝ) = (B : ℝ) - (M : ℝ) + (r : ℝ) + 1 := by
    linarith
  rw [hcast1, hcast2] at h2
  rw [hm]
  calc ((A.choose (r + 1) : ℝ) * (B.choose (M - (r + 1)) : ℝ)) *
        (((r : ℝ) + 1) * ((B : ℝ) - (M : ℝ) + (r : ℝ) + 1))
      = (((r : ℝ) + 1) * (A.choose (r + 1) : ℝ)) *
        (((B : ℝ) - (M : ℝ) + (r : ℝ) + 1) * (B.choose (M - (r + 1)) : ℝ)) := by ring
    _ = (((A : ℝ) - (r : ℝ)) * (A.choose r : ℝ)) *
        (((M : ℝ) - (r : ℝ)) * (B.choose ((M - (r + 1)) + 1) : ℝ)) := by rw [h1, ← h2]
    _ = ((A.choose r : ℝ) * (B.choose ((M - (r + 1)) + 1) : ℝ)) *
        (((A : ℝ) - (r : ℝ)) * ((M : ℝ) - (r : ℝ))) := by ring

private lemma sum_hypergeom (A B M : ℕ) :
    ∑ r ∈ range (M + 1), (A.choose r : ℝ) * (B.choose (M - r) : ℝ) =
      ((A + B).choose M : ℝ) := by
  have hnat : ∑ r ∈ range (M + 1), A.choose r * B.choose (M - r) = (A + B).choose M := by
    rw [Nat.add_choose_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => A.choose i * B.choose j)]
  exact_mod_cast hnat

set_option maxHeartbeats 800000 in
private lemma hypergeom_peak_bound (k A B M r : ℕ)
    (hk : 1600 ≤ k) (hA1 : k ≤ A) (hA2 : A ≤ 2 * k)
    (hB1 : k ≤ B) (hB2 : B ≤ 2 * k)
    (hM1 : k ≤ M) (hM2 : M + k / 4 ≤ A + B) (hr : r ≤ M) :
    (A.choose r : ℝ) * (B.choose (M - r) : ℝ) ≤
      (80 / Real.sqrt (k : ℝ)) * ((A + B).choose M : ℝ) := by
  let p (i : ℕ) : ℝ := (A.choose i : ℝ) * (B.choose (M - i) : ℝ)
  have hp_nonneg : ∀ i, 0 ≤ p i := fun i => by positivity
  -- Let r0 maximize p on range (M + 1)
  have hne : (range (M + 1)).Nonempty := ⟨0, mem_range.mpr (by omega)⟩
  obtain ⟨r0, hr0_mem, hr0_max⟩ := exists_max_image (range (M + 1)) p hne
  have hr0_le : r0 ≤ M := Nat.lt_succ_iff.mp (mem_range.mp hr0_mem)
  suffices hmode : p r0 ≤ (80 / Real.sqrt (k : ℝ)) * ((A + B).choose M : ℝ) by
    exact (hr0_max r (mem_range.mpr (by omega))).trans hmode
  by_cases hp0 : p r0 = 0
  · rw [hp0]; positivity
  have hp0_pos : 0 < p r0 := lt_of_le_of_ne (hp_nonneg r0) (Ne.symm hp0)
  have hr0_A : r0 ≤ A := by
    by_contra hgt
    have : A.choose r0 = 0 := Nat.choose_eq_zero_of_lt (by omega)
    exact hp0 (by simp [p, this])
  have hr0_B : M - r0 ≤ B := by
    by_contra hgt
    have : B.choose (M - r0) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    exact hp0 (by simp [p, this])
  -- Mode location: p(r0) ≥ p(r0 + 1) and p(r0) ≥ p(r0 - 1) imply r0 is near M * A / (A + B)
  -- Specifically, r0 ≥ k/10, A - r0 ≥ k/20, M - r0 ≥ k/10, B - (M - r0) ≥ k/20
  have hAB_pos : (0 : ℝ) < (A : ℝ) + (B : ℝ) := by
    have : 0 < A + B := by omega
    exact_mod_cast this
  have hmode_upper : ((r0 : ℝ) + 1) * ((B : ℝ) - (M : ℝ) + (r0 : ℝ) + 1) ≥
      ((A : ℝ) - (r0 : ℝ)) * ((M : ℝ) - (r0 : ℝ)) := by
    by_cases hrm : r0 < M
    · have hstep := hypergeom_step_eq A B M r0 hrm
      have hle : p (r0 + 1) ≤ p r0 := hr0_max (r0 + 1) (mem_range.mpr (by omega))
      have hden_nonneg : 0 ≤ ((r0 : ℝ) + 1) * ((B : ℝ) - (M : ℝ) + (r0 : ℝ) + 1) := by
        have : (M - r0 : ℕ) ≤ B := hr0_B
        have : (M : ℝ) - (r0 : ℝ) ≤ (B : ℝ) := by
          have hR : ((M - r0 : ℕ) : ℝ) ≤ (B : ℝ) := by exact_mod_cast this
          rwa [Nat.cast_sub hr0_le] at hR
        nlinarith
      nlinarith
    · have hr0M : r0 = M := by omega
      rw [hr0M]
      have : (M : ℝ) - (M : ℝ) = 0 := sub_self _
      rw [this, mul_zero, show (B : ℝ) - (M : ℝ) + (M : ℝ) + 1 = (B : ℝ) + 1 by ring]
      positivity
  have hmode_lower : (r0 : ℝ) * ((B : ℝ) - (M : ℝ) + (r0 : ℝ)) ≤
      ((A : ℝ) - (r0 : ℝ) + 1) * ((M : ℝ) - (r0 : ℝ) + 1) := by
    by_cases hr0_pos : 0 < r0
    · have hstep := hypergeom_step_eq A B M (r0 - 1) (by omega)
      have hle : p (r0 - 1) ≤ p r0 := hr0_max (r0 - 1) (mem_range.mpr (by omega))
      have hcast : ((r0 - 1 : ℕ) : ℝ) + 1 = (r0 : ℝ) := by
        rw [Nat.cast_sub (by omega : 1 ≤ r0)]; push_cast; ring
      have hsub1 : (A : ℝ) - ((r0 - 1 : ℕ) : ℝ) = (A : ℝ) - (r0 : ℝ) + 1 := by linarith
      have hsub2 : (M : ℝ) - ((r0 - 1 : ℕ) : ℝ) = (M : ℝ) - (r0 : ℝ) + 1 := by linarith
      have hsub3 : (B : ℝ) - (M : ℝ) + ((r0 - 1 : ℕ) : ℝ) + 1 = (B : ℝ) - (M : ℝ) + (r0 : ℝ) := by
        linarith
      have hidx : r0 - 1 + 1 = r0 := by omega
      rw [hidx, hcast, hsub1, hsub2, hsub3] at hstep
      have hnum_nonneg : 0 ≤ ((A : ℝ) - (r0 : ℝ) + 1) * ((M : ℝ) - (r0 : ℝ) + 1) := by
        have h1 : (r0 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hr0_A
        have h2 : (r0 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hr0_le
        nlinarith
      nlinarith
    · have hr00 : r0 = 0 := by omega
      rw [hr00]
      simp only [Nat.cast_zero, zero_mul, sub_zero, zero_add]
      positivity
  -- From hmode_upper and hmode_lower, deduce linear bounds on r0
  have hA1R : (k : ℝ) ≤ A := by exact_mod_cast hA1
  have hA2R : (A : ℝ) ≤ 2 * k := by exact_mod_cast hA2
  have hB1R : (k : ℝ) ≤ B := by exact_mod_cast hB1
  have hB2R : (B : ℝ) ≤ 2 * k := by exact_mod_cast hB2
  have hM1R : (k : ℝ) ≤ M := by exact_mod_cast hM1
  have hkR : (1600 : ℝ) ≤ k := by exact_mod_cast hk
  have hM2R : (M : ℝ) + (k : ℝ) / 5 ≤ (A : ℝ) + (B : ℝ) := by
    have : M + k / 4 ≤ A + B := hM2
    have hdiv : (k : ℝ) / 5 ≤ ((k / 4 : ℕ) : ℝ) := by
      have : 4 * (k / 4) + 3 ≥ k := by omega
      have hR : (4 : ℝ) * ((k / 4 : ℕ) : ℝ) + 3 ≥ (k : ℝ) := by exact_mod_cast this
      linarith
    have hR : (M : ℝ) + ((k / 4 : ℕ) : ℝ) ≤ (A : ℝ) + (B : ℝ) := by exact_mod_cast this
    linarith
  have hr0_lb : (k : ℝ) / 5 ≤ r0 := by nlinarith
  have hAr0_lb : (k : ℝ) / 25 ≤ (A : ℝ) - r0 := by nlinarith
  have hMr0_lb : (k : ℝ) / 5 ≤ (M : ℝ) - r0 := by nlinarith
  have hBMr0_lb : (k : ℝ) / 25 ≤ (B : ℝ) - (M : ℝ) + r0 := by nlinarith
  -- Step forward t = ⌊√k / 40⌋₊ steps from r0
  let t : ℕ := ⌊Real.sqrt (k : ℝ) / 40⌋₊
  have ht_le : (t : ℝ) ≤ Real.sqrt (k : ℝ) / 40 := Nat.floor_le (by positivity)
  have hsq_pos : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr (by positivity)
  have hsq_ge : 40 ≤ Real.sqrt (k : ℝ) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]; linarith
  have ht_ge1 : 1 ≤ t := (Nat.one_le_floor_iff _).mpr (by linarith)
  have ht_sq : (t : ℝ) ^ 2 ≤ (k : ℝ) / 1600 := by
    calc (t : ℝ) ^ 2 ≤ (Real.sqrt (k : ℝ) / 40) ^ 2 :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) ht_le 2
      _ = (k : ℝ) / 1600 := by rw [div_pow, Real.sq_sqrt (by positivity)]; norm_num
  have ht_lin : (t : ℝ) ≤ (k : ℝ) / 1600 := by
    have : Real.sqrt (k : ℝ) ≤ (k : ℝ) / 40 := by
      have : Real.sqrt (k : ℝ) * 40 ≤ Real.sqrt (k : ℝ) * Real.sqrt (k : ℝ) :=
        mul_le_mul_of_nonneg_left hsq_ge hsq_pos.le
      rw [Real.mul_self_sqrt (by positivity)] at this
      linarith
    linarith
  -- For every s ≤ t, p(r0 + s) ≥ (1 - 700 * s^2 / k) * p(r0) ≥ (1/2) * p(r0)
  have hstep_drop : ∀ s ≤ t, (1 - 700 * (s : ℝ) ^ 2 / (k : ℝ)) * p r0 ≤ p (r0 + s) := by
    intro s hs
    induction s with
    | zero => simp
    | succ s ih =>
      have hs_le : s ≤ t := by omega
      have ihs := ih hs_le
      have hrm : r0 + s < M := by
        have : (s : ℝ) ≤ t := by exact_mod_cast hs_le
        have : (r0 : ℝ) + (s : ℝ) < (M : ℝ) := by linarith
        exact_mod_cast this
      have hstep := hypergeom_step_eq A B M (r0 + s) hrm
      have hden_pos : 0 < ((r0 + s : ℕ) : ℝ) + 1 := by positivity
      have hden2_pos : 0 < (B : ℝ) - (M : ℝ) + ((r0 + s : ℕ) : ℝ) + 1 := by
        push_cast; linarith
      have hden_prod_pos : 0 < (((r0 + s : ℕ) : ℝ) + 1) * ((B : ℝ) - (M : ℝ) + ((r0 + s : ℕ) : ℝ) + 1) :=
        mul_pos hden_pos hden2_pos
      have hs_t : ((s + 1 : ℕ) : ℝ) ≤ t := by exact_mod_cast hs
      have hden_lb : (k : ℝ) ^ 2 / 125 ≤
          (((r0 + s : ℕ) : ℝ) + 1) * ((B : ℝ) - (M : ℝ) + ((r0 + s : ℕ) : ℝ) + 1) := by
        have h1 : (k : ℝ) / 5 ≤ ((r0 + s : ℕ) : ℝ) + 1 := by push_cast; linarith
        have h2 : (k : ℝ) / 25 ≤ (B : ℝ) - (M : ℝ) + ((r0 + s : ℕ) : ℝ) + 1 := by push_cast; linarith
        nlinarith
      have hdiff_ub :
          (((r0 + s : ℕ) : ℝ) + 1) * ((B : ℝ) - (M : ℝ) + ((r0 + s : ℕ) : ℝ) + 1) -
          ((A : ℝ) - ((r0 + s : ℕ) : ℝ)) * ((M : ℝ) - ((r0 + s : ℕ) : ℝ)) ≤
          ((s : ℝ) + 1) * ((A : ℝ) + (B : ℝ) + 2) := by
        push_cast
        nlinarith [hmode_lower]
      have hAB2 : (A : ℝ) + (B : ℝ) + 2 ≤ 5 * (k : ℝ) := by linarith
      have hdiff_k :
          (((r0 + s : ℕ) : ℝ) + 1) * ((B : ℝ) - (M : ℝ) + ((r0 + s : ℕ) : ℝ) + 1) -
          ((A : ℝ) - ((r0 + s : ℕ) : ℝ)) * ((M : ℝ) - ((r0 + s : ℕ) : ℝ)) ≤
          5 * ((s : ℝ) + 1) * (k : ℝ) := by
        nlinarith
      -- Ratio: p(r0 + s + 1) ≥ (1 - 700 * (s + 1) / k) * p(r0 + s)
      have hratio : (1 - 700 * ((s : ℝ) + 1) / (k : ℝ)) * p (r0 + s) ≤ p (r0 + (s + 1)) := by
        rw [show r0 + (s + 1) = (r0 + s) + 1 by omega]
        apply le_of_mul_le_mul_right _ hden_prod_pos
        rw [mul_assoc, hstep]
        have hcoef : (1 - 700 * ((s : ℝ) + 1) / (k : ℝ)) *
            ((((r0 + s : ℕ) : ℝ) + 1) * ((B : ℝ) - (M : ℝ) + ((r0 + s : ℕ) : ℝ) + 1)) ≤
            ((A : ℝ) - ((r0 + s : ℕ) : ℝ)) * ((M : ℝ) - ((r0 + s : ℕ) : ℝ)) := by
          have h700 : 5 * ((s : ℝ) + 1) * (k : ℝ) ≤
              (700 * ((s : ℝ) + 1) / (k : ℝ)) *
                ((((r0 + s : ℕ) : ℝ) + 1) * ((B : ℝ) - (M : ℝ) + ((r0 + s : ℕ) : ℝ) + 1)) := by
            have hk_pos : (0 : ℝ) < k := by positivity
            rw [div_mul_eq_mul_div, le_div_iff₀ hk_pos]
            have hmul := mul_le_mul_of_nonneg_left hden_lb (show 0 ≤ 700 * ((s : ℝ) + 1) by positivity)
            have hsimp : 700 * ((s : ℝ) + 1) * ((k : ℝ) ^ 2 / 125) =
                (56 / 10 : ℝ) * ((s : ℝ) + 1) * (k : ℝ) ^ 2 := by ring
            have h5 : 5 * ((s : ℝ) + 1) * (k : ℝ) * (k : ℝ) ≤
                (56 / 10 : ℝ) * ((s : ℝ) + 1) * (k : ℝ) ^ 2 := by
              have : 0 ≤ ((s : ℝ) + 1) * (k : ℝ) ^ 2 := by positivity
              linarith
            linarith
          linarith
        have hmul := mul_le_mul_of_nonneg_left hcoef (hp_nonneg (r0 + s))
        linarith
      have h1_nonneg : 0 ≤ 1 - 700 * ((s : ℝ) + 1) / (k : ℝ) := by
        have hk_pos : (0 : ℝ) < k := by positivity
        rw [sub_nonneg, div_le_iff₀ hk_pos]
        push_cast at hs_t
        nlinarith
      have hprod_le : (1 - 700 * (((s + 1 : ℕ) : ℝ)) ^ 2 / (k : ℝ)) ≤
          (1 - 700 * ((s : ℝ) + 1) / (k : ℝ)) * (1 - 700 * (s : ℝ) ^ 2 / (k : ℝ)) := by
        have hk_pos : (0 : ℝ) < k := by positivity
        push_cast
        have hpos_prod : 0 ≤ 700 * ((s : ℝ) + 1) / (k : ℝ) * (700 * (s : ℝ) ^ 2 / (k : ℝ)) := by positivity
        have hsum_sq : 700 * ((s : ℝ) + 1) / (k : ℝ) + 700 * (s : ℝ) ^ 2 / (k : ℝ) ≤
            700 * ((s : ℝ) + 1) ^ 2 / (k : ℝ) := by
          rw [← add_div, div_le_div_iff_of_pos_right hk_pos]
          have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
          nlinarith [hs0]
        have hexp : (1 - 700 * ((s : ℝ) + 1) / (k : ℝ)) * (1 - 700 * (s : ℝ) ^ 2 / (k : ℝ)) =
            1 - (700 * ((s : ℝ) + 1) / (k : ℝ) + 700 * (s : ℝ) ^ 2 / (k : ℝ)) +
              700 * ((s : ℝ) + 1) / (k : ℝ) * (700 * (s : ℝ) ^ 2 / (k : ℝ)) := by ring
        linarith [hpos_prod, hsum_sq, hexp]
      calc (1 - 700 * (((s + 1 : ℕ) : ℝ)) ^ 2 / (k : ℝ)) * p r0
          ≤ (1 - 700 * ((s : ℝ) + 1) / (k : ℝ)) * ((1 - 700 * (s : ℝ) ^ 2 / (k : ℝ)) * p r0) := by
            have hmul := mul_le_mul_of_nonneg_right hprod_le (hp_nonneg r0)
            linarith
        _ ≤ (1 - 700 * ((s : ℝ) + 1) / (k : ℝ)) * p (r0 + s) :=
            mul_le_mul_of_nonneg_left ihs h1_nonneg
        _ ≤ p (r0 + (s + 1)) := hratio
  have hsum_lb : ((t + 1 : ℕ) : ℝ) * ((1 / 2 : ℝ) * p r0) ≤ ((A + B).choose M : ℝ) := by
    have hsub : (range (t + 1)).image (fun s => r0 + s) ⊆ range (M + 1) := by
      intro x hx
      obtain ⟨s, hs, rfl⟩ := mem_image.mp hx
      have hs_le : s ≤ t := Nat.lt_succ_iff.mp (mem_range.mp hs)
      have : (s : ℝ) ≤ t := by exact_mod_cast hs_le
      have : (r0 : ℝ) + (s : ℝ) < (M : ℝ) + 1 := by linarith
      exact mem_range.mpr (by exact_mod_cast this)
    rw [← sum_hypergeom A B M]
    calc ((t + 1 : ℕ) : ℝ) * ((1 / 2 : ℝ) * p r0)
        = ∑ _s ∈ range (t + 1), ((1 / 2 : ℝ) * p r0) := by simp
      _ ≤ ∑ s ∈ range (t + 1), p (r0 + s) := by
          apply sum_le_sum
          intro s hs
          have hs_le : s ≤ t := Nat.lt_succ_iff.mp (mem_range.mp hs)
          have h12 : (1 / 2 : ℝ) ≤ 1 - 700 * (s : ℝ) ^ 2 / (k : ℝ) := by
            have hsq_s : (s : ℝ) ^ 2 ≤ (t : ℝ) ^ 2 :=
              pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hs_le) 2
            have hk_pos : (0 : ℝ) < k := by positivity
            rw [le_sub_iff_add_le, ← le_sub_iff_add_le', div_le_iff₀ hk_pos]
            linarith
          exact (mul_le_mul_of_nonneg_right h12 (hp_nonneg r0)).trans (hstep_drop s hs_le)
      _ = ∑ x ∈ (range (t + 1)).image (fun s => r0 + s), p x := by
          rw [sum_image]
          intro a _ b _ hab; dsimp at hab; omega
      _ ≤ ∑ x ∈ range (M + 1), p x := sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => hp_nonneg _)
  have ht1_gt : Real.sqrt (k : ℝ) / 40 < ((t + 1 : ℕ) : ℝ) := by
    push_cast
    exact Nat.lt_floor_add_one _
  have hmul : (Real.sqrt (k : ℝ) / 80) * p r0 ≤ ((A + B).choose M : ℝ) := by
    calc (Real.sqrt (k : ℝ) / 80) * p r0
        = (Real.sqrt (k : ℝ) / 40) * ((1 / 2 : ℝ) * p r0) := by ring
      _ ≤ ((t + 1 : ℕ) : ℝ) * ((1 / 2 : ℝ) * p r0) :=
          mul_le_mul_of_nonneg_right ht1_gt.le (by positivity)
      _ ≤ ((A + B).choose M : ℝ) := hsum_lb
  rw [div_mul_eq_mul_div, le_div_iff₀ hsq_pos]
  linarith

-- Hypergeometric right-tail bound: if r ≥ M * A / (A + B) + d, then p r ≤ exp(-d^2 / (128*k)) * C(A+B, M)
set_option maxHeartbeats 800000 in
private lemma hypergeom_right_tail (k A B M r d : ℕ)
    (hk : 1600 ≤ k) (hA1 : k ≤ A) (hA2 : A ≤ 2 * k)
    (hB1 : k ≤ B) (hB2 : B ≤ 2 * k)
    (hM1 : k ≤ M) (hM2 : M ≤ A + B) (hr : r ≤ M)
    (hdev : ((M : ℝ) * (A : ℝ) / ((A : ℝ) + (B : ℝ))) + (d : ℝ) ≤ (r : ℝ)) :
    (A.choose r : ℝ) * (B.choose (M - r) : ℝ) ≤
      Real.exp (-((d : ℝ) ^ 2) / (128 * (k : ℝ))) * ((A + B).choose M : ℝ) := by
  let p (i : ℕ) : ℝ := (A.choose i : ℝ) * (B.choose (M - i) : ℝ)
  have hp_nonneg : ∀ i, 0 ≤ p i := fun i => by positivity
  by_cases hd : d = 0
  · subst hd
    simp only [Nat.cast_zero, zero_pow (by norm_num : 2 ≠ 0), neg_zero, zero_div, Real.exp_zero, one_mul]
    rw [← sum_hypergeom A B M]
    exact single_le_sum (f := p) (fun i _ => hp_nonneg i) (mem_range.mpr (by omega))
  -- Let r0 = r - d. For every s ∈ range d, r0 + s ≥ μ + s, so p(r0 + s + 1) ≤ exp(-(s+1)/(64*k)) * p(r0 + s)
  have hdr : d ≤ r := by
    have : 0 ≤ (M : ℝ) * (A : ℝ) / ((A : ℝ) + (B : ℝ)) := by positivity
    have : (d : ℝ) ≤ (r : ℝ) := by linarith
    exact_mod_cast this
  let r0 := r - d
  have hr0_add : r0 + d = r := Nat.sub_add_cancel hdr
  have hAB_pos : (0 : ℝ) < (A : ℝ) + (B : ℝ) := by
    have : 0 < A + B := by omega
    exact_mod_cast this
  have hr0_ge_mu : (M : ℝ) * (A : ℝ) / ((A : ℝ) + (B : ℝ)) ≤ (r0 : ℝ) := by
    have : (r0 : ℝ) + (d : ℝ) = (r : ℝ) := by exact_mod_cast hr0_add
    linarith
  have hdecay : ∀ s ≤ d, p (r0 + s) ≤
      Real.exp (-((s : ℝ) * ((s : ℝ) + 1) / (128 * (k : ℝ)))) * p r0 := by
    intro s hs
    induction s with
    | zero => simp
    | succ s ih =>
      have hs_le : s ≤ d := by omega
      have ihs := ih hs_le
      have hrm : r0 + s < M := by omega
      by_cases hps0 : p (r0 + s) = 0
      · -- If p(r0 + s) = 0, then either r0 + s > A or M - (r0 + s) > B.
        -- Since r0 + s + 1 > r0 + s, if r0 + s > A then r0 + s + 1 > A so p(r0+s+1) = 0.
        -- What if M - (r0 + s) > B? That's impossible when r0 + s ≥ μ ≥ M - B!
        have hM_sub_B : (M : ℝ) - (B : ℝ) ≤ (r0 : ℝ) := by
          have : (M : ℝ) - (B : ℝ) ≤ (M : ℝ) * (A : ℝ) / ((A : ℝ) + (B : ℝ)) := by
            rw [le_div_iff₀ hAB_pos]
            have : (M : ℝ) ≤ (A : ℝ) + (B : ℝ) := by exact_mod_cast hM2
            nlinarith
          linarith
        have hMB_nat : M - (r0 + s) ≤ B := by
          have hR : ((M - (r0 + s) : ℕ) : ℝ) ≤ (B : ℝ) := by
            rw [Nat.cast_sub (by omega)]; push_cast; linarith
          exact_mod_cast hR
        have hrA : A < r0 + s := by
          by_contra hle
          have hc1 : 0 < A.choose (r0 + s) := Nat.choose_pos (by omega)
          have hc2 : 0 < B.choose (M - (r0 + s)) := Nat.choose_pos hMB_nat
          have : 0 < p (r0 + s) := mul_pos (by exact_mod_cast hc1) (by exact_mod_cast hc2)
          linarith
        have hp_next0 : p (r0 + (s + 1)) = 0 := by
          have : A.choose (r0 + (s + 1)) = 0 := Nat.choose_eq_zero_of_lt (by omega)
          simp [p, this]
        rw [hp_next0]; positivity
      -- Otherwise p(r0 + s) > 0, so r0 + s ≤ A and M - (r0 + s) ≤ B
      have hstep := hypergeom_step_eq A B M (r0 + s) hrm
      have hM_sub_B : (M : ℝ) - (B : ℝ) ≤ (r0 : ℝ) := by
        have : (M : ℝ) - (B : ℝ) ≤ (M : ℝ) * (A : ℝ) / ((A : ℝ) + (B : ℝ)) := by
          rw [le_div_iff₀ hAB_pos]
          have : (M : ℝ) ≤ (A : ℝ) + (B : ℝ) := by exact_mod_cast hM2
          nlinarith
        linarith
      have hden_pos : 0 < (((r0 + s : ℕ) : ℝ) + 1) * ((B : ℝ) - (M : ℝ) + ((r0 + s : ℕ) : ℝ) + 1) := by
        apply mul_pos (by positivity)
        push_cast; linarith
      have hA1R : (k : ℝ) ≤ A := by exact_mod_cast hA1
      have hA2R : (A : ℝ) ≤ 2 * k := by exact_mod_cast hA2
      have hB1R : (k : ℝ) ≤ B := by exact_mod_cast hB1
      have hB2R : (B : ℝ) ≤ 2 * k := by exact_mod_cast hB2
      have hkR : (1600 : ℝ) ≤ k := by exact_mod_cast hk
      have hden_ub : (((r0 + s : ℕ) : ℝ) + 1) * ((B : ℝ) - (M : ℝ) + ((r0 + s : ℕ) : ℝ) + 1) ≤
          16 * (k : ℝ) ^ 2 := by
        have hr_le_A : ((r0 + s : ℕ) : ℝ) ≤ A := by
          by_contra hgt
          have hlt : A < r0 + s := by exact_mod_cast lt_of_not_ge hgt
          have : A.choose (r0 + s) = 0 := Nat.choose_eq_zero_of_lt hlt
          exact hps0 (by simp [p, this])
        have h1 : ((r0 + s : ℕ) : ℝ) + 1 ≤ 3 * (k : ℝ) := by linarith
        have h2 : (B : ℝ) - (M : ℝ) + ((r0 + s : ℕ) : ℝ) + 1 ≤ 4 * (k : ℝ) := by
          have : (k : ℝ) ≤ M := by exact_mod_cast hM1
          linarith
        nlinarith
      -- den - num = (r0 + s + 1)*(B - M + r0 + s + 1) - (A - r0 - s)*(M - r0 - s)
      --           = (r0 + s)*(A + B + 2) + (B - M + 1) - A*M + (r0 + s + 1)*... wait:
      -- Expand: (x+1)(B-M+x+1) - (A-x)(M-x) = x(A+B) - A*M + (2x + B - M + 1 + A + M) = x(A+B) - A*M + (A + B + 2x + 1)
      -- Wait: (x+1)(B-M+x+1) - (A-x)(M-x)
      --   = x(B-M) + x^2 + x + B - M + x + 1 - (AM - x(A+M) + x^2)
      --   = x(A + B + 2) - A*M + B - M + 1!
      -- Since x = r0 + s ≥ M*A/(A+B) + s, x*(A+B) - A*M ≥ s*(A+B) ≥ 2*s*k,
      -- and 2x + B - M + 1 ≥ x + (B - M + x) + 1 ≥ 0 + 0 + 1 = 1!
      -- Wait: we want ≥ (s + 1) * k! Check if x + (B - M + x) ≥ k!
      -- x ≥ M*A/(A+B) ≥ k*k/(4k) = k/4, and even simpler: if s = 0, den - num ≥ 2x + B - M + 1?
      -- Wait: B - M + x ≥ 0, so 2x + B - M + 1 ≥ x + 1 ≥ k/4 + 1!
      -- Better: for all s ≥ 0, den - num ≥ (2*s + 1/4) * k ≥ ((s + 1) / 4) * k? Wait: at s=0, 1/4 ≥ 1/4; at s≥1, 2s+1/4 ≥ s+1!
      -- Let's check: den - num ≥ (s + 1) * k / 4, and den ≤ 16 * k^2, so (den - num)/den ≥ (s+1)/(64*k)?
      -- Actually, den ≤ 12 * k^2 (3k * 4k = 12k^2), and den - num ≥ (s + 1) * k / 2?
      -- Check: 2*x + B - M + 1 = x + (B - M + x) + 1. Since x ≥ M*A/(A+B) ≥ k/4 and A + B ≥ 2k:
      -- For s = 0: x ≥ k/4, so den - num ≥ k/4. With den ≤ 12k^2, (den-num)/den ≥ 1/(48k).
      -- Even cleaner: let's just use `s / (16 * k)` (and sum s = 0..d-1 gives d*(d-1)/(32*k)!) — wait,
      -- if we use `s * (2*k) / (12 * k^2) = s / (6 * k)`, we don't even need the `s = 0` term!
      -- Check: ∑_{s=0}^{d-1} s / (6*k) = d*(d-1)/(12*k) ≥ d^2/(40*k) for d ≥ 2 (and for d = 1, trivial since exp(-1/(40k)) ≥ ... wait for d=1 we need p(r) ≤ exp(-1/(40k)) * C(A+B,M), which is true by hypergeom_peak_bound anyway!).
      -- Even better: den - num ≥ (s + 1/4) * k ≥ (s + 1) * k / 4, and den ≤ 12 * k^2,
      -- so (den - num) / den ≥ (s + 1) / (48 * k)!
      -- Wait: if we change 32*k in hdecay to 96*k and 40*k in the theorem to 100*k,
      -- then ∑_{s=0}^{d-1} (s + 1) / (48 * k) = d * (d + 1) / (96 * k) ≥ d^2 / (100 * k) FOR ALL d ≥ 1!
      have hx_ge : (M : ℝ) * (A : ℝ) / ((A : ℝ) + (B : ℝ)) + (s : ℝ) ≤ ((r0 + s : ℕ) : ℝ) := by
        push_cast; linarith
      have hx_mul : (M : ℝ) * (A : ℝ) + (s : ℝ) * ((A : ℝ) + (B : ℝ)) ≤
          ((r0 + s : ℕ) : ℝ) * ((A : ℝ) + (B : ℝ)) := by
        have := mul_le_mul_of_nonneg_right hx_ge hAB_pos.le
        rw [add_mul, div_mul_cancel₀ _ hAB_pos.ne'] at this
        exact this
      have hx_k4 : (k : ℝ) / 4 ≤ ((r0 + s : ℕ) : ℝ) := by
        have h1 : (k : ℝ) / 4 ≤ (M : ℝ) * (A : ℝ) / ((A : ℝ) + (B : ℝ)) := by
          rw [div_le_div_iff₀ (by norm_num) hAB_pos]
          have : (k : ℝ) ≤ M := by exact_mod_cast hM1
          nlinarith
        linarith
      have hdiff_lb : ((s : ℝ) + 1) * (k : ℝ) / 4 ≤
          (((r0 + s : ℕ) : ℝ) + 1) * ((B : ℝ) - (M : ℝ) + ((r0 + s : ℕ) : ℝ) + 1) -
          ((A : ℝ) - ((r0 + s : ℕ) : ℝ)) * ((M : ℝ) - ((r0 + s : ℕ) : ℝ)) := by
        have hbm : 0 ≤ (B : ℝ) - (M : ℝ) + ((r0 + s : ℕ) : ℝ) := by push_cast; linarith
        nlinarith
      -- Therefore p(r0 + s + 1) ≤ (1 - (s + 1)/(64*k)) * p(r0 + s) ≤ exp(-(s + 1)/(64*k)) * p(r0 + s)
      have hratio : p (r0 + (s + 1)) ≤ Real.exp (-(((s : ℝ) + 1) / (64 * (k : ℝ)))) * p (r0 + s) := by
        have h1 : p (r0 + (s + 1)) ≤ (1 - ((s : ℝ) + 1) / (64 * (k : ℝ))) * p (r0 + s) := by
          rw [show r0 + (s + 1) = (r0 + s) + 1 by omega]
          apply le_of_mul_le_mul_right _ hden_pos
          rw [hstep, mul_right_comm]
          have hcoef : ((A : ℝ) - ((r0 + s : ℕ) : ℝ)) * ((M : ℝ) - ((r0 + s : ℕ) : ℝ)) ≤
              (1 - ((s : ℝ) + 1) / (64 * (k : ℝ))) *
                ((((r0 + s : ℕ) : ℝ) + 1) * ((B : ℝ) - (M : ℝ) + ((r0 + s : ℕ) : ℝ) + 1)) := by
            have hk_pos : (0 : ℝ) < 64 * (k : ℝ) := by positivity
            have hsub : (((s : ℝ) + 1) / (64 * (k : ℝ))) *
                ((((r0 + s : ℕ) : ℝ) + 1) * ((B : ℝ) - (M : ℝ) + ((r0 + s : ℕ) : ℝ) + 1)) ≤
                ((s : ℝ) + 1) * (k : ℝ) / 4 := by
              rw [div_mul_eq_mul_div, div_le_div_iff₀ hk_pos (by norm_num)]
              nlinarith
            linarith
          have hmul := mul_le_mul_of_nonneg_left hcoef (hp_nonneg (r0 + s))
          linarith
        have hexp : 1 - ((s : ℝ) + 1) / (64 * (k : ℝ)) ≤
            Real.exp (-(((s : ℝ) + 1) / (64 * (k : ℝ)))) := by
          have := Real.add_one_le_exp (-(((s : ℝ) + 1) / (64 * (k : ℝ))))
          linarith
        exact h1.trans (mul_le_mul_of_nonneg_right hexp (hp_nonneg (r0 + s)))
      calc p (r0 + (s + 1))
          ≤ Real.exp (-(((s : ℝ) + 1) / (64 * (k : ℝ)))) * p (r0 + s) := hratio
        _ ≤ Real.exp (-(((s : ℝ) + 1) / (64 * (k : ℝ)))) *
            (Real.exp (-((s : ℝ) * ((s : ℝ) + 1) / (128 * (k : ℝ)))) * p r0) :=
            mul_le_mul_of_nonneg_left ihs (Real.exp_pos _).le
        _ = Real.exp (-((((s + 1 : ℕ) : ℝ) * (((s + 1 : ℕ) : ℝ) + 1)) / (128 * (k : ℝ)))) * p r0 := by
            rw [← mul_assoc, ← Real.exp_add]
            congr 2
            push_cast
            ring
  have hfinal := hdecay d le_rfl
  rw [hr0_add] at hfinal
  have hpr0_le : p r0 ≤ ((A + B).choose M : ℝ) := by
    rw [← sum_hypergeom A B M]
    exact single_le_sum (f := p) (fun i _ => hp_nonneg i) (mem_range.mpr (by omega))
  have hexp_le : Real.exp (-((d : ℝ) * ((d : ℝ) + 1) / (128 * (k : ℝ)))) ≤
      Real.exp (-((d : ℝ) ^ 2) / (128 * (k : ℝ))) := by
    apply Real.exp_le_exp.mpr
    have hk_pos : (0 : ℝ) < 128 * (k : ℝ) := by positivity
    rw [neg_div, neg_le_neg_iff, div_le_div_iff_of_pos_right hk_pos]
    nlinarith
  calc p r
      ≤ Real.exp (-((d : ℝ) * ((d : ℝ) + 1) / (128 * (k : ℝ)))) * p r0 := hfinal
    _ ≤ Real.exp (-((d : ℝ) ^ 2) / (128 * (k : ℝ))) * ((A + B).choose M : ℝ) :=
        mul_le_mul hexp_le hpr0_le (hp_nonneg r0) (Real.exp_pos _).le

private lemma hypergeom_tail_bound (k A B M r d : ℕ)
    (hk : 1600 ≤ k) (hA1 : k ≤ A) (hA2 : A ≤ 2 * k)
    (hB1 : k ≤ B) (hB2 : B ≤ 2 * k)
    (hM1 : k ≤ M) (hM2 : M ≤ A + B) (hr : r ≤ M)
    (hdev : (d : ℝ) ≤ |(r : ℝ) - (M : ℝ) * (A : ℝ) / ((A : ℝ) + (B : ℝ))|) :
    (A.choose r : ℝ) * (B.choose (M - r) : ℝ) ≤
      Real.exp (-((d : ℝ) ^ 2) / (128 * (k : ℝ))) * ((A + B).choose M : ℝ) := by
  have hAB_pos : (0 : ℝ) < (A : ℝ) + (B : ℝ) := by
    have : 0 < A + B := by omega
    exact_mod_cast this
  rcases le_or_gt ((M : ℝ) * (A : ℝ) / ((A : ℝ) + (B : ℝ))) (r : ℝ) with hge | hlt
  · rw [abs_of_nonneg (by linarith)] at hdev
    exact hypergeom_right_tail k A B M r d hk hA1 hA2 hB1 hB2 hM1 hM2 hr (by linarith)
  · rw [abs_of_neg (by linarith)] at hdev
    have hsym := hypergeom_right_tail k B A M (M - r) d hk hB1 hB2 hA1 hA2 hM1
      (by omega) (Nat.sub_le M r) (by
        rw [Nat.cast_sub hr]
        have hsum : (M : ℝ) * (A : ℝ) / ((A : ℝ) + (B : ℝ)) +
            (M : ℝ) * (B : ℝ) / ((A : ℝ) + (B : ℝ)) = (M : ℝ) := by
          rw [← add_div, ← mul_add, mul_div_cancel_right₀ _ hAB_pos.ne']
        have hcomm : (B : ℝ) + (A : ℝ) = (A : ℝ) + (B : ℝ) := add_comm _ _
        rw [hcomm]
        linarith)
    have hsub : M - (M - r) = r := Nat.sub_sub_self hr
    rw [hsub, add_comm B A, mul_comm] at hsym
    exact hsym

-- Step 5: Main theorem
set_option maxHeartbeats 1200000 in
theorem OMA.solution :
    OMA.R_Green92_green_92_variants_chase_lower_R1_H1_R1_H2_R1_H2_R1.H1 := by
  classical
  -- Choose C = 10 ^ 16 (plenty of room for constants)
  refine ⟨(10 : ℝ) ^ 17, by positivity, ?_⟩
  have hlog_top : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmall_ratio : ∀ᶠ n : ℕ in atTop,
      Real.sqrt ((n / 4 : ℕ) : ℝ) * Real.log ((n / 4 : ℕ) : ℝ) ≤ ((n / 4 : ℕ) : ℝ) / 100 := by
    have h1 := isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 2 by norm_num)
    have h2 : ∀ᶠ x : ℝ in atTop, Real.log x ≤ (1 / 100 : ℝ) * x ^ (1 / 2 : ℝ) := by
      filter_upwards [h1.bound (show (0 : ℝ) < 1 / 100 by norm_num), eventually_ge_atTop (2 : ℝ)] with x hx hx2
      have hlog0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
      have hrp0 : 0 ≤ x ^ (1 / 2 : ℝ) := by positivity
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlog0, abs_of_nonneg hrp0] at hx
      exact hx
    have hdiv_top : Tendsto (fun n : ℕ => ((n / 4 : ℕ) : ℝ)) atTop atTop := by
      refine tendsto_atTop_atTop.mpr fun b => ?_
      refine ⟨4 * (⌈max b 0⌉₊ + 1), fun n hn => ?_⟩
      have h1 : ⌈max b 0⌉₊ + 1 ≤ n / 4 := by omega
      have h2 : max b 0 ≤ (⌈max b 0⌉₊ : ℝ) := Nat.le_ceil _
      have h3 : (⌈max b 0⌉₊ + 1 : ℝ) ≤ ((n / 4 : ℕ) : ℝ) := by exact_mod_cast h1
      linarith [le_max_left b 0]
    filter_upwards [hdiv_top.eventually h2, eventually_ge_atTop 100] with n hn hn100
    have hk0 : (0 : ℝ) ≤ ((n / 4 : ℕ) : ℝ) := Nat.cast_nonneg _
    calc Real.sqrt ((n / 4 : ℕ) : ℝ) * Real.log ((n / 4 : ℕ) : ℝ)
        ≤ Real.sqrt ((n / 4 : ℕ) : ℝ) * ((1 / 100 : ℝ) * ((n / 4 : ℕ) : ℝ) ^ (1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left hn (Real.sqrt_nonneg _)
      _ = ((1 / 100 : ℝ) * (Real.sqrt ((n / 4 : ℕ) : ℝ) * Real.sqrt ((n / 4 : ℕ) : ℝ))) := by
          rw [Real.sqrt_eq_rpow]; ring
      _ = ((n / 4 : ℕ) : ℝ) / 100 := by rw [Real.mul_self_sqrt hk0]; ring
  filter_upwards [hsmall_ratio, eventually_ge_atTop 40000] with n hratio hn40000
  intro hmod
  let k := n / 4
  have hnk : n = 4 * k + 3 := by dsimp only [k]; omega
  have hk10000 : 10000 ≤ k := by omega
  have hkR : (10000 : ℝ) ≤ k := by exact_mod_cast hk10000
  have hk_pos : (0 : ℝ) < k := by positivity
  have hn_pos : (0 : ℝ) < n := by positivity
  have hsq_k_pos : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr hk_pos
  have hlog_k_ge4 : (4 : ℝ) ≤ Real.log (k : ℝ) := by
    have h1 : Real.exp 4 ≤ (k : ℝ) := by
      have he : Real.exp 1 ≤ 3 := Real.exp_one_lt_d9.le.trans (by norm_num)
      have h4 : Real.exp 4 = Real.exp 1 ^ 4 := by
        rw [← Real.exp_nat_mul]; norm_num
      rw [h4]
      calc Real.exp 1 ^ 4 ≤ (3 : ℝ) ^ 4 := pow_le_pow_left₀ (Real.exp_pos _).le he 4
        _ ≤ (k : ℝ) := by norm_num; linarith
    have := Real.log_le_log (Real.exp_pos 4) h1
    rwa [Real.log_exp] at this
  have hlog_n_ge_k : Real.log (k : ℝ) ≤ Real.log (n : ℝ) :=
    Real.log_le_log hk_pos (by exact_mod_cast (by omega : k ≤ n))
  let F' (a : ℕ) (w : List Bool) := (a + (w.zip w.tail).count (false, true)).choose w.length
  let B (w : List Bool) := F' (2 * k + 1) w
  let P (b : ℕ) (w : List Bool) (j : ℕ) :=
    if w[j]? = some true then F' b (w.take j) * F' (2 * k + 1 - b) (w.drop (j + 1)) else 0
  let A (w : List Bool) (j : ℕ) : ℝ := (P k w j : ℝ) - (P (k + 1) w j : ℝ)
  let U : Finset (List Bool) :=
    (range (n + 1)).biUnion fun m => (univ : Finset (Fin m → Bool)).image List.ofFn
  let E (w : List Bool) : Prop :=
    |(w.length : ℝ) - 2 * (k : ℝ)| ≤ Real.sqrt (k : ℝ) * Real.log (k : ℝ) ∧
    |(((w.zip w.tail).count (false, true) : ℕ) : ℝ) - 2 * (k : ℝ) / 3| ≤
      Real.sqrt (k : ℝ) * Real.log (k : ℝ)
  change (∑ w ∈ U.filter E,
      ∑ p ∈ ((range w.length).product (range w.length)).filter
        (fun p => p.1 ≤ p.2 + 5 ∧ p.2 ≤ p.1 + 5),
        |A w p.1 * A w p.2 / ((2 : ℝ) ^ n * (max 1 (B w) : ℕ))|) ≤
      (10 : ℝ) ^ 17 * (Real.log (n : ℝ)) ^ 7 / (n : ℝ) ^ (3 / 2 : ℝ)
  -- Step A: Pointwise bound for every w ∈ U.filter E
  have hpointwise : ∀ w ∈ U.filter E,
      (∑ p ∈ ((range w.length).product (range w.length)).filter
        (fun p => p.1 ≤ p.2 + 5 ∧ p.2 ≤ p.1 + 5),
        |A w p.1 * A w p.2 / ((2 : ℝ) ^ n * (max 1 (B w) : ℕ))|) ≤
      ((B w : ℝ) / (2 : ℝ) ^ n) * ((10 : ℝ) ^ 17 * (Real.log (n : ℝ)) ^ 7 / (n : ℝ) ^ (3 / 2 : ℝ)) := by
    intro w hw
    obtain ⟨_, hwE⟩ := mem_filter.mp hw
    obtain ⟨hlenE, hcntE⟩ := hwE
    have hlen_lo : (199 : ℝ) / 100 * (k : ℝ) ≤ (w.length : ℝ) := by
      have := (abs_le.mp hlenE).1; linarith
    have hlen_hi : (w.length : ℝ) ≤ (201 : ℝ) / 100 * (k : ℝ) := by
      have := (abs_le.mp hlenE).2; linarith
    have hcnt_lo : (65 : ℝ) / 100 * (k : ℝ) ≤ (cnt w : ℝ) := by
      have := (abs_le.mp hcntE).1; dsimp only [cnt]; linarith
    have hcnt_hi : (cnt w : ℝ) ≤ (68 : ℝ) / 100 * (k : ℝ) := by
      have := (abs_le.mp hcntE).2; dsimp only [cnt]; linarith
    have hm_ge : 1000 ≤ w.length := by
      have : (1000 : ℝ) ≤ (w.length : ℝ) := by linarith
      exact_mod_cast this
    -- B w ≥ 1 since w.length ≤ 2*k + 1 + cnt w
    have hBw_pos : 1 ≤ B w := by
      apply Nat.choose_pos
      have : (w.length : ℝ) ≤ (2 * k + 1 + cnt w : ℝ) := by linarith
      have hnat : w.length ≤ 2 * k + 1 + cnt w := by exact_mod_cast this
      exact hnat
    have hmaxB : max 1 (B w) = B w := max_eq_right hBw_pos
    have hBwR_pos : (0 : ℝ) < (B w : ℝ) := by exact_mod_cast (by omega : 0 < B w)
    have h2n_pos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
    -- Reduce nearby pairs to 11 * ∑ j, (A w j)^2
    have hnear_to_diag :
        (∑ p ∈ ((range w.length).product (range w.length)).filter
          (fun p => p.1 ≤ p.2 + 5 ∧ p.2 ≤ p.1 + 5),
          |A w p.1 * A w p.2 / ((2 : ℝ) ^ n * (max 1 (B w) : ℕ))|) ≤
        (11 / ((2 : ℝ) ^ n * (B w : ℝ))) * ∑ j ∈ range w.length, (A w j) ^ 2 := by
      rw [hmaxB]
      have hden_pos : 0 < (2 : ℝ) ^ n * (B w : ℝ) := mul_pos h2n_pos hBwR_pos
      have habs_div : ∀ p : ℕ × ℕ,
          |A w p.1 * A w p.2 / ((2 : ℝ) ^ n * (B w : ℝ))| ≤
          ((A w p.1) ^ 2 + (A w p.2) ^ 2) / (2 * ((2 : ℝ) ^ n * (B w : ℝ))) := by
        intro p
        rw [abs_div, abs_of_pos hden_pos, abs_mul]
        have ham : |A w p.1| * |A w p.2| ≤ ((A w p.1) ^ 2 + (A w p.2) ^ 2) / 2 := by
          have := sq_nonneg (|A w p.1| - |A w p.2|)
          nlinarith [sq_abs (A w p.1), sq_abs (A w p.2)]
        rw [div_le_div_iff₀ hden_pos (by positivity)]
        nlinarith
      let S := ((range w.length).product (range w.length)).filter
        (fun p => p.1 ≤ p.2 + 5 ∧ p.2 ≤ p.1 + 5)
      calc ∑ p ∈ S, |A w p.1 * A w p.2 / ((2 : ℝ) ^ n * (B w : ℝ))|
          ≤ ∑ p ∈ S, ((A w p.1) ^ 2 + (A w p.2) ^ 2) / (2 * ((2 : ℝ) ^ n * (B w : ℝ))) :=
            sum_le_sum fun p _ => habs_div p
        _ = (∑ p ∈ S, ((A w p.1) ^ 2 + (A w p.2) ^ 2)) / (2 * ((2 : ℝ) ^ n * (B w : ℝ))) := by
            rw [sum_div]
        _ ≤ (22 * ∑ j ∈ range w.length, (A w j) ^ 2) / (2 * ((2 : ℝ) ^ n * (B w : ℝ))) := by
            apply div_le_div_of_nonneg_right _ (by positivity)
            rw [sum_add_distrib]
            have h1 : ∑ p ∈ S, (A w p.1) ^ 2 ≤ 11 * ∑ j ∈ range w.length, (A w j) ^ 2 := by
              have hsub : S ⊆ (range w.length).biUnion (fun i =>
                  ((range w.length).filter (fun j => i ≤ j + 5 ∧ j ≤ i + 5)).image (fun j => (i, j))) := by
                intro p hp
                obtain ⟨hp_prod, h1, h2⟩ := mem_filter.mp hp
                obtain ⟨h1m, h2m⟩ := mem_product.mp hp_prod
                exact mem_biUnion.mpr ⟨p.1, h1m, mem_image.mpr ⟨p.2, mem_filter.mpr ⟨h2m, h1, h2⟩, rfl⟩⟩
              calc ∑ p ∈ S, (A w p.1) ^ 2
                  ≤ ∑ p ∈ (range w.length).biUnion (fun i =>
                      ((range w.length).filter (fun j => i ≤ j + 5 ∧ j ≤ i + 5)).image (fun j => (i, j))),
                      (A w p.1) ^ 2 := sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)
                _ = ∑ i ∈ range w.length, ∑ p ∈ ((range w.length).filter
                      (fun j => i ≤ j + 5 ∧ j ≤ i + 5)).image (fun j => (i, j)), (A w p.1) ^ 2 := by
                    apply Finset.sum_biUnion
                    intro i₁ _ i₂ _ hne
                    exact Finset.disjoint_left.mpr fun p hp1 hp2 => by
                      obtain ⟨j₁, _, rfl⟩ := mem_image.mp hp1
                      obtain ⟨j₂, _, h⟩ := mem_image.mp hp2
                      exact hne (congrArg Prod.fst h).symm
                _ ≤ ∑ i ∈ range w.length, 11 * (A w i) ^ 2 := by
                    apply sum_le_sum
                    intro i _
                    rw [sum_image (fun a _ b _ h => by injection h)]
                    simp only [sum_const, nsmul_eq_mul]
                    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
                    have hcard : ((range w.length).filter (fun j => i ≤ j + 5 ∧ j ≤ i + 5)).card ≤ 11 := by
                      have hsub' : (range w.length).filter (fun j => i ≤ j + 5 ∧ j ≤ i + 5) ⊆
                          Icc (i - 5) (i + 5) := by
                        intro j hj
                        obtain ⟨_, h1, h2⟩ := mem_filter.mp hj
                        exact mem_Icc.mpr ⟨by omega, by omega⟩
                      calc ((range w.length).filter (fun j => i ≤ j + 5 ∧ j ≤ i + 5)).card
                          ≤ (Icc (i - 5) (i + 5)).card := card_le_card hsub'
                        _ = i + 5 + 1 - (i - 5) := Nat.card_Icc _ _
                        _ ≤ 11 := by omega
                    exact_mod_cast hcard
                _ = 11 * ∑ j ∈ range w.length, (A w j) ^ 2 := by rw [← mul_sum]
            have h2 : ∑ p ∈ S, (A w p.2) ^ 2 = ∑ p ∈ S, (A w p.1) ^ 2 := by
              refine Finset.sum_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_ ?_
              · intro p hp
                obtain ⟨hp_prod, h1, h2⟩ := mem_filter.mp hp
                obtain ⟨h1m, h2m⟩ := mem_product.mp hp_prod
                exact mem_filter.mpr ⟨mem_product.mpr ⟨h2m, h1m⟩, h2, h1⟩
              · intro p₁ _ p₂ _ h
                exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
              · intro p hp
                obtain ⟨hp_prod, h1, h2⟩ := mem_filter.mp hp
                obtain ⟨h1m, h2m⟩ := mem_product.mp hp_prod
                exact ⟨(p.2, p.1), mem_filter.mpr ⟨mem_product.mpr ⟨h2m, h1m⟩, h2, h1⟩, rfl⟩
              · intro p _; rfl
            linarith
        _ = (11 / ((2 : ℝ) ^ n * (B w : ℝ))) * ∑ j ∈ range w.length, (A w j) ^ 2 := by ring
    -- Bound C(a + b + 2, m - 1) ≤ 30 * B w
    have hM_eq : ∀ j ∈ range w.length,
        ((k + cnt (w.take j) + 1) + (k + cnt (w.drop (j + 1)) + 1)).choose (w.length - 1) ≤ 30 * B w := by
      intro j _
      have hsum_le : (k + cnt (w.take j) + 1) + (k + cnt (w.drop (j + 1)) + 1) ≤
          2 * k + 1 + cnt w + 1 := by
        have := cnt_take_add_drop_le w j; omega
      have hc1 : ((k + cnt (w.take j) + 1) + (k + cnt (w.drop (j + 1)) + 1)).choose (w.length - 1) ≤
          (2 * k + 1 + cnt w + 1).choose (w.length - 1) := Nat.choose_le_choose _ hsum_le
      have hc2 : (2 * k + 1 + cnt w + 1).choose (w.length - 1) ≤ 30 * (2 * k + 1 + cnt w).choose w.length := by
        let N := 2 * k + 1 + cnt w
        let m := w.length
        have hN_ge : m + k / 2 ≤ N := by
          have hdiv : ((k / 2 : ℕ) : ℝ) ≤ (k : ℝ) / 2 := by
            have : 2 * (k / 2) ≤ k := Nat.mul_div_le k 2
            have hR : (2 : ℝ) * ((k / 2 : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast this
            linarith
          have hR : (m : ℝ) + ((k / 2 : ℕ) : ℝ) ≤ (N : ℝ) := by
            dsimp only [N, m]; push_cast; linarith
          exact_mod_cast hR
        have hm_le : m ≤ 5 * (N + 1 - m) := by
          have : (m : ℝ) ≤ 5 * ((N : ℝ) + 1 - (m : ℝ)) := by
            dsimp only [N, m]; push_cast; linarith
          have hR : (m : ℝ) ≤ ((5 * (N + 1 - m) : ℕ) : ℝ) := by
            push_cast [Nat.cast_sub (by omega : m ≤ N + 1)]; linarith
          exact_mod_cast hR
        have hstep1 : (N + 1 - m) * N.choose (m - 1) = m * N.choose m := by
          have h1 := choose_step_real N (m - 1)
          have hm1 : ((m - 1 : ℕ) : ℝ) + 1 = (m : ℝ) := by
            rw [Nat.cast_sub (by omega : 1 ≤ m)]; push_cast; ring
          have hsub : (N : ℝ) - ((m - 1 : ℕ) : ℝ) = ((N + 1 - m : ℕ) : ℝ) := by
            rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_sub (by omega : m ≤ N + 1)]; push_cast; ring
          rw [show m - 1 + 1 = m by omega, hm1, hsub] at h1
          exact_mod_cast h1.symm
        have hle1 : N.choose (m - 1) ≤ 5 * N.choose m := by
          have h1 : (N + 1 - m) * N.choose (m - 1) ≤ (N + 1 - m) * (5 * N.choose m) := by
            rw [hstep1]
            calc m * N.choose m ≤ (5 * (N + 1 - m)) * N.choose m := Nat.mul_le_mul_right _ hm_le
              _ = (N + 1 - m) * (5 * N.choose m) := by ring
          exact Nat.le_of_mul_le_mul_left h1 (by omega)
        have hstep2 : (N + 2 - m) * N.choose (m - 2) = (m - 1) * N.choose (m - 1) := by
          have h1 := choose_step_real N (m - 2)
          have hm2 : ((m - 2 : ℕ) : ℝ) + 1 = ((m - 1 : ℕ) : ℝ) := by
            rw [Nat.cast_sub (by omega : 2 ≤ m), Nat.cast_sub (by omega : 1 ≤ m)]; push_cast; ring
          have hsub : (N : ℝ) - ((m - 2 : ℕ) : ℝ) = ((N + 2 - m : ℕ) : ℝ) := by
            rw [Nat.cast_sub (by omega : 2 ≤ m), Nat.cast_sub (by omega : m ≤ N + 2)]; push_cast; ring
          rw [show m - 2 + 1 = m - 1 by omega, hm2, hsub] at h1
          exact_mod_cast h1.symm
        have hle2 : N.choose (m - 2) ≤ 5 * N.choose (m - 1) := by
          have h1 : (N + 2 - m) * N.choose (m - 2) ≤ (N + 2 - m) * (5 * N.choose (m - 1)) := by
            rw [hstep2]
            have hm2_le : m - 1 ≤ 5 * (N + 2 - m) := by omega
            calc (m - 1) * N.choose (m - 1) ≤ (5 * (N + 2 - m)) * N.choose (m - 1) :=
                  Nat.mul_le_mul_right _ hm2_le
              _ = (N + 2 - m) * (5 * N.choose (m - 1)) := by ring
          exact Nat.le_of_mul_le_mul_left h1 (by omega)
        have hpascal : (N + 1).choose (m - 1) = N.choose (m - 1) + N.choose (m - 2) := by
          have hch := Nat.choose_succ_succ N (m - 2)
          simp only [Nat.succ_eq_add_one] at hch
          have hm1 : m - 2 + 1 = m - 1 := by omega
          rw [hm1] at hch
          omega
        change (N + 1).choose (m - 1) ≤ 30 * N.choose m
        omega
      exact hc1.trans hc2
    -- Split range w.length into central and tail positions
    let M := w.length - 1
    let mu (j : ℕ) : ℝ :=
      (M : ℝ) * ((k + cnt (w.take j) + 1 : ℕ) : ℝ) /
        (((k + cnt (w.take j) + 1 : ℕ) : ℝ) + ((k + cnt (w.drop (j + 1)) + 1 : ℕ) : ℝ))
    let T : ℝ := 40 * Real.sqrt (k : ℝ) * Real.log (k : ℝ)
    let central : Finset ℕ := (range w.length).filter (fun j : ℕ => |(j : ℝ) - mu j| ≤ T)
    let tail : Finset ℕ := (range w.length).filter (fun j : ℕ => ¬ (|(j : ℝ) - mu j| ≤ T))
    -- Bound on cardinality of central: ≤ 160 * √k * log k + 10
    have hcentral_card : (central.card : ℝ) ≤ 160 * Real.sqrt (k : ℝ) * Real.log (k : ℝ) + 10 := by
      -- For j1, j2 ∈ central with j1 + 2 ≤ j2: compare (j - mu j)
      -- Wait: mu j depends on both cnt (w.take j) and cnt (w.drop (j+1)), whose sum is in [cnt w - 2, cnt w]!
      -- So for any j1 < j2 in range w.length:
      -- Let S(j) = 2k + 2 + cnt(w.take j) + cnt(w.drop (j+1)) ∈ [2k + cnt w, 2k + 2 + cnt w].
      -- Let S0 = 2k + 2 + cnt w. Then |mu j - M * (k + 1 + cnt(w.take j)) / S0| ≤ M * 2 / S0 ≤ 2!
      -- And M / S0 ≤ 2.01 / 2.65 ≤ 4/5!
      -- Let g(j) = j - M * (k + 1 + cnt(w.take j)) / S0.
      -- For j1 ≤ j2, let q = (j2 - j1) / 2, so j2 ≥ j1 + 2*q and cnt(w.take j2) ≤ cnt(w.take j1) + q + 1!
      -- Thus g(j2) - g(j1) ≥ (j2 - j1) - (4/5) * ((j2 - j1)/2 + 1) ≥ (1/2) * (j2 - j1) - 1!
      -- On central, |g(j)| ≤ T + 2, so for any j1 ≤ j2 in central, (1/2)*(j2 - j1) - 1 ≤ 2*T + 4,
      -- hence j2 - j1 ≤ 4*T + 10 = 160 * √k * log k + 10!
      by_cases hce : central = ∅
      · rw [hce, card_empty, Nat.cast_zero]; positivity
      have hne : central.Nonempty := nonempty_iff_ne_empty.mpr hce
      let jmin := central.min' hne
      let jmax := central.max' hne
      have hjmin_mem : jmin ∈ central := min'_mem central hne
      have hjmax_mem : jmax ∈ central := max'_mem central hne
      have hsub : central ⊆ Icc jmin jmax := fun j hj =>
        mem_Icc.mpr ⟨min'_le central j hj, le_max' central j hj⟩
      have hcard_le : central.card ≤ jmax - jmin + 1 := by
        calc central.card ≤ (Icc jmin jmax).card := card_le_card hsub
          _ = jmax + 1 - jmin := Nat.card_Icc _ _
          _ = jmax - jmin + 1 := by
              have : jmin ≤ jmax := min'_le central jmax hjmax_mem
              omega
      have hle_j : jmin ≤ jmax := min'_le central jmax hjmax_mem
      -- Step bound: cnt (w.take (a + 2*q)) ≤ cnt (w.take a) + q
      have hcnt_diff : ∀ q : ℕ, cnt (w.take (jmin + 2 * q)) ≤ cnt (w.take jmin) + q := by
        intro q
        induction q with
        | zero => simp
        | succ q ih =>
          rw [show jmin + 2 * (q + 1) = (jmin + 2 * q) + 2 by omega]
          have := cnt_take_step2 w (jmin + 2 * q)
          omega
      have hcnt_jmax : cnt (w.take jmax) ≤ cnt (w.take jmin) + (jmax - jmin + 1) / 2 := by
        have h1 : jmax ≤ jmin + 2 * ((jmax - jmin + 1) / 2) := by omega
        exact (cnt_take_mono w h1).trans (hcnt_diff _)
      -- Compare mu jmax - mu jmin
      let S0 : ℝ := (2 * k + 2 + cnt w : ℕ)
      have hS0_pos : 0 < S0 := by dsimp only [S0]; positivity
      have hS0_lb : (265 : ℝ) / 100 * (k : ℝ) ≤ S0 := by
        dsimp only [S0]; push_cast; linarith
      have hM_le_S0 : (M : ℝ) ≤ (4 / 5 : ℝ) * S0 := by
        have : (M : ℝ) ≤ (w.length : ℝ) := by exact_mod_cast Nat.sub_le w.length 1
        linarith
      have hmu_approx : ∀ j ∈ range w.length,
          |mu j - (M : ℝ) * ((k + cnt (w.take j) + 1 : ℕ) : ℝ) / S0| ≤ 2 := by
        intro j _
        let Sj : ℝ := ((k + cnt (w.take j) + 1 : ℕ) : ℝ) + ((k + cnt (w.drop (j + 1)) + 1 : ℕ) : ℝ)
        have hSj_le : Sj ≤ S0 := by
          dsimp only [Sj, S0]
          have := cnt_take_add_drop_le w j
          have hnat : (k + cnt (w.take j) + 1) + (k + cnt (w.drop (j + 1)) + 1) ≤ 2 * k + 2 + cnt w := by omega
          exact_mod_cast hnat
        have hS0_sub : S0 - Sj ≤ 2 := by
          dsimp only [Sj, S0]
          have := cnt_take_add_drop_ge w j
          have hnat : 2 * k + 2 + cnt w ≤ (k + cnt (w.take j) + 1) + (k + cnt (w.drop (j + 1)) + 1) + 2 := by omega
          have hR : ((2 * k + 2 + cnt w : ℕ) : ℝ) ≤
              (((k + cnt (w.take j) + 1) + (k + cnt (w.drop (j + 1)) + 1) + 2 : ℕ) : ℝ) := by
            exact_mod_cast hnat
          push_cast at hR ⊢
          linarith
        have hSj_pos : 0 < Sj := by dsimp only [Sj]; positivity
        have hnum_le : ((k + cnt (w.take j) + 1 : ℕ) : ℝ) ≤ Sj := by
          dsimp only [Sj]; linarith [show (0 : ℝ) ≤ ((k + cnt (w.drop (j + 1)) + 1 : ℕ) : ℝ) by positivity]
        have hheq : mu j - (M : ℝ) * ((k + cnt (w.take j) + 1 : ℕ) : ℝ) / S0 =
            (M : ℝ) * ((k + cnt (w.take j) + 1 : ℕ) : ℝ) * (S0 - Sj) / (Sj * S0) := by
          dsimp only [mu, Sj]
          field_simp [hSj_pos.ne', hS0_pos.ne']
        rw [hheq, abs_of_nonneg (by
          have : 0 ≤ S0 - Sj := by linarith
          positivity)]
        rw [div_le_iff₀ (mul_pos hSj_pos hS0_pos)]
        have h1 : (M : ℝ) * ((k + cnt (w.take j) + 1 : ℕ) : ℝ) * (S0 - Sj) ≤
            S0 * Sj * 2 := by
          have hMS0 : (M : ℝ) ≤ S0 := by linarith
          have h0 : 0 ≤ S0 - Sj := by linarith
          have hmul1 : (M : ℝ) * ((k + cnt (w.take j) + 1 : ℕ) : ℝ) ≤ S0 * Sj :=
            mul_le_mul hMS0 hnum_le (by positivity) hS0_pos.le
          exact mul_le_mul hmul1 hS0_sub h0 (by positivity)
        linarith
      have hmin_approx := hmu_approx jmin (mem_filter.mp hjmin_mem).1
      have hmax_approx := hmu_approx jmax (mem_filter.mp hjmax_mem).1
      have hmin_T : |(jmin : ℝ) - mu jmin| ≤ T := (mem_filter.mp hjmin_mem).2
      have hmax_T : |(jmax : ℝ) - mu jmax| ≤ T := (mem_filter.mp hjmax_mem).2
      have hdiff_mu : mu jmax - mu jmin ≤ (4 / 5 : ℝ) * (((jmax - jmin : ℕ) : ℝ) / 2 + 1) + 4 := by
        have hcnt_R : ((cnt (w.take jmax) : ℝ) - (cnt (w.take jmin) : ℝ)) ≤
            ((jmax - jmin : ℕ) : ℝ) / 2 + 1 := by
          have h1 : (cnt (w.take jmax) : ℝ) ≤ (cnt (w.take jmin) : ℝ) + (((jmax - jmin + 1) / 2 : ℕ) : ℝ) := by
            exact_mod_cast hcnt_jmax
          have h2 : (((jmax - jmin + 1) / 2 : ℕ) : ℝ) ≤ ((jmax - jmin : ℕ) : ℝ) / 2 + 1 := by
            have : 2 * ((jmax - jmin + 1) / 2) ≤ jmax - jmin + 1 := Nat.mul_div_le _ 2
            have hR : (2 : ℝ) * (((jmax - jmin + 1) / 2 : ℕ) : ℝ) ≤ ((jmax - jmin + 1 : ℕ) : ℝ) := by
              exact_mod_cast this
            push_cast at hR; linarith
          linarith
        have hMS : (M : ℝ) / S0 ≤ 4 / 5 := (div_le_iff₀ hS0_pos).mpr hM_le_S0
        have hterm : (M : ℝ) * ((k + cnt (w.take jmax) + 1 : ℕ) : ℝ) / S0 -
            (M : ℝ) * ((k + cnt (w.take jmin) + 1 : ℕ) : ℝ) / S0 ≤
            (4 / 5 : ℝ) * (((jmax - jmin : ℕ) : ℝ) / 2 + 1) := by
          have heq : (M : ℝ) * ((k + cnt (w.take jmax) + 1 : ℕ) : ℝ) / S0 -
              (M : ℝ) * ((k + cnt (w.take jmin) + 1 : ℕ) : ℝ) / S0 =
              ((M : ℝ) / S0) * ((cnt (w.take jmax) : ℝ) - (cnt (w.take jmin) : ℝ)) := by
            push_cast; ring
          rw [heq]
          have hnn : 0 ≤ (cnt (w.take jmax) : ℝ) - (cnt (w.take jmin) : ℝ) := by
            have : cnt (w.take jmin) ≤ cnt (w.take jmax) := cnt_take_mono w hle_j
            have hR : (cnt (w.take jmin) : ℝ) ≤ (cnt (w.take jmax) : ℝ) := by exact_mod_cast this
            linarith
          exact mul_le_mul hMS hcnt_R hnn (by norm_num)
        have ha1 := (abs_le.mp hmin_approx).1
        have ha2 := (abs_le.mp hmax_approx).2
        linarith
      have hgap : ((jmax - jmin : ℕ) : ℝ) ≤ 4 * T + 9 := by
        have h1 := (abs_le.mp hmin_T).1
        have h2 := (abs_le.mp hmax_T).2
        have hsub : ((jmax - jmin : ℕ) : ℝ) = (jmax : ℝ) - (jmin : ℝ) := Nat.cast_sub hle_j
        have hT0 : 0 ≤ T := by dsimp only [T]; positivity
        linarith
      have hcard_R : (central.card : ℝ) ≤ ((jmax - jmin : ℕ) : ℝ) + 1 := by exact_mod_cast hcard_le
      dsimp only [T] at hgap
      linarith
    -- Per-j bound on (A w j)^2 / (B w)^2 in central regime
    have hM_ge_k : k ≤ M := by
      have hR : (k : ℝ) ≤ (M : ℝ) := by
        dsimp only [M]
        rw [Nat.cast_sub (by omega : 1 ≤ w.length)]
        push_cast; linarith
      exact_mod_cast hR
    have hA_central : ∀ j ∈ central,
        (A w j) ^ 2 ≤ (10 : ℝ) ^ 11 * (Real.log (k : ℝ)) ^ 2 / (k : ℝ) ^ 2 * (B w : ℝ) ^ 2 := by
      intro j hj
      have hj_lt : j < w.length := mem_range.mp (mem_filter.mp hj).1
      have hj_T : |(j : ℝ) - mu j| ≤ T := (mem_filter.mp hj).2
      by_cases htrue : w[j]? = some true
      · let a := k + cnt (w.take j)
        let b := k + cnt (w.drop (j + 1))
        let m1 := j
        let m2 := w.length - 1 - j
        have hm1_len : (w.take j).length = m1 := List.length_take_of_le (by omega)
        have hm2_len : (w.drop (j + 1)).length = m2 := by
          rw [List.length_drop]; dsimp only [m2]; omega
        have hA_eq : A w j =
            (((m2 : ℝ) * ((a : ℝ) + 1) - (m1 : ℝ) * ((b : ℝ) + 1)) /
              (((a : ℝ) + 1) * ((b : ℝ) + 1))) *
              (((a + 1).choose m1 : ℝ) * ((b + 1).choose m2 : ℝ)) := by
          dsimp only [A, P, F']
          simp only [htrue, ↓reduceIte, hm1_len, hm2_len]
          have hsub1 : 2 * k + 1 - k = k + 1 := by omega
          have hsub2 : 2 * k + 1 - (k + 1) = k := by omega
          rw [hsub1, hsub2]
          have hadd1 : k + 1 + cnt (w.drop (j + 1)) = b + 1 := by dsimp only [b]; omega
          have hadd2 : k + 1 + cnt (w.take j) = a + 1 := by dsimp only [a]; omega
          dsimp only [cnt] at hadd1 hadd2 ⊢
          rw [hadd1, hadd2]
          exact A_exact_identity a b m1 m2
        -- Numerator: |m2*(a+1) - m1*(b+1)| = ((a+1)+(b+1)) * |j - mu j| ≤ 3*k * T
        have hnum_eq : (m2 : ℝ) * ((a : ℝ) + 1) - (m1 : ℝ) * ((b : ℝ) + 1) =
            -(((a : ℝ) + 1) + ((b : ℝ) + 1)) * ((j : ℝ) - mu j) := by
          have hm12 : (m2 : ℝ) = (M : ℝ) - (j : ℝ) := by
            dsimp only [m2, M]; rw [Nat.cast_sub (by omega)]
          have hab_pos : (0 : ℝ) < ((a : ℝ) + 1) + ((b : ℝ) + 1) := by positivity
          dsimp only [mu, m1]
          have hcast_a : ((k + cnt (w.take j) + 1 : ℕ) : ℝ) = (a : ℝ) + 1 := by
            dsimp only [a]; push_cast; ring
          have hcast_b : ((k + cnt (w.drop (j + 1)) + 1 : ℕ) : ℝ) = (b : ℝ) + 1 := by
            dsimp only [b]; push_cast; ring
          rw [hcast_a, hcast_b, hm12]
          field_simp [hab_pos.ne']
          ring
        have hpeak := hypergeom_peak_bound k (a + 1) (b + 1) M j (by omega)
          (by dsimp only [a]; omega)
          (by have : cnt (w.take j) ≤ cnt w := by have := cnt_take_add_drop_le w j; omega
              have h1 : (cnt w : ℝ) ≤ (68 : ℝ) / 100 * (k : ℝ) := hcnt_hi
              have h2 : (a + 1 : ℝ) ≤ 2 * (k : ℝ) := by dsimp only [a]; push_cast; linarith [show (cnt (w.take j) : ℝ) ≤ cnt w by exact_mod_cast this]
              exact_mod_cast h2)
          (by dsimp only [b]; omega)
          (by have : cnt (w.drop (j + 1)) ≤ cnt w := by have := cnt_take_add_drop_le w j; omega
              have h2 : (b + 1 : ℝ) ≤ 2 * (k : ℝ) := by dsimp only [b]; push_cast; linarith [show (cnt (w.drop (j + 1)) : ℝ) ≤ cnt w by exact_mod_cast this]
              exact_mod_cast h2)
          (by exact hM_ge_k)
          (by have hge := cnt_take_add_drop_ge w j
              have hR : (M : ℝ) + (k : ℝ) / 4 ≤ ((a + 1) + (b + 1) : ℕ) := by
                dsimp only [M, a, b]
                have hMle : (w.length - 1 : ℕ) ≤ w.length := Nat.sub_le _ _
                have hgeR : (cnt w : ℝ) ≤ (cnt (w.take j) : ℝ) + (cnt (w.drop (j + 1)) : ℝ) + 2 := by
                  exact_mod_cast hge
                push_cast; linarith [show ((w.length - 1 : ℕ) : ℝ) ≤ w.length by exact_mod_cast hMle]
              have hdiv : ((k / 4 : ℕ) : ℝ) ≤ (k : ℝ) / 4 := by
                have : 4 * (k / 4) ≤ k := Nat.mul_div_le k 4
                have : (4 : ℝ) * ((k / 4 : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast this
                linarith
              exact_mod_cast (show (M : ℝ) + ((k / 4 : ℕ) : ℝ) ≤ ((a + 1) + (b + 1) : ℕ) by linarith))
          (by dsimp only [M]; omega)
        have hM_bw : (((a + 1) + (b + 1)).choose M : ℝ) ≤ 30 * (B w : ℝ) := by
          exact_mod_cast hM_eq j (mem_range.mpr hj_lt)
        have hab_le : ((a : ℝ) + 1) + ((b : ℝ) + 1) ≤ 3 * (k : ℝ) := by
          have : cnt (w.take j) + cnt (w.drop (j + 1)) ≤ cnt w := cnt_take_add_drop_le w j
          have hR : (cnt (w.take j) : ℝ) + (cnt (w.drop (j + 1)) : ℝ) ≤ cnt w := by exact_mod_cast this
          dsimp only [a, b]; push_cast; linarith
        have hden_ge : (k : ℝ) ^ 2 ≤ ((a : ℝ) + 1) * ((b : ℝ) + 1) := by
          have ha : (k : ℝ) ≤ (a : ℝ) + 1 := by dsimp only [a]; push_cast; linarith
          have hb : (k : ℝ) ≤ (b : ℝ) + 1 := by dsimp only [b]; push_cast; linarith
          nlinarith
        have hA_abs : |A w j| ≤ 300000 * Real.log (k : ℝ) / (k : ℝ) * (B w : ℝ) := by
          rw [hA_eq, hnum_eq, abs_mul, abs_div, abs_mul, abs_neg]
          have h1 : |((a : ℝ) + 1) + ((b : ℝ) + 1)| * |(j : ℝ) - mu j| ≤ 3 * (k : ℝ) * T := by
            rw [abs_of_pos (by positivity)]
            exact mul_le_mul hab_le hj_T (abs_nonneg _) (by positivity)
          have h2 : |((a : ℝ) + 1) * ((b : ℝ) + 1)| = ((a : ℝ) + 1) * ((b : ℝ) + 1) :=
            abs_of_pos (by positivity)
          have h3 : |((a + 1).choose m1 : ℝ) * ((b + 1).choose m2 : ℝ)| ≤
              (2400 / Real.sqrt (k : ℝ)) * (B w : ℝ) := by
            rw [abs_of_nonneg (by positivity)]
            calc ((a + 1).choose m1 : ℝ) * ((b + 1).choose m2 : ℝ)
                ≤ (80 / Real.sqrt (k : ℝ)) * (((a + 1) + (b + 1)).choose M : ℝ) := hpeak
              _ ≤ (80 / Real.sqrt (k : ℝ)) * (30 * (B w : ℝ)) :=
                  mul_le_mul_of_nonneg_left hM_bw (by positivity)
              _ = (2400 / Real.sqrt (k : ℝ)) * (B w : ℝ) := by ring
          rw [h2]
          have hfrac : |((a : ℝ) + 1) + ((b : ℝ) + 1)| * |(j : ℝ) - mu j| /
              (((a : ℝ) + 1) * ((b : ℝ) + 1)) ≤ 3 * (k : ℝ) * T / (k : ℝ) ^ 2 := by
            calc |((a : ℝ) + 1) + ((b : ℝ) + 1)| * |(j : ℝ) - mu j| /
                  (((a : ℝ) + 1) * ((b : ℝ) + 1))
                ≤ 3 * (k : ℝ) * T / (((a : ℝ) + 1) * ((b : ℝ) + 1)) :=
                  div_le_div_of_nonneg_right h1 (by positivity)
              _ ≤ 3 * (k : ℝ) * T / (k : ℝ) ^ 2 :=
                  div_le_div_of_nonneg_left (by dsimp only [T]; positivity) (by positivity) hden_ge
          calc (|((a : ℝ) + 1) + ((b : ℝ) + 1)| * |(j : ℝ) - mu j| /
                (((a : ℝ) + 1) * ((b : ℝ) + 1))) *
                |((a + 1).choose m1 : ℝ) * ((b + 1).choose m2 : ℝ)|
              ≤ (3 * (k : ℝ) * T / (k : ℝ) ^ 2) * ((2400 / Real.sqrt (k : ℝ)) * (B w : ℝ)) :=
                mul_le_mul hfrac h3 (abs_nonneg _) (by dsimp only [T]; positivity)
            _ = 288000 * Real.log (k : ℝ) / (k : ℝ) * (B w : ℝ) := by
                dsimp only [T]
                field_simp [hk_pos.ne', hsq_k_pos.ne']
                ring
            _ ≤ 300000 * Real.log (k : ℝ) / (k : ℝ) * (B w : ℝ) := by
                have hnn : 0 ≤ Real.log (k : ℝ) / (k : ℝ) * (B w : ℝ) := by positivity
                calc 288000 * Real.log (k : ℝ) / (k : ℝ) * (B w : ℝ)
                    = 288000 * (Real.log (k : ℝ) / (k : ℝ) * (B w : ℝ)) := by ring
                  _ ≤ 300000 * (Real.log (k : ℝ) / (k : ℝ) * (B w : ℝ)) :=
                      mul_le_mul_of_nonneg_right (by norm_num) hnn
                  _ = 300000 * Real.log (k : ℝ) / (k : ℝ) * (B w : ℝ) := by ring
        have hsq : (A w j) ^ 2 ≤ (300000 * Real.log (k : ℝ) / (k : ℝ) * (B w : ℝ)) ^ 2 := by
          rw [← sq_abs (A w j)]
          exact pow_le_pow_left₀ (abs_nonneg _) hA_abs 2
        calc (A w j) ^ 2 ≤ (300000 * Real.log (k : ℝ) / (k : ℝ) * (B w : ℝ)) ^ 2 := hsq
          _ = (9 * (10 : ℝ) ^ 10) * ((Real.log (k : ℝ)) ^ 2 / (k : ℝ) ^ 2 * (B w : ℝ) ^ 2) := by ring
          _ ≤ (10 : ℝ) ^ 11 * ((Real.log (k : ℝ)) ^ 2 / (k : ℝ) ^ 2 * (B w : ℝ) ^ 2) :=
              mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
          _ = (10 : ℝ) ^ 11 * (Real.log (k : ℝ)) ^ 2 / (k : ℝ) ^ 2 * (B w : ℝ) ^ 2 := by ring
      · have hA0 : A w j = 0 := by dsimp only [A, P]; simp [htrue]
        rw [hA0, zero_pow (by norm_num : 2 ≠ 0)]; positivity
    -- Per-j bound on (A w j)^2 in tail regime
    have hA_tail : ∀ j ∈ tail,
        (A w j) ^ 2 ≤ (10 : ℝ) ^ 6 / (k : ℝ) ^ 3 * (B w : ℝ) ^ 2 := by
      intro j hj
      have hj_lt : j < w.length := mem_range.mp (mem_filter.mp hj).1
      have hj_gt : T < |(j : ℝ) - mu j| := lt_of_not_ge (mem_filter.mp hj).2
      by_cases htrue : w[j]? = some true
      · let a := k + cnt (w.take j)
        let b := k + cnt (w.drop (j + 1))
        let m1 := j
        let m2 := w.length - 1 - j
        have hm1_len : (w.take j).length = m1 := List.length_take_of_le (by omega)
        have hm2_len : (w.drop (j + 1)).length = m2 := by
          rw [List.length_drop]; dsimp only [m2]; omega
        have hA_eq : A w j =
            (((m2 : ℝ) * ((a : ℝ) + 1) - (m1 : ℝ) * ((b : ℝ) + 1)) /
              (((a : ℝ) + 1) * ((b : ℝ) + 1))) *
              (((a + 1).choose m1 : ℝ) * ((b + 1).choose m2 : ℝ)) := by
          dsimp only [A, P, F']
          simp only [htrue, ↓reduceIte, hm1_len, hm2_len]
          have hsub1 : 2 * k + 1 - k = k + 1 := by omega
          have hsub2 : 2 * k + 1 - (k + 1) = k := by omega
          rw [hsub1, hsub2]
          have hadd1 : k + 1 + cnt (w.drop (j + 1)) = b + 1 := by dsimp only [b]; omega
          have hadd2 : k + 1 + cnt (w.take j) = a + 1 := by dsimp only [a]; omega
          dsimp only [cnt] at hadd1 hadd2 ⊢
          rw [hadd1, hadd2]
          exact A_exact_identity a b m1 m2
        -- Coefficient |m2*(a+1) - m1*(b+1)| / ((a+1)*(b+1)) ≤ 10
        have hcoef_le : |((m2 : ℝ) * ((a : ℝ) + 1) - (m1 : ℝ) * ((b : ℝ) + 1)) /
            (((a : ℝ) + 1) * ((b : ℝ) + 1))| ≤ 10 := by
          rw [abs_div, abs_of_pos (show 0 < ((a : ℝ) + 1) * ((b : ℝ) + 1) by positivity)]
          rw [div_le_iff₀ (show 0 < ((a : ℝ) + 1) * ((b : ℝ) + 1) by positivity)]
          have hm1_le : (m1 : ℝ) ≤ 3 * (k : ℝ) := by
            have : m1 ≤ w.length := by omega
            have : (m1 : ℝ) ≤ w.length := by exact_mod_cast this
            linarith
          have hm2_le : (m2 : ℝ) ≤ 3 * (k : ℝ) := by
            have : m2 ≤ w.length := by omega
            have : (m2 : ℝ) ≤ w.length := by exact_mod_cast this
            linarith
          have ha_le : (a : ℝ) + 1 ≤ 2 * (k : ℝ) := by
            have : cnt (w.take j) ≤ cnt w := by have := cnt_take_add_drop_le w j; omega
            have hR : (cnt (w.take j) : ℝ) ≤ cnt w := by exact_mod_cast this
            dsimp only [a]; push_cast; linarith
          have hb_le : (b : ℝ) + 1 ≤ 2 * (k : ℝ) := by
            have : cnt (w.drop (j + 1)) ≤ cnt w := by have := cnt_take_add_drop_le w j; omega
            have hR : (cnt (w.drop (j + 1)) : ℝ) ≤ cnt w := by exact_mod_cast this
            dsimp only [b]; push_cast; linarith
          have ha_ge : (k : ℝ) ≤ (a : ℝ) + 1 := by dsimp only [a]; push_cast; linarith
          have hb_ge : (k : ℝ) ≤ (b : ℝ) + 1 := by dsimp only [b]; push_cast; linarith
          have h1 : (m2 : ℝ) * ((a : ℝ) + 1) ≤ 6 * (k : ℝ) ^ 2 := by nlinarith
          have h2 : (m1 : ℝ) * ((b : ℝ) + 1) ≤ 6 * (k : ℝ) ^ 2 := by nlinarith
          have h3 : 10 * (((a : ℝ) + 1) * ((b : ℝ) + 1)) ≥ 10 * (k : ℝ) ^ 2 := by nlinarith
          rw [abs_le]
          constructor <;> nlinarith
        -- Apply hypergeom_tail_bound with d = ⌊T⌋₊
        let d := ⌊T⌋₊
        have hd_le_T : (d : ℝ) ≤ T := Nat.floor_le (by dsimp only [T]; positivity)
        have hd_ge : 39 * Real.sqrt (k : ℝ) * Real.log (k : ℝ) ≤ (d : ℝ) := by
          have hlt : T - 1 < (d : ℝ) := by linarith [Nat.lt_floor_add_one T]
          have hsq : 100 ≤ Real.sqrt (k : ℝ) := by
            rw [Real.le_sqrt (by norm_num) (by positivity)]; linarith
          dsimp only [T] at hlt
          nlinarith
        have htail := hypergeom_tail_bound k (a + 1) (b + 1) M j d (by omega)
          (by dsimp only [a]; omega)
          (by have : cnt (w.take j) ≤ cnt w := by have := cnt_take_add_drop_le w j; omega
              have h2 : (a + 1 : ℝ) ≤ 2 * (k : ℝ) := by dsimp only [a]; push_cast; linarith [show (cnt (w.take j) : ℝ) ≤ cnt w by exact_mod_cast this]
              exact_mod_cast h2)
          (by dsimp only [b]; omega)
          (by have : cnt (w.drop (j + 1)) ≤ cnt w := by have := cnt_take_add_drop_le w j; omega
              have h2 : (b + 1 : ℝ) ≤ 2 * (k : ℝ) := by dsimp only [b]; push_cast; linarith [show (cnt (w.drop (j + 1)) : ℝ) ≤ cnt w by exact_mod_cast this]
              exact_mod_cast h2)
          (by exact hM_ge_k)
          (by have hge := cnt_take_add_drop_ge w j
              have hR : (M : ℝ) ≤ ((a + 1) + (b + 1) : ℕ) := by
                dsimp only [M, a, b]
                have hMle : (w.length - 1 : ℕ) ≤ w.length := Nat.sub_le _ _
                have hgeR : (cnt w : ℝ) ≤ (cnt (w.take j) : ℝ) + (cnt (w.drop (j + 1)) : ℝ) + 2 := by
                  exact_mod_cast hge
                push_cast; linarith [show ((w.length - 1 : ℕ) : ℝ) ≤ w.length by exact_mod_cast hMle]
              exact_mod_cast hR)
          (by dsimp only [M]; omega)
          (by exact hd_le_T.trans hj_gt.le)
        have hM_bw : (((a + 1) + (b + 1)).choose M : ℝ) ≤ 30 * (B w : ℝ) := by
          exact_mod_cast hM_eq j (mem_range.mpr hj_lt)
        -- exp(-d^2 / (128*k)) ≤ exp(-2 * log k) = k^(-2)
        have hexp_le : Real.exp (-((d : ℝ) ^ 2) / (128 * (k : ℝ))) ≤ (k : ℝ) ^ (-2 : ℤ) := by
          have hd2 : 1000 * (k : ℝ) * (Real.log (k : ℝ)) ^ 2 ≤ (d : ℝ) ^ 2 := by
            have h1 : (39 * Real.sqrt (k : ℝ) * Real.log (k : ℝ)) ^ 2 ≤ (d : ℝ) ^ 2 :=
              pow_le_pow_left₀ (by positivity) hd_ge 2
            have h2 : (39 * Real.sqrt (k : ℝ) * Real.log (k : ℝ)) ^ 2 =
                1521 * (k : ℝ) * (Real.log (k : ℝ)) ^ 2 := by
              rw [mul_pow, mul_pow, Real.sq_sqrt hk_pos.le]; ring
            nlinarith
          have hlog2 : 2 * Real.log (k : ℝ) ≤ (d : ℝ) ^ 2 / (128 * (k : ℝ)) := by
            rw [le_div_iff₀ (by positivity)]
            nlinarith
          have hpow : (k : ℝ) ^ (-2 : ℤ) = Real.exp (-(2 * Real.log (k : ℝ))) := by
            rw [zpow_neg, zpow_two, Real.exp_neg,
              show (2 : ℝ) * Real.log (k : ℝ) = ((2 : ℕ) : ℝ) * Real.log (k : ℝ) by norm_num,
              Real.exp_nat_mul, Real.exp_log hk_pos]
            ring
          rw [hpow]
          apply Real.exp_le_exp.mpr
          rw [neg_div]
          linarith
        have hA_abs : |A w j| ≤ 300 / (k : ℝ) ^ 2 * (B w : ℝ) := by
          rw [hA_eq, abs_mul, abs_of_nonneg (show 0 ≤ ((a + 1).choose m1 : ℝ) * ((b + 1).choose m2 : ℝ) by positivity)]
          calc |((m2 : ℝ) * ((a : ℝ) + 1) - (m1 : ℝ) * ((b : ℝ) + 1)) /
                (((a : ℝ) + 1) * ((b : ℝ) + 1))| *
                (((a + 1).choose m1 : ℝ) * ((b + 1).choose m2 : ℝ))
              ≤ 10 * (Real.exp (-((d : ℝ) ^ 2) / (128 * (k : ℝ))) * (((a + 1) + (b + 1)).choose M : ℝ)) :=
                mul_le_mul hcoef_le htail (by positivity) (by norm_num)
            _ ≤ 10 * ((k : ℝ) ^ (-2 : ℤ) * (30 * (B w : ℝ))) := by
                apply mul_le_mul_of_nonneg_left _ (by norm_num)
                exact mul_le_mul hexp_le hM_bw (by positivity) (by positivity)
            _ = 300 / (k : ℝ) ^ 2 * (B w : ℝ) := by
                rw [zpow_neg, zpow_two]; ring
        have hsq : (A w j) ^ 2 ≤ (300 / (k : ℝ) ^ 2 * (B w : ℝ)) ^ 2 := by
          rw [← sq_abs (A w j)]
          exact pow_le_pow_left₀ (abs_nonneg _) hA_abs 2
        calc (A w j) ^ 2 ≤ (300 / (k : ℝ) ^ 2 * (B w : ℝ)) ^ 2 := hsq
          _ = 90000 / (k : ℝ) ^ 4 * (B w : ℝ) ^ 2 := by ring
          _ ≤ (10 : ℝ) ^ 6 / (k : ℝ) ^ 3 * (B w : ℝ) ^ 2 := by
              apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
              rw [div_le_div_iff₀ (by positivity) (by positivity)]
              have h4 : (k : ℝ) ^ 4 = (k : ℝ) * (k : ℝ) ^ 3 := by ring
              rw [h4, ← mul_assoc]
              exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      · have hA0 : A w j = 0 := by dsimp only [A, P]; simp [htrue]
        rw [hA0, zero_pow (by norm_num : 2 ≠ 0)]; positivity
    -- Combine central and tail sums
    have hsum_A2 : ∑ j ∈ range w.length, (A w j) ^ 2 ≤
        (10 : ℝ) ^ 14 * (Real.log (k : ℝ)) ^ 3 / ((k : ℝ) * Real.sqrt (k : ℝ)) * (B w : ℝ) ^ 2 := by
      rw [← sum_filter_add_sum_filter_not (range w.length) (fun j : ℕ => |(j : ℝ) - mu j| ≤ T)]
      have h1 : ∑ j ∈ central, (A w j) ^ 2 ≤
          (170 * Real.sqrt (k : ℝ) * Real.log (k : ℝ)) *
            ((10 : ℝ) ^ 11 * (Real.log (k : ℝ)) ^ 2 / (k : ℝ) ^ 2 * (B w : ℝ) ^ 2) := by
        calc ∑ j ∈ central, (A w j) ^ 2
            ≤ ∑ _j ∈ central, ((10 : ℝ) ^ 11 * (Real.log (k : ℝ)) ^ 2 / (k : ℝ) ^ 2 * (B w : ℝ) ^ 2) :=
              sum_le_sum hA_central
          _ = (central.card : ℝ) * ((10 : ℝ) ^ 11 * (Real.log (k : ℝ)) ^ 2 / (k : ℝ) ^ 2 * (B w : ℝ) ^ 2) := by
              simp
          _ ≤ (170 * Real.sqrt (k : ℝ) * Real.log (k : ℝ)) *
              ((10 : ℝ) ^ 11 * (Real.log (k : ℝ)) ^ 2 / (k : ℝ) ^ 2 * (B w : ℝ) ^ 2) := by
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              have hsq : 10 ≤ Real.sqrt (k : ℝ) := by
                rw [Real.le_sqrt (by norm_num) (by positivity)]; linarith
              nlinarith
      have h1' : (170 * Real.sqrt (k : ℝ) * Real.log (k : ℝ)) *
            ((10 : ℝ) ^ 11 * (Real.log (k : ℝ)) ^ 2 / (k : ℝ) ^ 2 * (B w : ℝ) ^ 2) =
          170 * (10 : ℝ) ^ 11 * (Real.log (k : ℝ)) ^ 3 / ((k : ℝ) * Real.sqrt (k : ℝ)) * (B w : ℝ) ^ 2 := by
        have hsq2 : Real.sqrt (k : ℝ) * Real.sqrt (k : ℝ) = (k : ℝ) := Real.mul_self_sqrt hk_pos.le
        field_simp [hk_pos.ne', hsq_k_pos.ne']
        nlinarith [hsq2]
      have h2 : ∑ j ∈ tail, (A w j) ^ 2 ≤
          (3 * (k : ℝ)) * ((10 : ℝ) ^ 6 / (k : ℝ) ^ 3 * (B w : ℝ) ^ 2) := by
        calc ∑ j ∈ tail, (A w j) ^ 2
            ≤ ∑ _j ∈ tail, ((10 : ℝ) ^ 6 / (k : ℝ) ^ 3 * (B w : ℝ) ^ 2) := sum_le_sum hA_tail
          _ = (tail.card : ℝ) * ((10 : ℝ) ^ 6 / (k : ℝ) ^ 3 * (B w : ℝ) ^ 2) := by simp
          _ ≤ (3 * (k : ℝ)) * ((10 : ℝ) ^ 6 / (k : ℝ) ^ 3 * (B w : ℝ) ^ 2) := by
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              have hcard : tail.card ≤ w.length := (card_filter_le _ _).trans_eq (card_range _)
              have hcardR : (tail.card : ℝ) ≤ (w.length : ℝ) := by exact_mod_cast hcard
              linarith
      have h2' : (3 * (k : ℝ)) * ((10 : ℝ) ^ 6 / (k : ℝ) ^ 3 * (B w : ℝ) ^ 2) ≤
          (10 : ℝ) ^ 11 * (Real.log (k : ℝ)) ^ 3 / ((k : ℝ) * Real.sqrt (k : ℝ)) * (B w : ℝ) ^ 2 := by
        have hsq_le : Real.sqrt (k : ℝ) ≤ (k : ℝ) := by
          rw [Real.sqrt_le_left hk_pos.le]; nlinarith
        have hlog3 : (1 : ℝ) ≤ (Real.log (k : ℝ)) ^ 3 := by nlinarith
        have hstep : 3 * (k : ℝ) * ((10 : ℝ) ^ 6 / (k : ℝ) ^ 3) ≤
            (10 : ℝ) ^ 11 * (Real.log (k : ℝ)) ^ 3 / ((k : ℝ) * Real.sqrt (k : ℝ)) := by
          rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
          have h1 : 3 * (k : ℝ) * (10 : ℝ) ^ 6 * ((k : ℝ) * Real.sqrt (k : ℝ)) ≤
              3 * (10 : ℝ) ^ 6 * (k : ℝ) ^ 3 := by nlinarith
          have h2 : 3 * (10 : ℝ) ^ 6 * (k : ℝ) ^ 3 ≤ (10 : ℝ) ^ 11 * (Real.log (k : ℝ)) ^ 3 * (k : ℝ) ^ 3 :=
            mul_le_mul_of_nonneg_right (by linarith) (by positivity)
          linarith
        calc (3 * (k : ℝ)) * ((10 : ℝ) ^ 6 / (k : ℝ) ^ 3 * (B w : ℝ) ^ 2)
            = (3 * (k : ℝ) * ((10 : ℝ) ^ 6 / (k : ℝ) ^ 3)) * (B w : ℝ) ^ 2 := by ring
          _ ≤ ((10 : ℝ) ^ 11 * (Real.log (k : ℝ)) ^ 3 / ((k : ℝ) * Real.sqrt (k : ℝ))) * (B w : ℝ) ^ 2 :=
              mul_le_mul_of_nonneg_right hstep (sq_nonneg _)
      have hsum_le : 170 * (10 : ℝ) ^ 11 + (10 : ℝ) ^ 11 ≤ (10 : ℝ) ^ 14 := by norm_num
      have hpos_term : 0 ≤ (Real.log (k : ℝ)) ^ 3 / ((k : ℝ) * Real.sqrt (k : ℝ)) * (B w : ℝ) ^ 2 := by
        positivity
      calc (∑ j ∈ central, (A w j) ^ 2) + (∑ j ∈ tail, (A w j) ^ 2)
          ≤ 170 * (10 : ℝ) ^ 11 * (Real.log (k : ℝ)) ^ 3 / ((k : ℝ) * Real.sqrt (k : ℝ)) * (B w : ℝ) ^ 2 +
            (10 : ℝ) ^ 11 * (Real.log (k : ℝ)) ^ 3 / ((k : ℝ) * Real.sqrt (k : ℝ)) * (B w : ℝ) ^ 2 := by
            linarith
        _ = (170 * (10 : ℝ) ^ 11 + (10 : ℝ) ^ 11) *
            ((Real.log (k : ℝ)) ^ 3 / ((k : ℝ) * Real.sqrt (k : ℝ)) * (B w : ℝ) ^ 2) := by ring
        _ ≤ (10 : ℝ) ^ 14 * ((Real.log (k : ℝ)) ^ 3 / ((k : ℝ) * Real.sqrt (k : ℝ)) * (B w : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_right hsum_le hpos_term
        _ = (10 : ℝ) ^ 14 * (Real.log (k : ℝ)) ^ 3 / ((k : ℝ) * Real.sqrt (k : ℝ)) * (B w : ℝ) ^ 2 := by ring
    -- Compare (k * √k) vs n^(3/2) and (log k)^3 vs (log n)^7
    have hn32 : (n : ℝ) ^ (3 / 2 : ℝ) ≤ 12 * ((k : ℝ) * Real.sqrt (k : ℝ)) := by
      have hn_le : (n : ℝ) ≤ 5 * (k : ℝ) := by
        have : n ≤ 5 * k := by omega
        exact_mod_cast this
      have h1 : (n : ℝ) ^ (3 / 2 : ℝ) ≤ (5 * (k : ℝ)) ^ (3 / 2 : ℝ) :=
        Real.rpow_le_rpow hn_pos.le hn_le (by norm_num)
      have h2 : (5 * (k : ℝ)) ^ (3 / 2 : ℝ) = (5 * (k : ℝ)) * Real.sqrt (5 * (k : ℝ)) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' (by positivity) (by norm_num)]
        norm_num
      have h3 : Real.sqrt (5 * (k : ℝ)) = Real.sqrt 5 * Real.sqrt (k : ℝ) :=
        Real.sqrt_mul (by norm_num) (k : ℝ)
      have h5 : Real.sqrt 5 ≤ 12 / 5 := by
        rw [Real.sqrt_le_left (by norm_num)]; norm_num
      calc (n : ℝ) ^ (3 / 2 : ℝ) ≤ (5 * (k : ℝ)) * (Real.sqrt 5 * Real.sqrt (k : ℝ)) := by
            rw [h2, h3] at h1; exact h1
        _ ≤ (5 * (k : ℝ)) * ((12 / 5 : ℝ) * Real.sqrt (k : ℝ)) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact mul_le_mul_of_nonneg_right h5 (Real.sqrt_nonneg _)
        _ = 12 * ((k : ℝ) * Real.sqrt (k : ℝ)) := by ring
    have hlog37 : (Real.log (k : ℝ)) ^ 3 ≤ (Real.log (n : ℝ)) ^ 7 := by
      have h1 : (Real.log (k : ℝ)) ^ 3 ≤ (Real.log (n : ℝ)) ^ 3 :=
        pow_le_pow_left₀ (by linarith) hlog_n_ge_k 3
      have h2 : (1 : ℝ) ≤ (Real.log (n : ℝ)) ^ 4 := by
        have : (1 : ℝ) ≤ Real.log (n : ℝ) := by linarith
        exact one_le_pow₀ this
      calc (Real.log (k : ℝ)) ^ 3 ≤ (Real.log (n : ℝ)) ^ 3 * 1 := by linarith
        _ ≤ (Real.log (n : ℝ)) ^ 3 * (Real.log (n : ℝ)) ^ 4 :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = (Real.log (n : ℝ)) ^ 7 := by ring
    calc (∑ p ∈ ((range w.length).product (range w.length)).filter
          (fun p => p.1 ≤ p.2 + 5 ∧ p.2 ≤ p.1 + 5),
          |A w p.1 * A w p.2 / ((2 : ℝ) ^ n * (max 1 (B w) : ℕ))|)
        ≤ (11 / ((2 : ℝ) ^ n * (B w : ℝ))) * ∑ j ∈ range w.length, (A w j) ^ 2 := hnear_to_diag
      _ ≤ (11 / ((2 : ℝ) ^ n * (B w : ℝ))) *
          ((10 : ℝ) ^ 14 * (Real.log (k : ℝ)) ^ 3 / ((k : ℝ) * Real.sqrt (k : ℝ)) * (B w : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left hsum_A2 (by positivity)
      _ = ((B w : ℝ) / (2 : ℝ) ^ n) *
          (11 * (10 : ℝ) ^ 14 * (Real.log (k : ℝ)) ^ 3 / ((k : ℝ) * Real.sqrt (k : ℝ))) := by
          field_simp [h2n_pos.ne', hBwR_pos.ne']
      _ ≤ ((B w : ℝ) / (2 : ℝ) ^ n) *
          ((10 : ℝ) ^ 17 * (Real.log (n : ℝ)) ^ 7 / (n : ℝ) ^ (3 / 2 : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          calc 11 * (10 : ℝ) ^ 14 * (Real.log (k : ℝ)) ^ 3 * (n : ℝ) ^ (3 / 2 : ℝ)
              ≤ 11 * (10 : ℝ) ^ 14 * (Real.log (n : ℝ)) ^ 7 * (12 * ((k : ℝ) * Real.sqrt (k : ℝ))) := by
                apply mul_le_mul _ hn32 (by positivity) (by positivity)
                exact mul_le_mul_of_nonneg_left hlog37 (by positivity)
            _ = 132 * (10 : ℝ) ^ 14 * (Real.log (n : ℝ)) ^ 7 * ((k : ℝ) * Real.sqrt (k : ℝ)) := by ring
            _ ≤ (10 : ℝ) ^ 17 * (Real.log (n : ℝ)) ^ 7 * ((k : ℝ) * Real.sqrt (k : ℝ)) := by
                have : 0 ≤ (Real.log (n : ℝ)) ^ 7 * ((k : ℝ) * Real.sqrt (k : ℝ)) := by positivity
                nlinarith
  calc (∑ w ∈ U.filter E,
        ∑ p ∈ ((range w.length).product (range w.length)).filter
          (fun p => p.1 ≤ p.2 + 5 ∧ p.2 ≤ p.1 + 5),
          |A w p.1 * A w p.2 / ((2 : ℝ) ^ n * (max 1 (B w) : ℕ))|)
      ≤ ∑ w ∈ U.filter E, ((B w : ℝ) / (2 : ℝ) ^ n) *
          ((10 : ℝ) ^ 17 * (Real.log (n : ℝ)) ^ 7 / (n : ℝ) ^ (3 / 2 : ℝ)) :=
        sum_le_sum hpointwise
    _ = ((∑ w ∈ U.filter E, (B w : ℝ)) / (2 : ℝ) ^ n) *
          ((10 : ℝ) ^ 17 * (Real.log (n : ℝ)) ^ 7 / (n : ℝ) ^ (3 / 2 : ℝ)) := by
        rw [← sum_mul, ← sum_div]
    _ ≤ 1 * ((10 : ℝ) ^ 17 * (Real.log (n : ℝ)) ^ 7 / (n : ℝ) ^ (3 / 2 : ℝ)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        rw [div_le_one (by positivity)]
        have hsumB : ∑ w ∈ U.filter E, B w ≤ 2 ^ (2 * (2 * k + 1)) :=
          sum_F_le_pow (2 * k + 1) (U.filter E)
        have hpow_le : 2 ^ (2 * (2 * k + 1)) ≤ 2 ^ n :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
        exact_mod_cast hsumB.trans hpow_le
    _ = (10 : ℝ) ^ 17 * (Real.log (n : ℝ)) ^ 7 / (n : ℝ) ^ (3 / 2 : ℝ) := one_mul _

end Green92ChaseH1
