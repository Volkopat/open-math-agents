import OMAStatements.S_oeis_a033282

namespace OMA.S_oeis_a033282_proof

open OMA.S_oeis_a033282

private lemma card_erase_lt {s : Multiset ℕ} {x : ℕ} (hx : x ∈ s) :
    (s.erase x).card < s.card := by
  have h := congrArg Multiset.card (Multiset.cons_erase hx)
  rw [Multiset.card_cons] at h
  omega

private lemma sum_count_eq_card (s : Multiset ℕ) :
    ∑ x ∈ s.toFinset, s.count x = s.card := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    by_cases ha : a ∈ s
    · have hfin : (a ::ₘ s).toFinset = s.toFinset := by
        ext y
        simp only [Multiset.mem_toFinset, Multiset.mem_cons]
        exact ⟨fun h => h.elim (fun hy => hy ▸ ha) id, Or.inr⟩
      have ham : a ∈ s.toFinset := Multiset.mem_toFinset.mpr ha
      rw [hfin, ← Finset.add_sum_erase _ _ ham]
      have her :
          ∑ y ∈ s.toFinset.erase a, (a ::ₘ s).count y = ∑ y ∈ s.toFinset.erase a, s.count y := by
        refine Finset.sum_congr rfl fun y hy => ?_
        exact Multiset.count_cons_of_ne (Finset.mem_erase.mp hy).1 s
      rw [her, Multiset.count_cons_self, Multiset.card_cons]
      have hsplit := Finset.add_sum_erase s.toFinset (fun y => s.count y) ham
      omega
    · have ham : a ∉ s.toFinset := fun h => ha (Multiset.mem_toFinset.mp h)
      rw [Multiset.toFinset_cons, Finset.sum_insert ham]
      have her : ∑ y ∈ s.toFinset, (a ::ₘ s).count y = ∑ y ∈ s.toFinset, s.count y := by
        refine Finset.sum_congr rfl fun y hy => ?_
        have hne : y ≠ a := fun h => ha (h ▸ Multiset.mem_toFinset.mp hy)
        exact Multiset.count_cons_of_ne hne s
      rw [her, ih, Multiset.count_cons_self, Multiset.count_eq_zero.mpr ha, Multiset.card_cons]
      omega

private def multFact (s : Multiset ℕ) : ℕ :=
  ∏ y ∈ s.toFinset, (s.count y).factorial

private lemma multFact_ne_zero (s : Multiset ℕ) : multFact s ≠ 0 := by
  unfold multFact
  exact Finset.prod_ne_zero_iff.mpr fun y _ => Nat.factorial_ne_zero _

private lemma multFact_eq_count_mul_erase (s : Multiset ℕ) {x : ℕ} (hx : x ∈ s) :
    multFact s = s.count x * multFact (s.erase x) := by
  have hsub : (s.erase x).toFinset ⊆ s.toFinset := fun y hy =>
    Multiset.mem_toFinset.mpr (Multiset.mem_of_mem_erase (Multiset.mem_toFinset.mp hy))
  have hprod_er : multFact (s.erase x) = ∏ y ∈ s.toFinset, ((s.erase x).count y).factorial := by
    unfold multFact
    refine Finset.prod_subset hsub fun y _ hy => ?_
    have hnot : y ∉ s.erase x := fun h => hy (Multiset.mem_toFinset.mpr h)
    rw [Multiset.count_eq_zero.mpr hnot, Nat.factorial_zero]
  have hxm : x ∈ s.toFinset := Multiset.mem_toFinset.mpr hx
  have hs_split :
      multFact s = (s.count x).factorial * ∏ y ∈ s.toFinset.erase x, (s.count y).factorial := by
    unfold multFact
    exact (Finset.mul_prod_erase s.toFinset (fun y => (s.count y).factorial) hxm).symm
  have her_split :
      multFact (s.erase x) =
        ((s.erase x).count x).factorial *
          ∏ y ∈ s.toFinset.erase x, ((s.erase x).count y).factorial := by
    rw [hprod_er]
    exact (Finset.mul_prod_erase s.toFinset (fun y => ((s.erase x).count y).factorial) hxm).symm
  have hrest :
      (∏ y ∈ s.toFinset.erase x, ((s.erase x).count y).factorial) =
        ∏ y ∈ s.toFinset.erase x, (s.count y).factorial := by
    refine Finset.prod_congr rfl fun y hy => ?_
    rw [Multiset.count_erase_of_ne (Finset.mem_erase.mp hy).1]
  have hcnt : s.count x = (s.erase x).count x + 1 := by
    have h := congrArg (Multiset.count x) (Multiset.cons_erase hx)
    rw [Multiset.count_cons_self] at h
    exact h.symm
  rw [hs_split, her_split, hrest, hcnt, Nat.factorial_succ]
  ring

private def permsOf (s : Multiset ℕ) : Finset (List ℕ) :=
  if s = 0 then {[]}
  else s.toFinset.attach.biUnion fun x => (permsOf (s.erase x.1)).image (x.1 :: ·)
termination_by s.card
decreasing_by exact card_erase_lt (Multiset.mem_toFinset.mp x.2)

private lemma permsOf_zero : permsOf 0 = {[]} := by
  rw [permsOf]
  simp

private lemma permsOf_ne_zero {s : Multiset ℕ} (hs : s ≠ 0) :
    permsOf s = s.toFinset.biUnion fun x => (permsOf (s.erase x)).image (x :: ·) := by
  rw [permsOf]
  split_ifs with h
  · exact absurd h hs
  · ext l
    simp only [Finset.mem_biUnion, Finset.mem_attach, true_and, Subtype.exists, exists_prop]

private lemma mem_permsOf (s : Multiset ℕ) (l : List ℕ) :
    l ∈ permsOf s ↔ (l : Multiset ℕ) = s := by
  induction hn : s.card using Nat.strong_induction_on generalizing s l with
  | h m ih =>
    by_cases hs : s = 0
    · subst hs
      rw [permsOf_zero]
      simp
    · rw [permsOf_ne_zero hs]
      simp only [Finset.mem_biUnion, Multiset.mem_toFinset, Finset.mem_image]
      constructor
      · rintro ⟨x, hx, t, ht, rfl⟩
        have hlt : (s.erase x).card < m := hn ▸ card_erase_lt hx
        have hteq : (t : Multiset ℕ) = s.erase x := (ih _ hlt (s.erase x) t rfl).mp ht
        change x ::ₘ (t : Multiset ℕ) = s
        rw [hteq, Multiset.cons_erase hx]
      · intro h
        cases l with
        | nil =>
          simp only [Multiset.coe_nil] at h
          exact absurd h.symm hs
        | cons x t =>
          have hxt : x ::ₘ (t : Multiset ℕ) = s := h
          have hx : x ∈ s := hxt ▸ Multiset.mem_cons_self x _
          have ht_eq : (t : Multiset ℕ) = s.erase x := by
            rw [← hxt, Multiset.erase_cons_head]
          have hlt : (s.erase x).card < m := hn ▸ card_erase_lt hx
          exact ⟨x, hx, t, (ih _ hlt (s.erase x) t rfl).mpr ht_eq, rfl⟩

private lemma card_permsOf_mul (s : Multiset ℕ) :
    (permsOf s).card * multFact s = s.card.factorial := by
  induction hn : s.card using Nat.strong_induction_on generalizing s with
  | h m ih =>
    by_cases hs : s = 0
    · subst hs
      simp only [Multiset.card_zero] at hn
      subst hn
      rw [permsOf_zero]
      simp [multFact]
    · rw [permsOf_ne_zero hs]
      have hdisj :
          Set.PairwiseDisjoint (s.toFinset : Set ℕ)
            (fun x => (permsOf (s.erase x)).image (x :: ·)) := by
        intro x _ y _ hxy
        dsimp only [Function.onFun]
        rw [Finset.disjoint_left]
        intro l hlx hly
        rcases Finset.mem_image.mp hlx with ⟨t₁, _, rfl⟩
        rcases Finset.mem_image.mp hly with ⟨t₂, _, hcons⟩
        exact hxy (List.cons.inj hcons).1.symm
      rw [Finset.card_biUnion hdisj]
      have hcard_img : ∀ x ∈ s.toFinset,
          ((permsOf (s.erase x)).image (x :: ·)).card = (permsOf (s.erase x)).card :=
        fun x _ => Finset.card_image_of_injective _ (fun _ _ h => (List.cons.inj h).2)
      rw [Finset.sum_congr rfl hcard_img, Finset.sum_mul]
      have hpos : 0 < s.card := Multiset.card_pos.mpr hs
      obtain ⟨r, hr⟩ : ∃ r, s.card = r + 1 :=
        Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
      have hterm : ∀ x ∈ s.toFinset,
          (permsOf (s.erase x)).card * multFact s = s.count x * r.factorial := by
        intro x hx
        have hxm : x ∈ s := Multiset.mem_toFinset.mp hx
        have hlt : (s.erase x).card < m := hn ▸ card_erase_lt hxm
        have hih := ih _ hlt (s.erase x) rfl
        have hcard_er : (s.erase x).card = r := by
          have h := congrArg Multiset.card (Multiset.cons_erase hxm)
          rw [Multiset.card_cons] at h
          omega
        rw [hcard_er] at hih
        rw [multFact_eq_count_mul_erase s hxm]
        calc
          (permsOf (s.erase x)).card * (s.count x * multFact (s.erase x))
            = s.count x * ((permsOf (s.erase x)).card * multFact (s.erase x)) := by ring
          _ = s.count x * r.factorial := by rw [hih]
      rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, sum_count_eq_card, ← hn, hr,
        Nat.factorial_succ]

private def incHead : List ℕ → List ℕ
  | [] => []
  | a :: t => (a + 1) :: t

private def compList : ℕ → ℕ → Finset (List ℕ)
  | 0, 0 => {[]}
  | 0, _ + 1 => ∅
  | _ + 1, 0 => ∅
  | n + 1, k + 1 => (compList n k).image (1 :: ·) ∪ (compList n (k + 1)).image incHead

private lemma mem_compList (n k : ℕ) (l : List ℕ) :
    l ∈ compList n k ↔ l.length = k ∧ (∀ x ∈ l, 1 ≤ x) ∧ l.sum = n := by
  induction n generalizing k l with
  | zero =>
    cases k with
    | zero =>
      simp only [compList, Finset.mem_singleton]
      cases l with
      | nil => simp
      | cons a t => simp
    | succ k =>
      simp only [compList, Finset.notMem_empty, false_iff, not_and]
      intro hlen hpos hsum
      cases l with
      | nil => simp at hlen
      | cons a t =>
        have ha : 1 ≤ a := hpos a (by simp)
        simp only [List.sum_cons] at hsum
        omega
  | succ n ih =>
    cases k with
    | zero =>
      simp only [compList, Finset.notMem_empty, false_iff, not_and]
      intro hlen _ hsum
      cases l with
      | nil => simp at hsum
      | cons a t => simp at hlen
    | succ k =>
      simp only [compList, Finset.mem_union, Finset.mem_image]
      constructor
      · rintro (⟨t, ht, rfl⟩ | ⟨u, hu, rfl⟩)
        · rcases (ih k t).mp ht with ⟨hlen, hpos, hsum⟩
          refine ⟨by simp [hlen], ?_, by simp [hsum]; omega⟩
          intro x hx
          simp only [List.mem_cons] at hx
          rcases hx with rfl | hx
          · omega
          · exact hpos x hx
        · rcases (ih (k + 1) u).mp hu with ⟨hlen, hpos, hsum⟩
          cases u with
          | nil => simp at hlen
          | cons a t =>
            simp only [incHead, List.length_cons, List.sum_cons] at hlen hsum ⊢
            refine ⟨hlen, ?_, by omega⟩
            intro x hx
            simp only [List.mem_cons] at hx
            rcases hx with rfl | hx
            · omega
            · exact hpos x (by simp [hx])
      · rintro ⟨hlen, hpos, hsum⟩
        cases l with
        | nil => simp at hlen
        | cons a t =>
          have ha : 1 ≤ a := hpos a (by simp)
          by_cases ha1 : a = 1
          · subst ha1
            left
            refine ⟨t, (ih k t).mpr ⟨by simpa using hlen, fun x hx => hpos x (by simp [hx]), ?_⟩, rfl⟩
            simp only [List.sum_cons] at hsum
            omega
          · right
            refine ⟨(a - 1) :: t, (ih (k + 1) ((a - 1) :: t)).mpr ⟨by simpa using hlen, ?_, ?_⟩, ?_⟩
            · intro x hx
              simp only [List.mem_cons] at hx
              rcases hx with rfl | hx
              · omega
              · exact hpos x (by simp [hx])
            · simp only [List.sum_cons] at hsum ⊢
              omega
            · simp only [incHead, List.cons.injEq, and_true]
              omega

private lemma card_compList_step (n k : ℕ) :
    (compList (n + 1) (k + 1)).card = (compList n k).card + (compList n (k + 1)).card := by
  rw [compList]
  have hdisj : Disjoint ((compList n k).image (1 :: ·)) ((compList n (k + 1)).image incHead) := by
    rw [Finset.disjoint_left]
    intro l hl1 hl2
    rcases Finset.mem_image.mp hl1 with ⟨t, _, rfl⟩
    rcases Finset.mem_image.mp hl2 with ⟨u, hu, heq⟩
    rcases (mem_compList n (k + 1) u).mp hu with ⟨hlen, hpos, _⟩
    cases u with
    | nil => simp at hlen
    | cons a v =>
      have ha : 1 ≤ a := hpos a (by simp)
      simp only [incHead, List.cons.injEq] at heq
      omega
  rw [Finset.card_union_of_disjoint hdisj]
  have h1 : ((compList n k).image (1 :: ·)).card = (compList n k).card :=
    Finset.card_image_of_injective _ (fun _ _ h => (List.cons.inj h).2)
  have h2 : ((compList n (k + 1)).image incHead).card = (compList n (k + 1)).card := by
    refine Finset.card_image_of_injOn fun u₁ hu₁ u₂ hu₂ heq => ?_
    rcases (mem_compList n (k + 1) u₁).mp hu₁ with ⟨hlen₁, _, _⟩
    rcases (mem_compList n (k + 1) u₂).mp hu₂ with ⟨hlen₂, _, _⟩
    cases u₁ with
    | nil => simp at hlen₁
    | cons a₁ v₁ =>
      cases u₂ with
      | nil => simp at hlen₂
      | cons a₂ v₂ =>
        simp only [incHead, List.cons.injEq] at heq
        have ha : a₁ = a₂ := by omega
        rw [ha, heq.2]
  rw [h1, h2]

private lemma card_compList_succ (n k : ℕ) :
    (compList (n + 1) (k + 1)).card = n.choose k := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => simp [compList]
    | succ k => simp [compList]
  | succ n ih =>
    cases k with
    | zero =>
      rw [card_compList_step, compList, Finset.card_empty, zero_add, ih 0]
      simp
    | succ k =>
      rw [card_compList_step, ih k, ih (k + 1), Nat.choose_succ_succ]

private lemma card_compList_eq_sum_permsOf (n k : ℕ) :
    (compList n k).card =
      ∑ p ∈ (Finset.univ : Finset (Nat.Partition n)).filter (fun p => p.parts.card = k),
        (permsOf p.parts).card := by
  have hbi : compList n k =
      ((Finset.univ : Finset (Nat.Partition n)).filter (fun p => p.parts.card = k)).biUnion
        (fun p => permsOf p.parts) := by
    ext l
    simp only [mem_compList, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and,
      mem_permsOf]
    constructor
    · rintro ⟨hlen, hpos, hsum⟩
      refine ⟨⟨(l : Multiset ℕ), ?_, by simpa using hsum⟩, by simpa using hlen, rfl⟩
      intro i hi
      have him : i ∈ l := Multiset.mem_coe.mp hi
      exact Nat.pos_of_ne_zero (by have := hpos i him; omega)
    · rintro ⟨p, hcard, heq⟩
      refine ⟨?_, ?_, ?_⟩
      · have h := congrArg Multiset.card heq
        simpa [hcard] using h
      · intro x hx
        have hxp : x ∈ p.parts := heq ▸ Multiset.mem_coe.mpr hx
        exact p.parts_pos hxp
      · have h := congrArg Multiset.sum heq
        simpa [p.parts_sum] using h
  rw [hbi, Finset.card_biUnion]
  intro p₁ _ p₂ _ hne
  dsimp only [Function.onFun]
  rw [Finset.disjoint_left]
  intro l hl₁ hl₂
  rw [mem_permsOf] at hl₁ hl₂
  have hparts : p₁.parts = p₂.parts := hl₁.symm.trans hl₂
  exact hne (by cases p₁; cases p₂; congr)

end OMA.S_oeis_a033282_proof

theorem OMA.solution : type_of% @OMA.S_oeis_a033282.main := by
  intro n k hn hk hkn
  obtain ⟨n', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have hchoose_nat :
      (n' + k' + 2).choose k' * k'.factorial * (n' + 2).factorial =
        (n' + k' + 2).factorial := by
    have h := Nat.choose_mul_factorial_mul_factorial (show k' ≤ n' + k' + 2 by omega)
    rwa [show n' + k' + 2 - k' = n' + 2 by omega] at h
  have hne1 : ((k' + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  have hne2 : ((n' + 2).factorial : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (n' + 2)
  have hne3 : ((k' + 1).factorial : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (k' + 1)
  have hchoose_q :
      ((n' + k' + 2).choose k' : ℚ) / ((k' + 1 : ℕ) : ℚ) =
        ((n' + k' + 2).factorial : ℚ) /
          (((n' + 2).factorial : ℚ) * ((k' + 1).factorial : ℚ)) := by
    have h1 :
        ((n' + k' + 2).choose k' : ℚ) * (k'.factorial : ℚ) * ((n' + 2).factorial : ℚ) =
          ((n' + k' + 2).factorial : ℚ) := by exact_mod_cast hchoose_nat
    have h2 : ((k' + 1).factorial : ℚ) = ((k' + 1 : ℕ) : ℚ) * (k'.factorial : ℚ) := by
      exact_mod_cast Nat.factorial_succ k'
    rw [div_eq_div_iff hne1 (mul_ne_zero hne2 hne3), h2]
    linear_combination ((k' + 1 : ℕ) : ℚ) * h1
  let C : ℚ :=
    (-1 : ℚ) ^ (k' + 1) * ((n' + k' + 2).factorial : ℚ) /
      (((n' + 2).factorial : ℚ) * ((k' + 1).factorial : ℚ))
  have hrev_eq :
      ∀ p ∈ (Finset.univ : Finset (Nat.Partition (n' + 1))).filter
        (fun p => p.parts.card = k' + 1),
        OMA.S_oeis_a033282.rev (n' + 1) p =
          C * ((OMA.S_oeis_a033282_proof.permsOf p.parts).card : ℚ) := by
    intro p hp
    have hcard : p.parts.card = k' + 1 := (Finset.mem_filter.mp hp).2
    have hperm_nat :
        (OMA.S_oeis_a033282_proof.permsOf p.parts).card *
            OMA.S_oeis_a033282_proof.multFact p.parts =
          (k' + 1).factorial := by
      simpa [hcard] using OMA.S_oeis_a033282_proof.card_permsOf_mul p.parts
    have hperm_q :
        ((OMA.S_oeis_a033282_proof.permsOf p.parts).card : ℚ) *
            (OMA.S_oeis_a033282_proof.multFact p.parts : ℚ) =
          ((k' + 1).factorial : ℚ) := by exact_mod_cast hperm_nat
    have hmf_ne : (OMA.S_oeis_a033282_proof.multFact p.parts : ℚ) ≠ 0 := by
      exact_mod_cast OMA.S_oeis_a033282_proof.multFact_ne_zero p.parts
    have hmf_cast :
        (∏ i ∈ p.parts.toFinset, ((p.parts.count i).factorial : ℚ)) =
          (OMA.S_oeis_a033282_proof.multFact p.parts : ℚ) := by
      simp [OMA.S_oeis_a033282_proof.multFact]
    have hdiv :
        (1 : ℚ) / (OMA.S_oeis_a033282_proof.multFact p.parts : ℚ) =
          ((OMA.S_oeis_a033282_proof.permsOf p.parts).card : ℚ) / ((k' + 1).factorial : ℚ) := by
      rw [div_eq_div_iff hmf_ne hne3]
      linarith [hperm_q]
    simp only [OMA.S_oeis_a033282.rev, hcard, hmf_cast,
      show n' + 1 + (k' + 1) = n' + k' + 2 by omega,
      show n' + 1 + 1 = n' + 2 by omega]
    calc
      (-1 : ℚ) ^ (k' + 1) * ((n' + k' + 2).factorial : ℚ) /
          (((n' + 2).factorial : ℚ) * (OMA.S_oeis_a033282_proof.multFact p.parts : ℚ))
        = ((-1 : ℚ) ^ (k' + 1) * ((n' + k' + 2).factorial : ℚ) / ((n' + 2).factorial : ℚ)) *
            (1 / (OMA.S_oeis_a033282_proof.multFact p.parts : ℚ)) := by ring
      _ = ((-1 : ℚ) ^ (k' + 1) * ((n' + k' + 2).factorial : ℚ) / ((n' + 2).factorial : ℚ)) *
            (((OMA.S_oeis_a033282_proof.permsOf p.parts).card : ℚ) /
              ((k' + 1).factorial : ℚ)) := by rw [hdiv]
      _ = C * ((OMA.S_oeis_a033282_proof.permsOf p.parts).card : ℚ) := by
            dsimp only [C]
            ring
  rw [Finset.sum_congr rfl hrev_eq, ← Finset.mul_sum, ← Nat.cast_sum,
    ← OMA.S_oeis_a033282_proof.card_compList_eq_sum_permsOf,
    OMA.S_oeis_a033282_proof.card_compList_succ]
  simp only [OMA.S_oeis_a033282.T,
    show n' + 1 + 2 - 3 = n' by omega,
    show k' + 1 - 1 = k' by omega,
    show n' + 1 + 2 + k' - 1 = n' + k' + 2 by omega]
  have hk_cast : (k' : ℚ) + 1 = ((k' + 1 : ℕ) : ℚ) := by push_cast; ring
  rw [hk_cast]
  calc
    (-1 : ℚ) ^ (k' + 1) * (((n'.choose k' : ℚ) * ((n' + k' + 2).choose k' : ℚ)) /
        ((k' + 1 : ℕ) : ℚ))
      = (-1 : ℚ) ^ (k' + 1) * (n'.choose k' : ℚ) *
          (((n' + k' + 2).choose k' : ℚ) / ((k' + 1 : ℕ) : ℚ)) := by ring
    _ = (-1 : ℚ) ^ (k' + 1) * (n'.choose k' : ℚ) *
          (((n' + k' + 2).factorial : ℚ) /
            (((n' + 2).factorial : ℚ) * ((k' + 1).factorial : ℚ))) := by rw [hchoose_q]
    _ = C * (n'.choose k' : ℚ) := by
          dsimp only [C]
          ring
