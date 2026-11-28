import OMAReductions.R_wp_1_3_2_3_conjecture_R1

-- Credit: @wispiANt
namespace OMA.R_wp_1_3_2_3_conjecture_R1_H2_R1

open scoped Classical in
def H1 : Prop := ∀ (P : Type) [PartialOrder P] [Fintype P],
    let C (A : Type) [PartialOrder A] [Fintype A] (l : List (A × A)) :=
      Nat.card {f : A ≃ Fin (Fintype.card A) // (∀ u v, u < v → f u < f v) ∧ ∀ p ∈ l, f p.1 < f p.2}
    (¬ ∀ x y : P, x ≤ y ∨ y ≤ x) →
    (¬ ∃ L : Set P, L.Nonempty ∧ (∃ y, y ∉ L) ∧
      ∀ x ∈ L, ∀ y ∉ L, x < y) →
    (∀ (e : P ≃o P) x, e x = x) →
    (∃ a b c : P, (¬ a ≤ b ∧ ¬ b ≤ a) ∧ (¬ a ≤ c ∧ ¬ c ≤ a) ∧ (¬ b ≤ c ∧ ¬ c ≤ b)) →
    (∃ x : P, let N := {y : P | ¬ x ≤ y ∧ ¬ y ≤ x}
      let Q := {y : P // y ≠ x}
      7 ≤ N.ncard ∧ (∀ a b : Q, a ≠ b → 2 * C P [] <
        3 * ((N.ncard+1) * max (C Q [(a,b)]) (C Q [(b,a)])) ∧
        3 * min (C Q [(a,b)]) (C Q [(b,a)]) < C P []) ∧
      (∃ a ∈ N, ∃ b ∈ N, ∃ c ∈ N, ∃ d ∈ N, a ⋖ b ∧ b ⋖ c ∧ c ⋖ d ∧
      let jump (u v : P) := 3 * C P [(x,u)] < C P [] ∧ 2 * C P [] < 3 * C P [(x,v)] ∧
        C P [] < 3 * C P [(u,x),(x,v)]
      2 * C P [] < 3 * C P [(x,a)] ∨ 2 * C P [] < 3 * C P [(d,x)] ∨
        jump a b ∨ jump b c ∨ jump c d)) →
    (let terminal (A : Type) [PartialOrder A] [Fintype A] := ∃ t a b c d : A,
      let inc (u v : A) := ¬ u ≤ v ∧ ¬ v ≤ u
      a ⋖ b ∧ a ⋖ c ∧ d ⋖ c ∧ inc d a ∧ inc d b ∧ inc b c ∧
      (∀ z ∈ [a,b,c], inc t z) ∧ 2 * C A [] < 3 * C A [(b,c)] ∧
      2 * C A [] < 3 * C A [(a,t)] ∧ 3 * C A [(b,t)] < C A [] ∧ 3 * C A [(c,t)] < C A []
     terminal P ∧ terminal Pᵒᵈ) →
    (∀ a b : P, ¬ a ≤ b → 2 * C P [] < 3 * C P [(a,b)] →
      2 ≤ ({z : P | (z < b ∧ ¬ z < a) ∨ (a < z ∧ ¬ b < z)} : Set P).ncard) →
    (¬ (∃ x y u v : P, x ≠ y ∧ u ≠ v ∧
      ∀ p ∈ [(x, y), (y, x)], ∀ q ∈ [(u, v), (v, u)],
        C P [p] + C P [p, q] ≤ C P [])) →
    let ext : Finset (P ≃ Fin (Fintype.card P)) := by
      classical
      exact Finset.univ.filter (fun rank => StrictMono rank)
    ∃ x y : P, x ≠ y ∧
      let p := ((ext.filter (fun r => r x < r y)).card : ℚ) / ext.card
      1 / 3 ≤ p ∧ p ≤ 2 / 3

open scoped Classical in
def H2 : Prop := ∀ (P : Type) [PartialOrder P] [Fintype P],
    let C (A : Type) [PartialOrder A] [Fintype A] (l : List (A × A)) :=
      Nat.card {f : A ≃ Fin (Fintype.card A) // (∀ u v, u < v → f u < f v) ∧ ∀ p ∈ l, f p.1 < f p.2}
    (¬ ∀ x y : P, x ≤ y ∨ y ≤ x) →
    (¬ ∃ L : Set P, L.Nonempty ∧ (∃ y, y ∉ L) ∧
      ∀ x ∈ L, ∀ y ∉ L, x < y) →
    (∀ (e : P ≃o P) x, e x = x) →
    (∃ x : P, let N := {y : P | ¬ x ≤ y ∧ ¬ y ≤ x}
      let Q := {y : P // y ≠ x}
      7 ≤ N.ncard ∧ (∀ a b : Q, a ≠ b → 2 * C P [] <
        3 * ((N.ncard+1) * max (C Q [(a,b)]) (C Q [(b,a)])) ∧
        3 * min (C Q [(a,b)]) (C Q [(b,a)]) < C P []) ∧
      (¬ ∃ a ∈ N, ∃ b ∈ N, ∃ c ∈ N, ∃ d ∈ N, a < b ∧ b < c ∧ c < d) ∧
      ∃ t : Finset P, x ∈ t ∧ (t : Set P).Pairwise (fun a b => ¬ a ≤ b) ∧
        4 ≤ t.card ∧ N.ncard + 3 ≤ 3 * t.card) →
    (let fork (r c : P → P → Prop) := ∃ x y, x ≠ y ∧ (∀ z, c z x ↔ c z y) ∧
      ∀ z ∈ [x,y], IsChain r {a | r z a}
     ¬ fork (· ≤ ·) (· ⋖ ·) ∧ ¬ fork (· ≥ ·) (fun a b => b ⋖ a)) →
    (∀ a b : P, ¬ a ≤ b → 2 * C P [] < 3 * C P [(a,b)] →
      2 ≤ ({z : P | (z < b ∧ ¬ z < a) ∨ (a < z ∧ ¬ b < z)} : Set P).ncard) →
    (¬ (∃ x y u v : P, x ≠ y ∧ u ≠ v ∧
      ∀ p ∈ [(x, y), (y, x)], ∀ q ∈ [(u, v), (v, u)],
        C P [p] + C P [p, q] ≤ C P [])) →
    let ext : Finset (P ≃ Fin (Fintype.card P)) := by
      classical
      exact Finset.univ.filter (fun rank => StrictMono rank)
    ∃ x y : P, x ≠ y ∧
      let p := ((ext.filter (fun r => r x < r y)).card : ℚ) / ext.card
      1 / 3 ≤ p ∧ p ≤ 2 / 3

-- The three levels consist of endpoints whose longest chain in s has
-- respectively one, two or three elements.
lemma large_level (P : Type) [PartialOrder P] (s : Finset P)
    (short : ¬ ∃ a ∈ s, ∃ b ∈ s, ∃ c ∈ s, ∃ d ∈ s, a < b ∧ b < c ∧ c < d) :
    ∃ t : Finset P, t ⊆ s ∧ (t : Set P).Pairwise (fun a b => ¬ a ≤ b) ∧
      s.card ≤ 3 * t.card := by
  classical
  let pred (b : P) := ∃ a ∈ s, a < b
  let two (c : P) := ∃ b ∈ s, pred b ∧ b < c
  let above := s.filter pred
  let low := s.filter (fun a => ¬ pred a)
  let mid := above.filter (fun a => ¬ two a)
  let high := above.filter two
  have lowerAnti : (low : Set P).Pairwise (fun a b => ¬ a ≤ b) := by
    intro a ha b hb ne ab
    exact (Finset.mem_filter.mp hb).2 ⟨a, (Finset.mem_filter.mp ha).1, lt_of_le_of_ne ab ne⟩
  have middleAnti : (mid : Set P).Pairwise (fun a b => ¬ a ≤ b) := by
    intro a ha b hb ne ab
    obtain ⟨mem, pr⟩ := Finset.mem_filter.mp (Finset.mem_filter.mp ha).1
    exact (Finset.mem_filter.mp hb).2 ⟨a, mem, pr, lt_of_le_of_ne ab ne⟩
  have upperAnti : (high : Set P).Pairwise (fun a b => ¬ a ≤ b) := by
    intro a ha b hb ne ab
    obtain ⟨c, hc, ⟨d, hd, dc⟩, ca⟩ := (Finset.mem_filter.mp ha).2
    exact short ⟨d, hd, c, hc, a, (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).1,
      b, (Finset.mem_filter.mp (Finset.mem_filter.mp hb).1).1, dc, ca, lt_of_le_of_ne ab ne⟩
  have cut₁ : above.card + low.card = s.card := Finset.card_filter_add_card_filter_not _
  have cut₂ : high.card + mid.card = above.card := Finset.card_filter_add_card_filter_not _
  have sub : above ⊆ s := Finset.filter_subset _ _
  by_cases l : s.card ≤ 3 * low.card
  · exact ⟨low, Finset.filter_subset _ _, lowerAnti, l⟩
  by_cases m : s.card ≤ 3 * mid.card
  · exact ⟨mid, (Finset.filter_subset _ _).trans sub, middleAnti, m⟩
  exact ⟨high, (Finset.filter_subset _ _).trans sub, upperAnti, by omega⟩

lemma antichain_through_vertex (P : Type) [PartialOrder P] [Fintype P] (x : P) :
    let N := {y : P | ¬ x ≤ y ∧ ¬ y ≤ x}
    (¬ ∃ a ∈ N, ∃ b ∈ N, ∃ c ∈ N, ∃ d ∈ N, a < b ∧ b < c ∧ c < d) →
    ∃ t : Finset P, x ∈ t ∧ (t : Set P).Pairwise (fun a b => ¬ a ≤ b) ∧
      N.ncard + 3 ≤ 3 * t.card := by
  classical
  intro N short
  let s := Finset.univ.filter (fun y : P => y ∈ N)
  have mem (y : P) : y ∈ s ↔ y ∈ N := by simp [s]
  have size : N.ncard = s.card := by
    have h : (s : Set P) = N := Set.ext mem
    rw [← h, Set.ncard_coe_finset]
  obtain ⟨t, sub, anti, bound⟩ := large_level P s (by
    rintro ⟨a, ha, b, hb, c, hc, d, hd, chain⟩
    exact short ⟨a, (mem _).1 ha, b, (mem _).1 hb, c, (mem _).1 hc, d, (mem _).1 hd, chain⟩)
  have inc {a : P} (ha : a ∈ t) : ¬ x ≤ a ∧ ¬ a ≤ x := (mem a).1 (sub ha)
  have outside : x ∉ t := fun h => (inc h).1 le_rfl
  refine ⟨insert x t, Finset.mem_insert_self _ _, ?_, ?_⟩
  · intro a ha b hb ne
    by_cases ax : a = x
    · subst a
      exact (inc ((Finset.mem_insert.mp hb).resolve_left ne.symm)).1
    have at' := (Finset.mem_insert.mp ha).resolve_left ax
    by_cases bx : b = x
    · subst b
      exact (inc at').2
    exact anti at' ((Finset.mem_insert.mp hb).resolve_left bx) ne
  · rw [size, Finset.card_insert_of_notMem outside]
    omega

-- On a chain, the count before v increases from the count before u by
-- exactly the number of extensions inserting x strictly between u and v.
lemma insertion_count (P : Type) [PartialOrder P] [Fintype P] :
    let C (l : List (P × P)) := Nat.card {r : P ≃ Fin (Fintype.card P) //
      (∀ a b : P, a < b → r a < r b) ∧ ∀ p ∈ l, r p.1 < r p.2}
    ∀ x u v : P, x ≠ u → u < v →
      C [(x,u)] + C [(u,x),(x,v)] = C [(x,v)] := by
  intro C x u v xu uv
  obtain ⟨_, _, split, cells⟩ := OMA.R_wp_1_3_2_3_conjecture_R1.comparison_counts P
  have nested : C [(x,v),(x,u)] = C [(x,u)] := by
    apply Nat.card_congr (Equiv.subtypeEquivRight ?_)
    intro r
    simp only [List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff]
    constructor
    · exact fun h => ⟨h.1, h.2.2⟩
    · exact fun h => ⟨h.1, lt_trans h.2.1 (h.1 u v uv), h.2⟩
  have parts : C [(x,v),(x,u)] + C [(x,v),(u,x)] = C [(x,v)] := split [(x,v)] x u xu
  have swap : C [(x,v),(u,x)] = C [(u,x),(x,v)] := (cells _ _).2.2
  rwa [nested, swap] at parts

lemma pair_of_count_bounds (P : Type) [PartialOrder P] [Fintype P] :
    let C (l : List (P × P)) := Nat.card {r : P ≃ Fin (Fintype.card P) //
      (∀ a b : P, a < b → r a < r b) ∧ ∀ p ∈ l, r p.1 < r p.2}
    ∀ x y : P, x ≠ y → C [] ≤ 3 * C [(x,y)] → 3 * C [(x,y)] ≤ 2 * C [] →
    let ext : Finset (P ≃ Fin (Fintype.card P)) := by
      classical
      exact Finset.univ.filter (fun rank => StrictMono rank)
    ∃ x y : P, x ≠ y ∧
      let p := ((ext.filter (fun r => r x < r y)).card : ℚ) / ext.card
      1 / 3 ≤ p ∧ p ≤ 2 / 3 := by
  classical
  intro C x y ne lo hi ext
  obtain ⟨den, num, _, _⟩ := OMA.R_wp_1_3_2_3_conjecture_R1.comparison_counts P
  have den' : C [] = ext.card := den
  have num' : C [(x,y)] = (ext.filter (fun r => r x < r y)).card := num x y
  rw [den', num'] at lo hi
  obtain ⟨r, hr⟩ := OMA.R_wp_1_3_2_3_conjecture_R1.rank_exists P
  have pos : 0 < ext.card := Finset.card_pos.mpr ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr⟩⟩
  let k := (ext.filter (fun r => r x < r y)).card
  have l : (ext.card : ℚ) ≤ 3 * (k : ℚ) := by exact_mod_cast lo
  have h : 3 * (k : ℚ) ≤ 2 * (ext.card : ℚ) := by exact_mod_cast hi
  have p : (0 : ℚ) < ext.card := by exact_mod_cast pos
  refine ⟨x, y, ne, (le_div_iff₀ p).2 ?_, (div_le_iff₀ p).2 ?_⟩ <;> linarith

-- A failed balanced-pair search forces either a heavy exterior slot or
-- an interior jump from strictly below one third to strictly above two thirds.
lemma four_chain_slots (P : Type) [PartialOrder P] [Fintype P] :
    let C (l : List (P × P)) := Nat.card {r : P ≃ Fin (Fintype.card P) //
      (∀ a b : P, a < b → r a < r b) ∧ ∀ p ∈ l, r p.1 < r p.2}
    ∀ x a b c d : P, x ≠ a → x ≠ b → x ≠ c → x ≠ d → a < b → b < c → c < d →
    (∃ y ∈ [a,b,c,d], C [] ≤ 3 * C [(x,y)] ∧ 3 * C [(x,y)] ≤ 2 * C []) ∨
    (let jump (u v : P) := 3 * C [(x,u)] < C [] ∧ 2 * C [] < 3 * C [(x,v)] ∧
        C [] < 3 * C [(u,x),(x,v)];
      2 * C [] < 3 * C [(x,a)] ∨ 2 * C [] < 3 * C [(d,x)] ∨ jump a b ∨ jump b c ∨ jump c d) := by
  classical
  intro C x a b c d xa xb xc xd ab bc cd
  apply or_iff_not_imp_left.mpr
  intro ok jump
  have dich (y : P) (hy : y ∈ [a,b,c,d]) : 3 * C [(x,y)] < C [] ∨ 2 * C [] < 3 * C [(x,y)] := by
    by_contra! h
    exact ok ⟨y, hy, h⟩
  have middle (u v : P) (ne : x ≠ u) (uv : u < v)
      (lo : 3 * C [(x,u)] < C []) (hi : 2 * C [] < 3 * C [(x,v)]) : jump u v := by
    have part : C [(x,u)] + C [(u,x),(x,v)] = C [(x,v)] := insertion_count P x u v ne uv
    exact ⟨lo, hi, by omega⟩
  rcases dich a (by simp) with la | ha
  · rcases dich b (by simp) with lb | hb
    · rcases dich c (by simp) with lc | hc
      · rcases dich d (by simp) with ld | hd
        · obtain ⟨_, _, split, _⟩ := OMA.R_wp_1_3_2_3_conjecture_R1.comparison_counts P
          have part : C [(x,d)] + C [(d,x)] = C [] := split [] x d xd
          exact Or.inr (Or.inl (by omega))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (middle c d xc cd lc hd))))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (middle b c xb bc lb hc))))
    · exact Or.inr (Or.inr (Or.inl (middle a b xa ab la hb)))
  · exact Or.inl ha

-- Rank transposition injects the source cell into any target cell whose
-- comparisons survive the swap.
open scoped Classical in
lemma swap_cell_bound (P : Type) [PartialOrder P] [Fintype P] :
    let C (l : List (P × P)) := Nat.card {r : P ≃ Fin (Fintype.card P) //
      (∀ a b : P, a < b → r a < r b) ∧ ∀ p ∈ l, r p.1 < r p.2}
    ∀ (l m : List (P × P)) (i j : P), ¬ i ≤ j → (i,j) ∈ l →
      (∀ r : P ≃ Fin (Fintype.card P), StrictMono r → (∀ p ∈ l, r p.1 < r p.2) →
        (∀ b, i < b → r j < r b) ∧ (∀ a, a < j → r a < r i) ∧
        ∀ p ∈ m, r (Equiv.swap i j p.1) < r (Equiv.swap i j p.2)) → C l ≤ C m := by
  classical
  intro C l m i j ij ordered safe
  let ranks (cs : List (P × P)) := {r : P ≃ Fin (Fintype.card P) //
    (∀ a b : P, a < b → r a < r b) ∧ ∀ p ∈ cs, r p.1 < r p.2}
  let swap := Equiv.swap i j
  have valid (r : ranks l) : StrictMono (swap.trans r.val) := by
    have mono : StrictMono r.val := fun _ _ h => r.property.1 _ _ h
    have before := r.property.2 (i,j) ordered
    obtain ⟨upper,lower,_⟩ := safe r.val mono r.property.2
    intro a b ab
    change r.val (swap a) < r.val (swap b)
    by_cases ai : a = i
    · subst a
      have bj : b ≠ j := fun h => ij (h ▸ ab.le)
      simp only [swap, Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne ab.ne.symm bj]
      exact upper b ab
    by_cases bj : b = j
    · subst b
      simp only [swap, Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne ai ab.ne]
      exact lower a ab
    have left : r.val (swap a) ≤ r.val a := by
      by_cases aj : a = j
      · simpa [aj,swap] using before.le
      · simp [swap, Equiv.swap_apply_of_ne_of_ne ai aj]
    have right : r.val b ≤ r.val (swap b) := by
      by_cases bi : b = i
      · simpa [bi,swap] using before.le
      · simp [swap, Equiv.swap_apply_of_ne_of_ne bi bj]
    exact lt_of_le_of_lt left (lt_of_lt_of_le (mono ab) right)
  let move (r : ranks l) : ranks m := ⟨swap.trans r.val, fun _ _ h => valid r h,
    (safe r.val (fun _ _ h => r.property.1 _ _ h) r.property.2).2.2⟩
  have inj : Function.Injective move := by
    intro r s h
    apply Subtype.ext
    apply Equiv.ext
    intro a
    have eq := congrArg (fun t : ranks m => t.val (swap.symm a)) h
    change r.val (swap (swap.symm a)) = s.val (swap (swap.symm a)) at eq
    simpa using eq
  exact Nat.card_le_card_of_injective move inj

lemma obstruction_of_count_excess (P : Type) [PartialOrder P] [Fintype P] :
    let C (l : List (P × P)) := Nat.card {r : P ≃ Fin (Fintype.card P) //
      (∀ a b : P, a < b → r a < r b) ∧ ∀ p ∈ l, r p.1 < r p.2}
    ∀ (l : List (P × P)) (i j : P), ¬ i ≤ j → (i,j) ∈ l →
      C [(j,i)] < C l →
      ∃ (r : P ≃ Fin (Fintype.card P)) (z : P), StrictMono r ∧
        (∀ p ∈ l, r p.1 < r p.2) ∧ r i < r z ∧ r z < r j ∧ (i < z ∨ z < j) := by
  classical
  intro C l i j ij ordered excess
  by_contra absent
  apply (not_le_of_gt excess)
  apply swap_cell_bound P l [(j,i)] i j ij ordered
  intro r mono extra
  refine ⟨?_,?_,?_⟩
  · intro b ib
    have bj : b ≠ j := fun h => ij (h ▸ ib.le)
    by_contra! h
    exact absent ⟨r,b,mono,extra,mono ib,lt_of_le_of_ne h (r.injective.ne bj),Or.inl ib⟩
  · intro a aj
    have ai : a ≠ i := fun h => ij (h ▸ aj.le)
    by_contra! h
    exact absent ⟨r,a,mono,extra,lt_of_le_of_ne h (r.injective.ne ai.symm),mono aj,Or.inr aj⟩
  · intro p hp
    obtain rfl : p = (j,i) := by simpa using hp
    simpa using extra (i,j) ordered

lemma four_chain_obstructions (P : Type) [PartialOrder P] [Fintype P] :
    let C (l : List (P × P)) := Nat.card {r : P ≃ Fin (Fintype.card P) //
      (∀ a b : P, a < b → r a < r b) ∧ ∀ p ∈ l, r p.1 < r p.2}
    ∀ x a b c d : P, (∀ y ∈ [a,b,c,d], ¬ x ≤ y ∧ ¬ y ≤ x) → a < b → b < c → c < d →
    (∃ y ∈ [a,b,c,d], C [] ≤ 3 * C [(x,y)] ∧ 3 * C [(x,y)] ≤ 2 * C []) ∨
    (let blocked (l : List (P × P)) (i j : P) := ∃ (r : P ≃ Fin (Fintype.card P)) (z : P),
        StrictMono r ∧ (∀ p ∈ l, r p.1 < r p.2) ∧ r i < r z ∧ r z < r j ∧ (i < z ∨ z < j);
      let jump (u v : P) := let l := [(u,x),(x,v)];
        3 * C [(x,u)] < C [] ∧ 2 * C [] < 3 * C [(x,v)] ∧
        C [] < 3 * C l ∧ blocked l u x ∧ blocked l x v;
      (2 * C [] < 3 * C [(x,a)] ∧ blocked [(x,a)] x a) ∨
      (2 * C [] < 3 * C [(d,x)] ∧ blocked [(d,x)] d x) ∨ jump a b ∨ jump b c ∨ jump c d) := by
  classical
  intro C x a b c d inc ab bc cd
  have neq (y : P) (hy : y ∈ [a,b,c,d]) : x ≠ y := fun h => (inc y hy).1 h.le
  obtain ⟨_, _, split, _⟩ := OMA.R_wp_1_3_2_3_conjecture_R1.comparison_counts P
  rcases four_chain_slots P x a b c d (neq _ (by simp)) (neq _ (by simp))
    (neq _ (by simp)) (neq _ (by simp)) ab bc cd with ok | gap
  · exact Or.inl ok
  right
  intro blocked jump
  have endSlot (i j : P) (ij : ¬ i ≤ j) (big : 2 * C [] < 3 * C [(i,j)]) :
      blocked [(i,j)] i j := by
    have part : C [(i,j)] + C [(j,i)] = C [] := split [] i j (fun h => ij h.le)
    have excess : C [(j,i)] < C [(i,j)] := by omega
    exact obstruction_of_count_excess P _ i j ij (by simp) excess
  have middle (u v : P) (hu : u ∈ [a,b,c,d]) (hv : v ∈ [a,b,c,d])
      (lo : 3 * C [(x,u)] < C []) (hi : 2 * C [] < 3 * C [(x,v)])
      (mass : C [] < 3 * C [(u,x),(x,v)]) : jump u v := by
    have part : C [(x,v)] + C [(v,x)] = C [] := split [] x v (neq v hv)
    have left : C [(x,u)] < C [(u,x),(x,v)] := by omega
    have right : C [(v,x)] < C [(u,x),(x,v)] := by omega
    exact ⟨lo, hi, mass,
      obstruction_of_count_excess P _ u x (inc u hu).2 (by simp) left,
      obstruction_of_count_excess P _ x v (inc v hv).1 (by simp) right⟩
  rcases gap with first | last | ⟨lo,hi,mass⟩ | ⟨lo,hi,mass⟩ | ⟨lo,hi,mass⟩
  · exact Or.inl ⟨first, endSlot x a (inc _ (by simp)).1 first⟩
  · exact Or.inr (Or.inl ⟨last, endSlot d x (inc _ (by simp)).2 last⟩)
  · exact Or.inr (Or.inr (Or.inl (middle a b (by simp) (by simp) lo hi mass)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (middle b c (by simp) (by simp) lo hi mass))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (middle c d (by simp) (by simp) lo hi mass))))

lemma next_cover_le (P : Type) [PartialOrder P] [Fintype P] (s t : P) (st : s < t) :
    ∃ y, s ⋖ y ∧ y ≤ t := by
  classical
  obtain ⟨rank, mono⟩ := OMA.R_wp_1_3_2_3_conjecture_R1.rank_exists P
  let candidates := Finset.univ.filter (fun z : P => s < z ∧ z ≤ t)
  have mem (z : P) : z ∈ candidates ↔ s < z ∧ z ≤ t := by simp [candidates]
  obtain ⟨y,hy,least⟩ := candidates.exists_min_image rank ⟨t,(mem t).2 ⟨st,le_rfl⟩⟩
  obtain ⟨sy,yt⟩ := (mem y).1 hy
  exact ⟨y,⟨sy,fun z sz zy => (mono zy).not_ge (least z ((mem z).2 ⟨sz,zy.le.trans yt⟩))⟩,yt⟩

-- At a maximal majority comparison only the successors outside the other
-- vertex's upper cone obstruct exchange. Compare Peczarski's upper-chain
-- argument in the parent reduction and Zaguia's good pairs (arXiv:1610.00809).
lemma majority_cover_alternative (P : Type) [PartialOrder P] [Fintype P] :
    let C (l : List (P × P)) := Nat.card {r : P ≃ Fin (Fintype.card P) //
      (∀ a b : P, a < b → r a < r b) ∧ ∀ p ∈ l, r p.1 < r p.2}
    ∀ s y : P, ¬ s ≤ y → ¬ y ≤ s → (∀ z, z < y → z < s) → C [] ≤ 2 * C [(s,y)] →
      ((∃ i j k l : P, i ≠ j ∧ k ≠ l ∧
        ∀ p ∈ [(i,j),(j,i)], ∀ q ∈ [(k,l),(l,k)], C [p] + C [p,q] ≤ C []) ∧
       ∃ t : P, s ≤ t ∧ t ≠ y ∧ C [] ≤ 3 * C [(t,y)] ∧ 3 * C [(t,y)] ≤ 2 * C []) ∨
      ∃ a b c : P, s ≤ a ∧ ¬ y ≤ a ∧ C [] ≤ 2 * C [(a,y)] ∧
        b ≠ c ∧ ∀ z ∈ [b,c], a ⋖ z ∧ ¬ y ≤ z ∧ 2 * C [(z,y)] < C [] := by
  classical
  intro C s y sy ys pred start
  obtain ⟨rank,mono⟩ := OMA.R_wp_1_3_2_3_conjecture_R1.rank_exists P
  let eligible := Finset.univ.filter (fun a : P => s ≤ a ∧ ¬ y ≤ a ∧ C [] ≤ 2 * C [(a,y)])
  have mem (a : P) : a ∈ eligible ↔ s ≤ a ∧ ¬ y ≤ a ∧ C [] ≤ 2 * C [(a,y)] := by simp [eligible]
  obtain ⟨a,ha,last⟩ := eligible.exists_max_image rank ⟨s,(mem s).2 ⟨le_rfl,ys,start⟩⟩
  obtain ⟨sa,ya,majority⟩ := (mem a).1 ha
  have ay : ¬ a ≤ y := fun h => sy (sa.trans h)
  have ne : a ≠ y := fun h => ay h.le
  have below (z : P) (zy : z < y) : z < a := lt_of_lt_of_le (pred z zy) sa
  have minority (z : P) (az : a < z) (yz : ¬ y ≤ z) : 2 * C [(z,y)] < C [] := by
    by_contra! high
    exact (mono az).not_ge (last z ((mem z).2 ⟨sa.trans az.le,yz,high⟩))
  obtain ⟨_,_,split,_⟩ := OMA.R_wp_1_3_2_3_conjecture_R1.comparison_counts P
  have row : C [(a,y)] + C [(y,a)] = C [] := split [] a y ne
  by_cases existsCover : ∃ b : P, a ⋖ b ∧ ¬ y ≤ b
  · obtain ⟨b,ab,yb⟩ := existsCover
    by_cases second : ∃ c : P, a ⋖ c ∧ ¬ y ≤ c ∧ b ≠ c
    · obtain ⟨c,ac,yc,bc⟩ := second
      right
      refine ⟨a,b,c,sa,ya,majority,bc,?_⟩
      intro z hz
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
      rcases hz with rfl | rfl
      · exact ⟨ab,yb,minority _ ab.1 yb⟩
      · exact ⟨ac,yc,minority _ ac.1 yc⟩
    left
    have cell : C [(a,y),(y,b)] ≤ C [(y,a)] := by
      apply OMA.R_wp_1_3_2_3_conjecture_R1.exchange_count_le P a y _ ay below
      intro r hr extra
      refine ⟨extra (a,y) (by simp),?_⟩
      intro t at'
      by_cases yt : y ≤ t
      · exact hr (lt_of_le_of_ne yt (fun e => ay (e ▸ at'.le)))
      obtain ⟨c,ac,ct⟩ := next_cover_le P a t at'
      have bc : b = c := by
        by_contra h
        exact second ⟨c,ac,fun yc => yt (yc.trans ct),h⟩
      exact lt_of_lt_of_le (extra (y,b) (by simp)) (hr.monotone (bc ▸ ct))
    have small := minority b ab.1 yb
    constructor
    · exact OMA.R_wp_1_3_2_3_conjecture_R1.balanced_triple_gold P a y b ne
        (fun e => yb e.le) ab.1.ne (cell.trans (le_max_left _ _)) (by
          change 2 * max (C [(y,a)]) (C [(b,y)]) ≤ C []
          omega)
    · by_cases hi : 3 * C [(a,y)] ≤ 2 * C []
      · exact ⟨a,sa,ne,by omega,hi⟩
      have partition : C [(y,a)] + C [(a,y),(y,b)] = C [(y,b)] :=
        insertion_count P y a b ne.symm ab.1
      have both : C [(y,b)] + C [(b,y)] = C [] := split [] y b (fun e => yb e.le)
      exact ⟨b,sa.trans ab.1.le,fun e => yb e.ge,by omega,by omega⟩
  · left
    have bound : C [(a,y)] ≤ C [(y,a)] := by
      apply OMA.R_wp_1_3_2_3_conjecture_R1.exchange_count_le P a y _ ay below
      intro r hr extra
      refine ⟨extra (a,y) (by simp),?_⟩
      intro t at'
      obtain ⟨c,ac,ct⟩ := next_cover_le P a t at'
      have yc : y ≤ c := by
        by_contra h
        exact existsCover ⟨c,ac,h⟩
      exact hr (lt_of_le_of_ne (yc.trans ct) (fun e => ay (e ▸ at'.le)))
    have tie : 2 * C [(a,y)] = C [] := by omega
    exact ⟨OMA.R_wp_1_3_2_3_conjecture_R1.tied_comparison_gold P a y ne tie,
      a,sa,ne,by omega,by omega⟩

-- Common successors can branch freely. A chain of exclusive successors
-- rules out the two distinct covers supplied by majority_cover_alternative.
lemma exclusive_chain_certificate (P : Type) [PartialOrder P] [Fintype P] :
    let C (l : List (P × P)) := Nat.card {r : P ≃ Fin (Fintype.card P) //
      (∀ a b : P, a < b → r a < r b) ∧ ∀ p ∈ l, r p.1 < r p.2}
    ∀ s y : P, ¬ s ≤ y → ¬ y ≤ s → (∀ z, z < y → z < s) → C [] ≤ 2 * C [(s,y)] →
      IsChain (· ≤ ·) {z : P | s < z ∧ ¬ y ≤ z} →
      (∃ i j k l : P, i ≠ j ∧ k ≠ l ∧
        ∀ p ∈ [(i,j),(j,i)], ∀ q ∈ [(k,l),(l,k)], C [p] + C [p,q] ≤ C []) ∧
      ∃ t : P, s ≤ t ∧ t ≠ y ∧ C [] ≤ 3 * C [(t,y)] ∧ 3 * C [(t,y)] ≤ 2 * C [] := by
  intro C s y sy ys pred start chain
  rcases majority_cover_alternative P s y sy ys pred start with cert | ⟨a,b,c,sa,_,_,bc,h⟩
  · exact cert
  obtain ⟨ab,yb,_⟩ := h b (by simp)
  obtain ⟨ac,yc,_⟩ := h c (by simp)
  rcases chain (show s < b ∧ ¬ y ≤ b from ⟨lt_of_le_of_lt sa ab.1,yb⟩)
    (show s < c ∧ ¬ y ≤ c from ⟨lt_of_le_of_lt sa ac.1,yc⟩) bc with le | le
  · exact (ac.2 ab.1 (lt_of_le_of_ne le bc)).elim
  · exact (ab.2 ac.1 (lt_of_le_of_ne le bc.symm)).elim

-- Restart the alternative at the two children whenever their majority
-- orientation still has predecessor inclusion. A maximal start rules that
-- out and forces a second lower cover of the later child, giving an induced N.
lemma terminal_majority_covers (P : Type) [PartialOrder P] [Fintype P] :
    let C (l : List (P × P)) := Nat.card {r : P ≃ Fin (Fintype.card P) //
      (∀ a b : P, a < b → r a < r b) ∧ ∀ p ∈ l, r p.1 < r p.2}
    let start (s y : P) := ¬ s ≤ y ∧ ¬ y ≤ s ∧ (∀ z, z < y → z < s) ∧ C [] ≤ 2 * C [(s,y)]
    ∀ s y : P, start s y →
      (∃ i j k l : P, i ≠ j ∧ k ≠ l ∧
        ∀ p ∈ [(i,j),(j,i)], ∀ q ∈ [(k,l),(l,k)], C [p] + C [p,q] ≤ C []) ∨
      ∃ t a b c d : P, s ≤ a ∧ a ⋖ b ∧ a ⋖ c ∧ d ⋖ c ∧
        (¬ d ≤ a ∧ ¬ a ≤ d) ∧ (¬ d ≤ b ∧ ¬ b ≤ d) ∧ (¬ b ≤ c ∧ ¬ c ≤ b) ∧
        (∀ z ∈ [a,b,c], ¬ t ≤ z ∧ ¬ z ≤ t) ∧
        C [] ≤ 2 * C [(b,c)] ∧ C [] ≤ 2 * C [(a,t)] ∧
        2 * C [(b,t)] < C [] ∧ 2 * C [(c,t)] < C [] := by
  classical
  intro C start s y initial
  obtain ⟨rank,mono⟩ := OMA.R_wp_1_3_2_3_conjecture_R1.rank_exists P
  let candidates := Finset.univ.filter (fun i : P => s ≤ i ∧ ∃ j, start i j)
  have mem (i : P) : i ∈ candidates ↔ s ≤ i ∧ ∃ j, start i j := by simp [candidates]
  obtain ⟨i,hi,last⟩ := candidates.exists_max_image rank ⟨s,(mem s).2 ⟨le_rfl,y,initial⟩⟩
  obtain ⟨si,t,it,ti,pred,majority⟩ := (mem i).1 hi
  rcases majority_cover_alternative P i t it ti pred majority with cert | ⟨a,b,c,ia,ta,am,bc,fork⟩
  · exact Or.inl cert.1
  right
  obtain ⟨ab,tb,bm⟩ := fork b (by simp)
  obtain ⟨ac,tc,cm⟩ := fork c (by simp)
  have ai : ¬ a ≤ t := fun h => it (ia.trans h)
  have bi : ¬ b ≤ t := fun h => ai (ab.1.le.trans h)
  have ci : ¬ c ≤ t := fun h => ai (ac.1.le.trans h)
  have finish (b c : P) (ab : a ⋖ b) (ac : a ⋖ c) (bc : b ≠ c)

      (major : C [] ≤ 2 * C [(b,c)]) :
      ∃ d : P, d ⋖ c ∧ (¬ d ≤ a ∧ ¬ a ≤ d) ∧ (¬ d ≤ b ∧ ¬ b ≤ d) ∧ (¬ b ≤ c ∧ ¬ c ≤ b) := by
    have cross : ¬ b ≤ c ∧ ¬ c ≤ b :=
      ⟨fun h => ac.2 ab.1 (lt_of_le_of_ne h bc),fun h => ab.2 ac.1 (lt_of_le_of_ne h bc.symm)⟩
    have fails : ¬ ∀ z, z < c → z < b := by
      intro h
      have ib := lt_of_le_of_lt ia ab.1
      exact (mono ib).not_ge (last b ((mem b).2 ⟨si.trans ib.le,c,cross.1,cross.2,h,major⟩))
    push Not at fails
    obtain ⟨z,zc,zb⟩ := fails
    obtain ⟨d',dc',zd⟩ := next_cover_le Pᵒᵈ c z zc
    let d : P := OrderDual.ofDual d'
    have dc : d ⋖ c := ⟨dc'.1,fun k dk kc => dc'.2 kc dk⟩
    have db : ¬ d ≤ b := by
      intro le
      have ne : z ≠ b := fun h => cross.1 (h ▸ zc.le)
      exact zb (lt_of_le_of_ne (LE.le.trans (show z ≤ d from zd) le) ne)
    have da : ¬ d ≤ a := fun h => db (h.trans ab.1.le)
    exact ⟨d,dc,⟨da,fun h => ac.2 (lt_of_le_of_ne h (fun e => da e.ge)) dc.1⟩,
      ⟨db,fun h => cross.1 (h.trans dc.1.le)⟩,cross⟩
  have part : C [(b,c)] + C [(c,b)] = C [] :=
    (OMA.R_wp_1_3_2_3_conjecture_R1.comparison_counts P).2.2.1 [] b c bc
  by_cases h : C [] ≤ 2 * C [(b,c)]
  · obtain ⟨d,dc,da,db,incBC⟩ := finish b c ab ac bc h
    refine ⟨t,a,b,c,d,si.trans ia,ab,ac,dc,da,db,incBC,?_,h,am,bm,cm⟩
    simpa using And.intro (And.intro ta ai) (And.intro (And.intro tb bi) (And.intro tc ci))
  · have rev : C [] ≤ 2 * C [(c,b)] := by omega
    obtain ⟨d,db,da,dc,incCB⟩ := finish c b ac ab bc.symm rev
    refine ⟨t,a,c,b,d,si.trans ia,ac,ab,db,da,dc,incCB,?_,rev,am,cm,bm⟩
    simpa using And.intro (And.intro ta ai) (And.intro (And.intro tc ci) (And.intro tb bi))

-- An indecomposable finite nonchain has two distinct minimal elements.
-- Their majority orientation gives a start without probability hypotheses.
lemma minimal_majority_start (P : Type) [PartialOrder P] [Fintype P]
    (nonchain : ¬ ∀ x y : P, x ≤ y ∨ y ≤ x)
    (indecomp : ¬ ∃ L : Set P, L.Nonempty ∧ (∃ y, y ∉ L) ∧ ∀ x ∈ L, ∀ y ∉ L, x < y) :
    let C (l : List (P × P)) := Nat.card {r : P ≃ Fin (Fintype.card P) //
      (∀ a b : P, a < b → r a < r b) ∧ ∀ p ∈ l, r p.1 < r p.2}
    ∃ s y : P, (∀ z, ¬ z < s) ∧ (∀ z, ¬ z < y) ∧ ¬ s ≤ y ∧ ¬ y ≤ s ∧ C [] ≤ 2 * C [(s,y)] := by
  classical
  intro C
  obtain ⟨rank,mono⟩ := OMA.R_wp_1_3_2_3_conjecture_R1.rank_exists P
  have bottom (x : P) : ∃ m : P, m ≤ x ∧ ∀ z, ¬ z < m := by
    let lower := Finset.univ.filter (fun z : P => z ≤ x)
    have mem (z : P) : z ∈ lower ↔ z ≤ x := by simp [lower]
    obtain ⟨m,hm,least⟩ := lower.exists_min_image rank ⟨x,(mem x).2 le_rfl⟩
    have mx := (mem m).1 hm
    exact ⟨m,mx,fun z zm => (mono zm).not_ge (least z ((mem z).2 (zm.le.trans mx)))⟩
  push Not at nonchain
  obtain ⟨u,v,uv,vu⟩ := nonchain
  obtain ⟨m,mu,minM⟩ := bottom u
  have outside : ¬ ∀ z, m ≤ z := by
    intro least
    apply indecomp
    refine ⟨{m},⟨m,rfl⟩,⟨v,?_⟩,?_⟩
    · intro h
      exact vu ((Set.mem_singleton_iff.mp h) ▸ mu)
    · intro x hx y hy
      obtain rfl := Set.mem_singleton_iff.mp hx
      exact lt_of_le_of_ne (least y) (fun e => hy (Set.mem_singleton_iff.mpr e.symm))
  obtain ⟨w,mw⟩ := Classical.not_forall.mp outside
  obtain ⟨n,nw,minN⟩ := bottom w
  have mn : ¬ m ≤ n := fun h => mw (h.trans nw)
  have nm : ¬ n ≤ m := fun h => minM n (lt_of_le_of_ne h (fun e => mn e.ge))
  have sum : C [(m,n)] + C [(n,m)] = C [] :=
    (OMA.R_wp_1_3_2_3_conjecture_R1.comparison_counts P).2.2.1 [] m n (fun h => mn h.le)
  by_cases h : C [] ≤ 2 * C [(m,n)]
  · exact ⟨m,n,minM,minN,mn,nm,h⟩
  · exact ⟨n,m,minN,minM,nm,mn,by omega⟩

-- The interval between two neighbors of x stays in the incomparable neighborhood.
-- Choose the next cover by minimizing an extension rank in the finite interval.
lemma neighborhood_cover_chain (P : Type) [PartialOrder P] [Fintype P] (x a b c d : P)
    (ax : ¬ a ≤ x) (xd : ¬ x ≤ d) (ab : a < b) (bc : b < c) (cd : c < d) :
    ∃ i j k : P, (¬ x ≤ i ∧ ¬ i ≤ x) ∧ (¬ x ≤ j ∧ ¬ j ≤ x) ∧
      (¬ x ≤ k ∧ ¬ k ≤ x) ∧ a ⋖ i ∧ i ⋖ j ∧ j ⋖ k := by
  classical
  have inside (z : P) (az : a ≤ z) (zd : z ≤ d) : ¬ x ≤ z ∧ ¬ z ≤ x :=
    ⟨fun h => xd (h.trans zd),fun h => ax (az.trans h)⟩
  obtain ⟨i,ai,ib⟩ := next_cover_le P a b ab
  obtain ⟨j,ij,jc⟩ := next_cover_le P i c (lt_of_le_of_lt ib bc)
  obtain ⟨k,jk,kd⟩ := next_cover_le P j d (lt_of_le_of_lt jc cd)
  exact ⟨i,j,k,inside i ai.1.le (ib.trans (bc.trans cd).le),
    inside j (ai.1.trans ij.1).le (jc.trans cd.le),
    inside k ((ai.1.trans ij.1).trans jk.1).le kd,ai,ij,jk⟩

-- The two blocked swaps may live in different ranks. The cover still forces
-- different elements of the poset, and each supplies a surviving incomparable pair.
lemma cover_blockers (P : Type) [PartialOrder P] [Fintype P] (u x v : P) (uv : u ⋖ v) (uin : ¬ u ≤ x) (vin : ¬ x ≤ v)
    (r s : P ≃ Fin (Fintype.card P)) (mr : StrictMono r) (ms : StrictMono s) (z w : P)
    (uz : r u < r z) (zx : r z < r x) (xv : r x < r v)
    (ux : s u < s x) (xw : s x < s w) (wv : s w < s v)
    (left : u < z ∨ z < x) (right : x < w ∨ w < v) :
    let inc (a b : P) := ¬ a ≤ b ∧ ¬ b ≤ a
    z ≠ w ∧ ((u < z ∧ inc z v) ∨ (z < x ∧ inc z u)) ∧
      ((x < w ∧ inc w v) ∨ (w < v ∧ inc w u)) := by
  intro inc
  have zv := zx.trans xv
  have uw := ux.trans xw
  refine ⟨?_,?_,?_⟩
  · rintro rfl
    rcases left with h | h <;> rcases right with k | k
    · exact zx.not_gt (mr k)
    · exact uv.2 h k
    · exact h.asymm k
    · exact xw.not_gt (ms h)
  · rcases left with h | h
    · have ne : z ≠ v := fun e => zv.ne (congrArg r e)
      exact Or.inl ⟨h,fun le => uv.2 h (lt_of_le_of_ne le ne),
        fun le => zv.not_ge (mr.monotone le)⟩
    · refine Or.inr ⟨h,fun le => uz.not_ge (mr.monotone le),?_⟩
      intro le
      exact uin (le.trans h.le)
  · rcases right with h | h
    · refine Or.inl ⟨h,?_,fun le => wv.not_ge (ms.monotone le)⟩
      intro le
      exact vin (h.le.trans le)
    · have ne : u ≠ w := fun e => uw.ne (congrArg s e)
      exact Or.inr ⟨h,fun le => uw.not_ge (ms.monotone le),
        fun le => uv.2 (lt_of_le_of_ne le ne) h⟩

-- An interior crossing of both thresholds on a cover forces two different
-- surviving witnesses, even when the obstructions occur in different extensions.
lemma cover_jump_survivors (P : Type) [PartialOrder P] [Fintype P] :
    let C (l : List (P × P)) := Nat.card {r : P ≃ Fin (Fintype.card P) //
      (∀ a b : P, a < b → r a < r b) ∧ ∀ p ∈ l, r p.1 < r p.2}
    let inc (a b : P) := ¬ a ≤ b ∧ ¬ b ≤ a
    ∀ u x v : P, u ⋖ v → inc u x → inc x v →
      3 * C [(x,u)] < C [] → 2 * C [] < 3 * C [(x,v)] →
      ∃ z w : P, z ≠ x ∧ w ≠ x ∧ z ≠ w ∧
        ((u < z ∧ inc z v) ∨ (z < x ∧ inc z u)) ∧
        ((x < w ∧ inc w v) ∨ (w < v ∧ inc w u)) := by
  intro C inc u x v uv ui vi lo hi
  obtain ⟨_,_,split,_⟩ := OMA.R_wp_1_3_2_3_conjecture_R1.comparison_counts P
  have sum : C [(x,v)] + C [(v,x)] = C [] := split [] x v (fun e => vi.1 e.le)
  have gap : C [(x,u)] + C [(u,x),(x,v)] = C [(x,v)] := by
    exact insertion_count P x u v (fun e => ui.2 e.le) uv.1
  have l : C [(x,u)] < C [(u,x),(x,v)] := by omega
  have h : C [(v,x)] < C [(u,x),(x,v)] := by omega
  obtain ⟨r,z,mr,er,uz,zx,left⟩ := obstruction_of_count_excess P _ u x ui.1 (by simp) l
  obtain ⟨s,w,ms,es,xw,wv,right⟩ := obstruction_of_count_excess P _ x v vi.1 (by simp) h
  exact ⟨z,w,fun e => zx.ne (congrArg r e),fun e => xw.ne (congrArg s e.symm),
    cover_blockers P u x v uv ui.1 vi.1 r s mr ms z w uz zx (er (x,v) (by simp))
      (es (u,x) (by simp)) xw wv left right⟩

-- When the boundary straddles one half, either endpoint gives a named
-- candidate. A minimal x with all strict successors of u above v excludes
-- the left witness. The order-dual condition excludes the right witness.
lemma cover_crossing_balance (P : Type) [PartialOrder P] [Fintype P] :
    let C (l : List (P × P)) := Nat.card {r : P ≃ Fin (Fintype.card P) //
      (∀ a b : P, a < b → r a < r b) ∧ ∀ p ∈ l, r p.1 < r p.2}
    let inc (a b : P) := ¬ a ≤ b ∧ ¬ b ≤ a
    ∀ u x v : P, u ⋖ v → inc u x → inc x v →
      2 * C [(x,u)] ≤ C [] → C [] ≤ 2 * C [(x,v)] →
      (((∀ z, u < z → v ≤ z) ∧ (∀ z, z < x → z ≤ u)) ∨
       ((∀ z, z < v → z ≤ u) ∧ (∀ z, x < z → v ≤ z))) →
      ∃ y ∈ [u,v], C [] ≤ 3 * C [(x,y)] ∧ 3 * C [(x,y)] ≤ 2 * C [] := by
  intro C inc u x v uv ui vi lower upper confined
  by_cases lo : C [] ≤ 3 * C [(x,u)]
  · exact ⟨u,by simp,lo,by omega⟩
  by_cases hi : 3 * C [(x,v)] ≤ 2 * C []
  · exact ⟨v,by simp,by omega,hi⟩
  obtain ⟨z,w,_,_,_,left,right⟩ :=
    cover_jump_survivors P u x v uv ui vi (lt_of_not_ge lo) (lt_of_not_ge hi)
  exfalso
  rcases confined with ⟨up,down⟩ | ⟨down,up⟩
  · rcases left with ⟨uz,_,vz⟩ | ⟨zx,zu,_⟩
    · exact vz (up z uz)
    · exact zu (down z zx)
  · rcases right with ⟨xw,_,vw⟩ | ⟨wv,wu,_⟩
    · exact vw (up w xw)
    · exact wu (down w wv)

-- Delete x and close the gap in the ranks. The inverse operation skips slot k.
lemma insert_rank_bijection (P : Type) (x : P) (n : ℕ) :
    let Q := {y : P // y ≠ x}
    ∃ E : ((Q ≃ Fin n) × Fin (n+1)) ≃ (P ≃ Fin (n+1)),
      ∀ (r : Q ≃ Fin n) k, E (r,k) x = k ∧ ∀ a : Q, E (r,k) a.val = k.succAbove (r a) := by
  classical
  intro Q
  let ins (r : Q ≃ Fin n) (k : Fin (n+1)) :=
    (Equiv.optionSubtypeNe x).symm.trans (r.optionCongr.trans (finSuccEquiv' k).symm)
  have atX (r : Q ≃ Fin n) (k) : ins r k x = k := by simp [ins]
  have atQ (r : Q ≃ Fin n) (k) (a : Q) : ins r k a.val = k.succAbove (r a) := by
    simp [ins,Equiv.optionSubtypeNe_symm_of_ne a.property]
  let del (f : P ≃ Fin (n+1)) : Q ≃ Fin n :=
    (f.subtypeEquiv (fun y => (f.injective.ne_iff : f y ≠ f x ↔ y ≠ x).symm)).trans
      (finSuccAboveEquiv (f x)).symm
  have close (f : P ≃ Fin (n+1)) (a : Q) : (f x).succAbove (del f a) = f a :=
    congrArg Subtype.val ((finSuccAboveEquiv (f x)).apply_symm_apply ⟨f a,f.injective.ne a.property⟩)
  let insertAll (p : (Q ≃ Fin n) × Fin (n+1)) := ins p.1 p.2
  have inj : Function.Injective insertAll := by
    rintro ⟨r,k⟩ ⟨s,l⟩ h
    change ins r k = ins s l at h
    have kl : k = l := (atX r k).symm.trans ((DFunLike.congr_fun h x).trans (atX s l))
    subst l
    have rs : r = s := by
      apply Equiv.ext
      intro a
      apply (Fin.strictMono_succAbove k).injective
      exact (atQ r k a).symm.trans ((DFunLike.congr_fun h a.val).trans (atQ s k a))
    simp [rs]
  have onto : Function.Surjective insertAll := by
    intro f
    refine ⟨⟨del f,f x⟩,?_⟩
    apply Equiv.ext
    intro a
    by_cases h : a = x
    · subst a
      exact atX _ _
    · exact (atQ _ _ ⟨a,h⟩).trans (close f ⟨a,h⟩)
  exact ⟨Equiv.ofBijective insertAll ⟨inj,onto⟩,fun r k => ⟨atX r k, atQ r k⟩⟩

-- T tests comparisons among surviving elements. V tests which survivors
-- follow x and can therefore vary between slots of the same extension.
open scoped Classical in
lemma deletion_slot_count (P : Type) [PartialOrder P] [Fintype P] (x : P) :
    let Q := {y : P // y ≠ x}
    let n := Fintype.card Q
    let legal (r : Q ≃ Fin n) (k : Fin (n+1)) :=
      (∀ a : Q, a.val < x → (r a).val < k.val) ∧ (∀ a : Q, x < a.val → k.val ≤ (r a).val)
    ∀ (T : (Q → Q → Prop) → Prop) (V : (Q → Prop) → Prop),
      Nat.card {f : P ≃ Fin (Fintype.card P) // (StrictMono f ∧ T (fun a b => f a.val < f b.val)) ∧
        V (fun a => f x < f a.val)} =
      ∑ r : {r : Q ≃ Fin n // StrictMono r ∧ T (fun a b => r a < r b)},
        Nat.card {k : Fin (n+1) // legal r.val k ∧ V (fun a => k.val ≤ (r.val a).val)} := by
  classical
  intro Q n legal T V
  have size : Fintype.card P = n+1 := by
    simpa [n,Q] using (Fintype.card_congr (Equiv.optionSubtypeNe x)).symm
  obtain ⟨E,hE⟩ := insert_rank_bijection P x n
  let castRank := finCongr size.symm
  let F := E.trans (Equiv.equivCongr (Equiv.refl P) castRank)
  have compare (r : Q ≃ Fin n) (k : Fin (n+1)) (a b : P) :
      F (r,k) a < F (r,k) b ↔ E (r,k) a < E (r,k) b := Iff.rfl
  have rest (r : Q ≃ Fin n) (k) (a b : Q) :
      F (r,k) a.val < F (r,k) b.val ↔ r a < r b := by
    rw [compare,(hE r k).2 a,(hE r k).2 b,Fin.succAbove_lt_succAbove_iff]
  have pred (r : Q ≃ Fin n) (k) (a : Q) :
      F (r,k) a.val < F (r,k) x ↔ (r a).val < k.val := by
    rw [compare,(hE r k).1,(hE r k).2 a,Fin.succAbove_lt_iff_castSucc_lt]
    rfl
  have succ (r : Q ≃ Fin n) (k) (a : Q) :
      F (r,k) x < F (r,k) a.val ↔ k.val ≤ (r a).val := by
    rw [compare,(hE r k).1,(hE r k).2 a,Fin.lt_succAbove_iff_le_castSucc]
    rfl
  have mono (r : Q ≃ Fin n) (k) : StrictMono (F (r,k)) ↔ StrictMono r ∧ legal r k := by
    constructor
    · intro h
      exact ⟨fun {a b} ab => (rest r k a b).mp (h (show a.val < b.val from ab)),
        fun a ax => (pred r k a).mp (h ax), fun a xa => (succ r k a).mp (h xa)⟩
    · rintro ⟨h,hp,hs⟩ a b ab
      by_cases ax : a = x
      · subst a
        exact (succ r k ⟨b,ab.ne.symm⟩).mpr (hs _ ab)
      by_cases bx : b = x
      · subst b
        exact (pred r k ⟨a,ax⟩).mpr (hp _ ab)
      exact (rest r k ⟨a,ax⟩ ⟨b,bx⟩).mpr (h (show (⟨a,ax⟩ : Q) < ⟨b,bx⟩ from ab))
  let good (r : Q ≃ Fin n) := StrictMono r ∧ T (fun a b => r a < r b)
  let allowed (r : Q ≃ Fin n) (k : Fin (n+1)) := legal r k ∧ V (fun a => k.val ≤ (r a).val)
  let fibers := (r : {r : Q ≃ Fin n // good r}) × {k : Fin (n+1) // allowed r.val k}
  let packed := {p : (Q ≃ Fin n) × Fin (n+1) // good p.1 ∧ allowed p.1 p.2}
  let pack : fibers ≃ packed := {
    toFun := fun ⟨r,k⟩ => ⟨(r.val,k.val),r.property,k.property⟩
    invFun := fun p => ⟨⟨p.val.1,p.property.1⟩,⟨p.val.2,p.property.2⟩⟩
    left_inv := fun ⟨⟨_,_⟩,⟨_,_⟩⟩ => rfl
    right_inv := fun ⟨⟨_,_⟩,_⟩ => rfl }
  have test (p : (Q ≃ Fin n) × Fin (n+1)) :
      good p.1 ∧ allowed p.1 p.2 ↔ (StrictMono (F p) ∧ T (fun a b : Q => F p a.val < F p b.val)) ∧
        V (fun a : Q => F p x < F p a.val) := by
    obtain ⟨r,k⟩ := p
    have rel : (fun a b : Q => F (r,k) a.val < F (r,k) b.val) = (fun a b => r a < r b) :=
      funext fun a => funext fun b => propext (rest r k a b)
    have side : (fun a : Q => F (r,k) x < F (r,k) a.val) = (fun a => k.val ≤ (r a).val) :=
      funext fun a => propext (succ r k a)
    rw [rel,side,mono]
    exact ⟨fun ⟨⟨m,t⟩,s,v⟩ => ⟨⟨⟨m,s⟩,t⟩,v⟩,fun ⟨⟨⟨m,s⟩,t⟩,v⟩ => ⟨⟨m,t⟩,s,v⟩⟩
  exact (Nat.card_congr (pack.trans (F.subtypeEquiv test))).symm.trans Nat.card_sigma

open scoped Classical in
lemma deletion_event_count (P : Type) [PartialOrder P] [Fintype P] (x : P) :
    let Q := {y : P // y ≠ x}
    let n := Fintype.card Q
    let legal (r : Q ≃ Fin n) (k : Fin (n+1)) :=
      (∀ a : Q, a.val < x → (r a).val < k.val) ∧ (∀ a : Q, x < a.val → k.val ≤ (r a).val)
    ∀ T : (Q → Q → Prop) → Prop,
      Nat.card {f : P ≃ Fin (Fintype.card P) // StrictMono f ∧ T (fun a b => f a.val < f b.val)} =
      ∑ r : {r : Q ≃ Fin n // StrictMono r ∧ T (fun a b => r a < r b)},
        Nat.card {k : Fin (n+1) // legal r.val k} := by
  classical
  intro Q n legal T
  simpa only [and_true] using deletion_slot_count P x T (fun _ => True)

-- Insertion immediately after the last predecessor is always legal.
open scoped Classical in
lemma legal_slot_exists (P : Type) [PartialOrder P] [Fintype P] (x : P) :
    let Q := {y : P // y ≠ x}
    let n := Fintype.card Q
    ∀ r : Q ≃ Fin n, StrictMono r → ∃ k : Fin (n+1),
      (∀ a : Q, a.val < x → (r a).val < k.val) ∧ (∀ a : Q, x < a.val → k.val ≤ (r a).val) := by
  classical
  intro Q n r mono
  let pred := Finset.univ.filter (fun a : Q => a.val < x)
  by_cases h : pred.Nonempty
  · obtain ⟨a,ha,last⟩ := pred.exists_max_image (fun a => (r a).val) h
    refine ⟨(r a).succ,fun b hb => Nat.lt_succ_of_le (last _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hb⟩)),?_⟩
    intro b hb
    have ab : a.val < b.val := lt_trans (Finset.mem_filter.mp ha).2 hb
    exact mono (show a < b from ab)
  · refine ⟨0,fun a ha => ?_,fun _ _ => Nat.zero_le _⟩
    exact (h ⟨a,Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha⟩⟩).elim

open scoped Classical in
lemma deletion_event_lower (P : Type) [PartialOrder P] [Fintype P] (x : P) :
    let Q := {y : P // y ≠ x}
    ∀ T : (Q → Q → Prop) → Prop,
      Nat.card {r : Q ≃ Fin (Fintype.card Q) // StrictMono r ∧ T (fun a b => r a < r b)} ≤
        Nat.card {f : P ≃ Fin (Fintype.card P) // StrictMono f ∧ T (fun a b => f a.val < f b.val)} := by
  classical
  intro Q T
  rw [deletion_event_count P x T, ← Nat.card_sigma]
  let R := {r : Q ≃ Fin (Fintype.card Q) // StrictMono r ∧ T (fun a b => r a < r b)}
  have slot (r : R) := legal_slot_exists P x r.val r.property.1
  choose k hk using slot
  exact Nat.card_le_card_of_injective (fun r : R => ⟨r,⟨k r,hk r⟩⟩)
    (fun _ _ h => congrArg Sigma.fst h)

-- Apart from the last legal slot, a slot can be charged to the survivor
-- immediately after it. That survivor must be incomparable with x.
open scoped Classical in
lemma legal_slot_bound (P : Type) [PartialOrder P] [Fintype P] (x : P) :
    let Q := {y : P // y ≠ x}
    let n := Fintype.card Q
    ∀ r : Q ≃ Fin n,
      Nat.card {k : Fin (n+1) //
        (∀ a : Q, a.val < x → (r a).val < k.val) ∧ (∀ a : Q, x < a.val → k.val ≤ (r a).val)} ≤
        ({y : P | ¬ x ≤ y ∧ ¬ y ≤ x} : Set P).ncard + 1 := by
  classical
  intro Q n r
  let S := {k : Fin (n+1) //
    (∀ a : Q, a.val < x → (r a).val < k.val) ∧ (∀ a : Q, x < a.val → k.val ≤ (r a).val)}
  change Nat.card S ≤ _
  by_cases hn : Nonempty S
  · obtain ⟨m,_,last⟩ := Finset.univ.exists_max_image (fun k : S => k.val.val)
      ⟨hn.some,Finset.mem_univ _⟩
    let A := {k : S // k ≠ m}
    have before (k : A) : k.val.val.val < m.val.val := by
      apply lt_of_le_of_ne (last _ (Finset.mem_univ _))
      exact fun eq => k.property (Subtype.ext (Fin.ext eq))
    let idx (k : A) : Fin n := ⟨k.val.val.val, by have := before k; have := m.val.isLt; omega⟩
    let elt (k : A) : Q := r.symm (idx k)
    have pos (k : A) : (r (elt k)).val = k.val.val.val := by simp [elt,idx]
    let N := {y : P | ¬ x ≤ y ∧ ¬ y ≤ x}
    have inc (k : A) : (elt k).val ∈ N := by
      constructor
      · intro h
        have bound := m.property.2 (elt k) (lt_of_le_of_ne h (elt k).property.symm)
        rw [pos] at bound
        exact (before k).not_ge bound
      · intro h
        have bound := k.val.property.1 (elt k) (lt_of_le_of_ne h (elt k).property)
        rw [pos] at bound
        exact (lt_irrefl _ bound)
    let charge (k : A) : ↥N := ⟨(elt k).val, inc k⟩
    have inj : Function.Injective charge := by
      intro k l eq
      have e : elt k = elt l := Subtype.ext (congrArg (fun z : ↥N => z.val) eq)
      exact Subtype.ext (Subtype.ext (Fin.ext ((pos k).symm.trans ((congrArg (fun a => (r a).val) e).trans (pos l)))))
    have cap := Nat.card_le_card_of_injective charge inj
    have split : Nat.card S = Nat.card A + 1 := by
      simpa only [Nat.card_eq_fintype_card,Fintype.card_option] using
        (Nat.card_congr (Equiv.optionSubtypeNe m)).symm
    rw [split]
    exact Nat.add_le_add_right cap 1
  · have : IsEmpty S := not_nonempty_iff.mp hn
    simp

open scoped Classical in
lemma deletion_event_bound (P : Type) [PartialOrder P] [Fintype P] (x : P) :
    let Q := {y : P // y ≠ x}
    let d := ({y : P | ¬ x ≤ y ∧ ¬ y ≤ x} : Set P).ncard
    ∀ T : (Q → Q → Prop) → Prop,
      Nat.card {f : P ≃ Fin (Fintype.card P) // StrictMono f ∧ T (fun a b => f a.val < f b.val)} ≤
        (d+1) * Nat.card {r : Q ≃ Fin (Fintype.card Q) // StrictMono r ∧ T (fun a b => r a < r b)} := by
  classical
  intro Q d T
  rw [deletion_event_count P x T]
  have bounded {A : Type} (s : Finset A) (w : A → ℕ) (h : ∀ i, w i ≤ d+1) :
      ∑ i ∈ s, w i ≤ (d+1) * s.card := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.card_insert_of_notMem hi,Nat.mul_succ]
      exact (Nat.add_le_add (h i) ih).trans_eq (Nat.add_comm _ _)
  simpa only [Finset.card_univ,Nat.card_eq_fintype_card] using
    bounded (Finset.univ : Finset {r : Q ≃ Fin (Fintype.card Q) // StrictMono r ∧ T (fun a b => r a < r b)})
      (fun r => Nat.card {k : Fin (Fintype.card Q+1) //
        (∀ a : Q, a.val < x → (r.val a).val < k.val) ∧ (∀ a : Q, x < a.val → k.val ≤ (r.val a).val)})
      (fun r => legal_slot_bound P x r.val)

-- Bound each restored orientation by charging its deleted extensions at
-- most d+1 times. A bound on the larger deleted row controls both tails.
open scoped Classical in
lemma deletion_balance_transfer (P : Type) [PartialOrder P] [Fintype P] (x : P) :
    let Q := {y : P // y ≠ x}
    let C (A : Type) [PartialOrder A] [Fintype A] (l : List (A × A)) :=
      Nat.card {f : A ≃ Fin (Fintype.card A) // (∀ u v, u < v → f u < f v) ∧ ∀ p ∈ l, f p.1 < f p.2}
    let d := ({y : P | ¬ x ≤ y ∧ ¬ y ≤ x} : Set P).ncard
    ∀ a b : Q, a ≠ b →
      (3 * ((d+1) * max (C Q [(a,b)]) (C Q [(b,a)])) ≤ 2 * C P [] ∨
       C P [] ≤ 3 * min (C Q [(a,b)]) (C Q [(b,a)])) →
      C P [] ≤ 3 * C P [(a.val,b.val)] ∧ 3 * C P [(a.val,b.val)] ≤ 2 * C P [] := by
  classical
  intro Q C d a b ne mass
  have ident (A : Type) [PartialOrder A] [Fintype A] (s t : A) :
        C A [(s,t)] = Nat.card {r : A ≃ Fin (Fintype.card A) // StrictMono r ∧ r s < r t} := by
    dsimp only [C]
    apply Nat.card_congr (Equiv.subtypeEquivRight ?_)
    intro r
    simp [StrictMono]
  have bound (u v : Q) : C P [(u.val,v.val)] ≤ (d+1) * C Q [(u,v)] := by
    rw [ident P,ident Q]
    exact deletion_event_bound P x (fun rel => rel u v)
  have lower (u v : Q) : C Q [(u,v)] ≤ C P [(u.val,v.val)] := by
    rw [ident P,ident Q]
    exact deletion_event_lower P x (fun rel => rel u v)
  have full : C P [(a.val,b.val)] + C P [(b.val,a.val)] = C P [] :=
    (OMA.R_wp_1_3_2_3_conjecture_R1.comparison_counts P).2.2.1 [] a.val b.val (fun e => ne (Subtype.ext e))
  rcases mass with high | low
  · have up := (bound a b).trans (Nat.mul_le_mul_left (d+1) (le_max_left (C Q [(a,b)]) (C Q [(b,a)])))
    have down := (bound b a).trans (Nat.mul_le_mul_left (d+1) (le_max_right (C Q [(a,b)]) (C Q [(b,a)])))
    constructor <;> omega
  · have up := lower a b
    have down := lower b a
    have left := min_le_left (C Q [(a,b)]) (C Q [(b,a)])
    have right := min_le_right (C Q [(a,b)]) (C Q [(b,a)])
    constructor <;> omega

-- A tied comparison on deletion survives as a balanced comparison if the
-- average fiber size is at least three quarters of the maximum slot bound.
open scoped Classical in
lemma tied_deletion_bounds (P : Type) [PartialOrder P] [Fintype P] (x : P) :
    let Q := {y : P // y ≠ x}
    let C (A : Type) [PartialOrder A] [Fintype A] (l : List (A × A)) :=
      Nat.card {f : A ≃ Fin (Fintype.card A) // (∀ u v, u < v → f u < f v) ∧ ∀ p ∈ l, f p.1 < f p.2}
    let d := ({y : P | ¬ x ≤ y ∧ ¬ y ≤ x} : Set P).ncard
    ∀ a b : Q, a ≠ b → 2 * C Q [(a,b)] = C Q [] →
      3 * (d+1) * C Q [] ≤ 4 * C P [] →
      C P [] ≤ 3 * C P [(a.val,b.val)] ∧ 3 * C P [(a.val,b.val)] ≤ 2 * C P [] := by
  classical
  intro Q C d a b ne tie mass
  have del : C Q [(a,b)] + C Q [(b,a)] = C Q [] :=
    (OMA.R_wp_1_3_2_3_conjecture_R1.comparison_counts Q).2.2.1 [] a b ne
  have both : C Q [(b,a)] = C Q [(a,b)] := by omega
  apply deletion_balance_transfer P x a b ne
  left
  change 3 * ((d+1) * max (C Q [(a,b)]) (C Q [(b,a)])) ≤ 2 * C P []
  rw [both,max_self]
  rw [← tie] at mass
  rw [show 3 * (d+1) * (2 * C Q [(a,b)]) = 2 * (3 * ((d+1) * C Q [(a,b)])) by ac_rfl] at mass
  omega

open scoped Classical in
lemma degree_seven_tie_transfer (P : Type) [PartialOrder P] [Fintype P] (x : P) :
    let Q := {y : P // y ≠ x}
    let C (A : Type) [PartialOrder A] [Fintype A] (l : List (A × A)) :=
      Nat.card {f : A ≃ Fin (Fintype.card A) // (∀ u v, u < v → f u < f v) ∧ ∀ p ∈ l, f p.1 < f p.2}
    let d := ({y : P | ¬ x ≤ y ∧ ¬ y ≤ x} : Set P).ncard
    d = 7 → ∀ a b : Q, a ≠ b → 2 * C Q [(a,b)] = C Q [] →
      6 * C Q [] ≤ C P [] →
      C P [] ≤ 3 * C P [(a.val,b.val)] ∧ 3 * C P [(a.val,b.val)] ≤ 2 * C P [] := by
  classical
  intro Q C d seven a b ne tie average
  apply tied_deletion_bounds P x a b ne tie
  change 3 * (d+1) * C Q [] ≤ 4 * C P []
  rw [seven]
  omega

-- With no exclusive successor of a and one exclusive predecessor z of b,
-- swap a and z from the first cell into the second, then swap a and b
-- from the second cell into the reverse orientation.
lemma one_predecessor_bound (P : Type) [PartialOrder P] [Fintype P] :
    let C (l : List (P × P)) := Nat.card {r : P ≃ Fin (Fintype.card P) //
      (∀ a b : P, a < b → r a < r b) ∧ ∀ p ∈ l, r p.1 < r p.2}
    ∀ a b : P, ¬ a ≤ b → (∀ k, a < k → b < k) →
      (∀ k, k < b → ¬ k < a → ∀ t, t < b → ¬ t < a → k = t) →
      C [(a,b)] ≤ 2 * C [(b,a)] := by
  classical
  intro C a b ab upper unique
  by_cases ex : ∃ z, z < b ∧ ¬ z < a
  · obtain ⟨z,zb,za⟩ := ex
    have az : ¬ a ≤ z := fun h => ab (h.trans zb.le)
    have ne : a ≠ z := fun e => az e.le
    have bn : b ≠ a := fun e => ab e.ge
    have lower (k : P) (kb : k < b) : k < a ∨ k = z :=
      or_iff_not_imp_left.mpr (fun miss => unique k kb miss z zb za)
    have first : C [(a,b),(a,z)] ≤ C [(a,b),(z,a)] := by
      apply swap_cell_bound P _ _ a z az (by simp)
      intro r mono extra
      have before := extra (a,z) (by simp)
      refine ⟨fun k h => mono (lt_trans zb (upper k h)), ?_, ?_⟩
      · intro k kz
        exact mono ((lower k (kz.trans zb)).resolve_right kz.ne)
      · intro p hp
        have cases : p = (a,b) ∨ p = (z,a) := by simpa using hp
        rcases cases with rfl | rfl
        · simpa [Equiv.swap_apply_of_ne_of_ne bn zb.ne.symm] using mono zb
        · simpa using before
    have second : C [(a,b),(z,a)] ≤ C [(b,a)] := by
      apply swap_cell_bound P _ _ a b ab (by simp)
      intro r mono extra
      refine ⟨fun k h => mono (upper k h), ?_, ?_⟩
      · intro k kb
        rcases lower k kb with h | rfl
        · exact mono h
        · exact extra (k,a) (by simp)
      · intro p hp
        obtain rfl : p = (b,a) := by simpa using hp
        simpa using extra (a,b) (by simp)
    have split : C [(a,b),(a,z)] + C [(a,b),(z,a)] = C [(a,b)] :=
      (OMA.R_wp_1_3_2_3_conjecture_R1.comparison_counts P).2.2.1 [(a,b)] a z ne
    omega
  · have bound : C [(a,b)] ≤ C [(b,a)] := by
      apply OMA.R_wp_1_3_2_3_conjecture_R1.exchange_count_le P a b _ ab
        (fun k kb => by_contra (fun miss => ex ⟨k,kb,miss⟩))
      exact fun r mono extra => ⟨extra (a,b) (by simp),fun k h => mono (upper k h)⟩
    omega

-- A majority exceeding two thirds requires at least two distinct elements
-- that obstruct exchanging the given pair in that direction.
lemma one_defect_bound (P : Type) [PartialOrder P] [Fintype P] :
    let C (l : List (P × P)) := Nat.card {r : P ≃ Fin (Fintype.card P) //
      (∀ a b : P, a < b → r a < r b) ∧ ∀ p ∈ l, r p.1 < r p.2}
    ∀ a b : P, ¬ a ≤ b →
      ({z : P | (z < b ∧ ¬ z < a) ∨ (a < z ∧ ¬ b < z)} : Set P).ncard ≤ 1 →
      3 * C [(a,b)] ≤ 2 * C [] := by
  classical
  intro C a b ab small
  let S := Finset.univ.filter (fun z : P => (z < b ∧ ¬ z < a) ∨ (a < z ∧ ¬ b < z))
  have size : S.card ≤ 1 := by simpa [S,← Set.ncard_coe_finset] using small
  have same := Finset.card_le_one.mp size
  have mem (z : P) : z ∈ S ↔ (z < b ∧ ¬ z < a) ∨ (a < z ∧ ¬ b < z) := by simp [S]
  have bound : C [(a,b)] ≤ 2 * C [(b,a)] := by
    by_cases h : ∀ k, a < k → b < k
    · apply one_predecessor_bound P a b ab h
      exact fun k kb ka t tb ta => same k ((mem k).2 (Or.inl ⟨kb,ka⟩)) t ((mem t).2 (Or.inl ⟨tb,ta⟩))
    · push Not at h
      obtain ⟨k,ak,bk⟩ := h
      have pred (u : P) (ub : u < b) : u < a := by
        by_contra ua
        have eq := same u ((mem u).2 (Or.inl ⟨ub,ua⟩)) k ((mem k).2 (Or.inr ⟨ak,bk⟩))
        exact ab ((ak.trans (eq ▸ ub)).le)
      have dual := one_predecessor_bound Pᵒᵈ b a ab pred
        (fun k ak bk t at' bt => same k ((mem k).2 (Or.inr ⟨ak,bk⟩)) t ((mem t).2 (Or.inr ⟨at',bt⟩)))
      let D (l : List (Pᵒᵈ × Pᵒᵈ)) := Nat.card {r : Pᵒᵈ ≃ Fin (Fintype.card Pᵒᵈ) //
        (∀ a b : Pᵒᵈ, a < b → r a < r b) ∧ ∀ p ∈ l, r p.1 < r p.2}
      have rev (u v : P) : D [(v,u)] = C [(u,v)] :=
        OMA.R_wp_1_3_2_3_conjecture_R1.dual_comparison_counts P [(v,u)]
      exact (rev a b).symm.trans_le (dual.trans_eq (congrArg (2 * ·) (rev b a)))
  have split : C [(a,b)] + C [(b,a)] = C [] :=
    (OMA.R_wp_1_3_2_3_conjecture_R1.comparison_counts P).2.2.1 [] a b (fun e => ab e.le)
  omega

-- Apply the directional bound twice to certify the named pair itself.
lemma two_sided_defect_balance (P : Type) [PartialOrder P] [Fintype P] :
    let C (l : List (P × P)) := Nat.card {r : P ≃ Fin (Fintype.card P) //
      (∀ a b : P, a < b → r a < r b) ∧ ∀ p ∈ l, r p.1 < r p.2}
    let defects (a b : P) := {z : P | (z < b ∧ ¬ z < a) ∨ (a < z ∧ ¬ b < z)}
    ∀ a b : P, ¬ a ≤ b → ¬ b ≤ a → (defects a b).ncard ≤ 1 → (defects b a).ncard ≤ 1 →
      C [] ≤ 3 * C [(a,b)] ∧ 3 * C [(a,b)] ≤ 2 * C [] := by
  intro C defects a b ab ba forward reverse
  have lo : 3 * C [(b,a)] ≤ 2 * C [] := one_defect_bound P b a ba reverse
  have split : C [(a,b)] + C [(b,a)] = C [] :=
    (OMA.R_wp_1_3_2_3_conjecture_R1.comparison_counts P).2.2.1 [] a b (fun e => ab e.le)
  exact ⟨by omega,one_defect_bound P a b ab forward⟩

-- In particular a pair of twins exposed by deleting x is balanced after x
-- is restored. Only x can belong to either set of exceptional elements.
-- See also Zaguia, arXiv:1610.00809, Theorem 3, on good pairs.
lemma deletion_twins_balance (P : Type) [PartialOrder P] [Fintype P] :
    let C (l : List (P × P)) := Nat.card {r : P ≃ Fin (Fintype.card P) //
      (∀ a b : P, a < b → r a < r b) ∧ ∀ p ∈ l, r p.1 < r p.2}
    ∀ x a b : P, a ≠ x → b ≠ x → a ≠ b →
      (∀ k, k ≠ x → (k < a ↔ k < b) ∧ (a < k ↔ b < k)) →
      C [] ≤ 3 * C [(a,b)] ∧ 3 * C [(a,b)] ≤ 2 * C [] := by
  classical
  intro C x a b ax bx ne twins
  have small (u v : P) (h : ∀ k, k ≠ x → (k < u ↔ k < v) ∧ (u < k ↔ v < k)) :
      ({k : P | (k < v ∧ ¬ k < u) ∨ (u < k ∧ ¬ v < k)} : Set P).ncard ≤ 1 := by
    have sub : {k : P | (k < v ∧ ¬ k < u) ∨ (u < k ∧ ¬ v < k)} ⊆ ({x} : Set P) := by
      intro k hk
      by_contra miss
      have kx : k ≠ x := fun e => miss (Set.mem_singleton_iff.mpr e)
      rcases hk with ⟨kv,ku⟩ | ⟨uk,vk⟩
      · exact ku ((h k kx).1.mpr kv)
      · exact vk ((h k kx).2.mp uk)
    simpa only [Set.ncard_singleton] using Set.ncard_le_ncard sub
  apply two_sided_defect_balance P a b
  · exact fun le => lt_irrefl a ((twins a ax).1.mpr (lt_of_le_of_ne le ne))
  · exact fun le => lt_irrefl b ((twins b bx).1.mp (lt_of_le_of_ne le ne.symm))
  · exact small a b twins
  · exact small b a (fun k kx => ⟨(twins k kx).1.symm,(twins k kx).2.symm⟩)

theorem main : H1 → H2 → OMA.R_wp_1_3_2_3_conjecture_R1.H2 := by
  classical
  intro chainCase antichainCase P _ _ nonchain indecomp rigid three wide up down noGold
  obtain ⟨x, hx⟩ := wide
  let N := {y : P | ¬ x ≤ y ∧ ¬ y ≤ x}
  let Q := {y : P // y ≠ x}
  let C (A : Type) [PartialOrder A] [Fintype A] (l : List (A × A)) :=
      Nat.card {f : A ≃ Fin (Fintype.card A) // (∀ u v, u < v → f u < f v) ∧ ∀ p ∈ l, f p.1 < f p.2}
  have forks :
    let fork (r c : P → P → Prop) := ∃ x y, x ≠ y ∧ (∀ z, c z x ↔ c z y) ∧
      ∀ z ∈ [x,y], IsChain r {a | r z a}
    ¬ fork (· ≤ ·) (· ⋖ ·) ∧ ¬ fork (· ≥ ·) (fun a b => b ⋖ a) := by
    constructor
    · rintro ⟨u,v,ne,cover,chains⟩
      apply up ⟨u,v,ne,cover,?_,?_⟩
      · intro a b ha hb
        by_cases e : a = b
        · exact Or.inl e.le
        · exact chains u (by simp) ha hb e
      · intro a b ha hb
        by_cases e : a = b
        · exact Or.inl e.le
        · exact chains v (by simp) ha hb e
    · rintro ⟨u,v,ne,cover,chains⟩
      apply down ⟨u,v,ne,cover,?_,?_⟩
      · intro a b ha hb
        by_cases e : a = b
        · exact Or.inl e.le
        · exact (chains u (by simp) ha hb e).symm
      · intro a b ha hb
        by_cases e : a = b
        · exact Or.inl e.le
        · exact (chains v (by simp) ha hb e).symm
  have barrier : ∀ a b : P, ¬ a ≤ b → 2 * C P [] < 3 * C P [(a,b)] →
      2 ≤ ({z : P | (z < b ∧ ¬ z < a) ∨ (a < z ∧ ¬ b < z)} : Set P).ncard := by
    intro a b ab heavy
    by_contra! small
    exact (not_le_of_gt heavy) (one_defect_bound P a b ab (by omega))
  by_contra noPair
  have obstruction (a b : Q) (ne : a ≠ b) :
      2 * C P [] < 3 * ((N.ncard+1) * max (C Q [(a,b)]) (C Q [(b,a)])) ∧
        3 * min (C Q [(a,b)]) (C Q [(b,a)]) < C P [] := by
    by_contra fail
    have mass : 3 * ((N.ncard+1) * max (C Q [(a,b)]) (C Q [(b,a)])) ≤ 2 * C P [] ∨
        C P [] ≤ 3 * min (C Q [(a,b)]) (C Q [(b,a)]) := by omega
    obtain ⟨lo,hi⟩ := deletion_balance_transfer P x a b ne mass
    apply noPair
    apply pair_of_count_bounds P a.val b.val (fun eq => ne (Subtype.ext eq))
    · exact lo
    · exact hi
  apply noPair
  by_cases chain : ∃ a ∈ N, ∃ b ∈ N, ∃ c ∈ N, ∃ d ∈ N, a < b ∧ b < c ∧ c < d
  · obtain ⟨a, ha, b₀, _, c₀, _, d₀, hd₀, ab₀, bc₀, cd₀⟩ := chain
    obtain ⟨b,c,d,hb,hc,hd,ab,bc,cd⟩ :=
      neighborhood_cover_chain P x a b₀ c₀ d₀ ha.2 hd₀.1 ab₀ bc₀ cd₀
    have ne (y : P) (hy : y ∈ N) : x ≠ y := fun h => hy.1 h.le
    rcases four_chain_slots P x a b c d (ne a ha) (ne b hb) (ne c hc) (ne d hd)
      ab.1 bc.1 cd.1 with ok | gap
    · obtain ⟨y, hy, lo, hi⟩ := ok
      have yn : y ∈ N := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl | rfl | rfl <;> assumption
      exact pair_of_count_bounds P x y (ne y yn) lo hi
    · refine chainCase P nonchain indecomp rigid three
        ⟨x, hx, obstruction, a, ha, b, hb, c, hc, d, hd, ab, bc, cd, gap⟩ ?_ barrier
        noGold
      have force (A : Type) [PartialOrder A] [Fintype A]
          (nc : ¬ ∀ u v : A, u ≤ v ∨ v ≤ u)
          (ind : ¬ ∃ L : Set A, L.Nonempty ∧ (∃ y, y ∉ L) ∧ ∀ x ∈ L, ∀ y ∉ L, x < y)
          (ng : ¬ ∃ i j k l : A, i ≠ j ∧ k ≠ l ∧ ∀ p ∈ [(i,j),(j,i)],
            ∀ q ∈ [(k,l),(l,k)], C A [p] + C A [p,q] ≤ C A [])
          (absent : ∀ i j : A, i ≠ j → ¬ (C A [] ≤ 3 * C A [(i,j)] ∧ 3 * C A [(i,j)] ≤ 2 * C A [])) :
          ∃ t a b c d : A, a ⋖ b ∧ a ⋖ c ∧ d ⋖ c ∧
            (¬ d ≤ a ∧ ¬ a ≤ d) ∧ (¬ d ≤ b ∧ ¬ b ≤ d) ∧ (¬ b ≤ c ∧ ¬ c ≤ b) ∧
            (∀ z ∈ [a,b,c], ¬ t ≤ z ∧ ¬ z ≤ t) ∧ 2 * C A [] < 3 * C A [(b,c)] ∧
            2 * C A [] < 3 * C A [(a,t)] ∧ 3 * C A [(b,t)] < C A [] ∧ 3 * C A [(c,t)] < C A [] := by
        obtain ⟨s,y,_,my,sy,ys,majority⟩ := minimal_majority_start A nc ind
        rcases terminal_majority_covers A s y ⟨sy,ys,fun z zy => (my z zy).elim,majority⟩
          with cert | ⟨t,a,b,c,d,_,ab,ac,dc,da,db,bc,inc,order,am,bm,cm⟩
        · exact (ng cert).elim
        · have heavy (u v : A) (ne : u ≠ v) (h : C A [] ≤ 2 * C A [(u,v)]) :
              2 * C A [] < 3 * C A [(u,v)] := by
            have fail := absent u v ne
            omega
          have light (u v : A) (ne : u ≠ v) (h : 2 * C A [(u,v)] < C A []) :
              3 * C A [(u,v)] < C A [] := by
            have fail := absent u v ne
            omega
          have ne (u : A) (hu : u ∈ [a,b,c]) : u ≠ t := fun e => (inc u hu).2 e.le
          exact ⟨t,a,b,c,d,ab,ac,dc,da,db,bc,inc,heavy _ _ (fun e => bc.1 e.le) order,
            heavy _ _ (ne a (by simp)) am,light _ _ (ne b (by simp)) bm,light _ _ (ne c (by simp)) cm⟩
      have absent (u v : P) (ne : u ≠ v) :
          ¬ (C P [] ≤ 3 * C P [(u,v)] ∧ 3 * C P [(u,v)] ≤ 2 * C P []) :=
        fun h => noPair (pair_of_count_bounds P u v ne h.1 h.2)
      refine ⟨force P nonchain indecomp noGold absent,force Pᵒᵈ ?_ ?_ ?_ ?_⟩
      · exact fun h => nonchain (fun u v => h v u)
      · rintro ⟨L,⟨i,hi⟩,⟨j,hj⟩,cut⟩
        apply indecomp
        refine ⟨{v : P | v ∉ L},⟨j,hj⟩,⟨i,fun h => h hi⟩,?_⟩
        intro u hu v hv
        exact cut v (Classical.byContradiction hv) u hu
      · exact fun h => noGold (OMA.R_wp_1_3_2_3_conjecture_R1.gold_of_dual P h)
      · intro u v ne h
        have cell : C Pᵒᵈ [(u,v)] = C P [(v,u)] :=
          OMA.R_wp_1_3_2_3_conjecture_R1.dual_comparison_counts P [(u,v)]
        have total : C Pᵒᵈ [] = C P [] :=
          OMA.R_wp_1_3_2_3_conjecture_R1.dual_comparison_counts P []
        rw [cell,total] at h
        exact absent v u ne.symm h
  · obtain ⟨t, xt, anti, bound⟩ := antichain_through_vertex P x chain
    have four : 4 ≤ t.card := by omega
    exact antichainCase P nonchain indecomp rigid ⟨x, hx, obstruction, chain, t, xt, anti, four, bound⟩ forks barrier
      noGold

end OMA.R_wp_1_3_2_3_conjecture_R1_H2_R1
