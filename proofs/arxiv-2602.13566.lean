import OMAStatements.S_arxiv_2602_13566

namespace OMA.PatternStability

noncomputable def partner {I : Type} (r : I → I → Prop) (i : I) : I := by
  classical
  exact if h : ∃ j, r i j then Classical.choose h else i

theorem partner_eq {I : Type} {r : I → I → Prop}
    (unique : ∀ i j k, r i j → r i k → j = k) {i j : I} (h : r i j) :
    partner r i = j := by
  classical
  unfold partner
  rw [dif_pos (show ∃ k, r i k from ⟨j, h⟩)]
  exact unique _ _ _ (Classical.choose_spec _) h

theorem partner_none {I : Type} {r : I → I → Prop} {i : I}
    (h : ¬ ∃ j, r i j) : partner r i = i := by
  classical
  simp [partner, h]

theorem partner_inv {I : Type} {r : I → I → Prop}
    (unique : ∀ i j k, r i j → r i k → j = k)
    (symmetric : ∀ i j, r i j → r j i) :
    Function.Involutive (partner r) := by
  intro i
  by_cases existsMate : ∃ j, r i j
  · obtain ⟨j, edge⟩ := existsMate
    rw [partner_eq unique edge, partner_eq unique (symmetric _ _ edge)]
  · rw [partner_none existsMate, partner_none existsMate]

noncomputable def pairing {I : Type} {r : I → I → Prop}
    (unique : ∀ i j k, r i j → r i k → j = k)
    (symmetric : ∀ i j, r i j → r j i) : Equiv.Perm I :=
  ⟨partner r, partner r, partner_inv unique symmetric, partner_inv unique symmetric⟩

def Paired {I : Type} (edges : I → I → Prop) (w : I → ℕ) (a : ℕ) (i j : I) : Prop :=
  (edges i j ∧ w i = a ∧ w j = a+1) ∨ (edges j i ∧ w j = a ∧ w i = a+1)

theorem paired_symm {I : Type} (edges : I → I → Prop) (w : I → ℕ) (a : ℕ) :
    ∀ i j, Paired edges w a i j → Paired edges w a j i := by
  intro i j h
  exact h.elim Or.inr Or.inl

theorem paired_unique {I : Type} (edges : I → I → Prop)
    (next : ∀ i j k, edges i j → edges i k → j = k)
    (last : ∀ i j k, edges j i → edges k i → j = k)
    (w : I → ℕ) (a : ℕ) : ∀ i j k, Paired edges w a i j → Paired edges w a i k → j = k := by
  intro i j k hj hk
  rcases hj with ⟨outJ, hij, _⟩ | ⟨inJ, _, hij⟩ <;>
    rcases hk with ⟨outK, hik, _⟩ | ⟨inK, _, hik⟩
  · exact next i j k outJ outK
  · omega
  · omega
  · exact last i j k inJ inK

noncomputable def paint {I : Type} (edges : I → I → Prop) (a : ℕ) (w : I → ℕ) (i : I) : ℕ :=
  Equiv.swap a (a+1) (w (partner (Paired edges w a) i))

theorem paint_matched {I : Type} {edges : I → I → Prop}
    (next : ∀ i j k, edges i j → edges i k → j = k)
    (last : ∀ i j k, edges j i → edges k i → j = k)
    {w : I → ℕ} {a : ℕ} {i j : I}
    (h : Paired edges w a i j) :
    paint edges a w i = w i := by
  unfold paint
  rw [partner_eq (paired_unique edges next last w a) h]
  rcases h with ⟨_, left, right⟩ | ⟨_, left, right⟩ <;> simp [left, right]

theorem paint_choice {I : Type} {edges : I → I → Prop}
    (next : ∀ i j k, edges i j → edges i k → j = k)
    (last : ∀ i j k, edges j i → edges k i → j = k)
    (w : I → ℕ) (a : ℕ) (i : I) :
    paint edges a w i = w i ∨ paint edges a w i = Equiv.swap a (a+1) (w i) := by
  by_cases mate : ∃ j, Paired edges w a i j
  · obtain ⟨j, hj⟩ := mate
    exact Or.inl (paint_matched next last hj)
  · exact Or.inr (by simp [paint, partner_none mate])

private theorem color_mono (a u v u' v' : ℕ)
    (h : u < v) (noPair : ¬ (u = a ∧ v = a+1))
    (hu : u' = u ∨ u' = Equiv.swap a (a+1) u)
    (hv : v' = v ∨ v' = Equiv.swap a (a+1) v) : u' < v' := by
  rw [Equiv.swap_apply_def] at hu hv
  split_ifs at hu hv <;> omega

theorem paint_valid {I : Type} {edges : I → I → Prop}
    (next : ∀ i j k, edges i j → edges i k → j = k)
    (last : ∀ i j k, edges j i → edges k i → j = k)
    {w : I → ℕ} (a : ℕ) (valid : ∀ i j, edges i j → w i < w j) :
    ∀ i j, edges i j → paint edges a w i < paint edges a w j := by
  intro i j edge
  by_cases both : w i = a ∧ w j = a+1
  · have pair : Paired edges w a i j := Or.inl ⟨edge, both.1, both.2⟩
    rw [paint_matched next last pair, paint_matched next last (paired_symm edges w a i j pair)]
    exact valid i j edge
  · exact color_mono a (w i) (w j) _ _ (valid i j edge) both
      (paint_choice next last w a i) (paint_choice next last w a j)

private theorem before_colored (a old fresh : ℕ)
    (choice : fresh = old ∨ fresh = Equiv.swap a (a+1) old)
    (after : fresh = a ∨ fresh = a+1) : old = a ∨ old = a+1 := by
  rw [Equiv.swap_apply_def] at choice
  split_ifs at choice <;> omega

private theorem old_pair {I : Type} {edges : I → I → Prop}
    (next : ∀ i j k, edges i j → edges i k → j = k)
    (last : ∀ i j k, edges j i → edges k i → j = k)
    {w : I → ℕ} {a : ℕ} (valid : ∀ i j, edges i j → w i < w j)
    {i j : I} (edge : edges i j) (low : paint edges a w i = a)
    (high : paint edges a w j = a+1) : w i = a ∧ w j = a+1 := by
  have ki := before_colored a _ _ (paint_choice next last w a i) (Or.inl low)
  have kj := before_colored a _ _ (paint_choice next last w a j) (Or.inr high)
  have ordered := valid i j edge
  omega

theorem paint_pairs {I : Type} {edges : I → I → Prop}
    (next : ∀ i j k, edges i j → edges i k → j = k)
    (last : ∀ i j k, edges j i → edges k i → j = k)
    {w : I → ℕ} (a : ℕ) (valid : ∀ i j, edges i j → w i < w j) :
    Paired edges (paint edges a w) a = Paired edges w a := by
  funext i j
  apply propext
  constructor
  · rintro (⟨edge, low, high⟩ | ⟨edge, low, high⟩)
    · exact Or.inl ⟨edge, old_pair next last valid edge low high⟩
    · exact Or.inr ⟨edge, old_pair next last valid edge low high⟩
  · intro h
    have li := paint_matched next last h
    have lj := paint_matched next last (paired_symm edges w a i j h)
    unfold Paired at h ⊢
    rwa [li, lj]

theorem paint_twice {I : Type} {edges : I → I → Prop}
    (next : ∀ i j k, edges i j → edges i k → j = k)
    (last : ∀ i j k, edges j i → edges k i → j = k)
    {w : I → ℕ} (a : ℕ) (valid : ∀ i j, edges i j → w i < w j) :
    paint edges a (paint edges a w) = w := by
  funext i
  change Equiv.swap a (a+1) (paint edges a w (partner (Paired edges (paint edges a w) a) i)) = w i
  rw [paint_pairs next last a valid]
  change Equiv.swap a (a+1) (Equiv.swap a (a+1)
    (w (partner (Paired edges w a) (partner (Paired edges w a) i)))) = w i
  rw [partner_inv (paired_unique edges next last w a) (paired_symm edges w a) i]
  simp

end OMA.PatternStability

namespace OMA.PatternStability

def ascending (w : ℕ → ℕ) (j : ℕ) : Prop :=
  w j < w (j+1) ∧ w (j+1) < w (j+2) ∧ w (j+2) < w (j+3) ∧ w (j+3) < w (j+4)

def crooked (w : ℕ → ℕ) (j : ℕ) : Prop :=
  w j < w (j+1) ∧ w (j+1) < w (j+3) ∧ w (j+3) < w (j+2) ∧ w (j+2) < w (j+4)

def Separated (S : Finset ℕ) : Prop :=
  ∀ j ∈ S, ∀ k ∈ S, j < k → j+3 ≤ k

theorem crooked_separated (w : ℕ → ℕ) (S : Finset ℕ)
    (marked : ∀ j ∈ S, crooked w j) : Separated S := by
  intro j hj k hk hlt
  by_contra! close
  have step : k = j+1 ∨ k = j+2 := by omega
  have rev := (marked j hj).2.2.1
  have order := marked k hk
  rcases step with rfl | rfl
  · have a : w (j+2) < w (j+4) := order.2.1
    have b : w (j+4) < w (j+3) := order.2.2.1
    omega
  · have a : w (j+2) < w (j+3) := order.1
    omega

private theorem same_near {S : Finset ℕ} (sep : Separated S) {a b : ℕ}
    (ha : a ∈ S) (hb : b ∈ S) (left : a < b+3) (right : b < a+3) : a = b := by
  rcases lt_trichotomy a b with h | h | h
  · have lower := sep a ha b hb h
    omega
  · exact h
  · have lower := sep b hb a ha h
    omega

def Slots {n : ℕ} (S : Finset ℕ) (i k : Fin n) : Prop :=
  ∃ j ∈ S, (i.val = j+2 ∧ k.val = j+3) ∨ (i.val = j+3 ∧ k.val = j+2)

theorem slots_symm {n : ℕ} (S : Finset ℕ) :
    ∀ i k : Fin n, Slots S i k → Slots S k i := by
  intro i k h
  obtain ⟨j, hj, orientation⟩ := h
  rcases orientation with ⟨hi, hk⟩ | ⟨hi, hk⟩
  · exact ⟨j, hj, Or.inr ⟨hk, hi⟩⟩
  · exact ⟨j, hj, Or.inl ⟨hk, hi⟩⟩

theorem slots_unique {n : ℕ} {S : Finset ℕ} (sep : Separated S) :
    ∀ i j k : Fin n, Slots S i j → Slots S i k → j = k := by
  intro i j k hj hk
  obtain ⟨a, ha, left⟩ := hj
  obtain ⟨b, hb, right⟩ := hk
  apply Fin.ext
  rcases left with ⟨iA, jA⟩ | ⟨iA, jA⟩ <;>
    rcases right with ⟨iB, kB⟩ | ⟨iB, kB⟩
  · omega
  · have eq := same_near sep ha hb (by omega) (by omega)
    omega
  · have eq := same_near sep ha hb (by omega) (by omega)
    omega
  · omega

def readAt {n : ℕ} (w : Fin n → ℕ) (i : ℕ) : ℕ :=
  if h : i < n then w ⟨i, h⟩ else 0

noncomputable def twist {n : ℕ} (S : Finset ℕ) (w : Fin n → ℕ) (i : Fin n) : ℕ :=
  w (partner (Slots S) i)

theorem twist_twice {n : ℕ} {S : Finset ℕ} (sep : Separated S) (w : Fin n → ℕ) :
    twist S (twist S w) = w := by
  funext i
  change w (partner (Slots S) (partner (Slots S) i)) = w i
  rw [partner_inv (slots_unique sep) (slots_symm S) i]

private theorem fixed_slot {n : ℕ} {S : Finset ℕ} {w : Fin n → ℕ} {i : ℕ}
    (hi : i < n) (free : ¬ ∃ k : Fin n, Slots S ⟨i, hi⟩ k) :
    readAt (twist S w) i = readAt w i := by
  simp [readAt, hi, twist, partner_none free]

private theorem moved_slot {n : ℕ} {S : Finset ℕ} {w : Fin n → ℕ} {i k : ℕ}
    (sep : Separated S) (hi : i < n) (hk : k < n) (pair : Slots S ⟨i, hi⟩ ⟨k, hk⟩) :
    readAt (twist S w) i = readAt w k := by
  simp [readAt, hi, hk, twist, partner_eq (slots_unique sep) pair]

private theorem no_offset {n : ℕ} {S : Finset ℕ} {i : ℕ} (hi : i < n)
    (avoid : ∀ s ∈ S, i ≠ s+2 ∧ i ≠ s+3) :
    ¬ ∃ k : Fin n, Slots S ⟨i, hi⟩ k := by
  rintro ⟨k, s, hs, h⟩
  rcases h with ⟨he, _⟩ | ⟨he, _⟩
  · exact (avoid s hs).1 he
  · exact (avoid s hs).2 he

theorem twist_slots {n : ℕ} {S : Finset ℕ} {w : Fin n → ℕ} {j : ℕ}
    (sep : Separated S) (mark : j ∈ S) (bound : j+4 < n) :
    (readAt (twist S w) j = readAt w j ∨
      ∃ k ∈ S, k+3 = j ∧ readAt (twist S w) j = readAt w (j-1)) ∧
    readAt (twist S w) (j+1) = readAt w (j+1) ∧
    readAt (twist S w) (j+2) = readAt w (j+3) ∧
    readAt (twist S w) (j+3) = readAt w (j+2) ∧
    readAt (twist S w) (j+4) = readAt w (j+4) := by
  have chk : ∀ k ∈ S, k < j+3 → j < k+3 → k = j := fun k hk l r =>
    same_near sep hk mark l r
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · by_cases prev : ∃ k ∈ S, k+3=j
    · obtain ⟨k, hk, position⟩ := prev
      apply Or.inr
      refine ⟨k, hk, position, ?_⟩
      exact moved_slot sep (by omega) (by omega)
        ⟨k, hk, Or.inr ⟨position.symm, by change j-1 = k+2; omega⟩⟩
    · apply Or.inl
      apply fixed_slot (by omega)
      apply no_offset
      intro k hk
      constructor
      · intro eq
        have equal := chk k hk (by omega) (by omega)
        omega
      · exact fun eq => prev ⟨k, hk, eq.symm⟩
  · apply fixed_slot (by omega)
    apply no_offset
    intro k hk
    constructor <;> intro eq
    · have equal := chk k hk (by omega) (by omega)
      omega
    · have equal := chk k hk (by omega) (by omega)
      omega
  · exact moved_slot sep (by omega) (by omega) ⟨j, mark, Or.inl ⟨rfl, rfl⟩⟩
  · exact moved_slot sep (by omega) (by omega) ⟨j, mark, Or.inr ⟨rfl, rfl⟩⟩
  · apply fixed_slot bound
    apply no_offset
    intro k hk
    constructor <;> intro eq
    · have equal := chk k hk (by omega) (by omega)
      omega
    · have equal := chk k hk (by omega) (by omega)
      omega

theorem twist_crooked {n : ℕ} {S : Finset ℕ} {w : Fin n → ℕ}
    (sep : Separated S) (within : ∀ j ∈ S, j+4 < n)
    (marks : ∀ j ∈ S, crooked (readAt w) j) :
    ∀ j ∈ S, ascending (readAt (twist S w)) j := by
  intro j hj
  obtain ⟨first, e1, e2, e3, e4⟩ := twist_slots (w := w) sep hj (within j hj)
  unfold ascending
  rw [e1, e2, e3, e4]
  refine ⟨?_, (marks j hj).2⟩
  rcases first with kept | ⟨k, hk, before, moved⟩
  · rw [kept]
    exact (marks j hj).1
  · rw [moved, show j-1 = k+2 by omega, show j+1 = k+4 by omega]
    exact (marks k hk).2.2.2

theorem twist_ascending {n : ℕ} {S : Finset ℕ} {w : Fin n → ℕ}
    (sep : Separated S) (within : ∀ j ∈ S, j+4 < n)
    (marks : ∀ j ∈ S, ascending (readAt w) j) :
    ∀ j ∈ S, crooked (readAt (twist S w)) j := by
  intro j hj
  obtain ⟨first, e1, e2, e3, e4⟩ := twist_slots (w := w) sep hj (within j hj)
  unfold crooked
  rw [e1, e2, e3, e4]
  refine ⟨?_, (marks j hj).2⟩
  rcases first with kept | ⟨k, hk, before, moved⟩
  · rw [kept]
    exact (marks j hj).1
  · rw [moved, show j-1 = k+2 by omega, show j+1 = k+4 by omega]
    exact lt_trans (marks k hk).2.2.1 (marks k hk).2.2.2

end OMA.PatternStability

namespace OMA.PatternStability

def Covered {n : ℕ} (S : Finset ℕ) (i j : Fin n) : Prop :=
  j.val = i.val+1 ∧ ∃ s ∈ S, s ≤ i.val ∧ i.val < s+4

theorem covered_next {n : ℕ} (S : Finset ℕ) :
    ∀ i j k : Fin n, Covered S i j → Covered S i k → j = k := by
  intro i j k h₁ h₂
  exact Fin.ext (h₁.1.trans h₂.1.symm)

theorem covered_last {n : ℕ} (S : Finset ℕ) :
    ∀ i j k : Fin n, Covered S j i → Covered S k i → j = k := by
  intro i j k h₁ h₂
  apply Fin.ext
  have a := h₁.1
  have b := h₂.1
  omega

theorem ascending_edges {n : ℕ} {S : Finset ℕ} {w : Fin n → ℕ}
    (within : ∀ s ∈ S, s+4 < n) :
    (∀ s ∈ S, ascending (readAt w) s) ↔ ∀ i j, Covered S i j → w i < w j := by
  constructor
  · intro asc i j edge
    obtain ⟨consecutive, s, hs, lower, upper⟩ := edge
    have index : i.val = s ∨ i.val = s+1 ∨ i.val = s+2 ∨ i.val = s+3 := by omega
    have localOrder := asc s hs
    have target : readAt w i.val < readAt w (i.val+1) := by
      rcases index with eq | eq | eq | eq
      · rw [eq]
        exact localOrder.1
      · rw [eq]
        exact localOrder.2.1
      · rw [eq]
        exact localOrder.2.2.1
      · rw [eq]
        exact localOrder.2.2.2
    rw [← consecutive] at target
    simpa [readAt, i.isLt, j.isLt] using target
  · intro order s hs
    have step (k : ℕ) (lower : s ≤ k) (upper : k < s+4) :
        readAt w k < readAt w (k+1) := by
      have bound := within s hs
      have kLt : k < n := by omega
      have nextLt : k+1 < n := by omega
      simpa [readAt, kLt, nextLt] using
        order ⟨k, kLt⟩ ⟨k+1, nextLt⟩ ⟨rfl, s, hs, lower, upper⟩
    exact ⟨step s le_rfl (by omega), step (s+1) (by omega) (by omega),
      step (s+2) (by omega) (by omega), step (s+3) (by omega) (by omega)⟩

noncomputable def recolor {n : ℕ} (S : Finset ℕ) (a : ℕ) (w : Fin n → ℕ) : Fin n → ℕ :=
  twist S (paint (Covered S) a (twist S w))

theorem recolor_valid {n : ℕ} {S : Finset ℕ} {w : Fin n → ℕ}
    (sep : Separated S) (within : ∀ j ∈ S, j+4 < n)
    (a : ℕ) (marks : ∀ j ∈ S, crooked (readAt w) j) :
    ∀ j ∈ S, crooked (readAt (recolor S a w)) j := by
  have order := (ascending_edges within).mp (twist_crooked sep within marks)
  have after := paint_valid (covered_next S) (covered_last S) a order
  exact twist_ascending sep within ((ascending_edges within).mpr after)

theorem recolor_twice {n : ℕ} {S : Finset ℕ} {w : Fin n → ℕ}
    (sep : Separated S) (within : ∀ j ∈ S, j+4 < n)
    (a : ℕ) (marks : ∀ j ∈ S, crooked (readAt w) j) :
    recolor S a (recolor S a w) = w := by
  have order := (ascending_edges within).mp (twist_crooked sep within marks)
  unfold recolor
  rw [twist_twice sep, paint_twice (covered_next S) (covered_last S) a order, twist_twice sep]

theorem twist_perm {n : ℕ} {S : Finset ℕ} (sep : Separated S) (w : Fin n → ℕ) :
    (List.ofFn (twist S w)).Perm (List.ofFn w) := by
  exact (pairing (slots_unique sep) (slots_symm S)).ofFn_comp_perm w

theorem paint_perm {n : ℕ} (S : Finset ℕ) (a : ℕ) (w : Fin n → ℕ) :
    (List.ofFn (paint (Covered S) a w)).Perm ((List.ofFn w).map (Equiv.swap a (a+1))) := by
  rw [List.map_ofFn]
  exact (pairing (paired_unique (Covered S) (covered_next S) (covered_last S) w a)
    (paired_symm (Covered S) w a)).ofFn_comp_perm (Equiv.swap a (a+1) ∘ w)

theorem recolor_perm {n : ℕ} {S : Finset ℕ} (sep : Separated S) (a : ℕ) (w : Fin n → ℕ) :
    (List.ofFn (recolor S a w)).Perm ((List.ofFn w).map (Equiv.swap a (a+1))) := by
  exact ((twist_perm sep _).trans (paint_perm S a (twist S w))).trans
    ((twist_perm sep w).map (Equiv.swap a (a+1)))

end OMA.PatternStability

namespace OMA.PatternStability

theorem coarsen {α ι : Type} [DecidableEq ι]
    (A : Finset α) (f : α → Finset ι) (P : Finset ι)
    (within : ∀ a ∈ A, f a ⊆ P) (Q : Finset ι → Prop) [DecidablePred Q] :
    (A.filter fun a => Q (f a)).card =
      ∑ T ∈ P.powerset.filter Q, (A.filter fun a => f a = T).card := by
  have maps : Set.MapsTo f (↑(A.filter fun a => Q (f a))) (↑(P.powerset.filter Q)) := by
    intro a ha
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset] at ha ⊢
    exact ⟨within a ha.1, ha.2⟩
  rw [Finset.card_eq_sum_card_fiberwise maps]
  apply Finset.sum_congr rfl
  intro T ht
  have good := (Finset.mem_filter.mp ht).2
  congr 1
  ext a
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨⟨ha, _⟩, eq⟩
    exact ⟨ha, eq⟩
  · rintro ⟨ha, eq⟩
    exact ⟨⟨ha, eq.symm ▸ good⟩, eq⟩

theorem exactCard {α ι : Type} [DecidableEq ι]
    (A B : Finset α) (f g : α → Finset ι) (P : Finset ι)
    (fWithin : ∀ a ∈ A, f a ⊆ P) (gWithin : ∀ b ∈ B, g b ⊆ P)
    (marked : ∀ S : Finset ι,
      (A.filter fun a => S ⊆ f a).card = (B.filter fun b => S ⊆ g b).card) :
    ∀ S ⊆ P, (A.filter fun a => f a = S).card = (B.filter fun b => g b = S).card := by
  classical
  let onA (T : Finset ι) := (A.filter fun a => f a = T).card
  let onB (T : Finset ι) := (B.filter fun b => g b = T).card
  have aux : ∀ d (S : Finset ι), S ⊆ P → P.card - S.card = d → onA S = onB S := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro S contained hd
      let U := P.powerset.filter fun T => S ⊆ T
      have inU : S ∈ U := Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr contained, le_rfl⟩
      have totalA : (A.filter fun a => S ⊆ f a).card = ∑ T ∈ U, onA T :=
        coarsen A f P fWithin (S ⊆ ·)
      have totalB : (B.filter fun b => S ⊆ g b).card = ∑ T ∈ U, onB T :=
        coarsen B g P gWithin (S ⊆ ·)
      have remaining : (∑ T ∈ U.erase S, onA T) = ∑ T ∈ U.erase S, onB T := by
        apply Finset.sum_congr rfl
        intro T hT
        obtain ⟨different, member⟩ := Finset.mem_erase.mp hT
        obtain ⟨subP, contains⟩ := Finset.mem_filter.mp member
        have inside := Finset.mem_powerset.mp subP
        have bigger : S.card < T.card := Finset.card_lt_card
          (Finset.ssubset_iff_subset_ne.mpr ⟨contains, Ne.symm different⟩)
        have bounded := Finset.card_le_card inside
        exact ih (P.card - T.card) (by omega) T inside rfl
      have splitA := Finset.sum_erase_add U onA inU
      have splitB := Finset.sum_erase_add U onB inU
      have equal := marked S
      rw [totalA, totalB] at equal
      omega
  intro S hS
  exact aux (P.card - S.card) S hS rfl

theorem cardinalityClass {α ι : Type} [DecidableEq ι]
    (A B : Finset α) (f g : α → Finset ι) (P : Finset ι)
    (fWithin : ∀ a ∈ A, f a ⊆ P) (gWithin : ∀ b ∈ B, g b ⊆ P)
    (marked : ∀ S : Finset ι,
      (A.filter fun a => S ⊆ f a).card = (B.filter fun b => S ⊆ g b).card)
    (count : ℕ) :
    (A.filter fun a => (f a).card = count).card =
      (B.filter fun b => (g b).card = count).card := by
  rw [coarsen A f P fWithin (fun T => T.card = count),
    coarsen B g P gWithin (fun T => T.card = count)]
  apply Finset.sum_congr rfl
  intro T hT
  exact exactCard A B f g P fWithin gWithin marked T
    (Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1)

end OMA.PatternStability

namespace OMA.PatternStability

private def spread (base : ℕ) : List ℕ → List ℕ
  | [] => []
  | c :: rest => List.replicate c base ++ spread (base+1) rest

private theorem spread_idx (base : ℕ) (k : List ℕ) :
    spread base k = (k.mapIdx fun i c => List.replicate c (base+i)).flatten := by
  induction k generalizing base with
  | nil => rfl
  | cons x rest ih =>
    rw [spread, ih (base+1), List.mapIdx_cons, List.flatten_cons, Nat.add_zero]
    congr 1
    have indexFn : (fun i : ℕ => fun c : ℕ => List.replicate c (base+1+i)) =
        (fun i : ℕ => fun c : ℕ => List.replicate c (base+(i+1))) := by
      funext i c
      rw [show base+1+i = base+(i+1) by omega]
    rw [indexFn]

private theorem fixed_spread (a base : ℕ) (above : a+1 < base) (k : List ℕ) :
    (spread base k).map (Equiv.swap a (a+1)) = spread base k := by
  induction k generalizing base with
  | nil => rfl
  | cons c rest ih =>
    simp only [spread, List.map_append, List.map_replicate]
    rw [Equiv.swap_apply_of_ne_of_ne (by omega : base ≠ a) (by omega : base ≠ a+1),
      ih (base+1) (by omega)]

private theorem spread_recolor (before : List ℕ) (base aCount bCount : ℕ) (after : List ℕ) :
    ((spread base (before ++ aCount :: bCount :: after)).map
      (Equiv.swap (base+before.length) (base+before.length+1))).Perm
        (spread base (before ++ bCount :: aCount :: after)) := by
  induction before generalizing base with
  | nil =>
    simp only [List.nil_append, List.length_nil, Nat.add_zero, spread, List.map_append,
      List.map_replicate, Equiv.swap_apply_left, Equiv.swap_apply_right]
    rw [fixed_spread base (base+1+1) (by omega) after]
    have exchange : (List.replicate aCount (base+1) ++ List.replicate bCount base).Perm
        (List.replicate bCount base ++ List.replicate aCount (base+1)) := List.perm_append_comm
    simpa only [List.append_assoc] using exchange.append_right (spread (base+1+1) after)
  | cons x rest ih =>
    simp only [List.cons_append, List.length_cons, spread, List.map_append, List.map_replicate]
    rw [Equiv.swap_apply_of_ne_of_ne (by omega : base ≠ base+(rest.length+1))
      (by omega : base ≠ base+(rest.length+1)+1),
      show base+(rest.length+1) = base+1+rest.length by omega]
    exact (ih (base+1)).append_left (List.replicate x base)

private def wordsSet (k : List ℕ) : Finset (List ℕ) :=
  (OMA.S_arxiv_2602_13566.words k).toFinset

private theorem words_membership (k w : List ℕ) :
    w ∈ wordsSet k ↔ w.Perm (spread 0 k) := by
  rw [spread_idx]
  simp [wordsSet, OMA.S_arxiv_2602_13566.words, List.mem_permutations]

private theorem word_length {k w : List ℕ} (member : w ∈ wordsSet k) :
    w.length = (spread 0 k).length :=
  ((words_membership k w).mp member).length_eq

private theorem adjacent_length (before : List ℕ) (a b : ℕ) (after : List ℕ) :
    (spread 0 (before ++ a :: b :: after)).length =
      (spread 0 (before ++ b :: a :: after)).length := by
  simpa using (spread_recolor before 0 a b after).length_eq

private theorem getD_inside {w : List ℕ} {i : ℕ} (bound : i < w.length) :
    w.getD i 0 = w[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem bound]
  rfl

private def indexed (n : ℕ) (w : List ℕ) (i : Fin n) : ℕ :=
  w.getD i.val 0

private theorem indexed_ofFn {n : ℕ} (values : Fin n → ℕ) :
    indexed n (List.ofFn values) = values := by
  funext i
  unfold indexed
  rw [getD_inside (by simp [i.isLt]), List.getElem_ofFn]

private theorem collect_indexed {n : ℕ} {w : List ℕ} (hlen : w.length = n) :
    List.ofFn (indexed n w) = w := by
  subst n
  have eq : indexed w.length w = w.get := by
    funext i
    exact getD_inside i.isLt
  rw [eq, List.ofFn_get]

private theorem indexed_read {n : ℕ} {w : List ℕ} (h : w.length = n)
    (i : ℕ) : readAt (indexed n w) i = w.getD i 0 := by
  unfold readAt indexed
  split
  · rfl
  · rename_i outside
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl

end OMA.PatternStability

namespace OMA.PatternStability

private def testPattern : List ℕ := [0, 1, 3, 2, 4]

private theorem window_iff (w : List ℕ) (j : ℕ) :
    (let f := (w.drop j).take testPattern.length
     f.length = testPattern.length ∧
      ∀ a < testPattern.length, ∀ b < testPattern.length,
        (f.getD a 0 < f.getD b 0 ↔ testPattern.getD a 0 < testPattern.getD b 0)) ↔
    j+4 < w.length ∧ crooked (fun i => w.getD i 0) j := by
  let f := (w.drop j).take 5
  have len : f.length = 5 ↔ j+4 < w.length := by
    simp only [f, List.length_take, List.length_drop]
    omega
  have point (bound : j+4 < w.length) (i : ℕ) (ok : i < 5) :
      f.getD i 0 = w.getD (j+i) 0 := by
    have inside : i < f.length := by have h := len.mpr bound; omega
    have atWord : j+i < w.length := by omega
    rw [getD_inside inside, getD_inside atWord]
    simp [f]
  change (f.length = 5 ∧
    ∀ a < 5, ∀ b < 5, (f.getD a 0 < f.getD b 0 ↔
      testPattern.getD a 0 < testPattern.getD b 0)) ↔ _
  constructor
  · rintro ⟨h, order⟩
    have bound := len.mp h
    have q₀ := (order 0 (by decide) 1 (by decide)).mpr (by decide)
    have q₁ := (order 1 (by decide) 3 (by decide)).mpr (by decide)
    have q₂ := (order 3 (by decide) 2 (by decide)).mpr (by decide)
    have q₃ := (order 2 (by decide) 4 (by decide)).mpr (by decide)
    rw [point bound 0 (by decide), Nat.add_zero, point bound 1 (by decide)] at q₀
    rw [point bound 1 (by decide), point bound 3 (by decide)] at q₁
    rw [point bound 3 (by decide), point bound 2 (by decide)] at q₂
    rw [point bound 2 (by decide), point bound 4 (by decide)] at q₃
    exact ⟨bound, q₀, q₁, q₂, q₃⟩
  · rintro ⟨bound, h₀, h₁, h₂, h₃⟩
    simp only [List.getD_eq_getElem?_getD] at h₀ h₁ h₂ h₃
    refine ⟨len.mpr bound, ?_⟩
    intro a ha b hb
    rw [point bound a ha, point bound b hb]
    interval_cases a <;> interval_cases b <;>
      simp [testPattern, List.getD] <;> omega

private noncomputable def positions (w : List ℕ) : Finset ℕ := by
  classical
  exact (Finset.range w.length).filter fun j =>
    j+4 < w.length ∧ crooked (fun i => w.getD i 0) j

private theorem mem_positions (w : List ℕ) (j : ℕ) :
    j ∈ positions w ↔ j+4 < w.length ∧ crooked (fun i => w.getD i 0) j := by
  classical
  simp only [positions, Finset.mem_filter, Finset.mem_range]
  exact ⟨fun h => h.2, fun h => ⟨by have upper := h.1; omega, h⟩⟩

private theorem occurrences_eq (w : List ℕ) :
    OMA.S_arxiv_2602_13566.occurrences testPattern w = (positions w).card := by
  unfold OMA.S_arxiv_2602_13566.occurrences
  rw [← List.toFinset_card_of_nodup (List.Nodup.sublist List.filter_sublist List.nodup_range)]
  congr 1
  ext j
  simp only [List.mem_toFinset, List.mem_filter, List.mem_range, decide_eq_true_eq, window_iff,
    mem_positions]
  exact ⟨fun h => h.2, fun h => ⟨by have upper := h.1; omega, h⟩⟩

private theorem count_eq (k : List ℕ) (count : ℕ) :
    OMA.S_arxiv_2602_13566.count testPattern k count =
      ((wordsSet k).filter fun w => (positions w).card = count).card := by
  classical
  have distinct : (OMA.S_arxiv_2602_13566.words k).Nodup := by
    unfold OMA.S_arxiv_2602_13566.words
    exact List.nodup_dedup _
  unfold OMA.S_arxiv_2602_13566.count
  rw [← List.toFinset_card_of_nodup (List.Nodup.sublist List.filter_sublist distinct)]
  congr 1
  ext w
  simp [wordsSet, occurrences_eq]

end OMA.PatternStability

namespace OMA.PatternStability

private theorem indexed_marks {n : ℕ} {S : Finset ℕ} {w : List ℕ}
    (length : w.length = n) (marks : S ⊆ positions w) :
    ∀ j ∈ S, crooked (readAt (indexed n w)) j := by
  intro j hj
  simpa only [crooked, indexed_read length] using ((mem_positions w j).mp (marks hj)).2

private noncomputable def changeWord (n : ℕ) (S : Finset ℕ) (a : ℕ) (w : List ℕ) : List ℕ :=
  List.ofFn (recolor S a (indexed n w))

private theorem changed_marks {n : ℕ} {S : Finset ℕ} {w : List ℕ}
    (length : w.length = n) (marks : S ⊆ positions w)
    (within : ∀ j ∈ S, j+4 < n) (sep : Separated S) (a : ℕ) :
    S ⊆ positions (changeWord n S a w) := by
  intro j hj
  have newLength : (changeWord n S a w).length = n := by simp [changeWord]
  have newRead (i : ℕ) :
      (changeWord n S a w).getD i 0 = readAt (recolor S a (indexed n w)) i := by
    rw [← indexed_read newLength i, changeWord, indexed_ofFn]
  apply (mem_positions _ j).mpr
  refine ⟨by rw [newLength]; exact within j hj, ?_⟩
  simpa only [crooked, newRead] using
    recolor_valid sep within a (indexed_marks length marks) j hj

private theorem change_twice {n : ℕ} {S : Finset ℕ} {w : List ℕ}
    (length : w.length = n) (marks : S ⊆ positions w)
    (within : ∀ j ∈ S, j+4 < n) (sep : Separated S) (a : ℕ) :
    changeWord n S a (changeWord n S a w) = w := by
  unfold changeWord
  rw [indexed_ofFn, recolor_twice sep within a (indexed_marks length marks)]
  exact collect_indexed length

private theorem changed_letters (before : List ℕ) (x y : ℕ) (after : List ℕ)
    {n : ℕ} {S : Finset ℕ} {w : List ℕ}
    (length : w.length = n) (sep : Separated S)
    (member : w ∈ wordsSet (before ++ x :: y :: after)) :
    changeWord n S before.length w ∈ wordsSet (before ++ y :: x :: after) := by
  have swapped := recolor_perm sep before.length (indexed n w)
  rw [collect_indexed length] at swapped
  have listed := ((words_membership _ _).mp member).map
    (Equiv.swap before.length (before.length+1))
  have arrangement := spread_recolor before 0 x y after
  simp only [Nat.zero_add] at arrangement
  exact (words_membership _ _).mpr (swapped.trans (listed.trans arrangement))

private theorem marked_shape {n : ℕ} {S : Finset ℕ} {w : List ℕ}
    (length : w.length = n) (marks : S ⊆ positions w) :
    (∀ j ∈ S, j+4 < n) ∧ Separated S := by
  refine ⟨?_, crooked_separated (fun i => w.getD i 0) S ?_⟩
  · intro j hj
    rw [← length]
    exact ((mem_positions w j).mp (marks hj)).1
  · intro j hj
    exact ((mem_positions w j).mp (marks hj)).2

private noncomputable def markedWords (k : List ℕ) (S : Finset ℕ) : Finset (List ℕ) := by
  classical
  exact (wordsSet k).filter fun w => S ⊆ positions w

private theorem mem_markedWords {k : List ℕ} {S : Finset ℕ} {w : List ℕ} :
    w ∈ markedWords k S ↔ w ∈ wordsSet k ∧ S ⊆ positions w := by
  classical
  exact Finset.mem_filter

private theorem adjacent_marked (before : List ℕ) (x y : ℕ) (after : List ℕ) (S : Finset ℕ) :
    (markedWords (before ++ x :: y :: after) S).card =
      (markedWords (before ++ y :: x :: after) S).card := by
  classical
  let left := before ++ x :: y :: after
  let right := before ++ y :: x :: after
  let n := (spread 0 left).length
  have leftLen {w : List ℕ} (h : w ∈ wordsSet left) : w.length = n := word_length h
  have rightLen {w : List ℕ} (h : w ∈ wordsSet right) : w.length = n :=
    (word_length h).trans (adjacent_length before x y after).symm
  change (markedWords left S).card = (markedWords right S).card
  by_cases h : (∀ j ∈ S, j+4 < n) ∧ Separated S
  · let move := changeWord n S before.length
    refine Finset.card_bij' (fun w _ => move w) (fun w _ => move w) ?_ ?_ ?_ ?_
    · intro w hw
      obtain ⟨mem, marks⟩ := mem_markedWords.mp hw
      exact mem_markedWords.mpr
        ⟨changed_letters before x y after (leftLen mem) h.2 mem,
         changed_marks (leftLen mem) marks h.1 h.2 before.length⟩
    · intro w hw
      obtain ⟨mem, marks⟩ := mem_markedWords.mp hw
      exact mem_markedWords.mpr
        ⟨changed_letters before y x after (rightLen mem) h.2 mem,
         changed_marks (rightLen mem) marks h.1 h.2 before.length⟩
    · intro w hw
      obtain ⟨mem, marks⟩ := mem_markedWords.mp hw
      exact change_twice (leftLen mem) marks h.1 h.2 before.length
    · intro w hw
      obtain ⟨mem, marks⟩ := mem_markedWords.mp hw
      exact change_twice (rightLen mem) marks h.1 h.2 before.length
  · have emptyLeft : markedWords left S = ∅ := by
      ext w
      simp only [mem_markedWords, Finset.notMem_empty, iff_false]
      rintro ⟨mem, marks⟩
      exact h (marked_shape (leftLen mem) marks)
    have emptyRight : markedWords right S = ∅ := by
      ext w
      simp only [mem_markedWords, Finset.notMem_empty, iff_false]
      rintro ⟨mem, marks⟩
      exact h (marked_shape (rightLen mem) marks)
    rw [emptyLeft, emptyRight]

private theorem perm_marked {k k' : List ℕ} (perm : k.Perm k') :
    ∀ (before : List ℕ) (S : Finset ℕ),
      (markedWords (before ++ k) S).card = (markedWords (before ++ k') S).card := by
  induction perm with
  | nil =>
    intro before S
    rfl
  | cons x _ ih =>
    intro before S
    simpa only [List.append_assoc, List.singleton_append] using ih (before ++ [x]) S
  | swap x y after =>
    intro before S
    exact adjacent_marked before y x after S
  | trans _ _ ih₁ ih₂ =>
    intro before S
    exact (ih₁ before S).trans (ih₂ before S)

private theorem stable_test : OMA.S_arxiv_2602_13566.Stable testPattern := by
  classical
  intro k k' perm count
  rw [count_eq, count_eq]
  let length := max (spread 0 k).length (spread 0 k').length
  apply cardinalityClass (wordsSet k) (wordsSet k') positions positions (Finset.range length)
  · intro w hw i hi
    apply Finset.mem_range.mpr
    have inBounds := ((mem_positions w i).mp hi).1
    rw [word_length hw] at inBounds
    exact (by omega : i < (spread 0 k).length).trans_le (le_max_left _ _)
  · intro w hw i hi
    apply Finset.mem_range.mpr
    have inBounds := ((mem_positions w i).mp hi).1
    rw [word_length hw] at inBounds
    exact (by omega : i < (spread 0 k').length).trans_le (le_max_right _ _)
  · intro S
    simpa only [markedWords, List.nil_append] using perm_marked perm [] S

end OMA.PatternStability

open OMA.S_arxiv_2602_13566 OMA.PatternStability

theorem OMA.disproof : ¬ (type_of% @OMA.S_arxiv_2602_13566.main) := by
  intro asserted
  have valid : testPattern.Perm (List.range testPattern.length) := by decide +kernel
  have contradiction := (asserted testPattern valid).mp stable_test
  exact (by decide +kernel : ¬ (testPattern = List.range testPattern.length ∨
    testPattern = (List.range testPattern.length).reverse)) contradiction