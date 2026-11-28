import OMAReductions.R_Erdos19_erdos_19_variants_large_n_R1_H1_R1_H1_R1

-- Reduction Erdos19.erdos_19.variants.large_n.R1.H1.R1.H1.R1.H2.R1 of step Erdos19.erdos_19.variants.large_n.R1.H1.R1.H1.R1.H2
-- Credit: @AlfredMelson

namespace OMA.R_Erdos19_erdos_19_variants_large_n_R1_H1_R1_H1_R1_H2_R1

open Finset

private theorem other_point {n : ℕ} {A : Finset (Fin n)} {x : Fin n}
    (hc : A.card = 2) (hx : x ∈ A) : ∃ y, y ≠ x ∧ A = {x,y} := by
  obtain ⟨a,b,hab,rfl⟩ := Finset.card_eq_two.mp hc
  simp only [mem_insert,mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact ⟨b,hab.symm,rfl⟩
  · exact ⟨a,hab,Finset.pair_comm ..⟩

theorem color_by_reflection {n : ℕ} [NeZero n] (L : Finset (Finset (Fin n)))
    (label : Fin n ≃ Fin n) (cent : Finset (Fin n) → Fin n)
    (linear : ∀ A ∈ L, ∀ B ∈ L, A ≠ B → (A ∩ B).card ≤ 1)
    (closed : ∀ A ∈ L, A.card ≠ 2 → ∀ x ∈ A, label.symm (cent A - label x) ∈ A)
    (separate : ∀ A ∈ L, ∀ B ∈ L, A ≠ B → A.card ≠ 2 → B.card ≠ 2 →
      (A ∩ B).Nonempty → cent A ≠ cent B) :
    ∃ c : Finset (Fin n) → Fin n,
      ∀ A ∈ L, ∀ B ∈ L, A ≠ B → (A ∩ B).Nonempty → c A ≠ c B := by
  let c (A : Finset (Fin n)) := if A.card = 2 then ∑ x ∈ A, label x else cent A
  have pair {A : Finset (Fin n)} {x y : Fin n} (h : y ≠ x) (e : A = {x,y}) :
      c A = label x + label y := by simp [c,e,h.symm]
  have mixed {A B : Finset (Fin n)} (ha : A ∈ L) (hb : B ∈ L) (ne : A ≠ B)
      (ac : A.card = 2) (bc : B.card ≠ 2) {x : Fin n} (xa : x ∈ A) (xb : x ∈ B) :
      c A ≠ c B := by
    obtain ⟨y,hy,ea⟩ := other_point ac xa
    intro eq
    rw [pair hy ea,show c B = cent B by simp [c,bc]] at eq
    have yc := closed B hb bc x xb
    rw [← eq, add_comm, add_sub_cancel_right, Equiv.symm_apply_apply] at yc
    have sub : A ⊆ A ∩ B := subset_inter subset_rfl (by rw [ea]; exact insert_subset xb (singleton_subset_iff.mpr yc))
    have := card_le_card sub
    have := linear A ha B hb ne
    omega
  refine ⟨c, ?_⟩
  rintro A ha B hb ne ⟨x,hx⟩
  obtain ⟨xa,xb⟩ := mem_inter.mp hx
  by_cases ac : A.card = 2 <;> by_cases bc : B.card = 2
  · obtain ⟨y,hy,ea⟩ := other_point ac xa
    obtain ⟨z,hz,eb⟩ := other_point bc xb
    intro eq
    rw [pair hy ea,pair hz eb] at eq
    have yz : y = z := label.injective (add_left_cancel eq)
    exact ne (by rw [ea,eb,yz])
  · exact mixed ha hb ne ac bc xa xb
  · exact (mixed hb ha ne.symm bc ac xb xa).symm
  · simpa [c,ac,bc] using separate A ha B hb ne ac bc ⟨x,hx⟩

private theorem reflect_bounds {n : ℕ} [NeZero n] {l x r : Fin n} (hl : l ≤ x) (hr : x ≤ r) :
    l ≤ l+r-x ∧ l+r-x ≤ r := by
  let y : Fin n := ⟨l.val+(r.val-x.val),by have := r.isLt; change l.val ≤ x.val at hl; omega⟩
  have hs : y + x = l + r := by
    apply Fin.ext
    simp only [Fin.val_add]
    congr 1
    change l.val + (r.val-x.val) + x.val = l.val + r.val
    change x.val ≤ r.val at hr
    omega
  rw [← hs, add_sub_cancel_right]
  change l.val ≤ l.val+(r.val-x.val) ∧ l.val+(r.val-x.val) ≤ r.val
  change l.val ≤ x.val at hl
  change x.val ≤ r.val at hr
  omega

theorem color_disjoint_large {n : ℕ} [NeZero n] (L : Finset (Finset (Fin n)))
    (linear : ∀ A ∈ L, ∀ B ∈ L, A ≠ B → (A ∩ B).card ≤ 1)
    (sep : ∀ A ∈ L, ∀ B ∈ L, A.card ≠ 2 → B.card ≠ 2 → (A ∩ B).Nonempty → A = B) :
    ∃ c : Finset (Fin n) → Fin n,
      ∀ A ∈ L, ∀ B ∈ L, A ≠ B → (A ∩ B).Nonempty → c A ≠ c B := by
  classical
  let big (A : Finset (Fin n)) := A ∈ L ∧ A.card ≠ 2
  let key (x : Fin n) := if h : ∃ A, big A ∧ x ∈ A then h.choose else ∅
  have key_eq {A : Finset (Fin n)} (ha : big A) {x : Fin n} (hx : x ∈ A) : key x = A := by
    have h : ∃ B, big B ∧ x ∈ B := ⟨A,ha,hx⟩
    simp only [key, dif_pos h]
    obtain ⟨hb,hm⟩ := h.choose_spec
    exact sep _ hb.1 _ ha.1 hb.2 ha.2 ⟨x,mem_inter.mpr ⟨hm,hx⟩⟩
  have mem_key {x : Fin n} {A : Finset (Fin n)} (hne : A.Nonempty) (he : key x = A) : x ∈ A := by
    unfold key at he
    split at he
    next h => exact he ▸ h.choose_spec.2
    next => exact (hne.ne_empty he.symm).elim
  let rank (x : Fin n) := Encodable.encode (key x)
  let order := Tuple.sort rank
  let label := order.symm
  let S (A : Finset (Fin n)) := A.image label
  let cent (A : Finset (Fin n)) := if h : (S A).Nonempty then (S A).min' h + (S A).max' h else 0
  apply color_by_reflection L label cent linear
  · intro A ha hbig x hx
    have hS : (S A).Nonempty := ⟨_,mem_image_of_mem label hx⟩
    let l := (S A).min' hS
    let r := (S A).max' hS
    obtain ⟨a,haA,hal⟩ := mem_image.mp ((S A).min'_mem hS)
    obtain ⟨b,hbA,hbr⟩ := mem_image.mp ((S A).max'_mem hS)
    have lo : l ≤ label x := (S A).min'_le _ (mem_image_of_mem label hx)
    have hi : label x ≤ r := (S A).le_max' _ (mem_image_of_mem label hx)
    obtain ⟨hlo,hhi⟩ := reflect_bounds lo hi
    rw [show cent A = l+r by simp [cent,hS,l,r]]
    apply mem_key ⟨x,hx⟩
    apply Encodable.encode_injective
    change rank (order (l+r-label x)) = Encodable.encode A
    have mono : Monotone (rank ∘ order) := Tuple.monotone_sort rank
    have hl : (rank ∘ order) l = Encodable.encode A := by
      change label a = l at hal
      rw [← hal]; change Encodable.encode (key (order (order.symm a))) = _
      rw [order.apply_symm_apply,key_eq ⟨ha,hbig⟩ haA]
    have hh : (rank ∘ order) r = Encodable.encode A := by
      change label b = r at hbr
      rw [← hbr]; change Encodable.encode (key (order (order.symm b))) = _
      rw [order.apply_symm_apply,key_eq ⟨ha,hbig⟩ hbA]
    exact le_antisymm ((mono hhi).trans hh.le) (hl.ge.trans (mono hlo))
  · intro A ha B hb ne ac bc hit
    exact (ne (sep A ha B hb ac bc hit)).elim

open Filter

private def nearFull {n : ℕ} (q : ℕ) (L : Finset (Finset (Fin n))) : Prop :=
  ∃ x : Fin n, (univ.filter
    (fun y => y ≠ x ∧ {x,y} ∉ L.filter (fun A => A.card = 2))).card < 2 * (n / q)

private def meetingLarge {n : ℕ} (L : Finset (Finset (Fin n))) : Prop :=
  ∃ A ∈ L, ∃ B ∈ L, A ≠ B ∧ A.card ≠ 2 ∧ B.card ≠ 2 ∧ (A ∩ B).Nonempty

private def commonPoint {n : ℕ} (L : Finset (Finset (Fin n))) : Prop :=
  ∃ x : Fin n, ∀ A ∈ L, A.card ≠ 2 → x ∈ A

def H1 : Prop := ∀ R : ℕ, ∃ q : ℕ, 2 ≤ q ∧ ∀ᶠ n in atTop, ∀ L : Finset (Finset (Fin n)),
  (∀ A ∈ L, 2 ≤ A.card ∧ A.card ≤ R) →
  (∀ A ∈ L, ∀ B ∈ L, A ≠ B → (A ∩ B).card ≤ 1) →
  nearFull q L → meetingLarge L → commonPoint L →
  ∃ c : Finset (Fin n) → Fin n,
    ∀ A ∈ L, ∀ B ∈ L, A ≠ B → (A ∩ B).Nonempty → c A ≠ c B

def H2 : Prop := ∀ R : ℕ, ∃ q : ℕ, 2 ≤ q ∧ ∀ᶠ n in atTop, ∀ L : Finset (Finset (Fin n)),
  (∀ A ∈ L, 2 ≤ A.card ∧ A.card ≤ R) →
  (∀ A ∈ L, ∀ B ∈ L, A ≠ B → (A ∩ B).card ≤ 1) →
  nearFull q L → meetingLarge L → ¬ commonPoint L →
  ∃ c : Finset (Fin n) → Fin n,
    ∀ A ∈ L, ∀ B ∈ L, A ≠ B → (A ∩ B).Nonempty → c A ≠ c B

theorem main : H1 → H2 → OMA.R_Erdos19_erdos_19_variants_large_n_R1_H1_R1_H1_R1.H2 := by
  intro h1 h2 R
  obtain ⟨a,ha,hA⟩ := h1 R
  obtain ⟨b,hb,hB⟩ := h2 R
  refine ⟨max a b, by omega, ?_⟩
  filter_upwards [hA,hB,eventually_ge_atTop 1] with n A B hn
  letI : NeZero n := ⟨by omega⟩
  intro L size linear dense
  obtain ⟨x,hx⟩ := dense
  have reduce (d : ℕ) (hd : 0 < d) (hle : d ≤ max a b) : nearFull d L :=
    ⟨x, lt_of_lt_of_le hx (Nat.mul_le_mul_left 2 (Nat.div_le_div_left hle hd))⟩
  by_cases meet : meetingLarge L
  · by_cases star : commonPoint L
    · exact A L size linear (reduce a (by omega) (le_max_left ..)) meet star
    · exact B L size linear (reduce b (by omega) (le_max_right ..)) meet star
  · apply color_disjoint_large L linear
    intro U hU V hV u v hit
    by_contra ne
    exact meet ⟨U,hU,V,hV,ne,u,v,hit⟩

end OMA.R_Erdos19_erdos_19_variants_large_n_R1_H1_R1_H1_R1_H2_R1
