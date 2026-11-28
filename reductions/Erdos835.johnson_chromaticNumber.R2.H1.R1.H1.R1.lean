import OMAReductions.R_Erdos835_johnson_chromaticNumber_R2_H1_R1

/-!
Contract the known small cases to derived Steiner systems. In the remaining
cases restrict an antipodal coloring to blocks containing one distinguished
point and avoiding a second point. The restriction must omit the same color
from each star and the complementary top.
-/

open Finset SimpleGraph

namespace OMA.R_Erdos835_johnson_chromaticNumber_R2_H1_R1_H1_R1

/-- The small cases follow from the corresponding derived Steiner systems. -/
def H1 : Prop :=
  ¬ (johnson 10 4).Colorable 7 ∧ ¬ (johnson 15 5).Colorable 11 ∧
    ¬ (johnson 17 5).Colorable 13

/-- Color the middle layer on two fewer points. Opposite blocks have distinct
colors, and a star and its complementary top omit a common color. -/
def H2 : Prop :=
  ∀ k : ℕ, 16 ≤ k → (k + 1).Prime →
    ¬ ∃ (c d : Finset (Fin (2*k - 2)) → Fin (k+1)),
      (∀ S T, S.card = k-1 → T.card = k-1 → (S ∩ T).card + 1 = k-1 → c S ≠ c T) ∧
      (∀ S, S.card = k-1 → c S ≠ c Sᶜ) ∧
      (∀ T S : Finset (Fin (2*k - 2)), T.card = k-2 → S.card = k-1 → T ⊆ S →
        c S ≠ d T ∧ c Sᶜ ≠ d T)

section Proof

private theorem intersection_compl {α : Type*} [Fintype α] [DecidableEq α]
    (A B : Finset α) : (A ∩ B).card + (A ∩ Bᶜ).card = A.card := by
  have he : A ∩ Bᶜ = A \ B := by
    ext x
    simp
  rw [he, add_comm]
  exact card_sdiff_add_card_inter _ _

private theorem complement_pair {k : ℕ} {S T : Finset (Fin (2*k))}
    (hS : S.card = k) (hT : T.card = k) :
    (Sᶜ ∩ Tᶜ).card = (S ∩ T).card := by
  rw [← compl_union, card_compl, Fintype.card_fin]
  have hh := card_union_add_card_inter S T
  omega

private theorem trace_le_succ {α : Type*} [DecidableEq α] (A S T : Finset α) :
    (A ∩ S).card ≤ (A ∩ T).card + (S \ T).card := by
  have hdiff : (A ∩ S) \ (A ∩ T) ⊆ S \ T := by
    intro z
    simp only [mem_sdiff, mem_inter]
    tauto
  have hsub : (A ∩ S) ∩ (A ∩ T) ⊆ A ∩ T := inter_subset_right
  have hsum := card_sdiff_add_card_inter (A ∩ S) (A ∩ T)
  have := card_le_card hdiff
  have := card_le_card hsub
  omega

/-- Extend a coloring of the closed half by reflecting the other half. -/
theorem extend_half {k : ℕ} (hk : Even k) (A : Finset (Fin (2*k))) (hA : A.card = k)
    (F : Fin (k+1) → Finset (Finset (Fin (2*k))))
    (hpart : ∀ B : Finset (Fin (2*k)), B.card = k → k ≤ 2*(A ∩ B).card → ∃! i, B ∈ F i)
    (hproper : ∀ i B C, B ∈ F i → C ∈ F i → (B ∩ C).card + 1 ≠ k)
    (heq : ∀ i B, B ∈ F i → 2*(A ∩ B).card = k → Bᶜ ∈ F i) :
    ∃ c : Finset (Fin (2*k)) → Fin (k+1),
      (∀ S T, S.card = k → T.card = k → (S ∩ T).card + 1 = k → c S ≠ c T) ∧
      (∀ S, S.card = k → c Sᶜ = c S) := by
  classical
  let fold (S : Finset (Fin (2*k))) := if k ≤ 2*(A ∩ S).card then S else Sᶜ
  have hcardcompl (S : Finset (Fin (2*k))) (hS : S.card = k) : Sᶜ.card = k := by
    rw [card_compl, Fintype.card_fin, hS]
    omega
  have hfold (S : Finset (Fin (2*k))) (hS : S.card = k) :
      (fold S).card = k ∧ k ≤ 2*(A ∩ fold S).card := by
    by_cases hs : k ≤ 2*(A ∩ S).card
    · simp [fold, hs, hS]
    · simp only [fold, if_neg hs]
      have := intersection_compl A S
      exact ⟨hcardcompl S hS, by omega⟩
  let c (S : Finset (Fin (2*k))) : Fin (k+1) :=
    if h : S.card = k then (hpart (fold S) (hfold S h).1 (hfold S h).2).exists.choose else 0
  have hc (S : Finset (Fin (2*k))) (hS : S.card = k) : fold S ∈ F (c S) := by
    simp only [c, dif_pos hS]
    exact (hpart _ (hfold S hS).1 (hfold S hS).2).exists.choose_spec
  have same (S T : Finset (Fin (2*k))) (hS : S.card = k) (hT : T.card = k)
      (h : fold S = fold T) : c S = c T := by
    obtain ⟨i, _, hu⟩ := hpart _ (hfold S hS).1 (hfold S hS).2
    exact (hu _ (hc S hS)).trans (hu _ (h ▸ hc T hT)).symm
  have hboundary (S : Finset (Fin (2*k))) (hS : S.card = k)
      (hs : k ≤ 2*(A ∩ S).card) : S ∈ F (c S) := by
    simpa only [fold, if_pos hs] using hc S hS
  have hopposite (S : Finset (Fin (2*k))) (hS : S.card = k) : c Sᶜ = c S := by
    have hSc := hcardcompl S hS
    have hsum := intersection_compl A S
    obtain hlt | he | hgt := lt_trichotomy (2*(A ∩ S).card) k
    · apply same _ _ hSc hS
      simp only [fold, if_pos (show k ≤ 2*(A ∩ Sᶜ).card by omega), if_neg (not_le.mpr hlt)]
    · have hsc : k ≤ 2*(A ∩ Sᶜ).card := by omega
      obtain ⟨i, _, hu⟩ := hpart Sᶜ hSc hsc
      exact (hu _ (hboundary _ hSc hsc)).trans
        (hu _ (heq _ _ (hboundary S hS he.ge) he)).symm
    · apply same _ _ hSc hS
      simp only [fold, if_neg (show ¬ k ≤ 2*(A ∩ Sᶜ).card by omega),
        if_pos hgt.le, compl_compl]
  have cross (S T : Finset (Fin (2*k))) (hS : S.card = k) (hT : T.card = k)
      (hadj : (S ∩ T).card + 1 = k) (hs : k ≤ 2*(A ∩ S).card)
      (ht : ¬ k ≤ 2*(A ∩ T).card) : c S ≠ c T := by
    have hdist : (S \ T).card = 1 := by
      have := card_sdiff_add_card_inter S T
      omega
    have htrace := trace_le_succ A S T
    obtain ⟨r, hr⟩ := hk
    have hes : 2*(A ∩ S).card = k := by omega
    have hts := intersection_compl A T
    have ht' : k ≤ 2*(A ∩ Tᶜ).card := by omega
    intro hcol
    have hp := hproper (c S) Sᶜ Tᶜ (heq _ _ (hboundary S hS hs) hes)
      (by rw [hcol, ← hopposite T hT]; exact hboundary _ (hcardcompl T hT) ht')
    exact hp (by rwa [complement_pair hS hT])
  refine ⟨c, ?_, hopposite⟩
  intro S T hS hT hadj
  by_cases hs : k ≤ 2*(A ∩ S).card <;> by_cases ht : k ≤ 2*(A ∩ T).card
  · intro h
    exact hproper _ _ _ (hboundary S hS hs) (h ▸ hboundary T hT ht) hadj
  · exact cross S T hS hT hadj hs ht
  · exact (cross T S hT hS (by simpa only [inter_comm] using hadj) ht hs).symm
  · intro h
    have hs' : fold S = Sᶜ := if_neg hs
    have ht' : fold T = Tᶜ := if_neg ht
    have hp := hproper _ _ _ (hc S hS) (h ▸ hc T hT)
    apply hp
    rw [hs', ht', complement_pair hS hT, hadj]

private theorem as_coloring {n k p : ℕ} (c : Finset (Fin n) → Fin p)
    (hc : ∀ S T, S.card = k → T.card = k → (S ∩ T).card + 1 = k → c S ≠ c T) :
    (johnson n k).Colorable p :=
  ⟨SimpleGraph.Coloring.mk (fun S => c S.val) fun {v w} h => hc _ _ v.property w.property h⟩

private theorem derived_coloring {n j t p : ℕ}
    (h : (johnson (n+t) (j+t)).Colorable p) :
    (johnson n j).Colorable p := by
  classical
  obtain ⟨c⟩ := h
  let e : Fin n ↪ Fin (n+t) :=
    ⟨fun i => ⟨i.val, by omega⟩, fun _ _ h => Fin.ext (Fin.mk.inj h)⟩
  let R : Finset (Fin (n+t)) := (univ : Finset (Fin t)).map
    (⟨fun i => ⟨n + i.val, by omega⟩, fun _ _ h => Fin.ext (by
      have := Fin.mk.inj h
      omega)⟩ : Fin t ↪ Fin (n+t))
  have hR : R.card = t := by simp [R]
  have hdis (S : Finset (Fin n)) : Disjoint (S.map e) R := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨i, _, rfl⟩ := mem_map.mp hx
    obtain ⟨j, _, hj⟩ := mem_map.mp hy
    have h := congrArg Fin.val hj
    change n + j.val = i.val at h
    omega
  let f (S : {S : Finset (Fin n) // S.card = j}) :
      {S : Finset (Fin (n+t)) // S.card = j+t} :=
    ⟨S.val.map e ∪ R, by rw [card_union_of_disjoint (hdis S.val), card_map, S.property, hR]⟩
  refine ⟨SimpleGraph.Coloring.mk (fun S => c (f S)) ?_⟩
  intro S T hST
  apply c.valid
  change ((S.val.map e ∪ R) ∩ (T.val.map e ∪ R)).card + 1 = j+t
  have he : (S.val.map e ∪ R) ∩ (T.val.map e ∪ R) = (S.val ∩ T.val).map e ∪ R := by
    rw [map_inter]
    ext x
    simp only [mem_inter, mem_union]
    tauto
  rw [he, card_union_of_disjoint (hdis (S.val ∩ T.val)), card_map, hR]
  change (S.val ∩ T.val).card + 1 = j at hST
  omega

private theorem two_points (k : ℕ) (hk : 1 ≤ k) :
    ∃ (e : Fin (2*k - 2) ↪ Fin (2*k)) (x y : Fin (2*k)), x ≠ y ∧
      (∀ a, e a ≠ x ∧ e a ≠ y) ∧ (∀ z, z ≠ x → z ≠ y → ∃ a, e a = z) := by
  let x : Fin (2*k) := ⟨2*k - 2, by omega⟩
  let y : Fin (2*k) := ⟨2*k - 1, by omega⟩
  let e : Fin (2*k - 2) ↪ Fin (2*k) :=
    ⟨fun a => ⟨a.val, by omega⟩, fun _ _ h => Fin.ext (Fin.mk.inj h)⟩
  refine ⟨e, x, y, ?_, ?_, ?_⟩
  · intro h
    have := Fin.mk.inj h
    omega
  · intro a
    constructor <;> intro h <;> have := Fin.mk.inj h <;> omega
  · intro z hx hy
    have hzx : z.val ≠ 2*k - 2 := fun h => hx (Fin.ext h)
    have hzy : z.val ≠ 2*k - 1 := fun h => hy (Fin.ext h)
    exact ⟨⟨z.val, by omega⟩, Fin.ext rfl⟩

private theorem fresh_map {α β : Type*} {e : α ↪ β} {x : β}
    (hx : ∀ a, e a ≠ x) (S : Finset α) : x ∉ S.map e := by
  rintro h
  obtain ⟨a, _, hax⟩ := mem_map.mp h
  exact hx a hax

private theorem compl_insert_map {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] {e : α ↪ β} {x y : β}
    (hxy : x ≠ y) (hf : ∀ a, e a ≠ x ∧ e a ≠ y)
    (hcover : ∀ z, z ≠ x → z ≠ y → ∃ a, e a = z) (S : Finset α) :
    (insert x (S.map e))ᶜ = insert y (Sᶜ.map e) := by
  ext z
  by_cases hx : z = x
  · subst z
    simp [hxy, fresh_map (fun a => (hf a).1)]
  by_cases hy : z = y
  · subst z
    simp [hxy.symm, fresh_map (fun a => (hf a).2)]
  obtain ⟨a, rfl⟩ := hcover z hx hy
  simp only [mem_compl, mem_insert, hx, hy, false_or, mem_map']

private theorem card_insert_map {α β : Type*} [DecidableEq β] {e : α ↪ β} {x : β}
    (hx : ∀ a, e a ≠ x) (S : Finset α) :
    (insert x (S.map e)).card = S.card + 1 := by
  rw [card_insert_of_notMem (fresh_map hx S), card_map]

/-- Taking the blocks through one point but avoiding a second gives the
two-point formulation with common missing colors. -/
theorem restrict_two_points {k : ℕ} (hk : 2 ≤ k) (C : Finset (Fin (2*k)) → Fin (k+1))
    (hp : ∀ S T, S.card = k → T.card = k → (S ∩ T).card + 1 = k → C S ≠ C T)
    (ha : ∀ S, S.card = k → C Sᶜ = C S) :
    ∃ (c d : Finset (Fin (2*k - 2)) → Fin (k+1)),
      (∀ S T, S.card = k-1 → T.card = k-1 → (S ∩ T).card + 1 = k-1 → c S ≠ c T) ∧
      (∀ S, S.card = k-1 → c S ≠ c Sᶜ) ∧
      (∀ T S : Finset (Fin (2*k - 2)), T.card = k-2 → S.card = k-1 → T ⊆ S →
        c S ≠ d T ∧ c Sᶜ ≠ d T) := by
  obtain ⟨e, x, y, hxy, hf, hcover⟩ := two_points k (by omega)
  let X (S : Finset (Fin (2*k - 2))) := insert x (S.map e)
  let Y (S : Finset (Fin (2*k - 2))) := insert y (S.map e)
  let Z (T : Finset (Fin (2*k - 2))) := insert y (X T)
  have hxc (S) : (X S).card = S.card + 1 := card_insert_map (fun a => (hf a).1) S
  have hyc (S) : (Y S).card = S.card + 1 := card_insert_map (fun a => (hf a).2) S
  have hxnot (S) : x ∉ Y S := by simp [Y, hxy, fresh_map (fun a => (hf a).1)]
  have hynot (S) : y ∉ X S := by simp [X, hxy.symm, fresh_map (fun a => (hf a).2)]
  have hzc (T) : (Z T).card = T.card + 2 := by
    rw [card_insert_of_notMem (hynot T), hxc]
  have hscompl (S : Finset (Fin (2*k - 2))) (hS : S.card = k-1) :
      Sᶜ.card = k-1 := by
    rw [card_compl, Fintype.card_fin, hS]
    omega
  have hcompl (S) (hS : S.card = k-1) : C (X Sᶜ) = C (Y S) := by
    have h := ha (X Sᶜ) (by rw [hxc, hscompl S hS]; omega)
    have hset : (X Sᶜ)ᶜ = Y S := by
      simpa only [compl_compl] using compl_insert_map hxy hf hcover Sᶜ
    rw [hset] at h
    exact h.symm
  refine ⟨fun S => C (X S), fun T => C (Z T), ?_, ?_, ?_⟩
  · intro S T hS hT hST
    apply hp _ _ (by rw [hxc, hS]; omega) (by rw [hxc, hT]; omega)
    have he : X S ∩ X T = X (S ∩ T) := by
      dsimp only [X]
      rw [← insert_inter_distrib, map_inter]
    rw [he, hxc]
    omega
  · intro S hS
    change C (X S) ≠ C (X Sᶜ)
    rw [hcompl S hS]
    apply hp _ _ (by rw [hxc, hS]; omega) (by rw [hyc, hS]; omega)
    have he : X S ∩ Y S = S.map e := by
      rw [show X S = insert x (S.map e) from rfl, insert_inter_of_notMem (hxnot S)]
      exact inter_eq_left.mpr (subset_insert _ _)
    rw [he, card_map, hS]
    omega
  · intro T S hT hS hTS
    have hZ : (Z T).card = k := by rw [hzc, hT]; omega
    have hXT : X T ⊆ X S := insert_subset_insert _ (map_subset_map.mpr hTS)
    have hYT : Y T ⊆ Y S := insert_subset_insert _ (map_subset_map.mpr hTS)
    have hZ' : Z T = insert x (Y T) := insert_comm _ _ _
    constructor
    · apply hp _ _ (by rw [hxc, hS]; omega) hZ
      rw [show Z T = insert y (X T) from rfl, inter_insert_of_notMem (hynot S),
        inter_eq_right.mpr hXT, hxc, hT]
      omega
    · change C (X Sᶜ) ≠ C (Z T)
      rw [hcompl S hS]
      apply hp _ _ (by rw [hyc, hS]; omega) hZ
      rw [hZ', inter_insert_of_notMem (hxnot S), inter_eq_right.mpr hYT, hyc, hT]
      omega

-- Adapt the matching-parity lemma from the merged two-point deletion proof.
private theorem even_of_involution {A : Type*} [Fintype A] [LinearOrder A]
    (τ : A → A) (hτ : Function.Involutive τ) (hne : ∀ a, τ a ≠ a) :
    Even (Fintype.card A) := by
  let L := univ.filter fun a : A => a < τ a
  let R := univ.filter fun a : A => τ a < a
  have hLR : L.card ≤ R.card := by
    refine card_le_card_of_injOn τ ?_ hτ.injective.injOn
    intro a ha
    have h := (mem_filter.mp (show a ∈ L from ha)).2
    exact mem_filter.mpr ⟨mem_univ _, by rw [hτ]; exact h⟩
  have hRL : R.card ≤ L.card := by
    refine card_le_card_of_injOn τ ?_ hτ.injective.injOn
    intro a ha
    have h := (mem_filter.mp (show a ∈ R from ha)).2
    exact mem_filter.mpr ⟨mem_univ _, by rw [hτ]; exact h⟩
  have hother : univ.filter (fun a : A => ¬ a < τ a) = R := by
    ext a
    simp only [R, mem_filter, mem_univ, true_and, not_lt]
    exact ⟨fun h => lt_of_le_of_ne h (hne a), le_of_lt⟩
  have hsum := (univ : Finset A).card_filter_add_card_filter_not (fun a => a < τ a)
  change L.card + (univ.filter fun a : A => ¬ a < τ a).card = (univ : Finset A).card at hsum
  rw [hother, card_univ] at hsum
  exact ⟨L.card, by omega⟩

private theorem missing_injective {α : Type*} [DecidableEq α] [LinearOrder α]
    {p : ℕ} (hp : Odd p) (Q : Finset α) (hQ : Q.card = p)
    (e : α → α → Fin p)
    (hsym : ∀ a ∈ Q, ∀ b ∈ Q, e a b = e b a)
    (hlocal : ∀ a ∈ Q, ∀ b ∈ Q, ∀ c ∈ Q, b ≠ a → c ≠ a → b ≠ c → e a b ≠ e a c)
    (f : α → Fin p)
    (hmiss : ∀ a ∈ Q, ∀ b ∈ Q, a ≠ b → e a b ≠ f a) : Set.InjOn f Q := by
  classical
  have himage (a : α) (ha : a ∈ Q) :
      (Q.erase a).image (e a) = (univ : Finset (Fin p)).erase (f a) := by
    apply eq_of_subset_of_card_le
    · intro c hc
      obtain ⟨b, hb, rfl⟩ := mem_image.mp hc
      obtain ⟨hba, hbQ⟩ := mem_erase.mp hb
      exact mem_erase.mpr ⟨hmiss a ha b hbQ hba.symm, mem_univ _⟩
    · have hi : Set.InjOn (e a) ((Q.erase a : Finset (α)) : Set _) := by
        intro b hb c hc hbc
        obtain ⟨hba, hbQ⟩ := mem_erase.mp (show b ∈ Q.erase a from hb)
        obtain ⟨hca, hcQ⟩ := mem_erase.mp (show c ∈ Q.erase a from hc)
        by_contra! hne
        exact hlocal a ha b hbQ c hcQ hba hca hne hbc
      rw [card_image_of_injOn hi, card_erase_of_mem ha, card_erase_of_mem (mem_univ _),
        card_univ, Fintype.card_fin, hQ]
  let F : Q → Fin p := fun a => f a
  have hs : Function.Surjective F := by
    intro c
    by_contra! hnone
    have hchoose (a : Q) : ∃ b : Q, b ≠ a ∧ e a b = c := by
      have hc : c ∈ (Q.erase (a : α)).image (e a) := by
        rw [himage a a.property]
        exact mem_erase.mpr ⟨(hnone a).symm, mem_univ _⟩
      obtain ⟨b, hb, he⟩ := mem_image.mp hc
      obtain ⟨hba, hbQ⟩ := mem_erase.mp hb
      exact ⟨⟨b, hbQ⟩, fun heq => hba (congrArg Subtype.val heq), he⟩
    choose τ hne hcolor using hchoose
    have hinv : Function.Involutive τ := by
      intro a
      apply Subtype.ext
      by_contra! hne'
      have ht₁ : (τ (τ a)).val ≠ (τ a).val := fun h => hne (τ a) (Subtype.ext h)
      have ht₂ : a.val ≠ (τ a).val := fun h => hne a (Subtype.ext h.symm)
      exact hlocal (τ a) (τ a).property (τ (τ a)) (τ (τ a)).property a a.property ht₁ ht₂ hne'
        ((hcolor (τ a)).trans ((hsym (τ a) (τ a).property a a.property).trans (hcolor a)).symm)
    have heven := even_of_involution τ hinv hne
    rw [Fintype.card_coe, hQ] at heven
    exact (Nat.not_even_iff_odd.mpr hp) heven
  have hcards : Fintype.card Q = Fintype.card (Fin p) := by rw [Fintype.card_coe, hQ, Fintype.card_fin]
  have hinj := ((Fintype.bijective_iff_surjective_and_card F).mpr ⟨hs, hcards⟩).1
  intro a ha b hb h
  exact congrArg Subtype.val (hinj (show F ⟨a, ha⟩ = F ⟨b, hb⟩ from h))


private theorem different_extensions {α : Type*} [DecidableEq α] (S : Finset α)
    {a b : α} (ha : a ∉ S) (hab : a ≠ b) : insert a S ∩ insert b S = S := by
  rw [insert_inter_of_notMem (by simp [ha, hab])]
  exact inter_eq_left.mpr (subset_insert _ _)

/-- The common missing-color map is proper on the layer one size down. -/
theorem missing_is_proper {k : ℕ} (hk : 3 ≤ k) (hodd : Odd (k+1))
    (c d : Finset (Fin (2*k - 2)) → Fin (k+1))
    (hc : ∀ S T, S.card = k-1 → T.card = k-1 → (S ∩ T).card + 1 = k-1 → c S ≠ c T)
    (hmiss : ∀ T S : Finset (Fin (2*k - 2)), T.card = k-2 → S.card = k-1 → T ⊆ S →
      c S ≠ d T) :
    ∀ S T, S.card = k-2 → T.card = k-2 → (S ∩ T).card + 1 = k-2 → d S ≠ d T := by
  intro S T hS hT hST
  let U := S ∩ T
  let Q := Uᶜ
  have hU : U.card + 1 = k-2 := hST
  have hQ : Q.card = k+1 := by
    dsimp only [Q]
    rw [card_compl, Fintype.card_fin]
    omega
  let color (a b : Fin (2*k - 2)) := c (insert b (insert a U))
  let missing (a : Fin (2*k - 2)) := d (insert a U)
  have hQa {a : Fin (2*k - 2)} (ha : a ∈ Q) : a ∉ U := mem_compl.mp ha
  have sizeOne {a : Fin (2*k - 2)} (ha : a ∈ Q) : (insert a U).card = k-2 := by
    rw [card_insert_of_notMem (hQa ha), hU]
  have sizeTwo {a b : Fin (2*k - 2)} (ha : a ∈ Q) (hb : b ∈ Q) (hab : b ≠ a) :
      (insert b (insert a U)).card = k-1 := by
    rw [card_insert_of_notMem (by simp [hab, hQa hb]), sizeOne ha]
    omega
  have hinj : Set.InjOn missing Q := by
    apply missing_injective hodd Q hQ color
    · intro a _ b _
      simp only [color, insert_comm]
    · intro a ha b hb e he hba hea hbe
      apply hc _ _ (sizeTwo ha hb hba) (sizeTwo ha he hea)
      rw [different_extensions _ (by simp [hba, hQa hb]) hbe, sizeOne ha]
      omega
    · intro a ha b hb hab
      exact hmiss _ _ (sizeOne ha) (sizeTwo ha hb hab.symm) (subset_insert _ _)
  have cover (B : Finset (Fin (2*k - 2))) (hB : B.card = k-2) (hUB : U ⊆ B) :
      ∃ a ∈ Q, B = insert a U := by
    have hd : (B \ U).card = 1 := by rw [card_sdiff_of_subset hUB, hB]; omega
    obtain ⟨a, ha⟩ := card_eq_one.mp hd
    have hab : a ∈ B \ U := ha.symm ▸ mem_singleton_self a
    have ⟨haB, haU⟩ := mem_sdiff.mp hab
    refine ⟨a, mem_compl.mpr haU, ?_⟩
    exact (eq_of_subset_of_card_le (insert_subset haB hUB)
      (by rw [card_insert_of_notMem haU, hU, hB])).symm
  obtain ⟨a, ha, hSa⟩ := cover S hS inter_subset_left
  obtain ⟨b, hb, hTb⟩ := cover T hT inter_subset_right
  intro h
  have he := hinj ha hb (by simpa only [missing, ← hSa, ← hTb] using h)
  have heq : S = T := by rw [hSa, hTb, he]
  rw [heq, inter_self] at hST
  omega

/-- A proper two-point restriction with the common missing colors extends to a
proper antipodal coloring of the full middle layer. -/
theorem restore_two_points {k : ℕ} (hk : 3 ≤ k) (hodd : Odd (k+1))
    (c d : Finset (Fin (2*k - 2)) → Fin (k+1))
    (hc : ∀ S T, S.card = k-1 → T.card = k-1 → (S ∩ T).card + 1 = k-1 → c S ≠ c T)
    (ha : ∀ S, S.card = k-1 → c S ≠ c Sᶜ)
    (hm : ∀ T S : Finset (Fin (2*k - 2)), T.card = k-2 → S.card = k-1 → T ⊆ S →
      c S ≠ d T ∧ c Sᶜ ≠ d T) :
    ∃ C : Finset (Fin (2*k)) → Fin (k+1),
      (∀ S T, S.card = k → T.card = k → (S ∩ T).card + 1 = k → C S ≠ C T) ∧
      (∀ S, S.card = k → C Sᶜ = C S) := by
  classical
  have hd := missing_is_proper hk hodd c d hc (fun T S hT hS hTS => (hm T S hT hS hTS).1)
  obtain ⟨e, x, y, hxy, hf, hcover⟩ := two_points k (by omega)
  let tail (B : Finset (Fin (2*k))) : Finset (Fin (2*k - 2)) :=
    univ.filter (fun a => e a ∈ B)
  have htail (B) : (tail B).map e = (B.erase x).erase y := by
    ext z
    simp only [tail, mem_map, mem_filter, mem_univ, true_and, mem_erase]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨(hf a).2, (hf a).1, ha⟩
    · rintro ⟨hy, hx, hB⟩
      obtain ⟨a, rfl⟩ := hcover z hx hy
      exact ⟨a, hB, rfl⟩
  let X (S : Finset (Fin (2*k - 2))) := insert x (S.map e)
  let Z (S : Finset (Fin (2*k - 2))) := insert y (X S)
  have hxc (S) : (X S).card = S.card + 1 := card_insert_map (fun a => (hf a).1) S
  have hyX (S) : y ∉ X S := by simp [X, hxy.symm, fresh_map (fun a => (hf a).2)]
  have hzc (S) : (Z S).card = S.card + 2 := by
    rw [card_insert_of_notMem (hyX S), hxc]
  have shapeX (B) (hx : x ∈ B) (hy : y ∉ B) : B = X (tail B) := by
    change B = insert x ((tail B).map e)
    rw [htail, erase_eq_of_notMem (fun h => hy (mem_of_mem_erase h)), insert_erase hx]
  have shapeZ (B) (hx : x ∈ B) (hy : y ∈ B) : B = Z (tail B) := by
    change B = insert y (insert x ((tail B).map e))
    rw [htail, insert_comm, insert_erase (mem_erase.mpr ⟨hxy.symm, hy⟩), insert_erase hx]
  have xx (S T) : X S ∩ X T = X (S ∩ T) := by
    dsimp only [X]
    rw [← insert_inter_distrib, map_inter]
  have zz (S T) : Z S ∩ Z T = Z (S ∩ T) := by
    dsimp only [Z]
    rw [← insert_inter_distrib, xx]
  have xz (S T) : X S ∩ Z T = X (S ∩ T) := by
    dsimp only [Z]
    rw [inter_insert_of_notMem (hyX S), xx]
  let keep (B : Finset (Fin (2*k))) := if x ∈ B then B else Bᶜ
  let C (B : Finset (Fin (2*k))) :=
    if y ∈ keep B then d (tail (keep B)) else c (tail (keep B))
  have hcomp (B : Finset (Fin (2*k))) : C Bᶜ = C B := by
    have h : keep Bᶜ = keep B := by
      by_cases hx : x ∈ B <;> simp [keep, hx]
    simp only [C, h]
  have hcX (B) (hx : x ∈ B) (hy : y ∉ B) : C B = c (tail B) := by
    simp only [C, keep, if_pos hx, if_neg hy]
  have hcZ (B) (hx : x ∈ B) (hy : y ∈ B) : C B = d (tail B) := by
    simp only [C, keep, if_pos hx, if_pos hy]
  have hccomp (B : Finset (Fin (2*k))) (hB : B.card = k) : Bᶜ.card = k := by
    rw [card_compl, Fintype.card_fin, hB]
    omega
  have disjoint_tail (S T : Finset (Fin (2*k - 2))) (h : (S ∩ T).card = 0) : T ⊆ Sᶜ := by
    have he := Finset.disjoint_iff_inter_eq_empty.mpr (card_eq_zero.mp h)
    exact fun _ ht => mem_compl.mpr fun hs => Finset.disjoint_left.mp he hs ht
  have xs_zs (B D : Finset (Fin (2*k))) (hB : B.card = k) (hD : D.card = k)
      (hxB : x ∈ B) (hxD : x ∈ D) (hyB : y ∉ B) (hyD : y ∈ D)
      (hi : (B ∩ D).card + 1 = k ∨ (B ∩ D).card = 1) : C B ≠ C D := by
    have hb := congrArg Finset.card (shapeX B hxB hyB)
    have hd' := congrArg Finset.card (shapeZ D hxD hyD)
    rw [hB, hxc] at hb
    rw [hD, hzc] at hd'
    have hh := congrArg Finset.card (congrArg₂ (· ∩ ·) (shapeX B hxB hyB) (shapeZ D hxD hyD))
    rw [xz, hxc] at hh
    rw [hcX B hxB hyB, hcZ D hxD hyD]
    rcases hi with hi | hi
    · have hsub : tail D ⊆ tail B := by
        have he : tail B ∩ tail D = tail D :=
          eq_of_subset_of_card_le inter_subset_right (by omega)
        exact he ▸ inter_subset_left
      exact (hm _ _ (by omega) (by omega) hsub).1
    · have hsub : tail D ⊆ (tail B)ᶜ := disjoint_tail _ _ (by omega)
      have hcard : (tail B)ᶜ.card = k-1 := by
        rw [card_compl, Fintype.card_fin]
        omega
      simpa only [compl_compl] using (hm _ _ (by omega) hcard hsub).2
  have hlink (B D : Finset (Fin (2*k))) (hB : B.card = k) (hD : D.card = k)
      (hxB : x ∈ B) (hxD : x ∈ D)
      (hi : (B ∩ D).card + 1 = k ∨ (B ∩ D).card = 1) : C B ≠ C D := by
    by_cases hyB : y ∈ B <;> by_cases hyD : y ∈ D
    · have hb := congrArg Finset.card (shapeZ B hxB hyB)
      have hd' := congrArg Finset.card (shapeZ D hxD hyD)
      rw [hB, hzc] at hb
      rw [hD, hzc] at hd'
      have hh := congrArg Finset.card (congrArg₂ (· ∩ ·) (shapeZ B hxB hyB) (shapeZ D hxD hyD))
      rw [zz, hzc] at hh
      rw [hcZ B hxB hyB, hcZ D hxD hyD]
      exact hd _ _ (by omega) (by omega) (by omega)
    · exact (xs_zs D B hD hB hxD hxB hyD hyB (by rwa [inter_comm])).symm
    · exact xs_zs B D hB hD hxB hxD hyB hyD hi
    · have hb := congrArg Finset.card (shapeX B hxB hyB)
      have hd' := congrArg Finset.card (shapeX D hxD hyD)
      rw [hB, hxc] at hb
      rw [hD, hxc] at hd'
      have hh := congrArg Finset.card (congrArg₂ (· ∩ ·) (shapeX B hxB hyB) (shapeX D hxD hyD))
      rw [xx, hxc] at hh
      rw [hcX B hxB hyB, hcX D hxD hyD]
      rcases hi with hi | hi
      · exact hc _ _ (by omega) (by omega) (by omega)
      · have hsub := disjoint_tail _ _ (show (tail B ∩ tail D).card = 0 by omega)
        have he : tail D = (tail B)ᶜ := eq_of_subset_of_card_le hsub (by
          rw [card_compl, Fintype.card_fin]
          omega)
        rw [he]
        exact ha _ (by omega)
  refine ⟨C, ?_, fun B _ => hcomp B⟩
  intro B D hB hD hadj
  by_cases hxB : x ∈ B <;> by_cases hxD : x ∈ D
  · exact hlink B D hB hD hxB hxD (Or.inl hadj)
  · rw [← hcomp D]
    have h := intersection_compl B D
    exact hlink B Dᶜ hB (hccomp D hD) hxB (mem_compl.mpr hxD) (Or.inr (by omega))
  · rw [← hcomp B]
    have h := intersection_compl D B
    rw [inter_comm B D] at hadj
    exact (hlink D Bᶜ hD (hccomp B hB) hxD (mem_compl.mpr hxB) (Or.inr (by omega))).symm
  · rw [← hcomp B, ← hcomp D]
    exact hlink Bᶜ Dᶜ (hccomp B hB) (hccomp D hD) (mem_compl.mpr hxB) (mem_compl.mpr hxD)
      (Or.inl (by rwa [complement_pair hB hD]))

/-- The two-point model and the full antipodal colorings are equivalent. -/
theorem two_point_iff {k : ℕ} (hk : 3 ≤ k) (hodd : Odd (k+1)) :
    (∃ C : Finset (Fin (2*k)) → Fin (k+1),
      (∀ S T, S.card = k → T.card = k → (S ∩ T).card + 1 = k → C S ≠ C T) ∧
      (∀ S, S.card = k → C Sᶜ = C S)) ↔
    (∃ (c d : Finset (Fin (2*k - 2)) → Fin (k+1)),
      (∀ S T, S.card = k-1 → T.card = k-1 → (S ∩ T).card + 1 = k-1 → c S ≠ c T) ∧
      (∀ S, S.card = k-1 → c S ≠ c Sᶜ) ∧
      (∀ T S : Finset (Fin (2*k - 2)), T.card = k-2 → S.card = k-1 → T ⊆ S →
        c S ≠ d T ∧ c Sᶜ ≠ d T)) := by
  constructor
  · rintro ⟨C, hC, hCa⟩
    exact restrict_two_points (by omega) C hC hCa
  · rintro ⟨c, d, hc, ha, hd⟩
    exact restore_two_points hk hodd c d hc ha hd

section Trace

-- Incidence and inclusion-exclusion from the merged proof of the trace identity.
variable {α : Type*} [DecidableEq α]

-- Count a block containing J once for each of its elements outside J.
private theorem extension_count [Fintype α] {Q : Finset (Finset α)} {k : ℕ}
    (hQ : ∀ B ∈ Q, B.card = k) (J : Finset α) :
    ∑ a ∈ univ \ J, ((Q.filter (insert a J ⊆ ·))).card =
      (k - J.card) * ((Q.filter (J ⊆ ·))).card := by
  have hex (a : α) :
      (Q.filter (insert a J ⊆ ·)) = ((Q.filter (J ⊆ ·))).filter (a ∈ ·) := by
    ext B
    simp only [mem_filter, insert_subset_iff]
    tauto
  calc
    _ = ∑ a ∈ univ \ J, ∑ B ∈ (Q.filter (J ⊆ ·)), if a ∈ B then (1 : ℕ) else 0 := by
      apply sum_congr rfl
      intro a _
      rw [hex, ← sum_filter]
      simp
    _ = ∑ B ∈ (Q.filter (J ⊆ ·)), ∑ a ∈ univ \ J, if a ∈ B then (1 : ℕ) else 0 := sum_comm
    _ = ∑ _B ∈ (Q.filter (J ⊆ ·)), (k - J.card) := by
      apply sum_congr rfl
      intro B hB
      have hJB := (mem_filter.mp hB).2
      have hBc := hQ B (mem_filter.mp hB).1
      have hsd := card_sdiff_add_card_eq_card hJB
      rw [← sum_filter, show ((univ \ J).filter (· ∈ B)) = B \ J by
        ext a
        simp only [mem_filter, mem_sdiff, mem_univ, true_and, and_comm]]
      simp only [sum_const, nsmul_eq_mul, mul_one]
      change (B \ J).card = k - J.card
      rw [← hBc, ← hsd, Nat.add_sub_cancel]
    _ = _ := by simp [mul_comm]

private theorem proper_counts [Fintype α] {Q R : Finset (Finset α)} {k : ℕ}
    (hQ : ∀ B ∈ Q, B.card = k) (hR : ∀ B ∈ R, B.card = k)
    (hcov : ∀ J : Finset α, J.card = k - 1 →
      ((Q.filter (J ⊆ ·))).card = 1 ∧ ((R.filter (J ⊆ ·))).card = 1)
    (J : Finset α) (hJ : J.card < k) : ((Q.filter (J ⊆ ·))).card = ((R.filter (J ⊆ ·))).card := by
  let P (d : ℕ) := ∀ T : Finset α, k - T.card = d → T.card < k →
    ((Q.filter (T ⊆ ·))).card = ((R.filter (T ⊆ ·))).card
  suffices ∀ d, P d from this (k - J.card) J rfl hJ
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro T hTd hTk
    by_cases hOne : d = 1
    · exact (hcov T (by omega)).1.trans (hcov T (by omega)).2.symm
    have hsum :
        ∑ a ∈ (univ \ T), ((Q.filter (insert a T ⊆ ·))).card =
          ∑ a ∈ (univ \ T), ((R.filter (insert a T ⊆ ·))).card := by
      apply sum_congr rfl
      intro a ha
      have hna := (mem_sdiff.mp ha).2
      have hcard := card_insert_of_notMem hna
      exact ih (k - (insert a T).card) (by omega) (insert a T) rfl (by omega)
    rw [extension_count hQ, extension_count hR] at hsum
    exact (Nat.mul_left_cancel_iff (by omega : 0 < k - T.card)).mp hsum

private theorem alternating_subsets (X : Finset α) :
    ∑ J ∈ X.powerset, (-1 : ℤ) ^ J.card = if X = ∅ then 1 else 0 := by
  have hx := (Finset.prod_add (fun _ : α => (-1 : ℤ)) (fun _ => (1 : ℤ)) X).symm
  simp only [prod_const, one_pow, mul_one, neg_add_cancel] at hx
  by_cases h : X = ∅
  · subst X
    simp
  · rw [if_neg h, hx]
    exact zero_pow (by simpa using h)

private theorem alternating_counts (Q : Finset (Finset α)) (A I : Finset α)
    (hI : I ⊆ A) :
    ∑ J ∈ (A \ I).powerset, (-1 : ℤ) ^ J.card * (((Q.filter (I ∪ J ⊆ ·))).card : ℤ) =
      ((Q.filter (fun B => A ∩ B = I)).card : ℤ) := by
  let R := (Q.filter (I ⊆ ·))
  have hfilter (J : Finset α) :
      (Q.filter (I ∪ J ⊆ ·)) = R.filter (J ⊆ ·) := by
    ext B
    simp only [R, mem_filter, union_subset_iff]
    tauto
  have hzero {B : Finset α} (hB : B ∈ R) : (A \ I) ∩ B = ∅ ↔ A ∩ B = I := by
    have hIB : I ⊆ B := (mem_filter.mp hB).2
    constructor
    · intro hempty
      apply Subset.antisymm
      · intro x hx
        by_contra hn
        obtain ⟨ha, hb⟩ := mem_inter.mp hx
        have hm : x ∈ (A \ I) ∩ B := mem_inter.mpr ⟨mem_sdiff.mpr ⟨ha, hn⟩, hb⟩
        simp [hempty] at hm
      · exact subset_inter hI hIB
    · intro heq
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      rcases mem_inter.mp hx with ⟨hd, hb⟩
      rcases mem_sdiff.mp hd with ⟨ha, hnot⟩
      exact hnot (heq ▸ mem_inter.mpr ⟨ha, hb⟩)
  calc
    _ = ∑ J ∈ (A \ I).powerset, ∑ B ∈ R, if J ⊆ B then (-1 : ℤ) ^ J.card else 0 := by
      apply sum_congr rfl
      intro J _
      rw [hfilter, ← sum_filter]
      simp [mul_comm]
    _ = ∑ B ∈ R, ∑ J ∈ (A \ I).powerset, if J ⊆ B then (-1 : ℤ) ^ J.card else 0 :=
      sum_comm
    _ = ∑ B ∈ R, if A ∩ B = I then (1 : ℤ) else 0 := by
      apply sum_congr rfl
      intro B hB
      rw [← sum_filter, show ((A \ I).powerset.filter (· ⊆ B)) = ((A \ I) ∩ B).powerset by
        ext J
        simp only [mem_filter, mem_powerset, Finset.subset_inter_iff], alternating_subsets]
      simp only [hzero hB]
    _ = _ := by
      rw [← sum_filter, show R.filter (fun B => A ∩ B = I) = Q.filter (fun B => A ∩ B = I) by
        ext B
        simp only [R, mem_filter, and_assoc]
        exact and_congr_right (fun _ => and_iff_right_of_imp (fun e => e ▸ inter_subset_right))]
      simp

private theorem top_count {Q : Finset (Finset α)} {A : Finset α} {k : ℕ}
    (hQ : ∀ B ∈ Q, B.card = k) (hA : A.card = k) :
    (((Q.filter (A ⊆ ·))).card : ℤ) = if A ∈ Q then 1 else 0 := by
  have hf : (Q.filter (A ⊆ ·)) = Q.filter (· = A) := by
    ext B
    simp only [mem_filter]
    exact and_congr_right fun hb =>
      ⟨fun h => (eq_of_subset_of_card_le h (by rw [hQ B hb, hA])).symm,
        fun h => h ▸ Subset.rfl⟩
  rw [hf]
  by_cases h : A ∈ Q
  · rw [if_pos h, show Q.filter (· = A) = {A} by
      ext B
      simp only [mem_filter, mem_singleton]
      exact ⟨And.right, fun e => ⟨e.symm ▸ h, e⟩⟩]
    simp
  · rw [if_neg h, show Q.filter (· = A) = ∅ by
      apply eq_empty_iff_forall_notMem.mpr
      intro B hB
      obtain ⟨hBQ, rfl⟩ := mem_filter.mp hB
      exact h hBQ]
    simp

private theorem design_trace_difference : OMA.R_Erdos835_johnson_chromaticNumber_R2.H2 := by
  classical
  intro n k F G hF hG hc A I hA hI
  rw [← alternating_counts F A I hI, ← alternating_counts G A I hI, ← sum_sub_distrib]
  rw [sum_eq_single (A \ I)]
  · rw [← mul_sub_left_distrib, union_sdiff_of_subset hI, top_count hF hA, top_count hG hA]
    congr 2
    have := card_sdiff_add_card_eq_card hI
    omega
  · intro J hJ hne
    have hs := mem_powerset.mp hJ
    have hu : I ∪ J ⊆ A := union_subset hI (hs.trans sdiff_subset)
    have hlt : (I ∪ J).card < k := by
      rw [← hA]
      apply card_lt_card
      refine Finset.ssubset_iff_subset_ne.mpr ⟨hu, ?_⟩
      intro heq
      apply hne
      apply Subset.antisymm hs
      intro x hx
      obtain ⟨hxA, hxI⟩ := mem_sdiff.mp hx
      exact (mem_union.mp (heq.symm ▸ hxA)).resolve_left hxI
    rw [proper_counts hF hG hc _ hlt, sub_self]
  · intro hm
    exact (hm (mem_powerset.mpr Subset.rfl)).elim

end Trace

/-- Restricting an antipodal coloring recovers all the exact trace quotas. -/
theorem half_from_full {k : ℕ} (hk : 1 ≤ k) (A : Finset (Fin (2*k))) (hA : A.card = k)
    (c : Finset (Fin (2*k)) → Fin (k+1))
    (hc : ∀ S T, S.card = k → T.card = k → (S ∩ T).card + 1 = k → c S ≠ c T)
    (ha : ∀ S, S.card = k → c Sᶜ = c S) :
    ∃ F : Fin (k+1) → Finset (Finset (Fin (2*k))),
      A ∈ F 0 ∧
      (∀ i B, B ∈ F i → B.card = k ∧ k ≤ 2*(A ∩ B).card) ∧
      (∀ B : Finset (Fin (2*k)), B.card = k → k ≤ 2*(A ∩ B).card →
        ∃! i, B ∈ F i) ∧
      (∀ i B C, B ∈ F i → C ∈ F i → (B ∩ C).card + 1 ≠ k) ∧
      (∀ i B, B ∈ F i → 2*(A ∩ B).card = k → Bᶜ ∈ F i) ∧
      (∀ I : Finset (Fin (2*k)), I ⊆ A → k ≤ 2*I.card → ∀ i,
        ((k : ℤ)+1) * ((F i).filter (fun B => A ∩ B = I)).card =
          (k.choose (k-I.card) : ℤ) +
            (-1 : ℤ)^(k-I.card) * (if i = 0 then (k : ℤ) else -1)) := by
  classical
  let C (S : Finset (Fin (2*k))) := Equiv.swap (c A) 0 (c S)
  have hC0 : C A = 0 := Equiv.swap_apply_left _ _
  have hcC (S T) (hS : S.card = k) (hT : T.card = k) (hST : (S ∩ T).card + 1 = k) :
      C S ≠ C T := fun e => hc S T hS hT hST ((Equiv.swap (c A) 0).injective e)
  let color : (johnson (2*k) k).Coloring (Fin (k+1)) :=
    SimpleGraph.Coloring.mk (fun S => C S.val) fun {v w} h =>
      hcC _ _ v.property w.property h
  let G (i : Fin (k+1)) :=
    (univ : Finset (Finset (Fin (2*k)))).filter (fun B => B.card = k ∧ C B = i)
  let F (i : Fin (k+1)) := (G i).filter (fun B => k ≤ 2*(A ∩ B).card)
  have gmem (i B) : B ∈ G i ↔ B.card = k ∧ C B = i := by
    simp [G]
  have fmem (i B) : B ∈ F i ↔ (B.card = k ∧ C B = i) ∧ k ≤ 2*(A ∩ B).card := by
    simp only [F, mem_filter, gmem]
  have fsize (i B) (h : B ∈ F i) : B.card = k ∧ k ≤ 2*(A ∩ B).card :=
    ⟨((fmem i B).mp h).1.1, ((fmem i B).mp h).2⟩
  have fpart (B : Finset (Fin (2*k))) (hB : B.card = k) (hhalf : k ≤ 2*(A ∩ B).card) :
      ∃! i, B ∈ F i :=
    ⟨C B, (fmem _ _).mpr ⟨⟨hB, rfl⟩, hhalf⟩, fun i hi => ((fmem i B).mp hi).1.2.symm⟩
  have star (i : Fin (k+1)) (T : Finset (Fin (2*k))) (hT : T.card = k-1) :
      ((G i).filter (T ⊆ ·)).card = 1 :=
    OMA.R_Erdos835_johnson_chromaticNumber_R2.star_count (by omega) color G
      (by
        intro j B
        rw [gmem]
        exact ⟨fun ⟨h, e⟩ => ⟨h, e⟩, fun ⟨h, e⟩ => ⟨h, e⟩⟩) i T hT
  have fcover (I : Finset (Fin (2*k))) (hI : k ≤ 2*I.card) (i : Fin (k+1)) :
      (F i).filter (fun B => A ∩ B = I) = (G i).filter (fun B => A ∩ B = I) := by
    ext B
    simp only [F, mem_filter, and_assoc]
    constructor
    · rintro ⟨h, _, he⟩
      exact ⟨h, he⟩
    · rintro ⟨h, he⟩
      exact ⟨h, he ▸ hI, he⟩
  refine ⟨F, (fmem 0 A).mpr ⟨⟨hA, hC0⟩, by simp [hA]; omega⟩, fsize, fpart, ?_, ?_, ?_⟩
  · intro i S T hs ht hj
    obtain ⟨⟨hS, hi⟩, _⟩ := (fmem i S).mp hs
    obtain ⟨⟨hT, hj'⟩, _⟩ := (fmem i T).mp ht
    exact hcC _ _ hS hT hj (hi.trans hj'.symm)
  · intro i B hb he
    obtain ⟨⟨hB, hi⟩, _⟩ := (fmem i B).mp hb
    have hsum := intersection_compl A B
    apply (fmem i Bᶜ).mpr
    refine ⟨⟨?_, ?_⟩, by omega⟩
    · rw [card_compl, Fintype.card_fin, hB]
      omega
    · exact (congrArg (Equiv.swap (c A) 0) (ha B hB)).trans hi
  · intro I hI hIhalf i
    have hdiff (j l : Fin (k+1)) :
        (((F j).filter (fun B => A ∩ B = I)).card : ℤ) -
          ((F l).filter (fun B => A ∩ B = I)).card =
            (-1 : ℤ)^(k-I.card) * ((if (0 : Fin (k+1)) = j then 1 else 0) -
              (if (0 : Fin (k+1)) = l then 1 else 0)) := by
      rw [fcover I hIhalf j, fcover I hIhalf l]
      have hh := design_trace_difference (2*k) k (G j) (G l)
        (fun B h => ((gmem j B).mp h).1) (fun B h => ((gmem l B).mp h).1)
        (fun T hT => ⟨star j T hT, star l T hT⟩) A I hA hI
      simpa only [gmem, hA, hC0, true_and] using hh
    have hquota := OMA.R_Erdos835_johnson_chromaticNumber_R2_H1_R1.trace_quota
      hA hI hIhalf F 0 (fun j B h => (fsize j B h).1) fpart hdiff i
    by_cases hi : i = 0
    · simp [hi] at hquota ⊢
      exact hquota
    · have hi' : (0 : Fin (k+1)) ≠ i := fun h => hi h.symm
      simpa [hi, hi'] using hquota

/-- The proposed half coloring is equivalent to the smaller system with
common missing colors. -/
theorem half_iff_two_points {k : ℕ} (hk : 3 ≤ k) (hodd : Odd (k+1))
    (A : Finset (Fin (2*k))) (hA : A.card = k) :
    (∃ F : Fin (k+1) → Finset (Finset (Fin (2*k))),
      A ∈ F 0 ∧
      (∀ i B, B ∈ F i → B.card = k ∧ k ≤ 2*(A ∩ B).card) ∧
      (∀ B : Finset (Fin (2*k)), B.card = k → k ≤ 2*(A ∩ B).card →
        ∃! i, B ∈ F i) ∧
      (∀ i B C, B ∈ F i → C ∈ F i → (B ∩ C).card + 1 ≠ k) ∧
      (∀ i B, B ∈ F i → 2*(A ∩ B).card = k → Bᶜ ∈ F i) ∧
      (∀ I : Finset (Fin (2*k)), I ⊆ A → k ≤ 2*I.card → ∀ i,
        ((k : ℤ)+1) * ((F i).filter (fun B => A ∩ B = I)).card =
          (k.choose (k-I.card) : ℤ) +
            (-1 : ℤ)^(k-I.card) * (if i = 0 then (k : ℤ) else -1))) ↔
    (∃ (c d : Finset (Fin (2*k - 2)) → Fin (k+1)),
      (∀ S T, S.card = k-1 → T.card = k-1 → (S ∩ T).card + 1 = k-1 → c S ≠ c T) ∧
      (∀ S, S.card = k-1 → c S ≠ c Sᶜ) ∧
      (∀ T S : Finset (Fin (2*k - 2)), T.card = k-2 → S.card = k-1 → T ⊆ S →
        c S ≠ d T ∧ c Sᶜ ≠ d T)) := by
  rw [← two_point_iff hk hodd]
  constructor
  · rintro ⟨F, _, _, hpart, hp, heq, _⟩
    have heven : Even k := by
      obtain ⟨t, ht⟩ := hodd
      exact ⟨t, by omega⟩
    exact extend_half heven A hA F hpart hp heq
  · rintro ⟨C, hc, ha⟩
    exact half_from_full (by omega) A hA C hc ha

theorem main : H1 → H2 → OMA.R_Erdos835_johnson_chromaticNumber_R2_H1_R1.H1 := by
  intro hsmall hlarge k hk hprime A hA hbad
  have hodd : Odd (k+1) := Nat.odd_iff.mpr
    ((Nat.Prime.mod_two_eq_one_iff_ne_two hprime).mpr (by omega))
  by_cases hk16 : 16 ≤ k
  · exact hlarge k hk16 hprime ((half_iff_two_points (by omega) hodd A hA).mp hbad)
  · obtain ⟨F, _, _, hpart, hproper, heq, _⟩ := hbad
    have heven : Even k := by
      obtain ⟨t, ht⟩ := hodd
      exact ⟨t, by omega⟩
    obtain ⟨c, hc, _⟩ := extend_half heven A hA F hpart hproper heq
    have hkSmall : k = 6 ∨ k = 10 ∨ k = 12 := by
      interval_cases k <;> first | decide | (exfalso; exact (by decide : ¬ Nat.Prime _) hprime)
    rcases hkSmall with rfl | rfl | rfl
    · exact hsmall.1 (derived_coloring (n := 10) (j := 4) (t := 2) (as_coloring c hc))
    · exact hsmall.2.1 (derived_coloring (n := 15) (j := 5) (t := 5) (as_coloring c hc))
    · exact hsmall.2.2 (derived_coloring (n := 17) (j := 5) (t := 7) (as_coloring c hc))

end Proof

end OMA.R_Erdos835_johnson_chromaticNumber_R2_H1_R1_H1_R1
