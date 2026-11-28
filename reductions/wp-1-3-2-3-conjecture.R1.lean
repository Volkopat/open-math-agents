import OMAStatements.S_wp_1_3_2_3_conjecture

-- Credit: @wispiANt
namespace OMA.R_wp_1_3_2_3_conjecture_R1

-- Linial's theorem below handles width at most two. On indecomposable
-- blocks of larger width, use the six-incomparable-elements split of #6209.
def H1 : Prop := ∀ (P : Type) [PartialOrder P] [Fintype P],
    (¬ ∀ x y : P, x ≤ y ∨ y ≤ x) →
    (¬ ∃ L : Set P, L.Nonempty ∧ (∃ y, y ∉ L) ∧
      ∀ x ∈ L, ∀ y ∉ L, x < y) →
    (∀ (e : P ≃o P) (x : P), e x = x) →
    (∃ a b c : P, (¬ a ≤ b ∧ ¬ b ≤ a) ∧ (¬ a ≤ c ∧ ¬ c ≤ a) ∧ (¬ b ≤ c ∧ ¬ c ≤ b)) →
    (∀ x : P, ({y : P | ¬ x ≤ y ∧ ¬ y ≤ x} : Set P).ncard ≤ 6) →
    (¬ ∃ x y : P, x ≠ y ∧ (∀ c : P, (c ⋖ x) ↔ (c ⋖ y)) ∧
      (∀ a b, x ≤ a → x ≤ b → a ≤ b ∨ b ≤ a) ∧
      (∀ a b, y ≤ a → y ≤ b → a ≤ b ∨ b ≤ a)) →
    (¬ ∃ x y : P, x ≠ y ∧ (∀ c : P, (x ⋖ c) ↔ (y ⋖ c)) ∧
      (∀ a b, a ≤ x → b ≤ x → a ≤ b ∨ b ≤ a) ∧
      (∀ a b, a ≤ y → b ≤ y → a ≤ b ∨ b ≤ a)) →
    (let count (extra : List (P × P)) :=
      Nat.card {σ : P ≃ Fin (Fintype.card P) //
        (∀ a b : P, a < b → σ a < σ b) ∧ ∀ c ∈ extra, σ c.1 < σ c.2}
     ¬ (∃ x y u v : P, x ≠ y ∧ u ≠ v ∧
      ∀ p ∈ [(x, y), (y, x)], ∀ q ∈ [(u, v), (v, u)],
        count [p] + count [p, q] ≤ count [])) →
    let ext : Finset (P ≃ Fin (Fintype.card P)) := by
      classical
      exact Finset.univ.filter (fun rank => StrictMono rank)
    ∃ x y : P, x ≠ y ∧
      let p := ((ext.filter (fun r => r x < r y)).card : ℚ) / ext.card
      1 / 3 ≤ p ∧ p ≤ 2 / 3

def H2 : Prop := ∀ (P : Type) [PartialOrder P] [Fintype P],
    (¬ ∀ x y : P, x ≤ y ∨ y ≤ x) →
    (¬ ∃ L : Set P, L.Nonempty ∧ (∃ y, y ∉ L) ∧
      ∀ x ∈ L, ∀ y ∉ L, x < y) →
    (∀ (e : P ≃o P) (x : P), e x = x) →
    (∃ a b c : P, (¬ a ≤ b ∧ ¬ b ≤ a) ∧ (¬ a ≤ c ∧ ¬ c ≤ a) ∧ (¬ b ≤ c ∧ ¬ c ≤ b)) →
    (∃ x : P, 7 ≤ ({y : P | ¬ x ≤ y ∧ ¬ y ≤ x} : Set P).ncard) →
    (¬ ∃ x y : P, x ≠ y ∧ (∀ c : P, (c ⋖ x) ↔ (c ⋖ y)) ∧
      (∀ a b, x ≤ a → x ≤ b → a ≤ b ∨ b ≤ a) ∧
      (∀ a b, y ≤ a → y ≤ b → a ≤ b ∨ b ≤ a)) →
    (¬ ∃ x y : P, x ≠ y ∧ (∀ c : P, (x ⋖ c) ↔ (y ⋖ c)) ∧
      (∀ a b, a ≤ x → b ≤ x → a ≤ b ∨ b ≤ a) ∧
      (∀ a b, a ≤ y → b ≤ y → a ≤ b ∨ b ≤ a)) →
    (let count (extra : List (P × P)) :=
      Nat.card {σ : P ≃ Fin (Fintype.card P) //
        (∀ a b : P, a < b → σ a < σ b) ∧ ∀ c ∈ extra, σ c.1 < σ c.2}
     ¬ (∃ x y u v : P, x ≠ y ∧ u ≠ v ∧
      ∀ p ∈ [(x, y), (y, x)], ∀ q ∈ [(u, v), (v, u)],
        count [p] + count [p, q] ≤ count [])) →
    let ext : Finset (P ≃ Fin (Fintype.card P)) := by
      classical
      exact Finset.univ.filter (fun rank => StrictMono rank)
    ∃ x y : P, x ≠ y ∧
      let p := ((ext.filter (fun r => r x < r y)).card : ℚ) / ext.card
      1 / 3 ≤ p ∧ p ≤ 2 / 3

-- Transport both extension counts along an order isomorphism. This lets
-- the two steps use small finite types even when the input lives higher.
lemma count_transport {A : Type*} {B : Type*} [PartialOrder A] [PartialOrder B]
    [Fintype A] [Fintype B] (e : A ≃o B) (x y : A) :
    let ea : Finset (A ≃ Fin (Fintype.card A)) := by
      classical
      exact Finset.univ.filter (fun r => StrictMono r)
    let eb : Finset (B ≃ Fin (Fintype.card B)) := by
      classical
      exact Finset.univ.filter (fun r => StrictMono r)
    ((ea.filter (fun r => r x < r y)).card : ℚ) / ea.card =
      ((eb.filter (fun r => r (e x) < r (e y))).card : ℚ) / eb.card := by
  classical
  intro ea eb
  let castRank := Fin.castOrderIso (Fintype.card_congr e.toEquiv)
  let transport := e.toEquiv.equivCongr castRank.toEquiv
  have evalRank (r : A ≃ Fin (Fintype.card A)) (b : B) :
      transport r b = castRank (r (e.symm b)) := rfl
  have mem (r : A ≃ Fin (Fintype.card A)) : r ∈ ea ↔ transport r ∈ eb := by
    simp only [ea, eb, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h a b hab
      rw [evalRank, evalRank]
      exact castRank.strictMono (h (e.symm.strictMono hab))
    · intro h a b hab
      have hlt := h (e.strictMono hab)
      simpa only [evalRank, e.symm_apply_apply, castRank.lt_iff_lt] using hlt
  have pair := Finset.card_equiv (s := ea.filter (fun r => r x < r y))
      (t := eb.filter (fun r => r (e x) < r (e y))) transport (by
        intro r
        simp only [Finset.mem_filter, ← mem, evalRank, e.symm_apply_apply, castRank.lt_iff_lt])
  rw [pair, Finset.card_equiv transport mem]

-- The rank-interval counting argument also appears in Samuel Schlesinger's
-- OneThirdTwoThirds/OrdinalSum.lean. Here the ranks are equivalences and
-- the partition is an arbitrary pair of factors of the ambient order.
-- Every rank in the lower factor is smaller than every rank in the upper
-- factor. Counting the ranks on either side pins down the boundary.
lemma factor_ranks {A B W : Type} [Fintype A] [Fintype B] [Fintype W]
    (parts : A ⊕ B ≃ W) (r : W ≃ Fin (Fintype.card W))
    (cross : ∀ a b, r (parts (.inl a)) < r (parts (.inr b))) :
    (∀ a, (r (parts (.inl a))).val < Fintype.card A) ∧
    (∀ b, Fintype.card A ≤ (r (parts (.inr b))).val) := by
  classical
  have size : Fintype.card W = Fintype.card A + Fintype.card B :=
    (Fintype.card_congr parts).symm.trans Fintype.card_sum
  constructor
  · intro a
    let v := r (parts (.inl a))
    let above (b : B) : Finset.Ioi v := ⟨r (parts (.inr b)), Finset.mem_Ioi.mpr (cross a b)⟩
    have inj : Function.Injective above := fun _ _ h =>
      Sum.inr_injective (parts.injective (r.injective (congrArg Subtype.val h)))
    have h := Fintype.card_le_of_injective above inj
    rw [Fintype.card_coe, Fin.card_Ioi] at h
    change v.val < Fintype.card A
    have := v.isLt
    omega
  · intro b
    let v := r (parts (.inr b))
    let below (a : A) : Finset.Iio v := ⟨r (parts (.inl a)), Finset.mem_Iio.mpr (cross a b)⟩
    have inj : Function.Injective below := fun _ _ h =>
      Sum.inl_injective (parts.injective (r.injective (congrArg Subtype.val h)))
    simpa only [Fintype.card_coe, Fin.card_Iio] using Fintype.card_le_of_injective below inj

lemma factor_extensions {A B W : Type} [PartialOrder A] [PartialOrder B] [PartialOrder W]
    [Fintype A] [Fintype B] [Fintype W] (parts : A ⊕ B ≃ W)
    (leftOrder : ∀ a a', parts (.inl a) < parts (.inl a') ↔ a < a')
    (rightOrder : ∀ b b', parts (.inr b) < parts (.inr b') ↔ b < b')
    (cross : ∀ a b, parts (.inl a) < parts (.inr b)) :
    let E (Q : Type) [PartialOrder Q] [Fintype Q] :=
      {r : Q ≃ Fin (Fintype.card Q) // StrictMono r}
    ∃ join : E A × E B ≃ E W, ∀ p,
      (∀ a, ((join p).val (parts (.inl a))).val = (p.1.val a).val) ∧
      (∀ b, ((join p).val (parts (.inr b))).val = Fintype.card A + (p.2.val b).val) := by
  classical
  intro E
  have size : Fintype.card A + Fintype.card B = Fintype.card W :=
    Fintype.card_sum.symm.trans (Fintype.card_congr parts)
  let concat (p : E A × E B) : W ≃ Fin (Fintype.card W) :=
    parts.symm.trans ((p.1.val.sumCongr p.2.val).trans (finSumFinEquiv.trans (finCongr size)))
  have leftVal (p : E A × E B) (a : A) :
      ((concat p) (parts (.inl a))).val = (p.1.val a).val := by
    simp [concat]
  have rightVal (p : E A × E B) (b : B) :
      ((concat p) (parts (.inr b))).val = Fintype.card A + (p.2.val b).val := by
    simp [concat]
  have mono (p : E A × E B) : StrictMono (concat p) := by
    intro x y h
    obtain ⟨a | b, rfl⟩ := parts.surjective x
    · obtain ⟨c | d, rfl⟩ := parts.surjective y
      · rw [Fin.lt_def, leftVal, leftVal]
        exact p.1.property ((leftOrder a c).1 h)
      · rw [Fin.lt_def, leftVal, rightVal]
        have := (p.1.val a).isLt
        omega
    · obtain ⟨c | d, rfl⟩ := parts.surjective y
      · exact ((cross c b).not_gt h).elim
      · rw [Fin.lt_def, rightVal, rightVal]
        exact Nat.add_lt_add_left (p.2.property ((rightOrder b d).1 h)) _
  let combine (p : E A × E B) : E W := ⟨concat p, mono p⟩
  have injective : Function.Injective combine := by
    intro p q h
    have valEq (w : W) := congrArg (fun z : E W => (z.val w).val) h
    apply Prod.ext
    · apply Subtype.ext
      apply Equiv.ext
      intro a
      apply Fin.ext
      exact (leftVal p a).symm.trans ((valEq (parts (.inl a))).trans (leftVal q a))
    · apply Subtype.ext
      apply Equiv.ext
      intro b
      apply Fin.ext
      apply Nat.add_left_cancel (n := Fintype.card A)
      exact (rightVal p b).symm.trans ((valEq (parts (.inr b))).trans (rightVal q b))
  have surjective : Function.Surjective combine := by
    rintro ⟨r, hr⟩
    obtain ⟨bottom, top⟩ := factor_ranks parts r (fun a b => hr (cross a b))
    let l (a : A) : Fin (Fintype.card A) := ⟨(r (parts (.inl a))).val, bottom a⟩
    let u (b : B) : Fin (Fintype.card B) :=
      ⟨(r (parts (.inr b))).val - Fintype.card A, by
        have := (r (parts (.inr b))).isLt
        have := top b
        omega⟩
    have li : Function.Injective l := by
      intro a a' h
      exact Sum.inl_injective (parts.injective (r.injective (Fin.ext (congrArg (fun z : Fin (Fintype.card A) => z.val) h))))
    have ui : Function.Injective u := by
      intro b b' h
      apply Sum.inr_injective
      apply parts.injective
      apply r.injective
      apply Fin.ext
      have hv := congrArg Fin.val h
      dsimp [u] at hv
      have := top b
      have := top b'
      omega
    let g := Equiv.ofBijective l ((Fintype.bijective_iff_injective_and_card l).2
      ⟨li, (Fintype.card_fin _).symm⟩)
    let k := Equiv.ofBijective u ((Fintype.bijective_iff_injective_and_card u).2
      ⟨ui, (Fintype.card_fin _).symm⟩)
    have gm : StrictMono g := fun {_ _} h => hr ((leftOrder _ _).2 h)
    have km : StrictMono k := by
      intro b b' h
      have lt := Fin.lt_def.mp (hr ((rightOrder _ _).2 h))
      change (r (parts (.inr b))).val - _ < (r (parts (.inr b'))).val - _
      have := top b
      omega
    let p : E A × E B := (⟨g, gm⟩, ⟨k, km⟩)
    refine ⟨p, Subtype.ext (Equiv.ext fun w => Fin.ext ?_)⟩
    obtain ⟨a | b, rfl⟩ := parts.surjective w
    · exact leftVal p a
    · rw [show ((combine p).val (parts (.inr b))).val = _ from rightVal p b]
      change Fintype.card A + ((r (parts (.inr b))).val - Fintype.card A) = (r (parts (.inr b))).val
      have := top b
      omega
  exact ⟨Equiv.ofBijective combine ⟨injective, surjective⟩, fun p => ⟨leftVal p, rightVal p⟩⟩

lemma rank_exists (Q : Type) [PartialOrder Q] [Fintype Q] :
    Nonempty {r : Q ≃ Fin (Fintype.card Q) // StrictMono r} := by
  classical
  let : Fintype (LinearExtension Q) := inferInstanceAs (Fintype Q)
  let sort := (Fintype.orderIsoFinOfCardEq (LinearExtension Q)
    (show Fintype.card (LinearExtension Q) = Fintype.card Q from rfl)).symm
  let r : Q ≃ Fin (Fintype.card Q) := (Equiv.refl Q).trans sort.toEquiv
  have strict : StrictMono (toLinearExtension : Q → LinearExtension Q) :=
    toLinearExtension.monotone.strictMono_of_injective (fun _ _ h => h)
  exact ⟨⟨r, sort.strictMono.comp strict⟩⟩

-- Counting a predicate depending only on the first coordinate multiplies
-- its numerator and denominator by the size of the second coordinate.
lemma uniform_factor {A B W : Type} [Fintype A] [Fintype B] [Fintype W] [Nonempty B]
    (join : A × B ≃ W) (localEvent : A → Prop) (wholeEvent : W → Prop)
    [DecidablePred localEvent] [DecidablePred wholeEvent]
    (event : ∀ p, localEvent p.1 ↔ wholeEvent (join p)) :
    ((Finset.univ.filter localEvent).card : ℚ) / Fintype.card A =
      ((Finset.univ.filter wholeEvent).card : ℚ) / Fintype.card W := by
  classical
  have num := Finset.card_equiv
    (s := (Finset.univ.filter localEvent) ×ˢ (Finset.univ : Finset B))
    (t := Finset.univ.filter wholeEvent) join (by
      intro p
      simpa only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, and_true]
        using event p)
  rw [Finset.card_product, Finset.card_univ] at num
  have den := Fintype.card_congr join
  rw [Fintype.card_prod] at den
  rw [← num, ← den, Nat.cast_mul, Nat.cast_mul]
  exact (mul_div_mul_right _ _ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)).symm

lemma rank_event (Q : Type) [PartialOrder Q] [Fintype Q] (x y : Q) :
    let E := {r : Q ≃ Fin (Fintype.card Q) // StrictMono r}
    let ext : Finset (Q ≃ Fin (Fintype.card Q)) := by
      classical
      exact Finset.univ.filter (fun r => StrictMono r)
    letI : Fintype E := by classical exact inferInstanceAs (Fintype {r : Q ≃ Fin _ // StrictMono r})
    ((ext.filter (fun r => r x < r y)).card : ℚ) / ext.card =
      ((Finset.univ.filter (fun r : E => r.val x < r.val y)).card : ℚ) / Fintype.card E := by
  classical
  intro E ext
  have den : Fintype.card E = ext.card := Fintype.card_of_subtype ext (by simp [ext])
  have num : (Finset.univ.filter (fun r : E => r.val x < r.val y)).card =
      (ext.filter (fun r => r x < r y)).card := by
    apply Finset.card_bij (fun r _ => r.val)
    · intro r hr
      exact Finset.mem_filter.mpr ⟨by simpa [ext] using r.property, (Finset.mem_filter.mp hr).2⟩
    · intro r _ s _ eq
      exact Subtype.ext eq
    · intro r hr
      obtain ⟨he, hxy⟩ := Finset.mem_filter.mp hr
      exact ⟨⟨r, by simpa [ext] using he⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxy⟩, rfl⟩
  rw [den, num]

lemma cut_probabilities {A B W : Type} [PartialOrder A] [PartialOrder B] [PartialOrder W]
    [Fintype A] [Fintype B] [Fintype W] (parts : A ⊕ B ≃ W)
    (leftOrder : ∀ a a', parts (.inl a) < parts (.inl a') ↔ a < a')
    (rightOrder : ∀ b b', parts (.inr b) < parts (.inr b') ↔ b < b')
    (cross : ∀ a b, parts (.inl a) < parts (.inr b)) :
    let prob (Q : Type) [PartialOrder Q] [Fintype Q] (x y : Q) : ℚ :=
      let ext : Finset (Q ≃ Fin (Fintype.card Q)) := by
        classical
        exact Finset.univ.filter (fun r => StrictMono r)
      ((ext.filter (fun r => r x < r y)).card : ℚ) / ext.card
    (∀ a c : A, prob A a c = prob W (parts (.inl a)) (parts (.inl c))) ∧
    (∀ b d : B, prob B b d = prob W (parts (.inr b)) (parts (.inr d))) := by
  classical
  intro prob
  let E (Q : Type) [PartialOrder Q] [Fintype Q] := {r : Q ≃ Fin (Fintype.card Q) // StrictMono r}
  let : Nonempty (E A) := rank_exists A
  let : Nonempty (E B) := rank_exists B
  obtain ⟨join, ranks⟩ := factor_extensions parts leftOrder rightOrder cross
  constructor
  · intro a c
    refine (rank_event A a c).trans (Eq.trans ?_ (rank_event W _ _).symm)
    apply uniform_factor join
    intro p
    simp only [Fin.lt_def, (ranks p).1]
  · intro b d
    refine (rank_event B b d).trans (Eq.trans ?_ (rank_event W _ _).symm)
    apply uniform_factor ((Equiv.prodComm (E B) (E A)).trans join)
    intro p
    change (p.1.val b).val < (p.1.val d).val ↔
      ((join (p.2, p.1)).val (parts (.inr b))).val < ((join (p.2, p.1)).val (parts (.inr d))).val
    simp only [(ranks (p.2, p.1)).2, Nat.add_lt_add_iff_left]

-- A single cut preserves the probability of every comparison inside either side.
lemma cut_identity :
  let prob (Q : Type) [PartialOrder Q] [Fintype Q] (x y : Q) : ℚ :=
    let ext : Finset (Q ≃ Fin (Fintype.card Q)) := by
      classical
      exact Finset.univ.filter (fun rank => StrictMono rank)
    ((ext.filter (fun rank => rank x < rank y)).card : ℚ) / ext.card
  ∀ (P : Type) [PartialOrder P] (S T : Finset P) (sub : T ⊂ S),
    ((∀ x ∈ T, ∀ y ∈ S, y ∉ T → x < y) ∨
     (∀ x ∈ T, ∀ y ∈ S, y ∉ T → y < x)) →
    ∀ x y : T, prob T x y =
      prob S ⟨x.val, sub.1 x.property⟩ ⟨y.val, sub.1 y.property⟩ := by
  classical
  intro prob P _ S T sub side x y
  let B := {z : S // z.val ∉ T}
  let inc : T ≃ {z : S // z.val ∈ T} :=
    { toFun := fun a => ⟨⟨a.val, sub.1 a.property⟩, a.property⟩
      invFun := fun z => ⟨z.val.val, z.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let parts : T ⊕ B ≃ S :=
    (inc.sumCongr (Equiv.refl B)).trans (Equiv.sumCompl (fun z : S => z.val ∈ T))
  rcases side with lower | upper
  · exact (cut_probabilities parts (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl)
      (fun a b => lower a.val a.property b.val.val b.val.property b.property)).1 x y
  · let rev := (Equiv.sumComm B T).trans parts
    exact (cut_probabilities rev (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl)
      (fun b a => upper a.val a.property b.val.val b.val.property b.property)).2 x y

-- Keep an incomparable pair together while taking a strictly smaller side.
lemma retain_pair {P : Type} [PartialOrder P] (S : Finset P) (a b : S)
    (hab : ¬ a ≤ b) (hba : ¬ b ≤ a) (L : Set S)
    (lo : L.Nonempty) (hi : ∃ y, y ∉ L) (cut : ∀ x ∈ L, ∀ y ∉ L, x < y) :
    ∃ T : Finset P, T ⊂ S ∧ a.val ∈ T ∧ b.val ∈ T ∧
      ((∀ x ∈ T, ∀ y ∈ S, y ∉ T → x < y) ∨
       (∀ x ∈ T, ∀ y ∈ S, y ∉ T → y < x)) := by
  classical
  have takeSide (D : Set S) (ha : a ∈ D) (hb : b ∈ D) (proper : ∃ z, z ∉ D)
      (side : (∀ x ∈ D, ∀ y ∉ D, x < y) ∨ (∀ x ∈ D, ∀ y ∉ D, y < x)) :
      ∃ T : Finset P, T ⊂ S ∧ a.val ∈ T ∧ b.val ∈ T ∧
        ((∀ x ∈ T, ∀ y ∈ S, y ∉ T → x < y) ∨
         (∀ x ∈ T, ∀ y ∈ S, y ∉ T → y < x)) := by
    let T := S.filter (fun x => ∃ h : x ∈ S, (⟨x, h⟩ : S) ∈ D)
    have incl : T ⊆ S := Finset.filter_subset _ _
    have mem (x : S) : x.val ∈ T ↔ x ∈ D := by simp [T, x.property]
    obtain ⟨z, hz⟩ := proper
    refine ⟨T, (Finset.ssubset_iff_of_subset incl).2 ⟨z.val, z.property, fun h => hz ((mem z).1 h)⟩,
      (mem a).2 ha, (mem b).2 hb, ?_⟩
    rcases side with h | h
    · left
      intro x hx y hy outside
      exact h ⟨x, incl hx⟩ ((mem _).1 hx) ⟨y, hy⟩ (fun h => outside ((mem _).2 h))
    · right
      intro x hx y hy outside
      exact h ⟨x, incl hx⟩ ((mem _).1 hx) ⟨y, hy⟩ (fun h => outside ((mem _).2 h))
  by_cases ha : a ∈ L
  · apply takeSide L ha _ hi (Or.inl cut)
    by_contra hb
    exact hab (cut a ha b hb).le
  · apply takeSide Lᶜ ha
    · intro hb
      exact hba (cut b hb a ha).le
    · obtain ⟨z, hz⟩ := lo
      exact ⟨z, fun h => h hz⟩
    · right
      intro x hx y hy
      exact cut y (by simpa using hy) x hx

lemma select_block :
  let prob (Q : Type) [PartialOrder Q] [Fintype Q] (x y : Q) : ℚ :=
    let ext : Finset (Q ≃ Fin (Fintype.card Q)) := by
      classical
      exact Finset.univ.filter (fun rank => StrictMono rank)
    ((ext.filter (fun rank => rank x < rank y)).card : ℚ) / ext.card
  ∀ (P : Type) [PartialOrder P] [Fintype P],
    (¬ ∀ x y : P, x ≤ y ∨ y ≤ x) →
    ∃ S : Finset P,
      (¬ ∀ x y : S, x ≤ y ∨ y ≤ x) ∧
      (¬ ∃ L : Set S, L.Nonempty ∧ (∃ y, y ∉ L) ∧
        ∀ x ∈ L, ∀ y ∉ L, x < y) ∧
      ∀ x y : S, prob S x y = prob P x.val y.val := by
  classical
  intro prob P _ _ nonchain
  obtain ⟨a, b, hab, hba⟩ : ∃ a b : P, ¬ a ≤ b ∧ ¬ b ≤ a := by
    by_contra! h
    exact nonchain (fun a b => or_iff_not_imp_left.mpr (h a b))
  let preservesProb (S : Finset P) := ∀ x y : S, prob S x y = prob P x.val y.val
  have descend (S : Finset P) (ha : a ∈ S) (hb : b ∈ S) (hg : preservesProb S) :
      ∃ T : Finset P, (¬ ∀ x y : T, x ≤ y ∨ y ≤ x) ∧
        (¬ ∃ L : Set T, L.Nonempty ∧ (∃ y, y ∉ L) ∧ ∀ x ∈ L, ∀ y ∉ L, x < y) ∧ preservesProb T := by
    induction S using Finset.strongInductionOn with
    | _ S ih =>
      by_cases split : ∃ L : Set S, L.Nonempty ∧ (∃ y, y ∉ L) ∧ ∀ x ∈ L, ∀ y ∉ L, x < y
      · obtain ⟨L, lo, hi, cut⟩ := split
        obtain ⟨T, sub, haT, hbT, side⟩ := retain_pair S ⟨a, ha⟩ ⟨b, hb⟩ hab hba L lo hi cut
        apply ih T sub haT hbT
        intro x y
        exact (cut_identity P S T sub side x y).trans (hg _ _)
      · exact ⟨S, fun total => (total ⟨a, ha⟩ ⟨b, hb⟩).elim hab hba, split, hg⟩
  let e : (Finset.univ : Finset P) ≃o P :=
    { toFun := Subtype.val
      invFun := fun x => ⟨x, Finset.mem_univ x⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  exact descend Finset.univ (Finset.mem_univ _) (Finset.mem_univ _)
    (fun x y => count_transport e x y)

lemma transfer_bounds {p q : ℚ} (h : p = q) (bounds : 1 / 3 ≤ p ∧ p ≤ 2 / 3) :
    1 / 3 ≤ q ∧ q ≤ 2 / 3 := h ▸ bounds

-- Translate rank bijections into the one-based natural-valued functions used
-- in PR #8413, preserving the denominator and every comparison numerator.
lemma rank_shift_counts (P : Type) [PartialOrder P] [Fintype P] :
    let ranks : Finset (P ≃ Fin (Fintype.card P)) := by
      classical
      exact Finset.univ.filter (fun r => StrictMono r)
    let ext := {f : P → ℕ | Monotone f ∧ Set.range f = Set.Icc 1 (Nat.card P)}
    ext.ncard = ranks.card ∧ ∀ x y : P,
      {f ∈ ext | f x < f y}.ncard = (ranks.filter (fun r => r x < r y)).card := by
  classical
  intro ranks ext
  let shift (r : P ≃ Fin (Fintype.card P)) (z : P) := (r z).val + 1
  have inj : Function.Injective shift := by
    intro r s h
    apply Equiv.ext
    intro z
    exact Fin.ext (Nat.succ.inj (congrFun h z))
  have image : shift '' (↑ranks : Set _) = ext := by
    ext f
    constructor
    · rintro ⟨r, hr, rfl⟩
      have hm : StrictMono r := by simpa [ranks] using hr
      constructor
      · intro a b hab
        exact Nat.succ_le_succ (hm.monotone hab)
      · ext k
        constructor
        · rintro ⟨z, rfl⟩
          exact ⟨Nat.le_add_left 1 _, by
            rw [Nat.card_eq_fintype_card]
            exact (r z).isLt⟩
        · rintro ⟨lo, hi⟩
          rw [Nat.card_eq_fintype_card] at hi
          let j : Fin (Fintype.card P) := ⟨k - 1, by omega⟩
          refine ⟨r.symm j, ?_⟩
          change (r (r.symm j)).val + 1 = k
          rw [r.apply_symm_apply]
          dsimp [j]
          omega
    · rintro ⟨hm, range_f⟩
      have bounds (z : P) : 1 ≤ f z ∧ f z ≤ Fintype.card P := by
        have h : f z ∈ Set.range f := Set.mem_range_self z
        rw [range_f, Nat.card_eq_fintype_card] at h
        exact h
      let raw (z : P) : Fin (Fintype.card P) := ⟨f z - 1, by have := bounds z; omega⟩
      have onto : Function.Surjective raw := by
        intro j
        have hj : j.val + 1 ∈ Set.range f := by
          rw [range_f, Nat.card_eq_fintype_card]
          exact ⟨Nat.le_add_left 1 _, j.isLt⟩
        obtain ⟨z, hz⟩ := hj
        exact ⟨z, Fin.ext (by simp [raw, hz])⟩
      have bij := (Fintype.bijective_iff_surjective_and_card raw).2
        ⟨onto, (Fintype.card_fin _).symm⟩
      let r := Equiv.ofBijective raw bij
      have project (z : P) : shift r z = f z := by
        change (f z - 1) + 1 = f z
        have := bounds z
        omega
      have mono : Monotone raw := fun _ _ h => Nat.sub_le_sub_right (hm h) 1
      refine ⟨r, ?_, funext project⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, mono.strictMono_of_injective bij.injective⟩
  constructor
  · rw [← image, Set.ncard_image_of_injective _ inj, Set.ncard_coe_finset]
  · intro x y
    have before : shift '' (↑(ranks.filter (fun r => r x < r y)) : Set _) =
        {f ∈ ext | f x < f y} := by
      ext f
      constructor
      · rintro ⟨r, hr, rfl⟩
        obtain ⟨hr, hxy⟩ := Finset.mem_filter.mp hr
        exact ⟨image ▸ ⟨r, hr, rfl⟩, Nat.succ_lt_succ hxy⟩
      · rintro ⟨hf, hxy⟩
        rw [← image] at hf
        obtain ⟨r, hr, rfl⟩ := hf
        exact ⟨r, Finset.mem_filter.mpr ⟨hr, Nat.lt_of_succ_lt_succ hxy⟩, rfl⟩
    rw [← before, Set.ncard_image_of_injective _ inj, Set.ncard_coe_finset]

-- Linial's width-two argument, adapted from @sobrien032's merged proof in
-- open-math-agents PR #8413. The sets below use its one-based coordinates.
namespace WidthTwo

lemma ext_injective {P : Type} [Fintype P] [PartialOrder P] :
    let Ext := {f : P → ℕ | Monotone f ∧ Set.range f = Set.Icc 1 (Nat.card P)}
    ∀ {f : P → ℕ}, f ∈ Ext → Function.Injective f := by
  intro Ext f hf
  have h : (f '' Set.univ).ncard = (Set.univ : Set P).ncard := by
    rw [Set.image_univ, hf.2, Set.ncard_univ, ← Finset.coe_Icc, Set.ncard_coe_finset, Nat.card_Icc]
    omega
  exact Set.injOn_univ.1 (Set.injOn_of_ncard_image_eq h)

lemma ext_finite {P : Type} [Fintype P] [PartialOrder P] :
    let Ext := {f : P → ℕ | Monotone f ∧ Set.range f = Set.Icc 1 (Nat.card P)}
    Ext.Finite := by
  intro Ext
  have h : (Set.pi Set.univ (fun _ : P => Set.Icc 1 (Nat.card P))).Finite :=
    Set.Finite.pi (fun _ => Set.finite_Icc 1 (Nat.card P))
  refine h.subset ?_
  intro f hf p _
  rw [← hf.2]
  exact Set.mem_range_self p

-- If p is the last incomparable element before x, the two are adjacent.
-- Swapping them injects the last-position class L into the before-class A.
lemma ncard_le_two_mul {P : Type} [Fintype P] [PartialOrder P] :
    let Ext := {f : P → ℕ | Monotone f ∧ Set.range f = Set.Icc 1 (Nat.card P)}
    let A (x y : P) := {f ∈ Ext | f x < f y}
    let L (x p : P) := {f ∈ Ext | f p < f x ∧ ∀ w, ¬ w ≤ x → ¬ x ≤ w → p < w → f x < f w}
    ∀ {x : P} (_hmin : ∀ z, z < x → ∀ v, z ≤ v ∨ v ≤ z)
    (_hchain : ∀ y y', ¬ y ≤ x → ¬ x ≤ y → ¬ y' ≤ x → ¬ x ≤ y' → y ≤ y' ∨ y' ≤ y)
    {p : P} (_hpx : ¬ p ≤ x) (_hxp : ¬ x ≤ p) {S : Set (P → ℕ)} (_hS : S ⊆ A x p ∪ L x p),
      S.ncard ≤ 2 * (A x p).ncard := by
  classical
  intro Ext A L
  have ext_strictMono {f : P → ℕ} (hf : f ∈ Ext) :
      StrictMono f :=
    hf.1.strictMono_of_injective (ext_injective hf)
  have ext_mem_Icc {f : P → ℕ} (hf : f ∈ Ext) (p : P) :
      1 ≤ f p ∧ f p ≤ Nat.card P := by
    have h : f p ∈ Set.Icc 1 (Nat.card P) := by
      rw [← hf.2]
      exact Set.mem_range_self p
    exact h
  have ext_surj {f : P → ℕ} (hf : f ∈ Ext) {k : ℕ}
      (h1 : 1 ≤ k) (h2 : k ≤ Nat.card P) : ∃ q, f q = k := by
    have h : k ∈ Set.range f := by
      rw [hf.2]
      exact ⟨h1, h2⟩
    exact h
  have swap_mem {f : P → ℕ}
      (hf : f ∈ Ext) {a b : P} (hab : ¬ a ≤ b) (hba : ¬ b ≤ a) (h : f b = f a + 1) :
      f ∘ Equiv.swap a b ∈ Ext := by
    have hs := ext_strictMono hf
    have hm := hf.1
    have e1 : Equiv.swap a b a = b := Equiv.swap_apply_left a b
    have e2 : Equiv.swap a b b = a := Equiv.swap_apply_right a b
    have e3 : ∀ q, q ≠ a → q ≠ b → Equiv.swap a b q = q :=
      fun q h1 h2 => Equiv.swap_apply_of_ne_of_ne h1 h2
    refine ⟨?_, ?_⟩
    · intro q r hqr
      show f (Equiv.swap a b q) ≤ f (Equiv.swap a b r)
      by_cases hqa : q = a
      · rw [hqa] at hqr ⊢
        rw [e1]
        by_cases hra : r = a
        · rw [hra, e1]
        · by_cases hrb : r = b
          · rw [hrb] at hqr
            exact absurd hqr hab
          · rw [e3 r hra hrb]
            have := hs (lt_of_le_of_ne hqr (Ne.symm hra))
            omega
      · by_cases hqb : q = b
        · rw [hqb] at hqr ⊢
          rw [e2]
          by_cases hra : r = a
          · rw [hra] at hqr
            exact absurd hqr hba
          · by_cases hrb : r = b
            · rw [hrb, e2]
            · rw [e3 r hra hrb]
              have := hm hqr
              omega
        · rw [e3 q hqa hqb]
          by_cases hra : r = a
          · rw [hra] at hqr ⊢
            rw [e1]
            have := hm hqr
            omega
          · by_cases hrb : r = b
            · rw [hrb] at hqr ⊢
              rw [e2]
              have := hs (lt_of_le_of_ne hqr hqb)
              omega
            · rw [e3 r hra hrb]
              exact hm hqr
    · rw [(Equiv.swap a b).surjective.range_comp f]
      exact hf.2
  have adjacent {x : P}
      (hmin : ∀ z, z < x → ∀ v, z ≤ v ∨ v ≤ z)
      (hchain : ∀ y y', ¬ y ≤ x → ¬ x ≤ y → ¬ y' ≤ x → ¬ x ≤ y' → y ≤ y' ∨ y' ≤ y)
    {f : P → ℕ} (hf : f ∈ Ext) {p : P} (hpx : ¬ p ≤ x) (hxp : ¬ x ≤ p)
      (hlt : f p < f x) (hlast : ∀ w, ¬ w ≤ x → ¬ x ≤ w → p < w → f x < f w) :
      f x = f p + 1 := by
    by_contra hne
    have hgap : f p + 1 < f x := by omega
    have hxn := (ext_mem_Icc hf x).2
    obtain ⟨q, hq⟩ := ext_surj hf (k := f p + 1) (by omega) (by omega)
    have hm := hf.1
    by_cases hqx : q ≤ x
    · have hqne : q ≠ x := by
        intro hqe
        rw [hqe] at hq
        omega
      rcases hmin q (lt_of_le_of_ne hqx hqne) p with h | h
      · have := hm h
        omega
      · exact hpx (le_trans h hqx)
    · by_cases hxq : x ≤ q
      · have := hm hxq
        omega
      · rcases hchain q p hqx hxq hpx hxp with h | h
        · have := hm h
          omega
        · have hpq : p ≠ q := by
            intro hpe
            rw [hpe] at hq
            omega
          have := hlast q hqx hxq (lt_of_le_of_ne h hpq)
          omega
  have ncard_L_le {x : P}
      (hmin : ∀ z, z < x → ∀ v, z ≤ v ∨ v ≤ z)
      (hchain : ∀ y y', ¬ y ≤ x → ¬ x ≤ y → ¬ y' ≤ x → ¬ x ≤ y' → y ≤ y' ∨ y' ≤ y)
    {p : P} (hpx : ¬ p ≤ x) (hxp : ¬ x ≤ p) : (L x p).ncard ≤ (A x p).ncard := by
    classical
    refine Set.ncard_le_ncard_of_injOn (fun f => f ∘ Equiv.swap p x) ?_ ?_
      ((ext_finite (P := P)).subset fun f hf => hf.1)
    · rintro f ⟨hf, hlt, hlast⟩
      have hadj := adjacent hmin hchain hf hpx hxp hlt hlast
      refine ⟨swap_mem hf hpx hxp hadj, ?_⟩
      show f (Equiv.swap p x x) < f (Equiv.swap p x p)
      rw [Equiv.swap_apply_right, Equiv.swap_apply_left]
      exact hlt
    · intro f _ g _ hfg
      exact (Equiv.swap p x).surjective.injective_comp_right hfg
  intro x hmin hchain p hpx hxp S hS
  have hfinA : (A x p).Finite := (ext_finite (P := P)).subset fun f hf => hf.1
  have hfinL : (L x p).Finite := (ext_finite (P := P)).subset fun f hf => hf.1
  have h1 : S.ncard ≤ (A x p ∪ L x p).ncard := Set.ncard_le_ncard hS (hfinA.union hfinL)
  have h2 : (A x p ∪ L x p).ncard ≤ (A x p).ncard + (L x p).ncard := Set.ncard_union_le _ _
  have h3 := ncard_L_le hmin hchain hpx hxp
  omega

-- Follow the chain of elements incomparable to x until the count crosses one third.
lemma core {P : Type} [Fintype P] [PartialOrder P] :
    let Ext := {f : P → ℕ | Monotone f ∧ Set.range f = Set.Icc 1 (Nat.card P)}
    let A (x y : P) := {f ∈ Ext | f x < f y}
    ∀ (_hw : ∀ a b c : P, a ≤ b ∨ b ≤ a ∨ a ≤ c ∨ c ≤ a ∨ b ≤ c ∨ c ≤ b)
    {x : P} (_hmin : ∀ z, z < x → ∀ v, z ≤ v ∨ v ≤ z)
    {y0 : P} (_hy0 : ¬ y0 ≤ x) (_hy0' : ¬ x ≤ y0)
    (_h0 : 3 * (A x y0).ncard ≤ 2 * Ext.ncard),
      ∃ y, Ext.ncard ≤ 3 * (A x y).ncard ∧ 3 * (A x y).ncard ≤ 2 * Ext.ncard := by
  classical
  intro Ext A hw x hmin y0 hy0 hy0' h0
  let L (x p : P) := {f ∈ Ext | f p < f x ∧ ∀ w, ¬ w ≤ x → ¬ x ≤ w → p < w → f x < f w}
  have hchain : ∀ y y', ¬ y ≤ x → ¬ x ≤ y → ¬ y' ≤ x → ¬ x ≤ y' → y ≤ y' ∨ y' ≤ y := by
    intro y y' h1 h2 h3 h4
    rcases hw x y y' with h | h | h | h | h | h
    · exact absurd h h2
    · exact absurd h h1
    · exact absurd h h4
    · exact absurd h h3
    · exact Or.inl h
    · exact Or.inr h
  by_cases hB : ∃ w, ¬ w ≤ x ∧ ¬ x ≤ w ∧ 3 * (A x w).ncard < Ext.ncard
  · obtain ⟨p, ⟨hpx, hxp, hp3⟩, hpmax⟩ := (wellFounded_gt (α := P)).has_min
      {w | ¬ w ≤ x ∧ ¬ x ≤ w ∧ 3 * (A x w).ncard < Ext.ncard} hB
    have hpne : p ≠ x := fun h => hpx (le_of_eq h)
    by_cases hS : ∃ w, ¬ w ≤ x ∧ ¬ x ≤ w ∧ p < w
    · obtain ⟨y, ⟨hyx, hxy, hpy⟩, hymin⟩ := (wellFounded_lt (α := P)).has_min
        {w | ¬ w ≤ x ∧ ¬ x ≤ w ∧ p < w} hS
      refine ⟨y, ?_, ?_⟩
      · by_contra hlt
        exact hpmax y ⟨hyx, hxy, by omega⟩ hpy
      · have hsub : A x y ⊆ A x p ∪ L x p := by
          rintro f ⟨hf, hlt⟩
          by_cases h : f x < f p
          · exact Or.inl ⟨hf, h⟩
          · refine Or.inr ⟨hf, ?_, ?_⟩
            · have hne : f p ≠ f x := fun h' => hpne (ext_injective hf h')
              omega
            · intro w hwx hxw hpw
              have hyw : y ≤ w := by
                rcases hchain y w hyx hxy hwx hxw with h' | h'
                · exact h'
                · by_contra hnot
                  exact hymin w ⟨hwx, hxw, hpw⟩ (lt_of_le_not_ge h' hnot)
              exact lt_of_lt_of_le hlt (hf.1 hyw)
        have : (A x y).ncard ≤ 2 * (A x p).ncard := ncard_le_two_mul hmin hchain hpx hxp hsub
        omega
    · exfalso
      have hsub : Ext ⊆ A x p ∪ L x p := by
        intro f hf
        by_cases h : f x < f p
        · exact Or.inl ⟨hf, h⟩
        · refine Or.inr ⟨hf, ?_, ?_⟩
          · have hne : f p ≠ f x := fun h' => hpne (ext_injective hf h')
            omega
          · intro w hwx hxw hpw
            exact absurd ⟨w, hwx, hxw, hpw⟩ hS
      have : Ext.ncard ≤ 2 * (A x p).ncard := ncard_le_two_mul hmin hchain hpx hxp hsub
      omega
  · refine ⟨y0, ?_, h0⟩
    by_contra hlt
    exact hB ⟨y0, hy0, hy0', by omega⟩

-- Choose a minimal element with an incomparable partner. Either orientation
-- supplies the starting bound for the chain argument.
lemma linial {P : Type} [Fintype P] [PartialOrder P] :
    let Ext := {f : P → ℕ | Monotone f ∧ Set.range f = Set.Icc 1 (Nat.card P)}
    let A (x y : P) := {f ∈ Ext | f x < f y}
    ∀ (_hnt : ¬ Std.Total (α := P) (· ≤ ·))
    (_hw : ∀ a b c : P, a ≤ b ∨ b ≤ a ∨ a ≤ c ∨ c ≤ a ∨ b ≤ c ∨ c ≤ b),
      ∃ x y : P, Ext.ncard ≤ 3 * (A x y).ncard ∧ 3 * (A x y).ncard ≤ 2 * Ext.ncard := by
  classical
  intro Ext A hnt hw
  have hN : ∃ a : P, ∃ b, ¬ a ≤ b ∧ ¬ b ≤ a := by
    by_contra h
    apply hnt
    constructor
    intro a b
    by_contra h'
    exact h ⟨a, b, fun hab => h' (Or.inl hab), fun hba => h' (Or.inr hba)⟩
  obtain ⟨x, ⟨u, hxu, hux⟩, hxmin⟩ := (wellFounded_lt (α := P)).has_min
    {a | ∃ b, ¬ a ≤ b ∧ ¬ b ≤ a} hN
  have hmin : ∀ z, z < x → ∀ v, z ≤ v ∨ v ≤ z := by
    intro z hz v
    by_contra h
    exact hxmin z ⟨v, fun h1 => h (Or.inl h1), fun h2 => h (Or.inr h2)⟩ hz
  obtain ⟨m, ⟨hmx, hxm⟩, hmmin⟩ := (wellFounded_lt (α := P)).has_min
    {w | ¬ w ≤ x ∧ ¬ x ≤ w} ⟨u, hux, hxu⟩
  by_cases h : 3 * (A x m).ncard ≤ 2 * Ext.ncard
  · obtain ⟨y, hy⟩ := core hw hmin hmx hxm h
    exact ⟨x, y, hy⟩
  · have hleast : ∀ w, ¬ w ≤ x → ¬ x ≤ w → m ≤ w := by
      intro w hwx hxw
      rcases hw x m w with h' | h' | h' | h' | h' | h'
      · exact absurd h' hxm
      · exact absurd h' hmx
      · exact absurd h' hxw
      · exact absurd h' hwx
      · exact h'
      · by_contra hnot
        exact hmmin w ⟨hwx, hxw⟩ (lt_of_le_not_ge h' hnot)
    have hmin' : ∀ z, z < m → ∀ v, z ≤ v ∨ v ≤ z := by
      intro z hz v
      by_cases hzx : z ≤ x
      · have hzne : z ≠ x := by
          intro hze
          rw [hze] at hz
          exact hxm (le_of_lt hz)
        exact hmin z (lt_of_le_of_ne hzx hzne) v
      · by_cases hxz : x ≤ z
        · exact absurd (le_trans hxz (le_of_lt hz)) hxm
        · exact absurd (hleast z hzx hxz) (not_le_of_gt hz)
    have hsum : (A x m).ncard + (A m x).ncard ≤ Ext.ncard := by
      have hfin := ext_finite (P := P)
      have hfinA : (A x m).Finite := hfin.subset fun f hf => hf.1
      have hfinA' : (A m x).Finite := hfin.subset fun f hf => hf.1
      have hdisj : Disjoint (A x m) (A m x) := by
        rw [Set.disjoint_left]
        rintro f ⟨_, h1⟩ ⟨_, h2⟩
        omega
      rw [← Set.ncard_union_eq hdisj hfinA hfinA']
      refine Set.ncard_le_ncard ?_ hfin
      rintro f (hf | hf)
      · exact hf.1
      · exact hf.1
    have bound : 3 * (A m x).ncard ≤ 2 * Ext.ncard := by omega
    obtain ⟨y, hy⟩ := core hw hmin' hxm hmx bound
    exact ⟨m, y, hy⟩

end WidthTwo

lemma width_two (P : Type) [PartialOrder P] [Fintype P]
    (nonchain : ¬ ∀ a b : P, a ≤ b ∨ b ≤ a)
    (width : ∀ a b c : P, a ≤ b ∨ b ≤ a ∨ a ≤ c ∨ c ≤ a ∨ b ≤ c ∨ c ≤ b) :
    let ranks : Finset (P ≃ Fin (Fintype.card P)) := by
      classical
      exact Finset.univ.filter (fun rank => StrictMono rank)
    ∃ x y : P, x ≠ y ∧
      let p := ((ranks.filter (fun r => r x < r y)).card : ℚ) / ranks.card
      1 / 3 ≤ p ∧ p ≤ 2 / 3 := by
  classical
  intro ranks
  obtain ⟨x, y, lower, upper⟩ := WidthTwo.linial (fun h => nonchain h.total) width
  obtain ⟨den, num⟩ := rank_shift_counts P
  rw [den, num x y] at lower upper
  obtain ⟨r, hr⟩ := rank_exists P
  have pos : 0 < ranks.card := Finset.card_pos.mpr ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr⟩⟩
  have ne : x ≠ y := by
    rintro rfl
    change ranks.card ≤ 3 * (ranks.filter (fun r => r x < r x)).card at lower
    simp only [lt_self_iff_false, Finset.filter_false, Finset.card_empty, Nat.mul_zero] at lower
    exact (Nat.not_lt_of_ge lower) pos
  let before := (ranks.filter (fun r => r x < r y)).card
  have lo : (ranks.card : ℚ) ≤ 3 * (before : ℚ) := by exact_mod_cast lower
  have hi : 3 * (before : ℚ) ≤ 2 * (ranks.card : ℚ) := by exact_mod_cast upper
  have posq : (0 : ℚ) < ranks.card := by exact_mod_cast pos
  refine ⟨x, y, ne, (le_div_iff₀ posq).2 ?_, (div_le_iff₀ posq).2 ?_⟩ <;> linarith

-- A finite strict total order is rigid: each element is determined by the
-- number of elements preceding it. The order can differ from the input order.
lemma fixed_of_preserves_total {P : Type} [Fintype P] (R : P → P → Prop)
    (irrefl : ∀ x, ¬ R x x) (transitive : ∀ {x y z}, R x y → R y z → R x z)
    (total : ∀ x y, x ≠ y → R x y ∨ R y x) (e : P ≃ P)
    (preserves : ∀ x y, R x y ↔ R (e x) (e y)) : ∀ x, e x = x := by
  classical
  let pred (x : P) := Finset.univ.filter (fun z => R z x)
  have increases {x y : P} (h : R x y) : (pred x).card < (pred y).card := by
    have sub : pred x ⊆ pred y := by
      intro z hz
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, transitive (Finset.mem_filter.mp hz).2 h⟩
    apply Finset.card_lt_card ((Finset.ssubset_iff_of_subset sub).2 ?_)
    exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩,
      fun hx => irrefl x (Finset.mem_filter.mp hx).2⟩
  intro x
  have same : (pred x).card = (pred (e x)).card := Finset.card_equiv e (by
    intro z
    simpa only [pred, Finset.mem_filter, Finset.mem_univ, true_and] using preserves z x)
  by_contra ne
  rcases total (e x) x ne with h | h
  · exact (increases h).ne same.symm
  · exact (increases h).ne same

-- Pouzet's symmetry argument. Without a balanced pair, the more-than-two-thirds
-- comparisons form a strict total order preserved by every poset automorphism.
-- The local count is the body of numExt from the gold-partition statement
-- (#6289). Keeping it local permits the reduction's single problem import.
lemma comparison_counts (P : Type) [PartialOrder P] [Fintype P] :
    let count (extra : List (P × P)) :=
      Nat.card {σ : P ≃ Fin (Fintype.card P) //
        (∀ a b : P, a < b → σ a < σ b) ∧ ∀ c ∈ extra, σ c.1 < σ c.2}
    let ext : Finset (P ≃ Fin (Fintype.card P)) := by
      classical
      exact Finset.univ.filter (fun r => StrictMono r)
    count [] = ext.card ∧
    (∀ x y : P, count [(x, y)] = (ext.filter (fun r => r x < r y)).card) ∧
    (∀ (extra : List (P × P)) (x y : P), x ≠ y →
      count (extra ++ [(x, y)]) + count (extra ++ [(y, x)]) = count extra) ∧
    (∀ p q : P × P, count [p, q] ≤ count [p] ∧ count [p, q] ≤ count [q] ∧
      count [p, q] = count [q, p]) := by
  classical
  intro count ext
  let allowed (l : List (P × P)) := ext.filter (fun r => ∀ c ∈ l, r c.1 < r c.2)
  have card (l : List (P × P)) : count l = (allowed l).card := by
    unfold count
    rw [Nat.card_eq_fintype_card]
    apply Fintype.card_of_subtype
    intro r
    simp only [allowed, ext, Finset.mem_filter, Finset.mem_univ, true_and]
    rfl
  have add (l : List (P × P)) (p : P × P) : allowed (l ++ [p]) =
      (allowed l).filter (fun r => r p.1 < r p.2) := by
    ext r
    simp only [allowed, Finset.mem_filter, List.forall_mem_append, List.forall_mem_cons,
      and_assoc]
    simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [card]
    simp [allowed]
  · intro x y
    rw [card]
    simp [allowed]
  · intro l x y ne
    have opposite : (allowed l).filter (fun r => r y < r x) =
        (allowed l).filter (fun r => ¬ r x < r y) := by
      apply Finset.filter_congr
      intro r _
      exact ⟨fun h => not_lt_of_gt h, fun h => lt_of_le_of_ne (le_of_not_gt h) (r.injective.ne ne.symm)⟩
    rw [card, card, card, add, add]
    change ((allowed l).filter (fun r => r x < r y)).card +
      ((allowed l).filter (fun r => r y < r x)).card = (allowed l).card
    rw [opposite]
    exact Finset.card_filter_add_card_filter_not _
  · intro p q
    have swap : allowed [p, q] = allowed [q, p] := by
      ext r
      simp [allowed, or_comm]
    have sub (i j : P × P) : allowed [i, j] ⊆ allowed [i] := by
      rw [show [i, j] = [i] ++ [j] from rfl, add]
      exact Finset.filter_subset _ _
    simp only [card]
    exact ⟨Finset.card_le_card (sub p q), Finset.card_le_card (swap ▸ sub q p), congrArg Finset.card swap⟩

-- Adding the two gold inequalities for a fixed first outcome bounds its row
-- by two thirds of the total. The other row supplies its lower bound.
lemma gold_first_pair (P : Type) [PartialOrder P] [Fintype P] :
    let count (extra : List (P × P)) :=
      Nat.card {σ : P ≃ Fin (Fintype.card P) //
        (∀ a b : P, a < b → σ a < σ b) ∧ ∀ c ∈ extra, σ c.1 < σ c.2}
    ∀ (x y u v : P), x ≠ y → u ≠ v →
      (∀ p ∈ [(x, y), (y, x)], ∀ q ∈ [(u, v), (v, u)],
        count [p] + count [p, q] ≤ count []) →
      count [] ≤ 3 * count [(x, y)] ∧ 3 * count [(x, y)] ≤ 2 * count [] := by
  classical
  intro count x y u v hxy huv gold
  obtain ⟨_, _, split, _⟩ := comparison_counts P
  have first : count [(x, y)] + count [(y, x)] = count [] := split [] x y hxy
  have row (p) (hp : p ∈ [(x, y), (y, x)]) : 3 * count [p] ≤ 2 * count [] := by
    have partition : count [p, (u, v)] + count [p, (v, u)] = count [p] := split [p] u v huv
    have a := gold p hp (u, v) (by simp)
    have b := gold p hp (v, u) (by simp)
    omega
  have up := row (x, y) (by simp)
  have rev := row (y, x) (by simp)
  exact ⟨by omega, up⟩

lemma gold_balanced (P : Type) [PartialOrder P] [Fintype P] :
    let count (extra : List (P × P)) :=
      Nat.card {σ : P ≃ Fin (Fintype.card P) //
        (∀ a b : P, a < b → σ a < σ b) ∧ ∀ c ∈ extra, σ c.1 < σ c.2}
    (∃ x y u v : P, x ≠ y ∧ u ≠ v ∧
      ∀ p ∈ [(x, y), (y, x)], ∀ q ∈ [(u, v), (v, u)],
        count [p] + count [p, q] ≤ count []) →
    let ext : Finset (P ≃ Fin (Fintype.card P)) := by
      classical
      exact Finset.univ.filter (fun r => StrictMono r)
    ∃ x y : P, x ≠ y ∧
      let p := ((ext.filter (fun r => r x < r y)).card : ℚ) / ext.card
      1 / 3 ≤ p ∧ p ≤ 2 / 3 := by
  classical
  intro count cert ext
  obtain ⟨x, y, u, v, xy, uv, gold⟩ := cert
  obtain ⟨lo, hi⟩ := gold_first_pair P x y u v xy uv gold
  obtain ⟨den, num, _, _⟩ := comparison_counts P
  rw [den, num] at lo hi
  obtain ⟨r, hr⟩ := rank_exists P
  have pos : 0 < ext.card := Finset.card_pos.mpr ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr⟩⟩
  let n := (ext.filter (fun r => r x < r y)).card
  have low : (ext.card : ℚ) ≤ 3 * (n : ℚ) := by exact_mod_cast lo
  have high : 3 * (n : ℚ) ≤ 2 * (ext.card : ℚ) := by exact_mod_cast hi
  have posq : (0 : ℚ) < ext.card := by exact_mod_cast pos
  refine ⟨x, y, xy, (le_div_iff₀ posq).2 ?_, (div_le_iff₀ posq).2 ?_⟩ <;> linarith

-- Peczarski's balanced-triple criterion (Comments on the Golden Partition
-- Conjecture, Fact 1). Use the comparison with the larger reverse count first.
lemma balanced_triple_gold (P : Type) [PartialOrder P] [Fintype P] :
    let count (extra : List (P × P)) :=
      Nat.card {σ : P ≃ Fin (Fintype.card P) //
        (∀ a b : P, a < b → σ a < σ b) ∧ ∀ c ∈ extra, σ c.1 < σ c.2}
    ∀ x y z : P, x ≠ y → y ≠ z → x ≠ z →
      count [(x, y), (y, z)] ≤ max (count [(y, x)]) (count [(z, y)]) →
      2 * max (count [(y, x)]) (count [(z, y)]) ≤ count [] →
      ∃ x y u v : P, x ≠ y ∧ u ≠ v ∧
      ∀ p ∈ [(x, y), (y, x)], ∀ q ∈ [(u, v), (v, u)],
        count [p] + count [p, q] ≤ count [] := by
  classical
  intro count x y z xy yz _ middle half
  obtain ⟨_, _, split, cells⟩ := comparison_counts P
  have chooseFirst (a b c d : P) (ab : a ≠ b) (cd : c ≠ d)
      (other : count [(d, c)] ≤ count [(b, a)])
      (chain : count [(a, b), (c, d)] ≤ count [(b, a)])
      (small : 2 * count [(b, a)] ≤ count []) :
      ∃ i j k l : P, i ≠ j ∧ k ≠ l ∧
        ∀ p ∈ [(i, j), (j, i)], ∀ q ∈ [(k, l), (l, k)], count [p] + count [p, q] ≤ count [] := by
    have rows : count [(a, b)] + count [(b, a)] = count [] := split [] a b ab
    refine ⟨a, b, c, d, ab, cd, ?_⟩
    intro p hp q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp hq
    rcases hp with rfl | rfl
    · rcases hq with rfl | rfl
      · omega
      · have cell : count [(a, b), (d, c)] ≤ count [(d, c)] := (cells _ _).2.1
        omega
    · have cell : count [(b, a), q] ≤ count [(b, a)] := (cells _ _).1
      omega
  rcases le_total (count [(z, y)]) (count [(y, x)]) with h | h
  · rw [max_eq_left h] at middle half
    exact chooseFirst x y y z xy yz h middle half
  · rw [max_eq_right h] at middle half
    have flip : count [(y, z), (x, y)] = count [(x, y), (y, z)] := (cells _ _).2.2
    exact chooseFirst y z x y yz xy h (flip.trans_le middle) half

-- A rank satisfying both comparisons puts x before z by transitivity.
lemma chain_count_le (P : Type) [PartialOrder P] [Fintype P] :
    let count (extra : List (P × P)) :=
      Nat.card {σ : P ≃ Fin (Fintype.card P) //
        (∀ a b : P, a < b → σ a < σ b) ∧ ∀ c ∈ extra, σ c.1 < σ c.2}
    ∀ x y z : P, count [(x, y), (y, z)] ≤ count [(x, z)] := by
  intro count x y z
  let ranks (l : List (P × P)) := {σ : P ≃ Fin (Fintype.card P) //
    (∀ a b : P, a < b → σ a < σ b) ∧ ∀ c ∈ l, σ c.1 < σ c.2}
  let forget (r : ranks [(x, y), (y, z)]) : ranks [(x, z)] := ⟨r.1, r.2.1, by
    intro p hp
    obtain rfl : p = (x, z) := by simpa using hp
    exact lt_trans (r.2.2 (x, y) (by simp)) (r.2.2 (y, z) (by simp))⟩
  exact Nat.card_le_card_of_injective forget (fun _ _ h => Subtype.ext (congrArg (fun r : ranks [(x, z)] => r.val) h))

-- Peczarski, Fact 3. Rotate the cycle so the omitted edge has a reverse
-- count at most the larger reverse count of the other two edges.
lemma majority_cycle_gold (P : Type) [PartialOrder P] [Fintype P] :
    let count (extra : List (P × P)) :=
      Nat.card {σ : P ≃ Fin (Fintype.card P) //
        (∀ a b : P, a < b → σ a < σ b) ∧ ∀ c ∈ extra, σ c.1 < σ c.2}
    ∀ x y z : P, x ≠ y → y ≠ z → z ≠ x →
      count [] < 2 * count [(x, y)] → count [] < 2 * count [(y, z)] →
      count [] < 2 * count [(z, x)] → ∃ x y u v : P, x ≠ y ∧ u ≠ v ∧
      ∀ p ∈ [(x, y), (y, x)], ∀ q ∈ [(u, v), (v, u)],
        count [p] + count [p, q] ≤ count [] := by
  intro count x y z xy yz zx a b c
  obtain ⟨_, _, split, _⟩ := comparison_counts P
  have half (i j : P) (ne : i ≠ j) (h : count [] < 2 * count [(i, j)]) :
      2 * count [(j, i)] ≤ count [] := by
    have part : count [(i, j)] + count [(j, i)] = count [] := split [] i j ne
    omega
  have h₁ := half x y xy a
  have h₂ := half y z yz b
  have h₃ := half z x zx c
  have fit (i j k : P) (ij : i ≠ j) (jk : j ≠ k) (ik : i ≠ k)
      (m : count [(i, k)] ≤ max (count [(j, i)]) (count [(k, j)]))
      (halfMax : 2 * max (count [(j, i)]) (count [(k, j)]) ≤ count []) :=
    balanced_triple_gold P i j k ij jk ik ((chain_count_le P i j k).trans m) halfMax
  by_cases h : count [(x, z)] ≤ max (count [(y, x)]) (count [(z, y)])
  · exact fit x y z xy yz zx.symm h (by omega)
  · exact fit y z x yz zx xy.symm (by omega) (by omega)

lemma tied_comparison_gold (P : Type) [PartialOrder P] [Fintype P] :
    let count (extra : List (P × P)) :=
      Nat.card {σ : P ≃ Fin (Fintype.card P) //
        (∀ a b : P, a < b → σ a < σ b) ∧ ∀ c ∈ extra, σ c.1 < σ c.2}
    ∀ x y : P, x ≠ y → 2 * count [(x, y)] = count [] → ∃ x y u v : P, x ≠ y ∧ u ≠ v ∧
      ∀ p ∈ [(x, y), (y, x)], ∀ q ∈ [(u, v), (v, u)],
        count [p] + count [p, q] ≤ count [] := by
  intro count x y xy tie
  obtain ⟨_, _, split, cells⟩ := comparison_counts P
  have part : count [(x, y)] + count [(y, x)] = count [] := split [] x y xy
  refine ⟨x, y, x, y, xy, xy, ?_⟩
  intro p hp q _
  have bound : count [p, q] ≤ count [p] := (cells p q).1
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl <;> omega

lemma no_gold_majority_order (P : Type) [PartialOrder P] [Fintype P] :
    let count (extra : List (P × P)) :=
      Nat.card {σ : P ≃ Fin (Fintype.card P) //
        (∀ a b : P, a < b → σ a < σ b) ∧ ∀ c ∈ extra, σ c.1 < σ c.2}
    ¬ (∃ x y u v : P, x ≠ y ∧ u ≠ v ∧
      ∀ p ∈ [(x, y), (y, x)], ∀ q ∈ [(u, v), (v, u)],
        count [p] + count [p, q] ≤ count []) →
    let R (x y : P) := count [] < 2 * count [(x, y)]
    (∀ x, ¬ R x x) ∧ (∀ x y, x ≠ y → R x y ∨ R y x) ∧
      (∀ {x y z}, R x y → R y z → R x z) := by
  classical
  intro count noGold R
  obtain ⟨_, num, split, _⟩ := comparison_counts P
  have irr (x : P) : ¬ R x x := by
    have zero : count [(x, x)] = 0 := (num x x).trans (by simp)
    simp [R, zero]
  have total (x y : P) (ne : x ≠ y) : R x y ∨ R y x := by
    have part : count [(x, y)] + count [(y, x)] = count [] := split [] x y ne
    have untied : 2 * count [(x, y)] ≠ count [] := fun h => noGold (tied_comparison_gold P x y ne h)
    dsimp only [R]
    omega
  refine ⟨irr, total, ?_⟩
  intro x y z a b
  have xy : x ≠ y := fun h => irr y (h ▸ a)
  have yz : y ≠ z := fun h => irr z (h ▸ b)
  have xz : x ≠ z := by
    rintro rfl
    have part : count [(x, y)] + count [(y, x)] = count [] := split [] x y xy
    dsimp only [R] at a b
    omega
  rcases total x z xz with h | h
  · exact h
  · exact (noGold (majority_cycle_gold P x y z xy yz xz.symm a b h)).elim

-- Peczarski, section 3. In the absence of gold a finite strict majority
-- order is total, so an automorphism preserving its counts fixes each point.
lemma automorphism_gold (P : Type) [PartialOrder P] [Fintype P]
    (moves : ∃ (e : P ≃o P) (x : P), e x ≠ x) :
    let count (extra : List (P × P)) :=
      Nat.card {σ : P ≃ Fin (Fintype.card P) //
        (∀ a b : P, a < b → σ a < σ b) ∧ ∀ c ∈ extra, σ c.1 < σ c.2}
    ∃ x y u v : P, x ≠ y ∧ u ≠ v ∧
      ∀ p ∈ [(x, y), (y, x)], ∀ q ∈ [(u, v), (v, u)],
        count [p] + count [p, q] ≤ count [] := by
  classical
  intro count
  by_contra noGold
  obtain ⟨irr, total, transitive⟩ := no_gold_majority_order P noGold
  obtain ⟨den, num, _, _⟩ := comparison_counts P
  obtain ⟨e, x, moved⟩ := moves
  let ext := Finset.univ.filter (fun r : P ≃ Fin (Fintype.card P) => StrictMono r)
  obtain ⟨r, hr⟩ := rank_exists P
  have pos : 0 < ext.card := Finset.card_pos.mpr ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr⟩⟩
  have posq : (0 : ℚ) < ext.card := by exact_mod_cast pos
  have invariant (a b : P) : count [(a, b)] = count [(e a, e b)] := by
    have ratio := count_transport e a b
    exact (num a b).trans (Eq.trans (by
      exact_mod_cast (div_left_inj' posq.ne').mp ratio) (num (e a) (e b)).symm)
  apply moved
  apply fixed_of_preserves_total (fun a b => count [] < 2 * count [(a, b)]) irr transitive total e.toEquiv _ x
  intro a b
  change (count [] < 2 * count [(a, b)]) ↔ count [] < 2 * count [(e a, e b)]
  rw [invariant]

lemma automorphism_balanced (P : Type) [PartialOrder P] [Fintype P]
    (moves : ∃ (e : P ≃o P) (x : P), e x ≠ x) :
    let ext : Finset (P ≃ Fin (Fintype.card P)) := by
      classical
      exact Finset.univ.filter (fun r => StrictMono r)
    ∃ x y : P, x ≠ y ∧
      let p := ((ext.filter (fun r => r x < r y)).card : ℚ) / ext.card
      1 / 3 ≤ p ∧ p ≤ 2 / 3 := by
  exact gold_balanced P (automorphism_gold P moves)

-- Exchange x and y in a family of extensions where every strict successor
-- of x is after y. The predecessor inclusion protects y when moved earlier.
lemma exchange_count_le (P : Type) [PartialOrder P] [Fintype P] :
    let count (extra : List (P × P)) :=
      Nat.card {σ : P ≃ Fin (Fintype.card P) //
        (∀ a b : P, a < b → σ a < σ b) ∧ ∀ c ∈ extra, σ c.1 < σ c.2}
    ∀ (x y : P) (extra : List (P × P)), ¬ x ≤ y →
      (∀ a, a < y → a < x) →
      (∀ r : P ≃ Fin (Fintype.card P), StrictMono r →
        (∀ c ∈ extra, r c.1 < r c.2) →
        r x < r y ∧ ∀ b, x < b → r y < r b) →
      count extra ≤ count [(y, x)] := by
  classical
  intro count x y extra inc pred safe
  let ranks (l : List (P × P)) := {σ : P ≃ Fin (Fintype.card P) //
    (∀ a b : P, a < b → σ a < σ b) ∧ ∀ c ∈ l, σ c.1 < σ c.2}
  let swap := Equiv.swap x y
  have valid (r : ranks extra) : StrictMono (swap.trans r.val) ∧
      (swap.trans r.val) y < (swap.trans r.val) x := by
    have mono : StrictMono r.val := fun _ _ h => r.property.1 _ _ h
    obtain ⟨xy, succ⟩ := safe r.val mono r.property.2
    constructor
    · intro a b ab
      change r.val (swap a) < r.val (swap b)
      by_cases ax : a = x
      · subst a
        have by' : b ≠ y := fun h => inc (h ▸ ab.le)
        simpa [swap, Equiv.swap_apply_of_ne_of_ne ab.ne.symm by'] using succ b ab
      by_cases by' : b = y
      · subst b
        simpa [swap, Equiv.swap_apply_of_ne_of_ne ax ab.ne] using mono (pred a ab)
      have left : r.val (swap a) ≤ r.val a := by
        by_cases ay : a = y
        · simpa [ay, swap] using xy.le
        · simp [swap, Equiv.swap_apply_of_ne_of_ne ax ay]
      have right : r.val b ≤ r.val (swap b) := by
        by_cases bx : b = x
        · simpa [bx, swap] using xy.le
        · simp [swap, Equiv.swap_apply_of_ne_of_ne bx by']
      exact lt_of_le_of_lt left (lt_of_lt_of_le (mono ab) right)
    · simpa [swap] using xy
  let move (r : ranks extra) : ranks [(y, x)] := ⟨swap.trans r.val,
    fun _ _ h => (valid r).1 h, by
      intro c hc
      obtain rfl : c = (y, x) := by simpa using hc
      exact (valid r).2⟩
  apply Nat.card_le_card_of_injective move
  intro r s h
  apply Subtype.ext
  apply Equiv.ext
  intro a
  have eq := congrArg (fun t : ranks [(y, x)] => t.val (swap.symm a)) h
  change r.val (swap (swap.symm a)) = s.val (swap (swap.symm a)) at eq
  simpa using eq

-- Peczarski, section 2 (one upper chain and a weak majority at its base).
lemma upper_chain_gold (P : Type) [PartialOrder P] [Fintype P] :
    let count (extra : List (P × P)) :=
      Nat.card {σ : P ≃ Fin (Fintype.card P) //
        (∀ a b : P, a < b → σ a < σ b) ∧ ∀ c ∈ extra, σ c.1 < σ c.2}
    ∀ x y : P, ¬ x ≤ y → (∀ a, a < y → a < x) →
      (∀ a b, x ≤ a → x ≤ b → a ≤ b ∨ b ≤ a) →
      count [] ≤ 2 * count [(x, y)] → ∃ x y u v : P, x ≠ y ∧ u ≠ v ∧
      ∀ p ∈ [(x, y), (y, x)], ∀ q ∈ [(u, v), (v, u)],
        count [p] + count [p, q] ≤ count [] := by
  classical
  intro count x y inc pred chain initial
  obtain ⟨rank, mono⟩ := rank_exists P
  obtain ⟨_, _, split, _⟩ := comparison_counts P
  let eligible := Finset.univ.filter (fun a : P => x ≤ a ∧ count [] ≤ 2 * count [(a, y)])
  have mem (a : P) : a ∈ eligible ↔ x ≤ a ∧ count [] ≤ 2 * count [(a, y)] := by simp [eligible]
  obtain ⟨a, ha, last⟩ := eligible.exists_max_image rank ⟨x, (mem x).2 ⟨le_rfl, initial⟩⟩
  obtain ⟨xa, majority⟩ := (mem a).1 ha
  have ay : ¬ a ≤ y := fun h => inc (xa.trans h)
  have ne : a ≠ y := fun h => ay h.le
  have pred' (b : P) (h : b < y) : b < a := lt_of_lt_of_le (pred b h) xa
  have part : count [(a, y)] + count [(y, a)] = count [] := split [] a y ne
  by_cases above : ∃ b, a < b
  · obtain ⟨b, hb⟩ := above
    let upper := Finset.univ.filter (fun z : P => a < z)
    have up (z : P) : z ∈ upper ↔ a < z := by simp [upper]
    obtain ⟨z, hz, first⟩ := upper.exists_min_image rank ⟨b, (up b).2 hb⟩
    have az := (up z).1 hz
    have least (v : P) (av : a < v) : z ≤ v := by
      rcases chain z v (xa.trans az.le) (xa.trans av.le) with h | h
      · exact h
      · by_contra bad
        exact (not_lt_of_ge (first v ((up v).2 av))) (mono (lt_of_le_of_ne h (fun eq => bad eq.ge)))
    have minority : 2 * count [(z, y)] < count [] := by
      by_contra! large
      exact (not_lt_of_ge (last z ((mem z).2 ⟨xa.trans az.le, large⟩))) (mono az)
    have cell : count [(a, y), (y, z)] ≤ count [(y, a)] := by
      apply exchange_count_le P a y _ ay pred'
      intro r hr extra
      exact ⟨extra (a, y) (by simp), fun v av =>
        lt_of_lt_of_le (extra (y, z) (by simp)) (hr.monotone (least v av))⟩
    have yz : y ≠ z := fun h => ay (h ▸ az.le)
    have bound : 2 * max (count [(y, a)]) (count [(z, y)]) ≤ count [] := by omega
    exact balanced_triple_gold P a y z ne yz az.ne (cell.trans (le_max_left _ _)) bound
  · have bound : count [(a, y)] ≤ count [(y, a)] := by
      apply exchange_count_le P a y _ ay pred'
      intro r _ extra
      exact ⟨extra (a, y) (by simp), fun b h => (above ⟨b, h⟩).elim⟩
    have tie : 2 * count [(a, y)] = count [] := by omega
    exact tied_comparison_gold P a y ne tie

lemma two_upper_chains_gold (P : Type) [PartialOrder P] [Fintype P] :
    let count (extra : List (P × P)) :=
      Nat.card {σ : P ≃ Fin (Fintype.card P) //
        (∀ a b : P, a < b → σ a < σ b) ∧ ∀ c ∈ extra, σ c.1 < σ c.2}
    ∀ x y : P, ¬ x ≤ y → ¬ y ≤ x → (∀ a, a < x ↔ a < y) →
      (∀ a b, x ≤ a → x ≤ b → a ≤ b ∨ b ≤ a) →
      (∀ a b, y ≤ a → y ≤ b → a ≤ b ∨ b ≤ a) → ∃ x y u v : P, x ≠ y ∧ u ≠ v ∧
      ∀ p ∈ [(x, y), (y, x)], ∀ q ∈ [(u, v), (v, u)],
        count [p] + count [p, q] ≤ count [] := by
  intro count x y xy yx pred cx cy
  obtain ⟨_, _, split, _⟩ := comparison_counts P
  have part : count [(x, y)] + count [(y, x)] = count [] :=
    split [] x y (fun h => xy h.le)
  by_cases majority : count [] ≤ 2 * count [(x, y)]
  · exact upper_chain_gold P x y xy (fun a => (pred a).2) cx majority
  · have reverse : count [] ≤ 2 * count [(y, x)] := by omega
    exact upper_chain_gold P y x yx (fun a => (pred a).1) cy reverse

-- Lower covers generate the strict lower set in a finite poset.
lemma lower_covers_determine_predecessors (P : Type) [PartialOrder P] [Fintype P]
    (x y : P) (covers : ∀ c : P, (c ⋖ x) ↔ (c ⋖ y)) :
    ∀ a : P, a < x ↔ a < y := by
  classical
  obtain ⟨rank, mono⟩ := rank_exists P
  have liftPred (i j : P) (sub : ∀ c : P, c ⋖ i → c ⋖ j) (a : P) (ai : a < i) : a < j := by
    let interval := Finset.univ.filter (fun c : P => a ≤ c ∧ c < i)
    have mem (c : P) : c ∈ interval ↔ a ≤ c ∧ c < i := by simp [interval]
    obtain ⟨c, hc, last⟩ := interval.exists_max_image rank ⟨a, (mem a).2 ⟨le_rfl, ai⟩⟩
    obtain ⟨ac, ci⟩ := (mem c).1 hc
    have cover : c ⋖ i := ⟨ci, fun d cd di =>
      (not_lt_of_ge (last d ((mem d).2 ⟨ac.trans cd.le, di⟩))) (mono cd)⟩
    exact lt_of_le_of_lt ac (sub c cover).1
  exact fun a => ⟨liftPred x y (fun c => (covers c).1) a, liftPred y x (fun c => (covers c).2) a⟩

lemma common_lower_covers_gold (P : Type) [PartialOrder P] [Fintype P] :
    let count (extra : List (P × P)) :=
      Nat.card {σ : P ≃ Fin (Fintype.card P) //
        (∀ a b : P, a < b → σ a < σ b) ∧ ∀ c ∈ extra, σ c.1 < σ c.2}
    ∀ x y : P, x ≠ y → (∀ c : P, (c ⋖ x) ↔ (c ⋖ y)) →
      (∀ a b, x ≤ a → x ≤ b → a ≤ b ∨ b ≤ a) →
      (∀ a b, y ≤ a → y ≤ b → a ≤ b ∨ b ≤ a) → ∃ x y u v : P, x ≠ y ∧ u ≠ v ∧
      ∀ p ∈ [(x, y), (y, x)], ∀ q ∈ [(u, v), (v, u)],
        count [p] + count [p, q] ≤ count [] := by
  intro count x y ne covers cx cy
  have pred := lower_covers_determine_predecessors P x y covers
  have xy : ¬ x ≤ y := fun h => (lt_irrefl x) ((pred x).2 (lt_of_le_of_ne h ne))
  have yx : ¬ y ≤ x := fun h => (lt_irrefl y) ((pred y).1 (lt_of_le_of_ne h ne.symm))
  exact two_upper_chains_gold P x y xy yx pred cx cy

-- Reverse every rank and both entries of each prescribed comparison.
-- This extends Schlesinger's single-comparison duality to arbitrary lists.
lemma dual_comparison_counts (P : Type) [PartialOrder P] [Fintype P] :
    let count (P : Type) [PartialOrder P] [Fintype P] (extra : List (P × P)) :=
      Nat.card {σ : P ≃ Fin (Fintype.card P) //
        (∀ a b : P, a < b → σ a < σ b) ∧ ∀ c ∈ extra, σ c.1 < σ c.2}
    ∀ l : List (P × P), count Pᵒᵈ l = count P (l.map Prod.swap) := by
  intro count l
  let ranks (A : Type) [PartialOrder A] [Fintype A] (cs : List (A × A)) :=
    {σ : A ≃ Fin (Fintype.card A) //
      (∀ a b : A, a < b → σ a < σ b) ∧ ∀ c ∈ cs, σ c.1 < σ c.2}
  let forward (r : ranks Pᵒᵈ l) : ranks P (l.map Prod.swap) :=
    ⟨r.val.trans Fin.revPerm, fun a b h => Fin.rev_lt_rev.mpr (r.property.1 b a h), by
      intro p hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      exact Fin.rev_lt_rev.mpr (r.property.2 q hq)⟩
  let backward (r : ranks P (l.map Prod.swap)) : ranks Pᵒᵈ l :=
    ⟨r.val.trans Fin.revPerm, fun a b h => Fin.rev_lt_rev.mpr (r.property.1 b a h), by
      intro p hp
      exact Fin.rev_lt_rev.mpr (r.property.2 p.swap (List.mem_map.mpr ⟨p, hp, rfl⟩))⟩
  apply Nat.card_congr (show ranks Pᵒᵈ l ≃ ranks P (l.map Prod.swap) from
    ⟨forward, backward, ?_, ?_⟩)
  all_goals
    intro r
    apply Subtype.ext
    apply Equiv.ext
    intro a
    exact Fin.rev_rev _

lemma gold_of_dual (P : Type) [PartialOrder P] [Fintype P] :
    let count (P : Type) [PartialOrder P] [Fintype P] (extra : List (P × P)) :=
      Nat.card {σ : P ≃ Fin (Fintype.card P) //
        (∀ a b : P, a < b → σ a < σ b) ∧ ∀ c ∈ extra, σ c.1 < σ c.2}
    (∃ x y u v : Pᵒᵈ, x ≠ y ∧ u ≠ v ∧
      ∀ p ∈ [(x, y), (y, x)], ∀ q ∈ [(u, v), (v, u)],
        count Pᵒᵈ [p] + count Pᵒᵈ [p, q] ≤ count Pᵒᵈ []) → ∃ x y u v : P, x ≠ y ∧ u ≠ v ∧
      ∀ p ∈ [(x, y), (y, x)], ∀ q ∈ [(u, v), (v, u)],
        count P [p] + count P [p, q] ≤ count P [] := by
  intro count cert
  obtain ⟨x, y, u, v, xy, uv, gold⟩ := cert
  have rev (l : List (P × P)) : count Pᵒᵈ l = count P (l.map Prod.swap) :=
    dual_comparison_counts P l
  refine ⟨y, x, v, u, xy.symm, uv.symm, ?_⟩
  intro p hp q hq
  have swap_mem (a b : P) (c : P × P) (hc : c ∈ [(b, a), (a, b)]) :
      c.swap ∈ [(a, b), (b, a)] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> simp
  have cell := gold p.swap (swap_mem x y p hp) q.swap (swap_mem u v q hq)
  have row : count Pᵒᵈ [p.swap] = count P [p] := rev [p.swap]
  have both : count Pᵒᵈ [p.swap, q.swap] = count P [p, q] := rev [p.swap, q.swap]
  exact (congrArg₂ Nat.add row both).symm.trans_le (cell.trans_eq (rev []))

lemma gold_dual_iff (P : Type) [PartialOrder P] [Fintype P] :
    let count (P : Type) [PartialOrder P] [Fintype P] (extra : List (P × P)) :=
      Nat.card {σ : P ≃ Fin (Fintype.card P) //
        (∀ a b : P, a < b → σ a < σ b) ∧ ∀ c ∈ extra, σ c.1 < σ c.2}
    (∃ x y u v : Pᵒᵈ, x ≠ y ∧ u ≠ v ∧
      ∀ p ∈ [(x, y), (y, x)], ∀ q ∈ [(u, v), (v, u)],
        count Pᵒᵈ [p] + count Pᵒᵈ [p, q] ≤ count Pᵒᵈ []) ↔ (∃ x y u v : P, x ≠ y ∧ u ≠ v ∧
      ∀ p ∈ [(x, y), (y, x)], ∀ q ∈ [(u, v), (v, u)],
        count P [p] + count P [p, q] ≤ count P []) := by
  intro count
  exact ⟨gold_of_dual P, gold_of_dual Pᵒᵈ⟩

lemma lower_chain_gold (P : Type) [PartialOrder P] [Fintype P] :
    let count (extra : List (P × P)) :=
      Nat.card {σ : P ≃ Fin (Fintype.card P) //
        (∀ a b : P, a < b → σ a < σ b) ∧ ∀ c ∈ extra, σ c.1 < σ c.2}
    ∀ x y : P, ¬ y ≤ x → (∀ a, y < a → x < a) →
      (∀ a b, a ≤ x → b ≤ x → a ≤ b ∨ b ≤ a) →
      count [] ≤ 2 * count [(y, x)] → ∃ x y u v : P, x ≠ y ∧ u ≠ v ∧
      ∀ p ∈ [(x, y), (y, x)], ∀ q ∈ [(u, v), (v, u)],
        count [p] + count [p, q] ≤ count [] := by
  intro count x y inc succ chain majority
  apply gold_of_dual P
  apply upper_chain_gold Pᵒᵈ x y inc succ
  · exact fun a b ha hb => (chain a b ha hb).symm
  · exact (dual_comparison_counts P []).trans_le
      (majority.trans_eq (congrArg (2 * ·) (dual_comparison_counts P [(x, y)])).symm)

lemma common_upper_covers_gold (P : Type) [PartialOrder P] [Fintype P] :
    let count (extra : List (P × P)) :=
      Nat.card {σ : P ≃ Fin (Fintype.card P) //
        (∀ a b : P, a < b → σ a < σ b) ∧ ∀ c ∈ extra, σ c.1 < σ c.2}
    ∀ x y : P, x ≠ y → (∀ c : P, (x ⋖ c) ↔ (y ⋖ c)) →
      (∀ a b, a ≤ x → b ≤ x → a ≤ b ∨ b ≤ a) →
      (∀ a b, a ≤ y → b ≤ y → a ≤ b ∨ b ≤ a) → ∃ x y u v : P, x ≠ y ∧ u ≠ v ∧
      ∀ p ∈ [(x, y), (y, x)], ∀ q ∈ [(u, v), (v, u)],
        count [p] + count [p, q] ≤ count [] := by
  intro count x y ne covers cx cy
  apply gold_of_dual P
  apply common_lower_covers_gold Pᵒᵈ x y ne
  · intro c
    exact (toDual_covBy_toDual_iff (a := x) (b := OrderDual.ofDual c)).trans
      ((covers (OrderDual.ofDual c)).trans (toDual_covBy_toDual_iff (a := y) (b := OrderDual.ofDual c)).symm)
  · exact fun a b ha hb => (cx a b ha hb).symm
  · exact fun a b ha hb => (cy a b ha hb).symm

-- The six-thin gold-partition theorem would discharge the existing H1.
lemma six_thin_gold_suffices (sixThin : ∀ (P : Type) [PartialOrder P] [Fintype P],
    (∃ a b : P, ¬ a ≤ b ∧ ¬ b ≤ a) →
    (∀ x : P, ({y : P | ¬ x ≤ y ∧ ¬ y ≤ x} : Set P).ncard ≤ 6) →
    let count (extra : List (P × P)) :=
      Nat.card {σ : P ≃ Fin (Fintype.card P) //
        (∀ a b : P, a < b → σ a < σ b) ∧ ∀ c ∈ extra, σ c.1 < σ c.2}
    ∃ x y u v : P, x ≠ y ∧ u ≠ v ∧
      ∀ p ∈ [(x, y), (y, x)], ∀ q ∈ [(u, v), (v, u)],
        count [p] + count [p, q] ≤ count []) : H1 := by
  intro P _ _ _ _ _ three thin _ _ noGold
  obtain ⟨x, y, _, xy, _, _⟩ := three
  exact (noGold (sixThin P ⟨x, y, xy⟩ thin)).elim

theorem main : H1 → H2 → type_of% @OMA.S_wp_1_3_2_3_conjecture.main := by
  classical
  intro thinCase remaining P _ _ nonchain
  let e : Shrink.{0} P ≃o P := (orderIsoShrink.{0} P).symm
  have hn : ¬ ∀ x y : Shrink.{0} P, x ≤ y ∨ y ≤ x := by
    intro total
    apply nonchain
    intro a b
    simpa only [e.symm.le_iff_le] using total (e.symm a) (e.symm b)
  obtain ⟨S, hS, hcut, hprob⟩ := select_block (Shrink.{0} P) hn
  have core (Q : Type) [PartialOrder Q] [Fintype Q]
      (hn : ¬ ∀ x y : Q, x ≤ y ∨ y ≤ x)
      (hi : ¬ ∃ L : Set Q, L.Nonempty ∧ (∃ y, y ∉ L) ∧ ∀ x ∈ L, ∀ y ∉ L, x < y) :
      let ext : Finset (Q ≃ Fin (Fintype.card Q)) := by
        classical
        exact Finset.univ.filter (fun r => StrictMono r)
      ∃ x y : Q, x ≠ y ∧
        let p := ((ext.filter (fun r => r x < r y)).card : ℚ) / ext.card
        1 / 3 ≤ p ∧ p ≤ 2 / 3 := by
    by_cases hw : ∀ a b c : Q, a ≤ b ∨ b ≤ a ∨ a ≤ c ∨ c ≤ a ∨ b ≤ c ∨ c ≤ b
    · exact width_two Q hn hw
    · simp only [not_forall, not_or] at hw
      obtain ⟨a, b, c, ab, ba, ac, ca, bc, cb⟩ := hw
      have three : ∃ i j k : Q,
          (¬ i ≤ j ∧ ¬ j ≤ i) ∧ (¬ i ≤ k ∧ ¬ k ≤ i) ∧ (¬ j ≤ k ∧ ¬ k ≤ j) :=
        ⟨a, b, c, ⟨ab, ba⟩, ⟨ac, ca⟩, bc, cb⟩
      by_contra noPair
      have noGold := fun h => noPair (gold_balanced Q h)
      have rigid (e : Q ≃o Q) (x : Q) : e x = x := by
        by_contra moved
        exact noGold (automorphism_gold Q ⟨e, x, moved⟩)
      have noChains : ¬ ∃ x y : Q, x ≠ y ∧ (∀ c : Q, (c ⋖ x) ↔ (c ⋖ y)) ∧
          (∀ a b, x ≤ a → x ≤ b → a ≤ b ∨ b ≤ a) ∧
          (∀ a b, y ≤ a → y ≤ b → a ≤ b ∨ b ≤ a) := by
        rintro ⟨x, y, ne, covers, cx, cy⟩
        exact noGold (common_lower_covers_gold Q x y ne covers cx cy)
      have noLowerChains : ¬ ∃ x y : Q, x ≠ y ∧ (∀ c : Q, (x ⋖ c) ↔ (y ⋖ c)) ∧
          (∀ a b, a ≤ x → b ≤ x → a ≤ b ∨ b ≤ a) ∧
          (∀ a b, a ≤ y → b ≤ y → a ≤ b ∨ b ≤ a) := by
        rintro ⟨x, y, ne, covers, cx, cy⟩
        exact noGold (common_upper_covers_gold Q x y ne covers cx cy)
      by_cases thin : ∀ x : Q, ({y : Q | ¬ x ≤ y ∧ ¬ y ≤ x} : Set Q).ncard ≤ 6
      · exact noPair (thinCase Q hn hi rigid three thin noChains noLowerChains noGold)
      · obtain ⟨x, hx⟩ := not_forall.mp thin
        exact noPair (remaining Q hn hi rigid three ⟨x, by omega⟩ noChains noLowerChains noGold)
  obtain ⟨x, y, hxy, hbounds⟩ := core S hS hcut
  have eqProb := (hprob x y).trans (count_transport e x.val y.val)
  exact ⟨e x.val, e y.val, fun h => hxy (Subtype.ext (e.injective h)),
    transfer_bounds eqProb hbounds⟩

end OMA.R_wp_1_3_2_3_conjecture_R1
