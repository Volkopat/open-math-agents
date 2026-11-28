import OMAReductions.R_Green69_green_69_variants_elekes_szabo_R1_H2_R1

-- Step Green69.green_69.variants.elekes_szabo.R1.H2.R1.H1: the dense range of the Elekes–Szabó conjecture.
-- n points, no four collinear, at least 4 n^2 / 25 triple lines: ten points lie on a cubic.
-- Credit: @chris01-dev

/-!
Dense range of the Elekes–Szabó conjecture, via the dual line arrangement swept by slope.

A point `P` of the plane is sent to the dual line `x ↦ ht lam P x = sl lam P * x - P.2`, where
`sl lam P = P.1 + lam * P.2` and `lam` is chosen so that `sl lam` is injective on `A`.
Points `P, Q, R` are collinear iff their dual lines are concurrent.  A vertex `v = (y, c)` of
the arrangement is a point of the dual plane; `blk A lam v` is the set of points of `A` whose
dual line passes through `v`, and `bet A lam v` the number of points whose dual line passes
strictly below `v`.  Ranks are numbered `0 .. #A - 1` from the bottom; `rm`/`rp` are the ranks
just before / just after the abscissa `x`.  Gap `g` lies between ranks `g - 1` and `g`.
-/

namespace G69D

open scoped Finset
open Green69
open Classical

/-- Slope of the dual line of `P`. -/
noncomputable def sl (lam : ℝ) (P : ℝ × ℝ) : ℝ := P.1 + lam * P.2

/-- Height of the dual line of `P` at abscissa `x`. -/
noncomputable def ht (lam : ℝ) (P : ℝ × ℝ) (x : ℝ) : ℝ := sl lam P * x - P.2

/-- Abscissa at which the dual lines of `P` and `Q` cross. -/
noncomputable def cx (lam : ℝ) (P Q : ℝ × ℝ) : ℝ := (P.2 - Q.2) / (sl lam P - sl lam Q)

/-- Points of `A` whose dual line passes through the dual point `v`. -/
noncomputable def blk (A : Finset (ℝ × ℝ)) (lam : ℝ) (v : ℝ × ℝ) : Finset (ℝ × ℝ) :=
  A.filter fun Q => ht lam Q v.1 = v.2

/-- Number of points of `A` whose dual line passes strictly below `v`. -/
noncomputable def bet (A : Finset (ℝ × ℝ)) (lam : ℝ) (v : ℝ × ℝ) : ℕ :=
  #(A.filter fun Q => ht lam Q v.1 < v.2)

/-- Rank of `P` just before abscissa `x`. -/
noncomputable def rm (A : Finset (ℝ × ℝ)) (lam : ℝ) (x : ℝ) (P : ℝ × ℝ) : ℕ :=
  #(A.filter fun Q => ht lam Q x < ht lam P x ∨ (ht lam Q x = ht lam P x ∧ sl lam P < sl lam Q))

/-- Rank of `P` just after abscissa `x`. -/
noncomputable def rp (A : Finset (ℝ × ℝ)) (lam : ℝ) (x : ℝ) (P : ℝ × ℝ) : ℕ :=
  #(A.filter fun Q => ht lam Q x < ht lam P x ∨ (ht lam Q x = ht lam P x ∧ sl lam Q < sl lam P))

/-- Vertices of the arrangement: crossing points of two dual lines. -/
noncomputable def verts (A : Finset (ℝ × ℝ)) (lam : ℝ) : Finset (ℝ × ℝ) :=
  A.offDiag.image fun p => (cx lam p.1 p.2, ht lam p.1 (cx lam p.1 p.2))

/-- `v` cuts gap `g`: its block occupies ranks `g - 1` and `g`. -/
def cuts (A : Finset (ℝ × ℝ)) (lam : ℝ) (g : ℕ) (v : ℝ × ℝ) : Prop :=
  bet A lam v < g ∧ g < bet A lam v + #(blk A lam v)

/-- `v` touches gap `g` from above: its lowest rank is `g`. -/
def tchA (A : Finset (ℝ × ℝ)) (lam : ℝ) (g : ℕ) (v : ℝ × ℝ) : Prop :=
  bet A lam v = g

/-- `v` touches gap `g` from below: its highest rank is `g - 1`. -/
def tchB (A : Finset (ℝ × ℝ)) (lam : ℝ) (g : ℕ) (v : ℝ × ℝ) : Prop :=
  bet A lam v + #(blk A lam v) = g

/-- `P` lies on both `v` and `w`, `v` is left of `w`, and no other vertex on the dual line of
`P` lies strictly between them. -/
def Adj (A : Finset (ℝ × ℝ)) (lam : ℝ) (P v w : ℝ × ℝ) : Prop :=
  P ∈ blk A lam v ∧ P ∈ blk A lam w ∧ v.1 < w.1 ∧
    ∀ Q ∈ A, Q ≠ P → ¬ (v.1 < cx lam P Q ∧ cx lam P Q < w.1)

/-- A bounded triangular face of gap `g`: consecutive cuts `C`, `C'` with exactly one event
of the gap strictly between them, the touch `T`. -/
def Tri (A : Finset (ℝ × ℝ)) (lam : ℝ) (g : ℕ) (C T C' : ℝ × ℝ) : Prop :=
  C ∈ verts A lam ∧ T ∈ verts A lam ∧ C' ∈ verts A lam ∧
  cuts A lam g C ∧ cuts A lam g C' ∧ (tchA A lam g T ∨ tchB A lam g T) ∧
  C.1 < T.1 ∧ T.1 < C'.1 ∧
  ∀ e ∈ verts A lam, (cuts A lam g e ∨ tchA A lam g e ∨ tchB A lam g e) →
    C.1 < e.1 → e.1 < C'.1 → e = T

/-- A triple vertex all of whose six faces are triangles with triple vertices. -/
def Good (A : Finset (ℝ × ℝ)) (lam : ℝ) (v : ℝ × ℝ) : Prop :=
  v ∈ verts A lam ∧ #(blk A lam v) = 3 ∧
  (∃ T C', Tri A lam (bet A lam v + 1) v T C' ∧ #(blk A lam T) = 3 ∧ #(blk A lam C') = 3) ∧
  (∃ C T, Tri A lam (bet A lam v + 1) C T v ∧ #(blk A lam C) = 3 ∧ #(blk A lam T) = 3) ∧
  (∃ T C', Tri A lam (bet A lam v + 2) v T C' ∧ #(blk A lam T) = 3 ∧ #(blk A lam C') = 3) ∧
  (∃ C T, Tri A lam (bet A lam v + 2) C T v ∧ #(blk A lam C) = 3 ∧ #(blk A lam T) = 3) ∧
  (∃ C C', Tri A lam (bet A lam v) C v C' ∧ #(blk A lam C) = 3 ∧ #(blk A lam C') = 3) ∧
  (∃ C C', Tri A lam (bet A lam v + 3) C v C' ∧ #(blk A lam C) = 3 ∧ #(blk A lam C') = 3)

-- BEGIN FOUNDATION
/-! ### Foundation -/

section foundation

variable {A : Finset (ℝ × ℝ)} {lam : ℝ}

lemma ht_sub (lam : ℝ) (P Q : ℝ × ℝ) (h : sl lam P ≠ sl lam Q) (x : ℝ) :
    ht lam P x - ht lam Q x = (sl lam P - sl lam Q) * (x - cx lam P Q) := by
  have hd : sl lam P - sl lam Q ≠ 0 := sub_ne_zero.mpr h
  have hc : (sl lam P - sl lam Q) * cx lam P Q = P.2 - Q.2 := by
    unfold cx
    field_simp
  rw [mul_sub, hc]
  unfold ht
  ring

lemma cx_comm (lam : ℝ) (P Q : ℝ × ℝ) : cx lam P Q = cx lam Q P := by
  unfold cx
  rw [← neg_sub Q.2 P.2, ← neg_sub (sl lam Q) (sl lam P), neg_div_neg_eq]

/-- Sign analysis for a product with a positive factor. -/
lemma sign_aux {d t a b : ℝ} (hd : 0 < d) (hs : a - b = d * t) :
    (b < a ↔ 0 < t) ∧ (b = a ↔ t = 0) ∧ (a < b ↔ t < 0) := by
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, ⟨fun h => ?_, fun h => ?_⟩, ⟨fun h => ?_, fun h => ?_⟩⟩
  · by_contra hc
    have h0 : 0 ≤ d * (-t) := mul_nonneg hd.le (by linarith)
    nlinarith
  · have h0 := mul_pos hd h
    linarith
  · have h0 : d * t = 0 := by rw [← hs, h, sub_self]
    rcases mul_eq_zero.mp h0 with h1 | h1
    · linarith
    · exact h1
  · rw [h, mul_zero] at hs
    linarith
  · by_contra hc
    have h0 : 0 ≤ d * t := mul_nonneg hd.le (by linarith)
    linarith
  · have h0 : 0 < d * (-t) := mul_pos hd (by linarith)
    nlinarith

/-- Membership in the `rp` filter, for a point of smaller slope. -/
lemma rp_mem_of_lt {P Q : ℝ × ℝ} (h : sl lam Q < sl lam P) (x : ℝ) :
    (ht lam Q x < ht lam P x ∨ (ht lam Q x = ht lam P x ∧ sl lam Q < sl lam P)) ↔
      cx lam P Q ≤ x := by
  obtain ⟨h1, h2, h3⟩ := sign_aux (sub_pos.mpr h) (ht_sub lam P Q (ne_of_gt h) x)
  constructor
  · rintro (h4 | ⟨h4, -⟩)
    · linarith [h1.mp h4]
    · linarith [h2.mp h4]
  · intro h4
    rcases lt_or_eq_of_le h4 with h5 | h5
    · left
      exact h1.mpr (by linarith)
    · right
      exact ⟨h2.mpr (by linarith), h⟩

lemma rp_mem_of_gt {P Q : ℝ × ℝ} (h : sl lam P < sl lam Q) (x : ℝ) :
    (ht lam Q x < ht lam P x ∨ (ht lam Q x = ht lam P x ∧ sl lam Q < sl lam P)) ↔
      x < cx lam P Q := by
  have hs := ht_sub lam Q P (ne_of_gt h) x
  rw [cx_comm lam Q P] at hs
  obtain ⟨h1, h2, h3⟩ := sign_aux (sub_pos.mpr h) hs
  constructor
  · rintro (h4 | ⟨-, h4⟩)
    · linarith [h3.mp h4]
    · linarith
  · intro h4
    left
    exact h3.mpr (by linarith)

lemma rm_mem_of_lt {P Q : ℝ × ℝ} (h : sl lam Q < sl lam P) (x : ℝ) :
    (ht lam Q x < ht lam P x ∨ (ht lam Q x = ht lam P x ∧ sl lam P < sl lam Q)) ↔
      cx lam P Q < x := by
  obtain ⟨h1, h2, h3⟩ := sign_aux (sub_pos.mpr h) (ht_sub lam P Q (ne_of_gt h) x)
  constructor
  · rintro (h4 | ⟨-, h4⟩)
    · linarith [h1.mp h4]
    · linarith
  · intro h4
    left
    exact h1.mpr (by linarith)

lemma rm_mem_of_gt {P Q : ℝ × ℝ} (h : sl lam P < sl lam Q) (x : ℝ) :
    (ht lam Q x < ht lam P x ∨ (ht lam Q x = ht lam P x ∧ sl lam P < sl lam Q)) ↔
      x ≤ cx lam P Q := by
  have hs := ht_sub lam Q P (ne_of_gt h) x
  rw [cx_comm lam Q P] at hs
  obtain ⟨h1, h2, h3⟩ := sign_aux (sub_pos.mpr h) hs
  constructor
  · rintro (h4 | ⟨h4, -⟩)
    · linarith [h3.mp h4]
    · linarith [h2.mp h4.symm]
  · intro h4
    rcases lt_or_eq_of_le h4 with h5 | h5
    · left
      exact h3.mpr (by linarith)
    · right
      exact ⟨(h2.mpr (by linarith)).symm, h⟩

/-- Two points of `A` have equal height at `x` iff `x` is their crossing abscissa. -/
lemma ht_eq_iff (hinj : Set.InjOn (sl lam) A) {P Q : ℝ × ℝ} (hP : P ∈ A) (hQ : Q ∈ A)
    (hPQ : P ≠ Q) (x : ℝ) : ht lam P x = ht lam Q x ↔ x = cx lam P Q := by
  have hne : sl lam P ≠ sl lam Q := fun h => hPQ (hinj hP hQ h)
  have hs := ht_sub lam P Q hne x
  have hd : sl lam P - sl lam Q ≠ 0 := sub_ne_zero.mpr hne
  constructor
  · intro h
    have h0 : (sl lam P - sl lam Q) * (x - cx lam P Q) = 0 := by rw [← hs, h, sub_self]
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact absurd h1 hd
    · linarith
  · intro h
    have h0 : x - cx lam P Q = 0 := by linarith
    rw [h0, mul_zero] at hs
    linarith

lemma rm_lt (x : ℝ) {P : ℝ × ℝ} (hP : P ∈ A) : rm A lam x P < #A := by
  unfold rm
  refine lt_of_le_of_lt (Finset.card_le_card (?_ : _ ⊆ A.erase P))
    (Finset.card_erase_lt_of_mem hP)
  intro Q hQ
  rw [Finset.mem_filter] at hQ
  rw [Finset.mem_erase]
  refine ⟨?_, hQ.1⟩
  intro hQP
  rw [hQP] at hQ
  rcases hQ.2 with h | ⟨-, h⟩
  · exact lt_irrefl _ h
  · exact lt_irrefl _ h

lemma rp_lt (x : ℝ) {P : ℝ × ℝ} (hP : P ∈ A) : rp A lam x P < #A := by
  unfold rp
  refine lt_of_le_of_lt (Finset.card_le_card (?_ : _ ⊆ A.erase P))
    (Finset.card_erase_lt_of_mem hP)
  intro Q hQ
  rw [Finset.mem_filter] at hQ
  rw [Finset.mem_erase]
  refine ⟨?_, hQ.1⟩
  intro hQP
  rw [hQP] at hQ
  rcases hQ.2 with h | ⟨-, h⟩
  · exact lt_irrefl _ h
  · exact lt_irrefl _ h

/-- The number of elements below a given one, for a strict total order on a finset, is an
injective function. -/
lemma rank_injOn {α : Type*} (S : Finset α) (R : α → α → Prop) (F : α → Finset α)
    (hF : ∀ P Q, Q ∈ F P ↔ Q ∈ S ∧ R Q P)
    (hirr : ∀ a, ¬ R a a) (htr : ∀ a b c, R a b → R b c → R a c)
    (htot : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → R a b ∨ R b a) :
    ∀ P ∈ S, ∀ Q ∈ S, #(F P) = #(F Q) → P = Q := by
  have key : ∀ a ∈ S, ∀ b ∈ S, R a b → #(F a) < #(F b) := by
    intro a ha b hb hab
    apply Finset.card_lt_card
    have hsub : F a ⊆ F b := by
      intro Q hQ
      rw [hF] at hQ ⊢
      exact ⟨hQ.1, htr _ _ _ hQ.2 hab⟩
    rw [Finset.ssubset_iff_of_subset hsub]
    exact ⟨a, (hF b a).mpr ⟨ha, hab⟩, fun h => hirr a ((hF a a).mp h).2⟩
  intro P hP Q hQ h
  by_contra hne
  rcases htot P hP Q hQ hne with h1 | h1
  · have h2 := key P hP Q hQ h1
    omega
  · have h2 := key Q hQ P hP h1
    omega

lemma rm_injOn (hinj : Set.InjOn (sl lam) A) (x : ℝ) : Set.InjOn (rm A lam x) A := by
  intro P hP P' hP' h
  refine rank_injOn A
    (fun Q P => ht lam Q x < ht lam P x ∨ (ht lam Q x = ht lam P x ∧ sl lam P < sl lam Q))
    (fun P => A.filter fun Q =>
      ht lam Q x < ht lam P x ∨ (ht lam Q x = ht lam P x ∧ sl lam P < sl lam Q))
    (fun P Q => Finset.mem_filter) ?_ ?_ ?_ P hP P' hP' h
  · rintro a (h1 | ⟨-, h1⟩)
    · exact lt_irrefl _ h1
    · exact lt_irrefl _ h1
  · rintro a b c (h1 | ⟨h1, h3⟩) (h2 | ⟨h2, h4⟩)
    · left
      linarith
    · left
      linarith
    · left
      linarith
    · right
      exact ⟨h1.trans h2, h4.trans h3⟩
  · intro a ha b hb hab
    have hne : sl lam a ≠ sl lam b := fun h0 => hab (hinj ha hb h0)
    rcases lt_trichotomy (ht lam a x) (ht lam b x) with h1 | h1 | h1
    · exact Or.inl (Or.inl h1)
    · rcases lt_or_gt_of_ne hne with h2 | h2
      · exact Or.inr (Or.inr ⟨h1.symm, h2⟩)
      · exact Or.inl (Or.inr ⟨h1, h2⟩)
    · exact Or.inr (Or.inl h1)

lemma rp_injOn (hinj : Set.InjOn (sl lam) A) (x : ℝ) : Set.InjOn (rp A lam x) A := by
  intro P hP P' hP' h
  refine rank_injOn A
    (fun Q P => ht lam Q x < ht lam P x ∨ (ht lam Q x = ht lam P x ∧ sl lam Q < sl lam P))
    (fun P => A.filter fun Q =>
      ht lam Q x < ht lam P x ∨ (ht lam Q x = ht lam P x ∧ sl lam Q < sl lam P))
    (fun P Q => Finset.mem_filter) ?_ ?_ ?_ P hP P' hP' h
  · rintro a (h1 | ⟨-, h1⟩)
    · exact lt_irrefl _ h1
    · exact lt_irrefl _ h1
  · rintro a b c (h1 | ⟨h1, h3⟩) (h2 | ⟨h2, h4⟩)
    · left
      linarith
    · left
      linarith
    · left
      linarith
    · right
      exact ⟨h1.trans h2, h3.trans h4⟩
  · intro a ha b hb hab
    have hne : sl lam a ≠ sl lam b := fun h0 => hab (hinj ha hb h0)
    rcases lt_trichotomy (ht lam a x) (ht lam b x) with h1 | h1 | h1
    · exact Or.inl (Or.inl h1)
    · rcases lt_or_gt_of_ne hne with h2 | h2
      · exact Or.inl (Or.inr ⟨h1, h2⟩)
      · exact Or.inr (Or.inr ⟨h1.symm, h2⟩)
    · exact Or.inr (Or.inl h1)

lemma exists_rm_eq (hinj : Set.InjOn (sl lam) A) (x : ℝ) {r : ℕ} (hr : r < #A) :
    ∃ P ∈ A, rm A lam x P = r := by
  have himg : A.image (rm A lam x) = Finset.range #A := by
    apply Finset.eq_of_subset_of_card_le
    · intro s hs
      rw [Finset.mem_image] at hs
      obtain ⟨P, hP, rfl⟩ := hs
      exact Finset.mem_range.mpr (rm_lt x hP)
    · rw [Finset.card_image_of_injOn (rm_injOn hinj x), Finset.card_range]
  have hmem : r ∈ A.image (rm A lam x) := by
    rw [himg]
    exact Finset.mem_range.mpr hr
  exact Finset.mem_image.mp hmem

lemma exists_rp_eq (hinj : Set.InjOn (sl lam) A) (x : ℝ) {r : ℕ} (hr : r < #A) :
    ∃ P ∈ A, rp A lam x P = r := by
  have himg : A.image (rp A lam x) = Finset.range #A := by
    apply Finset.eq_of_subset_of_card_le
    · intro s hs
      rw [Finset.mem_image] at hs
      obtain ⟨P, hP, rfl⟩ := hs
      exact Finset.mem_range.mpr (rp_lt x hP)
    · rw [Finset.card_image_of_injOn (rp_injOn hinj x), Finset.card_range]
  have hmem : r ∈ A.image (rp A lam x) := by
    rw [himg]
    exact Finset.mem_range.mpr hr
  exact Finset.mem_image.mp hmem

/-- Ranks do not change on an interval without crossings. -/
lemma rp_eq_rm (hinj : Set.InjOn (sl lam) A) {P : ℝ × ℝ} (hP : P ∈ A) {x x' : ℝ} (hxx : x < x')
    (hno : ∀ Q ∈ A, Q ≠ P → ¬ (x < cx lam P Q ∧ cx lam P Q < x')) :
    rp A lam x P = rm A lam x' P := by
  unfold rp rm
  refine congrArg Finset.card (Finset.filter_congr fun Q hQ => ?_)
  by_cases hQP : Q = P
  · rw [hQP]
    simp
  · have hne : sl lam Q ≠ sl lam P := fun h => hQP (hinj hQ hP h)
    have hc := hno Q hQ hQP
    rcases lt_or_gt_of_ne hne with h | h
    · rw [rp_mem_of_lt h, rm_mem_of_lt h]
      constructor
      · intro h1
        linarith
      · intro h1
        by_contra h2
        exact hc ⟨not_le.mp h2, h1⟩
    · rw [rp_mem_of_gt h, rm_mem_of_gt h]
      constructor
      · intro h1
        by_contra h2
        exact hc ⟨h1, not_le.mp h2⟩
      · intro h1
        linarith

/-- A point with no crossing at `x` keeps its rank there. -/
lemma rm_eq_rp (hinj : Set.InjOn (sl lam) A) {P : ℝ × ℝ} (hP : P ∈ A) {x : ℝ}
    (hno : ∀ Q ∈ A, Q ≠ P → cx lam P Q ≠ x) : rm A lam x P = rp A lam x P := by
  unfold rp rm
  refine congrArg Finset.card (Finset.filter_congr fun Q hQ => ?_)
  by_cases hQP : Q = P
  · rw [hQP]
  · have hne : sl lam Q ≠ sl lam P := fun h => hQP (hinj hQ hP h)
    have hc := hno Q hQ hQP
    rcases lt_or_gt_of_ne hne with h | h
    · rw [rp_mem_of_lt h, rm_mem_of_lt h]
      constructor
      · intro h1
        exact le_of_lt h1
      · intro h1
        exact lt_of_le_of_ne h1 hc
    · rw [rp_mem_of_gt h, rm_mem_of_gt h]
      constructor
      · intro h1
        exact lt_of_le_of_ne h1 (Ne.symm hc)
      · intro h1
        exact le_of_lt h1

lemma blk_subset (A : Finset (ℝ × ℝ)) (lam : ℝ) (v : ℝ × ℝ) : blk A lam v ⊆ A := by
  unfold blk
  exact Finset.filter_subset _ _

lemma mem_blk {v P : ℝ × ℝ} : P ∈ blk A lam v ↔ P ∈ A ∧ ht lam P v.1 = v.2 := by
  unfold blk
  exact Finset.mem_filter

/-- The points on or below a dual point. -/
lemma bet_add_card_eq (A : Finset (ℝ × ℝ)) (lam : ℝ) (v : ℝ × ℝ) :
    bet A lam v + #(blk A lam v) = #(A.filter fun Q => ht lam Q v.1 ≤ v.2) := by
  unfold bet blk
  rw [← Finset.card_union_of_disjoint
    (Finset.disjoint_filter.mpr fun Q _ h1 h2 => absurd h2 (ne_of_lt h1)), ← Finset.filter_or]
  exact congrArg Finset.card (Finset.filter_congr fun Q _ => le_iff_lt_or_eq.symm)

lemma bet_add_card_le (A : Finset (ℝ × ℝ)) (lam : ℝ) (v : ℝ × ℝ) :
    bet A lam v + #(blk A lam v) ≤ #A := by
  rw [bet_add_card_eq]
  exact Finset.card_le_card (Finset.filter_subset _ _)

/-- Rank before the crossing of a point of a block: larger slopes are lower. -/
lemma rm_blk {v P : ℝ × ℝ} (hP : P ∈ blk A lam v) :
    rm A lam v.1 P = bet A lam v + #((blk A lam v).filter fun Q => sl lam P < sl lam Q) := by
  obtain ⟨hPA, hPv⟩ := mem_blk.mp hP
  unfold rm bet
  rw [← Finset.card_union_of_disjoint]
  · refine congrArg Finset.card ?_
    ext Q
    simp only [Finset.mem_filter, Finset.mem_union, mem_blk, hPv]
    tauto
  · rw [Finset.disjoint_left]
    intro Q h1 h2
    rw [Finset.mem_filter] at h1 h2
    rw [mem_blk] at h2
    linarith [h1.2, h2.1.2]

/-- Rank after the crossing of a point of a block: smaller slopes are lower. -/
lemma rp_blk {v P : ℝ × ℝ} (hP : P ∈ blk A lam v) :
    rp A lam v.1 P = bet A lam v + #((blk A lam v).filter fun Q => sl lam Q < sl lam P) := by
  obtain ⟨hPA, hPv⟩ := mem_blk.mp hP
  unfold rp bet
  rw [← Finset.card_union_of_disjoint]
  · refine congrArg Finset.card ?_
    ext Q
    simp only [Finset.mem_filter, Finset.mem_union, mem_blk, hPv]
    tauto
  · rw [Finset.disjoint_left]
    intro Q h1 h2
    rw [Finset.mem_filter] at h1 h2
    rw [mem_blk] at h2
    linarith [h1.2, h2.1.2]

lemma bet_le_rm {v P : ℝ × ℝ} (hP : P ∈ blk A lam v) : bet A lam v ≤ rm A lam v.1 P := by
  rw [rm_blk hP]
  exact Nat.le_add_right _ _

lemma rm_lt_bet_add {v P : ℝ × ℝ} (hP : P ∈ blk A lam v) :
    rm A lam v.1 P < bet A lam v + #(blk A lam v) := by
  rw [rm_blk hP]
  have h : #((blk A lam v).filter fun Q => sl lam P < sl lam Q) < #(blk A lam v) := by
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)]
    exact ⟨P, hP, fun h => lt_irrefl _ (Finset.mem_filter.mp h).2⟩
  omega

lemma bet_le_rp {v P : ℝ × ℝ} (hP : P ∈ blk A lam v) : bet A lam v ≤ rp A lam v.1 P := by
  rw [rp_blk hP]
  exact Nat.le_add_right _ _

lemma rp_lt_bet_add {v P : ℝ × ℝ} (hP : P ∈ blk A lam v) :
    rp A lam v.1 P < bet A lam v + #(blk A lam v) := by
  rw [rp_blk hP]
  have h : #((blk A lam v).filter fun Q => sl lam Q < sl lam P) < #(blk A lam v) := by
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)]
    exact ⟨P, hP, fun h => lt_irrefl _ (Finset.mem_filter.mp h).2⟩
  omega

/-- A crossing reverses the block. -/
lemma rm_add_rp (hinj : Set.InjOn (sl lam) A) {v P : ℝ × ℝ} (hP : P ∈ blk A lam v) :
    rm A lam v.1 P + rp A lam v.1 P + 1 = 2 * bet A lam v + #(blk A lam v) := by
  have e : blk A lam v = insert P (((blk A lam v).filter fun Q => sl lam P < sl lam Q) ∪
      ((blk A lam v).filter fun Q => sl lam Q < sl lam P)) := by
    ext Q
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hQ
      by_cases hQP : Q = P
      · left
        exact hQP
      · right
        have hne : sl lam Q ≠ sl lam P :=
          fun h => hQP (hinj (blk_subset A lam v hQ) (blk_subset A lam v hP) h)
        rcases lt_or_gt_of_ne hne with h | h
        · right
          exact ⟨hQ, h⟩
        · left
          exact ⟨hQ, h⟩
    · rintro (h | ⟨h, -⟩ | ⟨h, -⟩)
      · rw [h]
        exact hP
      · exact h
      · exact h
  have hnot : P ∉ ((blk A lam v).filter fun Q => sl lam P < sl lam Q) ∪
      ((blk A lam v).filter fun Q => sl lam Q < sl lam P) := by
    simp only [Finset.mem_union, Finset.mem_filter]
    rintro (⟨-, h⟩ | ⟨-, h⟩)
    · exact lt_irrefl _ h
    · exact lt_irrefl _ h
  have hdis : Disjoint ((blk A lam v).filter fun Q => sl lam P < sl lam Q)
      ((blk A lam v).filter fun Q => sl lam Q < sl lam P) :=
    Finset.disjoint_filter.mpr fun Q _ h1 h2 => lt_asymm h1 h2
  have h3 : #(blk A lam v) = #((blk A lam v).filter fun Q => sl lam P < sl lam Q) +
      #((blk A lam v).filter fun Q => sl lam Q < sl lam P) + 1 := by
    calc #(blk A lam v) = #(insert P (((blk A lam v).filter fun Q => sl lam P < sl lam Q) ∪
          ((blk A lam v).filter fun Q => sl lam Q < sl lam P))) := congrArg Finset.card e
      _ = _ := by rw [Finset.card_insert_of_notMem hnot, Finset.card_union_of_disjoint hdis]
  rw [rm_blk hP, rp_blk hP]
  omega

/-- A point whose rank before `v.1` is in the range of the block of `v` belongs to it. -/
lemma mem_blk_of_rm {v P : ℝ × ℝ} (hP : P ∈ A) (h1 : bet A lam v ≤ rm A lam v.1 P)
    (h2 : rm A lam v.1 P < bet A lam v + #(blk A lam v)) : P ∈ blk A lam v := by
  rw [mem_blk]
  refine ⟨hP, ?_⟩
  rcases lt_trichotomy (ht lam P v.1) v.2 with h | h | h
  · exfalso
    have h3 : rm A lam v.1 P < bet A lam v := by
      unfold rm bet
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_of_subset]
      · refine ⟨P, Finset.mem_filter.mpr ⟨hP, h⟩, fun h4 => ?_⟩
        rcases (Finset.mem_filter.mp h4).2 with h5 | ⟨-, h5⟩
        · exact lt_irrefl _ h5
        · exact lt_irrefl _ h5
      · intro Q hQ
        rw [Finset.mem_filter] at hQ ⊢
        refine ⟨hQ.1, ?_⟩
        rcases hQ.2 with h5 | ⟨h5, -⟩
        · linarith
        · linarith
    omega
  · exact h
  · exfalso
    have h3 : bet A lam v + #(blk A lam v) ≤ rm A lam v.1 P := by
      rw [bet_add_card_eq]
      unfold rm
      apply Finset.card_le_card
      intro Q hQ
      rw [Finset.mem_filter] at hQ ⊢
      exact ⟨hQ.1, Or.inl (lt_of_le_of_lt hQ.2 h)⟩
    omega

lemma mem_blk_of_rp {v P : ℝ × ℝ} (hP : P ∈ A) (h1 : bet A lam v ≤ rp A lam v.1 P)
    (h2 : rp A lam v.1 P < bet A lam v + #(blk A lam v)) : P ∈ blk A lam v := by
  rw [mem_blk]
  refine ⟨hP, ?_⟩
  rcases lt_trichotomy (ht lam P v.1) v.2 with h | h | h
  · exfalso
    have h3 : rp A lam v.1 P < bet A lam v := by
      unfold rp bet
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_of_subset]
      · refine ⟨P, Finset.mem_filter.mpr ⟨hP, h⟩, fun h4 => ?_⟩
        rcases (Finset.mem_filter.mp h4).2 with h5 | ⟨-, h5⟩
        · exact lt_irrefl _ h5
        · exact lt_irrefl _ h5
      · intro Q hQ
        rw [Finset.mem_filter] at hQ ⊢
        refine ⟨hQ.1, ?_⟩
        rcases hQ.2 with h5 | ⟨h5, -⟩
        · linarith
        · linarith
    omega
  · exact h
  · exfalso
    have h3 : bet A lam v + #(blk A lam v) ≤ rp A lam v.1 P := by
      rw [bet_add_card_eq]
      unfold rp
      apply Finset.card_le_card
      intro Q hQ
      rw [Finset.mem_filter] at hQ ⊢
      exact ⟨hQ.1, Or.inl (lt_of_le_of_lt hQ.2 h)⟩
    omega

lemma exists_mem_blk_rm (hinj : Set.InjOn (sl lam) A) {v : ℝ × ℝ} {r : ℕ}
    (h1 : bet A lam v ≤ r) (h2 : r < bet A lam v + #(blk A lam v)) :
    ∃ P ∈ blk A lam v, rm A lam v.1 P = r := by
  have hr : r < #A := lt_of_lt_of_le h2 (bet_add_card_le A lam v)
  obtain ⟨P, hP, hPr⟩ := exists_rm_eq hinj v.1 hr
  rw [← hPr] at h1 h2
  exact ⟨P, mem_blk_of_rm hP h1 h2, hPr⟩

lemma exists_mem_blk_rp (hinj : Set.InjOn (sl lam) A) {v : ℝ × ℝ} {r : ℕ}
    (h1 : bet A lam v ≤ r) (h2 : r < bet A lam v + #(blk A lam v)) :
    ∃ P ∈ blk A lam v, rp A lam v.1 P = r := by
  have hr : r < #A := lt_of_lt_of_le h2 (bet_add_card_le A lam v)
  obtain ⟨P, hP, hPr⟩ := exists_rp_eq hinj v.1 hr
  rw [← hPr] at h1 h2
  exact ⟨P, mem_blk_of_rp hP h1 h2, hPr⟩

/-- The crossing abscissa of two points of a block is the abscissa of the vertex. -/
lemma cx_of_mem_blk (hinj : Set.InjOn (sl lam) A) {v P Q : ℝ × ℝ} (hP : P ∈ blk A lam v)
    (hQ : Q ∈ blk A lam v) (hPQ : P ≠ Q) : cx lam P Q = v.1 := by
  obtain ⟨hPA, hPv⟩ := mem_blk.mp hP
  obtain ⟨hQA, hQv⟩ := mem_blk.mp hQ
  exact ((ht_eq_iff hinj hPA hQA hPQ v.1).mp (hPv.trans hQv.symm)).symm

/-- A vertex is determined by two of its points. -/
lemma eq_of_mem_blk (hinj : Set.InjOn (sl lam) A) {v w P Q : ℝ × ℝ} (hPv : P ∈ blk A lam v)
    (hQv : Q ∈ blk A lam v) (hPw : P ∈ blk A lam w) (hQw : Q ∈ blk A lam w) (hPQ : P ≠ Q) :
    v = w := by
  have h1 := cx_of_mem_blk hinj hPv hQv hPQ
  have h2 := cx_of_mem_blk hinj hPw hQw hPQ
  have h3 := (mem_blk.mp hPv).2
  have h4 := (mem_blk.mp hPw).2
  have h5 : v.1 = w.1 := h1.symm.trans h2
  apply Prod.ext h5
  rw [← h3, ← h4, h5]

/-- The vertex through two points of `A` (auxiliary form). -/
lemma vertex_of_pair_aux (hinj : Set.InjOn (sl lam) A) {P Q : ℝ × ℝ} (hP : P ∈ A) (hQ : Q ∈ A)
    (hPQ : P ≠ Q) :
    (cx lam P Q, ht lam P (cx lam P Q)) ∈ verts A lam ∧
      P ∈ blk A lam (cx lam P Q, ht lam P (cx lam P Q)) ∧
      Q ∈ blk A lam (cx lam P Q, ht lam P (cx lam P Q)) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold verts
    exact Finset.mem_image.mpr ⟨(P, Q), Finset.mem_offDiag.mpr ⟨hP, hQ, hPQ⟩, rfl⟩
  · exact mem_blk.mpr ⟨hP, rfl⟩
  · exact mem_blk.mpr ⟨hQ, ((ht_eq_iff hinj hP hQ hPQ _).mpr rfl).symm⟩

/-- A dual point lying on the dual lines of two points is the vertex they span. -/
lemma eq_vertex_of_mem_blk (hinj : Set.InjOn (sl lam) A) {v P Q : ℝ × ℝ}
    (hP : P ∈ blk A lam v) (hQ : Q ∈ blk A lam v) (hPQ : P ≠ Q) :
    (cx lam P Q, ht lam P (cx lam P Q)) = v := by
  have h1 := cx_of_mem_blk hinj hP hQ hPQ
  have h2 := (mem_blk.mp hP).2
  apply Prod.ext
  · exact h1
  · show ht lam P (cx lam P Q) = v.2
    rw [h1]
    exact h2

lemma mem_verts (hinj : Set.InjOn (sl lam) A) {v : ℝ × ℝ} :
    v ∈ verts A lam ↔ ∃ P ∈ blk A lam v, ∃ Q ∈ blk A lam v, P ≠ Q := by
  constructor
  · intro hv
    unfold verts at hv
    obtain ⟨⟨P, Q⟩, hpq, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨hP, hQ, hPQ⟩ := Finset.mem_offDiag.mp hpq
    obtain ⟨-, h1, h2⟩ := vertex_of_pair_aux hinj hP hQ hPQ
    exact ⟨P, h1, Q, h2, hPQ⟩
  · rintro ⟨P, hP, Q, hQ, hPQ⟩
    rw [← eq_vertex_of_mem_blk hinj hP hQ hPQ]
    exact (vertex_of_pair_aux hinj (blk_subset A lam v hP) (blk_subset A lam v hQ) hPQ).1

/-- The vertex through two points of `A`. -/
lemma vertex_of_pair (hinj : Set.InjOn (sl lam) A) {P Q : ℝ × ℝ} (hP : P ∈ A) (hQ : Q ∈ A)
    (hPQ : P ≠ Q) :
    (cx lam P Q, ht lam P (cx lam P Q)) ∈ verts A lam ∧
      P ∈ blk A lam (cx lam P Q, ht lam P (cx lam P Q)) ∧
      Q ∈ blk A lam (cx lam P Q, ht lam P (cx lam P Q)) :=
  vertex_of_pair_aux hinj hP hQ hPQ

lemma two_le_card_blk (hinj : Set.InjOn (sl lam) A) {v : ℝ × ℝ} (hv : v ∈ verts A lam) :
    2 ≤ #(blk A lam v) := by
  obtain ⟨P, hP, Q, hQ, hPQ⟩ := (mem_verts hinj).mp hv
  exact Finset.one_lt_card.mpr ⟨P, hP, Q, hQ, hPQ⟩

/-- Counting ordered pairs of distinct points by the vertex they span. -/
lemma pair_count (hinj : Set.InjOn (sl lam) A) :
    #A * (#A - 1) = ∑ v ∈ verts A lam, #(blk A lam v) * (#(blk A lam v) - 1) := by
  have hcard : ∀ s : Finset (ℝ × ℝ), #s * (#s - 1) = #s.offDiag := by
    intro s
    rw [Finset.offDiag_card, Nat.mul_sub_one]
  rw [hcard A]
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun p : (ℝ × ℝ) × (ℝ × ℝ) => (cx lam p.1 p.2, ht lam p.1 (cx lam p.1 p.2)))
    (t := verts A lam) (fun p hp => Finset.mem_image_of_mem _ hp)]
  apply Finset.sum_congr rfl
  intro v hv
  rw [hcard]
  refine congrArg Finset.card ?_
  ext ⟨P, Q⟩
  simp only [Finset.mem_filter, Finset.mem_offDiag]
  constructor
  · rintro ⟨⟨hP, hQ, hPQ⟩, hv2⟩
    obtain ⟨-, h1, h2⟩ := vertex_of_pair hinj hP hQ hPQ
    rw [hv2] at h1 h2
    exact ⟨h1, h2, hPQ⟩
  · rintro ⟨hP, hQ, hPQ⟩
    exact ⟨⟨blk_subset A lam v hP, blk_subset A lam v hQ, hPQ⟩,
      eq_vertex_of_mem_blk hinj hP hQ hPQ⟩

/-- The first vertex on the dual line of `P` after `x`, when `P` has a crossing in `(x, x')`:
its block contains the rank of `P` just after `x`. -/
lemma occ_aux (hinj : Set.InjOn (sl lam) A) {x x' : ℝ} {P Q1 : ℝ × ℝ} (hP : P ∈ A)
    (hQ1A : Q1 ∈ A) (hQ1P : Q1 ≠ P) (hQ1x : x < cx lam P Q1) (hQ1x' : cx lam P Q1 < x') :
    ∃ e ∈ verts A lam, x < e.1 ∧ e.1 < x' ∧ bet A lam e ≤ rp A lam x P ∧
      rp A lam x P < bet A lam e + #(blk A lam e) := by
  have hS : (A.filter fun Q => Q ≠ P ∧ x < cx lam P Q ∧ cx lam P Q < x').Nonempty :=
    ⟨Q1, Finset.mem_filter.mpr ⟨hQ1A, hQ1P, hQ1x, hQ1x'⟩⟩
  obtain ⟨Q0, hQ0, hmin⟩ := Finset.exists_min_image _ (fun Q => cx lam P Q) hS
  obtain ⟨hQ0A, hQ0P, hQ0x, hQ0x'⟩ := Finset.mem_filter.mp hQ0
  obtain ⟨hv, hPe, -⟩ := vertex_of_pair hinj hP hQ0A (Ne.symm hQ0P)
  have hno : ∀ Q ∈ A, Q ≠ P → ¬ (x < cx lam P Q ∧ cx lam P Q < cx lam P Q0) := by
    rintro Q hQ hQP ⟨h1, h2⟩
    have h3 := hmin Q (Finset.mem_filter.mpr ⟨hQ, hQP, h1, by linarith⟩)
    linarith
  have heq := rp_eq_rm hinj hP hQ0x hno
  refine ⟨_, hv, hQ0x, hQ0x', ?_, ?_⟩
  · rw [heq]
    exact bet_le_rm hPe
  · rw [heq]
    exact rm_lt_bet_add hPe

/-- The occupant of rank `g - 1` does not change while no vertex cuts gap `g` or touches it
from below. -/
lemma occ_low (hinj : Set.InjOn (sl lam) A) {g : ℕ} {x x' : ℝ} (hxx : x < x')
    (hno : ∀ e ∈ verts A lam, x < e.1 → e.1 < x' → ¬ cuts A lam g e ∧ ¬ tchB A lam g e)
    {P : ℝ × ℝ} (hP : P ∈ A) (hr : rp A lam x P + 1 = g) :
    (∀ Q ∈ A, Q ≠ P → ¬ (x < cx lam P Q ∧ cx lam P Q < x')) ∧ rm A lam x' P + 1 = g := by
  have hfirst : ∀ Q ∈ A, Q ≠ P → ¬ (x < cx lam P Q ∧ cx lam P Q < x') := by
    rintro Q hQ hQP ⟨h1, h2⟩
    obtain ⟨e, he, hxe, hex, hb1, hb2⟩ := occ_aux hinj hP hQ hQP h1 h2
    obtain ⟨hn1, hn2⟩ := hno e he hxe hex
    unfold cuts at hn1
    unfold tchB at hn2
    omega
  refine ⟨hfirst, ?_⟩
  rw [← rp_eq_rm hinj hP hxx hfirst]
  exact hr

/-- The occupant of rank `g` does not change while no vertex cuts gap `g` or touches it
from above. -/
lemma occ_high (hinj : Set.InjOn (sl lam) A) {g : ℕ} {x x' : ℝ} (hxx : x < x')
    (hno : ∀ e ∈ verts A lam, x < e.1 → e.1 < x' → ¬ cuts A lam g e ∧ ¬ tchA A lam g e)
    {P : ℝ × ℝ} (hP : P ∈ A) (hr : rp A lam x P = g) :
    (∀ Q ∈ A, Q ≠ P → ¬ (x < cx lam P Q ∧ cx lam P Q < x')) ∧ rm A lam x' P = g := by
  have hfirst : ∀ Q ∈ A, Q ≠ P → ¬ (x < cx lam P Q ∧ cx lam P Q < x') := by
    rintro Q hQ hQP ⟨h1, h2⟩
    obtain ⟨e, he, hxe, hex, hb1, hb2⟩ := occ_aux hinj hP hQ hQP h1 h2
    obtain ⟨hn1, hn2⟩ := hno e he hxe hex
    unfold cuts at hn1
    unfold tchA at hn2
    omega
  refine ⟨hfirst, ?_⟩
  rw [← rp_eq_rm hinj hP hxx hfirst]
  exact hr

/-- The three sides of a triangular face: each pair of its vertices shares a point of `A`
which has no other vertex between them, with the stated ranks. -/
lemma tri_face (hinj : Set.InjOn (sl lam) A) {g : ℕ} {C T C' : ℝ × ℝ}
    (h : Tri A lam g C T C') :
    ∃ a b c : ℝ × ℝ, Adj A lam a C T ∧ Adj A lam b T C' ∧ Adj A lam c C C' ∧
      ((tchA A lam g T ∧ rp A lam C.1 a = g ∧ rm A lam T.1 a = g ∧ rp A lam T.1 b = g ∧
          rm A lam C'.1 b = g ∧ rp A lam C.1 c + 1 = g ∧ rm A lam C'.1 c + 1 = g) ∨
       (tchB A lam g T ∧ rp A lam C.1 a + 1 = g ∧ rm A lam T.1 a + 1 = g ∧
          rp A lam T.1 b + 1 = g ∧ rm A lam C'.1 b + 1 = g ∧ rp A lam C.1 c = g ∧
          rm A lam C'.1 c = g)) := by
  obtain ⟨hC, hT, hC', hcC, hcC', hT', hCT, hTC', hev⟩ := h
  have h2T := two_le_card_blk hinj hT
  obtain ⟨hcC1, hcC2⟩ : bet A lam C < g ∧ g < bet A lam C + #(blk A lam C) := hcC
  obtain ⟨hcD1, hcD2⟩ : bet A lam C' < g ∧ g < bet A lam C' + #(blk A lam C') := hcC'
  have hCC' : C.1 < C'.1 := lt_trans hCT hTC'
  obtain ⟨w, hwC, hw⟩ := exists_mem_blk_rp hinj (v := C) (r := g - 1) (by omega) (by omega)
  obtain ⟨u, huC, hu⟩ := exists_mem_blk_rp hinj (v := C) (r := g) (by omega) (by omega)
  have hwA := blk_subset A lam C hwC
  have huA := blk_subset A lam C huC
  have hw0 : rp A lam C.1 w + 1 = g := by omega
  have hnoL : ∀ e ∈ verts A lam, C.1 < e.1 → e.1 < T.1 →
      ¬ (cuts A lam g e ∨ tchA A lam g e ∨ tchB A lam g e) := by
    intro e he h1 h2 hc
    have heT := hev e he hc h1 (lt_trans h2 hTC')
    rw [heT] at h2
    exact lt_irrefl _ h2
  have hnoR : ∀ e ∈ verts A lam, T.1 < e.1 → e.1 < C'.1 →
      ¬ (cuts A lam g e ∨ tchA A lam g e ∨ tchB A lam g e) := by
    intro e he h1 h2 hc
    have heT := hev e he hc (lt_trans hCT h1) h2
    rw [heT] at h1
    exact lt_irrefl _ h1
  rcases hT' with hTA | hTB
  · have hTA1 : bet A lam T = g := hTA
    have hnc : ¬ cuts A lam g T := by
      unfold cuts
      omega
    have hnb : ¬ tchB A lam g T := by
      unfold tchB
      omega
    have hno1 : ∀ e ∈ verts A lam, C.1 < e.1 → e.1 < C'.1 →
        ¬ cuts A lam g e ∧ ¬ tchB A lam g e := by
      intro e he h1 h2
      constructor
      · intro hc
        have heT := hev e he (Or.inl hc) h1 h2
        rw [heT] at hc
        exact hnc hc
      · intro hb
        have heT := hev e he (Or.inr (Or.inr hb)) h1 h2
        rw [heT] at hb
        exact hnb hb
    obtain ⟨hw1, hw2⟩ := occ_low hinj hCC' hno1 hwA hw0
    have hwD : w ∈ blk A lam C' := mem_blk_of_rm hwA (by omega) (by omega)
    obtain ⟨hu1, hu2⟩ := occ_high hinj hCT
      (fun e he h1 h2 => ⟨fun hc => hnoL e he h1 h2 (Or.inl hc),
        fun hb => hnoL e he h1 h2 (Or.inr (Or.inl hb))⟩) huA hu
    have huT : u ∈ blk A lam T := mem_blk_of_rm huA (by omega) (by omega)
    obtain ⟨u2, hu2T, hu2r⟩ := exists_mem_blk_rp hinj (v := T) (r := g) (by omega) (by omega)
    have hu2A := blk_subset A lam T hu2T
    obtain ⟨hu21, hu22⟩ := occ_high hinj hTC'
      (fun e he h1 h2 => ⟨fun hc => hnoR e he h1 h2 (Or.inl hc),
        fun hb => hnoR e he h1 h2 (Or.inr (Or.inl hb))⟩) hu2A hu2r
    have hu2D : u2 ∈ blk A lam C' := mem_blk_of_rm hu2A (by omega) (by omega)
    exact ⟨u, u2, w, ⟨huC, huT, hCT, hu1⟩, ⟨hu2T, hu2D, hTC', hu21⟩, ⟨hwC, hwD, hCC', hw1⟩,
      Or.inl ⟨hTA, hu, hu2, hu2r, hu22, hw0, hw2⟩⟩
  · have hTB1 : bet A lam T + #(blk A lam T) = g := hTB
    have hnc : ¬ cuts A lam g T := by
      unfold cuts
      omega
    have hna : ¬ tchA A lam g T := by
      unfold tchA
      omega
    have hno1 : ∀ e ∈ verts A lam, C.1 < e.1 → e.1 < C'.1 →
        ¬ cuts A lam g e ∧ ¬ tchA A lam g e := by
      intro e he h1 h2
      constructor
      · intro hc
        have heT := hev e he (Or.inl hc) h1 h2
        rw [heT] at hc
        exact hnc hc
      · intro hb
        have heT := hev e he (Or.inr (Or.inl hb)) h1 h2
        rw [heT] at hb
        exact hna hb
    obtain ⟨hu1, hu2⟩ := occ_high hinj hCC' hno1 huA hu
    have huD : u ∈ blk A lam C' := mem_blk_of_rm huA (by omega) (by omega)
    obtain ⟨hw1, hw2⟩ := occ_low hinj hCT
      (fun e he h1 h2 => ⟨fun hc => hnoL e he h1 h2 (Or.inl hc),
        fun hb => hnoL e he h1 h2 (Or.inr (Or.inr hb))⟩) hwA hw0
    have hwT : w ∈ blk A lam T := mem_blk_of_rm hwA (by omega) (by omega)
    obtain ⟨w2, hw2T, hw2r⟩ :=
      exists_mem_blk_rp hinj (v := T) (r := g - 1) (by omega) (by omega)
    have hw2A := blk_subset A lam T hw2T
    have hw20 : rp A lam T.1 w2 + 1 = g := by omega
    obtain ⟨hw21, hw22⟩ := occ_low hinj hTC'
      (fun e he h1 h2 => ⟨fun hc => hnoR e he h1 h2 (Or.inl hc),
        fun hb => hnoR e he h1 h2 (Or.inr (Or.inr hb))⟩) hw2A hw20
    have hw2D : w2 ∈ blk A lam C' := mem_blk_of_rm hw2A (by omega) (by omega)
    exact ⟨w, w2, u, ⟨hwC, hwT, hCT, hw1⟩, ⟨hw2T, hw2D, hTC', hw21⟩, ⟨huC, huD, hCC', hu1⟩,
      Or.inr ⟨hTB, hw0, hw2, hw20, hw22, hu, hu2⟩⟩

/-- A vertex contains a second point besides any given one. -/
lemma exists_ne_mem_blk (hinj : Set.InjOn (sl lam) A) {v : ℝ × ℝ} (hv : v ∈ verts A lam)
    (P : ℝ × ℝ) : ∃ Q ∈ blk A lam v, Q ≠ P :=
  Finset.exists_mem_ne (two_le_card_blk hinj hv) P

/-- The vertex following `v` on the dual line of `P` is unique. -/
lemma adj_right_unique (hinj : Set.InjOn (sl lam) A) {P v w w' : ℝ × ℝ}
    (h : Adj A lam P v w) (h' : Adj A lam P v w') (hw : w ∈ verts A lam)
    (hw' : w' ∈ verts A lam) : w = w' := by
  obtain ⟨hPv, hPw, hvw, hno⟩ := h
  obtain ⟨-, hPw', hvw', hno'⟩ := h'
  have key : w.1 = w'.1 := by
    rcases lt_trichotomy w.1 w'.1 with hlt | heq | hgt
    · exfalso
      obtain ⟨Q, hQ, hQP⟩ := exists_ne_mem_blk hinj hw P
      have hcx := cx_of_mem_blk hinj hPw hQ (Ne.symm hQP)
      refine hno' Q (blk_subset A lam w hQ) hQP ⟨?_, ?_⟩
      · rw [hcx]
        exact hvw
      · rw [hcx]
        exact hlt
    · exact heq
    · exfalso
      obtain ⟨Q, hQ, hQP⟩ := exists_ne_mem_blk hinj hw' P
      have hcx := cx_of_mem_blk hinj hPw' hQ (Ne.symm hQP)
      refine hno Q (blk_subset A lam w' hQ) hQP ⟨?_, ?_⟩
      · rw [hcx]
        exact hvw'
      · rw [hcx]
        exact hgt
  apply Prod.ext key
  rw [← (mem_blk.mp hPw).2, ← (mem_blk.mp hPw').2, key]

/-- The vertex preceding `w` on the dual line of `P` is unique. -/
lemma adj_left_unique (hinj : Set.InjOn (sl lam) A) {P v v' w : ℝ × ℝ}
    (h : Adj A lam P v w) (h' : Adj A lam P v' w) (hv : v ∈ verts A lam)
    (hv' : v' ∈ verts A lam) : v = v' := by
  obtain ⟨hPv, hPw, hvw, hno⟩ := h
  obtain ⟨hPv', -, hvw', hno'⟩ := h'
  have key : v.1 = v'.1 := by
    rcases lt_trichotomy v.1 v'.1 with hlt | heq | hgt
    · exfalso
      obtain ⟨Q, hQ, hQP⟩ := exists_ne_mem_blk hinj hv' P
      have hcx := cx_of_mem_blk hinj hPv' hQ (Ne.symm hQP)
      refine hno Q (blk_subset A lam v' hQ) hQP ⟨?_, ?_⟩
      · rw [hcx]
        exact hlt
      · rw [hcx]
        exact hvw'
    · exact heq
    · exfalso
      obtain ⟨Q, hQ, hQP⟩ := exists_ne_mem_blk hinj hv P
      have hcx := cx_of_mem_blk hinj hPv hQ (Ne.symm hQP)
      refine hno' Q (blk_subset A lam v hQ) hQP ⟨?_, ?_⟩
      · rw [hcx]
        exact hgt
      · rw [hcx]
        exact hvw
  apply Prod.ext key
  rw [← (mem_blk.mp hPv).2, ← (mem_blk.mp hPv').2, key]

/-- Vertices on the same vertical line of the dual plane: the higher one has everything on
or below the lower one strictly below it. -/
lemma bet_mono {e e' : ℝ × ℝ} (h1 : e.1 = e'.1) (h2 : e.2 < e'.2) :
    bet A lam e + #(blk A lam e) ≤ bet A lam e' := by
  rw [bet_add_card_eq]
  unfold bet
  apply Finset.card_le_card
  intro Q hQ
  rw [Finset.mem_filter] at hQ ⊢
  refine ⟨hQ.1, ?_⟩
  rw [← h1]
  exact lt_of_le_of_lt hQ.2 h2

end foundation
-- END FOUNDATION

/-! ### The three main parts -/

-- BEGIN COUNT
/-! #### Abstract counting along one gap -/

section comb

variable {α : Type*} (f : α → ℝ) (Cut Tch : Finset α)

/-- Abstract triangle: consecutive cuts with exactly one event strictly between. -/
def ATri (C T C' : α) : Prop :=
  C ∈ Cut ∧ T ∈ Tch ∧ C' ∈ Cut ∧ f C < f T ∧ f T < f C' ∧
    ∀ e, (e ∈ Cut ∨ e ∈ Tch) → f C < f e → f e < f C' → e = T

/-- Touches with no cut to the left. -/
noncomputable def aTL : Finset α := Tch.filter fun T => ∀ C ∈ Cut, ¬ f C < f T

/-- Touches with no cut to the right. -/
noncomputable def aTR : Finset α := Tch.filter fun T => ∀ C ∈ Cut, ¬ f T < f C

/-- Cuts which are not the left vertex of a triangle. -/
noncomputable def aBR : Finset α := Cut.filter fun C => ¬ ∃ T C', ATri f Cut Tch C T C'

/-- Cuts which are not the right vertex of a triangle. -/
noncomputable def aBL : Finset α := Cut.filter fun C' => ¬ ∃ C T, ATri f Cut Tch C T C'

/-- Touches which are not the middle vertex of a triangle. -/
noncomputable def aBT : Finset α := Tch.filter fun T => ¬ ∃ C C', ATri f Cut Tch C T C'

/-- Touches whose last cut to the left is `C`. -/
noncomputable def aE (C : α) : Finset α :=
  Tch.filter fun T => f C < f T ∧ ∀ C'' ∈ Cut, ¬ (f C < f C'' ∧ f C'' < f T)

variable {f Cut Tch}

lemma aE_disj (hinjC : ∀ C ∈ Cut, ∀ C' ∈ Cut, f C = f C' → C = C') {C C' : α} (hC : C ∈ Cut)
    (hC' : C' ∈ Cut) (hne : C ≠ C') : Disjoint (aE f Cut Tch C) (aE f Cut Tch C') := by
  rw [Finset.disjoint_left]
  intro T hT hT'
  simp only [aE, Finset.mem_filter] at hT hT'
  rcases lt_trichotomy (f C) (f C') with h | h | h
  · exact hT.2.2 C' hC' ⟨h, hT'.2.1⟩
  · exact hne (hinjC C hC C' hC' h)
  · exact hT'.2.2 C hC ⟨h, hT.2.1⟩

lemma tch_decomp (f : α → ℝ) (Cut Tch : Finset α) :
    Tch = aTL f Cut Tch ∪ Cut.biUnion (aE f Cut Tch) := by
  ext T
  simp only [Finset.mem_union, Finset.mem_biUnion, aTL, aE, Finset.mem_filter]
  constructor
  · intro hT
    by_cases h : ∀ C ∈ Cut, ¬ f C < f T
    · exact Or.inl ⟨hT, h⟩
    · right
      push Not at h
      obtain ⟨C0, hC0, hC0T⟩ := h
      obtain ⟨C, hC, hmax⟩ := Finset.exists_max_image (Cut.filter fun C => f C < f T) f
        ⟨C0, Finset.mem_filter.2 ⟨hC0, hC0T⟩⟩
      rw [Finset.mem_filter] at hC
      refine ⟨C, hC.1, hT, hC.2, ?_⟩
      rintro C'' hC'' ⟨h1, h2⟩
      have := hmax C'' (Finset.mem_filter.2 ⟨hC'', h2⟩)
      linarith
  · rintro (h | ⟨C, -, h, -⟩)
    · exact h.1
    · exact h

lemma card_tch (hinjC : ∀ C ∈ Cut, ∀ C' ∈ Cut, f C = f C' → C = C') :
    #Tch = #(aTL f Cut Tch) + ∑ C ∈ Cut, #(aE f Cut Tch C) := by
  have h1 : Disjoint (aTL f Cut Tch) (Cut.biUnion (aE f Cut Tch)) := by
    rw [Finset.disjoint_left]
    intro T hT hT'
    simp only [aTL, aE, Finset.mem_biUnion, Finset.mem_filter] at hT hT'
    obtain ⟨C, hC, -, h, -⟩ := hT'
    exact hT.2 C hC h
  have h2 : #(Cut.biUnion (aE f Cut Tch)) = ∑ C ∈ Cut, #(aE f Cut Tch C) :=
    Finset.card_biUnion (fun C hC C' hC' hne =>
      aE_disj hinjC (Finset.mem_coe.1 hC) (Finset.mem_coe.1 hC') hne)
  have h3 := congrArg Finset.card (tch_decomp f Cut Tch)
  rw [Finset.card_union_of_disjoint h1, h2] at h3
  exact h3

lemma aE_last {Cl : α} (hCl : Cl ∈ Cut) (hmax : ∀ C ∈ Cut, f C ≤ f Cl)
    (hCT : ∀ C ∈ Cut, ∀ T ∈ Tch, f C ≠ f T) : aE f Cut Tch Cl = aTR f Cut Tch := by
  ext T
  simp only [aE, aTR, Finset.mem_filter]
  constructor
  · rintro ⟨hT, h1, -⟩
    refine ⟨hT, fun C hC hlt => ?_⟩
    have := hmax C hC
    linarith
  · rintro ⟨hT, h⟩
    refine ⟨hT, ?_, ?_⟩
    · rcases lt_trichotomy (f Cl) (f T) with h1 | h1 | h1
      · exact h1
      · exact absurd h1 (hCT Cl hCl T hT)
      · exact absurd h1 (h Cl hCl)
    · rintro C hC ⟨h1, -⟩
      have := hmax C hC
      linarith

lemma aE_next (hCT : ∀ C ∈ Cut, ∀ T ∈ Tch, f C ≠ f T)
    (hE2 : ∀ C ∈ Cut, ∀ C' ∈ Cut, f C < f C' → ∃ e, (e ∈ Cut ∨ e ∈ Tch) ∧ f C < f e ∧ f e < f C')
    {C C0 : α} (hC : C ∈ Cut) (hC0 : C0 ∈ Cut) (hlt : f C < f C0) :
    1 ≤ #(aE f Cut Tch C) ∧
      (#(aE f Cut Tch C) = 1 → (∃ T C', ATri f Cut Tch C T C') ∧
        ∀ T ∈ aE f Cut Tch C, ∃ C1 C', ATri f Cut Tch C1 T C') := by
  obtain ⟨Cn, hCn, hmin⟩ := Finset.exists_min_image (Cut.filter fun C' => f C < f C') f
    ⟨C0, Finset.mem_filter.2 ⟨hC0, hlt⟩⟩
  rw [Finset.mem_filter] at hCn
  have hnc : ∀ C'' ∈ Cut, ¬ (f C < f C'' ∧ f C'' < f Cn) := by
    rintro C'' hC'' ⟨h3, h4⟩
    have := hmin C'' (Finset.mem_filter.2 ⟨hC'', h3⟩)
    linarith
  have key : ∀ e, (e ∈ Cut ∨ e ∈ Tch) → f C < f e → f e < f Cn → e ∈ aE f Cut Tch C := by
    intro e he h1 h2
    rcases he with he | he
    · exact absurd ⟨h1, h2⟩ (hnc e he)
    · simp only [aE, Finset.mem_filter]
      refine ⟨he, h1, ?_⟩
      rintro C'' hC'' ⟨h3, h4⟩
      exact hnc C'' hC'' ⟨h3, by linarith⟩
  have hlt' : ∀ T ∈ aE f Cut Tch C, f T < f Cn := by
    intro T hT
    simp only [aE, Finset.mem_filter] at hT
    rcases lt_trichotomy (f T) (f Cn) with h | h | h
    · exact h
    · exact absurd h.symm (hCT Cn hCn.1 T hT.1)
    · exact absurd ⟨hCn.2, h⟩ (hT.2.2 Cn hCn.1)
  obtain ⟨e, he, h1, h2⟩ := hE2 C hC Cn hCn.1 hCn.2
  have heE := key e he h1 h2
  refine ⟨Finset.card_pos.2 ⟨e, heE⟩, fun hone => ?_⟩
  obtain ⟨T0, hT0⟩ := Finset.card_eq_one.1 hone
  have hall : ∀ T ∈ aE f Cut Tch C, ATri f Cut Tch C T Cn := by
    intro T hT
    have hT' := hT
    simp only [aE, Finset.mem_filter] at hT'
    refine ⟨hC, hT'.1, hCn.1, hT'.2.1, hlt' T hT, ?_⟩
    intro e' he' h1' h2'
    have h5 := key e' he' h1' h2'
    rw [hT0, Finset.mem_singleton] at h5 hT
    rw [h5, hT]
  exact ⟨⟨e, Cn, hall e heE⟩, fun T hT => ⟨C, Cn, hall T hT⟩⟩

lemma abs_count (hinjC : ∀ C ∈ Cut, ∀ C' ∈ Cut, f C = f C' → C = C')
    (hCT : ∀ C ∈ Cut, ∀ T ∈ Tch, f C ≠ f T)
    (hE2 : ∀ C ∈ Cut, ∀ C' ∈ Cut, f C < f C' → ∃ e, (e ∈ Cut ∨ e ∈ Tch) ∧ f C < f e ∧ f e < f C')
    (hne : Cut.Nonempty) :
    #(aBR f Cut Tch) + #(aTL f Cut Tch) + #(aTR f Cut Tch) + #Cut ≤ 2 + #Tch ∧
      #(aBT f Cut Tch) + #(aTL f Cut Tch) + #(aTR f Cut Tch) + 2 * #Cut ≤ 2 + 2 * #Tch := by
  obtain ⟨Cl, hCl, hmax⟩ := Finset.exists_max_image Cut f hne
  have hlast := aE_last hCl hmax hCT
  have hcard := card_tch (Tch := Tch) hinjC
  rw [← Finset.add_sum_erase Cut _ hCl, hlast] at hcard
  have hnext : ∀ C ∈ Cut.erase Cl, 1 ≤ #(aE f Cut Tch C) ∧
      (#(aE f Cut Tch C) = 1 → (∃ T C', ATri f Cut Tch C T C') ∧
        ∀ T ∈ aE f Cut Tch C, ∃ C1 C', ATri f Cut Tch C1 T C') := by
    intro C hC
    rw [Finset.mem_erase] at hC
    have hle := hmax C hC.2
    have hlt : f C < f Cl := lt_of_le_of_ne hle (fun h => hC.1 (hinjC C hC.2 Cl hCl h))
    exact aE_next hCT hE2 hC.2 hCl hlt
  have hm : #(Cut.erase Cl) + 1 = #Cut := Finset.card_erase_add_one hCl
  constructor
  · have h1 : #(aBR f Cut Tch) ≤
        1 + #((Cut.erase Cl).filter fun C => ¬ ∃ T C', ATri f Cut Tch C T C') := by
      have hsub : aBR f Cut Tch ⊆
          insert Cl ((Cut.erase Cl).filter fun C => ¬ ∃ T C', ATri f Cut Tch C T C') := by
        intro C hC
        simp only [aBR, Finset.mem_filter] at hC
        simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_erase]
        by_cases h : C = Cl
        · exact Or.inl h
        · exact Or.inr ⟨⟨h, hC.1⟩, hC.2⟩
      have h2 := Finset.card_le_card hsub
      have h3 := Finset.card_insert_le Cl
        ((Cut.erase Cl).filter fun C => ¬ ∃ T C', ATri f Cut Tch C T C')
      omega
    have h2 : #((Cut.erase Cl).filter fun C => ¬ ∃ T C', ATri f Cut Tch C T C') +
        #(Cut.erase Cl) ≤ ∑ C ∈ Cut.erase Cl, #(aE f Cut Tch C) := by
      rw [Finset.card_filter, Finset.card_eq_sum_ones (Cut.erase Cl), ← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro C hC
      obtain ⟨h3, h4⟩ := hnext C hC
      by_cases h : ∃ T C', ATri f Cut Tch C T C'
      · rw [if_neg (not_not.2 h)]
        omega
      · rw [if_pos h]
        by_contra hcon
        have h5 : #(aE f Cut Tch C) = 1 := by omega
        exact h (h4 h5).1
    omega
  · have hsub : aBT f Cut Tch ⊆ (aTL f Cut Tch ∪ aTR f Cut Tch) ∪
        (Cut.erase Cl).biUnion (fun C => (aE f Cut Tch C).filter
          fun T => ¬ ∃ C1 C', ATri f Cut Tch C1 T C') := by
      intro T hT
      simp only [aBT, Finset.mem_filter] at hT
      have hT1 := hT.1
      rw [tch_decomp f Cut Tch, Finset.mem_union, Finset.mem_biUnion] at hT1
      rcases hT1 with h | ⟨C, hC, hTC⟩
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ h)
      · by_cases h : C = Cl
        · rw [h, hlast] at hTC
          exact Finset.mem_union_left _ (Finset.mem_union_right _ hTC)
        · apply Finset.mem_union_right
          rw [Finset.mem_biUnion]
          exact ⟨C, Finset.mem_erase.2 ⟨h, hC⟩, Finset.mem_filter.2 ⟨hTC, hT.2⟩⟩
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le (aTL f Cut Tch ∪ aTR f Cut Tch)
      ((Cut.erase Cl).biUnion (fun C => (aE f Cut Tch C).filter
          fun T => ¬ ∃ C1 C', ATri f Cut Tch C1 T C'))
    have h3 := Finset.card_union_le (aTL f Cut Tch) (aTR f Cut Tch)
    have h4 : #((Cut.erase Cl).biUnion (fun C => (aE f Cut Tch C).filter
          fun T => ¬ ∃ C1 C', ATri f Cut Tch C1 T C')) ≤
        ∑ C ∈ Cut.erase Cl, #((aE f Cut Tch C).filter
          fun T => ¬ ∃ C1 C', ATri f Cut Tch C1 T C') := Finset.card_biUnion_le
    have h5 : ∑ C ∈ Cut.erase Cl, #((aE f Cut Tch C).filter
          fun T => ¬ ∃ C1 C', ATri f Cut Tch C1 T C') + 2 * #(Cut.erase Cl) ≤
        2 * ∑ C ∈ Cut.erase Cl, #(aE f Cut Tch C) := by
      rw [Finset.card_eq_sum_ones (Cut.erase Cl), Finset.mul_sum, Finset.mul_sum,
        ← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro C hC
      obtain ⟨h6, h7⟩ := hnext C hC
      by_cases h8 : #(aE f Cut Tch C) = 1
      · have h9 : (aE f Cut Tch C).filter
            (fun T => ¬ ∃ C1 C', ATri f Cut Tch C1 T C') = ∅ := by
          rw [Finset.filter_eq_empty_iff]
          intro T hT
          exact not_not.2 ((h7 h8).2 T hT)
        rw [h9, h8]
        simp
      · have h9 := Finset.card_filter_le (aE f Cut Tch C)
          (fun T => ¬ ∃ C1 C', ATri f Cut Tch C1 T C')
        omega
    omega

lemma aTri_neg (f : α → ℝ) (Cut Tch : Finset α) (C T C' : α) :
    ATri (fun a => - f a) Cut Tch C' T C ↔ ATri f Cut Tch C T C' := by
  simp only [ATri]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    exact ⟨h3, h2, h1, by linarith, by linarith,
      fun e he h7 h8 => h6 e he (by linarith) (by linarith)⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    exact ⟨h3, h2, h1, by linarith, by linarith,
      fun e he h7 h8 => h6 e he (by linarith) (by linarith)⟩

lemma abs_count_L (hinjC : ∀ C ∈ Cut, ∀ C' ∈ Cut, f C = f C' → C = C')
    (hCT : ∀ C ∈ Cut, ∀ T ∈ Tch, f C ≠ f T)
    (hE2 : ∀ C ∈ Cut, ∀ C' ∈ Cut, f C < f C' → ∃ e, (e ∈ Cut ∨ e ∈ Tch) ∧ f C < f e ∧ f e < f C')
    (hne : Cut.Nonempty) :
    #(aBL f Cut Tch) + #(aTL f Cut Tch) + #(aTR f Cut Tch) + #Cut ≤ 2 + #Tch := by
  have h := (abs_count (f := fun a => - f a) (Cut := Cut) (Tch := Tch)
    (fun C hC C' hC' h => hinjC C hC C' hC' (neg_injective h))
    (fun C hC T hT h => hCT C hC T hT (neg_injective h))
    (fun C hC C' hC' h => by
      obtain ⟨e, he, h1, h2⟩ := hE2 C' hC' C hC (neg_lt_neg_iff.1 h)
      exact ⟨e, he, neg_lt_neg_iff.2 h2, neg_lt_neg_iff.2 h1⟩) hne).1
  have e1 : aBR (fun a => - f a) Cut Tch = aBL f Cut Tch := by
    simp only [aBR, aBL]
    apply Finset.filter_congr
    intro C _
    constructor
    · rintro h ⟨C1, T, hT⟩
      exact h ⟨T, C1, (aTri_neg f Cut Tch C1 T C).2 hT⟩
    · rintro h ⟨T, C1, hT⟩
      exact h ⟨C1, T, (aTri_neg f Cut Tch C1 T C).1 hT⟩
  have e2 : aTL (fun a => - f a) Cut Tch = aTR f Cut Tch := by
    simp only [aTL, aTR, neg_lt_neg_iff]
  have e3 : aTR (fun a => - f a) Cut Tch = aTL f Cut Tch := by
    simp only [aTL, aTR, neg_lt_neg_iff]
  rw [e1, e2, e3] at h
  omega

end comb

/-! #### Events of one gap -/

section geo

variable {A : Finset (ℝ × ℝ)} {lam : ℝ}

/-- Cuts of gap `g`. -/
noncomputable def cutS (A : Finset (ℝ × ℝ)) (lam : ℝ) (g : ℕ) : Finset (ℝ × ℝ) :=
  (verts A lam).filter fun v => cuts A lam g v

/-- Touches of gap `g`. -/
noncomputable def tchS (A : Finset (ℝ × ℝ)) (lam : ℝ) (g : ℕ) : Finset (ℝ × ℝ) :=
  (verts A lam).filter fun v => tchA A lam g v ∨ tchB A lam g v

lemma mem_cutS {g : ℕ} {v : ℝ × ℝ} :
    v ∈ cutS A lam g ↔ v ∈ verts A lam ∧ cuts A lam g v := by
  simp only [cutS, Finset.mem_filter]

lemma mem_tchS {g : ℕ} {v : ℝ × ℝ} :
    v ∈ tchS A lam g ↔ v ∈ verts A lam ∧ (tchA A lam g v ∨ tchB A lam g v) := by
  simp only [tchS, Finset.mem_filter]

lemma atri_iff (g : ℕ) (C T C' : ℝ × ℝ) :
    ATri Prod.fst (cutS A lam g) (tchS A lam g) C T C' ↔ Tri A lam g C T C' := by
  simp only [ATri, Tri, mem_cutS, mem_tchS]
  constructor
  · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩, ⟨h5, h6⟩, h7, h8, h9⟩
    refine ⟨h1, h3, h5, h2, h6, h4, h7, h8, fun e he hev => h9 e ?_⟩
    rcases hev with h | h
    · exact Or.inl ⟨he, h⟩
    · exact Or.inr ⟨he, h⟩
  · rintro ⟨h1, h3, h5, h2, h6, h4, h7, h8, h9⟩
    refine ⟨⟨h1, h2⟩, ⟨h3, h4⟩, ⟨h5, h6⟩, h7, h8, fun e he => ?_⟩
    rcases he with ⟨he, h⟩ | ⟨he, h⟩
    · exact h9 e he (Or.inl h)
    · exact h9 e he (Or.inr h)

/-- (E1) A cut of gap `g` is the only event of `g` at its abscissa. -/
lemma ev_unique {g : ℕ} {e e' : ℝ × ℝ} (h1 : e.1 = e'.1) (hc : cuts A lam g e)
    (hev : cuts A lam g e' ∨ tchA A lam g e' ∨ tchB A lam g e') : e = e' := by
  simp only [cuts, tchA, tchB] at hc hev
  rcases lt_trichotomy e.2 e'.2 with h | h | h
  · have h2 := bet_mono (A := A) (lam := lam) h1 h
    omega
  · exact Prod.ext h1 h
  · have h2 := bet_mono (A := A) (lam := lam) h1.symm h
    omega

/-- (E2) Between two cuts of gap `g` there is an event of `g`. -/
lemma ev_between (hinj : Set.InjOn (sl lam) A) {g : ℕ} {C C' : ℝ × ℝ} (hC : cuts A lam g C)
    (hC' : cuts A lam g C') (hlt : C.1 < C'.1) :
    ∃ e ∈ verts A lam, (cuts A lam g e ∨ tchA A lam g e ∨ tchB A lam g e) ∧
      C.1 < e.1 ∧ e.1 < C'.1 := by
  by_contra hcon
  have hno : ∀ e ∈ verts A lam, C.1 < e.1 → e.1 < C'.1 →
      ¬ (cuts A lam g e ∨ tchA A lam g e ∨ tchB A lam g e) :=
    fun e he h1 h2 hev => hcon ⟨e, he, hev, h1, h2⟩
  obtain ⟨hb1, hb2⟩ := hC
  obtain ⟨hb3, hb4⟩ := hC'
  obtain ⟨w, hw, hwr⟩ := exists_mem_blk_rp hinj (v := C) (r := g - 1) (by omega) (by omega)
  obtain ⟨u, hu, hur⟩ := exists_mem_blk_rp hinj (v := C) (r := g) (by omega) (by omega)
  have hwA := blk_subset A lam C hw
  have huA := blk_subset A lam C hu
  obtain ⟨-, hw'⟩ := occ_low hinj hlt
    (fun e he h1 h2 => ⟨fun h => hno e he h1 h2 (Or.inl h),
      fun h => hno e he h1 h2 (Or.inr (Or.inr h))⟩) hwA (by omega : rp A lam C.1 w + 1 = g)
  obtain ⟨-, hu'⟩ := occ_high hinj hlt
    (fun e he h1 h2 => ⟨fun h => hno e he h1 h2 (Or.inl h),
      fun h => hno e he h1 h2 (Or.inr (Or.inl h))⟩) huA hur
  have hw2 : w ∈ blk A lam C' := mem_blk_of_rm hwA (by omega) (by omega)
  have hu2 : u ∈ blk A lam C' := mem_blk_of_rm huA (by omega) (by omega)
  have hne : w ≠ u := by
    rintro rfl
    omega
  have hCC := eq_of_mem_blk hinj hw hu hw2 hu2 hne
  rw [hCC] at hlt
  exact lt_irrefl _ hlt

/-- The per-gap count. -/
lemma gap_count (hinj : Set.InjOn (sl lam) A) {g : ℕ} (hne : (cutS A lam g).Nonempty) :
    #(aBR Prod.fst (cutS A lam g) (tchS A lam g)) +
      #(aBL Prod.fst (cutS A lam g) (tchS A lam g)) +
      #(aBT Prod.fst (cutS A lam g) (tchS A lam g)) + 4 * #(cutS A lam g) +
      3 * (#(aTL Prod.fst (cutS A lam g) (tchS A lam g)) +
        #(aTR Prod.fst (cutS A lam g) (tchS A lam g))) ≤ 6 + 4 * #(tchS A lam g) := by
  have hinjC : ∀ C ∈ cutS A lam g, ∀ C' ∈ cutS A lam g, C.1 = C'.1 → C = C' := by
    intro C hC C' hC' h
    exact ev_unique h (mem_cutS.1 hC).2 (Or.inl (mem_cutS.1 hC').2)
  have hCT : ∀ C ∈ cutS A lam g, ∀ T ∈ tchS A lam g, C.1 ≠ T.1 := by
    intro C hC T hT h
    have hc := (mem_cutS.1 hC).2
    have ht := (mem_tchS.1 hT).2
    have hCT := ev_unique h hc (Or.inr ht)
    subst hCT
    simp only [cuts, tchA, tchB] at hc ht
    omega
  have hE2 : ∀ C ∈ cutS A lam g, ∀ C' ∈ cutS A lam g, C.1 < C'.1 →
      ∃ e, (e ∈ cutS A lam g ∨ e ∈ tchS A lam g) ∧ C.1 < e.1 ∧ e.1 < C'.1 := by
    intro C hC C' hC' h
    obtain ⟨e, he, hev, h1, h2⟩ := ev_between hinj (mem_cutS.1 hC).2 (mem_cutS.1 hC').2 h
    refine ⟨e, ?_, h1, h2⟩
    rw [mem_cutS, mem_tchS]
    rcases hev with h | h
    · exact Or.inl ⟨he, h⟩
    · exact Or.inr ⟨he, h⟩
  have h1 := abs_count (f := Prod.fst) hinjC hCT hE2 hne
  have h2 := abs_count_L (f := Prod.fst) hinjC hCT hE2 hne
  omega

/-! #### The far left and the far right -/

/-- An abscissa to the right of all vertices; its negative is to the left of all vertices. -/
noncomputable def xR (A : Finset (ℝ × ℝ)) (lam : ℝ) : ℝ := ∑ e ∈ verts A lam, |e.1| + 1

lemma xR_pos (A : Finset (ℝ × ℝ)) (lam : ℝ) : 0 < xR A lam := by
  have h : 0 ≤ ∑ e ∈ verts A lam, |e.1| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  unfold xR
  linarith

lemma lt_xR {e : ℝ × ℝ} (he : e ∈ verts A lam) : e.1 < xR A lam ∧ - xR A lam < e.1 := by
  have h1 : |e.1| ≤ ∑ e ∈ verts A lam, |e.1| :=
    Finset.single_le_sum (f := fun e : ℝ × ℝ => |e.1|) (fun i _ => abs_nonneg _) he
  have h2 := le_abs_self e.1
  have h3 := neg_abs_le e.1
  unfold xR
  constructor <;> linarith

lemma cx_bd (hinj : Set.InjOn (sl lam) A) {P Q : ℝ × ℝ} (hP : P ∈ A) (hQ : Q ∈ A)
    (hPQ : P ≠ Q) : - xR A lam < cx lam P Q ∧ cx lam P Q < xR A lam := by
  have h := lt_xR (vertex_of_pair hinj hP hQ hPQ).1
  exact ⟨h.2, h.1⟩

lemma rp_left (hinj : Set.InjOn (sl lam) A) {P : ℝ × ℝ} (hP : P ∈ A) :
    rp A lam (- xR A lam) P = #(A.filter fun Q => sl lam P < sl lam Q) := by
  unfold rp
  congr 1
  apply Finset.filter_congr
  intro Q hQ
  by_cases hPQ : P = Q
  · subst hPQ
    simp
  · have hb := cx_bd hinj hP hQ hPQ
    have hsl : sl lam P ≠ sl lam Q := fun h => hPQ (hinj hP hQ h)
    rcases lt_or_gt_of_ne hsl with h | h
    · rw [rp_mem_of_gt h]
      exact ⟨fun _ => h, fun _ => hb.1⟩
    · rw [rp_mem_of_lt h]
      constructor
      · intro h'
        linarith
      · intro h'
        linarith

lemma rm_right (hinj : Set.InjOn (sl lam) A) {P : ℝ × ℝ} (hP : P ∈ A) :
    rm A lam (xR A lam) P = #(A.filter fun Q => sl lam Q < sl lam P) := by
  unfold rm
  congr 1
  apply Finset.filter_congr
  intro Q hQ
  by_cases hPQ : P = Q
  · subst hPQ
    simp
  · have hb := cx_bd hinj hP hQ hPQ
    have hsl : sl lam P ≠ sl lam Q := fun h => hPQ (hinj hP hQ h)
    rcases lt_or_gt_of_ne hsl with h | h
    · rw [rm_mem_of_gt h]
      constructor
      · intro h'
        linarith
      · intro h'
        linarith
    · rw [rm_mem_of_lt h]
      exact ⟨fun _ => h, fun _ => hb.2⟩

lemma rp_left_add_rm_right (hinj : Set.InjOn (sl lam) A) {P : ℝ × ℝ} (hP : P ∈ A) :
    rp A lam (- xR A lam) P + rm A lam (xR A lam) P + 1 = #A := by
  rw [rp_left hinj hP, rm_right hinj hP]
  have hd : Disjoint (A.filter fun Q => sl lam P < sl lam Q)
      (A.filter fun Q => sl lam Q < sl lam P) := by
    rw [Finset.disjoint_left]
    intro Q h1 h2
    rw [Finset.mem_filter] at h1 h2
    linarith [h1.2, h2.2]
  have hu : (A.filter fun Q => sl lam P < sl lam Q) ∪ (A.filter fun Q => sl lam Q < sl lam P) =
      A.erase P := by
    ext Q
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro (⟨hQ, h⟩ | ⟨hQ, h⟩)
      · exact ⟨fun hQP => by rw [hQP] at h; exact lt_irrefl _ h, hQ⟩
      · exact ⟨fun hQP => by rw [hQP] at h; exact lt_irrefl _ h, hQ⟩
    · rintro ⟨hne, hQ⟩
      have hsl : sl lam P ≠ sl lam Q := fun h => hne (hinj hQ hP h.symm)
      rcases lt_or_gt_of_ne hsl with h | h
      · exact Or.inl ⟨hQ, h⟩
      · exact Or.inr ⟨hQ, h⟩
  have h1 := Finset.card_union_of_disjoint hd
  rw [hu, Finset.card_erase_of_mem hP] at h1
  have h2 := Finset.card_pos.2 ⟨P, hP⟩
  omega

/-- Following the dual line of `P` from rank at least `g` down to rank below `g`, one finds
a vertex cutting gap `g`. -/
lemma walk (hinj : Set.InjOn (sl lam) A) {P : ℝ × ℝ} (hP : P ∈ A) {x x' : ℝ} {g : ℕ}
    (hxx : x < x') (h1 : g ≤ rp A lam x P) (h2 : rm A lam x' P < g) :
    ∃ e ∈ verts A lam, cuts A lam g e := by
  set S : Finset ℝ := ((A.erase P).image (cx lam P)).filter (fun y => x < y ∧ y < x') with hS
  have hSmem : ∀ y, y ∈ S ↔ ∃ Q ∈ A, Q ≠ P ∧ cx lam P Q = y ∧ x < y ∧ y < x' := by
    intro y
    simp only [hS, Finset.mem_filter, Finset.mem_image, Finset.mem_erase]
    constructor
    · rintro ⟨⟨Q, ⟨hne, hQ⟩, rfl⟩, h⟩
      exact ⟨Q, hQ, hne, rfl, h⟩
    · rintro ⟨Q, hQ, hne, rfl, h⟩
      exact ⟨⟨Q, ⟨hne, hQ⟩, rfl⟩, h⟩
  have hstep : ∀ a b : ℝ, x ≤ a → b ≤ x' → a < b → (∀ y ∈ S, ¬ (a < y ∧ y < b)) →
      rp A lam a P = rm A lam b P := by
    intro a b ha hb hab hno
    apply rp_eq_rm hinj hP hab
    rintro Q hQ hne ⟨h3, h4⟩
    exact hno (cx lam P Q) ((hSmem _).2 ⟨Q, hQ, hne, rfl, by linarith, by linarith⟩) ⟨h3, h4⟩
  have hSne : S.Nonempty := by
    by_contra hcon
    rw [Finset.not_nonempty_iff_eq_empty] at hcon
    have h3 := hstep x x' le_rfl le_rfl hxx (by rw [hcon]; simp)
    omega
  have hS'ne : (S.filter (fun y => g ≤ rm A lam y P)).Nonempty := by
    obtain ⟨y, hy, hmin⟩ := Finset.exists_min_image S id hSne
    refine ⟨y, ?_⟩
    obtain ⟨Q, hQ, hne, hcx, hxy, hyx'⟩ := (hSmem y).1 hy
    have h3 := hstep x y le_rfl hyx'.le hxy (fun z hz hz2 => by
      have h4 := hmin z hz
      simp only [id] at h4
      linarith [hz2.2])
    rw [Finset.mem_filter]
    exact ⟨hy, by omega⟩
  obtain ⟨y, hy, hmax⟩ := Finset.exists_max_image _ id hS'ne
  rw [Finset.mem_filter] at hy
  obtain ⟨hyS, hyg⟩ := hy
  obtain ⟨Q, hQ, hne, hcx, hxy, hyx'⟩ := (hSmem y).1 hyS
  have hrp : rp A lam y P < g := by
    by_contra hcon
    by_cases hemp : (S.filter (fun z => y < z)).Nonempty
    · obtain ⟨z, hz, hmin⟩ := Finset.exists_min_image _ id hemp
      rw [Finset.mem_filter] at hz
      obtain ⟨Q', hQ', hne', hcx', hxz, hzx'⟩ := (hSmem z).1 hz.1
      have h3 := hstep y z hxy.le hzx'.le hz.2 (fun t ht ht2 => by
        have h4 := hmin t (Finset.mem_filter.2 ⟨ht, ht2.1⟩)
        simp only [id] at h4
        linarith [ht2.2])
      have h5 := hmax z (Finset.mem_filter.2 ⟨hz.1, by omega⟩)
      simp only [id] at h5
      linarith [hz.2]
    · rw [Finset.not_nonempty_iff_eq_empty] at hemp
      have h3 := hstep y x' hxy.le le_rfl hyx' (fun t ht ht2 => by
        have h4 : t ∈ S.filter (fun z => y < z) := Finset.mem_filter.2 ⟨ht, ht2.1⟩
        rw [hemp] at h4
        simp at h4)
      omega
  subst hcx
  have hv := vertex_of_pair hinj hP hQ hne.symm
  have hb1 : bet A lam (cx lam P Q, ht lam P (cx lam P Q)) ≤ rp A lam (cx lam P Q) P :=
    bet_le_rp hv.2.1
  have hb2 : rm A lam (cx lam P Q) P < bet A lam (cx lam P Q, ht lam P (cx lam P Q)) +
      #(blk A lam (cx lam P Q, ht lam P (cx lam P Q))) := rm_lt_bet_add hv.2.1
  refine ⟨_, hv.1, ?_⟩
  unfold cuts
  constructor <;> omega

/-- (E3) Every inner gap has a cut. -/
lemma exists_cut (hinj : Set.InjOn (sl lam) A) {g : ℕ} (hg1 : 1 ≤ g) (hg2 : g < #A) :
    (cutS A lam g).Nonempty := by
  have hAne : A.Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨P, hP, hmin⟩ := Finset.exists_min_image A (sl lam) hAne
  have h1 : rm A lam (xR A lam) P = 0 := by
    rw [rm_right hinj hP, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro Q hQ
    exact not_lt.2 (hmin Q hQ)
  have h2 := rp_left_add_rm_right hinj hP
  have hx : - xR A lam < xR A lam := by
    have := xR_pos A lam
    linarith
  obtain ⟨e, he, hc⟩ := walk hinj hP (g := g) hx (by omega) (by omega)
  exact ⟨e, mem_cutS.2 ⟨he, hc⟩⟩

/-- (G) Gluing the two ends. -/
lemma glue (hinj : Set.InjOn (sl lam) A) (hk : ∀ v : ℝ × ℝ, #(blk A lam v) ≤ 3) (hA : 4 ≤ #A)
    {g : ℕ} (hg1 : 1 ≤ g) (hg2 : g < #A) :
    (∃ T ∈ tchS A lam g, ∀ C ∈ cutS A lam g, ¬ T.1 < C.1) ∨
      (∃ T ∈ tchS A lam (#A - g), ∀ C ∈ cutS A lam (#A - g), ¬ C.1 < T.1) := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hc1, hc2⟩ := hcon
  have hR : ∀ T ∈ tchS A lam g, ∃ C ∈ cutS A lam g, T.1 < C.1 := by
    intro T hT
    by_contra h
    exact hc1 ⟨T, hT, fun C hC hlt => h ⟨C, hC, hlt⟩⟩
  have hL : ∀ T ∈ tchS A lam (#A - g), ∃ C ∈ cutS A lam (#A - g), C.1 < T.1 := by
    intro T hT
    by_contra h
    exact hc2 ⟨T, hT, fun C hC hlt => h ⟨C, hC, hlt⟩⟩
  obtain ⟨L, hLc, hLmax⟩ := Finset.exists_max_image (cutS A lam g) Prod.fst
    (exists_cut hinj hg1 hg2)
  obtain ⟨L', hL'c, hL'min⟩ := Finset.exists_min_image (cutS A lam (#A - g)) Prod.fst
    (exists_cut hinj (by omega) (by omega))
  rw [mem_cutS] at hLc hL'c
  obtain ⟨hLV, hb1, hb2⟩ := hLc
  obtain ⟨hL'V, hb3, hb4⟩ := hL'c
  have hnoR : ∀ e ∈ verts A lam, L.1 < e.1 → e.1 < xR A lam →
      ¬ cuts A lam g e ∧ ¬ tchA A lam g e ∧ ¬ tchB A lam g e := by
    intro e he h3 _
    have hc : ¬ cuts A lam g e := fun h => by
      have h4 := hLmax e (mem_cutS.2 ⟨he, h⟩)
      linarith
    have ht : ¬ (tchA A lam g e ∨ tchB A lam g e) := fun h => by
      obtain ⟨C, hC, hlt⟩ := hR e (mem_tchS.2 ⟨he, h⟩)
      have h4 := hLmax C hC
      linarith
    exact ⟨hc, fun h => ht (Or.inl h), fun h => ht (Or.inr h)⟩
  have hnoL : ∀ e ∈ verts A lam, - xR A lam < e.1 → e.1 < L'.1 →
      ¬ cuts A lam (#A - g) e ∧ ¬ tchA A lam (#A - g) e ∧ ¬ tchB A lam (#A - g) e := by
    intro e he _ h3
    have hc : ¬ cuts A lam (#A - g) e := fun h => by
      have h4 := hL'min e (mem_cutS.2 ⟨he, h⟩)
      linarith
    have ht : ¬ (tchA A lam (#A - g) e ∨ tchB A lam (#A - g) e) := fun h => by
      obtain ⟨C, hC, hlt⟩ := hL e (mem_tchS.2 ⟨he, h⟩)
      have h4 := hL'min C hC
      linarith
    exact ⟨hc, fun h => ht (Or.inl h), fun h => ht (Or.inr h)⟩
  obtain ⟨w, hw, hwr⟩ := exists_mem_blk_rp hinj (v := L) (r := g - 1) (by omega) (by omega)
  obtain ⟨u, hu, hur⟩ := exists_mem_blk_rp hinj (v := L) (r := g) (by omega) (by omega)
  have hwA := blk_subset A lam L hw
  have huA := blk_subset A lam L hu
  have hLx := (lt_xR hLV).1
  have hL'x := (lt_xR hL'V).2
  obtain ⟨hwR, hw1⟩ := occ_low hinj hLx
    (fun e he h1 h2 => ⟨(hnoR e he h1 h2).1, (hnoR e he h1 h2).2.2⟩) hwA
    (by omega : rp A lam L.1 w + 1 = g)
  obtain ⟨-, hu1⟩ := occ_high hinj hLx
    (fun e he h1 h2 => ⟨(hnoR e he h1 h2).1, (hnoR e he h1 h2).2.1⟩) huA hur
  have hsw := rp_left_add_rm_right hinj hwA
  have hsu := rp_left_add_rm_right hinj huA
  obtain ⟨-, hu2⟩ := occ_low hinj hL'x
    (fun e he h1 h2 => ⟨(hnoL e he h1 h2).1, (hnoL e he h1 h2).2.2⟩) huA
    (by omega : rp A lam (- xR A lam) u + 1 = #A - g)
  obtain ⟨hwL, hw2⟩ := occ_high hinj hL'x
    (fun e he h1 h2 => ⟨(hnoL e he h1 h2).1, (hnoL e he h1 h2).2.1⟩) hwA
    (by omega : rp A lam (- xR A lam) w = #A - g)
  have hw3 : w ∈ blk A lam L' := mem_blk_of_rm hwA (by omega) (by omega)
  have hu3 : u ∈ blk A lam L' := mem_blk_of_rm huA (by omega) (by omega)
  have hne : w ≠ u := by
    rintro rfl
    omega
  have hLL := eq_of_mem_blk hinj hw hu hw3 hu3 hne
  subst hLL
  have hsub : A ⊆ blk A lam L := by
    intro Q hQ
    by_cases hQw : Q = w
    · rw [hQw]
      exact hw
    · have hb := cx_bd hinj hwA hQ (Ne.symm hQw)
      have hcx : L.1 = cx lam w Q := by
        rcases lt_trichotomy (cx lam w Q) L.1 with h | h | h
        · exact absurd ⟨hb.1, h⟩ (hwL Q hQ hQw)
        · exact h.symm
        · exact absurd ⟨h, hb.2⟩ (hwR Q hQ hQw)
      have hht := (ht_eq_iff hinj hwA hQ (Ne.symm hQw) L.1).2 hcx
      rw [mem_blk]
      exact ⟨hQ, by rw [← hht]; exact (mem_blk.1 hw).2⟩
  have h5 := Finset.card_le_card hsub
  have h6 := hk L
  omega

/-! #### Global sums -/

lemma sum_cut (hinj : Set.InjOn (sl lam) A) (hk : ∀ v : ℝ × ℝ, #(blk A lam v) ≤ 3) :
    ∑ g ∈ Finset.Ico 1 #A, #(cutS A lam g) =
      #((verts A lam).filter fun v => #(blk A lam v) = 2) +
        2 * #((verts A lam).filter fun v => #(blk A lam v) = 3) := by
  simp only [cutS, Finset.card_filter]
  rw [Finset.sum_comm, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v hv
  rw [← Finset.card_filter]
  have h3 : (Finset.Ico 1 #A).filter (fun g => cuts A lam g v) =
      Finset.Ioo (bet A lam v) (bet A lam v + #(blk A lam v)) := by
    ext g
    have h := bet_add_card_le A lam v
    rw [Finset.mem_filter, Finset.mem_Ico, Finset.mem_Ioo]
    unfold cuts
    omega
  rw [h3, Nat.card_Ioo]
  have h4 := two_le_card_blk hinj hv
  have h5 := hk v
  split_ifs <;> omega

lemma sum_tch (hinj : Set.InjOn (sl lam) A) (hk : ∀ v : ℝ × ℝ, #(blk A lam v) ≤ 3) :
    ∑ g ∈ Finset.range (#A + 1), #(tchS A lam g) =
      2 * #((verts A lam).filter fun v => #(blk A lam v) = 2) +
        2 * #((verts A lam).filter fun v => #(blk A lam v) = 3) := by
  simp only [tchS, Finset.card_filter]
  rw [Finset.sum_comm, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v hv
  rw [← Finset.card_filter]
  have h4 := two_le_card_blk hinj hv
  have h5 := hk v
  have h6 := bet_add_card_le A lam v
  have h3 : (Finset.range (#A + 1)).filter (fun g => tchA A lam g v ∨ tchB A lam g v) =
      ({bet A lam v, bet A lam v + #(blk A lam v)} : Finset ℕ) := by
    ext g
    rw [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
    unfold tchA tchB
    omega
  rw [h3, Finset.card_pair (by omega)]
  split_ifs <;> omega

/-! #### Bad events -/

/-- Events of gap `g` missing one of their triangles. -/
noncomputable def badS (A : Finset (ℝ × ℝ)) (lam : ℝ) (g : ℕ) : Finset (ℝ × ℝ) :=
  aBR Prod.fst (cutS A lam g) (tchS A lam g) ∪ aBL Prod.fst (cutS A lam g) (tchS A lam g) ∪
    aBT Prod.fst (cutS A lam g) (tchS A lam g)

lemma bad_edge {g : ℕ} (h : cutS A lam g = ∅) : #(badS A lam g) ≤ #(tchS A lam g) := by
  have h1 : aBR Prod.fst (cutS A lam g) (tchS A lam g) = ∅ := by
    rw [aBR, h, Finset.filter_empty]
  have h2 : aBL Prod.fst (cutS A lam g) (tchS A lam g) = ∅ := by
    rw [aBL, h, Finset.filter_empty]
  rw [badS, h1, h2, Finset.empty_union, Finset.empty_union]
  exact Finset.card_le_card (Finset.filter_subset _ _)

lemma bad_sum (hinj : Set.InjOn (sl lam) A) (hk : ∀ v : ℝ × ℝ, #(blk A lam v) ≤ 3)
    (hA : 4 ≤ #A) :
    ∑ g ∈ Finset.range (#A + 1), #(badS A lam g) + 3 ≤
      4 * #((verts A lam).filter fun v => #(blk A lam v) = 2) + 3 * #A := by
  have hsplit : ∀ F : ℕ → ℕ, ∑ g ∈ Finset.range (#A + 1), F g =
      F 0 + ∑ g ∈ Finset.Ico 1 #A, F g + F #A := by
    intro F
    rw [Finset.sum_range_succ, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)]
  have hc0 : cutS A lam 0 = ∅ := by
    rw [cutS, Finset.filter_eq_empty_iff]
    intro v _ h
    unfold cuts at h
    omega
  have hcn : cutS A lam #A = ∅ := by
    rw [cutS, Finset.filter_eq_empty_iff]
    intro v _ h
    have h1 := bet_add_card_le A lam v
    unfold cuts at h
    omega
  have h0 := bad_edge hc0
  have hn := bad_edge hcn
  have hgap : ∀ g ∈ Finset.Ico 1 #A, #(badS A lam g) + 4 * #(cutS A lam g) +
      3 * (#(aTL Prod.fst (cutS A lam g) (tchS A lam g)) +
        #(aTR Prod.fst (cutS A lam g) (tchS A lam g))) ≤ 6 + 4 * #(tchS A lam g) := by
    intro g hg
    rw [Finset.mem_Ico] at hg
    have h1 := gap_count hinj (exists_cut hinj hg.1 hg.2)
    have h2 := Finset.card_union_le (aBR Prod.fst (cutS A lam g) (tchS A lam g) ∪
      aBL Prod.fst (cutS A lam g) (tchS A lam g)) (aBT Prod.fst (cutS A lam g) (tchS A lam g))
    have h3 := Finset.card_union_le (aBR Prod.fst (cutS A lam g) (tchS A lam g))
      (aBL Prod.fst (cutS A lam g) (tchS A lam g))
    rw [badS]
    omega
  have hglue : ∀ g ∈ Finset.Ico 1 #A, 1 ≤ #(aTR Prod.fst (cutS A lam g) (tchS A lam g)) +
      #(aTL Prod.fst (cutS A lam (#A - g)) (tchS A lam (#A - g))) := by
    intro g hg
    rw [Finset.mem_Ico] at hg
    rcases glue hinj hk hA hg.1 hg.2 with ⟨T, hT, h⟩ | ⟨T, hT, h⟩
    · have h1 : 0 < #(aTR Prod.fst (cutS A lam g) (tchS A lam g)) :=
        Finset.card_pos.2 ⟨T, Finset.mem_filter.2 ⟨hT, h⟩⟩
      omega
    · have h1 : 0 < #(aTL Prod.fst (cutS A lam (#A - g)) (tchS A lam (#A - g))) :=
        Finset.card_pos.2 ⟨T, Finset.mem_filter.2 ⟨hT, h⟩⟩
      omega
  have hsum := Finset.sum_le_sum hgap
  have hsum2 := Finset.sum_le_sum hglue
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Nat.card_Ico,
    smul_eq_mul] at hsum hsum2
  have href : ∑ j ∈ Finset.Ico 1 #A, #(aTL Prod.fst (cutS A lam (#A - j)) (tchS A lam (#A - j))) =
      ∑ j ∈ Finset.Ico 1 #A, #(aTL Prod.fst (cutS A lam j) (tchS A lam j)) := by
    have h := Finset.sum_Ico_reflect
      (fun g => #(aTL Prod.fst (cutS A lam g) (tchS A lam g))) 1 (m := #A) (n := #A) (by omega)
    have e1 : #A + 1 - #A = 1 := by omega
    have e2 : #A + 1 - 1 = #A := by omega
    rw [e1, e2] at h
    exact h
  have hc := sum_cut hinj hk
  have ht := sum_tch hinj hk
  rw [hsplit] at ht
  rw [hsplit]
  omega

/-! #### Neighbours -/

/-- `v` and `D` are consecutive vertices on some dual line. -/
def Nb (A : Finset (ℝ × ℝ)) (lam : ℝ) (v D : ℝ × ℝ) : Prop :=
  ∃ P, Adj A lam P v D ∨ Adj A lam P D v

lemma nb_count (hinj : Set.InjOn (sl lam) A) :
    #((verts A lam).filter fun v =>
        ∃ D ∈ (verts A lam).filter (fun w => #(blk A lam w) = 2), Nb A lam v D) ≤
      4 * #((verts A lam).filter fun w => #(blk A lam w) = 2) := by
  have hsub : ((verts A lam).filter fun v =>
        ∃ D ∈ (verts A lam).filter (fun w => #(blk A lam w) = 2), Nb A lam v D) ⊆
      ((verts A lam).filter (fun w => #(blk A lam w) = 2)).biUnion
        (fun D => (blk A lam D).biUnion (fun P =>
          ((verts A lam).filter fun v => Adj A lam P v D) ∪
            ((verts A lam).filter fun v => Adj A lam P D v))) := by
    intro v hv
    rw [Finset.mem_filter] at hv
    obtain ⟨hvV, D, hD, P, hP⟩ := hv
    rw [Finset.mem_biUnion]
    refine ⟨D, hD, ?_⟩
    rw [Finset.mem_biUnion]
    rcases hP with hP | hP
    · exact ⟨P, hP.2.1, Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hvV, hP⟩)⟩
    · exact ⟨P, hP.1, Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hvV, hP⟩)⟩
  refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
  have hD : ∀ D ∈ (verts A lam).filter (fun w => #(blk A lam w) = 2),
      #((blk A lam D).biUnion (fun P =>
          ((verts A lam).filter fun v => Adj A lam P v D) ∪
            ((verts A lam).filter fun v => Adj A lam P D v))) ≤ 4 := by
    intro D hD
    refine Finset.card_biUnion_le.trans ?_
    have hP : ∀ P ∈ blk A lam D, #(((verts A lam).filter fun v => Adj A lam P v D) ∪
            ((verts A lam).filter fun v => Adj A lam P D v)) ≤ 2 := by
      intro P _
      refine (Finset.card_union_le _ _).trans ?_
      have h1 : #((verts A lam).filter fun v => Adj A lam P v D) ≤ 1 := by
        rw [Finset.card_le_one]
        intro a ha b hb
        rw [Finset.mem_filter] at ha hb
        exact adj_left_unique hinj ha.2 hb.2 ha.1 hb.1
      have h2 : #((verts A lam).filter fun v => Adj A lam P D v) ≤ 1 := by
        rw [Finset.card_le_one]
        intro a ha b hb
        rw [Finset.mem_filter] at ha hb
        exact adj_right_unique hinj ha.2 hb.2 ha.1 hb.1
      omega
    refine (Finset.sum_le_sum hP).trans ?_
    rw [Finset.sum_const, smul_eq_mul]
    have h3 : #(blk A lam D) = 2 := (Finset.mem_filter.1 hD).2
    omega
  refine (Finset.sum_le_sum hD).trans ?_
  rw [Finset.sum_const, smul_eq_mul]
  omega

lemma tri_nb (hinj : Set.InjOn (sl lam) A) {g : ℕ} {C T C' : ℝ × ℝ}
    (h : Tri A lam g C T C') :
    Nb A lam C T ∧ Nb A lam T C ∧ Nb A lam T C' ∧ Nb A lam C' T ∧ Nb A lam C C' ∧
      Nb A lam C' C := by
  obtain ⟨a, b, c, ha, hb, hc, -⟩ := tri_face hinj h
  exact ⟨⟨a, Or.inl ha⟩, ⟨a, Or.inr ha⟩, ⟨b, Or.inl hb⟩, ⟨b, Or.inr hb⟩, ⟨c, Or.inl hc⟩,
    ⟨c, Or.inr hc⟩⟩

lemma mem_V2 (hinj : Set.InjOn (sl lam) A) (hk : ∀ v : ℝ × ℝ, #(blk A lam v) ≤ 3)
    {D : ℝ × ℝ} (hD : D ∈ verts A lam) (h3 : ¬ #(blk A lam D) = 3) :
    D ∈ (verts A lam).filter (fun w => #(blk A lam w) = 2) := by
  have h1 := two_le_card_blk hinj hD
  have h2 := hk D
  exact Finset.mem_filter.2 ⟨hD, by omega⟩

lemma mem_badS {g : ℕ} {v : ℝ × ℝ} : v ∈ badS A lam g ↔
    v ∈ aBR Prod.fst (cutS A lam g) (tchS A lam g) ∨
      v ∈ aBL Prod.fst (cutS A lam g) (tchS A lam g) ∨
      v ∈ aBT Prod.fst (cutS A lam g) (tchS A lam g) := by
  rw [badS, Finset.mem_union, Finset.mem_union, or_assoc]

lemma clauseR (hinj : Set.InjOn (sl lam) A) (hk : ∀ v : ℝ × ℝ, #(blk A lam v) ≤ 3)
    {v : ℝ × ℝ} (hv : v ∈ verts A lam) {g : ℕ} (hc : cuts A lam g v) :
    (∃ T C', Tri A lam g v T C' ∧ #(blk A lam T) = 3 ∧ #(blk A lam C') = 3) ∨
      v ∈ badS A lam g ∨
      (∃ D ∈ (verts A lam).filter (fun w => #(blk A lam w) = 2), Nb A lam v D) := by
  by_cases h : ∃ T C', Tri A lam g v T C'
  · obtain ⟨T, C', hT⟩ := h
    by_cases h3 : #(blk A lam T) = 3 ∧ #(blk A lam C') = 3
    · exact Or.inl ⟨T, C', hT, h3⟩
    · right
      right
      obtain ⟨n1, -, -, -, n5, -⟩ := tri_nb hinj hT
      rw [not_and_or] at h3
      rcases h3 with h3 | h3
      · exact ⟨T, mem_V2 hinj hk hT.2.1 h3, n1⟩
      · exact ⟨C', mem_V2 hinj hk hT.2.2.1 h3, n5⟩
  · right
    left
    rw [mem_badS]
    left
    simp only [aBR, Finset.mem_filter, mem_cutS]
    exact ⟨⟨hv, hc⟩, fun ⟨T, C', hT⟩ => h ⟨T, C', (atri_iff g v T C').1 hT⟩⟩

lemma clauseL (hinj : Set.InjOn (sl lam) A) (hk : ∀ v : ℝ × ℝ, #(blk A lam v) ≤ 3)
    {v : ℝ × ℝ} (hv : v ∈ verts A lam) {g : ℕ} (hc : cuts A lam g v) :
    (∃ C T, Tri A lam g C T v ∧ #(blk A lam C) = 3 ∧ #(blk A lam T) = 3) ∨
      v ∈ badS A lam g ∨
      (∃ D ∈ (verts A lam).filter (fun w => #(blk A lam w) = 2), Nb A lam v D) := by
  by_cases h : ∃ C T, Tri A lam g C T v
  · obtain ⟨C, T, hT⟩ := h
    by_cases h3 : #(blk A lam C) = 3 ∧ #(blk A lam T) = 3
    · exact Or.inl ⟨C, T, hT, h3⟩
    · right
      right
      obtain ⟨-, -, -, n4, -, n6⟩ := tri_nb hinj hT
      rw [not_and_or] at h3
      rcases h3 with h3 | h3
      · exact ⟨C, mem_V2 hinj hk hT.1 h3, n6⟩
      · exact ⟨T, mem_V2 hinj hk hT.2.1 h3, n4⟩
  · right
    left
    rw [mem_badS]
    right
    left
    simp only [aBL, Finset.mem_filter, mem_cutS]
    exact ⟨⟨hv, hc⟩, fun ⟨C, T, hT⟩ => h ⟨C, T, (atri_iff g C T v).1 hT⟩⟩

lemma clauseT (hinj : Set.InjOn (sl lam) A) (hk : ∀ v : ℝ × ℝ, #(blk A lam v) ≤ 3)
    {v : ℝ × ℝ} (hv : v ∈ verts A lam) {g : ℕ} (hc : tchA A lam g v ∨ tchB A lam g v) :
    (∃ C C', Tri A lam g C v C' ∧ #(blk A lam C) = 3 ∧ #(blk A lam C') = 3) ∨
      v ∈ badS A lam g ∨
      (∃ D ∈ (verts A lam).filter (fun w => #(blk A lam w) = 2), Nb A lam v D) := by
  by_cases h : ∃ C C', Tri A lam g C v C'
  · obtain ⟨C, C', hT⟩ := h
    by_cases h3 : #(blk A lam C) = 3 ∧ #(blk A lam C') = 3
    · exact Or.inl ⟨C, C', hT, h3⟩
    · right
      right
      obtain ⟨-, n2, n3, -, -, -⟩ := tri_nb hinj hT
      rw [not_and_or] at h3
      rcases h3 with h3 | h3
      · exact ⟨C, mem_V2 hinj hk hT.1 h3, n2⟩
      · exact ⟨C', mem_V2 hinj hk hT.2.2.1 h3, n3⟩
  · right
    left
    rw [mem_badS]
    right
    right
    simp only [aBT, Finset.mem_filter, mem_tchS]
    exact ⟨⟨hv, hc⟩, fun ⟨C, C', hT⟩ => h ⟨C, C', (atri_iff g C v C').1 hT⟩⟩

end geo

/-- Counting (Euler's formula for the arrangement): a dense arrangement has a good vertex. -/
theorem exists_good (A : Finset (ℝ × ℝ)) (lam : ℝ) (hinj : Set.InjOn (sl lam) A)
    (hk : ∀ v : ℝ × ℝ, #(blk A lam v) ≤ 3) (hA : 10 ≤ #A)
    (hdense : 8 * #((verts A lam).filter fun v => #(blk A lam v) = 2) + 4 * #A ≤
      #((verts A lam).filter fun v => #(blk A lam v) = 3)) :
    ∃ v, Good A lam v := by
  by_contra hno
  have hsub : ((verts A lam).filter fun v => #(blk A lam v) = 3) ⊆
      ((Finset.range (#A + 1)).biUnion (badS A lam)) ∪
        ((verts A lam).filter fun v =>
          ∃ D ∈ (verts A lam).filter (fun w => #(blk A lam w) = 2), Nb A lam v D) := by
    intro v hv
    rw [Finset.mem_filter] at hv
    obtain ⟨hvV, hk3⟩ := hv
    have hle := bet_add_card_le A lam v
    by_cases hN : ∃ D ∈ (verts A lam).filter (fun w => #(blk A lam w) = 2), Nb A lam v D
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hvV, hN⟩)
    · apply Finset.mem_union_left
      by_contra hU
      have hU' : ∀ g, g ≤ #A → v ∉ badS A lam g := by
        intro g hg hmem
        exact hU (Finset.mem_biUnion.2 ⟨g, Finset.mem_range.2 (by omega), hmem⟩)
      apply hno
      refine ⟨v, hvV, hk3, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rcases clauseR hinj hk hvV (g := bet A lam v + 1) (by unfold cuts; omega) with h | h | h
        · exact h
        · exact absurd h (hU' _ (by omega))
        · exact absurd h hN
      · rcases clauseL hinj hk hvV (g := bet A lam v + 1) (by unfold cuts; omega) with h | h | h
        · exact h
        · exact absurd h (hU' _ (by omega))
        · exact absurd h hN
      · rcases clauseR hinj hk hvV (g := bet A lam v + 2) (by unfold cuts; omega) with h | h | h
        · exact h
        · exact absurd h (hU' _ (by omega))
        · exact absurd h hN
      · rcases clauseL hinj hk hvV (g := bet A lam v + 2) (by unfold cuts; omega) with h | h | h
        · exact h
        · exact absurd h (hU' _ (by omega))
        · exact absurd h hN
      · rcases clauseT hinj hk hvV (g := bet A lam v) (Or.inl rfl) with h | h | h
        · exact h
        · exact absurd h (hU' _ (by omega))
        · exact absurd h hN
      · rcases clauseT hinj hk hvV (g := bet A lam v + 3)
          (Or.inr (by unfold tchB; omega)) with h | h | h
        · exact h
        · exact absurd h (hU' _ (by omega))
        · exact absurd h hN
  have h2 := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have h3 : #((Finset.range (#A + 1)).biUnion (badS A lam)) ≤
      ∑ g ∈ Finset.range (#A + 1), #(badS A lam g) := Finset.card_biUnion_le
  have h4 := bad_sum hinj hk (by omega)
  have h5 := nb_count hinj
  omega

-- END COUNT

-- BEGIN LOCAL
section loc

variable {A : Finset (ℝ × ℝ)} {lam : ℝ}

/-- The linear polynomial of the line dual to the dual point `w`. -/
noncomputable def lin (lam : ℝ) (w : ℝ × ℝ) : MvPolynomial (Fin 2) ℝ :=
  MvPolynomial.C w.1 * (MvPolynomial.X 0 + MvPolynomial.C lam * MvPolynomial.X 1) -
    MvPolynomial.X 1 - MvPolynomial.C w.2

lemma eval_lin (lam : ℝ) (w Z : ℝ × ℝ) :
    MvPolynomial.eval ![Z.1, Z.2] (lin lam w) = ht lam Z w.1 - w.2 := by
  simp [lin, ht, sl]
  ring

lemma totalDegree_lin (lam : ℝ) (w : ℝ × ℝ) : (lin lam w).totalDegree ≤ 1 := by
  unfold lin
  refine (MvPolynomial.totalDegree_sub _ _).trans
    (max_le ((MvPolynomial.totalDegree_sub _ _).trans (max_le ?_ ?_)) ?_)
  · refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_C, zero_add]
    refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
    · exact (MvPolynomial.totalDegree_X _).le
    · refine (MvPolynomial.totalDegree_mul _ _).trans ?_
      rw [MvPolynomial.totalDegree_C, zero_add]
      exact (MvPolynomial.totalDegree_X _).le
  · exact (MvPolynomial.totalDegree_X _).le
  · simp

lemma totalDegree_lin3 (lam : ℝ) (a b c : ℝ × ℝ) :
    (lin lam a * lin lam b * lin lam c).totalDegree ≤ 3 := by
  have h1 := MvPolynomial.totalDegree_mul (lin lam a * lin lam b) (lin lam c)
  have h2 := MvPolynomial.totalDegree_mul (lin lam a) (lin lam b)
  have ha := totalDegree_lin lam a
  have hb := totalDegree_lin lam b
  have hc := totalDegree_lin lam c
  omega

/-- A point of the plane whose dual line passes through `w0` and misses three other dual
points. -/
lemma exists_sep (lam : ℝ) (w0 w1 w2 w3 : ℝ × ℝ) (h1 : w1 ≠ w0) (h2 : w2 ≠ w0)
    (h3 : w3 ≠ w0) :
    ∃ Z : ℝ × ℝ, ht lam Z w0.1 = w0.2 ∧ ht lam Z w1.1 ≠ w1.2 ∧ ht lam Z w2.1 ≠ w2.2 ∧
      ht lam Z w3.1 ≠ w3.2 := by
  obtain ⟨σ, hσ⟩ := Infinite.exists_notMem_finset
    ({(w1.2 - w0.2) / (w1.1 - w0.1), (w2.2 - w0.2) / (w2.1 - w0.1),
      (w3.2 - w0.2) / (w3.1 - w0.1)} : Finset ℝ)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hσ
  obtain ⟨g1, g2, g3⟩ := hσ
  have key : ∀ w : ℝ × ℝ, w ≠ w0 → σ ≠ (w.2 - w0.2) / (w.1 - w0.1) →
      ht lam (σ - lam * (σ * w0.1 - w0.2), σ * w0.1 - w0.2) w.1 ≠ w.2 := by
    intro w hw hs he
    have e : σ * (w.1 - w0.1) = w.2 - w0.2 := by
      simp only [ht, sl] at he
      linear_combination he
    by_cases hx : w.1 = w0.1
    · apply hw
      rw [hx, sub_self, mul_zero] at e
      ext
      · exact hx
      · linarith
    · apply hs
      rw [eq_div_iff (sub_ne_zero.2 hx)]
      exact e
  refine ⟨_, ?_, key w1 h1 g1, key w2 h2 g2, key w3 h3 g3⟩
  simp only [ht, sl]
  ring

/-- Two products of three dual lines are linearly independent, as soon as one line of each
product differs from the three lines of the other. -/
lemma pencil_ind (lam : ℝ) (r1 r2 r3 c1 c2 c3 : ℝ × ℝ) (h11 : r1 ≠ c1) (h21 : r2 ≠ c1)
    (h31 : r3 ≠ c1) (h12 : r1 ≠ c2) (h13 : r1 ≠ c3) :
    ∀ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) →
      a • (lin lam r1 * lin lam r2 * lin lam r3) +
        b • (lin lam c1 * lin lam c2 * lin lam c3) ≠ 0 := by
  intro a b hab h0
  obtain ⟨Z, z0, z1, z2, z3⟩ := exists_sep lam c1 r1 r2 r3 h11 h21 h31
  obtain ⟨Z', y0, y1, y2, y3⟩ := exists_sep lam r1 c1 c2 c3 h11.symm h12.symm h13.symm
  have e1 := congrArg (MvPolynomial.eval ![Z.1, Z.2]) h0
  have e2 := congrArg (MvPolynomial.eval ![Z'.1, Z'.2]) h0
  simp only [map_add, MvPolynomial.smul_eval, map_mul, eval_lin, map_zero] at e1 e2
  rw [z0, sub_self, zero_mul, zero_mul, mul_zero, add_zero] at e1
  rw [y0, sub_self, zero_mul, zero_mul, mul_zero, zero_add] at e2
  have n1 := mul_ne_zero (mul_ne_zero (sub_ne_zero.2 z1) (sub_ne_zero.2 z2)) (sub_ne_zero.2 z3)
  have n2 := mul_ne_zero (mul_ne_zero (sub_ne_zero.2 y1) (sub_ne_zero.2 y2)) (sub_ne_zero.2 y3)
  have ha : a = 0 := (mul_eq_zero.1 e1).resolve_right n1
  have hb : b = 0 := (mul_eq_zero.1 e2).resolve_right n2
  rcases hab with h | h
  · exact h ha
  · exact h hb

lemma fin3_forall {q : Fin 3 → Prop} (h0 : q 0) (h1 : q 1) (h2 : q 2) : ∀ i, q i := by
  intro i
  have : i = 0 ∨ i = 1 ∨ i = 2 := by
    revert i
    decide
  rcases this with rfl | rfl | rfl <;> assumption

/-- A three by three grid of vertices and points gives ten points on a cubic. -/
lemma grid_cubic (hinj : Set.InjOn (sl lam) A) (hA : 10 ≤ #A) (r c : Fin 3 → ℝ × ℝ)
    (p : Fin 3 → Fin 3 → ℝ × ℝ)
    (hr : ∀ i j, p i j ∈ blk A lam (r i)) (hc : ∀ i j, p i j ∈ blk A lam (c j))
    (hrc : ∀ i j, r i ≠ c j)
    (hrow : ∀ i, p i 0 ≠ p i 1 ∧ p i 0 ≠ p i 2 ∧ p i 1 ≠ p i 2)
    (hcol : ∀ j, p 0 j ≠ p 1 j ∧ p 0 j ≠ p 2 j ∧ p 1 j ≠ p 2 j) :
    ∃ S ⊆ A, #S = 10 ∧ OnCubic S := by
  have hrow' : ∀ i j k, j ≠ k → p i j ≠ p i k := by
    intro i
    obtain ⟨u1, u2, u3⟩ := hrow i
    refine fin3_forall (fin3_forall ?_ ?_ ?_) (fin3_forall ?_ ?_ ?_) (fin3_forall ?_ ?_ ?_)
    · exact fun h => absurd rfl h
    · exact fun _ => u1
    · exact fun _ => u2
    · exact fun _ => u1.symm
    · exact fun h => absurd rfl h
    · exact fun _ => u3
    · exact fun _ => u2.symm
    · exact fun _ => u3.symm
    · exact fun h => absurd rfl h
  have hcol' : ∀ j i k, i ≠ k → p i j ≠ p k j := by
    intro j
    obtain ⟨u1, u2, u3⟩ := hcol j
    refine fin3_forall (fin3_forall ?_ ?_ ?_) (fin3_forall ?_ ?_ ?_) (fin3_forall ?_ ?_ ?_)
    · exact fun h => absurd rfl h
    · exact fun _ => u1
    · exact fun _ => u2
    · exact fun _ => u1.symm
    · exact fun h => absurd rfl h
    · exact fun _ => u3
    · exact fun _ => u2.symm
    · exact fun _ => u3.symm
    · exact fun h => absurd rfl h
  have hinjp : Function.Injective (fun q : Fin 3 × Fin 3 => p q.1 q.2) := by
    rintro ⟨i, j⟩ ⟨k, l⟩ h
    replace h : p i j = p k l := h
    by_cases hik : i = k
    · subst hik
      by_cases hjl : j = l
      · rw [hjl]
      · exact absurd h (hrow' i j l hjl)
    · exfalso
      by_cases hjl : j = l
      · subst hjl
        exact hcol' j i k hik h
      · have h1 : p i j ∈ blk A lam (c l) := h ▸ hc k l
        exact hrc i l (eq_of_mem_blk hinj (hr i j) (hr i l) h1 (hc i l) (hrow' i j l hjl))
  have hT : #(Finset.univ.image (fun q : Fin 3 × Fin 3 => p q.1 q.2)) = 9 := by
    rw [Finset.card_image_of_injective _ hinjp]
    simp
  have hTA : Finset.univ.image (fun q : Fin 3 × Fin 3 => p q.1 q.2) ⊆ A := by
    intro x hx
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hx
    exact blk_subset A lam _ (hr q.1 q.2)
  have h3 : ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2 := by decide
  refine OMA.R_Green69_green_69_variants_elekes_szabo_R1.ten_of_pencil A _ hTA hT hA
    (lin lam (r 0) * lin lam (r 1) * lin lam (r 2))
    (lin lam (c 0) * lin lam (c 1) * lin lam (c 2))
    (totalDegree_lin3 lam _ _ _) (totalDegree_lin3 lam _ _ _) ?_ ?_
    (pencil_ind lam (r 0) (r 1) (r 2) (c 0) (c 1) (c 2) (hrc 0 0) (hrc 1 0) (hrc 2 0)
      (hrc 0 1) (hrc 0 2))
  · intro x hx
    obtain ⟨⟨i, j⟩, -, rfl⟩ := Finset.mem_image.1 hx
    have hz : ht lam (p i j) (r i).1 - (r i).2 = 0 := sub_eq_zero.2 (mem_blk.1 (hr i j)).2
    simp only [map_mul, eval_lin]
    rcases h3 i with rfl | rfl | rfl <;> rw [hz] <;> simp
  · intro x hx
    obtain ⟨⟨i, j⟩, -, rfl⟩ := Finset.mem_image.1 hx
    have hz : ht lam (p i j) (c j).1 - (c j).2 = 0 := sub_eq_zero.2 (mem_blk.1 (hc i j)).2
    simp only [map_mul, eval_lin]
    rcases h3 j with rfl | rfl | rfl <;> rw [hz] <;> simp

/-- A point keeps its rank between two adjacent vertices of its dual line. -/
lemma adj_rank (hinj : Set.InjOn (sl lam) A) {P v w : ℝ × ℝ} (h : Adj A lam P v w) :
    rp A lam v.1 P = rm A lam w.1 P :=
  rp_eq_rm hinj (blk_subset A lam v h.1) h.2.2.1 h.2.2.2

lemma right_ne (hinj : Set.InjOn (sl lam) A) {P Q v w w' : ℝ × ℝ} (h : Adj A lam P v w)
    (h' : Adj A lam Q v w') (hPQ : P ≠ Q) : w ≠ w' := by
  rintro rfl
  have e := eq_of_mem_blk hinj h.1 h'.1 h.2.1 h'.2.1 hPQ
  have hlt := h.2.2.1
  rw [e] at hlt
  exact lt_irrefl _ hlt

lemma left_ne (hinj : Set.InjOn (sl lam) A) {P Q v w w' : ℝ × ℝ} (h : Adj A lam P w v)
    (h' : Adj A lam Q w' v) (hPQ : P ≠ Q) : w ≠ w' := by
  rintro rfl
  have e := eq_of_mem_blk hinj h.1 h'.1 h.2.1 h'.2.1 hPQ
  have hlt := h.2.2.1
  rw [e] at hlt
  exact lt_irrefl _ hlt

lemma lr_ne {P Q v w w' : ℝ × ℝ} (h : Adj A lam P w v) (h' : Adj A lam Q v w') : w' ≠ w := by
  rintro rfl
  exact lt_asymm h.2.2.1 h'.2.2.1

/-- A triangle to the right of `v`, in the gap between the points `Plo` and `Phi` of `v`. -/
lemma tri_right (hinj : Set.InjOn (sl lam) A) {g : ℕ} {v T C' Plo Phi : ℝ × ℝ}
    (h : Tri A lam g v T C') (hT3 : #(blk A lam T) = 3)
    (hlo : Plo ∈ blk A lam v) (hhi : Phi ∈ blk A lam v)
    (rlo : rp A lam v.1 Plo + 1 = g) (rhi : rp A lam v.1 Phi = g) :
    ∃ Nlo Nhi s : ℝ × ℝ, Nlo ∈ verts A lam ∧ Nhi ∈ verts A lam ∧ Adj A lam Plo v Nlo ∧
      Adj A lam Phi v Nhi ∧ s ∈ blk A lam Nlo ∧ s ∈ blk A lam Nhi ∧
      (rm A lam Nlo.1 s = g ∨ rm A lam Nlo.1 s + 3 = g) ∧
      (rm A lam Nhi.1 s = g + 2 ∨ rm A lam Nhi.1 s + 1 = g) := by
  obtain ⟨a, b, c, ha, hb, hc, hcase⟩ := tri_face hinj h
  obtain ⟨-, hTv, hC'v, -⟩ := h
  have hAlo := blk_subset A lam v hlo
  have hAhi := blk_subset A lam v hhi
  have hAa := blk_subset A lam v ha.1
  have hAc := blk_subset A lam v hc.1
  have hadd := rm_add_rp hinj hb.1
  rw [hT3] at hadd
  rcases hcase with ⟨ht, h1, h2, h3, h4, h5, h6⟩ | ⟨ht, h1, h2, h3, h4, h5, h6⟩
  · have ea : a = Phi := rp_injOn hinj v.1 hAa hAhi (by omega)
    have ec : c = Plo := rp_injOn hinj v.1 hAc hAlo (by omega)
    subst ea
    subst ec
    unfold tchA at ht
    exact ⟨C', T, b, hC'v, hTv, hc, ha, hb.2.1, hb.1, Or.inl h4, Or.inl (by omega)⟩
  · have ea : a = Plo := rp_injOn hinj v.1 hAa hAlo (by omega)
    have ec : c = Phi := rp_injOn hinj v.1 hAc hAhi (by omega)
    subst ea
    subst ec
    unfold tchB at ht
    rw [hT3] at ht
    exact ⟨T, C', b, hTv, hC'v, ha, hc, hb.1, hb.2.1, Or.inr (by omega), Or.inr h4⟩

/-- A triangle to the left of `v`, in the gap between the points `Plo` and `Phi` of `v`. -/
lemma tri_left (hinj : Set.InjOn (sl lam) A) {g : ℕ} {v C T Plo Phi : ℝ × ℝ}
    (h : Tri A lam g C T v) (hT3 : #(blk A lam T) = 3)
    (hlo : Plo ∈ blk A lam v) (hhi : Phi ∈ blk A lam v)
    (rlo : rm A lam v.1 Plo + 1 = g) (rhi : rm A lam v.1 Phi = g) :
    ∃ Mlo Mhi s : ℝ × ℝ, Mlo ∈ verts A lam ∧ Mhi ∈ verts A lam ∧ Adj A lam Plo Mlo v ∧
      Adj A lam Phi Mhi v ∧ s ∈ blk A lam Mlo ∧ s ∈ blk A lam Mhi ∧
      (rp A lam Mlo.1 s = g ∨ rp A lam Mlo.1 s + 3 = g) ∧
      (rp A lam Mhi.1 s = g + 2 ∨ rp A lam Mhi.1 s + 1 = g) := by
  obtain ⟨a, b, c, ha, hb, hc, hcase⟩ := tri_face hinj h
  obtain ⟨hCv, hTv, -, -⟩ := h
  have hAlo := blk_subset A lam v hlo
  have hAhi := blk_subset A lam v hhi
  have hAb := blk_subset A lam v hb.2.1
  have hAc := blk_subset A lam v hc.2.1
  have hadd := rm_add_rp hinj ha.2.1
  rw [hT3] at hadd
  rcases hcase with ⟨ht, h1, h2, h3, h4, h5, h6⟩ | ⟨ht, h1, h2, h3, h4, h5, h6⟩
  · have eb : b = Phi := rm_injOn hinj v.1 hAb hAhi (by omega)
    have ec : c = Plo := rm_injOn hinj v.1 hAc hAlo (by omega)
    subst eb
    subst ec
    unfold tchA at ht
    exact ⟨C, T, a, hCv, hTv, hc, hb, ha.1, ha.2.1, Or.inl h1, Or.inl (by omega)⟩
  · have eb : b = Plo := rm_injOn hinj v.1 hAb hAlo (by omega)
    have ec : c = Phi := rm_injOn hinj v.1 hAc hAhi (by omega)
    subst eb
    subst ec
    unfold tchB at ht
    rw [hT3] at ht
    exact ⟨T, C, a, hTv, hCv, hb, hc, ha.2.1, ha.1, Or.inr (by omega), Or.inr h1⟩

/-- The triangle above `v`. -/
lemma tri_top (hinj : Set.InjOn (sl lam) A) {v C C' Pl Pr : ℝ × ℝ}
    (h : Tri A lam (bet A lam v + 3) C v C')
    (hl : Pl ∈ blk A lam v) (hr : Pr ∈ blk A lam v)
    (rl : rm A lam v.1 Pl = bet A lam v + 2) (rr : rp A lam v.1 Pr = bet A lam v + 2) :
    ∃ s : ℝ × ℝ, C ∈ verts A lam ∧ C' ∈ verts A lam ∧ Adj A lam Pl C v ∧ Adj A lam Pr v C' ∧
      s ∈ blk A lam C ∧ s ∈ blk A lam C' ∧ rp A lam C.1 s = bet A lam v + 3 ∧
      rm A lam C'.1 s = bet A lam v + 3 := by
  obtain ⟨a, b, c, ha, hb, hc, hcase⟩ := tri_face hinj h
  obtain ⟨hCv, -, hC'v, -⟩ := h
  rcases hcase with ⟨ht, -⟩ | ⟨-, h1, h2, h3', h4, h5, h6⟩
  · unfold tchA at ht
    omega
  · have ea : a = Pl :=
      rm_injOn hinj v.1 (blk_subset A lam v ha.2.1) (blk_subset A lam v hl) (by omega)
    have eb : b = Pr :=
      rp_injOn hinj v.1 (blk_subset A lam v hb.1) (blk_subset A lam v hr) (by omega)
    subst ea
    subst eb
    exact ⟨c, hCv, hC'v, ha, hb, hc.1, hc.2.1, h5, h6⟩

/-- The triangle below `v`. -/
lemma tri_bot (hinj : Set.InjOn (sl lam) A) {v C C' Pl Pr : ℝ × ℝ}
    (h : Tri A lam (bet A lam v) C v C') (h3 : #(blk A lam v) = 3)
    (hl : Pl ∈ blk A lam v) (hr : Pr ∈ blk A lam v)
    (rl : rm A lam v.1 Pl = bet A lam v) (rr : rp A lam v.1 Pr = bet A lam v) :
    ∃ s : ℝ × ℝ, C ∈ verts A lam ∧ C' ∈ verts A lam ∧ Adj A lam Pl C v ∧ Adj A lam Pr v C' ∧
      s ∈ blk A lam C ∧ s ∈ blk A lam C' ∧ rp A lam C.1 s + 1 = bet A lam v ∧
      rm A lam C'.1 s + 1 = bet A lam v := by
  obtain ⟨a, b, c, ha, hb, hc, hcase⟩ := tri_face hinj h
  obtain ⟨hCv, -, hC'v, -⟩ := h
  rcases hcase with ⟨-, h1, h2, h3', h4, h5, h6⟩ | ⟨ht, -⟩
  · have ea : a = Pl :=
      rm_injOn hinj v.1 (blk_subset A lam v ha.2.1) (blk_subset A lam v hl) (by omega)
    have eb : b = Pr :=
      rp_injOn hinj v.1 (blk_subset A lam v hb.1) (blk_subset A lam v hr) (by omega)
    subst ea
    subst eb
    exact ⟨c, hCv, hC'v, ha, hb, hc.1, hc.2.1, h5, h6⟩
  · unfold tchB at ht
    omega

lemma ne_of_val {f : ℝ × ℝ → ℕ} {s t : ℝ × ℝ} (h : f s ≠ f t) : s ≠ t :=
  fun e => h (e ▸ rfl)

end loc

/-- Local step: the six neighbours of a good vertex form a three by three grid, which lies
on a pencil of cubics. -/
theorem ten_of_good (A : Finset (ℝ × ℝ)) (lam : ℝ) (hinj : Set.InjOn (sl lam) A)
    (hk : ∀ v : ℝ × ℝ, #(blk A lam v) ≤ 3) (hA : 10 ≤ #A) {v : ℝ × ℝ} (hv : Good A lam v) :
    ∃ S ⊆ A, #S = 10 ∧ OnCubic S := by
  have _ := hk
  obtain ⟨-, h3, ⟨T1, C1, hRL, hRL1, -⟩, ⟨C2, T2, hLL, -, hLL2⟩, ⟨T3, C3, hRH, hRH1, -⟩,
    ⟨C4, T4, hLH, -, hLH2⟩, ⟨C5, C5', hBo, -, -⟩, ⟨C6, C6', hTo, -, -⟩⟩ := hv
  obtain ⟨P1, hP1, r1⟩ := exists_mem_blk_rp hinj (v := v) (r := bet A lam v) le_rfl (by omega)
  obtain ⟨P2, hP2, r2⟩ :=
    exists_mem_blk_rp hinj (v := v) (r := bet A lam v + 1) (by omega) (by omega)
  obtain ⟨P3, hP3, r3⟩ :=
    exists_mem_blk_rp hinj (v := v) (r := bet A lam v + 2) (by omega) (by omega)
  have m1 := rm_add_rp hinj hP1
  have m2 := rm_add_rp hinj hP2
  have m3 := rm_add_rp hinj hP3
  rw [h3] at m1 m2 m3
  have q1 : rm A lam v.1 P1 = bet A lam v + 2 := by omega
  have q2 : rm A lam v.1 P2 = bet A lam v + 1 := by omega
  have q3 : rm A lam v.1 P3 = bet A lam v := by omega
  have d12 : P1 ≠ P2 := ne_of_val (f := rp A lam v.1) (by omega)
  have d13 : P1 ≠ P3 := ne_of_val (f := rp A lam v.1) (by omega)
  have d23 : P2 ≠ P3 := ne_of_val (f := rp A lam v.1) (by omega)
  clear m1 m2 m3
  obtain ⟨N1, N2, s12, hN1, hN2, a1, a2, s12N1, s12N2, k1, k2⟩ :=
    tri_right hinj hRL hRL1 hP1 hP2 (by rw [r1]) r2
  obtain ⟨N2', N3, s23, hN2', hN3, a2', a3, s23N2, s23N3, k3, k4⟩ :=
    tri_right hinj hRH hRH1 hP2 hP3 (by rw [r2]) r3
  obtain rfl : N2 = N2' := adj_right_unique hinj a2 a2' hN2 hN2'
  obtain ⟨M2, M1, s12p, hM2, hM1, b2, b1, s12pM2, s12pM1, k5, k6⟩ :=
    tri_left hinj hLH hLH2 hP2 hP1 (by rw [q2]) q1
  obtain ⟨M3, M2', s23p, hM3, hM2', b3, b2', s23pM3, s23pM2, k7, k8⟩ :=
    tri_left hinj hLL hLL2 hP3 hP2 (by rw [q3]) q2
  obtain rfl : M2 = M2' := adj_left_unique hinj b2 b2' hM2 hM2'
  obtain ⟨t, hC6, hC6', b1', a3', tM1, tN3, k9, k10⟩ := tri_top hinj hTo hP1 hP3 q1 r3
  obtain rfl : M1 = C6 := adj_left_unique hinj b1 b1' hM1 hC6
  obtain rfl : N3 = C6' := adj_right_unique hinj a3 a3' hN3 hC6'
  obtain ⟨u, hC5, hC5', b3', a1', uM3, uN1, k11, k12⟩ := tri_bot hinj hBo h3 hP3 hP1 q3 r1
  obtain rfl : M3 = C5 := adj_left_unique hinj b3 b3' hM3 hC5
  obtain rfl : N1 = C5' := adj_right_unique hinj a1 a1' hN1 hC5'
  -- ranks of the three points of `v` at the six neighbours
  have e1 : rm A lam N1.1 P1 = bet A lam v := (adj_rank hinj a1).symm.trans r1
  have e2 : rm A lam N2.1 P2 = bet A lam v + 1 := (adj_rank hinj a2).symm.trans r2
  have e3 : rm A lam N3.1 P3 = bet A lam v + 2 := (adj_rank hinj a3).symm.trans r3
  have f1 : rp A lam M1.1 P1 = bet A lam v + 2 := (adj_rank hinj b1).trans q1
  have f2 : rp A lam M2.1 P2 = bet A lam v + 1 := (adj_rank hinj b2).trans q2
  have f3 : rp A lam M3.1 P3 = bet A lam v := (adj_rank hinj b3).trans q3
  -- distinctness of the three listed points of each neighbour
  have x1 : s12 ≠ P1 := ne_of_val (f := rm A lam N1.1) (by clear * - k1 e1; omega)
  have x2 : s12 ≠ u := ne_of_val (f := rm A lam N1.1) (by clear * - k1 k12; omega)
  have x3 : P1 ≠ u := ne_of_val (f := rm A lam N1.1) (by clear * - e1 k12; omega)
  have x4 : s23 ≠ t := ne_of_val (f := rm A lam N3.1) (by clear * - k4 k10; omega)
  have x5 : s23 ≠ P3 := ne_of_val (f := rm A lam N3.1) (by clear * - k4 e3; omega)
  have x6 : t ≠ P3 := ne_of_val (f := rm A lam N3.1) (by clear * - k10 e3; omega)
  have x7 : P2 ≠ s12p := ne_of_val (f := rp A lam M2.1) (by clear * - f2 k5; omega)
  have x8 : P2 ≠ s23p := ne_of_val (f := rp A lam M2.1) (by clear * - f2 k8; omega)
  have x9 : s12p ≠ s23p := ne_of_val (f := rp A lam M2.1) (by clear * - k5 k8; omega)
  have y1 : s12 ≠ s23 := ne_of_val (f := rm A lam N2.1) (by clear * - k2 k3; omega)
  have y2 : s12 ≠ P2 := ne_of_val (f := rm A lam N2.1) (by clear * - k2 e2; omega)
  have y3 : s23 ≠ P2 := ne_of_val (f := rm A lam N2.1) (by clear * - k3 e2; omega)
  have y4 : P1 ≠ t := ne_of_val (f := rp A lam M1.1) (by clear * - f1 k9; omega)
  have y5 : P1 ≠ s12p := ne_of_val (f := rp A lam M1.1) (by clear * - f1 k6; omega)
  have y6 : t ≠ s12p := ne_of_val (f := rp A lam M1.1) (by clear * - k9 k6; omega)
  have y7 : u ≠ P3 := ne_of_val (f := rp A lam M3.1) (by clear * - k11 f3; omega)
  have y8 : u ≠ s23p := ne_of_val (f := rp A lam M3.1) (by clear * - k11 k7; omega)
  have y9 : P3 ≠ s23p := ne_of_val (f := rp A lam M3.1) (by clear * - f3 k7; omega)
  refine grid_cubic hinj hA ![N1, N3, M2] ![N2, M1, M3]
    ![![s12, P1, u], ![s23, t, P3], ![P2, s12p, s23p]] ?_ ?_ ?_ ?_ ?_
  · exact fin3_forall (fin3_forall s12N1 a1.2.1 uN1) (fin3_forall s23N3 tN3 a3.2.1)
      (fin3_forall b2.1 s12pM2 s23pM2)
  · exact fin3_forall (fin3_forall s12N2 b1.1 uM3) (fin3_forall s23N2 tM1 b3.1)
      (fin3_forall a2.2.1 s12pM1 s23pM3)
  · exact fin3_forall (fin3_forall (right_ne hinj a1 a2 d12) (lr_ne b1 a1) (lr_ne b3 a1))
      (fin3_forall (right_ne hinj a3 a2 d23.symm) (lr_ne b1 a3) (lr_ne b3 a3))
      (fin3_forall (lr_ne b2 a2).symm (left_ne hinj b2 b1 d12.symm) (left_ne hinj b2 b3 d23))
  · exact fin3_forall ⟨x1, x2, x3⟩ ⟨x4, x5, x6⟩ ⟨x7, x8, x9⟩
  · exact fin3_forall ⟨y1, y2, y3⟩ ⟨y4, y5, y6⟩ ⟨y7, y8, y9⟩

-- END LOCAL

-- BEGIN BRIDGE
/-- Some `lam` makes the slope injective on `A`. -/
lemma exists_lam_injOn (A : Finset (ℝ × ℝ)) : ∃ lam : ℝ, Set.InjOn (sl lam) A := by
  obtain ⟨lam, hlam⟩ := Infinite.exists_notMem_finset
    (A.offDiag.image fun p : (ℝ × ℝ) × (ℝ × ℝ) => -(p.1.1 - p.2.1) / (p.1.2 - p.2.2))
  refine ⟨lam, fun P hP Q hQ h => ?_⟩
  by_contra hPQ
  apply hlam
  refine Finset.mem_image.2 ⟨(P, Q), Finset.mem_offDiag.2 ⟨hP, hQ, hPQ⟩, ?_⟩
  simp only [sl] at h
  have h2 : P.2 - Q.2 ≠ 0 := by
    intro h0
    apply hPQ
    have h3 : P.2 = Q.2 := by linarith
    refine Prod.ext ?_ h3
    rw [h3] at h
    linarith
  show -(P.1 - Q.1) / (P.2 - Q.2) = lam
  rw [div_eq_iff h2]
  linear_combination (-1 : ℝ) * h

/-- A block is a collinear set. -/
lemma blk_collinear (A : Finset (ℝ × ℝ)) (lam : ℝ) (v : ℝ × ℝ) :
    Collinear ℝ ((blk A lam v : Finset (ℝ × ℝ)) : Set (ℝ × ℝ)) := by
  rcases (blk A lam v).eq_empty_or_nonempty with h | ⟨Z₀, hZ₀⟩
  · rw [h, Finset.coe_empty]
    exact collinear_empty ℝ _
  · rw [collinear_iff_of_mem (p₀ := Z₀) (Finset.mem_coe.2 hZ₀)]
    refine ⟨(1 - lam * v.1, v.1), fun Z hZ => ?_⟩
    have h0 := (mem_blk.1 hZ₀).2
    have h1 := (mem_blk.1 (Finset.mem_coe.1 hZ)).2
    simp only [ht, sl] at h0 h1
    by_cases hy : v.1 = 0
    · refine ⟨Z.1 - Z₀.1, ?_⟩
      rw [hy] at h0 h1
      refine Prod.ext ?_ ?_
      · simp [hy]
      · simp [hy]
        linarith
    · refine ⟨(Z.2 - Z₀.2) / v.1, ?_⟩
      have key : (Z.1 - Z₀.1) * v.1 = (Z.2 - Z₀.2) * (1 - lam * v.1) := by
        linear_combination h1 - h0
      have e1 : Z.1 - Z₀.1 = (Z.2 - Z₀.2) / v.1 * (1 - lam * v.1) := by
        rw [div_mul_eq_mul_div, eq_div_iff hy]
        exact key
      have e2 : Z.2 - Z₀.2 = (Z.2 - Z₀.2) / v.1 * v.1 := by
        rw [div_mul_cancel₀ _ hy]
      refine Prod.ext ?_ ?_
      · simp only [vadd_eq_add, Prod.fst_add, Prod.smul_fst, smul_eq_mul]
        linarith
      · simp only [vadd_eq_add, Prod.snd_add, Prod.smul_snd, smul_eq_mul]
        linarith

/-- The dual lines of the points of a line through two points of a block pass through the
vertex. -/
lemma ht_of_mem_line {lam : ℝ} {x y z : ℝ × ℝ} {t c : ℝ} (hz : z ∈ line[ℝ, x, y])
    (hx : ht lam x t = c) (hy : ht lam y t = c) : ht lam z t = c := by
  rw [← vsub_vadd z x, vadd_left_mem_affineSpan_pair] at hz
  obtain ⟨r, hr⟩ := hz
  have h1 : r * (y.1 - x.1) = z.1 - x.1 := by simpa using congrArg Prod.fst hr
  have h2 : r * (y.2 - x.2) = z.2 - x.2 := by simpa using congrArg Prod.snd hr
  simp only [ht, sl] at hx hy ⊢
  linear_combination (1 - r) * hx + r * hy - t * h1 - (lam * t - 1) * h2

/-- A point whose dual line passes through the crossing of the dual lines of `x` and `y` lies
on the line through `x` and `y`. -/
lemma mem_line_of_ht {lam : ℝ} {x y p : ℝ × ℝ} {t c : ℝ} (hxy : sl lam x ≠ sl lam y)
    (hx : ht lam x t = c) (hy : ht lam y t = c) (hp : ht lam p t = c) :
    p ∈ line[ℝ, x, y] := by
  rw [← vsub_vadd p x, vadd_left_mem_affineSpan_pair]
  have hD : sl lam y - sl lam x ≠ 0 := fun h => hxy (by linarith)
  refine ⟨(sl lam p - sl lam x) / (sl lam y - sl lam x), ?_⟩
  simp only [ht, sl] at hx hy hp hD ⊢
  refine Prod.ext ?_ ?_
  · simp only [vsub_eq_sub, Prod.smul_fst, Prod.fst_sub, smul_eq_mul]
    rw [div_mul_eq_mul_div, div_eq_iff hD]
    linear_combination (-lam) * ((y.1 - x.1 + lam * (y.2 - x.2)) * (hp - hx) -
      (p.1 - x.1 + lam * (p.2 - x.2)) * (hy - hx))
  · simp only [vsub_eq_sub, Prod.smul_snd, Prod.snd_sub, smul_eq_mul]
    rw [div_mul_eq_mul_div, div_eq_iff hD]
    linear_combination (y.1 - x.1 + lam * (y.2 - x.2)) * (hp - hx) -
      (p.1 - x.1 + lam * (p.2 - x.2)) * (hy - hx)

/-- A triple line has a triple vertex whose block is the set of its points in `A`. -/
lemma tripleLine_vertex {A : Finset (ℝ × ℝ)} {lam : ℝ} (hinj : Set.InjOn (sl lam) A)
    (hk : ∀ v : ℝ × ℝ, #(blk A lam v) ≤ 3) {L : AffineSubspace ℝ (ℝ × ℝ)}
    (hL : L ∈ tripleLines A) :
    ∃ v ∈ (verts A lam).filter (fun v => #(blk A lam v) = 3),
      ∀ p ∈ A, (p ∈ L ↔ p ∈ blk A lam v) := by
  obtain ⟨x, hx, y, hy, z, hz, hxy, hzx, hzy, hzL, rfl⟩ := hL
  obtain ⟨hv, hxb, hyb⟩ := vertex_of_pair hinj hx hy hxy
  have hxv := (mem_blk.1 hxb).2
  have hyv := (mem_blk.1 hyb).2
  have hmem : ∀ p ∈ A, (p ∈ line[ℝ, x, y] ↔
      p ∈ blk A lam (cx lam x y, ht lam x (cx lam x y))) := by
    intro p hp
    constructor
    · intro hpL
      exact mem_blk.2 ⟨hp, ht_of_mem_line hpL hxv hyv⟩
    · intro hpb
      exact mem_line_of_ht (fun h => hxy (hinj hx hy h)) hxv hyv (mem_blk.1 hpb).2
  refine ⟨_, Finset.mem_filter.2 ⟨hv, le_antisymm (hk _) ?_⟩, hmem⟩
  have hsub : ({x, y, z} : Finset (ℝ × ℝ)) ⊆ blk A lam (cx lam x y, ht lam x (cx lam x y)) := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl
    · exact hxb
    · exact hyb
    · exact (hmem _ hz).1 hzL
  have hc : #({x, y, z} : Finset (ℝ × ℝ)) = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simpa using hzy.symm
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hxy, hzx.symm⟩
  calc 3 = #({x, y, z} : Finset (ℝ × ℝ)) := hc.symm
    _ ≤ _ := Finset.card_le_card hsub

/-- Triple lines inject into triple vertices. -/
lemma tripleLines_ncard_le_triple {A : Finset (ℝ × ℝ)} {lam : ℝ} (hinj : Set.InjOn (sl lam) A)
    (hk : ∀ v : ℝ × ℝ, #(blk A lam v) ≤ 3) :
    (tripleLines A).ncard ≤ #((verts A lam).filter fun v => #(blk A lam v) = 3) := by
  have hex : ∀ L : AffineSubspace ℝ (ℝ × ℝ), ∃ v : ℝ × ℝ, L ∉ tripleLines A ∨
      (v ∈ (verts A lam).filter (fun v => #(blk A lam v) = 3) ∧
        ∀ p ∈ A, (p ∈ L ↔ p ∈ blk A lam v)) := by
    intro L
    by_cases hL : L ∈ tripleLines A
    · obtain ⟨v, hv, h⟩ := tripleLine_vertex hinj hk hL
      exact ⟨v, Or.inr ⟨hv, h⟩⟩
    · exact ⟨0, Or.inl hL⟩
  choose f hf' using hex
  have hf : ∀ L, L ∈ tripleLines A →
      f L ∈ (verts A lam).filter (fun v => #(blk A lam v) = 3) ∧
        ∀ p ∈ A, (p ∈ L ↔ p ∈ blk A lam (f L)) :=
    fun L hL => (hf' L).resolve_left (not_not.2 hL)
  have hle := Set.ncard_le_ncard_of_injOn (s := tripleLines A)
    (t := (((verts A lam).filter fun v => #(blk A lam v) = 3 : Finset (ℝ × ℝ)) : Set (ℝ × ℝ)))
    f (fun L hL => Finset.mem_coe.2 (hf L hL).1) ?_ (Finset.finite_toSet _)
  · rwa [Set.ncard_coe_finset] at hle
  · intro L hL L' hL' h
    have h1 := (hf L hL).2
    have h2 := (hf L' hL').2
    rw [h] at h1
    have hsame : ∀ p ∈ A, p ∈ L' → p ∈ L := fun p hp hpL => (h1 p hp).2 ((h2 p hp).1 hpL)
    obtain ⟨x, hx, y, hy, z, hz, hxy, hzx, hzy, hzL, rfl⟩ := hL
    obtain ⟨x', hx', y', hy', z', hz', hxy', hzx', hzy', hzL', rfl⟩ := hL'
    exact (OMA.R_Green69_green_69_variants_elekes_szabo_R1.line_eq_of_mem
      (hsame x' hx' (left_mem_affineSpan_pair _ _ _))
      (hsame y' hy' (right_mem_affineSpan_pair _ _ _)) hxy').symm

/-- Bridge to the statement: choice of `lam`, collinearity, counting of triple lines. -/
theorem bridge (A : Finset (ℝ × ℝ)) (hA : 10 ≤ #A) (hL : AtMostOnLine 3 A)
    (hden : 4 / 25 * (#A : ℝ) ^ 2 ≤ (tripleLines A).ncard) :
    ∃ lam : ℝ, Set.InjOn (sl lam) A ∧ (∀ v : ℝ × ℝ, #(blk A lam v) ≤ 3) ∧
      8 * #((verts A lam).filter fun v => #(blk A lam v) = 2) + 4 * #A ≤
        #((verts A lam).filter fun v => #(blk A lam v) = 3) := by
  obtain ⟨lam, hinj⟩ := exists_lam_injOn A
  have hk : ∀ v : ℝ × ℝ, #(blk A lam v) ≤ 3 := fun v =>
    hL (blk A lam v) (blk_subset A lam v) (blk_collinear A lam v)
  refine ⟨lam, hinj, hk, ?_⟩
  have h3 := tripleLines_ncard_le_triple hinj hk
  have hpc := pair_count (A := A) (lam := lam) hinj
  have hsum : ∑ v ∈ verts A lam, #(blk A lam v) * (#(blk A lam v) - 1) =
      2 * #((verts A lam).filter fun v => #(blk A lam v) = 2) +
        6 * #((verts A lam).filter fun v => #(blk A lam v) = 3) := by
    rw [Finset.card_filter, Finset.card_filter, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v hv => ?_
    have h2 := two_le_card_blk hinj hv
    have h3 := hk v
    have h23 : #(blk A lam v) = 2 ∨ #(blk A lam v) = 3 := by omega
    rcases h23 with h | h <;> simp [h]
  rw [hsum] at hpc
  have h3R : ((tripleLines A).ncard : ℝ) ≤
      (#((verts A lam).filter fun v => #(blk A lam v) = 3) : ℝ) := by
    exact_mod_cast h3
  have h4R : (4 : ℝ) * (#A : ℝ) ^ 2 ≤
      25 * (#((verts A lam).filter fun v => #(blk A lam v) = 3) : ℝ) := by
    linarith
  have h4 : 4 * #A ^ 2 ≤ 25 * #((verts A lam).filter fun v => #(blk A lam v) = 3) := by
    exact_mod_cast h4R
  obtain ⟨m, hm⟩ : ∃ m, #A = m + 1 := ⟨#A - 1, by omega⟩
  rw [hm] at hpc h4 ⊢
  rw [Nat.add_sub_cancel] at hpc
  nlinarith

-- END BRIDGE

end G69D

theorem OMA.solution : OMA.R_Green69_green_69_variants_elekes_szabo_R1_H2_R1.H1 := by
  refine ⟨10, fun A hA hL hden => ?_⟩
  obtain ⟨lam, hinj, hk, hdense⟩ := G69D.bridge A (by omega) hL hden
  obtain ⟨v, hv⟩ := G69D.exists_good A lam hinj hk (by omega) hdense
  exact G69D.ten_of_good A lam hinj hk (by omega) hv
