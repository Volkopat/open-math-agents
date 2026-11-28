import OMAStatements.S_oeis_a224159

-- Credit: @marcusbuffett (the owner of the agent is credited as the solver)
-- Sketch: the slices of the array along its long side (its columns) form a sequence of states with
-- conditions on single states, on adjacent pairs and on adjacent triples (handled through the overlapping pairs).
-- w k y counts valid sequences ending in y (bijection via Fin.init / Fin.snoc, adapted from the merged
-- proof of oeis-a223443 by @sntntHb); the dual vectors u j are tabulated and checked by decide +kernel,
-- together with the coordinatewise relation that gives the recurrence; the g.f. follows
-- coefficientwise from the recurrence and the first values.

namespace OMA.P_oeis_a224159

open Finset

section Gen
variable {σ : Type} [Fintype σ] [DecidableEq σ] (I : σ → Prop) [DecidablePred I]
  (B : σ → Prop) [DecidablePred B] (T : σ → σ → Prop) [DecidableRel T]

def Gd (n : ℕ) (f : Fin n → σ) : Prop :=
  (∀ i : Fin n, i.val = 0 → I (f i)) ∧ (∀ i, B (f i)) ∧ ∀ i j : Fin n, j.val = i.val + 1 → T (f i) (f j)

instance (n : ℕ) : DecidablePred (Gd I B T n) := fun f => by unfold Gd; infer_instance

def w : ℕ → σ → ℕ
  | 0, y => if I y ∧ B y then 1 else 0
  | k + 1, y => ∑ x, if B y ∧ T x y then w k x else 0

def u : ℕ → σ → ℕ
  | 0, _ => 1
  | j + 1, x => ∑ y, if B y ∧ T x y then u j y else 0

def cnt (k : ℕ) (y : σ) : ℕ :=
  ((univ : Finset (Fin (k + 1) → σ)).filter (fun f => Gd I B T (k + 1) f ∧ f (Fin.last k) = y)).card

lemma gd_succ (k : ℕ) (f : Fin (k + 2) → σ) :
    Gd I B T (k + 2) f ↔ Gd I B T (k + 1) (Fin.init f) ∧ B (f (Fin.last (k + 1))) ∧
      T (f (Fin.castSucc (Fin.last k))) (f (Fin.last (k + 1))) := by
  constructor
  · rintro ⟨hI, h0, h⟩
    refine ⟨⟨fun i hi => ?_, fun i => h0 _, fun i j hij => h _ _ (by simp [hij])⟩, h0 _, h _ _ (by simp)⟩
    simpa [Fin.init] using hI (Fin.castSucc i) (by simpa using hi)
  · rintro ⟨⟨hI, h0, h1⟩, h2, h3⟩
    refine ⟨fun i hi => ?_, fun i => ?_, fun i j hij => ?_⟩
    · have := hI ⟨i.val, by omega⟩ hi
      simpa [Fin.init] using this
    · by_cases hi : i.val < k + 1
      · have := h0 ⟨i.val, hi⟩
        simpa [Fin.init] using this
      · have hi' : i = Fin.last (k + 1) := Fin.ext (by simp; omega)
        subst hi'; exact h2
    · by_cases hj : j.val < k + 1
      · have := h1 ⟨i.val, by omega⟩ ⟨j.val, hj⟩ hij
        simpa [Fin.init] using this
      · have hj' : j = Fin.last (k + 1) := Fin.ext (by simp; omega)
        have hi' : i = Fin.castSucc (Fin.last k) := Fin.ext (by simp; omega)
        subst hj' hi'; exact h3

lemma cnt_zero (y : σ) : cnt I B T 0 y = if I y ∧ B y then 1 else 0 := by
  unfold cnt
  split_ifs with hy
  · rw [Finset.card_eq_one]
    refine ⟨fun _ => y, ?_⟩
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨-, h⟩; funext i; rw [show i = Fin.last 0 from Fin.ext (by omega)]; exact h
    · rintro rfl; exact ⟨⟨fun _ _ => hy.1, fun _ => hy.2, fun i j hij => by omega⟩, rfl⟩
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro f - ⟨⟨hI, h0, -⟩, h⟩; exact hy ⟨h ▸ hI (Fin.last 0) rfl, h ▸ h0 _⟩

lemma cnt_succ (k : ℕ) (y : σ) :
    cnt I B T (k + 1) y = ∑ x, if B y ∧ T x y then cnt I B T k x else 0 := by
  by_cases hy : B y
  · have e : cnt I B T (k + 1) y = ((univ : Finset (Fin (k + 1) → σ)).filter
        (fun g => Gd I B T (k + 1) g ∧ T (g (Fin.last k)) y)).card := by
      unfold cnt
      apply Finset.card_nbij' (fun f => Fin.init f) (fun g => Fin.snoc g y)
      · intro f hf
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hf ⊢
        obtain ⟨hg, hl⟩ := hf
        rw [gd_succ] at hg
        refine ⟨hg.1, ?_⟩
        have := hg.2.2; rw [hl] at this; simpa [Fin.init] using this
      · intro g hg
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hg ⊢
        refine ⟨?_, by simp⟩
        rw [gd_succ]
        refine ⟨by simpa using hg.1, by simpa using hy, ?_⟩
        simpa using hg.2
      · intro f hf
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hf
        rw [← hf.2]; exact Fin.snoc_init_self f
      · intro g _; exact Fin.init_snoc _ _
    rw [e, Finset.card_eq_sum_card_fiberwise
      (f := fun g : Fin (k + 1) → σ => g (Fin.last k))
      (t := univ) (fun _ _ => Finset.mem_univ _)]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.filter_filter]
    split_ifs with h
    · unfold cnt; congr 1; apply Finset.filter_congr
      intro g _
      constructor
      · rintro ⟨⟨hg, -⟩, hx⟩; exact ⟨hg, hx⟩
      · rintro ⟨hg, hx⟩; exact ⟨⟨hg, hx ▸ h.2⟩, hx⟩
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro g - ⟨⟨-, ha⟩, hx⟩; exact h ⟨hy, hx ▸ ha⟩
  · have : cnt I B T (k + 1) y = 0 := by
      unfold cnt
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro f - ⟨⟨-, h0, -⟩, h⟩; exact hy (h ▸ h0 _)
    rw [this]; symm
    apply Finset.sum_eq_zero; intro x _
    rw [if_neg (fun h => hy h.1)]

lemma cnt_eq (k : ℕ) (y : σ) : cnt I B T k y = w I B T k y := by
  induction k generalizing y with
  | zero => rw [cnt_zero]; rfl
  | succ k ih => rw [cnt_succ]; simp only [w, ih]

lemma total (k : ℕ) :
    ((univ : Finset (Fin (k + 1) → σ)).filter (Gd I B T (k + 1))).card = ∑ y, w I B T k y := by
  simp only [← cnt_eq]
  unfold cnt
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun g : Fin (k + 1) → σ => g (Fin.last k))
    (t := univ) (fun _ _ => Finset.mem_univ _)]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.filter_filter]

lemma w_zero_of (k : ℕ) (x : σ) (hx : ¬ B x) : w I B T k x = 0 := by
  cases k with
  | zero => simp [w, hx]
  | succ k =>
    simp only [w]
    apply Finset.sum_eq_zero; intro y _
    rw [if_neg (fun h => hx h.1)]

lemma dual (j k : ℕ) : ∑ y, w I B T (k + j) y = ∑ x, w I B T k x * u B T j x := by
  induction j generalizing k with
  | zero => simp [u]
  | succ j ih =>
    rw [show k + (j + 1) = (k + 1) + j by ring, ih (k + 1)]
    simp only [w, u, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro x _
    apply Finset.sum_congr rfl; intro y _
    split_ifs <;> simp

/-- The count of valid sequences of length k + 1 + j through the dual vectors. -/
lemma total_dual (k j : ℕ) :
    ((univ : Finset (Fin (k + j + 1) → σ)).filter (Gd I B T (k + j + 1))).card =
      ∑ x, w I B T k x * u B T j x := by
  rw [total, dual]

end Gen

section Flags

/-- Valley-free: no three positions whose middle value is below both outer values. -/
def VF {n M : ℕ} (g : Fin n → Fin M) : Prop :=
  ∀ j₁ j₂ j₃ : Fin n, j₁ < j₂ → j₂ < j₃ → ¬ (g j₂ < g j₁ ∧ g j₂ < g j₃)

/-- A strict descent occurs at an adjacent pair ending at or before position j. -/
abbrev Dn {n M : ℕ} (g : Fin n → Fin M) (j : Fin n) : Prop :=
  ∃ i i' : Fin n, i'.val = i.val + 1 ∧ i'.val ≤ j.val ∧ g i' < g i

lemma ivt_nat (G : ℕ → ℕ) (a d : ℕ) (h : G (a + d) < G a) :
    ∃ i, a ≤ i ∧ i < a + d ∧ G (i + 1) < G i := by
  induction d with
  | zero => simp at h
  | succ d ih =>
    by_cases h' : G (a + d + 1) < G (a + d)
    · exact ⟨a + d, by omega, by omega, h'⟩
    · obtain ⟨i, h1, h2, h3⟩ := ih (by rw [← add_assoc] at h; omega)
      exact ⟨i, h1, by omega, h3⟩

lemma ivt_nat' (G : ℕ → ℕ) (a d : ℕ) (h : G a < G (a + d)) :
    ∃ i, a ≤ i ∧ i < a + d ∧ G i < G (i + 1) := by
  induction d with
  | zero => simp at h
  | succ d ih =>
    by_cases h' : G (a + d) < G (a + d + 1)
    · exact ⟨a + d, by omega, by omega, h'⟩
    · obtain ⟨i, h1, h2, h3⟩ := ih (by rw [← add_assoc] at h; omega)
      exact ⟨i, h1, by omega, h3⟩

lemma vf_iff {n M : ℕ} (g : Fin n → Fin M) :
    VF g ↔ ∀ j j' : Fin n, j'.val = j.val + 1 → ¬ (Dn g j ∧ g j < g j') := by
  constructor
  · rintro hv j j' hj ⟨⟨i, i', hi, hij, hd⟩, ha⟩
    obtain ⟨q, hq, hmin⟩ := Finset.exists_min_image
      ((univ : Finset (Fin n)).filter (fun q => i'.val ≤ q.val ∧ q.val ≤ j.val)) g
      ⟨i', by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨le_refl _, hij⟩⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq hmin
    have h1 := hmin i' ⟨le_refl _, hij⟩
    have h2 := hmin j ⟨hij, le_refl _⟩
    exact hv i q j' (Fin.lt_def.mpr (by omega)) (Fin.lt_def.mpr (by omega))
      ⟨lt_of_le_of_lt h1 hd, lt_of_le_of_lt h2 ha⟩
  · intro h j₁ j₂ j₃ h12 h23 ⟨hv1, hv2⟩
    have a12 := Fin.lt_def.mp h12; have a23 := Fin.lt_def.mp h23
    let G : ℕ → ℕ := fun k => if hk : k < n then (g ⟨k, hk⟩).val else 0
    have hG : ∀ q : Fin n, G q.val = (g q).val := fun q => by simp [G, q.isLt]
    obtain ⟨i, hi1, hi2, hi3⟩ := ivt_nat G j₁.val (j₂.val - j₁.val)
      (by rw [show j₁.val + (j₂.val - j₁.val) = j₂.val by omega, hG, hG]; exact hv1)
    obtain ⟨k, hk1, hk2, hk3⟩ := ivt_nat' G j₂.val (j₃.val - j₂.val)
      (by rw [show j₂.val + (j₃.val - j₂.val) = j₃.val by omega, hG, hG]; exact hv2)
    have e1 : G (i + 1) = (g ⟨i + 1, by omega⟩).val := hG ⟨i + 1, by omega⟩
    have e2 : G i = (g ⟨i, by omega⟩).val := hG ⟨i, by omega⟩
    have e3 : G (k + 1) = (g ⟨k + 1, by omega⟩).val := hG ⟨k + 1, by omega⟩
    have e4 : G k = (g ⟨k, by omega⟩).val := hG ⟨k, by omega⟩
    refine h ⟨k, by omega⟩ ⟨k + 1, by omega⟩ rfl
      ⟨⟨⟨i, by omega⟩, ⟨i + 1, by omega⟩, rfl, by simp; omega, ?_⟩, ?_⟩
    · rw [Fin.lt_def]; omega
    · rw [Fin.lt_def]; omega

variable {K M : ℕ}

/-- The descent flags of the lines of a sequence of slices at position j. -/
def Fl {n : ℕ} (f : Fin n → Fin K → Fin M) (j : Fin n) : Fin K → Bool :=
  fun l => decide (Dn (fun i => f i l) j)

lemma Fl_zero {n : ℕ} (f : Fin n → Fin K → Fin M) (j : Fin n) (hj : j.val = 0) (l : Fin K) :
    Fl f j l = false := by
  show decide (Dn (fun i => f i l) j) = false
  rw [decide_eq_false_iff_not]
  rintro ⟨i, i', h1, h2, -⟩; omega

lemma Fl_succ {n : ℕ} (f : Fin n → Fin K → Fin M) (j j' : Fin n) (hj : j'.val = j.val + 1)
    (l : Fin K) : Fl f j' l = (Fl f j l || decide (f j' l < f j l)) := by
  show decide (Dn (fun i => f i l) j') = (decide (Dn (fun i => f i l) j) || decide (f j' l < f j l))
  rw [Bool.eq_iff_iff, Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq, decide_eq_true_eq]
  constructor
  · rintro ⟨i, i', h1, h2, h3⟩
    by_cases hc : i'.val ≤ j.val
    · exact Or.inl ⟨i, i', h1, hc, h3⟩
    · right
      have e1 : i' = j' := Fin.ext (by omega)
      have e2 : i = j := Fin.ext (by omega)
      rw [e1, e2] at h3; exact h3
  · rintro (⟨i, i', h1, h2, h3⟩ | h)
    · exact ⟨i, i', h1, by omega, h3⟩
    · exact ⟨j, j', hj, le_refl _, h⟩

variable (B : (Fin K → Fin M) → Prop) [DecidablePred B]
  (T : (Fin K → Fin M) → (Fin K → Fin M) → Prop) [DecidableRel T]

def FI (x : (Fin K → Fin M) × (Fin K → Bool)) : Prop := ∀ l, x.2 l = false

def FB (x : (Fin K → Fin M) × (Fin K → Bool)) : Prop := B x.1

def FT (x y : (Fin K → Fin M) × (Fin K → Bool)) : Prop :=
  T x.1 y.1 ∧ (∀ l, y.2 l = (x.2 l || decide (y.1 l < x.1 l))) ∧
    ∀ l, ¬ (x.2 l = true ∧ x.1 l < y.1 l)

instance : DecidablePred (@FI K M) := fun x => by unfold FI; infer_instance
instance : DecidablePred (FB B) := fun x => by unfold FB; infer_instance
instance : DecidableRel (FT T) := fun x y => by unfold FT; infer_instance

/-- The plain condition: B on every slice, T on adjacent slices, every line valley-free. -/
def GdV (n : ℕ) (f : Fin n → Fin K → Fin M) : Prop :=
  ((∀ i, B (f i)) ∧ ∀ i j : Fin n, j.val = i.val + 1 → T (f i) (f j)) ∧ ∀ l, VF (fun i => f i l)

instance (n : ℕ) : DecidablePred (GdV B T n) := fun f => by unfold GdV VF; infer_instance

lemma flags_consistent {n : ℕ} (h : Fin n → (Fin K → Fin M) × (Fin K → Bool))
    (hh : Gd FI (FB B) (FT T) n h) (j : Fin n) : (h j).2 = Fl (fun i => (h i).1) j := by
  obtain ⟨hI, -, hT⟩ := hh
  obtain ⟨m, hm⟩ := j
  induction m with
  | zero => funext l; rw [Fl_zero _ _ rfl]; exact hI _ rfl l
  | succ m ih =>
    funext l
    rw [Fl_succ _ ⟨m, by omega⟩ _ rfl, ← ih (by omega)]
    exact (hT ⟨m, by omega⟩ ⟨m + 1, hm⟩ rfl).2.1 l

lemma card_flags (n : ℕ) :
    ((univ : Finset (Fin n → Fin K → Fin M)).filter (GdV B T n)).card =
      ((univ : Finset (Fin n → (Fin K → Fin M) × (Fin K → Bool))).filter
        (Gd FI (FB B) (FT T) n)).card := by
  apply Finset.card_nbij' (fun f j => (f j, Fl f j)) (fun h j => (h j).1)
  · intro f hf
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hf ⊢
    obtain ⟨⟨hB, hT⟩, hV⟩ := hf
    refine ⟨fun i hi l => Fl_zero f i hi l, fun i => hB i, fun i j hij => ⟨hT i j hij, fun l => ?_, fun l => ?_⟩⟩
    · exact Fl_succ f i j hij l
    · rintro ⟨h1, h2⟩
      simp only [Fl, decide_eq_true_eq] at h1
      exact (vf_iff _).1 (hV l) i j hij ⟨h1, h2⟩
  · intro h hh
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hh ⊢
    have hc := flags_consistent B T h hh
    obtain ⟨-, hB, hT⟩ := hh
    refine ⟨⟨fun i => hB i, fun i j hij => (hT i j hij).1⟩, fun l => (vf_iff _).2 ?_⟩
    rintro i j hij ⟨h1, h2⟩
    apply (hT i j hij).2.2 l
    refine ⟨?_, h2⟩
    rw [hc i]; simp only [Fl, decide_eq_true_eq]; exact h1
  · intro f _; rfl
  · intro h hh
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hh
    funext j
    exact Prod.ext rfl (flags_consistent B T h hh j).symm

end Flags

section Sparse
variable {X σ : Type} [Fintype X] [DecidableEq X] [Fintype σ] [DecidableEq σ]
  (BX : X → Prop) [DecidablePred BX] (TX : X → X → Prop) [DecidableRel TX]
  (π : X → σ) (nx : X → σ → X) (R : X → σ → Prop) [∀ x t, Decidable (R x t)]

lemma sum_sparse (hπ : ∀ x t, π (nx x t) = t) (hT : ∀ x y, TX x y ↔ y = nx x (π y) ∧ R x (π y))
    (x : X) (g : X → ℕ) :
    (∑ y, if BX y ∧ TX x y then g y else 0) =
      ∑ t, if BX (nx x t) ∧ R x t then g (nx x t) else 0 := by
  rw [← Finset.sum_fiberwise (s := univ) (g := π)]
  apply Finset.sum_congr rfl; intro t _
  rw [Finset.sum_eq_single_of_mem (nx x t) (by simp [hπ])]
  · simp only [hT, hπ, true_and]
  · intro y hy hne
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    rw [if_neg]; rintro ⟨-, h⟩; rw [hT] at h; exact hne (by rw [h.1, hy])

/-- The dual vectors computed through the next slice only. -/
def vS : ℕ → X → ℕ
  | 0, _ => 1
  | j + 1, x => ∑ t, if BX (nx x t) ∧ R x t then vS j (nx x t) else 0

lemma u_eq_vS (hπ : ∀ x t, π (nx x t) = t) (hT : ∀ x y, TX x y ↔ y = nx x (π y) ∧ R x (π y))
    (j : ℕ) (x : X) : u BX TX j x = vS BX nx R j x := by
  induction j generalizing x with
  | zero => rfl
  | succ j ih =>
    simp only [u, vS, ih]
    exact sum_sparse BX TX π nx R hπ hT x _

end Sparse

section FlagStep
variable {K M : ℕ} (T : (Fin K → Fin M) → (Fin K → Fin M) → Prop) [DecidableRel T]

def fnx (x : (Fin K → Fin M) × (Fin K → Bool)) (t : Fin K → Fin M) : (Fin K → Fin M) × (Fin K → Bool) :=
  (t, fun l => x.2 l || decide (t l < x.1 l))

def fR (x : (Fin K → Fin M) × (Fin K → Bool)) (t : Fin K → Fin M) : Prop :=
  T x.1 t ∧ ∀ l, ¬ (x.2 l = true ∧ x.1 l < t l)

instance : ∀ x t, Decidable (fR T x t) := fun x t => by unfold fR; infer_instance

lemma fT_iff (x y : (Fin K → Fin M) × (Fin K → Bool)) :
    FT T x y ↔ y = fnx x (Prod.fst y) ∧ fR T x (Prod.fst y) := by
  unfold FT fnx fR
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨Prod.ext rfl (funext h2), h1, h3⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h2, fun l => ?_, h3⟩
    conv_lhs => rw [h1]

end FlagStep

section Gen3
variable {σ : Type} [Fintype σ] [DecidableEq σ] (B : σ → Prop) [DecidablePred B]
  (T : σ → σ → Prop) [DecidableRel T] (U : σ → σ → σ → Prop) [∀ a b c, Decidable (U a b c)]

def Gd3 (n : ℕ) (f : Fin n → σ) : Prop :=
  (∀ i, B (f i)) ∧ (∀ i j : Fin n, j.val = i.val + 1 → T (f i) (f j)) ∧
    ∀ i j l : Fin n, j.val = i.val + 1 → l.val = j.val + 1 → U (f i) (f j) (f l)

instance (n : ℕ) : DecidablePred (Gd3 B T U n) := fun f => by unfold Gd3; infer_instance

def PB (p : σ × σ) : Prop := B p.1 ∧ B p.2 ∧ T p.1 p.2

def PT (p q : σ × σ) : Prop := p.2 = q.1 ∧ U p.1 p.2 q.2

instance : DecidablePred (PB B T) := fun p => by unfold PB; infer_instance
instance : DecidableRel (PT U) := fun p q => by unfold PT; infer_instance

/-- The overlapping pairs of a sequence. -/
def toP (n : ℕ) (f : Fin (n + 2) → σ) : Fin (n + 1) → σ × σ :=
  fun i => (f i.castSucc, f i.succ)

/-- A sequence from a sequence of pairs. -/
def ofP (n : ℕ) (h : Fin (n + 1) → σ × σ) : Fin (n + 2) → σ :=
  fun i => if hi : i.val < n + 1 then (h ⟨i.val, hi⟩).1 else (h (Fin.last n)).2

lemma gd3_toP (n : ℕ) (f : Fin (n + 2) → σ) (hf : Gd3 B T U (n + 2) f) :
    Gd (fun _ => True) (PB B T) (PT U) (n + 1) (toP n f) := by
  obtain ⟨h1, h2, h3⟩ := hf
  refine ⟨fun _ _ => trivial, fun i => ⟨h1 _, h1 _, h2 _ _ (by simp)⟩, fun i j hij => ⟨?_, ?_⟩⟩
  · simp only [toP]; congr 1; ext; simp [hij]
  · simp only [toP]
    exact h3 _ _ _ (by simp) (by simp [hij])

lemma toP_ofP (n : ℕ) (h : Fin (n + 1) → σ × σ) (hh : Gd (fun _ => True) (PB B T) (PT U) (n + 1) h) :
    toP n (ofP n h) = h := by
  funext i
  simp only [toP, ofP]
  ext
  · simp only [Fin.coe_castSucc, i.isLt, dite_true]
  · by_cases hi : i.val + 1 < n + 1
    · simp only [Fin.val_succ, hi, dite_true]
      have := (hh.2.2 i ⟨i.val + 1, hi⟩ rfl).1
      exact this.symm
    · have hi' : i = Fin.last n := Fin.ext (by simp; omega)
      subst hi'
      simp

lemma ofP_toP (n : ℕ) (f : Fin (n + 2) → σ) : ofP n (toP n f) = f := by
  funext i
  simp only [ofP, toP]
  split_ifs with hi
  · rfl
  · have : i = Fin.last (n + 1) := Fin.ext (by simp; omega)
    subst this; rfl

lemma gd_ofP (n : ℕ) (h : Fin (n + 1) → σ × σ) (hh : Gd (fun _ => True) (PB B T) (PT U) (n + 1) h) :
    Gd3 B T U (n + 2) (ofP n h) := by
  have e := toP_ofP B T U n h hh
  set f := ofP n h
  have hp : ∀ i : Fin (n + 1), PB B T (f i.castSucc, f i.succ) := fun i => by
    have := hh.2.1 i; rw [← e] at this; exact this
  have hq : ∀ i j : Fin (n + 1), j.val = i.val + 1 →
      PT U (f i.castSucc, f i.succ) (f j.castSucc, f j.succ) := fun i j hij => by
    have := hh.2.2 i j hij; rw [← e] at this; exact this
  refine ⟨fun i => ?_, fun i j hij => ?_, fun i j l hij hjl => ?_⟩
  · by_cases hi : i.val < n + 1
    · have := (hp ⟨i.val, hi⟩).1; exact this
    · have := (hp (Fin.last n)).2.1
      have hi' : i = (Fin.last n).succ := Fin.ext (by simp; omega)
      rw [hi']; exact this
  · have := (hp ⟨i.val, by omega⟩).2.2
    have hj : j = (⟨i.val, by omega⟩ : Fin (n + 1)).succ := Fin.ext (by simp; omega)
    rw [hj]; exact this
  · have := (hq ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ hij).2
    have e1 : (⟨i.val, by omega⟩ : Fin (n + 1)).castSucc = i := Fin.ext rfl
    have e2 : (⟨i.val, by omega⟩ : Fin (n + 1)).succ = j := Fin.ext (by simp; omega)
    have e3 : (⟨j.val, by omega⟩ : Fin (n + 1)).succ = l := Fin.ext (by simp; omega)
    rw [e1, e2, e3] at this; exact this

lemma card_pairs (n : ℕ) :
    ((univ : Finset (Fin (n + 2) → σ)).filter (Gd3 B T U (n + 2))).card =
      ((univ : Finset (Fin (n + 1) → σ × σ)).filter (Gd (fun _ => True) (PB B T) (PT U) (n + 1))).card := by
  apply Finset.card_nbij' (toP n) (ofP n)
  · intro f hf
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hf ⊢
    exact gd3_toP B T U n f hf
  · intro h hh
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hh ⊢
    exact gd_ofP B T U n h hh
  · intro f _; exact ofP_toP n f
  · intro h hh
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hh
    exact toP_ofP B T U n h hh

end Gen3

section Flags3
variable {K M : ℕ} (B : (Fin K → Fin M) → Prop) [DecidablePred B]
  (T : (Fin K → Fin M) → (Fin K → Fin M) → Prop) [DecidableRel T]
  (U : (Fin K → Fin M) → (Fin K → Fin M) → (Fin K → Fin M) → Prop) [∀ a b c, Decidable (U a b c)]

/-- Window conditions and valley-free lines. -/
def GdV3 (n : ℕ) (f : Fin n → Fin K → Fin M) : Prop :=
  Gd3 B T U n f ∧ ∀ l, VF (fun i => f i l)

instance (n : ℕ) : DecidablePred (GdV3 B T U n) := fun f => by unfold GdV3 VF; infer_instance

abbrev Yt (K M : ℕ) := ((Fin K → Fin M) × (Fin K → Fin M)) × (Fin K → Bool)

def YI (y : Yt K M) : Prop := ∀ l, y.2 l = decide (y.1.2 l < y.1.1 l)

def YB (y : Yt K M) : Prop := PB B T y.1

def YT (y z : Yt K M) : Prop :=
  PT U y.1 z.1 ∧ (∀ l, z.2 l = (y.2 l || decide (z.1.2 l < y.1.2 l))) ∧
    ∀ l, ¬ (y.2 l = true ∧ y.1.2 l < z.1.2 l)

instance : DecidablePred (@YI K M) := fun y => by unfold YI; infer_instance
instance : DecidablePred (YB B T) := fun y => by unfold YB PB; infer_instance
instance : DecidableRel (YT U) := fun y z => by unfold YT PT; infer_instance

lemma Dn_zero {n : ℕ} (g : Fin n → Fin M) (j : Fin n) (hj : j.val = 0) : ¬ Dn g j := by
  rintro ⟨i, i', h1, h2, -⟩; omega

lemma flags3_consistent (n : ℕ) (h : Fin (n + 1) → Yt K M) (hh : Gd YI (YB B T) (YT U) (n + 1) h)
    (i : Fin (n + 1)) : (h i).2 = Fl (ofP n (fun i => (h i).1)) i.succ := by
  have hp : Gd (fun _ => True) (PB B T) (PT U) (n + 1) (fun i => (h i).1) :=
    ⟨fun _ _ => trivial, fun i => hh.2.1 i, fun i j hij => (hh.2.2 i j hij).1⟩
  have e := toP_ofP B T U n _ hp
  have ec : ∀ i : Fin (n + 1), ofP n (fun i => (h i).1) i.castSucc = (h i).1.1 := fun i => by
    have := congrFun e i; simp only [toP] at this; exact congrArg Prod.fst this
  have es : ∀ i : Fin (n + 1), ofP n (fun i => (h i).1) i.succ = (h i).1.2 := fun i => by
    have := congrFun e i; simp only [toP] at this; exact congrArg Prod.snd this
  obtain ⟨m, hm⟩ := i
  induction m with
  | zero =>
    funext l
    rw [Fl_succ _ (Fin.castSucc ⟨0, hm⟩) _ (by simp), Fl_zero _ _ (by simp), Bool.false_or,
      ec, es]
    exact hh.1 ⟨0, hm⟩ rfl l
  | succ m ih =>
    funext l
    have h1 := (hh.2.2 ⟨m, by omega⟩ ⟨m + 1, hm⟩ rfl).2.1 l
    rw [h1, ih (by omega), Fl_succ _ (Fin.succ ⟨m, by omega⟩) (Fin.succ ⟨m + 1, hm⟩) (by simp),
      show (Fin.succ ⟨m + 1, hm⟩ : Fin (n + 2)) = Fin.succ ⟨m + 1, hm⟩ from rfl, es, es]

lemma card_flags3 (n : ℕ) :
    ((univ : Finset (Fin (n + 2) → Fin K → Fin M)).filter (GdV3 B T U (n + 2))).card =
      ((univ : Finset (Fin (n + 1) → Yt K M)).filter (Gd YI (YB B T) (YT U) (n + 1))).card := by
  apply Finset.card_nbij' (fun f i => (toP n f i, Fl f i.succ)) (fun h => ofP n (fun i => (h i).1))
  · intro f hf
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hf ⊢
    obtain ⟨hg, hV⟩ := hf
    have hp := gd3_toP B T U n f hg
    refine ⟨fun i hi l => ?_, fun i => hp.2.1 i, fun i j hij => ⟨hp.2.2 i j hij, fun l => ?_, fun l => ?_⟩⟩
    · show Fl f i.succ l = decide (f i.succ l < f i.castSucc l)
      rw [Fl_succ _ i.castSucc i.succ (by simp), Fl_zero _ _ (by simpa using hi), Bool.false_or]
    · exact Fl_succ f i.succ j.succ (by simp [hij]) l
    · rintro ⟨h1, h2⟩
      simp only [Fl, decide_eq_true_eq, toP] at h1 h2
      have hs : j.castSucc = i.succ := Fin.ext (by simp [hij])
      try rw [hs] at h2
      exact (vf_iff _).1 (hV l) i.succ j.succ (by simp [hij]) ⟨h1, h2⟩
  · intro h hh
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hh ⊢
    have hp : Gd (fun _ => True) (PB B T) (PT U) (n + 1) (fun i => (h i).1) :=
      ⟨fun _ _ => trivial, fun i => hh.2.1 i, fun i j hij => (hh.2.2 i j hij).1⟩
    have hc := flags3_consistent B T U n h hh
    have e := toP_ofP B T U n _ hp
    have es : ∀ i : Fin (n + 1), ofP n (fun i => (h i).1) i.succ = (h i).1.2 := fun i => by
      have := congrFun e i; simp only [toP] at this; exact congrArg Prod.snd this
    refine ⟨gd_ofP B T U n _ hp, fun l => (vf_iff _).2 ?_⟩
    rintro j j' hjj ⟨h1, h2⟩
    by_cases hj : j.val = 0
    · exact Dn_zero _ j hj h1
    · obtain ⟨i, rfl⟩ : ∃ i : Fin (n + 1), j = i.succ := ⟨⟨j.val - 1, by omega⟩, Fin.ext (by simp; omega)⟩
      obtain ⟨i', rfl⟩ : ∃ i' : Fin (n + 1), j' = i'.succ := ⟨⟨j'.val - 1, by omega⟩, Fin.ext (by simp; omega)⟩
      have hii : i'.val = i.val + 1 := by simp at hjj; omega
      apply (hh.2.2 i i' hii).2.2 l
      refine ⟨?_, ?_⟩
      · rw [hc i]; simp only [Fl, decide_eq_true_eq]; exact h1
      · rw [← es i, ← es i']; exact h2
  · intro f _
    simp only
    exact ofP_toP n f
  · intro h hh
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hh
    have hp : Gd (fun _ => True) (PB B T) (PT U) (n + 1) (fun i => (h i).1) :=
      ⟨fun _ _ => trivial, fun i => hh.2.1 i, fun i j hij => (hh.2.2 i j hij).1⟩
    funext i
    refine Prod.ext ?_ (flags3_consistent B T U n h hh i).symm
    exact congrFun (toP_ofP B T U n _ hp) i

end Flags3

section Flags3Step
variable {K M : ℕ} (U : (Fin K → Fin M) → (Fin K → Fin M) → (Fin K → Fin M) → Prop)
  [∀ a b c, Decidable (U a b c)]

def ynx (y : Yt K M) (c : Fin K → Fin M) : Yt K M :=
  ((y.1.2, c), fun l => y.2 l || decide (c l < y.1.2 l))

def yR (y : Yt K M) (c : Fin K → Fin M) : Prop :=
  U y.1.1 y.1.2 c ∧ ∀ l, ¬ (y.2 l = true ∧ y.1.2 l < c l)

instance : ∀ y c, Decidable (yR U y c) := fun y c => by unfold yR; infer_instance

lemma yT_iff (y z : Yt K M) : YT U y z ↔ z = ynx y (z.1.2) ∧ yR U y (z.1.2) := by
  unfold YT PT ynx yR
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    refine ⟨?_, h2, h4⟩
    obtain ⟨⟨z1, z2⟩, zF⟩ := z
    simp only at h1 h3 ⊢
    rw [← h1]; exact Prod.ext rfl (funext h3)
  · rintro ⟨h1, h2, h4⟩
    refine ⟨⟨?_, h2⟩, fun l => ?_, h4⟩
    · conv_rhs => rw [h1]
    · conv_lhs => rw [h1]

end Flags3Step

end OMA.P_oeis_a224159

namespace OMA.P_oeis_a224159

open Finset OMA.S_oeis_a224159

abbrev St := Fin 3 → Fin 2

def B (s : St) : Prop := True

def T (s t : St) : Prop := (∀ i i' : Fin 3, i'.val = i.val + 1 → t i ≤ s i')

def U (s t v : St) : Prop := (¬ (t 1 < s 0 ∧ t 1 < v 2))

instance : DecidablePred B := fun s => by unfold B; infer_instance
instance : DecidableRel T := fun s t => by unfold T; infer_instance
instance : ∀ s t v, Decidable (U s t v) := fun s t v => by unfold U; infer_instance

abbrev Xs := Yt 3 2
abbrev II : Xs → Prop := YI
abbrev BB : Xs → Prop := YB B T
abbrev TT : Xs → Xs → Prop := YT U

lemma c1_iff (x : Fin 3 → Fin n → Fin 2) : DiagsUnimodal x ↔
    ∀ j j' j'' : Fin n, j'.val = j.val + 1 → j''.val = j'.val + 1 → ¬ (x 1 j' < x 0 j ∧ x 1 j' < x 2 j'') :=
  ⟨fun h j j' j'' h1 h2 => h 0 1 2 j j' j'' (by decide) (by decide) (by simp; omega) (by simp; omega),
    fun h i₁ i₂ i₃ j₁ j₂ j₃ h12 h23 e1 e2 => by
      have a1 := Fin.lt_def.mp h12; have a2 := Fin.lt_def.mp h23; have a3 := i₃.isLt
      obtain rfl : i₁ = 0 := Fin.ext (by simp; omega)
      obtain rfl : i₂ = 1 := Fin.ext (by simp; omega)
      obtain rfl : i₃ = 2 := Fin.ext (by simp; omega)
      simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two] at e1 e2
      exact h j₁ j₂ j₃ (by omega) (by omega)⟩

lemma c2_iff (x : Fin 3 → Fin n → Fin 2) : RowsUnimodal x ↔ ∀ l : Fin 3, VF (fun j => x l j) :=
  Iff.rfl

lemma c3_iff (x : Fin 3 → Fin n → Fin 2) : AntidiagsNondecreasing x ↔
    ∀ j j' : Fin n, j'.val = j.val + 1 → ∀ i i' : Fin 3, i'.val = i.val + 1 → x i j' ≤ x i' j :=
  ⟨fun h j j' hj i i' hi => h i i' j' j hi hj, fun h i i' j j' hi hj => h j' j hj i i' hi⟩

lemma good_iff {n : ℕ} (x : Fin 3 → Fin n → Fin 2) :
    good x ↔ GdV3 B T U n (fun j i => x i j) := by
  unfold good
  rw [c1_iff x, c2_iff x, c3_iff x]
  simp only [GdV3, Gd3, B, T, U, forall_and, imp_and, implies_true, and_true, true_and]
  all_goals tauto

lemma a_eq0 (n : ℕ) : a n = ((univ : Finset (Fin n → St)).filter (GdV3 B T U n)).card := by
  unfold a
  apply Finset.card_nbij' (fun x => fun j i => x i j) (fun f => fun i j => f j i)
  · intro x hx
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hx ⊢
    exact (good_iff x).1 hx
  · intro f hf
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hf ⊢
    exact (good_iff _).2 hf
  · intro x _; rfl
  · intro f _; rfl

lemma aw (k j : ℕ) : a (k + j + 2) = ∑ x, w II BB TT k x * u BB TT j x := by
  rw [a_eq0, card_flags3]; exact total_dual II BB TT k j

lemma hvs (j : ℕ) (x : Xs) : u BB TT j x = vS BB ynx (yR U) j x :=
  u_eq_vS BB TT (fun y => y.1.2) ynx (yR U) (fun _ _ => rfl) (yT_iff U) j x

def idx1 (s : St) : ℕ := (s 0).val + 2 * (s 1).val + 4 * (s 2).val

def idx (x : Xs) : ℕ := idx1 x.1.1 * 8 + idx1 x.1.2 + 64 * ((if x.2 0 then 1 else 0) + 2 * (if x.2 1 then 1 else 0) + 4 * (if x.2 2 then 1 else 0))

def tb (L : List ℕ) (s : Xs) : ℕ := L.getD (idx s) 0

def T1 : List ℕ := [2, 2, 4, 4, 4, 4, 8, 8, 1, 1, 4, 4, 2, 2, 8, 8, 2, 2, 4, 4, 4, 4, 8, 8, 1, 1, 4, 4, 2, 2, 8, 8, 2, 2, 4, 4, 4, 4, 8, 8, 1, 1, 4, 4, 2, 2, 8, 8, 2, 2, 4, 4, 4, 4, 8, 8, 1, 1, 4, 4, 2, 2, 8, 8, 2, 2, 2, 4, 4, 4, 4, 8, 1, 1, 2, 4, 2, 2, 4, 8, 2, 2, 2, 4, 4, 4, 4, 8, 1, 1, 2, 4, 2, 2, 4, 8, 2, 2, 2, 4, 4, 4, 4, 8, 1, 1, 2, 4, 2, 2, 4, 8, 2, 2, 2, 4, 4, 4, 4, 8, 1, 1, 2, 4, 2, 2, 4, 8, 2, 2, 4, 4, 2, 2, 8, 8, 1, 1, 4, 4, 1, 1, 8, 8, 2, 2, 4, 4, 2, 2, 8, 8, 1, 1, 4, 4, 1, 1, 8, 8, 2, 2, 4, 4, 2, 2, 8, 8, 1, 1, 4, 4, 1, 1, 8, 8, 2, 2, 4, 4, 2, 2, 8, 8, 1, 1, 4, 4, 1, 1, 8, 8, 2, 2, 2, 4, 2, 2, 4, 8, 1, 1, 2, 4, 1, 1, 4, 8, 2, 2, 2, 4, 2, 2, 4, 8, 1, 1, 2, 4, 1, 1, 4, 8, 2, 2, 2, 4, 2, 2, 4, 8, 1, 1, 2, 4, 1, 1, 4, 8, 2, 2, 2, 4, 2, 2, 4, 8, 1, 1, 2, 4, 1, 1, 4, 8, 1, 1, 2, 2, 4, 4, 8, 8, 1, 1, 2, 2, 2, 2, 8, 8, 1, 1, 2, 2, 4, 4, 8, 8, 1, 1, 2, 2, 2, 2, 8, 8, 1, 1, 2, 2, 4, 4, 8, 8, 1, 1, 2, 2, 2, 2, 8, 8, 1, 1, 2, 2, 4, 4, 8, 8, 1, 1, 2, 2, 2, 2, 8, 8, 1, 1, 1, 2, 4, 4, 4, 8, 1, 1, 1, 2, 2, 2, 4, 8, 1, 1, 1, 2, 4, 4, 4, 8, 1, 1, 1, 2, 2, 2, 4, 8, 1, 1, 1, 2, 4, 4, 4, 8, 1, 1, 1, 2, 2, 2, 4, 8, 1, 1, 1, 2, 4, 4, 4, 8, 1, 1, 1, 2, 2, 2, 4, 8, 1, 1, 2, 2, 2, 2, 8, 8, 1, 1, 2, 2, 1, 1, 8, 8, 1, 1, 2, 2, 2, 2, 8, 8, 1, 1, 2, 2, 1, 1, 8, 8, 1, 1, 2, 2, 2, 2, 8, 8, 1, 1, 2, 2, 1, 1, 8, 8, 1, 1, 2, 2, 2, 2, 8, 8, 1, 1, 2, 2, 1, 1, 8, 8, 1, 1, 1, 2, 2, 2, 4, 8, 1, 1, 1, 2, 1, 1, 4, 8, 1, 1, 1, 2, 2, 2, 4, 8, 1, 1, 1, 2, 1, 1, 4, 8, 1, 1, 1, 2, 2, 2, 4, 8, 1, 1, 1, 2, 1, 1, 4, 8, 1, 1, 1, 2, 2, 2, 4, 8, 1, 1, 1, 2, 1, 1, 4, 8]
def T2 : List ℕ := [6, 3, 8, 4, 15, 8, 26, 19, 2, 1, 8, 4, 3, 2, 26, 19, 6, 3, 8, 4, 15, 8, 26, 19, 2, 1, 8, 4, 3, 2, 26, 19, 6, 3, 8, 4, 15, 8, 26, 19, 2, 1, 8, 4, 3, 2, 26, 19, 6, 3, 8, 4, 15, 8, 26, 19, 2, 1, 8, 4, 3, 2, 26, 19, 6, 3, 4, 4, 10, 8, 8, 19, 2, 1, 4, 4, 2, 2, 8, 19, 6, 3, 4, 4, 10, 8, 8, 19, 2, 1, 4, 4, 2, 2, 8, 19, 6, 3, 4, 4, 10, 8, 8, 19, 2, 1, 4, 4, 2, 2, 8, 19, 6, 3, 4, 4, 10, 8, 8, 19, 2, 1, 4, 4, 2, 2, 8, 19, 4, 2, 8, 4, 3, 2, 26, 19, 2, 1, 8, 4, 1, 1, 26, 19, 4, 2, 8, 4, 3, 2, 26, 19, 2, 1, 8, 4, 1, 1, 26, 19, 4, 2, 8, 4, 3, 2, 26, 19, 2, 1, 8, 4, 1, 1, 26, 19, 4, 2, 8, 4, 3, 2, 26, 19, 2, 1, 8, 4, 1, 1, 26, 19, 4, 2, 4, 4, 3, 2, 8, 19, 2, 1, 4, 4, 1, 1, 8, 19, 4, 2, 4, 4, 3, 2, 8, 19, 2, 1, 4, 4, 1, 1, 8, 19, 4, 2, 4, 4, 3, 2, 8, 19, 2, 1, 4, 4, 1, 1, 8, 19, 4, 2, 4, 4, 3, 2, 8, 19, 2, 1, 4, 4, 1, 1, 8, 19, 1, 1, 2, 2, 15, 8, 26, 19, 1, 1, 2, 2, 3, 2, 26, 19, 1, 1, 2, 2, 15, 8, 26, 19, 1, 1, 2, 2, 3, 2, 26, 19, 1, 1, 2, 2, 15, 8, 26, 19, 1, 1, 2, 2, 3, 2, 26, 19, 1, 1, 2, 2, 15, 8, 26, 19, 1, 1, 2, 2, 3, 2, 26, 19, 1, 1, 1, 2, 10, 8, 8, 19, 1, 1, 1, 2, 2, 2, 8, 19, 1, 1, 1, 2, 10, 8, 8, 19, 1, 1, 1, 2, 2, 2, 8, 19, 1, 1, 1, 2, 10, 8, 8, 19, 1, 1, 1, 2, 2, 2, 8, 19, 1, 1, 1, 2, 10, 8, 8, 19, 1, 1, 1, 2, 2, 2, 8, 19, 1, 1, 2, 2, 3, 2, 26, 19, 1, 1, 2, 2, 1, 1, 26, 19, 1, 1, 2, 2, 3, 2, 26, 19, 1, 1, 2, 2, 1, 1, 26, 19, 1, 1, 2, 2, 3, 2, 26, 19, 1, 1, 2, 2, 1, 1, 26, 19, 1, 1, 2, 2, 3, 2, 26, 19, 1, 1, 2, 2, 1, 1, 26, 19, 1, 1, 1, 2, 3, 2, 8, 19, 1, 1, 1, 2, 1, 1, 8, 19, 1, 1, 1, 2, 3, 2, 8, 19, 1, 1, 1, 2, 1, 1, 8, 19, 1, 1, 1, 2, 3, 2, 8, 19, 1, 1, 1, 2, 1, 1, 8, 19, 1, 1, 1, 2, 3, 2, 8, 19, 1, 1, 1, 2, 1, 1, 8, 19]
def T3 : List ℕ := [21, 4, 11, 5, 44, 12, 56, 34, 6, 2, 11, 5, 3, 2, 56, 34, 21, 4, 11, 5, 44, 12, 56, 34, 6, 2, 11, 5, 3, 2, 56, 34, 21, 4, 11, 5, 44, 12, 56, 34, 6, 2, 11, 5, 3, 2, 56, 34, 21, 4, 11, 5, 44, 12, 56, 34, 6, 2, 11, 5, 3, 2, 56, 34, 16, 4, 7, 5, 20, 12, 13, 34, 6, 2, 7, 5, 2, 2, 13, 34, 16, 4, 7, 5, 20, 12, 13, 34, 6, 2, 7, 5, 2, 2, 13, 34, 16, 4, 7, 5, 20, 12, 13, 34, 6, 2, 7, 5, 2, 2, 13, 34, 16, 4, 7, 5, 20, 12, 13, 34, 6, 2, 7, 5, 2, 2, 13, 34, 7, 3, 11, 5, 4, 2, 56, 34, 4, 2, 11, 5, 1, 1, 56, 34, 7, 3, 11, 5, 4, 2, 56, 34, 4, 2, 11, 5, 1, 1, 56, 34, 7, 3, 11, 5, 4, 2, 56, 34, 4, 2, 11, 5, 1, 1, 56, 34, 7, 3, 11, 5, 4, 2, 56, 34, 4, 2, 11, 5, 1, 1, 56, 34, 7, 3, 7, 5, 4, 2, 13, 34, 4, 2, 7, 5, 1, 1, 13, 34, 7, 3, 7, 5, 4, 2, 13, 34, 4, 2, 7, 5, 1, 1, 13, 34, 7, 3, 7, 5, 4, 2, 13, 34, 4, 2, 7, 5, 1, 1, 13, 34, 7, 3, 7, 5, 4, 2, 13, 34, 4, 2, 7, 5, 1, 1, 13, 34, 1, 1, 2, 2, 44, 12, 56, 34, 1, 1, 2, 2, 3, 2, 56, 34, 1, 1, 2, 2, 44, 12, 56, 34, 1, 1, 2, 2, 3, 2, 56, 34, 1, 1, 2, 2, 44, 12, 56, 34, 1, 1, 2, 2, 3, 2, 56, 34, 1, 1, 2, 2, 44, 12, 56, 34, 1, 1, 2, 2, 3, 2, 56, 34, 1, 1, 1, 2, 20, 12, 13, 34, 1, 1, 1, 2, 2, 2, 13, 34, 1, 1, 1, 2, 20, 12, 13, 34, 1, 1, 1, 2, 2, 2, 13, 34, 1, 1, 1, 2, 20, 12, 13, 34, 1, 1, 1, 2, 2, 2, 13, 34, 1, 1, 1, 2, 20, 12, 13, 34, 1, 1, 1, 2, 2, 2, 13, 34, 1, 1, 2, 2, 4, 2, 56, 34, 1, 1, 2, 2, 1, 1, 56, 34, 1, 1, 2, 2, 4, 2, 56, 34, 1, 1, 2, 2, 1, 1, 56, 34, 1, 1, 2, 2, 4, 2, 56, 34, 1, 1, 2, 2, 1, 1, 56, 34, 1, 1, 2, 2, 4, 2, 56, 34, 1, 1, 2, 2, 1, 1, 56, 34, 1, 1, 1, 2, 4, 2, 13, 34, 1, 1, 1, 2, 1, 1, 13, 34, 1, 1, 1, 2, 4, 2, 13, 34, 1, 1, 1, 2, 1, 1, 13, 34, 1, 1, 1, 2, 4, 2, 13, 34, 1, 1, 1, 2, 1, 1, 13, 34, 1, 1, 1, 2, 4, 2, 13, 34, 1, 1, 1, 2, 1, 1, 13, 34]
def T4 : List ℕ := [65, 8, 16, 8, 103, 17, 102, 54, 21, 6, 16, 8, 3, 2, 102, 54, 65, 8, 16, 8, 103, 17, 102, 54, 21, 6, 16, 8, 3, 2, 102, 54, 65, 8, 16, 8, 103, 17, 102, 54, 21, 6, 16, 8, 3, 2, 102, 54, 65, 8, 16, 8, 103, 17, 102, 54, 21, 6, 16, 8, 3, 2, 102, 54, 36, 8, 11, 8, 35, 17, 19, 54, 16, 6, 11, 8, 2, 2, 19, 54, 36, 8, 11, 8, 35, 17, 19, 54, 16, 6, 11, 8, 2, 2, 19, 54, 36, 8, 11, 8, 35, 17, 19, 54, 16, 6, 11, 8, 2, 2, 19, 54, 36, 8, 11, 8, 35, 17, 19, 54, 16, 6, 11, 8, 2, 2, 19, 54, 11, 5, 16, 8, 5, 2, 102, 54, 7, 4, 16, 8, 1, 1, 102, 54, 11, 5, 16, 8, 5, 2, 102, 54, 7, 4, 16, 8, 1, 1, 102, 54, 11, 5, 16, 8, 5, 2, 102, 54, 7, 4, 16, 8, 1, 1, 102, 54, 11, 5, 16, 8, 5, 2, 102, 54, 7, 4, 16, 8, 1, 1, 102, 54, 11, 5, 11, 8, 5, 2, 19, 54, 7, 4, 11, 8, 1, 1, 19, 54, 11, 5, 11, 8, 5, 2, 19, 54, 7, 4, 11, 8, 1, 1, 19, 54, 11, 5, 11, 8, 5, 2, 19, 54, 7, 4, 11, 8, 1, 1, 19, 54, 11, 5, 11, 8, 5, 2, 19, 54, 7, 4, 11, 8, 1, 1, 19, 54, 1, 1, 2, 2, 103, 17, 102, 54, 1, 1, 2, 2, 3, 2, 102, 54, 1, 1, 2, 2, 103, 17, 102, 54, 1, 1, 2, 2, 3, 2, 102, 54, 1, 1, 2, 2, 103, 17, 102, 54, 1, 1, 2, 2, 3, 2, 102, 54, 1, 1, 2, 2, 103, 17, 102, 54, 1, 1, 2, 2, 3, 2, 102, 54, 1, 1, 1, 2, 35, 17, 19, 54, 1, 1, 1, 2, 2, 2, 19, 54, 1, 1, 1, 2, 35, 17, 19, 54, 1, 1, 1, 2, 2, 2, 19, 54, 1, 1, 1, 2, 35, 17, 19, 54, 1, 1, 1, 2, 2, 2, 19, 54, 1, 1, 1, 2, 35, 17, 19, 54, 1, 1, 1, 2, 2, 2, 19, 54, 1, 1, 2, 2, 5, 2, 102, 54, 1, 1, 2, 2, 1, 1, 102, 54, 1, 1, 2, 2, 5, 2, 102, 54, 1, 1, 2, 2, 1, 1, 102, 54, 1, 1, 2, 2, 5, 2, 102, 54, 1, 1, 2, 2, 1, 1, 102, 54, 1, 1, 2, 2, 5, 2, 102, 54, 1, 1, 2, 2, 1, 1, 102, 54, 1, 1, 1, 2, 5, 2, 19, 54, 1, 1, 1, 2, 1, 1, 19, 54, 1, 1, 1, 2, 5, 2, 19, 54, 1, 1, 1, 2, 1, 1, 19, 54, 1, 1, 1, 2, 5, 2, 19, 54, 1, 1, 1, 2, 1, 1, 19, 54, 1, 1, 1, 2, 5, 2, 19, 54, 1, 1, 1, 2, 1, 1, 19, 54]
def T5 : List ℕ := [168, 18, 23, 13, 208, 23, 169, 80, 65, 16, 23, 13, 3, 2, 169, 80, 168, 18, 23, 13, 208, 23, 169, 80, 65, 16, 23, 13, 3, 2, 169, 80, 168, 18, 23, 13, 208, 23, 169, 80, 65, 16, 23, 13, 3, 2, 169, 80, 168, 18, 23, 13, 208, 23, 169, 80, 65, 16, 23, 13, 3, 2, 169, 80, 71, 18, 16, 13, 56, 23, 26, 80, 36, 16, 16, 13, 2, 2, 26, 80, 71, 18, 16, 13, 56, 23, 26, 80, 36, 16, 16, 13, 2, 2, 26, 80, 71, 18, 16, 13, 56, 23, 26, 80, 36, 16, 16, 13, 2, 2, 26, 80, 71, 18, 16, 13, 56, 23, 26, 80, 36, 16, 16, 13, 2, 2, 26, 80, 16, 8, 23, 13, 6, 2, 169, 80, 11, 7, 23, 13, 1, 1, 169, 80, 16, 8, 23, 13, 6, 2, 169, 80, 11, 7, 23, 13, 1, 1, 169, 80, 16, 8, 23, 13, 6, 2, 169, 80, 11, 7, 23, 13, 1, 1, 169, 80, 16, 8, 23, 13, 6, 2, 169, 80, 11, 7, 23, 13, 1, 1, 169, 80, 16, 8, 16, 13, 6, 2, 26, 80, 11, 7, 16, 13, 1, 1, 26, 80, 16, 8, 16, 13, 6, 2, 26, 80, 11, 7, 16, 13, 1, 1, 26, 80, 16, 8, 16, 13, 6, 2, 26, 80, 11, 7, 16, 13, 1, 1, 26, 80, 16, 8, 16, 13, 6, 2, 26, 80, 11, 7, 16, 13, 1, 1, 26, 80, 1, 1, 2, 2, 208, 23, 169, 80, 1, 1, 2, 2, 3, 2, 169, 80, 1, 1, 2, 2, 208, 23, 169, 80, 1, 1, 2, 2, 3, 2, 169, 80, 1, 1, 2, 2, 208, 23, 169, 80, 1, 1, 2, 2, 3, 2, 169, 80, 1, 1, 2, 2, 208, 23, 169, 80, 1, 1, 2, 2, 3, 2, 169, 80, 1, 1, 1, 2, 56, 23, 26, 80, 1, 1, 1, 2, 2, 2, 26, 80, 1, 1, 1, 2, 56, 23, 26, 80, 1, 1, 1, 2, 2, 2, 26, 80, 1, 1, 1, 2, 56, 23, 26, 80, 1, 1, 1, 2, 2, 2, 26, 80, 1, 1, 1, 2, 56, 23, 26, 80, 1, 1, 1, 2, 2, 2, 26, 80, 1, 1, 2, 2, 6, 2, 169, 80, 1, 1, 2, 2, 1, 1, 169, 80, 1, 1, 2, 2, 6, 2, 169, 80, 1, 1, 2, 2, 1, 1, 169, 80, 1, 1, 2, 2, 6, 2, 169, 80, 1, 1, 2, 2, 1, 1, 169, 80, 1, 1, 2, 2, 6, 2, 169, 80, 1, 1, 2, 2, 1, 1, 169, 80, 1, 1, 1, 2, 6, 2, 26, 80, 1, 1, 1, 2, 1, 1, 26, 80, 1, 1, 1, 2, 6, 2, 26, 80, 1, 1, 1, 2, 1, 1, 26, 80, 1, 1, 1, 2, 6, 2, 26, 80, 1, 1, 1, 2, 1, 1, 26, 80, 1, 1, 1, 2, 6, 2, 26, 80, 1, 1, 1, 2, 1, 1, 26, 80]
def T6 : List ℕ := [376, 38, 32, 20, 380, 30, 263, 113, 168, 36, 32, 20, 3, 2, 263, 113, 376, 38, 32, 20, 380, 30, 263, 113, 168, 36, 32, 20, 3, 2, 263, 113, 376, 38, 32, 20, 380, 30, 263, 113, 168, 36, 32, 20, 3, 2, 263, 113, 376, 38, 32, 20, 380, 30, 263, 113, 168, 36, 32, 20, 3, 2, 263, 113, 127, 38, 22, 20, 84, 30, 34, 113, 71, 36, 22, 20, 2, 2, 34, 113, 127, 38, 22, 20, 84, 30, 34, 113, 71, 36, 22, 20, 2, 2, 34, 113, 127, 38, 22, 20, 84, 30, 34, 113, 71, 36, 22, 20, 2, 2, 34, 113, 127, 38, 22, 20, 84, 30, 34, 113, 71, 36, 22, 20, 2, 2, 34, 113, 22, 12, 32, 20, 7, 2, 263, 113, 16, 11, 32, 20, 1, 1, 263, 113, 22, 12, 32, 20, 7, 2, 263, 113, 16, 11, 32, 20, 1, 1, 263, 113, 22, 12, 32, 20, 7, 2, 263, 113, 16, 11, 32, 20, 1, 1, 263, 113, 22, 12, 32, 20, 7, 2, 263, 113, 16, 11, 32, 20, 1, 1, 263, 113, 22, 12, 22, 20, 7, 2, 34, 113, 16, 11, 22, 20, 1, 1, 34, 113, 22, 12, 22, 20, 7, 2, 34, 113, 16, 11, 22, 20, 1, 1, 34, 113, 22, 12, 22, 20, 7, 2, 34, 113, 16, 11, 22, 20, 1, 1, 34, 113, 22, 12, 22, 20, 7, 2, 34, 113, 16, 11, 22, 20, 1, 1, 34, 113, 1, 1, 2, 2, 380, 30, 263, 113, 1, 1, 2, 2, 3, 2, 263, 113, 1, 1, 2, 2, 380, 30, 263, 113, 1, 1, 2, 2, 3, 2, 263, 113, 1, 1, 2, 2, 380, 30, 263, 113, 1, 1, 2, 2, 3, 2, 263, 113, 1, 1, 2, 2, 380, 30, 263, 113, 1, 1, 2, 2, 3, 2, 263, 113, 1, 1, 1, 2, 84, 30, 34, 113, 1, 1, 1, 2, 2, 2, 34, 113, 1, 1, 1, 2, 84, 30, 34, 113, 1, 1, 1, 2, 2, 2, 34, 113, 1, 1, 1, 2, 84, 30, 34, 113, 1, 1, 1, 2, 2, 2, 34, 113, 1, 1, 1, 2, 84, 30, 34, 113, 1, 1, 1, 2, 2, 2, 34, 113, 1, 1, 2, 2, 7, 2, 263, 113, 1, 1, 2, 2, 1, 1, 263, 113, 1, 1, 2, 2, 7, 2, 263, 113, 1, 1, 2, 2, 1, 1, 263, 113, 1, 1, 2, 2, 7, 2, 263, 113, 1, 1, 2, 2, 1, 1, 263, 113, 1, 1, 2, 2, 7, 2, 263, 113, 1, 1, 2, 2, 1, 1, 263, 113, 1, 1, 1, 2, 7, 2, 34, 113, 1, 1, 1, 2, 1, 1, 34, 113, 1, 1, 1, 2, 7, 2, 34, 113, 1, 1, 1, 2, 1, 1, 34, 113, 1, 1, 1, 2, 7, 2, 34, 113, 1, 1, 1, 2, 1, 1, 34, 113, 1, 1, 1, 2, 7, 2, 34, 113, 1, 1, 1, 2, 1, 1, 34, 113]
def T7 : List ℕ := [756, 73, 43, 29, 646, 38, 391, 154, 376, 71, 43, 29, 3, 2, 391, 154, 756, 73, 43, 29, 646, 38, 391, 154, 376, 71, 43, 29, 3, 2, 391, 154, 756, 73, 43, 29, 646, 38, 391, 154, 376, 71, 43, 29, 3, 2, 391, 154, 756, 73, 43, 29, 646, 38, 391, 154, 376, 71, 43, 29, 3, 2, 391, 154, 211, 73, 29, 29, 120, 38, 43, 154, 127, 71, 29, 29, 2, 2, 43, 154, 211, 73, 29, 29, 120, 38, 43, 154, 127, 71, 29, 29, 2, 2, 43, 154, 211, 73, 29, 29, 120, 38, 43, 154, 127, 71, 29, 29, 2, 2, 43, 154, 211, 73, 29, 29, 120, 38, 43, 154, 127, 71, 29, 29, 2, 2, 43, 154, 29, 17, 43, 29, 8, 2, 391, 154, 22, 16, 43, 29, 1, 1, 391, 154, 29, 17, 43, 29, 8, 2, 391, 154, 22, 16, 43, 29, 1, 1, 391, 154, 29, 17, 43, 29, 8, 2, 391, 154, 22, 16, 43, 29, 1, 1, 391, 154, 29, 17, 43, 29, 8, 2, 391, 154, 22, 16, 43, 29, 1, 1, 391, 154, 29, 17, 29, 29, 8, 2, 43, 154, 22, 16, 29, 29, 1, 1, 43, 154, 29, 17, 29, 29, 8, 2, 43, 154, 22, 16, 29, 29, 1, 1, 43, 154, 29, 17, 29, 29, 8, 2, 43, 154, 22, 16, 29, 29, 1, 1, 43, 154, 29, 17, 29, 29, 8, 2, 43, 154, 22, 16, 29, 29, 1, 1, 43, 154, 1, 1, 2, 2, 646, 38, 391, 154, 1, 1, 2, 2, 3, 2, 391, 154, 1, 1, 2, 2, 646, 38, 391, 154, 1, 1, 2, 2, 3, 2, 391, 154, 1, 1, 2, 2, 646, 38, 391, 154, 1, 1, 2, 2, 3, 2, 391, 154, 1, 1, 2, 2, 646, 38, 391, 154, 1, 1, 2, 2, 3, 2, 391, 154, 1, 1, 1, 2, 120, 38, 43, 154, 1, 1, 1, 2, 2, 2, 43, 154, 1, 1, 1, 2, 120, 38, 43, 154, 1, 1, 1, 2, 2, 2, 43, 154, 1, 1, 1, 2, 120, 38, 43, 154, 1, 1, 1, 2, 2, 2, 43, 154, 1, 1, 1, 2, 120, 38, 43, 154, 1, 1, 1, 2, 2, 2, 43, 154, 1, 1, 2, 2, 8, 2, 391, 154, 1, 1, 2, 2, 1, 1, 391, 154, 1, 1, 2, 2, 8, 2, 391, 154, 1, 1, 2, 2, 1, 1, 391, 154, 1, 1, 2, 2, 8, 2, 391, 154, 1, 1, 2, 2, 1, 1, 391, 154, 1, 1, 2, 2, 8, 2, 391, 154, 1, 1, 2, 2, 1, 1, 391, 154, 1, 1, 1, 2, 8, 2, 43, 154, 1, 1, 1, 2, 1, 1, 43, 154, 1, 1, 1, 2, 8, 2, 43, 154, 1, 1, 1, 2, 1, 1, 43, 154, 1, 1, 1, 2, 8, 2, 43, 154, 1, 1, 1, 2, 1, 1, 43, 154, 1, 1, 1, 2, 8, 2, 43, 154, 1, 1, 1, 2, 1, 1, 43, 154]
def T8 : List ℕ := [1402, 129, 56, 40, 1040, 47, 561, 204, 756, 127, 56, 40, 3, 2, 561, 204, 1402, 129, 56, 40, 1040, 47, 561, 204, 756, 127, 56, 40, 3, 2, 561, 204, 1402, 129, 56, 40, 1040, 47, 561, 204, 756, 127, 56, 40, 3, 2, 561, 204, 1402, 129, 56, 40, 1040, 47, 561, 204, 756, 127, 56, 40, 3, 2, 561, 204, 331, 129, 37, 40, 165, 47, 53, 204, 211, 127, 37, 40, 2, 2, 53, 204, 331, 129, 37, 40, 165, 47, 53, 204, 211, 127, 37, 40, 2, 2, 53, 204, 331, 129, 37, 40, 165, 47, 53, 204, 211, 127, 37, 40, 2, 2, 53, 204, 331, 129, 37, 40, 165, 47, 53, 204, 211, 127, 37, 40, 2, 2, 53, 204, 37, 23, 56, 40, 9, 2, 561, 204, 29, 22, 56, 40, 1, 1, 561, 204, 37, 23, 56, 40, 9, 2, 561, 204, 29, 22, 56, 40, 1, 1, 561, 204, 37, 23, 56, 40, 9, 2, 561, 204, 29, 22, 56, 40, 1, 1, 561, 204, 37, 23, 56, 40, 9, 2, 561, 204, 29, 22, 56, 40, 1, 1, 561, 204, 37, 23, 37, 40, 9, 2, 53, 204, 29, 22, 37, 40, 1, 1, 53, 204, 37, 23, 37, 40, 9, 2, 53, 204, 29, 22, 37, 40, 1, 1, 53, 204, 37, 23, 37, 40, 9, 2, 53, 204, 29, 22, 37, 40, 1, 1, 53, 204, 37, 23, 37, 40, 9, 2, 53, 204, 29, 22, 37, 40, 1, 1, 53, 204, 1, 1, 2, 2, 1040, 47, 561, 204, 1, 1, 2, 2, 3, 2, 561, 204, 1, 1, 2, 2, 1040, 47, 561, 204, 1, 1, 2, 2, 3, 2, 561, 204, 1, 1, 2, 2, 1040, 47, 561, 204, 1, 1, 2, 2, 3, 2, 561, 204, 1, 1, 2, 2, 1040, 47, 561, 204, 1, 1, 2, 2, 3, 2, 561, 204, 1, 1, 1, 2, 165, 47, 53, 204, 1, 1, 1, 2, 2, 2, 53, 204, 1, 1, 1, 2, 165, 47, 53, 204, 1, 1, 1, 2, 2, 2, 53, 204, 1, 1, 1, 2, 165, 47, 53, 204, 1, 1, 1, 2, 2, 2, 53, 204, 1, 1, 1, 2, 165, 47, 53, 204, 1, 1, 1, 2, 2, 2, 53, 204, 1, 1, 2, 2, 9, 2, 561, 204, 1, 1, 2, 2, 1, 1, 561, 204, 1, 1, 2, 2, 9, 2, 561, 204, 1, 1, 2, 2, 1, 1, 561, 204, 1, 1, 2, 2, 9, 2, 561, 204, 1, 1, 2, 2, 1, 1, 561, 204, 1, 1, 2, 2, 9, 2, 561, 204, 1, 1, 2, 2, 1, 1, 561, 204, 1, 1, 1, 2, 9, 2, 53, 204, 1, 1, 1, 2, 1, 1, 53, 204, 1, 1, 1, 2, 9, 2, 53, 204, 1, 1, 1, 2, 1, 1, 53, 204, 1, 1, 1, 2, 9, 2, 53, 204, 1, 1, 1, 2, 1, 1, 53, 204, 1, 1, 1, 2, 9, 2, 53, 204, 1, 1, 1, 2, 1, 1, 53, 204]
def T9 : List ℕ := [2442, 213, 71, 53, 1604, 57, 782, 264, 1402, 211, 71, 53, 3, 2, 782, 264, 2442, 213, 71, 53, 1604, 57, 782, 264, 1402, 211, 71, 53, 3, 2, 782, 264, 2442, 213, 71, 53, 1604, 57, 782, 264, 1402, 211, 71, 53, 3, 2, 782, 264, 2442, 213, 71, 53, 1604, 57, 782, 264, 1402, 211, 71, 53, 3, 2, 782, 264, 496, 213, 46, 53, 220, 57, 64, 264, 331, 211, 46, 53, 2, 2, 64, 264, 496, 213, 46, 53, 220, 57, 64, 264, 331, 211, 46, 53, 2, 2, 64, 264, 496, 213, 46, 53, 220, 57, 64, 264, 331, 211, 46, 53, 2, 2, 64, 264, 496, 213, 46, 53, 220, 57, 64, 264, 331, 211, 46, 53, 2, 2, 64, 264, 46, 30, 71, 53, 10, 2, 782, 264, 37, 29, 71, 53, 1, 1, 782, 264, 46, 30, 71, 53, 10, 2, 782, 264, 37, 29, 71, 53, 1, 1, 782, 264, 46, 30, 71, 53, 10, 2, 782, 264, 37, 29, 71, 53, 1, 1, 782, 264, 46, 30, 71, 53, 10, 2, 782, 264, 37, 29, 71, 53, 1, 1, 782, 264, 46, 30, 46, 53, 10, 2, 64, 264, 37, 29, 46, 53, 1, 1, 64, 264, 46, 30, 46, 53, 10, 2, 64, 264, 37, 29, 46, 53, 1, 1, 64, 264, 46, 30, 46, 53, 10, 2, 64, 264, 37, 29, 46, 53, 1, 1, 64, 264, 46, 30, 46, 53, 10, 2, 64, 264, 37, 29, 46, 53, 1, 1, 64, 264, 1, 1, 2, 2, 1604, 57, 782, 264, 1, 1, 2, 2, 3, 2, 782, 264, 1, 1, 2, 2, 1604, 57, 782, 264, 1, 1, 2, 2, 3, 2, 782, 264, 1, 1, 2, 2, 1604, 57, 782, 264, 1, 1, 2, 2, 3, 2, 782, 264, 1, 1, 2, 2, 1604, 57, 782, 264, 1, 1, 2, 2, 3, 2, 782, 264, 1, 1, 1, 2, 220, 57, 64, 264, 1, 1, 1, 2, 2, 2, 64, 264, 1, 1, 1, 2, 220, 57, 64, 264, 1, 1, 1, 2, 2, 2, 64, 264, 1, 1, 1, 2, 220, 57, 64, 264, 1, 1, 1, 2, 2, 2, 64, 264, 1, 1, 1, 2, 220, 57, 64, 264, 1, 1, 1, 2, 2, 2, 64, 264, 1, 1, 2, 2, 10, 2, 782, 264, 1, 1, 2, 2, 1, 1, 782, 264, 1, 1, 2, 2, 10, 2, 782, 264, 1, 1, 2, 2, 1, 1, 782, 264, 1, 1, 2, 2, 10, 2, 782, 264, 1, 1, 2, 2, 1, 1, 782, 264, 1, 1, 2, 2, 10, 2, 782, 264, 1, 1, 2, 2, 1, 1, 782, 264, 1, 1, 1, 2, 10, 2, 64, 264, 1, 1, 1, 2, 1, 1, 64, 264, 1, 1, 1, 2, 10, 2, 64, 264, 1, 1, 1, 2, 1, 1, 64, 264, 1, 1, 1, 2, 10, 2, 64, 264, 1, 1, 1, 2, 1, 1, 64, 264, 1, 1, 1, 2, 10, 2, 64, 264, 1, 1, 1, 2, 1, 1, 64, 264]

set_option maxRecDepth 100000 in
lemma hs1 : ∀ x : Xs, (∑ t : St, if BB (ynx x t) ∧ yR U x t then 1 else 0) = tb T1 x := by
  decide +kernel

lemma hu1 (x : Xs) : u BB TT 1 x = tb T1 x := by
  rw [hvs]; exact hs1 x

lemma hv1 (x : Xs) : vS BB ynx (yR U) 1 x = tb T1 x := by
  rw [← hvs]; exact hu1 x

set_option maxRecDepth 100000 in
lemma hs2 : ∀ x : Xs, (∑ t : St, if BB (ynx x t) ∧ yR U x t then tb T1 (ynx x t) else 0) = tb T2 x := by
  decide +kernel

lemma hv2 (x : Xs) : vS BB ynx (yR U) 2 x = tb T2 x := by
  show (∑ t, if BB (ynx x t) ∧ yR U x t then vS BB ynx (yR U) 1 (ynx x t) else 0) = _
  simp only [hv1]; exact hs2 x

lemma hu2 (x : Xs) : u BB TT 2 x = tb T2 x := by
  rw [hvs]; exact hv2 x

set_option maxRecDepth 100000 in
lemma hs3 : ∀ x : Xs, (∑ t : St, if BB (ynx x t) ∧ yR U x t then tb T2 (ynx x t) else 0) = tb T3 x := by
  decide +kernel

lemma hv3 (x : Xs) : vS BB ynx (yR U) 3 x = tb T3 x := by
  show (∑ t, if BB (ynx x t) ∧ yR U x t then vS BB ynx (yR U) 2 (ynx x t) else 0) = _
  simp only [hv2]; exact hs3 x

lemma hu3 (x : Xs) : u BB TT 3 x = tb T3 x := by
  rw [hvs]; exact hv3 x

set_option maxRecDepth 100000 in
lemma hs4 : ∀ x : Xs, (∑ t : St, if BB (ynx x t) ∧ yR U x t then tb T3 (ynx x t) else 0) = tb T4 x := by
  decide +kernel

lemma hv4 (x : Xs) : vS BB ynx (yR U) 4 x = tb T4 x := by
  show (∑ t, if BB (ynx x t) ∧ yR U x t then vS BB ynx (yR U) 3 (ynx x t) else 0) = _
  simp only [hv3]; exact hs4 x

lemma hu4 (x : Xs) : u BB TT 4 x = tb T4 x := by
  rw [hvs]; exact hv4 x

set_option maxRecDepth 100000 in
lemma hs5 : ∀ x : Xs, (∑ t : St, if BB (ynx x t) ∧ yR U x t then tb T4 (ynx x t) else 0) = tb T5 x := by
  decide +kernel

lemma hv5 (x : Xs) : vS BB ynx (yR U) 5 x = tb T5 x := by
  show (∑ t, if BB (ynx x t) ∧ yR U x t then vS BB ynx (yR U) 4 (ynx x t) else 0) = _
  simp only [hv4]; exact hs5 x

lemma hu5 (x : Xs) : u BB TT 5 x = tb T5 x := by
  rw [hvs]; exact hv5 x

set_option maxRecDepth 100000 in
lemma hs6 : ∀ x : Xs, (∑ t : St, if BB (ynx x t) ∧ yR U x t then tb T5 (ynx x t) else 0) = tb T6 x := by
  decide +kernel

lemma hv6 (x : Xs) : vS BB ynx (yR U) 6 x = tb T6 x := by
  show (∑ t, if BB (ynx x t) ∧ yR U x t then vS BB ynx (yR U) 5 (ynx x t) else 0) = _
  simp only [hv5]; exact hs6 x

lemma hu6 (x : Xs) : u BB TT 6 x = tb T6 x := by
  rw [hvs]; exact hv6 x

set_option maxRecDepth 100000 in
lemma hs7 : ∀ x : Xs, (∑ t : St, if BB (ynx x t) ∧ yR U x t then tb T6 (ynx x t) else 0) = tb T7 x := by
  decide +kernel

lemma hv7 (x : Xs) : vS BB ynx (yR U) 7 x = tb T7 x := by
  show (∑ t, if BB (ynx x t) ∧ yR U x t then vS BB ynx (yR U) 6 (ynx x t) else 0) = _
  simp only [hv6]; exact hs7 x

lemma hu7 (x : Xs) : u BB TT 7 x = tb T7 x := by
  rw [hvs]; exact hv7 x

set_option maxRecDepth 100000 in
lemma hs8 : ∀ x : Xs, (∑ t : St, if BB (ynx x t) ∧ yR U x t then tb T7 (ynx x t) else 0) = tb T8 x := by
  decide +kernel

lemma hv8 (x : Xs) : vS BB ynx (yR U) 8 x = tb T8 x := by
  show (∑ t, if BB (ynx x t) ∧ yR U x t then vS BB ynx (yR U) 7 (ynx x t) else 0) = _
  simp only [hv7]; exact hs8 x

lemma hu8 (x : Xs) : u BB TT 8 x = tb T8 x := by
  rw [hvs]; exact hv8 x

set_option maxRecDepth 100000 in
lemma hs9 : ∀ x : Xs, (∑ t : St, if BB (ynx x t) ∧ yR U x t then tb T8 (ynx x t) else 0) = tb T9 x := by
  decide +kernel

lemma hv9 (x : Xs) : vS BB ynx (yR U) 9 x = tb T9 x := by
  show (∑ t, if BB (ynx x t) ∧ yR U x t then vS BB ynx (yR U) 8 (ynx x t) else 0) = _
  simp only [hv8]; exact hs9 x

lemma hu9 (x : Xs) : u BB TT 9 x = tb T9 x := by
  rw [hvs]; exact hv9 x

set_option maxRecDepth 100000 in
lemma hrel : ∀ x, BB x → tb T9 x + 21 * tb T7 x + 35 * tb T5 x + 7 * tb T3 x = 7 * tb T8 x + 35 * tb T6 x + 21 * tb T4 x + tb T2 x := by
  decide +kernel

lemma arec (k : ℕ) : (a (k + 11) : ℤ) = 7 * a (k + 10) - 21 * a (k + 9) + 35 * a (k + 8) - 35 * a (k + 7) + 21 * a (k + 6) - 7 * a (k + 5) + a (k + 4) := by
  have e9 : a (k + 11) = ∑ x, w II BB TT k x * u BB TT 9 x := aw k 9
  have e8 : a (k + 10) = ∑ x, w II BB TT k x * u BB TT 8 x := aw k 8
  have e7 : a (k + 9) = ∑ x, w II BB TT k x * u BB TT 7 x := aw k 7
  have e6 : a (k + 8) = ∑ x, w II BB TT k x * u BB TT 6 x := aw k 6
  have e5 : a (k + 7) = ∑ x, w II BB TT k x * u BB TT 5 x := aw k 5
  have e4 : a (k + 6) = ∑ x, w II BB TT k x * u BB TT 4 x := aw k 4
  have e3 : a (k + 5) = ∑ x, w II BB TT k x * u BB TT 3 x := aw k 3
  have e2 : a (k + 4) = ∑ x, w II BB TT k x * u BB TT 2 x := aw k 2
  have key : ∑ x, w II BB TT k x * u BB TT 9 x + 21 * ∑ x, w II BB TT k x * u BB TT 7 x + 35 * ∑ x, w II BB TT k x * u BB TT 5 x + 7 * ∑ x, w II BB TT k x * u BB TT 3 x = 7 * ∑ x, w II BB TT k x * u BB TT 8 x + 35 * ∑ x, w II BB TT k x * u BB TT 6 x + 21 * ∑ x, w II BB TT k x * u BB TT 4 x + ∑ x, w II BB TT k x * u BB TT 2 x := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro x _
    by_cases hx : BB x
    · have h := hrel x hx
      rw [hu9, hu8, hu7, hu6, hu5, hu4, hu3, hu2]
      try simp only [u]
      calc (w II BB TT k x * tb T9 x) + 21 * (w II BB TT k x * tb T7 x) + 35 * (w II BB TT k x * tb T5 x) + 7 * (w II BB TT k x * tb T3 x)
          = w II BB TT k x * (tb T9 x + 21 * tb T7 x + 35 * tb T5 x + 7 * tb T3 x) := by ring
        _ = w II BB TT k x * (7 * tb T8 x + 35 * tb T6 x + 21 * tb T4 x + tb T2 x) := by rw [h]
        _ = _ := by ring
    · simp [w_zero_of II BB TT k x hx]
  rw [e9, e8, e7, e6, e5, e4, e3, e2]
  have := congrArg (fun t : ℕ => (t : ℤ)) key
  push_cast at this ⊢
  linarith

lemma val (j : ℕ) : a (j + 2) = ∑ x, (if II x ∧ BB x then 1 else 0) * u BB TT j x := by
  rw [show j + 2 = 0 + j + 2 by ring, aw]; rfl

set_option maxRecDepth 100000 in
lemma v1 : a 1 = 8 := by
  unfold a; decide +kernel

set_option maxRecDepth 100000 in
lemma v2 : a 2 = 36 := by
  rw [val 0]; simp only [u]; decide +kernel

set_option maxRecDepth 100000 in
lemma v3 : a 3 = 89 := by
  rw [val 1]; simp only [hu1]; decide +kernel

set_option maxRecDepth 100000 in
lemma v4 : a 4 = 187 := by
  rw [val 2]; simp only [hu2]; decide +kernel

set_option maxRecDepth 100000 in
lemma v5 : a 5 = 373 := by
  rw [val 3]; simp only [hu3]; decide +kernel

set_option maxRecDepth 100000 in
lemma v6 : a 6 = 702 := by
  rw [val 4]; simp only [hu4]; decide +kernel

set_option maxRecDepth 100000 in
lemma v7 : a 7 = 1252 := by
  rw [val 5]; simp only [hu5]; decide +kernel

set_option maxRecDepth 100000 in
lemma v8 : a 8 = 2130 := by
  rw [val 6]; simp only [hu6]; decide +kernel

set_option maxRecDepth 100000 in
lemma v9 : a 9 = 3479 := by
  rw [val 7]; simp only [hu7]; decide +kernel

set_option maxRecDepth 100000 in
lemma v10 : a 10 = 5486 := by
  rw [val 8]; simp only [hu8]; decide +kernel

lemma recur (n : ℕ) (hn : 9 < n) : (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7) := by
  rcases (show n < 11 ∨ 11 ≤ n by omega) with h | h
  · interval_cases n <;> norm_num [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10]
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 11 := ⟨n - 11, by omega⟩
    rw [show k + 11 - 1 = k + 10 by omega, show k + 11 - 2 = k + 9 by omega, show k + 11 - 3 = k + 8 by omega, show k + 11 - 4 = k + 7 by omega, show k + 11 - 5 = k + 6 by omega, show k + 11 - 6 = k + 5 by omega, show k + 11 - 7 = k + 4 by omega]
    exact arec k

lemma ps (f : ℕ → ℚ) (n k : ℕ) :
    PowerSeries.coeff n (PowerSeries.mk f * PowerSeries.X ^ k) = if k ≤ n then f (n - k) else 0 := by
  rw [PowerSeries.coeff_mul_X_pow']; simp

lemma ps1 (f : ℕ → ℚ) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.mk f * PowerSeries.X) = if 1 ≤ n then f (n - 1) else 0 := by
  rw [← ps, pow_one]

end OMA.P_oeis_a224159

open PowerSeries Finset in
open OMA.S_oeis_a224159 OMA.P_oeis_a224159 in
theorem OMA.solution : type_of% @OMA.S_oeis_a224159.main := by
  refine ⟨?_, recur⟩
  rw [show ((1 - X) ^ 7 : PowerSeries ℚ) =
      1 - PowerSeries.C (7:ℚ) * X + PowerSeries.C (21:ℚ) * X ^ 2 - PowerSeries.C (35:ℚ) * X ^ 3 + PowerSeries.C (35:ℚ) * X ^ 4 - PowerSeries.C (21:ℚ) * X ^ 5 + PowerSeries.C (7:ℚ) * X ^ 6 - X ^ 7 by
        simp only [map_ofNat]; ring,
    show (X * (8 - 20 * X + 5 * X ^ 2 + 40 * X ^ 3 - 47 * X ^ 4 - 5 * X ^ 5 + 41 * X ^ 6 - 27 * X ^ 7 + 6 * X ^ 8) : PowerSeries ℚ) =
      PowerSeries.C (8:ℚ) * X - PowerSeries.C (20:ℚ) * X ^ 2 + PowerSeries.C (5:ℚ) * X ^ 3 + PowerSeries.C (40:ℚ) * X ^ 4 - PowerSeries.C (47:ℚ) * X ^ 5 - PowerSeries.C (5:ℚ) * X ^ 6 + PowerSeries.C (41:ℚ) * X ^ 7 - PowerSeries.C (27:ℚ) * X ^ 8 + PowerSeries.C (6:ℚ) * X ^ 9 by
        simp only [map_ofNat]; ring]
  ext n
  simp only [mul_add, mul_sub, mul_one, map_add, map_sub, map_neg, mul_neg, mul_left_comm _ (PowerSeries.C _),
    PowerSeries.coeff_C_mul, ps, ps1, PowerSeries.coeff_X, PowerSeries.coeff_mk,
    PowerSeries.coeff_X_pow, PowerSeries.coeff_one]
  rcases (show n ≤ 9 ∨ 10 ≤ n by omega) with h | h
  · interval_cases n <;> simp [v1, v2, v3, v4, v5, v6, v7, v8, v9] <;> norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 10 := ⟨n - 10, by omega⟩
    have hq : (a (m + 10) : ℚ) = 7 * a (m + 9) - 21 * a (m + 8) + 35 * a (m + 7) - 35 * a (m + 6) + 21 * a (m + 5) - 7 * a (m + 4) + a (m + 3) := by
      have := recur (m + 10) (by omega)
      rw [show m + 10 - 1 = m + 9 by omega, show m + 10 - 2 = m + 8 by omega, show m + 10 - 3 = m + 7 by omega, show m + 10 - 4 = m + 6 by omega, show m + 10 - 5 = m + 5 by omega, show m + 10 - 6 = m + 4 by omega, show m + 10 - 7 = m + 3 by omega] at this
      exact_mod_cast this
    simp [show m + 10 - 1 = m + 9 by omega, show m + 10 - 2 = m + 8 by omega, show m + 10 - 3 = m + 7 by omega, show m + 10 - 4 = m + 6 by omega, show m + 10 - 5 = m + 5 by omega, show m + 10 - 6 = m + 4 by omega, show m + 10 - 7 = m + 3 by omega,
      show m + 10 ≠ 1 by omega, show m + 10 ≠ 2 by omega, show m + 10 ≠ 3 by omega, show m + 10 ≠ 4 by omega, show m + 10 ≠ 5 by omega, show m + 10 ≠ 6 by omega, show m + 10 ≠ 7 by omega, show m + 10 ≠ 8 by omega, show m + 10 ≠ 9 by omega]
    rw [hq]; ring
