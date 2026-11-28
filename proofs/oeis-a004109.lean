import OMAStatements.S_oeis_a004109
import Mathlib

/-!
A004109: asymptotics of connected labelled cubic graphs

Proof of a(n) ~ 2^(n+1/2) 3^n n^(3n) / exp(3n+2) via the configuration (pairing) model:

* Configurations are fixed-point-free involutions of the 6n stubs `Fin (2n) × Fin 3`;
  there are Q(6n) = (6n)!/((3n)! 2^(3n)) of them, and those containing k prescribed
  disjoint pairs number Q(6n-2k).
* Simple connected configurations correspond 6^(2n)-to-1 to connected labelled cubic graphs.
* Loops and double edges: the factorial moments E[C(L,c) C(D,d)] tend to 1/(c! d!),
  by union bounds over witnesses (upper) and exactly-double witnesses (lower);
  Bonferroni inequalities then give P(simple) -> exp(-2).
* Disconnected configurations have a closed vertex set of size at most n; a union bound
  gives probability at most 1/n + 2/(n-1).
* Stirling's formula converts exp(-2) Q(6n)/6^(2n) into the stated expression.

The method is the classical one of E. A. Bender and E. R. Canfield, J. Combin. Theory
Ser. A 24 (1978) 296-307; B. Bollobas, European J. Combin. 1 (1980) 311-316; and
N. C. Wormald, J. Combin. Theory Ser. B 31 (1981) 156-167 (connectedness).
-/


namespace OMA.A4109
open Classical Finset

/-- Fixed-point-free involutions: perfect matchings of `T`. -/
def IsFPF {T : Type} (f : T → T) : Prop := ∀ t, f t ≠ t ∧ f (f t) = t

/-- Number of perfect matchings on `m` points. -/
def Q : ℕ → ℕ
  | 0 => 1
  | 1 => 0
  | (m+2) => (m+1) * Q m

section restrict
variable {T : Type} [Fintype T] (x y : T)

/-- Points other than `x` and `y`. -/
abbrev Rest := {t : T // t ≠ x ∧ t ≠ y}

noncomputable def extend (g : Rest x y → Rest x y) (t : T) : T :=
  if h : t ≠ x ∧ t ≠ y then (g ⟨t, h⟩).1 else if t = x then y else x

theorem extend_rest (g : Rest x y → Rest x y) (t : Rest x y) : extend x y g t.1 = (g t).1 := by
  simp [extend, t.2]

theorem extend_x (g : Rest x y → Rest x y) : extend x y g x = y := by
  simp [extend]

theorem extend_y (hxy : x ≠ y) (g : Rest x y → Rest x y) : extend x y g y = x := by
  simp [extend, hxy.symm]

theorem extend_fpf (hxy : x ≠ y) (g : Rest x y → Rest x y) (hg : IsFPF g) :
    IsFPF (extend x y g) := by
  intro t
  by_cases h : t ≠ x ∧ t ≠ y
  · have e1 := extend_rest x y g ⟨t, h⟩
    simp only at e1
    rw [e1]
    have e2 := extend_rest x y g (g ⟨t, h⟩)
    rw [e2, (hg _).2]
    refine ⟨fun h' => (hg ⟨t,h⟩).1 (Subtype.ext h'), rfl⟩
  · by_cases htx : t = x
    · subst htx; rw [extend_x, extend_y _ _ hxy]; exact ⟨hxy.symm, rfl⟩
    · have hty : t = y := by tauto
      rw [hty, extend_y _ _ hxy, extend_x]; exact ⟨hxy, rfl⟩

theorem fpf_maps_rest {f : T → T} (hf : IsFPF f) (hfx : f x = y) (t : T) (ht : t ≠ x ∧ t ≠ y) :
    f t ≠ x ∧ f t ≠ y := by
  constructor
  · intro h; apply ht.2; rw [← (hf t).2, h, hfx]
  · intro h; apply ht.1; rw [← (hf t).2, h, ← hfx, (hf x).2]

theorem extend_restrict {f : T → T} (hxy : x ≠ y) (hf : IsFPF f) (hfx : f x = y) :
    extend x y (fun t => ⟨f t.1, fpf_maps_rest x y hf hfx t.1 t.2⟩) = f := by
  funext t
  by_cases h : t ≠ x ∧ t ≠ y
  · exact extend_rest x y _ ⟨t, h⟩
  · by_cases htx : t = x
    · rw [htx, extend_x, hfx]
    · have hty : t = y := by tauto
      have h2 : f y = x := by rw [← hfx]; exact (hf x).2
      rw [hty, extend_y _ _ hxy, h2]

/-- Restricting a matching containing the pair `x y` to the other points. -/
noncomputable def restrictEquiv (hxy : x ≠ y) (P : (T → T) → Prop) :
    {f : T → T // IsFPF f ∧ f x = y ∧ P f} ≃
      {g : Rest x y → Rest x y // IsFPF g ∧ P (extend x y g)} where
  toFun f := ⟨fun t => ⟨f.1 t.1, fpf_maps_rest x y f.2.1 f.2.2.1 t.1 t.2⟩, by
    refine ⟨fun t => ⟨fun h => (f.2.1 t.1).1 (congrArg Subtype.val h), ?_⟩, ?_⟩
    · exact Subtype.ext (f.2.1 t.1).2
    · rw [extend_restrict x y hxy f.2.1 f.2.2.1]; exact f.2.2.2⟩
  invFun g := ⟨extend x y g.1, extend_fpf x y hxy g.1 g.2.1, extend_x x y g.1, g.2.2⟩
  left_inv f := Subtype.ext (extend_restrict x y hxy f.2.1 f.2.2.1)
  right_inv g := by
    apply Subtype.ext
    funext t
    apply Subtype.ext
    exact extend_rest x y g.1 t

theorem card_restrict (hxy : x ≠ y) (P : (T → T) → Prop) :
    Nat.card {f : T → T // IsFPF f ∧ f x = y ∧ P f} =
      Nat.card {g : Rest x y → Rest x y // IsFPF g ∧ P (extend x y g)} :=
  Nat.card_congr (restrictEquiv x y hxy P)

theorem card_rest (hxy : x ≠ y) : Nat.card (Rest x y) = Nat.card T - 2 := by
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have : (univ.filter fun t : T => t ≠ x ∧ t ≠ y) = univ \ {x, y} := by
    ext t; simp [not_or]
  rw [this, card_sdiff_of_subset (subset_univ _), card_pair hxy, card_univ]

end restrict

theorem card_fpf_aux (n : ℕ) : ∀ (T : Type) [Fintype T], Nat.card T = n →
    Nat.card {f : T → T // IsFPF f} = Q n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro T _ hT
  match n, ih with
  | 0, _ =>
    rw [Nat.card_eq_fintype_card] at hT
    have : IsEmpty T := Fintype.card_eq_zero_iff.mp hT
    rw [Q, Nat.card_eq_fintype_card, Fintype.card_eq_one_iff]
    refine ⟨⟨fun t => t, fun t => isEmptyElim t⟩, fun f => Subtype.ext (funext fun t => isEmptyElim t)⟩
  | 1, _ =>
    rw [Nat.card_eq_fintype_card] at hT
    obtain ⟨x, hx⟩ := Fintype.card_eq_one_iff.mp hT
    rw [Q, Nat.card_eq_fintype_card, Fintype.card_eq_zero_iff]
    exact ⟨fun f => (f.2 x).1 (hx _)⟩
  | m+2, ih =>
    have hne : Nonempty T := by
      rw [Nat.card_eq_fintype_card] at hT; exact Fintype.card_pos_iff.mp (by omega)
    obtain ⟨x⟩ := hne
    let g : {f : T → T // IsFPF f} → {y : T // y ≠ x} := fun f => ⟨f.1 x, (f.2 x).1⟩
    have hterm : ∀ y : {y : T // y ≠ x}, Nat.card {f // g f = y} = Q m := by
      intro y
      have hy' : x ≠ y.1 := Ne.symm y.2
      have e : {f // g f = y} ≃ {f : T → T // IsFPF f ∧ f x = y.1 ∧ True} :=
        { toFun := fun f => ⟨f.1.1, f.1.2, congrArg Subtype.val f.2, trivial⟩
          invFun := fun f => ⟨⟨f.1, f.2.1⟩, Subtype.ext f.2.2.1⟩
          left_inv := fun f => rfl
          right_inv := fun f => rfl }
      rw [Nat.card_congr e, card_restrict x y.1 hy' (fun _ => True)]
      have : Nat.card {g : Rest x y.1 → Rest x y.1 // IsFPF g ∧ True} =
          Nat.card {g : Rest x y.1 → Rest x y.1 // IsFPF g} :=
        Nat.card_congr (Equiv.subtypeEquivRight (fun g => ⟨fun h => h.1, fun h => ⟨h, trivial⟩⟩))
      rw [this]
      exact ih m (by omega) _ (by rw [card_rest x y.1 hy', hT]; rfl)
    have hsig := Nat.card_congr (Equiv.sigmaFiberEquiv g)
    rw [← hsig, Nat.card_sigma]
    rw [Finset.sum_congr rfl (fun y _ => hterm y), sum_const, card_univ, smul_eq_mul]
    have hc : Fintype.card {y : T // y ≠ x} = m + 1 := by
      rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, ← Nat.card_eq_fintype_card, hT]; rfl
    rw [hc]
    rfl

theorem card_fpf (T : Type) [Fintype T] :
    Nat.card {f : T → T // IsFPF f} = Q (Nat.card T) :=
  card_fpf_aux _ T rfl

theorem card_prescribed (k : ℕ) : ∀ (T : Type) [Fintype T] (e : Fin k ⊕ Fin k → T),
    Function.Injective e →
    Nat.card {f : T → T // IsFPF f ∧ ∀ i, f (e (.inl i)) = e (.inr i)} = Q (Nat.card T - 2*k) := by
  induction k with
  | zero =>
    intro T _ e _
    rw [Nat.mul_zero, Nat.sub_zero, ← card_fpf T]
    exact Nat.card_congr (Equiv.subtypeEquivRight (fun f => ⟨fun h => h.1, fun h => ⟨h, fun i => i.elim0⟩⟩))
  | succ k ih =>
    intro T _ e he
    set x := e (.inl 0)
    set y := e (.inr 0)
    have hxy : x ≠ y := fun h => by simpa using he h
    have hmap : ∀ z : Fin k ⊕ Fin k, e (Sum.map Fin.succ Fin.succ z) ≠ x ∧
        e (Sum.map Fin.succ Fin.succ z) ≠ y := by
      intro z
      constructor
      · intro h; have := he h; cases z <;> simp at this
      · intro h; have := he h; cases z <;> simp at this
    let e' : Fin k ⊕ Fin k → Rest x y := fun z => ⟨e (Sum.map Fin.succ Fin.succ z), hmap z⟩
    have he' : Function.Injective e' := by
      intro z w h
      have := he (congrArg Subtype.val h)
      cases z <;> cases w <;> simp_all [Fin.succ_inj]
    have step1 : Nat.card {f : T → T // IsFPF f ∧ ∀ i, f (e (.inl i)) = e (.inr i)} =
        Nat.card {f : T → T // IsFPF f ∧ f x = y ∧
          ∀ i : Fin k, f (e (.inl i.succ)) = e (.inr i.succ)} :=
      Nat.card_congr (Equiv.subtypeEquivRight (fun f => by rw [Fin.forall_fin_succ]))
    rw [step1, card_restrict x y hxy]
    have step2 : Nat.card {g : Rest x y → Rest x y // IsFPF g ∧
          ∀ i : Fin k, extend x y g (e (.inl i.succ)) = e (.inr i.succ)} =
        Nat.card {g : Rest x y → Rest x y // IsFPF g ∧ ∀ i, g (e' (.inl i)) = e' (.inr i)} := by
      refine Nat.card_congr (Equiv.subtypeEquivRight (fun g => and_congr_right (fun _ => ?_)))
      refine forall_congr' (fun i => ?_)
      have h1 := extend_rest x y g (e' (.inl i))
      simp only [e', Sum.map_inl, Sum.map_inr] at h1 ⊢
      rw [h1, Subtype.ext_iff]
    rw [step2, ih _ e' he', card_rest x y hxy]
    congr 1
    omega


theorem card_prescribed' {I : Type} [Fintype I] (T : Type) [Fintype T] (e : I ⊕ I → T)
    (he : Function.Injective e) :
    Nat.card {f : T → T // IsFPF f ∧ ∀ i, f (e (.inl i)) = e (.inr i)} =
      Q (Nat.card T - 2 * Fintype.card I) := by
  let σ := Fintype.equivFin I
  have h := card_prescribed (Fintype.card I) T (e ∘ Sum.map σ.symm σ.symm)
    (he.comp (Sum.map_injective.mpr ⟨σ.symm.injective, σ.symm.injective⟩))
  rw [← h]
  refine Nat.card_congr (Equiv.subtypeEquivRight (fun f => and_congr_right (fun _ => ?_)))
  simp only [Function.comp, Sum.map_inl, Sum.map_inr]
  exact ⟨fun h j => h _, fun h i => by simpa using h (σ i)⟩

theorem card_filter_fpf {T : Type} [Fintype T] [DecidableEq T] [DecidablePred (@IsFPF T)] (P : (T → T) → Prop)
    [DecidablePred P] :
    ((univ.filter IsFPF).filter P).card = Nat.card {f : T → T // IsFPF f ∧ P f} := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, filter_filter]

/-! Cubic configurations -/

abbrev WL := {q : Fin 2 → Fin 3 // q 0 < q 1}
abbrev WD := {q : (Fin 2 → Fin 3) × (Fin 2 → Fin 3) // q.1 0 < q.1 1 ∧ q.2 0 ≠ q.2 1}

theorem card_WL : Fintype.card WL = 3 := by decide
theorem card_WD : Fintype.card WD = 18 := by decide

/-- The third point of `Fin 3`. -/
def tr (x y : Fin 3) : Fin 3 := ⟨(3 - x.1 - y.1) % 3, Nat.mod_lt _ (by norm_num)⟩

theorem tr_ne : ∀ x y : Fin 3, x ≠ y → tr x y ≠ x ∧ tr x y ≠ y := by decide
theorem tr_uniq : ∀ x y z : Fin 3, x ≠ y → z ≠ x → z ≠ y → z = tr x y := by decide
theorem fin3_meet : ∀ a b a' b' : Fin 3, a ≠ b → a' ≠ b' → a = a' ∨ a = b' ∨ b = a' ∨ b = b' := by
  decide
theorem fin3_sorted : ∀ x y x' y' : Fin 3, x < y → x' < y' → (x' = x ∨ x' = y) →
    (y' = x ∨ y' = y) → x' = x ∧ y' = y := by decide
theorem fin2_inj {q : Fin 2 → Fin 3} (hq : q 0 ≠ q 1) {s s' : Fin 2} (h : q s = q s') : s = s' := by
  fin_cases s <;> fin_cases s' <;> simp_all [eq_comm]

theorem fpf_inj {T : Type} {f : T → T} (hf : IsFPF f) : Function.Injective f := by
  intro a b h; rw [← (hf a).2, h, (hf b).2]

section cubic
variable {V : Type} [Fintype V] [LinearOrder V] {c d : ℕ}

def Loop (f : V × Fin 3 → V × Fin 3) (v : V) : Prop := ∃ q : WL, f (v, q.1 0) = (v, q.1 1)
def Dbl (f : V × Fin 3 → V × Fin 3) (v w : V) : Prop :=
  ∃ q : WD, ∀ s, f (v, q.1.1 s) = (w, q.1.2 s)

abbrev Slot (c d : ℕ) := Fin c ⊕ Fin d × Fin 2

def Ev (f : V × Fin 3 → V × Fin 3) (γ : Slot c d → V) : Prop :=
  (∀ i, Loop f (γ (.inl i))) ∧ ∀ j, Dbl f (γ (.inr (j, 0))) (γ (.inr (j, 1)))

def Disj (γ : Slot c d → V) : Prop :=
  Function.Injective γ ∧ ∀ j, γ (.inr (j, 0)) < γ (.inr (j, 1))

def Two (f : V × Fin 3 → V × Fin 3) (x y : V) : Prop :=
  ∃ a b, a ≠ b ∧ (f (x, a)).1 = y ∧ (f (x, b)).1 = y

theorem two_eq {f : V × Fin 3 → V × Fin 3} {x y z : V} (h1 : Two f x y) (h2 : Two f x z) :
    y = z := by
  obtain ⟨a, b, hab, ha, hb⟩ := h1
  obtain ⟨a', b', hab', ha', hb'⟩ := h2
  rcases fin3_meet a b a' b' hab hab' with h | h | h | h <;> subst h
  · exact ha.symm.trans ha'
  · exact ha.symm.trans hb'
  · exact hb.symm.trans ha'
  · exact hb.symm.trans hb'

theorem two_of_loop {f : V × Fin 3 → V × Fin 3} (hf : IsFPF f) {x : V} (h : Loop f x) :
    Two f x x := by
  obtain ⟨q, hq⟩ := h
  refine ⟨q.1 0, q.1 1, ne_of_lt q.2, by rw [hq], ?_⟩
  have : f (x, q.1 1) = (x, q.1 0) := by rw [← hq, (hf _).2]
  rw [this]

theorem two_of_dbl {f : V × Fin 3 → V × Fin 3} (hf : IsFPF f) {v w : V} (h : Dbl f v w) :
    Two f v w ∧ Two f w v := by
  obtain ⟨q, hq⟩ := h
  refine ⟨⟨q.1.1 0, q.1.1 1, ne_of_lt q.2.1, by rw [hq], by rw [hq]⟩,
    ⟨q.1.2 0, q.1.2 1, q.2.2, ?_, ?_⟩⟩
  · rw [← hq 0, (hf _).2]
  · rw [← hq 1, (hf _).2]

theorem fin2_cases (s : Fin 2) : s = 0 ∨ s = 1 := by fin_cases s <;> simp

/-- Occurring events have disjoint supports. -/
theorem inj_of_ev {f : V × Fin 3 → V × Fin 3} (hf : IsFPF f) {γ : Slot c d → V}
    (hev : Ev f γ) (hord : ∀ j, γ (.inr (j, 0)) < γ (.inr (j, 1)))
    (hα : Function.Injective fun i => γ (.inl i))
    (hβ : Function.Injective fun j => (γ (.inr (j, 0)), γ (.inr (j, 1)))) :
    Function.Injective γ := by
  intro u u' h
  rcases u with i | ⟨j, s⟩ <;> rcases u' with i' | ⟨j', s'⟩
  · exact congrArg _ (hα h)
  · exfalso
    have hl := two_of_loop hf (hev.1 i)
    have hd := two_of_dbl hf (hev.2 j')
    have := hord j'
    rcases fin2_cases s' with rfl | rfl
    · rw [h] at hl; exact absurd (two_eq hl hd.1) (ne_of_lt this)
    · rw [h] at hl; exact absurd (two_eq hl hd.2) (ne_of_gt this)
  · exfalso
    have hl := two_of_loop hf (hev.1 i')
    have hd := two_of_dbl hf (hev.2 j)
    have := hord j
    rcases fin2_cases s with rfl | rfl
    · rw [← h] at hl; exact absurd (two_eq hl hd.1) (ne_of_lt this)
    · rw [← h] at hl; exact absurd (two_eq hl hd.2) (ne_of_gt this)
  · have hd := two_of_dbl hf (hev.2 j)
    have hd' := two_of_dbl hf (hev.2 j')
    have o := hord j
    have o' := hord j'
    rcases fin2_cases s with rfl | rfl <;> rcases fin2_cases s' with rfl | rfl
    · have e1 := two_eq hd.1 (h ▸ hd'.1)
      have := hβ (Prod.ext h e1); subst this; rfl
    · have e1 := two_eq hd.1 (h ▸ hd'.2)
      exfalso; rw [h] at o; rw [e1] at o; exact lt_asymm o o'
    · have e1 := two_eq hd.2 (h ▸ hd'.1)
      exfalso; rw [← h] at o'; rw [← e1] at o'; exact lt_asymm o o'
    · have e1 := two_eq hd.2 (h ▸ hd'.2)
      have := hβ (Prod.ext e1 h); subst this; rfl

/-! Witnesses -/

def slotOf : Slot c d ⊕ Slot c d → Slot c d
  | .inl (.inl i) => .inl i
  | .inr (.inl i) => .inl i
  | .inl (.inr (j, _)) => .inr (j, 0)
  | .inr (.inr (j, _)) => .inr (j, 1)

def stubOf (ω : (Fin c → WL) × (Fin d → WD)) : Slot c d ⊕ Slot c d → Fin 3
  | .inl (.inl i) => (ω.1 i).1 0
  | .inr (.inl i) => (ω.1 i).1 1
  | .inl (.inr (j, s)) => (ω.2 j).1.1 s
  | .inr (.inr (j, s)) => (ω.2 j).1.2 s

def wit (γ : Slot c d → V) (ω : (Fin c → WL) × (Fin d → WD)) (z : Slot c d ⊕ Slot c d) :
    V × Fin 3 := (γ (slotOf z), stubOf ω z)

theorem wit_inj {γ : Slot c d → V} (hγ : Function.Injective γ) (ω : (Fin c → WL) × (Fin d → WD)) :
    Function.Injective (wit γ ω) := by
  intro z z' h
  simp only [wit, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have h1 := hγ h1
  rcases z with (i | ⟨j, s⟩) | (i | ⟨j, s⟩) <;> rcases z' with (i' | ⟨j', s'⟩) | (i' | ⟨j', s'⟩) <;>
    simp only [slotOf, stubOf, Sum.inl.injEq, Sum.inr.injEq, Prod.mk.injEq, reduceCtorEq,
      Fin.zero_eq_one_iff, false_and, and_false] at h1 h2 ⊢
  all_goals first
    | (subst h1; rfl)
    | (subst h1; exact absurd h2 (ne_of_lt (ω.1 i).2))
    | (subst h1; exact absurd h2.symm (ne_of_lt (ω.1 i).2))
    | (obtain ⟨rfl, -⟩ := h1; exact ⟨rfl, fin2_inj (ne_of_lt (ω.2 j).2.1) h2⟩)
    | (obtain ⟨rfl, -⟩ := h1; exact ⟨rfl, fin2_inj (ω.2 j).2.2 h2⟩)
    | exact absurd h1.2 (by decide)


theorem ev_iff {f : V × Fin 3 → V × Fin 3} {γ : Slot c d → V} :
    Ev f γ ↔ ∃ ω, ∀ z, f (wit γ ω (.inl z)) = wit γ ω (.inr z) := by
  constructor
  · rintro ⟨hL, hD⟩
    choose qL hqL using hL
    choose qD hqD using hD
    refine ⟨(qL, qD), ?_⟩
    rintro (i | ⟨j, s⟩)
    · exact hqL i
    · exact hqD j s
  · rintro ⟨ω, h⟩
    exact ⟨fun i => ⟨ω.1 i, h (.inl i)⟩, fun j => ⟨ω.2 j, fun s => h (.inr (j, s))⟩⟩

theorem card_slot : Fintype.card (Slot c d) = c + d * 2 := by
  simp [Fintype.card_sum, Fintype.card_prod]

theorem card_wit : Fintype.card ((Fin c → WL) × (Fin d → WD)) = 3 ^ c * 18 ^ d := by
  simp [Fintype.card_prod, Fintype.card_fun, card_WL, card_WD]

/-- Upper bound: union over witnesses. -/
theorem ev_upper {γ : Slot c d → V} (hγ : Disj γ) :
    (((univ : Finset (V × Fin 3 → V × Fin 3)).filter IsFPF).filter (fun f => Ev f γ)).card ≤
      3 ^ c * 18 ^ d * Q (Nat.card (V × Fin 3) - 2 * (c + d * 2)) := by
  calc _ ≤ ((univ : Finset ((Fin c → WL) × (Fin d → WD))).biUnion fun ω =>
        ((univ : Finset (V × Fin 3 → V × Fin 3)).filter IsFPF).filter
          (fun f => ∀ z, f (wit γ ω (.inl z)) = wit γ ω (.inr z))).card := by
        apply card_le_card
        intro f hf
        rw [mem_filter] at hf
        obtain ⟨ω, hω⟩ := ev_iff.mp hf.2
        rw [mem_biUnion]
        exact ⟨ω, mem_univ _, mem_filter.mpr ⟨hf.1, hω⟩⟩
    _ ≤ _ := card_biUnion_le
    _ = ∑ ω : (Fin c → WL) × (Fin d → WD), Q (Nat.card (V × Fin 3) - 2 * (c + d * 2)) := by
        refine sum_congr rfl (fun ω _ => ?_)
        rw [card_filter_fpf, card_prescribed' _ _ (wit_inj hγ.1 ω), card_slot]
    _ = _ := by rw [sum_const, card_univ, card_wit, smul_eq_mul]

theorem loop_uniq {f : V × Fin 3 → V × Fin 3} (hf : IsFPF f) {x : V} {q q' : WL}
    (h : f (x, q.1 0) = (x, q.1 1)) (h' : f (x, q'.1 0) = (x, q'.1 1)) : q = q' := by
  obtain ⟨q, hq⟩ := q
  obtain ⟨q', hq'⟩ := q'
  simp only at h h' ⊢
  have h1 : f (x, q 1) = (x, q 0) := by rw [← h, (hf _).2]
  have h1' : f (x, q' 1) = (x, q' 0) := by rw [← h', (hf _).2]
  have E : ∀ a b b' : Fin 3, f (x, a) = (x, b) → f (x, a) = (x, b') → b = b' :=
    fun a b b' e1 e2 => by have := e1.symm.trans e2; simpa using this
  have key : q 0 = q' 0 ∧ q 1 = q' 1 := by
    rcases fin3_meet (q 0) (q 1) (q' 0) (q' 1) (ne_of_lt hq) (ne_of_lt hq') with e | e | e | e
    · rw [e] at h; exact ⟨e, E _ _ _ h h'⟩
    · rw [e] at h; have t := E _ _ _ h h1'
      exfalso
      have : q 0 < q 0 := calc
        q 0 < q 1 := hq
        _ = q' 0 := t
        _ < q' 1 := hq'
        _ = q 0 := e.symm
      exact lt_irrefl _ this
    · rw [e] at h1; have t := E _ _ _ h1 h'
      exfalso
      have : q 0 < q 0 := calc
        q 0 < q 1 := hq
        _ = q' 0 := e
        _ < q' 1 := hq'
        _ = q 0 := t.symm
      exact lt_irrefl _ this
    · rw [e] at h1; exact ⟨E _ _ _ h1 h1', e⟩
  exact Subtype.ext (funext fun s => by rcases fin2_cases s with rfl | rfl; exacts [key.1, key.2])

theorem dbl_uniq {f : V × Fin 3 → V × Fin 3} (hf : IsFPF f) {v w : V} {q q' : WD}
    (h : ∀ s, f (v, q.1.1 s) = (w, q.1.2 s))
    (hc : f (v, tr (q.1.1 0) (q.1.1 1)) ≠ (w, tr (q.1.2 0) (q.1.2 1)))
    (h' : ∀ s, f (v, q'.1.1 s) = (w, q'.1.2 s)) : q = q' := by
  obtain ⟨⟨a, b⟩, ha, hb⟩ := q
  obtain ⟨⟨a', b'⟩, ha', hb'⟩ := q'
  simp only at h hc h' ⊢
  have finj := fpf_inj hf
  have mem : ∀ s, a' s = a 0 ∨ a' s = a 1 := by
    intro s
    by_contra hn
    push_neg at hn
    have e := tr_uniq (a 0) (a 1) (a' s) (ne_of_lt ha) hn.1 hn.2
    have hfs := h' s
    rw [e] at hfs
    have n0 : b' s ≠ b 0 := by
      intro hb0
      rw [hb0, ← h 0] at hfs
      have := finj hfs
      simp only [Prod.mk.injEq, true_and] at this
      exact (tr_ne _ _ (ne_of_lt ha)).1 this
    have n1 : b' s ≠ b 1 := by
      intro hb1
      rw [hb1, ← h 1] at hfs
      have := finj hfs
      simp only [Prod.mk.injEq, true_and] at this
      exact (tr_ne _ _ (ne_of_lt ha)).2 this
    have := tr_uniq (b 0) (b 1) (b' s) hb n0 n1
    rw [this] at hfs
    exact hc hfs
  obtain ⟨e0, e1⟩ := fin3_sorted (a 0) (a 1) (a' 0) (a' 1) ha ha' (mem 0) (mem 1)
  have ea : a' = a := funext fun s => by rcases fin2_cases s with rfl | rfl; exacts [e0, e1]
  subst ea
  have eb : b' = b := funext fun s => by
    have := (h s).symm.trans (h' s)
    simp only [Prod.mk.injEq, true_and] at this
    exact this.symm
  subst eb
  rfl

def clo (γ : Slot c d → V) (ω : (Fin c → WL) × (Fin d → WD)) (j : Fin d) :
    (V × Fin 3) × (V × Fin 3) :=
  ((γ (.inr (j, 0)), tr ((ω.2 j).1.1 0) ((ω.2 j).1.1 1)),
    (γ (.inr (j, 1)), tr ((ω.2 j).1.2 0) ((ω.2 j).1.2 1)))

def wit2 (γ : Slot c d → V) (ω : (Fin c → WL) × (Fin d → WD)) (j : Fin d) :
    (Slot c d ⊕ Unit) ⊕ (Slot c d ⊕ Unit) → V × Fin 3
  | .inl (.inl z) => wit γ ω (.inl z)
  | .inr (.inl z) => wit γ ω (.inr z)
  | .inl (.inr _) => (clo γ ω j).1
  | .inr (.inr _) => (clo γ ω j).2

theorem clo_ne {γ : Slot c d → V} (hγ : Function.Injective γ) (ω : (Fin c → WL) × (Fin d → WD))
    (j : Fin d) (y : Slot c d ⊕ Slot c d) :
    (clo γ ω j).1 ≠ wit γ ω y ∧ (clo γ ω j).2 ≠ wit γ ω y := by
  constructor
  · intro h
    simp only [clo, wit, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have h1 := hγ h1
    rcases y with (i | ⟨j', s⟩) | (i | ⟨j', s⟩) <;>
      simp only [slotOf, stubOf, Sum.inl.injEq, Sum.inr.injEq, Prod.mk.injEq, reduceCtorEq] at h1 h2
    · obtain ⟨rfl, -⟩ := h1
      rcases fin2_cases s with rfl | rfl
      · exact (tr_ne _ _ (ne_of_lt (ω.2 j).2.1)).1 h2
      · exact (tr_ne _ _ (ne_of_lt (ω.2 j).2.1)).2 h2
    · exact absurd h1.2 (by decide)
  · intro h
    simp only [clo, wit, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have h1 := hγ h1
    rcases y with (i | ⟨j', s⟩) | (i | ⟨j', s⟩) <;>
      simp only [slotOf, stubOf, Sum.inl.injEq, Sum.inr.injEq, Prod.mk.injEq, reduceCtorEq] at h1 h2
    · exact absurd h1.2 (by decide)
    · obtain ⟨rfl, -⟩ := h1
      rcases fin2_cases s with rfl | rfl
      · exact (tr_ne _ _ (ω.2 j).2.2).1 h2
      · exact (tr_ne _ _ (ω.2 j).2.2).2 h2

theorem wit2_inj {γ : Slot c d → V} (hγ : Function.Injective γ) (ω : (Fin c → WL) × (Fin d → WD))
    (j : Fin d) : Function.Injective (wit2 γ ω j) := by
  have hw := wit_inj hγ ω
  have hc := clo_ne hγ ω j
  have h01 : (clo γ ω j).1 ≠ (clo γ ω j).2 := by
    intro h
    simp only [clo, Prod.mk.injEq] at h
    have := hγ h.1
    simp only [Sum.inr.injEq, Prod.mk.injEq, true_and] at this
    exact absurd this (by decide)
  intro z z' h
  rcases z with (z | u) | (z | u) <;> rcases z' with (z' | u') | (z' | u') <;>
    simp only [wit2] at h
  all_goals first
    | (have := hw h; cases this; try rfl)
    | exact absurd h.symm ((hc _).1)
    | exact absurd h.symm ((hc _).2)
    | exact absurd h ((hc _).1)
    | exact absurd h ((hc _).2)
    | exact absurd h h01
    | exact absurd h.symm h01
    | rfl


/-- Lower bound: witnesses with exactly two edges at each double are disjoint. -/
theorem ev_lower {γ : Slot c d → V} (hγ : Disj γ) :
    (3 ^ c * 18 ^ d : ℤ) * ((Q (Nat.card (V × Fin 3) - 2 * (c + d * 2)) : ℤ) -
        d * Q (Nat.card (V × Fin 3) - 2 * (c + d * 2) - 2)) ≤
      ((((univ : Finset (V × Fin 3 → V × Fin 3)).filter IsFPF).filter
        (fun f => Ev f γ)).card : ℤ) := by
  set M := Nat.card (V × Fin 3)
  set k := c + d * 2
  set Ω := (univ : Finset (V × Fin 3 → V × Fin 3)).filter IsFPF
  let A : (Fin c → WL) × (Fin d → WD) → Finset (V × Fin 3 → V × Fin 3) := fun ω =>
    Ω.filter (fun f => ∀ z, f (wit γ ω (.inl z)) = wit γ ω (.inr z))
  let R : (Fin c → WL) × (Fin d → WD) → Finset (V × Fin 3 → V × Fin 3) := fun ω =>
    (A ω).filter (fun f => ∀ j, f (clo γ ω j).1 ≠ (clo γ ω j).2)
  let C : (Fin c → WL) × (Fin d → WD) → Fin d → Finset (V × Fin 3 → V × Fin 3) := fun ω j =>
    (A ω).filter (fun f => f (clo γ ω j).1 = (clo γ ω j).2)
  have hA : ∀ ω, (A ω).card = Q (M - 2 * k) := by
    intro ω
    simp only [A, Ω]
    rw [card_filter_fpf, card_prescribed' _ _ (wit_inj hγ.1 ω), card_slot]
  have hC : ∀ ω j, (C ω j).card = Q (M - 2 * k - 2) := by
    intro ω j
    simp only [C, A, Ω]
    rw [filter_filter, card_filter_fpf]
    have e : Nat.card {f : V × Fin 3 → V × Fin 3 // IsFPF f ∧
        ((∀ z, f (wit γ ω (.inl z)) = wit γ ω (.inr z)) ∧ f (clo γ ω j).1 = (clo γ ω j).2)} =
        Nat.card {f : V × Fin 3 → V × Fin 3 // IsFPF f ∧
          ∀ i, f (wit2 γ ω j (.inl i)) = wit2 γ ω j (.inr i)} := by
      refine Nat.card_congr (Equiv.subtypeEquivRight (fun f => and_congr_right (fun _ => ?_)))
      constructor
      · rintro ⟨h1, h2⟩ (z | u)
        · exact h1 z
        · exact h2
      · intro h
        exact ⟨fun z => h (.inl z), h (.inr ())⟩
    rw [e, card_prescribed' _ _ (wit2_inj hγ.1 ω j)]
    congr 1
    simp only [Fintype.card_sum, Fintype.card_unit, Fintype.card_fin, Fintype.card_prod, k]
    omega
  have hAR : ∀ ω, ((A ω).card : ℤ) ≤ (R ω).card + ∑ j, (C ω j).card := by
    intro ω
    have hsub : A ω ⊆ R ω ∪ (univ : Finset (Fin d)).biUnion (C ω) := by
      intro f hf
      by_cases h : ∀ j, f (clo γ ω j).1 ≠ (clo γ ω j).2
      · exact mem_union_left _ (mem_filter.mpr ⟨hf, h⟩)
      · push_neg at h
        obtain ⟨j, hj⟩ := h
        exact mem_union_right _ (mem_biUnion.mpr ⟨j, mem_univ _, mem_filter.mpr ⟨hf, hj⟩⟩)
    have := (card_le_card hsub).trans ((card_union_le _ _).trans
      (Nat.add_le_add_left card_biUnion_le _))
    exact_mod_cast this
  have hdisj : (↑(univ : Finset ((Fin c → WL) × (Fin d → WD))) :
      Set ((Fin c → WL) × (Fin d → WD))).PairwiseDisjoint R := by
    intro ω _ ω' _ hne
    rw [Function.onFun, disjoint_left]
    intro f hf hf'
    apply hne
    simp only [R, A, Ω, mem_filter, mem_univ, true_and] at hf hf'
    obtain ⟨⟨hfpf, h⟩, hc⟩ := hf
    obtain ⟨⟨-, h'⟩, -⟩ := hf'
    refine Prod.ext (funext fun i => ?_) (funext fun j => ?_)
    · exact loop_uniq (x := γ (.inl i)) hfpf (h (.inl i)) (h' (.inl i))
    · exact dbl_uniq (v := γ (.inr (j, 0))) (w := γ (.inr (j, 1))) hfpf
        (fun s => h (.inr (j, s))) (hc j) (fun s => h' (.inr (j, s)))
  have hsub : (univ : Finset ((Fin c → WL) × (Fin d → WD))).biUnion R ⊆ Ω.filter (fun f => Ev f γ) := by
    intro f hf
    obtain ⟨ω, -, hf⟩ := mem_biUnion.mp hf
    simp only [R, A, mem_filter] at hf
    exact mem_filter.mpr ⟨hf.1.1, ev_iff.mpr ⟨ω, hf.1.2⟩⟩
  have h1 : ((((univ : Finset ((Fin c → WL) × (Fin d → WD))).biUnion R).card : ℕ) : ℤ) ≤
      ((Ω.filter (fun f => Ev f γ)).card : ℤ) := by exact_mod_cast card_le_card hsub
  rw [card_biUnion hdisj] at h1
  refine le_trans ?_ h1
  push_cast
  calc (3 ^ c * 18 ^ d : ℤ) * ((Q (M - 2 * k) : ℤ) - d * Q (M - 2 * k - 2))
      = ∑ _ω : (Fin c → WL) × (Fin d → WD), ((Q (M - 2 * k) : ℤ) - d * Q (M - 2 * k - 2)) := by
        rw [sum_const, card_univ, card_wit, nsmul_eq_mul]; push_cast; ring
    _ ≤ ∑ ω, ((R ω).card : ℤ) := by
        refine sum_le_sum (fun ω _ => ?_)
        have := hAR ω
        rw [hA ω] at this
        simp only [hC ω, sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at this
        push_cast at this
        linarith


/-! Counting disjoint patterns -/

def sw (s : Fin d → Bool) : Slot c d → Slot c d
  | .inl i => .inl i
  | .inr (j, t) => .inr (j, if s j then t.rev else t)

theorem sw_sw (s : Fin d → Bool) (z : Slot c d) : sw s (sw s z) = z := by
  rcases z with i | ⟨j, t⟩
  · rfl
  · simp only [sw]; split_ifs <;> simp

def ord (γ : Slot c d → V) (j : Fin d) : Bool := decide (γ (.inr (j, 1)) < γ (.inr (j, 0)))

theorem ord_disj {g : Slot c d → V} (hg : Function.Injective g) : Disj (g ∘ sw (ord g)) := by
  refine ⟨hg.comp (fun z w h => by rw [← sw_sw (ord g) z, h, sw_sw]), fun j => ?_⟩
  simp only [Function.comp, sw]
  by_cases h : g (.inr (j, 1)) < g (.inr (j, 0))
  · have : ord g j = true := decide_eq_true h
    simp only [this, if_true]
    exact h
  · have : ord g j = false := decide_eq_false h
    simp only [this, if_false, Bool.false_eq_true]
    refine lt_of_le_of_ne (not_lt.mp h) (fun e => ?_)
    have := hg e
    simp only [Sum.inr.injEq, Prod.mk.injEq, true_and] at this
    exact absurd this (by decide)

theorem rev0 : (0 : Fin 2).rev = 1 := by decide
theorem rev1 : (1 : Fin 2).rev = 0 := by decide

theorem ord_sw {γ : Slot c d → V} (hγ : Disj γ) (s : Fin d → Bool) : ord (γ ∘ sw s) = s := by
  funext j
  simp only [ord, Function.comp, sw]
  by_cases hs : s j = true
  · simp only [hs, if_true, rev0, rev1]
    exact decide_eq_true (hγ.2 j)
  · simp only [hs, if_false, Bool.false_eq_true]
    rw [Bool.not_eq_true] at hs
    first | (rw [hs]; exact decide_eq_false (lt_asymm (hγ.2 j))) | exact decide_eq_false (lt_asymm (hγ.2 j))

theorem card_disj_mul :
    Fintype.card {γ : Slot c d → V // Disj γ} * 2 ^ d =
      (Fintype.card V).descFactorial (c + d * 2) := by
  let e : {γ : Slot c d → V // Disj γ} × (Fin d → Bool) ≃
      {γ : Slot c d → V // Function.Injective γ} :=
    { toFun := fun p => ⟨p.1.1 ∘ sw p.2,
        p.1.2.1.comp (fun z w h => by rw [← sw_sw p.2 z, h, sw_sw])⟩
      invFun := fun g => ⟨⟨g.1 ∘ sw (ord g.1), ord_disj g.2⟩, ord g.1⟩
      left_inv := by
        rintro ⟨⟨γ, hγ⟩, s⟩
        have hs := ord_sw hγ s
        refine Prod.ext (Subtype.ext ?_) hs
        funext z
        simp only [Function.comp, hs, sw_sw]
      right_inv := by
        rintro ⟨g, hg⟩
        apply Subtype.ext
        funext z
        simp only [Function.comp, sw_sw] }
  have h2 : Fintype.card (Fin d → Bool) = 2 ^ d := by simp
  rw [← h2, ← Fintype.card_prod, Fintype.card_congr e,
    Fintype.card_congr (Equiv.subtypeInjectiveEquivEmbedding _ _), Fintype.card_embedding_eq,
    card_slot]

/-! Factorial moments -/

noncomputable def LS (f : V × Fin 3 → V × Fin 3) : Finset V := univ.filter (Loop f)
noncomputable def DS (f : V × Fin 3 → V × Fin 3) : Finset (V × V) :=
  univ.filter (fun p => p.1 < p.2 ∧ Dbl f p.1 p.2)

theorem desc_mul_desc {f : V × Fin 3 → V × Fin 3} (hf : IsFPF f) :
    (LS f).card.descFactorial c * (DS f).card.descFactorial d =
      (univ.filter (fun γ : Slot c d → V => Disj γ ∧ Ev f γ)).card := by
  let e : {γ : Slot c d → V // Disj γ ∧ Ev f γ} ≃ (Fin c ↪ LS f) × (Fin d ↪ DS f) :=
    { toFun := fun γ => (⟨fun i => ⟨γ.1 (.inl i), mem_filter.mpr ⟨mem_univ _, γ.2.2.1 i⟩⟩,
          fun i i' h => by
            have := γ.2.1.1 (congrArg Subtype.val h)
            simpa using this⟩,
        ⟨fun j => ⟨(γ.1 (.inr (j, 0)), γ.1 (.inr (j, 1))),
            mem_filter.mpr ⟨mem_univ _, γ.2.1.2 j, γ.2.2.2 j⟩⟩,
          fun j j' h => by
            have := γ.2.1.1 (congrArg (fun p => p.1.1) h)
            simpa using this⟩)
      invFun := fun p => ⟨Sum.elim (fun i => (p.1 i).1)
          (fun js => if js.2 = 0 then (p.2 js.1).1.1 else (p.2 js.1).1.2), by
        have hev : Ev f (Sum.elim (fun i => (p.1 i).1)
            (fun js => if js.2 = 0 then (p.2 js.1).1.1 else (p.2 js.1).1.2)) := by
          refine ⟨fun i => (mem_filter.mp (p.1 i).2).2, fun j => ?_⟩
          simp only [Sum.elim_inr, if_true, Fin.one_eq_zero_iff, if_false]
          exact (mem_filter.mp (p.2 j).2).2.2
        have hord : ∀ j, (Sum.elim (fun i => (p.1 i).1)
            (fun js => if js.2 = 0 then (p.2 js.1).1.1 else (p.2 js.1).1.2) :
              Slot c d → V) (.inr (j, 0)) <
            (Sum.elim (fun i => (p.1 i).1)
              (fun js => if js.2 = 0 then (p.2 js.1).1.1 else (p.2 js.1).1.2) :
                Slot c d → V) (.inr (j, 1)) := by
          intro j
          simp only [Sum.elim_inr, if_true, Fin.one_eq_zero_iff, if_false]
          exact (mem_filter.mp (p.2 j).2).2.1
        refine ⟨⟨inj_of_ev hf hev hord ?_ ?_, hord⟩, hev⟩
        · intro i i' h
          exact p.1.injective (Subtype.ext h)
        · intro j j' h
          simp only [Sum.elim_inr, if_true, Fin.one_eq_zero_iff, if_false] at h
          exact p.2.injective (Subtype.ext h)⟩
      left_inv := by
        intro γ
        apply Subtype.ext
        funext z
        rcases z with i | ⟨j, t⟩
        · rfl
        · rcases fin2_cases t with rfl | rfl <;> simp <;> rfl
      right_inv := by
        intro p
        refine Prod.ext ?_ ?_
        · ext i; rfl
        · ext j <;> simp }
  have := Fintype.card_congr e
  rw [Fintype.card_prod, Fintype.card_embedding_eq, Fintype.card_embedding_eq, Fintype.card_fin,
    Fintype.card_fin, Fintype.card_coe, Fintype.card_coe] at this
  rw [← this, Fintype.card_subtype]

theorem sum_desc :
    ∑ f ∈ (univ : Finset (V × Fin 3 → V × Fin 3)).filter IsFPF,
        (LS f).card.descFactorial c * (DS f).card.descFactorial d =
      ∑ γ ∈ (univ : Finset (Slot c d → V)).filter Disj,
        (((univ : Finset (V × Fin 3 → V × Fin 3)).filter IsFPF).filter (fun f => Ev f γ)).card := by
  rw [sum_congr rfl (fun f hf => desc_mul_desc (mem_filter.mp hf).2)]
  have := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (fun f (γ : Slot c d → V) => Ev f γ)
    (s := (univ : Finset (V × Fin 3 → V × Fin 3)).filter IsFPF)
    (t := (univ : Finset (Slot c d → V)).filter Disj)
  simp only [bipartiteAbove, bipartiteBelow, filter_filter] at this ⊢
  exact this

theorem moment_upper :
    2 ^ d * ∑ f ∈ (univ : Finset (V × Fin 3 → V × Fin 3)).filter IsFPF,
        (LS f).card.descFactorial c * (DS f).card.descFactorial d ≤
      (Fintype.card V).descFactorial (c + d * 2) *
        (3 ^ c * 18 ^ d * Q (Nat.card (V × Fin 3) - 2 * (c + d * 2))) := by
  rw [sum_desc, ← card_disj_mul, Fintype.card_subtype]
  calc 2 ^ d * ∑ γ ∈ (univ : Finset (Slot c d → V)).filter Disj, _
      ≤ 2 ^ d * ∑ γ ∈ (univ : Finset (Slot c d → V)).filter Disj,
          (3 ^ c * 18 ^ d * Q (Nat.card (V × Fin 3) - 2 * (c + d * 2))) := by
        gcongr with γ hγ
        exact ev_upper (mem_filter.mp hγ).2
    _ = _ := by rw [sum_const, smul_eq_mul]; ring

theorem moment_lower :
    ((Fintype.card V).descFactorial (c + d * 2) : ℤ) * ((3 ^ c * 18 ^ d : ℤ) *
        ((Q (Nat.card (V × Fin 3) - 2 * (c + d * 2)) : ℤ) -
          d * Q (Nat.card (V × Fin 3) - 2 * (c + d * 2) - 2))) ≤
      2 ^ d * ((∑ f ∈ (univ : Finset (V × Fin 3 → V × Fin 3)).filter IsFPF,
        (LS f).card.descFactorial c * (DS f).card.descFactorial d : ℕ) : ℤ) := by
  rw [sum_desc, ← card_disj_mul, Fintype.card_subtype]
  push_cast
  rw [mul_comm (((filter Disj univ).card : ℕ) : ℤ), mul_assoc]
  gcongr
  rw [← nsmul_eq_mul, ← sum_const]
  exact sum_le_sum (fun γ hγ => ev_lower (mem_filter.mp hγ).2)

end cubic

/-! Asymptotics of the factorial moments -/

section asym
open Filter Topology

theorem Q_add (m k : ℕ) : Q (m + 2 * k) = Q m * ∏ j ∈ range k, (m + 2 * j + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show m + 2 * (k + 1) = (m + 2 * k) + 2 by ring, Q, ih, prod_range_succ]; ring

theorem Q_even_pos (m : ℕ) : 0 < Q (2 * m) := by
  induction m with
  | zero => simp [Q]
  | succ m ih => rw [show 2 * (m + 1) = 2 * m + 2 by ring, Q]; positivity

theorem term_lim (k j : ℕ) :
    Tendsto (fun n : ℕ => ((2 * n : ℝ) - j) / (6 * n - 2 * k + 2 * j + 1)) atTop (𝓝 (1 / 3)) := by
  have invlim : Tendsto (fun n : ℕ => ((n : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have num := (tendsto_const_nhds (x := (2 : ℝ))).sub ((tendsto_const_nhds (x := (j : ℝ))).mul invlim)
  have den := (tendsto_const_nhds (x := (6 : ℝ))).sub
    ((tendsto_const_nhds (x := (2 * (k : ℝ) - 2 * j - 1))).mul invlim)
  have h := num.div den (by norm_num)
  simp only [mul_zero, sub_zero] at h
  rw [show (1 / 3 : ℝ) = 2 / 6 by norm_num]
  apply h.congr'
  filter_upwards [eventually_ge_atTop (k + 1)] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hkn : (k : ℝ) + 1 ≤ n := by exact_mod_cast hn
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hd : (6 * n - 2 * k + 2 * j + 1 : ℝ) ≠ 0 := by
    apply ne_of_gt; nlinarith
  have e1 : (2 : ℝ) - j * (n : ℝ)⁻¹ = (2 * n - j) / n := by field_simp
  have e2 : (6 : ℝ) - (2 * k - 2 * j - 1) * (n : ℝ)⁻¹ = (6 * n - 2 * k + 2 * j + 1) / n := by
    field_simp; ring
  show (2 - j * (n : ℝ)⁻¹) / (6 - (2 * k - 2 * j - 1) * (n : ℝ)⁻¹) = _
  rw [e1, e2, div_div_div_cancel_right₀ hn0.ne']

theorem prod_lim (k : ℕ) :
    Tendsto (fun n : ℕ => ∏ j ∈ range k, (((2 * n : ℝ) - j) / (6 * n - 2 * k + 2 * j + 1)))
      atTop (𝓝 ((1 / 3) ^ k)) := by
  have := tendsto_finsetProd (range k) (fun j _ => term_lim k j)
  simpa [prod_const, card_range] using this

theorem ratio_eq (n k : ℕ) (hk : k ≤ n) :
    ((2 * n).descFactorial k : ℝ) * Q (6 * n - 2 * k) / Q (6 * n) =
      ∏ j ∈ range k, (((2 * n : ℝ) - j) / (6 * n - 2 * k + 2 * j + 1)) := by
  have hQ : Q (6 * n) = Q (6 * n - 2 * k) * ∏ j ∈ range k, (6 * n - 2 * k + 2 * j + 1) := by
    have := Q_add (6 * n - 2 * k) k
    rwa [Nat.sub_add_cancel (by omega)] at this
  have hpos : (0 : ℝ) < Q (6 * n - 2 * k) := by
    have := Q_even_pos (3 * n - k)
    rw [show 2 * (3 * n - k) = 6 * n - 2 * k by omega] at this
    exact_mod_cast this
  have hA : ((2 * n).descFactorial k : ℝ) = ∏ j ∈ range k, ((2 * n : ℝ) - j) := by
    rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
    refine prod_congr rfl (fun j hj => ?_)
    have := mem_range.mp hj
    rw [Nat.cast_sub (by omega)]
    push_cast; ring
  have hB : ((∏ j ∈ range k, (6 * n - 2 * k + 2 * j + 1) : ℕ) : ℝ) =
      ∏ j ∈ range k, (6 * n - 2 * k + 2 * j + 1 : ℝ) := by
    rw [Nat.cast_prod]
    refine prod_congr rfl (fun j _ => ?_)
    rw [Nat.cast_add, Nat.cast_add, Nat.cast_sub (by omega)]
    push_cast; ring
  rw [hQ, Nat.cast_mul, hA, hB, prod_div_distrib]
  field_simp

theorem ratio2_eq (n k : ℕ) (hk : k + 1 ≤ n) :
    ((2 * n).descFactorial k : ℝ) * Q (6 * n - 2 * k - 2) / Q (6 * n) =
      (∏ j ∈ range k, (((2 * n : ℝ) - j) / (6 * n - 2 * k + 2 * j + 1))) /
        (6 * n - 2 * k - 1) := by
  rw [← ratio_eq n k (by omega)]
  have hQ : Q (6 * n - 2 * k) = (6 * n - 2 * k - 1) * Q (6 * n - 2 * k - 2) := by
    rw [show 6 * n - 2 * k = (6 * n - 2 * k - 2) + 2 by omega, Q]
    congr 1
  rw [hQ]
  have h1 : ((6 * n - 2 * k - 1 : ℕ) : ℝ) = 6 * n - 2 * k - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
  push_cast
  rw [h1]
  have hd : (6 * n - 2 * k - 1 : ℝ) ≠ 0 := by
    have : (k : ℝ) + 1 ≤ n := by exact_mod_cast hk
    apply ne_of_gt; linarith
  field_simp

noncomputable def Om (n : ℕ) : Finset (Fin (2 * n) × Fin 3 → Fin (2 * n) × Fin 3) :=
  univ.filter IsFPF

theorem Q_six_pos (n : ℕ) : (0 : ℝ) < Q (6 * n) := by
  have := Q_even_pos (3 * n)
  rw [show 2 * (3 * n) = 6 * n by ring] at this
  exact_mod_cast this

theorem card_om (n : ℕ) : (Om n).card = Q (6 * n) := by
  have := card_fpf (Fin (2 * n) × Fin 3)
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at this
  rw [Om, this, Nat.card_prod, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Fintype.card_fin, Fintype.card_fin]
  ring_nf

theorem mom_lim (c d : ℕ) :
    Tendsto (fun n : ℕ => (∑ f ∈ Om n, ((LS f).card.choose c * (DS f).card.choose d : ℝ)) /
      Q (6 * n)) atTop (𝓝 (1 / (c.factorial * d.factorial))) := by
  set k := c + d * 2
  let X : ℕ → ℝ := fun n =>
    (2 ^ d * ∑ f ∈ Om n, ((LS f).card.descFactorial c * (DS f).card.descFactorial d : ℝ)) / Q (6 * n)
  let r : ℕ → ℝ := fun n => ∏ j ∈ range k, (((2 * n : ℝ) - j) / (6 * n - 2 * k + 2 * j + 1))
  have hM : ∀ n, Nat.card (Fin (2 * n) × Fin 3) - 2 * (c + d * 2) = 6 * n - 2 * k := by
    intro n; rw [Nat.card_prod, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      Fintype.card_fin, Fintype.card_fin]; omega
  have hup : ∀ n, k ≤ n → X n ≤ 3 ^ c * 18 ^ d * r n := by
    intro n hn
    have h := moment_upper (V := Fin (2 * n)) (c := c) (d := d)
    rw [hM, Fintype.card_fin] at h
    have h' : (2 ^ d * ∑ f ∈ Om n, ((LS f).card.descFactorial c * (DS f).card.descFactorial d : ℝ)) ≤
        ((2 * n).descFactorial k : ℝ) * (3 ^ c * 18 ^ d * Q (6 * n - 2 * k)) := by
      exact_mod_cast h
    simp only [X, r]
    rw [← ratio_eq n k hn, div_le_iff₀ (Q_six_pos n)]
    calc _ ≤ _ := h'
      _ = _ := by have hQ0 := (Q_six_pos n).ne'; field_simp
  have hlo : ∀ n, k + 1 ≤ n → 3 ^ c * 18 ^ d * (r n - d * (r n / (6 * n - 2 * k - 1))) ≤ X n := by
    intro n hn
    have h := moment_lower (V := Fin (2 * n)) (c := c) (d := d)
    rw [hM, Fintype.card_fin] at h
    have h' : ((2 * n).descFactorial k : ℝ) * ((3 ^ c * 18 ^ d : ℝ) *
        ((Q (6 * n - 2 * k) : ℝ) - d * Q (6 * n - 2 * k - 2))) ≤
        (2 ^ d * ∑ f ∈ Om n, ((LS f).card.descFactorial c * (DS f).card.descFactorial d : ℝ)) := by
      have := (Int.cast_le (R := ℝ)).mpr h
      push_cast at this
      simpa [Om] using this
    simp only [X, r]
    rw [← ratio2_eq n k hn, ← ratio_eq n k (by omega), le_div_iff₀ (Q_six_pos n)]
    have hQ0 := (Q_six_pos n).ne'
    calc _ = ((2 * n).descFactorial k : ℝ) * ((3 ^ c * 18 ^ d : ℝ) *
        ((Q (6 * n - 2 * k) : ℝ) - d * Q (6 * n - 2 * k - 2))) := by
          field_simp
      _ ≤ _ := h'
  have hr := prod_lim k
  have hr2 : Tendsto (fun n : ℕ => r n / (6 * n - 2 * k - 1)) atTop (𝓝 0) := by
    have hden : Tendsto (fun n : ℕ => (6 * n - 2 * k - 1 : ℝ)) atTop atTop := by
      apply tendsto_atTop_add_const_right
      apply tendsto_atTop_add_const_right
      exact (tendsto_natCast_atTop_atTop).const_mul_atTop (by norm_num)
    exact hr.div_atTop hden
  have hlim : (3 : ℝ) ^ c * 18 ^ d * (1 / 3) ^ k = 2 ^ d := by
    have e1 : (1 / 3 : ℝ) ^ k = (1 / 3) ^ c * (1 / 9) ^ d := by
      simp only [k]; rw [pow_add, mul_comm d 2, pow_mul]; norm_num
    have e2 : (18 : ℝ) ^ d = 2 ^ d * 9 ^ d := by rw [← mul_pow]; norm_num
    rw [e1, e2]
    calc (3 : ℝ) ^ c * (2 ^ d * 9 ^ d) * ((1 / 3) ^ c * (1 / 9) ^ d)
        = 2 ^ d * ((3 * (1 / 3)) ^ c * (9 * (1 / 9)) ^ d) := by rw [mul_pow, mul_pow]; ring
      _ = 2 ^ d := by norm_num
  have hX : Tendsto X atTop (𝓝 (2 ^ d)) := by
    have hu : Tendsto (fun n => 3 ^ c * 18 ^ d * r n) atTop (𝓝 (2 ^ d)) := by
      rw [← hlim]; exact hr.const_mul _
    have hl : Tendsto (fun n => 3 ^ c * 18 ^ d * (r n - d * (r n / (6 * n - 2 * k - 1))))
        atTop (𝓝 (2 ^ d)) := by
      rw [← hlim]
      have := (hr.sub (hr2.const_mul (d : ℝ))).const_mul ((3 : ℝ) ^ c * 18 ^ d)
      simp only [mul_zero, sub_zero] at this
      exact this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hu
      (eventually_atTop.mpr ⟨k + 1, hlo⟩) (eventually_atTop.mpr ⟨k, hup⟩)
  have hfac : (0 : ℝ) < c.factorial * d.factorial := by positivity
  have := hX.div_const ((2 : ℝ) ^ d * (c.factorial * d.factorial))
  rw [show (2 : ℝ) ^ d / (2 ^ d * (c.factorial * d.factorial)) = 1 / (c.factorial * d.factorial) by
    field_simp] at this
  refine this.congr (fun n => ?_)
  have hs : (∑ f ∈ Om n, ((LS f).card.descFactorial c * (DS f).card.descFactorial d : ℝ)) =
      (c.factorial * d.factorial) * ∑ f ∈ Om n, ((LS f).card.choose c * (DS f).card.choose d : ℝ) := by
    rw [mul_sum]
    refine sum_congr rfl (fun f _ => ?_)
    rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_factorial_mul_choose]
    push_cast; ring
  simp only [X]
  rw [hs]
  have hQ0 := (Q_six_pos n).ne'
  field_simp

end asym

/-! Bonferroni: the probability of a simple configuration tends to `exp (-2)` -/

section bonf
open Filter Topology

theorem alt_bounds (b t : ℕ) :
    (∑ j ∈ range (2 * t + 2), ((-1 : ℤ) ^ j * b.choose j)) ≤ (if b = 0 then 1 else 0) ∧
    (if b = 0 then (1 : ℤ) else 0) ≤ ∑ j ∈ range (2 * t + 1), ((-1 : ℤ) ^ j * b.choose j) := by
  cases b with
  | zero =>
    have one_sum (u : ℕ) : (∑ j ∈ range (u + 1), ((-1 : ℤ) ^ j * (0 : ℕ).choose j)) = 1 := by
      rw [sum_range_succ']
      simp [Nat.choose_eq_zero_of_lt]
    rw [show 2 * t + 2 = (2 * t + 1) + 1 by omega, one_sum, one_sum]
    simp
  | succ b =>
    rw [show 2 * t + 2 = (2 * t + 1) + 1 by omega]
    rw [Int.alternating_sum_range_choose_eq_choose, Int.alternating_sum_range_choose_eq_choose]
    simp [pow_add, pow_mul]

theorem sum_inv_fact (j : ℕ) :
    ∑ p ∈ antidiagonal j, (1 / ((p.1.factorial : ℝ) * p.2.factorial)) = 2 ^ j / j.factorial := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => 1 / ((a.factorial : ℝ) * b.factorial))]
  have h : ∀ k ∈ range j.succ, 1 / ((k.factorial : ℝ) * (j - k).factorial) =
      (j.choose k : ℝ) / j.factorial := by
    intro k hk
    have hk' : k ≤ j := Nat.lt_succ_iff.mp (mem_range.mp hk)
    rw [Nat.cast_choose ℝ hk']
    field_simp
  rw [sum_congr rfl h, ← sum_div]
  congr 1
  have := Nat.sum_range_choose j
  exact_mod_cast this

theorem S_lim (j : ℕ) :
    Tendsto (fun n : ℕ => (∑ f ∈ Om n, (((LS f).card + (DS f).card).choose j : ℝ)) / Q (6 * n))
      atTop (𝓝 (2 ^ j / j.factorial)) := by
  have hsplit : ∀ n, (∑ f ∈ Om n, (((LS f).card + (DS f).card).choose j : ℝ)) / Q (6 * n) =
      ∑ p ∈ antidiagonal j,
        (∑ f ∈ Om n, ((LS f).card.choose p.1 * (DS f).card.choose p.2 : ℝ)) / Q (6 * n) := by
    intro n
    rw [← sum_div]
    congr 1
    rw [sum_comm]
    refine sum_congr rfl (fun f _ => ?_)
    rw [Nat.add_choose_eq]
    push_cast
    rfl
  have hlim := tendsto_finset_sum (antidiagonal j) (fun p _ => mom_lim p.1 p.2)
  rw [← sum_inv_fact]
  exact hlim.congr (fun n => (hsplit n).symm)

theorem exp_series_lim :
    Tendsto (fun m => ∑ j ∈ range m, (-1 : ℝ) ^ j * (2 ^ j / j.factorial)) atTop
      (𝓝 (Real.exp (-2))) := by
  have h := NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) (-2)
  rw [← Real.exp_eq_exp_ℝ] at h
  have := h.tendsto_sum_nat
  refine this.congr (fun m => sum_congr rfl (fun j _ => ?_))
  rw [neg_pow, mul_div_assoc]

theorem simple_lim :
    Tendsto (fun n : ℕ => (((Om n).filter (fun f => (LS f).card + (DS f).card = 0)).card : ℝ) /
      Q (6 * n)) atTop (𝓝 (Real.exp (-2))) := by
  let P : ℕ → ℝ := fun n =>
    (((Om n).filter (fun f => (LS f).card + (DS f).card = 0)).card : ℝ) / Q (6 * n)
  let T : ℕ → ℕ → ℝ := fun m n => ∑ j ∈ range m, (-1 : ℝ) ^ j *
    ((∑ f ∈ Om n, (((LS f).card + (DS f).card).choose j : ℝ)) / Q (6 * n))
  have hT : ∀ m, Tendsto (T m) atTop (𝓝 (∑ j ∈ range m, (-1 : ℝ) ^ j * (2 ^ j / j.factorial))) :=
    fun m => tendsto_finset_sum _ (fun j _ => (S_lim j).const_mul _)
  have hTe : ∀ m n, T m n = (∑ f ∈ Om n, ∑ j ∈ range m,
      (-1 : ℝ) ^ j * (((LS f).card + (DS f).card).choose j : ℝ)) / Q (6 * n) := by
    intro m n
    calc T m n = ∑ j ∈ range m, ∑ f ∈ Om n, (-1 : ℝ) ^ j *
          (((LS f).card + (DS f).card).choose j : ℝ) / Q (6 * n) := by
          simp only [T]
          refine sum_congr rfl (fun j _ => ?_)
          rw [sum_div, mul_sum]
          refine sum_congr rfl (fun f _ => ?_)
          ring
      _ = ∑ f ∈ Om n, ∑ j ∈ range m, (-1 : ℝ) ^ j *
          (((LS f).card + (DS f).card).choose j : ℝ) / Q (6 * n) := sum_comm
      _ = _ := by
          rw [sum_div]
          refine sum_congr rfl (fun f _ => ?_)
          rw [sum_div]
  have hPe : ∀ n, P n = (∑ f ∈ Om n,
      (if (LS f).card + (DS f).card = 0 then (1 : ℝ) else 0)) / Q (6 * n) := by
    intro n
    simp only [P]
    rw [sum_boole]
  have hlow : ∀ t n, T (2 * t + 2) n ≤ P n := by
    intro t n
    rw [hTe, hPe]
    apply div_le_div_of_nonneg_right _ (Q_six_pos n).le
    apply sum_le_sum
    intro f _
    have := (alt_bounds ((LS f).card + (DS f).card) t).1
    have := (Int.cast_le (R := ℝ)).mpr this
    push_cast at this
    convert this using 2 <;> split_ifs <;> simp
  have hupp : ∀ t n, P n ≤ T (2 * t + 1) n := by
    intro t n
    rw [hTe, hPe]
    apply div_le_div_of_nonneg_right _ (Q_six_pos n).le
    apply sum_le_sum
    intro f _
    have := (alt_bounds ((LS f).card + (DS f).card) t).2
    have := (Int.cast_le (R := ℝ)).mpr this
    push_cast at this
    convert this using 1 <;> split_ifs <;> simp
  have hev : Tendsto (fun t : ℕ => 2 * t + 2) atTop atTop :=
    tendsto_atTop_mono (fun t => by show t ≤ 2 * t + 2; omega) tendsto_id
  have hod : Tendsto (fun t : ℕ => 2 * t + 1) atTop atTop :=
    tendsto_atTop_mono (fun t => by show t ≤ 2 * t + 1; omega) tendsto_id
  rw [tendsto_order]
  constructor
  · intro a ha
    obtain ⟨t, ht⟩ := ((exp_series_lim.comp hev).eventually (lt_mem_nhds ha)).exists
    filter_upwards [(hT (2 * t + 2)).eventually (lt_mem_nhds ht)] with n hn
    exact lt_of_lt_of_le hn (hlow t n)
  · intro b hb
    obtain ⟨t, ht⟩ := ((exp_series_lim.comp hod).eventually (gt_mem_nhds hb)).exists
    filter_upwards [(hT (2 * t + 1)).eventually (gt_mem_nhds ht)] with n hn
    exact lt_of_le_of_lt (hupp t n) hn

end bonf

/-! Simple configurations and labelled cubic graphs -/

section graph
variable {V : Type} [Fintype V] [LinearOrder V]

def Gr (f : V × Fin 3 → V × Fin 3) : SimpleGraph V :=
  SimpleGraph.fromRel (fun v w => ∃ a b, f (v, a) = (w, b))

theorem noLoop_of {f : V × Fin 3 → V × Fin 3} (hs : (LS f).card + (DS f).card = 0) (v : V) :
    ¬ Loop f v := by
  intro h
  have : (LS f).card = 0 := by omega
  rw [card_eq_zero, LS, filter_eq_empty_iff] at this
  exact this (mem_univ v) h

theorem noDbl_of {f : V × Fin 3 → V × Fin 3} (hs : (LS f).card + (DS f).card = 0) {v w : V}
    (hvw : v < w) : ¬ Dbl f v w := by
  intro h
  have : (DS f).card = 0 := by omega
  rw [card_eq_zero, DS, filter_eq_empty_iff] at this
  exact this (mem_univ (v, w)) ⟨hvw, h⟩

theorem noloop {f : V × Fin 3 → V × Fin 3} (hf : IsFPF f) (hs : (LS f).card + (DS f).card = 0)
    (v : V) (a : Fin 3) : (f (v, a)).1 ≠ v := by
  intro h
  set b := (f (v, a)).2
  have hfa : f (v, a) = (v, b) := Prod.ext h rfl
  have hab : a ≠ b := fun e => (hf (v, a)).1 (by rw [hfa, e])
  rcases lt_or_gt_of_ne hab with hl | hl
  · exact noLoop_of hs v ⟨⟨![a, b], by simpa using hl⟩, by simpa using hfa⟩
  · have hfb : f (v, b) = (v, a) := by rw [← hfa, (hf _).2]
    exact noLoop_of hs v ⟨⟨![b, a], by simpa using hl⟩, by simpa using hfb⟩

theorem dbl_of {f : V × Fin 3 → V × Fin 3} {v w : V} {a a' b b' : Fin 3} (ha : a ≠ a') (hb : b ≠ b')
    (h1 : f (v, a) = (w, b)) (h2 : f (v, a') = (w, b')) : Dbl f v w := by
  rcases lt_or_gt_of_ne ha with hl | hl
  · refine ⟨⟨(![a, a'], ![b, b']), by simpa using hl, by simpa using hb⟩, fun s => ?_⟩
    rcases fin2_cases s with rfl | rfl <;> simpa
  · refine ⟨⟨(![a', a], ![b', b]), by simpa using hl, by simpa using hb.symm⟩, fun s => ?_⟩
    rcases fin2_cases s with rfl | rfl <;> simpa

theorem nodbl {f : V × Fin 3 → V × Fin 3} (hf : IsFPF f) (hs : (LS f).card + (DS f).card = 0)
    (v : V) {a a' : Fin 3} (h : (f (v, a)).1 = (f (v, a')).1) : a = a' := by
  by_contra ha
  set w := (f (v, a)).1
  set b := (f (v, a)).2
  set b' := (f (v, a')).2
  have h1 : f (v, a) = (w, b) := rfl
  have h2 : f (v, a') = (w, b') := Prod.ext h.symm rfl
  have hb : b ≠ b' := by
    intro e
    have : f (v, a) = f (v, a') := by rw [h1, h2, e]
    exact ha (by simpa using fpf_inj hf this)
  have hvw : v ≠ w := (noloop hf hs v a).symm
  rcases lt_or_gt_of_ne hvw with hl | hl
  · exact noDbl_of hs hl (dbl_of ha hb h1 h2)
  · have h1' : f (w, b) = (v, a) := by rw [← h1, (hf _).2]
    have h2' : f (w, b') = (v, a') := by rw [← h2, (hf _).2]
    exact noDbl_of hs hl (dbl_of hb ha h1' h2')

theorem gr_adj {f : V × Fin 3 → V × Fin 3} (hf : IsFPF f) (hs : (LS f).card + (DS f).card = 0)
    (v w : V) : (Gr f).Adj v w ↔ ∃ a, (f (v, a)).1 = w := by
  rw [Gr, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨-, ⟨a, b, h⟩ | ⟨a, b, h⟩⟩
    · exact ⟨a, by rw [h]⟩
    · refine ⟨b, ?_⟩
      have : f (v, b) = (w, a) := by rw [← h, (hf _).2]
      rw [this]
  · rintro ⟨a, rfl⟩
    exact ⟨(noloop hf hs v a).symm, Or.inl ⟨a, (f (v, a)).2, rfl⟩⟩

theorem gr_cubic {f : V × Fin 3 → V × Fin 3} (hf : IsFPF f) (hs : (LS f).card + (DS f).card = 0)
    (v : V) : ((Gr f).neighborFinset v).card = 3 := by
  have : (Gr f).neighborFinset v = univ.image (fun a => (f (v, a)).1) := by
    ext w
    rw [SimpleGraph.mem_neighborFinset, gr_adj hf hs, mem_image]
    simp
  rw [this, card_image_of_injective _ (fun a a' h => nodbl hf hs v h), card_univ, Fintype.card_fin]

theorem card_fibre (G : SimpleGraph V) (hG : ∀ v, (G.neighborFinset v).card = 3) :
    Nat.card {f : V × Fin 3 → V × Fin 3 // IsFPF f ∧ (LS f).card + (DS f).card = 0 ∧ Gr f = G} =
      6 ^ Fintype.card V := by
  have hN : ∀ v, Fintype.card (G.neighborSet v) = 3 := by
    intro v; rw [SimpleGraph.card_neighborSet_eq_degree]; exact hG v
  let fwd : {f : V × Fin 3 → V × Fin 3 // IsFPF f ∧ (LS f).card + (DS f).card = 0 ∧ Gr f = G} →
      ∀ v, Fin 3 ≃ G.neighborSet v := fun f v =>
    Equiv.ofBijective (fun a => ⟨(f.1 (v, a)).1, by
        have h := (gr_adj f.2.1 f.2.2.1 v (f.1 (v, a)).1).mpr ⟨a, rfl⟩
        rw [f.2.2.2] at h
        exact h⟩)
      ((Fintype.bijective_iff_injective_and_card _).mpr
        ⟨fun a a' h => nodbl f.2.1 f.2.2.1 v (congrArg Subtype.val h), by
          rw [Fintype.card_fin, hN]⟩)
  let bwd : (∀ v, Fin 3 ≃ G.neighborSet v) → V × Fin 3 → V × Fin 3 := fun L t =>
    ((L t.1 t.2).1, (L (L t.1 t.2).1).symm ⟨t.1, G.adj_symm (L t.1 t.2).2⟩)
  have key : ∀ (L : ∀ v, Fin 3 ≃ G.neighborSet v) (v : V) (a : Fin 3) (x : V) (hx : x = v)
      (h : (L v a).1 ∈ G.neighborSet x), (L x).symm ⟨(L v a).1, h⟩ = a := by
    rintro L v a x rfl h
    rw [Equiv.symm_apply_eq]
  have bwd_fpf : ∀ L, IsFPF (bwd L) := by
    intro L t
    refine ⟨fun h => G.irrefl (by
      have := congrArg Prod.fst h
      simp only [bwd] at this
      have h2 := (L t.1 t.2).2
      rw [this] at h2
      exact h2), ?_⟩
    have e1 : (L (L t.1 t.2).1 ((L (L t.1 t.2).1).symm ⟨t.1, G.adj_symm (L t.1 t.2).2⟩)).1 = t.1 := by
      rw [Equiv.apply_symm_apply]
    refine Prod.ext ?_ ?_
    · exact e1
    · exact key L t.1 t.2 _ e1 _
  have bwd_simple : ∀ L, (LS (bwd L)).card + (DS (bwd L)).card = 0 := by
    intro L
    have h1 : LS (bwd L) = ∅ := by
      rw [LS, filter_eq_empty_iff]
      rintro v - ⟨q, hq⟩
      have := congrArg Prod.fst hq
      simp only [bwd] at this
      have h2 := (L v (q.1 0)).2
      rw [this] at h2
      exact G.irrefl h2
    have h2 : DS (bwd L) = ∅ := by
      rw [DS, filter_eq_empty_iff]
      rintro ⟨v, w⟩ - ⟨-, q, hq⟩
      have e0 := congrArg Prod.fst (hq 0)
      have e1 := congrArg Prod.fst (hq 1)
      simp only [bwd] at e0 e1
      have := (L v).injective (Subtype.ext (e0.trans e1.symm))
      exact absurd this (ne_of_lt q.2.1)
    rw [h1, h2]; rfl
  have bwd_gr : ∀ L, Gr (bwd L) = G := by
    intro L
    ext v w
    rw [gr_adj (bwd_fpf L) (bwd_simple L)]
    constructor
    · rintro ⟨a, rfl⟩
      exact (L v a).2
    · intro h
      exact ⟨(L v).symm ⟨w, h⟩, by simp [bwd]⟩
  let e : {f : V × Fin 3 → V × Fin 3 // IsFPF f ∧ (LS f).card + (DS f).card = 0 ∧ Gr f = G} ≃
      ∀ v, Fin 3 ≃ G.neighborSet v :=
    { toFun := fwd
      invFun := fun L => ⟨bwd L, bwd_fpf L, bwd_simple L, bwd_gr L⟩
      left_inv := by
        rintro ⟨f, hf, hs, hg⟩
        apply Subtype.ext
        funext t
        obtain ⟨v, a⟩ := t
        refine Prod.ext rfl ((Equiv.symm_apply_eq _).mpr ?_)
        apply Subtype.ext
        show (v : V) = (f ((f (v, a)).1, (f (v, a)).2)).1
        rw [Prod.mk.eta, (hf _).2]
      right_inv := by
        intro L
        funext v
        apply Equiv.ext
        intro a
        rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_pi]
  rw [prod_congr rfl (fun v _ => Fintype.card_equiv (Fintype.equivOfCardEq (by
    rw [Fintype.card_fin, hN])))]
  simp [Nat.factorial]

end graph

theorem count_conn (n : ℕ) :
    ((Om n).filter (fun f => (LS f).card + (DS f).card = 0 ∧ (Gr f).Connected)).card =
      OMA.S_oeis_a004109.a n * 6 ^ (2 * n) := by
  set A := (univ : Finset (SimpleGraph (Fin (2 * n)))).filter
    (fun G => G.Connected ∧ ∀ v, (G.neighborFinset v).card = 3) with hA
  have hmaps : ∀ f ∈ (Om n).filter (fun f => (LS f).card + (DS f).card = 0 ∧ (Gr f).Connected),
      Gr f ∈ A := by
    intro f hf
    simp only [Om, mem_filter, mem_univ, true_and] at hf
    exact mem_filter.mpr ⟨mem_univ _, hf.2.2, gr_cubic hf.1 hf.2.1⟩
  rw [card_eq_sum_card_fiberwise hmaps]
  have hfib : ∀ G ∈ A, (((Om n).filter (fun f => (LS f).card + (DS f).card = 0 ∧
      (Gr f).Connected)).filter (fun f => Gr f = G)).card = 6 ^ (2 * n) := by
    intro G hG
    have hG' := (mem_filter.mp hG).2
    rw [filter_filter, Om, card_filter_fpf]
    have hcf := card_fibre G hG'.2
    rw [Fintype.card_fin] at hcf
    rw [← hcf]
    refine Nat.card_congr (Equiv.subtypeEquivRight (fun f => and_congr_right (fun _ => ?_)))
    constructor
    · rintro ⟨⟨h1, -⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨⟨h1, h3 ▸ hG'.1⟩, h3⟩
  rw [sum_congr rfl hfib, sum_const, smul_eq_mul]
  rfl

/-! Disconnected configurations -/
open Filter Topology

section closed
variable {V : Type} [Fintype V] [LinearOrder V]

def Closed (f : V × Fin 3 → V × Fin 3) (S : Finset V) : Prop :=
  ∀ t : V × Fin 3, t.1 ∈ S → (f t).1 ∈ S

noncomputable def glue (S : Finset V) (g : {t : V × Fin 3 // t.1 ∈ S} → {t : V × Fin 3 // t.1 ∈ S})
    (h : {t : V × Fin 3 // t.1 ∉ S} → {t : V × Fin 3 // t.1 ∉ S}) (t : V × Fin 3) : V × Fin 3 :=
  if ht : t.1 ∈ S then (g ⟨t, ht⟩).1 else (h ⟨t, ht⟩).1

theorem card_closed (S : Finset V) :
    Nat.card {f : V × Fin 3 → V × Fin 3 // IsFPF f ∧ Closed f S} =
      Q (3 * S.card) * Q (3 * (Fintype.card V - S.card)) := by
  have compl : ∀ f : V × Fin 3 → V × Fin 3, IsFPF f → Closed f S →
      ∀ t : V × Fin 3, t.1 ∉ S → (f t).1 ∉ S := by
    intro f hf hc t ht h
    exact ht (by have := hc (f t) h; rwa [(hf t).2] at this)
  have gin : ∀ g h (t : V × Fin 3) (ht : t.1 ∈ S), glue S g h t = (g ⟨t, ht⟩).1 :=
    fun g h t ht => dif_pos ht
  have gout : ∀ g h (t : V × Fin 3) (ht : t.1 ∉ S), glue S g h t = (h ⟨t, ht⟩).1 :=
    fun g h t ht => dif_neg ht
  let e : {f : V × Fin 3 → V × Fin 3 // IsFPF f ∧ Closed f S} ≃
      {g : {t : V × Fin 3 // t.1 ∈ S} → {t : V × Fin 3 // t.1 ∈ S} // IsFPF g} ×
        {h : {t : V × Fin 3 // t.1 ∉ S} → {t : V × Fin 3 // t.1 ∉ S} // IsFPF h} :=
    { toFun := fun f => (⟨fun t => ⟨f.1 t.1, f.2.2 t.1 t.2⟩, fun t =>
          ⟨fun h => (f.2.1 t.1).1 (congrArg Subtype.val h), Subtype.ext (f.2.1 t.1).2⟩⟩,
        ⟨fun t => ⟨f.1 t.1, compl f.1 f.2.1 f.2.2 t.1 t.2⟩, fun t =>
          ⟨fun h => (f.2.1 t.1).1 (congrArg Subtype.val h), Subtype.ext (f.2.1 t.1).2⟩⟩)
      invFun := fun p => ⟨glue S p.1.1 p.2.1, by
          intro t
          by_cases ht : t.1 ∈ S
          · rw [gin _ _ t ht, gin _ _ _ (p.1.1 ⟨t, ht⟩).2]
            exact ⟨fun h => (p.1.2 ⟨t, ht⟩).1 (Subtype.ext h),
              congrArg Subtype.val (p.1.2 ⟨t, ht⟩).2⟩
          · rw [gout _ _ t ht, gout _ _ _ (p.2.1 ⟨t, ht⟩).2]
            exact ⟨fun h => (p.2.2 ⟨t, ht⟩).1 (Subtype.ext h),
              congrArg Subtype.val (p.2.2 ⟨t, ht⟩).2⟩, by
          intro t ht
          rw [gin _ _ t ht]
          exact (p.1.1 ⟨t, ht⟩).2⟩
      left_inv := by
        intro f
        apply Subtype.ext
        funext t
        by_cases ht : t.1 ∈ S
        · exact gin _ _ t ht
        · exact gout _ _ t ht
      right_inv := by
        intro p
        refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
        · funext t; exact Subtype.ext (gin _ _ t.1 t.2)
        · funext t; exact Subtype.ext (gout _ _ t.1 t.2) }
  rw [Nat.card_congr e, Nat.card_prod, card_fpf, card_fpf]
  have h1 : Nat.card {t : V × Fin 3 // t.1 ∈ S} = 3 * S.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    have : (univ.filter fun t : V × Fin 3 => t.1 ∈ S) = S ×ˢ univ := by ext t; simp
    rw [this, card_product, card_univ, Fintype.card_fin, mul_comm]
  have h2 : Nat.card {t : V × Fin 3 // t.1 ∉ S} = 3 * (Fintype.card V - S.card) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    have : (univ.filter fun t : V × Fin 3 => t.1 ∉ S) = Sᶜ ×ˢ univ := by ext t; simp
    rw [this, card_product, card_univ, Fintype.card_fin, card_compl, mul_comm]
  rw [h1, h2]

end closed

theorem exists_closed {n : ℕ} (hn : 1 ≤ n) {f : Fin (2 * n) × Fin 3 → Fin (2 * n) × Fin 3}
    (hc : ¬ (Gr f).Connected) :
    ∃ S : Finset (Fin (2 * n)), 1 ≤ S.card ∧ S.card ≤ n ∧ Closed f S := by
  have hne : Nonempty (Fin (2 * n)) := ⟨⟨0, by omega⟩⟩
  have hp : ¬ (Gr f).Preconnected := fun h => hc ((SimpleGraph.connected_iff _).mpr ⟨h, hne⟩)
  simp only [SimpleGraph.Preconnected, not_forall] at hp
  obtain ⟨u, w, huw⟩ := hp
  have adj : ∀ x a, (f (x, a)).1 ≠ x → (Gr f).Adj x (f (x, a)).1 := by
    intro x a h
    rw [Gr, SimpleGraph.fromRel_adj]
    exact ⟨Ne.symm h, Or.inl ⟨a, _, rfl⟩⟩
  set S := (univ : Finset (Fin (2 * n))).filter (fun x => (Gr f).Reachable u x)
  set Sc := (univ : Finset (Fin (2 * n))).filter (fun x => ¬ (Gr f).Reachable u x)
  have cS : Closed f S := by
    rintro ⟨x, a⟩ hx
    simp only [S, mem_filter, mem_univ, true_and] at hx ⊢
    by_cases h : (f (x, a)).1 = x
    · rw [h]; exact hx
    · exact hx.trans (adj x a h).reachable
  have cSc : Closed f Sc := by
    rintro ⟨x, a⟩ hx
    simp only [Sc, mem_filter, mem_univ, true_and] at hx ⊢
    intro hy
    by_cases h : (f (x, a)).1 = x
    · rw [h] at hy; exact hx hy
    · exact hx (hy.trans (adj x a h).symm.reachable)
  have hsum : S.card + Sc.card = 2 * n := by
    rw [card_filter_add_card_filter_not, card_univ, Fintype.card_fin]
  have hu : 1 ≤ S.card := card_pos.mpr ⟨u, by simp [S]⟩
  have hw : 1 ≤ Sc.card := card_pos.mpr ⟨w, by simp [Sc, huw]⟩
  by_cases h : S.card ≤ n
  · exact ⟨S, hu, h, cS⟩
  · exact ⟨Sc, hw, by omega, cSc⟩

theorem disc_bound (n : ℕ) (hn : 1 ≤ n) :
    ((Om n).filter (fun f => ¬ (Gr f).Connected)).card ≤
      ∑ s ∈ Icc 1 n, (2 * n).choose s * (Q (3 * s) * Q (3 * (2 * n - s))) := by
  set F := (univ : Finset (Finset (Fin (2 * n)))).filter (fun S => 1 ≤ S.card ∧ S.card ≤ n)
  calc _ ≤ (F.biUnion (fun S => (Om n).filter (fun f => Closed f S))).card := by
        apply card_le_card
        intro f hf
        rw [mem_filter] at hf
        obtain ⟨S, h1, h2, h3⟩ := exists_closed hn hf.2
        exact mem_biUnion.mpr ⟨S, mem_filter.mpr ⟨mem_univ _, h1, h2⟩, mem_filter.mpr ⟨hf.1, h3⟩⟩
    _ ≤ ∑ S ∈ F, ((Om n).filter (fun f => Closed f S)).card := card_biUnion_le
    _ = ∑ S ∈ F, Q (3 * S.card) * Q (3 * (2 * n - S.card)) := by
        refine sum_congr rfl (fun S _ => ?_)
        rw [Om, card_filter_fpf, card_closed, Fintype.card_fin]
    _ = ∑ s ∈ Icc 1 n, ∑ S ∈ F with S.card = s, Q (3 * S.card) * Q (3 * (2 * n - S.card)) :=
        (sum_fiberwise_of_maps_to (fun S hS => by
          rw [mem_filter] at hS; exact mem_Icc.mpr hS.2) _).symm
    _ = _ := by
        refine sum_congr rfl (fun s hs => ?_)
        rw [sum_congr rfl (fun S hS => by rw [(mem_filter.mp hS).2]), sum_const, smul_eq_mul]
        congr 1
        have : (F.filter fun S => S.card = s) = (univ : Finset (Finset (Fin (2 * n)))).filter
            (fun S => S.card = s) := by
          ext S
          simp only [F, mem_filter, mem_univ, true_and]
          constructor
          · exact fun h => h.2
          · intro h; rw [h]; exact ⟨mem_Icc.mp hs, rfl⟩
        rw [this, univ_filter_card_eq, card_powersetCard, card_univ, Fintype.card_fin]


/-! Binomial estimates for closed vertex sets -/

theorem Q_odd (m : ℕ) : Q (2 * m + 1) = 0 := by
  induction m with
  | zero => rfl
  | succ m ih => rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 2 by ring, Q, ih, mul_zero]

theorem Q_fact (m : ℕ) : Q (2 * m) * (m.factorial * 2 ^ m) = (2 * m).factorial := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 2 by ring, Q, Nat.factorial_succ, pow_succ,
      show 2 * m + 2 = (2 * m + 1) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ, ← ih]
    ring

theorem Q_real (m : ℕ) : (Q (2 * m) : ℝ) = (2 * m).factorial / (m.factorial * 2 ^ m) := by
  rw [eq_div_iff (by positivity)]
  exact_mod_cast Q_fact m

theorem Q_split (a b : ℕ) :
    Q (2 * a) * Q (2 * b) * (2 * a + 2 * b).choose (2 * a) = Q (2 * (a + b)) * (a + b).choose a := by
  have hc1 : ((2 * a + 2 * b).choose (2 * a) : ℝ) =
      (2 * a + 2 * b).factorial / ((2 * a).factorial * (2 * b).factorial) := by
    rw [eq_div_iff (by positivity)]
    have := Nat.add_choose_mul_factorial_mul_factorial (2 * b) (2 * a)
    rw [add_comm (2 * b)] at this
    exact_mod_cast (by rw [← this]; ring)
  have hc2 : ((a + b).choose a : ℝ) = (a + b).factorial / (a.factorial * b.factorial) := by
    rw [eq_div_iff (by positivity)]
    have := Nat.add_choose_mul_factorial_mul_factorial b a
    rw [add_comm b] at this
    exact_mod_cast (by rw [← this]; ring)
  have : (Q (2 * a) * Q (2 * b) * (2 * a + 2 * b).choose (2 * a) : ℝ) =
      Q (2 * (a + b)) * (a + b).choose a := by
    rw [Q_real, Q_real, Q_real, hc1, hc2, show 2 * (a + b) = 2 * a + 2 * b by ring, pow_add]
    field_simp
  exact_mod_cast this

theorem choose_mul_le (a b i j : ℕ) : a.choose i * b.choose j ≤ (a + b).choose (i + j) := by
  rw [Nat.add_choose_eq]
  exact single_le_sum (f := fun p : ℕ × ℕ => a.choose p.1 * b.choose p.2)
    (fun _ _ => Nat.zero_le _) (mem_antidiagonal.mpr rfl : (i, j) ∈ antidiagonal (i + j))

theorem key_nat (n i : ℕ) (hi : i ≤ n) :
    (2 * n).choose (2 * i) * n.choose i * (Q (6 * i) * Q (6 * n - 6 * i)) ≤ Q (6 * n) := by
  have hsplit := Q_split (3 * i) (3 * n - 3 * i)
  rw [show 2 * (3 * i) = 6 * i by ring, show 2 * (3 * n - 3 * i) = 6 * n - 6 * i by omega,
    show 6 * i + (6 * n - 6 * i) = 6 * n by omega, show 3 * i + (3 * n - 3 * i) = 3 * n by omega,
    show 2 * (3 * n) = 6 * n by ring] at hsplit
  have hvan : (2 * n).choose (2 * i) * (3 * n).choose (3 * i) * n.choose i ≤ (6 * n).choose (6 * i) := by
    calc _ ≤ (2 * n + 3 * n).choose (2 * i + 3 * i) * n.choose i :=
          Nat.mul_le_mul_right _ (choose_mul_le _ _ _ _)
      _ ≤ (2 * n + 3 * n + n).choose (2 * i + 3 * i + i) := choose_mul_le _ _ _ _
      _ = _ := by rw [show 2 * n + 3 * n + n = 6 * n by ring, show 2 * i + 3 * i + i = 6 * i by ring]
  have hpos : 0 < (6 * n).choose (6 * i) := Nat.choose_pos (by omega)
  apply Nat.le_of_mul_le_mul_right _ hpos
  calc (2 * n).choose (2 * i) * n.choose i * (Q (6 * i) * Q (6 * n - 6 * i)) * (6 * n).choose (6 * i)
      = (2 * n).choose (2 * i) * n.choose i * (Q (6 * n) * (3 * n).choose (3 * i)) := by
        rw [← hsplit]; ring
    _ = Q (6 * n) * ((2 * n).choose (2 * i) * (3 * n).choose (3 * i) * n.choose i) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ hvan

theorem choose_two_le {n i : ℕ} (h2 : 2 ≤ i) (hi : i ≤ n / 2) : n.choose 2 ≤ n.choose i := by
  induction i, h2 using Nat.le_induction with
  | base => exact le_rfl
  | succ i hi2 ih => exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))

theorem term_le (n s : ℕ) (hn : 2 ≤ n) (hs : s ∈ Icc 1 n) :
    ((2 * n).choose s * (Q (3 * s) * Q (3 * (2 * n - s))) : ℝ) ≤
      Q (6 * n) * ((if s = 2 then 1 / (n : ℝ) else 0) + 2 / ((n : ℝ) * (n - 1))) := by
  have hs' := mem_Icc.mp hs
  have hn1 : (1 : ℝ) < n := by exact_mod_cast hn
  have hQ := Q_six_pos n
  have hrhs : 0 ≤ (if s = 2 then 1 / (n : ℝ) else 0) + 2 / ((n : ℝ) * (n - 1)) := by
    apply add_nonneg
    · split_ifs <;> positivity
    · apply div_nonneg (by norm_num); nlinarith
  obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' s
  · have hi : 1 ≤ i := by omega
    have e1 : 3 * (2 * i) = 6 * i := by ring
    have e2 : 3 * (2 * n - 2 * i) = 6 * n - 6 * i := by omega
    rw [e1, e2]
    have hk := key_nat n i (by omega)
    have hci : (0 : ℝ) < n.choose i := by exact_mod_cast Nat.choose_pos (by omega)
    have hk' : ((2 * n).choose (2 * i) * (Q (6 * i) * Q (6 * n - 6 * i)) : ℝ) ≤ Q (6 * n) / n.choose i := by
      rw [le_div_iff₀ hci]
      have : (((2 * n).choose (2 * i) * n.choose i * (Q (6 * i) * Q (6 * n - 6 * i)) : ℕ) : ℝ) ≤ Q (6 * n) := by
        exact_mod_cast hk
      push_cast at this
      linarith
    refine hk'.trans ?_
    rw [div_eq_mul_one_div]
    apply mul_le_mul_of_nonneg_left _ hQ.le
    by_cases h1 : i = 1
    · subst h1
      simp only [Nat.choose_one_right, mul_one, if_true]
      have : (0 : ℝ) ≤ 2 / ((n : ℝ) * (n - 1)) := by apply div_nonneg (by norm_num); nlinarith
      linarith
    · have h2 : 2 ≤ i := by omega
      have hle : (n.choose 2 : ℝ) ≤ n.choose i := by exact_mod_cast choose_two_le h2 (by omega)
      rw [Nat.cast_choose_two] at hle
      rw [if_neg (by omega), zero_add]
      rw [div_le_div_iff₀ hci (by nlinarith)]
      nlinarith
  · have e1 : 3 * (2 * i + 1) = 2 * (3 * i + 1) + 1 := by ring
    rw [e1, Q_odd]
    simp only [Nat.cast_zero, zero_mul, mul_zero]
    exact mul_nonneg hQ.le hrhs

theorem disc_lim : Tendsto (fun n : ℕ =>
    (((Om n).filter (fun f => ¬ (Gr f).Connected)).card : ℝ) / Q (6 * n)) atTop (𝓝 0) := by
  have hb : ∀ n, 2 ≤ n → (((Om n).filter (fun f => ¬ (Gr f).Connected)).card : ℝ) / Q (6 * n) ≤
      1 / (n : ℝ) + 2 / ((n : ℝ) - 1) := by
    intro n hn
    have hn1 : (1 : ℝ) < n := by exact_mod_cast hn
    rw [div_le_iff₀ (Q_six_pos n)]
    have h1 : (((Om n).filter (fun f => ¬ (Gr f).Connected)).card : ℝ) ≤
        ∑ s ∈ Icc 1 n, ((2 * n).choose s * (Q (3 * s) * Q (3 * (2 * n - s))) : ℝ) := by
      exact_mod_cast disc_bound n (by omega)
    refine h1.trans ((sum_le_sum (fun s hs => term_le n s hn hs)).trans (le_of_eq ?_))
    rw [← mul_sum, sum_add_distrib, sum_ite_eq' (Icc 1 n) 2 (fun _ => 1 / (n : ℝ)),
      if_pos (mem_Icc.mpr ⟨by norm_num, hn⟩), sum_const, Nat.card_Icc, nsmul_eq_mul]
    rw [show n + 1 - 1 = n by omega]
    field_simp
  have hlim : Tendsto (fun n : ℕ => 1 / (n : ℝ) + 2 / ((n : ℝ) - 1)) atTop (𝓝 0) := by
    have t1 : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) := by
      have := tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))
      refine this.congr (fun n => ?_)
      simp
    have t2 : Tendsto (fun n : ℕ => 2 / ((n : ℝ) - 1)) atTop (𝓝 0) := by
      apply Tendsto.div_atTop tendsto_const_nhds
      exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    simpa using t1.add t2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
  · exact Eventually.of_forall fun n => div_nonneg (Nat.cast_nonneg _) (Q_six_pos n).le
  · exact eventually_atTop.mpr ⟨2, hb⟩


/-! Assembly -/

open Asymptotics in
theorem conn_lim : Tendsto (fun n : ℕ =>
    ((OMA.S_oeis_a004109.a n * 6 ^ (2 * n) : ℕ) : ℝ) / Q (6 * n)) atTop (𝓝 (Real.exp (-2))) := by
  have hsplit : ∀ n, ((OMA.S_oeis_a004109.a n * 6 ^ (2 * n) : ℕ) : ℝ) / Q (6 * n) =
      (((Om n).filter (fun f => (LS f).card + (DS f).card = 0)).card : ℝ) / Q (6 * n) -
      ((((Om n).filter (fun f => (LS f).card + (DS f).card = 0)).filter
        (fun f => ¬ (Gr f).Connected)).card : ℝ) / Q (6 * n) := by
    intro n
    rw [← count_conn, ← sub_div]
    congr 1
    have := card_filter_add_card_filter_not (s := (Om n).filter (fun f => (LS f).card + (DS f).card = 0))
      (fun f => (Gr f).Connected)
    rw [filter_filter] at this
    rw [← this]
    push_cast
    ring
  have he : Tendsto (fun n : ℕ => ((((Om n).filter (fun f => (LS f).card + (DS f).card = 0)).filter
        (fun f => ¬ (Gr f).Connected)).card : ℝ) / Q (6 * n)) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds disc_lim
      (fun n => div_nonneg (Nat.cast_nonneg _) (Q_six_pos n).le) (fun n => ?_)
    apply div_le_div_of_nonneg_right _ (Q_six_pos n).le
    exact_mod_cast card_le_card (fun f hf => by
      simp only [mem_filter] at hf ⊢; exact ⟨hf.1.1, hf.2⟩)
  have := simple_lim.sub he
  rw [sub_zero] at this
  exact this.congr (fun n => (hsplit n).symm)

theorem stirling_identity (n : ℕ) (hn : 0 < n) :
    Real.sqrt (2 * ((6 * n : ℕ) : ℝ) * Real.pi) * (((6 * n : ℕ) : ℝ) / Real.exp 1) ^ (6 * n) /
      (Real.sqrt (2 * ((3 * n : ℕ) : ℝ) * Real.pi) * (((3 * n : ℕ) : ℝ) / Real.exp 1) ^ (3 * n) *
        2 ^ (3 * n) * 6 ^ (2 * n)) =
    Real.sqrt 2 * 2 ^ n * 3 ^ n * ((n : ℝ) / Real.exp 1) ^ (3 * n) := by
  push_cast
  set x := (n : ℝ) / Real.exp 1 with hx
  set A := Real.sqrt (2 * (3 * (n : ℝ)) * Real.pi) with hA
  have hx0 : 0 < x := by positivity
  have hA0 : 0 < A := by positivity
  have h6 : 6 * (n : ℝ) / Real.exp 1 = 6 * x := by rw [hx]; ring
  have h3 : 3 * (n : ℝ) / Real.exp 1 = 3 * x := by rw [hx]; ring
  have hs : Real.sqrt (2 * (6 * (n : ℝ)) * Real.pi) = Real.sqrt 2 * A := by
    rw [hA, ← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1; ring
  rw [h6, h3, hs, mul_pow, mul_pow]
  have e1 : (6 : ℝ) ^ (6 * n) = 2 ^ n * 2 ^ (3 * n) * 2 ^ (2 * n) * (3 ^ n * 3 ^ (3 * n) * 3 ^ (2 * n)) := by
    rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← mul_pow]
    norm_num
    ring_nf
  have e2 : (6 : ℝ) ^ (2 * n) = 2 ^ (2 * n) * 3 ^ (2 * n) := by rw [← mul_pow]; norm_num
  have e3 : x ^ (6 * n) = x ^ (3 * n) * x ^ (3 * n) := by rw [← pow_add]; ring_nf
  rw [e1, e2, e3]
  field_simp

open Asymptotics in
theorem final :
    (fun n : ℕ => (OMA.S_oeis_a004109.a n : ℝ)) ~[atTop]
      fun n : ℕ => (2 : ℝ) ^ ((n : ℝ) + 1 / 2) * 3 ^ n * (n : ℝ) ^ (3 * n) / Real.exp (3 * n + 2) := by
  let M : ℕ → ℝ := fun n =>
    ((6 * n).factorial : ℝ) / ((3 * n).factorial * (2 : ℝ) ^ (3 * n) * 6 ^ (2 * n))
  have hM : ∀ n, M n = Q (6 * n) / 6 ^ (2 * n) := by
    intro n
    have := Q_real (3 * n)
    rw [show 2 * (3 * n) = 6 * n by ring] at this
    simp only [M]
    rw [this]
    field_simp
  have h1 : (fun n : ℕ => (OMA.S_oeis_a004109.a n : ℝ)) ~[atTop] fun n => Real.exp (-2) * M n := by
    apply isEquivalent_of_tendsto_one
    have := conn_lim.div_const (Real.exp (-2))
    rw [div_self (Real.exp_pos _).ne'] at this
    refine this.congr (fun n => ?_)
    simp only [Pi.div_apply, hM]
    have hQ := (Q_six_pos n).ne'
    push_cast
    field_simp
  have h6 := Stirling.factorial_isEquivalent_stirling.comp_tendsto
    (tendsto_atTop_mono (fun n : ℕ => show n ≤ 6 * n by omega) tendsto_id)
  have h3 := Stirling.factorial_isEquivalent_stirling.comp_tendsto
    (tendsto_atTop_mono (fun n : ℕ => show n ≤ 3 * n by omega) tendsto_id)
  have hp2 : (fun n : ℕ => (2 : ℝ) ^ (3 * n)) ~[atTop] (fun n : ℕ => (2 : ℝ) ^ (3 * n)) :=
    IsEquivalent.refl
  have hp6 : (fun n : ℕ => (6 : ℝ) ^ (2 * n)) ~[atTop] (fun n : ℕ => (6 : ℝ) ^ (2 * n)) :=
    IsEquivalent.refl
  have hM2 : M ~[atTop] fun n : ℕ => Real.sqrt 2 * 2 ^ n * 3 ^ n * ((n : ℝ) / Real.exp 1) ^ (3 * n) := by
    have h := h6.div ((h3.mul hp2).mul hp6)
    refine h.trans_eventuallyEq ?_
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact stirling_identity n hn
  have hc : (fun _ : ℕ => Real.exp (-2)) ~[atTop] (fun _ : ℕ => Real.exp (-2)) := IsEquivalent.refl
  refine h1.trans ((hc.mul hM2).trans_eventuallyEq ?_)
  filter_upwards [] with n
  simp only [Pi.mul_apply, div_pow]
  have he : (Real.exp 1) ^ (3 * n) = Real.exp (3 * (n : ℝ)) := by
    rw [← Real.exp_nat_mul]; push_cast; ring_nf
  have h2 : (2 : ℝ) ^ ((n : ℝ) + 1 / 2) = 2 ^ n * Real.sqrt 2 := by
    rw [Real.rpow_add (by norm_num), Real.rpow_natCast, Real.sqrt_eq_rpow]
  rw [he, h2, Real.exp_add, Real.exp_neg]
  field_simp

end OMA.A4109

theorem OMA.solution : type_of% @OMA.S_oeis_a004109.main := OMA.A4109.final
