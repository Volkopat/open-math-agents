import OMAStatements.S_arxiv_2509_19940

/-!
# Proof that no finite nonempty functional digraph is prime

We formalize Ralph Seifert's 1971 theorem, following the simplified presentation of
Adrien Richard (arXiv:2509.19940): no nonempty finite functional digraph is prime under
the direct product.

The proof proceeds in three main steps:
1. Every prime functional digraph is connected (using `X * (p C_p) ≅ C_p * (C_p X₁ + p X₂)`).
2. Every connected prime functional digraph has a cycle of length 1 (using explicit
   distance-mod-`g` bijections for `C_n * X` and Chinese Remainder Theorem for cycles).
3. No connected functional digraph with a cycle of length 1 is prime (Seifert's explicit
   construction of `A`, `B`, `Y` with `X * Y ≅ A * B`, `X ∤ A`, and `X ∤ B`).
-/

namespace OMA.P_arxiv_2509_19940

open OMA.S_arxiv_2509_19940

section BasicIso

lemma iso_refl {V : Type} (f : V → V) : Iso f f :=
  ⟨Equiv.refl V, fun _ => rfl⟩

lemma iso_symm {V W : Type} {f : V → V} {g : W → W} (h : Iso f g) : Iso g f := by
  rcases h with ⟨e, he⟩
  refine ⟨e.symm, fun w => ?_⟩
  apply e.injective
  simp [he]

lemma iso_trans {U V W : Type} {f : U → U} {g : V → V} {h : W → W}
    (h1 : Iso f g) (h2 : Iso g h) : Iso f h := by
  rcases h1 with ⟨e1, he1⟩
  rcases h2 with ⟨e2, he2⟩
  exact ⟨e1.trans e2, fun u => by simp [he1, he2]⟩

lemma iso_prod_congr {U U' V V' : Type} {f : U → U} {f' : U' → U'} {g : V → V} {g' : V' → V'}
    (h1 : Iso f f') (h2 : Iso g g') : Iso (Prod.map f g) (Prod.map f' g') := by
  rcases h1 with ⟨e1, he1⟩
  rcases h2 with ⟨e2, he2⟩
  exact ⟨Equiv.prodCongr e1 e2, fun ⟨u, v⟩ => Prod.ext (he1 u) (he2 v)⟩

lemma iso_sum_congr {U U' V V' : Type} {f : U → U} {f' : U' → U'} {g : V → V} {g' : V' → V'}
    (h1 : Iso f f') (h2 : Iso g g') : Iso (Sum.map f g) (Sum.map f' g') := by
  rcases h1 with ⟨e1, he1⟩
  rcases h2 with ⟨e2, he2⟩
  refine ⟨Equiv.sumCongr e1 e2, fun x => ?_⟩
  cases x with
  | inl u => simp [he1]
  | inr v => simp [he2]

lemma iso_prod_comm {U V : Type} (f : U → U) (g : V → V) :
    Iso (Prod.map f g) (Prod.map g f) :=
  ⟨Equiv.prodComm U V, fun _ => rfl⟩

lemma iso_prod_assoc {U V W : Type} (f : U → U) (g : V → V) (h : W → W) :
    Iso (Prod.map (Prod.map f g) h) (Prod.map f (Prod.map g h)) :=
  ⟨Equiv.prodAssoc U V W, fun _ => rfl⟩

lemma iso_sum_prod_distrib {U V W : Type} (f : U → U) (g : V → V) (h : W → W) :
    Iso (Prod.map (Sum.map f g) h) (Sum.map (Prod.map f h) (Prod.map g h)) := by
  refine ⟨Equiv.sumProdDistrib U V W, fun ⟨x, w⟩ => ?_⟩
  cases x <;> rfl

lemma iso_prod_sum_distrib {U V W : Type} (f : U → U) (g : V → V) (h : W → W) :
    Iso (Prod.map f (Sum.map g h)) (Sum.map (Prod.map f g) (Prod.map f h)) := by
  refine ⟨Equiv.prodSumDistrib U V W, fun ⟨u, x⟩ => ?_⟩
  cases x <;> rfl

lemma iso_iterate {V W : Type} {f : V → V} {g : W → W} (e : V ≃ W)
    (he : ∀ v, e (f v) = g (e v)) (k : ℕ) (v : V) :
    e (f^[k] v) = g^[k] (e v) := by
  induction k generalizing v with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, he]

lemma iso_card_eq {V W : Type} [Fintype V] [Fintype W] {f : V → V} {g : W → W}
    (h : Iso f g) : Fintype.card V = Fintype.card W := by
  rcases h with ⟨e, _⟩
  exact Fintype.card_congr e

lemma divides_of_iso_right {U V W : Type} {x : U → U} {a : V → V} {b : W → W}
    (hd : Divides x a) (hi : Iso a b) : Divides x b := by
  rcases hd with ⟨n, y, hxy⟩
  exact ⟨n, y, iso_trans hxy hi⟩

lemma divides_of_fintype {U V W : Type} [Fintype V] {x : U → U} {y : V → V} {a : W → W}
    (h : Iso (Prod.map x y) a) : Divides x a := by
  let e := Fintype.equivFin V
  let y' : Fin (Fintype.card V) → Fin (Fintype.card V) := fun i => e (y (e.symm i))
  refine ⟨Fintype.card V, y', iso_trans ?_ h⟩
  exact iso_prod_congr (iso_refl x) ⟨e.symm, fun i => by simp [y']⟩

lemma isPrime_prod_dvd {V A B : Type} [Fintype A] [Fintype B] {x : V → V}
    (hx : IsPrime x) (fa : A → A) (fb : B → B)
    (hd : Divides x (Prod.map fa fb)) : Divides x fa ∨ Divides x fb := by
  let eA := Fintype.equivFin A
  let eB := Fintype.equivFin B
  let fa' : Fin (Fintype.card A) → Fin (Fintype.card A) := fun i => eA (fa (eA.symm i))
  let fb' : Fin (Fintype.card B) → Fin (Fintype.card B) := fun i => eB (fb (eB.symm i))
  have hA : Iso fa fa' := ⟨eA, fun u => by simp [fa']⟩
  have hB : Iso fb fb' := ⟨eB, fun u => by simp [fb']⟩
  have hd' : Divides x (Prod.map fa' fb') := divides_of_iso_right hd (iso_prod_congr hA hB)
  rcases hx.2 _ _ fa' fb' hd' with h1 | h2
  · exact Or.inl (divides_of_iso_right h1 (iso_symm hA))
  · exact Or.inr (divides_of_iso_right h2 (iso_symm hB))

lemma prod_map_iterate {V W : Type} (f : V → V) (g : W → W) (k : ℕ) (p : V × W) :
    (Prod.map f g)^[k] p = (f^[k] p.1, g^[k] p.2) := by
  induction k generalizing p with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_succ_apply]
    exact ih (f p.1, g p.2)

lemma sum_map_iterate_inl {V W : Type} (f : V → V) (g : W → W) (k : ℕ) (v : V) :
    (Sum.map f g)^[k] (Sum.inl v) = Sum.inl (f^[k] v) := by
  induction k generalizing v with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    exact ih (f v)

lemma sum_map_iterate_inr {V W : Type} (f : V → V) (g : W → W) (k : ℕ) (w : W) :
    (Sum.map f g)^[k] (Sum.inr w) = Sum.inr (g^[k] w) := by
  induction k generalizing w with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    exact ih (g w)

lemma iso_unit_of_card_one {V : Type} [Fintype V] (f : V → V) (h1 : Fintype.card V = 1) :
    Iso f (id : Unit → Unit) := by
  obtain ⟨huniq⟩ := Fintype.card_eq_one_iff_nonempty_unique.mp h1
  refine ⟨
    { toFun := fun _ => ()
      invFun := fun _ => huniq.default
      left_inv := fun v => huniq.uniq v |>.symm
      right_inv := fun u => Subsingleton.elim _ u },
    fun _ => rfl⟩

lemma iso_prod_of_card_one {V W : Type} [Fintype W] (f : V → V) (g : W → W)
    (h1 : Fintype.card W = 1) : Iso (Prod.map f g) f := by
  obtain ⟨huniq⟩ := Fintype.card_eq_one_iff_nonempty_unique.mp h1
  refine ⟨
    { toFun := Prod.fst
      invFun := fun v => (v, huniq.default)
      left_inv := fun ⟨v, w⟩ => Prod.ext rfl (huniq.uniq w).symm
      right_inv := fun _ => rfl },
    fun _ => rfl⟩

lemma card_ge_two_of_isPrime {V : Type} [Fintype V] [Nonempty V] {f : V → V}
    (hf : IsPrime f) : 2 ≤ Fintype.card V := by
  have hpos : 0 < Fintype.card V := Fintype.card_pos
  by_contra hlt
  have h1 : Fintype.card V = 1 := by omega
  exact hf.1 (iso_unit_of_card_one f h1)

end BasicIso

section Periodic

/-- A vertex `v` is periodic under `f` if it returns to itself after some positive number of steps. -/
def IsPeriodic {V : Type} (f : V → V) (v : V) : Prop :=
  ∃ m : ℕ, 0 < m ∧ f^[m] v = v

/-- The subtype of periodic vertices of `f`. -/
abbrev Per {V : Type} (f : V → V) : Type := {v : V // IsPeriodic f v}

/-- Minimal positive period of a periodic vertex (0 for non-periodic vertices). -/
noncomputable def period {V : Type} (f : V → V) (v : V) : ℕ :=
  open Classical in if h : IsPeriodic f v then Nat.find h else 0

lemma period_pos {V : Type} {f : V → V} {v : V} (hv : IsPeriodic f v) : 0 < period f v := by
  classical
  simp only [period, dif_pos hv]
  exact (Nat.find_spec hv).1

lemma iterate_period {V : Type} {f : V → V} {v : V} (hv : IsPeriodic f v) :
    f^[period f v] v = v := by
  classical
  simp only [period, dif_pos hv]
  exact (Nat.find_spec hv).2

lemma iterate_mul_period {V : Type} {f : V → V} {v : V} (hv : IsPeriodic f v) (q : ℕ) :
    f^[q * period f v] v = v := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.succ_mul, Function.iterate_add_apply, iterate_period hv, ih]

lemma iterate_eq_self_iff_period_dvd {V : Type} {f : V → V} {v : V} (hv : IsPeriodic f v) (m : ℕ) :
    f^[m] v = v ↔ period f v ∣ m := by
  constructor
  · intro hm
    set d := period f v
    have hd : 0 < d := period_pos hv
    set r := m % d
    have hdiv : m = d * (m / d) + r := (Nat.div_add_mod m d).symm
    have hr : f^[r] v = v := by
      have h1 : f^[r + (m / d) * d] v = v := by
        rw [Nat.add_comm, Nat.mul_comm, ← hdiv]; exact hm
      rw [Function.iterate_add_apply, iterate_mul_period hv] at h1
      exact h1
    by_contra hndvd
    have hrpos : 0 < r := Nat.pos_of_ne_zero fun h0 => hndvd (Nat.dvd_of_mod_eq_zero h0)
    have hrlt : r < d := Nat.mod_lt m hd
    classical
    have hmin : d ≤ r := by
      change (if h : IsPeriodic f v then Nat.find h else 0) ≤ r
      rw [dif_pos hv]
      exact Nat.find_min' hv ⟨hrpos, hr⟩
    omega
  · rintro ⟨q, rfl⟩
    rw [Nat.mul_comm]
    exact iterate_mul_period hv q

lemma exists_periodic_iterate {V : Type} [Fintype V] (f : V → V) (v : V) :
    ∃ k : ℕ, IsPeriodic f (f^[k] v) := by
  have hcard : Fintype.card V < Fintype.card (Fin (Fintype.card V + 1)) := by simp
  obtain ⟨i, j, hne, hij⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt (fun n : Fin (Fintype.card V + 1) => f^[n.val] v) hcard
  wlog hlt : i.val < j.val generalizing i j
  · exact this j i hne.symm hij.symm (by omega)
  refine ⟨i.val, j.val - i.val, by omega, ?_⟩
  rw [← Function.iterate_add_apply, Nat.sub_add_cancel (by omega)]
  exact hij.symm

lemma nonempty_per {V : Type} [Fintype V] [Nonempty V] (f : V → V) : Nonempty (Per f) := by
  obtain ⟨v⟩ := ‹Nonempty V›
  obtain ⟨k, hk⟩ := exists_periodic_iterate f v
  exact ⟨⟨f^[k] v, hk⟩⟩

lemma isPeriodic_iterate {V : Type} {f : V → V} {v : V} (hv : IsPeriodic f v) (k : ℕ) :
    IsPeriodic f (f^[k] v) := by
  rcases hv with ⟨m, hm, hmv⟩
  refine ⟨m, hm, ?_⟩
  rw [← Function.iterate_add_apply, Nat.add_comm, Function.iterate_add_apply, hmv]

lemma period_iterate {V : Type} {f : V → V} {v : V} (hv : IsPeriodic f v) (k : ℕ) :
    period f (f^[k] v) = period f v := by
  have hkv := isPeriodic_iterate hv k
  apply Nat.dvd_antisymm
  · rw [← iterate_eq_self_iff_period_dvd hkv]
    rw [← Function.iterate_add_apply, Nat.add_comm, Function.iterate_add_apply, iterate_period hv]
  · rw [← iterate_eq_self_iff_period_dvd hv]
    set d := period f (f^[k] v)
    obtain ⟨m, hm⟩ : ∃ m, f^[m] (f^[k] v) = v := by
      refine ⟨(k / period f v + 1) * period f v - k, ?_⟩
      rw [← Function.iterate_add_apply, Nat.sub_add_cancel]
      · exact iterate_mul_period hv _
      · have h1 := Nat.lt_div_mul_add (a := k) (period_pos hv)
        nlinarith [Nat.div_mul_le_self k (period f v)]
    have h1 : f^[d] (f^[m] (f^[k] v)) = f^[m] (f^[k] v) := by
      rw [← Function.iterate_add_apply, Nat.add_comm, Function.iterate_add_apply, iterate_period hkv]
    rwa [hm] at h1

lemma orbit_injective {V : Type} {f : V → V} {v : V} (hv : IsPeriodic f v) :
    Function.Injective (fun i : Fin (period f v) => (⟨f^[i.val] v, isPeriodic_iterate hv i.val⟩ : Per f)) := by
  have aux : ∀ (i j : Fin (period f v)), i.val ≤ j.val → f^[i.val] v = f^[j.val] v → i = j := by
    intro i j hle heq
    have h1 : f^[j.val - i.val] (f^[i.val] v) = f^[i.val] v := by
      rw [← Function.iterate_add_apply, Nat.sub_add_cancel hle, heq]
    have hdvd : period f (f^[i.val] v) ∣ j.val - i.val :=
      (iterate_eq_self_iff_period_dvd (isPeriodic_iterate hv i.val) _).mp h1
    rw [period_iterate hv] at hdvd
    have h0 : j.val - i.val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
    exact Fin.ext (by omega)
  intro i j hij
  have heq : f^[i.val] v = f^[j.val] v := congrArg Subtype.val hij
  rcases le_total i.val j.val with hle | hle
  · exact aux i j hle heq
  · exact (aux j i hle heq.symm).symm

lemma period_le_card_per {V : Type} [Fintype V] {f : V → V} {v : V} (hv : IsPeriodic f v) :
    period f v ≤ Nat.card (Per f) := by
  classical
  rw [Nat.card_eq_fintype_card]
  simpa using Fintype.card_le_of_injective _ (orbit_injective hv)

lemma isPeriodic_iso {V W : Type} {f : V → V} {g : W → W} (e : V ≃ W)
    (he : ∀ v, e (f v) = g (e v)) (v : V) :
    IsPeriodic g (e v) ↔ IsPeriodic f v := by
  constructor
  · rintro ⟨m, hm, hmv⟩
    refine ⟨m, hm, e.injective ?_⟩
    rw [iso_iterate e he m v, hmv]
  · rintro ⟨m, hm, hmv⟩
    refine ⟨m, hm, ?_⟩
    rw [← iso_iterate e he m v, hmv]

lemma period_iso {V W : Type} {f : V → V} {g : W → W} (e : V ≃ W)
    (he : ∀ v, e (f v) = g (e v)) (v : V) :
    period g (e v) = period f v := by
  classical
  by_cases hv : IsPeriodic f v
  · have hgv : IsPeriodic g (e v) := (isPeriodic_iso e he v).mpr hv
    apply Nat.dvd_antisymm
    · rw [← iterate_eq_self_iff_period_dvd hgv, ← iso_iterate e he, iterate_period hv]
    · rw [← iterate_eq_self_iff_period_dvd hv]
      apply e.injective
      rw [iso_iterate e he, iterate_period hgv]
  · have hgv : ¬ IsPeriodic g (e v) := mt (isPeriodic_iso e he v).mp hv
    simp [period, hv, hgv]

lemma card_per_iso {V W : Type} {f : V → V} {g : W → W}
    (h : Iso f g) : Nat.card (Per f) = Nat.card (Per g) := by
  rcases h with ⟨e, he⟩
  refine Nat.card_congr
    { toFun := fun ⟨v, hv⟩ => ⟨e v, (isPeriodic_iso e he v).mpr hv⟩
      invFun := fun ⟨w, hw⟩ => ⟨e.symm w, (isPeriodic_iso e he (e.symm w)).mp (by simpa using hw)⟩
      left_inv := fun ⟨v, _⟩ => by simp
      right_inv := fun ⟨w, _⟩ => by simp }

lemma isPeriodic_prod_iff {V W : Type} {f : V → V} {g : W → W} (p : V × W) :
    IsPeriodic (Prod.map f g) p ↔ IsPeriodic f p.1 ∧ IsPeriodic g p.2 := by
  constructor
  · rintro ⟨m, hm, hmp⟩
    rw [prod_map_iterate, Prod.ext_iff] at hmp
    exact ⟨⟨m, hm, hmp.1⟩, ⟨m, hm, hmp.2⟩⟩
  · rintro ⟨⟨m1, hm1, h1⟩, ⟨m2, hm2, h2⟩⟩
    refine ⟨m1 * m2, Nat.mul_pos hm1 hm2, ?_⟩
    rw [prod_map_iterate, Prod.ext_iff]
    constructor
    · have hd1 : period f p.1 ∣ m1 := (iterate_eq_self_iff_period_dvd ⟨m1, hm1, h1⟩ m1).mp h1
      exact (iterate_eq_self_iff_period_dvd ⟨m1, hm1, h1⟩ (m1 * m2)).mpr (dvd_mul_of_dvd_left hd1 m2)
    · have hd2 : period g p.2 ∣ m2 := (iterate_eq_self_iff_period_dvd ⟨m2, hm2, h2⟩ m2).mp h2
      exact (iterate_eq_self_iff_period_dvd ⟨m2, hm2, h2⟩ (m1 * m2)).mpr (dvd_mul_of_dvd_right hd2 m1)

lemma period_prod {V W : Type} {f : V → V} {g : W → W} {v : V} {w : W}
    (hv : IsPeriodic f v) (hw : IsPeriodic g w) :
    period (Prod.map f g) (v, w) = Nat.lcm (period f v) (period g w) := by
  have hvw : IsPeriodic (Prod.map f g) (v, w) := (isPeriodic_prod_iff (v, w)).mpr ⟨hv, hw⟩
  apply Nat.dvd_antisymm
  · rw [← iterate_eq_self_iff_period_dvd hvw, prod_map_iterate, Prod.ext_iff]
    exact ⟨(iterate_eq_self_iff_period_dvd hv _).mpr (Nat.dvd_lcm_left _ _),
           (iterate_eq_self_iff_period_dvd hw _).mpr (Nat.dvd_lcm_right _ _)⟩
  · rw [Nat.lcm_dvd_iff]
    have h1 := iterate_period hvw
    rw [prod_map_iterate, Prod.ext_iff] at h1
    exact ⟨(iterate_eq_self_iff_period_dvd hv _).mp h1.1,
           (iterate_eq_self_iff_period_dvd hw _).mp h1.2⟩

lemma card_per_prod {V W : Type} (f : V → V) (g : W → W) :
    Nat.card (Per (Prod.map f g)) = Nat.card (Per f) * Nat.card (Per g) := by
  rw [← Nat.card_prod]
  refine Nat.card_congr
    { toFun := fun ⟨⟨v, w⟩, h⟩ =>
        (⟨v, ((isPeriodic_prod_iff (v, w)).mp h).1⟩, ⟨w, ((isPeriodic_prod_iff (v, w)).mp h).2⟩)
      invFun := fun ⟨⟨v, hv⟩, ⟨w, hw⟩⟩ => ⟨(v, w), (isPeriodic_prod_iff (v, w)).mpr ⟨hv, hw⟩⟩
      left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
      right_inv := fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ => rfl }

lemma isPeriodic_sum_inl {V W : Type} {f : V → V} {g : W → W} (v : V) :
    IsPeriodic (Sum.map f g) (Sum.inl v) ↔ IsPeriodic f v := by
  constructor
  · rintro ⟨m, hm, h⟩; rw [sum_map_iterate_inl] at h; exact ⟨m, hm, Sum.inl.inj h⟩
  · rintro ⟨m, hm, h⟩; exact ⟨m, hm, by rw [sum_map_iterate_inl, h]⟩

lemma isPeriodic_sum_inr {V W : Type} {f : V → V} {g : W → W} (w : W) :
    IsPeriodic (Sum.map f g) (Sum.inr w) ↔ IsPeriodic g w := by
  constructor
  · rintro ⟨m, hm, h⟩; rw [sum_map_iterate_inr] at h; exact ⟨m, hm, Sum.inr.inj h⟩
  · rintro ⟨m, hm, h⟩; exact ⟨m, hm, by rw [sum_map_iterate_inr, h]⟩

lemma period_sum_inl {V W : Type} {f : V → V} {g : W → W} {v : V} (hv : IsPeriodic f v) :
    period (Sum.map f g) (Sum.inl v) = period f v := by
  have h1 : IsPeriodic (Sum.map f g) (Sum.inl v) := (isPeriodic_sum_inl v).mpr hv
  apply Nat.dvd_antisymm
  · rw [← iterate_eq_self_iff_period_dvd h1, sum_map_iterate_inl, iterate_period hv]
  · rw [← iterate_eq_self_iff_period_dvd hv]
    have h2 := iterate_period h1
    rw [sum_map_iterate_inl] at h2
    exact Sum.inl.inj h2

lemma period_sum_inr {V W : Type} {f : V → V} {g : W → W} {w : W} (hw : IsPeriodic g w) :
    period (Sum.map f g) (Sum.inr w) = period g w := by
  have h1 : IsPeriodic (Sum.map f g) (Sum.inr w) := (isPeriodic_sum_inr w).mpr hw
  apply Nat.dvd_antisymm
  · rw [← iterate_eq_self_iff_period_dvd h1, sum_map_iterate_inr, iterate_period hw]
  · rw [← iterate_eq_self_iff_period_dvd hw]
    have h2 := iterate_period h1
    rw [sum_map_iterate_inr] at h2
    exact Sum.inr.inj h2

lemma card_per_sum {V W : Type} [Fintype V] [Fintype W] (f : V → V) (g : W → W) :
    Nat.card (Per (Sum.map f g)) = Nat.card (Per f) + Nat.card (Per g) := by
  classical
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      ← Fintype.card_sum]
  refine Fintype.card_congr
    { toFun := fun ⟨x, hx⟩ => match x, hx with
        | Sum.inl v, hv => Sum.inl ⟨v, (isPeriodic_sum_inl v).mp hv⟩
        | Sum.inr w, hw => Sum.inr ⟨w, (isPeriodic_sum_inr w).mp hw⟩
      invFun := fun x => match x with
        | Sum.inl ⟨v, hv⟩ => ⟨Sum.inl v, (isPeriodic_sum_inl v).mpr hv⟩
        | Sum.inr ⟨w, hw⟩ => ⟨Sum.inr w, (isPeriodic_sum_inr w).mpr hw⟩
      left_inv := fun ⟨x, _⟩ => by cases x <;> rfl
      right_inv := fun x => by cases x <;> rfl }

lemma isPeriodic_id {V : Type} (v : V) : IsPeriodic (id : V → V) v :=
  ⟨1, Nat.one_pos, rfl⟩

lemma period_id {V : Type} (v : V) : period (id : V → V) v = 1 := by
  have hv := isPeriodic_id v
  apply Nat.le_antisymm
  · exact Nat.le_of_dvd Nat.one_pos ((iterate_eq_self_iff_period_dvd hv 1).mp rfl)
  · exact period_pos hv

lemma card_per_id (V : Type) [Fintype V] : Nat.card (Per (id : V → V)) = Fintype.card V := by
  rw [← Nat.card_eq_fintype_card]
  refine Nat.card_congr
    { toFun := Subtype.val
      invFun := fun v => ⟨v, isPeriodic_id v⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- The directed cycle `C_n` on `ZMod n` given by `i ↦ i + 1`. -/
def cyc (n : ℕ) : ZMod n → ZMod n := fun i => i + 1

lemma cyc_iterate (n : ℕ) (k : ℕ) (i : ZMod n) : (cyc n)^[k] i = i + (k : ZMod n) := by
  induction k generalizing i with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih, cyc]
    push_cast
    ring

lemma isPeriodic_cyc {n : ℕ} (hn : 0 < n) (i : ZMod n) : IsPeriodic (cyc n) i :=
  ⟨n, hn, by rw [cyc_iterate, ZMod.natCast_self, add_zero]⟩

lemma period_cyc {n : ℕ} (hn : 0 < n) (i : ZMod n) : period (cyc n) i = n := by
  have hi := isPeriodic_cyc hn i
  apply Nat.dvd_antisymm
  · exact (iterate_eq_self_iff_period_dvd hi n).mp (by rw [cyc_iterate, ZMod.natCast_self, add_zero])
  · have h := iterate_period hi
    rw [cyc_iterate] at h
    have h0 : (period (cyc n) i : ZMod n) = 0 := by
      have := congrArg (fun x => x - i) h
      simpa using this
    exact (ZMod.natCast_eq_zero_iff _ _).mp h0

lemma card_per_cyc (n : ℕ) [NeZero n] : Nat.card (Per (cyc n)) = n := by
  have hn : 0 < n := NeZero.pos n
  calc Nat.card (Per (cyc n))
      = Nat.card (ZMod n) := Nat.card_congr
        { toFun := Subtype.val
          invFun := fun i => ⟨i, isPeriodic_cyc hn i⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
    _ = n := by rw [Nat.card_eq_fintype_card, ZMod.card]

/-- Shearing isomorphism `C_n × C_n ≅ id_(ZMod n) × C_n`. -/
lemma iso_cyc_prod_cyc (n : ℕ) :
    Iso (Prod.map (cyc n) (cyc n)) (Prod.map (id : ZMod n → ZMod n) (cyc n)) := by
  refine ⟨
    { toFun := fun ⟨a, b⟩ => (b - a, b)
      invFun := fun ⟨c, b⟩ => (b - c, b)
      left_inv := fun ⟨a, b⟩ => by simp
      right_inv := fun ⟨c, b⟩ => by simp },
    fun ⟨a, b⟩ => by simp [cyc]⟩

/-- Shearing isomorphism `C_q × C_{p*q} ≅ id_(ZMod q) × C_{p*q}`. -/
lemma iso_cyc_prod_cyc_mul (p q : ℕ) :
    Iso (Prod.map (cyc q) (cyc (p * q))) (Prod.map (id : ZMod q → ZMod q) (cyc (p * q))) := by
  let cast := ZMod.castHom (dvd_mul_left q p) (ZMod q)
  refine ⟨
    { toFun := fun ⟨a, b⟩ => (a - cast b, b)
      invFun := fun ⟨c, b⟩ => (c + cast b, b)
      left_inv := fun ⟨a, b⟩ => by simp
      right_inv := fun ⟨c, b⟩ => by simp },
    fun ⟨a, b⟩ => by simp [cyc, map_add, map_one]⟩

/-- Chinese Remainder Theorem isomorphism `C_{a*b} ≅ C_a × C_b` for coprime `a, b`. -/
lemma iso_cyc_mul_of_coprime {a b : ℕ} (h : Nat.Coprime a b) :
    Iso (cyc (a * b)) (Prod.map (cyc a) (cyc b)) := by
  let e := ZMod.chineseRemainder h
  refine ⟨e.toEquiv, fun x => ?_⟩
  simp only [RingEquiv.toEquiv_eq_coe, EquivLike.coe_coe, cyc, map_add, map_one]
  exact Prod.ext rfl rfl

/-- Restriction of a functional digraph to an invariant subtype preserves iterates. -/
lemma restrict_iterate {V : Type} {P : V → Prop} {f : V → V}
    (hP : ∀ v, P v → P (f v)) (k : ℕ) (v : {v : V // P v}) :
    ((fun x : {v : V // P v} => (⟨f x.1, hP x.1 x.2⟩ : {v : V // P v}))^[k] v).1 = f^[k] v.1 := by
  induction k generalizing v with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    exact ih ⟨f v.1, hP v.1 v.2⟩

end Periodic

section Connectedness

/-- Two vertices are in the same connected component of `f` if their forward orbits meet. -/
def CompRel {V : Type} (f : V → V) (u v : V) : Prop :=
  ∃ a b : ℕ, f^[a] u = f^[b] v

lemma compRel_refl {V : Type} (f : V → V) (u : V) : CompRel f u u := ⟨0, 0, rfl⟩

lemma compRel_symm {V : Type} {f : V → V} {u v : V} (h : CompRel f u v) : CompRel f v u := by
  rcases h with ⟨a, b, hab⟩; exact ⟨b, a, hab.symm⟩

lemma compRel_trans {V : Type} {f : V → V} {u v w : V}
    (h1 : CompRel f u v) (h2 : CompRel f v w) : CompRel f u w := by
  rcases h1 with ⟨a, b, hab⟩
  rcases h2 with ⟨c, d, hcd⟩
  refine ⟨a + c, b + d, ?_⟩
  rw [Nat.add_comm a c, Function.iterate_add_apply, hab, ← Function.iterate_add_apply,
      Nat.add_comm c b, Function.iterate_add_apply, hcd, ← Function.iterate_add_apply]

lemma compRel_step {V : Type} (f : V → V) (u : V) : CompRel f u (f u) :=
  ⟨1, 0, rfl⟩

/-- A functional digraph is connected if every two vertices have meeting forward orbits. -/
def IsConnected {V : Type} (f : V → V) : Prop :=
  ∀ u v : V, CompRel f u v

lemma isConnected_iso {V W : Type} {f : V → V} {g : W → W} (h : Iso f g)
    (hc : IsConnected f) : IsConnected g := by
  rcases h with ⟨e, he⟩
  intro u v
  obtain ⟨a, b, hab⟩ := hc (e.symm u) (e.symm v)
  refine ⟨a, b, ?_⟩
  have h1 := congrArg e hab
  rw [iso_iterate e he, iso_iterate e he] at h1
  simpa using h1

lemma isConnected_cyc {n : ℕ} (hn : 0 < n) : IsConnected (cyc n) := by
  have : NeZero n := ⟨Nat.ne_of_gt hn⟩
  intro u v
  refine ⟨(v - u).val, 0, ?_⟩
  simp [cyc_iterate]

lemma periodic_reaches_of_compRel {V : Type} {f : V → V} {u v : V}
    (hv : IsPeriodic f v) (h : CompRel f u v) : ∃ t : ℕ, f^[t] u = v := by
  rcases h with ⟨a, b, hab⟩
  set d := period f v
  have hd : 0 < d := period_pos hv
  set m := (b / d + 1) * d - b
  have hbm : m + b = (b / d + 1) * d := by
    apply Nat.sub_add_cancel
    have := Nat.lt_div_mul_add (a := b) hd
    nlinarith [Nat.div_mul_le_self b d]
  refine ⟨m + a, ?_⟩
  rw [Function.iterate_add_apply, hab, ← Function.iterate_add_apply, hbm]
  exact iterate_mul_period hv _

lemma periodic_eq_iterate_of_compRel {V : Type} {f : V → V} {u v : V}
    (hv : IsPeriodic f v) (h : CompRel f u v) :
    ∃ r < period f v, f^[r] v = u ∨ ¬ IsPeriodic f u := by
  by_cases hu : IsPeriodic f u
  · obtain ⟨t, ht⟩ := periodic_reaches_of_compRel hu (compRel_symm h)
    refine ⟨t % period f v, Nat.mod_lt t (period_pos hv), Or.inl ?_⟩
    have hdiv : t = period f v * (t / period f v) + t % period f v := (Nat.div_add_mod t _).symm
    have h1 : f^[t % period f v] v = f^[t] v := by
      conv_rhs => rw [hdiv, Nat.add_comm, Function.iterate_add_apply, Nat.mul_comm, iterate_mul_period hv]
    rw [h1, ht]
  · exact ⟨0, period_pos hv, Or.inr hu⟩

lemma card_per_eq_period_of_connected {V : Type} [Fintype V] {f : V → V}
    (hc : IsConnected f) {x0 : V} (hx0 : IsPeriodic f x0) :
    Nat.card (Per f) = period f x0 := by
  classical
  apply Nat.le_antisymm
  · rw [Nat.card_eq_fintype_card]
    let g : Fin (period f x0) → Per f := fun i => ⟨f^[i.val] x0, isPeriodic_iterate hx0 i.val⟩
    have hsurj : Function.Surjective g := by
      rintro ⟨u, hu⟩
      obtain ⟨r, hr, hru | hnu⟩ := periodic_eq_iterate_of_compRel hx0 (hc u x0)
      · exact ⟨⟨r, hr⟩, Subtype.ext hru⟩
      · exact absurd hu hnu
    simpa using Fintype.card_le_of_surjective g hsurj
  · exact period_le_card_per hx0

lemma isConnected_of_card_per_eq_period {V : Type} [Fintype V] {f : V → V}
    {x0 : V} (hx0 : IsPeriodic f x0) (hcard : Nat.card (Per f) = period f x0) :
    IsConnected f := by
  classical
  let g : Fin (period f x0) → Per f := fun i => ⟨f^[i.val] x0, isPeriodic_iterate hx0 i.val⟩
  have hfc : Fintype.card (Per f) = period f x0 := by rwa [← Nat.card_eq_fintype_card]
  have hbij : Function.Bijective g :=
    (Fintype.bijective_iff_injective_and_card g).mpr ⟨orbit_injective hx0, by simp [hfc]⟩
  have hreach : ∀ u : V, CompRel f u x0 := by
    intro u
    obtain ⟨k, hk⟩ := exists_periodic_iterate f u
    obtain ⟨i, hi⟩ := hbij.2 ⟨f^[k] u, hk⟩
    exact ⟨k, i.val, (congrArg Subtype.val hi).symm⟩
  intro u v
  exact compRel_trans (hreach u) (compRel_symm (hreach v))

lemma all_periods_eq_of_card_per_eq_period {V : Type} [Fintype V] {f : V → V}
    {x0 : V} (hx0 : IsPeriodic f x0) (hcard : Nat.card (Per f) = period f x0)
    {u : V} (hu : IsPeriodic f u) : period f u = period f x0 := by
  classical
  let g : Fin (period f x0) → Per f := fun i => ⟨f^[i.val] x0, isPeriodic_iterate hx0 i.val⟩
  have hfc : Fintype.card (Per f) = period f x0 := by rwa [← Nat.card_eq_fintype_card]
  have hbij : Function.Bijective g :=
    (Fintype.bijective_iff_injective_and_card g).mpr ⟨orbit_injective hx0, by simp [hfc]⟩
  obtain ⟨i, hi⟩ := hbij.2 ⟨u, hu⟩
  have heq : f^[i.val] x0 = u := congrArg Subtype.val hi
  rw [← heq, period_iterate hx0]

/-- Lemma 2 (Richard 2025): Every prime functional digraph is connected. -/
lemma isConnected_of_isPrime {V : Type} [Fintype V] [Nonempty V] {f : V → V}
    (hf : IsPrime f) : IsConnected f := by
  classical
  by_contra hnc
  have hper_ne : (Finset.univ : Finset (Per f)).Nonempty :=
    Finset.univ_nonempty_iff.mpr (nonempty_per f)
  obtain ⟨⟨x0, hx0⟩, _, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (Per f)) (fun v => period f v.1) hper_ne
  set ℓ := period f x0
  have hℓpos : 0 < ℓ := period_pos hx0
  let P1 : V → Prop := fun v => CompRel f v x0
  let P2 : V → Prop := fun v => ¬ CompRel f v x0
  have hP1 : ∀ v, P1 v → P1 (f v) := fun v hv => compRel_trans (compRel_symm (compRel_step f v)) hv
  have hP2 : ∀ v, P2 v → P2 (f v) := fun v hv h => hv (compRel_trans (compRel_step f v) h)
  have hV2_ne : Nonempty {v : V // P2 v} := by
    unfold IsConnected at hnc
    push Not at hnc
    rcases hnc with ⟨u, v, huv⟩
    by_cases hu : CompRel f u x0
    · exact ⟨⟨v, fun hv => huv (compRel_trans hu (compRel_symm hv))⟩⟩
    · exact ⟨⟨u, hu⟩⟩
  let f1 : {v : V // P1 v} → {v : V // P1 v} := fun ⟨v, hv⟩ => ⟨f v, hP1 v hv⟩
  let f2 : {v : V // P2 v} → {v : V // P2 v} := fun ⟨v, hv⟩ => ⟨f v, hP2 v hv⟩
  have hsplit : Iso f (Sum.map f1 f2) := by
    refine ⟨
      { toFun := fun v => if h : P1 v then Sum.inl ⟨v, h⟩ else Sum.inr ⟨v, h⟩
        invFun := fun x => match x with | Sum.inl ⟨v, _⟩ => v | Sum.inr ⟨v, _⟩ => v
        left_inv := fun v => by by_cases h : P1 v <;> simp [h]
        right_inv := fun x => by
          rcases x with ⟨v, hv⟩ | ⟨v, hv⟩
          · simp only [dif_pos hv]
          · have hv' : ¬ P1 v := hv
            simp only [dif_neg hv'] },
      fun v => ?_⟩
    by_cases hv : P1 v
    · simp only [Equiv.coe_fn_mk, dif_pos hv, dif_pos (hP1 v hv), Sum.map_inl, f1]
    · have hfv : ¬ P1 (f v) := hP2 v hv
      simp only [Equiv.coe_fn_mk, dif_neg hv, dif_neg hfv, Sum.map_inr, f2]
  obtain ⟨p, hp_ge, hp⟩ := Nat.exists_infinite_primes (ℓ + 1)
  have hp_gt : ℓ < p := by omega
  have hp_pos : 0 < p := by omega
  have : NeZero p := ⟨Nat.ne_of_gt hp_pos⟩
  let A := cyc p
  let B := Sum.map (Prod.map (cyc p) f1) (Prod.map (id : ZMod p → ZMod p) f2)
  let Y := Prod.map (id : ZMod p → ZMod p) (cyc p)
  have hprod : Iso (Prod.map f Y) (Prod.map A B) := by
    have hL1 := iso_trans (iso_prod_congr hsplit (iso_refl Y)) (iso_sum_prod_distrib f1 f2 Y)
    have hR1 := iso_prod_sum_distrib A (Prod.map (cyc p) f1) (Prod.map (id : ZMod p → ZMod p) f2)
    have h1 : Iso (Prod.map f1 Y) (Prod.map A (Prod.map (cyc p) f1)) :=
      iso_trans (iso_prod_comm f1 Y)
        (iso_trans (iso_prod_congr (iso_symm (iso_cyc_prod_cyc p)) (iso_refl f1))
          (iso_prod_assoc (cyc p) (cyc p) f1))
    have h2 : Iso (Prod.map f2 Y) (Prod.map A (Prod.map (id : ZMod p → ZMod p) f2)) :=
      iso_trans (iso_prod_comm f2 Y)
        (iso_trans (iso_prod_congr (iso_prod_comm (id : ZMod p → ZMod p) (cyc p)) (iso_refl f2))
          (iso_prod_assoc (cyc p) (id : ZMod p → ZMod p) f2))
    exact iso_trans (iso_trans hL1 (iso_sum_congr h1 h2)) (iso_symm hR1)
  rcases isPrime_prod_dvd hf A B (divides_of_fintype hprod) with ⟨n, g, hfg⟩ | ⟨n, g, hfg⟩
  · have hcard : Fintype.card V * n = p := by
      have h1 := iso_card_eq hfg
      simpa [ZMod.card] using h1
    have hV2 : 2 ≤ Fintype.card V := card_ge_two_of_isPrime hf
    rcases (Nat.dvd_prime hp).mp ⟨n, hcard.symm⟩ with hV1 | hVp
    · omega
    · have hn1 : n = 1 := by
        rw [hVp] at hcard
        exact Nat.eq_of_mul_eq_mul_left hp_pos (by simpa using hcard)
      have hfA : Iso f A := iso_trans (iso_symm (iso_prod_of_card_one f g (by simp [hn1]))) hfg
      exact hnc (isConnected_iso (iso_symm hfA) (isConnected_cyc hp_pos))
  · have hperB : Nat.card (Per B) = p * Nat.card (Per f) := by
      have h1 : Nat.card (Per f) = Nat.card (Per f1) + Nat.card (Per f2) := by
        rw [card_per_iso hsplit, card_per_sum]
      rw [card_per_sum, card_per_prod, card_per_prod, card_per_cyc, card_per_id, ZMod.card,
          ← Nat.mul_add, h1]
    have hperg : Nat.card (Per g) = p := by
      have h1 : Nat.card (Per f) * Nat.card (Per g) = Nat.card (Per f) * p := by
        rw [← card_per_prod, card_per_iso hfg, hperB, Nat.mul_comm]
      have hpos : 0 < Nat.card (Per f) := by
        rw [Nat.card_eq_fintype_card]; exact Fintype.card_pos_iff.mpr (nonempty_per f)
      exact Nat.eq_of_mul_eq_mul_left hpos h1
    rcases hfg with ⟨e, he⟩
    let x0' : {v : V // P1 v} := ⟨x0, compRel_refl f x0⟩
    have hx0' : IsPeriodic f1 x0' := by
      rcases hx0 with ⟨m, hm, hmx⟩
      exact ⟨m, hm, Subtype.ext (by rw [restrict_iterate hP1, hmx])⟩
    have hpx0' : period f1 x0' = ℓ := by
      apply Nat.dvd_antisymm
      · rw [← iterate_eq_self_iff_period_dvd hx0']
        exact Subtype.ext (by rw [restrict_iterate hP1, iterate_period hx0])
      · rw [← iterate_eq_self_iff_period_dvd hx0]
        have h := congrArg Subtype.val (iterate_period hx0')
        rwa [restrict_iterate hP1] at h
    let b0 : (ZMod p × {v : V // P1 v}) ⊕ (ZMod p × {v : V // P2 v}) :=
      Sum.inl ((0 : ZMod p), x0')
    have hb0 : IsPeriodic B b0 :=
      (isPeriodic_sum_inl _).mpr ((isPeriodic_prod_iff _).mpr ⟨isPeriodic_cyc hp_pos 0, hx0'⟩)
    have hpb0 : period B b0 = Nat.lcm p ℓ := by
      rw [period_sum_inl ((isPeriodic_prod_iff _).mpr ⟨isPeriodic_cyc hp_pos 0, hx0'⟩),
          period_prod (isPeriodic_cyc hp_pos 0) hx0', period_cyc hp_pos, hpx0']
    set xy := e.symm b0
    have hxy : IsPeriodic (Prod.map f g) xy :=
      (isPeriodic_iso e he xy).mp (by simpa [xy] using hb0)
    have hx : IsPeriodic f xy.1 := ((isPeriodic_prod_iff xy).mp hxy).1
    have hy : IsPeriodic g xy.2 := ((isPeriodic_prod_iff xy).mp hxy).2
    have hplcm : Nat.lcm (period f xy.1) (period g xy.2) = Nat.lcm p ℓ := by
      rw [← period_prod hx hy, ← period_iso e he xy]
      simp only [xy, Equiv.apply_symm_apply, hpb0]
    have hp_dvd_lcm : p ∣ Nat.lcm (period f xy.1) (period g xy.2) := by
      rw [hplcm]; exact Nat.dvd_lcm_left p ℓ
    have hpx_le : period f xy.1 ≤ ℓ := hmax ⟨xy.1, hx⟩ (Finset.mem_univ _)
    have hp_ndvd_x : ¬ p ∣ period f xy.1 :=
      Nat.not_dvd_of_pos_of_lt (period_pos hx) (by omega)
    have hp_dvd_y : p ∣ period g xy.2 := by
      have hd : p ∣ period f xy.1 * period g xy.2 := dvd_trans hp_dvd_lcm (Nat.lcm_dvd_mul _ _)
      exact (hp.dvd_mul.mp hd).resolve_left hp_ndvd_x
    have hpy_eq : period g xy.2 = p :=
      Nat.le_antisymm (by rw [← hperg]; exact period_le_card_per hy)
        (Nat.le_of_dvd (period_pos hy) hp_dvd_y)
    obtain ⟨⟨x2, hx2⟩⟩ := nonempty_per f2
    have hx2_f : IsPeriodic f x2.1 := by
      rcases hx2 with ⟨m, hm, hmx⟩
      have h := congrArg Subtype.val hmx
      rw [restrict_iterate hP2] at h
      exact ⟨m, hm, h⟩
    have hpx2 : period f2 x2 = period f x2.1 := by
      apply Nat.dvd_antisymm
      · rw [← iterate_eq_self_iff_period_dvd hx2]
        exact Subtype.ext (by rw [restrict_iterate hP2, iterate_period hx2_f])
      · rw [← iterate_eq_self_iff_period_dvd hx2_f]
        have h := congrArg Subtype.val (iterate_period hx2)
        rwa [restrict_iterate hP2] at h
    let b2 : (ZMod p × {v : V // P1 v}) ⊕ (ZMod p × {v : V // P2 v}) :=
      Sum.inr ((0 : ZMod p), x2)
    have hb2 : IsPeriodic B b2 :=
      (isPeriodic_sum_inr _).mpr ((isPeriodic_prod_iff _).mpr ⟨isPeriodic_id 0, hx2⟩)
    have hpb2 : period B b2 ≤ ℓ := by
      rw [period_sum_inr ((isPeriodic_prod_iff _).mpr ⟨isPeriodic_id 0, hx2⟩),
          period_prod (isPeriodic_id 0) hx2, period_id, Nat.lcm_one_left, hpx2]
      exact hmax ⟨x2.1, hx2_f⟩ (Finset.mem_univ _)
    set xy2 := e.symm b2
    have hxy2 : IsPeriodic (Prod.map f g) xy2 :=
      (isPeriodic_iso e he xy2).mp (by simpa [xy2] using hb2)
    have hx' : IsPeriodic f xy2.1 := ((isPeriodic_prod_iff xy2).mp hxy2).1
    have hy' : IsPeriodic g xy2.2 := ((isPeriodic_prod_iff xy2).mp hxy2).2
    have hpy' : period g xy2.2 = p := by
      rw [all_periods_eq_of_card_per_eq_period hy (by rw [hperg, hpy_eq]) hy', hpy_eq]
    have hge_p : p ≤ period B b2 := by
      have h1 : period B b2 = Nat.lcm (period f xy2.1) p := by
        calc period B b2 = period B (e xy2) := by simp [xy2]
          _ = period (Prod.map f g) xy2 := period_iso e he xy2
          _ = Nat.lcm (period f xy2.1) (period g xy2.2) := period_prod hx' hy'
          _ = Nat.lcm (period f xy2.1) p := by rw [hpy']
      rw [h1]
      have hpos : 0 < Nat.lcm (period f xy2.1) p :=
        Nat.pos_of_ne_zero (Nat.lcm_ne_zero (Nat.ne_of_gt (period_pos hx')) (Nat.ne_of_gt hp_pos))
      exact Nat.le_of_dvd hpos (Nat.dvd_lcm_right _ _)
    omega

end Connectedness

section F1Reduction

/-- Minimum number of steps from `v` to the periodic vertex `x0` in a connected digraph. -/
noncomputable def distTo {V : Type} (f : V → V) (x0 : V) (hc : IsConnected f)
    (hx0 : IsPeriodic f x0) (v : V) : ℕ :=
  open Classical in Nat.find (periodic_reaches_of_compRel hx0 (hc v x0))

lemma iterate_distTo {V : Type} {f : V → V} {x0 : V} (hc : IsConnected f)
    (hx0 : IsPeriodic f x0) (v : V) :
    f^[distTo f x0 hc hx0 v] v = x0 := by
  classical
  exact Nat.find_spec (periodic_reaches_of_compRel hx0 (hc v x0))

lemma distTo_le {V : Type} {f : V → V} {x0 : V} (hc : IsConnected f)
    (hx0 : IsPeriodic f x0) {v : V} {k : ℕ} (hk : f^[k] v = x0) :
    distTo f x0 hc hx0 v ≤ k := by
  classical
  exact Nat.find_min' (periodic_reaches_of_compRel hx0 (hc v x0)) hk

lemma distTo_self {V : Type} {f : V → V} {x0 : V} (hc : IsConnected f)
    (hx0 : IsPeriodic f x0) : distTo f x0 hc hx0 x0 = 0 :=
  Nat.eq_zero_of_le_zero (distTo_le hc hx0 rfl)

lemma distTo_step_zmod {V : Type} {f : V → V} {x0 : V} (hc : IsConnected f)
    (hx0 : IsPeriodic f x0) (v : V) :
    ((distTo f x0 hc hx0 (f v) : ZMod (period f x0)) + 1) =
      (distTo f x0 hc hx0 v : ZMod (period f x0)) := by
  set ℓ := period f x0
  have hℓpos : 0 < ℓ := period_pos hx0
  by_cases hv : v = x0
  · rw [hv, distTo_self]
    have hle : distTo f x0 hc hx0 (f x0) ≤ ℓ - 1 := by
      apply distTo_le hc hx0
      rw [← Function.iterate_succ_apply, Nat.succ_eq_add_one, Nat.sub_add_cancel hℓpos]
      exact iterate_period hx0
    have hdvd : ℓ ∣ distTo f x0 hc hx0 (f x0) + 1 := by
      rw [← iterate_eq_self_iff_period_dvd hx0, Function.iterate_succ_apply]
      exact iterate_distTo hc hx0 (f x0)
    have heq : distTo f x0 hc hx0 (f x0) + 1 = ℓ :=
      Nat.le_antisymm (by omega) (Nat.le_of_dvd (Nat.succ_pos _) hdvd)
    rw [← Nat.cast_one, ← Nat.cast_add, heq, ZMod.natCast_self, Nat.cast_zero]
  · have hpos : 0 < distTo f x0 hc hx0 v := by
      by_contra h0
      have hz : distTo f x0 hc hx0 v = 0 := by omega
      have h := iterate_distTo hc hx0 v
      rw [hz] at h
      exact hv h
    have hle1 : distTo f x0 hc hx0 (f v) ≤ distTo f x0 hc hx0 v - 1 := by
      apply distTo_le hc hx0
      rw [← Function.iterate_succ_apply, Nat.succ_eq_add_one, Nat.sub_add_cancel hpos]
      exact iterate_distTo hc hx0 v
    have hle2 : distTo f x0 hc hx0 v ≤ distTo f x0 hc hx0 (f v) + 1 := by
      apply distTo_le hc hx0
      rw [Function.iterate_succ_apply]
      exact iterate_distTo hc hx0 (f v)
    have heq : distTo f x0 hc hx0 (f v) + 1 = distTo f x0 hc hx0 v := by omega
    rw [← Nat.cast_one, ← Nat.cast_add, heq]

lemma distTo_step_zmod_of_dvd {V : Type} {f : V → V} {x0 : V} (hc : IsConnected f)
    (hx0 : IsPeriodic f x0) {g : ℕ} (hg : g ∣ period f x0) (v : V) :
    ((distTo f x0 hc hx0 (f v) : ZMod g) + 1) = (distTo f x0 hc hx0 v : ZMod g) := by
  have h := congrArg (ZMod.castHom hg (ZMod g)) (distTo_step_zmod hc hx0 v)
  simpa [map_add, map_one] using h

/-- Lemma 2.2(b): If `n ∣ ℓ`, then `C_n × f ≅ id_(ZMod n) × f`. -/
lemma iso_cyc_prod_of_dvd {V : Type} {f : V → V} {x0 : V} (hc : IsConnected f)
    (hx0 : IsPeriodic f x0) {n : ℕ} (hn : n ∣ period f x0) :
    Iso (Prod.map (cyc n) f) (Prod.map (id : ZMod n → ZMod n) f) := by
  let d : V → ZMod n := fun v => (distTo f x0 hc hx0 v : ZMod n)
  refine ⟨
    { toFun := fun ⟨i, v⟩ => (i + d v, v)
      invFun := fun ⟨j, v⟩ => (j - d v, v)
      left_inv := fun ⟨i, v⟩ => by simp
      right_inv := fun ⟨j, v⟩ => by simp },
    fun ⟨i, v⟩ => ?_⟩
  simp only [Equiv.coe_fn_mk, Prod.map_apply, id_eq, cyc, Prod.mk.injEq, and_true]
  have hstep := distTo_step_zmod_of_dvd hc hx0 hn v
  change i + 1 + d (f v) = i + d v
  rw [add_assoc, add_comm (1 : ZMod n), hstep]

/-- Lemma 2.2(a): For `n > 0` and `g = gcd n ℓ`, `C_n × f ≅ id_(ZMod g) × f'` for a subdigraph `f'`. -/
lemma exists_iso_cyc_prod {V : Type} [Fintype V] {f : V → V} {x0 : V} (hc : IsConnected f)
    (hx0 : IsPeriodic f x0) (n : ℕ) [NeZero n] :
    ∃ (V' : Type) (_ : Fintype V') (f' : V' → V'),
      Iso (Prod.map (cyc n) f)
        (Prod.map (id : ZMod (Nat.gcd n (period f x0)) → ZMod (Nat.gcd n (period f x0))) f') := by
  classical
  set g := Nat.gcd n (period f x0)
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left _ (NeZero.pos n)
  have : NeZero g := ⟨Nat.ne_of_gt hgpos⟩
  let castN := ZMod.castHom (Nat.gcd_dvd_left n (period f x0)) (ZMod g)
  let r : ZMod n × V → ZMod g := fun p => castN p.1 + (distTo f x0 hc hx0 p.2 : ZMod g)
  have hr_inv : ∀ p, r (Prod.map (cyc n) f p) = r p := by
    rintro ⟨i, v⟩
    simp only [r, Prod.map_apply, cyc, map_add, map_one]
    have hstep := distTo_step_zmod_of_dvd hc hx0 (Nat.gcd_dvd_right n (period f x0)) v
    rw [add_assoc, add_comm (1 : ZMod g), hstep]
  let V' := {p : ZMod n × V // r p = 0}
  let f' : V' → V' := fun ⟨p, hp⟩ => ⟨Prod.map (cyc n) f p, by rw [hr_inv, hp]⟩
  have hcast_val : ∀ k : ZMod g, castN (k.val : ZMod n) = k := by
    intro k
    simp [castN]
  refine ⟨V', inferInstance, f', ?_⟩
  refine ⟨
    { toFun := fun p => (r p, ⟨(p.1 - ((r p).val : ZMod n), p.2), by
        simp [r, map_sub]⟩)
      invFun := fun ⟨k, ⟨⟨i, v⟩, _⟩⟩ => (i + (k.val : ZMod n), v)
      left_inv := fun ⟨i, v⟩ => by simp
      right_inv := fun ⟨k, ⟨⟨i, v⟩, h0⟩⟩ => by
        have hrk : r (i + (k.val : ZMod n), v) = k := by
          have h0' : castN i + (distTo f x0 hc hx0 v : ZMod g) = 0 := h0
          simp only [r, map_add, hcast_val]
          calc castN i + k + (distTo f x0 hc hx0 v : ZMod g)
              = (castN i + (distTo f x0 hc hx0 v : ZMod g)) + k := by ring
            _ = k := by rw [h0', zero_add]
        apply Prod.ext
        · exact hrk
        · apply Subtype.ext
          apply Prod.ext
          · change i + (k.val : ZMod n) - ((r (i + (k.val : ZMod n), v)).val : ZMod n) = i
            rw [hrk]; ring
          · rfl },
    fun ⟨i, v⟩ => ?_⟩
  apply Prod.ext
  · exact hr_inv (i, v)
  · apply Subtype.ext
    apply Prod.ext
    · change i + 1 - ((r (i + 1, f v)).val : ZMod n) = i - ((r (i, v)).val : ZMod n) + 1
      have h := hr_inv (i, v)
      simp only [Prod.map_apply, cyc] at h
      rw [h]; ring
    · rfl

lemma iso_cyc_of_connected_card_eq_period {V : Type} [Fintype V] {f : V → V} {x0 : V}
    (_hc : IsConnected f) (hx0 : IsPeriodic f x0) (hcard : Fintype.card V = period f x0) :
    Iso (cyc (period f x0)) f := by
  set q := period f x0
  have hqpos : 0 < q := period_pos hx0
  have : NeZero q := ⟨Nat.ne_of_gt hqpos⟩
  let toV : ZMod q → V := fun i => f^[i.val] x0
  have hinj : Function.Injective toV := by
    intro i j hij
    have h := @orbit_injective V f x0 hx0 ⟨i.val, ZMod.val_lt i⟩ ⟨j.val, ZMod.val_lt j⟩
      (Subtype.ext hij)
    exact (ZMod.val_injective q) (congrArg Fin.val h)
  have hbij : Function.Bijective toV :=
    (Fintype.bijective_iff_injective_and_card toV).mpr ⟨hinj, by rw [ZMod.card, hcard]⟩
  refine ⟨Equiv.ofBijective toV hbij, fun i => ?_⟩
  change f^[(i + 1).val] x0 = f (f^[i.val] x0)
  rw [← Function.iterate_succ_apply' f i.val x0]
  have hval : (i + 1).val = (i.val + 1) % q := by
    rw [ZMod.val_add, ZMod.val_one_eq_one_mod, Nat.add_mod_mod]
  rw [hval]
  have hdiv : i.val + 1 = q * ((i.val + 1) / q) + (i.val + 1) % q := (Nat.div_add_mod _ _).symm
  conv_rhs => rw [Nat.succ_eq_add_one, hdiv, Nat.add_comm, Function.iterate_add_apply,
                  Nat.mul_comm, iterate_mul_period hx0]

lemma sq_dvd_of_lcm_eq_sq {ℓ d : ℕ} (hℓ : 0 < ℓ) (h : Nat.lcm ℓ d = ℓ * ℓ) : ℓ * ℓ ∣ d := by
  have hℓ0 : ℓ ≠ 0 := Nat.ne_of_gt hℓ
  have hd0 : d ≠ 0 := by
    intro h0; rw [h0, Nat.lcm_zero_right] at h
    exact Nat.mul_ne_zero hℓ0 hℓ0 h.symm
  rw [← Nat.factorization_le_iff_dvd (Nat.mul_ne_zero hℓ0 hℓ0) hd0]
  intro r
  have h1 : (ℓ * ℓ).factorization r = max (ℓ.factorization r) (d.factorization r) := by
    rw [← h, Nat.factorization_lcm hℓ0 hd0]
    rfl
  rw [Nat.factorization_mul hℓ0 hℓ0, Finsupp.add_apply] at h1 ⊢
  omega

lemma lcm_pow_ne_mul_pow {p α d : ℕ} (hp : p.Prime) (hα : 1 ≤ α) (hd1 : 1 ≤ d) (hdp : d ≤ p) :
    Nat.lcm (p ^ α) d ≠ p * p ^ α := by
  intro heq
  have hp0 : p ≠ 0 := hp.ne_zero
  have hq0 : p ^ α ≠ 0 := pow_ne_zero α hp0
  have hd0 : d ≠ 0 := by omega
  have h1 := congrArg (fun n => n.factorization p) heq
  rw [Nat.factorization_lcm hq0 hd0, Finsupp.sup_apply, Nat.factorization_mul hp0 hq0,
      Finsupp.add_apply, hp.factorization_self, hp.factorization_pow, Finsupp.single_eq_same] at h1
  have hdf : d.factorization p ≤ 1 := by
    by_contra hgt
    have h2 : 2 ≤ d.factorization p := by omega
    have hdvd : p ^ 2 ∣ d := dvd_trans (pow_dvd_pow p h2) (Nat.ordProj_dvd d p)
    have hle : p ^ 2 ≤ d := Nat.le_of_dvd (by omega) hdvd
    have hp2 : 2 ≤ p := hp.two_le
    nlinarith
  have hmax : (α ⊔ d.factorization p) = α := Nat.max_eq_left (by omega)
  rw [hmax] at h1
  omega

/-- Case 1 of Lemma 3: a prime connected digraph with `|V| = p^α` cannot have `p^α ∣ ℓ`. -/
lemma not_card_eq_prime_pow_of_isPrime {V : Type} [Fintype V] [Nonempty V] {f : V → V}
    (hf : IsPrime f) (hc : IsConnected f) {x0 : V} (hx0 : IsPeriodic f x0)
    {p α : ℕ} (hp : p.Prime) (hα : 1 ≤ α) (hq_dvd : p ^ α ∣ period f x0)
    (hcardq : Fintype.card V = p ^ α) : False := by
  classical
  set q := p ^ α
  have hℓpos : 0 < period f x0 := period_pos hx0
  have hq_pos : 0 < q := pow_pos hp.pos α
  have : NeZero p := ⟨hp.ne_zero⟩
  have : NeZero q := ⟨Nat.ne_of_gt hq_pos⟩
  have : NeZero (p * q) := ⟨Nat.mul_ne_zero hp.ne_zero (Nat.ne_of_gt hq_pos)⟩
  have hℓ_le_V : period f x0 ≤ Fintype.card V := by
    rw [← card_per_eq_period_of_connected hc hx0, Nat.card_eq_fintype_card]
    exact Fintype.card_subtype_le _
  have hℓ_eq_q : period f x0 = q :=
    Nat.le_antisymm (by omega) (Nat.le_of_dvd hℓpos hq_dvd)
  have hf_cyc : Iso f (cyc q) := by
    have h := iso_cyc_of_connected_card_eq_period hc hx0 (by rw [hcardq, hℓ_eq_q])
    rw [hℓ_eq_q] at h
    exact iso_symm h
  let Y := Prod.map (id : ZMod p → ZMod p) (cyc (p * q))
  have hprod : Iso (Prod.map f Y) (Prod.map (cyc (p * q)) (cyc (p * q))) := by
    have h1 : Iso (Prod.map (cyc q) Y)
        (Prod.map (id : ZMod (p * q) → ZMod (p * q)) (cyc (p * q))) := by
      have h1a : Iso (Prod.map (cyc q) Y)
          (Prod.map (id : ZMod p → ZMod p) (Prod.map (cyc q) (cyc (p * q)))) :=
        iso_trans (iso_symm (iso_prod_assoc (cyc q) (id : ZMod p → ZMod p) (cyc (p * q))))
          (iso_trans (iso_prod_congr (iso_prod_comm (cyc q) (id : ZMod p → ZMod p))
            (iso_refl (cyc (p * q))))
            (iso_prod_assoc (id : ZMod p → ZMod p) (cyc q) (cyc (p * q))))
      have h1b := iso_prod_congr (iso_refl (id : ZMod p → ZMod p)) (iso_cyc_prod_cyc_mul p q)
      have h1c := iso_symm (iso_prod_assoc (id : ZMod p → ZMod p) (id : ZMod q → ZMod q) (cyc (p * q)))
      have hid : Iso (Prod.map (id : ZMod p → ZMod p) (id : ZMod q → ZMod q))
          (id : ZMod (p * q) → ZMod (p * q)) :=
        ⟨Fintype.equivOfCardEq (by simp [ZMod.card]), fun _ => rfl⟩
      exact iso_trans h1a (iso_trans h1b (iso_trans h1c (iso_prod_congr hid (iso_refl _))))
    exact iso_trans (iso_prod_congr hf_cyc (iso_refl Y))
      (iso_trans h1 (iso_symm (iso_cyc_prod_cyc (p * q))))
  have hdvd : Divides f (cyc (p * q)) := by
    rcases isPrime_prod_dvd hf (cyc (p * q)) (cyc (p * q)) (divides_of_fintype hprod) with
      h | h <;> exact h
  rcases hdvd with ⟨n, g, hfg⟩
  have hperg : Nat.card (Per g) = p := by
    have h1 : q * Nat.card (Per g) = q * p := by
      have h2 := card_per_iso hfg
      rw [card_per_prod, card_per_eq_period_of_connected hc hx0, hℓ_eq_q, card_per_cyc,
          Nat.mul_comm p q] at h2
      exact h2
    exact Nat.eq_of_mul_eq_mul_left hq_pos h1
  rcases hfg with ⟨e, he⟩
  set xy := e.symm (0 : ZMod (p * q))
  have hxy : IsPeriodic (Prod.map f g) xy :=
    (isPeriodic_iso e he xy).mp (by simpa [xy] using isPeriodic_cyc (Nat.mul_pos hp.pos hq_pos) 0)
  have hx : IsPeriodic f xy.1 := ((isPeriodic_prod_iff xy).mp hxy).1
  have hy : IsPeriodic g xy.2 := ((isPeriodic_prod_iff xy).mp hxy).2
  have hpx : period f xy.1 = q := by
    rw [all_periods_eq_of_card_per_eq_period hx0 (card_per_eq_period_of_connected hc hx0) hx, hℓ_eq_q]
  have hlcm : Nat.lcm q (period g xy.2) = p * q := by
    calc Nat.lcm q (period g xy.2)
        = Nat.lcm (period f xy.1) (period g xy.2) := by rw [hpx]
      _ = period (Prod.map f g) xy := (period_prod hx hy).symm
      _ = period (cyc (p * q)) (e xy) := (period_iso e he xy).symm
      _ = period (cyc (p * q)) 0 := by simp [xy]
      _ = p * q := period_cyc (Nat.mul_pos hp.pos hq_pos) 0
  exact lcm_pow_ne_mul_pow hp hα (period_pos hy) (by rw [← hperg]; exact period_le_card_per hy) hlcm

/-- Lemma 3 (Richard 2025): Every connected prime functional digraph has a cycle of length 1. -/
lemma period_eq_one_of_isPrime_connected {V : Type} [Fintype V] [Nonempty V] {f : V → V}
    (hf : IsPrime f) (hc : IsConnected f) {x0 : V} (hx0 : IsPeriodic f x0) :
    period f x0 = 1 := by
  classical
  set ℓ := period f x0 with hℓ_def
  have hℓpos : 0 < ℓ := period_pos hx0
  by_contra hne1
  obtain ⟨p, hp, hp_dvd⟩ := Nat.exists_prime_and_dvd (by omega : ℓ ≠ 1)
  set α := ℓ.factorization p
  have hα : 1 ≤ α := Nat.Prime.factorization_pos_of_dvd hp (Nat.ne_of_gt hℓpos) hp_dvd
  set q := p ^ α
  have hq_dvd : q ∣ ℓ := Nat.ordProj_dvd ℓ p
  have hq_pos : 0 < q := pow_pos hp.pos α
  have hq_ge2 : 2 ≤ q := by
    calc 2 ≤ p := hp.two_le
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ α := Nat.pow_le_pow_right hp.pos hα
  by_cases hcardq : Fintype.card V = q
  · exact not_card_eq_prime_pow_of_isPrime hf hc hx0 hp hα hq_dvd hcardq
  · set m := ℓ / q
    have hqm : q * m = ℓ := Nat.mul_div_cancel' hq_dvd
    have hm_pos : 0 < m := Nat.div_pos (Nat.le_of_dvd hℓpos hq_dvd) hq_pos
    have hm_lt : m < ℓ := by nlinarith
    have hcop : Nat.Coprime q m := by
      rw [Nat.coprime_pow_left_iff hα, hp.coprime_iff_not_dvd]
      intro hd
      have h1 : p ^ (α + 1) ∣ ℓ := by
        rcases hd with ⟨c, hmc⟩
        exact ⟨c, by rw [← hqm, hmc, pow_succ, mul_assoc]⟩
      exact Nat.pow_succ_factorization_not_dvd (Nat.ne_of_gt hℓpos) hp h1
    have : NeZero ℓ := ⟨Nat.ne_of_gt hℓpos⟩
    have : NeZero q := ⟨Nat.ne_of_gt hq_pos⟩
    have : NeZero m := ⟨Nat.ne_of_gt hm_pos⟩
    have : NeZero (ℓ * ℓ) := ⟨Nat.mul_ne_zero (Nat.ne_of_gt hℓpos) (Nat.ne_of_gt hℓpos)⟩
    obtain ⟨V', hfin', f', hf'iso⟩ := exists_iso_cyc_prod hc hx0 (ℓ * ℓ)
    have hgcd : Nat.gcd (ℓ * ℓ) (period f x0) = ℓ := by
      rw [← hℓ_def]; exact Nat.gcd_eq_right (dvd_mul_left ℓ ℓ)
    have hf'iso' : Iso (Prod.map (cyc (ℓ * ℓ)) f) (Prod.map (id : ZMod ℓ → ZMod ℓ) f') := by
      rw [hgcd] at hf'iso; exact hf'iso
    have hper_f' : Nat.card (Per f') = ℓ * ℓ := by
      have h1 := card_per_iso hf'iso'
      rw [card_per_prod, card_per_prod, card_per_cyc, card_per_id, ZMod.card,
          card_per_eq_period_of_connected hc hx0, ← hℓ_def] at h1
      exact Nat.eq_of_mul_eq_mul_left hℓpos (by rw [← h1]; ring)
    have hV'_ne : Nonempty (Per f') := by
      have hpos : 0 < Fintype.card (Per f') := by
        rw [← Nat.card_eq_fintype_card, hper_f']; exact Nat.mul_pos hℓpos hℓpos
      exact Fintype.card_pos_iff.mp hpos
    obtain ⟨⟨v0', hv0'⟩⟩ := hV'_ne
    have hper_v0' : ∀ u' : V', IsPeriodic f' u' → period f' u' = ℓ * ℓ := by
      intro u' hu'
      rcases hf'iso' with ⟨e, he⟩
      set ab := e.symm (0, u')
      have hab : IsPeriodic (Prod.map (cyc (ℓ * ℓ)) f) ab :=
        (isPeriodic_iso e he ab).mp (by
          simpa [ab] using (isPeriodic_prod_iff ((0 : ZMod ℓ), u')).mpr ⟨isPeriodic_id 0, hu'⟩)
      have hb : IsPeriodic f ab.2 := ((isPeriodic_prod_iff ab).mp hab).2
      have hpb : period f ab.2 = ℓ :=
        all_periods_eq_of_card_per_eq_period hx0 (card_per_eq_period_of_connected hc hx0) hb
      have h1 : period (Prod.map (id : ZMod ℓ → ZMod ℓ) f') (0, u') =
          period (Prod.map (cyc (ℓ * ℓ)) f) ab := by
        rw [← period_iso e he ab]; simp [ab]
      rw [period_prod (isPeriodic_id 0) hu', period_id, Nat.lcm_one_left,
          period_prod (isPeriodic_cyc (Nat.mul_pos hℓpos hℓpos) ab.1) hb,
          period_cyc (Nat.mul_pos hℓpos hℓpos), hpb] at h1
      rw [h1]
      exact Nat.lcm_eq_left (dvd_mul_left ℓ ℓ)
    have hf'_conn : IsConnected f' :=
      isConnected_of_card_per_eq_period hv0' (by rw [hper_f', hper_v0' v0' hv0'])
    have hstep1 : Iso (Prod.map (cyc ℓ) f') (Prod.map (id : ZMod ℓ → ZMod ℓ) f') :=
      iso_cyc_prod_of_dvd hf'_conn hv0' (by rw [hper_v0' v0' hv0']; exact dvd_mul_left ℓ ℓ)
    have hstep2 : Iso (cyc ℓ) (Prod.map (cyc q) (cyc m)) := by
      have h := iso_cyc_mul_of_coprime hcop
      rwa [hqm] at h
    have hprod : Iso (Prod.map f (cyc (ℓ * ℓ))) (Prod.map (cyc q) (Prod.map (cyc m) f')) :=
      iso_trans (iso_prod_comm f (cyc (ℓ * ℓ)))
        (iso_trans hf'iso'
          (iso_trans (iso_symm hstep1)
            (iso_trans (iso_prod_congr hstep2 (iso_refl f'))
              (iso_prod_assoc (cyc q) (cyc m) f'))))
    rcases isPrime_prod_dvd hf (cyc q) (Prod.map (cyc m) f') (divides_of_fintype hprod) with
      ⟨n, g, hfg⟩ | ⟨n, g, hfg⟩
    · rcases hfg with ⟨e, he⟩
      set xy := e.symm (0 : ZMod q)
      have hxy : IsPeriodic (Prod.map f g) xy :=
        (isPeriodic_iso e he xy).mp (by simpa [xy] using isPeriodic_cyc hq_pos 0)
      have hx : IsPeriodic f xy.1 := ((isPeriodic_prod_iff xy).mp hxy).1
      have hy : IsPeriodic g xy.2 := ((isPeriodic_prod_iff xy).mp hxy).2
      have hpx : period f xy.1 = ℓ :=
        all_periods_eq_of_card_per_eq_period hx0 (card_per_eq_period_of_connected hc hx0) hx
      have hlcm : Nat.lcm ℓ (period g xy.2) = q := by
        rw [← hpx, ← period_prod hx hy, ← period_iso e he xy]
        simp only [xy, Equiv.apply_symm_apply]
        exact period_cyc hq_pos 0
      have hcard_dvd : Fintype.card V ∣ q := by
        refine ⟨n, ?_⟩
        have h1 := iso_card_eq ⟨e, he⟩
        simpa [ZMod.card] using h1.symm
      have hcard_le : Fintype.card V ≤ q := Nat.le_of_dvd hq_pos hcard_dvd
      have hℓ_le_V : ℓ ≤ Fintype.card V := by
        rw [hℓ_def, ← card_per_eq_period_of_connected hc hx0, Nat.card_eq_fintype_card]
        exact Fintype.card_subtype_le _
      have hq_le_ℓ : q ≤ ℓ := Nat.le_of_dvd hℓpos hq_dvd
      exact hcardq (by omega)
    · rcases hfg with ⟨e, he⟩
      set xy := e.symm ((0 : ZMod m), v0')
      have hxy : IsPeriodic (Prod.map f g) xy :=
        (isPeriodic_iso e he xy).mp (by
          simpa [xy] using (isPeriodic_prod_iff ((0 : ZMod m), v0')).mpr ⟨isPeriodic_cyc hm_pos 0, hv0'⟩)
      have hx : IsPeriodic f xy.1 := ((isPeriodic_prod_iff xy).mp hxy).1
      have hy : IsPeriodic g xy.2 := ((isPeriodic_prod_iff xy).mp hxy).2
      have hpx : period f xy.1 = ℓ :=
        all_periods_eq_of_card_per_eq_period hx0 (card_per_eq_period_of_connected hc hx0) hx
      have hlcm : Nat.lcm ℓ (period g xy.2) = ℓ * ℓ := by
        calc Nat.lcm ℓ (period g xy.2)
            = Nat.lcm (period f xy.1) (period g xy.2) := by rw [hpx]
          _ = period (Prod.map f g) xy := (period_prod hx hy).symm
          _ = period (Prod.map (cyc m) f') (e xy) := (period_iso e he xy).symm
          _ = period (Prod.map (cyc m) f') ((0 : ZMod m), v0') := by simp [xy]
          _ = Nat.lcm (period (cyc m) 0) (period f' v0') := period_prod (isPeriodic_cyc hm_pos 0) hv0'
          _ = Nat.lcm m (ℓ * ℓ) := by rw [period_cyc hm_pos, hper_v0' v0' hv0']
          _ = ℓ * ℓ := Nat.lcm_eq_right (dvd_trans ⟨q, by rw [mul_comm, hqm]⟩ (dvd_mul_left ℓ ℓ))
      have hdvd_y : ℓ * ℓ ∣ period g xy.2 := sq_dvd_of_lcm_eq_sq hℓpos hlcm
      have hy_ge : ℓ * ℓ ≤ Nat.card (Per g) :=
        le_trans (Nat.le_of_dvd (period_pos hy) hdvd_y) (period_le_card_per hy)
      have hper_eq : ℓ * Nat.card (Per g) = m * (ℓ * ℓ) := by
        have h1 := card_per_iso ⟨e, he⟩
        rw [card_per_prod, card_per_prod, card_per_eq_period_of_connected hc hx0,
            ← hℓ_def, card_per_cyc, hper_f'] at h1
        exact h1
      have hge : ℓ * (ℓ * ℓ) ≤ m * (ℓ * ℓ) := by
        rw [← hper_eq]; exact Nat.mul_le_mul_left ℓ hy_ge
      have hlt : m * (ℓ * ℓ) < ℓ * (ℓ * ℓ) :=
        Nat.mul_lt_mul_of_pos_right hm_lt (Nat.mul_pos hℓpos hℓpos)
      omega

end F1Reduction

section SeifertF1

/-- Depth of `x` in an `F_1` functional digraph with fixed point `χ`. -/
noncomputable def depth {V : Type} (f : V → V) (χ : V)
    (hreach : ∀ v : V, ∃ k : ℕ, f^[k] v = χ) (v : V) : ℕ :=
  open Classical in Nat.find (hreach v)

lemma iterate_depth {V : Type} {f : V → V} {χ : V}
    (hreach : ∀ v : V, ∃ k : ℕ, f^[k] v = χ) (v : V) :
    f^[depth f χ hreach v] v = χ := by
  classical exact Nat.find_spec (hreach v)

lemma depth_le {V : Type} {f : V → V} {χ : V}
    (hreach : ∀ v : V, ∃ k : ℕ, f^[k] v = χ) {v : V} {k : ℕ} (hk : f^[k] v = χ) :
    depth f χ hreach v ≤ k := by
  classical exact Nat.find_min' (hreach v) hk

lemma depth_eq_zero_iff {V : Type} {f : V → V} {χ : V}
    (hreach : ∀ v : V, ∃ k : ℕ, f^[k] v = χ) (v : V) :
    depth f χ hreach v = 0 ↔ v = χ := by
  constructor
  · intro h; have := iterate_depth hreach v; rwa [h] at this
  · rintro rfl; exact Nat.eq_zero_of_le_zero (depth_le hreach rfl)

lemma iterate_eq_fix_iff_depth_le {V : Type} {f : V → V} {χ : V} (hfix : f χ = χ)
    (hreach : ∀ v : V, ∃ k : ℕ, f^[k] v = χ) (v : V) (k : ℕ) :
    f^[k] v = χ ↔ depth f χ hreach v ≤ k := by
  constructor
  · exact depth_le hreach
  · intro hle
    have hfix_it : ∀ m, f^[m] χ = χ := fun m => by
      induction m with
      | zero => rfl
      | succ m ih => rw [Function.iterate_succ_apply, hfix, ih]
    rw [← Nat.sub_add_cancel hle, Function.iterate_add_apply, iterate_depth hreach, hfix_it]

lemma depth_step {V : Type} {f : V → V} {χ : V} (hfix : f χ = χ)
    (hreach : ∀ v : V, ∃ k : ℕ, f^[k] v = χ) (v : V) :
    depth f χ hreach (f v) = depth f χ hreach v - 1 := by
  by_cases hv : v = χ
  · rw [hv, hfix, (depth_eq_zero_iff hreach χ).mpr rfl]
  · have hpos : 0 < depth f χ hreach v := by
      have hne := mt (depth_eq_zero_iff hreach v).mp hv; omega
    apply Nat.le_antisymm
    · apply depth_le hreach
      rw [← Function.iterate_succ_apply, Nat.succ_eq_add_one, Nat.sub_add_cancel hpos]
      exact iterate_depth hreach v
    · have h := depth_le hreach (v := v) (k := depth f χ hreach (f v) + 1) (by
        rw [Function.iterate_succ_apply]; exact iterate_depth hreach (f v))
      omega

/-- Extended functional digraph `X_ext = X + t` with `X_ext(t) = xhat`. -/
def Xext {V : Type} (f : V → V) (xhat : V) : Option V → Option V
  | some x => some (f x)
  | none => some xhat

lemma Xext_iterate_some {V : Type} (f : V → V) (xhat : V) (k : ℕ) (x : V) :
    (Xext f xhat)^[k] (some x) = some (f^[k] x) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Xext]
    exact ih (f x)

lemma Xext_iterate_none_succ {V : Type} (f : V → V) (xhat : V) (k : ℕ) :
    (Xext f xhat)^[k + 1] none = some (f^[k] xhat) := by
  rw [Function.iterate_succ_apply, Xext, Xext_iterate_some]

/-- Extended depth on `Option V`: `some x ↦ depth x`, `none ↦ d + 1`. -/
noncomputable def depthExt {V : Type} (f : V → V) (χ : V)
    (hreach : ∀ v : V, ∃ k : ℕ, f^[k] v = χ) (d : ℕ) : Option V → ℕ
  | some x => depth f χ hreach x
  | none => d + 1

lemma depthExt_step {V : Type} {f : V → V} {χ xhat : V} (hfix : f χ = χ)
    (hreach : ∀ v : V, ∃ k : ℕ, f^[k] v = χ) {d : ℕ} (hxhat : depth f χ hreach xhat = d)
    (v : Option V) :
    depthExt f χ hreach d (Xext f xhat v) = depthExt f χ hreach d v - 1 := by
  cases v with
  | none => simp [Xext, depthExt, hxhat]
  | some x => simp [Xext, depthExt, depth_step hfix hreach x]

/-- Path functional digraph `P` on `Fin (d + 1)`: `i ↦ max(i - 1, 0)`. -/
def pathFn (d : ℕ) (i : Fin (d + 1)) : Fin (d + 1) := ⟨i.val - 1, by omega⟩

/-- Vertex type of Seifert's functional digraph `B`. -/
abbrev SeifertVB {V : Type} (f : V → V) (χ : V)
    (hreach : ∀ v : V, ∃ k : ℕ, f^[k] v = χ) (d : ℕ) : Type :=
  ∀ j : Fin (d + 1), {v : Option V // depthExt f χ hreach d v ≤ j.val + 1}

/-- Transition map of Seifert's functional digraph `B`. -/
noncomputable def seifertB {V : Type} {f : V → V} {χ xhat : V} (hfix : f χ = χ)
    (hreach : ∀ v : V, ∃ k : ℕ, f^[k] v = χ) {d : ℕ} (hxhat : depth f χ hreach xhat = d)
    (b : SeifertVB f χ hreach d) : SeifertVB f χ hreach d :=
  fun j =>
    if h : j.val < d then
      ⟨Xext f xhat (b ⟨j.val + 1, by omega⟩).1, by
        rw [depthExt_step hfix hreach hxhat]
        have := (b ⟨j.val + 1, by omega⟩).2
        dsimp only at this
        omega⟩
    else
      ⟨none, by have := j.isLt; simp [depthExt]; omega⟩

/-- Fixed point `β` of `seifertB`. -/
noncomputable def seifertBeta {V : Type} {f : V → V} {χ xhat : V} (hfix : f χ = χ)
    (hreach : ∀ v : V, ∃ k : ℕ, f^[k] v = χ) {d : ℕ} (hxhat : depth f χ hreach xhat = d) :
    SeifertVB f χ hreach d :=
  fun j => ⟨(Xext f xhat)^[d - j.val] none, by
    have hiter : ∀ k, depthExt f χ hreach d ((Xext f xhat)^[k] none) = d + 1 - k := by
      intro k
      induction k with
      | zero => simp [depthExt]
      | succ k ih =>
        rw [Function.iterate_succ_apply', depthExt_step hfix hreach hxhat, ih]
        omega
    rw [hiter]
    have hjle : j.val ≤ d := Nat.lt_succ_iff.mp j.isLt
    omega⟩

/-- Unified iterate formula for `seifertB`. -/
lemma seifertB_iterate {V : Type} {f : V → V} {χ xhat : V} (hfix : f χ = χ)
    (hreach : ∀ v : V, ∃ k : ℕ, f^[k] v = χ) {d : ℕ} (hxhat : depth f χ hreach xhat = d)
    (k : ℕ) (b : SeifertVB f χ hreach d) (j : Fin (d + 1)) :
    ((seifertB hfix hreach hxhat)^[k] b j).1 =
      if h : j.val + k ≤ d then
        (Xext f xhat)^[k] (b ⟨j.val + k, by omega⟩).1
      else
        (seifertBeta hfix hreach hxhat j).1 := by
  induction k generalizing j with
  | zero =>
    have hj : j.val + 0 ≤ d := by have := j.isLt; omega
    simp only [Function.iterate_zero_apply, dif_pos hj]
    exact congrArg (fun idx => (b idx).1) (Fin.ext (Nat.add_zero j.val).symm)
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    simp only [seifertB]
    have hjlt := j.isLt
    by_cases hjd : j.val < d
    · simp only [dif_pos hjd]
      rw [ih ⟨j.val + 1, by omega⟩]
      by_cases hle : j.val + (k + 1) ≤ d
      · have hle1 : j.val + 1 + k ≤ d := by omega
        simp only [dif_pos hle1, dif_pos hle]
        rw [← Function.iterate_succ_apply' (Xext f xhat) k]
        exact congrArg (fun idx => (Xext f xhat)^[k + 1] (b idx).1) (Fin.ext (by dsimp only; omega))
      · have hgt1 : ¬ (j.val + 1 + k ≤ d) := by omega
        simp only [dif_neg hgt1, dif_neg hle, seifertBeta]
        rw [← Function.iterate_succ_apply' (Xext f xhat) (d - (j.val + 1)), Nat.succ_eq_add_one]
        congr 1
        omega
    · have hjeq : j.val = d := by omega
      have hgt : ¬ (j.val + (k + 1) ≤ d) := by omega
      simp only [dif_neg hjd, dif_neg hgt]
      dsimp only [seifertBeta]
      rw [hjeq, Nat.sub_self, Function.iterate_zero_apply]

lemma seifertB_fix {V : Type} {f : V → V} {χ xhat : V} (hfix : f χ = χ)
    (hreach : ∀ v : V, ∃ k : ℕ, f^[k] v = χ) {d : ℕ} (hxhat : depth f χ hreach xhat = d) :
    seifertB hfix hreach hxhat (seifertBeta hfix hreach hxhat) = seifertBeta hfix hreach hxhat := by
  funext j
  apply Subtype.ext
  have h := seifertB_iterate hfix hreach hxhat 1 (seifertBeta hfix hreach hxhat) j
  simp only [Function.iterate_one] at h
  rw [h]
  split_ifs with hle
  · simp only [seifertBeta]
    rw [← Function.iterate_succ_apply' (Xext f xhat) (d - (j.val + 1)), Nat.succ_eq_add_one]
    congr 1
    omega
  · rfl

lemma seifertB_height_le {V : Type} {f : V → V} {χ xhat : V} (hfix : f χ = χ)
    (hreach : ∀ v : V, ∃ k : ℕ, f^[k] v = χ) {d : ℕ} (hxhat : depth f χ hreach xhat = d)
    (b : SeifertVB f χ hreach d) :
    (seifertB hfix hreach hxhat)^[d + 1] b = seifertBeta hfix hreach hxhat := by
  funext j
  apply Subtype.ext
  rw [seifertB_iterate]
  have hgt : ¬ (j.val + (d + 1) ≤ d) := by omega
  simp [hgt]

lemma seifertB_iter_d_iff {V : Type} {f : V → V} {χ xhat : V} (hfix : f χ = χ)
    (hreach : ∀ v : V, ∃ k : ℕ, f^[k] v = χ) {d : ℕ} (hd : 1 ≤ d)
    (hle_d : ∀ x, depth f χ hreach x ≤ d) (hxhat : depth f χ hreach xhat = d)
    (b : SeifertVB f χ hreach d) :
    (seifertB hfix hreach hxhat)^[d] b = seifertBeta hfix hreach hxhat ↔
      (b ⟨d, by omega⟩).1 = none := by
  constructor
  · intro h
    have h0 := congrArg (fun c : SeifertVB f χ hreach d => (c ⟨0, by omega⟩).1) h
    rw [seifertB_iterate] at h0
    simp only [Nat.zero_add, le_refl, ↓reduceDIte, seifertBeta, Nat.sub_zero] at h0
    have hidx : (b ⟨0 + d, by omega⟩).1 = (b ⟨d, by omega⟩).1 :=
      congrArg (fun idx => (b idx).1) (Fin.ext (Nat.zero_add d))
    rw [hidx] at h0
    cases hv : (b ⟨d, by omega⟩).1 with
    | none => rfl
    | some x =>
      rw [hv, Xext_iterate_some] at h0
      have hx_chi : f^[d] x = χ := (iterate_eq_fix_iff_depth_le hfix hreach x d).mpr (hle_d x)
      have hnone : (Xext f xhat)^[d] none = some (f^[d - 1] xhat) := by
        conv_lhs => rw [← Nat.sub_add_cancel hd]
        exact Xext_iterate_none_succ f xhat (d - 1)
      rw [hx_chi, hnone] at h0
      have hfx : f^[d - 1] xhat = χ := (Option.some.inj h0).symm
      have hle : depth f χ hreach xhat ≤ d - 1 := depth_le hreach hfx
      omega
  · intro hnone
    funext j
    apply Subtype.ext
    rw [seifertB_iterate]
    have hjlt := j.isLt
    by_cases hj : j.val = 0
    · have hle : j.val + d ≤ d := by omega
      simp only [dif_pos hle, seifertBeta]
      have hb_eq : (b ⟨j.val + d, by omega⟩).1 = (b ⟨d, by omega⟩).1 :=
        congrArg (fun idx => (b idx).1) (Fin.ext (by dsimp only; omega))
      rw [hb_eq, hnone, hj, Nat.sub_zero]
    · have hgt : ¬ (j.val + d ≤ d) := by omega
      simp [hgt]

/-- Helper to read coordinate `i : Fin (d + 1)` of `b : SeifertVB` as an element of `V` (`0 ↦ χ`). -/
noncomputable def getB {V : Type} {f : V → V} {χ : V}
    (hreach : ∀ v : V, ∃ k : ℕ, f^[k] v = χ) {d : ℕ}
    (b : SeifertVB f χ hreach d) (i : Fin (d + 1)) : V :=
  if hi : i.val = 0 then χ
  else
    match (b ⟨i.val - 1, by omega⟩).1 with
    | some x => x
    | none => χ

lemma some_getB_eq {V : Type} {f : V → V} {χ : V}
    (hreach : ∀ v : V, ∃ k : ℕ, f^[k] v = χ) {d : ℕ}
    (b : SeifertVB f χ hreach d) {i : Fin (d + 1)} (hi : i.val ≠ 0) :
    some (getB hreach b i) = (b ⟨i.val - 1, by omega⟩).1 := by
  simp only [getB, dif_neg hi]
  have hle := (b ⟨i.val - 1, by omega⟩).2
  have hilt := i.isLt
  cases h : (b ⟨i.val - 1, by omega⟩).1 with
  | some x => rfl
  | none =>
    rw [h] at hle
    simp only [depthExt] at hle
    omega

lemma depth_getB_le {V : Type} {f : V → V} {χ : V}
    (hreach : ∀ v : V, ∃ k : ℕ, f^[k] v = χ) {d : ℕ}
    (b : SeifertVB f χ hreach d) (i : Fin (d + 1)) :
    depth f χ hreach (getB hreach b i) ≤ i.val := by
  by_cases hi : i.val = 0
  · simp [getB, hi, (depth_eq_zero_iff hreach χ).mpr rfl]
  · have hs := some_getB_eq hreach b hi
    have hle := (b ⟨i.val - 1, by omega⟩).2
    rw [← hs] at hle
    simp only [depthExt] at hle
    omega

/-- Helper to update coordinate `i : Fin (d + 1)` of `b : SeifertVB` to `some x` (no-op for `i = 0`). -/
noncomputable def setB {V : Type} {f : V → V} {χ : V}
    (hreach : ∀ v : V, ∃ k : ℕ, f^[k] v = χ) {d : ℕ}
    (b : SeifertVB f χ hreach d) (i : Fin (d + 1)) (x : V)
    (hx : depth f χ hreach x ≤ i.val) : SeifertVB f χ hreach d :=
  if hi : i.val = 0 then b
  else fun j =>
    if hj : j.val = i.val - 1 then
      ⟨some x, by simp only [depthExt]; omega⟩
    else b j

lemma getB_setB {V : Type} {f : V → V} {χ : V}
    (hreach : ∀ v : V, ∃ k : ℕ, f^[k] v = χ) {d : ℕ}
    (b : SeifertVB f χ hreach d) (i : Fin (d + 1)) (x : V)
    (hx : depth f χ hreach x ≤ i.val) :
    getB hreach (setB hreach b i x hx) i = x := by
  by_cases hi : i.val = 0
  · simp only [getB, dif_pos hi]
    exact ((depth_eq_zero_iff hreach x).mp (by omega)).symm
  · apply Option.some.inj
    rw [some_getB_eq hreach _ hi]
    simp [setB, hi]

lemma setB_setB_self {V : Type} {f : V → V} {χ : V}
    (hreach : ∀ v : V, ∃ k : ℕ, f^[k] v = χ) {d : ℕ}
    (b : SeifertVB f χ hreach d) (i : Fin (d + 1)) (x y : V)
    (hx : depth f χ hreach x ≤ i.val) (hy : depth f χ hreach y ≤ i.val) :
    setB hreach (setB hreach b i x hx) i y hy = setB hreach b i y hy := by
  by_cases hi : i.val = 0
  · simp [setB, hi]
  · funext j
    simp only [setB, dif_neg hi]
    split_ifs <;> rfl

lemma setB_getB {V : Type} {f : V → V} {χ : V}
    (hreach : ∀ v : V, ∃ k : ℕ, f^[k] v = χ) {d : ℕ}
    (b : SeifertVB f χ hreach d) (i : Fin (d + 1)) :
    setB hreach b i (getB hreach b i) (depth_getB_le hreach b i) = b := by
  by_cases hi : i.val = 0
  · simp [setB, hi]
  · funext j
    simp only [setB, dif_neg hi]
    split_ifs with hj
    · apply Subtype.ext
      change some (getB hreach b i) = (b j).1
      rw [some_getB_eq hreach b hi]
      exact congrArg (fun idx => (b idx).1) (Fin.ext (by dsimp only; omega))
    · rfl

lemma getB_seifertB {V : Type} {f : V → V} {χ xhat : V} (hfix : f χ = χ)
    (hreach : ∀ v : V, ∃ k : ℕ, f^[k] v = χ) {d : ℕ} (hxhat : depth f χ hreach xhat = d)
    (b : SeifertVB f χ hreach d) (i : Fin (d + 1)) :
    getB hreach (seifertB hfix hreach hxhat b) (pathFn d i) = f (getB hreach b i) := by
  have hilt := i.isLt
  by_cases hi0 : i.val = 0
  · simp [pathFn, getB, hi0, hfix]
  · by_cases hi1 : i.val = 1
    · have hpi : (pathFn d i).val = 0 := by simp [pathFn, hi1]
      have hd1 : depth f χ hreach (getB hreach b i) ≤ 1 := by
        have := depth_getB_le hreach b i; omega
      have hfd : depth f χ hreach (f (getB hreach b i)) = 0 := by
        rw [depth_step hfix hreach]; omega
      rw [(depth_eq_zero_iff hreach _).mp hfd]
      simp [getB, hpi]
    · have hpi : (pathFn d i).val ≠ 0 := by simp [pathFn]; omega
      apply Option.some.inj
      rw [some_getB_eq hreach _ hpi]
      have hlt : (pathFn d i).val - 1 < d := by simp [pathFn]; omega
      simp only [seifertB, dif_pos hlt]
      have hidx_eq : (⟨(pathFn d i).val - 1 + 1, by omega⟩ : Fin (d + 1)) = ⟨i.val - 1, by omega⟩ := by
        apply Fin.ext
        simp only [pathFn]
        omega
      have hb_eq : (b ⟨(pathFn d i).val - 1 + 1, by omega⟩).1 = (b ⟨i.val - 1, by omega⟩).1 :=
        congrArg (fun idx => (b idx).1) hidx_eq
      rw [hb_eq, ← some_getB_eq hreach b hi0, Xext]

lemma setB_seifertB {V : Type} {f : V → V} {χ xhat : V} (hfix : f χ = χ)
    (hreach : ∀ v : V, ∃ k : ℕ, f^[k] v = χ) {d : ℕ} (hxhat : depth f χ hreach xhat = d)
    (b : SeifertVB f χ hreach d) (i : Fin (d + 1)) (x : V)
    (hx : depth f χ hreach x ≤ i.val) :
    setB hreach (seifertB hfix hreach hxhat b) (pathFn d i) (f x)
      (by rw [depth_step hfix hreach]; simp [pathFn]; omega) =
      seifertB hfix hreach hxhat (setB hreach b i x hx) := by
  have hilt := i.isLt
  funext j
  have hjlt := j.isLt
  apply Subtype.ext
  by_cases hi0 : i.val = 0
  · have hpi : (pathFn d i).val = 0 := by simp [pathFn, hi0]
    simp [setB, hi0, hpi]
  · by_cases hi1 : i.val = 1
    · have hpi : (pathFn d i).val = 0 := by simp [pathFn, hi1]
      simp only [setB, dif_pos hpi, dif_neg hi0, seifertB]
      by_cases hjd : j.val < d
      · have hne : (⟨j.val + 1, by omega⟩ : Fin (d + 1)).val ≠ i.val - 1 := by simp; omega
        simp only [dif_pos hjd, dif_neg hne]
      · simp only [dif_neg hjd]
    · have hpi : (pathFn d i).val ≠ 0 := by simp [pathFn]; omega
      simp only [setB, dif_neg hpi, dif_neg hi0, seifertB]
      by_cases hjd : j.val < d
      · simp only [dif_pos hjd]
        by_cases hj : j.val = (pathFn d i).val - 1
        · have hj1 : (⟨j.val + 1, by omega⟩ : Fin (d + 1)).val = i.val - 1 := by
            simp [pathFn] at hj ⊢; omega
          simp only [dif_pos hj, dif_pos hj1, Xext]
        · have hj1 : (⟨j.val + 1, by omega⟩ : Fin (d + 1)).val ≠ i.val - 1 := by
            simp [pathFn] at hj ⊢; omega
          simp only [dif_neg hj, dif_neg hj1]
      · have hj : j.val ≠ (pathFn d i).val - 1 := by simp [pathFn]; omega
        simp only [dif_neg hjd, dif_neg hj]

/-- Counting image of `E^[d - 1]` on `{e | E^[d] e = fix_E}` is invariant under isomorphism. -/
lemma card_image_iter_iso {U W : Type} [Fintype U] [Fintype W] [DecidableEq U] [DecidableEq W]
    {f : U → U} {g : W → W} (e : U ≃ W) (he : ∀ u, e (f u) = g (e u))
    (fixU : U) (d : ℕ) :
    ((Finset.univ.filter fun u => f^[d] u = fixU).image (f^[d - 1])).card =
      ((Finset.univ.filter fun w => g^[d] w = e fixU).image (g^[d - 1])).card := by
  classical
  have hmap : ((Finset.univ.filter fun u => f^[d] u = fixU).image (f^[d - 1])).image e =
      (Finset.univ.filter fun w => g^[d] w = e fixU).image (g^[d - 1]) := by
    ext w
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
      exact ⟨e u, by rw [← iso_iterate e he, hu], (iso_iterate e he _ u).symm⟩
    · rintro ⟨w0, hw0, rfl⟩
      refine ⟨f^[d - 1] (e.symm w0), ⟨e.symm w0, e.injective ?_, rfl⟩, ?_⟩
      · rw [iso_iterate e he]; simpa using hw0
      · rw [iso_iterate e he]; simp
  rw [← Finset.card_image_of_injective _ e.injective, hmap]

/-- Part 1 of Seifert's construction: explicit isomorphism `X × Y ≅ A × B`. -/
lemma seifert_iso_XY_AB {V : Type} {f : V → V} {χ xhat : V} (hfix : f χ = χ)
    (hreach : ∀ v : V, ∃ k : ℕ, f^[k] v = χ) {d : ℕ} (hd : 1 ≤ d)
    (hle_d : ∀ x, depth f χ hreach x ≤ d) (hxhat : depth f χ hreach xhat = d) :
    let VA := Option (V × Fin (d + 1))
    let A : VA → VA := fun a => match a with
      | some (x, i) => some (f x, pathFn d i)
      | none => some (χ, ⟨d - 1, by omega⟩)
    let VB := SeifertVB f χ hreach d
    let B : VB → VB := seifertB hfix hreach hxhat
    let VchiB := {b : VB // (b ⟨d - 1, by omega⟩).1 = some χ}
    let VY := (Fin (d + 1) × VB) ⊕ VchiB
    let Y : VY → VY := fun y => match y with
      | Sum.inl (i, b) => Sum.inl (pathFn d i, B b)
      | Sum.inr ⟨b, _⟩ => Sum.inl (⟨d - 1, by omega⟩, B b)
    Iso (Prod.map f Y) (Prod.map A B) := by
  intro VA A VB B VchiB VY Y
  let dLast : Fin (d + 1) := ⟨d, by omega⟩
  have hdLast_ne : dLast.val ≠ 0 := by simp [dLast]; omega
  let toFun : V × VY → VA × VB := fun z => match z with
    | (x, Sum.inl (i, b)) =>
      if h : depth f χ hreach x ≤ i.val then
        (some (getB hreach b i, i), setB hreach b i x h)
      else
        (some (x, i), b)
    | (x, Sum.inr ⟨b, _⟩) => (none, setB hreach b dLast x (hle_d x))
  let invFun : VA × VB → V × VY := fun w => match w with
    | (some (y, i), c) =>
      if h : depth f χ hreach y ≤ i.val then
        (getB hreach c i, Sum.inl (i, setB hreach c i y h))
      else
        (y, Sum.inl (i, c))
    | (none, c) =>
      (getB hreach c dLast,
        Sum.inr ⟨setB hreach c dLast χ (by rw [(depth_eq_zero_iff hreach χ).mpr rfl]; omega),
          by simp [setB, hdLast_ne, dLast]⟩)
  have hphi_left : Function.LeftInverse invFun toFun := by
    rintro ⟨x, y⟩
    rcases y with ⟨i, b⟩ | ⟨b, hb⟩
    · simp only [toFun]
      by_cases hx : depth f χ hreach x ≤ i.val
      · simp only [dif_pos hx, invFun, dif_pos (depth_getB_le hreach b i)]
        rw [getB_setB, setB_setB_self, setB_getB]
      · simp [dif_neg hx, invFun]
    · simp only [toFun, invFun]
      apply Prod.ext
      · exact getB_setB hreach b dLast x (hle_d x)
      · apply congrArg Sum.inr
        apply Subtype.ext
        change setB hreach (setB hreach b dLast x (hle_d x)) dLast χ (hle_d χ) = b
        rw [setB_setB_self]
        funext j
        simp only [setB, dif_neg hdLast_ne]
        split_ifs with hj
        · apply Subtype.ext
          change some χ = (b j).1
          have hidx : j = ⟨d - 1, by omega⟩ := Fin.ext (by simpa [dLast] using hj)
          rw [hidx, hb]
        · rfl
  have hphi_right : Function.RightInverse invFun toFun := by
    rintro ⟨a, c⟩
    rcases a with _ | ⟨y, i⟩
    · simp only [invFun, toFun]
      rw [setB_setB_self, setB_getB]
    · simp only [invFun]
      by_cases hy : depth f χ hreach y ≤ i.val
      · simp only [dif_pos hy, toFun, dif_pos (depth_getB_le hreach c i)]
        rw [getB_setB, setB_setB_self, setB_getB]
      · simp [dif_neg hy, toFun]
  have hphi_hom : ∀ z, toFun (Prod.map f Y z) = Prod.map A B (toFun z) := by
    rintro ⟨x, y⟩
    rcases y with ⟨i, b⟩ | ⟨b, hb⟩
    · simp only [Prod.map_apply, Y, toFun]
      by_cases hx : depth f χ hreach x ≤ i.val
      · have hfx : depth f χ hreach (f x) ≤ (pathFn d i).val := by
          rw [depth_step hfix hreach]; simp [pathFn]; omega
        simp only [dif_pos hx, dif_pos hfx, Prod.map_apply, A]
        exact Prod.ext (congrArg some (Prod.ext (getB_seifertB hfix hreach hxhat b i) rfl))
          (setB_seifertB hfix hreach hxhat b i x hx)
      · by_cases hfx : depth f χ hreach (f x) ≤ (pathFn d i).val
        · have hi0 : i.val = 0 := by
            rw [depth_step hfix hreach] at hfx; simp [pathFn] at hfx; omega
          have hfx0 : f x = χ := by
            rw [← depth_eq_zero_iff hreach]
            simp [pathFn, hi0] at hfx; omega
          have hpi0 : (pathFn d i).val = 0 := by simp [pathFn, hi0]
          simp only [dif_neg hx, dif_pos hfx, Prod.map_apply, A]
          exact Prod.ext (congrArg some (Prod.ext (by simp [getB, hpi0, hfx0]) rfl))
            (by simp [setB, hpi0])
        · simp [dif_neg hx, dif_neg hfx, Prod.map_apply, A]
    · simp only [Prod.map_apply, Y, toFun]
      have hfx : depth f χ hreach (f x) ≤ (⟨d - 1, by omega⟩ : Fin (d + 1)).val := by
        rw [depth_step hfix hreach]; have := hle_d x; dsimp only; omega
      simp only [dif_pos hfx, A]
      have hpath : pathFn d dLast = ⟨d - 1, by omega⟩ := Fin.ext (by simp [pathFn, dLast])
      apply Prod.ext
      · apply congrArg some
        apply Prod.ext
        · have hget_path : getB hreach (B b) ⟨d - 1, by omega⟩ = getB hreach (B b) (pathFn d dLast) :=
            congrArg (getB hreach (B b)) hpath.symm
          rw [hget_path, getB_seifertB hfix hreach hxhat b dLast]
          have hget : getB hreach b dLast = χ := by
            apply Option.some.inj
            rw [some_getB_eq hreach b hdLast_ne]
            exact hb
          rw [hget, hfix]
        · rfl
      · dsimp only [B]
        have hset := setB_seifertB hfix hreach hxhat b dLast x (hle_d x)
        rw [← hset]
        funext j
        apply Subtype.ext
        by_cases hd1 : d - 1 = 0
        · have hpi : (pathFn d dLast).val = 0 := by simp [pathFn, dLast, hd1]
          simp [setB, hd1, hpi]
        · have hpi : (pathFn d dLast).val ≠ 0 := by simp [pathFn, dLast, hd1]
          simp only [setB, dif_neg hd1, dif_neg hpi]
          have hval : (pathFn d dLast).val - 1 = d - 1 - 1 := by simp [pathFn, dLast]
          by_cases hj : j.val = d - 1 - 1
          · simp [hj, hval]
          · simp [hj, hval]
  exact ⟨⟨toFun, invFun, hphi_left, hphi_right⟩, hphi_hom⟩

/-- Part 2 of Seifert's construction: `X ∤ B`. -/
lemma seifert_not_dvd_B {V : Type} [Fintype V] [Nonempty V] {f : V → V} {χ xhat : V}
    (hfix : f χ = χ) (hreach : ∀ v : V, ∃ k : ℕ, f^[k] v = χ) {d : ℕ} (hd : 1 ≤ d)
    (hle_d : ∀ x, depth f χ hreach x ≤ d) (hxhat : depth f χ hreach xhat = d) :
    ¬ Divides f (seifertB hfix hreach hxhat) := by
  classical
  rintro ⟨n, g, e, he⟩
  let VB := SeifertVB f χ hreach d
  let B : VB → VB := seifertB hfix hreach hxhat
  let β : VB := seifertBeta hfix hreach hxhat
  let dLast : Fin (d + 1) := ⟨d, by omega⟩
  have hdLast_ne : dLast.val ≠ 0 := by simp [dLast]; omega
  have hB_fix : B β = β := seifertB_fix hfix hreach hxhat
  have hB_all : ∀ b : VB, B^[d + 1] b = β := seifertB_height_le hfix hreach hxhat
  set xz0 := e.symm β
  have hxz0_fix : Prod.map f g xz0 = xz0 :=
    e.injective (by rw [he, Equiv.apply_symm_apply]; exact hB_fix)
  have hfx0 : f xz0.1 = xz0.1 := (Prod.ext_iff.mp hxz0_fix).1
  have hζ_fix : g xz0.2 = xz0.2 := (Prod.ext_iff.mp hxz0_fix).2
  have hx0_eq : xz0.1 = χ := by
    have h1 : f^[d] xz0.1 = χ := (iterate_eq_fix_iff_depth_le hfix hreach xz0.1 d).mpr (hle_d xz0.1)
    have h2 : ∀ k, f^[k] xz0.1 = xz0.1 := fun k => by
      induction k with
      | zero => rfl
      | succ k ih => rw [Function.iterate_succ_apply, hfx0, ih]
    rw [← h2 d, h1]
  set ζ := xz0.2
  have he_fix : e (χ, ζ) = β := by
    have : (χ, ζ) = xz0 := Prod.ext hx0_eq.symm rfl
    rw [this, Equiv.apply_symm_apply]
  have hg_all : ∀ z : Fin n, g^[d + 1] z = ζ := by
    intro z
    have h1 : (Prod.map f g)^[d + 1] (χ, z) = (χ, ζ) := by
      apply e.injective
      rw [iso_iterate e he, hB_all, he_fix]
    rw [prod_map_iterate] at h1
    exact (Prod.ext_iff.mp h1).2
  let S_X := Finset.univ.image (f^[d - 1])
  let S_B := (Finset.univ.filter fun b : VB => B^[d] b = β).image (B^[d - 1])
  have hB_dm1 : ∀ b : VB, B^[d] b = β → ∀ j : Fin (d + 1),
      (B^[d - 1] b j).1 =
        if j.val = 0 then (Xext f xhat)^[d - 1] (b ⟨d - 1, by omega⟩).1 else (β j).1 := by
    intro b hb j
    have hjlt := j.isLt
    have hnone : (b ⟨d, by omega⟩).1 = none := (seifertB_iter_d_iff hfix hreach hd hle_d hxhat b).mp hb
    rw [seifertB_iterate]
    by_cases hj0 : j.val = 0
    · have hle : j.val + (d - 1) ≤ d := by omega
      simp only [dif_pos hle, if_pos hj0]
      exact congrArg (fun idx => (Xext f xhat)^[d - 1] (b idx).1) (Fin.ext (by simp [hj0]))
    · by_cases hj1 : j.val = 1
      · have hle : j.val + (d - 1) ≤ d := by omega
        simp only [dif_pos hle, if_neg hj0, β, seifertBeta]
        have hb_eq : (b ⟨j.val + (d - 1), by omega⟩).1 = (b ⟨d, by omega⟩).1 :=
          congrArg (fun idx => (b idx).1) (Fin.ext (by simp [hj1]; omega))
        rw [hb_eq, hnone]
        congr 1; omega
      · have hgt : ¬ (j.val + (d - 1) ≤ d) := by omega
        simp only [dif_neg hgt, if_neg hj0]
        rfl
  have hnB_eq : S_B.card = S_X.card := by
    let toV : VB → V := fun c => match (c ⟨0, by omega⟩).1 with | some x => x | none => χ
    have h_im : S_B.image toV = S_X := by
      ext y
      simp only [S_B, S_X, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨_, ⟨b, hb, rfl⟩, rfl⟩
        have h0 := hB_dm1 b hb ⟨0, by omega⟩
        simp only [↓reduceIte] at h0
        have hs := some_getB_eq hreach b hdLast_ne
        have hidx : (⟨dLast.val - 1, by omega⟩ : Fin (d + 1)) = ⟨d - 1, by omega⟩ := Fin.ext rfl
        rw [hidx] at hs
        refine ⟨getB hreach b dLast, ?_⟩
        simp only [toV, h0, ← hs, Xext_iterate_some]
      · rintro ⟨x, rfl⟩
        let b0 : VB := fun j =>
          if hj : j.val = d then ⟨none, by simp [depthExt]; omega⟩
          else if hjd : j.val = d - 1 then ⟨some x, by simp [depthExt]; have := hle_d x; omega⟩
          else ⟨some χ, by simp [depthExt, (depth_eq_zero_iff hreach χ).mpr rfl]⟩
        have hb0 : B^[d] b0 = β :=
          (seifertB_iter_d_iff hfix hreach hd hle_d hxhat b0).mpr (by simp [b0])
        refine ⟨B^[d - 1] b0, ⟨b0, hb0, rfl⟩, ?_⟩
        have h0 := hB_dm1 b0 hb0 ⟨0, by omega⟩
        simp only [↓reduceIte] at h0
        have hbd : (b0 ⟨d - 1, by omega⟩).1 = some x := by
          have hne : d - 1 ≠ d := by omega
          simp [b0, hne]
        change (match (B^[d - 1] b0 ⟨0, by omega⟩).1 with | some z => z | none => χ) = f^[d - 1] x
        rw [h0, hbd, Xext_iterate_some]
    have h_inj : Set.InjOn toV (S_B : Set VB) := by
      intro c1 hc1 c2 hc2 heq
      simp only [S_B, Finset.mem_coe, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hc1 hc2
      rcases hc1 with ⟨b1, hb1, rfl⟩
      rcases hc2 with ⟨b2, hb2, rfl⟩
      funext j
      apply Subtype.ext
      rw [hB_dm1 b1 hb1 j, hB_dm1 b2 hb2 j]
      split_ifs with hj0
      · have h01 := hB_dm1 b1 hb1 ⟨0, by omega⟩
        have h02 := hB_dm1 b2 hb2 ⟨0, by omega⟩
        simp only [↓reduceIte] at h01 h02
        have hs1 := some_getB_eq hreach b1 hdLast_ne
        have hs2 := some_getB_eq hreach b2 hdLast_ne
        have hidx : (⟨dLast.val - 1, by omega⟩ : Fin (d + 1)) = ⟨d - 1, by omega⟩ := Fin.ext rfl
        rw [hidx] at hs1 hs2
        rw [← hs1, Xext_iterate_some] at h01 ⊢
        rw [← hs2, Xext_iterate_some] at h02 ⊢
        simp only [toV, h01, h02] at heq
        rw [heq]
      · rfl
    rw [← h_im, Finset.card_image_of_injOn h_inj]
  let S_Z := (Finset.univ.filter fun z : Fin n => g^[d] z = ζ).image (g^[d - 1])
  let S_XZ := (Finset.univ.filter fun p : V × Fin n => (Prod.map f g)^[d] p = (χ, ζ)).image
    ((Prod.map f g)^[d - 1])
  have hXZ_prod : S_XZ = S_X ×ˢ S_Z := by
    ext ⟨x, z⟩
    simp only [S_XZ, S_X, S_Z, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_product, prod_map_iterate, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨x0, z0⟩, ⟨_, hz0⟩, rfl, rfl⟩
      exact ⟨⟨x0, rfl⟩, ⟨z0, hz0, rfl⟩⟩
    · rintro ⟨⟨x0, rfl⟩, ⟨z0, hz0, rfl⟩⟩
      exact ⟨(x0, z0), ⟨(iterate_eq_fix_iff_depth_le hfix hreach x0 d).mpr (hle_d x0), hz0⟩, rfl, rfl⟩
  have hnXZ_eq : S_XZ.card = S_B.card := by
    have h := card_image_iter_iso e he (χ, ζ) d
    rw [he_fix] at h
    exact h
  have hnZ_eq1 : S_Z.card = 1 := by
    have h1 : S_X.card * S_Z.card = S_X.card := by
      rw [← Finset.card_product, ← hXZ_prod, hnXZ_eq, hnB_eq]
    have hX_pos : 0 < S_X.card := Finset.card_pos.mpr (Finset.Nonempty.image Finset.univ_nonempty _)
    exact Nat.eq_of_mul_eq_mul_left hX_pos (by simpa using h1)
  have hζ_iter : ∀ k, g^[k] ζ = ζ := fun k => by
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply, hζ_fix, ih]
  have hζ_mem : ζ ∈ S_Z := by
    simp only [S_Z, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨ζ, hζ_iter d, hζ_iter (d - 1)⟩
  have hZ_dm1 : ∀ z : Fin n, g^[d] z = ζ → g^[d - 1] z = ζ := by
    intro z hz
    have hmem : g^[d - 1] z ∈ S_Z := by
      simp only [S_Z, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨z, hz, rfl⟩
    exact Finset.card_le_one.mp (le_of_eq hnZ_eq1) (g^[d - 1] z) hmem ζ hζ_mem
  have hg_d : ∀ z : Fin n, g^[d] z = ζ := by
    intro z
    have h1 : g^[d] (g z) = ζ := by
      rw [← Function.iterate_succ_apply]; exact hg_all z
    have h2 := hZ_dm1 (g z) h1
    rwa [← Function.iterate_succ_apply, Nat.succ_eq_add_one, Nat.sub_add_cancel hd] at h2
  let b_chi : VB := fun _ => ⟨some χ, by simp [depthExt, (depth_eq_zero_iff hreach χ).mpr rfl]⟩
  have hb_chi_eq : B^[d] b_chi = β := by
    set p := e.symm b_chi
    have hp : (Prod.map f g)^[d] p = (χ, ζ) := by
      rw [prod_map_iterate]
      exact Prod.ext ((iterate_eq_fix_iff_depth_le hfix hreach p.1 d).mpr (hle_d p.1)) (hg_d p.2)
    have h1 := congrArg e hp
    rw [iso_iterate e he, Equiv.apply_symm_apply, he_fix] at h1
    exact h1
  have hnone := (seifertB_iter_d_iff hfix hreach hd hle_d hxhat b_chi).mp hb_chi_eq
  simp [b_chi] at hnone

/-- Lemma 4 (Seifert 1971 / Richard 2025): No functional digraph in `F_1` is prime. -/
lemma not_isPrime_of_F1 {V : Type} [Fintype V] [Nonempty V] {f : V → V}
    {χ : V} (hfix : f χ = χ) (hreach : ∀ v : V, ∃ k : ℕ, f^[k] v = χ) :
    ¬ IsPrime f := by
  classical
  intro hf
  have hcard_ge2 : 2 ≤ Fintype.card V := card_ge_two_of_isPrime hf
  let d := Finset.univ.sup (depth f χ hreach)
  have hle_d : ∀ x : V, depth f χ hreach x ≤ d := fun x => Finset.le_sup (Finset.mem_univ x)
  obtain ⟨xhat, _, hxhat_eq⟩ :=
    Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty (depth f χ hreach)
  have hxhat : depth f χ hreach xhat = d := hxhat_eq.symm
  have hd : 1 ≤ d := by
    obtain ⟨v, hv⟩ : ∃ v : V, v ≠ χ := by
      by_contra hall
      push Not at hall
      have hle1 : Fintype.card V ≤ 1 := Fintype.card_le_one_iff.mpr fun a b => by rw [hall a, hall b]
      omega
    have hpos : 0 < depth f χ hreach v := by
      have := mt (depth_eq_zero_iff hreach v).mp hv; omega
    have := hle_d v
    omega
  let VA := Option (V × Fin (d + 1))
  let A : VA → VA := fun a => match a with
    | some (x, i) => some (f x, pathFn d i)
    | none => some (χ, ⟨d - 1, by omega⟩)
  have hprod := seifert_iso_XY_AB hfix hreach hd hle_d hxhat
  rcases isPrime_prod_dvd hf A (seifertB hfix hreach hxhat) (divides_of_fintype hprod) with
    ⟨n, g, hfg⟩ | hdivB
  · have hcard : Fintype.card V * n = Fintype.card V * (d + 1) + 1 := by
      have h1 := iso_card_eq hfg
      simpa [VA, Fintype.card_option, Fintype.card_prod] using h1
    have hdvd1 : Fintype.card V ∣ 1 := by
      have hsub : Fintype.card V ∣ Fintype.card V * n - Fintype.card V * (d + 1) :=
        Nat.dvd_sub (dvd_mul_right _ _) (dvd_mul_right _ _)
      have h1 : Fintype.card V * n - Fintype.card V * (d + 1) = 1 := by omega
      rwa [h1] at hsub
    have hle1 : Fintype.card V ≤ 1 := Nat.le_of_dvd Nat.one_pos hdvd1
    omega
  · exact seifert_not_dvd_B hfix hreach hd hle_d hxhat hdivB

end SeifertF1

theorem main_proof : ∀ (k : ℕ) (x : Fin k → Fin k), 0 < k → ¬ IsPrime x := by
  intro k x hk hx
  have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  have hconn : IsConnected x := isConnected_of_isPrime hx
  obtain ⟨⟨x0, hx0⟩⟩ := nonempty_per x
  have hp1 : period x x0 = 1 := period_eq_one_of_isPrime_connected hx hconn hx0
  have hfix : x x0 = x0 := by
    have h := iterate_period hx0
    rwa [hp1, Function.iterate_one] at h
  have hreach : ∀ v : Fin k, ∃ m : ℕ, x^[m] v = x0 :=
    fun v => periodic_reaches_of_compRel hx0 (hconn v x0)
  exact not_isPrime_of_F1 hfix hreach hx

end OMA.P_arxiv_2509_19940

theorem OMA.solution : type_of% @OMA.S_arxiv_2509_19940.main :=
  OMA.P_arxiv_2509_19940.main_proof
