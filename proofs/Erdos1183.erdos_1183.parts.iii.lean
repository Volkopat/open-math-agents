import FormalConjectures.ErdosProblems.«1183»
import Mathlib.Combinatorics.SetFamily.Shatter
import Mathlib.Combinatorics.HalesJewett
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Nat.Choose.Bounds

/-!
Erdős Problem 1183, part iii.
The upper bound uses the shattering and random-colouring argument of Przemyslaw Chojecki.
For the lower bound we use the block-cube gluing method of Deep Bhattacharjee,
Priyabrata Mandal and Ushashi Bhattacharya, with finite local rearrangements and
Mathlib's multidimensional Hales–Jewett theorem.
-/

open Finset
open scoped Classical
namespace OMA1183

abbrev Col (n : ℕ) := Finset (Fin n) → Bool

lemma leF {n m : ℕ} (h : ∀ c : Col n, ∃ U : Finset (Finset (Fin n)),
    m ≤ U.card ∧ Erdos1183.IsMonochromatic c U ∧ SupClosed (U : Set (Finset (Fin n)))) :
    m ≤ Erdos1183.F n := by
  unfold Erdos1183.F
  refine le_csSup ⟨Fintype.card (Finset (Fin n)), ?_⟩ (Set.mem_ofPred_eq.mpr h)
  intro k hk
  obtain ⟨U, hU, _⟩ := hk (fun _ => true)
  exact hU.trans (card_le_univ U)

lemma Fle {n m : ℕ} (c : Col n) (h : ∀ U : Finset (Finset (Fin n)),
    Erdos1183.IsMonochromatic c U → SupClosed (U : Set (Finset (Fin n))) → U.card ≤ m) :
    Erdos1183.F n ≤ m := by
  unfold Erdos1183.F
  apply csSup_le
  · exact ⟨0, fun c => ⟨∅, by simp, ⟨true, by simp⟩, by simp⟩⟩
  · intro k hk
    obtain ⟨U, hU, hM, hS⟩ := hk c
    exact hU.trans (h U hM hS)

abbrev Tuple (n d : ℕ) := Fin d → Finset (Fin n)

def unions {n d : ℕ} (a : Tuple n d) : Finset (Finset (Fin n)) :=
  (univ.erase (∅ : Finset (Fin d))).image (fun s => s.sup a)

def bad {n d : ℕ} (a : Tuple n d) (b : Bool) : Finset (Col n) :=
  univ.filter fun c => (unions a).card + 1 = 2 ^ d ∧ ∀ s ∈ unions a, c s = b

lemma bad_bound {n d : ℕ} (a : Tuple n d) (b : Bool) :
    (bad a b).card * 2 ^ (2 ^ d) ≤ 2 * 2 ^ (2 ^ n) := by
  by_cases h : (unions a).card + 1 = 2 ^ d
  swap
  · simp [bad, h]
  let S := unions a
  have hs : S.card ≤ 2 ^ n := by simpa [Fintype.card_finset] using card_le_univ S
  have hinj : (bad a b).card ≤ (univ : Finset (↥(Sᶜ) → Bool)).card := by
    refine card_le_card_of_injOn (fun c (s : ↥(Sᶜ)) => c s) (fun _ _ => mem_univ _) ?_
    intro c hc e he eq
    have hc' := (mem_filter.mp (mem_coe.mp hc)).2.2
    have he' := (mem_filter.mp (mem_coe.mp he)).2.2
    funext s
    by_cases hx : s ∈ S
    · exact (hc' s hx).trans (he' s hx).symm
    · exact congrFun eq ⟨s, mem_compl.mpr hx⟩
  simp only [card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe, card_compl,
    Fintype.card_finset, Fintype.card_fin] at hinj
  calc
    _ ≤ 2 ^ (2 ^ n - S.card) * 2 ^ (2 ^ d) := Nat.mul_le_mul_right _ hinj
    _ = 2 * 2 ^ (2 ^ n) := by
      change S.card + 1 = 2 ^ d at h
      rw [← h, pow_succ, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hs, mul_comm]

lemma avoiding {n d : ℕ} (hd : n * d + 2 < 2 ^ d) :
    ∃ c : Col n, ∀ a : Tuple n d, ∀ b, c ∉ bad a b := by
  by_contra! hf
  have hcover : (univ : Finset (Col n)) ⊆
      (univ : Finset (Tuple n d × Bool)).biUnion (fun p => bad p.1 p.2) := by
    intro c _
    obtain ⟨a,b,h⟩ := hf c
    exact mem_biUnion.mpr ⟨(a,b), mem_univ _, h⟩
  have hc := (card_le_card hcover).trans card_biUnion_le
  simp only [card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_finset,
    Fintype.card_fin] at hc
  have hlt := Nat.pow_lt_pow_right (a := 2) (by norm_num) hd
  refine (lt_irrefl (2 ^ (2 ^ n) * 2 ^ (2 ^ d))) ?_
  calc
    _ ≤ (∑ p : Tuple n d × Bool, (bad p.1 p.2).card) * 2 ^ (2 ^ d) :=
      Nat.mul_le_mul_right _ hc
    _ ≤ ∑ _p : Tuple n d × Bool, 2 * 2 ^ (2 ^ n) := by
      rw [sum_mul]
      exact sum_le_sum fun p _ => bad_bound p.1 p.2
    _ = 2 ^ (n * d + 2) * 2 ^ (2 ^ n) := by
      simp only [sum_const, card_univ, Fintype.card_prod, Fintype.card_fun, Fintype.card_finset,
        Fintype.card_fin, Fintype.card_bool, smul_eq_mul, pow_add, pow_mul]
      ring
    _ < 2 ^ (2 ^ n) * 2 ^ (2 ^ d) := by
      rw [mul_comm (2 ^ (2 ^ n))]
      exact Nat.mul_lt_mul_of_pos_right hlt (by positivity)

lemma choose_bound {n d : ℕ} (hd : n * d + 2 < 2 ^ d) :
    Erdos1183.F n ≤ ∑ i ∈ range d, n.choose i := by
  obtain ⟨c, hc⟩ := avoiding hd
  apply Fle c
  rintro U ⟨b,hb⟩ hu
  have ht : ∀ s ∈ U.shatterer, s.card < d := by
    intro s hs
    by_contra! h
    obtain ⟨v, hv, hvc⟩ := exists_subset_card_eq h
    let e := (v.equivFinOfCardEq hvc).symm
    have he := (mem_shatterer.mp hs).mono_right hv
    choose a ha htrace using (fun i : Fin d => he.exists_inter_eq_singleton (e i).2)
    have hmem (I : Finset (Fin d)) (i : Fin d) : (e i : Fin n) ∈ I.sup a ↔ i ∈ I := by
      rw [Finset.mem_sup]
      constructor
      · rintro ⟨j,hj,hij⟩
        have hh : (e i : Fin n) ∈ v ∩ a j := mem_inter.mpr ⟨(e i).2, hij⟩
        rw [htrace, mem_singleton] at hh
        rwa [e.injective (Subtype.ext hh)]
      · intro hi
        refine ⟨i,hi, (mem_inter.mp (show (e i : Fin n) ∈ v ∩ a i from ?_)).2⟩
        rw [htrace]
        exact mem_singleton_self _
    have hj : Function.Injective (fun I : Finset (Fin d) => I.sup a) := by
      intro I J hIJ
      change I.sup a = J.sup a at hIJ
      ext i
      rw [← hmem, ← hmem, hIJ]
    apply hc a b
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_, ?_⟩
    · have hpos : 0 < (2 : ℕ)^d := by positivity
      simp [unions, card_image_of_injective _ hj, Fintype.card_finset, Nat.sub_add_cancel hpos]
    · intro x hx
      obtain ⟨I, hi, rfl⟩ := mem_image.mp hx
      exact hb _ (hu.finsetSup_mem (nonempty_iff_ne_empty.mpr (mem_erase.mp hi).1) fun i _ => ha i)
  have hsub : U.shatterer ⊆ (range d).biUnion (fun i => (univ : Finset (Fin n)).powersetCard i) := by
    intro s hs
    exact mem_biUnion.mpr ⟨s.card, mem_range.mpr (ht s hs), mem_powersetCard.mpr ⟨subset_univ _, rfl⟩⟩
  exact (card_le_card_shatterer U).trans ((card_le_card hsub).trans (by
    simpa only [card_powersetCard, card_univ, Fintype.card_fin] using
      (card_biUnion_le (s := range d) (t := fun i => (univ : Finset (Fin n)).powersetCard i))))

lemma averaging {X E J : Type*} [Fintype X] [Fintype E] [Fintype J] [Nonempty E]
    (P : X → E → Prop) (act : X → J → E → E)
    (hinj : ∀ x j, Function.Injective (act x j))
    (hcover : ∀ x e, ∃ j, P x (act x j e)) :
    ∃ e, Fintype.card X ≤ Fintype.card J * (univ.filter fun x => P x e).card := by
  let T (x : X) (j : J) := univ.filter fun e => P x (act x j e)
  let G (x : X) := univ.filter (P x)
  have hrow (x : X) : Fintype.card E ≤ Fintype.card J * (G x).card := by
    have hsub : (univ : Finset E) ⊆ univ.biUnion (T x) := by
      intro e _
      obtain ⟨j,hj⟩ := hcover x e
      exact mem_biUnion.mpr ⟨j,mem_univ _,mem_filter.mpr ⟨mem_univ _,hj⟩⟩
    calc
      _ ≤ (univ.biUnion (T x)).card := by simpa using card_le_card hsub
      _ ≤ ∑ j, (T x j).card := card_biUnion_le
      _ ≤ ∑ _j : J, (G x).card := by
        apply sum_le_sum
        intro j _
        refine card_le_card_of_injOn (act x j) ?_ (hinj x j).injOn
        intro e he
        exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp he).2⟩
      _ = _ := by simp [smul_eq_mul]
  let N (e : E) := (univ.filter fun x => P x e).card
  have hsum : ∑ x, (G x).card = ∑ e, N e := by
    simp only [G,N,card_filter]
    exact sum_comm
  obtain ⟨e,_,he⟩ := exists_max_image (univ : Finset E) N univ_nonempty
  refine ⟨e, Nat.le_of_mul_le_mul_right ?_ (Fintype.card_pos (α := E))⟩
  calc
    Fintype.card X * Fintype.card E = ∑ _x : X, Fintype.card E := by simp [smul_eq_mul]
    _ ≤ ∑ x, Fintype.card J * (G x).card := sum_le_sum fun x _ => hrow x
    _ = Fintype.card J * ∑ e, N e := by simp only [← mul_sum, hsum]
    _ ≤ Fintype.card J * ∑ _e' : E, N e := Nat.mul_le_mul_left _ (sum_le_sum he)
    _ = (Fintype.card J * N e) * Fintype.card E := by simp [smul_eq_mul]; ring

abbrev Ix (t m : ℕ) := Fin t × Fin m
abbrev Grid (t m M : ℕ) := Option (Ix t m) × Fin M
abbrev Pick (t m : ℕ) := Fin t → Fin m
abbrev Sizes (t m M : ℕ) := Ix t m → Fin M
abbrev Local (t M : ℕ) := Option (Fin t) × Fin M
abbrev Word (t M : ℕ) := Fin M → Fin t ⊕ Bool

def fiber {α β : Type*} [Fintype α] [DecidableEq β] (f : α → β) (y : β) : Finset α :=
  univ.filter fun a => f a = y

@[simp] lemma mem_fiber {α β : Type*} [Fintype α] [DecidableEq β] (f : α → β) (y : β) (a : α) :
    a ∈ fiber f y ↔ f a = y := by simp [fiber]

lemma fiber_match {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (f g : α → β) (z : β) (h : ∀ y ≠ z, (fiber f y).card = (fiber g y).card) :
    ∃ τ : Equiv.Perm α, ∀ a, f a = g (τ a) := by
  have hs (l : α → β) : ∑ y, (fiber l y).card = Fintype.card α := by
    unfold fiber
    rw [← card_univ, card_eq_sum_card_fiberwise (f := l) (t := univ) (fun _ _ => mem_univ _)]
  have hc : ∀ y, (fiber f y).card = (fiber g y).card := by
    intro y
    by_cases hy : y = z
    · subst y
      have hf := hs f
      have hg := hs g
      rw [← add_sum_erase _ _ (mem_univ z)] at hf hg
      rw [sum_congr rfl fun y hy => h y (ne_of_mem_erase hy)] at hf
      omega
    · exact h y hy
  let e : ∀ y, {a // f a = y} ≃ {a // g a = y} := fun y =>
    Fintype.equivOfCardEq (by simpa [Fintype.card_subtype, fiber] using hc y)
  refine ⟨(Equiv.sigmaFiberEquiv f).symm.trans
    ((Equiv.sigmaCongrRight e).trans (Equiv.sigmaFiberEquiv g)), fun a => ?_⟩
  exact ((e (f a)) ((Equiv.sigmaFiberEquiv f).symm a).2).2.symm

section
variable {t m M n : ℕ}

def src (w : Word t M) (p : Local t M) : Fin t ⊕ Bool := if p.1 = none then w p.2 else .inr false

noncomputable def dst (a : Fin t → Fin M) (k : ℕ) (p : Local t M) : Fin t ⊕ Bool :=
  match p.1 with
  | none => .inr (decide (p.2.val < k))
  | some i => if p.2 ≤ a i then .inl i else .inr false

def colEmb (i : Option (Fin t)) : Fin M ↪ Local t M :=
  ⟨fun q => (i,q), fun _ _ h => congrArg Prod.snd h⟩

@[simp] lemma mem_col (S : Finset (Fin M)) (i j : Option (Fin t)) (q : Fin M) :
    (j,q) ∈ S.map (colEmb i) ↔ j = i ∧ q ∈ S := by
  rw [mem_map]
  change (∃ r ∈ S, (i,r) = (j,q)) ↔ _
  simp [eq_comm (a := i), and_comm]

def pref (k : ℕ) : Finset (Fin M) := univ.filter fun q => q.val < k

lemma pref_card {k : ℕ} (h : k ≤ M) : (pref (M := M) k).card = k := by
  have he : pref (M := M) k = (univ : Finset (Fin k)).map (Fin.castLEEmb h) := by
    ext q
    simp only [pref, mem_filter, mem_univ, true_and, mem_map, Fin.castLEEmb_apply]
    refine ⟨fun hq => ⟨⟨q.val,hq⟩, Fin.ext rfl⟩, fun ⟨a,ha⟩ => ?_⟩
    have heq := congrArg Fin.val ha
    exact heq ▸ a.isLt
  simp [he]

lemma local_match (w : Word t M) (hp : ∀ i, ∃ q, w q = .inl i) :
    ∃ (τ : Equiv.Perm (Local t M)) (a : Fin t → Fin M) (k : Fin (M+1)),
      ∀ p, dst a k.val p = src w (τ p) := by
  have hu (y : Fin t ⊕ Bool) : (fiber w y).card ≤ M := by simpa using card_le_univ (fiber w y)
  have hl (i : Fin t) : 0 < (fiber w (.inl i)).card := by
    obtain ⟨q,hq⟩ := hp i
    exact card_pos.mpr ⟨q, by simp [hq]⟩
  let a (i : Fin t) : Fin M := ⟨(fiber w (.inl i)).card - 1, by have := hu (.inl i); have := hl i; omega⟩
  let k : Fin (M+1) := ⟨(fiber w (.inr true)).card, by have := hu (.inr true); omega⟩
  have ha (i : Fin t) : (a i).val.succ = (fiber w (.inl i)).card := Nat.sub_add_cancel (hl i)
  have h (y : Fin t ⊕ Bool) (hy : y ≠ .inr false) :
      (fiber (dst a k.val) y).card = (fiber (src w) y).card := by
    have hs : fiber (src w) y = (fiber w y).map (colEmb none) := by
      ext ⟨j,q⟩
      simp only [mem_fiber, mem_col]
      cases j <;> simp [src, Ne.symm hy]
    rw [hs, card_map]
    cases y with
    | inl i =>
      have hd : fiber (dst a k.val) (.inl i) = (pref ((a i).val.succ)).map (colEmb (some i)) := by
        ext ⟨j,q⟩
        simp only [mem_fiber, mem_col]
        cases j with
        | none => simp [dst]
        | some j =>
          by_cases hji : j = i
          · subst j
            by_cases hh : q ≤ a i <;> simp [dst, pref, hh]
          · by_cases hq : q ≤ a j <;> simp [dst,hq,hji]
      rw [hd, card_map, pref_card (Nat.succ_le_of_lt (a i).isLt), ha]
    | inr b =>
      cases b
      · exact (hy rfl).elim
      have hd : fiber (dst a k.val) (.inr true) = (pref k.val).map (colEmb none) := by
        ext ⟨j,q⟩
        simp only [mem_fiber, mem_col]
        cases j with
        | none => simp [dst,pref]
        | some j => by_cases hq : q ≤ a j <;> simp [dst,hq]
      rw [hd, card_map, pref_card (hu (.inr true))]
  obtain ⟨τ,hτ⟩ := fiber_match _ _ (Sum.inr false) h
  exact ⟨τ,a,k,hτ⟩

def picks (x : Pick t m) : Finset (Ix t m) := univ.filter fun j => j.2 = x j.1

@[simp] lemma mem_picks (x : Pick t m) (j : Ix t m) : j ∈ picks x ↔ j.2 = x j.1 := by simp [picks]

noncomputable def cfg (b : Sizes t m M) (k : ℕ) (D : Finset (Ix t m)) : Finset (Grid t m M) :=
  univ.filter fun p => match p.1 with
    | none => p.2.val < k
    | some j => p.2 ≤ b j ∧ j ∉ D

@[simp] lemma mem_cfg_none (b : Sizes t m M) (k : ℕ) (D : Finset (Ix t m)) (q : Fin M) :
    (none,q) ∈ cfg b k D ↔ q.val < k := by simp [cfg]

@[simp] lemma mem_cfg_some (b : Sizes t m M) (k : ℕ) (D : Finset (Ix t m)) (j : Ix t m) (q : Fin M) :
    (some j,q) ∈ cfg b k D ↔ q ≤ b j ∧ j ∉ D := by simp [cfg]

lemma cfg_union (b : Sizes t m M) (k l : ℕ) (D E : Finset (Ix t m)) :
    cfg b k D ∪ cfg b l E = cfg b (max k l) (D ∩ E) := by
  ext ⟨j,q⟩
  cases j with
  | none => simp
  | some j => simp; tauto

noncomputable def cfgW (b : Sizes t m M) (x : Pick t m) (w : Fin M → Bool) : Finset (Grid t m M) :=
  univ.filter fun p => match p.1 with
    | none => w p.2 = true
    | some j => p.2 ≤ b j ∧ j ∉ picks x

@[simp] lemma mem_cfgW_none (b : Sizes t m M) (x : Pick t m) (w : Fin M → Bool) (q : Fin M) :
    (none,q) ∈ cfgW b x w ↔ w q = true := by simp [cfgW]

@[simp] lemma mem_cfgW_some (b : Sizes t m M) (x : Pick t m) (w : Fin M → Bool) (j : Ix t m) (q : Fin M) :
    (some j,q) ∈ cfgW b x w ↔ q ≤ b j ∧ j ∉ picks x := by simp [cfgW]

def patch (x : Pick t m) : Local t M ↪ Grid t m M := by
  refine ⟨fun p => (p.1.map (fun i => (i,x i)),p.2), ?_⟩
  rintro ⟨i,q⟩ ⟨j,r⟩ h
  cases i <;> cases j <;> simp_all

noncomputable def liftPatch (x : Pick t m) (τ : Equiv.Perm (Local t M)) : Equiv.Perm (Grid t m M) :=
  τ.extendDomain (Equiv.ofInjective (patch x) (patch x).injective)

lemma lift_apply (x : Pick t m) (τ : Equiv.Perm (Local t M)) (p : Local t M) :
    liftPatch x τ (patch x p) = patch x (τ p) := by
  exact Equiv.Perm.extendDomain_apply_image τ (Equiv.ofInjective (patch x) (patch x).injective) p

noncomputable def edit (x : Pick t m) (f : Fin t → Equiv.Perm (Fin M)) (b : Sizes t m M) : Sizes t m M :=
  fun j => if j ∈ picks x then f j.1 (b j) else b j

lemma transport {l : Combinatorics.Subspace (Fin t) Bool (Fin M)}
    (x : Pick t m) (b b' : Sizes t m M) (a : Fin t → Fin M) (k : Fin (M+1))
    (τ : Equiv.Perm (Local t M)) (hτ : ∀ p, dst a k.val p = src (fun q => (l.idxFun q).swap) (τ p))
    (ha : ∀ i, b' (i,x i) = a i) (hb : ∀ j ∉ picks x, b' j = b j)
    (D : Finset (Ix t m)) (hD : D ⊆ picks x) :
    (cfg b' k.val D).map (liftPatch x τ).toEmbedding =
      cfgW b x (l (fun i => decide ((i,x i) ∉ D))) := by
  let v : Fin t → Bool := fun i => decide ((i,x i) ∉ D)
  have hL (p : Local t M) : patch x p ∈ cfg b' k.val D ↔ (dst a k.val p).elim v id = true := by
    rcases p with ⟨i,q⟩
    cases i with
    | none => change (none,q) ∈ cfg b' k.val D ↔ _; simp [dst]
    | some i =>
      change (some (i,x i),q) ∈ cfg b' k.val D ↔ _
      by_cases hq : q ≤ a i <;> simp [dst, ha, hq, v]
  have hR (p : Local t M) : patch x p ∈ cfgW b x (l v) ↔
      (src (fun q => (l.idxFun q).swap) p).elim v id = true := by
    rcases p with ⟨i,q⟩
    cases i with
    | none =>
      change (none,q) ∈ cfgW b x (l v) ↔ _
      rw [mem_cfgW_none, Combinatorics.Subspace.coe_apply]
      cases h : l.idxFun q <;> simp [src,h]
    | some i =>
      change (some (i,x i),q) ∈ cfgW b x (l v) ↔ _
      simp [src]
  have key (p : Grid t m M) : p ∈ cfg b' k.val D ↔ liftPatch x τ p ∈ cfgW b x (l v) := by
    by_cases hp : p ∈ Set.range (patch (M := M) x)
    · obtain ⟨z,rfl⟩ := hp
      rw [lift_apply, hL, hR, hτ]
    · have hfix : liftPatch x τ p = p :=
        Equiv.Perm.extendDomain_apply_not_subtype τ (Equiv.ofInjective (patch x) (patch x).injective) hp
      rw [hfix]
      obtain ⟨j,q⟩ := p
      cases j with
      | none => exact (hp ⟨(none,q),rfl⟩).elim
      | some j =>
        have hj : j ∉ picks x := by
          rintro hj
          obtain ⟨i,j⟩ := j
          have he : j = x i := (mem_picks _ _).mp hj
          subst j
          exact hp ⟨(some i,q),rfl⟩
        have hDj : j ∉ D := fun h => hj (hD h)
        simp [hb j hj,hj,hDj]
  ext p
  rw [mem_map_equiv, key, Equiv.apply_symm_apply]

variable (χ : Col n) (g : Grid t m M ↪ Fin n)

def mono (b : Sizes t m M) (x : Pick t m) (k : ℕ) (c : Bool) : Prop :=
  ∀ D ⊆ picks x, χ ((cfg b k D).map g) = c

def good (b : Sizes t m M) (x : Pick t m) : Prop :=
  ∃ k : Fin (M+1), ∃ c, mono χ g b x k.val c

lemma glue (b : Sizes t m M) :
    ∃ U : Finset (Finset (Fin n)),
      (univ.filter (good χ g b)).card ≤ 2 * U.card ∧
      Erdos1183.IsMonochromatic χ U ∧ SupClosed (U : Set (Finset (Fin n))) := by
  let S := univ.filter (good χ g b)
  have hw (x : ↥S) : ∃ k : Fin (M+1), ∃ c, mono χ g b x.val k.val c :=
    (mem_filter.mp x.property).2
  choose k col hmono using hw
  let S' (c : Bool) := (univ : Finset ↥S).filter fun x => col x = c
  have hsplit : S.card = (S' true).card + (S' false).card := by
    simpa [S', Fintype.card_coe] using
      (card_filter_add_card_filter_not (s := (univ : Finset ↥S)) (fun x => col x = true)).symm
  obtain ⟨c,hc⟩ : ∃ c, S.card ≤ 2 * (S' c).card := by
    by_cases h : S.card ≤ 2 * (S' true).card
    · exact ⟨true,h⟩
    · exact ⟨false,by omega⟩
  let U := (S' c).biUnion fun x => (picks x.val).powerset.image fun D => (cfg b (k x).val D).map g
  have hU (A : Finset (Fin n)) : A ∈ U ↔ ∃ x ∈ S' c, ∃ D ⊆ picks x.val,
      (cfg b (k x).val D).map g = A := by simp [U]
  refine ⟨U, Nat.le_trans hc (Nat.mul_le_mul_left _ ?_), ⟨c,?_⟩, ?_⟩
  · refine card_le_card_of_injOn (fun x => (cfg b (k x).val (picks x.val)).map g) (fun x hx => ?_) ?_
    · exact (hU _).mpr ⟨x,hx,_,Subset.rfl,rfl⟩
    · intro x _ y _ he
      have hcfg := map_injective g he
      apply Subtype.ext
      funext i
      let j : Ix t m := (i,x.val i)
      have hm : (some j,b j) ∈ cfg b (k y).val (picks y.val) ↔ j ∉ picks y.val := by simp
      rw [← hcfg] at hm
      have hp : j ∈ picks y.val := by by_contra h; simpa [j] using hm.mpr h
      exact (mem_picks _ _).mp hp
  · intro A ha
    obtain ⟨x,hx,D,hD,rfl⟩ := (hU A).mp ha
    exact (hmono x _ hD).trans (mem_filter.mp hx).2
  · intro A ha B hb
    change A ∈ U at ha
    change B ∈ U at hb
    obtain ⟨x,hx,D,hD,rfl⟩ := (hU A).mp ha
    obtain ⟨y,hy,E,hE,rfl⟩ := (hU B).mp hb
    change (cfg b (k x).val D).map g ∪ (cfg b (k y).val E).map g ∈ U
    rw [← map_union, cfg_union]
    apply (hU _).mpr
    rcases le_total (k x).val (k y).val with h | h
    · exact ⟨y,hy,D∩E,inter_subset_right.trans hE,by rw [max_eq_right h]⟩
    · exact ⟨x,hx,D∩E,inter_subset_left.trans hD,by rw [max_eq_left h]⟩

abbrev Trial (t m M : ℕ) := Equiv.Perm (Grid t m M) × Sizes t m M
abbrev Change (t M : ℕ) := Equiv.Perm (Local t M) × (Fin t → Equiv.Perm (Fin M))

noncomputable def action (x : Pick t m) (j : Change t M) (e : Trial t m M) : Trial t m M :=
  ((liftPatch x j.1).trans e.1, edit x j.2 e.2)

lemma action_inj (x : Pick t m) (j : Change t M) : Function.Injective (action x j) := by
  intro e e' he
  have h1 := congrArg Prod.fst he
  have h2 := congrArg Prod.snd he
  apply Prod.ext
  · apply Equiv.ext
    intro p
    have h := Equiv.congr_fun h1 ((liftPatch x j.1).symm p)
    simpa [action] using h
  · funext p
    have h := congrFun h2 p
    change edit x j.2 e.2 p = edit x j.2 e'.2 p at h
    by_cases hp : p ∈ picks x
    · exact (j.2 p.1).injective (by simpa only [edit, hp, if_true] using h)
    · simpa only [edit, hp, if_false] using h

lemma family_bound (g : Grid t m M ↪ Fin n) [NeZero M]
    (hHJ : ∀ C : (Fin M → Bool) → Bool,
      ∃ l : Combinatorics.Subspace (Fin t) Bool (Fin M), l.IsMono C) :
    ∃ U : Finset (Finset (Fin n)), m ^ t ≤ (Fintype.card (Change t M) * 2) * U.card ∧
      Erdos1183.IsMonochromatic χ U ∧ SupClosed (U : Set (Finset (Fin n))) := by
  let P (x : Pick t m) (e : Trial t m M) := good χ (e.1.toEmbedding.trans g) e.2 x
  have hcover (x : Pick t m) (e : Trial t m M) : ∃ j, P x (action x j e) := by
    let g' := e.1.toEmbedding.trans g
    obtain ⟨l,c,hl⟩ := hHJ (fun w => χ ((cfgW e.2 x w).map g'))
    change ∀ v, χ ((cfgW e.2 x (l v)).map g') = c at hl
    obtain ⟨τ,a,k,hτ⟩ := local_match (fun q => (l.idxFun q).swap) (by
      intro i
      obtain ⟨q,hq⟩ := l.proper i
      exact ⟨q, by simp [hq]⟩)
    let f (i : Fin t) := Equiv.swap (e.2 (i,x i)) (a i)
    refine ⟨(τ,f),k,c,?_⟩
    intro D hD
    have hmap := transport x e.2 (edit x f e.2) a k τ hτ
      (fun i => by simp [edit,f]) (fun j hj => by simp [edit,hj]) D hD
    change χ ((cfg (edit x f e.2) k.val D).map (((liftPatch x τ).trans e.1).toEmbedding.trans g)) = c
    have hem : ((liftPatch x τ).trans e.1).toEmbedding.trans g =
        (liftPatch x τ).toEmbedding.trans g' := rfl
    rw [hem, ← map_map, hmap]
    exact hl _
  obtain ⟨e,he⟩ := averaging P action action_inj hcover
  obtain ⟨U,hU,hM,hS⟩ := glue χ (e.1.toEmbedding.trans g) e.2
  have h : m ^ t ≤ Fintype.card (Change t M) * (univ.filter (good χ (e.1.toEmbedding.trans g) e.2)).card := by
    simpa [P, Fintype.card_fun] using he
  exact ⟨U, (h.trans (Nat.mul_le_mul_left _ hU)).trans_eq (by ring), hM,hS⟩
end

lemma poly_bound (t : ℕ) (ht : 0 < t) : ∃ M C : ℕ, 0 < M ∧ 0 < C ∧ ∀ m n : ℕ,
    (t*m+1)*M ≤ n → m ^ t ≤ C * Erdos1183.F n := by
  obtain ⟨M,hM⟩ := Combinatorics.Subspace.exists_mono_in_high_dimension_fin Bool Bool (Fin t)
  have hMp : 0 < M := by
    obtain ⟨l,_⟩ := hM (fun _ => true)
    obtain ⟨q,_⟩ := l.proper ⟨0,ht⟩
    exact q.pos
  let _ : NeZero M := ⟨hMp.ne'⟩
  refine ⟨M,Fintype.card (Change t M)*2,hMp,by positivity,?_⟩
  intro m n hn
  have hcard : Fintype.card (Grid t m M) ≤ n := by simpa [Grid, Ix, Nat.add_comm] using hn
  let g : Grid t m M ↪ Fin n := (Fintype.equivFin _).toEmbedding.trans (Fin.castLEEmb hcard)
  by_contra! hf
  have h := leF (n := n) (m := Erdos1183.F n + 1) (fun χ => by
    obtain ⟨U,hU,hMo,hS⟩ := family_bound χ g hM
    refine ⟨U, ?_, hMo,hS⟩
    have hl : ¬ U.card ≤ Erdos1183.F n := fun hh =>
      (not_le_of_gt hf) (hU.trans (Nat.mul_le_mul_left _ hh))
    omega)
  omega

open Filter

lemma lower : ∀ c : ℝ, ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ c < (Erdos1183.F n : ℝ) := by
  intro c
  obtain ⟨k,hk⟩ := exists_nat_ge c
  let t := k+1
  obtain ⟨M,C,hM,hC,h⟩ := poly_bound t (by dsimp [t]; omega)
  let a := 2*t*M
  have ha : 0 < a := by dsimp [a,t]; positivity
  have haM : 2*M ≤ a := by dsimp [a,t]; nlinarith
  let B := (2*a)^t*C
  filter_upwards [eventually_ge_atTop (max a (B+1))] with n hn
  have hna : a ≤ n := (le_max_left _ _).trans hn
  have hnB : B < n := (Nat.lt_succ_self B).trans_le ((le_max_right _ _).trans hn)
  let m := n/a
  have hm : m*a ≤ n := Nat.div_mul_le_self n a
  have hmpos : 0 < m := Nat.div_pos hna ha
  have hmul : a ≤ m*a := by simpa using Nat.mul_le_mul_right a hmpos
  have hdiv : n % a + m*a = n := by
    simpa [m, Nat.mul_comm] using Nat.mod_add_div n a
  have hmod := Nat.mod_lt n ha
  have hn2 : n ≤ (2*a)*m := by nlinarith
  have hcap : (t*m+1)*M ≤ n := by
    have hh : 2*(t*m*M) = m*a := by dsimp [a]; ring
    nlinarith
  have hf := h m n hcap
  have hp' : n^t ≤ B*Erdos1183.F n := calc
    n^t ≤ ((2*a)*m)^t := Nat.pow_le_pow_left hn2 _
    _ = (2*a)^t*m^t := by rw [mul_pow]
    _ ≤ (2*a)^t*(C*Erdos1183.F n) := Nat.mul_le_mul_left _ hf
    _ = _ := by dsimp [B]; ring
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (ha.trans_le hna)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hBR : (B : ℝ) < n := by exact_mod_cast hnB
  have hpow : (n : ℝ)^t ≤ (B : ℝ)*(Erdos1183.F n : ℝ) := by exact_mod_cast hp'
  have hF : (0 : ℝ) < Erdos1183.F n := by
    have hpos : 0 < (n : ℝ)^t := pow_pos hn0 _
    by_contra! hh
    exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg B) hh)) (hpos.trans_le hpow)
  have hlt : (n : ℝ)^k < (Erdos1183.F n : ℝ) := by
    have haux := hpow.trans_lt (mul_lt_mul_of_pos_right hBR hF)
    rw [show t = k+1 from rfl, pow_succ, mul_comm (n : ℝ)] at haux
    exact lt_of_not_ge (fun hh => (not_lt_of_ge (mul_le_mul_of_nonneg_right hh hn0.le)) haux)
  exact (Real.rpow_le_rpow_of_exponent_le hn1 hk).trans_lt (by simpa [Real.rpow_natCast] using hlt)

lemma upper : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, (Erdos1183.F n : ℝ) < (1 + ε) ^ n := by
  intro ε hε
  let c := Real.log (1 + ε)
  have hc : 0 < c := Real.log_pos (by linarith)
  have h1 := (Real.isLittleO_pow_log_id_atTop (n := 2)).bound (show 0 < c / 16 by positivity)
  have h2 := (Real.isLittleO_pow_log_id_atTop (n := 1)).bound (show 0 < c / 16 by positivity)
  filter_upwards [tendsto_natCast_atTop_atTop.eventually h1,
    tendsto_natCast_atTop_atTop.eventually h2,
    tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop (16 / c)), eventually_ge_atTop (2 : ℕ)]
    with n hn1 hn2 hn3 hn
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  let k := Nat.log 2 n
  let d := 2 * (k + 1)
  have hpk : n < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have hk : k < 2 ^ k := Nat.lt_two_pow_self
  have hpd : d ≤ 2 ^ (k + 1) := by dsimp [d]; rw [pow_succ]; omega
  have hp4 : 4 ≤ 2 ^ (k + 1) := by
    have h : 0 < k := Nat.log_pos (show 1 < 2 by norm_num) hn
    calc
      4 = (2 : ℕ)^2 := by norm_num
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hd : n * d + 2 < 2 ^ d := by
    change n * d + 2 < 2 ^ (2 * (k+1))
    rw [Nat.mul_comm 2, pow_mul]
    generalize 2 ^ (k + 1) = p at hpk hpd hp4 ⊢
    nlinarith
  have hb : Erdos1183.F n ≤ d * n ^ d := (choose_bound hd).trans (calc
    ∑ i ∈ range d, n.choose i ≤ ∑ _i ∈ range d, n ^ d := sum_le_sum fun i hi =>
      (Nat.choose_le_pow n i).trans (Nat.pow_le_pow_right (by omega) (mem_range.mp hi).le)
    _ = _ := by simp [smul_eq_mul])
  have hbR : (Erdos1183.F n : ℝ) ≤ (d : ℝ) * (n : ℝ) ^ d := by exact_mod_cast hb
  apply hbR.trans_lt
  let L := Real.log n
  have hL : 0 ≤ L := Real.log_nonneg (by linarith)
  have hnpos : (0 : ℝ) < n := by linarith
  change ‖(Real.log (n : ℝ)) ^ 2‖ ≤ c / 16 * ‖(n : ℝ)‖ at hn1
  change ‖(Real.log (n : ℝ)) ^ 1‖ ≤ c / 16 * ‖(n : ℝ)‖ at hn2
  simp only [← show L = Real.log n from rfl, pow_one, Real.norm_eq_abs,
    abs_of_nonneg hL, abs_of_nonneg (sq_nonneg L), abs_of_pos hnpos] at hn1 hn2
  have hnc : 16 < (n : ℝ) * c := (div_lt_iff₀ hc).mp hn3
  have hlow : (2 : ℝ) ^ k ≤ n := by exact_mod_cast Nat.pow_log_le_self 2 (show n ≠ 0 by omega)
  have hlog := Real.log_le_log (show 0 < (2 : ℝ)^k by positivity) hlow
  rw [Real.log_pow] at hlog
  have hlog2 := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
  norm_num at hlog2
  have hkR : (k : ℝ) ≤ 2 * L := by nlinarith [Nat.cast_nonneg (α := ℝ) k]
  have hdR : (d : ℝ) ≤ 4 * L + 2 := by dsimp [d]; push_cast; linarith
  have hdp : (0 : ℝ) < d := by dsimp [d]; positivity
  rw [← Real.log_lt_log_iff (by positivity) (by positivity),
    Real.log_mul hdp.ne' (by positivity), Real.log_pow, Real.log_pow]
  have hlogd := Real.log_le_sub_one_of_pos hdp
  have hp := mul_le_mul_of_nonneg_right hdR (show 0 ≤ 1+L by positivity)
  change Real.log d + (d : ℝ) * L < (n : ℝ) * c
  nlinarith
end OMA1183

theorem OMA.solution : type_of% @Erdos1183.erdos_1183.parts.iii := by
  exact ⟨OMA1183.lower, OMA1183.upper⟩