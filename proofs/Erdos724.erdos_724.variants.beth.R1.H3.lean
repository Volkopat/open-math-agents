import OMAReductions.R_Erdos724_erdos_724_variants_beth_R1

/-!
Wilson’s truncated transversal design recursion. The array gluing argument generalizes the four-column construction of @ptc-prover-bot in merged PR 3230, commit 02c8589. The arbitrary-size Latin square family and its conversion to and from an orthogonal array are supplied here.
-/
/-! Generalized from @ptc-prover-bot, merged PR 3230, commit 02c8589. -/
namespace W724
def IsOA {α : Type*} (k : ℕ) (S : Set (Fin k → α)) : Prop :=
  ∀ a b : Fin k, a ≠ b → Set.BijOn (fun r => (r a, r b)) S Set.univ

variable {T U M : Type*} {d : ℕ}

def rowA (β : Fin (d+1) → T) (r : Fin d → M) : Fin d → (T × M) ⊕ U :=
  fun g => Sum.inl (β g.castSucc, r g)

def rowB (β : Fin (d+1) → T) (k : U) (r : Fin d → Option M) : Fin d → (T × M) ⊕ U :=
  fun g => match r g with
    | none => Sum.inr k
    | some s => Sum.inl (β g.castSucc, s)

def rowC (r : Fin d → U) : Fin d → (T × M) ⊕ U := fun g => Sum.inr (r g)

def W (S5 : Set (Fin (d+1) → T)) (S3 : Set (Fin d → M)) (S4 : Set (Fin d → Option M))
    (SU : Set (Fin d → U)) (ι : U → T) : Set (Fin d → (T × M) ⊕ U) :=
  {x | ∃ β ∈ S5, (∀ k, ι k ≠ β (Fin.last d)) ∧ ∃ r ∈ S3, x = rowA β r} ∪
  {x | ∃ β ∈ S5, ∃ k, ι k = β (Fin.last d) ∧ ∃ r ∈ S4, r ≠ (fun _ => none) ∧ x = rowB β k r} ∪
  {x | ∃ r ∈ SU, x = rowC r}

lemma rowB_eq_inl {β : Fin (d+1) → T} {k : U} {r : Fin d → Option M} {g : Fin d} {p : T × M} :
    rowB β k r g = Sum.inl p ↔ ∃ s, r g = some s ∧ p = (β g.castSucc, s) := by
  unfold rowB
  cases r g <;> simp [eq_comm]

lemma rowB_eq_inr {β : Fin (d+1) → T} {k : U} {r : Fin d → Option M} {g : Fin d} {k' : U} :
    rowB β k r g = Sum.inr k' ↔ r g = none ∧ k = k' := by
  unfold rowB
  cases r g <;> simp

lemma inj_of {α : Type*} {k : ℕ} {S : Set (Fin k → α)} (h : IsOA k S) {a b : Fin k} (hab : a ≠ b)
    {r r' : Fin k → α} (hr : r ∈ S) (hr' : r' ∈ S) (h1 : r a = r' a) (h2 : r b = r' b) : r = r' :=
  (h a b hab).injOn hr hr' (Prod.ext h1 h2)

lemma ex_of {α : Type*} {k : ℕ} {S : Set (Fin k → α)} (h : IsOA k S) {a b : Fin k} (hab : a ≠ b)
    (x y : α) : ∃ r ∈ S, r a = x ∧ r b = y := by
  obtain ⟨r, hr, he⟩ := (h a b hab).surjOn (Set.mem_univ (x, y))
  exact ⟨r, hr, (Prod.ext_iff.mp he).1, (Prod.ext_iff.mp he).2⟩

theorem wilson_OA {S5 : Set (Fin (d+1) → T)} {S3 : Set (Fin d → M)}
    {S4 : Set (Fin d → Option M)} {SU : Set (Fin d → U)} {ι : U → T}
    (h5 : IsOA (d+1) S5) (h3 : IsOA d S3) (h4 : IsOA d S4) (hnone : (fun _ => none) ∈ S4)
    (hU : IsOA d SU) (hι : Function.Injective ι) : IsOA d (W S5 S3 S4 SU ι) := by
  classical
  intro a b hab
  have hab' : a.castSucc ≠ b.castSucc := fun h => hab (Fin.castSucc_injective _ h)
  have ha4 : a.castSucc ≠ Fin.last d := Fin.castSucc_ne_last a
  have hb4 : b.castSucc ≠ Fin.last d := Fin.castSucc_ne_last b
  -- a row of S4 with two `none` entries at a, b is the all-none row
  have allnone : ∀ r ∈ S4, r a = none → r b = none → r = fun _ => none := fun r hr h1 h2 =>
    inj_of h4 hab hr hnone h1 h2
  refine ⟨fun _ _ => Set.mem_univ _, ?_, ?_⟩
  · -- injectivity
    rintro x hx y hy hxy
    simp only [Prod.mk.injEq] at hxy
    obtain ⟨hxa, hxb⟩ := hxy
    rcases hx with (⟨β, hβ, hβι, r, hr, rfl⟩ | ⟨β, hβ, k, hk, r, hr, hrn, rfl⟩) | ⟨r, hr, rfl⟩ <;>
    rcases hy with (⟨γ, hγ, hγι, s, hs, rfl⟩ | ⟨γ, hγ, k', hk', s, hs, hsn, rfl⟩) | ⟨s, hs, rfl⟩
    -- A A
    · simp only [rowA, Sum.inl.injEq, Prod.mk.injEq] at hxa hxb
      rw [inj_of h5 hab' hβ hγ hxa.1 hxb.1, inj_of h3 hab hr hs hxa.2 hxb.2]
    -- A B
    · exfalso
      obtain ⟨s1, hs1, e1⟩ := rowB_eq_inl.mp hxa.symm
      obtain ⟨s2, hs2, e2⟩ := rowB_eq_inl.mp hxb.symm
      simp only [rowA, Prod.mk.injEq] at e1 e2
      have := inj_of h5 hab' hβ hγ e1.1 e2.1
      exact hβι k' (this ▸ hk')
    -- A C
    · simp [rowA, rowC] at hxa
    -- B A
    · exfalso
      obtain ⟨s1, hs1, e1⟩ := rowB_eq_inl.mp hxa
      obtain ⟨s2, hs2, e2⟩ := rowB_eq_inl.mp hxb
      simp only [rowA, Prod.mk.injEq] at e1 e2
      have := inj_of h5 hab' hβ hγ e1.1.symm e2.1.symm
      exact hγι k (this ▸ hk)
    -- B B
    · cases hra : r a with
      | none =>
        cases hrb : r b with
        | none => exact absurd (allnone r hr hra hrb) hrn
        | some v =>
          have xa : rowB β k r a = Sum.inr k := by simp [rowB, hra]
          have xb : rowB β k r b = Sum.inl (β b.castSucc, v) := by simp [rowB, hrb]
          rw [xa] at hxa; rw [xb] at hxb
          obtain ⟨hsa, rfl⟩ := rowB_eq_inr.mp hxa.symm
          obtain ⟨w, hsb, e⟩ := rowB_eq_inl.mp hxb.symm
          simp only [Prod.mk.injEq] at e
          have hβγ : β = γ := inj_of h5 hb4 hβ hγ e.1 (hk.symm.trans hk')
          subst hβγ
          rw [inj_of h4 hab hr hs (hra.trans hsa.symm) (hrb.trans (by rw [hsb, e.2]))]
      | some v =>
        have xa : rowB β k r a = Sum.inl (β a.castSucc, v) := by simp [rowB, hra]
        rw [xa] at hxa
        obtain ⟨w, hsa, e⟩ := rowB_eq_inl.mp hxa.symm
        simp only [Prod.mk.injEq] at e
        cases hrb : r b with
        | none =>
          have xb : rowB β k r b = Sum.inr k := by simp [rowB, hrb]
          rw [xb] at hxb
          obtain ⟨hsb, rfl⟩ := rowB_eq_inr.mp hxb.symm
          have hβγ : β = γ := inj_of h5 ha4 hβ hγ e.1 (hk.symm.trans hk')
          subst hβγ
          rw [inj_of h4 hab hr hs (hra.trans (by rw [hsa, e.2])) (hrb.trans hsb.symm)]
        | some v' =>
          have xb : rowB β k r b = Sum.inl (β b.castSucc, v') := by simp [rowB, hrb]
          rw [xb] at hxb
          obtain ⟨w', hsb, e'⟩ := rowB_eq_inl.mp hxb.symm
          simp only [Prod.mk.injEq] at e'
          have hβγ : β = γ := inj_of h5 hab' hβ hγ e.1 e'.1
          subst hβγ
          have hkk : k = k' := hι (hk.trans hk'.symm)
          subst hkk
          rw [inj_of h4 hab hr hs (hra.trans (by rw [hsa, e.2])) (hrb.trans (by rw [hsb, e'.2]))]
    -- B C
    · exfalso
      obtain ⟨h1, -⟩ := rowB_eq_inr.mp hxa
      obtain ⟨h2, -⟩ := rowB_eq_inr.mp hxb
      exact hrn (allnone r hr h1 h2)
    -- C A
    · simp [rowA, rowC] at hxa
    -- C B
    · exfalso
      obtain ⟨h1, -⟩ := rowB_eq_inr.mp hxa.symm
      obtain ⟨h2, -⟩ := rowB_eq_inr.mp hxb.symm
      exact hsn (allnone s hs h1 h2)
    -- C C
    · simp only [rowC, Sum.inr.injEq] at hxa hxb
      rw [inj_of hU hab hr hs hxa hxb]
  · -- surjectivity
    rintro ⟨P, Q⟩ -
    rcases P with ⟨p, α⟩ | k <;> rcases Q with ⟨q, α'⟩ | k'
    · obtain ⟨β, hβ, e1, e2⟩ := ex_of h5 hab' p q
      by_cases hι' : ∃ k, ι k = β (Fin.last d)
      · obtain ⟨k, hk⟩ := hι'
        obtain ⟨r, hr, r1, r2⟩ := ex_of h4 hab (some α) (some α')
        refine ⟨rowB β k r, Or.inl (Or.inr ⟨β, hβ, k, hk, r, hr, fun h => by simp [h] at r1, rfl⟩), ?_⟩
        simp [rowB, r1, r2, e1, e2]
      · push_neg at hι'
        obtain ⟨r, hr, r1, r2⟩ := ex_of h3 hab α α'
        exact ⟨rowA β r, Or.inl (Or.inl ⟨β, hβ, hι', r, hr, rfl⟩), by simp [rowA, r1, r2, e1, e2]⟩
    · obtain ⟨β, hβ, e1, e2⟩ := ex_of h5 ha4 p (ι k')
      obtain ⟨r, hr, r1, r2⟩ := ex_of h4 hab (some α) none
      refine ⟨rowB β k' r, Or.inl (Or.inr ⟨β, hβ, k', e2.symm, r, hr, fun h => by simp [h] at r1, rfl⟩), ?_⟩
      simp [rowB, r1, r2, e1]
    · obtain ⟨β, hβ, e1, e2⟩ := ex_of h5 hb4 q (ι k)
      obtain ⟨r, hr, r1, r2⟩ := ex_of h4 hab none (some α')
      refine ⟨rowB β k r, Or.inl (Or.inr ⟨β, hβ, k, e2.symm, r, hr, fun h => by simp [h] at r2, rfl⟩), ?_⟩
      simp [rowB, r1, r2, e1]
    · obtain ⟨r, hr, r1, r2⟩ := ex_of hU hab k k'
      exact ⟨rowC r, Or.inr ⟨r, hr, rfl⟩, by simp [rowC, r1, r2]⟩


lemma oa_of_range {ι α : Type*} [Fintype ι] [Fintype α] {k : ℕ} (f : ι → Fin k → α)
    (hcard : Fintype.card ι = Fintype.card α * Fintype.card α)
    (h : ∀ a b : Fin k, a ≠ b → Function.Injective fun i => (f i a, f i b)) :
    IsOA k (Set.range f) := by
  intro a b hab
  refine ⟨fun _ _ => Set.mem_univ _, ?_, ?_⟩
  · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hij
    rw [h a b hab hij]
  · intro xy _
    have hb : Function.Bijective fun i => (f i a, f i b) :=
      (Fintype.bijective_iff_injective_and_card _).mpr ⟨h a b hab, by rw [hcard, Fintype.card_prod]⟩
    obtain ⟨i, hi⟩ := hb.2 xy
    exact ⟨f i, ⟨i, rfl⟩, hi⟩


end W724

namespace W724
open Finset Erdos724

private def sizes (n : ℕ) : Set ℕ := {k | ∃ S : Finset (LatinSquare n), S.card=k ∧ (S:Set (LatinSquare n)).Pairwise IsOrthogonal}
lemma sizes_bdd (n : ℕ) : BddAbove (sizes n) := by
  refine ⟨Fintype.card (LatinSquare n),?_⟩
  rintro _ ⟨S,rfl,_⟩; exact card_le_univ S

lemma getFamily {s n : ℕ} (h : s ≤ maxMOLS n) : ∃ L : Fin s → LatinSquare n,
    ∀ i j, i≠j → IsOrthogonal (L i) (L j) := by
  classical
  have h0 : 0∈sizes n := ⟨∅,rfl,by simp⟩
  obtain ⟨S,hS,hp⟩ := Nat.sSup_mem ⟨0,h0⟩ (sizes_bdd n)
  have hle : s≤S.card := by rw [hS]; exact h
  let E : Fin s ↪ S := (Fin.castLEEmb hle).trans (Fintype.equivFinOfCardEq (α:=S) (by simp : Fintype.card S = S.card)).symm.toEmbedding
  exact ⟨fun i => E i,fun i j hij => hp (E i).2 (E j).2 (fun eq => hij (E.injective (Subtype.ext eq)))⟩

def fullRow {s n : ℕ} (L : Fin s → LatinSquare n) (p : Fin n × Fin n) : Fin (s+2) → Fin n :=
  Fin.cases p.1 (Fin.cases p.2 (fun v => (L v).mat p.1 p.2))

lemma input {s n : ℕ} (h : s ≤ maxMOLS n) : ∃ S, @IsOA (Fin n) (s+2) S := by
  classical
  obtain ⟨L,hL⟩ := getFamily h
  refine ⟨Set.range (fullRow L),oa_of_range _ (by simp) ?_⟩
  intro c d hcd
  rintro ⟨i,j⟩ ⟨i',j'⟩ eq
  obtain ⟨hx,hy⟩ := Prod.mk.inj eq
  rcases Fin.eq_zero_or_eq_succ c with rfl|⟨c,rfl⟩
  · rcases Fin.eq_zero_or_eq_succ d with rfl|⟨d,rfl⟩
    · exact (hcd rfl).elim
    rcases Fin.eq_zero_or_eq_succ d with rfl|⟨d,rfl⟩
    · exact Prod.ext hx hy
    change i=i' at hx
    subst i'
    exact Prod.ext rfl ((L d).row_injective i hy)
  rcases Fin.eq_zero_or_eq_succ c with rfl|⟨c,rfl⟩
  · rcases Fin.eq_zero_or_eq_succ d with rfl|⟨d,rfl⟩
    · exact Prod.ext hy hx
    rcases Fin.eq_zero_or_eq_succ d with rfl|⟨d,rfl⟩
    · exact (hcd rfl).elim
    change j=j' at hx
    subst j'
    exact Prod.ext ((L d).col_injective j hy) rfl
  rcases Fin.eq_zero_or_eq_succ d with rfl|⟨d,rfl⟩
  · change i=i' at hy
    subst i'
    exact Prod.ext rfl ((L c).row_injective i hx)
  rcases Fin.eq_zero_or_eq_succ d with rfl|⟨d,rfl⟩
  · change j=j' at hy
    subst j'
    exact Prod.ext ((L c).col_injective j hx) rfl
  exact hL c d (fun E => hcd (E ▸ rfl)) (Prod.ext hx hy)

lemma relabel {α β : Type*} {d : ℕ} {S : Set (Fin d → α)} (hS : IsOA d S) (e : Fin d → α ≃ β) :
    IsOA d ((fun (r : Fin d → α) i => e i (r i)) '' S) := by
  intro a b hab
  refine ⟨fun _ _ => Set.mem_univ _,?_,?_⟩
  · rintro _ ⟨r,hr,rfl⟩ _ ⟨s,hs,rfl⟩ eq
    have := inj_of hS hab hr hs ((e a).injective (Prod.mk.inj eq).1) ((e b).injective (Prod.mk.inj eq).2)
    rw [this]
  · rintro ⟨x,y⟩ -
    obtain ⟨r,hr,hx,hy⟩ := ex_of hS hab ((e a).symm x) ((e b).symm y)
    exact ⟨_,⟨r,hr,rfl⟩,by simp [hx,hy]⟩

lemma withNone {s m : ℕ} (h : s ≤ maxMOLS (m+1)) : ∃ S, @IsOA (Option (Fin m)) (s+2) S ∧ (fun _ => none) ∈ S := by
  classical
  obtain ⟨A,hA⟩ := input h
  obtain ⟨r,hr,_,_⟩ := ex_of hA (show (0:Fin (s+2))≠1 by exact Fin.zero_ne_one) 0 0
  let e : Fin (m+1) ≃ Option (Fin m) := (Fintype.equivFinOfCardEq (by simp)).symm
  let E (i : Fin (s+2)) := e.trans (Equiv.swap (e (r i)) none)
  refine ⟨_,relabel hA E, r,hr,?_⟩
  funext i
  simp [E]
end W724


namespace W724
open Finset Erdos724

-- The two axes and the remaining columns of an array give the required family.
theorem output {s n : ℕ} (hn : 2≤n) {α : Type*} (e : α ≃ Fin n)
    {S : Set (Fin (s+2) → α)} (h : IsOA (s+2) S) : s ≤ maxMOLS n := by
  classical
  let a : Fin (s+2) := 0
  let b : Fin (s+2) := (0:Fin (s+1)).succ
  let c (i : Fin s) := i.succ.succ
  have hab : a ≠ b := Ne.symm (Fin.succ_ne_zero _)
  have hac (i : Fin s) : a ≠ c i := Ne.symm (Fin.succ_ne_zero _)
  have hbc (i : Fin s) : b ≠ c i := fun eq => Fin.succ_ne_zero i (Fin.succ_injective _ eq).symm
  let row (p : Fin n × Fin n) := (ex_of h hab (e.symm p.1) (e.symm p.2)).choose
  have hr (p : Fin n × Fin n) : row p∈S ∧ row p a=e.symm p.1 ∧ row p b=e.symm p.2 :=
    (ex_of h hab _ _).choose_spec
  have key {u v : Fin (s+2)} (huv : u≠v) {p q : Fin n × Fin n}
      (hu : row p u=row q u) (hv : row p v=row q v) : p=q := by
    have eq := inj_of h huv (hr p).1 (hr q).1 hu hv
    exact Prod.ext (e.symm.injective ((hr p).2.1.symm.trans ((congrFun eq a).trans (hr q).2.1)))
      (e.symm.injective ((hr p).2.2.symm.trans ((congrFun eq b).trans (hr q).2.2)))
  let L (i : Fin s) : LatinSquare n := {
    mat := fun x y => e (row (x,y) (c i))
    row_injective := fun x y z eq => congrArg Prod.snd (key (hac i)
      ((hr (x,y)).2.1.trans (hr (x,z)).2.1.symm) (e.injective eq))
    col_injective := fun y x z eq => congrArg Prod.fst (key (hbc i)
      ((hr (x,y)).2.2.trans (hr (z,y)).2.2.symm) (e.injective eq)) }
  have horth {i j : Fin s} (hij : i≠j) : IsOrthogonal (L i) (L j) := by
    intro p q eq
    exact key (show c i ≠ c j from fun E => hij (Fin.succ_injective _ (Fin.succ_injective _ E)))
      (e.injective (Prod.mk.inj eq).1) (e.injective (Prod.mk.inj eq).2)
  have hinj : Function.Injective L := by
    intro i j E
    by_contra hij
    have hh := horth hij; rw [E] at hh
    let z : Fin n := ⟨0,by omega⟩
    let o : Fin n := ⟨1,by omega⟩
    obtain ⟨k,hk⟩ := (Finite.injective_iff_surjective.mp ((L j).row_injective o)) ((L j).mat z z)
    have eq : (o,k)=(z,z) := hh (Prod.ext hk hk)
    have := congrArg (fun p : Fin n × Fin n => p.1.val) eq
    contradiction
  apply le_csSup (sizes_bdd n)
  refine ⟨univ.image L,by rw [card_image_of_injective _ hinj]; simp,?_⟩
  rintro _ h1 _ h2 hne
  obtain ⟨i,_,rfl⟩ := mem_image.mp h1
  obtain ⟨j,_,rfl⟩ := mem_image.mp h2
  exact horth (fun eq => hne (congrArg L eq))

theorem wilson (m t u s : ℕ) (hm : 1 ≤ m) (hu : 1≤u) (hut : u≤t)
    (h1 : s ≤ maxMOLS m) (h2 : s ≤ maxMOLS (m+1)) (h3 : s+1 ≤ maxMOLS t)
    (h4 : s ≤ maxMOLS u) : s ≤ maxMOLS (m*t+u) := by
  classical
  obtain ⟨A,hA⟩ := input h3
  obtain ⟨B,hB⟩ := input h1
  obtain ⟨C,hC,h0⟩ := withNone h2
  obtain ⟨D,hD⟩ := input h4
  have hOA := wilson_OA hA hB hC h0 hD (Fin.castLEEmb hut).injective
  let e : ((Fin t × Fin m) ⊕ Fin u) ≃ Fin (m*t+u) := Fintype.equivFinOfCardEq (by simp [Nat.mul_comm])
  exact output (by nlinarith) e hOA
end W724


theorem OMA.solution : OMA.R_Erdos724_erdos_724_variants_beth_R1.H3 := W724.wilson
