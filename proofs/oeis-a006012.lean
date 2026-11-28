import OMAStatements.S_oeis_a006012

-- Based on the counting argument of Yonah Biers-Ariel, JIS 20 (2017), Article 17.8.3.

namespace OMA
open S_oeis_a006012

def classicalPattern {m : ℕ} (σ : Fin m → Fin m) : Prop :=
  ∃ i j k l : Fin m, i < j ∧ j < k ∧ k < l ∧ max (σ i) (σ k) < min (σ j) (σ l)

lemma discrete_crossing (P : ℕ → Prop) (j k : ℕ) (hj : P j) (hk : ¬P k) (hjk : j ≤ k) :
    ∃ e : ℕ, j ≤ e ∧ e < k ∧ P e ∧ ¬P (e+1) := by
  classical
  induction k with
  | zero => simp_all
  | succ k ih =>
    have hne : j ≠ k + 1 := fun he => hk (he ▸ hj)
    have hjk' : j ≤ k := by omega
    by_cases h : P k
    · exact ⟨k, hjk', by omega, h, hk⟩
    · obtain ⟨e, hje, hek, hgood⟩ := ih h hjk'
      exact ⟨e, hje, by omega, hgood⟩

lemma contains_iff_classical {m : ℕ} (σ : Equiv.Perm (Fin m)) :
    containsPattern σ ↔ classicalPattern σ := by
  constructor
  · rintro ⟨i,j,k,l,hij,hjk,hkl,h⟩
    exact ⟨i,j,k,l,hij,by omega,hkl,h⟩
  · rintro ⟨i,j,k,l,hij,hjk,hkl,h⟩
    let z := max (σ i) (σ k)
    let P (u : ℕ) := ∃ hu : u < m, z < σ ⟨u,hu⟩
    have hboth : z < σ j ∧ z < σ l := lt_min_iff.mp h
    obtain ⟨e, hje, hek, ⟨he, hhigh⟩, hnext⟩ := discrete_crossing P j k ⟨j.isLt,hboth.1⟩
      (by rintro ⟨_,hx⟩; exact (not_lt_of_ge (le_max_right _ _)) hx) (by omega)
    have hes : e+1 < m := by omega
    have hlo : σ ⟨e+1,hes⟩ ≤ z := le_of_not_gt (fun hc => hnext ⟨hes,hc⟩)
    refine ⟨i, ⟨e,he⟩, ⟨e+1,hes⟩, l, (show i.val < e by omega), rfl, (show e+1 < l.val by omega), ?_⟩
    exact lt_min ((max_le (le_max_left _ _) hlo).trans_lt hhigh) ((max_le (le_max_left _ _) hlo).trans_lt hboth.2)

/-- The two least entries of a classical avoider occupy consecutive positions,
or one of them is the last entry. The order of the two least values is immaterial. -/
lemma pair_adjacent_or_last {n : ℕ} (σ : Equiv.Perm (Fin (n+2))) (havoid : ¬classicalPattern σ)
    (u v : Fin (n+2)) (huv : u < v) (hlo : (σ u).val ≤ 1) (hlo' : (σ v).val ≤ 1) :
    v.val = u.val+1 ∨ v = Fin.last (n+1) := by
  by_contra! hbad
  have hx : u.val+1 < v.val := by omega
  have hv : v.val < n+1 := by
    have hn : v.val ≠ n+1 := fun he => hbad.2 (Fin.ext he)
    omega
  let j : Fin (n+2) := ⟨u.val+1, by omega⟩
  let l : Fin (n+2) := ⟨v.val+1, by omega⟩
  have hhigh (x : Fin (n+2)) (hxu : x ≠ u) (hxv : x ≠ v) : 1 < (σ x).val := by
    have h' : (σ u).val ≠ (σ v).val := fun he => (ne_of_lt huv) (σ.injective (Fin.ext he))
    have hx' : (σ x).val ≠ (σ u).val := fun he => hxu (σ.injective (Fin.ext he))
    have hx'' : (σ x).val ≠ (σ v).val := fun he => hxv (σ.injective (Fin.ext he))
    omega
  have hp : u < j := by change u.val < u.val+1; omega
  have hq : j < v := hx
  have hr : v < l := by change v.val < v.val+1; omega
  have hj := hhigh j hp.ne' hq.ne
  have hl := hhigh l ((huv.trans hr).ne') hr.ne'
  exact havoid ⟨u,j,v,l,hp,hq,hr,lt_min (max_lt (show (σ u).val < (σ j).val by omega)
    (show (σ v).val < (σ j).val by omega)) (max_lt (show (σ u).val < (σ l).val by omega)
    (show (σ v).val < (σ l).val by omega))⟩



/-- Insert a given value at a given position, standardizing all other positions and values in order. -/
def insertPerm {n : ℕ} (p q : Fin (n+1)) (σ : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n+1)) :=
  (finSuccEquiv' p).trans ((Equiv.optionCongr σ).trans (finSuccEquiv' q).symm)

@[simp] lemma insertPerm_at {n : ℕ} (p q : Fin (n+1)) (σ : Equiv.Perm (Fin n)) :
    insertPerm p q σ p = q := by simp [insertPerm]

@[simp] lemma insertPerm_away {n : ℕ} (p q : Fin (n+1)) (σ : Equiv.Perm (Fin n)) (x : Fin n) :
    insertPerm p q σ (p.succAbove x) = q.succAbove (σ x) := by simp [insertPerm]

def removePerm {n : ℕ} (p : Fin (n+1)) (τ : Equiv.Perm (Fin (n+1))) : Equiv.Perm (Fin n) :=
  (finSuccAboveEquiv p).trans ((τ.subtypeEquiv (p:=fun x => x ≠ p) (q:=fun y => y ≠ τ p)
    (fun _ => τ.injective.ne_iff.symm)).trans (finSuccAboveEquiv (τ p)).symm)

lemma removePerm_spec {n : ℕ} (p : Fin (n+1)) (τ : Equiv.Perm (Fin (n+1))) (x : Fin n) :
    (τ p).succAbove (removePerm p τ x) = τ (p.succAbove x) := by
  have h := (finSuccAboveEquiv (τ p)).apply_symm_apply
    ((τ.subtypeEquiv (p:=fun x => x ≠ p) (q:=fun y => y ≠ τ p) (fun _ => τ.injective.ne_iff.symm)) (finSuccAboveEquiv p x))
  exact congrArg Subtype.val h

lemma reinsert_remove {n : ℕ} (p : Fin (n+1)) (τ : Equiv.Perm (Fin (n+1))) :
    insertPerm p (τ p) (removePerm p τ) = τ := by
  ext y
  refine Fin.succAboveCases p ?_ (fun x => ?_) y
  · simp
  · simp [removePerm_spec]

lemma insertPerm_inj {n : ℕ} (p q : Fin (n+1)) : Function.Injective (insertPerm p q) := by
  intro σ τ h
  apply Equiv.ext
  intro x
  apply Fin.succAbove_right_injective (p:=q)
  simpa using DFunLike.congr_fun h (p.succAbove x)

lemma insert_inherits {n : ℕ} (p q : Fin (n+1)) (σ : Equiv.Perm (Fin n)) :
    classicalPattern σ → classicalPattern (insertPerm p q σ) := by
  rintro ⟨i,j,k,l,hij,hjk,hkl,h⟩
  have hp := Fin.strictMono_succAbove p
  have hq := Fin.strictMono_succAbove q
  refine ⟨_,_,_,_,hp hij,hp hjk,hp hkl,?_⟩
  simpa [← hq.monotone.map_max, ← hq.monotone.map_min] using hq h

/-- In any pattern the two high values have rank at least two, since they both exceed two distinct entries. -/
lemma pattern_peaks {m : ℕ} (τ : Equiv.Perm (Fin m)) {i j k l : Fin m} (hik : i < k)
    (h : max (τ i) (τ k) < min (τ j) (τ l)) : 1 < (τ j).val ∧ 1 < (τ l).val := by
  obtain ⟨h1,h2⟩ := lt_min_iff.mp h
  obtain ⟨h3,h4⟩ := max_lt_iff.mp h1
  obtain ⟨h5,h6⟩ := max_lt_iff.mp h2
  have hne : (τ i).val ≠ (τ k).val := fun he => hik.ne (τ.injective (Fin.ext he))
  constructor <;> omega

lemma from_inherited {n : ℕ} {p q : Fin (n+1)} {σ : Equiv.Perm (Fin n)}
    {i j k l : Fin (n+1)} (hij : i < j) (hjk : j < k) (hkl : k < l)
    (h : max (insertPerm p q σ i) (insertPerm p q σ k) < min (insertPerm p q σ j) (insertPerm p q σ l))
    (hi : i ≠ p) (hj : j ≠ p) (hk : k ≠ p) (hl : l ≠ p) : classicalPattern σ := by
  obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq hi
  obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hj
  obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hk
  obtain ⟨l, rfl⟩ := Fin.exists_succAbove_eq hl
  refine ⟨i,j,k,l,(Fin.strictMono_succAbove p).lt_iff_lt.mp hij,(Fin.strictMono_succAbove p).lt_iff_lt.mp hjk,
    (Fin.strictMono_succAbove p).lt_iff_lt.mp hkl,?_⟩
  have hq := Fin.strictMono_succAbove q
  exact hq.lt_iff_lt.mp (by simpa [hq.monotone.map_max,hq.monotone.map_min] using h)

lemma append_low_iff {n : ℕ} (q : Fin (n+1)) (hq : q.val ≤ 1) (σ : Equiv.Perm (Fin n)) :
    classicalPattern (insertPerm (Fin.last n) q σ) ↔ classicalPattern σ := by
  refine ⟨?_,insert_inherits _ _ _⟩
  rintro ⟨i,j,k,l,hij,hjk,hkl,hw⟩
  have hpk := (pattern_peaks _ (hij.trans hjk) hw).2
  have hl : l ≠ Fin.last n := by intro he; subst l; simp at hpk; omega
  exact from_inherited hij hjk hkl hw (Fin.ne_last_of_lt hij) (Fin.ne_last_of_lt hjk) (Fin.ne_last_of_lt hkl) hl



lemma succAbove_low_rank {n : ℕ} (q : Fin (n+2)) (hq : q.val ≤ 1) (x : Fin (n+1)) :
    (q.succAbove x).val - 1 = x.val := by
  by_cases h : x.castSucc < q
  · rw [Fin.succAbove_of_castSucc_lt _ _ h]; change x.val - 1 = x.val
    change x.val < q.val at h; omega
  · rw [Fin.succAbove_of_le_castSucc _ _ (le_of_not_gt h)]; simp

lemma duplicate_low_iff {n : ℕ} (q : Fin (n+2)) (hq : q.val ≤ 1) (σ : Equiv.Perm (Fin (n+1))) :
    classicalPattern (insertPerm (σ.symm 0).castSucc q σ) ↔ classicalPattern σ := by
  let t := σ.symm 0
  let τ := insertPerm t.castSucc q σ
  have hclip (x : Fin (n+2)) : (σ (t.predAbove x)).val = (τ x).val - 1 := by
    refine Fin.succAboveCases t.castSucc ?_ (fun y => ?_) x
    · simp [t, τ]; omega
    · simp [τ, Fin.predAbove_succAbove, succAbove_low_rank q hq]
  refine ⟨?_,insert_inherits _ _ _⟩
  rintro ⟨i,j,k,l,hij,hjk,hkl,h⟩
  change max (τ i) (τ k) < min (τ j) (τ l) at h
  have ⟨hj,hl⟩ := pattern_peaks τ (hij.trans hjk) h
  rcases lt_min_iff.mp h with ⟨hj',hl'⟩
  rcases max_lt_iff.mp hj' with ⟨hij',hkj'⟩
  rcases max_lt_iff.mp hl' with ⟨hil',hkl'⟩
  have hkeep {u v : Fin (n+2)} (huv : τ u < τ v) (hv : 1 < (τ v).val) : σ (t.predAbove u) < σ (t.predAbove v) := by
    change (σ (t.predAbove u)).val < (σ (t.predAbove v)).val
    rw [hclip,hclip]; omega
  have p1 := hkeep hij' hj
  have p2 := hkeep hkj' hj
  have p3 := hkeep hil' hl
  have p4 := hkeep hkl' hl
  have ho {u v : Fin (n+2)} (h : u < v) (h' : σ (t.predAbove u) ≠ σ (t.predAbove v)) : t.predAbove u < t.predAbove v :=
    lt_of_le_of_ne (t.predAbove_right_monotone h.le) (fun he => h' (congrArg σ he))
  exact ⟨_,_,_,_,ho hij p1.ne,ho hjk p2.ne',ho hkl p4.ne,lt_min (max_lt p1 p2) (max_lt p3 p4)⟩



abbrev Avoid (n : ℕ) := {σ : Equiv.Perm (Fin n) // ¬classicalPattern σ}
abbrev Interior (n : ℕ) := {σ : Avoid (n+1) // σ.1.symm 0 ≠ Fin.last n}

def lowDigit {n : ℕ} (b : Fin 2) : Fin (n+2) := ⟨b.val,by omega⟩
lemma lowDigit_le {n : ℕ} (b : Fin 2) : (lowDigit (n:=n) b).val ≤ 1 := by change b.val ≤ 1; omega

def grow {n : ℕ} : Fin 2 × (Avoid (n+1) ⊕ Interior n) → Avoid (n+2)
  | (b, .inl s) => ⟨insertPerm (Fin.last (n+1)) (lowDigit b) s, fun h => s.2 ((append_low_iff _ (lowDigit_le _) _).mp h)⟩
  | (b, .inr s) => ⟨insertPerm (s.1.1.symm 0).castSucc (lowDigit b) s.1, fun h => s.1.2 ((duplicate_low_iff _ (lowDigit_le _) _).mp h)⟩

lemma split_low_entries {n : ℕ} (b : Fin 2) (s : Equiv.Perm (Fin (n+1))) :
    let t := s.symm 0
    let τ := insertPerm t.castSucc (lowDigit b) s
    (τ t.castSucc).val ≤ 1 ∧ (τ t.succ).val ≤ 1 := by
  dsimp only
  constructor
  · simpa using lowDigit_le (n:=n) b
  · have he := insertPerm_away (s.symm 0).castSucc (lowDigit (n:=n) b) s (s.symm 0)
    simp only [Fin.succAbove_castSucc_self, Equiv.apply_symm_apply] at he
    rw [he]
    have h := succAbove_low_rank (lowDigit (n:=n) b) (lowDigit_le _) 0
    change _ - 1 = 0 at h
    omega

lemma split_ends_high {n : ℕ} (b : Fin 2) (s : Interior n) :
    1 < ((grow (b, .inr s)).1 (Fin.last (n+1))).val := by
  let t := s.1.1.symm 0
  have he := insertPerm_away t.castSucc (lowDigit (n:=n) b) s.1.1 (Fin.last n)
  rw [Fin.succAbove_ne_last_last (Fin.castSucc_ne_last _)] at he
  change 1 < (insertPerm _ _ _ _).val
  rw [he]
  have h := succAbove_low_rank (lowDigit (n:=n) b) (lowDigit_le _) (s.1.1 (Fin.last n))
  have hne : (s.1.1 (Fin.last n)).val ≠ 0 := by
    intro h0
    exact s.2 (s.1.1.symm_apply_eq.mpr (Fin.ext h0).symm)
  omega

lemma low_pair_location {n : ℕ} (τ : Equiv.Perm (Fin (n+2))) (p : Fin (n+1))
    (h0 : (τ p.castSucc).val ≤ 1) (h1 : (τ p.succ).val ≤ 1) :
    min (τ.symm 0).val (τ.symm 1).val = p.val := by
  have hne : (τ p.castSucc).val ≠ (τ p.succ).val := fun he => (show p.castSucc < p.succ from Fin.castSucc_lt_succ).ne (τ.injective (Fin.ext he))
  have hpair : (τ p.castSucc = 0 ∧ τ p.succ = 1) ∨ (τ p.castSucc = 1 ∧ τ p.succ = 0) := by
    have h1v : (1:Fin (n+2)).val = 1 := by simp
    by_cases hh : (τ p.castSucc).val = 0
    · left; exact ⟨Fin.ext hh, Fin.ext (by omega)⟩
    · right; exact ⟨Fin.ext (by omega), Fin.ext (by change _ = 0; omega)⟩
  rcases hpair with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · rw [τ.symm_apply_eq.mpr ha.symm,τ.symm_apply_eq.mpr hb.symm]; simp
  · rw [τ.symm_apply_eq.mpr hb.symm,τ.symm_apply_eq.mpr ha.symm]; simp

lemma grow_injective (n : ℕ) : Function.Injective (@grow n) := by
  rintro ⟨b, s|s⟩ ⟨b', s'|s'⟩ he
  · have h := congrArg Subtype.val he
    change insertPerm _ _ _ = insertPerm _ _ _ at h
    have hb := DFunLike.congr_fun h (Fin.last (n+1))
    simp only [insertPerm_at] at hb
    have hbb : b = b' := Fin.ext (congrArg (fun z : Fin (n+2) => z.val) hb)
    subst b'
    have hs := insertPerm_inj _ _ h
    cases Subtype.ext hs
    rfl
  · have h := congrArg (fun z : Avoid (n+2) => (z.1 (Fin.last (n+1))).val) he
    change (insertPerm _ _ _ _).val = _ at h
    rw [insertPerm_at] at h
    exact False.elim ((not_lt_of_ge (lowDigit_le b)) (h ▸ split_ends_high b' s'))
  · have h := congrArg (fun z : Avoid (n+2) => (z.1 (Fin.last (n+1))).val) he.symm
    change (insertPerm _ _ _ _).val = _ at h
    rw [insertPerm_at] at h
    exact False.elim ((not_lt_of_ge (lowDigit_le b')) (h ▸ split_ends_high b s))
  · have h := congrArg Subtype.val he
    change insertPerm _ _ _ = insertPerm _ _ _ at h
    have hL := split_low_entries b s.1.1
    have hR := split_low_entries b' s'.1.1
    have heL := low_pair_location _ _ hL.1 hL.2
    have heR := low_pair_location _ _ hR.1 hR.2
    rw [h] at heL
    have ht : s.1.1.symm 0 = s'.1.1.symm 0 := Fin.ext (heL.symm.trans heR)
    rw [ht] at h
    have hq := DFunLike.congr_fun h (s'.1.1.symm 0).castSucc
    simp only [insertPerm_at] at hq
    have hbb : b = b' := Fin.ext (congrArg (fun z : Fin (n+2) => z.val) hq)
    subst b'
    have hs := insertPerm_inj _ _ h
    cases Subtype.ext (Subtype.ext hs : s.1 = s'.1)
    rfl



lemma remove_avoids {n : ℕ} (p : Fin (n+1)) (τ : Avoid (n+1)) : ¬classicalPattern (removePerm p τ.1) := by
  intro h
  have he := insert_inherits p (τ.1 p) _ h
  rw [reinsert_remove] at he
  exact τ.2 he

lemma grow_of_adjacent {n : ℕ} (s : Avoid (n+2)) (t : Fin (n+1)) (ht : t ≠ Fin.last n)
    (hu : (s.1 t.castSucc).val ≤ 1) (hv : (s.1 t.succ).val ≤ 1) :
    ∃ a, grow a = s := by
  let p := t.castSucc
  let σ : Avoid (n+1) := ⟨removePerm p s.1, remove_avoids p s⟩
  have hd : (s.1 p).succAbove (σ.1 t) = s.1 t.succ := by
    simpa [σ,p] using removePerm_spec t.castSucc s.1 t
  have hr := succAbove_low_rank (s.1 p) hu (σ.1 t)
  rw [hd] at hr
  have hz : σ.1 t = 0 := Fin.ext (by change (σ.1 t).val = 0; omega)
  have hpos : σ.1.symm 0 = t := σ.1.symm_apply_eq.mpr hz.symm
  let b : Fin 2 := ⟨(s.1 p).val, by change (s.1 t.castSucc).val < 2; omega⟩
  have hq : lowDigit (n:=n) b = s.1 p := Fin.ext rfl
  refine ⟨(b, .inr ⟨σ, hpos ▸ ht⟩), Subtype.ext ?_⟩
  change insertPerm (σ.1.symm 0).castSucc (lowDigit b) σ.1 = s.1
  rw [hpos,hq]
  exact reinsert_remove p s.1

lemma grow_surjective (n : ℕ) : Function.Surjective (@grow n) := by
  intro s
  let e := Fin.last (n+1)
  by_cases htail : (s.1 e).val ≤ 1
  · let b : Fin 2 := ⟨(s.1 e).val, by omega⟩
    refine ⟨(b, .inl ⟨removePerm e s.1, remove_avoids e s⟩), Subtype.ext ?_⟩
    exact reinsert_remove e s.1
  · have hpositions (u v : Fin (n+2)) (huv : u < v) (hu : (s.1 u).val ≤ 1) (hv : (s.1 v).val ≤ 1) :
        ∃ a, grow a = s := by
      have hvne : v ≠ e := fun he => htail (he ▸ hv)
      have hstep := (pair_adjacent_or_last s.1 s.2 u v huv hu hv).resolve_right hvne
      have he : u.val < n+1 := by omega
      let t : Fin (n+1) := ⟨u.val, he⟩
      have ht1 : t.castSucc = u := Fin.ext rfl
      have ht2 : t.succ = v := Fin.ext hstep.symm
      have ht : t ≠ Fin.last n := by intro h; rw [← ht2,h,Fin.succ_last] at hvne; exact hvne rfl
      exact grow_of_adjacent s t ht (ht1 ▸ hu) (ht2 ▸ hv)
    have h01 : (0:Fin (n+2)) ≠ 1 := by intro h; have := congrArg Fin.val h; simp at this
    have hne : s.1.symm 0 ≠ s.1.symm 1 := s.1.symm.injective.ne h01
    rcases lt_or_gt_of_ne hne with h | h
    · exact hpositions _ _ h (by simp) (by simp)
    · exact hpositions _ _ h (by simp) (by simp)



abbrev EndsMin (n : ℕ) := {s : Avoid (n+1) // s.1.symm 0 = Fin.last n}

def appendMin {n : ℕ} (s : Avoid n) : EndsMin n :=
  ⟨⟨insertPerm (Fin.last n) 0 s.1, fun h => s.2 ((append_low_iff _ (by simp) _).mp h)⟩,
   (insertPerm (Fin.last n) 0 s.1).symm_apply_eq.mpr (by simp)⟩

lemma appendMin_bijective (n : ℕ) : Function.Bijective (@appendMin n) := by
  constructor
  · intro s t he
    exact Subtype.ext (insertPerm_inj (Fin.last n) 0 (congrArg (fun z : EndsMin n => z.1.1) he))
  · rintro ⟨s,hs⟩
    have hz : s.1 (Fin.last n) = 0 := (s.1.symm_apply_eq.mp hs).symm
    refine ⟨⟨_,remove_avoids (Fin.last n) s⟩, Subtype.ext (Subtype.ext ?_)⟩
    change insertPerm _ 0 _ = s.1
    rw [← hz]
    exact reinsert_remove _ _

lemma avoid_count_recurrence (n : ℕ) :
    (Nat.card (Avoid (n+2)):ℤ) = 4*(Nat.card (Avoid (n+1)):ℤ) - 2*(Nat.card (Avoid n):ℤ) := by
  classical
  have h1 := Nat.card_congr (Equiv.ofBijective (@grow n) ⟨grow_injective n,grow_surjective n⟩)
  rw [Nat.card_prod, Nat.card_fin,Nat.card_sum] at h1
  have h2 := Nat.card_congr (Equiv.sumCompl (fun s : Avoid (n+1) => s.1.symm 0 = Fin.last n))
  change Nat.card (EndsMin n ⊕ Interior n) = _ at h2
  rw [Nat.card_sum, ← Nat.card_congr (Equiv.ofBijective _ (appendMin_bijective n))] at h2
  omega

lemma avoid_card_small (n : ℕ) (hn : n ≤ 3) : Nat.card (Avoid n) = n.factorial := by
  have no : ∀ s : Equiv.Perm (Fin n), ¬classicalPattern s := by
    rintro s ⟨i,j,k,l,hij,hjk,hkl,_⟩
    omega
  rw [Nat.card_congr (Equiv.subtypeUnivEquiv no),Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin]

lemma avoid_count_exact : ∀ n : ℕ, (Nat.card (Avoid (n+1)):ℤ) = S_oeis_a006012.a n
  | 0 => by rw [avoid_card_small 1 (by decide)]; rfl
  | 1 => by rw [avoid_card_small 2 (by decide)]; rfl
  | n+2 => by rw [avoid_count_recurrence (n+1), avoid_count_exact (n+1), avoid_count_exact n]; rfl

end OMA

open OMA

theorem OMA.solution : type_of% @OMA.S_oeis_a006012.main := by
  intro n
  have he := Equiv.subtypeEquivRight (fun σ : Equiv.Perm (Fin (n+1)) => not_congr (contains_iff_classical σ))
  rw [Nat.card_congr he]
  exact avoid_count_exact n

