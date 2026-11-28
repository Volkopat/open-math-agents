import OMAStatements.S_mo_275692
namespace OMA.S_mo_275692
open List Finset
private lemma run_cons {n} (p : G n) (k : Fin n) (l : List (Fin n)) :
    run p (k::l) = run (step p k) l := rfl
private lemma run_label {n} (p τ : G n) (l : List (Fin n)) :
    run (p.trans τ) l = (run p l).trans τ := by
  induction l generalizing p with
  | nil => rfl
  | cons k l ih => exact ih (step p k)

private lemma cross_pos {n} (k : Fin n) (i j : Fin (n+1)) (h : i<j)
    (hf : ¬ Equiv.swap k.castSucc k.succ i < Equiv.swap k.castSucc k.succ j) :
    i=k.castSucc ∧ j=k.succ := by
  have hki : k.castSucc.val=k.val := rfl
  have hkj : k.succ.val=k.val+1 := rfl
  simp only [Equiv.swap_apply_def] at hf
  split_ifs at hf <;> simp_all only [Fin.ext_iff,Fin.lt_def,Fin.val_castSucc,Fin.val_succ] <;> first | trivial | omega

private lemma uncross {n : ℕ} (a b : Fin (n+1)) (p : G n) (l : List (Fin n))
    (hs : p.symm a < p.symm b) (he : (run p l).symm b < (run p l).symm a) :
    ∃ m : List (Fin n), m.Sublist l ∧ run p m = (run p l).trans (Equiv.swap a b) := by
  induction l generalizing p with
  | nil => simp [run] at he;exact False.elim (hs.not_gt he)
  | cons k l ih =>
    by_cases h : (step p k).symm a < (step p k).symm b
    · obtain ⟨m,hm,hm'⟩ := ih (step p k) h he
      exact ⟨k::m,hm.cons_cons k,hm'⟩
    · change ¬ Equiv.swap k.castSucc k.succ (p.symm a) < Equiv.swap k.castSucc k.succ (p.symm b) at h
      obtain ⟨hi,hj⟩ := cross_pos k _ _ hs h
      have ha : p k.castSucc=a := by rw [← hi,p.apply_symm_apply]
      have hb : p k.succ=b := by rw [← hj,p.apply_symm_apply]
      have hstep : p=(step p k).trans (Equiv.swap a b) := by
        apply Equiv.ext
        intro j
        change p j = Equiv.swap a b (p (Equiv.swap k.castSucc k.succ j))
        rw [← ha,← hb,p.injective.swap_apply,Equiv.swap_apply_self]
      refine ⟨l,(Sublist.refl _).cons k,?_⟩
      rw [run_cons,← run_label,← hstep]

private def height {n : ℕ} (p : G n) : ℕ := ∑ i : Fin (n+1), i.val*(p i).val

private lemma height_step {n : ℕ} (p : G n) (k : Fin n) (ha : p k.castSucc < p k.succ) :
    height (step p k) < height p := by
  let x := k.castSucc
  let y := k.succ
  have hxy : x ≠ y := Fin.ne_of_val_ne (by dsimp [x,y];omega)
  let rest := (univ.erase x).erase y
  have sum_two (f : Fin (n+1) → ℕ) : ∑ i, f i = f x+f y+∑ i ∈ rest, f i := by
    have h1 := add_sum_erase univ f (mem_univ x)
    have h2 := add_sum_erase (univ.erase x) f (mem_erase.mpr ⟨hxy.symm,mem_univ y⟩)
    dsimp [rest];omega
  have hr : ∑ i ∈ rest, i.val*((step p k) i).val = ∑ i ∈ rest, i.val*(p i).val := by
    apply sum_congr rfl
    intro i hi
    obtain ⟨hiy,hix⟩ := mem_erase.mp hi
    change _* (p (Equiv.swap x y i)).val = _
    rw [Equiv.swap_apply_of_ne_of_ne (mem_erase.mp hix).1 hiy]
  unfold height
  rw [sum_two,sum_two (fun i => i.val*(p i).val),hr]
  dsimp [step,x,y]
  simp only [Equiv.swap_apply_left,Equiv.swap_apply_right]
  have hp : (p k.castSucc).val < (p k.succ).val := ha
  nlinarith

private lemma ascend_or_rev {n : ℕ} (p : G n) :
    (∃ i : Fin n, p i.castSucc < p i.succ) ∨ p=Fin.revPerm := by
  by_cases h : ∃ i : Fin n, p i.castSucc < p i.succ
  · exact Or.inl h
  right
  have anti : StrictAnti p := Fin.strictAnti_iff_succ_lt.mpr fun i =>
    lt_of_le_of_ne (le_of_not_gt (fun hi => h ⟨i,hi⟩))
      (p.injective.ne (Fin.ne_of_val_ne (by simp)))
  have hmono := Fin.rev_strictAnti.comp anti
  apply Equiv.ext
  intro i
  have hi : Fin.rev (p i)=i := hmono.apply_eq
  simpa using congrArg Fin.rev hi

private lemma rev_reachable {n : ℕ} (p : G n) : ∃ l : List (Fin n),run p l=Fin.revPerm := by
  rcases ascend_or_rev p with ⟨k,hk⟩|hp
  · obtain ⟨l,hl⟩ := rev_reachable (step p k)
    exact ⟨k::l,hl⟩
  · exact ⟨[],hp⟩
termination_by height p
decreasing_by exact height_step p k hk

private lemma subword_rev {n : ℕ} (l : List (Fin n))
    (hl : run (Equiv.refl _) l=Fin.revPerm) (p : G n) :
    ∃ w : List (Fin n), w.Sublist l ∧ run (Equiv.refl _) w = p := by
  rcases ascend_or_rev p with ⟨k,hk⟩|hp
  · obtain ⟨w,hw,he⟩ := subword_rev l hl (step p k)
    let a := p k.castSucc
    let b := p k.succ
    have hpos : (run (Equiv.refl _) w).symm b < (run (Equiv.refl _) w).symm a := by
      rw [he]
      simp [a,b,step]
    obtain ⟨t,ht,te⟩ := uncross a b (Equiv.refl _) w hk hpos
    refine ⟨t,ht.trans hw,?_⟩
    rw [te,he]
    apply Equiv.ext
    intro j
    change Equiv.swap (p k.castSucc) (p k.succ) (p (Equiv.swap k.castSucc k.succ j)) = p j
    rw [p.injective.swap_apply,Equiv.swap_apply_self]
  · exact ⟨l,Sublist.refl _,hl.trans hp.symm⟩
termination_by height p
decreasing_by exact height_step p k hk

private lemma any_pair {n : ℕ} (l : List (Fin n)) (hl : run (Equiv.refl _) l=Fin.revPerm)
    (p q : G n) : ∃ t : List (Fin n), t.Sublist l ∧ run p t=q := by
  obtain ⟨t,ht,he⟩ := subword_rev l hl (q.trans p.symm)
  refine ⟨t,ht,?_⟩
  have h := run_label (Equiv.refl _) p t
  simpa [Equiv.trans_assoc,he] using h

private def states {n : ℕ} (p : G n) : List (Fin n) → List (G n)
  | [] => [p]
  | k::l => p::states (step p k) l
private lemma length_states {n : ℕ} (p : G n) (l : List (Fin n)) :
    (states p l).length=l.length+1 := by
  induction l generalizing p with
  | nil => rfl
  | cons k l ih => simp [states,ih]

private lemma suffix_states {n : ℕ} (p x : G n) (l : List (Fin n)) (hx : x ∈ states p l) :
    ∃ t : List (Fin n), t.Sublist l ∧ run x t=run p l ∧ (states x t).Sublist (states p l) := by
  induction l generalizing p with
  | nil =>
    have he : x=p := by simpa [states] using hx
    subst x
    exact ⟨[],Sublist.refl _,rfl,Sublist.refl _⟩
  | cons k l ih =>
    rcases List.mem_cons.mp hx with rfl|ht
    · exact ⟨_,Sublist.refl _,rfl,Sublist.refl _⟩
    · obtain ⟨t,hl,he,hs⟩ := ih (step p k) ht
      exact ⟨t,hl.cons k,he,hs.cons p⟩

private lemma simple_subword {n : ℕ} (p : G n) (l : List (Fin n)) :
    ∃ t : List (Fin n), t.Sublist l ∧ run p t=run p l ∧ (states p t).Nodup := by
  induction l generalizing p with
  | nil => exact ⟨[],Sublist.refl _,rfl,by simp [states]⟩
  | cons k l ih =>
    obtain ⟨t,ht,he,hs⟩ := ih (step p k)
    by_cases hp : p ∈ states (step p k) t
    · obtain ⟨u,hu,hu',hsu⟩ := suffix_states (step p k) p t hp
      exact ⟨u,(hu.trans ht).cons k,hu'.trans he,hsu.nodup hs⟩
    · exact ⟨k::t,ht.cons_cons k, he,List.nodup_cons.mpr ⟨hp,hs⟩⟩

private lemma shorter {n : ℕ} (p : G n) (l : List (Fin n)) :
    ∃ t : List (Fin n), t.Sublist l ∧ run p t=run p l ∧ t.length < (n+1).factorial := by
  obtain ⟨t,ht,he,hs⟩ := simple_subword p l
  have hb := hs.length_le_card
  rw [length_states] at hb
  exact ⟨t,ht,he,by simpa [G,Fintype.card_perm] using hb⟩

private lemma cost_le {n : ℕ} (w : Fin n → ℝ) (hw : ∀ j, 0 ≤ w j) {u l : List (Fin n)}
    (hl : u.Sublist l) : cost w u ≤ cost w l := by
  induction hl with
  | slnil => exact le_rfl
  | cons a _ ih => simpa [cost] using (le_add_of_nonneg_left (hw a) : cost w _ ≤ w a+cost w _ ) |>.trans' ih
  | cons_cons a _ ih => simpa [cost] using add_le_add_left ih (w a)

private lemma min_word {n : ℕ} (w : Fin n → ℝ) (hw : ∀ j, 0 ≤ w j) (p q : G n)
    (reach : ∃ l,run p l=q) :
    ∃ l : List (Fin n), l.length < (n+1).factorial ∧ run p l=q ∧ IsLeast (costs w p q) (cost w l) := by
  classical
  let C : Set (List (Fin n)) := {l | l.length < (n+1).factorial ∧ run p l=q}
  have hf : C.Finite := (List.finite_length_lt (Fin n) _).subset fun _ h => h.1
  obtain ⟨u,hu⟩ := reach
  obtain ⟨t,_,he,ht⟩ := shorter p u
  obtain ⟨l,hl,hmin⟩ := Set.exists_min_image C (cost w) hf ⟨t,ht,he.trans hu⟩
  refine ⟨l,hl.1,hl.2,⟨⟨l,hl.2,rfl⟩,?_⟩⟩
  rintro _ ⟨v,hv,rfl⟩
  obtain ⟨v',hsub,hv',hlen⟩ := shorter p v
  exact (hmin v' ⟨hlen,hv'.trans hv⟩).trans (cost_le w hw hsub)

private lemma diameter (n : ℕ) (w : Fin n → ℝ) (hw : ∀ j,0 ≤ w j) :
    IsGreatest {d : ℝ | ∃ p q : G n, distance w p q=d}
      (distance w (Equiv.refl _) Fin.revPerm) ∧
      ∃ l : List (Fin n), l.length < (n+1).factorial ∧ run (Equiv.refl _) l=Fin.revPerm ∧
        IsLeast (costs w (Equiv.refl _) Fin.revPerm) (cost w l) := by
  obtain ⟨l,hlen,hl,hmin⟩ := min_word w hw (Equiv.refl _) Fin.revPerm (rev_reachable _)
  refine ⟨⟨⟨_,_,rfl⟩,?_⟩,l,hlen,hl,hmin⟩
  rintro _ ⟨p,q,rfl⟩
  obtain ⟨t,ht,hq⟩ := any_pair l hl p q
  obtain ⟨u,_,_,hu⟩ := min_word w hw p q ⟨t,hq⟩
  unfold distance
  rw [hu.csInf_eq,hmin.csInf_eq]
  exact (hu.2 ⟨t,hq,rfl⟩).trans (cost_le w hw ht)

private def increasing {n : ℕ} (p : G n) : List (Fin n) → Prop
  | [] => True
  | k::l => p k.castSucc < p k.succ ∧ increasing (step p k) l

private lemma run_append {n} (p : G n) (a b : List (Fin n)) :
    run p (a++b)=run (run p a) b := by
  induction a generalizing p with
  | nil => rfl
  | cons k a ih => exact ih (step p k)
private lemma increasing_snoc {n} (p : G n) (l : List (Fin n)) (k : Fin n)
    (h : increasing p l) (hk : run p l k.castSucc < run p l k.succ) :
    increasing p (l++[k]) := by
  induction l generalizing p with
  | nil => exact ⟨hk,True.intro⟩
  | cons a l ih => exact ⟨h.1,ih (step p a) h.2 hk⟩

private lemma normalize_word {n : ℕ} (l : List (Fin n)) :
    ∃ u : List (Fin n), u.Sublist l ∧ run (Equiv.refl _) u=run (Equiv.refl _) l ∧
      increasing (Equiv.refl _) u := by
  classical
  cases h : l.reverse with
  | nil =>
    have he : l=[] := List.reverse_eq_nil_iff.mp h
    subst l
    exact ⟨[],Sublist.refl _,rfl,trivial⟩
  | cons k r =>
    let v := r.reverse
    have heq : l=v++[k] := by simpa [v] using congrArg List.reverse h
    let p := run (Equiv.refl _) v
    have hp : run (Equiv.refl _) l=step p k := by rw [heq,run_append];rfl
    by_cases ha : p k.castSucc < p k.succ
    · obtain ⟨u,hu,hend,hir⟩ := normalize_word v
      refine ⟨u++[k],heq ▸ hu.append_right _,?_,increasing_snoc _ _ _ hir (hend ▸ ha)⟩
      rw [run_append,hend,hp];rfl
    · have hlt : p k.succ < p k.castSucc := lt_of_le_of_ne (le_of_not_gt ha)
        (p.injective.ne (Fin.ne_of_val_ne (by simp)))
      have hpos : p.symm (p k.castSucc) < p.symm (p k.succ) := by simp
      obtain ⟨t,ht,hte⟩ := uncross (p k.succ) (p k.castSucc) (Equiv.refl _) v hlt hpos
      obtain ⟨u,hu,hend,hir⟩ := normalize_word t
      refine ⟨u,heq ▸ (hu.trans ht).trans (List.sublist_append_left _ _),?_,hir⟩
      rw [hend,hte,hp]
      apply Equiv.ext
      intro j
      change Equiv.swap (p k.succ) (p k.castSucc) (p j)=p (Equiv.swap k.castSucc k.succ j)
      rw [p.injective.swap_apply,Equiv.swap_comm k.succ k.castSucc]
termination_by l.length
decreasing_by
  all_goals rw [heq,List.length_append,List.length_singleton]
  · exact Nat.lt_succ_self _
  · have := ht.length_le;omega

private def inversions {n : ℕ} (p : G n) :=
  (univ : Finset (Fin (n+1) × Fin (n+1))).filter (fun ab => ab.1<ab.2 ∧ p.symm ab.2 < p.symm ab.1)

private lemma flips {n : ℕ} (p : G n) (k : Fin n) {a b : Fin (n+1)}
    (h : p.symm a < p.symm b) (h' : ¬ (step p k).symm a < (step p k).symm b) :
    a=p k.castSucc ∧ b=p k.succ := by
  obtain ⟨ha,hb⟩ := cross_pos k _ _ h h'
  exact ⟨by rw [← ha,p.apply_symm_apply],by rw [← hb,p.apply_symm_apply]⟩

private lemma inv_advance {n : ℕ} (p : G n) (k : Fin n) (h : p k.castSucc < p k.succ) :
    (inversions (step p k)).card=(inversions p).card+1 := by
  classical
  let u := p k.castSucc
  let v := p k.succ
  have huv : (u,v) ∉ inversions p := by simp [u,v,inversions,Fin.le_def]
  have he : inversions (step p k)=insert (u,v) (inversions p) := by
    ext ⟨a,b⟩
    simp only [inversions,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert,Prod.mk.injEq]
    constructor
    · rintro ⟨hab,hab'⟩
      by_cases hold : p.symm b < p.symm a
      · exact Or.inr ⟨hab,hold⟩
      · apply Or.inl
        exact flips p k (lt_of_le_of_ne (le_of_not_gt hold) (p.symm.injective.ne hab.ne)) hab'.not_gt
    · rintro (⟨rfl,rfl⟩|⟨hab,hold⟩)
      · exact ⟨h,by simp [step,u,v]⟩
      · refine ⟨hab,?_⟩
        by_contra hn
        obtain ⟨hb,ha⟩ := flips p k hold hn
        rw [hb,ha] at hab
        exact h.not_gt hab
  rw [he,card_insert_of_notMem huv]

private lemma count_increasing {n : ℕ} (p : G n) (l : List (Fin n)) (h : increasing p l) :
    (inversions (run p l)).card=(inversions p).card+l.length := by
  induction l generalizing p with
  | nil => simp [run]
  | cons k l ih =>
    rw [run_cons,ih _ h.2,inv_advance _ _ h.1,List.length_cons]
    omega

private lemma inv_rev (n : ℕ) : (inversions (Fin.revPerm : G n)).card=(n+1).choose 2 := by
  have h : (inversions (Fin.revPerm : G n)).card =
      ∑ b : Fin (n+1), ∑ a : Fin (n+1), if a<b then (1:ℕ) else 0 := by
    unfold inversions
    rw [Finset.card_eq_sum_ones,Finset.sum_filter,Fintype.sum_prod_type,Finset.sum_comm]
    simp [Fin.revPerm,Fin.rev_lt_rev]
  rw [h]
  have hj (b : Fin (n+1)) : (∑ a : Fin (n+1), if a<b then (1:ℕ) else 0)=b.val := by
    rw [sum_boole]
    rw [show (univ.filter fun a : Fin (n+1) => a<b) = Finset.Iio b by ext a;simp]
    simp
  simp_rw [hj]
  have hh (m : ℕ) : (∑ i ∈ range m, i)=m.choose 2 := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ,ih,Nat.choose_succ_succ]
      simp [add_comm]
  exact (Fin.sum_univ_eq_sum_range (fun i : ℕ => i) (n+1)).trans (hh _)

private lemma exact_diameter (n : ℕ) (w : Fin n → ℝ) (hw : ∀ j,0 ≤ w j) :
    IsGreatest {d : ℝ | ∃ p q : G n, distance w p q=d} (distance w (Equiv.refl _) Fin.revPerm) ∧
    ∃ l : List (Fin n), l.length=(n+1).choose 2 ∧ run (Equiv.refl _) l=Fin.revPerm ∧
      IsLeast (costs w (Equiv.refl _) Fin.revPerm) (cost w l) := by
  obtain ⟨hd,l,_,hl,hm⟩ := diameter n w hw
  obtain ⟨t,ht,he,hir⟩ := normalize_word l
  have hfin := he.trans hl
  have hcount := count_increasing (Equiv.refl _) t hir
  have hid : inversions (Equiv.refl _ : G n)=∅ := by
    ext ⟨a,b⟩
    constructor
    · intro hm
      obtain ⟨_,hab,hba⟩ := Finset.mem_filter.mp hm
      exact False.elim (hab.not_gt hba)
    · simp
  rw [hfin,inv_rev,hid,card_empty,zero_add] at hcount
  refine ⟨hd,t,hcount.symm,hfin,⟨⟨t,hfin,rfl⟩,?_⟩⟩
  intro v hv
  exact (cost_le w hw ht).trans (hm.2 hv)

private def wt3 (i : Fin 2) : ℕ := if i=0 then 2 else 1
private lemma check3 : ∀ (t : Fin 6) (u : Fin t.val → Fin 2),
    run (Equiv.refl _) (List.ofFn u)=Fin.revPerm → 4 ≤ ((List.ofFn u).map wt3).sum := by decide
private lemma cast_cost3 (l : List (Fin 2)) :
    cost (![2,1] : Fin 2 → ℝ) l = ((l.map wt3).sum : ℕ) := by
  induction l with
  | nil => simp [cost]
  | cons i l ih =>
    have hw : (![2,1] : Fin 2 → ℝ) i=(wt3 i : ℕ) := by fin_cases i <;> norm_num [wt3]
    simp [cost] at ih ⊢
    rw [hw,ih]

private lemma three : distance (![2,1] : Fin 2 → ℝ) (Equiv.refl _) Fin.revPerm=4 := by
  let w : Fin 2 → ℝ := ![2,1]
  have hw (j : Fin 2) : 0 ≤ w j := by fin_cases j <;> norm_num [w]
  obtain ⟨l,hl,he,hm⟩ := (diameter 2 w hw).2
  change sInf (costs w (Equiv.refl _) Fin.revPerm)=4
  rw [hm.csInf_eq]
  apply le_antisymm
  · have hrun : run (Equiv.refl _) ([1,0,1] : List (Fin 2))=Fin.revPerm := by decide
    have hc : cost w [1,0,1]=4 := by norm_num [w,cost]
    exact hm.2 ⟨_,hrun,hc⟩
  · have hlen : l.length < 6 := by norm_num [Nat.factorial] at hl;exact hl
    have hb := check3 ⟨l.length,hlen⟩ l.get
    simp only [List.ofFn_get] at hb
    rw [show w=(![2,1] : Fin 2→ℝ) from rfl,cast_cost3]
    exact_mod_cast hb he

end OMA.S_mo_275692
open OMA.S_mo_275692
theorem OMA.solution : type_of% @OMA.S_mo_275692.main := ⟨exact_diameter,three⟩
