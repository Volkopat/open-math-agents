import OMAStatements.S_mo_365616

/-!
Consider the left and right combs L and R on the same long word of distinct
letters. The identity L*R = R*L holds by either commutativity or associativity.
For any proposed finite basis we construct a magma that separates its two sides.

In the free magma, keep the subterms of L*R distinct and identify all other
terms with a single absorbing element. A common identity preserves both the
word of variables and the binary tree up to exchanges of children. A proper
subterm of L*R has distinct letters, so its tree and word determine it uniquely.
At the root, exchanging the children in a short identity would force every
substituted variable from the left side to occur also on the right. Distinct
combs share only letters as subterms, so such an identity must contain at
least as many variable occurrences as the entire word. Choosing a longer
word than any basis identity gives the contradiction.

The two different bracketings extend the three-variable example in bof's
Math Stack Exchange answer to question 3754837.
-/

open OMA.S_mo_365616

namespace CombIdentities

open Term
private def word : Term → List ℕ
  | var i => [i]
  | mul a b => word a ++ word b
private lemma nonempty_word (a : Term) : word a ≠ [] := by
  induction a <;> simp_all [word]
private def sub (v : ℕ → Term) (a : Term) := a.eval mul v
private lemma word_sub (v : ℕ → Term) (a : Term) : word (sub v a) = (word a).flatMap (word ∘ v) := by
  induction a <;> simp_all [word,sub,Term.eval]
private theorem word_id {a b : Term} (h : CommonIdentity (a,b)) : word a=word b := by
  have E (t : Term) : t.eval List.append (fun i => [i])=word t := by induction t <;> simp_all [word,Term.eval]
  simpa only [E] using h (List ℕ) List.append (Or.inr ⟨List.append_assoc⟩) (fun i => [i])

private inductive Flip : Term → Term → Prop
  | leaf (i : ℕ) : Flip (var i) (var i)
  | node {a b c d} : Flip a c → Flip b d → Flip (mul a b) (mul c d)
  | swap {a b c d} : Flip a d → Flip b c → Flip (mul a b) (mul c d)

private lemma Flip.refl (a : Term) : Flip a a := by induction a with
  | var i => exact .leaf i
  | mul a b ha hb => exact .node ha hb
private lemma Flip.symm {a b} (h : Flip a b) : Flip b a := by induction h with
  | leaf i => exact .leaf i
  | node _ _ h₁ h₂ => exact .node h₁ h₂
  | swap _ _ h₁ h₂ => exact .swap h₂ h₁
private lemma Flip.trans {a b c} (h : Flip a b) (h' : Flip b c) : Flip a c := by
  induction h generalizing c with
  | leaf i => exact h'
  | node _ _ ih₁ ih₂ =>
    cases h' with
    | node h₁ h₂ => exact .node (ih₁ h₁) (ih₂ h₂)
    | swap h₁ h₂ => exact .swap (ih₁ h₁) (ih₂ h₂)
  | swap _ _ ih₁ ih₂ =>
    cases h' with
    | node h₁ h₂ => exact .swap (ih₁ h₂) (ih₂ h₁)
    | swap h₁ h₂ => exact .node (ih₁ h₂) (ih₂ h₁)

private def flipSetoid : Setoid Term := ⟨Flip,⟨Flip.refl,Flip.symm,Flip.trans⟩⟩
private abbrev CommTree := Quotient flipSetoid
private def mkC (t : Term) : CommTree := Quotient.mk flipSetoid t
private def joinC : CommTree → CommTree → CommTree :=
  Quotient.map₂ mul fun _ _ h _ _ h' => Flip.node h h'
private lemma flip_id {a b : Term} (h : CommonIdentity (a,b)) : Flip a b := by
  have comm : Std.Commutative joinC := ⟨by
    intro a b
    induction a using Quotient.inductionOn with | _ a =>
      induction b using Quotient.inductionOn with | _ b =>
        exact Quotient.sound (Flip.swap (Flip.refl a) (Flip.refl b))⟩
  have E (t : Term) : t.eval joinC (fun i => mkC (var i))=mkC t := by
    induction t <;> simp_all [Term.eval,joinC,mkC]
    rfl
  have H := h CommTree joinC (Or.inl comm) (fun i => mkC (var i))
  change a.eval joinC (fun i => mkC (var i))=b.eval joinC (fun i => mkC (var i)) at H
  rw [E,E] at H
  exact Quotient.exact (s := flipSetoid) H

private lemma Flip.perm {a b} (h : Flip a b) : (word a).Perm (word b) := by
  induction h with
  | leaf => rfl
  | node _ _ ha hb => exact ha.append hb
  | swap _ _ ha hb => exact (ha.append hb).trans List.perm_append_comm

private lemma Flip.subst {a b} (h : Flip a b) (v : ℕ → Term) : Flip (sub v a) (sub v b) := by
  induction h with
  | leaf => exact .refl _
  | node _ _ ha hb => exact .node ha hb
  | swap _ _ ha hb => exact .swap ha hb

private lemma split_eq {α : Type} {a b c d : List α} (he : a++b=c++d) (hl : a.length=c.length) :
    a=c ∧ b=d := by
  have h := congrArg (List.take a.length) he
  have h' := congrArg (List.drop a.length) he
  rw [List.take_left,hl,List.take_left] at h
  rw [List.drop_left,hl,List.drop_left] at h'
  exact ⟨h,h'⟩

private lemma rigid {a b : Term} (hf : Flip a b) (hw : word a=word b) (hn : (word a).Nodup) : a=b := by
  induction hf with
  | leaf => rfl
  | node h₁ h₂ ih₁ ih₂ =>
    obtain ⟨hl,hr⟩ := split_eq hw h₁.perm.length_eq
    obtain ⟨n₁,n₂,_⟩ := List.nodup_append.1 hn
    rw [ih₁ hl n₁,ih₂ hr n₂]
  | @swap a b c d h₁ h₂ ih₁ ih₂ =>
    have disj := (List.nodup_append.1 hn).2.2
    have ha := nonempty_word a
    have hc := nonempty_word c
    obtain ⟨i,is,hi⟩ := List.exists_cons_of_ne_nil ha
    obtain ⟨j,js,hj⟩ := List.exists_cons_of_ne_nil hc
    have he : i=j := by simpa [word,hi,hj] using congrArg List.head? hw
    have hb : i ∈ word b := h₂.perm.mem_iff.2 (by simp [hj,he])
    exact False.elim (disj i (by simp [hi] : i ∈ word a) i hb rfl)



private inductive Part (p : Term) : Term → Prop
  | self : Part p p
  | left {a b} : Part p a → Part p (mul a b)
  | right {a b} : Part p b → Part p (mul a b)

private lemma Part.down {p q t} (h : Part p q) (h' : Part q t) : Part p t := by
  induction h' with
  | self => exact h
  | left _ ih => exact .left ih
  | right _ ih => exact .right ih

private lemma Part.nodup {p q} (h : Part p q) (hn : (word q).Nodup) : (word p).Nodup := by
  induction h with
  | self => exact hn
  | left _ ih => exact ih (List.nodup_append.1 hn).1
  | right _ ih => exact ih (List.nodup_append.1 hn).2.1

private lemma part_var {i t} (v : ℕ → Term) (hi : i ∈ word t) : Part (v i) (sub v t) := by
  induction t with
  | var j =>
    obtain rfl : i=j := by simpa [word] using hi
    exact .self
  | mul a b ha hb =>
    rcases List.mem_append.1 hi with h | h
    · exact .left (ha h)
    · exact .right (hb h)

private def leftC : ℕ → Term
  | 0 => var 0
  | n+1 => mul (leftC n) (var (n+1))
private def rightC (i : ℕ) : ℕ → Term
  | 0 => var i
  | n+1 => mul (var i) (rightC (i+1) n)
private def test (n : ℕ) := mul (leftC n) (rightC 0 n)

private lemma left_word (n : ℕ) : word (leftC n)=List.range (n+1) := by
  induction n with
  | zero => rfl
  | succ n ih => change word (leftC n)++[n+1]=_
                 rw [ih, List.range_succ (n := n+1)]
private lemma right_word (i n : ℕ) : word (rightC i n)=List.range' i (n+1) := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih => simp [rightC,word,ih,List.range'_succ]
private lemma words_eq (n : ℕ) : word (leftC n)=word (rightC 0 n) := by
  simp [left_word,right_word,List.range_eq_range']
private lemma left_nd (n : ℕ) : (word (leftC n)).Nodup := by rw [left_word]; exact List.nodup_range
private lemma right_nd (n : ℕ) : (word (rightC 0 n)).Nodup := words_eq n ▸ left_nd n

private lemma left_part {p q n} (h : Part (mul p q) (leftC n)) :
    ∃ j<n, p=leftC j ∧ q=var (j+1) := by
  induction n with
  | zero => cases h
  | succ n ih =>
    change Part _ (mul (leftC n) (var (n+1))) at h
    cases h with
    | self => exact ⟨_,by omega,rfl,rfl⟩
    | left h =>
      obtain ⟨j,hj,hp,hq⟩ := ih h
      exact ⟨_,by omega,hp,hq⟩
    | right h => cases h

private lemma right_part {p q i n} (h : Part (mul p q) (rightC i n)) :
    ∃ j r, j+r+1=i+n ∧ p=var j ∧ q=rightC (j+1) r := by
  induction n generalizing i with
  | zero => cases h
  | succ n ih =>
    change Part _ (mul (var i) (rightC (i+1) n)) at h
    cases h with
    | self => exact ⟨i,n,by omega,rfl,rfl⟩
    | left h => cases h
    | right h =>
      obtain ⟨j,r,hh,hp,hq⟩ := ih h
      exact ⟨_,_,by omega,hp,hq⟩

private lemma only_letters {t : Term} {n : ℕ} (hn : 2≤n)
    (hl : Part t (leftC n)) (hr : Part t (rightC 0 n)) : ∃ i, t=var i := by
  cases t with
  | var i => exact ⟨_,rfl⟩
  | mul p q =>
    obtain ⟨k,_,rfl,rfl⟩ := left_part hl
    obtain ⟨j,r,h,jj,rr⟩ := right_part hr
    cases k <;> cases r <;> simp_all [leftC,rightC]
    omega

private lemma split_weight {v : ℕ → Term} {a b c d : List ℕ}
    (he : a++b=c++d)
    (hl : (a.flatMap (word ∘ v)).length=(c.flatMap (word ∘ v)).length) : a=c := by
  induction a generalizing c with
  | nil =>
    cases c with
    | nil => rfl
    | cons j js =>
      have hp : 0<(word (v j)).length := List.length_pos_iff.2 (nonempty_word _)
      simp at hl
      omega
  | cons i is ih =>
    cases c with
    | nil => simp [nonempty_word] at hl
    | cons j js =>
      simp only [List.cons_append,List.cons.injEq] at he
      obtain ⟨rfl,he⟩ := he
      simp only [List.flatMap_cons,List.length_append,Nat.add_left_cancel_iff] at hl
      rw [ih he hl]

private lemma singleton_len (v : ℕ → Term) (w : List ℕ)
    (h : ∀ i ∈ w, ∃ j, v i=var j) : (w.flatMap (word ∘ v)).length=w.length := by
  induction w with
  | nil => rfl
  | cons i is ih =>
    obtain ⟨j,hj⟩ := h i (by simp)
    simp [hj,word,ih (fun k hk => h k (by simp [hk]))]


private lemma part_cases {s a b} (h : Part s (mul a b)) : s=mul a b ∨ Part s a ∨ Part s b := by
  cases h with
  | self => exact Or.inl rfl
  | left h => exact Or.inr (Or.inl h)
  | right h => exact Or.inr (Or.inr h)

private lemma locked {a b : Term} {n : ℕ} (hn : 2≤n) (hs : (word a).length≤n)
    (hc : CommonIdentity (a,b)) (v : ℕ → Term) (hp : Part (sub v a) (test n)) :
    sub v a = sub v b := by
  have h := flip_id hc
  have w := word_id hc
  have W : word (sub v a)=word (sub v b) := by rw [word_sub,word_sub,w]
  rcases part_cases hp with ht | hp | hp
  · cases h with
    | leaf => rfl
    | @node a b c d hac hbd =>
      obtain ⟨ha,hb⟩ := Term.mul.inj ht
      obtain ⟨wl,wr⟩ := split_eq W (hac.subst v).perm.length_eq
      change sub v a=leftC n at ha
      change sub v b=rightC 0 n at hb
      have lc := rigid (hac.subst v) wl (by rw [ha]; exact left_nd n)
      have rc := rigid (hbd.subst v) wr (by rw [hb]; exact right_nd n)
      exact congrArg₂ mul lc rc
    | @swap a b c d had hbc =>
      obtain ⟨ha,hb⟩ := Term.mul.inj ht
      change sub v a=leftC n at ha
      change sub v b=rightC 0 n at hb
      have eq : (word (sub v a)).length=(word (sub v c)).length := by
        rw [←(hbc.subst v).perm.length_eq,ha,hb,words_eq]
      rw [word_sub,word_sub] at eq
      have wa := split_weight w eq
      have one (i : ℕ) (hi : i ∈ word a) : ∃ j, v i=var j := by
        have hi' : i ∈ word b := hbc.perm.mem_iff.2 (wa ▸ hi)
        exact only_letters hn (ha ▸ part_var v hi) (hb ▸ part_var v hi')
      have len := singleton_len v (word a) one
      rw [←word_sub,ha,left_word,List.length_range] at len
      simp only [word,List.length_append] at hs
      omega
  · exact rigid (h.subst v) W (hp.nodup (left_nd n))
  · exact rigid (h.subst v) W (hp.nodup (right_nd n))

private def represents (t : Term) (x y : Term) : Prop :=
  x=y ∨ (¬Part x t ∧ ¬Part y t)

private def factors (t : Term) : Setoid Term where
  r := represents t
  iseqv := ⟨fun _ => Or.inl rfl, by rintro x y (rfl | ⟨hx,hy⟩); exact Or.inl rfl; exact Or.inr ⟨hy,hx⟩,
    by rintro a b c (rfl | ⟨ha,hb⟩) h
       · exact h
       · rcases h with rfl | ⟨_,hc⟩
         · exact Or.inr ⟨ha,hb⟩
         · exact Or.inr ⟨ha,hc⟩⟩

private abbrev Magma (t : Term) := Quotient (factors t)
private def mkM (t a : Term) : Magma t := Quotient.mk _ a
private def prodM (t : Term) : Magma t → Magma t → Magma t := Quotient.map₂ mul (by
  intro a c hac b d hbd
  change represents t a c at hac
  change represents t b d at hbd
  change represents t _ _
  rcases hac with rfl | ⟨ha,hc⟩
  · rcases hbd with rfl | ⟨hb,hd⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨fun h => hb ((Part.right Part.self).down h),fun h => hd ((Part.right Part.self).down h)⟩
  · exact Or.inr ⟨fun h => ha ((Part.left Part.self).down h),fun h => hc ((Part.left Part.self).down h)⟩)

private lemma eval_mk (t w : Term) (v : ℕ → Term) :
    w.eval (prodM t) (fun i => mkM t (v i))=mkM t (sub v w) := by
  induction w with
  | var => rfl
  | mul a b ha hb => change prodM t _ _ = _; rw [ha,hb]; rfl

private lemma holds_small {n : ℕ} (hn : 2≤n) {a b : Term} (h : CommonIdentity (a,b))
    (hs : (word a).length≤n) : Satisfies (prodM (test n)) (a,b) := by
  intro v
  let v' (i : ℕ) := (v i).out
  have hv : v=fun i => mkM (test n) (v' i) := funext fun i => (Quotient.out_eq _).symm
  rw [hv]
  change a.eval _ _=b.eval _ _
  rw [eval_mk,eval_mk]
  apply Quotient.sound
  by_cases h₁ : Part (sub v' a) (test n)
  · exact Or.inl (locked hn hs h v' h₁)
  by_cases h₂ : Part (sub v' b) (test n)
  · have h' : CommonIdentity (b,a) := fun A op ho val => (h A op ho val).symm
    exact Or.inl (locked hn ((word_id h) ▸ hs) h' v' h₂).symm
  · exact Or.inr ⟨h₁,h₂⟩

private lemma left_ne_right {n : ℕ} (hn : 2≤n) : leftC n ≠ rightC 0 n := by
  obtain _ | _ | j := n <;> simp_all [leftC,rightC]

private lemma assoc_eval {A : Type} {op : A → A → A} (h : Std.Associative op)
    (v : ℕ → A) (a b : Term) (w : word a=word b) : a.eval op v=b.eval op v := by
  let f (u : A) (l : List ℕ) := l.foldl (fun x i => op x (v i)) u
  have fold (t : Term) (u : A) : f u (word t)=op u (t.eval op v) := by
    induction t generalizing u with
    | var => rfl
    | mul l r hl hr =>
      change (word l++word r).foldl _ u = _
      rw [List.foldl_append]
      change f (f u (word l)) (word r)=_
      rw [hr,hl,h.assoc]; rfl
  have word_eval (t : Term) (i : ℕ) (l : List ℕ) (eq : word t=i::l) :
      t.eval op v=f (v i) l := by
    induction t generalizing i l with
    | var j => simp [word] at eq; obtain ⟨rfl,rfl⟩ := eq; rfl
    | mul a b ha hb =>
      obtain ⟨j,js,hj⟩ := List.exists_cons_of_ne_nil (nonempty_word a)
      simp only [word,hj,List.cons_append,List.cons.injEq] at eq
      obtain ⟨rfl,rfl⟩ := eq
      change op (a.eval op v) (b.eval op v)=_
      rw [ha j js hj]
      exact (by simpa [f,List.foldl_append] using (fold b (f (v j) js)).symm)
  obtain ⟨i,l,hl⟩ := List.exists_cons_of_ne_nil (nonempty_word a)
  exact (word_eval a i l hl).trans (word_eval b i l (w ▸ hl)).symm

private lemma sub_vars (t : Term) : sub var t=t := by
  induction t <;> simp_all [sub,Term.eval]

end CombIdentities

open CombIdentities OMA.S_mo_365616.Term

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_365616.main) := by
  rintro ⟨basis,basisCriterion⟩
  let n := basis.sup (fun e => (word e.1).length)+2
  have hn : 2 ≤ n := by dsimp [n]; omega
  let L := leftC n
  let R := rightC 0 n
  have big : CommonIdentity (mul L R,mul R L) := by
    intro A op h v
    change op (L.eval op v) (R.eval op v)=op (R.eval op v) (L.eval op v)
    rcases h with comm | assoc
    · exact comm.comm _ _
    · rw [assoc_eval assoc v L R (words_eq n)]
  have allSmall : ∀ b ∈ basis, Satisfies (prodM (test n)) b := by
    rintro ⟨a,b⟩ hab
    have small : CommonIdentity (a,b) := (basisCriterion _).2 (fun _ _ h => h _ hab)
    apply holds_small hn small
    have := Finset.le_sup (f := fun e : Equation => (word e.1).length) hab
    dsimp [n]; exact this.trans (by omega)
  have fail := (basisCriterion _).1 big (Magma (test n)) (prodM (test n)) allSmall (fun i => mkM (test n) (var i))
  change (mul L R).eval _ _=(mul R L).eval _ _ at fail
  rw [eval_mk,eval_mk,sub_vars,sub_vars] at fail
  have H : represents (test n) (mul L R) (mul R L) := Quotient.exact (s := factors (test n)) fail
  rcases H with H | H
  · exact left_ne_right hn (Term.mul.inj H).1
  · exact H.1 Part.self
