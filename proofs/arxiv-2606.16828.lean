import OMAStatements.S_arxiv_2606_16828

/-!
In CRIM, a partition is read from a binary Ferrers boundary. The moves
that preserve length parity remove eligible run pairs from the ends.
Their remaining number gives the losing positions of even length.

Source: https://arxiv.org/abs/2606.16828, Conjecture 1.
-/

namespace OMA.S_arxiv_2606_16828.WordGame

open List

def Valid (w : List Bool) : Prop := w = [] ∨ ∃ mid : List Bool, w = false :: (mid ++ [true])

def trim (w : List Bool) : List Bool := ((w.dropWhile id).reverse.dropWhile (fun b => !b)).reverse

def delete (w : List Bool) (i : ℕ) : List Bool := trim (w.eraseIdx i)

private abbrev Runs := List (ℕ × ℕ)
private def Pos (l : Runs) : Prop := ∀ p ∈ l, 0 < p.1 ∧ 0 < p.2
private def pairWord (p : ℕ × ℕ) : List Bool := replicate p.1 false ++ replicate p.2 true
private def word (l : Runs) : List Bool := l.flatMap pairWord

private theorem pos_append {l r : Runs} : Pos (l ++ r) ↔ Pos l ∧ Pos r := by
  simp only [Pos, List.mem_append, or_imp, forall_and]
  tauto

private theorem pos_cons {l : Runs} {p : ℕ × ℕ} : Pos (p :: l) ↔ (0 < p.1 ∧ 0 < p.2) ∧ Pos l := by
  simp only [Pos, List.mem_cons, or_imp, forall_and, forall_eq]
  tauto

private theorem word_append (l r : Runs) : word (l ++ r) = word l ++ word r := by
  simp [word]

private theorem word_cons (p : ℕ × ℕ) (l : Runs) : word (p :: l) = pairWord p ++ word l := rfl

private theorem word_nil : word [] = [] := rfl

private theorem word_starts_false (l : Runs) (hp : Pos l) (hn : l ≠ []) :
    ∃ tail : List Bool, word l = false :: tail := by
  obtain ⟨⟨a,b⟩,r,rfl⟩ := List.exists_cons_of_ne_nil hn
  have ha : 0 < a := (hp (a,b) (by simp)).1
  cases a with
  | zero => omega
  | succ a => exact ⟨_, rfl⟩

private theorem word_ends_true (l : Runs) (hp : Pos l) (hn : l ≠ []) :
    ∃ pre : List Bool, word l = pre ++ [true] := by
  induction l using List.reverseRecOn with
  | nil => exact (hn rfl).elim
  | append_singleton l p _ =>
      obtain ⟨a,b⟩ := p
      have hb : 0 < b := (hp (a,b) (by simp)).2
      cases b with
      | zero => omega
      | succ b =>
        refine ⟨word l ++ replicate a false ++ replicate b true, ?_⟩
        simp only [word_append,word_cons,word_nil,pairWord,List.append_nil,
          List.replicate_add,List.append_assoc]
        rfl

private theorem word_valid (l : Runs) (hp : Pos l) : Valid (word l) := by
  by_cases hn : l = []
  · simp [Valid, hn, word_nil]
  · obtain ⟨tail, ht⟩ := word_starts_false l hp hn
    obtain ⟨pre, hp'⟩ := word_ends_true l hp hn
    cases pre with
    | nil => simp [ht] at hp'
    | cons a mid =>
      have h := ht.symm.trans hp'
      have hm := List.cons.inj h
      exact Or.inr ⟨mid, ht.trans (congrArg (List.cons false) hm.2)⟩

private theorem trim_decomposition (b a : ℕ) (l : Runs) (hl : Pos l) :
    trim (replicate b true ++ word l ++ replicate a false) = word l := by
  have hlead : (replicate b true ++ (word l ++ replicate a false)).dropWhile id =
      (word l ++ replicate a false).dropWhile id := by
    apply List.dropWhile_append_of_pos
    simp
  unfold trim
  rw [List.append_assoc, hlead]
  by_cases hn : l = []
  · subst l
    simp [word_nil]
  · obtain ⟨tail, htail⟩ := word_starts_false l hl hn
    obtain ⟨pre, hpre⟩ := word_ends_true l hl hn
    have hdr : (word l ++ replicate a false).dropWhile id = word l ++ replicate a false := by
      simp [htail]
    rw [hdr, List.reverse_append, List.reverse_replicate, List.dropWhile_append_of_pos (by simp)]
    simp [hpre]

private theorem parse (w : List Bool) : ∃ b l a, Pos l ∧ w = replicate b true ++ word l ++ replicate a false := by
  induction w with
  | nil => exact ⟨0, [], 0, by simp [Pos], rfl⟩
  | cons x w ih =>
    obtain ⟨b,l,a,hl,rfl⟩ := ih
    cases x with
    | true => exact ⟨b+1,l,a,hl, by simp [List.replicate_succ]⟩
    | false =>
      cases b with
      | succ b =>
        refine ⟨0,(1,b+1)::l,a,pos_cons.mpr ⟨by simp,hl⟩,?_⟩
        simp [word_cons, pairWord, List.append_assoc, List.replicate_succ]
      | zero =>
        cases l with
        | nil => exact ⟨0,[],a+1,hl, by simp [word_nil, List.replicate_succ]⟩
        | cons p l =>
          obtain ⟨c,d⟩ := p
          obtain ⟨hp,ht⟩ := pos_cons.mp hl
          refine ⟨0,(c+1,d)::l,a,pos_cons.mpr ⟨⟨by simp,hp.2⟩,ht⟩,?_⟩
          simp [word_cons, pairWord, List.replicate_succ]

theorem trim_valid (w : List Bool) : Valid (trim w) := by
  obtain ⟨b,l,a,hl,rfl⟩ := parse w
  rw [trim_decomposition b a l hl]
  exact word_valid l hl

private theorem trim_valid_eq {w : List Bool} (hw : Valid w) : trim w = w := by
  rcases hw with rfl | ⟨mid,rfl⟩
  · rfl
  · simp [trim]

private theorem valid_parse {w : List Bool} (hw : Valid w) : ∃ l, Pos l ∧ w = word l := by
  obtain ⟨b,l,a,hl,he⟩ := parse w
  have ht := trim_valid_eq hw
  refine ⟨l,hl,?_⟩
  rw [he, trim_decomposition] at ht
  · exact he.trans ht.symm
  · exact hl

private def flipWord (w : List Bool) : List Bool := w.reverse.map (fun b => !b)
private def flipRuns (l : Runs) : Runs := l.reverse.map Prod.swap

private theorem flipWord_flip (w : List Bool) : flipWord (flipWord w) = w := by
  simp [flipWord, List.map_reverse, List.map_map, Function.comp_def]

private theorem flipRuns_flip (l : Runs) : flipRuns (flipRuns l) = l := by
  simp [flipRuns, List.map_reverse, List.map_map, Function.comp_def]

private theorem pos_flipRuns {l : Runs} (hl : Pos l) : Pos (flipRuns l) := by
  intro p hp
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
  exact (and_comm.mp (hl q (List.mem_reverse.mp hq)))

private theorem flipRuns_append (l r : Runs) : flipRuns (l ++ r) = flipRuns r ++ flipRuns l := by
  simp [flipRuns]

private theorem flipRuns_cons (p : ℕ × ℕ) (l : Runs) : flipRuns (p :: l) = flipRuns l ++ [p.swap] := by
  simp [flipRuns]

private theorem word_flipRuns (l : Runs) : word (flipRuns l) = flipWord (word l) := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    simp [flipRuns_cons, word_append, word_cons, word_nil, ih, flipWord, pairWord]

private theorem flipWord_length (w : List Bool) : (flipWord w).length = w.length := by simp [flipWord]

private theorem flipWord_trim (w : List Bool) : flipWord (trim w) = trim (flipWord w) := by
  obtain ⟨b,l,a,hl,rfl⟩ := parse w
  rw [trim_decomposition b a l hl]
  have hh : flipWord (replicate b true ++ word l ++ replicate a false) =
      replicate a true ++ word (flipRuns l) ++ replicate b false := by
    simp [word_flipRuns, flipWord, List.append_assoc]
  rw [hh, trim_decomposition a b _ (pos_flipRuns hl), word_flipRuns]

private def MoveWord (w v : List Bool) : Prop := ∃ i, i < w.length ∧ delete w i = v

private theorem eraseIdx_split {α : Type*} (l : List α) (i : ℕ) (hi : i < l.length) :
    ∃ a x b, l = a ++ x :: b ∧ a.length = i ∧ l.eraseIdx i = a ++ b := by
  induction l generalizing i with
  | nil => simp at hi
  | cons x l ih =>
    cases i with
    | zero => exact ⟨[],x,l,rfl,rfl,rfl⟩
    | succ i =>
      obtain ⟨a,y,b,he,hl,hd⟩ := ih i (by simpa using hi)
      exact ⟨x::a,y,b,by simp [he],by simp [hl],by simp [hd]⟩

private theorem move_erase_cons (a b : List Bool) (x : Bool) :
    MoveWord (a ++ x :: b) (trim (a ++ b)) := by
  refine ⟨a.length, by simp, ?_⟩
  unfold delete
  rw [List.eraseIdx_append_of_length_le (Nat.le_refl a.length)]
  simp

private theorem flipWord_append (a b : List Bool) : flipWord (a ++ b) = flipWord b ++ flipWord a := by
  simp [flipWord]

private theorem flipWord_cons (b : Bool) (w : List Bool) : flipWord (b :: w) = flipWord w ++ [!b] := by
  simp [flipWord]

private theorem flip_move {w v : List Bool} (h : MoveWord w v) : MoveWord (flipWord w) (flipWord v) := by
  obtain ⟨i,hi,hi'⟩ := h
  obtain ⟨a,x,b,hw,_,he⟩ := eraseIdx_split w i hi
  have hv : v = trim (a ++ b) := by rw [←hi', delete, he]
  rw [hw, hv, flipWord_append, flipWord_cons, flipWord_trim, flipWord_append, List.append_assoc]
  exact move_erase_cons (flipWord b) (flipWord a) (!x)

private def rowDelete (pre : Runs) (a b : ℕ) (post : Runs) : Runs :=
  if 1 < b then pre ++ (a,b-1) :: post else
    match post with
    | [] => pre
    | (c,d) :: rest => pre ++ (a+c,d) :: rest

private theorem row_pos {pre post : Runs} {a b : ℕ} (h : Pos (pre ++ (a,b) :: post)) :
    Pos (rowDelete pre a b post) := by
  obtain ⟨hp,hbd,hs⟩ := (pos_append.mp h).imp_right pos_cons.mp
  unfold rowDelete
  split
  · exact pos_append.mpr ⟨hp,pos_cons.mpr ⟨⟨hbd.1,by omega⟩,hs⟩⟩
  · cases post with
    | nil => exact hp
    | cons q qs =>
      obtain ⟨c,d⟩ := q
      obtain ⟨hq,ht⟩ := pos_cons.mp hs
      exact pos_append.mpr ⟨hp,pos_cons.mpr ⟨⟨by omega,hq.2⟩,ht⟩⟩

private theorem word_split (pre post : Runs) (a b : ℕ) :
    word (pre ++ (a,b) :: post) = (word pre ++ replicate a false) ++ (replicate b true ++ word post) := by
  simp [word_append, word_cons, pairWord, List.append_assoc]

private theorem erase_row_raw (pre post : Runs) (a b j : ℕ) (hj : j < b) :
    (word (pre ++ (a,b) :: post)).eraseIdx ((word pre).length + a + j) =
      (word pre ++ replicate a false) ++ (replicate (b-1) true ++ word post) := by
  rw [word_split, List.eraseIdx_append_of_length_le (by simp),
    List.eraseIdx_append_of_lt_length (by simpa using hj), List.eraseIdx_replicate]
  simp [hj]

private theorem row_delete_eq {pre post : Runs} {a b j : ℕ} (h : Pos (pre ++ (a,b) :: post))
    (hj : j < b) : delete (word (pre ++ (a,b) :: post)) ((word pre).length+a+j) =
      word (rowDelete pre a b post) := by
  unfold delete
  rw [erase_row_raw _ _ _ _ _ hj]
  unfold rowDelete
  split
  · rename_i hb
    rw [← word_split]
    apply trim_valid_eq
    apply word_valid
    simpa only [rowDelete,if_pos hb] using row_pos h
  · have h1 : b = 1 := by omega
    obtain ⟨hp,hs⟩ := pos_append.mp h
    subst b
    cases post with
    | nil => simpa [word_nil, List.append_assoc] using trim_decomposition 0 a pre hp
    | cons q qs =>
      obtain ⟨c,d⟩ := q
      have hr : Pos (pre ++ (a+c,d)::qs) := by
        simpa [rowDelete] using row_pos h
      have ht := trim_valid_eq (word_valid _ hr)
      simp only [word_append,word_cons,pairWord,List.replicate_add,List.append_assoc] at ht
      simpa only [word_append,word_cons,pairWord,List.replicate_add,Nat.sub_self,List.replicate_zero,
        List.nil_append,List.append_assoc] using ht

private theorem row_move {pre post : Runs} {a b : ℕ} (h : Pos (pre ++ (a,b) :: post)) :
    MoveWord (word (pre ++ (a,b)::post)) (word (rowDelete pre a b post)) := by
  have hb := ((pos_cons.mp ((pos_append.mp h).2)).1).2
  exact ⟨(word pre).length+a+0, by rw [word_split]; simp; omega, row_delete_eq h hb⟩

private theorem col_shrink_move {pre post : Runs} {a b : ℕ} (h : Pos (pre ++ (a,b) :: post))
    (ha : 1 < a) : MoveWord (word (pre ++ (a,b)::post)) (word (pre ++ (a-1,b)::post)) := by
  have hh : Pos (flipRuns post ++ (b,a) :: flipRuns pre) := by
    simpa [flipRuns_append, flipRuns_cons, List.append_assoc] using pos_flipRuns h
  have hm := flip_move (row_move hh)
  simp [rowDelete, ha, ←word_flipRuns, flipRuns_append, flipRuns_cons, flipRuns_flip, List.append_assoc] at hm
  exact hm

private theorem locate_pair (l : Runs) (i : ℕ) (hi : i < (word l).length) :
    ∃ pre a b post j, l = pre ++ (a,b)::post ∧ i = (word pre).length+j ∧ j < a+b := by
  induction l generalizing i with
  | nil => simp [word_nil] at hi
  | cons p l ih =>
    obtain ⟨a,b⟩ := p
    by_cases h : i < a+b
    · exact ⟨[],a,b,l,i,rfl,by simp [word_nil],h⟩
    · have hi' : i-(a+b) < (word l).length := by
        simp [word_cons,pairWord] at hi
        omega
      obtain ⟨pre,c,d,post,j,he,hi,jl⟩ := ih _ hi'
      refine ⟨(a,b)::pre,c,d,post,j,by simp [he],?_ ,jl⟩
      simp [word_cons, pairWord]
      omega

private theorem erase_col_raw (pre post : Runs) (a b j : ℕ) (hj : j < a) :
    (word (pre ++ (a,b) :: post)).eraseIdx ((word pre).length+j) =
      (word pre ++ replicate (a-1) false) ++ (replicate b true ++ word post) := by
  rw [word_append, List.eraseIdx_append_of_length_le (Nat.le_add_right _ _), word_cons, pairWord]
  simp only [List.append_assoc, Nat.add_sub_cancel_left]
  rw [List.eraseIdx_append_of_lt_length (by simpa using hj), List.eraseIdx_replicate]
  simp [hj]

private theorem delete_into_run (l : Runs) (hl : Pos l) (i : ℕ) (hi : i < (word l).length) :
    (∃ pre a b post, l = pre ++ (a,b)::post ∧ delete (word l) i = word (rowDelete pre a b post)) ∨
    (∃ pre a b post, flipRuns l = pre ++ (a,b)::post ∧
      flipWord (delete (word l) i) = word (rowDelete pre a b post)) := by
  obtain ⟨pre,a,b,post,j,rfl,hi',hbound⟩ := locate_pair l i hi
  rw [hi']
  by_cases hj : j < a
  · right
    have hp : Pos (flipRuns post ++ (b,a) :: flipRuns pre) := by
      simpa [flipRuns_append, flipRuns_cons, List.append_assoc] using pos_flipRuns hl
    refine ⟨flipRuns post,b,a,flipRuns pre,?_ ,?_⟩
    · simp [flipRuns_append, flipRuns_cons, List.append_assoc]
    · unfold delete
      rw [erase_col_raw _ _ _ _ _ hj, flipWord_trim]
      have hr := row_delete_eq (pre:=flipRuns post) (post:=flipRuns pre) (a:=b) (b:=a) (j:=j) hp hj
      unfold delete at hr
      rw [erase_row_raw _ _ _ _ _ hj] at hr
      simp only [flipWord_append, ← word_flipRuns]
      have hrF (n : ℕ) (x : Bool) : flipWord (replicate n x) = replicate n (!x) := by simp [flipWord]
      rw [hrF,hrF]
      simpa only [List.append_assoc,Bool.not_true,Bool.not_false] using hr
  · left
    refine ⟨pre,a,b,post,rfl,?_⟩
    have ha : j = a+(j-a) := by omega
    rw [ha, ← Nat.add_assoc]
    exact row_delete_eq hl (by omega)

private theorem move_smaller {w v : List Bool} (h : MoveWord w v) : v.length < w.length := by
  obtain ⟨i,hi,rfl⟩ := h
  obtain ⟨a,b,c,he,_,hd⟩ := eraseIdx_split w i hi
  have hleft := List.length_dropWhile_le id (w.eraseIdx i)
  have hright := List.length_dropWhile_le (fun b : Bool => !b) ((w.eraseIdx i).dropWhile id).reverse
  simp only [List.length_reverse] at hright
  unfold delete trim
  rw [List.length_reverse]
  have : (w.eraseIdx i).length < w.length := by rw [hd,he]; simp
  omega

private def leftRem (p : ℕ × ℕ) : Bool := decide (p.1 = 1 ∧ Odd p.2)
private def rightRem (p : ℕ × ℕ) : Bool := leftRem p.swap
private def runCount {α : Type*} (test : α → Bool) (l : List α) : ℕ := (l.takeWhile test).length
private def leftCount (l : Runs) : ℕ := runCount leftRem l
private def rightCount (l : Runs) : ℕ := runCount rightRem l.reverse
private def score (l : Runs) : ℕ := min l.length (leftCount l + rightCount l)

private theorem leftRem_true {a b : ℕ} : leftRem (a,b) = true ↔ a=1 ∧ Odd b := by
  simp [leftRem]

private theorem rightRem_true {a b : ℕ} : rightRem (a,b) = true ↔ b=1 ∧ Odd a := by
  simp [rightRem,leftRem]

private theorem runCount_le {α : Type*} (test : α → Bool) (l : List α) : runCount test l ≤ l.length :=
  (List.takeWhile_sublist (l:=l) test).length_le

private theorem runCount_append {α : Type*} (test : α → Bool) (l r : List α) :
    runCount test (l ++ r) = runCount test l + if runCount test l = l.length then runCount test r else 0 := by
  unfold runCount
  rw [List.takeWhile_append]
  split <;> simp_all

private theorem runCount_cons {α : Type*} (test : α → Bool) (x : α) (l : List α) :
    runCount test (x :: l) = if test x then 1+runCount test l else 0 := by
  cases h : test x <;> simp [runCount, h, Nat.add_comm]

private theorem left_append (l r : Runs) :
    leftCount (l ++ r) = leftCount l + if leftCount l = l.length then leftCount r else 0 :=
  runCount_append _ _ _

private theorem right_append (l r : Runs) :
    rightCount (l ++ r) = rightCount r + if rightCount r = r.length then rightCount l else 0 := by
  unfold rightCount
  rw [List.reverse_append, runCount_append, List.length_reverse]

private theorem left_cons (p : ℕ × ℕ) (l : Runs) :
    leftCount (p :: l) = if leftRem p then 1+leftCount l else 0 := runCount_cons _ _ _

private theorem right_snoc (p : ℕ × ℕ) (l : Runs) :
    rightCount (l ++ [p]) = if rightRem p then 1+rightCount l else 0 := by
  simpa only [rightCount,List.reverse_append,List.reverse_singleton,List.singleton_append] using
    runCount_cons rightRem p l.reverse

private theorem left_le (l : Runs) : leftCount l ≤ l.length := runCount_le _ _
private theorem right_le (l : Runs) : rightCount l ≤ l.length := by
  simpa only [rightCount,List.length_reverse] using runCount_le rightRem l.reverse

private theorem left_stop (pre post : Runs) {p : ℕ × ℕ} (hp : leftRem p = false) :
    leftCount (pre ++ p::post) = leftCount pre := by
  rw [left_append,left_cons,hp]
  simp

private theorem right_stop (pre post : Runs) {p : ℕ × ℕ} (hp : rightRem p = false) :
    rightCount (pre ++ p::post) = rightCount post := by
  rw [show pre ++ p::post = (pre ++ [p]) ++ post by simp, right_append, right_snoc, hp]
  simp

private theorem right_count_step (pre post : Runs) (p : ℕ × ℕ) :
    rightCount (pre ++ p::post) = rightCount post +
      if rightCount post = post.length ∧ rightRem p = true then 1+rightCount pre else 0 := by
  rw [show pre ++ p::post = (pre ++ [p]) ++ post by simp, right_append, right_snoc]
  by_cases h : rightCount post = post.length <;> cases hp : rightRem p <;> simp [h]

private theorem count_length_iff {α : Type*} (test : α → Bool) (l : List α) :
    runCount test l = l.length ↔ ∀ p ∈ l, test p = true := by
  constructor
  · intro h
    have htake : l.takeWhile test = l := (List.takeWhile_sublist (l:=l) test).eq_of_length h
    have htrue : (l.takeWhile test).all test = true := List.all_takeWhile
    rw [htake] at htrue
    exact List.all_eq_true.mp htrue
  · intro h
    have htake : l.takeWhile test = l := List.takeWhile_eq_self_iff.mpr h
    simp only [runCount,htake]

private theorem left_length_iff (l : Runs) :
    leftCount l = l.length ↔ ∀ p ∈ l, leftRem p = true := count_length_iff _ _

private theorem right_length_iff (l : Runs) :
    rightCount l = l.length ↔ ∀ p ∈ l, rightRem p = true := by
  unfold rightCount
  rw [← List.length_reverse (as:=l), count_length_iff]
  simp

private theorem right_left_flip (l : Runs) : leftCount (flipRuns l) = rightCount l := by
  simp only [leftCount,rightCount,runCount,flipRuns,List.takeWhile_map,List.length_map,Function.comp_def]
  rfl

private theorem left_right_flip (l : Runs) : rightCount (flipRuns l) = leftCount l := by
  rw [←right_left_flip,flipRuns_flip]

private theorem score_flip (l : Runs) : score (flipRuns l) = score l := by
  unfold score
  rw [right_left_flip,left_right_flip]
  simp [flipRuns,Nat.add_comm]

private theorem word_length_split (pre post : Runs) (a b : ℕ) :
    (word (pre ++ (a,b)::post)).length = (word pre).length+a+b+(word post).length := by
  simp [word_split, Nat.add_assoc]

private theorem row_word_length {pre post : Runs} {a b : ℕ} (hb : 0<b) :
    (word (pre ++ (a,b)::post)).length = (word (rowDelete pre a b post)).length +
      if b=1 ∧ post=[] then a+1 else 1 := by
  unfold rowDelete
  split
  · rename_i hz
    have hne : b ≠ 1 := by omega
    simp [word_length_split,hne]
    omega
  · rename_i hz
    have he : b=1 := by omega
    subst b
    cases post with
    | nil => simp [word_length_split,word_nil,Nat.add_assoc]
    | cons p l =>
      obtain ⟨c,d⟩ := p
      simp [word_length_split,word_cons,pairWord]
      omega

private theorem score_snoc_right (l : Runs) {p : ℕ × ℕ} (hp : rightRem p=true) :
    score (l ++ [p]) = score l + 1 := by
  have hright := right_snoc p l
  rw [hp,if_pos rfl] at hright
  have hleft := left_append l [p]
  have hle := left_le l
  unfold score
  rw [hright,hleft,List.length_append,List.length_singleton]
  split_ifs with h
  · omega
  · omega

private theorem even_word_odd_pair_notL (p : ℕ × ℕ) (hp : Odd (p.1+p.2)) : leftRem p = false := by
  obtain ⟨a,b⟩ := p
  by_contra hh
  have hh' : leftRem (a,b) = true := Bool.eq_true_of_not_eq_false hh
  obtain ⟨ha,hb⟩ := leftRem_true.mp hh'
  simp only [Nat.odd_iff] at hp hb
  omega

private theorem even_word_odd_pair_notR (p : ℕ × ℕ) (hp : Odd (p.1+p.2)) : rightRem p = false := by
  obtain ⟨a,b⟩ := p
  by_contra hh
  have hh' : rightRem (a,b) = true := Bool.eq_true_of_not_eq_false hh
  obtain ⟨ha,hb⟩ := rightRem_true.mp hh'
  simp only [Nat.odd_iff] at hp hb
  omega

private theorem word_even_if_pair_even {l : Runs} (h : ∀ p ∈ l, Even (p.1+p.2)) : Even (word l).length := by
  induction l with
  | nil => simp [word_nil]
  | cons p l ih =>
    obtain ⟨a,b⟩ := p
    have hp := h (a,b) (by simp)
    have ht : ∀ p ∈ l, Even (p.1+p.2) := fun p hp => h p (List.mem_cons_of_mem _ hp)
    simpa [word_cons,pairWord,Nat.add_assoc] using hp.add (ih ht)

private theorem odd_split (l : Runs) (h : Odd (word l).length) :
    ∃ pre a b post, l = pre ++ (a,b)::post ∧ Odd (a+b) := by
  have he : ∃ p ∈ l, Odd (p.1+p.2) := by
    by_contra! H
    have hEven := word_even_if_pair_even (l:=l) (fun p hp => Nat.not_odd_iff_even.mp (H p hp))
    exact (Nat.not_even_iff_odd.mpr h) hEven
  obtain ⟨⟨a,b⟩,hp,hab⟩ := he
  obtain ⟨pre,post,rfl⟩ := List.append_of_mem hp
  exact ⟨pre,a,b,post,rfl,hab⟩

private theorem score_odd_word (l : Runs) (hl : Odd (word l).length) :
    score l = leftCount l + rightCount l := by
  obtain ⟨pre,a,b,post,rfl,h⟩ := odd_split l hl
  have hL := left_stop pre post (even_word_odd_pair_notL (a,b) h)
  have hR := right_stop pre post (even_word_odd_pair_notR (a,b) h)
  have h1 := left_le pre
  have h2 := right_le post
  unfold score
  rw [hL,hR,Nat.min_eq_right]
  simp
  omega

private theorem row_score_drop {pre post : Runs} {a b : ℕ}
    (hp : Pos (pre ++ (a,b)::post)) (he : Even (word (pre ++ (a,b)::post)).length)
    (he' : Even (word (rowDelete pre a b post)).length) :
    score (pre ++ (a,b)::post) = score (rowDelete pre a b post) + 1 := by
  have hlen := row_word_length (pre:=pre) (post:=post) (a:=a) ((pos_cons.mp (pos_append.mp hp).2).1).2
  by_cases h : b=1 ∧ post=[]
  · obtain ⟨rfl,rfl⟩ := h
    simp at hlen
    have ha : Odd a := by
      simp only [Nat.odd_iff,Nat.even_iff] at he he' ⊢
      omega
    simpa [rowDelete] using score_snoc_right pre (rightRem_true.mpr ⟨rfl,ha⟩)
  · simp only [if_neg h, Nat.even_iff] at hlen he he'
    omega

private theorem run_child (l : Runs) (hl : Pos l) (i : ℕ) (hi : i < (word l).length) :
    ∃ r, Pos r ∧ delete (word l) i = word r ∧
      (Even (word l).length → Even (word r).length → score l = score r + 1) := by
  rcases delete_into_run l hl i hi with ⟨pre,a,b,post,hp,he⟩ | ⟨pre,a,b,post,hp,he⟩
  · exact ⟨rowDelete pre a b post,row_pos (hp ▸ hl),he,fun h0 h1 =>
      hp.symm ▸ row_score_drop (hp ▸ hl) (hp ▸ h0) h1⟩
  · have hf : Pos (pre ++ (a,b)::post) := hp ▸ pos_flipRuns hl
    let r := rowDelete pre a b post
    have hEq : delete (word l) i = word (flipRuns r) := by
      rw [word_flipRuns, ← he, flipWord_flip]
    refine ⟨flipRuns r,pos_flipRuns (row_pos hf),hEq,fun h0 h1 => ?_⟩
    have ha : Even (word (pre ++ (a,b)::post)).length := by
      rw [←hp,word_flipRuns,flipWord_length]
      exact h0
    have hb : Even (word r).length := by rw [word_flipRuns,flipWord_length] at h1; exact h1
    have hd := row_score_drop hf ha hb
    rw [score_flip]
    rwa [←hp,score_flip] at hd

private theorem even_right_child {l : Runs} (hl : Pos l) (hR : 0 < rightCount l)
    (he : Even (word l).length) :
    ∃ r, Pos r ∧ MoveWord (word l) (word r) ∧ Even (word r).length ∧ score l = score r+1 := by
  induction l using List.reverseRecOn with
  | nil => simp [rightCount,runCount] at hR
  | append_singleton l p _ =>
    obtain ⟨a,b⟩ := p
    rw [right_snoc] at hR
    have hab : rightRem (a,b)=true := by
      cases h : rightRem (a,b) <;> simp [h] at hR ⊢
    obtain ⟨rfl,ha⟩ := rightRem_true.mp hab
    have hm := row_move (pre:=l) (post:=[]) hl
    refine ⟨l,(pos_append.mp hl).1,by simpa [rowDelete] using hm,?_,score_snoc_right l hab⟩
    rw [word_length_split,word_nil] at he
    simp only [List.length_nil,Nat.even_iff,Nat.odd_iff] at ha he ⊢
    omega

private theorem mirror_child {l r : Runs} (hr : Pos r) (hm : MoveWord (word (flipRuns l)) (word r))
    (he : Even (word r).length) :
    Pos (flipRuns r) ∧ MoveWord (word l) (word (flipRuns r)) ∧ Even (word (flipRuns r)).length := by
  refine ⟨pos_flipRuns hr, ?_, ?_⟩
  · have hh := flip_move hm
    rwa [←word_flipRuns,←word_flipRuns,flipRuns_flip] at hh
  · rwa [word_flipRuns,flipWord_length]

private theorem even_child_exists {l : Runs} (hl : Pos l) (hs : 0 < score l)
    (he : Even (word l).length) :
    ∃ r, Pos r ∧ MoveWord (word l) (word r) ∧ Even (word r).length ∧ score l = score r+1 := by
  by_cases hR : 0 < rightCount l
  · exact even_right_child hl hR he
  · have hL : 0 < leftCount l := by unfold score at hs; omega
    have hR' : 0 < rightCount (flipRuns l) := by rwa [left_right_flip]
    have he' : Even (word (flipRuns l)).length := by rwa [word_flipRuns,flipWord_length]
    obtain ⟨r,hr,hm,her,hd⟩ := even_right_child (pos_flipRuns hl) hR' he'
    obtain ⟨hp,hM,hE⟩ := mirror_child hr hm her
    exact ⟨flipRuns r,hp,hM,hE,by rwa [score_flip, ←score_flip l]⟩

private theorem row_even_length {pre post : Runs} {a b : ℕ} (hb : 0<b)
    (h : Odd (word (pre ++ (a,b)::post)).length) (ha : Even a) :
    Even (word (rowDelete pre a b post)).length := by
  have hh := row_word_length (pre:=pre) (post:=post) (a:=a) hb
  split_ifs at hh <;> simp only [Nat.odd_iff,Nat.even_iff] at ha h ⊢ <;> omega

private theorem rightRem_add_even {a c d : ℕ} (ha : Even a) :
    rightRem (a+c,d) = rightRem (c,d) := by
  have hz := Nat.even_iff.mp ha
  simp [rightRem,leftRem,Nat.odd_iff,Nat.add_mod,hz]

private theorem row_remove_one_counts (pre post : Runs) {a : ℕ} (ha : Even a) (ha' : 1<a) :
    (rowDelete pre a 1 post).length = pre.length+post.length ∧
    leftCount (rowDelete pre a 1 post) = leftCount pre ∧
    rightCount (rowDelete pre a 1 post) = rightCount (pre++post) := by
  cases post with
  | nil => simp [rowDelete]
  | cons p ps =>
    obtain ⟨c,d⟩ := p
    simp only [rowDelete,lt_self_iff_false,if_false,List.length_append,List.length_cons,true_and]
    constructor
    · apply left_stop
      have hne : a+c ≠ 1 := by omega
      simp [leftRem,hne]
    · rw [right_count_step,right_count_step,rightRem_add_even ha]

private theorem odd_even_score_one {pre post : Runs} {a : ℕ}
    (hp : Pos (pre ++ (a,1)::post)) (ha : Even a) (ha2 : 1<a)
    (ho : Odd (word (pre ++ (a,1)::post)).length) (hs : Even (leftCount pre + rightCount post)) :
    ∃ r, Pos r ∧ MoveWord (word (pre ++ (a,1)::post)) (word r) ∧
      Even (word r).length ∧ Even (score r) := by
  let r := rowDelete pre a 1 post
  have hRdata := row_remove_one_counts pre post ha ha2
  have hrP : Pos r := row_pos hp
  have hrM : MoveWord (word (pre ++ (a,1)::post)) (word r) := row_move hp
  have hrE : Even (word r).length := row_even_length (by decide) ho ha
  have hLot := left_le pre
  have hRot := right_le post
  by_cases hS : rightCount post=post.length
  · let s := pre ++ (a-1,1)::post
    have hSpos : Pos s := by
      obtain ⟨hl,hx,hp⟩ := (pos_append.mp hp).imp_right pos_cons.mp
      exact pos_append.mpr ⟨hl,pos_cons.mpr ⟨by simp; omega,hp⟩⟩
    have hSstep : MoveWord (word (pre ++ (a,1)::post)) (word s) := col_shrink_move hp ha2
    have hSe : Even (word s).length := by
      dsimp only [s]
      rw [word_length_split] at ho ⊢
      simp only [Nat.odd_iff,Nat.even_iff] at ho ⊢
      omega
    have hSa : Odd (a-1) := by
      simp only [Nat.odd_iff,Nat.even_iff] at ha ⊢
      omega
    have hrRem := (rightRem_true (a:=a-1) (b:=1)).mpr ⟨rfl,hSa⟩
    have hRs : rightCount s = post.length+1+rightCount pre := by
      dsimp only [s]
      rw [right_count_step,hS,if_pos ⟨rfl,hrRem⟩]
      omega
    have hscore_r : score r = min (pre.length+post.length) (leftCount pre+post.length+rightCount pre) := by
      dsimp only [r,score]
      rw [hRdata.1,hRdata.2.1,hRdata.2.2,right_append,hS,if_pos rfl]
      omega
    have hscore_s : score s = score r+1 := by
      rw [hscore_r]
      unfold score
      rw [hRs]
      dsimp only [s]
      rw [List.length_append,List.length_cons,left_append]
      split_ifs <;> omega
    by_cases he : Even (score r)
    · exact ⟨r,hrP,hrM,hrE,he⟩
    · refine ⟨s,hSpos,hSstep,hSe,?_⟩
      rw [hscore_s, Nat.even_iff]
      simp only [Nat.even_iff] at he
      omega
  · refine ⟨r,hrP,hrM,hrE,?_⟩
    dsimp only [r,score]
    rw [hRdata.1,hRdata.2.1,hRdata.2.2,right_append,if_neg hS,Nat.add_zero,Nat.min_eq_right]
    · exact hs
    · omega

private theorem odd_even_score_right_odd {pre post : Runs} {a b : ℕ}
    (hp : Pos (pre ++ (a,b)::post)) (ho : Odd (word (pre ++ (a,b)::post)).length)
    (hs : Even (score (pre ++ (a,b)::post))) (hab : Odd (a+b)) (hb : Odd b) :
    ∃ r, Pos r ∧ MoveWord (word (pre ++ (a,b)::post)) (word r) ∧
      Even (word r).length ∧ Even (score r) := by
  have ha : Even a := by simp only [Nat.odd_iff,Nat.even_iff] at hab hb ⊢; omega
  obtain ⟨hpre,hpos,hpost⟩ := (pos_append.mp hp).imp_right pos_cons.mp
  have hL := left_stop pre post (even_word_odd_pair_notL (a,b) hab)
  have hR := right_stop pre post (even_word_odd_pair_notR (a,b) hab)
  have hSE : Even (leftCount pre + rightCount post) := by
    rwa [score_odd_word _ ho,hL,hR] at hs
  have ha2 : 1<a := by have := hpos.1; simp only [Nat.even_iff] at ha; omega
  by_cases hB : b=1
  · subst b
    exact odd_even_score_one hp ha ha2 ho hSE
  · have hb3 : 1<b-1 := by have := hpos.2; simp only [Nat.odd_iff] at hb; omega
    let r := rowDelete pre a b post
    have he' : r = pre ++ (a,b-1)::post := by
      have hb2 : 1<b := by omega
      simp [r,rowDelete,hb2]
    refine ⟨r,row_pos hp,row_move hp,row_even_length hpos.2 ho ha,?_⟩
    have hl' : leftRem (a,b-1) = false := by simp [leftRem,show a≠1 by omega]
    have hr' : rightRem (a,b-1) = false := by simp [rightRem,leftRem,show (b-1 : ℕ) ≠ 1 by omega]
    rw [he',score,left_stop pre post hl',right_stop pre post hr',Nat.min_eq_right]
    · exact hSE
    · have hl := left_le pre
      have hr := right_le post
      simp
      omega

private theorem odd_even_score_child {l : Runs} (hl : Pos l) (ho : Odd (word l).length)
    (hs : Even (score l)) : ∃ r, Pos r ∧ MoveWord (word l) (word r) ∧
      Even (word r).length ∧ Even (score r) := by
  obtain ⟨pre,a,b,post,rfl,hab⟩ := odd_split l ho
  by_cases hB : Odd b
  · exact odd_even_score_right_odd hl ho hs hab hB
  · let l := pre ++ (a,b)::post
    have hF : flipRuns l = flipRuns post ++ (b,a)::flipRuns pre := by
      simp [l,flipRuns_append,flipRuns_cons,List.append_assoc]
    have ha : Odd a := by simp only [Nat.odd_iff] at hab hB ⊢; omega
    have hf := pos_flipRuns hl
    have hfo : Odd (word (flipRuns l)).length := by rwa [word_flipRuns,flipWord_length]
    have hfs : Even (score (flipRuns l)) := by rwa [score_flip]
    rw [hF] at hf hfo hfs
    obtain ⟨r,hr,hm,hrE,hrS⟩ := odd_even_score_right_odd hf hfo hfs (by rwa [Nat.add_comm]) ha
    rw [← hF] at hm
    exact ⟨flipRuns r,mirror_child hr hm hrE |>.1,mirror_child hr hm hrE |>.2.1,
      mirror_child hr hm hrE |>.2.2,by rwa [score_flip]⟩

private theorem drop_left_head (l : Runs) {q : ℕ × ℕ} {r : Runs}
    (h : l.dropWhile leftRem = q::r) : leftRem q = false := by
  induction l with
  | nil => simp at h
  | cons p l ih =>
    cases hp : leftRem p
    · simp [hp] at h
      simpa [h.1] using hp
    · apply ih
      simpa [hp] using h

private theorem last_left_pair (l : Runs) (hL : 0 < leftCount l) (hM : leftCount l < l.length) :
    ∃ pre b a d rest, l = pre ++ (1,b) :: (a,d) :: rest ∧
      leftCount pre = pre.length ∧ Odd b ∧ leftRem (a,d) = false := by
  let lead := l.takeWhile leftRem
  let tail := l.dropWhile leftRem
  have hall : lead ++ tail = l := List.takeWhile_append_dropWhile
  have hlead : lead ≠ [] := fun he => by
    have hh : lead.length = leftCount l := rfl
    rw [he] at hh
    simp at hh
    omega
  have htail : tail ≠ [] := fun he => by
    rw [he, List.append_nil] at hall
    have hh : lead.length = leftCount l := rfl
    rw [hall] at hh
    omega
  have hlast (w : Runs) (hne : w ≠ []) : ∃ pre q, w = pre ++ [q] := by
    induction w using List.reverseRecOn with
    | nil => exact (hne rfl).elim
    | append_singleton w q _ => exact ⟨w, q, rfl⟩
  obtain ⟨pre, ⟨a₀,b⟩, hpre⟩ := hlast lead hlead
  cases ht : tail with
  | nil => exact (htail ht).elim
  | cons p rest =>
    obtain ⟨a,d⟩ := p
    have hgood (q : ℕ × ℕ) (hq : q ∈ pre ++ [(a₀,b)]) : leftRem q = true := by
      have hh : q ∈ l.takeWhile leftRem := by
        change q ∈ lead
        rwa [hpre]
      exact List.mem_takeWhile_imp hh
    obtain ⟨rfl, hbo⟩ := leftRem_true.mp (hgood (a₀,b) (by simp))
    refine ⟨pre, b, a, d, rest, ?_, ?_, hbo, drop_left_head l ht⟩
    · simpa [hpre, ht, List.append_assoc] using hall.symm
    · exact (left_length_iff _).mpr (fun q hq => hgood q (by simp [hq]))

private theorem odd_limited (l : Runs) (hodd : Odd (word l).length) :
    leftCount l + rightCount l < l.length := by
  obtain ⟨pre,a,b,post,rfl,h⟩ := odd_split l hodd
  rw [left_stop pre post (even_word_odd_pair_notL (a,b) h),
    right_stop pre post (even_word_odd_pair_notR (a,b) h), List.length_append, List.length_cons]
  have h₁ := left_le pre
  have h₂ := right_le post
  omega

set_option maxHeartbeats 3000000 in
private theorem odd_score_odd_left (l : Runs) (hl : Pos l) (hodd : Odd (word l).length)
    (hs : Odd (score l)) (hL : 0 < leftCount l) :
    ∃ r, Pos r ∧ MoveWord (word l) (word r) ∧ Even (word r).length ∧ Even (score r) := by
  have hLR := odd_limited l hodd
  obtain ⟨pre,b,a,d,rest,rfl,hpre,hbOdd,hblock⟩ :=
    last_left_pair l hL (by omega)
  let post : Runs := (a,d)::rest
  change Pos (pre++(1,b)::post) at hl
  change Odd (word (pre++(1,b)::post)).length at hodd
  change Odd (score (pre++(1,b)::post)) at hs
  have hpair : leftRem (1,b) = true := leftRem_true.mpr ⟨rfl,hbOdd⟩
  have hleft : leftCount (pre++(1,b)::post) = pre.length+1 := by
    rw [left_append,hpre,if_pos rfl,left_cons,hpair,if_pos rfl]
    simp [post,left_cons,hblock]
  have hrupper : rightCount post < post.length := by
    change leftCount (pre++(1,b)::post) + rightCount (pre++(1,b)::post) <
      (pre++(1,b)::post).length at hLR
    rw [hleft, List.length_append, List.length_cons] at hLR
    have hr := right_append (pre++[(1,b)]) post
    rw [List.append_assoc, List.singleton_append] at hr
    omega
  have hright_eq (p : ℕ × ℕ) : rightCount (pre++p::post) = rightCount post := by
    rw [show pre++p::post = (pre++[p])++post by simp, right_append, if_neg hrupper.ne, add_zero]
  have hsOld : Odd (pre.length+1+rightCount post) := by
    simpa only [score_odd_word _ hodd, hleft, hright_eq] using hs
  obtain ⟨hprePos,hbd,hposPost⟩ := (pos_append.mp hl).imp_right pos_cons.mp
  have hbPos : 0 < b := hbd.2
  obtain ⟨hPosPair, hPosRest⟩ := pos_cons.mp (show Pos ((a,d)::rest) from hposPost)
  have ha : 0 < a := hPosPair.1
  have hRowEver : Even (word (rowDelete pre 1 b post)).length := by
    have hh := row_word_length (pre:=pre) (post:=post) (a:=1) hbPos
    have hne : post ≠ [] := by simp [post]
    simp only [hne, and_false, if_false] at hh
    rw [Nat.even_iff]
    rw [Nat.odd_iff] at hodd
    omega
  by_cases hb : 1 < b
  · have hStop : leftRem (1,b-1) = false := by
      by_contra h
      have hh := (leftRem_true.mp (Bool.eq_true_of_not_eq_false h)).2
      rw [Nat.odd_iff] at hh hbOdd
      omega
    refine ⟨rowDelete pre 1 b post, row_pos hl, row_move hl, hRowEver, ?_⟩
    rw [rowDelete,if_pos hb,score,left_stop pre post hStop,hpre,hright_eq]
    have hprelen : pre.length+rightCount post ≤ (pre++(1,b-1)::post).length := by
      rw [List.length_append]
      change _ ≤ pre.length+(post.length+1)
      omega
    rw [Nat.min_eq_right hprelen]
    rw [Nat.even_iff]
    rw [Nat.odd_iff] at hsOld
    omega
  · have hb1 : b = 1 := by omega
    subst b
    have holdStop : ¬(rightCount rest = rest.length ∧ rightRem (a,d) = true) := by
      intro h
      have hh := right_count_step [] rest (a,d)
      rw [List.nil_append,if_pos h,h.1] at hh
      change rightCount ((a,d)::rest) < rest.length+1 at hrupper
      omega
    have holdR : rightCount post = rightCount rest := by
      simpa [post,holdStop] using right_count_step [] rest (a,d)
    by_cases hnew : rightCount rest = rest.length ∧ rightRem (1+a,d) = true
    · obtain ⟨hd, hea⟩ := rightRem_true.mp hnew.2
      have ha' : 1 < a := by rw [Nat.odd_iff] at hea; omega
      have hRight : rightRem (a-1,d) = true := by
        apply rightRem_true.mpr
        refine ⟨hd, ?_⟩
        rw [Nat.odd_iff] at hea ⊢
        omega
      let pre' := pre++[(1,1)]
      have he : pre'++(a,d)::rest = pre++(1,1)::post := by simp [pre',post,List.append_assoc]
      have hprime : Pos (pre'++(a,d)::rest) := by rwa [he]
      have hp' : Pos pre' := (pos_append.mp hprime).1
      refine ⟨pre'++(a-1,d)::rest, pos_append.mpr ⟨hp',pos_cons.mpr ⟨⟨by omega,hPosPair.2⟩,hPosRest⟩⟩,
        ?_,?_,?_⟩
      · rw [← he]
        exact col_shrink_move hprime ha'
      · rw [← he, word_length_split] at hodd
        rw [word_length_split,Nat.even_iff]
        rw [Nat.odd_iff] at hodd
        omega
      · have hfull : leftCount pre' = pre'.length := by
          rw [left_append,hpre,if_pos rfl,List.length_append,List.length_singleton,left_cons,
            if_pos (leftRem_true.mpr ⟨rfl,by decide⟩)]
          rfl
        have hL' : pre'.length ≤ leftCount (pre'++(a-1,d)::rest) := by
          rw [left_append,hfull,if_pos rfl]
          omega
        have hR' : rest.length+1 ≤ rightCount (pre'++(a-1,d)::rest) := by
          rw [right_count_step,if_pos ⟨hnew.1,hRight⟩,hnew.1]
          omega
        rw [score,Nat.min_eq_left (by simp only [List.length_append,List.length_cons]; omega),
          List.length_append,List.length_cons]
        rw [Nat.even_iff]
        rw [holdR,hnew.1,Nat.odd_iff] at hsOld
        simp [pre']
        omega
    · have hStop : leftRem (1+a,d) = false := by
        by_contra h
        have hh := (leftRem_true.mp (Bool.eq_true_of_not_eq_false h)).1
        omega
      refine ⟨rowDelete pre 1 1 post,row_pos hl,row_move hl,hRowEver,?_⟩
      have hres : rowDelete pre 1 1 post = pre++(1+a,d)::rest := by simp [rowDelete,post]
      rw [hres,score,left_stop pre rest hStop,hpre,right_count_step,if_neg hnew,add_zero]
      rw [Nat.min_eq_right (by simp only [List.length_append,List.length_cons]; have := right_le rest; omega)]
      rw [holdR,Nat.odd_iff] at hsOld
      rw [Nat.even_iff]
      omega

private theorem odd_child_exists {l : Runs} (hl : Pos l) (ho : Odd (word l).length) :
    ∃ r, Pos r ∧ MoveWord (word l) (word r) ∧ Even (word r).length ∧ Even (score r) := by
  by_cases he : Even (score l)
  · exact odd_even_score_child hl ho he
  · have hO := Nat.not_even_iff_odd.mp he
    by_cases hL : 0 < leftCount l
    · exact odd_score_odd_left l hl ho hO hL
    · have hR : 0 < rightCount l := by
        have hcalc := score_odd_word l ho
        simp only [Nat.odd_iff] at hO
        omega
      have hlF : 0 < leftCount (flipRuns l) := by rwa [right_left_flip]
      have hoF : Odd (word (flipRuns l)).length := by rwa [word_flipRuns,flipWord_length]
      have hsF : Odd (score (flipRuns l)) := by rwa [score_flip]
      obtain ⟨r,hr,hm,her,hes⟩ := odd_score_odd_left (flipRuns l) (pos_flipRuns hl) hoF hsF hlF
      obtain ⟨hp,hM,hE⟩ := mirror_child hr hm her
      exact ⟨flipRuns r,hp,hM,hE,by rwa [score_flip]⟩

private theorem losing_classification (P : Set (List Bool))
    (hP : ∀ w, Valid w → (w ∈ P ↔ ∀ i, i < w.length → delete w i ∉ P))
    (l : Runs) (hl : Pos l) (n : ℕ) (hn : (word l).length = n) :
    word l ∈ P ↔ Even (word l).length ∧ Even (score l) := by
  induction n using Nat.strong_induction_on generalizing l with
  | h n ih =>
    have hc (r : Runs) (hr : Pos r) (hm : MoveWord (word l) (word r)) :
        word r ∈ P ↔ Even (word r).length ∧ Even (score r) :=
      ih (word r).length (hn ▸ move_smaller hm) r hr rfl
    rw [hP _ (word_valid l hl)]
    by_cases hE : Even (word l).length
    · constructor
      · intro hnone
        refine ⟨hE,?_⟩
        by_contra hbad
        have hs : 0 < score l := by simp only [Nat.even_iff] at hbad; omega
        obtain ⟨r,hr,hm,he,hd⟩ := even_child_exists hl hs hE
        have hes : Even (score r) := by
          simp only [Nat.even_iff] at hbad ⊢
          omega
        have hp := (hc r hr hm).mpr ⟨he,hes⟩
        obtain ⟨i,hi,hi'⟩ := hm
        exact hnone i hi (hi'.symm ▸ hp)
      · rintro ⟨_,hs⟩ i hi
        obtain ⟨r,hr,hd,hscore⟩ := run_child l hl i hi
        rw [hd, hc r hr ⟨i,hi,hd⟩]
        rintro ⟨her,hsr⟩
        have hdrop := hscore hE her
        simp only [Nat.even_iff] at hs hsr
        omega
    · have ho := Nat.not_even_iff_odd.mp hE
      obtain ⟨r,hr,hm,her,hsr⟩ := odd_child_exists hl ho
      have hp := (hc r hr hm).mpr ⟨her,hsr⟩
      obtain ⟨i,hi,hi'⟩ := hm
      constructor
      · intro hh
        exact (hh i hi (hi'.symm ▸ hp)).elim
      · intro h
        exact (hE h.1).elim

theorem even_length_of_losing (P : Set (List Bool))
    (hP : ∀ w, Valid w → (w ∈ P ↔ ∀ i, i < w.length → delete w i ∉ P))
    (w : List Bool) (hw : Valid w) (hl : w ∈ P) : Even w.length := by
  obtain ⟨l,hp,rfl⟩ := valid_parse hw
  exact ((losing_classification P hP l hp _ rfl).mp hl).1

end OMA.S_arxiv_2606_16828.WordGame

namespace OMA.S_arxiv_2606_16828.FerrersBridge

open WordGame (Valid trim delete)

private def zeroCount (w : List Bool) := w.count false
private def oneCount (w : List Bool) := w.count true

private def read : ℕ → List Bool → Multiset ℕ
  | _, [] => 0
  | x, false :: w => read (x+1) w
  | x, true :: w => if x = 0 then read x w else x ::ₘ read x w

def decode (w : List Bool) : Multiset ℕ := read 0 w

private def write : ℕ → List ℕ → List Bool
  | _, [] => []
  | x, p::ps => List.replicate (p-x) false ++ true :: write p ps

private theorem read_append (x : ℕ) (u v : List Bool) :
    read x (u++v) = read x u + read (x+zeroCount u) v := by
  induction u generalizing x with
  | nil => simp [read, zeroCount]
  | cons b u ih =>
    cases b
    · simpa [read, zeroCount, List.count_cons, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ih (x+1)
    · by_cases h : x = 0 <;> simp [read, zeroCount, h, ih, Multiset.cons_add]

private theorem read_replicate (x n : ℕ) (w : List Bool) :
    read x (List.replicate n false ++ w) = read (x+n) w := by
  induction n generalizing x with
  | zero => simp
  | succ n ih => simpa [List.replicate_succ, read, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (x+1)

private theorem read_write (x : ℕ) (ps : List ℕ) (hs : ps.Pairwise (· ≤ ·))
    (hx : ∀ p ∈ ps, x ≤ p) (hp : ∀ p ∈ ps, 0 < p) : read x (write x ps) = (ps : Multiset ℕ) := by
  induction ps generalizing x with
  | nil => rfl
  | cons p ps ih =>
    obtain ⟨hle, htail⟩ := List.pairwise_cons.mp hs
    have hpx : x ≤ p := hx p (by simp)
    have hp' : p ≠ 0 := (hp p (by simp)).ne'
    have hh := ih p htail hle (fun q hq => hp q (by simp [hq]))
    simp only [write, read_replicate]
    rw [Nat.add_sub_of_le hpx, read, if_neg hp', hh]
    rfl

private theorem read_all_zeros (x : ℕ) (w : List Bool) (h : ∀ b ∈ w, b = false) : read x w = 0 := by
  induction w generalizing x with
  | nil => rfl
  | cons b w ih =>
    have hb := h b (by simp)
    subst b
    exact ih (x+1) (fun c hc => h c (by simp [hc]))

private theorem read_trim_front (w : List Bool) : read 0 (w.dropWhile id) = read 0 w := by
  induction w with
  | nil => rfl
  | cons b w ih => cases b <;> simp [read, ih]

private theorem read_trim_back (x : ℕ) (w : List Bool) :
    read x ((w.reverse.dropWhile fun b => !b).reverse) = read x w := by
  let tail := (w.reverse.takeWhile fun b => !b).reverse
  let front := (w.reverse.dropWhile fun b => !b).reverse
  have hw : front ++ tail = w := by
    dsimp [front, tail]
    rw [← List.reverse_append, List.takeWhile_append_dropWhile, List.reverse_reverse]
  have htail : ∀ b ∈ tail, b = false := by
    intro b hb
    have hb' : b ∈ w.reverse.takeWhile (fun c => !c) := by simpa [tail] using hb
    have h := List.mem_takeWhile_imp hb'
    cases b <;> simp_all
  change read x front = read x w
  conv_rhs => rw [← hw]
  rw [read_append, read_all_zeros _ _ htail, add_zero]

theorem decode_trim (w : List Bool) : decode (trim w) = decode w := by
  unfold trim decode
  rw [read_trim_back, read_trim_front]

theorem represents (htrim : ∀ w, Valid (trim w)) (l : Multiset ℕ) (hp : ∀ p ∈ l, 0 < p) :
    ∃ w, Valid w ∧ decode w = l := by
  let ps := l.sort (· ≤ ·)
  refine ⟨trim (write 0 ps), htrim _, ?_⟩
  rw [decode_trim]
  change read 0 (write 0 ps) = l
  rw [read_write 0 ps (l.pairwise_sort _) (fun _ _ => Nat.zero_le _) (fun p hp' => hp p (by simpa [ps] using hp'))]
  exact l.sort_eq _

private theorem read_bounds (x : ℕ) (w : List Bool) (p : ℕ) (h : p ∈ read x w) :
    0 < p ∧ x ≤ p ∧ p ≤ x+zeroCount w := by
  induction w generalizing x with
  | nil => simp [read] at h
  | cons b w ih =>
    cases b
    · have ⟨hp, hlo, hhi⟩ := ih (x+1) h
      refine ⟨hp, by omega, ?_⟩
      simp [zeroCount] at hhi ⊢
      omega
    · by_cases hx : x = 0
      · have hh : p ∈ read x w := by simpa [read, hx] using h
        simpa [zeroCount, List.count_cons] using ih x hh
      · have hh : p = x ∨ p ∈ read x w := by simpa [read, hx] using h
        rcases hh with rfl | hh
        · exact ⟨Nat.pos_of_ne_zero hx, le_rfl, by omega⟩
        · simpa [zeroCount, List.count_cons] using ih x hh

theorem decode_positive (w : List Bool) : ∀ p ∈ decode w, 0 < p := fun p h => (read_bounds 0 w p h).1

private theorem read_card (x : ℕ) (hx : 0 < x) (w : List Bool) :
    (read x w).card = oneCount w := by
  induction w generalizing x with
  | nil => rfl
  | cons b w ih =>
    cases b
    · simpa [read, oneCount, List.count_cons] using ih (x+1) (by omega)
    · simp [read, oneCount, show x ≠ 0 by omega, ih x hx]

private theorem read_sup_last (x : ℕ) (hx : 0 < x) (w : List Bool) :
    (read x (w++[true])).sup = x+zeroCount w := by
  apply le_antisymm
  · apply Multiset.sup_le.mpr
    intro p hp
    simpa [zeroCount, List.count_append] using (read_bounds x (w++[true]) p hp).2.2
  · apply Multiset.le_sup
    rw [read_append, read, if_neg (by omega : x+zeroCount w ≠ 0)]
    simp [read]

private theorem counts_add (w : List Bool) : zeroCount w + oneCount w = w.length := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    simp only [zeroCount, oneCount] at ih
    cases b <;> simp [zeroCount, oneCount]
    all_goals omega

theorem sizes (w : List Bool) (hw : Valid w) :
    (decode w).card = oneCount w ∧ (decode w).sup = zeroCount w := by
  rcases hw with rfl | ⟨mid, rfl⟩
  · simp [decode, read, zeroCount, oneCount]
  · constructor
    · change (read 1 (mid++[true])).card = oneCount (false :: (mid++[true]))
      simpa [oneCount, List.count_cons] using read_card 1 (by decide) (mid++[true])
    · change (read 1 (mid++[true])).sup = zeroCount (false :: (mid++[true]))
      rw [read_sup_last 1 (by decide)]
      simp [zeroCount, List.count_append, Nat.add_comm]

theorem length_eq (w : List Bool) (hw : Valid w) : w.length = (decode w).card + (decode w).sup := by
  rw [(sizes w hw).1, (sizes w hw).2, Nat.add_comm, counts_add]

private def column (j : ℕ) (l : Multiset ℕ) :=
  (l.map (fun p => if j ≤ p then p-1 else p)).filter (0 < ·)

private theorem column_cons_before (j p : ℕ) (l : Multiset ℕ) (hp : 0 < p) (h : p < j) :
    column j (p ::ₘ l) = p ::ₘ column j l := by
  simp [column, not_le.mpr h, hp]

private theorem column_front (j x : ℕ) (hj : 1 ≤ j) (h : j ≤ x) (w : List Bool) :
    column j (read x w) = read (x-1) w := by
  induction w generalizing x with
  | nil => simp [column, read]
  | cons b w ih =>
    cases b
    · simpa [read, show x+1-1 = x by omega, show x-1+1 = x by omega] using
        ih (x+1) (by omega)
    · have hx : x ≠ 0 := by omega
      have hstep := ih x h
      by_cases hs : x-1 = 0
      · simp [read, column, hx, hs, h] at hstep ⊢
        exact hstep
      · have hspos : 0 < x-1 := by omega
        simp [read, column, hx, hs, hspos, h] at hstep ⊢
        exact hstep

private theorem column_unchanged (j : ℕ) (l : Multiset ℕ) (h : ∀ p ∈ l, 0 < p ∧ p < j) :
    column j l = l := by
  induction l using Multiset.induction_on with
  | empty => simp [column]
  | cons p l ih =>
    have hp := h p (by simp)
    rw [column_cons_before j p l hp.1 hp.2, ih (fun q hq => h q (by simp [hq]))]

private theorem erase_at_split (u v : List Bool) (b : Bool) :
    (u++b::v).eraseIdx u.length = u++v := by
  induction u with
  | nil => simp
  | cons x u ih => simp [List.eraseIdx_cons_succ, ih]

private theorem index_split (w : List Bool) (i : ℕ) (hi : i < w.length) :
    ∃ u v : List Bool, ∃ b, w = u++b::v ∧ i = u.length := by
  induction i generalizing w with
  | zero => cases w with
    | nil => simp at hi
    | cons b w => exact ⟨[], w, b, rfl, rfl⟩
  | succ i ih => cases w with
    | nil => simp at hi
    | cons b w =>
      obtain ⟨u, v, c, rfl, he⟩ := ih w (by simpa using hi)
      exact ⟨b::u, v, c, rfl, by simp [he]⟩

private theorem row_split (x : ℕ) (w : List Bool) (p : ℕ) (hp : p ∈ read x w) :
    ∃ u v, w = u++true::v ∧ x+zeroCount u = p := by
  induction w generalizing x with
  | nil => simp [read] at hp
  | cons b w ih =>
    cases b
    · obtain ⟨u, v, rfl, hh⟩ := ih (x+1) hp
      exact ⟨false::u, v, rfl, by simpa [zeroCount, List.count_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh⟩
    · have carry (hh : p ∈ read x w) : ∃ u v, true::w = u++true::v ∧ x+zeroCount u = p := by
        obtain ⟨u, v, rfl, hu⟩ := ih x hh
        exact ⟨true::u, v, rfl, by simpa [zeroCount, List.count_cons] using hu⟩
      by_cases hx : x = 0
      · exact carry (by simpa [read, hx] using hp)
      · have hh : p = x ∨ p ∈ read x w := by simpa [read, hx] using hp
        rcases hh with rfl | hh
        · exact ⟨[], w, rfl, by simp [zeroCount]⟩
        · exact carry hh

private theorem col_split (w : List Bool) (j : ℕ) (hj : 1 ≤ j) (h : j ≤ zeroCount w) :
    ∃ u v, w = u++false::v ∧ zeroCount u+1 = j := by
  induction w generalizing j with
  | nil => simp [zeroCount] at h; omega
  | cons b w ih =>
    cases b
    · by_cases h1 : j = 1
      · exact ⟨[], w, rfl, by simp [zeroCount, h1]⟩
      · have htail : j-1 ≤ zeroCount w := by
          simp only [zeroCount, List.count_cons, beq_self_eq_true, if_true] at h ⊢
          omega
        obtain ⟨u, v, rfl, hh⟩ := ih (j-1) (by omega) htail
        refine ⟨false::u, v, rfl, ?_⟩
        simp only [zeroCount, List.count_cons, beq_self_eq_true, if_true] at hh ⊢
        omega
    · obtain ⟨u, v, rfl, hh⟩ := ih j hj (by simpa [zeroCount, List.count_cons] using h)
      exact ⟨true::u, v, rfl, by simpa [zeroCount, List.count_cons] using hh⟩

private theorem read_row_change (u v : List Bool) (h : 0 < zeroCount u) :
    zeroCount u ∈ decode (u++true::v) ∧
      decode (u++v) = (decode (u++true::v)).erase (zeroCount u) := by
  simp [decode, read_append, read, h.ne', Multiset.add_cons]

private theorem read_col_change (u v : List Bool) :
    decode (u++v) = column (zeroCount u+1) (decode (u++false::v)) := by
  have h₁ : column (zeroCount u+1) (read 0 u) = read 0 u :=
    column_unchanged _ _ (fun p hp => ⟨(read_bounds 0 u p hp).1, by have := (read_bounds 0 u p hp).2.2; omega⟩)
  have h₂ : column (zeroCount u+1) (read (zeroCount u+1) v) = read (zeroCount u) v := by
    simpa using column_front (zeroCount u+1) (zeroCount u+1) (by omega) le_rfl v
  simp only [decode, read_append, zero_add, read]
  change _ = column (zeroCount u+1) (read 0 u + read (zeroCount u+1) v)
  have hadd : column (zeroCount u+1) (read 0 u + read (zeroCount u+1) v) =
      column (zeroCount u+1) (read 0 u) + column (zeroCount u+1) (read (zeroCount u+1) v) := by
    simp [column, Multiset.filter_add]
  rw [hadd, h₁, h₂]

private theorem zero_before_true (u v : List Bool) (hw : Valid (u++true::v)) : 0 < zeroCount u := by
  rcases hw with h | ⟨m, h⟩
  · simp at h
  · cases u with
    | nil => simp at h
    | cons b u =>
      have hb : b = false := (List.cons.inj h).1
      subst b
      simp [zeroCount]

theorem bit_move (w : List Bool) (hw : Valid w) (i : ℕ) (hi : i < w.length) :
    Move (decode w) (decode (delete w i)) := by
  obtain ⟨u, v, b, rfl, rfl⟩ := index_split w i hi
  unfold delete
  rw [decode_trim, erase_at_split]
  cases b
  · apply Or.inr
    refine ⟨zeroCount u+1, by omega, ?_, read_col_change u v⟩
    rw [(sizes _ hw).2]
    simp [zeroCount, List.count_append]
  · exact Or.inl ⟨zeroCount u, (read_row_change u v (zero_before_true u v hw)).1,
      (read_row_change u v (zero_before_true u v hw)).2⟩

theorem move_bit (w : List Bool) (hw : Valid w) (l : Multiset ℕ) (h : Move (decode w) l) :
    ∃ i < w.length, decode (delete w i) = l := by
  rcases h with ⟨p, hp, rfl⟩ | ⟨j, hj, hsup, rfl⟩
  · obtain ⟨u, v, rfl, he⟩ := row_split 0 w p hp
    have hh : zeroCount u = p := by simpa using he
    have h0 := zero_before_true u v hw
    refine ⟨u.length, by simp, ?_⟩
    rw [delete, decode_trim, erase_at_split, ← hh]
    exact (read_row_change u v h0).2
  · rw [(sizes w hw).2] at hsup
    obtain ⟨u, v, rfl, he⟩ := col_split w j hj hsup
    refine ⟨u.length, by simp, ?_⟩
    rw [delete, decode_trim, erase_at_split, ← he]
    exact read_col_change u v

theorem partition_even
    (htrim : ∀ w, Valid (trim w))
    (hgame : ∀ (Q : Set (List Bool)),
      (∀ w, Valid w → (w ∈ Q ↔ ∀ i, i < w.length → delete w i ∉ Q)) →
      ∀ w, Valid w → w ∈ Q → Even w.length)
    (P : Set (Multiset ℕ)) (hP : IsPSet P) (l : Multiset ℕ)
    (hpositive : ∀ p ∈ l, 0 < p) (hl : l ∈ P) : Even (l.card + l.sup) := by
  let Q : Set (List Bool) := {w | decode w ∈ P}
  have hQ (w : List Bool) (hw : Valid w) :
      w ∈ Q ↔ ∀ i, i < w.length → delete w i ∉ Q := by
    change decode w ∈ P ↔ ∀ i, i < w.length → decode (delete w i) ∉ P
    rw [hP]
    constructor
    · intro h i hi
      exact h _ (bit_move w hw i hi)
    · intro h m hm
      obtain ⟨i, hi, rfl⟩ := move_bit w hw m hm
      exact h i hi
  obtain ⟨w, hw, he⟩ := represents htrim l hpositive
  have hwp : w ∈ Q := by change decode w ∈ P; simpa [he] using hl
  have heven := hgame Q hQ w hw hwp
  rwa [length_eq w hw, he] at heven

end OMA.S_arxiv_2606_16828.FerrersBridge

theorem OMA.solution : type_of% @OMA.S_arxiv_2606_16828.main :=
  OMA.S_arxiv_2606_16828.FerrersBridge.partition_even
    OMA.S_arxiv_2606_16828.WordGame.trim_valid
    OMA.S_arxiv_2606_16828.WordGame.even_length_of_losing
