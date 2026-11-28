import OMAReductions.R_GracefulLabeling_graceful_tree_conjecture_R2
import Mathlib

/-!
# Simultaneous edge divisibility counts in a rooted tree

Credit goes to @ysanatomic.

Order the nonroot vertices in pairs, each consisting of two siblings or two
consecutive vertices on a path. Three pairs form a block of six. For each
possible pattern of parents and previously assigned residues, a finite
certificate selects a permutation of the six residues. The numbers of edges
whose endpoint residues agree modulo two, three, and six are three, two, and
one respectively. The unique edge per block with equal residues modulo six
defines a parent on the smaller set of blocks. Induction on this smaller
tree controls the higher powers of six. The construction puts zero next to
the prescribed root and preserves the largest multiple at each scale.
-/

namespace OMA.SixSpectrum


open SimpleGraph
namespace GracefulLabeling

private theorem depth_ordering {V : Type*} [Fintype V] (T : SimpleGraph V) (ht : T.IsTree)
    (root : V) {n : ℕ} (hn : Fintype.card V = n + 1) :
    ∃ e : V ≃ Fin (n+1), e root = Fin.last n ∧
      ∀ {x y}, T.dist root y < T.dist root x → e x < e y := by
  classical
  let t := Fintype.equivFin V
  let key (x : V) := toLex (OrderDual.toDual (T.dist root x), t x)
  have key_inj : Function.Injective key := by
    intro x y h
    exact t.injective (congrArg (fun k => (ofLex k).2) h)
  let : LinearOrder V := LinearOrder.lift' key key_inj
  let e := (Fintype.orderIsoFinOfCardEq V hn).symm
  have hdec {x y : V} (h : T.dist root y < T.dist root x) : e x < e y := by
    apply e.strictMono
    change key x < key y
    exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl h)
  refine ⟨e.toEquiv,?_,fun h => hdec h⟩
  change e root = Fin.last n
  let y := e.symm (Fin.last n)
  by_contra h
  have hy : root ≠ y := by
    intro hr
    apply h
    simpa [y] using congrArg e hr
  have hxy := ht.connected.pos_dist_of_ne hy
  have hlt : e y < e root := hdec (by simpa using hxy)
  have hl : e y = Fin.last n := e.apply_symm_apply _
  rw [hl] at hlt
  exact (not_lt_of_ge (Fin.le_last _)) hlt

/-- A prescribed root can be numbered last, with every parent greater than its
child. The unordered parent edges of all nonroot indices enumerate the edge set. -/
theorem exists_ordered_parent {V : Type*} [Fintype V] (T : SimpleGraph V) (ht : T.IsTree)
    (root : V) {n : ℕ} (hn : Fintype.card V = n+1) :
    ∃ (e : V ≃ Fin (n+1)) (p : ℕ → ℕ) (E : Fin n ≃ T.edgeSet)
      (hp : ∀ v < n, v < p v ∧ p v ≤ n), e root = Fin.last n ∧
      ∀ i : Fin n, (E i).val = s(e.symm i.castSucc,
        e.symm ⟨p i.val,Nat.lt_succ_of_le (hp i.val i.isLt).2⟩) := by
  classical
  obtain ⟨e,hr,hdec⟩ := depth_ordering T ht root hn
  let v (i : Fin n) := e.symm i.castSucc
  have hnr (i : Fin n) : root ≠ v i := by
    intro h
    have he : Fin.last n = i.castSucc := by simpa [v,hr] using congrArg e h
    exact (Nat.ne_of_gt i.isLt) (congrArg Fin.val he)
  have existsParent (i : Fin n) : ∃ y, T.Adj (v i) y ∧ e (v i) < e y := by
    obtain ⟨w,hw⟩ := ht.connected.exists_walk_length_eq_dist root (v i)
    have hnil := w.not_nil_of_ne (hnr i)
    refine ⟨w.penultimate,(w.adj_penultimate hnil).symm,hdec ?_⟩
    have h₁ := T.dist_le w.dropLast
    have h₂ := w.length_dropLast_add_one hnil
    omega
  choose par hadj hlt using existsParent
  let p (z : ℕ) := if h : z < n then (e (par ⟨z,h⟩)).val else n
  have hpi (i : Fin n) : p i.val = (e (par i)).val := dif_pos i.isLt
  have hp (z : ℕ) (hz : z < n) : z < p z ∧ p z ≤ n := by
    let i : Fin n := ⟨z,hz⟩
    rw [show z = i.val from rfl, hpi i]
    have hlt' : i.castSucc < e (par i) := by simpa [v] using hlt i
    exact ⟨hlt',Nat.le_of_lt_succ (e (par i)).isLt⟩
  let ar (i : Fin n) : T.edgeSet := ⟨s(v i,par i),hadj i⟩
  have ari : Function.Injective ar := by
    intro i j he
    have he' : s(v i,par i) = s(v j,par j) := congrArg Subtype.val he
    rcases Sym2.eq_iff.mp he' with h | h
    · apply Fin.ext
      simpa [v] using congrArg (fun x => (e x).val) h.1
    · have hi := hlt i
      have hj := hlt j
      rw [h.1,h.2] at hi
      exact (lt_asymm hi hj).elim
  have hec : Fintype.card (Fin n) = Fintype.card T.edgeSet := by
    rw [Fintype.card_fin,T.card_edgeSet]
    have h := ht.card_edgeFinset
    omega
  let E := Equiv.ofBijective ar ((Fintype.bijective_iff_injective_and_card ar).mpr ⟨ari,hec⟩)
  refine ⟨e,p,E,hp,hr,?_⟩
  intro i
  have hepar : (⟨p i.val,Nat.lt_succ_of_le (hp i.val i.isLt).2⟩ : Fin (n+1)) = e (par i) :=
    Fin.ext (hpi i)
  rw [hepar,e.symm_apply_apply]
  rfl


end GracefulLabeling



namespace GracefulLabeling.BinaryParents

private theorem peel {n : ℕ} (p : ℕ → ℕ) (S : Finset ℕ) (hsize : 2 ≤ S.card)
    (hp : ∀ x ∈ S, x < p x ∧ p x ≤ n) (hclosed : ∀ x ∈ S, p x ∈ S ∨ p x = n) :
    ∃ x ∈ S, ∃ y ∈ S, x ≠ y ∧ p y ≠ x ∧ (p x = p y ∨ p x = y) ∧
      ∀ z ∈ S, z ≠ x → z ≠ y → p z ≠ x ∧ p z ≠ y := by
  obtain ⟨x,hx,hmin⟩ := S.exists_min_image p (Finset.card_pos.mp (by omega))
  have hxlt := (hp x hx).1
  by_cases hsib : ∃ y ∈ S, y ≠ x ∧ p y = p x
  · obtain ⟨y,hy,hyx,he⟩ := hsib
    have hylt := (hp y hy).1
    refine ⟨x,hx,y,hy,hyx.symm,by omega,Or.inl he.symm,?_⟩
    intro z hz _ _
    have hm := hmin z hz
    omega
  · have hun (z) (hz : z ∈ S) (he : p z = p x) : z = x := by
      by_contra hn
      exact hsib ⟨z,hz,hn,he⟩
    have hpx : p x ∈ S := by
      apply (hclosed x hx).resolve_right
      intro he
      have hle : S.card ≤ 1 := Finset.card_le_one.mpr (by
        intro z hz w hw
        have all (v) (hv : v ∈ S) : v = x := hun v hv (le_antisymm (he ▸ (hp v hv).2) (hmin v hv))
        exact (all z hz).trans (all w hw).symm)
      omega
    have hpl := (hp (p x) hpx).1
    refine ⟨x,hx,p x,hpx,Nat.ne_of_lt hxlt,by omega,Or.inr rfl,?_⟩
    intro z hz hzx _
    have hm := hmin z hz
    exact ⟨by omega,fun he => hzx (hun z hz he)⟩

/-- The nonroot vertices, listed child before parent. Consecutive pairs
are siblings or a child and its parent. One final vertex may be left over. -/
theorem exists_paired_list {n : ℕ} (p : ℕ → ℕ) (S : Finset ℕ)
    (hp : ∀ x ∈ S, x < p x ∧ p x ≤ n) (hclosed : ∀ x ∈ S, p x ∈ S ∨ p x = n) :
    ∃ l : List ℕ, l.Nodup ∧ (∀ z, z ∈ l ↔ z ∈ S) ∧
      l.Pairwise (fun x y => p y ≠ x) ∧
      ∀ b x y, l[2*b]? = some x → l[2*b+1]? = some y → p x = p y ∨ p x = y := by
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    by_cases hsize : 2 ≤ S.card
    · obtain ⟨x,hx,y,hy,hne,hyx,hpair,havo⟩ := peel p S hsize hp hclosed
      let R := (S.erase x).erase y
      have hR (z) : z ∈ R ↔ z ∈ S ∧ z ≠ x ∧ z ≠ y := by simp [R]; tauto
      have hsub : R ⊂ S := Finset.ssubset_iff_subset_ne.mpr ⟨fun z hz => ((hR z).mp hz).1,by
        intro e
        have hxr : x ∈ R := e.symm ▸ hx
        exact ((hR x).mp hxr).2.1 rfl⟩
      have hclosed' (z) (hz : z ∈ R) : p z ∈ R ∨ p z = n := by
        obtain ⟨hz',hzx,hzy⟩ := (hR z).mp hz
        exact (hclosed z hz').imp_left (fun hpz => (hR _).mpr ⟨hpz,havo _ hz' hzx hzy⟩)
      obtain ⟨l,hnd,hm,horder,hpairs⟩ := ih R hsub (fun z hz => hp z ((hR z).mp hz).1) hclosed'
      have hxnl : x ∉ l := fun h => ((hR x).mp ((hm x).mp h)).2.1 rfl
      have hynl : y ∉ l := fun h => ((hR y).mp ((hm y).mp h)).2.2 rfl
      refine ⟨x::y::l, by simp [hne,hxnl,hynl,hnd],?_,?_,?_⟩
      · intro z
        simp only [List.mem_cons,hm,hR]
        by_cases hzx : z = x
        · subst z; simp [hx]
        by_cases hzy : z = y
        · subst z; simp [hy]
        simp [hzx,hzy]
      · simp only [List.pairwise_cons,List.mem_cons,forall_eq_or_imp]
        refine ⟨⟨hyx,?_⟩,?_,horder⟩
        · intro z hz
          obtain ⟨hz',hzx,hzy⟩ := (hR z).mp ((hm z).mp hz)
          exact (havo z hz' hzx hzy).1
        · intro z hz
          obtain ⟨hz',hzx,hzy⟩ := (hR z).mp ((hm z).mp hz)
          exact (havo z hz' hzx hzy).2
      · rintro (_|b) z w hz hw
        · change some x = some z at hz
          change some y = some w at hw
          exact (Option.some.inj hz) ▸ (Option.some.inj hw) ▸ hpair
        · exact hpairs b z w (by simpa [Nat.mul_succ] using hz) (by simpa [Nat.mul_succ] using hw)
    · refine ⟨S.toList,S.nodup_toList,by simp,?_,?_⟩
      · apply List.pairwise_iff_getElem.mpr
        intro i j hi hj hij
        simp at hi hj
        omega
      · intro b x y hx hy
        have hlt := List.getElem?_eq_some_iff.mp hy
        obtain ⟨hj,_⟩ := hlt
        simp at hj
        omega

end GracefulLabeling.BinaryParents

namespace GracefulLabeling.BinaryParents

/-- Permute the indices of any increasing parent map so each complete binary
block consists of siblings or of a child and its parent. The new-to-old index
bijections commute with the parent maps and both fix the root position. -/
theorem reindex {n : ℕ} (p : ℕ → ℕ) (hp : ∀ i<n, i < p i ∧ p i ≤ n) :
    ∃ (r : Fin (n+1) ≃ Fin (n+1)) (s : Fin n ≃ Fin n) (P : ℕ → ℕ)
      (hP : ∀ i<n, i < P i ∧ P i ≤ n), r (Fin.last n) = Fin.last n ∧
      (∀ i : Fin n, r i.castSucc = (s i).castSucc) ∧
      (∀ i : Fin n, (r ⟨P i,Nat.lt_succ_of_le (hP i i.isLt).2⟩).val = p (s i)) ∧
      ∀ b<n/2, P (2*b) = P (2*b+1) ∨ P (2*b) = 2*b+1 := by
  classical
  obtain ⟨l,hnd,hm,ho,hpair⟩ := exists_paired_list p (Finset.range n)
    (fun i hi => hp i (Finset.mem_range.mp hi)) (by
      intro i hi
      have hh := (hp i (Finset.mem_range.mp hi)).2
      exact (lt_or_eq_of_le hh).imp_left Finset.mem_range.mpr)
  have hmem (x) : x ∈ l ↔ x < n := (hm x).trans Finset.mem_range
  have hset : l.toFinset = Finset.range n := by ext x; simpa using hm x
  have hl : l.length = n := by rw [← List.toFinset_card_of_nodup hnd,hset,Finset.card_range]
  let f (i : Fin n) : Fin n :=
    ⟨l[i.val]'(hl ▸ i.isLt),(hmem _).mp (List.getElem_mem _)⟩
  have fi : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    exact hnd.getElem_inj_iff.mp (congrArg Fin.val hij)
  let s := Equiv.ofBijective f (Finite.injective_iff_bijective.mp fi)
  let g (i : Fin (n+1)) := if h : i.val < n then (s ⟨i.val,h⟩).castSucc else Fin.last n
  have gs (i : Fin n) : g i.castSucc = (s i).castSucc := dif_pos i.isLt
  have gr : g (Fin.last n) = Fin.last n := dif_neg (Nat.lt_irrefl _)
  have gi : Function.Injective g := by
    intro i j hij
    refine Fin.lastCases (motive := fun i => ∀ j, g i = g j → i = j) ?_ ?_ i j hij
    · intro j
      refine Fin.lastCases (motive := fun j => g (Fin.last n) = g j → Fin.last n = j) (fun _ => rfl) ?_ j
      intro a he
      rw [gr,gs] at he
      exact ((Fin.castSucc_ne_last _ ) he.symm).elim
    · intro a j
      refine Fin.lastCases (motive := fun j => g a.castSucc = g j → a.castSucc = j) ?_ ?_ j
      · intro he
        rw [gs,gr] at he
        exact ((Fin.castSucc_ne_last _) he).elim
      · intro b he
        rw [gs,gs] at he
        exact congrArg Fin.castSucc (s.injective (Fin.castSucc_inj.mp he))
  let r := Equiv.ofBijective g (Finite.injective_iff_bijective.mp gi)
  let par (i : Fin n) : Fin (n+1) := r.symm ⟨p (s i),Nat.lt_succ_of_le (hp _ (s i).isLt).2⟩
  have par_spec (i : Fin n) : (r (par i)).val = p (s i) := congrArg Fin.val (r.apply_symm_apply _)
  have pg (i : Fin n) : i.val < (par i).val := by
    by_contra h
    have hle : (par i).val ≤ i.val := Nat.le_of_not_gt h
    let j : Fin n := ⟨(par i).val,lt_of_le_of_lt hle i.isLt⟩
    have hej : j.castSucc = par i := Fin.ext rfl
    have he : (s j).val = p (s i) := by
      have h₁ : r j.castSucc = (s j).castSucc := gs j
      rw [hej] at h₁
      exact (congrArg Fin.val h₁).symm.trans (par_spec i)
    rcases lt_or_eq_of_le hle with hj | hj
    · have hne := List.pairwise_iff_getElem.mp ho j.val i.val (hl ▸ j.isLt) (hl ▸ i.isLt) hj
      exact hne he.symm
    · have hji : j = i := Fin.ext hj
      rw [hji] at he
      exact (Nat.ne_of_lt (hp _ (s i).isLt).1) he
  let P (v : ℕ) := if h : v<n then (par ⟨v,h⟩).val else n
  have eqP (i : Fin n) : P i.val = (par i).val := dif_pos i.isLt
  have hP (v) (hv : v<n) : v < P v ∧ P v ≤ n := by
    let i : Fin n := ⟨v,hv⟩
    rw [show v = i.val from rfl,eqP i]
    exact ⟨pg i,Nat.le_of_lt_succ (par i).isLt⟩
  refine ⟨r,s,P,hP,gr,gs,?_,?_⟩
  · intro i
    have hr' : (⟨P i.val,Nat.lt_succ_of_le (hP i i.isLt).2⟩ : Fin (n+1)) = par i := Fin.ext (eqP i)
    rw [hr',par_spec]
  · intro b hb
    let i : Fin n := ⟨2*b,by omega⟩
    let j : Fin n := ⟨2*b+1,by omega⟩
    have h₁ : l[2*b]? = some (s i).val := List.getElem?_eq_getElem (hl ▸ i.isLt)
    have h₂ : l[2*b+1]? = some (s j).val := List.getElem?_eq_getElem (hl ▸ j.isLt)
    change P i.val = P j.val ∨ P i.val = j.val
    rw [eqP i,eqP j]
    rcases hpair b _ _ h₁ h₂ with h | h
    · apply Or.inl
      exact congrArg Fin.val (r.injective (Fin.ext ((par_spec i).trans (h.trans (par_spec j).symm))))
    · apply Or.inr
      have hj : r j.castSucc = (s j).castSucc := gs j
      have he : r (par i) = r j.castSucc := Fin.ext ((par_spec i).trans (h.trans (congrArg Fin.val hj).symm))
      exact congrArg Fin.val (r.injective he)

end GracefulLabeling.BinaryParents

namespace GracefulLabeling.RadixTree

/-- Number vertices from leaves toward the root n. -/
def Parent (n : ℕ) (p : ℕ → ℕ) : Prop := ∀ v < n, v < p v ∧ p v ≤ n

def count (n : ℕ) (p f : ℕ → ℕ) (d : ℕ) : ℕ :=
  ((Finset.range n).filter (fun v => f v % d = f (p v) % d)).card

theorem mod_digits {q : ℕ} (hq : 0 < q) (x y : Fin q) (a b d : ℕ) :
    (q*a+x.val) % (q*d) = (q*b+y.val) % (q*d) ↔ x=y ∧ a%d=b%d := by
  constructor
  · intro h
    have h₁ := congrArg (· % q) h
    have h₂ := congrArg (· / q) h
    simp only [Nat.mod_mul_right_mod,Nat.mul_add_mod,Nat.mod_eq_of_lt x.isLt,
      Nat.mod_eq_of_lt y.isLt] at h₁
    simp only [Nat.mod_mul_right_div_self,Nat.mul_add_div hq,
      Nat.div_eq_of_lt x.isLt,Nat.div_eq_of_lt y.isLt,Nat.add_zero] at h₂
    exact ⟨Fin.ext h₁,h₂⟩
  · rintro ⟨rfl,h⟩
    have e : a ≡ b [MOD d] := h
    have e' : q*a ≡ q*b [MOD q*d] := Nat.ModEq.mul_left' q e
    exact e'.add_right x.val

def digit {q : ℕ} (hq : 0 < q) (v : ℕ) : Fin q := ⟨v%q,Nat.mod_lt _ hq⟩

def pos {q : ℕ} (b : ℕ) (i : Fin q) : ℕ := q*b+i

@[simp] theorem pos_digit {q : ℕ} (hq : 0<q) (v : ℕ) :
    pos (v/q) (digit hq v) = v := by
  exact Nat.div_add_mod v q

@[simp] theorem pos_div {q : ℕ} (hq : 0<q) (b : ℕ) (i : Fin q) :
    pos b i /q = b := by
  simp [pos,Nat.mul_add_div hq,Nat.div_eq_of_lt i.isLt]

@[simp] theorem digit_pos {q : ℕ} (hq : 0<q) (b : ℕ) (i : Fin q) :
    digit hq (pos b i) = i := by
  apply Fin.ext
  simp [digit,pos,Nat.mod_eq_of_lt i.isLt]

theorem pos_lt {q : ℕ} (hq : 0<q) {b n : ℕ} (hb : b<n/q) (i : Fin q) :
    pos b i < n := by
  dsimp [pos]
  have hi := i.isLt
  have h₂ := (Nat.le_div_iff_mul_le hq).mp (show b+1 ≤ n/q by omega)
  rw [Nat.add_mul,Nat.one_mul,Nat.mul_comm b q] at h₂
  omega

/-- A full block is colored by a permutation of the low digits. -/
abbrev Digits (q : ℕ) := ℕ → Equiv.Perm (Fin q)

def shade {q : ℕ} (hq : 0<q) (D : Digits q) (v : ℕ) : Fin q :=
  D (v/q) (digit hq v)

def Winners {q : ℕ} (hq : 0<q) (D : Digits q) (p : ℕ → ℕ) (b : ℕ) (i : Fin q) : Prop :=
  let u := pos b i
  b < p u / q ∧ D b i = shade hq D (p u)


/-- Permutations of the label interval fixing its largest point. -/
def Layout (n : ℕ) (f : ℕ → ℕ) : Prop :=
  f n=n ∧ (∀ v≤n, f v≤n) ∧ ∀ v≤n, ∀ w≤n, f v=f w → v=w


def width {V : Type*} (f : V → ℕ) : Sym2 V → ℕ :=
  Sym2.lift ⟨fun x y => Nat.dist (f x) (f y),fun _ _ => Nat.dist_comm ..⟩

theorem width_dvd (d a b : ℕ) : d ∣ Nat.dist a b ↔ a%d=b%d := by
  rcases le_total a b with h|h
  · rw [Nat.dist_eq_sub_of_le h]
    exact (Nat.modEq_iff_dvd' h).symm
  · rw [Nat.dist_comm,Nat.dist_eq_sub_of_le h,eq_comm (a:=a%d)]
    exact (Nat.modEq_iff_dvd' h).symm

open SimpleGraph

/-- The largest label and zero occur on an edge at the distinguished root. -/
def Extreme (n : ℕ) (p f : ℕ → ℕ) : Prop :=
  0 < n → ∃ v < n, p v = n ∧ f v = 0


theorem transport_layout_extreme {n : ℕ} (p P f : ℕ → ℕ)
    (r : Equiv.Perm (Fin (n+1))) (s : Equiv.Perm (Fin n)) (hP : Parent n P)
    (hr : r (Fin.last n)=Fin.last n) (hs : ∀ i : Fin n, r i.castSucc=(s i).castSucc)
    (hc : ∀ i : Fin n, (r ⟨P i,(Nat.lt_succ_of_le (hP i i.isLt).2)⟩).val=p (s i))
    (hf : Layout n f) (ef : Extreme n P f) :
    ∃ g, Layout n g ∧ Extreme n p g ∧ ∀ d, count n p g d = count n P f d := by
  classical
  let g (v : ℕ) := if hv : v≤n then f (r.symm ⟨v,Nat.lt_succ_of_le hv⟩).val else 0
  have hgr (i : Fin (n+1)) : g (r i).val = f i.val := by
    simp [g,Nat.le_of_lt_succ (r i).isLt]
  have hg : Layout n g := by
    refine ⟨?_,?_,?_⟩
    · have h := hgr (Fin.last n)
      simpa [hr] using h.trans hf.1
    · intro v hv
      let i : Fin (n+1) := ⟨v,Nat.lt_succ_of_le hv⟩
      simpa only [g,dif_pos hv] using hf.2.1 _ (Nat.le_of_lt_succ (r.symm i).isLt)
    · intro v hv w hw he
      let i : Fin (n+1) := ⟨v,Nat.lt_succ_of_le hv⟩
      let j : Fin (n+1) := ⟨w,Nat.lt_succ_of_le hw⟩
      have h := hf.2.2 _ (Nat.le_of_lt_succ (r.symm i).isLt) _
        (Nat.le_of_lt_succ (r.symm j).isLt) (by simpa [g,hv,hw] using he)
      exact congrArg Fin.val (r.symm.injective (Fin.ext h))
  have hgs (i : Fin n) : g (s i).val=f i.val := by
    simpa only [hs,Fin.val_castSucc] using hgr i.castSucc
  have hgc (i : Fin n) : g (p (s i))=f (P i) := by
    simpa only [hc] using hgr ⟨P i,Nat.lt_succ_of_le (hP i i.isLt).2⟩
  have eg : Extreme n p g := by
    intro hn
    obtain ⟨v,hv,hvP,hv0⟩ := ef hn
    let i : Fin n := ⟨v,hv⟩
    have e : (⟨P i,(Nat.lt_succ_of_le (hP i i.isLt).2)⟩ : Fin (n+1)) = Fin.last n := Fin.ext hvP
    have eq := hc i
    rw [e,hr] at eq
    exact ⟨s i,(s i).isLt,eq.symm,(hgs i).trans hv0⟩
  refine ⟨g,hg,eg,?_⟩
  intro d
  symm
  unfold count
  apply Finset.card_bij (fun v hv => (s ⟨v,Finset.mem_range.mp (Finset.mem_filter.mp hv).1⟩).val)
  · intro v hv
    let i : Fin n := ⟨v,Finset.mem_range.mp (Finset.mem_filter.mp hv).1⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (s i).isLt,
      by change g (s i).val % d = g (p (s i)) % d; rw [hgs i,hgc i]; exact (Finset.mem_filter.mp hv).2⟩
  · intro v hv w hw he
    exact congrArg Fin.val (s.injective (Fin.ext he))
  · intro v hv
    let j : Fin n := ⟨v,Finset.mem_range.mp (Finset.mem_filter.mp hv).1⟩
    let i := s.symm j
    have hi : s i=j := s.apply_symm_apply j
    have h := (Finset.mem_filter.mp hv).2
    change g j.val % d = g (p j.val) % d at h
    rw [← hi,hgs,hgc] at h
    exact ⟨i.val,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr i.isLt,h⟩,congrArg Fin.val hi⟩


theorem extreme_count {n : ℕ} {p f : ℕ → ℕ} (hp : Parent n p)
    (hl : Layout n f) (he : Extreme n p f) : count n p f n = n/n := by
  by_cases hn : n=0
  · subst n; simp [count]
  have hpos := Nat.pos_of_ne_zero hn
  obtain ⟨v,hv,hpv,hfv⟩ := he hpos
  have small (u : ℕ) (hu : u<n) : f u < n := by
    have hu' := hl.2.1 u hu.le
    have hne : f u ≠ n := fun h => (Nat.ne_of_lt hu) (hl.2.2 u hu.le n le_rfl (h.trans hl.1.symm))
    omega
  have hset : (Finset.range n).filter (fun w => f w%n = f (p w)%n) = {v} := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    constructor
    · rintro ⟨hw,hrem⟩
      rw [Nat.mod_eq_of_lt (small _ hw)] at hrem
      rcases lt_or_eq_of_le (hp w hw).2 with hlt|eq
      · rw [Nat.mod_eq_of_lt (small _ hlt)] at hrem
        exact ((Nat.ne_of_lt (hp w hw).1) (hl.2.2 _ hw.le _ hlt.le hrem)).elim
      · rw [eq,hl.1,Nat.mod_self] at hrem
        exact hl.2.2 _ hw.le _ hv.le (hrem.trans hfv.symm)
    · rintro rfl
      exact ⟨hv,by simp [hpv,hfv,hl.1]⟩
  simp [count,hset,Nat.div_self hpos]

end GracefulLabeling.RadixTree

namespace GracefulLabeling.SixCell

/-- The anchor of a pair is either one of six external digits or an earlier
vertex inside this block. In a path, the second vertex instead uses the first. -/
def parentDigit (ref : (b : Fin 3) → Fin (6+2*b.val)) (fork : Fin 3 → Bool)
    (f : Fin 6 → Fin 6) (j : Fin 6) : Fin 6 :=
  let b : Fin 3 := ⟨j.val / 2,by omega⟩
  let a := (ref b).val
  if j.val % 2 = 1 ∧ fork b = false then f (Fin.ofNat 6 (j.val-1))
  else if h : a < 6 then ⟨a,h⟩ else f (Fin.ofNat 6 (a-6))

def matchCount (ref : (b : Fin 3) → Fin (6+2*b.val)) (fork : Fin 3 → Bool)
    (f : Fin 6 → Fin 6) (d : ℕ) : ℕ :=
  (Finset.univ.filter (fun j : Fin 6 => (f j).val % d = (parentDigit ref fork f j).val % d)).card

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private def palette (i : Fin 57) (j : Fin 6) : Fin 6 :=
  Fin.ofNat 6 ((240867062432331168372940698353878709769443253816753940374853323984549276603275418253820955495293330166456920282523171510866923982687394396348773629111251893805369486938071768519463422971966240672381106900959585755804690830184310259464155615460892090521146101304310593310748449024149898551236116287522190312536 >>> (18*i.val+3*j.val)) % 8)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem palette_injective : ∀ i : Fin 57, Function.Injective (palette i) := by decide

private def refs (a : Fin 6) (b : Fin 8) (c : Fin 10) (i : Fin 3) : Fin (6+2*i.val) :=
  match i with
  | ⟨0,_⟩ => a
  | ⟨1,_⟩ => b
  | ⟨2,_⟩ => c

private def flags (x y z : Bool) : Fin 3 → Bool := ![x,y,z]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private def row (a : ℕ) : ℕ :=
  match a with
  | 0 => 8905831819773711226388907632523131240835818268222257615936483073375836266951360549817134373163736864665466969338994667865034667133622485792920626839560652433786377457508257816122811632781302970488049848335736963352371826863696827590928577787604073813700308013784756929094336116852134471627452041952664018842616731094703006049962161839287112767538867477748868167407854870032690426697377820700907892293028947011352391107447746767576646567906209214488087140478000483644681367497097272386865354661311023540301965234164295986184941362266977022851957129456387703847265863960124465286
  | 1 => 8905831804571578647250042737820251875326809151052754645090327770750126561785581455457621601179478954366512382061556532104929464316612922827104914189678290755238885193902117187624709386386944321787674395702318709865775127295882720482039053757228390236430369121518525057616387073918333430855577500608746525218959854892557353088777490341315230294978924881902414023328185679284661950934013667884104435995638003994712282638927044376087002743713366261880356749120927588090224533581243328246503588087674261034218852399156755991366020975456154652674372164114128416673670996808837427270
  | 2 => 11897557115128897522241460652290069007028990931524178123548075812056953098983913488031851237197579484520785020863988930159261117552385319801153164188124385949430312989718420557408781724264135313954719955219654728008987057237863237620896303329254520928482157572363479674310853801659659703640564522601233276458933371347249281024764411690145584546425939902576921651481453458941777213196017268788824434792471197900106496969880507408262529331352239277348781447165643985736862092415549855797291212958705937311840632192425784898649424018727859546718302490253423885093251893593708987396
  | 3 => 11897557115128897522247745490504548079784508141195634584912568395062680009809097825102186389335663952960869744251087021256496654628543689768977042400507917116596445246138058120598619338924693525768667909575353519021725136443977111696599092597078580285384917873679664628346643814713074963216621412737957892217777568176381836553836523048325116860970206518962121752499045715496060950765740246877366402709371789238460101661798407150065816914588893902585607068447746852697682175444478987624222621007851633623426471396105971030849898464810901782329471243837567370613211832478591910154
  | 4 => 17857945821916863603687183948093041351574123773018645885022218483406001620429756094081258513116336275595109407146063260539194693727636229842812551126764126298506521274336585784307202113421134786905907095758044078770089512420929983120979181440786713295327744317800686166481965260559260538170405592311465883617706857609641836036522646741396947138660766505935659501458559027089843437942050129327258930854592714161791786139214257009196157803250329791488742890348888068318789233509860850065281207221711510783709227104514178693607985095333501127930387856453223937466788987641175668053
  | 5 => 11920800103446215095563444637356182792464708785394340098919853242371291985203153294586561720698328630196951427321694588241514384319427654953327827853991464508950226817854710276381313249535722714371986922267204793602822120004980592648464222243770038114610457544768267135398936107978007787840248611532602242203504732431737433368259787059553802852565233489816269562459462894006074892985808604813998600399277993114878452848881061856335421475514988042576044650122302887624453941356042886105321671257760678217636010538167982435983993525488718987890634083115361223900907378431095767108
  | 6 => 6146083310655177373206078428990692586295970659212105948155183431097144433515038606493279935274533808521246454850070876370836209678956787384798755119436331173441928138385293752503159845943280307865806493887086096488277643541899335339343429192261353365924195347093504010071739061607494556218112704704981335920281425667587012531985198218752699971655551070325956375898172825697799401008280807694212773363377506066664067808992485527317310302838930117885156578857973369348952626270392011999791114223215471276351261375968091257580523195792300335349137206770410212451711015924598575653
  | 7 => 5937258945336280723151782355110010058868099976113708507168877073576709297318711254518082376757631405078036440772198050957761657446746254016934528097964594169974679584121056942840439576136547477446745712014472760342619935056112036866075867767507017514513061569306072342603582689416974256560295068539972160635716777363700491513396690614812095721010403446017140308123233411713931259628050637122032272723496721350586371373659298525995286575494971827560759498173184889737654552758049666750501367412709236969739137863805921772053180896831464646362964852009512488646613900972764754005
  | 8 => 37913389458819791437432314518187997708656537116027061831124379498131901133808396436897237441376216895824631377282257034589185707492814227583143789279944355550058141203176557044857817006553713157987733878875039106114021223453742813700423035989639487440468634303252309438020363524313920344598083729983369489788158703664755406135282934164018512769882141826373812858009384352426788494572288859324308944725589841626832738974168927032491896825177900917116426753560179279275286384283048711692715916711243904677751894882873087203704635292200849572686131568764996798503199952932472103064
  | 9 => 5960049089760207404878937033482031986782907960831093265681142504945450181441004819600866839800672962538338038165542059625342835780388782004330597197042561027974177152090404104081748407768477631142972051194716658278479482744862357185239188385949898296125497737233034252516352869044898598968472302857963888190616837949053874241196492338174270387963963613052193828107281329837035167966363295251515705339724660478276249757684874662696547826657043312879814586150497236487902903896505223769080751007634508672343768634499016208225227392490687879251916621411646760255163349494291567632
  | 10 => 25297543314921196743259084436345067851562122877623566066295162105471437036765123597119979300904125924785887359944524533742490788731724889391742139128810316637926916133068667875092854130531076954427037747070749363317458992899730241801354876871997508580138009687972428038248830649963355326396737938438410776489772222483145626948001069249647682537587484697801872166093120017945218932663561777770933784764675104083383338293350878056558928767323525982026612767721627080075078620170899572546070715520679020727313748107898442329388192418922296783908890528997366424411682228586592604676
  | 11 => 8951140385707382263653341903323007417023763175889074946420840952682857516295804308233348503127198944521195056737447371003721898936085008080390699819289955624004572721478420262285555386120020831644044372423451534982171129231592060314875118424872844406478274045171549401388119500172119977862970153102975459806017608879367712191398635940142185505689521078467294396681004609736029751825599926317178903740859931617036461192004992773588043179819681632980885728365787498826315080355930136925868989338887899966714681305519345825516950543682510970802375714948168722626236662361893965892
  | _ => 0

private def pick (a : Fin 6) (b : Fin 8) (c : Fin 10) (x y z : Bool) : Fin 57 :=
  Fin.ofNat 57 ((row (2*a.val+x.toNat) >>> (6*(20*(2*b.val+y.toNat) + 2*c.val+z.toNat))) % 64)

private def verify (a : Fin 6) (b : Fin 8) (c : Fin 10) (x y z : Bool) : Prop :=
  let f := palette (pick a b c x y z)
  matchCount (refs a b c) (flags x y z) f 2 = 3 ∧
  matchCount (refs a b c) (flags x y z) f 3 = 2 ∧
  matchCount (refs a b c) (flags x y z) f 6 = 1

private instance (a : Fin 6) (b : Fin 8) (c : Fin 10) (x y z : Bool) :
    Decidable (verify a b c x y z) := by unfold verify; infer_instance

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem verified : ∀ (a : Fin 6) (b : Fin 8) (c : Fin 10) (x y z : Bool),
    verify a b c x y z := by decide

/-- A six-vertex cell of three forks or paths permits a permutation with
exactly three, two, and one parent coincidences modulo 2, 3, and 6. -/
theorem exists_permutation (ref : (b : Fin 3) → Fin (6+2*b.val)) (fork : Fin 3 → Bool) :
    ∃ f : Equiv.Perm (Fin 6), matchCount ref fork f 2 = 3 ∧
      matchCount ref fork f 3 = 2 ∧ matchCount ref fork f 6 = 1 := by
  let i := pick (ref 0) (ref 1) (ref 2) (fork 0) (fork 1) (fork 2)
  let f := Equiv.ofBijective (palette i) (Finite.injective_iff_bijective.mp (palette_injective i))
  refine ⟨f,?_⟩
  have h := verified (ref 0) (ref 1) (ref 2) (fork 0) (fork 1) (fork 2)
  unfold verify at h
  have hr : refs (ref 0) (ref 1) (ref 2) = ref := by funext b; fin_cases b <;> rfl
  have hf : flags (fork 0) (fork 1) (fork 2) = fork := by funext b; fin_cases b <;> rfl
  change matchCount ref fork (palette i) 2 = 3 ∧ matchCount ref fork (palette i) 3 = 2 ∧ matchCount ref fork (palette i) 6 = 1
  rw [hr,hf] at h
  exact h

end GracefulLabeling.SixCell

namespace GracefulLabeling.RadixTree

abbrev sixPositive : 0 < 6 := by decide

def sixCount (D : Digits 6) (p : ℕ → ℕ) (b d : ℕ) : ℕ :=
  (Finset.univ.filter (fun i : Fin 6 =>
    (shade sixPositive D (pos b i)).val % d =
      (shade sixPositive D (p (pos b i))).val % d)).card

def sixGood (D : Digits 6) (p : ℕ → ℕ) (b : ℕ) : Prop :=
  ∀ d, d = 2 ∨ d = 3 ∨ d = 6 → sixCount D p b d = 6/d

def sixRule (n : ℕ) (p : ℕ → ℕ) : Prop :=
  ∀ b < n/6, ∀ D : Digits 6, ∃ e : Equiv.Perm (Fin 6),
    sixGood (Function.update D b e) p b


theorem sixColors {n : ℕ} (p : ℕ → ℕ) (hp : Parent n p)
    (top : Equiv.Perm (Fin 6)) (rule : sixRule n p) :
    ∃ D : Digits 6, D (n/6) = top ∧ ∀ b < n/6, sixGood D p b := by
  classical
  let k := n/6
  have stage : ∀ a ≤ k, ∃ D : Digits 6, D k = top ∧
      ∀ b, k-a ≤ b → b<k → sixGood D p b := by
    intro a
    induction a with
    | zero =>
      intro ha
      exact ⟨fun _ => top,rfl,fun b hb hb' => by omega⟩
    | succ a ih =>
      intro ha
      obtain ⟨D,hroot,hgood⟩ := ih (by omega)
      let b := k-(a+1)
      have hbk : b<k := by dsimp [b]; omega
      obtain ⟨e,he⟩ := rule b hbk D
      let D' : Digits 6 := Function.update D b e
      refine ⟨D',by simpa [D', Function.update_of_ne (Nat.ne_of_gt hbk)] using hroot,?_⟩
      intro c hc hck
      by_cases hcb : c=b
      · subst c
        exact he
      have hbc : b<c := by dsimp [b] at *; omega
      have prev := hgood c (by dsimp [b] at hbc; omega) hck
      intro d hd
      rw [← prev d hd]
      unfold sixCount
      congr 1
      apply Finset.filter_congr
      intro i _
      have hv : pos c i < n := pos_lt sixPositive hck i
      have hab : pos c i / 6 ≤ p (pos c i)/6 := Nat.div_le_div_right (hp _ hv).1.le
      rw [pos_div sixPositive] at hab
      have hpb : p (pos c i)/6 ≠ b := Nat.ne_of_gt (lt_of_lt_of_le hbc hab)
      simp [shade,D',Function.update_of_ne hpb,Function.update_of_ne hcb]
  obtain ⟨D,hd,hv⟩ := stage k (le_refl _)
  exact ⟨D,hd,fun b hb => hv b (by omega) hb⟩

theorem sixUnique {n : ℕ} (p : ℕ → ℕ) (hp : Parent n p) (D : Digits 6)
    (hD : ∀ b < n/6, sixGood D p b) :
    ∀ b < n/6, ∃! i, Winners sixPositive D p b i := by
  intro b hb
  classical
  obtain ⟨j,hj⟩ := Finset.card_eq_one.mp (show sixCount D p b 6 = 1 from hD b hb 6 (by simp))
  have iffwin (i : Fin 6) : Winners sixPositive D p b i ↔ i = j := by
    have mem := Finset.ext_iff.mp hj i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton,
      Nat.mod_eq_of_lt (shade sixPositive D (pos b i)).isLt,
      Nat.mod_eq_of_lt (shade sixPositive D (p (pos b i))).isLt] at mem
    have eqfirst : shade sixPositive D (pos b i) = D b i := by
      simp [shade]
    rw [eqfirst] at mem
    rw [←mem]
    constructor
    · intro hw
      exact congrArg Fin.val hw.2
    · intro he
      have ec : D b i = shade sixPositive D (p (pos b i)) := Fin.ext he
      refine ⟨?_,ec⟩
      have hv := (hp _ (pos_lt sixPositive hb i)).1
      have hle : pos b i / 6 ≤ p (pos b i) /6 := Nat.div_le_div_right hv.le
      rw [pos_div sixPositive] at hle
      by_contra! hn
      have hq : p (pos b i)/6=b := by omega
      have hd : i=digit sixPositive (p (pos b i)) := (D b).injective (by simpa [shade,hq] using ec)
      have heq : pos b i = p (pos b i) := by
        calc
          pos b i = pos (p (pos b i)/6) (digit sixPositive (p (pos b i))) := by rw [hq,←hd]
          _ = _ := pos_digit sixPositive _
      omega
  exact ⟨j,(iffwin j).2 rfl,fun i hi => (iffwin i).1 hi⟩

private theorem six_count_split (n : ℕ) (H : ℕ → ℕ) (t u : ℕ)
    (hfull : ∀ b<n/6, ∑ i : Fin 6, H (pos b i) = t)
    (htop : ∑ i ∈ Finset.range (n%6), H (6*(n/6)+i) = u) :
    ∑ i ∈ Finset.range n, H i = (n/6)*t+u := by
  have full : ∀ b≤n/6, ∑ i ∈ Finset.range (6*b), H i = b*t := by
    intro b
    induction b with
    | zero => simp
    | succ b ih =>
      intro hb
      rw [Nat.mul_succ,Finset.sum_range_add,ih (by omega),Nat.succ_mul b t]
      congr 1
      exact (Fin.sum_univ_eq_sum_range (fun i => H (6*b+i)) 6).symm.trans (hfull b (by omega))
  calc
    ∑ i ∈ Finset.range n, H i = ∑ i ∈ Finset.range (6*(n/6)+n%6), H i := by rw [Nat.div_add_mod]
    _ = _ := by rw [Finset.sum_range_add, full _ le_rfl,htop]

private def sixTailParent (n : ℕ) (p : ℕ → ℕ) (v : ℕ) := p (6*(n/6)+v) - 6*(n/6)

private theorem sixLowCount {n d : ℕ} (p : ℕ → ℕ) (hp : Parent n p)
    (D : Digits 6) (e : Equiv.Perm (Fin 6)) (hroot : D (n/6)=e)
    (hgood : ∀ b<n/6, sixGood D p b)
    (he : count (n%6) (sixTailParent n p) (fun v => (e (digit sixPositive v)).val) d = n%6/d)
    (hd : d=2 ∨ d=3) (f : ℕ → ℕ) :
    count n p (fun v => 6*f (v/6)+(shade sixPositive D v).val) d = n/d := by
  let H (v : ℕ) : ℕ := if (shade sixPositive D v).val % d = (shade sixPositive D (p v)).val % d then 1 else 0
  have countLow : count n p (fun v => 6*f (v/6)+(shade sixPositive D v).val) d =
      ∑ i ∈ Finset.range n, H i := by
    unfold count
    rw [Finset.card_filter]
    apply Finset.sum_congr rfl
    intro v _
    have reduce (a c : ℕ) : (6*a+c)%d=c%d := by rcases hd with rfl|rfl <;> omega
    simp only [reduce,H]
  have hfull (b) (hb : b<n/6) : ∑ i : Fin 6, H (pos b i) = 6/d := by
    have hc := hgood b hb d (hd.imp_right Or.inl)
    simpa only [sixCount,Finset.card_filter,H] using hc
  have htop : ∑ i ∈ Finset.range (n%6), H (6*(n/6)+i) = n%6/d := by
    rw [←he]
    unfold count
    rw [Finset.card_filter]
    apply Finset.sum_congr rfl
    intro i hi
    have hir := Finset.mem_range.mp hi
    have hm : n%6<6 := Nat.mod_lt _ (by decide)
    have hn := Nat.div_add_mod n 6
    have hpi := hp (6*(n/6)+i) (by omega)
    have hdiv : (6*(n/6)+i)/6=n/6 := by omega
    have hpd : p (6*(n/6)+i)/6=n/6 := by omega
    have hiEq : digit sixPositive (6*(n/6)+i)=digit sixPositive i := by
      apply Fin.ext; dsimp [digit]; omega
    have hpEq : digit sixPositive (p (6*(n/6)+i))=digit sixPositive (sixTailParent n p i) := by
      apply Fin.ext; dsimp [digit,sixTailParent]; omega
    simp [H,shade,hdiv,hpd,hroot,hiEq,hpEq]
  rw [countLow,six_count_split n H (6/d) (n%6/d) hfull htop]
  rcases hd with rfl|rfl <;> omega


def sixPaired : Prop :=
  ∀ {n : ℕ} (p : ℕ → ℕ), Parent n p →
    (∀ b<n/2, p (2*b)=p (2*b+1) ∨ p (2*b)=2*b+1) → sixRule n p


end GracefulLabeling.RadixTree



namespace GracefulLabeling.RadixTree

/-- A child-before-parent ordering in binary forks and paths satisfies the
three simultaneous local counting requirements of every full six-block. -/
theorem sixRule_of_pairs {n : ℕ} (p : ℕ → ℕ) (hp : Parent n p)
    (hpair : ∀ b<n/2, p (2*b) = p (2*b+1) ∨ p (2*b) = 2*b+1) : sixRule n p := by
  classical
  intro b hb D
  let first (c : Fin 3) := 6*b+(5-2*c.val)
  let second (c : Fin 3) := 6*b+(4-2*c.val)
  let A (c : Fin 3) := p (first c)
  have hgt (c : Fin 3) : first c < A c := (hp _ (by dsimp [first]; omega)).1
  have hshape (c : Fin 3) : p (second c) = A c ∨ p (second c) = first c := by
    have hc := c.isLt
    let m := 3*b+(2-c.val)
    have h0 : 2*m=second c := by dsimp [m,second]; omega
    have h1 : 2*m+1=first c := by dsimp [m,first]; omega
    have hm := hpair m (by dsimp [m]; omega)
    rw [h1,h0] at hm
    exact hm
  let ref (c : Fin 3) : Fin (6+2*c.val) :=
    if h : A c / 6 = b then ⟨6+(5-(A c % 6)),by
      have hc := c.isLt
      have ha := hgt c
      dsimp [first] at ha
      omega⟩
    else ⟨(shade sixPositive D (A c)).val,by have := (shade sixPositive D (A c)).isLt; omega⟩
  let fork (c : Fin 3) := decide (p (second c) = A c)
  obtain ⟨f,h₂,h₃,h₆⟩ := SixCell.exists_permutation ref fork
  let e := Fin.revPerm.trans f
  let D' := Function.update D b e
  have hin (j : Fin 6) : shade sixPositive D' (pos b j.rev) = f j := by
    simp [shade,D',e,Fin.revPerm]
  let anchor (c : Fin 3) : Fin 6 :=
    if h : (ref c).val < 6 then ⟨(ref c).val,h⟩ else f (Fin.ofNat 6 ((ref c).val-6))
  have ha (c : Fin 3) : anchor c = shade sixPositive D' (A c) := by
    by_cases hi : A c / 6 = b
    · have hr : (ref c).val = 6+(5-(A c%6)) := by simp [ref,hi]
      have hbig : ¬(ref c).val < 6 := by omega
      simp only [anchor,dif_neg hbig,hr,shade,hi,D',Function.update_self,e,Equiv.trans_apply]
      apply congrArg f
      apply Fin.ext
      simp [Fin.revPerm,Fin.rev,digit]
      omega
    · have hr : (ref c).val = (shade sixPositive D (A c)).val := by simp [ref,hi]
      have hlt : (ref c).val < 6 := hr ▸ (shade sixPositive D (A c)).isLt
      simp only [anchor,dif_pos hlt,shade,D',Function.update_of_ne hi]
      exact Fin.ext hr
  have hparent (j : Fin 6) : SixCell.parentDigit ref fork f j =
      shade sixPositive D' (p (pos b j.rev)) := by
    let c : Fin 3 := ⟨j.val/2,by omega⟩
    change (if j.val%2=1 ∧ fork c = false then f (Fin.ofNat 6 (j.val-1)) else anchor c) = _
    by_cases hodd : j.val%2=1
    · have hs : pos b j.rev=second c := by dsimp [pos,second,c,Fin.rev]; omega
      rw [hs]
      by_cases hfork : p (second c)=A c
      · have htrue : fork c = true := by simp [fork,hfork]
        simpa [htrue,hfork] using ha c
      · have hfalse : fork c = false := by simp [fork,hfork]
        have hpath := (hshape c).resolve_left hfork
        rw [if_pos ⟨hodd,hfalse⟩,hpath]
        have hloc : pos b (Fin.ofNat 6 (j.val-1)).rev = first c := by
          dsimp [pos,first,c,Fin.rev,Fin.ofNat]; omega
        rw [←hloc,hin]
    · have hfirst : pos b j.rev = first c := by dsimp [pos,first,c,Fin.rev]; omega
      rw [if_neg (fun h => hodd h.1),hfirst]
      exact ha c
  have hcount (d : ℕ) : sixCount D' p b d = SixCell.matchCount ref fork f d := by
    symm
    apply Finset.card_equiv Fin.revPerm
    intro j
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    change _ ↔ (shade sixPositive D' (pos b j.rev)).val%d =
      (shade sixPositive D' (p (pos b j.rev))).val%d
    rw [hin,hparent]
  refine ⟨e,?_⟩
  intro d hd
  change sixCount D' p b d = 6/d
  rw [hcount]
  rcases hd with rfl | rfl | rfl
  · exact h₂
  · exact h₃
  · exact h₆

end GracefulLabeling.RadixTree

namespace GracefulLabeling.RadixTree
open SimpleGraph


private def tailExtremeMap (a : Fin 5) (b : Fin 4) (c : Fin 3) (d : Fin 2) : Fin 6 → ℕ :=
  ![a.val+1,b.val+2,c.val+3,d.val+4,5,5]

private def tailExtremePerm : Fin 32 → Fin 6 → Fin 6 := ![![4,3,1,2,0,5],![2,4,1,3,0,5],![1,4,2,3,0,5],![3,4,1,2,0,5],![3,1,2,0,4,5],![3,1,2,4,0,5],![3,2,4,0,1,5],![0,1,2,4,3,5],![3,2,1,0,4,5],![2,4,3,1,0,5],![2,1,3,0,4,5],![1,3,2,0,4,5],![4,0,3,2,1,5],![2,1,3,4,0,5],![2,1,0,3,5,4],![4,3,0,2,1,5],![4,2,1,3,0,5],![2,4,3,0,1,5],![1,3,2,4,0,5],![1,2,3,0,4,5],![1,0,2,4,3,5],![4,3,2,1,0,5],![4,3,2,0,1,5],![4,2,3,1,0,5],![4,2,0,1,3,5],![3,2,1,4,0,5],![3,2,0,1,4,5],![2,1,4,3,0,5],![2,0,1,3,5,4],![1,2,0,3,5,4],![0,4,3,2,1,5],![0,2,1,3,5,4]]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private def tailExtremeSelect : Fin 6 → Fin 5 → Fin 4 → Fin 3 → Fin 2 → Fin 32 := ![![![![![7,7],![7,7],![7,7]],![![7,7],![7,7],![7,7]],![![7,7],![7,7],![7,7]],![![7,7],![7,7],![7,7]]],![![![7,7],![7,7],![7,7]],![![7,7],![7,7],![7,7]],![![7,7],![7,7],![7,7]],![![7,7],![7,7],![7,7]]],![![![7,7],![7,7],![7,7]],![![7,7],![7,7],![7,7]],![![7,7],![7,7],![7,7]],![![7,7],![7,7],![7,7]]],![![![7,7],![7,7],![7,7]],![![7,7],![7,7],![7,7]],![![7,7],![7,7],![7,7]],![![7,7],![7,7],![7,7]]],![![![7,7],![7,7],![7,7]],![![7,7],![7,7],![7,7]],![![7,7],![7,7],![7,7]],![![7,7],![7,7],![7,7]]]],![![![![7,7],![7,7],![7,7]],![![7,7],![7,7],![7,7]],![![7,7],![7,7],![7,7]],![![7,7],![7,7],![7,7]]],![![![0,0],![0,0],![0,0]],![![0,0],![0,0],![0,0]],![![0,0],![0,0],![0,0]],![![0,0],![0,0],![0,0]]],![![![0,0],![0,0],![0,0]],![![0,0],![0,0],![0,0]],![![0,0],![0,0],![0,0]],![![0,0],![0,0],![0,0]]],![![![0,0],![0,0],![0,0]],![![0,0],![0,0],![0,0]],![![0,0],![0,0],![0,0]],![![0,0],![0,0],![0,0]]],![![![0,0],![0,0],![0,0]],![![0,0],![0,0],![0,0]],![![0,0],![0,0],![0,0]],![![0,0],![0,0],![0,0]]]],![![![![20,20],![20,20],![20,20]],![![0,0],![0,0],![0,0]],![![0,0],![0,0],![0,0]],![![0,0],![0,0],![0,0]]],![![![7,7],![7,7],![7,7]],![![0,0],![0,0],![0,0]],![![0,0],![0,0],![0,0]],![![0,0],![0,0],![0,0]]],![![![0,0],![0,0],![0,0]],![![0,0],![0,0],![0,0]],![![0,0],![0,0],![0,0]],![![0,0],![0,0],![0,0]]],![![![0,0],![0,0],![0,0]],![![0,0],![0,0],![0,0]],![![0,0],![0,0],![0,0]],![![0,0],![0,0],![0,0]]],![![![0,0],![0,0],![0,0]],![![0,0],![0,0],![0,0]],![![0,0],![0,0],![0,0]],![![0,0],![0,0],![0,0]]]],![![![![29,29],![0,0],![0,0]],![![14,14],![0,0],![0,0]],![![0,0],![0,0],![0,0]],![![0,0],![0,0],![0,0]]],![![![14,14],![0,0],![0,0]],![![28,28],![0,0],![0,0]],![![0,0],![0,0],![0,0]],![![0,0],![0,0],![0,0]]],![![![31,31],![0,0],![0,0]],![![14,14],![0,0],![0,0]],![![0,0],![0,0],![0,0]],![![0,0],![0,0],![0,0]]],![![![0,0],![0,0],![0,0]],![![0,0],![0,0],![0,0]],![![0,0],![0,0],![0,0]],![![0,0],![0,0],![0,0]]],![![![0,0],![0,0],![0,0]],![![0,0],![0,0],![0,0]],![![0,0],![0,0],![0,0]],![![0,0],![0,0],![0,0]]]],![![![![10,0],![26,0],![0,0]],![![19,0],![8,0],![0,0]],![![19,0],![8,0],![0,0]],![![0,0],![0,0],![0,0]]],![![![10,0],![8,0],![0,0]],![![11,0],![11,0],![0,0]],![![4,0],![4,0],![0,0]],![![0,0],![0,0],![0,0]]],![![![4,0],![4,0],![0,0]],![![4,0],![4,0],![0,0]],![![8,0],![10,0],![0,0]],![![0,0],![0,0],![0,0]]],![![![11,0],![11,0],![0,0]],![![10,0],![8,0],![0,0]],![![4,0],![4,0],![0,0]],![![0,0],![0,0],![0,0]]],![![![0,0],![0,0],![0,0]],![![0,0],![0,0],![0,0]],![![0,0],![0,0],![0,0]],![![0,0],![0,0],![0,0]]]],![![![![16,2],![13,1],![3,0]],![![1,5],![27,2],![1,3]],![![25,2],![1,4],![0,3]],![![1,6],![13,2],![1,0]]],![![![0,1],![0,6],![15,1]],![![5,3],![5,3],![0,9]],![![1,3],![2,3],![1,2]],![![0,6],![0,12],![5,3]]],![![![2,0],![18,0],![3,1]],![![5,9],![2,22],![24,0]],![![0,6],![0,9],![1,3]],![![20,0],![2,0],![5,2]]],![![![5,0],![2,0],![16,2]],![![1,17],![3,23],![1,0]],![![0,21],![0,6],![15,2]],![![1,0],![12,0],![1,6]]],![![![2,9],![3,17],![5,0]],![![7,1],![2,3],![18,1]],![![2,3],![30,1],![0,7]],![![13,1],![2,12],![7,0]]]]]

private def tailExtremeCount (m : Fin 6) (p : Fin 6 → ℕ) (f : Fin 6 → Fin 6) (d : ℕ) : ℕ :=
  count m (fun j => p (digit (by decide : 0<6) j)) (fun j => (f (digit (by decide : 0<6) j)).val) d

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem tail_extreme_table : ∀ (m : Fin 6) (a : Fin 5) (b : Fin 4) (c : Fin 3) (d : Fin 2),
    let p := tailExtremeMap a b c d
    let f := tailExtremePerm (tailExtremeSelect m a b c d)
    (∀ v : Fin 6, v.val < m.val → p v ≤ m.val) →
    f m=m ∧ (∀ i : Fin 6, i.val ≤ m.val → (f i).val ≤ m.val) ∧
      tailExtremeCount m p f 2=m.val/2 ∧ tailExtremeCount m p f 3=m.val/3 ∧
      (0 < m.val → ∃ v : Fin 6, v.val < m.val ∧ p v=m.val ∧ (f v).val=0) := by
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem tail_extreme_perm_injective : ∀ i, Function.Injective (tailExtremePerm i) := by decide

theorem six_remainder_extreme {m : ℕ} (hm : m < 6) (p : ℕ→ℕ) (hp : Parent m p) :
    ∃ e : Equiv.Perm (Fin 6), e ⟨m,hm⟩=⟨m,hm⟩ ∧
      (∀ i : Fin 6, i.val ≤ m → (e i).val ≤ m) ∧
      count m p (fun v => (e (digit (by decide : 0<6) v)).val) 2=m/2 ∧
      count m p (fun v => (e (digit (by decide : 0<6) v)).val) 3=m/3 ∧
      (0 < m → ∃ v < m, p v=m ∧ (e (digit (by decide : 0<6) v)).val=0) := by
  let a : Fin 5 := ⟨(p 0-1)%5, Nat.mod_lt _ (by decide)⟩
  let b : Fin 4 := ⟨(p 1-2)%4, Nat.mod_lt _ (by decide)⟩
  let c : Fin 3 := ⟨(p 2-3)%3, Nat.mod_lt _ (by decide)⟩
  let d : Fin 2 := ⟨(p 3-4)%2, Nat.mod_lt _ (by decide)⟩
  let z : Fin 6 := ⟨m,hm⟩
  have hpar (v : Fin 6) (hv : v.val < m) : tailExtremeMap a b c d v=p v.val := by
    have h := hp v.val hv
    fin_cases v <;> simp only [Fin.reduceFinMk] at hv h ⊢ <;>
      simp [tailExtremeMap,a,b,c,d] <;> omega
  have ht := tail_extreme_table z a b c d (fun v hv => by rw [hpar v hv]; exact (hp v.val hv).2)
  let j := tailExtremeSelect z a b c d
  let e := Equiv.ofBijective (tailExtremePerm j) (Finite.injective_iff_bijective.mp (tail_extreme_perm_injective j))
  refine ⟨e,ht.1,ht.2.1,?_,?_,?_⟩
  case refine_3 =>
    intro hpos
    obtain ⟨v,hv,hp',hval⟩ := ht.2.2.2.2 hpos
    refine ⟨v.val,hv,(hpar v hv).symm.trans hp',?_⟩
    have heq : digit (by decide : 0<6) v.val=v := Fin.ext (Nat.mod_eq_of_lt v.isLt)
    rw [heq]
    exact hval
  all_goals
    have he (D : ℕ) : count m p (fun v => (e (digit (by decide : 0<6) v)).val) D =
        tailExtremeCount z (tailExtremeMap a b c d) (tailExtremePerm j) D := by
      unfold tailExtremeCount count
      congr 1
      apply Finset.filter_congr
      intro x hx
      have hl := Finset.mem_range.mp hx
      have hmod : x%6=x := Nat.mod_eq_of_lt (show x<6 by omega)
      have hxm : (digit (by decide : 0<6) x).val < m := by simpa [digit,hmod] using hl
      have hxp : tailExtremeMap a b c d (digit (by decide : 0<6) x)=p x :=
        (hpar _ hxm).trans (congrArg p hmod)
      dsimp only
      rw [hxp]
      rfl
    first | exact (he 2).trans ht.2.2.1 | exact (he 3).trans ht.2.2.2.1

end GracefulLabeling.RadixTree

namespace GracefulLabeling.RadixTree

def sixSmallExtreme : Prop :=
  ∀ {m : ℕ} (_ : m<6) (p : ℕ → ℕ), Parent m p →
    ∃ e : Equiv.Perm (Fin 6), e (digit sixPositive m) = digit sixPositive m ∧
      (∀ i : Fin 6, i.val ≤ m → (e i).val ≤ m) ∧
      count m p (fun v => (e (digit sixPositive v)).val) 2 = m/2 ∧
      count m p (fun v => (e (digit sixPositive v)).val) 3 = m/3 ∧
      (0 < m → ∃ v < m, p v=m ∧ (e (digit sixPositive v)).val=0)

private def zeroFiberFlip (n a : ℕ) := if a%6=0 then 6*(n/6)-a else a

private theorem zeroFiberProps (n : ℕ) (hr : n%6 ≠ 0) :
    let R := zeroFiberFlip n
    Layout n R ∧ R (6*(n/6))=0 ∧
      ∀ a≤n, ∀ b≤n, ∀ d, (d=2 ∨ d=3 ∨ 6 ∣ d) →
        (R a % d = R b % d ↔ a%d=b%d) := by
  have residue (a : ℕ) (ha : a≤n) : zeroFiberFlip n a % 6 = a % 6 := by
    simp only [zeroFiberFlip]; split <;> omega
  have bound (a : ℕ) (ha : a≤n) : zeroFiberFlip n a ≤ n := by
    simp only [zeroFiberFlip]; split <;> omega
  have inv (a : ℕ) (ha : a≤n) : zeroFiberFlip n (zeroFiberFlip n a)=a := by
    by_cases h : a%6=0
    · have ha' : 6*(n/6)-a ≤ n := by omega
      simp [zeroFiberFlip,h,show (6*(n/6)-a)%6=0 by omega]
      omega
    · simp [zeroFiberFlip,h]
  have preserves (a : ℕ) (ha : a≤n) (b : ℕ) (hb : b≤n) (d : ℕ) (hd : 6 ∣ d)
      (he : a%d=b%d) : zeroFiberFlip n a % d=zeroFiberFlip n b % d := by
    obtain ⟨c,rfl⟩ := hd
    have hres : a%6=b%6 := (width_dvd ..).mp (dvd_trans (by exact dvd_mul_right 6 c) ((width_dvd ..).mpr he))
    by_cases h : a%6=0
    · have h' : b%6=0 := hres ▸ h
      simp only [zeroFiberFlip,if_pos h,if_pos h']
      apply (width_dvd ..).mp
      rw [show Nat.dist (6*(n/6)-a) (6*(n/6)-b) = Nat.dist a b by
        simp only [Nat.dist]; omega]
      exact (width_dvd ..).mpr he
    · simp [zeroFiberFlip,h,show b%6≠0 from hres ▸ h,he]
  refine ⟨⟨by simp [zeroFiberFlip,hr],bound,?_⟩,by simp [zeroFiberFlip],?_⟩
  · intro a ha b hb h
    simpa only [inv _ ha, inv _ hb] using congrArg (zeroFiberFlip n) h
  · intro a ha b hb d hd
    rcases hd with rfl|rfl|hd
    · have ha' := residue a ha
      have hb' := residue b hb
      omega
    · have ha' := residue a ha
      have hb' := residue b hb
      omega
    · refine ⟨?_,preserves a ha b hb d hd⟩
      intro h
      simpa only [inv _ ha, inv _ hb] using preserves _ (bound a ha) _ (bound b hb) d hd h

theorem sixBlockLiftExtreme {n : ℕ} (p : ℕ → ℕ) (hp : Parent n p) (rule : sixRule n p)
    (tail : sixSmallExtreme) :
    ∃ P : ℕ → ℕ, Parent (n/6) P ∧ ∀ f, Layout (n/6) f → Extreme (n/6) P f →
      ∃ g, Layout n g ∧ Extreme n p g ∧ count n p g 2=n/2 ∧ count n p g 3=n/3 ∧
        ∀ d, count n p g (6*d) = count (n/6) P f d := by
  classical
  have hm : n%6<6 := Nat.mod_lt _ (by decide)
  have hpt : Parent (n%6) (sixTailParent n p) := by
    intro v hv
    have hn := Nat.div_add_mod n 6
    have hpar := hp (6*(n/6)+v) (by omega)
    dsimp [sixTailParent]
    omega
  obtain ⟨e,hefix',hebound,he2,he3,hneigh⟩ := tail hm (sixTailParent n p) hpt
  have hefix : e (digit sixPositive n)=digit sixPositive n := by
    simpa [digit] using hefix'
  obtain ⟨D,hroot,hgood⟩ := sixColors p hp e rule
  have hD := sixUnique p hp D hgood
  let k := n/6
  let hit (b : ℕ) : Fin 6 := if h : b<k then (hD b h).exists.choose else ⟨0,sixPositive⟩
  have win {b : ℕ} (hb : b<k) : Winners sixPositive D p b (hit b) := by
    simpa [hit,hb] using (hD b hb).exists.choose_spec
  let vertex (b : ℕ) := pos b (hit b)
  let P (b : ℕ) := p (vertex b) / 6
  have hP : Parent k P := by
    intro b hb
    exact ⟨(win hb).1,Nat.div_le_div_right ((hp _ (pos_lt sixPositive hb (hit b))).2)⟩
  refine ⟨P,hP,?_⟩
  intro f hf ef
  let g (v : ℕ) := 6*f (v/6) + (shade sixPositive D v).val
  have top {v : ℕ} (hv : v/6=k) : shade sixPositive D v = e (digit sixPositive v) := by
    simp only [shade,hv,show D k = e from hroot]
  have label {v : ℕ} (hv : v/6=k) : g v=6*k+(e (digit sixPositive v)).val := by
    simp only [g,top hv,hv,show f k=k from hf.1]
  have rootFixed : g n = n := by
    rw [label rfl, hefix]
    exact Nat.div_add_mod n 6
  have hbound {v : ℕ} (hv : v≤n) : g v≤n := by
    have hk : v/6≤k := Nat.div_le_div_right hv
    rcases lt_or_eq_of_le hk with hvk|hvk
    · have hfsmall : f (v/6)<k := by
        have hm := hf.2.1 _ hk
        have hn : f (v/6) ≠ k := by
          intro h
          exact (Nat.ne_of_lt hvk) (hf.2.2 _ hk k (le_refl _) (h.trans hf.1.symm))
        omega
      exact (pos_lt sixPositive hfsmall (shade sixPositive D v)).le
    · rw [label hvk]
      have hm : (digit sixPositive v).val ≤ n%6 := by
        change v%6 ≤ n%6
        have hd := Nat.div_add_mod v 6
        have hn := Nat.div_add_mod n 6
        change v/6=n/6 at hvk
        omega
      have hle := hebound _ hm
      have hn := Nat.div_add_mod n 6
      dsimp [k]
      omega
  have hinj {v w : ℕ} (hv : v≤n) (hw : w≤n) (he : g v=g w) : v=w := by
    have he₁ := congrArg (· / 6) he
    have he₂ := congrArg (· % 6) he
    simp only [g,Nat.mul_add_div sixPositive,Nat.div_eq_of_lt (shade sixPositive D v).isLt,
      Nat.div_eq_of_lt (shade sixPositive D w).isLt,Nat.add_zero] at he₁
    have hb := hf.2.2 _ (Nat.div_le_div_right hv) _ (Nat.div_le_div_right hw) he₁
    simp only [g,Nat.mul_add_mod,Nat.mod_eq_of_lt (shade sixPositive D v).isLt,
      Nat.mod_eq_of_lt (shade sixPositive D w).isLt] at he₂
    have heq : shade sixPositive D v = shade sixPositive D w := Fin.ext he₂
    simp only [shade,hb] at heq
    have hrem := (D (w/6)).injective heq
    calc
      v = pos (v/6) (digit sixPositive v) := (pos_digit sixPositive v).symm
      _ = pos (w/6) (digit sixPositive w) := by rw [hb,hrem]
      _ = w := pos_digit sixPositive w
  have layout : Layout n g := ⟨rootFixed,fun _ hv => hbound hv,fun _ hv _ hw he => hinj hv hw he⟩
  have htwo : count n p g 2=n/2 := sixLowCount p hp D e hroot hgood he2 (by decide : 2=2 ∨ 2=3) f
  have hthree : count n p g 3=n/3 := sixLowCount p hp D e hroot hgood he3 (by decide : 3=2 ∨ 3=3) f
  have hvshade {v : ℕ} (hv : v<n) (he : shade sixPositive D v=shade sixPositive D (p v)) :
      v/6 < k ∧ vertex (v/6)=v := by
    have hpar := hp v hv
    have hmono : v/6 ≤ p v/6 := Nat.div_le_div_right (Nat.le_of_lt hpar.1)
    have hstrict : v/6 < p v/6 := by
      by_contra! h
      have heqb := Nat.le_antisymm hmono h
      simp only [shade,heqb] at he
      have hd := (D (p v/6)).injective he
      have hcontr : v=p v := by
        calc
          v = pos (v/6) (digit sixPositive v) := (pos_digit sixPositive v).symm
          _ = pos (p v/6) (digit sixPositive (p v)) := by rw [heqb,hd]
          _ = p v := pos_digit sixPositive _
      omega
    have hb : v/6<k := lt_of_lt_of_le hstrict (Nat.div_le_div_right hpar.2)
    have wi : Winners sixPositive D p (v/6) (digit sixPositive v) := by
      simpa only [Winners,pos_digit,shade] using And.intro hstrict he
    have equ := (hD _ hb).unique (win hb) wi
    exact ⟨hb,by simp [vertex,equ]⟩
  have counts : ∀ d, count n p g (6*d) = count (n/6) P f d := by
    intro d
    unfold count
    refine Finset.card_bij' (fun v _ => v/6) (fun b _ => vertex b) ?_ ?_ ?_ ?_
    · intro v hv
      obtain ⟨hv,he⟩ := Finset.mem_filter.mp hv
      have hw := (mod_digits sixPositive (shade sixPositive D v) (shade sixPositive D (p v)) _ _ d).mp he
      obtain ⟨hb,hv'⟩ := hvshade (Finset.mem_range.mp hv) hw.1
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hb,by simpa only [P,hv'] using hw.2⟩
    · intro b hb
      obtain ⟨hb,he⟩ := Finset.mem_filter.mp hb
      have hbk := Finset.mem_range.mp hb
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (pos_lt sixPositive hbk (hit b)),?_⟩
      apply (mod_digits sixPositive (shade sixPositive D (vertex b)) (shade sixPositive D (p (vertex b))) _ _ d).2
      exact ⟨by simpa only [vertex,shade,pos_div sixPositive,digit_pos] using (win hbk).2,
        by simpa only [vertex,pos_div sixPositive,P] using he⟩
    · intro v hv
      obtain ⟨hv,he⟩ := Finset.mem_filter.mp hv
      exact (hvshade (Finset.mem_range.mp hv)
        ((mod_digits sixPositive (shade sixPositive D v) (shade sixPositive D (p v)) _ _ d).mp he).1).2
    · intro b _
      exact pos_div sixPositive b (hit b)

  by_cases ht : n%6=0
  · refine ⟨g,layout,?_,htwo,hthree,counts⟩
    intro hn
    have hk : 0<k := by dsimp [k]; omega
    obtain ⟨b,hb,hpar,hzero⟩ := ef hk
    let u := vertex b
    have hu : u<n := pos_lt sixPositive hb (hit b)
    have hqtop : p u/6=k := hpar
    have hpn : p u=n := by
      have hab := (hp _ hu).2
      dsimp [k] at hqtop
      omega
    have hshade : shade sixPositive D u = shade sixPositive D (p u) := by
      simpa only [u,vertex,shade,pos_div sixPositive,digit_pos] using (win hb).2
    have hcolor : (shade sixPositive D u).val=0 := by
      rw [hshade,hpn,top rfl,hefix]
      exact ht
    refine ⟨u,hu,hpn,?_⟩
    change 6*f (u/6)+(shade sixPositive D u).val=0
    rw [show u/6=b from pos_div sixPositive b (hit b),hzero,hcolor]
  · obtain ⟨hflip,fzero,fres⟩ := zeroFiberProps n ht
    let R := zeroFiberFlip n
    have hlayout : Layout n (R ∘ g) :=
      ⟨by simp only [Function.comp_apply,layout.1]; exact hflip.1,
       fun v hv => hflip.2.1 _ (hbound hv),fun a ha b hb h => hinj ha hb (hflip.2.2 _ (hbound ha) _ (hbound hb) h)⟩
    have compare (d : ℕ) (hd : d=2 ∨ d=3 ∨ 6∣d) : count n p (R ∘ g) d = count n p g d := by
      unfold count
      congr 1
      apply Finset.filter_congr
      intro v hv
      exact fres _ (hbound (Finset.mem_range.mp hv).le) _ (hbound (hp _ (Finset.mem_range.mp hv)).2) d hd
    refine ⟨R ∘ g,hlayout,?_,(compare 2 (by simp)).trans htwo,
      (compare 3 (by simp)).trans hthree,fun d => (compare (6*d) (by simp)).trans (counts d)⟩
    intro _
    obtain ⟨u,hu,hupar,hzero⟩ := hneigh (by omega)
    let v := 6*k+u
    have hv : v<n := by dsimp [v,k]; omega
    have hvpar : p v=n := by
      have hl := (hp v hv).1
      dsimp [sixTailParent] at hupar
      dsimp [v,k] at *
      omega
    have hdiv : v/6=k := by dsimp [v,k]; omega
    have hdigit : digit sixPositive v=digit sixPositive u := by
      apply Fin.ext; dsimp [digit,v,k]; omega
    refine ⟨v,hv,hvpar,?_⟩
    change R (g v)=0
    rw [label hdiv,hdigit,hzero,Nat.add_zero]
    exact fzero

theorem anySixBlockLiftExtreme {n : ℕ} (p : ℕ → ℕ) (hp : Parent n p)
    (paired : sixPaired) (tail : sixSmallExtreme) :
    ∃ P : ℕ → ℕ, Parent (n/6) P ∧ ∀ f, Layout (n/6) f → Extreme (n/6) P f →
      ∃ g, Layout n g ∧ Extreme n p g ∧ count n p g 2=n/2 ∧ count n p g 3=n/3 ∧
        ∀ d, count n p g (6*d) = count (n/6) P f d := by
  obtain ⟨r,s,P,hP,hr,hs,hc,hpair⟩ := BinaryParents.reindex p hp
  obtain ⟨Q,hQ,hg⟩ := sixBlockLiftExtreme P hP (paired P hP hpair) tail
  refine ⟨Q,hQ,?_⟩
  intro f hf ef
  obtain ⟨g,hl,eg,h2,h3,hcnt⟩ := hg f hf ef
  obtain ⟨g',hl',eg',hsame⟩ := transport_layout_extreme p P g r s hP hr hs hc hl eg
  exact ⟨g',hl',eg',(hsame _).trans h2,(hsame _).trans h3,fun d => (hsame _).trans (hcnt d)⟩


theorem sixAllExtreme (n : ℕ) (p : ℕ → ℕ) (hp : Parent n p)
    (paired : sixPaired) (tail : sixSmallExtreme) :
    ∃ f, Layout n f ∧ Extreme n p f ∧
      (∀ j a : ℕ, a=1 ∨ a=2 ∨ a=3 ∨ a=6 → count n p f (6^j*a) = n/(6^j*a)) ∧
      ∀ j : ℕ, count n p f (6^j*(n/6^j)) = n/(6^j*(n/6^j)) := by
  induction n using Nat.strong_induction_on generalizing p with
  | h n ih =>
    by_cases hn : n=0
    · subst n
      exact ⟨id,⟨rfl,fun _ => id,fun _ _ _ _ => id⟩,by simp [Extreme],by simp [count],by simp [count]⟩
    obtain ⟨P,hP,lift⟩ := anySixBlockLiftExtreme p hp paired tail
    obtain ⟨f,hf,ef,hcnt,htops⟩ := ih (n/6) (by omega) P hP
    obtain ⟨g,hg,eg,h2,h3,hgcnt⟩ := lift f hf ef
    refine ⟨g,hg,eg,?_,?_⟩
    · rintro (_|j) a ha
      · simp only [pow_zero,one_mul]
        rcases ha with rfl|rfl|rfl|rfl
        · simp [count,Nat.mod_one]
        · exact h2
        · exact h3
        · simpa [count,Nat.mod_one] using hgcnt 1
      · rw [pow_succ',Nat.mul_assoc,hgcnt,hcnt j a ha,Nat.div_div_eq_div_mul]
    · rintro (_|j)
      · simpa using extreme_count hp hg eg
      · rw [pow_succ',← Nat.div_div_eq_div_mul,Nat.mul_assoc,hgcnt,htops j,Nat.div_div_eq_div_mul]

end GracefulLabeling.RadixTree

namespace GracefulLabeling.RadixTree
open SimpleGraph
/-- A prescribed vertex of a finite tree can carry the largest label while each modulus of the
form a times a power of six, for a in {1,2,3,6}, has the exact edge count. -/
theorem finite_tree_six_counts_with_tops {V : Type*} [Fintype V] (T : SimpleGraph V)
    [DecidableEq V] [DecidableRel T.Adj] (ht : T.IsTree) (root : V) :
    ∃ F : V → ℕ, Function.Injective F ∧
      F root=T.edgeFinset.card ∧ (∀ x, F x ≤ T.edgeFinset.card) ∧
      ∀ j a : ℕ, a=1 ∨ a=2 ∨ a=3 ∨ a=6 ∨ a=T.edgeFinset.card/6^j →
        (T.edgeFinset.filter (fun e => 6^j*a ∣ width F e)).card = T.edgeFinset.card/(6^j*a) := by
  classical
  let n := T.edgeFinset.card
  obtain ⟨e,p,E,hp,hr,hedge⟩ := GracefulLabeling.exists_ordered_parent T ht root
    (show Fintype.card V = n+1 by have := ht.card_edgeFinset; dsimp [n]; omega)
  obtain ⟨f,hf,_,hcounts,htops⟩ := sixAllExtreme n p hp (fun P hP pairs => sixRule_of_pairs P hP pairs)
    (fun hm pp hpp => by obtain ⟨e,he,hl,h₂,h₃,hx⟩ := six_remainder_extreme hm pp hpp; exact ⟨e,by simpa [digit,Nat.mod_eq_of_lt hm] using he,hl,h₂,h₃,hx⟩)
  let F (v : V) := f (e v).val
  refine ⟨F,fun x y h => e.injective (Fin.ext (hf.2.2 _ (Nat.le_of_lt_succ (e x).isLt) _
    (Nat.le_of_lt_succ (e y).isLt) h)),by simpa [F,hr] using hf.1,
    fun v => hf.2.1 _ (Nat.le_of_lt_succ (e v).isLt),?_⟩
  have hw (d : ℕ) (i : Fin n) :
      d ∣ width F (E i).val ↔ f i.val % d = f (p i.val) % d := by
    rw [hedge]
    simp only [width,Sym2.lift_mk,F,e.apply_symm_apply,Fin.val_castSucc]
    exact width_dvd ..
  intro j a ha
  let d := 6^j*a
  change (T.edgeFinset.filter (fun w => d ∣ width F w)).card = n/d
  have hval : count n p f d = n/d := by
    rcases ha with h|h|h|h|h
    · exact hcounts j a (Or.inl h)
    · exact hcounts j a (Or.inr (Or.inl h))
    · exact hcounts j a (Or.inr (Or.inr (Or.inl h)))
    · exact hcounts j a (Or.inr (Or.inr (Or.inr h)))
    · simpa only [d,h] using htops j
  rw [← hval]
  symm
  unfold count
  apply Finset.card_bij (fun v hv => (E ⟨v,Finset.mem_range.mp (Finset.mem_filter.mp hv).1⟩).val)
  · intro v hv
    let i : Fin n := ⟨v,Finset.mem_range.mp (Finset.mem_filter.mp hv).1⟩
    exact Finset.mem_filter.mpr ⟨T.mem_edgeFinset.mpr (E i).property,(hw d i).2 (Finset.mem_filter.mp hv).2⟩
  · intro v hv w hw h
    exact congrArg Fin.val (E.injective (Subtype.ext h))
  · intro b hb
    let s : T.edgeSet := ⟨b,T.mem_edgeFinset.mp (Finset.mem_filter.mp hb).1⟩
    let i := E.symm s
    have hb' : (E i).val=b := congrArg Subtype.val (E.apply_symm_apply s)
    exact ⟨i.val,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr i.isLt,
      (hw d i).1 (hb' ▸ (Finset.mem_filter.mp hb).2)⟩,hb'⟩



end GracefulLabeling.RadixTree

end OMA.SixSpectrum

theorem OMA.solution : OMA.R_GracefulLabeling_graceful_tree_conjecture_R2.H1 := by
  intro V _ _ T _ hT r
  exact OMA.SixSpectrum.GracefulLabeling.RadixTree.finite_tree_six_counts_with_tops T hT r
