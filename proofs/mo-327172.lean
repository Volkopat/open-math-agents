import OMAStatements.S_mo_327172

/-!
Finite-round tree peeling follows Häger, Pfister, Graell i Amat and Brännström,
DOI 10.1109/TIT.2017.2689783. For the fixed-edge multigraph, expose one
frontier at a time. Count the extensions with distinct fresh endpoints and
bound each outcome from below. The two limiting Poisson probabilities sum
to one, which absorbs the omitted collisions.
-/
namespace Cuckoo


open OMA.S_mo_327172

variable {N : ℕ} (g : Fin N → Fin N × Fin N)

def side (n : ℕ) : Bool := decide (n % 2 = 1)

lemma side_add_two (n : ℕ) : side (n+2) = side n := by
  simp [side]

/-- A nonbacktracking walk continues away from its initial edge for n further edges. -/
def arm : ℕ → Fin N → Prop
  | 0, _ => True
  | n+1, e => ∃ j, j ≠ e ∧ endpt g (side n) e = endpt g (side n) j ∧ arm n j

lemma arm_drop (n : ℕ) (e : Fin N) : arm g (n+2) e → arm g n e := by
  induction n generalizing e with
  | zero => exact fun _ => trivial
  | succ n ih =>
    rintro ⟨j, hj, heq, h⟩
    exact ⟨j, hj, (side_add_two n) ▸ heq, ih j h⟩

lemma trim_iff (s : Bool) (E : Finset (Fin N)) (e : Fin N) :
    e ∈ trim g s E ↔ e ∈ E ∧ ∃ j ∈ E, j ≠ e ∧ endpt g s e = endpt g s j := by
  simp only [trim, Finset.mem_filter]
  constructor
  · rintro ⟨he, hc⟩
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hc
    simp only [Finset.mem_filter] at ha hb
    by_cases h : a = e
    · subst a
      exact ⟨he, b, hb.1, Ne.symm hab, hb.2.symm⟩
    · exact ⟨he, a, ha.1, h, ha.2.symm⟩
  · rintro ⟨he, j, hj, hne, h⟩
    exact ⟨he, Finset.one_lt_card.mpr ⟨e, Finset.mem_filter.mpr ⟨he, rfl⟩,
      j, Finset.mem_filter.mpr ⟨hj, h.symm⟩, Ne.symm hne⟩⟩

/-- The other edge can use e as its first step in the older direction. -/
lemma back (n : ℕ) {e j : Fin N} (hne : j ≠ e)
    (h : endpt g (side n) e = endpt g (side n) j) (ha : arm g n e) :
    arm g (n-1) j := by
  cases n with
  | zero => trivial
  | succ n =>
    cases n with
    | zero => trivial
    | succ n =>
      exact ⟨e, Ne.symm hne, (side_add_two n) ▸ h.symm, arm_drop g n e ha⟩

theorem remaining_iff (n : ℕ) (e : Fin N) :
    e ∈ remaining g n ↔ arm g n e ∧ arm g (n-1) e := by
  induction n generalizing e with
  | zero => simp [remaining, arm]
  | succ n ih =>
    change e ∈ trim g (side n) (remaining g n) ↔ arm g (n+1) e ∧ arm g n e
    rw [trim_iff]
    constructor
    · rintro ⟨he, j, hj, hne, h⟩
      exact ⟨⟨j, hne, h, ((ih j).mp hj).1⟩, ((ih e).mp he).1⟩
    · rintro ⟨⟨j, hne, h, hj⟩, he⟩
      exact ⟨(ih e).mpr ⟨he, back g n (Ne.symm hne) h.symm hj⟩,
        j, (ih j).mpr ⟨hj, back g n hne h he⟩, hne, h⟩


open Filter Topology BigOperators

abbrev Graph (n : ℕ) := Fin n → Fin n × Fin n

def next (s : Bool) (g : Graph N) (Q : Finset (Fin N)) : Finset (Fin N) :=
  Finset.univ.filter fun j => ∃ e ∈ Q, j ≠ e ∧ endpt g s e = endpt g s j

/-- The set of graphs consistent with an exploration. Known edges have fixed labels.
    Every other edge independently ranges over the indicated rectangle. -/
def tables (K : Finset (Fin N)) (u : Graph N) (L R : Finset (Fin N)) :
    Finset (Graph N) :=
  Fintype.piFinset fun e => if e ∈ K then {u e} else L ×ˢ R

lemma mem_tables {K : Finset (Fin N)} {u g : Graph N} {L R : Finset (Fin N)} :
    g ∈ tables K u L R ↔
      (∀ e ∈ K, g e = u e) ∧ (∀ e ∉ K, (g e).1 ∈ L ∧ (g e).2 ∈ R) := by
  simp only [tables, Fintype.mem_piFinset]
  constructor
  · intro h
    exact ⟨fun e he => by simpa [he] using h e, fun e he => by simpa [he] using h e⟩
  · rintro ⟨h₁,h₂⟩ e
    by_cases he : e ∈ K
    · simpa [he] using h₁ e he
    · simpa [he] using h₂ e he

lemma card_tables (K : Finset (Fin N)) (u : Graph N) (L R : Finset (Fin N)) :
    (tables K u L R).card = (L.card * R.card)^(N - K.card) := by
  classical
  simp only [tables, Fintype.card_piFinset]
  simp_rw [apply_ite Finset.card, Finset.card_singleton, Finset.card_product]
  rw [Finset.prod_ite]
  simp [Finset.filter_not, Finset.card_sdiff_of_subset (Finset.subset_univ _)]

lemma arm_relabel (σ : Equiv.Perm (Fin N)) (h : ℕ) (e : Fin N) :
    arm (g ∘ σ) h e ↔ arm g h (σ e) := by
  induction h generalizing e with
  | zero => rfl
  | succ n ih =>
    simp only [arm, ih]
    constructor
    · rintro ⟨j,hj,hs,ha⟩
      exact ⟨σ j,σ.injective.ne hj,hs,ha⟩
    · rintro ⟨j,hj,hs,ha⟩
      obtain ⟨j,rfl⟩ := σ.surjective j
      exact ⟨j,fun h => hj (congrArg σ h),hs,ha⟩

def survivors (N h : ℕ) (e : Fin N) : Finset (Graph N) :=
  Finset.univ.filter fun g => e ∈ remaining g h

lemma card_survivors (h : ℕ) (e j : Fin N) :
    (survivors N h e).card = (survivors N h j).card := by
  classical
  let σ := Equiv.swap j e
  let τ : Graph N ≃ Graph N := σ.symm.arrowCongr (Equiv.refl _)
  apply Finset.card_equiv τ
  intro g
  simp only [survivors, Finset.mem_filter, Finset.mem_univ, true_and, remaining_iff]
  change _ ↔ arm (g ∘ σ) h j ∧ arm (g ∘ σ) (h-1) j
  simp [arm_relabel, σ]

lemma f_root (h : ℕ) (e : Fin N) :
    f N h = ((survivors N h e).card : ℝ) / (N : ℝ)^(2*N) := by
  classical
  have hn := e.isLt
  have hpos : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have heq (g : Graph N) : ((remaining g h).card : ℝ) =
      ∑ j : Fin N, if j ∈ remaining g h then (1 : ℝ) else 0 := by
    simp
  simp only [f, heq]
  rw [Finset.sum_comm]
  have hcount (j : Fin N) : (∑ g : Graph N, if j ∈ remaining g h then (1 : ℝ) else 0) =
      (survivors N h e).card := by
    rw [← card_survivors h j e]
    simp [survivors]
  simp_rw [hcount]
  simp [div_mul_eq_div_div, hpos, mul_comm]

/-- Explore first-coordinate endpoints, then exchange the two sides. -/
def flip (g : Graph N) : Graph N := fun e => (g e).swap

def step (g : Graph N) (Q : Finset (Fin N)) : Finset (Fin N) := next false g Q

/-- Each active edge leads to a distinct available vertex incident to precisely one known edge. -/
def clean (u : Graph N) (K L Q : Finset (Fin N)) : Prop :=
  Q ⊆ K ∧ (∀ e ∈ Q, (u e).1 ∈ L) ∧
    ∀ e ∈ Q, ∀ j ∈ K, (u j).1 = (u e).1 → j = e

lemma clean_image_card {u : Graph N} {K L Q : Finset (Fin N)} (h : clean u K L Q) :
    (Q.image fun e => (u e).1).card = Q.card := by
  apply Finset.card_image_of_injOn
  intro a ha b hb hab
  exact h.2.2 b hb a (h.1 ha) hab

abbrev Free (K : Finset (Fin N)) (j : ℕ) := ↥(Kᶜ.powersetCard j)

structure Config (u : Graph N) (K Q R : Finset (Fin N)) (j : ℕ) where
  edges : Free K j
  src : (↥edges.val) → ↥(Q.image fun e => (u e).1)
  dest : (↥edges.val) ↪ ↥(R \ K.image fun e => (u e).2)

noncomputable def configEquiv (u : Graph N) (K Q R : Finset (Fin N)) (j : ℕ) :
    Config u K Q R j ≃
      Σ edges : Free K j, (↥edges.val → ↥(Q.image fun e => (u e).1)) ×
        (↥edges.val ↪ ↥(R \ K.image fun e => (u e).2)) where
  toFun c := ⟨c.edges,c.src,c.dest⟩
  invFun c := ⟨c.1,c.2.1,c.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance configFintype (u : Graph N) (K Q R : Finset (Fin N)) (j : ℕ) :
    Fintype (Config u K Q R j) := Fintype.ofEquiv _ (configEquiv u K Q R j).symm

lemma card_config {u : Graph N} {K L Q R : Finset (Fin N)} (hc : clean u K L Q) (j : ℕ) :
    Fintype.card (Config u K Q R j) =
      (N-K.card).choose j * Q.card^j * ((R \ K.image fun e => (u e).2).card.descFactorial j) := by
  classical
  rw [Fintype.card_congr (configEquiv u K Q R j), Fintype.card_sigma]
  have hcard (a : Free K j) : a.val.card = j := (Finset.mem_powersetCard.mp a.prop).2
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_coe, Fintype.card_embedding_eq,
    hcard, clean_image_card hc]
  simp [Free, mul_assoc, Finset.card_compl]

variable {u : Graph N} {K Q R : Finset (Fin N)} {j : ℕ}

def upd (c : Config u K Q R j) (e : Fin N) : Fin N × Fin N :=
  if h : e ∈ c.edges.val then ((c.src ⟨e,h⟩).val, (c.dest ⟨e,h⟩).val) else u e

lemma cfg_free (c : Config u K Q R j) {e : Fin N} (he : e ∈ c.edges.val) : e ∉ K := by
  simpa using (Finset.mem_powersetCard.mp c.edges.prop).1 he

def child (c : Config u K Q R j) (L : Finset (Fin N)) : Finset (Graph N) :=
  tables (K ∪ c.edges.val) (upd c) (L \ Q.image fun e => (u e).1) R

lemma cfg_step (c : Config u K Q R j) {L : Finset (Fin N)} (hc : clean u K L Q)
    {g : Graph N} (hg : g ∈ child c L) : step g Q = c.edges.val := by
  obtain ⟨hfix,hfree⟩ := mem_tables.mp hg
  have old (e : Fin N) (he : e ∈ K) : g e = u e := by
    rw [hfix e (Finset.mem_union_left _ he)]
    exact dif_neg (fun h => cfg_free c h he)
  have fresh (e : Fin N) (he : e ∈ c.edges.val) :
      g e = ((c.src ⟨e,he⟩).val,(c.dest ⟨e,he⟩).val) := by
    rw [hfix e (Finset.mem_union_right _ he)]
    simp [upd, he]
  ext e
  simp only [step, next, Finset.mem_filter, Finset.mem_univ, true_and, endpt, Bool.false_eq_true,
    if_false]
  constructor
  · rintro ⟨a,ha,hne,heq⟩
    by_contra he
    rw [old a (hc.1 ha)] at heq
    by_cases hk : e ∈ K
    · rw [old e hk] at heq
      exact hne (hc.2.2 a ha e hk heq.symm)
    · have h := (Finset.mem_sdiff.mp (hfree e (by simp [he,hk])).1).2
      exact h (Finset.mem_image.mpr ⟨a,ha,heq⟩)
  · intro he
    obtain ⟨a,ha,heq⟩ := Finset.mem_image.mp (c.src ⟨e,he⟩).prop
    exact ⟨a,ha,fun h => cfg_free c he (h ▸ hc.1 ha), by rw [old a (hc.1 ha),fresh e he]; exact heq⟩

lemma child_subset (c : Config u K Q R j) {L : Finset (Fin N)} (hc : clean u K L Q) :
    child c L ⊆ tables K u L R := by
  intro g hg
  obtain ⟨hfix,hfree⟩ := mem_tables.mp hg
  apply mem_tables.mpr
  constructor
  · intro e he
    rw [hfix e (Finset.mem_union_left _ he)]
    exact dif_neg (fun h => cfg_free c h he)
  · intro e he
    by_cases hj : e ∈ c.edges.val
    · rw [hfix e (Finset.mem_union_right _ hj)]
      simp only [upd, dif_pos hj]
      obtain ⟨a,ha,h⟩ := Finset.mem_image.mp (c.src ⟨e,hj⟩).prop
      exact ⟨h ▸ hc.2.1 a ha,(Finset.mem_sdiff.mp (c.dest ⟨e,hj⟩).prop).1⟩
    · obtain ⟨hl,hr⟩ := hfree e (by simp [he,hj])
      exact ⟨(Finset.mem_sdiff.mp hl).1,hr⟩

lemma upd_old (c : Config u K Q R j) {e : Fin N} (he : e ∈ K) : upd c e = u e :=
  dif_neg (fun h => cfg_free c h he)

lemma upd_new (c : Config u K Q R j) (e : c.edges.val) :
    upd c e = ((c.src e).val,(c.dest e).val) := dif_pos e.prop

lemma clean_children (c : Config u K Q R j) {B : Finset (Fin N)} (hb : clean (flip u) K R B) :
    clean (flip (upd c)) (K ∪ c.edges.val) R (c.edges.val ∪ B) := by
  classical
  have hd (e : c.edges.val) : (upd c e).2 ∈ R ∧
      (upd c e).2 ∉ K.image (fun a => (u a).2) := by
    rw [upd_new]
    exact Finset.mem_sdiff.mp (c.dest e).prop
  refine ⟨Finset.union_subset (Finset.subset_union_right) (hb.1.trans Finset.subset_union_left), ?_, ?_⟩
  · intro e he
    rcases Finset.mem_union.mp he with hn | ho
    · exact (hd ⟨e,hn⟩).1
    · change (upd c e).2 ∈ R
      rw [upd_old c (hb.1 ho)]
      exact hb.2.1 e ho
  · intro e he a ha heq
    change (upd c a).2 = (upd c e).2 at heq
    rcases Finset.mem_union.mp he with hn | ho <;> rcases Finset.mem_union.mp ha with hak | han
    · rw [upd_old c hak] at heq
      exact False.elim ((hd ⟨e,hn⟩).2 (Finset.mem_image.mpr ⟨a,hak,heq⟩))
    · have h : c.dest ⟨a,han⟩ = c.dest ⟨e,hn⟩ := by
        apply Subtype.ext
        simpa only [upd_new c (⟨a,han⟩ : c.edges.val),upd_new c (⟨e,hn⟩ : c.edges.val)] using heq
      exact congrArg Subtype.val (c.dest.injective h)
    · rw [upd_old c hak,upd_old c (hb.1 ho)] at heq
      exact hb.2.2 e ho a hak heq
    · rw [upd_old c (hb.1 ho)] at heq
      exact False.elim ((hd ⟨a,han⟩).2 (Finset.mem_image.mpr ⟨e,hb.1 ho,heq.symm⟩))

lemma cfg_unique {i : ℕ} (c : Config u K Q R i) (d : Config u K Q R j) {L : Finset (Fin N)}
    (hc : clean u K L Q) {g : Graph N} (h₁ : g ∈ child c L) (h₂ : g ∈ child d L) :
    (⟨i,c⟩ : Σ j, Config u K Q R j) = ⟨j,d⟩ := by
  have he := (cfg_step c hc h₁).symm.trans (cfg_step d hc h₂)
  have hij : i = j := by
    have := (Finset.mem_powersetCard.mp c.edges.prop).2
    have := (Finset.mem_powersetCard.mp d.edges.prop).2
    grind
  subst j
  obtain ⟨m,s,t⟩ := c
  obtain ⟨m',s',t'⟩ := d
  have hmm : m = m' := Subtype.ext he
  subst m'
  congr 2
  · ext e
    have hf := (mem_tables.mp h₁).1 e (Finset.mem_union_right _ e.prop)
    have hf' := (mem_tables.mp h₂).1 e (Finset.mem_union_right _ e.prop)
    exact congrArg Fin.val (congrArg Prod.fst ((dif_pos e.prop).symm.trans (hf.symm.trans (hf'.trans (dif_pos e.prop)))))
  · ext e
    have hf := (mem_tables.mp h₁).1 e (Finset.mem_union_right _ e.prop)
    have hf' := (mem_tables.mp h₂).1 e (Finset.mem_union_right _ e.prop)
    exact congrArg Fin.val (congrArg Prod.snd ((dif_pos e.prop).symm.trans (hf.symm.trans (hf'.trans (dif_pos e.prop)))))

def flipEquiv (N : ℕ) : Graph N ≃ Graph N where
  toFun := flip
  invFun := flip
  left_inv _ := rfl
  right_inv _ := rfl

lemma flip_mem_tables (K : Finset (Fin N)) (u g : Graph N) (L R : Finset (Fin N)) :
    flip g ∈ tables K (flip u) R L ↔ g ∈ tables K u L R := by
  simp only [mem_tables,flip,Prod.swap_inj, Prod.fst_swap, Prod.snd_swap, and_comm]

def reach (g : Graph N) (Q B : Finset (Fin N)) : ℕ → Bool
  | 0 => decide Q.Nonempty
  | h+1 => reach (flip g) (step g Q ∪ B) ∅ h

def good (K : Finset (Fin N)) (u : Graph N) (L R Q B : Finset (Fin N)) (h : ℕ) (z : Bool) :=
  (tables K u L R).filter fun g => reach g Q B h = z

/-- Number of tables certified for an outcome with at most cap new edges per round. -/
def lower (N cap : ℕ) (z : Bool) : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
  | 0,k,l,r,q,_ => if decide (0 < q) = z then (l*r)^(N-k) else 0
  | h+1,k,l,r,q,b => ∑ j ∈ Finset.range (cap+1),
      ((N-k).choose j * q^j * (r-k).descFactorial j) *
        lower N cap z h (k+j) r (l-q) (j+b) 0

lemma clean_empty (u : Graph N) (K L : Finset (Fin N)) : clean u K L ∅ := by simp [clean]

lemma card_child_good (c : Config u K Q R j) {L B : Finset (Fin N)} (hc : clean u K L Q)
    (h : ℕ) (z : Bool) :
    ((child c L).filter fun g => reach g Q B (h+1) = z).card =
      (good (K ∪ c.edges.val) (flip (upd c)) R (L \ Q.image fun e => (u e).1)
        (c.edges.val ∪ B) ∅ h z).card := by
  apply Finset.card_equiv (flipEquiv N)
  intro g
  simp only [good, Finset.mem_filter]
  change _ ↔ flip g ∈ _ ∧ reach (flip g) _ ∅ h = z
  rw [flip_mem_tables]
  exact and_congr_right fun hg => by rw [reach,cfg_step c hc hg]

lemma lower_bound (cap : ℕ) (z : Bool) (h : ℕ) (u : Graph N) (K L R Q B : Finset (Fin N))
    (hc : clean u K L Q) (hb : clean (flip u) K R B) :
    lower N cap z h K.card L.card R.card Q.card B.card ≤ (good K u L R Q B h z).card := by
  classical
  induction h generalizing u K L R Q B with
  | zero =>
    simp only [lower,good,reach,Finset.card_pos]
    split_ifs with hz <;> simp [hz,card_tables]
  | succ h ih =>
    let I := (Finset.range (cap+1)).sigma fun j => (Finset.univ : Finset (Config u K Q R j))
    let F (p : Σ j, Config u K Q R j) :=
      (child p.2 L).filter fun g => reach g Q B (h+1) = z
    have hdis : (I : Set _).PairwiseDisjoint F := by
      intro p _ p' _ hne
      apply Finset.disjoint_left.mpr
      intro g hg hg'
      exact hne (cfg_unique p.2 p'.2 hc (Finset.mem_filter.mp hg).1 (Finset.mem_filter.mp hg').1)
    have hsub : I.biUnion F ⊆ good K u L R Q B (h+1) z := by
      intro g hg
      obtain ⟨p,_,hp⟩ := Finset.mem_biUnion.mp hg
      obtain ⟨hg,hz⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_filter.mpr ⟨child_subset p.2 hc hg,hz⟩
    apply le_trans _ (Finset.card_le_card hsub)
    rw [Finset.card_biUnion hdis, Finset.sum_sigma]
    apply Finset.sum_le_sum
    intro j hj
    let m := lower N cap z h (K.card+j) R.card (L.card-Q.card) (j+B.card) 0
    have hct : (N-K.card).choose j * Q.card^j * (R.card-K.card).descFactorial j ≤
        Fintype.card (Config u K Q R j) := by
      rw [card_config hc]
      gcongr
      exact (Nat.sub_le_sub_left Finset.card_image_le _).trans (Finset.le_card_sdiff _ _)
    apply le_trans (Nat.mul_le_mul_right m hct)
    change Fintype.card (Config u K Q R j) * m ≤ _
    rw [← Finset.card_univ, ← Nat.nsmul_eq_mul, ← Finset.sum_const]
    apply Finset.sum_le_sum
    intro c _
    change m ≤ ((child c L).filter _).card
    rw [card_child_good c hc h z]
    have ht := ih (flip (upd c)) (K ∪ c.edges.val) R (L \ Q.image fun e => (u e).1)
      (c.edges.val ∪ B) ∅ (clean_children c hb) (clean_empty _ _ _)
    have hj' := (Finset.mem_powersetCard.mp c.edges.prop).2
    have hds : Disjoint K c.edges.val := Finset.disjoint_left.mpr fun _ hk hn => cfg_free c hn hk
    have hdb : Disjoint c.edges.val B := Finset.disjoint_left.mpr fun _ hn ho => cfg_free c hn (hb.1 ho)
    have him : Q.image (fun e => (u e).1) ⊆ L := Finset.image_subset_iff.mpr hc.2.1
    simpa only [Finset.card_union_of_disjoint hds, Finset.card_union_of_disjoint hdb,hj',
      Finset.card_empty, Finset.card_sdiff_of_subset him, clean_image_card hc, m] using ht

lemma shiftRatio (a : ℕ) :
    Tendsto (fun n : ℕ => ((n-a : ℕ) : ℝ) / n) atTop (𝓝 1) := by
  have H := (tendsto_const_nhds (x := (1:ℝ))).sub (tendsto_const_div_atTop_nhds_zero_nat (a:ℝ))
  simp only [sub_zero] at H
  refine H.congr' ?_
  filter_upwards [eventually_ge_atTop a,eventually_gt_atTop 0] with n ha hn
  rw [Nat.cast_sub ha]
  field_simp

lemma shiftFall (a j : ℕ) :
    Tendsto (fun n : ℕ => ((n-a).descFactorial j : ℝ) / (n:ℝ)^j) atTop (𝓝 1) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have H := (shiftRatio (a+j)).mul ih
    simp only [one_mul] at H
    convert H using 1
    ext n
    rw [Nat.descFactorial_succ,Nat.cast_mul,pow_succ, Nat.sub_sub]
    ring

lemma shiftChoose (a j : ℕ) :
    Tendsto (fun n : ℕ => ((n-a).choose j : ℝ) / (n:ℝ)^j) atTop (𝓝 (1 / (j.factorial:ℝ))) := by
  convert (shiftFall a j).div_const (j.factorial : ℝ) using 1
  ext n
  rw [Nat.choose_eq_descFactorial_div_factorial,
    Nat.cast_div (Nat.factorial_dvd_descFactorial _ _) (by positivity : (j.factorial : ℝ) ≠ 0)]
  ring

lemma shiftPow (a k : ℕ) :
    Tendsto (fun n : ℕ => (((n-a : ℕ) : ℝ) / n)^(n-k)) atTop (𝓝 (Real.exp (-(a:ℝ)))) := by
  have H := (Real.tendsto_one_add_div_pow_exp (-(a:ℝ))).div ((shiftRatio a).pow k) (by simp)
  simp only [one_pow, div_one] at H
  refine H.congr' ?_
  filter_upwards [eventually_gt_atTop a,eventually_ge_atTop k] with n ha hk
  have hn : (n:ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hp : ((n-a : ℕ) : ℝ) / n ≠ 0 := div_ne_zero (by exact_mod_cast (show n-a ≠ 0 by omega)) hn
  have hr : 1 + -(a:ℝ) / n = ((n-a : ℕ) : ℝ) / n := by
    rw [Nat.cast_sub ha.le]
    field_simp; ring
  change (1 + -(a:ℝ) / n)^n / _ = _
  rw [hr, div_eq_mul_inv, ← pow_sub₀ _ hp hk]

noncomputable def pois (q j : ℕ) : ℝ := Real.exp (-(q:ℝ)) * (q:ℝ)^j / j.factorial

noncomputable def model (cap : ℕ) (z : Bool) : ℕ → ℕ → ℕ → ℝ
  | 0,q,_ => if decide (0 < q) = z then 1 else 0
  | h+1,q,b => ∑ j ∈ Finset.range (cap+1), pois q j * model cap z h (j+b) 0

lemma lower_lim (cap : ℕ) (z : Bool) (h k l r q b : ℕ) :
    Tendsto (fun n : ℕ => (lower n cap z h k (n-l) (n-r) q b : ℝ) / (n:ℝ)^(2*(n-k)))
      atTop (𝓝 (Real.exp (-(l:ℝ) - r) * model cap z h q b)) := by
  induction h generalizing k l r q b with
  | zero =>
    simp only [lower,model]
    split_ifs
    · rw [mul_one,sub_eq_add_neg,Real.exp_add]
      convert (shiftPow l k).mul (shiftPow r k) using 1
      ext n
      simp only [Nat.cast_pow,Nat.cast_mul,div_pow,mul_pow,pow_mul,pow_two]
      ring
    · simp
  | succ h ih =>
    simp only [lower,model,Nat.cast_sum,Finset.sum_div,Finset.mul_sum]
    apply tendsto_finsetSum
    intro j _
    have H := (((shiftChoose k j).mul_const ((q:ℝ)^j)).mul (shiftFall (r+k) j)).mul
      (ih (k+j) r (l+q) (j+b) 0)
    convert H.congr' _ using 1
    · simp only [pois,Nat.cast_add]
      rw [show -(r:ℝ) - (l+q) = (-(l:ℝ)-r) + (-q) by ring, Real.exp_add]
      ring
    · filter_upwards [eventually_ge_atTop (k+j)] with n hn
      simp only [Nat.cast_mul,Nat.cast_pow,Nat.sub_sub]
      have he : 2*(n-k) = j + j + 2*(n-(k+j)) := by omega
      rw [he, pow_add, pow_add]
      ring


lemma pois_nonneg (q j : ℕ) : 0 ≤ pois q j := by unfold pois; positivity

lemma pois_sum (q : ℕ) : HasSum (pois q) 1 := by
  unfold pois
  simpa using ProbabilityTheory.hasSum_one_poissonMeasure (q : NNReal)

lemma model_bounds (cap : ℕ) (z : Bool) (h q b : ℕ) :
    0 ≤ model cap z h q b ∧ model cap z h q b ≤ 1 := by
  induction h generalizing q b with
  | zero => simp only [model]; split <;> norm_num
  | succ h ih =>
    constructor
    · exact Finset.sum_nonneg fun j _ => mul_nonneg (pois_nonneg q j) (ih (j+b) 0).1
    · calc
        _ ≤ ∑ j ∈ Finset.range (cap+1), pois q j :=
          Finset.sum_le_sum fun j _ => mul_le_of_le_one_right (pois_nonneg _ _) (ih _ _).2
        _ ≤ 1 := (pois_sum q).tsum_eq ▸ (pois_sum q).summable.sum_le_tsum _ (fun j _ => pois_nonneg q j)

noncomputable def dead : ℕ → ℝ
  | 0 => 0
  | h+1 => Real.exp (dead h - 1)

noncomputable def extinction : ℕ → ℕ → ℕ → ℝ
  | 0, q, _ => (0 : ℝ)^q
  | h+1,q,b => dead (h+1)^q * dead h^b

lemma extinction_no_delay (h q : ℕ) : extinction h q 0 = dead h^q := by
  cases h <;> simp [extinction,dead]

lemma exp_pgf (q : ℕ) (x : ℝ) :
    HasSum (fun j => pois q j * x^j) (Real.exp (x-1)^q) := by
  have H := ((NormedSpace.expSeries_div_hasSum_exp ((q:ℝ)*x)).mul_left (Real.exp (-(q:ℝ))))
  have hr : Real.exp (x-1)^q = Real.exp (-(q:ℝ)) * NormedSpace.exp ((q:ℝ)*x) := by
    rw [← Real.exp_nat_mul, ← Real.exp_eq_exp_ℝ, ← Real.exp_add]
    congr 1
    ring
  rw [hr]
  exact H.congr_fun (fun j => by simp only [pois, mul_pow]; ring)

lemma extinction_sum (h q b : ℕ) :
    HasSum (fun j => pois q j * extinction h (j+b) 0) (extinction (h+1) q b) := by
  simp_rw [extinction_no_delay]
  simpa only [pow_add, ← mul_assoc, extinction, dead] using
    (exp_pgf q (dead h)).mul_right (dead h^b)

noncomputable def prob (z : Bool) (h q b : ℕ) : ℝ :=
  if z then 1-extinction h q b else extinction h q b

lemma prob_sum (z : Bool) (h q b : ℕ) :
    HasSum (fun j => pois q j * prob z h (j+b) 0) (prob z (h+1) q b) := by
  cases z
  · exact extinction_sum h q b
  · simpa [prob,mul_sub] using (pois_sum q).sub (extinction_sum h q b)

lemma model_lim (z : Bool) (h q b : ℕ) :
    Tendsto (fun cap => model cap z h q b) atTop (𝓝 (prob z h q b)) := by
  induction h generalizing q b with
  | zero =>
    cases z <;> cases q <;> simp [model,prob,extinction]
  | succ h ih =>
    let F (cap j : ℕ) := if j ≤ cap then pois q j * model cap z h (j+b) 0 else 0
    have H (j : ℕ) : Tendsto (F · j) atTop (𝓝 (pois q j * prob z h (j+b) 0)) := by
      refine ((ih (j+b) 0).const_mul _).congr' ?_
      filter_upwards [eventually_ge_atTop j] with cap hc using by simp [F,hc]
    have hb (cap j : ℕ) : ‖F cap j‖ ≤ pois q j := by
      dsimp [F]
      split
      · rw [abs_of_nonneg (mul_nonneg (pois_nonneg _ _) (model_bounds ..).1)]
        exact mul_le_of_le_one_right (pois_nonneg _ _) (model_bounds ..).2
      · simpa using pois_nonneg q j
    have T := tendsto_tsum_of_dominated_convergence (pois_sum q).summable H (Eventually.of_forall hb)
    rw [(prob_sum z h q b).tsum_eq] at T
    refine T.congr fun cap => ?_
    change ∑' j, F cap j = _
    rw [tsum_eq_sum (s := Finset.range (cap+1)) (fun j hj => by
      simp only [Finset.mem_range] at hj
      simp [F,show ¬ j ≤ cap by omega])]
    exact Finset.sum_congr rfl fun j hj => if_pos (by simpa [Nat.lt_succ_iff] using hj)

def oriented (s : Bool) (g : Graph N) : Graph N := if s then flip g else g

lemma step_oriented (s : Bool) (g : Graph N) (Q : Finset (Fin N)) :
    step (oriented s g) Q = next s g Q := by cases s <;> rfl

lemma flip_side (n : ℕ) (g : Graph N) :
    flip (oriented (side (n+1)) g) = oriented (side n) g := by
  have hs : side (n+1) = !(side n) := by
    unfold side
    by_cases h : n % 2 = 1
    · simp [h,show (n+1)%2 ≠ 1 by omega]
    · simp [h,show (n+1)%2 = 1 by omega]
  rw [hs]
  cases side n <;> rfl

lemma reach_arms (g : Graph N) (n : ℕ) (Q B : Finset (Fin N)) :
    reach (oriented (side n) g) Q B (n+1) = true ↔
      (∃ e ∈ Q, arm g (n+1) e) ∨ ∃ e ∈ B, arm g n e := by
  induction n generalizing Q B with
  | zero =>
    simp [reach,step_oriented,next,arm, Finset.Nonempty]
    grind
  | succ n ih =>
    rw [reach, flip_side,ih, step_oriented]
    simp only [next,Finset.mem_union,Finset.mem_filter,Finset.mem_univ,true_and,
      Finset.notMem_empty, false_and, exists_false,or_false]
    change _ ↔ (∃ e ∈ Q, ∃ j, j ≠ e ∧ _ ∧ arm g (n+1) j) ∨ _
    grind

/-- The second root can enter one round later, when its side becomes active. -/
def marks (a : Bool) (e : Fin N) : Finset (Fin N) := if a then {e} else ∅

lemma card_marks (a : Bool) (e : Fin N) : (marks a e).card = a.toNat := by cases a <;> simp [marks]

lemma clean_root (u : Graph N) (e : Fin N) (a : Bool) : clean u {e} Finset.univ (marks a e) := by
  cases a <;> simp [marks,clean]

def query (s : Bool) (e : Fin N) (h : ℕ) (a b z : Bool) :=
  Finset.univ.filter fun g : Graph N => reach (oriented s g) (marks a e) (marks b e) h = z

lemma query_card_oriented (s : Bool) (e : Fin N) (h : ℕ) (a b z : Bool) :
    (query s e h a b z).card = (query false e h a b z).card := by
  cases s
  · rfl
  · apply Finset.card_equiv (flipEquiv N)
    intro g
    simp [query,oriented,flipEquiv]
    rfl

lemma root_bound (s : Bool) (e : Fin N) (cap h : ℕ) (a b z : Bool) :
    N^2 * lower N cap z h 1 N N a.toNat b.toNat ≤ (query s e h a b z).card := by
  classical
  rw [query_card_oriented]
  let S := query false e h a b z
  rw [Finset.card_eq_sum_card_fiberwise (s := S) (t := Finset.univ)
    (f := fun g => g e) (fun _ _ => Finset.mem_univ _)]
  have hct : N^2 = Fintype.card (Fin N × Fin N) := by simp [pow_two]
  rw [hct,← Finset.card_univ,← Nat.nsmul_eq_mul,← Finset.sum_const]
  apply Finset.sum_le_sum
  intro v _
  have H := lower_bound cap z h (fun _ => v) {e} Finset.univ Finset.univ (marks a e) (marks b e)
    (clean_root _ _ _) (clean_root _ _ _)
  simp only [Finset.card_singleton,Finset.card_univ,Fintype.card_fin,card_marks] at H
  apply H.trans
  apply Finset.card_le_card
  intro g hg
  obtain ⟨hg,hz⟩ := Finset.mem_filter.mp hg
  have he := (mem_tables.mp hg).1 e (Finset.mem_singleton_self _)
  exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hz⟩,he⟩

noncomputable def queryFrac (N h : ℕ) (s a b z : Bool) : ℝ :=
  if hn : 0 < N then ((query s ⟨0,hn⟩ h a b z).card : ℝ) / (N:ℝ)^(2*N) else 0

lemma frac_bound (cap h : ℕ) (s a b z : Bool) :
    ∀ᶠ n : ℕ in atTop,
      (lower n cap z h 1 n n a.toNat b.toNat : ℝ) / (n:ℝ)^(2*(n-1)) ≤ queryFrac n h s a b z := by
  filter_upwards [eventually_gt_atTop 0] with n hn
  rw [queryFrac,dif_pos hn]
  have hpow : 2*n = 2 + 2*(n-1) := by omega
  rw [hpow,pow_add]
  have hn' : 0 < (n:ℝ) := by exact_mod_cast hn
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have H : (n:ℝ)^2 * (lower n cap z h 1 n n a.toNat b.toNat : ℝ) ≤
      ((query s ⟨0,hn⟩ h a b z).card : ℝ) := by exact_mod_cast root_bound s ⟨0,hn⟩ cap h a b z
  nlinarith only [mul_le_mul_of_nonneg_right H (show 0 ≤ (n:ℝ)^(2*(n-1)) by positivity)]

lemma frac_add (h : ℕ) (s a b : Bool) :
    ∀ᶠ n : ℕ in atTop, queryFrac n h s a b true + queryFrac n h s a b false = 1 := by
  classical
  filter_upwards [eventually_gt_atTop 0] with n hn
  simp only [queryFrac,dif_pos hn, ← add_div,← Nat.cast_add,query]
  have H := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Graph n)))
    (p := fun g => reach (oriented s g) (marks a ⟨0,hn⟩) (marks b ⟨0,hn⟩) h = true)
  simp only [Bool.not_eq_true] at H
  rw [H]
  simp [Graph, pow_mul, pow_two, mul_pow, show (n:ℝ) ≠ 0 by exact_mod_cast hn.ne']

lemma frac_lower_limit (h : ℕ) (s a b z : Bool) (x : ℝ)
    (hx : x < prob z h a.toNat b.toNat) :
    ∀ᶠ n : ℕ in atTop, x < queryFrac n h s a b z := by
  obtain ⟨cap,hcap⟩ := ((model_lim z h a.toNat b.toNat).eventually_const_lt hx).exists
  have H : Tendsto (fun n : ℕ => (lower n cap z h 1 n n a.toNat b.toNat : ℝ) / (n:ℝ)^(2*(n-1)))
      atTop (𝓝 (model cap z h a.toNat b.toNat)) := by
    simpa using lower_lim cap z h 1 0 0 a.toNat b.toNat
  filter_upwards [H.eventually_const_lt hcap,frac_bound cap h s a b z] with n h₁ h₂
  exact h₁.trans_le h₂

lemma frac_lim (h : ℕ) (s a b : Bool) :
    Tendsto (fun n => queryFrac n h s a b true) atTop (𝓝 (1-extinction h a.toNat b.toNat)) := by
  apply tendsto_order.mpr
  constructor
  · exact frac_lower_limit h s a b true
  · intro y hy
    have H := frac_lower_limit h s a b false (1-y) (by change _ < extinction ..; linarith)
    filter_upwards [H,frac_add h s a b] with n h₁ h₂
    linarith

lemma query_succ {g : Graph N} (e : Fin N) (n : ℕ) (a b : Bool) :
    g ∈ query (side n) e (n+1) a b true ↔
      (a = true ∧ arm g (n+1) e) ∨ (b = true ∧ arm g n e) := by
  simp only [query, Finset.mem_filter, Finset.mem_univ,true_and,reach_arms]
  cases a <;> cases b <;> simp [marks]

lemma f_query (n : ℕ) :
    ∀ᶠ N : ℕ in atTop, f N (n+1) =
      queryFrac N (n+1) (side n) true false true + queryFrac N (n+1) (side n) false true true -
      queryFrac N (n+1) (side n) true true true := by
  classical
  filter_upwards [eventually_gt_atTop 0] with N hn
  let e : Fin N := ⟨0,hn⟩
  rw [f_root (n+1) e]
  simp only [queryFrac,dif_pos hn,← add_div,← sub_div]
  apply congrArg (· / (N:ℝ)^(2*N))
  let A := query (side n) e (n+1) true false true
  let B := query (side n) e (n+1) false true true
  have h₁ : A ∩ B = survivors N (n+1) e := by
    ext g
    simp [A,B,survivors,query_succ,remaining_iff]
  have h₂ : A ∪ B = query (side n) e (n+1) true true true := by
    ext g
    simp [A,B,query_succ]
  have he := Finset.card_union_add_card_inter A B
  rw [h₁,h₂] at he
  exact_mod_cast (show (↑(survivors N (n+1) e).card : ℤ) =
    (A.card:ℤ) + B.card - (query (side n) e (n+1) true true true).card by omega)

lemma dead_eq (n : ℕ) : dead n = 1 - seqA (n+1) := by
  induction n with
  | zero => simp [dead,seqA]
  | succ n ih => simp [dead,seqA,ih]

lemma base_lim : Tendsto (fun N => f N 0) atTop (𝓝 (seqA 0 * seqA 1)) := by
  simp only [seqA, mul_one]
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hn
  rw [f_root 0 (⟨0,hn⟩ : Fin N)]
  simp [survivors,remaining,Graph,pow_mul,pow_two,mul_pow, show (N:ℝ) ≠ 0 by exact_mod_cast hn.ne']

theorem all_rounds (i : ℕ) : Tendsto (fun N => f N i) atTop (𝓝 (seqA i * seqA (i+1))) := by
  cases i with
  | zero => exact base_lim
  | succ n =>
    have H := ((frac_lim (n+1) (side n) true false).add (frac_lim (n+1) (side n) false true)).sub
      (frac_lim (n+1) (side n) true true)
    have he := (f_query n).mono fun _ hn => hn.symm
    convert H.congr' he using 1
    simp only [extinction, Bool.toNat_true,Bool.toNat_false,pow_one,pow_zero,mul_one,one_mul,dead_eq]
    ring

end Cuckoo

theorem OMA.solution : type_of% @OMA.S_mo_327172.main := Cuckoo.all_rounds
