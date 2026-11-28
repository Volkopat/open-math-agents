import OMAStatements.S_oeis_a363265

-- Credit: @rleshner (agent: Codex, model: GPT-6)

/-!
# Nine does not occur in Gus Wiseman's unique-mode factorization sequence

Replace each factor by its multiset of prime divisors, with multiplicity.
Unique factorization identifies multiplicative factorizations with partitions
of the multiset of primes into nonempty blocks. It preserves multiplicities
of equal factors, hence also the unique-mode condition.

If all prime factors are distinct, a block cannot occur twice. Only the
one-block partition can have a unique mode. For a multiset of at least
seven prime factors with a repeated prime, choose seven including two equal
ones. In each equality pattern on these seven atoms, ten distinct modal
partitions have a largest block with the following property. Removing that
block leaves either the empty family or a unique mode of multiplicity at
least two. Add all remaining atoms to the chosen block. When the added
multiset is nonempty, the enlarged block is the unique largest block, so
the partition still has a unique mode and removing the added atoms
recovers the original partition. This gives at least ten factorizations.

The finite certificates below treat equality patterns of sorted lists of at
most seven primes. Their numeric keys have one octal digit per position,
from least to most significant. Equal digits assign positions to the same
block. The kernel checks ten distinct witnesses per tabulated pattern, and
direct enumeration treats the smaller cases.

Source: https://oeis.org/A363265
-/

namespace ModalPartitions
open Multiset
abbrev Block := Multiset ℕ
abbrev Family := Multiset Block

private def Mode {α : Type} [DecidableEq α] (s : Multiset α) : Prop :=
  ∃ x ∈ s, ∀ y ∈ s, y ≠ x → s.count y < s.count x

private instance {α : Type} [DecidableEq α] (s : Multiset α) : Decidable (Mode s) := by
  exact decidable_of_iff (∃ x ∈ s.toFinset, ∀ y ∈ s.toFinset, y ≠ x → s.count y < s.count x) (by simp [Mode])

private theorem mode_map {α β : Type} [DecidableEq α] [DecidableEq β]
    (s : Multiset α) (f : α → β) (hf : Set.InjOn f {x | x ∈ s}) :
    Mode (s.map f) ↔ Mode s := by
  constructor
  · rintro ⟨_,hxm,hm⟩
    obtain ⟨x,hx,rfl⟩ := mem_map.mp hxm
    refine ⟨x,hx, fun y hy hne => ?_⟩
    have h := hm _ (mem_map.mpr ⟨y,hy,rfl⟩) (fun he => hne (hf hy hx he))
    simpa [count_map_eq_count f s hf _ hy,count_map_eq_count f s hf _ hx] using h
  · rintro ⟨x,hx,hm⟩
    refine ⟨f x,mem_map.mpr ⟨x,hx,rfl⟩,?_⟩
    rintro _ hym hne
    obtain ⟨y,hy,rfl⟩ := mem_map.mp hym
    simpa [count_map_eq_count f s hf _ hy,count_map_eq_count f s hf _ hx] using
      hm y hy (fun h => hne (congrArg f h))

private def Proper (g : Family) : Prop := ∀ b ∈ g, b ≠ 0

private theorem sum_mem (g : Family) (x : ℕ) : x ∈ g.sum ↔ ∃ b ∈ g, x ∈ b := by
  induction g using Multiset.induction_on with
  | empty => simp
  | cons b g ih => simp [ih]

private def extend (x : ℕ) (g : Family) : Finset Family :=
  insert (({x} : Block) ::ₘ g) (g.toFinset.image fun b => (x ::ₘ b) ::ₘ g.erase b)

private def parts : List ℕ → Finset Family
  | [] => {0}
  | x::l => (parts l).biUnion (extend x)

private theorem parts_spec (l : List ℕ) (g : Family) :
    g ∈ parts l ↔ Proper g ∧ g.sum = (l : Block) := by
  induction l generalizing g with
  | nil =>
    constructor
    · intro hg; have : g=0 := by simpa [parts] using hg
      subst g; simp [Proper]
    · rintro ⟨hg,hs⟩
      have hz : ∀ b ∈ g, b=0 := sum_eq_zero_iff.mp hs
      have : g=0 := by
        by_contra ha
        obtain ⟨b,hb⟩ := exists_mem_of_ne_zero ha
        exact hg b hb (hz b hb)
      simpa [parts] using this
  | cons x l ih =>
    constructor
    · intro h
      obtain ⟨s,hs,hg⟩ := Finset.mem_biUnion.mp h
      obtain ⟨hp,hv⟩ := (ih s).1 hs
      rcases Finset.mem_insert.mp hg with rfl | hg
      · simp [Proper] at hp ⊢
        exact ⟨hp,by simpa [singleton_add] using congrArg (x ::ₘ ·) hv⟩
      · obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hg
        have hb' : b ∈ s := mem_toFinset.mp hb
        obtain ⟨t,rfl⟩ := exists_cons_of_mem hb'
        simp [Proper] at hp ⊢
        refine ⟨hp.2,?_⟩
        simpa [cons_add] using congrArg (x ::ₘ ·) hv
    · rintro ⟨hp,hs⟩
      have hsumx : x ∈ g.sum := by rw [hs]; simp
      obtain ⟨b,hb,hx⟩ := (sum_mem g x).mp hsumx
      obtain ⟨t,rfl⟩ := exists_cons_of_mem hb
      obtain ⟨c,rfl⟩ := exists_cons_of_mem hx
      have hrest : Proper t := fun a ha => hp a (mem_cons_of_mem ha)
      have ht : c + t.sum = (l : Block) := by
        simpa only [Multiset.sum_cons, cons_add, ← cons_coe, cons_inj_right] using hs
      by_cases hc : c = 0
      · subst c
        apply Finset.mem_biUnion.mpr
        refine ⟨t,(ih t).2 ⟨hrest,by simpa using ht⟩,?_⟩
        exact Finset.mem_insert_self _ _
      · apply Finset.mem_biUnion.mpr
        refine ⟨c ::ₘ t,(ih _).2 ⟨?_, by simpa using ht⟩,?_⟩
        · simpa [Proper] using And.intro hc hrest
        · apply Finset.mem_insert_of_mem
          apply Finset.mem_image.mpr
          exact ⟨c, by simp, by simp⟩

private def valid (l : List ℕ) := (parts l).filter Mode

private theorem valid_spec (l : List ℕ) (g : Family) :
    g ∈ valid l ↔ (Proper g ∧ g.sum = (l : Block)) ∧ Mode g := by
  simp [valid,parts_spec]

private def atoms (n : ℕ) : Block := n.primeFactorsList

private theorem finish_atoms {b : Block} (h : ∀ p ∈ b, Nat.Prime p) :
    atoms b.prod = b := by
  induction b using Quotient.inductionOn with
  | _ l =>
    exact (Multiset.coe_eq_coe.mpr (Nat.primeFactorsList_unique rfl h)).symm

private theorem atoms_prod {n : ℕ} (hn : n ≠ 0) : (atoms n).prod = n :=
  Nat.prod_primeFactorsList hn

private theorem atoms_mul {a b : ℕ} (ha : a≠0) (hb : b≠0) :
    atoms (a*b) = atoms a + atoms b :=
  Multiset.coe_eq_coe.mpr (Nat.perm_primeFactorsList_mul ha hb)

private theorem prod_blocks (g : Family) :
    (g.map Multiset.prod).prod = g.sum.prod := by
  induction g using Multiset.induction_on with
  | empty => simp
  | cons _ _ ih => simp [ih]

private theorem atoms_factors (f : Multiset ℕ) (hp : ∀ x ∈ f, 1<x) :
    (f.map atoms).sum = atoms f.prod := by
  induction f using Multiset.induction_on with
  | empty => simp [atoms]
  | cons a f ih =>
    have ha : 1<a := hp a (by simp)
    have hf : ∀ x∈f, 1<x := fun x hx => hp x (by simp [hx])
    have hn : 0 ∉ f := fun h => Nat.not_lt_zero 1 (hf 0 h)
    simp [ih hf, atoms_mul (by omega : a≠0) (prod_ne_zero hn)]

private theorem a_card {n : ℕ} (hn : n≠0) :
    OMA.S_oeis_a363265.a n = (valid n.primeFactorsList).card := by
  let S := valid n.primeFactorsList
  have primeBlocks {g : Family} (hg : g ∈ S) {b : Block} (hb : b∈g) :
      ∀ x∈b, Nat.Prime x := by
    intro x hx
    have h := (sum_mem g x).2 ⟨b,hb,hx⟩
    rw [((valid_spec _ _).1 hg).1.2] at h
    exact Nat.prime_of_mem_primeFactorsList h
  have recover {g : Family} (hg : g ∈ S) :
      (g.map Multiset.prod).map atoms = g := by
    rw [map_map]
    exact (map_congr (g:=id) rfl (fun b hb => finish_atoms (primeBlocks hg hb))).trans (Multiset.map_id g)
  have himage : {f : Multiset ℕ | OMA.S_oeis_a363265.IsUniqueModeFactorization n f} =
      (fun g : Family => g.map Multiset.prod) '' (S : Set Family) := by
    ext f
    constructor
    · rintro ⟨hf,hs,hm⟩
      have hx {x : ℕ} (hh : x∈f) : (atoms x).prod=x := atoms_prod (by have := hf x hh; omega)
      have hi : Set.InjOn atoms {x | x ∈ f} := fun x hp y hq he => by
        simpa [hx hp,hx hq] using congrArg Multiset.prod he
      refine ⟨f.map atoms,(valid_spec _ _).2 ⟨⟨?_,by rw [atoms_factors f hf,hs]; rfl⟩,
        (mode_map f atoms hi).2 hm⟩,?_⟩
      · rintro _ hh hz
        obtain ⟨x,hxf,rfl⟩ := mem_map.mp hh
        have hx' := hx hxf
        have hr := hf x hxf
        rw [hz] at hx'
        simp at hx'
        omega
      · change (f.map atoms).map Multiset.prod = f
        rw [map_map]
        exact (map_congr (g:=id) rfl (fun x hx' => hx hx')).trans (Multiset.map_id f)
    · rintro ⟨g,hg,rfl⟩
      obtain ⟨⟨hne,hf⟩,hm⟩ := (valid_spec _ _).1 hg
      have hi : Set.InjOn Multiset.prod {x | x ∈ g} := fun b hb c hc he => by
        simpa [finish_atoms (primeBlocks hg hb),finish_atoms (primeBlocks hg hc)] using congrArg atoms he
      refine ⟨?_,by rw [prod_blocks,hf]; exact atoms_prod hn,(mode_map _ _ hi).2 hm⟩
      rintro _ hh
      obtain ⟨b,hbg,rfl⟩ := mem_map.mp hh
      have hb := hne b hbg
      have hu := finish_atoms (primeBlocks hg hbg)
      by_contra! h
      rcases (by omega : b.prod=0 ∨ b.prod=1) with h|h <;> simp [h,atoms] at hu <;> exact hb hu.symm
  unfold OMA.S_oeis_a363265.a
  rw [himage, Set.InjOn.ncard_image, Set.ncard_coe_finset]
  intro g hg h hh he
  simpa [recover hg, recover hh] using congrArg (Multiset.map atoms) he

private def Strong (g : Family) : Prop :=
  ∃ m ∈ g.toFinset, 2 ≤ g.count m ∧ ∀ x ∈ g.toFinset, x ≠ m → g.count x < g.count m
private instance (g : Family) : Decidable (Strong g) := by unfold Strong; infer_instance

private def Sturdy (g : Family) : Prop :=
  ∃ b ∈ g.toFinset, (∀ x ∈ g.toFinset, x.card ≤ b.card) ∧
    (g.erase b = 0 ∨ Strong (g.erase b))
private instance (g : Family) : Decidable (Sturdy g) := by unfold Sturdy; infer_instance
private def sturdy (l : List ℕ) := (valid l).filter Sturdy

private def codes : ℕ → Finset (List ℕ)
  | 0 => {[]}
  | k+1 => (codes k).biUnion fun l => {(k+1)::l, (l.headD (k+1))::l}


private theorem code_bound {k : ℕ} {c : List ℕ} (hc : c ∈ codes k) :
    ∀ x∈c, x ≤ k := by
  induction k generalizing c with
  | zero => simp [codes] at hc; subst c; simp
  | succ k ih =>
    obtain ⟨l,hl,hh⟩ := Finset.mem_biUnion.mp hc
    have htop : l.headD (k+1) ≤ k+1 := by
      cases l with
      | nil => simp
      | cons a s => simpa using Nat.le_succ_of_le (ih hl a (by simp))
    simp only [Finset.mem_insert,Finset.mem_singleton] at hh
    rcases hh with rfl | rfl <;> intro x hx <;> rcases List.mem_cons.mp hx with rfl|hx
    · omega
    · exact Nat.le_succ_of_le (ih hl _ hx)
    · exact htop
    · exact Nat.le_succ_of_le (ih hl _ hx)

private theorem canonical (s : List ℕ) (hs : s.Pairwise (· ≤ ·)) :
    ∃ c ∈ codes s.length, ∃ e : Equiv.Perm ℕ, c.map e = s := by
  induction s with
  | nil => exact ⟨[],by simp [codes],Equiv.refl _,rfl⟩
  | cons a l ih =>
    obtain ⟨hal,hsl⟩ := List.pairwise_cons.mp hs
    obtain ⟨c,hc,e,he⟩ := ih hsl
    by_cases ha : a ∈ l
    · obtain ⟨b,t,rfl⟩ := List.exists_cons_of_ne_nil (show c≠[] by rintro rfl; simp at he; subst l; simp at ha)
      rw [←he] at hal ha
      have hba : e b ≤ a := by
        cases hl : (b::t).map e with
        | nil => simp at hl
        | cons v r =>
          have hsr : (v::r).Pairwise (·≤·) := by simpa [he,←hl] using hsl
          have hav : a=v ∨ a∈r := List.mem_cons.mp (hl ▸ ha)
          have hv : v=e b := by simpa using congrArg (List.headD · 0) hl.symm
          rcases hav with hav|hav
          · omega
          · simpa [hv] using (List.pairwise_cons.mp hsr).1 a hav
      have hab : a=e b := by have := hal (e b) (by simp); omega
      refine ⟨b::b::t,Finset.mem_biUnion.mpr ⟨b::t,hc,by simp⟩,e,?_⟩
      simp [hab,←he]
    · let j := l.length+1
      have hj : j ∉ c := fun h => (by have hh:=code_bound hc j h; dsimp [j] at hh; omega)
      let e' := e.trans (Equiv.swap (e j) a)
      have hmap : c.map e' = c.map e := by
        apply List.map_congr_left
        intro x hx
        have hne : e x ≠ e j := fun he => hj ((e.injective he) ▸ hx)
        have hna : e x ≠ a := fun h => ha (he ▸ List.mem_map.mpr ⟨x,hx,h⟩)
        exact Equiv.swap_apply_of_ne_of_ne hne hna
      refine ⟨j::c, Finset.mem_biUnion.mpr ⟨c,hc,Finset.mem_insert_self _ _⟩, e',?_⟩
      change (e.trans (Equiv.swap (e j) a)) j :: c.map e' = a :: l
      rw [hmap,he]
      simp

private def recode (e : Equiv.Perm ℕ) (g : Family) := g.map (Multiset.map e)

private theorem recode_rev (e : Equiv.Perm ℕ) (g : Family) : recode e.symm (recode e g) = g := by
  induction g using Multiset.induction_on with
  | empty => simp [recode]
  | cons b g ih =>
    simp [recode] at ih ⊢

private theorem recode_sum (e : Equiv.Perm ℕ) (g : Family) :
    (recode e g).sum = g.sum.map e := by
  induction g using Multiset.induction_on with
  | empty => simp [recode]
  | cons b g ih => simpa [recode] using congrArg ((b.map e)+·) ih

private theorem recode_valid (e : Equiv.Perm ℕ) {l m : List ℕ}
    (he : ((l : Block).map e) = (m : Block)) {g : Family} (hg : g ∈ valid l) :
    recode e g ∈ valid m := by
  obtain ⟨⟨hp,hs⟩,hm⟩ := (valid_spec _ _).1 hg
  refine (valid_spec _ _).2 ⟨⟨?_,by rw [recode_sum,hs,he]⟩,
    (mode_map g (Multiset.map e) (Multiset.map_injective e.injective).injOn).2 hm⟩
  rintro _ hh h0
  obtain ⟨b,hb,rfl⟩ := mem_map.mp hh
  exact hp b hb (by simpa using congrArg Multiset.card h0)

private theorem recode_card (e : Equiv.Perm ℕ) {l m : List ℕ}
    (he : ((l : Block).map e) = (m : Block)) : (valid l).card = (valid m).card := by
  have leq (e : Equiv.Perm ℕ) {l m : List ℕ} (h : (l : Block).map e = (m : Block)) :
      (valid l).card ≤ (valid m).card :=
    Finset.card_le_card_of_injOn (recode e) (fun _ hg => recode_valid e h hg)
      (fun g _ k _ he => by simpa [recode_rev] using congrArg (recode e.symm) he)
  refine le_antisymm (leq e he) (leq e.symm ?_)
  rw [←he,map_map]
  simp

private theorem strong_fresh {g : Family} (h : Strong g) {b : Block} (hb : b ∉ g) :
    Mode (b ::ₘ g) := by
  obtain ⟨m,hm,h2,hu⟩ := h
  have hm' : m∈g := mem_toFinset.mp hm
  have hmb : m≠b := fun he => hb (he ▸ hm')
  refine ⟨m,mem_cons_of_mem hm',?_⟩
  intro x hx hxne
  rw [count_cons_of_ne hmb]
  rcases mem_cons.mp hx with rfl|hx
  · have h0 : g.count x=0 := count_eq_zero.mpr hb
    simp [h0]; omega
  · have hxb : x≠b := fun he => hb (he ▸ hx)
    rw [count_cons_of_ne hxb]
    exact hu _ (mem_toFinset.mpr hx) hxne

private theorem lift_count (l m : List ℕ) (z : Block)
    (hsum : (l : Block)+z = (m : Block)) : (sturdy l).card ≤ (valid m).card := by
  classical
  by_cases hzero : z=0
  · subst z
    have he : (l : Block) = (m : Block) := by simpa using hsum
    exact Finset.card_le_card (fun g hg =>
      (valid_spec _ _).2 (by simpa [he] using (valid_spec l g).1 (Finset.mem_filter.mp hg).1))
  let T := {g // g ∈ sturdy l}
  have pick (t : T) : ∃ b ∈ t.val, (∀ x ∈ t.val, x.card ≤ b.card) ∧
      (t.val.erase b=0 ∨ Strong (t.val.erase b)) := by
    simpa [Sturdy] using (Finset.mem_filter.mp t.property).2
  choose b hmem hmax hsafe using pick
  let tail := fun t : T => t.val.erase (b t)
  let head := fun t : T => b t + z
  let extendG := fun t : T => head t ::ₘ tail t
  have H (t : T) : b t ::ₘ tail t = t.val := cons_erase (hmem t)
  have biggest (t : T) (d : Block) (hd : d∈tail t) : d.card < (head t).card := by
    have h := hmax t d (mem_of_mem_erase hd)
    have hz := card_pos.mpr hzero
    dsimp [head]; rw [card_add]; omega
  have fresh (t : T) : head t ∉ tail t := fun hh => (Nat.lt_irrefl _) (biggest t _ hh)
  have good (t : T) : extendG t ∈ valid m := by
    obtain ⟨⟨hp,hs⟩,_⟩ := (valid_spec _ _).1 (Finset.mem_filter.mp t.property).1
    refine (valid_spec _ _).2 ⟨⟨?_,?_⟩,?_⟩
    · intro c hc
      rcases mem_cons.mp hc with rfl|hc
      · exact fun hh => hzero ((add_eq_zero.mp hh).2)
      · exact hp c (mem_of_mem_erase hc)
    · dsimp only [extendG, head]
      rw [sum_cons]
      rw [add_right_comm,←sum_cons,H,hs,hsum]
    · rcases hsafe t with he|he
      · have ht : tail t=0 := he
        simp [extendG,ht,Mode]
      · exact strong_fresh he (fresh t)
  have hinj : Function.Injective extendG := by
    intro t u he
    have headEq : head t=head u := by
      by_contra hd
      have h1 : head t ∈ extendG u := he ▸ mem_cons_self _ _
      have h2 : head u ∈ extendG t := he.symm ▸ mem_cons_self _ _
      have h3 := biggest u _ ((mem_cons.mp h1).resolve_left hd)
      have h4 := biggest t _ ((mem_cons.mp h2).resolve_left (Ne.symm hd))
      omega
    have hb : b t=b u := add_right_cancel headEq
    have ht : tail t=tail u := by simpa [extendG,headEq] using he
    exact Subtype.ext (by rw [←H t,←H u,hb,ht])
  simpa using Finset.card_le_card_of_injOn (s:=(sturdy l).attach) (t:=valid m)
    extendG (fun t _ => good t) hinj.injOn

private theorem nodup_low {l : List ℕ} (hl : l.Nodup) : (valid l).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  have singleton (g : Family) (hg : g ∈ valid l) : g = {(l : Block)} := by
    obtain ⟨⟨hp,hs⟩,m,hm,hmode⟩ := (valid_spec _ _).1 hg
    have hmne := hp m hm
    obtain ⟨p,hp'⟩ := exists_mem_of_ne_zero hmne
    obtain ⟨r,rfl⟩ := exists_cons_of_mem hm
    have H : m ∉ r := by
      intro hh
      obtain ⟨t,rfl⟩ := exists_cons_of_mem hh
      have hN : (m+(m+t.sum)).Nodup := by simpa [←hs] using (show (l : Block).Nodup from hl)
      have hc := nodup_iff_count_le_one.mp hN p
      have hpos := count_pos.mpr hp'
      simp only [count_add] at hc; omega
    have hr : r=0 := by
      by_contra! hh
      obtain ⟨b,hb⟩ := exists_mem_of_ne_zero hh
      have hne : b≠m := fun h => H (h ▸ hb)
      have h := hmode b (mem_cons_of_mem hb) hne
      rw [count_cons_self,count_eq_zero.mpr H,count_cons_of_ne hne] at h
      have := count_pos.mpr hb
      omega
    subst r
    simpa using congrArg (fun b : Block => ({b} : Family)) hs
  intro g hg k hk
  rw [singleton g hg,singleton k hk]

private theorem has_repeat {w : Block} (h : ¬w.Nodup) :
    ∃ p : ℕ, ∃ r : Block, w = p ::ₘ p ::ₘ r := by
  rw [nodup_iff_count_le_one] at h
  push Not at h
  obtain ⟨p,hp⟩ := h
  have hm : p ∈ w := count_pos.mp (by omega)
  obtain ⟨r,rfl⟩ := exists_cons_of_mem hm
  rw [count_cons_self] at hp
  obtain ⟨s,rfl⟩ := exists_cons_of_mem (count_pos.mp (by omega : 0<r.count p))
  exact ⟨p,s,rfl⟩

private theorem seven_core {w : Block} (hlen : 7 ≤ w.card) (hr : ¬w.Nodup) :
    ∃ u z : Block, u+z=w ∧ u.card=7 ∧ ¬u.Nodup := by
  obtain ⟨p,r,rfl⟩ := has_repeat hr
  let s := r.sort (· ≤ ·)
  let a : Block := s.take 5
  let z : Block := s.drop 5
  have hsum : a+z=r := by
    change (↑(s.take 5) : Block) + ↑(s.drop 5) = r
    rw [coe_add,List.take_append_drop,Multiset.sort_eq]
  have hlen' : 5 ≤ s.length := by
    have hs : s.length=r.card := Multiset.length_sort (s:=r) (r:=(· ≤ ·))
    simp at hlen
    omega
  refine ⟨p ::ₘ p ::ₘ a,z,by simp [cons_add,hsum],?_,by simp⟩
  simp [a,List.length_take,Nat.min_eq_left hlen']

private def packet (l : List ℕ) (key : ℕ) : Family :=
  let groups := (List.range l.length).map fun i =>
    (((l.zipIdx.filter fun t => key / 8^t.2 % 8 == i).map Prod.fst) : Block)
  (groups.filter (· ≠ 0) : List Block)

private def Certified (t : Bool) (l : List ℕ) (keys : List ℕ) : Prop :=
  let w := keys.map (packet l)
  10 ≤ w.length ∧ w.Nodup ∧ ∀ g ∈ w, (∀ b ∈ g.toFinset, b≠0) ∧
    g.sum = (l : Block) ∧ Mode g ∧ (t = true → Sturdy g)
private instance (t : Bool) (l keys : List ℕ) : Decidable (Certified t l keys) := by
  unfold Certified; infer_instance

private theorem cert_bound {t : Bool} {l keys : List ℕ} (h : Certified t l keys) :
    10 ≤ (if t then sturdy l else valid l).card := by
  obtain ⟨hlen,hn,hs⟩ := h
  have hd := List.toFinset_card_of_nodup hn
  have sub : (keys.map (packet l)).toFinset ⊆ (if t then sturdy l else valid l) := by
    intro g hg
    obtain ⟨hp,he,hm,ht⟩ := hs g (List.mem_toFinset.mp hg)
    have hv := (valid_spec l g).2 ⟨⟨by simpa [Proper] using hp,he⟩,hm⟩
    cases t with
    | false => exact hv
    | true => exact Finset.mem_filter.mpr ⟨hv,ht rfl⟩
  exact (by simpa [hd] using hlen : 10 ≤ (keys.map (packet l)).toFinset.card).trans
    (Finset.card_le_card sub)


private theorem entry6_0 : Certified false [5,5,4,3,2,1] [5356,675,4259,5155,4771,90,4634,5219,4186,538] := by decide

private theorem entry6_1 : Certified false [6,4,4,3,2,1] [5405,724,4308,5400,4820,139,4816,5401,4305,720] := by decide

private theorem entry6_2 : Certified false [4,4,4,3,2,1] [5475,794,4378,5400,4890,209,4816,5401,4305,720] := by decide

private theorem entry6_3 : Certified false [6,5,3,3,2,1] [5797,1116,5764,5792,5772,1091,5768,5793,5761,1112] := by decide

private theorem entry6_4 : Certified false [5,5,3,3,2,1] [5155,5792,5219,538,4634,5793,1112,5768,5283,602] := by decide

private theorem entry6_5 : Certified false [6,3,3,3,2,1] [6357,1676,5764,6352,5772,1091,5768,6353,5761,1672] := by decide

private theorem entry6_6 : Certified false [3,3,3,3,2,1] [6938,2257,6352,6353,1672,5768,6426,1745,5760,5769] := by decide

private theorem entry6_7 : Certified false [6,5,4,2,2,1] [8933,8732,8900,8928,8924,8707,8920,8931,8899,8728] := by decide

private theorem entry6_8 : Certified false [5,5,4,2,2,1] [4259,8928,4771,90,4634,8867,4186,4122,4698,17] := by decide

private theorem entry6_9 : Certified false [6,4,4,2,2,1] [4308,8900,4820,139,4816,8986,4305,4304,8843,8840] := by decide

private theorem entry6_10 : Certified false [4,4,4,2,2,1] [9059,4378,4890,209,4816,8986,4305,4304,4817,136] := by decide

private theorem entry6_11 : Certified false [6,5,2,2,2,1] [13413,8732,13380,13408,13404,8707,13400,13411,13379,8728] := by decide

private theorem entry6_12 : Certified false [5,5,2,2,2,1] [13420,13408,9315,4122,4634,13411,8728,13400,4698,17] := by decide

private theorem entry6_13 : Certified false [6,2,2,2,2,1] [18061,13380,18056,13964,8707,13960,18060,13379,13376,9291] := by decide

private theorem entry6_14 : Certified false [2,2,2,2,2,1] [22737,18056,18641,13376,13960,14033,8704,13969,9288,0] := by decide

private theorem entry6_15 : Certified false [6,5,4,3,1,1] [34021,33948,34004,34018,34012,33939,34010,34019,34003,33946] := by decide

private theorem entry6_16 : Certified false [5,5,4,3,1,1] [675,33443,33891,90,32858,538,33992,602,33370,17] := by decide

private theorem entry6_17 : Certified false [6,4,4,3,1,1] [724,33492,34073,139,32977,33859,720,34004,721,33489] := by decide

private theorem entry6_18 : Certified false [4,4,4,3,1,1] [34147,794,33562,34073,209,32977,720,33992,721,33489] := by decide

private theorem entry6_19 : Certified false [6,5,3,3,1,1] [1116,34444,34465,33299,1091,34433,1112,33948,34460,34467] := by decide

private theorem entry6_20 : Certified false [5,5,3,3,1,1] [33891,34465,538,1112,602,33370,17,33928,34467,33946] := by decide

private theorem entry6_21 : Certified false [6,3,3,3,1,1] [35029,1676,34444,35025,1091,33859,34433,1672,34516,1675] := by decide

private theorem entry6_22 : Certified false [3,3,3,3,1,1] [35610,2257,35025,1672,1745,34441,1088,33928,34522,1161] := by decide

private theorem entry6_23 : Certified false [6,5,4,1,1,1] [69861,69788,69844,69858,69852,69779,69850,69859,69843,69786] := by decide

private theorem entry6_24 : Certified false [5,5,4,1,1,1] [69868,37027,69858,90,32858,36954,69841,17,69649,69859] := by decide

private theorem entry6_25 : Certified false [6,4,4,1,1,1] [69917,37076,69844,139,32977,69771,37073,69698,136,69852] := by decide

private theorem entry6_26 : Certified false [4,4,4,1,1,1] [37146,209,32977,37073,69841,136,69768,69923,69842,69850] := by decide

private theorem entry6_27 : Certified false [6,5,1,1,1,1] [107045,74268,107036,107043,36883,74259,107027,74266,107044,74267] := by decide

private theorem entry6_28 : Certified false [5,5,1,1,1,1] [107052,107043,37402,74266,17,69649,36872,107044,74267,107035] := by decide

private theorem entry6_29 : Certified false [6,1,1,1,1,1] [144453,111684,144452,74819,74307,107587,111683,70146,74818,0] := by decide

private def table6 : List (List ℕ × List ℕ) := [
  ([5,5,4,3,2,1],[5356,675,4259,5155,4771,90,4634,5219,4186,538]),
  ([6,4,4,3,2,1],[5405,724,4308,5400,4820,139,4816,5401,4305,720]),
  ([4,4,4,3,2,1],[5475,794,4378,5400,4890,209,4816,5401,4305,720]),
  ([6,5,3,3,2,1],[5797,1116,5764,5792,5772,1091,5768,5793,5761,1112]),
  ([5,5,3,3,2,1],[5155,5792,5219,538,4634,5793,1112,5768,5283,602]),
  ([6,3,3,3,2,1],[6357,1676,5764,6352,5772,1091,5768,6353,5761,1672]),
  ([3,3,3,3,2,1],[6938,2257,6352,6353,1672,5768,6426,1745,5760,5769]),
  ([6,5,4,2,2,1],[8933,8732,8900,8928,8924,8707,8920,8931,8899,8728]),
  ([5,5,4,2,2,1],[4259,8928,4771,90,4634,8867,4186,4122,4698,17]),
  ([6,4,4,2,2,1],[4308,8900,4820,139,4816,8986,4305,4304,8843,8840]),
  ([4,4,4,2,2,1],[9059,4378,4890,209,4816,8986,4305,4304,4817,136]),
  ([6,5,2,2,2,1],[13413,8732,13380,13408,13404,8707,13400,13411,13379,8728]),
  ([5,5,2,2,2,1],[13420,13408,9315,4122,4634,13411,8728,13400,4698,17]),
  ([6,2,2,2,2,1],[18061,13380,18056,13964,8707,13960,18060,13379,13376,9291]),
  ([2,2,2,2,2,1],[22737,18056,18641,13376,13960,14033,8704,13969,9288,0]),
  ([6,5,4,3,1,1],[34021,33948,34004,34018,34012,33939,34010,34019,34003,33946]),
  ([5,5,4,3,1,1],[675,33443,33891,90,32858,538,33992,602,33370,17]),
  ([6,4,4,3,1,1],[724,33492,34073,139,32977,33859,720,34004,721,33489]),
  ([4,4,4,3,1,1],[34147,794,33562,34073,209,32977,720,33992,721,33489]),
  ([6,5,3,3,1,1],[1116,34444,34465,33299,1091,34433,1112,33948,34460,34467]),
  ([5,5,3,3,1,1],[33891,34465,538,1112,602,33370,17,33928,34467,33946]),
  ([6,3,3,3,1,1],[35029,1676,34444,35025,1091,33859,34433,1672,34516,1675]),
  ([3,3,3,3,1,1],[35610,2257,35025,1672,1745,34441,1088,33928,34522,1161]),
  ([6,5,4,1,1,1],[69861,69788,69844,69858,69852,69779,69850,69859,69843,69786]),
  ([5,5,4,1,1,1],[69868,37027,69858,90,32858,36954,69841,17,69649,69859]),
  ([6,4,4,1,1,1],[69917,37076,69844,139,32977,69771,37073,69698,136,69852]),
  ([4,4,4,1,1,1],[37146,209,32977,37073,69841,136,69768,69923,69842,69850]),
  ([6,5,1,1,1,1],[107045,74268,107036,107043,36883,74259,107027,74266,107044,74267]),
  ([5,5,1,1,1,1],[107052,107043,37402,74266,17,69649,36872,107044,74267,107035]),
  ([6,1,1,1,1,1],[144453,111684,144452,74819,74307,107587,111683,70146,74818,0])]


private theorem audited6 : ∀ r ∈ table6, Certified false r.1 r.2 := by

  simp only [table6, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]

  exact ⟨entry6_0, entry6_1, entry6_2, entry6_3, entry6_4, entry6_5, entry6_6, entry6_7, entry6_8, entry6_9, entry6_10, entry6_11, entry6_12, entry6_13, entry6_14, entry6_15, entry6_16, entry6_17, entry6_18, entry6_19, entry6_20, entry6_21, entry6_22, entry6_23, entry6_24, entry6_25, entry6_26, entry6_27, entry6_28, entry6_29⟩

private theorem entry7_0 : Certified true [6,6,5,4,3,2,1] [42805,5356,34028,41196,42540,38124,675,37027,37923,41708] := by decide

private theorem entry7_1 : Certified true [7,5,5,4,3,2,1] [42854,5405,34077,41245,42848,38173,724,37076,38168,41757] := by decide

private theorem entry7_2 : Certified true [5,5,5,4,3,2,1] [42924,5475,34147,41315,42848,38243,794,37146,38168,41827] := by decide

private theorem entry7_3 : Certified true [7,6,4,4,3,2,1] [43246,5797,34469,43205,43240,38565,1116,38532,38560,43213] := by decide

private theorem entry7_4 : Certified true [6,6,4,4,3,2,1] [42540,43240,37923,38560,42604,33891,5155,41507,43241,34465] := by decide

private theorem entry7_5 : Certified true [7,4,4,4,3,2,1] [43806,6357,35029,43205,43800,39125,1676,38532,39120,43213] := by decide

private theorem entry7_6 : Certified true [4,4,4,4,3,2,1] [44387,6938,35610,43800,39706,2257,39120,43801,35025,6352] := by decide

private theorem entry7_7 : Certified true [7,6,5,3,3,2,1] [46382,8933,46117,46341,46376,46181,8732,46148,46176,46349] := by decide

private theorem entry7_8 : Certified true [6,6,5,3,3,2,1] [41196,46376,41708,4259,37027,41507,41059,46176,46377,46113] := by decide

private theorem entry7_9 : Certified true [7,5,5,3,3,2,1] [41245,46341,41757,4308,37076,41752,46349,8900,46148,46344] := by decide

private theorem entry7_10 : Certified true [5,5,5,3,3,2,1] [46508,9059,41315,41827,4378,37146,41752,41241,46344,42339] := by decide

private theorem entry7_11 : Certified true [7,6,3,3,3,2,1] [50862,13413,46117,50821,50856,46181,8732,46148,46176,50829] := by decide

private theorem entry7_12 : Certified true [6,6,3,3,3,2,1] [50869,13420,50856,41507,46176,50857,46113,13408,50824,46764] := by decide

private theorem entry7_13 : Certified true [7,3,3,3,3,2,1] [55510,18061,50821,55504,50829,13380,46148,50824,55505,50817] := by decide

private theorem entry7_14 : Certified true [3,3,3,3,3,2,1] [60186,22737,55504,55505,18056,50824,56090,18641,50816,51408] := by decide

private theorem entry7_15 : Certified true [7,6,5,4,2,2,1] [71470,69861,71205,71429,71464,71397,69660,71364,71392,71453] := by decide

private theorem entry7_16 : Certified true [6,6,5,4,2,2,1] [34028,71464,38124,675,37027,37923,70892,33443,32931,70691] := by decide

private theorem entry7_17 : Certified true [7,5,5,4,2,2,1] [34077,71429,38173,724,37076,38168,70941,33492,32980,70936] := by decide

private theorem entry7_18 : Certified true [5,5,5,4,2,2,1] [71596,34147,69987,38243,794,37146,38168,71011,33562,33050] := by decide

private theorem entry7_19 : Certified true [7,6,4,4,2,2,1] [34469,71205,38565,1116,38532,38560,71893,34444,34436,71888] := by decide

private theorem entry7_20 : Certified true [6,6,4,4,2,2,1] [37923,38560,71340,33891,33827,70691,71914,34465,34464,71888] := by decide

private theorem entry7_21 : Certified true [7,4,4,4,2,2,1] [72478,35029,72472,39125,1676,38532,39120,71893,34444,34436] := by decide

private theorem entry7_22 : Certified true [4,4,4,4,2,2,1] [73059,35610,72472,39706,2257,39120,72474,35025,35024,71888] := by decide

private theorem entry7_23 : Certified true [7,6,5,2,2,2,1] [107310,69861,107045,107269,107304,107237,69660,107204,107232,107293] := by decide

private theorem entry7_24 : Certified true [6,6,5,2,2,2,1] [107317,107052,107304,74476,32931,37027,74275,69795,107232,107307] := by decide

private theorem entry7_25 : Certified true [7,5,5,2,2,2,1] [107366,107269,107360,74525,32980,37076,74520,107293,69828,107204] := by decide

private theorem entry7_26 : Certified true [5,5,5,2,2,2,1] [69987,107360,74595,33050,37146,74520,69914,107288,37658,209] := by decide

private theorem entry7_27 : Certified true [7,6,2,2,2,2,1] [144494,107045,144453,144488,111717,69660,111684,111712,144485,107036] := by decide

private theorem entry7_28 : Certified true [6,6,2,2,2,2,1] [144501,107052,144488,74275,111712,144492,107043,107040,144480,74851] := by decide

private theorem entry7_29 : Certified true [7,2,2,2,2,2,1] [181902,144453,181896,149133,107012,111684,149128,181901,144452,144448] := by decide

private theorem entry7_30 : Certified true [2,2,2,2,2,2,1] [219345,181896,186577,144448,149128,149713,107008,112264,111680,111752] := by decide

private theorem entry7_31 : Certified true [7,6,5,4,3,1,1] [272174,271589,272037,272149,272170,272101,271516,272084,272098,272157] := by decide

private theorem entry7_32 : Certified true [6,6,5,4,3,1,1] [5356,267500,271084,271980,675,262819,263267,4259,270435,5155] := by decide

private theorem entry7_33 : Certified true [7,5,5,4,3,1,1] [5405,267549,271133,272225,724,262868,263449,4308,270617,5400] := by decide

private theorem entry7_34 : Certified true [5,5,5,4,3,1,1] [272300,5475,267619,271203,272225,794,262938,263449,4378,270617] := by decide

private theorem entry7_35 : Certified true [7,6,4,4,3,1,1] [5797,267941,272589,272617,1116,263820,263841,5764,272577,5792] := by decide

private theorem entry7_36 : Certified true [6,6,4,4,3,1,1] [271980,272617,263267,263841,5155,5792,5219,267363,271459,538] := by decide

private theorem entry7_37 : Certified true [7,4,4,4,3,1,1] [273182,6357,268501,272589,273177,1676,263820,264401,5764,272577] := by decide

private theorem entry7_38 : Certified true [4,4,4,4,3,1,1] [273763,6938,269082,273177,2257,264401,6352,273178,6353,268497] := by decide

private theorem entry7_39 : Certified true [7,6,5,3,3,1,1] [8933,275557,275725,275753,8732,275468,275489,8900,275713,8928] := by decide

private theorem entry7_40 : Certified true [6,6,5,3,3,1,1] [271084,275753,4259,270435,275489,8928,4771,266915,271459,90] := by decide

private theorem entry7_41 : Certified true [7,5,5,3,3,1,1] [271133,275725,4308,270617,8900,275713,4820,266964,271641,139] := by decide

private theorem entry7_42 : Certified true [5,5,5,3,3,1,1] [275884,9059,271203,4378,266522,270617,271715,4890,267034,271641] := by decide

private theorem entry7_43 : Certified true [7,6,3,3,3,1,1] [280238,13413,275557,280205,280233,8732,275468,275489,13380,280193] := by decide

private theorem entry7_44 : Certified true [6,6,3,3,3,1,1] [280245,13420,280233,275489,13408,280200,9315,270947,271459,4122] := by decide

private theorem entry7_45 : Certified true [7,3,3,3,3,1,1] [284886,18061,280205,284881,13380,280193,18056,13964,275532,280785] := by decide

private theorem entry7_46 : Certified true [3,3,3,3,3,1,1] [289562,22737,284881,18056,280200,285466,18641,280201,280785,13376] := by decide

private theorem entry7_47 : Certified true [7,6,5,4,1,1,1] [558894,558309,558757,558869,558890,558821,558236,558804,558818,558877] := by decide

private theorem entry7_48 : Certified true [6,6,5,4,1,1,1] [558901,296172,558890,675,262819,263267,295587,557731,296035,90] := by decide

private theorem entry7_49 : Certified true [7,5,5,4,1,1,1] [558950,296221,558869,724,262868,263449,295636,557850,296217,139] := by decide

private theorem entry7_50 : Certified true [5,5,5,4,1,1,1] [296291,558435,794,262938,263449,295706,557850,296217,209,262353] := by decide

private theorem entry7_51 : Certified true [7,6,4,4,1,1,1] [559342,296613,558757,1116,263820,263841,296588,559306,296609,557587] := by decide

private theorem entry7_52 : Certified true [6,6,4,4,1,1,1] [559349,263267,263841,296035,296609,538,262682,557594,558609,1112] := by decide

private theorem entry7_53 : Certified true [7,4,4,4,1,1,1] [297173,559898,1676,263820,264401,296588,559306,297169,1091,263809] := by decide

private theorem entry7_54 : Certified true [4,4,4,4,1,1,1] [560483,297754,559898,2257,264401,297169,1672,263816,558728,559971] := by decide

private theorem entry7_55 : Certified true [7,6,5,1,1,1,1] [856366,594149,856293,856349,856363,594076,856220,856227,594132,856339] := by decide

private theorem entry7_56 : Certified true [6,6,5,1,1,1,1] [856373,856300,856363,299171,561315,856227,594146,90,262234,295002] := by decide

private theorem entry7_57 : Certified true [7,5,5,1,1,1,1] [856422,856349,856419,299220,561434,594132,856339,139,262353,557195] := by decide

private theorem entry7_58 : Certified true [5,5,5,1,1,1,1] [856492,594275,856419,299290,295194,561434,209,262353,295121,557265] := by decide

private theorem entry7_59 : Certified true [7,6,1,1,1,1,1] [1155630,893477,1155621,1155628,598556,860700,860707,893468,1155612,893475] := by decide

private theorem entry7_60 : Certified true [6,6,1,1,1,1,1] [1155637,893484,1155628,860707,893475,1155619,299546,299034,561178,856602] := by decide

private theorem entry7_61 : Certified true [7,1,1,1,1,1,1] [1455174,1193029,1455173,898116,1160260,1193028,599107,861251,594435,860739] := by decide

private theorem entry7_62 : Certified true [1,1,1,1,1,1,1] [1754760,1492616,1197704,1193608,898696,898184,894024,599176,598592,0] := by decide

private def table7 : List (List ℕ × List ℕ) := [
  ([6,6,5,4,3,2,1],[42805,5356,34028,41196,42540,38124,675,37027,37923,41708]),
  ([7,5,5,4,3,2,1],[42854,5405,34077,41245,42848,38173,724,37076,38168,41757]),
  ([5,5,5,4,3,2,1],[42924,5475,34147,41315,42848,38243,794,37146,38168,41827]),
  ([7,6,4,4,3,2,1],[43246,5797,34469,43205,43240,38565,1116,38532,38560,43213]),
  ([6,6,4,4,3,2,1],[42540,43240,37923,38560,42604,33891,5155,41507,43241,34465]),
  ([7,4,4,4,3,2,1],[43806,6357,35029,43205,43800,39125,1676,38532,39120,43213]),
  ([4,4,4,4,3,2,1],[44387,6938,35610,43800,39706,2257,39120,43801,35025,6352]),
  ([7,6,5,3,3,2,1],[46382,8933,46117,46341,46376,46181,8732,46148,46176,46349]),
  ([6,6,5,3,3,2,1],[41196,46376,41708,4259,37027,41507,41059,46176,46377,46113]),
  ([7,5,5,3,3,2,1],[41245,46341,41757,4308,37076,41752,46349,8900,46148,46344]),
  ([5,5,5,3,3,2,1],[46508,9059,41315,41827,4378,37146,41752,41241,46344,42339]),
  ([7,6,3,3,3,2,1],[50862,13413,46117,50821,50856,46181,8732,46148,46176,50829]),
  ([6,6,3,3,3,2,1],[50869,13420,50856,41507,46176,50857,46113,13408,50824,46764]),
  ([7,3,3,3,3,2,1],[55510,18061,50821,55504,50829,13380,46148,50824,55505,50817]),
  ([3,3,3,3,3,2,1],[60186,22737,55504,55505,18056,50824,56090,18641,50816,51408]),
  ([7,6,5,4,2,2,1],[71470,69861,71205,71429,71464,71397,69660,71364,71392,71453]),
  ([6,6,5,4,2,2,1],[34028,71464,38124,675,37027,37923,70892,33443,32931,70691]),
  ([7,5,5,4,2,2,1],[34077,71429,38173,724,37076,38168,70941,33492,32980,70936]),
  ([5,5,5,4,2,2,1],[71596,34147,69987,38243,794,37146,38168,71011,33562,33050]),
  ([7,6,4,4,2,2,1],[34469,71205,38565,1116,38532,38560,71893,34444,34436,71888]),
  ([6,6,4,4,2,2,1],[37923,38560,71340,33891,33827,70691,71914,34465,34464,71888]),
  ([7,4,4,4,2,2,1],[72478,35029,72472,39125,1676,38532,39120,71893,34444,34436]),
  ([4,4,4,4,2,2,1],[73059,35610,72472,39706,2257,39120,72474,35025,35024,71888]),
  ([7,6,5,2,2,2,1],[107310,69861,107045,107269,107304,107237,69660,107204,107232,107293]),
  ([6,6,5,2,2,2,1],[107317,107052,107304,74476,32931,37027,74275,69795,107232,107307]),
  ([7,5,5,2,2,2,1],[107366,107269,107360,74525,32980,37076,74520,107293,69828,107204]),
  ([5,5,5,2,2,2,1],[69987,107360,74595,33050,37146,74520,69914,107288,37658,209]),
  ([7,6,2,2,2,2,1],[144494,107045,144453,144488,111717,69660,111684,111712,144485,107036]),
  ([6,6,2,2,2,2,1],[144501,107052,144488,74275,111712,144492,107043,107040,144480,74851]),
  ([7,2,2,2,2,2,1],[181902,144453,181896,149133,107012,111684,149128,181901,144452,144448]),
  ([2,2,2,2,2,2,1],[219345,181896,186577,144448,149128,149713,107008,112264,111680,111752]),
  ([7,6,5,4,3,1,1],[272174,271589,272037,272149,272170,272101,271516,272084,272098,272157]),
  ([6,6,5,4,3,1,1],[5356,267500,271084,271980,675,262819,263267,4259,270435,5155]),
  ([7,5,5,4,3,1,1],[5405,267549,271133,272225,724,262868,263449,4308,270617,5400]),
  ([5,5,5,4,3,1,1],[272300,5475,267619,271203,272225,794,262938,263449,4378,270617]),
  ([7,6,4,4,3,1,1],[5797,267941,272589,272617,1116,263820,263841,5764,272577,5792]),
  ([6,6,4,4,3,1,1],[271980,272617,263267,263841,5155,5792,5219,267363,271459,538]),
  ([7,4,4,4,3,1,1],[273182,6357,268501,272589,273177,1676,263820,264401,5764,272577]),
  ([4,4,4,4,3,1,1],[273763,6938,269082,273177,2257,264401,6352,273178,6353,268497]),
  ([7,6,5,3,3,1,1],[8933,275557,275725,275753,8732,275468,275489,8900,275713,8928]),
  ([6,6,5,3,3,1,1],[271084,275753,4259,270435,275489,8928,4771,266915,271459,90]),
  ([7,5,5,3,3,1,1],[271133,275725,4308,270617,8900,275713,4820,266964,271641,139]),
  ([5,5,5,3,3,1,1],[275884,9059,271203,4378,266522,270617,271715,4890,267034,271641]),
  ([7,6,3,3,3,1,1],[280238,13413,275557,280205,280233,8732,275468,275489,13380,280193]),
  ([6,6,3,3,3,1,1],[280245,13420,280233,275489,13408,280200,9315,270947,271459,4122]),
  ([7,3,3,3,3,1,1],[284886,18061,280205,284881,13380,280193,18056,13964,275532,280785]),
  ([3,3,3,3,3,1,1],[289562,22737,284881,18056,280200,285466,18641,280201,280785,13376]),
  ([7,6,5,4,1,1,1],[558894,558309,558757,558869,558890,558821,558236,558804,558818,558877]),
  ([6,6,5,4,1,1,1],[558901,296172,558890,675,262819,263267,295587,557731,296035,90]),
  ([7,5,5,4,1,1,1],[558950,296221,558869,724,262868,263449,295636,557850,296217,139]),
  ([5,5,5,4,1,1,1],[296291,558435,794,262938,263449,295706,557850,296217,209,262353]),
  ([7,6,4,4,1,1,1],[559342,296613,558757,1116,263820,263841,296588,559306,296609,557587]),
  ([6,6,4,4,1,1,1],[559349,263267,263841,296035,296609,538,262682,557594,558609,1112]),
  ([7,4,4,4,1,1,1],[297173,559898,1676,263820,264401,296588,559306,297169,1091,263809]),
  ([4,4,4,4,1,1,1],[560483,297754,559898,2257,264401,297169,1672,263816,558728,559971]),
  ([7,6,5,1,1,1,1],[856366,594149,856293,856349,856363,594076,856220,856227,594132,856339]),
  ([6,6,5,1,1,1,1],[856373,856300,856363,299171,561315,856227,594146,90,262234,295002]),
  ([7,5,5,1,1,1,1],[856422,856349,856419,299220,561434,594132,856339,139,262353,557195]),
  ([5,5,5,1,1,1,1],[856492,594275,856419,299290,295194,561434,209,262353,295121,557265]),
  ([7,6,1,1,1,1,1],[1155630,893477,1155621,1155628,598556,860700,860707,893468,1155612,893475]),
  ([6,6,1,1,1,1,1],[1155637,893484,1155628,860707,893475,1155619,299546,299034,561178,856602]),
  ([7,1,1,1,1,1,1],[1455174,1193029,1455173,898116,1160260,1193028,599107,861251,594435,860739]),
  ([1,1,1,1,1,1,1],[1754760,1492616,1197704,1193608,898696,898184,894024,599176,598592,0])]


private theorem audited7 : ∀ r ∈ table7, Certified true r.1 r.2 := by

  simp only [table7, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]

  exact ⟨entry7_0, entry7_1, entry7_2, entry7_3, entry7_4, entry7_5, entry7_6, entry7_7, entry7_8, entry7_9, entry7_10, entry7_11, entry7_12, entry7_13, entry7_14, entry7_15, entry7_16, entry7_17, entry7_18, entry7_19, entry7_20, entry7_21, entry7_22, entry7_23, entry7_24, entry7_25, entry7_26, entry7_27, entry7_28, entry7_29, entry7_30, entry7_31, entry7_32, entry7_33, entry7_34, entry7_35, entry7_36, entry7_37, entry7_38, entry7_39, entry7_40, entry7_41, entry7_42, entry7_43, entry7_44, entry7_45, entry7_46, entry7_47, entry7_48, entry7_49, entry7_50, entry7_51, entry7_52, entry7_53, entry7_54, entry7_55, entry7_56, entry7_57, entry7_58, entry7_59, entry7_60, entry7_61, entry7_62⟩


set_option maxRecDepth 16000 in
set_option maxHeartbeats 2000000 in
private theorem below_seven : ∀ k : Fin 6, ∀ c ∈ codes k, c.Nodup ∨ (valid c).card ≠ 9 := by decide

private theorem lookup6 : ∀ c ∈ codes 6, c.Nodup ∨ c=[1,1,1,1,1,1] ∨
    ∃ row ∈ table6, row.1 = c := by decide

set_option maxRecDepth 12000 in
private theorem lookup7 : ∀ c ∈ codes 7, c.Nodup ∨ ∃ row ∈ table7, row.1 = c := by decide

private theorem small_all (c : List ℕ) (k : Fin 7) (hc : c ∈ codes k) : (valid c).card ≠ 9 := by
  by_cases hk : k.val < 6
  · rcases below_seven ⟨k,hk⟩ c hc with h|h
    · have := nodup_low h; omega
    · exact h
  have he : k.val=6 := by omega
  rcases lookup6 c (he ▸ hc) with h|rfl|⟨r,hr,rfl⟩
  · have := nodup_low h; omega
  · decide
  · have h : 10 ≤ (valid r.1).card := cert_bound (audited6 r hr)
    omega

private theorem sturdy_all (c : List ℕ) (hc : c ∈ codes 7) (hd : ¬c.Nodup) :
    10 ≤ (sturdy c).card := by
  obtain ⟨r,hr,rfl⟩ := (lookup7 _ hc).resolve_left hd
  exact cert_bound (audited7 r hr)


private theorem solve_degree (l : List ℕ) : (valid l).card ≠ 9 := by
  by_cases hnodup : l.Nodup
  · have := nodup_low hnodup; omega
  by_cases hlen : l.length < 7
  · let s := (l : Block).sort (·≤·)
    obtain ⟨c,hc,e,he⟩ := canonical s (Multiset.pairwise_sort _ _)
    have hsl : s.length=l.length := Multiset.length_sort _
    have hr : ((c : Block).map e)=(l : Block) := by
      change (↑(c.map e):Block)=l
      rw [he,Multiset.sort_eq]
    rw [← recode_card e hr]
    exact small_all c ⟨s.length,by omega⟩ hc
  have hsz : 7 ≤ (l : Block).card := by simpa using Nat.le_of_not_gt hlen
  obtain ⟨u,z,huz,hu,hud⟩ := seven_core hsz hnodup
  let s := u.sort (· ≤ ·)
  obtain ⟨c,hc,e,he⟩ := canonical s (Multiset.pairwise_sort _ _)
  have hsl : s.length=7 := (Multiset.length_sort _).trans hu
  have hu' : ((c : Block).map e)=u := by
    change (↑(c.map e):Block)=u
    rw [he,Multiset.sort_eq]
  have hcn : ¬c.Nodup := by
    intro h; apply hud
    rw [←hu']; exact h.map e.injective
  have hb := sturdy_all c (hsl ▸ hc) hcn
  let extra := z.map e.symm
  let v := ((c : Block)+extra).sort (· ≤ ·)
  have hv : (v : Block)=(c : Block)+extra := Multiset.sort_eq _ _
  have htot : (v : Block).map e = (l : Block) := by
    rw [hv, Multiset.map_add,hu',←huz]
    simp [extra,map_map]
  have hh := lift_count c v extra hv.symm
  rw [←recode_card e htot]; omega

end ModalPartitions

theorem OMA.solution : type_of% @OMA.S_oeis_a363265.main := by
  intro n hn
  rw [ModalPartitions.a_card (by omega)]
  exact ModalPartitions.solve_degree _
