import OMAStatements.S_oeis_a060014

/-!
To pass from n to n+m symbols, rotate the new block of m symbols and conjugate
the permutation by that rotation. For a permutation which sends an old symbol
into the new block, fix one such old symbol from the set of possible inputs.
Its image takes each of the m positions exactly once under rotation. These
permutations therefore contribute zero modulo m to any sum depending on order.

A permutation preserving the blocks has order lcm(r,s), where r and s are
the orders of its restrictions. Track the sums of lcm(d,order) modulo m for
all divisors d of m!. Appending a block gives the same transition each time.
A finite window of these sums must repeat, and the recurrence propagates that
repetition to every later index. The choice d=1 recovers the proposed sequence.
-/

namespace PermutationOrderSums

open Equiv Finset

variable {A B : Type}

private def crossing (s : Perm (A ⊕ B)) : Set A := {x | ∃ b, s (.inl x) = .inr b}
private abbrev Mix (A B : Type) := {s : Perm (A ⊕ B) // (crossing s).Nonempty}
private abbrev Split (A B : Type) := {s : Perm (A ⊕ B) // ¬(crossing s).Nonempty}

private def splitMap (p : Perm A × Perm B) : Split A B := by
  refine ⟨Perm.sumCongrHom A B p,?_⟩
  rintro ⟨x,b,h⟩
  change (Sum.inl (p.1 x) : A ⊕ B) = Sum.inr b at h
  cases h

private theorem split_bijective [Fintype A] [Fintype B] : Function.Bijective (@splitMap A B) := by
  constructor
  · intro p q h
    exact Perm.sumCongrHom_injective (congrArg Subtype.val h)
  · rintro ⟨s,hs⟩
    have keep : Set.MapsTo s (Set.range Sum.inl) (Set.range Sum.inl) := by
      rintro _ ⟨x,rfl⟩
      cases h : s (.inl x) with
      | inl a => exact ⟨a,rfl⟩
      | inr b => exact (hs ⟨x,b,h⟩).elim
    obtain ⟨p,hp⟩ := Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl keep
    exact ⟨p,Subtype.ext hp⟩

variable [AddCommGroup B]

private def rotate (b : B) : Perm (A ⊕ B) :=
  Equiv.sumCongr (Equiv.refl A) (Equiv.addLeft b)

private def twist (b : B) (s : Perm (A ⊕ B)) : Perm (A ⊕ B) := (rotate b).permCongr s

private theorem rotate_add (b c : B) : (rotate c : Perm (A ⊕ B)).trans (rotate b) = rotate (b+c) := by
  ext (x | y)
  · rfl
  · change Sum.inr (b+(c+y)) = Sum.inr ((b+c)+y)
    rw [add_assoc]

private theorem twist_add (b c : B) (s : Perm (A ⊕ B)) :
    twist b (twist c s) = twist (b+c) s := by
  unfold twist
  rw [← rotate_add]
  rfl

private theorem twist_zero (s : Perm (A ⊕ B)) : twist 0 s = s := by
  have e : (rotate (0 : B) : Perm (A ⊕ B)) = .refl _ := by
    ext (x | y)
    · rfl
    · change Sum.inr (0+y) = Sum.inr y
      rw [zero_add]
  simp [twist,e,Equiv.permCongr]

private theorem crossing_twist (b : B) (s : Perm (A ⊕ B)) : crossing (twist b s) = crossing s := by
  ext x
  change (∃ d, rotate b (s (.inl x)) = .inr d) ↔ ∃ d, s (.inl x) = .inr d
  cases h : s (.inl x) with
  | inl a => simp [rotate]
  | inr c => simp [rotate]

private def move (b : B) (s : Mix A B) : Mix A B :=
  ⟨twist b s.val, (crossing_twist b s.val).symm ▸ s.property⟩

private noncomputable def anchor (u : {s : Set A // s.Nonempty}) : A := u.property.choose

private noncomputable def first (s : Mix A B) : A := anchor ⟨crossing s.val,s.property⟩

omit [AddCommGroup B] in
private theorem first_mem (s : Mix A B) : first s ∈ crossing s.val := s.property.choose_spec

private noncomputable def mark (s : Mix A B) : B := (first_mem s).choose

omit [AddCommGroup B] in
private theorem mark_spec (s : Mix A B) : s.val (.inl (first s)) = .inr (mark s) :=
  (first_mem s).choose_spec

private theorem first_move (b : B) (s : Mix A B) : first (move b s) = first s :=
  congrArg anchor (Subtype.ext (crossing_twist b s.val))

private theorem mark_move (b : B) (s : Mix A B) : mark (move b s) = b + mark s := by
  have h := mark_spec (move b s)
  rw [first_move] at h
  change rotate b (s.val (.inl (first s))) = Sum.inr _ at h
  rw [mark_spec] at h
  exact (Sum.inr.inj h).symm

private abbrev Normal (A B : Type) [AddCommGroup B] := {s : Mix A B // mark s = 0}

private def spread (u : Normal A B × B) : Mix A B := move u.2 u.1.val

private theorem spread_bijective : Function.Bijective (@spread A B _) := by
  constructor
  · rintro ⟨s,b⟩ ⟨t,c⟩ h
    have e := congrArg mark h
    change mark (move b s.val) = mark (move c t.val) at e
    rw [mark_move,mark_move,s.property,t.property,add_zero,add_zero] at e
    subst c
    have hs : twist b s.val.val = twist b t.val.val := congrArg Subtype.val h
    have st : s = t := Subtype.ext (Subtype.ext ((rotate b).permCongr.injective hs))
    cases st
    rfl
  · intro s
    let b := mark s
    let t := move (-b) s
    have ht : mark t = 0 := by simp [t,mark_move,b]
    refine ⟨(⟨t,ht⟩,b),Subtype.ext ?_⟩
    change twist b (twist (-b) s.val) = s.val
    rw [twist_add,add_neg_cancel,twist_zero]

private noncomputable def weight {α : Type} (m d : ℕ) (s : Perm α) : ZMod m :=
  (Nat.lcm d (orderOf s) : ℕ)

private theorem weight_relabel {α β : Type}
    (e : α ≃ β) (s : Perm α) (m d : ℕ) : weight m d (e.permCongr s) = weight m d s := by
  change (Nat.lcm d (orderOf (e.permCongrHom s)) : ZMod m) = _
  rw [e.permCongrHom.orderOf_eq]
  rfl

omit [AddCommGroup B] in
private theorem weight_split (p : Perm A × Perm B) (m d : ℕ) :
    weight m d (splitMap p).val = weight m (Nat.lcm d (orderOf p.2)) p.1 := by
  change ((Nat.lcm d (orderOf (Perm.sumCongrHom A B p)) : ℕ) : ZMod m) = _
  rw [orderOf_injective _ Perm.sumCongrHom_injective, Prod.orderOf]
  rw [Nat.lcm_comm (orderOf p.1) (orderOf p.2),← Nat.lcm_assoc]
  rfl

private theorem mix_zero (A : Type) [Fintype A] (m d : ℕ) [NeZero m] [Fintype (Mix A (Fin m))] :
    ∑ s : Mix A (Fin m), weight m d s.val = 0 := by
  classical
  let e := Equiv.ofBijective _ (spread_bijective (A := A) (B := Fin m))
  rw [← e.sum_comp (fun s : Mix A (Fin m) => weight m d s.val),Fintype.sum_prod_type]
  apply Finset.sum_eq_zero
  intro u _
  change ∑ b : Fin m, weight m d ((rotate b).permCongr u.val.val) = 0
  simp only [weight_relabel, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ZMod.natCast_self, zero_mul]

private noncomputable def total (m n d : ℕ) : ZMod m := ∑ s : Perm (Fin n), weight m d s

private theorem block_step (m n d : ℕ) [NeZero m] :
    total m (n+m) d = ∑ t : Perm (Fin m), total m n (Nat.lcm d (orderOf t)) := by
  classical
  let e : Fin n ⊕ Fin m ≃ Fin (n+m) := finSumFinEquiv
  have h := e.permCongr.sum_comp (weight m d)
  simp only [weight_relabel] at h
  change _ = total m (n+m) d at h
  rw [← h, ← Fintype.sum_subtype_add_sum_subtype (fun s : Perm (Fin n ⊕ Fin m) => (crossing s).Nonempty)]
  change (∑ s : Mix (Fin n) (Fin m), weight m d s.val) +
    (∑ s : Split (Fin n) (Fin m), weight m d s.val) = _
  rw [mix_zero (Fin n) m d,zero_add]
  let f := Equiv.ofBijective _ (split_bijective (A := Fin n) (B := Fin m))
  rw [← f.sum_comp (fun s : Split (Fin n) (Fin m) => weight m d s.val),Fintype.sum_prod_type_right]
  apply sum_congr rfl
  intro t _
  apply sum_congr rfl
  intro s _
  exact weight_split (s,t) m d

private abbrev Divs (m : ℕ) := ↥m.factorial.divisors

private theorem periods (m : ℕ) [NeZero m] :
    ∃ N p : ℕ, 0 < p ∧ ∀ n, N ≤ n → ∀ d : Divs m, total m (n+p) d = total m n d := by
  classical
  let state (n : ℕ) (i : Fin m) (d : Divs m) := total m (n+i.val) d
  obtain ⟨u,v,huv,eq⟩ := Finite.exists_ne_map_eq_of_infinite state
  obtain ⟨N,K,hNK,H⟩ : ∃ N K : ℕ, N < K ∧ state N = state K := by
    rcases lt_or_gt_of_ne huv with h|h
    · exact ⟨u,v,h,eq⟩
    · exact ⟨v,u,h,eq.symm⟩
  let p := K-N
  have hp : 0 < p := by dsimp [p]; omega
  refine ⟨N,p,hp,?_⟩
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn d
    by_cases small : n < N+m
    · let i : Fin m := ⟨n-N,by omega⟩
      have h := congrFun (congrFun H i) d
      change total m (N+(n-N)) d = total m (K+(n-N)) d at h
      have a : N+(n-N) = n := by omega
      have b : K+(n-N) = n+p := by dsimp [p]; omega
      simpa [a,b] using h.symm
    · have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
      let k := n-m
      have kn : k+m = n := by dsimp [k]; omega
      have knp : (k+p)+m = n+p := by omega
      rw [← knp,block_step,← kn,block_step]
      apply sum_congr rfl
      intro t _
      have ht : orderOf t ∣ m.factorial := by
        simpa [Fintype.card_perm] using (orderOf_dvd_card (x := t))
      have hd := (Nat.mem_divisors.mp d.property).1
      let c : Divs m := ⟨Nat.lcm d.val (orderOf t), Nat.mem_divisors.mpr
        ⟨Nat.lcm_dvd hd ht,Nat.factorial_ne_zero _⟩⟩
      exact ih k (by omega) (by omega) c

end PermutationOrderSums

open PermutationOrderSums OMA.S_oeis_a060014

theorem OMA.solution : type_of% @OMA.S_oeis_a060014.main := by
  intro m hm
  let _ : NeZero m := ⟨hm.ne'⟩
  obtain ⟨N,p,hp,h⟩ := periods m
  refine ⟨N,p,hp,?_⟩
  intro n hn
  let one : Divs m := ⟨1,Nat.mem_divisors.mpr ⟨one_dvd _,Nat.factorial_ne_zero _⟩⟩
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
  simpa [one,total,weight,a] using h n hn one
