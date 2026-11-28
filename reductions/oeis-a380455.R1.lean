import OMAStatements.S_oeis_a380455

open Finset OMA.S_oeis_a380455
namespace OMA.R_oeis_a380455_R1

set_option maxHeartbeats 1600000 in
private lemma lower_and_seventeen :
    realizes 14 10 ∧ realizes 15 3 ∧ realizes 16 12 ∧ maximum 17 1 := by

  let Orientation := Bool × Bool × Bool

  let sign (b : Bool) : ℤ := if b then -1 else 1

  let turn (g : Orientation) (p : Cell) : Cell :=
    let q := if g.1 then (p.2,p.1) else p
    (sign g.2.1 * q.1,sign g.2.2 * q.2)

  let move (g : Orientation) (o p : Cell) : Cell := o + turn g p

  have sign_ok (b : Bool) : sign b=1 ∨ sign b = -1 := by cases b <;> decide

  have sign_exists {x : ℤ} (h : x=1 ∨ x= -1) : ∃ b, x=sign b := by
    rcases h with rfl|rfl
    · exact ⟨false,rfl⟩
    · exact ⟨true,rfl⟩

  have congruent_iff (A B : Shape) :
      congruent A B ↔ ∃ (g : Orientation) (o : Cell), B=A.image (move g o) := by
    constructor
    · rintro ⟨sw,sx,sy,o,hx,hy,rfl⟩
      obtain ⟨a,rfl⟩ := sign_exists hx
      obtain ⟨b,rfl⟩ := sign_exists hy
      exact ⟨⟨sw,a,b⟩,o,rfl⟩
    · rintro ⟨⟨sw,a,b⟩,o,rfl⟩
      exact ⟨sw,sign a,sign b,o,sign_ok a,sign_ok b,rfl⟩

  let inverse (g : Orientation) : Orientation :=
    if g.1 then ⟨true,g.2.2,g.2.1⟩ else g

  let compose (g h : Orientation) : Orientation :=
    ⟨g.1 ^^ h.1,(if h.1 then g.2.2 else g.2.1) ^^ h.2.1,
      (if h.1 then g.2.1 else g.2.2) ^^ h.2.2⟩

  have turn_inv (g : Orientation) (p : Cell) : turn (inverse g) (turn g p)=p := by
    obtain ⟨s,a,b⟩ := g
    cases s <;> cases a <;> cases b <;> simp [turn,inverse,sign]

  have turn_comp (g h : Orientation) (p : Cell) : turn (compose g h) p=turn h (turn g p) := by
    obtain ⟨s,a,b⟩ := g
    obtain ⟨t,c,d⟩ := h
    cases s <;> cases t <;> cases a <;> cases b <;> cases c <;> cases d <;> simp [turn,compose,sign]

  have turn_add (g : Orientation) (p q : Cell) : turn g (p+q)=turn g p+turn g q := by
    obtain ⟨s,a,b⟩:=g
    cases s <;> ext <;> simp [turn,mul_add]

  have motion_card {A B : Shape} (h : congruent A B) : A.card=B.card := by
    obtain ⟨g,o,rfl⟩ := (congruent_iff _ _).mp h
    symm
    apply card_image_of_injective
    intro p q eq
    have e : turn g p = turn g q := add_left_cancel (show o+turn g p=o+turn g q from eq)
    simpa only [turn_inv] using congrArg (turn (inverse g)) e

  have motion_symm {A B : Shape} (h : congruent A B) : congruent B A := by
    obtain ⟨g,o,rfl⟩ := (congruent_iff _ _).mp h
    apply (congruent_iff _ _).mpr
    refine ⟨inverse g,-turn (inverse g) o,?_⟩
    rw [image_image]
    have e : move (inverse g) (-turn (inverse g) o) ∘ move g o = id := by
      funext p
      simp [move,turn_add,turn_inv]
    simp only [e,image_id]

  have motion_trans {A B C : Shape} (h : congruent A B) (k : congruent B C) : congruent A C := by
    obtain ⟨g,o,rfl⟩ := (congruent_iff _ _).mp h
    obtain ⟨f,p,rfl⟩ := (congruent_iff _ _).mp k
    apply (congruent_iff _ _).mpr
    refine ⟨compose g f,p+turn f o,?_⟩
    rw [image_image]
    apply Finset.image_congr
    intro v hv
    simp [move,turn_add,turn_comp,add_assoc]

  let pairWeight (p q : Cell) : ℕ :=
    let a := (p.1-q.1).natAbs
    let b := (p.2-q.2).natAbs
    64 ^ (5*max a b + min a b)

  let signature (s : Shape) : ℕ :=
    ∑ p ∈ s, (∑ q ∈ s, pairWeight p q)^2

  have sign_delta (b : Bool) (x y : ℤ) :
      (sign b*x-sign b*y).natAbs=(x-y).natAbs := by
    rw [← mul_sub,Int.natAbs_mul]
    cases b <;> simp [sign]

  have weight_move (g : Orientation) (o p q : Cell) :
      pairWeight (move g o p) (move g o q)=pairWeight p q := by
    obtain ⟨s,x,y⟩:=g
    cases s <;> simp [pairWeight,move,turn,sign_delta,max_comm,min_comm]

  have signature_invariant {A B : Shape} (eq : congruent A B) : signature A=signature B := by
    obtain ⟨g,o,rfl⟩ := (congruent_iff A B).mp eq
    have inj : Function.Injective (move g o) := by
      intro p q h
      have e : turn g p=turn g q := add_left_cancel (show o+turn g p=o+turn g q from h)
      simpa only [turn_inv] using congrArg (turn (inverse g)) e
    unfold signature
    rw [sum_image inj.injOn]
    apply sum_congr rfl
    intro p hp
    rw [sum_image inj.injOn]
    simp only [weight_move]

  have reverse_adj {a b : Cell} (h : adjacent a b) : adjacent b a := by
    rcases h with ⟨e,f|f⟩|⟨e,f|f⟩
    · exact Or.inl ⟨e.symm, Or.inr f⟩
    · exact Or.inl ⟨e.symm, Or.inl f⟩
    · exact Or.inr ⟨e.symm, Or.inr f⟩
    · exact Or.inr ⟨e.symm, Or.inl f⟩

  have add_cell {s : Shape} (h : polyomino s) (p q : Cell) (mem : q∈s)
      (edge : adjacent p q) : polyomino (insert p s) := by
    let lift (z : s) : ↥(insert p s) := ⟨z.val,mem_insert_of_mem z.property⟩
    let R (a b : ↥(insert p s)) := adjacent a.val b.val
    have within (a b : s) : Relation.ReflTransGen R (lift a) (lift b) :=
      Relation.ReflTransGen.lift lift (fun _ _ e => e) a b (h.2 a b)
    have both (a : ↥(insert p s)) :
        Relation.ReflTransGen R a (lift ⟨q,mem⟩) ∧ Relation.ReflTransGen R (lift ⟨q,mem⟩) a := by
      obtain ⟨v,hv⟩:=a
      rcases mem_insert.mp hv with rfl|hv
      · exact ⟨.single edge,.single (reverse_adj edge)⟩
      · exact ⟨within ⟨v,hv⟩ _,within _ ⟨v,hv⟩⟩
    exact ⟨insert_nonempty _ _,fun a b => (both a).1.trans (both b).2⟩

  let neighborFlag (a b : Cell) : Bool :=
    decide ((a.1=b.1 ∧ (a.2+1=b.2 ∨ b.2+1=a.2)) ∨
      (a.2=b.2 ∧ (a.1+1=b.1 ∨ b.1+1=a.1)))

  have neighborFlag_spec (p q : Cell) : neighborFlag p q=true ↔ adjacent p q :=
    decide_eq_true_iff

  let building (l : List Cell) : Bool :=
    List.rec false (fun p rest value => if rest=[] then true else
      value && rest.any (neighborFlag p)) l

  let rec poly_of_building : ∀ l : List Cell, building l=true → polyomino l.toFinset
    | [],h => by simp [building] at h
    | [p],_ => by
      refine ⟨by simp,?_⟩
      rintro ⟨a,ha⟩ ⟨b,hb⟩
      simp at ha hb
      subst a
      subst b
      rfl
    | p::q::rest,h => by
      have hb : building (q::rest)=true ∧ (q::rest).any (neighborFlag p)=true := by
        simpa [building] using h
      obtain ⟨v,hv,edge⟩ := List.any_eq_true.mp hb.2
      simpa only [List.toFinset_cons] using add_cell (poly_of_building _ hb.1) p v (List.mem_toFinset.mpr hv) ((neighborFlag_spec _ _).mp edge)

  have move_injective (g : Orientation) (o : Cell) : Function.Injective (move g o) := by
    intro p q e
    have h : turn g p=turn g q := add_left_cancel (show o+turn g p=o+turn g q from e)
    simpa only [turn_inv] using congrArg (turn (inverse g)) h

  have self_congruent (s : Shape) : congruent s s := by
    refine (congruent_iff _ _).mpr ⟨⟨false,false,false⟩,0,?_⟩
    have g : move ⟨false,false,false⟩ 0 = id := by funext p; ext <;> simp [move,turn,sign]
    simp [g]

  have tile_area {f b : Shape} (tiling : tiles f b) : f.card ∣ b.card := by
    classical
    obtain ⟨parts,_,cover,cong,disj⟩ := tiling
    have rest : (∑ t∈parts,t.card)=parts.card*f.card := by
      calc
        _ = ∑ _t∈parts,f.card := sum_congr rfl (fun t ht => (motion_card (cong t ht)).symm)
        _ = _ := by simp
    refine ⟨parts.card,?_⟩
    rw [← cover,card_biUnion (by
      intro i hi j hj ne
      exact disj i hi j hj ne)]
    simpa only [id_eq,Nat.mul_comm] using rest

  have prime_area {s : Shape} (poly : polyomino s) (prime : s.card.Prime) : primeShape s := by
    refine ⟨poly,prime.one_lt,?_⟩
    intro t _ h ts
    exact ((Nat.dvd_prime prime).mp (tile_area ts)).resolve_left (by omega)

  have single_tile {s b : Shape} (h : tiles s b) (eq : s.card=b.card) : congruent s b := by
    obtain ⟨parts,⟨p,hp⟩,cover,cong,_⟩:=h
    have sub : p⊆b := by
      rw [← cover]
      intro a ha
      exact mem_biUnion.mpr ⟨p,hp,ha⟩
    have e : p=b := eq_of_subset_of_card_le sub (by rw [← eq,motion_card (cong p hp)])
    exact e ▸ cong p hp

  have tiles_itself (s : Shape) : tiles s s := by
    refine ⟨{s},by simp,by simp,?_,?_⟩
    · simpa using self_congruent s
    · simp

  have one_factor_of_prime {n : ℕ} (prime : n.Prime)
      (exists_poly : ∃ s : Shape,polyomino s ∧ s.card=n) : maximum n 1 := by
    obtain ⟨s,poly,hs⟩:=exists_poly
    constructor
    · refine ⟨s,{s},poly,hs,by simp,?_,?_⟩
      · simpa using And.intro (prime_area poly (hs ▸ prime)) (tiles_itself s)
      · simp
    · rintro j ⟨b,fs,_,hb,hj,fact,different⟩
      rw [← hj,card_le_one]
      have all (t : Shape) (ht : t∈fs) : congruent t b := by
        have g := fact t ht
        have p : b.card.Prime := hb ▸ prime
        exact single_tile g.2 (((Nat.dvd_prime p).mp (tile_area g.2)).resolve_left (by
          have := g.1.2.1
          omega))
      intro p hp q hq
      exact different p hp q hq (motion_trans (all p hp) (motion_symm (all q hq)))

  let mark (p : Cell) : ZMod 2 := (p.1 : ZMod 2)+(p.2 : ZMod 2)
  let mass (s : Shape) : ZMod 2 := ∑ p∈s,mark p

  have affine_mark (g : Orientation) (o p : Cell) :
      mark (move g o p)=mark o+mark p := by
    obtain ⟨s,a,b⟩:=g
    cases s <;> cases a <;> cases b <;> simp [move,turn,sign,mark] <;> ring

  have mass_motion {s t : Shape} (h : congruent s t) (even : (s.card : ZMod 2)=0) :
      mass t=mass s := by
    obtain ⟨g,o,rfl⟩ := (congruent_iff _ _).mp h
    unfold mass
    rw [sum_image (move_injective g o).injOn]
    simp only [affine_mark,sum_add_distrib,sum_const,nsmul_eq_mul,even,zero_mul,zero_add]

  have eight_arithmetic {n k : ℕ} (h : k*n=8) (two : 1<n) (proper : n≠8) :
      (n=2 ∧ k=4) ∨ (n=4 ∧ k=2) := by
    have pos : 0<k := by
      cases k with
      | zero => simp at h
      | succ k => omega
    have bound : n≤8 := h ▸ Nat.le_mul_of_pos_left n pos
    interval_cases n <;> omega

  have odd_mass_eight {s : Shape} (poly : polyomino s) (size : s.card=8) (odd : mass s≠0) :
      primeShape s := by
    classical
    refine ⟨poly,by omega,?_⟩
    rintro t _ nt ⟨parts,_,cover,cong,disj⟩
    by_contra bad
    have sep : (↑parts : Set Shape).PairwiseDisjoint id := by
      intro a ha b hb ne
      exact disj a ha b hb ne
    have ar : parts.card*t.card=8 := calc
      _ = ∑ _u∈parts,t.card := by simp
      _ = ∑ u∈parts,u.card := sum_congr rfl (fun u hu => motion_card (cong u hu))
      _ = (parts.biUnion id).card := (card_biUnion sep).symm
      _ = 8 := by rw [cover,size]
    have cases_ := eight_arithmetic ar nt (by simpa only [size] using bad)
    have even_size : (t.card : ZMod 2)=0 := by rcases cases_ with h|h <;> rw [h.1] <;> decide
    have even_q : (parts.card : ZMod 2)=0 := by rcases cases_ with h|h <;> rw [h.2] <;> decide
    apply odd
    change (∑ c∈s,mark c) = 0
    rw [← cover,sum_biUnion sep]
    calc
      _ = ∑ _u∈parts,mass t := sum_congr rfl (fun u hu => mass_motion (cong u hu) even_size)
      _ = 0 := by simp [nsmul_eq_mul,even_q]



  let Placement := Orientation × Cell

  let tileParts (s : Shape) (places : List Placement) : Finset Shape :=
    (places.map (fun m => s.image (move m.1 m.2))).toFinset

  let checkTiling (s board : Shape) (places : List Placement) : Bool :=
    let parts := tileParts s places
    decide (parts.Nonempty ∧ parts.biUnion id=board ∧
      ∀ p∈parts, ∀ q∈parts, p≠q → Disjoint p q)

  have checked_tiling {s b : Shape} {ms : List Placement} (ok : checkTiling s b ms=true) :
      tiles s b := by
    let parts := tileParts s ms
    have h : parts.Nonempty ∧ parts.biUnion id = b ∧
        ∀ p∈parts, ∀ q∈parts, p≠q → Disjoint p q := of_decide_eq_true ok
    refine ⟨parts,h.1,h.2.1,?_,h.2.2⟩
    intro p hp
    obtain ⟨m,_,em⟩ := List.mem_map.mp (List.mem_toFinset.mp hp)
    exact (congruent_iff _ _).mpr ⟨m.1,m.2,em.symm⟩

  let Entry := List Cell × List Placement

  let entryShape (e : Entry) : Shape := e.1.toFinset

  let entryCheck (board : Shape) (e : Entry) : Bool :=
    building e.1 && (decide (entryShape e).card.Prime ||
        decide ((entryShape e).card=8 ∧ mass (entryShape e)≠0)) &&
      checkTiling (entryShape e) board e.2

  have entry_ok (board : Shape) (e : Entry) (ok : entryCheck board e=true) :
      primeShape (entryShape e) ∧ tiles (entryShape e) board := by
    simp only [entryCheck,Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq] at ok
    have poly := poly_of_building e.1 ok.1.1
    refine ⟨?_,checked_tiling ok.2⟩
    rcases ok.1.2 with hp|⟨sz,odd⟩
    · exact prime_area poly hp
    · exact odd_mass_eight poly sz odd

  let modelsOf (es : List Entry) : Finset Shape := (es.map entryShape).toFinset

  have of_entries (n k : ℕ) (b : List Cell) (entries : List Entry)
      (connected : building b=true) (area : b.toFinset.card=n)
      (count : (modelsOf entries).card=k) (ok : entries.all (entryCheck b.toFinset)=true)
      (unique : ((modelsOf entries).image signature).card=(modelsOf entries).card) :
      realizes n k := by
    refine ⟨b.toFinset,modelsOf entries,poly_of_building _ connected,area,count,?_,?_⟩
    · intro t ht
      obtain ⟨e,he,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ht)
      exact entry_ok _ _ (List.all_eq_true.mp ok e he)
    · intro p hp q hq eq
      exact card_image_iff.mp unique hp hq (signature_invariant eq)



  let boardFourteen : List Cell := [(5,2),(4,2),(3,2),(4,1),(2,2),(3,1),(4,0),(1,2),(2,1),(3,0),(1,1),(2,0),(1,0),(0,0)]

  let factorsFourteen : List Entry := [
    ⟨[(4,0),(3,0),(1,1),(2,0),(0,1),(1,0),(0,0)],[(⟨false,true,false⟩,(4,0)),(⟨false,false,true⟩,(1,2))]⟩,
    ⟨[(4,0),(2,1),(3,0),(2,0),(0,1),(1,0),(0,0)],[(⟨false,true,false⟩,(4,0)),(⟨false,false,true⟩,(1,2))]⟩,
    ⟨[(4,0),(2,1),(3,0),(1,1),(2,0),(1,0),(0,0)],[(⟨false,false,false⟩,(0,0)),(⟨false,true,true⟩,(5,2))]⟩,
    ⟨[(3,1),(4,0),(3,0),(1,1),(2,0),(1,0),(0,0)],[(⟨false,false,false⟩,(0,0)),(⟨false,false,true⟩,(1,2))]⟩,
    ⟨[(2,2),(2,1),(3,0),(2,0),(0,1),(1,0),(0,0)],[(⟨false,true,false⟩,(3,0)),(⟨false,false,true⟩,(2,2))]⟩,
    ⟨[(1,2),(2,1),(3,0),(1,1),(2,0),(1,0),(0,0)],[(⟨false,false,false⟩,(0,0)),(⟨false,true,true⟩,(5,2))]⟩,
    ⟨[(2,1),(0,2),(1,1),(2,0),(0,1),(1,0),(0,0)],[(⟨true,true,false⟩,(2,0)),(⟨true,false,true⟩,(3,2))]⟩,
    ⟨[(3,2),(2,2),(2,1),(2,0),(0,1),(1,0),(0,0)],[(⟨false,true,true⟩,(3,2)),(⟨false,false,false⟩,(2,0))]⟩,
    ⟨[(3,2),(2,2),(2,1),(1,1),(2,0),(1,0),(0,0)],[(⟨false,true,true⟩,(3,2)),(⟨false,false,false⟩,(2,0))]⟩,
    ⟨[(1,0),(0,0)],[(⟨false,false,false⟩,(0,0)),(⟨false,false,false⟩,(2,0)),(⟨true,false,false⟩,(4,0)),(⟨false,false,false⟩,(1,1)),(⟨true,false,false⟩,(3,1)),(⟨false,false,false⟩,(1,2)),(⟨false,false,false⟩,(4,2))]⟩]

  set_option maxRecDepth 20000 in
  have tested14 : factorsFourteen.all (entryCheck boardFourteen.toFinset)=true := by decide +kernel

  set_option maxRecDepth 20000 in
  have distinct14 : ((modelsOf factorsFourteen).image signature).card=(modelsOf factorsFourteen).card := by decide +kernel

  have achieves_14 : realizes 14 10 :=
    of_entries 14 10 boardFourteen factorsFourteen (by decide +kernel) (by decide +kernel)
      (by decide +kernel) tested14 distinct14



  let boardFifteen : List Cell := [(6,1),(7,0),(5,1),(6,0),(3,2),(4,1),(5,0),(3,1),(4,0),(2,1),(3,0),(1,1),(2,0),(1,0),(0,0)]

  let factorsFifteen : List Entry := [
    ⟨[(3,0),(1,1),(2,0),(1,0),(0,0)],[(⟨false,false,false⟩,(0,0)),(⟨false,true,false⟩,(7,0)),(⟨false,false,false⟩,(2,1))]⟩,
    ⟨[(1,1),(2,0),(0,1),(1,0),(0,0)],[(⟨false,true,false⟩,(2,0)),(⟨true,false,false⟩,(3,0)),(⟨false,false,false⟩,(5,0))]⟩,
    ⟨[(0,1),(1,0),(0,0)],[(⟨false,true,false⟩,(1,0)),(⟨false,false,false⟩,(2,0)),(⟨false,true,false⟩,(5,0)),(⟨false,false,false⟩,(6,0)),(⟨false,false,false⟩,(3,1))]⟩]

  set_option maxRecDepth 20000 in
  have tested15 : factorsFifteen.all (entryCheck boardFifteen.toFinset)=true := by decide +kernel

  set_option maxRecDepth 20000 in
  have distinct15 : ((modelsOf factorsFifteen).image signature).card=(modelsOf factorsFifteen).card := by decide +kernel

  have achieves_15 : realizes 15 3 :=
    of_entries 15 3 boardFifteen factorsFifteen (by decide +kernel) (by decide +kernel)
      (by decide +kernel) tested15 distinct15



  let boardSixteen : List Cell := [(4,3),(5,2),(3,3),(4,2),(2,3),(3,0),(3,2),(4,1),(2,0),(2,2),(3,1),(1,0),(1,2),(2,1),(1,1),(0,1)]

  let factorsSixteen : List Entry := [
    ⟨[(3,1),(4,0),(2,1),(3,0),(1,1),(2,0),(1,0),(0,0)],[(⟨false,false,true⟩,(0,1)),(⟨false,false,false⟩,(1,2))]⟩,
    ⟨[(1,2),(2,1),(3,0),(1,1),(2,0),(0,1),(1,0),(0,0)],[(⟨true,true,false⟩,(2,0)),(⟨true,false,true⟩,(3,3))]⟩,
    ⟨[(2,2),(3,1),(2,1),(1,1),(2,0),(0,1),(1,0),(0,0)],[(⟨false,true,false⟩,(3,0)),(⟨false,false,true⟩,(2,3))]⟩,
    ⟨[(2,2),(3,1),(2,1),(0,2),(2,0),(0,1),(1,0),(0,0)],[(⟨false,true,false⟩,(3,0)),(⟨false,false,true⟩,(2,3))]⟩,
    ⟨[(2,2),(3,1),(1,2),(2,1),(1,1),(2,0),(1,0),(0,0)],[(⟨false,true,false⟩,(3,0)),(⟨false,false,true⟩,(2,3))]⟩,
    ⟨[(4,2),(3,2),(3,1),(2,1),(1,1),(2,0),(1,0),(0,0)],[(⟨false,false,false⟩,(1,0)),(⟨false,true,true⟩,(4,3))]⟩,
    ⟨[(4,2),(3,2),(2,2),(2,1),(1,1),(2,0),(1,0),(0,0)],[(⟨false,true,true⟩,(5,2)),(⟨false,false,false⟩,(0,1))]⟩,
    ⟨[(0,2),(1,2),(2,2),(3,1),(2,1),(2,0),(1,0),(0,0)],[(⟨false,true,false⟩,(3,0)),(⟨false,false,false⟩,(2,1))]⟩,
    ⟨[(2,3),(3,2),(2,2),(2,1),(1,1),(0,1),(1,0),(0,0)],[(⟨false,true,true⟩,(3,3)),(⟨false,false,false⟩,(2,0))]⟩,
    ⟨[(2,3),(3,2),(2,2),(1,2),(2,1),(1,1),(1,0),(0,0)],[(⟨false,true,true⟩,(3,3)),(⟨false,false,false⟩,(2,0))]⟩,
    ⟨[(4,1),(3,1),(3,0),(2,0),(1,0),(1,2),(1,1),(0,1)],[(⟨false,true,false⟩,(4,0)),(⟨false,false,true⟩,(1,3))]⟩,
    ⟨[(2,3),(3,2),(2,0),(2,2),(1,0),(1,2),(1,1),(0,1)],[(⟨false,false,false⟩,(0,0)),(⟨false,true,true⟩,(5,3))]⟩]

  set_option maxRecDepth 20000 in
  have tested16 : factorsSixteen.all (entryCheck boardSixteen.toFinset)=true := by decide +kernel

  set_option maxRecDepth 20000 in
  have distinct16 : ((modelsOf factorsSixteen).image signature).card=(modelsOf factorsSixteen).card := by decide +kernel

  have achieves_16 : realizes 16 12 :=
    of_entries 16 12 boardSixteen factorsSixteen (by decide +kernel) (by decide +kernel)
      (by decide +kernel) tested16 distinct16



  let barSeventeen : List Cell := [(16,0),(15,0),(14,0),(13,0),(12,0),(11,0),(10,0),(9,0),(8,0),(7,0),(6,0),(5,0),(4,0),(3,0),(2,0),(1,0),(0,0)]

  have exact_seventeen : maximum 17 1 :=
    one_factor_of_prime (by decide) ⟨barSeventeen.toFinset,poly_of_building _ (by decide +kernel),by decide +kernel⟩


  exact ⟨achieves_14,achieves_15,achieves_16,exact_seventeen⟩

def H1 : Prop := ∀ j : ℕ, realizes 14 j → j≤10

def H2 : Prop := ∀ j : ℕ, realizes 15 j → j≤3

def H3 : Prop := ∀ j : ℕ, realizes 16 j → j≤12

theorem main : H1 → H2 → H3 → type_of% @OMA.S_oeis_a380455.main := by
  intro fourteen fifteen sixteen
  obtain ⟨a,b,c,d⟩ := lower_and_seventeen
  exact ⟨⟨a,fourteen⟩,⟨b,fifteen⟩,⟨c,sixteen⟩,d⟩

end OMA.R_oeis_a380455_R1
