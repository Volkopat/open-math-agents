import OMAStatements.S_oeis_a395495
import Mathlib

/-!
# A size-57 counterexample at order 11

Myeongjin Kang gave this fixed-polyomino container in
https://mathdb.com/abs/2611.00029. We verify it using a rooted search.
The root is the leftmost cell on the bottom row. At each frontier cell,
the search includes or excludes it. A bit in the running intersection
records a single translation placing every included cell in the container.
-/
-- Credit: @VestigeClub
namespace PolyominoSearch
abbrev Cell := ℤ × ℤ

def inside (p : Cell) : Bool :=
  decide (|p.1|+|p.2|≤5 ∧ ¬(|p.1|=2 ∧ |p.2|=2))

def shift (j : ℕ) : Cell := (((j%11 : ℕ):ℤ)-5, ((j/11 : ℕ):ℤ)-5)

/-- Each row concatenates 21 masks, one for each horizontal offset.
A mask has one bit for each translation of the root into the 11-by-11 box. -/
def packed : ℕ → ℕ
  | 0 => 0x800000000000000000000000000200c00800000000000000000000080300e00c00800000000000000020080380f00e008008000000000080300a03c0f80f00a00c0080000200c0380b03e0fc0f80b00e00c0080200e03c0b83f0fe0fc0b80f00e0080200e03e0b83f8ff0fe0b80f80e0080200e03e0ba3fcff8ff0ba0f80e0080200e03e0ba3feffcff8ba0f80e0080200e03e0ba3feffeff8ba0f80e0080200e03e0ba3fe7feff8ba0f80e0080200e03e0ba1fe3fe7f8ba0f80e0080200e03e03a0fe1fe3f83a0f80e0080200e01e03a07e0fe1f83a0780e0080200600e01a03e07e0f81a038060080000200600a01e03e0780a018020000000000200200e01e03802008000000000000000200600e0180200000000000000000000020060080000000000000000000000000020000000000000000
  | 1 => 0x1000000000000000000000000000401801000000000000000000000100601c01801000000000000000040100701e01c01001000000000010060140781f01e014018010000040180701607c1f81f01601c0180000401c0781707e1fc1f81701e01c0000401c07c1707f1fe1fc1701f01c0000401c07c1747f9ff1fe1741f01c0000401c07c1747fdff9ff1741f01c0000401c07c1747fdffdff1741f01c0000401c07c1747fcffdff1741f01c0000401c07c1743fc7fcff1741f01c0000401c07c0741fc3fc7f0741f01c0000401c03c0740fc1fc3f0740f01c0000400c01c03407c0fc1f0340700c0000000400c01403c07c0f014030040000000000400401c03c07004010000000000000000400c01c03004000000000000000000000400c0100000000000000000000000000040000000000000
  | 2 => 0x2000000000000000000000000000803002000000000000000000000200c03803002000000000000000080200e03c038020020000000000200c0280f03e03c028030000000080300e02c0f83f03e02c038000000080380f02e0fc3f83f02e03c000000080380f82e0fe3fc3f82e03e000000080380f82e8ff3fe3fc2e83e000000080380f82e8ffbff3fe2e83e000000080380f82e8ffbffbfe2e83e000000080380f82e8ff9ffbfe2e83e000000080380f82e87f8ff9fe2e83e000000080380f80e83f87f8fe0e83e000000080380780e81f83f87e0e81e000000080180380680f81f83e0680e000000000080180280780f81e02806000000000000080080380780e00802000000000000000080180380600800000000000000000000080180200000000000000000000000000080000000000
  | 3 => 0x4000000000000000000000000001006004000000000000000000000401807006004000000000000000100401c07807004000000000000040180501e07c078050000000000100601c0581f07e07c058000000000100701e05c1f87f07e05c000000000100701f05c1fc7f87f05c000000000100701f05d1fe7fc7f85d000000000100701f05d1ff7fe7fc5d000000000100701f05d1ff7ff7fc5d000000000100701f05d1ff3ff7fc5d000000000100701f05d0ff1ff3fc5d000000000100701f01d07f0ff1fc1d000000000100700f01d03f07f0fc1d000000000100300700d01f03f07c0d000000000000100300500f01f03c05000000000000000100100700f01c01000000000000000000100300700c01000000000000000000000100300400000000000000000000000000100000000
  | 4 => 0x800000000000000000000000000200c00800000000000000000000080300e00c00000000000000000020080380f00e000000000000000080300a03c0f80f0000000000000200c0380b03e0fc0f8000000000000200e03c0b83f0fe0fc000000000000200e03e0b83f8ff0fe000000000000200e03e0ba3fcff8ff000000000000200e03e0ba3feffcff800000000000200e03e0ba3feffeff800000000000200e03e0ba3fe7feff800000000000200e03e0ba1fe3fe7f800000000000200e03e03a0fe1fe3f800000000000200e01e03a07e0fe1f800000000000200600e01a03e07e0f800000000000000200600a01e03e07800000000000000000200200e01e03800000000000000000000200600e01800000000000000000000000200600800000000000000000000000000200000
  | 5 => 0x1000000000000000000000000000401800000000000000000000000100601c00000000000000000000040100701e00000000000000000010060140781f000000000000000040180701607c1f8000000000000000401c0781707e1fc000000000000000401c07c1707f1fe000000000000000401c07c1747f9ff000000000000000401c07c1747fdff800000000000000401c07c1747fdffc00000000000000401c07c1747fcffc00000000000000401c07c1743fc7fc00000000000000401c07c0741fc3fc00000000000000401c03c0740fc1fc00000000000000400c01c03407c0fc00000000000000000400c01403c07c00000000000000000000400401c03c00000000000000000000000400c01c00000000000000000000000000400c00000000000000000000000000000400
  | 6 => 0x800000000000000000000000000200c00000000000000000000000080200e000000000000000000000200c0280f000000000000000000080300e02c0f800000000000000000080380f02e0fc00000000000000000080380f82e0fe00000000000000000080380f82e8ff00000000000000000080380f82e8ff80000000000000000080380f82e8ff80000000000000000080380f82e8ff80000000000000000080380f82e87f80000000000000000080380f80e83f80000000000000000080380780e81f80000000000000000080180380680f800000000000000000000801802807800000000000000000000000800803800000000000000000000000000801800000000000000000000000000000800000000000000000000000000000000
  | 7 => 0x4000000000000000000000000001004000000000000000000000000401805000000000000000000000100601c05800000000000000000000100701e05c00000000000000000000100701f05c00000000000000000000100701f05d00000000000000000000100701f05d00000000000000000000100701f05d00000000000000000000100701f05d00000000000000000000100701f05d00000000000000000000100701f01d00000000000000000000100700f01d00000000000000000000100300700d000000000000000000000001003005000000000000000000000000001001000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000
  | 8 => 0x2000000000000000000000000000803000000000000000000000000200c03800000000000000000000000200e03c00000000000000000000000200e03e00000000000000000000000200e03e00000000000000000000000200e03e00000000000000000000000200e03e00000000000000000000000200e03e00000000000000000000000200e03e00000000000000000000000200e03e00000000000000000000000200e01e00000000000000000000000200600e000000000000000000000000002006000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
  | 9 => 0x1000000000000000000000000000401800000000000000000000000000401c00000000000000000000000000401c00000000000000000000000000401c00000000000000000000000000401c00000000000000000000000000401c00000000000000000000000000401c00000000000000000000000000401c00000000000000000000000000401c00000000000000000000000000401c00000000000000000000000000400c000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
  | 10 => 0x8000000000000000000000000000008000000000000000000000000000008000000000000000000000000000008000000000000000000000000000008000000000000000000000000000008000000000000000000000000000008000000000000000000000000000008000000000000000000000000000008000000000000000000000000000008000000000000000000000000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
  | _ => 0

def slot (x y : ℕ) := (packed y >>> (121*x))%2^121

def possibilities (p : Cell) : ℕ :=
  if -10≤p.1 ∧ p.1≤10 ∧ 0≤p.2 ∧ p.2≤10 then slot (p.1+10).toNat p.2.toNat else 0

def eligible (p : Cell) : Bool := decide (0<p.2 ∨ (p.2=0 ∧ 0≤p.1))

def neighbors (p : Cell) : List Cell :=
  [(p.1+1,p.2), (p.1-1,p.2), (p.1,p.2+1), (p.1,p.2-1)]

def key (p : Cell) : ℕ := Encodable.encode p

def remember (xs : List Cell) (s : ℕ) : ℕ :=
  xs.foldr (fun p old => old ||| (1 <<< key p)) s

def fresh (p : Cell) (seen : ℕ) : List Cell :=
  (neighbors p).filter (fun q => eligible q && !(seen.testBit (key q)))

def inspect (later : List Cell → ℕ → ℕ → Bool) (seen possible : ℕ) : List Cell → Bool
  | [] => true
  | v::tail =>
      let add := fresh v seen
      later (add++tail) (remember add seen) (possible &&& possibilities v) &&
        inspect later seen possible tail

def check : ℕ → List Cell → ℕ → ℕ → Bool
  | 0, _, _, possible => possible != 0
  | n+1, queue, seen, possible => inspect (check n) seen possible queue

def origin : Cell := (0,0)
def initial := fresh origin (remember [origin] 0)
def allFit (n : ℕ) : Bool :=
  check n initial (remember initial (remember [origin] 0)) (possibilities origin)

end PolyominoSearch

namespace PolyominoSearch

private theorem marked (xs : List Cell) (s : ℕ) (x : Cell) :
    (remember xs s).testBit (key x)=true ↔ x∈xs ∨ s.testBit (key x)=true := by
  induction xs with
  | nil => simp [remember]
  | cons a xs ih =>
    change ((remember xs s) ||| (1 <<< key a)).testBit (key x)=true ↔
      x∈a::xs ∨ s.testBit (key x)=true
    have injective : Function.Injective key := Encodable.encode_injective
    rw [Nat.testBit_or,Nat.shiftLeft_eq,one_mul,Nat.testBit_two_pow,Bool.or_eq_true,
      decide_eq_true_eq,ih,List.mem_cons,injective.eq_iff]
    tauto

def Boundary (whole : Finset Cell) : Prop :=
  ∀ A : Finset Cell, A.Nonempty → A⊆whole → A≠whole →
    ∃ u∈A, ∃ v∈whole, v∉A ∧ v∈neighbors u

def Covered (whole : Finset Cell) : Prop :=
  ∃ j : ℕ, ∀ p∈whole, (possibilities p).testBit j=true

private structure State (whole taken : Finset Cell) (todo : List Cell) (seen possible : ℕ) : Prop where
  sub : taken⊆whole
  nonempty : taken.Nonempty
  pending : ∀ p∈whole, seen.testBit (key p)=true → p∈taken ∨ p∈todo
  frontier : ∀ u∈taken, ∀ p∈whole, p∈neighbors u → seen.testBit (key p)=true
  usable : ∀ j, possible.testBit j=true → ∀ p∈taken, (possibilities p).testBit j=true

private theorem skip {whole taken v tail seen possible}
    (st : State whole taken (v::tail) seen possible) (miss : ¬(v∈whole ∧ v∉taken)) :
    State whole taken tail seen possible := by
  refine ⟨st.sub,st.nonempty,?_,st.frontier,st.usable⟩
  intro p hp bit
  rcases st.pending p hp bit with inside | mem
  · exact Or.inl inside
  rcases List.mem_cons.mp mem with rfl | later
  · exact Or.inl (by by_contra no; exact miss ⟨hp,no⟩)
  · exact Or.inr later

private theorem add {whole taken v tail seen possible}
    (st : State whole taken (v::tail) seen possible) (hv : v∈whole)
    (allowed : ∀ p∈whole, eligible p=true) :
    State whole (insert v taken) (fresh v seen++tail) (remember (fresh v seen) seen)
      (possible &&& possibilities v) := by
  refine ⟨Finset.insert_subset hv st.sub,Finset.insert_nonempty _ _,?_,?_,?_⟩
  · intro p hp bit
    rcases (marked _ _ _).mp bit with added | old
    · exact Or.inr (List.mem_append_left _ added)
    rcases st.pending p hp old with takenP | todo
    · exact Or.inl (Finset.mem_insert_of_mem takenP)
    rcases List.mem_cons.mp todo with rfl | later
    · exact Or.inl (Finset.mem_insert_self _ _)
    · exact Or.inr (List.mem_append_right _ later)
  · intro u hu p hp adj
    apply (marked _ _ _).mpr
    rcases Finset.mem_insert.mp hu with rfl | prior
    · by_cases seenP : seen.testBit (key p)=true
      · exact Or.inr seenP
      · exact Or.inl (List.mem_filter.mpr ⟨adj,by simp [allowed p hp,seenP]⟩)
    · exact Or.inr (st.frontier u prior p hp adj)
  · intro j bit p hp
    rw [Nat.testBit_and,Bool.and_eq_true] at bit
    rcases Finset.mem_insert.mp hp with rfl | prior
    · exact bit.2
    · exact st.usable j bit.1 p prior

/-- Follow the branch prescribed by the target piece. Connectivity guarantees a
frontier edge until the piece is complete. -/
private theorem check_sound (whole : Finset Cell) (boundary : Boundary whole)
    (allowed : ∀ p∈whole, eligible p=true) (n : ℕ) :
    ∀ todo seen possible taken, State whole taken todo seen possible →
    taken.card+n=whole.card → check n todo seen possible=true → Covered whole := by
  induction n with
  | zero =>
    intro todo seen possible taken st count checked
    have nonzero : possible ≠ 0 := by simpa [check] using checked
    obtain ⟨j,bit⟩ := Nat.exists_testBit_of_ne_zero nonzero
    have eq := Finset.eq_of_subset_of_card_le st.sub (by omega)
    exact ⟨j,eq ▸ st.usable j bit⟩
  | succ n ih =>
    intro todo
    induction todo with
    | nil =>
      intro seen possible taken st count checked
      have ne : taken≠whole := by intro eq; subst taken; omega
      obtain ⟨u,hu,v,hv,out,edge⟩ := boundary taken st.nonempty st.sub ne
      rcases st.pending v hv (st.frontier u hu v hv edge) with inside | bad
      · exact (out inside).elim
      · exact (List.not_mem_nil bad).elim
    | cons v tail lower =>
      intro seen possible taken st count checked
      change (check n (fresh v seen++tail) (remember (fresh v seen) seen)
        (possible &&& possibilities v) && inspect (check n) seen possible tail)=true at checked
      rw [Bool.and_eq_true] at checked
      obtain ⟨yes,no⟩ := checked
      by_cases has : v∈whole ∧ v∉taken
      · apply ih _ _ _ _ (add st has.1 allowed) _ yes
        rw [Finset.card_insert_of_notMem has.2]
        omega
      · exact lower seen possible taken (skip st has) count no

theorem rooted (whole : Finset Cell) (contains : origin∈whole) (n : ℕ) (size : whole.card=n+1)
    (allowed : ∀ p∈whole, eligible p=true) (boundary : Boundary whole)
    (verified : allFit n=true) : Covered whole := by
  apply check_sound whole boundary allowed n initial _ _ {origin} _ (by simpa [Nat.add_comm] using size.symm) verified
  refine ⟨Finset.singleton_subset_iff.mpr contains,Finset.singleton_nonempty _,?_,?_,?_⟩
  · intro p hp bit
    rcases (marked _ _ _).mp bit with queue | before
    · exact Or.inr queue
    rcases (marked _ _ _).mp before with start | zero
    · exact Or.inl (by simpa using start)
    · simp at zero
  · intro u hu p hp edge
    have eq := Finset.mem_singleton.mp hu
    subst u
    apply (marked _ _ _).mpr
    by_cases old : (remember [origin] 0).testBit (key p)=true
    · exact Or.inr old
    · exact Or.inl (List.mem_filter.mpr ⟨edge,by simp [allowed p hp,old]⟩)
  · intro j hj p hp
    simpa only [Finset.mem_singleton.mp hp] using hj

end PolyominoSearch

namespace PolyominoSearch

private def slotCheck (y x j : ℕ) : Bool :=
  !(slot x y).testBit j || inside ((((x : ℤ)-10,(y : ℤ)) : Cell)+shift j)

private theorem geometricTable :
    (List.range 11).all (fun y => (List.range 21).all (fun x =>
      (List.range 121).all (fun j => slotCheck y x j)))=true := by
  decide +kernel

theorem fits_of_bit {p : Cell} {j : ℕ} (bit : (possibilities p).testBit j=true) :
    inside (p+shift j)=true := by
  unfold possibilities at bit
  split at bit
  next guard =>
    obtain ⟨xl,xh,yl,yh⟩ := guard
    have bound : slot (p.1+10).toNat p.2.toNat < 2^121 := Nat.mod_lt _ (by decide)
    have jbound : j<121 := by
      by_contra! large
      have off := Nat.testBit_lt_two_pow (lt_of_lt_of_le bound (Nat.pow_le_pow_right (by decide : 0<2) large))
      rw [off] at bit
      contradiction
    have x : (p.1+10).toNat < 21 := by omega
    have y : p.2.toNat < 11 := by omega
    have a := List.all_eq_true.mp geometricTable p.2.toNat (List.mem_range.mpr y)
    have b := List.all_eq_true.mp a (p.1+10).toNat (List.mem_range.mpr x)
    have c := List.all_eq_true.mp b j (List.mem_range.mpr jbound)
    have xpos : (((p.1+10).toNat : ℤ)-10)=p.1 := by omega
    have ypos : (p.2.toNat : ℤ)=p.2 := by omega
    simpa only [slotCheck,bit,Bool.not_true,Bool.false_or,xpos,ypos,Prod.mk.eta] using c
  next no => simp at bit

end PolyominoSearch

namespace PolyominoSearch

open OMA.S_oeis_a395495 (squareGrid Polyomino)

private theorem neighbors_iff (p q : Cell) : q ∈ neighbors p ↔ squareGrid.Adj p q := by
  obtain ⟨a,b⟩ := p
  obtain ⟨c,d⟩ := q
  change (c,d) ∈ [(a+1,b),(a-1,b),(a,b+1),(a,b-1)] ↔ |a-c|+|b-d|=1
  simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq]
  simp only [abs_eq_max_neg]
  omega

private theorem shifted_neighbors {p q o : Cell} (edge : squareGrid.Adj p q) :
    q-o∈neighbors (p-o) := by
  apply (neighbors_iff _ _).mpr
  change |(p.1-o.1)-(q.1-o.1)|+|(p.2-o.2)-(q.2-o.2)|=1
  change |p.1-q.1|+|p.2-q.2|=1 at edge
  simpa only [sub_sub_sub_cancel_right] using edge

theorem translated_boundary (P : Finset Cell) (connected : Polyomino P) (o : Cell) :
    Boundary (P.image (fun p => p-o)) := by
  intro A existsA sub ne
  by_contra absent
  have closed {u v : ↥P} (adj : (squareGrid.induce (P : Set Cell)).Adj u v)
      (inside : u.val-o∈A) : v.val-o∈A := by
    by_contra outside
    exact absent ⟨u.val-o,inside,v.val-o,Finset.mem_image.mpr ⟨v.val,v.property,rfl⟩,
      outside,shifted_neighbors adj⟩
  have propagate {u v : ↥P} (walk : (squareGrid.induce (P : Set Cell)).Walk u v) :
      u.val-o∈A → v.val-o∈A := by
    induction walk with
    | nil => exact id
    | cons adj rest ih => exact fun hu => ih (closed adj hu)
  obtain ⟨a,ha⟩ := existsA
  obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp (sub ha)
  apply ne
  apply Finset.Subset.antisymm sub
  intro z hz
  obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨walk⟩ := connected.preconnected ⟨s,hs⟩ ⟨t,ht⟩
  exact propagate walk ha

noncomputable def container : Finset Cell :=
  ((Finset.Icc (-5 : ℤ) 5) ×ˢ (Finset.Icc (-5 : ℤ) 5)).filter (fun p => inside p=true)

theorem inside_mem {p : Cell} (hp : inside p=true) : p∈container := by
  have bounds := (of_decide_eq_true hp).1
  have hx : |p.1|≤5 := by have := abs_nonneg p.2; omega
  have hy : |p.2|≤5 := by have := abs_nonneg p.1; omega
  refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_,?_⟩,hp⟩
  · exact Finset.mem_Icc.mpr (abs_le.mp hx)
  · exact Finset.mem_Icc.mpr (abs_le.mp hy)

theorem container_size : container.card=57 := by decide +kernel

private def weight (p : Cell) : ℕ := p.1.natAbs+p.2.natAbs

private theorem descent :
    ∀ p∈container, p≠origin → ∃ q∈neighbors p, q∈container ∧ weight q<weight p := by
  decide +kernel

private theorem center_mem : origin∈container := by decide +kernel

private theorem reachable_center (p : ↥container) :
    (squareGrid.induce (container : Set Cell)).Reachable p ⟨origin,center_mem⟩ := by
  by_cases center : p.val=origin
  · have eq : p=⟨origin,center_mem⟩ := Subtype.ext center
    subst p
    exact .rfl
  · obtain ⟨q,neighbor,member,less⟩ := descent p.val p.property center
    have edge : (squareGrid.induce (container : Set Cell)).Adj p ⟨q,member⟩ :=
      (neighbors_iff _ _).mp neighbor
    exact edge.reachable.trans (reachable_center ⟨q,member⟩)
termination_by weight p.val

theorem container_connected : Polyomino container where
  preconnected p q := (reachable_center p).trans (reachable_center q).symm
  nonempty := ⟨⟨origin,center_mem⟩⟩

end PolyominoSearch

namespace PolyominoSearch

open OMA.S_oeis_a395495 (Polyomino Universal)

theorem universal_of_search (tested : allFit 10=true) : Universal 11 container := by
  refine ⟨container_connected,?_⟩
  intro P card connected
  have nonempty : P.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨a,ha,low⟩ := P.exists_min_image Prod.snd nonempty
  let bottom := P.filter (fun p => p.2=a.2)
  have nonemptyBottom : bottom.Nonempty := ⟨a,Finset.mem_filter.mpr ⟨ha,rfl⟩⟩
  obtain ⟨o,ho,first⟩ := bottom.exists_min_image Prod.fst nonemptyBottom
  obtain ⟨member,level⟩ := Finset.mem_filter.mp ho
  let whole := P.image (fun p => p-o)
  have contains : origin∈whole := by
    exact Finset.mem_image.mpr ⟨o,member,by rw [sub_self]; rfl⟩
  have size : whole.card=10+1 := by
    change (P.image (fun p => p-o)).card=11
    rw [Finset.card_image_of_injective _ (fun _ _ h => sub_left_inj.mp h),card]
  have allowed : ∀ p∈whole, eligible p=true := by
    intro p hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    apply decide_eq_true
    change 0<q.2-o.2 ∨ (q.2-o.2=0 ∧ 0≤q.1-o.1)
    have atLeast := low q hq
    by_cases same : q.2=a.2
    · have hx := first q (Finset.mem_filter.mpr ⟨hq,same⟩)
      change o.1≤q.1 at hx
      exact Or.inr ⟨by omega,by omega⟩
    · change a.2≤q.2 at atLeast
      exact Or.inl (by omega)
  obtain ⟨j,covered⟩ := rooted whole contains 10 size allowed (translated_boundary P connected o) tested
  refine ⟨shift j-o,?_⟩
  intro p memberP
  have translated := inside_mem (fits_of_bit (covered (p-o) (Finset.mem_image.mpr ⟨p,memberP,rfl⟩)))
  have shift_eq : p+(shift j-o)=(p-o)+shift j := by abel
  simpa only [shift_eq] using translated

end PolyominoSearch

namespace PolyominoSearch

/-- Explicit starting states keep each closed kernel computation small. -/
private structure Branch where
  remaining : ℕ
  queue : List Cell
  seen : ℕ
  possible : ℕ

private def project (s : Branch) := check s.remaining s.queue s.seen s.possible

private def choose (s : Branch) : Branch :=
  match s with
  | ⟨n+1,v::tail,seen,possible⟩ =>
      let next := fresh v seen
      ⟨n,next++tail,remember next seen,possible &&& possibilities v⟩
  | x => x

private def discardFront (s : Branch) : Branch :=
  match s with
  | ⟨n+1,_::tail,seen,possible⟩ => ⟨n+1,tail,seen,possible⟩
  | x => x

private theorem splitChecked (s : Branch) (a : project (choose s)=true)
    (b : project (discardFront s)=true) : project s=true := by
  obtain ⟨_ | n,queue,seen,possible⟩ := s
  · exact a
  · cases queue with
    | nil => rfl
    | cons v tail =>
      change (_ && _)=true
      rw [Bool.and_eq_true]
      exact ⟨a,b⟩

private def start : Branch :=
  ⟨10,initial,remember initial (remember [origin] 0),possibilities origin⟩

set_option maxRecDepth 16000 in
private theorem testYYYYYY : project (choose (choose (choose (choose (choose (choose start))))))=true := by decide +kernel

set_option maxRecDepth 16000 in
private theorem testYYYYYN : project (discardFront (choose (choose (choose (choose (choose start))))))=true := by decide +kernel

private theorem testYYYYY : project (choose (choose (choose (choose (choose start)))))=true := splitChecked _ testYYYYYY testYYYYYN

set_option maxRecDepth 16000 in
private theorem testYYYYNY : project (choose (discardFront (choose (choose (choose (choose start))))))=true := by decide +kernel

set_option maxRecDepth 16000 in
private theorem testYYYYNN : project (discardFront (discardFront (choose (choose (choose (choose start))))))=true := by decide +kernel

private theorem testYYYYN : project (discardFront (choose (choose (choose (choose start)))))=true := splitChecked _ testYYYYNY testYYYYNN

private theorem testYYYY : project (choose (choose (choose (choose start))))=true := splitChecked _ testYYYYY testYYYYN

set_option maxRecDepth 16000 in
private theorem testYYYNYY : project (choose (choose (discardFront (choose (choose (choose start))))))=true := by decide +kernel

set_option maxRecDepth 16000 in
private theorem testYYYNYN : project (discardFront (choose (discardFront (choose (choose (choose start))))))=true := by decide +kernel

private theorem testYYYNY : project (choose (discardFront (choose (choose (choose start)))))=true := splitChecked _ testYYYNYY testYYYNYN

set_option maxRecDepth 16000 in
private theorem testYYYNNY : project (choose (discardFront (discardFront (choose (choose (choose start))))))=true := by decide +kernel

set_option maxRecDepth 16000 in
private theorem testYYYNNN : project (discardFront (discardFront (discardFront (choose (choose (choose start))))))=true := by decide +kernel

private theorem testYYYNN : project (discardFront (discardFront (choose (choose (choose start)))))=true := splitChecked _ testYYYNNY testYYYNNN

private theorem testYYYN : project (discardFront (choose (choose (choose start))))=true := splitChecked _ testYYYNY testYYYNN

private theorem testYYY : project (choose (choose (choose start)))=true := splitChecked _ testYYYY testYYYN

set_option maxRecDepth 16000 in
private theorem testYYNYYY : project (choose (choose (choose (discardFront (choose (choose start))))))=true := by decide +kernel

set_option maxRecDepth 16000 in
private theorem testYYNYYN : project (discardFront (choose (choose (discardFront (choose (choose start))))))=true := by decide +kernel

private theorem testYYNYY : project (choose (choose (discardFront (choose (choose start)))))=true := splitChecked _ testYYNYYY testYYNYYN

set_option maxRecDepth 16000 in
private theorem testYYNYNY : project (choose (discardFront (choose (discardFront (choose (choose start))))))=true := by decide +kernel

set_option maxRecDepth 16000 in
private theorem testYYNYNN : project (discardFront (discardFront (choose (discardFront (choose (choose start))))))=true := by decide +kernel

private theorem testYYNYN : project (discardFront (choose (discardFront (choose (choose start)))))=true := splitChecked _ testYYNYNY testYYNYNN

private theorem testYYNY : project (choose (discardFront (choose (choose start))))=true := splitChecked _ testYYNYY testYYNYN

set_option maxRecDepth 16000 in
private theorem testYYNNYY : project (choose (choose (discardFront (discardFront (choose (choose start))))))=true := by decide +kernel

set_option maxRecDepth 16000 in
private theorem testYYNNYN : project (discardFront (choose (discardFront (discardFront (choose (choose start))))))=true := by decide +kernel

private theorem testYYNNY : project (choose (discardFront (discardFront (choose (choose start)))))=true := splitChecked _ testYYNNYY testYYNNYN

set_option maxRecDepth 16000 in
private theorem testYYNNNY : project (choose (discardFront (discardFront (discardFront (choose (choose start))))))=true := by decide +kernel

set_option maxRecDepth 16000 in
private theorem testYYNNNN : project (discardFront (discardFront (discardFront (discardFront (choose (choose start))))))=true := by decide +kernel

private theorem testYYNNN : project (discardFront (discardFront (discardFront (choose (choose start)))))=true := splitChecked _ testYYNNNY testYYNNNN

private theorem testYYNN : project (discardFront (discardFront (choose (choose start))))=true := splitChecked _ testYYNNY testYYNNN

private theorem testYYN : project (discardFront (choose (choose start)))=true := splitChecked _ testYYNY testYYNN

private theorem testYY : project (choose (choose start))=true := splitChecked _ testYYY testYYN

set_option maxRecDepth 16000 in
private theorem testYNYYYY : project (choose (choose (choose (choose (discardFront (choose start))))))=true := by decide +kernel

set_option maxRecDepth 16000 in
private theorem testYNYYYN : project (discardFront (choose (choose (choose (discardFront (choose start))))))=true := by decide +kernel

private theorem testYNYYY : project (choose (choose (choose (discardFront (choose start)))))=true := splitChecked _ testYNYYYY testYNYYYN

set_option maxRecDepth 16000 in
private theorem testYNYYNY : project (choose (discardFront (choose (choose (discardFront (choose start))))))=true := by decide +kernel

set_option maxRecDepth 16000 in
private theorem testYNYYNN : project (discardFront (discardFront (choose (choose (discardFront (choose start))))))=true := by decide +kernel

private theorem testYNYYN : project (discardFront (choose (choose (discardFront (choose start)))))=true := splitChecked _ testYNYYNY testYNYYNN

private theorem testYNYY : project (choose (choose (discardFront (choose start))))=true := splitChecked _ testYNYYY testYNYYN

set_option maxRecDepth 16000 in
private theorem testYNYNYY : project (choose (choose (discardFront (choose (discardFront (choose start))))))=true := by decide +kernel

set_option maxRecDepth 16000 in
private theorem testYNYNYN : project (discardFront (choose (discardFront (choose (discardFront (choose start))))))=true := by decide +kernel

private theorem testYNYNY : project (choose (discardFront (choose (discardFront (choose start)))))=true := splitChecked _ testYNYNYY testYNYNYN

set_option maxRecDepth 16000 in
private theorem testYNYNNY : project (choose (discardFront (discardFront (choose (discardFront (choose start))))))=true := by decide +kernel

set_option maxRecDepth 16000 in
private theorem testYNYNNN : project (discardFront (discardFront (discardFront (choose (discardFront (choose start))))))=true := by decide +kernel

private theorem testYNYNN : project (discardFront (discardFront (choose (discardFront (choose start)))))=true := splitChecked _ testYNYNNY testYNYNNN

private theorem testYNYN : project (discardFront (choose (discardFront (choose start))))=true := splitChecked _ testYNYNY testYNYNN

private theorem testYNY : project (choose (discardFront (choose start)))=true := splitChecked _ testYNYY testYNYN

set_option maxRecDepth 16000 in
private theorem testYNNYYY : project (choose (choose (choose (discardFront (discardFront (choose start))))))=true := by decide +kernel

set_option maxRecDepth 16000 in
private theorem testYNNYYN : project (discardFront (choose (choose (discardFront (discardFront (choose start))))))=true := by decide +kernel

private theorem testYNNYY : project (choose (choose (discardFront (discardFront (choose start)))))=true := splitChecked _ testYNNYYY testYNNYYN

set_option maxRecDepth 16000 in
private theorem testYNNYNY : project (choose (discardFront (choose (discardFront (discardFront (choose start))))))=true := by decide +kernel

set_option maxRecDepth 16000 in
private theorem testYNNYNN : project (discardFront (discardFront (choose (discardFront (discardFront (choose start))))))=true := by decide +kernel

private theorem testYNNYN : project (discardFront (choose (discardFront (discardFront (choose start)))))=true := splitChecked _ testYNNYNY testYNNYNN

private theorem testYNNY : project (choose (discardFront (discardFront (choose start))))=true := splitChecked _ testYNNYY testYNNYN

set_option maxRecDepth 16000 in
private theorem testYNNNYY : project (choose (choose (discardFront (discardFront (discardFront (choose start))))))=true := by decide +kernel

set_option maxRecDepth 16000 in
private theorem testYNNNYN : project (discardFront (choose (discardFront (discardFront (discardFront (choose start))))))=true := by decide +kernel

private theorem testYNNNY : project (choose (discardFront (discardFront (discardFront (choose start)))))=true := splitChecked _ testYNNNYY testYNNNYN

set_option maxRecDepth 16000 in
private theorem testYNNNNY : project (choose (discardFront (discardFront (discardFront (discardFront (choose start))))))=true := by decide +kernel

set_option maxRecDepth 16000 in
private theorem testYNNNNN : project (discardFront (discardFront (discardFront (discardFront (discardFront (choose start))))))=true := by decide +kernel

private theorem testYNNNN : project (discardFront (discardFront (discardFront (discardFront (choose start)))))=true := splitChecked _ testYNNNNY testYNNNNN

private theorem testYNNN : project (discardFront (discardFront (discardFront (choose start))))=true := splitChecked _ testYNNNY testYNNNN

private theorem testYNN : project (discardFront (discardFront (choose start)))=true := splitChecked _ testYNNY testYNNN

private theorem testYN : project (discardFront (choose start))=true := splitChecked _ testYNY testYNN

private theorem testY : project (choose start)=true := splitChecked _ testYY testYN

set_option maxRecDepth 16000 in
private theorem testNYYYYY : project (choose (choose (choose (choose (choose (discardFront start))))))=true := by decide +kernel

set_option maxRecDepth 16000 in
private theorem testNYYYYN : project (discardFront (choose (choose (choose (choose (discardFront start))))))=true := by decide +kernel

private theorem testNYYYY : project (choose (choose (choose (choose (discardFront start)))))=true := splitChecked _ testNYYYYY testNYYYYN

set_option maxRecDepth 16000 in
private theorem testNYYYNY : project (choose (discardFront (choose (choose (choose (discardFront start))))))=true := by decide +kernel

set_option maxRecDepth 16000 in
private theorem testNYYYNN : project (discardFront (discardFront (choose (choose (choose (discardFront start))))))=true := by decide +kernel

private theorem testNYYYN : project (discardFront (choose (choose (choose (discardFront start)))))=true := splitChecked _ testNYYYNY testNYYYNN

private theorem testNYYY : project (choose (choose (choose (discardFront start))))=true := splitChecked _ testNYYYY testNYYYN

set_option maxRecDepth 16000 in
private theorem testNYYNYY : project (choose (choose (discardFront (choose (choose (discardFront start))))))=true := by decide +kernel

set_option maxRecDepth 16000 in
private theorem testNYYNYN : project (discardFront (choose (discardFront (choose (choose (discardFront start))))))=true := by decide +kernel

private theorem testNYYNY : project (choose (discardFront (choose (choose (discardFront start)))))=true := splitChecked _ testNYYNYY testNYYNYN

set_option maxRecDepth 16000 in
private theorem testNYYNNY : project (choose (discardFront (discardFront (choose (choose (discardFront start))))))=true := by decide +kernel

set_option maxRecDepth 16000 in
private theorem testNYYNNN : project (discardFront (discardFront (discardFront (choose (choose (discardFront start))))))=true := by decide +kernel

private theorem testNYYNN : project (discardFront (discardFront (choose (choose (discardFront start)))))=true := splitChecked _ testNYYNNY testNYYNNN

private theorem testNYYN : project (discardFront (choose (choose (discardFront start))))=true := splitChecked _ testNYYNY testNYYNN

private theorem testNYY : project (choose (choose (discardFront start)))=true := splitChecked _ testNYYY testNYYN

set_option maxRecDepth 16000 in
private theorem testNYNYYY : project (choose (choose (choose (discardFront (choose (discardFront start))))))=true := by decide +kernel

set_option maxRecDepth 16000 in
private theorem testNYNYYN : project (discardFront (choose (choose (discardFront (choose (discardFront start))))))=true := by decide +kernel

private theorem testNYNYY : project (choose (choose (discardFront (choose (discardFront start)))))=true := splitChecked _ testNYNYYY testNYNYYN

set_option maxRecDepth 16000 in
private theorem testNYNYNY : project (choose (discardFront (choose (discardFront (choose (discardFront start))))))=true := by decide +kernel

set_option maxRecDepth 16000 in
private theorem testNYNYNN : project (discardFront (discardFront (choose (discardFront (choose (discardFront start))))))=true := by decide +kernel

private theorem testNYNYN : project (discardFront (choose (discardFront (choose (discardFront start)))))=true := splitChecked _ testNYNYNY testNYNYNN

private theorem testNYNY : project (choose (discardFront (choose (discardFront start))))=true := splitChecked _ testNYNYY testNYNYN

set_option maxRecDepth 16000 in
private theorem testNYNNYY : project (choose (choose (discardFront (discardFront (choose (discardFront start))))))=true := by decide +kernel

set_option maxRecDepth 16000 in
private theorem testNYNNYN : project (discardFront (choose (discardFront (discardFront (choose (discardFront start))))))=true := by decide +kernel

private theorem testNYNNY : project (choose (discardFront (discardFront (choose (discardFront start)))))=true := splitChecked _ testNYNNYY testNYNNYN

set_option maxRecDepth 16000 in
private theorem testNYNNNY : project (choose (discardFront (discardFront (discardFront (choose (discardFront start))))))=true := by decide +kernel

set_option maxRecDepth 16000 in
private theorem testNYNNNN : project (discardFront (discardFront (discardFront (discardFront (choose (discardFront start))))))=true := by decide +kernel

private theorem testNYNNN : project (discardFront (discardFront (discardFront (choose (discardFront start)))))=true := splitChecked _ testNYNNNY testNYNNNN

private theorem testNYNN : project (discardFront (discardFront (choose (discardFront start))))=true := splitChecked _ testNYNNY testNYNNN

private theorem testNYN : project (discardFront (choose (discardFront start)))=true := splitChecked _ testNYNY testNYNN

private theorem testNY : project (choose (discardFront start))=true := splitChecked _ testNYY testNYN

set_option maxRecDepth 16000 in
private theorem testNNYYYY : project (choose (choose (choose (choose (discardFront (discardFront start))))))=true := by decide +kernel

set_option maxRecDepth 16000 in
private theorem testNNYYYN : project (discardFront (choose (choose (choose (discardFront (discardFront start))))))=true := by decide +kernel

private theorem testNNYYY : project (choose (choose (choose (discardFront (discardFront start)))))=true := splitChecked _ testNNYYYY testNNYYYN

set_option maxRecDepth 16000 in
private theorem testNNYYNY : project (choose (discardFront (choose (choose (discardFront (discardFront start))))))=true := by decide +kernel

set_option maxRecDepth 16000 in
private theorem testNNYYNN : project (discardFront (discardFront (choose (choose (discardFront (discardFront start))))))=true := by decide +kernel

private theorem testNNYYN : project (discardFront (choose (choose (discardFront (discardFront start)))))=true := splitChecked _ testNNYYNY testNNYYNN

private theorem testNNYY : project (choose (choose (discardFront (discardFront start))))=true := splitChecked _ testNNYYY testNNYYN

set_option maxRecDepth 16000 in
private theorem testNNYNYY : project (choose (choose (discardFront (choose (discardFront (discardFront start))))))=true := by decide +kernel

set_option maxRecDepth 16000 in
private theorem testNNYNYN : project (discardFront (choose (discardFront (choose (discardFront (discardFront start))))))=true := by decide +kernel

private theorem testNNYNY : project (choose (discardFront (choose (discardFront (discardFront start)))))=true := splitChecked _ testNNYNYY testNNYNYN

set_option maxRecDepth 16000 in
private theorem testNNYNNY : project (choose (discardFront (discardFront (choose (discardFront (discardFront start))))))=true := by decide +kernel

set_option maxRecDepth 16000 in
private theorem testNNYNNN : project (discardFront (discardFront (discardFront (choose (discardFront (discardFront start))))))=true := by decide +kernel

private theorem testNNYNN : project (discardFront (discardFront (choose (discardFront (discardFront start)))))=true := splitChecked _ testNNYNNY testNNYNNN

private theorem testNNYN : project (discardFront (choose (discardFront (discardFront start))))=true := splitChecked _ testNNYNY testNNYNN

private theorem testNNY : project (choose (discardFront (discardFront start)))=true := splitChecked _ testNNYY testNNYN

set_option maxRecDepth 16000 in
private theorem testNNNYYY : project (choose (choose (choose (discardFront (discardFront (discardFront start))))))=true := by decide +kernel

set_option maxRecDepth 16000 in
private theorem testNNNYYN : project (discardFront (choose (choose (discardFront (discardFront (discardFront start))))))=true := by decide +kernel

private theorem testNNNYY : project (choose (choose (discardFront (discardFront (discardFront start)))))=true := splitChecked _ testNNNYYY testNNNYYN

set_option maxRecDepth 16000 in
private theorem testNNNYNY : project (choose (discardFront (choose (discardFront (discardFront (discardFront start))))))=true := by decide +kernel

set_option maxRecDepth 16000 in
private theorem testNNNYNN : project (discardFront (discardFront (choose (discardFront (discardFront (discardFront start))))))=true := by decide +kernel

private theorem testNNNYN : project (discardFront (choose (discardFront (discardFront (discardFront start)))))=true := splitChecked _ testNNNYNY testNNNYNN

private theorem testNNNY : project (choose (discardFront (discardFront (discardFront start))))=true := splitChecked _ testNNNYY testNNNYN

set_option maxRecDepth 16000 in
private theorem testNNNNYY : project (choose (choose (discardFront (discardFront (discardFront (discardFront start))))))=true := by decide +kernel

set_option maxRecDepth 16000 in
private theorem testNNNNYN : project (discardFront (choose (discardFront (discardFront (discardFront (discardFront start))))))=true := by decide +kernel

private theorem testNNNNY : project (choose (discardFront (discardFront (discardFront (discardFront start)))))=true := splitChecked _ testNNNNYY testNNNNYN

set_option maxRecDepth 16000 in
private theorem testNNNNNY : project (choose (discardFront (discardFront (discardFront (discardFront (discardFront start))))))=true := by decide +kernel

set_option maxRecDepth 16000 in
private theorem testNNNNNN : project (discardFront (discardFront (discardFront (discardFront (discardFront (discardFront start))))))=true := by decide +kernel

private theorem testNNNNN : project (discardFront (discardFront (discardFront (discardFront (discardFront start)))))=true := splitChecked _ testNNNNNY testNNNNNN

private theorem testNNNN : project (discardFront (discardFront (discardFront (discardFront start))))=true := splitChecked _ testNNNNY testNNNNN

private theorem testNNN : project (discardFront (discardFront (discardFront start)))=true := splitChecked _ testNNNY testNNNN

private theorem testNN : project (discardFront (discardFront start))=true := splitChecked _ testNNY testNNN

private theorem testN : project (discardFront start)=true := splitChecked _ testNY testNN

private theorem test : project start=true := splitChecked _ testY testN

theorem allElevenFit : allFit 10=true := test

end PolyominoSearch

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a395495.main) := by
  intro proposed
  have lower := (proposed 11 (by decide)).2
    (show 57 ∈ {k : ℕ | ∃ C : Finset OMA.S_oeis_a395495.Cell,
      OMA.S_oeis_a395495.Universal 11 C ∧ C.card=k} from
      ⟨PolyominoSearch.container,PolyominoSearch.universal_of_search
        PolyominoSearch.allElevenFit,PolyominoSearch.container_size⟩)
  norm_num at lower
