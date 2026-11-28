import OMAReductions.R_Erdos28_erdos_28_R1_H1_R1

/-!
# Six ordered representations are forced by the endpoint 70

Every subset of the natural numbers covering 0 through 70 by sums of two
members has an integer in that interval with at least six ordered representations.
The included witness covers the interval through 69 with a maximum of five.
Grekos, Haddad, Helou and Pihko published the endpoint in J. Number Theory 102
(2003), section 6.4. TheWaler independently enumerated it on the worksheet.
This file contributes a kernel-checked finite proof and a witness at 69.
Credit for the Lean formalization and independent search: @anmolspace.

At each position the search considers including or excluding that position.
An uncovered sum at the current position cannot be repaired by larger terms.
The inclusion test extracts six distinct first coordinates and checks their
reflected partners. Each surviving choice is explored through the endpoint.
-/


namespace OMA.Erdos28Five

private def pick (v : Nat) : Nat := ((0x14293caa19f60aca4480811b172b07150b15341248462414c9a3a00b5b0f0059e0633180273b097937e89c0d089488b12cc03500ecc0038b9f370640400005cdbd041c01a0200000 : Nat) >>> (7*((v ^^^ (v-1))%83)))%128

private def gather : Nat → Nat → Bool
  | 0, _ => true
  | k+1, v =>
    let p := pick v
    v.testBit p && gather k (v ^^^ (1 <<< p))

private theorem singleBit (i j : Nat) : (1 <<< i : Nat).testBit j = decide (i=j) := by
  rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow]

private theorem gather_sound {k v : Nat} (h : gather k v = true) :
    ∃ l : List Nat, l.length=k ∧ l.Nodup ∧ ∀ i ∈ l, v.testBit i=true := by
  induction k generalizing v with
  | zero => exact ⟨[],rfl,List.nodup_nil,by simp⟩
  | succ k ih =>
    let p := pick v
    obtain ⟨hp,hr⟩ := Bool.and_eq_true_iff.mp h
    change v.testBit p = true at hp
    obtain ⟨l,hl,hd,hs⟩ := ih hr
    have ne (i : Nat) (hi : i ∈ l) : p ≠ i := by
      rintro rfl
      have hz := hs _ hi
      simp [Nat.testBit_xor, singleBit, hp, p] at hz
    refine ⟨p::l, by simp [hl], List.nodup_cons.mpr ⟨fun z => ne _ z rfl, hd⟩, ?_⟩
    intro i hi
    rcases List.mem_cons.mp hi with rfl|hi
    · exact hp
    · have hz := hs _ hi
      rw [Nat.testBit_xor, singleBit] at hz
      simpa only [show decide (pick v=i)=false from decide_eq_false (ne i hi), Bool.xor_false] using hz

private structure State where
  pos : Nat
  rev : Nat
  one : Nat
  two : Nat
  deriving DecidableEq

private def add (s : State) (x : Nat) : State :=
  let t := s.pos <<< x
  ⟨s.pos ||| (1 <<< x), s.rev ||| (1 <<< (70-x)),
   s.one ||| t, s.two ||| (s.one &&& t)⟩

private def pairs (s : State) (n : Nat) := s.pos &&& (s.rev >>> (70-n))

private def crowded (s : State) (n : Nat) : Bool :=
  decide (n ≤ 70) && gather 6 (pairs s n)

private def includeStops (s : State) (x : Nat) : Bool :=
  let bad := ((s.pos <<< x) &&& s.two) &&& (2^71-1)
  bad != 0 && crowded (add s x) (pick bad)

/-- Six distinct first coordinates of ordered representations of one sum. -/
def Six (A : Nat → Prop) : Prop :=
  ∃ n ≤ 70, ∃ l : List Nat, l.length = 6 ∧ l.Nodup ∧
    ∀ a ∈ l, ∃ b, A a ∧ A b ∧ a+b=n

private structure Fits (A : Nat → Prop) (x : Nat) (s : State) : Prop where
  complete : ∀ a < x, A a → s.pos.testBit a = true ∧ s.rev.testBit (70-a) = true
  forward : ∀ a, s.pos.testBit a = true → A a
  backward : ∀ i, s.rev.testBit i = true → ∃ b ≤ 70, A b ∧ i = 70-b

private theorem skipFits {A x s} (h : Fits A x s) (hn : ¬A x) : Fits A (x+1) s := by
  refine ⟨?_,h.forward,h.backward⟩
  intro a ha hA
  exact h.complete a (by by_cases z : a=x; exact False.elim (hn (z ▸ hA)); omega) hA

private theorem addFits {A x s} (h : Fits A x s) (hx : x ≤ 70) (ha : A x) :
    Fits A (x+1) (add s x) := by
  refine ⟨?_,?_,?_⟩
  · intro a hv hA
    by_cases hz : a=x
    · subst a
      simp [add,Nat.testBit_or,singleBit]
    · obtain ⟨hp,hr⟩ := h.complete a (by omega) hA
      simp [add,Nat.testBit_or,hp,hr]
  · intro a hb
    simp only [add,Nat.testBit_or,Bool.or_eq_true_iff,singleBit,decide_eq_true_eq] at hb
    rcases hb with hi|rfl
    · exact h.forward _ hi
    · exact ha
  · intro i hb
    simp only [add,Nat.testBit_or,Bool.or_eq_true_iff,singleBit,decide_eq_true_eq] at hb
    rcases hb with hi|rfl
    · exact h.backward _ hi
    · exact ⟨x,hx,ha,rfl⟩

private theorem pairSound {A x s n a} (h : Fits A x s) (hn : n ≤ 70)
    (ha : (pairs s n).testBit a = true) : ∃ b, A a ∧ A b ∧ a+b=n := by
  simp only [pairs,Nat.testBit_and,Nat.testBit_shiftRight,Bool.and_eq_true_iff] at ha
  obtain ⟨b,hb,hA,he⟩ := h.backward _ ha.2
  exact ⟨b,h.forward _ ha.1,hA,by omega⟩

private theorem crowdedSound {A x s n} (h : Fits A x s) (hc : crowded s n = true) : Six A := by
  obtain ⟨hn, hg⟩ := Bool.and_eq_true_iff.mp hc
  have hn' : n ≤ 70 := of_decide_eq_true hn
  obtain ⟨l,hl,hd,hs⟩ := gather_sound hg
  exact ⟨n,hn',l,hl,hd,fun a ha => pairSound h hn' (hs a ha)⟩

private def Covers (A : Nat → Prop) := ∀ n ≤ 70, ∃ a b, A a ∧ A b ∧ a+b=n

private theorem cannotSkip {A x s} (h : Fits A x s) (hx : x ≤ 70) (cov : Covers A)
    (hn : ¬A x) (hz : pairs s x = 0) : False := by
  obtain ⟨a,b,ha,hb,hs⟩ := cov x hx
  have h₁ : a < x := by by_cases e : a=x; exact False.elim (hn (e ▸ ha)); omega
  have h₂ : b < x := by by_cases e : b=x; exact False.elim (hn (e ▸ hb)); omega
  have hp := (h.complete a h₁ ha).1
  have hr := (h.complete b h₂ hb).2
  have he : (70-x)+a=70-b := by omega
  have : (pairs s x).testBit a = true := by simp [pairs,Nat.testBit_shiftRight,he,hp,hr]
  simp [hz] at this

private def check : Nat → Nat → State → Bool
  | 0, _, _ => false
  | k+1, x, s =>
    (includeStops s x || check k (x+1) (add s x)) &&
    (pairs s x == 0 || check k (x+1) s)

private theorem check_sound {A : Nat → Prop} (cov : Covers A) (k x : Nat) (s : State)
    (bound : k+x ≤ 71) (h : Fits A x s) (hc : check k x s = true) : Six A := by
  induction k generalizing x s with
  | zero => contradiction
  | succ k ih =>
    have hx : x ≤ 70 := by omega
    have hh := Bool.and_eq_true_iff.mp hc
    by_cases ha : A x
    · rcases Bool.or_eq_true_iff.mp hh.1 with hp|hr
      · exact crowdedSound (addFits h hx ha) (Bool.and_eq_true_iff.mp hp).2
      · exact ih (x+1) _ (by omega) (addFits h hx ha) hr
    · rcases Bool.or_eq_true_iff.mp hh.2 with hp|hr
      · exact False.elim (cannotSkip h hx cov ha (beq_iff_eq.mp hp))
      · exact ih (x+1) _ (by omega) (skipFits h ha) hr

private def zero : State := ⟨0,0,0,0⟩

set_option maxHeartbeats 0 in
private theorem checked : check 71 0 zero = true := by decide +kernel

theorem six_of_cover (A : Nat → Prop) (h : ∀ n ≤ 70, ∃ a b, A a ∧ A b ∧ a+b=n) : Six A := by
  apply check_sound h 71 0 zero (by decide) _ checked
  exact ⟨by simp,by simp [zero],by simp [zero]⟩

end OMA.Erdos28Five

namespace OMA.Erdos28Five

theorem five_lt_count (S : Finset Nat)
    (cov : ∀ n ≤ 70, ∃ a ∈ S, ∃ b ∈ S, a+b=n) :
    ∃ n ≤ 70, 5 < ((Finset.HasAntidiagonal.antidiagonal n).filter (fun p => p.1 ∈ S ∧ p.2 ∈ S)).card := by
  obtain ⟨n,hn,l,hl,hd,hw⟩ := six_of_cover (fun a => a ∈ S) (by
    intro n hn
    obtain ⟨a,ha,b,hb,he⟩ := cov n hn
    exact ⟨a,b,ha,hb,he⟩)
  let f : Nat → Nat × Nat := fun a => (a,n-a)
  have fi : Function.Injective f := fun _ _ h => congrArg Prod.fst h
  have card := Finset.card_image_of_injective l.toFinset fi
  rw [List.toFinset_card_of_nodup hd, hl] at card
  have sub : l.toFinset.image f ⊆ (Finset.HasAntidiagonal.antidiagonal n).filter (fun p => p.1 ∈ S ∧ p.2 ∈ S) := by
    intro p hp
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨b, h₁, h₂, he⟩ := hw a (List.mem_toFinset.mp ha)
    have hb : n-a=b := by omega
    exact Finset.mem_filter.mpr ⟨Finset.HasAntidiagonal.mem_antidiagonal.mpr (by change a+(n-a)=n; omega),
      h₁, by change n-a ∈ S; simpa only [hb] using h₂⟩
  have hb := Finset.card_le_card sub
  exact ⟨n,hn,by omega⟩

end OMA.Erdos28Five

namespace OMA.Erdos28Endpoint

/-- A cover of 0 through 69 with at most five ordered representations per sum. -/
def lastCover : Finset ℕ :=
  {0, 1, 3, 4, 5, 6, 10, 15, 17, 23, 31, 39, 47, 55, 63}

def countAt (n : ℕ) : ℕ :=
  ((Finset.HasAntidiagonal.antidiagonal n).filter (fun p => p.1 ∈ lastCover ∧ p.2 ∈ lastCover)).card

set_option maxRecDepth 8000 in
set_option maxHeartbeats 9000000 in
theorem last_counts : ∀ n : Fin 70, 0 < countAt n ∧ countAt n ≤ 5 := by
  decide

theorem last_subset : lastCover ⊆ Finset.Iic 69 := by decide

theorem last_covers (n : ℕ) (hn : n ≤ 69) :
    ∃ a ∈ lastCover, ∃ b ∈ lastCover, a+b=n := by
  have h := (last_counts ⟨n, by omega⟩).1
  change 0 < ((Finset.HasAntidiagonal.antidiagonal n).filter
    (fun p => p.1 ∈ lastCover ∧ p.2 ∈ lastCover)).card at h
  obtain ⟨p,hp⟩ := Finset.card_pos.mp h
  obtain ⟨hs, ha, hb⟩ := Finset.mem_filter.mp hp
  exact ⟨p.1, ha, p.2, hb, Finset.HasAntidiagonal.mem_antidiagonal.mp hs⟩

end OMA.Erdos28Endpoint


theorem OMA.solution : OMA.R_Erdos28_erdos_28_R1_H1_R1.H1 := by
  classical
  intro S _ cov
  obtain ⟨n,hn,hs⟩ := OMA.Erdos28Five.five_lt_count S cov
  exact ⟨n,hn,by simpa only [AdditiveCombinatorics.sumRep_def, Finset.mem_coe] using hs⟩
