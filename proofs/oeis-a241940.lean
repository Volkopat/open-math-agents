import OMAStatements.S_oeis_a241940
import Mathlib

/-!
# Window sums in Hardin's eight-entry arrays

R. H. Hardin proposed the counting problem A241940 and gave an empirical
polynomial. Colin Barker conjectured the generating function and finite
difference recurrence in October 2018. Source: https://oeis.org/A241940.

Prefix sums turn the five-term inequalities into comparisons across two
positions. At scale n the order type of their remainders modulo n, together
with their integer quotients, records every required comparison. Choosing
the distinct positive remainders gives a polynomial in the binomial basis.
A certified split of the array at its four middle entries supplies the nine
initial values, which determine that polynomial and both conjectures.
-/

namespace Window241

open OMA.S_oeis_a241940
open scoped Classical

def leftIndex (j : Fin 4) : Fin 9 := ⟨j.val, by omega⟩
def rightIndex (j : Fin 4) : Fin 9 := ⟨j.val+5, by omega⟩

def allowed (q : Fin 9 → Fin 9) (leR : Fin 9 → Fin 9 → Prop) : Prop :=
  let cmp (i j : Fin 9) (c : ℕ) :=
    (q i).val < (q j).val + c ∨ ((q i).val = (q j).val + c ∧ leR i j)
  (q 0).val = 0 ∧
    (∀ i : Fin 8, cmp i.castSucc i.succ 0 ∧ cmp i.succ i.castSucc 1) ∧
    (∀ j : Fin 4, cmp (rightIndex j) (leftIndex j) 2)

private def prefixSum {n : ℕ} (x : Fin 8 → Fin (n+1)) (k : ℕ) : ℕ :=
  ∑ j ∈ Finset.range k, get x j

private theorem prefix_step {n : ℕ} (x : Fin 8 → Fin (n+1)) (i : Fin 8) :
    prefixSum x (i.val+1) = prefixSum x i.val + (x i).val := by
  simp [prefixSum, Finset.sum_range_succ, OMA.S_oeis_a241940.get, i.isLt]

private theorem prefix_window {n : ℕ} (x : Fin 8 → Fin (n+1)) (j : ℕ) :
    prefixSum x (j+5) = prefixSum x j + ∑ t ∈ Finset.range 5, get x (j+t) := by
  simp [prefixSum, Finset.sum_range_add]

private theorem prefix_le {n : ℕ} (x : Fin 8 → Fin (n+1)) (i : Fin 9) :
    prefixSum x i.val ≤ 8*n := by
  calc
    _ ≤ ∑ _j ∈ Finset.range i.val, n := by
      apply Finset.sum_le_sum
      intro j hj
      simp only [OMA.S_oeis_a241940.get]
      split
      · exact Nat.le_of_lt_succ (x _).isLt
      · exact Nat.zero_le _
    _ = i.val*n := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ (by omega)

private def bounds (n : ℕ) (S : Fin 9 → ℕ) : Prop :=
  S 0 = 0 ∧
    (∀ i : Fin 8, S i.castSucc ≤ S i.succ ∧ S i.succ ≤ S i.castSucc + n) ∧
    (∀ j : Fin 4, S (rightIndex j) ≤ S (leftIndex j) + 2*n)

private theorem prefix_bounds {n : ℕ} (x : Fin 8 → Fin (n+1)) :
    good x = true ↔ bounds n (fun i => prefixSum x i.val) := by
  simp only [good, decide_eq_true_eq, bounds, Fin.val_zero, Fin.val_castSucc,
    Fin.val_succ, leftIndex, rightIndex]
  constructor
  · intro h
    refine ⟨by simp [prefixSum], ?_, ?_⟩
    · intro i
      rw [prefix_step]
      have := (x i).isLt
      omega
    · intro j
      rw [prefix_window]
      exact Nat.add_le_add_left (h j.val j.isLt) _
  · rintro ⟨_, _, h⟩ j hj
    have hh := h ⟨j,hj⟩
    change prefixSum x (j+5) ≤ prefixSum x j+2*n at hh
    rw [prefix_window] at hh
    omega

private theorem digits_le {n a b u v : ℕ} (hu : u < n) (hv : v < n) :
    n*a + u ≤ n*b + v ↔ a < b ∨ (a=b ∧ u≤v) := by
  constructor
  · intro h
    rcases lt_trichotomy a b with ha|ha|ha
    · exact Or.inl ha
    · subst b
      exact Or.inr ⟨rfl, by omega⟩
    · have hh := Nat.mul_le_mul_left n (Nat.succ_le_iff.mpr ha)
      rw [Nat.mul_succ] at hh
      omega
  · rintro (ha | ⟨rfl, hv'⟩)
    · have hh := Nat.mul_le_mul_left n (Nat.succ_le_iff.mpr ha)
      rw [Nat.mul_succ] at hh
      omega
    · omega

private def height {n : ℕ} (q : Fin 9 → Fin 9) (r : Fin 9 → Fin n) (i : Fin 9) : ℕ :=
  n*(q i).val+(r i).val

private theorem height_cmp {n : ℕ} (q : Fin 9 → Fin 9) (r : Fin 9 → Fin n)
    (i j : Fin 9) (c : ℕ) :
    height q r i ≤ height q r j + c*n ↔
      (q i).val < (q j).val+c ∨ ((q i).val=(q j).val+c ∧ r i ≤ r j) := by
  unfold height
  rw [show n*(q j).val+(r j).val+c*n=n*((q j).val+c)+(r j).val by ring]
  exact digits_le (r i).isLt (r j).isLt

private theorem height_bounds {n : ℕ} (hn : 0<n) (q : Fin 9 → Fin 9) (r : Fin 9 → Fin n) :
    bounds n (height q r) ↔ (r 0).val=0 ∧ allowed q (fun i j => r i ≤ r j) := by
  have h0 : height q r 0 = 0 ↔ (r 0).val = 0 ∧ (q 0).val = 0 := by
    simp [height, Nat.add_eq_zero_iff, hn.ne', and_comm]
  have hcmp0 (i : Fin 8) := height_cmp q r i.castSucc i.succ 0
  have hcmp1 (i : Fin 8) := height_cmp q r i.succ i.castSucc 1
  simp only [Nat.zero_mul,Nat.add_zero] at hcmp0
  simp only [Nat.one_mul] at hcmp1
  unfold bounds allowed
  simp only [h0, hcmp0, hcmp1, height_cmp, Nat.add_zero]
  tauto

private def quotient {n : ℕ} (hn : 0<n) (x : Fin 8 → Fin (n+1)) (i : Fin 9) : Fin 9 :=
  ⟨prefixSum x i.val / n, (Nat.div_lt_iff_lt_mul hn).mpr
    (lt_of_le_of_lt (prefix_le x i) (by omega))⟩

private def remainder {n : ℕ} (hn : 0<n) (x : Fin 8 → Fin (n+1)) (i : Fin 9) : Fin n :=
  ⟨prefixSum x i.val % n, Nat.mod_lt _ hn⟩

private theorem height_digits {n : ℕ} (hn : 0<n) (x : Fin 8 → Fin (n+1)) :
    height (quotient hn x) (remainder hn x) = fun i => prefixSum x i.val := by
  funext i
  exact Nat.div_add_mod _ _

private def increments {n : ℕ} (S : Fin 9 → ℕ) (h : bounds n S) (i : Fin 8) : Fin (n+1) :=
  ⟨S i.succ - S i.castSucc, by have := (h.2.1 i).2; omega⟩

private theorem prefix_increments {n : ℕ} (S : Fin 9 → ℕ) (h : bounds n S) :
    (fun i : Fin 9 => prefixSum (increments S h) i.val) = S := by
  funext i
  induction i using Fin.induction with
  | zero => simpa [prefixSum] using h.1.symm
  | succ j ih =>
    change prefixSum _ (j.val+1) = _
    rw [prefix_step]
    change prefixSum _ j.val = S j.castSucc at ih
    rw [ih]
    change S j.castSucc + (S j.succ-S j.castSucc) = S j.succ
    have := (h.2.1 j).1
    omega

private noncomputable def prefixEquiv {n : ℕ} (hn : 0<n) :
    {x : Fin 8 → Fin (n+1) // good x = true} ≃
      {qr : (Fin 9 → Fin 9) × (Fin 9 → Fin n) //
        (qr.2 0).val = 0 ∧ allowed qr.1 (fun i j => qr.2 i ≤ qr.2 j)} := by
  let f (x : {x : Fin 8 → Fin (n+1) // good x = true}) :
      {qr : (Fin 9 → Fin 9) × (Fin 9 → Fin n) //
        (qr.2 0).val = 0 ∧ allowed qr.1 (fun i j => qr.2 i ≤ qr.2 j)} :=
    ⟨(quotient hn x.val,remainder hn x.val), (height_bounds hn _ _).mp
      (by rw [height_digits]; exact (prefix_bounds _).mp x.property)⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro x y e
    have he := congrArg (fun z => height z.val.1 z.val.2) e
    change height (quotient hn x.val) (remainder hn x.val) =
      height (quotient hn y.val) (remainder hn y.val) at he
    rw [height_digits, height_digits] at he
    apply Subtype.ext
    funext i
    apply Fin.ext
    have h1 := congrFun he i.succ
    have h0 := congrFun he i.castSucc
    change prefixSum x.val (i.val+1) = prefixSum y.val (i.val+1) at h1
    change prefixSum x.val i.val = prefixSum y.val i.val at h0
    rw [prefix_step, prefix_step, h0] at h1
    omega
  · rintro ⟨⟨q,r⟩,h⟩
    have hb := (height_bounds hn q r).mpr h
    let x := increments (height q r) hb
    have he : (fun i : Fin 9 => prefixSum x i.val) = height q r := prefix_increments _ _
    have hx : good x = true := (prefix_bounds _).mpr (he.symm ▸ hb)
    refine ⟨⟨x,hx⟩, Subtype.ext (Prod.ext ?_ ?_)⟩
    · funext i
      apply Fin.ext
      change prefixSum x i.val / n = (q i).val
      rw [show prefixSum x i.val = height q r i from congrFun he i]
      simp [height, Nat.mul_add_div hn, Nat.div_eq_of_lt (r i).isLt]
    · funext i
      apply Fin.ext
      change prefixSum x i.val % n = (r i).val
      rw [show prefixSum x i.val = height q r i from congrFun he i]
      simp [height,Nat.mod_eq_of_lt (r i).isLt]

theorem prefix_count (n : ℕ) (hn : 0<n) :
    OMA.S_oeis_a241940.a n =
      (Fintype.card {qr : (Fin 9 → Fin 9) × (Fin 9 → Fin n) //
        (qr.2 0).val=0 ∧ allowed qr.1 (fun i j => qr.2 i ≤ qr.2 j)} : ℤ) := by
  have h := Fintype.card_congr (prefixEquiv hn)
  simpa [a,Fintype.card_subtype] using (congrArg (fun k : ℕ => (k : ℤ)) h)

end Window241

namespace Window241
open Finset
open scoped Classical

/-- A pair consisting of a state and a zero-based residue word can be standardized
by replacing each used positive residue with its rank. Each set of positive residues
of the prescribed size contributes exactly the same number of words. -/
theorem levels_count {Q : Type*} [Fintype Q] (P : Q → (Fin 9 → Fin 9 → Prop) → Prop) :
    ∃ c : ℕ → ℕ, ∀ n : ℕ,
      Fintype.card {v : Q × (Fin 9 → Fin (n+1)) //
        (v.2 0).val = 0 ∧ P v.1 (fun i j => v.2 i ≤ v.2 j)} =
      ∑ d ∈ range 9, c d * n.choose d := by
  classical
  let valid (n : ℕ) (v : Q × (Fin 9 → Fin (n+1))) :=
    (v.2 0).val = 0 ∧ P v.1 (fun i j => v.2 i ≤ v.2 j)
  let norm (d : ℕ) := (univ : Finset (Q × (Fin 9 → Fin (d+1)))).filter
    fun v => valid d v ∧ Function.Surjective v.2
  refine ⟨fun d => (norm d).card, fun n => ?_⟩
  let A := (univ : Finset (Q × (Fin 9 → Fin (n+1)))).filter (valid n)
  let U := (univ : Finset (Fin (n+1))).erase 0
  let L := U.powerset.filter (fun s => s.card < 9)
  let support (v : Q × (Fin 9 → Fin (n+1))) := (univ.image v.2).erase 0
  have maps : (A : Set _) |>.MapsTo support L := by
    intro v hv
    have h0 : v.2 0 = 0 := Fin.ext (mem_filter.mp hv).2.1
    have hm : 0 ∈ univ.image v.2 := mem_image.mpr ⟨0,mem_univ _,h0⟩
    have hc : (univ.image v.2).card ≤ 9 := (card_image_le).trans_eq (by simp)
    have he := card_erase_add_one hm
    exact mem_filter.mpr ⟨mem_powerset.mpr (fun i hi => mem_erase.mpr ⟨(mem_erase.mp hi).1,mem_univ _⟩),
      by dsimp [support]; omega⟩
  have fiber (S : Finset (Fin (n+1))) (hS : S ∈ L) :
      (A.filter (fun v => support v = S)).card = (norm S.card).card := by
    have hs : S ⊆ U := mem_powerset.mp (mem_filter.mp hS).1
    have h0 : (0 : Fin (n+1)) ∉ S := fun h => (mem_erase.mp (hs h)).1 rfl
    let W := insert 0 S
    have hw : W.card=S.card+1 := card_insert_of_notMem h0
    let e := W.orderIsoOfFin hw
    have e0 : ((e 0 : W) : Fin (n+1)) = 0 := by
      let z : W := ⟨0, mem_insert_self _ _⟩
      have he := e.monotone (Fin.zero_le (e.symm z))
      rw [e.apply_symm_apply] at he
      exact Fin.le_zero_iff.mp he
    let lift (v : Q × (Fin 9 → Fin (S.card+1))) : Q × (Fin 9 → Fin (n+1)) :=
      (v.1,fun i => (e (v.2 i)).val)
    have cmp (v : Q × (Fin 9 → Fin (S.card+1))) :
        (fun i j => (lift v).2 i ≤ (lift v).2 j) = (fun i j => v.2 i ≤ v.2 j) := by
      funext i j
      exact propext e.le_iff_le
    symm
    apply card_bij (fun v _ => lift v)
    · intro v hv
      obtain ⟨⟨hz,hp⟩,sur⟩ := (mem_filter.mp hv).2
      have heq : univ.image (lift v).2 = W := by
        ext i
        constructor
        · rintro hi
          obtain ⟨j,_,rfl⟩ := mem_image.mp hi
          exact (e (v.2 j)).property
        · intro hi
          obtain ⟨j,hj⟩ := sur (e.symm ⟨i,hi⟩)
          exact mem_image.mpr ⟨j,mem_univ _, by
            dsimp [lift]; rw [hj, e.apply_symm_apply]⟩
      refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,?_,?_⟩,?_⟩
      · change ((e (v.2 0)).val).val=0
        rw [show v.2 0=0 from Fin.ext hz,e0]
        rfl
      · change P v.1 _
        rw [cmp]
        exact hp
      · dsimp only [support]; rw [heq]; exact erase_insert h0
    · intro v _ w _ hh
      refine Prod.ext ?_ ?_
      · exact (congrArg (fun z : Q × (Fin 9 → Fin (n+1)) => z.1) hh)
      funext i
      apply e.injective
      apply Subtype.ext
      exact congrArg (fun z => z.2 i) hh
    · intro w hw'
      obtain ⟨hwA,hsp⟩ := mem_filter.mp hw'
      obtain ⟨hz,hp⟩ := (mem_filter.mp hwA).2
      have hzero : w.2 0=0 := Fin.ext hz
      have h0mem : 0 ∈ univ.image w.2 := mem_image.mpr ⟨0,mem_univ _,hzero⟩
      have hW : W = univ.image w.2 := by
        change insert 0 S = _
        rw [←hsp]; exact insert_erase h0mem
      let r (i : Fin 9) := e.symm ⟨w.2 i, hW ▸ mem_image_of_mem _ (mem_univ _)⟩
      let v : Q × (Fin 9 → Fin (S.card+1)) := (w.1,r)
      have hlr : lift v = w := by
        refine Prod.ext ?_ ?_
        · rfl
        funext i
        simp [lift,v,r]
      have hrz : r 0=0 := by
        apply e.injective
        apply Subtype.ext
        simpa only [r,e.apply_symm_apply,e0] using hzero
      refine ⟨v,mem_filter.mpr ⟨mem_univ _,⟨congrArg Fin.val hrz,?_⟩,?_⟩,hlr⟩
      · change P w.1 _
        rw [←cmp v,hlr]
        exact hp
      · intro j
        have hm : (e j).val ∈ univ.image w.2 := hW ▸ (e j).property
        obtain ⟨i,_,hi⟩ := mem_image.mp hm
        refine ⟨i,e.injective ?_⟩
        apply Subtype.ext
        simpa [v,r] using hi
  have hc (d : ℕ) (hd : d ∈ range 9) :
      L.filter (fun s => s.card = d) = U.powersetCard d := by
    ext s
    simp only [L,mem_filter,mem_powerset,mem_powersetCard]
    have hd' := mem_range.mp hd
    aesop
  have hmaps : (L : Set _) |>.MapsTo Finset.card (range 9) :=
    fun s hs => mem_range.mpr ((mem_filter.mp (show s ∈ L from hs)).2)
  rw [Fintype.card_subtype]
  change A.card = _
  rw [card_eq_sum_card_fiberwise maps]
  calc
    _ = ∑ S ∈ L, (norm S.card).card := sum_congr rfl fiber
    _ = ∑ d ∈ range 9, ∑ S ∈ L.filter (fun s => s.card = d), (norm d).card := by
      rw [← sum_fiberwise_of_maps_to hmaps]
      apply sum_congr rfl
      intro d _
      apply sum_congr rfl
      intro s hs
      rw [(mem_filter.mp hs).2]
    _ = _ := by
      apply sum_congr rfl
      intro d hd
      rw [hc d hd,sum_const,card_powersetCard]
      simp [U,Nat.mul_comm]
end Window241

namespace Window241
open OMA.S_oeis_a241940

/-- The eight free cumulative sums give a positive binomial expansion in n. -/
theorem native_levels : ∃ weights : Fin 9 → ℤ, ∀ n : ℕ,
    a (n+1) = ∑ d : Fin 9, weights d * ((n.choose d.val : ℕ):ℤ) := by
  obtain ⟨c,hc⟩ := levels_count allowed
  refine ⟨fun d => (c d.val : ℤ),fun n => ?_⟩
  rw [prefix_count (n+1) (by omega),hc n]
  push_cast
  exact (Fin.sum_univ_eq_sum_range (fun d : ℕ => (c d : ℤ)*(n.choose d : ℤ)) 9).symm

end Window241

namespace Window241
open OMA.S_oeis_a241940 Finset

private theorem all_four (P : ℕ → Prop) :
    (∀ i<4, P i) ↔ P 0 ∧ P 1 ∧ P 2 ∧ P 3 := by
  constructor
  · exact fun h => ⟨h 0 (by decide),h 1 (by decide),h 2 (by decide),h 3 (by decide)⟩
  · rintro ⟨h0,h1,h2,h3⟩ i hi
    interval_cases i <;> assumption

theorem good_ends {n : ℕ} (u b c s t d e z : Fin (n+1)) :
    good ![u,b,c,s,t,d,e,z] = true ↔
      ((↑s:ℕ)+t+c+b+u ≤ 2*n ∧ (↑s:ℕ)+t+c+d+b ≤ 2*n) ∧
      ((↑s:ℕ)+t+d+c+e ≤ 2*n ∧ (↑s:ℕ)+t+d+e+z ≤ 2*n) := by
  simp only [good,decide_eq_true_eq,all_four]
  norm_num [Finset.sum_range_succ,OMA.S_oeis_a241940.get]; omega

/-- For fixed inner entries, count choices of the two leftmost entries. -/
def side (n h c d : ℕ) : ℕ :=
  ∑ b ∈ range (n+1), if h+c+d+b ≤ 2*n then min (n+1) (2*n+1-(h+c+b)) else 0

private theorem count_ends (n q : ℕ) :
    (∑ u : Fin (n+1), if q+u ≤ 2*n then 1 else 0) = min (n+1) (2*n+1-q) := by
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => if q+i ≤ 2*n then 1 else 0)]
  have mask : (range (n+1)).filter (fun i => q+i ≤ 2*n) = range (min (n+1) (2*n+1-q)) := by
    ext i
    simp only [mem_filter,mem_range,lt_min_iff]
    omega
  rw [←Finset.card_filter,mask,Finset.card_range]

private theorem side_sum (n h c d : ℕ) :
    (∑ b : Fin (n+1), ∑ u : Fin (n+1),
      if h+c+b+u ≤ 2*n ∧ h+c+d+b ≤ 2*n then 1 else 0) = side n h c d := by
  change _ = ∑ b ∈ range (n+1),_
  rw [← Fin.sum_univ_eq_sum_range]
  apply sum_congr rfl
  intro b _
  by_cases hb : h+c+d+b ≤ 2*n
  · simpa only [hb,and_true,if_true] using count_ends n (h+c+b)
  · simp [hb]

/-- Conditioning on the four middle entries separates the two free pairs. -/
theorem meet_count (n : ℕ) :
    a n = ((∑ s : Fin (n+1), ∑ t : Fin (n+1), ∑ c : Fin (n+1), ∑ d : Fin (n+1),
      side n ((s:ℕ)+t) c d * side n ((s:ℕ)+t) d c : ℕ) : ℤ) := by
  let A := Fin (n+1)
  let E : (Fin 8 → A) ≃ A × A × A × A × A × A × A × A :=
    { toFun := fun x => (x 3,x 4,x 2,x 5,x 1,x 0,x 6,x 7)
      invFun := fun ⟨s,t,c,d,b,u,e,z⟩ => ![u,b,c,s,t,d,e,z]
      left_inv := by intro x; funext i; fin_cases i <;> rfl
      right_inv := by rintro ⟨s,t,c,d,b,u,e,z⟩; rfl }
  let W (x : Fin 8 → A) : ℕ := if good x then 1 else 0
  change (↑((univ.filter (fun x : Fin 8 → A => good x)).card) : ℤ) = _
  apply congrArg Nat.cast
  have ha : ((univ.filter (fun x : Fin 8 → A => good x)).card) = ∑ x,W x := by
    rw [card_filter]
  rw [ha,←E.symm.sum_comp W]
  simp only [Fintype.sum_prod_type]
  apply sum_congr rfl; intro s _
  apply sum_congr rfl; intro t _
  apply sum_congr rfl; intro c _
  apply sum_congr rfl; intro d _
  change (∑ b : Fin (n+1),∑ u : Fin (n+1),∑ e : Fin (n+1),∑ z : Fin (n+1),
    if good ![u,b,c,s,t,d,e,z] then (1:ℕ) else 0) = _
  simp only [good_ends]
  rw [←side_sum n _ c d,←side_sum n _ d c,sum_mul]
  apply sum_congr rfl; intro b _
  rw [sum_mul]
  apply sum_congr rfl; intro u _
  rw [mul_sum]
  apply sum_congr rfl; intro e _
  rw [mul_sum]
  apply sum_congr rfl; intro z _
  split_ifs <;> simp_all

end Window241

namespace Window241
open OMA.S_oeis_a241940

theorem value_1 : a 1 = 71 := by
  let v : ℕ → ℕ := fun h => ([44,13,1] : List ℕ)[h]!
  have check (h : Fin 3) :
      (∑ c : Fin 2, ∑ d : Fin 2, side 1 h c d * side 1 h d c) = v h := by
    fin_cases h <;> decide +kernel
  rw [meet_count]
  have use (s t : Fin 2) :
      (∑ c : Fin 2, ∑ d : Fin 2, side 1 ((s:ℕ)+t) c d * side 1 ((s:ℕ)+t) d c) = v (s+t) :=
    check ⟨(s:ℕ)+t,by omega⟩
  simp only [use]
  decide +kernel

theorem value_2 : a 2 = 1187 := by
  let v : ℕ → ℕ := fun h => ([466,233,76,13,1] : List ℕ)[h]!
  have check (h : Fin 5) :
      (∑ c : Fin 3, ∑ d : Fin 3, side 2 h c d * side 2 h d c) = v h := by
    fin_cases h <;> decide +kernel
  rw [meet_count]
  have use (s t : Fin 3) :
      (∑ c : Fin 3, ∑ d : Fin 3, side 2 ((s:ℕ)+t) c d * side 2 ((s:ℕ)+t) d c) = v (s+t) :=
    check ⟨(s:ℕ)+t,by omega⟩
  simp only [use]
  decide +kernel

theorem value_3 : a 3 = 9500 := by
  let v : ℕ → ℕ := fun h => ([2552,1579,785,295,76,13,1] : List ℕ)[h]!
  have check (h : Fin 7) :
      (∑ c : Fin 4, ∑ d : Fin 4, side 3 h c d * side 3 h d c) = v h := by
    fin_cases h <;> decide +kernel
  rw [meet_count]
  have use (s t : Fin 4) :
      (∑ c : Fin 4, ∑ d : Fin 4, side 3 ((s:ℕ)+t) c d * side 3 ((s:ℕ)+t) d c) = v (s+t) :=
    check ⟨(s:ℕ)+t,by omega⟩
  simp only [use]
  decide +kernel

theorem value_4 : a 4 = 49355 := by
  let v : ℕ → ℕ := fun h => ([9620,6672,4045,2094,889,295,76,13,1] : List ℕ)[h]!
  have check (h : Fin 9) :
      (∑ c : Fin 5, ∑ d : Fin 5, side 4 h c d * side 4 h d c) = v h := by
    fin_cases h <;> decide +kernel
  rw [meet_count]
  have use (s t : Fin 5) :
      (∑ c : Fin 5, ∑ d : Fin 5, side 4 ((s:ℕ)+t) c d * side 4 ((s:ℕ)+t) d c) = v (s+t) :=
    check ⟨(s:ℕ)+t,by omega⟩
  simp only [use]
  decide +kernel

theorem value_5 : a 5 = 193179 := by
  let v : ℕ → ℕ := fun h => ([28540,21246,14433,8851,4808,2254,889,295,76,13,1] : List ℕ)[h]!
  have check (h : Fin 11) :
      (∑ c : Fin 6, ∑ d : Fin 6, side 5 h c d * side 5 h d c) = v h := by
    fin_cases h <;> decide +kernel
  rw [meet_count]
  have use (s t : Fin 6) :
      (∑ c : Fin 6, ∑ d : Fin 6, side 5 ((s:ℕ)+t) c d * side 5 ((s:ℕ)+t) d c) = v (s+t) :=
    check ⟨(s:ℕ)+t,by omega⟩
  simp only [use]
  decide +kernel

theorem value_6 : a 6 = 619132 := by
  let v : ℕ → ℕ := fun h => ([71687,55993,40923,27829,17434,9920,5040,2254,889,295,76,13,1] : List ℕ)[h]!
  have check (h : Fin 13) :
      (∑ c : Fin 7, ∑ d : Fin 7, side 6 h c d * side 6 h d c) = v h := by
    fin_cases h <;> decide +kernel
  rw [meet_count]
  have use (s t : Fin 7) :
      (∑ c : Fin 7, ∑ d : Fin 7, side 6 ((s:ℕ)+t) c d * side 6 ((s:ℕ)+t) d c) = v (s+t) :=
    check ⟨(s:ℕ)+t,by omega⟩
  simp only [use]
  decide +kernel

theorem value_7 : a 7 = 1710198 := by
  let v : ℕ → ℕ := fun h => ([159328,128842,99057,72176,49556,31800,18873,10242,5040,2254,889,295,76,13,1] : List ℕ)[h]!
  have check (h : Fin 15) :
      (∑ c : Fin 8, ∑ d : Fin 8, side 7 h c d * side 7 h d c) = v h := by
    fin_cases h <;> decide +kernel
  rw [meet_count]
  have use (s t : Fin 8) :
      (∑ c : Fin 8, ∑ d : Fin 8, side 7 ((s:ℕ)+t) c d * side 7 ((s:ℕ)+t) d c) = v (s+t) :=
    check ⟨(s:ℕ)+t,by omega⟩
  simp only [use]
  decide +kernel

theorem value_8 : a 8 = 4211175 := by
  let v : ℕ → ℕ := fun h => ([322443,267672,213550,163422,119540,83159,54657,33679,19305,10242,5040,2254,889,295,76,13,1] : List ℕ)[h]!
  have check (h : Fin 17) :
      (∑ c : Fin 9, ∑ d : Fin 9, side 8 h c d * side 8 h d c) = v h := by
    fin_cases h <;> decide +kernel
  rw [meet_count]
  have use (s t : Fin 9) :
      (∑ c : Fin 9, ∑ d : Fin 9, side 8 ((s:ℕ)+t) c d * side 8 ((s:ℕ)+t) d c) = v (s+t) :=
    check ⟨(s:ℕ)+t,by omega⟩
  simp only [use]
  decide +kernel

theorem value_9 : a 9 = 9462805 := by
  let v : ℕ → ℕ := fun h => ([605980,513459,421329,334410,256152,188735,133193,89562,57052,34243,19305,10242,5040,2254,889,295,76,13,1] : List ℕ)[h]!
  have check (h : Fin 19) :
      (∑ c : Fin 10, ∑ d : Fin 10, side 9 h c d * side 9 h d c) = v h := by
    fin_cases h <;> decide +kernel
  rw [meet_count]
  have use (s t : Fin 10) :
      (∑ c : Fin 10, ∑ d : Fin 10, side 9 ((s:ℕ)+t) c d * side 9 ((s:ℕ)+t) d c) = v (s+t) :=
    check ⟨(s:ℕ)+t,by omega⟩
  simp only [use]
  decide +kernel

theorem native_samples : ∀ n : Fin 9, a (n.val+1) =
    (![71,1187,9500,49355,193179,619132,1710198,4211175,9462805] : Fin 9 → ℤ) n := by
  intro n
  fin_cases n
  · exact value_1
  · exact value_2
  · exact value_3
  · exact value_4
  · exact value_5
  · exact value_6
  · exact value_7
  · exact value_8
  · exact value_9

end Window241

namespace Window241
open PowerSeries
open OMA.S_oeis_a241940

def samples : Fin 9 → ℤ := ![71,1187,9500,49355,193179,619132,1710198,4211175,9462805]
def weights : Fin 9 → ℤ := ![71,1116,7197,24345,48082,57651,41440,16459,2782]

/-- The square matrix of binomial coefficients is unit lower triangular. -/
theorem binomial_unique {D : ℕ} {c t : Fin D → ℤ}
    (h : ∀ n : Fin D, ∑ d, c d * ((n.val.choose d.val : ℕ):ℤ) =
      ∑ d, t d * ((n.val.choose d.val : ℕ):ℤ)) : c=t := by
  funext i
  induction hi : i.val using Nat.strong_induction_on generalizing i with
  | h k ih =>
    have hz : ∑ d : Fin D, (c d-t d) * ((i.val.choose d.val : ℕ):ℤ) = 0 := by
      simp only [sub_mul,Finset.sum_sub_distrib,h i,sub_self]
    rw [Finset.sum_eq_single i] at hz
    · simpa using sub_eq_zero.mp (by simpa using hz : c i-t i=0)
    · intro d _ hdi
      by_cases lt : d.val < i.val
      · have e := ih d.val (by omega) d rfl
        simp [e]
      · have hn : i.val < d.val := by
          have ne : d.val≠i.val := fun h => hdi (Fin.ext h)
          omega
        simp [Nat.choose_eq_zero_of_lt hn]
    · simp

theorem weights_samples (n : Fin 9) :
    ∑ d : Fin 9, weights d * ((n.val.choose d.val : ℕ):ℤ) = samples n := by
  revert n
  decide +kernel

/-- The explicit binomial-basis polynomial valid at every positive parameter. -/
theorem explicit_counts
    (shape : ∃ c : Fin 9 → ℤ, ∀ n : ℕ, a (n+1) = ∑ d, c d * ((n.choose d.val : ℕ):ℤ))
    (data : ∀ n : Fin 9, a (n.val+1)=samples n) (n : ℕ) :
    a (n+1)= ∑ d : Fin 9, weights d * ((n.choose d.val : ℕ):ℤ) := by
  obtain ⟨c,hc⟩ := shape
  have ht : c=weights := binomial_unique (fun i => by rw [← hc,data,weights_samples])
  simpa [ht] using hc n

noncomputable def binSeries (d : ℕ) : PowerSeries ℚ := mk fun n => (n.choose d : ℚ)

theorem binSeries_one_sub (d : ℕ) : binSeries d * (1-X)^(d+1) = X^d := by
  induction d with
  | zero =>
    ext n
    cases n with
    | zero => simp [binSeries]
    | succ n => simp [binSeries,mul_sub,coeff_succ_mul_X,coeff_one]
  | succ d ih =>
    have step : binSeries (d+1)*(1-X)=X*binSeries d := by
      ext n
      cases n with
      | zero => simp [binSeries,mul_sub]
      | succ n =>
        simp [binSeries,mul_sub,coeff_succ_mul_X,coeff_succ_X_mul,Nat.choose_succ_succ]
    calc
      _ = (binSeries (d+1)*(1-X))*(1-X)^(d+1) := by ring
      _ = X*(binSeries d*(1-X)^(d+1)) := by rw [step]; ring
      _ = X^(d+1) := by rw [ih,pow_succ]; ring

noncomputable def series : PowerSeries ℚ := mk fun n => if n < 1 then 0 else (a n:ℚ)

theorem gf_of_explicit
    (h : ∀ n : ℕ, a (n+1)= ∑ d : Fin 9, weights d * ((n.choose d.val : ℕ):ℤ)) :
    series * (1-X)^9 = X*(71+548*X+1373*X^2+623*X^3+222*X^4-83*X^5+36*X^6-9*X^7+X^8) := by
  have rep : series = X * ∑ d : Fin 9, C ((weights d:ℤ):ℚ)*binSeries d.val := by
    ext n
    cases n with
    | zero => simp [series]
    | succ n =>
      rw [coeff_succ_X_mul]
      simp only [series,coeff_mk,if_neg (by omega : ¬n+1<1),map_sum,coeff_C_mul,binSeries]
      exact_mod_cast h n
  have reduce (d : Fin 9) : binSeries d.val*(1-X)^9 = X^d.val*(1-X)^(8-d.val) := by
    have add : 9=d.val+1+(8-d.val) := by omega
    have ep := congrArg (fun e : ℕ => (1-X : PowerSeries ℚ)^e) add
    rw [pow_add] at ep
    rw [ep,← mul_assoc,binSeries_one_sub]
  rw [rep,mul_assoc,Finset.sum_mul]
  simp_rw [mul_assoc,reduce]
  norm_num [weights,Fin.sum_univ_succ]
  ring

end Window241

namespace Window241
open PowerSeries
open OMA.S_oeis_a241940

/-- Read the ninth finite difference off the numerator. -/
theorem recurrence_of_gf
    (h : series * (1-X)^9 = X*(71+548*X+1373*X^2+623*X^3+222*X^4-83*X^5+36*X^6-9*X^7+X^8))
    (n : ℕ) (hn : 10≤n) :
    (a n : ℚ) = 9 * a (n - 1) - 36 * a (n - 2) + 84 * a (n - 3) - 126 * a (n - 4) +
      126 * a (n - 5) - 84 * a (n - 6) + 36 * a (n - 7) - 9 * a (n - 8) + a (n - 9) := by
  have eqn : series - C 9*(series*X^1) + C 36*(series*X^2) - C 84*(series*X^3)
      + C 126*(series*X^4) - C 126*(series*X^5) + C 84*(series*X^6)
      - C 36*(series*X^7) + C 9*(series*X^8) - series*X^9 =
      C 71*X^1+C 548*X^2+C 1373*X^3+C 623*X^4+C 222*X^5-C 83*X^6+
      C 36*X^7-C 9*X^8+X^9 := by
    simp only [map_ofNat]
    linear_combination h
  have atn := congrArg (coeff n) eqn
  simp only [map_sub,map_add,coeff_C_mul,coeff_mul_X_pow',coeff_X_pow,coeff_C,series,coeff_mk] at atn
  simp (disch := omega) only [if_pos, if_neg, add_zero, sub_zero] at atn
  linarith only [atn]

end Window241

namespace Window241
open PowerSeries OMA.S_oeis_a241940

/-- Hardin's count, expressed in the binomial basis centered at parameter one. -/
theorem all_counts (n : ℕ) :
    a (n+1)=∑ d : Fin 9, weights d * ((n.choose d.val : ℕ):ℤ) :=
  explicit_counts native_levels native_samples n

/-- Restoring the zero-dilate constant gives the Ehrhart numerator. -/
theorem ehrhart_numerator :
    mk (fun n => (a n : ℚ)) * (1-X)^9 =
      1+62*X+584*X^2+1289*X^3+749*X^4+96*X^5+X^6 := by
  have zero : a 0=1 := by decide +kernel
  have fix : mk (fun n => (a n : ℚ)) = 1+series := by
    ext n
    cases n with
    | zero => simp [series,zero]
    | succ n => simp [series,coeff_one]
  rw [fix,add_mul,one_mul,gf_of_explicit all_counts]
  ring

end Window241

theorem OMA.solution : type_of% @OMA.S_oeis_a241940.main := by
  have gf := Window241.gf_of_explicit Window241.all_counts
  exact ⟨gf, Window241.recurrence_of_gf gf⟩
