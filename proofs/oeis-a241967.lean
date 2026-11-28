import OMAStatements.S_oeis_a241967
import Mathlib

/-!
# Four-entry window sums in Hardin's seven-entry arrays

The OEIS problem is https://oeis.org/A241967. R. H. Hardin provided an
empirical polynomial, and Colin Barker conjectured the generating function
and eighth-order recurrence in 2018. The proof uses the prefix-coordinate
method of https://github.com/lefttosolve2/open-math-agents/pull/31241.
Here the order-type counting theorem and binomial-series formula are proved
in arbitrary dimension. Checking the eight native counts determines the
coefficients for the four-entry window predicate.
-/

namespace Window967

open OMA.S_oeis_a241967
open scoped Classical

def leftIndex (j : Fin 4) : Fin 8 := ⟨j.val, by omega⟩
def rightIndex (j : Fin 4) : Fin 8 := ⟨j.val+4, by omega⟩

def allowed (q : Fin 8 → Fin 8) (leR : Fin 8 → Fin 8 → Prop) : Prop :=
  let cmp (i j : Fin 8) (c : ℕ) :=
    (q i).val < (q j).val + c ∨ ((q i).val = (q j).val + c ∧ leR i j)
  (q 0).val = 0 ∧
    (∀ i : Fin 7, cmp i.castSucc i.succ 0 ∧ cmp i.succ i.castSucc 1) ∧
    (∀ j : Fin 4, cmp (rightIndex j) (leftIndex j) 2)

private def prefixSum {n : ℕ} (x : Fin 7 → Fin (n+1)) (k : ℕ) : ℕ :=
  ∑ j ∈ Finset.range k, get x j

private theorem prefix_step {n : ℕ} (x : Fin 7 → Fin (n+1)) (i : Fin 7) :
    prefixSum x (i.val+1) = prefixSum x i.val + (x i).val := by
  simp [prefixSum, Finset.sum_range_succ, OMA.S_oeis_a241967.get, i.isLt]

private theorem prefix_window {n : ℕ} (x : Fin 7 → Fin (n+1)) (j : ℕ) :
    prefixSum x (j+4) = prefixSum x j + ∑ t ∈ Finset.range 4, get x (j+t) := by
  simp [prefixSum, Finset.sum_range_add]

private theorem prefix_le {n : ℕ} (x : Fin 7 → Fin (n+1)) (i : Fin 8) :
    prefixSum x i.val ≤ 7*n := by
  calc
    _ ≤ ∑ _j ∈ Finset.range i.val, n := by
      apply Finset.sum_le_sum
      intro j hj
      simp only [OMA.S_oeis_a241967.get]
      split
      · exact Nat.le_of_lt_succ (x _).isLt
      · exact Nat.zero_le _
    _ = i.val*n := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ (by omega)

private def bounds (n : ℕ) (S : Fin 8 → ℕ) : Prop :=
  S 0 = 0 ∧
    (∀ i : Fin 7, S i.castSucc ≤ S i.succ ∧ S i.succ ≤ S i.castSucc + n) ∧
    (∀ j : Fin 4, S (rightIndex j) ≤ S (leftIndex j) + 2*n)

private theorem prefix_bounds {n : ℕ} (x : Fin 7 → Fin (n+1)) :
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
    change prefixSum x (j+4) ≤ prefixSum x j+2*n at hh
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

private def height {n : ℕ} (q : Fin 8 → Fin 8) (r : Fin 8 → Fin n) (i : Fin 8) : ℕ :=
  n*(q i).val+(r i).val

private theorem height_cmp {n : ℕ} (q : Fin 8 → Fin 8) (r : Fin 8 → Fin n)
    (i j : Fin 8) (c : ℕ) :
    height q r i ≤ height q r j + c*n ↔
      (q i).val < (q j).val+c ∨ ((q i).val=(q j).val+c ∧ r i ≤ r j) := by
  unfold height
  rw [show n*(q j).val+(r j).val+c*n=n*((q j).val+c)+(r j).val by ring]
  exact digits_le (r i).isLt (r j).isLt

private theorem height_bounds {n : ℕ} (hn : 0<n) (q : Fin 8 → Fin 8) (r : Fin 8 → Fin n) :
    bounds n (height q r) ↔ (r 0).val=0 ∧ allowed q (fun i j => r i ≤ r j) := by
  have h0 : height q r 0 = 0 ↔ (r 0).val = 0 ∧ (q 0).val = 0 := by
    simp [height, Nat.add_eq_zero_iff, hn.ne', and_comm]
  have hcmp0 (i : Fin 7) := height_cmp q r i.castSucc i.succ 0
  have hcmp1 (i : Fin 7) := height_cmp q r i.succ i.castSucc 1
  simp only [Nat.zero_mul,Nat.add_zero] at hcmp0
  simp only [Nat.one_mul] at hcmp1
  unfold bounds allowed
  simp only [h0, hcmp0, hcmp1, height_cmp, Nat.add_zero]
  tauto

private def quotient {n : ℕ} (hn : 0<n) (x : Fin 7 → Fin (n+1)) (i : Fin 8) : Fin 8 :=
  ⟨prefixSum x i.val / n, (Nat.div_lt_iff_lt_mul hn).mpr
    (lt_of_le_of_lt (prefix_le x i) (by omega))⟩

private def remainder {n : ℕ} (hn : 0<n) (x : Fin 7 → Fin (n+1)) (i : Fin 8) : Fin n :=
  ⟨prefixSum x i.val % n, Nat.mod_lt _ hn⟩

private theorem height_digits {n : ℕ} (hn : 0<n) (x : Fin 7 → Fin (n+1)) :
    height (quotient hn x) (remainder hn x) = fun i => prefixSum x i.val := by
  funext i
  exact Nat.div_add_mod _ _

private def increments {n : ℕ} (S : Fin 8 → ℕ) (h : bounds n S) (i : Fin 7) : Fin (n+1) :=
  ⟨S i.succ - S i.castSucc, by have := (h.2.1 i).2; omega⟩

private theorem prefix_increments {n : ℕ} (S : Fin 8 → ℕ) (h : bounds n S) :
    (fun i : Fin 8 => prefixSum (increments S h) i.val) = S := by
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
    {x : Fin 7 → Fin (n+1) // good x = true} ≃
      {qr : (Fin 8 → Fin 8) × (Fin 8 → Fin n) //
        (qr.2 0).val = 0 ∧ allowed qr.1 (fun i j => qr.2 i ≤ qr.2 j)} := by
  let f (x : {x : Fin 7 → Fin (n+1) // good x = true}) :
      {qr : (Fin 8 → Fin 8) × (Fin 8 → Fin n) //
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
    have he : (fun i : Fin 8 => prefixSum x i.val) = height q r := prefix_increments _ _
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
    OMA.S_oeis_a241967.a n =
      (Fintype.card {qr : (Fin 8 → Fin 8) × (Fin 8 → Fin n) //
        (qr.2 0).val=0 ∧ allowed qr.1 (fun i j => qr.2 i ≤ qr.2 j)} : ℤ) := by
  have h := Fintype.card_congr (prefixEquiv hn)
  simpa [a,Fintype.card_subtype] using (congrArg (fun k : ℕ => (k : ℤ)) h)

end Window967

namespace Window967
open Finset
open scoped Classical

/-- A pair consisting of a state and a zero-based residue word can be standardized
by replacing each used positive residue with its rank. Each set of positive residues
of the prescribed size contributes exactly the same number of words. -/
theorem levels_count (D : ℕ) {Q : Type*} [Fintype Q] (P : Q → (Fin (D+1) → Fin (D+1) → Prop) → Prop) :
    ∃ c : ℕ → ℕ, ∀ n : ℕ,
      Fintype.card {v : Q × (Fin (D+1) → Fin (n+1)) //
        (v.2 0).val = 0 ∧ P v.1 (fun i j => v.2 i ≤ v.2 j)} =
      ∑ d ∈ range (D+1), c d * n.choose d := by
  classical
  let valid (n : ℕ) (v : Q × (Fin (D+1) → Fin (n+1))) :=
    (v.2 0).val = 0 ∧ P v.1 (fun i j => v.2 i ≤ v.2 j)
  let norm (d : ℕ) := (univ : Finset (Q × (Fin (D+1) → Fin (d+1)))).filter
    fun v => valid d v ∧ Function.Surjective v.2
  refine ⟨fun d => (norm d).card, fun n => ?_⟩
  let A := (univ : Finset (Q × (Fin (D+1) → Fin (n+1)))).filter (valid n)
  let U := (univ : Finset (Fin (n+1))).erase 0
  let L := U.powerset.filter (fun s => s.card < D+1)
  let support (v : Q × (Fin (D+1) → Fin (n+1))) := (univ.image v.2).erase 0
  have maps : (A : Set _) |>.MapsTo support L := by
    intro v hv
    have h0 : v.2 0 = 0 := Fin.ext (mem_filter.mp hv).2.1
    have hm : 0 ∈ univ.image v.2 := mem_image.mpr ⟨0,mem_univ _,h0⟩
    have hc : (univ.image v.2).card ≤ D+1 := (card_image_le).trans_eq (by simp)
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
    let lift (v : Q × (Fin (D+1) → Fin (S.card+1))) : Q × (Fin (D+1) → Fin (n+1)) :=
      (v.1,fun i => (e (v.2 i)).val)
    have cmp (v : Q × (Fin (D+1) → Fin (S.card+1))) :
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
      · exact (congrArg (fun z : Q × (Fin (D+1) → Fin (n+1)) => z.1) hh)
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
      let r (i : Fin (D+1)) := e.symm ⟨w.2 i, hW ▸ mem_image_of_mem _ (mem_univ _)⟩
      let v : Q × (Fin (D+1) → Fin (S.card+1)) := (w.1,r)
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
  have hc (d : ℕ) (hd : d ∈ range (D+1)) :
      L.filter (fun s => s.card = d) = U.powersetCard d := by
    ext s
    simp only [L,mem_filter,mem_powerset,mem_powersetCard]
    have hd' := mem_range.mp hd
    aesop
  have hmaps : (L : Set _) |>.MapsTo Finset.card (range (D+1)) :=
    fun s hs => mem_range.mpr ((mem_filter.mp (show s ∈ L from hs)).2)
  rw [Fintype.card_subtype]
  change A.card = _
  rw [card_eq_sum_card_fiberwise maps]
  calc
    _ = ∑ S ∈ L, (norm S.card).card := sum_congr rfl fiber
    _ = ∑ d ∈ range (D+1), ∑ S ∈ L.filter (fun s => s.card = d), (norm d).card := by
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
end Window967

namespace Window967

open scoped Classical

/-- For arbitrary coordinate and constraint sets, quotient coordinates and the order on remainders
determine all integral bounds on coordinate differences. A distinguished coordinate is fixed at zero. -/
noncomputable def differenceConstraintEquiv {I J : Type*} (z : I) (src dst : J → I)
    (bound : J → ℕ) (Q n : ℕ) :
    {S : I → Fin (Q*n) // (S z).val = 0 ∧
      ∀ j, (S (dst j)).val ≤ (S (src j)).val + bound j*n} ≃
    {w : (I → Fin Q) × (I → Fin n) //
      (w.2 z).val = 0 ∧ (w.1 z).val = 0 ∧ ∀ j,
        (w.1 (dst j)).val < (w.1 (src j)).val + bound j ∨
        ((w.1 (dst j)).val = (w.1 (src j)).val + bound j ∧ w.2 (dst j) ≤ w.2 (src j))} := by
  let E : (I → Fin (Q*n)) ≃ ((I → Fin Q) × (I → Fin n)) :=
    (Equiv.piCongrRight (fun _ : I => finProdFinEquiv.symm)).trans
      (Equiv.arrowProdEquivProdArrow I (fun _ => Fin Q) (fun _ => Fin n))
  apply E.subtypeEquiv
  intro S
  let w := E S
  have hv (i : I) : (S i).val = n*(w.1 i).val+(w.2 i).val := by
    change (S i).val = n*((S i).val/n) + (S i).val%n
    exact (Nat.div_add_mod _ _).symm
  have hn : 0<n := lt_of_le_of_lt (Nat.zero_le _) (w.2 z).isLt
  have h0 : (S z).val=0 ↔ (w.2 z).val=0 ∧ (w.1 z).val=0 := by
    rw [hv z]
    simp [Nat.add_eq_zero_iff, hn.ne', and_comm]
  have hc (j : J) : (S (dst j)).val ≤ (S (src j)).val+bound j*n ↔
      (w.1 (dst j)).val < (w.1 (src j)).val + bound j ∨
        ((w.1 (dst j)).val = (w.1 (src j)).val + bound j ∧ w.2 (dst j) ≤ w.2 (src j)) := by
    set a := (w.1 (dst j)).val
    set b := (w.1 (src j)).val + bound j
    rw [hv (dst j), hv (src j)]
    change n*a+(w.2 (dst j)).val ≤ _ ↔ _
    rw [show n*(w.1 (src j)).val+(w.2 (src j)).val+bound j*n =
      n*b+(w.2 (src j)).val by unfold b; ring]
    have hu := (w.2 (dst j)).isLt
    have hv' := (w.2 (src j)).isLt
    change _ ↔ a < b ∨ (a=b ∧ (w.2 (dst j)).val ≤ (w.2 (src j)).val)
    rcases lt_trichotomy a b with h|h|h
    · have hh := Nat.mul_le_mul_left n (Nat.succ_le_iff.mpr h)
      rw [Nat.mul_succ] at hh
      omega
    · rw [h]
      simp
    · have hh := Nat.mul_le_mul_left n (Nat.succ_le_iff.mpr h)
      rw [Nat.mul_succ] at hh
      omega
  change _ ↔ (w.2 z).val=0 ∧ _
  simp only [h0,hc]
  tauto

end Window967

namespace Window967

open scoped Classical

/-- The lattice-point count for a bounded system of scaled difference inequalities, with one
coordinate pinned to zero, has nonnegative integer coefficients in the binomial basis. -/
theorem differenceConstraint_count (D Q : ℕ) {J : Type*} (src dst : J → Fin (D+1))
    (bound : J → ℕ) :
    ∃ c : ℕ → ℕ, ∀ n : ℕ,
      Fintype.card {S : Fin (D+1) → Fin (Q*(n+1)) // (S 0).val = 0 ∧
        ∀ j, (S (dst j)).val ≤ (S (src j)).val + bound j*(n+1)} =
      ∑ d ∈ Finset.range (D+1), c d * n.choose d := by
  let P (q : Fin (D+1) → Fin Q) (leR : Fin (D+1) → Fin (D+1) → Prop) :=
    (q 0).val = 0 ∧ ∀ j,
      (q (dst j)).val < (q (src j)).val + bound j ∨
      ((q (dst j)).val = (q (src j)).val + bound j ∧ leR (dst j) (src j))
  obtain ⟨c,hc⟩ := levels_count D P
  refine ⟨c, fun n => ?_⟩
  rw [← hc n]
  simp only [← Nat.card_eq_fintype_card]
  exact Nat.card_congr (differenceConstraintEquiv 0 src dst bound Q (n+1))

end Window967

namespace Window967
open OMA.S_oeis_a241967

/-- The seven free cumulative sums give a binomial expansion in the alphabet size minus one. -/
theorem native_levels : ∃ weights : Fin 8 → ℤ, ∀ n : ℕ,
    a (n+1) = ∑ d : Fin 8, weights d * ((n.choose d.val : ℕ):ℤ) := by
  obtain ⟨c,hc⟩ := levels_count 7 allowed
  refine ⟨fun d => (c d.val : ℤ),fun n => ?_⟩
  rw [prefix_count (n+1) (by omega),hc n]
  push_cast
  exact (Fin.sum_univ_eq_sum_range (fun d : ℕ => (c d : ℤ)*(n.choose d : ℤ)) 8).symm

end Window967

namespace Window967
open OMA.S_oeis_a241967 Finset

private theorem all_four (P : ℕ → Prop) :
    (∀ i<4, P i) ↔ P 0 ∧ P 1 ∧ P 2 ∧ P 3 := by
  constructor
  · exact fun h => ⟨h 0 (by decide),h 1 (by decide),h 2 (by decide),h 3 (by decide)⟩
  · rintro ⟨h0,h1,h2,h3⟩ i hi
    interval_cases i <;> assumption

theorem good_ends {n : ℕ} (u b c s d e z : Fin (n+1)) :
    good ![u,b,c,s,d,e,z] = true ↔
      ((↑s:ℕ)+c+b+u ≤ 2*n ∧ (↑s:ℕ)+c+d+b ≤ 2*n) ∧
      ((↑s:ℕ)+d+c+e ≤ 2*n ∧ (↑s:ℕ)+d+e+z ≤ 2*n) := by
  simp only [good,decide_eq_true_eq,all_four]
  norm_num [Finset.sum_range_succ,OMA.S_oeis_a241967.get]; omega

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

/-- Conditioning on the three middle entries separates the two free pairs. -/
theorem meet_count (n : ℕ) :
    a n = ((∑ s : Fin (n+1), ∑ c : Fin (n+1), ∑ d : Fin (n+1),
      side n (s:ℕ) c d * side n (s:ℕ) d c : ℕ) : ℤ) := by
  let A := Fin (n+1)
  let E : (Fin 7 → A) ≃ A × A × A × A × A × A × A :=
    { toFun := fun x => (x 3,x 2,x 4,x 1,x 0,x 5,x 6)
      invFun := fun ⟨s,c,d,b,u,e,z⟩ => ![u,b,c,s,d,e,z]
      left_inv := by intro x; funext i; fin_cases i <;> rfl
      right_inv := by rintro ⟨s,c,d,b,u,e,z⟩; rfl }
  let W (x : Fin 7 → A) : ℕ := if good x then 1 else 0
  change (↑((univ.filter (fun x : Fin 7 → A => good x)).card) : ℤ) = _
  apply congrArg Nat.cast
  have ha : ((univ.filter (fun x : Fin 7 → A => good x)).card) = ∑ x,W x := by
    rw [card_filter]
  rw [ha,←E.symm.sum_comp W]
  simp only [Fintype.sum_prod_type]
  apply sum_congr rfl; intro s _
  apply sum_congr rfl; intro c _
  apply sum_congr rfl; intro d _
  change (∑ b : Fin (n+1),∑ u : Fin (n+1),∑ e : Fin (n+1),∑ z : Fin (n+1),
    if good ![u,b,c,s,d,e,z] then (1:ℕ) else 0) = _
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

end Window967

namespace Window967
open OMA.S_oeis_a241967

theorem native_samples : ∀ n : Fin 8, a (n.val+1) =
    (![57,775,5211,23320,80132,228826,569874,1277427] : Fin 8 → ℤ) n := by
  intro n
  rw [meet_count]
  fin_cases n <;> decide +kernel

end Window967

namespace Window967
open PowerSeries
open OMA.S_oeis_a241967

def samples : Fin 8 → ℤ := ![57,775,5211,23320,80132,228826,569874,1277427]
def weights : Fin 8 → ℤ := ![57,718,3718,9955,15075,13074,6070,1172]

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

theorem weights_samples (n : Fin 8) :
    ∑ d : Fin 8, weights d * ((n.val.choose d.val : ℕ):ℤ) = samples n := by
  revert n
  decide +kernel

/-- The explicit binomial-basis polynomial valid at every positive parameter. -/
theorem explicit_counts
    (shape : ∃ c : Fin 8 → ℤ, ∀ n : ℕ, a (n+1) = ∑ d, c d * ((n.choose d.val : ℕ):ℤ))
    (data : ∀ n : Fin 8, a (n.val+1)=samples n) (n : ℕ) :
    a (n+1)= ∑ d : Fin 8, weights d * ((n.choose d.val : ℕ):ℤ) := by
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

theorem rational_binomial_series {D : ℕ} (v : Fin (D+1) → ℤ) (b : ℕ → ℤ)
    (h : ∀ n : ℕ, b (n+1)= ∑ d : Fin (D+1), v d * ((n.choose d.val : ℕ):ℤ)) :
    mk (fun n => if n<1 then 0 else (b n : ℚ)) * (1-X)^(D+1) =
      X*∑ d : Fin (D+1), C ((v d:ℤ):ℚ)*(X^d.val*(1-X)^(D-d.val)) := by
  have rep : mk (fun n => if n<1 then 0 else (b n : ℚ)) =
      X * ∑ d : Fin (D+1), C ((v d:ℤ):ℚ)*binSeries d.val := by
    ext n
    cases n with
    | zero => simp
    | succ n =>
      rw [coeff_succ_X_mul]
      simp only [coeff_mk,if_neg (by omega : ¬n+1<1),map_sum,coeff_C_mul,binSeries]
      exact_mod_cast h n
  have reduce (d : Fin (D+1)) : binSeries d.val*(1-X)^(D+1) = X^d.val*(1-X)^(D-d.val) := by
    have add : D+1=d.val+1+(D-d.val) := by omega
    have ep := congrArg (fun e : ℕ => (1-X : PowerSeries ℚ)^e) add
    rw [pow_add _ (d.val+1) (D-d.val)] at ep
    rw [ep,← mul_assoc,binSeries_one_sub]
  rw [rep,mul_assoc,Finset.sum_mul]
  simp_rw [mul_assoc,reduce]

theorem gf_of_explicit
    (h : ∀ n : ℕ, a (n+1)= ∑ d : Fin 8, weights d * ((n.choose d.val : ℕ):ℤ)) :
    series * (1-X)^8 = X*(57+319*X+607*X^2+140*X^3+70*X^4-28*X^5+8*X^6-X^7) := by
  have hf := rational_binomial_series (D:=7) weights a h
  change series*(1-X)^8 = _ at hf
  rw [hf]
  norm_num [weights,Fin.sum_univ_succ]
  ring

end Window967

namespace Window967
open PowerSeries
open OMA.S_oeis_a241967

/-- Read the eighth finite difference off the numerator. -/
theorem recurrence_of_gf
    (h : series * (1-X)^8 = X*(57+319*X+607*X^2+140*X^3+70*X^4-28*X^5+8*X^6-X^7))
    (n : ℕ) (hn : 9≤n) :
    (a n : ℚ) = 8 * a (n - 1) - 28 * a (n - 2) + 56 * a (n - 3) - 70 * a (n - 4) +
      56 * a (n - 5) - 28 * a (n - 6) + 8 * a (n - 7) - a (n - 8) := by
  have eqn : series - C 8*(series*X^1) + C 28*(series*X^2) - C 56*(series*X^3)
      + C 70*(series*X^4) - C 56*(series*X^5) + C 28*(series*X^6)
      - C 8*(series*X^7) + series*X^8 =
      C 57*X^1+C 319*X^2+C 607*X^3+C 140*X^4+C 70*X^5-C 28*X^6+
      C 8*X^7-X^8 := by
    simp only [map_ofNat]
    linear_combination h
  have atn := congrArg (coeff n) eqn
  simp only [map_sub,map_add,coeff_C_mul,coeff_mul_X_pow',coeff_X_pow,coeff_C,series,coeff_mk] at atn
  simp (disch := omega) only [if_pos, if_neg, add_zero, sub_zero] at atn
  linarith only [atn]

end Window967

namespace Window967
open PowerSeries OMA.S_oeis_a241967

/-- Hardin's count, expressed in the binomial basis centered at parameter one. -/
theorem all_counts (n : ℕ) :
    a (n+1)=∑ d : Fin 8, weights d * ((n.choose d.val : ℕ):ℤ) :=
  explicit_counts native_levels native_samples n

/-- Restoring the zero-dilate constant gives the Ehrhart numerator. -/
theorem ehrhart_numerator :
    mk (fun n => (a n : ℚ)) * (1-X)^8 =
      1+49*X+347*X^2+551*X^3+210*X^4+14*X^5 := by
  have zero : a 0=1 := by decide +kernel
  have fix : mk (fun n => (a n : ℚ)) = 1+series := by
    ext n
    cases n with
    | zero => simp [series,zero]
    | succ n => simp [series,coeff_one]
  rw [fix,add_mul,one_mul,gf_of_explicit all_counts]
  ring

end Window967

theorem OMA.solution : type_of% @OMA.S_oeis_a241967.main := by
  have gf := Window967.gf_of_explicit Window967.all_counts
  exact ⟨gf, Window967.recurrence_of_gf gf⟩
