import OMAStatements.S_mo_203533
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic

-- Problem source: https://mathoverflow.net/questions/203533
-- Formal statement: formal-conjectures, statements/mo-203533.lean (credit: @LDJAI)
-- Proof credit: @grp06

open Finset Configuration
open scoped BigOperators

open OMA.S_mo_203533 (contained)

section
variable {P L : Type*} [Fintype L] [Membership P L]

private theorem mem_contained' {S : Finset P} {l : L} :
    l ∈ contained P L S ↔ ∀ p : P, p ∈ l → p ∈ S := by
  classical
  simp [contained]

variable [Fintype P] [ProjectivePlane P L]

private theorem pencil_witness (m : ℕ) (hm : 1 ≤ m)
    (hm' : m ≤ Fintype.card P) :
    ∃ S : Finset P, S.card = m ∧
      (m - 1) / ProjectivePlane.order P L ≤ (contained P L S).card := by
  classical
  let q := ProjectivePlane.order P L
  let j := (m - 1) / q
  have hq : 0 < q := lt_trans Nat.zero_lt_one (ProjectivePlane.one_lt_order P L)
  have hjmul : j * q ≤ m - 1 := Nat.div_mul_le_self _ _
  have hj : j ≤ q + 1 := by
    apply Nat.le_of_mul_le_mul_right _ hq
    have hc : Fintype.card P = q ^ 2 + q + 1 := ProjectivePlane.card_points P L
    have h : m - 1 ≤ q ^ 2 + q := by omega
    exact hjmul.trans (by simpa only [add_mul, one_mul, pow_two] using h)
  obtain ⟨c, _⟩ := ProjectivePlane.exists_config (P := P) (L := L)
  let pencil : Finset L := univ.filter (fun l : L => c ∈ l)
  have hpencil : pencil.card = q + 1 := by
    calc
      pencil.card = lineCount L c := by
        rw [lineCount, Nat.card_eq_fintype_card]
        exact (Fintype.card_subtype (fun l : L => c ∈ l)).symm
      _ = q + 1 := ProjectivePlane.lineCount_eq L c
  have hj' : j ≤ pencil.card := by rw [hpencil]; exact hj
  obtain ⟨A, hA, hAj⟩ := Finset.exists_subset_card_eq hj'
  have hcA (l : L) (hl : l ∈ A) : c ∈ l := (mem_filter.mp (hA hl)).2
  let off (l : L) : Finset P := (univ.filter (fun p : P => p ∈ l)).erase c
  have hoff (l : L) (p : P) : p ∈ off l ↔ p ≠ c ∧ p ∈ l := by
    simp [off]
  have hcard (l : L) (hl : l ∈ A) : (off l).card = q := by
    have hline : (univ.filter (fun p : P => p ∈ l)).card = q + 1 := by
      calc
        _ = pointCount P l := by
          rw [pointCount, Nat.card_eq_fintype_card]
          exact (Fintype.card_subtype (fun p : P => p ∈ l)).symm
        _ = q + 1 := ProjectivePlane.pointCount_eq P l
    have he := card_erase_add_one
      (s := univ.filter (fun p : P => p ∈ l)) (a := c) (by simp [hcA l hl])
    change (off l).card + 1 = _ at he
    omega
  have hdisj : (A : Set L).PairwiseDisjoint off := by
    intro l hl k hk hne
    apply Finset.disjoint_left.mpr
    intro p hpl hpk
    obtain ⟨hpc, hpl'⟩ := (hoff l p).mp hpl
    have hpk' := ((hoff k p).mp hpk).2
    exact (Nondegenerate.eq_or_eq hpl' (hcA l hl) hpk' (hcA k hk)).elim hpc hne
  let U := A.biUnion off
  have hU : U.card = j * q := by
    change (A.biUnion off).card = j * q
    rw [card_biUnion hdisj]
    calc
      (∑ l ∈ A, (off l).card) = ∑ _l ∈ A, q :=
        sum_congr rfl hcard
      _ = j * q := by
        rw [← hAj]
        exact sum_const_nat (fun _ _ => rfl)
  have hcU : c ∉ U := by
    intro hc
    change c ∈ A.biUnion off at hc
    obtain ⟨l, _, hcl⟩ := mem_biUnion.mp hc
    exact ((hoff l c).mp hcl).1 rfl
  have hsize : (insert c U).card ≤ m := by
    rw [card_insert_of_notMem hcU, hU]
    omega
  obtain ⟨S, hUS, hSm⟩ := Finset.exists_superset_card_eq hsize hm'
  refine ⟨S, hSm, ?_⟩
  change j ≤ (contained P L S).card
  rw [← hAj]
  apply card_le_card
  intro l hl
  apply mem_contained'.mpr
  intro p hpl
  apply hUS
  by_cases hp : p = c
  · simp [hp]
  · exact mem_insert_of_mem (mem_biUnion.mpr ⟨l, hl, (hoff l p).mpr ⟨hp, hpl⟩⟩)

private theorem incidence_bound (S : Finset P) :
    (contained P L S).card * (ProjectivePlane.order P L + 1)^2 ≤
      S.card * (ProjectivePlane.order P L + (contained P L S).card) := by
  classical
  let q := ProjectivePlane.order P L
  let B := contained P L S
  let w (p : P) (l : L) : ℕ := if p ∈ l then 1 else 0
  let r (p : P) : ℕ := ∑ l ∈ B, w p l
  have hcol (l : L) (hl : l ∈ B) : (∑ p ∈ S, w p l) = q + 1 := by
    have hfilter : S.filter (fun p : P => p ∈ l) = univ.filter (fun p : P => p ∈ l) := by
      ext p
      simp only [mem_filter, mem_univ, true_and]
      exact ⟨And.right, fun hp => ⟨(mem_contained'.mp hl) p hp, hp⟩⟩
    calc
      (∑ p ∈ S, w p l) = (S.filter (fun p : P => p ∈ l)).card := by
        change (∑ p ∈ S, if p ∈ l then (1 : ℕ) else 0) = _
        rw [card_eq_sum_ones, sum_filter]
      _ = pointCount P l := by
        rw [hfilter, pointCount, Nat.card_eq_fintype_card]
        exact (Fintype.card_subtype (fun p : P => p ∈ l)).symm
      _ = q + 1 := ProjectivePlane.pointCount_eq P l
  have hfirst : (∑ p ∈ S, r p) = B.card * (q + 1) := by
    change (∑ p ∈ S, ∑ l ∈ B, w p l) = _
    rw [sum_comm]
    calc
      (∑ l ∈ B, ∑ p ∈ S, w p l) = ∑ _l ∈ B, (q + 1) := sum_congr rfl hcol
      _ = _ := sum_const_nat (fun _ _ => rfl)
  have hpair (l : L) (hl : l ∈ B) (k : L) :
      (∑ p ∈ S, w p l * w p k) = 1 + (if l = k then q else 0) := by
    by_cases hlk : l = k
    · subst k
      rw [if_pos (rfl : l = l)]
      calc
        (∑ p ∈ S, w p l * w p l) = ∑ p ∈ S, w p l := by
          apply sum_congr rfl
          intro p _
          by_cases hp : p ∈ l <;> simp [w, hp]
        _ = q + 1 := hcol l hl
        _ = 1 + q := Nat.add_comm _ _
    · obtain ⟨c, hc, hunique⟩ := HasPoints.existsUnique_point P L l k hlk
      have hcS : c ∈ S := (mem_contained'.mp hl) c hc.1
      simp only [if_neg hlk, add_zero]
      rw [sum_eq_single c]
      · simp [w, hc.1, hc.2]
      · intro p _ hpc
        by_cases hp : p ∈ l
        · have hpk : p ∉ k := fun hpk => hpc (hunique p ⟨hp, hpk⟩)
          simp [w, hp, hpk]
        · simp [w, hp]
      · exact fun h => (h hcS).elim
  have hsecond : (∑ p ∈ S, r p ^ 2) = B.card * (q + B.card) := by
    calc
      (∑ p ∈ S, r p ^ 2) = ∑ p ∈ S, ∑ l ∈ B, ∑ k ∈ B, w p l * w p k := by
        apply sum_congr rfl
        intro p _
        simp only [r, pow_two, sum_mul, mul_sum]
        exact sum_comm
      _ = ∑ l ∈ B, ∑ k ∈ B, ∑ p ∈ S, w p l * w p k := by
        rw [sum_comm]
        exact sum_congr rfl (fun l _ => sum_comm)
      _ = ∑ _l ∈ B, (q + B.card) := by
        apply sum_congr rfl
        intro l hl
        calc
          (∑ k ∈ B, ∑ p ∈ S, w p l * w p k) =
              ∑ k ∈ B, (1 + (if l = k then q else 0)) :=
            sum_congr rfl (fun k _ => hpair l hl k)
          _ = q + B.card := by
            rw [sum_add_distrib, ← card_eq_sum_ones, sum_ite_eq, if_pos hl, add_comm]
      _ = _ := sum_const_nat (fun _ _ => rfl)
  have hcs := sq_sum_le_card_mul_sum_sq (s := S) (f := r)
  rw [hfirst, hsecond] at hcs
  change B.card * (q + 1)^2 ≤ S.card * (q + B.card)
  by_cases hf : B.card = 0
  · simp [hf]
  · apply Nat.le_of_mul_le_mul_left _ (Nat.pos_of_ne_zero hf)
    calc
      B.card * (B.card * (q + 1)^2) = (B.card * (q + 1))^2 := by ring
      _ ≤ S.card * (B.card * (q + B.card)) := hcs
      _ = B.card * (S.card * (q + B.card)) := by ring

end

set_option maxHeartbeats 1000000 in
theorem OMA.solution : type_of% @OMA.S_mo_203533.main := by
  classical
  intro P L _ _ _ _
  dsimp only
  intro m hm hm'
  let q := ProjectivePlane.order P L
  change m ≤ q^2 + q + 1 at hm'
  have hmP : m ≤ Fintype.card P := by
    rw [ProjectivePlane.card_points P L]
    exact hm'
  obtain ⟨W, hW, hWbound⟩ := pencil_witness (L := L) m hm hmP
  let values : Finset ℕ :=
    ((univ : Finset P).powerset.filter (fun S => S.card = m)).image
      (fun S => (contained P L S).card)
  have hvalues (t : ℕ) : t ∈ values ↔
      ∃ S : Finset P, S.card = m ∧ (contained P L S).card = t := by
    simp only [values, mem_image, mem_filter, mem_powerset, subset_univ, true_and]
  have hne : values.Nonempty := ⟨_, (hvalues _).mpr ⟨W, hW, rfl⟩⟩
  let f := values.max' hne
  obtain ⟨S, hS, hf⟩ := (hvalues f).mp (max'_mem values hne)
  have hgreat (t : ℕ) (ht : ∃ U : Finset P, U.card = m ∧
      (contained P L U).card = t) : t ≤ f :=
    le_max' values t ((hvalues t).mpr ht)
  have hlo : (m - 1) / q ≤ f :=
    hWbound.trans (hgreat _ ⟨W, hW, rfl⟩)
  have hup : f * (q + 1)^2 ≤ m * (q + f) := by
    simpa only [hf, hS] using incidence_bound (L := L) S
  refine ⟨f, ⟨⟨S, hS, hf⟩, fun ⦃t⦄ ht => hgreat t ht⟩, hlo, hup, ?_⟩
  intro T hT hTq hTm
  change T * q ≤ m at hTq
  change T * m ≤ q^2 at hTm
  change (T - 1) * m ≤ T * (q * f) ∧ (T - 1) * (q * f) ≤ T * m
  have hq : 0 < q := lt_trans Nat.zero_lt_one (ProjectivePlane.one_lt_order P L)
  have hTsplit : T - 1 + 1 = T := Nat.sub_add_cancel (by omega)
  have hfloor : m ≤ q * f + q := by
    have hd := Nat.div_add_mod (m - 1) q
    have hr := Nat.mod_lt (m - 1) hq
    have hb := Nat.mul_le_mul_left q hlo
    omega
  constructor
  · have hmul := Nat.mul_le_mul_left T hfloor
    rw [Nat.mul_add] at hmul
    have he : (T - 1) * m + m = T * m := by
      calc
        _ = (T - 1 + 1) * m := by rw [add_mul, one_mul]
        _ = _ := congrArg (fun a => a * m) hTsplit
    omega
  · have hsq : q^2 ≤ (q + 1)^2 := by
      nlinarith only [Nat.zero_le q]
    have hcoef : (T - 1) * q^2 + T * m ≤ T * (q + 1)^2 :=
      calc
        _ ≤ (T - 1) * q^2 + q^2 := Nat.add_le_add_left hTm _
        _ = T * q^2 := by
          calc
            _ = (T - 1 + 1) * q^2 := by ring
            _ = _ := by rw [hTsplit]
        _ ≤ _ := Nat.mul_le_mul_left T hsq
    have hchain := (Nat.mul_le_mul_right f hcoef).trans
      (show T * (q + 1)^2 * f ≤ T * (m * (q + f)) from
        calc
          _ = T * (f * (q + 1)^2) := by ring
          _ ≤ _ := Nat.mul_le_mul_left T hup)
    apply Nat.le_of_mul_le_mul_right _ hq
    have he₁ :
        ((T - 1) * q^2 + T * m) * f =
          (T - 1) * (q * f) * q + T * m * f := by ring
    have he₂ : T * (m * (q + f)) = T * m * q + T * m * f := by ring
    rw [he₁, he₂] at hchain
    omega
